import Intuitionism.VeldmanConcrete
namespace IPC
open fin_seq

namespace VeldmanConcrete

/-- A handy cut rule for the Hilbert system (used in the k0-forced branch). -/
lemma prf_cut {Γ : Set Form} {X A : Form} :
    (Γ ⊢ᵢ X) → ((Γ ⸴ X) ⊢ᵢ A) → (Γ ⊢ᵢ A) := by
  intro hX hXA
  exact IPC.prf.mp (IPC.prf.deduction (Γ := Γ) (a := X) (b := A) hXA) hX

/--
`runState` after extending a prefix by a single digit `q`.

This is the exact computation lemma you want whenever you need to rewrite
`FS E (extend s (singleton q))`.

It avoids the common pitfall “`simp [FS_child_eq]` turns the equation into `True`”.
-/
lemma runState_extend_singleton (E : Enumerations) (s : fin_seq) (q : ℕ) :
    runState E (extend s (singleton q)) = step E (runState E s) q := by
  -- abbreviations
  let child : fin_seq := extend s (singleton q)

  -- child length facts
  have hLen : child.len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hSucc : s.len.succ ≤ child.len := by
    rw [hLen]
  have hPred : s.len ≤ child.len := Nat.le_of_succ_le hSucc
  have hDigitLt : s.len < child.len := by
    rw [hLen]
    exact Nat.lt_succ_self s.len

  -- prefix relation
  have hPref : Prefix s child := Prefix_child s q

  -- state agreement on the common prefix length
  have hEq0 :
      runStateAux E child s.len (Prefix_len_le hPref)
        = runStateAux E s s.len le_rfl := by
    simpa [child] using (runStateAux_eq_of_Prefix (E := E) (h := hPref) s.len le_rfl)

  have hEqPrefix :
      runStateAux E child s.len (Nat.le_of_succ_le hSucc)
        = runStateAux E s s.len le_rfl := by
    -- change the ≤-proof on the child side using proof-irrelevance
    have hpi :
        runStateAux E child s.len (Nat.le_of_succ_le hSucc)
          = runStateAux E child s.len (Prefix_len_le hPref) := by
      symm
      exact runStateAux_proof_irrel (E := E) (s := child) s.len (Prefix_len_le hPref)
        (Nat.le_of_succ_le hSucc)
    simpa [hpi] using hEq0

  -- the last digit of `child` is `q`, and this is exactly the index used by runStateAux
  have hDigit :
      child.seq
        ⟨s.len, hDigitLt⟩ = q := by
    simpa [child] using (extend_singleton_last s q)

  -- now compute runState on the child
  -- unfold runState; rewrite child.len; unfold runStateAux at the final step
  unfold runState
  -- rewrite the length so that the last step is a `succ`
  -- (this avoids fragile simp with dependent arguments)
  have : runStateAux E child child.len le_rfl = runStateAux E child s.len.succ (by
      simp [hLen]) := by
    cases hLen
    rfl
  -- use that rewrite
  rw [this]
  -- unfold the last step of runStateAux
  -- the predecessor state is `runStateAux E child s.len _`, which equals `runState E s`
  simp [runStateAux, step, hEqPrefix, hDigit, child]

/-- Fs after extending by a singleton digit: the “one-step” computation rule. -/
lemma Fs_extend_singleton (E : Enumerations) (s : fin_seq) (q : ℕ) :
    (runState E (extend s (singleton q))).Fs = FStep E (runState E s) q := by
  -- take Fs-field of the state computation lemma
  simp [runState_extend_singleton (E := E) (s := s) (q := q), step]

/-- Coercion compatibility: `(↑(insert X Γ) : Set _) = (↑Γ : Set _) ⸴ X`. -/
lemma coe_insert_finset (Γ : Finset Form) (X : Form) :
    (↑(insert X Γ) : Set Form) = ((↑Γ : Set Form) ⸴ X) := by
  ext p
  constructor
  · intro hp
    exact Finset.mem_insert.mp hp
  · intro hp
    exact Finset.mem_insert.mpr hp

/-- If `decK t ≠ k0` and `decK t ≠ k1`, then `decK t = k2`. -/
lemma decK_eq_k2_of_ne (t : ℕ) (h0 : decK t ≠ k0) (h1 : decK t ≠ k1) :
    decK t = k2 := by
  -- Let v be the underlying Nat value of decK t (0,1,2).
  cases hv : (decK t).val with
  | zero =>
      -- decK t has val 0, so it's k0, contradict h0
      exfalso
      apply h0
      apply Fin.ext
      -- show vals equal
      simp [k0, hv]
  | succ v1 =>
      cases hv1 : v1 with
      | zero =>
          -- val = 1, so it's k1, contradict h1
          exfalso
          apply h1
          apply Fin.ext
          simp [k1, hv, hv1]
      | succ v2 =>
          cases hv2 : v2 with
          | zero =>
              -- val = 2, so it's k2
              apply Fin.ext
              simp [k2, hv, hv1, hv2]
          | succ v3 =>
              -- val ≥ 3 contradicts (decK t).isLt : val < 3
              have hlt : (decK t).val < 3 := (decK t).isLt
              -- rewrite hlt with hv/hv1/hv2
              have hlt' : Nat.succ (Nat.succ (Nat.succ v3)) < 3 := by
                simpa [hv, hv1, hv2] using hlt
              -- but 3 ≤ succ(succ(succ v3))
              have hge : 3 ≤ Nat.succ (Nat.succ (Nat.succ v3)) := by
                exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le v3)))
              exact False.elim (Nat.not_lt_of_ge hge hlt')


end VeldmanConcrete
end IPC
/-!
# Bar-induction step for the concrete Veldman fan

This file provides the local bar-induction step needed in `UniversalModel.lean`
for the concrete Σ/F construction in `VeldmanConcrete.lean`.

It does **not** depend on `UniversalModel.lean`, so it can be safely imported there.
-/

open NatSeq
open fin_seq
open IPC
open scoped IPC

namespace IPC.VeldmanConcrete

open Finset

/-! ## Proof-theory helper: cut -/



/-! ## Small state-machine lemmas -/

/-- Time counter correctness: after reading `n` symbols, the state has `t = n`. -/
lemma runStateAux_t_eq (E : Enumerations) (s : fin_seq) :
    ∀ n (hn : n ≤ s.len), (runStateAux E s n hn).t = n := by
  intro n hn
  induction n with
  | zero =>
      simp [runStateAux]
      rfl
  | succ n ih =>
      have hn' : n ≤ s.len := Nat.le_of_succ_le hn
      have ht : (runStateAux E s n hn').t = n := ih hn'
      simp [runStateAux, step, ht]

lemma runState_t_eq_len (E : Enumerations) (s : fin_seq) :
    (runState E s).t = s.len := by
  simpa [runState] using runStateAux_t_eq (E := E) (s := s) (n := s.len) le_rfl

/-- If `prev2 = 1` in the final state, then the sequence length is at least 2.
(For length 0 or 1, `prev2` is forced to be 0 by construction.) -/
lemma two_le_len_of_prev2_eq_one (E : Enumerations) (s : fin_seq) :
    (runState E s).prev2 = 1 → 2 ≤ s.len := by
  intro hp
  cases hlen : s.len with
  | zero =>
      -- runState on empty sequence is initState, so prev2=0
      have : (runState E s).prev2 = 0 := by
        -- runStateAux 0 = initState
        simp [runState, hlen, runStateAux, initState]
      have h01 : (0 : ℕ) ≠ 1 := by decide
      exact False.elim (h01 (by simp [this] at hp))
  | succ n =>
      cases n with
      | zero =>
          -- length 1: one step from initState, prev2 still 0
          have : (runState E s).prev2 = 0 := by
            -- unfold runState with len=1
            -- runStateAux 1 = step initState q0, and step sets prev2 := init.prev1 = 0
            simp [runState, hlen, runStateAux, step, initState]
          have h01 : (0 : ℕ) ≠ 1 := by decide
          exact False.elim (h01 (by simp [this] at hp))
      | succ n =>
          -- length ≥ 2
          -- s.len = n.succ.succ
          simp

/-! ## Σ: admitted child lemma -/

/-- If `s` is admitted and `q` is allowed at `s`, then the child `s⋆[q]` is admitted.

This is just unpacking the definition of `Admittedb` / `admittedAuxb` in §3.32.
-/
lemma Sigma_child_eq_zero_of_allowed
    (E : Enumerations)
    (s : fin_seq) (q : ℕ)
    (hs0 : Sigma E s = 0)
    (hq : AllowedStepb E (runState E s) q = true) :
    Sigma E (extend s (singleton q)) = 0 := by
  -- rewrite Sigma=0 ↔ Admittedb=true
  have hsAd : Admittedb E s = true := (Sigma_eq_zero_iff (E := E) s).1 hs0

  let child : fin_seq := extend s (singleton q)

  have hChildLen : child.len = s.len + 1 := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hSucc : s.len.succ ≤ child.len := by
    rw [hChildLen, Nat.succ_eq_add_one]
  have hPred : s.len ≤ child.len := Nat.le_of_succ_le hSucc
  have hDigitLt : s.len < child.len := by
    rw [hChildLen]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos 0)

  have hPref : Prefix s child := Prefix_child s q

  -- admittedAuxb on the prefix length agrees by Prefix
  have hEqAdm : admittedAuxb E child s.len hPred = admittedAuxb E s s.len le_rfl := by
    have hEq := admittedAuxb_eq_of_Prefix (E := E) (h := hPref) s.len le_rfl
    -- align the `≤` proof with proof-irrelevance
    have hpi :
        admittedAuxb E child s.len (Nat.le_trans le_rfl hPred)
          = admittedAuxb E child s.len hPred :=
      admittedAuxb_proof_irrel (E := E) (s := child) s.len (Nat.le_trans le_rfl hPred) hPred
    simpa [hpi] using hEq

  have hsAux : admittedAuxb E s s.len le_rfl = true := by
    simpa [Admittedb] using hsAd
  have hChildPrefix : admittedAuxb E child s.len hPred = true := by
    simpa [hEqAdm] using hsAux

  -- compute the last digit and the prefix state
  have hLast :
      child.seq ⟨s.len, hDigitLt⟩ = q := by
    simpa [child] using extend_singleton_last s q

  have hStateEq :
      runStateAux E child s.len (Nat.le_of_succ_le hSucc)
        = runStateAux E s s.len le_rfl := by
    have hEq := runStateAux_eq_of_Prefix (E := E) (h := hPref) s.len le_rfl
    have hpi :
        runStateAux E child s.len (Nat.le_trans le_rfl hPred)
          = runStateAux E child s.len (Nat.le_of_succ_le hSucc) :=
      runStateAux_proof_irrel (E := E) (s := child) s.len (Nat.le_trans le_rfl hPred)
        (Nat.le_of_succ_le hSucc)
    simpa [hpi] using hEq

  have hAllowedChild :
      AllowedStepb E (runStateAux E child s.len (Nat.le_of_succ_le hSucc))
        (child.seq ⟨s.len, hDigitLt⟩)
        = true := by
    -- rewrite the state and digit to the given hypothesis `hq`
    -- runState E s is runStateAux ... s.len
    simpa [runState, hStateEq, hLast] using hq

  -- admittedAuxb at succ length: prefix AND allowed
  have hAuxChild : admittedAuxb E child s.len.succ hSucc = true := by
    simp [admittedAuxb, hChildPrefix, hAllowedChild]

  have hAdChild : Admittedb E child = true := by
    -- Admittedb is admittedAuxb at full length; child.len = s.len+1
    simpa [Admittedb, child, fin_seq.extend, fin_seq.singleton] using hAuxChild

  exact (Sigma_eq_zero_iff (E := E) child).2 hAdChild

/-! ## F: one-step computation lemma -/

/-- `FS` on a child `s⋆[q]` is computed by a single `FStep` from the parent state.

This is the direct formal counterpart of the recursive definition of Γ(a*q) in §3.32.
-/
lemma FS_child_eq
    (E : Enumerations)
    (s : fin_seq) (q : ℕ) :
    FS E (extend s (singleton q)) = FStep E (runState E s) q := by
  simpa [FS] using Fs_extend_singleton (E := E) (s := s) (q := q)

/-! ## Forced witness extraction -/

/-- Extract the Prop witness encoded by `Forced0b = true`.

Paper: §3.32 Case 1 “forced” subcase.
-/
lemma Forced0_witness_of_Forced0b
    (E : Enumerations)
    (st : State)
    (hk0 : decK st.t = k0)
    (hF : Forced0b E st = true) :
    ∃ i : ℕ, i ≤ st.t ∧
      (E.d i).2 = E.W (decN st.t) ∧
      (E.d i).1 ⊆ st.Fs := by
  -- unfold Forced0b and use `anyUpTo_eq_true`
  unfold Forced0b at hF
  simp [hk0] at hF
  -- At this point `hF` has the following shape:
  -- hF : anyUpTo st.t (fun i => decide ((E.d i).2 = ...) && decide ((E.d i).1 ⊆ ...)) = true

  have hAny :=
    (Finset.anyUpTo_eq_true (t := st.t) (p := fun i =>
      decide ((E.d i).2 = E.W (decN st.t)) &&
      decide ((E.d i).1 ⊆ st.Fs)))

  rcases (hAny.mp hF) with ⟨i, hi, hdec⟩
  -- hdec : (decide p && decide q) = true

  have hdec' :
      decide ((E.d i).2 = E.W (decN st.t)) = true ∧
      decide ((E.d i).1 ⊆ st.Fs) = true := by
    -- Either of the following two styles works; use the one whose lemma name is available in your environment.
    · exact Bool.and_eq_true_iff.mp hdec
    -- · exact (by
    --     -- If `Bool.and_eq_true` is not available, you can also proceed as follows:
    --     have : (decide ((E.d i).2 = E.W (decN st.t)) &&
    --              decide ((E.d i).1 ⊆ st.Fs)) = true := hdec
    --     -- Usually `simp` turns `&& = true` into a conjunction.
    --     simpa using this)

  have h1 : (E.d i).2 = E.W (decN st.t) :=
    (Finset.decide_eq_true_iff (P := (E.d i).2 = E.W (decN st.t))).1 hdec'.1

  have h2 : (E.d i).1 ⊆ st.Fs :=
    (Finset.decide_eq_true_iff (P := (E.d i).1 ⊆ st.Fs)).1 hdec'.2

  exact ⟨i, hi, h1, h2⟩


/-! ## k2 bookkeeping: if `prev2 = 1`, then the current `W_n` is already in `Fs` -/

/-- A key invariant used in the k2 split case:

If we are at a k2-time `t` and the state remembers `prev2 = 1`, then the formula
`W (decN t)` was inserted two steps earlier (at time `t-2`, which is a k0-time for the
same `n`), hence it is a member of the current `Fs`.

This matches Veldman §3.32 Case 3.2 (the split case): we can use the disjunction
`A∨B` because it was added in Case 1 two steps before.
-/
lemma W_mem_Fs_of_k2_prev2_eq_one
    (E : Enumerations)
    (s : fin_seq)
    (hk2 : decK (runState E s).t = k2)
    (hp2 : (runState E s).prev2 = 1) :
    E.W (decN (runState E s).t) ∈ (runState E s).Fs := by


  -- Abbreviate the final state/time.
  let st : State := runState E s
  have ht : st.t = s.len := by
    simpa [st] using (runState_t_eq_len (E := E) s)

  -- Work with `t := len` and `u := 3*(t/3)` (the k0-slot before a k2-time).
  let t : ℕ := s.len
  let u : ℕ := 3 * (t / 3)

  -- Turn hk2 into a statement about `decK t`.
  have hk2_t : decK t = k2 := by
    simpa [st, ht, t] using hk2

  -- Extract the remainder information `t % 3 = 2`.
  have htmod : t % 3 = 2 := by
    have h := congrArg Fin.val hk2_t
    simpa [decK, schedDecode, k2] using h

  -- Decompose `t` as `3*(t/3)+2`.
  have htdecomp : t = 3 * (t / 3) + 2 := by
    calc
      t = (t / 3) * 3 + t % 3 := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.div_add_mod t 3).symm
      _ = (t / 3) * 3 + 2 := by simp [htmod]
      _ = 3 * (t / 3) + 2 := by
        simp [Nat.mul_comm,
          Nat.add_comm]

  -- Therefore `decK u = k0` and `decN u = decN t`.
  have hdecK_u : decK u = k0 := by
    apply Fin.eq_of_val_eq
    simp [decK, schedDecode, schedDecodeBin, u, k0]

  have hdiv : u / 3 = t / 3 := by
    simp [u]

  have hdecN_u : decN u = decN t := by
    simp [decN, schedDecode, schedDecodeBin, hdiv]

  -- `u+2 = t`, and hence `(u+2) ≤ len`.
  have hu2_eq : u + 2 = t := by
    calc
      u + 2 = 3 * (t / 3) + 2 := by simp [u]
      _ = t := htdecomp.symm

  have hu2_eq' : u.succ.succ = t := by
    -- `u.succ.succ = u+2`
    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hu2_eq

  have hu2_eq_len : u.succ.succ = s.len := by
    simpa [t] using hu2_eq'

  have hu2_le : u.succ.succ ≤ s.len := by
    -- Rewrite the left-hand side to `s.len`; then the proof is simply `le_rfl`.
    rw [hu2_eq_len]

  -- Choose the exact prefix states needed to unfold twice.
  have hu1_le : u.succ ≤ s.len := Nat.le_of_succ_le hu2_le
  have hu0_le : u ≤ s.len := Nat.le_of_succ_le hu1_le

  let st0 : State := runStateAux E s u hu0_le
  let st1 : State := runStateAux E s u.succ hu1_le
  let st2 : State := runStateAux E s u.succ.succ hu2_le

  -- `st2` is the same as the final state `st`.
  -- First record the identity `u.succ.succ = s.len`.
  have hu2_eq_len : u.succ.succ = s.len := by
    simpa [t] using hu2_eq'

  -- Here `st2` is `runStateAux` at `u+2`, while `st` is `runStateAux` at the full length.
  have hst2_to_len :
      st2 = runStateAux E s s.len (by
        -- Transport `hu2_le : u.succ.succ ≤ s.len` into the canonical proof `s.len ≤ s.len`.
        simp) := by
    -- Key point: the goal here is an equality of `State` terms, so `simp` will not collapse it to `True`.
      simp [st2]
      exact runStateAux.congr_simp E E rfl s s rfl (u + 1 + 1) s.len hu2_eq hu2_le

  -- 2) With the same `n = s.len`, use proof irrelevance to remove the difference between proof arguments (do not wrap this in another `simpa`).
  have hpi :
      runStateAux E s s.len (by simp)
        = runStateAux E s s.len le_rfl :=
    runStateAux_proof_irrel (E := E) (s := s) (n := s.len)
      (by simp) le_rfl

  -- 3) Unfold `st` so that it becomes `runStateAux ... s.len le_rfl` (still an equality of `State` terms).
  have hst_def : st = runStateAux E s s.len le_rfl := by
    simp [st, runState]

  -- Finally chain the three equalities together.
  have hst2 : st2 = st := by
    calc
      st2
          = runStateAux E s s.len (by simp) := hst2_to_len
      _   = runStateAux E s s.len le_rfl := hpi
      _   = st := by
            -- Here `simp` only rewrites `st_def` inside a `State` term; it does not turn the equality into `True`.
            simp [hst_def]

  -- Unfold the two final steps explicitly.
  have hu_lt_len : u < s.len := by
    exact Nat.lt_of_succ_le hu1_le
  have hu_succ_lt_len : u.succ < s.len := by
    exact Nat.lt_of_succ_le hu2_le

  have hst1_step :
      st1 = step E st0 (s.seq ⟨u, hu_lt_len⟩) := by
    simp [st1, st0, runStateAux]

  have hst2_step :
      st2 = step E st1 (s.seq ⟨u.succ, hu_succ_lt_len⟩) := by
    simp [st2, st1, runStateAux]

  -- Hence `prev2` of the final state is the digit at position `u`.
  have hprev2 :
      st2.prev2 = (s.seq ⟨u, hu_lt_len⟩) := by
    simp [hst2_step, hst1_step, step]

  -- From `hp2`, deduce that digit is `1`.
  have hq : (s.seq ⟨u, hu_lt_len⟩) = 1 := by
    have : st2.prev2 = 1 := by
      simpa [hst2, st] using hp2
    simpa [hprev2] using this

  -- Time component at `st0`.
  have hst0_t : st0.t = u := by
    simpa [st0] using (runStateAux_t_eq (E := E) (s := s) u hu0_le)

  have hk0_u : decK st0.t = k0 := by
    simpa [hst0_t] using hdecK_u

  -- Compute `st1.Fs`: in k0 and with `q=1`, we insert `W(decN u)`.
  have hFs1 : st1.Fs = insert (E.W (decN t)) st0.Fs := by
    have : st1.Fs = FStep E st0 1 := by
      simp [hst1_step, hq, step]
    have hFStep : FStep E st0 1 = insert (E.W (decN st0.t)) st0.Fs := by
      simp [FStep, hk0_u]
    calc
      st1.Fs = FStep E st0 1 := by simpa using this
      _ = insert (E.W (decN st0.t)) st0.Fs := by simpa using hFStep
      _ = insert (E.W (decN u)) st0.Fs := by simp [hst0_t]
      _ = insert (E.W (decN t)) st0.Fs := by simp [hdecN_u]

  have hW_mem_st1 : E.W (decN t) ∈ st1.Fs := by
    simp [hFs1]

  -- Monotonicity across the last step.
  have hmono : st1.Fs ⊆ st2.Fs := by
    simpa [hst2_step] using
      (step_Fs_mono (E := E) (st := st1)
        (q := s.seq ⟨u.succ, hu_succ_lt_len⟩))

  have hW_mem_st2 : E.W (decN t) ∈ st2.Fs := hmono hW_mem_st1

  -- Translate back to the final state `st = runState E s` and rewrite `t = st.t`.
  simpa [hst2, st, ht, t] using hW_mem_st2

/-! ## The main result: the concrete bar-induction step -/

/-! Local induction step for the bar lemma, for the concrete Σ/F.

This is the propositional analogue of the closure step used in Veldman Lemma §3.43.

Structure of proof matches §3.32:
- k0 (Case 1): forced vs not forced
- k1 (Case 2): only q=0, nothing changes
- k2 (Case 3): split if `W_n` is a disjunction and `prev2=1`; otherwise only q=0
-/

/-- Local bar-induction step for the concrete fan. In the paper this corresponds to the rootward induction on admitted nodes used inside the completeness argument after the subfan construction of §4.1. -/
theorem barIndStep_concrete
    (E : Enumerations)
    (A : Form) :
  ∀ s : fin_seq,
    Sigma E s = 0 →
      (∀ n : ℕ, Sigma E (extend s (singleton n)) = 0 →
          ((↑(FS E (extend s (singleton n))) : Set Form) ⊢ᵢ A)) →
        ((↑(FS E s) : Set Form) ⊢ᵢ A) := by
  intro s hs0 hall


  -- abbreviations
  let st : State := runState E s
  let Γ : Set Form := (↑(FS E s) : Set Form)

  -- case split on decK t
  by_cases hk0 : decK st.t = k0
  · -- k0: Case 1
    by_cases hF : Forced0b E st = true
    · -- forced subcase: must take q=1 and cut out W_n
      let q : ℕ := 1
      have hAllowed : AllowedStepb E st q = true := by
        -- AllowedStepb in forced hk0 case reduces to decide(q=1)
        unfold AllowedStepb
        simp [hk0, hF, q]

      have hChild : Sigma E (extend s (singleton q)) = 0 :=
        Sigma_child_eq_zero_of_allowed (E := E) (s := s) (q := q) hs0 (by
          simpa [st] using hAllowed)

      have hChildPrf : ((↑(FS E (extend s (singleton q))) : Set Form) ⊢ᵢ A) :=
        hall q hChild

      let X : Form := E.W (decN st.t)
      have hFsStep :
    (runState E (extend s (singleton 1))).Fs
      = FStep E (runState E s) 1 := IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := 1)
      -- rewrite FS(child) = insert X (FS s)
      have hFSchild : FS E (extend s (singleton q)) = insert X (FS E s) := by
        simpa [st, IPC.VeldmanConcrete.FStep, hk0] using hFsStep
      -- convert child proof to (Γ ⸴ X) ⊢ A
      have hΓX : (Set.insert X Γ) ⊢ᵢ A := by
        have hSub :
            (↑(FS E (extend s (singleton q))) : Set Form) ⊆ (Set.insert X Γ) := by
          intro p hp
          have hp' : p ∈ FS E (extend s (singleton q)) := by simpa using hp
          have hp'' : p ∈ insert X (FS E s) := by simpa [hFSchild] using hp'
          rcases Finset.mem_insert.mp hp'' with hpX | hpΓ
          · exact Or.inl hpX
          · exact Or.inr (by simpa [Γ] using hpΓ)
        exact IPC.prf.sub_weak
          (Δ := (↑(FS E (extend s (singleton q))) : Set Form))
          (Γ := Set.insert X Γ) (p := A) hChildPrf hSub

      -- derive Γ ⊢ X from the forced witness
      rcases Forced0_witness_of_Forced0b (E := E) (st := st) hk0 hF with ⟨i, hi, hconcl, hprem⟩

      have hDer : ((↑(E.d i).1 : Set Form) ⊢ᵢ (E.d i).2) := E.d_sound i
      have hX_from_prem : ((↑(E.d i).1 : Set Form) ⊢ᵢ X) := by
        simpa [X, hconcl] using hDer

      have hPrem_sub : (↑(E.d i).1 : Set Form) ⊆ Γ := by
        intro p hp
        have hp' : p ∈ st.Fs := hprem hp
        -- st.Fs = FS E s by definition
        simpa [Γ, FS, st, runState] using hp'

      have hΓ_X : Γ ⊢ᵢ X :=
        IPC.prf.sub_weak (Δ := (↑(E.d i).1 : Set Form)) (Γ := Γ) (p := X) hX_from_prem hPrem_sub

      -- cut
      have hΓA : Γ ⊢ᵢ A := prf_cut (Γ := Γ) (X := X) (A := A) hΓ_X hΓX
      simpa [Γ] using hΓA

    · -- not forced: take q=0, FS stays the same
      let q : ℕ := 0
      have hAllowed : AllowedStepb E st q = true := by
        unfold AllowedStepb
        simp [hk0, hF, q]

      have hChild : Sigma E (extend s (singleton q)) = 0 :=
        Sigma_child_eq_zero_of_allowed (E := E) (s := s) (q := q) hs0 (by
          simpa [st] using hAllowed)

      have hChildPrf : ((↑(FS E (extend s (singleton q))) : Set Form) ⊢ᵢ A) :=
        hall q hChild

      -- FS(child)=FS(s)
      have hFS : FS E (extend s (singleton q)) = FS E s := by
  -- First rewrite the child's `Fs` as the corresponding `FStep` value.
        have hstep :
      (runState E (extend s (singleton q))).Fs
        = FStep E (runState E s) q :=
    IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q)

  -- In the `k0` branch with `q ≠ 1`, `FStep` is exactly `st.Fs` (hence `FS E s`).
  -- Here we use `hk0 : decK st.t = k0` together with `hqne : q ≠ 1`.
        simpa [FS, st, IPC.VeldmanConcrete.FStep, hk0] using hstep

      simpa [Γ, hFS] using hChildPrf

  · -- hk0 false
    by_cases hk1 : decK st.t = k1
    · -- k1: Case 2, only q=0 and FS unchanged
      let q : ℕ := 0
      have hk10 : (k1 : Fin 3) ≠ k0 := by decide
      have hAllowed : AllowedStepb E st q = true := by
        unfold AllowedStepb
        simp [ hk1, q, hk10]

      have hChild : Sigma E (extend s (singleton q)) = 0 :=
        Sigma_child_eq_zero_of_allowed (E := E) (s := s) (q := q) hs0 (by
          simpa [st] using hAllowed)

      have hChildPrf : ((↑(FS E (extend s (singleton q))) : Set Form) ⊢ᵢ A) :=
        hall q hChild

      have hFS : FS E (extend s (singleton q)) = FS E s := by
  -- Again begin by rewriting `runState(child).Fs` as `FStep`.
        have hstep :
      (runState E (extend s (singleton q))).Fs
        = FStep E (runState E s) q :=
    IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q)

  -- In the `k1` branch, `FStep` is always `st.Fs`, independently of `q`.
        simpa [FS, st, IPC.VeldmanConcrete.FStep, hk0, hk1, q] using hstep
      simpa [Γ, hFS] using hChildPrf

    · -- k2: Case 3
      have hk2 : decK st.t = k2 := IPC.VeldmanConcrete.decK_eq_k2_of_ne (t := st.t) hk0 hk1

      -- inspect W_n
      cases hW : E.W (decN st.t) with
      | or P Q =>
          -- disjunction at this time
          by_cases hp : st.prev2 = 1
          · -- split subcase: q=1 and q=2 admitted; use or_elim
            let q1 : ℕ := 1
            let q2 : ℕ := 2

            have hAllowed1 : AllowedStepb E st q1 = true := by
              unfold AllowedStepb
              simp [hk0, hk1, hW, hp, q1]
            have hAllowed2 : AllowedStepb E st q2 = true := by
              unfold AllowedStepb
              simp [hk0, hk1, hW, hp, q2]

            have hChild1 : Sigma E (extend s (singleton q1)) = 0 :=
              Sigma_child_eq_zero_of_allowed (E := E) (s := s) (q := q1) hs0 (by
                simpa [st] using hAllowed1)
            have hChild2 : Sigma E (extend s (singleton q2)) = 0 :=
              Sigma_child_eq_zero_of_allowed (E := E) (s := s) (q := q2) hs0 (by
                simpa [st] using hAllowed2)

            have hPrf1 : ((↑(FS E (extend s (singleton q1))) : Set Form) ⊢ᵢ A) :=
              hall q1 hChild1
            have hPrf2 : ((↑(FS E (extend s (singleton q2))) : Set Form) ⊢ᵢ A) :=
              hall q2 hChild2

            -- FS(child1)=insert P FS(s), FS(child2)=insert Q FS(s)
            have hFs1_step :
    (runState E (extend s (singleton q1))).Fs = FStep E (runState E s) q1 :=
  IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q1)
            have hFS1 : FS E (extend s (singleton q1)) = insert P (FS E s) := by
              simpa [FS, st, IPC.VeldmanConcrete.FStep, hk0, hk1, hW, hp, q1] using hFs1_step

-- FS(child2)=insert Q FS(s)
            have hFS2 : FS E (extend s (singleton q2)) = insert Q (FS E s) := by
  -- First rewrite the child's `runState`-level `Fs` field into `FStep`.
              have hstep :
      (runState E (extend s (singleton q2))).Fs
        = FStep E (runState E s) q2 :=
              IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q2)

  -- Then simplify `FStep` by direct computation (note that `hk2` is not actually needed here).
  -- Recall that `FStep` is coded as `if k = k0 / else if k = k1 / else match Wn with ...`.
  -- We use `hk0` and `hk1` to force the computation into the `Case 3` match branch.
              simpa [FS, st, IPC.VeldmanConcrete.FStep, hk0, hk1, hW, hp, q2] using hstep

            -- The disjunction itself is in FS(s) (k2 invariant)
            have hWmem : E.W (decN st.t) ∈ st.Fs :=
              W_mem_Fs_of_k2_prev2_eq_one (E := E) (s := s) hk2 (by simpa [st] using hp)

            have hOr : Γ ⊢ᵢ Form.or P Q := by
              -- use ax, after rewriting membership
              apply IPC.prf.ax
              -- hWmem is membership in st.Fs; rewrite st.Fs = FS(s) and hW
              --
              -- st.Fs = FS E s by definition
              have : st.Fs = FS E s := by simp [FS, st]
              -- hW : E.W(...) = Form.or P Q
              -- and Γ is ↑(FS E s)
              simpa [Γ, this, hW] using hWmem

            -- convert child proofs into (Γ⸴P) ⊢ A and (Γ⸴Q) ⊢ A
            have hΓP : (Γ ⸴ P) ⊢ᵢ A := by
              have hSubP :
                  (↑(FS E (extend s (singleton q1))) : Set Form) ⊆ (Γ ⸴ P) := by
                intro p hp
                have hp' : p ∈ FS E (extend s (singleton q1)) := by simpa using hp
                have hp'' : p ∈ insert P (FS E s) := by simpa [hFS1] using hp'
                rcases Finset.mem_insert.mp hp'' with hpP | hpΓ
                · exact Or.inl hpP
                · exact Or.inr (by simpa [Γ] using hpΓ)
              exact IPC.prf.sub_weak
                (Δ := (↑(FS E (extend s (singleton q1))) : Set Form))
                (Γ := (Γ ⸴ P)) (p := A) hPrf1 hSubP

            have hΓQ : (Set.insert Q Γ) ⊢ᵢ A := by
              have hSubQ :
                  (↑(FS E (extend s (singleton q2))) : Set Form) ⊆ (Set.insert Q Γ) := by
                intro p hp
                have hp' : p ∈ FS E (extend s (singleton q2)) := by simpa using hp
                have hp'' : p ∈ insert Q (FS E s) := by simpa [hFS2] using hp'
                rcases Finset.mem_insert.mp hp'' with hpQ | hpΓ
                · exact Or.inl hpQ
                · exact Or.inr (by simpa [Γ] using hpΓ)
              exact IPC.prf.sub_weak
                (Δ := (↑(FS E (extend s (singleton q2))) : Set Form))
                (Γ := Set.insert Q Γ) (p := A) hPrf2 hSubQ

            -- or elimination
            have hΓA : Γ ⊢ᵢ A :=
              IPC.prf.or_elim (Γ := Γ) (p := P) (q := Q) (r := A) hOr hΓP hΓQ
            simpa [Γ] using hΓA

          · -- not split: only q=0 admitted; FS unchanged
            let q : ℕ := 0
            have hAllowed : AllowedStepb E st q = true := by
              unfold AllowedStepb
              simp [hk0, hk1, hW, hp, q]

            have hChild : Sigma E (extend s (singleton q)) = 0 :=
              Sigma_child_eq_zero_of_allowed (E := E) (s := s) (q := q) hs0 (by
                simpa [st] using hAllowed)

            have hChildPrf : ((↑(FS E (extend s (singleton q))) : Set Form) ⊢ᵢ A) :=
              hall q hChild

            have hFS : FS E (extend s (singleton q)) = FS E s := by
  -- Rewrite `runState(child).Fs` as `FStep (runState s) q`.
              have hstep :
      (runState E (extend s (singleton q))).Fs
        = FStep E (runState E s) q :=
    IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q)

  -- Here we are in the non-splitting branch of Case 3, so the actual digit `q` is `0`.
  -- In this situation `FStep` returns `st.Fs` directly.
              simpa [FS, st, IPC.VeldmanConcrete.FStep, hk0, hk1, hk2, hW, hp, q] using hstep
            simpa [Γ, hFS] using hChildPrf

      | _ =>
          -- not a disjunction: only q=0 admitted; FS unchanged
          let q : ℕ := 0
          have hAllowed : AllowedStepb E st q = true := by
            unfold AllowedStepb
            simp [hk0, hk1, hW, q]

          have hChild : Sigma E (extend s (singleton q)) = 0 :=
            Sigma_child_eq_zero_of_allowed (E := E) (s := s) (q := q) hs0 (by
              simpa [st] using hAllowed)

          have hChildPrf : ((↑(FS E (extend s (singleton q))) : Set Form) ⊢ᵢ A) :=
            hall q hChild

          have hFS : FS E (extend s (singleton q)) = FS E s := by
  -- Rewrite `runState(child).Fs` as `FStep (runState s) q`.
            have hstep :
      (runState E (extend s (singleton q))).Fs
        = FStep E (runState E s) q :=
    IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q)

  -- This is the Case 3 branch where the formula is not a disjunction or we are not in split mode; hence only `q = 0` is allowed and `FStep` returns `st.Fs`.
            simpa [FS, st, IPC.VeldmanConcrete.FStep, hk0, hk1, hk2, hW, q] using hstep

          simpa [Γ, hFS] using hChildPrf

end IPC.VeldmanConcrete
