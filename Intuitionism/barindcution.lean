import Intuitionism.VeldmanConcrete
namespace IPC
open fin_seq

namespace VeldmanConcrete

/-- A handy cut rule for the Hilbert system (used in Todo C, k0-forced branch). -/
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
    simpa [hLen]
  have hPred : s.len ≤ child.len := Nat.le_of_succ_le hSucc

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
        ⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc⟩ = q := by
    -- align the Fin index with the one in `extend_singleton_last`
    have hFin :
        (⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc⟩ : Fin child.len)
          = ⟨s.len, by
              simpa [child, fin_seq.extend, fin_seq.singleton]⟩ := by
      apply Fin.ext; rfl
    simpa [child, hFin] using (extend_singleton_last s q)

  -- now compute runState on the child
  -- unfold runState; rewrite child.len; unfold runStateAux at the final step
  unfold runState
  -- rewrite the length so that the last step is a `succ`
  -- (this avoids fragile simp with dependent arguments)
  have : runStateAux E child child.len le_rfl = runStateAux E child s.len.succ (by
      simpa [hLen]) := by
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
  simpa [runState_extend_singleton (E := E) (s := s) (q := q), step] using
    congrArg State.Fs (runState_extend_singleton (E := E) (s := s) (q := q))

/-- Coercion compatibility: `(↑(insert X Γ) : Set _) = (↑Γ : Set _) ⸴ X`. -/
lemma coe_insert_finset (Γ : Finset Form) (X : Form) :
    (↑(insert X Γ) : Set Form) = ((↑Γ : Set Form) ⸴ X) := by
  ext p
  simp
  exact Iff.symm (Eq.to_iff rfl)

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
      simpa [k0, hv]
  | succ v1 =>
      cases hv1 : v1 with
      | zero =>
          -- val = 1, so it's k1, contradict h1
          exfalso
          apply h1
          apply Fin.ext
          simpa [k1, hv, hv1]
      | succ v2 =>
          cases hv2 : v2 with
          | zero =>
              -- val = 2, so it's k2
              apply Fin.ext
              simpa [k2, hv, hv1, hv2]
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
# Bar induction step for the concrete Veldman fan (Todo C)

This file provides the local bar-induction step needed in `sketch.lean`
for the concrete Σ/F construction in `VeldmanConcrete.lean`.

It does **not** depend on `sketch.lean`, so it can be safely imported there.
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
      -- contradiction
      simp [this] at hp
  | succ n =>
      cases n with
      | zero =>
          -- length 1: one step from initState, prev2 still 0
          have : (runState E s).prev2 = 0 := by
            -- unfold runState with len=1
            -- runStateAux 1 = step initState q0, and step sets prev2 := init.prev1 = 0
            simp [runState, hlen, runStateAux, step, initState]
          simp [this] at hp
      | succ n =>
          -- length ≥ 2
          -- s.len = n.succ.succ
          simpa [hlen] using (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n)))

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

  have hSucc : s.len.succ ≤ child.len := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hPred : s.len ≤ child.len := Nat.le_of_succ_le hSucc

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
      child.seq ⟨s.len, by
        simp [child, fin_seq.extend, fin_seq.singleton]⟩ = q := by
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
        (child.seq ⟨s.len, by
          simp [child, fin_seq.extend, fin_seq.singleton]⟩)
        = true := by
    -- rewrite the state and digit to the given hypothesis `hq`
    -- runState E s is runStateAux ... s.len
    simpa [runState, hStateEq, hLast] using hq

  -- admittedAuxb at succ length: prefix AND allowed
  have hAuxChild : admittedAuxb E child s.len.succ hSucc = true := by
    simp [admittedAuxb, hSucc, hChildPrefix, hAllowedChild]

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

  -- We prove the stronger statement about runState itself, then project `.Fs`.
  let child : fin_seq := extend s (singleton q)

  have hlen : child.len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hSucc : s.len.succ ≤ child.len := by
    simpa [hlen]

  -- `runState E child` is `runStateAux ... child.len`; rewrite the length to `s.len+1`.
  have hpi_len :
      runStateAux E child child.len le_rfl = runStateAux E child s.len.succ hSucc := by
    -- proof irrelevance + hlen
    have h' : s.len.succ ≤ child.len := hSucc
    -- change `child.len` to `s.len.succ`
    -- and align proofs
    have := runStateAux_proof_irrel (E := E) (s := child) (n := child.len) le_rfl (by
      simpa [hlen] using h')
    simpa [hlen] using this

  -- unfold runStateAux at the last step (succ)
  have hUnfold :
      runStateAux E child s.len.succ hSucc
        =
      let st := runStateAux E child s.len (Nat.le_of_succ_le hSucc)
      let qq := child.seq ⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc⟩
      step E st qq := by
    simp [runStateAux]

  -- rewrite the prefix state using Prefix
  have hPref : Prefix s child := Prefix_child s q
  have hPred : s.len ≤ child.len := Nat.le_of_succ_le hSucc

  have hStateEq :
      runStateAux E child s.len (Nat.le_of_succ_le hSucc) = runStateAux E s s.len le_rfl := by
    have hEq := runStateAux_eq_of_Prefix (E := E) (h := hPref) s.len le_rfl
    have hpi :
        runStateAux E child s.len (Nat.le_trans le_rfl hPred)
          = runStateAux E child s.len (Nat.le_of_succ_le hSucc) :=
      runStateAux_proof_irrel (E := E) (s := child) s.len (Nat.le_trans le_rfl hPred)
        (Nat.le_of_succ_le hSucc)
    simpa [hpi] using hEq

  have hDigit :
      child.seq ⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc⟩ = q := by
    -- the proof in the index is irrelevant
    -- use the dedicated lemma about the last digit
    have :
        child.seq ⟨s.len, by
          simp [child, fin_seq.extend, fin_seq.singleton]⟩ = q := by
      simpa [child] using extend_singleton_last s q
    -- now coerce the Fin index equality
    simpa [child, fin_seq.extend, fin_seq.singleton] using this

  -- Put it together: runState child = step (runState s) q
  have hRun : runState E child = step E (runState E s) q := by
    -- start from runStateAux form
    -- runState E child = runStateAux E child child.len le_rfl
    --                 = runStateAux E child (s.len+1) ...
    --                 = step E (runStateAux E child s.len ...) q
    --                 = step E (runStateAux E s s.len) q
    --                 = step E (runState E s) q

    -- rewrite runStateEchild
    have : runState E child = runStateAux E child child.len le_rfl := by rfl
    -- rewrite via hpi_len, unfold, rewrite state & digit
    --
    -- We keep this as a calc chain for readability.
    calc
      runState E child
          = runStateAux E child child.len le_rfl := by rfl
      _   = runStateAux E child s.len.succ hSucc := by simpa using hpi_len
      _   = (let st := runStateAux E child s.len (Nat.le_of_succ_le hSucc)
             let qq := child.seq ⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc⟩
             step E st qq) := by
             simpa using hUnfold
      _   = step E (runStateAux E s s.len le_rfl) q := by
             simp [hStateEq, hDigit]
      _   = step E (runState E s) q := by
             simp [runState]

  -- Now compute FS by projecting `.Fs` and unfolding `step`.
  -- `step` sets `Fs := FStep E st q`.
  --
  -- So:
  --   FS(child) = (runState child).Fs = (step ...).Fs = FStep (runState s) q.
    -- `hRun` uses the local abbrev `child`, but the goal has `extend s [q]`.
  have hRun' : runState E (extend s (singleton q)) = step E (runState E s) q := by
    simpa [child] using hRun
  simp [FS, hRun', step]


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
  -- 现在 hF 的形状是：
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
    -- 下面两种写法二选一；看你环境里哪个 lemma 名字可用
    · exact Bool.and_eq_true_iff.mp hdec
    -- · exact (by
    --     -- 如果没有 Bool.and_eq_true，也可以：
    --     have : (decide ((E.d i).2 = E.W (decN st.t)) &&
    --              decide ((E.d i).1 ⊆ st.Fs)) = true := hdec
    --     -- simp 通常能把 && = true 变成 ∧
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

  -- `prev2 = 1` forces length ≥ 2.
  have hlen2 : 2 ≤ s.len :=
    two_le_len_of_prev2_eq_one (E := E) (s := s) (by simpa [st] using hp2)

  -- Work with `t := len` and `u := t-2`.
  let t : ℕ := s.len
  let u : ℕ := t - 2

  -- Turn hk2 into a statement about `decK t`.
  have hk2_t : decK t = k2 := by
    simpa [st, ht, t] using hk2

  -- Extract the remainder information `t % 3 = 2`.
  have htmod : t % 3 = 2 := by
    have h := congrArg Fin.val hk2_t
    simpa [decK, schedDecode, k2] using h

  -- Decompose `t` as `3*(t/3)+2`, hence `u = 3*(t/3)`.
  have htdecomp : t = 3 * (t / 3) + 2 := by
    calc
      t = (t / 3) * 3 + t % 3 := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.div_add_mod t 3).symm
      _ = (t / 3) * 3 + 2 := by simp [htmod]
      _ = 3 * (t / 3) + 2 := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm]

  have hu_eq : u = 3 * (t / 3) := by
    -- Apply `(_ - 2)` to the decomposition, then cancel.
    have ht_sub : t - 2 = (3 * (t / 3) + 2) - 2 := by
      simpa using (congrArg (fun x => x - 2) htdecomp)
    have : t - 2 = 3 * (t / 3) := by
      calc
        t - 2 = (3 * (t / 3) + 2) - 2 := ht_sub
        _ = 3 * (t / 3) := by simp
    simpa [u] using this
  -- Therefore `decK u = k0` and `decN u = decN t`.
  have hdecK_u : decK u = k0 := by
    apply Fin.eq_of_val_eq
    simp [decK, schedDecode, hu_eq, k0]

  have hdiv : u / 3 = t / 3 := by
    simp [hu_eq]

  have hdecN_u : decN u = decN t := by
    simp [decN, schedDecode, hdiv]

  -- `u+2 = t`, and hence `(u+2) ≤ len`.
  have hu2_eq : u + 2 = t := by
    simpa [u] using (Nat.sub_add_cancel (by simpa [t] using hlen2))

  have hu2_eq' : u.succ.succ = t := by
    -- `u.succ.succ = u+2`
    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hu2_eq

  have hu2_eq_len : u.succ.succ = s.len := by
    simpa [t] using hu2_eq'

  have hu2_le : u.succ.succ ≤ s.len := by
    -- 把左边改写成 s.len，然后就是 le_rfl
    rw [hu2_eq_len]

  -- Choose the exact prefix states needed to unfold twice.
  have hu1_le : u.succ ≤ s.len := Nat.le_of_succ_le hu2_le
  have hu0_le : u ≤ s.len := Nat.le_of_succ_le hu1_le

  let st0 : State := runStateAux E s u hu0_le
  let st1 : State := runStateAux E s u.succ hu1_le
  let st2 : State := runStateAux E s u.succ.succ hu2_le

  -- `st2` is the same as the final state `st`.
  -- 先把 u.succ.succ = s.len 记下来
  have hu2_eq_len : u.succ.succ = s.len := by
    simpa [t] using hu2_eq'

  -- st2 就是 runStateAux 在 u+2；st 是 runStateAux 在 len
  have hst2_to_len :
      st2 = runStateAux E s s.len (by
        -- 把 hu2_le : u.succ.succ ≤ s.len 搬运成 s.len ≤ s.len
        simpa [hu2_eq_len] using hu2_le) := by
    -- 关键：这里 simp 的目标是“State 项”，不会简成 True
      simp [st2, hu2_eq_len]
      exact runStateAux.congr_simp E E rfl s s rfl (u + 1 + 1) s.len hu2_eq hu2_le

  -- 2) 在同一个 n = s.len 下，用 proof_irrel 消掉证明参数差异（这里千万别再套 simpa）
  have hpi :
      runStateAux E s s.len (by simpa [hu2_eq_len] using hu2_le)
        = runStateAux E s s.len le_rfl :=
    runStateAux_proof_irrel (E := E) (s := s) (n := s.len)
      (by simpa [hu2_eq_len] using hu2_le) le_rfl

  -- 3) 展开 st，把它写成 runStateAux ... s.len le_rfl（仍然是 State 等式）
  have hst_def : st = runStateAux E s s.len le_rfl := by
    simp [st, runState]

  -- 最后把三段串起来
  have hst2 : st2 = st := by
    calc
      st2
          = runStateAux E s s.len (by simpa [hu2_eq_len] using hu2_le) := hst2_to_len
      _   = runStateAux E s s.len le_rfl := hpi
      _   = st := by
            -- 这里 simp 只是在 State 里重写 st_def，不会把等式变 True
            simpa [hst_def]

  -- Unfold the two final steps explicitly.
  have hst1_step :
      st1 = step E st0 (s.seq ⟨u, Nat.lt_of_lt_of_le (Nat.lt_succ_self u) hu1_le⟩) := by
    simp [st1, st0, runStateAux]

  have hst2_step :
      st2 = step E st1 (s.seq ⟨u.succ, Nat.lt_of_lt_of_le (Nat.lt_succ_self u.succ) hu2_le⟩) := by
    simp [st2, st1, runStateAux]

  -- Hence `prev2` of the final state is the digit at position `u`.
  have hprev2 :
      st2.prev2 = (s.seq ⟨u, Nat.lt_of_lt_of_le (Nat.lt_succ_self u) hu1_le⟩) := by
    simp [hst2_step, hst1_step, step]

  -- From `hp2`, deduce that digit is `1`.
  have hq : (s.seq ⟨u, Nat.lt_of_lt_of_le (Nat.lt_succ_self u) hu1_le⟩) = 1 := by
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
        (q := s.seq ⟨u.succ, Nat.lt_of_lt_of_le (Nat.lt_succ_self u.succ) hu2_le⟩))

  have hW_mem_st2 : E.W (decN t) ∈ st2.Fs := hmono hW_mem_st1

  -- Translate back to the final state `st = runState E s` and rewrite `t = st.t`.
  simpa [hst2, st, ht, t] using hW_mem_st2


/-! ## The main result: the concrete bar-induction step -/

/-- **Todo C**: local induction step for the bar lemma, for the concrete Σ/F.

This is the propositional analogue of the closure step used in Veldman Lemma §3.43.

Structure of proof matches §3.32:
- k0 (Case 1): forced vs not forced
- k1 (Case 2): only q=0, nothing changes
- k2 (Case 3): split if `W_n` is a disjunction and `prev2=1`; otherwise only q=0
-/
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
        have hset :
    (↑(insert X (FS E s)) : Set Form) = (Γ ⸴ X) := by
  -- Γ = ↑(FS E s)
  -- 用 TodoC_Fix.lean 的 coe_insert_finset
          simpa [Γ] using (IPC.VeldmanConcrete.coe_insert_finset (Γ := FS E s) (X := X))
        -- rewrite hChildPrf along hFSchild and hset
        simpa [hFSchild, hset, Γ] using hChildPrf

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
  -- 先把子节点的 Fs 化为 FStep
        have hstep :
      (runState E (extend s (singleton q))).Fs
        = FStep E (runState E s) q :=
    IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q)

  -- 在 k0 分支 + q ≠ 1 时，FStep 直接等于 st.Fs（即 FS E s）
  -- 这里用你的 hk0 : decK st.t = k0，以及 hqne : q ≠ 1
        simpa [FS, st, IPC.VeldmanConcrete.FStep, hk0] using hstep

      simpa [Γ, hFS] using hChildPrf

  · -- hk0 false
    by_cases hk1 : decK st.t = k1
    · -- k1: Case 2, only q=0 and FS unchanged
      let q : ℕ := 0
      have hk10 : (k1 : Fin 3) ≠ k0 := by decide
      have hAllowed : AllowedStepb E st q = true := by
        unfold AllowedStepb
        simp [hk0, hk1, q, hk10]

      have hChild : Sigma E (extend s (singleton q)) = 0 :=
        Sigma_child_eq_zero_of_allowed (E := E) (s := s) (q := q) hs0 (by
          simpa [st] using hAllowed)

      have hChildPrf : ((↑(FS E (extend s (singleton q))) : Set Form) ⊢ᵢ A) :=
        hall q hChild

      have hFS : FS E (extend s (singleton q)) = FS E s := by
  -- 仍然先把 runState(child).Fs 化为 FStep
        have hstep :
      (runState E (extend s (singleton q))).Fs
        = FStep E (runState E s) q :=
    IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q)

  -- 在 k1 分支，FStep 恒等于 st.Fs（不依赖 q）
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
  -- 先把“子节点 runState 的 Fs”化成 FStep
              have hstep :
      (runState E (extend s (singleton q2))).Fs
        = FStep E (runState E s) q2 :=
              IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q2)

  -- 然后对 FStep 做纯计算化简（注意：这里根本不需要 hk2）
  -- FStep 的代码结构是 if k=k0 / else if k=k1 / else match Wn with ...
  -- 我们用 hk0,hk1 直接把它推进到 “Case 3” 的 match 分支
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
  -- 第一步：只用 hFS1，把 child 的 FS 改写成 insert P (FS s)
              have hPrf1' : (↑(insert P (FS E s)) : Set Form) ⊢ᵢ A := by
    -- 这里用 rw 控制方向，避免 simp 自己乱选方向
    -- 先把 hFS1 作用到 hPrf1 的上下文上
                simpa [hFS1] using hPrf1
              have hset : (↑(insert P (FS E s)) : Set Form) = Set.insert P Γ := by
                ext p; simp [Γ]
                exact Iff.symm (Eq.to_iff rfl)
  -- 第二步：再用 hset 把 ↑(insert ...) 改写成 Γ ⸴ P
  -- 注意方向：hset : ↑(insert P (FS E s)) = Γ ⸴ P
  -- 我们要把 hPrf1' 的上下文 ↑(insert ...) 换成 Γ ⸴ P，所以用 rw [hset] 即可
              simpa [hset] using hPrf1'

            have hΓQ : (Set.insert Q Γ) ⊢ᵢ A := by
              have hset : (↑(insert Q (FS E s)) : Set Form) = Set.insert Q Γ := by
                ext p; simp [Γ]
                exact Iff.symm (Eq.to_iff rfl)
              simpa [hFS2, hset, Γ] using hPrf2

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
  -- 把 runState(child).Fs 化成 FStep(runState s) q
              have hstep :
      (runState E (extend s (singleton q))).Fs
        = FStep E (runState E s) q :=
    IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q)

  -- 这里是在 Case 3 的非 split 分支，你的 q 实际就是 0
  -- 在这种情况下，FStep 直接返回 st.Fs
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
  -- 把 runState(child).Fs 化成 FStep(runState s) q
            have hstep :
      (runState E (extend s (singleton q))).Fs
        = FStep E (runState E s) q :=
    IPC.VeldmanConcrete.Fs_extend_singleton (E := E) (s := s) (q := q)

  -- 这里是 Case 3 且 “不是析取/不是 split” 的分支，所以只允许 q=0，FStep 返回 st.Fs
            simpa [FS, st, IPC.VeldmanConcrete.FStep, hk0, hk1, hk2, hW, q] using hstep

          simpa [Γ, hFS] using hChildPrf

end IPC.VeldmanConcrete
