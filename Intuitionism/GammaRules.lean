import Mathlib
import Intuitionism.UniversalModel
import Intuitionism.VeldmanConcrete

/-!
# Concrete Γ-rules for the concrete Veldman fan

This file proves (for the *concrete* fan defined in `VeldmanConcrete.lean`):

* `Gamma V a` is a **theory** (closed under intuitionistic derivability), and
* `Gamma V a` is **disjunctive**.

These are the two fields of `GammaRules` in `UniversalModel.lean`.

We do **not** change any existing definitions; we only add lemmas and package them.
-/

open NatSeq
open fin_seq
open IPC
open scoped IPC
namespace ConcreteGammaRules



namespace Concrete

/-- Convert the `Enumerations` from `UniversalModel.lean` to the one used in `VeldmanConcrete.lean`.
The payload is the same; only the namespace differs. -/
def Enumerations.toConcrete (E : _root_.Enumerations) : IPC.VeldmanConcrete.Enumerations :=
{ W := E.W
  d := E.d
  W_surj := E.W_surj
  d_sound := by
    intro i
    -- Both `DerOK` definitions unfold to the same proposition.
    simpa [IPC.VeldmanConcrete.DerOK, DerOK] using (E.d_sound i)
  d_complete := by
    intro Γ A h
    simpa [IPC.VeldmanConcrete.DerOK, DerOK] using (E.d_complete Γ A h) }

/-- The concrete fan packaged using the `VeldmanFan` record from `UniversalModel.lean`. -/
def mkConcreteFan (E : _root_.Enumerations) : VeldmanFan E := by
  let E' : IPC.VeldmanConcrete.Enumerations := Concrete.Enumerations.toConcrete E
  refine
  { S := IPC.VeldmanConcrete.Sigma E'
    hS := IPC.VeldmanConcrete.Sigma_is_fan_law (E := E')
    F := IPC.VeldmanConcrete.FS E'
    F_empty := by simpa using (IPC.VeldmanConcrete.FS_empty (E := E'))
    F_mono := by
      intro s t hPre hs0 ht0
      exact IPC.VeldmanConcrete.F_mono (E := E') hPre hs0 ht0 }

/-- Shorthand for the concrete enumeration. -/
abbrev E' (E : _root_.Enumerations) : IPC.VeldmanConcrete.Enumerations := Concrete.Enumerations.toConcrete E
/-- Shorthand for the concrete fan. -/
abbrev V (E : _root_.Enumerations) : VeldmanFan E := mkConcreteFan E

end Concrete


/-! ## Helper lemmas -/

namespace Helpers

open IPC.VeldmanConcrete

/-- `finitize a n` is a prefix of `finitize a m` if `n ≤ m`. -/
lemma Prefix_finitize {a : 𝒩} {n m : ℕ} (hnm : n ≤ m) :
    Prefix (finitize a n) (finitize a m) := by
  refine ⟨hnm, ?_⟩
  intro i
  simp [fin_seq.finitize]

/-- Along an admitted branch, `F` is monotone on finite prefixes. -/
lemma F_mono_on_branch {E : _root_.Enumerations} (V : VeldmanFan E) (a : Branch V)
    {n m : ℕ} (hnm : n ≤ m) :
    V.F (finitize a.1 n) ⊆ V.F (finitize a.1 m) := by
  have hPre : Prefix (finitize a.1 n) (finitize a.1 m) := Prefix_finitize (a := a.1) hnm
  have hn0 : V.S (finitize a.1 n) = 0 := a.2 n
  have hm0 : V.S (finitize a.1 m) = 0 := a.2 m
  exact V.F_mono hPre hn0 hm0

/-- A finite set included in `Gamma V a` is contained in some finite stage `F(a↾N)`.
This is the standard “finite set is bounded in an increasing union” argument. -/
lemma Finset.subset_some_prefix {E : _root_.Enumerations} (V : VeldmanFan E) (a : Branch V)
    (Δ : Finset Form) (hΔ : (↑Δ : Set Form) ⊆ Gamma V a) :
    ∃ N : ℕ, Δ ⊆ V.F (finitize a.1 N) := by

  -- Strengthen the induction statement by keeping the `Gamma`-membership assumption.
  revert hΔ
  refine Finset.induction_on Δ ?base ?step
  · intro _hΔ
    refine ⟨0, ?_⟩
    intro p hp
    exact False.elim (by simp at hp)
  · intro x Δ hxNotMem ih hAll
    -- hAll : (↑(insert x Δ) : Set Form) ⊆ Gamma V a
    have hxGamma : x ∈ Gamma V a := by
      exact hAll (Finset.mem_insert_self x Δ)
    rcases hxGamma with ⟨nx, hxIn⟩

    have hAll' : (↑Δ : Set Form) ⊆ Gamma V a := by
      intro p hp
      exact hAll (Finset.mem_insert.mpr (Or.inr hp))
    rcases ih hAll' with ⟨N, hN⟩

    let M := Nat.max nx N
    refine ⟨M, ?_⟩
    intro p hp
    have hp' : p = x ∨ p ∈ Δ := Finset.mem_insert.mp hp
    cases hp' with
    | inl hpx =>
        subst hpx
        have hnx : nx ≤ M := Nat.le_max_left _ _
        have hsub : V.F (finitize a.1 nx) ⊆ V.F (finitize a.1 M) :=
          F_mono_on_branch (V := V) (a := a) hnx
        exact hsub hxIn
    | inr hpΔ =>
        have hmem : p ∈ V.F (finitize a.1 N) := hN hpΔ
        have hNM : N ≤ M := Nat.le_max_right _ _
        have hsub : V.F (finitize a.1 N) ⊆ V.F (finitize a.1 M) :=
          F_mono_on_branch (V := V) (a := a) hNM
        exact hsub hmem


/-!
### Time-tracking in the concrete state machine

`runStateAux` increments the `t` field by 1 at each step, so after `n` steps we have `t = n`.
-/

lemma runStateAux_t (E : IPC.VeldmanConcrete.Enumerations) (s : fin_seq) :
    ∀ n (hn : n ≤ s.len), (runStateAux E s n hn).t = n := by
  intro n
  induction n with
  | zero =>
      intro hn
      simp [runStateAux, initState]
  | succ n ih =>
      intro hn
      have hn' : n ≤ s.len := Nat.le_of_succ_le hn
      simp [runStateAux, ih hn', step]

lemma runState_t (E : IPC.VeldmanConcrete.Enumerations) (s : fin_seq) :
    (runState E s).t = s.len := by
  simpa [runState] using runStateAux_t (E := E) (s := s) (n := s.len) (hn := le_rfl)


/-!
### Scheduler facts

We need a simple lower bound: for `t = <<n,m,0>>` we have `m ≤ t`, so we can pick a time
large enough for bounded searches.
-/

namespace Scheduler

open IPC

lemma le_pair_right (a b : ℕ) : b ≤ Nat.pair a b := by
  exact Nat.right_le_pair a b


lemma le_pairEncodeBin_right (n m : ℕ) : m ≤ IPC.pairEncodeBin n m := by
  induction n with
  | zero =>
      simpa [IPC.pairEncodeBin, Nat.bit, Nat.mul_comm] using
        (Nat.le_mul_of_pos_left m (by decide : 0 < 2))
  | succ n ih =>
      have hstep : IPC.pairEncodeBin n m ≤ IPC.pairEncodeBin (n + 1) m := by
        calc
          IPC.pairEncodeBin n m ≤ 2 * IPC.pairEncodeBin n m := by
            simpa [Nat.mul_comm] using
              (Nat.le_mul_of_pos_left (IPC.pairEncodeBin n m) (by decide : 0 < 2))
          _ ≤ 2 * IPC.pairEncodeBin n m + 1 := Nat.le_succ _
          _ = IPC.pairEncodeBin (n + 1) m := by simp [IPC.pairEncodeBin, Nat.bit]
      exact Nat.le_trans ih hstep


lemma le_schedEncode_k0 (n m : ℕ) : m ≤ IPC.schedEncode ⟨n, m, IPC.k0⟩ := by
  have hm : m ≤ IPC.pairEncodeBin n m := le_pairEncodeBin_right n m
  have hmul : IPC.pairEncodeBin n m ≤ 3 * IPC.pairEncodeBin n m := by
    simpa [Nat.mul_comm] using
      (Nat.le_mul_of_pos_left (IPC.pairEncodeBin n m) (by decide : 0 < 3))
  have : m ≤ 3 * IPC.pairEncodeBin n m := Nat.le_trans hm hmul
  simpa [IPC.schedEncode, IPC.schedEncodeBin, IPC.k0] using this

end Scheduler


/-!
### Linking `Sigma = 0` to “the next digit is allowed”

`Sigma` was defined as `0` iff `Admittedb = true`, and `Admittedb` checks all digits
using `AllowedStepb`.
-/

lemma allowedStep_of_admitted_prefix
    (E : IPC.VeldmanConcrete.Enumerations) (a : 𝒩) (t : ℕ)
    (hAdm : Admittedb E (finitize a (t+1)) = true) :
    AllowedStepb E (runState E (finitize a t)) (a t) = true := by
  -- Let s₁ = a↾(t+1).
  let s₁ : fin_seq := finitize a (t+1)
  have hAux : admittedAuxb E s₁ (t+1) (le_rfl) = true := by
    simpa [Admittedb, s₁] using hAdm

  -- Unfold one step of `admittedAuxb` to expose the last conjunct.
  have hAnd :
      admittedAuxb E s₁ t (Nat.le_of_succ_le (le_rfl)) &&
        (let st := runStateAux E s₁ t (Nat.le_of_succ_le (le_rfl));
         let q := s₁.seq ⟨t, Nat.lt_succ_self t⟩;
         AllowedStepb E st q) = true := by
    simpa [admittedAuxb, s₁] using hAux

  have hLet :
      (let st := runStateAux E s₁ t (Nat.le_of_succ_le (le_rfl));
       let q := s₁.seq ⟨t, Nat.lt_succ_self t⟩;
       AllowedStepb E st q) = true :=
    (IPC.VeldmanConcrete.and_eq_true_iff _ _).1 hAnd |>.2

  have hq : s₁.seq ⟨t, Nat.lt_succ_self t⟩ = a t := by
    simp [s₁, fin_seq.finitize]

  -- Replace the intermediate state by `runState` on the shorter prefix `a↾t`.
  let s₀ : fin_seq := finitize a t
  have hPref : Prefix s₀ s₁ := Prefix_finitize (a := a) (n := t) (m := t+1) (Nat.le_succ t)

  have hEq_aux :
      runStateAux E s₁ t (Nat.le_trans le_rfl (VeldmanConcrete.Prefix_len_le hPref))
        = runStateAux E s₀ t le_rfl :=
    runStateAux_eq_of_Prefix (E := E) (h := hPref) t le_rfl

  have hEq_left :
      runStateAux E s₁ t (Nat.le_of_succ_le le_rfl)
        = runStateAux E s₁ t (Nat.le_trans le_rfl (VeldmanConcrete.Prefix_len_le hPref)) :=
    runStateAux_proof_irrel (E := E) (s := s₁) (n := t) _ _

  have hSt : runStateAux E s₁ t (Nat.le_of_succ_le le_rfl) = runState E s₀ := by
    have : runStateAux E s₀ t le_rfl = runState E s₀ := by
      simp [runState, s₀, fin_seq.finitize]
    calc
      runStateAux E s₁ t (Nat.le_of_succ_le le_rfl)
          = runStateAux E s₁ t (Nat.le_trans le_rfl (VeldmanConcrete.Prefix_len_le hPref)) := by
              simp
      _ = runStateAux E s₀ t le_rfl := by simpa using hEq_aux
      _ = runState E s₀ := this

  simpa [hq, hSt] using hLet


/-!
### One-step unfolding of `runState` on `finitize`
-/

lemma runState_finitize_succ
    (E : IPC.VeldmanConcrete.Enumerations) (a : 𝒩) (t : ℕ) :
    runState E (finitize a (t+1)) = step E (runState E (finitize a t)) (a t) := by
  let s₀ : fin_seq := finitize a t
  let s₁ : fin_seq := finitize a (t+1)
  have hPref : Prefix s₀ s₁ := Prefix_finitize (a := a) (n := t) (m := t+1) (Nat.le_succ t)

  have hEq_aux :
      runStateAux E s₁ t (Nat.le_trans le_rfl (VeldmanConcrete.Prefix_len_le hPref))
        = runStateAux E s₀ t le_rfl :=
    runStateAux_eq_of_Prefix (E := E) (h := hPref) t le_rfl

  have hEq_left :
      runStateAux E s₁ t (Nat.le_of_succ_le le_rfl)
        = runStateAux E s₁ t (Nat.le_trans le_rfl (VeldmanConcrete.Prefix_len_le hPref)) :=
    runStateAux_proof_irrel (E := E) (s := s₁) (n := t) _ _

  have hSt : runStateAux E s₁ t (Nat.le_of_succ_le le_rfl) = runState E s₀ := by
    have : runStateAux E s₀ t le_rfl = runState E s₀ := by
      simp [runState, s₀, fin_seq.finitize]
    calc
      runStateAux E s₁ t (Nat.le_of_succ_le le_rfl)
          = runStateAux E s₁ t (Nat.le_trans le_rfl (VeldmanConcrete.Prefix_len_le hPref)) := by
              simp
      _ = runStateAux E s₀ t le_rfl := by simpa using hEq_aux
      _ = runState E s₀ := this

  simp [runState]
  exact (Eq.to_iff
        (congrArg
          (Eq (runStateAux E (finitize a (t + 1)) (finitize a (t + 1)).len (runState._proof_1 (finitize a (t + 1)))))
          (congrFun (congrArg (step E) (id (Eq.symm hEq_aux))) (a t)))).mpr
    rfl

/-!
### Forced action lemma

If at a k0-time the bounded search sees a derivation whose premises are already in `Fs`,
then `Forced0b` is true.
-/

lemma Forced0b_of_witness
    (E : IPC.VeldmanConcrete.Enumerations) (st : IPC.VeldmanConcrete.State) (i : ℕ)
    (hk0 : IPC.VeldmanConcrete.decK st.t = IPC.k0)
    (hi : i ≤ st.t)
    (hconc : (E.d i).2 = E.W (IPC.VeldmanConcrete.decN st.t))
    (hprem : (E.d i).1 ⊆ st.Fs) :
    IPC.VeldmanConcrete.Forced0b E st = true := by
  unfold IPC.VeldmanConcrete.Forced0b
  simp [hk0]
  refine (Finset.anyUpTo_eq_true (t := st.t) (p := fun j =>
    decide ((E.d j).2 = E.W (IPC.VeldmanConcrete.decN st.t)) && decide ((E.d j).1 ⊆ st.Fs))).2 ?_
  refine ⟨i, hi, ?_⟩

  have h1 :
    decide ((E.d i).2 = E.W (IPC.VeldmanConcrete.decN st.t)) = true :=
  (Finset.decide_eq_true_iff (P := ((E.d i).2 = E.W (IPC.VeldmanConcrete.decN st.t)))).2 hconc

  have h2 :
    decide ((E.d i).1 ⊆ st.Fs) = true :=
  (Finset.decide_eq_true_iff (P := ((E.d i).1 ⊆ st.Fs))).2 hprem

  exact Bool.and_intro h1 h2

end Helpers


/-! ## Finite support lemma for IPC proofs (needed for theory closure) -/

namespace IPC
namespace prf

/-- Any IPC proof `Γ ⊢ᵢ p` uses only finitely many assumptions from `Γ`. -/
lemma finite_ctx {Γ : Set Form} {p : Form} (h : Γ ⊢ᵢ p) :
    ∃ Δ : Finset Form, (↑Δ : Set Form) ⊆ Γ ∧ ((↑Δ : Set Form) ⊢ᵢ p) := by

  induction h with
  | ax hp =>
    rename_i p'   -- Rename the branch conclusion formula to `p'`.
    refine ⟨insert p' (∅ : Finset Form), ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with hqeq | hqempty
      · subst hqeq
        exact hp
      · cases hqempty
    · exact prf.ax (Γ := (↑(insert p' (∅ : Finset Form)) : Set Form))
        (p := p') (Finset.mem_insert_self p' (∅ : Finset Form))
  | k =>
    refine ⟨(∅ : Finset Form), ?_⟩
    constructor
    · intro q hq; cases hq
    · exact prf.k (Γ := (↑(∅ : Finset Form) : Set Form))

  | s =>
    refine ⟨(∅ : Finset Form), ?_⟩
    constructor
    · intro q hq; cases hq
    · exact prf.s (Γ := (↑(∅ : Finset Form) : Set Form))

  | exf =>
    refine ⟨(∅ : Finset Form), ?_⟩
    constructor
    · intro q hq; cases hq
    · exact prf.exf (Γ := (↑(∅ : Finset Form) : Set Form))
  | pr1 =>
      refine ⟨(∅ : Finset Form), ?_⟩
      constructor
      · intro q hq; cases hq
      · exact prf.pr1 (Γ := (↑(∅ : Finset Form) : Set Form))
  | pr2 =>
      refine ⟨(∅ : Finset Form), ?_⟩
      constructor
      · intro q hq; cases hq
      · exact prf.pr2 (Γ := (↑(∅ : Finset Form) : Set Form))
  | pair =>
      refine ⟨(∅ : Finset Form), ?_⟩
      constructor
      · intro q hq; cases hq
      · exact prf.pair (Γ := (↑(∅ : Finset Form) : Set Form))
  | inl =>
      refine ⟨(∅ : Finset Form), ?_⟩
      constructor
      · intro q hq; cases hq
      · exact prf.inl (Γ := (↑(∅ : Finset Form) : Set Form))
  | inr =>
      refine ⟨(∅ : Finset Form), ?_⟩
      constructor
      · intro q hq; cases hq
      · exact prf.inr (Γ := (↑(∅ : Finset Form) : Set Form))
  | case =>
      refine ⟨(∅ : Finset Form), ?_⟩
      constructor
      · intro q hq; cases hq
      · exact prf.case (Γ := (↑(∅ : Finset Form) : Set Form))
  | mp hpq hp ihpq ihp =>
      rcases ihpq with ⟨Δ₁, hΔ₁sub, hΔ₁prf⟩
      rcases ihp  with ⟨Δ₂, hΔ₂sub, hΔ₂prf⟩
      have merge :
          ∀ (Δ₂' : Finset Form), (↑Δ₂' : Set Form) ⊆ Γ →
            ∃ Δ : Finset Form,
              (↑Δ₁ : Set Form) ⊆ (↑Δ : Set Form) ∧
              (↑Δ₂' : Set Form) ⊆ (↑Δ : Set Form) ∧
              (↑Δ : Set Form) ⊆ Γ := by
        intro Δ₂' hΔ₂'sub
        induction Δ₂' using Finset.induction_on with
        | empty =>
            refine ⟨Δ₁, ?_, ?_, ?_⟩
            · intro q hq
              exact hq
            · intro q hq
              cases hq
            · exact hΔ₁sub
        | insert x Δ₂' hx ih =>
            have hxΓ : x ∈ Γ := hΔ₂'sub (Finset.mem_insert_self x Δ₂')
            have htail : (↑Δ₂' : Set Form) ⊆ Γ := by
              intro q hq
              exact hΔ₂'sub (Finset.mem_insert.mpr (Or.inr hq))
            rcases ih htail with ⟨Δ, hsub1, hsub2, hΔsub⟩
            refine ⟨insert x Δ, ?_, ?_, ?_⟩
            · intro q hq
              exact Finset.mem_insert.mpr (Or.inr (hsub1 hq))
            · intro q hq
              rcases Finset.mem_insert.mp hq with hqeq | hqtail
              · exact Finset.mem_insert.mpr (Or.inl hqeq)
              · exact Finset.mem_insert.mpr (Or.inr (hsub2 hqtail))
            · intro q hq
              rcases Finset.mem_insert.mp hq with hqeq | hqΔ
              · subst hqeq
                exact hxΓ
              · exact hΔsub hqΔ
      rcases merge Δ₂ hΔ₂sub with ⟨Δ, hsub1, hsub2, hΔsub⟩
      refine ⟨Δ, hΔsub, ?_⟩
      have hpq' : (↑Δ : Set Form) ⊢ᵢ _ :=
        prf.sub_weak (Γ := (↑Δ : Set Form)) (Δ := (↑Δ₁ : Set Form)) (p := _) hΔ₁prf hsub1
      have hp' : (↑Δ : Set Form) ⊢ᵢ _ :=
        prf.sub_weak (Γ := (↑Δ : Set Form)) (Δ := (↑Δ₂ : Set Form)) (p := _) hΔ₂prf hsub2
      exact prf.mp hpq' hp'

end prf
end IPC


/-! ## Concrete Γ-rules packaged as `GammaRules` -/

namespace Main

open IPC.VeldmanConcrete
open Helpers
open Concrete

/-- `Gamma` for the concrete fan is a theory (closure under derivability).

This is the formalisation of Veldman §3.32 Case 1 (“forced action”). -/
lemma gamma_isTheory_concrete (E0 : _root_.Enumerations) :
    ∀ a : Branch (V E0), IsTheory (Gamma (V E0) a) := by
  intro a p hp
  -- Extract finite support Δ ⊆ Γₐ with Δ ⊢ p
  rcases IPC.prf.finite_ctx (h := hp) with ⟨Δ, hΔsub, hΔprf⟩

  -- Completeness of the derivation enumeration gives i with d i = (Δ,p)
  rcases E0.d_complete Δ p hΔprf with ⟨i, hi⟩

  -- Choose n0 with W n0 = p
  rcases E0.W_surj p with ⟨n0, hn0⟩

  -- Bound Δ inside some finite stage F(a↾N)
  rcases Finset.subset_some_prefix (V := V E0) (a := a) (Δ := Δ) hΔsub with ⟨N, hN⟩

  -- Pick a k0-time t = <<n0, m, 0>> large enough that i ≤ t and N ≤ t.
  let m : ℕ := Nat.max i N
  let t : ℕ := IPC.schedEncode ⟨n0, m, IPC.k0⟩
  have hm_le_t : m ≤ t := Scheduler.le_schedEncode_k0 n0 m
  have hi_le_t : i ≤ t := Nat.le_trans (Nat.le_max_left _ _) hm_le_t
  have hN_le_t : N ≤ t := Nat.le_trans (Nat.le_max_right _ _) hm_le_t

  -- Premises are present by time t.
  have hΔ_in_t : Δ ⊆ (V E0).F (finitize a.1 t) := by
    have hmono : (V E0).F (finitize a.1 N) ⊆ (V E0).F (finitize a.1 t) :=
      F_mono_on_branch (V := V E0) (a := a) hN_le_t
    exact Finset.Subset.trans hN hmono

  -- Work in the concrete state machine.
  let E'0 : IPC.VeldmanConcrete.Enumerations := E' E0
  let st : IPC.VeldmanConcrete.State := runState E'0 (finitize a.1 t)

  have hdec : IPC.schedDecode t = ⟨n0, m, IPC.k0⟩ := by
    simpa [t] using (IPC.schedDecode_encode ⟨n0, m, IPC.k0⟩)

  have ht_st : st.t = t := by
    simpa [st] using (runState_t (E := E'0) (s := finitize a.1 t))

  have hk0 : decK st.t = IPC.k0 := by
    simp [decK, ht_st, hdec]

  -- Show Forced0b is true at time t using witness i
  have hForced : Forced0b E'0 st = true := by
    have hi1 : (E'0.d i).1 = Δ := by
      simpa [E'0, Concrete.Enumerations.toConcrete] using congrArg Prod.fst hi
    have hi2 : (E'0.d i).2 = p := by
      simpa [E'0, Concrete.Enumerations.toConcrete] using congrArg Prod.snd hi

    have hdecN : decN st.t = n0 := by
      simp [decN, ht_st, hdec]

    have hprem : (E'0.d i).1 ⊆ st.Fs := by
      intro q hq
      have hqΔ : q ∈ Δ := by simpa [hi1] using hq
      have hqt : q ∈ (V E0).F (finitize a.1 t) := hΔ_in_t hqΔ
      simpa [st, V, Concrete.mkConcreteFan, E'0, Concrete.Enumerations.toConcrete,
        IPC.VeldmanConcrete.FS] using hqt

    have hconc : (E'0.d i).2 = E'0.W (decN st.t) := by
      have : E'0.W (decN st.t) = p := by
        simp [E'0, Concrete.Enumerations.toConcrete, hn0, hdecN]
      simp [hi2, this]

    have hi_le : i ≤ st.t := by simpa [ht_st] using hi_le_t

    exact Forced0b_of_witness (E := E'0) (st := st) (i := i) hk0 hi_le hconc hprem

  -- Admittedness of a↾(t+1) gives AllowedStepb at time t
  have hAdm : Admittedb E'0 (finitize a.1 (t+1)) = true := by
    have hSigma0 : (V E0).S (finitize a.1 (t+1)) = 0 := a.2 (t+1)
    have hSigma0' : Sigma E'0 (finitize a.1 (t+1)) = 0 := by
      simpa [V, Concrete.mkConcreteFan, E'0] using hSigma0
    exact (Sigma_eq_zero_iff (E := E'0) (s := finitize a.1 (t+1))).1 hSigma0'

  have hAllowed : AllowedStepb E'0 (runState E'0 (finitize a.1 t)) (a.1 t) = true :=
    allowedStep_of_admitted_prefix (E := E'0) (a := a.1) (t := t) hAdm

  -- Under k0 and Forced0b, AllowedStepb forces the digit to be 1.
  have hk0t : decK (runState E'0 (finitize a.1 t)).t = IPC.k0 := by
    simpa [st] using hk0

  have hForced' : Forced0b E'0 (runState E'0 (finitize a.1 t)) = true := by
  -- Key step: rewrite `st` back to the corresponding `runState ...` term.
    simpa [st] using hForced

  have hq1 : a.1 t = 1 := by
    have hAllowed' := hAllowed
  -- First unfold `AllowedStepb` to its `if`, then use `hForced'` to select the `then` branch.
    simp [AllowedStepb, hk0t] at hAllowed'
  -- At this point `hAllowed'` has the form: if `Forced0b ... = true` then `a.1 t = 1` else `a.1 t = 0 ∨ a.1 t = 1`.
  -- Now eliminate the `if` using `hForced'`.
    simpa [hForced'] using hAllowed'

  -- Now p is inserted at stage t+1.
  have hp_in_stage : p ∈ (V E0).F (finitize a.1 (t+1)) := by
    have hRun : runState E'0 (finitize a.1 (t+1)) = step E'0 (runState E'0 (finitize a.1 t)) (a.1 t) :=
      runState_finitize_succ (E := E'0) (a := a.1) (t := t)

    have hk0_dec : decK t = IPC.k0 := by
      simp [decK, hdec]
    have hdecN : decN t = n0 := by
      simp [decN, hdec]

    have : p ∈ (runState E'0 (finitize a.1 (t+1))).Fs := by
      have ht0 : (runState E'0 (finitize a.1 t)).t = t := by
        simpa using (runState_t (E := E'0) (s := finitize a.1 t))

      have hEq :
          (runState E'0 (finitize a.1 (t+1))).Fs
            = insert (E'0.W (decN t)) (runState E'0 (finitize a.1 t)).Fs := by
        simp [hRun, step, FStep, ht0, hk0_dec, hq1]

      have hpW : E'0.W (decN t) = p := by
        simp [E'0, Concrete.Enumerations.toConcrete, hn0, hdecN]

      simp [hEq, hpW]

    simpa [V, Concrete.mkConcreteFan, E'0, Concrete.Enumerations.toConcrete,
      IPC.VeldmanConcrete.FS] using this

  exact ⟨t+1, hp_in_stage⟩


/-!
### Disjunction property

If `A ∨ B ∈ Γₐ`, then there is an index `n` with `W n = A ∨ B`.
At a sufficiently late k0-time for that `n`, the bounded search sees the trivial derivation
`{A ∨ B} ⊢ A ∨ B`, hence forces the digit to be `1`.
Two time-units later we are at the corresponding k2-time, where `AllowedStepb` forces the
next digit to be `1` or `2`, inserting `A` or `B`.
-/

/-- Scheduler alignment: from a k0-time we reach the corresponding k2-time two steps later
(with the same `n,m`). -/
lemma decN_decK_add2_of_k0 (t : ℕ) (hk : decK t = IPC.k0) :
    decN (t+2) = decN t ∧ decK (t+2) = IPC.k2 := by
  let x : ℕ × ℕ × Fin 3 := IPC.schedDecode t
  have ht : IPC.schedEncode x = t := IPC.schedEncode_decode t
  have hk' : x.2.2 = IPC.k0 := by
    simpa [decK, x] using hk

  rcases x with ⟨n, m, k⟩
  have hkEq : k = IPC.k0 := by simpa using hk'
  subst hkEq

  have ht0 : t = IPC.schedEncode ⟨n, m, IPC.k0⟩ := by
    simpa using ht.symm

  have halign0 : IPC.schedEncode ⟨n, m, IPC.k0⟩ + 2 = IPC.schedEncode ⟨n, m, IPC.k2⟩ :=
    (IPC.sched_align n m).1.trans (IPC.sched_align n m).2
  have ht2 : t + 2 = IPC.schedEncode ⟨n, m, IPC.k2⟩ := by
    simpa [ht0] using halign0

  have hdec2 : IPC.schedDecode (t+2) = ⟨n, m, IPC.k2⟩ := by
    simpa [ht2] using (IPC.schedDecode_encode ⟨n, m, IPC.k2⟩)
  have hdec0 : IPC.schedDecode t = ⟨n, m, IPC.k0⟩ := by
    simpa [ht0] using (IPC.schedDecode_encode ⟨n, m, IPC.k0⟩)

  constructor
  · simp [decN, hdec2, hdec0]
  · simp [decK, hdec2]


/-- `Gamma` for the concrete fan is disjunctive (Veldman §3.32, Case 3 for disjunction). -/
lemma gamma_disjunctive_concrete (E0 : _root_.Enumerations) :
    ∀ a : Branch (V E0), Disjunctive (Gamma (V E0) a) := by

  intro a A B hAB

  -- unpack Gamma membership: some stage N contains A∨B
  rcases hAB with ⟨N, hN⟩

  -- pick an index nAB with W nAB = A∨B
  rcases E0.W_surj (Form.or A B) with ⟨nAB, hnAB⟩

  -- singleton proof {A∨B} ⊢ A∨B
  have hax : ((↑({Form.or A B} : Finset Form) : Set Form) ⊢ᵢ Form.or A B) := by
    apply IPC.prf.ax
    change Form.or A B ∈ ({Form.or A B} : Finset Form)
    exact Finset.mem_singleton_self _

  -- get derivation index i with d i = ({A∨B}, A∨B)
  rcases E0.d_complete ({Form.or A B}) (Form.or A B) hax with ⟨i, hi⟩

  -- choose a large enough k0-time t = <<nAB, m, 0>>
  let m : ℕ := Nat.max i N
  let t : ℕ := IPC.schedEncode ⟨nAB, m, IPC.k0⟩
  have hm_le_t : m ≤ t := Scheduler.le_schedEncode_k0 nAB m
  have hi_le_t : i ≤ t := Nat.le_trans (Nat.le_max_left _ _) hm_le_t
  have hN_le_t : N ≤ t := Nat.le_trans (Nat.le_max_right _ _) hm_le_t

  -- A∨B is present by stage t (monotonicity along the branch)
  have hOr_in_t : Form.or A B ∈ (V E0).F (finitize a.1 t) := by
    have hmono : (V E0).F (finitize a.1 N) ⊆ (V E0).F (finitize a.1 t) :=
      F_mono_on_branch (V := V E0) (a := a) hN_le_t
    exact hmono hN

  -- work in the concrete state machine
  let E'0 : IPC.VeldmanConcrete.Enumerations := E' E0
  let st : IPC.VeldmanConcrete.State := runState E'0 (finitize a.1 t)

  -- decode facts for t
  have hdec : IPC.schedDecode t = ⟨nAB, m, IPC.k0⟩ := by
    simpa [t] using (IPC.schedDecode_encode ⟨nAB, m, IPC.k0⟩)

  have ht_st : st.t = t := by
    simpa [st] using (runState_t (E := E'0) (s := finitize a.1 t))

  have hk0 : decK st.t = IPC.k0 := by
    simp [decK, ht_st, hdec]

  -- Forced0b is true at st (witness i)
  have hForced : Forced0b E'0 st = true := by
    have hi1 : (E'0.d i).1 = {Form.or A B} := by
      simpa [E'0, Concrete.Enumerations.toConcrete] using congrArg Prod.fst hi
    have hi2 : (E'0.d i).2 = Form.or A B := by
      simpa [E'0, Concrete.Enumerations.toConcrete] using congrArg Prod.snd hi

    have hdecN : decN st.t = nAB := by
      simp [decN, ht_st, hdec]

    have hi_le : i ≤ st.t := by
      simpa [ht_st] using hi_le_t

    have hOr_in_st : Form.or A B ∈ st.Fs := by
      simpa [st, V, Concrete.mkConcreteFan, E'0, Concrete.Enumerations.toConcrete,
        IPC.VeldmanConcrete.FS] using hOr_in_t

    have hprem : (E'0.d i).1 ⊆ st.Fs := by
      intro q hq
      have hq' : q ∈ ({Form.or A B} : Finset Form) := by
        simpa [hi1] using hq
      have : q = Form.or A B := by
        simpa [Finset.mem_singleton] using hq'
      subst this
      exact hOr_in_st

    have hconc : (E'0.d i).2 = E'0.W (decN st.t) := by
      have : E'0.W (decN st.t) = Form.or A B := by
        simp [E'0, Concrete.Enumerations.toConcrete, hnAB, hdecN]
      simp [hi2, this]

    exact Forced0b_of_witness (E := E'0) (st := st) (i := i) hk0 hi_le hconc hprem

  -- From admittedness of a↾(t+1), the digit at time t is allowed.
  have hAdm_t1 : Admittedb E'0 (finitize a.1 (t+1)) = true := by
    have hSigma0 : (V E0).S (finitize a.1 (t+1)) = 0 := a.2 (t+1)
    have hSigma0' : Sigma E'0 (finitize a.1 (t+1)) = 0 := by
      simpa [V, Concrete.mkConcreteFan, E'0] using hSigma0
    exact (Sigma_eq_zero_iff (E := E'0) (s := finitize a.1 (t+1))).1 hSigma0'

  have hAllowed_t : AllowedStepb E'0 (runState E'0 (finitize a.1 t)) (a.1 t) = true :=
    allowedStep_of_admitted_prefix (E := E'0) (a := a.1) (t := t) hAdm_t1

  -- Under k0 and Forced0b, the digit is forced to 1.
  have hk0t : decK (runState E'0 (finitize a.1 t)).t = IPC.k0 := by
    simpa [st] using hk0

  -- Rewrite `hForced` into the `runState` form; otherwise `simp` cannot use it here.
  have hForced' : Forced0b E'0 (runState E'0 (finitize a.1 t)) = true := by
    simpa [st] using hForced

  have hq1 : a.1 t = 1 := by
    have hAllowed' := hAllowed_t
  -- First unfold `AllowedStepb` to an explicit if-then-else.
    simp [AllowedStepb, hk0t] at hAllowed'
  -- At this stage `hAllowed'` says:
  --   if Forced0b E'0 (runState ...) = true then a.1 t = 1 else a.1 t = 0 ∨ a.1 t = 1
  -- Now eliminate the `if` using `hForced'`, yielding `a.1 t = 1`.
    simpa [hForced'] using hAllowed'

  -- Move to the corresponding k2-time two steps later.
  have hk0_dec : decK t = IPC.k0 := by
    simp [decK, hdec]
  have hDec : decN (t+2) = decN t ∧ decK (t+2) = IPC.k2 :=
    decN_decK_add2_of_k0 (t := t) (hk := hk0_dec)

  -- At time t+2, prev2 = 1 because the digit at time t was 1.
  have hPrev2 : (runState E'0 (finitize a.1 (t+2))).prev2 = 1 := by
    have hRun1 : runState E'0 (finitize a.1 (t+1)) = step E'0 (runState E'0 (finitize a.1 t)) (a.1 t) :=
      runState_finitize_succ (E := E'0) (a := a.1) (t := t)
    have hRun2 : runState E'0 (finitize a.1 (t+2))
        = step E'0 (runState E'0 (finitize a.1 (t+1))) (a.1 (t+1)) :=
      runState_finitize_succ (E := E'0) (a := a.1) (t := t+1)
    simp [hRun2, hRun1, step, hq1]

  -- At time t+2, the digit is allowed (since a↾(t+3) is admitted).
  have hAdm_t3 : Admittedb E'0 (finitize a.1 (t+3)) = true := by
    have hSigma0 : (V E0).S (finitize a.1 (t+3)) = 0 := a.2 (t+3)
    have hSigma0' : Sigma E'0 (finitize a.1 (t+3)) = 0 := by
      simpa [V, Concrete.mkConcreteFan, E'0] using hSigma0
    exact (Sigma_eq_zero_iff (E := E'0) (s := finitize a.1 (t+3))).1 hSigma0'

  have hAllowed_t2 : AllowedStepb E'0 (runState E'0 (finitize a.1 (t+2))) (a.1 (t+2)) = true :=
    allowedStep_of_admitted_prefix (E := E'0) (a := a.1) (t := t+2) hAdm_t3

  -- The disjunction split forces the digit at time t+2 to be 1 or 2.
  have hDigit12 : a.1 (t+2) = 1 ∨ a.1 (t+2) = 2 := by
    have ht2 : (runState E'0 (finitize a.1 (t+2))).t = t+2 := by
      simpa using (runState_t (E := E'0) (s := finitize a.1 (t+2)))
    have hk2t : decK (runState E'0 (finitize a.1 (t+2))).t = IPC.k2 := by
      simpa [ht2] using hDec.2
    have hWnAB : E'0.W nAB = Form.or A B := by
      simpa [E'0, Concrete.Enumerations.toConcrete] using hnAB

    have hdecN2 : decN (runState E'0 (finitize a.1 (t+2))).t = nAB := by
      have hdecN0 : decN t = nAB := by
        simp [decN, hdec]   -- Here `hdec : schedDecode t = (nAB, m, k0)`.
      calc
        decN (runState E'0 (finitize a.1 (t+2))).t
          = decN (t+2) := by simp [ht2]
      _ = decN t := by simp [hDec.1]
      _ = nAB := hdecN0

    have hW2 :
    E'0.W (decN (runState E'0 (finitize a.1 (t+2))).t) = Form.or A B := by
      simpa [hdecN2] using hWnAB
    have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
    have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide

    have hAllowed' := hAllowed_t2
  -- This rewrites `decK(...)` to `k2`, and then `if k2 = k0` / `if k2 = k1` are discharged by `hk20` and `hk21`.
    simp [AllowedStepb, hk2t, hk20, hk21, hW2, hPrev2] at hAllowed'
  -- Now `hAllowed'` is exactly `a.1 (t+2) = 1 ∨ a.1 (t+2) = 2`.
    exact hAllowed'

  -- Finally, at stage t+3 the machine inserts A or B accordingly.
  cases hDigit12 with
  | inl h1 =>
      left
      refine ⟨t+3, ?_⟩
      have hRun3 : runState E'0 (finitize a.1 (t+3))
          = step E'0 (runState E'0 (finitize a.1 (t+2))) (a.1 (t+2)) :=
        runState_finitize_succ (E := E'0) (a := a.1) (t := t+2)

      have ht2 : (runState E'0 (finitize a.1 (t+2))).t = t+2 := by
        simpa using (runState_t (E := E'0) (s := finitize a.1 (t+2)))
      have hk2t_nat : decK (t+2) = IPC.k2 := by
        simpa using hDec.2
      have hW2_nat : E'0.W (decN (t+2)) = Form.or A B := by
        have : decN (t+2) = decN t := hDec.1
        have hdecN0 : decN t = nAB := by
          simp [decN, hdec]
        simp [this, hdecN0, E'0, Concrete.Enumerations.toConcrete, hnAB]

      have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
      have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide

      have : A ∈ (runState E'0 (finitize a.1 (t+3))).Fs := by
        simp [hRun3, step, FStep, ht2, hk2t_nat, hW2_nat, hPrev2, h1, hk20, hk21]


      simpa [V, Concrete.mkConcreteFan, E'0, Concrete.Enumerations.toConcrete,
        IPC.VeldmanConcrete.FS] using this

  | inr h2 =>
      right
      refine ⟨t+3, ?_⟩
      have hRun3 : runState E'0 (finitize a.1 (t+3))
          = step E'0 (runState E'0 (finitize a.1 (t+2))) (a.1 (t+2)) :=
        runState_finitize_succ (E := E'0) (a := a.1) (t := t+2)

      have ht2 : (runState E'0 (finitize a.1 (t+2))).t = t+2 := by
        simpa using (runState_t (E := E'0) (s := finitize a.1 (t+2)))
      have hk2t_nat : decK (t+2) = IPC.k2 := by
        simpa using hDec.2
      have hW2_nat : E'0.W (decN (t+2)) = Form.or A B := by
        have : decN (t+2) = decN t := hDec.1
        have hdecN0 : decN t = nAB := by
          simp [decN, hdec]
        simp [this, hdecN0, E'0, Concrete.Enumerations.toConcrete, hnAB]

      have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
      have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide

      have : B ∈ (runState E'0 (finitize a.1 (t+3))).Fs := by
        simp [hRun3, step, FStep, ht2, hk2t_nat, hW2_nat, hPrev2, h2, hk20, hk21]

      simpa [V, Concrete.mkConcreteFan, E'0, Concrete.Enumerations.toConcrete,
        IPC.VeldmanConcrete.FS] using this


/-- Package the concrete Γ-rules as an instance of `GammaRules` for the concrete fan. -/
theorem gammaRules_concrete (E0 : _root_.Enumerations) : GammaRules (V := V E0) := by
  refine ⟨?_, ?_⟩
  · exact gamma_isTheory_concrete (E0 := E0)
  · exact gamma_disjunctive_concrete (E0 := E0)

end Main

end ConcreteGammaRules
