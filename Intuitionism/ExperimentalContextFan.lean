import Intuitionism.FiniteContextLifting
import Intuitionism.ConcreteEnumerations

/-!
# Concrete arbitrary-set context completeness, propositional fragment

This file adds the non-finite-context version of the propositional Veldman-style
completeness theorem.

The additional hypothesis on an arbitrary context `Γ : Set Form` is a positive
presentation of membership in `Γ`.  This is the propositional analogue of
Veldman's §4.4 condition: membership in the external theory is not allowed to
come from an unrestricted free-choice parameter.

The concrete subfan below forces digit `1` at scheduler times `⟪n,m,0⟫` whenever
`beta (W n) m = true`.  Hence every branch of the subfan contains all formulas
of `Γ`; the rootward induction is the same One/Forced/Context/Split analysis as
in the implication subfan.
-/

open NatSeq
open fin_seq
open IPC
open scoped IPC

namespace IPC

/-- Veldman-style positive presentation of an arbitrary propositional context. -/
structure VeldmanContext (Γ : Set Form) : Type where
  beta : Form → ℕ → Bool
  beta_sound : ∀ B n, beta B n = true → B ∈ Γ
  beta_complete : ∀ B, B ∈ Γ → ∃ n, beta B n = true

/-- Equivalent enumeration-style presentation; useful for examples. -/
structure EnumerableContext (Γ : Set Form) : Type where
  enum : ℕ → Option Form
  mem_iff : ∀ B, B ∈ Γ ↔ ∃ n, enum n = some B

namespace VeldmanContext

/-- Turn an `Option`-enumeration of `Γ` into a positive Boolean trace. -/
def ofEnumerable {Γ : Set Form} (hΓ : EnumerableContext Γ) : VeldmanContext Γ where
  beta B n :=
    match hΓ.enum n with
    | some C => decide (C = B)
    | none => false
  beta_sound := by
    intro B n h
    cases hcase : hΓ.enum n with
    | none => simp [hcase] at h
    | some C =>
        have hCB : C = B := by
          simpa [hcase] using h
        exact (hΓ.mem_iff B).2 ⟨n, by simpa [hCB] using hcase⟩
  beta_complete := by
    intro B hB
    rcases (hΓ.mem_iff B).1 hB with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simp [hn]

end VeldmanContext
end IPC

namespace ContextGammaRules

/-- One-step case for the Γ-subfan: choose an admitted child whose finite `F` is unchanged. -/
def CaseOne {E : Enumerations} (V : VeldmanFan E)
    (T : fin_seq → ℕ) (s : fin_seq) : Prop :=
  ∃ q : ℕ,
    T (extend s (singleton q)) = 0 ∧
    V.F (extend s (singleton q)) = V.F s

/-- Concrete forced case: insert a formula already derivable from `F(s)`. -/
def CaseForced {E : Enumerations} (V : VeldmanFan E)
    (T : fin_seq → ℕ) (s : fin_seq) : Prop :=
  ∃ (q : ℕ) (X : Form),
    T (extend s (singleton q)) = 0 ∧
    V.F (extend s (singleton q)) = insert X (V.F s) ∧
    ((↑(V.F s) : Set Form) ⊢ᵢ X)

/-- Γ-context case: insert a formula justified by the external context `Γ`. -/
def CaseCtxΓ {E : Enumerations} (V : VeldmanFan E)
    (Γ : Set Form) (T : fin_seq → ℕ) (s : fin_seq) : Prop :=
  ∃ (q : ℕ) (X : Form),
    T (extend s (singleton q)) = 0 ∧
    V.F (extend s (singleton q)) = insert X (V.F s) ∧
    X ∈ Γ

/-- Disjunction split case. -/
def CaseSplit {E : Enumerations} (V : VeldmanFan E)
    (T : fin_seq → ℕ) (s : fin_seq) : Prop :=
  ∃ (A B : Form),
    T (extend s (singleton 1)) = 0 ∧
    T (extend s (singleton 2)) = 0 ∧
    V.F (extend s (singleton 1)) = insert A (V.F s) ∧
    V.F (extend s (singleton 2)) = insert B (V.F s) ∧
    (A ⋎ B) ∈ V.F s

/-- Local case analysis required for rootward induction over `Γ ∪ F(s)`. -/
structure IndStepRulesΓ {E : Enumerations} (V : VeldmanFan E)
    (Γ : Set Form) (A : Form) (T : fin_seq → ℕ) : Prop where
  cases_cover :
    ∀ s : fin_seq, T s = 0 →
      CaseOne V T s ∨ CaseForced V T s ∨ CaseCtxΓ V Γ T s ∨ CaseSplit V T s

/-- Backward induction step for the arbitrary-context subfan. -/
theorem ind_step_of_rules {E : Enumerations} (V : VeldmanFan E)
    (Γ : Set Form) (A : Form) (T : fin_seq → ℕ)
    (hStep : IndStepRulesΓ V Γ A T) :
  ∀ s : fin_seq,
    T s = 0 →
      (∀ n : ℕ, T (extend s (singleton n)) = 0 →
          (Γ ∪ (↑(V.F (extend s (singleton n))) : Set Form)) ⊢ᵢ A) →
        (Γ ∪ (↑(V.F s) : Set Form)) ⊢ᵢ A := by
  intro s hs0 hall
  have hc := hStep.cases_cover s hs0
  rcases hc with hOne | hRest
  · rcases hOne with ⟨q, hq0, hF⟩
    have hCq :
        (Γ ∪ (↑(V.F (extend s (singleton q))) : Set Form)) ⊢ᵢ A :=
      hall q hq0
    have hFset :
        (↑(V.F (extend s (singleton q))) : Set Form) = (↑(V.F s) : Set Form) := by
      ext x; simp [hF]
    simpa [hFset] using hCq

  · rcases hRest with hForced | hRest'
    · rcases hForced with ⟨q, X, hq0, hF, hX⟩
      let sq : fin_seq := extend s (singleton q)
      let Δ : Set Form := Γ ∪ (↑(V.F s) : Set Form)
      have hCq :
          (Γ ∪ (↑(V.F sq) : Set Form)) ⊢ᵢ A :=
        hall q hq0
      have hsubCtx :
          (Γ ∪ (↑(V.F sq) : Set Form)) ⊆ (Δ ⸴ X) := by
        intro p hp
        rcases hp with hpΓ | hpFq
        · exact Or.inr (Or.inl hpΓ)
        · have hpFin0 : p ∈ V.F sq := by simpa using hpFq
          have hpFin : p ∈ insert X (V.F s) := by simpa [sq, hF] using hpFin0
          have hpEither : p = X ∨ p ∈ V.F s := by
            simpa [Finset.mem_insert] using hpFin
          rcases hpEither with rfl | hpFs
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (show p ∈ (↑(V.F s) : Set Form) from hpFs))
      have hA_from_ΔX : (Δ ⸴ X) ⊢ᵢ A :=
        IPC.prf.sub_weak
          (Δ := (Γ ∪ (↑(V.F sq) : Set Form)))
          (Γ := (Δ ⸴ X)) (p := A) hCq hsubCtx
      have hX_from_Δ : Δ ⊢ᵢ X := by
        have hsubF : (↑(V.F s) : Set Form) ⊆ Δ := by
          intro p hpFs; exact Or.inr hpFs
        exact IPC.prf.sub_weak
          (Δ := (↑(V.F s) : Set Form)) (Γ := Δ) (p := X) hX hsubF
      have hA_from_Δ : Δ ⊢ᵢ A :=
        IPC.VeldmanConcrete.prf_cut (Γ := Δ) (X := X) (A := A) hX_from_Δ hA_from_ΔX
      simpa [Δ] using hA_from_Δ

    · rcases hRest' with hCtx | hSplit
      · rcases hCtx with ⟨q, X, hq0, hF, hXΓ⟩
        let sq : fin_seq := extend s (singleton q)
        let Δ : Set Form := Γ ∪ (↑(V.F s) : Set Form)
        have hCq :
            (Γ ∪ (↑(V.F sq) : Set Form)) ⊢ᵢ A :=
          hall q hq0
        have hsubCtx :
            (Γ ∪ (↑(V.F sq) : Set Form)) ⊆ (Δ ⸴ X) := by
          intro p hp
          rcases hp with hpΓ | hpFq
          · exact Or.inr (Or.inl hpΓ)
          · have hpFin0 : p ∈ V.F sq := by simpa using hpFq
            have hpFin : p ∈ insert X (V.F s) := by simpa [sq, hF] using hpFin0
            have hpEither : p = X ∨ p ∈ V.F s := by
              simpa [Finset.mem_insert] using hpFin
            rcases hpEither with rfl | hpFs
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (show p ∈ (↑(V.F s) : Set Form) from hpFs))
        have hA_from_ΔX : (Δ ⸴ X) ⊢ᵢ A :=
          IPC.prf.sub_weak
            (Δ := (Γ ∪ (↑(V.F sq) : Set Form)))
            (Γ := (Δ ⸴ X)) (p := A) hCq hsubCtx
        have hX_from_Δ : Δ ⊢ᵢ X := by
          apply IPC.prf.ax
          exact Or.inl hXΓ
        have hA_from_Δ : Δ ⊢ᵢ A :=
          IPC.VeldmanConcrete.prf_cut (Γ := Δ) (X := X) (A := A) hX_from_Δ hA_from_ΔX
        simpa [Δ] using hA_from_Δ

      · rcases hSplit with ⟨P, Q, h1, h2, hF1, hF2, hDisj⟩
        let s1 : fin_seq := extend s (singleton 1)
        let s2 : fin_seq := extend s (singleton 2)
        let Δ : Set Form := Γ ∪ (↑(V.F s) : Set Form)
        have hPQ : Δ ⊢ᵢ (P ⋎ Q) := by
          apply IPC.prf.ax
          exact Or.inr (show P ⋎ Q ∈ (↑(V.F s) : Set Form) from hDisj)
        have hQ1 :
            (Γ ∪ (↑(V.F s1) : Set Form)) ⊢ᵢ A := hall 1 h1
        have hQ2 :
            (Γ ∪ (↑(V.F s2) : Set Form)) ⊢ᵢ A := hall 2 h2
        have hsub1 :
            (Γ ∪ (↑(V.F s1) : Set Form)) ⊆ (Δ ⸴ P) := by
          intro p hp
          rcases hp with hpΓ | hpF
          · exact Or.inr (Or.inl hpΓ)
          · have hpFin0 : p ∈ V.F s1 := by simpa using hpF
            have hpFin : p ∈ insert P (V.F s) := by simpa [s1, hF1] using hpFin0
            have hpEither : p = P ∨ p ∈ V.F s := by
              simpa [Finset.mem_insert] using hpFin
            rcases hpEither with rfl | hpFs
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (show p ∈ (↑(V.F s) : Set Form) from hpFs))
        have hsub2 :
            (Γ ∪ (↑(V.F s2) : Set Form)) ⊆ (Δ ⸴ Q) := by
          intro p hp
          rcases hp with hpΓ | hpF
          · exact Or.inr (Or.inl hpΓ)
          · have hpFin0 : p ∈ V.F s2 := by simpa using hpF
            have hpFin : p ∈ insert Q (V.F s) := by simpa [s2, hF2] using hpFin0
            have hpEither : p = Q ∨ p ∈ V.F s := by
              simpa [Finset.mem_insert] using hpFin
            rcases hpEither with rfl | hpFs
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (show p ∈ (↑(V.F s) : Set Form) from hpFs))
        have hA1 : (Δ ⸴ P) ⊢ᵢ A :=
          IPC.prf.sub_weak
            (Δ := (Γ ∪ (↑(V.F s1) : Set Form)))
            (Γ := (Δ ⸴ P)) (p := A) hQ1 hsub1
        have hA2 : (Δ ⸴ Q) ⊢ᵢ A :=
          IPC.prf.sub_weak
            (Δ := (Γ ∪ (↑(V.F s2) : Set Form)))
            (Γ := (Δ ⸴ Q)) (p := A) hQ2 hsub2
        have hA : Δ ⊢ᵢ A :=
          IPC.prf.or_elim (Γ := Δ) (p := P) (q := Q) (r := A) hPQ hA1 hA2
        simpa [Δ] using hA

end ContextGammaRules

namespace ContextSubfanConcrete

/-- The middle coordinate of the scheduler `⟪n,m,k⟫`. -/
def decM (t : ℕ) : ℕ := (IPC.schedDecode t).2.1

@[simp] lemma decM_schedEncode (n m : ℕ) (k : Fin 3) :
    decM (IPC.schedEncode ⟨n, m, k⟩) = m := by
  simp [decM, IPC.schedDecode_encode]

/-- At a `k0`-time, this Boolean says that the Γ-subfan must take digit `1`. -/
def needsΓb {Γ : Set Form} (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (t : ℕ) : Bool :=
  decide (ImplicationSubfan.VC.decK t = IPC.k0) && hΓ.beta (E.W (ImplicationSubfan.VC.decN t)) (decM t)

lemma needsΓb_k0_of_true {Γ : Set Form} (E : Enumerations)
    (hΓ : IPC.VeldmanContext Γ) (t : ℕ) :
    needsΓb E hΓ t = true → ImplicationSubfan.VC.decK t = IPC.k0 := by
  intro h
  have hAnd := Bool.and_eq_true_iff.mp h
  exact (_root_.decide_eq_true_iff).1 hAnd.1

lemma needsΓb_mem_of_true {Γ : Set Form} (E : Enumerations)
    (hΓ : IPC.VeldmanContext Γ) (t : ℕ) :
    needsΓb E hΓ t = true → E.W (ImplicationSubfan.VC.decN t) ∈ Γ := by
  intro h
  have hAnd := Bool.and_eq_true_iff.mp h
  exact hΓ.beta_sound (E.W (ImplicationSubfan.VC.decN t)) (decM t) hAnd.2

lemma needsΓb_true_of {Γ : Set Form} (E : Enumerations)
    (hΓ : IPC.VeldmanContext Γ) (t : ℕ)
    (hk0 : ImplicationSubfan.VC.decK t = IPC.k0)
    (hβ : hΓ.beta (E.W (ImplicationSubfan.VC.decN t)) (decM t) = true) :
    needsΓb E hΓ t = true := by
  exact Bool.and_eq_true_iff.mpr ⟨(_root_.decide_eq_true_iff).2 hk0, hβ⟩

lemma eq_one_of_needsΓb_true_of_decK_ne_k0 {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ) (t q : ℕ)
    (hk0ne : ImplicationSubfan.VC.decK t ≠ IPC.k0) :
    needsΓb E hΓ t = true → q = 1 := by
  intro hb
  exact False.elim (hk0ne (needsΓb_k0_of_true E hΓ t hb))

/-- Recursive check: every Γ-required position among the first `k` digits carries digit `1`. -/
def StepsOKΓbUpTo {Γ : Set Form} (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (s : fin_seq) : (k : ℕ) → (hk : k ≤ s.len) → Bool
| 0, _ => true
| (k+1), hk =>
    let hk' : k ≤ s.len := Nat.le_of_succ_le hk
    let i : Fin s.len := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    StepsOKΓbUpTo E hΓ s k hk' &&
      (if needsΓb E hΓ k then decide (s.seq i = 1) else true)

/-- Full-length version of `StepsOKΓbUpTo`. -/
def StepsOKΓb {Γ : Set Form} (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (s : fin_seq) : Bool :=
  StepsOKΓbUpTo E hΓ s s.len le_rfl

/-- Propositional version of the Boolean check. -/
def StepsOKΓ {Γ : Set Form} (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (s : fin_seq) : Prop :=
  StepsOKΓb E hΓ s = true

instance {Γ : Set Form} (E : Enumerations) (hΓ : IPC.VeldmanContext Γ) (s : fin_seq) :
    Decidable (StepsOKΓ E hΓ s) := by
  dsimp [StepsOKΓ]
  infer_instance

/-- The Γ-subfan law: restrict the concrete fan by the positive Γ-trace. -/
def TΓlaw {Γ : Set Form} (E : Enumerations) (hΓ : IPC.VeldmanContext Γ) :
    fin_seq → ℕ :=
  fun s =>
    match (ImplicationSubfan.Vconcrete E).S s with
    | 0 => if StepsOKΓb E hΓ s then 0 else 1
    | _ + 1 => 1

lemma TΓlaw_eq_zero_iff {Γ : Set Form} (E : Enumerations)
    (hΓ : IPC.VeldmanContext Γ) (s : fin_seq) :
    TΓlaw E hΓ s = 0 ↔
      (ImplicationSubfan.Vconcrete E).S s = 0 ∧ StepsOKΓ E hΓ s := by
  unfold TΓlaw StepsOKΓ StepsOKΓb
  cases (ImplicationSubfan.Vconcrete E).S s with
  | zero => simp
  | succ n => simp

lemma TΓ_le_S {Γ : Set Form} (E : Enumerations) (hΓ : IPC.VeldmanContext Γ) :
    ∀ s : fin_seq, TΓlaw E hΓ s = 0 → (ImplicationSubfan.Vconcrete E).S s = 0 := by
  intro s hs
  exact (TΓlaw_eq_zero_iff E hΓ s).1 hs |>.1

lemma StepsOKΓbUpTo_pred_true {Γ : Set Form} (E : Enumerations)
    (hΓ : IPC.VeldmanContext Γ) (s : fin_seq) (k : ℕ) (hk : k.succ ≤ s.len) :
    StepsOKΓbUpTo E hΓ s k.succ hk = true →
    StepsOKΓbUpTo E hΓ s k (Nat.le_of_succ_le hk) = true := by
  intro h
  have h' :
      StepsOKΓbUpTo E hΓ s k (Nat.le_of_succ_le hk) = true ∧
        (needsΓb E hΓ k = false ∨
          s.seq ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ = 1) := by
    simpa [StepsOKΓbUpTo] using h
  exact h'.1

lemma StepsOKΓbUpTo_proof_irrel {Γ : Set Form} (E : Enumerations)
    (hΓ : IPC.VeldmanContext Γ) (s : fin_seq) :
    ∀ k (hk1 hk2 : k ≤ s.len),
      StepsOKΓbUpTo E hΓ s k hk1 = StepsOKΓbUpTo E hΓ s k hk2 := by
  intro k
  induction k with
  | zero => intro hk1 hk2; rfl
  | succ k ih =>
      intro hk1 hk2
      have hrec := ih (Nat.le_of_succ_le hk1) (Nat.le_of_succ_le hk2)
      by_cases hneed : needsΓb E hΓ k
      · simp [StepsOKΓbUpTo, hneed, hrec]
      · simp [StepsOKΓbUpTo, hneed, hrec]

lemma child_len_ge (s : fin_seq) (q : ℕ) : s.len ≤ (ImplicationSubfan.child s q).len := by
  change s.len ≤ s.len + 1
  exact Nat.le_succ s.len

lemma StepsOKΓbUpTo_child_eq {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (s : fin_seq) (q : ℕ) :
    ∀ k (hk : k ≤ s.len),
      StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) k
          (Nat.le_trans hk (child_len_ge s q))
      = StepsOKΓbUpTo E hΓ s k hk := by
  intro k hk
  induction k with
  | zero => simp [StepsOKΓbUpTo]
  | succ k ih =>
      have hk' : k ≤ s.len := Nat.le_of_succ_le hk
      have hkChild : k.succ ≤ (ImplicationSubfan.child s q).len := Nat.le_trans hk (child_len_ge s q)
      have hlt : k < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hltChild : k < (ImplicationSubfan.child s q).len := Nat.lt_of_lt_of_le hlt (child_len_ge s q)
      let iS : Fin s.len := ⟨k, hlt⟩
      let iC : Fin (ImplicationSubfan.child s q).len := ⟨k, hltChild⟩
      have hseq : (ImplicationSubfan.child s q).seq iC = s.seq iS := by
        simp [ImplicationSubfan.child, fin_seq.extend, fin_seq.singleton, hlt, iS, iC]
      simp [StepsOKΓbUpTo, ih hk', hseq, iS, iC]

lemma StepsOKΓbUpTo_prefix_child {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (s : fin_seq) (q : ℕ) :
    StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) (ImplicationSubfan.child s q).len le_rfl = true →
    StepsOKΓbUpTo E hΓ s s.len le_rfl = true := by
  intro h
  have hlen : (ImplicationSubfan.child s q).len = s.len.succ := by
    simp [ImplicationSubfan.child, fin_seq.extend, fin_seq.singleton]
  have h' :
      StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) s.len.succ (by simp [hlen]) = true := by
    simpa [hlen] using h
  have hdown :
      StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) s.len
        (Nat.le_of_succ_le (by simp [hlen])) = true := by
    exact StepsOKΓbUpTo_pred_true E hΓ (ImplicationSubfan.child s q) s.len
      (by simp [hlen]) h'
  have heq :
      StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) s.len
        (Nat.le_trans (le_rfl : s.len ≤ s.len) (child_len_ge s q))
      = StepsOKΓbUpTo E hΓ s s.len le_rfl :=
    StepsOKΓbUpTo_child_eq E hΓ s q s.len le_rfl
  simpa [heq] using hdown

lemma StepsOKΓ_child_of_StepsOK {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (s : fin_seq) (q : ℕ)
    (hS : StepsOKΓ E hΓ s)
    (hnew : needsΓb E hΓ s.len = true → q = 1) :
    StepsOKΓ E hΓ (ImplicationSubfan.child s q) := by
  unfold StepsOKΓ at hS ⊢
  unfold StepsOKΓb at hS ⊢
  have hlen : (ImplicationSubfan.child s q).len = s.len + 1 := by
    simp [ImplicationSubfan.child, fin_seq.extend, fin_seq.singleton]
  have hkfull : s.len.succ ≤ (ImplicationSubfan.child s q).len := by rw [hlen]
  have hPrefixEq :
      StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) s.len (Nat.le_of_succ_le hkfull)
      = StepsOKΓbUpTo E hΓ s s.len le_rfl := by
    calc
      StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) s.len (Nat.le_of_succ_le hkfull)
          = StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) s.len
              (Nat.le_trans le_rfl (child_len_ge s q)) :=
            StepsOKΓbUpTo_proof_irrel E hΓ (ImplicationSubfan.child s q) s.len _ _
      _ = StepsOKΓbUpTo E hΓ s s.len le_rfl :=
            StepsOKΓbUpTo_child_eq E hΓ s q s.len le_rfl
  have hPrefixTrue :
      StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) s.len (Nat.le_of_succ_le hkfull) = true := by
    rw [hPrefixEq]
    exact hS
  by_cases hb : needsΓb E hΓ s.len
  · have hq : q = 1 := hnew hb
    subst q
    have hLast : (ImplicationSubfan.child s 1).seq
        ⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hkfull⟩ = 1 := by
      have hidx :
          (⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hkfull⟩ : Fin (ImplicationSubfan.child s 1).len)
            = ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ := by
        apply Fin.ext; rfl
      calc
        (ImplicationSubfan.child s 1).seq ⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hkfull⟩
            = (ImplicationSubfan.child s 1).seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ := by rw [hidx]
        _ = 1 := by
            change (extend s (singleton 1)).seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ = 1
            exact ImplicationSubfan.VC.extend_singleton_last s 1
    have hmain :
        StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s 1) s.len.succ hkfull = true := by
      simp [StepsOKΓbUpTo, hb, hPrefixTrue, hLast]
    simpa [hlen] using hmain
  · have hmain :
        StepsOKΓbUpTo E hΓ (ImplicationSubfan.child s q) s.len.succ hkfull = true := by
      simp [StepsOKΓbUpTo, hb, hPrefixTrue]
    simpa [hlen] using hmain

lemma StepsOKΓ_empty {Γ : Set Form} (E : Enumerations) (hΓ : IPC.VeldmanContext Γ) :
    StepsOKΓ E hΓ empty_seq := by
  dsimp [StepsOKΓ, StepsOKΓb]
  have hlen : empty_seq.len = 0 := by simp [empty_seq]
  simp [hlen, StepsOKΓbUpTo]

lemma StepsOKΓ_finitize_digit_eq_one {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (bseq : 𝒩) (t : ℕ)
    (hSteps : StepsOKΓ E hΓ (finitize bseq (t + 1)))
    (hneed : needsΓb E hΓ t = true) :
    bseq t = 1 := by
  unfold StepsOKΓ StepsOKΓb at hSteps
  have hlen : (finitize bseq (t + 1)).len = t + 1 := by
    simp [fin_seq.finitize_len]
  have hSteps' :
      StepsOKΓbUpTo E hΓ (finitize bseq (t + 1)) (t + 1) (by simp [hlen]) = true := by
    simpa [hlen] using hSteps
  have hLayer :
      StepsOKΓbUpTo E hΓ (finitize bseq (t + 1)) t
          (Nat.le_of_succ_le (by simp [hlen])) = true ∧
        (needsΓb E hΓ t = false ∨
          (finitize bseq (t + 1)).seq
            ⟨t, Nat.lt_of_lt_of_le (Nat.lt_succ_self t) (by simp [hlen])⟩ = 1) := by
    simpa [StepsOKΓbUpTo] using hSteps'
  have hDigit :
      (finitize bseq (t + 1)).seq
        ⟨t, Nat.lt_of_lt_of_le (Nat.lt_succ_self t) (by simp [hlen])⟩ = 1 := by
    simpa [hneed] using hLayer.2
  simpa [fin_seq.finitize] using hDigit

/-- The Γ-subfan law is a fan law. -/
theorem TΓlaw_is_fan_law {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ) :
    is_fan_law (TΓlaw E hΓ) := by
  let V : VeldmanFan E := ImplicationSubfan.Vconcrete E
  refine And.intro ?spread ?bound
  · refine And.intro ?empty ?ext
    · have hS0 : V.S empty_seq = 0 := Sigma_empty (V := V)
      have hOK : StepsOKΓ E hΓ empty_seq := StepsOKΓ_empty E hΓ
      simpa [V] using (TΓlaw_eq_zero_iff E hΓ empty_seq).2 ⟨hS0, hOK⟩
    · intro s
      constructor
      · intro hs0
        have hSs : V.S s = 0 := by
          simpa [V] using ((TΓlaw_eq_zero_iff E hΓ s).1 hs0 |>.1)
        have hOKs : StepsOKΓ E hΓ s := (TΓlaw_eq_zero_iff E hΓ s).1 hs0 |>.2
        let E0 : ImplicationSubfan.VC.Enumerations := ImplicationSubfan.toConcreteEnum E
        let st : ImplicationSubfan.VC.State := ImplicationSubfan.VC.runState E0 s
        let q : ℕ := if needsΓb E hΓ s.len then 1 else ImplicationSubfan.VC.chooseNext E0 st
        have ht : st.t = s.len := by
          simpa [st, E0] using (ImplicationSubfan.runState_t (E0 := E0) (s := s))
        have hAllowed : ImplicationSubfan.VC.AllowedStepb E0 st q = true := by
          by_cases hneed : needsΓb E hΓ s.len = true
          · have hq : q = 1 := by simp [q, hneed]
            have hk0s : ImplicationSubfan.VC.decK s.len = IPC.k0 := needsΓb_k0_of_true E hΓ s.len hneed
            have hk0t : ImplicationSubfan.VC.decK st.t = IPC.k0 := by simpa [ht] using hk0s
            rw [hq]
            exact ImplicationSubfan.AllowedStepb_k0_one E0 st hk0t
          · have hq : q = ImplicationSubfan.VC.chooseNext E0 st := by simp [q, hneed]
            simpa [hq] using ImplicationSubfan.VC.Allowed_chooseNext E0 st
        have hSsSigma : ImplicationSubfan.VC.Sigma E0 s = 0 := by
          simpa [V, ImplicationSubfan.Vconcrete, E0] using hSs
        have hSigmaChildSigma : ImplicationSubfan.VC.Sigma E0 (ImplicationSubfan.child s q) = 0 :=
          ImplicationSubfan.Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := q) hSsSigma
            (by simpa [ImplicationSubfan.VC.runState, st] using hAllowed)
        have hSigmaChild : V.S (ImplicationSubfan.child s q) = 0 := by
          simpa [V, ImplicationSubfan.Vconcrete, E0] using hSigmaChildSigma
        have hnew : needsΓb E hΓ s.len = true → q = 1 := by
          intro hneed; simp [q, hneed]
        have hOKchild : StepsOKΓ E hΓ (ImplicationSubfan.child s q) :=
          StepsOKΓ_child_of_StepsOK E hΓ s q hOKs hnew
        have hTchild : TΓlaw E hΓ (ImplicationSubfan.child s q) = 0 :=
          (TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s q)).2 (by simpa [V] using ⟨hSigmaChild, hOKchild⟩)
        exact ⟨q, by simpa [ImplicationSubfan.child] using hTchild⟩
      · rintro ⟨q, hq0⟩
        have hq0' : TΓlaw E hΓ (ImplicationSubfan.child s q) = 0 := by simpa [ImplicationSubfan.child] using hq0
        have hSChild : V.S (ImplicationSubfan.child s q) = 0 := by
          simpa [V] using ((TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s q)).1 hq0' |>.1)
        have hSs : V.S s = 0 := by
          have hspread : is_spread_law V.S := (fan_law_is_spread_law V.S V.hS)
          exact (hspread.2 s).2 ⟨q, hSChild⟩
        have hOKs : StepsOKΓ E hΓ s :=
          StepsOKΓbUpTo_prefix_child E hΓ s q
            ((TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s q)).1 hq0' |>.2)
        exact (TΓlaw_eq_zero_iff E hΓ s).2 (by simpa [V] using ⟨hSs, hOKs⟩)
  · intro s hs0
    have hSs : V.S s = 0 := by
      simpa [V] using ((TΓlaw_eq_zero_iff E hΓ s).1 hs0 |>.1)
    rcases (V.hS.2 s hSs) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro m hm0
    have hm0' : TΓlaw E hΓ (ImplicationSubfan.child s m) = 0 := by simpa [ImplicationSubfan.child] using hm0
    have hmS : V.S (ImplicationSubfan.child s m) = 0 := by
      simpa [V] using ((TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s m)).1 hm0' |>.1)
    exact hn m hmS

/-- Every branch of the Γ-subfan contains the external context `Γ`. -/
lemma gamma_ok_concrete {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ)
    (hT : is_fan_law (TΓlaw E hΓ)) :
    ∀ b : fan (TΓlaw E hΓ) hT,
      Γ ⊆ Gamma (ImplicationSubfan.Vconcrete E)
        (toBranchOfSubfan (V := ImplicationSubfan.Vconcrete E) (hT := hT)
          (hsub := TΓ_le_S E hΓ) b) := by
  intro b B hB
  rcases hΓ.beta_complete B hB with ⟨m, hm⟩
  rcases E.W_surj B with ⟨n, hn⟩
  let t : ℕ := IPC.schedEncode ⟨n, m, IPC.k0⟩
  have hdec : IPC.schedDecode t = ⟨n, m, IPC.k0⟩ := by
    simpa [t] using (IPC.schedDecode_encode ⟨n, m, IPC.k0⟩)
  have hk0 : ImplicationSubfan.VC.decK t = IPC.k0 := by
    simp [ImplicationSubfan.VC.decK, hdec]
  have hdecN : ImplicationSubfan.VC.decN t = n := by
    simp [ImplicationSubfan.VC.decN, hdec]
  have hdecM : decM t = m := by
    simp [decM, hdec]
  have hneed : needsΓb E hΓ t = true := by
    apply needsΓb_true_of E hΓ t hk0
    simpa [hdecN, hdecM, hn] using hm
  have hTpref : TΓlaw E hΓ (finitize b.1 (t + 1)) = 0 := b.2 (t + 1)
  have hOKpref : StepsOKΓ E hΓ (finitize b.1 (t + 1)) :=
    (TΓlaw_eq_zero_iff E hΓ (finitize b.1 (t + 1))).1 hTpref |>.2
  have hbDigit : b.1 t = 1 :=
    StepsOKΓ_finitize_digit_eq_one E hΓ b.1 t hOKpref hneed
  let s0 : fin_seq := finitize b.1 t
  have hs0 : finitize b.1 (t + 1) = ImplicationSubfan.child s0 1 := by
    have hchild : finitize b.1 (t + 1) = ImplicationSubfan.child (finitize b.1 t) (b.1 t) :=
      ImplicationSubfan.finitize_succ_eq_child (bseq := b.1) (t := t)
    simpa [s0, hbDigit] using hchild
  have hk0s0 : ImplicationSubfan.VC.decK s0.len = IPC.k0 := by
    simpa [s0, fin_seq.finitize_len] using hk0
  have hdecNs0 : ImplicationSubfan.VC.decN s0.len = n := by
    simpa [s0, fin_seq.finitize_len] using hdecN
  have hmemChild : E.W n ∈ (ImplicationSubfan.Vconcrete E).F (ImplicationSubfan.child s0 1) := by
    have hF := ImplicationSubfan.StepRules.Vconcrete_F_child_k0_one (E := E) (s := s0) hk0s0
    rw [hF]
    simp [hdecNs0]
  refine ⟨t + 1, ?_⟩
  have hcoe :
      (toBranchOfSubfan (V := ImplicationSubfan.Vconcrete E) (hT := hT)
        (hsub := TΓ_le_S E hΓ) b).1 = b.1 := rfl
  simpa [Gamma, hcoe, hs0, hn] using hmemChild

/-- Concrete local case analysis for the Γ-subfan. -/
theorem stepRulesΓ {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ) (A : Form) :
    ContextGammaRules.IndStepRulesΓ (ImplicationSubfan.Vconcrete E) Γ A (TΓlaw E hΓ) := by
  let V : VeldmanFan E := ImplicationSubfan.Vconcrete E
  refine ⟨?_⟩
  intro s hs0
  have hSs : V.S s = 0 := by
    simpa [V] using ((TΓlaw_eq_zero_iff E hΓ s).1 hs0 |>.1)
  have hOKs : StepsOKΓ E hΓ s := (TΓlaw_eq_zero_iff E hΓ s).1 hs0 |>.2
  let E0 : ImplicationSubfan.VC.Enumerations := ImplicationSubfan.toConcreteEnum E
  let st : ImplicationSubfan.VC.State := ImplicationSubfan.VC.runState E0 s
  have ht : st.t = s.len := by
    simpa [st, E0] using (ImplicationSubfan.runState_t (E0 := E0) (s := s))
  by_cases hk0 : ImplicationSubfan.VC.decK s.len = IPC.k0
  · have hk0st : ImplicationSubfan.VC.decK st.t = IPC.k0 := by simpa [ht] using hk0
    by_cases hF : ImplicationSubfan.VC.Forced0b E0 st = true
    · refine Or.inr (Or.inl ?_)
      let X : Form := E.W (ImplicationSubfan.VC.decN s.len)
      refine ⟨1, X, ?_, ?_, ?_⟩
      · have hAllowed : ImplicationSubfan.VC.AllowedStepb E0 st 1 = true :=
          ImplicationSubfan.StepRules.AllowedStepb_k0_force_only_1 E0 st hk0st (by simpa [st] using hF)
        have hSigmaChild : V.S (ImplicationSubfan.child s 1) = 0 := by
          have : ImplicationSubfan.VC.Sigma E0 (ImplicationSubfan.child s 1) = 0 :=
            ImplicationSubfan.Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 1)
              (by simpa [V, ImplicationSubfan.Vconcrete, E0] using hSs)
              (by simpa [ImplicationSubfan.VC.runState, st] using hAllowed)
          simpa [V, ImplicationSubfan.Vconcrete, E0] using this
        have hOKchild : StepsOKΓ E hΓ (ImplicationSubfan.child s 1) :=
          StepsOKΓ_child_of_StepsOK E hΓ s 1 hOKs (by intro _; rfl)
        have hTchild : TΓlaw E hΓ (ImplicationSubfan.child s 1) = 0 :=
          (TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s 1)).2 (by simpa [V] using ⟨hSigmaChild, hOKchild⟩)
        simpa [ImplicationSubfan.child] using hTchild
      · subst X
        simpa [V] using (ImplicationSubfan.StepRules.Vconcrete_F_child_k0_one (E := E) (s := s) hk0)
      · have hprf : ((↑(st.Fs) : Set Form) ⊢ᵢ (E0.W (ImplicationSubfan.VC.decN st.t))) :=
          ImplicationSubfan.Forced0b_prf (E0 := E0) (st := st) (by simpa [st] using hF)
        have hFs : (↑(V.F s) : Set Form) = (↑st.Fs : Set Form) := by
          simp [V, ImplicationSubfan.Vconcrete, ImplicationSubfan.VC.FS, st, E0]
        have hX : E0.W (ImplicationSubfan.VC.decN st.t) = X := by
          subst X
          simp [E0, ImplicationSubfan.toConcreteEnum, ht]
        have hprfX : (↑st.Fs : Set Form) ⊢ᵢ X := by
          simpa [hX] using hprf
        have hΓX : (↑(V.F s) : Set Form) ⊢ᵢ X := by
          simpa [hFs] using hprfX
        simpa [V] using hΓX

    · have hF' : ImplicationSubfan.VC.Forced0b E0 st = false := by
        cases h0 : ImplicationSubfan.VC.Forced0b E0 st with
        | true => exact False.elim (hF h0)
        | false => simp
      by_cases hneed : needsΓb E hΓ s.len = true
      · refine Or.inr (Or.inr (Or.inl ?_))
        let X : Form := E.W (ImplicationSubfan.VC.decN s.len)
        refine ⟨1, X, ?_, ?_, ?_⟩
        · have hAllowed : ImplicationSubfan.VC.AllowedStepb E0 st 1 = true :=
            (ImplicationSubfan.StepRules.AllowedStepb_k0_allow_0_1 E0 st hk0st hF').2
          have hSigmaChild : V.S (ImplicationSubfan.child s 1) = 0 := by
            have : ImplicationSubfan.VC.Sigma E0 (ImplicationSubfan.child s 1) = 0 :=
              ImplicationSubfan.Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 1)
                (by simpa [V, ImplicationSubfan.Vconcrete, E0] using hSs)
                (by simpa [ImplicationSubfan.VC.runState, st] using hAllowed)
            simpa [V, ImplicationSubfan.Vconcrete, E0] using this
          have hOKchild : StepsOKΓ E hΓ (ImplicationSubfan.child s 1) :=
            StepsOKΓ_child_of_StepsOK E hΓ s 1 hOKs (by intro _; rfl)
          have hTchild : TΓlaw E hΓ (ImplicationSubfan.child s 1) = 0 :=
            (TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s 1)).2 (by simpa [V] using ⟨hSigmaChild, hOKchild⟩)
          simpa [ImplicationSubfan.child] using hTchild
        · subst X
          simpa [ImplicationSubfan.VC.FS, E0] using (ImplicationSubfan.StepRules.FS_child_k0_one (E := E) (s := s) hk0)
        · subst X
          exact needsΓb_mem_of_true E hΓ s.len hneed
      · refine Or.inl ?_
        refine ⟨0, ?_, ?_⟩
        · have hAllowed : ImplicationSubfan.VC.AllowedStepb E0 st 0 = true :=
            (ImplicationSubfan.StepRules.AllowedStepb_k0_allow_0_1 E0 st hk0st hF').1
          have hSigmaChild : V.S (ImplicationSubfan.child s 0) = 0 := by
            have : ImplicationSubfan.VC.Sigma E0 (ImplicationSubfan.child s 0) = 0 :=
              ImplicationSubfan.Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
                (by simpa [V, ImplicationSubfan.Vconcrete, E0] using hSs)
                (by simpa [ImplicationSubfan.VC.runState, st] using hAllowed)
            simpa [V, ImplicationSubfan.Vconcrete, E0] using this
          have hnew : needsΓb E hΓ s.len = true → (0 : ℕ) = 1 := by
            intro hb; exact False.elim (hneed hb)
          have hOKchild : StepsOKΓ E hΓ (ImplicationSubfan.child s 0) :=
            StepsOKΓ_child_of_StepsOK E hΓ s 0 hOKs hnew
          have hTchild : TΓlaw E hΓ (ImplicationSubfan.child s 0) = 0 :=
            (TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s 0)).2 (by simpa [V] using ⟨hSigmaChild, hOKchild⟩)
          simpa [ImplicationSubfan.child] using hTchild
        · change (ImplicationSubfan.VC.runState E0 (ImplicationSubfan.child s 0)).Fs = (ImplicationSubfan.VC.runState E0 s).Fs
          simpa [E0] using (ImplicationSubfan.StepRules.Fs_child_k0_zero_eq (E := E) (s := s) hk0)

  · by_cases hk1 : ImplicationSubfan.VC.decK s.len = IPC.k1
    · refine Or.inl ?_
      refine ⟨0, ?_, ?_⟩
      · have hk1st : ImplicationSubfan.VC.decK st.t = IPC.k1 := by simpa [ht] using hk1
        have hAllowed : ImplicationSubfan.VC.AllowedStepb E0 st 0 = true :=
          ImplicationSubfan.StepRules.AllowedStepb_k1_only_0 E0 st hk1st
        have hSigmaChild : V.S (ImplicationSubfan.child s 0) = 0 := by
          have : ImplicationSubfan.VC.Sigma E0 (ImplicationSubfan.child s 0) = 0 :=
            ImplicationSubfan.Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
              (by simpa [V, ImplicationSubfan.Vconcrete, E0] using hSs)
              (by simpa [ImplicationSubfan.VC.runState, st] using hAllowed)
          simpa [V, ImplicationSubfan.Vconcrete, E0] using this
        have hnew : needsΓb E hΓ s.len = true → (0 : ℕ) = 1 := by
          intro hb
          exact False.elim (hk0 (needsΓb_k0_of_true E hΓ s.len hb))
        have hOKchild : StepsOKΓ E hΓ (ImplicationSubfan.child s 0) :=
          StepsOKΓ_child_of_StepsOK E hΓ s 0 hOKs hnew
        have hTchild : TΓlaw E hΓ (ImplicationSubfan.child s 0) = 0 :=
          (TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s 0)).2 (by simpa [V] using ⟨hSigmaChild, hOKchild⟩)
        simpa [ImplicationSubfan.child] using hTchild
      · change (ImplicationSubfan.VC.runState E0 (ImplicationSubfan.child s 0)).Fs = (ImplicationSubfan.VC.runState E0 s).Fs
        simpa [E0] using (ImplicationSubfan.StepRules.Fs_child_k1_zero_eq (E := E) (s := s) hk1)

    · have hk2 : ImplicationSubfan.VC.decK s.len = IPC.k2 :=
        ImplicationSubfan.StepRules.decK_eq_k2_of_ne_k0_k1 (t := s.len) hk0 hk1
      have hk2st : ImplicationSubfan.VC.decK st.t = IPC.k2 := by simpa [ht] using hk2
      have caseOne_zero
          (hNoSplitSt :
            ¬ (∃ P Q : Form, E0.W (ImplicationSubfan.VC.decN st.t) = P ⋎ Q ∧ st.prev2 = 1)) :
          ContextGammaRules.CaseOne V (TΓlaw E hΓ) s := by
        refine ⟨0, ?_, ?_⟩
        · have hAllowed : ImplicationSubfan.VC.AllowedStepb E0 st 0 = true :=
            ImplicationSubfan.StepRules.AllowedStepb_k2_default_0 E0 st hNoSplitSt hk2st
          have hSigmaChild : V.S (ImplicationSubfan.child s 0) = 0 := by
            have : ImplicationSubfan.VC.Sigma E0 (ImplicationSubfan.child s 0) = 0 :=
              ImplicationSubfan.Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
                (by simpa [V, ImplicationSubfan.Vconcrete, E0] using hSs)
                (by simpa [ImplicationSubfan.VC.runState, st] using hAllowed)
            simpa [V, ImplicationSubfan.Vconcrete, E0] using this
          have hnew : needsΓb E hΓ s.len = true → (0 : ℕ) = 1 := by
            intro hb
            exact False.elim (hk0 (needsΓb_k0_of_true E hΓ s.len hb))
          have hOKchild : StepsOKΓ E hΓ (ImplicationSubfan.child s 0) :=
            StepsOKΓ_child_of_StepsOK E hΓ s 0 hOKs hnew
          have hTchild : TΓlaw E hΓ (ImplicationSubfan.child s 0) = 0 :=
            (TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s 0)).2 (by simpa [V] using ⟨hSigmaChild, hOKchild⟩)
          simpa [ImplicationSubfan.child] using hTchild
        · change (ImplicationSubfan.VC.runState E0 (ImplicationSubfan.child s 0)).Fs = (ImplicationSubfan.VC.runState E0 s).Fs
          simpa [E0] using (ImplicationSubfan.StepRules.Fs_child_k2_zero_eq (E := E) (s := s) hk2)
      cases hWcase : E.W (ImplicationSubfan.VC.decN s.len) with
      | atom n =>
          refine Or.inl ?_
          exact caseOne_zero (by
            intro h
            rcases h with ⟨P, Q, hWst, _⟩
            simp [E0, ImplicationSubfan.toConcreteEnum, ht, hWcase] at hWst)
      | bot =>
          refine Or.inl ?_
          exact caseOne_zero (by
            intro h
            rcases h with ⟨P, Q, hWst, _⟩
            simp [E0, ImplicationSubfan.toConcreteEnum, ht, hWcase] at hWst)
      | imp R S =>
          refine Or.inl ?_
          exact caseOne_zero (by
            intro h
            rcases h with ⟨P, Q, hWst, _⟩
            simp [E0, ImplicationSubfan.toConcreteEnum, ht, hWcase] at hWst)
      | and R S =>
          refine Or.inl ?_
          exact caseOne_zero (by
            intro h
            rcases h with ⟨P, Q, hWst, _⟩
            simp [E0, ImplicationSubfan.toConcreteEnum, ht, hWcase] at hWst)
      | or P Q =>
        by_cases hp : st.prev2 = 1
        · have hSplit : ContextGammaRules.CaseSplit V (TΓlaw E hΓ) s := by
            refine ⟨P, Q, ?_, ?_, ?_, ?_, ?_⟩
            · have hWst : E0.W (ImplicationSubfan.VC.decN st.t) = P ⋎ Q := by
                simpa [E0, ImplicationSubfan.toConcreteEnum, ht] using hWcase
              have hAllowed : ImplicationSubfan.VC.AllowedStepb E0 st 1 = true :=
                ImplicationSubfan.StepRules.AllowedStepb_k2_split_q1 E0 st P Q hk2st hWst (by simpa [st] using hp)
              have hSigmaChild : V.S (ImplicationSubfan.child s 1) = 0 := by
                have : ImplicationSubfan.VC.Sigma E0 (ImplicationSubfan.child s 1) = 0 :=
                  ImplicationSubfan.Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 1)
                    (by simpa [V, ImplicationSubfan.Vconcrete, E0] using hSs)
                    (by simpa [ImplicationSubfan.VC.runState, st] using hAllowed)
                simpa [V, ImplicationSubfan.Vconcrete, E0] using this
              have hOKchild : StepsOKΓ E hΓ (ImplicationSubfan.child s 1) :=
                StepsOKΓ_child_of_StepsOK E hΓ s 1 hOKs (by intro _; rfl)
              have hTchild : TΓlaw E hΓ (ImplicationSubfan.child s 1) = 0 :=
                (TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s 1)).2 (by simpa [V] using ⟨hSigmaChild, hOKchild⟩)
              simpa [ImplicationSubfan.child] using hTchild
            · have hWst : E0.W (ImplicationSubfan.VC.decN st.t) = P ⋎ Q := by
                simpa [E0, ImplicationSubfan.toConcreteEnum, ht] using hWcase
              have hAllowed : ImplicationSubfan.VC.AllowedStepb E0 st 2 = true :=
                ImplicationSubfan.StepRules.AllowedStepb_k2_split_q2 E0 st P Q hk2st hWst (by simpa [st] using hp)
              have hSigmaChild : V.S (ImplicationSubfan.child s 2) = 0 := by
                have : ImplicationSubfan.VC.Sigma E0 (ImplicationSubfan.child s 2) = 0 :=
                  ImplicationSubfan.Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 2)
                    (by simpa [V, ImplicationSubfan.Vconcrete, E0] using hSs)
                    (by simpa [ImplicationSubfan.VC.runState, st] using hAllowed)
                simpa [V, ImplicationSubfan.Vconcrete, E0] using this
              have hnew : needsΓb E hΓ s.len = true → (2 : ℕ) = 1 := by
                intro hb
                exact False.elim (hk0 (needsΓb_k0_of_true E hΓ s.len hb))
              have hOKchild : StepsOKΓ E hΓ (ImplicationSubfan.child s 2) :=
                StepsOKΓ_child_of_StepsOK E hΓ s 2 hOKs hnew
              have hTchild : TΓlaw E hΓ (ImplicationSubfan.child s 2) = 0 :=
                (TΓlaw_eq_zero_iff E hΓ (ImplicationSubfan.child s 2)).2 (by simpa [V] using ⟨hSigmaChild, hOKchild⟩)
              simpa [ImplicationSubfan.child] using hTchild
            · simpa [V, ImplicationSubfan.Vconcrete, ImplicationSubfan.VC.FS, E0, ImplicationSubfan.child] using
                (ImplicationSubfan.StepRules.Fs_child_k2_split_one_eq (E := E) (s := s) (A := P) (B := Q) hk2 hWcase (by simpa [st, E0] using hp))
            · simpa [V, ImplicationSubfan.Vconcrete, ImplicationSubfan.VC.FS, E0, ImplicationSubfan.child] using
                (ImplicationSubfan.StepRules.Fs_child_k2_split_two_eq (E := E) (s := s) (A := P) (B := Q) hk2 hWcase (by simpa [st, E0] using hp))
            · have hWmem : E0.W (ImplicationSubfan.VC.decN (ImplicationSubfan.VC.runState E0 s).t) ∈ (ImplicationSubfan.VC.runState E0 s).Fs :=
                IPC.VeldmanConcrete.W_mem_Fs_of_k2_prev2_eq_one
                  (E := E0) (s := s)
                  (by simpa [st] using hk2st)
                  (by simpa [st] using hp)
              have hWst : E0.W (ImplicationSubfan.VC.decN (ImplicationSubfan.VC.runState E0 s).t) = P ⋎ Q := by
                have hrun_t : (ImplicationSubfan.VC.runState E0 s).t = s.len := by
                  simpa [st] using ht
                rw [hrun_t]
                simpa [E0, ImplicationSubfan.toConcreteEnum] using hWcase
              simpa [V, ImplicationSubfan.Vconcrete, ImplicationSubfan.VC.FS, E0, hWst] using hWmem
          exact Or.inr (Or.inr (Or.inr hSplit))
        · refine Or.inl ?_
          exact caseOne_zero (by
            intro h
            rcases h with ⟨_A, _B, _hWst, hpst⟩
            exact hp hpst)

/-- The concrete Γ-subfan package required by the abstract arbitrary-context theorem. -/
def contextSubfanData_concrete {Γ : Set Form}
    (E : Enumerations) (hΓ : IPC.VeldmanContext Γ) (A : Form) :
    ImpHardData.ContextSubfanData (ImplicationSubfan.Vconcrete E) Γ A := by
  let T : fin_seq → ℕ := TΓlaw E hΓ
  have hT : is_fan_law T := by
    simpa [T] using (TΓlaw_is_fan_law E hΓ)
  have hsub : ∀ s : fin_seq, T s = 0 → (ImplicationSubfan.Vconcrete E).S s = 0 := by
    intro s hs
    simpa [T] using (TΓ_le_S E hΓ s hs)
  let toB : fan T hT → Branch (ImplicationSubfan.Vconcrete E) :=
    toBranchOfSubfan (V := ImplicationSubfan.Vconcrete E) (hT := hT) (hsub := hsub)
  refine
  { T := T
    hT := hT
    T_le_S := hsub
    toBranch := toB
    toBranch_coe := by intro b; simp [toB]
    gamma_ok := ?_
    ind_step := ?_ }
  · intro b
    have h := gamma_ok_concrete (E := E) (hΓ := hΓ) (hT := hT) b
    simpa [T, toB, hsub] using h
  · intro s hs0 hall
    have hRules : ContextGammaRules.IndStepRulesΓ (ImplicationSubfan.Vconcrete E) Γ A T := by
      simpa [T] using (stepRulesΓ (E := E) (hΓ := hΓ) (A := A))
    exact ContextGammaRules.ind_step_of_rules
      (V := ImplicationSubfan.Vconcrete E) (Γ := Γ) (A := A) (T := T)
      hRules s hs0 hall

end ContextSubfanConcrete

namespace ConcreteCompleteness

universe u

/-- Concrete arbitrary-set semantic completeness, with an explicit enumeration parameter.

This is the non-finite propositional context theorem.  The context is arbitrary as
a set, but must be supplied with a Veldman-positive code `hΓ`.
-/
theorem semantic_completeness_concrete_set_context
    (hBar : BarInductionStd) (E : Enumerations)
    (Γ : Set Form) (hΓ : IPC.VeldmanContext Γ) (A : Form) :
    (∀ {X : Type} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} Γ) → (w ⊩{M} A)) →
      (Γ ⊢ᵢ A) := by
  intro hSem
  let V : VeldmanFan E := ImplicationSubfan.Vconcrete E
  let ctx : ImpHardData.CompletenessCtx V := ctxConcrete hBar E
  let data : ImpHardData.ContextSubfanData V Γ A :=
    ContextSubfanConcrete.contextSubfanData_concrete
      (E := E) (Γ := Γ) (A := A) (hΓ := hΓ)
  exact ImpHardData.contextual_completeness_from_subfan
    (V := V) (ctx := ctx) (Γ := Γ) (A := A) data hSem

private def uliftModelSet {X : Type} (M : emodel X) : emodel (ULift.{u, 0} X) where
  W := { w | w.down ∈ M.W }
  R w v := M.R w.down v.down
  val p w := M.val p w.down
  explodes w := M.explodes w.down
  refl w hw := M.refl w.down hw
  trans w hw v hv z hz hwv hvz := M.trans w.down hw v.down hv z.down hz hwv hvz
  mono p w1 w2 hw1 hw2 hv hR := M.mono p w1.down w2.down hw1 hw2 hv hR
  explodes_mono w1 w2 hw1 hw2 hexplodes hR :=
    M.explodes_mono w1.down w2.down hw1 hw2 hexplodes hR

private lemma forces_uliftModelSet_iff {X : Type} (M : emodel X) :
    ∀ (P : Form) (w : ULift.{u, 0} X),
      (w ⊩{uliftModelSet M} P) ↔ (w.down ⊩{M} P) := by
  intro P
  induction P with
  | atom n =>
      intro w
      rfl
  | bot =>
      intro w
      rfl
  | imp A B ihA ihB =>
      intro w
      constructor
      · intro h v hv hw hRel hA
        have hB : (ULift.up v ⊩{uliftModelSet M} B) :=
          h (ULift.up v)
            (by simpa [uliftModelSet] using hv)
            (by simpa [uliftModelSet] using hw)
            (by simpa [uliftModelSet] using hRel)
            ((ihA (ULift.up v)).2 hA)
        exact (ihB (ULift.up v)).1 hB
      · intro h v hv hw hRel hA
        have hB : (v.down ⊩{M} B) :=
          h v.down
            (by simpa [uliftModelSet] using hv)
            (by simpa [uliftModelSet] using hw)
            (by simpa [uliftModelSet] using hRel)
            ((ihA v).1 hA)
        exact (ihB v).2 hB
  | and A B ihA ihB =>
      intro w
      constructor <;> intro h
      · exact And.intro ((ihA w).1 h.1) ((ihB w).1 h.2)
      · exact And.intro ((ihA w).2 h.1) ((ihB w).2 h.2)
  | or A B ihA ihB =>
      intro w
      constructor <;> intro h
      · rcases h with hA | hB
        · exact Or.inl ((ihA w).1 hA)
        · exact Or.inr ((ihB w).1 hB)
      · rcases h with hA | hB
        · exact Or.inl ((ihA w).2 hA)
        · exact Or.inr ((ihB w).2 hB)

private lemma forces_ctx_uliftModelSet_iff {X : Type} (M : emodel X)
    (Γ : Set Form) (w : ULift.{u, 0} X) :
    (w ⊩{uliftModelSet M} Γ) ↔ (w.down ⊩{M} Γ) := by
  change (∀ P, P ∈ Γ → (w ⊩{uliftModelSet M} P)) ↔
    (∀ P, P ∈ Γ → (w.down ⊩{M} P))
  constructor
  · intro h P hP
    exact (forces_uliftModelSet_iff M P w).1 (h P hP)
  · intro h P hP
    exact (forces_uliftModelSet_iff M P w).2 (h P hP)

/-- Closed arbitrary-set semantic completeness using `DefaultEnumerations.defaultEnumerations`. -/
theorem semantic_completeness_set_context_closed
    (hBar : BarInductionStd)
    (Γ : Set Form) (hΓ : IPC.VeldmanContext Γ) (A : Form) :
    (∀ {X : Type u} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} Γ) → (w ⊩{M} A)) →
      (Γ ⊢ᵢ A) := by
  intro hSem
  have hSem' :
      ∀ {X : Type} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} Γ) → (w ⊩{M} A) := by
    intro X M w hw hΓw
    let M' : emodel (ULift.{u, 0} X) := uliftModelSet M
    have hw' : ULift.up w ∈ M'.W := by
      simpa [M', uliftModelSet] using hw
    have hΓ' : (ULift.up w ⊩{M'} Γ) := by
      exact (forces_ctx_uliftModelSet_iff M Γ (ULift.up w)).2 hΓw
    have hA' : (ULift.up w ⊩{M'} A) :=
      hSem (M := M') (w := ULift.up w) hw' hΓ'
    exact (forces_uliftModelSet_iff M A (ULift.up w)).1 hA'
  exact semantic_completeness_concrete_set_context
    (hBar := hBar)
    (E := DefaultEnumerations.defaultEnumerations)
    (Γ := Γ) (hΓ := hΓ) (A := A) hSem'

/-- Notation-oriented spelling of the closed arbitrary-set theorem. -/
theorem semantic_completeness_set
    (hBar : BarInductionStd)
    (Γ : Set Form) (hΓ : IPC.VeldmanContext Γ) (A : Form) :
    (Γ ⊨ᵢ A) → (Γ ⊢ᵢ A) := by
  simpa [IPC.sem_csq] using
    (semantic_completeness_set_context_closed
      (hBar := hBar) (Γ := Γ) (hΓ := hΓ) (A := A))

end ConcreteCompleteness
