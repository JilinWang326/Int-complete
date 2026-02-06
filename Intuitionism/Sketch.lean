import Intuitionism.RickKoenders.FinSeq
import Intuitionism.RickKoenders.Fan
import Intuitionism.IPC
import Intuitionism.Enumeration
import Intuitionism.VeldmanConcrete

open NatSeq
open fin_seq
open IPC


/-- Derivation code: finite context + goal formula.
    (This is the encoded version of the paper §3.31 “derivation enumeration d₁, d₂, …”.) -/
abbrev DerCode : Type := Finset Form × Form

/-- Soundness of one derivation code:
    `DerOK (Γ,A)` := Γ ⊢ᵢ A.
    (This corresponds to the basic correctness requirement in the paper that “dᵢ is a derivation
     of a formula from a finite set”, see §3.31.) -/
def DerOK (d : DerCode) : Prop :=
  ((↑d.1 : Set Form) ⊢ᵢ d.2)

/-- Enumerations of formulas and derivations.

Corresponds to paper §3.31 (Preliminaries):
- `W : ℕ → Form` corresponds to the paper’s enumeration of sentences `Wₙ`;
- `d : ℕ → DerCode` corresponds to the paper’s enumeration of derivations `dₙ`;
- `d_complete` is the completeness/coverage of the enumeration: any derivable sequent can be found
  at some index `i` with `d i = (Γ, A)`.
-/
structure Enumerations where
  W : ℕ → Form
  d : ℕ → DerCode
  W_surj : Function.Surjective W
  d_sound : ∀ i : ℕ, DerOK (d i)
  d_complete :
      ∀ (Γ : Finset Form) (A : Form),
        ((↑Γ : Set Form) ⊢ᵢ A) → ∃ i : ℕ, d i = (Γ, A)

--------------------------------------------------------------------------------



def child (s : fin_seq) (q : ℕ) : fin_seq :=
  extend s (singleton q)

/-- The “ambient” fan used for the universal model construction.

Corresponds to paper §3.1 + §3.32 (Definition of Σ, Γ, D):
- `S` corresponds to the paper’s spread/fan law Σ;
- `F` corresponds to the paper’s complementary law Γ (the paper uses Γ(a) for the finite set at node a;
  here we name it `F s`);
- `F_empty` corresponds to paper §3.32: Γ(<>) = ∅;
- `F_mono` corresponds to the monotonicity condition in paper §3.1:
  b ⊑ a and admitted ⇒ Γ(a) ⊆ Γ(b).
-/
structure VeldmanFan (E : Enumerations) where
  S  : fin_seq → ℕ
  hS : is_fan_law S
  F : CompLaw S
  F_empty : F empty_seq = ∅
  F_mono : MonotoneOnAdmitted S F

/-- In paper §3.32, Σ(<>) = 0 (the empty sequence is admitted). -/
lemma Sigma_empty {E : Enumerations} (V : VeldmanFan E) : V.S empty_seq = 0 := by
  exact (V.hS.1).1

--------------------------------------------------------------------------------

/-!

§3.1 (definition Γ_α := ⋃ₙ Γ(α↾n)) and §2.2 (semiregular):
- In the paper, for each branch α (an infinite sequence), Γ_α is defined as the set of all sentences
  collected along the branch;
- Here `Gamma V a` is the paper’s Γ_α (note: the paper’s complementary law is also denoted Γ;
  this code uses `F` to avoid confusion).
-/

/-- A branch (path) in the fan S is your `fan S hS`. -/
abbrev Branch {E : Enumerations} (V : VeldmanFan E) : Type :=
  fan V.S V.hS

/-- Γₐ: collect all formulas that appear in `F(prefix)` along branch `a`.
    Corresponds to paper §3.1: `Γ_α := ⋃ₙ Γ(α↾n)` (the paper also denotes the complementary law by Γ). -/
def Gamma {E : Enumerations} (V : VeldmanFan E) (a : Branch V) : Set Form :=
  { p : Form | ∃ n : ℕ, p ∈ V.F (finitize a.1 n) }

/-- To be proved later; assumed for now. -/
structure GammaRules {E : Enumerations} (V : VeldmanFan E) : Prop where
  gamma_isTheory    : ∀ a : Branch V, IsTheory (Gamma V a)
  gamma_disjunctive : ∀ a : Branch V, Disjunctive (Gamma V a)


theorem Gamma_isTheory {E : Enumerations} (V : VeldmanFan E) (a : Branch V)
  (hR : GammaRules V) :
  IsTheory (Gamma V a) := by
  exact hR.gamma_isTheory a


theorem Gamma_disjunctive {E : Enumerations} (V : VeldmanFan E) (a : Branch V)
  (hR : GammaRules V) :
  Disjunctive (Gamma V a) := by
  exact hR.gamma_disjunctive a


theorem Gamma_semiregular {E : Enumerations} (V : VeldmanFan E)
  (hR : GammaRules V) :
  ∀ a : Branch V, SemiRegular (Gamma V a) := by
  intro a
  refine And.intro ?_ ?_
  · exact Gamma_isTheory (V:=V) a hR
  · exact Gamma_disjunctive (V:=V) a hR


/-- Kripke order in U: a ≤ b iff Γₐ ⊆ Γ_b.
    This is the partial order defined in paper §3.41. -/
def leU {E : Enumerations} (V : VeldmanFan E) (a b : Branch V) : Prop :=
  Gamma V a ⊆ Gamma V b

/-- The universal modified Kripke model U built from branches.
- The model frame corresponds to Definition 1.2 (modified Kripke-model) + the specialized construction in §3.41;
- The treatment of atoms and I corresponds to Definition 1.3 (the atomic forcing/validity clause includes “or m ⊩ I”).
-/
def U {E : Enumerations} (V : VeldmanFan E) : emodel (Branch V) := by
  refine
  { W := Set.univ
    R := leU V
    val := fun p a => (Form.atom p) ∈ Gamma V a
    ival := fun a => (Form.I) ∈ Gamma V a
    refl := by
      intro w hw
      dsimp [leU]
      exact Set.Subset.rfl
    trans := by
      intro w hw v hv u hu hwv hvu
      exact Set.Subset.trans hwv hvu
    mono := by
      intro p w1 w2 hw1 hw2 hv hR
      exact hR hv
    monoI := by
      intro w1 w2 hw1 hw2 hI hR
      exact hR hI }

--------------------------------------------------------------------------------

/-
This part consists of proof-theoretic “structural” lemmas (it does not directly correspond to a numbered item in the paper,
but is used later for CaseForced/CaseCtx, etc.).
-/
namespace IPC
namespace prf
open Finset

/-- Cut / meta-rule: if Γ ⊢ A and Γ,A ⊢ B, then Γ ⊢ B. -/
lemma cut {Γ : Set Form} {A B : Form} :
    (Γ ⊢ᵢ A) → ((Γ ⸴ A) ⊢ᵢ B) → (Γ ⊢ᵢ B) := by
  intro hA hB
  have hAB : Γ ⊢ᵢ (A ⊃ B) :=
    prf.deduction (Γ := Γ) (a := A) (b := B) hB
  exact prf.mp hAB hA
end prf
end IPC

--------------------------------------------------------------------------------

/-
Paper §3.32’s recursive definition (Case 1/2/3 and subcases), and the proof strategy of §4.1 Lemma:
- In the paper’s implicational case (Lemma 4.1), a subfan is constructed and admitted nodes are analyzed by cases,
  so that “holds for all children” implies “holds for the parent” (backward induction).
- Here we abstract the decomposition needed for the propositional version into four cases: One / Forced / Ctx / Split.
-/
namespace GammaRules

/-- CaseOne: choose a child q, T is still admitted and F is unchanged.
    This does not change Γ(a) (e.g. Case 1 Subcase 1.1 or Case 3 Subcase 3.1). -/
def CaseOne {E : Enumerations} (V : VeldmanFan E)
    (T : fin_seq → ℕ) (s : fin_seq) : Prop :=
  ∃ q : ℕ,
    T (extend s (singleton q)) = 0 ∧
    V.F (extend s (singleton q)) = V.F s

/-- CaseForced: we are forced to insert some X into F(s), and X is derivable from the current F(s).
    Paper §3.32 Case 1 Subcase 1.2. -/
def CaseForced {E : Enumerations} (V : VeldmanFan E)
   (T : fin_seq → ℕ) (s : fin_seq) : Prop :=
  ∃ (q : ℕ) (X : Form),
    T (extend s (singleton q)) = 0 ∧
    V.F (extend s (singleton q)) = insert X (V.F s) ∧
    ((↑(V.F s) : Set Form) ⊢ᵢ X)

/-- CaseCtx: insert X into F(s), but X is either already in Γₐ or equals the current “context goal” W.
    This is a “controlled extension” case added in the propositional version to maintain constraints like
    `Γₐ ⊆ Γ_b` and `W ∈ Γ_b`;
    it can be seen as an abstraction of how the paper’s §4.1 subfan construction maintains the (i)-type invariant. -/
def CaseCtx {E : Enumerations} (V : VeldmanFan E)
    (a : Branch V) (W : Form)
    (T : fin_seq → ℕ) (s : fin_seq) : Prop :=
  ∃ (q : ℕ) (X : Form),
    T (extend s (singleton q)) = 0 ∧
    V.F (extend s (singleton q)) = insert X (V.F s) ∧
    (X ∈ Gamma V a ∨ X = W)

/-- CaseSplit: if F(s) contains A∨B, we must split into two admitted children, inserting A and B respectively.
    Corresponds to paper §3.32 Case 3 Subcase 3.2. -/
def CaseSplit {E : Enumerations} (V : VeldmanFan E)
 (T : fin_seq → ℕ) (s : fin_seq) : Prop :=
  ∃ (A B : Form),
    T (extend s (singleton 1)) = 0 ∧
    T (extend s (singleton 2)) = 0 ∧
    V.F (extend s (singleton 1)) = insert A (V.F s) ∧
    V.F (extend s (singleton 2)) = insert B (V.F s) ∧
    (Form.or A B) ∈ V.F s

/-- Package the assumption “every admitted node falls into one of the above cases” as a rule hypothesis. -/
structure IndStepRules {E : Enumerations} (V : VeldmanFan E)
    (a : Branch V) (W Q : Form) (T : fin_seq → ℕ) : Prop where
  cases_cover :
    ∀ s : fin_seq, T s = 0 →
      CaseOne V  T s ∨ CaseForced V T s ∨ CaseCtx V a W T s ∨ CaseSplit V T s

/-
Corresponds to the case analysis on admitted nodes in the proof of paper §4.1 (Lemma 4.1),
used to push “holds for children” back to “holds for the parent” (the induction step for C).
-/
theorem ind_step_of_rules {E : Enumerations} (V : VeldmanFan E)
    (a : Branch V) (W Q : Form) (T : fin_seq → ℕ)
    (hStep : IndStepRules V a W Q T) :
  ∀ s : fin_seq,
    T s = 0 →
      (∀ n : ℕ, T (extend s (singleton n)) = 0 →
          (Gamma V a ∪ {W} ∪ (↑(V.F (extend s (singleton n))) : Set Form)) ⊢ᵢ Q) →
        (Gamma V a ∪ {W} ∪ (↑(V.F s) : Set Form)) ⊢ᵢ Q := by
  intro s hs0 hall
  have hc := hStep.cases_cover s hs0
  rcases hc with hOne | hRest
  · -- CaseOne
    rcases hOne with ⟨q, hq0, hF⟩
    have hCq :
        (Gamma V a ∪ {W} ∪ (↑(V.F (extend s (singleton q))) : Set Form)) ⊢ᵢ Q :=
      hall q hq0
    have hFset :
        (↑(V.F (extend s (singleton q))) : Set Form) = (↑(V.F s) : Set Form) := by
      ext x; simp [hF]
    simpa [hFset] using hCq

  · rcases hRest with hForced | hRest'
    · -- CaseForced
      rcases hForced with ⟨q, X, hq0, hF, hX⟩
      let sq : fin_seq := extend s (singleton q)
      let Δ : Set Form := Gamma V a ∪ {W} ∪ (↑(V.F s) : Set Form)

      have hCq :
          (Gamma V a ∪ {W} ∪ (↑(V.F sq) : Set Form)) ⊢ᵢ Q :=
        hall q hq0

      have hsubCtx :
          (Gamma V a ∪ {W} ∪ (↑(V.F sq) : Set Form)) ⊆ (Δ ⸴ X) := by
        intro p hp
        rcases hp with hpGW | hpFq
        · exact Or.inr (Or.inl hpGW)
        · have hpFin0 : p ∈ V.F sq := by simpa using hpFq
          have hpFin : p ∈ insert X (V.F s) := by simpa [sq, hF] using hpFin0
          have hpEither : p = X ∨ p ∈ V.F s := by
            simpa [Finset.mem_insert] using hpFin
          rcases hpEither with rfl | hpFs
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (show p ∈ (↑(V.F s) : Set Form) from hpFs))

      have hQ_from_ΔX : (Δ ⸴ X) ⊢ᵢ Q :=
        IPC.prf.sub_weak
          (Δ := (Gamma V a ∪ {W} ∪ (↑(V.F sq) : Set Form)))
          (Γ := (Δ ⸴ X)) (p := Q) hCq hsubCtx

      have hX_from_Δ : Δ ⊢ᵢ X := by
        have hsubF : (↑(V.F s) : Set Form) ⊆ Δ := by
          intro p hpFs; exact Or.inr hpFs
        exact IPC.prf.sub_weak
          (Δ := (↑(V.F s) : Set Form)) (Γ := Δ) (p := X) hX hsubF

      have hQ_from_Δ : Δ ⊢ᵢ Q :=
        IPC.prf.cut (Γ := Δ) (A := X) (B := Q) hX_from_Δ hQ_from_ΔX

      simpa [Δ] using hQ_from_Δ

    · rcases hRest' with hCtx | hSplit
      · -- CaseCtx
        rcases hCtx with ⟨q, X, hq0, hF, hXctx⟩
        let sq : fin_seq := extend s (singleton q)
        let Δ : Set Form := Gamma V a ∪ {W} ∪ (↑(V.F s) : Set Form)

        have hCq :
            (Gamma V a ∪ {W} ∪ (↑(V.F sq) : Set Form)) ⊢ᵢ Q :=
          hall q hq0

        have hsubCtx :
            (Gamma V a ∪ {W} ∪ (↑(V.F sq) : Set Form)) ⊆ (Δ ⸴ X) := by
          intro p hp
          rcases hp with hpGW | hpFq
          · exact Or.inr (Or.inl hpGW)
          · have hpFin0 : p ∈ V.F sq := by simpa using hpFq
            have hpFin : p ∈ insert X (V.F s) := by simpa [sq, hF] using hpFin0
            have hpEither : p = X ∨ p ∈ V.F s := by
              simpa [Finset.mem_insert] using hpFin
            rcases hpEither with rfl | hpFs
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (show p ∈ (↑(V.F s) : Set Form) from hpFs))

        have hQ_from_ΔX : (Δ ⸴ X) ⊢ᵢ Q :=
          IPC.prf.sub_weak
            (Δ := (Gamma V a ∪ {W} ∪ (↑(V.F sq) : Set Form)))
            (Γ := (Δ ⸴ X)) (p := Q) hCq hsubCtx

        have hX_from_Δ : Δ ⊢ᵢ X := by
          have hmem : X ∈ Δ := by
            rcases hXctx with hXa | rfl
            · exact Or.inl (Or.inl hXa)
            · exact Or.inl (Or.inr (by simp))
          exact IPC.prf.ax (Γ := Δ) (p := X) hmem

        have hQ_from_Δ : Δ ⊢ᵢ Q :=
          IPC.prf.cut (Γ := Δ) (A := X) (B := Q) hX_from_Δ hQ_from_ΔX

        simpa [Δ] using hQ_from_Δ

      · -- CaseSplit
        rcases hSplit with ⟨A, B, h1, h2, hF1, hF2, hDisj⟩
        let s1 : fin_seq := extend s (singleton 1)
        let s2 : fin_seq := extend s (singleton 2)
        let Δ : Set Form := Gamma V a ∪ {W} ∪ (↑(V.F s) : Set Form)

        have hAB : Δ ⊢ᵢ (Form.or A B) := by
          apply IPC.prf.ax
          exact Or.inr (show Form.or A B ∈ (↑(V.F s) : Set Form) from hDisj)

        have hQ1 :
            (Gamma V a ∪ {W} ∪ (↑(V.F s1) : Set Form)) ⊢ᵢ Q := hall 1 h1
        have hQ2 :
            (Gamma V a ∪ {W} ∪ (↑(V.F s2) : Set Form)) ⊢ᵢ Q := hall 2 h2

        have hsub1 :
            (Gamma V a ∪ {W} ∪ (↑(V.F s1) : Set Form)) ⊆ (Δ ⸴ A) := by
          intro p hp
          rcases hp with hpGW | hpF
          · exact Or.inr (Or.inl hpGW)
          · have hpFin0 : p ∈ V.F s1 := by simpa using hpF
            have hpFin : p ∈ insert A (V.F s) := by simpa [s1, hF1] using hpFin0
            have hpEither : p = A ∨ p ∈ V.F s := by
              simpa [Finset.mem_insert] using hpFin
            rcases hpEither with rfl | hpFs
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (show p ∈ (↑(V.F s) : Set Form) from hpFs))

        have hsub2 :
            (Gamma V a ∪ {W} ∪ (↑(V.F s2) : Set Form)) ⊆ (Δ ⸴ B) := by
          intro p hp
          rcases hp with hpGW | hpF
          · exact Or.inr (Or.inl hpGW)
          · have hpFin0 : p ∈ V.F s2 := by simpa using hpF
            have hpFin : p ∈ insert B (V.F s) := by simpa [s2, hF2] using hpFin0
            have hpEither : p = B ∨ p ∈ V.F s := by
              simpa [Finset.mem_insert] using hpFin
            rcases hpEither with rfl | hpFs
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (show p ∈ (↑(V.F s) : Set Form) from hpFs))

        have hA : (Δ ⸴ A) ⊢ᵢ Q :=
          IPC.prf.sub_weak
            (Δ := (Gamma V a ∪ {W} ∪ (↑(V.F s1) : Set Form)))
            (Γ := (Δ ⸴ A)) (p := Q) hQ1 hsub1

        have hB : (Δ ⸴ B) ⊢ᵢ Q :=
          IPC.prf.sub_weak
            (Δ := (Gamma V a ∪ {W} ∪ (↑(V.F s2) : Set Form)))
            (Γ := (Δ ⸴ B)) (p := Q) hQ2 hsub2

        have hQ : Δ ⊢ᵢ Q :=
          IPC.prf.or_elim (Γ := Δ) (p := A) (q := B) (r := Q) hAB hA hB

        simpa [Δ] using hQ

end GammaRules



/-- If `T s = 0 → S s = 0`, then a `T`-branch canonically is an `S`-branch. -/
def toBranchOfSubfan {E : Enumerations} (V : VeldmanFan E)
    {T : fin_seq → ℕ} (hT : is_fan_law T)
    (hsub : ∀ s : fin_seq, T s = 0 → V.S s = 0) :
    fan T hT → Branch V :=
by
  intro b
  refine ⟨b.1, ?_⟩
  intro n
  exact hsub (finitize b.1 n) (b.2 n)

@[simp] lemma toBranchOfSubfan_coe {E : Enumerations} (V : VeldmanFan E)
    {T : fin_seq → ℕ} (hT : is_fan_law T)
    (hsub : ∀ s : fin_seq, T s = 0 → V.S s = 0)
    (b : fan T hT) :
    (toBranchOfSubfan V hT hsub b).1 = b.1 := rfl

--------------------------------------------------------------------------------

/-!
ImpHardData: package the “hard construction” data for the implicational case

Corresponds to the proof of paper §4.1 (Lemma 4.1):
- For given α, W, Q, the paper constructs a subfan and ensures:
  (i) every branch β in this subfan satisfies Γ_α ⊆ Γ_β and W ∈ Γ_β;
  (ii) a case analysis on nodes provides the backward-induction step;
  then bar induction yields Γ_α, W ⊢ Q, hence Γ_α ⊢ W→Q, and finally we return to membership.
- Here `ImpHardData` packages these construction results as a parameter “supplied to the →-case
  of the truth lemma”. The concrete construction depends on future work; we put it in the
  `VeldmanConcrete` module.
-/
structure ImpHardData {E : Enumerations} (V : VeldmanFan E)
    (a : Branch V) (W Q : Form) : Type where
  /-- the subfan law Σ' -/
  T   : fin_seq → ℕ
  hT  : is_fan_law T
  /-- subfan condition: admitted in T implies admitted in the ambient fan V.S -/
  T_le_S : ∀ s : fin_seq, T s = 0 → V.S s = 0

  /-- canonical embedding of T-branches into V-branches (same infinite sequence) -/
  toBranch : fan T hT → Branch V :=
    fun b =>
      ⟨ b.1
      , by
          intro n
          exact T_le_S (finitize b.1 n) (b.2 n)
      ⟩

  /-- toBranch preserves the underlying infinite sequence (definitional). -/
  toBranch_coe : ∀ b : fan T hT, (toBranch b).1 = b.1 := by
    intro b
    rfl

  /-- the defining property of Σ' on branches -/
  subfan_ok :
    ∀ b : fan T hT,
      (Gamma V a ⊆ Gamma V (toBranch b) ∧ W ∈ Gamma V (toBranch b))

  /-- the real Σ/F local step analysis (One / Forced / Ctx / Split) -/
  stepRules : GammaRules.IndStepRules V a W Q T

  /-- backward-induction step, derived from stepRules (no need to provide manually) -/
  ind_step :
    ∀ s : fin_seq,
      T s = 0 →
        (∀ n : ℕ, T (extend s (singleton n)) = 0 →
            (Gamma V a ∪ {W} ∪ (↑(V.F (extend s (singleton n))) : Set Form)) ⊢ᵢ Q) →
          (Gamma V a ∪ {W} ∪ (↑(V.F s) : Set Form)) ⊢ᵢ Q
    := by
      intro s hs0 hall
      exact
        ind_step_of_rules (V := V) (a := a) (W := W) (Q := Q) (T := T) stepRules s hs0 hall

namespace ImpHardData

/-!

Corresponds to the proof idea of paper §4.1 Lemma 4.1 “right-to-left (hard direction)”:
use bar induction on the subfan to obtain Γₐ ∪ {W} ⊢ Q, then use deduction to get Γₐ ⊢ W→Q,
and finally use that Γₐ is a theory to turn derivability into membership.
-/
theorem gamma_imp_hard_skeleton {E : Enumerations}
    (V : VeldmanFan E) (hR : GammaRules V)
    (BarIndStd :
      ∀ (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : Set fin_seq) (hB : is_bar β hβ B)
        (C : Set fin_seq) (hBC : B ⊆ C)
        (hInd :
          ∀ s : fin_seq,
            β s = 0 →
              (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
                s ∈ C),
        principle_of_bar_induction_std β hβ B hB C hBC hInd
    ) :
  ∀ (a : Branch V) (W Q : Form),
    ImpHardData V a W Q →
    ( (∀ b : Branch V,
          (Gamma V a ⊆ Gamma V b ∧ W ∈ Gamma V b) → Q ∈ Gamma V b)
      → (W ⊃ Q) ∈ Gamma V a ) := by
  intro a W Q data h

  have hTa : IsTheory (Gamma V a) := hR.gamma_isTheory a

  have h_prf : (Gamma V a ⊢ᵢ (W ⊃ Q)) := by
    have h_goal : ((Gamma V a ⸴ W) ⊢ᵢ Q) := by
      -- subfan law
      let β : fin_seq → ℕ := data.T
      have hβ : is_fan_law β := data.hT

      -- bar B(s) : β(s)=0 ∧ Q ∈ F(s)
      let B : Set fin_seq := { s | β s = 0 ∧ Q ∈ V.F s }

      -- show B is a bar
      have hB : is_bar β hβ B := by
        intro b
        have hb_ok :
            (Gamma V a ⊆ Gamma V (data.toBranch b) ∧ W ∈ Gamma V (data.toBranch b)) :=
          data.subfan_ok b
        have hQ_in : Q ∈ Gamma V (data.toBranch b) := h _ hb_ok
        rcases hQ_in with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        refine And.intro (b.2 n) ?_
        have hn' : Q ∈ V.F (finitize (data.toBranch b).1 n) := hn
        simpa [B, data.toBranch_coe b] using hn'

      -- predicate C(s): Γa ∪ {W} ∪ F(s) ⊢ Q
      let C : Set fin_seq :=
        { s | (Gamma V a ∪ {W} ∪ (↑(V.F s) : Set Form)) ⊢ᵢ Q }

      -- B ⊆ C
      have hBC : B ⊆ C := by
        intro s hsB
        rcases hsB with ⟨hs0, hsQ⟩
        apply prf.ax
        refine Or.inr ?_
        exact (show Q ∈ (↑(V.F s) : Set Form) from hsQ)

      -- induction step for C from data.ind_step
      have hInd :
        ∀ s : fin_seq,
          β s = 0 →
            (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
              s ∈ C := by
        intro s hs0 hall
        have hall' :
          ∀ n : ℕ, β (extend s (singleton n)) = 0 →
            (Gamma V a ∪ {W} ∪ (↑(V.F (extend s (singleton n))) : Set Form)) ⊢ᵢ Q := by
          intro n hn0
          have hnC : (extend s (singleton n)) ∈ C := hall n hn0
          simpa [C] using hnC

        have hsPrf :
          (Gamma V a ∪ {W} ∪ (↑(V.F s) : Set Form)) ⊢ᵢ Q :=
          data.ind_step s hs0 hall'

        dsimp [C]
        exact hsPrf

      -- bar induction gives empty_seq ∈ C
      have hemptyC : empty_seq ∈ C :=
        BarIndStd β hβ B hB C hBC hInd

      have hempty0 :
        (Gamma V a ∪ {W} ∪ (↑(V.F empty_seq) : Set Form)) ⊢ᵢ Q := by
        simpa [C] using hemptyC

      have hF0 : (↑(V.F empty_seq) : Set Form) = (∅ : Set Form) := by
        ext x
        simp [V.F_empty]

      have hempty1 :
        (Gamma V a ∪ {W} ∪ (∅ : Set Form)) ⊢ᵢ Q := by
        simpa [hF0] using hempty0

      have hempty2 :
        (Gamma V a ∪ {W}) ⊢ᵢ Q := by
        simpa [Set.union_empty] using hempty1

      have hsub : (Gamma V a ∪ {W}) ⊆ (Gamma V a ⸴ W) := by
        intro x hx
        rcases hx with hxΓ | hxW
        · exact Or.inr hxΓ
        · have hxEq : x = W := by
            simpa [Set.mem_singleton_iff] using hxW
          exact Or.inl hxEq

      exact prf.sub_weak (Δ := (Gamma V a ∪ {W})) (Γ := (Gamma V a ⸴ W)) (p := Q) hempty2 hsub

    exact prf.deduction (Γ := Gamma V a) (a := W) (b := Q) h_goal

  exact hTa h_prf

-- (the rest of your code continues unchanged, with comments already in English or to be translated similarly)


theorem implication_lemma {E : Enumerations} (V : VeldmanFan E) (hR : GammaRules V)

    (BarIndStd :
      ∀ (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : Set fin_seq) (hB : is_bar β hβ B)
        (C : Set fin_seq) (hBC : B ⊆ C)
        (hInd :
          ∀ s : fin_seq,
            β s = 0 →
              (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
                s ∈ C),
        principle_of_bar_induction_std β hβ B hB C hBC hInd
    ) :
  ∀ (a : Branch V) (W Q : Form),
    ImpHardData V a W Q →
    ((W ⊃ Q) ∈ Gamma V a ↔
      ∀ b : Branch V, (Gamma V a ⊆ Gamma V b ∧ W ∈ Gamma V b) → Q ∈ Gamma V b) := by
  intro a W Q data
  constructor
  · -- (→) easy direction
    intro hImp b hb
    rcases hb with ⟨hab, hWb⟩
    have hImp_b : (W ⊃ Q) ∈ Gamma V b := hab hImp
    have hTb : IsTheory (Gamma V b) := hR.gamma_isTheory b
    exact theory_mp_mem (Γ := Gamma V b) hTb hImp_b hWb

  · -- (←) hard direction:
    intro hcond
    have hhard :
        ( (∀ b : Branch V,
              (Gamma V a ⊆ Gamma V b ∧ W ∈ Gamma V b) → Q ∈ Gamma V b)
          → (W ⊃ Q) ∈ Gamma V a ) :=
      gamma_imp_hard_skeleton (V := V) (hR := hR)
        (BarIndStd := BarIndStd) a W Q data
    exact hhard hcond



/-- If Γ is a theory and `I ∈ Γ`, then every formula belongs to Γ (explosion). -/
lemma mem_of_I {Γ : Set Form} (hT : IsTheory Γ) (A : Form) :
    (Form.I ∈ Γ) → A ∈ Γ := by
  intro hI
  have hIprf : Γ ⊢ᵢ Form.I := prf_of_mem (Γ := Γ) hI
  have hexf  : Γ ⊢ᵢ (Form.I ⊃ A) := prf.exf (Γ := Γ) (p := A)
  have hAprf : Γ ⊢ᵢ A := prf.mp hexf hIprf
  exact hT hAprf


/-- in the universal model U, forcing = membership in Γα.

Constructive version: depends on Fan/Bar principles and ImpHardData provider
for the implication case.
-/
theorem truth_lemma {E : Enumerations} (V : VeldmanFan E) (hR : GammaRules V)

    (BarIndStd :
      ∀ (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : Set fin_seq) (hB : is_bar β hβ B)
        (C : Set fin_seq) (hBC : B ⊆ C)
        (hInd :
          ∀ s : fin_seq,
            β s = 0 →
              (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
                s ∈ C),
        principle_of_bar_induction_std β hβ B hB C hBC hInd
    )
    (impData : ∀ (a : Branch V) (W Q : Form), ImpHardData V a W Q) :
  ∀ (a : Branch V) (A : Form),
    (a ⊩{U V} A) ↔ A ∈ Gamma V a := by
  intro a A
  induction A generalizing a with
  | atom n =>
      constructor
      · intro hF
        have h' : (Form.atom n) ∈ Gamma V a ∨ Form.I ∈ Gamma V a := by
          simpa [Forces, U] using hF
        cases h' with
        | inl hn =>
            exact hn
        | inr hI =>
            have hTa : IsTheory (Gamma V a) := hR.gamma_isTheory a
            exact mem_of_I (Γ := Gamma V a) hTa (Form.atom n) hI
      · intro hn
        have : (Form.atom n) ∈ Gamma V a ∨ Form.I ∈ Gamma V a := Or.inl hn
        simpa [Forces, U] using this

  | «I» =>
      simp [Forces, U]

  | imp P Q ihP ihQ =>
      constructor
      · intro hForces
        have hRHS :
            ∀ b : Branch V, (Gamma V a ⊆ Gamma V b ∧ P ∈ Gamma V b) → Q ∈ Gamma V b := by
          intro b hb
          rcases hb with ⟨hab, hPb⟩
          have hb_forcesP : (b ⊩{U V} P) := (ihP (a := b)).2 hPb
          have hbW : b ∈ (U V).W := by simp [U]
          have haW : a ∈ (U V).W := by simp [U]
          have hRel : (U V).R a b := by
            simpa [U, leU] using hab

          have hb_forcesQ : (b ⊩{U V} Q) :=
            hForces b hbW haW hRel hb_forcesP

          exact (ihQ (a := b)).1 hb_forcesQ

        have hIff :=
          implication_lemma (V := V) (hR := hR)
            (BarIndStd := BarIndStd)
            a P Q (impData a P Q)
        exact hIff.2 hRHS

      · intro hMem b hbW haW hRel hb_forcesP
        have hab : Gamma V a ⊆ Gamma V b := by
          simpa [U, leU] using hRel

        have hPb : P ∈ Gamma V b := (ihP (a := b)).1 hb_forcesP

        have hImp_b : (P ⊃ Q) ∈ Gamma V b := hab hMem
        have hTb : IsTheory (Gamma V b) := hR.gamma_isTheory b

        have hQb : Q ∈ Gamma V b :=
          theory_mp_mem (Γ := Gamma V b) hTb hImp_b hPb

        exact (ihQ (a := b)).2 hQb

  | and P Q ihP ihQ =>
      have hTa : IsTheory (Gamma V a) := hR.gamma_isTheory a
      constructor
      · intro h
        have hPmem : P ∈ Gamma V a := (ihP (a := a)).1 h.1
        have hQmem : Q ∈ Gamma V a := (ihQ (a := a)).1 h.2
        have hPprf : (Gamma V a ⊢ᵢ P) := prf_of_mem (Γ := Gamma V a) hPmem
        have hQprf : (Gamma V a ⊢ᵢ Q) := prf_of_mem (Γ := Gamma V a) hQmem
        have hAndPrf : (Gamma V a ⊢ᵢ (P & Q)) := by
          exact prf.mp (prf.mp (prf.pair (Γ := Gamma V a) (p := P) (q := Q)) hPprf) hQprf
        exact hTa hAndPrf
      · intro hMem
        have hAndPrf : (Gamma V a ⊢ᵢ (P & Q)) := prf_of_mem (Γ := Gamma V a) hMem
        have hPprf : (Gamma V a ⊢ᵢ P) :=
          prf.and_elim1 (Γ := Gamma V a) (p := P) (q := Q) hAndPrf
        have hQprf : (Gamma V a ⊢ᵢ Q) :=
          prf.and_elim2 (Γ := Gamma V a) (p := P) (q := Q) hAndPrf
        have hPmem : P ∈ Gamma V a := hTa hPprf
        have hQmem : Q ∈ Gamma V a := hTa hQprf
        exact And.intro ((ihP (a := a)).2 hPmem) ((ihQ (a := a)).2 hQmem)

  | or P Q ihP ihQ =>
      have hTa : IsTheory (Gamma V a) := hR.gamma_isTheory a
      have hDa : Disjunctive (Gamma V a) := hR.gamma_disjunctive a
      constructor
      · intro h
        cases h with
        | inl hP =>
            have hPmem : P ∈ Gamma V a := (ihP (a := a)).1 hP
            have hPprf : (Gamma V a ⊢ᵢ P) := prf_of_mem (Γ := Gamma V a) hPmem
            have hOrPrf : (Gamma V a ⊢ᵢ (P ⋎ Q)) := by
              exact prf.mp (prf.inr (Γ := Gamma V a) (p := P) (q := Q)) hPprf
            exact hTa hOrPrf
        | inr hQ =>
            have hQmem : Q ∈ Gamma V a := (ihQ (a := a)).1 hQ
            have hQprf : (Gamma V a ⊢ᵢ Q) := prf_of_mem (Γ := Gamma V a) hQmem
            have hOrPrf : (Gamma V a ⊢ᵢ (P ⋎ Q)) := by
              exact prf.mp (prf.inl (Γ := Gamma V a) (p := P) (q := Q)) hQprf
            exact hTa hOrPrf
      · intro hMem
        have : P ∈ Gamma V a ∨ Q ∈ Gamma V a := hDa (p := P) (q := Q) hMem
        cases this with
        | inl hPmem => exact Or.inl ((ihP (a := a)).2 hPmem)
        | inr hQmem => exact Or.inr ((ihQ (a := a)).2 hQmem)

structure CompletenessCtx {E : Enumerations} (V : VeldmanFan E) : Type where
  hR : GammaRules V
  /-- Bar induction (standard direction). -/
  BarIndStd :
    ∀ (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : Set fin_seq) (hB : is_bar β hβ B)
      (C : Set fin_seq) (hBC : B ⊆ C)
      (hInd :
        ∀ s : fin_seq,
          β s = 0 →
            (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
              s ∈ C),
      principle_of_bar_induction_std β hβ B hB C hBC hInd
  /-- Implication hard-data provider (from your Σ/F construction). -/
  impData : ∀ (a : Branch V) (W Q : Form), ImpHardData V a W Q

  /-- Bar-lemma induction step provider for each target A. -/
  barIndStep :
    ∀ (A : Form),
      ∀ s : fin_seq,
        V.S s = 0 →
          (∀ n : ℕ, V.S (extend s (singleton n)) = 0 →
              ((↑(V.F (extend s (singleton n))) : Set Form) ⊢ᵢ A)) →
            ((↑(V.F s) : Set Form) ⊢ᵢ A)

/-!
bar_lemma
§3.43 Lemma。
-/
theorem bar_lemma {E : Enumerations} (V : VeldmanFan E) (A : Form)

    (BarIndStd :
      ∀ (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : Set fin_seq) (hB : is_bar β hβ B)
        (C : Set fin_seq) (hBC : B ⊆ C)
        (hInd :
          ∀ s : fin_seq,
            β s = 0 →
              (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
                s ∈ C),
        principle_of_bar_induction_std β hβ B hB C hBC hInd
    )
    (ind_step :
      ∀ s : fin_seq,
        V.S s = 0 →
          (∀ n : ℕ, V.S (extend s (singleton n)) = 0 →
              ((↑(V.F (extend s (singleton n))) : Set Form) ⊢ᵢ A)) →
            ((↑(V.F s) : Set Form) ⊢ᵢ A))
    :
  (∀ a : Branch V, A ∈ Gamma V a) → ((∅ : Set Form) ⊢ᵢ A) := by
  intro hAll

  let β : fin_seq → ℕ := V.S
  have hβ : is_fan_law β := V.hS

  let B : Set fin_seq := { s | β s = 0 ∧ A ∈ V.F s }

  have hB : is_bar β hβ B := by
    intro a
    have hAin : A ∈ Gamma V a := hAll a
    rcases hAin with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change (β (finitize a.1 n) = 0 ∧ A ∈ V.F (finitize a.1 n))
    refine And.intro ?_ hn
    simpa [β] using (a.2 n)

  let C : Set fin_seq := { s | ((↑(V.F s) : Set Form) ⊢ᵢ A) }

  have hBC : B ⊆ C := by
    intro s hsB
    rcases hsB with ⟨hs0, hsA⟩
    have hPrf : ((↑(V.F s) : Set Form) ⊢ᵢ A) :=
      prf.ax (Γ := (↑(V.F s) : Set Form)) (p := A) hsA
    exact (by simpa [C] using hPrf)

  have hInd :
      ∀ s : fin_seq,
        β s = 0 →
          (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
            s ∈ C := by
    intro s hs0 hall

    have hall' :
        ∀ n : ℕ, V.S (extend s (singleton n)) = 0 →
          ((↑(V.F (extend s (singleton n))) : Set Form) ⊢ᵢ A) := by
      intro n hn0
      have hnC : (extend s (singleton n)) ∈ C :=
        hall n (by simpa [β] using hn0)
      simpa [C] using hnC

    have hsPrf : ((↑(V.F s) : Set Form) ⊢ᵢ A) :=
      ind_step s (by simpa [β] using hs0) hall'

    exact (by simpa [C] using hsPrf)

  have hemptyC : empty_seq ∈ C :=
    BarIndStd β hβ B hB C hBC hInd

  have hemptyPrf : ((↑(V.F empty_seq) : Set Form) ⊢ᵢ A) := by
    simpa [C] using hemptyC

  have hF0 : (↑(V.F empty_seq) : Set Form) = (∅ : Set Form) := by
    ext x
    simp [V.F_empty]

  simpa [hF0] using hemptyPrf

theorem bar_lemma' {E : Enumerations} (V : VeldmanFan E) (ctx : CompletenessCtx V) (A : Form) :
  (∀ a : Branch V, A ∈ Gamma V a) → ((∅ : Set Form) ⊢ᵢ A) := by
  intro hAll
  exact bar_lemma (V := V) (A := A)
    (BarIndStd := ctx.BarIndStd)
    (ind_step := ctx.barIndStep A) hAll


/-- Universal-model completeness (paper: consequence of Lemma 3.42 + 3.43). -/
theorem universal_model_completeness {E : Enumerations} (V : VeldmanFan E) (A : Form)
    (hR : GammaRules V)

    (BarIndStd :
      ∀ (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : Set fin_seq) (hB : is_bar β hβ B)
        (C : Set fin_seq) (hBC : B ⊆ C)
        (hInd :
          ∀ s : fin_seq,
            β s = 0 →
              (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
                s ∈ C),
        principle_of_bar_induction_std β hβ B hB C hBC hInd
    )
    (impData : ∀ (a : Branch V) (W Q : Form), ImpHardData V a W Q)
    (ind_step :
      ∀ s : fin_seq,
        V.S s = 0 →
          (∀ n : ℕ, V.S (extend s (singleton n)) = 0 →
              ((↑(V.F (extend s (singleton n))) : Set Form) ⊢ᵢ A)) →
            ((↑(V.F s) : Set Form) ⊢ᵢ A))
    :
  Valid (U V) A → ((∅ : Set Form) ⊢ᵢ A) := by
  intro hValid

  have hAll : ∀ a : Branch V, A ∈ Gamma V a := by
    intro a
    have haW : a ∈ (U V).W := by
      simp [U]
    have hForces : a ⊩{U V} A := hValid a haW
    have hTL :
        (a ⊩{U V} A) ↔ A ∈ Gamma V a :=
      truth_lemma (V := V) (hR := hR)
         (BarIndStd := BarIndStd) (impData := impData) a A
    exact hTL.1 hForces

  exact bar_lemma (V := V) (A := A)
    (BarIndStd := BarIndStd) (ind_step := ind_step) hAll

theorem universal_model_completeness' {E : Enumerations}
    (V : VeldmanFan E) (ctx : CompletenessCtx V) (A : Form) :
  Valid (U V) A → ((∅ : Set Form) ⊢ᵢ A) := by
  intro hValid
  have hAll : ∀ a : Branch V, A ∈ Gamma V a := by
    intro a
    have haW : a ∈ (U V).W := by simp [U]
    have hForces : a ⊩{U V} A := hValid a haW
    have hTL := truth_lemma (V := V) (hR := ctx.hR)
      (BarIndStd := ctx.BarIndStd) (impData := ctx.impData) a A
    exact hTL.1 hForces
  exact bar_lemma' (V := V) ctx A hAll

/-- Same corollary in terms of semantic consequence: if valid in all models then provable.
-/
theorem semantic_completeness' {E : Enumerations}
    (V : VeldmanFan E) (ctx : CompletenessCtx V) (A : Form) :
  (∀ {X : Type} (M : emodel X), Valid M A) → ((∅ : Set Form) ⊢ᵢ A) := by
  intro hAllValid
  have hValidU : Valid (U V) A := by
    simpa using (hAllValid (M := U V))
  exact universal_model_completeness' (V := V) ctx A hValidU

-- #print axioms universal_model_completeness
-- #print axioms universal_model_completeness'
