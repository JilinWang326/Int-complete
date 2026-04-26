import Intuitionism.completeness_context
import Intuitionism.ConcreteEnumerations


/-!
# Closed context completeness theorem

This file uses the concrete context construction already present in
`completeness_context.lean`, namely

* `ImpHardData.finite_context_completeness'`, and
* `ConcreteCompleteness.semantic_completeness_concrete_finite_context`.

The only extra step here is to close the enumeration parameter by using
`DefaultEnumerations.defaultEnumerations` from `ConcreteEnumerations.lean`.

No `ContextSubfanData` parameter is introduced in this file.
-/

open IPC
open scoped IPC

universe u

namespace ConcreteCompleteness

/-- The fixed enumeration package used for the concrete Veldman construction. -/
abbrev closedEnumerations : Enumerations :=
  DefaultEnumerations.defaultEnumerations

private def uliftModel {X : Type} (M : emodel X) : emodel (ULift.{u, 0} X) where
  W := { w | w.down ∈ M.W }
  R w v := M.R w.down v.down
  val p w := M.val p w.down
  ival w := M.ival w.down
  refl w hw := M.refl w.down hw
  trans w hw v hv z hz hwv hvz := M.trans w.down hw v.down hv z.down hz hwv hvz
  mono p w1 w2 hw1 hw2 hval hrel := M.mono p w1.down w2.down hw1 hw2 hval hrel
  monoI w1 w2 hw1 hw2 hival hrel := M.monoI w1.down w2.down hw1 hw2 hival hrel

private lemma forces_uliftModel_iff {X : Type} (M : emodel X) :
    ∀ (P : Form) (w : ULift.{u, 0} X),
      (w ⊩{uliftModel M} P) ↔ (w.down ⊩{M} P) := by
  intro P
  induction P with
  | atom n =>
      intro w
      rfl
  | «I» =>
      intro w
      rfl
  | imp A B ihA ihB =>
      intro w
      constructor
      · intro h v hv hw hRel hA
        have hB :
            (ULift.up v ⊩{uliftModel M} B) :=
          h (ULift.up v)
            (by simpa [uliftModel] using hv)
            (by simpa [uliftModel] using hw)
            (by simpa [uliftModel] using hRel)
            ((ihA (ULift.up v)).2 hA)
        exact (ihB (ULift.up v)).1 hB
      · intro h v hv hw hRel hA
        have hB : (v.down ⊩{M} B) :=
          h v.down
            (by simpa [uliftModel] using hv)
            (by simpa [uliftModel] using hw)
            (by simpa [uliftModel] using hRel)
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

private lemma forces_ctx_uliftModel_iff {X : Type} (M : emodel X)
    (Γ : Set Form) (w : ULift.{u, 0} X) :
    (w ⊩{uliftModel M} Γ) ↔ (w.down ⊩{M} Γ) := by
  change (∀ P, P ∈ Γ → (w ⊩{uliftModel M} P)) ↔
    (∀ P, P ∈ Γ → (w.down ⊩{M} P))
  constructor
  · intro h P hP
    exact (forces_uliftModel_iff M P w).1 (h P hP)
  · intro h P hP
    exact (forces_uliftModel_iff M P w).2 (h P hP)

/--
Contextual semantic completeness for finite contexts, with the enumeration
parameter closed.

This is the theorem obtained by combining the concrete finite-context theorem
from `completeness_context.lean` with the concrete enumeration instance from
`ConcreteEnumerations.lean`.
-/
theorem semantic_completeness_concrete_context_closed
    (hBar : BarInductionStd) (Γ : Finset Form) (A : Form) :
    (∀ {X : Type u} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} (↑Γ : Set Form)) → (w ⊩{M} A)) →
      ((↑Γ : Set Form) ⊢ᵢ A) := by
  intro hSem
  have hSem' :
      ∀ {X : Type} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} (↑Γ : Set Form)) → (w ⊩{M} A) := by
    intro X M w hw hΓ
    let M' : emodel (ULift.{u, 0} X) := uliftModel M
    have hw' : ULift.up w ∈ M'.W := by
      simpa [M', uliftModel] using hw
    have hΓ' : (ULift.up w ⊩{M'} (↑Γ : Set Form)) := by
      exact (forces_ctx_uliftModel_iff M (↑Γ : Set Form) (ULift.up w)).2 hΓ
    have hA' : (ULift.up w ⊩{M'} A) :=
      hSem (M := M') (w := ULift.up w) hw' hΓ'
    exact (forces_uliftModel_iff M A (ULift.up w)).1 hA'
  exact semantic_completeness_concrete_finite_context
    (hBar := hBar)
    (E := closedEnumerations)
    (Γ := Γ)
    (A := A)
    hSem'



/-- Expanded version of `semantic_completeness_concrete_context_closed`. -/
theorem semantic_completeness_concrete_context_closed_explicit
    (hBar : BarInductionStd) (Γ : Finset Form) (A : Form) :
    (∀ {X : Type u} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} (↑Γ : Set Form)) → (w ⊩{M} A)) →
      ((↑Γ : Set Form) ⊢ᵢ A) := by
  exact semantic_completeness_concrete_context_closed
    (hBar := hBar) (Γ := Γ) (A := A)



/--
Set-context wrapper for contexts that are definitionally/propositionally equal to
some finite context.
-/
theorem semantic_completeness_concrete_context_closed_of_finset_eq
    (hBar : BarInductionStd) (Γ : Set Form) (Δ : Finset Form)
    (hΓ : Γ = (↑Δ : Set Form)) (A : Form) :
    (∀ {X : Type u} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} Γ) → (w ⊩{M} A)) →
      (Γ ⊢ᵢ A) := by
  subst Γ
  exact semantic_completeness_concrete_context_closed
    (hBar := hBar) (Γ := Δ) (A := A)



/-- Expanded version of `semantic_completeness_concrete_context_closed_of_finset_eq`. -/
theorem semantic_completeness_concrete_context_closed_of_finset_eq_explicit
    (hBar : BarInductionStd) (Γ : Set Form) (Δ : Finset Form)
    (hΓ : Γ = (↑Δ : Set Form)) (A : Form) :
    (∀ {X : Type u} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} Γ) → (w ⊩{M} A)) →
      (Γ ⊢ᵢ A) := by
  subst Γ
  exact semantic_completeness_concrete_context_closed_explicit
    (hBar := hBar) (Γ := Δ) (A := A)

theorem semantic_completeness
    (hBar : BarInductionStd) (Γ : Finset Form) (A : Form) :
    (Γ ⊨ᵢ A) → (Γ ⊢ᵢ A) := by
  simpa [IPC.sem_csq] using
    (semantic_completeness_concrete_context_closed
      (hBar := hBar) (Γ := Γ) (A := A))



end ConcreteCompleteness
