import Intuitionism.EmptyCompleteness

/-!
# Finite-context version of the concrete completeness theorem

This file adds a finite-context/strong-completeness corollary on top of the
empty-context theorem already assembled in `completeness.lean`.

Mathematically, this is the propositional finite-premise specialization of the
contextual form stated by Veldman in §4.4.  The fully arbitrary-set version of
§4.4 requires a separate Γ-dependent subfan construction; for finite Γ this
corollary follows from the already formalized empty-context completeness theorem
by iterating the semantic deduction theorem.
-/

open NatSeq
open fin_seq
open IPC
open scoped IPC

namespace IPC

/-- Semantic deduction theorem for one additional assumption.

If `Γ ∪ {P}` semantically entails `Q`, then `Γ` semantically entails `P ⊃ Q`.
This is the Kripke-semantics analogue of the proof-theoretic deduction theorem.
-/
lemma sem_csq_deduction_insert {Γ : Set Form} {P Q : Form} :
    (∀ {X : Type} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} (Γ ⸴ P)) → (w ⊩{M} Q)) →
      (∀ {X : Type} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} Γ) → (w ⊩{M} (P ⊃ Q))) := by
  intro hSem X M w hw hΓ v hv _hw hRel hP
  have hAtV : (v ⊩{M} (Γ ⸴ P)) → (v ⊩{M} Q) := by
    intro hΓP
    exact hSem (M := M) (w := v) hv hΓP
  exact hAtV <| by
    intro C hC
    rcases (Set.mem_insert_iff.mp hC) with hEq | hCΓ
    · simpa [hEq] using hP
    · exact mono_r (M := M) C w v hw hv (hΓ C hCΓ) hRel



end IPC

namespace ImpHardData


/-- Data needed for the arbitrary-context version of Veldman §4.4.

For a general set of assumptions `Γ`, the paper constructs a Γ-dependent subfan.
This structure isolates exactly what that construction must provide in the
propositional development:

* a subfan law `T` of the concrete/universal fan;
* every `T`-branch embeds as a branch of `V` and contains `Γ` in its generated
  semiregular theory;
* the local rootward induction step for the proof predicate
  `Γ ∪ F(s) ⊢ A`.
-/
structure ContextSubfanData {E : Enumerations}
    (V : VeldmanFan E) (Γ : Set Form) (A : Form) : Type where
  T : fin_seq → ℕ
  hT : is_fan_law T
  T_le_S : ∀ s : fin_seq, T s = 0 → V.S s = 0
  toBranch : fan T hT → Branch V :=
    fun b =>
      ⟨b.1, by
        intro n
        exact T_le_S (finitize b.1 n) (b.2 n)⟩
  toBranch_coe : ∀ b : fan T hT, (toBranch b).1 = b.1 := by
    intro b
    rfl
  gamma_ok : ∀ b : fan T hT, Γ ⊆ Gamma V (toBranch b)
  ind_step :
    ∀ s : fin_seq,
      T s = 0 →
        (∀ n : ℕ, T (extend s (singleton n)) = 0 →
            (Γ ∪ (↑(V.F (extend s (singleton n))) : Set Form)) ⊢ᵢ A) →
          (Γ ∪ (↑(V.F s) : Set Form)) ⊢ᵢ A

/-- Arbitrary-context completeness from a Γ-dependent subfan.

This is the direct Lean abstraction of Veldman's generalized theorem in §4.4:
once the Γ-subfan construction is supplied as `ContextSubfanData`, semantic
consequence over `Γ` yields a derivation from `Γ`.
-/
theorem contextual_completeness_from_subfan {E : Enumerations}
    (V : VeldmanFan E) (ctx : CompletenessCtx V)
    (Γ : Set Form) (A : Form)
    (data : ContextSubfanData V Γ A) :
    (∀ {X : Type} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} Γ) → (w ⊩{M} A)) →
      (Γ ⊢ᵢ A) := by
  intro hSem

  have hAll : ∀ b : fan data.T data.hT, A ∈ Gamma V (data.toBranch b) := by
    intro b
    have hForcesΓ : (data.toBranch b) ⊩{U V} Γ := by
      intro P hPΓ
      have hMem : P ∈ Gamma V (data.toBranch b) := data.gamma_ok b hPΓ
      have hTL := truth_lemma (V := V) (hR := ctx.hR)
        (BarIndStd := ctx.BarIndStd) (impData := ctx.impData)
        (data.toBranch b) P
      exact hTL.2 hMem

    have hWorld : (data.toBranch b) ∈ (U V).W := by
      simp [U]

    have hForcesA : (data.toBranch b) ⊩{U V} A := by
      exact hSem (M := U V) (w := data.toBranch b) hWorld hForcesΓ

    have hTLA := truth_lemma (V := V) (hR := ctx.hR)
      (BarIndStd := ctx.BarIndStd) (impData := ctx.impData)
      (data.toBranch b) A
    exact hTLA.1 hForcesA

  let β : fin_seq → ℕ := data.T
  let B : Set fin_seq := { s | β s = 0 ∧ A ∈ V.F s }

  have hB : is_bar β data.hT B := by
    intro b
    have hAin : A ∈ Gamma V (data.toBranch b) := hAll b
    rcases hAin with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    refine And.intro (b.2 n) ?_
    have hcoe : (data.toBranch b).1 = b.1 := data.toBranch_coe b
    simpa [B, β, hcoe] using hn

  let C : Set fin_seq := { s | (Γ ∪ (↑(V.F s) : Set Form)) ⊢ᵢ A }

  have hBC : B ⊆ C := by
    intro s hsB
    rcases hsB with ⟨hs0, hsA⟩
    have hPrf : (Γ ∪ (↑(V.F s) : Set Form)) ⊢ᵢ A := by
      apply IPC.prf.ax
      exact Or.inr (show A ∈ (↑(V.F s) : Set Form) from hsA)
    simpa [C] using hPrf

  have hInd :
      ∀ s : fin_seq,
        β s = 0 →
          (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
            s ∈ C := by
    intro s hs0 hall
    have hall' :
        ∀ n : ℕ, data.T (extend s (singleton n)) = 0 →
          (Γ ∪ (↑(V.F (extend s (singleton n))) : Set Form)) ⊢ᵢ A := by
      intro n hn0
      have hnC : (extend s (singleton n)) ∈ C := hall n (by simpa [β] using hn0)
      simpa [C] using hnC

    have hsPrf : (Γ ∪ (↑(V.F s) : Set Form)) ⊢ᵢ A :=
      data.ind_step s (by simpa [β] using hs0) hall'
    simpa [C] using hsPrf

  have hemptyC : empty_seq ∈ C :=
    ctx.BarIndStd β data.hT B hB C hBC hInd

  have hemptyPrf : (Γ ∪ (↑(V.F empty_seq) : Set Form)) ⊢ᵢ A := by
    simpa [C] using hemptyC

  have hsubEmpty : Γ ∪ (↑(V.F empty_seq) : Set Form) ⊆ Γ := by
    intro P hP
    rcases hP with hPΓ | hPF
    · exact hPΓ
    · have hPF0 : P ∈ V.F empty_seq := by
        change P ∈ V.F empty_seq at hPF
        exact hPF
      rw [V.F_empty] at hPF0
      exact False.elim (Finset.notMem_empty P hPF0)

  exact IPC.prf.sub_weak
    (Δ := Γ ∪ (↑(V.F empty_seq) : Set Form))
    (Γ := Γ)
    (p := A) hemptyPrf hsubEmpty



/-- Finite-context strong completeness from the already-proved empty-context theorem.

The proof removes the assumptions one at a time using `sem_csq_deduction_insert`,
applies empty-context completeness to the resulting implication formula, and then
uses modus ponens to reintroduce the finite assumptions syntactically.
-/
theorem finite_context_completeness' {E : Enumerations}
    (V : VeldmanFan E) (ctx : CompletenessCtx V) :
    ∀ (Γ : Finset Form) (A : Form),
      (∀ {X : Type} (M : emodel X) (w : X),
          w ∈ M.W → (w ⊩{M} (↑Γ : Set Form)) → (w ⊩{M} A)) →
        ((↑Γ : Set Form) ⊢ᵢ A) := by
  intro Γ
  induction Γ using Finset.induction with
  | empty =>
      intro A hSem
      have hValid : ∀ {X : Type} (M : emodel X), Valid M A := by
        intro X M w hw
        have hAtW : (w ⊩{M} (↑(∅ : Finset Form) : Set Form)) → (w ⊩{M} A) := by
          intro hEmptyCtx
          exact hSem (M := M) (w := w) hw hEmptyCtx
        exact hAtW <| by
          intro B hB
          change B ∈ (∅ : Finset Form) at hB
          exact False.elim (Finset.notMem_empty B hB)
      have hEmpty : ((∅ : Set Form) ⊢ᵢ A) :=
        semantic_completeness' (V := V) (ctx := ctx) (A := A) hValid
      have hSub : (∅ : Set Form) ⊆ (↑(∅ : Finset Form) : Set Form) := by
        intro B hB
        exact False.elim hB
      exact IPC.prf.sub_weak
        (Δ := (∅ : Set Form))
        (Γ := (↑(∅ : Finset Form) : Set Form))
        (p := A) hEmpty hSub
  | insert P Γ hPnot ih =>
      intro A hSem
      have hSem' : (((↑Γ : Set Form) ⸴ P) ⊨ᵢ A) := by
        intro X M w hw hΓP
        have hInsert : w ⊩{M} (↑(insert P Γ) : Set Form) := by
          intro B hB
          change B ∈ insert P Γ at hB
          rcases Finset.mem_insert.mp hB with rfl | hBΓ
          · exact hΓP _ (Set.mem_insert_iff.mpr (Or.inl rfl))
          · exact hΓP B (Set.mem_insert_iff.mpr (Or.inr hBΓ))
        exact hSem (M := M) (w := w) hw hInsert

      have hSemImp : ((↑Γ : Set Form) ⊨ᵢ (P ⊃ A)) :=
        IPC.sem_csq_deduction_insert
          (Γ := (↑Γ : Set Form)) (P := P) (Q := A) hSem'

      have hImp : ((↑Γ : Set Form) ⊢ᵢ (P ⊃ A)) :=
        ih (P ⊃ A) hSemImp

      have hSub : (↑Γ : Set Form) ⊆ (↑(insert P Γ) : Set Form) := by
        intro B hB
        change B ∈ Γ at hB
        exact Finset.mem_insert_of_mem hB

      have hImp' : ((↑(insert P Γ) : Set Form) ⊢ᵢ (P ⊃ A)) :=
        IPC.prf.sub_weak
          (Δ := (↑Γ : Set Form))
          (Γ := (↑(insert P Γ) : Set Form))
          (p := (P ⊃ A)) hImp hSub

      have hP : ((↑(insert P Γ) : Set Form) ⊢ᵢ P) := by
        apply IPC.prf.ax
        change P ∈ insert P Γ
        exact Finset.mem_insert_self P Γ

      exact IPC.prf.mp hImp' hP



end ImpHardData

namespace ConcreteCompleteness

/-- Concrete finite-context semantic completeness.

This is the finite-premise version of the generalized contextual completeness
statement in Veldman §4.4, specialized to the propositional development here.
-/
theorem semantic_completeness_concrete_finite_context
    (hBar : BarInductionStd) (E : Enumerations) (Γ : Finset Form) (A : Form) :
    (∀ {X : Type} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} (↑Γ : Set Form)) → (w ⊩{M} A)) →
      ((↑Γ : Set Form) ⊢ᵢ A) := by
  let V : VeldmanFan E := ImplicationSubfan.Vconcrete E
  let ctx : ImpHardData.CompletenessCtx V := ctxConcrete hBar E
  intro hSem
  exact ImpHardData.finite_context_completeness'
    (V := V) (ctx := ctx) Γ A hSem


/-- Equivalent spelling using an explicit all-model/all-world semantic premise. -/
theorem semantic_completeness_concrete_finite_context_explicit
    (hBar : BarInductionStd) (E : Enumerations) (Γ : Finset Form) (A : Form) :
    (∀ {X : Type} (M : emodel X) (w : X),
        w ∈ M.W → (w ⊩{M} (↑Γ : Set Form)) → (w ⊩{M} A)) →
      ((↑Γ : Set Form) ⊢ᵢ A) := by
  intro hSem
  exact semantic_completeness_concrete_finite_context
    (hBar := hBar) (E := E) (Γ := Γ) (A := A) hSem



end ConcreteCompleteness
