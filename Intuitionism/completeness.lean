import Intuitionism.sketch
import Intuitionism.Gammarules
import Intuitionism.intfan
import Intuitionism.barindcution

/-!
# Final assembly of the concrete completeness proof

This file packages the concrete fan, the `GammaRules` proof, the implication-case
data, and the bar-induction step into the abstract completeness context from
`sketch.lean`.

Mathematically this is the Lean assembly point corresponding to the end of paper
§3.43 and the final completeness statement (paper §4.4, in the present
propositional specialization).
-/

open NatSeq
open fin_seq
open IPC
open scoped IPC

namespace ConcreteCompleteness

open TodoA TodoB

/-- Standard bar induction packaged as the abstract root-closing principle used by the Lean proof skeleton. This is proof-engineering infrastructure for the fan/subfan reasoning behind paper §4.1 and §4.3. -/
abbrev BarInductionStd : Prop :=
  ∀ (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : Set fin_seq) (hB : is_bar β hβ B)
    (C : Set fin_seq) (hBC : B ⊆ C)
    (hInd :
      ∀ s : fin_seq,
        β s = 0 →
          (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
            s ∈ C),
    principle_of_bar_induction_std β hβ B hB C hBC hInd

/-- Instantiate the abstract completeness context with the concrete Veldman fan. The fields correspond respectively to semiregularity of `Γ_α`, the implication hard case (paper §4.1), and the local bar-induction step used to push derivability back to the root. -/
noncomputable def ctxConcrete
    (hBar : BarInductionStd) (E : Enumerations) :
    ImpHardData.CompletenessCtx (TodoB.Vconcrete E) := by
  refine
  { hR := ?_
    BarIndStd := hBar
    impData := TodoB.impDataConcrete (E := E)
    barIndStep := ?_ }

  ·
    simpa [TodoB.Vconcrete, TodoB.toConcreteEnum,
      TodoA.Concrete.mkConcreteFan, TodoA.Concrete.Enumerations.toConcrete] using
      (TodoA.Main.gammaRules_concrete (E0 := E))

  ·
    intro A s hs0 hall
    let E0 : IPC.VeldmanConcrete.Enumerations := TodoB.toConcreteEnum E

    have hs0' : IPC.VeldmanConcrete.Sigma E0 s = 0 := by
      simpa [TodoB.Vconcrete, E0] using hs0

    have hall' :
        ∀ n : ℕ,
          IPC.VeldmanConcrete.Sigma E0 (extend s (singleton n)) = 0 →
            ((↑(IPC.VeldmanConcrete.FS E0 (extend s (singleton n))) : Set Form) ⊢ᵢ A) := by
      intro n hn0
      have hn0V : (TodoB.Vconcrete E).S (extend s (singleton n)) = 0 := by
        simpa [TodoB.Vconcrete, E0] using hn0
      have hprf :
          ((↑((TodoB.Vconcrete E).F (extend s (singleton n))) : Set Form) ⊢ᵢ A) :=
        hall n hn0V
      simpa [TodoB.Vconcrete, E0] using hprf

    simpa [TodoB.Vconcrete, E0] using
      (IPC.VeldmanConcrete.barIndStep_concrete (E := E0) (A := A) s hs0' hall')

/-- Final semantic completeness theorem for the concrete universal model construction. This is the propositional analogue of Veldman's main completeness statement and of the generalized form stated in paper §4.4. -/
theorem semantic_completeness_concrete
    (hBar : BarInductionStd) (E : Enumerations) (A : Form) :
    (∀ {X : Type} (M : emodel X), Valid M A) → ((∅ : Set Form) ⊢ᵢ A) := by
  let V : VeldmanFan E := TodoB.Vconcrete E
  let ctx : ImpHardData.CompletenessCtx V := ctxConcrete hBar E
  simpa [V, ctx] using
    (ImpHardData.semantic_completeness' (V := V) (ctx := ctx) (A := A))

end ConcreteCompleteness
