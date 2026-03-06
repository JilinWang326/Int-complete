import Intuitionism.sketch
import Intuitionism.Gammarules
import Intuitionism.intfan
import Intuitionism.barindcution

open NatSeq
open fin_seq
open IPC
open scoped IPC

namespace ConcreteCompleteness

open TodoA TodoB

abbrev BarInductionStd : Prop :=
  ∀ (β : fin_seq → ℕ) (hβ : is_fan_law β) (B : Set fin_seq) (hB : is_bar β hβ B)
    (C : Set fin_seq) (hBC : B ⊆ C)
    (hInd :
      ∀ s : fin_seq,
        β s = 0 →
          (∀ n : ℕ, β (extend s (singleton n)) = 0 → (extend s (singleton n)) ∈ C) →
            s ∈ C),
    principle_of_bar_induction_std β hβ B hB C hBC hInd

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

theorem semantic_completeness_concrete
    (hBar : BarInductionStd) (E : Enumerations) (A : Form) :
    (∀ {X : Type} (M : emodel X), Valid M A) → ((∅ : Set Form) ⊢ᵢ A) := by
  let V : VeldmanFan E := TodoB.Vconcrete E
  let ctx : ImpHardData.CompletenessCtx V := ctxConcrete hBar E
  simpa [V, ctx] using
    (ImpHardData.semantic_completeness' (V := V) (ctx := ctx) (A := A))

end ConcreteCompleteness
