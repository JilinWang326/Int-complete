import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic

/-!
# Propositional IPC and modified Kripke semantics

This file formalizes the propositional fragment of the machinery used in Veldman
1976:

- paper §1.1: syntax of formulas;
- paper §1.2: modified Kripke models with exploding worlds;
- paper §1.3: forcing/validity clauses;
- paper §1.4: soundness;
- paper §2.2: semiregular sets (here specialized to the propositional fragment,
  so the existential clause disappears).

Whenever the Lean development intentionally specializes the predicate paper to the
propositional case, the comments say so explicitly.
-/

namespace IPC

universe u

/-- Syntax for the propositional fragment of paper §1.1, with Veldman's falsity constant `⊥`. -/
inductive Form : Type
| atom : Nat → Form
| bot : Form
| imp : Form → Form → Form
| and : Form → Form → Form
| or  : Form → Form → Form
deriving DecidableEq, Repr

namespace Form
def neg (A : Form) : Form := imp A bot
end Form

scoped[IPC] prefix:100 "#" => Form.atom
scoped[IPC] notation "⊥" => Form.bot
scoped[IPC] infixr:60 " ⊃ " => Form.imp
scoped[IPC] notation:70 p " & " q => Form.and p q
scoped[IPC] infixr:65 " ⋎ " => Form.or

open scoped IPC

/-- Modified Kripke models in the sense of paper §1.2, specialized to the propositional fragment. -/
structure emodel (A : Type u) where
  W     : Set A
  R     : A → A → Prop
  val   : Nat → A → Prop
  explodes  : A → Prop
  refl  : ∀ w, w ∈ W → R w w
  trans : ∀ w, w ∈ W → ∀ v, v ∈ W → ∀ u, u ∈ W → R w v → R v u → R w u
  mono  : ∀ p : Nat, ∀ w1 w2 : A, w1 ∈ W → w2 ∈ W → val p w1 → R w1 w2 → val p w2
  explodes_mono : ∀ w1 w2 : A, w1 ∈ W → w2 ∈ W → explodes w1 → R w1 w2 → explodes w2

/-- Forcing relation from paper §1.3. The atomic clause includes the explosion predicate, exactly as in Veldman's modified semantics with exploding worlds. -/
@[simp]
def Forces {A : Type u} (M : emodel A) : Form → A → Prop
| Form.atom p, v => M.val p v ∨ M.explodes v
| Form.bot,      v => M.explodes v
| Form.imp p q, v =>
    ∀ w, w ∈ M.W → v ∈ M.W → M.R v w → Forces M p w → Forces M q w
| Form.and p q, v => Forces M p v ∧ Forces M q v
| Form.or  p q, v => Forces M p v ∨ Forces M q v

notation w " ⊩{" M "} " P => Forces M P w

/-- Context forcing. -/
def forces_ctx {A : Type u} (M : emodel A) (Γ : Set Form) : A → Prop :=
  fun w => ∀ p, p ∈ Γ → Forces M p w

notation w " ⊩{" M "} " Γ => forces_ctx M Γ w

/-- Semantic consequence (local). -/
def sem_csq (Γ : Set Form) (p : Form) : Prop :=
  ∀ {A : Type u} (M : emodel A) (w : A),
    w ∈ M.W → (w ⊩{M} Γ) → (w ⊩{M} p)

notation Γ " ⊨ᵢ " p => sem_csq Γ p

/-- Hilbert-style proof system for the propositional fragment of IPC. This instantiates Veldman's remark in §1.1 that the particular axiomatization is not essential. -/
inductive prf : Set Form → Form → Prop
| ax   {Γ} {p} (h : p ∈ Γ) : prf Γ p
| k    {Γ} {p q} : prf Γ (p ⊃ (q ⊃ p))
| s    {Γ} {p q r} :
    prf Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| exf  {Γ} {p} : prf Γ (⊥ ⊃ p)
| mp   {Γ} {p q} (hpq : prf Γ (p ⊃ q)) (hp : prf Γ p) : prf Γ q
| pr1  {Γ} {p q} : prf Γ ((p & q) ⊃ p)
| pr2  {Γ} {p q} : prf Γ ((p & q) ⊃ q)
| pair {Γ} {p q} : prf Γ (p ⊃ (q ⊃ (p & q)))
| inr  {Γ} {p q} : prf Γ (p ⊃ (p ⋎ q))
| inl  {Γ} {p q} : prf Γ (q ⊃ (p ⋎ q))
| case {Γ} {p q r} : prf Γ ((p ⊃ r) ⊃ ((q ⊃ r) ⊃ ((p ⋎ q) ⊃ r)))

notation:50 Γ " ⊢ᵢ " p => prf Γ p
/- some helpful lemmas -/
namespace prf
notation:50 Γ " ⊬ᵢ " p => (prf Γ p → False)
/-- Context extension: `Γ ⸴ p` means `insert p Γ`. -/
notation:55 Γ " ⸴ " a => Set.insert a Γ
/-- If `Γ ⊢ φ` then `Γ ⊢ a ⊃ φ`. -/
lemma lift {Γ : Set Form} {a φ : Form} (hφ : Γ ⊢ᵢ φ) : Γ ⊢ᵢ (a ⊃ φ) :=
  prf.mp (prf.k (Γ := Γ) (p := φ) (q := a)) hφ

lemma id {p : Form} {Γ : Set Form} : Γ ⊢ᵢ (p ⊃ p) := by
  exact prf.mp
    (prf.mp (prf.s (Γ := Γ) (p := p) (q := (p ⊃ p)) (r := p)) prf.k)
    prf.k

theorem deduction {Γ : Set Form} {a b : Form} :
  ((Γ ⸴ a) ⊢ᵢ b) → (Γ ⊢ᵢ (a ⊃ b)) := by
  intro h
  induction h with
  | ax hmem =>
      rcases (Set.mem_insert_iff.mp hmem) with rfl | hpΓ
      ·
        exact id
      ·
        exact prf.mp (prf.k (Γ := Γ) (q := a)) (prf.ax hpΓ)
  | k =>
      exact lift (Γ := Γ) (a := a) (prf.k (Γ := Γ))
  | s =>
      exact lift (Γ := Γ) (a := a) (prf.s (Γ := Γ))
  | exf =>
      exact lift (Γ := Γ) (a := a) (prf.exf (Γ := Γ))
  | mp hpq hp ihpq ihp =>
      exact prf.mp (prf.mp (prf.s (Γ := Γ) (p := a)) ihpq) ihp
  | pr1 =>
      exact lift (Γ := Γ) (a := a) (prf.pr1 (Γ := Γ))
  | pr2 =>
      exact lift (Γ := Γ) (a := a) (prf.pr2 (Γ := Γ))
  | pair =>
      exact lift (Γ := Γ) (a := a) (prf.pair (Γ := Γ))
  | inr =>
      exact lift (Γ := Γ) (a := a) (prf.inr (Γ := Γ))
  | inl =>
      exact lift (Γ := Γ) (a := a) (prf.inl (Γ := Γ))
  | case =>
      exact lift (Γ := Γ) (a := a) (prf.case (Γ := Γ))

theorem contradeduction {Γ : Set Form} {p q : Form} :
  (Γ ⊬ᵢ (p ⊃ q)) → ((Γ ⸴ p) ⊬ᵢ q) := by
  intro hn h
  exact hn (deduction (Γ := Γ) (a := p) (b := q) h)

lemma or_elim {p q r : Form} {Γ : Set Form} :
  (Γ ⊢ᵢ (p ⋎ q)) → ((Γ ⸴ p) ⊢ᵢ r) → ((Γ ⸴ q) ⊢ᵢ r) → (Γ ⊢ᵢ r) := by
  intro hpq hp hq
  have hp' : Γ ⊢ᵢ (p ⊃ r) := deduction (Γ := Γ) (a := p) (b := r) hp
  have hq' : Γ ⊢ᵢ (q ⊃ r) := deduction (Γ := Γ) (a := q) (b := r) hq
  exact prf.mp (prf.mp (prf.mp (prf.case (Γ := Γ)) hp') hq') hpq

lemma and_elim1 {p q : Form} {Γ : Set Form} :
  (Γ ⊢ᵢ (p & q)) → (Γ ⊢ᵢ p) := by
  intro hpq
  exact prf.mp (prf.pr1 (Γ := Γ) (p := p) (q := q)) hpq

lemma and_elim2 {p q : Form} {Γ : Set Form} :
  (Γ ⊢ᵢ (p & q)) → (Γ ⊢ᵢ q) := by
  intro hpq
  exact prf.mp (prf.pr2 (Γ := Γ) (p := p) (q := q)) hpq

/- structural rule: weakening by subset -/
lemma sub_weak {Γ Δ : Set Form} {p : Form} :
  (Δ ⊢ᵢ p) → (Δ ⊆ Γ) → (Γ ⊢ᵢ p) := by
  intro hp hsub
  induction hp with
  | ax hmem =>
      exact ax (hsub hmem)
  | k  =>
      exact k
  | s  =>
      exact s
  | exf  =>
      exact exf
  | mp hpq hp ihpq ihp =>
      exact prf.mp ihpq ihp
  | pr1 =>
      exact pr1
  | pr2 =>
      exact pr2
  | pair=>
      exact pair
  | inr=>
      exact inr
  | inl =>
      exact inl
  | case =>
      exact case

end prf
/-- Forcing is monotone along R (persistence). -/
lemma mono_r {A : Type u} {M : emodel A} :
  ∀ p : Form, ∀ w1 w2 : A, w1 ∈ M.W → w2 ∈ M.W →
    (w1 ⊩{M} p) → M.R w1 w2 → (w2 ⊩{M} p) := by
  intro p
  induction p with
  | atom n =>
      intro w1 w2 hw1 hw2 h hR
      cases h with
      | inl hv => exact Or.inl (M.mono n w1 w2 hw1 hw2 hv hR)
      | inr hi => exact Or.inr (M.explodes_mono w1 w2 hw1 hw2 hi hR)
  | bot =>
      intro w1 w2 hw1 hw2 h hR
      exact M.explodes_mono w1 w2 hw1 hw2 h hR
  | imp p q ihp ihq =>
      intro w1 w2 hw1 hw2 h h12 w3 hw3 hw2' h23 hpw3
      have h13 : M.R w1 w3 := M.trans w1 hw1 w2 hw2 w3 hw3 h12 h23
      exact h w3 hw3 hw1 h13 hpw3
  | and p q ihp ihq =>
      intro w1 w2 hw1 hw2 h hR
      exact And.intro (ihp w1 w2 hw1 hw2 h.1 hR) (ihq w1 w2 hw1 hw2 h.2 hR)
  | or p q ihp ihq =>
      intro w1 w2 hw1 hw2 h hR
      cases h with
      | inl hp => exact Or.inl (ihp w1 w2 hw1 hw2 hp hR)
      | inr hq => exact Or.inr (ihq w1 w2 hw1 hw2 hq hR)

/-- At exploding worlds (`explodes`), every formula is forced. -/
lemma forces_of_explodes {A : Type u} (M : emodel A) :
  ∀ p : Form, ∀ w : A, w ∈ M.W → M.explodes w → (w ⊩{M} p) := by
  intro p
  induction p with
  | atom n =>
      intro w hw hi
      exact Or.inr hi
  | bot =>
      intro w hw hi
      exact hi
  | and p q ihp ihq =>
      intro w hw hi
      exact And.intro (ihp w hw hi) (ihq w hw hi)
  | or p q ihp ihq =>
      intro w hw hi
      exact Or.inl (ihp w hw hi)
  | imp p q ihp ihq =>
      intro w hw hi w' hw' hw'0 hww' hpw'
      have hi' : M.explodes w' := M.explodes_mono w w' hw hw' hi hww'
      exact ihq w' hw' hi'

/-- Soundness for the modified semantics: if `Γ ⊢ᵢ p`, then `Γ ⊨ᵢ p`. This is the propositional analogue of Veldman Theorem 1.4. -/
theorem prf_sound {Γ : Set Form} {p : Form} (h : Γ ⊢ᵢ p) : Γ ⊨ᵢ p := by
  intro A M w hw hΓ
  induction h with
  | ax hmem =>
      exact hΓ _ hmem
  | k =>
      intro w1 hw1 _ hww1 hpw1 w2 hw2 _ hw1w2 hqw2
      exact mono_r (M:=M) _ w1 w2 hw1 hw2 hpw1 hw1w2
  | s =>
      intro w1 hw1 _ hww1 hPQR w2 hw2 _ hw1w2 hPQ w3 hw3 _ hw2w3 hP
      have hw1w3 : M.R w1 w3 := M.trans w1 hw1 w2 hw2 w3 hw3 hw1w2 hw2w3
      have hQR : w3 ⊩{M} (_ ⊃ _) := hPQR w3 hw3 hw1 hw1w3 hP
      have hQ  := hPQ  w3 hw3 hw2 hw2w3 hP
      exact hQR w3 hw3 hw3 (M.refl w3 hw3) hQ
  | exf =>
      intro w1 hw1 _ hww1 hexplodes
      exact forces_of_explodes M _ w1 hw1 hexplodes
  | mp hpq hp ihpq ihp =>
      -- apply implication at w itself using reflexivity
      exact ihpq w hw hw (M.refl w hw) ihp
  | pr1 =>
      intro w1 hw1 _ hww1 hpq
      exact hpq.1
  | pr2 =>
      intro w1 hw1 _ hww1 hpq
      exact hpq.2
  | pair =>
      intro w1 hw1 _ hww1 hP w2 hw2 _ hw1w2 hQ

      have hP' := mono_r (M:=M) _ w1 w2 hw1 hw2 hP hw1w2
      exact And.intro hP' hQ
  | inr =>
      intro w1 hw1 _ hww1 hP
      exact Or.inl hP
  | inl =>
      intro w1 hw1 _ hww1 hQ
      exact Or.inr hQ
  | case =>
      intro w1 hw1 _ hww1 hPR w2 hw2 _ hw1w2 hQR w3 hw3 _ hw2w3 hPorQ
      have hw1w3 : M.R w1 w3 := M.trans w1 hw1 w2 hw2 w3 hw3 hw1w2 hw2w3
      cases hPorQ with
      | inl hP => exact hPR w3 hw3 hw1 hw1w3 hP
      | inr hQ => exact hQR w3 hw3 hw2 hw2w3 hQ

/-- Global (all-worlds) form matching the paper statement style. -/
def Models {A : Type u} (M : emodel A) (Γ : Set Form) : Prop :=
  ∀ w, w ∈ M.W → w ⊩{M} Γ

def Valid {A : Type u} (M : emodel A) (p : Form) : Prop :=
  ∀ w, w ∈ M.W → w ⊩{M} p

/-- Veldman Theorem 1.4 (propositional analogue): if Γ ⊢ᵢ p and M models Γ everywhere, then M validates p everywhere. -/
theorem veldman_1_4 {Γ : Set Form} {p : Form} (h : Γ ⊢ᵢ p) :
  ∀ {A : Type u} (M : emodel A), Models M Γ → Valid M p := by
  intro A M hΓ w hw
  exact (prf_sound (Γ:=Γ) (p:=p) h) M w hw (hΓ w hw)

/-- Deductive closure, corresponding to clause (i) in paper §2.2 after propositional specialization. -/
def IsTheory (Γ : Set Form) : Prop :=
  ∀ {p : Form}, (Γ ⊢ᵢ p) → p ∈ Γ

/-- Disjunctivity, corresponding to clause (ii) in paper §2.2. -/
def Disjunctive (Γ : Set Form) : Prop :=
  ∀ {p q : Form}, (Form.or p q) ∈ Γ → p ∈ Γ ∨ q ∈ Γ

/-- Semiregularity in the propositional fragment: paper §2.2 with the existential clause omitted because the language here has no quantifiers. -/
def SemiRegular (Γ : Set Form) : Prop :=
  IsTheory Γ ∧ Disjunctive Γ

/-- Membership gives a proof by the assumption rule. -/
lemma prf_of_mem {Γ : Set Form} {p : Form} (hp : p ∈ Γ) : Γ ⊢ᵢ p := by

  exact (by

    exact prf.ax hp
  )

/-- In a theory, any proof implies membership. -/
lemma mem_of_prf {Γ : Set Form} (hT : IsTheory Γ) {p : Form} (hp : Γ ⊢ᵢ p) : p ∈ Γ :=
  hT hp

/-- So inside a theory: membership ↔ provability. -/
lemma mem_iff_prf {Γ : Set Form} (hT : IsTheory Γ) {p : Form} : p ∈ Γ ↔ Γ ⊢ᵢ p := by
  constructor
  · intro hp; exact prf_of_mem (Γ:=Γ) hp
  · intro hp; exact hT hp

/-- In a semiregular Γ, proofs of (p ⊔ q) split. -/
lemma semiregular_disjunctive_prf
  {Γ : Set Form} (hSR : SemiRegular Γ) {p q : Form} :
  (Γ ⊢ᵢ Form.or p q) → ((Γ ⊢ᵢ p) ∨ Γ ⊢ᵢ q) := by
  intro hpq

  have hpq_mem : (Form.or p q) ∈ Γ := hSR.1 hpq

  cases hSR.2 (p:=p) (q:=q) hpq_mem with
  | inl hp_mem =>
      exact Or.inl (prf_of_mem (Γ:=Γ) hp_mem)
  | inr hq_mem =>
      exact Or.inr (prf_of_mem (Γ:=Γ) hq_mem)

/-- A theory is closed under modus ponens at the level of membership. -/
lemma theory_mp_mem
  {Γ : Set Form} (hT : IsTheory Γ) {p q : Form} :
  (p ⊃ q) ∈ Γ → p ∈ Γ → q ∈ Γ := by
  intro hpq hp
  have hpq' : Γ ⊢ᵢ (p ⊃ q) := prf_of_mem (Γ:=Γ) hpq
  have hp'  : Γ ⊢ᵢ p       := prf_of_mem (Γ:=Γ) hp

  have hq' : Γ ⊢ᵢ q := by
    exact prf.mp hpq' hp'
  exact hT hq'



end IPC
