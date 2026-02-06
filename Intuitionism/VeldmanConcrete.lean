import Intuitionism.fin_seq
import Intuitionism.fan
import Intuitionism.IPC
import Intuitionism.Enumeration

namespace Finset

/-
Finite-bounded Bool search utility.
Goal: turn “∃ i ≤ t, p i = true” into a computable Bool.
Later, in `Forced0b`, we use it to perform a bounded search for whether a derivation witness
appears within the first `t` steps.
-/

def anyUpTo : ℕ → (ℕ → Bool) → Bool
| 0,     p => p 0
| (t+1), p => anyUpTo t p || p (t+1)

/-
Uses: `anyUpTo`.
Result: `anyUpTo t p = true ↔ ∃ i ≤ t, p i = true`.
This will later serve as the bridge that turns
“there exists a derivation index i ≤ t” from a Bool statement into a Prop (and back).
-/
lemma anyUpTo_eq_true {p : ℕ → Bool} :
    ∀ t : ℕ, anyUpTo t p = true ↔ ∃ i : ℕ, i ≤ t ∧ p i = true := by
  intro t
  induction t with
  | zero =>
      constructor
      · intro h
        refine ⟨0, Nat.le_refl 0, ?_⟩
        simpa [anyUpTo] using h
      · rintro ⟨i, hi, hpi⟩
        have : i = 0 := Nat.eq_zero_of_le_zero hi
        subst this
        simpa [anyUpTo] using hpi
  | succ t ih =>
      constructor
      · intro h
        have h' : (anyUpTo t p || p (t+1)) = true := by
          simpa [anyUpTo] using h
        cases ht : anyUpTo t p with
        | true =>
            rcases (ih.mp ht) with ⟨i, hi, hpi⟩
            exact ⟨i, Nat.le_trans hi (Nat.le_succ t), hpi⟩
        | false =>
            cases hp : p (t+1) with
            | true =>
                refine ⟨t+1, Nat.le_refl (t+1), ?_⟩
                simp [hp]
            | false =>
                simp [ht, hp] at h'
      · rintro ⟨i, hi, hpi⟩
        have hcases : i < t+1 ∨ i = t+1 := Nat.lt_or_eq_of_le hi
        cases hcases with
        | inr heq =>
            subst heq
            cases ht : anyUpTo t p <;> simp [anyUpTo, ht, hpi]
        | inl hlt =>
            have hi' : i ≤ t := Nat.lt_succ_iff.mp hlt
            have ht : anyUpTo t p = true := ih.mpr ⟨i, hi', hpi⟩
            cases hp : p (t+1) <;> simp [anyUpTo, ht, hp]
/-
In `Forced0b` / `AllowedStepb` we frequently use `decide (...)` to produce a Bool.
Here we provide the general lemma `decide P = true ↔ P`.
-/
lemma decide_eq_true_iff (P : Prop) [Decidable P] : decide P = true ↔ P := by
  constructor
  · intro hdec
    cases hInst : (inferInstance : Decidable P) with
    | isTrue hp =>
        exact hp
    | isFalse hn =>
        have hfalse : decide P = false := by
          simp [decide, hInst]
        have : False := by
          have : (false = true) := by
            calc
              false = decide P := by symm; exact hfalse
              _     = true     := hdec
          cases this
        exact False.elim this
  · intro hP
    cases hInst : (inferInstance : Decidable P) with
    | isTrue hp =>
        simp [decide, hInst]
    | isFalse hn =>
        exact False.elim (hn hP)

end Finset

namespace IPC
open NatSeq
open fin_seq

open Finset

namespace VeldmanConcrete

/-
§3.31 “enumeration of derivations”
In the paper we enumerate Sent and derivations:
- W₁, W₂, ... : Sent
- d₁, d₂, ... : derivations

Here, in the propositional version:
- Sent is just `Form` (see the previous IPC code block).
- A derivation code is represented as (Γ, A): Γ is a finite set of premises, A is the conclusion.
- `DerOK` means: A is provable from Γ (viewed as a Set) in the Hilbert IPC proof system.
-/
abbrev DerCode : Type := Finset Form × Form
def DerOK (d : DerCode) : Prop := ((↑d.1 : Set Form) ⊢ᵢ d.2)



/-
Corresponds to §3.32: the simultaneous recursive definition of Σ, Γ, D.
In the paper, Σ(a), Γ(a), D(a) are defined by recursion on the length of the finite sequence `a`:
- admitted/forbidden status of Σ(a*q)
- finite-set update of Γ(a*q)
- constant-set update of D(a*q) (can be ignored in the propositional version)

Here we package the information needed during recursion into a `State`:
- t     : current time step
- prev1 : the previous choice q
- prev2 : the choice before the previous one
- Fs    : the current Γ(a)
-/
structure State where
  t : ℕ
  prev1 : ℕ
  prev2 : ℕ
  Fs : Finset Form

/-
Corresponds to §3.32: the initial values for the empty sequence.
Paper: Σ(⟨⟩)=0, Γ(⟨⟩)=∅ (and also D(⟨⟩)=X₀; omitted here since the propositional version has no constants).
Here: t=0, prev1=0, prev2=0, Fs=∅.
-/
def initState : State := ⟨0, 0, 0, ∅⟩

/-
§3.31: enumerations of Sent and derivations + technical assumptions
- W : ℕ → Form
  corresponds to the paper’s enumeration W₁, W₂, ... (here we require surjectivity: every Form appears)
- d : ℕ → DerCode
  corresponds to the paper’s enumeration d₁, d₂, ... of derivations (here a derivation is coded as (Γ, A))
and additionally:
- d_sound    : every enumerated derivation code is a correct derivation (`DerOK`)
- d_complete : every provable judgment (Γ ⊢ A) appears somewhere in the enumeration: ∃ i, d i = (Γ, A)

This is a formalizable version of “we list all derivations”.
-/
structure Enumerations where
  W : ℕ → Form
  d : ℕ → DerCode
  W_surj : Function.Surjective W
  d_sound : ∀ i : ℕ, DerOK (d i)
  d_complete :
    ∀ (Γ : Finset Form) (A : Form),
      ((↑Γ : Set Form) ⊢ᵢ A) → ∃ i : ℕ, d i = (Γ, A)

/-
§3.31: ⟪n,m,k⟫
We fix a bijection ⟪·⟫ : Nat² × {0,1,2} → Nat to schedule three kinds of steps:
- k=0: Case 1 (check whether a formula Wₙ is “forced” to be added to Γ)
- k=1: Case 2 (extend the constant set D)
- k=2: Case 3 (forced action for a disjunction/∃ possibly added two steps ago)

Here `schedDecode` is the decoder you already have in the project:
- decN t : extract the current “n” being handled
- decK t : extract which class of step we are in, k ∈ Fin 3 (k0/k1/k2)
-/

def decN (t : ℕ) : ℕ := (schedDecode t).1
def decK (t : ℕ) : Fin 3 := (schedDecode t).2.2

/-
§3.32 Case 1: deciding whether a formula is forced to be added
Intuition in the paper: if Wₙ is already derivable from the current Γ(a) (using “the first p derivations”),
then we are not allowed to keep it out; we must take the “add it” branch.

Here `Forced0` (Prop) expresses:
- the current step is k0
- ∃ i ≤ t such that the conclusion of d i is exactly W(decN t)
- and the premise set (E.d i).1 is included in the current Fs
(In the propositional version there is no IC/D(a) side condition, so we only keep
“premise inclusion + conclusion match”.)
-/

def Forced0 (E : Enumerations) (st : State) : Prop :=
  decK st.t = k0 ∧
  ∃ i : ℕ, i ≤ st.t ∧
    (E.d i).2 = E.W (decN st.t) ∧
    (E.d i).1 ⊆ st.Fs

/-
§3.32 Case 1 (Bool version)
Uses:
- anyUpTo: bounded search for i ≤ t
- decide : turn a decidable Prop into Bool

Behavior:
- only when decK = k0 do we search for a witness; otherwise return false.
-/
def Forced0b (E : Enumerations) (st : State) : Bool :=
  if hk : decK st.t = k0 then
    anyUpTo st.t (fun i =>
      decide ((E.d i).2 = E.W (decN st.t) ∧ (E.d i).1 ⊆ st.Fs))
  else
    false

/-
§3.32: recursive update of the complementary law Γ (propositional version),
i.e. how Γ(a*q) is obtained from Γ(a).
Here `FStep` computes “the next Fs = Γ(extend s q)”:

- Case k0 (paper Case 1):
  * q=1: insert the currently considered formula Wₙ into Fs
  * q≠1: leave Fs unchanged
- Case k1 (paper Case 2, degenerated in the propositional version):
  * the paper extends D(a), but Fs itself does not change; so we keep Fs unchanged.
- Case k2 (paper Case 3; propositional version keeps only the disjunction subcase):
  * if Wₙ is (A ⋎ B) and two steps ago prev2=1 (meaning we “chose to add” two steps ago),
    then we must split: q=1 adds A, q=2 adds B (paper Subcase 3.2)
  * otherwise Fs is unchanged
-/
def FStep (E : Enumerations) (st : State) (q : ℕ) : Finset Form :=
  let n := decN st.t
  let k := decK st.t
  if hk0 : k = k0 then
    if q = 1 then insert (E.W n) st.Fs else st.Fs
  else if hk1 : k = k1 then
    st.Fs
  else
    match E.W n with
    | Form.or A B =>
        if st.prev2 = 1 then
          if q = 1 then insert A st.Fs
          else if q = 2 then insert B st.Fs
          else st.Fs
        else st.Fs
    | _ => st.Fs

/-
Corresponds to §3.1 + §3.32: the “allowed next-step choice rule” for the spread law Σ.
Paper: Σ(a*q)=0/1 determines whether a node is admitted.
Here `AllowedStepb` decides whether, in state st (corresponding to the current prefix a),
a number q is an allowed extension.

Correspondence (simplified for the propositional version):
- k0 (Case 1):
  * if Forced0b=true (forced to add), only allow q=1
  * otherwise allow q=0 or q=1
- k1 (Case 2): propositional version allows only q=0 (a “fixed action / no constant extension”)
- k2 (Case 3):
  * if Wₙ is a disjunction and prev2=1: allow q=1 or 2 (paper Subcase 3.2)
  * otherwise allow only q=0
-/
def AllowedStepb (E : Enumerations) (st : State) (q : ℕ) : Bool :=
  let n := decN st.t
  let k := decK st.t
  if hk0 : k = k0 then
    if Forced0b E st then
      decide (q = 1)
    else
      decide (q = 0 ∨ q = 1)
  else if hk1 : k = k1 then
    decide (q = 0)
  else
    match E.W n with
    | Form.or _ _ =>
        if st.prev2 = 1 then
          decide (q = 1 ∨ q = 2)
        else
          decide (q = 0)
    | _ =>
        decide (q = 0)

/-
论文 §3.32：状态转移（读入一个 q）
用到：`FStep`。
把 t 加 1，并滚动 prev2/prev1，同时更新 Fs。
-/
def step (E : Enumerations) (st : State) (q : ℕ) : State :=
{ t := st.t + 1
  prev2 := st.prev1
  prev1 := q
  Fs := FStep E st q }

/-
Paper §3.32: state transition (consuming a q)
Uses: `FStep`.
Increment t by 1, shift prev2/prev1, and update Fs.
-/

def runStateAux (E : Enumerations) (s : fin_seq) :
  (n : ℕ) → n ≤ s.len → State
| 0, _ => initState
| n+1, hn =>
    let st := runStateAux E s n (Nat.le_of_succ_le hn)
    let q  := s.seq ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    step E st q

def runState (E : Enumerations) (s : fin_seq) : State :=
  runStateAux E s s.len le_rfl

/-
Paper §3.1: recursive computation over Seq (finite sequences of naturals)
Here `runStateAux` / `runState` treat a `fin_seq s` as a “path prefix a”
and compute the corresponding `State` (containing Γ(a)=Fs).
-/

def admittedAuxb (E : Enumerations) (s : fin_seq) :
  (n : ℕ) → n ≤ s.len → Bool
| 0, _ => true
| n+1, hn =>
    admittedAuxb E s n (Nat.le_of_succ_le hn) &&
    let st := runStateAux E s n (Nat.le_of_succ_le hn)
    let q  := s.seq ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    AllowedStepb E st q
/-
Corresponds to §3.1: implementing “Σ(a)=0” as a step-by-step check along the path
`admittedAuxb E s n` checks the first n steps of s, requiring each step q to satisfy `AllowedStepb`.
`Admittedb E s` checks that the whole sequence s is admitted (corresponding to Σ(s)=0).
-/
def Admittedb (E : Enumerations) (s : fin_seq) : Bool :=
  admittedAuxb E s s.len le_rfl

/-
Corresponds to §3.1: spread law Σ : Seq → {0,1}
Paper: Σ(a)=0 means admitted.
Here: if Admittedb=true then Sigma=0, otherwise Sigma=1.
-/

def Sigma (E : Enumerations) (s : fin_seq) : ℕ :=
  if Admittedb E s then 0 else 1

/-
Corresponds to §3.1: complementary law Γ
Paper: Γ is defined only on admitted nodes, producing a finite subset.
Here we first give a raw function `F`: map s to the Fs produced by runState (i.e. Γ(s)).
Later we package it as `FS : CompLaw (Sigma E)`.
-/
def F (E : Enumerations) : fin_seq → Finset Form :=
  fun s => (runState E s).Fs



/-- Prefix ⇒ monotonicity of length -/
lemma Prefix_len_le {s t : fin_seq} (h : Prefix s t) : s.len ≤ t.len := by
  rcases h with ⟨hle, _⟩
  exact hle

/-- Under Prefix, the symbols at the same position are equal -/
lemma seq_eq_of_Prefix {s t : fin_seq} (h : Prefix s t) {k : ℕ} (hk : k < s.len) :
    t.seq ⟨k, Nat.lt_of_lt_of_le hk (Prefix_len_le h)⟩ = s.seq ⟨k, hk⟩ := by
  rcases h with ⟨hle, hseq⟩
  let iS : Fin s.len := ⟨k, hk⟩
  have hcast : (Fin.castLE hle iS : Fin t.len) = ⟨k, Nat.lt_of_lt_of_le hk hle⟩ := by
    apply Fin.ext; rfl
  have := hseq iS
  simpa [hcast] using this.symm

/-- runStateAux is insensitive to the particular “≤ proof” (proof-irrelevance) -/
lemma runStateAux_proof_irrel (E : Enumerations) (s : fin_seq) :
    ∀ n (h₁ h₂ : n ≤ s.len), runStateAux E s n h₁ = runStateAux E s n h₂ := by
  intro n
  induction n with
  | zero =>
      intro h₁ h₂
      simp [runStateAux]
  | succ n ih =>
      intro h₁ h₂
      have h₁' : n ≤ s.len := Nat.le_of_succ_le h₁
      have h₂' : n ≤ s.len := Nat.le_of_succ_le h₂
      have hst : runStateAux E s n h₁' = runStateAux E s n h₂' := ih _ _
      have hnlt₁ : n < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) h₁
      have hnlt₂ : n < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) h₂
      have hFin : (⟨n, hnlt₁⟩ : Fin s.len) = ⟨n, hnlt₂⟩ := by
        apply Fin.ext; rfl
      have hq : s.seq ⟨n, hnlt₁⟩ = s.seq ⟨n, hnlt₂⟩ := by
        simp [hFin]
      simp [runStateAux, hst, hq, step]

/-- admittedAuxb is likewise insensitive to the particular “≤ proof” -/

lemma admittedAuxb_proof_irrel (E : Enumerations) (s : fin_seq) :
    ∀ n (h₁ h₂ : n ≤ s.len), admittedAuxb E s n h₁ = admittedAuxb E s n h₂ := by
  intro n
  induction n with
  | zero =>
      intro h₁ h₂
      simp [admittedAuxb]
  | succ n ih =>
      intro h₁ h₂
      have h₁' : n ≤ s.len := Nat.le_of_succ_le h₁
      have h₂' : n ≤ s.len := Nat.le_of_succ_le h₂
      have had : admittedAuxb E s n h₁' = admittedAuxb E s n h₂' := ih _ _
      have hst : runStateAux E s n h₁' = runStateAux E s n h₂' :=
        runStateAux_proof_irrel (E := E) (s := s) n h₁' h₂'
      have hnlt₁ : n < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) h₁
      have hnlt₂ : n < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) h₂
      have hFin : (⟨n, hnlt₁⟩ : Fin s.len) = ⟨n, hnlt₂⟩ := by
        apply Fin.ext; rfl
      have hq : s.seq ⟨n, hnlt₁⟩ = s.seq ⟨n, hnlt₂⟩ := by
        simp [hFin]
      simp [admittedAuxb, had, hst, hq]

/-- Prefix ⇒ runStateAux agrees on the common prefix length -/

lemma runStateAux_eq_of_Prefix (E : Enumerations) {s t : fin_seq} (h : Prefix s t) :
    ∀ n (hn : n ≤ s.len),
      runStateAux E t n (Nat.le_trans hn (Prefix_len_le h))
        = runStateAux E s n hn := by
  intro n hn
  induction n with
  | zero =>
      simp [runStateAux]
  | succ n ih =>
      have hn' : n ≤ s.len := Nat.le_of_succ_le hn
      have hle : s.len ≤ t.len := Prefix_len_le h
      have ht  : n.succ ≤ t.len := Nat.le_trans hn hle
      have ht' : n ≤ t.len := Nat.le_of_succ_le ht
      have ih' :
          runStateAux E t n ht' = runStateAux E s n hn' := by
        have := ih hn'
        have hpi :
            runStateAux E t n (Nat.le_trans hn' hle)
              = runStateAux E t n ht' := by
          symm
          exact runStateAux_proof_irrel (E := E) (s := t) n ht' (Nat.le_trans hn' hle)
        simpa [hpi] using this
      have hnlt_s : n < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hnlt_t : n < t.len := Nat.lt_of_lt_of_le hnlt_s hle
      have hq : t.seq ⟨n, hnlt_t⟩ = s.seq ⟨n, hnlt_s⟩ := seq_eq_of_Prefix (h := h) hnlt_s
      simp [runStateAux, ih', step, hq]

/-- Prefix ⇒ admittedAuxb agrees on the common prefix length -/
lemma admittedAuxb_eq_of_Prefix (E : Enumerations) {s t : fin_seq} (h : Prefix s t) :
    ∀ n (hn : n ≤ s.len),
      admittedAuxb E t n (Nat.le_trans hn (Prefix_len_le h))
        = admittedAuxb E s n hn := by
  intro n hn
  induction n with
  | zero =>
      simp [admittedAuxb]
  | succ n ih =>
      have hn' : n ≤ s.len := Nat.le_of_succ_le hn
      have hle : s.len ≤ t.len := Prefix_len_le h
      have ht  : n.succ ≤ t.len := Nat.le_trans hn hle
      have ht' : n ≤ t.len := Nat.le_of_succ_le ht
      have ih' :
          admittedAuxb E t n ht' = admittedAuxb E s n hn' := by
        have := ih hn'
        have hpi :
            admittedAuxb E t n (Nat.le_trans hn' hle)
              = admittedAuxb E t n ht' := by
          symm
          exact admittedAuxb_proof_irrel (E := E) (s := t) n ht' (Nat.le_trans hn' hle)
        simpa [hpi] using this
      have hst' :
          runStateAux E t n ht' = runStateAux E s n hn' := by
        have := runStateAux_eq_of_Prefix (E := E) (h := h) n hn'
        have hpi :
            runStateAux E t n (Nat.le_trans hn' hle)
              = runStateAux E t n ht' := by
          symm
          exact runStateAux_proof_irrel (E := E) (s := t) n ht' (Nat.le_trans hn' hle)
        simpa [hpi] using this
      have hnlt_s : n < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hnlt_t : n < t.len := Nat.lt_of_lt_of_le hnlt_s hle
      have hq : t.seq ⟨n, hnlt_t⟩ = s.seq ⟨n, hnlt_s⟩ := seq_eq_of_Prefix (h := h) hnlt_s
      simp [admittedAuxb, ih', hst', hq, AllowedStepb]

/-
Core monotonicity of Γ in §3.1: Fs only grows as we step forward.
First show that a single `FStep` always contains the previous Fs (subset).
This will be used in the final `F_mono`.
-/
lemma FStep_mono (E : Enumerations) (st : State) (q : ℕ) :
    st.Fs ⊆ FStep E st q := by
  unfold FStep
  by_cases hk0 : decK st.t = k0
  · simp [hk0]
    by_cases hq : q = 1
    · subst hq
      exact Finset.subset_insert _ _
    · simp [hq, Finset.Subset.rfl]
  · by_cases hk1 : decK st.t = k1
    · have hk10 : (k1 : Fin 3) ≠ k0 := by decide
      simp [hk0, hk1, hk10]
    · simp [hk0, hk1]
      cases hW : E.W (decN st.t) with
      | or A B =>
          by_cases hp : st.prev2 = 1
          · simp [hW, hp]
            by_cases hq1 : q = 1
            · subst hq1
              exact Finset.subset_insert _ _
            · by_cases hq2 : q = 2
              · subst hq2
                exact Finset.subset_insert _ _
              · simp [hq1, hq2, Finset.Subset.rfl]
          · simp [hW, hp, Finset.Subset.rfl]
      | atom n =>
          simp [hW, Finset.Subset.rfl]
      | «I» =>
          simp [hW, Finset.Subset.rfl]
      | imp p q =>
          simp [hW, Finset.Subset.rfl]
      | and p q =>
          simp [hW, Finset.Subset.rfl]

/-- After one `step`, Fs is monotone (only grows) -/
lemma step_Fs_mono (E : Enumerations) (st : State) (q : ℕ) :
    st.Fs ⊆ (step E st q).Fs := by
  simpa [step] using (FStep_mono (E := E) (st := st) (q := q))

/-- In runStateAux, Fs is monotone across two consecutive steps -/
lemma runStateAux_Fs_mono_succ (E : Enumerations) (s : fin_seq) (n : ℕ)
    (hn : n.succ ≤ s.len) :
    (runStateAux E s n (Nat.le_of_succ_le hn)).Fs ⊆ (runStateAux E s n.succ hn).Fs := by
  simp [runStateAux, step_Fs_mono]

/-- In runStateAux, Fs is monotone when n ≤ m -/
lemma runStateAux_Fs_mono_le (E : Enumerations) (s : fin_seq) :
  ∀ {n m : ℕ} (hn : n ≤ s.len) (hm : m ≤ s.len), n ≤ m →
      (runStateAux E s n hn).Fs ⊆ (runStateAux E s m hm).Fs := by
  intro n m hn hm hnm
  induction hnm with
  | refl =>
      have hEq : runStateAux E s n hn = runStateAux E s n hm :=
        runStateAux_proof_irrel (E := E) (s := s) n hn hm
      simpa [hEq] using (Finset.subset_rfl : (runStateAux E s n hn).Fs ⊆ (runStateAux E s n hn).Fs)
  | @step m hnm ih =>
      have hm' : m ≤ s.len := Nat.le_of_succ_le hm
      have ih' :
          (runStateAux E s n hn).Fs ⊆ (runStateAux E s m hm').Fs :=
        ih hm'
      have hstep :
          (runStateAux E s m hm').Fs ⊆ (runStateAux E s m.succ hm).Fs := by
        simpa using runStateAux_Fs_mono_succ (E := E) (s := s) (n := m) (hn := hm)
      intro x hx
      exact hstep (ih' hx)

/-
Rewriting lemma: Sigma ↔ Admittedb
Uses: `Sigma`, `Admittedb`.
-/

lemma Sigma_eq_zero_iff (E : Enumerations) (s : fin_seq) :
    Sigma E s = 0 ↔ Admittedb E s = true := by
  unfold Sigma
  cases hs : Admittedb E s <;> simp [hs]


/-
Paper §3.32 base case: the empty sequence is admitted
Uses: Admittedb / admittedAuxb / empty_seq.
Corresponds to: Σ(⟨⟩)=0 in the paper.
-/
lemma Admittedb_empty (E : Enumerations) : Admittedb E empty_seq = true := by
  simp [Admittedb, admittedAuxb, empty_seq]

/-- §3.32: Sigma(⟨⟩)=0 -/
lemma Sigma_empty (E : Enumerations) : Sigma E empty_seq = 0 := by
  have : Admittedb E empty_seq = true := Admittedb_empty (E := E)
  simpa [Sigma_eq_zero_iff] using this

/-- A Prefix constructor: s is a prefix of s⋆[q] -/
lemma Prefix_child (s : fin_seq) (q : ℕ) : Prefix s (extend s (singleton q)) := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  intro i
  have hi : (Fin.castLE (Nat.le_add_right s.len 1) i).val < s.len := by
    simp
  simp [fin_seq.extend, hi]

/-- The last element of extend s [q] is q -/
lemma extend_singleton_last (s : fin_seq) (q : ℕ) :
    (extend s (singleton q)).seq
      ⟨s.len, by
        simp [fin_seq.extend, fin_seq.singleton]⟩
    = q := by
  have hnot : ¬ (s.len < s.len) := Nat.lt_irrefl _
  simp [fin_seq.extend, fin_seq.singleton, hnot, Nat.sub_self]

/-
§3.1: “constructive choice” used to prove spreadness
(for every admitted node there exists an admitted child).
Given a state st, `chooseNext` constructs a q such that AllowedStepb E st q = true.
This provides the witness for “there exists an extendable branch” in the spread law.
-/
def chooseNext (E : Enumerations) (st : State) : ℕ :=
  let n := decN st.t
  let k := decK st.t
  if hk0 : k = k0 then
    if Forced0b E st then 1 else 0
  else if hk1 : k = k1 then
    0
  else
    match E.W n with
    | Form.or _ _ =>
        if st.prev2 = 1 then 1 else 0
    | _ => 0

/-
Correctness of chooseNext
Uses: chooseNext, AllowedStepb.
Result: AllowedStepb E st (chooseNext E st) = true.
-/
lemma Allowed_chooseNext (E : Enumerations) (st : State) :
    AllowedStepb E st (chooseNext E st) = true := by
  unfold chooseNext AllowedStepb
  by_cases hk0 : decK st.t = k0
  · simp [hk0]
  · by_cases hk1 : decK st.t = k1
    · have hk10 : (k1 : Fin 3) ≠ k0 := by decide
      simp [hk0, hk1, hk10]
    · simp [hk0, hk1]
      cases hW : E.W (decN st.t) <;> simp [hW]
      · by_cases hp : st.prev2 = 1 <;> simp [hp]


lemma and_eq_true_iff (a b : Bool) :
    (a && b = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

/-
Expanded form of the spread law
The paper’s spread law requires, informally:
“a node is admitted iff it lies in the spread, and it can be extended to some admitted child.”
-/
lemma Sigma_spread_iff (E : Enumerations) (s : fin_seq) :
    Sigma E s = 0 ↔ ∃ n : ℕ, Sigma E (extend s (singleton n)) = 0 := by
  constructor
  · intro hs0
    have hsAd : Admittedb E s = true := (Sigma_eq_zero_iff (E := E) s).1 hs0

    let st : State := runState E s
    let q  : ℕ := chooseNext E st
    refine ⟨q, ?_⟩
    let child : fin_seq := extend s (singleton q)

    have hSucc : s.len.succ ≤ child.len := by
      simp [child, fin_seq.extend, fin_seq.singleton]
    have hPred : s.len ≤ child.len := Nat.le_of_succ_le hSucc

    have hPref : Prefix s child := Prefix_child s q
    have hEqAdm :
        admittedAuxb E child s.len hPred = admittedAuxb E s s.len le_rfl :=
      admittedAuxb_eq_of_Prefix (E := E) (h := hPref) s.len le_rfl
    have hsAux : admittedAuxb E s s.len le_rfl = true := by
      simpa [Admittedb] using hsAd
    have hChildAux_pred : admittedAuxb E child s.len hPred = true := by
      simpa [hEqAdm] using hsAux

    have hPred' : s.len ≤ child.len := Nat.le_of_succ_le hSucc
    have hChildAux :
        admittedAuxb E child s.len hPred' = true := by
      have hpi :
          admittedAuxb E child s.len hPred' = admittedAuxb E child s.len hPred :=
        admittedAuxb_proof_irrel (E := E) (s := child) s.len hPred' hPred
      simpa [hpi] using hChildAux_pred

    have hStateEq :
        runStateAux E child s.len hPred' = runStateAux E s s.len le_rfl := by
      have hEq :=
        runStateAux_eq_of_Prefix (E := E) (h := hPref) s.len le_rfl
      have hpi :
          runStateAux E child s.len hPred = runStateAux E child s.len hPred' :=
        runStateAux_proof_irrel (E := E) (s := child) s.len hPred hPred'
      simpa [hpi] using hEq

    have hAllowed : AllowedStepb E (runState E s) q = true := by
      dsimp [st, q]
      simp [runState, Allowed_chooseNext]

    have hChildAd : Admittedb E child = true := by
      have hnChild : s.len.succ ≤ child.len := hSucc
      have hChildAux0 :
          admittedAuxb E child s.len (Nat.le_of_succ_le hnChild) = true := by
        have hpi :
            admittedAuxb E child s.len (Nat.le_of_succ_le hnChild)
              = admittedAuxb E child s.len hPred' :=
          admittedAuxb_proof_irrel (E := E) (s := child) s.len
            (Nat.le_of_succ_le hnChild) hPred'
        simpa [hpi] using hChildAux

      have hAllowedChild :
          AllowedStepb E (runStateAux E child s.len (Nat.le_of_succ_le hnChild))
            (child.seq ⟨s.len, by
              simp [child, fin_seq.extend, fin_seq.singleton]⟩)
            = true := by
        have hDigit :
            child.seq ⟨s.len, by
              simp [child, fin_seq.extend, fin_seq.singleton]⟩ = q := by
          simpa [child] using extend_singleton_last s q

        have hStateEq' :
            runStateAux E child s.len (Nat.le_of_succ_le hnChild)
              = runStateAux E s s.len le_rfl := by
          have hpi :
              runStateAux E child s.len (Nat.le_of_succ_le hnChild)
                = runStateAux E child s.len hPred' :=
            runStateAux_proof_irrel (E := E) (s := child) s.len
              (Nat.le_of_succ_le hnChild) hPred'
          simpa [hpi] using hStateEq

        simpa [hStateEq', hDigit, runState] using hAllowed

      have hAuxSucc :
          admittedAuxb E child s.len.succ hnChild = true := by
        simp [admittedAuxb, hnChild, hChildAux0, hAllowedChild]

      simpa [Admittedb, child, fin_seq.extend, fin_seq.singleton] using hAuxSucc

    exact (Sigma_eq_zero_iff (E := E) child).2 hChildAd

  · rintro ⟨n, hn0⟩
    let child : fin_seq := extend s (singleton n)
    have hChildAd : Admittedb E child = true :=
      (Sigma_eq_zero_iff (E := E) child).1 hn0

    have hSucc : s.len.succ ≤ child.len := by
      simp [child, fin_seq.extend, fin_seq.singleton]
    have hPred' : s.len ≤ child.len := Nat.le_of_succ_le hSucc

    have hChildAux_succ :
        admittedAuxb E child s.len.succ (by
          simp [child, fin_seq.extend, fin_seq.singleton]) = true := by
      simpa [Admittedb, child] using hChildAd

    have hChildAux_pred : admittedAuxb E child s.len hPred' = true := by
      have : admittedAuxb E child s.len hPred' &&
              (let st := runStateAux E child s.len hPred'
               let q  := child.seq ⟨s.len, by
                 simp [child, fin_seq.extend, fin_seq.singleton]⟩
               AllowedStepb E st q) = true := by
        simpa [admittedAuxb, child] using hChildAux_succ
      exact ((and_eq_true_iff _ _).1 this).1

    have hPref : Prefix s child := Prefix_child s n
    have hEqAdm :
        admittedAuxb E child s.len hPred' = admittedAuxb E s s.len le_rfl := by
      have hle : s.len ≤ child.len := Prefix_len_le hPref
      have hEq := admittedAuxb_eq_of_Prefix (E := E) (h := hPref) s.len le_rfl
      have hpi :
          admittedAuxb E child s.len hle = admittedAuxb E child s.len hPred' :=
        admittedAuxb_proof_irrel (E := E) (s := child) s.len hle hPred'
      simpa [hpi] using hEq

    have hsAux : admittedAuxb E s s.len le_rfl = true := by
      simpa [hEqAdm] using hChildAux_pred

    have hsAd : Admittedb E s = true := by
      simpa [Admittedb] using hsAux

    exact (Sigma_eq_zero_iff (E := E) s).2 hsAd

/-
§3.1: finite branching constraint for “fan”
The paper mentions the fan theorem (and the binary fan).
Here `is_fan_law` needs an explicit branching bound:
AllowedStepb=true ⇒ q ≤ 2
(i.e. at each step only 0/1/2 can occur, so we get a uniform finite branching bound.)
-/

lemma AllowedStepb_bound (E : Enumerations) (st : State) (q : ℕ) :
    AllowedStepb E st q = true → q ≤ 2 := by
  intro h
  unfold AllowedStepb at h
  by_cases hk0 : decK st.t = k0
  · simp [hk0] at h
    by_cases hF : Forced0b E st
    · simp [hF] at h
      subst h
      decide
    · simp [hF] at h
      rcases h with rfl | rfl <;> decide
  by_cases hk1 : decK st.t = k1
  · simp [hk0, hk1] at h
    subst h
    decide
  · simp [hk0, hk1] at h
    cases hW : E.W (decN st.t) <;> simp [hW] at h
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · by_cases hp : st.prev2 = 1
      · simp [hp] at h
        rcases h with rfl | rfl <;> decide
      · simp [hp] at h
        subst h
        decide
/-
§3.1: proving “Σ is a fan law (= spread + bounded branching)”
This combines the two ingredients above:
- spreadness: Sigma_empty + Sigma_spread_iff
- branching bound: AllowedStepb_bound (bound = 2 here)
-/


theorem Sigma_is_fan_law (E : Enumerations) : is_fan_law (Sigma E) := by
  refine And.intro ?spread ?bound
  · refine And.intro (Sigma_empty (E := E)) ?_
    intro s
    exact Sigma_spread_iff (E := E) s
  · intro s hs0
    refine ⟨2, ?_⟩
    intro m hm0

    have hChildAd : Admittedb E (extend s (singleton m)) = true :=
      (Sigma_eq_zero_iff (E := E) (extend s (singleton m))).1 hm0

    let child : fin_seq := extend s (singleton m)
    have hSucc : s.len.succ ≤ child.len := by
      simp [child, fin_seq.extend, fin_seq.singleton]
    have hPred' : s.len ≤ child.len := Nat.le_of_succ_le hSucc

    have hAux_succ :
        admittedAuxb E child s.len.succ (by
          simp [child, fin_seq.extend, fin_seq.singleton]) = true := by
      simpa [Admittedb, child] using hChildAd

    have hAnd :
        admittedAuxb E child s.len hPred' &&
          (let st := runStateAux E child s.len hPred'
           let q  := child.seq ⟨s.len, by
             simp [child, fin_seq.extend, fin_seq.singleton]⟩
           AllowedStepb E st q) = true := by
      simpa [admittedAuxb, child] using hAux_succ

    have hLastAllowed :
    (let st := runStateAux E child s.len hPred'
     let q  := child.seq ⟨s.len, by
       simp [child, fin_seq.extend, fin_seq.singleton]⟩
     AllowedStepb E st q) = true := by
      let b : Bool :=
        (let st := runStateAux E child s.len hPred'
         let q  := child.seq ⟨s.len, by
           simp[child, fin_seq.extend, fin_seq.singleton]⟩
         AllowedStepb E st q)
      have hab :
        (admittedAuxb E child s.len hPred' = true ∧ b = true) :=
          (and_eq_true_iff (admittedAuxb E child s.len hPred') b).1 hAnd
      simpa [b] using hab.2

    have hPref : Prefix s child := Prefix_child s m
    have hStateEq :
        runStateAux E child s.len hPred' = runStateAux E s s.len le_rfl := by
      have hle : s.len ≤ child.len := Prefix_len_le hPref
      have hEq := runStateAux_eq_of_Prefix (E := E) (h := hPref) s.len le_rfl
      have hpi :
          runStateAux E child s.len hle = runStateAux E child s.len hPred' :=
        runStateAux_proof_irrel (E := E) (s := child) s.len hle hPred'
      simpa [hpi] using hEq

    have hDigit :
        child.seq ⟨s.len, by simp [child, fin_seq.extend, fin_seq.singleton]⟩ = m := by
      simpa [child] using extend_singleton_last s m

    have hAllowed : AllowedStepb E (runState E s) m = true := by
      have : AllowedStepb E (runStateAux E child s.len hPred')
                (child.seq ⟨s.len, by simp [child, fin_seq.extend, fin_seq.singleton]⟩) = true := by
        simpa using hLastAllowed
      simpa [runState, hStateEq, hDigit] using this

    exact AllowedStepb_bound (E := E) (st := runState E s) (q := m) hAllowed

/-
§3.1: packaging the complementary law Γ as a `CompLaw`
- `CompLaw (Sigma E)`: a “complementary law” meaningful only on admitted nodes
- `FS E s`: the Fs computed by runState (i.e. Γ(s))
-/
def FS (E : Enumerations) : CompLaw (Sigma E) := fun s => (runState E s).Fs

/-- §3.32: Γ(⟨⟩)=∅ (propositional version) -/
lemma FS_empty (E : Enumerations) : FS E empty_seq = ∅ := by
  simp [FS, runState, runStateAux, initState, empty_seq]

/-
Paper requirement (note: the paper’s “b ⊆ a” means “a is an initial segment of b”):
If t extends s (Prefix) and both are admitted, then Γ(s) ⊆ Γ(t).

Here `F_mono` proves that `FS E` is monotone w.r.t. Prefix on admitted nodes.
Key lemmas used:
- runStateAux_eq_of_Prefix: states coincide on the common prefix
- runStateAux_Fs_mono_le: within the same sequence, Fs is monotone with length
-/
lemma F_mono (E : Enumerations) : MonotoneOnAdmitted (Sigma E) (FS E) := by
  intro s t hPre _hs0 _ht0

  have hle : s.len ≤ t.len := Prefix_len_le hPre
  have hEq :
      runStateAux E t s.len hle = runStateAux E s s.len le_rfl := by
    have hEq0 := runStateAux_eq_of_Prefix (E := E) (h := hPre) s.len le_rfl
    have hle0 : s.len ≤ t.len := Prefix_len_le hPre
    have hpi :
        runStateAux E t s.len hle0 = runStateAux E t s.len hle :=
      runStateAux_proof_irrel (E := E) (s := t) s.len hle0 hle
    simpa [hpi] using hEq0

  have hmono :
      (runStateAux E t s.len hle).Fs ⊆ (runStateAux E t t.len le_rfl).Fs :=
    runStateAux_Fs_mono_le (E := E) (s := t) (hn := hle) (hm := le_rfl) hle

  simpa [FS, runState, hEq] using hmono

/-
§3.1: packaging (Σ, Γ) as a “fan/spread + complementary law” object
In the paper, ⟨Σ, Γ⟩ represents a spread (then combined with the Brouwer–Kripke principle / fan theorem).
Here `VeldmanFan` collects the required components:
- S        : fan law (corresponding to Σ)
- hS       : proof that it is a fan law
- F        : complementary law (corresponding to Γ)
- F_empty  : initial condition (paper §3.32)
- F_mono   : monotonicity condition (paper §3.1)
-/

structure VeldmanFan (E : Enumerations) where
  S  : fin_seq → ℕ
  hS : is_fan_law S

  F : CompLaw S

  /-- (Required) initial condition for F. -/
  F_empty : F empty_seq = ∅

  /-- (Required) monotonicity of F on admitted nodes. -/
  F_mono : MonotoneOnAdmitted S F

/-
§3.32: constructing ⟨Σ, Γ⟩ from the enumeration data E (propositional version)
We simply take:
- S := Sigma E
- F := FS E
and reuse the already proved facts:
- Sigma_is_fan_law
- FS_empty
- F_mono
-/
def mkVeldmanFan (E : Enumerations) : VeldmanFan E := by
  refine
  { S := Sigma E
    hS := Sigma_is_fan_law (E := E)
    F := FS E
    F_empty := FS_empty (E := E)
    F_mono := F_mono (E := E)
  }

end VeldmanConcrete
end IPC
