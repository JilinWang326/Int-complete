import Intuitionism.EmptyCompleteness
import Mathlib.Data.Nat.BitIndices

/-!
# A closed constructive enumeration instance for the concrete Veldman construction

This file closes the `Enumerations` parameter from the main development by giving:

* an explicit enumeration of formulas;
* an explicit enumeration of derivation codes obtained from raw Hilbert proof trees.

Unlike the previous countability-based construction, this version is fully constructive:
it does not use `Classical.choice`, and the derivation enumeration is computed directly
from encoded proof trees.
-/

open IPC
open scoped IPC

namespace DefaultEnumerations

/-! ## Formula enumeration -/

/-- Syntactic rank of a propositional formula. -/
def formRank : Form → ℕ
  | Form.atom _ => 0
  | Form.bot => 0
  | Form.imp A B => Nat.succ (Nat.max (formRank A) (formRank B))
  | Form.and A B => Nat.succ (Nat.max (formRank A) (formRank B))
  | Form.or  A B => Nat.succ (Nat.max (formRank A) (formRank B))



/-- A simple numeric code for formulas. It is only used to prove surjectivity of `formEnum`. -/
def formCode : Form → ℕ
  | Form.atom n => IPC.pairEncodeBin 0 n
  | Form.bot => IPC.pairEncodeBin 1 0
  | Form.imp A B => IPC.pairEncodeBin 2 (IPC.pairEncodeBin (formCode A) (formCode B))
  | Form.and A B => IPC.pairEncodeBin 3 (IPC.pairEncodeBin (formCode A) (formCode B))
  | Form.or  A B => IPC.pairEncodeBin 4 (IPC.pairEncodeBin (formCode A) (formCode B))



/-- Decode a formula from a bounded syntactic rank and a numeric payload. -/
def formAt : ℕ → ℕ → Form
  | 0, c =>
      let p := IPC.pairDecodeBin c
      match p.1 with
      | 0 => Form.atom p.2
      | 1 => Form.bot
      | _ => Form.bot
  | d + 1, c =>
      let p := IPC.pairDecodeBin c
      match p.1 with
      | 0 => Form.atom p.2
      | 1 => Form.bot
      | 2 =>
          let q := IPC.pairDecodeBin p.2
          Form.imp (formAt d q.1) (formAt d q.2)
      | 3 =>
          let q := IPC.pairDecodeBin p.2
          Form.and (formAt d q.1) (formAt d q.2)
      | 4 =>
          let q := IPC.pairDecodeBin p.2
          Form.or (formAt d q.1) (formAt d q.2)
      | _ => Form.bot



lemma formAt_code_of_rank_le (A : Form) :
    ∀ d : ℕ, formRank A ≤ d → formAt d (formCode A) = A := by
  induction A with
  | atom n =>
      intro d hd
      cases d <;> simp [formAt, formCode]
  | bot =>
      intro d hd
      cases d <;> simp [formAt, formCode]
  | imp A B ihA ihB =>
      intro d hd
      rcases Nat.exists_eq_add_of_le hd with ⟨k, rfl⟩
      have hA : formRank A ≤ Nat.max (formRank A) (formRank B) + k := by
        exact le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)
      have hB : formRank B ≤ Nat.max (formRank A) (formRank B) + k := by
        exact le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)
      simp [formRank, Nat.succ_add, formAt, formCode, ihA _ hA, ihB _ hB]
  | and A B ihA ihB =>
      intro d hd
      rcases Nat.exists_eq_add_of_le hd with ⟨k, rfl⟩
      have hA : formRank A ≤ Nat.max (formRank A) (formRank B) + k := by
        exact le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)
      have hB : formRank B ≤ Nat.max (formRank A) (formRank B) + k := by
        exact le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)
      simp [formRank, Nat.succ_add, formAt, formCode, ihA _ hA, ihB _ hB]
  | or A B ihA ihB =>
      intro d hd
      rcases Nat.exists_eq_add_of_le hd with ⟨k, rfl⟩
      have hA : formRank A ≤ Nat.max (formRank A) (formRank B) + k := by
        exact le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)
      have hB : formRank B ≤ Nat.max (formRank A) (formRank B) + k := by
        exact le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)
      simp [formRank, Nat.succ_add, formAt, formCode, ihA _ hA, ihB _ hB]



/-- The actual enumeration of formulas. -/
def formEnum (n : ℕ) : Form :=
  let p := IPC.pairDecodeBin n
  formAt p.1 p.2

/-- A right-inverse code for `formEnum`. -/
def formEnumCode (A : Form) : ℕ :=
  IPC.pairEncodeBin (formRank A) (formCode A)

@[simp] lemma formEnum_code (A : Form) : formEnum (formEnumCode A) = A := by
  simpa [formEnum, formEnumCode] using
    formAt_code_of_rank_le A (formRank A) le_rfl



lemma formEnum_surjective : Function.Surjective formEnum := by
  intro A
  exact ⟨formEnumCode A, formEnum_code A⟩



/-! ## Finite-context enumeration -/

/-- A constructive right-inverse code for `formEnum`. -/
def formCodeEmbedding : Form ↪ ℕ where
  toFun := formEnumCode
  inj' := by
    intro A B h
    have := congrArg formEnum h
    simpa [formEnum_code] using this

/-- Decode a list of natural numbers from a prescribed length and payload. -/
def natListAt : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, c =>
      let p := IPC.pairDecodeBin c
      p.1 :: natListAt k p.2

/-- Encode a list of natural numbers. -/
def natListCode : List ℕ → ℕ
  | [] => 0
  | n :: ns => IPC.pairEncodeBin n (natListCode ns)

@[simp] lemma natListAt_code (xs : List ℕ) :
    natListAt xs.length (natListCode xs) = xs := by
  induction xs with
  | nil =>
      simp [natListAt, natListCode]
  | cons x xs ih =>
      simp [natListAt, natListCode, ih]

/-- A constructive `List → Finset` conversion by repeated insertion. -/
def listToFinset {α : Type*} [DecidableEq α] : List α → Finset α
  | [] => ∅
  | a :: l => insert a (listToFinset l)

@[simp] lemma mem_listToFinset {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    a ∈ listToFinset l ↔ a ∈ l := by
  induction l with
  | nil =>
      simp [listToFinset]
  | cons b l ih =>
      simp [listToFinset, ih]

/-- Enumerate finite contexts by decoding a list of formula codes and inserting them into a finset. -/
def ctxEnum (n : ℕ) : Finset Form :=
  let p := IPC.pairDecodeBin n
  listToFinset ((natListAt p.1 p.2).map formEnum)

/-- Encode a finite context by sorting its formula codes and then using the list code. -/
def ctxCode (Γ : Finset Form) : ℕ :=
  let codes := (Γ.map formCodeEmbedding).sort (· ≤ ·)
  IPC.pairEncodeBin codes.length (natListCode codes)

lemma ctxEnum_code (Γ : Finset Form) : ctxEnum (ctxCode Γ) = Γ := by
  unfold ctxEnum ctxCode
  simp only [IPC.pairDecodeBin_encode, natListAt_code]
  ext A
  constructor
  · intro hA
    rw [mem_listToFinset] at hA
    rcases List.mem_map.mp hA with ⟨n, hn, hnA⟩
    have hn' : n ∈ Γ.map formCodeEmbedding := (Finset.mem_sort _).mp hn
    rcases Finset.mem_map.mp hn' with ⟨B, hB, hcode⟩
    have hdecode : formEnum n = B := by
      have := congrArg formEnum hcode
      simpa [formCodeEmbedding, formEnum_code] using this.symm
    have : A = B := by
      calc
        A = formEnum n := by simp [hnA]
        _ = B := hdecode
    simpa [this] using hB
  · intro hA
    rw [mem_listToFinset, List.mem_map]
    refine ⟨formEnumCode A, ?_, formEnum_code A⟩
    exact (Finset.mem_sort _).2 (Finset.mem_map.mpr ⟨A, hA, rfl⟩)



lemma ctxCode_injective : Function.Injective ctxCode := by
  intro Γ Δ h
  have := congrArg ctxEnum h
  simp [ctxEnum_code] at this
  exact this



lemma ctxEnum_surjective : Function.Surjective ctxEnum := by
  intro Γ
  exact ⟨ctxCode Γ, ctxEnum_code Γ⟩

/-! ## Derivation enumeration -/

/-- A fixed valid derivation code used as the default output of the proof checker. -/
def defaultDerCode : DerCode := (∅, Form.imp Form.bot Form.bot)

lemma defaultDerCode_sound : DerOK defaultDerCode := by
  unfold defaultDerCode DerOK
  exact IPC.prf.id

/-- Raw Hilbert proof trees over finite contexts. -/
inductive RawProof : Type
  | ax   : Finset Form → Form → RawProof
  | k    : Finset Form → Form → Form → RawProof
  | s    : Finset Form → Form → Form → Form → RawProof
  | exf  : Finset Form → Form → RawProof
  | mp   : RawProof → RawProof → RawProof
  | pr1  : Finset Form → Form → Form → RawProof
  | pr2  : Finset Form → Form → Form → RawProof
  | pair : Finset Form → Form → Form → RawProof
  | inr  : Finset Form → Form → Form → RawProof
  | inl  : Finset Form → Form → Form → RawProof
  | case : Finset Form → Form → Form → Form → RawProof

/-- Tree height for raw proofs. -/
def rawProofRank : RawProof → ℕ
  | RawProof.mp t u => Nat.succ (Nat.max (rawProofRank t) (rawProofRank u))
  | _ => 0

/-- Payload encoding for constructors that store one context and one formula. -/
def codeCtxForm (Γ : Finset Form) (A : Form) : ℕ :=
  IPC.pairEncodeBin (ctxCode Γ) (formEnumCode A)

/-- Payload encoding for constructors that store one context and two formulas. -/
def codeCtxTwoForms (Γ : Finset Form) (A B : Form) : ℕ :=
  IPC.pairEncodeBin (ctxCode Γ) (IPC.pairEncodeBin (formEnumCode A) (formEnumCode B))

/-- Payload encoding for constructors that store one context and three formulas. -/
def codeCtxThreeForms (Γ : Finset Form) (A B C : Form) : ℕ :=
  IPC.pairEncodeBin (ctxCode Γ)
    (IPC.pairEncodeBin (formEnumCode A)
      (IPC.pairEncodeBin (formEnumCode B) (formEnumCode C)))

/-- Decode one context and one formula from a numeric payload. -/
def decodeCtxForm (c : ℕ) : Finset Form × Form :=
  let p := IPC.pairDecodeBin c
  (ctxEnum p.1, formEnum p.2)

/-- Decode one context and two formulas from a numeric payload. -/
def decodeCtxTwoForms (c : ℕ) : Finset Form × (Form × Form) :=
  let p := IPC.pairDecodeBin c
  let q := IPC.pairDecodeBin p.2
  (ctxEnum p.1, (formEnum q.1, formEnum q.2))

/-- Decode one context and three formulas from a numeric payload. -/
def decodeCtxThreeForms (c : ℕ) : Finset Form × (Form × (Form × Form)) :=
  let p := IPC.pairDecodeBin c
  let q := IPC.pairDecodeBin p.2
  let r := IPC.pairDecodeBin q.2
  (ctxEnum p.1, (formEnum q.1, (formEnum r.1, formEnum r.2)))

/-- Encode raw proof trees numerically. -/
def rawProofCode : RawProof → ℕ
  | RawProof.ax Γ A => IPC.pairEncodeBin 0 (codeCtxForm Γ A)
  | RawProof.k Γ A B => IPC.pairEncodeBin 1 (codeCtxTwoForms Γ A B)
  | RawProof.s Γ A B C => IPC.pairEncodeBin 2 (codeCtxThreeForms Γ A B C)
  | RawProof.exf Γ A => IPC.pairEncodeBin 3 (codeCtxForm Γ A)
  | RawProof.mp t u => IPC.pairEncodeBin 4 (IPC.pairEncodeBin (rawProofCode t) (rawProofCode u))
  | RawProof.pr1 Γ A B => IPC.pairEncodeBin 5 (codeCtxTwoForms Γ A B)
  | RawProof.pr2 Γ A B => IPC.pairEncodeBin 6 (codeCtxTwoForms Γ A B)
  | RawProof.pair Γ A B => IPC.pairEncodeBin 7 (codeCtxTwoForms Γ A B)
  | RawProof.inr Γ A B => IPC.pairEncodeBin 8 (codeCtxTwoForms Γ A B)
  | RawProof.inl Γ A B => IPC.pairEncodeBin 9 (codeCtxTwoForms Γ A B)
  | RawProof.case Γ A B C => IPC.pairEncodeBin 10 (codeCtxThreeForms Γ A B C)

/-- Decode leaf proof constructors from a numeric payload. -/
def rawProofLeafAt (c : ℕ) : RawProof :=
  let p := IPC.pairDecodeBin c
  match p.1 with
  | 0 =>
      let q := decodeCtxForm p.2
      RawProof.ax q.1 q.2
  | 1 =>
      let q := decodeCtxTwoForms p.2
      RawProof.k q.1 q.2.1 q.2.2
  | 2 =>
      let q := decodeCtxThreeForms p.2
      RawProof.s q.1 q.2.1 q.2.2.1 q.2.2.2
  | 3 =>
      let q := decodeCtxForm p.2
      RawProof.exf q.1 q.2
  | 5 =>
      let q := decodeCtxTwoForms p.2
      RawProof.pr1 q.1 q.2.1 q.2.2
  | 6 =>
      let q := decodeCtxTwoForms p.2
      RawProof.pr2 q.1 q.2.1 q.2.2
  | 7 =>
      let q := decodeCtxTwoForms p.2
      RawProof.pair q.1 q.2.1 q.2.2
  | 8 =>
      let q := decodeCtxTwoForms p.2
      RawProof.inr q.1 q.2.1 q.2.2
  | 9 =>
      let q := decodeCtxTwoForms p.2
      RawProof.inl q.1 q.2.1 q.2.2
  | 10 =>
      let q := decodeCtxThreeForms p.2
      RawProof.case q.1 q.2.1 q.2.2.1 q.2.2.2
  | _ =>
      RawProof.k ∅ Form.bot Form.bot

/-- Decode raw proofs from a bounded tree height and a numeric payload. -/
def rawProofAt : ℕ → ℕ → RawProof
  | 0, c => rawProofLeafAt c
  | d + 1, c =>
      let p := IPC.pairDecodeBin c
      match p.1 with
      | 4 =>
          let q := IPC.pairDecodeBin p.2
          RawProof.mp (rawProofAt d q.1) (rawProofAt d q.2)
      | _ => rawProofLeafAt c

lemma rawProofAt_code_of_rank_le (t : RawProof) :
    ∀ d : ℕ, rawProofRank t ≤ d → rawProofAt d (rawProofCode t) = t := by
  induction t with
  | ax Γ A =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxForm, decodeCtxForm,
          ctxEnum_code, formEnum_code]
  | k Γ A B =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxTwoForms, decodeCtxTwoForms,
          ctxEnum_code, formEnum_code]
  | s Γ A B C =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxThreeForms, decodeCtxThreeForms,
          ctxEnum_code, formEnum_code]
  | exf Γ A =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxForm, decodeCtxForm,
          ctxEnum_code, formEnum_code]
  | mp t u iht ihu =>
      intro d hd
      rcases Nat.exists_eq_add_of_le hd with ⟨k, rfl⟩
      have ht : rawProofRank t ≤ Nat.max (rawProofRank t) (rawProofRank u) + k := by
        exact le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)
      have hu : rawProofRank u ≤ Nat.max (rawProofRank t) (rawProofRank u) + k := by
        exact le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)
      simp [rawProofRank, rawProofAt, rawProofCode, Nat.succ_add, iht _ ht, ihu _ hu]
  | pr1 Γ A B =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxTwoForms, decodeCtxTwoForms,
          ctxEnum_code, formEnum_code]
  | pr2 Γ A B =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxTwoForms, decodeCtxTwoForms,
          ctxEnum_code, formEnum_code]
  | pair Γ A B =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxTwoForms, decodeCtxTwoForms,
          ctxEnum_code, formEnum_code]
  | inr Γ A B =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxTwoForms, decodeCtxTwoForms,
          ctxEnum_code, formEnum_code]
  | inl Γ A B =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxTwoForms, decodeCtxTwoForms,
          ctxEnum_code, formEnum_code]
  | case Γ A B C =>
      intro d hd
      cases d <;>
        simp [rawProofAt, rawProofLeafAt, rawProofCode, codeCtxThreeForms, decodeCtxThreeForms,
          ctxEnum_code, formEnum_code]

/-- The explicit enumeration of raw proof trees. -/
def rawProofEnum (n : ℕ) : RawProof :=
  let p := IPC.pairDecodeBin n
  rawProofAt p.1 p.2

/-- A right-inverse code for `rawProofEnum`. -/
def rawProofEnumCode (t : RawProof) : ℕ :=
  IPC.pairEncodeBin (rawProofRank t) (rawProofCode t)

@[simp] lemma rawProofEnum_code (t : RawProof) : rawProofEnum (rawProofEnumCode t) = t := by
  simpa [rawProofEnum, rawProofEnumCode] using
    rawProofAt_code_of_rank_le t (rawProofRank t) le_rfl

/-- Apply modus ponens at the level of derivation codes, falling back to `defaultDerCode` if the
payloads do not line up. -/
def applyMP (d₁ d₂ : DerCode) : DerCode :=
  match d₁.2 with
  | Form.imp A B =>
      if _hΓ : ctxCode d₁.1 = ctxCode d₂.1 then
        if _hA : d₂.2 = A then
          (d₁.1, B)
        else
          defaultDerCode
      else
        defaultDerCode
  | _ => defaultDerCode

lemma applyMP_sound {d₁ d₂ : DerCode} (hd₁ : DerOK d₁) (hd₂ : DerOK d₂) :
    DerOK (applyMP d₁ d₂) := by
  cases d₁ with
  | mk Γ₁ F =>
      cases d₂ with
      | mk Γ₂ A₂ =>
          cases hF : F with
          | atom n =>
              simpa [applyMP, hF] using defaultDerCode_sound
          | bot =>
              simpa [applyMP, hF] using defaultDerCode_sound
          | imp A B =>
              by_cases hΓcode : ctxCode Γ₁ = ctxCode Γ₂
              · have hΓ : Γ₁ = Γ₂ := ctxCode_injective hΓcode
                by_cases hA : A₂ = A
                · have hd1' : ((↑Γ₁ : Set Form) ⊢ᵢ Form.imp A B) := by
                    simpa [DerOK, hF] using hd₁
                  have hd2' : ((↑Γ₁ : Set Form) ⊢ᵢ A) := by
                    simpa [DerOK, hΓ, hA] using hd₂
                  simpa [applyMP, hF, hΓcode, hA, DerOK] using IPC.prf.mp hd1' hd2'
                · simpa [applyMP, hF, hΓcode, hA] using defaultDerCode_sound
              · simpa [applyMP, hF, hΓcode] using defaultDerCode_sound
          | and A B =>
              simpa [applyMP, hF] using defaultDerCode_sound
          | or A B =>
              simpa [applyMP, hF] using defaultDerCode_sound

/-- Interpret raw proof trees as derivation codes, sending malformed trees to `defaultDerCode`. -/
def rawProofDer : RawProof → DerCode
  | RawProof.ax Γ A =>
      if _ : A ∈ Γ then
        (Γ, A)
      else
        defaultDerCode
  | RawProof.k Γ A B =>
      (Γ, Form.imp A (Form.imp B A))
  | RawProof.s Γ A B C =>
      (Γ, Form.imp (Form.imp A (Form.imp B C))
        (Form.imp (Form.imp A B) (Form.imp A C)))
  | RawProof.exf Γ A =>
      (Γ, Form.imp Form.bot A)
  | RawProof.mp t u =>
      applyMP (rawProofDer t) (rawProofDer u)
  | RawProof.pr1 Γ A B =>
      (Γ, Form.imp (Form.and A B) A)
  | RawProof.pr2 Γ A B =>
      (Γ, Form.imp (Form.and A B) B)
  | RawProof.pair Γ A B =>
      (Γ, Form.imp A (Form.imp B (Form.and A B)))
  | RawProof.inr Γ A B =>
      (Γ, Form.imp A (Form.or A B))
  | RawProof.inl Γ A B =>
      (Γ, Form.imp B (Form.or A B))
  | RawProof.case Γ A B C =>
      (Γ, Form.imp (Form.imp A C)
        (Form.imp (Form.imp B C) (Form.imp (Form.or A B) C)))

lemma rawProofDer_sound (t : RawProof) : DerOK (rawProofDer t) := by
  induction t with
  | ax Γ A =>
      by_cases hA : A ∈ Γ
      · simpa [rawProofDer, hA, DerOK] using (IPC.prf.ax hA)
      · simpa [rawProofDer, hA] using defaultDerCode_sound
  | k Γ A B =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.k (Γ := (↑Γ : Set Form)) (p := A) (q := B))
  | s Γ A B C =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.s (Γ := (↑Γ : Set Form)) (p := A) (q := B) (r := C))
  | exf Γ A =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.exf (Γ := (↑Γ : Set Form)) (p := A))
  | mp t u iht ihu =>
      exact applyMP_sound iht ihu
  | pr1 Γ A B =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.pr1 (Γ := (↑Γ : Set Form)) (p := A) (q := B))
  | pr2 Γ A B =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.pr2 (Γ := (↑Γ : Set Form)) (p := A) (q := B))
  | pair Γ A B =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.pair (Γ := (↑Γ : Set Form)) (p := A) (q := B))
  | inr Γ A B =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.inr (Γ := (↑Γ : Set Form)) (p := A) (q := B))
  | inl Γ A B =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.inl (Γ := (↑Γ : Set Form)) (p := A) (q := B))
  | case Γ A B C =>
      simpa [rawProofDer, DerOK] using
        (IPC.prf.case (Γ := (↑Γ : Set Form)) (p := A) (q := B) (r := C))

lemma rawProof_complete (Γ : Finset Form) :
    ∀ {A : Form}, ((↑Γ : Set Form) ⊢ᵢ A) → ∃ t : RawProof, rawProofDer t = (Γ, A)
  | p, IPC.prf.ax hmem =>
      let hA : _ := by simpa using hmem
      ⟨RawProof.ax Γ p, by simp [rawProofDer, hA]⟩
  | _, IPC.prf.k =>
      ⟨RawProof.k Γ _ _, rfl⟩
  | _, IPC.prf.s =>
      ⟨RawProof.s Γ _ _ _, rfl⟩
  | _, IPC.prf.exf =>
      ⟨RawProof.exf Γ _, rfl⟩
  | _, IPC.prf.mp hpq hp =>
      by
        rcases rawProof_complete Γ hpq with ⟨tpq, htpq⟩
        rcases rawProof_complete Γ hp with ⟨tp, htp⟩
        refine ⟨RawProof.mp tpq tp, ?_⟩
        simp [rawProofDer, applyMP, htpq, htp]
  | _, IPC.prf.pr1 =>
      ⟨RawProof.pr1 Γ _ _, rfl⟩
  | _, IPC.prf.pr2 =>
      ⟨RawProof.pr2 Γ _ _, rfl⟩
  | _, IPC.prf.pair =>
      ⟨RawProof.pair Γ _ _, rfl⟩
  | _, IPC.prf.inr =>
      ⟨RawProof.inr Γ _ _, rfl⟩
  | _, IPC.prf.inl =>
      ⟨RawProof.inl Γ _ _, rfl⟩
  | _, IPC.prf.case =>
      ⟨RawProof.case Γ _ _ _, rfl⟩

/-- Veldman's enumeration `d₀, d₁, ...` of derivations, as derivation codes. -/
def derivEnum (n : ℕ) : DerCode :=
  rawProofDer (rawProofEnum n)

lemma derivEnum_sound (n : ℕ) : DerOK (derivEnum n) := by
  exact rawProofDer_sound (rawProofEnum n)

lemma derivEnum_complete
    (Γ : Finset Form) (A : Form)
    (h : ((↑Γ : Set Form) ⊢ᵢ A)) :
    ∃ i : ℕ, derivEnum i = (Γ, A) := by
  rcases rawProof_complete Γ h with ⟨t, ht⟩
  refine ⟨rawProofEnumCode t, ?_⟩
  simp [derivEnum, ht]

/-- The closed enumeration package required by `VeldmanConcrete` and `completeness.lean`. -/
def defaultEnumerations : Enumerations where
  W := formEnum
  d := derivEnum
  W_surj := formEnum_surjective
  d_sound := derivEnum_sound
  d_complete := derivEnum_complete

end DefaultEnumerations

namespace ConcreteCompleteness

/-- Empty-context semantic completeness with the enumeration parameter closed. -/
theorem semantic_completeness_concrete_closed
    (hBar : BarInductionStd) (A : Form) :
    (∀ {X : Type} (M : emodel X), Valid M A) → ((∅ : Set Form) ⊢ᵢ A) := by
  exact semantic_completeness_concrete
    hBar DefaultEnumerations.defaultEnumerations A



end ConcreteCompleteness
