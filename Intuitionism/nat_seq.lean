/-
This file defines natural sequences, here defined as functions ℕ → ℕ
Also defined here are the comparisons =, ≠, <, ≤ and #
-/

import Mathlib

def NatSeq := ℕ → ℕ

notation "𝒩" => NatSeq

namespace NatSeq

def zero : 𝒩 := fun _ => 0

def seq_eq (a b : 𝒩) : Prop := ∀ n : ℕ, a n = b n

infix:50 " =' " => seq_eq

theorem eq_iff {a b : 𝒩} : a = b ↔ a =' b := funext_iff

def seq_ne (a b : 𝒩) : Prop := ¬ a =' b

infix:50 " ≠' " => seq_ne

def seq_lt (a b : 𝒩) : Prop := ∃ n : ℕ, (∀ i : ℕ, i < n → a i = b i) ∧ a n < b n

instance : LT 𝒩 where
  lt := seq_lt

def seq_le (a b : 𝒩) : Prop := ∀ n : ℕ, (∀ i : ℕ, i < n → a i = b i) → a n ≤ b n

instance : LE 𝒩 where
  le := seq_le

theorem le_of_eq' (a b : 𝒩) (h : a =' b) : a ≤ b := by
  intro n _
  rw [h]

theorem imp_eq_iff_imp_eq (a b : 𝒩) (n : ℕ) :
    (∀ i : ℕ, i < n → a i = b i) ↔ (∀ i : ℕ, i < n → b i = a i) := by
  constructor <;> (intro h i hi; exact (h i hi).symm)

theorem imp_eq_trans (a b c : 𝒩) (n : ℕ)
    (h₁ : ∀ i : ℕ, i < n → a i = b i)
    (h₂ : ∀ i : ℕ, i < n → b i = c i) :
    ∀ i : ℕ, i < n → a i = c i := by
  intro i hi
  rw [h₁ i hi]
  exact h₂ i hi

@[trans] theorem seq_eq_trans (a b c : 𝒩) : a =' b → b =' c → a =' c := by
  intro ab bc n
  rw [ab n]
  exact bc n

@[symm] theorem seq_eq_symm {a b : 𝒩} : a =' b ↔ b =' a := by
  constructor <;> (intro h n; exact (h n).symm)

@[refl] theorem seq_eq_refl {a : 𝒩} : a =' a := fun _ => rfl

@[symm] theorem seq_ne_symm (a b : 𝒩) : a ≠' b ↔ b ≠' a := by
  simp only [seq_ne, seq_eq_symm]

theorem lt_eq_lt_le (a b : 𝒩) (n m : ℕ)
    (h1 : ∀ i : ℕ, i < n → a i = b i) (h2 : a m < b m) :
    n ≤ m := by
  rcases le_or_lt n m with nlem | ngtm
  · exact nlem
  · exfalso
    have aibi := h1 m ngtm
    rw [eq_iff_le_not_lt] at aibi
    exact aibi.2 h2

theorem lt_eq_ne_le (a b : 𝒩) (n m : ℕ)
    (h1 : ∀ i : ℕ, i < n → a i = b i) (h2 : a m ≠ b m) :
    n ≤ m := by
  rcases h2.lt_or_lt with hlt | hgt
  · exact lt_eq_lt_le a b n m h1 hlt
  · rw [imp_eq_iff_imp_eq] at h1
    exact lt_eq_lt_le b a n m h1 hgt

-- The following lemma immediately follows from lt_eq_ne_le and n = m ↔ (n ≤ m ∨ m ≤ n)
-- We will use this in reckless.lean to prove weak_LEM_implies_LLPO
theorem first_zero_eq (a : 𝒩) (n m : ℕ) (hn1 : ∀ i : ℕ, i < n → a i = 0) (hn2 : a n ≠ 0)
    (hm1 : ∀ i : ℕ, i < m → a i = 0) (hm2 : a m ≠ 0) :
    n = m := by
  rw [eq_iff_le_not_lt]
  constructor
  · exact lt_eq_ne_le a zero n m hn1 hm2
  · exact Nat.not_lt.mpr (lt_eq_ne_le a zero m n hm1 hn2)

theorem le_of_lt' (a b : 𝒩) (less : a < b) : a ≤ b := by
  show seq_le a b
  intro n h
  obtain ⟨d, p, q⟩ := less
  have hnd := lt_eq_lt_le a b n d h q
  rcases hnd.eq_or_lt with ndeq | ndlt
  · rw [← ndeq] at q
    exact Nat.le_of_lt q
  · exact Nat.le_of_eq (p n ndlt)

@[trans] theorem seq_lt_trans (a b c : 𝒩) : a < b → b < c → a < c := by
  intro hab hbc
  obtain ⟨n, p₁, p₂⟩ := hab
  obtain ⟨m, q₁, q₂⟩ := hbc
  use min n m
  constructor
  · intro i hi
    rw [lt_min_iff] at hi
    rw [p₁ i hi.1]
    exact q₁ i hi.2
  · rcases Nat.lt_trichotomy n m with nltm | neqm | mltn
    · rw [min_eq_left (Nat.le_of_lt nltm)]
      rw [← q₁ n nltm]
      exact p₂
    · rw [neqm, min_self]
      rw[neqm] at p₂
      exact Nat.lt_trans p₂ q₂
    · rw [min_eq_right (Nat.le_of_lt mltn)]
      rw [p₁ m mltn]
      exact q₂

-- Doing a finite amount of comparisons is allowed
theorem all_eq_or_exists_neq (a b : 𝒩) (n : ℕ) :
    (∀ i : ℕ, i < n → a i = b i) ∨
    (∃ i : ℕ, i < n ∧ (∀ j : ℕ, j < i → a j = b j) ∧ a i ≠ b i) := by
  induction n with
  | zero =>
    left
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  | succ d hd =>
    rcases hd with all_eq | exists_neq
    · rcases lt_trichotomy (a d) (b d) with adltbd | adeqbd | adgtbd
      · right
        exact ⟨d, Nat.lt_succ_self d, all_eq, adltbd.ne⟩
      · left
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with iltd | ieqd
        · exact all_eq i iltd
        · rw [ieqd]; exact adeqbd
      · right
        exact ⟨d, Nat.lt_succ_self d, all_eq, adgtbd.ne'⟩
    · right
      obtain ⟨i, iltd, ajbj, ainebi⟩ := exists_neq
      exact ⟨i, Nat.lt_succ_of_lt iltd, ajbj, ainebi⟩

theorem nat_lt_cotrans (a b : ℕ) (h : a < b) : ∀ c : ℕ, a < c ∨ c < b := by
  intro c
  induction c with
  | zero =>
    right
    exact Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le a) h))
  | succ d hd =>
    rcases hd with ad | db
    · left
      exact Nat.lt_trans ad (Nat.lt_succ_self d)
    ·
      rcases (Nat.succ_le_of_lt db).eq_or_lt with sd_eq_b | sd_lt_b
      ·
        left
        have : d + 1 = b := sd_eq_b
        rw [← this] at h

        exact h
      ·
        right
        exact sd_lt_b
theorem seq_lt_cotrans (a b : 𝒩) (h : a < b) : ∀ c : 𝒩, a < c ∨ c < b := by
  intro c
  obtain ⟨n, hnl, hnr⟩ := h
  rcases all_eq_or_exists_neq a c n with all_eq | exists_neq
  · rcases nat_lt_cotrans (a n) (b n) hnr (c n) with ancn | cnbn
    · left
      exact ⟨n, all_eq, ancn⟩
    · right
      use n
      constructor
      · rw [imp_eq_iff_imp_eq a c n] at all_eq
        exact imp_eq_trans c a b n all_eq hnl
      · exact cnbn
  · obtain ⟨i, hil, him, hir⟩ := exists_neq
    rcases hir.lt_or_lt with ailtci | aigtci
    · left
      exact ⟨i, him, ailtci⟩
    · right
      use i
      constructor
      · intro j hj
        rw [← him j hj]
        exact hnl j (Nat.lt_trans hj hil)
      · rw [hnl i hil] at aigtci
        exact aigtci

theorem le_iff_not_lt' (a b : 𝒩) : a ≤ b ↔ ¬ b < a := by
  constructor
  · intro h ex
    obtain ⟨n, ind, blta⟩ := ex
    have g' := h n
    rw [imp_eq_iff_imp_eq b a n] at ind
    have aleb := g' ind
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le blta aleb)
  · intro h n hi
    rcases le_or_lt (a n) (b n) with hle | hgt
    · exact hle
    · exfalso
      apply h
      use n
      constructor
      · rw [imp_eq_iff_imp_eq b a n]
        exact hi
      · exact hgt

-- The following theorem now easily follows from le_iff_not_lt and lt_cotrans
theorem le_trans' (a b c : 𝒩) : a ≤ b → b ≤ c → a ≤ c := by
  intro h₁ h₂
  rw [le_iff_not_lt'] at *
  intro h₃
  rcases seq_lt_cotrans c a h₃ b with cb | ba
  · exact h₂ cb
  · exact h₁ ba

theorem le_stable (a b : 𝒩) : ¬¬a ≤ b → a ≤ b := by
  rw [le_iff_not_lt']
  exact fun hnn hba => hnn fun h => h hba

theorem eq_of_le_le {a b : 𝒩} (hab : a ≤ b) (hba : b ≤ a) : a =' b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ d hd =>
    have hle : a d ≤ b d := hab d hd
    have hge : b d ≤ a d := by
      apply hba
      intro i hi
      exact (hd i hi).symm
    exact Nat.le_antisymm hle hge
@[simp]
def apart (a b : 𝒩) : Prop := ∃ n, a n ≠ b n

infix:50 " # " => apart

-- If two natural sequences are apart from each other, they are not equal
theorem ne_of_apart (a b : 𝒩) : a # b → a ≠' b := by
  intro r h
  obtain ⟨n, hn⟩ := r
  exact hn (h n)

theorem eq_iff_not_apart (a b : 𝒩) : a =' b ↔ ¬ a # b := by
  constructor
  · intro h g
    obtain ⟨n, hn⟩ := g
    exact hn (h n)
  · intro h n
    rw [apart, not_exists] at h
    have g := h n
    push_neg at g
    exact g

theorem eq_stable (a b : 𝒩) : ¬¬ a =' b → a =' b := by
  rw [eq_iff_not_apart]
  exact fun hnn hab => hnn fun h => h hab

theorem apart_iff_lt_or_lt (a b : 𝒩) : a # b ↔ a < b ∨ b < a := by
  constructor
  · intro ab
    obtain ⟨n, hn⟩ := ab
    rcases all_eq_or_exists_neq a b n with all_eq | exists_neq
    · rcases hn.lt_or_lt with ab' | ba
      · left
        exact ⟨n, all_eq, ab'⟩
      · right
        use n
        constructor
        · rw [imp_eq_iff_imp_eq b a n]
          exact all_eq
        · exact ba
    · obtain ⟨i, _, ajbj, aineqbi⟩ := exists_neq
      rcases aineqbi.lt_or_lt with aibi | biai
      · left
        exact ⟨i, ajbj, aibi⟩
      · right
        use i
        constructor
        · rw [imp_eq_iff_imp_eq b a i]
          exact ajbj
        · exact biai
  · intro aborba
    rcases aborba with ⟨n, _, hn⟩ | ⟨n, _, hn⟩
    · exact ⟨n, hn.ne⟩
    · exact ⟨n, hn.ne'⟩

theorem apart_cotrans (a b : 𝒩) (h : a # b) : ∀ c : 𝒩, a # c ∨ c # b := by
  intro c
  rw [apart_iff_lt_or_lt] at h
  rcases h with ab | ba
  · -- ab : a < b
    rcases seq_lt_cotrans a b ab c with ac | cb
    · 
      left
      rw [apart_iff_lt_or_lt]
      left
      exact ac
    ·
      right
      rw [apart_iff_lt_or_lt]
      left
      exact cb
  ·
    rcases seq_lt_cotrans b a ba c with bc | ca
    ·
      right
      rw [apart_iff_lt_or_lt]
      right
      exact bc
    ·
      left
      rw [apart_iff_lt_or_lt]
      right
      exact ca

@[symm] theorem apart_symm (a b : 𝒩) : a # b ↔ b # a := by
  constructor <;> (intro ⟨n, hn⟩; exact ⟨n, hn.symm⟩)

-- 0 is the smallest sequence
theorem zero_le' (a : 𝒩) : zero ≤ a := by
  intro n _
  simp only [zero, Nat.zero_le]

theorem apart_zero_lt (a : 𝒩) (h : a # zero) : zero < a := by
  rw [apart_iff_lt_or_lt] at h
  rcases h with alt | agt
  · exfalso
    have h₁ := zero_le' a
    rw [le_iff_not_lt'] at h₁
    exact h₁ alt
  · exact agt

/-
There are uncountably (defined positively) many natural sequences.
The proof of this theorem is Cantor's Diagonal argument
-/
theorem uncountable (f : ℕ → 𝒩) : ∃ a : 𝒩, ∀ n : ℕ, a # (f n) := by
  use fun n => (f n n) + 1
  intro n
  use n
  exact Nat.succ_ne_self (f n n)

end NatSeq
