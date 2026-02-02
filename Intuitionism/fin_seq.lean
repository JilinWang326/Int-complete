import Mathlib
import MyNewProject.Intuitionism.nat_seq

open NatSeq

/-
This file defines finite sequences from {0, ..., n} to ℕ
-/

@[ext] structure fin_seq where
  len : ℕ
  seq : Fin len → ℕ

namespace fin_seq

/-- Take the first `n` values of an infinite natural sequence as a `fin_seq`. -/
def finitize (a : 𝒩) (n : ℕ) : fin_seq :=
  ⟨n, fun i => a i.val⟩

lemma finitize_len (a : 𝒩) (n : ℕ) : (finitize a n).len = n := rfl

/-- `a ⊑ b` means `a` is an initial segment of the infinite sequence `b`. -/
def is_initial_of (a : fin_seq) (b : 𝒩) : Prop :=
  ∀ i : Fin a.len, a.seq i = b i

infix:50 " ⊑ " => is_initial_of

lemma is_initial_of_self (a : 𝒩) {n : ℕ} : (finitize a n) ⊑ a := by
  intro i
  rfl

/-- Shorten a finite sequence to length `m ≤ a.len`. -/
def shorten (a : fin_seq) (m : ℕ) (h : m ≤ a.len) : fin_seq :=
  ⟨m, fun i => a.seq (Fin.castLE h i)⟩

/--
Concatenate two finite sequences.
Indices `< a.len` read from `a`, otherwise read from `b` with shifted index.
-/
def extend (a b : fin_seq) : fin_seq :=
  ⟨a.len + b.len, fun i =>
    if h : i.val < a.len then
      a.seq ⟨i.val, h⟩
    else
      b.seq ⟨i.val - a.len, by
        -- show: i.val - a.len < b.len
        have ha : a.len ≤ i.val := Nat.le_of_not_lt h
        rcases Nat.exists_eq_add_of_le ha with ⟨t, ht⟩
        have hi : a.len + t < a.len + b.len := by
          -- i.isLt : i.val < a.len + b.len
          simpa [ht] using i.isLt
        have htlt : t < b.len := Nat.lt_of_add_lt_add_left hi
        have hsub : i.val - a.len = t := by
          -- (a.len + t) - a.len = t
          simp [ht]
        -- i.val - a.len < b.len
        simpa [hsub] using htlt
      ⟩⟩

/-- Extend a finite prefix `a` with an infinite tail `b`. -/
def extend_inf (a : fin_seq) (b : 𝒩) : 𝒩 :=
  fun i =>
    if h : i < a.len then
      a.seq ⟨i, h⟩
    else
      b (i - a.len)

lemma extend_inf_eq {a : fin_seq} {b₁ b₂ : 𝒩} (h : b₁ =' b₂) :
    extend_inf a b₁ =' extend_inf a b₂ := by
  intro n
  by_cases hn : n < a.len
  · simp [extend_inf, hn]
  · simp [extend_inf, hn, h (n - a.len)]

/--
If two finite sequences have the same length and agree pointwise (after casting),
then extending both with the same tail gives equal infinite sequences.
-/
lemma eq_extend_inf {a₁ a₂ : fin_seq} {b : 𝒩} (h₁ : a₁.len = a₂.len)
    (h₂ : ∀ i : Fin a₁.len, a₁.seq i = a₂.seq (Fin.cast h₁ i)) :
    extend_inf a₁ b =' extend_inf a₂ b := by
  intro n
  by_cases g₁ : n < a₁.len
  · have g₂ : n < a₂.len := by simpa [h₁] using g₁
    -- both sides take the prefix branch
    simp [extend_inf, g₁, g₂]
    -- goal: a₁.seq ⟨n,g₁⟩ = a₂.seq ⟨n,g₂⟩
    have hn := h₂ ⟨n, g₁⟩
    have hcast : (Fin.cast h₁ ⟨n, g₁⟩ : Fin a₂.len) = ⟨n, g₂⟩ := by
      apply Fin.ext
      rfl
    simpa [hcast] using hn
  · have g₂ : ¬ n < a₂.len := by
      intro g2
      apply g₁
      -- rewrite `g2` using h₁ back to a₁.len
      have : n < a₁.len := by simpa [h₁] using g2
      exact this
    -- both sides take tail branch; lengths equal so n - len equal
    simp [extend_inf, g₁, g₂, h₁]

/-- The empty finite sequence. -/
def empty_seq : fin_seq :=
  ⟨0, fun _ => 0⟩

/--
Trivial lemma: any statement about an element of `Fin 0` is provable (because `Fin 0` is empty).
This is the Lean4-friendly replacement of the Lean3 proof-by-contradiction.
-/
lemma empty_seq_eq {a : fin_seq} (ha : a.len = 0) :
    ∀ i : Fin empty_seq.len,
      empty_seq.seq i = a.seq (Fin.cast (by simp [empty_seq, ha]) i) := by
  intro i
  -- i : Fin 0
  exact Fin.elim0 i

lemma empty_extend_eq_self (a : 𝒩) : extend_inf empty_seq a =' a := by
  intro i
  -- empty_seq.len = 0, so the if-branch is impossible
  simp [extend_inf, empty_seq]

/-- A singleton finite sequence. -/
def singleton (n : ℕ) : fin_seq :=
  ⟨1, fun _ => n⟩

theorem finitize_initial_iff_start_eq (a b : 𝒩) (n : ℕ) :
    finitize a n ⊑ b ↔ (∀ j : ℕ, j < n → a j = b j) := by
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h i
    exact h i.val i.isLt

theorem finitize_eq_iff_start_eq (a b : 𝒩) (n : ℕ) :
    finitize a n = finitize b n ↔ (∀ j : ℕ, j < n → a j = b j) := by
  constructor
  · intro h j hj
    have hmk :
        fin_seq.mk n (fun i : Fin n => a i.val)
          =
        fin_seq.mk n (fun i : Fin n => b i.val) := by
      simpa [finitize] using h

    have hinj :
        (n = n ∧ HEq (fun i : Fin n => a i.val) (fun i : Fin n => b i.val)) := by
      exact (Eq.mp
        (fin_seq.mk.injEq n (fun i : Fin n => a i.val) n (fun i : Fin n => b i.val))
        hmk)
    have hfun :
        (fun i : Fin n => a i.val) = (fun i : Fin n => b i.val) :=
      eq_of_heq hinj.2
    have hj' := congrFun hfun ⟨j, hj⟩
    simpa using hj'


  · intro hstart
    have hfun : (fun i : Fin n => a i.val) = (fun i : Fin n => b i.val) := by
      funext i
      exact hstart i.val i.isLt
    have hmk : fin_seq.mk n (fun i : Fin n => a i.val) = fin_seq.mk n (fun i : Fin n => b i.val) :=
      congrArg (fun f => fin_seq.mk n f) hfun
    simpa [finitize] using hmk



lemma finitize_initial_iff_finitize_eq (a b : 𝒩) (n : ℕ) :
    finitize a n ⊑ b ↔ finitize a n = finitize b n := by
  -- both sides are equivalent to “a and b agree on indices < n”
  rw [finitize_initial_iff_start_eq, finitize_eq_iff_start_eq]

/--
The tail of the finite sequence `a`.
If `a` is empty, then `a.len - 1 = 0` and the domain is empty, so it is still well-defined.
-/
def tail (a : fin_seq) : fin_seq :=
  ⟨a.len - 1, fun i => a.seq (Fin.castLE (Nat.sub_le a.len 1) i)⟩

lemma tail_singleton_len_zero : ∀ n : ℕ, (tail (singleton n)).len = 0 := by
  intro n
  rfl

end fin_seq


/-- Finite sequences with a fixed length. -/
def len_seq (n : ℕ) : Type := Fin n → ℕ

namespace len_seq

def to_fin_seq {n : ℕ} : len_seq n → fin_seq :=
  fun f => ⟨n, f⟩

lemma fin_len_eq {n : ℕ} {a : len_seq n} : (to_fin_seq a).seq = a := rfl

lemma len_fin_eq (a : fin_seq) : (to_fin_seq (n := a.len) a.seq) = a := by
  cases a
  rfl

lemma len_seq_0_unique (x y : len_seq 0) : x = y := by
  funext a
  exact Fin.elim0 a

end len_seq
