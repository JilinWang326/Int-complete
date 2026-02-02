import Mathlib

-- Rational segments
-- Each s in 𝕊 is a pair of rational numbers (p, q) such that p ≤ q
-- Rational segments can be interpreted as intervals, [p, q], with rational end points
def segments := {s : ℚ × ℚ // s.1 ≤ s.2}


abbrev 𝕊 := segments

namespace segment

def fst (s : 𝕊) : ℚ := s.1.1

def snd (s : 𝕊) : ℚ := s.1.2

def proper (s : 𝕊) : Prop := fst s < snd s

def contained (s t : 𝕊) : Prop := fst t ≤ fst s ∧ snd s ≤ snd t


infix:50 " ⊑ " => contained

def proper_contained (s t : 𝕊) : Prop := fst t < fst s ∧ snd s < snd t

infix:50 " ⊏ " => proper_contained

def lt (s t : 𝕊) : Prop := snd s < fst t

infix:50 " < " => lt
@[simp]
def le (s t : 𝕊) : Prop := fst s ≤ snd t

infix:50 " ≤ " => le

def inclusion (q : ℚ) : 𝕊 :=
  ⟨(q, q), by rfl⟩

instance : Zero 𝕊 where
  zero := inclusion 0

def two_sided_inclusion (q : ℚ) (hq : q > 0) : 𝕊 :=
  ⟨(-q, q), by
    simp
    exact le_of_lt hq
  ⟩

lemma two_sided_inclusion_contained {q₁ q₂ : ℚ} {hq₁ : q₁ > 0} {hq₂ : q₂ > 0} (h : q₁ ≤ q₂) :
    two_sided_inclusion q₁ hq₁ ⊑ two_sided_inclusion q₂ hq₂ := by
  simp [two_sided_inclusion, contained, fst, snd, h]


@[trans] theorem contained_trans (s t v : 𝕊) (h₁ : s ⊑ t) (h₂ : t ⊑ v) : s ⊑ v := by
  constructor
  · -- need to prove: fst v ≤ fst s
    trans fst t
    exact h₂.1
    exact h₁.1
  · -- need to prove: snd s ≤ snd v
    trans snd t
    exact h₁.2
    exact h₂.2

@[trans] theorem proper_contained_trans (s t v : 𝕊) (h₁ : s ⊏ t) (h₂ : t ⊏ v) : s ⊏ v := by
  constructor
  · -- need to prove: fst v < fst s
    trans fst t
    exact h₂.1
    exact h₁.1
  · -- need to prove: snd s < snd v
    trans snd t
    exact h₁.2
    exact h₂.2

@[refl] theorem contained_refl (s : 𝕊) : s ⊑ s := by
  constructor
  · rfl -- le_refl
  · rfl

-- This lemma immediately follows from a similar statement about ℚ
lemma le_iff_not_lt (s t : 𝕊) : s ≤ t ↔ ¬ t < s := by
  constructor
  · -- need to prove: s ≤ t → ¬ t < s
    intro h
    apply not_lt_of_le
    exact h
  · -- need to prove: ¬ t < s → s ≤ t
    intro h
    apply le_of_not_lt
    exact h

lemma lt_iff_not_le (s t : 𝕊) : s < t ↔ ¬ t ≤ s := by
  constructor
  · -- need to prove: s < t → ¬ t ≤ s
    intro h
    apply not_le_of_lt
    exact h
  · -- need to prove: ¬ t ≤ s → s < t
    intro h
    apply lt_of_not_ge
    rw [ge_iff_le]
    exact h

@[trans] theorem lt_trans (s t v : 𝕊) (h₁ : s < t) (h₂ : t < v) : s < v := by
  have ht := s.2 -- s.property

  have t_prop := t.2
  rw [segment.lt]
  calc
    segment.snd s < segment.fst t := h₁
    _               ≤ segment.snd t := t_prop
    _               < segment.fst v := h₂

@[refl] theorem le_refl (s : 𝕊) : s ≤ s := by
  exact s.2 -- subtype.property

/--
We say that two rational segments 'touch' if they partially cover eachother
-/
@[simp]
def touches (s t : 𝕊) : Prop := s ≤ t ∧ t ≤ s

infix:50 " ≈ " => touches

@[refl] theorem touches_refl (s : 𝕊) : s ≈ s := by
  constructor
  · exact le_refl s
  · exact le_refl s

@[symm] theorem touches_symm (s t : 𝕊) : s ≈ t ↔ t ≈ s := by
  exact And.comm

def add (s t : 𝕊) : 𝕊 :=
  ⟨(fst s + fst t, snd s + snd t), by
    apply add_le_add
    exact s.2
    exact t.2
  ⟩


lemma mk_eq_mk_iff (a b : ℚ × ℚ) (ha hb) : (⟨a, ha⟩ : 𝕊) = ⟨b, hb⟩ ↔ a = b := Subtype.mk_eq_mk

theorem add_assoc (s t v : 𝕊) : add (add s t) v = add s (add t v) := by
  apply Subtype.eq
  simp only [add]
  simp only [Prod.mk.injEq]
  constructor
  ·
    calc
      fst (add (add s t) v)
          = fst (add s t) + fst v := rfl
      _ = (fst s + fst t) + fst v := rfl
      _ = fst s + (fst t + fst v) := by rw [Rat.add_assoc]
      _ = fst s + fst (add t v) := rfl
      _ = fst (add s (add t v)) := rfl
  ·
    calc
      snd (add (add s t) v)
          = snd (add s t) + snd v := rfl
      _ = (snd s + snd t) + snd v := rfl
      _ = snd s + (snd t + snd v) := by rw [Rat.add_assoc]
      _ = snd s + snd (add t v) := rfl

lemma fst_add_comm {s t : 𝕊} : fst (add s t) = fst s + fst t := rfl

lemma snd_add_comm {s t : 𝕊} : snd (add s t) = snd s + snd t := rfl

theorem add_comm (s t : 𝕊) : add s t = add t s := by
  apply Subtype.eq
  simp only [add]
  simp only [Prod.mk.injEq]
  constructor
  ·
    calc
      fst (add s t)
          = fst s + fst t := rfl
      _   = fst t + fst s := by rw [Rat.add_comm]
      _   = fst (add t s) := rfl
  ·
    calc
      snd (add s t)
          = snd s + snd t := rfl
      _   = snd t + snd s := by rw [Rat.add_comm]
      _   = snd (add t s) := rfl

-- We use this lemma in proving that addition on ℛ is well-defined
lemma contained_bounds_le (s t : 𝕊) (h : s ⊑ t) : segment.snd s - segment.fst s ≤ segment.snd t - segment.fst t := by
  apply sub_le_sub
  exact h.2 -- h.elim_right
  exact h.1 -- h.elim_left

instance : AddCommSemigroup 𝕊 where
  add := segment.add
  add_assoc := segment.add_assoc
  add_comm := segment.add_comm

def neg (s : 𝕊) : 𝕊 :=
  ⟨(-segment.snd s, -segment.fst s), by
    dsimp
    apply neg_le_neg
    exact s.2
  ⟩

end segment
