import MyNewProject.Intuitionism.segment
import Mathlib
set_option maxHeartbeats 10000000
/--
We say that a sequence of segments is 'shrinking' if each segment is contained within its predecessor
-/
def shrinking (r : ℕ → 𝕊) : Prop := ∀ n, r (n + 1) ⊑ r n

/--
We say that a sequence of segments is 'dwindling' if we can make the segments arbitrarily small
-/
def dwindling (r : ℕ → 𝕊) : Prop :=
  ∀ q : ℚ, q > 0 → ∃ n : ℕ, segment.snd (r n) - segment.fst (r n) < q

/--
The definition of real sequences ℛ, representing the real numbers
(Called 'real_seq' here to not interfere with the classical real numbers,
which are already defined in Lean using Cauchy sequences)
A real sequence is a sequence of rational segments that shrinks and dwindles
-/
def real_seq := { r : ℕ → 𝕊 // shrinking r ∧ dwindling r }

notation "ℛ" => real_seq

namespace real_seq

/--
Used to extract the underlying sequence of rational segments
-/
def seq (r : ℛ) : ℕ → 𝕊 := r.val

-- We can turn a real segment into a sequence of rationals by only taking the first position
def fst (r : ℛ) : ℕ → ℚ := fun n => segment.fst (r.seq n)

-- We can turn a real segment into a sequence of rationals by only taking the second position
def snd (r : ℛ) : ℕ → ℚ := fun n => segment.snd (r.seq n)

lemma shrinking (r : ℛ) : shrinking r.val := r.property.1
lemma dwindling (r : ℛ) : dwindling r.val := r.property.2

theorem contained_of_le (r : ℛ) {n m : ℕ} (h₁ : n ≤ m) : r.seq m ⊑ r.seq n := by

  induction m generalizing n with
  | zero =>

      have hn : n = 0 := Nat.eq_zero_of_le_zero h₁
      subst hn
      simpa using segment.contained_refl (r.seq 0)
  | succ m ih =>

      have hnm : n = m + 1 ∨ n ≤ m := by

        exact Nat.eq_or_lt_of_le h₁ |> (fun h =>
          match h with
          | Or.inl heq => Or.inl heq
          | Or.inr hlt => Or.inr (Nat.le_of_lt_succ hlt))
      cases hnm with
      | inl heq =>
          subst heq
          simpa using segment.contained_refl (r.seq (m + 1))
      | inr hnle =>

          have hs : r.seq (m + 1) ⊑ r.seq m := by

            simpa [seq] using r.shrinking m
          have ih' : r.seq m ⊑ r.seq n := ih hnle
          exact segment.contained_trans (r.seq (m + 1)) (r.seq m) (r.seq n) hs ih'
/-- `<` on real sequences -/
def lt (x y : ℛ) : Prop := ∃ n : ℕ, x.seq n < y.seq n

instance : LT ℛ := ⟨lt⟩

/-- `≤` on real sequences -/
def le (x y : ℛ) : Prop := ∀ n : ℕ, x.seq n ≤ y.seq n

instance : LE ℛ := ⟨le⟩

def apart (x y : ℛ) : Prop := x < y ∨ y < x
infix:50 " # " => apart

def eq (x y : ℛ) : Prop := ∀ n : ℕ, x.seq n ≈ y.seq n
infix:50 " =' " => eq

def ne (x y : ℛ) : Prop := ¬ x =' y
infix:50 " ≠' " => ne

@[trans] theorem lt_trans (x y z : ℛ) (h₁ : x < y) (h₂ : y < z) : x < z := by
  rcases h₁ with ⟨n, hn⟩
  rcases h₂ with ⟨m, hm⟩
  refine ⟨max m n, ?_⟩
  transitivity (y.seq (max m n))
  · -- need to prove: seq x (max m n) < seq y (max m n)
    have hx := contained_of_le x (le_max_right m n)
    have hy := contained_of_le y (le_max_right m n)
    apply lt_of_le_of_lt hx.2
    apply lt_of_lt_of_le hn
    exact hy.1
  · -- need to prove: seq y (max m n) < seq z (max m n)
    have hy := contained_of_le y (le_max_left m n)
    have hz := contained_of_le z (le_max_left m n)
    apply lt_of_le_of_lt hy.2
    apply lt_of_lt_of_le hm
    exact hz.1

lemma lt_or_lt_from_sub_lt_sub {a b c d : ℚ} (h : a - b < c - d) : a < c ∨ d < b := by
  by_cases hac : a < c
  · exact Or.inl hac
  ·
    have hca : c ≤ a := le_of_not_gt hac
    have h1 : a - b < a - d := lt_of_lt_of_le h (sub_le_sub_right hca d)
    have h2 : (-b) < (-d) :=
      (add_lt_add_iff_left a).1 (by simpa [sub_eq_add_neg] using h1)
    exact Or.inr ((neg_lt_neg_iff).1 h2)

theorem lt_cotrans (x y z : ℛ) (h₁ : x < y) : x < z ∨ z < y := by
  rcases h₁ with ⟨n, hn⟩

  have hn' : segment.fst (y.seq n) - segment.snd (x.seq n) > 0 := by

    simpa [segment.lt, sub_pos] using hn
  rcases z.dwindling (segment.fst (y.seq n) - segment.snd (x.seq n)) hn' with ⟨m, hm⟩
  have hsplit := lt_or_lt_from_sub_lt_sub hm
  cases hsplit with
  | inl zlty =>
      -- case: z.snd m < y.fst n
      right
      refine ⟨max m n, ?_⟩
      have hz := contained_of_le z (le_max_left m n)
      have hy := contained_of_le y (le_max_right m n)
      apply lt_of_le_of_lt hz.2
      exact lt_of_lt_of_le zlty hy.1
  | inr xltz =>
      -- case: x.snd n < z.fst m
      left
      refine ⟨max m n, ?_⟩
      have hz := contained_of_le z (le_max_left m n)
      have hx := contained_of_le x (le_max_right m n)
      apply lt_of_le_of_lt hx.2
      exact lt_of_lt_of_le xltz hz.1

theorem apart_cotrans (x y z : ℛ) (h : x # y) : x # z ∨ z # y := by
  cases h with
  | inl hxy =>
      -- case: x < y
      cases lt_cotrans x y z hxy with
      | inl hxz =>
          left;  left; exact hxz
      | inr hzy =>
          right; left; exact hzy
  | inr hyx =>
      -- case: y < x
      cases lt_cotrans y x z hyx with
      | inl hyz =>
          right; right; exact hyz
      | inr hzx =>
          left;  right; exact hzx

theorem le_iff_not_lt (x y : ℛ) : x ≤ y ↔ ¬ y < x := by
  constructor
  · -- x ≤ y → ¬ y < x
    intro h₁ h₂
    rcases h₂ with ⟨n, hn⟩
    have hn₁ := h₁ n
    -- hn₁ : x.seq n ≤ y.seq n
    -- segment.le_iff_not_lt : a ≤ b ↔ ¬ b < a
    have : ¬ y.seq n < x.seq n := by

      have: segment.fst (x.seq n) ≤ segment.snd (y.seq n) := by
        simpa [segment.le_iff_not_lt] using hn₁
      exact (segment.le_iff_not_lt (x.seq n) (y.seq n)).mp (h₁ n)
    exact this hn
  · -- ¬ y < x → x ≤ y
    intro h n
    -- goal: x.seq n ≤ y.seq n
    -- rewrite goal to ¬ (y.seq n < x.seq n)
    rw [segment.le_iff_not_lt]
    intro hynx
    exact h ⟨n, hynx⟩

theorem eq_of_le_of_le (x y : ℛ) : x ≤ y → y ≤ x → x =' y := by
  intro hxy hyx n
  constructor
  · exact hxy n
  · exact hyx n

@[trans] theorem le_trans (x y z : ℛ) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by

  -- rw le_iff_not_lt at *
  have h₁' : ¬ y < x := (le_iff_not_lt x y).1 h₁
  have h₂' : ¬ z < y := (le_iff_not_lt y z).1 h₂

  apply (le_iff_not_lt x z).2
  intro zltx
  cases lt_cotrans z x y zltx with
  | inl zlty =>
      exact h₂' zlty
  | inr yltx =>
      exact h₁' yltx

@[refl] theorem le_refl (x : ℛ) : x ≤ x := by
  intro n
  rfl

theorem eq_iff_not_apart (x y : ℛ) : x =' y ↔ ¬ x # y := by
  constructor
  · -- x =' y → ¬ x # y
    intro h₁ h₂
    cases h₂ with
    | inl xlty =>
        rcases xlty with ⟨n, hn⟩
        have hn₁ := h₁ n
        -- hn : x.seq n < y.seq n
        -- hn₁ : x.seq n ≈ y.seq n  (touches)
        -- segment.lt_iff_not_le : a < b ↔ ¬ b ≤ a
        have : ¬ y.seq n ≤ x.seq n := by
          simpa [segment.lt_iff_not_le] using hn
        exact this hn₁.2
    | inr yltx =>
        rcases yltx with ⟨n, hn⟩
        have hn₁ := h₁ n
        have : ¬ x.seq n ≤ y.seq n := by
          simpa [segment.lt_iff_not_le] using hn
        exact this hn₁.1
  · -- ¬ x # y → x =' y
    intro h n
    -- h : ¬ (x < y ∨ y < x)
    have h' : ¬ x < y ∧ ¬ y < x := by

      simpa [apart, not_or] using h
    -- goal: x.seq n ≈ y.seq n

    rw [segment.touches]
    constructor
    ·
      rw [segment.le_iff_not_lt]
      intro hynx
      exact h'.2 ⟨n, hynx⟩
    ·
      rw [segment.le_iff_not_lt]
      intro hxny
      exact h'.1 ⟨n, hxny⟩

@[trans] theorem eq_trans (x y z : ℛ) (h₁ : x =' y) (h₂ : y =' z) : x =' z := by

  rw [eq_iff_not_apart]
  intro h₃
  cases apart_cotrans x z y h₃ with
  | inl xay =>
      have hxyn : ¬ x # y := (eq_iff_not_apart x y).1 h₁
      exact hxyn xay
  | inr yaz =>
      have hyzn : ¬ y # z := (eq_iff_not_apart y z).1 h₂
      exact hyzn yaz

@[symm] theorem eq_symm (x y : ℛ) : x =' y ↔ y =' x := by
  unfold eq
  constructor
  · intro h n
    have hn := h n

    have: segment.fst (x.seq n) ≤ segment.snd (y.seq n) ∧ segment.fst (y.seq n) ≤ segment.snd (x.seq n):= by
      simpa [segment.touches_symm] using hn
    exact id (And.symm this)
  · intro h n
    have hn := h n
    have: segment.fst (y.seq n) ≤ segment.snd (x.seq n) ∧ segment.fst (x.seq n) ≤ segment.snd (y.seq n)  := by
      simpa [segment.touches_symm] using hn
    exact id (And.symm this)

@[refl] theorem eq_refl (x : ℛ) : x =' x := by
  intro n
  rfl

theorem le_stable (x y : ℛ) : ¬¬ x ≤ y → x ≤ y := by

  intro h
  apply (le_iff_not_lt x y).2
  intro yltx
  apply h

  intro hxy
  have : ¬ y < x := (le_iff_not_lt x y).1 hxy
  exact this yltx

theorem eq_stable (x y : ℛ) : ¬¬ x =' y → x =' y := by
  intro h
  apply (eq_iff_not_apart x y).2
  intro hxy
  apply h
  intro heq
  exact (eq_iff_not_apart x y).1 heq hxy


def inclusion_const (q : ℚ) : ℛ :=
  ⟨(fun _ => segment.inclusion q), by
    constructor
    ·
      intro n
      simpa using segment.contained_refl (segment.inclusion q)
    · -- dwindling
      intro e he
      refine ⟨0, ?_⟩

      simpa [segment.inclusion, segment.fst, segment.snd] using he
  ⟩
instance : Zero ℛ := ⟨inclusion_const 0⟩

lemma zero : (0 : ℛ) = inclusion_const 0 := rfl

def add (x y : ℛ) : ℛ :=
  ⟨(fun n => segment.add (x.seq n) (y.seq n)), by
    constructor
    · -- shrinking
      intro n
      constructor
      ·
        have hx : segment.fst (x.seq n) ≤ segment.fst (x.seq (n + 1)) := (x.shrinking n).1
        have hy : segment.fst (y.seq n) ≤ segment.fst (y.seq (n + 1)) := (y.shrinking n).1
        simpa [segment.add, segment.fst] using add_le_add hx hy
      ·
        have hx : segment.snd (x.seq (n + 1)) ≤ segment.snd (x.seq n) := (x.shrinking n).2
        have hy : segment.snd (y.seq (n + 1)) ≤ segment.snd (y.seq n) := (y.shrinking n).2
        simpa [segment.add, segment.snd] using add_le_add hx hy
    · -- dwindling
      intro q hq
      have hq2 : q / 2 > 0 := by
        -- 0 < q/2
        exact div_pos hq (by norm_num)

      rcases x.dwindling (q / 2) hq2 with ⟨xn, hxn⟩
      rcases y.dwindling (q / 2) hq2 with ⟨yn, hyn⟩
      let k : ℕ := max xn yn
      refine ⟨k, ?_⟩


      have hxk : segment.snd (x.seq k) - segment.fst (x.seq k) < q / 2 := by
        have hle :
            segment.snd (x.seq k) - segment.fst (x.seq k)
              ≤
            segment.snd (x.seq xn) - segment.fst (x.seq xn) := by
          apply segment.contained_bounds_le
          exact contained_of_le x (le_max_left xn yn)
        exact lt_of_le_of_lt hle hxn


      have hyk : segment.snd (y.seq k) - segment.fst (y.seq k) < q / 2 := by
        have hle :
            segment.snd (y.seq k) - segment.fst (y.seq k)
              ≤
            segment.snd (y.seq yn) - segment.fst (y.seq yn) := by
          apply segment.contained_bounds_le
          exact contained_of_le y (le_max_right xn yn)
        exact lt_of_le_of_lt hle hyn

      have hqa : (q / 2) + (q / 2) = q := by
        simp [(add_halves q)]


      have hsum :
          (segment.snd (x.seq k) - segment.fst (x.seq k))
            +
          (segment.snd (y.seq k) - segment.fst (y.seq k)) < q := by
        have : (segment.snd (x.seq k) - segment.fst (x.seq k))
                  +
                (segment.snd (y.seq k) - segment.fst (y.seq k)) < (q / 2) + (q / 2) :=
          add_lt_add hxk hyk
        simpa [hqa] using this

      have hring :
          (segment.snd (x.seq k) - segment.fst (x.seq k))
            +
          (segment.snd (y.seq k) - segment.fst (y.seq k))
            =
          (segment.snd (x.seq k) + segment.snd (y.seq k))
            -
          (segment.fst (x.seq k) + segment.fst (y.seq k)) := by
        ring

      have hsum' :
          (segment.snd (x.seq k) + segment.snd (y.seq k))
            -
          (segment.fst (x.seq k) + segment.fst (y.seq k)) < q := by
        simpa [hring] using hsum

      simpa [k, segment.add, segment.fst, segment.snd] using hsum'
  ⟩

theorem add_assoc {x y z : ℛ} : add (add x y) z =' add x (add y z) := by
  intro n

  change segment.touches
    (segment.add (segment.add (x.seq n) (y.seq n)) (z.seq n))
    (segment.add (x.seq n) (segment.add (y.seq n) (z.seq n)))

  have hseg :
      segment.add (segment.add (x.seq n) (y.seq n)) (z.seq n)
        =
      segment.add (x.seq n) (segment.add (y.seq n) (z.seq n)) := by
    simpa using segment.add_assoc (x.seq n) (y.seq n) (z.seq n)

  unfold segment.touches
  constructor
  · -- s ≤ t
    rw [hseg]

  · -- t ≤ s
    rw [hseg]



theorem add_comm {x y : ℛ} : add x y =' add y x := by
  intro n
  change segment.touches
    (segment.add (x.seq n) (y.seq n))
    (segment.add (y.seq n) (x.seq n))

  have hseg : segment.add (x.seq n) (y.seq n) = segment.add (y.seq n) (x.seq n) := by
    simpa using segment.add_comm (x.seq n) (y.seq n)

  unfold segment.touches
  constructor
  · rw [hseg]

  · rw [hseg]



theorem add_zero {x : ℛ} : add x 0 =' x := by
  intro n

  unfold segment.touches
  constructor
  ·
    simpa [add, seq, zero, inclusion_const,
      segment.le, segment.add, segment.inclusion, segment.fst, segment.snd] using (x.seq n).2
  · -- x.seq n ≤ (add x 0).seq n
    simpa [add, seq, zero, inclusion_const,
      segment.le, segment.add, segment.inclusion, segment.fst, segment.snd] using (x.seq n).2
theorem zero_add {x : ℛ} : add 0 x =' x := by

  transitivity (add x 0)
  · exact add_comm
  · exact add_zero

theorem eq_implies_add_eq_add {x y z : ℛ} : y =' z → add x y =' add x z := by
  intro h n
  have hn := h n
  constructor
  · -- ≤
    simp [seq, add, segment.le, segment.fst, segment.snd, segment.add]
    apply add_le_add
    · exact Subtype.property (x.val n)
    · exact hn.1
  · -- ≥
    simp [seq, add, segment.le, segment.fst, segment.snd, segment.add]
    apply add_le_add
    · exact Subtype.property (x.val n)
    · exact hn.2

def neg (x : ℛ) : ℛ :=
  ⟨(fun n => segment.neg (x.val n)), by
    constructor
    · -- shrinking
      intro n
      constructor
      ·
        simp [segment.fst, segment.neg, neg_le_neg_iff]
        exact (x.property.1 n).2
      ·
        simp [segment.snd, segment.neg, neg_le_neg_iff]
        exact (x.property.1 n).1
    · -- dwindling
      intro q hq
      rcases x.property.2 q hq with ⟨xn, hxn⟩
      refine ⟨xn, ?_⟩

      have :
          segment.snd ((fun n : ℕ => segment.neg (x.val n)) xn)
            - segment.fst ((fun n : ℕ => segment.neg (x.val n)) xn)
          =
          segment.snd (x.val xn) - segment.fst (x.val xn) := by
        simp [segment.snd, segment.fst, segment.neg]
        ring
      simpa [this] using hxn
  ⟩

def sub (x y : ℛ) : ℛ := add x (neg y)

theorem sub_self_eq_zero (x : ℛ) : sub x x =' 0 := by
  intro n

  have hs :
      segment.touches
        (segment.add (x.seq n) (segment.neg (x.seq n)))
        (segment.inclusion 0) := by
    have hseg : segment.fst (x.seq n) ≤ segment.snd (x.seq n) := (x.seq n).2
    unfold segment.touches
    constructor
    · -- (s + (-s)) ≤ [0,0]
      have : segment.fst (x.seq n) + (-segment.snd (x.seq n)) ≤ 0 := by
        -- fst - snd ≤ 0  ↔  fst ≤ snd
        simpa [sub_eq_add_neg] using (sub_nonpos.mpr hseg)
      simpa [segment.le, segment.add, segment.neg, segment.inclusion,
        segment.fst, segment.snd] using this
    · -- [0,0] ≤ (s + (-s))
      have : 0 ≤ segment.snd (x.seq n) + (-segment.fst (x.seq n)) := by
        -- 0 ≤ snd - fst  ↔  fst ≤ snd
        simpa [sub_eq_add_neg] using (sub_nonneg.mpr hseg)
      simpa [segment.le, segment.add, segment.neg, segment.inclusion,
        segment.fst, segment.snd] using this


  simpa [sub, add, neg, seq, inclusion_const] using hs

theorem forall_exists_additive_inverse : ∀ x : ℛ, ∃ y : ℛ, add x y =' 0 := by
  intro x
  refine ⟨neg x, ?_⟩
  -- add x (neg x) = sub x x
  simpa [sub] using sub_self_eq_zero x

-- In traditional notation: (x + y) - y = x
theorem sub_add (x y : ℛ) : sub (add x y) y =' x := by

  transitivity (add x (add y (neg y)))
  · exact add_assoc
  transitivity (add x 0)
  · -- need: add x (sub y y) =' add x 0
    exact eq_implies_add_eq_add (sub_self_eq_zero y)
  · exact add_zero

theorem sub_add_comm {x y z : ℛ} : sub (add x y) z =' add x (sub y z) :=
  add_assoc

end real_seq
