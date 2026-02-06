import Mathlib.Algebra.Order.Field.Basic        -- one_div_le_one_div
import Mathlib.Algebra.Order.Archimedean.Basic  -- exists_nat_one_div_lt
import Intuitionism.RickKoenders.NatSeq
import Intuitionism.RickKoenders.Real

namespace reckless

open NatSeq
open real_seq

/--
The principle of omniscience, also called the law of the excluded middle
-/
def PO : Prop := ∀ Q : Prop, Q ∨ ¬ Q

/--
Limited principle of omniscience
-/
def LPO : Prop := ∀ a : 𝒩, (∀ n : ℕ, a n = 0) ∨ (∃ n : ℕ, a n ≠ 0)

def reckless_LPO (P : Prop) : Prop := (PO → P) ∧ (P → LPO)

/--
Lesser limited principle of omniscience
-/
def LLPO : Prop :=
  ∀ a : 𝒩,
    (∀ k : ℕ, ((∀ i : ℕ, i < k → a i = 0) ∧ a k ≠ 0) → k % 2 = 0) ∨
    (∀ k : ℕ, ((∀ i : ℕ, i < k → a i = 0) ∧ a k ≠ 0) → k % 2 = 1)

def reckless_LLPO (P : Prop) : Prop :=
  (PO → P) ∧ (P → LLPO)

/-!
### Basic facts: PO ⇒ LPO ⇒ LLPO
-/

theorem PO_implies_LPO : PO → LPO := by
  intro po a
  have h := po (∃ n : ℕ, a n ≠ 0)
  cases h with
  | inl hex =>
      right
      exact hex
  | inr hnex =>
      left
      -- hnex : ¬ ∃ n, a n ≠ 0
      -- turn into ∀ n, a n = 0
      have hforall : ∀ n : ℕ, ¬ a n ≠ 0 := by
        exact forall_not_of_not_exists hnex
      intro n
      -- from ¬(a n ≠ 0) and decidable equality on ℕ, get a n = 0
      by_cases h0 : a n = 0
      · exact h0
      · -- h0 : a n ≠ 0 contradicts hforall n
        exact False.elim (hforall n h0)

-- A simple lemma to show a reckless statement exists: PO itself is reckless
lemma exists_reckless : ∃ P : Prop, reckless_LPO P := by
  refine ⟨PO, ?_⟩
  constructor
  · intro h
    exact h
  · exact PO_implies_LPO

/--
A helper: for any proposition P, ¬¬(P ∨ ¬P).
(Constructive proof, no classical needed.)
-/
theorem not_not_em (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  intro h
  apply h
  right
  intro p
  apply h
  left
  exact p

theorem LPO_implies_LLPO : LPO → LLPO := by
  intro lpo a
  rcases lpo a with faeq | eneq
  · -- case: ∀ n, a n = 0 (vacuous)
    left
    intro k hk
    exfalso

    exact hk.2 (faeq k)
  ·
    rcases eneq with ⟨n, hn⟩

    rcases NatSeq.all_eq_or_exists_neq a NatSeq.zero n with alleq | exneq
    ·
      have hnpar : n % 2 = 0 ∨ n % 2 = 1 := by
        -- Mathlib usually has this lemma; if not, replace with your own proof.
        simpa using Nat.mod_two_eq_zero_or_one n
      cases hnpar with
      | inl neven =>
          left
          intro k hk

          have hkn : k ≤ n :=
            NatSeq.lt_eq_ne_le a NatSeq.zero k n hk.1 hn
          have hnk : n ≤ k :=
            NatSeq.lt_eq_ne_le a NatSeq.zero n k alleq hk.2
          have keqn : k = n := Nat.le_antisymm hkn hnk
          simpa [keqn] using neven
      | inr nodd =>
          right
          intro k hk
          have hkn : k ≤ n :=
            NatSeq.lt_eq_ne_le a NatSeq.zero k n hk.1 hn
          have hnk : n ≤ k :=
            NatSeq.lt_eq_ne_le a NatSeq.zero n k alleq hk.2
          have keqn : k = n := Nat.le_antisymm hkn hnk
          simpa [keqn] using nodd
    ·
      rcases exneq with ⟨i, hiltn, hi⟩

      have hipar : i % 2 = 0 ∨ i % 2 = 1 := by
        simpa using Nat.mod_two_eq_zero_or_one i
      cases hipar with
      | inl ieven =>
          left
          intro k hk
          have hki : k ≤ i :=
            NatSeq.lt_eq_ne_le a NatSeq.zero k i hk.1 hi.2
          have hik : i ≤ k :=
            NatSeq.lt_eq_ne_le a NatSeq.zero i k hi.1 hk.2
          have keqi : k = i := Nat.le_antisymm hki hik
          simpa [keqi] using ieven
      | inr iodd =>
          right
          intro k hk
          have hki : k ≤ i :=
            NatSeq.lt_eq_ne_le a NatSeq.zero k i hk.1 hi.2
          have hik : i ≤ k :=
            NatSeq.lt_eq_ne_le a NatSeq.zero i k hi.1 hk.2
          have keqi : k = i := Nat.le_antisymm hki hik
          simpa [keqi] using iodd

/-!
### Recklessness examples
-/

/--
Double negation cannot be eliminated for all propositions P (reckless wrt LPO)
-/
theorem reckless_not_not_implies : reckless_LPO (∀ P : Prop, ¬¬ P → P) := by
  constructor
  · -- PO → ∀ P, ¬¬P → P
    intro po P nnp
    have hpornp := po P
    cases hpornp with
    | inl hp => exact hp
    | inr hnp =>
        exfalso
        exact nnp hnp
  · -- (∀ P, ¬¬P → P) → LPO (in fact implies PO, hence LPO)
    intro h
    apply PO_implies_LPO
    intro P

    have hn : ¬¬ (P ∨ ¬ P) := by
      intro hcontra
      apply hcontra
      right
      intro p
      apply hcontra
      left
      exact p
    exact h (P ∨ ¬ P) hn

theorem reckless_implies_not_or :
    reckless_LPO (∀ P Q : Prop, (P → Q) → (Q ∨ ¬ P)) := by
  constructor
  · intro po P Q hPQ
    cases po P with
    | inl hp =>
        left
        exact hPQ hp
    | inr hnp =>
        right
        exact hnp
  · intro h
    apply PO_implies_LPO
    intro Q
    -- use h with P=Q, Q=Q and identity
    have := h Q Q (fun q => q)
    exact this

/--
The statement "a ≤ b → (a < b ∨ a =' b)" implies LPO, hence is reckless.
-/
theorem reckless_LPO_le_implies_lt_or_eq :
    reckless_LPO (∀ a b : 𝒩, a ≤ b → a < b ∨ a =' b) := by
  constructor
  · -- PO → ...
    intro po a b hab
    cases po (a < b) with
    | inl hablt =>
        left
        exact hablt
    | inr hnlt =>
        right
        -- from ¬ a < b, get b ≤ a, then equality by ≤≤
        have hba : b ≤ a := by
          -- NatSeq.le_iff_not_lt' : b ≤ a ↔ ¬ a < b
          exact (NatSeq.le_iff_not_lt' b a).2 hnlt
        exact NatSeq.eq_of_le_le hab hba
  · -- (∀ a b, a ≤ b → a < b ∨ a =' b) → LPO
    intro h a
    -- apply h to zero ≤ a
    have hz : NatSeq.zero ≤ a := NatSeq.zero_le' a
    cases h NatSeq.zero a hz with
    | inl zlt =>
        -- 0 < a → ∃ n, a n ≠ 0
        right

        have : a # NatSeq.zero := by
          -- apart_iff_lt_or_lt : a # b ↔ a < b ∨ b < a
          -- Here we know zero < a, so use (NatSeq.zero # a) then symmetry
          have : NatSeq.zero # a := by
            -- (zero < a) gives (zero # a)
            have : NatSeq.zero < a ∨ a < NatSeq.zero := Or.inl zlt
            exact (NatSeq.apart_iff_lt_or_lt NatSeq.zero a).2 this
          -- symmetry
          exact (apart_symm NatSeq.zero a).mp this
        -- apart gives ∃ n, a n ≠ 0
        rcases this with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        -- hn : a n ≠ zero n = 0
        simpa [NatSeq.zero] using hn
    | inr zeq =>
        -- 0 =' a
        left
        intro n
        have := zeq n
        -- zeq n : zero n = a n
        simpa [NatSeq.zero] using this.symm

/-- The two following theorems look funny together -/
theorem implies_not_implies_not : ∀ P Q : Prop, (P ∨ ¬ P → ¬ Q) → ¬ Q := by
  intro P Q h hq
  -- hq : Q
  -- want False
  have h' : ¬ (P ∨ ¬ P) := by
    intro hp
    exact h hp hq
  -- but ¬¬(P ∨ ¬P) holds constructively
  exact not_not_em P h'

theorem reckless_LPO_implies_implies :
    reckless_LPO (∀ P Q : Prop, (P ∨ ¬ P → Q) → Q) := by
  constructor
  · intro po P Q hpq
    exact hpq (po P)
  · intro h
    apply PO_implies_LPO
    intro P
    -- choose Q := P ∨ ¬P
    have hp := h P (P ∨ ¬ P)
    apply hp
    intro pop
    exact pop

/-!
### Decidability instances (finite search)
-/

instance start_le_not_zero_decidable (a : 𝒩) (n : ℕ) :
    Decidable (∃ i : ℕ, i ≤ n ∧ a i ≠ 0) := by
  -- finite search by recursion on n
  induction n with
  | zero =>
    refine decidable_of_iff (a 0 ≠ 0) ?_
    constructor
    · -- (a 0 ≠ 0) → (∃ i ≤ 0, a i ≠ 0)
      intro h0
      exact ⟨0, le_rfl, h0⟩
    · -- (∃ i ≤ 0, a i ≠ 0) → (a 0 ≠ 0)
      intro h
      rcases h with ⟨i, hi, hai⟩
      have : i = 0 := Nat.eq_zero_of_le_zero hi
      simpa [this] using hai
  | succ d ih =>
      classical
      -- simp handles decidability of bounded exists
      simpa using (inferInstance : Decidable (∃ i : ℕ, i ≤ Nat.succ d ∧ a i ≠ 0))

instance start_lt_not_zero_decidable (a : 𝒩) (n : ℕ) :
    Decidable (∃ i : ℕ, i < n ∧ a i ≠ 0) := by
  induction n with
  | zero =>
      refine isFalse ?_
      intro h
      rcases h with ⟨i, hi, _⟩
      exact (Nat.not_lt_zero i) hi
  | succ d ih =>
      -- (∃ i < d+1, ...) ↔ (∃ i < d, ...) ∨ (a d ≠ 0)
      refine decidable_of_iff ((∃ i : ℕ, i < d ∧ a i ≠ 0) ∨ (a d ≠ 0)) ?_
      ·

        exact Iff.symm Nat.exists_lt_succ_right


/--
snap : 𝒩 → ℛ
-/
def snap (a : 𝒩) : ℛ :=
  ⟨(fun n : ℕ =>
      if h : (∃ i : ℕ, i ≤ n ∧ a i ≠ 0) then
        segment.inclusion ((1 : ℚ) / (Nat.succ (Nat.find h)))
      else
        segment.two_sided_inclusion ((1 : ℚ) / (Nat.succ n))
          (by
            -- 0 < 1/(n+1)
            have hnpos : (0 : ℚ) < (Nat.succ n : ℚ) := by
              exact_mod_cast Nat.succ_pos n
            simpa using (one_div_pos.mpr hnpos)
          )
    ), by
      constructor
      · -- shrinking
        intro n
        classical

        by_cases h1 : (∃ i : ℕ, i ≤ n + 1 ∧ a i ≠ 0)
        · by_cases h2 : (∃ i : ℕ, i ≤ n ∧ a i ≠ 0)
          ·
            have hs1 := Nat.find_spec h1
            have hs2 := Nat.find_spec h2

            have hh : Nat.find h1 = Nat.find h2 := by

              rcases lt_trichotomy (Nat.find h1) (Nat.find h2) with hlt | heq | hgt
              · exfalso
                -- Nat.find_min' : m < find h2 -> ¬(m≤n ∧ a m≠0)
                have hmin : ¬ (Nat.find h1 ≤ n ∧ a (Nat.find h1) ≠ 0) :=
                  Nat.find_min h2 hlt
                have : Nat.find h1 ≤ n ∧ a (Nat.find h1) ≠ 0 := by
                  constructor
                  · have : Nat.find h1 ≤ Nat.find h2 := Nat.le_of_lt hlt
                    exact Nat.le_trans this hs2.1
                  · exact hs1.2
                exact hmin this
              · exact heq
              · exfalso
                have hmin : ¬ (Nat.find h2 ≤ n + 1 ∧ a (Nat.find h2) ≠ 0) :=
                  Nat.find_min h1 hgt
                have : Nat.find h2 ≤ n + 1 ∧ a (Nat.find h2) ≠ 0 := by
                  constructor
                  · exact Nat.le_trans hs2.1 (Nat.le_succ n)
                  · exact hs2.2
                exact hmin this
            simp [h1, h2]
            rw [hh]

          · -- h1 true, h2 false : inclusion ⊑ two_sided_inclusion
            have hs1 := Nat.find_spec h1
            simp [h1, h2, seq]

            dsimp [segment.contained, segment.inclusion, segment.two_sided_inclusion,
              segment.fst, segment.snd]
            constructor
            · -- -q ≤ p
              have hqpos : (0 : ℚ) < (1 : ℚ) / (Nat.succ n) := by
                have hnpos : (0 : ℚ) < (Nat.succ n : ℚ) := by
                  exact_mod_cast Nat.succ_pos n
                simpa using (one_div_pos.mpr hnpos)
              have hppos : (0 : ℚ) ≤ (1 : ℚ) / (Nat.succ (Nat.find h1)) := by
                have hp' : (0 : ℚ) < (1 : ℚ) / (Nat.succ (Nat.find h1)) := by
                  have hpos : (0 : ℚ) < (Nat.succ (Nat.find h1) : ℚ) := by
                    exact_mod_cast Nat.succ_pos (Nat.find h1)
                  simpa using (one_div_pos.mpr hpos)
                exact le_of_lt hp'
              have hneg : -((1 : ℚ) / (Nat.succ n)) ≤ 0 := by
                exact neg_nonpos.mpr (le_of_lt hqpos)
              have hnpos' : (0 : ℚ) < (↑n + 1) := by
                have : (0 : ℚ) < (Nat.succ n : ℚ) := by
                  exact_mod_cast Nat.succ_pos n
                simpa [Nat.cast_succ] using this

              have hfpos' : (0 : ℚ) < (↑(Nat.find h1) + 1) := by
                have : (0 : ℚ) < (Nat.succ (Nat.find h1) : ℚ) := by
                  exact_mod_cast Nat.succ_pos (Nat.find h1)
                simpa [Nat.cast_succ] using this

              have hneg' : -((↑n + 1 : ℚ)⁻¹) ≤ 0 := by
                exact neg_nonpos.mpr (le_of_lt (inv_pos.2 hnpos'))

              have hppos' : (0 : ℚ) ≤ (↑(Nat.find h1) + 1 : ℚ)⁻¹ := by
                exact le_of_lt (inv_pos.2 hfpos')

              have hchain :
                  -((↑n + 1 : ℚ)⁻¹) ≤ (↑(Nat.find h1) + 1 : ℚ)⁻¹ :=
                le_trans hneg' hppos'
              simpa [one_div, Nat.cast_succ] using hchain
            ·
              have hle : Nat.find h1 ≤ n + 1 := hs1.1
              rcases lt_or_eq_of_le hle with hlt | heq
              · -- find < n+1 -> find ≤ n -> contradict h2
                have hfindle : Nat.find h1 ≤ n := by
                  exact Nat.lt_succ_iff.mp hlt
                exfalso
                apply h2
                refine ⟨Nat.find h1, hfindle, hs1.2⟩
              · -- find = n+1
                 -- find = n+1
                simp[heq]

                have ha : (0 : ℚ) < (Nat.succ (n + 1) : ℚ) := by
                  exact_mod_cast Nat.succ_pos (n + 1)
                have hb : (0 : ℚ) < (Nat.succ n : ℚ) := by
                  exact_mod_cast Nat.succ_pos n
                have hden : (Nat.succ n : ℚ) ≤ (Nat.succ (n + 1) : ℚ) := by
                  -- n+1 ≤ n+2
                  exact_mod_cast (Nat.le_succ (Nat.succ n))
                have hq :
                    (1 : ℚ) / (Nat.succ (n + 1) : ℚ) ≤ (1 : ℚ) / (Nat.succ n : ℚ) :=
                  (one_div_le_one_div ha hb).2 hden


                simpa [one_div, Nat.cast_succ, add_assoc] using hq
        · -- h1 false
          by_cases h2 : (∃ i : ℕ, i ≤ n ∧ a i ≠ 0)
          ·
            exfalso
            apply h1
            rcases h2 with ⟨i, hi, hai⟩
            refine ⟨i, ?_, hai⟩
            exact Nat.le_trans hi (Nat.le_succ n)
          · -- h1 false, h2 false : two_sided_inclusion_contained
            simp [h1, h2, seq]
            apply segment.two_sided_inclusion_contained
            have ha : (0 : ℚ) < (Nat.succ (n + 1) : ℚ) := by
              exact_mod_cast Nat.succ_pos (n + 1)
            have hb : (0 : ℚ) < (Nat.succ n : ℚ) := by
              exact_mod_cast Nat.succ_pos n
            have hden : (Nat.succ n : ℚ) ≤ (Nat.succ (n + 1) : ℚ) := by
              exact_mod_cast (Nat.le_succ (Nat.succ n))
            have hq :
                (1 : ℚ) / (Nat.succ (n + 1) : ℚ) ≤ (1 : ℚ) / (Nat.succ n : ℚ) :=
              (one_div_le_one_div ha hb).2 hden
            simpa [one_div, Nat.cast_succ, add_assoc] using hq
      · -- dwindling
        intro q hq
        classical
        -- 取 q/2
        have hq2 : (0 : ℚ) < q / 2 := by
          exact div_pos hq (by norm_num)
        rcases exists_nat_one_div_lt hq2 with ⟨n, hn⟩
        refine ⟨n, ?_⟩

        by_cases h : (∃ i : ℕ, i ≤ n ∧ a i ≠ 0)
        ·
          simp [h, segment.inclusion, segment.fst, segment.snd]
          exact hq
        · -- two_sided_inclusion: width = r - (-r) = r+r < q
          have rdef : (segment.snd (segment.two_sided_inclusion ((1 : ℚ) / (Nat.succ n))
              (by
                have hnpos : (0 : ℚ) < (Nat.succ n : ℚ) := by
                  exact_mod_cast Nat.succ_pos n
                simpa using (one_div_pos.mpr hnpos)))
            -
            segment.fst (segment.two_sided_inclusion ((1 : ℚ) / (Nat.succ n))
              (by
                have hnpos : (0 : ℚ) < (Nat.succ n : ℚ) := by
                  exact_mod_cast Nat.succ_pos n
                simpa using (one_div_pos.mpr hnpos))))
            =
            ((1 : ℚ) / (Nat.succ n)) + ((1 : ℚ) / (Nat.succ n)) := by
              simp [segment.two_sided_inclusion, segment.fst, segment.snd, sub_eq_add_neg]

          have hsum : ((1 : ℚ) / (Nat.succ n)) + ((1 : ℚ) / (Nat.succ n)) < q := by
            have : ((1 : ℚ) / (Nat.succ n)) + ((1 : ℚ) / (Nat.succ n)) < (q / 2) + (q / 2) :=by
              have hn' : (1 : ℚ) / (Nat.succ n : ℚ) < q / 2 := by
                -- ↑(Nat.succ n) = ↑n + 1
                simpa [Nat.cast_succ] using hn
              exact add_lt_add hn' hn'
            simpa [add_halves q] using this

          simp [ h, segment.two_sided_inclusion, segment.fst, segment.snd, sub_eq_add_neg] at *

          simpa [rdef] using hsum
  ⟩


theorem reckless_LPO_real_lt_eq_gt :
    reckless_LPO (∀ x y : ℛ, x < y ∨ real_seq.eq x y ∨ y < x) := by
  constructor
  · -- PO → trichotomy
    intro po x y
    cases po (x < y) with
    | inl xlt =>
        exact Or.inl xlt
    | inr nxlt =>

        cases po (y < x) with
        | inl ylt =>
            exact Or.inr (Or.inr ylt)
        | inr nylt =>

            have hxy : x ≤ y := (real_seq.le_iff_not_lt x y).2 nylt
            have hyx : y ≤ x := (real_seq.le_iff_not_lt y x).2 nxlt
            have heq : real_seq.eq x y := real_seq.eq_of_le_of_le x y hxy hyx
            exact Or.inr (Or.inl heq)
  ·  -- trichotomy → LPO
    intro h a
    have hsnap := h (snap a) (real_seq.inclusion_const 0)
    cases hsnap with
    | inl hlt =>

        exfalso
        rcases hlt with ⟨n, hn⟩
        -- hn : (snap a).seq n < (inclusion 0).seq n
        -- segment.lt: snd left < fst right
        have hn' : segment.snd ((snap a).seq n) < 0 := by
          -- fst (inclusion 0) = 0
          simpa [real_seq.seq, real_seq.inclusion_const, segment.lt, segment.inclusion,
            segment.fst, segment.snd] using hn

        by_cases h0 : (∃ i : ℕ, i ≤ n ∧ a i ≠ 0)
        ·
          have hpos : (0 : ℚ) < (1 : ℚ) / (Nat.succ (Nat.find h0) : ℚ) := by
            have : (0 : ℚ) < (Nat.succ (Nat.find h0) : ℚ) := by
              exact_mod_cast Nat.succ_pos (Nat.find h0)
            simpa using (one_div_pos.mpr this)
          have hsnd_nonneg : (0 : ℚ) ≤ segment.snd ((snap a).seq n) := by

            simp [snap, real_seq.seq, h0, segment.inclusion, segment.snd, segment.fst]

            have : (0 : ℚ) ≤ (↑(Nat.find h0) + 1 : ℚ) := by
              exact add_nonneg (Nat.cast_nonneg _) (by norm_num)
            simpa [one_div, Nat.cast_succ] using (inv_nonneg.2 this)
          exact (not_lt_of_ge hsnd_nonneg) hn'
        ·
          have hpos : (0 : ℚ) < (1 : ℚ) / (Nat.succ n : ℚ) := by
            have : (0 : ℚ) < (Nat.succ n : ℚ) := by
              exact_mod_cast Nat.succ_pos n
            simpa using (one_div_pos.mpr this)
          have hsnd_nonneg : (0 : ℚ) ≤ segment.snd ((snap a).seq n) := by
            simp [snap, real_seq.seq, h0, segment.two_sided_inclusion, segment.snd, segment.fst]
            have : (0 : ℚ) ≤ (↑n + 1 : ℚ) := by
              exact add_nonneg (Nat.cast_nonneg _) (by norm_num)

            simpa [one_div, Nat.cast_succ] using (inv_nonneg.2 this)
          exact (not_lt_of_ge hsnd_nonneg) hn'

    | inr hge =>
        cases hge with
        | inl heq =>

            left
            intro n
            have hn := heq n
            -- hn : (snap a).seq n ≈ (inclusion 0).seq n
            -- touches = ≤ ∧ ≥
            have hn1 : (snap a).seq n ≤ (real_seq.inclusion_const 0).seq n := hn.1

            by_cases h0 : (∃ i : ℕ, i ≤ n ∧ a i ≠ 0)
            ·
              have hpos : (0 : ℚ) < (1 : ℚ) / (Nat.succ (Nat.find h0) : ℚ) := by
                have : (0 : ℚ) < (Nat.succ (Nat.find h0) : ℚ) := by
                  exact_mod_cast Nat.succ_pos (Nat.find h0)
                simpa using (one_div_pos.mpr this)
              have hle : (1 : ℚ) / (Nat.succ (Nat.find h0) : ℚ) ≤ 0 := by
                -- segment.le : fst s ≤ snd t
                simpa [real_seq.seq, real_seq.inclusion_const, snap, h0,
                  segment.le, segment.inclusion, segment.fst, segment.snd] using hn1
              exact False.elim (not_lt_of_ge hle hpos)
            ·
              by_cases han : a n = 0
              · exact han
              · exfalso
                apply h0
                exact ⟨n, Nat.le_refl n, han⟩

        | inr hgt =>
            -- 0 < snap a -> ∃ n, a n ≠ 0
            right
            rcases hgt with ⟨n, hn⟩
            -- hn : (inclusion 0).seq n < (snap a).seq n
            -- segment.lt: snd left < fst right; snd(inclusion 0)=0
            have hn' : (0 : ℚ) < segment.fst ((snap a).seq n) := by
              simpa [real_seq.seq, real_seq.inclusion_const, segment.lt, segment.inclusion,
                segment.snd, segment.fst] using hn

            by_cases h0 : (∃ i : ℕ, i ≤ n ∧ a i ≠ 0)
            · rcases h0 with ⟨i, hi, hai⟩
              exact ⟨i, hai⟩
            ·
              have hpos : (0 : ℚ) < (1 : ℚ) / (Nat.succ n : ℚ) := by
                have : (0 : ℚ) < (Nat.succ n : ℚ) := by
                  exact_mod_cast Nat.succ_pos n
                simpa using (one_div_pos.mpr this)
              have hfst_le0 : segment.fst ((snap a).seq n) ≤ 0 := by
                -- fst(two_sided_inclusion r) = -r ≤ 0
                simp [snap, real_seq.seq, h0, segment.two_sided_inclusion,
                  segment.fst, segment.snd]
                have : (0 : ℚ) ≤ (↑n + 1 : ℚ) := by
                  exact add_nonneg (Nat.cast_nonneg _) (by norm_num)
                have hinv : (0 : ℚ) ≤ (↑n + 1 : ℚ)⁻¹ := inv_nonneg.2 this
                simpa [one_div, Nat.cast_succ] using (neg_nonpos.2 hinv)
              exact False.elim (not_lt_of_ge hfst_le0 hn')


def WLEM : Prop := ∀ P : Prop, ¬ P ∨ ¬¬ P

def WLPO : Prop := ∀ a : 𝒩, (∀ n : ℕ, a n = 0) ∨ (¬ ∀ n : ℕ, a n = 0)

theorem PO_implies_WLEM : PO → WLEM := by
  intro po P
  cases po P with
  | inl hp =>
      right
      intro np
      exact np hp
  | inr hnp =>
      left
      exact hnp

theorem LPO_implies_WLPO : LPO → WLPO := by
  intro lpo a
  cases lpo a with
  | inl aeq =>
      left; exact aeq
  | inr ane =>
      right
      intro aeq
      rcases ane with ⟨n, hn⟩
      exact hn (aeq n)

theorem weak_LEM_implies_weak_LPO : WLEM → WLPO := by
  intro wlem a
  cases wlem (∃ n : ℕ, a n ≠ 0) with
  | inl nh =>
      left
      have h : ∀ n : ℕ, ¬ a n ≠ 0 := forall_not_of_not_exists nh
      intro n
      by_cases hn : a n = 0
      · exact hn
      · exact False.elim (h n hn)
  | inr nnh =>
      right
      intro hzero
      apply nnh
      intro hex
      rcases hex with ⟨n, hn⟩
      exact hn (hzero n)

theorem weak_LPO_implies_LLPO : WLPO → LLPO := by
  intro wlpo a
  classical

  let d : 𝒩 :=
    fun n =>
      if n % 2 = 0 then
        if (∃ i : ℕ, i < n ∧ a i ≠ 0) then 0 else a n
      else
        0

  have ddef :
      d =
        (fun n =>
          if n % 2 = 0 then
            if (∃ i : ℕ, i < n ∧ a i ≠ 0) then 0 else a n
          else 0) := rfl

  cases wlpo d with
  | inl deq =>
      right
      intro k hk

      have hdk : d k = 0 := deq k

      dsimp [d] at hdk
      by_cases hk0 : k % 2 = 0
      ·
        simp [hk0] at hdk
        by_cases hex : (∃ i : ℕ, i < k ∧ a i ≠ 0)
        ·
          rcases hex with ⟨i, hik, hai⟩
          have : a i = 0 := hk.1 i hik
          exact False.elim (hai (this))
        ·
          have hak0 : a k = 0 := by


            have hkfun : (∀ x : ℕ, x < k → a x = 0) → a k = 0 := by
              simpa [hex] using hdk
            exact hkfun hk.1

          exact False.elim (hk.2 hak0)
      ·
        have : k % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
          · exfalso; exact hk0 (h0)
          · exact h1
        exact this
  | inr nd =>

      left
      intro k hk

      by_contra hkodd
      -- hkodd : ¬ k%2=0
      have hk0 : k % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
        · exact h0
        · exfalso
          apply nd
          intro n
          dsimp [d]
          by_cases hn0 : n % 2 = 0
          · -- n%2=0
            simp [hn0]
            by_cases hex : (∃ i : ℕ, i < n ∧ a i ≠ 0)
            · simp [hex]
            · -- hex false -> d n = a n, need a n = 0
              have han : a n = 0 := by
                by_cases hnk : n < k
                · exact hk.1 n hnk
                · have hk_le_n : k ≤ n := Nat.le_of_not_gt hnk
                  cases hk_le_n.eq_or_lt with
                  | inl hEq =>
                      -- n = k, but hn0 says k%2=0 contradicts h1 : k%2=1
                      subst hEq
                      exfalso
                      have : (0:ℕ) ≠ 1 := by decide
                      exact this (by simp [hn0] at h1)
                  | inr hLt =>
                      -- k < n -> hex should be true by taking i=k
                      exfalso
                      apply hex
                      refine ⟨k, hLt, hk.2⟩
              simp [hex, han]
          · -- n%2≠0 -> d n = 0
            simp [hn0]
      apply nd
      intro n
      dsimp [d]
      by_cases hn0 : n % 2 = 0
      · simp [hn0]
        by_cases hex : (∃ i : ℕ, i < n ∧ a i ≠ 0)
        ·
          simp [hex]
        ·
          have han : a n = 0 := by

            by_cases hnk : n < k
            · exact hk.1 n hnk
            ·

              have hk_le_n : k ≤ n := Nat.le_of_not_gt hnk
              cases hk_le_n.eq_or_lt with
              | inl hEq =>
                  -- n=k
                  subst hEq
                  exfalso
                  exact hkodd hk0
              | inr hLt =>
                  exfalso
                  apply hex
                  refine ⟨k, hLt, ?_⟩
                  exact hk.2
          simp [hex, han]
      · -- n%2≠0 -> d n =0
        simp [hn0]

theorem weak_LEM_implies_LLPO : WLEM → LLPO := by
  intro wlem
  apply weak_LPO_implies_LLPO
  exact weak_LEM_implies_weak_LPO wlem

theorem weak_LEM_implies_LLPO' : WLEM → LLPO := by
  intro wlem b
  classical
  cases wlem (∀ k : ℕ, ((∀ i : ℕ, i < k → b i = 0) ∧ b k ≠ 0 → k % 2 = 0)) with
  | inl nh =>
      right
      intro k hk
      have : k % 2 ≠ 0 := by
        intro hk0
        apply nh
        intro j hj
        have hjk : j = k :=
          NatSeq.first_zero_eq b j k hj.1 hj.2 hk.1 hk.2
        simpa [hjk] using hk0
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · exfalso; exact this h0
      · exact h1
  | inr nnh =>
      left
      intro k hk
      by_contra hk1
      apply nnh
      intro h
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · exact hk1 (by simp [h0])
      ·
        have hk0 : k % 2 = 0 := h k hk
        have h01 : (0 : ℕ) ≠ 1 := by decide
        exact h01 (by
          have : (0 : ℕ) = 1 := by
            exact (hk0.symm.trans h1)
          exact this)

/-!
## Reckless wrt LLPO
-/

theorem reckless_LLPO_not_not_or :
    reckless_LLPO (∀ P Q : Prop, ¬¬ (P ∨ Q) → (¬¬ P ∨ ¬¬ Q)) := by
  constructor
  · intro po P Q h
    cases po P with
    | inl hp =>
        left
        intro np
        exact np hp
    | inr np =>
        cases po Q with
        | inl hq =>
            right
            intro nq
            exact nq hq
        | inr nq =>
            exfalso
            apply h
            intro pq
            cases pq with
            | inl hp => exact np hp
            | inr hq => exact nq hq
  · intro h₁
    apply weak_LEM_implies_LLPO
    intro P
    have h₂ := h₁ P (¬ P) (by
      intro hn
      apply hn
      right
      intro p
      apply hn
      left
      exact p)
    cases h₂ with
    | inl nnP =>
        right; exact nnP
    | inr nnnotP =>
        left
        -- ¬¬¬P -> ¬P
        intro p
        exact nnnotP (by intro np; exact np p)

theorem reckless_LLPO_not_and_implies_not_or_not :
    reckless_LLPO (∀ P Q : Prop, ¬ (P ∧ Q) → (¬ P ∨ ¬ Q)) := by
  constructor
  · intro po P Q h
    cases po P with
    | inl hp =>
        cases po Q with
        | inl hq =>
            exfalso
            exact h ⟨hp, hq⟩
        | inr nq =>
            right; exact nq
    | inr np =>
        left; exact np
  · intro h
    apply weak_LEM_implies_LLPO
    intro P
    -- ¬(P ∧ ¬P) is always true
    have : ¬ (P ∧ ¬ P) := by
      intro hp
      exact hp.2 hp.1
    exact h P (¬ P) this

/--
If P ∨ ¬P holds for some proposition P, then eliminating double negation is allowed for P
-/
lemma or_not_implies_not_not_implies (P: Prop) (h : P ∨ ¬ P) : ¬¬ P → P := by
  intro hp
  cases h with
  | inl p => exact p
  | inr np =>
      exfalso
      exact hp np

theorem reckless_LLPO_not_not_implies_or :
    reckless_LLPO (∀ P : Prop, (¬¬ P → P) → P ∨ ¬ P) := by
  constructor
  · intro po P h
    exact po P
  · intro h
    apply weak_LEM_implies_LLPO
    intro P
    have hp := h (¬ P)
    -- (¬¬¬P → ¬P)
    have : (¬¬ (¬ P) → ¬ P) := by
      intro nnp
      intro p
      exact nnp (by intro np; exact np p)
    exact hp this

-- A reminder that brackets are important
example : (∀ P : Prop, ¬¬ P → P) → (∀ P : Prop, P ∨ ¬ P) := by
  intro h P
  -- ¬¬(P ∨ ¬P)
  have : ¬¬ (P ∨ ¬ P) := by
    intro hn
    apply hn
    right
    intro p
    apply hn
    left
    exact p
  exact h (P ∨ ¬ P) this

end reckless
