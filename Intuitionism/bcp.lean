import Mathlib
import MyNewProject.Intuitionism.nat_seq
import MyNewProject.Intuitionism.reckless

open NatSeq

/--
Brouwer's Continuity Principle (BCP)

If the relation R on 𝒩×ℕ satisfies:
  for all infinite sequences α ∈ 𝒩 there is an n ∈ ℕ such that (α R n),
then the relation should be decidable based on an initial part of α.
-/
def BCP : Prop :=
  ∀ R : 𝒩 → ℕ → Prop,
    (∀ a : 𝒩, ∃ n : ℕ, R a n) →
    ∀ a : 𝒩, ∃ m n : ℕ, ∀ b : 𝒩, (∀ i : ℕ, i < m → a i = b i) → R b n

/--
Given a : 𝒩 and n : ℕ, we can build b : 𝒩 that agrees with a on indices < n,
but differs at index n.
-/
lemma exists_start_eq_ne (a : 𝒩) (n : ℕ) :
    ∃ b : 𝒩, (∀ i : ℕ, i < n → a i = b i) ∧ a n ≠ b n := by
  let b : 𝒩 := fun i : ℕ => if i < n then a i else a i + 1
  refine ⟨b, ?_, ?_⟩
  · intro i hi
    simp [b, hi]
  · have hn : ¬ n < n := Nat.lt_irrefl n
    -- b n = a n + 1, so a n ≠ b n
    simp [b, hn]

/--
Using BCP, a function f : 𝒩 → ℕ can never be injective, in a strong sense:
for every a there exists b with a # b and f a = f b.
-/
theorem strongly_not_injective (f : 𝒩 → ℕ) :
    BCP → ∀ a : 𝒩, ∃ b : 𝒩, a # b ∧ f a = f b := by
  intro bcp a
  let R : 𝒩 → ℕ → Prop := fun α n => f α = n
  have g₁ : ∀ α : 𝒩, ∃ n : ℕ, R α n := by
    intro α
    exact ⟨f α, rfl⟩

  rcases bcp R g₁ a with ⟨m, n, hcon⟩
  rcases exists_start_eq_ne a m with ⟨b, hab_start, hab_ne⟩
  refine ⟨b, ?_, ?_⟩
  · -- a # b
    exact ⟨m, hab_ne⟩
  · -- f a = f b
    have g₂ : R a n := by
      apply hcon a
      intro i hi
      rfl
    have g₃ : R b n := by
      apply hcon b
      intro i hi
      exact hab_start i hi
    -- g₂ : f a = n, g₃ : f b = n
    exact g₂.trans g₃.symm

/--
A more classical-looking "not injective" corollary.
-/
theorem not_injective (f : 𝒩 → ℕ) :
    BCP → ¬ (∀ a b : 𝒩, f a = f b → a =' b) := by
  intro bcp h
  have h0 := h NatSeq.zero
  rcases strongly_not_injective f bcp NatSeq.zero with ⟨b, hb, hfb⟩
  have hb0 : NatSeq.zero =' b := h0 b hfb
  have hne : NatSeq.zero ≠' b := NatSeq.ne_of_apart NatSeq.zero b hb
  exact hne hb0

/--
If a and b agree on all indices ≥ n+1, and also agree at n,
then they agree on all indices ≥ n.
-/
lemma grow_tail (a b : 𝒩) (n : ℕ)
    (h₁ : ∀ i : ℕ, Nat.succ n ≤ i → a i = b i)
    (h₂ : a n = b n) :
    ∀ i : ℕ, n ≤ i → a i = b i := by
  intro i hi
  rcases lt_or_eq_of_le hi with hlt | heq
  · -- n < i
    exact h₁ i (Nat.succ_le_of_lt hlt)
  · -- n = i
    subst heq
    exact h₂

/--
If a and b are equal from index n onward, but not equal everywhere,
then there exists an index i < n where they differ.
(Constructive, because it's a finite search on the first n positions.)
-/
lemma tail_equal_not_forall_equal_implies_exists_ne (a b : 𝒩) (n : ℕ)
    (h₁ : ∀ i : ℕ, n ≤ i → a i = b i)
    (h₂ : ¬ ∀ i : ℕ, a i = b i) :
    ∃ i : ℕ, i < n ∧ a i ≠ b i := by
  revert h₁ h₂
  induction n with
  | zero =>
      intro h₁ h₂
      exfalso
      apply h₂
      intro i
      exact h₁ i (Nat.zero_le i)
  | succ m ih =>
      intro h₁ h₂
      by_cases hmb : a m = b m
      ·
        have htail : ∀ i : ℕ, m ≤ i → a i = b i := by
          intro i hi
          rcases lt_or_eq_of_le hi with hlt | heq
          ·
            have : Nat.succ m ≤ i := Nat.succ_le_of_lt hlt
            exact h₁ i this
          ·
            subst heq
            exact hmb
        rcases ih htail h₂ with ⟨i, him, hine⟩
        refine ⟨i, Nat.lt_trans him (Nat.lt_succ_self m), hine⟩
      ·
        exact ⟨m, Nat.lt_succ_self m, hmb⟩


lemma ite_cond_eq (a b d : 𝒩) (n : ℕ)
    (hd : d =' (fun i => if i < n then b i else a i)) :
    ∀ i : ℕ, n ≤ i → d i = a i := by
  intro i hi
  have hnot : ¬ i < n := Nat.not_lt_of_ge hi
  simpa [hnot] using (hd i)

/--
BCP example:
If a # b, then any c cannot be equal to both a and b;
and conversely, with BCP, that property implies a # b.
-/
theorem apart_iff_forall_ne_or_ne (bcp : BCP) (a b : 𝒩) :
    a # b ↔ ∀ c : 𝒩, a ≠' c ∨ c ≠' b := by
  constructor
  · -- → direction: use apart_cotrans
    intro hab c
    rcases NatSeq.apart_cotrans a b hab c with hac | hcb
    · left
      exact NatSeq.ne_of_apart a c hac
    · right
      exact NatSeq.ne_of_apart c b hcb
  ·
    intro h
    let R : 𝒩 → ℕ → Prop := fun c n => if n = 0 then c ≠' a else c ≠' b

    have hr : ∀ c : 𝒩, ∃ n : ℕ, R c n := by
      intro c
      cases h c with
      | inl hac =>
          refine ⟨0, ?_⟩
          have hca : c ≠' a := (NatSeq.seq_ne_symm a c).1 hac
          simpa [R] using hca
      | inr hcb =>
          refine ⟨1, ?_⟩
          simpa [R] using hcb

    rcases bcp R hr b with ⟨m, n, hbcp⟩
    have hb : R b n := hbcp b (by intro i hi; rfl)

    cases n with
    | zero =>
        -- n = 0, so any d with same prefix as b satisfies d ≠' a.
        let d : 𝒩 := fun i => if i < m then b i else a i

        have hd_prefix : ∀ i : ℕ, i < m → b i = d i := by
          intro i hi
          simp [d, hi]

        have hdR : R d 0 := hbcp d hd_prefix
        have hd_ne : d ≠' a := by
          simpa [R] using hdR

        -- d equals a on the tail i ≥ m
        have hd_eq : d =' (fun i => if i < m then b i else a i) := by
          intro i; rfl
        have htail : ∀ i : ℕ, m ≤ i → d i = a i :=
          ite_cond_eq a b d m hd_eq

        -- from d ≠' a get ¬ ∀ i, d i = a i
        have hnotforall : ¬ ∀ i : ℕ, d i = a i := by
          simpa [NatSeq.seq_ne, NatSeq.seq_eq] using hd_ne

        rcases tail_equal_not_forall_equal_implies_exists_ne d a m htail hnotforall with
          ⟨j, hjlt, hjne⟩

        -- since j < m, d j = b j, hence b j ≠ a j
        have hdj : d j = b j := by
          simp [d, hjlt]
        have hbj : b j ≠ a j := by
          intro hEq
          apply hjne
          exact hdj.trans hEq
        have haj : a j ≠ b j := by
          intro hEq
          exact hbj hEq.symm

        exact ⟨j, haj⟩
    | succ n' =>
        -- n>0 would force R b n = (b ≠' b), contradiction
        exfalso
        have hbb : b ≠' b := by
          simpa [R] using hb
        exact hbb NatSeq.seq_eq_refl

/--
BCP implies not LPO.
-/
theorem BCP_implies_not_LPO : BCP → ¬ reckless.LPO := by
  intro bcp lpo
  let R : 𝒩 → ℕ → Prop :=
    fun a i => if i = 0 then (∀ n : ℕ, a n = 0) else (∃ n : ℕ, a n ≠ 0)

  have hr : ∀ a : 𝒩, ∃ i : ℕ, R a i := by
    intro a
    cases lpo a with
    | inl aeq0 =>
        refine ⟨0, ?_⟩
        simpa [R] using aeq0
    | inr ane0 =>
        refine ⟨1, ?_⟩
        simpa [R] using ane0

  rcases bcp R hr NatSeq.zero with ⟨m, n, hcon⟩
  cases n with
  | zero =>
      let b : 𝒩 := fun k => if k < m then 0 else 1
      have bstart : ∀ i : ℕ, i < m → NatSeq.zero i = b i := by
        intro i hi
        simp [NatSeq.zero, b, hi]
      have hb : R b 0 := hcon b bstart
      have hb0 : ∀ k : ℕ, b k = 0 := by
        simpa [R] using hb
      have hb_m : b m = 0 := hb0 m
      have hb_m' : b m = 1 := by
        have h : ¬ m < m := Nat.lt_irrefl m
        simp [b, h]
      have : (1 : ℕ) = 0 := by
        calc
          (1 : ℕ) = b m := hb_m'.symm
          _ = 0 := hb_m
      exact Nat.one_ne_zero this
  | succ n' =>
      have hz : ∀ i : ℕ, i < m → NatSeq.zero i = NatSeq.zero i := by
        intro i hi; rfl
      have hR0 : R NatSeq.zero (Nat.succ n') := hcon NatSeq.zero hz
      have hex : ∃ k : ℕ, NatSeq.zero k ≠ 0 := by
        simpa [R] using hR0
      rcases hex with ⟨k, hk⟩
      exact hk rfl

/--
BCP implies not WLPO.
-/
theorem BCP_implies_not_WLPO : BCP → ¬ reckless.WLPO := by
  intro bcp wlpo
  let R : 𝒩 → ℕ → Prop :=
    fun a i => if i = 0 then (∀ n : ℕ, a n = 0) else (¬ ∀ n : ℕ, a n = 0)

  have hr : ∀ a : 𝒩, ∃ i : ℕ, R a i := by
    intro a
    cases wlpo a with
    | inl aeq0 =>
        refine ⟨0, ?_⟩
        simpa [R] using aeq0
    | inr naeq0 =>
        refine ⟨1, ?_⟩
        simpa [R] using naeq0

  rcases bcp R hr NatSeq.zero with ⟨m, n, hcon⟩
  cases n with
  | zero =>
      let b : 𝒩 := fun k => if k < m then 0 else 1
      have bstart : ∀ i : ℕ, i < m → NatSeq.zero i = b i := by
        intro i hi
        simp [NatSeq.zero, b, hi]
      have hb : R b 0 := hcon b bstart
      have hb0 : ∀ k : ℕ, b k = 0 := by
        simpa [R] using hb
      have hb_m : b m = 0 := hb0 m
      have hb_m' : b m = 1 := by
        have h : ¬ m < m := Nat.lt_irrefl m
        simp [b, h]
      have : (1 : ℕ) = 0 := by
        calc
          (1 : ℕ) = b m := hb_m'.symm
          _ = 0 := hb_m
      exact Nat.one_ne_zero this
  | succ n' =>
      have hz : ∀ i : ℕ, i < m → NatSeq.zero i = NatSeq.zero i := by
        intro i hi; rfl
      have hR0 : R NatSeq.zero (Nat.succ n') := hcon NatSeq.zero hz
      have hnot : ¬ ∀ k : ℕ, NatSeq.zero k = 0 := by
        simpa [R] using hR0
      have hall : ∀ k : ℕ, NatSeq.zero k = 0 := by
        intro k; rfl
      exact hnot hall
