import Mathlib.Data.Nat.Pairing
import Intuitionism.FinSeq
import Intuitionism.Fan
import Intuitionism.IPC


namespace IPC

/-
Veldman 1976, §3.31 (Preliminaries)
  “<< >> : Nat^2 × {0,1,2} → Nat”. This is a concrete computable implementation
  of the paper's <<n,m,k>>:
  - base part: (n,m) ↦ Nat.pair n m
  - mod 3 part: k ∈ Fin 3 ↦ k.1
-/
/-- Encode (n,m,k) into ℕ by putting (n,m) into base part and k into mod 3 part. -/
def schedEncode : (ℕ × ℕ × Fin 3) → ℕ
| ⟨n,m,k⟩ => 3 * Nat.pair n m + k.1


/-
Corresponds to the “inverse (decoding)” part of §3.31 where “<< >> is a bijection”.
The paper only states that a bijection exists; in Lean we must provide an explicit
inverse in order to package it as an `Equiv`.
-/
/-- Decode ℕ back into (n,m,k) by div/mod 3 and unpair. -/
def schedDecode (t : ℕ) : (ℕ × ℕ × Fin 3) :=
  let q := t / 3
  let r := t % 3
  let nm := Nat.unpair q
  ⟨nm.1, nm.2, ⟨r, Nat.mod_lt _ (by decide : 0 < 3)⟩⟩


/-
One half of §3.31’s statement that “<< >> is a bijective mapping”:
  here we prove `schedEncode ∘ schedDecode = id` (a right inverse on ℕ),
  thereby supporting “surjectivity / right inverse”.
-/
/-- easier direction: encode (decode t) = t -/
theorem schedEncode_decode (t : ℕ) :
    schedEncode (schedDecode t) = t := by
  -- q := t/3, r := t%3, nm := unpair q, then pair (unpair q)=q
  -- and div_add_mod gives q*3 + r = t
  simp [schedEncode, schedDecode, Nat.pair_unpair, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
        Nat.div_add_mod]


/-
The other half of §3.31’s statement that “<< >> is a bijective mapping”:
  here we prove `schedDecode ∘ schedEncode = id` (a left inverse on ℕ×ℕ×Fin3),
  thereby supporting “injectivity / left inverse”.
-/
/-- harder direction: decode (encode x) = x -/
theorem schedDecode_encode (x : ℕ × ℕ × Fin 3) :
    schedDecode (schedEncode x) = x := by
  rcases x with ⟨n, m, k⟩
  set p : ℕ := Nat.pair n m
  have hk : (k.1 : ℕ) < 3 := k.2

  -- remainder: (3*p + k) % 3 = k
  have hmod : (3 * p + k.1) % 3 = k.1 := by
    calc
      (3 * p + k.1) % 3 = (k.1 + 3 * p) % 3 := by
        -- commute the addition
        simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = (k.1 % 3) := by
        -- (a + b*c) % b = a % b
        -- here b=3, a=k.1, c=p
        simp [Nat.add_mul_mod_self_left, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = k.1 := by
        simp [Nat.mod_eq_of_lt hk]

  -- quotient: (3*p + k) / 3 = p
  have hdiv : (3 * p + k.1) / 3 = p := by
    calc
      (3 * p + k.1) / 3 = (k.1 + 3 * p) / 3 := by
        simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = (k.1 / 3 + p) := by
        -- (a + b*c) / b = a/b + c
        -- here b=3, a=k.1, c=p
        have h0 := (Nat.add_mul_mod_self_left k.1 3 p)
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [Nat.add_mul_div_right (↑k) p (Nat.le.step (Nat.le.step Nat.le.refl))]
      _ = p := by
        simp [Nat.div_eq_of_lt hk]

  -- now unfold decode(encode ...) and compare components
  ext
  · -- first component = n
    simp [schedDecode, schedEncode, p, hdiv, Nat.unpair_pair]
  · simp
    · -- second component = m
      simp [schedDecode, schedEncode, p, hdiv, Nat.unpair_pair]
  simp
  simp [schedDecode, schedEncode, p, hdiv, Nat.unpair_pair]


/-
§3.31 “Let << >> be a bijective mapping … to Nat”:
  in Lean we package the “bijection” as the standard structure `Equiv`.
-/
/-- The equivalence (ℕ×ℕ×Fin3) ≃ ℕ. -/
noncomputable def schedEquiv : (ℕ × ℕ × Fin 3) ≃ ℕ :=
{ toFun := schedEncode
  invFun := schedDecode
  left_inv := schedDecode_encode
  right_inv := schedEncode_decode }


/-! ### Alignment property (Veldman-style) -/

/-
In §3.31, the third component of <<n,m,k>> comes from {0,1,2}.
Lean represents this as `Fin 3`, and we provide the three explicit elements 0/1/2.
These will later be used for the “alignment property”.
-/
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩


/-
Veldman 1976, §3.31 imposes an additional requirement on << >> (alignment/synchronization):
  for all n,m, <<n,m,0>> + 2 = <<n,m,1>> + 1 = <<n,m,2>>.
The role of this property is to place the three cases for the same (n,m) at three
consecutive “time points”, so that in the recursive definition in §3.32 the
“Case 1/2/3” steps can interleave in a regular rhythm.
-/
/-- Alignment: <<n,m,0>>+2 = <<n,m,1>>+1 = <<n,m,2>>. -/
lemma sched_align (n m : ℕ) :
    (schedEncode ⟨n, m, k0⟩ + 2 = schedEncode ⟨n, m, k1⟩ + 1) ∧
    (schedEncode ⟨n, m, k1⟩ + 1 = schedEncode ⟨n, m, k2⟩) := by
  constructor <;>
    simp [schedEncode, k0, k1, k2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  simp [Nat.pair]
  split_ifs
  symm
  rw[← Nat.add_assoc]
  symm
  rw[← Nat.add_assoc]
  rw[← Nat.add_assoc]
