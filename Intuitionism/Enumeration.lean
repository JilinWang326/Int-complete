import Mathlib.Tactic.Set
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.Nat.Pairing

/-!
# Constructive scheduler for Veldman §3.31

Paper §3.31 fixes a bijection `⟪n,m,k⟫ : Nat² × {0,1,2} → Nat` with the
alignment property
`⟪n,m,0⟫ + 2 = ⟪n,m,1⟫ + 1 = ⟪n,m,2⟫`.

This file provides an explicit constructive implementation of that scheduler and
its inverse.  The binary-recursive version is used as the default encoding.
-/

namespace IPC
/-- Reference implementation of Veldman's scheduler `⟪n,m,k⟫` from paper §3.31,
using `Nat.pair` for the `(n,m)` component. -/
def schedEncodePair : (ℕ × ℕ × Fin 3) → ℕ
| ⟨n,m,k⟩ => 3 * Nat.pair n m + k.1


/-
Corresponds to the “inverse (decoding)” part of §3.31 where “<< >> is a bijection”.
The paper only states that a bijection exists; in Lean we must provide an explicit
inverse in order to package it as an `Equiv`.
-/
/-- Decode ℕ back into (n,m,k) by div/mod 3 and unpair. -/
def schedDecodePair (t : ℕ) : (ℕ × ℕ × Fin 3) :=
  let q := t / 3
  let r := t % 3
  let nm := Nat.unpair q
  ⟨nm.1, nm.2, ⟨r, Nat.mod_lt _ (by decide : 0 < 3)⟩⟩

def pairEncodeBin : ℕ → ℕ → ℕ
  | 0,     m => Nat.bit false m
  | n + 1, m => Nat.bit true (pairEncodeBin n m)

/-
Inverse of `pairEncodeBin`, defined by binary recursion:
- if the last bit is `0`, we are at first coordinate `0`
- if the last bit is `1`, peel it off and recurse
-/
def pairDecodeBin : ℕ → ℕ × ℕ :=
  Nat.binaryRec
    (motive := fun _ => ℕ × ℕ)
    (zero := (0, 0))
    (bit := fun b n ih =>
      if b then
        (ih.1 + 1, ih.2)
      else
        (0, n))

@[simp] theorem pairDecodeBin_bit (b : Bool) (n : ℕ) :
    pairDecodeBin (Nat.bit b n) =
      if b then
        let p := pairDecodeBin n
        (p.1 + 1, p.2)
      else
        (0, n) := by
  simpa [pairDecodeBin] using
    (Nat.binaryRec_eq
      (motive := fun _ => ℕ × ℕ)
      (zero := (0, 0))
      (bit := fun b n (ih : ℕ × ℕ) =>
        if b then
          (ih.1 + 1, ih.2)
        else
          (0, n))
      b n (Or.inl rfl))

@[simp] theorem pairDecodeBin_encode (n m : ℕ) :
    pairDecodeBin (pairEncodeBin n m) = (n, m) := by
  induction n with
  | zero =>
      simpa [pairEncodeBin] using (pairDecodeBin_bit false m)
  | succ n ih =>
      simpa [pairEncodeBin, ih] using (pairDecodeBin_bit true (pairEncodeBin n m))

@[simp] theorem pairEncodeBin_decode (t : ℕ) :
    pairEncodeBin (pairDecodeBin t).1 (pairDecodeBin t).2 = t := by
  refine Nat.binaryRec ?h0 ?hbit t
  · have hzero : pairDecodeBin 0 = (0, 0) := by
      simpa [Nat.bit] using (pairDecodeBin_bit false 0)
    simp [hzero, pairEncodeBin]
  · intro b n ih
    cases b with
    | false =>
      have hdec : pairDecodeBin (2 * n) = (0, n) := by
        simpa [Nat.bit] using (pairDecodeBin_bit false n)
      simp [hdec, pairEncodeBin]
    | true =>
      have hdec : pairDecodeBin (2 * n + 1) = ((pairDecodeBin n).1 + 1, (pairDecodeBin n).2) := by
        simpa [Nat.bit] using (pairDecodeBin_bit true n)
      calc
        pairEncodeBin (pairDecodeBin (2 * n + 1)).1 (pairDecodeBin (2 * n + 1)).2
            = pairEncodeBin ((pairDecodeBin n).1 + 1) (pairDecodeBin n).2 := by simp [hdec]
        _ = Nat.bit true (pairEncodeBin (pairDecodeBin n).1 (pairDecodeBin n).2) := by
            simp [pairEncodeBin]
        _ = Nat.bit true n := by simp [ih]

/-- The new constructive equivalence `(ℕ × ℕ) ≃ ℕ`. -/
def pairEquivBin : (ℕ × ℕ) ≃ ℕ where
  toFun := fun x => pairEncodeBin x.1 x.2
  invFun := pairDecodeBin
  left_inv := by
    intro x
    rcases x with ⟨n, m⟩
    simp
  right_inv := by
    intro t
    simp



/-
Same outer shell as before, but now the pair-part uses `pairEncodeBin`.
-/
def schedEncodeBin : (ℕ × ℕ × Fin 3) → ℕ
  | ⟨n, m, k⟩ => 3 * pairEncodeBin n m + k.1

def schedDecodeBin (t : ℕ) : (ℕ × ℕ × Fin 3) :=
  let q := t / 3
  let r := t % 3
  let nm := pairDecodeBin q
  ⟨nm.1, nm.2, ⟨r, Nat.mod_lt _ (by decide : 0 < 3)⟩⟩

theorem schedEncodeBin_decode (t : ℕ) :
    schedEncodeBin (schedDecodeBin t) = t := by
  calc
    schedEncodeBin (schedDecodeBin t) = 3 * (t / 3) + (t % 3) := by
      simp [schedEncodeBin, schedDecodeBin]
    _ = t % 3 + 3 * (t / 3) := by
      rw [Nat.add_comm]
    _ = t := by
      simpa using (Nat.mod_add_div t 3)

theorem schedDecodeBin_encode (x : ℕ × ℕ × Fin 3) :
    schedDecodeBin (schedEncodeBin x) = x := by
  rcases x with ⟨n, m, k⟩
  set p : ℕ := pairEncodeBin n m
  have hk : (k.1 : ℕ) < 3 := k.2

  have hmod : (3 * p + k.1) % 3 = k.1 := by
    calc
      (3 * p + k.1) % 3 = (k.1 + p * 3) % 3 := by
        simp [Nat.mul_comm, Nat.add_comm]
      _ = k.1 % 3 := by
        simp
      _ = k.1 := by
        exact Nat.mod_eq_of_lt hk

  have hdiv : (3 * p + k.1) / 3 = p := by
    calc
      (3 * p + k.1) / 3 = (k.1 + p * 3) / 3 := by
        simp [Nat.mul_comm, Nat.add_comm]
      _ = k.1 / 3 + p := by
        simpa using (Nat.add_mul_div_right k.1 p (show 0 < 3 by decide))
      _ = p := by
        simp [Nat.div_eq_of_lt hk]

  ext <;> simp [schedDecodeBin, schedEncodeBin, p, hdiv, hmod]

/-- New coding packaged as an equivalence. -/
def schedEquivBin : (ℕ × ℕ × Fin 3) ≃ ℕ where
  toFun := schedEncodeBin
  invFun := schedDecodeBin
  left_inv := schedDecodeBin_encode
  right_inv := schedEncodeBin_decode



/-
Keep the `Nat.pair` / `Nat.unpair` scheduler above as a reference implementation,
but expose the binary-recursive scheduler as the default one: its inverse proofs do
not go through `Nat.pair_unpair`, so `#print axioms` no longer reports
`Classical.choice` for the main scheduler lemmas.
-/
abbrev schedEncode : (ℕ × ℕ × Fin 3) → ℕ := schedEncodeBin

abbrev schedDecode : ℕ → (ℕ × ℕ × Fin 3) := schedDecodeBin

theorem schedDecode_encode (x : ℕ × ℕ × Fin 3) :
    schedDecode (schedEncode x) = x := by
  simpa [schedEncode, schedDecode] using schedDecodeBin_encode x

theorem schedEncode_decode (t : ℕ) :
    schedEncode (schedDecode t) = t := by
  simpa [schedEncode, schedDecode] using schedEncodeBin_decode t

/-
§3.31 “Let << >> be a bijective mapping … to Nat”:
in Lean we package the “bijection” as the standard structure `Equiv`.
-/
/-- The equivalence `(ℕ × ℕ × Fin 3) ≃ ℕ`. -/
def schedEquiv : (ℕ × ℕ × Fin 3) ≃ ℕ :=
{ toFun := schedEncode
  invFun := schedDecode
  left_inv := schedDecode_encode
  right_inv := schedEncode_decode }


/-! ### Alignment property (Veldman-style) -/

/-
In §3.31, the third component of `<<n,m,k>>` comes from `{0,1,2}`.
Lean represents this as `Fin 3`, and we provide the three explicit elements `0/1/2`.
These will later be used for the alignment property.
-/
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩

/-
Veldman 1976, §3.31 imposes an additional synchronization requirement:
for all `n,m`, `<<n,m,0>> + 2 = <<n,m,1>> + 1 = <<n,m,2>>`.
With the current constructive scheduler this is immediate, because the third
component is still inserted as the remainder mod `3`.
-/
/-- Alignment: `<<n,m,0>> + 2 = <<n,m,1>> + 1 = <<n,m,2>>`. -/
lemma sched_align (n m : ℕ) :
    (schedEncode ⟨n, m, k0⟩ + 2 = schedEncode ⟨n, m, k1⟩ + 1) ∧
    (schedEncode ⟨n, m, k1⟩ + 1 = schedEncode ⟨n, m, k2⟩) := by
  constructor <;>
    simp [schedEncode, schedEncodeBin, k0, k1, k2, Nat.add_comm]
  · omega
  · omega
