import Mathlib

import MyNewProject.Intuitionism.fin_seq

open fin_seq
open len_seq





/-- Encode a fixed-length sequence `Fin (n+1) → ℕ` into a natural number. -/
def encode_len_seq : ∀ n : ℕ, len_seq (Nat.succ n) → ℕ
| 0, a => a 0
| n+1, a =>
    Nat.pair (a 0) (encode_len_seq n (fun i : Fin (Nat.succ n) => a i.succ))

/-- Decode a natural number into a fixed-length sequence `Fin (n+1) → ℕ`. -/
def decode_len_seq : ∀ n : ℕ, ℕ → len_seq (Nat.succ n)
| 0, k => fun _ => k
| n+1, k =>
    let p := Nat.unpair k
    Fin.cases p.1 (fun i : Fin (Nat.succ n) => decode_len_seq n p.2 i)

/-- `decode` is left-inverse of `encode` for `len_seq (n+1)`. -/
theorem decode_encode_len_seq :
    ∀ n (a : len_seq (Nat.succ n)),
      decode_len_seq n (encode_len_seq n a) = a
| 0, a => by
    funext i
    -- i : Fin 1, so i = 0
    have hi : i = (0 : Fin 1) := by
      apply Fin.ext
      have : i.val ≤ 0 := (Nat.lt_succ_iff.mp i.isLt)
      exact Nat.eq_zero_of_le_zero this
    simp [encode_len_seq, decode_len_seq, hi]
| n+1, a => by
    let tail : len_seq (Nat.succ n) := fun j => a j.succ
    have ih := decode_encode_len_seq n tail
    funext i
    cases i using Fin.cases with
    | zero =>
        simp [encode_len_seq, decode_len_seq, tail, Nat.unpair_pair]
    | succ j =>
        have htj :
            decode_len_seq n (encode_len_seq n tail) j = tail j := by
          simpa using congrArg (fun f => f j) ih
        simp [encode_len_seq, decode_len_seq, tail, Nat.unpair_pair, htj]

/-- `encode` is right-inverse of `decode` for `len_seq (n+1)`. -/
theorem encode_decode_len_seq :
    ∀ n (k : ℕ),
      encode_len_seq n (decode_len_seq n k) = k
| 0, k => by
    simp [encode_len_seq, decode_len_seq]
| n+1, k => by
    let p := Nat.unpair k
    have ih := encode_decode_len_seq n p.2
    simp [encode_len_seq, decode_len_seq, p, ih, Nat.pair_unpair]

/-- Main equivalence: `len_seq (n+1) ≃ ℕ`. -/
def len_seq_equiv_nat (n : ℕ) : len_seq (Nat.succ n) ≃ ℕ :=
{ toFun := encode_len_seq n
  invFun := decode_len_seq n
  left_inv := decode_encode_len_seq n
  right_inv := encode_decode_len_seq n }

/-- Compatibility name from the old file: `len_seq 1 ≃ ℕ`. -/
def len_seq_1_equiv_nat : len_seq 1 ≃ ℕ :=
by
  simpa using (len_seq_equiv_nat 0)

/-- Optional: `len_seq 0 ≃ PUnit`-/
def len_seq_0_equiv_punit : len_seq 0 ≃ PUnit :=
{ toFun := fun _ => PUnit.unit
  invFun := fun _ => fun i => (Fin.elim0 i)
  left_inv := by
    intro a
    funext i
    exact Fin.elim0 i
  right_inv := by
    intro u
    cases u
    rfl }

/-- Optional: an equivalence between lengths `n+2` and `n+1` (可由两边都等价于 ℕ 得到). -/
def len_seq_succ_equiv_len_seq (n : ℕ) :
    len_seq (Nat.succ (Nat.succ n)) ≃ len_seq (Nat.succ n) :=
  (len_seq_equiv_nat (Nat.succ n)).trans (len_seq_equiv_nat n).symm

/-- Old helper: if `n ≠ 0`, then `len_seq n ≃ ℕ`. -/
def len_seq_equiv_nat' (n : ℕ) (h : n ≠ 0) : len_seq n ≃ ℕ := by
  cases n with
  | zero => cases (h rfl)
  | succ m =>
      simpa using len_seq_equiv_nat m




/-- Encode a `fin_seq` into ℕ (bijective with the decode below). -/
def encode_fin_seq : fin_seq → ℕ
| ⟨0, _⟩ => 0
| ⟨Nat.succ n, s⟩ =>
    Nat.succ (Nat.pair n ((len_seq_equiv_nat n).toFun s))

/-- Decode ℕ back into a `fin_seq`. -/
def decode_fin_seq : ℕ → fin_seq
| 0 => fin_seq.empty_seq
| Nat.succ k =>
    let p := Nat.unpair k
    ⟨Nat.succ p.1, (len_seq_equiv_nat p.1).invFun p.2⟩

/-- `decode_fin_seq` is left-inverse of `encode_fin_seq`. -/
theorem decode_encode_fin_seq (a : fin_seq) :
    decode_fin_seq (encode_fin_seq a) = a := by
  cases a with
  | mk len seq =>
    cases len with
    | zero =>
        ext
        · rfl
        ·
          have hfun : (fun _ : Fin 0 => 0) = seq := by
            funext i
            exact Fin.elim0 i
          simpa [encode_fin_seq, decode_fin_seq, fin_seq.empty_seq] using (heq_of_eq hfun)

    | succ n =>
        ext
        · simp [encode_fin_seq, decode_fin_seq, Nat.unpair_pair]
        ·
          simp [encode_fin_seq, decode_fin_seq]
          let t : ℕ := (len_seq_equiv_nat n) seq
          have hn : (Nat.unpair (Nat.pair n t)).1 = n := by
            simp
          have hk : (Nat.unpair (Nat.pair n t)).2 = t := by
            simp
          rw [hn]
          have hEq : (len_seq_equiv_nat n).symm t = seq := by
            simp [t]
          exact heq_of_eq hEq


/-- `encode_fin_seq` is right-inverse of `decode_fin_seq`. -/
theorem encode_decode_fin_seq (n : ℕ) :
    encode_fin_seq (decode_fin_seq n) = n := by
  cases n with
  | zero =>
      rfl
  | succ k =>
      let p := Nat.unpair k
      have hcode :
          (len_seq_equiv_nat p.1).toFun ((len_seq_equiv_nat p.1).invFun p.2) = p.2 :=
        (len_seq_equiv_nat p.1).right_inv p.2
      simp [decode_fin_seq, encode_fin_seq, p, hcode, Nat.pair_unpair]

/-- Final result: `fin_seq ≃ ℕ`. -/
def fin_seq_equiv_of_nat : fin_seq ≃ ℕ :=
{ toFun := encode_fin_seq
  invFun := decode_fin_seq
  left_inv := decode_encode_fin_seq
  right_inv := encode_decode_fin_seq }
