import Intuitionism.UniversalModel
import Intuitionism.VeldmanConcrete
import Mathlib

set_option maxRecDepth 2000
/-!
Implication subfan for the propositional truth lemma: provide the `ImpHardData` needed for the implication-case
of the truth lemma in `UniversalModel.lean`, without changing the existing setup.

This file works *on top of* the existing files you provided:
- `UniversalModel.lean` (abstract completeness skeleton)
- `VeldmanConcrete.lean` (concrete Σ / F construction)
- `Enumeration.lean` (scheduler encoding/decoding)

Paper reference (Veldman 1976): Lemma 4.1 is the “hard direction” for implication.
In the propositional-only version, the subfan construction only needs the (i)(ii)
parts of Lemma 4.1; the quantifier-related (iii) disappears.

We implement a *subfan law* `T` which is a restriction of Σ and forces that,
for every k0-time `t`, if the currently scheduled formula is already in Γ_α
(or equals the special context formula `W`), then the digit at time `t` is `1`.
This guarantees `Γ_α ⊆ Γ_β` and `W ∈ Γ_β` for every β in the subfan.

Then we prove `stepRules` (One/Forced/Ctx/Split) for this subfan, yielding an
`ImpHardData` provider.
-/

open NatSeq
open fin_seq
open IPC

namespace ImplicationSubfan
namespace VC
open NatSeq fin_seq IPC

export IPC.VeldmanConcrete
  ( Enumerations
    Sigma Sigma_is_fan_law
    FS FS_empty F_mono
    -- The following exports are the concrete state-machine lemmas used repeatedly below.
    State initState
    decN decK
    Forced0 Forced0b
    AllowedStepb
    step runStateAux runState
    admittedAuxb Admittedb Sigma_eq_zero_iff
    Prefix_len_le Prefix_child
    runStateAux_proof_irrel
    admittedAuxb_proof_irrel
    runStateAux_eq_of_Prefix
    admittedAuxb_eq_of_Prefix
    extend_singleton_last
    chooseNext Allowed_chooseNext
    runStateAux_Fs_mono_le
    AllowedStepb_bound
    decK decN
    State FStep runStateAux runState step initState
  )
end VC

/-- The enumeration type from `UniversalModel.lean` (root namespace version). -/
abbrev ESk : Type := _root_.Enumerations
/-- The enumeration type from `VeldmanConcrete.lean` (the `IPC.VeldmanConcrete` version). -/
abbrev ECon : Type := VC.Enumerations

/-- Copy the enumeration data from the abstract universal-model namespace into the concrete namespace. -/
def toConcreteEnum (E : ESk) : ECon :=
{ W := E.W
, d := E.d
, W_surj := E.W_surj
, d_sound := E.d_sound
, d_complete := E.d_complete }

/-! ### The concrete fan as a `VeldmanFan` -/

/-- The concrete fan obtained by taking `IPC.VeldmanConcrete.Sigma/FS` as the `S/F` fields of `VeldmanFan`. -/

def Vconcrete (E : ESk) : _root_.VeldmanFan E := by
  let E0 : ECon := toConcreteEnum E
  refine
  { S := VC.Sigma E0
    hS := VC.Sigma_is_fan_law E0
    F := VC.FS E0
    F_empty := by
      -- The goal here is exactly `VC.FS E0 empty_seq = ∅` after unfolding definitions.
      simpa using (IPC.VeldmanConcrete.FS_empty (E := E0))
    F_mono := by
      intro s t hPre hs0 ht0
      -- Feed `s` and `t` explicitly to avoid leaving metavariables in `simpa using`.
      exact IPC.VeldmanConcrete.F_mono (E := E0) (s := s) (t := t) hPre hs0 ht0 }

lemma runStateAux_t (E0 : ECon) (s : fin_seq) :
    ∀ n (hn : n ≤ s.len), (VC.runStateAux E0 s n hn).t = n := by
  intro n hn
  induction n with
  | zero =>
      simp [VC.runStateAux, VC.initState]
  | succ n ih =>
      have hn' : n ≤ s.len := Nat.le_of_succ_le hn
      have ht : (VC.runStateAux E0 s n hn').t = n := ih hn'
      simp [VC.runStateAux, VC.step, ht]

lemma runState_t (E0 : VC.Enumerations) (s : fin_seq) :
    (VC.runState E0 s).t = s.len := by
  simpa [VC.runState] using (runStateAux_t (E0 := E0) (s := s) s.len le_rfl)


/-- Given `n ≤ s.len` and `0 < n`, construct the index `(n-1) : Fin s.len`. -/
def predIdx (s : fin_seq) (n : ℕ) (hn : n ≤ s.len) (hnpos : 0 < n) : Fin s.len := by
  cases n with
  | zero =>
      cases (Nat.lt_irrefl 0 hnpos)
  | succ k =>
      -- Here `n = k+1`, so `n-1 = k`, and therefore `k < s.len`.
      exact ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩

lemma runStateAux_prev1 (E0 : VC.Enumerations) (s : fin_seq) :
  ∀ n (hn : n ≤ s.len) (hnpos : 0 < n),
    (VC.runStateAux E0 s n hn).prev1 = s.seq (predIdx s n hn hnpos) := by
  intro n hn (hnpos : 0 < n)
  -- At this point `hnpos` is fixed as a proof of `0 < n`; it will not drift into a metavariable proof.
  let i : Fin s.len := predIdx s n hn hnpos
  change (VC.runStateAux E0 s n hn).prev1 = s.seq i
  -- From here we continue with the intended `cases`/`simp` proof structure.
  cases n with
  | zero =>
      cases (Nat.lt_irrefl 0 hnpos)
  | succ k =>
      simp [VC.runStateAux, VC.step, predIdx, i]
      -- If `simp` gets stuck on different `Fin` proof terms, add the indicated `Fin.ext` step.
      -- · apply congrArg s.seq; apply Fin.ext; rfl

/-- The index `n-2 : Fin s.len`, with the bound discharged automatically by `omega`. -/

def pred2Idx (s : fin_seq) (n : ℕ) (hn : n ≤ s.len) (hn2 : 2 ≤ n) : Fin s.len :=
  ⟨n - 2, by omega⟩

/-- At step `n` (with `n ≥ 2`), `runStateAux` stores in `prev2` exactly the digit at position `n-2`. -/
lemma runStateAux_prev2 (E0 : VC.Enumerations) (s : fin_seq) :
    ∀ n (hn : n ≤ s.len) (hn2 : 2 ≤ n),
      (VC.runStateAux E0 s n hn).prev2
        = s.seq (pred2Idx s n hn hn2) := by
  intro n hn hn2
  cases n with
  | zero =>
      -- `2 ≤ 0` is impossible.
      cases (by omega : False)
  | succ n =>
      cases n with
      | zero =>
          -- `2 ≤ 1` is impossible.
          cases (by omega : False)
      | succ k =>
          -- At this point the original `n` is `k+2`.
          -- First derive `hn1 : k+1 ≤ s.len` from `hn : k+2 ≤ s.len`.
          have hn1 : k + 1 ≤ s.len := by
            exact Nat.le_trans (Nat.le_succ (k + 1)) hn

          -- Step 1: unfold the successor clause of `runStateAux`; `prev2` becomes the previous state's `prev1`.
          have hstep :
              (VC.runStateAux E0 s (k + 2) hn).prev2
                = (VC.runStateAux E0 s (k + 1) hn1).prev1 := by
            -- Indeed, `runStateAux (n+1) = step st q`, and `step` sets `prev2 := st.prev1`.
            simp [VC.runStateAux, VC.step]

          -- Step 2: unfold the previous state's `prev1`; it is exactly the `k`-th digit.
          have hk_lt : k < s.len := by omega
          have hprev1 :
              (VC.runStateAux E0 s (k + 1) hn1).prev1
                = s.seq ⟨k, hk_lt⟩ := by
            -- runStateAux (k+1) = step (runStateAux k) (s.seq k)
            simp [VC.runStateAux, VC.step]

          -- Step 3: align the right-hand `⟨k, hk_lt⟩` with `pred2Idx ...`.
          have hk2 : 2 ≤ k + 2 := by omega
          have hFin :
              (⟨k, hk_lt⟩ : Fin s.len) = pred2Idx s (k + 2) hn hk2 := by
            apply Fin.ext
            unfold pred2Idx
            -- (k+2)-2 = k
            show k = k + 2 - 2
            omega

          -- Now concatenate the three equalities.
          calc
            (VC.runStateAux E0 s (k + 2) hn).prev2
                = (VC.runStateAux E0 s (k + 1) hn1).prev1 := hstep
            _   = s.seq ⟨k, hk_lt⟩ := hprev1
            _   = s.seq (pred2Idx s (k + 2) hn hk2) := by
                    simp [hFin]

/-! ### A helper: extending `Sigma` by an allowed digit -/

def child (s : fin_seq) (q : ℕ) : fin_seq := extend s (singleton q)

lemma Sigma_extend_of_Allowed (E0 : VC.Enumerations) (s : fin_seq) (q : ℕ) :
    VC.Sigma E0 s = 0 → VC.AllowedStepb E0 (VC.runState E0 s) q = true →
      VC.Sigma E0 (child s q) = 0 := by
  intro hs0 hAllowed
  have hsAd : VC.Admittedb E0 s = true := (VC.Sigma_eq_zero_iff E0 s).1 hs0

  let c : fin_seq := child s q
  have hSucc : s.len.succ ≤ c.len := by
    simp [c, child, fin_seq.extend, fin_seq.singleton]
  have hPred : s.len ≤ c.len := Nat.le_of_succ_le hSucc
  have hPref : Prefix s c := VC.Prefix_child s q

  have hEqAdm :
      VC.admittedAuxb E0 c s.len hPred
        = VC.admittedAuxb E0 s s.len le_rfl :=
    VC.admittedAuxb_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl

  have hsAux : VC.admittedAuxb E0 s s.len le_rfl = true := by
    simpa [VC.Admittedb] using hsAd
  have hcAux_pred : VC.admittedAuxb E0 c s.len hPred = true := by
    simpa [hEqAdm] using hsAux

  -- relate states at length s.len
  have hStateEq : VC.runStateAux E0 c s.len hPred = VC.runStateAux E0 s s.len le_rfl := by
    have hEq := VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl
    -- proof-irrelevance massage
    have hpi :
        VC.runStateAux E0 c s.len (Nat.le_trans le_rfl (VC.Prefix_len_le hPref))
          = VC.runStateAux E0 c s.len hPred := by
      exact VC.runStateAux_proof_irrel (E := E0) (s := c) s.len _ _
    simpa [hpi] using hEq

  have hDigit : c.seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ = q := by
    change (extend s (singleton q)).seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ = q
    exact VC.extend_singleton_last s q

  have hAllowedChild :
      VC.AllowedStepb E0 (VC.runStateAux E0 c s.len hPred)
        (c.seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩) = true := by
    simpa [VC.runState, hStateEq, hDigit] using hAllowed

  have hcAux_succ :
      VC.admittedAuxb E0 c s.len.succ (by
        simp [c, child, fin_seq.extend, fin_seq.singleton]) = true := by
    simp [VC.admittedAuxb, hcAux_pred, hAllowedChild]

  have hcAd : VC.Admittedb E0 c = true := by
    simpa [VC.Admittedb, c, child] using hcAux_succ
  exact (VC.Sigma_eq_zero_iff E0 c).2 hcAd

/-! ### The subfan law `T` -/

/-- Boolean test for the `k0`-case: the scheduled formula is already in `F(α↾(t+1))` or equals the distinguished context formula `W`. -/
def needs1b {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ) : Bool :=
  decide (VC.decK t = IPC.k0) &&
    (decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t+1))) ||
     decide (E.W (VC.decN t) = W))

/-- Recursive boolean check: among the first `k` positions, every place marked by `needs1b` carries digit `1`. -/
def StepsOKbUpTo {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (s : fin_seq) : (k : ℕ) → (hk : k ≤ s.len) → Bool
| 0, _ => true
| (k+1), hk =>
    let hk' : k ≤ s.len := Nat.le_of_succ_le hk
    let i  : Fin s.len := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    StepsOKbUpTo V a W s k hk' &&
      (if needs1b (V := V) (a := a) (W := W) k then
         decide (s.seq i = 1)
       else
         true)

/-- Full-length version of the previous check, i.e. the case `k = s.len`. -/
def StepsOKb {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) : Bool :=
  StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl

/-- Propositional version of `StepsOK`: simply the statement that the boolean test is `true`. -/
def StepsOK {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) : Prop :=
  StepsOKb (V := V) (a := a) (W := W) s = true

instance {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) :
    Decidable (StepsOK (V := V) (a := a) (W := W) s) :=
by
  -- Equality of booleans is constructively decidable.
  dsimp [StepsOK]
  infer_instance

def Tlaw {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) : fin_seq → ℕ :=
  fun s =>
    match V.S s with
    | 0   => if StepsOKb (V := V) (a := a) (W := W) s then 0 else 1
    | _+1 => 1

/-- Convenient unfolding lemma: `Tlaw = 0` iff `Σ = 0` and `StepsOKb = true`. -/
lemma Tlaw_eq_zero_iff {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) :
    Tlaw (V := V) (a := a) (W := W) s = 0
      ↔ (V.S s = 0 ∧ StepsOK (V := V) (a := a) (W := W) s) := by
  unfold Tlaw StepsOK StepsOKb
  cases hS : V.S s with
  | zero =>
      simp
  | succ n =>
      simp

lemma T_le_S {E : Enumerations} (V : VeldmanFan E) (a : Branch V) (W : Form) :
    ∀ s : fin_seq, Tlaw (E := E) V a W s = 0 → V.S s = 0 := by
  intro s hs
  exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := s)).1 hs |>.1

/-- If `UpTo (k+1) = true`, then `UpTo k = true`, since the recursive definition is `UpTo k && ...`. -/
lemma StepsOKbUpTo_pred_true {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (s : fin_seq) (k : ℕ) (hk : k.succ ≤ s.len) :
    StepsOKbUpTo (V := V) (a := a) (W := W) s k.succ hk = true →
    StepsOKbUpTo (V := V) (a := a) (W := W) s k (Nat.le_of_succ_le hk) = true := by
  intro h
  -- unfold one step and take the left conjunct
  have h' :
      StepsOKbUpTo (V := V) (a := a) (W := W) s k (Nat.le_of_succ_le hk) = true ∧
        (if needs1b (V := V) (a := a) (W := W) k then
            decide (s.seq ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ = 1)
         else true) = true := by
    simpa [StepsOKbUpTo] using h
  exact h'.1


lemma StepsOKbUpTo_proof_irrel {E : ESk}
    (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) :
    ∀ k (hk1 hk2 : k ≤ s.len),
      StepsOKbUpTo (V := V) (a := a) (W := W) s k hk1
        = StepsOKbUpTo (V := V) (a := a) (W := W) s k hk2 := by
  intro k
  induction k with
  | zero =>
      intro hk1 hk2
      rfl
  | succ k ih =>
      intro hk1 hk2
      have hrec := ih (Nat.le_of_succ_le hk1) (Nat.le_of_succ_le hk2)
      by_cases hneed : needs1b (V := V) (a := a) (W := W) k
      · simp [StepsOKbUpTo, hneed, hrec]
      · simp [StepsOKbUpTo, hneed, hrec]







/-- The first `k` checks for `child s q` agree with the first `k` checks for `s` whenever `k ≤ s.len`. -/
lemma child_len_ge (s : fin_seq) (q : ℕ) : s.len ≤ (child s q).len := by
  change s.len ≤ s.len + 1
  exact Nat.le_succ s.len

lemma StepsOKbUpTo_child_eq {E : ESk}
    (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (s : fin_seq) (q : ℕ) :
    ∀ k (hk : k ≤ s.len),
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q) k
          (Nat.le_trans hk (child_len_ge s q))
      =
      StepsOKbUpTo (V := V) (a := a) (W := W) s k hk := by
  intro k hk
  induction k with
  | zero =>
      simp [StepsOKbUpTo]
  | succ k ih =>
      have hk' : k ≤ s.len := Nat.le_of_succ_le hk
      have hkChild : k.succ ≤ (child s q).len := Nat.le_trans hk (child_len_ge s q)
      have hkChild' : k ≤ (child s q).len := Nat.le_of_succ_le hkChild

      -- Here we use that when `k < s.len`, the `k`-th entry of `child.seq` is exactly the `k`-th entry of `s.seq`.
      have hlt : k < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hltChild : k < (child s q).len := Nat.lt_of_lt_of_le hlt (child_len_ge s q)

      let iS : Fin s.len := ⟨k, hlt⟩
      let iC : Fin (child s q).len := ⟨k, hltChild⟩

      have hseq : (child s q).seq iC = s.seq iS := by
        -- Since `k < s.len`, the `extend` operation reads from the old prefix `s` at this position.
        simp [child, fin_seq.extend, fin_seq.singleton, hlt, iS, iC]

      -- Unfold the successor clause of `StepsOKbUpTo`; on both sides we get `recursive && (if needs1b k then decide(seq=1) else true)`.
      simp [StepsOKbUpTo, ih hk', hseq, iS, iC]

/-- The main prefix-transfer lemma: if the full `StepsOKbUpTo` check holds for `child s q`, then it already holds for `s`. -/
lemma StepsOKbUpTo_prefix_child {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (s : fin_seq) (q : ℕ) :
    StepsOKbUpTo (V := V) (a := a) (W := W) (child s q)
        (child s q).len le_rfl = true →
    StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl = true := by
  intro h
  -- First simplify `child.len` to `s.len.succ`.
  have hlen : (child s q).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  -- Rewrite `h` into the `UpTo (s.len.succ)` form.
  have h' :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q)
        s.len.succ (by simp [hlen]) = true := by
    simpa [hlen] using h
  -- Drop the last position and obtain the `UpTo s.len` statement.
  have hdown :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q)
        s.len (Nat.le_of_succ_le (by simp [hlen] )) = true := by
    -- Use the predecessor lemma above.
    exact StepsOKbUpTo_pred_true (V := V) (a := a) (W := W) (s := child s q)
        (k := s.len) (hk := by simp [hlen] ) h'

  -- Rewrite `child`'s `UpTo s.len` check back to the one for `s`.
  have heq :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q)
        s.len (Nat.le_trans (le_rfl : s.len ≤ s.len) (child_len_ge s q))
      =
      StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl :=
    StepsOKbUpTo_child_eq (V := V) (a := a) (W := W) (s := s) (q := q) s.len le_rfl

  -- The two `hk` proofs need not be definitionally equal; rewrite the target side using `heq`.
  -- Finish the proof with `simpa [heq]`.
  simpa [heq] using hdown

/-- Extend `StepsOK` from `s` to `child s q`; the final coordinate is forced to be `1` by `hnew`. -/
lemma StepsOK_child_of_StepsOK {E : ESk}
    (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (s : fin_seq) (q : ℕ)
    (hS : StepsOK (V := V) (a := a) (W := W) s)
    (hnew : needs1b (V := V) (a := a) (W := W) s.len = true → q = 1) :
    StepsOK (V := V) (a := a) (W := W) (child s q) := by
  -- Unfold `StepsOK` and `StepsOKb`.
  unfold StepsOK at hS ⊢
  unfold StepsOKb at hS ⊢

  -- Since `child.len = s.len + 1`, `StepsOKb(child)` is the `StepsOKbUpTo(child) (s.len+1)` instance.
  have hlen : (child s q).len = s.len + 1 := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hkfull : s.len.succ ≤ (child s q).len := by
    rw [hlen]

  have hPrefixEq :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q) s.len
          (Nat.le_of_succ_le hkfull)
      =
      StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl :=
    calc
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q) s.len
          (Nat.le_of_succ_le hkfull)
          = StepsOKbUpTo (V := V) (a := a) (W := W) (child s q) s.len
              (Nat.le_trans le_rfl (child_len_ge s q)) :=
            StepsOKbUpTo_proof_irrel (V := V) (a := a) (W := W) (s := child s q) s.len _ _
      _ = StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl :=
            StepsOKbUpTo_child_eq (V := V) (a := a) (W := W) (s := s) (q := q) s.len le_rfl

  have hPrefixTrue :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q) s.len
          (Nat.le_of_succ_le hkfull) = true := by
    rw [hPrefixEq]
    exact hS

  by_cases hb : needs1b (V := V) (a := a) (W := W) s.len
  · -- hb : needs1b ... s.len = true
    have hq : q = 1 := hnew hb
    subst hq
    have hLast : (child s 1).seq
        ⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hkfull⟩ = 1 := by
      have hidx :
          (⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hkfull⟩ : Fin (child s 1).len)
            = ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ := by
        apply Fin.ext
        rfl
      calc
        (child s 1).seq ⟨s.len, Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hkfull⟩
            = (child s 1).seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ := by rw [hidx]
        _ = 1 := by
            change (extend s (singleton 1)).seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ = 1
            exact VC.extend_singleton_last s 1
    have hmain :
        StepsOKbUpTo (V := V) (a := a) (W := W) (child s 1) s.len.succ hkfull = true := by
      simp [StepsOKbUpTo, hb, hPrefixTrue, hLast]
    simpa [hlen] using hmain
  · -- hb : needs1b ... s.len = false
    have hmain :
        StepsOKbUpTo (V := V) (a := a) (W := W) (child s q) s.len.succ hkfull = true := by
      simp [StepsOKbUpTo, hb, hPrefixTrue]
    simpa [hlen] using hmain

lemma StepsOK_empty {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) :
    StepsOK (E := E) V a W empty_seq := by
  -- StepsOK = (StepsOKb = true)
  dsimp [StepsOK, StepsOKb]
  -- The goal becomes `StepsOKbUpTo ... empty_seq empty_seq.len le_rfl = true`.

  -- Key simplification: rewrite `empty_seq.len` to `0`.
  have hlen : empty_seq.len = 0 := by
    -- This is usually enough; if `empty_seq` lives in a different namespace in your setup,
    -- replace `[empty_seq]` by the actual name used in your development.
    simp [empty_seq]

  -- After rewriting with `hlen`, the `0`-case of `StepsOKbUpTo` is exactly `true`.
  simp [hlen, StepsOKbUpTo]

lemma needs1b_k0_of_true {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ) :
    needs1b (V := V) (a := a) (W := W) t = true → VC.decK t = IPC.k0 := by
  intro h
  unfold needs1b at h
  -- needs1b = decide(k=k0) && (...)
  have h1 : decide (VC.decK t = IPC.k0) = true :=
    by exact Bool.and_elim_left h
  exact (_root_.decide_eq_true_iff).1 h1

lemma AllowedStepb_k0_one (E0 : VC.Enumerations) (st : VC.State) :
    VC.decK st.t = IPC.k0 → VC.AllowedStepb E0 st 1 = true := by
  intro hk0
  -- Unfold `AllowedStepb`: in the `k0` branch we get either `decide (1 = 1)` or `decide (1 = 0 ∨ 1 = 1)`, both equal to `true`.
  unfold VC.AllowedStepb
  simp [hk0]

/-! ### `Tlaw` is a fan law -/

theorem Tlaw_is_fan_law {E : Enumerations} (V : VeldmanFan E) (a : Branch V) (W : Form)(hV : V = Vconcrete E) :
    is_fan_law (Tlaw (E := E) V a W) := by
  refine And.intro ?spread ?bound
  · -- spread law
    refine And.intro ?empty ?ext
    · -- empty admitted
      have hS0 : V.S empty_seq = 0 := Sigma_empty (V := V)
      have hOK : StepsOK (E := E) V a W empty_seq := StepsOK_empty (V := V) (a := a) (W := W)
      exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := empty_seq)).2 ⟨hS0, hOK⟩
    · intro s
      constructor
      · intro hs0
        have hSs : V.S s = 0 := (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := s)).1 hs0 |>.1
        have hOKs : StepsOK (E := E) V a W s := (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := s)).1 hs0 |>.2
        -- pick a witness digit
        let q : ℕ :=
          if h : needs1b (E := E) V a W s.len then 1
          else VC.chooseNext (toConcreteEnum E) (VC.runState (toConcreteEnum E) s)
        let E0 : VC.Enumerations := toConcreteEnum E
        let st : VC.State := VC.runState E0 s
        have ht : st.t = s.len := by
    -- This is exactly the already proved fact `runState_t : (VC.runState E0 s).t = s.len`.
          simpa [st] using runState_t (E0 := E0) (s := s)

        have hAllowed : VC.AllowedStepb E0 st q = true := by
          by_cases hneed : needs1b (V := V) (a := a) (W := W) s.len = true
          · -- q = 1
            have hq : q = 1 := by simp [q, hneed]

            have hk0s : VC.decK s.len = IPC.k0 :=
              needs1b_k0_of_true (V := V) (a := a) (W := W) (t := s.len) hneed
            have hk0t : VC.decK st.t = IPC.k0 := by simpa [ht] using hk0s
            rw[hq]
            exact AllowedStepb_k0_one (E0 := E0) (st := st) hk0t
          · -- q = chooseNext
            have hq : q = VC.chooseNext E0 st := by simp [q, hneed, E0, st]
      -- Allowed_chooseNext : AllowedStepb E0 st (chooseNext E0 st) = true
            simpa [hq] using VC.Allowed_chooseNext E0 st

        have hSsSigma : VC.Sigma E0 s = 0 := by
          cases hV
    -- Because `V.S = Sigma E0` by the definition of `Vconcrete`.
          simpa [Vconcrete, E0] using hSs

        have hSigmaChildSigma : VC.Sigma E0 (child s q) = 0 :=
    Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := q) hSsSigma (by simpa [st] using hAllowed)

        have hSigmaChild : V.S (child s q) = 0 := by
          cases hV
          simpa [Vconcrete, E0] using hSigmaChildSigma

        have hnew : needs1b (E := E) V a W s.len → q = 1 := by
          intro hneed
          simp [q, hneed]

        have hOKchild : StepsOK (E := E) V a W (child s q) :=
          StepsOK_child_of_StepsOK (V := V) (a := a) (W := W) (s := s) (q := q) hOKs hnew

        have hTchild : Tlaw (E := E) V a W (child s q) = 0 :=
          (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s q)).2 ⟨hSigmaChild, hOKchild⟩

        exact ⟨q, hTchild⟩

      · rintro ⟨q, hq0⟩
        have hSChild : V.S (child s q) = 0 := (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s q)).1 hq0 |>.1
        have hSs : V.S s = 0 := by
          -- since Σ is a spread law, existence of an admitted child implies the parent is admitted
          have hspread : is_spread_law V.S := (fan_law_is_spread_law V.S V.hS)
          have : V.S s = 0 := (hspread.2 s).2 ⟨q, hSChild⟩
          exact this
        have hOKs : StepsOK (E := E) V a W s :=
          StepsOKbUpTo_prefix_child (V := V) (a := a) (W := W) (s := s) (q := q)
            ((Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s q)).1 hq0 |>.2)
        exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := s)).2 ⟨hSs, hOKs⟩

  · -- branching bound
    intro s hs0
    have hSs : V.S s = 0 := (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := s)).1 hs0 |>.1
    -- reuse the bound from the ambient fan V.S
    rcases (V.hS.2 s hSs) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro m hm0
    have hmS : V.S (child s m) = 0 := (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s m)).1 hm0 |>.1
    exact hn m hmS

/-! ### `Forced0b = true` yields a derivability proof from the current `Fs` -/

lemma Forced0b_witness (E0 : VC.Enumerations) (st : VC.State) :
    VC.Forced0b E0 st = true →
      ∃ i : ℕ, i ≤ st.t ∧
        ((E0.d i).2 = E0.W (VC.decN st.t) ∧ (E0.d i).1 ⊆ st.Fs) := by

  intro h
  unfold VC.Forced0b at h
  by_cases hk0 : VC.decK st.t = IPC.k0
  · simp [hk0] at h
    rcases (Finset.anyUpTo_eq_true (t := st.t) (p := fun i =>
        decide ((E0.d i).2 = E0.W (VC.decN st.t)) &&
        decide ((E0.d i).1 ⊆ st.Fs)
      )).1 h with
      ⟨i, hi, hpi⟩

    -- Split the conjunction `&& = true` into its two boolean components.
    have hsplit :
        decide ((E0.d i).2 = E0.W (VC.decN st.t)) = true ∧
        decide ((E0.d i).1 ⊆ st.Fs) = true :=
      by exact Bool.and_eq_true_iff.mp hpi

    have hEq : (E0.d i).2 = E0.W (VC.decN st.t) :=
      (_root_.decide_eq_true_iff).1 hsplit.1

    have hSub : (E0.d i).1 ⊆ st.Fs :=
      (_root_.decide_eq_true_iff).1 hsplit.2

    exact ⟨i, hi, ⟨hEq, hSub⟩⟩
  · -- If `hk0` is false, then `Forced0b = false`, so this branch is impossible.
    simp [hk0] at h

lemma Forced0b_prf (E0 : VC.Enumerations) (st : VC.State) :
    VC.Forced0b E0 st = true →
      ((↑st.Fs : Set Form) ⊢ᵢ (E0.W (VC.decN st.t))) := by
  intro hF
  rcases Forced0b_witness (E0 := E0) (st := st) hF with ⟨i, _hi, hEq, hsub⟩
  have hDer : ((↑(E0.d i).1 : Set Form) ⊢ᵢ (E0.d i).2) := (E0.d_sound i)
  have hDer' : ((↑st.Fs : Set Form) ⊢ᵢ (E0.d i).2) := by
    apply IPC.prf.sub_weak (Δ := (↑(E0.d i).1 : Set Form)) (Γ := (↑st.Fs : Set Form)) (p := (E0.d i).2)
    · exact hDer
    · intro p hp
      exact hsub hp
  simpa [hEq] using hDer'

/-! ### `runState` on a child prefix is one `step` from the parent state -/

lemma runState_child (E0 : VC.Enumerations) (s : fin_seq) (q : ℕ) :
    VC.runState E0 (child s q) = VC.step E0 (VC.runState E0 s) q := by
  have hlen : (child s q).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton, Nat.succ_eq_add_one]
  have hle : s.len ≤ (child s q).len := child_len_ge s q
  have hkfull : s.len.succ ≤ (child s q).len := by
    rw [hlen]

  have hPref : Prefix s (child s q) := VC.Prefix_child s q
  have hEqPrefix :
      VC.runStateAux E0 (child s q) s.len (Nat.le_trans le_rfl (VC.Prefix_len_le hPref))
        = VC.runStateAux E0 s s.len le_rfl :=
    VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl

  have hEq :
      VC.runStateAux E0 (child s q) s.len hle = VC.runStateAux E0 s s.len le_rfl := by
    calc
      VC.runStateAux E0 (child s q) s.len hle
          = VC.runStateAux E0 (child s q) s.len (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
              symm
              exact VC.runStateAux_proof_irrel (E := E0) (s := child s q) s.len _ _
      _ = VC.runStateAux E0 s s.len le_rfl := hEqPrefix

  have hDigit :
      (child s q).seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ = q := by
    change (extend s (singleton q)).seq ⟨s.len, Nat.lt_add_of_pos_right (Nat.succ_pos 0)⟩ = q
    exact VC.extend_singleton_last s q

  have hpi :
      VC.runStateAux E0 (child s q) s.len (Nat.le_of_succ_le hkfull)
        = VC.runStateAux E0 (child s q) s.len hle := by
    exact VC.runStateAux_proof_irrel (E := E0) (s := child s q) s.len _ _

  have hle_simp : s.len ≤ (child s q).len := by
    simp[hlen]

  have hSt : VC.runStateAux E0 (child s q) s.len hle_simp = VC.runState E0 s := by
    calc
      VC.runStateAux E0 (child s q) s.len hle_simp
          = VC.runStateAux E0 (child s q) s.len hle := by
              exact VC.runStateAux_proof_irrel (E := E0) (s := child s q) s.len _ _
      _ = VC.runStateAux E0 s s.len le_rfl := hEq
      _ = VC.runState E0 s := by
            rw [VC.runState]

  change VC.runStateAux E0 (child s q) (child s q).len le_rfl = VC.step E0 (VC.runState E0 s) q
  have hStep :
      VC.runStateAux E0 (child s q) (child s q).len le_rfl
        = VC.step E0 (VC.runStateAux E0 (child s q) s.len hle_simp) q := by
    simp [child, fin_seq.extend, fin_seq.singleton, VC.runStateAux, VC.step]
  calc
    VC.runStateAux E0 (child s q) (child s q).len le_rfl
        = VC.step E0 (VC.runStateAux E0 (child s q) s.len hle_simp) q := hStep
    _ = VC.step E0 (VC.runState E0 s) q := by
          rw [hSt]

/-! ### Subfan property (paper 4.1(i) in propositional form): Γα ⊆ Γβ and W ∈ Γβ -/



/-- Prefix relation between two finitize prefixes of the same infinite sequence. -/
lemma Prefix_finitize (α : NatSeq) {n m : ℕ} (h : n ≤ m) :
    Prefix (finitize α n) (finitize α m) := by
  refine ⟨h, ?_⟩
  intro i
  rfl

/-- A simple lower bound: the scheduling time `schedEncode ⟨n, m, k0⟩` is at least `m`. -/

lemma le_pairEncodeBin_right (n m : ℕ) : m ≤ IPC.pairEncodeBin n m := by
  induction n with
  | zero =>
      simpa [IPC.pairEncodeBin, Nat.bit, Nat.mul_comm] using
        (Nat.le_mul_of_pos_left m (by decide : 0 < 2))
  | succ n ih =>
      have hstep : IPC.pairEncodeBin n m ≤ IPC.pairEncodeBin (n + 1) m := by
        calc
          IPC.pairEncodeBin n m ≤ 2 * IPC.pairEncodeBin n m := by
            simpa [Nat.mul_comm] using
              (Nat.le_mul_of_pos_left (IPC.pairEncodeBin n m) (by decide : 0 < 2))
          _ ≤ 2 * IPC.pairEncodeBin n m + 1 := Nat.le_succ _
          _ = IPC.pairEncodeBin (n + 1) m := by simp [IPC.pairEncodeBin, Nat.bit]
      exact Nat.le_trans ih hstep

lemma le_schedEncode_k0 (n m : ℕ) : m ≤ IPC.schedEncode ⟨n, m, IPC.k0⟩ := by
  have hm : m ≤ IPC.pairEncodeBin n m := le_pairEncodeBin_right n m
  have hmul : IPC.pairEncodeBin n m ≤ 3 * IPC.pairEncodeBin n m := by
    simpa [Nat.mul_comm] using
      (Nat.le_mul_of_pos_left (IPC.pairEncodeBin n m) (by decide : 0 < 3))
  have : m ≤ 3 * IPC.pairEncodeBin n m := Nat.le_trans hm hmul
  simpa [IPC.schedEncode, IPC.schedEncodeBin, IPC.k0] using this

lemma Prefix_finitize_le (x : 𝒩) {m n : ℕ} (h : m ≤ n) :
    Prefix (finitize x m) (finitize x n) := by
  refine ⟨h, ?_⟩
  intro i
  -- Both sides evaluate to `x i.val`.
  rfl
lemma needs1b_true_of_k0_mem
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ)
    (hk0 : VC.decK t = IPC.k0)
    (hmem : E.W (VC.decN t) ∈ V.F (finitize a.1 (t+1))) :
    needs1b (V := V) (a := a) (W := W) t = true := by
  unfold needs1b
  -- Expand the boolean test into `decide(...) && (decide(mem) || decide(eq))`.
  have hk0' : decide (VC.decK t = IPC.k0) = true :=
    (_root_.decide_eq_true_iff).2 hk0
  have hmem' : decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t+1))) = true :=
    (_root_.decide_eq_true_iff).2 hmem
  -- The left conjunct is true, and the left side of the right-hand disjunction is true, so the whole expression is true.
  simp [hk0', hmem']

lemma StepsOK_finitize_digit_eq_one
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (bseq : 𝒩) (t : ℕ)
    (hSteps : StepsOK (V := V) (a := a) (W := W) (finitize bseq (t+1)))
    (hneed : needs1b (V := V) (a := a) (W := W) t = true) :
    bseq t = 1 := by
  unfold StepsOK at hSteps
  unfold StepsOKb at hSteps

  have hLayer :
      StepsOKbUpTo (V := V) (a := a) (W := W) (finitize bseq (t+1)) (t+1) le_rfl = true := hSteps

  have hAnd :
      StepsOKbUpTo (V := V) (a := a) (W := W) (finitize bseq (t+1)) t (Nat.le_of_succ_le le_rfl)
        &&
      (if needs1b (V := V) (a := a) (W := W) t then
          decide ((finitize bseq (t+1)).seq ⟨t, Nat.lt_succ_self t⟩ = 1)
       else true)
      = true := by
    simpa [StepsOKbUpTo] using hLayer

  have hDec :
      decide ((finitize bseq (t+1)).seq ⟨t, Nat.lt_succ_self t⟩ = 1) = true := by
    simpa [hneed] using (Bool.and_eq_true_iff.mp hAnd).2

  have hEq :
      (finitize bseq (t+1)).seq ⟨t, Nat.lt_succ_self t⟩ = 1 :=
    (_root_.decide_eq_true_iff).1 hDec

  change bseq t = 1 at hEq
  exact hEq

/-- `finitize b (t+1)` is obtained from `finitize b t` by extending with the final digit `b t`. -/
lemma finitize_succ_eq_child (bseq : 𝒩) (t : ℕ) :
    finitize bseq (t+1) = child (finitize bseq t) (bseq t) := by
  change
    fin_seq.mk (t + 1) (fun i : Fin (t + 1) => bseq i.val)
      =
    fin_seq.mk (t + 1) (fun i : Fin (t + 1) =>
      if h : i.val < t then bseq i.val else bseq t)
  apply congrArg (fun f => fin_seq.mk (t + 1) f)
  funext i
  by_cases hi : i.val < t
  · simp [hi]
  · have hi_eq : i.val = t := by
      have hi_lt : i.val < t + 1 := i.isLt
      omega
    simp [ hi_eq]

/-- From `StepsOK` in boolean form together with `needs1b = true`, conclude that the digit at time `t0` is `1`. -/
lemma digit_one_of_StepsOK_of_needs1b
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (bseq : 𝒩) (t0 : ℕ)
    (hSteps : StepsOK (V := V) (a := a) (W := W) (finitize bseq (t0 + 1)))
    (hneed : needs1b (V := V) (a := a) (W := W) t0 = true) :
    (finitize bseq (t0 + 1)).seq ⟨t0, Nat.lt_succ_self t0⟩ = 1 := by
  have hnat : bseq t0 = 1 :=
    StepsOK_finitize_digit_eq_one
      (V := V) (a := a) (W := W) (bseq := bseq) (t := t0) hSteps hneed
  simpa [fin_seq.finitize] using hnat

/-
Paper: Lemma 2.3 (constructive version)

Given a branch `b` of the subfan `T` (defined below), we construct a branch of the original fan
(with the same underlying infinite sequence), and prove:
1) `Γ_a ⊆ Γ_b`, and
2) `W ∈ Γ_b`.

Key change vs. the previous nonconstructive attempt:
`needs1` is decidable because it only looks at the *finite* set `F(prefix a t)` (not `Γ_a`),
so `T` can be defined without nonconstructive axioms.
-/
lemma subfan_ok
    {E : Enumerations} (V : VeldmanFan E)
    (a : Branch V) (W : Form)
    (hV : V = Vconcrete E)
    (T : fin_seq -> Nat) (hTdef : T = Tlaw (E := E) V a W)
    (hT : is_fan_law T)
    (b : fan T hT) :
    And
      (Set.Subset (Gamma V a)
        (Gamma V
          (toBranchOfSubfan V hT (fun s hs => by
              subst hV
              subst hTdef
              exact T_le_S (V := Vconcrete E) (a := a) (W := W) (s := s) hs) b)))
      ((Gamma V
          (toBranchOfSubfan V hT (fun s hs => by
              subst hV
              subst hTdef
              exact T_le_S (V := Vconcrete E) (a := a) (W := W) (s := s) hs) b)) W) := by
  subst hV
  subst hTdef
  let V : VeldmanFan E := Vconcrete E
  let T : fin_seq -> Nat := Tlaw (E := E) V a W
  let beta : Branch V := toBranchOfSubfan V hT (T_le_S (V := V) (a := a) (W := W)) b
  have hbSeq : beta.1 = b.1 := rfl

  have hmem_child_k0_one :
      forall {n : Nat} {s : fin_seq},
        VC.decK s.len = IPC.k0 ->
        VC.decN s.len = n ->
        E.W n ∈ V.F (child s 1) := by
    intro n s hk0s hdecNs
    let E0 : VC.Enumerations := toConcreteEnum E
    have hlen : (child s 1).len = s.len.succ := by
      simp [child, fin_seq.extend, fin_seq.singleton, Nat.succ_eq_add_one]
    have hSucc : s.len.succ <= (child s 1).len := by
      simp[hlen]
    have hPred : s.len <= (child s 1).len := Nat.le_of_succ_le hSucc
    have hPref : Prefix s (child s 1) := VC.Prefix_child s 1
    have hEqPrefix :
        VC.runStateAux E0 (child s 1) s.len hPred = VC.runState E0 s := by
      calc
        VC.runStateAux E0 (child s 1) s.len hPred
            = VC.runStateAux E0 (child s 1) s.len
                (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
                  exact VC.runStateAux_proof_irrel (E := E0) (s := child s 1) s.len _ _
        _ = VC.runStateAux E0 s s.len le_rfl :=
              VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl
        _ = VC.runState E0 s := by
              rw [VC.runState]
    have htPrefix :
        (VC.runStateAux E0 (child s 1) s.len hPred).t = s.len := by
      calc
        (VC.runStateAux E0 (child s 1) s.len hPred).t
            = (VC.runState E0 s).t := by
                simpa using congrArg (fun st => st.t) hEqPrefix
        _ = s.len := by
              simpa using runState_t (E0 := E0) (s := s)
    have hk0Prefix : VC.decK (VC.runStateAux E0 (child s 1) s.len hPred).t = IPC.k0 := by
      simpa [htPrefix] using hk0s
    have hdecNPrefix : VC.decN (VC.runStateAux E0 (child s 1) s.len hPred).t = n := by
      simpa [htPrefix] using hdecNs
    have hFsPrefix :
        (VC.runStateAux E0 (child s 1) s.len hPred).Fs = (VC.runState E0 s).Fs := by
      simpa using congrArg (fun st => st.Fs) hEqPrefix
    have hpi :
        VC.runStateAux E0 (child s 1) s.len (Nat.le_of_succ_le hSucc)
          = VC.runStateAux E0 (child s 1) s.len hPred := by
      exact VC.runStateAux_proof_irrel (E := E0) (s := child s 1) s.len _ _
    have hDigit :
        (child s 1).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)) = 1 := by
      simp [child, fin_seq.extend, fin_seq.singleton]
    have hFsChild :
        (VC.runState E0 (child s 1)).Fs = insert (E.W n) (VC.runState E0 s).Fs := by
      change
        (VC.step E0
          (VC.runStateAux E0 (child s 1) s.len (Nat.le_of_succ_le hSucc))
          ((child s 1).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)))).Fs
            = insert (E.W n) (VC.runState E0 s).Fs
      rw [hpi, hDigit]
      change VC.FStep E0 (VC.runStateAux E0 (child s 1) s.len hPred) 1 = _
      unfold VC.FStep
      dsimp
      rw [if_pos hk0Prefix]
      rw [hdecNPrefix, hFsPrefix]
      simp [E0, toConcreteEnum]
    have hmem : E.W n ∈ (VC.runState E0 (child s 1)).Fs := by
      rw [hFsChild]
      exact Finset.mem_insert_self _ _
    simpa [V, Vconcrete, VC.FS, E0] using hmem

  constructor
  case left =>
    intro p hp
    cases hp with
    | intro nA hpA =>
        cases E.W_surj p with
        | intro n0 hn0 =>
            let t0 : Nat := IPC.schedEncode (n0, nA, IPC.k0)
            have hk0 : VC.decK t0 = IPC.k0 := by
              simp [t0, VC.decK, IPC.schedDecode_encode]
            have hdecN : VC.decN t0 = n0 := by
              simp [t0, VC.decN, IPC.schedDecode_encode]
            have hle : nA <= t0 := le_schedEncode_k0 n0 nA
            have hPref : Prefix (finitize a.1 nA) (finitize a.1 t0) := Prefix_finitize a.1 hle
            have hmemA : E.W n0 ∈ V.F (finitize a.1 t0) := by
              exact (V.F_mono hPref (a.2 nA) (a.2 t0)) (by simpa [hn0] using hpA)
            have hPref01 : Prefix (finitize a.1 t0) (finitize a.1 (t0 + 1)) :=
              Prefix_finitize_le a.1 (Nat.le_succ t0)
            have hmemA1 : E.W n0 ∈ V.F (finitize a.1 (t0 + 1)) := by
              exact (V.F_mono hPref01 (a.2 t0) (a.2 (t0 + 1))) hmemA
            have hneed : needs1b (V := V) (a := a) (W := W) t0 = true :=
              needs1b_true_of_k0_mem (V := V) (a := a) (W := W) (t := t0) hk0
                (by simpa [hdecN] using hmemA1)
            have hb0 : T (finitize b.1 (t0 + 1)) = 0 := b.2 (t0 + 1)
            have hbSteps : StepsOK (V := V) (a := a) (W := W) (finitize b.1 (t0 + 1)) :=
              (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := finitize b.1 (t0 + 1))).1 hb0 |>.2
            have hbDigit : b.1 t0 = 1 :=
              StepsOK_finitize_digit_eq_one (V := V) (a := a) (W := W)
                (bseq := b.1) (t := t0) hbSteps hneed
            let s0 : fin_seq := finitize b.1 t0
            have hs0 : finitize b.1 (t0 + 1) = child s0 1 := by
              have hchild : finitize b.1 (t0 + 1) = child (finitize b.1 t0) (b.1 t0) :=
                finitize_succ_eq_child (bseq := b.1) (t := t0)
              simpa [s0, hbDigit] using hchild
            have hk0s0 : VC.decK s0.len = IPC.k0 := by
              simpa [s0, fin_seq.finitize_len] using hk0
            have hdecNs0 : VC.decN s0.len = n0 := by
              simpa [s0, fin_seq.finitize_len] using hdecN
            have hmemChild : E.W n0 ∈ V.F (child s0 1) :=
              hmem_child_k0_one (s := s0) hk0s0 hdecNs0
            have hmemB : E.W n0 ∈ V.F (finitize b.1 (t0 + 1)) := by
              rw [hs0]
              exact hmemChild
            exact Exists.intro (t0 + 1) (by simpa [hbSeq, hn0] using hmemB)

  case right =>
    cases E.W_surj W with
    | intro n0 hn0 =>
        let t0 : Nat := IPC.schedEncode (n0, 0, IPC.k0)
        have hk0 : VC.decK t0 = IPC.k0 := by
          simp [t0, VC.decK, IPC.schedDecode_encode]
        have hdecN : VC.decN t0 = n0 := by
          simp [t0, VC.decN, IPC.schedDecode_encode]
        have hneedW : needs1b (E := E) V a (E.W n0) t0 = true := by
          unfold needs1b
          have hk0d : decide (VC.decK t0 = IPC.k0) = true := by
            exact (_root_.decide_eq_true_iff).2 hk0
          have heqd : decide (E.W (VC.decN t0) = E.W n0) = true := by
            have hEq : E.W (VC.decN t0) = E.W n0 := by
              simp [hdecN]
            exact (_root_.decide_eq_true_iff).2 hEq
          simp [hk0d, heqd]
        have hb0 : T (finitize b.1 (t0 + 1)) = 0 := b.2 (t0 + 1)
        have hbSteps : StepsOK (V := V) (a := a) (W := E.W n0) (finitize b.1 (t0 + 1)) :=
          (Tlaw_eq_zero_iff (V := V) (a := a) (W := E.W n0) (s := finitize b.1 (t0 + 1))).1
            (by simpa [hn0] using hb0) |>.2
        let bseq : NatSeq := b.1
        have hbDigitNat : bseq t0 = 1 := by
          exact StepsOK_finitize_digit_eq_one
            (V := V) (a := a) (W := E.W n0) (bseq := bseq) (t := t0)
            (by simpa [bseq] using hbSteps) hneedW
        let s0 : fin_seq := finitize b.1 t0
        have hs0 : finitize bseq (t0 + 1) = child s0 1 := by
          have hchild : finitize bseq (t0 + 1) = child (finitize bseq t0) (bseq t0) :=
            finitize_succ_eq_child bseq t0
          simpa [s0, hbDigitNat] using hchild
        have hk0s0 : VC.decK s0.len = IPC.k0 := by
          simpa [s0, fin_seq.finitize_len] using hk0
        have hdecNs0 : VC.decN s0.len = n0 := by
          simpa [s0, fin_seq.finitize_len] using hdecN
        have hmemChild : E.W n0 ∈ V.F (child s0 1) :=
          hmem_child_k0_one (s := s0) hk0s0 hdecNs0
        have hmemB : E.W n0 ∈ V.F (finitize b.1 (t0 + 1)) := by
          change E.W n0 ∈ V.F (finitize bseq (t0 + 1))
          rw [hs0]
          exact hmemChild
        exact Exists.intro (t0 + 1) (by simpa [hbSeq, hn0] using hmemB)


namespace StepRules

open GammaRules

lemma AllowedStepb_k0_allow_0_1 (E0 : VC.Enumerations) (st : VC.State) :
    VC.decK st.t = IPC.k0 → VC.Forced0b E0 st = false →
      VC.AllowedStepb E0 st 0 = true ∧ VC.AllowedStepb E0 st 1 = true := by
  intro hk0 hF
  unfold VC.AllowedStepb
  simp [hk0, hF]

lemma AllowedStepb_k0_force_only_1 (E0 : VC.Enumerations) (st : VC.State) :
    VC.decK st.t = IPC.k0 → VC.Forced0b E0 st = true →
      (VC.AllowedStepb E0 st 1 = true) := by
  intro hk0 hF
  unfold VC.AllowedStepb
  simp [hk0, hF]

lemma AllowedStepb_k1_only_0 (E0 : VC.Enumerations) (st : VC.State) :
    VC.decK st.t = IPC.k1 → VC.AllowedStepb E0 st 0 = true := by
  intro hk1
  unfold VC.AllowedStepb
  have hk10 : (IPC.k1 : Fin 3) ≠ IPC.k0 := by decide
  simp [hk1, hk10]

lemma AllowedStepb_k2_default_0 (E0 : VC.Enumerations) (st : VC.State)
    (hNoSplit : ¬ (∃ A B : Form, E0.W (VC.decN st.t) = A ⋎ B ∧ st.prev2 = 1)) :
    VC.decK st.t = IPC.k2 → VC.AllowedStepb E0 st 0 = true := by
  intro hk2
  unfold VC.AllowedStepb
  have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
  have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
  cases hcase : E0.W (VC.decN st.t) with
  | or A B =>
      by_cases hp : st.prev2 = 1
      · -- The split case is excluded by `hNoSplit`.
        exfalso
        exact hNoSplit ⟨A, B, hcase, hp⟩
      · -- not split: only q=0 allowed, so q=0 is allowed
        simp [hk2, hk20, hk21, hcase, hp]
  | atom n =>
      simp [hk2, hk20, hk21, hcase]
  | bot =>
      simp [hk2, hk20, hk21, hcase]
  | imp P Q =>
      simp [hk2, hk20, hk21, hcase]
  | and P Q =>
      simp [hk2, hk20, hk21, hcase]

lemma FS_child_k0_one
    (E : Enumerations) (s : fin_seq)
    (hk0 : VC.decK s.len = IPC.k0) :
    VC.FS (toConcreteEnum E) (child s 1)
      =
    insert (E.W (VC.decN s.len)) (VC.FS (toConcreteEnum E) s) := by

  let E0 : VC.Enumerations := toConcreteEnum E
  have hlen : (child s 1).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton, Nat.succ_eq_add_one]
  have hSucc : s.len.succ <= (child s 1).len := by
    simp[hlen]
  have hPred : s.len <= (child s 1).len := Nat.le_of_succ_le hSucc
  have hPref : Prefix s (child s 1) := VC.Prefix_child s 1
  have hEqPrefix :
      VC.runStateAux E0 (child s 1) s.len hPred = VC.runState E0 s := by
    calc
      VC.runStateAux E0 (child s 1) s.len hPred
          = VC.runStateAux E0 (child s 1) s.len
              (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
                exact VC.runStateAux_proof_irrel (E := E0) (s := child s 1) s.len _ _
      _ = VC.runStateAux E0 s s.len le_rfl :=
            VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl
      _ = VC.runState E0 s := by
            rw [VC.runState]
  have htPrefix :
      (VC.runStateAux E0 (child s 1) s.len hPred).t = s.len := by
    calc
      (VC.runStateAux E0 (child s 1) s.len hPred).t
          = (VC.runState E0 s).t := by
              simpa using congrArg (fun st => st.t) hEqPrefix
      _ = s.len := by
            simpa using runState_t (E0 := E0) (s := s)
  have hk0Prefix : VC.decK (VC.runStateAux E0 (child s 1) s.len hPred).t = IPC.k0 := by
    simpa [htPrefix] using hk0
  have hdecNPrefix : VC.decN (VC.runStateAux E0 (child s 1) s.len hPred).t = VC.decN s.len := by
    simp [htPrefix]
  have hFsPrefix :
      (VC.runStateAux E0 (child s 1) s.len hPred).Fs = (VC.runState E0 s).Fs := by
    simpa using congrArg (fun st => st.Fs) hEqPrefix
  have hpi :
      VC.runStateAux E0 (child s 1) s.len (Nat.le_of_succ_le hSucc)
        = VC.runStateAux E0 (child s 1) s.len hPred := by
    exact VC.runStateAux_proof_irrel (E := E0) (s := child s 1) s.len _ _
  have hDigit :
      (child s 1).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)) = 1 := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hFsChild :
      (VC.runState E0 (child s 1)).Fs = insert (E.W (VC.decN s.len)) (VC.runState E0 s).Fs := by
    change
      (VC.step E0
        (VC.runStateAux E0 (child s 1) s.len (Nat.le_of_succ_le hSucc))
        ((child s 1).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)))).Fs
          = insert (E.W (VC.decN s.len)) (VC.runState E0 s).Fs
    rw [hpi, hDigit]
    change VC.FStep E0 (VC.runStateAux E0 (child s 1) s.len hPred) 1 = _
    unfold VC.FStep
    dsimp
    rw [if_pos hk0Prefix]
    rw [hdecNPrefix, hFsPrefix]
    simp [E0, toConcreteEnum]

  simpa [VC.FS, E0] using hFsChild

lemma Vconcrete_F_child_k0_one
    (E : Enumerations) (s : fin_seq)
    (hk0 : VC.decK s.len = IPC.k0) :
    (Vconcrete E).F (child s 1)
      =
    insert (E.W (VC.decN s.len)) ((Vconcrete E).F s) := by
  -- Unfold the `F` field of `Vconcrete`; it is exactly `FS (toConcreteEnum E)`.
  -- Then apply the previously proved `FS` lemma.
  simpa [Vconcrete] using (FS_child_k0_one (E := E) (s := s) hk0)

/-- Propositional version of the `needs1` predicate: `k0` together with `(mem ∨ eq)`, using the `(t+1)`-prefix exactly as in `needs1b`. -/
def needs1 {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ) : Prop :=
  VC.decK t = IPC.k0 ∧
    (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1)) ∨ E.W (VC.decN t) = W)


lemma bool_and_eq_true_iff (x y : Bool) : (x && y = true) ↔ (x = true ∧ y = true) := by
  cases x <;> cases y <;> simp

lemma bool_or_eq_true_iff (x y : Bool) : (x || y = true) ↔ (x = true ∨ y = true) := by
  cases x <;> cases y <;> simp


lemma needs1b_eq_true_iff_needs1
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : Nat) :
    Iff (needs1b (V := V) (a := a) (W := W) t = true) (needs1 (V := V) (a := a) (W := W) t) := by

  unfold needs1b needs1
  constructor
  case mp =>
    intro hb
    have hAnd := Bool.and_eq_true_iff.mp hb
    have hk0 : VC.decK t = IPC.k0 := (_root_.decide_eq_true_iff).1 hAnd.1
    have hmem_or_eq :
        Or (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1))) (E.W (VC.decN t) = W) := by
      cases hmem : decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1))) with
      | true =>
          exact Or.inl ((_root_.decide_eq_true_iff).1 hmem)
      | false =>
          have heq : decide (E.W (VC.decN t) = W) = true := by
            simpa [hmem] using hAnd.2
          exact Or.inr ((_root_.decide_eq_true_iff).1 heq)
    exact And.intro hk0 hmem_or_eq

  case mpr =>
    intro hNeeds
    have hk0d : decide (VC.decK t = IPC.k0) = true :=
      (_root_.decide_eq_true_iff).2 hNeeds.1
    have hOr :
        (decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1))) ||
         decide (E.W (VC.decN t) = W)) = true := by
      cases hNeeds.2 with
      | inl hm =>
          have hm' : decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1))) = true :=
            (_root_.decide_eq_true_iff).2 hm
          simp [hm']
      | inr he =>
          have he' : decide (E.W (VC.decN t) = W) = true :=
            (_root_.decide_eq_true_iff).2 he
          simp [he']
    exact Bool.and_eq_true_iff.mpr (And.intro hk0d hOr)

lemma k0_of_needs1b_true
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ) :
    needs1b (V := V) (a := a) (W := W) t = true → VC.decK t = IPC.k0 := by
  intro hb
  exact (needs1b_eq_true_iff_needs1 (V := V) (a := a) (W := W) (t := t)).1 hb |>.1

lemma mem_or_eq_of_needs1b_true
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ) :
    needs1b (V := V) (a := a) (W := W) t = true →
      (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1)) ∨ E.W (VC.decN t) = W) := by
  intro hb
  exact (needs1b_eq_true_iff_needs1 (V := V) (a := a) (W := W) (t := t)).1 hb |>.2

lemma Fs_child_k0_zero_eq
    (E : Enumerations) (s : fin_seq)
    (hk0 : VC.decK s.len = IPC.k0) :
    (VC.runState (toConcreteEnum E) (child s 0)).Fs
      = (VC.runState (toConcreteEnum E) s).Fs := by

  let E0 : VC.Enumerations := toConcreteEnum E
  have hlen : (child s 0).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton, Nat.succ_eq_add_one]
  have hSucc : s.len.succ <= (child s 0).len := by
    simp [hlen]
  have hPred : s.len <= (child s 0).len := Nat.le_of_succ_le hSucc
  have hPref : Prefix s (child s 0) := VC.Prefix_child s 0
  have hEqPrefix :
      VC.runStateAux E0 (child s 0) s.len hPred = VC.runState E0 s := by
    calc
      VC.runStateAux E0 (child s 0) s.len hPred
          = VC.runStateAux E0 (child s 0) s.len
              (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
                exact VC.runStateAux_proof_irrel (E := E0) (s := child s 0) s.len _ _
      _ = VC.runStateAux E0 s s.len le_rfl :=
            VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl
      _ = VC.runState E0 s := by
            rw [VC.runState]
  have htPrefix :
      (VC.runStateAux E0 (child s 0) s.len hPred).t = s.len := by
    calc
      (VC.runStateAux E0 (child s 0) s.len hPred).t
          = (VC.runState E0 s).t := by
              simpa using congrArg (fun st => st.t) hEqPrefix
      _ = s.len := by
            simpa using runState_t (E0 := E0) (s := s)
  have hk0Prefix : VC.decK (VC.runStateAux E0 (child s 0) s.len hPred).t = IPC.k0 := by
    simpa [htPrefix] using hk0
  have hFsPrefix :
      (VC.runStateAux E0 (child s 0) s.len hPred).Fs = (VC.runState E0 s).Fs := by
    simpa using congrArg (fun st => st.Fs) hEqPrefix
  have hpi :
      VC.runStateAux E0 (child s 0) s.len (Nat.le_of_succ_le hSucc)
        = VC.runStateAux E0 (child s 0) s.len hPred := by
    exact VC.runStateAux_proof_irrel (E := E0) (s := child s 0) s.len _ _
  have hDigit :
      (child s 0).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)) = 0 := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hFsChild :
      (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs := by
    change
      (VC.step E0
        (VC.runStateAux E0 (child s 0) s.len (Nat.le_of_succ_le hSucc))
        ((child s 0).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)))).Fs
          = (VC.runState E0 s).Fs
    rw [hpi, hDigit]
    change VC.FStep E0 (VC.runStateAux E0 (child s 0) s.len hPred) 0 = _
    unfold VC.FStep
    dsimp
    rw [if_pos hk0Prefix]
    simp [hFsPrefix]

  simpa [E0] using hFsChild

lemma Fs_child_k1_zero_eq
    (E : Enumerations) (s : fin_seq)
    (hk1 : VC.decK s.len = IPC.k1) :
    (VC.runState (toConcreteEnum E) (child s 0)).Fs
      = (VC.runState (toConcreteEnum E) s).Fs := by

  let E0 : VC.Enumerations := toConcreteEnum E
  have hlen : (child s 0).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton, Nat.succ_eq_add_one]
  have hSucc : s.len.succ <= (child s 0).len := by
    simp[hlen]
  have hPred : s.len <= (child s 0).len := Nat.le_of_succ_le hSucc
  have hPref : Prefix s (child s 0) := VC.Prefix_child s 0
  have hEqPrefix :
      VC.runStateAux E0 (child s 0) s.len hPred = VC.runState E0 s := by
    calc
      VC.runStateAux E0 (child s 0) s.len hPred
          = VC.runStateAux E0 (child s 0) s.len
              (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
                exact VC.runStateAux_proof_irrel (E := E0) (s := child s 0) s.len _ _
      _ = VC.runStateAux E0 s s.len le_rfl :=
            VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl
      _ = VC.runState E0 s := by
            rw [VC.runState]
  have htPrefix :
      (VC.runStateAux E0 (child s 0) s.len hPred).t = s.len := by
    calc
      (VC.runStateAux E0 (child s 0) s.len hPred).t
          = (VC.runState E0 s).t := by
              simpa using congrArg (fun st => st.t) hEqPrefix
      _ = s.len := by
            simpa using runState_t (E0 := E0) (s := s)
  have hk1Prefix : VC.decK (VC.runStateAux E0 (child s 0) s.len hPred).t = IPC.k1 := by
    simpa [htPrefix] using hk1
  have hk0ne : Ne (VC.decK (VC.runStateAux E0 (child s 0) s.len hPred).t) IPC.k0 := by
    intro hk0Prefix
    have : (IPC.k1 : Fin 3) = IPC.k0 := by
      calc
        (IPC.k1 : Fin 3)
            = VC.decK (VC.runStateAux E0 (child s 0) s.len hPred).t := by
                symm
                exact hk1Prefix
        _ = IPC.k0 := hk0Prefix
    exact (show Ne (IPC.k1 : Fin 3) IPC.k0 by decide) this
  have hFsPrefix :
      (VC.runStateAux E0 (child s 0) s.len hPred).Fs = (VC.runState E0 s).Fs := by
    simpa using congrArg (fun st => st.Fs) hEqPrefix
  have hpi :
      VC.runStateAux E0 (child s 0) s.len (Nat.le_of_succ_le hSucc)
        = VC.runStateAux E0 (child s 0) s.len hPred := by
    exact VC.runStateAux_proof_irrel (E := E0) (s := child s 0) s.len _ _
  have hDigit :
      (child s 0).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)) = 0 := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hFsChild :
      (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs := by
    change
      (VC.step E0
        (VC.runStateAux E0 (child s 0) s.len (Nat.le_of_succ_le hSucc))
        ((child s 0).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)))).Fs
          = (VC.runState E0 s).Fs
    rw [hpi, hDigit]
    change VC.FStep E0 (VC.runStateAux E0 (child s 0) s.len hPred) 0 = _
    unfold VC.FStep
    dsimp
    rw [if_neg hk0ne]
    rw [if_pos hk1Prefix]
    simp [hFsPrefix]

  simpa [E0] using hFsChild

lemma decK_eq_k2_of_ne_k0_k1 (t : ℕ)
    (h0 : VC.decK t ≠ IPC.k0) (h1 : VC.decK t ≠ IPC.k1) :
    VC.decK t = IPC.k2 := by
  -- First split the underlying value into the three cases `0`, `1`, and `2`.
  have hcases :
      (VC.decK t).val = 0 ∨ (VC.decK t).val = 1 ∨ (VC.decK t).val = 2 := by
    have : (VC.decK t).val < 3 := (VC.decK t).isLt
    omega
  -- Exclude the `0` and `1` cases separately; the remainder is `2`.
  cases hcases with
  | inl h0val =>
      have : VC.decK t = IPC.k0 := by
        apply Fin.ext
        simp [IPC.k0, h0val]
      exact False.elim (h0 this)
  | inr h12 =>
      cases h12 with
      | inl h1val =>
          have : VC.decK t = IPC.k1 := by
            apply Fin.ext
            simp [IPC.k1, h1val]
          exact False.elim (h1 this)
      | inr h2val =>
          apply Fin.ext
          simp [IPC.k2, h2val]

lemma eq_one_of_needs1b_true_of_decK_ne_k0
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t q : ℕ)
    (hk0ne : VC.decK t ≠ IPC.k0) :
    needs1b (V := V) (a := a) (W := W) t = true → q = 1 := by
  intro hb
  have hk0 : VC.decK t = IPC.k0 :=
    k0_of_needs1b_true (V := V) (a := a) (W := W) (t := t) hb
  exact False.elim (hk0ne hk0)

lemma two_le_of_decK_eq_k2 (t : ℕ) (hk2 : VC.decK t = IPC.k2) : 2 ≤ t := by
  -- Extract `(decK t).val = 2` from `hk2`.
  have hval : (VC.decK t).val = 2 := by
    -- This is just equality of the underlying `Fin.val` components.
    simpa [IPC.k2] using congrArg Fin.val hk2

  -- Since `decK t = (schedDecode t).2.2` and `schedDecode` uses `r := t % 3`,
  -- we obtain `(decK t).val = t % 3`.
  have hmod : t % 3 = 2 := by
    -- Unfold `decK` and `schedDecode`.
    -- Key fact: the third component of `schedDecode` is exactly `⟨t % 3, _⟩`.
    simpa [VC.decK, IPC.schedDecode] using hval

  -- Contradiction argument: if `t < 2`, then `t < 3`, hence `t % 3 = t`, contradicting `hmod`.
  by_contra hle
  have ht2 : t < 2 := Nat.lt_of_not_ge hle
  have ht3 : t < 3 := lt_trans ht2 (by decide : 2 < 3)
  have hmodt : t % 3 = t := Nat.mod_eq_of_lt ht3
  have htEq : t = 2 := by
    -- hmod : t%3=2, hmodt : t%3=t
    simpa [hmodt] using hmod
  exact (Nat.ne_of_lt ht2) htEq

/-- If `decK t = k2`, then two steps earlier we were necessarily in the corresponding `k0` phase. -/
lemma decK_sub2_of_decK_eq_k2 (t : Nat) (_ : 2 <= t) (hk2 : VC.decK t = IPC.k2) :
    VC.decK (t - 2) = IPC.k0 := by

  have hmod2 : t % 3 = 2 := by
    have hval : (VC.decK t).val = 2 := by
      simpa [IPC.k2] using congrArg Fin.val hk2
    simpa [VC.decK, IPC.schedDecode] using hval

  have ht_eq : t = 2 + 3 * (t / 3) := by
    have h := Nat.mod_add_div t 3
    simpa [hmod2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm

  have hsub : t - 2 = 3 * (t / 3) := by
    conv_lhs => rw [ht_eq]
    exact Nat.add_sub_cancel_left 2 (3 * (t / 3))

  have hmod0 : (t - 2) % 3 = 0 := by
    have h := Nat.add_mul_mod_self_left 0 3 (t / 3)
    omega

  apply Fin.eq_of_val_eq
  change (t - 2) % 3 = 0
  exact hmod0

/-- In the `k2` case, if the scheduled formula is a disjunction but `prev2 ≠ 1` (so we are not in split mode), then `q = 0` is always allowed. -/
lemma AllowedStepb_k2_or_prev2_ne_one_allow_0
    (E : Enumerations) (s : fin_seq) (A B : Form)
    (hk2 : VC.decK s.len = IPC.k2)
    (hW  : E.W (VC.decN s.len) = A ⋎ B)
    (hp  : (VC.runState (toConcreteEnum E) s).prev2 ≠ 1) :
    VC.AllowedStepb (toConcreteEnum E) (VC.runState (toConcreteEnum E) s) 0 = true := by
  let E0 : VC.Enumerations := toConcreteEnum E
  let st : VC.State := VC.runState E0 s
  have ht : st.t = s.len := by
    simpa [st, E0] using runState_t (E0 := E0) (s := s)

  have hk2st : VC.decK st.t = IPC.k2 := by
    simpa [ht] using hk2

  have hk0ne : ¬ VC.decK st.t = IPC.k0 := by
    simpa [hk2st] using (by decide : (IPC.k2 : Fin 3) ≠ IPC.k0)

  have hk1ne : ¬ VC.decK st.t = IPC.k1 := by
    simpa [hk2st] using (by decide : (IPC.k2 : Fin 3) ≠ IPC.k1)

  have hpst : st.prev2 ≠ 1 := by
    -- Rewrite `runState (toConcreteEnum E) s` as `st`.
    simpa [st, E0] using hp

  have hWst : E0.W (VC.decN st.t) = A ⋎ B := by
    simpa [E0, toConcreteEnum, ht] using hW

  -- Key point: `simp` must see the definitions of `st` and `E0`, otherwise it cannot use `hk0ne`, `hk1ne`, `hpst`, or `hWst`.
  unfold VC.AllowedStepb
  simp [E0, st, hk0ne, hk1ne, hWst, hpst]

lemma runStateAux_Fs_len
    (E0 : VC.Enumerations) (s : fin_seq)
    (h : s.len ≤ s.len) :
    (VC.runStateAux E0 s s.len h).Fs = (VC.runState E0 s).Fs := by
  have hEq :
      VC.runStateAux E0 s s.len h = VC.runStateAux E0 s s.len le_rfl :=
    VC.runStateAux_proof_irrel (E := E0) (s := s) (n := s.len) h le_rfl
  have hEqFs := congrArg (fun st : VC.State => st.Fs) hEq
  simp [VC.runState]

lemma AllowedStepb_k2_split_q1
    (E0 : VC.Enumerations) (st : VC.State) (A B : Form)
    (hk2 : VC.decK st.t = IPC.k2)
    (hW  : E0.W (VC.decN st.t) = A ⋎ B)
    (hp  : st.prev2 = 1) :
    VC.AllowedStepb E0 st 1 = true := by
  unfold VC.AllowedStepb
  have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
  have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
  -- Do not use `Finset.decide_eq_true_iff` here; plain `simp` already evaluates the needed `decide` terms.
  simp [hk2, hk20, hk21, hW, hp]

lemma AllowedStepb_k2_split_q2
    (E0 : VC.Enumerations) (st : VC.State) (A B : Form)
    (hk2 : VC.decK st.t = IPC.k2)
    (hW  : E0.W (VC.decN st.t) = A ⋎ B)
    (hp  : st.prev2 = 1) :
    VC.AllowedStepb E0 st 2 = true := by
  unfold VC.AllowedStepb
  have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
  have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
  simp [hk2, hk20, hk21, hW, hp]

lemma Fs_child_k2_split_one_eq
    (E : Enumerations) (s : fin_seq) (A B : Form)
    (hk2 : VC.decK s.len = IPC.k2)
    (hW  : E.W (VC.decN s.len) = Form.or A B)
    (hp  : (VC.runState (toConcreteEnum E) s).prev2 = 1) :
    (VC.runState (toConcreteEnum E) (child s 1)).Fs
      = insert A (VC.runState (toConcreteEnum E) s).Fs := by
  let E0 : VC.Enumerations := toConcreteEnum E
  have hlen : (child s 1).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton, Nat.succ_eq_add_one]
  have hSucc : s.len.succ <= (child s 1).len := by
    simp [hlen]
  have hPred : s.len <= (child s 1).len := Nat.le_of_succ_le hSucc
  have hPref : Prefix s (child s 1) := VC.Prefix_child s 1
  have hEqPrefix :
      VC.runStateAux E0 (child s 1) s.len hPred = VC.runState E0 s := by
    calc
      VC.runStateAux E0 (child s 1) s.len hPred
          = VC.runStateAux E0 (child s 1) s.len
              (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
                exact VC.runStateAux_proof_irrel (E := E0) (s := child s 1) s.len _ _
      _ = VC.runStateAux E0 s s.len le_rfl :=
            VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl
      _ = VC.runState E0 s := by
            rw [VC.runState]
  have htPrefix :
      (VC.runStateAux E0 (child s 1) s.len hPred).t = s.len := by
    calc
      (VC.runStateAux E0 (child s 1) s.len hPred).t
          = (VC.runState E0 s).t := by
              simpa using congrArg (fun st => st.t) hEqPrefix
      _ = s.len := by
            simpa using runState_t (E0 := E0) (s := s)
  have hk2Prefix : VC.decK (VC.runStateAux E0 (child s 1) s.len hPred).t = IPC.k2 := by
    simpa [htPrefix] using hk2
  have hk20 : Ne (IPC.k2 : Fin 3) IPC.k0 := by decide
  have hk21 : Ne (IPC.k2 : Fin 3) IPC.k1 := by decide
  have hk0ne : Ne (VC.decK (VC.runStateAux E0 (child s 1) s.len hPred).t) IPC.k0 := by
    intro hk0Prefix
    exact hk20 (hk2Prefix.symm.trans hk0Prefix)
  have hk1ne : Ne (VC.decK (VC.runStateAux E0 (child s 1) s.len hPred).t) IPC.k1 := by
    intro hk1Prefix
    exact hk21 (hk2Prefix.symm.trans hk1Prefix)
  have hdecNPrefix :
      VC.decN (VC.runStateAux E0 (child s 1) s.len hPred).t = VC.decN s.len := by
    simp [htPrefix]
  have hWPrefix :
      E0.W (VC.decN (VC.runStateAux E0 (child s 1) s.len hPred).t) = Form.or A B := by
    simpa [E0, hdecNPrefix] using hW
  have hpPrefix :
      (VC.runStateAux E0 (child s 1) s.len hPred).prev2 = 1 := by
    calc
      (VC.runStateAux E0 (child s 1) s.len hPred).prev2
          = (VC.runState E0 s).prev2 := by
              simpa using congrArg (fun st => st.prev2) hEqPrefix
      _ = 1 := by
            simpa [E0] using hp
  have hFsPrefix :
      (VC.runStateAux E0 (child s 1) s.len hPred).Fs = (VC.runState E0 s).Fs := by
    simpa using congrArg (fun st => st.Fs) hEqPrefix
  have hpi :
      VC.runStateAux E0 (child s 1) s.len (Nat.le_of_succ_le hSucc)
        = VC.runStateAux E0 (child s 1) s.len hPred := by
    exact VC.runStateAux_proof_irrel (E := E0) (s := child s 1) s.len _ _
  have hDigit :
      (child s 1).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)) = 1 := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hFsChild :
      (VC.runState E0 (child s 1)).Fs = insert A (VC.runState E0 s).Fs := by
    change
      (VC.step E0
        (VC.runStateAux E0 (child s 1) s.len (Nat.le_of_succ_le hSucc))
        ((child s 1).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)))).Fs
          = insert A (VC.runState E0 s).Fs
    rw [hpi, hDigit]
    change VC.FStep E0 (VC.runStateAux E0 (child s 1) s.len hPred) 1 = _
    unfold VC.FStep
    dsimp
    rw [if_neg hk0ne]
    rw [if_neg hk1ne]
    simp [hWPrefix, hpPrefix, hFsPrefix]

  simpa [E0] using hFsChild


lemma Fs_child_k2_split_two_eq
    (E : Enumerations) (s : fin_seq) (A B : Form)
    (hk2 : VC.decK s.len = IPC.k2)
    (hW  : E.W (VC.decN s.len) = Form.or A B)
    (hp  : (VC.runState (toConcreteEnum E) s).prev2 = 1) :
    (VC.runState (toConcreteEnum E) (child s 2)).Fs
      = insert B (VC.runState (toConcreteEnum E) s).Fs := by
  let E0 : VC.Enumerations := toConcreteEnum E
  have hlen : (child s 2).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton, Nat.succ_eq_add_one]
  have hSucc : s.len.succ <= (child s 2).len := by
    simp [hlen]
  have hPred : s.len <= (child s 2).len := Nat.le_of_succ_le hSucc
  have hPref : Prefix s (child s 2) := VC.Prefix_child s 2
  have hEqPrefix :
      VC.runStateAux E0 (child s 2) s.len hPred = VC.runState E0 s := by
    calc
      VC.runStateAux E0 (child s 2) s.len hPred
          = VC.runStateAux E0 (child s 2) s.len
              (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
                exact VC.runStateAux_proof_irrel (E := E0) (s := child s 2) s.len _ _
      _ = VC.runStateAux E0 s s.len le_rfl :=
            VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl
      _ = VC.runState E0 s := by
            rw [VC.runState]
  have htPrefix :
      (VC.runStateAux E0 (child s 2) s.len hPred).t = s.len := by
    calc
      (VC.runStateAux E0 (child s 2) s.len hPred).t
          = (VC.runState E0 s).t := by
              simpa using congrArg (fun st => st.t) hEqPrefix
      _ = s.len := by
            simpa using runState_t (E0 := E0) (s := s)
  have hk2Prefix : VC.decK (VC.runStateAux E0 (child s 2) s.len hPred).t = IPC.k2 := by
    simpa [htPrefix] using hk2
  have hk20 : Ne (IPC.k2 : Fin 3) IPC.k0 := by decide
  have hk21 : Ne (IPC.k2 : Fin 3) IPC.k1 := by decide
  have hk0ne : Ne (VC.decK (VC.runStateAux E0 (child s 2) s.len hPred).t) IPC.k0 := by
    intro hk0Prefix
    exact hk20 (hk2Prefix.symm.trans hk0Prefix)
  have hk1ne : Ne (VC.decK (VC.runStateAux E0 (child s 2) s.len hPred).t) IPC.k1 := by
    intro hk1Prefix
    exact hk21 (hk2Prefix.symm.trans hk1Prefix)
  have hdecNPrefix :
      VC.decN (VC.runStateAux E0 (child s 2) s.len hPred).t = VC.decN s.len := by
    simp [htPrefix]
  have hWPrefix :
      E0.W (VC.decN (VC.runStateAux E0 (child s 2) s.len hPred).t) = Form.or A B := by
    simpa [E0, hdecNPrefix] using hW
  have hpPrefix :
      (VC.runStateAux E0 (child s 2) s.len hPred).prev2 = 1 := by
    calc
      (VC.runStateAux E0 (child s 2) s.len hPred).prev2
          = (VC.runState E0 s).prev2 := by
              simpa using congrArg (fun st => st.prev2) hEqPrefix
      _ = 1 := by
            simpa [E0] using hp
  have hFsPrefix :
      (VC.runStateAux E0 (child s 2) s.len hPred).Fs = (VC.runState E0 s).Fs := by
    simpa using congrArg (fun st => st.Fs) hEqPrefix
  have hpi :
      VC.runStateAux E0 (child s 2) s.len (Nat.le_of_succ_le hSucc)
        = VC.runStateAux E0 (child s 2) s.len hPred := by
    exact VC.runStateAux_proof_irrel (E := E0) (s := child s 2) s.len _ _
  have hDigit :
      (child s 2).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)) = 2 := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hFsChild :
      (VC.runState E0 (child s 2)).Fs = insert B (VC.runState E0 s).Fs := by
    change
      (VC.step E0
        (VC.runStateAux E0 (child s 2) s.len (Nat.le_of_succ_le hSucc))
        ((child s 2).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)))).Fs
          = insert B (VC.runState E0 s).Fs
    rw [hpi, hDigit]
    change VC.FStep E0 (VC.runStateAux E0 (child s 2) s.len hPred) 2 = _
    unfold VC.FStep
    dsimp
    rw [if_neg hk0ne]
    rw [if_neg hk1ne]
    simp [hWPrefix, hpPrefix, hFsPrefix]

  simpa [E0] using hFsChild
lemma Fs_child_k2_split_one_eq_aux
    (E : Enumerations) (s : fin_seq) (A B : Form)
    (hk2 : VC.decK s.len = IPC.k2)
    (hW  : E.W (VC.decN s.len) = A ⋎ B)
    (hp  : (VC.runState (toConcreteEnum E) s).prev2 = 1) :
    ∀ (h1 : (child s 1).len ≤ (child s 1).len) (h2 : s.len ≤ s.len),
      (VC.runStateAux (toConcreteEnum E) (child s 1) (child s 1).len h1).Fs
        = insert A (VC.runStateAux (toConcreteEnum E) s s.len h2).Fs := by
  intro h1 h2
  have hL :
      (VC.runStateAux (toConcreteEnum E) (child s 1) (child s 1).len h1).Fs
        = (VC.runState (toConcreteEnum E) (child s 1)).Fs := by
    simpa using (runStateAux_Fs_len (E0 := toConcreteEnum E) (s := child s 1) (h := h1))
  have hR :
      (VC.runStateAux (toConcreteEnum E) s s.len h2).Fs
        = (VC.runState (toConcreteEnum E) s).Fs := by
    simpa using (runStateAux_Fs_len (E0 := toConcreteEnum E) (s := s) (h := h2))
  rw [hL, hR]
  simpa using (Fs_child_k2_split_one_eq (E := E) (s := s) (A := A) (B := B) hk2 hW hp)

lemma Fs_child_k2_split_two_eq_aux
    (E : Enumerations) (s : fin_seq) (A B : Form)
    (hk2 : VC.decK s.len = IPC.k2)
    (hW  : E.W (VC.decN s.len) = A ⋎ B)
    (hp  : (VC.runState (toConcreteEnum E) s).prev2 = 1) :
    ∀ (h1 : (child s 2).len ≤ (child s 2).len) (h2 : s.len ≤ s.len),
      (VC.runStateAux (toConcreteEnum E) (child s 2) (child s 2).len h1).Fs
        = insert B (VC.runStateAux (toConcreteEnum E) s s.len h2).Fs := by
  intro h1 h2
  have hL :
      (VC.runStateAux (toConcreteEnum E) (child s 2) (child s 2).len h1).Fs
        = (VC.runState (toConcreteEnum E) (child s 2)).Fs := by
    simpa using (runStateAux_Fs_len (E0 := toConcreteEnum E) (s := child s 2) (h := h1))
  have hR :
      (VC.runStateAux (toConcreteEnum E) s s.len h2).Fs
        = (VC.runState (toConcreteEnum E) s).Fs := by
    simpa using (runStateAux_Fs_len (E0 := toConcreteEnum E) (s := s) (h := h2))
  rw [hL, hR]
  simpa using (Fs_child_k2_split_two_eq (E := E) (s := s) (A := A) (B := B) hk2 hW hp)

lemma Fs_child_k2_zero_eq
    (E : Enumerations) (s : fin_seq)
    (hk2 : VC.decK s.len = IPC.k2) :
    (VC.runState (toConcreteEnum E) (child s 0)).Fs
      = (VC.runState (toConcreteEnum E) s).Fs := by
  let E0 : VC.Enumerations := toConcreteEnum E
  have hlen : (child s 0).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton, Nat.succ_eq_add_one]
  have hSucc : s.len.succ <= (child s 0).len := by
    simp [hlen]
  have hPred : s.len <= (child s 0).len := Nat.le_of_succ_le hSucc
  have hPref : Prefix s (child s 0) := VC.Prefix_child s 0
  have hEqPrefix :
      VC.runStateAux E0 (child s 0) s.len hPred = VC.runState E0 s := by
    calc
      VC.runStateAux E0 (child s 0) s.len hPred
          = VC.runStateAux E0 (child s 0) s.len
              (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
                exact VC.runStateAux_proof_irrel (E := E0) (s := child s 0) s.len _ _
      _ = VC.runStateAux E0 s s.len le_rfl :=
            VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl
      _ = VC.runState E0 s := by
            rw [VC.runState]
  have htPrefix :
      (VC.runStateAux E0 (child s 0) s.len hPred).t = s.len := by
    calc
      (VC.runStateAux E0 (child s 0) s.len hPred).t
          = (VC.runState E0 s).t := by
              simpa using congrArg (fun st => st.t) hEqPrefix
      _ = s.len := by
            simpa using runState_t (E0 := E0) (s := s)
  have hk2Prefix : VC.decK (VC.runStateAux E0 (child s 0) s.len hPred).t = IPC.k2 := by
    simpa [htPrefix] using hk2
  have hk20 : Ne (IPC.k2 : Fin 3) IPC.k0 := by decide
  have hk21 : Ne (IPC.k2 : Fin 3) IPC.k1 := by decide
  have hk0ne : Ne (VC.decK (VC.runStateAux E0 (child s 0) s.len hPred).t) IPC.k0 := by
    intro hk0Prefix
    exact hk20 (hk2Prefix.symm.trans hk0Prefix)
  have hk1ne : Ne (VC.decK (VC.runStateAux E0 (child s 0) s.len hPred).t) IPC.k1 := by
    intro hk1Prefix
    exact hk21 (hk2Prefix.symm.trans hk1Prefix)
  have hFsPrefix :
      (VC.runStateAux E0 (child s 0) s.len hPred).Fs = (VC.runState E0 s).Fs := by
    simpa using congrArg (fun st => st.Fs) hEqPrefix
  have hpi :
      VC.runStateAux E0 (child s 0) s.len (Nat.le_of_succ_le hSucc)
        = VC.runStateAux E0 (child s 0) s.len hPred := by
    exact VC.runStateAux_proof_irrel (E := E0) (s := child s 0) s.len _ _
  have hDigit :
      (child s 0).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)) = 0 := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  have hFsChild :
      (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs := by
    change
      (VC.step E0
        (VC.runStateAux E0 (child s 0) s.len (Nat.le_of_succ_le hSucc))
        ((child s 0).seq (Fin.mk s.len (Nat.lt_of_lt_of_le (Nat.lt_succ_self s.len) hSucc)))).Fs
          = (VC.runState E0 s).Fs
    rw [hpi, hDigit]
    change VC.FStep E0 (VC.runStateAux E0 (child s 0) s.len hPred) 0 = _
    unfold VC.FStep
    dsimp
    rw [if_neg hk0ne]
    rw [if_neg hk1ne]
    have hmatch :
        (match E0.W (VC.decN (VC.runStateAux E0 (child s 0) s.len hPred).t) with
          | Form.or A B => (VC.runStateAux E0 (child s 0) s.len hPred).Fs
          | x => (VC.runStateAux E0 (child s 0) s.len hPred).Fs)
          = (VC.runStateAux E0 (child s 0) s.len hPred).Fs := by
      cases hForm : E0.W (VC.decN (VC.runStateAux E0 (child s 0) s.len hPred).t) <;> simp
    simpa [hFsPrefix] using hmatch

  simpa [E0] using hFsChild

/-- Key lemma: if step `n` is a `k0` step and the `n`-th digit is `1`, then at step `n+1` the set `Fs` is updated by inserting the currently scheduled formula. -/
lemma runStateAux_Fs_succ_k0_digit1
    (E0 : VC.Enumerations) (s : fin_seq) (n : ℕ)
    (hn : n.succ ≤ s.len)
    (hk0 : VC.decK n = k0)
    (hq : s.seq ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩ = 1) :
    (VC.runStateAux E0 s n.succ hn).Fs
      = insert (E0.W (VC.decN n)) (VC.runStateAux E0 s n (Nat.le_of_succ_le hn)).Fs := by

  have hn0 : n ≤ s.len := Nat.le_of_succ_le hn
  let st0 : VC.State := VC.runStateAux E0 s n hn0

  -- st0.t = n
  have ht0 : st0.t = n := by
    simpa [st0] using runStateAux_t (E0 := E0) (s := s) (n := n) (hn := hn0)

  -- decK st0.t = k0
  have hk0st0 : VC.decK st0.t = k0 := by
    simpa [ht0] using hk0

  -- Unfold the successor branch of `runStateAux` into `step`, and then unfold `step.Fs = FStep`.
  -- Then use `hk0st0` to select the `k0` branch, `hq` to select `q = 1`, and `ht0` to rewrite `decN st0.t` as `decN n`.
  -- This is the correct way to resolve the large nested `if` expression that otherwise gets stuck.
  dsimp [VC.runStateAux]   -- Expand the `(n+1)` layer: `let st := ...; let q := ...; step ...`.
  -- The left-hand side is now `(VC.step E0 st0 (s.seq ⟨n, ...⟩)).Fs`.
  -- The `Fs` field of `step` is by definition `FStep`.
  simp [VC.step, VC.FStep, st0, hq, ht0]
  intro hnk0
  exact False.elim (hnk0 hk0)

/-- If `decK t = k2`, then `decN (t-2) = decN t`; this is the three-phase alignment for a fixed pair `(n,m)`. -/
lemma decN_sub2_of_decK_eq_k2 (t : Nat) (hk2 : VC.decK t = IPC.k2) :
    VC.decN (t - 2) = VC.decN t := by

  have hmod2 : t % 3 = 2 := by
    have hval : (VC.decK t).val = 2 := by
      simpa [IPC.k2] using congrArg Fin.val hk2
    simpa [VC.decK, IPC.schedDecode] using hval

  have ht_eq : t = 2 + 3 * (t / 3) := by
    have h := Nat.mod_add_div t 3
    simpa [hmod2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm

  have hsub : t - 2 = 3 * (t / 3) := by
    conv_lhs => rw [ht_eq]
    exact Nat.add_sub_cancel_left 2 (3 * (t / 3))

  have hdiv : (t - 2) / 3 = t / 3 := by
    rw [hsub]
    have hmul : (3 * (t / 3)) / 3 = ((t / 3) * 3) / 3 := by
      simp [Nat.mul_comm]
    rw [hmul]
    simp

  unfold VC.decN IPC.schedDecode
  change (IPC.pairDecodeBin ((t - 2) / 3)).1 = (IPC.pairDecodeBin (t / 3)).1
  rw [hdiv]


/-!
Main rule package for `Tlaw`.

We analyze a node `s` with `Tlaw s = 0` by cases on `k = decK (len s)`:
- k0: Forced → CaseForced; else if needs1 → CaseCtx; else CaseOne (q=0)
- k1: CaseOne (q=0)
- k2: if disjunction & prev2=1 → CaseSplit; else CaseOne (q=0)
-/

theorem stepRules
    (E : Enumerations)
    (a : Branch (Vconcrete E))
    (W Q : Form) :
    IndStepRules (Vconcrete E) a W Q (Tlaw (E := E) (Vconcrete E) a W) := by
  let V : VeldmanFan E := Vconcrete E
  refine ⟨?_⟩
  intro s hs0
  have hSs : V.S s = 0 := (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := s)).1 hs0 |>.1
  have hOKs : StepsOK (E := E) V a W s := (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := s)).1 hs0 |>.2

  let E0 : VC.Enumerations := toConcreteEnum E
  let st : VC.State := VC.runState E0 s
  have ht : st.t = s.len := by
    simpa [st, E0] using (runState_t (E0 := E0) (s := s))

  have hk : VC.decK st.t = VC.decK s.len := by simp[ht]
  -- Split on decK
  by_cases hk0 : VC.decK s.len = IPC.k0
  · -- k0 case
    have hk0' : VC.decK st.t = IPC.k0 := by simpa [ht] using hk0
    by_cases hF : VC.Forced0b E0 st = true
    · -- CaseForced with q=1, X = W(decN t)
      refine Or.inr (Or.inl ?_)
      let X : Form := E.W (VC.decN s.len)
      refine ⟨1, X, ?_, ?_, ?_⟩
      · -- T(child)=0
        have hAllowed : VC.AllowedStepb E0 st 1 = true :=
          AllowedStepb_k0_force_only_1 (E0 := E0) (st := st) (by simpa [ht] using hk0) (by simpa [st] using hF)
        have hSigmaChild : V.S (child s 1) = 0 := by
          have : VC.Sigma E0 (child s 1) = 0 :=
            Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 1)
              (by simpa [V, Vconcrete, E0] using hSs)
              (by simpa [VC.runState, st] using hAllowed)
          simpa [V, Vconcrete, E0] using this
        have hOKchild : StepsOK (E := E) V a W (child s 1) :=
          StepsOK_child_of_StepsOK (V := V) (a := a) (W := W) (s := s) (q := 1) hOKs (by intro _; rfl)
        exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 1)).2 ⟨hSigmaChild, hOKchild⟩
      · -- F(child)=insert X (F s)
        have : V.F (child s 1) = insert X (V.F s) := by
          -- compute using concrete FStep at k0
          subst X
          simpa [V] using (Vconcrete_F_child_k0_one (E := E) (s := s) hk0)
        simpa using this
      · -- derivability
        have hprf : ((↑(st.Fs) : Set Form) ⊢ᵢ (E0.W (VC.decN st.t))) := Forced0b_prf (E0 := E0) (st := st) (by simpa [st] using hF)
        -- rewrite Fs and formula
        have hFs : (↑(V.F s) : Set Form) = (↑st.Fs : Set Form) := by
          simp [V, Vconcrete, VC.FS, st, E0]
        let X : Form := E.W (VC.decN s.len)

        have hX : E0.W (VC.decN st.t) = X := by
  -- First use `ht : st.t = s.len`.
  -- Then unfold `E0`.
          subst X
          simp [E0, toConcreteEnum, ht]

        have hprfX : (↑st.Fs : Set Form) ⊢ᵢ X := by
  -- Rewrite the conclusion using `hX`.
          simpa [hX] using hprf

-- Step 2: rewrite the context from `st.Fs` to `V.F s`.
        have hΓ : (↑(V.F s) : Set Form) ⊢ᵢ X := by
  -- Rewrite the context using `hFs` (note the direction).
          simpa [hFs] using hprfX

-- If your goal is `↑((Vconcrete E).F s) ⊢ᵢ X` while you have `let V := Vconcrete E`,
-- then in the last line you only need to unfold `V`:
        simpa [V] using hΓ



    · -- not forced
      have hF' : VC.Forced0b E0 st = false := by
        cases h0 : VC.Forced0b E0 st with
        | true =>
            -- Here `h0 : Forced0b = true`, contradicting `hF : Forced0b ≠ true`.
            exact False.elim (hF h0)
        | false =>

            simp
      -- if needs1 at this time, we must take q=1 (CaseCtx), else take q=0 (CaseOne)
      by_cases hneed :
  (E.W (VC.decN s.len) ∈ V.F (finitize a.1 (s.len + 1)) ∨
   E.W (VC.decN s.len) = W)
      · -- CaseCtx (q=1)
        refine Or.inr (Or.inr (Or.inl ?_))
        let X : Form := E.W (VC.decN s.len)
        refine ⟨1, X, ?_, ?_, ?_⟩
        · -- T(child)=0
          have hAllowed : VC.AllowedStepb E0 st 1 = true :=
            (AllowedStepb_k0_allow_0_1 (E0 := E0) (st := st) (by simpa [ht] using hk0) hF').2
          have hSigmaChild : V.S (child s 1) = 0 := by
            have : VC.Sigma E0 (child s 1) = 0 :=
              Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 1)
                (by simpa [V, Vconcrete, E0] using hSs)
                (by simpa [VC.runState, st] using hAllowed)
            simpa [V, Vconcrete, E0] using this
          have hnew : needs1b (E := E) V a W s.len → (1 : ℕ) = 1 := by intro _; rfl
          have hOKchild : StepsOK (E := E) V a W (child s 1) :=
            StepsOK_child_of_StepsOK (V := V) (a := a) (W := W) (s := s) (q := 1) hOKs (by intro _; rfl)
          exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 1)).2 ⟨hSigmaChild, hOKchild⟩
        · -- F(child)=insert X (F s)
          subst X
          simpa [VC.FS, E0] using (FS_child_k0_one (E := E) (s := s) hk0)
        · -- X in Gamma a or X=W
          rcases hneed with hmem | hEq
          · -- X ∈ Γ_a because it's already in F(prefix a (s.len))
            left
            refine ⟨s.len + 1, ?_⟩
-- Note that `Gamma` is defined using `finitize a.1 n`, so we also work with `a.1` here rather than `↑a`.
            simpa [Gamma, X] using hmem
          · right
            simpa [X] using hEq

      · -- CaseOne with q=0
        refine Or.inl ?_
        refine ⟨0, ?_, ?_⟩
        · -- T(child)=0
          have hAllowed : VC.AllowedStepb E0 st 0 = true :=
            (AllowedStepb_k0_allow_0_1 (E0 := E0) (st := st) (by simpa [ht] using hk0) hF').1
          have hSigmaChild : V.S (child s 0) = 0 := by
            have : VC.Sigma E0 (child s 0) = 0 :=
              Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
                (by simpa [V, Vconcrete, E0] using hSs)
                (by simpa [VC.runState, st] using hAllowed)
            simpa [V, Vconcrete, E0] using this
          have hnew : needs1b (E := E) V a W s.len → (0 : ℕ) = 1 := by
            intro hb
            have hP :
      (E.W (VC.decN s.len) ∈ V.F (finitize a.1 (s.len + 1)) ∨ E.W (VC.decN s.len) = W) :=
    mem_or_eq_of_needs1b_true (V := V) (a := a) (W := W) (t := s.len) hb
            exact False.elim (hneed hP)
          have hOKchild : StepsOK (E := E) V a W (child s 0) :=
            StepsOK_child_of_StepsOK (V := V) (a := a) (W := W) (s := s) (q := 0) hOKs hnew
          exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 0)).2 ⟨hSigmaChild, hOKchild⟩
        · -- F unchanged
          change (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs
          simpa [E0] using (Fs_child_k0_zero_eq (E := E) (s := s) hk0)



  · -- not k0
    by_cases hk1 : VC.decK s.len = IPC.k1
    · -- k1: only q=0, Fs unchanged
      refine Or.inl ?_
      refine ⟨0, ?_, ?_⟩
      · have hAllowed : VC.AllowedStepb E0 st 0 = true :=
          AllowedStepb_k1_only_0 (E0 := E0) (st := st) (by simpa [ht] using hk1)
        have hSigmaChild : V.S (child s 0) = 0 := by
          have : VC.Sigma E0 (child s 0) = 0 :=
            Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
              (by simpa [V, Vconcrete, E0] using hSs)
              (by simpa [VC.runState, st] using hAllowed)
          simpa [V, Vconcrete, E0] using this
        have hnew : needs1b (E := E) V a W s.len → (0 : ℕ) = 1 := by
          intro hb
          have hk0_of_hb : VC.decK s.len = IPC.k0 :=
    k0_of_needs1b_true (V := V) (a := a) (W := W) (t := s.len) hb
          exact False.elim (hk0 hk0_of_hb)
        have hOKchild : StepsOK (E := E) V a W (child s 0) :=
          StepsOK_child_of_StepsOK (V := V) (a := a) (W := W) (s := s) (q := 0) hOKs hnew
        exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 0)).2 ⟨hSigmaChild, hOKchild⟩
      · change (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs
        simpa [E0] using (Fs_child_k1_zero_eq (E := E) (s := s) hk1)
    · -- k2
      have hk2 : VC.decK s.len = IPC.k2 :=
        decK_eq_k2_of_ne_k0_k1 (t := s.len) hk0 hk1
      -- analyze whether we are in the disjunction split
      cases hW : E.W (VC.decN s.len) with
      | or A B =>
          by_cases hp : (VC.runState E0 s).prev2 = 1
          · -- CaseSplit
            refine Or.inr (Or.inr (Or.inr ?_))
            refine ⟨A, B, ?_, ?_, ?_, ?_, ?_⟩
            · -- T(child 1)=0
              have hAllowed : VC.AllowedStepb E0 st 1 = true := by

                have hk2st : VC.decK st.t = IPC.k2 := by
                  simpa [ht] using hk2
                have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
                have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide

                have hWst : E0.W (VC.decN st.t) = A ⋎ B := by
                  simpa [E0, toConcreteEnum, ht] using hW

                have hp' : st.prev2 = 1 := by
                  simpa [st] using hp

                simp [VC.AllowedStepb, hk2st, hk20, hk21, hWst, hp']

              have hSigmaChild : V.S (child s 1) = 0 := by
                have : VC.Sigma E0 (child s 1) = 0 :=
                  Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 1)
                    (by simpa [V, Vconcrete, E0] using hSs)
                    (by simpa [st] using hAllowed)
                simpa [V, Vconcrete, E0] using this

              have hOKchild : StepsOK (E := E) V a W (child s 1) :=
                StepsOK_child_of_StepsOK (V := V) (a := a) (W := W) (s := s) (q := 1)
                  hOKs (by intro _; rfl)

              exact
                (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 1)).2
                  ⟨hSigmaChild, hOKchild⟩
            · -- T(child 2)=0
              have hAllowed : VC.AllowedStepb E0 st 2 = true := by
                have hk2st : VC.decK st.t = IPC.k2 := by
                  simpa [ht] using hk2
                have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
                have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
                have hWst : E0.W (VC.decN st.t) = A ⋎ B := by
                  simpa [E0, toConcreteEnum, ht] using hW
                have hp' : st.prev2 = 1 := by
                  simpa [st] using hp
                simp [VC.AllowedStepb, hk2st, hk20, hk21, hWst, hp']
              have hSigmaChild : V.S (child s 2) = 0 := by
                have : VC.Sigma E0 (child s 2) = 0 :=
                  Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 2)
                    (by simpa [V, Vconcrete, E0] using hSs)
                    (by simpa [VC.runState, st] using hAllowed)
                simpa [V, Vconcrete, E0] using this
              have hnew : needs1b (E := E) V a W s.len = true → (2 : ℕ) = 1 := by
  -- Here `hk0 : ¬ decK s.len = k0` comes from the outer “not k0” branch split.
                have hk0ne : VC.decK s.len ≠ IPC.k0 := by simpa using hk0
                simpa using
    (eq_one_of_needs1b_true_of_decK_ne_k0 (V := V) (a := a) (W := W) (t := s.len) (q := 2) hk0ne)
              have hOKchild : StepsOK (E := E) V a W (child s 2) :=
                StepsOK_child_of_StepsOK (V := V) (a := a) (W := W) (s := s) (q := 2) hOKs hnew
              exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 2)).2 ⟨hSigmaChild, hOKchild⟩
            · -- F(child 1)=insert A
              simpa using (Fs_child_k2_split_one_eq_aux (E := E) (s := s) (A := A) (B := B) hk2 hW hp)
            · -- F(child 2)=insert B
              simpa using (Fs_child_k2_split_two_eq_aux (E := E) (s := s) (A := A) (B := B) hk2 hW hp)
            · -- disjunction is in F(s)
              -- We show it was inserted at time t-2 (a k0 step), because prev2=1.
              -- This uses the state/sequence alignment lemma for prev2.
              have htlen : st.t = s.len := ht
              have hp2 : 2 ≤ s.len :=
                -- if decK = k2 then s.len has remainder 2 mod 3, hence ≥ 2
                two_le_of_decK_eq_k2 (t := s.len) hk2
              have hprev2 : st.prev2 = s.seq ⟨s.len - 2, by omega⟩ := by
                -- use prev2 lemma on runStateAux
                have : (VC.runStateAux E0 s s.len le_rfl).prev2 = s.seq ⟨s.len - 2, by omega⟩ :=
                  runStateAux_prev2 (E0 := E0) (s := s) (n := s.len) (hn := le_rfl) (by simpa using hp2)
                simpa [VC.runState, st] using this
              have hq2 : s.seq ⟨s.len - 2, by omega⟩ = 1 := by simpa [hprev2, st, htlen] using hp
              -- At time t-2, we are at a k0 step with digit 1, so the formula Wn is inserted.
              -- Use the concrete monotonicity lemma `runStateAux_Fs_mono_le`.
              -- We'll show membership already holds at stage (t-1) and then grows.
              have hk0t2 : VC.decK (s.len - 2) = IPC.k0 := decK_sub2_of_decK_eq_k2 (t := s.len) hp2 hk2
              -- show membership in Fs after processing time (t-2)
              -- We use `runStateAux` at n=(t-1).
              let n1 : ℕ := (s.len - 2) + 1
              have hn1 : n1 ≤ s.len := by omega
              have hst1 :
    (VC.runStateAux E0 s n1 hn1).Fs = insert (E0.W (VC.decN (s.len - 2))) (VC.runStateAux E0 s (s.len - 2) (by omega)).Fs := by

                have hn2 : (s.len - 2).succ ≤ s.len := by omega
                have hq2' :
                    s.seq ⟨s.len - 2, by omega⟩ = 1 := hq2

                have hq2std :
                    s.seq ⟨(s.len - 2), Nat.lt_of_lt_of_le (Nat.lt_succ_self (s.len - 2)) hn2⟩ = 1 := by
                  have hi :
                      (⟨(s.len - 2), Nat.lt_of_lt_of_le (Nat.lt_succ_self (s.len - 2)) hn2⟩ : Fin s.len)
                        = ⟨s.len - 2, by omega⟩ := by
                    apply Fin.ext; rfl
                  simpa [hi] using hq2'

                simpa [n1, hn1] using
                  runStateAux_Fs_succ_k0_digit1 (E0 := E0) (s := s) (n := (s.len - 2)) (hn := hn2)
                    (hk0 := hk0t2) (hq := hq2std)
              have hIns : A ⋎ B = E0.W (VC.decN (s.len - 2)) := by

                have hW0 : E0.W (VC.decN s.len) = A ⋎ B := by
                  simpa [E0, toConcreteEnum] using hW

                have hdec : VC.decN (s.len - 2) = VC.decN s.len :=
                  decN_sub2_of_decK_eq_k2 (t := s.len) hk2

                have : E0.W (VC.decN (s.len - 2)) = A ⋎ B := by simpa [hdec] using hW0
                exact this.symm
              have hmem1 : (Form.or A B) ∈ (VC.runStateAux E0 s n1 hn1).Fs := by
                -- from the inserted form
                simp [hst1, hIns]

              have hmono : (VC.runStateAux E0 s n1 hn1).Fs ⊆ (VC.runStateAux E0 s s.len le_rfl).Fs :=
                VC.runStateAux_Fs_mono_le (E := E0) (s := s) (hn := hn1) (hm := le_rfl) (by omega)
              have hmemFinal : (Form.or A B) ∈ (VC.runStateAux E0 s s.len le_rfl).Fs := hmono hmem1
              -- rewrite to V.F
              simpa [V, Vconcrete, VC.FS, VC.runState, E0, st] using hmemFinal

          · -- not split (prev2 ≠ 1)
            refine Or.inl ?_
            refine ⟨0, ?_, ?_⟩
            · have hAllowed : VC.AllowedStepb E0 st 0 = true := by
                simpa [E0, st] using
    AllowedStepb_k2_or_prev2_ne_one_allow_0 (E := E) (s := s) (A := A) (B := B) hk2 hW hp
              have hSigmaChild : V.S (child s 0) = 0 := by
                have : VC.Sigma E0 (child s 0) = 0 :=
                  Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
                    (by simpa [V, Vconcrete, E0] using hSs)
                    (by simpa [VC.runState, st] using hAllowed)
                simpa [V, Vconcrete, E0] using this
              have hnew : needs1b (E := E) V a W s.len → (0 : ℕ) = 1 := by
                have hk0ne : VC.decK s.len ≠ IPC.k0 := by simpa using hk0
                simpa using
    (eq_one_of_needs1b_true_of_decK_ne_k0 (V := V) (a := a) (W := W) (t := s.len) (q := 0) hk0ne)
              have hOKchild : StepsOK (E := E) V a W (child s 0) :=
                StepsOK_child_of_StepsOK (V := V) (a := a) (W := W) (s := s) (q := 0) hOKs hnew
              exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 0)).2 ⟨hSigmaChild, hOKchild⟩
            · change (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs
              simpa [E0] using (Fs_child_k2_zero_eq (E := E) (s := s) hk2)

      | atom n =>
          refine Or.inl ?_
          refine ⟨0, ?_, ?_⟩
          · -- T(child 0)=0
            have hk2st : VC.decK st.t = IPC.k2 := by
              simpa [ht] using hk2
            have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
            have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
            have hWst : E0.W (VC.decN st.t) = (#n) := by
              simpa [E0, toConcreteEnum, ht] using hW

            have hAllowed : VC.AllowedStepb E0 st 0 = true := by
              unfold VC.AllowedStepb
              simp [hk2st, hk20, hk21, hWst]

            have hSsSigma : VC.Sigma E0 s = 0 := by
              simpa [V, Vconcrete, E0] using hSs
            have hSigmaChildSigma : VC.Sigma E0 (child s 0) = 0 :=
              Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
                hSsSigma (by simpa [st] using hAllowed)
            have hSigmaChild : V.S (child s 0) = 0 := by
              simpa [V, Vconcrete, E0] using hSigmaChildSigma


            have hnew : needs1b (E := E) V a W s.len = true → (0 : ℕ) = 1 := by
              intro hb
              have hk0_of_hb : VC.decK s.len = IPC.k0 :=
                k0_of_needs1b_true (V := V) (a := a) (W := W) (t := s.len) hb
              exact False.elim (hk0 hk0_of_hb)

            have hOKchild : StepsOK (E := E) V a W (child s 0) :=
              StepsOK_child_of_StepsOK (V := V) (a := a) (W := W)
                (s := s) (q := 0) hOKs hnew

            exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 0)).2
              ⟨hSigmaChild, hOKchild⟩
          ·
            have hFsRun :
                (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs := by
              simpa [E0] using (Fs_child_k2_zero_eq (E := E) (s := s) hk2)
            simpa [V, Vconcrete, VC.FS, E0] using hFsRun
            | bot =>
          refine Or.inl ?_
          refine ⟨0, ?_, ?_⟩
          ·
            have hk2st : VC.decK st.t = IPC.k2 := by simpa [ht] using hk2
            have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
            have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
            have hWst : E0.W (VC.decN st.t) = Form.bot := by
              simpa [E0, toConcreteEnum, ht] using hW

            have hAllowed : VC.AllowedStepb E0 st 0 = true := by
              unfold VC.AllowedStepb
              simp [hk2st, hk20, hk21, hWst]

            have hSsSigma : VC.Sigma E0 s = 0 := by
              simpa [V, Vconcrete, E0] using hSs
            have hSigmaChildSigma : VC.Sigma E0 (child s 0) = 0 :=
              Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
                hSsSigma (by simpa [st] using hAllowed)
            have hSigmaChild : V.S (child s 0) = 0 := by
              simpa [V, Vconcrete, E0] using hSigmaChildSigma

            have hnew : needs1b (E := E) V a W s.len = true → (0 : ℕ) = 1 := by
              intro hb
              have hk0_of_hb : VC.decK s.len = IPC.k0 :=
                k0_of_needs1b_true (V := V) (a := a) (W := W) (t := s.len) hb
              exact False.elim (hk0 hk0_of_hb)

            have hOKchild : StepsOK (E := E) V a W (child s 0) :=
              StepsOK_child_of_StepsOK (V := V) (a := a) (W := W)
                (s := s) (q := 0) hOKs hnew

            exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 0)).2
              ⟨hSigmaChild, hOKchild⟩
          ·
            have hFsRun :
                (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs := by
              simpa [E0] using (Fs_child_k2_zero_eq (E := E) (s := s) hk2)
            simpa [V, Vconcrete, VC.FS, E0] using hFsRun

            | imp P R =>
          refine Or.inl ?_
          refine ⟨0, ?_, ?_⟩
          ·
            have hk2st : VC.decK st.t = IPC.k2 := by simpa [ht] using hk2
            have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
            have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
            have hWst : E0.W (VC.decN st.t) = Form.imp P R := by
              simpa [E0, toConcreteEnum, ht] using hW

            have hAllowed : VC.AllowedStepb E0 st 0 = true := by
              unfold VC.AllowedStepb
              simp [hk2st, hk20, hk21, hWst]

            have hSsSigma : VC.Sigma E0 s = 0 := by
              simpa [V, Vconcrete, E0] using hSs
            have hSigmaChildSigma : VC.Sigma E0 (child s 0) = 0 :=
              Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
                hSsSigma (by simpa [st] using hAllowed)
            have hSigmaChild : V.S (child s 0) = 0 := by
              simpa [V, Vconcrete, E0] using hSigmaChildSigma

            have hnew : needs1b (E := E) V a W s.len = true → (0 : ℕ) = 1 := by
              intro hb
              have hk0_of_hb : VC.decK s.len = IPC.k0 :=
                k0_of_needs1b_true (V := V) (a := a) (W := W) (t := s.len) hb
              exact False.elim (hk0 hk0_of_hb)

            have hOKchild : StepsOK (E := E) V a W (child s 0) :=
              StepsOK_child_of_StepsOK (V := V) (a := a) (W := W)
                (s := s) (q := 0) hOKs hnew

            exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 0)).2
              ⟨hSigmaChild, hOKchild⟩
          ·
            have hFsRun :
                (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs := by
              simpa [E0] using (Fs_child_k2_zero_eq (E := E) (s := s) hk2)
            simpa [V, Vconcrete, VC.FS, E0] using hFsRun

            | and P R =>
          refine Or.inl ?_
          refine ⟨0, ?_, ?_⟩
          ·
            have hk2st : VC.decK st.t = IPC.k2 := by simpa [ht] using hk2
            have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
            have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
            have hWst : E0.W (VC.decN st.t) = Form.and P R := by
              simpa [E0, toConcreteEnum, ht] using hW

            have hAllowed : VC.AllowedStepb E0 st 0 = true := by
              unfold VC.AllowedStepb
              simp [hk2st, hk20, hk21, hWst]

            have hSsSigma : VC.Sigma E0 s = 0 := by
              simpa [V, Vconcrete, E0] using hSs
            have hSigmaChildSigma : VC.Sigma E0 (child s 0) = 0 :=
              Sigma_extend_of_Allowed (E0 := E0) (s := s) (q := 0)
                hSsSigma (by simpa [st] using hAllowed)
            have hSigmaChild : V.S (child s 0) = 0 := by
              simpa [V, Vconcrete, E0] using hSigmaChildSigma

            have hnew : needs1b (E := E) V a W s.len = true → (0 : ℕ) = 1 := by
              intro hb
              have hk0_of_hb : VC.decK s.len = IPC.k0 :=
                k0_of_needs1b_true (V := V) (a := a) (W := W) (t := s.len) hb
              exact False.elim (hk0 hk0_of_hb)

            have hOKchild : StepsOK (E := E) V a W (child s 0) :=
              StepsOK_child_of_StepsOK (V := V) (a := a) (W := W)
                (s := s) (q := 0) hOKs hnew

            exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := child s 0)).2
              ⟨hSigmaChild, hOKchild⟩
          ·
            have hFsRun :
                (VC.runState E0 (child s 0)).Fs = (VC.runState E0 s).Fs := by
              simpa [E0] using (Fs_child_k2_zero_eq (E := E) (s := s) hk2)
            simpa [V, Vconcrete, VC.FS, E0] using hFsRun

end StepRules

/-! ### Final: `impDataConcrete` -/
/-- Package the concrete subfan construction as the `ImpHardData` required for the implication case of the truth lemma (paper §4.1, propositional fragment). -/
def impDataConcrete (E : Enumerations) :
    ∀ (a : Branch (Vconcrete E)) (W Q : Form), ImpHardData (Vconcrete E) a W Q := by
  intro a W Q
  let V : VeldmanFan E := Vconcrete E
  let T : fin_seq → ℕ := Tlaw (E := E) V a W

  have hT : is_fan_law T := by

    simpa [T] using (Tlaw_is_fan_law (E := E) (V := V) (a := a) (W := W) rfl)

  have hsub : ∀ s : fin_seq, T s = 0 → V.S s = 0 := by
    intro s hs
    simpa [T] using (T_le_S (V := V) (a := a) (W := W) (s := s) hs)

  let toB : fan T hT → Branch V :=
    toBranchOfSubfan (V := V) (hT := hT) (hsub := hsub)

  have hRules : _root_.GammaRules.IndStepRules V a W Q T := by

    simpa [V, T] using (StepRules.stepRules (E := E) (a := a) (W := W) (Q := Q))

  refine
  { T := T
    hT := hT
    T_le_S := hsub
    toBranch := toB
    toBranch_coe := by
      intro b
      simp [toB]
    subfan_ok := by
      intro b
      have h :=
        ImplicationSubfan.subfan_ok (E := E) (V := V) (a := a) (W := W)
          (hV := rfl) (T := T) (hTdef := rfl) (hT := hT) b

      simpa [toB, hsub] using h
    stepRules := hRules



    ind_step := by
      intro s hs0 hall
      exact _root_.GammaRules.ind_step_of_rules
        (V := V) (a := a) (W := W) (Q := Q) (T := T)
        hRules s hs0 hall
  }

end ImplicationSubfan
