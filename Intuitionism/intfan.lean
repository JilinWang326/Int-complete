import Intuitionism.sketch
import Intuitionism.VeldmanConcrete
import Mathlib

set_option maxRecDepth 2000
set_option maxHeartbeats 0  -- 仅用于定位卡住点；定位完再撤掉
/-!
Todo B (propositional version): provide the `ImpHardData` needed for the implication-case
of the truth lemma in `sketch.lean`, without changing the existing setup.

This file works *on top of* the existing files you provided:
- `sketch.lean` (abstract completeness skeleton)
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

/-!
Todo B (propositional version): provide the `ImpHardData` needed for the implication-case
of the truth lemma in `sketch.lean`, without changing the existing setup.
-/

namespace TodoB
namespace VC
open NatSeq fin_seq IPC

export IPC.VeldmanConcrete
  ( Enumerations
    Sigma Sigma_is_fan_law
    FS FS_empty F_mono
    -- 下面这些是你后面证明里常用的（按需增删）
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

/-- `sketch.lean` 里的枚举类型（根命名空间）。 -/
abbrev ESk : Type := _root_.Enumerations
/-- `VeldmanConcrete.lean` 里的枚举类型（在 `IPC.VeldmanConcrete` 里）。 -/
abbrev ECon : Type := VC.Enumerations

/-- 把 sketch 的枚举数据“拷贝”成 concrete 的枚举数据（字段同名同型）。 -/
def toConcreteEnum (E : ESk) : ECon :=
{ W := E.W
, d := E.d
, W_surj := E.W_surj
, d_sound := E.d_sound
, d_complete := E.d_complete }

/-! ### The concrete fan as a `sketch.VeldmanFan` -/

/-- 具体扇：把 `IPC.VeldmanConcrete.Sigma/FS` 作为 `sketch.VeldmanFan` 的 S/F。 -/

def Vconcrete (E : ESk) : _root_.VeldmanFan E := by
  let E0 : ECon := toConcreteEnum E
  refine
  { S := VC.Sigma E0
    hS := VC.Sigma_is_fan_law E0
    F := VC.FS E0
    F_empty := by
      -- 这里 goal 是 `VC.FS E0 empty_seq = ∅`（定义展开后就是这个）
      simpa using (IPC.VeldmanConcrete.FS_empty (E := E0))
    F_mono := by
      intro s t hPre hs0 ht0
      -- 显式把 s t 喂进去，避免 `simpa using` 留 metavars
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
/-- 给定 `n ≤ s.len` 且 `0 < n`，构造索引 `(n-1) : Fin s.len`。 -/
def predIdx (s : fin_seq) (n : ℕ) (hn : n ≤ s.len) (hnpos : 0 < n) : Fin s.len := by
  cases n with
  | zero =>
      cases (Nat.lt_irrefl 0 hnpos)
  | succ k =>
      -- n = k+1，所以 n-1 = k，并且 k < s.len
      exact ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩

lemma runStateAux_prev1 (E0 : VC.Enumerations) (s : fin_seq) :
  ∀ n (hn : n ≤ s.len) (hnpos : 0 < n),
    (VC.runStateAux E0 s n hn).prev1 = s.seq (predIdx s n hn hnpos) := by
  intro n hn (hnpos : 0 < n)
  -- 现在 hnpos 的类型已经锁死为 0 < n，不会再变成 ?m.1
  let i : Fin s.len := predIdx s n hn hnpos
  change (VC.runStateAux E0 s n hn).prev1 = s.seq i
  -- 后面照你原来的 cases/simp 继续写
  cases n with
  | zero =>
      cases (Nat.lt_irrefl 0 hnpos)
  | succ k =>
      simp [VC.runStateAux, VC.step, VC.initState, predIdx, i]
      -- 如果 simp 卡在 Fin 证明不同上，再补：
      -- · apply congrArg s.seq; apply Fin.ext; rfl
/-- 你给的定义：n-2 的索引（用 omega 自动证明 n-2 < s.len）。 -/
def pred2Idx (s : fin_seq) (n : ℕ) (hn : n ≤ s.len) (hn2 : 2 ≤ n) : Fin s.len :=
  ⟨n - 2, by omega⟩

/-- `runStateAux` 在第 n 步（n≥2）时的 `prev2` 恰好等于第 (n-2) 个 digit。 -/
lemma runStateAux_prev2 (E0 : VC.Enumerations) (s : fin_seq) :
    ∀ n (hn : n ≤ s.len) (hn2 : 2 ≤ n),
      (VC.runStateAux E0 s n hn).prev2
        = s.seq (pred2Idx s n hn hn2) := by
  intro n hn hn2
  cases n with
  | zero =>
      -- 2 ≤ 0 不可能
      cases (by omega : False)
  | succ n =>
      cases n with
      | zero =>
          -- 2 ≤ 1 不可能
          cases (by omega : False)
      | succ k =>
          -- 现在原来的 n = k+2
          -- 先从 hn : k+2 ≤ s.len 推出 hn1 : k+1 ≤ s.len
          have hn1 : k + 1 ≤ s.len := by
            exact Nat.le_trans (Nat.le_succ (k + 1)) hn

          -- 第一步：展开 runStateAux 的 succ，prev2 会变成“前一状态的 prev1”
          have hstep :
              (VC.runStateAux E0 s (k + 2) hn).prev2
                = (VC.runStateAux E0 s (k + 1) hn1).prev1 := by
            -- runStateAux (n+1) = step st q，step 里 prev2 := st.prev1
            simp [VC.runStateAux, VC.step]

          -- 第二步：展开前一状态的 prev1，它就是第 k 个 digit
          have hk_lt : k < s.len := by omega
          have hprev1 :
              (VC.runStateAux E0 s (k + 1) hn1).prev1
                = s.seq ⟨k, hk_lt⟩ := by
            -- runStateAux (k+1) = step (runStateAux k) (s.seq k)
            simp [VC.runStateAux, VC.step, hk_lt]

          -- 第三步：把右边的 `⟨k, hk_lt⟩` 对齐到 `pred2Idx ...`
          have hFin :
              (⟨k, hk_lt⟩ : Fin s.len) = pred2Idx s (k + 2) hn (by omega) := by
            apply Fin.ext
            -- (k+2)-2 = k
            simp [pred2Idx]

          -- 合并
          calc
            (VC.runStateAux E0 s (k + 2) hn).prev2
                = (VC.runStateAux E0 s (k + 1) hn1).prev1 := hstep
            _   = s.seq ⟨k, hk_lt⟩ := hprev1
            _   = s.seq (pred2Idx s (k + 2) hn (by omega)) := by
                    simpa [hFin]

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

  have hDigit : c.seq ⟨s.len, by
      simp [c, child, fin_seq.extend, fin_seq.singleton]⟩ = q := by
    simpa [c, child] using VC.extend_singleton_last s q

  have hAllowedChild :
      VC.AllowedStepb E0 (VC.runStateAux E0 c s.len hPred)
        (c.seq ⟨s.len, by simp [c, child, fin_seq.extend, fin_seq.singleton]⟩) = true := by
    simpa [VC.runState, hStateEq, hDigit] using hAllowed

  have hcAux_succ :
      VC.admittedAuxb E0 c s.len.succ (by
        simp [c, child, fin_seq.extend, fin_seq.singleton]) = true := by
    simp [VC.admittedAuxb, hcAux_pred, hAllowedChild]

  have hcAd : VC.Admittedb E0 c = true := by
    simpa [VC.Admittedb, c, child] using hcAux_succ
  exact (VC.Sigma_eq_zero_iff E0 c).2 hcAd

/-! ### The subfan law `T` (Todo B) -/

/-- k0 时刻，且当前公式已在有限集合 F(α↾(t+1)) 中，或等于 W。全部可判定 → Bool。 -/
def needs1b {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ) : Bool :=
  decide (VC.decK t = IPC.k0) &&
    (decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t+1))) ||
     decide (E.W (VC.decN t) = W))

/-- 递归检查：前 k 个位置（0..k-1）里，所有 needs1b 的位置 digit=1。k ≤ s.len。 -/
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

/-- 全部位置的检查（k = s.len）。 -/
def StepsOKb {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) : Bool :=
  StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl

/-- Prop 版 StepsOK：就是 Bool 版等于 true。这个当然可判定（Bool 等式）。 -/
def StepsOK {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) : Prop :=
  StepsOKb (V := V) (a := a) (W := W) s = true

instance {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) :
    Decidable (StepsOK (V := V) (a := a) (W := W) s) :=
by
  -- Bool 等式的 decidable 是构造性的
  dsimp [StepsOK]
  infer_instance

def Tlaw {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) : fin_seq → ℕ :=
  fun s =>
    match V.S s with
    | 0   => if StepsOKb (V := V) (a := a) (W := W) s then 0 else 1
    | _+1 => 1

/-- 便于后续用的展开引理：Tlaw=0 ↔ Σ=0 ∧ StepsOKb=true -/
lemma Tlaw_eq_zero_iff {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (s : fin_seq) :
    Tlaw (V := V) (a := a) (W := W) s = 0
      ↔ (V.S s = 0 ∧ StepsOK (V := V) (a := a) (W := W) s) := by
  unfold Tlaw StepsOK StepsOKb
  cases hS : V.S s with
  | zero =>
      simp [hS, StepsOKb, StepsOKbUpTo]
  | succ n =>
      simp [hS]

lemma T_le_S {E : Enumerations} (V : VeldmanFan E) (a : Branch V) (W : Form) :
    ∀ s : fin_seq, Tlaw (E := E) V a W s = 0 → V.S s = 0 := by
  intro s hs
  exact (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := s)).1 hs |>.1

/-- 从 `UpTo (k+1)=true` 推回 `UpTo k=true`（因为定义里是 `UpTo k && ...`）。 -/
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







/-- child 的前 k 步检查等于原 s 的前 k 步检查（k ≤ s.len）。 -/
lemma StepsOKbUpTo_child_eq {E : ESk}
    (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (s : fin_seq) (q : ℕ) :
    ∀ k (hk : k ≤ s.len),
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q) k
          (Nat.le_trans hk (by
            -- k ≤ s.len ≤ (child s q).len
            simpa [child, fin_seq.extend, fin_seq.singleton] using Nat.le_succ s.len))
      =
      StepsOKbUpTo (V := V) (a := a) (W := W) s k hk := by
  intro k hk
  induction k with
  | zero =>
      simp [StepsOKbUpTo]
  | succ k ih =>
      have hk' : k ≤ s.len := Nat.le_of_succ_le hk
      have hkChild : k.succ ≤ (child s q).len := by
        -- k+1 ≤ s.len ≤ s.len+1 = child.len
        refine Nat.le_trans hk ?_
        simpa [child, fin_seq.extend, fin_seq.singleton] using Nat.le_succ s.len
      have hkChild' : k ≤ (child s q).len := Nat.le_of_succ_le hkChild

      -- 这一层需要用到：当 k < s.len 时，child.seq 在索引 k 处等于 s.seq 在索引 k 处
      have hlt : k < s.len := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hltChild : k < (child s q).len :=
        Nat.lt_of_lt_of_le hlt (by
          simpa [child, fin_seq.extend, fin_seq.singleton] using Nat.le_succ s.len)

      let iS : Fin s.len := ⟨k, hlt⟩
      let iC : Fin (child s q).len := ⟨k, hltChild⟩

      have hseq : (child s q).seq iC = s.seq iS := by
        -- 因为 k < s.len，所以 extend 的旧位置直接回到 s
        simp [child, fin_seq.extend, fin_seq.singleton, hlt, iS, iC]

      -- 展开 StepsOKbUpTo 在 succ 处，左右各自都是 “递归 && (if needs1b k then decide(seq=1) else true)”
      simp [StepsOKbUpTo, hk, hkChild, hk', hkChild', ih hk', hseq, iS, iC]

/-- 你真正想用的：`child` 的 StepsOKbUpTo(full) 为真 ⇒ `s` 的 StepsOKbUpTo(full) 为真。 -/
lemma StepsOKbUpTo_prefix_child {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (s : fin_seq) (q : ℕ) :
    StepsOKbUpTo (V := V) (a := a) (W := W) (child s q)
        (child s q).len le_rfl = true →
    StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl = true := by
  intro h
  -- 先把 child.len 化简成 s.len.succ
  have hlen : (child s q).len = s.len.succ := by
    simp [child, fin_seq.extend, fin_seq.singleton]
  -- 把 h 改写成 UpTo (s.len.succ)
  have h' :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q)
        s.len.succ (by simpa [hlen]) = true := by
    simpa [hlen] using h
  -- 去掉最后一格：得到 UpTo s.len
  have hdown :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q)
        s.len (Nat.le_of_succ_le (by simpa [hlen] using (le_rfl : s.len.succ ≤ (child s q).len))) = true := by
    -- 用 pred_true
    exact StepsOKbUpTo_pred_true (V := V) (a := a) (W := W) (s := child s q)
        (k := s.len) (hk := by simpa [hlen] using (le_rfl : s.len.succ ≤ (child s q).len)) h'

  -- 把 child 的 UpTo s.len 改写成 s 的 UpTo s.len
  have heq :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q)
        s.len (Nat.le_trans (le_rfl : s.len ≤ s.len)
          (by simpa [child, fin_seq.extend, fin_seq.singleton] using (Nat.le_succ s.len)))
      =
      StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl :=
    StepsOKbUpTo_child_eq (V := V) (a := a) (W := W) (s := s) (q := q) s.len le_rfl

  -- 两个 hk 证明可能不是 definitional 相等：用 heq 把目标那边换掉即可
  -- 这里用 `simpa [heq]` 收尾
  simpa [heq] using hdown

/-- 从 StepsOK s 推出 StepsOK (child s q)，最后一位用 hnew 强制 q=1。 -/
lemma StepsOK_child_of_StepsOK {E : ESk}
    (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (s : fin_seq) (q : ℕ)
    (hS : StepsOK (V := V) (a := a) (W := W) s)
    (hnew : needs1b (V := V) (a := a) (W := W) s.len = true → q = 1) :
    StepsOK (V := V) (a := a) (W := W) (child s q) := by
  -- 展开 StepsOK/StepsOKb
  unfold StepsOK at hS ⊢
  unfold StepsOKb at hS ⊢

  -- child.len = s.len + 1，所以 StepsOKb(child) = StepsOKbUpTo(child) (s.len+1) ...
  -- 我们先把目标展开一层（k+1 情形）
  have hlen : (child s q).len = s.len + 1 := by
    simp [child, fin_seq.extend, fin_seq.singleton]

  -- 把目标化成 “前 s.len 步 && 最后一位检查”
  -- 注意：StepsOKbUpTo 的 (k+1) 分支会在索引 k= s.len 处检查 digit
  -- 所以这里 k = s.len
  -- 先把 child 的前 s.len 步检查换回 s 的前 s.len 步检查
  have hPrefixEq :
      StepsOKbUpTo (V := V) (a := a) (W := W) (child s q) s.len
          (Nat.le_trans le_rfl (by
            simpa [hlen] using Nat.le_succ s.len))
      =
      StepsOKbUpTo (V := V) (a := a) (W := W) s s.len le_rfl :=
    StepsOKbUpTo_child_eq (V := V) (a := a) (W := W) (s := s) (q := q) s.len le_rfl

  -- 现在展开 StepsOKbUpTo(child) 在 (s.len+1)
  -- 其形式是：prefix && (if needs1b s.len then decide(lastDigit=1) else true)
  -- lastDigit = q
  have hLast : (child s q).seq ⟨s.len, by
      -- s.len < child.len
      simpa [hlen] using Nat.lt_succ_self s.len
    ⟩ = q := by
    simpa [child] using (VC.extend_singleton_last s q)

  -- 对 needs1b(s.len) 分情况
  by_cases hb : needs1b (V := V) (a := a) (W := W) s.len
  · -- hb : needs1b ... s.len = true
    have hq : q = 1 := hnew hb
    subst hq
    -- 目标 becomes: (prefix = true) && decide(1=1)=true
    -- prefix = StepsOKb s = true，由 hS 得到
    -- decide(...) = true by simp
    -- 直接 simp 即可
    -- 先把 prefix 部分换成 s 的 prefix
    -- 再用 hS
    simp [StepsOKbUpTo, hlen, hPrefixEq, hS, hb, hLast]
  · -- hb : needs1b ... s.len = false
    -- 最后一项 if ... else true 直接为 true，不需要约束 q
    simp [StepsOKbUpTo, hlen, hPrefixEq, hS, hb, hLast]

lemma StepsOK_empty {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) :
    StepsOK (E := E) V a W empty_seq := by
  -- StepsOK = (StepsOKb = true)
  dsimp [StepsOK, StepsOKb]
  -- 目标变成：StepsOKbUpTo ... empty_seq empty_seq.len le_rfl = true

  -- 关键：把 empty_seq.len 化成 0
  have hlen : empty_seq.len = 0 := by
    -- 这一步通常就够了；如果你 empty_seq 的名字在别的 namespace，
    -- 就把 [empty_seq] 换成你实际的定义名
    simp [empty_seq]

  -- 用 hlen 改写目标，StepsOKbUpTo 的 0 分支就是 true
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
  -- unfold AllowedStepb: 在 k0 分支里要么 decide (1=1) 要么 decide(1=0 ∨ 1=1)，都为 true
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
    -- 你已经有 runState_t : (VC.runState E0 s).t = s.len
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
    -- 因为 V.S = Sigma E0 （在 Vconcrete 的定义里）
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

    -- 拆 && = true
    have hsplit :
        decide ((E0.d i).2 = E0.W (VC.decN st.t)) = true ∧
        decide ((E0.d i).1 ⊆ st.Fs) = true :=
      by exact Bool.and_eq_true_iff.mp hpi

    have hEq : (E0.d i).2 = E0.W (VC.decN st.t) :=
      (_root_.decide_eq_true_iff).1 hsplit.1

    have hSub : (E0.d i).1 ⊆ st.Fs :=
      (_root_.decide_eq_true_iff).1 hsplit.2

    exact ⟨i, hi, ⟨hEq, hSub⟩⟩
  · -- hk0 false 时 Forced0b = false，所以 h 不可能
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

  -- 记 t = child s q
  let t : fin_seq := child s q

  -- t.len = s.len + 1 = s.len.succ
  have hlen : t.len = s.len.succ := by
    -- simp 先出 s.len + 1，再用 succ_eq_add_one
    have : t.len = s.len + 1 := by
      simp [t, child, fin_seq.extend, fin_seq.singleton]
    simpa [Nat.succ_eq_add_one] using this

  -- s.len ≤ t.len
  have hle : s.len ≤ t.len := by
    simpa [hlen] using (Nat.le_succ s.len)

  -- Prefix s t
  have hPref : Prefix s t := VC.Prefix_child s q

  -- Prefix 等价：runStateAux 在公共前缀长度 s.len 上相同
  have hEqPrefix :
      VC.runStateAux E0 t s.len (Nat.le_trans le_rfl (VC.Prefix_len_le hPref))
        = VC.runStateAux E0 s s.len le_rfl :=
    VC.runStateAux_eq_of_Prefix (E := E0) (h := hPref) s.len le_rfl

  -- 把 hEqPrefix 左边的“≤证明”换成我们想用的 hle（靠 proof-irrelevance）
  have hEq :
      VC.runStateAux E0 t s.len hle = VC.runStateAux E0 s s.len le_rfl := by
    calc
      VC.runStateAux E0 t s.len hle
          = VC.runStateAux E0 t s.len (Nat.le_trans le_rfl (VC.Prefix_len_le hPref)) := by
              symm
              exact VC.runStateAux_proof_irrel (E := E0) (s := t) s.len
                hle (Nat.le_trans le_rfl (VC.Prefix_len_le hPref))
      _ = VC.runStateAux E0 s s.len le_rfl := hEqPrefix

  -- t.seq 在位置 s.len 的 digit 就是 q（要对齐 Fin 的 proof）
  have hDigit :
      t.seq ⟨s.len, by
        -- s.len < t.len
        simpa [hlen] using Nat.lt_succ_self s.len
      ⟩ = q := by
    -- 先用 VeldmanConcrete.extend_singleton_last 得到一个“标准 proof”的索引版本
    have h' :
        t.seq ⟨s.len, by
          simp [t, child, fin_seq.extend, fin_seq.singleton]
        ⟩ = q := by
      simpa [t, child] using VC.extend_singleton_last s q
    -- 两个 Fin 索引 val 相同，只是证明不同，用 Fin.ext 对齐
    have hFin :
        (⟨s.len, by simpa [hlen] using Nat.lt_succ_self s.len⟩ : Fin t.len)
          = ⟨s.len, by simp [t, child, fin_seq.extend, fin_seq.singleton]⟩ := by
      apply Fin.ext; rfl
    simpa [hFin] using h'

  -- 展开 runState(t) = runStateAux t t.len，化简一次 runStateAux 的 succ 分支
  -- 注意：runStateAux 的 succ 分支里会用 `Nat.le_of_succ_le` 从 (s.len+1 ≤ t.len) 得到 (s.len ≤ t.len)，
  -- 这也是一个“≤证明”，用 proof-irrelevance 换成 hle
  have hpi :
      VC.runStateAux E0 t s.len (Nat.le_of_succ_le (by
        -- (s.len.succ ≤ t.len) 由 hlen 得到
        simpa [hlen] using (le_rfl : s.len.succ ≤ s.len.succ)
      )) = VC.runStateAux E0 t s.len hle := by
    exact VC.runStateAux_proof_irrel (E := E0) (s := t) s.len
      (Nat.le_of_succ_le (by simpa [hlen] using (le_rfl : s.len.succ ≤ s.len.succ)))
      hle

  -- 最后一步：把 runStateAux(t, s.len) 换成 runStateAux(s, s.len)，digit 换成 q
  -- 就得到 step E0 (runState E0 s) q
  simp [VC.runState, t, hlen, VC.runStateAux, VC.step, hpi, hEq, hDigit]
    -- 由 state 等式推出各字段等式
  refine And.intro ?_ (And.intro ?_ ?_)
  · -- t 字段相等
    simpa using congrArg (fun st => st.t) hEq
  · -- prev1 字段相等
    simpa using congrArg (fun st => st.prev1) hEq
  · -- FStep 在同一个 state 上重写
    -- 这里不用 VC.FStep，直接用全名最稳
    simpa using congrArg (fun st => IPC.VeldmanConcrete.FStep E0 st q) hEq

/-! ### Subfan property (paper 4.1(i) in propositional form): Γα ⊆ Γβ and W ∈ Γβ -/



/-- Prefix relation between two finitize prefixes of the same infinite sequence. -/
lemma Prefix_finitize (α : NatSeq) {n m : ℕ} (h : n ≤ m) :
    Prefix (finitize α n) (finitize α m) := by
  refine ⟨h, ?_⟩
  intro i
  rfl

/-- A simple lower bound: the scheduling time `schedEncode ⟨n, m, k0⟩` is at least `m`. -/

lemma le_schedEncode_k0 (n m : ℕ) : m ≤ IPC.schedEncode ⟨n, m, IPC.k0⟩ := by
  -- unfold schedEncode, k0; goal becomes `m ≤ 3 * Nat.pair n m`
  simp [IPC.schedEncode, IPC.k0]

  have hpair : m ≤ Nat.pair n m := Nat.right_le_pair n m

  -- m = 1*m ≤ 3*m
  have hm : m ≤ 3 * m := by
    simpa [Nat.one_mul] using
      (Nat.mul_le_mul_right m (show (1 : ℕ) ≤ 3 by decide))

  -- 3*m ≤ 3*(pair n m)
  have hmul : (3 * m : ℕ) ≤ (3 * Nat.pair n m : ℕ) := by
    exact Nat.mul_le_mul_left 3 hpair

  exact le_trans hm hmul

lemma Prefix_finitize_le (x : 𝒩) {m n : ℕ} (h : m ≤ n) :
    Prefix (finitize x m) (finitize x n) := by
  refine ⟨h, ?_⟩
  intro i
  -- 两边都是 x i.val
  rfl
lemma needs1b_true_of_k0_mem
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ)
    (hk0 : VC.decK t = IPC.k0)
    (hmem : E.W (VC.decN t) ∈ V.F (finitize a.1 (t+1))) :
    needs1b (V := V) (a := a) (W := W) t = true := by
  unfold needs1b
  -- 拆成 decide(...) && (decide(mem) || decide(eq))
  have hk0' : decide (VC.decK t = IPC.k0) = true :=
    (_root_.decide_eq_true_iff).2 hk0
  have hmem' : decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t+1))) = true :=
    (_root_.decide_eq_true_iff).2 hmem
  -- 左边 true，右边 or 的左支 true ⇒ 整体 true
  simp [hk0', hmem']
lemma StepsOK_finitize_digit_eq_one
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (bseq : 𝒩) (t : ℕ)
    (hSteps : StepsOK (V := V) (a := a) (W := W) (finitize bseq (t+1)))
    (hneed : needs1b (V := V) (a := a) (W := W) t = true) :
    bseq t = 1 := by
  -- StepsOK 是 Prop：StepsOKb = true
  unfold StepsOK at hSteps
  unfold StepsOKb at hSteps
  -- 展开 StepsOKbUpTo 在 (t+1) 这一层，只展开一层即可
  have hLayer :
      StepsOKbUpTo (V := V) (a := a) (W := W) (finitize bseq (t+1)) (t+1) le_rfl = true := hSteps

  -- 展开 succ 分支：prefix && (if needs1b t then decide(seq=1) else true)
  have hAnd :
      StepsOKbUpTo (V := V) (a := a) (W := W) (finitize bseq (t+1)) t (Nat.le_of_succ_le le_rfl)
        &&
      (if needs1b (V := V) (a := a) (W := W) t then
          decide ((finitize bseq (t+1)).seq ⟨t, Nat.lt_succ_self t⟩ = 1)
       else true)
      = true := by
    simpa [StepsOKbUpTo] using hLayer

  have hLast :
      (if needs1b (V := V) (a := a) (W := W) t then
          decide ((finitize bseq (t+1)).seq ⟨t, Nat.lt_succ_self t⟩ = 1)
       else true)
      = true := by exact Bool.and_elim_right hSteps

  -- 由于 hneed=true，if 分支落到 decide(...)
  have hDec :
      decide ((finitize bseq (t+1)).seq ⟨t, Nat.lt_succ_self t⟩ = 1) = true := by
    simpa [hneed] using hLast

  have hEq :
      (finitize bseq (t+1)).seq ⟨t, Nat.lt_succ_self t⟩ = 1 :=
    (_root_.decide_eq_true_iff).1 hDec

  -- finitize 的 seq 在索引 t 处就是 bseq t
  simpa [fin_seq.finitize] using hEq

/-- `finitize b (t+1)` 等于把 `finitize b t` 用最后一位 `b t` 扩展一格。 -/
lemma finitize_succ_eq_child (bseq : 𝒩) (t : ℕ) :
    finitize bseq (t+1) = child (finitize bseq t) (bseq t) := by
  -- 两边长度都是 t+1
  have hlen :
      (finitize bseq (t+1)).len = (child (finitize bseq t) (bseq t)).len := by
    simp [child, fin_seq.extend, fin_seq.singleton, fin_seq.finitize]

  -- 用 fan.lean 里的 ext_cast
  apply ext_cast hlen
  intro i

  -- 先把 cast 消掉（因为 hlen 其实就是 rfl 形态）
  have hcast : (Fin.cast hlen i).1 = i.1 := rfl

  by_cases hi : i.1 < t
  · -- i < t：extend 走左侧（prefix）分支
    -- LHS = bseq i, RHS = (finitize bseq t).seq ... = bseq i
    simp [fin_seq.finitize, child, fin_seq.extend, fin_seq.singleton, hi, hcast]
  · -- i ≥ t：由于 i < t+1，只能是 i = t
    have hi_le : i.1 ≤ t := Nat.le_of_lt_succ (by
      -- i.2 : i.val < (t+1) （因为 i : Fin (t+1)）
      simpa [fin_seq.finitize] using i.2)
    have hi_eq : i.1 = t := (Nat.lt_or_eq_of_le hi_le).resolve_left hi

    -- RHS 走 extend 的 else 分支，singleton 的索引是 (i.val - t)=0
    -- LHS 在 i=t 时就是 bseq t
    simp [fin_seq.finitize, child, fin_seq.extend, fin_seq.singleton, hi, hi_eq, hcast]

/-- 从 Bool 版 StepsOK + needs1b=true 推出第 t0 位 digit=1（用于 t0+1 长度前缀）。 -/
lemma digit_one_of_StepsOK_of_needs1b
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form)
    (bseq : 𝒩) (t0 : ℕ)
    (hSteps : StepsOK (V := V) (a := a) (W := W) (finitize bseq (t0 + 1)))
    (hneed : needs1b (V := V) (a := a) (W := W) t0 = true) :
    (finitize bseq (t0 + 1)).seq ⟨t0, Nat.lt_succ_self t0⟩ = 1 := by

  let s1 : fin_seq := finitize bseq (t0 + 1)

  -- 展开 StepsOK / StepsOKb
  have hStepsb : StepsOKb (V := V) (a := a) (W := W) s1 = true := by
    simpa [StepsOK, s1] using hSteps

  unfold StepsOKb at hStepsb

  -- hUp : StepsOKbUpTo ... (t0+1) ... = true
  have hUp : StepsOKbUpTo (V := V) (a := a) (W := W) s1 (t0 + 1) (by
      -- (t0+1) ≤ s1.len
      simpa [s1, fin_seq.finitize_len] using (le_rfl : t0 + 1 ≤ t0 + 1)
    ) = true := by
    simpa [s1, fin_seq.finitize_len] using hStepsb

  -- 定义 hk / hk'，保证和 StepsOKbUpTo 递归里生成的 proof 对齐
  have hk : t0 + 1 ≤ s1.len := by
    simpa [s1, fin_seq.finitize_len] using (le_rfl : t0 + 1 ≤ t0 + 1)
  let hk' : t0 ≤ s1.len := Nat.le_of_succ_le hk

  -- 关键：把 StepsOKbUpTo 在 (t0+1) 展开成 “prefix && last”
  have hUpAnd :
      StepsOKbUpTo (V := V) (a := a) (W := W) s1 t0 hk' &&
        (if needs1b (V := V) (a := a) (W := W) t0 = true then
            decide (s1.seq ⟨t0, by
              -- t0 < s1.len
              simpa [s1, fin_seq.finitize_len] using Nat.lt_succ_self t0
            ⟩ = 1)
         else true)
      = true := by
    -- 注意：这里第二项就是那个 Bool 本身，不要包一层 decide((...)=true)
    -- 直接对 StepsOKbUpTo 的递归方程 simp
    simpa [StepsOKbUpTo, hk, hk', s1, fin_seq.finitize_len] using hUp

  -- 用 Eq.mp (Bool.and_eq_true _ _) 拆出两个子句
  have hAnd :
      StepsOKbUpTo (V := V) (a := a) (W := W) s1 t0 hk' = true ∧
      (if needs1b (V := V) (a := a) (W := W) t0 = true then
          decide (s1.seq ⟨t0, by
            simpa [s1, fin_seq.finitize_len] using Nat.lt_succ_self t0
          ⟩ = 1)
       else true) = true := by
    exact Bool.and_eq_true_iff.mp hSteps

  -- 用 hneed 选中 then 分支，得到 decide(seq=1)=true
  have hDec :
      decide (s1.seq ⟨t0, by
        simpa [s1, fin_seq.finitize_len] using Nat.lt_succ_self t0
      ⟩ = 1) = true := by
    simpa [hneed] using hAnd.2

  have hEq : s1.seq ⟨t0, by
        simpa [s1, fin_seq.finitize_len] using Nat.lt_succ_self t0
      ⟩ = 1 :=
    (_root_.decide_eq_true_iff).1 hDec

  -- 把 s1 展开回 finitize bseq (t0+1)
  simpa [s1] using hEq
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
    (T : fin_seq → ℕ) (hTdef : T = Tlaw (E := E) V a W)
    (hT : is_fan_law T)
    (b : fan T hT) :
    (Gamma V a ⊆
        Gamma V
          (toBranchOfSubfan V hT (fun s hs => by
              subst hV
              subst hTdef
              exact T_le_S (V := Vconcrete E) (a := a) (W := W) (s := s) hs) b)) ∧
      W ∈
        Gamma V
          (toBranchOfSubfan V hT (fun s hs => by
              subst hV
              subst hTdef
              exact T_le_S (V := Vconcrete E) (a := a) (W := W) (s := s) hs) b) := by
  subst hV
  subst hTdef
  -- From now on, `V` is the concrete fan and `T` is our `Tlaw`.
  let V : VeldmanFan E := Vconcrete E
  let T : fin_seq → ℕ := Tlaw (E := E) V a W
  let β : Branch V := toBranchOfSubfan V hT (T_le_S (V := V) (a := a) (W := W)) b
  have hbSeq : β.1 = b.1 := rfl

  refine ⟨?_, ?_⟩
  · -- Γ_a ⊆ Γ_β
    intro p hp
    rcases hp with ⟨nA, hpA⟩
    -- Pick an index enumerating `p`.
    rcases E.W_surj p with ⟨n0, rfl⟩

    -- Choose a scheduling time that is *after* the witness `nA`,
    -- so that `E.W n0` is already in `F(prefix a t0)` by monotonicity.
    let t0 : ℕ := IPC.schedEncode ⟨n0, nA, IPC.k0⟩
    have hk0 : VC.decK t0 = IPC.k0 := by
      simp [t0, VC.decK, IPC.schedDecode_encode]
    have hdecN : VC.decN t0 = n0 := by
      simp [t0, VC.decN, IPC.schedDecode_encode]

    have hle : nA ≤ t0 := le_schedEncode_k0 n0 nA
    have hPref : Prefix (finitize a.1 nA) (finitize a.1 t0) := Prefix_finitize a.1 hle
    have hmono : V.F (finitize a.1 nA) ⊆ V.F (finitize a.1 t0) :=
      V.F_mono hPref (a.2 nA) (a.2 t0)
    have hmemA : E.W n0 ∈ V.F (finitize a.1 t0) := hmono hpA

    -- 先把 hmemA 提升到 t0+1（因为 needs1b 看的是 t+1）
    have hPref01 : Prefix (finitize a.1 t0) (finitize a.1 (t0+1)) :=
  Prefix_finitize_le a.1 (Nat.le_succ t0)
    have hmono01 : V.F (finitize a.1 t0) ⊆ V.F (finitize a.1 (t0+1)) :=
  V.F_mono hPref01 (a.2 t0) (a.2 (t0+1))
    have hmemA1 : E.W n0 ∈ V.F (finitize a.1 (t0+1)) := hmono01 hmemA

    have hneed : needs1b (V := V) (a := a) (W := W) t0 = true :=
  needs1b_true_of_k0_mem (V := V) (a := a) (W := W) (t := t0) hk0 (by simpa [hdecN] using hmemA1)

    -- Extract `b[t0] = 1` from StepsOK on the prefix of length `t0+1`.
    have hb0 : T (finitize b.1 (t0 + 1)) = 0 := b.2 (t0 + 1)
    have hbSteps : StepsOK V a W (finitize b.1 (t0 + 1)) :=
      (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := finitize b.1 (t0 + 1))).1 hb0 |>.2
    have hb0 : T (finitize b.1 (t0 + 1)) = 0 := b.2 (t0 + 1)
    have hbSteps : StepsOK (V := V) (a := a) (W := W) (finitize b.1 (t0+1)) :=
  (Tlaw_eq_zero_iff (V := V) (a := a) (W := W) (s := finitize b.1 (t0+1))).1 hb0 |>.2

    have hbDigit : b.1 t0 = 1 :=
  StepsOK_finitize_digit_eq_one (V := V) (a := a) (W := W) (bseq := b.1) (t := t0) hbSteps hneed

    -- Show that at stage `t0+1`, `E.W n0` is inserted into `F` along `b`.
    let s0 : fin_seq := finitize b.1 t0
    have hs0 : finitize b.1 (t0+1) = child s0 1 := by
  -- 先用通用等式，再用 hbDigit 把 b t0 改成 1
      have : finitize b.1 (t0+1) = child (finitize b.1 t0) (b.1 t0) :=
    finitize_succ_eq_child (bseq := b.1) (t := t0)
      simpa [s0, hbDigit] using this


  -- 先把 V.F 改写成 concrete 的 FS，再改写成 runState.Fs
    sorry

  · -- W ∈ Γ_β
    rcases E.W_surj W with ⟨n0, rfl⟩
    let t0 : ℕ := IPC.schedEncode ⟨n0, 0, IPC.k0⟩
    have hk0 : VC.decK t0 = IPC.k0 := by
      simp [t0, VC.decK, IPC.schedDecode_encode]
    have hdecN : VC.decN t0 = n0 := by
      simp [t0, VC.decN, IPC.schedDecode_encode]

    -- 你要的：needs1b V a (E.W n0) t0 = true
    have hneedW : needs1b (E := E) V a (E.W n0) t0 = true := by
  -- needs1b = decide(k=k0) && (decide(mem) || decide(eq))
      unfold needs1b
  -- 把 decide(k=k0) 变成 true
      have hk0d : decide (VC.decK t0 = IPC.k0) = true := by
        exact (_root_.decide_eq_true_iff).2 hk0
  -- 把 decide(E.W(decN t0) = E.W n0) 变成 true（用 hdecN）
      have heqd : decide (E.W (VC.decN t0) = E.W n0) = true := by
    -- 先把等式化简成 rfl
        have : E.W (VC.decN t0) = E.W n0 := by simpa [hdecN]
        exact (_root_.decide_eq_true_iff).2 this
  -- 收尾：true && (_ || true) = true
      simp [hk0d, heqd]

    have hb0 : T (finitize b.1 (t0 + 1)) = 0 := b.2 (t0 + 1)
    have hbSteps : StepsOK V a (E.W n0) (finitize b.1 (t0 + 1)) :=
      (Tlaw_eq_zero_iff (V := V) (a := a) (W := E.W n0) (s := finitize b.1 (t0 + 1))).1 hb0 |>.2
    -- s1 := finitize (↑b) (t0+1)
    let bseq : 𝒩 := b.1
    have hbDigit :
    (finitize bseq (t0 + 1)).seq ⟨t0, Nat.lt_succ_self t0⟩ = 1 := by
      exact
    (digit_one_of_StepsOK_of_needs1b
      (V := V) (a := a) (W := E.W n0) (bseq := bseq) (t0 := t0)
      (by simpa [bseq] using hbSteps)
      hneedW)
    have hbDigitNat : bseq t0 = 1 := by
  -- hbDigit : (finitize bseq (t0+1)).seq ⟨t0, _⟩ = 1
  -- finitize 的 seq 定义就是 bseq i.val
      simpa [fin_seq.finitize] using hbDigit
    let s0 : fin_seq := finitize b.1 t0
    have hs0 : finitize bseq (t0 + 1) = child s0 1 := by
      have h : finitize bseq (t0 + 1) = child (finitize bseq t0) (bseq t0) :=
    finitize_succ_eq_child bseq t0
  -- 用 hbDigitNat 把 bseq t0 改成 1
      simpa [s0, hbDigitNat] using h

    have hmemB : E.W n0 ∈ V.F (finitize b.1 (t0 + 1)) := by
      have : E.W n0 ∈ V.F (child s0 1) := by
        simp [Vconcrete, V, VC.FS, VC.runState, runState_child, VC.step, VC.FStep, s0, hk0, hdecN]
        let E0 : VC.Enumerations := toConcreteEnum E
        let st0 : VC.State := VC.runState E0 s0

        have ht0 : st0.t = t0 := by
  -- runState_t : (runState E0 s).t = s.len
  -- s0.len = t0
          have : (VC.runState E0 s0).t = s0.len := by
            simpa using runState_t (E0 := E0) (s := s0)
          simpa [st0, s0, fin_seq.finitize_len] using this

        have hk0st : VC.decK st0.t = IPC.k0 := by simpa [st0, ht0] using hk0
        have hdecNst : VC.decN st0.t = n0 := by simpa [st0, ht0] using hdecN

        have : E.W n0 ∈ V.F (child s0 1) := by
  -- V = Vconcrete E，所以 V.F = VC.FS E0 = (runState E0 _).Fs
  -- 用 runState_child 把 runState(child) 化成 step(runState s0) 1
          have hr : VC.runState E0 (child s0 1) = VC.step E0 (VC.runState E0 s0) 1 :=
    runState_child (E0 := E0) (s := s0) (q := 1)
          -- 设 concrete 枚举 & 状态
          let E0  : VC.Enumerations := toConcreteEnum E
          let st0 : VC.State := VC.runState E0 s0

-- 把 hr 里的 runState E0 s0 改成 st0，得到更好用的版本
          have hr' : VC.runState E0 (child s0 1) = VC.step E0 st0 1 := by
            simpa [st0] using hr


          have hmem_step : E.W n0 ∈ (VC.step E0 st0 1).Fs := by
  -- step 的 Fs 定义就是 FStep
            change E.W n0 ∈ VC.FStep E0 st0 1
  -- 展开 FStep，只保留 k0 分支
            unfold VC.FStep
  -- 用 hk0st 把最外层 if 锁定到 then 分支
  -- 这一步不会产生你之前那种“else 分支的目标”
            simp [hk0st]
  -- 现在目标变成：E.W n0 ∈ insert (E.W (VC.decN st0.t)) st0.Fs
  -- 用 hdecNst 把 decN st0.t 改成 n0，然后 mem_insert_self
            have ht0' : st0.t = t0 := by
  -- st0 = runState E0 s0, 且 runState_t 给出 t = len
              have : st0.t = s0.len := by
                simpa [st0] using (runState_t (E0 := E0) (s := s0))
  -- s0 = finitize bseq t0，所以 s0.len = t0
              simpa [s0, fin_seq.finitize_len] using this

            have hk0st0 : VC.decK st0.t = IPC.k0 := by
              simpa [ht0'] using hk0

            have hdecNst0 : VC.decN st0.t = n0 := by
              simpa [ht0'] using hdecN

-- 现在你的目标就是 mem(FStep...)；先锁定 if，再改写 decN，再用 mem_insert_self
            have : E.W n0 ∈
    (if VC.decK st0.t = IPC.k0 then
        insert (E0.W (VC.decN st0.t)) st0.Fs
     else
        if VC.decK st0.t = IPC.k1 then st0.Fs
        else
          match E0.W (VC.decN st0.t) with
          | A ⋎ B => if st0.prev2 = 1 then insert A st0.Fs else st0.Fs
          | x => st0.Fs) := by
  -- 关键：hk0st0 直接把 else 整坨扔掉；hdecNst0 把 E0.W(decN)=E0.W n0；
  -- 再用 toConcreteEnum 把 E0.W n0 化成 E.W n0；最后 simp 用 mem_insert_self 收尾
              simp [hk0st0, hdecNst0, E0, toConcreteEnum]

            exact this


-- 再用 hr' 把 step 换回 runState(child)
          have : E.W n0 ∈ (VC.runState E0 (child s0 1)).Fs := by
            simpa [hr'] using hmem_step

-- 如果你要的是 V.F (child s0 1)，再用 V=Vconcrete 的定义把 V.F 化成 FS=runState.Fs
          have : E.W n0 ∈ V.F (child s0 1) := by
  -- V = Vconcrete E 时，V.F = VC.FS E0，VC.FS 定义就是 runState.Fs
            simpa [Vconcrete, V, VC.FS, E0] using this
          exact this
  -- 现在算 Fs：step 的 Fs 是 FStep
  -- 并且在 k0 且 q=1 时插入 E0.W(decN st0.t) = E.W n0
  -- 全程用 simp 即可

        simpa [hs0] using this
      have : E.W n0 ∈ V.F (finitize bseq (t0 + 1)) := by
  -- this : E.W n0 ∈ V.F (child s0 1)
        simpa [hs0] using this
      exact Finset.mem_def.mpr this



    refine ⟨t0 + 1, ?_⟩
    simpa [hbSeq] using hmemB
namespace StepRules

open GammaRules

lemma AllowedStepb_k0_allow_0_1 (E0 : VC.Enumerations) (st : VC.State) :
    VC.decK st.t = IPC.k0 → VC.Forced0b E0 st = false →
      VC.AllowedStepb E0 st 0 = true ∧ VC.AllowedStepb E0 st 1 = true := by
  intro hk0 hF
  unfold VC.AllowedStepb
  simp [hk0, hF, Finset.decide_eq_true_iff]

lemma AllowedStepb_k0_force_only_1 (E0 : VC.Enumerations) (st : VC.State) :
    VC.decK st.t = IPC.k0 → VC.Forced0b E0 st = true →
      (VC.AllowedStepb E0 st 1 = true) := by
  intro hk0 hF
  unfold VC.AllowedStepb
  simp [hk0, hF, Finset.decide_eq_true_iff]

lemma AllowedStepb_k1_only_0 (E0 : VC.Enumerations) (st : VC.State) :
    VC.decK st.t = IPC.k1 → VC.AllowedStepb E0 st 0 = true := by
  intro hk1
  unfold VC.AllowedStepb
  have hk10 : (IPC.k1 : Fin 3) ≠ IPC.k0 := by decide
  simp [hk1, hk10, Finset.decide_eq_true_iff]

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
      · -- split 情形被 hNoSplit 排除
        exfalso
        exact hNoSplit ⟨A, B, hcase, hp⟩
      · -- not split: only q=0 allowed, so q=0 is allowed
        simp [hk2, hk20, hk21, hcase, hp, Finset.decide_eq_true_iff]
  | atom n =>
      simp [hk2, hk20, hk21, hcase, Finset.decide_eq_true_iff]
  | «I» =>
      simp [hk2, hk20, hk21, hcase, Finset.decide_eq_true_iff]
  | imp P Q =>
      simp [hk2, hk20, hk21, hcase, Finset.decide_eq_true_iff]
  | and P Q =>
      simp [hk2, hk20, hk21, hcase, Finset.decide_eq_true_iff]
lemma FS_child_k0_one
    (E : Enumerations) (s : fin_seq)
    (hk0 : VC.decK s.len = IPC.k0) :
    VC.FS (toConcreteEnum E) (child s 1)
      =
    insert (E.W (VC.decN s.len)) (VC.FS (toConcreteEnum E) s) := by

  let E0 : VC.Enumerations := toConcreteEnum E
  let st : VC.State := VC.runState E0 s

  -- st.t = s.len
  have ht : st.t = s.len := by
    simpa [st] using (runState_t (E0 := E0) (s := s))

  -- 把 hk0 搬到 st.t 上
  have hk0st : VC.decK st.t = IPC.k0 := by
    simpa [ht] using hk0

  -- 用 runState_child：runState(child) = step(runState s) 1
  have hr : VC.runState E0 (child s 1) = VC.step E0 (VC.runState E0 s) 1 :=
    runState_child (E0 := E0) (s := s) (q := 1)

  -- 取 Fs 字段
  have hFsEq :
      (VC.runState E0 (child s 1)).Fs = (VC.step E0 (VC.runState E0 s) 1).Fs := by
    simpa using congrArg (fun st => st.Fs) hr

  -- 计算 step 的 Fs
  have hFsStep :
    (VC.step E0 (VC.runState E0 s) 1).Fs
      =
    insert (E.W (VC.decN s.len)) (VC.runState E0 s).Fs := by
  -- 关键：把“展开的枚举 record”识别成 E0
    have hE0 :
      ({ W := E.W
       , d := E.d
       , W_surj := E.W_surj
       , d_sound := E.d_sound
       , d_complete := E.d_complete } : VC.Enumerations) = E0 := by
    -- E0 := toConcreteEnum E
      simp [E0, toConcreteEnum]

  -- 现在把 step/FStep 展开，并用 hE0 把 runState{..} 改成 runState E0
  -- 然后 hk0run 锁死 if，hdecNrun 改写 decN
    try rw [hE0]
    have ht_run : (VC.runState E0 s).t = s.len := by
      simpa using runState_t (E0 := E0) (s := s)
    have hk0run : VC.decK (VC.runState E0 s).t = IPC.k0 := by
      simpa [st, ht_run] using hk0st
    simp [VC.step, VC.FStep, hk0run, ht_run, E0, toConcreteEnum]
    rw [hE0]
    have hdecNrun : VC.decN (VC.runState E0 s).t = VC.decN s.len := by
      simpa [st, ht]
    simp [hk0run, hdecNrun]


  -- 把 FS 展开成 runState.Fs 并收尾
  -- FS E0 x = (runState E0 x).Fs
  simp [VC.FS, E0, hFsEq, hFsStep]

lemma Vconcrete_F_child_k0_one
    (E : Enumerations) (s : fin_seq)
    (hk0 : VC.decK s.len = IPC.k0) :
    (Vconcrete E).F (child s 1)
      =
    insert (E.W (VC.decN s.len)) ((Vconcrete E).F s) := by
  -- 展开 Vconcrete 的 F：就是 FS (toConcreteEnum E)
  -- 然后用上面 FS lemma
  simpa [Vconcrete] using (FS_child_k0_one (E := E) (s := s) hk0)

/-- Prop 版：k0 且（mem 或 eq），注意 mem 用的是 (t+1) 前缀，和 needs1b 一致。 -/
def needs1 {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ) : Prop :=
  VC.decK t = IPC.k0 ∧
    (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1)) ∨ E.W (VC.decN t) = W)
lemma bool_and_eq_true_iff (x y : Bool) : (x && y = true) ↔ (x = true ∧ y = true) := by
  cases x <;> cases y <;> simp

lemma bool_or_eq_true_iff (x y : Bool) : (x || y = true) ↔ (x = true ∨ y = true) := by
  cases x <;> cases y <;> simp


lemma needs1b_eq_true_iff_needs1
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t : ℕ) :
    needs1b (V := V) (a := a) (W := W) t = true ↔ needs1 (V := V) (a := a) (W := W) t := by

  unfold needs1b needs1
  constructor
  · intro hb
    -- hb : decide(k0) && (decide(mem) || decide(eq)) = true
    have hAnd :
        decide (VC.decK t = IPC.k0) = true ∧
        (decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1))) ||
         decide (E.W (VC.decN t) = W)) = true :=
      by exact Bool.and_eq_true_iff.mp hb

    have hk0 : VC.decK t = IPC.k0 :=
      (_root_.decide_eq_true_iff).1 hAnd.1

    let P : Prop := (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1)))
    let Q : Prop := (E.W (VC.decN t) = W)

    have hOrBool :
        (decide P || decide Q) = true := by
      simpa [P, Q] using hAnd.2

    have hOr :
        decide P = true ∨ decide Q = true := by
      -- 对 decide P 分两种情况
      cases hm : decide P with
      | true =>
          left
          -- hm : decide P = true
          exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)
      | false =>
          right
          -- hOrBool : (false || decide Q) = true  ⇒ decide Q = true
          -- 这里用 simpa 不会触发 “decide_eq_true_iff” 变 Prop，因为我们没有把 decide 展开成 Prop
          simpa [hm] using hOrBool
    have hmem_or_eq :
        (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1)) ∨ E.W (VC.decN t) = W) := by
      cases hOr with
      | inl hm =>
          left
          exact (_root_.decide_eq_true_iff).1 hm
      | inr he =>
          right
          exact (_root_.decide_eq_true_iff).1 he

    exact ⟨hk0, hmem_or_eq⟩

  · rintro ⟨hk0, hmem_or_eq⟩
    have hk0d : decide (VC.decK t = IPC.k0) = true :=
      (_root_.decide_eq_true_iff).2 hk0

    have hOr : (decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1))) ||
                decide (E.W (VC.decN t) = W)) = true := by
      cases hmem_or_eq with
      | inl hm =>
          have hm' : decide (E.W (VC.decN t) ∈ V.F (finitize a.1 (t + 1))) = true :=
            (_root_.decide_eq_true_iff).2 hm
          exact Bool.or_inl hm'
      | inr he =>
          have he' : decide (E.W (VC.decN t) = W) = true :=
            (_root_.decide_eq_true_iff).2 he
          exact Bool.or_inr he'

    exact Bool.and_intro hk0d hOr

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

  -- runState(child) = step(runState s) 0
  have hr :
      VC.runState E0 (child s 0) = VC.step E0 (VC.runState E0 s) 0 :=
    runState_child (E0 := E0) (s := s) (q := 0)

  -- 先改写成 step
  rw [hr]
  -- step 的 Fs 就是 FStep
  simp [VC.step]

  -- 现在目标变成：FStep E0 (runState E0 s) 0 = (runState E0 s).Fs
  have ht : (VC.runState E0 s).t = s.len := by
    simpa using runState_t (E0 := E0) (s := s)

  have hk0st : VC.decK (VC.runState E0 s).t = IPC.k0 := by
    simpa [ht] using hk0

  -- 展开 FStep：k0 分支下 q=0 -> else -> st.Fs
  -- 这里不会再产生 “¬k0 → ¬k1 → …” 的目标
  simp [VC.FStep, hk0st]
  exact Finset.val_inj.mp rfl
lemma Fs_child_k1_zero_eq
    (E : Enumerations) (s : fin_seq)
    (hk1 : VC.decK s.len = IPC.k1) :
    (VC.runState (toConcreteEnum E) (child s 0)).Fs
      = (VC.runState (toConcreteEnum E) s).Fs := by

  let E0 : VC.Enumerations := toConcreteEnum E
  have hr :
      VC.runState E0 (child s 0) = VC.step E0 (VC.runState E0 s) 0 :=
    runState_child (E0 := E0) (s := s) (q := 0)

  have ht : (VC.runState E0 s).t = s.len := by
    simpa using runState_t (E0 := E0) (s := s)

  have hk1st : VC.decK (VC.runState E0 s).t = IPC.k1 := by
    simpa [ht] using hk1

  -- step 的 Fs 是 FStep；k1 分支 FStep = st.Fs（不变）
  simp [hr, VC.step, VC.FStep, hk1st, E0, ht]
  exact fun a a_1 =>
    VeldmanConcrete.FStep.match_1.eq_2 (fun x => Finset Form)
      ((toConcreteEnum E).W (VeldmanConcrete.decN s.len))
      (fun A B => (VeldmanConcrete.runState (toConcreteEnum E) s).Fs)
      (fun x => (VeldmanConcrete.runState (toConcreteEnum E) s).Fs) fun A B x => a_1 hk1
lemma decK_eq_k2_of_ne_k0_k1 (t : ℕ)
    (h0 : VC.decK t ≠ IPC.k0) (h1 : VC.decK t ≠ IPC.k1) :
    VC.decK t = IPC.k2 := by
  -- 先把 val 分成 0/1/2（三分法）
  have hcases :
      (VC.decK t).val = 0 ∨ (VC.decK t).val = 1 ∨ (VC.decK t).val = 2 := by
    have : (VC.decK t).val < 3 := (VC.decK t).isLt
    omega
  -- 分情况排除 0/1，剩下 2
  cases hcases with
  | inl h0val =>
      have : VC.decK t = IPC.k0 := by
        apply Fin.ext
        simpa [IPC.k0, h0val]
      exact False.elim (h0 this)
  | inr h12 =>
      cases h12 with
      | inl h1val =>
          have : VC.decK t = IPC.k1 := by
            apply Fin.ext
            simpa [IPC.k1, h1val]
          exact False.elim (h1 this)
      | inr h2val =>
          apply Fin.ext
          simpa [IPC.k2, h2val]
lemma eq_one_of_needs1b_true_of_decK_ne_k0
    {E : ESk} (V : _root_.VeldmanFan E) (a : Branch V) (W : Form) (t q : ℕ)
    (hk0ne : VC.decK t ≠ IPC.k0) :
    needs1b (V := V) (a := a) (W := W) t = true → q = 1 := by
  intro hb
  have hk0 : VC.decK t = IPC.k0 :=
    k0_of_needs1b_true (V := V) (a := a) (W := W) (t := t) hb
  exact False.elim (hk0ne hk0)

lemma two_le_of_decK_eq_k2 (t : ℕ) (hk2 : VC.decK t = IPC.k2) : 2 ≤ t := by
  -- 从 hk2 得到 (decK t).val = 2
  have hval : (VC.decK t).val = 2 := by
    -- Fin.val 等于 .val
    simpa [IPC.k2] using congrArg Fin.val hk2

  -- decK t = (schedDecode t).2.2，而 schedDecode 用 r := t % 3
  -- 所以 (decK t).val = t % 3
  have hmod : t % 3 = 2 := by
    -- 展开 decK / schedDecode
    -- 关键：schedDecode 的第三分量就是 ⟨t%3, _⟩
    simpa [VC.decK, IPC.schedDecode] using hval

  -- 反证：若 t < 2，则 t < 3，从而 t % 3 = t，与 hmod 矛盾
  by_contra hle
  have ht2 : t < 2 := Nat.lt_of_not_ge hle
  have ht3 : t < 3 := lt_trans ht2 (by decide : 2 < 3)
  have hmodt : t % 3 = t := Nat.mod_eq_of_lt ht3
  have htEq : t = 2 := by
    -- hmod : t%3=2, hmodt : t%3=t
    simpa [hmodt] using hmod
  exact (Nat.ne_of_lt ht2) htEq

/-- 如果 `decK t = k2`，那么两步之前一定是 `k0`。 -/
lemma decK_sub2_of_decK_eq_k2 (t : ℕ) (ht2 : 2 ≤ t) (hk2 : VC.decK t = IPC.k2) :
    VC.decK (t - 2) = IPC.k0 := by

  -- 1) 从 hk2 得到 t % 3 = 2
  have hmod2 : t % 3 = 2 := by
    have : (VC.decK t).val = 2 := by
      simpa [IPC.k2] using congrArg Fin.val hk2
    -- decK 的 val 就是 (t % 3)
    simpa [VC.decK, IPC.schedDecode] using this

  -- 2) 用 mod_add_div 得到 t = t%3 + 3*(t/3)，再代入 t%3=2
  have ht_eq : t = 2 + 3 * (t / 3) := by
    -- Nat.mod_add_div : t % 3 + 3 * (t / 3) = t
    have h := Nat.mod_add_div t 3
    -- h.symm : t = t%3 + 3*(t/3)
    -- 再把 t%3 换成 2，并整理一下加法顺序
    simpa [hmod2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm

  -- 3) 所以 t-2 = 3*(t/3)
  have hsub : t - 2 = 3 * (t / 3) := by
    calc
      t - 2 = (2 + 3 * (t / 3)) - 2 := by rw [ht_eq];simp;rw[← ht_eq]
      _ = 3 * (t / 3) := Nat.add_sub_cancel_left 2 (3 * (t / 3))

  -- 4) (t-2) % 3 = 0
  have hmod0 : (t - 2) % 3 = 0 := by
    -- 用 hsub 改写成 (3*(t/3))%3
    -- 再用 add_mul_mod_self_left 证明它等于 0
    -- (0 + 3*(t/3)) % 3 = 0 % 3
    have h := Nat.add_mul_mod_self_left 0 3 (t / 3)
    -- h : (0 + 3*(t/3)) %3 = 0%3
    -- 左边化简成 (3*(t/3))%3
    -- 右边化简成 0
    simpa [hsub, Nat.zero_add] using h

  -- 5) decK(t-2) 的 val = (t-2)%3 = 0，所以等于 k0
  apply Fin.ext
  -- Fin.ext 只要比较 val
  -- (decK (t-2)).val = (t-2)%3
  -- (k0).val = 0
  simpa [VC.decK, IPC.schedDecode, IPC.k0, hmod0]

/-- k2 且调度公式是析取，但 prev2 ≠ 1（不在 split 模式）时，q=0 一定 Allowed。 -/
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
    -- 把 runState (toConcreteEnum E) s 改写成 st
    simpa [st, E0] using hp

  have hWst : E0.W (VC.decN st.t) = A ⋎ B := by
    simpa [E0, toConcreteEnum, ht] using hW

  -- 关键：这里一定要让 simp 看到 st/E0 的定义，否则 hk0ne/hk1ne/hpst/hWst 用不上
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
  simpa [VC.runState] using hEqFs
lemma AllowedStepb_k2_split_q1
    (E0 : VC.Enumerations) (st : VC.State) (A B : Form)
    (hk2 : VC.decK st.t = IPC.k2)
    (hW  : E0.W (VC.decN st.t) = A ⋎ B)
    (hp  : st.prev2 = 1) :
    VC.AllowedStepb E0 st 1 = true := by
  unfold VC.AllowedStepb
  have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
  have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
  -- 这里不要再用 Finset.decide_eq_true_iff；直接 simp 就能把 decide 算掉
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
    (hW  : E.W (VC.decN s.len) = A ⋎ B)
    (hp  : (VC.runState (toConcreteEnum E) s).prev2 = 1) :
    (VC.runState (toConcreteEnum E) (child s 1)).Fs
      = insert A (VC.runState (toConcreteEnum E) s).Fs := by
  let E0 : VC.Enumerations := toConcreteEnum E
  let st : VC.State := VC.runState E0 s

  have ht : st.t = s.len := by
    simpa [st, E0] using (runState_t (E0 := E0) (s := s))

  have hk2st : VC.decK st.t = IPC.k2 := by
    simpa [ht] using hk2

  have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
  have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
  have hk0st : ¬ VC.decK st.t = IPC.k0 := by simpa [hk2st] using hk20
  have hk1st : ¬ VC.decK st.t = IPC.k1 := by simpa [hk2st] using hk21

  have hWst : E0.W (VC.decN st.t) = A ⋎ B := by
    simpa [E0, ht] using hW

  have hpst : st.prev2 = 1 := by
    simpa [st, E0] using hp

  have hr :
      VC.runState E0 (child s 1) = VC.step E0 (VC.runState E0 s) 1 :=
    runState_child (E0 := E0) (s := s) (q := 1)
  have hr' : VC.runState E0 (child s 1) = VC.step E0 st 1 := by
    simpa [st] using hr

  rw [hr']
  simp [VC.step, VC.FStep, hk0st, hk1st, hWst, hpst, st]
  exact Finset.val_inj.mp rfl


lemma Fs_child_k2_split_two_eq
    (E : Enumerations) (s : fin_seq) (A B : Form)
    (hk2 : VC.decK s.len = IPC.k2)
    (hW  : E.W (VC.decN s.len) = A ⋎ B)
    (hp  : (VC.runState (toConcreteEnum E) s).prev2 = 1) :
    (VC.runState (toConcreteEnum E) (child s 2)).Fs
      = insert B (VC.runState (toConcreteEnum E) s).Fs := by
  let E0 : VC.Enumerations := toConcreteEnum E
  let st : VC.State := VC.runState E0 s

  have ht : st.t = s.len := by
    simpa [st, E0] using (runState_t (E0 := E0) (s := s))

  have hk2st : VC.decK st.t = IPC.k2 := by
    simpa [ht] using hk2

  have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
  have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
  have hk0st : ¬ VC.decK st.t = IPC.k0 := by simpa [hk2st] using hk20
  have hk1st : ¬ VC.decK st.t = IPC.k1 := by simpa [hk2st] using hk21

  have hWst : E0.W (VC.decN st.t) = A ⋎ B := by
    simpa [E0, ht] using hW

  have hpst : st.prev2 = 1 := by
    simpa [st, E0] using hp

  have hr :
      VC.runState E0 (child s 2) = VC.step E0 (VC.runState E0 s) 2 :=
    runState_child (E0 := E0) (s := s) (q := 2)
  have hr' : VC.runState E0 (child s 2) = VC.step E0 st 2 := by
    simpa [st] using hr

  rw [hr']
  simp [VC.step, VC.FStep, hk0st, hk1st, hWst, hpst, st]
  exact Finset.val_inj.mp rfl

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

  -- runState(child) = step(runState s) 0
  have hr : VC.runState E0 (child s 0) = VC.step E0 (VC.runState E0 s) 0 :=
    runState_child (E0 := E0) (s := s) (q := 0)

  -- 改写成 step
  rw [hr]
  simp [VC.step]

  -- 把 hk2 从 s.len 推到 (runState E0 s).t
  have ht : (VC.runState E0 s).t = s.len := by
    simpa using runState_t (E0 := E0) (s := s)

  have hk2st : VC.decK (VC.runState E0 s).t = IPC.k2 := by
    simpa [ht] using hk2

  -- 由 k2 得到 not k0 / not k1
  have hk0ne : ¬ VC.decK (VC.runState E0 s).t = IPC.k0 := by
    intro h
    have : (IPC.k2 : Fin 3) = IPC.k0 := by simpa [hk2st] using h
    exact (by decide : (IPC.k2 : Fin 3) ≠ IPC.k0) this

  have hk1ne : ¬ VC.decK (VC.runState E0 s).t = IPC.k1 := by
    intro h
    have : (IPC.k2 : Fin 3) = IPC.k1 := by simpa [hk2st] using h
    exact (by decide : (IPC.k2 : Fin 3) ≠ IPC.k1) this

  -- 展开 FStep：走到 k2 分支；q=0 时无论公式/prev2 都不会插入，直接等于 Fs
  simp [VC.FStep, hk0ne, hk1ne]
    -- 现在目标是一个 match 两支都相同的表达式，直接 cases 掉匹配项即可
  have hmatch :
      (match E0.W (VC.decN (VC.runState E0 s).t) with
        | A ⋎ B => (VC.runState E0 s).Fs
        | x     => (VC.runState E0 s).Fs)
        = (VC.runState E0 s).Fs := by
    cases hForm : E0.W (VC.decN (VC.runState E0 s).t) <;> simp [hForm]

  -- 右边是 runState (toConcreteEnum E) s，用 E0 := toConcreteEnum E 抹平
  simpa [E0] using hmatch

/-- **关键引理**：在第 n 步是 k0，且第 n 个 digit=1，则 Fs 在 n+1 步变成插入当前调度公式。 -/
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

  -- 把 runStateAux 的 succ 分支展开成 step，再展开 step.Fs = FStep
  -- 然后用 hk0st0 选中 k0 分支，用 hq 选中 q=1 分支，用 ht0 把 decN st0.t 改成 decN n
  -- （这一步就是你卡住的那个巨大 if 的“正确消解方式”）
  dsimp [VC.runStateAux]   -- 把 (n+1) 这一层展开出来：let st := ...; let q := ...; step ...
  -- 这时左边变成 (VC.step E0 st0 (s.seq ⟨n,...⟩)).Fs
  -- step 的 Fs 就是 FStep
  simp [VC.step, VC.FStep, st0, hk0st0, hq, ht0]
  intro hnk0
  exact False.elim (hnk0 hk0)

/-- 若 `decK t = k2`，则 `decN (t-2) = decN t`（同一 (n,m) 的三拍对齐）。 -/
lemma decN_sub2_of_decK_eq_k2 (t : ℕ) (hk2 : VC.decK t = IPC.k2) :
    VC.decN (t - 2) = VC.decN t := by

  -- 从 hk2 得到 t % 3 = 2
  have hmod2 : t % 3 = 2 := by
    have : (VC.decK t).val = 2 := by
      simpa [IPC.k2] using congrArg Fin.val hk2
    simpa [VC.decK, IPC.schedDecode] using this

  -- 令 q := t/3。由 mod_add_div 得到 t = t%3 + 3*q = 2 + 3*q
  have ht_eq : t = 2 + 3 * (t / 3) := by
    -- Nat.mod_add_div : t%3 + 3*(t/3) = t
    have h := Nat.mod_add_div t 3
    -- 受控改写，不用 simp [ht_eq] 以免爆栈
    -- h.symm : t = t%3 + 3*(t/3)
    simpa [hmod2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm

  -- t-2 = 3*(t/3)
  have hsub : t - 2 = 3 * (t / 3) := by
    -- 用 congrArg 把等式塞进 (-2)
    have := congrArg (fun x => x - 2) ht_eq
    -- (2 + X) - 2 = X
    simpa [Nat.add_sub_cancel_left] using this

  -- (t-2)/3 = t/3
  have hdiv : (t - 2) / 3 = t / 3 := by
    rw [hsub]
    -- (3 * q) / 3 = q
    -- 先换成 q*3 再用 mul_div_right
    have : (3 * (t / 3)) / 3 = ((t / 3) * 3) / 3 := by
      simp [Nat.mul_comm]
    rw [this]
    simpa using Nat.mul_div_right (t / 3) 3

  -- decN 只取 schedDecode 的第一分量 = unpair(q).1，所以只要 q 相等即可
  simp [VC.decN, IPC.schedDecode, hdiv]

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

  have hk : VC.decK st.t = VC.decK s.len := by simpa [ht]
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
  -- 先用 ht : st.t = s.len
  -- 再展开 E0
          subst X
          simpa [E0, toConcreteEnum, ht]

        have hprfX : (↑st.Fs : Set Form) ⊢ᵢ X := by
  -- 用 hX 改写结论
          simpa [hX] using hprf

-- 第二步：再把上下文从 st.Fs 改成 V.F s
        have hΓ : (↑(V.F s) : Set Form) ⊢ᵢ X := by
  -- 用 hFs 改写上下文（注意方向）
          simpa [hFs] using hprfX

-- 如果你的 goal 是 ↑((Vconcrete E).F s) ⊢ᵢ X，而你这里 let V := Vconcrete E
-- 最后一行只需要把 V 展开一下：
        simpa [V] using hΓ



    · -- not forced
      have hF' : VC.Forced0b E0 st = false := by
        cases h0 : VC.Forced0b E0 st with
        | true =>
            -- h0 : Forced0b = true，与 hF : Forced0b ≠ true 矛盾
            exact False.elim (hF h0)
        | false =>

            simpa using h0
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
          change (VC.runState E0 (child s 1)).Fs =
            insert X (VC.runState E0 s).Fs


          have hk0st : VC.decK (VC.runState E0 s).t = IPC.k0 := by
          -- runState_t : (runState E0 s).t = s.len
            simpa [runState_t (E0 := E0) (s := s)] using hk0


          have hr : VC.runState E0 (child s 1) = VC.step E0 (VC.runState E0 s) 1 :=
          runState_child (E0 := E0) (s := s) (q := 1)


          have hW : (toConcreteEnum E).W (VC.decN s.len) = E.W (VC.decN s.len) := by rfl

          simp [VC.FStep, hk0, X, hW]
          have ht' : (VC.runState E0 s).t = s.len := by
            simpa [st] using ht
          rw [hr]
          simp [VC.step, VC.FStep, hk0st, ht', hW]
          have hW0 : E0.W (VC.decN s.len) = E.W (VC.decN s.len) := by

            simpa [E0] using hW

          simp [hk0, hW0]
        · -- X in Gamma a or X=W
          rcases hneed with hmem | hEq
          · -- X ∈ Γ_a because it's already in F(prefix a (s.len))
            left
            refine ⟨s.len + 1, ?_⟩
-- 注意：Gamma 用的是 finitize a.1 n，所以这里也用 a.1，不用 ↑a
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
  -- hk0 : ¬ decK s.len = k0  从你的 “not k0” 分支里来的
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
            | «I» =>
          refine Or.inl ?_
          refine ⟨0, ?_, ?_⟩
          ·
            have hk2st : VC.decK st.t = IPC.k2 := by simpa [ht] using hk2
            have hk20 : (IPC.k2 : Fin 3) ≠ IPC.k0 := by decide
            have hk21 : (IPC.k2 : Fin 3) ≠ IPC.k1 := by decide
            have hWst : E0.W (VC.decN st.t) = Form.I := by
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

/-! ### Final: `impDataConcrete` (Todo B) -/
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
      simpa [toB] using
        (toBranchOfSubfan_coe (V := V) (hT := hT) (hsub := hsub) b)
    subfan_ok := by
      intro b
      have h :=
        TodoB.subfan_ok (E := E) (V := V) (a := a) (W := W)
          (hV := rfl) (T := T) (hTdef := rfl) (hT := hT) b

      simpa [toB, hsub] using h
    stepRules := hRules



    ind_step := by
      intro s hs0 hall
      exact _root_.GammaRules.ind_step_of_rules
        (V := V) (a := a) (W := W) (Q := Q) (T := T)
        hRules s hs0 hall
  }

end TodoB
