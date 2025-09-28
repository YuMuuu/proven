import LTL

namespace MTL

-- 本ファイルの方針（明記）
-- - future-MTL（未来側の区間付き F/G/U のみ）は、LTL の演算子（X, ∧, ∨, ⊥ など）
--   だけでマクロとして定義できる＝LTL の特殊化として実装可能。
-- - 一方で、過去演算子を含む past-MTL（例: S_I）は、
--   未来断面のみの LTL の特殊化としては実装不可能。

-- MTL の式は LTL の式をそのまま用いる。
abbrev Formula (α : Type) := LTL α

namespace Defs

variable {α : Type}

-- future-MTL（未来側の区間付き F/G/U）を LTL の演算子だけで構文マクロとして定義する

/- 補助: `X` の n 回反復（単純な再帰方程式） -/
def nextN : Nat → LTL α → LTL α
  | 0,       φ => φ
  | Nat.succ n, φ => LTL.next (nextN n φ)

/- 補助: 区間型（未来側のみ） -/
inductive Interval where
  | closed (l u : Nat) (hle : l ≤ u)    -- [l, u]
  | from   (l : Nat)                    -- [l, ∞)

namespace Builders

/- 有界回数の大析取/大連言（長さは `steps+1`。基底は f l） -/
def bigOrSteps (f : Nat → LTL α) (l : Nat) : Nat → LTL α
  | 0     => f l
  | n+1   => LTL.or  (f l) (bigOrSteps f (l+1) n)

def bigAndSteps (f : Nat → LTL α) (l : Nat) : Nat → LTL α
  | 0     => f l
  | n+1   => LTL.and (f l) (bigAndSteps f (l+1) n)

/- [l,u] の大析取/大連言 -/
def bigOrFromTo (f : Nat → LTL α) (l u : Nat) : LTL α :=
  bigOrSteps f l (u - l)

def bigAndFromTo (f : Nat → LTL α) (l u : Nat) : LTL α :=
  bigAndSteps f l (u - l)

/- `k` ステップ後に ψ が起こり、それまで φ が維持される（長さちょうど k の until 展開）。
   具体的には: k=0 で ψ、k>0 で φ ∧ X(…(φ ∧ X ψ))。 -/
def untilAt (φ ψ : LTL α) : Nat → LTL α
  | 0     => ψ
  | k+1   => LTL.and φ (LTL.next (untilAt φ ψ k))

end Builders

open Builders

/- 区間付き Finally（F） -/
def F_I (I : Interval) (φ : LTL α) : LTL α :=
  match I with
  | Interval.closed l u _ =>
      bigOrFromTo (fun k => nextN k φ) l u                    -- ⋁_{k=l..u} X^k φ
  | Interval.from l         => nextN l (LTL.finaly φ)         -- X^l F φ

/- 区間付き Glbally（G） -/
def G_I (I : Interval) (φ : LTL α) : LTL α :=
  match I with
  | Interval.closed l u _ =>
      bigAndFromTo (fun k => nextN k φ) l u                   -- ⋀_{k=l..u} X^k φ
  | Interval.from l         => nextN l (LTL.globally φ)       -- X^l G φ

/- 区間付き Until（U）
   意味: ∃k ∈ I. (∀m < k, X^m φ) ∧ X^k ψ。
   [l,u] は有限展開、[l,∞) は先頭 l 区間の φ と X^l(φ U ψ) の合成で表す。 -/
def U_I (I : Interval) (φ ψ : LTL α) : LTL α :=
  match I with
  | Interval.closed l u _ =>
      bigOrFromTo (untilAt φ ψ) l u                           -- ⋁_{k=l..u} (φ … U_k ψ)
  | Interval.from 0         => LTL.until φ ψ                  -- [0,∞): そのまま U
  | Interval.from (Nat.succ n) =>
      -- (⋀_{m=0..n} X^m φ) ∧ X^{n+1} (φ U ψ)
      LTL.and
        (bigAndFromTo (fun m => nextN m φ) 0 n)
        (nextN (n+1) (LTL.until φ ψ))

/- 使いやすいラッパ（必要に応じて利用） -/
def F_closed (l u : Nat) (hle : l ≤ u) (φ : LTL α) : LTL α :=
  F_I (Interval.closed l u hle) φ

def F_from (l : Nat) (φ : LTL α) : LTL α :=
  F_I (Interval.from l) φ

def G_closed (l u : Nat) (hle : l ≤ u) (φ : LTL α) : LTL α :=
  G_I (Interval.closed l u hle) φ

def G_from (l : Nat) (φ : LTL α) : LTL α :=
  G_I (Interval.from l) φ

def U_closed (l u : Nat) (hle : l ≤ u) (φ ψ : LTL α) : LTL α :=
  U_I (Interval.closed l u hle) φ ψ

def U_from (l : Nat) (φ ψ : LTL α) : LTL α :=
  U_I (Interval.from l) φ ψ

end Defs

/-
このセクションでは、上で定義した future-MTL のマクロ（区間付き F/G/U）の
使い方を簡単なモデル上で示す。ここでの例は LTL の意味論（`holds`）のみを用いる。
-/
namespace Examples

open MTL Defs

/- 例の評価用：ブール値モデルと評価器
   fuel により未来方向の探索を有限に制限した実行可能意味論を与える。 -/

abbrev MyModelB (α : Type) := Nat → α → Bool

def holdsB {α} (fuel : Nat) (σ : MyModelB α) (i : Nat) : LTL α → Bool
  | LTL.atom a      => σ i a
  | LTL.not φ       => !(holdsB fuel σ i φ)
  | LTL.and φ ψ     => holdsB fuel σ i φ && holdsB fuel σ i ψ
  | LTL.or  φ ψ     => holdsB fuel σ i φ || holdsB fuel σ i ψ
  | LTL.impl φ ψ    => (!holdsB fuel σ i φ) || holdsB fuel σ i ψ
  | LTL.next φ      => match fuel with
                       | 0     => false
                       | n+1   => holdsB n σ (i+1) φ
  | LTL.until φ ψ   => match fuel with
                       | 0     => holdsB 0 σ i ψ
                       | n+1   =>
                           holdsB (n+1) σ i ψ ||
                           (holdsB (n+1) σ i φ && holdsB n σ (i+1) (LTL.until φ ψ))
  | LTL.release φ ψ => match fuel with
                       | 0     => holdsB 0 σ i ψ
                       | n+1   =>
                           holdsB (n+1) σ i ψ &&
                           (holdsB (n+1) σ i φ || holdsB n σ (i+1) (LTL.release φ ψ))
  | LTL.finaly φ    => match fuel with
                       | 0     => holdsB 0 σ i φ
                       | n+1   => holdsB (n+1) σ i φ || holdsB n σ (i+1) (LTL.finaly φ)
  | LTL.globally φ  => match fuel with
                       | 0     => holdsB 0 σ i φ
                       | n+1   => holdsB (n+1) σ i φ && holdsB n σ (i+1) (LTL.globally φ)

def evalB {α} (σ : MyModelB α) (fuel i : Nat) (φ : LTL α) : Bool :=
  holdsB fuel σ i φ

/- 例で使う原子命題 -/
inductive AP where
  | p | q
deriving DecidableEq

/- サンプルモデル：
   - p は全ての時点で真
   - q は時点 2 と 5 で真 -/
def σ : MyModel AP := fun i a =>
  match a with
  | AP.p => True
  | AP.q => (i = 2) ∨ (i = 5)

def σb : MyModelB AP := fun i a =>
  match a with
  | AP.p => true
  | AP.q => decide (i = 2 ∨ i = 5)

def φ : Formula AP := LTL.atom AP.p
def ψ : Formula AP := LTL.atom AP.q

/- マクロを用いた式の例 -/
def exF_1_3_q : Formula AP := F_closed 1 3 (by decide) ψ
def exG_from2_p : Formula AP := G_from 2 φ
def exU_0_2_pUq : Formula AP := U_closed 0 2 (by decide) φ ψ

/- 補足：
   これらの例に対する `holds` の証明（`example`）も追加可能。
   ただしプロジェクト全体の `lake build` には依存取得が必要なので、
   ネットワークが利用可能な環境での検証を推奨する。 -/

/- #eval! による「成功（true）」と「失敗（false）」の例
   ここでは `holdsB`（ブール値の簡易評価器）で確認する。
   燃料 `fuel` は Next の展開可能ステップ数。 -/
def fuel := 10

def eval (φ : Formula AP) : Bool := evalB σb fuel 0 φ

-- 成功例: q は [1,3] の範囲で時刻 2 に真になるので真
#eval! eval (F_closed 1 3 (by decide) ψ)

-- 失敗例: q は時刻 1 では真でないので偽
#eval! eval (F_closed 1 1 (by decide) ψ)

-- 成功例: p U q は [0,2] の範囲で時刻 2 に q が起こるため真
#eval! eval (U_closed 0 2 (by decide) φ ψ)

-- 失敗例: [0,1] の範囲内には q が起こらないので偽
#eval! eval (U_closed 0 1 (by decide) φ ψ)

-- 追加: 未使用だった演算子を使う例（F/G/U(無限), R）
-- F（無限）: q は 2 で起こるので真
#eval! eval (F_from 0 ψ)

-- G（無限）: p は常に真なので真、q は常に真ではないので偽
#eval! eval (G_from 0 φ)
#eval! eval (G_from 0 ψ)

-- U（無限）: fuel を 1 にすると（到達できず）偽、fuel を 10 にすると真
#eval! evalB σb 1 0 (U_from 0 φ ψ)
#eval! eval (U_from 0 φ ψ)

-- R（Release）: p R p は真、p R q は偽（時刻0で q が偽）
#eval! evalB σb fuel 0 (LTL.release φ φ)
#eval! evalB σb fuel 0 (LTL.release φ ψ)

end Examples

end MTL
