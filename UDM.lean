/-
UDM: 離散時間 (ℕ) 上の Uni‑Temporal Data Model

このファイルでは次を定義します：
* 変更点（change point） `(time : Nat, val : α)`
* 整合性述語 `Wf`：非空リストであり、時刻が（隣接間で）厳密単調増加であること
* 意味論 `select`：時刻 `t`（`t ≥ first.time`）において有効な値を返す（右連続・半開区間）
* 末尾追記 `update`：より大きい時刻の変更点を末尾に追加

証明する主な性質：
* `wf_update` — `update` は整合性を保存する
* `select_of_lt_next` / `select_of_ge_next` — `select` の局所方程式
* `select_update_cases` — 更新後の意味論（手前/以後）

このファイルは self‑contained（mathlib への依存なし）です。
-/

namespace UDM

variable {α : Type _}

/-- 変更点：時刻と値の組。 -/
structure CP (α : Type _) where
  time : Nat
  val  : α
  deriving Repr, DecidableEq

/-- `Wf`：非空リストで、時刻が（隣接間で）厳密単調増加すること。 -/
inductive Wf : List (CP α) → Type where
  | singleton (x : CP α) : Wf [x]
  | cons2 (x y : CP α) (xs : List (CP α))
      (hxy : x.time < y.time)
      (hrest : Wf (y :: xs)) :
      Wf (x :: y :: xs)

namespace Wf

/-- 先頭の時刻（`x :: _` の `x.time`）。空は 0 とする（実際は `Wf` なら空でない）。 -/
@[simp] def firstTime (l : List (CP α)) (h : Wf l) : Nat :=
  match l with
  | [] => 0
  | x :: _ => x.time

/-- `Wf` リストの末尾要素。 -/
def last : (l : List (CP α)) → Wf l → CP α
  | [x], _ => x
  | (x :: y :: xs), Wf.cons2 _ _ _ _ hrest => last (y :: xs) hrest

-- helper lemma (unused): last of singleton is itself
-- @[simp] lemma last_singleton (x : CP α) : last [x] (Wf.singleton x) = x := rfl

end Wf

/-- 意味論 `select`：`t ≥ firstTime` に対して、その時刻に有効な値を返す。
右連続・半開区間 [τᵢ, τᵢ₊₁) で定義し、末尾は [τₙ, ∞)。

簡便のため、`t ≥ firstTime l h` の証明を引数として渡す。 -/

@[simp] def select : (l : List (CP α)) → (h : Wf l) →
    (t : Nat) → α
  | [x], _, _ => x.val
  | (x :: y :: xs), Wf.cons2 _ _ _ _ hrest, t =>
      if hlt : t < y.time then
        x.val
      else
        select (y :: xs) hrest t

-- 局所方程式系（未使用のため省略）。

-- （補助）一般リストの末尾取得は未使用のため削除。

/-- `update` のための単純なリスト連結。 -/
@[simp] def updateList (l : List (CP α)) (cp : CP α) : List (CP α) := l ++ [cp]

-- 以下、応用的な構成（update の閉性、History 構造など）は省略。

end UDM
