import LTL

namespace MTL

-- 本ファイルの方針（明記）
-- - future-MTL（未来側の区間付き F/G/U のみ）は、LTL の演算子（X, ∧, ∨, ⊥ など）
--   だけでマクロとして定義できる＝LTL の特殊化として実装可能。
-- - 一方で、過去演算子を含む past-MTL（例: S_I）は、
--   未来断面のみの LTL の特殊化としては実装不可能。
--   （必要なら独立の意味論を導入するか、LTL 自体に過去演算子を拡張する。）

-- MTL の式は LTL の式をそのまま用いる。
abbrev Formula (α : Type) := LTL α

namespace Defs

variable {α : Type}

-- ⊤ に相当する式（¬⊥）
def topF : Formula α := LTL.not LTL.bot

-- X を n 回繰り返す：X^0 φ = φ, X^{n+1} φ = X (X^n φ)
def nextN : Nat → Formula α → Formula α
  | 0,       φ => φ
  | Nat.succ n, φ => LTL.next (nextN n φ)

-- 有限回の論理和：f(0) ∨ f(1) ∨ ... ∨ f(n)
def bigOrUpTo : Nat → (Nat → Formula α) → Formula α
  | 0,       f => f 0
  | Nat.succ n, f => LTL.or (f 0) (bigOrUpTo n (fun k => f (k+1)))

-- 有限回の論理積：f(0) ∧ f(1) ∧ ... ∧ f(n)
def bigAndUpTo : Nat → (Nat → Formula α) → Formula α
  | 0,       f => f 0
  | Nat.succ n, f => LTL.and (f 0) (bigAndUpTo n (fun k => f (k+1)))

-- 個数で区切る有限論理積：k = 0..(n-1)
-- bigAndLt 0 f = ⊤、bigAndLt (n+1) f = f 0 ∧ f 1 ∧ ... ∧ f n
def bigAndLt : Nat → (Nat → Formula α) → Formula α
  | 0,       _ => topF
  | Nat.succ n, f => LTL.and (f 0) (bigAndLt n (fun k => f (k+1)))

-- 有界Eventually：F_[a,b] φ
-- 意味（離散時間）：∃ d ∈ [0, b-a], X^a (X^d φ)
def eventuallyI (a b : Nat) (φ : Formula α) : Formula α :=
  if a ≤ b then
    let len := b - a
    nextN a (bigOrUpTo len (fun d => nextN d φ))
  else
    LTL.bot

-- 有界Always：G_[a,b] φ
-- 意味（離散時間）：∀ d ∈ [0, b-a], X^a (X^d φ)
-- よって有限個の論理積になる。区間が空のときは ⊤ とする。
def alwaysI (a b : Nat) (φ : Formula α) : Formula α :=
  if a ≤ b then
    let len := b - a
    nextN a (bigAndUpTo len (fun d => nextN d φ))
  else
    topF

-- 有界Until：φ U_[a,b] ψ
-- 意味（離散時間）：∃ d ∈ [0, b-a], X^a ( (∧_{k=0..d-1} X^k φ) ∧ X^d ψ )
def untilI (a b : Nat) (φ ψ : Formula α) : Formula α :=
  if a ≤ b then
    let len := b - a
    nextN a (bigOrUpTo len (fun d =>
      -- d = 0 のときは ∧ が空（⊤）、d > 0 で k=0..d-1 の ∧ をとる
      LTL.and (bigAndLt d (fun k => nextN k φ)) (nextN d ψ)))
  else
    LTL.bot

end Defs

open Defs

variable {α : Type}

abbrev nextN (n : Nat) (φ : Formula α) : Formula α := Defs.nextN (α:=α) n φ

end MTL
