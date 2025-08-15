
-- Logic Operator の定義
inductive LO (α : Type) where
  | atom : α → LO α -- 原始命題
  | bot  : LO α -- ⊥
  | not  : LO α → LO α -- ¬φ
  | and  : LO α → LO α → LO α -- φ ∧ ψ
  | or   : LO α → LO α → LO α -- φ ∨ ψ
  | impl : LO α → LO α → LO α -- φ → ψ

variable {α : Type}

def eval (v : α → Bool) : LO α → Bool
  | LO.atom a    => v a
  | LO.bot       => false
  | LO.not p     => !(eval v p)
  | LO.and p q   => eval v p && eval v q
  | LO.or  p q   => eval v p || eval v q
  | LO.impl p q  => !eval v p || eval v q

def interp {α : Type} (v : α → Prop) : LO α → Prop
  | LO.atom a   => v a
  | LO.bot      => False
  | LO.not p    => ¬ interp v p
  | LO.and p q  => interp v p ∧ interp v q
  | LO.or p q   => interp v p ∨ interp v q
  | LO.impl p q => interp v p → interp v q

def Valid (φ : LO α) : Prop :=
  ∀ v : α → Bool, eval v φ = true

class ProofSystem (α : Type) where
  Provable : LO α → Prop


-- ヒルベルト体系
inductive Provable {α : Type} : LO α → Prop where
  | ax1 {p q : LO α} : Provable (LO.impl p (LO.impl q p))
  | ax2 {p q r : LO α} : Provable (LO.impl (LO.impl p (LO.impl q r)) (LO.impl (LO.impl p q) (LO.impl p r)))
  | mp {p q : LO α} : Provable (LO.impl p q) → Provable p → Provable q

-- 自然演繹スタイル（コンテキスト付き）
inductive NDProvable {α : Type} : List (LO α) → LO α → Prop where
  -- 仮定
  | assume {Γ p} : p ∈ Γ → NDProvable Γ p
  -- 連言
  | intro_and {Γ p q} : NDProvable Γ p → NDProvable Γ q → NDProvable Γ (LO.and p q)
  | elim_and_left {Γ p q} : NDProvable Γ (LO.and p q) → NDProvable Γ p
  | elim_and_right {Γ p q} : NDProvable Γ (LO.and p q) → NDProvable Γ q
  -- 選言
  | intro_or_left {Γ p q} : NDProvable Γ p → NDProvable Γ (LO.or p q)
  | intro_or_right {Γ p q} : NDProvable Γ q → NDProvable Γ (LO.or p q)
  | elim_or {Γ p q r} : NDProvable Γ (LO.or p q) → NDProvable (p :: Γ) r → NDProvable (q :: Γ) r → NDProvable Γ r
  -- 含意
  | intro_impl {Γ p q} : NDProvable (p :: Γ) q → NDProvable Γ (LO.impl p q)
  | elim_impl {Γ p q} : NDProvable Γ (LO.impl p q) → NDProvable Γ p → NDProvable Γ q
  -- 否定
  | intro_not {Γ p} : NDProvable (p :: Γ) LO.bot → NDProvable Γ (LO.not p)
  | elim_not {Γ p} : NDProvable Γ (LO.not p) → NDProvable Γ p → NDProvable Γ LO.bot
  -- 爆発律
  | ex_falso {Γ p} : NDProvable Γ LO.bot → NDProvable Γ p

-- コンテキストの解釈
def interp_context {α : Type} (v : α → Prop) (Γ : List (LO α)) : Prop :=
  ∀ φ ∈ Γ, interp v φ

-- NDProvableの健全性定理
theorem nd_soundness {α} {Γ : List (LO α)} {φ : LO α} (h : NDProvable Γ φ) :
    ∀ v, interp_context v Γ → interp v φ := by
  induction h with
  | assume h_mem =>
    intros v h_ctx
    exact h_ctx _ h_mem
  | intro_and h_p h_q ih_p ih_q =>
    intros v h_ctx
    constructor
    · exact ih_p v h_ctx
    · exact ih_q v h_ctx
  | elim_and_left h_pq ih =>
    intros v h_ctx
    exact (ih v h_ctx).1
  | elim_and_right h_pq ih =>
    intros v h_ctx
    exact (ih v h_ctx).2
  | intro_or_left h_p ih =>
    intros v h_ctx
    left
    exact ih v h_ctx
  | intro_or_right h_q ih =>
    intros v h_ctx
    right
    exact ih v h_ctx
  | elim_or h_pq h_pr h_qr ih_pq ih_pr ih_qr =>
    intros v h_ctx
    cases ih_pq v h_ctx with
    | inl h_p =>
      apply ih_pr v
      intros φ h_mem
      cases h_mem with
      | head => exact h_p
      | tail _ h_mem' => exact h_ctx φ h_mem'
    | inr h_q =>
      apply ih_qr v
      intros φ h_mem
      cases h_mem with
      | head => exact h_q
      | tail _ h_mem' => exact h_ctx φ h_mem'
  | intro_impl h_pq ih =>
    intros v h_ctx h_p
    apply ih v
    intros φ h_mem
    cases h_mem with
    | head => exact h_p
    | tail _ h_mem' => exact h_ctx φ h_mem'
  | elim_impl h_pq h_p ih_pq ih_p =>
    intros v h_ctx
    exact ih_pq v h_ctx (ih_p v h_ctx)
  | intro_not h_pb ih =>
    intros v h_ctx h_p
    apply ih v
    intros φ h_mem
    cases h_mem with
    | head => exact h_p
    | tail _ h_mem' => exact h_ctx φ h_mem'
  | elim_not h_np h_p ih_np ih_p =>
    intros v h_ctx
    exact ih_np v h_ctx (ih_p v h_ctx)
  | ex_falso h_bot ih =>
    intros v h_ctx
    exact False.elim (ih v h_ctx)
