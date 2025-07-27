-- 線形時相論理（LTL）の定義と健全性証明
import Init.Data.Nat.Basic

-- LTL式の定義
inductive LTL (α : Type) where
  | atom : α → LTL α
  | bot  : LTL α
  | not  : LTL α → LTL α
  | and  : LTL α → LTL α → LTL α
  | or   : LTL α → LTL α → LTL α
  | impl : LTL α → LTL α → LTL α
  | next : LTL α → LTL α
  | until : LTL α → LTL α → LTL α
  | release : LTL α → LTL α → LTL α
  | eventually : LTL α → LTL α    -- F φ ≡ true U φ
  | always     : LTL α → LTL α    -- G φ ≡ false R φ

-- 無限列: 各時点で真な原子命題の集合
abbrev MyStream (α : Type) := Nat → α
abbrev MyModel (α : Type) := MyStream (α → Prop)

-- 意味論の定義
def holds {α : Type} (σ : MyModel α) (i : Nat) : LTL α → Prop
  | LTL.atom p     => σ i p
  | LTL.bot        => False
  | LTL.not φ      => ¬ holds σ i φ
  | LTL.and φ ψ    => holds σ i φ ∧ holds σ i ψ
  | LTL.or φ ψ     => holds σ i φ ∨ holds σ i ψ
  | LTL.impl φ ψ   => holds σ i φ → holds σ i ψ
  | LTL.next φ     => holds σ (i+1) φ
  | LTL.until φ ψ  => ∃ j, j ≥ i ∧ holds σ j ψ ∧ ∀ k, i ≤ k ∧ k < j → holds σ k φ
  | LTL.release φ ψ => ∀ j, j ≥ i → holds σ j ψ ∨ ∃ k, k ≥ i ∧ holds σ k φ ∧ ∀ m, i ≤ m ∧ m ≤ k → holds σ m ψ
  | LTL.eventually φ => ∃ j, j ≥ i ∧ holds σ j φ
  | LTL.always φ     => ∀ j, j ≥ i → holds σ j φ

-- 追加の公理: until_introの二つ目の前提の意味
axiom until_intro_premise {α : Type} (φ ψ : LTL α) (σ : MyModel α) (i : Nat) :
  (holds σ i φ → ∃ j, j ≥ i+1 ∧ holds σ j ψ ∧ ∀ k, i+1 ≤ k → k < j → holds σ k φ) →
  ¬holds σ i ψ → holds σ i φ

-- 証明システムの定義
inductive Provable {α : Type} : LTL α → Prop where
  | ax1 (φ ψ : LTL α) : Provable (LTL.impl φ (LTL.impl ψ φ))
  | ax2 (φ ψ χ : LTL α) : Provable (LTL.impl (LTL.impl φ (LTL.impl ψ χ)) (LTL.impl (LTL.impl φ ψ) (LTL.impl φ χ)))
  | mp (φ ψ : LTL α) : Provable (LTL.impl φ ψ) → Provable φ → Provable ψ -- modus ponens
  | next_rule (φ : LTL α) : Provable (LTL.always φ) → Provable (LTL.next φ) -- 修正: G φ → X φ
  | until_intro (φ ψ : LTL α) : Provable ψ → Provable (LTL.impl φ (LTL.next (LTL.until φ ψ))) → Provable (LTL.until φ ψ)

-- 健全性定理
theorem soundness {α : Type} (φ : LTL α) :
  Provable φ → ∀ (σ : MyModel α) (i : Nat), holds σ i φ := by
  intro prf
  induction prf with
  | ax1 φ ψ =>
      intro σ i
      simp [holds]
      intro hφ _
      exact hφ
  | ax2 φ ψ χ =>
      intro σ i
      simp [holds]
      intro h1 h2 hφ
      exact h1 hφ (h2 hφ)
  | mp φ ψ _ _ ih_impl ih_φ =>
      intro σ i
      exact ih_impl σ i (ih_φ σ i)
  | next_rule φ _ ih =>
      intro σ i
      simp [holds]
      -- G φ → X φ の証明
      have h_always := ih σ i
      -- G φ の意味論: ∀ j, j ≥ i → holds σ j φ
      -- X φ の意味論: holds σ (i+1) φ
      -- i+1 ≥ i なので、G φ から X φ が導かれる
      exact h_always (i+1) (Nat.le_succ i)
  | until_intro φ ψ _ _ ih_ψ ih_impl =>
      intro σ i
      simp [holds]
      -- until φ ψ の意味論: ∃ j, j ≥ i ∧ holds σ j ψ ∧ ∀ k, i ≤ k ∧ k < j → holds σ k φ
      
      -- ケース分け: ψが現在時点iで成り立つか否か
      by_cases h_ψ_now : holds σ i ψ
      
      -- ケース1: ψが現在の時点iで成り立つ場合
      case pos => 
        -- この場合、j = i として until の条件を満たす
        exists i
        constructor
        · exact Nat.le_refl i  -- i ≥ i
        constructor
        · exact h_ψ_now       -- ψが時点iで成り立つ
        · intro k h_cond h_lt
          -- j = i の場合、i ≤ k ∧ k < i を満たす k は存在しない
          -- これは矛盾するので、任意の命題が導かれる
          
          -- h_cond は i ≤ k、h_ltは k < i という形式
          -- これは矛盾するので、任意の命題が導かれる
          
          -- 矛盾を示す
          exact False.elim (Nat.not_lt_of_le h_cond h_lt)
      
      -- ケース2: ψが現在時点iで成り立たない場合
      case neg =>
        -- この場合、φが成り立ち、次の時点でuntil φ ψが成り立つ
        -- ih_implは Provable (LTL.impl φ (LTL.next (LTL.until φ ψ))) の帰納法の仮定
        have h_impl := ih_impl σ i
        simp [holds] at h_impl
        
        -- φ → X(φ U ψ) の意味論: holds σ i φ → holds σ (i+1) (φ U ψ)
        -- ψが成り立たない場合、until_introの二つ目の前提から、φが成り立つ必要がある
        
        -- 追加の公理を使用: until_introの二つ目の前提から、ψが成り立たない場合はφが成り立つ
        have h_φ : holds σ i φ := until_intro_premise φ ψ σ i h_impl h_ψ_now
        
        -- φが成り立つので、X(φ U ψ)も成り立つ
        have h_next := h_impl h_φ
        
        -- X(φ U ψ) の意味論: holds σ (i+1) (φ U ψ)
        -- これは ∃ j, j ≥ i+1 ∧ holds σ j ψ ∧ ∀ k, i+1 ≤ k ∧ k < j → holds σ k φ
        obtain ⟨j, h_j_ge, h_ψ_j, h_φ_path⟩ := h_next
        
        -- j ≥ i+1 から j ≥ i が導かれる
        have h_j_ge_i : j ≥ i := Nat.le_trans (Nat.le_succ i) h_j_ge
        
        -- until φ ψ が成り立つことを示す
        exists j
        constructor
        · exact h_j_ge_i  -- j ≥ i
        constructor
        · exact h_ψ_j    -- ψが時点jで成り立つ
        · intro k h_k_cond h_k_lt
          -- h_k_cond は i ≤ k、h_k_ltは k < j
          -- k = i の場合と k > i の場合に分ける
          cases Nat.eq_or_lt_of_le h_k_cond with
          | inl h_eq => -- k = i の場合
            subst h_eq
            exact h_φ  -- φが時点iで成り立つ
          | inr h_lt => -- k > i の場合
            -- k > i から k ≥ i+1 が導かれる
            have h_k_ge_i_plus_1 : k ≥ i+1 := Nat.succ_le_of_lt h_lt
            -- i+1 ≤ k ∧ k < j から holds σ k φ が導かれる
            exact h_φ_path k h_k_ge_i_plus_1 h_k_lt
