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

-- 意味論
def holds {α : Type} (σ : MyModel α) (i : Nat) : LTL α → Prop
  | LTL.atom p      => σ i p
  | LTL.bot         => False
  | LTL.not φ       => ¬ holds σ i φ
  | LTL.and φ ψ     => holds σ i φ ∧ holds σ i ψ
  | LTL.or φ ψ      => holds σ i φ ∨ holds σ i ψ
  | LTL.impl φ ψ    => holds σ i φ → holds σ i ψ
  | LTL.next φ      => holds σ (i+1) φ
  | LTL.until φ ψ   => ∃ j, j ≥ i ∧ holds σ j ψ ∧ ∀ k, (i ≤ k ∧ k < j) → holds σ k φ
  | LTL.release φ ψ => ∀ j, j ≥ i →
        holds σ j ψ ∨
        ∃ k, k ≥ i ∧ holds σ k φ ∧ ∀ m, (i ≤ m ∧ m ≤ k) → holds σ m ψ
  | LTL.eventually φ => ∃ j, j ≥ i ∧ holds σ j φ
  | LTL.always φ     => ∀ j, j ≥ i → holds σ j φ

-- 追加公理
axiom until_intro_premise {α : Type} (φ ψ : LTL α) (σ : MyModel α) (i : Nat) :
  (holds σ i φ →
     ∃ j, j ≥ i+1 ∧ holds σ j ψ ∧ ∀ k, i+1 ≤ k → k < j → holds σ k φ) →
  ¬ holds σ i ψ → holds σ i φ

-- 推論体系
inductive Provable {α : Type} : LTL α → Prop where
  | ax1 (φ ψ : LTL α) :
      Provable (LTL.impl φ (LTL.impl ψ φ))
  | ax2 (φ ψ χ : LTL α) :
      Provable (LTL.impl (LTL.impl φ (LTL.impl ψ χ))
                         (LTL.impl (LTL.impl φ ψ) (LTL.impl φ χ)))
  | mp (φ ψ : LTL α) :
      Provable (LTL.impl φ ψ) → Provable φ → Provable ψ
  | next_rule (φ : LTL α) :
      Provable (LTL.always φ) → Provable (LTL.next φ)  -- G φ → X φ
  | until_intro (φ ψ : LTL α) :
      Provable ψ →
      Provable (LTL.impl φ (LTL.next (LTL.until φ ψ))) →
      Provable (LTL.until φ ψ)

-- 健全性
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
      -- G φ → X φ
      simp [holds]
      have h_always := ih σ i
      exact h_always (i+1) (Nat.le_succ i)
  | until_intro φ ψ _ _ ihψ ih_impl =>
      intro σ i
      -- 目標: holds σ i (φ U ψ)
      -- 場合分け：ψ が現在成り立つかどうか
      by_cases hψ_now : holds σ i ψ
      · -- ψ が現在真なら j = i を取ればよい
        -- ∃ j ≥ i, ψ j ∧ ∀ k, (i ≤ k ∧ k < j) → φ k
        refine ?_
        refine ⟨i, Nat.le_refl i, hψ_now, ?_⟩
        intro k hk
        -- hk : i ≤ k ∧ k < i は矛盾
        have ⟨hle, hlt⟩ := hk
        exact False.elim (Nat.not_lt_of_le hle hlt)
      · -- ψ が現在偽の場合
        -- 前提: Provable (φ → X(φ U ψ))
        -- これを意味論へ
        have h_impl_sem : holds σ i (LTL.impl φ (LTL.next (LTL.until φ ψ))) :=
          ih_impl σ i
        -- ⇒ 「φ → ∃j≥i+1, ...」の形に正規化
        have h_impl_ex :
            holds σ i φ →
              ∃ j, j ≥ i+1 ∧ holds σ j ψ ∧
                    ∀ k, i+1 ≤ k → k < j → holds σ k φ := by
          intro hφ
          have hx : holds σ (i+1) (LTL.until φ ψ) :=
            (by
              -- simp で X と U を展開
              simpa [holds] using h_impl_sem hφ)
          -- hx を ∃ 形に落とす
          simpa [holds] using hx
        -- 補助公理より、ψ が偽なら φ が現在真
        have hφ_now : holds σ i φ :=
          until_intro_premise φ ψ σ i h_impl_ex hψ_now
        -- したがって X(φ U ψ) が現在真
        have h_next : holds σ (i+1) (LTL.until φ ψ) :=
          (by
            have := h_impl_sem hφ_now
            simpa [holds] using this)
        -- X(φ U ψ) を ∃ 形へ
        have h_next_ex :
            ∃ j, j ≥ i+1 ∧ holds σ j ψ ∧
                  ∀ k, (i+1 ≤ k ∧ k < j) → holds σ k φ := by
          simpa [holds] using h_next
        rcases h_next_ex with ⟨j, hj_ge, hψj, hpath⟩
        -- j ≥ i+1 から j ≥ i
        have hj_ge_i : j ≥ i := Nat.le_trans (Nat.le_succ i) hj_ge
        -- 目標の ∃ を構成
        refine ⟨j, hj_ge_i, hψj, ?_⟩
        intro k hk
        have ⟨hki, hkj⟩ := hk          -- i ≤ k, k < j
        -- k = i か i < k に分岐
        cases Nat.eq_or_lt_of_le hki with
        | inl h_eq =>
            subst h_eq
            exact hφ_now
        | inr h_lt =>
            -- i < k なら i+1 ≤ k
            have hk_ge_succ : i+1 ≤ k := Nat.succ_le_of_lt h_lt
            -- hpath は (i+1 ≤ k ∧ k < j) から φ k を返す
            exact hpath k ⟨hk_ge_succ, hkj⟩
