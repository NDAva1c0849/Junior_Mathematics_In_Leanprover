import Mathlib
import Mathlib.Algebra.Order.Nonneg.Basic  -- 基础定义
import Mathlib.Algebra.Order.Nonneg.Ring   -- 非负环的定义
import Mathlib.Tactic.Linarith  -- 线性推理
import Mathlib.Data.Real.Basic -- 实数的基本定义
import Mathlib.Data.Real.Sqrt -- 实数的平方根
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic
import Mathlib.Order.Defs.LinearOrder

theorem am_gm (a b : ℝ) (ha : (0 : ℝ) ≤ a) (hb : (0 : ℝ) ≤ b) :
    (a + b) / 2 ≥ √(a * b) := by
  have h : (√a - √b) ^ 2 ≥ 0 := sq_nonneg (√a - √b)
  -- 展开平方
  rw [sub_sq] at h
  -- 简化平方根平方
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb] at h
  have h1 : a - 2 * √a * √b + b = a + b - 2 * (√a * √b) := by ring
  rw [h1] at h
  have h2 : √a * √b = √(a * b) := by
    rw [Real.sqrt_mul ha b]
  rw [h2] at h
  linarith

theorem gm_hm (a b : ℝ) (ha : (0 : ℝ) < a) (hb : (0 : ℝ) < b) :
    2 / (1 / a + 1 / b) ≤ √(a * b) := by
  have h_harmonic : 2 / (1 / a + 1 / b) = 2 * a * b / (a + b) := by
    field_simp
    ring

  rw [h_harmonic]

  -- 两边乘以 (a + b) 并除以 √(a * b)（因为 a, b > 0，所以这些操作保持不等式方向）
  have h_pos : 0 < a + b := add_pos ha hb
  have h_sqrt_pos : 0 < √(a * b) := Real.sqrt_pos.mpr (mul_pos ha hb)

  -- 两边乘以 (a + b) * √(a * b)，得到 2ab√(ab) ≤ (a + b)(ab)
  have h_am_gm : (a + b) / 2 ≥ √(a * b) := am_gm a b (le_of_lt ha) (le_of_lt hb)

  -- 将 AM-GM 不等式两边取倒数并调整
  have h_inv : 2 / (a + b) ≤ 1 / √(a * b) := by
    have h_denom_pos : 0 < (a + b) * √(a * b) := mul_pos h_pos h_sqrt_pos
    rw [div_le_div_iff₀ h_pos h_sqrt_pos, one_mul, mul_comm]
    have h_patch : (a + b) / 2 ≥ √(a * b) ↔ √(a * b) * 2 ≤ a + b := by
      have h_sqrt_nonneg : 0 ≤ √(a * b) := Real.sqrt_nonneg _
      have h_two_pos : 0 < (2 : ℝ) := by norm_num
      rw [ge_iff_le, le_div_iff₀ h_two_pos, mul_comm]
    rw [h_patch] at h_am_gm
    exact h_am_gm
  have step1 := mul_le_mul_of_nonneg_left h_inv (le_of_lt (mul_pos ha hb))
  simp
  have div_sqrt : a * b / √(a * b) = √(a * b) := by
    simp
  have : a * b * (2 / (a + b)) = 2 * a * b / (a + b) := by ring
  rw [this] at step1
  have : a * b * (1 / √(a * b)) = a * b / √(a * b) := by ring
  rw [this, div_sqrt] at step1
  exact step1

theorem qm_am (a b : ℝ) (ha : (0 : ℝ) ≤ a) (hb : (0 : ℝ) ≤ b) :
    √((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 := by
  have h_sq1 : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by
    linarith
  have h_sq2 : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  have h_sq3 : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := by
    rw [h_sq1]
    exact h_sq2
  have h_sq4 : -(a ^ 2) + 2 * a * b - (b ^ 2) ≤ 0 := by
    have : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := h_sq3
    linarith
  have h_sq5 : 2 * a ^ 2 + 2 * b ^ 2 ≥ a ^ 2 + 2 * a * b + b ^ 2 := by
    linarith
  have h_sq6 : (a ^ 2 + b ^ 2) / 2 ≥ (a ^ 2 + 2 * a * b + b ^ 2) / 4 := by
    linarith
  have h_sq7 : (a ^ 2 + b ^ 2) / 2 ≥ (a + b) ^ 2 / 4 := by
    linarith
  have h_sq8 : √((a ^ 2 + b ^ 2) / 2) ≥ √((a + b) ^ 2 / 4) :=
    Real.sqrt_le_sqrt h_sq7
  have h_sq9 : √((a + b) ^ 2 / 4) = √((a + b) ^ 2) / √4 := by
    exact Real.sqrt_div (pow_two_nonneg (a + b)) 4
  have h_sqa : √((a + b) ^ 2) / √4 = (a + b) / 2 := by
    rw [Real.sqrt_sq (add_nonneg ha hb), show √4 = 2 by norm_num]
  have h_sqb : √((a ^ 2 + b ^ 2) / 2) ≥ √((a + b) ^ 2) / √4 := by
    rw [h_sq9] at h_sq8
    exact h_sq8
  have h_final : √((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 := by
    rw [h_sqa] at h_sqb
    exact h_sqb
  exact h_final

theorem qm_am_gm_hm_chain (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    √((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 ∧
    (a + b) / 2 ≥ √(a * b) ∧
    √(a * b) ≥ 2 / (1 / a + 1 / b) :=
  ⟨qm_am a b (le_of_lt ha) (le_of_lt hb),
    am_gm a b (le_of_lt ha) (le_of_lt hb),
    gm_hm a b ha hb⟩

-- 以下条件中均省略 a 的大小限制，因为已经假设 a = b
theorem am_gm_eq_iff (a b : ℝ) (hb : 0 ≤ b) (hab : a = b) :
    (a + b) / 2 = √(a * b) := by
  have h1 : (a + b) / 2 = a := by
    linarith
  have h2 : √(a * b) = a := by
    rw [hab]
    exact Real.sqrt_mul_self hb
  have h3 : a = √(a * b) := by
    linarith
  have h_final : (a + b) / 2 = √(a * b) := by
    rw [h3] at h1
    exact Mathlib.Tactic.Ring.div_congr (congrFun (congrArg HAdd.hAdd h3) b) rfl h1 -- apply?
  exact h_final

theorem gm_hm_eq_iff (a b : ℝ) (hb : 0 < b) (hab : a = b) :
    √(a * b) = 2 / (1 / a + 1 / b) := by
  have h1 : 2 / (1 / a + 1 / b) = a := by
    rw [hab]
    field_simp
    ring
  have h2 : √(a * b) = a := by
    rw [hab]
    exact (Real.sqrt_eq_iff_mul_self_eq_of_pos hb).mpr rfl
  have h3 : a = √(a * b) := by
    linarith
  have h_final : √(a * b) = 2 / (1 / a + 1 / b) := by
    rw [h1, h2]
  exact h_final

theorem qm_am_eq_iff (a b : ℝ) (hb : 0 ≤ b) (hab : a = b) :
    √((a ^ 2 + b ^ 2) / 2) = (a + b) / 2 := by
  have h1 : √((a ^ 2 + b ^ 2) / 2) = a := by
    rw [hab]
    simp
    exact Real.sqrt_sq hb
  have h2 : (a + b) / 2 = a := by
    linarith
  have h_final : √((a ^ 2 + b ^ 2) / 2) = (a + b) / 2 := by
    rw [h1, h2]
  exact h_final

theorem qm_am_gm_hm_chain_eq_iff (a b : ℝ) (hb : 0 < b) (hab : a = b) :
    √((a ^ 2 + b ^ 2) / 2) = (a + b) / 2 ∧
    (a + b) / 2 = √(a * b) ∧
    √(a * b) = 2 / (1 / a + 1 / b) :=
  ⟨qm_am_eq_iff a b (le_of_lt hb) hab,
    am_gm_eq_iff a b (le_of_lt hb) hab,
    gm_hm_eq_iff a b hb hab⟩ -- le_of_lt : a > b → a >= b

theorem cauchy_schwarz_inequality (a b c d : ℝ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) ≥ (a * c + b * d) ^ 2 := by
  have h1 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
          = a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2
          + b ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 := by
    linarith
  have h2 : (a * c + b * d) ^ 2
          = (a * c) ^ 2 + 2 * a * b * c * d + (b * d) ^ 2 := by
    linarith
  have h3 : (a * c) ^ 2 + 2 * a * b * c * d + (b * d) ^ 2
          = a ^ 2 * c ^ 2 + 2 * a * b * c * d + b ^ 2 * d ^ 2 := by
    linarith
  have h4 : a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2 + b ^ 2 * d ^ 2
          - (a ^ 2 * c ^ 2 + 2 * a * b * c * d + b ^ 2 * d ^ 2)
          = a ^ 2 * d ^ 2 - 2 * a * b * c * d + b ^ 2 * c ^ 2 := by
    linarith
  have h5 : a ^ 2 * d ^ 2 - 2 * a * b * c * d + b ^ 2 * c ^ 2
          = (a * d - b * c) ^ 2 := by
    linarith
  have h6 : (a * d - b * c) ^ 2 ≥ 0 := by
    exact sq_nonneg (a * d - b * c)
  have h7 : (a * d - b * c) ^ 2
          = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
          - (a * c + b * d) ^ 2 := by
    linarith
  have h8 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
          - (a * c + b * d) ^ 2 ≥ 0 := by
    rw [h7] at h6
    exact h6
  have h_final : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) ≥ (a * c + b * d) ^ 2 := by
    linarith
  exact h_final
theorem cauchy_schwarz_inequality_eq_iff (a b c d : ℝ) (habcd : a * d = b * c) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 := by
  have h1 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
          = a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2
          + b ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 := by
    linarith
  have h2 : (a * d) ^ 2 = (b * c) ^ 2 := by
    rw [habcd]
  have h3 : a ^ 2 * d ^ 2 = b ^ 2 * c ^ 2 := by
    linarith
  have h4 : b ^ 2 * c ^ 2 + a ^ 2 * d ^ 2 = 2 * a ^ 2 * d ^ 2 := by
    rw [h3]
    linarith
  have h5 : a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * d ^ 2 + b ^ 2 * d ^ 2
          = a ^ 2 * c ^ 2 + 2 * a ^ 2 * d ^ 2 + b ^ 2 * d ^ 2 := by
    linarith
  have h6 : 2 * a ^ 2 * d ^ 2 = 2 * a * (a * d) * d := by
    linarith
  have h7 : 2 * a * (a * d) * d = 2 * a * (b * c) * d := by
    rw [habcd]
  have h8 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
          = a ^ 2 * c ^ 2 + 2 * a * b * c * d + b ^ 2 * d ^ 2 := by
    linarith
  have h9 : (a * c + b * d) ^ 2 = a ^ 2 * c ^ 2 + 2 * a * b * c * d + b ^ 2 * d ^ 2 := by
    linarith
  have h_final : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 := by
    linarith
  exact h_final
theorem abs_inequality_pos (a b : ℝ) : (|(|a| - |b|)| ≤ |a + b| ∧ |a + b| ≤ |a| + |b|) := by
  have h_1 : -|a| ≤ a ∧ a ≤ |a| := by
    apply abs_le.1
    exact le_refl |a|
  have h_2 : -|b| ≤ b ∧ b ≤ |b| := by
    apply abs_le.1
    exact le_refl |b|
  have h_3 : a + b ≤ |a| + |b| := by
    linarith
  have h_4 : |a + b| ≤ |a| + |b| := by
    have h_5 (hab : a + b ≥ 0) : |a + b| ≤ |a| + |b| := by
      have h_5_1 : |a + b| = a + b := by
        exact abs_of_nonneg hab
      have h_5_2 : a + b ≤ |a| + |b| := by
        linarith
      have h_5_final : |a + b| ≤ |a| + |b| := by
        linarith
      exact h_5_final
    have h_6 (hab : a + b < 0) : |a + b| ≤ |a| + |b| := by
      have h_6_1 : |a + b| = -(a + b) := by
        exact abs_of_neg hab
      have h_6_2 : a + b ≥ -|a| - |b| := by
        linarith
      have h_6_final : |a + b| ≤ |a| + |b| := by
        linarith
      exact h_6_final
    have h_7 : a + b ≥ 0 ∨ a + b < 0 := by
      exact le_or_lt 0 (a + b)
    have h_8 : |a + b| ≤ |a| + |b| := by
      cases h_7 with
      | inl hab => exact h_5 hab
      | inr hab => exact h_6 hab
    exact h_8
  have h_9 : |(|a| - |b|)| ≤ |a + b| := by
    have h_9_1 : |(|a| - |b|)| ≥ 0 := by
      exact abs_nonneg (|a| - |b|)

    have h_9_2 : |a + b| ≥ 0 := by
      exact abs_nonneg (a + b)

    have h_9_3 : (|(|a| - |b|)|) ^ 2 = |a| ^ 2 - 2 * |a| * |b| + |b| ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      rw [abs_sq_lemma (|a| - |b|)]
      rw [sub_sq]
    have h_9_4 : (|a + b|) ^ 2 = (a + b) ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      exact abs_sq_lemma (a + b)
    have h_9_5 : (|a + b|) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
      linarith
    have h_9_6 : |a| ^ 2 - 2 * |a| * |b| + |b| ^ 2 = a ^ 2 - 2 * |a * b| + b ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      rw [abs_sq_lemma a, abs_sq_lemma b]
      rw [abs_mul a b]
      linarith
    have h_9_7 : (|(|a| - |b|)|) ^ 2 = a ^ 2 - 2 * |a * b| + b ^ 2 := by
      linarith
    have h_9_8 : -2 * |a * b| ≤ 2 * a * b := by
      cases le_or_lt (a * b) 0 with
      | inl h =>  -- a * b ≤ 0
        rw [abs_of_nonpos h]
        linarith
      | inr h =>  -- a * b > 0
        rw [abs_of_pos h]
        linarith
    have h_9_9 : a ^ 2 - 2 * |a * b| + b ^ 2 ≤ a ^ 2 + 2 * a * b + b ^ 2 := by
      have h_9_9_1 : a ^ 2 ≥ 0 := by
        exact sq_nonneg a
      have h_9_9_2 : b ^ 2 ≥ 0 := by
        exact sq_nonneg b
      have h_9_9_3 : -2 * |a * b| = -(2 * |a * b|) := by
        linarith
      apply add_le_add_right
      apply add_le_add_left
      rw [h_9_9_3] at h_9_8
      exact h_9_8
    have h_9_10 : (|(|a| - |b|)|) ^ 2 ≤ (|a + b|) ^ 2 := by
      linarith
    have h_9_11 : |(|a| - |b|)| ≤ |a + b| := by
      refine abs_le_of_sq_le_sq ?_ h_9_2
      have h_9_11_1 : |(|a| - |b|)| ^ 2 = (|a| - |b|) ^ 2 := by
        linarith
      rw [h_9_11_1] at h_9_10
      exact h_9_10
    exact h_9_11
  have h_final : (|(|a| - |b|)| ≤ |a + b| ∧ |a + b| ≤ |a| + |b|) := by
    exact ⟨h_9, h_4⟩
  exact h_final
theorem abs_inequality_neg (a b : ℝ) : (|(|a| - |b|)| ≤ |a - b| ∧ |a - b| ≤ |a| + |b|) := by
  have h_1 : -|a| ≤ a ∧ a ≤ |a| := by
    apply abs_le.1
    exact le_refl |a|
  have h_2 : -|b| ≤ b ∧ b ≤ |b| := by
    apply abs_le.1
    exact le_refl |b|
  have h_3 : |(|a| - |b|)| ≤ |a - b| := by
    have h_3_1 : |a - b| ≥ 0 := by
      exact abs_nonneg (a - b)
    have h_3_2 : |a| + |b| ≥ 0 := by
      linarith
    have h_3_3 : (|a - b|) ^ 2 = (a - b) ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      exact abs_sq_lemma (a - b)
    have h_3_4 : (|a - b|) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
      linarith
    have h_3_5 : (|(|a| - |b|)|) ^ 2 = (|a| - |b|) ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      exact abs_sq_lemma (|a| - |b|)
    have h_3_6 : (|(|a| - |b|)|) ^ 2 = (|a|) ^ 2 - 2 * |a| * |b| + (|b|) ^ 2 := by
      linarith
    have h_3_7 : |a| ^ 2 - 2 * |a| * |b| + |b| ^ 2 = a ^ 2 - 2 * |a * b| + b ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      rw [abs_sq_lemma a, abs_sq_lemma b]
      rw [abs_mul a b]
      linarith
    have h_3_8 : (|(|a| - |b|)|) ^ 2 = a ^ 2 - 2 * |a * b| + b ^ 2 := by
      linarith
    have h_3_9 : |a * b| ≥ a * b := by
      exact le_abs_self (a * b)
    have h_3_10 : -2 * |a * b| ≤ -2 * a * b := by
      linarith
    have h_3_11 : a ^ 2 - 2 * |a * b| + b ^ 2 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
      have h_3_11_1 : a ^ 2 ≥ 0 := by
        exact sq_nonneg a
      have h_3_11_2 : b ^ 2 ≥ 0 := by
        exact sq_nonneg b
      have h_3_11_3 : -2 * |a * b| = -(2 * |a * b|) := by
        linarith
      have h_3_11_4 : -2 * a * b = -(2 * a * b) := by
        linarith
      apply add_le_add_right
      apply add_le_add_left
      rw [h_3_11_3] at h_3_10
      rw [h_3_11_4] at h_3_10
      exact h_3_10
    have h_3_12 : (|(|a| - |b|)|) ^ 2 ≤ (|a - b|) ^ 2 := by
      linarith
    have h_3_13 : |(|a| - |b|)| ≤ |a - b| := by
      refine abs_le_of_sq_le_sq ?_ h_3_1
      have h_3_13_1 : |(|a| - |b|)| ^ 2 = (|a| - |b|) ^ 2 := by
        linarith
      rw [h_3_13_1] at h_3_12
      exact h_3_12
    exact h_3_13
  have h_4 : |a - b| ≤ |a| + |b| := by
    have h_4_1 (hab : a - b ≥ 0) : |a - b| ≤ |a| + |b| := by
      have h_4_1_1 : |a - b| = a - b := by
        exact abs_of_nonneg hab
      have h_4_1_2 : a - b ≤ |a| + |b| := by
        linarith
      have h_4_1_final : |a - b| ≤ |a| + |b| := by
        linarith
      exact h_4_1_final
    have h_4_2 (hab : a - b < 0) : |a - b| ≤ |a| + |b| := by
      have h_4_2_1 : |a - b| = -(a - b) := by
        exact abs_of_neg hab
      have h_4_2_2 : a - b ≥ -|a| - |b| := by
        linarith
      have h_4_2_final : |a - b| ≤ |a| + |b| := by
        linarith
      exact h_4_2_final
    have h_4_3 : a - b ≥ 0 ∨ a - b < 0 := by
      exact le_or_lt 0 (a - b)
    have h_4_4 : |a - b| ≤ |a| + |b| := by
      cases h_4_3 with
      | inl hab => exact h_4_1 hab
      | inr hab => exact h_4_2 hab
    exact h_4_4
  exact ⟨h_3, h_4⟩

theorem abs_inequality_eq_iff_upper (a b : ℝ) (hab : a * b ≥ 0) : |a + b| = |a| + |b| := by
  have h_1 : -|a| ≤ a ∧ a ≤ |a| := by
    apply abs_le.1
    exact le_refl |a|
  have h_2 : -|b| ≤ b ∧ b ≤ |b| := by
    apply abs_le.1
    exact le_refl |b|
  have h_3 : |(|a| - |b|)| ≥ 0 := by
    exact abs_nonneg (|a| - |b|)
  have h_4 : |a - b| ≥ 0 := by
    exact abs_nonneg (a - b)
  have h_5 : |a + b| ≥ 0 := by
    exact abs_nonneg (a + b)
  have h_6 : |a| + |b| ≥ 0 := by
    linarith
  have h_7 : |a + b| = |a| + |b| := by
    have h_7_1 : (|a + b|) ^ 2 = (a + b) ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      exact abs_sq_lemma (a + b)
    have h_7_2 : (|a| + |b|) ^ 2 = |a| ^ 2 + 2 * |a| * |b| + |b| ^ 2 := by
      linarith
    have h_7_3 : |a| ^ 2 = a ^ 2 := by
      exact sq_abs a
    have h_7_4 : |b| ^ 2 = b ^ 2 := by
      exact sq_abs b
    have h_7_5 : (|a| + |b|) ^ 2 = a ^ 2 + 2 * |a| * |b| + b ^ 2 := by
      linarith
    have h_7_6 : |a * b| = |a| * |b| := by
      exact abs_mul a b
    have h_7_7 : (|a| + |b|) ^ 2 = a ^ 2 + 2 * |a * b| + b ^ 2 := by
      linarith
    have h_7_8 : (|a + b|) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
      linarith
    have h_7_9 : 2 * a * b = 2 * |a * b| := by
      rw [abs_of_nonneg hab]
      linarith
    have h_7_10 : a ^ 2 + 2 * a * b + b ^ 2 = a ^ 2 + 2 * |a * b| + b ^ 2 := by
      linarith
    have h_7_11 : (|a + b|) ^ 2 = (|a| + |b|) ^ 2 := by
      linarith
    have h_7_12 : |a + b| = |a| + |b| := by
      have h_sq_eq : (|a + b|) ^ 2 = (|a| + |b|) ^ 2 := h_7_11
      have h_nonneg_left : 0 ≤ |(|a| - |b|)| := h_3
      have h_nonneg_right : 0 ≤ |a - b| := h_4
      rw [sq_eq_sq_iff_abs_eq_abs] at h_sq_eq
      have h_sq_eq_tmp_1 : |(|a + b|)| = |a + b| := by
        exact abs_abs (a + b)
      have h_sq_eq_tmp_2 : |(|a| + |b|)| = |a| + |b| := by
        exact abs_of_nonneg h_6
      rw [h_sq_eq_tmp_1] at h_sq_eq
      rw [h_sq_eq_tmp_2] at h_sq_eq
      exact h_sq_eq
    exact h_7_12
  exact h_7

theorem abs_inequality_eq_iff_lower (a b : ℝ) (hab : (a = 0 ∨ b = 0) ∨ (a * b ≥ 0 ∧ |a| ≥ |b|)) : (|(|a| - |b|)| = |a - b|) := by
  have h_1 : -|a| ≤ a ∧ a ≤ |a| := by
    apply abs_le.1
    exact le_refl |a|
  have h_2 : -|b| ≤ b ∧ b ≤ |b| := by
    apply abs_le.1
    exact le_refl |b|
  have h_3 : |(|a| - |b|)| ≥ 0 := by
    exact abs_nonneg (|a| - |b|)
  have h_4 : |a - b| ≥ 0 := by
    exact abs_nonneg (a - b)
  have h_5 : |a + b| ≥ 0 := by
    exact abs_nonneg (a + b)
  have h_6 : |a| + |b| ≥ 0 := by
    linarith
  have h_7 : |(|a| - |b|)| = |a - b| := by
    have h_7_1 : (|(|a| - |b|)|) ^ 2 = |a| ^ 2 - 2 * |a| * |b| + |b| ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      rw [abs_sq_lemma (|a| - |b|)]
      rw [sub_sq]
    have h_7_2 : (|a - b|) ^ 2 = (a - b) ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      exact abs_sq_lemma (a - b)
    have h_7_3 : (|a - b|) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
      linarith
    have h_7_4 : |a| ^ 2 - 2 * |a| * |b| + |b| ^ 2 = a ^ 2 - 2 * |a * b| + b ^ 2 := by
      have abs_sq_lemma (x : ℝ) : |x| ^ 2 = x ^ 2 := by
        rw [sq, sq]
        exact abs_mul_abs_self x
      rw [abs_sq_lemma a, abs_sq_lemma b]
      rw [abs_mul a b]
      linarith
    have h_7_5 : (|(|a| - |b|)|) ^ 2 = a ^ 2 - 2 * |a * b| + b ^ 2 := by
      linarith
    have h_7_6 : -2 * |a * b| = -2 * a * b := by
      cases hab with
      | inl h_zero =>
        cases h_zero with
        | inl ha =>
          rw [ha]
          simp only [zero_mul, abs_zero, mul_zero, neg_zero]
        | inr hb =>
          rw [hb]
          simp only [mul_zero, abs_zero, zero_mul, neg_zero]
      | inr h_nonneg =>
        rcases h_nonneg with ⟨hab_ge, h_abs⟩
        rw [abs_of_nonneg hab_ge]
        rw [mul_assoc]
    have h_7_7 : (|(|a| - |b|)|) ^ 2 = (|a - b|) ^ 2 := by
      linarith
    have h_7_8 : |(|a| - |b|)| = |a - b| := by
      have h_sq_eq : |(|a| - |b|)| ^ 2 = |a - b| ^ 2 := h_7_7
      have h_nonneg_left : 0 ≤ |(|a| - |b|)| := h_3
      have h_nonneg_right : 0 ≤ |a - b| := h_4
      rw [sq_eq_sq_iff_abs_eq_abs] at h_sq_eq
      have h_sq_eq_tmp_1 : |(|(|a| - |b|)|)| = |(|a| - |b|)| := by
        exact abs_abs (|a| - |b|)
      have h_sq_eq_tmp_2 : |(|a - b|)| = |a - b| := by
        exact abs_abs (a - b)
      rw [h_sq_eq_tmp_1] at h_sq_eq
      rw [h_sq_eq_tmp_2] at h_sq_eq
      exact h_sq_eq
    exact h_7_8
  exact h_7
