import Mathlib
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic
theorem am_gm (a b : ℝ) (ha : (0 : ℝ) ≤ a) (hb : (0 : ℝ) ≤ b) :
  (a + b) / 2 ≥ √(a * b) := by
  have h : (√a - √b) ^ 2 ≥ 0 := sq_nonneg (√a - √b)
  rw [sub_sq] at h
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb] at h
  have h1: a - 2 * √a * √b + b = a + b - 2 * (√a * √b) := by ring
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

  have h_pos : 0 < a + b := add_pos ha hb
  have h_sqrt_pos : 0 < √(a * b) := Real.sqrt_pos.mpr (mul_pos ha hb)

  have h_am_gm : (a + b) / 2 ≥ √(a * b) := am_gm a b (le_of_lt ha) (le_of_lt hb)

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
  have div_sqrt: a * b / √(a * b) = √(a * b) := by
    simp
  have : a * b * (2 / (a + b)) = 2 * a * b / (a + b) := by ring
  rw [this] at step1
  have : a * b * (1 / √(a * b)) = a * b / √(a * b) := by ring
  rw [this, div_sqrt] at step1
  exact step1

theorem qm_am (a b : ℝ) (ha : (0 : ℝ) ≤ a) (hb : (0 : ℝ) ≤ b) :
  √((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 := by
  have h_sq1 : a ^ 2 - 2 * a * b + b ^ 2 = (a - b)  ^  2 := by
    linarith
  have h_sq2 : (a - b)  ^  2 ≥ 0 := sq_nonneg (a - b)
  have h_sq3 : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := by
    rw[h_sq1]
    exact h_sq2
  have h_sq4 : -(a ^ 2) + 2 * a * b -(b ^ 2) ≤ 0 := by
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
  have h_sq9 : √((a + b) ^ 2 / 4) = √((a + b) ^ 2) / √4  := by
    exact Real.sqrt_div (pow_two_nonneg (a + b)) 4
  have h_sqa : √((a + b) ^ 2) / √4 = (a + b) / 2 := by
    rw [Real.sqrt_sq (add_nonneg ha hb), show √4 = 2 by norm_num]
  have h_sqb : √((a ^ 2 + b ^ 2) / 2) ≥ √((a + b) ^ 2) / √4 := by
    rw[h_sq9] at h_sq8
    exact h_sq8
  have h_final : √((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 := by
    rw[h_sqa] at h_sqb
    exact h_sqb
  exact h_final

theorem qm_am_gm_hm_chain (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  √((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 ∧
  (a + b) / 2 ≥ √(a * b) ∧
  √(a * b) ≥ 2 / (1 / a + 1 / b) :=
  ⟨ qm_am a b (le_of_lt ha) (le_of_lt hb),
    am_gm a b (le_of_lt ha) (le_of_lt hb),
    gm_hm a b ha hb ⟩

theorem am_gm_eq_iff (a b : ℝ) (hb : 0 ≤ b) (hab : a = b) :
  (a + b) / 2 = √(a * b) := by
  have h1 : (a + b) / 2 = a := by
    linarith
  have h2 : √(a * b) = a := by
    rw[hab]
    exact Real.sqrt_mul_self hb
  have h3 : a = √(a * b) := by
    linarith
  have h_final : (a + b) / 2 = √(a * b) := by
    rw[h3] at h1
    exact Mathlib.Tactic.Ring.div_congr (congrFun (congrArg HAdd.hAdd h3) b) rfl h1
  exact h_final

theorem gm_hm_eq_iff (a b : ℝ) (hb : 0 < b) (hab : a = b) :
  √(a * b) = 2 / (1 / a + 1 / b) := by
  have h1 : 2 / (1 / a + 1 / b) = a := by
    rw[hab]
    field_simp
    ring
  have h2 : √(a * b) = a := by
    rw[hab]
    exact (Real.sqrt_eq_iff_mul_self_eq_of_pos hb).mpr rfl
  have h3 : a = √(a * b) := by
    linarith
  have h_final : √(a * b) = 2 / (1 / a + 1 / b) := by
    rw[h1,h2]
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
    rw[h1,h2]
  exact h_final

theorem qm_am_gm_hm_chain_eq_iff (a b : ℝ) (hb : 0 < b) (hab : a = b) :
    √((a ^ 2 + b ^ 2) / 2) = (a + b) / 2 ∧
    (a + b) / 2 = √(a * b) ∧
    √(a * b) = 2 / (1 / a + 1 / b) :=
  ⟨ qm_am_eq_iff a b (le_of_lt hb) hab,
    am_gm_eq_iff a b (le_of_lt hb) hab,
    gm_hm_eq_iff a b hb hab ⟩
