import KEBall.DirichletOscillationGeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Interpolation of quarter-scale geometric decay to an all-radius power bound. -/

set_option autoImplicit false

namespace KEBall

theorem exists_dirichlet_decay_exponent {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ τ ≤ (1 / 4 : ℝ) ^ α := by
  let b : ℝ := Real.log τ / Real.log (1 / 4 : ℝ)
  have hlogq : Real.log (1 / 4 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hb : 0 < b := div_pos_of_neg_of_neg (Real.log_neg hτ0 hτ1) hlogq
  have hpow : (1 / 4 : ℝ) ^ b = τ := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have he : Real.log (1 / 4 : ℝ) * b = Real.log τ := by
      dsimp only [b]
      field_simp
    rw [he, Real.exp_log hτ0]
  refine ⟨min 1 b, lt_min zero_lt_one hb, min_le_left _ _, ?_⟩
  rw [← hpow]
  exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (min_le_right _ _)

theorem dirichlet_power_bound_of_geometric
    (o : ℝ → ℝ) {R₀ D τ α : ℝ} (hR₀ : 0 < R₀) (hD : 0 ≤ D)
    (hτ0 : 0 ≤ τ) (hα : 0 ≤ α) (hτα : τ ≤ (1 / 4 : ℝ) ^ α)
    (hMono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ R₀ → o r ≤ o s)
    (hGeo : ∀ k : ℕ, o (R₀ * (1 / 4 : ℝ) ^ k) ≤ D * τ ^ k)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R₀) :
    o r ≤ (D * (4 / R₀ : ℝ) ^ α) * r ^ α := by
  obtain ⟨k, hkSmall, hkLarge⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hR₀) ((div_le_one hR₀).mpr hrR)
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
  have hOuter : R₀ * (1 / 4 : ℝ) ^ k ≤ R₀ :=
    mul_le_of_le_one_right hR₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hInner : r ≤ R₀ * (1 / 4 : ℝ) ^ k := by
    have h := (div_le_iff₀ hR₀).mp hkLarge
    simpa only [mul_comm R₀] using h
  have hScale : (1 / 4 : ℝ) ^ k ≤ (4 / R₀) * r := by
    have h := (lt_div_iff₀ hR₀).mp hkSmall
    rw [pow_succ] at h
    have h' : (1 / 4 : ℝ) ^ k * R₀ ≤ 4 * r := by nlinarith
    calc
      _ ≤ (4 * r) / R₀ := (le_div_iff₀ hR₀).mpr h'
      _ = _ := by ring
  calc
    o r ≤ o (R₀ * (1 / 4 : ℝ) ^ k) := hMono _ _ hr hInner hOuter
    _ ≤ D * τ ^ k := hGeo k
    _ ≤ D * ((1 / 4 : ℝ) ^ α) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ0 hτα k) hD
    _ = D * ((1 / 4 : ℝ) ^ k) ^ α := by rw [Real.rpow_pow_comm (by norm_num)]
    _ ≤ D * ((4 / R₀) * r) ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hScale hα) hD
    _ = _ := by rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / R₀) hr.le]; ring

end KEBall
