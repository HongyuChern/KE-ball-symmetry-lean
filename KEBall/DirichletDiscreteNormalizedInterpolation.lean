import KEBall.DirichletDiscreteInterpolationStep

/-! Step-size independent interpolation for genuine normalized differences. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem dirichlet_discrete_normalized_lp_logconvex {n : ℕ} (hn : 0 < n)
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0) {f g h : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hh : ContinuousOn h (closedUnitBall n))
    (hDf : ∀ x ∈ unitBall n, f (R x) - f x = τ * g x)
    (hDg : ∀ x ∈ unitBall n, g (R x) - g x = τ * h x)
    {p a c : ℝ} (hp : 2 < p) (ha : 0 < a) (hc : 0 < c)
    (hBalance : a⁻¹ + c⁻¹ = 2 / p) :
    dirichletLpSize g p ^ 2 ≤ 2 * (p - 1) * dirichletLpSize f a * dirichletLpSize h c := by
  have hDiff : ∀ x ∈ unitBall n, τ⁻¹ * f (R x) - τ⁻¹ * f x = g x := by
    intro x hx
    rw [← mul_sub, hDf x hx, ← mul_assoc, inv_mul_cancel₀ hτ, one_mul]
  have H := dirichlet_discrete_lp_logconvex hn R (hf.const_mul τ⁻¹) hg
    (hh.const_mul τ) hDiff hDg hp ha hc hBalance
  rw [dirichletLpSize_const_mul _ _ ha, dirichletLpSize_const_mul _ _ hc,
    abs_inv] at H
  have hCancel : 2 * (p - 1) * (|τ|⁻¹ * dirichletLpSize f a) *
      (|τ| * dirichletLpSize h c) =
      2 * (p - 1) * dirichletLpSize f a * dirichletLpSize h c := by
    field_simp [abs_ne_zero.mpr hτ] <;> ring
  exact H.trans_eq hCancel

theorem dirichlet_discrete_normalized_lp_logconvex_sup {n : ℕ} (hn : 0 < n)
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0) {f g h : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hh : ContinuousOn h (closedUnitBall n))
    (hDf : ∀ x ∈ unitBall n, f (R x) - f x = τ * g x)
    (hDg : ∀ x ∈ unitBall n, g (R x) - g x = τ * h x)
    {p B : ℝ} (hp : 2 < p) (hB : 0 ≤ B)
    (hF : ∀ x ∈ unitBall n, |f x| ≤ B) :
    dirichletLpSize g p ^ 2 ≤ 2 * (p - 1) * B * dirichletLpSize h (p / 2) := by
  have hDiff : ∀ x ∈ unitBall n, τ⁻¹ * f (R x) - τ⁻¹ * f x = g x := by
    intro x hx
    rw [← mul_sub, hDf x hx, ← mul_assoc, inv_mul_cancel₀ hτ, one_mul]
  have hBound : ∀ x ∈ unitBall n, |τ⁻¹ * f x| ≤ |τ|⁻¹ * B := by
    intro x hx
    rw [abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left (hF x hx) (inv_nonneg.mpr (abs_nonneg τ))
  have H := dirichlet_discrete_lp_logconvex_sup hn R (hf.const_mul τ⁻¹) hg
    (hh.const_mul τ) hDiff hDg hp (mul_nonneg (inv_nonneg.mpr (abs_nonneg τ)) hB) hBound
  rw [dirichletLpSize_const_mul _ _ (show 0 < p / 2 by linarith)] at H
  have hCancel : 2 * (p - 1) * (|τ|⁻¹ * B) * (|τ| * dirichletLpSize h (p / 2)) =
      2 * (p - 1) * B * dirichletLpSize h (p / 2) := by
    field_simp [abs_ne_zero.mpr hτ] <;> ring
  exact H.trans_eq hCancel

end KEBall
