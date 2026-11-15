import KEBall.DirichletDiscreteDifferences

/-!
# The step-uniform quartic estimate and its absorption consequence

The estimate applies to continuous scalar Hessian components. A small
uniform bound for such a component gives a small coefficient in front of
the second normalized difference. No derivative is assumed to exist.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem dirichletLpSize_rpow {n : ℕ} (f : E n → ℝ) {p : ℝ} (hp : 0 < p) :
    dirichletLpSize f p ^ p = ∫ x in unitBall n, |f x| ^ p ∂volume0 n := by
  unfold dirichletLpSize
  rw [← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _),
    one_div_mul_cancel hp.ne', Real.rpow_one]

theorem dirichletLpSize_two_sq {n : ℕ} (f : E n → ℝ) :
    dirichletLpSize f 2 ^ 2 = ∫ x in unitBall n, (f x) ^ 2 ∂volume0 n := by
  have h := dirichletLpSize_rpow f (p := 2) (by norm_num)
  simpa only [Real.rpow_two, sq_abs] using h

theorem dirichletLpSize_four_pow {n : ℕ} (f : E n → ℝ) :
    dirichletLpSize f 4 ^ 4 = ∫ x in unitBall n, (f x) ^ 4 ∂volume0 n := by
  have h := dirichletLpSize_rpow f (p := 4) (by norm_num)
  have h4 (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := Real.rpow_natCast x 4
  simp only [h4] at h
  have he (x : ℝ) : |x| ^ 4 = x ^ 4 := by
    calc
      |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := by rw [sq_abs]
      _ = x ^ 4 := by ring
  simpa only [he] using h

theorem integral_pow_four_le_of_dirichlet_discrete_normalized_chain {n : ℕ}
    (hn : 0 < n) (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {f g h : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hh : ContinuousOn h (closedUnitBall n))
    (hDf : ∀ x ∈ unitBall n, f (R x) - f x = τ * g x)
    (hDg : ∀ x ∈ unitBall n, g (R x) - g x = τ * h x)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x ∈ unitBall n, |f x| ≤ B) :
    (∫ x in unitBall n, (g x) ^ 4 ∂volume0 n) ≤
      36 * B ^ 2 * ∫ x in unitBall n, (h x) ^ 2 ∂volume0 n := by
  have h := dirichlet_discrete_normalized_lp_logconvex_sup hn R hτ hf hg hh hDf hDg
    (p := 4) (by norm_num) hB hF
  norm_num only at h
  have hSq := pow_le_pow_left₀ (sq_nonneg (dirichletLpSize g 4)) h 2
  rw [← pow_mul, show 2 * 2 = 4 by norm_num, dirichletLpSize_four_pow,
    mul_pow, mul_pow, dirichletLpSize_two_sq] at hSq
  norm_num at hSq ⊢
  exact hSq

theorem integral_dirichletOrthogonalDifference_pow_four_le {n : ℕ}
    (hn : 0 < n) (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x ∈ unitBall n, |f x| ≤ B) :
    (∫ x in unitBall n, (dirichletOrthogonalDifference R τ f x) ^ 4 ∂volume0 n) ≤
      36 * B ^ 2 * ∫ x in unitBall n,
        (dirichletOrthogonalDifference R τ (dirichletOrthogonalDifference R τ f) x) ^ 2
          ∂volume0 n := by
  apply integral_pow_four_le_of_dirichlet_discrete_normalized_chain hn R hτ hf
    (continuousOn_dirichletOrthogonalDifference R τ hf)
    (continuousOn_dirichletOrthogonalDifference R τ
      (continuousOn_dirichletOrthogonalDifference R τ hf))
  · intro x _
    exact dirichletIteratedOrthogonalDifference_chain R hτ f 0 x
  · intro x _
    exact dirichletIteratedOrthogonalDifference_chain R hτ f 1 x
  · exact hB
  · exact hF

/-- Absorption uses an explicit strict margin. This conclusion still
requires the displayed second-difference estimate; it is not asserted as
an unconditional elliptic regularity theorem. -/
theorem dirichlet_discrete_quartic_absorption {n : ℕ}
    (hn : 0 < n) (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n))
    {B A C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hF : ∀ x ∈ unitBall n, |f x| ≤ B)
    (hSmall : 36 * C * B ^ 2 ≤ (1 / 2 : ℝ))
    (hEstimate :
      (∫ x in unitBall n,
        (dirichletOrthogonalDifference R τ (dirichletOrthogonalDifference R τ f) x) ^ 2
          ∂volume0 n) ≤
        A + C * ∫ x in unitBall n, (dirichletOrthogonalDifference R τ f x) ^ 4 ∂volume0 n) :
    (∫ x in unitBall n,
      (dirichletOrthogonalDifference R τ (dirichletOrthogonalDifference R τ f) x) ^ 2
        ∂volume0 n) ≤ 2 * A := by
  have hQ := integral_dirichletOrthogonalDifference_pow_four_le hn R hτ hf hB hF
  have hH : 0 ≤ ∫ x in unitBall n,
      (dirichletOrthogonalDifference R τ (dirichletOrthogonalDifference R τ f) x) ^ 2
        ∂volume0 n := integral_nonneg fun _ => sq_nonneg _
  have hScaled := mul_le_mul_of_nonneg_left hQ hC
  have hMargin := mul_le_mul_of_nonneg_right hSmall hH
  nlinarith only [hEstimate, hScaled, hMargin]

end KEBall
