import KEBall.DirichletDiscreteAngularPower

/-! Signed-power identities for genuine, undifferentiated orthogonal differences. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem integral_dirichlet_discrete_power_identity {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {f g : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hDf : ∀ x ∈ unitBall n, f (R x) - f x = g x)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ x in unitBall n, |g x| ^ p ∂volume0 n) =
      ∫ x in unitBall n, f x *
        (dirichletSignedPower (p - 2) (g (R.symm x)) -
          dirichletSignedPower (p - 2) (g x)) ∂volume0 n := by
  calc
    _ = ∫ x in unitBall n, (f (R x) - f x) *
        dirichletSignedPower (p - 2) (g x) ∂volume0 n := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      change |g x| ^ p = (f (R x) - f x) * dirichletSignedPower (p - 2) (g x)
      rw [hDf x hx, mul_dirichletSignedPower (show 0 ≤ p - 2 by linarith)]
      congr 1
      ring
    _ = _ := integral_dirichlet_orthogonal_difference_mul R hf
      ((contDiff_dirichletSignedPower (show 0 ≤ p - 2 by linarith)).continuous.comp_continuousOn hg)

theorem integral_dirichlet_discrete_power_le_abs {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {f g h : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n))
    (hh : ContinuousOn h (closedUnitBall n))
    (hDf : ∀ x ∈ unitBall n, f (R x) - f x = g x)
    (hDg : ∀ x ∈ unitBall n, g (R x) - g x = h x)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ x in unitBall n, |g x| ^ p ∂volume0 n) ≤
      (p - 1) * ((∫ x in unitBall n,
        |f x| * |g (R.symm x)| ^ (p - 2) * |h (R.symm x)| ∂volume0 n) +
        ∫ x in unitBall n,
          |f x| * |g x| ^ (p - 2) * |h (R.symm x)| ∂volume0 n) := by
  let μ := (volume0 n).restrict (unitBall n)
  have hr : 0 ≤ p - 2 := by linarith
  have hG := continuousOn_dirichlet_orthogonal_comp hg R.symm
  have hH := continuousOn_dirichlet_orthogonal_comp hh R.symm
  have hGP := hG.abs.rpow_const (fun _ _ => Or.inr hr)
  have hgP := hg.abs.rpow_const (fun _ _ => Or.inr hr)
  have hInt {v : E n → ℝ} (hv : ContinuousOn v (closedUnitBall n)) : Integrable v μ :=
    (hv.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
      ball_subset_closedBall
  have h₁ : Integrable (fun x => |f x| * |g (R.symm x)| ^ (p - 2) * |h (R.symm x)|) μ :=
    hInt ((hf.abs.mul hGP).mul hH.abs)
  have h₂ : Integrable (fun x => |f x| * |g x| ^ (p - 2) * |h (R.symm x)|) μ :=
    hInt ((hf.abs.mul hgP).mul hH.abs)
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      f x * (dirichletSignedPower (p - 2) (g (R.symm x)) -
        dirichletSignedPower (p - 2) (g x)) ≤
      (p - 1) * (|f x| * |g (R.symm x)| ^ (p - 2) * |h (R.symm x)| +
        |f x| * |g x| ^ (p - 2) * |h (R.symm x)|) := by
    have hxR : R.symm x ∈ unitBall n := by
      simpa only [unitBall, mem_ball_zero_iff, R.symm.norm_map] using hx
    have hDiff : |g (R.symm x) - g x| = |h (R.symm x)| := by
      rw [← hDg (R.symm x) hxR, R.apply_symm_apply, abs_sub_comm]
    have hPow := abs_dirichletSignedPower_sub_le hr (g x) (g (R.symm x))
    rw [hDiff, show p - 2 + 1 = p - 1 by ring] at hPow
    calc
      _ ≤ |f x| * |dirichletSignedPower (p - 2) (g (R.symm x)) -
          dirichletSignedPower (p - 2) (g x)| := by
        rw [← abs_mul]
        exact le_abs_self _
      _ ≤ |f x| * ((p - 1) * (|g x| ^ (p - 2) + |g (R.symm x)| ^ (p - 2)) *
          |h (R.symm x)|) := mul_le_mul_of_nonneg_left hPow (abs_nonneg _)
      _ = _ := by ring
  rw [integral_dirichlet_discrete_power_identity R hf hg hDf hp,
    ← integral_add h₁ h₂, ← integral_const_mul]
  apply integral_mono_ae
    (hInt (hf.mul (((contDiff_dirichletSignedPower hr).continuous.comp_continuousOn hG).sub
      ((contDiff_dirichletSignedPower hr).continuous.comp_continuousOn hg))))
    ((h₁.add h₂).const_mul _)
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  exact hPoint x hx

end KEBall
