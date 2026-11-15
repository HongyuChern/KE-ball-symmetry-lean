import KEBall.DirichletSobolevRotations
import KEBall.DirichletSignedPower
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Discrete angular integration by parts

Orthogonal pullback preserves the normalized ball measure.  All identities
below require only continuity on the closed ball, not angular derivatives.
The signed-power bound will be used for difference-quotient interpolation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem continuousOn_dirichlet_orthogonal_comp {n : ℕ} {F : Type*}
    [TopologicalSpace F] {f : E n → F} (hf : ContinuousOn f (closedUnitBall n))
    (R : E n ≃ₗᵢ[ℝ] E n) :
    ContinuousOn (fun x => f (R x)) (closedUnitBall n) := by
  apply hf.comp R.continuous.continuousOn
  intro x hx
  simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hx

theorem integral_dirichlet_orthogonal_comp {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (f : E n → ℝ) :
    (∫ x in unitBall n, f (R x) ∂volume0 n) =
      ∫ x in unitBall n, f x ∂volume0 n :=
  (orthogonal_measurePreserving_dirichletBall R).integral_comp
    R.toHomeomorph.toMeasurableEquiv.measurableEmbedding f

theorem integral_dirichlet_orthogonal_comp_mul {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (f g : E n → ℝ) :
    (∫ x in unitBall n, f (R x) * g x ∂volume0 n) =
      ∫ x in unitBall n, f x * g (R.symm x) ∂volume0 n := by
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    integral_dirichlet_orthogonal_comp R (fun x => f x * g (R.symm x))

theorem integral_dirichlet_orthogonal_difference_mul {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {f g : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n))
    (hg : ContinuousOn g (closedUnitBall n)) :
    (∫ x in unitBall n, (f (R x) - f x) * g x ∂volume0 n) =
      ∫ x in unitBall n, f x * (g (R.symm x) - g x) ∂volume0 n := by
  have hInt {v : E n → ℝ} (hv : ContinuousOn v (closedUnitBall n)) :
      Integrable v ((volume0 n).restrict (unitBall n)) :=
    (hv.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
      ball_subset_closedBall
  have h₁ : Integrable (fun x => f (R x) * g x)
      ((volume0 n).restrict (unitBall n)) :=
    hInt ((continuousOn_dirichlet_orthogonal_comp hf R).mul hg)
  have h₂ : Integrable (fun x => f x * g x)
      ((volume0 n).restrict (unitBall n)) := hInt (hf.mul hg)
  have h₃ : Integrable (fun x => f x * g (R.symm x))
      ((volume0 n).restrict (unitBall n)) :=
    hInt (hf.mul (continuousOn_dirichlet_orthogonal_comp hg R.symm))
  simp_rw [sub_mul, mul_sub]
  rw [integral_sub h₁ h₂, integral_sub h₃ h₂, integral_dirichlet_orthogonal_comp_mul]

theorem abs_dirichletSignedPower_sub_le {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    |dirichletSignedPower r b - dirichletSignedPower r a| ≤
      (r + 1) * (|a| ^ r + |b| ^ r) * |b - a| := by
  let M := max |a| |b|
  have ha : a ∈ Icc (-M) M := abs_le.mp ((le_max_left _ _).trans le_rfl)
  have hb : b ∈ Icc (-M) M := abs_le.mp ((le_max_right _ _).trans le_rfl)
  have hPow : M ^ r ≤ |a| ^ r + |b| ^ r := by
    rcases le_total |a| |b| with h | h
    · rw [show M = |b| from max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
    · rw [show M = |a| from max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
  have hBound (x : ℝ) (hx : x ∈ Icc (-M) M) :
      ‖(r + 1) * |x| ^ r‖ ≤ (r + 1) * (|a| ^ r + |b| ^ r) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg (abs_nonneg _) _))]
    exact mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow (abs_nonneg x) (abs_le.mpr hx) hr).trans hPow)
      (by linarith)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (-M) M).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hasDerivAt_dirichletSignedPower hr x).hasDerivWithinAt) hBound ha hb

end KEBall
