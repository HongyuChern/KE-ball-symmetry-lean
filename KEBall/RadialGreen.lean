import KEBall.SphereMeasure
import PoincareLib.Geometry.Riemannian.Measure.CoordinateGreen
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Radial cutoff Green identity from the actual Euclidean divergence

This module consumes the fixed PoincareLib compact-support coordinate Green
theorem on actual functions. It then performs actual polar change of variables.
The cutoff identity is a prerequisite for a boundary limit, not a claim that
the nonzero ball boundary flux theorem has already been proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff BigOperators RealInnerProductSpace

namespace KEBall

/-- A cutoff that vanishes beyond a fixed squared radius has genuinely compact
support after composition with the squared Euclidean norm. -/
theorem hasCompactSupport_radialCutoff {n : ℕ} {χ : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hχzero : ∀ s : ℝ, R ^ 2 ≤ s → χ s = 0) :
    HasCompactSupport (fun x : E n => χ (‖x‖ ^ 2)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E n) R)
  intro x hx
  by_contra hnot
  have hnorm : R < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hnot
  exact hx (hχzero (‖x‖ ^ 2) (by nlinarith [norm_nonneg x]))

/-- Euclidean divergence of an actual vector field in the fixed real basis. -/
noncomputable def euclideanDivergence {n : ℕ} (V : E n → E n) (x : E n) : ℝ :=
  ∑ i : Fin (2 * n), fderiv ℝ (fun y => V y i) x
    (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)

theorem fderiv_radialCutoff {n : ℕ} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (x : E n) (i : Fin (2 * n)) :
    fderiv ℝ (fun y : E n => χ (‖y‖ ^ 2)) x
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) =
      2 * deriv χ (‖x‖ ^ 2) * x i := by
  have h := ((hχ.differentiable one_ne_zero (‖x‖ ^ 2)).hasDerivAt).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change fderiv ℝ (χ ∘ fun y : E n => ‖y‖ ^ 2) x _ = _
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    EuclideanSpace.inner_basisFun_real]
  ring

/-- A radial compactly supported test produces the actual weak divergence
identity. The vector field only needs `C¹` regularity on the test support. -/
theorem integral_radialCutoff_divergence {n : ℕ} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport (fun x : E n => χ (‖x‖ ^ 2)))
    (V : E n → E n)
    (hV : ∀ x ∈ tsupport (fun y : E n => χ (‖y‖ ^ 2)), ContDiffAt ℝ 1 V x) :
    (∫ x, χ (‖x‖ ^ 2) * euclideanDivergence V x) =
      -2 * ∫ x, deriv χ (‖x‖ ^ 2) * inner ℝ x (V x) := by
  have hu : ContDiff ℝ 1 (fun x : E n => χ (‖x‖ ^ 2)) :=
    hχ.comp (contDiff_norm_sq ℝ)
  have hVi (i : Fin (2 * n)) (x : E n)
      (hx : x ∈ tsupport (fun y : E n => χ (‖y‖ ^ 2))) :
      ContDiffAt ℝ 1 (fun y => V y i) x := by
    have hp : ContDiff ℝ 1 (fun z : E n => z i) :=
      (EuclideanSpace.proj i : E n →L[ℝ] ℝ).contDiff
    exact hp.contDiffAt.comp x (hV x hx)
  have h := Poincare.integral_mul_coordinate_divergence hu hc hVi
  have hp (x : E n) :
      (∑ i : Fin (2 * n), fderiv ℝ (fun y : E n => χ (‖y‖ ^ 2)) x
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) * V x i) =
      2 * (deriv χ (‖x‖ ^ 2) * inner ℝ x (V x)) := by
    simp only [fderiv_radialCutoff hχ, PiLp.inner_apply, RCLike.inner_apply,
      starRingEnd_apply, star_trivial]
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hp] at h
  rw [integral_const_mul] at h
  simpa only [euclideanDivergence, neg_mul] using h

/-- The same genuine Green identity expressed with the actual polar surface
measure. Passing to a sharp unit-ball cutoff is a further obligation. -/
theorem integral_radialCutoff_divergence_polar {n : ℕ} (hn : 0 < n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport (fun x : E n => χ (‖x‖ ^ 2)))
    (V : E n → E n)
    (hV : ∀ x ∈ tsupport (fun y : E n => χ (‖y‖ ^ 2)), ContDiffAt ℝ 1 V x) :
    (∫ x, χ (‖x‖ ^ 2) * euclideanDivergence V x) =
      -2 * ∫ p : Sphere n × Ioi (0 : ℝ),
        deriv χ (p.2.1 ^ 2) * p.2.1 * inner ℝ p.1.1 (V (p.2.1 • p.1.1))
        ∂((sphereMeasure n).prod (Measure.volumeIoiPow (2 * n - 1))) := by
  rw [integral_radialCutoff_divergence hχ hc V hV,
    integral_polar n hn]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  have hnorm : ‖p.1.1‖ = 1 := by
    simpa only [unitSphere, Metric.mem_sphere, dist_zero_right] using p.1.2
  simp only [norm_smul, Real.norm_eq_abs, hnorm, mul_one, sq_abs,
    real_inner_smul_left, mul_assoc]

#print axioms fderiv_radialCutoff
#print axioms hasCompactSupport_radialCutoff
#print axioms integral_radialCutoff_divergence
#print axioms integral_radialCutoff_divergence_polar

end KEBall
