import Drafts.KEBall.AuxiliaryPRegularity
import KEBall.HorizontalPower

/-!
Stage07 SOURCE_DRAFT_UNCOMPILED.
This module integrates a precisely stated boundary conormal formula using
the actual normalized Green identity and horizontal integration by parts.
Its auxiliary hypothesis must be discharged by the separate boundary-jet
calculation; this module alone is not the full logarithmic flux theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology

namespace KEBall

/-- Scalar weighting before integration. Natural exponents never replace
the reciprocal weight in complex dimension two. -/
theorem logarithmic_conormal_weight_algebra {n : ℕ} (hn : 2 ≤ n)
    (μ t d G : ℝ) (ht : t ≠ 0) :
    t ^ (n - 1) *
        (2 * n * μ / t ^ n + 2 * n * (t / (n + 1 : ℝ) - 1) +
          d / (2 * t) - G / t ^ 2) =
      -2 * n * ((boundaryPolynomial n t - μ) / t) +
        (1 / 2 : ℝ) * (t ^ (n - 2) * d) - horizontalFluxWeight n t * G := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hp : t ^ n = t ^ (n - 1) * t := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  have hp' : t ^ (n - 1) = t ^ (n - 2) * t := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
  unfold boundaryPolynomial horizontalFluxWeight
  simp only [hp, hp']
  field_simp [ht, hk]
  <;> ring

/-- The actual normalized integral identity follows from its pointwise
boundary formula. The premise is explicit and is not hidden in IsSolution. -/
theorem IsSolution.logarithmicFlux_of_conormal_formula {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    (hD : ∀ x ∈ unitSphere n,
      conormalDerivative u (auxiliaryW u) x =
        2 * n * μ / boundarySlope u x ^ n +
        2 * n * (boundarySlope u x / (n + 1 : ℝ) - 1) +
        horizontalLaplacian (boundarySlope u) x / (2 * boundarySlope u x) -
        ‖horizontalGradient (boundarySlope u) x‖ ^ 2 / boundarySlope u x ^ 2) :
    (∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
        (complexHessian u x).det.re ∂volume0 n) =
      -(n : ℝ) ^ 2 *
        ((∫ x : Sphere n,
            (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
              ∂sphere0 n) +
          1 / 4 * ∫ x : Sphere n,
            horizontalFluxWeight n (boundarySlope u x.1) *
              ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n) := by
  letI : NeZero n := ⟨by omega⟩
  let F : Sphere n → ℝ := fun x =>
    (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
  let H : Sphere n → ℝ := fun x => boundarySlope u x.1 ^ (n - 2) *
    horizontalLaplacian (boundarySlope u) x.1
  let G : Sphere n → ℝ := fun x => horizontalFluxWeight n (boundarySlope u x.1) *
    ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2
  have ht := hu.2.1.boundarySlope_continuous_sphere
  have htnz (x : Sphere n) : boundarySlope u x.1 ≠ 0 :=
    ne_of_gt (hu.boundarySlope_pos hn x.2)
  have hFc : Continuous F := by
    exact (((ht.pow n).mul
      (continuous_const.sub (ht.div_const (n + 1 : ℝ)))).sub continuous_const).div ht htnz
  have hHc : Continuous H := (ht.pow (n - 2)).mul
    hu.2.1.boundarySlope.horizontalLaplacian_continuous_sphere
  have hGc : Continuous G := by
    exact ((ht.pow (n - 1)).div (ht.pow 2) (fun x => pow_ne_zero 2 (htnz x))).mul
      (hu.2.1.boundarySlope.horizontalGradient_continuous_sphere.norm.pow 2)
  have hFi : Integrable F (sphere0 n) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHi : Integrable H (sphere0 n) :=
    hHc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGi : Integrable G (sphere0 n) :=
    hGc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (x : Sphere n) :
      boundarySlope u x.1 ^ (n - 1) * conormalDerivative u (auxiliaryW u) x.1 =
        -2 * n * F x + (1 / 2 : ℝ) * H x - G x := by
    rw [hD x.1 x.2]
    exact logarithmic_conormal_weight_algebra hn μ (boundarySlope u x.1)
      (horizontalLaplacian (boundarySlope u) x.1)
      (‖horizontalGradient (boundarySlope u) x.1‖ ^ 2) (htnz x)
  have hs : (∫ x : Sphere n, boundarySlope u x.1 ^ (n - 1) *
      conormalDerivative u (auxiliaryW u) x.1 ∂sphere0 n) =
      -2 * n * (∫ x, F x ∂sphere0 n) + (1 / 2 : ℝ) * (∫ x, H x ∂sphere0 n) -
        ∫ x, G x ∂sphere0 n := by
    calc
      _ = ∫ x, (-2 * n * F x + (1 / 2 : ℝ) * H x - G x) ∂sphere0 n :=
        integral_congr_ae (Eventually.of_forall hpoint)
      _ = _ := by
        have hsumI : Integrable (fun x => -2 * (n : ℝ) * F x + 1 / 2 * H x)
            (sphere0 n) := (hFi.const_mul _).add (hHi.const_mul _)
        rw [integral_sub hsumI hGi,
          integral_add (hFi.const_mul _) (hHi.const_mul _), integral_const_mul,
          integral_const_mul]
  have hH : (∫ x, H x ∂sphere0 n) = -(n - 2 : ℝ) * ∫ x, G x ∂sphere0 n :=
    hu.horizontal_power_identity hn
  rw [hu.conormalGreen hn (hu.auxiliaryW_smoothNear hn), hs, hH]
  change (n : ℝ) / 2 *
      (-2 * n * (∫ x, F x ∂sphere0 n) +
        1 / 2 * (-(n - 2 : ℝ) * ∫ x, G x ∂sphere0 n) - ∫ x, G x ∂sphere0 n) =
    -(n : ℝ) ^ 2 * ((∫ x, F x ∂sphere0 n) + 1 / 4 * ∫ x, G x ∂sphere0 n)
  ring

end KEBall
