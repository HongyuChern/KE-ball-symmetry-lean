import Drafts.KEBall.BoundaryQNormal
import Drafts.KEBall.ConormalCalculus
import Drafts.KEBall.LogarithmicFluxAssembly

/-!
Stage07 SOURCE_DRAFT_UNCOMPILED.
The boundary normal derivative is imported as an actual-solution theorem;
the only remaining steps here are the genuine conormal chain rules and
scalar algebra. No boundary flux identity is an additional hypothesis.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace KEBall

/-- Substitution of the computed normal derivative into the actual conormal
logarithm rule. The reciprocal weight is retained in dimension two. -/
theorem normal_to_logarithmic_conormal_algebra {n : ℕ} (hn : 2 ≤ n)
    (μ t d G : ℝ) (hμ : μ ≠ 0) (ht : t ≠ 0) :
    (((2 * (n + 1 : ℝ) * t + 2 * t ^ 2 * (t - n) / (μ / t ^ (n - 1)) +
          t / (2 * (μ / t ^ (n - 1))) * d +
          (n - 1 : ℝ) / (2 * (μ / t ^ (n - 1))) * G -
          (n + 1 : ℝ) * t ^ (n - 1) * G / (2 * μ)) / (n + 1 : ℝ) -
        2 * t / (n + 1 : ℝ) * (1 + (t ^ (n + 1) / μ) / (n + 1 : ℝ))) /
      ((1 + (t ^ (n + 1) / μ) / (n + 1 : ℝ)) - 1)) =
        2 * n * μ / t ^ n + 2 * n * (t / (n + 1 : ℝ) - 1) +
          d / (2 * t) - G / t ^ 2 := by
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  have hp : t ^ n = t ^ (n - 1) * t := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  have hpp : t ^ (n + 1) = t ^ (n - 1) * t * t := by
    rw [pow_succ, hp]
  simp only [hp, hpp, add_sub_cancel_left]
  field_simp [ht, hμ, hk, pow_ne_zero (n - 1) ht]
  <;> ring

/-- The complete boundary formula for the frozen W, from the original
solution hypotheses and the ambient normal derivative of q. -/
theorem IsSolution.conormalDerivative_auxiliaryW_on_sphere {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitSphere n) :
    conormalDerivative u (auxiliaryW u) x =
      2 * n * μ / boundarySlope u x ^ n +
      2 * n * (boundarySlope u x / (n + 1 : ℝ) - 1) +
      horizontalLaplacian (boundarySlope u) x / (2 * boundarySlope u x) -
      ‖horizontalGradient (boundarySlope u) x‖ ^ 2 / boundarySlope u x ^ 2 := by
  rw [hu.conormalDerivative_auxiliaryW hn hx,
    hu.conormalDerivative_auxiliaryP_on_sphere hx,
    hu.conormalDerivative_gradientNormSq_on_sphere hn hx,
    hu.fderiv_gradientNormSq_normal hn hx,
    hu.auxiliaryP_on_sphere hx, hu.gradientNormSq_on_sphere hn hx]
  exact normal_to_logarithmic_conormal_algebra hn μ (boundarySlope u x)
    (horizontalLaplacian (boundarySlope u) x)
    (‖horizontalGradient (boundarySlope u) x‖ ^ 2)
    (ne_of_gt hu.1) (ne_of_gt (hu.boundarySlope_pos hn hx))

/-- Exact normalized logarithmic flux: all pointwise boundary premises of
the internal assembler are now discharged from IsSolution. -/
theorem IsSolution.logarithmicFlux_identity {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    (∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
        (complexHessian u x).det.re ∂volume0 n) =
      -(n : ℝ) ^ 2 *
        ((∫ x : Sphere n,
            (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
              ∂sphere0 n) +
          1 / 4 * ∫ x : Sphere n,
            horizontalFluxWeight n (boundarySlope u x.1) *
              ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n) :=
  hu.logarithmicFlux_of_conormal_formula hn
    (fun _ hx => hu.conormalDerivative_auxiliaryW_on_sphere hn hx)

#print axioms IsSolution.conormalDerivative_auxiliaryW_on_sphere
#print axioms IsSolution.logarithmicFlux_identity

end KEBall
