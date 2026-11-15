import Drafts.KEBall.BoundaryScalarComparison
import Drafts.KEBall.BoundaryLogarithm
import Drafts.KEBall.LogarithmicEquality
import KEBall.BoundaryParameter
import KEBall.LowerSlope

/-!
Stage08 SOURCE_DRAFT_UNCOMPILED.
The zero flux is proved for every original solution. No integral-vanishing
premise is added to IsSolution or to the final Hessian-rigidity theorem.
-/
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ContDiff

namespace KEBall

/-- The defect quotient is continuous for the actual strictly positive slope. -/
theorem IsSolution.boundaryFluxDefect_continuous {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    Continuous (fun x : Sphere n =>
      (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1) := by
  have ht := hu.2.1.boundarySlope_continuous_sphere
  exact (((continuous_boundaryPolynomial n).comp ht).sub continuous_const).div ht
    (fun x => ne_of_gt (hu.boundarySlope_pos hn x.2))

theorem IsSolution.boundaryFluxEnergy_continuous {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    Continuous (fun x : Sphere n =>
      horizontalFluxWeight n (boundarySlope u x.1) *
        ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2) := by
  have ht := hu.2.1.boundarySlope_continuous_sphere
  exact ((ht.pow (n - 1)).div (ht.pow 2)
    (fun x => pow_ne_zero 2 (ne_of_gt (hu.boundarySlope_pos hn x.2)))).mul
    (hu.2.1.boundarySlope.horizontalGradient_continuous_sphere.norm.pow 2)

/-- Pohozaev permits subtracting any fixed reciprocal from the weight.
All terms are integrable on the actual normalized sphere measure. -/
theorem IsSolution.boundaryFluxDefect_shift {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) (c : ℝ) :
    (∫ x : Sphere n,
      (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
        ∂sphere0 n) =
    ∫ x : Sphere n, (boundaryPolynomial n (boundarySlope u x.1) - μ) *
      (1 / boundarySlope u x.1 - 1 / c) ∂sphere0 n := by
  letI : NeZero n := ⟨by omega⟩
  let f : Sphere n → ℝ := fun x => boundaryPolynomial n (boundarySlope u x.1) - μ
  let q : Sphere n → ℝ := fun x => f x / boundarySlope u x.1
  have hfc : Continuous f :=
    ((continuous_boundaryPolynomial n).comp hu.2.1.boundarySlope_continuous_sphere).sub
      continuous_const
  have hfi : Integrable f (sphere0 n) :=
    hfc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqi : Integrable q (sphere0 n) :=
    (hu.boundaryFluxDefect_continuous hn).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF := (continuous_boundaryPolynomial n).comp hu.2.1.boundarySlope_continuous_sphere
  have hFi : Integrable
      (fun x : Sphere n => boundaryPolynomial n (boundarySlope u x.1)) (sphere0 n) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfzero : (∫ x, f x ∂sphere0 n) = 0 := by
    dsimp [f]
    rw [integral_sub hFi (integrable_const μ), hu.pohozaev_identity hn]
    simp
  calc
    _ = (∫ x, q x ∂sphere0 n) - (1 / c) * ∫ x, f x ∂sphere0 n := by
      rw [hfzero]
      simp only [mul_zero, sub_zero]
      rfl
    _ = ∫ x, q x - (1 / c) * f x ∂sphere0 n := by
      rw [integral_sub hqi (hfi.const_mul _), integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [q]
      ring

/-- The scalar sign argument is used only after the lower-root comparison
has been proved for the actual solution. -/
theorem IsSolution.boundaryFluxDefect_integral_nonneg_subcritical {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    (hμc : μ < criticalCoefficient n) :
    0 ≤ ∫ x : Sphere n,
      (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
        ∂sphere0 n := by
  obtain ⟨a, c, ha, han, hnc, hck, hFa, hFc, _⟩ :=
    boundaryPolynomial_subcritical (by omega) hu.1 hμc
  rw [hu.boundaryFluxDefect_shift hn c]
  apply integral_nonneg
  intro x
  exact boundary_weighted_defect_nonneg (by omega) hu.1 ha han hnc hck hFa hFc
    (hu.boundarySlope_ge_lower_root ha han hFa x.2)

/-- Critical and subcritical coefficients exhaust every actual solution. -/
theorem IsSolution.boundaryFluxDefect_integral_nonneg {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    0 ≤ ∫ x : Sphere n,
      (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
        ∂sphere0 n := by
  rcases lt_or_eq_of_le (hu.coefficient_le_critical hn) with hlt | heq
  · exact hu.boundaryFluxDefect_integral_nonneg_subcritical hn hlt
  · have hz (x : Sphere n) :
        (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1 = 0 := by
      rw [hu.boundarySlope_eq_dim_of_critical hn heq x.2,
        boundaryPolynomial_peak, heq, sub_self, zero_div]
    simp only [hz, integral_zero, le_refl]

/-- Both boundary terms have the opposite sign to the nonnegative interior
integral. Hence all three terms in the exact flux identity vanish. -/
theorem IsSolution.logarithmicFlux_all_integrals_zero {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    ((∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
      (complexHessian u x).det.re ∂volume0 n) = 0) ∧
    ((∫ x : Sphere n,
      (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
        ∂sphere0 n) = 0) ∧
    ((∫ x : Sphere n, horizontalFluxWeight n (boundarySlope u x.1) *
      ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n) = 0) := by
  have hA := hu.boundaryFluxDefect_integral_nonneg hn
  have hB : 0 ≤ ∫ x : Sphere n, horizontalFluxWeight n (boundarySlope u x.1) *
      ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n := by
    apply integral_nonneg
    intro x
    exact mul_nonneg
      (div_nonneg (pow_nonneg (hu.boundarySlope_pos hn x.2).le _) (sq_nonneg _))
      (sq_nonneg _)
  have hI : 0 ≤ ∫ x in unitBall n, complexLaplacian u (auxiliaryW u) x *
      (complexHessian u x).det.re ∂volume0 n := by
    apply integral_nonneg_of_ae
    apply ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
    intro x hx
    exact mul_nonneg (hu.auxiliaryW_laplacian_nonneg hn hx)
      (hu.det_re_pos_closedBall (Metric.ball_subset_closedBall hx)).le
  have hflux := hu.logarithmicFlux_identity hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnR _
  have hsum : (∫ x : Sphere n,
      (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
        ∂sphere0 n) +
      1 / 4 * (∫ x : Sphere n, horizontalFluxWeight n (boundarySlope u x.1) *
        ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n) ≤ 0 := by
    by_contra h
    have hp := mul_pos hn2 (lt_of_not_ge h)
    nlinarith only [hI, hflux, hp]
  have hAz : (∫ x : Sphere n,
      (boundaryPolynomial n (boundarySlope u x.1) - μ) / boundarySlope u x.1
        ∂sphere0 n) = 0 := by linarith
  have hBz : (∫ x : Sphere n, horizontalFluxWeight n (boundarySlope u x.1) *
      ‖horizontalGradient (boundarySlope u) x.1‖ ^ 2 ∂sphere0 n) = 0 := by linarith
  refine ⟨?_, hAz, hBz⟩
  rw [hflux, hAz, hBz]
  ring

/-- The earlier equality consequence now has no additional zero-integral
premise: it holds for every original solution. -/
theorem IsSolution.covariantHessian20_eq_rank_one {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) {x : E n}
    (hx : x ∈ unitBall n) (i j : Fin n) :
    covariantHessian20 u x i j = (n + 1 : ℂ)⁻¹ *
      partialZ i (fun y => (u y : ℂ)) x * partialZ j (fun y => (u y : ℂ)) x :=
  hu.logarithmicFlux_equality_consequence hn
    (hu.logarithmicFlux_all_integrals_zero hn).1 x hx i j

#print axioms IsSolution.logarithmicFlux_all_integrals_zero
#print axioms IsSolution.covariantHessian20_eq_rank_one

end KEBall
