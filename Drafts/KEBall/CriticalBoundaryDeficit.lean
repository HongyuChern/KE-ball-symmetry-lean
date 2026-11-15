import Drafts.KEBall.PeakDeficitAlgebra
import KEBall.BoundaryParameter

/-!
Stage20 SOURCE_DRAFT_UNCOMPILED.
The original Pohozaev identity gives a quantitative critical boundary
estimate. No classification, upper slope bound, integral hypothesis or
new boundary regularity is assumed.
-/
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff BigOperators

namespace KEBall

/-- The squared distance of the actual boundary slope from the critical value. -/
theorem IsSolution.boundarySlope_square_integral_bound {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    (n : ℝ) ^ (n - 2) *
        (∫ x : Sphere n, (boundarySlope u x.1 - (n : ℝ)) ^ 2 ∂sphere0 n) ≤
      (n + 1 : ℝ) * (criticalCoefficient n - μ) := by
  letI : NeZero n := ⟨by omega⟩
  have ht := hu.2.1.boundarySlope_continuous_sphere
  have hqc : Continuous (fun x : Sphere n =>
      (boundarySlope u x.1 - (n : ℝ)) ^ 2) :=
    (ht.sub continuous_const).pow 2
  have hqi : Integrable (fun x : Sphere n =>
      (boundarySlope u x.1 - (n : ℝ)) ^ 2) (sphere0 n) :=
    hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFc := (continuous_boundaryPolynomial n).comp ht
  have hFi : Integrable (fun x : Sphere n =>
      boundaryPolynomial n (boundarySlope u x.1)) (sphere0 n) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDi : Integrable (fun x : Sphere n =>
      criticalCoefficient n - boundaryPolynomial n (boundarySlope u x.1)) (sphere0 n) :=
    (continuous_const.sub hFc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono (hqi.const_mul ((n : ℝ) ^ (n - 2)))
    (hDi.const_mul (n + 1 : ℝ))
    (fun x : Sphere n => boundaryPolynomial_quadratic_deficit hn
      (hu.boundarySlope_pos hn x.2).le)
  rw [integral_const_mul, integral_const_mul,
    integral_sub (integrable_const _) hFi, hu.pohozaev_identity hn] at h
  simpa using h

/-- At the critical coefficient the nonnegative square integral vanishes. -/
theorem IsSolution.boundarySlope_square_integral_zero_of_critical {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) (hμ : μ = criticalCoefficient n) :
    (∫ x : Sphere n, (boundarySlope u x.1 - (n : ℝ)) ^ 2 ∂sphere0 n) = 0 := by
  have hbound := hu.boundarySlope_square_integral_bound hn
  rw [hμ, sub_self, mul_zero] at hbound
  have hnonneg : 0 ≤ ∫ x : Sphere n,
      (boundarySlope u x.1 - (n : ℝ)) ^ 2 ∂sphere0 n :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcoef : 0 < (n : ℝ) ^ (n - 2) := pow_pos hnR _
  nlinarith

/-- A direct critical rigidity proof without selecting a scalar root. -/
theorem IsSolution.boundarySlope_eq_dim_via_square_deficit {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) (hμ : μ = criticalCoefficient n)
    {x : E n} (hx : x ∈ unitSphere n) : boundarySlope u x = (n : ℝ) := by
  let f : Sphere n → ℝ := fun y => (boundarySlope u y.1 - (n : ℝ)) ^ 2
  have hc : Continuous f := (hu.2.1.boundarySlope_continuous_sphere.sub continuous_const).pow 2
  have hpos : 0 ≤ f := fun _ => sq_nonneg _
  have hzero := sphere_eq_zero_of_integral_eq_zero n (by omega) f hc hpos
    (hu.boundarySlope_square_integral_zero_of_critical hn hμ)
  have hpoint := congrFun hzero (⟨x, hx⟩ : Sphere n)
  change (boundarySlope u x - (n : ℝ)) ^ 2 = 0 at hpoint
  nlinarith

/-- Supplementary diagnostic statement; the original seven specifications stay fixed. -/
def CriticalBoundaryDeficitStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (μ : ℝ) (u : E n → ℝ), IsSolution n μ u →
    (n : ℝ) ^ (n - 2) *
        (∫ x : Sphere n, (boundarySlope u x.1 - (n : ℝ)) ^ 2 ∂sphere0 n) ≤
      (n + 1 : ℝ) * (criticalCoefficient n - μ)

theorem criticalBoundaryDeficit : CriticalBoundaryDeficitStatement := by
  intro n hn μ u hu
  exact hu.boundarySlope_square_integral_bound hn

end KEBall
