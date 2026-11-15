import Drafts.KEBall.BoundaryFluxZero
import Mathlib.Analysis.Normed.Module.Connected

/-!
Stage08 SOURCE_DRAFT_UNCOMPILED.
Continuous full-support equality gives the scalar root equation on the
whole sphere. Connectedness, not an unstated root selection, gives a single
constant slope. All critical and subcritical cases are included.
-/
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff BigOperators

namespace KEBall

/-- Equality in the integrated scalar comparison holds at each sphere point. -/
theorem IsSolution.boundaryPolynomial_slope_eq_subcritical {n : ℕ}
    (hn : 2 ≤ n) {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    (hμc : μ < criticalCoefficient n) {x : E n} (hx : x ∈ unitSphere n) :
    boundaryPolynomial n (boundarySlope u x) = μ := by
  obtain ⟨a, c, ha, han, hnc, hck, hFa, hFc, _⟩ :=
    boundaryPolynomial_subcritical (by omega) hu.1 hμc
  let f : Sphere n → ℝ := fun y => (boundaryPolynomial n (boundarySlope u y.1) - μ) *
    (1 / boundarySlope u y.1 - 1 / c)
  have ht := hu.2.1.boundarySlope_continuous_sphere
  have hfc : Continuous f :=
    (((continuous_boundaryPolynomial n).comp ht).sub continuous_const).mul
      ((continuous_const.div ht (fun y => ne_of_gt (hu.boundarySlope_pos hn y.2))).sub
        continuous_const)
  have hfpos : 0 ≤ f := by
    intro y
    exact boundary_weighted_defect_nonneg (by omega) hu.1 ha han hnc hck hFa hFc
      (hu.boundarySlope_ge_lower_root ha han hFa y.2)
  have hfint : (∫ y, f y ∂sphere0 n) = 0 := by
    rw [← hu.boundaryFluxDefect_shift hn c]
    exact (hu.logarithmicFlux_all_integrals_zero hn).2.1
  have hfzero := sphere_eq_zero_of_integral_eq_zero n (by omega) f hfc hfpos hfint
  have hpoint := congrFun hfzero (⟨x, hx⟩ : Sphere n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact boundaryPolynomial_eq_of_weighted_defect_zero (hu.boundarySlope_pos hn hx)
    (hnR.trans hnc) hFc hpoint

/-- Every actual slope is a positive root of the same scalar equation. -/
theorem IsSolution.boundaryPolynomial_slope_eq {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitSphere n) :
    boundaryPolynomial n (boundarySlope u x) = μ := by
  rcases lt_or_eq_of_le (hu.coefficient_le_critical hn) with hlt | heq
  · exact hu.boundaryPolynomial_slope_eq_subcritical hn hlt hx
  · rw [hu.boundarySlope_eq_dim_of_critical hn heq hx, boundaryPolynomial_peak, heq]

/-- Intermediate value excludes switching between two distinct real values
on a preconnected set. The midpoint is explicitly incompatible with both. -/
theorem eqOn_const_of_two_values {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) {f : X → ℝ} (hf : ContinuousOn f s)
    {a c : ℝ} (hac : a < c) (hvalues : ∀ x ∈ s, f x = a ∨ f x = c)
    {x₀ : X} (hx₀ : x₀ ∈ s) : ∀ x ∈ s, f x = f x₀ := by
  have hno (x y : X) (hx : x ∈ s) (hy : y ∈ s)
      (hxa : f x = a) (hyc : f y = c) : False := by
    have hm : (a + c) / 2 ∈ Icc (f x) (f y) := by
      rw [hxa, hyc]
      constructor <;> linarith
    obtain ⟨z, hz, hzm⟩ := hs.intermediate_value hx hy hf hm
    rcases hvalues z hz with hza | hzc
    · linarith
    · linarith
  intro x hx
  rcases hvalues x hx with hxa | hxc <;>
    rcases hvalues x₀ hx₀ with h0a | h0c
  · exact hxa.trans h0a.symm
  · exact (hno x x₀ hx hx₀ hxa h0c).elim
  · exact (hno x₀ x hx₀ hx h0a hxc).elim
  · exact hxc.trans h0c.symm

/-- Dimension is checked in the actual real Euclidean space of dimension 2n. -/
theorem unitSphere_isConnected {n : ℕ} (hn : 2 ≤ n) : IsConnected (unitSphere n) := by
  have hdim : 1 < Module.rank ℝ (E n) := by
    rw [← Module.finrank_eq_rank, finrank_E]
    exact_mod_cast (show 1 < 2 * n by omega)
  exact isConnected_sphere hdim (0 : E n) (by norm_num : (0 : ℝ) ≤ 1)

/-- A single positive boundary parameter describes every point of the sphere.
The exact parameter/coefficient relation is included in the conclusion. -/
theorem IsSolution.exists_constant_boundarySlope {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < (n + 1 : ℝ) ∧
      boundaryPolynomial n t₀ = μ ∧ ∀ x ∈ unitSphere n, boundarySlope u x = t₀ := by
  obtain ⟨x₀, hx₀⟩ := (unitSphere_isConnected hn).nonempty
  let t₀ := boundarySlope u x₀
  have ht₀ : 0 < t₀ := hu.boundarySlope_pos hn hx₀
  have hF₀ : boundaryPolynomial n t₀ = μ := hu.boundaryPolynomial_slope_eq hn hx₀
  have htk : t₀ < (n + 1 : ℝ) :=
    (boundaryPolynomial_pos_iff ht₀).mp (hF₀.symm ▸ hu.1)
  refine ⟨t₀, ht₀, htk, hF₀, ?_⟩
  rcases lt_or_eq_of_le (hu.coefficient_le_critical hn) with hlt | heq
  · obtain ⟨a, c, ha, han, hnc, hck, hFa, hFc, hroots⟩ :=
      boundaryPolynomial_subcritical (by omega) hu.1 hlt
    have hvalues : ∀ x ∈ unitSphere n, boundarySlope u x = a ∨ boundarySlope u x = c := by
      intro x hx
      exact (hroots _ (hu.boundarySlope_pos hn hx)).mp (hu.boundaryPolynomial_slope_eq hn hx)
    have htcont : ContinuousOn (boundarySlope u) (unitSphere n) := by
      intro x hx
      exact ((hu.2.1.boundarySlope).contDiffAt
        (Metric.sphere_subset_closedBall hx)).continuousAt.continuousWithinAt
    exact eqOn_const_of_two_values (unitSphere_isConnected hn).isPreconnected
      htcont (by linarith : a < c) hvalues hx₀
  · intro x hx
    exact (hu.boundarySlope_eq_dim_of_critical hn heq hx).trans
      (hu.boundarySlope_eq_dim_of_critical hn heq hx₀).symm

/-- Horizontal energy vanishing yields the actual horizontal gradient zero.
Its positive weight, including the reciprocal in dimension two, is retained. -/
theorem IsSolution.horizontalGradient_boundarySlope_eq_zero {n : ℕ} (hn : 2 ≤ n)
    {μ : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u)
    {x : E n} (hx : x ∈ unitSphere n) :
    horizontalGradient (boundarySlope u) x = 0 := by
  let f : Sphere n → ℝ := fun y => horizontalFluxWeight n (boundarySlope u y.1) *
    ‖horizontalGradient (boundarySlope u) y.1‖ ^ 2
  have hc : Continuous f := hu.boundaryFluxEnergy_continuous hn
  have hpos : 0 ≤ f := by
    intro y
    exact mul_nonneg
      (div_nonneg (pow_nonneg (hu.boundarySlope_pos hn y.2).le _) (sq_nonneg _))
      (sq_nonneg _)
  have hz := sphere_eq_zero_of_integral_eq_zero n (by omega) f hc hpos
    (hu.logarithmicFlux_all_integrals_zero hn).2.2
  have hpoint := congrFun hz (⟨x, hx⟩ : Sphere n)
  have hw : 0 < horizontalFluxWeight n (boundarySlope u x) :=
    div_pos (pow_pos (hu.boundarySlope_pos hn hx) _) (pow_pos (hu.boundarySlope_pos hn hx) _)
  have hnorm : ‖horizontalGradient (boundarySlope u) x‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hpoint).resolve_left (ne_of_gt hw)
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (horizontalGradient (boundarySlope u) x)])

#print axioms IsSolution.exists_constant_boundarySlope
#print axioms IsSolution.horizontalGradient_boundarySlope_eq_zero

end KEBall
