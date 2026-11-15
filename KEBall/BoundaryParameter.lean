import KEBall.Pohozaev
import KEBall.ScalarBranches

/-!
# The sharp parameter bound and the critical boundary slope

These statements apply to every actual solution. The sharp scalar bound
is integrated using the proved Pohozaev identity; at equality, full
support of the genuine sphere measure gives pointwise equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators

namespace KEBall

theorem IsSolution.coefficient_le_critical {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) : μ ≤ criticalCoefficient n := by
  letI : NeZero n := ⟨by omega⟩
  have hc := (continuous_boundaryPolynomial n).comp hu.2.1.boundarySlope_continuous_sphere
  have hi : Integrable (fun x : Sphere n => boundaryPolynomial n (boundarySlope u x.1))
      (sphere0 n) := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : ∀ x : Sphere n, boundaryPolynomial n (boundarySlope u x.1) ≤ criticalCoefficient n :=
    fun x => boundaryPolynomial_le_critical_of_nonneg (by omega) (hu.boundarySlope_pos hn x.2).le
  have h := integral_mono hi (integrable_const (criticalCoefficient n)) hb
  rw [hu.pohozaev_identity hn] at h
  simpa using h

theorem IsSolution.boundarySlope_eq_dim_of_critical {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    {u : E n → ℝ} (hu : IsSolution n μ u) (hμ : μ = criticalCoefficient n)
    {x : E n} (hx : x ∈ unitSphere n) : boundarySlope u x = (n : ℝ) := by
  letI : NeZero n := ⟨by omega⟩
  let f : Sphere n → ℝ := fun y => criticalCoefficient n - boundaryPolynomial n (boundarySlope u y.1)
  have hFc := (continuous_boundaryPolynomial n).comp hu.2.1.boundarySlope_continuous_sphere
  have hfc : Continuous f := continuous_const.sub hFc
  have hFi : Integrable (fun y : Sphere n => boundaryPolynomial n (boundarySlope u y.1))
      (sphere0 n) := hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfnonneg : 0 ≤ f := by
    intro y
    exact sub_nonneg.mpr
      (boundaryPolynomial_le_critical_of_nonneg (by omega) (hu.boundarySlope_pos hn y.2).le)
  have hfint : (∫ y, f y ∂sphere0 n) = 0 := by
    rw [show f = (fun y : Sphere n => criticalCoefficient n -
      boundaryPolynomial n (boundarySlope u y.1)) from rfl,
      integral_sub (integrable_const _) hFi, hu.pohozaev_identity hn, hμ]
    simp
  have hfzero := sphere_eq_zero_of_integral_eq_zero n (by omega) f hfc hfnonneg hfint
  have hvalue : boundaryPolynomial n (boundarySlope u x) = criticalCoefficient n := by
    have h := congrFun hfzero (⟨x, hx⟩ : Sphere n)
    change criticalCoefficient n - boundaryPolynomial n (boundarySlope u x) = 0 at h
    exact (sub_eq_zero.mp h).symm
  exact (boundaryPolynomial_critical (by omega) (hu.boundarySlope_pos hn hx)).mp hvalue

theorem not_isSolution_of_supercritical {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    (hμ : criticalCoefficient n < μ) (u : E n → ℝ) : ¬ IsSolution n μ u := by
  intro hu
  exact (not_le_of_gt hμ) (hu.coefficient_le_critical hn)

theorem solutionSet_eq_empty_of_supercritical {n : ℕ} (hn : 2 ≤ n) {μ : ℝ}
    (hμ : criticalCoefficient n < μ) : solutionSet n μ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro v ⟨u, hu, _⟩
  exact not_isSolution_of_supercritical hn hμ u hu

#print axioms IsSolution.coefficient_le_critical
#print axioms IsSolution.boundarySlope_eq_dim_of_critical
#print axioms solutionSet_eq_empty_of_supercritical

end KEBall
