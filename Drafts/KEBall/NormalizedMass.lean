import Drafts.KEBall.NormalizedBridge

/-!
Stage17 SOURCE_DRAFT_UNCOMPILED.
The normalization constant is derived from the original solution's mass
and boundary polynomial, not inserted as an additional hypothesis. These
remain statements about the frozen determinant equation and volume0.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff

namespace KEBall

theorem IsNormalizedSolution.boundaryPolynomial_parameter {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    γ < (n + 1 : ℝ) ∧
      boundaryPolynomial n γ = γ ^ n / normalizingIntegral γ φ := by
  let u : E n → ℝ := fun x => γ * φ x
  have hu : IsSolution n (γ ^ n / normalizingIntegral γ φ) u := hφ.rescale
  obtain ⟨t₀, ht, htk, hF, hSlope, _⟩ :=
    hu.exists_exponentialGradient_closedBall_data hn
  have hmass := hu.exponential_mass_of_constant_slope hn hSlope
  have hI : (∫ x in unitBall n, Real.exp (-u x) ∂volume0 n) =
      normalizingIntegral γ φ := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x _
    congr 1
    dsimp [u]
    ring
  rw [hI, div_mul_cancel₀ _ (ne_of_gt hφ.normalizingIntegral_pos)] at hmass
  have htg : t₀ = γ :=
    (pow_left_inj₀ ht.le hφ.1.le (by omega : n ≠ 0)).mp hmass.symm
  subst t₀
  exact ⟨htk, hF⟩

/-- The actual integral, including its exact coefficient. -/
theorem IsNormalizedSolution.normalizingIntegral_eq {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    normalizingIntegral γ φ = (1 - γ / (n + 1 : ℝ))⁻¹ := by
  obtain ⟨_, hF⟩ := hφ.boundaryPolynomial_parameter hn
  have hpow : γ ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hφ.1)
  have hcoef : 1 - γ / (n + 1 : ℝ) = (normalizingIntegral γ φ)⁻¹ := by
    apply mul_left_cancel₀ hpow
    simpa only [boundaryPolynomial, div_eq_mul_inv] using hF
  calc
    normalizingIntegral γ φ = ((normalizingIntegral γ φ)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (1 - γ / (n + 1 : ℝ))⁻¹ := by rw [← hcoef]

theorem IsNormalizedSolution.det_eq_explicit_coefficient {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ)
    {x : E n} (hx : x ∈ unitBall n) :
    (complexHessian φ x).det =
      (((1 - γ / (n + 1 : ℝ)) * Real.exp (-γ * φ x) : ℝ) : ℂ) := by
  rw [hφ.det_eq_real_density hx]
  rw [hφ.normalizingIntegral_eq hn, div_eq_mul_inv, inv_inv, mul_comm]

theorem normalizedPotential_normalizingIntegral {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) (hγκ : γ < (n + 1 : ℝ)) :
    normalizingIntegral γ (normalizedPotential n γ) =
      (1 - γ / (n + 1 : ℝ))⁻¹ :=
  (normalizedPotential_isNormalizedSolution hn hγ hγκ).normalizingIntegral_eq hn

theorem normalizedPotential_det {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) (hγκ : γ < (n + 1 : ℝ))
    {x : E n} (hx : x ∈ unitBall n) :
    (complexHessian (normalizedPotential n γ) x).det =
      (((1 - γ / (n + 1 : ℝ)) *
        Real.exp (-γ * normalizedPotential n γ x) : ℝ) : ℂ) :=
  (normalizedPotential_isNormalizedSolution hn hγ hγκ).det_eq_explicit_coefficient hn hx

#print axioms IsNormalizedSolution.normalizingIntegral_eq
#print axioms normalizedPotential_det

end KEBall
