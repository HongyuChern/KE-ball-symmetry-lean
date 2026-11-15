import KEBall.PaperSpecification20261016
import Drafts.KEBall.NormalizedEndpoints
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bridges to the 2026-10-16 paper

All additional inputs below are discharged from the original solution
predicate.  In particular the constant boundary slope is derived from the
existing rigidity theorem before it is used to evaluate the actual mass.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff ENNReal ComplexOrder

namespace KEBall.Paper20261016

theorem normalized_equation_iff_full_top_form {n : ℕ} (γ : ℝ) (φ : E n → ℝ) :
    (∀ x ∈ unitBall n, (complexHessian φ x).det =
      ((Real.exp (-γ * φ x) / normalizingIntegral γ φ : ℝ) : ℂ)) ↔
    (∀ x ∈ unitBall n, d0Exterior φ x ^ n =
      ((Real.exp (-γ * φ x) / normalizingIntegral γ φ : ℝ) : ℂ) •
        normalizedExteriorVolume n) := by
  have hcR : 0 < (n.factorial : ℝ) / Real.pi ^ n := by positivity
  have hc : (((n.factorial : ℝ) / Real.pi ^ n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcR)
  constructor
  · intro h x hx
    rw [d0Exterior_top, h x hx]
  · intro h x hx
    have he := congrArg (exteriorEvaluation (euclideanFrame n)) (h x hx)
    rw [exteriorEvaluation_d0_top, map_smul,
      exteriorEvaluation_normalized_volume, smul_eq_mul] at he
    exact mul_right_cancel₀ hc he

theorem meanField_iff_normalized (n : ℕ) (γ : ℝ) (φ : E n → ℝ) :
    IsMeanFieldSolution n γ φ ↔ IsNormalizedSolution n γ φ := by
  rw [isNormalizedSolution_iff_real_density]
  unfold IsMeanFieldSolution
  rw [normalized_equation_iff_full_top_form]

theorem meanFieldSolutionSet_eq (n : ℕ) (γ : ℝ) :
    meanFieldSolutionSet n γ = normalizedSolutionSet n γ := by
  ext v
  simp only [meanFieldSolutionSet, normalizedSolutionSet, Set.mem_setOf_eq,
    meanField_iff_normalized]

theorem meanFieldClassification : MeanFieldClassificationStatement := by
  intro n hn γ hγ
  obtain ⟨hsub, hsuper⟩ := KEBall.Stage09.normalizedClassification n hn γ hγ
  constructor
  · intro hγκ
    obtain ⟨hex, hset⟩ := hsub hγκ
    exact ⟨(meanField_iff_normalized n γ _).2 hex,
      (meanFieldSolutionSet_eq n γ).trans hset⟩
  · intro hγκ
    exact (meanFieldSolutionSet_eq n γ).trans (hsuper hγκ)

theorem radialSymmetry : RadialSymmetryStatement := by
  intro n hn μ u hu
  obtain ⟨b, _, heq, _⟩ := hu.radial_classification hn
  intro x hx y hy hnorm
  rw [heq hx, heq hy]
  simp only [radialPotential, hnorm]

theorem radial_const_mul_iff {n : ℕ} {c : ℝ} (hc : c ≠ 0) (u : E n → ℝ) :
    IsRadialOnClosedBall (fun x => c * u x) ↔ IsRadialOnClosedBall u := by
  constructor
  · intro h x hx y hy he
    exact mul_left_cancel₀ hc (h x hx y hy he)
  · intro h x hx y hy he
    exact congrArg (fun r : ℝ => c * r) (h x hx y hy he)

/-- The slope hypothesis here is an internal computation input, discharged
by rigidity at the public normalization endpoint. -/
theorem actual_mass_of_constant_slope {n : ℕ} (hn : 2 ≤ n)
    {μ t : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) (ht : 0 < t)
    (hSlope : ∀ x ∈ unitSphere n, boundarySlope u x = t) :
    (d0TopMeasure u) (unitBall n) = ENNReal.ofReal (t ^ n) ∧
      mongeAmpereMass n u = t ^ n := by
  letI : NeZero n := ⟨by omega⟩
  have hi : (∫ x in unitBall n, (complexHessian u x).det.re ∂volume0 n) =
      t ^ n := by
    rw [hu.mass_identity hn]
    simp_rw [hSlope _ (Subtype.property _)]
    simp
  have hint : IntegrableOn (fun x => (complexHessian u x).det.re)
      (unitBall n) (volume0 n) := by
    apply Integrable.of_integral_ne_zero
    rw [hi]
    exact ne_of_gt (pow_pos ht n)
  have hnonneg : ∀ᵐ x ∂((volume0 n).restrict (unitBall n)),
      0 ≤ (complexHessian u x).det.re := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (posDef_det_re_pos (hu.2.2.1 x hx)).le
  have hm : (d0TopMeasure u) (unitBall n) = ENNReal.ofReal (t ^ n) := by
    rw [d0TopMeasure_eq_density,
      withDensity_apply _ (show MeasurableSet (unitBall n) from Metric.isOpen_ball.measurableSet),
      ← ofReal_integral_eq_lintegral_ofReal hint hnonneg, hi]
  refine ⟨hm, ?_⟩
  rw [mongeAmpereMass, hm, ENNReal.toReal_ofReal (pow_pos ht n).le]

theorem positive_nth_root_nat_power {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) : (t ^ n : ℝ) ^ (1 / (n : ℝ)) = t := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rw [mul_one_div_cancel hnR, Real.rpow_one]

theorem mass_coupling_eq_slope {n : ℕ} (hn : 2 ≤ n)
    {μ t : ℝ} {u : E n → ℝ} (hu : IsSolution n μ u) (ht : 0 < t)
    (hSlope : ∀ x ∈ unitSphere n, boundarySlope u x = t) :
    massCoupling n u = t := by
  rw [massCoupling, (actual_mass_of_constant_slope hn hu ht hSlope).2]
  exact positive_nth_root_nat_power (by omega) ht

theorem normalized_actual_mass {n : ℕ} {γ : ℝ} {φ : E n → ℝ}
    (hφ : IsNormalizedSolution n γ φ) : mongeAmpereMass n φ = 1 := by
  have hm := hφ.d0TopMeasure_total_mass
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hm
  rw [mongeAmpereMass, hm, ENNReal.toReal_one]

theorem rescaled_actual_mass {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} {φ : E n → ℝ}
    (hφ : IsNormalizedSolution n γ φ) :
    mongeAmpereMass n (fun x => γ * φ x) = γ ^ n := by
  have hu := hφ.rescale
  obtain ⟨t, ht, _, _, hSlope, _⟩ := hu.exists_exponentialGradient_closedBall_data hn
  have hm := hu.exponential_mass_of_constant_slope hn hSlope
  have hI : (∫ x in unitBall n, Real.exp (-(γ * φ x)) ∂volume0 n) =
      normalizingIntegral γ φ := by
    unfold normalizingIntegral
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x _
    congr 1
    ring
  rw [hI, div_mul_cancel₀ _ (ne_of_gt hφ.normalizingIntegral_pos)] at hm
  exact (actual_mass_of_constant_slope hn hu ht hSlope).2.trans hm.symm

theorem normalizationCorrespondence : NormalizationCorrespondenceStatement := by
  constructor
  · intro n hn γ φ hφ
    have h := (meanField_iff_normalized n γ φ).1 hφ
    exact ⟨h.rescale, normalized_actual_mass h, rescaled_actual_mass hn h,
      radial_const_mul_iff (ne_of_gt h.1) φ⟩
  · intro n hn μ u hu
    obtain ⟨t, ht, htk, _, hSlope, _⟩ := hu.exists_exponentialGradient_closedBall_data hn
    have hc := mass_coupling_eq_slope hn hu ht hSlope
    have hfun : (fun x => u x / t) = (fun x => t⁻¹ * u x) := by
      funext x
      ring
    rw [hc, hfun]
    exact ⟨ht, htk,
      (meanField_iff_normalized n t _).2 (hu.normalized_rescale_of_slope hn ht hSlope),
      radial_const_mul_iff (inv_ne_zero (ne_of_gt ht)) u⟩

end KEBall.Paper20261016
