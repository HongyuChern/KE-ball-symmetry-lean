import Drafts.KEBall.NormalizedMass
import Drafts.KEBall.ExteriorMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Stage17 SOURCE_DRAFT_UNCOMPILED.
The unchanged determinant-level normalized equation is identified with actual
top exterior evaluation and its Euclidean measure. Mass one is a consequence,
not a replacement definition or added assumption. No kernel receipt is claimed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal ContDiff ComplexOrder

namespace KEBall

/-- Pointwise equivalence before taking a positive-part measure. -/
theorem normalized_equation_iff_top_evaluation {n : ℕ} (γ : ℝ) (φ : E n → ℝ) :
    (∀ x ∈ unitBall n, (complexHessian φ x).det =
      ((Real.exp (-γ * φ x) / normalizingIntegral γ φ : ℝ) : ℂ)) ↔
    (∀ x ∈ unitBall n,
      exteriorEvaluation (euclideanFrame n) (d0Exterior φ x ^ n) =
        (((Real.exp (-γ * φ x) / normalizingIntegral γ φ) *
          ((n.factorial : ℝ) / Real.pi ^ n) : ℝ) : ℂ)) := by
  have hcR : 0 < (n.factorial : ℝ) / Real.pi ^ n := by positivity
  have hc : (((n.factorial : ℝ) / Real.pi ^ n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcR)
  constructor
  · intro h x hx
    rw [exteriorEvaluation_d0_top, h x hx, Complex.ofReal_mul]
  · intro h x hx
    have he := h x hx
    rw [exteriorEvaluation_d0_top, Complex.ofReal_mul] at he
    exact mul_right_cancel₀ hc he

/-- The original regularity, positivity and boundary conditions stay identical. -/
theorem normalizedSolution_iff_exteriorEquation (n : ℕ) (γ : ℝ) (φ : E n → ℝ) :
    IsNormalizedSolution n γ φ ↔
      0 < γ ∧ SmoothNear (closedUnitBall n) φ ∧
      (∀ x ∈ unitBall n, (complexHessian φ x).PosDef) ∧
      (∀ x ∈ unitSphere n, φ x = 0) ∧
      (∀ x ∈ unitBall n,
        exteriorEvaluation (euclideanFrame n) (d0Exterior φ x ^ n) =
          (((Real.exp (-γ * φ x) / normalizingIntegral γ φ) *
            ((n.factorial : ℝ) / Real.pi ^ n) : ℝ) : ℂ)) := by
  have hEq :
      (∀ x ∈ unitBall n, (complexHessian φ x).det =
        (Real.exp (-γ * φ x) /
          (∫ y in unitBall n, Real.exp (-γ * φ y) ∂volume0 n) : ℂ)) ↔
      (∀ x ∈ unitBall n,
        exteriorEvaluation (euclideanFrame n) (d0Exterior φ x ^ n) =
          (((Real.exp (-γ * φ x) / normalizingIntegral γ φ) *
            ((n.factorial : ℝ) / Real.pi ^ n) : ℝ) : ℂ)) := by
    simpa only [normalizingIntegral, Complex.ofReal_div, integral_complex_ofReal]
      using normalized_equation_iff_top_evaluation γ φ
  unfold IsNormalizedSolution
  rw [hEq]

/-- A nonzero totalized Bochner integral forces genuine integrability. -/
theorem IsNormalizedSolution.exponential_integrableOn {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    IntegrableOn (fun x => Real.exp (-γ * φ x)) (unitBall n) (volume0 n) := by
  apply Integrable.of_integral_ne_zero
  change normalizingIntegral γ φ ≠ 0
  exact ne_of_gt hφ.normalizingIntegral_pos

theorem IsNormalizedSolution.normalized_density_integrableOn {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    IntegrableOn (fun x => Real.exp (-γ * φ x) / normalizingIntegral γ φ)
      (unitBall n) (volume0 n) :=
  hφ.exponential_integrableOn.div_const _

theorem IsNormalizedSolution.normalized_density_integral {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    (∫ x in unitBall n, Real.exp (-γ * φ x) / normalizingIntegral γ φ
      ∂volume0 n) = 1 := by
  rw [integral_div]
  change normalizingIntegral γ φ / normalizingIntegral γ φ = 1
  exact div_self (ne_of_gt hφ.normalizingIntegral_pos)

theorem IsNormalizedSolution.d0TopMeasure_normalized {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    (d0TopMeasure φ).restrict (unitBall n) =
      ((volume0 n).restrict (unitBall n)).withDensity
        (fun x => ENNReal.ofReal
          (Real.exp (-γ * φ x) / normalizingIntegral γ φ)) := by
  have hB : MeasurableSet (unitBall n) := Metric.isOpen_ball.measurableSet
  rw [d0TopMeasure_eq_density, restrict_withDensity hB]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet)] with x hx
  rw [hφ.det_eq_real_density hx, Complex.ofReal_re]

theorem IsNormalizedSolution.d0_top_real_positive {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ)
    {x : E n} (hx : x ∈ unitBall n) :
    exteriorEvaluation (euclideanFrame n) (d0Exterior φ x ^ n) =
        (((Real.exp (-γ * φ x) / normalizingIntegral γ φ) *
          ((n.factorial : ℝ) / Real.pi ^ n) : ℝ) : ℂ) ∧
      0 < (exteriorEvaluation (euclideanFrame n) (d0Exterior φ x ^ n)).re := by
  have he := (normalized_equation_iff_top_evaluation γ φ).mp
    (fun _ hy => hφ.det_eq_real_density hy) x hx
  refine ⟨he, ?_⟩
  rw [he, Complex.ofReal_re]
  exact mul_pos (div_pos (Real.exp_pos _) hφ.normalizingIntegral_pos) (by positivity)

/-- The actual exterior measure restricted to the ball has total mass one. -/
theorem IsNormalizedSolution.d0TopMeasure_total_mass {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    ((d0TopMeasure φ).restrict (unitBall n)) univ = 1 := by
  rw [hφ.d0TopMeasure_normalized, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hnonneg : ∀ᵐ x ∂((volume0 n).restrict (unitBall n)),
      0 ≤ Real.exp (-γ * φ x) / normalizingIntegral γ φ :=
    Filter.Eventually.of_forall (fun x =>
      (div_pos (Real.exp_pos _) hφ.normalizingIntegral_pos).le)
  rw [← ofReal_integral_eq_lintegral_ofReal
    hφ.normalized_density_integrableOn hnonneg]
  rw [hφ.normalized_density_integral, ENNReal.ofReal_one]

theorem IsNormalizedSolution.d0TopMeasure_isProbability {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    IsProbabilityMeasure ((d0TopMeasure φ).restrict (unitBall n)) :=
  ⟨hφ.d0TopMeasure_total_mass⟩

theorem IsNormalizedSolution.d1TopMeasure_half {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    (d1TopMeasure (fun y => φ y / 2)).restrict (unitBall n) =
      (d0TopMeasure φ).restrict (unitBall n) := by
  unfold d1TopMeasure d0TopMeasure exteriorTopMeasure
  have hB : MeasurableSet (unitBall n) := Metric.isOpen_ball.measurableSet
  simp only [restrict_withDensity hB]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet)] with x hx
  rw [d1Exterior_half (hφ.2.1.contDiffAt (Metric.ball_subset_closedBall hx))]

theorem normalizingIntegral_double_half {n : ℕ} (γ : ℝ) (φ : E n → ℝ) :
    normalizingIntegral (2 * γ) (fun x => φ x / 2) =
      normalizingIntegral γ φ := by
  unfold normalizingIntegral
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro x _
  congr 1
  ring

theorem IsNormalizedSolution.d1_half_normalized_eq {n : ℕ} {γ : ℝ}
    {φ : E n → ℝ} (hφ : IsNormalizedSolution n γ φ) :
    (d1TopMeasure (fun y => φ y / 2)).restrict (unitBall n) =
      ((volume0 n).restrict (unitBall n)).withDensity
        (fun x => ENNReal.ofReal
          (Real.exp (-(2 * γ) * (φ x / 2)) /
            normalizingIntegral (2 * γ) (fun y => φ y / 2))) := by
  have he (x : E n) : Real.exp (-(2 * γ) * (φ x / 2)) =
      Real.exp (-γ * φ x) := by
    congr 1
    ring
  simp only [hφ.d1TopMeasure_half, hφ.d0TopMeasure_normalized,
    normalizingIntegral_double_half, he]

#print axioms normalizedSolution_iff_exteriorEquation
#print axioms IsNormalizedSolution.d0TopMeasure_total_mass
#print axioms IsNormalizedSolution.d1_half_normalized_eq

end KEBall
