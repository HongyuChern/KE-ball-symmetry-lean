import KEBall.DirichletHessianOscillationAlgebra
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Averaging the two-point directional comparison

This module uses a probability measure (the normalized measure of the
smaller ball in the application).  The scalar functions remain arbitrary
integrable representatives.  All upper and lower bounds are a.e. bounds.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace KEBall

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
variable {μ : Measure X} [IsProbabilityMeasure μ]

/-- Averaging the first spatial variable in the two-point inequality
controls the distance from an outer upper bound to the inner essential
infimum.  No point attaining an essential extremum is used. -/
theorem dirichlet_mean_defect_lower_control
    (q : ι → X → ℝ) (M : ι → ℝ) (hInt : ∀ i, Integrable (q i) μ)
    (hUpper : ∀ i, ∀ᵐ x ∂μ, q i x ≤ M i)
    {l U E : ℝ} (hl : 0 < l)
    (hCompare : ∀ j, ∀ᵐ y ∂μ, ∀ᵐ x ∂μ,
      l * (q j x - q j y) ≤ U * (∑ i : ι, (M i - q i x)) + E)
    (j : ι) :
    l * (M j - essInf (q j) μ) ≤
      l * (∫ x, M j - q j x ∂μ) +
        U * (∑ i : ι, ∫ x, M i - q i x ∂μ) + E := by
  let J : ι → ℝ := fun i => ∫ x, M i - q i x ∂μ
  let T : ℝ := U * (∑ i : ι, J i) + E
  have hDefInt (i : ι) : Integrable (fun x => M i - q i x) μ :=
    (integrable_const _).sub (hInt i)
  have hSumInt : Integrable (fun x => ∑ i : ι, (M i - q i x)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hDefInt i)
  have hJ (i : ι) : J i = M i - ∫ x, q i x ∂μ := by
    dsimp only [J]
    rw [integral_sub (integrable_const _) (hInt i)]
    simp
  have hMean : ∀ᵐ y ∂μ, l * ((∫ x, q j x ∂μ) - q j y) ≤ T := by
    filter_upwards [hCompare j] with y hy
    have h := integral_mono_ae (((hInt j).sub (integrable_const _)).const_mul l)
      ((hSumInt.const_mul U).add (integrable_const E)) hy
    change (∫ x, l * (q j x - q j y) ∂μ) ≤
      ∫ x, U * (∑ i : ι, (M i - q i x)) + E ∂μ at h
    simpa only [integral_add (hSumInt.const_mul U) (integrable_const E),
      integral_const_mul, integral_sub (hInt j) (integrable_const _),
      integral_finsetSum Finset.univ (fun i _ => hDefInt i), integral_const, probReal_univ,
      one_smul, T, J] using h
  have hLow : ∀ᵐ y ∂μ, (∫ x, q j x ∂μ) - T / l ≤ q j y := by
    filter_upwards [hMean] with y hy
    have he : (T / l) * l = T := div_mul_cancel₀ _ hl.ne'
    nlinarith only [hy, he, hl]
  have hBdd : IsBoundedUnder (· ≤ ·) (ae μ) (q j) := ⟨M j, hUpper j⟩
  have hInf := le_essInf_of_ae_le ((∫ x, q j x ∂μ) - T / l) hLow
    hBdd.isCoboundedUnder_ge
  have hMul := mul_le_mul_of_nonneg_left hInf hl.le
  have he : (T / l) * l = T := div_mul_cancel₀ _ hl.ne'
  have hFinal : l * (M j - essInf (q j) μ) ≤ l * J j + T := by
    rw [hJ]
    nlinarith only [hMul, he]
  simpa only [J, T, add_assoc] using hFinal

end KEBall
