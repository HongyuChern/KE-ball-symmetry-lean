import KEBall.BedfordTaylorWeightedLevi

/-!
# Weighting real measure coefficients

A real order-zero coefficient is represented as the difference of two
positive Radon measures on the domain. Multiplication by a locally
bounded PSH function is independent of the representing pair.
-/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

private theorem regular_add (μ ν : Measure Ω) [μ.Regular] [ν.Regular] : (μ + ν).Regular := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let : IsFiniteMeasureOnCompacts (μ + ν) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  infer_instance

/-- A distribution represented by a difference of positive Radon measures. -/
def IsMeasureDifference (T : 𝓓'(Ω, ℝ)) : Prop :=
  ∃ μ ν : Measure Ω, μ.Regular ∧ ν.Regular ∧
    ∀ φ : 𝓓(Ω, ℝ), T φ = (∫ x : Ω, φ x ∂μ) - ∫ x : Ω, φ x ∂ν

noncomputable def weightRadonMeasure (hu : IsLocallyBoundedPshOn Ω u)
    (μ : Measure Ω) [μ.Regular] : 𝓓'(Ω, ℝ) :=
  regularDistribution (μ.map (Subtype.val : Ω → ComplexModel n)) u
    (locallyIntegrableOn_map_subtype_of_locallyBoundedPsh hu μ)

theorem weightRadonMeasure_apply (hu : IsLocallyBoundedPshOn Ω u)
    (μ : Measure Ω) [μ.Regular] (φ : 𝓓(Ω, ℝ)) :
    weightRadonMeasure hu μ φ = ∫ x : Ω, φ x * u x ∂μ := by
  rw [weightRadonMeasure, regularDistribution_apply]
  exact (MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet).integral_map
    (fun x : ComplexModel n => φ x * u x)

/-- The difference of weighted measures representing a real coefficient. -/
noncomputable def weightMeasureDifference {T : 𝓓'(Ω, ℝ)}
    (hu : IsLocallyBoundedPshOn Ω u) (hT : IsMeasureDifference T) : 𝓓'(Ω, ℝ) := by
  classical
  let μ := hT.choose
  let ν := hT.choose_spec.choose
  let : μ.Regular := hT.choose_spec.choose_spec.1
  let : ν.Regular := hT.choose_spec.choose_spec.2.1
  exact weightRadonMeasure hu μ - weightRadonMeasure hu ν

/-- The weighted coefficient can be evaluated with any pair of positive
measures representing the original coefficient. -/
theorem weightMeasureDifference_apply {T : 𝓓'(Ω, ℝ)}
    (hu : IsLocallyBoundedPshOn Ω u) (hT : IsMeasureDifference T)
    {μ ν : Measure Ω} [μ.Regular] [ν.Regular]
    (hpair : ∀ ψ : 𝓓(Ω, ℝ), T ψ = (∫ x : Ω, ψ x ∂μ) - ∫ x : Ω, ψ x ∂ν)
    (φ : 𝓓(Ω, ℝ)) :
    weightMeasureDifference hu hT φ = (∫ x : Ω, φ x * u x ∂μ) - ∫ x : Ω, φ x * u x ∂ν := by
  classical
  let μ₀ := hT.choose
  let ν₀ := hT.choose_spec.choose
  let : μ₀.Regular := hT.choose_spec.choose_spec.1
  let : ν₀.Regular := hT.choose_spec.choose_spec.2.1
  let : (μ₀ + ν).Regular := regular_add μ₀ ν
  let : (μ + ν₀).Regular := regular_add μ ν₀
  have hpair₀ : ∀ ψ : 𝓓(Ω, ℝ), T ψ = (∫ x : Ω, ψ x ∂μ₀) - ∫ x : Ω, ψ x ∂ν₀ :=
    hT.choose_spec.choose_spec.2.2
  have hsum : μ₀ + ν = μ + ν₀ := by
    apply measure_eq_of_smooth_test
    intro ψ
    have hint (ρ : Measure Ω) [ρ.Regular] : Integrable (fun x : Ω => ψ x) ρ :=
      (testFunctionToCompactlySupportedLM Ω ψ).integrable
    rw [integral_add_measure (hint μ₀) (hint ν), integral_add_measure (hint μ) (hint ν₀)]
    linarith [hpair ψ, hpair₀ ψ]
  have heq := congrArg (fun ρ : Measure Ω => ∫ x : Ω, φ x * u x ∂ρ) hsum
  rw [integral_add_measure (integrable_test_mul_psh hu μ₀ φ) (integrable_test_mul_psh hu ν φ),
    integral_add_measure (integrable_test_mul_psh hu μ φ) (integrable_test_mul_psh hu ν₀ φ)] at heq
  change (weightRadonMeasure hu μ₀ - weightRadonMeasure hu ν₀) φ = _
  rw [sub_apply, weightRadonMeasure_apply, weightRadonMeasure_apply]
  linarith

theorem weightMeasureDifference_congr {p : ComplexModel n → ℝ}
    {T : 𝓓'(Ω, ℝ)} (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p)
    (heq : EqOn u p Ω) (hT : IsMeasureDifference T) :
    weightMeasureDifference hu hT = weightMeasureDifference hp hT := by
  let μ := hT.choose
  let ν := hT.choose_spec.choose
  let : μ.Regular := hT.choose_spec.choose_spec.1
  let : ν.Regular := hT.choose_spec.choose_spec.2.1
  have hpair (ψ : 𝓓(Ω, ℝ)) : T ψ = (∫ x : Ω, ψ x ∂μ) - ∫ x : Ω, ψ x ∂ν :=
    hT.choose_spec.choose_spec.2.2 ψ
  ext φ
  rw [weightMeasureDifference_apply hu hT hpair, weightMeasureDifference_apply hp hT hpair]
  congr 1 <;> exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    congrArg (φ x * ·) (heq x.property))

end KEBall.BedfordTaylor
