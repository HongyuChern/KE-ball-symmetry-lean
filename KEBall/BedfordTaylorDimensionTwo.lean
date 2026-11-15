import KEBall.BedfordTaylorSecondTopMeasure
import KEBall.BedfordTaylorJointWeightLimit

/-!
# The Bedford–Taylor relation in complex dimension two
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {Ω : Opens (ComplexModel 2)} {u : ComplexModel 2 → ℝ}

/-- In dimension two a locally bounded PSH potential has the local
Bedford–Taylor measure for every admissible smooth approximation. -/
theorem isLocalBedfordTaylorMeasure_two (hu : IsLocallyBoundedPshOn Ω u) :
    IsLocalBedfordTaylorMeasure Ω u (secondTopMeasure hu) := by
  refine ⟨hu, secondTopMeasure_compl hu, fun _ => secondTopMeasure_finite_on_compact hu, ?_⟩
  intro V hV
  refine ⟨exists_decreasingMollifierApproximation hu hV, ?_⟩
  intro p hp f hf hfc hfV
  have hVΩ : V ≤ Ω := subset_closure.trans hV.2
  let huV := IsLocallyBoundedPshOn.mono hu hVΩ
  let hpS : ∀ j, IsSmoothPshOn V (p j) := hp.1
  let hpL := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hpS j)
  let μ := fun j => secondMixedMeasure (hpL j) (hpL j) coordinateVector
  let ν := secondMixedMeasure huV huV coordinateVector
  let : ∀ j, (μ j).Regular := fun j => secondMixedMeasure_regular (hpL j) (hpL j) coordinateVector
  let : ν.Regular := secondMixedMeasure_regular huV huV coordinateVector
  have htest (φ : 𝓓(V, ℝ)) :
      Tendsto (fun j => ∫ x : V, φ x ∂μ j) atTop (𝓝 (∫ x : V, φ x ∂ν)) := by
    simp only [μ, ν, integral_secondMixedMeasure]
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_secondMixedHessian_of_decreasing_smooth huV huV hpS hpS
        hp.2.1 hp.2.2 hp.2.1 hp.2.2 coordinateVector coordinateVector φ)
  have hweak := tendsto_integral_of_tendsto_smooth_tests htest hf hfc hfV
  have hres : (∫ x, f x ∂secondTopMeasure hu) =
      ∫ x, f x ∂secondTopMeasure huV := by
    rw [← secondTopMeasure_restrict hu hVΩ,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun _ hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hfV ht)))]
  change Tendsto (fun j => ∫ x, f x ∂smoothMeasure V (p j) (hpS j)) atTop
    (𝓝 (∫ x, f x ∂secondTopMeasure hu))
  rw [hres, integral_secondTopMeasure_map huV f]
  simp_rw [← secondTopMeasure_eq_smoothMeasure, integral_secondTopMeasure_map]
  exact tendsto_const_nhds.mul hweak

theorem isLocalBedfordTaylorMeasure_two_of_continuous
    (hu : IsLocallyBoundedPshOn Ω u) (_hc : ContinuousOn u Ω) :
    IsLocalBedfordTaylorMeasure Ω u (secondTopMeasure hu) :=
  isLocalBedfordTaylorMeasure_two hu

#print axioms isLocalBedfordTaylorMeasure_two

end KEBall.BedfordTaylor
