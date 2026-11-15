import KEBall.BedfordTaylorLocalLevi
import KEBall.BedfordTaylorSmoothCompatibility

/-!
# The local Bedford–Taylor measure in complex dimension one

In this dimension the normalized top product is the first Levi measure
divided by π. Its construction requires no higher mixed products.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {U : Opens (ComplexModel 1)} {u : ComplexModel 1 → ℝ}

/-- The positive measure of `ddᶜ u` in complex dimension one, with
`ddᶜ = i ∂∂̄ / (2π)`. -/
noncomputable def bedfordTaylorMeasureOne (hu : IsLocallyBoundedPshOn U u) :
    Measure (ComplexModel 1) :=
  ENNReal.ofReal Real.pi⁻¹ • ambientDirectionalLeviMeasure hu (coordinateVector 0)

private theorem bedfordTaylorMeasureOne_compl (hu : IsLocallyBoundedPshOn U u) :
    bedfordTaylorMeasureOne hu (U : Set (ComplexModel 1))ᶜ = 0 := by
  rw [bedfordTaylorMeasureOne, Measure.smul_apply, ambientDirectionalLeviMeasure_compl]
  simp

private theorem bedfordTaylorMeasureOne_finite_on_compact
    (hu : IsLocallyBoundedPshOn U u) {K : Set (ComplexModel 1)} (hK : IsCompact K) (hKU : K ⊆ U) :
    bedfordTaylorMeasureOne hu K < ⊤ := by
  rw [bedfordTaylorMeasureOne, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ambientDirectionalLeviMeasure_finite_on_compact hu (coordinateVector 0) hK hKU)

theorem bedfordTaylorMeasureOne_eq_smoothMeasure (hu : IsSmoothPshOn U u) :
    bedfordTaylorMeasureOne (isLocallyBoundedPshOn_of_isSmoothPshOn hu) = smoothMeasure U u hu := by
  apply ambientMeasure_eq_of_smooth_test (bedfordTaylorMeasureOne_compl _)
    (smoothMeasure_compl hu) (fun _ => bedfordTaylorMeasureOne_finite_on_compact _)
    (smoothMeasure_finite_on_compact hu)
  intro φ
  rw [bedfordTaylorMeasureOne, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    integral_ambientDirectionalLeviMeasure, integral_directionalLeviMeasure_of_isSmoothPshOn hu,
    smul_eq_mul, ← integral_const_mul, smoothMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((continuousOn_smoothDensity hu.1).aemeasurable U.isOpen.measurableSet).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ,
    ← integral_indicator U.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz, smoothMeasure_weight_toReal U u hu hz]
    simp only [smul_eq_mul, smoothDensity, Nat.factorial_one, Nat.cast_one, pow_one, one_div,
      Matrix.det_fin_one, complexHessian_diagonal_re]
    ring
  · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (φ.tsupport_subset ht))
    simp [hφ, hz]

/-- Every locally bounded PSH potential in complex dimension one has the
Bedford–Taylor measure, with convergence for all admissible approximations. -/
theorem isLocalBedfordTaylorMeasure_one (hu : IsLocallyBoundedPshOn U u) :
    IsLocalBedfordTaylorMeasure U u (bedfordTaylorMeasureOne hu) := by
  refine ⟨hu, bedfordTaylorMeasureOne_compl hu,
    fun _ => bedfordTaylorMeasureOne_finite_on_compact hu, fun V hVU => ?_⟩
  refine ⟨exists_decreasingMollifierApproximation hu hVU, ?_⟩
  intro p hp f hf hfc hfV
  have hsub : V ≤ U := subset_closure.trans hVU.2
  have hp₁ : ∀ j, IsSmoothPshOn V (p j) := hp.1
  have h := tendsto_directionalLeviMeasure_continuous_test (IsLocallyBoundedPshOn.mono hu hsub)
    (fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hp₁ j)) hp.2.1 hp.2.2
    (coordinateVector 0) hf hfc hfV
  change Tendsto (fun j => ∫ z, f z ∂smoothMeasure V (p j) (hp₁ j)) atTop
    (𝓝 (∫ z, f z ∂bedfordTaylorMeasureOne hu))
  simp_rw [← bedfordTaylorMeasureOne_eq_smoothMeasure, bedfordTaylorMeasureOne, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.pi_pos.le),
    smul_eq_mul]
  have heq : (∫ z, f z ∂ambientDirectionalLeviMeasure hu (coordinateVector 0)) =
      ∫ z : V, f z ∂directionalLeviMeasure (IsLocallyBoundedPshOn.mono hu hsub) (coordinateVector 0) := by
    rw [← integral_ambientDirectionalLeviMeasure, ← ambientDirectionalLeviMeasure_restrict hu hsub,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => image_eq_zero_of_notMem_tsupport (fun ht => hz (hfV ht)))]
  simp_rw [heq, integral_ambientDirectionalLeviMeasure]
  exact tendsto_const_nhds.mul h

theorem bedfordTaylorMeasureOne_eq_map_d0TopMeasure_unitBall {q : E 1 → ℝ}
    (hq : IsSmoothPshOn (complexUnitBall 1) (q ∘ (complexCoordinates 1).symm)) :
    bedfordTaylorMeasureOne (isLocallyBoundedPshOn_of_isSmoothPshOn hq) =
      Measure.map (complexCoordinates 1) ((d0TopMeasure q).restrict (unitBall 1)) :=
  eq_map_d0TopMeasure_unitBall (isLocalBedfordTaylorMeasure_one _) hq

#print axioms bedfordTaylorMeasureOne_eq_smoothMeasure
#print axioms isLocalBedfordTaylorMeasure_one
#print axioms bedfordTaylorMeasureOne_eq_map_d0TopMeasure_unitBall

end KEBall.BedfordTaylor
