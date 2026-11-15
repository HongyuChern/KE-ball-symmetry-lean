import KEBall.BedfordTaylorSecondMixedMeasure
import KEBall.BedfordTaylorSmoothCompatibility

/-!
# The normalized second product in complex dimension two

The top coefficient is a positive measure for each locally bounded PSH
potential. Its smooth density agrees with the original project measure.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere

variable {Ω : Opens (ComplexModel 2)} {u : ComplexModel 2 → ℝ}

/-- The second product of a potential with itself in the standard
orientation, normalized by `π⁻²` and extended by zero off the domain. -/
noncomputable def secondTopMeasure (hu : IsLocallyBoundedPshOn Ω u) :
    Measure (ComplexModel 2) :=
  ENNReal.ofReal ((Real.pi ^ 2)⁻¹) • (secondMixedMeasure hu hu coordinateVector).map Subtype.val

theorem secondTopMeasure_compl (hu : IsLocallyBoundedPshOn Ω u) :
    secondTopMeasure hu (Ω : Set (ComplexModel 2))ᶜ = 0 := by
  rw [secondTopMeasure, Measure.smul_apply,
    Measure.map_apply measurable_subtype_coe Ω.isOpen.measurableSet.compl]
  have hempty : (Subtype.val : Ω → ComplexModel 2) ⁻¹' (Ω : Set (ComplexModel 2))ᶜ = ∅ := by
    ext z
    exact iff_false_intro (fun h => h z.property)
  rw [hempty, measure_empty, smul_eq_mul, mul_zero]

theorem secondTopMeasure_finite_on_compact (hu : IsLocallyBoundedPshOn Ω u)
    {K : Set (ComplexModel 2)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    secondTopMeasure hu K < ⊤ := by
  let : (secondMixedMeasure hu hu coordinateVector).Regular :=
    secondMixedMeasure_regular hu hu coordinateVector
  have hc : IsCompact ((Subtype.val : Ω → ComplexModel 2) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (by
      intro z hz
      exact ⟨⟨z, hKΩ hz⟩, rfl⟩)
  rw [secondTopMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_subtype_coe hK.measurableSet]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc.measure_lt_top

private theorem smoothMixedHessianDensity_coordinate_eq {x : ComplexModel 2}
    (hu : ContDiffAt ℝ ∞ u x) :
    smoothMixedHessianDensity u u coordinateVector coordinateVector x =
      2 * (PshLines.FirstPass.MongeAmpere.complexHessian u x).det := by
  have hH (i j : Fin 2) :
      classicalComplexHessianEntry u (coordinateVector i) (coordinateVector j) x =
        PshLines.FirstPass.MongeAmpere.complexHessian u x i j := by
    rw [classicalComplexHessianEntry_eq_realHessian hu]
    rfl
  simp only [smoothMixedHessianDensity, hH, Matrix.det_fin_two]
  ring

theorem integral_secondTopMeasure_map (hu : IsLocallyBoundedPshOn Ω u) (f : ComplexModel 2 → ℝ) :
    (∫ x, f x ∂secondTopMeasure hu) =
      (Real.pi ^ 2)⁻¹ * ∫ x : Ω, f x ∂secondMixedMeasure hu hu coordinateVector := by
  rw [secondTopMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  exact (MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet).integral_map
    (μ := secondMixedMeasure hu hu coordinateVector) f

theorem integral_secondTopMeasure (hu : IsLocallyBoundedPshOn Ω u) (φ : 𝓓(Ω, ℝ)) :
    (∫ x, φ x ∂secondTopMeasure hu) =
      (Real.pi ^ 2)⁻¹ * (secondMixedHessian hu hu coordinateVector coordinateVector φ).re := by
  rw [integral_secondTopMeasure_map hu (fun x => φ x), integral_secondMixedMeasure]

theorem secondTopMeasure_restrict (hu : IsLocallyBoundedPshOn Ω u)
    {V : Opens (ComplexModel 2)} (hVΩ : V ≤ Ω) :
    (secondTopMeasure hu).restrict (V : Set (ComplexModel 2)) =
      secondTopMeasure (IsLocallyBoundedPshOn.mono hu hVΩ) := by
  apply ambientMeasure_eq_of_smooth_test (U := V)
  · rw [Measure.restrict_apply V.isOpen.measurableSet.compl, compl_inter_self, measure_empty]
  · exact secondTopMeasure_compl _
  · intro K hK hKV
    exact (Measure.restrict_le_self K).trans_lt
      (secondTopMeasure_finite_on_compact hu hK (hKV.trans hVΩ))
  · intro K hK hKV
    exact secondTopMeasure_finite_on_compact _ hK hKV
  · intro φ
    rw [← integral_indicator V.isOpen.measurableSet,
      indicator_eq_self.mpr ((subset_tsupport φ).trans φ.tsupport_subset)]
    change (∫ x, extendTest hVΩ φ x ∂secondTopMeasure hu) = _
    rw [integral_secondTopMeasure, integral_secondTopMeasure, secondMixedHessian_extendTest]

theorem secondTopMeasure_eq_smoothMeasure (hu : IsSmoothPshOn Ω u) :
    secondTopMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) = smoothMeasure Ω u hu := by
  apply ambientMeasure_eq_of_smooth_test (secondTopMeasure_compl _) (smoothMeasure_compl hu)
    (fun _ => secondTopMeasure_finite_on_compact _) (smoothMeasure_finite_on_compact hu)
  intro φ
  have hs := contDiffOn_smoothMixedHessianDensity hu.1 hu.1 coordinateVector coordinateVector
  have hI : Integrable (fun x => φ x • smoothMixedHessianDensity u u coordinateVector coordinateVector x) :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_of_contDiffOn hs)
  rw [integral_secondTopMeasure, secondMixedHessian_integral_of_isSmoothPshOn hu hu]
  change (Real.pi ^ 2)⁻¹ *
    Complex.reCLM (∫ x, φ x • smoothMixedHessianDensity u u coordinateVector coordinateVector x) = _
  rw [← Complex.reCLM.integral_comp_comm hI, ← integral_const_mul, smoothMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      ((continuousOn_smoothDensity hu.1).aemeasurable Ω.isOpen.measurableSet).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ,
    ← integral_indicator Ω.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · rw [indicator_of_mem hx, smoothMeasure_weight_toReal Ω u hu hx,
      smoothMixedHessianDensity_coordinate_eq (hu.1.contDiffAt (Ω.isOpen.mem_nhds hx))]
    norm_num [Complex.real_smul, Complex.mul_re, smoothDensity, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
    simp [hzero, hx]

theorem secondTopMeasure_eq_map_d0TopMeasure_unitBall {q : E 2 → ℝ}
    (hq : IsSmoothPshOn (complexUnitBall 2) (q ∘ (complexCoordinates 2).symm)) :
    secondTopMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hq) =
      Measure.map (complexCoordinates 2) ((d0TopMeasure q).restrict (unitBall 2)) := by
  rw [secondTopMeasure_eq_smoothMeasure hq]
  simpa only [preimage_complexUnitBall] using
    (map_d0TopMeasure_restrict_eq_smoothMeasure (complexUnitBall 2) hq).symm

#print axioms secondTopMeasure_eq_map_d0TopMeasure_unitBall

end KEBall.BedfordTaylor
