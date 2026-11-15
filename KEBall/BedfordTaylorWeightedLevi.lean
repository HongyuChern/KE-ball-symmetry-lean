import KEBall.BedfordTaylorLeviMeasure

/-!
# Multiplying a Levi measure by a locally bounded PSH potential

The coefficient measures of the first Levi form can be multiplied by a
second potential before taking the next distributional derivative.
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}

theorem measurable_subtype_of_locallyBoundedPsh (hu : IsLocallyBoundedPshOn Ω u) :
    Measurable (fun z : Ω => u z) := by
  have hsc : UpperSemicontinuousOn (fun z : Ω => (u z : EReal)) univ :=
    hu.1.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun z _ => z.property)
  have hm := (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  simpa only [Function.comp_def, EReal.toReal_coe] using measurable_ereal_toReal.comp hm

/-- A locally bounded PSH function is locally integrable against the zero
extension of any measure locally finite on the open domain. -/
theorem locallyIntegrableOn_map_subtype_of_locallyBoundedPsh
    (hu : IsLocallyBoundedPshOn Ω u) (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] :
    LocallyIntegrableOn u Ω (μ.map (Subtype.val : Ω → ComplexModel n)) := by
  let ρ := μ.map (Subtype.val : Ω → ComplexModel n)
  have he := MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet
  have hm : AEMeasurable u (ρ.restrict Ω) :=
    aemeasurable_restrict_of_measurable_subtype Ω.isOpen.measurableSet
      (measurable_subtype_of_locallyBoundedPsh hu)
  apply (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2
  intro K hKΩ hK
  have hc : IsCompact ((Subtype.val : Ω → ComplexModel n) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (by
      intro z hz
      exact ⟨⟨z, hKΩ hz⟩, rfl⟩)
  have hfin : ρ K < ⊤ := by
    rw [show ρ K = μ ((Subtype.val : Ω → ComplexModel n) ⁻¹' K) from he.map_apply μ K]
    exact hc.measure_lt_top
  obtain ⟨C, _, hC⟩ := hu.exists_compact_abs_bound hK hKΩ
  refine IntegrableOn.of_bound hfin
    (hm.mono_measure (Measure.restrict_mono_set _ hKΩ)).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  simpa only [Real.norm_eq_abs] using hC z hz

theorem integrable_test_mul_psh (hu : IsLocallyBoundedPshOn Ω u)
    (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] (χ : 𝓓(Ω, ℝ)) :
    Integrable (fun x : Ω => χ x * u x) μ :=
  (MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet).integrable_map_iff.mp
    (χ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrableOn_map_subtype_of_locallyBoundedPsh hu μ))

private theorem locallyIntegrableOn_directionalLeviMeasure
    (hu : IsLocallyBoundedPshOn Ω u) (hp : IsLocallyBoundedPshOn Ω p) (v : ComplexModel n) :
    LocallyIntegrableOn u Ω ((directionalLeviMeasure hp v).map (Subtype.val : Ω → ComplexModel n)) := by
  let : (directionalLeviMeasure hp v).Regular := directionalLeviMeasure_regular hp v
  exact locallyIntegrableOn_map_subtype_of_locallyBoundedPsh hu _

/-- The distribution induced by multiplying a directional Levi coefficient
of `p` by the PSH weight `u`. -/
noncomputable def weightedLeviDistribution (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v : ComplexModel n) : 𝓓'(Ω, ℝ) :=
  regularDistribution _ u (locallyIntegrableOn_directionalLeviMeasure hu hp v)

theorem weightedLeviDistribution_apply (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    weightedLeviDistribution hu hp v φ =
      ∫ z : Ω, φ z * u z ∂directionalLeviMeasure hp v := by
  rw [weightedLeviDistribution, regularDistribution_apply]
  exact (MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet).integral_map
    (fun z : ComplexModel n => φ z * u z)

theorem distributionalLeviCLM_weightedLeviDistribution_apply (hu : IsLocallyBoundedPshOn Ω u)
    (hp : IsLocallyBoundedPshOn Ω p) (v w : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM w (weightedLeviDistribution hu hp v) φ =
      ∫ z : Ω, u z * leviForm φ z w ∂directionalLeviMeasure hp v := by
  rw [weightedLeviDistribution, distributionalLeviCLM_regularDistribution_apply]
  exact (MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet).integral_map
    (fun z : ComplexModel n => u z * leviForm φ z w)

/-- A decreasing sequence of locally bounded PSH weights converges after
integration against any fixed positive Radon measure on the open domain. -/
theorem tendsto_integral_psh_weight_of_antitone (hu : IsLocallyBoundedPshOn Ω u)
    {q : ℕ → ComplexModel n → ℝ} (hq : ∀ j, IsLocallyBoundedPshOn Ω (q j))
    (hanti : ∀ x ∈ Ω, Antitone (fun j => q j x))
    (hlim : ∀ x ∈ Ω, Tendsto (fun j => q j x) atTop (𝓝 (u x)))
    (μ : Measure Ω) [μ.Regular] (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun j => ∫ x : Ω, φ x * q j x ∂μ) atTop (𝓝 (∫ x : Ω, φ x * u x ∂μ)) := by
  obtain ⟨C, _, hC⟩ :=
    exists_compact_abs_bound_of_antitone hu hq hanti hlim φ.hasCompactSupport φ.tsupport_subset
  apply tendsto_integral_of_dominated_convergence (fun x : Ω => C * |φ x|)
  · intro j
    exact ((φ.continuous.comp continuous_subtype_val).measurable.mul
      (measurable_subtype_of_locallyBoundedPsh (hq j))).aestronglyMeasurable
  · exact (testFunctionToCompactlySupportedLM Ω φ).integrable.abs.const_mul C
  · intro j
    filter_upwards with x
    rw [Real.norm_eq_abs, mul_comm (φ x), abs_mul]
    by_cases hx : (x : ComplexModel n) ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (hC j x hx) (abs_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, abs_zero, mul_zero, le_refl]
  · filter_upwards with x
    exact tendsto_const_nhds.mul (hlim x x.property)

#print axioms weightedLeviDistribution_apply
#print axioms distributionalLeviCLM_weightedLeviDistribution_apply

end KEBall.BedfordTaylor
