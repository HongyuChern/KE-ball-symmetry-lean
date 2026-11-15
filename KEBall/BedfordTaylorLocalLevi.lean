import KEBall.BedfordTaylorWeakConvergence

/-!
# Locality and smooth integration by parts for Levi measures
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn IsSmoothPshOn)

variable {n : ℕ} {U V : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

theorem IsLocallyBoundedPshOn.mono (hu : IsLocallyBoundedPshOn U u) (hVU : V ≤ U) :
    IsLocallyBoundedPshOn V u := by
  refine ⟨hu.1.mono hVU, fun x hx => ?_⟩
  obtain ⟨W, hxW, _, C, hC⟩ := hu.2 x (hVU hx)
  exact ⟨W ⊓ V, ⟨hxW, hx⟩, inf_le_right, C, fun y hy => hC y hy.1⟩

theorem isLocallyBoundedPshOn_of_isSmoothPshOn (hu : IsSmoothPshOn U u) :
    IsLocallyBoundedPshOn U u := by
  refine ⟨hu.2.1, fun x hx => ?_⟩
  have hn : {y | |u y| < |u x| + 1} ∩ (U : Set (ComplexModel n)) ∈ 𝓝 x :=
    inter_mem (((hu.1 x hx).contDiffAt (U.isOpen.mem_nhds hx)).continuousAt.abs
      (Iio_mem_nhds (lt_add_one _))) (U.isOpen.mem_nhds hx)
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hn
  exact ⟨⟨W, hWo⟩, hxW, fun _ hy => (hW hy).2, |u x| + 1, fun y hy => (hW hy).1.le⟩

private theorem integral_mul_leviForm_eq_integral_leviForm_mul
    (hu : ContDiffOn ℝ ∞ u U) (v : ComplexModel n) (φ : 𝓓(U, ℝ)) :
    (∫ z, u z * leviForm φ z v) = ∫ z, φ z * leviForm u z v := by
  obtain ⟨W, hWo, hφW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport U.isOpen φ.tsupport_subset
  obtain ⟨χ, _, hχ⟩ := exists_testFunction_one_on hWc hWU
  let g := fun z => χ z * u z
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact χ.contDiff.contDiffAt.mul ((hu z hz).contDiffAt (U.isOpen.mem_nhds hz))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hzχ : z ∈ (tsupport χ)ᶜ := fun ht => hz (χ.tsupport_subset ht)
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hzχ] with y hy
      change χ y * u y = 0
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have heq (z : ComplexModel n) (hz : z ∈ tsupport φ) : g =ᶠ[𝓝 z] u := by
    filter_upwards [hWo.mem_nhds (hφW hz)] with y hy
    change χ y * u y = u y
    rw [hχ (subset_closure hy), Pi.one_apply, one_mul]
  have hg2 : ContDiff ℝ 2 g := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hgL : LocallyIntegrableOn g U volume := hg.continuous.locallyIntegrable.locallyIntegrableOn U
  have hpair := congrArg (fun T : 𝓓'(U, ℝ) => T φ)
    (distributionalLeviCLM_regularDistribution (μ := volume) (Ω := U) hg2 v)
  change distributionalLeviCLM v (regularDistribution volume g hgL) φ = _ at hpair
  rw [distributionalLeviCLM_regularDistribution_apply, regularDistribution_apply] at hpair
  calc
    _ = ∫ z, g z * leviForm φ z v := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport φ
      · rw [(heq z hz).eq_of_nhds]
      · simp [leviForm_eq_zero_of_notMem_tsupport hz v]
    _ = ∫ z, φ z * leviForm g z v := hpair
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport φ
      · have hd := ((heq z hz).iteratedFDeriv (𝕜 := ℝ) 2).eq_of_nhds
        simp only [leviForm, realHessian, hd]
      · simp [image_eq_zero_of_notMem_tsupport hz]

/-- On its smooth locus the first-degree Levi measure has the classical
Levi density, tested against smooth compactly supported functions. -/
theorem integral_directionalLeviMeasure_of_isSmoothPshOn
    (hu : IsSmoothPshOn U u) (v : ComplexModel n) (φ : 𝓓(U, ℝ)) :
    (∫ z : U, φ z ∂directionalLeviMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn hu) v) =
      ∫ z, φ z * leviForm u z v :=
  (integral_directionalLeviMeasure _ v φ).trans
    (integral_mul_leviForm_eq_integral_leviForm_mul hu.1 v φ)

/-- Extend the directional Levi measure by zero to the ambient space. -/
noncomputable def ambientDirectionalLeviMeasure (hu : IsLocallyBoundedPshOn U u)
    (v : ComplexModel n) : Measure (ComplexModel n) :=
  (directionalLeviMeasure hu v).map Subtype.val

theorem integral_ambientDirectionalLeviMeasure (hu : IsLocallyBoundedPshOn U u)
    (v : ComplexModel n) (f : ComplexModel n → ℝ) :
    (∫ z, f z ∂ambientDirectionalLeviMeasure hu v) = ∫ z : U, f z ∂directionalLeviMeasure hu v :=
  (MeasurableEmbedding.subtype_coe U.isOpen.measurableSet).integral_map f

theorem ambientDirectionalLeviMeasure_compl (hu : IsLocallyBoundedPshOn U u)
    (v : ComplexModel n) :
    ambientDirectionalLeviMeasure hu v (U : Set (ComplexModel n))ᶜ = 0 := by
  rw [ambientDirectionalLeviMeasure, Measure.map_apply measurable_subtype_coe
    U.isOpen.measurableSet.compl]
  have hempty : (Subtype.val : U → ComplexModel n) ⁻¹' (U : Set (ComplexModel n))ᶜ = ∅ := by
    ext z
    exact iff_false_intro (fun h => h z.property)
  rw [hempty, measure_empty]

theorem ambientDirectionalLeviMeasure_finite_on_compact (hu : IsLocallyBoundedPshOn U u)
    (v : ComplexModel n) {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ambientDirectionalLeviMeasure hu v K < ⊤ := by
  let : (directionalLeviMeasure hu v).Regular := directionalLeviMeasure_regular hu v
  rw [ambientDirectionalLeviMeasure, Measure.map_apply measurable_subtype_coe hK.measurableSet]
  have hc : IsCompact ((Subtype.val : U → ComplexModel n) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (by
      intro z hz
      exact ⟨⟨z, hKU hz⟩, rfl⟩)
  exact hc.measure_lt_top

/-- Restricting the zero-extended Levi measure to an inner open set agrees
with constructing it there from the restricted potential. -/
theorem ambientDirectionalLeviMeasure_restrict (hu : IsLocallyBoundedPshOn U u)
    (hVU : V ≤ U) (v : ComplexModel n) :
    (ambientDirectionalLeviMeasure hu v).restrict (V : Set (ComplexModel n)) =
      ambientDirectionalLeviMeasure (IsLocallyBoundedPshOn.mono hu hVU) v := by
  apply ambientMeasure_eq_of_smooth_test (U := V)
  · rw [Measure.restrict_apply V.isOpen.measurableSet.compl, compl_inter_self, measure_empty]
  · exact ambientDirectionalLeviMeasure_compl _ _
  · intro K hK hKV
    exact (Measure.restrict_le_self K).trans_lt
      (ambientDirectionalLeviMeasure_finite_on_compact hu v hK (hKV.trans hVU))
  · intro K hK hKV
    exact ambientDirectionalLeviMeasure_finite_on_compact _ _ hK hKV
  · intro φ
    rw [← integral_indicator V.isOpen.measurableSet,
      indicator_eq_self.mpr ((subset_tsupport φ).trans φ.tsupport_subset),
      integral_ambientDirectionalLeviMeasure, integral_ambientDirectionalLeviMeasure]
    let ψ : 𝓓(U, ℝ) :=
      ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
    change (∫ z : U, ψ z ∂directionalLeviMeasure hu v) = _
    rw [integral_directionalLeviMeasure, integral_directionalLeviMeasure]
    rfl

#print axioms integral_directionalLeviMeasure_of_isSmoothPshOn
#print axioms ambientDirectionalLeviMeasure_restrict

end KEBall.BedfordTaylor
