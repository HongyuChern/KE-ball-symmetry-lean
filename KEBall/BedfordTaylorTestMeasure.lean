import PshLines.PositiveDistributionMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Positive measures on open sets, tested on smooth functions

The measures live on the open subtype, so local finiteness is required only
at points in the domain.
-/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Manifold

namespace KEBall.BedfordTaylor

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- A compact set in an open domain admits a smooth cutoff valued in [0,1]. -/
theorem exists_testFunction_one_on {U : Opens H} {K : Set H}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ φ : 𝓓(U, ℝ), (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧ EqOn φ 1 K := by
  obtain ⟨V, hV, hKV, hVU, hc⟩ :=
    exists_open_between_and_isCompact_closure hK U.isOpen hKU
  obtain ⟨f, hf, hfr, hfs, hfK⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, H)) (n := ⊤)
      hV hK.isClosed hKV
  refine ⟨⟨f, hf.contDiff, ?_, ?_⟩, fun x => hfr (mem_range_self x), ?_⟩
  · simpa only [HasCompactSupport, tsupport, hfs] using hc
  · simpa only [tsupport, hfs] using hVU
  · intro x hx
    exact (hfK x).mp hx

variable [MeasurableSpace H] [BorelSpace H]

private theorem measure_compact_le_of_test {U : Opens H} {μ ν : Measure U}
    [μ.Regular] [ν.Regular]
    (htest : ∀ φ : 𝓓(U, ℝ), (∀ x, 0 ≤ φ x) → (∫ x : U, φ x ∂μ) ≤ ∫ x : U, φ x ∂ν)
    {K : Set U} (hK : IsCompact K) : μ K ≤ ν K := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  by_contra! hlt
  have hμK : μ K < ⊤ := hK.measure_lt_top
  obtain ⟨V, hKV, hV, hνV⟩ := hK.exists_isOpen_lt_of_lt (μ := ν) (μ K) hlt
  have hνVfin : ν V < ⊤ := hνV.trans hμK
  let K' : Set H := Subtype.val '' K
  let V' : Opens H := ⟨Subtype.val '' V, U.isOpen.isOpenMap_subtype_val V hV⟩
  have hK' : IsCompact K' := hK.image continuous_subtype_val
  have hK'V' : K' ⊆ V' := image_mono hKV
  have hV'U : V' ≤ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  obtain ⟨φ, hφ, hφK⟩ := exists_testFunction_one_on hK' hK'V'
  let ψ : 𝓓(U, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hV'U⟩
  have hle (x : U) : K.indicator 1 x ≤ ψ x := by
    by_cases hx : x ∈ K
    · have hx' : (x : H) ∈ K' := ⟨x, hx, rfl⟩
      rw [indicator_of_mem hx]
      change 1 ≤ φ (x : H)
      exact (hφK hx').ge
    · rw [indicator_of_notMem hx]
      exact (hφ x).1
  have hge (x : U) : ψ x ≤ V.indicator 1 x := by
    by_cases hx : x ∈ V
    · rw [indicator_of_mem hx]
      exact (hφ x).2
    · rw [indicator_of_notMem hx]
      have hx' : (x : H) ∉ tsupport φ := by
        intro h
        obtain ⟨y, hy, he⟩ := φ.tsupport_subset h
        exact hx (Subtype.ext he ▸ hy)
      exact (image_eq_zero_of_notMem_tsupport hx').le
  have hleft : Integrable (fun x : U => ψ x) μ :=
    (PshLines.testFunctionToCompactlySupportedLM U ψ).integrable
  have hright : Integrable (fun x : U => ψ x) ν :=
    (PshLines.testFunctionToCompactlySupportedLM U ψ).integrable
  have hKint : Integrable (K.indicator (1 : U → ℝ)) μ :=
    (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hVint : Integrable (V.indicator (1 : U → ℝ)) ν :=
    (integrableOn_const (hs := hνVfin.ne)).integrable_indicator hV.measurableSet
  have hleReal : μ.real K ≤ ν.real V := by
    rw [← integral_indicator_one hK.measurableSet, ← integral_indicator_one hV.measurableSet]
    exact (integral_mono hKint hleft hle).trans
      ((htest ψ (fun x => (hφ x).1)).trans (integral_mono hright hVint hge))
  exact (not_le_of_gt hνV) ((ENNReal.toReal_le_toReal hμK.ne hνVfin.ne).mp hleReal)

/-- Nonnegative compact smooth tests detect the order of regular measures. -/
theorem measure_le_of_smooth_test {U : Opens H} {μ ν : Measure U}
    [μ.Regular] [ν.Regular]
    (htest : ∀ φ : 𝓓(U, ℝ), (∀ x, 0 ≤ φ x) →
      (∫ x : U, φ x ∂μ) ≤ ∫ x : U, φ x ∂ν) : μ ≤ ν := by
  intro A
  rw [A.measure_eq_iInf_isOpen ν]
  refine le_iInf₂ fun V hAV => le_iInf fun hV => (measure_mono hAV).trans ?_
  rw [Measure.Regular.innerRegular.measure_eq_iSup (μ := μ) hV]
  exact iSup_le fun K => iSup_le fun hKV => iSup_le fun hK =>
    (measure_compact_le_of_test htest hK).trans (measure_mono hKV)

/-- Locally finite regular measures are determined by their compactly supported
smooth test integrals on the domain. -/
theorem measure_eq_of_smooth_test {U : Opens H} {μ ν : Measure U}
    [μ.Regular] [ν.Regular]
    (htest : ∀ φ : 𝓓(U, ℝ), (∫ x : U, φ x ∂μ) = ∫ x : U, φ x ∂ν) : μ = ν :=
  le_antisymm (measure_le_of_smooth_test fun φ _ => (htest φ).le)
    (measure_le_of_smooth_test fun φ _ => (htest φ).ge)

/-- Nonnegative compact smooth tests detect the order of measures carried
by the open domain and finite on its compact subsets. -/
theorem ambientMeasure_le_of_smooth_test {U : Opens H} {μ ν : Measure H}
    (hμ₀ : μ (U : Set H)ᶜ = 0) (hν₀ : ν (U : Set H)ᶜ = 0)
    (hμ : ∀ K : Set H, IsCompact K → K ⊆ U → μ K < ⊤)
    (hν : ∀ K : Set H, IsCompact K → K ⊆ U → ν K < ⊤)
    (htest : ∀ φ : 𝓓(U, ℝ), (∀ x, 0 ≤ φ x) → (∫ x, φ x ∂μ) ≤ ∫ x, φ x ∂ν) : μ ≤ ν := by
  let f : U → H := Subtype.val
  let μ' := μ.comap f
  let ν' := ν.comap f
  have hf := MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have finiteOnCompacts {ρ : Measure H}
      (hρ : ∀ K : Set H, IsCompact K → K ⊆ U → ρ K < ⊤) :
      IsFiniteMeasureOnCompacts (ρ.comap f) := by
    constructor
    intro K hK
    calc
      (ρ.comap f) K = ρ (Subtype.val '' K) := hf.comap_apply ρ K
      _ < ⊤ := hρ _ (hK.image continuous_subtype_val) (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let : IsFiniteMeasureOnCompacts μ' := finiteOnCompacts hμ
  let : IsFiniteMeasureOnCompacts ν' := finiteOnCompacts hν
  have hr {ρ : Measure H} (hρ : ρ (U : Set H)ᶜ = 0) :
      ρ.restrict (U : Set H) = ρ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rwa [ae_iff]
  have hsub : μ' ≤ ν' := by
    apply measure_le_of_smooth_test
    intro φ hφ
    have hiμ : (∫ x : U, φ x ∂μ') = ∫ x, φ x ∂μ := by
      have h := integral_subtype_comap (μ := μ) U.isOpen.measurableSet (φ : H → ℝ)
      rwa [hr hμ₀] at h
    have hiν : (∫ x : U, φ x ∂ν') = ∫ x, φ x ∂ν := by
      have h := integral_subtype_comap (μ := ν) U.isOpen.measurableSet (φ : H → ℝ)
      rwa [hr hν₀] at h
    rw [hiμ, hiν]
    exact htest φ hφ
  calc
    μ = Measure.map f μ' :=
      (hr hμ₀).symm.trans (map_comap_subtype_coe U.isOpen.measurableSet μ).symm
    _ ≤ Measure.map f ν' := Measure.map_mono hsub hf.measurable
    _ = ν := (map_comap_subtype_coe U.isOpen.measurableSet ν).trans (hr hν₀)

/-- Measures extended by zero from an open set are determined by smooth
test integrals and local finiteness in that set. -/
theorem ambientMeasure_eq_of_smooth_test {U : Opens H} {μ ν : Measure H}
    (hμ₀ : μ (U : Set H)ᶜ = 0) (hν₀ : ν (U : Set H)ᶜ = 0)
    (hμ : ∀ K : Set H, IsCompact K → K ⊆ U → μ K < ⊤)
    (hν : ∀ K : Set H, IsCompact K → K ⊆ U → ν K < ⊤)
    (htest : ∀ φ : 𝓓(U, ℝ), (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν) : μ = ν :=
  le_antisymm (ambientMeasure_le_of_smooth_test hμ₀ hν₀ hμ hν (fun φ _ => (htest φ).le))
    (ambientMeasure_le_of_smooth_test hν₀ hμ₀ hν hμ (fun φ _ => (htest φ).ge))

#print axioms measure_eq_of_smooth_test
#print axioms ambientMeasure_eq_of_smooth_test

end KEBall.BedfordTaylor
