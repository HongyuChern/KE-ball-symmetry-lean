import KEBall.BedfordTaylorSmoothMeasure
import KEBall.BedfordTaylorTestMeasure

/-!
# Smooth compatibility for the local Bedford–Taylor relation

Constant smooth approximations identify any measure satisfying the
Bedford–Taylor relation, including when it is only locally finite in the domain.
-/

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsSmoothPshOn IsLocalBedfordTaylorMeasure RelativelyCompactIn smoothMeasure smoothDensity)

theorem continuousOn_smoothDensity {n : ℕ} {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContinuousOn (smoothDensity u) U := by
  have hD : ContinuousOn (iteratedFDeriv ℝ 2 u) U :=
    (hu.continuousOn_iteratedFDerivWithin (m := 2)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) U.isOpen.uniqueDiffOn).congr
      (fun x hx => (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) 2 U.isOpen hx).symm)
  have hR (a b : ComplexModel n) : ContinuousOn (fun z => PshLines.realHessian u z a b) U := by
    exact (continuous_eval_const ![a, b]).comp_continuousOn hD
  have hH : ContinuousOn (PshLines.FirstPass.MongeAmpere.complexHessian u) U := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    unfold PshLines.FirstPass.MongeAmpere.complexHessian
    fun_prop
  unfold smoothDensity
  exact continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
    (continuous_id.matrix_det.comp_continuousOn hH))

theorem smoothMeasure_finite_on_compact {n : ℕ} {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn U u)
    (K : Set (ComplexModel n)) (hK : IsCompact K) (hKU : K ⊆ U) :
    smoothMeasure U u hu K < ⊤ := by
  obtain ⟨C, hC⟩ :=
    (hK.image_of_continuousOn ((continuousOn_smoothDensity hu.1).mono hKU)).bddAbove
  unfold smoothMeasure
  rw [withDensity_apply _ hK.measurableSet]
  have hKfin : (volume.restrict (U : Set (ComplexModel n))) K < ⊤ :=
    (Measure.restrict_le_self K).trans_lt hK.measure_lt_top
  calc
    _ ≤ ∫⁻ x in K, ENNReal.ofReal C ∂volume.restrict (U : Set (ComplexModel n)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact ENNReal.ofReal_le_ofReal (hC ⟨x, hx, rfl⟩)
    _ < ⊤ := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin

theorem smoothMeasure_compl {n : ℕ} {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn U u) :
    smoothMeasure U u hu (U : Set (ComplexModel n))ᶜ = 0 := by
  unfold smoothMeasure
  rw [withDensity_apply _ U.isOpen.measurableSet.compl,
    Measure.restrict_restrict U.isOpen.measurableSet.compl]
  simp

/-- Compact-test convergence characterizes the local Bedford–Taylor measure
whenever it exists. -/
theorem isLocalBedfordTaylorMeasure_unique {n : ℕ}
    {U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure U u μ) (hν : IsLocalBedfordTaylorMeasure U u ν) :
    μ = ν := by
  apply ambientMeasure_eq_of_smooth_test hμ.2.1 hν.2.1 hμ.2.2.1 hν.2.2.1
  intro φ
  obtain ⟨V, hVo, hφV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport U.isOpen φ.tsupport_subset
  let W : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hrel : RelativelyCompactIn W U := ⟨hVc, hVU⟩
  obtain ⟨p, hp⟩ := hμ.approximations_exist hrel
  exact tendsto_nhds_unique
    ((hμ.2.2.2 W hrel).2 p hp φ φ.continuous φ.hasCompactSupport hφV)
    ((hν.2.2.2 W hrel).2 p hp φ φ.continuous φ.hasCompactSupport hφV)

/-- For a smooth PSH potential, any measure satisfying the local
Bedford–Taylor relation equals the ordinary smooth Monge–Ampère measure. -/
theorem eq_smoothMeasure_of_isLocalBedfordTaylorMeasure {n : ℕ}
    {U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure U u μ) (hu : IsSmoothPshOn U u) :
    μ = smoothMeasure U u hu := by
  apply ambientMeasure_eq_of_smooth_test hμ.2.1 (smoothMeasure_compl hu)
    hμ.2.2.1 (smoothMeasure_finite_on_compact hu)
  intro φ
  obtain ⟨V, hVo, hφV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport U.isOpen φ.tsupport_subset
  let W : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hrel : RelativelyCompactIn W U := ⟨hVc, hVU⟩
  have hWU : W ≤ U := subset_closure.trans hVU
  have hw : IsSmoothPshOn W u :=
    ⟨hu.1.mono hWU, hu.2.1.mono hWU, fun x hx => hu.2.2 x (hWU hx)⟩
  have hl := (hμ.2.2.2 W hrel).2 _ hw.constantApproximation
    φ φ.continuous φ.hasCompactSupport hφV
  have heq : (∫ x, φ x ∂smoothMeasure W u hw) = ∫ x, φ x ∂μ :=
    tendsto_nhds_unique tendsto_const_nhds hl
  rw [← PshLines.FirstPass.MongeAmpere.smoothMeasure_restrict hWU u hu hw] at heq
  change (∫ x in V, φ x ∂smoothMeasure U u hu) = _ at heq
  rw [← integral_indicator hVo.measurableSet] at heq
  have hind : V.indicator (φ : ComplexModel n → ℝ) = φ :=
    indicator_eq_self.mpr ((subset_tsupport φ).trans hφV)
  rwa [hind, eq_comm] at heq

/-- Smooth compatibility with the original oriented top-form measure in
the interleaved real coordinates. -/
theorem eq_map_d0TopMeasure_of_isLocalBedfordTaylorMeasure {n : ℕ}
    {U : Opens (ComplexModel n)} {u : E n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure U (u ∘ (complexCoordinates n).symm) μ)
    (hu : IsSmoothPshOn U (u ∘ (complexCoordinates n).symm)) :
    μ = Measure.map (complexCoordinates n)
      ((d0TopMeasure u).restrict ((complexCoordinates n) ⁻¹' (U : Set (ComplexModel n)))) :=
  (eq_smoothMeasure_of_isLocalBedfordTaylorMeasure hμ hu).trans
    (map_d0TopMeasure_restrict_eq_smoothMeasure U hu).symm

/-- The domain of the manuscript, expressed in complex Euclidean coordinates. -/
def complexUnitBall (n : ℕ) : Opens (ComplexModel n) :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

@[simp] theorem preimage_complexUnitBall (n : ℕ) :
    (complexCoordinates n) ⁻¹' (complexUnitBall n : Set (ComplexModel n)) = unitBall n := by
  ext x
  change dist (complexCoordinates n x) 0 < 1 ↔ dist x 0 < 1
  simp only [dist_zero_right, LinearIsometryEquiv.norm_map]

theorem eq_map_d0TopMeasure_unitBall {n : ℕ}
    {u : E n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure (complexUnitBall n) (u ∘ (complexCoordinates n).symm) μ)
    (hu : IsSmoothPshOn (complexUnitBall n) (u ∘ (complexCoordinates n).symm)) :
    μ = Measure.map (complexCoordinates n) ((d0TopMeasure u).restrict (unitBall n)) := by
  simpa only [preimage_complexUnitBall] using eq_map_d0TopMeasure_of_isLocalBedfordTaylorMeasure hμ hu

#print axioms isLocalBedfordTaylorMeasure_unique
#print axioms eq_map_d0TopMeasure_unitBall

end KEBall.BedfordTaylor
