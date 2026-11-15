import KEBall.BedfordTaylorLocallyBoundedMonotone
import KEBall.BedfordTaylorQuadraticTaylorModel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Identifying the top measure from a bounded limit of smooth densities
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (IsLocallyBoundedPshOn IsDecreasingApproximation smoothMeasure smoothDensity smoothDensity_nonneg)

variable {n : ℕ} {W : Opens (ComplexModel n)}

theorem exists_smoothDensity_bound_of_boundedHessian (C : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ComplexModel n → ℝ) (x : ComplexModel n),
      ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C → |smoothDensity u x| ≤ D := by
  let T := ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ
  let _ : ProperSpace T := FiniteDimensional.proper ℝ T
  let d (A : T) := (n.factorial : ℝ) / Real.pi ^ n * (complexHessianOfBilinear A).det.re
  have hd : Continuous d := continuous_const.mul
    (Complex.continuous_re.comp continuous_complexHessianOfBilinear.matrix_det)
  have hcompact : IsCompact (closedBall (0 : T) C) := isCompact_closedBall _ _
  obtain ⟨D, hD⟩ := (hcompact.image hd.abs).bddAbove
  refine ⟨max D 0, le_max_right _ _, fun u x hx => ?_⟩
  have hmem : fderiv ℝ (fderiv ℝ u) x ∈ closedBall (0 : T) C := by
    exact mem_closedBall.mpr ((dist_zero_right (fderiv ℝ (fderiv ℝ u) x : T)).trans_le hx)
  have hle := hD ⟨fderiv ℝ (fderiv ℝ u) x, hmem, rfl⟩
  rw [smoothDensity, complexHessian_eq_ofBilinear]
  exact hle.trans (le_max_left _ _)

/-- A bounded almost-everywhere density limit of the decreasing smooth
approximation is the density of its actual Bedford–Taylor top measure. -/
theorem topMeasure_eq_withDensity_of_smoothDensity_limit
    {v d : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn W v)
    {q : ℕ → ComplexModel n → ℝ} (hq : IsDecreasingApproximation W v q)
    {D : ℝ} (hBound : ∀ j x, x ∈ W → |smoothDensity (q j) x| ≤ D)
    (hLim : ∀ᵐ x ∂volume.restrict (W : Set (ComplexModel n)),
      Tendsto (fun j => smoothDensity (q j) x) atTop (𝓝 (d x))) :
    topMeasure hv = (volume.restrict (W : Set (ComplexModel n))).withDensity (fun x => ENNReal.ofReal (d x)) := by
  let μ := volume.restrict (W : Set (ComplexModel n))
  let ν := μ.withDensity (fun x => ENNReal.ofReal (d x))
  have hAEW : ∀ᵐ x ∂μ, x ∈ W := ae_restrict_mem W.isOpen.measurableSet
  have hm (j : ℕ) : AEMeasurable (smoothDensity (q j)) μ :=
    (continuousOn_smoothDensity (hq.1 j).1).aemeasurable W.isOpen.measurableSet
  have hd : AEMeasurable d μ := aemeasurable_of_tendsto_metrizable_ae atTop hm hLim
  have hnonneg (j : ℕ) : ∀ᵐ x ∂μ, 0 ≤ smoothDensity (q j) x :=
    hAEW.mono fun x hx => smoothDensity_nonneg ((hq.1 j).2.2 x hx)
  have hdn : ∀ᵐ x ∂μ, 0 ≤ d x := by
    filter_upwards [hLim, hAEW] with x hx hxW
    exact ge_of_tendsto hx (Eventually.of_forall fun j => smoothDensity_nonneg ((hq.1 j).2.2 x hxW))
  have hdB : ∀ᵐ x ∂μ, |d x| ≤ D := by
    filter_upwards [hLim, hAEW] with x hx hxW
    exact le_of_tendsto hx.abs (Eventually.of_forall fun j => hBound j x hxW)
  have hνcompl : ν (W : Set (ComplexModel n))ᶜ = 0 := by
    unfold ν μ
    rw [withDensity_apply _ W.isOpen.measurableSet.compl,
      Measure.restrict_restrict W.isOpen.measurableSet.compl]
    simp
  have hνle : ν ≤ ENNReal.ofReal D • μ := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hdB] with x hx
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hx)
  have hνfin (K : Set (ComplexModel n)) (hK : IsCompact K) : ν K < ⊤ := by
    apply (hνle K).trans_lt
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((Measure.restrict_le_self K).trans_lt hK.measure_lt_top)
  apply ambientMeasure_eq_of_smooth_test (topMeasure_compl hv) hνcompl
    (fun _ hK hKW => topMeasure_finite_on_compact hv hK hKW)
    (fun K hK _ => hνfin K hK)
  intro φ
  have h₁ := tendsto_topMeasure_of_decreasing hv
    (fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hq.1 j)) hq.2.1 hq.2.2
    φ φ.continuous φ.hasCompactSupport φ.tsupport_subset
  have h₂ : Tendsto (fun j => ∫ x, smoothDensity (q j) x * φ x ∂μ) atTop
      (𝓝 (∫ x, d x * φ x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => D * |φ x|)
    · exact fun j => ((hm j).mul φ.continuous.measurable.aemeasurable).aestronglyMeasurable
    · exact ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).abs.const_mul D).restrict
    · intro j
      filter_upwards [hAEW] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hBound j x hx) (abs_nonneg _)
    · filter_upwards [hLim] with x hx
      exact hx.mul_const _
  have heqDensity {f : ComplexModel n → ℝ} (hf : AEMeasurable f μ) (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) :
      (∫ x, φ x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) = ∫ x, f x * φ x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hf.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hfn] with x hx
    rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  have he (j : ℕ) :
      (∫ x, φ x ∂topMeasure (isLocallyBoundedPshOn_of_isSmoothPshOn (hq.1 j))) =
        ∫ x, smoothDensity (q j) x * φ x ∂μ := by
    rw [topMeasure_eq_smoothMeasure (hq.1 j), smoothMeasure]
    exact heqDensity (hm j) (hnonneg j)
  simp_rw [he] at h₁
  exact (tendsto_nhds_unique h₁ h₂).trans (heqDensity hd hdn).symm

end KEBall.BedfordTaylor
