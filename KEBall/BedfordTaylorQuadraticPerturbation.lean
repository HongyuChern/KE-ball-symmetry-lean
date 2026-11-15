import KEBall.BedfordTaylorCompactDifference
import KEBall.BedfordTaylorQuadraticDeterminant
import KEBall.BedfordTaylorScaling

/-!
# Quadratic perturbations of the Bedford–Taylor measure
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ComplexOrder ContDiff Distributions ENNReal Topology

namespace KEBall.BedfordTaylor

open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
open PshLines.Regularization.HolomorphicPullback (exists_decreasingMollifierApproximation)

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

theorem locallyBoundedPsh_add {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v) :
    IsLocallyBoundedPshOn Ω (fun x => u x + v x) := by
  refine ⟨?_, ?_⟩
  · simpa only [EReal.coe_add] using hu.1.add hv.1
  · intro x hx
    obtain ⟨U, hxU, hU, C, hC⟩ := hu.2 x hx
    obtain ⟨V, hxV, hV, D, hD⟩ := hv.2 x hx
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, inf_le_left.trans hU, C + D, fun y hy => ?_⟩
    exact (abs_add_le (u y) (v y)).trans (add_le_add (hC y hy.1) (hD y hy.2))

private theorem hessian_add_quadratic {u : ComplexModel n → ℝ} {x : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u x) (c : ℝ) :
    PshLines.FirstPass.MongeAmpere.complexHessian (fun y => u y + c * ‖y‖ ^ 2) x =
      PshLines.FirstPass.MongeAmpere.complexHessian u x + (c : ℂ) • 1 := by
  let q : ComplexModel n → ℝ := fun y => ‖y‖ ^ 2
  have hq : ContDiffAt ℝ 2 q x := (contDiff_norm_sq ℝ).contDiffAt
  change PshLines.FirstPass.MongeAmpere.complexHessian (u + c • q) x = _
  rw [PshLines.FirstPass.MongeAmpere.complexHessian_add hu (show ContDiffAt ℝ 2 (c • q) x from hq.const_smul c),
    PshLines.FirstPass.MongeAmpere.complexHessian_smul hq,
    show PshLines.FirstPass.MongeAmpere.complexHessian q x = 1 from complexHessian_norm_sq x]

private theorem smoothPsh_add_quadratic {u : ComplexModel n → ℝ}
    (hu : IsSmoothPshOn Ω u) {c : ℝ} (hc : 0 ≤ c) :
    IsSmoothPshOn Ω (fun x => u x + c * ‖x‖ ^ 2) := by
  apply isSmoothPshOn_of_coordinateHessian (hu.1.add (contDiffOn_const.mul (contDiff_norm_sq ℝ).contDiffOn))
  intro x hx
  rw [hessian_add_quadratic
    ((hu.1.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  exact (hu.2.2 x hx).add (Matrix.PosSemidef.one.smul (by exact_mod_cast hc))

theorem locallyBoundedPsh_add_quadratic {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {c : ℝ} (hc : 0 < c) :
    IsLocallyBoundedPshOn Ω (fun x => u x + c * ‖x‖ ^ 2) :=
  locallyBoundedPsh_add hu
    (isLocallyBoundedPshOn_of_isSmoothPshOn (smoothPsh_const_mul (isSmoothPshOn_norm_sq Ω) hc))

private theorem smoothMeasure_add_quadratic_ge (hn : 0 < n)
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn Ω u) {c : ℝ} (hc : 0 ≤ c) :
    smoothMeasure Ω u hu +
        ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * c ^ n) • volume.restrict (Ω : Set (ComplexModel n)) ≤
      smoothMeasure Ω (fun x => u x + c * ‖x‖ ^ 2) (smoothPsh_add_quadratic hu hc) := by
  unfold smoothMeasure
  rw [← withDensity_const, ← withDensity_add_right _ measurable_const]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  change ENNReal.ofReal (smoothDensity u x) + ENNReal.ofReal _ ≤ ENNReal.ofReal _
  rw [← ENNReal.ofReal_add (smoothDensity_nonneg (hu.2.2 x hx)) (by positivity),
    smoothDensity, smoothDensity, hessian_add_quadratic
      ((hu.1.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)), ← mul_add]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (det_re_add_scalar_one_ge hn (hu.2.2 x hx) hc) (by positivity))

/-- Adding a positive quadratic contributes at least its constant-density
Monge–Ampère measure, even for a locally bounded potential. -/
theorem topMeasure_add_quadratic_ge (hn : 0 < n)
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {c : ℝ} (hc : 0 < c) :
    topMeasure hu +
        ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * c ^ n) • volume.restrict (Ω : Set (ComplexModel n)) ≤
      topMeasure (locallyBoundedPsh_add_quadratic hu hc) := by
  let density := ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n * c ^ n)
  have hfin : density < ⊤ := ENNReal.ofReal_lt_top
  refine ambientMeasure_le_of_smooth_test (U := Ω) ?_ (topMeasure_compl _) ?_ ?_ ?_
  · rw [Measure.add_apply, topMeasure_compl hu, zero_add, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (Ω.isOpen.measurableSet.compl), compl_inter_self,
      measure_empty, mul_zero]
  · intro K hK hKΩ
    rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.add_lt_top.mpr ⟨topMeasure_finite_on_compact hu hK hKΩ,
      ENNReal.mul_lt_top hfin ((Measure.restrict_le_self (s := (Ω : Set (ComplexModel n)))
        (μ := volume) K).trans_lt hK.measure_lt_top)⟩
  · exact fun _ => topMeasure_finite_on_compact _
  · intro φ hφ
    obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
    let W : Opens (ComplexModel n) := ⟨V, hVo⟩
    have hrel : RelativelyCompactIn W Ω := ⟨hVc, hVΩ⟩
    let ψ : 𝓓(W, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩
    obtain ⟨p, hp⟩ := exists_decreasingMollifierApproximation hu hrel
    let hs := fun j => smoothPsh_add_quadratic (hp.1 j) hc.le
    have hanti (x : ComplexModel n) (hx : x ∈ W) :
        Antitone (fun j => p j x + c * ‖x‖ ^ 2) :=
      fun _ _ hij => add_le_add (hp.2.1 x hx hij) le_rfl
    have hlim (x : ComplexModel n) (hx : x ∈ W) :
        Tendsto (fun j => p j x + c * ‖x‖ ^ 2) atTop (𝓝 (u x + c * ‖x‖ ^ 2)) :=
      (hp.2.2 x hx).add_const _
    have huLim := (isLocalBedfordTaylorMeasure_top hu).2.2.2 W hrel |>.2
      p hp φ φ.continuous φ.hasCompactSupport hφV
    have hvLim := (isLocalBedfordTaylorMeasure_top (locallyBoundedPsh_add_quadratic hu hc)).2.2.2 W hrel |>.2
      (fun j x => p j x + c * ‖x‖ ^ 2) ⟨hs, hanti, hlim⟩
      φ φ.continuous φ.hasCompactSupport hφV
    have hφvol : Integrable (fun x => φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have hvol_eq : (∫ x, φ x ∂density • volume.restrict (W : Set (ComplexModel n))) =
        ∫ x, φ x ∂density • volume.restrict (Ω : Set (ComplexModel n)) := by
      rw [integral_smul_measure, integral_smul_measure]
      apply congrArg (fun a : ℝ => density.toReal • a)
      calc
        (∫ x in (W : Set (ComplexModel n)), φ x) = ∫ x, φ x :=
          setIntegral_eq_integral_of_forall_compl_eq_zero
            (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hφV h)))
        _ = ∫ x in (Ω : Set (ComplexModel n)), φ x :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero
            (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)))).symm
    rw [integral_add_measure (integrable_test_topMeasure hu φ) (hφvol.restrict.smul_measure hfin.ne)]
    apply le_of_tendsto_of_tendsto' (huLim.add_const _) hvLim
    intro j
    have hi {v : ComplexModel n → ℝ} (hv : IsSmoothPshOn W v) :
        Integrable (fun x => φ x) (smoothMeasure W v hv) := by
      rw [← topMeasure_eq_smoothMeasure hv]
      exact integrable_test_topMeasure _ ψ
    rw [← hvol_eq, ← integral_add_measure (hi (hp.1 j)) (hφvol.restrict.smul_measure hfin.ne)]
    exact integral_mono_measure (smoothMeasure_add_quadratic_ge hn (hp.1 j) hc.le)
      (Eventually.of_forall hφ) (hi (hs j))

end KEBall.BedfordTaylor
