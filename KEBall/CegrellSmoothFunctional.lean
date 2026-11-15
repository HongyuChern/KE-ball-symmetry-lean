import KEBall.CegrellExponential
import KEBall.CegrellRadialTests

/-!
# Agreement of the finite-energy functional with the smooth formulas
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn isSmoothPshOn_of_psh)

variable {n : ℕ}

/-- A real-coordinate potential regarded as an extended-real
potential in complex coordinates. -/
noncomputable abbrev realModelPotential (v : E n → ℝ) (z : ComplexModel n) : EReal :=
  (v ((complexCoordinates n).symm z) : EReal)

theorem exponentialIntegral_realModelPotential_of_continuousOn (hn : 0 < n) {v : E n → ℝ}
    (hv : ContinuousOn v (closedUnitBall n)) (γ : ℝ) :
    exponentialIntegral γ (realModelPotential v) = ENNReal.ofReal (normalizingIntegral γ v) := by
  have hc : ContinuousOn (fun x => Real.exp (-γ * v x)) (closedUnitBall n) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hv)
  have hi : IntegrableOn (fun x => Real.exp (-γ * v x)) (unitBall n) (volume0 n) :=
    hc.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) isOpen_ball.measurableSet
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  unfold exponentialIntegral normalizingIntegral
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet : MeasurableSet (unitBall n))] with x hx
  rw [finiteEnergyWeight, if_pos hx, realModelPotential, LinearIsometryEquiv.symm_apply_apply,
    ← expNeg_const_mul _ γ, ← EReal.coe_mul, expNeg_coe]
  ring_nf

theorem exponentialIntegral_realModelPotential (hn : 0 < n) {v : E n → ℝ}
    (hv : SmoothNear (closedUnitBall n) v) (γ : ℝ) :
    exponentialIntegral γ (realModelPotential v) = ENNReal.ofReal (normalizingIntegral γ v) :=
  exponentialIntegral_realModelPotential_of_continuousOn hn
    (fun _ hx => (hv.contDiffAt hx).continuousAt.continuousWithinAt) γ

theorem energy_realModelPotential (hn : 0 < n) {v : E n → ℝ}
    (hv : SmoothNear (closedUnitBall n) v)
    (hE0 : IsE0 (complexUnitBall n) (v ∘ (complexCoordinates n).symm)) :
    (energy hE0.isE1).toReal = smoothEnergy v := by
  let e := complexCoordinates n
  obtain ⟨U, _, hBU, hs⟩ := hv
  have hcont : ContDiffOn ℝ ∞ (v ∘ e.symm) (complexUnitBall n) := by
    apply hs.comp e.symm.toContinuousLinearEquiv.contDiff.contDiffOn
    intro z hz
    apply hBU
    apply ball_subset_closedBall
    change dist (e.symm z) 0 < 1
    rw [dist_zero_right, e.symm.norm_map]
    exact mem_ball_zero_iff.mp hz
  have hpsh : IsSmoothPshOn (complexUnitBall n) (v ∘ e.symm) :=
    isSmoothPshOn_of_psh hcont hE0.psh
  let μ := (d0TopMeasure v).restrict (unitBall n)
  have hM : topMeasure hE0.locallyBoundedPsh = μ.map e := topMeasure_eq_map_d0TopMeasure_unitBall hpsh
  have hmass : d0TopMeasure v (unitBall n) < ⊤ := by
    have h := hE0.finiteMass
    rw [hM, Measure.map_apply e.continuous.measurable MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ] at h
    exact h
  have hInt : Integrable (fun x => -v x) μ :=
    ((hs.continuousOn.mono hBU).neg).integrableOn_of_subset_isCompact
      (isCompact_closedBall _ _) isOpen_ball.measurableSet ball_subset_closedBall hmass.ne
  have hNonneg : 0 ≤ᵐ[μ] fun x => -v x := by
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet : MeasurableSet (unitBall n))] with x hx
    have hx' : e x ∈ complexUnitBall n := by
      change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
      rwa [preimage_complexUnitBall]
    have h := hE0.nonpositive_unitBall hn (e x) hx'
    change 0 ≤ -v x
    exact neg_nonneg.mpr (by simpa only [e, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply] using h)
  have he : MeasurableEmbedding (e : E n → ComplexModel n) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hm := he.lintegral_map (μ := μ) (fun z : ComplexModel n => ENNReal.ofReal (-(v ∘ e.symm) z))
  rw [energy_eq_boundedEnergy hn hE0, boundedEnergy, hM, hm]
  change (∫⁻ x, ENNReal.ofReal (-v (e.symm (e x))) ∂μ).toReal = _
  simp_rw [LinearIsometryEquiv.symm_apply_apply]
  exact (integral_eq_lintegral_of_nonneg_ae hNonneg hInt.aestronglyMeasurable).symm

theorem finiteEnergyFunctional_realModelPotential (hn : 0 < n) {v : E n → ℝ}
    (hv : SmoothNear (closedUnitBall n) v)
    (hE0 : IsE0 (complexUnitBall n) (v ∘ (complexCoordinates n).symm))
    (γ : ℝ) :
    finiteEnergyFunctional γ hE0.isE1 =
      ((Real.log (normalizingIntegral γ v) / γ - smoothEnergy v / (n + 1 : ℝ) : ℝ) : EReal) := by
  have hexp : exponentialIntegral γ (realModelPotential v) < ⊤ := by
    rw [exponentialIntegral_realModelPotential hn hv γ]
    exact ENNReal.ofReal_lt_top
  have hI : 0 ≤ normalizingIntegral γ v := integral_nonneg fun _ => (Real.exp_pos _).le
  change finiteEnergyFunctional γ (u := realModelPotential v) hE0.isE1 = _
  unfold finiteEnergyFunctional
  rw [if_neg hexp.ne, exponentialIntegral_realModelPotential hn hv γ,
    ENNReal.toReal_ofReal hI, energy_realModelPotential hn hv hE0]

theorem meanFieldSolution_memE0 {γ : ℝ} {v : E n → ℝ}
    (h : Paper20261016.IsMeanFieldSolution n γ v) :
    IsE0 (complexUnitBall n) (v ∘ (complexCoordinates n).symm) :=
  isE0_onBall_of_smooth_real_model h.2.1 (fun x hx => (h.2.2.1 x hx).posSemidef) h.2.2.2.1

end KEBall.MoserTrudinger
