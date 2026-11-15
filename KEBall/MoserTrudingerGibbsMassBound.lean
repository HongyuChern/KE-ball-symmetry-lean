import KEBall.MoserTrudingerFiberBound
import KEBall.CegrellSmoothFunctional
import KEBall.MoserTrudingerSmoothGibbs

/-!
# The entropy step from a mass estimate to the finite-energy functional
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn isSmoothPshOn_of_psh)

/-- Smooth solvability of the Dirichlet equation with Gibbs density on the unit ball. -/
def SmoothGibbsDirichletSolvable (n : ℕ) (γ : ℝ) : Prop :=
  ∀ (u : E n → ℝ), ContDiff ℝ ∞ u → (∀ x ∈ unitSphere n, u x = 0) →
    (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      ∀ x ∈ unitBall n, (complexHessian v x).det.re = gibbsDensity γ u x

private theorem d0TopMeasure_unitBall_eq_one_of_gibbs {n : ℕ} (hn : 0 < n)
    {u v : E n → ℝ} (hu : ContDiff ℝ ∞ u) {γ : ℝ}
    (hEq : ∀ x ∈ unitBall n, (complexHessian v x).det.re = gibbsDensity γ u x) :
    d0TopMeasure v (unitBall n) = 1 := by
  have hB : MeasurableSet (unitBall n) := measurableSet_ball
  have hZ := normalizingIntegral_pos_of_continuousOn hn hu.continuous.continuousOn γ
  have hp₀ (x : E n) : 0 ≤ gibbsDensity γ u x := div_nonneg (Real.exp_nonneg _) hZ.le
  have hp : ContinuousOn (gibbsDensity γ u) (closedUnitBall n) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hu.continuous.continuousOn)).div_const _
  have hpi : IntegrableOn (gibbsDensity γ u) (unitBall n) (volume0 n) :=
    hp.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) hB ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hm : (∫ x in unitBall n, gibbsDensity γ u x ∂volume0 n) = 1 := by
    unfold gibbsDensity
    rw [integral_div, ← normalizingIntegral, div_self hZ.ne']
  rw [d0TopMeasure_eq_density, withDensity_apply _ hB]
  calc
    _ = ∫⁻ x in unitBall n, ENNReal.ofReal (gibbsDensity γ u x) ∂volume0 n := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume0 n) hB] with x hx
      rw [hEq x hx]
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hpi (Eventually.of_forall hp₀), hm, ENNReal.ofReal_one]

/-- A Euclidean-volume mass bound applies to the normalized Gibbs
partition integral after scaling the potential. -/
theorem normalizingIntegral_le_of_smoothMass_bound {n : ℕ} (hn : 0 < n)
    {m C : ℝ≥0∞}
    (hBound : ∀ (q : ComplexModel n → ℝ) (hq : IsE0 (complexUnitBall n) q),
      ContDiff ℝ ∞ q → (∀ x ∈ sphere 0 1, q x = 0) → topMeasure hq.locallyBoundedPsh univ ≤ m →
      (∫⁻ x in complexUnitBall n, ENNReal.ofReal (Real.exp (-q x))) ≤ C)
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) {β : ℝ} (hβ : 0 < β)
    (hMass : ENNReal.ofReal (β ^ n) * d0TopMeasure v (unitBall n) ≤ m) :
    ENNReal.ofReal (normalizingIntegral β v) ≤ ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) * C := by
  let e := complexCoordinates n
  let q : ComplexModel n → ℝ := v ∘ e.symm
  let w (x : ComplexModel n) := β * q x
  have hNear : SmoothNear (closedUnitBall n) v := ⟨univ, isOpen_univ, subset_univ _, hv.contDiffOn⟩
  have hqC : ContDiff ℝ ∞ q := hv.comp e.symm.toContinuousLinearEquiv.contDiff
  have hq : IsE0 (complexUnitBall n) q := isE0_onBall_of_smooth_real_model hNear
    (fun x hx => (hvP x hx).posSemidef) hv0
  have hw := hq.const_mul hβ
  have hwC : ContDiff ℝ ∞ w := contDiff_const.mul hqC
  have hw0 (x : ComplexModel n) (hx : x ∈ sphere 0 1) : w x = 0 := by
    have he : e.symm x ∈ unitSphere n := mem_sphere_zero_iff_norm.mpr
      ((e.symm.norm_map x).trans (mem_sphere_zero_iff_norm.mp hx))
    change β * v (e.symm x) = 0
    rw [hv0 _ he, mul_zero]
  have hqS : IsSmoothPshOn (complexUnitBall n) q := isSmoothPshOn_of_psh hqC.contDiffOn hq.psh
  have hMass' : topMeasure hw.locallyBoundedPsh univ ≤ m := by
    rw [show topMeasure hw.locallyBoundedPsh = ENNReal.ofReal (β ^ n) • topMeasure hq.locallyBoundedPsh from
        topMeasure_const_mul hq.locallyBoundedPsh hβ, Measure.smul_apply, smul_eq_mul,
      show topMeasure hq.locallyBoundedPsh =
        Measure.map e ((d0TopMeasure v).restrict (unitBall n)) from topMeasure_eq_map_d0TopMeasure_unitBall hqS,
      Measure.map_apply e.continuous.measurable MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
    exact hMass
  have he := exponentialIntegral_realModelPotential hn hNear β
  change exponentialIntegral β (fun x => (q x : EReal)) = _ at he
  rw [exponentialIntegral_real_eq_lintegral_volume] at he
  exact he.symm.trans_le (mul_le_mul_right (hBound w hw hwC hw0 hMass') _)

set_option maxHeartbeats 900000 in
/-- The entropy step uses one smooth Gibbs-density Dirichlet solve for
each input. The remaining inputs are a mass bound and a subcritical margin. -/
theorem finiteEnergyFunctional_le_of_gibbsSolvability_and_massBound {n : ℕ} (hn : 0 < n)
    {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hγβ : γ * ((n : ℝ) / (n + 1)) ≤ β)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hBound : ∀ (q : ComplexModel n → ℝ) (hq : IsE0 (complexUnitBall n) q),
      ContDiff ℝ ∞ q → (∀ x ∈ sphere 0 1, q x = 0) →
      topMeasure hq.locallyBoundedPsh univ ≤ ENNReal.ofReal (β ^ n) →
      (∫⁻ x in complexUnitBall n, ENNReal.ofReal (Real.exp (-q x))) ≤ C)
    (hSolve : SmoothGibbsDirichletSolvable n γ)
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) :
    finiteEnergyFunctional γ hu ≤
      ((Real.log ((ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) * C).toReal) / γ : ℝ) : EReal) := by
  let K := ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) * C
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  apply finiteEnergyFunctional_le_of_smooth_bound hn hγ _ hu
  intro q hq hqC hqP
  let e := complexCoordinates n
  let p : E n → ℝ := q ∘ e
  have hpC : ContDiff ℝ ∞ p := hqC.comp e.toContinuousLinearEquiv.contDiff
  have hp0 (x : E n) (hx : x ∈ unitSphere n) : p x = 0 := by
    let B := (complexUnitBall n : Set (ComplexModel n))
    have hz : e x ∈ frontier B := by
      change e x ∈ frontier (ball (0 : ComplexModel n) 1)
      rw [frontier_ball _ one_ne_zero, mem_sphere_zero_iff_norm, e.norm_map]
      exact mem_sphere_zero_iff_norm.mp hx
    let : NeBot (𝓝[B] e x) := mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hz)
    exact tendsto_nhds_unique (hqC.continuous.continuousWithinAt (s := B) (x := e x)) (hq.boundary _ hz)
  have hqEq : p ∘ e.symm = q := by
    funext x
    simp only [p, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  have hpP (x : E n) (hx : x ∈ unitBall n) : (complexHessian p x).PosDef := by
    have hx' : e x ∈ complexUnitBall n := by
      change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
      simpa only [e, preimage_complexUnitBall] using hx
    rw [← complexHessian_coordinates hpC.contDiffAt, hqEq]
    exact hqP _ hx'
  obtain ⟨v, hvC, hv0, hvP, hvEq⟩ := hSolve p hpC hp0 hpP
  have hvMass := d0TopMeasure_unitBall_eq_one_of_gibbs hn hpC hvEq
  have hV := normalizingIntegral_le_of_smoothMass_bound hn hBound hvC hv0 hvP hβ (by rw [hvMass, mul_one])
  have hV₀ := normalizingIntegral_pos_of_continuousOn hn hvC.continuous.continuousOn β
  have hLog : Real.log (normalizingIntegral β v) ≤ Real.log K.toReal := by
    apply Real.log_le_log hV₀
    simpa only [ENNReal.toReal_ofReal hV₀.le] using ENNReal.toReal_mono hK hV
  have hvNear : SmoothNear (closedUnitBall n) v := ⟨univ, isOpen_univ, subset_univ _, hvC.contDiffOn⟩
  have hvE0 := isE0_onBall_of_smooth_real_model hvNear (fun x hx => (hvP x hx).posSemidef) hv0
  have hvneg (x : E n) (hx : x ∈ unitBall n) : v x ≤ 0 := by
    have hx' : e x ∈ complexUnitBall n := by
      change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
      simpa only [e, preimage_complexUnitBall] using hx
    have h := hvE0.nonpositive_unitBall hn (e x) hx'
    change v (e.symm (e x)) ≤ 0 at h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h
  have h := smoothFunctional_le_of_gibbs_mass_bound hn isOpen_univ (subset_univ _)
    hpC.contDiffOn hvC.contDiffOn hp0 hv0 hpP hvP hvneg hγ hγβ hvEq hLog
  have hpNear : SmoothNear (closedUnitBall n) p := ⟨univ, isOpen_univ, subset_univ _, hpC.contDiffOn⟩
  have hpE0 : IsE0 (complexUnitBall n) (p ∘ e.symm) := hqEq.symm ▸ hq
  have hEqF : finiteEnergyFunctional γ hq.isE1 = finiteEnergyFunctional γ hpE0.isE1 := by
    congr 1
    exact congrArg (fun v : ComplexModel n → ℝ => fun x => (v x : EReal)) hqEq.symm
  rw [hEqF, finiteEnergyFunctional_realModelPotential hn hpNear hpE0 γ, EReal.coe_le_coe_iff]
  rw [smoothFunctional, signedSmoothEnergy_eq isOpen_univ hpC.contDiffOn (subset_univ _) hpP] at h
  simpa only [neg_div, sub_eq_add_neg, add_comm, K] using h

end KEBall.MoserTrudinger
