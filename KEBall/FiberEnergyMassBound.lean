import KEBall.FiberEnergyCurvature
import KEBall.MoserTrudingerDisc

/-!
# From the fiber energy bound to the smooth product mass estimate
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Laplacian

namespace KEBall.MoserTrudinger

open BrezisMerle

/-- The integral of the full Hessian determinant with the product of the
two normalized ball volumes. -/
noncomputable def productHessianMass {n : ℕ} (u : E n × E 1 → ℝ) : ℝ :=
  ∫ w in unitBall 1, (∫ z in unitBall n, (productComplexHessian u z w).det.re ∂volume0 n) ∂volume0 1

theorem discMass_const_smul {f : E 1 → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) :
    discMass (c • f) = c * discMass f := by
  unfold discMass
  simp_rw [InnerProductSpace.laplacian_smul c hf.contDiffAt, smul_eq_mul, integral_const_mul]
  ring

/-- The disc mass of the fiber energy is precisely the product mass. -/
theorem discMass_fiberEnergy {n : ℕ} (hn : 0 < n) {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ w z, z ∈ unitSphere n → u (z, w) = 0)
    (hP : ∀ w ∈ unitBall 1, ∀ z ∈ unitBall n,
      (complexHessian (fun y => u (y, w)) z).PosDef) :
    discMass (fiberEnergy u) = productHessianMass u := by
  unfold discMass productHessianMass
  rw [setIntegral_volume0]
  have h : (∫ w in unitBall 1, Δ (fiberEnergy u) w) =
      4 * ∫ w in unitBall 1, (∫ z in unitBall n, (productComplexHessian u z w).det.re ∂volume0 n) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (show MeasurableSet (unitBall 1) from measurableSet_ball)
      (fun _ hw => laplacian_fiberEnergy hn hu h0 hP hw)
  rw [h]
  norm_num
  have hp := Real.pi_pos
  field_simp

private theorem continuous_normalizingIntegral_fiber {n : ℕ} (hn : 0 < n)
    {u : E n × E 1 → ℝ} (hu : ContDiff ℝ ∞ u) (γ : ℝ) :
    Continuous (fun w => normalizingIntegral γ (fun z => u (z, w))) := by
  have h : ContDiff ℝ ∞ (fun p : E 1 × E n => Real.exp (-γ * u (p.2, p.1))) :=
    (contDiff_const.mul (hu.comp (contDiff_snd.prodMk contDiff_fst))).exp
  exact (contDiff_fiberIntegral hn h).continuous

/-- The smooth fiber step of the Brezis–Merle–Demailly induction. The
mass uses the product normalization, so its coefficient is the same
coupling as the one used in the fiber functional. -/
theorem product_exponential_le_of_fiber_bound {n : ℕ} (hn : 0 < n) {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ w z, z ∈ unitSphere n → u (z, w) = 0)
    (hB : ∀ w ∈ unitSphere 1, ∀ z ∈ unitBall n, u (z, w) = 0)
    (hP : ∀ w ∈ unitBall 1, ∀ z ∈ unitBall n,
      (complexHessian (fun y => u (y, w)) z).PosDef)
    (hJoint : ∀ w ∈ unitBall 1, ∀ z ∈ unitBall n, (productComplexHessian u z w).PosSemidef)
    {γ C r : ℝ} (hγ : 0 < γ) (hr : 0 < r) (hr' : r < 1)
    (hm : γ * productHessianMass u ≤ r)
    (hF : ∀ w ∈ unitBall 1, smoothFunctional γ (fun z => u (z, w)) ≤ C / γ) :
    (∫ w in unitBall 1, normalizingIntegral γ (fun z => u (z, w)) ∂volume0 1) ≤
      Real.exp C * (4 / (1 - r)) := by
  let v := fiberEnergy u
  have hv : ContDiff ℝ ∞ v := fiberEnergy_contDiff hn hu
  have hv0 (w : E 1) (hw : w ∈ unitSphere 1) : v w = 0 := by
    change (∫ z in unitBall n, u (z, w) *
        (complexHessian (fun y => u (y, w)) z).det.re ∂volume0 n) / (n + 1 : ℝ) = 0
    have hI : (∫ z in unitBall n, u (z, w) *
        (complexHessian (fun y => u (y, w)) z).det.re ∂volume0 n) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with z hz
      simp [hB w hw z hz]
    rw [hI, zero_div]
  have hvΔ (w : E 1) (hw : w ∈ unitBall 1) : 0 ≤ Δ v w := by
    change 0 ≤ Δ (fiberEnergy u) w
    rw [laplacian_fiberEnergy hn hu h0 hP hw]
    apply mul_nonneg (by norm_num)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with z hz
    exact (RCLike.nonneg_iff.mp (hJoint w hw z hz).det_nonneg).1
  have hm' : discMass (γ • v) ≤ r := by
    rw [discMass_const_smul (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      show discMass v = productHessianMass u from discMass_fiberEnergy hn hu h0 hP]
    exact hm
  have hvBound := normalizingIntegral_disc_le_of_mass hv hv0 hvΔ hγ hr hr' hm'
  have hpoint (w : E 1) (hw : w ∈ unitBall 1) :
      normalizingIntegral γ (fun z => u (z, w)) ≤ Real.exp C * Real.exp (-γ * v w) := by
    have h := hF w hw
    change v w + Real.log (normalizingIntegral γ (fun z => u (z, w))) / γ ≤ C / γ at h
    have h' := mul_le_mul_of_nonneg_right h hγ.le
    rw [add_mul, div_mul_cancel₀ _ hγ.ne', div_mul_cancel₀ _ hγ.ne'] at h'
    have hU : ContinuousOn (fun z => u (z, w)) (closedUnitBall n) :=
      (hu.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    rw [← Real.exp_log (normalizingIntegral_pos_of_continuousOn hn hU γ), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hInt {f : E 1 → ℝ} (hf : Continuous f) :
      IntegrableOn f (unitBall 1) (volume0 1) :=
    hf.continuousOn.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall 1 (by decide)]; exact ENNReal.one_ne_top)
  have hLeft := hInt (continuous_normalizingIntegral_fiber hn hu γ)
  have hRight : IntegrableOn (fun w => Real.exp C * Real.exp (-γ * v w)) (unitBall 1) (volume0 1) :=
    hInt ((Real.continuous_exp.comp (hv.continuous.const_mul (-γ))).const_mul _)
  have h := setIntegral_mono_on hLeft hRight
    (show MeasurableSet (unitBall 1) from measurableSet_ball) hpoint
  rw [integral_const_mul, ← normalizingIntegral] at h
  exact h.trans (mul_le_mul_of_nonneg_left hvBound (Real.exp_nonneg _))

end KEBall.MoserTrudinger
