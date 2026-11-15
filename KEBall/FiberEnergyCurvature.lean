import KEBall.FiberEnergyDiscDerivative
import KEBall.FiberEnergyDeterminant

/-!
# The smooth fiber energy curvature identity on a ball times a disc
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Laplacian Topology

namespace KEBall.MoserTrudinger

private theorem integrableOn_fiber_of_continuous {n : ℕ} (hn : 0 < n)
    {V : Type*} [NormedAddCommGroup V] {f : E n → V} (hf : Continuous f) :
    IntegrableOn f (unitBall n) (volume0 n) :=
  hf.continuousOn.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
    measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)

private theorem continuous_realHessian_discSlice {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (w a : E 1) :
    Continuous (fun z => realHessian (fun y => u (z, y)) w a a) := by
  let L := ContinuousLinearMap.inr ℝ (E n) (E 1)
  have h2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hE (z : E n) : realHessian (fun y => u (z, y)) w a a =
      fderiv ℝ (fderiv ℝ u) (z, w) (0, a) (0, a) := by
    have h := PshLines.realHessian_comp_affine (hu.of_le h2) L (z, 0) w a a
    have he (y : E 1) : ((z, 0) : E n × E 1) + L y = (z, y) := by simp [L]
    simp only [he, PshLines.realHessian_eq_fderiv] at h
    exact h
  simp_rw [hE]
  have hD' : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hD'.fderiv_right (by simp)
  exact ((hD.continuous.comp (continuous_id.prodMk continuous_const)).clm_apply
    continuous_const).clm_apply continuous_const

/-- The disc Laplacian of the signed fiber energy equals four times the
fiber integral of the determinant of the full complex Hessian. -/
theorem laplacian_fiberEnergy_of_eventually_posDef {n : ℕ} (hn : 0 < n) {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ w z, z ∈ unitSphere n → u (z, w) = 0)
    {w : E 1} (hP : ∀ᶠ w' in 𝓝 w, ∀ z ∈ unitBall n,
      (complexHessian (fun y => u (y, w')) z).PosDef) :
    Δ (fiberEnergy u) w =
      4 * ∫ z in unitBall n, (productComplexHessian u z w).det.re ∂volume0 n := by
  have hPw := hP.self_of_nhds
  let f : E n → ℝ := fun z => u (z, w)
  let R : E n → ℝ := fun z => discDirectionalDerivative u (realDirection 0) (z, w)
  let S : E n → ℝ := fun z => discDirectionalDerivative u (imagDirection 0) (z, w)
  let A (z : E n) := (complexHessian f z).det.re
  let HR (z : E n) := realHessian (fun y => u (z, y)) w (realDirection 0) (realDirection 0)
  let HS (z : E n) := realHessian (fun y => u (z, y)) w (imagDirection 0) (imagDirection 0)
  let Δu (z : E n) := Δ (fun y => u (z, y)) w
  let G (g : E n → ℝ) (z : E n) := g z * cofactorContraction f g z
  let Q (g h : E n → ℝ) := cofactorGradientContraction f g h
  let μ := (volume0 n).restrict (unitBall n)
  have hf : ContDiff ℝ ∞ f := hu.comp (contDiff_id.prodMk contDiff_const)
  have hR : ContDiff ℝ ∞ R :=
    (discDirectionalDerivative_contDiff hu (realDirection 0)).comp (contDiff_id.prodMk contDiff_const)
  have hS : ContDiff ℝ ∞ S :=
    (discDirectionalDerivative_contDiff hu (imagDirection 0)).comp (contDiff_id.prodMk contDiff_const)
  have hzero (a : E 1) (z : E n) (hz : z ∈ unitSphere n) :
      discDirectionalDerivative u a (z, w) = 0 := by
    have hu' := hu.differentiable (by simp) (z, w)
    have h := (hu'.hasFDerivAt.comp w (hasFDerivAt_prodMk_right z w)).fderiv
    have he : (fun y : E 1 => u (z, y)) = 0 := funext fun y => h0 y z hz
    change fderiv ℝ (fun y : E 1 => u (z, y)) w = _ at h
    rw [he, fderiv_zero] at h
    exact (congrFun (congrArg DFunLike.coe h) a).symm
  have hR0 : ∀ z ∈ unitSphere n, R z = 0 := hzero _
  have hS0 : ∀ z ∈ unitSphere n, S z = 0 := hzero _
  have hA : Continuous A :=
    Complex.continuous_re.comp
      (contDiffOn_univ.mp (matrixField_det_contDiffOn (complexHessian_contDiffOn isOpen_univ hf.contDiffOn))).continuous
  have hHR : Integrable (fun z => HR z * A z) μ :=
    integrableOn_fiber_of_continuous hn ((continuous_realHessian_discSlice hu w _).mul hA)
  have hHS : Integrable (fun z => HS z * A z) μ :=
    integrableOn_fiber_of_continuous hn ((continuous_realHessian_discSlice hu w _).mul hA)
  have hG (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) : Integrable (G g) μ :=
    integrable_mul_contraction hn isOpen_univ (subset_univ _) hf.contDiffOn hg.contDiffOn hg.contDiffOn
  have hΔEq : Δu = fun z => HR z + HS z :=
    funext fun z => BrezisMerle.laplacian_eq_realHessian_disc (fun y => u (z, y)) w
  have hBase : Integrable (fun z => Δu z * A z) μ := by
    rw [hΔEq]
    simp only [add_mul]
    exact hHR.add hHS
  have hQ (g h : E n → ℝ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
      Integrable (Q g h) μ :=
    integrableOn_fiber_of_continuous hn (continuous_cofactorGradientContraction hf hg hh)
  have hQre (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : ∀ z ∈ unitSphere n, g z = 0) :
      (∫ z, (Q g g z).re ∂μ) = -(∫ z, G g z ∂μ) := by
    change (∫ z, RCLike.re (Q g g z) ∂μ) = _
    rw [integral_re (hQ g g hg hg)]
    have h := integral_cofactorGradientContraction hn hf hg hg hPw hg0
    change (∫ z, Q g g z ∂μ) = -(∫ z, ((G g z : ℝ) : ℂ) ∂μ) at h
    rw [h, integral_complex_ofReal]
    simp
  have hQim (g h : E n → ℝ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
      (hg0 : ∀ z ∈ unitSphere n, g z = 0) :
      (∫ z, (Q g h z).im ∂μ) = 0 := by
    change (∫ z, RCLike.im (Q g h z) ∂μ) = _
    rw [integral_im (hQ g h hg hh)]
    have he := integral_cofactorGradientContraction hn hf hg hh hPw hg0
    change (∫ z, Q g h z ∂μ) =
      -(∫ z, ((g z * cofactorContraction f h z : ℝ) : ℂ) ∂μ) at he
    rw [he, integral_complex_ofReal]
    simp
  have hE : Δ (fiberEnergy u) w =
      (∫ z, Δu z * A z ∂μ) + (∫ z, G R z ∂μ) + (∫ z, G S z ∂μ) := by
    rw [BrezisMerle.laplacian_eq_realHessian_disc,
      realHessian_fiberEnergy_of_eventually_posDef hn hu h0 w (realDirection 0) hP,
      realHessian_fiberEnergy_of_eventually_posDef hn hu h0 w (imagDirection 0) hP]
    change (∫ z, HR z * A z + G R z ∂μ) + (∫ z, HS z * A z + G S z ∂μ) = _
    rw [integral_add hHR (hG R hR), integral_add hHS (hG S hS), hΔEq]
    simp only [add_mul]
    rw [integral_add hHR hHS]
    ring
  have hDet : 4 * (∫ z in unitBall n, (productComplexHessian u z w).det.re ∂volume0 n) =
      ∫ z, Δu z * A z - (Q R R z).re - (Q S S z).re + (Q S R z).im - (Q R S z).im ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball)
    intro z hz
    dsimp only
    rw [productComplexHessian_det_re hu z w (hPw z hz)]
    dsimp only [Δu, A, Q, R, S, f]
    ring
  have hRR : Integrable (fun z => (Q R R z).re) μ := (hQ R R hR hR).re
  have hSS : Integrable (fun z => (Q S S z).re) μ := (hQ S S hS hS).re
  have hSR : Integrable (fun z => (Q S R z).im) μ := (hQ S R hS hR).im
  have hRS : Integrable (fun z => (Q R S z).im) μ := (hQ R S hR hS).im
  have h1 : Integrable (fun z => Δu z * A z - (Q R R z).re) μ := hBase.sub hRR
  have h2 : Integrable (fun z => Δu z * A z - (Q R R z).re - (Q S S z).re) μ := h1.sub hSS
  have h3 : Integrable (fun z => Δu z * A z - (Q R R z).re - (Q S S z).re + (Q S R z).im) μ :=
    h2.add hSR
  rw [hE, hDet, integral_sub h3 hRS, integral_add h2 hSR, integral_sub h1 hSS,
    integral_sub hBase hRR, hQre R hR hR0, hQre S hS hS0,
    hQim S R hS hR hS0, hQim R S hR hS hR0]
  ring

theorem laplacian_fiberEnergy {n : ℕ} (hn : 0 < n) {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ w z, z ∈ unitSphere n → u (z, w) = 0)
    (hP : ∀ w ∈ unitBall 1, ∀ z ∈ unitBall n,
      (complexHessian (fun y => u (y, w)) z).PosDef)
    {w : E 1} (hw : w ∈ unitBall 1) :
    Δ (fiberEnergy u) w =
      4 * ∫ z in unitBall n, (productComplexHessian u z w).det.re ∂volume0 n :=
  laplacian_fiberEnergy_of_eventually_posDef hn hu h0
    (Filter.Eventually.mono (isOpen_ball.mem_nhds hw) hP)

end KEBall.MoserTrudinger
