import KEBall.SecondGreen
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# The Euclidean Green inequality for a zero-boundary potential

The boundary contribution is nonpositive when the test function is
nonpositive on the sphere.
-/

set_option autoImplicit false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff ENNReal Gradient Laplacian Pointwise RealInnerProductSpace Topology

namespace KEBall.BrezisMerle

private theorem gradient_contDiff {n : ℕ} {u : E n → ℝ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (∇ u) := by
  change ContDiff ℝ 1 (fun x => (toDual ℝ (E n)).symm (fderiv ℝ u x))
  exact (toDual ℝ (E n)).symm.toContinuousLinearEquiv.contDiff.comp
    (hu.fderiv_right (by norm_num))

private theorem divergence_gradient {n : ℕ} {u : E n → ℝ} (hu : ContDiff ℝ 2 u)
    (x : E n) : euclideanDivergence (∇ u) x = Δ u x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun _ _)]
  unfold euclideanDivergence
  apply Finset.sum_congr rfl
  intro i _
  let e := EuclideanSpace.basisFun (Fin (2 * n)) ℝ i
  have hcoords (y : E n) : (∇ u y) i = fderiv ℝ u y e := by
    rw [← EuclideanSpace.inner_basisFun_real, inner_gradient_left]
  simp only [hcoords, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_clm_apply ((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
    (differentiableAt_const e)]
  simp [e, ContinuousLinearMap.flip_apply]

theorem continuous_laplacian {n : ℕ} {u : E n → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (Δ u) := by
  have heq := funext (divergence_gradient hu)
  rw [← heq]
  exact euclideanDivergence_continuous (gradient_contDiff hu)

private theorem boundary_normal_nonneg {n : ℕ} {u : E n → ℝ} (hu : ContDiff ℝ 2 u)
    (hneg : ∀ x ∈ closedUnitBall n, u x ≤ 0) (hzero : ∀ x ∈ unitSphere n, u x = 0)
    {x : E n} (hx : x ∈ unitSphere n) : 0 ≤ inner ℝ x (∇ u x) := by
  have hxc : x ∈ closedUnitBall n := sphere_subset_closedBall hx
  have hm : IsMaxOn u (closedUnitBall n) x := by
    intro y hy
    rw [hzero x hx]
    exact hneg y hy
  have hs : segment ℝ x (0 : E n) ⊆ closedUnitBall n :=
    (convex_closedBall (0 : E n) 1).segment_subset hxc (mem_closedBall_self zero_le_one)
  have hc := sub_mem_posTangentConeAt_of_segment_subset hs
  rw [zero_sub] at hc
  have h := hm.localize.hasFDerivWithinAt_nonpos
    ((hu.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt) hc
  rw [map_neg, neg_nonpos] at h
  rw [real_inner_comm (∇ u x) x, inner_gradient_left]
  exact h

/-- Integration by parts twice and the sign of the outward derivative. -/
theorem integral_mul_laplacian_le {n : ℕ} (hn : 0 < n)
    {u w : E n → ℝ} (hu : ContDiff ℝ 2 u) (hw : ContDiff ℝ 2 w)
    (hneg : ∀ x ∈ closedUnitBall n, u x ≤ 0) (hzero : ∀ x ∈ unitSphere n, u x = 0)
    (hwneg : ∀ x ∈ unitSphere n, w x ≤ 0) :
    (∫ x in unitBall n, w x * Δ u x) ≤ ∫ x in unitBall n, u x * Δ w x := by
  let F : E n → E n := fun x => w x • (∇ u x) - u x • (∇ w x)
  have hgU := gradient_contDiff hu
  have hgW := gradient_contDiff hw
  have hF : ContDiff ℝ 1 F :=
    ((hw.of_le (by norm_num)).smul hgU).sub ((hu.of_le (by norm_num)).smul hgW)
  have hd (x : E n) : euclideanDivergence F x = w x * Δ u x - u x * Δ w x := by
    have hu' := hu.differentiable (by norm_num) x
    have hw' := hw.differentiable (by norm_num) x
    have hgU' := hgU.differentiable one_ne_zero x
    have hgW' := hgW.differentiable one_ne_zero x
    change euclideanDivergence
      (fun y => w y • (∇ u y) - u y • (∇ w y)) x = _
    rw [euclideanDivergence_sub (V := fun y => w y • ∇ u y)
      (W := fun y => u y • ∇ w y) (hw'.smul hgU') (hu'.smul hgW'),
      euclideanDivergence_smul hw' hgU', euclideanDivergence_smul hu' hgW',
      divergence_gradient hu, divergence_gradient hw,
      ← inner_gradient_left, ← inner_gradient_left,
      real_inner_comm (∇ w x) (∇ u x)]
    ring
  have hi (v g : E n → ℝ) (hv : ContDiff ℝ 2 v) (hg : ContDiff ℝ 2 g) :
      IntegrableOn (fun x => v x * Δ g x) (unitBall n) := by
    have hc : Continuous (fun x => v x * Δ g x) := by
      simp_rw [← divergence_gradient hg]
      exact hv.continuous.mul (euclideanDivergence_continuous (gradient_contDiff hg))
    exact (hc.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : E n) 1)).mono_set ball_subset_closedBall
  have hflux := integral_unitBall_divergence hn hF
  simp_rw [hd] at hflux
  rw [integral_sub (hi w u hw hu) (hi u w hu hw)] at hflux
  apply sub_nonpos.mp
  rw [hflux]
  apply integral_nonpos
  intro x
  have h := boundary_normal_nonneg hu hneg hzero x.2
  simp only [F, inner_sub_right, real_inner_smul_right, hzero _ x.2, zero_mul, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg (hwneg _ x.2) h

/-- A smooth logarithmic pole, nonpositive at distance at most two. -/
noncomputable def regularizedLog (ε : ℝ) (z x : E 1) : ℝ :=
  Real.log (‖x - z‖ ^ 2 + ε) - Real.log (4 + ε)

theorem regularizedLog_smooth {ε : ℝ} (hε : 0 < ε) (z : E 1) :
    ContDiff ℝ 2 (regularizedLog ε z) := by
  have h : ContDiff ℝ 2 (fun x : E 1 => ‖x - z‖ ^ 2 + ε) :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).add contDiff_const
  exact (h.log fun x => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)).sub contDiff_const

theorem regularizedLog_nonpos {ε : ℝ} (hε : 0 < ε) {z x : E 1}
    (hx : ‖x - z‖ ≤ 2) : regularizedLog ε z x ≤ 0 := by
  apply sub_nonpos.mpr
  exact Real.log_le_log (by positivity) (by nlinarith [norm_nonneg (x - z)])

private theorem fderiv_squared_distance_add (ε : ℝ) (z x : E 1) :
    HasFDerivAt (fun y => ‖y - z‖ ^ 2 + ε) (2 • innerSL ℝ (x - z)) x := by
  have h : HasFDerivAt (fun y : E 1 => y - z) (ContinuousLinearMap.id ℝ _) x :=
    (hasFDerivAt_id x).sub_const z
  simpa using (h.norm_sq.add_const ε)

private theorem regularizedLog_gradient {ε : ℝ} (hε : 0 < ε) (z x : E 1) :
    ∇ (regularizedLog ε z) x = (2 / (‖x - z‖ ^ 2 + ε)) • (x - z) := by
  have hq : 0 < ‖x - z‖ ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have h := ((fderiv_squared_distance_add ε z x).log hq.ne').sub_const (Real.log (4 + ε))
  apply (toDual ℝ (E 1)).injective
  rw [toDual_gradient]
  unfold regularizedLog
  rw [h.fderiv, map_smul]
  ext v
  simp only [smul_apply, smul_eq_mul, toDual_apply_apply, innerSL_apply_apply]
  ring

/-- The ordinary Laplacian of the smooth logarithmic pole. -/
theorem laplacian_regularizedLog {ε : ℝ} (hε : 0 < ε) (z x : E 1) :
    Δ (regularizedLog ε z) x = 4 * ε / (‖x - z‖ ^ 2 + ε) ^ 2 := by
  let q : E 1 → ℝ := fun y => ‖y - z‖ ^ 2 + ε
  let c : E 1 → ℝ := fun y => 2 / q y
  let V : E 1 → E 1 := fun y => y - z
  have hq : 0 < q x := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have hc := ((hasDerivAt_const (x := q x) (2 : ℝ)).div (hasDerivAt_id (q x)) hq.ne')
    |>.comp_hasFDerivAt x (fderiv_squared_distance_add ε z x)
  have hV : DifferentiableAt ℝ V x := differentiableAt_id.sub_const z
  have hdiv : euclideanDivergence V x = 2 := by
    unfold euclideanDivergence
    have hcoord (i : Fin 2) : HasFDerivAt (fun y : E 1 => V y i)
        (EuclideanSpace.proj i : E 1 →L[ℝ] ℝ) x := by
      change HasFDerivAt (fun y : E 1 => y i - z i) _ x
      exact (EuclideanSpace.proj i : E 1 →L[ℝ] ℝ).hasFDerivAt.sub_const (z i)
    simp only [fun i => (hcoord i).fderiv]
    change (∑ i : Fin 2, ((EuclideanSpace.basisFun (Fin 2) ℝ) i) i) = _
    simp [EuclideanSpace.basisFun_apply]
  have hgrad : (∇ (regularizedLog ε z)) = fun y => c y • V y :=
    funext (regularizedLog_gradient hε z)
  rw [← divergence_gradient (regularizedLog_smooth hε z), hgrad,
    euclideanDivergence_smul (f := c) hc.differentiableAt hV, hdiv]
  change c x * 2 + _ = _
  have hc' : fderiv ℝ c x = ((0 * q x - 2 * 1) / q x ^ 2) • (2 • innerSL ℝ (x - z)) :=
    hc.fderiv
  rw [hc']
  simp only [c, V, zero_mul, mul_one, zero_sub, smul_apply,
    smul_eq_mul, innerSL_apply_apply, real_inner_self_eq_norm_sq]
  dsimp [q] at hq ⊢
  field_simp
  ring

/-- The Laplacian of the regularized logarithm divided by `4π`. -/
noncomputable def logLaplacianKernel (ε : ℝ) (z x : E 1) : ℝ :=
  ε / (Real.pi * (‖x - z‖ ^ 2 + ε) ^ 2)

theorem logLaplacianKernel_eq {ε : ℝ} (hε : 0 < ε) (z x : E 1) :
    logLaplacianKernel ε z x = Δ (regularizedLog ε z) x / (4 * Real.pi) := by
  rw [laplacian_regularizedLog hε, logLaplacianKernel]
  have hp := Real.pi_pos
  field_simp

theorem logLaplacianKernel_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (Function.uncurry (logLaplacianKernel ε)) := by
  have h : Continuous (fun p : E 1 × E 1 => Real.pi * (‖p.2 - p.1‖ ^ 2 + ε) ^ 2) := by
    fun_prop
  exact continuous_const.div h fun p => by positivity

theorem logLaplacianKernel_nonneg {ε : ℝ} (hε : 0 ≤ ε) (z x : E 1) :
    0 ≤ logLaplacianKernel ε z x := by unfold logLaplacianKernel; positivity

private theorem integral_logLaplacianKernel_unitBall {ε : ℝ} (hε : 0 < ε) :
    (∫ x in unitBall 1, logLaplacianKernel ε 0 x) = 1 / (1 + ε) := by
  have h := integral_unitBall_divergence (n := 1) (by decide)
    (gradient_contDiff (regularizedLog_smooth hε (0 : E 1)))
  simp_rw [divergence_gradient (regularizedLog_smooth hε _)] at h
  have hs (x : Sphere 1) : inner ℝ x.1 (∇ (regularizedLog ε 0) x.1) = 2 / (1 + ε) := by
    have hx : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    rw [regularizedLog_gradient hε, sub_zero, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
  simp_rw [hs] at h
  rw [integral_const, measureReal_def, sphereMeasure_univ 1 (by decide)] at h
  norm_num [ENNReal.toReal_ofReal, Real.pi_pos.le] at h
  calc
    _ = (∫ x in unitBall 1, Δ (regularizedLog ε 0) x) / (4 * Real.pi) := by
      simp_rw [logLaplacianKernel_eq hε]
      rw [integral_div]
    _ = _ := by
      rw [h]
      have hp := Real.pi_pos
      field_simp
      norm_num

theorem integral_logLaplacianKernel_ball {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (z : E 1) :
    (∫ x in ball z r, logLaplacianKernel ε z x) = r ^ 2 / (r ^ 2 + ε) := by
  have himage : (fun x : E 1 => z + x) '' ball 0 r = ball z r := by
    exact vadd_ball_zero r z
  rw [← himage, (measurePreserving_add_left (volume : Measure (E 1)) z).setIntegral_image_emb
    (MeasurableEquiv.addLeft z).measurableEmbedding]
  have hshift (x : E 1) : logLaplacianKernel ε z (z + x) = logLaplacianKernel ε 0 x := by
    simp [logLaplacianKernel, add_sub_cancel_left]
  simp_rw [hshift]
  have hscale := Measure.setIntegral_comp_smul_of_pos (volume : Measure (E 1))
    (logLaplacianKernel ε 0) (unitBall 1) hr
  have hdim : Module.finrank ℝ (E 1) = 2 := finrank_E 1
  simp only [hdim, show r • unitBall 1 = ball 0 r from smul_unitBall_of_pos hr,
    smul_eq_mul] at hscale
  have hpoint (x : E 1) :
      logLaplacianKernel ε 0 (r • x) = (r ^ 2)⁻¹ * logLaplacianKernel (ε / r ^ 2) 0 x := by
    simp only [logLaplacianKernel, sub_zero, norm_smul, Real.norm_of_nonneg hr.le]
    have hp := Real.pi_pos
    have hq : 0 < (r * ‖x‖) ^ 2 + ε := by positivity
    have hq' : 0 < ‖x‖ ^ 2 + ε / r ^ 2 := by positivity
    field_simp
  simp_rw [hpoint] at hscale
  rw [integral_const_mul, mul_right_inj' (inv_ne_zero (pow_ne_zero _ hr.ne')),
    integral_logLaplacianKernel_unitBall (by positivity : 0 < ε / r ^ 2)] at hscale
  rw [← hscale]
  field_simp

/-- The normalized Laplacians of the regularized poles converge to the
point mass at every interior point of the unit disc. -/
theorem tendsto_integral_logLaplacianKernel {u : E 1 → ℝ} (hu : Continuous u)
    {z : E 1} (hz : z ∈ unitBall 1)
    {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k) (hε₀ : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in unitBall 1, logLaplacianKernel (ε k) z x * u x) atTop (𝓝 (u z)) := by
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  have hInt : IntegrableOn u (unitBall 1) :=
    (hu.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E 1) 1)).mono_set ball_subset_closedBall
  have hPeak : Tendsto (fun k => ∫ x in ball z r, logLaplacianKernel (ε k) z x) atTop (𝓝 1) := by
    simp_rw [integral_logLaplacianKernel_ball (hε _) hr]
    have h : Tendsto (fun k => r ^ 2 / (r ^ 2 + ε k)) atTop (𝓝 (r ^ 2 / (r ^ 2 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add hε₀) (by positivity)
    simpa [pow_ne_zero 2 hr.ne'] using h
  have hUniform (W : Set (E 1)) (hW : IsOpen W) (hzW : z ∈ W) :
      TendstoUniformlyOn (fun k => logLaplacianKernel (ε k) z) 0 atTop (unitBall 1 \ W) := by
    obtain ⟨d, hd, hdW⟩ := Metric.isOpen_iff.mp hW z hzW
    rw [Metric.tendstoUniformlyOn_iff]
    intro b hb
    filter_upwards [((tendsto_order.1 hε₀).2 (b * (Real.pi * (d ^ 2) ^ 2)) (by positivity))]
      with k hk x hx
    have hdist : d ≤ ‖x - z‖ := by
      have h : x ∉ ball z d := fun hx' => hx.2 (hdW hx')
      simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using h
    rw [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (logLaplacianKernel_nonneg (hε k).le z x)]
    have he := hε k
    apply (div_lt_iff₀ (by positivity : 0 < Real.pi * (‖x - z‖ ^ 2 + ε k) ^ 2)).mpr
    refine hk.trans_le ?_
    gcongr
    exact (pow_le_pow_left₀ hd.le hdist 2).trans (le_add_of_nonneg_right (hε k).le)
  exact tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto measurableSet_ball
    measurableSet_ball hrB (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hr))
    (measure_ball_lt_top.ne)
    (Eventually.of_forall fun k x _ => logLaplacianKernel_nonneg (hε k).le z x)
    hUniform hPeak (Eventually.of_forall fun k =>
      ((logLaplacianKernel_continuous (hε k)).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    hInt hu.continuousAt.continuousWithinAt

end KEBall.BrezisMerle
