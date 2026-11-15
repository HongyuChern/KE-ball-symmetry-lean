import KEBall.DirichletAnnularSmooth
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Local translations that leave the boundary data unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

private theorem complexHessian_comp_add_left {n : ℕ} (u : E n → ℝ) (a x : E n)
    (hu : ContDiffAt ℝ 2 u (a + x)) :
    complexHessian (fun y => u (a + y)) x = complexHessian u (a + x) := by
  have hv : ContDiffAt ℝ 2 (fun y => u (a + y)) x :=
    hu.comp x (contDiffAt_const.add contDiffAt_id)
  rw [← complexHessianOfRealBilinear_eq hv, ← complexHessianOfRealBilinear_eq hu]
  apply congrArg complexHessianOfRealBilinear
  ext b c
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, realHessian] using
    congrFun (congrArg DFunLike.coe (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := u) 2 a x))
      ![b, c]

private noncomputable def dirichletCenterBump (n : ℕ) : ContDiffBump (0 : E n) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- This family translates the potential near zero and agrees with it near
the sphere. -/
private noncomputable def dirichletCenterShift {n : ℕ} (v : E n → ℝ)
    (p : E n × E n) : ℝ :=
  v (p.2 + dirichletCenterBump n p.2 • p.1)

private theorem dirichletCenterShift_zero {n : ℕ} (v : E n → ℝ) (x : E n) :
    dirichletCenterShift v (0, x) = v x := by
  simp [dirichletCenterShift]

private theorem dirichletCenterShift_near_center {n : ℕ} (v : E n → ℝ)
    (h x : E n) (hx : ‖x‖ < 1 / 4) :
    (fun y => dirichletCenterShift v (h, y)) =ᶠ[𝓝 x] fun y => v (h + y) := by
  have hx' : x ∈ ball (0 : E n) (1 / 4) := by simpa only [mem_ball, dist_zero_right]
  filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
  have h₁ := (dirichletCenterBump n).one_of_mem_closedBall (ball_subset_closedBall hy)
  simp only [dirichletCenterShift, h₁, one_smul, add_comm]

private theorem dirichletCenterShift_near_sphere {n : ℕ} (v : E n → ℝ)
    (h x : E n) (hx : 1 / 2 < ‖x‖) :
    (fun y => dirichletCenterShift v (h, y)) =ᶠ[𝓝 x] v := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  have h₀ : dirichletCenterBump n y = 0 :=
    (dirichletCenterBump n).zero_of_le_dist (by change (1 : ℝ) / 2 ≤ dist y 0; rw [dist_zero_right]; exact hy.le)
  simp only [dirichletCenterShift, h₀, zero_smul, add_zero]

private theorem contDiff_dirichletCenterShift_arg (n : ℕ) :
    ContDiff ℝ ∞ (fun p : E n × E n => p.2 + dirichletCenterBump n p.2 • p.1) :=
  contDiff_snd.add (((dirichletCenterBump n).contDiff.comp contDiff_snd).smul contDiff_fst)

private theorem mapsTo_dirichletCenterShift_arg_closed {n : ℕ} {h : E n} (hh : ‖h‖ < 1 / 8) :
    MapsTo (fun x : E n => x + dirichletCenterBump n x • h) (closedUnitBall n) (closedUnitBall n) := by
  intro x hx
  by_cases hx' : ‖x‖ ≤ 1 / 2
  · rw [closedUnitBall, mem_closedBall, dist_zero_right]
    have hNorm : ‖dirichletCenterBump n x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg ((dirichletCenterBump n).nonneg)]
      exact (dirichletCenterBump n).le_one
    calc
      _ ≤ ‖x‖ + ‖dirichletCenterBump n x‖ * ‖h‖ := by
        rw [← norm_smul]
        exact norm_add_le _ _
      _ ≤ 1 / 2 + 1 * (1 / 8) := add_le_add hx' (mul_le_mul hNorm hh.le (norm_nonneg h) zero_le_one)
      _ ≤ 1 := by norm_num
  · have h₀ : dirichletCenterBump n x = 0 :=
      (dirichletCenterBump n).zero_of_le_dist (by change (1 : ℝ) / 2 ≤ dist x 0; rw [dist_zero_right]; exact le_of_lt (lt_of_not_ge hx'))
    simpa only [h₀, zero_smul, add_zero] using hx

private theorem contDiffOn_dirichletCenterShift_closed {n : ℕ} {h : E n} (hh : ‖h‖ < 1 / 8)
    {v : E n → ℝ} (hv : ContDiffOn ℝ 2 v (closedUnitBall n)) :
    ContDiffOn ℝ 2 (fun x => dirichletCenterShift v (h, x)) (closedUnitBall n) :=
  hv.comp (((contDiff_dirichletCenterShift_arg n).comp (contDiff_const.prodMk contDiff_id)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn
    (mapsTo_dirichletCenterShift_arg_closed hh)


private theorem centerShift_translatedArgument_mem_unitBall {n : ℕ} {h x : E n}
    (hh : ‖h‖ < 1 / 8) (hx : ‖x‖ < 1 / 4) : h + x ∈ unitBall n := by
  rw [unitBall, mem_ball, dist_zero_right]
  exact (norm_add_le _ _).trans_lt (by linarith)

private theorem contDiffAt_dirichletCenterShift {n : ℕ} {v : E n → ℝ}
    (hvS : ContDiffOn ℝ ∞ v (closedUnitBall n ∩ ({0} : Set (E n))ᶜ))
    {h x : E n} (hh : ‖h‖ < 1 / 8) (hx : 1 / 8 < ‖x‖) (hx' : ‖x‖ < 7 / 8) :
    ContDiffAt ℝ ∞ (dirichletCenterShift v) (h, x) := by
  let y := x + dirichletCenterBump n x • h
  have hSize : ‖dirichletCenterBump n x • h‖ < 1 / 8 := by
    rw [norm_smul, Real.norm_of_nonneg ((dirichletCenterBump n).nonneg)]
    exact (mul_le_of_le_one_left (norm_nonneg h) ((dirichletCenterBump n).le_one)).trans_lt hh
  have hNear : ‖y‖ < 1 := (norm_add_le _ _).trans_lt (by linarith)
  have hNotZero : y ≠ 0 := by
    intro he
    have h' : x = -(dirichletCenterBump n x • h) := eq_neg_of_add_eq_zero_left he
    have hNorm : ‖x‖ < 1 / 8 := by rw [h', norm_neg]; exact hSize
    exact (not_lt_of_gt hx) hNorm
  have hY : unitBall n ∩ ({0} : Set (E n))ᶜ ∈ 𝓝 y := by
    apply (isOpen_ball.inter isClosed_singleton.isOpen_compl).mem_nhds
    exact ⟨by simpa only [unitBall, mem_ball, dist_zero_right] using hNear,
      by simpa only [mem_compl_iff, mem_singleton_iff] using hNotZero⟩
  exact ((hvS.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)).contDiffAt hY).comp
    (h, x) (contDiff_dirichletCenterShift_arg n).contDiffAt


set_option maxHeartbeats 500000 in
private theorem contDiffAt_complexHessian_slice {n : ℕ} {F : E n × E n → ℝ}
    {p : E n × E n} (hF : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ ∞ F q) :
    ContDiffAt ℝ ∞ (fun q : E n × E n => complexHessian (fun x => F (q.1, x)) q.2) p := by
  let I : E n →L[ℝ] E n × E n := ContinuousLinearMap.inr ℝ (E n) (E n)
  have hOrder : (∞ : ℕ∞ω) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have h₂ := (hF.self_of_nhds.fderiv_right (m := ∞) hOrder).fderiv_right (m := ∞) hOrder
  let H (q : E n × E n) := fderiv ℝ (fderiv ℝ F) q
  have hR (a b : E n) :
      ContDiffAt ℝ ∞ (fun q => H q (I a) (I b)) p :=
    (h₂.clm_apply (contDiffAt_const (c := I a))).clm_apply (contDiffAt_const (c := I b))
  have hCoord (a b : E n) :
      ContDiffAt ℝ ∞ (fun q => (H q (I a) (I b) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (hR a b)
  have hAll := hF.eventually_nhds
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  let r := realDirection i
  let s := realDirection j
  let a := imagDirection i
  let b := imagDirection j
  have h := (((hCoord r s).add (hCoord a b)).add
    (((hCoord r b).sub (hCoord a s)).const_smul Complex.I)).const_smul ((4 : ℂ)⁻¹)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hAll] with q hqNear
  have hq := hqNear.self_of_nhds
  have hSlice : ContDiffAt ℝ ∞ (fun x : E n => F (q.1, x)) q.2 :=
    hq.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)
  have hOrder₂ : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  rw [complexHessian_real_entry_C2 (hSlice.of_le hOrder₂)]
  have hEq (u w : E n) :
      realHessian (fun x : E n => F (q.1, x)) q.2 u w = H q (I u) (I w) := by
    have hNear : ∀ᶠ y in 𝓝 q.2, DifferentiableAt ℝ F (q.1, y) := by
      have ht : Tendsto (fun y : E n => (q.1, y)) (𝓝 q.2) (𝓝 q) :=
        (continuous_const.prodMk continuous_id).continuousAt.tendsto
      exact (ht.eventually hqNear).mono fun _ h => h.differentiableAt (by simp)
    have hD : (fun y => fderiv ℝ (fun x : E n => F (q.1, x)) y) =ᶠ[𝓝 q.2]
        fun y => (fderiv ℝ F (q.1, y)).comp I := by
      filter_upwards [hNear] with y hy
      exact ((hy.hasFDerivAt).comp y (hasFDerivAt_prodMk_right q.1 y)).fderiv
    unfold realHessian
    rw [hD.fderiv_eq]
    have hH := (hq.fderiv_right (m := ∞) hOrder).differentiableAt (by simp)
    have hPartial : HasFDerivAt (fun y : E n => fderiv ℝ F (q.1, y)) (H q ∘L I) q.2 :=
      hH.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)
    have he := hPartial.clm_comp (hasFDerivAt_const I q.2)
    rw [he.fderiv]
    rw [ContinuousLinearMap.comp_zero, zero_add]
    rfl
  simp only [r, s, a, b, hEq, smul_eq_mul]


private noncomputable def centerDensityInnerBump (n : ℕ) : ContDiffBump (0 : E n) :=
  ⟨1 / 6, 1 / 5, by norm_num, by norm_num⟩

private noncomputable def centerDensityOuterBump (n : ℕ) : ContDiffBump (0 : E n) :=
  ⟨5 / 8, 3 / 4, by norm_num, by norm_num⟩

private noncomputable def dirichletCenterShiftDensity {n : ℕ} (v f : E n → ℝ)
    (p : E n × E n) : ℝ :=
  let a := centerDensityInnerBump n p.2
  let b := centerDensityOuterBump n p.2
  a * f (p.1 + p.2) +
    (b - a) * (complexHessian (fun y => dirichletCenterShift v (p.1, y)) p.2).det.re +
    (1 - b) * f p.2

private theorem centerDensityInnerBump_eq_one {n : ℕ} {x : E n} (hx : ‖x‖ ≤ 1 / 6) :
    centerDensityInnerBump n x = 1 :=
  (centerDensityInnerBump n).one_of_mem_closedBall (by
    change x ∈ closedBall 0 (1 / 6)
    rwa [mem_closedBall, dist_zero_right])

private theorem centerDensityOuterBump_eq_one {n : ℕ} {x : E n} (hx : ‖x‖ ≤ 5 / 8) :
    centerDensityOuterBump n x = 1 :=
  (centerDensityOuterBump n).one_of_mem_closedBall (by
    change x ∈ closedBall 0 (5 / 8)
    rwa [mem_closedBall, dist_zero_right])

private theorem centerDensityInnerBump_eq_zero {n : ℕ} {x : E n} (hx : 1 / 5 ≤ ‖x‖) :
    centerDensityInnerBump n x = 0 :=
  (centerDensityInnerBump n).zero_of_le_dist (by change (1 : ℝ) / 5 ≤ dist x 0; rwa [dist_zero_right])

private theorem centerDensityOuterBump_eq_zero {n : ℕ} {x : E n} (hx : 3 / 4 ≤ ‖x‖) :
    centerDensityOuterBump n x = 0 :=
  (centerDensityOuterBump n).zero_of_le_dist (by change (3 : ℝ) / 4 ≤ dist x 0; rwa [dist_zero_right])

private theorem contDiffAt_centerShiftDensity {n : ℕ} {v f : E n → ℝ}
    (hv : ContDiffOn ℝ ∞ v (closedUnitBall n ∩ ({0} : Set (E n))ᶜ))
    (hf : ContDiff ℝ ∞ f) {p : E n × E n} (hp : ‖p.1‖ < 1 / 8) :
    ContDiffAt ℝ ∞ (dirichletCenterShiftDensity v f) p := by
  by_cases h : 1 / 8 < ‖p.2‖ ∧ ‖p.2‖ < 7 / 8
  · have hOpen : IsOpen {q : E n × E n | ‖q.1‖ < 1 / 8 ∧ 1 / 8 < ‖q.2‖ ∧ ‖q.2‖ < 7 / 8} :=
      (isOpen_lt continuous_fst.norm continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd.norm).inter (isOpen_lt continuous_snd.norm continuous_const))
    have hSmooth : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ ∞ (dirichletCenterShift v) q := by
      filter_upwards [hOpen.mem_nhds ⟨hp, h⟩] with q hq
      exact contDiffAt_dirichletCenterShift hv hq.1 hq.2.1 hq.2.2
    have hH := contDiffAt_complexHessian_slice hSmooth
    have hDet : ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A.det.re) := by
      rw [← contDiffOn_univ]
      apply Complex.reCLM.contDiff.comp_contDiffOn
      exact contDiffOn_det_of_contDiffOn_entries (A := id) fun i j =>
        (contDiff_pi.mp (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Matrix (Fin n) (Fin n) ℂ)) i) j).contDiffOn
    have ha : ContDiffAt ℝ ∞ (fun q : E n × E n => centerDensityInnerBump n q.2) p :=
      ((centerDensityInnerBump n).contDiff.comp contDiff_snd).contDiffAt
    have hb : ContDiffAt ℝ ∞ (fun q : E n × E n => centerDensityOuterBump n q.2) p :=
      ((centerDensityOuterBump n).contDiff.comp contDiff_snd).contDiffAt
    have hF := (hf.comp (contDiff_fst.add contDiff_snd)).contDiffAt (x := p)
    exact ((ha.mul hF).add ((hb.sub ha).mul (hDet.contDiffAt.comp p hH))).add
      ((contDiffAt_const.sub hb).mul (hf.comp contDiff_snd).contDiffAt)
  · by_cases hx : ‖p.2‖ ≤ 1 / 8
    · have hEq : (fun q : E n × E n => f (q.1 + q.2)) =ᶠ[𝓝 p] dirichletCenterShiftDensity v f := by
        have hp' : ‖p.2‖ < 1 / 6 := hx.trans_lt (by norm_num)
        filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hp'] with q hq
        have hq' : ‖q.2‖ ≤ 5 / 8 := hq.le.trans (by norm_num)
        simp [dirichletCenterShiftDensity, centerDensityInnerBump_eq_one hq.le,
          centerDensityOuterBump_eq_one hq']
      exact (hf.comp (contDiff_fst.add contDiff_snd)).contDiffAt.congr_of_eventuallyEq hEq.symm
    · have hx' : 3 / 4 < ‖p.2‖ := (show (3 / 4 : ℝ) < 7 / 8 by norm_num).trans_le
        (le_of_not_gt fun hlt => h ⟨lt_of_not_ge hx, hlt⟩)
      have hEq : (fun q : E n × E n => f q.2) =ᶠ[𝓝 p] dirichletCenterShiftDensity v f := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd.norm).mem_nhds hx'] with q hq
        have hq' : 1 / 5 ≤ ‖q.2‖ := (show (1 / 5 : ℝ) ≤ 3 / 4 by norm_num).trans hq.le
        simp [dirichletCenterShiftDensity, centerDensityInnerBump_eq_zero hq',
          centerDensityOuterBump_eq_zero hq.le]
      exact (hf.comp contDiff_snd).contDiffAt.congr_of_eventuallyEq hEq.symm


private theorem dirichletCenterShiftDensity_eq_det {n : ℕ} {v f : E n → ℝ}
    (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    {h x : E n} (hh : ‖h‖ < 1 / 8) (hx : x ∈ unitBall n) :
    dirichletCenterShiftDensity v f (h, x) =
      (complexHessian (fun y => dirichletCenterShift v (h, y)) x).det.re := by
  let A := (complexHessian (fun y => dirichletCenterShift v (h, y)) x).det.re
  have hInner :
      centerDensityInnerBump n x * f (h + x) = centerDensityInnerBump n x * A := by
    by_cases hi : ‖x‖ < 1 / 4
    · have hY := centerShift_translatedArgument_mem_unitBall hh hi
      have hH := complexHessian_congr_of_eventuallyEq (dirichletCenterShift_near_center v h x hi)
      rw [complexHessian_comp_add_left v h x ((hv.mono ball_subset_closedBall).contDiffAt
        (isOpen_ball.mem_nhds hY))] at hH
      rw [show A = (complexHessian v (h + x)).det.re from congrArg (fun M => M.det.re) hH, show (complexHessian v (h + x)).det.re = f (h + x) from hEq hY]
    · rw [centerDensityInnerBump_eq_zero ((show (1 / 5 : ℝ) ≤ 1 / 4 by norm_num).trans (le_of_not_gt hi)),
        zero_mul, zero_mul]
  have hOuter :
      (1 - centerDensityOuterBump n x) * f x = (1 - centerDensityOuterBump n x) * A := by
    by_cases ho : 1 / 2 < ‖x‖
    · have hH := complexHessian_congr_of_eventuallyEq (dirichletCenterShift_near_sphere v h x ho)
      rw [show A = (complexHessian v x).det.re from congrArg (fun M => M.det.re) hH, show (complexHessian v x).det.re = f x from hEq hx]
    · rw [centerDensityOuterBump_eq_one ((le_of_not_gt ho).trans (by norm_num)), sub_self,
        zero_mul, zero_mul]
  change centerDensityInnerBump n x * f (h + x) +
    (centerDensityOuterBump n x - centerDensityInnerBump n x) * A +
      (1 - centerDensityOuterBump n x) * f x = A
  rw [hInner, hOuter]
  ring


/-- A globally smooth density family with the prescribed equation on
the ball for all small local translations. -/
private theorem exists_contDiff_dirichletCenterShift_density {n : ℕ} {v f : E n → ℝ}
    (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hvS : ContDiffOn ℝ ∞ v (closedUnitBall n ∩ ({0} : Set (E n))ᶜ))
    (hf : ContDiff ℝ ∞ f)
    (hEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n)) :
    ∃ ρ : E n × E n → ℝ, ContDiff ℝ ∞ ρ ∧
      ∀ h : E n, ‖h‖ < 1 / 16 → ∀ x ∈ unitBall n,
        ρ (h, x) = (complexHessian (fun y => dirichletCenterShift v (h, y)) x).det.re := by
  let χ : ContDiffBump (0 : E n) := ⟨1 / 16, 3 / 32, by norm_num, by norm_num⟩
  refine ⟨fun p => χ p.1 * dirichletCenterShiftDensity v f p, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : ‖p.1‖ < 1 / 8
    · exact (χ.contDiff.comp contDiff_fst).contDiffAt.mul (contDiffAt_centerShiftDensity hvS hf hp)
    · have hp' : 3 / 32 < ‖p.1‖ := (show (3 / 32 : ℝ) < 1 / 8 by norm_num).trans_le (le_of_not_gt hp)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_fst.norm).mem_nhds hp'] with q hq
      have h₀ : χ q.1 = 0 := χ.zero_of_le_dist (by
        change (3 : ℝ) / 32 ≤ dist q.1 0
        rw [dist_zero_right]
        exact hq.le)
      simp only [h₀, zero_mul]
  · intro h hh x hx
    have h₁ : χ h = 1 := χ.one_of_mem_closedBall (by
      change h ∈ closedBall 0 (1 / 16)
      rw [mem_closedBall, dist_zero_right]
      exact hh.le)
    change χ h * dirichletCenterShiftDensity v f (h, x) = _
    rw [h₁, one_mul]
    exact dirichletCenterShiftDensity_eq_det hv hEq (hh.trans (by norm_num)) hx


set_option maxHeartbeats 450000 in
private theorem eventually_centerShift_posDef {n : ℕ} {v : E n → ℝ}
    (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hvS : ContDiffOn ℝ ∞ v (closedUnitBall n ∩ ({0} : Set (E n))ᶜ))
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    ∀ᶠ h in 𝓝 (0 : E n), ∀ x ∈ unitBall n,
      (complexHessian (fun y => dirichletCenterShift v (h, y)) x).PosDef := by
  let K := {x : E n | 1 / 4 ≤ ‖x‖} ∩ closedBall (0 : E n) (1 / 2)
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)
  let H (p : E n × E n) := complexHessian (fun y => dirichletCenterShift v (p.1, y)) p.2
  let U := {p : E n × E n | ‖p.1‖ < 1 / 8 ∧ 1 / 8 < ‖p.2‖ ∧ ‖p.2‖ < 7 / 8}
  have hU : IsOpen U := (isOpen_lt continuous_fst.norm continuous_const).inter
    ((isOpen_lt continuous_const continuous_snd.norm).inter (isOpen_lt continuous_snd.norm continuous_const))
  have hHU : ContinuousOn H U := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply ContDiffAt.continuousAt (𝕜 := ℝ) (n := ∞)
    apply contDiffAt_complexHessian_slice
    filter_upwards [hU.mem_nhds hp] with q hq
    exact contDiffAt_dirichletCenterShift hvS hq.1 hq.2.1 hq.2.2
  let A : Set (Matrix (Fin n) (Fin n) ℂ) :=
    ⋃₀ {W | IsOpen W ∧ ∀ B ∈ W, Matrix.IsHermitian B → Matrix.PosDef B}
  have hA : IsOpen A := isOpen_sUnion (fun W hW => hW.1)
  have hBase : ({0} : Set (E n)) ×ˢ K ⊆ U ∩ H ⁻¹' A := by
    rintro ⟨h, x⟩ ⟨hh, hx⟩
    have he : h = 0 := hh
    subst h
    have hx' : ‖x‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_zero_right] using hx.2
    have hxU : x ∈ unitBall n := by
      rw [unitBall, mem_ball, dist_zero_right]
      exact hx'.trans_lt (by norm_num)
    refine ⟨⟨by simp, (by norm_num : (1 / 8 : ℝ) < 1 / 4).trans_le hx.1,
      hx'.trans_lt (by norm_num)⟩, ?_⟩
    have he : H (0, x) = complexHessian v x := by
      change complexHessian (fun y => dirichletCenterShift v (0, y)) x = _
      simp only [dirichletCenterShift_zero]
    obtain ⟨W, hW, hxW, hWP⟩ := exists_isOpen_hermitian_posDef_nhds (hvP x hxU)
    exact mem_sUnion.mpr ⟨W, ⟨hW, hWP⟩, he.symm ▸ hxW⟩
  obtain ⟨V, V', hV, _, h0V, hKV, hSub⟩ :
      ∃ V V' : Set (E n), IsOpen V ∧ IsOpen V' ∧ {0} ⊆ V ∧ K ⊆ V' ∧
        V ×ˢ V' ⊆ U ∩ H ⁻¹' A :=
    generalized_tube_lemma isCompact_singleton hK (hHU.isOpen_inter_preimage hU hA) hBase
  have hNear : ∀ᶠ h in 𝓝 (0 : E n), ‖h‖ < 1 / 8 := by
    have hBall : ∀ᶠ y in 𝓝 (0 : E n), y ∈ ball 0 (1 / 8) := ball_mem_nhds _ (by norm_num)
    exact hBall.mono fun y hy => by simpa only [mem_ball, dist_zero_right] using hy
  filter_upwards [hV.mem_nhds (h0V (mem_singleton 0)), hNear] with h hh hhNorm x hx
  by_cases hSmall : ‖x‖ < 1 / 4
  · have hY := centerShift_translatedArgument_mem_unitBall hhNorm hSmall
    rw [complexHessian_congr_of_eventuallyEq (dirichletCenterShift_near_center v h x hSmall),
      complexHessian_comp_add_left v h x ((hv.mono ball_subset_closedBall).contDiffAt
        (isOpen_ball.mem_nhds hY))]
    exact hvP _ hY
  · by_cases hBig : 1 / 2 < ‖x‖
    · rw [complexHessian_congr_of_eventuallyEq (dirichletCenterShift_near_sphere v h x hBig)]
      exact hvP x hx
    · have hxK : x ∈ K := ⟨le_of_not_gt hSmall, by
        rw [mem_closedBall, dist_zero_right]
        exact le_of_not_gt hBig⟩
      have hProd : (h, x) ∈ V ×ˢ V' := ⟨hh, hKV hxK⟩
      have hInter : (h, x) ∈ U ∩ H ⁻¹' A := hSub hProd
      have hHA : H (h, x) ∈ A := hInter.2
      obtain ⟨W, hW, hHW⟩ := mem_sUnion.mp hHA
      have hC : ContDiffAt ℝ 2 (fun y => dirichletCenterShift v (h, y)) x :=
        ((contDiffOn_dirichletCenterShift_closed hhNorm hv).mono ball_subset_closedBall).contDiffAt
          (isOpen_ball.mem_nhds hx)
      exact hW.2 _ hHW (complexHessian_isHermitian_of_C2 hC)


/-- Smoothness off the center and a smooth local inverse in a fixed
Sobolev space imply smoothness on the entire closed ball. -/
theorem contDiffOn_closedBall_infty_of_smooth_localInverse {n k : ℕ} (hn : 0 < n)
    {G : dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun _ ℝ) →
      dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ)}
    (T : dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ) →L[ℝ] C(ClosedBall n, ℝ))
    (hT : ∀ (z : dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun _ ℝ))
      (w : E n → ℝ), ContinuousOn w (closedUnitBall n) → w =ᵐ[ν[n]] z.val.1 →
        ∀ x : ClosedBall n, T z x = w x)
    {d : dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun _ ℝ)}
    (hG : ∀ᶠ q in 𝓝 d, ContDiffAt ℝ ∞ G q)
    (hSol : ∀ᶠ q in 𝓝 d, ∀ f : E n → ℝ, ContinuousOn f (unitBall n) → f =ᵐ[ν[n]] q.val.1 →
      ∃ w : E n → ℝ, ContDiffOn ℝ 2 w (closedUnitBall n) ∧
        (∀ x ∈ unitSphere n, w x = 0) ∧ (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
        EqOn (fun x => (complexHessian w x).det.re) f (unitBall n) ∧
        w =ᵐ[ν[n]] (G q).val.1)
    {v f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hvS : ContDiffOn ℝ ∞ v (closedUnitBall n ∩ ({0} : Set (E n))ᶜ))
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hvEq : EqOn (fun x => (complexHessian v x).det.re) f (unitBall n))
    (hd : d.val.1 =ᵐ[ν[n]] f) :
    ContDiffOn ℝ ∞ v (closedUnitBall n) := by
  obtain ⟨ρ, hρ, hρEq⟩ := exists_contDiff_dirichletCenterShift_density hv hvS hf hvEq
  have hSlice (h : E n) : ContDiff ℝ ∞ (fun x => ρ (h, x)) :=
    hρ.comp (contDiff_const.prodMk contDiff_id)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let q (h : E n) := dirichletSobolevJetOfSmooth (k := k) hn b (hSlice h)
  have hq : ContDiff ℝ ∞ q := contDiff_dirichletSobolevJetOfSmooth_family hn b hρ hSlice
  have hData (h : E n) : (q h).val.1 =ᵐ[ν[n]] fun x => ρ (h, x) :=
    dirichletSobolevJetOfSmooth_fst_ae hn b (hSlice h)
  have hq0 : q 0 = d := by
    apply dirichletSobolevJetGraph_fst_injective hn b
    apply Lp.ext
    filter_upwards [hData 0, hd, ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hX hD hx
    have he := hρEq 0 (by simp) x hx
    simp only [dirichletCenterShift_zero] at he
    exact hX.trans (he.trans ((hvEq hx).trans hD.symm))
  have hqT : Tendsto q (𝓝 0) (𝓝 d) := hq0 ▸ hq.continuous.continuousAt.tendsto
  let O : ClosedBall n := ⟨0, by simp [closedUnitBall]⟩
  let W (h : E n) := T (G (q h)) O
  have hW : ContDiffAt ℝ ∞ W 0 :=
    ((ContinuousMap.evalCLM ℝ O).comp T).contDiff.contDiffAt.comp 0
      ((hqT.eventually hG).self_of_nhds.comp 0 hq.contDiffAt)
  have hNear : ∀ᶠ h : E n in 𝓝 0, ‖h‖ < 1 / 16 := by
    have hBall : ∀ᶠ y in 𝓝 (0 : E n), y ∈ ball 0 (1 / 16) := ball_mem_nhds _ (by norm_num)
    exact hBall.mono fun y hy => by simpa only [mem_ball, dist_zero_right] using hy
  have hWeq : v =ᶠ[𝓝 (0 : E n)] W := by
    filter_upwards [hqT.eventually hSol, eventually_centerShift_posDef hv hvS hvP, hNear]
      with h hs hPos hh
    let w' (x : E n) := dirichletCenterShift v (h, x)
    obtain ⟨w, hw, hw0, hwP, hwEq, hwAE⟩ := hs (fun x => ρ (h, x))
      (hSlice h).continuous.continuousOn (hData h).symm
    have hw' : ContDiffOn ℝ 2 w' (closedUnitBall n) :=
      contDiffOn_dirichletCenterShift_closed (hh.trans (by norm_num)) hv
    have hw'0 (x : E n) (hx : x ∈ unitSphere n) : w' x = 0 := by
      have hNorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      have hBig : (1 / 2 : ℝ) < ‖x‖ := by rw [hNorm]; norm_num
      exact (dirichletCenterShift_near_sphere v h x hBig).self_of_nhds.trans (hv0 x hx)
    have hEqual := eqOn_of_det_eq_of_closedBall_C2 hn hw hw' hw0 hw'0 hwP hPos
      (fun x hx => (hwEq hx).trans (hρEq h hh x hx))
    have hV : w' 0 = v h := by
      have he := (dirichletCenterShift_near_center v h (0 : E n) (by simp)).self_of_nhds
      simpa only [add_zero] using he
    exact hV.symm.trans ((hEqual O.property).symm.trans (hT _ w hw.continuousOn hwAE O).symm)
  have hV₀ : ContDiffAt ℝ ∞ v 0 := hW.congr_of_eventuallyEq hWeq
  intro x hx
  by_cases h : x = 0
  · exact h ▸ hV₀.contDiffWithinAt
  · have hN : ({0} : Set (E n))ᶜ ∈ 𝓝 x :=
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa only [mem_compl_iff, mem_singleton_iff])
    exact (hvS x ⟨hx, mem_of_mem_nhds hN⟩).mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hN))

end KEBall
