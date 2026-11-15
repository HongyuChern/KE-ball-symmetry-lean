import KEBall.DirichletPositiveMatrix
import KEBall.DirichletDeterminantComparison

/-! Comparison of classical C² solutions of the complex Monge–Ampère equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ComplexOrder ContDiff Matrix Topology

namespace KEBall

private theorem realHessian_nonpos_of_isLocalMax_C2 {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ 2 h x) (hmax : IsLocalMax h x) (v : E n) :
    realHessian h x v v ≤ 0 := by
  let γ : ℝ → E n := fun t => x + t • v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa only [γ, id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add x
  have hγ0 : γ 0 = x := by simp [γ]
  have ht : Tendsto γ (𝓝 0) (𝓝 x) := by
    simpa only [hγ0] using (hγ 0).continuousAt.tendsto
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y := by
    filter_upwards [(hh.of_le (m := 1) (by norm_num)).eventually (by simp)] with y hy
    exact hy.differentiableAt one_ne_zero
  have heq : deriv (fun t => h (γ t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ h (γ t) v) := by
    filter_upwards [ht.eventually hnear] with t htd
    exact (htd.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hdf := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hdγ : HasDerivAt (fun t => fderiv ℝ h (γ t) v)
      (realHessian h x v v) 0 := by
    have hd' : HasFDerivAt (fun y => fderiv ℝ h y v) ((realHessian h x).flip v) x := by
      simpa [realHessian] using hd
    have hdAt : HasFDerivAt (fun y => fderiv ℝ h y v) ((realHessian h x).flip v) (γ 0) := by
      simpa only [hγ0] using hd'
    exact hdAt.comp_hasDerivAt 0 (hγ 0)
  have hdd : deriv (deriv (fun t => h (γ t))) 0 = realHessian h x v v := by
    rw [heq.deriv_eq, hdγ.deriv]
  have hmaxγ : IsLocalMax (fun t => h (γ t)) 0 := by
    filter_upwards [ht.eventually hmax] with t ht'
    simpa only [hγ0] using ht'
  have hcont : ContinuousAt (fun t => h (γ t)) 0 := by
    have hc : ContinuousAt h (γ 0) := by simpa only [hγ0] using hh.continuousAt
    exact hc.comp (hγ 0).continuousAt
  exact hdd ▸ PoincareMT.LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax hmaxγ hcont

theorem realMetricForm_eq_average_hessian_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (v w : E n) :
    realMetricForm u x v w =
      (realHessian u x v w + realHessian u x (J v) (J w)) / 2 := by
  unfold realMetricForm
  simp only [complexHessian_real_entry_C2 hu, Complex.re_sum, Finset.mul_sum]
  rw [realBilinear_interleaved, realBilinear_interleaved]
  simp only [J_realIndex, J_imagIndex, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [complexCoord, Complex.mul_re, Complex.mul_im]
  ring

private theorem complexHessian_posSemidef_of_realHessian_nonneg_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (hR : ∀ v, 0 ≤ realHessian u x v v) :
    (complexHessian u x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨complexHessian_isHermitian_of_C2 hu, fun z => ?_⟩
  obtain ⟨v, hv⟩ := complexCoord_surjective (star z)
  have h := add_nonneg (hR v) (hR (J v))
  have hMetric : 0 ≤ realMetricForm u x v v := by
    rw [realMetricForm_eq_average_hessian_C2 hu]
    exact div_nonneg h (by norm_num)
  rw [realMetricForm_eq, hermitianRealification_apply, hv] at hMetric
  simp only [Pi.star_apply, star_star] at hMetric
  have hQ := nonneg_of_mul_nonneg_right hMetric (by norm_num : 0 < (2 : ℝ))
  have hRe : 0 ≤ (star z ⬝ᵥ (complexHessian u x *ᵥ z)).re := by
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc, mul_left_comm] using hQ
  exact RCLike.nonneg_iff.mpr
    ⟨hRe, (complexHessian_isHermitian_of_C2 hu).im_star_dotProduct_mulVec_self z⟩

private theorem realHessian_sub_C2 {n : ℕ} {u v : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    realHessian (u - v) x = realHessian u x - realHessian v x := by
  have h : (fun y => fderiv ℝ (u - v) y) =ᶠ[𝓝 x] fun y => fderiv ℝ u y - fderiv ℝ v y := by
    filter_upwards [(hu.of_le (m := 1) (by norm_num)).eventually (by simp),
      (hv.of_le (m := 1) (by norm_num)).eventually (by simp)] with y hy hy'
    exact fderiv_sub (hy.differentiableAt one_ne_zero) (hy'.differentiableAt one_ne_zero)
  rw [realHessian, h.fderiv_eq, fderiv_fun_sub
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)]
  rfl

private theorem complexHessian_sub_C2 {n : ℕ} {u v : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    complexHessian (u - v) x = complexHessian u x - complexHessian v x := by
  ext i j
  have hw : ContDiffAt ℝ 2 (u - v) x := hu.sub hv
  rw [Matrix.sub_apply, complexHessian_real_entry_C2 hw,
    complexHessian_real_entry_C2 hu, complexHessian_real_entry_C2 hv, realHessian_sub_C2 hu hv]
  simp only [sub_apply, Complex.ofReal_sub]
  ring

private theorem realHessian_const_smul_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (a : ℝ) :
    realHessian (a • u) x = a • realHessian u x := by
  have h : (fun y => fderiv ℝ (a • u) y) =ᶠ[𝓝 x] fun y => a • fderiv ℝ u y := by
    filter_upwards [(hu.of_le (m := 1) (by norm_num)).eventually (by simp)] with y hy
    exact ((hy.differentiableAt one_ne_zero).hasFDerivAt.const_smul a).fderiv
  rw [realHessian, h.fderiv_eq]
  exact ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt.const_smul a |>.fderiv

private theorem complexHessian_const_smul_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (a : ℝ) :
    complexHessian (a • u) x = (a : ℂ) • complexHessian u x := by
  ext i j
  have hw : ContDiffAt ℝ 2 (a • u) x := hu.const_smul a
  rw [Matrix.smul_apply, complexHessian_real_entry_C2 hw,
    complexHessian_real_entry_C2 hu, realHessian_const_smul_C2 hu a]
  simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- Equal positive determinant and zero boundary data determine a
classical C² solution uniquely on the closed ball. -/
theorem eqOn_of_det_eq_of_closedBall_C2 {n : ℕ} (hn : 0 < n) {u v : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (hv : ContDiffOn ℝ 2 v (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hEq : EqOn (fun x => (complexHessian u x).det.re)
      (fun x => (complexHessian v x).det.re) (unitBall n)) :
    EqOn u v (closedUnitBall n) := by
  have compare {f g : E n → ℝ}
      (hf : ContDiffOn ℝ 2 f (closedUnitBall n)) (hg : ContDiffOn ℝ 2 g (closedUnitBall n))
      (hf0 : ∀ x ∈ unitSphere n, f x = 0) (hg0 : ∀ x ∈ unitSphere n, g x = 0)
      (hfP : ∀ x ∈ unitBall n, (complexHessian f x).PosDef)
      (hfg : EqOn (fun x => (complexHessian f x).det.re)
        (fun x => (complexHessian g x).det.re) (unitBall n)) :
      ∀ x ∈ closedUnitBall n, f x ≤ g x := by
    have hLe (t : ℝ) (ht : 1 < t) : ∀ x ∈ closedUnitBall n, t * f x ≤ g x := by
      let w : E n → ℝ := t • f - g
      have hw : ContDiffOn ℝ 2 w (closedUnitBall n) := (hf.const_smul t).sub hg
      obtain ⟨x, hx, hMax⟩ := (isCompact_closedBall (0 : E n) 1).exists_isMaxOn
        (show (closedUnitBall n).Nonempty from ⟨0, by simp [closedUnitBall]⟩) hw.continuousOn
      have hNorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
      rcases hNorm.lt_or_eq with hlt | heq
      · exfalso
        have hxB : x ∈ unitBall n := mem_ball_zero_iff.mpr hlt
        have hxN := isOpen_ball.mem_nhds hxB
        have hxF := (hf.mono ball_subset_closedBall).contDiffAt hxN
        have hxG := (hg.mono ball_subset_closedBall).contDiffAt hxN
        have hLocal : IsLocalMax w x := hMax.isLocalMax (mem_of_superset hxN ball_subset_closedBall)
        have hxW : ContDiffAt ℝ 2 w x := (hxF.const_smul t).sub hxG
        have htF : ContDiffAt ℝ 2 (t • f) x := hxF.const_smul t
        have hW' : ContDiffAt ℝ 2 (g - t • f) x := hxG.sub htF
        have hSemi : (complexHessian (g - t • f) x).PosSemidef := by
          apply complexHessian_posSemidef_of_realHessian_nonneg_C2 hW'
          intro y
          have hh := realHessian_nonpos_of_isLocalMax_C2 hxW hLocal y
          change realHessian (t • f - g) x y y ≤ 0 at hh
          rw [realHessian_sub_C2 htF hxG, sub_apply, sub_apply] at hh
          rw [realHessian_sub_C2 hxG htF, sub_apply, sub_apply]
          linarith only [hh]
        rw [complexHessian_sub_C2 hxG htF, complexHessian_const_smul_C2 hxF] at hSemi
        let A := (t : ℂ) • complexHessian f x
        have ht0 : 0 < t := zero_lt_one.trans ht
        have hA : A.PosDef := by
          exact (hfP x hxB).smul (show 0 < (t : ℂ) from RCLike.pos_iff.mpr ⟨ht0, rfl⟩)
        have hDet := BedfordTaylor.det_re_add_ge hn hSemi hA
        have hMono : A.det.re ≤ (complexHessian g x).det.re := by
          rw [sub_add_cancel] at hDet
          have hNonneg := (RCLike.nonneg_iff.mp hSemi.det_nonneg).1
          exact (le_add_of_nonneg_left hNonneg).trans hDet
        have hScale : A.det.re = t ^ n * (complexHessian f x).det.re := by
          rw [show A = (t : ℂ) • complexHessian f x from rfl, Matrix.det_smul]
          rw [Fintype.card_fin]
          change (((t : ℂ) ^ n) * (complexHessian f x).det).re = _
          rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have htN : 1 < t ^ n := one_lt_pow₀ ht hn.ne'
        have hStrict := mul_lt_mul_of_pos_right htN (posDef_det_re_pos (hfP x hxB))
        rw [one_mul, ← hScale] at hStrict
        exact (hStrict.trans_le hMono).ne (hfg hxB)
      · have hxS : x ∈ unitSphere n := mem_sphere_zero_iff_norm.mpr heq
        intro y hy
        have h := hMax hy
        change t * f y - g y ≤ t * f x - g x at h
        rw [hf0 x hxS, hg0 x hxS, mul_zero, sub_zero] at h
        exact sub_nonpos.mp h
    intro x hx
    have hT : Tendsto (fun t : ℝ => t * f x) (𝓝[>] (1 : ℝ)) (𝓝 (f x)) := by
      have h : Tendsto (fun t : ℝ => t) (𝓝[>] (1 : ℝ)) (𝓝 1) := nhdsWithin_le_nhds
      simpa only [one_mul] using h.mul_const (f x)
    exact le_of_tendsto hT (Filter.Eventually.mono self_mem_nhdsWithin fun t ht => hLe t ht x hx)
  intro x hx
  exact le_antisymm (compare hu hv hu0 hv0 huP hEq x hx)
    (compare hv hu hv0 hu0 hvP hEq.symm x hx)

end KEBall
