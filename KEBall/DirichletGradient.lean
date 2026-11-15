import KEBall.CegrellDirichletBarrier
import KEBall.EulerLaplacian

/-!
# Linearization and first-order estimates for the smooth Dirichlet equation
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

open KEBallProbe

/-- Taking a fixed directional derivative preserves smoothness on open sets. -/
theorem contDiffOn_directionalDerivative {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (v : E n) :
    ContDiffOn ℝ ∞ (fun y => fderiv ℝ u y v) U :=
  (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- The complex Hessian commutes with differentiation in a fixed real direction. -/
theorem complexHessian_directionalDerivative {n : ℕ} {u : E n → ℝ}
    {U : Set (E n)} (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    {x : E n} (hx : x ∈ U) (v : E n) (i j : Fin n) :
    complexHessian (fun y => fderiv ℝ u y v) x i j =
      fderiv ℝ (fun y => complexHessian u y i j) x v := by
  let w (y : E n) := fderiv ℝ u y v
  have hw := (contDiffOn_directionalDerivative hU hu v).contDiffAt (hU.mem_nhds hx)
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hD (a b : E n) : realHessian w x a b = realThirdDerivative u x v a b := by
    have heq : (fun y => fderiv ℝ w y b) =ᶠ[𝓝 x] fun y => realHessian u y b v := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact fderiv_firstDerivative_apply (hu.contDiffAt (hU.mem_nhds hy)) b v
    rw [← fderiv_firstDerivative_apply hw, heq.fderiv_eq, fderiv_realHessian_apply huAt,
      realThirdDerivative_symm23 hU hu hx a b v, realThirdDerivative_symm12 huAt a v b]
  rw [complexHessian_real_entry hw, fderiv_complexHessian_entry hU hu hx]
  simp only [show (fun y => fderiv ℝ u y v) = w from rfl, hD]

/-- Differentiating the prescribed smooth positive determinant in a constant
direction gives the linearized Dirichlet equation for that directional derivative. -/
theorem complexLaplacian_directionalDerivative_eq_logDensity {n : ℕ} {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ unitBall n) (v : E n) :
    complexLaplacian u (fun y => fderiv ℝ u y v) x =
      fderiv ℝ (fun y => Real.log (f y)) x v := by
  obtain ⟨U, hU, hsub, huU⟩ := hu
  have hxU := hsub (ball_subset_closedBall hx)
  have hp := huP x hx
  have hfpos : 0 < f x := (hEq x hx) ▸ posDef_det_re_pos hp
  have hunit := hp.isUnit
  have hdetUnit : IsUnit (complexHessian u x).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hF := (hf.contDiffAt (ball_subset_closedBall hx)).differentiableAt (by simp)
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y => complexHessian u y i j) x :=
    ((complexHessian_contDiffOn hU huU i j).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have heq : (fun y => (complexHessian u y).det) =ᶠ[𝓝 x] fun y => (f y : ℂ) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    rw [posDef_det_eq_ofReal_re (huP y hy), hEq y hy]
  have hContract := adjugate_contraction_eq_det_mul (complexHessian u x)
    (fun i j => fderiv ℝ (fun y => complexHessian u y i j) x v) hdetUnit
  have hCalc : (f x : ℂ) *
      (∑ i : Fin n, ∑ j : Fin n, inverseCoefficient u x i j *
        complexHessian (fun y => fderiv ℝ u y v) x i j) = (fderiv ℝ f x v : ℂ) := by
    simp_rw [complexHessian_directionalDerivative hU huU hxU v]
    rw [← show (complexHessian u x).det = (f x : ℂ) from heq.self_of_nhds]
    unfold inverseCoefficient
    rw [← hContract]
    have hd := rd_det_field hG v
    unfold rd at hd
    rw [← hd]
    change fderiv ℝ (fun y => (complexHessian u y).det) x v = _
    rw [heq.fderiv_eq]
    exact rd_ofReal hF v
  have hr := congrArg Complex.re hCalc
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  change f x * complexLaplacian u (fun y => fderiv ℝ u y v) x = fderiv ℝ f x v at hr
  rw [(hF.hasFDerivAt.log hfpos.ne').fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [← hr, ← mul_assoc, inv_mul_cancel₀ hfpos.ne', one_mul]

/-- A strict linearized subsolution is bounded above by its boundary values. -/
theorem le_boundary_bound_of_complexLaplacian_pos {n : ℕ} {u w : E n → ℝ}
    (hw : SmoothNear (closedUnitBall n) w)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hL : ∀ x ∈ unitBall n, 0 < complexLaplacian u w x)
    {C : ℝ} (hC : ∀ x ∈ unitSphere n, w x ≤ C) :
    ∀ x ∈ closedUnitBall n, w x ≤ C := by
  have hW : ContinuousOn w (closedUnitBall n) :=
    fun x hx => (hw.contDiffAt hx).continuousAt.continuousWithinAt
  have hne : (closedUnitBall n).Nonempty := ⟨0, by simp [closedUnitBall]⟩
  obtain ⟨x, hx, hxmax⟩ := (isCompact_closedBall (0 : E n) 1).exists_isMaxOn hne hW
  have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  rcases hx'.lt_or_eq with hlt | heq
  · have hxB : x ∈ unitBall n := mem_ball_zero_iff.mpr hlt
    have hMax := hxmax.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hxB) ball_subset_closedBall)
    exact False.elim ((hL x hxB).not_ge
      (complexLaplacian_nonpos_of_isLocalMax (huP x hxB) (hw.contDiffAt hx) hMax))
  · exact fun y hy => (hxmax hy).trans (hC x (mem_sphere_zero_iff_norm.mpr heq))

/-- A global first-derivative bound for the smooth zero-boundary solution with
fixed positive density, in terms of the density bounds and the log-density derivative. -/
theorem norm_fderiv_le_of_dirichlet_det {n : ℕ} (hn : 0 < n) {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {a b M : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 0 ≤ M)
    (hDensity : ∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n)
    (hLog : ∀ x ∈ unitBall n, ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ M) :
    ∀ x ∈ closedUnitBall n, ‖fderiv ℝ u x‖ ≤ 2 * b + ((M + 1) / n) * b := by
  have hBound := Cegrell.quadratic_and_boundarySlope_bounds hn hu (fun x hx => (huP x hx).posSemidef)
    hu0 ha hb (fun x hx => hEq x hx ▸ hDensity x hx)
  have hSlope (v : E n) (hv : ‖v‖ = 1) (x : E n) (hx : x ∈ unitSphere n) :
      |fderiv ℝ u x v| ≤ 2 * b := by
    have hInner := abs_real_inner_le_norm x v
    rw [mem_sphere_zero_iff_norm.mp hx, hv, one_mul] at hInner
    obtain ⟨h₁, h₂⟩ := hBound.2 x hx
    have hPos : 0 ≤ 2 * boundarySlope u x := mul_nonneg (by norm_num) (ha.le.trans h₁)
    rw [sphere_fderiv_normal hu hu0 hx v, abs_mul, abs_of_nonneg hPos]
    exact (mul_le_mul_of_nonneg_left hInner hPos).trans (by linarith)
  let c := (M + 1) / (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hcN : c * (n : ℝ) = M + 1 := div_mul_cancel₀ _ hnR.ne'
  have hDeriv (v : E n) (hv : ‖v‖ = 1) (x : E n) (hx : x ∈ closedUnitBall n) :
      fderiv ℝ u x v ≤ 2 * b + c * b := by
    let w (y : E n) := fderiv ℝ u y v - (-c) * u y
    obtain ⟨U, hU, hSub, huU⟩ := hu
    have hdu := contDiffOn_directionalDerivative hU huU v
    have hw : SmoothNear (closedUnitBall n) w := ⟨U, hU, hSub, hdu.sub (contDiffOn_const.mul huU)⟩
    have hL (y : E n) (hy : y ∈ unitBall n) : 0 < complexLaplacian u w y := by
      have hyU := hU.mem_nhds (hSub (ball_subset_closedBall hy))
      have huAt := huU.contDiffAt hyU
      have hdet : IsUnit (complexHessian u y).det := (Matrix.isUnit_iff_isUnit_det _).mp (huP y hy).isUnit
      have he := complexLaplacian_directionalDerivative_eq_logDensity
        (⟨U, hU, hSub, huU⟩ : SmoothNear (closedUnitBall n) u) hf huP hEq hy v
      have hh := (fderiv ℝ (fun z => Real.log (f z)) y).le_opNorm v
      rw [hv, mul_one, Real.norm_eq_abs] at hh
      have hm := (abs_le.mp (hh.trans (hLog y hy))).1
      rw [show w = (fun z => fderiv ℝ u z v - (-c) * u z) from rfl,
        complexLaplacian_sub_at u (hdu.contDiffAt hyU) (contDiffAt_const.mul huAt),
        complexLaplacian_const_mul_at u huAt, complexLaplacian_self_of_isUnit hdet, he, neg_mul, hcN]
      linarith
    have hW := le_boundary_bound_of_complexLaplacian_pos hw huP hL
      (fun y hy => by simpa only [w, hu0 y hy, mul_zero, sub_zero] using
        (le_abs_self _).trans (hSlope v hv y hy)) x hx
    have hLow : -b ≤ u x := by
      linarith only [(hBound.1 x hx).1, mul_nonneg hb.le (sq_nonneg ‖x‖)]
    dsimp [w] at hW
    linarith only [hW, mul_le_mul_of_nonneg_left hLow hc.le]
  intro x hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  rw [Real.norm_eq_abs, abs_le]
  have hneg := hDeriv (-v) (by simpa only [norm_neg] using hv) x hx
  rw [map_neg] at hneg
  exact ⟨by linarith only [hneg], hDeriv v hv x hx⟩

end KEBall
