import KEBall.DirichletBoundaryHessian

/-!
# Interior Hessian estimates for the prescribed Dirichlet equation

The log-determinant tangent inequality gives the linearized lower bound
for each fixed directional second derivative. The maximum principle
extends the sphere Hessian bound to the closed ball.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ComplexOrder ContDiff Matrix Matrix.Norms.Elementwise Topology

namespace KEBall

private noncomputable def traceLeftReCLM {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((((Matrix.traceLinearMap (n := Fin n) (R := ℂ) ℂ).comp
      (LinearMap.mulLeft ℂ B)).restrictScalars ℝ).toContinuousLinearMap)

@[simp] private theorem traceLeftReCLM_apply {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℂ) :
    traceLeftReCLM B H = (B * H).trace.re := rfl

private theorem isLocalMax_logDensity_sub_frozenTrace {n : ℕ} {u f : E n → ℝ}
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ unitBall n) :
    IsLocalMax (fun y => Real.log (f y) -
      traceLeftReCLM (complexHessian u x)⁻¹ (complexHessian u y)) x := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  have h := posDef_logdet_tangent (huP x hx) (huP y hy)
  rw [hEq x hx, hEq y hy, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h
  change Real.log (f y) - traceLeftReCLM (complexHessian u x)⁻¹ (complexHessian u y) ≤
    Real.log (f x) - traceLeftReCLM (complexHessian u x)⁻¹ (complexHessian u x)
  simp only [traceLeftReCLM_apply]
  linarith only [h]

private theorem fderiv_traceLeftReCLM {n : ℕ} {H : E n → Matrix (Fin n) (Fin n) ℂ} {x : E n}
    (hH : DifferentiableAt ℝ H x) (B : Matrix (Fin n) (Fin n) ℂ) (v : E n) :
    fderiv ℝ (fun y => traceLeftReCLM B (H y)) x v =
      traceLeftReCLM B (fun i j => fderiv ℝ (fun y => H y i j) x v) := by
  have hd := (traceLeftReCLM B).hasFDerivAt.comp (f := H) x hH.hasFDerivAt
  change HasFDerivAt (fun y => traceLeftReCLM B (H y)) _ x at hd
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  congr 1
  ext i j
  have hI : DifferentiableAt ℝ (fun y => H y i) x := (differentiableAt_pi.mp hH) i
  rw [fderiv_apply hI, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    fderiv_apply hH, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rfl

private theorem contDiffOn_complexHessian_matrix {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (complexHessian u) U :=
  contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => complexHessian_contDiffOn hU hu i j

private theorem fderiv_frozenTrace_hessian {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (B : Matrix (Fin n) (Fin n) ℂ) (v : E n) :
    fderiv ℝ (fun y => traceLeftReCLM B (complexHessian u y)) x v =
      traceLeftReCLM B (complexHessian (fun y => fderiv ℝ u y v) x) := by
  have hH := ((contDiffOn_complexHessian_matrix hU hu).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [fderiv_traceLeftReCLM hH]
  congr 1
  ext i j
  exact (complexHessian_directionalDerivative hU hu hx v i j).symm

/-- Differentiating the log-determinant tangent inequality twice in a fixed
direction gives the lower bound for the linearized Hessian equation. -/
theorem complexLaplacian_realHessian_self_ge_logDensity {n : ℕ} {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ unitBall n) (v : E n) :
    realHessian (fun y => Real.log (f y)) x v v ≤
      complexLaplacian u (fun y => realHessian u y v v) x := by
  let B := (complexHessian u x)⁻¹
  let g : E n → ℝ := fun y => Real.log (f y)
  let d : E n → ℝ := fun y => fderiv ℝ u y v
  let dd : E n → ℝ := fun y => fderiv ℝ d y v
  let w : E n → ℝ := fun y => g y - traceLeftReCLM B (complexHessian u y)
  have hxC := ball_subset_closedBall hx
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hxU := hSub hxC
  have hxN := hU.mem_nhds hxU
  have hdU : ContDiffOn ℝ ∞ d U := contDiffOn_directionalDerivative hU huU v
  have hgAt : ContDiffAt ℝ ∞ g x :=
    (hf.contDiffAt hxC).log (((hEq x hx) ▸ posDef_det_re_pos (huP x hx)) : 0 < f x).ne'
  have hTraceAt : ContDiffAt ℝ ∞ (fun y => traceLeftReCLM B (complexHessian u y)) x :=
    (traceLeftReCLM B).contDiff.contDiffAt.comp x
      ((contDiffOn_complexHessian_matrix hU huU).contDiffAt hxN)
  have hwAt : ContDiffAt ℝ ∞ w x := hgAt.sub hTraceAt
  have hmax : IsLocalMax w x := isLocalMax_logDensity_sub_frozenTrace huP hEq hx
  have hSecond := realHessian_nonpos_of_isLocalMax hwAt hmax v
  have he : (fun y => fderiv ℝ w y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ g y v - traceLeftReCLM B (complexHessian d y)) := by
    filter_upwards [hxN, isOpen_ball.mem_nhds hx] with y hy hyB
    have hgAt' : ContDiffAt ℝ ∞ g y :=
      (hf.contDiffAt (ball_subset_closedBall hyB)).log
        (((hEq y hyB) ▸ posDef_det_re_pos (huP y hyB)) : 0 < f y).ne'
    have hTraceAt' : ContDiffAt ℝ ∞ (fun z => traceLeftReCLM B (complexHessian u z)) y :=
      (traceLeftReCLM B).contDiff.contDiffAt.comp y
        ((contDiffOn_complexHessian_matrix hU huU).contDiffAt (hU.mem_nhds hy))
    change (fderiv ℝ (fun z => g z - traceLeftReCLM B (complexHessian u z)) y) v = _
    rw [fderiv_fun_sub (hgAt'.differentiableAt (by simp)) (hTraceAt'.differentiableAt (by simp)),
      sub_apply, fderiv_frozenTrace_hessian hU huU hy B v]
  have hDg : DifferentiableAt ℝ (fun y => fderiv ℝ g y v) x :=
    ((hgAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ (fun y => traceLeftReCLM B (complexHessian d y)) x :=
    ((traceLeftReCLM B).contDiff.contDiffAt.comp x
      ((contDiffOn_complexHessian_matrix hU hdU).contDiffAt hxN)).differentiableAt (by simp)
  rw [← fderiv_firstDerivative_apply hwAt, he.fderiv_eq, fderiv_fun_sub hDg hDd, sub_apply,
    fderiv_firstDerivative_apply hgAt, fderiv_frozenTrace_hessian hU hdU hxU B v] at hSecond
  have hNear : dd =ᶠ[𝓝 x] (fun y => realHessian u y v v) := by
    filter_upwards [hxN] with y hy
    exact fderiv_firstDerivative_apply (huU.contDiffAt (hU.mem_nhds hy)) v v
  rw [complexLaplacian_eq_trace]
  have hHess : complexHessian dd x = complexHessian (fun y => realHessian u y v v) x :=
    complexHessian_congr_of_eventuallyEq hNear
  change realHessian g x v v - traceLeftReCLM B (complexHessian dd x) ≤ 0 at hSecond
  rw [hHess, traceLeftReCLM_apply] at hSecond
  exact sub_nonpos.mp hSecond

/-- A sphere Hessian bound and a lower bound for the second derivative of
the prescribed log density yield a Hessian bound on the entire closed ball. -/
theorem abs_realHessian_self_le_of_dirichlet_det {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {a b C M : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 0 ≤ M)
    (hDensity : ∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n)
    (hBoundary : ∀ x ∈ unitSphere n, ∀ v : E n, ‖v‖ = 1 →
      |realHessian u x v v| ≤ C)
    (hLog : ∀ x ∈ unitBall n, ∀ v : E n, ‖v‖ = 1 →
      -M ≤ realHessian (fun y => Real.log (f y)) x v v) :
    ∀ x ∈ closedUnitBall n, ∀ v : E n, ‖v‖ = 1 →
      |realHessian u x v v| ≤ C + ((M + 1) / n) * b := by
  let c := (M + 1) / (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcN : c * (n : ℝ) = M + 1 := div_mul_cancel₀ _ hnR.ne'
  have hcb : 0 ≤ c * b := mul_nonneg hc hb.le
  have hBound := Cegrell.quadratic_and_boundarySlope_bounds hn hu (fun x hx => (huP x hx).posSemidef)
    hu0 ha hb (fun x hx => hEq x hx ▸ hDensity x hx)
  have hUp (v : E n) (hv : ‖v‖ = 1) (x : E n) (hx : x ∈ closedUnitBall n) :
      realHessian u x v v ≤ C + c * b := by
    let H : E n → ℝ := fun y => realHessian u y v v
    let w : E n → ℝ := fun y => H y - (-c) * u y
    obtain ⟨U, hU, hSub, huU⟩ := hu
    have hdu := contDiffOn_directionalDerivative hU huU v
    have hdd := contDiffOn_directionalDerivative hU hdu v
    have hHU : ContDiffOn ℝ ∞ H U := by
      apply hdd.congr
      intro y hy
      exact (fderiv_firstDerivative_apply (huU.contDiffAt (hU.mem_nhds hy)) v v).symm
    have hw : SmoothNear (closedUnitBall n) w := ⟨U, hU, hSub, hHU.sub (contDiffOn_const.mul huU)⟩
    have hL (y : E n) (hy : y ∈ unitBall n) : 0 < complexLaplacian u w y := by
      have hyU := hU.mem_nhds (hSub (ball_subset_closedBall hy))
      have huAt := huU.contDiffAt hyU
      have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (huP y hy).isUnit
      have he := complexLaplacian_realHessian_self_ge_logDensity
        (⟨U, hU, hSub, huU⟩ : SmoothNear (closedUnitBall n) u) hf huP hEq hy v
      have hm := (hLog y hy v hv).trans he
      rw [show w = (fun z => H z - (-c) * u z) from rfl,
        complexLaplacian_sub_at u (hHU.contDiffAt hyU) (contDiffAt_const.mul huAt),
        complexLaplacian_const_mul_at u huAt, complexLaplacian_self_of_isUnit hdet,
        neg_mul, hcN]
      change 0 < complexLaplacian u H y - -(M + 1)
      linarith only [hm]
    have hW := le_boundary_bound_of_complexLaplacian_pos hw huP hL
      (fun y hy => by simpa only [w, H, hu0 y hy, mul_zero, sub_zero] using
        (le_abs_self _).trans (hBoundary y hy v hv)) x hx
    have hLow : -b ≤ u x := by
      linarith only [(hBound.1 x hx).1, mul_nonneg hb.le (sq_nonneg ‖x‖)]
    dsimp [w, H] at hW
    linarith only [hW, mul_le_mul_of_nonneg_left hLow hc]
  intro x hx v hv
  have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  rcases hx'.lt_or_eq with hlt | heq
  · have hxB : x ∈ unitBall n := mem_ball_zero_iff.mpr hlt
    have hv' : v ≠ 0 := by intro h; simp [h] at hv
    have hPos : 0 < realMetricForm u x v v := by
      rw [realMetricForm_eq]
      exact hermitianRealification_pos (huP x hxB) v hv'
    rw [realMetricForm_eq_average_hessian (hu.contDiffAt hx)] at hPos
    have hJ := hUp (J v) (by rw [norm_J, hv]) x hx
    exact abs_le.mpr ⟨by linarith only [hPos, hJ], hUp v hv x hx⟩
  · exact (hBoundary x (mem_sphere_zero_iff_norm.mpr heq) v hv).trans (le_add_of_nonneg_right hcb)

end KEBall
