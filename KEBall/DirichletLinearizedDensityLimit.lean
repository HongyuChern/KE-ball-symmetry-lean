import KEBall.DirichletHessianPerturbation
import KEBall.MoserTrudingerSmoothVariation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual L2 limit of determinant difference quotients

The matrix determinant is differentiated along the genuine potential
u + t q.  A compact matrix Lipschitz bound supplies a single integrable
majorant before passing the squared difference quotients to the limit.
No regularity of a weak solution is assumed or concluded here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

theorem dirichlet_realHessian_affine {n : ℕ} {u q : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hq : ContDiffAt ℝ ∞ q x) (t : ℝ) :
    realHessian (u + t • q) x = realHessian u x + t • realHessian q x := by
  have h2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have ht : ContDiffAt ℝ ∞ (t • q) x := hq.const_smul t
  ext a b
  change realHessian (u + t • q) x a b =
    realHessian u x a b + t * realHessian q x a b
  simp only [← PshLines.realHessian_eq_fderiv, KEBall.realHessian]
  rw [PshLines.realHessian_add (hu.of_le h2) (ht.of_le h2),
    PshLines.realHessian_smul (hq.of_le h2)]

theorem dirichlet_complexHessian_affine {n : ℕ} {u q : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hq : ContDiffAt ℝ ∞ q x) (t : ℝ) :
    complexHessian (u + t • q) x =
      complexHessian u x + (t : ℂ) • complexHessian q x := by
  have hR (a b : E n) : realHessian (u + t • q) x a b =
      realHessian u x a b + t * realHessian q x a b := by
    rw [dirichlet_realHessian_affine hu hq]
    rfl
  ext i j
  have hp : ContDiffAt ℝ ∞ (u + t • q) x := hu.add (hq.const_smul t)
  rw [complexHessian_real_entry hp i j]
  simp only [complexHessian_real_entry hu, complexHessian_real_entry hq,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hR]
  push_cast
  ring

theorem hasDerivAt_dirichlet_det_affine {n : ℕ} {u q : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hq : ContDiffAt ℝ ∞ q x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (complexHessian (u + s • q) x).det.re)
      (MoserTrudinger.cofactorContraction (u + t • q) q x) t := by
  let A (s : ℝ) := complexHessian u x + (s : ℂ) • complexHessian q x
  have hA (i j : Fin n) :
      HasDerivAt (fun s => A s i j) (complexHessian q x i j) t := by
    change HasDerivAt (fun s : ℝ => complexHessian u x i j +
      (s : ℂ) * complexHessian q x i j) _ t
    simpa using (Complex.ofRealCLM.hasFDerivAt.hasDerivAt.mul_const
      (complexHessian q x i j)).const_add (complexHessian u x i j)
  have hdiff := (field_det_differentiableAt fun i j => (hA i j).differentiableAt).hasDerivAt
  have heq : deriv (fun s => (A s).det) t =
      ∑ i : Fin n, ∑ j : Fin n, (A t).adjugate j i * complexHessian q x i j := by
    rw [← fderiv_apply_one_eq_deriv]
    change KEBallProbe.rd (1 : ℝ) (fun s => (A s).det) t = _
    rw [rd_det_field (fun i j => (hA i j).differentiableAt)]
    simp only [KEBallProbe.rd, fderiv_apply_one_eq_deriv, fun i j => (hA i j).deriv]
  rw [heq] at hdiff
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdiff
  simpa only [Function.comp_def, dirichlet_complexHessian_affine hu hq,
    MoserTrudinger.cofactorContraction, Complex.reCLM_apply, A] using h

theorem tendsto_integral_sq_dirichlet_density_slope {n : ℕ} (hn : 0 < n)
    {u q : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hq : SmoothNear (closedUnitBall n) q) {t : ℕ → ℝ}
    (hT : Tendsto t atTop (𝓝[≠] (0 : ℝ))) :
    Tendsto (fun m => ∫ x in unitBall n,
      (((complexHessian (u + t m • q) x).det.re -
        (complexHessian u x).det.re) / t m) ^ 2 ∂volume0 n) atTop
      (𝓝 (∫ x in unitBall n, (MoserTrudinger.cofactorContraction u q x) ^ 2 ∂volume0 n)) := by
  let μ := (volume0 n).restrict (unitBall n)
  have : NeZero n := ⟨hn.ne'⟩
  let A := complexHessian u
  let B := complexHessian q
  have hCont {v : E n → ℝ} (hv : SmoothNear (closedUnitBall n) v) :
      ContinuousOn (complexHessian v) (closedUnitBall n) := by
    obtain ⟨U, hU, hSub, hvU⟩ := hv
    exact (continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (complexHessian_contDiffOn hU hvU i j).continuousOn).mono hSub
  have hAC : ContinuousOn A (closedUnitBall n) := hCont hu
  have hBC : ContinuousOn B (closedUnitBall n) := hCont hq
  obtain ⟨a, ha⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hAC
  obtain ⟨b, hb⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hBC
  let a₀ := max a 0
  let b₀ := max b 0
  have ha₀ : 0 ≤ a₀ := le_max_right _ _
  have hb₀ : 0 ≤ b₀ := le_max_right _ _
  have hAB (x : E n) (hx : x ∈ closedUnitBall n) : ‖A x‖ ≤ a₀ :=
    (ha x hx).trans (le_max_left _ _)
  have hBB (x : E n) (hx : x ∈ closedUnitBall n) : ‖B x‖ ≤ b₀ :=
    (hb x hx).trans (le_max_left _ _)
  obtain ⟨C, hC, hDet⟩ := exists_abs_det_re_sub_le_mul_norm_sub (n := n) (a₀ + b₀)
  let p (s : ℝ) (x : E n) :=
    (((complexHessian (u + s • q) x).det.re - (complexHessian u x).det.re) / s) ^ 2
  have hPC (s : ℝ) : ContinuousOn (p s) (closedUnitBall n) := by
    have hsB : ContinuousOn (fun x => (s : ℂ) • B x) (closedUnitBall n) := by
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      change ContinuousOn (fun x => (s : ℂ) * B x i j) (closedUnitBall n)
      exact continuousOn_const.mul (continuousOn_pi.mp (continuousOn_pi.mp hBC i) j)
    have hc : ContinuousOn (fun x => (A x + (s : ℂ) • B x).det.re)
        (closedUnitBall n) :=
      Complex.continuous_re.comp_continuousOn
        (continuous_id.matrix_det.comp_continuousOn (hAC.add hsB))
    refine ((hc.sub (Complex.continuous_re.comp_continuousOn
      (continuous_id.matrix_det.comp_continuousOn hAC))).div_const s).pow 2 |>.congr ?_
    intro x hx
    change (((complexHessian (u + s • q) x).det.re -
      (complexHessian u x).det.re) / s) ^ 2 =
      (((complexHessian u x + (s : ℂ) • complexHessian q x).det.re -
        (complexHessian u x).det.re) / s) ^ 2
    rw [dirichlet_complexHessian_affine (hu.contDiffAt hx) (hq.contDiffAt hx)]
  have hBound (s : ℝ) (hs : |s| ≤ 1) (x : E n) (hx : x ∈ closedUnitBall n) :
      ‖p s x‖ ≤ (C * b₀) ^ 2 := by
    have hPair : ‖A x + (s : ℂ) • B x‖ ≤ a₀ + b₀ := by
      refine (norm_add_le _ _).trans (add_le_add (hAB x hx) ?_)
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hBB x hx) (abs_nonneg _)).trans
        (mul_le_of_le_one_left hb₀ hs)
    have hD := hDet (A x) (A x + (s : ℂ) • B x)
      ((hAB x hx).trans (le_add_of_nonneg_right hb₀)) hPair
    rw [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hD
    have hQuot : |((A x + (s : ℂ) • B x).det.re - (A x).det.re) / s| ≤ C * b₀ := by
      by_cases hs0 : s = 0
      · simp only [hs0, div_zero, abs_zero]
        positivity
      rw [abs_div, div_le_iff₀ (abs_pos.mpr hs0)]
      exact hD.trans (by
        have h := mul_le_mul_of_nonneg_left (hBB x hx) (mul_nonneg hC (abs_nonneg s))
        nlinarith only [h])
    dsimp only [p]
    rw [dirichlet_complexHessian_affine (hu.contDiffAt hx) (hq.contDiffAt hx),
      Real.norm_eq_abs, abs_pow, sq_abs]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hQuot 2
  have hSmall : ∀ᶠ m in atTop, |t m| ≤ 1 := by
    have h := (hT.mono_right nhdsWithin_le_nhds) (closedBall_mem_nhds (0 : ℝ) zero_lt_one)
    change ∀ᶠ m in atTop, t m ∈ closedBall (0 : ℝ) 1 at h
    simpa only [mem_closedBall, Real.dist_eq, sub_zero] using h
  have hLim : ∀ᵐ x ∂μ, Tendsto (fun m => p (t m) x) atTop
      (𝓝 ((MoserTrudinger.cofactorContraction u q x) ^ 2)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    have h := ((hasDerivAt_dirichlet_det_affine
      (hu.contDiffAt (ball_subset_closedBall hx))
      (hq.contDiffAt (ball_subset_closedBall hx)) (0 : ℝ)).tendsto_slope_zero).comp hT
    have h' : Tendsto (fun m =>
        ((complexHessian (u + t m • q) x).det.re - (complexHessian u x).det.re) / t m)
        atTop (𝓝 (MoserTrudinger.cofactorContraction u q x)) := by
      simpa only [Function.comp_def, zero_add, zero_smul, add_zero, smul_eq_mul, div_eq_mul_inv,
        mul_comm] using h
    exact h'.pow 2
  exact tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun _ => (C * b₀) ^ 2)
    (Eventually.of_forall fun m => ((hPC (t m)).mono ball_subset_closedBall).aestronglyMeasurable
      measurableSet_ball)
    (hSmall.mono fun m hm => (ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)).mono
        fun x hx => hBound (t m) hm x (ball_subset_closedBall hx))
    (integrable_const _) hLim

end KEBall
