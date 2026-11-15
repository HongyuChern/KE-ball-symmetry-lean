import KEBall.DirichletLinearizedDensityLimit

/-! Uniform-in-space small affine variations of a smooth elliptic potential. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

theorem eventually_dirichlet_affine_elliptic_bounds {n : ℕ}
    {u q : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hq : SmoothNear (closedUnitBall n) q) {a b D : ℝ}
    (hPos : ∀ x ∈ closedUnitBall n, (complexHessian u x).PosDef)
    (hDen : ∀ x ∈ closedUnitBall n,
      a < (complexHessian u x).det.re ∧ (complexHessian u x).det.re < b)
    (hHess : ∀ x ∈ closedUnitBall n, ‖realHessian u x‖ < D) :
    ∀ᶠ s : ℝ in 𝓝 0, ∀ x ∈ closedUnitBall n,
      (complexHessian (u + s • q) x).PosDef ∧
      a < (complexHessian (u + s • q) x).det.re ∧
      (complexHessian (u + s • q) x).det.re < b ∧
      ‖realHessian (u + s • q) x‖ < D := by
  obtain ⟨U, hU, hSubU, huU⟩ := hu
  obtain ⟨V, hV, hSubV, hqV⟩ := hq
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hSubW : closedUnitBall n ⊆ W := subset_inter hSubU hSubV
  have huW : ContDiffOn ℝ ∞ u W := huU.mono inter_subset_left
  have hqW : ContDiffOn ℝ ∞ q W := hqV.mono inter_subset_right
  have hCu : ContinuousOn (complexHessian u) W :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (complexHessian_contDiffOn hW huW i j).continuousOn
  have hCq : ContinuousOn (complexHessian q) W :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (complexHessian_contDiffOn hW hqW i j).continuousOn
  let H (p : ℝ × E n) := complexHessian u p.2 + (p.1 : ℂ) • complexHessian q p.2
  let R (p : ℝ × E n) := realHessian u p.2 + p.1 • realHessian q p.2
  apply (isCompact_closedBall (0 : E n) 1).eventually_forall_of_forall_eventually
  intro x hx
  have hxW := hSubW hx
  have hux := huW.contDiffAt (hW.mem_nhds hxW)
  have hqx := hqW.contDiffAt (hW.mem_nhds hxW)
  have hHC : ContinuousAt H (0, x) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    change ContinuousAt (fun p : ℝ × E n => complexHessian u p.2 i j +
      (p.1 : ℂ) * complexHessian q p.2 i j) (0, x)
    exact (((continuousOn_pi.mp (continuousOn_pi.mp hCu i) j).continuousAt
      (hW.mem_nhds hxW)).comp continuousAt_snd).add
      ((Complex.continuous_ofReal.continuousAt.comp continuousAt_fst).mul
        (((continuousOn_pi.mp (continuousOn_pi.mp hCq i) j).continuousAt
          (hW.mem_nhds hxW)).comp continuousAt_snd))
  have hRC : ContinuousAt R (0, x) :=
    (((realHessian_contDiffAt hux).continuousAt).comp continuousAt_snd).add
      (continuousAt_fst.smul
        (((realHessian_contDiffAt hqx).continuousAt).comp continuousAt_snd))
  have hH0 : H (0, x) = complexHessian u x := by simp [H]
  have hR0 : R (0, x) = realHessian u x := by simp [R]
  have hDC : ContinuousAt (fun p => (H p).det.re) (0, x) :=
    (Complex.continuous_re.comp continuous_id.matrix_det).continuousAt.comp hHC
  have hLow : ∀ᶠ p in 𝓝 (0, x), a < (H p).det.re :=
    hDC.eventually_const_lt (by
      change a < (H (0, x)).det.re
      rw [hH0]
      exact (hDen x hx).1)
  have hHigh : ∀ᶠ p in 𝓝 (0, x), (H p).det.re < b :=
    hDC.eventually_lt_const (by
      change (H (0, x)).det.re < b
      rw [hH0]
      exact (hDen x hx).2)
  have hNorm : ∀ᶠ p in 𝓝 (0, x), ‖R p‖ < D :=
    hRC.norm.eventually_lt_const (by
      change ‖R (0, x)‖ < D
      rw [hR0]
      exact hHess x hx)
  obtain ⟨O, hO, hxO, hOP⟩ := exists_isOpen_hermitian_posDef_nhds (hPos x hx)
  have hNearO : ∀ᶠ p in 𝓝 (0, x), H p ∈ O :=
    hHC (hO.mem_nhds (hH0.symm ▸ hxO))
  have hNearW : ∀ᶠ p : ℝ × E n in 𝓝 (0, x), p.2 ∈ W :=
    continuousAt_snd (hW.mem_nhds hxW)
  filter_upwards [hNearW, hNearO, hLow, hHigh, hNorm] with p hpW hpO hpLow hpHigh hpNorm
  have huAt := huW.contDiffAt (hW.mem_nhds hpW)
  have hqAt := hqW.contDiffAt (hW.mem_nhds hpW)
  have hHe : complexHessian (u + p.1 • q) p.2 = H p :=
    dirichlet_complexHessian_affine huAt hqAt p.1
  have hRe : realHessian (u + p.1 • q) p.2 = R p :=
    dirichlet_realHessian_affine huAt hqAt p.1
  have hHerm : (H p).IsHermitian := by
    rw [← hHe]
    exact MoserTrudinger.complexHessian_isHermitian_of_smooth
      (huAt.add (hqAt.const_smul p.1))
  rw [hHe, hRe]
  exact ⟨hOP _ hpO hHerm, hpLow, hpHigh, hpNorm⟩

end KEBall
