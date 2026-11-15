import KEBall.DirichletBoundaryInterpolation
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Local C2 regularity of an actual first-jet limit. The second derivative
is obtained by compactness and closedness of differentiation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

theorem local_C2_of_uniform_firstJet_and_hessian_holder {n : ℕ}
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    {p : E n} {r : ℝ} {α K : ℝ≥0} (hα : 0 < α)
    (hU : TendstoUniformlyOn u w atTop (closedBall p r))
    (hG : TendstoUniformlyOn (fun j => fderiv ℝ (u j)) G atTop (closedBall p r))
    (hBound : ∀ j x, x ∈ closedBall p r → ‖fderiv ℝ (fderiv ℝ (u j)) x‖ ≤ K)
    (hHolder : ∀ j, HolderOnWith K α (fderiv ℝ (fderiv ℝ (u j))) (closedBall p r)) :
    ContDiffOn ℝ 2 w (ball p r) ∧
      HolderOnWith K α (fderiv ℝ (fderiv ℝ w)) (ball p r) ∧
      (∀ x ∈ ball p r, ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ K) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformlyOn (fun j => fderiv ℝ (fderiv ℝ (u (φ j))))
          (fderiv ℝ (fderiv ℝ w)) atTop (ball p r) := by
  classical
  let S := ↥(closedBall p r)
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall p r)
  let V := E n →L[ℝ] E n →L[ℝ] ℝ
  let f (j : ℕ) : BoundedContinuousFunction S V := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => fderiv ℝ (fderiv ℝ (u j)) x,
      (hHolder j).continuousOn hα |>.restrict⟩
  let C := closedBall (0 : V) (K : ℝ)
  have hC : IsCompact C := isCompact_closedBall _ _
  have hFC (g : BoundedContinuousFunction S V) (x : S) (hg : g ∈ range f) : g x ∈ C := by
    obtain ⟨j, rfl⟩ := hg
    exact mem_closedBall_zero_iff.mpr (hBound j x x.property)
  have hEqui : Equicontinuous (fun g : range f => (g.val : S → V)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun d => (K : ℝ) * d ^ (α : ℝ))
    · have hc : ContinuousAt (fun d : ℝ => (K : ℝ) * d ^ (α : ℝ)) 0 :=
        continuousAt_const.mul (Real.continuous_rpow_const α.coe_nonneg).continuousAt
      simpa only [Real.zero_rpow (show (α : ℝ) ≠ 0 by exact_mod_cast hα.ne'), mul_zero]
        using hc.tendsto
    · intro x y g
      obtain ⟨j, hj⟩ := g.property
      change dist (g.val x) (g.val y) ≤ (K : ℝ) * dist x y ^ (α : ℝ)
      rw [← hj]
      exact (hHolder j).dist_le x.property y.property
  have hComp := BoundedContinuousFunction.arzela_ascoli C hC (range f) hFC hEqui
  obtain ⟨f0, _, φ, hφ, hφf⟩ := hComp.tendsto_subseq (fun j => subset_closure (mem_range_self j))
  have hUnif := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφf
  let H (x : E n) : V := if hx : x ∈ closedBall p r then f0 ⟨x, hx⟩ else 0
  have hHU : TendstoUniformlyOn (fun j => fderiv ℝ (fderiv ℝ (u (φ j))))
      H atTop (closedBall p r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    rw [Metric.tendstoUniformly_iff] at hUnif
    intro ε hε
    filter_upwards [hUnif ε hε] with j hj x hx
    have hh := hj ⟨x, hx⟩
    change dist (f0 ⟨x, hx⟩) (fderiv ℝ (fderiv ℝ (u (φ j))) x) < ε at hh
    simpa only [H, dif_pos hx] using hh
  have hHH : HolderOnWith K α H (closedBall p r) := by
    apply dirichlet_holderOnWith_of_norm_bound K.coe_nonneg α.coe_nonneg
    intro x hx y hy
    have h := le_of_tendsto ((hHU.tendsto_at hx).dist (hHU.tendsto_at hy))
      (Eventually.of_forall fun j => (hHolder (φ j)).dist_le hx hy)
    simpa only [dist_eq_norm] using h
  have hHN (x : E n) (hx : x ∈ closedBall p r) : ‖H x‖ ≤ K :=
    le_of_tendsto (hHU.tendsto_at hx).norm (Eventually.of_forall fun j => hBound (φ j) x hx)
  have hwD (x : E n) (hx : x ∈ ball p r) : HasFDerivAt w (G x) x :=
    hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hG.mono ball_subset_closedBall)
      (fun j y _ => ((hu j).differentiable (by simp) y).hasFDerivAt)
      (fun y hy => hU.tendsto_at (ball_subset_closedBall hy)) hx
  have hGD (x : E n) (hx : x ∈ ball p r) : HasFDerivAt G (H x) x :=
    hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hHU.mono ball_subset_closedBall)
      (fun j y _ => (((hu (φ j)).fderiv_right (m := ∞) (by simp)).differentiable
        (by simp) y).hasFDerivAt)
      (fun y hy => (hG.tendsto_at (ball_subset_closedBall hy)).comp hφ.tendsto_atTop) hx
  have hGC1 : ContDiffOn ℝ 1 G (ball p r) := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) isOpen_ball.uniqueDiffOn).mpr
    refine ⟨by simp, H, ?_, fun x hx => (hGD x hx).hasFDerivWithinAt⟩
    exact contDiffOn_zero.mpr ((hHH.continuousOn hα).mono ball_subset_closedBall)
  have hwC2 : ContDiffOn ℝ 2 w (ball p r) := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) isOpen_ball).mpr
    refine ⟨fun x hx => (hwD x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact hGC1.congr fun x hx => (hwD x hx).fderiv
  have hHess (x : E n) (hx : x ∈ ball p r) : fderiv ℝ (fderiv ℝ w) x = H x := by
    have heq : fderiv ℝ w =ᶠ[𝓝 x] G := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hwD y hy).fderiv
    exact heq.fderiv_eq.trans (hGD x hx).fderiv
  refine ⟨hwC2, ?_, (fun x hx => by rw [hHess x hx]; exact hHN x (ball_subset_closedBall hx)),
    φ, hφ, ?_⟩
  · intro x hx y hy
    simpa only [hHess x hx, hHess y hy] using hHH x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
  · rw [Metric.tendstoUniformlyOn_iff] at hHU ⊢
    intro ε hε
    filter_upwards [hHU ε hε] with j hj x hx
    simpa only [hHess x hx] using hj x (ball_subset_closedBall hx)

end KEBall
