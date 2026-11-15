import KEBall.DirichletFirstJetBoundary
import KEBall.DirichletBoundaryInterpolation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Actual closed-ball first-jet compactness from a common Holder modulus,
without a uniform real Hessian bound. Uncompiled continuation draft. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff NNReal Topology

namespace KEBall

theorem exists_subseq_dirichlet_C1_of_uniform_firstJet_holder {n : ℕ} {u : ℕ → E n → ℝ}
    (hu : ∀ j, SmoothNear (closedUnitBall n) (u j)) {R : ℝ} {K D α : ℝ≥0} (hα : 0 < α)
    (hU : ∀ j x, x ∈ closedUnitBall n → ‖u j x‖ ≤ R)
    (hG : ∀ j x, x ∈ closedUnitBall n → ‖fderiv ℝ (u j) x‖ ≤ K)
    (hHold : ∀ j, HolderOnWith D α (fderiv ℝ (u j)) (closedUnitBall n)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ), StrictMono φ ∧
      TendstoUniformlyOn (fun j => u (φ j)) w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      HolderOnWith D α G (closedUnitBall n) ∧
      ContDiffOn ℝ 1 w (closedUnitBall n) ∧
      (∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x) := by
  let S := ↥(closedUnitBall n)
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)
  let V := ℝ × (E n →L[ℝ] ℝ)
  let p (j : ℕ) : BoundedContinuousFunction S V := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (u j x, fderiv ℝ (u j) x), by
      apply Continuous.prodMk
      · apply continuous_iff_continuousAt.mpr
        intro x
        exact ((hu j).contDiffAt x.property).continuousAt.comp continuous_subtype_val.continuousAt
      · apply continuous_iff_continuousAt.mpr
        intro x
        exact (((hu j).contDiffAt x.property).fderiv_right (m := ∞) (by simp)).continuousAt.comp
          continuous_subtype_val.continuousAt⟩
  have hLipU (j : ℕ) : LipschitzOnWith K (u j) (closedUnitBall n) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall (0 : E n) 1)
    · intro x hx
      exact ((hu j).contDiffAt hx).differentiableAt (by simp)
    · intro x hx
      exact_mod_cast hG j x hx
  let C := closedBall (0 : V) (max R (K : ℝ))
  have hC : IsCompact C := isCompact_closedBall _ _
  have hPC (f : BoundedContinuousFunction S V) (x : S) (hf : f ∈ range p) : f x ∈ C := by
    obtain ⟨j, rfl⟩ := hf
    apply mem_closedBall_zero_iff.mpr
    change max ‖u j x‖ ‖fderiv ℝ (u j) x‖ ≤ max R (K : ℝ)
    exact max_le_max (hU j x x.property) (hG j x x.property)
  have hEqui : Equicontinuous (fun g : range p => (g.val : S → V)) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun r => (K : ℝ) * r + (D : ℝ) * r ^ (α : ℝ))
    · have hc : ContinuousAt
          (fun r : ℝ => (K : ℝ) * r + (D : ℝ) * r ^ (α : ℝ)) 0 :=
        (continuousAt_const.mul continuousAt_id).add
          (continuousAt_const.mul (Real.continuous_rpow_const α.coe_nonneg).continuousAt)
      simpa only [mul_zero, Real.zero_rpow (show (α : ℝ) ≠ 0 by exact_mod_cast hα.ne'), add_zero]
        using hc.tendsto
    · intro x y g
      obtain ⟨j, hj⟩ := g.property
      change dist (g.val x) (g.val y) ≤
        (K : ℝ) * dist x y + (D : ℝ) * dist x y ^ (α : ℝ)
      rw [← hj]
      change max (dist (u j x) (u j y)) (dist (fderiv ℝ (u j) x) (fderiv ℝ (u j) y)) ≤ _
      apply max_le
      · exact ((hLipU j).dist_le_mul x x.property y y.property).trans
          (le_add_of_nonneg_right (by positivity))
      · exact ((hHold j).dist_le x.property y.property).trans
          (le_add_of_nonneg_left (by positivity))
  have hComp := BoundedContinuousFunction.arzela_ascoli C hC (range p) hPC hEqui
  obtain ⟨f, _, φ, hφ, hf⟩ := hComp.tendsto_subseq (fun j => subset_closure (mem_range_self j))
  have hUnif := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hf
  classical
  let W (x : E n) : V := if hx : x ∈ closedUnitBall n then f ⟨x, hx⟩ else 0
  have hW : TendstoUniformlyOn (fun j x => (u (φ j) x, fderiv ℝ (u (φ j)) x))
      W atTop (closedUnitBall n) := by
    rw [Metric.tendstoUniformlyOn_iff]
    rw [Metric.tendstoUniformly_iff] at hUnif
    intro ε hε
    filter_upwards [hUnif ε hε] with j hj x hx
    have hjx := hj ⟨x, hx⟩
    change dist (f ⟨x, hx⟩) (u (φ j) x, fderiv ℝ (u (φ j)) x) < ε at hjx
    simpa only [W, dif_pos hx] using hjx
  let w (x : E n) := (W x).1
  let G (x : E n) := (W x).2
  have hw : TendstoUniformlyOn (fun j => u (φ j)) w atTop (closedUnitBall n) := by
    rw [Metric.tendstoUniformlyOn_iff] at hW ⊢
    intro ε hε
    filter_upwards [hW ε hε] with j hj x hx
    exact (le_max_left _ _).trans_lt (hj x hx)
  have hG' : TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) := by
    rw [Metric.tendstoUniformlyOn_iff] at hW ⊢
    intro ε hε
    filter_upwards [hW ε hε] with j hj x hx
    exact (le_max_right _ _).trans_lt (hj x hx)
  have hD (x : E n) (hx : x ∈ unitBall n) : HasFDerivAt w (G x) x :=
    hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hG'.mono ball_subset_closedBall)
      (fun j y hy => (((hu (φ j)).contDiffAt (ball_subset_closedBall hy)).differentiableAt
        (by simp)).hasFDerivAt) (fun y hy => hw.tendsto_at (ball_subset_closedBall hy)) hx
  have hGH : HolderOnWith D α G (closedUnitBall n) := by
    apply dirichlet_holderOnWith_of_norm_bound D.coe_nonneg α.coe_nonneg
    intro x hx y hy
    have h := le_of_tendsto ((hG'.tendsto_at hx).dist (hG'.tendsto_at hy))
      (Eventually.of_forall fun j => (hHold (φ j)).dist_le hx hy)
    simpa only [dist_eq_norm] using h
  have hwC : ContinuousOn w (closedUnitBall n) :=
    hw.continuousOn (Eventually.frequently (Eventually.of_forall fun j x hx =>
      ((hu (φ j)).contDiffAt hx).continuousAt.continuousWithinAt))
  have hGC : ContinuousOn G (closedUnitBall n) := hGH.continuousOn hα
  exact ⟨φ, w, G, hφ, hw, hG', hD, hGH,
    contDiffOn_one_dirichlet_closedBall hwC hGC hD,
    fun x hx => hasFDerivWithinAt_dirichlet_closedBall hwC hGC hD hx⟩

end KEBall
