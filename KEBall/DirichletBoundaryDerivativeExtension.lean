import KEBall.DirichletFirstJetBoundary

/-!
# Extending a derivative field across the sphere

The interior limit and the continuous sphere value are glued on the closed
ball.  The derivative extension theorem then supplies the actual within
derivative, including at the boundary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ContDiff Topology

namespace KEBall

noncomputable def dirichletClosedBallExtension {n : ℕ} {F : Type*}
    (f a : E n → F) : E n → F := by
  classical
  exact fun x => if x ∈ unitBall n then f x else a x

theorem continuousOn_dirichlet_closedBall_extension {n : ℕ} {F : Type*}
    [TopologicalSpace F] {f a : E n → F}
    (hf : ContinuousOn f (unitBall n)) (ha : ContinuousOn a (unitSphere n))
    (hLim : ∀ p ∈ unitSphere n, Tendsto f (𝓝[unitBall n] p) (𝓝 (a p))) :
    ContinuousOn (dirichletClosedBallExtension f a) (closedUnitBall n) := by
  classical
  change ContinuousOn (fun x => if x ∈ unitBall n then f x else a x) (closedUnitBall n)
  let g (x : E n) := if x ∈ unitBall n then f x else a x
  have hInterior (x : E n) (hx : x ∈ unitBall n) : ContinuousAt g x := by
    have he : g =ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact if_pos hy
    exact ((hf x hx).continuousAt (isOpen_ball.mem_nhds hx)).congr_of_eventuallyEq he
  have hSphere (x : E n) (hx : x ∈ unitSphere n) : x ∉ unitBall n := by
    intro h
    have hlt := mem_ball_zero_iff.mp h
    rw [mem_sphere_zero_iff_norm.mp hx] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  intro x hx
  by_cases hi : x ∈ unitBall n
  · exact (hInterior x hi).continuousWithinAt
  · have hs : x ∈ unitSphere n := by
      apply mem_sphere_zero_iff_norm.mpr
      have hle := mem_closedBall_zero_iff.mp hx
      have hge : 1 ≤ ‖x‖ := le_of_not_gt (fun h => hi (mem_ball_zero_iff.mpr h))
      exact le_antisymm hle hge
    have hUnion : closedUnitBall n = unitBall n ∪ unitSphere n := by
      exact (ball_union_sphere : ball (0 : E n) 1 ∪ sphere (0 : E n) 1 =
        closedBall (0 : E n) 1).symm
    change Tendsto g (𝓝[closedUnitBall n] x) (𝓝 (g x))
    rw [hUnion, nhdsWithin_union, tendsto_sup]
    have hgx : g x = a x := if_neg hi
    rw [hgx]
    constructor
    · apply (hLim x hs).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (if_pos hy).symm
    · apply (ha x hs).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (if_neg (hSphere y hy)).symm

theorem exists_dirichlet_closedBall_derivative_extension {n : ℕ}
    {q : E n → ℝ} {A : E n → E n →L[ℝ] ℝ}
    (hq : ContinuousOn q (closedUnitBall n))
    (hq1 : ContDiffOn ℝ 1 q (unitBall n))
    (hA : ContinuousOn A (unitSphere n))
    (hLim : ∀ p ∈ unitSphere n, Tendsto (fderiv ℝ q) (𝓝[unitBall n] p) (𝓝 (A p))) :
    ∃ Q : E n → E n →L[ℝ] ℝ,
      ContinuousOn Q (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, Q x = fderiv ℝ q x) ∧
      (∀ p ∈ unitSphere n, Q p = A p) ∧
      (∀ x ∈ closedUnitBall n, HasFDerivWithinAt q (Q x) (closedUnitBall n) x) ∧
      ContDiffOn ℝ 1 q (closedUnitBall n) := by
  classical
  let Q (x : E n) := if x ∈ unitBall n then fderiv ℝ q x else A x
  have hDC : ContinuousOn (fderiv ℝ q) (unitBall n) := by
    intro x hx
    exact ((hq1.contDiffAt (isOpen_ball.mem_nhds hx)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hQC : ContinuousOn Q (closedUnitBall n) :=
    continuousOn_dirichlet_closedBall_extension hDC hA hLim
  have hD (x : E n) (hx : x ∈ unitBall n) : HasFDerivAt q (Q x) x := by
    rw [show Q x = fderiv ℝ q x from if_pos hx]
    exact ((hq1.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨Q, hQC, fun x hx => if_pos hx, ?_,
    fun x hx => hasFDerivWithinAt_dirichlet_closedBall hq hQC hD hx,
    contDiffOn_one_dirichlet_closedBall hq hQC hD⟩
  intro p hp
  apply if_neg
  intro h
  have hlt := mem_ball_zero_iff.mp h
  rw [mem_sphere_zero_iff_norm.mp hp] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

end KEBall
