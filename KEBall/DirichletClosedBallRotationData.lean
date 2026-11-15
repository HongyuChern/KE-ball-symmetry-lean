import KEBall.DirichletInteriorRotationEquation
import KEBall.DirichletCompactHolder
import KEBall.DirichletFirstJetBoundary
import KEBall.DirichletAngularWordEquation

/-!
# Closed-ball first jets and the equation of genuine angular derivatives

The rotation derivative uses the actual within first derivative.  It is
zero on the sphere, is C1 with a Holder first jet on the closed ball, and
solves the correctly normalized cofactor equation in the open ball.
There is no assertion here that its second derivative extends to the sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall

theorem exists_dirichlet_closedBall_holder_rotation_jet {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hH : HasDirichletHolderOn α
      (fderivWithin ℝ (fderivWithin ℝ u (closedUnitBall n)) (closedUnitBall n))
      (closedUnitBall n)) (T : E n →L[ℝ] E n) :
    ∃ Q : E n → E n →L[ℝ] ℝ,
      HasDirichletHolderOn α Q (closedUnitBall n) ∧
      (∀ x ∈ closedUnitBall n, HasFDerivWithinAt
        (dirichletAngularDerivative T u) (Q x) (closedUnitBall n) x) ∧
      ContDiffOn ℝ 1 (dirichletAngularDerivative T u) (closedUnitBall n) := by
  let S := closedUnitBall n
  let G := fderivWithin ℝ u S
  let B := fderivWithin ℝ G S
  let Q (x : E n) := (G x).comp T + (B x).flip (T x)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hUnique : UniqueDiffOn ℝ S := uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
    ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hG : ContDiffOn ℝ 1 G S := hu.fderivWithin hUnique (by norm_num)
  have hGH : HasDirichletHolderOn α G S :=
    hasDirichletHolderOn_of_contDiffOn hS (convex_closedBall _ _) hG hα1
  have hTH : HasDirichletHolderOn α (fun x => T x) S :=
    hasDirichletHolderOn_of_contDiffOn hS (convex_closedBall _ _)
      T.contDiff.contDiffOn hα1
  have hBH : HasDirichletHolderOn α (fun x => (B x).flip) S :=
    hH.clm (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toContinuousLinearMap
  have hQ : HasDirichletHolderOn α Q S :=
    (hGH.clm_comp (HasDirichletHolderOn.const T) hS hα).add
      (hBH.clm_apply hTH hS hα) hS hα
  refine ⟨Q, hQ, ?_, hG.clm_apply T.contDiff.contDiffOn⟩
  intro x hx
  exact ((hG.differentiableOn (by norm_num) x hx).hasFDerivWithinAt).clm_apply
    T.hasFDerivAt.hasFDerivWithinAt

theorem dirichlet_closedBall_rotation_zero_on_sphere {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (T : E n →L[ℝ] E n) (hT : star T = -T) :
    ∀ x ∈ unitSphere n, dirichletAngularDerivative T u x = 0 := by
  intro x hx
  exact dirichlet_closedBall_firstJet_tangent_zero
    (fun y hy => (hu.differentiableOn (by norm_num) y hy).hasFDerivWithinAt) hu0 hx
    (inner_dirichlet_skew_field_self T hT x)

theorem contDiffOn_dirichletAngularDerivative_interior {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) (T : E n →L[ℝ] E n) :
    ContDiffOn ℝ ∞ (dirichletAngularDerivative T u) (unitBall n) := by
  refine ((hu.fderiv_of_isOpen isOpen_ball (by simp)).clm_apply T.contDiff.contDiffOn).congr ?_
  intro x hx
  unfold dirichletAngularDerivative
  have hN : closedUnitBall n ∈ 𝓝 x :=
    mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
  exact congrArg (fun L : E n →L[ℝ] ℝ => L (T x))
    (fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := u) hN)

theorem dirichlet_within_cofactor_rotation_equation {n : ℕ} {u f : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (T : E n →L[ℝ] E n) (hT : star T = -T)
    (hTJ : ∀ y, T (J y) = J (T y)) {x : E n} (hx : x ∈ unitBall n) :
    dirichletContractionCLM n (dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x))
      (realHessian (dirichletAngularDerivative T u) x) = fderiv ℝ f x (T x) := by
  have hN : closedUnitBall n ∈ 𝓝 x :=
    mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
  have hHC : dirichletWithinComplexHessian u x = complexHessian u x := by
    unfold dirichletWithinComplexHessian
    rw [fderivWithin_fderivWithin_eq_of_mem_nhds hN]
    exact complexHessianOfRealBilinear_eq
      ((hu.contDiffAt (isOpen_ball.mem_nhds hx)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have he : dirichletAngularDerivative T u =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y (T y)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    unfold dirichletAngularDerivative
    have hyN : closedUnitBall n ∈ 𝓝 y :=
      mem_of_superset (isOpen_ball.mem_nhds hy) ball_subset_closedBall
    exact congrArg (fun L : E n →L[ℝ] ℝ => L (T y))
      (fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := u) hyN)
  rw [hHC, show realHessian (dirichletAngularDerivative T u) x =
    realHessian (fun y => fderiv ℝ u y (T y)) x from he.fderiv.fderiv_eq]
  exact dirichlet_cofactor_rotation_equation_on_open isOpen_ball hu hEq T hT hTJ hx

end KEBall
