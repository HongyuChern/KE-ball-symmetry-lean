import KEBall.HermitianRealification
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! Basic consequences of the original equation, including its continuous
extension to the boundary. None is added to the definition of a solution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff BigOperators

namespace KEBall

theorem IsSolution.contDiffOn_ball {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) : ContDiffOn ℝ ∞ u (unitBall n) := by
  intro x hx
  exact (hu.2.1.contDiffAt (Metric.ball_subset_closedBall hx)).contDiffWithinAt

theorem IsSolution.hessian_continuousOn_closedBall {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) :
    ContinuousOn (complexHessian u) (closedUnitBall n) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu.2.1
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (complexHessian_contDiffOn hU huU i j).continuousOn.mono hKU

theorem IsSolution.det_eq_on_closedBall {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) :
    (complexHessian u x).det = (μ * Real.exp (-u x) : ℂ) := by
  have hf : ContinuousOn (fun y => (complexHessian u y).det) (closedUnitBall n) :=
    continuous_id.matrix_det.comp_continuousOn hu.hessian_continuousOn_closedBall
  have hur : ContinuousOn u (closedUnitBall n) := by
    intro y hy
    exact (hu.2.1.contDiffAt hy).continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun y => (μ * Real.exp (-u y) : ℂ)) (closedUnitBall n) :=
    by
      have hr : ContinuousOn (fun y => μ * Real.exp (-u y)) (closedUnitBall n) :=
        continuousOn_const.mul (Real.continuous_exp.comp_continuousOn hur.neg)
      simpa only [Function.comp_def, Complex.ofReal_mul] using
        Complex.continuous_ofReal.comp_continuousOn hr
  apply Set.EqOn.of_subset_closure hu.2.2.2.1 hf hg
    Metric.ball_subset_closedBall ?_ hx
  rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
  exact Set.Subset.rfl

theorem IsSolution.det_eq_on_sphere {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ unitSphere n) :
    (complexHessian u x).det = (μ : ℂ) := by
  rw [hu.det_eq_on_closedBall (Metric.sphere_subset_closedBall hx), hu.2.2.2.2 x hx]
  simp

theorem IsSolution.det_isUnit_closedBall {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) :
    IsUnit (complexHessian u x).det := by
  rw [hu.det_eq_on_closedBall hx]
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast mul_ne_zero (ne_of_gt hu.1) (Real.exp_ne_zero (-u x))

theorem complexLaplacian_self_of_isUnit {n : ℕ} {u : E n → ℝ} {x : E n}
    (hunit : IsUnit (complexHessian u x).det) :
    complexLaplacian u u x = (n : ℝ) := by
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
      (complexHessian u x)⁻¹ j i * complexHessian u x i j) = (n : ℂ) := by
    rw [Finset.sum_comm]
    change Matrix.trace ((complexHessian u x)⁻¹ * complexHessian u x) = _
    rw [Matrix.nonsing_inv_mul _ hunit]
    simp
  unfold complexLaplacian inverseCoefficient
  rw [hsum]
  simp

theorem IsSolution.complexLaplacian_self {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) :
    complexLaplacian u u x = (n : ℝ) :=
  complexLaplacian_self_of_isUnit (hu.det_isUnit_closedBall hx)

end KEBall
