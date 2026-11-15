import KEBall.EquationBasics
import Mathlib.Topology.Order.OrderClosed

/-!
# Positivity reaches the boundary

Interior positive definiteness first gives semidefiniteness on the closed
ball. The actual equation supplies a nonzero determinant there. This proves
the boundary positivity stated in the manuscript without strengthening
`IsSolution`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff BigOperators ComplexOrder Topology

namespace KEBall

theorem IsSolution.hessian_isHermitian_closedBall {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) :
    (complexHessian u x).IsHermitian := by
  have he (i j : Fin n) : ContinuousOn (fun y => complexHessian u y i j)
      (closedUnitBall n) :=
    continuousOn_pi.mp (continuousOn_pi.mp hu.hessian_continuousOn_closedBall i) j
  ext i j
  change star (complexHessian u x j i) = complexHessian u x i j
  have hEq : Set.EqOn (fun y => star (complexHessian u y j i))
      (fun y => complexHessian u y i j) (unitBall n) := by
    intro y hy
    exact (hu.2.2.1 y hy).isHermitian.apply i j
  apply hEq.of_subset_closure (he j i).star (he i j)
    Metric.ball_subset_closedBall ?_ hx
  rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
  exact Set.Subset.rfl

theorem IsSolution.hessian_posSemidef_closedBall {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) :
    (complexHessian u x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hu.hessian_isHermitian_closedBall hx, ?_⟩
  intro v
  have he (i j : Fin n) : ContinuousOn (fun y => complexHessian u y i j)
      (closedUnitBall n) :=
    continuousOn_pi.mp (continuousOn_pi.mp hu.hessian_continuousOn_closedBall i) j
  have hq : ContinuousOn (fun y => star v ⬝ᵥ ((complexHessian u y).mulVec v))
      (closedUnitBall n) := by
    simp only [dotProduct, Matrix.mulVec]
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro j _
    exact (he i j).mul continuousOn_const
  have hxcl : x ∈ closure (unitBall n) := by
    simpa only [unitBall, closedUnitBall,
      closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)] using hx
  have : (𝓝[Metric.ball (0 : E n) 1] x).NeBot := mem_closure_iff_clusterPt.mp hxcl
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    ((hq x hx).mono Metric.ball_subset_closedBall)
    (Filter.eventually_of_mem self_mem_nhdsWithin
      (fun y hy => (hu.2.2.1 y hy).posSemidef.dotProduct_mulVec_nonneg v))

theorem posDef_of_posSemidef_of_det_ne_zero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hd : A.det ≠ 0) : A.PosDef := by
  apply hA.isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  have he : hA.isHermitian.eigenvalues i ≠ 0 := by
    intro hi
    apply hd
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm he)

theorem IsSolution.hessian_posDef_closedBall {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {x : E n} (hx : x ∈ closedUnitBall n) :
    (complexHessian u x).PosDef :=
  posDef_of_posSemidef_of_det_ne_zero (hu.hessian_posSemidef_closedBall hx)
    (isUnit_iff_ne_zero.mp (hu.det_isUnit_closedBall hx))

end KEBall
