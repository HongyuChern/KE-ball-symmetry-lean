import KEBall.DirichletUniformEllipticity
import KEBall.DirichletPositiveTraceRatio

/-! Spectral and ellipticity bounds from the complex trace and determinant.
No bound on the full real Hessian is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

open Matrix Metric Set
open scoped BigOperators ComplexOrder ContDiff

namespace KEBall

theorem eigenvalues_bounds_of_posDef_det_trace {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    {d D : ℝ} (hD : 0 < D) (hdet : d ≤ A.det.re) (htrace : A.trace.re ≤ D)
    (i : Fin n) :
    d / D ^ (n - 1) ≤ hA.isHermitian.eigenvalues i ∧
      hA.isHermitian.eigenvalues i ≤ D := by
  have htr : A.trace.re = ∑ j, hA.isHermitian.eigenvalues j := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    rfl
  have hUp (j : Fin n) : hA.isHermitian.eigenvalues j ≤ D := by
    apply le_trans ?_ htrace
    rw [htr]
    exact Finset.single_le_sum (fun k _ => (hA.eigenvalues_pos k).le) (Finset.mem_univ j)
  have hProd : A.det.re = ∏ j, hA.isHermitian.eigenvalues j := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    rfl
  have hErase : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      hA.isHermitian.eigenvalues j) ≤ D ^ (n - 1) := by
    calc
      _ ≤ ∏ _j ∈ (Finset.univ : Finset (Fin n)).erase i, D :=
        Finset.prod_le_prod (fun j _ => (hA.eigenvalues_pos j).le) (fun j _ => hUp j)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
  refine ⟨(div_le_iff₀ (pow_pos hD _)).mpr ?_, hUp i⟩
  rw [hProd, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)] at hdet
  exact hdet.trans (mul_le_mul_of_nonneg_left hErase (hA.eigenvalues_pos i).le)

/-- The eigenvalue interval follows from the actual closed-ball determinant
and trace. In particular, no real Hessian upper bound is a hypothesis. -/
theorem complexHessian_eigenvalues_bounds_of_det_trace {n : ℕ}
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {a D : ℝ} (ha : 0 < a) (hD : 0 < D)
    (hDensity : ∀ y ∈ closedUnitBall n, a ^ n ≤ f y)
    (hTrace : ∀ y ∈ closedUnitBall n, (complexHessian u y).trace.re ≤ D)
    {x : E n} (hx : x ∈ closedUnitBall n) (i : Fin n) :
    let hA := (dirichlet_posDef_on_closedBall hu hf huP hEq ha
      (fun y hy => hDensity y (ball_subset_closedBall hy)) hx).isHermitian
    a ^ n / D ^ (n - 1) ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ D := by
  apply eigenvalues_bounds_of_posDef_det_trace
    (dirichlet_posDef_on_closedBall hu hf huP hEq ha
      (fun y hy => hDensity y (ball_subset_closedBall hy)) hx) hD
  · rw [dirichlet_det_eq_on_closedBall hu hf huP hEq hx]
    exact hDensity x hx
  · exact hTrace x hx

theorem complexLaplacian_rankOne_bounds_of_det_trace {n : ℕ}
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {a D : ℝ} (ha : 0 < a) (hD : 0 < D)
    (hDensity : ∀ y ∈ closedUnitBall n, a ^ n ≤ f y)
    (hTrace : ∀ y ∈ closedUnitBall n, (complexHessian u y).trace.re ≤ D)
    {x : E n} (hx : x ∈ closedUnitBall n) (v : E n) :
    (D⁻¹ / 4) * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x ∧
      complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x ≤
        ((a ^ n / D ^ (n - 1))⁻¹ / 4) * ‖v‖ ^ 2 := by
  exact complexLaplacian_rankOne_bounds
    (dirichlet_posDef_on_closedBall hu hf huP hEq ha
      (fun y hy => hDensity y (ball_subset_closedBall hy)) hx)
    (by positivity : 0 < a ^ n / D ^ (n - 1))
    (complexHessian_eigenvalues_bounds_of_det_trace hu hf huP hEq ha hD hDensity hTrace hx) v

end KEBall
