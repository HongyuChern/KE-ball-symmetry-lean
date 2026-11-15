import KEBall.DirichletSobolevBound
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Controlling the norm of a derivative by its orthonormal components. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace KEBall

theorem ContinuousMultilinearMap.norm_le_sum_orthonormalBasis {n k : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E n) F)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) :
    ‖T‖ ≤ ∑ i : Fin k → Fin (2 * n), ‖T (fun j => b (i j))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro m
  let r (j : Fin k) (i : Fin (2 * n)) := b.repr (m j) i
  have hm : m = fun j => ∑ i, r j i • b i := funext fun j => (b.sum_repr (m j)).symm
  have hNorm (j : Fin k) (i : Fin (2 * n)) : ‖r j i‖ ≤ ‖m j‖ := by
    exact (PiLp.norm_apply_le (b.repr (m j)) i).trans_eq (b.repr.norm_map (m j))
  calc
    ‖T m‖ = ‖∑ i : Fin k → Fin (2 * n), (∏ j, r j (i j)) • T (fun j => b (i j))‖ := by
      congr 1
      have h := T.toMultilinearMap.map_sum (fun j i => r j i • b i)
      simp only [ContinuousMultilinearMap.coe_coe, MultilinearMap.map_smul_univ] at h
      simpa only [← hm] using h
    _ ≤ ∑ i : Fin k → Fin (2 * n), ‖(∏ j, r j (i j)) • T (fun j => b (i j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin k → Fin (2 * n), (∏ j, ‖m j‖) * ‖T (fun j => b (i j))‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, norm_prod]
      gcongr with j _
      exact hNorm j (i j)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

theorem iteratedFDeriv_eq_foldr_directions {n k : ℕ} {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : Fin k → E n) (x : E n) :
    iteratedFDeriv ℝ k f x v = (List.ofFn v).foldr (fun d C y => fderiv ℝ C y d) f x := by
  induction k generalizing x with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
      have hD : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
        hf.differentiable_iteratedFDeriv (show (k : ℕ∞ω) < ∞ from WithTop.coe_lt_coe.mpr
          (ENat.natCast_lt_top k))
      rw [(hD x).iteratedFDeriv_succ_apply_left', List.ofFn_succ]
      simp only [List.foldr_cons]
      exact congrArg (fun g : E n → ℝ => fderiv ℝ g x (v 0))
        (funext fun y => ih (Fin.tail v) y)

end KEBall
