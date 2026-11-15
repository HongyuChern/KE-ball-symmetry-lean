import KEBall.DirichletSchauderPositiveMatrix
import KEBall.DirichletSchauderCoefficientExtension

/-!
# A scale satisfying the actual Schauder absorption condition

The imported defect constant is homogeneous in the two source bounds.
Consequently the common factor r^alpha produced by spatial rescaling
makes the defect smaller than one for every positive Holder exponent.
This verifies the smallness hypothesis; it is not a regularity theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal Topology

namespace KEBall

theorem lipschitzWith_dirichletSchauderMatrix_entry {n : ℕ} (i j : Fin (2 * n)) :
    LipschitzWith 1 (fun A : E n →L[ℝ] E n => dirichletSchauderMatrix A i j) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    abs_dirichletSchauderMatrix_sub_le A B i j

theorem holderOnWith_dirichletSchauderMatrix_entry {n : ℕ} {S : Set (E n)}
    {A : E n → E n →L[ℝ] E n} {K α : ℝ≥0} (hA : HolderOnWith K α A S)
    (i j : Fin (2 * n)) :
    HolderOnWith K α (fun x => dirichletSchauderMatrix (A x) i j) S := by
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] using
    (lipschitzWith_dirichletSchauderMatrix_entry i j).holderWith.comp_holderOnWith hA

theorem abs_dirichletSchauderMatrix_le {n : ℕ} (A : E n →L[ℝ] E n)
    (i j : Fin (2 * n)) : |dirichletSchauderMatrix A i j| ≤ ‖A‖ := by
  simpa only [dirichletSchauderMatrix, map_zero, ContinuousLinearMap.zero_apply,
    inner_zero_right, sub_zero] using abs_dirichletSchauderMatrix_sub_le A 0 i j

theorem exists_dirichlet_schauder_absorption_scale {n : ℕ}
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hA : A.PosDef)
    (α K B R : ℝ≥0) (hα : 0 < α) (hR : 0 < R) :
    ∃ r : ℝ≥0, 0 < r ∧ r < R ∧
      spdLaplacianSchauderDefectConst A hA α
        (r ^ (α : ℝ) * K) (r ^ (α : ℝ) * B) < 1 := by
  let D := spdLaplacianSchauderDefectConst A hA α K B
  have hlim : Tendsto (fun r : ℝ≥0 => r ^ (α : ℝ) * D) (𝓝[>] 0) (𝓝 0) := by
    simpa only [NNReal.zero_rpow (show (α : ℝ) ≠ 0 from ne_of_gt hα), zero_mul] using
      (((NNReal.continuous_rpow_const α.coe_nonneg).mul_const D).continuousAt
        (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ≥0 in 𝓝[>] 0, r < R :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const hR
  obtain ⟨r, hr, hsmall, hrR⟩ :=
    (eventually_mem_nhdsWithin.and ((hlim.eventually (gt_mem_nhds zero_lt_one)).and hlt)).exists
  refine ⟨r, hr, hrR, ?_⟩
  rw [spdLaplacianSchauderDefectConst_nnreal_mul]
  exact hsmall

end KEBall
