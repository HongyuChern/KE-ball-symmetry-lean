import KEBall.DirichletHessianStability
import KEBall.DirichletCofactorHessian

/-! Compact bounds for the two matrix expressions in the stability estimate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix Matrix.Norms.Elementwise Topology

namespace KEBall

/-- Closed bounds on the entries and determinant give a common bound
for the inverse-Hessian pairing. -/
theorem exists_abs_trace_inverse_sub_bound {n : ℕ} {d C : ℝ} (hd : 0 < d) :
    ∃ K ≥ (0 : ℝ), ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      ‖A‖ ≤ C → ‖B‖ ≤ C → d ≤ B.det.re →
      |(B⁻¹ * (B - A)).trace.re| ≤ K := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let S : Set M := closedBall 0 C
  let T : Set M := S ∩ {B | d ≤ B.det.re}
  have hS : IsCompact S := isCompact_closedBall _ _
  have hT : IsCompact T := hS.inter_right (isClosed_le continuous_const
    (Complex.continuous_re.comp continuous_id.matrix_det))
  have hInv : ContinuousOn (Inv.inv : M → M) T := by
    intro B hB
    have hD : B.det ≠ 0 := by
      intro h
      have he : d ≤ B.det.re := hB.2
      rw [h, Complex.zero_re] at he
      exact (not_le_of_gt hd) he
    exact (continuousAt_matrix_inv B (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hD)).continuousWithinAt
  let p (z : M × M) := (z.2⁻¹ * (z.2 - z.1)).trace.re
  have hP : ContinuousOn p (S ×ˢ T) := by
    have hF : ContinuousOn (fun z : M × M => z.2⁻¹) (S ×ˢ T) :=
      hInv.comp continuous_snd.continuousOn (fun _ h => h.2)
    have hG : ContinuousOn (fun z : M × M => z.2 - z.1) (S ×ˢ T) :=
      (continuous_snd.sub continuous_fst).continuousOn
    apply Complex.continuous_re.comp_continuousOn
    simp only [Matrix.trace, Matrix.diag]
    apply continuousOn_finsetSum
    intro i _
    change ContinuousOn (fun z : M × M => ∑ j : Fin n, z.2⁻¹ i j * (z.2 - z.1) j i) (S ×ˢ T)
    exact continuousOn_finsetSum Finset.univ fun j _ =>
      (continuousOn_pi.mp (continuousOn_pi.mp hF i) j).mul
        (continuousOn_pi.mp (continuousOn_pi.mp hG j) i)
  obtain ⟨K, hK⟩ := (hS.prod hT).exists_bound_of_continuousOn hP
  exact ⟨max K 0, le_max_right _ _, fun A B hA hB hD =>
    (hK (A, B) ⟨mem_closedBall_zero_iff.mpr hA, mem_closedBall_zero_iff.mpr hB, hD⟩).trans
      (le_max_left _ _)⟩

set_option maxHeartbeats 500000 in
set_option maxSynthPendingDepth 8 in
/-- Bounded complex Hessian entries bound the real cofactor operators. -/
theorem exists_norm_dirichletCofactorOperator_bound {n : ℕ} (C : ℝ) :
    ∃ K ≥ (0 : ℝ), ∀ (u : E n → ℝ) (x : E n), ‖complexHessian u x‖ ≤ C →
      ‖dirichletCofactorOperator u x‖ ≤ K := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let R := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let T (A : M) := (8 : ℝ)⁻¹ • R.comp (hermitianRealification A.adjugate)
  have hA : Continuous (fun A : M => A.adjugate) := continuous_id.matrix_adjugate
  have hR : ContinuousOn (fun A : M => hermitianRealification A.adjugate) univ := by
    let U : Set M := univ
    let B (i j : Fin n) (A : M) : E n →L[ℝ] E n →L[ℝ] ℝ :=
      (A.adjugate i j).re • (coordinateProduct (realIndex i) (realIndex j) +
        coordinateProduct (imagIndex i) (imagIndex j)) +
      (A.adjugate i j).im • (coordinateProduct (realIndex i) (imagIndex j) -
        coordinateProduct (imagIndex i) (realIndex j))
    have hB (i j : Fin n) : ContDiffOn ℝ 0 (B i j) U := by
      have hEntry : Continuous (fun A : M => A.adjugate i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp hA)
      have hr : ContDiffOn ℝ 0 (fun A : M => (A.adjugate i j).re) U :=
        contDiffOn_zero.mpr (Complex.continuous_re.comp hEntry).continuousOn
      have hi : ContDiffOn ℝ 0 (fun A : M => (A.adjugate i j).im) U :=
        contDiffOn_zero.mpr (Complex.continuous_im.comp hEntry).continuousOn
      exact (hr.smul contDiffOn_const).add (hi.smul contDiffOn_const)
    have hSum : ContDiffOn ℝ 0 (fun A : M => ∑ i : Fin n, ∑ j : Fin n, B i j A) U :=
      ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => hB i j
    exact ((contDiffOn_const (c := (2 : ℝ))).smul hSum).continuousOn
  have hT : ContinuousOn T (closedBall (0 : M) C) :=
    ((continuous_const_smul _).comp_continuousOn
      ((ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n) R).continuous.comp_continuousOn
        hR)).mono (subset_univ _)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : M) C).exists_bound_of_continuousOn hT
  exact ⟨max K 0, le_max_right _ _, fun u x hx =>
    (hK (complexHessian u x) (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _)⟩

end KEBall
