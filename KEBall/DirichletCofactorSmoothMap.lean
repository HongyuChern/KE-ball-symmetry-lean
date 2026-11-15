import KEBall.DirichletWeakDivergenceLimit
import KEBall.DirichletRankOneRecovery
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Smoothness and bounded-set Lipschitz control of the actual cofactor map

The adjugate is polynomial on all matrices.  This provides the coefficient
modulus required by interior Schauder estimates without assuming extra
regularity of the potential.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem contDiff_dirichlet_adjugate {n : ℕ} :
    ContDiff ℝ ∞ (Matrix.adjugate : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  rw [← contDiffOn_univ]
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_adjugate_of_contDiffOn_entries (A := id)
    (fun i j => (contDiff_apply_apply ℝ ℂ i j).contDiffOn) i j

theorem contDiff_dirichlet_hermitianRealification {n : ℕ} :
    ContDiff ℝ ∞ (@hermitianRealification n) := by
  unfold hermitianRealification
  apply ContDiff.const_smul (2 : ℝ)
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  have hij : ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) :=
    contDiff_apply_apply ℝ ℂ i j
  exact ((Complex.reCLM.contDiff.comp hij).smul contDiff_const).add
    ((Complex.imCLM.contDiff.comp hij).smul contDiff_const)

theorem contDiff_dirichletCofactorOfMatrix {n : ℕ} :
    ContDiff ℝ ∞ (@dirichletCofactorOfMatrix n) := by
  let R := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hR : ContDiff ℝ ∞ (fun B : E n →L[ℝ] E n →L[ℝ] ℝ => R.comp B) :=
    (ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n) R).contDiff
  exact (hR.comp (contDiff_dirichlet_hermitianRealification.comp
    contDiff_dirichlet_adjugate)).const_smul (8 : ℝ)⁻¹

theorem exists_dirichlet_cofactor_lipschitz_on_matrix_ball {n : ℕ} (R : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (@dirichletCofactorOfMatrix n)
      (closedBall 0 R) := by
  exact contDiff_dirichletCofactorOfMatrix.contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

end KEBall
