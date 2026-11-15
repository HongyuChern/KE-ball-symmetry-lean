import KEBall.DirichletDeterminantDifferenceEquation
import KEBall.DirichletBoundedBilinear

/-!
# Uniform convergence of the arbitrary-order leading determinant coefficient

The coefficient acts on the actual real Hessian space. At zero step it is
exactly the original cofactor contraction, including its fixed normalization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix Metric Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

theorem continuous_dirichletDeterminantDifferenceCLM {m : ℕ} :
    Continuous (fun p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ =>
      dirichletDeterminantDifferenceCLM p.1 p.2) := by
  unfold dirichletDeterminantDifferenceCLM
  fun_prop

noncomputable def dirichletRealDeterminantDifferenceCLM {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℂ) : (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((dirichletDeterminantDifferenceCLM M N).comp dirichletComplexHessianCLM)

theorem dirichletRealDeterminantDifferenceCLM_same {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    dirichletRealDeterminantDifferenceCLM M M =
      dirichletContractionCLM n (dirichletCofactorOfMatrix M) := by
  ext H
  simp only [dirichletRealDeterminantDifferenceCLM, ContinuousLinearMap.comp_apply,
    dirichletDeterminantDifferenceCLM_same_apply, Complex.reCLM_apply,
    dirichletComplexHessianCLM_apply, dirichletContractionCLM_apply,
    dirichletBilinearContraction_cofactor]

theorem continuous_dirichletRealDeterminantDifferenceCLM {n : ℕ} :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      dirichletRealDeterminantDifferenceCLM p.1 p.2) :=
  continuous_const.clm_comp (continuous_dirichletDeterminantDifferenceCLM.clm_comp continuous_const)

theorem orthogonalFlow_iterate_mapsTo_closedUnitBall {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t : ℝ) (k : ℕ)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    (orthogonalFlow S hS t)^[k] x ∈ closedUnitBall n := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact orthogonalFlow_mapsTo_closedUnitBall S hS t ih

theorem continuous_orthogonalFlow_iterate_closedBall {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    Continuous (fun p : ℝ × closedUnitBall n => (orthogonalFlow S hS p.1)^[k] p.2) := by
  have hL : Continuous (fun t : ℝ => NormedSpace.exp (t • S)) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exp_smul_const S t).continuousAt)
  induction k with
  | zero => exact continuous_subtype_val.comp continuous_snd
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact (hL.comp continuous_fst).clm_apply ih

theorem orthogonalFlow_zero_iterate_apply {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) (x : E n) :
    (orthogonalFlow S hS 0)^[k] x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', orthogonalFlow_zero_apply, ih]

theorem continuous_field_orthogonalFlow_iterate_closedBall {n : ℕ} {V : Type*}
    [TopologicalSpace V] {F : E n → V} (hF : ContinuousOn F (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    Continuous (fun p : ℝ × closedUnitBall n => F ((orthogonalFlow S hS p.1)^[k] p.2)) := by
  have hO := continuous_orthogonalFlow_iterate_closedBall S hS k
  have hOS : Continuous (fun p : ℝ × closedUnitBall n =>
      (⟨(orthogonalFlow S hS p.1)^[k] p.2,
        orthogonalFlow_iterate_mapsTo_closedUnitBall S hS p.1 k p.2.property⟩ : closedUnitBall n)) :=
    hO.subtype_mk _
  exact hF.domRestrict.comp hOS

theorem continuous_dirichletDeterminantLeadingField {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) :
    Continuous (fun p : ℝ × closedUnitBall n =>
      dirichletRealDeterminantDifferenceCLM
        (dirichletWithinComplexHessian u ((orthogonalFlow S hS p.1)^[k] p.2))
        (dirichletWithinComplexHessian u ((orthogonalFlow S hS p.1)^[k + 1] p.2))) := by
  have hOrbit (j : ℕ) : Continuous (fun p : ℝ × closedUnitBall n =>
      dirichletWithinComplexHessian u ((orthogonalFlow S hS p.1)^[j] p.2)) :=
    continuous_field_orthogonalFlow_iterate_closedBall
      (continuousOn_dirichletWithinComplexHessian_of_C2 hu) S hS j
  convert! (continuous_dirichletRealDeterminantDifferenceCLM (n := n)).comp
    ((hOrbit k).prodMk (hOrbit (k + 1))) using 1

theorem eventually_dirichletDeterminantLeadingField_close {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ closedUnitBall n,
      ‖dirichletContractionCLM n (dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x)) -
        dirichletRealDeterminantDifferenceCLM
          (dirichletWithinComplexHessian u ((orthogonalFlow S hS t)^[k] x))
          (dirichletWithinComplexHessian u ((orthogonalFlow S hS t)^[k + 1] x))‖ < ε := by
  let : CompactSpace (closedUnitBall n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let F (t : ℝ) (x : closedUnitBall n) :=
    dirichletRealDeterminantDifferenceCLM
      (dirichletWithinComplexHessian u ((orthogonalFlow S hS t)^[k] x))
      (dirichletWithinComplexHessian u ((orthogonalFlow S hS t)^[k + 1] x))
  have hF : Continuous F.uncurry := continuous_dirichletDeterminantLeadingField hu S hS k
  have hT : TendstoUniformly F (F 0) (𝓝 (0 : ℝ)) := Continuous.tendstoUniformly F hF 0
  filter_upwards [Metric.tendstoUniformly_iff.mp hT ε hε] with t ht x hx
  have h := ht (⟨x, hx⟩ : closedUnitBall n)
  simpa only [F, orthogonalFlow_zero_iterate_apply, dirichletRealDeterminantDifferenceCLM_same,
    dist_eq_norm] using h

end KEBall
