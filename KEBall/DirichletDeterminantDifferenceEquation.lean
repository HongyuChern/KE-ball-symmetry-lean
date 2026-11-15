import KEBall.DirichletProductDifferenceEquation
import KEBall.DirichletCofactorContraction
import KEBall.DirichletComplexHessianHolder

/-! The exact arbitrary-order difference equation for the actual determinant. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open scoped BigOperators Matrix.Norms.Elementwise

namespace KEBall

noncomputable def dirichletMatrixEntryCLM {m : ℕ} (i j : Fin m) :
    Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : (Fin m → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : Matrix (Fin m) (Fin m) ℂ →L[ℝ] (Fin m → ℂ))

theorem dirichletMatrixEntryCLM_apply {m : ℕ} (i j : Fin m) (M : Matrix (Fin m) (Fin m) ℂ) :
    dirichletMatrixEntryCLM i j M = M i j := rfl

noncomputable def dirichletDeterminantDifferenceCLM {m : ℕ}
    (M N : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℂ :=
  ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
    ∑ i : Fin m, ((∏ j ∈ Finset.univ with j < i, N (σ j) j) *
      (∏ j ∈ Finset.univ with i < j, M (σ j) j)) • dirichletMatrixEntryCLM (σ i) i

theorem dirichletDeterminantDifferenceCLM_apply {m : ℕ}
    (M N B : Matrix (Fin m) (Fin m) ℂ) :
    dirichletDeterminantDifferenceCLM M N B =
      ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
        ∑ i : Fin m, ((∏ j ∈ Finset.univ with j < i, N (σ j) j) *
          (∏ j ∈ Finset.univ with i < j, M (σ j) j)) * B (σ i) i := by
  simp only [dirichletDeterminantDifferenceCLM, ContinuousLinearMap.sum_apply,
    _root_.smul_apply, smul_eq_mul, dirichletMatrixEntryCLM_apply]

theorem dirichletIteratedFieldDifference_matrix_apply {n m : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (M : E n → Matrix (Fin m) (Fin m) ℂ)
    (k : ℕ) (x : E n) (i j : Fin m) :
    dirichletIteratedFieldDifference R τ (fun y => M y i j) k x =
      dirichletIteratedFieldDifference R τ M k x i j := by
  exact congrArg (fun f => f x)
    (dirichletIteratedFieldDifference_clm R τ (dirichletMatrixEntryCLM i j) M k)

noncomputable def dirichletDeterminantDifferenceRemainder {n m : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (M : E n → Matrix (Fin m) (Fin m) ℂ)
    (k : ℕ) (x : E n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
    dirichletProductDifferenceRemainder R τ Finset.univ (fun i y => M y (σ i) i) k x

theorem dirichletIteratedFieldDifference_determinant_eq {n m : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (M : E n → Matrix (Fin m) (Fin m) ℂ)
    (k : ℕ) (x : E n) :
    dirichletIteratedFieldDifference R τ (fun y => (M y).det) (k + 1) x =
      dirichletDeterminantDifferenceCLM (M (R^[k] x)) (M (R^[k + 1] x))
        (dirichletIteratedFieldDifference R τ M (k + 1) x) +
      dirichletDeterminantDifferenceRemainder R τ M k x := by
  classical
  have hDet : (fun y => (M y).det) = fun y =>
      ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤ) : ℂ)) * ∏ i : Fin m, M y (σ i) i := by
    funext y
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  rw [hDet, dirichletIteratedFieldDifference_finsetSum]
  simp only [dirichletIteratedFieldDifference_const_mul,
    dirichletIteratedFieldDifference_finsetProd_eq,
    dirichletProductDifferenceCoefficient, dirichletDeterminantDifferenceCLM_apply,
    dirichletDeterminantDifferenceRemainder, mul_add, Finset.sum_add_distrib,
    dirichletIteratedFieldDifference_matrix_apply]

theorem dirichlet_prod_lt_mul_prod_gt {ι A : Type*} [LinearOrder ι] [CommMonoid A]
    (s : Finset ι) (F : ι → A) (i : ι) :
    (∏ j ∈ s with j < i, F j) * (∏ j ∈ s with i < j, F j) = ∏ j ∈ s.erase i, F j := by
  classical
  have hd : Disjoint (s.filter (fun j => j < i)) (s.filter (fun j => i < j)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    exact lt_asymm (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hj').2
  rw [← Finset.prod_union hd]
  apply Finset.prod_congr
  · ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hj, hlt⟩ | ⟨hj, hgt⟩)
      · exact ⟨hlt.ne, hj⟩
      · exact ⟨hgt.ne', hj⟩
    · rintro ⟨hne, hj⟩
      rcases lt_or_gt_of_ne hne with hl | hr
      · exact Or.inl ⟨hj, hl⟩
      · exact Or.inr ⟨hj, hr⟩
  · intro j hj
    rfl

theorem hasFDerivAt_dirichletDeterminantDifference_same {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℂ) :
    HasFDerivAt Matrix.det (dirichletDeterminantDifferenceCLM M M) M := by
  classical
  have hProd (σ : Equiv.Perm (Fin m)) :
      HasFDerivAt (fun B : Matrix (Fin m) (Fin m) ℂ => ∏ i : Fin m, B (σ i) i)
        (∑ i : Fin m, (∏ j ∈ Finset.univ.erase i, M (σ j) j) •
          dirichletMatrixEntryCLM (σ i) i) M :=
    HasFDerivAt.finsetProd (fun i _ => (dirichletMatrixEntryCLM (σ i) i).hasFDerivAt)
  have hSum := HasFDerivAt.sum (u := Finset.univ) (fun σ _ =>
    (hProd σ).const_smul (((Equiv.Perm.sign σ : ℤ) : ℂ)))
  convert! hSum using 1
  · funext B
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.det_apply, Units.smul_def,
      zsmul_eq_mul]
  · simp only [dirichletDeterminantDifferenceCLM, dirichlet_prod_lt_mul_prod_gt]

theorem dirichletDeterminantDifferenceCLM_same_apply {m : ℕ}
    (M B : Matrix (Fin m) (Fin m) ℂ) :
    dirichletDeterminantDifferenceCLM M M B = (M.adjugate * B).trace := by
  rw [← (hasFDerivAt_dirichletDeterminantDifference_same M).fderiv]
  exact KEBallProbe.fderiv_real_complex_det M B

end KEBall
