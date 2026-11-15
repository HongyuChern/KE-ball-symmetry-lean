import KEBall.DirichletRemainderMonomials
import KEBall.DirichletTameFunctionSpace
import KEBall.DirichletPolynomialRemainderEnergy

/-! The exact determinant remainder has an arbitrarily small coefficient on the highest Hessian energy. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000

open MeasureTheory Metric Set
open scoped BigOperators ContDiff

namespace KEBall

noncomputable def dirichletFlowHessianEnergy {n : ℕ} (u : E n → ℝ)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x in unitBall n,
    ‖dirichletWithinRealHessian (dirichletIteratedOrthogonalDifference (orthogonalFlow S hS t) t u k) x‖ ^ 2 ∂volume0 n

noncomputable def dirichletFlowLowerHessianEnergy {n : ℕ} (u : E n → ℝ)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, dirichletFlowHessianEnergy u S hS j t

theorem dirichletFlowHessianEnergy_nonneg {n : ℕ} (u : E n → ℝ)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) (t : ℝ) :
    0 ≤ dirichletFlowHessianEnergy u S hS k t :=
  integral_nonneg (fun _ => sq_nonneg _)

noncomputable def dirichletFlowFamilyRestriction {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ((E n ≃ₗᵢ[ℝ] E n) → ℝ → E n → ℂ) →ₗ[ℝ] (ℝ → E n → ℂ) where
  toFun F t x := F (orthogonalFlow S hS t) t x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem dirichlet_orthogonal_pow_apply {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) (k : ℕ) (x : E n) :
    (R ^ k) x = R^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, LinearIsometryEquiv.coe_mul, Function.comp_apply, ih, Function.iterate_succ_apply]

theorem dirichletProperDifferenceSpan_tame {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℂ)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    {G : (E n ≃ₗᵢ[ℝ] E n) → ℝ → E n → ℂ}
    (hG : G ∈ dirichletProperDifferenceSpan s (fun i y => L i (dirichletWithinRealHessian u y)) k) :
    dirichletFlowFamilyRestriction S hS G ∈
      dirichletTameFunctionSpace hn (dirichletFlowHessianEnergy u S hS k)
        (dirichletFlowLowerHessianEnergy u S hS k) (dirichletFlowHessianEnergy_nonneg u S hS k) := by
  classical
  let F (i : ι) (y : E n) := L i (dirichletWithinRealHessian u y)
  let T := dirichletTameFunctionSpace hn (dirichletFlowHessianEnergy u S hS k)
    (dirichletFlowLowerHessianEnergy u S hS k) (dirichletFlowHessianEnergy_nonneg u S hS k)
  have hLe : dirichletProperDifferenceSpan s F k ≤ T.comap (dirichletFlowFamilyRestriction S hS) := by
    apply Submodule.span_le.mpr
    rintro G ⟨j, a, hSum, hj, rfl⟩
    change dirichletFlowFamilyRestriction S hS (fun R τ x => dirichletDifferenceMonomial R τ s F j a x) ∈ T
    constructor
    · intro t ht
      exact continuousOn_finsetProd s (fun i _ =>
        continuousOn_dirichlet_orthogonal_iterate_comp (orthogonalFlow S hS t)
          (continuousOn_dirichletIteratedFieldDifference (orthogonalFlow S hS t) t
            ((L i).continuous.comp_continuousOn (continuousOn_dirichletWithinRealHessian hu)) (j i)) (a i))
    · intro ε hε
      let Λ := ∑ i ∈ s, ‖L i‖
      have hΛ : 0 ≤ Λ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      have hL (i : ι) (hi : i ∈ s) : ‖L i‖ ≤ Λ := Finset.single_le_sum (fun _ _ => norm_nonneg _) hi
      obtain ⟨C, hC, hBound⟩ := exists_dirichlet_hessian_monomial_tame_bound hn hk s j hj hSum hu huS hu0 S hS hΛ hε
      refine ⟨C, hC, ?_⟩
      intro t ht
      let R := orthogonalFlow S hS t
      have hD (i : ι) (x : E n) : dirichletIteratedFieldDifference R t (F i) (j i) x =
          L i (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (j i) x) :=
        congrArg (fun f => f x) (dirichletIteratedFieldDifference_clm R t (L i) (dirichletWithinRealHessian u) (j i))
      have hEq (x : E n) : ‖dirichletDifferenceMonomial R t s F j a x‖ ^ 2 =
          ∏ i ∈ s, ‖L i (dirichletIteratedFieldDifference R t (dirichletWithinRealHessian u) (j i) ((R ^ a i) x))‖ ^ 2 := by
        simp only [dirichletDifferenceMonomial, norm_prod, ← Finset.prod_pow, hD, dirichlet_orthogonal_pow_apply]
      have h := hBound t ht (fun i => R ^ a i) L hL
      dsimp only at h
      change (∫ x in unitBall n, ‖dirichletDifferenceMonomial R t s F j a x‖ ^ 2 ∂volume0 n) ≤ _
      simp only [hEq]
      exact h
  exact hLe hG

theorem dirichletProductDifferenceRemainder_tame {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (L : ι → (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] ℂ)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    (fun t x => dirichletProductDifferenceRemainder (orthogonalFlow S hS t) t s
      (fun i y => L i (dirichletWithinRealHessian u y)) k x) ∈
      dirichletTameFunctionSpace hn (dirichletFlowHessianEnergy u S hS (k + 1))
        (dirichletFlowLowerHessianEnergy u S hS (k + 1)) (dirichletFlowHessianEnergy_nonneg u S hS (k + 1)) := by
  exact dirichletProperDifferenceSpan_tame hn (by omega) s L hu huS hu0 S hS
    (dirichletProductDifferenceRemainder_mem_properSpan s _ k)

theorem dirichletDeterminantDifferenceRemainder_tame {n k : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    (fun t x => dirichletDeterminantDifferenceRemainder (orthogonalFlow S hS t) t
      (dirichletWithinComplexHessian u) k x) ∈
      dirichletTameFunctionSpace hn (dirichletFlowHessianEnergy u S hS (k + 1))
        (dirichletFlowLowerHessianEnergy u S hS (k + 1)) (dirichletFlowHessianEnergy_nonneg u S hS (k + 1)) := by
  classical
  let T := dirichletTameFunctionSpace hn (dirichletFlowHessianEnergy u S hS (k + 1))
    (dirichletFlowLowerHessianEnergy u S hS (k + 1)) (dirichletFlowHessianEnergy_nonneg u S hS (k + 1))
  by_cases hk : k = 0
  · subst k
    have hZero : (fun t x => dirichletDeterminantDifferenceRemainder (orthogonalFlow S hS t) t
        (dirichletWithinComplexHessian u) 0 x) = (0 : ℝ → E n → ℂ) := by
      funext t x
      simp only [dirichletDeterminantDifferenceRemainder, dirichletProductDifferenceRemainder,
        mul_zero, Finset.sum_const_zero, Pi.zero_apply]
    rw [hZero]
    exact T.zero_mem
  have hk1 : 1 ≤ k := by omega
  let F (σ : Equiv.Perm (Fin n)) (t : ℝ) (x : E n) :=
    dirichletProductDifferenceRemainder (orthogonalFlow S hS t) t Finset.univ
      (fun i y => dirichletWithinComplexHessian u y (σ i) i) k x
  have hF (σ : Equiv.Perm (Fin n)) : F σ ∈ T := by
    exact dirichletProductDifferenceRemainder_tame hn hk1 Finset.univ
      (fun i => (dirichletMatrixEntryCLM (σ i) i).comp dirichletComplexHessianCLM) hu huS hu0 S hS
  have hSum : (∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤ) : ℝ)) • F σ) ∈ T :=
    Submodule.sum_mem _ (fun σ _ => T.smul_mem _ (hF σ))
  convert! hSum using 1
  funext t x
  simp only [dirichletDeterminantDifferenceRemainder, F, Finset.sum_apply, Pi.smul_apply,
    Complex.real_smul, Complex.ofReal_intCast]

theorem exists_dirichlet_determinant_remainder_tame_bound {n : ℕ} (hn : 0 < n)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 →
      (∫ x in unitBall n,
        ‖dirichletDeterminantDifferenceRemainder (orthogonalFlow S hS t) t
          (dirichletWithinComplexHessian u) k x‖ ^ 2 ∂volume0 n) ≤
        ε * dirichletFlowHessianEnergy u S hS (k + 1) t +
          C * dirichletFlowLowerHessianEnergy u S hS (k + 1) t + C :=
  (dirichletDeterminantDifferenceRemainder_tame hn hu huS hu0 S hS).2 ε hε

end KEBall
