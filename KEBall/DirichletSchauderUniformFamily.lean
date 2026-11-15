import KEBall.DirichletSchauderUniformConstants

/-!
# One Schauder normalization scale for an entire elliptic family

All quantifiers on the coefficient index occur after the physical radius
has been selected.  This is the order needed for difference quotients.
The coefficient entries, the double-sum defect, and the factor r^alpha
are exactly those used in the imported Schauder estimate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped BigOperators NNReal BoundedContinuousFunction

namespace KEBall

theorem exists_dirichlet_normalized_coefficients_at_scale {n : ℕ}
    (p : E n) (R r K α M : ℝ≥0) (hrR : r ≤ R) (hα : 0 < α)
    {A : E n → E n →L[ℝ] E n}
    (hA : HolderOnWith K α A (closedBall p R))
    (hM : ∀ x ∈ closedBall p R, ‖A x‖ ≤ M) :
    ∃ a : Fin (2 * n) → Fin (2 * n) → BoundedContinuousFunction (E n) ℝ,
      (∀ i j, a i j 0 = dirichletSchauderMatrix (A p) i j) ∧
      (∀ i j x, x ∈ closedBall (0 : E n) 1 →
        a i j x = dirichletSchauderMatrix (A (p + (r : ℝ) • x)) i j) ∧
      (∀ i j, HolderWith (K * r ^ (α : ℝ)) α (a i j : E n → ℝ)) ∧
      (∀ i j, ‖a i j‖ ≤ M) ∧
      ∀ i j x, ‖a i j 0 - a i j x‖ ≤ (K * r ^ (α : ℝ) : ℝ≥0) := by
  classical
  have hSub : closedBall p ((r : ℝ) * (1 : ℝ≥0)) ⊆ closedBall p R :=
    closedBall_subset_closedBall (by
      simp only [NNReal.coe_one, mul_one]
      exact_mod_cast hrR)
  have hScalar (i j : Fin (2 * n)) :=
    (holderOnWith_dirichletSchauderMatrix_entry hA i j).mono hSub
  have hScalarBound (i j : Fin (2 * n)) :
      ∀ x ∈ closedBall p ((r : ℝ) * (1 : ℝ≥0)),
        ‖dirichletSchauderMatrix (A x) i j‖ ≤ M := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact (abs_dirichletSchauderMatrix_le (A x) i j).trans (hM x (hSub hx))
  choose a haEq haOn haHolder haM haOsc using
    fun i j => exists_dirichlet_scaled_holder_coefficient_extension
      p r 1 K α M hα (hScalar i j) (hScalarBound i j)
  have hCenter (i j : Fin (2 * n)) :
      a i j 0 = dirichletSchauderMatrix (A p) i j := by
    rw [haEq]
    simp only [ballRetraction, norm_zero, div_zero, smul_zero, add_zero]
  refine ⟨a, hCenter, haOn, haHolder, haM, ?_⟩
  intro i j x
  rw [hCenter, norm_sub_rev]
  simpa only [NNReal.coe_one, mul_one, NNReal.coe_mul, NNReal.coe_rpow] using haOsc i j x

theorem exists_dirichlet_uniform_normalized_schauder_family {n : ℕ} {I : Type*}
    (p : E n) (R K α M : ℝ≥0) (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (A : I → E n → E n →L[ℝ] E n)
    (hA : ∀ s, HolderOnWith K α (A s) (closedBall p R))
    (hM : ∀ s, ∀ x ∈ closedBall p R, ‖A s x‖ ≤ M)
    (hAp : ∀ s, (dirichletSchauderMatrix (A s p)).PosDef)
    {l : ℝ} (hl : 0 < l)
    (hEll : ∀ s, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A s p v) v) :
    ∃ r : ℝ≥0, 0 < r ∧ r < R ∧
      ∀ s, ∃ a : Fin (2 * n) → Fin (2 * n) → BoundedContinuousFunction (E n) ℝ,
        (∀ i j, a i j 0 = dirichletSchauderMatrix (A s p) i j) ∧
        (∀ i j x, x ∈ closedBall (0 : E n) 1 →
          a i j x = dirichletSchauderMatrix (A s (p + (r : ℝ) • x)) i j) ∧
        (∀ i j, HolderWith (K * r ^ (α : ℝ)) α (a i j : E n → ℝ)) ∧
        (∀ i j, ‖a i j‖ ≤ M) ∧
        (∀ i j x, ‖a i j 0 - a i j x‖ ≤ (K * r ^ (α : ℝ) : ℝ≥0)) ∧
        spdLaplacianSchauderDefectConst (dirichletSchauderMatrix (A s p)) (hAp s) α
          (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n),
            (K * r ^ (α : ℝ) + K * r ^ (α : ℝ)))
          (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), K * r ^ (α : ℝ)) < 1 / 2 := by
  let L : ℝ≥0 := Real.toNNReal (Real.sqrt (M : ℝ))
  let Q : ℝ≥0 := Real.toNNReal (Real.sqrt l)⁻¹
  have hL (s : I) :
      ‖(spdSqrtEquiv (dirichletSchauderMatrix (A s p)) (hAp s) : E n →L[ℝ] E n)‖₊ ≤ L := by
    change ‖(spdSqrtEquiv (dirichletSchauderMatrix (A s p)) (hAp s) : E n →L[ℝ] E n)‖ ≤ (L : ℝ)
    rw [show (L : ℝ) = Real.sqrt (M : ℝ) from Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    exact norm_dirichletSchauderSqrt_le (hAp s) M.coe_nonneg
      (hM s p (mem_closedBall_self R.coe_nonneg))
  have hQ (s : I) :
      ‖((spdSqrtEquiv (dirichletSchauderMatrix (A s p)) (hAp s)).symm : E n →L[ℝ] E n)‖₊ ≤ Q := by
    change ‖((spdSqrtEquiv (dirichletSchauderMatrix (A s p)) (hAp s)).symm : E n →L[ℝ] E n)‖ ≤ (Q : ℝ)
    rw [show (Q : ℝ) = (Real.sqrt l)⁻¹ from
      Real.coe_toNNReal _ (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact norm_dirichletSchauderSqrt_symm_le (hAp s) hl (hEll s)
  obtain ⟨r, hr, hrR, hsmall⟩ := exists_dirichlet_uniform_schauder_absorption_scale n α L Q
    (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), (K + K))
    (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), K) R hα hR
  refine ⟨r, hr, hrR, ?_⟩
  intro s
  obtain ⟨a, hCenter, hOn, hHolder, hNorm, hOsc⟩ :=
    exists_dirichlet_normalized_coefficients_at_scale p R r K α M hrR.le hα (hA s) (hM s)
  refine ⟨a, hCenter, hOn, hHolder, hNorm, hOsc, ?_⟩
  have hSumK : (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n),
        (K * r ^ (α : ℝ) + K * r ^ (α : ℝ))) =
      r ^ (α : ℝ) * (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), (K + K)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hSumB : (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), K * r ^ (α : ℝ)) =
      r ^ (α : ℝ) * (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), K) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hSumK, hSumB]
  exact (dirichletSchauderDefectConst_le_majorant _ (hAp s) hα1 (hL s) (hQ s) _ _).trans_lt hsmall

end KEBall
