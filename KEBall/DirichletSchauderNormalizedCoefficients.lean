import KEBall.DirichletSchauderAbsorptionScale

/-!
# Genuine normalized coefficients with Schauder smallness

Every local positive definite Holder coefficient admits a sufficiently
small physical radius and bounded global coefficient entries which agree
with it on the normalized unit ball.  Both the Holder constants and the
oscillation bounds are K*r^alpha.  The exact double sums in the upstream
absorption hypothesis are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Calculus
open scoped BigOperators NNReal BoundedContinuousFunction

namespace KEBall

theorem exists_dirichlet_normalized_schauder_coefficients {n : ℕ}
    (p : E n) (R K α M : ℝ≥0) (hR : 0 < R) (hα : 0 < α)
    {A : E n → E n →L[ℝ] E n}
    (hA : HolderOnWith K α A (closedBall p R))
    (hM : ∀ x ∈ closedBall p R, ‖A x‖ ≤ M)
    (hAp : (dirichletSchauderMatrix (A p)).PosDef) :
    ∃ r : ℝ≥0, 0 < r ∧ r < R ∧
      ∃ a : Fin (2 * n) → Fin (2 * n) → BoundedContinuousFunction (E n) ℝ,
        (∀ i j, a i j 0 = dirichletSchauderMatrix (A p) i j) ∧
        (∀ i j x, x ∈ closedBall (0 : E n) 1 →
          a i j x = dirichletSchauderMatrix (A (p + (r : ℝ) • x)) i j) ∧
        (∀ i j, HolderWith (K * r ^ (α : ℝ)) α (a i j : E n → ℝ)) ∧
        (∀ i j, ‖a i j‖ ≤ M) ∧
        (∀ i j x, ‖a i j 0 - a i j x‖ ≤ (K * r ^ (α : ℝ) : ℝ≥0)) ∧
        spdLaplacianSchauderDefectConst (dirichletSchauderMatrix (A p)) hAp α
          (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n),
            (K * r ^ (α : ℝ) + K * r ^ (α : ℝ)))
          (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), K * r ^ (α : ℝ)) < 1 := by
  classical
  obtain ⟨r, hr, hrR, hsmall⟩ := exists_dirichlet_schauder_absorption_scale
    (dirichletSchauderMatrix (A p)) hAp α
    (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), (K + K))
    (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), K) R hα hR
  have hSub : closedBall p ((r : ℝ) * (1 : ℝ≥0)) ⊆ closedBall p R :=
    closedBall_subset_closedBall (by
      simp only [NNReal.coe_one, mul_one]
      exact_mod_cast hrR.le)
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
  refine ⟨r, hr, hrR, a, hCenter, ?_, haHolder, haM, ?_, ?_⟩
  · intro i j x hx
    exact haOn i j x hx
  · intro i j x
    rw [hCenter, norm_sub_rev]
    simpa only [NNReal.coe_one, mul_one, NNReal.coe_mul, NNReal.coe_rpow] using haOsc i j x
  · have hSumK : (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n),
          (K * r ^ (α : ℝ) + K * r ^ (α : ℝ))) =
        r ^ (α : ℝ) * (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), (K + K)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hSumB : (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), K * r ^ (α : ℝ)) =
        r ^ (α : ℝ) * (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), K) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hSumK, hSumB]
    exact hsmall

end KEBall
