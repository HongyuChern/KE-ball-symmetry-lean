import KEBall.DirichletSchauderContraction
import DifferentialGeometry.Analysis.Calculus.Retraction.Ball
import Mathlib.Topology.MetricSpace.Holder

/-!
# Scaling and extension of the actual local coefficient

The coefficient is evaluated on a nonexpansive ball retraction.  This keeps
the original coefficient on the rescaled ball, keeps its supremum bound,
and changes its Holder constant by exactly the spatial scale to that power.
The oscillation around the center is bounded by the original Holder
constant times the physical radius to that same power.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open DifferentialGeometry.Analysis.Calculus
open scoped NNReal BoundedContinuousFunction

namespace KEBall

theorem dirichlet_scaled_ballRetraction_mem {n : ℕ}
    (p : E n) (r R : ℝ≥0) (x : E n) :
    p + (r : ℝ) • ballRetraction (R : ℝ) x ∈ closedBall p ((r : ℝ) * R) := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg r.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (ballRetraction_mem_closedBall R.coe_nonneg x) r.coe_nonneg

theorem lipschitzWith_dirichlet_scaled_ballRetraction {n : ℕ}
    (p : E n) (r R : ℝ≥0) :
    LipschitzWith r (fun x : E n => p + (r : ℝ) • ballRetraction (R : ℝ) x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, show p + (r : ℝ) • ballRetraction (R : ℝ) x -
      (p + (r : ℝ) • ballRetraction (R : ℝ) y) =
      (r : ℝ) • (ballRetraction (R : ℝ) x - ballRetraction (R : ℝ) y) by module,
    norm_smul, Real.norm_of_nonneg r.coe_nonneg]
  apply mul_le_mul_of_nonneg_left _ r.coe_nonneg
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
    (lipschitzWith_one_ballRetraction (X := E n) R.coe_nonneg).dist_le_mul x y

theorem exists_dirichlet_scaled_holder_coefficient_extension {n : ℕ}
    {F : Type*} [NormedAddCommGroup F]
    (p : E n) (r R K α M : ℝ≥0) (hα : 0 < α) {A : E n → F}
    (hA : HolderOnWith K α A (closedBall p ((r : ℝ) * R)))
    (hM : ∀ x ∈ closedBall p ((r : ℝ) * R), ‖A x‖ ≤ M) :
    ∃ a : BoundedContinuousFunction (E n) F,
      (∀ x, a x = A (p + (r : ℝ) • ballRetraction (R : ℝ) x)) ∧
      (∀ x ∈ closedBall (0 : E n) R, a x = A (p + (r : ℝ) • x)) ∧
      HolderWith (K * r ^ (α : ℝ)) α (a : E n → F) ∧
      ‖a‖ ≤ M ∧
      ∀ x, ‖a x - A p‖ ≤ (K : ℝ) * ((r : ℝ) * R) ^ (α : ℝ) := by
  let q (x : E n) := p + (r : ℝ) • ballRetraction (R : ℝ) x
  have hq (x : E n) : q x ∈ closedBall p ((r : ℝ) * R) :=
    dirichlet_scaled_ballRetraction_mem p r R x
  have hHolder : HolderWith (K * r ^ (α : ℝ)) α (A ∘ q) := by
    simpa only [mul_one] using hA.comp_holderWith
      (lipschitzWith_dirichlet_scaled_ballRetraction p r R).holderWith hq
  let a : BoundedContinuousFunction (E n) F :=
    ⟨⟨A ∘ q, hHolder.continuous hα⟩, 2 * (M : ℝ), fun x y => by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans ((add_le_add (hM _ (hq x)) (hM _ (hq y))).trans_eq (by ring))⟩
  refine ⟨a, fun _ => rfl, ?_, hHolder, ?_, ?_⟩
  · intro x hx
    change A (p + (r : ℝ) • ballRetraction (R : ℝ) x) = _
    rw [ballRetraction_eq_self_of_mem (mem_closedBall_zero_iff.mp hx)]
  · exact (BoundedContinuousFunction.norm_le M.coe_nonneg).mpr (fun x => hM _ (hq x))
  · intro x
    rw [← dist_eq_norm]
    exact hA.dist_le_of_le (hq x) (mem_closedBall_self (mul_nonneg r.coe_nonneg R.coe_nonneg))
      (mem_closedBall.mp (hq x))

end KEBall
