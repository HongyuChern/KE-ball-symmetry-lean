import KEBall.DirichletSchauderCoefficientExtension

/-!
# A bounded global Holder extension from a closed ball

The nonexpansive radial retraction preserves the Holder constant.  This
extension is used for the values of each local jet; differentiability is
subsequently restored by a smooth cutoff supported strictly inside the ball.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open DifferentialGeometry.Analysis.Calculus
open scoped NNReal

namespace KEBall

theorem exists_dirichlet_bounded_holder_extension {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] (p : E n) (R K α : ℝ≥0) (hα : 0 < α)
    {f : E n → F} (hf : HolderOnWith K α f (closedBall p R)) :
    ∃ g : BoundedContinuousFunction (E n) F,
      EqOn (g : E n → F) f (closedBall p R) ∧ HolderWith K α (g : E n → F) := by
  let q (x : E n) := p + ballRetraction (R : ℝ) (x - p)
  have hq (x : E n) : q x ∈ closedBall p R := by
    simpa only [NNReal.coe_one, one_smul, one_mul] using
      dirichlet_scaled_ballRetraction_mem p 1 R (x - p)
  have hqLip : LipschitzWith 1 q := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (lipschitzWith_one_ballRetraction (X := E n) R.coe_nonneg).dist_le_mul (x - p) (y - p)
    simpa only [q, NNReal.coe_one, one_mul, dist_eq_norm,
      add_sub_add_left_eq_sub, sub_sub_sub_cancel_right] using h
  have hHold : HolderWith K α (f ∘ q) := by
    simpa only [NNReal.one_rpow, mul_one] using hf.comp_holderWith hqLip.holderWith hq
  obtain ⟨B, hB⟩ := (isCompact_closedBall p (R : ℝ)).exists_bound_of_continuousOn (hf.continuousOn hα)
  let g := BoundedContinuousFunction.ofNormedAddCommGroup (f ∘ q)
    (hHold.continuous hα) B (fun x => hB _ (hq x))
  refine ⟨g, ?_, hHold⟩
  intro x hx
  change f (p + ballRetraction (R : ℝ) (x - p)) = f x
  have hxp : ‖x - p‖ ≤ (R : ℝ) := by simpa only [dist_eq_norm] using mem_closedBall.mp hx
  rw [ballRetraction_eq_self_of_mem hxp, add_sub_cancel]

end KEBall
