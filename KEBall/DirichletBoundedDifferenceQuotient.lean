import KEBall.DirichletDifferenceQuotientLimit
import DifferentialGeometry.Analysis.Schauder.Cutoff.Product

/-!
# Bounded continuous difference quotients and their actual jets

The supremum and Holder estimates obtained from the first derivative are
uniform in every nonzero step.  The elementary Holder estimate without a
derivative is allowed to depend on the reciprocal step; it supplies only
the initial regularity assumption that disappears from the Schauder bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal

namespace KEBall

noncomputable def dirichletBoundedDifferenceQuotient {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : BoundedContinuousFunction (E n) F) (v : E n) (h : ℝ) :
    BoundedContinuousFunction (E n) F :=
  h⁻¹ • (f.compContinuous ⟨fun x => x + h • v, continuous_id.add_const _⟩ - f)

theorem dirichletBoundedDifferenceQuotient_apply {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : BoundedContinuousFunction (E n) F) (v : E n) (h : ℝ) (x : E n) :
    dirichletBoundedDifferenceQuotient f v h x =
      dirichletDifferenceQuotient (f : E n → F) v h x := rfl

theorem hasFDerivAt_dirichletBoundedDifferenceQuotient {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : BoundedContinuousFunction (E n) F}
    {D : BoundedContinuousFunction (E n) (E n →L[ℝ] F)}
    (hD : ∀ x, HasFDerivAt (f : E n → F) (D x) x)
    (v : E n) (h : ℝ) (x : E n) :
    HasFDerivAt (dirichletBoundedDifferenceQuotient f v h : E n → F)
      (dirichletBoundedDifferenceQuotient D v h x) x :=
  hasFDerivAt_dirichletDifferenceQuotient v h x (hD x) (hD _)

theorem nnnorm_dirichletBoundedDifferenceQuotient_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : BoundedContinuousFunction (E n) F}
    {D : BoundedContinuousFunction (E n) (E n →L[ℝ] F)}
    (hD : ∀ x, HasFDerivAt (f : E n → F) (D x) x) (v : E n) {h : ℝ} (hh : h ≠ 0) :
    ‖dirichletBoundedDifferenceQuotient f v h‖₊ ≤ ‖D‖₊ * ‖v‖₊ := by
  change ‖dirichletBoundedDifferenceQuotient f v h‖ ≤ (‖D‖₊ * ‖v‖₊ : ℝ≥0)
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  exact norm_dirichletDifferenceQuotient_le_of_derivative_bound (S := univ)
    (fun z _ => hD z) (fun z _ => D.norm_coe_le_norm z) v x hh (fun _ _ => mem_univ _)

theorem holderWith_dirichletDifferenceQuotient {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → F} {K α : ℝ≥0} (hf : HolderWith K α f) (v : E n) (h : ℝ) :
    HolderWith (‖h⁻¹‖₊ * (K + K)) α (dirichletDifferenceQuotient f v h) := by
  have ht : HolderWith K α (fun x => f (x + h • v)) := by
    intro x y
    simpa only [edist_add_right] using hf (x + h • v) (y + h • v)
  have hSub := holderWith_sub ht hf
  apply holderOnWith_univ.mp
  apply dirichlet_holderOnWith_of_norm_sub_le
  intro x _ y _
  have hEst : ‖(f (x + h • v) - f x) - (f (y + h • v) - f y)‖ ≤
      ((K + K : ℝ≥0) : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
    simpa only [dist_eq_norm, Pi.sub_apply] using hSub.dist_le x y
  calc
    _ = ‖h⁻¹‖ * ‖(f (x + h • v) - f x) - (f (y + h • v) - f y)‖ := by
      rw [dirichletDifferenceQuotient, dirichletDifferenceQuotient, ← smul_sub, norm_smul]
    _ ≤ ‖h⁻¹‖ * (((K + K : ℝ≥0) : ℝ) * ‖x - y‖ ^ (α : ℝ)) :=
      mul_le_mul_of_nonneg_left hEst (norm_nonneg _)
    _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm, mul_assoc]

theorem holderWith_dirichletDifferenceQuotient_of_holder_derivative {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → F} {D : E n → E n →L[ℝ] F} {K α : ℝ≥0}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hH : HolderWith K α D)
    (v : E n) {h : ℝ} (hh : h ≠ 0) :
    HolderWith (K * ‖v‖₊) α (dirichletDifferenceQuotient f v h) := by
  apply holderOnWith_univ.mp
  apply dirichlet_holderOnWith_of_norm_sub_le
  intro x _ y _
  have hHold : ∀ a ∈ (univ : Set (E n)), ∀ b ∈ (univ : Set (E n)),
      ‖D a - D b‖ ≤ (K : ℝ) * ‖a - b‖ ^ (α : ℝ) := by
    intro a _ b _
    simpa only [dist_eq_norm] using hH.dist_le a b
  exact norm_dirichletDifferenceQuotient_sub_le_of_holder_derivative (S := univ)
    (fun z _ => hD z) hHold v x y hh (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)

end KEBall
