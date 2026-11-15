import KEBall.DirichletDifferenceQuotientHolder
import DifferentialGeometry.Analysis.Schauder.Holder.LocalDerivativeLimit

/-!
# Uniform convergence of actual translation quotients

A Holder bound on the first derivative gives a Taylor error uniform in
space.  Applied to the first jet of the potential, this identifies the
limit used in the Schauder difference-quotient argument as the actual
Hessian applied to the fixed translation direction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal Topology

namespace KEBall

theorem norm_dirichletDifferenceQuotient_sub_derivative_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → F} {D : E n → E n →L[ℝ] F} {K α : ℝ≥0}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hH : HolderWith K α D)
    (v x : E n) {h : ℝ} (hh : h ≠ 0) :
    ‖dirichletDifferenceQuotient f v h x - D x v‖ ≤
      (K : ℝ) * ‖v‖ * (|h| * ‖v‖) ^ (α : ℝ) := by
  by_cases hv : v = 0
  · simp [hv, dirichletDifferenceQuotient]
  have hH' : HolderWith K α (fderiv ℝ f) := by
    have he : fderiv ℝ f = D := funext fun z => (hD z).fderiv
    rwa [he]
  have hTaylor := norm_first_order_taylor_remainder_le (fun z => (hD z).differentiableAt)
    hH' x (x + h • v)
  rw [(hD x).fderiv, add_sub_cancel_left] at hTaylor
  have hEq : dirichletDifferenceQuotient f v h x - D x v =
      h⁻¹ • (f (x + h • v) - f x - D x (h • v)) := by
    simp only [dirichletDifferenceQuotient, map_smul, smul_sub, smul_smul,
      inv_mul_cancel₀ hh, one_smul]
  rw [hEq, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |h|⁻¹ * ((K : ℝ) * ‖h • v‖ ^ (1 + (α : ℝ))) :=
      mul_le_mul_of_nonneg_left hTaylor (inv_nonneg.mpr (abs_nonneg h))
    _ = (K : ℝ) * ‖v‖ * (|h| * ‖v‖) ^ (α : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs,
        Real.rpow_add (mul_pos (abs_pos.mpr hh) (norm_pos_iff.mpr hv)), Real.rpow_one]
      field_simp [abs_ne_zero.mpr hh]

theorem tendstoUniformly_dirichletDifferenceQuotient {n : ℕ} {F I : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → F} {D : E n → E n →L[ℝ] F} {K α : ℝ≥0}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hH : HolderWith K α D) (hα : 0 < α)
    (v : E n) {l : Filter I} {h : I → ℝ}
    (hh : ∀ i, h i ≠ 0) (hlim : Tendsto h l (𝓝 0)) :
    TendstoUniformly (fun i => dirichletDifferenceQuotient f v (h i)) (fun x => D x v) l := by
  have hbase : Tendsto (fun i => |h i| * ‖v‖) l (𝓝 0) := by
    simpa only [abs_zero, zero_mul] using hlim.abs.mul_const ‖v‖
  have herror : Tendsto (fun i => (K : ℝ) * ‖v‖ * (|h i| * ‖v‖) ^ (α : ℝ)) l (𝓝 0) := by
    simpa only [mul_zero] using
      (hbase.rpow_const_nhds_zero (show 0 < (α : ℝ) from hα)).const_mul ((K : ℝ) * ‖v‖)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [herror.eventually (gt_mem_nhds hε)] with i hi
  intro x
  rw [dist_comm, dist_eq_norm]
  exact (norm_dirichletDifferenceQuotient_sub_derivative_le hD hH v x (hh i)).trans_lt hi

end KEBall
