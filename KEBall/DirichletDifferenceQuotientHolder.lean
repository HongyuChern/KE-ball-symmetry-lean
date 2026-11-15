import KEBall.DirichletSchauderCoefficientExtension
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform Holder bounds for actual translation quotients

The estimates retain both translated segments inside the domain.  Their
constants do not contain an inverse power of the translation parameter:
the mean-value estimate supplies the cancelling factor |h|.  Applying the
vector-valued result to the first derivative will control the first jets
of the difference quotients used in interior Schauder bootstrapping.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped NNReal

namespace KEBall

theorem dirichlet_holderOnWith_of_norm_sub_le {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] {f : E n → F} {S : Set (E n)}
    {K α : ℝ≥0}
    (h : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ (K : ℝ) * ‖x - y‖ ^ (α : ℝ)) :
    HolderOnWith K α f S := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
  apply ENNReal.ofReal_le_ofReal
  simpa only [dist_eq_norm] using h x hx y hy

noncomputable def dirichletDifferenceQuotient {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E n → F) (v : E n) (h : ℝ) (x : E n) : F :=
  h⁻¹ • (f (x + h • v) - f x)

theorem hasFDerivAt_dirichletDifferenceQuotient {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → F} {D : E n → E n →L[ℝ] F} (v : E n) (h : ℝ) (x : E n)
    (hx : HasFDerivAt f (D x) x) (hxh : HasFDerivAt f (D (x + h • v)) (x + h • v)) :
    HasFDerivAt (dirichletDifferenceQuotient f v h)
      (h⁻¹ • (D (x + h • v) - D x)) x := by
  have ht := hxh.comp x ((hasFDerivAt_id x).add_const (h • v))
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id, dirichletDifferenceQuotient,
    Pi.smul_apply, Pi.sub_apply, id_eq] using!
    (ht.sub hx).const_smul h⁻¹

theorem norm_dirichletDifferenceQuotient_le_of_derivative_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → F} {D : E n → E n →L[ℝ] F} {S : Set (E n)}
    (hD : ∀ x ∈ S, HasFDerivAt f (D x) x) {M : ℝ}
    (hM : ∀ x ∈ S, ‖D x‖ ≤ M)
    (v x : E n) {h : ℝ} (hh : h ≠ 0)
    (hSeg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • v) ∈ S) :
    ‖dirichletDifferenceQuotient f v h x‖ ≤ M * ‖v‖ := by
  have hDeriv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s : ℝ => f (x + s • (h • v)))
        (D (x + t • (h • v)) (h • v)) (Icc (0 : ℝ) 1) t := by
    have hLine : HasDerivAt (fun s : ℝ => x + s • (h • v)) (h • v) t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const (h • v)).const_add x
    exact ((hD _ (hSeg t ht)).comp_hasDerivAt t hLine).hasDerivWithinAt
  have hEst : ‖f (x + h • v) - f x‖ ≤ M * (|h| * ‖v‖) := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hDeriv (fun t ht =>
      ((D _).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (hM _ (hSeg t (Ico_subset_Icc_self ht))) (norm_nonneg _))))
    simpa only [one_smul, zero_smul, add_zero, norm_smul, Real.norm_eq_abs] using h
  calc
    ‖dirichletDifferenceQuotient f v h x‖ = |h|⁻¹ * ‖f (x + h • v) - f x‖ := by
      simp only [dirichletDifferenceQuotient, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |h|⁻¹ * (M * (|h| * ‖v‖)) :=
      mul_le_mul_of_nonneg_left hEst (inv_nonneg.mpr (abs_nonneg h))
    _ = M * ‖v‖ := by field_simp [abs_ne_zero.mpr hh]

theorem norm_dirichletDifferenceQuotient_sub_le_of_holder_derivative {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → F} {D : E n → E n →L[ℝ] F} {S : Set (E n)}
    (hD : ∀ x ∈ S, HasFDerivAt f (D x) x) {K α : ℝ}
    (hHolder : ∀ x ∈ S, ∀ y ∈ S, ‖D x - D y‖ ≤ K * ‖x - y‖ ^ α)
    (v x y : E n) {h : ℝ} (hh : h ≠ 0)
    (hSegX : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • v) ∈ S)
    (hSegY : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (h • v) ∈ S) :
    ‖dirichletDifferenceQuotient f v h x - dirichletDifferenceQuotient f v h y‖ ≤
      K * ‖v‖ * ‖x - y‖ ^ α := by
  let g (t : ℝ) := f (x + t • (h • v)) - f (y + t • (h • v))
  let dg (t : ℝ) := (D (x + t • (h • v)) - D (y + t • (h • v))) (h • v)
  have hDeriv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt g (dg t) (Icc (0 : ℝ) 1) t := by
    have hLine (z : E n) : HasDerivAt (fun s : ℝ => z + s • (h • v)) (h • v) t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const (h • v)).const_add z
    have hx := (hD _ (hSegX t ht)).comp_hasDerivAt t (hLine x)
    have hy := (hD _ (hSegY t ht)).comp_hasDerivAt t (hLine y)
    exact (hx.sub hy).hasDerivWithinAt
  have hBound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖dg t‖ ≤ (K * ‖x - y‖ ^ α) * (|h| * ‖v‖) := by
    have hH := hHolder _ (hSegX t (Ico_subset_Icc_self ht)) _ (hSegY t (Ico_subset_Icc_self ht))
    rw [add_sub_add_right_eq_sub] at hH
    exact ((D _ - D _).le_opNorm _).trans (by
      simpa only [norm_smul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right hH (norm_nonneg (h • v)))
  have hEst := norm_image_sub_le_of_norm_deriv_le_segment_01' hDeriv hBound
  have hEq : dirichletDifferenceQuotient f v h x - dirichletDifferenceQuotient f v h y =
      h⁻¹ • (g 1 - g 0) := by
    simp only [dirichletDifferenceQuotient, g, one_smul, zero_smul, add_zero, ← smul_sub]
    congr 1
    abel
  rw [hEq, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |h|⁻¹ * ((K * ‖x - y‖ ^ α) * (|h| * ‖v‖)) :=
      mul_le_mul_of_nonneg_left hEst (inv_nonneg.mpr (abs_nonneg h))
    _ = K * ‖v‖ * ‖x - y‖ ^ α := by
      field_simp [abs_ne_zero.mpr hh]

end KEBall
