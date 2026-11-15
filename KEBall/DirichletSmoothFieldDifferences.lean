import KEBall.DirichletTensorDifferences
import KEBall.DirichletAngularL2

/-!
# Uniform differences of smooth reference fields

These bounds are used only for a fixed smooth reference and the prescribed
density, never as an additional regularity assumption on the C2 potential.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped ContDiff NNReal

namespace KEBall

theorem orthogonalFlow_apply_generator {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t : ℝ) (x : E n) :
    orthogonalFlow S hS t (S x) = S (orthogonalFlow S hS t x) := by
  have h := ((Commute.refl S).smul_right t).exp_right
  exact (congrArg (fun L : E n →L[ℝ] E n => L x) h.eq).symm

theorem norm_dirichletFieldDifference_flow_le {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E n → V} {K : ℝ≥0}
    (hF : LipschitzOnWith K F (closedUnitBall n))
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    ‖dirichletFieldDifference (orthogonalFlow S hS t) t F x‖ ≤ (K : ℝ) * ‖S‖ := by
  let R := orthogonalFlow S hS t
  let L := R.toContinuousLinearEquiv.toContinuousLinearMap
  have hMove : dist (R x) x ≤ ‖S‖ * |t| := by
    change ‖(L - ContinuousLinearMap.id ℝ (E n)) x‖ ≤ _
    exact ((L - ContinuousLinearMap.id ℝ (E n)).le_opNorm x).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp hx)).trans
        (norm_orthogonalFlow_sub_id_le S hS t))
  have hLip := hF.dist_le_mul _ (orthogonalFlow_mapsTo_closedUnitBall S hS t hx) _ hx
  have hBound : ‖F (R x) - F x‖ ≤ (K : ℝ) * (‖S‖ * |t|) := by
    simpa only [dist_eq_norm] using hLip.trans
      (mul_le_mul_of_nonneg_left hMove K.coe_nonneg)
  rw [dirichletFieldDifference, norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    _ ≤ |t|⁻¹ * ((K : ℝ) * (‖S‖ * |t|)) :=
      mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr (abs_nonneg t))
    _ = (K : ℝ) * ‖S‖ := by field_simp

theorem norm_dirichletFieldDifference_flow_le_of_angular_bound {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E n → V} {F' : E n → E n →L[ℝ] V}
    (hF : ∀ x ∈ closedUnitBall n, HasFDerivAt F (F' x) x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) {B : ℝ}
    (hBound : ∀ x ∈ closedUnitBall n, ‖F' x (S x)‖ ≤ B)
    {t : ℝ} (ht : t ≠ 0) {x : E n} (hx : x ∈ closedUnitBall n) :
    ‖dirichletFieldDifference (orthogonalFlow S hS t) t F x‖ ≤ B := by
  let R := orthogonalFlow S hS
  let g (s : ℝ) := F (R s x)
  let g' (s : ℝ) := F' (R s x) (S (R s x))
  have hDeriv (s : ℝ) : HasDerivAt g (g' s) s := by
    have h := (hF _ (orthogonalFlow_mapsTo_closedUnitBall S hS s hx)).comp_hasDerivAt s
      (hasDerivAt_orthogonalFlow_apply S hS x s)
    simpa only [Function.comp_def, orthogonalFlow_apply_generator, g, g', R] using h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ)) (f := g) (f' := g')
    (fun s _ => (hDeriv s).hasDerivWithinAt)
    (fun s _ => hBound _ (orthogonalFlow_mapsTo_closedUnitBall S hS s hx))
    convex_univ (mem_univ (0 : ℝ)) (mem_univ t)
  have hInc : ‖F (R t x) - F x‖ ≤ B * |t| := by
    simpa only [g, R, orthogonalFlow_zero_apply, sub_zero, Real.norm_eq_abs] using h
  rw [dirichletFieldDifference, norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    _ ≤ |t|⁻¹ * (B * |t|) :=
      mul_le_mul_of_nonneg_left hInc (inv_nonneg.mpr (abs_nonneg t))
    _ = B := by field_simp

theorem exists_dirichlet_smooth_field_difference_bounds {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E n → V} (hF : ∀ x ∈ closedUnitBall n, ContDiffAt ℝ ∞ F x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ A ≥ (0 : ℝ), ∃ B ≥ (0 : ℝ), ∀ t : ℝ, t ≠ 0 → ∀ x ∈ closedUnitBall n,
      ‖dirichletFieldDifference (orthogonalFlow S hS t) t F x‖ ≤ A ∧
      ‖dirichletFieldDifference (orthogonalFlow S hS t) t
        (dirichletFieldDifference (orthogonalFlow S hS t) t F) x‖ ≤ B := by
  have hFC : ContDiffOn ℝ ∞ F (closedUnitBall n) :=
    fun x hx => (hF x hx).contDiffWithinAt
  let G (x : E n) := fderiv ℝ F x (S x)
  have hG : ContDiffOn ℝ ∞ G (closedUnitBall n) := by
    intro x hx
    exact (((hF x hx).fderiv_right (m := ∞) (by simp)).clm_apply
      S.contDiff.contDiffAt).contDiffWithinAt
  obtain ⟨K, hK⟩ := hFC.exists_lipschitzOnWith (by simp)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨L, hL⟩ := hG.exists_lipschitzOnWith (by simp)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨(K : ℝ) * ‖S‖, by positivity, (L : ℝ) * ‖S‖, by positivity, ?_⟩
  intro t ht x hx
  constructor
  · exact norm_dirichletFieldDifference_flow_le hK S hS ht hx
  let R := orthogonalFlow S hS t
  let q := dirichletFieldDifference R t F
  let Q (y : E n) : E n →L[ℝ] V :=
    t⁻¹ • ((fderiv ℝ F (R y)).comp R.toContinuousLinearEquiv.toContinuousLinearMap -
      fderiv ℝ F y)
  have hq (y : E n) (hy : y ∈ closedUnitBall n) : HasFDerivAt q (Q y) y := by
    have h₀ := ((hF y hy).differentiableAt (by simp)).hasFDerivAt
    have h₁ := (((hF (R y) (orthogonalFlow_mapsTo_closedUnitBall S hS t hy)).differentiableAt
      (by simp)).hasFDerivAt.comp y R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)
    convert! (h₁.sub h₀).const_smul t⁻¹ using 1
  apply norm_dirichletFieldDifference_flow_le_of_angular_bound hq S hS _ ht hx
  intro y hy
  have hQ : Q y (S y) = dirichletFieldDifference R t G y := by
    change t⁻¹ • (fderiv ℝ F (R y) (R (S y)) - fderiv ℝ F y (S y)) =
      t⁻¹ • (fderiv ℝ F (R y) (S (R y)) - fderiv ℝ F y (S y))
    rw [orthogonalFlow_apply_generator]
  rw [hQ]
  exact norm_dirichletFieldDifference_flow_le hL S hS ht hy

end KEBall
