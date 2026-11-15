import KEBall.DirichletCompactCofactorFamily
import KEBall.DirichletSchauderUniformFamily
import KEBall.DirichletDifferenceQuotientEquation

/-!
# Uniform bounds for the actual coefficients of translation quotients

The two Hessian arguments lie in one fixed compact ball.  The coefficient
Holder constant, coercivity lower bound and norm bound are chosen before
the translation parameter.  The translated segment may approach zero;
none of these constants contains its reciprocal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix Metric Set
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem dirichlet_add_mem_double_closedBall {n : ℕ} {p x : E n} {R : ℝ}
    (hx : x ∈ closedBall p R) {z : E n} (hz : ‖z‖ ≤ R) :
    x + z ∈ closedBall p (2 * R) := by
  rw [mem_closedBall]
  calc
    dist (x + z) p ≤ dist (x + z) x + dist x p := dist_triangle _ _ _
    _ = ‖z‖ + dist x p := by rw [dist_eq_norm, add_sub_cancel_left]
    _ ≤ R + R := add_le_add hz (mem_closedBall.mp hx)
    _ = 2 * R := by ring

theorem dirichlet_holderOnWith_translate {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {p z : E n} {R : ℝ} {K α : ℝ≥0}
    {f : E n → F} (hf : HolderOnWith K α f (closedBall p (2 * R))) (hz : ‖z‖ ≤ R) :
    HolderOnWith K α (fun x => f (x + z)) (closedBall p R) := by
  intro x hx y hy
  simpa only [edist_add_right] using!
    hf (x + z) (dirichlet_add_mem_double_closedBall hx hz)
      (y + z) (dirichlet_add_mem_double_closedBall hy hz)

theorem exists_dirichlet_uniform_difference_quotient_cofactor_bounds {n : ℕ}
    (p v : E n) (R K α : ℝ≥0) (hα : 0 < α)
    {H : E n → Matrix (Fin n) (Fin n) ℂ}
    (hH : HolderOnWith K α H (closedBall p (2 * R)))
    (hPos : ∀ x ∈ closedBall p (2 * R), (H x).PosDef) :
    ∃ (Ka : ℝ≥0) (l M : ℝ), 0 < l ∧ 0 < M ∧
      ∀ h : ℝ, |h| * ‖v‖ ≤ R →
        HolderOnWith Ka α (fun x => dirichletMeanCofactor (H x) (H (x + h • v))) (closedBall p R) ∧
        (∀ x ∈ closedBall p R, ‖dirichletMeanCofactor (H x) (H (x + h • v))‖ ≤ M) ∧
        (∀ x ∈ closedBall p R, ∀ a b : E n,
          inner ℝ (dirichletMeanCofactor (H x) (H (x + h • v)) a) b =
            inner ℝ (dirichletMeanCofactor (H x) (H (x + h • v)) b) a) ∧
        ∀ x ∈ closedBall p R, ∀ a : E n,
          l * ‖a‖ ^ 2 ≤ inner ℝ (dirichletMeanCofactor (H x) (H (x + h • v)) a) a := by
  have hC := hH.continuousOn hα
  obtain ⟨l, M, hl, hM, hBound, hEll⟩ :=
    exists_uniform_dirichletMeanCofactor_bounds_on_compact
      (isCompact_closedBall p (2 * (R : ℝ))) hC hPos
  obtain ⟨B, hB⟩ := (isCompact_closedBall p (2 * (R : ℝ))).exists_bound_of_continuousOn hC
  obtain ⟨L, hL⟩ := exists_dirichlet_cofactor_lipschitz_on_matrix_ball (n := n) B
  have hSub : closedBall p (R : ℝ) ⊆ closedBall p (2 * R) :=
    closedBall_subset_closedBall (by nlinarith [R.coe_nonneg])
  refine ⟨L * K, l, M, hl, hM, ?_⟩
  intro h hh
  have hz : ‖h • v‖ ≤ (R : ℝ) := by simpa only [norm_smul, Real.norm_eq_abs] using hh
  have hShift (x : E n) (hx : x ∈ closedBall p R) : x + h • v ∈ closedBall p (2 * R) :=
    dirichlet_add_mem_double_closedBall hx hz
  refine ⟨holderOnWith_dirichletMeanCofactor hL (hH.mono hSub)
      (dirichlet_holderOnWith_translate hH hz)
      (fun x hx => hB x (hSub hx)) (fun x hx => hB _ (hShift x hx)),
    fun x hx => hBound x (hSub hx) _ (hShift x hx), ?_,
    fun x hx a => hEll x (hSub hx) _ (hShift x hx) a⟩
  intro x hx a b
  exact dirichletMeanCofactor_symmetric (hPos x (hSub hx)) (hPos _ (hShift x hx)) a b

end KEBall
