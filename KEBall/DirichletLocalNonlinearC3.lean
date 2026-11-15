import KEBall.DirichletNonlinearC3Jets
import KEBall.DirichletSchauderLocalC1

/-!
# Interior C3 regularity for the original nonlinear solution

The cutoff extensions are auxiliary.  The conclusion concerns the
original function, and the hypotheses use only its local C2 regularity,
Holder Hessian, positive complex Hessian, and a C2 prescribed density.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal Topology

namespace KEBall

theorem dirichlet_C3At_of_local_positive_determinant_and_holder_hessian {n : ℕ}
    (hn : 0 < n) {S : Set (E n)} (hS : IsOpen S) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u S) (hf : ContDiffOn ℝ 2 f S)
    (hPos : ∀ x ∈ S, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ S, (complexHessian u x).det.re = f x)
    (p : E n) (R α KH : ℝ≥0) (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hSub : closedBall p (R : ℝ) ⊆ S)
    (hHH : HolderOnWith KH α (fderiv ℝ (fderiv ℝ u)) (closedBall p R)) :
    ContDiffAt ℝ 3 u p := by
  have hhalf : R / 2 < R := by exact div_lt_self hR (by norm_num)
  obtain ⟨w, Dw, Hw, Kw, KDw, KHw, hwEq, hwDer, hDwDer, hwH, hDwH, hHwH⟩ :=
    exists_dirichlet_actual_C2_holder_extension p (R / 2) R α KH hhalf hα hα1.le
      hS hSub hu hHH
  obtain ⟨g, Dg, Kg, KDg, hgEq, hgDer, hgH, hDgH⟩ :=
    exists_dirichlet_C1_holder_extension_of_C2 p (R / 2) R α hhalf hα hα1.le hS hSub hf
  have hNear (x : E n) (hx : x ∈ ball p ((R / 2 : ℝ≥0) : ℝ)) :
      (w : E n → ℝ) =ᶠ[𝓝 x] u := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hwEq (ball_subset_closedBall hy)
  have hSmall : closedBall p (2 * ((R / 8 : ℝ≥0) : ℝ)) ⊆ ball p ((R / 2 : ℝ≥0) : ℝ) := by
    apply closedBall_subset_ball
    push_cast
    have hR' : (0 : ℝ) < R := hR
    linarith
  have hBallSub : ball p ((R / 2 : ℝ≥0) : ℝ) ⊆ S :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (by exact_mod_cast hhalf.le))).trans hSub
  have hPosW (x : E n) (hx : x ∈ closedBall p (2 * ((R / 8 : ℝ≥0) : ℝ))) :
      (complexHessian (w : E n → ℝ) x).PosDef := by
    rw [complexHessian_congr_of_eventuallyEq (hNear x (hSmall hx))]
    exact hPos x (hBallSub (hSmall hx))
  have hEqW (x : E n) (hx : x ∈ closedBall p (2 * ((R / 8 : ℝ≥0) : ℝ))) :
      (complexHessian (w : E n → ℝ) x).det.re = g x := by
    rw [complexHessian_congr_of_eventuallyEq (hNear x (hSmall hx)),
      hEq x (hBallSub (hSmall hx)), hgEq (ball_subset_closedBall (hSmall hx))]
  have hwC3 := dirichlet_C3At_of_positive_determinant_C2_holder_jets hn w Dw Hw g Dg
    hwDer hDwDer hgDer hα hα1 hDwH hHwH hDgH p (R / 8)
    (div_pos hR (by norm_num)) hPosW hEqW
  exact hwC3.congr_of_eventuallyEq (hNear p (mem_ball_self (by
    change (0 : ℝ) < (R : ℝ) / 2
    exact div_pos hR (by norm_num)))).symm

end KEBall
