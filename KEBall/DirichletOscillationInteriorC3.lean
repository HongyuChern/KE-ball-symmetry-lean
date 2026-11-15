import KEBall.DirichletLocalNonlinearC3
import KEBall.DirichletHessianHolderNorm
import KEBall.DirichletBoundaryRemainder

/-!
# The oscillation-decay solution is C3 in the open ball

The previously established Hessian oscillation decay supplies the only
Holder hypothesis.  Its exponent is reduced by one half on a compact
interior ball, ensuring the strict exponent range needed by Schauder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ComplexOrder NNReal Topology

namespace KEBall

theorem contDiffOn_three_of_dirichlet_hessian_oscillation_and_determinant {n : ℕ}
    (hn : 0 < n) {w f : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G)
    (hf : ContDiffOn ℝ 2 f (unitBall n))
    (hPos : ∀ x ∈ unitBall n, (complexHessian w x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian w x).det.re = f x) :
    ContDiffOn ℝ 3 w (unitBall n) := by
  have hw := contDiffOn_two_of_dirichlet_hessian_oscillation hD hG hDecay
  obtain ⟨β, hβ, hβ1, hHolder⟩ :=
    exists_dirichlet_realHessian_local_holder_of_oscillation hD hG hDecay
  let b : ℝ≥0 := ⟨β, hβ.le⟩
  have hb : 0 < b := hβ
  have hb1 : b ≤ 1 := hβ1
  have hα : 0 < b / 2 := div_pos hb (by norm_num)
  have hα1 : b / 2 < 1 := by
    exact (div_le_div_of_nonneg_right hb1 (by norm_num)).trans_lt (by norm_num)
  intro p hp
  have hp' : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  let R : ℝ := (1 - ‖p‖) / 4
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R ≤ 1 := by dsimp [R]; have := norm_nonneg p; linarith
  have hMargin : closedBall p (2 * R) ⊆ unitBall n :=
    closedBall_subset_dirichlet_unitBall_of_margin (by dsimp [R]; linarith)
  obtain ⟨C, hC, hCbound⟩ := hHolder p R hR hR1 hMargin
  let r : ℝ≥0 := ⟨R / 4, by positivity⟩
  have hr : 0 < r := by change (0 : ℝ) < R / 4; positivity
  have hSmall : closedBall p (r : ℝ) ⊆ ball p (R / 2) :=
    closedBall_subset_ball (by change R / 4 < R / 2; linarith)
  have hSub : closedBall p (r : ℝ) ⊆ unitBall n :=
    (closedBall_subset_closedBall (by change R / 4 ≤ 2 * R; linarith)).trans hMargin
  have hOld : HolderOnWith (⟨C, hC⟩ : ℝ≥0) b (realHessian w) (closedBall p r) :=
    dirichlet_holderOnWith_of_norm_sub_le
      (fun x hx y hy => hCbound x (hSmall hx) y (hSmall hy))
  have hNew := hOld.of_le (fun x hx y hy => dirichlet_closedBall_edist_le hx hy)
    (show b / 2 ≤ b from (div_le_self (bot_le : (0 : ℝ≥0) ≤ b) (by norm_num)))
  exact (dirichlet_C3At_of_local_positive_determinant_and_holder_hessian hn isOpen_ball
    hw hf hPos hEq p r (b / 2) _ hr hα hα1 hSub hNew).contDiffWithinAt

end KEBall
