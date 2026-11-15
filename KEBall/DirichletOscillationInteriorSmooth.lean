import KEBall.DirichletNonlinearHolderBootstrap
import KEBall.DirichletOscillationInteriorC3

/-!
# From actual Hessian oscillation decay to interior smoothness

The initial C2,alpha jet is supplied by the already proved oscillation
estimate for the actual first jet.  The nonlinear bootstrap then applies
to smooth prescribed densities and to exponential densities separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall

theorem exists_dirichlet_holderAt_two_of_hessian_oscillation {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G) :
    ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧ ∀ p ∈ unitBall n, HasDirichletHolderAt 2 α w p := by
  have hw := contDiffOn_two_of_dirichlet_hessian_oscillation hD hG hDecay
  obtain ⟨β, hβ, hβ1, hHolder⟩ :=
    exists_dirichlet_realHessian_local_holder_of_oscillation hD hG hDecay
  let b : ℝ≥0 := ⟨β, hβ.le⟩
  have hb : 0 < b := hβ
  have hb1 : b ≤ 1 := hβ1
  have hα : 0 < b / 2 := div_pos hb (by norm_num)
  have hα1 : b / 2 < 1 :=
    (div_le_div_of_nonneg_right hb1 (by norm_num)).trans_lt (by norm_num)
  refine ⟨b / 2, hα, hα1, ?_⟩
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
    (show b / 2 ≤ b from div_le_self (bot_le : (0 : ℝ≥0) ≤ b) (by norm_num))
  exact ⟨r, hr, hw.mono (ball_subset_closedBall.trans hSub), _,
    dirichlet_holderOn_iterated_two_iff.mpr (hNew.mono ball_subset_closedBall)⟩

theorem contDiffOn_infty_of_dirichlet_hessian_oscillation_and_determinant {n : ℕ}
    (hn : 0 < n) {w f : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G)
    (hf : ContDiffOn ℝ ∞ f (unitBall n))
    (hPos : ∀ x ∈ unitBall n, (complexHessian w x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian w x).det.re = f x) :
    ContDiffOn ℝ ∞ w (unitBall n) := by
  obtain ⟨α, hα, hα1, hSeed⟩ := exists_dirichlet_holderAt_two_of_hessian_oscillation hD hG hDecay
  intro p hp
  exact (contDiffAt_infty_of_positive_determinant_smooth_density hn isOpen_ball hp hα hα1
    (hSeed p hp) (hf.contDiffAt (isOpen_ball.mem_nhds hp)) hPos hEq).contDiffWithinAt

theorem contDiffOn_infty_of_dirichlet_hessian_oscillation_and_exponential {n : ℕ}
    (hn : 0 < n) {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G) (c a : ℝ)
    (hPos : ∀ x ∈ unitBall n, (complexHessian w x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian w x).det.re = c * Real.exp (a * w x)) :
    ContDiffOn ℝ ∞ w (unitBall n) := by
  obtain ⟨α, hα, hα1, hSeed⟩ := exists_dirichlet_holderAt_two_of_hessian_oscillation hD hG hDecay
  intro p hp
  exact (contDiffAt_infty_of_positive_determinant_exponential hn isOpen_ball hp hα hα1
    (hSeed p hp) c a hPos hEq).contDiffWithinAt

end KEBall
