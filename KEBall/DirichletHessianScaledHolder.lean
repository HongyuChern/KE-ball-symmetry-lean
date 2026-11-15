import KEBall.DirichletHessianHolderNorm

/-!
# Interior Hessian Hölder estimates with an explicit radius factor

The constant is selected before the center and radius.  This retains the
scale dependence needed when an interior ball approaches the boundary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ContDiff NNReal Topology

namespace KEBall

theorem exists_dirichlet_realHessian_scaled_holder_of_oscillation {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G) :
    ∃ α H : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ H ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖realHessian w x - realHessian w y‖ ≤
            (H * (4 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
  have hw := contDiffOn_two_of_dirichlet_hessian_oscillation hD hG hDecay
  have hw1 : ContDiffOn ℝ 1 (fderiv ℝ w) (unitBall n) :=
    hw.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hw0 : ContDiffOn ℝ 0 (realHessian w) (unitBall n) :=
    hw1.fderiv_of_isOpen isOpen_ball (by norm_num)
  obtain ⟨m, v, θ, C, hθ0, hθ1, hC, hBasis, hPairs, hStep⟩ := hDecay
  obtain ⟨α, D, hα0, hα1, _, hHolder⟩ :=
    exists_dirichlet_hessian_local_holder_of_step hG v hθ0 hθ1 hC hStep
  let H : ℝ := (2 * n : ℝ) ^ 2 * (3 / 2 * (DeGiorgi.CCampanatoHolder (2 * n) α * D))
  refine ⟨α, max H 0, hα0, hα1, le_max_right _ _, ?_⟩
  intro x₀ R hR hR1 hMargin
  let K : ℝ := DeGiorgi.CCampanatoHolder (2 * n) α * (D * (4 / R : ℝ) ^ α)
  choose q hqEq hqHold using hHolder x₀ R hR hR1 hMargin
  have hSmall : ball x₀ (R / 2) ⊆ ball x₀ R := ball_subset_ball (by linarith)
  have hInside : ball x₀ (R / 2) ⊆ unitBall n :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hMargin)
  have hPoint (j : Fin m) : EqOn (q j)
      (fun x => realHessian w x (v j) (v j)) (ball x₀ (R / 2)) := by
    have he : q j =ᵐ[(volume : Measure (E n)).restrict (ball x₀ (R / 2))]
        fun x => realHessian w x (v j) (v j) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hSmall (hqEq j),
        ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx hxB
      rw [fderiv_dirichlet_firstJet_eq_realHessian hD (hInside hxB)] at hx
      exact hx
    exact Measure.eqOn_open_of_ae_eq he isOpen_ball
      (continuousOn_of_dirichlet_holder_bound hα0 (hqHold j))
      (((hw0.clm_apply contDiffOn_const).clm_apply contDiffOn_const).continuousOn.mono hInside)
  intro x hx y hy
  have hSym (z : E n) (hz : z ∈ unitBall n) (a b : E n) :
      realHessian w z a b = realHessian w z b a :=
    ((hw.contDiffAt (isOpen_ball.mem_nhds hz)).isSymmSndFDerivAt (by norm_num)).eq a b
  have hDiag (j : Fin m) :
      |realHessian w x (v j) (v j) - realHessian w y (v j) (v j)| ≤ K * ‖x - y‖ ^ α := by
    have heX := hPoint j hx
    have heY := hPoint j hy
    dsimp only at heX heY
    rw [← heX, ← heY]
    exact hqHold j x hx y hy
  have hNorm := norm_dirichlet_symmetric_bilinear_sub_le_of_frame
    (realHessian w x) (realHessian w y) (hSym x (hInside hx)) (hSym y (hInside hy))
    v hBasis hPairs hDiag
  calc
    ‖realHessian w x - realHessian w y‖ ≤ (H * (4 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
      calc
        _ ≤ (2 * n : ℝ) ^ 2 * (3 / 2 * (K * ‖x - y‖ ^ α)) := hNorm
        _ = _ := by dsimp [H, K]; ring
    _ ≤ (max H 0 * (4 / R : ℝ) ^ α) * ‖x - y‖ ^ α :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (norm_nonneg _) _)

end KEBall
