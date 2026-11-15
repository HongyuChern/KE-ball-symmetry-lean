import KEBall.DirichletHessianPowerDecay
import KEBall.DirichletHessianMeanOscillation
import DifferentialGeometry.External.DeGiorgi.Oscillation.Campanato

/-!
# Hölder representatives of actual directional Hessian entries

The Campanato estimate is derived from the proved oscillation inequality.
The scalar representatives agree almost everywhere with the entries of the
original `fderiv ℝ G`; this module does not yet identify a classical second jet.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped BigOperators NNReal

noncomputable section

namespace KEBall

theorem dirichlet_hessian_hasCampanatoBound_of_oscillation {n m : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : Fin m → E n)
    {x₀ : E n} {R α C : ℝ} (hBall : ball x₀ R ⊆ unitBall n)
    (hOsc : ∀ (x : E n) (r : ℝ), x ∈ ball x₀ R → 0 < r → r ≤ R →
      ball x r ⊆ ball x₀ R → dirichletHessianOscillation G v x r ≤ C * r ^ α)
    (j : Fin m) :
    DeGiorgi.HasCampanatoBound (fun x => fderiv ℝ G x (v j) (v j)) x₀ R α C := by
  intro b
  have hr := b.radius_pos
  have hSub : ball b.center b.radius ⊆ unitBall n := b.subset_ball.trans hBall
  have hx : b.center ∈ ball x₀ R := b.subset_ball (mem_ball_self hr)
  refine ⟨integrableOn_dirichlet_hessianEntry_ball hG (v j) hSub, ?_⟩
  have hMean := (dirichlet_hessian_mean_oscillation_le hG (v j) hr hSub).trans
    ((dirichletHessianOscillation_entry_le hG v hr hSub j).trans
      (hOsc b.center b.radius hx hr b.radius_le b.subset_ball))
  change (b.radius⁻¹) ^ α *
    (⨍ x in ball b.center b.radius,
      |fderiv ℝ G x (v j) (v j) - ⨍ y in ball b.center b.radius, fderiv ℝ G y (v j) (v j)|) ≤ C
  have hCancel : (b.radius⁻¹) ^ α * b.radius ^ α = 1 := by
    rw [← Real.mul_rpow (inv_nonneg.mpr hr.le) hr.le, inv_mul_cancel₀ hr.ne', Real.one_rpow]
  calc
    _ ≤ (b.radius⁻¹) ^ α * (C * b.radius ^ α) :=
      mul_le_mul_of_nonneg_left hMean (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _)
    _ = C * ((b.radius⁻¹) ^ α * b.radius ^ α) := by ring
    _ = C := by rw [hCancel, mul_one]

theorem exists_dirichlet_hessian_local_holder_of_step {n m : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : Fin m → E n)
    {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hStep : ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ R ⊆ unitBall n →
      dirichletHessianOscillation G v x₀ (R / 4) ≤
        θ * dirichletHessianOscillation G v x₀ R + C * R) :
    ∃ α D : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ D ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ j : Fin m, ∃ q : E n → ℝ,
          (∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ R),
            q x = fderiv ℝ G x (v j) (v j)) ∧
          ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
            |q x - q y| ≤
              (DeGiorgi.CCampanatoHolder (2 * n) α * (D * (4 / R : ℝ) ^ α)) * ‖x - y‖ ^ α := by
  obtain ⟨α, D, hα0, hα1, hD, hPower⟩ :=
    exists_dirichlet_hessian_power_decay hG v hθ0 hθ1 hC hStep
  refine ⟨α, D, hα0, hα1, hD, ?_⟩
  intro x₀ R hR hR1 hMargin j
  have hBall : ball x₀ R ⊆ unitBall n :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hMargin)
  have hSub (x : E n) (hx : x ∈ ball x₀ R) : closedBall x R ⊆ unitBall n := by
    intro y hy
    apply hMargin
    apply mem_closedBall.mpr
    have hd := dist_triangle y x x₀
    have hx' := mem_ball.mp hx
    have hy' := mem_closedBall.mp hy
    linarith
  apply DeGiorgi.campanato_implies_holder hα0 hα1 hR
  apply dirichlet_hessian_hasCampanatoBound_of_oscillation hG v hBall
  intro x r hx hr hrR _
  exact hPower x R hR hR1 (hSub x hx) r hr hrR

end KEBall
