import KEBall.DirichletHessianBallBounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Almost-everywhere symmetry and polarization of the actual second jet. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped NNReal Topology

noncomputable section

namespace KEBall

theorem ae_dirichlet_firstJet_hessian_symmetric {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n)) :
    ∀ᵐ x ∂(volume : Measure (E n)).restrict (unitBall n),
      ∀ a b : E n, fderiv ℝ G x a b = fderiv ℝ G x b a := by
  obtain ⟨W, hW, hGW⟩ := hG.extend_finite_dimension
  have hAe := ae_restrict_of_ae (s := unitBall n) (hW.ae_differentiableAt (μ := volume))
  filter_upwards [hAe, ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball]
    with x hx hxB
  have hN : ∀ᶠ y in 𝓝 x, y ∈ unitBall n := isOpen_ball.mem_nhds hxB
  have he : G =ᶠ[𝓝 x] W := hN.mono fun y hy => hGW (ball_subset_closedBall hy)
  have hdG : DifferentiableAt ℝ G x := he.differentiableAt_iff.mpr hx
  exact second_derivative_symmetric_of_eventually (hN.mono fun y hy => hD y hy) hdG.hasFDerivAt

theorem dirichlet_symmetric_bilinear_polarization {n : ℕ}
    (D : E n →L[ℝ] E n →L[ℝ] ℝ) (hD : ∀ a b, D a b = D b a) (a b : E n) :
    D a b = (D (a + b) (a + b) - D a a - D b b) / 2 := by
  simp only [map_add, ContinuousLinearMap.add_apply, hD b a]
  ring

end KEBall
