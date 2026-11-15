import KEBall.DirichletHessianHolderNorm
import KEBall.DirichletLogDensityInteriorClassical
import KEBall.DirichletBoundaryNormalTrace

/-!
# The same path limit: classical equation and interior Hölder Hessian

All conclusions below concern the single limit supplied by the weak
compactness and Hessian oscillation theorem.  In particular, no identification
of independently chosen limits, or closed-ball second-order regularity, is
assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem exists_dirichlet_interior_holder_limit_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0) (α : ℝ),
      0 < α ∧ α ≤ 1 ∧
      ContDiffOn ℝ 1 w (closedUnitBall n) ∧
      ContDiffOn ℝ 2 w (unitBall n) ∧
      (∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖realHessian w x - realHessian w y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨w, G, L, hwC, hD, hLip, hw0, hAe, hDecay⟩ :=
    exists_dirichlet_limit_with_hessian_oscillation_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  have hw2 := contDiffOn_two_of_dirichlet_hessian_oscillation hD hLip hDecay
  obtain ⟨α, hα0, hα1, hHolder⟩ :=
    exists_dirichlet_realHessian_local_holder_of_oscillation hD hLip hDecay
  have hHess (x : E n) (hx : x ∈ unitBall n) :
      complexHessianOfRealBilinear (fderiv ℝ G x) = complexHessian w x := by
    rw [fderiv_dirichlet_firstJet_eq_realHessian hD hx]
    exact complexHessianOfRealBilinear_eq (hw2.contDiffAt (isOpen_ball.mem_nhds hx))
  have hAe' : ∀ᵐ x ∂ν[n], (complexHessian w x).PosDef ∧
      (complexHessian w x).det.re = Real.exp (t₀ * g x) := by
    filter_upwards [hAe, ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx hxB
    rwa [hHess x hxB] at hx
  have hgC : ContinuousOn g (unitBall n) := by
    obtain ⟨U, _, hSub, hgU⟩ := hg
    exact hgU.continuousOn.mono (ball_subset_closedBall.trans hSub)
  have hPoint : EqOn (fun x => (complexHessian w x).det.re)
      (fun x => Real.exp (t₀ * g x)) (unitBall n) :=
    Measure.eqOn_open_of_ae_eq (hAe'.mono fun _ hx => hx.2) isOpen_ball
      (continuousOn_det_complexHessian_C2 hw2)
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hgC))
  have hPos := dirichlet_complexHessian_posDef_of_interior_C2_ae hw2
    (hAe'.mono fun _ hx => hx.1)
    (fun x hx => by
      have he := hPoint hx
      dsimp only at he
      exact (Real.exp_pos _).trans_eq he.symm)
  exact ⟨w, G, L, α, hα0, hα1,
    contDiffOn_one_dirichlet_closedBall hwC hLip.continuousOn hD, hw2,
    fun _ hx => hasFDerivWithinAt_dirichlet_closedBall hwC hLip.continuousOn hD hx,
    hD, hLip, hw0, hPos, fun _ hx => hPoint hx, hHolder⟩

end KEBall
