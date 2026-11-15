import KEBall.DirichletHessianContinuousField
import KEBall.DirichletFirstJetClassical

/-!
# Classical interior second derivatives of the actual log-density path limit

The weak Harnack and oscillation estimates are applied to the derivative of
the original first jet.  The continuous representatives are identified with
that derivative by Lipschitz mollification.  This proves interior C²
regularity, without asserting boundary regularity or smoothness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem contDiffOn_two_of_dirichlet_hessian_oscillation {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    (hDecay : HasDirichletHessianOscillationDecay G) :
    ContDiffOn ℝ 2 w (unitBall n) := by
  intro x hx
  have hxN : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  let R : ℝ := (1 - ‖x‖) / 4
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R ≤ 1 := by dsimp [R]; linarith [norm_nonneg x]
  have hMargin : closedBall x (2 * R) ⊆ unitBall n := by
    intro y hy
    apply mem_ball_zero_iff.mpr
    have hdist : dist y x ≤ 2 * R := mem_closedBall.mp hy
    have hnorm : ‖y‖ ≤ dist y x + ‖x‖ := by
      simpa only [dist_zero_right] using dist_triangle y x (0 : E n)
    dsimp [R] at hdist
    linarith
  obtain ⟨H, hHC, hHE⟩ :=
    exists_dirichlet_continuous_hessian_field_on_ball hD hG hDecay hR hR1 hMargin
  have hInside : ball x (R / 2) ⊆ unitBall n :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hMargin)
  have hLocal : ContDiffOn ℝ 2 w (ball x (R / 2)) :=
    contDiffOn_two_of_dirichlet_continuous_ae_hessian hD hG isOpen_ball hInside hHC hHE
  exact (hLocal.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (by linarith)))).contDiffWithinAt

/-- The original smooth log-density path sequence has a limit which is
classically C² at every interior point.  Its first jet remains Lipschitz on
the closed ball, and the original a.e. determinant identity is retained. -/
theorem exists_dirichlet_limit_interior_C2_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      ContinuousOn w (closedUnitBall n) ∧
      ContDiffOn ℝ 2 w (unitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef ∧
        (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (t₀ * g x)) := by
  obtain ⟨w, G, L, hwC, hD, hLip, hw0, hH, hDecay⟩ :=
    exists_dirichlet_limit_with_hessian_oscillation_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  exact ⟨w, G, L, hwC, contDiffOn_two_of_dirichlet_hessian_oscillation hD hLip hDecay,
    hD, hLip, hw0, hH⟩

end KEBall
