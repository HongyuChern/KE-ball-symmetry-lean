import KEBall.DirichletLogDensityInteriorHolder
import KEBall.DirichletHessianScaledHolder

/-!
# Interior regularity while retaining the original C1 convergence

The same w,G carry the convergence, weak cofactor equation and oscillation
decay.  This interface is used to pass boundary estimates to that limit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions ENNReal Gradient NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem exists_dirichlet_C1_limit_with_hessian_oscillation_of_logDensityPath {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      StrictMono φ ∧ TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      ContinuousOn w (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef ∧
        (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (t₀ * g x)) ∧
      HasDirichletHessianOscillationDecay G := by
  obtain ⟨φ, w, G, L, hφ, hUw, hGrad, hwC, hD, hLip, hw0, hH, hA,
      hEllData, hDiv, _, hSecond⟩ :=
    exists_dirichlet_C1_limit_with_divergence_free_cofactor_of_logDensityPath
      (by omega : 0 < n) hg ht hT hu hu0 huP hEq
  obtain ⟨c, C, hc, hC, hEll⟩ := hEllData
  have hHarnack : HasDirichletHessianWeakHarnack G c := by
    obtain ⟨H, hH₀, hEstimate⟩ := exists_correctedHessian_weakHarnack hn hg t₀ hLip hA hDiv hc
      (hEll.mono fun x hx v => (hx v).1)
    refine ⟨H, hH₀, fun v => ?_⟩
    obtain ⟨F, hWeak, hSub⟩ := hSecond v
    exact hEstimate v F (Lp.memLp F) hWeak hSub
  have hg' : SmoothNear (closedUnitBall n) (fun x => t₀ * g x) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, contDiffOn_const.mul hgU⟩
  exact ⟨φ, w, G, L, hφ, hUw, hGrad, hwC, hD, hLip, hw0, hH,
    hasDirichletHessianOscillationDecay_of_cofactor (by omega) hLip hg'
      (hH.mono fun _ hx => hx.1) (hH.mono fun _ hx => hx.2) hA hc
      (hEll.mono fun _ hx v => (hx v).1) hHarnack⟩

theorem exists_dirichlet_C1_interior_classical_holder_limit_of_logDensityPath
    {n : ℕ} (hn : 2 ≤ n) {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (φ : ℕ → ℕ) (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0) (α H : ℝ),
      StrictMono φ ∧ TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (φ j))) G atTop (closedUnitBall n) ∧
      0 < α ∧ α ≤ 1 ∧ 0 ≤ H ∧
      ContDiffOn ℝ 1 w (closedUnitBall n) ∧ ContDiffOn ℝ 2 w (unitBall n) ∧
      (∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (G x) (closedUnitBall n) x) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧ (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      HasDirichletHessianOscillationDecay G ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
          ‖realHessian w x - realHessian w y‖ ≤
            (H * (4 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
  obtain ⟨φ, w, G, L, hφ, hUw, hGrad, hwC, hD, hLip, hw0, hAe, hDecay⟩ :=
    exists_dirichlet_C1_limit_with_hessian_oscillation_of_logDensityPath hn hg ht hT hu hu0 huP hEq
  have hw2 := contDiffOn_two_of_dirichlet_hessian_oscillation hD hLip hDecay
  obtain ⟨α, H, hα0, hα1, hH, hHolder⟩ :=
    exists_dirichlet_realHessian_scaled_holder_of_oscillation hD hLip hDecay
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
  exact ⟨φ, w, G, L, α, H, hφ, hUw, hGrad, hα0, hα1, hH,
    contDiffOn_one_dirichlet_closedBall hwC hLip.continuousOn hD, hw2,
    fun _ hx => hasFDerivWithinAt_dirichlet_closedBall hwC hLip.continuousOn hD hx,
    hD, hLip, hw0, hPos, fun _ hx => hPoint hx, hDecay, hHolder⟩

end KEBall
