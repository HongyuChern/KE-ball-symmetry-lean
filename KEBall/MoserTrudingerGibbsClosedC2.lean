import KEBall.MoserTrudingerGibbsInteriorLimit
import KEBall.MoserTrudingerGibbsHessianHolderLimit
import KEBall.MoserTrudingerGibbsBoundaryLimit
import KEBall.DirichletClosedBallEllipticity

/-! Closed-ball C2 regularity and strict within-Hessian positivity of the
same genuine Gibbs fixed point selected by the inverse iteration. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal NNReal Topology

namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell

theorem closedBall_C2_of_firstJet_limit_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0)
    {ι : ℕ → ℕ} (hι : StrictMono ι)
    {w : E n → ℝ} {Dw : E n → E n →L[ℝ] ℝ}
    (hU : TendstoUniformlyOn (fun j => u (ι j)) w atTop (closedUnitBall n))
    (hDU : TendstoUniformlyOn (fun j => fderiv ℝ (u (ι j))) Dw atTop (closedUnitBall n))
    (hwC : ContinuousOn w (closedUnitBall n))
    (hDclosed : ∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (Dw x) (closedUnitBall n) x)
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (Dw x) x)
    (hw0 : ∀ x ∈ unitSphere n, w x = 0) :
    ContDiffOn ℝ 2 w (closedUnitBall n) ∧ ContDiffOn ℝ ∞ w (unitBall n) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = gibbsDensity γ w x) ∧
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian w x).PosDef ∧
        (dirichletWithinComplexHessian w x).det.re = gibbsDensity γ w x) := by
  have hn0 : 0 < n := by omega
  obtain ⟨L, hL⟩ := exists_uniform_lipschitz_firstJet_of_bounded_smoothGibbsIteration
    hn0 hγ.le hu hu0 huP hEq hM huB
  have hLip : LipschitzOnWith L Dw (closedUnitBall n) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hDU.tendsto_at hx).dist (hDU.tendsto_at hy))
      (Eventually.of_forall fun j => (hL (ι j)).dist_le_mul x hx y hy)
  obtain ⟨hwS, hwPos, hwEq⟩ :=
    interior_smooth_of_firstJet_limit_of_bounded_smoothGibbsIteration
      hn hγ hγn hu hu0 huP hEq hM huB hι hU hDU hwC
  have hw2 : ContDiffOn ℝ 2 w (unitBall n) :=
    hwS.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hHolder := scaled_realHessian_holder_of_bounded_smoothGibbs_firstJet_limit
    hn hγ.le hu hu0 huP hEq hM huB hι hU hDU
  have hPower := hasDirichletRotationBoundaryPower_of_bounded_smoothGibbs_firstJet_limit
    hn hγ.le hu hu0 huP hEq hM huB hι hDU
  have hfC : ContinuousOn (gibbsDensity γ w) (closedUnitBall n) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hwC)).div_const _
  have hfPos (x : E n) (_hx : x ∈ closedUnitBall n) : 0 < gibbsDensity γ w x :=
    div_pos (Real.exp_pos _) (normalizingIntegral_pos_of_continuousOn hn0 hwC γ)
  have hwClosed := contDiffOn_two_dirichlet_of_rotation_boundary_power hn0
    hwC hw2 hDclosed hD hLip hw0 hHolder hPower hfC hfPos hwPos hwEq
  have hClosed := closedBall_withinHessian_posDef_and_det_of_C2 hwClosed hfC hfPos hwPos hwEq
  exact ⟨hwClosed, hwS, hwPos, hwEq, hClosed⟩

theorem exists_closedBall_C2_weakGibbs_ge_smooth_subcritical
    {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    ∃ w : E n → ℝ, ∃ hw : IsWeakGibbsSolution n γ w,
      ContDiffOn ℝ 2 w (closedUnitBall n) ∧ ContDiffOn ℝ ∞ w (unitBall n) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = gibbsDensity γ w x) ∧
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian w x).PosDef) ∧
      (smoothFunctional γ v : EReal) ≤ finiteEnergyFunctional γ hw.memE0.isE1 := by
  obtain ⟨u, M, B, G, D, hInit, hu, hu0, huP, hEq, _, hM, _, huB, _, _, _, _⟩ :=
    exists_uniformly_bounded_smoothGibbsIteration hn hγ hγn hv hv0 hvP
  obtain ⟨ι, w, Dw, hι, hU, hDU, hw, _, hD, hDclosed, _, hValue⟩ :=
    exists_C1_weakGibbs_limit_of_bounded_smoothGibbsIteration hn hγ hγn hu hu0 huP hEq hM huB
  obtain ⟨hwC2, hwS, hwPos, hwEq, hwClosed⟩ :=
    closedBall_C2_of_firstJet_limit_of_bounded_smoothGibbsIteration
      hn hγ hγn hu hu0 huP hEq hM huB hι hU hDU hw.continuousOn hDclosed hD hw.zero_on_sphere
  refine ⟨w, hw, hwC2, hwS, hwPos, hwEq, (fun x hx => (hwClosed x hx).1), ?_⟩
  simpa only [hInit] using hValue 0

end KEBall.MoserTrudinger
