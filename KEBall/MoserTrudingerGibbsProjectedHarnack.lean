import KEBall.MoserTrudingerGibbsProjectedSource
import KEBall.MoserTrudingerGibbsCofactorUniform
import KEBall.DirichletBoundaryAverageHarnack

/-! A common Harnack estimate for the actual projected Hessian defects
along the Gibbs iteration.  Both the coefficient constants and the
quadratic source amplitude are independent of the iteration number. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open MeasureTheory Metric Set
open scoped ComplexOrder ContDiff

namespace KEBall.MoserTrudinger

theorem exists_uniform_projected_defect_harnack_of_smoothGibbs_trace
    {n : ℕ} (hn : 2 ≤ n) {γ B D : ℝ} (hγ : 0 ≤ γ) (hD : 0 < D)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0)
    (hTrace : ∀ j x, x ∈ closedUnitBall n → (complexHessian (u (j + 1)) x).trace.re ≤ D) :
    ∃ c C S : ℝ, 0 < c ∧ 1 ≤ C ∧ 0 ≤ S ∧
      ∀ (j : ℕ) (v : E n) (M : ℝ) (x₀ : E n) (R : ℝ),
        0 < R → closedBall x₀ R ⊆ unitBall n →
        (∀ x ∈ ball x₀ R, complexProjectedHessian (u (j + 2)) x v v ≤ M) →
        ∀ y ∈ ball x₀ (R / 4),
          (∫ x, M - complexProjectedHessian (u (j + 2)) x v v
            ∂dirichletBallProbability x₀ (R / 4)) ≤
              C * (M - complexProjectedHessian (u (j + 2)) y v v +
                (S * ‖v‖ ^ 2) / (4 * n * c) * R ^ 2) := by
  have hn0 : 0 < n := by omega
  obtain ⟨a, b, ha, hb, hDensity⟩ := exists_power_density_bounds_of_bounded_family hn0 hγ
    (fun j => (hu j).continuous.continuousOn) huB
  obtain ⟨c, K, hc, hK, hCoeff⟩ := exists_uniform_cofactor_bounds_of_smoothGibbs_trace
    hn0 hγ hD hu huP hEq huB hTrace
  obtain ⟨C, hC, hHarnack⟩ := exists_uniform_smooth_cofactor_source_average_harnack hn hc hK.le
  let S : ℝ := 2 * γ * b ^ n * D
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨c, C, S, hc, hC, hS, ?_⟩
  intro j v M x₀ R hR hBall hM y hy
  let q : E n → ℝ := fun x => M - complexProjectedHessian (u (j + 2)) x v v
  have hq : ContDiff ℝ ∞ q := contDiff_const.sub
    (((complexProjectedHessian_contDiff (hu (j + 2))).clm_apply contDiff_const).clm_apply
      contDiff_const)
  apply hHarnack (u (j + 2))
    ⟨univ, isOpen_univ, subset_univ _, (hu (j + 2)).contDiffOn⟩ (huP (j + 2))
    (fun x hx => (hCoeff (j + 1) x (ball_subset_closedBall hx)).1)
    (fun x hx => (hCoeff (j + 1) x (ball_subset_closedBall hx)).2)
    q ⟨univ, isOpen_univ, subset_univ _, hq.contDiffOn⟩ (S * ‖v‖ ^ 2)
    (mul_nonneg hS (sq_nonneg _)) ?_ x₀ R hR hBall
    (fun x hx => sub_nonneg.mpr (hM x hx)) y hy
  intro x hx
  exact gibbs_projected_defect_cofactor_source_bound hn0 hγ (pow_pos hb n).le hD.le
    (hu (j + 2)) (hu (j + 1)) (huP (j + 2)) (huP (j + 1)) (hEq (j + 1))
    (fun z hz => (hDensity (j + 1) z (ball_subset_closedBall hz)).2)
    (fun z hz => hTrace j z (ball_subset_closedBall hz)) M v hx

theorem exists_uniform_projected_defect_harnack_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ c C S : ℝ, 0 < c ∧ 1 ≤ C ∧ 0 ≤ S ∧
      ∀ (j : ℕ) (v : E n) (Q : ℝ) (x₀ : E n) (R : ℝ),
        0 < R → closedBall x₀ R ⊆ unitBall n →
        (∀ x ∈ ball x₀ R, complexProjectedHessian (u (j + 2)) x v v ≤ Q) →
        ∀ y ∈ ball x₀ (R / 4),
          (∫ x, Q - complexProjectedHessian (u (j + 2)) x v v
            ∂dirichletBallProbability x₀ (R / 4)) ≤
              C * (Q - complexProjectedHessian (u (j + 2)) y v v +
                (S * ‖v‖ ^ 2) / (4 * n * c) * R ^ 2) := by
  obtain ⟨_, _, D, hD, _, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration
      (by omega : 0 < n) hγ hu hu0 huP hEq hM huB
  exact exists_uniform_projected_defect_harnack_of_smoothGibbs_trace
    hn hγ hD hu huP hEq huB hTrace

end KEBall.MoserTrudinger
