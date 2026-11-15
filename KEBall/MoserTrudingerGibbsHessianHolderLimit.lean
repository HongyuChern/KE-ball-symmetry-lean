import KEBall.DirichletHessianHolderLimit
import KEBall.MoserTrudingerGibbsRealHessianHolder

/-! The scaled full Hessian Holder estimate is retained by the same
actual Gibbs first-jet limit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open Filter Metric Set
open scoped ComplexOrder ContDiff NNReal Topology

namespace KEBall.MoserTrudinger

theorem scaled_realHessian_holder_of_bounded_smoothGibbs_firstJet_limit
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 ≤ γ)
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0)
    {ι : ℕ → ℕ} (hι : StrictMono ι) {w : E n → ℝ} {Dw : E n → E n →L[ℝ] ℝ}
    (hU : TendstoUniformlyOn (fun j => u (ι j)) w atTop (closedUnitBall n))
    (hDU : TendstoUniformlyOn (fun j => fderiv ℝ (u (ι j))) Dw atTop (closedUnitBall n)) :
    ∃ α H : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ H ∧
      ∀ (p : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall p (2 * R) ⊆ unitBall n →
        ∀ x ∈ ball p (R / 2), ∀ y ∈ ball p (R / 2),
          ‖realHessian w x - realHessian w y‖ ≤ (H * (4 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
  obtain ⟨N, hN, hNorm⟩ := exists_uniform_realHessian_bound_of_bounded_smoothGibbsIteration
    (by omega : 0 < n) hγ hu hu0 huP hEq hM huB
  obtain ⟨α, K, hα, hα1, hK, hHolder⟩ :=
    exists_uniform_scaled_realHessian_holder_of_bounded_smoothGibbsIteration hn hγ hu hu0 huP hEq hM huB
  refine ⟨α, K * (2 : ℝ) ^ α, hα, hα1, by positivity, ?_⟩
  intro p R hR hR1 hBall
  let κ (j : ℕ) := ι (j + 2)
  have hκ (j : ℕ) : 2 ≤ κ j := (by omega : 2 ≤ j + 2).trans (hι.id_le (j + 2))
  have hSub : ball p (R / 2) ⊆ closedUnitBall n :=
    ((ball_subset_ball (by linarith : R / 2 ≤ 2 * R)).trans ball_subset_closedBall).trans
      (hBall.trans ball_subset_closedBall)
  have hUκ : TendstoUniformlyOn (fun j => u (κ j)) w atTop (closedUnitBall n) := by
    rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
    intro ε hε
    exact (tendsto_add_atTop_nat 2).eventually (hU ε hε)
  have hDκ : TendstoUniformlyOn (fun j => fderiv ℝ (u (κ j))) Dw atTop (closedUnitBall n) := by
    rw [Metric.tendstoUniformlyOn_iff] at hDU ⊢
    intro ε hε
    exact (tendsto_add_atTop_nat 2).eventually (hDU ε hε)
  let β : ℝ≥0 := ⟨α, hα.le⟩
  let KL : ℝ≥0 := ⟨K * (8 / R : ℝ) ^ α, by positivity⟩
  have hβ : 0 < β := hα
  have hH : ∀ j, HolderOnWith KL β (fderiv ℝ (fderiv ℝ (u (κ j)))) (ball p (R / 2)) := by
    intro j
    apply dirichlet_holderOnWith_of_norm_bound (by positivity) hα.le
    intro x hx y hy
    have h := hHolder (κ j - 2) p R hR hR1 hBall x hx y hy
    simpa only [Nat.sub_add_cancel (hκ j), realHessian] using h
  have hLim := hessian_holder_of_uniform_firstJet_limit_on_ball
    (fun j => hu (κ j)) (N := (⟨N, hN.le⟩ : ℝ≥0)) hβ (hUκ.mono hSub) (hDκ.mono hSub)
    (fun j x hx => hNorm (κ j) x (hSub hx)) hH
  intro x hx y hy
  have h := hLim.dist_le hx hy
  simp only [dist_eq_norm] at h
  change ‖realHessian w x - realHessian w y‖ ≤
    (K * (8 / R : ℝ) ^ α) * ‖x - y‖ ^ α at h
  have he : (8 / R : ℝ) ^ α = (2 : ℝ) ^ α * (4 / R : ℝ) ^ α := by
    rw [show (8 / R : ℝ) = 2 * (4 / R) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 4 / R)]
  exact h.trans_eq (by rw [he]; ring)

end KEBall.MoserTrudinger
