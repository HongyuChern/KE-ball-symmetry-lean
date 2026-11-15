import KEBall.DirichletFirstJetHolderCompactness
import KEBall.MoserTrudingerGibbsClosedGradientHolder
import KEBall.MoserTrudingerGibbsIterationLimit
import KEBall.MoserTrudingerUniformLimitValue
import KEBall.MoserTrudingerWeakGibbsExtension

/-! A genuine C1 closed-ball weak Gibbs fixed point from the inverse iteration,
with its actual Cegrell variational value. This does not claim C2 regularity
or the frozen smooth attainment endpoint. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal NNReal Topology

namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell

local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)

theorem exists_C1_weakGibbs_limit_of_bounded_smoothGibbsIteration
    {n : ℕ} (hn : 2 ≤ n) {γ M B : ℝ} (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    {u : ℕ → E n → ℝ} (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n →
      (complexHessian (u (j + 1)) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j x, x ∈ closedUnitBall n → -B ≤ u j x ∧ u j x ≤ 0) :
    ∃ (ι : ℕ → ℕ) (w : E n → ℝ) (Dw : E n → E n →L[ℝ] ℝ),
      StrictMono ι ∧
      TendstoUniformlyOn (fun j => u (ι j)) w atTop (closedUnitBall n) ∧
      TendstoUniformlyOn (fun j => fderiv ℝ (u (ι j))) Dw atTop (closedUnitBall n) ∧
      ∃ hw : IsWeakGibbsSolution n γ w,
        ContDiffOn ℝ 1 w (closedUnitBall n) ∧
        (∀ x ∈ unitBall n, HasFDerivAt w (Dw x) x) ∧
        (∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (Dw x) (closedUnitBall n) x) ∧
        (∃ θ K : ℝ≥0, 0 < θ ∧ θ < 1 ∧ HolderOnWith K θ Dw (closedUnitBall n)) ∧
        ∀ j, (smoothFunctional γ (u j) : EReal) ≤ finiteEnergyFunctional γ hw.memE0.isE1 := by
  have hn0 : 0 < n := by omega
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration hn0 hγ.le hu hu0 huP hEq hM huB
  obtain ⟨θ, K, hθ, hθ1, hHolder⟩ :=
    exists_uniform_closed_gradient_holder_of_smoothGibbs_bounds hn hD hG.le hu hu0 huP hTrace hGrad
  let uNear (j : ℕ) : SmoothNear (closedUnitBall n) (u j) :=
    ⟨univ, isOpen_univ, subset_univ _, (hu j).contDiffOn⟩
  have hAmp (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) : ‖u j x‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_of_nonpos (huB j x hx).2]
    linarith only [(huB j x hx).1]
  have hAE (j : ℕ) : ∀ᵐ x ∂ν[n], u j x ∈ Icc (-B) 0 := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact huB j x (ball_subset_closedBall hx)
  obtain ⟨φ, v, Dv, hφ, hvU, _, _, _, _, _⟩ :=
    exists_subseq_dirichlet_C1_of_uniform_firstJet_holder
      (K := (⟨G, hG.le⟩ : ℝ≥0)) (D := K) (α := θ)
      (u := fun j => u (j + 1)) (fun j => uNear (j + 1)) hθ
      (fun j => hAmp (j + 1)) (fun j => hGrad (j + 1)) hHolder
  obtain ⟨m, hm, hUpper, hInc⟩ :=
    exists_smoothFunctional_limit_of_gibbsIteration hn0 hγ hγn hu hu0 huP hEq
  have hGap (j : ℕ) := gibbsEntropyGap_le_functional_increase hn0 isOpen_univ (subset_univ _)
    (hu j).contDiffOn (hu (j + 1)).contDiffOn (hu0 j) (hu0 (j + 1))
    (huP j) (huP (j + 1)) hγ (hEq j)
  have hGapL : Tendsto (fun j => gibbsEntropyGap γ (u j) (u (j + 1))) atTop (𝓝 0) := by
    have ht := hInc.const_mul γ
    rw [mul_zero] at ht
    exact tendsto_const_nhds.squeeze ht (fun j => (hGap j).1) (fun j => (hGap j).2)
  let a (j : ℕ) := u (φ j + 1)
  let b (j : ℕ) := u (φ j + 2)
  have haL : ∀ᵐ x ∂ν[n], Tendsto (fun j => a j x) atTop (𝓝 (v x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact hvU.tendsto_at (ball_subset_closedBall hx)
  have hIndex : Tendsto (fun j => φ j + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hGapAB : Tendsto (fun j => gibbsEntropyGap γ (a j) (b j)) atTop (𝓝 0) := by
    simpa only [a, b, Function.comp_def, Nat.add_assoc, Nat.reduceAdd] using hGapL.comp hIndex
  obtain ⟨r, hrU, hr⟩ := exists_weakGibbsLimit_of_vanishing_gap hn0 hγ
    (u := a) (v := b) (fun j => (hu (φ j + 1)).continuous.continuousOn)
    (fun j => uNear (φ j + 2)) (fun j => hu0 (φ j + 2)) (fun j => huP (φ j + 2))
    (fun j x hx => by simpa only [a, b, Nat.add_assoc] using hEq (φ j + 1) x hx)
    (fun j => hAE (φ j + 1)) (fun j => hAE (φ j + 2)) haL hGapAB
  obtain ⟨ψ, w, Dw, hψ, hwU, hwDU, hwD, hwHolder, hwC1, hwClosedD⟩ :=
    exists_subseq_dirichlet_C1_of_uniform_firstJet_holder
      (K := (⟨G, hG.le⟩ : ℝ≥0)) (D := K) (α := θ)
      (u := b) (fun j => uNear (φ j + 2)) hθ
      (fun j => hAmp (φ j + 2)) (fun j => hGrad (φ j + 2))
      (fun j => by simpa only [b, Nat.add_assoc] using hHolder (φ j + 1))
  have hRW : EqOn r w (closedUnitBall n) := by
    intro x hx
    exact tendsto_nhds_unique ((hrU.tendsto_at hx).comp hψ.tendsto_atTop) (hwU.tendsto_at hx)
  have hw : IsWeakGibbsSolution n γ w := hr.congr_closedBall hRW
  let ι (j : ℕ) := φ (ψ j) + 2
  have hι : StrictMono ι := by
    intro j k hjk
    exact Nat.add_lt_add_right (hφ (hψ hjk)) 2
  have hιT : Tendsto ι atTop atTop := hι.tendsto_atTop
  have hValue : (m : EReal) ≤ finiteEnergyFunctional γ hw.memE0.isE1 :=
    finiteEnergyFunctional_ge_of_uniform_smooth_limit hn0
      (fun j => hu (ι j)) (fun j => hu0 (ι j)) (fun j => huP (ι j))
      (fun j => hAE (ι j)) hwU (hm.comp hιT) hw
  refine ⟨ι, w, Dw, hι, hwU, hwDU, hw, hwC1, hwD, hwClosedD,
    ⟨θ, K, hθ, hθ1, hwHolder⟩, ?_⟩
  intro j
  exact (EReal.coe_le_coe_iff.mpr (hUpper j)).trans hValue

theorem exists_C1_weakGibbs_ge_smooth_subcritical
    {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    ∃ (w : E n → ℝ) (Dw : E n → E n →L[ℝ] ℝ),
      ∃ hw : IsWeakGibbsSolution n γ w,
        ContDiffOn ℝ 1 w (closedUnitBall n) ∧
        (∀ x ∈ unitBall n, HasFDerivAt w (Dw x) x) ∧
        (∀ x ∈ closedUnitBall n, HasFDerivWithinAt w (Dw x) (closedUnitBall n) x) ∧
        (∃ θ K : ℝ≥0, 0 < θ ∧ θ < 1 ∧ HolderOnWith K θ Dw (closedUnitBall n)) ∧
        (smoothFunctional γ v : EReal) ≤ finiteEnergyFunctional γ hw.memE0.isE1 := by
  obtain ⟨u, M, B, G, D, hInit, hu, hu0, huP, hEq, _, hM, _, huB, _, _, _, _⟩ :=
    exists_uniformly_bounded_smoothGibbsIteration hn hγ hγn hv hv0 hvP
  obtain ⟨ι, w, Dw, _, _, _, hw, hwC1, hwD, hwClosedD, hwHolder, hValue⟩ :=
    exists_C1_weakGibbs_limit_of_bounded_smoothGibbsIteration hn hγ hγn hu hu0 huP hEq hM huB
  refine ⟨w, Dw, hw, hwC1, hwD, hwClosedD, hwHolder, ?_⟩
  simpa only [hInit] using hValue 0

end KEBall.MoserTrudinger
