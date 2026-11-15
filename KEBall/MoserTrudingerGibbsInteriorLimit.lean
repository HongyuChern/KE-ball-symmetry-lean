import KEBall.DirichletInteriorDensityLimit
import KEBall.DirichletNonlinearHolderBootstrap
import KEBall.MoserTrudingerGibbsInteriorHessian
import KEBall.MoserTrudingerGibbsFirstJetLimit

/-! Interior smoothness of the same genuine Gibbs first-jet limit.
The preceding inputs are compactified separately; vanishing entropy
identifies their density with that of the actual output limit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal NNReal Topology

namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell
local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem uniform_subseq {X Y : Type*} [MetricSpace Y]
    {u : ℕ → X → Y} {w : X → Y} {s : Set X}
    (hU : TendstoUniformlyOn u w atTop s) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    TendstoUniformlyOn (fun j => u (φ j)) w atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro ε hε
  exact hφ.eventually (hU ε hε)

private theorem local_hessian_bounds_on_closed_balls {n : ℕ}
    {u : ℕ → E n → ℝ} {β : ℝ≥0}
    (hH : ∀ (p : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall p (2 * R) ⊆ unitBall n →
      ∃ C : ℝ≥0, ∀ j,
        (∀ x ∈ ball p (R / 8), ‖fderiv ℝ (fderiv ℝ (u (j + 2))) x‖ ≤ C) ∧
        HolderOnWith C β (fderiv ℝ (fderiv ℝ (u (j + 2)))) (ball p (R / 8)))
    (ι : ℕ → ℕ) (hι : ∀ j, 2 ≤ ι j) :
    ∀ p ∈ unitBall n, ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ unitBall n ∧
      ∃ C : ℝ≥0, ∀ j,
        (∀ x ∈ closedBall p r, ‖fderiv ℝ (fderiv ℝ (u (ι j))) x‖ ≤ C) ∧
        HolderOnWith C β (fderiv ℝ (fderiv ℝ (u (ι j)))) (closedBall p r) := by
  intro p hp
  have hpN : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  let R : ℝ := (1 - ‖p‖) / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by dsimp [R]; linarith [norm_nonneg p]
  have hBall : closedBall p (2 * R) ⊆ unitBall n := by
    intro x hx
    apply mem_ball_zero_iff.mpr
    have hdist : ‖x - p‖ ≤ 2 * R := by simpa only [dist_eq_norm] using mem_closedBall.mp hx
    have hnorm := norm_le_norm_sub_add x p
    dsimp [R] at hdist
    linarith
  obtain ⟨C, hC⟩ := hH p R hR hR1 hBall
  have hSmall : closedBall p (R / 16) ⊆ ball p (R / 8) := closedBall_subset_ball (by linarith)
  have hSub : closedBall p (R / 16) ⊆ unitBall n :=
    (closedBall_subset_closedBall (by linarith : R / 16 ≤ 2 * R)).trans hBall
  refine ⟨R / 16, by positivity, hSub, C, ?_⟩
  intro j
  have hj := hC (ι j - 2)
  rw [Nat.sub_add_cancel (hι j)] at hj
  exact ⟨fun x hx => hj.1 x (hSmall hx), hj.2.mono hSmall⟩

theorem interior_smooth_of_firstJet_limit_of_bounded_smoothGibbsIteration
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
    (hwC : ContinuousOn w (closedUnitBall n)) :
    ContDiffOn ℝ ∞ w (unitBall n) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = gibbsDensity γ w x) := by
  have hn0 : 0 < n := by omega
  obtain ⟨G, hG, D, hD, hGrad, hTrace⟩ :=
    exists_uniform_first_and_trace_bounds_of_smoothGibbsIteration hn0 hγ.le hu hu0 huP hEq hM huB
  obtain ⟨θ, KG, hθ, _, hGH⟩ :=
    exists_uniform_closed_gradient_holder_of_smoothGibbs_bounds hn hD hG.le hu hu0 huP hTrace hGrad
  obtain ⟨β, hβ, hβ1, hH⟩ :=
    exists_uniform_interior_realHessian_holder_of_bounded_smoothGibbsIteration
      hn hγ.le hu hu0 huP hEq hM huB
  let κ (j : ℕ) := ι (j + 2)
  have hκ : StrictMono κ := fun _ _ hj => hι (Nat.add_lt_add_right hj 2)
  have hκ2 (j : ℕ) : 2 ≤ κ j := (by omega : 2 ≤ j + 2).trans (hι.id_le (j + 2))
  let a (j : ℕ) := u (κ j - 1)
  have hAmp (j : ℕ) (x : E n) (hx : x ∈ closedUnitBall n) : ‖u j x‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_of_nonpos (huB j x hx).2]
    linarith only [(huB j x hx).1]
  have hAH (j : ℕ) : HolderOnWith KG θ (fderiv ℝ (a j)) (closedUnitBall n) := by
    have he : κ j - 2 + 1 = κ j - 1 := by have := hκ2 j; omega
    simpa only [a, he] using hGH (κ j - 2)
  obtain ⟨ψ, v, Dv, hψ, hV, _, _, _, hvC1, _⟩ :=
    exists_subseq_dirichlet_C1_of_uniform_firstJet_holder
      (K := (⟨G, hG.le⟩ : ℝ≥0)) (D := KG) (α := θ) (u := a)
      (fun j => ⟨univ, isOpen_univ, subset_univ _, (hu (κ j - 1)).contDiffOn⟩)
      hθ (fun j => hAmp (κ j - 1)) (fun j => hGrad (κ j - 1)) hAH
  let aa (j : ℕ) := a (ψ j)
  let b (j : ℕ) := u (κ (ψ j))
  have hOutU : TendstoUniformlyOn b w atTop (closedUnitBall n) :=
    uniform_subseq (uniform_subseq hU (tendsto_add_atTop_nat 2)) hψ.tendsto_atTop
  have hOutDU : TendstoUniformlyOn (fun j => fderiv ℝ (b j)) Dw atTop (closedUnitBall n) :=
    uniform_subseq (uniform_subseq hDU (tendsto_add_atTop_nat 2)) hψ.tendsto_atTop
  have hRel (j : ℕ) : κ (ψ j) - 1 + 1 = κ (ψ j) := Nat.sub_add_cancel (by have := hκ2 (ψ j); omega)
  have hAM (j : ℕ) : AEMeasurable (aa j) ν[n] := (hu (κ (ψ j) - 1)).continuous.aemeasurable
  have hBM (j : ℕ) : AEMeasurable (b j) ν[n] := (hu (κ (ψ j))).continuous.aemeasurable
  have hVM : AEMeasurable v ν[n] :=
    (hvC1.continuousOn.mono ball_subset_closedBall).aemeasurable measurableSet_ball
  have hWM : AEMeasurable w ν[n] := (hwC.mono ball_subset_closedBall).aemeasurable measurableSet_ball
  have hAE (j : ℕ) : ∀ᵐ x ∂ν[n], u j x ∈ Icc (-B) 0 := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact huB j x (ball_subset_closedBall hx)
  have hAL : ∀ᵐ x ∂ν[n], Tendsto (fun j => aa j x) atTop (𝓝 (v x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact hV.tendsto_at (ball_subset_closedBall hx)
  have hBL : ∀ᵐ x ∂ν[n], Tendsto (fun j => b j x) atTop (𝓝 (w x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact hOutU.tendsto_at (ball_subset_closedBall hx)
  have hAB (j : ℕ) : ∀ᵐ x ∂ν[n], aa j x ∈ Icc (-B) 0 := hAE (κ (ψ j) - 1)
  have hBB (j : ℕ) : ∀ᵐ x ∂ν[n], b j x ∈ Icc (-B) 0 := hAE (κ (ψ j))
  obtain ⟨_, _, _, hInc⟩ :=
    exists_smoothFunctional_limit_of_gibbsIteration hn0 hγ hγn hu hu0 huP hEq
  have hGap (j : ℕ) := gibbsEntropyGap_le_functional_increase hn0 isOpen_univ (subset_univ _)
    (hu j).contDiffOn (hu (j + 1)).contDiffOn (hu0 j) (hu0 (j + 1))
    (huP j) (huP (j + 1)) hγ (hEq j)
  have hGapL : Tendsto (fun j => gibbsEntropyGap γ (u j) (u (j + 1))) atTop (𝓝 0) := by
    have ht := hInc.const_mul γ
    rw [mul_zero] at ht
    exact tendsto_const_nhds.squeeze ht (fun j => (hGap j).1) (fun j => (hGap j).2)
  have hIndex : Tendsto (fun j => κ (ψ j) - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (hκ.tendsto_atTop.comp hψ.tendsto_atTop)
  have hGapAB : Tendsto (fun j => gibbsEntropyGap γ (aa j) (b j)) atTop (𝓝 0) := by
    simpa only [aa, a, b, Function.comp_def, hRel] using hGapL.comp hIndex
  have hGap0 : gibbsEntropyGap γ v w = 0 := tendsto_nhds_unique
    (tendsto_gibbsEntropyGap_of_ae_of_bounded hn0 hγ.le hAM hBM hVM hWM hAB hBB hAL hBL) hGapAB
  obtain ⟨hZV, _, _, hDL⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn0 hγ.le hAM hVM hAB hAL
  obtain ⟨hZW, _, _, _⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn0 hγ.le hBM hWM hBB hBL
  have hVB : ∀ᵐ x ∂ν[n], v x ∈ Icc (-B) 0 := by
    filter_upwards [hAL, ae_all_iff.mpr hAB] with x hx hI
    exact isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall hI)
  have hWB : ∀ᵐ x ∂ν[n], w x ∈ Icc (-B) 0 := by
    filter_upwards [hBL, ae_all_iff.mpr hBB] with x hx hI
    exact isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall hI)
  have hSame := gibbsDensity_ae_eq_of_entropyGap_eq_zero hn0 hγ.le hVM hWM hVB hWB hZV hZW hGap0
  have hDLw : ∀ᵐ x ∂ν[n], Tendsto (fun j => gibbsDensity γ (aa j) x) atTop
      (𝓝 (gibbsDensity γ w x)) := by
    filter_upwards [hDL, hSame] with x hx he
    exact he ▸ hx
  have hfC : ContinuousOn (gibbsDensity γ w) (unitBall n) :=
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hwC)).div_const _).mono
      ball_subset_closedBall
  have hfPos (x : E n) (_hx : x ∈ unitBall n) : 0 < gibbsDensity γ w x :=
    div_pos (Real.exp_pos _) (zero_lt_one.trans_le hZW)
  obtain ⟨_, hwHolder, hwPos, hwEq⟩ :=
    interior_classical_limit_of_uniform_firstJet_and_local_hessian_holder
      (fun j => hu (κ (ψ j))) hβ hOutU hOutDU
      (local_hessian_bounds_on_closed_balls hH (fun j => κ (ψ j)) (fun j => hκ2 (ψ j)))
      hfC hfPos (fun j => huP (κ (ψ j)))
      (fun j x hx => by simpa only [aa, a, b, hRel] using hEq (κ (ψ j) - 1) x hx) hDLw
  refine ⟨?_, hwPos, hwEq⟩
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_infty_of_positive_determinant_exponential hn0 isOpen_ball hx hβ hβ1
    (hwHolder x hx) (normalizingIntegral γ w)⁻¹ (-γ) hwPos
  intro y hy
  rw [hwEq y hy]
  unfold gibbsDensity
  ring

theorem exists_interior_smooth_weakGibbs_ge_smooth_subcritical
    {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    ∃ w : E n → ℝ, ∃ hw : IsWeakGibbsSolution n γ w,
      ContDiffOn ℝ 1 w (closedUnitBall n) ∧ ContDiffOn ℝ ∞ w (unitBall n) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = gibbsDensity γ w x) ∧
      (smoothFunctional γ v : EReal) ≤ finiteEnergyFunctional γ hw.memE0.isE1 := by
  obtain ⟨u, M, B, G, D, hInit, hu, hu0, huP, hEq, _, hM, _, huB, _, _, _, _⟩ :=
    exists_uniformly_bounded_smoothGibbsIteration hn hγ hγn hv hv0 hvP
  obtain ⟨ι, w, Dw, hι, hU, hDU, hw, hwC1, _, _, _, hValue⟩ :=
    exists_C1_weakGibbs_limit_of_bounded_smoothGibbsIteration hn hγ hγn hu hu0 huP hEq hM huB
  obtain ⟨hwS, hwPos, hwEq⟩ :=
    interior_smooth_of_firstJet_limit_of_bounded_smoothGibbsIteration
      hn hγ hγn hu hu0 huP hEq hM huB hι hU hDU hw.continuousOn
  refine ⟨w, hw, hwC1, hwS, hwPos, hwEq, ?_⟩
  simpa only [hInit] using hValue 0

end KEBall.MoserTrudinger
