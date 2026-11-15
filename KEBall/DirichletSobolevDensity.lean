import KEBall.DirichletSmoothBounds
import KEBall.DirichletSobolevGraph

/-! Strong approximation by inward mollification in each Sobolev norm. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions ENNReal NNReal Topology
open PshLines (shrinkingBump shrinkingBump_rOut_le tendsto_shrinkingBump_rOut)

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private theorem tendsto_L2_of_ae_tendsto_of_eventually_norm_le {n : ℕ}
    {X : ℕ → DirichletBallL2 n ℝ} {Y : DirichletBallL2 n ℝ}
    (hAe : ∀ᵐ x ∂ν[n], Tendsto (fun j => X j x) atTop (𝓝 (Y x)))
    (hU : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ‖X j‖ ^ 2 ≤ ‖Y‖ ^ 2 + ε) :
    Tendsto X atTop (𝓝 Y) := by
  let Z (j : ℕ) := X j + Y
  have hZAe : ∀ᵐ x ∂ν[n], Tendsto (fun j => Z j x) atTop (𝓝 ((Y + Y : DirichletBallL2 n ℝ) x)) := by
    filter_upwards [hAe, ae_all_iff.mpr (fun j => Lp.coeFn_add (X j) Y), Lp.coeFn_add Y Y] with x hx hX hY
    rw [hY]
    exact (hx.add tendsto_const_nhds).congr (fun j => (hX j).symm)
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun j => (Lp.memLp (Z j)).aestronglyMeasurable) _ hZAe
  simp only [← Lp.enorm_def] at hFatou
  have hLow (δ : ℝ) (hδ : 0 < δ) (hδY : δ < 2 * ‖Y‖) :
      ∀ᶠ j in atTop, 2 * ‖Y‖ - δ < ‖Z j‖ := by
    have hYpos : 0 < ‖Y‖ := by linarith only [hδ, hδY]
    have h : ENNReal.ofReal (2 * ‖Y‖ - δ) < ‖Y + Y‖ₑ := by
      rw [← ofReal_norm, ← two_smul ℝ, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * ‖Y‖) |>.mpr
        (by linarith only [hδ])
    have hEv := eventually_lt_of_lt_liminf (h.trans_le hFatou)
      (by isBoundedDefault : IsBoundedUnder (· ≥ ·) atTop (fun j => ‖Z j‖ₑ))
    filter_upwards [hEv] with j hj
    rw [← ofReal_norm] at hj
    have hZpos : 0 < ‖Z j‖ := by
      by_contra! hn
      rw [ENNReal.ofReal_eq_zero.mpr hn] at hj
      exact not_lt_zero hj
    exact (ENNReal.ofReal_lt_ofReal_iff hZpos).mp hj
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_cases hY : Y = 0
  · filter_upwards [hU (ε ^ 2 / 2) (by positivity)] with j hj
    rw [hY, norm_zero] at hj
    rw [hY, dist_zero_right]
    nlinarith only [hj, hε, norm_nonneg (X j), sq_pos_of_pos hε]
  · have hYpos := norm_pos_iff.mpr hY
    let δ := min ‖Y‖ (ε ^ 2 / (16 * ‖Y‖))
    have hδ : 0 < δ := lt_min hYpos (by positivity)
    have hδY : δ < 2 * ‖Y‖ := (min_le_left _ _).trans_lt (by linarith only [hYpos])
    have hSmall : 4 * ‖Y‖ * δ ≤ ε ^ 2 / 4 := by
      calc
        _ ≤ 4 * ‖Y‖ * (ε ^ 2 / (16 * ‖Y‖)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        _ = _ := by field_simp; ring
    filter_upwards [hLow δ hδ hδY, hU (ε ^ 2 / 8) (by positivity)] with j hL hJ
    have hSq : (2 * ‖Y‖ - δ) ^ 2 ≤ ‖Z j‖ ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr hδY.le) hL.le 2
    have hPar := parallelogram_law_with_norm_mul ℝ (X j) Y
    change ‖Z j‖ * ‖Z j‖ + ‖X j - Y‖ * ‖X j - Y‖ = _ at hPar
    rw [dist_eq_norm]
    by_contra! hContra
    have hContraSq := pow_le_pow_left₀ hε.le hContra 2
    nlinarith only [hSq, hJ, hPar, hSmall, sq_nonneg δ, hContraSq, sq_pos_of_pos hε]

private theorem memLp_dirichlet_continuous {n : ℕ} (hn : 0 < n) {f : E n → ℝ}
    (hf : Continuous f) : MemLp f 2 ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  exact hC x (ball_subset_closedBall hx)

private theorem norm_sq_eq_integral_sq {n : ℕ} (w : DirichletBallL2 n ℝ) :
    ‖w‖ ^ 2 = ∫ x, (w x) ^ 2 ∂ν[n] := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply, pow_two]

/-- Every finite directional derivative of the inward mollifications converges
strongly in L² to the corresponding weak derivative. -/
theorem tendsto_dirichletSmoothApproximation_derivative_L2 {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (ds : List (E n)) (hf : HasDirichletWeakDerivativesL2 f ds.length)
    (F : DirichletBallL2 n ℝ)
    (he : ∀ ψ : 𝓓B[n], dirichletWeakDerivativeTest f ds ψ = ∫ x, ψ x * F x ∂ν[n]) :
    ∃ X : ℕ → DirichletBallL2 n ℝ,
      (∀ j, X j =ᵐ[ν[n]] ds.foldr (fun d D y => fderiv ℝ D y d)
        (dirichletSmoothApproximation f j)) ∧ Tendsto X atTop (𝓝 F) := by
  let g (j : ℕ) := ds.foldr (fun d D y => fderiv ℝ D y d) (dirichletSmoothApproximation f j)
  have hg (j : ℕ) : MemLp (g j) 2 ν[n] :=
    memLp_dirichlet_continuous hn
      (iteratedLineDerivative_contDiff (contDiff_dirichletSmoothApproximation hf.1 j) ds).continuous
  let X (j : ℕ) := (hg j).toLp (g j)
  have hX (j : ℕ) : X j =ᵐ[ν[n]] g j := MemLp.coeFn_toLp (hg j)
  refine ⟨X, hX, tendsto_L2_of_ae_tendsto_of_eventually_norm_le ?_ ?_⟩
  · filter_upwards [ae_all_iff.mpr hX,
      ae_tendsto_iteratedLineDerivative_dilatedDirichletTranslationPairing ds hf (Lp.memLp F)
        he (1 / 2) (by norm_num)] with x hx hA
    exact hA.congr (fun j => (hx j).symm)
  · let φ := shrinkingBump (E := E n) (1 / 2) (by norm_num)
    let a (j : ℕ) := 1 - (φ j).rOut
    have ha (j : ℕ) : 0 < a j := by
      have h := shrinkingBump_rOut_le (E := E n) (1 / 2) (by norm_num) j
      change (φ j).rOut ≤ (1 : ℝ) / 2 at h
      dsimp only [a]
      linarith only [h]
    have hNorm (j : ℕ) : ‖X j‖ ^ 2 ≤ (a j ^ (2 * n))⁻¹ * ‖F‖ ^ 2 := by
      rw [norm_sq_eq_integral_sq, norm_sq_eq_integral_sq]
      have hInt : (∫ x, (X j x) ^ 2 ∂ν[n]) = ∫ x, g j x ^ 2 ∂ν[n] :=
        integral_congr_ae ((hX j).mono fun x hx => congrArg (fun t : ℝ => t ^ 2) hx)
      rw [hInt]
      exact setIntegral_sq_iteratedLineDerivative_dilatedMollification_le (φ j) (ha j)
        (by dsimp only [a]; linarith) ds hf (Lp.memLp F) he
    have haLim : Tendsto a atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (tendsto_shrinkingBump_rOut (E := E n) (1 / 2) (by norm_num))
    have hT : Tendsto (fun j => (a j ^ (2 * n))⁻¹ * ‖F‖ ^ 2) atTop (𝓝 (‖F‖ ^ 2)) := by
      have hp : Tendsto (fun j => a j ^ (2 * n)) atTop (𝓝 1) := by simpa using haLim.pow (2 * n)
      simpa using (hp.inv₀ one_ne_zero).mul_const (‖F‖ ^ 2)
    intro ε hε
    filter_upwards [hT.eventually (gt_mem_nhds (lt_add_of_pos_right (‖F‖ ^ 2) hε))] with j hj
    exact (hNorm j).trans hj.le

private theorem dirichletWeakDerivativeTest_eq_classical {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ContDiff ℝ ∞ f) (ds : List (E n)) (ψ : 𝓓B[n]) :
    dirichletWeakDerivativeTest f ds ψ =
      ∫ x, ψ x * (ds.foldr (fun d D y => fderiv ℝ D y d) f) x ∂ν[n] := by
  induction ds generalizing ψ with
  | nil => rfl
  | cons d ds ih =>
      rw [dirichletWeakDerivativeTest, ih]
      have hD := iteratedLineDerivative_contDiff hf ds
      have he := integral_dirichletTest_fieldDerivative_mul_smooth hn ψ hD
        (contDiff_const (c := d))
      dsimp only at he
      have hz (x : E n) : dirichletVectorDivergence (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
          (fun _ => d) x = 0 := by simp [dirichletVectorDivergence]
      simp only [hz, mul_zero, add_zero] at he
      exact neg_eq_iff_eq_neg.mpr he

/-- A smooth function determines an element of the Sobolev graph by its
classical derivatives. -/
noncomputable def dirichletSobolevJetOfSmooth {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) : dirichletSobolevJetGraph (k := k) b := by
  let F (i : DirichletJetIndex n k) := (dirichletJetDirections b i).foldr
    (fun d D y => fderiv ℝ D y d) f
  let h0 := memLp_dirichlet_continuous hn hf.continuous
  have hF (i : DirichletJetIndex n k) : MemLp (F i) 2 ν[n] :=
    memLp_dirichlet_continuous hn (iteratedLineDerivative_contDiff hf _).continuous
  let z : DirichletJetGraphAmbient n k := (h0.toLp f, fun i => (hF i).toLp (F i))
  refine ⟨z, (mem_dirichletSobolevJetGraph_iff b z).mpr fun i ψ => ?_⟩
  have hPair (τ : 𝓓B[n]) : (∫ x, τ x * z.1 x ∂ν[n]) = ∫ x, τ x * f x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp h0] with x hx
    change τ x * (h0.toLp f) x = τ x * f x
    rw [hx]
  rw [dirichletWeakDerivativeTest_congr_tested hPair, dirichletWeakDerivativeTest_eq_classical hn hf]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hF i)] with x hx
  change ψ x * F i x = ψ x * ((hF i).toLp (F i)) x
  rw [hx]

theorem dirichletSobolevJetOfSmooth_fst_ae {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    (dirichletSobolevJetOfSmooth (k := k) hn b hf).val.1 =ᵐ[ν[n]] f :=
  MemLp.coeFn_toLp (memLp_dirichlet_continuous hn hf.continuous)

theorem dirichletSobolevJetOfSmooth_snd_ae {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : DirichletJetIndex n k) :
    (dirichletSobolevJetOfSmooth (k := k) hn b hf).val.2 i =ᵐ[ν[n]]
      (dirichletJetDirections b i).foldr (fun d D y => fderiv ℝ D y d) f :=
  MemLp.coeFn_toLp (memLp_dirichlet_continuous hn (iteratedLineDerivative_contDiff hf _).continuous)

/-- Inward mollification converges in the full finite-order Sobolev graph. -/
theorem tendsto_dirichletSobolevJetOfSmoothApproximation {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (z : dirichletSobolevJetGraph (k := k) b) :
    Tendsto (fun j => dirichletSobolevJetOfSmooth hn b
      (contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j)) atTop (𝓝 z) := by
  let w (j : ℕ) : dirichletSobolevJetGraph (k := k) b :=
    dirichletSobolevJetOfSmooth hn b (contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j)
  have hReg := hasDirichletWeakDerivativesL2_of_jetGraph hn b z
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun j => ((w j).val.1, (w j).val.2)) atTop (𝓝 (z.val.1, z.val.2))
  rw [nhds_prod_eq]
  apply Tendsto.prodMk
  · obtain ⟨X, hX, hL⟩ := tendsto_dirichletSmoothApproximation_derivative_L2 hn []
      (HasDirichletWeakDerivativesL2.zero_order (Lp.memLp z.val.1)) z.val.1 (fun _ => rfl)
    refine hL.congr fun j => Lp.ext ((hX j).trans ?_)
    exact (dirichletSobolevJetOfSmooth_fst_ae hn b
      (contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j)).symm
  · apply tendsto_pi_nhds.mpr
    intro i
    have hi : (dirichletJetDirections b i).length ≤ k := by
      simpa only [dirichletJetDirections, List.length_ofFn] using Nat.le_of_lt_succ i.1.isLt
    obtain ⟨X, hX, hL⟩ := tendsto_dirichletSmoothApproximation_derivative_L2 hn
      (dirichletJetDirections b i) (hReg.of_le hi) (z.val.2 i)
      ((mem_dirichletSobolevJetGraph_iff b z.val).mp z.property i)
    refine hL.congr fun j => Lp.ext ((hX j).trans ?_)
    exact (dirichletSobolevJetOfSmooth_snd_ae hn b
      (contDiff_dirichletSmoothApproximation (Lp.memLp z.val.1) j) i).symm

end KEBall
