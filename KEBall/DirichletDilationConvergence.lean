import KEBall.DirichletMollifierDilation

/-! The inward-dilated approximations still converge to the weak function. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory MeasureTheory.Measure Metric Set
open scoped ContDiff Distributions NNReal Topology
open PshLines (translationPairing contDiff_translationPairing shrinkingBump shrinkingBump_radius_ratio
  tendsto_shrinkingBump_rOut)

namespace KEBall

/-- Simultaneous inward displacement by the mollifier radius preserves
almost-everywhere convergence on the unit ball. -/
theorem ae_tendsto_dilatedDirichletTranslationPairing {n : ℕ} {f : E n → ℝ}
    (hf : MemLp f 2 ((volume0 n).restrict (unitBall n))) (R : ℝ) (hR : 0 < R) :
    let φ : ℕ → ContDiffBump (0 : E n) := shrinkingBump R hR
    ∀ᵐ x ∂((volume0 n).restrict (unitBall n)), Tendsto
      (fun j => translationPairing ((volume0 n).restrict (unitBall n)) f
        ((φ j).normed (volume0 n)) ((1 - (φ j).rOut) • x)) atTop (𝓝 (f x)) := by
  let μ := volume0 n
  let I := (unitBall n).indicator f
  let φ : ℕ → ContDiffBump (0 : E n) := shrinkingBump R hR
  let r (j : ℕ) : ℝ := (φ j).rOut
  have hHaar : μ.IsAddHaarMeasure := by
    change (volume0 n).IsAddHaarMeasure
    unfold volume0
    exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top
  have hI : LocallyIntegrable I μ :=
    ((memLp_indicator_iff_restrict measurableSet_ball).mpr hf).locallyIntegrable (by norm_num)
  have hRadius : Tendsto (fun j => 2 * r j) atTop (𝓝 0) := by
    simpa using (tendsto_shrinkingBump_rOut (E := E n) R hR).const_mul 2
  have hRadius' : Tendsto (fun j => 2 * r j) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hRadius, Eventually.of_forall fun j => by
      have h := (φ j).rOut_pos
      change 0 < 2 * r j
      dsimp only [r]
      positivity⟩
  filter_upwards [ae_restrict_of_ae ((Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hI),
    ae_restrict_mem (μ := μ) (show MeasurableSet (unitBall n) from measurableSet_ball)]
    with x hx hxB
  have hAvg := (hx.comp (Besicovitch.tendsto_filterAt μ x)).comp hRadius'
  let k (j : ℕ) (y : E n) := (φ j).normed μ (y - (1 - r j) • x)
  have hDist (j : ℕ) : ‖(1 - r j) • x - x‖ ≤ r j := by
    have h := (φ j).rOut_pos
    change 0 < r j at h
    conv_lhs => arg 1; arg 2; rw [← one_smul ℝ x]
    rw [← sub_smul, sub_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos h]
    exact mul_le_of_le_one_right h.le (mem_ball_zero_iff.mp hxB).le
  have hlim : Tendsto (fun j => ∫ y, k j y • I y ∂μ) atTop (𝓝 (I x)) := by
    apply tendsto_integral_smul_of_tendsto_average_norm_sub ((4 : ℝ) ^ Module.finrank ℝ (E n)) hAvg
    · exact Eventually.of_forall fun j => hI.integrableOn_isCompact (isCompact_closedBall x (2 * r j))
    · apply tendsto_const_nhds.congr
      intro j
      change 1 = ∫ y, (φ j).normed μ (y - (1 - r j) • x) ∂μ
      rw [integral_sub_right_eq_self, (φ j).integral_normed]
    · filter_upwards with j y hy
      have hy' : ‖y - (1 - r j) • x‖ < r j := by
        change y - (1 - r j) • x ∈ Function.support ((φ j).normed μ) at hy
        rw [(φ j).support_normed_eq, mem_ball_zero_iff] at hy
        exact hy
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le_norm_sub_add_norm_sub y ((1 - r j) • x) x).trans
        (by linarith [hDist j])
    · filter_upwards with j y
      have hpos : 0 < r j := (φ j).rOut_pos
      have hRatio := shrinkingBump_radius_ratio (E := E n) R hR j
      change r j = 2 * (φ j).rIn at hRatio
      rw [abs_of_nonneg ((φ j).nonneg_normed (y - (1 - r j) • x))]
      apply ((φ j).normed_le_div_measure_closedBall_rIn μ _).trans_eq
      rw [addHaar_real_closedBall_center μ x (2 * r j),
        addHaar_real_closedBall' _ _ (show 0 ≤ 2 * r j by linarith),
        addHaar_real_closedBall' _ _ (φ j).rIn_pos.le,
        show 2 * r j = 4 * (φ j).rIn by linarith, mul_pow, mul_assoc, div_mul_eq_div_div (a := (4 : ℝ) ^ _) (b := (4 : ℝ) ^ _),
        div_self (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0))]
  rw [show I x = f x from indicator_of_mem hxB f] at hlim
  apply hlim.congr
  intro j
  unfold translationPairing
  rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change k j y * (unitBall n).indicator f y = (unitBall n).indicator
      (fun z => f z * k j z) y
    by_cases hy : y ∈ unitBall n <;> simp [hy, mul_comm]

/-- Every iterated directional derivative of the inward-dilated
approximants converges almost everywhere to its weak representative. -/
theorem ae_tendsto_iteratedLineDerivative_dilatedDirichletTranslationPairing {n : ℕ}
    {f F : E n → ℝ} (ds : List (E n)) (hf : HasDirichletWeakDerivativesL2 f ds.length)
    (hF : MemLp F 2 ((volume0 n).restrict (unitBall n)))
    (he : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ), dirichletWeakDerivativeTest f ds ψ =
      ∫ x in unitBall n, ψ x * F x ∂volume0 n) (R : ℝ) (hR : 0 < R) :
    let φ : ℕ → ContDiffBump (0 : E n) := shrinkingBump R hR
    ∀ᵐ x ∂((volume0 n).restrict (unitBall n)), Tendsto
      (fun j => (ds.foldr (fun d C y => fderiv ℝ C y d)
        (fun y => translationPairing ((volume0 n).restrict (unitBall n)) f
          ((φ j).normed (volume0 n)) ((1 - (φ j).rOut) • y))) x) atTop (𝓝 (F x)) := by
  let ν := (volume0 n).restrict (unitBall n)
  let φ : ℕ → ContDiffBump (0 : E n) := shrinkingBump R hR
  let a (j : ℕ) : ℝ := 1 - (φ j).rOut
  have hR₀ := tendsto_shrinkingBump_rOut (E := E n) R hR
  have hA : Tendsto a atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hR₀
  have ha : ∀ᶠ j in atTop, 0 < a j := hA.eventually (lt_mem_nhds zero_lt_one)
  have hPow : Tendsto (fun j => a j ^ ds.length) atTop (𝓝 1) := by
    simpa only [one_pow] using hA.pow ds.length
  filter_upwards [ae_tendsto_dilatedDirichletTranslationPairing hF R hR,
    ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
    with x hx hxB
  have hT : Tendsto (fun j => a j ^ ds.length *
      translationPairing ν F ((φ j).normed (volume0 n)) (a j • x)) atTop (𝓝 (F x)) := by
    simpa only [one_mul] using hPow.mul hx
  apply hT.congr'
  filter_upwards [ha] with j hj
  let k := (φ j).normed (volume0 n)
  have hDiff : ContDiff ℝ ∞ (translationPairing ν f k) :=
    contDiff_translationPairing (hf.1.locallyIntegrable (by norm_num))
      (φ j).hasCompactSupport_normed (φ j).contDiff_normed
  have hInside (z : E n) (hz : z ∈ ball (0 : E n) (a j))
      (y : E n) (hy : y ∈ tsupport k) : y + z ∈ unitBall n := by
    have hz' := mem_ball_zero_iff.mp hz
    change y ∈ tsupport ((φ j).normed (volume0 n)) at hy
    rw [(φ j).tsupport_normed_eq, mem_closedBall, dist_zero_right] at hy
    apply mem_ball_zero_iff.mpr
    exact (norm_add_le _ _).trans_lt
      ((add_lt_add_of_le_of_lt hy hz').trans_le (by dsimp only [a]; linarith))
  have hAx : a j • x ∈ ball (0 : E n) (a j) := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hj]
    exact mul_lt_of_lt_one_right hj (mem_ball_zero_iff.mp hxB)
  change a j ^ ds.length * translationPairing ν F k (a j • x) =
    (ds.foldr (fun d C y => fderiv ℝ C y d) (fun y => translationPairing ν f k (a j • y))) x
  rw [iteratedLineDerivative_comp_real_smul hDiff]
  exact congrArg (fun c => a j ^ ds.length * c)
    (iteratedLineDerivative_dirichletTranslationPairing isOpen_ball (φ j).contDiff_normed
      (φ j).hasCompactSupport_normed hInside ds hf he hAx).symm

end KEBall
