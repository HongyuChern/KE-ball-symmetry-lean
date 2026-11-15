import KEBall.BrezisMerleDiscDilation
import KEBall.BrezisMerleDiscWeakIntegrable
import KEBall.BrezisMerleDiscRadialKernel

/-!
# The disk exponential bound for a weak Laplacian measure
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Laplacian Topology

namespace KEBall.BrezisMerle

open PshLines (translationPairing)

/-- Mollification on a subdisk preserves the quadratic lower barrier
up to the distance from the mollifier support to the unit circle. -/
private theorem discMollifier_boundary_lower {u : E 1 → ℝ} (hu : Integrable u)
    {M : ℝ} (hM : 0 ≤ M)
    (hBound : ∀ x ∈ unitBall 1, -(M * (1 - ‖x‖ ^ 2)) ≤ u x)
    (j : ℕ) {r : ℝ} (hsr : 1 / ((j : ℝ) + 1) < r)
    (hr : r + 1 / ((j : ℝ) + 1) < 1) {z : E 1} (hz : z ∈ sphere 0 r) :
    -(M * (1 - (r - 1 / ((j : ℝ) + 1)) ^ 2)) ≤ translationPairing volume u (discMollifier j) z := by
  let s := 1 / ((j : ℝ) + 1)
  let δ := M * (1 - (r - s) ^ 2)
  let k := discMollifier j
  have hz' : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  have hCont := (discMollifier_contDiff j).continuous
  have hk := PshLines.integrable_translationPairing
    (locallyIntegrable_const (μ := volume) (1 : ℝ)) (discMollifier_hasCompactSupport j) hCont z
  have hkt : Integrable (fun x => k (x - z)) := by
    simpa only [one_mul, k] using hk
  have hInt := PshLines.integrable_translationPairing hu.locallyIntegrable
    (discMollifier_hasCompactSupport j) hCont z
  have hMass : (∫ x, k (x - z)) = 1 :=
    (integral_add_right_eq_self (μ := volume) k (-z)).trans (discMollifier_integral_one j)
  change -δ ≤ ∫ x, u x * k (x - z)
  calc
    -δ = ∫ x, (-δ) * k (x - z) := by rw [integral_const_mul, hMass, mul_one]
    _ ≤ _ := by
      apply integral_mono (hkt.const_mul _) hInt
      intro x
      by_cases hx : x - z ∈ tsupport k
      · have hd : ‖x - z‖ ≤ s :=
          mem_closedBall_zero_iff.mp (discMollifier_tsupport_subset j hx)
        have hx₁ : x ∈ unitBall 1 := by
          apply mem_ball_zero_iff.mpr
          have ht := norm_add_le (x - z) z
          rw [sub_add_cancel, hz'] at ht
          change r + s < 1 at hr
          linarith only [ht, hd, hr]
        have hx₂ : r - s ≤ ‖x‖ := by
          have he := norm_sub_norm_le z x
          rw [norm_sub_rev, hz'] at he
          linarith only [he, hd]
        have hSq := pow_le_pow_left₀ (sub_nonneg.mpr hsr.le) hx₂ 2
        have hLo : -δ ≤ -(M * (1 - ‖x‖ ^ 2)) :=
          neg_le_neg (mul_le_mul_of_nonneg_left (sub_le_sub_left hSq 1) hM)
        exact mul_le_mul_of_nonneg_right (hLo.trans (hBound x hx₁)) (discMollifier_nonneg j _)
      · change (-δ) * k (x - z) ≤ u x * k (x - z)
        rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

set_option maxHeartbeats 900000 in
/-- On each smaller disk the weak estimate has the boundary error given by
the quadratic barrier on that disk. -/
private theorem lintegral_exp_addBoundary_le_of_weakBallMass {u : E 1 → ℝ}
    (hu : Integrable u) {μ : Measure (E 1)} [IsFiniteMeasure μ]
    (hWeak : ∀ φ : E 1 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ unitBall 1 →
      (∫ x, u x * Δ φ x) = (4 * Real.pi) * ∫ x, φ x ∂μ)
    {M : ℝ} (hM : 0 ≤ M) (hBound : ∀ x ∈ unitBall 1, -(M * (1 - ‖x‖ ^ 2)) ≤ u x)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) (hMass : (μ univ).toReal ≤ t)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    (∫⁻ x in ball (0 : E 1) r, ENNReal.ofReal (Real.exp (-(u x + M * (1 - r ^ 2))))) ≤
      ENNReal.ofReal (r ^ 2 * (4 * Real.pi / (1 - t))) := by
  obtain ⟨J, hJ⟩ := exists_nat_one_div_lt (lt_min hr₀ (sub_pos.mpr hr₁))
  let s (j : ℕ) := 1 / (((j + J : ℕ) : ℝ) + 1)
  let δ (j : ℕ) := M * (1 - (r - s j) ^ 2)
  let v (j : ℕ) := translationPairing volume u (discMollifier (j + J))
  have hs₀ (j : ℕ) : s j < min r (1 - r) := by
    apply lt_of_le_of_lt _ hJ
    exact one_div_le_one_div_of_le (by positivity)
      (add_le_add (by exact_mod_cast Nat.le_add_left J j) le_rfl)
  have hsr (j : ℕ) : s j < r := (hs₀ j).trans_le (min_le_left _ _)
  have hrs (j : ℕ) : r + s j < 1 := by
    have h := (hs₀ j).trans_le (min_le_right _ _)
    linarith only [h]
  have hsLim : Tendsto s atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat J)
  have hδLim : Tendsto δ atTop (𝓝 (M * (1 - r ^ 2))) := by
    simpa only [δ, sub_zero] using
      (tendsto_const_nhds.sub ((tendsto_const_nhds.sub hsLim).pow 2)).const_mul M
  have hv (j : ℕ) : ContDiff ℝ ∞ (v j) :=
    PshLines.contDiff_translationPairing hu.locallyIntegrable
      (discMollifier_hasCompactSupport _) (discMollifier_contDiff _)
  have hvΔ (j : ℕ) (x : E 1) (hx : x ∈ ball (0 : E 1) r) :
      Δ (v j) x = (4 * Real.pi) * ∫ y, discMollifier (j + J) (y - x) ∂μ := by
    have hb := mem_ball_zero_iff.mp hx
    apply laplacian_translationPairing_eq_measure_integral hu.locallyIntegrable hWeak
      (discMollifier_contDiff _) (discMollifier_hasCompactSupport _) (discMollifier_tsupport_subset _)
    change ‖x‖ + s j < 1
    exact (add_lt_add_left hb (s j)).trans (hrs j)
  have hvMass (j : ℕ) : (∫ x in ball (0 : E 1) r, Δ (v j) x) / (4 * Real.pi) ≤ t := by
    rw [setIntegral_congr_fun measurableSet_ball (hvΔ j), integral_const_mul,
      mul_div_cancel_left₀ _ (by positivity : 4 * Real.pi ≠ 0)]
    exact (setIntegral_measure_translation_le_mass (discMollifier_contDiff _).continuous
      (discMollifier_hasCompactSupport _) (discMollifier_nonneg _) (discMollifier_integral_one _) μ r).trans hMass
  have hvNonneg (j : ℕ) (x : E 1) (hx : x ∈ ball (0 : E 1) r) : 0 ≤ Δ (v j) x := by
    rw [hvΔ j x hx]
    exact mul_nonneg (by positivity) (integral_nonneg fun y => discMollifier_nonneg _ _)
  have hvBoundary (j : ℕ) (x : E 1) (hx : x ∈ sphere 0 r) : -δ j ≤ v j x :=
    discMollifier_boundary_lower hu hM hBound (j + J) (hsr j) (hrs j) hx
  let F (j : ℕ) (x : E 1) := ENNReal.ofReal (Real.exp (-(v j x + δ j)))
  have hFm (j : ℕ) : Measurable (F j) :=
    (Real.measurable_exp.comp (((hv j).continuous.measurable.add_const _).neg)).ennreal_ofReal
  have hF (j : ℕ) : (∫⁻ x in ball (0 : E 1) r, F j x) ≤
      ENNReal.ofReal (r ^ 2 * (4 * Real.pi / (1 - t))) :=
    lintegral_exp_addBoundary_le_of_ballMass_le
      ((hv j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      hr₀ (hvBoundary j) (hvNonneg j) ht₀ ht₁ (hvMass j)
  have hConv : ∀ᵐ x ∂(volume : Measure (E 1)).restrict (ball 0 r),
      Tendsto (fun j => F j x) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(u x + M * (1 - r ^ 2)))))) := by
    filter_upwards [ae_restrict_of_ae (ae_tendsto_translationPairing_discMollifier hu)] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp
      (((hx.comp (tendsto_add_atTop_nat J)).add hδLim).neg))
  calc
    _ = ∫⁻ x in ball (0 : E 1) r, liminf (fun j => F j x) atTop := by
      apply lintegral_congr_ae
      exact hConv.mono fun _ h => h.liminf_eq.symm
    _ ≤ liminf (fun j => ∫⁻ x in ball (0 : E 1) r, F j x) atTop :=
      lintegral_liminf_le hFm
    _ ≤ _ := liminf_le_of_le (h := fun b hb => by
      obtain ⟨j, hj⟩ := hb.exists
      exact hj.trans (hF j))

set_option maxHeartbeats 900000 in
/-- Brezis–Merle on the unit disk for a weak Laplacian measure and a
potential with zero trace controlled by the quadratic barrier. -/
theorem lintegral_exp_le_of_weakDiscMass {u : E 1 → ℝ} {μ : Measure (E 1)}
    (hWeak : ∀ φ : E 1 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ unitBall 1 →
      Integrable (fun x => u x * Δ φ x) ∧ (∫ x, u x * Δ φ x) = (4 * Real.pi) * ∫ x, φ x ∂μ)
    (hZero : ∀ x ∉ unitBall 1, u x = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hBound : ∀ x ∈ unitBall 1, -(M * (1 - ‖x‖ ^ 2)) ≤ u x ∧ u x ≤ 0)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) (hMass : μ univ ≤ ENNReal.ofReal t) :
    (∫⁻ x in unitBall 1, ENNReal.ofReal (Real.exp (-u x))) ≤
      ENNReal.ofReal (4 * Real.pi / (1 - t)) := by
  let : IsFiniteMeasure μ := ⟨hMass.trans_lt ENNReal.ofReal_lt_top⟩
  have hu := integrable_zeroExtension_of_integrable_laplacian_tests
    (fun φ hφ hc hs => (hWeak φ hφ hc hs).1) hZero hBound hM
  have hm : (μ univ).toReal ≤ t := by
    simpa only [ENNReal.toReal_ofReal ht₀.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hMass
  let f (x : E 1) := ENNReal.ofReal (Real.exp (-u x))
  let C := 4 * Real.pi / (1 - t)
  have hRad (r : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1) :
      (∫⁻ x in ball (0 : E 1) r, f x) ≤
        ENNReal.ofReal (Real.exp (M * (1 - r ^ 2)) * (r ^ 2 * C)) := by
    let d := M * (1 - r ^ 2)
    have h := lintegral_exp_addBoundary_le_of_weakBallMass hu
      (fun φ hφ hc hs => (hWeak φ hφ hc hs).2) hM (fun x hx => (hBound x hx).1)
      ht₀ ht₁ hm hr₀ hr₁
    have he (x : E 1) : f x = ENNReal.ofReal (Real.exp d) *
        ENNReal.ofReal (Real.exp (-(u x + d))) := by
      change ENNReal.ofReal (Real.exp (-u x)) = _
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    calc
      _ = ENNReal.ofReal (Real.exp d) *
          ∫⁻ x in ball (0 : E 1) r, ENNReal.ofReal (Real.exp (-(u x + d))) := by
        simp_rw [he]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
        rw [ENNReal.ofReal_mul (Real.exp_nonneg d)]
        exact mul_le_mul_right h _
  let r (j : ℕ) := 1 - 1 / (((j + 1 : ℕ) : ℝ) + 1)
  let B (j : ℕ) : Set (E 1) := ball 0 (r j)
  have hr₀ (j : ℕ) : 0 < r j := by
    dsimp [r]
    apply sub_pos.mpr
    rw [div_lt_iff₀ (by positivity)]
    have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
    linarith only [hj]
  have hr₁ (j : ℕ) : r j < 1 := by dsimp [r]; exact sub_lt_self 1 (by positivity)
  have hrMono : Monotone r := by
    intro i j hij
    exact sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
      (add_le_add (by exact_mod_cast Nat.add_le_add_right hij 1) le_rfl)) 1
  have hMono : Monotone B := fun _ _ hij => ball_subset_ball (hrMono hij)
  have hR : Tendsto r atTop (𝓝 1) := by
    simpa only [r, sub_zero, Function.comp_apply] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
  have hUnion : (⋃ j, B j) = unitBall 1 := by
    apply Subset.antisymm (iUnion_subset fun j => ball_subset_ball (hr₁ j).le)
    intro x hx
    obtain ⟨j, hj⟩ := ((tendsto_order.1 hR).1 ‖x‖ (mem_ball_zero_iff.mp hx)).exists
    exact mem_iUnion.mpr ⟨j, mem_ball_zero_iff.mpr hj⟩
  have hf : AEMeasurable f volume :=
    (Real.measurable_exp.comp_aemeasurable hu.aemeasurable.neg).ennreal_ofReal
  have hI : (∫⁻ x in unitBall 1, f x) = ⨆ j, ∫⁻ x in B j, f x := by
    have he : (unitBall 1).indicator f = fun x => ⨆ j, (B j).indicator f x := by
      funext x
      by_cases hx : x ∈ unitBall 1
      · rw [indicator_of_mem hx]
        apply le_antisymm _ (iSup_le fun j => by
          by_cases h : x ∈ B j <;> simp [h])
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hUnion.symm ▸ hx)
        exact le_iSup_of_le j (by rw [indicator_of_mem hj])
      · rw [indicator_of_notMem hx]
        symm
        exact bot_unique (iSup_le fun j => by
          rw [indicator_of_notMem (fun h => hx (hUnion ▸ mem_iUnion.mpr ⟨j, h⟩))]; rfl)
    have hBm (j : ℕ) : MeasurableSet (B j) := measurableSet_ball
    have hBi : Monotone (fun j => (B j).indicator f) := by
      intro i j hij x
      exact indicator_le_indicator_of_subset (hMono hij) (fun _ => zero_le) x
    rw [← lintegral_indicator (show MeasurableSet (unitBall 1) from measurableSet_ball), he,
      lintegral_iSup' (fun j => hf.indicator (hBm j))
        (Eventually.of_forall fun x _ _ hij => hBi hij x)]
    have hInt (j : ℕ) :
        (∫⁻ x, (B j).indicator f x) = ∫⁻ x in B j, f x := lintegral_indicator (hBm j) f
    simp only [hInt]
  have hCLim : Tendsto
      (fun j => ENNReal.ofReal (Real.exp (M * (1 - r j ^ 2)) * (r j ^ 2 * C))) atTop
      (𝓝 (ENNReal.ofReal C)) := by
    have hSq := hR.pow 2
    have hD := ((tendsto_const_nhds (x := (1 : ℝ))).sub hSq).const_mul M
    have he := (Real.continuous_exp.tendsto _).comp hD
    simpa only [Function.comp_def, one_pow, sub_self, mul_zero, Real.exp_zero, one_mul] using
      (ENNReal.continuous_ofReal.tendsto _).comp (he.mul (hSq.mul_const C))
  change (∫⁻ x in unitBall 1, f x) ≤ ENNReal.ofReal C
  rw [hI]
  apply iSup_le
  intro j
  apply ge_of_tendsto hCLim
  filter_upwards [eventually_ge_atTop j] with k hjk
  have hK : (∫⁻ x in B k, f x) ≤ ENNReal.ofReal (Real.exp (M * (1 - r k ^ 2)) * (r k ^ 2 * C)) :=
    hRad (r k) (hr₀ k) (hr₁ k)
  exact (lintegral_mono_set (hMono hjk)).trans hK

end KEBall.BrezisMerle
