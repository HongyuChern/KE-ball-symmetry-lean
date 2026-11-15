import KEBall.CegrellMollifier

/-!
# Approximation of an energy sublevel by an equicontinuous family
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass
open PshLines.Regularization.HolomorphicPullback

variable {n : ℕ}

private theorem integral_negativePotential_le (hn : 0 < n) {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) {M : ℝ≥0∞} (hM : energy hu ≤ M) (hMfin : M < ⊤)
    {ρ : Measure (ComplexModel n)} (hρ : ρ ≤ volume) (hρfin : ρ univ < ⊤)
    {R : ℝ} (hR : 1 ≤ R) :
    (∫ x, negativePotential u x ∂ρ) ≤ (ρ univ).toReal * R + volumeTailConstant n M / R := by
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hC : 0 ≤ volumeTailConstant n M := ENNReal.toReal_nonneg
  have hi := (integrable_negativePotential hn hu).mono_measure hρ
  have h := lintegral_negativePotential_le hn hu hM hMfin hρ hR
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (negativePotential_nonneg hn hu)),
    ← ENNReal.ofReal_toReal hρfin.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hR₀) (div_nonneg hC hR₀)] at h
  exact (ENNReal.ofReal_le_iff_le_toReal ENNReal.ofReal_ne_top).mp h |>.trans_eq
    (ENNReal.toReal_ofReal (by positivity))

private theorem translationPairing_bounds
    {f k : ComplexModel n → ℝ} (hf : Integrable f volume)
    (hkS : HasCompactSupport k) (hkC : Continuous k)
    {C K : ℝ≥0} (hC : (∫ x, |f x|) ≤ C) (hK : ∀ x, |k x| ≤ K)
    {L : ℝ≥0} (hL : LipschitzWith L k) :
    (∀ x, |translationPairing volume f k x| ≤ ((C * K : ℝ≥0) : ℝ)) ∧
      LipschitzWith (C * L) (translationPairing volume f k) := by
  constructor
  · intro x
    rw [translationPairing, ← Real.norm_eq_abs]
    calc
      _ ≤ ∫ z, |f z| * (K : ℝ) := by
        apply norm_integral_le_of_norm_le (hf.abs.mul_const (K : ℝ))
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _)
      _ = (∫ z, |f z|) * K := integral_mul_const _ _
      _ ≤ _ := by
        exact_mod_cast mul_le_mul_of_nonneg_right hC K.coe_nonneg
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, translationPairing, translationPairing,
      ← integral_sub (integrable_translationPairing hf.locallyIntegrable hkS hkC x)
        (integrable_translationPairing hf.locallyIntegrable hkS hkC y), ← Real.norm_eq_abs]
    calc
      _ ≤ ∫ z, |f z| * ((L : ℝ) * dist x y) := by
        apply norm_integral_le_of_norm_le (hf.abs.mul_const ((L : ℝ) * dist x y))
        filter_upwards with z
        simp only [Real.norm_eq_abs, ← mul_sub, abs_mul]
        have h := hL.dist_le_mul (z - x) (z - y)
        rw [dist_sub_left, Real.dist_eq] at h
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = (∫ z, |f z|) * ((L : ℝ) * dist x y) := integral_mul_const _ _
      _ ≤ _ := by
        rw [NNReal.coe_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right hC (mul_nonneg L.coe_nonneg dist_nonneg)

/-- At any requested accuracy, a family of bounded potentials in an
energy sublevel has uniform (L^1) approximants with common bounds on
their values, Lipschitz constants, and supports. -/
theorem exists_lipschitz_approximation_of_boundedEnergy (hn : 0 < n)
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsE0 (complexUnitBall n) (p j))
    {M : ℝ≥0∞} (hMfin : M < ⊤) (hM : ∀ j, boundedEnergy (hp j) ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : ℕ → ComplexModel n → ℝ) (A L : ℝ≥0),
      (∀ j x, |g j x| ≤ (A : ℝ)) ∧ (∀ j, LipschitzWith L (g j)) ∧
      (∀ j, tsupport (g j) ⊆ complexUnitBall n) ∧
      ∀ j, (∫ x, |negativePotential (fun x => (p j x : EReal)) x - g j x|) < ε := by
  let B := complexUnitBall n
  let μ := (volume : Measure (ComplexModel n)).restrict B
  let f (j : ℕ) := negativePotential (fun x => (p j x : EReal))
  have hf (j : ℕ) : Integrable (f j) volume := integrable_negativePotential hn (hp j).isE1
  have hnonneg (j : ℕ) (x : ComplexModel n) : 0 ≤ f j x :=
    negativePotential_nonneg hn (hp j).isE1 x
  have hzero (j : ℕ) (x : ComplexModel n) (hx : x ∉ B) : f j x = 0 :=
    indicator_of_notMem hx _
  have hμfin : μ univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt (isCompact_closure_complexUnitBall n).measure_lt_top
  let C₀ := volumeTailConstant n M
  have hC₀ : 0 ≤ C₀ := ENNReal.toReal_nonneg
  let C : ℝ≥0 := ⟨(μ univ).toReal + C₀, add_nonneg ENNReal.toReal_nonneg hC₀⟩
  have hL1 (j : ℕ) : (∫ x, f j x) ≤ C := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hzero j)]
    have hE := (energy_eq_boundedEnergy hn (hp j)).le.trans (hM j)
    change (∫ x, f j x ∂μ) ≤ (μ univ).toReal + C₀
    simpa only [mul_one, div_one] using integral_negativePotential_le hn (hp j).isE1 hE hMfin (ρ := μ)
        Measure.restrict_le_self hμfin (R := 1) le_rfl
  have hL1abs (j : ℕ) : (∫ x, |f j x|) ≤ C := by
    simpa only [abs_of_nonneg (hnonneg j _)] using hL1 j
  let R := 1 + C₀ / (ε / 4)
  have hR : 1 ≤ R := le_add_of_nonneg_right (div_nonneg hC₀ (by positivity))
  have hR₀ := zero_lt_one.trans_le hR
  have hTail : C₀ / R < ε / 4 := by
    rw [div_lt_iff₀ hR₀]
    dsimp [R]
    have he : ε / 4 * (C₀ / (ε / 4)) = C₀ := by field_simp
    rw [mul_add, mul_one, he]
    linarith
  let δ := ε / (4 * R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hBfin : volume (B : Set (ComplexModel n)) ≠ ⊤ := by
    rw [← Measure.restrict_apply_univ]
    exact hμfin.ne
  obtain ⟨K, hKB, hK, hVol⟩ := B.isOpen.measurableSet.exists_isCompact_sdiff_lt
    (μ := (volume : Measure (ComplexModel n))) hBfin (ENNReal.ofReal_pos.mpr hδ).ne'
  have hVolFin : volume ((B : Set (ComplexModel n)) \ K) < ⊤ := hVol.trans ENNReal.ofReal_lt_top
  have hVolReal : (volume ((B : Set (ComplexModel n)) \ K)).toReal < δ := by
    have h := ENNReal.toReal_lt_toReal hVolFin.ne (ENNReal.ofReal_ne_top (r := δ))
    exact (h.mpr hVol).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have htail (j : ℕ) : (∫ x in (B : Set (ComplexModel n)) \ K, f j x) < ε / 2 := by
    let ρ := (volume : Measure (ComplexModel n)).restrict ((B : Set (ComplexModel n)) \ K)
    have hρ : ρ univ < ⊤ := by simpa only [ρ, Measure.restrict_apply_univ] using hVolFin
    have hE := (energy_eq_boundedEnergy hn (hp j)).le.trans (hM j)
    have h := integral_negativePotential_le hn (hp j).isE1 hE hMfin
      (ρ := ρ) Measure.restrict_le_self hρ hR
    simp only [ρ, Measure.restrict_apply_univ, ← show C₀ = volumeTailConstant n M from rfl] at h
    have hprod := mul_lt_mul_of_pos_right hVolReal hR₀
    have hd : δ * R = ε / 4 := by
      dsimp [δ]
      field_simp
    linarith
  obtain ⟨χ, hχ, hχK⟩ := exists_testFunction_one_on hK hKB
  obtain ⟨Lχ, hLχ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport χ.contDiff (by simp)
  obtain ⟨r, hr, horder⟩ := exists_radialKernel_le_negativePotential χ
  have ht := tendsto_shrinkingBump_rOut (E := ComplexModel n) r hr
  have hRate : Tendsto (fun l => ((Lχ : ℝ) *
      (2 * (shrinkingBump (E := ComplexModel n) r hr l).rOut)) * C) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using ((ht.const_mul 2).const_mul (Lχ : ℝ)).mul_const (C : ℝ)
  obtain ⟨l, hl⟩ := (hRate.eventually_lt_const (half_pos hε)).exists
  let k := explicitRadialKernel (n := n) r hr l
  let s (j : ℕ) := translationPairing volume (f j) k
  let g (j : ℕ) (x : ComplexModel n) := χ x * s j x
  have hkS : HasCompactSupport k := explicitRadialKernel_hasCompactSupport r hr l
  have hkC : ContDiff ℝ ∞ k := explicitRadialKernel_contDiff r hr l
  obtain ⟨K₀, hK₀⟩ := hkS.exists_bound_of_continuous hkC.continuous
  let K₁ : ℝ≥0 := ⟨max 0 K₀, le_max_left _ _⟩
  have hkB (x : ComplexModel n) : |k x| ≤ (K₁ : ℝ) :=
    (Real.norm_eq_abs _ ▸ hK₀ x).trans (le_max_right _ _)
  obtain ⟨Lk, hLk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hkS hkC (by simp)
  have hs (j : ℕ) := translationPairing_bounds (hf j) hkS hkC.continuous (hL1abs j) hkB hLk
  let A := C * K₁
  let L := C * Lk + A * Lχ
  refine ⟨g, A, L, ?_, ?_, ?_, ?_⟩
  · intro j x
    change |χ x * s j x| ≤ (A : ℝ)
    rw [abs_mul, abs_of_nonneg (hχ x).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hχ x).2).trans ((hs j).1 x)
  · intro j
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have h₁ := (hs j).2.dist_le_mul x y
    have h₂ := hLχ.dist_le_mul x y
    rw [Real.dist_eq] at h₁ h₂
    calc
      _ = |χ x * (s j x - s j y) + s j y * (χ x - χ y)| := by
        change |χ x * s j x - χ y * s j y| = _
        congr 1
        ring
      _ ≤ |χ x| * |s j x - s j y| + |s j y| * |χ x - χ y| := by
        simpa only [abs_mul] using abs_add_le (χ x * (s j x - s j y)) (s j y * (χ x - χ y))
      _ ≤ (C * Lk : ℝ≥0) * dist x y + (A : ℝ) * (Lχ * dist x y) := by
        apply add_le_add
        · rw [abs_of_nonneg (hχ x).1]
          exact (mul_le_of_le_one_left (abs_nonneg _) (hχ x).2).trans h₁
        · exact mul_le_mul ((hs j).1 y) h₂ (abs_nonneg _) A.coe_nonneg
      _ = _ := by simp only [L, NNReal.coe_add, NNReal.coe_mul]; ring
  · intro j
    exact tsupport_mul_subset_left.trans χ.tsupport_subset
  · intro j
    have hsI : Integrable (s j) volume := by
      change Integrable (translationPairing volume (f j) k) volume
      rw [translationPairing_eq_convolution,
        show (fun x => k (-x)) = k from funext (explicitRadialKernel_neg r hr l)]
      exact (hf j).integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
        (integrable_of_integral_eq_one (explicitRadialKernel_integral_one r hr l))
    have hχf : Integrable (fun x => χ x * f j x) volume :=
      (hf j).bdd_mul χ.continuous.aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ x).1]
        exact (hχ x).2)
    have hχs : Integrable (fun x => χ x * s j x) volume :=
      hsI.bdd_mul χ.continuous.aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ x).1]
        exact (hχ x).2)
    have hterm₁ : Integrable (fun x => (1 - χ x) * f j x) volume := by
      simp only [sub_mul, one_mul]
      exact (hf j).sub hχf
    have hterm₂ : Integrable (fun x => χ x * |f j x - s j x|) volume := by
      apply Integrable.congr (hχf.sub hχs)
      filter_upwards with x
      change χ x * f j x - χ x * s j x = _
      by_cases hx : x ∈ tsupport χ
      · rw [abs_of_nonneg (sub_nonneg.mpr (horder (hp j) l x hx)), mul_sub]
      · rw [image_eq_zero_of_notMem_tsupport (f := χ) hx, zero_mul, zero_mul, zero_mul, sub_zero]
    have hsplit (x : ComplexModel n) :
        |f j x - g j x| = (1 - χ x) * f j x + χ x * |f j x - s j x| := by
      by_cases hx : x ∈ tsupport χ
      · have h := horder (hp j) l x hx
        change s j x ≤ f j x at h
        have hNon : 0 ≤ f j x - g j x := by
          apply sub_nonneg.mpr
          exact (mul_le_mul_of_nonneg_left h (hχ x).1).trans
            (mul_le_of_le_one_left (hnonneg j x) (hχ x).2)
        rw [abs_of_nonneg hNon, abs_of_nonneg (sub_nonneg.mpr h)]
        simp only [g]
        ring
      · rw [show χ x = 0 from image_eq_zero_of_notMem_tsupport (f := χ) hx]
        simp [g, image_eq_zero_of_notMem_tsupport (f := χ) hx, abs_of_nonneg (hnonneg j x)]
    have hfirst : (∫ x, (1 - χ x) * f j x) ≤ ∫ x in (B : Set (ComplexModel n)) \ K, f j x := by
      let D : Set (ComplexModel n) := B \ K
      have hD := B.isOpen.measurableSet.diff hK.isClosed.measurableSet
      rw [← integral_indicator hD]
      apply integral_mono hterm₁ ((hf j).indicator hD)
      intro x
      change (1 - χ x) * f j x ≤ D.indicator (f j) x
      by_cases hx : x ∈ D
      · rw [indicator_of_mem hx]
        exact mul_le_of_le_one_left (hnonneg j x) (sub_le_self _ (hχ x).1)
      · rw [indicator_of_notMem hx]
        by_cases hxB : x ∈ B
        · have hxK : x ∈ K := not_not.mp fun h => hx ⟨hxB, h⟩
          rw [hχK hxK, Pi.one_apply, sub_self, zero_mul]
        · rw [hzero j x hxB, mul_zero]
    have hsecond := integral_cutoff_mollification_error_le hn (hp j) χ hLχ hr l
      (fun x hx => horder (hp j) l x hx)
    have hProd := mul_le_mul_of_nonneg_left (hL1 j)
      (mul_nonneg Lχ.coe_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
        (shrinkingBump (E := ComplexModel n) r hr l).rOut_pos.le))
    change (∫ x, |f j x - g j x|) < ε
    simp_rw [hsplit]
    rw [integral_add hterm₁ hterm₂]
    exact add_lt_add (hfirst.trans_lt (htail j))
      ((hsecond.trans hProd).trans_lt hl) |>.trans_eq (add_halves ε)

end KEBall.Cegrell
