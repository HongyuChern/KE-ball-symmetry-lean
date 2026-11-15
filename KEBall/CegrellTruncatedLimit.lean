import KEBall.CegrellBallBoundary
import KEBall.CegrellTruncation

/-!
# Truncations of an extended-real finite-energy potential
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}

/-- A real-valued representative of the potential truncated below. -/
noncomputable def truncatePotential (u : ComplexModel n → EReal) (c : ℝ) :
    ComplexModel n → ℝ :=
  fun x => (max (u x) (c : EReal)).toReal

private theorem max_ne_top (h : ∀ x ∈ Ω, u x ≠ ⊤) (c : ℝ)
    (x : ComplexModel n) (hx : x ∈ Ω) :
    max (u x) (c : EReal) ≠ ⊤ :=
  ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (h x hx)) (EReal.coe_lt_top c))

private theorem max_ne_bot (u : ComplexModel n → EReal) (c : ℝ) (x : ComplexModel n) :
    max (u x) (c : EReal) ≠ ⊥ :=
  ne_of_gt ((EReal.bot_lt_coe c).trans_le (le_max_right _ _))

theorem coe_truncatePotential (hu : PlurisubharmonicOn u Ω) (c : ℝ)
    (x : ComplexModel n) (hx : x ∈ Ω) :
    (truncatePotential u c x : EReal) = max (u x) (c : EReal) :=
  EReal.coe_toReal (max_ne_top (fun y hy => (hu y hy).ne_top) c x hx) (max_ne_bot u c x)

theorem E1Approximation.le_term (p : E1Approximation Ω u) (j : ℕ)
    (x : ComplexModel n) (hx : x ∈ Ω) : u x ≤ (p.term j x : EReal) :=
  le_of_tendsto (p.pointwise x hx) ((eventually_ge_atTop j).mono fun _ hm =>
    EReal.coe_le_coe_iff.mpr (p.antitone x hx hm))

theorem truncatePotential_locallyBoundedPsh (hu : IsE1 Ω u) (c : ℝ) :
    IsLocallyBoundedPshOn Ω (truncatePotential u c) := by
  have hP : PlurisubharmonicOn (fun x => max (u x) (c : EReal)) Ω :=
    hu.1.max (fun x _ => plurisubharmonicAt_const (c : EReal) (by simp) x)
  have hQ : PlurisubharmonicOn (fun x => (truncatePotential u c x : EReal)) Ω := by
    intro x hx
    apply (hP x hx).congr
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact (coe_truncatePotential hu.1 c y hy).symm
  obtain ⟨p⟩ := hu.2
  obtain ⟨C, hC⟩ := (p.term_mem 0).bounded
  refine ⟨hQ, fun x hx => ⟨Ω, hx, le_rfl, max C |c|, fun y hy => ?_⟩⟩
  have hcy : c ≤ truncatePotential u c y := by
    rw [← EReal.coe_le_coe_iff, coe_truncatePotential hu.1 c y hy]
    exact le_max_right _ _
  have hyC : truncatePotential u c y ≤ max C |c| := by
    rw [← EReal.coe_le_coe_iff, coe_truncatePotential hu.1 c y hy]
    exact max_le ((p.le_term 0 y hy).trans (EReal.coe_le_coe_iff.mpr
      (((abs_le.mp (hC y hy)).2).trans (le_max_left _ _))))
      (EReal.coe_le_coe_iff.mpr ((le_abs_self c).trans (le_max_right _ _)))
  exact abs_le.mpr ⟨(neg_le_neg (le_max_right C |c|)).trans ((neg_abs_le c).trans hcy), hyC⟩

theorem max_coe_real (a b : ℝ) :
    ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
  · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.mpr h)]

theorem E1Approximation.tendsto_truncate (p : E1Approximation Ω u)
    (hu : PlurisubharmonicOn u Ω) (c : ℝ) (x : ComplexModel n) (hx : x ∈ Ω) :
    Tendsto (fun j => max (p.term j x) c) atTop (𝓝 (truncatePotential u c x)) := by
  have h := (EReal.tendsto_toReal (max_ne_top (fun y hy => (hu y hy).ne_top) c x hx)
    (max_ne_bot u c x)).comp ((p.pointwise x hx).max (tendsto_const_nhds (x := (c : EReal))))
  apply h.congr
  intro j
  change (max (p.term j x : EReal) (c : EReal)).toReal = _
  rw [← max_coe_real, EReal.toReal_coe]

theorem truncatePotential_nonpositive (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    {c : ℝ} (hc : c ≤ 0) (x : ComplexModel n) (hx : x ∈ complexUnitBall n) :
    truncatePotential u c x ≤ 0 := by
  rw [← EReal.coe_le_coe_iff, coe_truncatePotential hu.1 c x hx, EReal.coe_zero]
  exact max_le (hu.nonpositive_unitBall hn x hx) (by exact_mod_cast hc)

theorem isCompact_closure_complexUnitBall (n : ℕ) :
    IsCompact (closure (complexUnitBall n : Set (ComplexModel n))) := by
  change IsCompact (closure (ball (0 : ComplexModel n) 1))
  rw [closure_ball _ one_ne_zero]
  exact isCompact_closedBall _ _

theorem integrable_test_mul_topMeasure {v w : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn Ω v) (hw : IsLocallyBoundedPshOn Ω w) (χ : 𝓓(Ω, ℝ)) :
    Integrable (fun x => χ x * v x) (topMeasure hw) := by
  let μ := diagonalMeasure (mixedProduct_positive (k := n) (u := fun _ => w) (fun _ => hw)) id
  let : μ.Regular := diagonalMeasure_regular
    (mixedProduct_positive (k := n) (u := fun _ => w) (fun _ => hw)) id
  have he : MeasurableEmbedding (Subtype.val : Ω → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet
  have h : Integrable (fun x => χ x * v x) (μ.map (Subtype.val : Ω → ComplexModel n)) :=
    he.integrable_map_iff.mpr (integrable_test_mul_psh hv μ χ)
  change Integrable _ (ENNReal.ofReal ((Real.pi ^ n)⁻¹) • μ.map Subtype.val)
  exact (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).mpr h

theorem lintegral_test_energy_eq_ofReal {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn Ω v) (hneg : ∀ x ∈ Ω, v x ≤ 0)
    (χ : 𝓓(Ω, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    (∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂topMeasure hv) =
      ENNReal.ofReal (-(∫ x, χ x * v x ∂topMeasure hv)) := by
  have hInt := (integrable_test_mul_topMeasure hv hv χ).neg
  have ha : ∀ᵐ x ∂topMeasure hv, x ∈ Ω := by
    rw [ae_iff]
    exact topMeasure_compl hv
  have hnonneg : 0 ≤ᵐ[topMeasure hv] fun x => -(χ x * v x) := by
    filter_upwards [ha] with x hx
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hχ x) (hneg x hx))
  have he := (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
  simp only [Pi.neg_apply, mul_neg, integral_neg] at he ⊢
  exact he

/-- Smooth cutoffs on an exhaustion of the ball suffice to bound a
nonnegative weighted integral for a measure carried by the ball. -/
theorem lintegral_energy_le_of_cutoff_bound {v : ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} {M : ℝ≥0∞}
    (hμ : μ (Ω : Set (ComplexModel n))ᶜ = 0)
    (hbound : ∀ χ : 𝓓(Ω, ℝ), (∀ x, χ x ∈ Icc (0 : ℝ) 1) →
      (∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂μ) ≤ M) :
    (∫⁻ x, ENNReal.ofReal (-v x) ∂μ) ≤ M := by
  haveI : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let K (j : ℕ) := Subtype.val '' compactCovering Ω j
  have hK (j : ℕ) : IsCompact (K j) := (isCompact_compactCovering Ω j).image continuous_subtype_val
  have hKB (j : ℕ) : K j ⊆ Ω := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hKmono : Monotone K := fun _ _ hij => image_mono (compactCovering_subset Ω hij)
  have hKcover : (⋃ j, K j) = (Ω : Set (ComplexModel n)) := by
    apply Subset.antisymm (iUnion_subset hKB)
    intro x hx
    obtain ⟨j, hj⟩ := exists_mem_compactCovering (⟨x, hx⟩ : Ω)
    exact mem_iUnion.mpr ⟨j, ⟨⟨x, hx⟩, hj, rfl⟩⟩
  have hdom : μ.restrict (Ω : Set (ComplexModel n)) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rwa [ae_iff])
  change (∫⁻ x, ENNReal.ofReal (-v x) ∂μ) ≤ M
  rw [← hdom, ← hKcover, setLIntegral_iUnion_of_directed _ hKmono.directed_le]
  apply iSup_le
  intro j
  obtain ⟨χ, hχ, hχK⟩ := exists_testFunction_one_on (hK j) (hKB j)
  calc
    _ = ∫⁻ x in K j, ENNReal.ofReal (χ x * -v x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hK j).measurableSet] with x hx
      rw [hχK hx, Pi.one_apply, one_mul]
    _ ≤ ∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ M := hbound χ hχ

/-- The uniform bounded energy of any defining sequence controls the
energy of every bounded truncation of its limit. -/
theorem truncation_energy_le_iSup (hn : 0 < n) {u : ComplexModel n → EReal}
    (hu : IsE1 (complexUnitBall n) u) (p : E1Approximation (complexUnitBall n) u)
    {c : ℝ} (hc : c < 0) :
    (∫⁻ x, ENNReal.ofReal (-truncatePotential u c x) ∂
      topMeasure (truncatePotential_locallyBoundedPsh hu c)) ≤ ⨆ j, boundedEnergy (p.term_mem j) := by
  let B := complexUnitBall n
  let M := ⨆ j, boundedEnergy (p.term_mem j)
  let v := truncatePotential u c
  let vj (j : ℕ) (x : ComplexModel n) := max (p.term j x) c
  let hv := truncatePotential_locallyBoundedPsh hu c
  let hvjE (j : ℕ) := (p.term_mem j).truncate (isCompact_closure_complexUnitBall n) hc
  let hvj (j : ℕ) := (hvjE j).locallyBoundedPsh
  let μ := topMeasure hv
  have hbound (χ : 𝓓(B, ℝ)) (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) :
      (∫⁻ x, ENNReal.ofReal (χ x * -v x) ∂μ) ≤ M := by
    have ha (x : ComplexModel n) (hx : x ∈ B) : Antitone (fun j => vj j x) :=
      fun _ _ h => max_le_max_right _ (p.antitone x hx h)
    have hl (x : ComplexModel n) (hx : x ∈ B) : Tendsto (fun j => vj j x) atTop (𝓝 (v x)) :=
      p.tendsto_truncate hu.1 c x hx
    have hlim := (tendsto_weightedTopMeasure_of_decreasing hv hv hvj hvj ha ha hl hl χ).neg
    have hfin : M ≠ ⊤ := p.energyBound.ne
    have hle (j : ℕ) : -(∫ x, χ x * vj j x ∂topMeasure (hvj j)) ≤ M.toReal := by
      have he := boundedEnergy_truncate_le (isCompact_closure_complexUnitBall n) (p.term_mem j) hc
      have htest : (∫⁻ x, ENNReal.ofReal (χ x * -vj j x) ∂topMeasure (hvj j)) ≤ boundedEnergy (hvjE j) := by
        apply lintegral_mono_ae
        have hdom : ∀ᵐ x ∂topMeasure (hvj j), x ∈ B := by
          rw [ae_iff]
          exact topMeasure_compl (hvj j)
        filter_upwards [hdom] with x hx
        exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left
          (neg_nonneg.mpr ((hvjE j).nonpositive_unitBall hn x hx)) (hχ x).2)
      rw [lintegral_test_energy_eq_ofReal (hvj j) ((hvjE j).nonpositive_unitBall hn)
        χ (fun x => (hχ x).1)] at htest
      exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp
        (htest.trans (he.trans (le_iSup (fun j => boundedEnergy (p.term_mem j)) j)))
    have hleLim := le_of_tendsto hlim (Eventually.of_forall hle)
    rw [lintegral_test_energy_eq_ofReal hv (truncatePotential_nonpositive hn hu hc.le) χ
      (fun x => (hχ x).1)]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mpr hleLim
  exact lintegral_energy_le_of_cutoff_bound (topMeasure_compl hv) hbound

end KEBall.Cegrell
