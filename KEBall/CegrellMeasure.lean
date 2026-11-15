import KEBall.CegrellIncreasingMeasures
import KEBall.CegrellTruncatedLimit

/-!
# The Monge–Ampère measure of a finite-energy potential on the ball
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {u : ComplexModel n → EReal}

private def truncationLevel (k : ℕ) : ℝ := -((k : ℝ) + 1)

private theorem truncationLevel_neg (k : ℕ) : truncationLevel k < 0 := by
  unfold truncationLevel
  exact neg_lt_zero.mpr (by positivity)

private theorem truncationLevel_antitone : Antitone truncationLevel := by
  intro a b hab
  unfold truncationLevel
  exact neg_le_neg (by exact_mod_cast Nat.add_le_add_right hab 1)

private def superlevel (u : ComplexModel n → EReal) (k : ℕ) : Set (ComplexModel n) :=
  {x ∈ complexUnitBall n | (truncationLevel k : EReal) < u x}

private theorem superlevel_mono (u : ComplexModel n → EReal) : Monotone (superlevel u) := by
  intro k l hkl x hx
  exact ⟨hx.1, (EReal.coe_le_coe_iff.mpr (truncationLevel_antitone hkl)).trans_lt hx.2⟩

private theorem superlevel_eq_of_le (hu : IsE1 (complexUnitBall n) u) {k l : ℕ} (hkl : k ≤ l) :
    {x ∈ complexUnitBall n | truncationLevel k < truncatePotential u (truncationLevel l) x} =
      superlevel u k := by
  ext x
  refine and_congr_right fun hx => ?_
  rw [← EReal.coe_lt_coe_iff, coe_truncatePotential hu.1 _ x hx, lt_max_iff]
  exact or_iff_left (not_lt_of_ge (EReal.coe_le_coe_iff.mpr (truncationLevel_antitone hkl)))

private theorem measurableSet_superlevel (hu : IsE1 (complexUnitBall n) u) (k : ℕ) :
    MeasurableSet (superlevel u k) := by
  rw [← superlevel_eq_of_le hu (le_refl k)]
  exact measurableSet_gt_on_domain (truncatePotential_locallyBoundedPsh hu (truncationLevel k)) _

private noncomputable def truncatedMeasure (hu : IsE1 (complexUnitBall n) u) (k : ℕ) :
    Measure (ComplexModel n) :=
  topMeasure (truncatePotential_locallyBoundedPsh hu (truncationLevel k))

private theorem truncatedMeasure_restrict_eq (hu : IsE1 (complexUnitBall n) u) {k l : ℕ} (hkl : k ≤ l) :
    (truncatedMeasure hu l).restrict (superlevel u k) =
      (truncatedMeasure hu k).restrict (superlevel u k) := by
  let hl := truncatePotential_locallyBoundedPsh hu (truncationLevel l)
  let hk := truncatePotential_locallyBoundedPsh hu (truncationLevel k)
  have hEq : EqOn (fun x => max (truncatePotential u (truncationLevel l) x) (truncationLevel k))
      (truncatePotential u (truncationLevel k)) (complexUnitBall n : Set (ComplexModel n)) := by
    intro x hx
    apply EReal.coe_injective
    rw [max_coe_real, coe_truncatePotential hu.1 _ x hx, coe_truncatePotential hu.1 _ x hx,
      max_assoc, max_eq_right (EReal.coe_le_coe_iff.mpr (truncationLevel_antitone hkl))]
  have h := topMeasure_restrict_gt_truncation hl (truncationLevel k)
  change (truncatedMeasure hu l).restrict
      {x ∈ complexUnitBall n | truncationLevel k < truncatePotential u (truncationLevel l) x} = _ at h
  rw [superlevel_eq_of_le hu hkl, topMeasure_congr (locallyBoundedPsh_max_const hl _) hk hEq] at h
  exact h

private noncomputable def restrictedTruncatedMeasure (hu : IsE1 (complexUnitBall n) u) (k : ℕ) :
    Measure (ComplexModel n) :=
  (truncatedMeasure hu k).restrict (superlevel u k)

private theorem restrictedTruncatedMeasure_mono (hu : IsE1 (complexUnitBall n) u) :
    Monotone (restrictedTruncatedMeasure hu) := by
  intro k l hkl
  unfold restrictedTruncatedMeasure
  rw [← truncatedMeasure_restrict_eq hu hkl]
  exact Measure.restrict_mono (superlevel_mono u hkl) le_rfl

/-- The finite-energy Monge–Ampère measure, constructed from the
compatible bounded truncations of the potential. -/
noncomputable def mongeAmpereMeasure (hu : IsE1 (complexUnitBall n) u) :
    Measure (ComplexModel n) :=
  increasingMeasureLimit (restrictedTruncatedMeasure hu) (restrictedTruncatedMeasure_mono hu)

private theorem mongeAmpereMeasure_restrict_superlevel (hu : IsE1 (complexUnitBall n) u) (k : ℕ) :
    (mongeAmpereMeasure hu).restrict (superlevel u k) = restrictedTruncatedMeasure hu k := by
  apply Measure.ext
  intro A hA
  let G := superlevel u k
  have hG := measurableSet_superlevel hu k
  rw [Measure.restrict_apply hA, mongeAmpereMeasure,
    increasingMeasureLimit_apply _ _ (hA.inter hG)]
  have hfixed {l : ℕ} (hkl : k ≤ l) :
      restrictedTruncatedMeasure hu l (A ∩ G) = restrictedTruncatedMeasure hu k A := by
    rw [restrictedTruncatedMeasure, Measure.restrict_apply (hA.inter hG),
      inter_assoc, inter_eq_left.mpr (superlevel_mono u hkl),
      ← Measure.restrict_apply hA, truncatedMeasure_restrict_eq hu hkl]
    rfl
  apply le_antisymm
  · apply iSup_le
    intro l
    exact ((restrictedTruncatedMeasure_mono hu (le_max_left l k)) (A ∩ G)).trans_eq
      (hfixed (le_max_right l k))
  · exact (hfixed (le_refl k)).symm.le.trans (le_iSup (fun l => restrictedTruncatedMeasure hu l (A ∩ G)) k)

theorem mongeAmpereMeasure_compl (hu : IsE1 (complexUnitBall n) u) :
    mongeAmpereMeasure hu (complexUnitBall n : Set (ComplexModel n))ᶜ = 0 := by
  rw [mongeAmpereMeasure, increasingMeasureLimit_apply _ _ (complexUnitBall n).isOpen.measurableSet.compl]
  apply le_antisymm (iSup_le ?_) bot_le
  intro k
  rw [restrictedTruncatedMeasure, Measure.restrict_apply (complexUnitBall n).isOpen.measurableSet.compl]
  have hempty : (complexUnitBall n : Set (ComplexModel n))ᶜ ∩ superlevel u k = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun _ hx => hx.1 hx.2.1
  rw [hempty, measure_empty]
  exact bot_le

/-- The nonnegative energy integral of a finite-energy potential. -/
noncomputable def energy (hu : IsE1 (complexUnitBall n) u) : ℝ≥0∞ :=
  ∫⁻ x, (-u x).toENNReal ∂mongeAmpereMeasure hu

theorem energy_le_iSup (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u) :
    energy hu ≤ ⨆ j, boundedEnergy (p.term_mem j) := by
  rw [energy, mongeAmpereMeasure, lintegral_increasingMeasureLimit]
  apply iSup_le
  intro k
  let c := truncationLevel k
  let g := truncatePotential u c
  have hEq (x : ComplexModel n) (hx : x ∈ superlevel u k) :
      (-u x).toENNReal = ENNReal.ofReal (-g x) := by
    have h := coe_truncatePotential hu.1 c x hx.1
    rw [max_eq_left hx.2.le] at h
    rw [← h, ← EReal.coe_neg]
    rfl
  calc
    _ = ∫⁻ x, ENNReal.ofReal (-g x) ∂restrictedTruncatedMeasure hu k := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_superlevel hu k)] with x hx
      exact hEq x hx
    _ ≤ ∫⁻ x, ENNReal.ofReal (-g x) ∂truncatedMeasure hu k :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ _ := truncation_energy_le_iSup hn hu p (truncationLevel_neg k)

theorem energy_lt_top (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u) :
    energy hu < ⊤ := by
  obtain ⟨p⟩ := hu.2
  exact (energy_le_iSup hn hu p).trans_lt p.energyBound

theorem topMeasure_le_div_energy_of_sublevel {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn (complexUnitBall n) v)
    {A : Set (ComplexModel n)} (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r)
    (hLevel : ∀ x ∈ A, x ∈ complexUnitBall n → v x ≤ -r)
    {M : ℝ≥0∞} (hM : (∫⁻ x, ENNReal.ofReal (-v x) ∂topMeasure hv) ≤ M) :
    topMeasure hv A ≤ M / ENNReal.ofReal r := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hr)))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm, ← Measure.restrict_apply_univ (μ := topMeasure hv) A, ← lintegral_const]
  refine (lintegral_mono_ae ?_).trans ((lintegral_mono' Measure.restrict_le_self le_rfl).trans hM)
  have hdom : ∀ᵐ x ∂topMeasure hv, x ∈ complexUnitBall n := by
    rw [ae_iff]
    exact topMeasure_compl hv
  filter_upwards [ae_restrict_mem hA, ae_mono Measure.restrict_le_self hdom] with x hx hxB
  exact ENNReal.ofReal_le_ofReal (by linarith [hLevel x hx hxB])

private theorem truncatedMeasure_tail_le (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u) {k l : ℕ} (hkl : k ≤ l) :
    truncatedMeasure hu l (superlevel u k)ᶜ ≤
      (⨆ j, boundedEnergy (p.term_mem j)) / ENNReal.ofReal ((k : ℝ) + 1) := by
  apply topMeasure_le_div_energy_of_sublevel (truncatePotential_locallyBoundedPsh hu (truncationLevel l))
    (measurableSet_superlevel hu k).compl (by positivity) _
    (truncation_energy_le_iSup hn hu p (truncationLevel_neg l))
  intro x hx hxB
  have hcut : u x ≤ (truncationLevel k : EReal) := le_of_not_gt fun h => hx ⟨hxB, h⟩
  change truncatePotential u (truncationLevel l) x ≤ truncationLevel k
  rw [← EReal.coe_le_coe_iff, coe_truncatePotential hu.1 _ x hxB]
  exact max_le hcut (EReal.coe_le_coe_iff.mpr (truncationLevel_antitone hkl))

private theorem mongeAmpereMeasure_tail_le (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u) (k : ℕ) :
    mongeAmpereMeasure hu (superlevel u k)ᶜ ≤
      (⨆ j, boundedEnergy (p.term_mem j)) / ENNReal.ofReal ((k : ℝ) + 1) := by
  rw [mongeAmpereMeasure, increasingMeasureLimit_apply _ _ (measurableSet_superlevel hu k).compl]
  apply iSup_le
  intro l
  calc
    _ ≤ restrictedTruncatedMeasure hu (max l k) (superlevel u k)ᶜ :=
      restrictedTruncatedMeasure_mono hu (le_max_left _ _) _
    _ ≤ truncatedMeasure hu (max l k) (superlevel u k)ᶜ := Measure.restrict_le_self _
    _ ≤ _ := truncatedMeasure_tail_le hn hu p (le_max_right l k)

/-- The finite-energy measure is finite on compact subsets of the ball. -/
theorem mongeAmpereMeasure_finite_on_compact (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKB : K ⊆ complexUnitBall n) :
    mongeAmpereMeasure hu K < ⊤ := by
  obtain ⟨p⟩ := hu.2
  let G := superlevel u 0
  let μ := mongeAmpereMeasure hu
  let ν := truncatedMeasure hu 0
  have hG : MeasurableSet G := measurableSet_superlevel hu 0
  have hKG : μ (K ∩ G) ≤ ν K := by
    rw [← Measure.restrict_apply hK.measurableSet, mongeAmpereMeasure_restrict_superlevel hu 0]
    exact Measure.restrict_le_self _
  have hTail : μ (K \ G) ≤ (⨆ j, boundedEnergy (p.term_mem j)) / ENNReal.ofReal (0 + 1) := by
    refine (measure_mono (fun _ hx => hx.2 : K \ G ⊆ Gᶜ)).trans ?_
    change mongeAmpereMeasure hu (superlevel u 0)ᶜ ≤ _
    simpa only [Nat.cast_zero] using mongeAmpereMeasure_tail_le hn hu p 0
  rw [← measure_inter_add_sdiff (μ := μ) K hG]
  exact ENNReal.add_lt_top.mpr
    ⟨hKG.trans_lt (topMeasure_finite_on_compact _ hK hKB),
      hTail.trans_lt (ENNReal.div_lt_top p.energyBound.ne (by norm_num))⟩

private theorem integrable_of_compact_test {f : ComplexModel n → ℝ}
    (hfc : HasCompactSupport f) {μ : Measure (ComplexModel n)}
    (hf : AEMeasurable f μ) (hμ : μ (tsupport f) < ⊤)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ := by
  have hi : IntegrableOn f (tsupport f) μ :=
    Measure.integrableOn_of_bounded hμ.ne hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
  have h := hi.integrable_indicator hfc.isClosed.measurableSet
  rwa [indicator_eq_self.mpr (subset_tsupport f)] at h

private theorem abs_integral_sub_le_of_restrict_eq {f : ComplexModel n → ℝ}
    {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    {μ ν : Measure (ComplexModel n)} (hμ : Integrable f μ) (hν : Integrable f ν)
    {G : Set (ComplexModel n)} (hG : MeasurableSet G) (hEq : μ.restrict G = ν.restrict G)
    {R : ℝ≥0∞} (hR : R < ⊤) (hμR : μ Gᶜ ≤ R) (hνR : ν Gᶜ ≤ R) :
    dist (∫ x, f x ∂μ) (∫ x, f x ∂ν) ≤ 2 * C * R.toReal := by
  have hnorm (ρ : Measure (ComplexModel n)) (hρ : Integrable f ρ) (hρR : ρ Gᶜ ≤ R) :
      |∫ x in Gᶜ, f x ∂ρ| ≤ C * R.toReal := by
    have hFin : IsFiniteMeasure (ρ.restrict Gᶜ) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hρR.trans_lt hR⟩
    calc
      _ ≤ ∫ x in Gᶜ, |f x| ∂ρ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := ρ.restrict Gᶜ) f
      _ ≤ ∫ _ in Gᶜ, C ∂ρ := integral_mono hρ.restrict.abs (integrable_const C) hC
      _ = C * (ρ Gᶜ).toReal := by
        rw [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hR.ne hρR) hC₀
  rw [Real.dist_eq, ← integral_add_compl hG hμ, ← integral_add_compl hG hν, hEq,
    add_sub_add_left_eq_sub]
  have h := abs_add_le (∫ x in Gᶜ, f x ∂μ) (-(∫ x in Gᶜ, f x ∂ν))
  rw [← sub_eq_add_neg, abs_neg] at h
  exact h.trans (by linarith [hnorm μ hμ hμR, hnorm ν hν hνR])

private theorem truncation_error_bounded (p : E1Approximation (complexUnitBall n) u)
    {f : ComplexModel n → ℝ}
    (hf : ∀ μ : Measure (ComplexModel n), μ (complexUnitBall n : Set (ComplexModel n))ᶜ = 0 →
      AEMeasurable f μ)
    (hfc : HasCompactSupport f) (hfB : tsupport f ⊆ complexUnitBall n) {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (j k : ℕ) :
    dist (∫ x, f x ∂topMeasure (p.term_mem j).locallyBoundedPsh)
      (∫ x, f x ∂topMeasure (locallyBoundedPsh_max_const (p.term_mem j).locallyBoundedPsh
        (truncationLevel k))) ≤
      2 * C * ((⨆ j, boundedEnergy (p.term_mem j)).toReal / ((k : ℝ) + 1)) := by
  let hu := p.term_mem j
  let c := truncationLevel k
  let hv := hu.truncate (isCompact_closure_complexUnitBall n) (truncationLevel_neg k)
  let μ := topMeasure hu.locallyBoundedPsh
  let ν := topMeasure hv.locallyBoundedPsh
  let G := {x ∈ complexUnitBall n | c < p.term j x}
  let M := ⨆ j, boundedEnergy (p.term_mem j)
  let R := M / ENNReal.ofReal ((k : ℝ) + 1)
  have hG := measurableSet_gt_on_domain hu.locallyBoundedPsh c
  have hEq : μ.restrict G = ν.restrict G := topMeasure_restrict_gt_truncation hu.locallyBoundedPsh c
  have hR : R < ⊤ := ENNReal.div_lt_top p.energyBound.ne (by positivity)
  have hLevel (x : ComplexModel n) (hx : x ∈ Gᶜ) (hxB : x ∈ complexUnitBall n) :
      p.term j x ≤ c := le_of_not_gt fun h => hx ⟨hxB, h⟩
  have hμR : μ Gᶜ ≤ R :=
    topMeasure_le_div_energy_of_sublevel hu.locallyBoundedPsh hG.compl (by positivity) hLevel
      (le_iSup (fun j => boundedEnergy (p.term_mem j)) j)
  have hνR : ν Gᶜ ≤ R :=
    topMeasure_le_div_energy_of_sublevel hv.locallyBoundedPsh hG.compl (by positivity)
      (fun x hx hxB => max_le (hLevel x hx hxB) le_rfl)
      ((boundedEnergy_truncate_le (isCompact_closure_complexUnitBall n) hu (truncationLevel_neg k)).trans
        (le_iSup (fun j => boundedEnergy (p.term_mem j)) j))
  have hμ := integrable_of_compact_test hfc (hf μ (topMeasure_compl hu.locallyBoundedPsh))
    (topMeasure_finite_on_compact hu.locallyBoundedPsh hfc hfB) hC
  have hν := integrable_of_compact_test hfc (hf ν (topMeasure_compl hv.locallyBoundedPsh))
    (topMeasure_finite_on_compact hv.locallyBoundedPsh hfc hfB) hC
  have h := abs_integral_sub_le_of_restrict_eq hC₀ hC hμ hν hG hEq hR hμR hνR
  have hreal : R.toReal = M.toReal / ((k : ℝ) + 1) := by
    simp only [R, ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity : 0 ≤ (k : ℝ) + 1)]
  rw [hreal] at h
  exact h

private theorem truncation_error_limit (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u)
    {f : ComplexModel n → ℝ}
    (hf : ∀ μ : Measure (ComplexModel n), μ (complexUnitBall n : Set (ComplexModel n))ᶜ = 0 →
      AEMeasurable f μ)
    (hfc : HasCompactSupport f) (hfB : tsupport f ⊆ complexUnitBall n) {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (k : ℕ) :
    dist (∫ x, f x ∂truncatedMeasure hu k) (∫ x, f x ∂mongeAmpereMeasure hu) ≤
      2 * C * ((⨆ j, boundedEnergy (p.term_mem j)).toReal / ((k : ℝ) + 1)) := by
  let G := superlevel u k
  let M := ⨆ j, boundedEnergy (p.term_mem j)
  let R := M / ENNReal.ofReal ((k : ℝ) + 1)
  have hR : R < ⊤ := ENNReal.div_lt_top p.energyBound.ne (by positivity)
  have ht := truncatePotential_locallyBoundedPsh hu (truncationLevel k)
  have hμ := integrable_of_compact_test hfc (hf (truncatedMeasure hu k) (topMeasure_compl ht))
    (topMeasure_finite_on_compact ht hfc hfB) hC
  have hν := integrable_of_compact_test hfc
    (hf (mongeAmpereMeasure hu) (mongeAmpereMeasure_compl hu))
    (mongeAmpereMeasure_finite_on_compact hn hu hfc hfB) hC
  have h := abs_integral_sub_le_of_restrict_eq hC₀ hC hμ hν (measurableSet_superlevel hu k)
    (mongeAmpereMeasure_restrict_superlevel hu k).symm hR
    (truncatedMeasure_tail_le hn hu p (le_refl k)) (mongeAmpereMeasure_tail_le hn hu p k)
  have hreal : R.toReal = M.toReal / ((k : ℝ) + 1) := by
    simp only [R, ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity : 0 ≤ (k : ℝ) + 1)]
  rw [hreal] at h
  exact h

private theorem tendsto_mongeAmpereMeasure_of_truncated_tests (hn : 0 < n)
    (hu : IsE1 (complexUnitBall n) u) (p : E1Approximation (complexUnitBall n) u)
    {f : ComplexModel n → ℝ}
    (hf : ∀ μ : Measure (ComplexModel n), μ (complexUnitBall n : Set (ComplexModel n))ᶜ = 0 →
      AEMeasurable f μ)
    (hfc : HasCompactSupport f) (hfB : tsupport f ⊆ complexUnitBall n)
    {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (htrunc : ∀ k : ℕ, Tendsto (fun j => ∫ x, f x ∂topMeasure
      (locallyBoundedPsh_max_const (p.term_mem j).locallyBoundedPsh (truncationLevel k))) atTop
      (𝓝 (∫ x, f x ∂truncatedMeasure hu k))) :
    Tendsto (fun j => ∫ x, f x ∂topMeasure (p.term_mem j).locallyBoundedPsh) atTop
      (𝓝 (∫ x, f x ∂mongeAmpereMeasure hu)) := by
  let M := ⨆ j, boundedEnergy (p.term_mem j)
  let error (k : ℕ) := 2 * C * (M.toReal / ((k : ℝ) + 1))
  have hError : Tendsto error atTop (𝓝 0) := by
    have h := (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop M.toReal
    simpa only [error, mul_zero] using h.const_mul (2 * C)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := (hError.eventually_lt_const (show 0 < ε / 3 by positivity)).exists
  let hq := fun j => locallyBoundedPsh_max_const (p.term_mem j).locallyBoundedPsh (truncationLevel k)
  have hWeak := htrunc k
  filter_upwards [Metric.tendsto_nhds.mp hWeak (ε / 3) (by positivity)] with j hj
  have hLeft : dist (∫ x, f x ∂topMeasure (p.term_mem j).locallyBoundedPsh)
      (∫ x, f x ∂topMeasure (hq j)) ≤ error k :=
    truncation_error_bounded p hf hfc hfB hC₀ hC j k
  have hRight : dist (∫ x, f x ∂truncatedMeasure hu k)
      (∫ x, f x ∂mongeAmpereMeasure hu) ≤ error k :=
    truncation_error_limit hn hu p hf hfc hfB hC₀ hC k
  let a := ∫ x, f x ∂topMeasure (p.term_mem j).locallyBoundedPsh
  let b := ∫ x, f x ∂topMeasure (hq j)
  let c := ∫ x, f x ∂truncatedMeasure hu k
  let d := ∫ x, f x ∂mongeAmpereMeasure hu
  change dist a d < ε
  change dist b c < ε / 3 at hj
  exact (dist_triangle4 a b c d).trans_lt (by linarith)

/-- Every defining sequence converges on compactly supported continuous
tests to the same finite-energy Monge–Ampère measure. -/
theorem tendsto_mongeAmpereMeasure (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u)
    {f : ComplexModel n → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfB : tsupport f ⊆ complexUnitBall n) :
    Tendsto (fun j => ∫ x, f x ∂topMeasure (p.term_mem j).locallyBoundedPsh) atTop
      (𝓝 (∫ x, f x ∂mongeAmpereMeasure hu)) := by
  obtain ⟨C₀, hC₀⟩ := (hfc.image_of_continuousOn hf.abs.continuousOn).bddAbove
  let C := max 0 C₀
  have hC (x : ComplexModel n) : |f x| ≤ C := by
    by_cases hx : x ∈ tsupport f
    · exact (hC₀ ⟨x, hx, rfl⟩).trans (le_max_right _ _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, abs_zero, C, le_max_left]
  apply tendsto_mongeAmpereMeasure_of_truncated_tests hn hu p
    (fun _ _ => hf.aemeasurable) hfc hfB (le_max_left _ _) hC
  intro k
  let q (j : ℕ) (x : ComplexModel n) := max (p.term j x) (truncationLevel k)
  let hq := fun j => locallyBoundedPsh_max_const (p.term_mem j).locallyBoundedPsh (truncationLevel k)
  let v := truncatePotential u (truncationLevel k)
  have hAnti (x : ComplexModel n) (hx : x ∈ complexUnitBall n) : Antitone (fun j => q j x) :=
    fun _ _ h => max_le_max_right _ (p.antitone x hx h)
  have hLim (x : ComplexModel n) (hx : x ∈ complexUnitBall n) :
      Tendsto (fun j => q j x) atTop (𝓝 (v x)) :=
    p.tendsto_truncate hu.1 (truncationLevel k) x hx
  exact tendsto_topMeasure_of_decreasing
    (truncatePotential_locallyBoundedPsh hu (truncationLevel k)) hq hAnti hLim f hf hfc hfB

private theorem weightedTest_aemeasurable {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn (complexUnitBall n) v) (χ : 𝓓(complexUnitBall n, ℝ))
    (μ : Measure (ComplexModel n)) (hμ : μ (complexUnitBall n : Set (ComplexModel n))ᶜ = 0) :
    AEMeasurable (fun x => χ x * v x) μ := by
  have hdom : ∀ᵐ x ∂μ, x ∈ complexUnitBall n := by rwa [ae_iff]
  have hvmeas := aemeasurable_restrict_of_measurable_subtype
    (complexUnitBall n).isOpen.measurableSet (measurable_subtype_of_locallyBoundedPsh hv)
    (μ := μ)
  rw [Measure.restrict_eq_self_of_ae_mem hdom] at hvmeas
  exact χ.continuous.aemeasurable.mul hvmeas

private theorem weightedTest_bdd {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn (complexUnitBall n) v) (χ : 𝓓(complexUnitBall n, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |χ x * v x| ≤ C := by
  obtain ⟨D, hD⟩ := (χ.hasCompactSupport.image_of_continuousOn χ.continuous.abs.continuousOn).bddAbove
  obtain ⟨B, hB₀, hB⟩ := hv.exists_compact_abs_bound χ.hasCompactSupport χ.tsupport_subset
  let C := max 0 D * B
  refine ⟨C, mul_nonneg (le_max_left _ _) hB₀, fun x => ?_⟩
  by_cases hx : x ∈ tsupport χ
  · rw [abs_mul]
    exact mul_le_mul ((hD ⟨x, hx, rfl⟩).trans (le_max_right _ _)) (hB x hx)
      (abs_nonneg _) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport (f := χ) hx, zero_mul, abs_zero]
    exact mul_nonneg (le_max_left _ _) hB₀

theorem integrable_test_mul_mongeAmpereMeasure (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn (complexUnitBall n) v)
    (χ : 𝓓(complexUnitBall n, ℝ)) :
    Integrable (fun x => χ x * v x) (mongeAmpereMeasure hu) := by
  obtain ⟨C, _, hC⟩ := weightedTest_bdd hv χ
  have hs : tsupport (fun x => χ x * v x) ⊆ tsupport χ := tsupport_mul_subset_left
  exact integrable_of_compact_test χ.hasCompactSupport.mul_right
    (weightedTest_aemeasurable hv χ _ (mongeAmpereMeasure_compl hu))
    (mongeAmpereMeasure_finite_on_compact hn hu χ.hasCompactSupport χ.tsupport_subset
      |>.trans_le' (measure_mono hs)) hC

/-- Compactly supported PSH weights are also valid tests for convergence
along the defining Cegrell approximation. -/
theorem tendsto_weighted_mongeAmpereMeasure (hn : 0 < n) (hu : IsE1 (complexUnitBall n) u)
    (p : E1Approximation (complexUnitBall n) u)
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn (complexUnitBall n) v)
    (χ : 𝓓(complexUnitBall n, ℝ)) :
    Tendsto (fun j => ∫ x, χ x * v x ∂topMeasure (p.term_mem j).locallyBoundedPsh) atTop
      (𝓝 (∫ x, χ x * v x ∂mongeAmpereMeasure hu)) := by
  obtain ⟨C, hC₀, hC⟩ := weightedTest_bdd hv χ
  have hs : tsupport (fun x => χ x * v x) ⊆ tsupport χ := tsupport_mul_subset_left
  apply tendsto_mongeAmpereMeasure_of_truncated_tests hn hu p
    (weightedTest_aemeasurable hv χ) χ.hasCompactSupport.mul_right (hs.trans χ.tsupport_subset) hC₀ hC
  intro k
  let q (j : ℕ) (x : ComplexModel n) := max (p.term j x) (truncationLevel k)
  let hq := fun j => locallyBoundedPsh_max_const (p.term_mem j).locallyBoundedPsh (truncationLevel k)
  let v := truncatePotential u (truncationLevel k)
  have hAnti (x : ComplexModel n) (hx : x ∈ complexUnitBall n) : Antitone (fun j => q j x) :=
    fun _ _ h => max_le_max_right _ (p.antitone x hx h)
  have hLim (x : ComplexModel n) (hx : x ∈ complexUnitBall n) :
      Tendsto (fun j => q j x) atTop (𝓝 (v x)) :=
    p.tendsto_truncate hu.1 (truncationLevel k) x hx
  exact tendsto_weightedTopMeasure_of_decreasing hv
    (truncatePotential_locallyBoundedPsh hu (truncationLevel k)) (fun _ => hv) hq
    (fun _ _ => antitone_const) hAnti (fun _ _ => tendsto_const_nhds) hLim χ

/-- On the bounded class the finite-energy measure is the original
Bedford–Taylor measure. -/
theorem mongeAmpereMeasure_eq_topMeasure (hn : 0 < n)
    {v : ComplexModel n → ℝ} (hv : IsE0 (complexUnitBall n) v) :
    mongeAmpereMeasure hv.isE1 = topMeasure hv.locallyBoundedPsh := by
  apply ambientMeasure_eq_of_smooth_test (mongeAmpereMeasure_compl hv.isE1)
    (topMeasure_compl hv.locallyBoundedPsh)
    (fun _ => mongeAmpereMeasure_finite_on_compact hn hv.isE1)
    (fun _ => topMeasure_finite_on_compact hv.locallyBoundedPsh)
  intro φ
  let p : E1Approximation (complexUnitBall n) (fun x => (v x : EReal)) :=
    ⟨fun _ => v, fun _ => hv, fun _ _ _ _ _ => le_rfl, fun _ _ => tendsto_const_nhds,
      by simpa only [ciSup_const] using boundedEnergy_lt_top hv⟩
  exact tendsto_nhds_unique (tendsto_mongeAmpereMeasure hn hv.isE1 p
    φ.continuous φ.hasCompactSupport φ.tsupport_subset) tendsto_const_nhds

theorem energy_eq_boundedEnergy (hn : 0 < n)
    {v : ComplexModel n → ℝ} (hv : IsE0 (complexUnitBall n) v) :
    energy hv.isE1 = boundedEnergy hv := by
  rw [energy, boundedEnergy, mongeAmpereMeasure_eq_topMeasure hn hv]
  apply lintegral_congr
  intro x
  rw [← EReal.coe_neg]
  rfl

#print axioms tendsto_mongeAmpereMeasure
#print axioms energy_lt_top

end KEBall.Cegrell
