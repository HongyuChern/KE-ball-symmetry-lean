import KEBall.CegrellTruncatedLimit
import KEBall.BedfordTaylorEnergyComparison

/-!
# Monotonicity of the bounded Cegrell energy
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}

theorem IsE0.integrable_against_topMeasure (hu : IsE0 Ω u) (hv : IsE0 Ω v) :
    Integrable u (topMeasure hv.locallyBoundedPsh) := by
  let μ := topMeasure hv.locallyBoundedPsh
  let : IsFiniteMeasure μ := ⟨hv.finiteMass⟩
  have hdom : ∀ᵐ x ∂μ, x ∈ Ω := by
    rw [ae_iff]
    exact topMeasure_compl hv.locallyBoundedPsh
  have hm : AEMeasurable u (μ.restrict Ω) :=
    aemeasurable_restrict_of_measurable_subtype Ω.isOpen.measurableSet
      (measurable_subtype_of_locallyBoundedPsh hu.locallyBoundedPsh)
  rw [Measure.restrict_eq_self_of_ae_mem hdom] at hm
  obtain ⟨C, hC⟩ := hu.bounded
  exact Integrable.of_bound hm.aestronglyMeasurable C (by
    filter_upwards [hdom] with x hx
    simpa only [Real.norm_eq_abs] using hC x hx)

/-- The nonnegative integral of one bounded potential against the top
measure of another. -/
noncomputable def crossEnergy (hu : IsE0 Ω u) (v : ComplexModel n → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-v x) ∂topMeasure hu.locallyBoundedPsh

theorem crossEnergy_eq_ofReal (hu : IsE0 Ω u) (hv : IsE0 Ω v)
    (hneg : ∀ x ∈ Ω, v x ≤ 0) :
    crossEnergy hu v = ENNReal.ofReal (-(∫ x, v x ∂topMeasure hu.locallyBoundedPsh)) := by
  have ha : ∀ᵐ x ∂topMeasure hu.locallyBoundedPsh, x ∈ Ω := by
    rw [ae_iff]
    exact topMeasure_compl hu.locallyBoundedPsh
  have hnonneg : 0 ≤ᵐ[topMeasure hu.locallyBoundedPsh] fun x => -v x := by
    filter_upwards [ha] with x hx
    exact neg_nonneg.mpr (hneg x hx)
  simpa only [crossEnergy, Pi.neg_apply, integral_neg] using
    (ofReal_integral_eq_lintegral_ofReal (hv.integrable_against_topMeasure hu).neg hnonneg).symm

private theorem integral_weight_le_of_eq_off_compact (hu : IsE0 Ω u) (hv : IsE0 Ω v)
    (hle : ∀ x ∈ Ω, u x ≤ v x)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (he : EqOn u v (Ω \ K)) :
    (∫ x, v x ∂topMeasure hu.locallyBoundedPsh) ≤ ∫ x, v x ∂topMeasure hv.locallyBoundedPsh := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨χ, hχrange, hχone⟩ := exists_testFunction_one_on hWc hWΩ
  have hχ (x : ComplexModel n) (hx : x ∈ K) : (χ : ComplexModel n → ℝ) =ᶠ[𝓝 x] 1 := by
    filter_upwards [hWo.mem_nhds (hKW hx)] with y hy
    exact hχone (subset_closure hy)
  let μ := topMeasure hu.locallyBoundedPsh
  let ν := topMeasure hv.locallyBoundedPsh
  have hterm : (∫ x, χ x * v x ∂μ) ≤ ∫ x, χ x * v x ∂ν := by
    dsimp only [μ, ν]
    rw [integral_topMeasure_map, integral_topMeasure_map]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact integral_weightedDiagonalMeasure_mono_of_eq_off_compact hu.locallyBoundedPsh
      hv.locallyBoundedPsh hK hKΩ he hle χ hχ (fun x _ => (hχrange x).1) id
  have hcompl : μ.restrict Kᶜ = ν.restrict Kᶜ :=
    topMeasure_restrict_compl_eq_of_eq_off_compact hu.locallyBoundedPsh hv.locallyBoundedPsh hK he
  have hzero (x : ComplexModel n) (hx : x ∉ Kᶜ) : (1 - χ x) * v x = 0 := by
    rw [show χ x = 1 from (hχ x (by simpa using hx)).eq_of_nhds, sub_self, zero_mul]
  have hcomp : (∫ x, (1 - χ x) * v x ∂μ) = ∫ x, (1 - χ x) * v x ∂ν := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) hzero,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν) hzero, hcompl]
  have hsplit {p : ComplexModel n → ℝ} (hp : IsE0 Ω p) :
      (∫ x, (1 - χ x) * v x ∂topMeasure hp.locallyBoundedPsh) =
        (∫ x, v x ∂topMeasure hp.locallyBoundedPsh) -
          ∫ x, χ x * v x ∂topMeasure hp.locallyBoundedPsh := by
    simp only [sub_mul, one_mul]
    exact integral_sub (hv.integrable_against_topMeasure hp)
      (integrable_test_mul_topMeasure hv.locallyBoundedPsh hp.locallyBoundedPsh χ)
  rw [hsplit hu, hsplit hv] at hcomp
  change (∫ x, v x ∂μ) ≤ ∫ x, v x ∂ν
  linarith

theorem IsE0.max_shift (hΩ : IsCompact (closure (Ω : Set (ComplexModel n))))
    (hu : IsE0 Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    (huNeg : ∀ x ∈ Ω, u x ≤ 0) (hvNeg : ∀ x ∈ Ω, v x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    IsE0 Ω (fun x => max (u x) (v x + -ε)) ∧
      ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ Ω ∧
        EqOn u (fun x => max (u x) (v x + -ε)) (Ω \ K) := by
  let hp := locallyBoundedPsh_max hu.locallyBoundedPsh (locallyBoundedPsh_add_const hv (-ε))
  let K := closure {x ∈ Ω | u x ≤ -ε}
  have hKΩ : K ⊆ Ω := sublevel_closure_subset hu (neg_lt_zero.mpr hε)
  have hK : IsCompact K :=
    hΩ.of_isClosed_subset isClosed_closure (closure_mono fun _ hx => hx.1)
  have he : EqOn u (fun x => max (u x) (v x + -ε)) (Ω \ K) := by
    intro x hx
    have hlt : -ε < u x := lt_of_not_ge fun h => hx.2 (subset_closure ⟨hx.1, h⟩)
    exact (max_eq_left (by linarith [hvNeg x hx.1])).symm
  obtain ⟨A, hA⟩ := hu.bounded
  have hnonpos (x : ComplexModel n) (hx : x ∈ Ω) :
      max (u x) (v x + -ε) ≤ 0 :=
    max_le (huNeg x hx) (add_nonpos (hvNeg x hx) (neg_nonpos.mpr hε.le))
  refine ⟨⟨hp.1, ⟨A, ?_⟩, ?_, ?_⟩, K, hK, hKΩ, he⟩
  · intro x hx
    rw [abs_of_nonpos (hnonpos x hx)]
    exact (neg_le_neg (le_max_left _ _)).trans ((neg_le_abs _).trans (hA x hx))
  · intro z hz
    have hmem : ∀ᶠ x in 𝓝[Ω] z, x ∈ Ω := self_mem_nhdsWithin
    exact (hu.boundary z hz).squeeze' tendsto_const_nhds
      (Eventually.of_forall fun x => le_max_left _ _) (hmem.mono hnonpos)
  · exact (topMeasure_total_eq_of_eq_off_compact hu.locallyBoundedPsh hp hK hKΩ he).symm.trans_lt
      hu.finiteMass

/-- An upper potential has energy bounded by its integral against the
top measure of the lower potential. -/
theorem boundedEnergy_le_crossEnergy (hn : 0 < n) {u v : ComplexModel n → ℝ}
    (hu : IsE0 (complexUnitBall n) u) (hv : IsE0 (complexUnitBall n) v)
    (hle : ∀ x ∈ complexUnitBall n, u x ≤ v x) :
    boundedEnergy hv ≤ crossEnergy hu v := by
  let B := complexUnitBall n
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεAnti : Antitone ε := fun i j hij => one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hεLim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  let q (j : ℕ) (x : ComplexModel n) := max (u x) (v x + -ε j)
  have hq (j : ℕ) : IsE0 B (q j) ∧
      ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ B ∧ EqOn u (q j) (B \ K) :=
    hu.max_shift (isCompact_closure_complexUnitBall n) hv.locallyBoundedPsh
      (hu.nonpositive_unitBall hn) (hv.nonpositive_unitBall hn) (hε j)
  let hqE (j : ℕ) := (hq j).1
  have hqBound (j : ℕ) :
      (∫ x, q j x ∂topMeasure hu.locallyBoundedPsh) ≤
        ∫ x, q j x ∂topMeasure (hqE j).locallyBoundedPsh := by
    obtain ⟨K, hK, hKB, he⟩ := (hq j).2
    exact integral_weight_le_of_eq_off_compact hu (hqE j) (fun x _ => le_max_left _ _) hK hKB he
  let p (j : ℕ) (x : ComplexModel n) := q j x + ε j
  let hp (j : ℕ) := locallyBoundedPsh_add_const (hqE j).locallyBoundedPsh (ε j)
  have hEq (j : ℕ) (x : ComplexModel n) : p j x = max (u x + ε j) (v x) := by
    change max (u x) (v x + -ε j) + ε j = _
    rw [← max_add_add_right]
    simp only [neg_add_cancel_right]
  have hAnti (x : ComplexModel n) (_ : x ∈ B) : Antitone (fun j => p j x) := by
    intro i j hij
    change p j x ≤ p i x
    rw [hEq, hEq]
    exact max_le_max_right _ (add_le_add le_rfl (hεAnti hij))
  have hLim (x : ComplexModel n) (hx : x ∈ B) :
      Tendsto (fun j => p j x) atTop (𝓝 (v x)) := by
    simp_rw [hEq]
    simpa only [add_zero, max_eq_right (hle x hx)] using
      ((tendsto_const_nhds (x := u x)).add hεLim).max (tendsto_const_nhds (x := v x))
  apply lintegral_energy_le_of_cutoff_bound (topMeasure_compl hv.locallyBoundedPsh)
  intro χ hχ
  have hχnonneg (x : ComplexModel n) : 0 ≤ χ x := (hχ x).1
  have hlim := (tendsto_weightedTopMeasure_of_decreasing hv.locallyBoundedPsh
    hv.locallyBoundedPsh hp hp hAnti hAnti hLim hLim χ).neg
  let μ := topMeasure hu.locallyBoundedPsh
  let : IsFiniteMeasure μ := ⟨hu.finiteMass⟩
  let L := -(∫ x, v x ∂μ)
  have hbound (j : ℕ) :
      -(∫ x, χ x * p j x ∂topMeasure (hp j)) ≤ L + ε j * μ.real univ := by
    let ν := topMeasure (hqE j).locallyBoundedPsh
    have hν : ∀ᵐ x ∂ν, x ∈ B := by
      rw [ae_iff]
      exact topMeasure_compl (hqE j).locallyBoundedPsh
    have htest : (∫ x, q j x ∂ν) ≤ ∫ x, χ x * p j x ∂ν :=
      integral_mono_ae ((hqE j).integrable_against_topMeasure (hqE j))
        (integrable_test_mul_topMeasure (hp j) (hqE j).locallyBoundedPsh χ) (by
          filter_upwards [hν] with x hx
          calc
            q j x ≤ χ x * q j x :=
              le_mul_of_le_one_left ((hqE j).nonpositive_unitBall hn x hx) (hχ x).2
            _ ≤ χ x * p j x :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hε j).le) (hχnonneg x))
    have herr : (∫ x, v x ∂μ) - ε j * μ.real univ ≤ ∫ x, q j x ∂μ := by
      have hi := integral_mono
        ((hv.integrable_against_topMeasure hu).sub (integrable_const (ε j)))
        ((hqE j).integrable_against_topMeasure hu)
        (fun x => show v x - ε j ≤ q j x from by rw [sub_eq_add_neg]; exact le_max_right _ _)
      change (∫ x, v x - ε j ∂μ) ≤ ∫ x, q j x ∂μ at hi
      rw [integral_sub (hv.integrable_against_topMeasure hu) (integrable_const (ε j)),
        integral_const, smul_eq_mul, mul_comm] at hi
      exact hi
    rw [show topMeasure (hp j) = ν from topMeasure_add_const (hqE j).locallyBoundedPsh _]
    have horder := herr.trans ((hqBound j).trans htest)
    dsimp only [L]
    linarith
  have hRhs : Tendsto (fun j => L + ε j * μ.real univ) atTop (𝓝 L) := by
    simpa only [zero_mul, add_zero] using (tendsto_const_nhds (x := L)).add
      (hεLim.mul_const (μ.real univ))
  rw [lintegral_test_energy_eq_ofReal hv.locallyBoundedPsh (hv.nonpositive_unitBall hn) χ hχnonneg,
    crossEnergy_eq_ofReal hu hv (hv.nonpositive_unitBall hn)]
  exact ENNReal.ofReal_le_ofReal (le_of_tendsto_of_tendsto' hlim hRhs hbound)

/-- The Cegrell energy is order-reversing on bounded zero-boundary
potentials on the ball. -/
theorem boundedEnergy_le_of_le (hn : 0 < n) {u v : ComplexModel n → ℝ}
    (hu : IsE0 (complexUnitBall n) u) (hv : IsE0 (complexUnitBall n) v)
    (hle : ∀ x ∈ complexUnitBall n, u x ≤ v x) :
    boundedEnergy hv ≤ boundedEnergy hu := by
  refine (boundedEnergy_le_crossEnergy hn hu hv hle).trans ?_
  apply lintegral_mono_ae
  have hae : ∀ᵐ x ∂topMeasure hu.locallyBoundedPsh, x ∈ complexUnitBall n := by
    rw [ae_iff]
    exact topMeasure_compl hu.locallyBoundedPsh
  filter_upwards [hae] with x hx
  exact ENNReal.ofReal_le_ofReal (neg_le_neg (hle x hx))

end KEBall.Cegrell
