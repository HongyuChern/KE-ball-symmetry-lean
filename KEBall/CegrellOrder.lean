import KEBall.CegrellEnergyConvergence

/-!
# Order properties of the Cegrell classes on the ball
-/

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

variable {n : ℕ} {u v : ComplexModel n → ℝ}

private theorem test_integral_le_mass
    {Ω : Opens (ComplexModel n)} (hu : IsLocallyBoundedPshOn Ω u) (χ : 𝓓(Ω, ℝ))
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (∫ x, χ x ∂topMeasure hu) ≤ topMeasure hu univ := by
  have hi : Integrable (fun x => χ x) (topMeasure hu) := by
    simpa only [mul_one] using
      integrable_test_mul_topMeasure (locallyBoundedPsh_const 1) hu χ
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => (hχ x).1)]
  exact (lintegral_mono fun x => (ENNReal.ofReal_le_ofReal (hχ x).2).trans_eq ENNReal.ofReal_one).trans_eq
    (by rw [lintegral_const, one_mul])

/-- Total Monge–Ampère mass decreases when a bounded zero-boundary
potential is raised to a nonpositive locally bounded PSH potential. -/
theorem topMeasure_univ_le_of_e0_le {Ω : Opens (ComplexModel n)}
    (hΩ : IsCompact (closure (Ω : Set (ComplexModel n)))) (hu : IsE0 Ω u)
    (hu₀ : ∀ x ∈ Ω, u x ≤ 0) (hv : IsLocallyBoundedPshOn Ω v)
    (hv₀ : ∀ x ∈ Ω, v x ≤ 0) (hle : ∀ x ∈ Ω, u x ≤ v x) :
    topMeasure hv univ ≤ topMeasure hu.locallyBoundedPsh univ := by
  let μ := topMeasure hv
  let M := topMeasure hu.locallyBoundedPsh univ
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεAnti : Antitone ε := fun i j hij => one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hεLim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  let q (j : ℕ) (x : ComplexModel n) := max (u x) (v x + -ε j)
  let p (j : ℕ) (x : ComplexModel n) := max (u x + ε j) (v x)
  have hq (j : ℕ) : IsE0 Ω (q j) ∧
      ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ Ω ∧ EqOn u (q j) (Ω \ K) :=
    hu.max_shift hΩ hv hu₀ hv₀ (hε j)
  let hqE (j : ℕ) := (hq j).1
  have he (j : ℕ) : (fun x => q j x + ε j) = p j := by
    funext x
    change max (u x) (v x + -ε j) + ε j = max (u x + ε j) (v x)
    rw [← max_add_add_right, neg_add_cancel_right]
  have hp (j : ℕ) : IsLocallyBoundedPshOn Ω (p j) :=
    he j ▸ locallyBoundedPsh_add_const (hqE j).locallyBoundedPsh (ε j)
  have hMassP (j : ℕ) : topMeasure (hp j) univ = M := by
    obtain ⟨K, hK, hKB, hKq⟩ := (hq j).2
    have hShift := topMeasure_add_const (hqE j).locallyBoundedPsh (ε j)
    have hShift' : topMeasure (hp j) = topMeasure (hqE j).locallyBoundedPsh := by
      rw [← hShift]
      exact topMeasure_congr (hp j) _ (fun x _ => congrFun (he j).symm x)
    rw [hShift']
    exact (topMeasure_total_eq_of_eq_off_compact hu.locallyBoundedPsh
      (hqE j).locallyBoundedPsh hK hKB hKq).symm
  have hAnti (x : ComplexModel n) (_ : x ∈ Ω) : Antitone (fun j => p j x) :=
    fun _ _ h => max_le_max_right _ (add_le_add le_rfl (hεAnti h))
  have hLim (x : ComplexModel n) (hx : x ∈ Ω) :
      Tendsto (fun j => p j x) atTop (𝓝 (v x)) := by
    simpa only [p, add_zero, max_eq_right (hle x hx)] using
      ((tendsto_const_nhds (x := u x)).add hεLim).max (tendsto_const_nhds (x := v x))
  have hbound : (∫⁻ _ : ComplexModel n, ENNReal.ofReal (-(-1 : ℝ)) ∂μ) ≤ M := by
    apply lintegral_energy_le_of_cutoff_bound (v := fun _ => -1) (topMeasure_compl hv)
    intro χ hχ
    have hi : Integrable (fun x => χ x) μ := by
      simpa only [mul_one] using integrable_test_mul_topMeasure (locallyBoundedPsh_const 1) hv χ
    simp only [neg_neg, mul_one]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => (hχ x).1)]
    have hWeak := tendsto_topMeasure_of_decreasing hv hp hAnti hLim
      χ χ.continuous χ.hasCompactSupport χ.tsupport_subset
    exact le_of_tendsto (ENNReal.tendsto_ofReal hWeak) (Eventually.of_forall fun j =>
      (test_integral_le_mass (hp j) χ hχ).trans_eq (hMassP j))
  simpa only [neg_neg, ENNReal.ofReal_one, lintegral_const, one_mul] using hbound

/-- A locally bounded nonpositive PSH function lying above a bounded
zero-boundary potential has zero boundary trace and no larger total mass. -/
theorem IsE0.of_ge_on {Ω : Opens (ComplexModel n)}
    (hΩ : IsCompact (closure (Ω : Set (ComplexModel n)))) (hu : IsE0 Ω u)
    (hu₀ : ∀ x ∈ Ω, u x ≤ 0) (hv : IsLocallyBoundedPshOn Ω v)
    (hneg : ∀ x ∈ Ω, v x ≤ 0) (hle : ∀ x ∈ Ω, u x ≤ v x) : IsE0 Ω v := by
  have hMass := topMeasure_univ_le_of_e0_le hΩ hu hu₀ hv hneg hle
  obtain ⟨C, hC⟩ := hu.bounded
  refine ⟨hv.1, ⟨C, fun x hx => ?_⟩, ?_, hMass.trans_lt hu.finiteMass⟩
  · rw [abs_of_nonpos (hneg x hx)]
    exact (neg_le_neg (hle x hx)).trans ((neg_le_abs _).trans (hC x hx))
  · intro z hz
    have hmem : ∀ᶠ x in 𝓝[Ω] z, x ∈ Ω := self_mem_nhdsWithin
    exact (hu.boundary z hz).squeeze' tendsto_const_nhds (hmem.mono hle) (hmem.mono hneg)

theorem IsE0.of_ge (hn : 0 < n) (hu : IsE0 (complexUnitBall n) u)
    (hv : IsLocallyBoundedPshOn (complexUnitBall n) v)
    (hneg : ∀ x ∈ complexUnitBall n, v x ≤ 0)
    (hle : ∀ x ∈ complexUnitBall n, u x ≤ v x) :
    IsE0 (complexUnitBall n) v :=
  hu.of_ge_on (isCompact_closure_complexUnitBall n) (hu.nonpositive_unitBall hn) hv hneg hle

/-- Truncate an extended-real potential from below by a finite potential. -/
noncomputable def maxRealPotential (p : ComplexModel n → EReal) (b : ComplexModel n → ℝ) :
    ComplexModel n → ℝ :=
  fun x => (max (p x) (b x : EReal)).toReal

theorem coe_maxRealPotential {p : ComplexModel n → EReal} {b : ComplexModel n → ℝ}
    {x : ComplexModel n} (hp : p x ≠ ⊤) :
    (maxRealPotential p b x : EReal) = max (p x) (b x : EReal) := by
  apply EReal.coe_toReal
  · exact ne_of_lt (max_lt (lt_top_iff_ne_top.mpr hp) (EReal.coe_lt_top _))
  · exact ne_of_gt ((bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot (b x))).trans_le (le_max_right _ _))

theorem maxRealPotential_locallyBounded
    {p : ComplexModel n → EReal} {b : ComplexModel n → ℝ}
    (hp : PlurisubharmonicOn p (complexUnitBall n))
    (hneg : ∀ x ∈ complexUnitBall n, p x ≤ 0)
    (hb : IsLocallyBoundedPshOn (complexUnitBall n) b)
    (hbNeg : ∀ x ∈ complexUnitBall n, b x ≤ 0) :
    IsLocallyBoundedPshOn (complexUnitBall n) (maxRealPotential p b) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    apply (hp.max hb.1 x hx).congr
    filter_upwards [(complexUnitBall n).isOpen.mem_nhds hx] with y hy
    exact (coe_maxRealPotential ((hp y hy).ne_top)).symm
  · intro x hx
    obtain ⟨W, hxW, hWB, C, hC⟩ := hb.2 x hx
    refine ⟨W, hxW, hWB, C, fun y hy => ?_⟩
    have he := coe_maxRealPotential (b := b) ((hp y (hWB hy)).ne_top)
    have h₁ : b y ≤ maxRealPotential p b y := by
      rw [← EReal.coe_le_coe_iff, he]
      exact le_max_right _ _
    have h₂ : maxRealPotential p b y ≤ 0 := by
      rw [← EReal.coe_le_coe_iff, he, EReal.coe_zero]
      exact max_le (hneg y (hWB hy)) (by exact_mod_cast hbNeg y (hWB hy))
    rw [abs_of_nonpos h₂]
    exact (neg_le_neg h₁).trans ((neg_le_abs _).trans (hC y hy))

/-- The finite-energy class is closed under passing to a larger
nonpositive PSH potential, with an energy bound from the original potential. -/
theorem IsE1.of_ge (hn : 0 < n)
    {p q : ComplexModel n → EReal} (hp : IsE1 (complexUnitBall n) p)
    (hq : PlurisubharmonicOn q (complexUnitBall n))
    (hqNeg : ∀ x ∈ complexUnitBall n, q x ≤ 0)
    (hpq : ∀ x ∈ complexUnitBall n, p x ≤ q x) :
    ∃ h : IsE1 (complexUnitBall n) q, energy h ≤ energy hp := by
  obtain ⟨a⟩ := hp.2
  let B := complexUnitBall n
  let b (j : ℕ) := maxRealPotential q (a.term j)
  have hbEq (j : ℕ) (x : ComplexModel n) (hx : x ∈ B) :
      (b j x : EReal) = max (q x) (a.term j x : EReal) :=
    coe_maxRealPotential ((hq x hx).ne_top)
  have hbge (j : ℕ) (x : ComplexModel n) (hx : x ∈ B) : a.term j x ≤ b j x := by
    rw [← EReal.coe_le_coe_iff, hbEq j x hx]
    exact le_max_right _ _
  have hbNeg (j : ℕ) (x : ComplexModel n) (hx : x ∈ B) : b j x ≤ 0 := by
    rw [← EReal.coe_le_coe_iff, hbEq j x hx, EReal.coe_zero]
    exact max_le (hqNeg x hx) (by exact_mod_cast (a.term_mem j).nonpositive_unitBall hn x hx)
  let hbE (j : ℕ) : IsE0 B (b j) := (a.term_mem j).of_ge hn
    (maxRealPotential_locallyBounded hq hqNeg (a.term_mem j).locallyBoundedPsh
      ((a.term_mem j).nonpositive_unitBall hn)) (hbNeg j) (hbge j)
  have hbound : (⨆ j, boundedEnergy (hbE j)) ≤ ⨆ j, boundedEnergy (a.term_mem j) :=
    iSup_mono fun j => boundedEnergy_le_of_le hn (a.term_mem j) (hbE j) (hbge j)
  let approx : E1Approximation B q := {
    term := b
    term_mem := hbE
    antitone := fun x hx i j hij => by
      rw [← EReal.coe_le_coe_iff, hbEq i x hx, hbEq j x hx]
      exact max_le_max_left _ (EReal.coe_le_coe_iff.mpr (a.antitone x hx hij))
    pointwise := fun x hx => by
      apply (show Tendsto (fun j => max (q x) (a.term j x : EReal)) atTop (𝓝 (q x)) from by
        simpa only [max_eq_left (hpq x hx)] using
          (tendsto_const_nhds (x := q x)).max (a.pointwise x hx)).congr
      intro j
      exact (hbEq j x hx).symm
    energyBound := hbound.trans_lt a.energyBound }
  let h : IsE1 B q := ⟨hq, ⟨approx⟩⟩
  exact ⟨h, (energy_eq_iSup hn h approx).le.trans (hbound.trans (energy_eq_iSup hn hp a).ge)⟩

end KEBall.Cegrell
