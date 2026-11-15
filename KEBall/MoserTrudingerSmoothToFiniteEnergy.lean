import KEBall.CegrellSmoothApproximation
import KEBall.CegrellExponentialConvergence
import KEBall.CegrellUniformExponential

/-!
# Passing smooth ball inequalities to the finite-energy class
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

variable {n : ℕ}

theorem finiteEnergyFunctional_le_iff_exponentialIntegral_le (hn : 0 < n) {γ C : ℝ}
    (hγ : 0 < γ) {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) :
    finiteEnergyFunctional γ hu ≤ (C : EReal) ↔
      exponentialIntegral γ u ≤ ENNReal.ofReal (Real.exp (γ * (C + (energy hu).toReal / (n + 1 : ℝ)))) := by
  by_cases hfin : exponentialIntegral γ u = ⊤
  · rw [finiteEnergyFunctional, if_pos hfin, hfin]
    exact iff_of_false (fun h => EReal.coe_ne_top _ (top_le_iff.mp h))
      (fun h => ENNReal.ofReal_ne_top (top_le_iff.mp h))
  · have hpos : 0 < (exponentialIntegral γ u).toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (exponentialIntegral_ge_one hn hu hγ.le)).ne' hfin
    rw [finiteEnergyFunctional, if_neg hfin, EReal.coe_le_coe_iff, sub_le_iff_le_add,
      div_le_iff₀ hγ, mul_comm _ γ, Real.log_le_iff_le_exp hpos,
      ← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, ENNReal.ofReal_toReal hfin]

private theorem finiteEnergyFunctional_le_of_tendsto (hn : 0 < n) {γ C : ℝ}
    (hγ : 0 < γ) {p : ℕ → ComplexModel n → EReal}
    (hp : ∀ j, IsE1 (complexUnitBall n) (p j))
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u)
    (hE : Tendsto (fun j => energy (hp j)) atTop (𝓝 (energy hu)))
    (hZ : Tendsto (fun j => exponentialIntegral γ (p j)) atTop (𝓝 (exponentialIntegral γ u)))
    (h : ∀ j, finiteEnergyFunctional γ (hp j) ≤ (C : EReal)) :
    finiteEnergyFunctional γ hu ≤ (C : EReal) := by
  rw [finiteEnergyFunctional_le_iff_exponentialIntegral_le hn hγ hu]
  have hE' := (ENNReal.tendsto_toReal (energy_lt_top hn hu).ne).comp hE
  have hR := ENNReal.tendsto_ofReal
    (Real.continuous_exp.continuousAt.tendsto.comp
      (((hE'.div_const (n + 1 : ℝ)).const_add C).const_mul γ))
  exact le_of_tendsto_of_tendsto' hZ hR
    (fun j => (finiteEnergyFunctional_le_iff_exponentialIntegral_le hn hγ (hp j)).mp (h j))

private theorem exponentialIntegral_tendsto_of_uniform_lower (hn : 0 < n) {γ A : ℝ}
    (hγ : 0 < γ)
    {p : ℕ → ComplexModel n → ℝ} (hp : ∀ j, IsE0 (complexUnitBall n) (p j))
    {u : ComplexModel n → ℝ}
    (hlim : ∀ x ∈ complexUnitBall n, Tendsto (fun j => p j x) atTop (𝓝 (u x)))
    (hLower : ∀ j x, x ∈ complexUnitBall n → -A ≤ p j x) :
    Tendsto (fun j => exponentialIntegral γ (fun x => (p j x : EReal))) atTop
      (𝓝 (exponentialIntegral γ (fun x => (u x : EReal)))) := by
  let β := γ + 1
  have hβ : γ < β := lt_add_of_pos_right γ zero_lt_one
  have hmaps (x : E n) (hx : x ∈ unitBall n) : complexCoordinates n x ∈ complexUnitBall n := by
    change x ∈ (complexCoordinates n) ⁻¹' (complexUnitBall n : Set (ComplexModel n))
    rwa [preimage_complexUnitBall]
  have hAe : ∀ᵐ x ∂(volume0 n).restrict (unitBall n),
      Tendsto (fun j => (p j (complexCoordinates n x) : EReal)) atTop
        (𝓝 (u (complexCoordinates n x) : EReal)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from isOpen_ball.measurableSet)] with x hx
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp (hlim _ (hmaps x hx))
  apply exponentialIntegral_tendsto_of_uniform_higher hn (fun j => (hp j).isE1) hAe
    hγ hβ (C := ENNReal.ofReal (Real.exp (β * A))) ENNReal.ofReal_ne_top
  intro j
  unfold exponentialIntegral
  calc
    _ ≤ ∫⁻ _ in unitBall n, ENNReal.ofReal (Real.exp (β * A)) ∂volume0 n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from isOpen_ball.measurableSet)] with x hx
      rw [finiteEnergyWeight, if_pos hx, ← expNeg_const_mul _ β, ← EReal.coe_mul, expNeg_coe]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
        have hb := mul_le_mul_of_nonneg_left (hLower j _ (hmaps x hx)) (hγ.trans hβ).le
        linarith))
    _ = _ := by rw [setLIntegral_const, volume0_unitBall n hn, mul_one]

/-- A uniform bound verified on globally smooth, strictly PSH
zero-boundary potentials extends to the actual finite-energy class. -/
theorem finiteEnergyFunctional_le_of_smooth_bound (hn : 0 < n) {γ C : ℝ}
    (hγ : 0 < γ)
    (hSmooth : ∀ {q : ComplexModel n → ℝ} (hq : IsE0 (complexUnitBall n) q),
      ContDiff ℝ ∞ q → (∀ x ∈ complexUnitBall n, (modelHessian q x).PosDef) →
      finiteEnergyFunctional γ hq.isE1 ≤ (C : EReal))
    {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u) :
    finiteEnergyFunctional γ hu ≤ (C : EReal) := by
  let B := complexUnitBall n
  have hCollar {w : ComplexModel n → ℝ} (hw : IsE0 B w)
      {c : ℝ} (hc : 0 < c) {K : Set (ComplexModel n)} (hK : IsCompact K) (hKB : K ⊆ B)
      (hEq : EqOn w (fun x => c * ballQuadratic n x) (B \ K))
      (hLower : ∀ x ∈ B, c * ballQuadratic n x ≤ w x) :
      finiteEnergyFunctional γ hw.isE1 ≤ (C : EReal) := by
    obtain ⟨q, hq, hqC, hqH, hqLower, hqLim, hqE⟩ :=
      exists_smoothApproximation_of_quadratic_collar hn hw hc hK hKB hEq hLower
    apply finiteEnergyFunctional_le_of_tendsto hn hγ (fun j => (hq j).isE1) hw.isE1
    · change Tendsto (fun j => energy (hq j).isE1) atTop (𝓝 (energy hw.isE1))
      rw [energy_eq_boundedEnergy hn hw]
      exact hqE.congr fun j => (energy_eq_boundedEnergy hn (hq j)).symm
    · apply exponentialIntegral_tendsto_of_uniform_lower hn hγ hq hqLim (A := c + 1)
      intro j x hx
      refine le_trans ?_ (hqLower j x hx)
      have hr : -1 ≤ ballQuadratic n x := by dsimp [ballQuadratic]; nlinarith [sq_nonneg ‖x‖]
      simpa only [mul_neg, mul_one, neg_mul] using
        mul_le_mul_of_nonneg_left hr (show 0 ≤ c + 1 by positivity)
    · exact fun j => hSmooth (hq j) (hqC j) (hqH j)
  have hBounded {w : ComplexModel n → ℝ} (hw : IsE0 B w) :
      finiteEnergyFunctional γ hw.isE1 ≤ (C : EReal) := by
    let c (k : ℕ) : ℝ := (k : ℝ) + 1
    have hc (k : ℕ) : 0 < c k := by dsimp [c]; positivity
    let b (k : ℕ) (x : ComplexModel n) := c k * ballQuadratic n x
    let hb (k : ℕ) := (ballQuadratic_isE0 n).const_mul (hc k)
    let v (k : ℕ) (x : ComplexModel n) := max (b k x) (w x)
    let hv (k : ℕ) : IsE0 B (v k) := (hb k).of_ge hn
      (locallyBoundedPsh_max (hb k).locallyBoundedPsh hw.locallyBoundedPsh)
      (fun x hx => max_le ((hb k).nonpositive_unitBall hn x hx) (hw.nonpositive_unitBall hn x hx))
      (fun _ _ => le_max_left _ _)
    have hvBound (k : ℕ) : finiteEnergyFunctional γ (hv k).isE1 ≤ (C : EReal) := by
      let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
      have hε₀ (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
      have hεAnti : Antitone ε := fun i j hij => one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hij 1)
      have hεLim : Tendsto ε atTop (𝓝 0) :=
        (tendsto_atTop_add_const_right atTop (1 : ℝ)
          (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
      let p (j : ℕ) (x : ComplexModel n) := max (b k x) (w x + -ε j)
      have hp (j : ℕ) : IsE0 B (p j) ∧
          ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ B ∧ EqOn (b k) (p j) (B \ K) :=
        (hb k).max_shift (isCompact_closure_complexUnitBall n) hw.locallyBoundedPsh
          ((hb k).nonpositive_unitBall hn) (hw.nonpositive_unitBall hn) (hε₀ j)
      let hpE (j : ℕ) := (hp j).1
      apply finiteEnergyFunctional_le_of_tendsto hn hγ (fun j => (hpE j).isE1) (hv k).isE1
      · change Tendsto (fun j => energy (hpE j).isE1) atTop (𝓝 (energy (hv k).isE1))
        rw [energy_eq_boundedEnergy hn (hv k)]
        exact (tendsto_energy_max_sub_const hn (hb k) hw hεLim hε₀ hεAnti (hv k) hpE).congr
          (fun j => (energy_eq_boundedEnergy hn (hpE j)).symm)
      · refine exponentialIntegral_tendsto_of_uniform_lower hn hγ hpE (A := c k) ?_ ?_
        · intro x _
          simpa only [p, v, neg_zero, add_zero] using
            (tendsto_const_nhds (x := b k x)).max ((tendsto_const_nhds (x := w x)).add hεLim.neg)
        · intro j x hx
          have hr : -1 ≤ ballQuadratic n x := by dsimp [ballQuadratic]; nlinarith [sq_nonneg ‖x‖]
          have hb' : -(c k) ≤ b k x := by
            simpa only [b, mul_neg, mul_one, neg_mul] using
              mul_le_mul_of_nonneg_left hr (hc k).le
          exact hb'.trans (le_max_left _ _)
      · intro j
        obtain ⟨K, hK, hKB, he⟩ := (hp j).2
        exact hCollar (hpE j) (hc k) hK hKB (fun x hx => (he hx).symm)
          (fun _ _ => le_max_left _ _)
    let a : E1Approximation B (fun x => (w x : EReal)) := {
      term := v
      term_mem := hv
      antitone := fun x hx i j hij => by
        apply max_le_max_right
        exact mul_le_mul_of_nonpos_right (show c i ≤ c j from
          add_le_add_left (by exact_mod_cast hij) _) (ballQuadratic_neg n hx).le
      pointwise := fun x hx => by
        have hTop : Tendsto c atTop atTop :=
          tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
        have hBot : Tendsto (fun k => b k x) atTop atBot :=
          hTop.atTop_mul_const_of_neg (ballQuadratic_neg n hx)
        apply tendsto_const_nhds.congr'
        filter_upwards [(tendsto_atBot.mp hBot) (w x)] with k hk
        change (w x : EReal) = ((max (b k x) (w x) : ℝ) : EReal)
        rw [max_eq_right hk]
      energyBound := (iSup_le (fun k => boundedEnergy_le_of_le hn hw (hv k)
        (fun _ _ => le_max_right _ _))).trans_lt (boundedEnergy_lt_top hw) }
    apply finiteEnergyFunctional_le_of_tendsto hn hγ (fun k => (hv k).isE1) hw.isE1
    · change Tendsto (fun j => energy (hv j).isE1) atTop (𝓝 (energy hw.isE1))
      simp_rw [energy_eq_boundedEnergy hn (hv _)]
      exact tendsto_boundedEnergy hn hw.isE1 a
    · exact exponentialIntegral_tendsto_of_approximation a hγ.le
    · exact hvBound
  obtain ⟨p⟩ := hu.2
  apply finiteEnergyFunctional_le_of_tendsto hn hγ (fun j => (p.term_mem j).isE1) hu
  · change Tendsto (fun j => energy (p.term_mem j).isE1) atTop (𝓝 (energy hu))
    simp_rw [energy_eq_boundedEnergy hn (p.term_mem _)]
    exact tendsto_boundedEnergy hn hu p
  · exact exponentialIntegral_tendsto_of_approximation p hγ.le
  · exact fun j => hBounded (p.term_mem j)

end KEBall.MoserTrudinger
