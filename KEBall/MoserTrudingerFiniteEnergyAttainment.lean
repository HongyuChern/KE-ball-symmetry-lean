import KEBall.CegrellL1Compactness
import KEBall.CegrellCoercivity
import KEBall.CegrellUniformExponential

/-!
# Variational attainment at a smaller coupling
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}

theorem ae_coordinates_of_ae_complexBall
    {P : ComplexModel n → Prop}
    (h : ∀ᵐ z ∂(volume : Measure (ComplexModel n)).restrict (complexUnitBall n), P z) :
    ∀ᵐ x ∂(volume0 n).restrict (unitBall n), P (complexCoordinates n x) := by
  let e := (complexCoordinates n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e ((volume : Measure (E n)).restrict (unitBall n))
      ((volume : Measure (ComplexModel n)).restrict (complexUnitBall n)) := by
    refine ⟨e.measurable, ?_⟩
    rw [← preimage_complexUnitBall]
    change Measure.map e (volume.restrict (e ⁻¹' (complexUnitBall n : Set (ComplexModel n)))) = _
    rw [← e.restrict_map]
    exact congrArg (fun μ : Measure (ComplexModel n) => μ.restrict (complexUnitBall n))
      (complexCoordinates_measurePreserving n).map_eq
  rw [volume0, Measure.restrict_smul]
  exact Measure.ae_smul_measure (he.quasiMeasurePreserving.tendsto_ae.eventually h) _

/-- A finite upper bound at a larger coupling gives an actual
finite-energy maximizer at the smaller coupling. -/
theorem exists_finiteEnergyFunctional_maximizer_of_bound (hn : 0 < n) {α β C : ℝ}
    (hα : 0 < α) (hαβ : α < β)
    (hBound : ∀ {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u),
      finiteEnergyFunctional β hu ≤ (C : EReal)) :
    ∃ (v : ComplexModel n → EReal) (hv : IsE1 (complexUnitBall n) v),
      ∀ {u : ComplexModel n → EReal} (hu : IsE1 (complexUnitBall n) u),
        finiteEnergyFunctional α hu ≤ finiteEnergyFunctional α hv := by
  let B := complexUnitBall n
  let a := α / β
  let D := C / a
  let d := (1 - a ^ n) / (n + 1 : ℝ)
  have hd : 0 < d := div_pos (coercivity_coefficient_pos hn hα hαβ) (by positivity)
  let value (u : ComplexModel n → EReal) (hu : IsE1 B u) :=
    Real.log (exponentialIntegral α u).toReal / α - (energy hu).toReal / (n + 1 : ℝ)
  have hαfin {u : ComplexModel n → EReal} (hu : IsE1 B u) :
      exponentialIntegral α u ≠ ⊤ :=
    (finiteEnergyFunctional_coercive_of_bound hn hα hαβ hBound hu).1.ne
  have hvalue {u : ComplexModel n → EReal} (hu : IsE1 B u) :
      finiteEnergyFunctional α hu = (value u hu : EReal) := by
    rw [finiteEnergyFunctional, if_neg (hαfin hu)]
  have hCoer {u : ComplexModel n → EReal} (hu : IsE1 B u) :
      value u hu ≤ D - d * (energy hu).toReal := by
    have h := (finiteEnergyFunctional_coercive_of_bound hn hα hαβ hBound hu).2
    rw [hvalue hu, EReal.coe_le_coe_iff] at h
    dsimp [D, d, a]
    linarith only [h, show (1 - (α / β) ^ n) * ((energy hu).toReal / (n + 1 : ℝ)) =
      (1 - (α / β) ^ n) / (n + 1 : ℝ) * (energy hu).toReal by ring]
  let S : Set ℝ := {s | ∃ (u : ComplexModel n → EReal) (hu : IsE1 B u), s = value u hu}
  have hS : S.Nonempty :=
    ⟨_, _, (ballQuadratic_isE0 n).isE1, rfl⟩
  have hSb : BddAbove S := ⟨D, by
    rintro s ⟨u, hu, rfl⟩
    exact (hCoer hu).trans (sub_le_self _ (mul_nonneg hd.le ENNReal.toReal_nonneg))⟩
  let m := sSup S
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε₁ (j : ℕ) : ε j ≤ 1 := (div_le_one (by positivity)).mpr
    (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hex (j : ℕ) : ∃ (u : ComplexModel n → EReal) (hu : IsE1 B u), m - ε j < value u hu := by
    obtain ⟨r, ⟨u, hu, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hS (sub_lt_self m (hε j))
    exact ⟨u, hu, hr⟩
  choose p hp hnear using hex
  have hpUpper (j : ℕ) : value (p j) (hp j) ≤ m := le_csSup hSb ⟨p j, hp j, rfl⟩
  have hpLim : Tendsto (fun j => value (p j) (hp j)) atTop (𝓝 m) := by
    have h := (tendsto_const_nhds (x := m)).sub hεlim
    rw [sub_zero] at h
    exact h.squeeze tendsto_const_nhds (fun j => (hnear j).le) hpUpper
  let M := max 0 ((D - m + 1) / d)
  have hM₀ : 0 ≤ M := le_max_left _ _
  have hM (j : ℕ) : (energy (hp j)).toReal ≤ M := by
    apply le_max_of_le_right
    apply (le_div_iff₀ hd).mpr
    linarith [hCoer (hp j), hnear j, hε₁ j]
  have hMenn (j : ℕ) : energy (hp j) ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal (energy_lt_top hn (hp j)).ne]
    exact ENNReal.ofReal_le_ofReal (hM j)
  obtain ⟨v, hv, φ, hφ, _, _, hAe⟩ := exists_subseq_tendsto_of_energy_le hn hp
    ENNReal.ofReal_lt_top hMenn
  have hβ₀ : 0 < β := hα.trans hαβ
  let Cβ := ENNReal.ofReal (Real.exp (β * (C + M / (n + 1 : ℝ))))
  have hβfin (j : ℕ) : exponentialIntegral β (p j) ≠ ⊤ := by
    intro htop
    have h := hBound (hp j)
    rw [finiteEnergyFunctional, if_pos htop] at h
    exact (EReal.coe_ne_top _ (top_le_iff.mp h)).elim
  have hβExp (j : ℕ) : exponentialIntegral β (p j) ≤ Cβ := by
    have h := hBound (hp j)
    rw [finiteEnergyFunctional, if_neg (hβfin j), EReal.coe_le_coe_iff] at h
    have hlog : Real.log (exponentialIntegral β (p j)).toReal ≤ β * (C + M / (n + 1 : ℝ)) := by
      rw [mul_comm β]
      apply (div_le_iff₀ hβ₀).mp
      have he := div_le_div_of_nonneg_right (hM j) (show 0 ≤ (n + 1 : ℝ) by positivity)
      linarith
    have hpos := ENNReal.toReal_pos
      (zero_lt_one.trans_le (exponentialIntegral_ge_one hn (hp j) hβ₀.le)).ne' (hβfin j)
    rw [← ENNReal.ofReal_toReal (hβfin j)]
    exact ENNReal.ofReal_le_ofReal ((Real.log_le_iff_le_exp hpos).mp hlog)
  have hZ := exponentialIntegral_tendsto_of_uniform_higher hn (fun j => hp (φ j))
    (ae_coordinates_of_ae_complexBall hAe) hα hαβ (C := Cβ) ENNReal.ofReal_ne_top
    (fun j => hβExp (φ j))
  have hZpos := ENNReal.toReal_pos
    (zero_lt_one.trans_le (exponentialIntegral_ge_one hn hv hα.le)).ne' (hαfin hv)
  have hLog : Tendsto (fun j => Real.log (exponentialIntegral α (p (φ j))).toReal / α)
      atTop (𝓝 (Real.log (exponentialIntegral α v).toReal / α)) :=
    ((Real.continuousAt_log hZpos.ne').tendsto.comp ((ENNReal.tendsto_toReal (hαfin hv)).comp hZ)).div_const α
  have hVal := hpLim.comp hφ.tendsto_atTop
  have hEn : Tendsto (fun j => (energy (hp (φ j))).toReal) atTop
      (𝓝 ((Real.log (exponentialIntegral α v).toReal / α - m) * (n + 1 : ℝ))) := by
    apply ((hLog.sub hVal).mul_const (n + 1 : ℝ)).congr
    intro j
    change (Real.log (exponentialIntegral α (p (φ j))).toReal / α -
      value (p (φ j)) (hp (φ j))) * (n + 1 : ℝ) = (energy (hp (φ j))).toReal
    dsimp [value]
    field_simp
    ring
  have hE := energy_toReal_le_of_ae_tendsto hn (fun j => hp (φ j)) hv hAe hEn
  have hMax : m ≤ value v hv := by
    dsimp [value]
    have he := (div_le_iff₀ (show 0 < (n + 1 : ℝ) by positivity)).mpr hE
    linarith
  refine ⟨v, hv, fun hu => ?_⟩
  rw [hvalue hu, hvalue hv, EReal.coe_le_coe_iff]
  exact (le_csSup hSb ⟨_, hu, rfl⟩).trans hMax

end KEBall.MoserTrudinger
