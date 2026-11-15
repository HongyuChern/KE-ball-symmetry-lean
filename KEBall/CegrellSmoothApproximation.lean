import KEBall.CegrellCollarRegularization
import KEBall.CegrellShiftedApproximation

/-!
# Strictly plurisubharmonic smooth approximation with zero boundary data
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere hiding complexHessian

local notation "modelHessian" => PshLines.FirstPass.MongeAmpere.complexHessian

variable {n : ℕ}

private theorem complexHessian_ballQuadratic (n : ℕ) (x : ComplexModel n) :
    modelHessian (ballQuadratic n) x = 1 := by
  have h : modelHessian (ballQuadratic n) x = modelHessian (fun y => ‖y‖ ^ 2) x := by
    have hd : fderiv ℝ (ballQuadratic n) = fderiv ℝ (fun y : ComplexModel n => ‖y‖ ^ 2) :=
      funext fun _ => fderiv_sub_const _
    ext i j : 1
    simp only [PshLines.FirstPass.MongeAmpere.complexHessian, PshLines.realHessian_eq_fderiv, hd]
  rw [h, complexHessian_norm_sq]

private theorem complexHessian_sub_const {p : ComplexModel n → ℝ} (x : ComplexModel n) (a : ℝ) :
    modelHessian (fun y => p y - a) x = modelHessian p x := by
  have hd : fderiv ℝ (fun y => p y - a) = fderiv ℝ p := funext fun _ => fderiv_sub_const a
  ext i j : 1
  simp only [PshLines.FirstPass.MongeAmpere.complexHessian, PshLines.realHessian_eq_fderiv, hd]

/-- A bounded potential with a quadratic collar can be approximated
pointwise and in energy by globally smooth, strictly PSH zero-boundary potentials. -/
theorem exists_smoothApproximation_of_quadratic_collar (hn : 0 < n)
    {u : ComplexModel n → ℝ} (hu : IsE0 (complexUnitBall n) u)
    {c : ℝ} (hc : 0 < c)
    {K₀ : Set (ComplexModel n)} (hK₀ : IsCompact K₀) (hK₀B : K₀ ⊆ complexUnitBall n)
    (he : EqOn u (fun x => c * ballQuadratic n x) ((complexUnitBall n : Set (ComplexModel n)) \ K₀))
    (hle : ∀ x ∈ complexUnitBall n, c * ballQuadratic n x ≤ u x) :
    ∃ (q : ℕ → ComplexModel n → ℝ) (hq : ∀ j, IsE0 (complexUnitBall n) (q j)),
      (∀ j, ContDiff ℝ ∞ (q j)) ∧
      (∀ j x, x ∈ complexUnitBall n → (modelHessian (q j) x).PosDef) ∧
      (∀ j x, x ∈ complexUnitBall n → (c + 1) * ballQuadratic n x ≤ q j x) ∧
      (∀ x ∈ complexUnitBall n, Tendsto (fun j => q j x) atTop (𝓝 (u x))) ∧
      Tendsto (fun j => boundedEnergy (hq j)) atTop (𝓝 (boundedEnergy hu)) := by
  obtain ⟨R, hR, p, K, hK, hKB, hpSmooth, hp, hpCollar, hpLower⟩ :=
    exists_decreasingRegularization_quadratic_collar hu hc hK₀ hK₀B he hle
  let B := complexUnitBall n
  let ρ := ballQuadratic n
  let δ (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  let m (j : ℕ) := c * radialKernelSecondMoment n R hR j
  let q (j : ℕ) (x : ComplexModel n) := p j x - m j + δ j * ρ x
  have hδ₀ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδ₁ (j : ℕ) : δ j ≤ 1 := (div_le_one (by positivity)).mpr
    (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hδAnti : Antitone δ := fun i j hij => one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hδLim : Tendsto δ atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hmLim : Tendsto m atTop (𝓝 0) := by
    simpa only [m, mul_zero] using (radialKernelSecondMoment_tendsto n hR).const_mul c
  have hρSmooth : ContDiff ℝ ∞ ρ := (contDiff_norm_sq ℝ).sub contDiff_const
  have hqSmooth (j : ℕ) : ContDiff ℝ ∞ (q j) :=
    ((hpSmooth j).sub contDiff_const).add ((contDiff_const (c := δ j)).mul hρSmooth)
  have hqPos (j : ℕ) (x : ComplexModel n) (hx : x ∈ B) :
      (modelHessian (q j) x).PosDef := by
    let a (x : ComplexModel n) := p j x - m j
    let b (x : ComplexModel n) := δ j * ρ x
    have h₂ : (2 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
    have ha : ContDiffAt ℝ 2 a x := (((hpSmooth j).sub contDiff_const).of_le h₂).contDiffAt
    have hb : ContDiffAt ℝ 2 b x := (((contDiff_const (c := δ j)).mul hρSmooth).of_le h₂).contDiffAt
    change (modelHessian (a + b) x).PosDef
    rw [PshLines.FirstPass.MongeAmpere.complexHessian_add ha hb]
    have hA : (modelHessian a x).PosSemidef := by
      rw [complexHessian_sub_const x (m j)]
      exact (hp.1 j).2.2 x hx
    have hB : (modelHessian b x).PosDef := by
      change (modelHessian (δ j • ρ) x).PosDef
      rw [PshLines.FirstPass.MongeAmpere.complexHessian_smul
        (hρSmooth.of_le h₂).contDiffAt (δ j), complexHessian_ballQuadratic]
      have he : ((δ j : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
          δ j • (1 : Matrix (Fin n) (Fin n) ℂ) := by ext i k : 1; rfl
      rw [he]
      exact Matrix.PosDef.one.smul (hδ₀ j)
    exact Matrix.PosDef.posSemidef_add hA hB
  have hqCollar (j : ℕ) (x : ComplexModel n) (hx : x ∈ closure (B : Set (ComplexModel n)))
      (hxK : x ∉ K) : q j x = (c + δ j) * ρ x := by
    simp only [q, hpCollar j x hx hxK, ρ, m]
    ring
  let hq (j : ℕ) : IsE0 B (q j) := by
    have hS : IsSmoothPshOn B (q j) :=
      isSmoothPshOn_of_coordinateHessian (hqSmooth j).contDiffOn (fun x hx => (hqPos j x hx).posSemidef)
    apply isE0_of_smoothOn_closure (isCompact_closure_complexUnitBall n)
      (W := ⊤) (subset_univ _) hS (hqSmooth j).contDiffOn
    intro x hx
    have hxK : x ∉ K := fun h =>
      Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr B.isOpen) hx (hKB h)
    rw [hqCollar j x (frontier_subset_closure hx) hxK]
    change x ∈ frontier (ball (0 : ComplexModel n) 1) at hx
    rw [frontier_ball _ one_ne_zero] at hx
    simp only [ρ, ballQuadratic, mem_sphere_zero_iff_norm.mp hx, one_pow, sub_self, mul_zero,
      Pi.zero_apply]
  have hqLower (j : ℕ) (x : ComplexModel n) (hx : x ∈ B) : (c + 1) * ρ x ≤ q j x := by
    have hp' := hpLower j x hx
    have hm' : c * ρ x ≤ p j x - m j := by dsimp [ρ, m]; linarith
    have hδ := mul_le_mul_of_nonpos_right (hδ₁ j) (ballQuadratic_neg n hx).le
    change (c + 1) * ρ x ≤ p j x - m j + δ j * ρ x
    linarith
  let s (j : ℕ) := m j + δ j
  have hsLim : Tendsto s atTop (𝓝 0) := by
    simpa only [s, add_zero] using hmLim.add hδLim
  have hsEq (j : ℕ) (x : ComplexModel n) : q j x + s j = p j x + δ j * ‖x‖ ^ 2 := by
    simp only [q, ρ, s, ballQuadratic]
    ring
  have hAnti (x : ComplexModel n) (hx : x ∈ B) : Antitone (fun j => q j x + s j) := by
    intro i j hij
    change q j x + s j ≤ q i x + s i
    rw [hsEq, hsEq]
    exact add_le_add (hp.2.1 x hx hij) (mul_le_mul_of_nonneg_right (hδAnti hij) (sq_nonneg _))
  have hLim (x : ComplexModel n) (hx : x ∈ B) :
      Tendsto (fun j => q j x + s j) atTop (𝓝 (u x)) := by
    simp_rw [hsEq]
    simpa only [zero_mul, add_zero] using (hp.2.2 x hx).add (hδLim.mul_const (‖x‖ ^ 2))
  have hLim' (x : ComplexModel n) (hx : x ∈ B) : Tendsto (fun j => q j x) atTop (𝓝 (u x)) := by
    simpa only [add_sub_cancel_right, sub_zero] using (hLim x hx).sub hsLim
  let hb := (ballQuadratic_isE0 n).const_mul (show 0 < c + 1 by positivity)
  let M := topMeasure hb.locallyBoundedPsh univ + topMeasure hu.locallyBoundedPsh univ
  have hMass (j : ℕ) : topMeasure (hq j).locallyBoundedPsh univ ≤ M := by
    have hδc : 0 < c + δ j := add_pos hc (hδ₀ j)
    let hδB := (ballQuadratic_isE0 n).const_mul hδc
    rw [topMeasure_total_eq_of_eq_off_compact (hq j).locallyBoundedPsh hδB.locallyBoundedPsh hK hKB
      (fun x hx => hqCollar j x (subset_closure hx.1) hx.2)]
    have hmB : topMeasure hδB.locallyBoundedPsh univ ≤ topMeasure hb.locallyBoundedPsh univ := by
      rw [topMeasure_const_mul (ballQuadratic_isE0 n).locallyBoundedPsh hδc,
        topMeasure_const_mul (ballQuadratic_isE0 n).locallyBoundedPsh (show 0 < c + 1 by positivity),
        Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ hδc.le (add_le_add le_rfl (hδ₁ j)) n)) _
    exact hmB.trans le_self_add
  refine ⟨q, hq, hqSmooth, hqPos, hqLower, hLim', ?_⟩
  apply tendsto_boundedEnergy_of_shifted_decreasing hn hb hu hq hsLim hAnti hLim
    (fun x hx => ?_) hqLower (M := M) (ENNReal.add_lt_top.mpr ⟨hb.finiteMass, hu.finiteMass⟩)
    le_add_self hMass
  exact (mul_le_mul_of_nonpos_right (le_add_of_nonneg_right zero_le_one)
    (ballQuadratic_neg n hx).le).trans (hle x hx)

end KEBall.Cegrell
