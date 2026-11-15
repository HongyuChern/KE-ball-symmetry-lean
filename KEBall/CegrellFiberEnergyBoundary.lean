import KEBall.BedfordTaylorFiberEnergySeam
import KEBall.CegrellBoundedEnergy

/-!
# The bounded Cegrell class and zero base trace of unit fibers
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace KEBall.Cegrell

open BedfordTaylor
open PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsLocallyBoundedPshOn)

set_option maxHeartbeats 800000 in
/-- A product potential above the product quadratic barrier has bounded
Cegrell fibers. Their energies in absolute value are bounded by a constant
times the defining function of the base ball. -/
theorem exists_isE0_complexFiberSlice_and_energy_bound {n : ℕ}
    {v : ComplexModel (n + 1) → ℝ} (hv : IsLocallyBoundedPshOn (complexProductBall n 1) v)
    (hv₀ : ∀ x ∈ complexProductBall n 1, v x ≤ 0)
    {A : ℝ} (hA : 0 < A)
    (hBarrier : ∀ x ∈ complexProductBall n 1,
      A * max (‖(complexProductCoordinates n 1 x).1‖ ^ 2 - 1)
        (‖(complexProductCoordinates n 1 x).2‖ ^ 2 - 1) ≤ v x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ unitBall 1,
      IsE0 (complexUnitBall n) (complexFiberSlice v (complexCoordinates 1 w)) ∧
        -(M * (1 - ‖w‖ ^ 2)) ≤ bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w ∧
        bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w ≤ 0 := by
  classical
  let e := complexProductCoordinates n 1
  let c := complexCoordinates 1
  let P := complexProductBall n 1
  let p := gluedMax (P : Set (ComplexModel (n + 1))) v (fun x => A * productFiberQuadratic n 1 x)
  let B₁ := complexUnitBall n
  let B₂ : Opens (ComplexModel n) := ballDomain 0 2
  have hvLower (x : ComplexModel (n + 1)) (hx : x ∈ P) : A * productFiberQuadratic n 1 x ≤ v x :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hA.le).trans (hBarrier x hx)
  have hp : IsLocallyBoundedPshOn (complexProductCylinder n 1) p :=
    locallyBoundedPsh_gluedMax_productFiberQuadratic hv hv₀ hA hvLower
  let hp₂ := IsLocallyBoundedPshOn.mono hp (fiberEnergyCylinder_le_complexProductCylinder 2 le_rfl)
  let S := ENNReal.ofReal (A ^ n) * (ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) *
    (volume : Measure (ComplexModel n)) (ball 0 2))
  have hS : S < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)
  refine ⟨A * S.toReal / (n + 1 : ℝ), by positivity, ?_⟩
  intro w hw
  have hw' : ‖c w‖ < 1 := (c.norm_map w).trans_lt (mem_ball_zero_iff.mp hw)
  let u := complexFiberSlice v (c w)
  let u₂ := complexFiberSlice p (c w)
  let hu := locallyBoundedPsh_complexFiberSlice (R := 1) (ρ := 1) hv hw'
  let hu₂ := locallyBoundedPsh_complexFiberSlice hp₂ hw'
  let h12 : B₁ ≤ B₂ := fun _ hz => ball_subset_ball (by norm_num) hz
  have hCoord (z : ComplexModel n) : e (e.symm (z, c w)) = (z, c w) := e.apply_symm_apply _
  have hzP (z : ComplexModel n) (hz : z ∈ B₁) : e.symm (z, c w) ∈ P := by
    apply mem_complexProductBall.mpr
    change ‖(e (e.symm (z, c w))).1‖ < 1 ∧ ‖(e (e.symm (z, c w))).2‖ < 1
    rw [hCoord z]
    exact ⟨mem_ball_zero_iff.mp hz, hw'⟩
  have hEq : EqOn u₂ u B₁ := by
    intro z hz
    change p (e.symm (z, c w)) = v (e.symm (z, c w))
    simp only [p, gluedMax, if_pos (show e.symm (z, c w) ∈ (P : Set (ComplexModel (n + 1))) from hzP z hz),
      max_eq_left (hvLower _ (hzP z hz))]
  have hOut (z : ComplexModel n) (_ : z ∈ ball (0 : ComplexModel n) 2) (hz : 1 < ‖z‖) :
      u₂ z = A * ‖z‖ ^ 2 + -A := by
    have hnP : e.symm (z, c w) ∉ (P : Set (ComplexModel (n + 1))) := by
      intro h
      have hlt := (mem_complexProductBall.mp h).1
      change ‖(e (e.symm (z, c w))).1‖ < 1 at hlt
      rw [hCoord z] at hlt
      exact (not_lt_of_ge hz.le) hlt
    change p (e.symm (z, c w)) = _
    simp only [p, gluedMax, if_neg hnP, productFiberQuadratic, ← show e = complexProductCoordinates n 1 from rfl,
      hCoord]
    ring
  have hmass₂ : topMeasure hu₂ univ = S :=
    topMeasure_univ_eq_of_quadratic_collar (by norm_num : (1 : ℝ) < 2) hA hu₂ hOut
  have hmass : topMeasure hu univ ≤ S := by
    have h := topMeasure_congr (IsLocallyBoundedPshOn.mono hu₂ h12) hu hEq
    rw [← topMeasure_restrict hu₂ h12] at h
    rw [← h, Measure.restrict_apply_univ, ← hmass₂]
    exact measure_mono (subset_univ _)
  have huFin := hmass.trans_lt hS
  have huBounds (z : ComplexModel n) (hz : z ∈ B₁) :
      A * (‖z‖ ^ 2 - 1) ≤ u z ∧ A * (‖c w‖ ^ 2 - 1) ≤ u z ∧ u z ≤ 0 := by
    have h := hBarrier (e.symm (z, c w)) (hzP z hz)
    change A * max (‖(e (e.symm (z, c w))).1‖ ^ 2 - 1)
      (‖(e (e.symm (z, c w))).2‖ ^ 2 - 1) ≤ u z at h
    rw [hCoord z] at h
    exact ⟨(mul_le_mul_of_nonneg_left (le_max_left _ _) hA.le).trans h,
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hA.le).trans h, hv₀ _ (hzP z hz)⟩
  have huBdd (z : ComplexModel n) (hz : z ∈ B₁) : |u z| ≤ A := by
    rw [abs_of_nonpos (huBounds z hz).2.2]
    linarith only [(huBounds z hz).1, mul_nonneg hA.le (sq_nonneg ‖z‖)]
  have huBoundary (z : ComplexModel n) (hz : z ∈ frontier (B₁ : Set (ComplexModel n))) :
      Tendsto u (𝓝[B₁] z) (𝓝 0) := by
    change z ∈ frontier (ball (0 : ComplexModel n) 1) at hz
    rw [frontier_ball _ one_ne_zero] at hz
    have hz1 := mem_sphere_zero_iff_norm.mp hz
    have hLower : Tendsto (fun z : ComplexModel n => A * (‖z‖ ^ 2 - 1)) (𝓝[B₁] z) (𝓝 0) := by
      have hc₀ : Continuous (fun z : ComplexModel n => A * (‖z‖ ^ 2 - 1)) :=
        continuous_const.mul ((continuous_norm.pow 2).sub continuous_const)
      have he : A * (‖z‖ ^ 2 - 1) = 0 := by rw [hz1]; ring
      rw [← he]
      exact hc₀.continuousAt.continuousWithinAt
    have hB : ∀ᶠ y in 𝓝[B₁] z, y ∈ B₁ := self_mem_nhdsWithin
    exact hLower.squeeze' tendsto_const_nhds
      (hB.mono fun y hy => (huBounds y hy).1)
      (hB.mono fun y hy => (huBounds y hy).2.2)
  refine ⟨⟨hu.1, ⟨A, huBdd⟩, huBoundary, huFin⟩, ?_⟩
  have hConst : A * (‖c w‖ ^ 2 - 1) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos hA.le
    nlinarith only [hw', norm_nonneg (c w)]
  let : IsFiniteMeasure (topMeasure hu) := ⟨huFin⟩
  have huInt := integrable_topMeasure_of_bounded hu hu huFin
    (fun z hz => by simpa only [Real.norm_eq_abs] using huBdd z hz)
  have hLo := integral_mono_ae (integrable_const (A * (‖c w‖ ^ 2 - 1))) huInt
    ((ae_mem_domain_topMeasure hu).mono fun z hz => (huBounds z hz).2.1)
  rw [integral_const, smul_eq_mul, measureReal_def, mul_comm] at hLo
  have hHi := integral_nonpos_of_ae ((ae_mem_domain_topMeasure hu).mono fun z hz => (huBounds z hz).2.2)
  have hLo' := (mul_le_mul_of_nonpos_left (ENNReal.toReal_mono hS.ne hmass) hConst).trans hLo
  have hN : (0 : ℝ) < n + 1 := by positivity
  have h' : ‖complexCoordinates 1 w‖ < 1 := hw'
  simp only [bedfordTaylorFiberEnergy, dif_pos h']
  change -(A * S.toReal / (n + 1 : ℝ) * (1 - ‖w‖ ^ 2)) ≤
      (∫ z, u z ∂topMeasure hu) / (n + 1 : ℝ) ∧
    (∫ z, u z ∂topMeasure hu) / (n + 1 : ℝ) ≤ 0
  refine ⟨?_, div_nonpos_of_nonpos_of_nonneg hHi hN.le⟩
  have hE : -(A * S.toReal / (n + 1 : ℝ) * (1 - ‖w‖ ^ 2)) =
      (A * (‖c w‖ ^ 2 - 1) * S.toReal) / (n + 1 : ℝ) := by
    rw [c.norm_map]
    ring
  rw [hE]
  exact div_le_div_of_nonneg_right hLo' hN.le

/-- The zero trace follows from the product barrier estimate. -/
theorem tendsto_bedfordTaylorFiberEnergy_at_baseSphere {n : ℕ}
    {v : ComplexModel (n + 1) → ℝ} (hv : IsLocallyBoundedPshOn (complexProductBall n 1) v)
    {M : ℝ} (hBound : ∀ w ∈ unitBall 1,
      -(M * (1 - ‖w‖ ^ 2)) ≤ bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w ∧
        bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w ≤ 0)
    {z : E 1} (hz : z ∈ unitSphere 1) :
    Tendsto (bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv) (𝓝[unitBall 1] z) (𝓝 0) := by
  have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have hC : Continuous (fun w : E 1 => -(M * (1 - ‖w‖ ^ 2))) :=
    (continuous_const.mul (continuous_const.sub (continuous_norm.pow 2))).neg
  have hL : Tendsto (fun w : E 1 => -(M * (1 - ‖w‖ ^ 2))) (𝓝[unitBall 1] z) (𝓝 0) := by
    have he : -(M * (1 - ‖z‖ ^ 2)) = 0 := by rw [hz1]; ring
    rw [← he]
    exact hC.continuousAt.continuousWithinAt
  have hB : ∀ᶠ w in 𝓝[unitBall 1] z, w ∈ unitBall 1 := self_mem_nhdsWithin
  exact hL.squeeze' tendsto_const_nhds
    (hB.mono fun w hw => (hBound w hw).1) (hB.mono fun w hw => (hBound w hw).2)

/-- The signed unit-fiber energy is the negative Cegrell energy divided
by the fiber dimension plus one. -/
theorem bedfordTaylorFiberEnergy_eq_neg_boundedEnergy {n : ℕ} (hn : 0 < n)
    {v : ComplexModel (n + 1) → ℝ} (hv : IsLocallyBoundedPshOn (complexProductBall n 1) v)
    {w : E 1} (hw : w ∈ unitBall 1)
    (hE : IsE0 (complexUnitBall n) (complexFiberSlice v (complexCoordinates 1 w))) :
    bedfordTaylorFiberEnergy (R := 1) (ρ := 1) hv w = -(boundedEnergy hE).toReal / (n + 1 : ℝ) := by
  have hw' : ‖complexCoordinates 1 w‖ < 1 :=
    ((complexCoordinates 1).norm_map w).trans_lt (mem_ball_zero_iff.mp hw)
  let u := complexFiberSlice v (complexCoordinates 1 w)
  have hnp := hE.nonpositive_unitBall hn
  have hI : (∫ z, u z ∂topMeasure hE.locallyBoundedPsh) ≤ 0 :=
    integral_nonpos_of_ae ((ae_mem_domain_topMeasure hE.locallyBoundedPsh).mono hnp)
  simp only [bedfordTaylorFiberEnergy, dif_pos hw']
  change (∫ z, u z ∂topMeasure hE.locallyBoundedPsh) / (n + 1 : ℝ) =
    -(crossEnergy hE u).toReal / (n + 1 : ℝ)
  rw [crossEnergy_eq_ofReal hE hE hnp, ENNReal.toReal_ofReal (neg_nonneg.mpr hI), neg_neg]

end KEBall.Cegrell
