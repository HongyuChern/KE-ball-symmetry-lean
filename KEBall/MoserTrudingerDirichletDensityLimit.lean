import KEBall.CegrellUniformDirichletLimit
import KEBall.CegrellSmoothFunctional
import KEBall.DirichletComplexABP
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual Dirichlet equation at bounded density limits
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn isSmoothPshOn_of_psh)

variable {n : ℕ}
local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)

private theorem density_cauchy_sq_of_ae_of_bounded (hn : 0 < n) {D : ℝ}
    {p : ℕ → E n → ℝ} {q : E n → ℝ}
    (hp : ∀ j, AEMeasurable (p j) ν[n]) (hq : AEMeasurable q ν[n])
    (hB : ∀ j, ∀ᵐ x ∂ν[n], p j x ∈ Icc 0 D)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun j => p j x) atTop (𝓝 (q x))) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      (∫ x, (p j x - p k x) ^ 2 ∂ν[n]) < ε := by
  let : NeZero n := ⟨hn.ne'⟩
  have hqB : ∀ᵐ x ∂ν[n], q x ∈ Icc 0 D := by
    filter_upwards [hLim, ae_all_iff.mpr hB] with x hx hI
    exact isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall hI)
  have hM (j : ℕ) : AEStronglyMeasurable (fun x => (p j x - q x) ^ 2) ν[n] :=
    ((hp j).sub hq).pow_const 2 |>.aestronglyMeasurable
  have hBound (j : ℕ) : ∀ᵐ x ∂ν[n], ‖(p j x - q x) ^ 2‖ ≤ D ^ 2 := by
    filter_upwards [hB j, hqB] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _) _ 2
    exact abs_le.mpr ⟨by linarith only [hx.1, hy.2], by linarith only [hx.2, hy.1]⟩
  have hInt (j : ℕ) : Integrable (fun x => (p j x - q x) ^ 2) ν[n] :=
    (integrable_const (D ^ 2)).mono' (hM j) (hBound j)
  have hL : Tendsto (fun j => ∫ x, (p j x - q x) ^ 2 ∂ν[n]) atTop (𝓝 0) := by
    have h : Tendsto (fun j => ∫ x, (p j x - q x) ^ 2 ∂ν[n]) atTop (𝓝 (∫ _ : E n, (0 : ℝ) ∂ν[n])) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => D ^ 2) hM (integrable_const _) hBound
      filter_upwards [hLim] with x hx
      simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using (hx.sub (tendsto_const_nhds (x := q x))).pow 2
    simpa only [integral_zero] using h
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hL.eventually_lt_const (show 0 < ε / 4 by positivity))
  refine ⟨N, fun j hj k hk => ?_⟩
  have hI : (∫ x, (p j x - p k x) ^ 2 ∂ν[n]) ≤
      ∫ x, 2 * (p j x - q x) ^ 2 + 2 * (p k x - q x) ^ 2 ∂ν[n] := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
      (((hInt j).const_mul 2).add ((hInt k).const_mul 2))
    exact Eventually.of_forall fun x => by
      change (p j x - p k x) ^ 2 ≤ 2 * (p j x - q x) ^ 2 + 2 * (p k x - q x) ^ 2
      nlinarith only [sq_nonneg (p j x + p k x - 2 * q x)]
  rw [integral_add ((hInt j).const_mul 2) ((hInt k).const_mul 2), integral_const_mul, integral_const_mul] at hI
  exact hI.trans_lt (by linarith only [hN j hj, hN k hk])

/-- A bounded almost-everywhere limit of smooth Dirichlet densities gives a
uniform potential limit with the stated Bedford–Taylor density and zero trace. -/
theorem exists_dirichletLimit_of_ae_of_bounded_density (hn : 0 < n) {D : ℝ}
    {u f : ℕ → E n → ℝ} {p : E n → ℝ}
    (hu : ∀ j, SmoothNear (closedUnitBall n) (u j))
    (hf : ∀ j, ContinuousOn (f j) (closedUnitBall n)) (hp : AEMeasurable p ν[n])
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).det.re = f j x)
    (hB : ∀ j, ∀ᵐ x ∂ν[n], f j x ∈ Icc 0 D)
    (hLim : ∀ᵐ x ∂ν[n], Tendsto (fun j => f j x) atTop (𝓝 (p x))) :
    ∃ v : E n → ℝ, TendstoUniformlyOn u v atTop (closedUnitBall n) ∧
      ContinuousOn v (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      ∃ hv : IsE0 (complexUnitBall n) (v ∘ (complexCoordinates n).symm),
        topMeasure hv.locallyBoundedPsh =
          Measure.map (complexCoordinates n) (ν[n].withDensity (fun x => ENNReal.ofReal (p x))) := by
  let : NeZero n := ⟨hn.ne'⟩
  let e := complexCoordinates n
  let B := complexUnitBall n
  let μ := ν[n]
  have hfM (j : ℕ) : AEMeasurable (f j) μ := ((hf j).mono ball_subset_closedBall).aemeasurable measurableSet_ball
  have hCauchy := density_cauchy_sq_of_ae_of_bounded hn hfM hp hB hLim
  obtain ⟨v, hU, hvC⟩ := exists_uniform_limit_of_dirichlet_density_cauchy hn hu hf hu0 huP hEq hCauchy
  have hv0 (x : E n) (hx : x ∈ unitSphere n) : v x = 0 := by
    have h := (hU.tendsto_at (sphere_subset_closedBall hx)).congr (fun j => hu0 j x hx)
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨v, hU, hvC, hv0, ?_⟩
  have hK := isCompact_closure_complexUnitBall n
  have hClosed : MapsTo e.symm (closure (B : Set (ComplexModel n))) (closedUnitBall n) := by
    rw [show closure (B : Set (ComplexModel n)) = closedBall 0 1 from closure_ball _ one_ne_zero]
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    rw [e.symm.norm_map]
    exact mem_closedBall_zero_iff.mp hz
  have hBall : MapsTo e.symm (B : Set (ComplexModel n)) (unitBall n) := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    rw [e.symm.norm_map]
    exact mem_ball_zero_iff.mp hz
  let q (j : ℕ) := u j ∘ e.symm
  have hq (j : ℕ) : IsE0 B (q j) :=
    isE0_onBall_of_smooth_real_model (hu j) (fun x hx => (huP j x hx).posSemidef) (hu0 j)
  have hqU : TendstoUniformlyOn q (v ∘ e.symm) atTop B := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact (Metric.tendstoUniformlyOn_iff.mp hU ε hε).mono fun j hj z hz =>
      hj (e.symm z) (ball_subset_closedBall (hBall hz))
  have hq0 (z : ComplexModel n) (hz : z ∈ frontier (B : Set (ComplexModel n))) : (v ∘ e.symm) z = 0 := by
    change z ∈ frontier (ball (0 : ComplexModel n) 1) at hz
    rw [frontier_ball _ one_ne_zero] at hz
    exact hv0 _ (mem_sphere_zero_iff_norm.mpr ((e.symm.norm_map z).trans (mem_sphere_zero_iff_norm.mp hz)))
  let ρ (g : E n → ℝ) := μ.withDensity (fun x => ENNReal.ofReal (g x))
  let ζ := Measure.map e (ρ p)
  have hpB : ∀ᵐ x ∂μ, p x ∈ Icc 0 D := by
    filter_upwards [hLim, ae_all_iff.mpr hB] with x hx hI
    exact isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall hI)
  have hMass : ζ univ < ⊤ := by
    rw [show ζ = Measure.map e (ρ p) from rfl,
      Measure.map_apply e.continuous.measurable MeasurableSet.univ, preimage_univ]
    change (μ.withDensity (fun x => ENNReal.ofReal (p x))) univ < ⊤
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    refine (lintegral_mono_ae (hpB.mono fun x hx => ENNReal.ofReal_le_ofReal hx.2)).trans_lt ?_
    simp
  have hSupport : ζ (B : Set (ComplexModel n))ᶜ = 0 := by
    rw [show ζ = Measure.map e (ρ p) from rfl, Measure.map_apply e.continuous.measurable B.isOpen.measurableSet.compl,
      preimage_compl, show e ⁻¹' (B : Set (ComplexModel n)) = unitBall n from preimage_complexUnitBall n]
    apply withDensity_absolutelyContinuous μ _
    change ((volume0 n).restrict (unitBall n)) (unitBall n)ᶜ = 0
    rw [Measure.restrict_apply (show MeasurableSet (unitBall n)ᶜ from measurableSet_ball.compl),
      compl_inter_self, measure_empty]
  have hMj (j : ℕ) : topMeasure (hq j).locallyBoundedPsh = Measure.map e (ρ (f j)) := by
    have hqC : ContDiffOn ℝ ∞ (q j) B := by
      obtain ⟨U, hU', hBU, hS⟩ := hu j
      exact hS.comp e.symm.toContinuousLinearEquiv.contDiff.contDiffOn
        (fun z hz => hBU (ball_subset_closedBall (hBall hz)))
    have hqS := isSmoothPshOn_of_psh hqC (hq j).psh
    rw [show topMeasure (hq j).locallyBoundedPsh = Measure.map e ((d0TopMeasure (u j)).restrict (unitBall n)) from
        topMeasure_eq_map_d0TopMeasure_unitBall hqS, d0TopMeasure_eq_density,
      restrict_withDensity (show MeasurableSet (unitBall n) from measurableSet_ball)]
    apply congrArg (Measure.map e)
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    rw [hEq j x hx]
  apply exists_isE0_of_tendstoUniformlyOn_and_measure hK (fun j => (hq j).locallyBoundedPsh)
    (hvC.comp e.symm.continuous.continuousOn hClosed) hq0 hqU hMass hSupport
  intro φ
  have hTest (g : E n → ℝ) (hg : AEMeasurable g μ) (hg₀ : 0 ≤ᵐ[μ] g) :
      (∫ x, φ x ∂Measure.map e (ρ g)) = ∫ x, g x * φ (e x) ∂μ := by
    rw [integral_map_of_stronglyMeasurable e.continuous.measurable φ.continuous.stronglyMeasurable]
    change (∫ x, φ (e x) ∂μ.withDensity (fun x => ENNReal.ofReal (g x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀ hg.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hg₀] with x hx
    rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  rw [show ζ = Measure.map e (ρ p) from rfl, hTest p hp (hpB.mono fun _ hx => hx.1)]
  simp_rw [hMj, hTest _ (hfM _) ((hB _).mono fun _ hx => hx.1)]
  obtain ⟨K, hK⟩ := (φ.hasCompactSupport.image_of_continuousOn φ.continuous.norm.continuousOn).bddAbove
  have hφ (z : ComplexModel n) : ‖φ z‖ ≤ max 0 K := by
    by_cases hz : z ∈ tsupport φ
    · exact (hK ⟨z, hz, rfl⟩).trans (le_max_right _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_left _ _
  have hD : 0 ≤ D := by
    obtain ⟨x, hx⟩ := (hB 0).exists
    exact hx.1.trans hx.2
  apply tendsto_integral_of_dominated_convergence (fun _ => D * max 0 K)
  · intro j
    exact ((hfM j).mul (φ.continuous.comp e.continuous).aemeasurable).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    filter_upwards [hB j] with x hx
    rw [norm_mul, Real.norm_eq_abs (f j x), abs_of_nonneg hx.1]
    exact mul_le_mul hx.2 (hφ (e x)) (norm_nonneg _) hD
  · filter_upwards [hLim] with x hx
    exact hx.mul_const _

end KEBall.MoserTrudinger
