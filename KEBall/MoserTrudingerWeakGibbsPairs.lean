import KEBall.MoserTrudingerWeakGibbsLimit
import KEBall.MoserTrudingerGibbsUniform
import KEBall.MoserTrudingerFiniteEnergyAttainment

/-!
# A weak Gibbs fixed point with a variational lower bound
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)

variable {n : ℕ}
local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)

/-- Two sequences related by smooth Gibbs solves and with the same limiting
functional value yield a weak fixed point attaining at least that value. -/
theorem exists_weakGibbsSolution_ge_of_smoothGibbsPairs (hn : 0 < n)
    {γ M B m : ℝ} (hγ : 0 < γ) {u v : ℕ → E n → ℝ}
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (hv : ∀ j, ContDiff ℝ ∞ (v j))
    (hu0 : ∀ j x, x ∈ unitSphere n → u j x = 0)
    (hv0 : ∀ j x, x ∈ unitSphere n → v j x = 0)
    (huP : ∀ j x, x ∈ unitBall n → (complexHessian (u j) x).PosDef)
    (hvP : ∀ j x, x ∈ unitBall n → (complexHessian (v j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (v j) x).det.re = gibbsDensity γ (u j) x)
    (hM : ∀ j, smoothEnergy (u j) ≤ M)
    (huB : ∀ j, ∀ᵐ x ∂ν[n], u j x ∈ Icc (-B) 0)
    (hvB : ∀ j, ∀ᵐ x ∂ν[n], v j x ∈ Icc (-B) 0)
    (huF : Tendsto (fun j => smoothFunctional γ (u j)) atTop (𝓝 m))
    (hvF : Tendsto (fun j => smoothFunctional γ (v j)) atTop (𝓝 m)) :
    ∃ r : E n → ℝ, ∃ hr : IsWeakGibbsSolution n γ r,
      (m : EReal) ≤ finiteEnergyFunctional γ hr.memE0.isE1 := by
  let e := complexCoordinates n
  let uNear (j : ℕ) : SmoothNear (closedUnitBall n) (u j) := ⟨univ, isOpen_univ, subset_univ _, (hu j).contDiffOn⟩
  let vNear (j : ℕ) : SmoothNear (closedUnitBall n) (v j) := ⟨univ, isOpen_univ, subset_univ _, (hv j).contDiffOn⟩
  have huE (j : ℕ) : IsE0 (complexUnitBall n) (u j ∘ e.symm) :=
    isE0_onBall_of_smooth_real_model (uNear j) (fun x hx => (huP j x hx).posSemidef) (hu0 j)
  have hvE (j : ℕ) : IsE0 (complexUnitBall n) (v j ∘ e.symm) :=
    isE0_onBall_of_smooth_real_model (vNear j) (fun x hx => (hvP j x hx).posSemidef) (hv0 j)
  have hGap (j : ℕ) := gibbsEntropyGap_le_functional_increase hn isOpen_univ (subset_univ _)
    (hu j).contDiffOn (hv j).contDiffOn (hu0 j) (hv0 j) (huP j) (hvP j) hγ (hEq j)
  have hGapL : Tendsto (fun j => gibbsEntropyGap γ (u j) (v j)) atTop (𝓝 0) := by
    have h := (hvF.sub huF).const_mul γ
    rw [sub_self, mul_zero] at h
    exact tendsto_const_nhds.squeeze h (fun j => (hGap j).1) (fun j => (hGap j).2)
  have hMenn (j : ℕ) : energy (huE j).isE1 ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal (energy_lt_top hn (huE j).isE1).ne,
      energy_realModelPotential hn (uNear j) (huE j)]
    exact ENNReal.ofReal_le_ofReal (hM j)
  obtain ⟨p, hp, φ, hφ, _, _, hPL⟩ := exists_subseq_tendsto_of_energy_le hn
    (fun j => (huE j).isE1) ENNReal.ofReal_lt_top hMenn
  let a (j : ℕ) := u (φ j)
  let b (j : ℕ) := v (φ j)
  let w (x : E n) := (p (e x)).toReal
  have haL : ∀ᵐ x ∂ν[n], Tendsto (fun j => a j x) atTop (𝓝 (w x)) := by
    filter_upwards [ae_coordinates_of_ae_complexBall hPL, ae_coordinates_of_ae_complexBall (hp.ae_finite hn)]
      with x hx hFinite
    have h := (EReal.tendsto_toReal hFinite.1 hFinite.2).comp hx
    change Tendsto (fun j => ((u (φ j) (e.symm (e x)) : ℝ) : EReal).toReal) atTop (𝓝 (w x)) at h
    simpa only [e.symm_apply_apply, EReal.toReal_coe, a] using h
  obtain ⟨r, hrU, hr⟩ := exists_weakGibbsLimit_of_vanishing_gap hn hγ
    (u := a) (v := b) (fun j => (hu (φ j)).continuous.continuousOn)
    (fun j => vNear _) (fun j => hv0 _) (fun j => hvP _) (fun j => hEq _)
    (fun j => huB (φ j)) (fun j => hvB (φ j)) haL (hGapL.comp hφ.tendsto_atTop)
  have hbL : ∀ᵐ x ∂ν[n], Tendsto (fun j => b j x) atTop (𝓝 (r x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    exact hrU.tendsto_at (ball_subset_closedBall hx)
  have hbM (j : ℕ) : AEMeasurable (b j) ν[n] := (hv (φ j)).continuous.measurable.aemeasurable
  have hrM : AEMeasurable r ν[n] := (hr.continuousOn.mono ball_subset_closedBall).aemeasurable measurableSet_ball
  obtain ⟨hrZ, hZL, _, _⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn hγ.le hbM hrM (fun j => hvB (φ j)) hbL
  have hLog := ((Real.continuousAt_log (zero_lt_one.trans_le hrZ).ne').tendsto.comp hZL).div_const γ
  have hVal := hvF.comp hφ.tendsto_atTop
  have hEnergyL : Tendsto (fun j => (energy (hvE (φ j)).isE1).toReal) atTop
      (𝓝 ((Real.log (normalizingIntegral γ r) / γ - m) * (n + 1 : ℝ))) := by
    apply ((hLog.sub hVal).mul_const (n + 1 : ℝ)).congr
    intro j
    rw [energy_realModelPotential hn (vNear (φ j)) (hvE (φ j))]
    change (Real.log (normalizingIntegral γ (b j)) / γ - smoothFunctional γ (v (φ j))) * (n + 1 : ℝ) = _
    dsimp only [smoothFunctional, b]
    rw [signedSmoothEnergy_eq isOpen_univ (hv (φ j)).contDiffOn (subset_univ _) (hvP (φ j))]
    field_simp
    ring
  have hAe : ∀ᵐ z ∂(volume : Measure (ComplexModel n)).restrict (complexUnitBall n),
      Tendsto (fun j => realModelPotential (b j) z) atTop (𝓝 (realModelPotential r z)) := by
    filter_upwards [ae_restrict_mem (complexUnitBall n).isOpen.measurableSet] with z hz
    have hx : e.symm z ∈ unitBall n := by
      apply mem_ball_zero_iff.mpr
      rw [e.symm.norm_map]
      exact mem_ball_zero_iff.mp hz
    exact EReal.tendsto_coe.mpr (hrU.tendsto_at (ball_subset_closedBall hx))
  have hEnergy := energy_toReal_le_of_ae_tendsto hn
    (fun j => (hvE (φ j)).isE1) hr.memE0.isE1 hAe hEnergyL
  have hRF : finiteEnergyFunctional γ hr.memE0.isE1 =
      ((Real.log (normalizingIntegral γ r) / γ - (energy hr.memE0.isE1).toReal / (n + 1 : ℝ) : ℝ) : EReal) := by
    change finiteEnergyFunctional γ (u := realModelPotential r) hr.memE0.isE1 = _
    unfold finiteEnergyFunctional
    rw [exponentialIntegral_realModelPotential_of_continuousOn hn hr.continuousOn,
      if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (zero_le_one.trans hrZ)]
  refine ⟨r, hr, ?_⟩
  rw [hRF, EReal.coe_le_coe_iff]
  have h := (div_le_iff₀ (show 0 < (n + 1 : ℝ) by positivity)).mpr hEnergy
  linarith only [h]

end KEBall.MoserTrudinger
