import KEBall.MoserTrudingerWeakGibbsPairs

/-! Passing the actual variational value to a uniform smooth limit.
This is an upper-semicontinuity statement for the actual Cegrell energy,
with no smoothness assumption on the limiting weak Gibbs solution. Draft. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell

variable {n : ℕ}
local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)

theorem finiteEnergyFunctional_ge_of_uniform_smooth_limit (hn : 0 < n)
    {γ B m : ℝ} {v : ℕ → E n → ℝ} {r : E n → ℝ}
    (hv : ∀ j, ContDiff ℝ ∞ (v j))
    (hv0 : ∀ j x, x ∈ unitSphere n → v j x = 0)
    (hvP : ∀ j x, x ∈ unitBall n → (complexHessian (v j) x).PosDef)
    (hvB : ∀ j, ∀ᵐ x ∂ν[n], v j x ∈ Icc (-B) 0)
    (hvU : TendstoUniformlyOn v r atTop (closedUnitBall n))
    (hvF : Tendsto (fun j => smoothFunctional γ (v j)) atTop (𝓝 m))
    (hr : IsWeakGibbsSolution n γ r) :
    (m : EReal) ≤ finiteEnergyFunctional γ hr.memE0.isE1 := by
  let e := complexCoordinates n
  let vNear (j : ℕ) : SmoothNear (closedUnitBall n) (v j) :=
    ⟨univ, isOpen_univ, subset_univ _, (hv j).contDiffOn⟩
  have hvE (j : ℕ) : IsE0 (complexUnitBall n) (v j ∘ e.symm) :=
    isE0_onBall_of_smooth_real_model (vNear j) (fun x hx => (hvP j x hx).posSemidef) (hv0 j)
  have hvL : ∀ᵐ x ∂ν[n], Tendsto (fun j => v j x) atTop (𝓝 (r x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    exact hvU.tendsto_at (ball_subset_closedBall hx)
  have hvM (j : ℕ) : AEMeasurable (v j) ν[n] := (hv j).continuous.measurable.aemeasurable
  have hrM : AEMeasurable r ν[n] :=
    (hr.continuousOn.mono ball_subset_closedBall).aemeasurable measurableSet_ball
  obtain ⟨hrZ, hZL, _, _⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn hr.gamma_pos.le
    hvM hrM hvB hvL
  have hLog := ((Real.continuousAt_log (zero_lt_one.trans_le hrZ).ne').tendsto.comp hZL).div_const γ
  have hEnergyL : Tendsto (fun j => (energy (hvE j).isE1).toReal) atTop
      (𝓝 ((Real.log (normalizingIntegral γ r) / γ - m) * (n + 1 : ℝ))) := by
    apply ((hLog.sub hvF).mul_const (n + 1 : ℝ)).congr
    intro j
    rw [energy_realModelPotential hn (vNear j) (hvE j)]
    change (Real.log (normalizingIntegral γ (v j)) / γ - smoothFunctional γ (v j)) *
      (n + 1 : ℝ) = _
    dsimp only [smoothFunctional]
    rw [signedSmoothEnergy_eq isOpen_univ (hv j).contDiffOn (subset_univ _) (hvP j)]
    field_simp
    ring
  have hAe : ∀ᵐ z ∂(volume : Measure (PshLines.FirstPass.ComplexModel n)).restrict (complexUnitBall n),
      Tendsto (fun j => realModelPotential (v j) z) atTop (𝓝 (realModelPotential r z)) := by
    filter_upwards [ae_restrict_mem (complexUnitBall n).isOpen.measurableSet] with z hz
    have hx : e.symm z ∈ unitBall n := by
      apply mem_ball_zero_iff.mpr
      rw [e.symm.norm_map]
      exact mem_ball_zero_iff.mp hz
    exact EReal.tendsto_coe.mpr (hvU.tendsto_at (ball_subset_closedBall hx))
  have hEnergy := energy_toReal_le_of_ae_tendsto hn
    (fun j => (hvE j).isE1) hr.memE0.isE1 hAe hEnergyL
  have hRF : finiteEnergyFunctional γ hr.memE0.isE1 =
      ((Real.log (normalizingIntegral γ r) / γ -
        (energy hr.memE0.isE1).toReal / (n + 1 : ℝ) : ℝ) : EReal) := by
    change finiteEnergyFunctional γ (u := realModelPotential r) hr.memE0.isE1 = _
    unfold finiteEnergyFunctional
    rw [exponentialIntegral_realModelPotential_of_continuousOn hn hr.continuousOn,
      if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (zero_le_one.trans hrZ)]
  rw [hRF, EReal.coe_le_coe_iff]
  have h := (div_le_iff₀ (show 0 < (n + 1 : ℝ) by positivity)).mpr hEnergy
  linarith only [h]

end KEBall.MoserTrudinger
