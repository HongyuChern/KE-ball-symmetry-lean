import KEBall.MoserTrudingerDirichletDensityLimit
import KEBall.MoserTrudingerGibbsEntropyLimit

/-!
# Identifying a weak Gibbs solution from smooth Dirichlet pairs
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell

variable {n : ℕ}
local notation "ν[" k "]" => Measure.restrict (volume0 k) (unitBall k)

/-- The normalized mean-field equation for a continuous bounded potential,
expressed using its actual Bedford–Taylor top measure. -/
structure IsWeakGibbsSolution (n : ℕ) (γ : ℝ) (v : E n → ℝ) : Prop where
  gamma_pos : 0 < γ
  continuousOn : ContinuousOn v (closedUnitBall n)
  zero_on_sphere : ∀ x ∈ unitSphere n, v x = 0
  memE0 : IsE0 (complexUnitBall n) (v ∘ (complexCoordinates n).symm)
  measure_eq : topMeasure memE0.locallyBoundedPsh =
    Measure.map (complexCoordinates n)
      (ν[n].withDensity (fun x => ENNReal.ofReal (gibbsDensity γ v x)))

/-- Smooth Gibbs pairs with bounded potentials and vanishing entropy gap
give a continuous weak Gibbs solution at the uniform limit of the outputs. -/
theorem exists_weakGibbsLimit_of_vanishing_gap (hn : 0 < n) {γ B : ℝ} (hγ : 0 < γ)
    {u v : ℕ → E n → ℝ} {w : E n → ℝ}
    (hu : ∀ j, ContinuousOn (u j) (closedUnitBall n))
    (hv : ∀ j, SmoothNear (closedUnitBall n) (v j))
    (hv0 : ∀ j x, x ∈ unitSphere n → v j x = 0)
    (hvP : ∀ j x, x ∈ unitBall n → (complexHessian (v j) x).PosDef)
    (hEq : ∀ j x, x ∈ unitBall n → (complexHessian (v j) x).det.re = gibbsDensity γ (u j) x)
    (huB : ∀ j, ∀ᵐ x ∂ν[n], u j x ∈ Icc (-B) 0)
    (hvB : ∀ j, ∀ᵐ x ∂ν[n], v j x ∈ Icc (-B) 0)
    (huL : ∀ᵐ x ∂ν[n], Tendsto (fun j => u j x) atTop (𝓝 (w x)))
    (hGap : Tendsto (fun j => gibbsEntropyGap γ (u j) (v j)) atTop (𝓝 0)) :
    ∃ r : E n → ℝ, TendstoUniformlyOn v r atTop (closedUnitBall n) ∧ IsWeakGibbsSolution n γ r := by
  have huM (j : ℕ) : AEMeasurable (u j) ν[n] :=
    ((hu j).mono ball_subset_closedBall).aemeasurable measurableSet_ball
  have hwM : AEMeasurable w ν[n] := aemeasurable_of_tendsto_metrizable_ae' huM huL
  obtain ⟨hwZ, _, hDB, hDL⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn hγ.le huM hwM huB huL
  have hfC (j : ℕ) : ContinuousOn (gibbsDensity γ (u j)) (closedUnitBall n) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hu j))).div_const _
  obtain ⟨r, hU, hrC, hr0, hrE, hrMeasure⟩ := exists_dirichletLimit_of_ae_of_bounded_density hn
    hv hfC (gibbsDensity_aemeasurable hwM) hv0 hvP hEq hDB hDL
  have hvL : ∀ᵐ x ∂ν[n], Tendsto (fun j => v j x) atTop (𝓝 (r x)) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    exact hU.tendsto_at (ball_subset_closedBall hx)
  have hvC (j : ℕ) : ContinuousOn (v j) (closedUnitBall n) :=
    fun x hx => ((hv j).contDiffAt hx).continuousAt.continuousWithinAt
  have hvM (j : ℕ) : AEMeasurable (v j) ν[n] :=
    ((hvC j).mono ball_subset_closedBall).aemeasurable measurableSet_ball
  have hrM : AEMeasurable r ν[n] := (hrC.mono ball_subset_closedBall).aemeasurable measurableSet_ball
  have hEqGap := tendsto_nhds_unique
    (tendsto_gibbsEntropyGap_of_ae_of_bounded hn hγ.le huM hvM hwM hrM huB hvB huL hvL) hGap
  obtain ⟨hrZ, _, _, _⟩ := gibbsDensity_tendsto_of_ae_of_bounded hn hγ.le hvM hrM hvB hvL
  have hwB : ∀ᵐ x ∂ν[n], w x ∈ Icc (-B) 0 := by
    filter_upwards [huL, ae_all_iff.mpr huB] with x hx h
    exact isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall h)
  have hrB : ∀ᵐ x ∂ν[n], r x ∈ Icc (-B) 0 := by
    filter_upwards [hvL, ae_all_iff.mpr hvB] with x hx h
    exact isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall h)
  have hD := gibbsDensity_ae_eq_of_entropyGap_eq_zero hn hγ.le hwM hrM hwB hrB hwZ hrZ hEqGap
  refine ⟨r, hU, ⟨hγ, hrC, hr0, hrE, hrMeasure.trans ?_⟩⟩
  apply congrArg (Measure.map (complexCoordinates n))
  apply withDensity_congr_ae
  exact hD.mono fun x hx => congrArg ENNReal.ofReal hx

end KEBall.MoserTrudinger
