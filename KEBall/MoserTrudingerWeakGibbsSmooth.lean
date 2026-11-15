import KEBall.MoserTrudingerWeakGibbsMaximizer
import KEBall.MoserTrudingerSubcriticalInduction
import KEBall.MoserTrudingerFiniteEnergy

/-!
# The weak Gibbs equation and the smooth statement of the paper
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger

open BedfordTaylor Cegrell
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn isSmoothPshOn_of_psh)

variable {n : ℕ}

/-- Once a weak Gibbs solution is smooth near the closed ball, positivity
of its density recovers the strict Hessian and the paper's full top-form equation. -/
theorem IsWeakGibbsSolution.isMeanFieldSolution_of_smoothNear (hn : 0 < n)
    {γ : ℝ} {v : E n → ℝ} (h : IsWeakGibbsSolution n γ v)
    (hv : SmoothNear (closedUnitBall n) v) : Paper20261016.IsMeanFieldSolution n γ v := by
  let : NeZero n := ⟨hn.ne'⟩
  let e := complexCoordinates n
  let q := v ∘ e.symm
  let μ := (volume0 n).restrict (unitBall n)
  obtain ⟨U, hU, hsub, hV⟩ := hv
  have hqC : ContDiffOn ℝ ∞ q (complexUnitBall n) := by
    apply hV.comp e.symm.toContinuousLinearEquiv.contDiff.contDiffOn
    intro z hz
    apply hsub
    apply ball_subset_closedBall
    exact mem_ball_zero_iff.mpr ((e.symm.norm_map z).trans_lt (mem_ball_zero_iff.mp hz))
  have hqS := isSmoothPshOn_of_psh hqC h.memE0.psh
  have hCompat : topMeasure h.memE0.locallyBoundedPsh =
      Measure.map e ((d0TopMeasure v).restrict (unitBall n)) := topMeasure_eq_map_d0TopMeasure_unitBall hqS
  have hM : (d0TopMeasure v).restrict (unitBall n) =
      μ.withDensity (fun x => ENNReal.ofReal (gibbsDensity γ v x)) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.map_injective (hCompat.symm.trans h.measure_eq)
  rw [d0TopMeasure_eq_density, restrict_withDensity (show MeasurableSet (unitBall n) from measurableSet_ball)] at hM
  have hDetC : ContinuousOn (fun x => (complexHessian v x).det.re) (unitBall n) :=
    (Complex.continuous_re.comp_continuousOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU hV)).continuousOn).mono
        (ball_subset_closedBall.trans hsub)
  have hDC : ContinuousOn (gibbsDensity γ v) (unitBall n) :=
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul h.continuousOn)).div_const _).mono
      ball_subset_closedBall
  have hAe₀ := (withDensity_eq_iff_of_sigmaFinite (μ := μ)
    (hDetC.aemeasurable measurableSet_ball).ennreal_ofReal
    (hDC.aemeasurable measurableSet_ball).ennreal_ofReal).mp hM
  have hPSD (x : E n) (hx : x ∈ unitBall n) : (complexHessian v x).PosSemidef := by
    have he : e x ∈ complexUnitBall n := by
      change x ∈ e ⁻¹' (complexUnitBall n : Set (ComplexModel n))
      rwa [preimage_complexUnitBall]
    have hxU := hsub (ball_subset_closedBall hx)
    rw [← complexHessian_coordinates (hV.contDiffAt (hU.mem_nhds hxU))]
    exact hqS.2.2 _ he
  have hDpos (x : E n) : 0 < gibbsDensity γ v x :=
    div_pos (Real.exp_pos _) (normalizingIntegral_pos_of_continuousOn hn h.continuousOn γ)
  have hAe : (fun x => (complexHessian v x).det.re) =ᵐ[μ] gibbsDensity γ v := by
    filter_upwards [hAe₀, ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx hxB
    have hDet₀ : 0 ≤ (complexHessian v x).det.re := (RCLike.nonneg_iff.mp (hPSD x hxB).det_nonneg).1
    exact (ENNReal.ofReal_eq_ofReal_iff hDet₀ (hDpos x).le).mp hx
  have hPoint := Measure.eqOn_open_of_ae_eq hAe isOpen_ball hDetC hDC
  have hPD (x : E n) (hx : x ∈ unitBall n) : (complexHessian v x).PosDef := by
    apply (hPSD x hx).posDef_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hz' : (complexHessian v x).det.re = 0 := by rw [hz, Complex.zero_re]
    exact (hDpos x).ne' ((hPoint hx).symm.trans hz')
  apply (Paper20261016.meanField_iff_normalized n γ v).mpr
  apply (isNormalizedSolution_iff_real_density n γ v).mpr
  refine ⟨h.gamma_pos, ⟨U, hU, hsub, hV⟩, hPD, h.zero_on_sphere, ?_⟩
  intro x hx
  rw [posDef_det_eq_ofReal_re (hPD x hx)]
  exact congrArg (fun a : ℝ => (a : ℂ)) (hPoint hx)

/-- Auxiliary Gibbs solvability and smooth regularity of the continuous
weak solutions suffice for the exact subcritical attainment statement. -/
theorem subcriticalSmoothAttainment_of_smoothGibbs_and_regularity (hn : 2 ≤ n)
    (hSolve : ∀ (d : ℕ) (γ : ℝ), 1 < d → 0 < γ → γ < (d + 1 : ℝ) →
      SmoothGibbsDirichletSolvable d γ)
    (hRegular : ∀ {γ : ℝ} {v : E n → ℝ}, γ < (n + 1 : ℝ) → IsWeakGibbsSolution n γ v →
      SmoothNear (closedUnitBall n) v) :
    SubcriticalSmoothAttainment n := by
  intro γ hγ
  let β := (γ + (n + 1 : ℝ)) / 2
  have hγβ : γ < β := by dsimp [β]; linarith only [hγ.2]
  have hβn : β < (n + 1 : ℝ) := by dsimp [β]; linarith only [hγ.2]
  have hn₀ : 0 < n := by omega
  obtain ⟨C, hC⟩ := exists_finiteEnergyFunctional_bound_of_smoothGibbs hSolve n hn₀ β
    (hγ.1.trans hγβ) hβn
  obtain ⟨v, hv, hMax⟩ := exists_weakGibbs_maximizer_of_smoothGibbs hn₀ hγ.1 hγβ
    (fun hw => hC _ hw) (hSolve n γ (by omega) hγ.1 hγ.2)
  refine ⟨v, hv.isMeanFieldSolution_of_smoothNear hn₀ (hRegular hγ.2 hv), fun hu => hMax hu⟩

end KEBall.MoserTrudinger
