import KEBall.MoserTrudingerGibbsClosedC2
import KEBall.DirichletExponentialBoundarySmooth
import KEBall.MoserTrudingerWeakGibbsExtension

/-! The actual Gibbs inverse iteration produces a genuine smooth-near
fixed point with value at least that of any smooth strict initial potential. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff ENNReal Topology

namespace KEBall.MoserTrudinger
open BedfordTaylor Cegrell

theorem exists_smooth_meanField_ge_smooth_subcritical {n : ℕ}
    (hn : 2 ≤ n) {γ : ℝ} (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    ∃ w : E n → ℝ, ∃ hw : Paper20261016.IsMeanFieldSolution n γ w,
      (smoothFunctional γ v : EReal) ≤ finiteEnergyFunctional γ (meanFieldSolution_memE0 hw).isE1 := by
  have hn0 : 0 < n := by omega
  obtain ⟨u, huG, hu, huS, _, huEq, huP, hValue⟩ :=
    exists_closedBall_C2_weakGibbs_ge_smooth_subcritical hn hγ hγn hv hv0 hvP
  have hExp : ∀ x ∈ unitBall n,
      (complexHessian u x).det.re = (normalizingIntegral γ u)⁻¹ * Real.exp ((-γ) * u x) := by
    intro x hx
    rw [huEq x hx]
    simp only [gibbsDensity, div_eq_mul_inv, mul_comm]
  obtain ⟨w, hw, he⟩ := exists_smoothNear_representative_of_exponential_C2_dirichlet_solution
    hn0 hu huS huG.zero_on_sphere huP (-γ) (normalizingIntegral γ u)⁻¹ hExp
  have hwG := huG.congr_closedBall he.symm
  have hwMean := hwG.isMeanFieldSolution_of_smoothNear hn0 hw
  refine ⟨w, hwMean, hValue.trans_eq ?_⟩
  apply finiteEnergyFunctional_congr_onBall hn0
  intro z hz
  apply congrArg (fun t : ℝ => (t : EReal))
  apply he.symm
  apply ball_subset_closedBall
  exact mem_ball_zero_iff.mpr
    (((complexCoordinates n).symm.norm_map z).trans_lt (mem_ball_zero_iff.mp hz))

theorem smoothFunctional_le_normalized_subcritical {n : ℕ}
    (hn : 2 ≤ n) {γ : ℝ} (hγ : 0 < γ) (hγn : γ < (n + 1 : ℝ))
    {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef) :
    (smoothFunctional γ v : EReal) ≤
      finiteEnergyFunctional γ (meanFieldSolution_memE0
        ((Paper20261016.meanField_iff_normalized n γ (normalizedPotential n γ)).mpr
          (normalizedPotential_isNormalizedSolution hn hγ hγn))).isE1 := by
  obtain ⟨w, hw, hValue⟩ := exists_smooth_meanField_ge_smooth_subcritical hn hγ hγn hv hv0 hvP
  have hNorm := (Paper20261016.meanField_iff_normalized n γ w).mp hw
  have he := (hNorm.eqOn_normalizedPotential hn).2
  refine hValue.trans_eq ?_
  apply finiteEnergyFunctional_congr_onBall (by omega : 0 < n)
  intro z hz
  apply congrArg (fun t : ℝ => (t : EReal))
  apply he
  apply ball_subset_closedBall
  exact mem_ball_zero_iff.mpr
    (((complexCoordinates n).symm.norm_map z).trans_lt (mem_ball_zero_iff.mp hz))

end KEBall.MoserTrudinger
