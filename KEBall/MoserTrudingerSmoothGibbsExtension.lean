import KEBall.MoserTrudingerGibbsMassBound
import KEBall.BedfordTaylorTestMeasure
import KEBall.RayODE

/-!
# Extending the auxiliary Dirichlet solution away from the ball
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set TopologicalSpace
open scoped ComplexOrder ContDiff Distributions Topology

namespace KEBall.MoserTrudinger

variable {n : ℕ}

/-- A smooth potential near the closed ball can be extended globally while
preserving its values and derivatives on that ball. -/
theorem exists_global_contDiff_of_smoothNear {v : E n → ℝ}
    (hv : SmoothNear (closedUnitBall n) v) :
    ∃ w : E n → ℝ, ContDiff ℝ ∞ w ∧ ∀ x ∈ closedUnitBall n, w =ᶠ[𝓝 x] v := by
  obtain ⟨U, hU, hKU, hvU⟩ := hv
  let Ω : Opens (E n) := ⟨U, hU⟩
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_closedBall (0 : E n) 1) hU hKU
  obtain ⟨χ, _, hχ⟩ := BedfordTaylor.exists_testFunction_one_on (U := Ω) hVc hVU
  let w (x : E n) := χ x * v x
  refine ⟨w, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact χ.contDiff.contDiffAt.mul (hvU.contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (χ.tsupport_subset h)
      have hZ : w =ᶠ[𝓝 x] (fun _ : E n => (0 : ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
        simp only [w, hy, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hZ
  · intro x hx
    filter_upwards [hV.mem_nhds (hKV hx)] with y hy
    have he : χ y = 1 := hχ (subset_closure hy)
    simp only [w, he, one_mul]

/-- Prescribed positive-density Dirichlet solvability with a smooth
extension near the closed ball supplies the auxiliary Gibbs solver. -/
theorem smoothGibbsDirichletSolvable_of_prescribed_density (hn : 0 < n) (γ : ℝ)
    (hSolve : ∀ f : E n → ℝ, ContDiff ℝ ∞ f → (∀ x ∈ closedUnitBall n, 0 < f x) →
      ∃ v : E n → ℝ, SmoothNear (closedUnitBall n) v ∧
        (∀ x ∈ unitSphere n, v x = 0) ∧ (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
        ∀ x ∈ unitBall n, (complexHessian v x).det.re = f x) :
    SmoothGibbsDirichletSolvable n γ := by
  intro u hu _ _
  have hp : ContDiff ℝ ∞ (gibbsDensity γ u) :=
    ((contDiff_const.mul hu).exp).div_const _
  have hZ := normalizingIntegral_pos_of_continuousOn hn hu.continuous.continuousOn γ
  obtain ⟨v, hv, hv0, hvP, hvEq⟩ :=
    hSolve (gibbsDensity γ u) hp (fun _ _ => div_pos (Real.exp_pos _) hZ)
  obtain ⟨w, hw, hEq⟩ := exists_global_contDiff_of_smoothNear hv
  have hH (x : E n) (hx : x ∈ unitBall n) : complexHessian w x = complexHessian v x :=
    complexHessian_congr_of_eventuallyEq (hEq x (ball_subset_closedBall hx))
  exact ⟨w, hw, fun x hx => (hEq x (sphere_subset_closedBall hx)).self_of_nhds.trans (hv0 x hx),
    fun x hx => hH x hx ▸ hvP x hx,
    fun x hx => by rw [hH x hx]; exact hvEq x hx⟩

end KEBall.MoserTrudinger
