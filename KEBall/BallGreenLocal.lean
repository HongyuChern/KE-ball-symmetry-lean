import KEBall.BallGreen
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Localization of the true ball divergence theorem

Only regularity on an open neighborhood of the closed unit ball is required.
An actual smooth bump produces a global compactly supported extension agreeing
with the original field in a neighborhood of every closed-ball point. Thus both
the field and its actual derivatives used by the Green formula agree there.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace KEBall

theorem exists_contDiff_extension_closedUnitBall {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ∞)
    {U : Set (E n)} (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U)
    {V : E n → F} (hV : ContDiffOn ℝ k V U) :
    ∃ W : E n → F, HasCompactSupport W ∧ ContDiff ℝ k W ∧
      ∀ x ∈ closedUnitBall n, W =ᶠ[𝓝 x] V := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : E n) 1).exists_cthickening_subset_open
    hU hsub
  rw [cthickening_closedBall hδ.le zero_le_one] at hδU
  let χ : ContDiffBump (0 : E n) :=
    { rIn := 1 + δ / 2
      rOut := 1 + δ
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let W : E n → F := fun x => χ x • V x
  have hχU : tsupport (χ : E n → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    simpa only [χ, add_comm δ 1] using hδU
  refine ⟨W, χ.hasCompactSupport.smul_right, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact χ.contDiffAt.smul (hV.contDiffAt (hU.mem_nhds hx))
    · have hnotsupp : x ∉ tsupport (χ : E n → ℝ) := fun hx' => hx (hχU hx')
      have heq : W =ᶠ[𝓝 x] (0 : E n → F) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnotsupp] with y hy
        simp only [W, hy, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · intro x hx
    have hxball : x ∈ Metric.ball (0 : E n) χ.rIn := by
      have hnorm : ‖x‖ ≤ 1 := by
        simpa only [closedUnitBall, Metric.mem_closedBall, dist_zero_right] using hx
      change ‖x - 0‖ < 1 + δ / 2
      simp only [sub_zero]
      linarith
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hxball] with y hy
    simp only [W, hy, Pi.one_apply, one_smul]

/-- Green's divergence theorem with exactly neighborhood `C¹` regularity. -/
theorem integral_unitBall_divergence_of_contDiffOn {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U)
    {V : E n → E n} (hV : ContDiffOn ℝ 1 V U) :
    (∫ x in unitBall n, euclideanDivergence V x) =
      ∫ θ : Sphere n, inner ℝ θ.1 (V θ.1) ∂sphereMeasure n := by
  obtain ⟨W, _, hW, hWV⟩ := exists_contDiff_extension_closedUnitBall 1 hU hsub hV
  have hdiv : ∀ x ∈ unitBall n, euclideanDivergence W x = euclideanDivergence V x := by
    intro x hx
    have heq := hWV x (Metric.ball_subset_closedBall hx)
    unfold euclideanDivergence
    apply Finset.sum_congr rfl
    intro i hi
    have heqi : (fun y => W y i) =ᶠ[𝓝 x] (fun y => V y i) :=
      heq.fun_comp (fun z : E n => z i)
    rw [heqi.fderiv_eq]
  have hboundary : ∀ θ : Sphere n, W θ.1 = V θ.1 := by
    intro θ
    exact (hWV θ.1 (Metric.sphere_subset_closedBall θ.2)).eq_of_nhds
  calc
    _ = ∫ x in unitBall n, euclideanDivergence W x :=
      (setIntegral_congr_fun Metric.isOpen_ball.measurableSet hdiv).symm
    _ = ∫ θ : Sphere n, inner ℝ θ.1 (W θ.1) ∂sphereMeasure n :=
      integral_unitBall_divergence hn hW
    _ = _ := integral_congr_ae
      (Eventually.of_forall (fun θ => congrArg (inner ℝ θ.1) (hboundary θ)))

theorem integral_unitBall_divergence_normalized_of_contDiffOn {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hsub : closedUnitBall n ⊆ U)
    {V : E n → E n} (hV : ContDiffOn ℝ 1 V U) :
    (∫ x in unitBall n, euclideanDivergence V x ∂volume0 n) =
      (2 * n : ℝ) * ∫ θ : Sphere n, inner ℝ θ.1 (V θ.1) ∂sphere0 n := by
  rw [setIntegral_volume0, integral_unitBall_divergence_of_contDiffOn hn hU hsub hV,
    integral_sphere0 n hn]
  have hcoeff : (n.factorial : ℝ) / Real.pi ^ n =
      (2 * n : ℝ) * ((n.factorial : ℝ) / ((2 * n : ℝ) * Real.pi ^ n)) := by
    field_simp
  rw [hcoeff, mul_assoc]

#print axioms exists_contDiff_extension_closedUnitBall
#print axioms integral_unitBall_divergence_of_contDiffOn
#print axioms integral_unitBall_divergence_normalized_of_contDiffOn

end KEBall
