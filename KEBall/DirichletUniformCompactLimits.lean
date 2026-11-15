import KEBall.DirichletZeroBoundaryApproximation
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Uniform compact limits, continuous nonlinear maps, and normalized ball integrals. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

theorem dirichlet_eventually_mem_open_of_uniform_limit
    {X Y ι : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : ContinuousOn f K)
    {F : ι → X → Y} {l : Filter ι} (hF : TendstoUniformlyOn F f l K)
    {O : Set Y} (hO : IsOpen O) (hMaps : MapsTo f K O) :
    ∀ᶠ i in l, MapsTo (F i) K O := by
  obtain ⟨δ, hδ, hThick⟩ := (hK.image_of_continuousOn hf).exists_thickening_subset_open
    hO (by rintro y ⟨x, hx, rfl⟩; exact hMaps hx)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF δ hδ] with i hi x hx
  apply hThick
  exact mem_thickening_iff.mpr ⟨f x, mem_image_of_mem f hx, by simpa only [dist_comm] using hi x hx⟩

theorem dirichlet_uniform_limit_comp_continuous
    {X F G ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [ProperSpace F] [PseudoMetricSpace G]
    {K : Set X} (hK : IsCompact K) {f : X → F} (hf : ContinuousOn f K)
    {v : ι → X → F} {l : Filter ι} (hv : TendstoUniformlyOn v f l K)
    {g : F → G} (hg : Continuous g) :
    TendstoUniformlyOn (fun i x => g (v i x)) (fun x => g (f x)) l K := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  let R := max B 0 + 1
  have hfB (x : X) (hx : x ∈ K) : ‖f x‖ ≤ R :=
    (hB x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  have hvB : ∀ᶠ i in l, ∀ x ∈ K, v i x ∈ closedBall (0 : F) R := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hv 1 zero_lt_one] with i hi x hx
    apply mem_closedBall_zero_iff.mpr
    calc
      ‖v i x‖ ≤ ‖f x‖ + dist (f x) (v i x) := norm_le_norm_add_const_of_dist_le (le_of_eq (dist_comm _ _))
      _ ≤ B + 1 := add_le_add (hB x hx) (hi x hx).le
      _ ≤ R := add_le_add (le_max_left _ _) le_rfl
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hvB
    (fun x hx => mem_closedBall_zero_iff.mpr (hfB x hx))
    ((isCompact_closedBall (0 : F) R).uniformContinuousOn_of_continuous hg.continuousOn) hv

theorem tendsto_integral_dirichlet_uniform_limit {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n))
    {v : ℕ → E n → ℝ} (hv : ∀ j, ContinuousOn (v j) (closedUnitBall n))
    (hConv : TendstoUniformlyOn v f atTop (closedUnitBall n)) :
    Tendsto (fun j => ∫ x in unitBall n, v j x ∂volume0 n) atTop
      (𝓝 (∫ x in unitBall n, f x ∂volume0 n)) := by
  let μ := (volume0 n).restrict (unitBall n)
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hf
  have hBound : ∀ᶠ j in atTop, ∀ᵐ x ∂μ, ‖v j x‖ ≤ max B 0 + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hConv 1 zero_lt_one] with j hj
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    calc
      ‖v j x‖ ≤ ‖f x‖ + dist (f x) (v j x) := norm_le_norm_add_const_of_dist_le (le_of_eq (dist_comm _ _))
      _ ≤ B + 1 := add_le_add (hB x (ball_subset_closedBall hx))
        (hj x (ball_subset_closedBall hx)).le
      _ ≤ max B 0 + 1 := add_le_add (le_max_left _ _) le_rfl
  apply tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun _ => max B 0 + 1)
    (Eventually.of_forall fun j => ((hv j).mono ball_subset_closedBall).aestronglyMeasurable
      measurableSet_ball) hBound (integrable_const _)
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  exact hConv.tendsto_at (ball_subset_closedBall hx)

end KEBall
