import KEBall.BrezisMerleDiscMass
import KEBall.BedfordTaylorTestMeasure

/-!
# Integrability for bounded potentials specified by weak disk tests
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Laplacian Topology

namespace KEBall.BrezisMerle

/-- Integrability against the Laplacian of every smooth interior test
implies local integrability on the open disk. -/
theorem locallyIntegrableOn_of_integrable_laplacian_tests {u : E 1 → ℝ}
    (hTest : ∀ φ : E 1 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ unitBall 1 →
      Integrable (fun x => u x * Δ φ x)) :
    LocallyIntegrableOn u (unitBall 1) volume := by
  apply (locallyIntegrableOn_iff (f := u) (μ := volume)
    (isOpen_ball : IsOpen (unitBall 1)).isLocallyClosed).2
  intro K hK hKc
  let B : Opens (E 1) := ⟨unitBall 1, isOpen_ball⟩
  obtain ⟨r, hr, hKr⟩ := exists_lt_subset_ball hKc.isClosed hK
  obtain ⟨χ, _, hχ⟩ := BedfordTaylor.exists_testFunction_one_on (U := B)
    (isCompact_closedBall (0 : E 1) r) (closedBall_subset_ball hr)
  let q (x : E 1) := ‖x‖ ^ 2 - (1 : ℝ)
  let φ (x : E 1) := χ x * q x
  have hφ : ContDiff ℝ ∞ φ := χ.contDiff.mul ((contDiff_norm_sq ℝ).sub contDiff_const)
  have hφc : HasCompactSupport φ := χ.hasCompactSupport.mul_right
  have hφB : tsupport φ ⊆ unitBall 1 :=
    tsupport_mul_subset_left.trans χ.tsupport_subset
  have hΔ (x : E 1) (hx : x ∈ K) : Δ φ x = 4 := by
    have he : φ =ᶠ[𝓝 x] q := by
      filter_upwards [isOpen_ball.mem_nhds (hKr hx)] with y hy
      change χ y * q y = q y
      rw [hχ (ball_subset_closedBall hy), Pi.one_apply, one_mul]
    rw [(InnerProductSpace.laplacian_congr_nhds he).eq_of_nhds]
    exact laplacian_disc_quadratic x
  have hInt := (hTest φ hφ hφc hφB).restrict (s := K)
  refine (hInt.div_const 4).congr ?_
  filter_upwards [ae_restrict_mem hKc.measurableSet] with x hx
  change u x * Δ φ x / 4 = u x
  rw [hΔ x hx]
  ring

/-- The zero extension of a bounded weak disk potential is integrable. -/
theorem integrable_zeroExtension_of_integrable_laplacian_tests {u : E 1 → ℝ}
    (hTest : ∀ φ : E 1 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ unitBall 1 →
      Integrable (fun x => u x * Δ φ x))
    (hZero : ∀ x ∉ unitBall 1, u x = 0)
    {M : ℝ} (hBound : ∀ x ∈ unitBall 1, -(M * (1 - ‖x‖ ^ 2)) ≤ u x ∧ u x ≤ 0)
    (hM : 0 ≤ M) : Integrable u := by
  have hBound' (x : E 1) (hx : x ∈ unitBall 1) : ‖u x‖ ≤ M := by
    rw [Real.norm_of_nonpos (hBound x hx).2]
    have h := mul_nonneg hM (sq_nonneg ‖x‖)
    linarith only [(hBound x hx).1, h]
  have hMeas := (locallyIntegrableOn_of_integrable_laplacian_tests hTest).aestronglyMeasurable
  have hI : IntegrableOn u (unitBall 1) :=
    (integrableOn_const (C := M) measure_ball_lt_top.ne).mono' hMeas
      ((ae_restrict_mem measurableSet_ball).mono hBound')
  have hi := hI.integrable_indicator (show MeasurableSet (unitBall 1) from measurableSet_ball)
  rwa [indicator_eq_self.mpr (fun x hx => by
    by_contra h
    exact hx (hZero x h))] at hi

end KEBall.BrezisMerle
