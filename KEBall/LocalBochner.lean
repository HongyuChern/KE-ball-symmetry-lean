import KEBall.LocalMetric
import KEBall.GradientBridge
import KEBall.EquationBasics
import PoincareLib.Geometry.Riemannian.ScalarOperators.Bochner
import PoincareLib.Geometry.Riemannian.ScalarOperators.Locality

/-!
# Local use of the retained Bochner identity

The scalar function is extended by an actual smooth cutoff before applying
the existing geometric-analysis theorem. Locality returns the identity to
the original scalar potential; no global smoothness of it is imposed.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology BigOperators

namespace KEBall

theorem exists_smooth_scalar_extension {n : ℕ} {U : Set (E n)}
    (hU : IsOpen U) {x : E n} (hx : x ∈ U) {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) :
    ∃ f : E n → ℝ, ContDiff ℝ ∞ f ∧ f =ᶠ[𝓝 x] u := by
  obtain ⟨χ, _, hχU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 (2 * n)) x).mem_iff.mp
      (hU.mem_nhds hx)
  have hχ : ContDiff ℝ ∞ (fun y => χ y) := contMDiff_iff_contDiff.mp χ.contMDiff
  refine ⟨fun y => χ y * u y, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact hχ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds (hχU hy)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [hz]
  · filter_upwards [χ.eventuallyEq_one] with y hy
    simp [hy]

theorem metric_gradient_eq_of_eventuallyEq {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {f h : E n → ℝ} {x : E n}
    (heq : f =ᶠ[𝓝 x] h) : D.gradient f x = D.gradient h x := by
  unfold PoincareMT.LeviCivitaData.gradient
  rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]

theorem bochner_on_open {n : ℕ}
    {g : PoincareMT.RiemannianMetric (2 * n) (E n)}
    (D : PoincareMT.LeviCivitaData g) {U : Set (E n)} (hU : IsOpen U)
    {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U) :
    D.laplacian (fun y => g.inner y (D.gradient u y) (D.gradient u y)) x =
      2 * (∑ i, ∑ j, (D.hessian u x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) +
      2 * mvfderiv (𝓡 (2 * n)) (D.laplacian u) x (D.gradient u x) +
      2 * D.ricci x (D.gradient u x) (D.gradient u x) := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_scalar_extension hU hx hu
  have hgrad : D.gradient f =ᶠ[𝓝 x] D.gradient u := by
    filter_upwards [heq.eventually_nhds] with y hy
    exact metric_gradient_eq_of_eventuallyEq D hy
  have hnorm : (fun y => g.inner y (D.gradient f y) (D.gradient f y)) =ᶠ[𝓝 x]
      (fun y => g.inner y (D.gradient u y) (D.gradient u y)) := by
    filter_upwards [hgrad] with y hy
    rw [hy]
  have hlap : D.laplacian f =ᶠ[𝓝 x] D.laplacian u := by
    filter_upwards [heq.eventually_nhds] with y hy
    exact D.laplacian_eq_of_eventuallyEq hy
  have h := D.bochner_identity (contMDiff_iff_contDiff.mpr hf) x
  rw [D.laplacian_eq_of_eventuallyEq hnorm,
    Poincare.mvfderiv_eq_of_eventuallyEq hlap, hgrad.eq_of_nhds] at h
  simpa only [D.hessian_eq_of_eventuallyEq heq] using h

/-- A solution itself, rather than supplied geometric data, constructs all
objects used in this local real Bochner identity and its gradient factor.
The Ricci, scalar-Laplacian and covariant-Hessian complex identifications
are further obligations and are not conclusions of this theorem. -/
theorem IsSolution.exists_local_real_bochner {n : ℕ} {μ : ℝ} {u : E n → ℝ}
    (hu : IsSolution n μ u) {p : E n} (hp : p ∈ unitBall n) :
    ∃ (g : PoincareMT.RiemannianMetric (2 * n) (E n))
      (D : PoincareMT.LeviCivitaData g) (V : Set (E n)),
      IsOpen V ∧ p ∈ V ∧ V ⊆ unitBall n ∧
      (∀ x ∈ V, ∀ v w : E n, g.inner x v w = realMetricForm u x v w) ∧
      (∀ x ∈ V, g.inner x (D.gradient u x) (D.gradient u x) =
        2 * gradientNormSq u x) ∧
      (∀ x ∈ V,
        D.laplacian (fun y => g.inner y (D.gradient u y) (D.gradient u y)) x =
          2 * (∑ i, ∑ j, (D.hessian u x
            (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) +
          2 * mvfderiv (𝓡 (2 * n)) (D.laplacian u) x (D.gradient u x) +
          2 * D.ricci x (D.gradient u x) (D.gradient u x)) := by
  obtain ⟨g, D, V, hV, hpV, hVB, hg⟩ := hu.exists_local_metric hp
  refine ⟨g, D, V, hV, hpV, hVB, hg, ?_, ?_⟩
  · intro x hx
    have hxclosed := Metric.ball_subset_closedBall (hVB hx)
    exact gradient_normSq_eq_twice_complex D
      ((hu.2.1.contDiffAt hxclosed).differentiableAt (by simp))
      (hu.det_isUnit_closedBall hxclosed) (hg x hx)
  · intro x hx
    exact bochner_on_open D Metric.isOpen_ball hu.contDiffOn_ball (hVB hx)

end KEBall
