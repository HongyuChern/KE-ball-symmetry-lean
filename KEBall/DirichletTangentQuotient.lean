import KEBall.DirichletTangentBall

/-!
# Quantitative boundary quotient improvement from a tangent annulus

The annular comparison is evaluated on the inward radius.  The division is
by the positive smooth proxy `(1 - |x|^2)/2`, and the source loss is retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped ContDiff

namespace KEBall

theorem dirichlet_tangent_barrier_quotient_lower {n : ℕ}
    {p : E n} (hp : p ∈ unitSphere n) {R s κ m c : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hs : 0 < s) (hsR : s ≤ R)
    (hκ : 0 ≤ κ) (hm : 0 ≤ m) (hc : 0 ≤ c) {q : E n → ℝ}
    (hCompare : m * dirichletAnnularBarrier κ R (dirichletTangentBallCenter p R) ((1 - s) • p) +
      c * (‖(1 - s) • p - dirichletTangentBallCenter p R‖ ^ 2 - R ^ 2) ≤ q ((1 - s) • p)) :
    m * κ * R * Real.exp (-κ * R ^ 2) - 4 * c * R ≤
      q ((1 - s) • p) / dirichletBoundaryDistanceProxy ((1 - s) • p) := by
  let x : E n := (1 - s) • p
  let z : E n := dirichletTangentBallCenter p R
  let ρ : ℝ := dirichletBoundaryDistanceProxy x
  let a : ℝ := m * κ * R * Real.exp (-κ * R ^ 2)
  have hxNorm : ‖x‖ = 1 - s := norm_dirichlet_radial_point hp (hsR.trans hR1)
  have hx : x ∈ unitBall n := mem_ball_zero_iff.mpr (by rw [hxNorm]; linarith)
  have hρ : 0 < ρ := dirichletBoundaryDistanceProxy_pos hx
  have hρBounds : s / 2 ≤ ρ ∧ ρ ≤ s := by
    simpa only [hxNorm, sub_sub_cancel] using
      dirichletBoundaryDistanceProxy_bounds (ball_subset_closedBall hx)
  have hNorm : ‖x - z‖ = R - s := by
    simpa only [dist_eq_norm] using dist_dirichlet_radial_point_tangent_center hp hsR
  have hBar : κ * R * Real.exp (-κ * R ^ 2) * s ≤ dirichletAnnularBarrier κ R z x := by
    have h := dirichletAnnularBarrier_lower_distance (R := R) hκ z x (by rw [hNorm]; linarith)
    simpa only [hNorm, sub_sub_cancel] using h
  have hmBar : a * s ≤ m * dirichletAnnularBarrier κ R z x := by
    calc
      a * s = m * (κ * R * Real.exp (-κ * R ^ 2) * s) := by dsimp [a]; ring
      _ ≤ m * dirichletAnnularBarrier κ R z x := mul_le_mul_of_nonneg_left hBar hm
  have hQuad : -(2 * c * R * s) ≤ c * (‖x - z‖ ^ 2 - R ^ 2) := by
    rw [hNorm]
    nlinarith only [mul_nonneg hc (sq_nonneg s)]
  have hq : a * s - 2 * c * R * s ≤ q x := by
    change m * dirichletAnnularBarrier κ R z x + c * (‖x - z‖ ^ 2 - R ^ 2) ≤ q x at hCompare
    linarith only [hmBar, hQuad, hCompare]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hMain := mul_le_mul_of_nonneg_left hρBounds.2 ha
  have hLoss := mul_le_mul_of_nonneg_left
    (show s ≤ 2 * ρ by linarith [hρBounds.1]) (by positivity : 0 ≤ 2 * c * R)
  apply (le_div_iff₀ hρ).mpr
  change (a - 4 * c * R) * ρ ≤ q x
  nlinarith only [hMain, hLoss, hq]

/-- The actual inhomogeneous cofactor-style comparison yields a boundary
quotient lower bound along each inward normal radius. -/
theorem dirichlet_tangent_quotient_lower_of_source_le {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {p : E n} (hp : p ∈ unitSphere n) {r R ell Λ κ m c S s : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR1 : R ≤ 1) (hell : 0 < ell) (hκ : 0 < κ)
    (hm : 0 ≤ m) (hc : 0 ≤ c) (hs : 0 < s) (hsr : s ≤ R - r)
    (hScale : (2 * n : ℝ) * Λ ≤ κ * ell * r ^ 2)
    (hSourceScale : S ≤ 2 * c * (2 * n : ℝ) * ell)
    {A : E n → E n →L[ℝ] E n}
    (hSym : ∀ x ∈ interior (closedBall (dirichletTangentBallCenter p R) R \
      ball (dirichletTangentBallCenter p R) r), (A x).toLinearMap.IsSymmetric)
    (hNorm : ∀ x ∈ interior (closedBall (dirichletTangentBallCenter p R) R \
      ball (dirichletTangentBallCenter p R) r), ‖A x‖ ≤ Λ)
    (hCoer : ∀ x ∈ interior (closedBall (dirichletTangentBallCenter p R) R \
      ball (dirichletTangentBallCenter p R) r), ∀ v : E n,
      ell * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {q : E n → ℝ}
    (hq : ContinuousOn q (closedBall (dirichletTangentBallCenter p R) R \
      ball (dirichletTangentBallCenter p R) r))
    (hq2 : ContDiffOn ℝ 2 q (interior (closedBall (dirichletTangentBallCenter p R) R \
      ball (dirichletTangentBallCenter p R) r)))
    (hLq : ∀ x ∈ interior (closedBall (dirichletTangentBallCenter p R) R \
      ball (dirichletTangentBallCenter p R) r),
      dirichletBilinearContraction b (A x) (realHessian q x) ≤ S)
    (hInner : ∀ x ∈ sphere (dirichletTangentBallCenter p R) r, m ≤ q x)
    (hOuter : ∀ x ∈ sphere (dirichletTangentBallCenter p R) R, 0 ≤ q x) :
    m * κ * R * Real.exp (-κ * R ^ 2) - 4 * c * R ≤
      q ((1 - s) • p) / dirichletBoundaryDistanceProxy ((1 - s) • p) := by
  have hsR : s ≤ R := by linarith
  apply dirichlet_tangent_barrier_quotient_lower hp (hr.trans hrR) hR1 hs hsR hκ.le hm hc
  apply dirichlet_annular_lower_bound_of_source_le b (dirichletTangentBallCenter p R)
    hr hrR hell hκ hm hc hScale hSourceScale hSym hNorm hCoer hq hq2 hLq hInner hOuter
  constructor
  · apply mem_closedBall.mpr
    rw [dist_dirichlet_radial_point_tangent_center hp hsR]
    linarith
  · intro h
    have hd := mem_ball.mp h
    rw [dist_dirichlet_radial_point_tangent_center hp hsR] at hd
    linarith

end KEBall
