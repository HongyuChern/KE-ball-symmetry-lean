import KEBall.DirichletBoundaryCapGeometry
import KEBall.DirichletTangentQuotient

/-!
# Propagating a common interior lower bound to a whole boundary cap

Only continuity on the closed ball and second differentiability in the
open ball are required for the function.  The coefficient may be merely
bounded and pointwise elliptic; no boundary second derivatives are assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped ContDiff

namespace KEBall

theorem dirichlet_boundary_quotient_lower_on_cap {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {p₀ : E n} (hp₀ : p₀ ∈ unitSphere n) {R ell Λ κ m a S : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hell : 0 < ell) (hκ : 0 < κ)
    (hm : 0 ≤ m) (ha : 0 ≤ a)
    (hScale : (2 * n : ℝ) * Λ ≤ κ * ell * (R / 32) ^ 2)
    (hSourceScale : S ≤ 2 * a * (2 * n : ℝ) * ell)
    {A : E n → E n →L[ℝ] E n}
    (hSym : ∀ x ∈ unitBall n, (A x).toLinearMap.IsSymmetric)
    (hNorm : ∀ x ∈ unitBall n, ‖A x‖ ≤ Λ)
    (hCoer : ∀ x ∈ unitBall n, ∀ v : E n, ell * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {q : E n → ℝ} (hq : ContinuousOn q (closedUnitBall n))
    (hq2 : ContDiffOn ℝ 2 q (unitBall n))
    (hLq : ∀ x ∈ unitBall n, dirichletBilinearContraction b (A x) (realHessian q x) ≤ S)
    (hNonneg : ∀ x ∈ closedUnitBall n, x ∈ ball p₀ (4 * R) → 0 ≤ q x)
    (hInner : ∀ x ∈ ball (dirichletTangentBallCenter p₀ R) ((R / 2) / 4), m ≤ q x) :
    ∀ x ∈ unitBall n, x ∈ ball p₀ (R / 64) →
      m * κ * R * Real.exp (-κ * R ^ 2) - 4 * a * R ≤
        q x / dirichletBoundaryDistanceProxy x := by
  intro x hx hxCap
  obtain ⟨p, s, hp, hs, hsR, hpDist, hRep⟩ :=
    exists_dirichlet_nearby_boundary_radius hp₀ hR hR1 hx hxCap
  let z : E n := dirichletTangentBallCenter p R
  let K : Set (E n) := closedBall z R \ ball z (R / 32)
  have hK : K ⊆ closedUnitBall n :=
    diff_subset.trans (dirichlet_tangent_closedBall_subset hp hR1)
  have hInt : interior K ⊆ unitBall n := by
    have h := interior_mono hK
    rw [closedUnitBall, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] at h
    exact h
  have hCap : closedBall z R ⊆ ball p₀ (4 * R) :=
    dirichlet_tangent_closedBall_subset_cap hp hR hpDist
  have h := dirichlet_tangent_quotient_lower_of_source_le b hp
    (by positivity : 0 < R / 32) (by linarith : R / 32 < R) hR1 hell hκ hm ha hs
    (by linarith : s ≤ R - R / 32) hScale hSourceScale
    (fun y hy => hSym y (hInt hy)) (fun y hy => hNorm y (hInt hy))
    (fun y hy => hCoer y (hInt hy)) (hq.mono hK) (hq2.mono hInt)
    (fun y hy => hLq y (hInt hy))
    (fun y hy => hInner y (dirichlet_inner_sphere_subset_common_quarter p p₀ hR hR1 hpDist hy))
    (fun y hy => hNonneg y (dirichlet_tangent_closedBall_subset hp hR1 (sphere_subset_closedBall hy))
      (hCap (sphere_subset_closedBall hy)))
  simpa only [← hRep] using h

end KEBall
