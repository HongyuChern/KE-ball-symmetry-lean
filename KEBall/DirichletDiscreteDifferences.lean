import KEBall.DirichletDiscreteGagliardoNirenberg

/-!
# Actual iterated normalized orthogonal differences

These are finite differences of the supplied potential itself. The closed
ball is preserved at every iteration, including for C2 potentials that do
not yet have a smooth extension across the sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace KEBall

noncomputable def dirichletOrthogonalDifference {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (f : E n → ℝ) : E n → ℝ :=
  fun x => (f (R x) - f x) / τ

noncomputable def dirichletIteratedOrthogonalDifference {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) (f : E n → ℝ) : ℕ → E n → ℝ
  | 0 => f
  | k + 1 => dirichletOrthogonalDifference R τ (dirichletIteratedOrthogonalDifference R τ f k)

theorem continuousOn_dirichletOrthogonalDifference {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {f : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n)) :
    ContinuousOn (dirichletOrthogonalDifference R τ f) (closedUnitBall n) :=
  ((continuousOn_dirichlet_orthogonal_comp hf R).sub hf).div_const τ

theorem continuousOn_dirichletIteratedOrthogonalDifference {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {f : E n → ℝ}
    (hf : ContinuousOn f (closedUnitBall n)) (k : ℕ) :
    ContinuousOn (dirichletIteratedOrthogonalDifference R τ f k) (closedUnitBall n) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact continuousOn_dirichletOrthogonalDifference R τ ih

theorem contDiffOn_dirichletOrthogonalDifference {n : ℕ} {m : ℕ∞ω}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {f : E n → ℝ}
    (hf : ContDiffOn ℝ m f (closedUnitBall n)) :
    ContDiffOn ℝ m (dirichletOrthogonalDifference R τ f) (closedUnitBall n) := by
  have hMaps : MapsTo R (closedUnitBall n) (closedUnitBall n) := by
    intro x hx
    simpa only [closedUnitBall, mem_closedBall_zero_iff, R.norm_map] using hx
  exact ((hf.comp R.toContinuousLinearEquiv.contDiff.contDiffOn hMaps).sub hf).div_const τ

theorem contDiffOn_dirichletIteratedOrthogonalDifference {n : ℕ} {m : ℕ∞ω}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {f : E n → ℝ}
    (hf : ContDiffOn ℝ m f (closedUnitBall n)) (k : ℕ) :
    ContDiffOn ℝ m (dirichletIteratedOrthogonalDifference R τ f k) (closedUnitBall n) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact contDiffOn_dirichletOrthogonalDifference R τ ih

theorem dirichletIteratedOrthogonalDifference_zero_on_sphere {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (τ : ℝ) {f : E n → ℝ}
    (hf : ∀ x ∈ unitSphere n, f x = 0) (k : ℕ) :
    ∀ x ∈ unitSphere n, dirichletIteratedOrthogonalDifference R τ f k x = 0 := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    intro x hx
    have hxR : R x ∈ unitSphere n := by
      simpa only [unitSphere, mem_sphere_zero_iff_norm, R.norm_map] using hx
    simp only [dirichletIteratedOrthogonalDifference, dirichletOrthogonalDifference,
      ih x hx, ih (R x) hxR, sub_self, zero_div]

theorem dirichletIteratedOrthogonalDifference_chain {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0) (f : E n → ℝ) (k : ℕ) (x : E n) :
    dirichletIteratedOrthogonalDifference R τ f k (R x) -
        dirichletIteratedOrthogonalDifference R τ f k x =
      τ * dirichletIteratedOrthogonalDifference R τ f (k + 1) x := by
  simp only [dirichletIteratedOrthogonalDifference, dirichletOrthogonalDifference]
  field_simp [hτ]

/-- The discrete interpolation constant is uniform in the nonzero step,
without a differentiability assumption on the actual scalar field. -/
theorem dirichlet_iterated_difference_gagliardo_nirenberg {n k : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) (R : E n ≃ₗᵢ[ℝ] E n) {τ : ℝ} (hτ : τ ≠ 0)
    {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n))
    {B : ℝ} (hB : 0 ≤ B) (hBase : ∀ x ∈ unitBall n, |f x| ≤ B)
    {j : ℕ} (hj : 0 < j) (hjk : j < k) :
    (dirichletLpSize (dirichletIteratedOrthogonalDifference R τ f j) (2 * (k : ℝ) / j)) ^ k ≤
      (4 * (k : ℝ)) ^ (k ^ 3) * B ^ (k - j) *
        (dirichletLpSize (dirichletIteratedOrthogonalDifference R τ f k) 2) ^ j := by
  exact dirichlet_discrete_chain_gagliardo_nirenberg hn hk R hτ
    (dirichletIteratedOrthogonalDifference R τ f)
    (fun i _ => continuousOn_dirichletIteratedOrthogonalDifference R τ hf i)
    (fun i _ x _ => dirichletIteratedOrthogonalDifference_chain R hτ f i x)
    hB hBase hj hjk

end KEBall
