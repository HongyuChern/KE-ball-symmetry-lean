import PoincareLib.Geometry.Riemannian.ScalarOperators.Bochner

/-! A genuine upstream reuse test. This is a real Riemannian corollary;
it does not construct the complex Hessian metric or prove the Kahler bridge. -/
set_option autoImplicit false
open scoped Manifold ContDiff Bundle BigOperators
open Bundle

namespace KEBallProbe
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : PoincareMT.RiemannianMetric n M}

theorem bochner_einstein_const_laplacian
    (D : PoincareMT.LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {c lam : ℝ}
    (hLap : D.laplacian f = fun _ => c)
    (hRic : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      D.ricci x v w = lam * g.inner x v w) (x : M) :
    D.laplacian (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x =
      2 * (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) +
      2 * lam * g.inner x (D.gradient f x) (D.gradient f x) := by
  rw [D.bochner_identity hf, hLap, hRic]
  simp only [mvfderiv_const, zero_apply, mul_zero, add_zero]
  ring

/-- Conditional normalization check. The three real/complex identifications
below are explicit hypotheses, NOT already formalized geometric facts. -/
theorem complex_bochner_of_real_identifications
    (D : PoincareMT.LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hLap : D.laplacian f = fun _ => c)
    (hRic : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      D.ricci x v w = (1 : ℝ) * g.inner x v w)
    (x : M) (q s m lq : ℝ)
    (hNorm : g.inner x (D.gradient f x) (D.gradient f x) = 2 * q)
    (hHess : (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) = 2 * (m + s))
    (hDelta : D.laplacian (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x
      = 4 * lq) :
    lq = m + q + s := by
  have h := bochner_einstein_const_laplacian D hf hLap hRic x
  rw [hNorm, hHess, hDelta] at h
  linarith

#print axioms bochner_einstein_const_laplacian
#print axioms complex_bochner_of_real_identifications
end KEBallProbe
