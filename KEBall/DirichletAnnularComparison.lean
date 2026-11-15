import KEBall.DirichletAnnularBarrier
import KEBall.DirichletCompactComparison

/-!
# Annular lower comparison with a bounded source

The operator is the actual real Hessian contraction.  Coercivity, symmetry
and the norm bound are hypotheses on its coefficient; no regularity of
that coefficient or boundary differentiability of the solution is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Metric Set
open scoped BigOperators ContDiff

noncomputable section

namespace KEBall

def dirichletHessianContractionLinearMap {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (A : E n →L[ℝ] E n) :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun D := dirichletBilinearContraction b A D
  map_add' D Q := by
    simp only [dirichletBilinearContraction, _root_.add_apply, Finset.sum_add_distrib]
  map_smul' c D := by
    simp only [dirichletBilinearContraction, _root_.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]

theorem dirichletBilinearContraction_nonpos_of_positive {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n →L[ℝ] E n} (hA : A.IsPositive)
    (D : E n →L[ℝ] E n →L[ℝ] ℝ) (hD : ∀ v : E n, D v v ≤ 0) :
    dirichletBilinearContraction b A D ≤ 0 := by
  obtain ⟨m, v, hv⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hA
  apply dirichletBilinearContraction_nonpos_of_frame b D hD (fun _ : Fin m => 1) v
    (fun _ => zero_le_one)
  simpa only [one_smul] using hv

theorem contDiff_dirichletAnnularBarrier {n : ℕ} (κ R : ℝ) (z : E n) :
    ContDiff ℝ ∞ (dirichletAnnularBarrier κ R z) :=
  (contDiff_dirichletRadialExponential κ z).sub contDiff_const

theorem realHessian_dirichletAnnularBarrier {n : ℕ} (κ R : ℝ) (z x : E n) :
    realHessian (dirichletAnnularBarrier κ R z) x =
      realHessian (dirichletRadialExponential κ z) x := by
  have he : fderiv ℝ (dirichletAnnularBarrier κ R z) =
      fderiv ℝ (dirichletRadialExponential κ z) := by
    funext y
    exact fderiv_sub_const _
  rw [realHessian, he]
  rfl

theorem frontier_dirichlet_annulus_subset {n : ℕ} (z : E n) (r R : ℝ) :
    frontier (closedBall z R \ ball z r) ⊆ sphere z R ∪ sphere z r := by
  intro x hx
  have h := frontier_inter_subset (closedBall z R) (ball z r)ᶜ hx
  rcases h with h | h
  · exact Or.inl (frontier_closedBall_subset_sphere h.1)
  · exact Or.inr (frontier_ball_subset_sphere (by simpa only [frontier_compl] using h.2))

/-- Explicit lower growth from the inner sphere, including the source loss.
The condition on `c` is `S ≤ 2 c (2n) ell`, with the project's real dimension. -/
theorem dirichlet_annular_lower_bound_of_source_le {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (z : E n) {r R ell Λ κ m c S : ℝ}
    (hr : 0 < r) (hrR : r < R) (hell : 0 < ell) (hκ : 0 < κ)
    (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hScale : (2 * n : ℝ) * Λ ≤ κ * ell * r ^ 2)
    (hSourceScale : S ≤ 2 * c * (2 * n : ℝ) * ell)
    {A : E n → E n →L[ℝ] E n}
    (hSym : ∀ x ∈ interior (closedBall z R \ ball z r), (A x).toLinearMap.IsSymmetric)
    (hNorm : ∀ x ∈ interior (closedBall z R \ ball z r), ‖A x‖ ≤ Λ)
    (hCoer : ∀ x ∈ interior (closedBall z R \ ball z r), ∀ v : E n,
      ell * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {q : E n → ℝ} (hq : ContinuousOn q (closedBall z R \ ball z r))
    (hq2 : ContDiffOn ℝ 2 q (interior (closedBall z R \ ball z r)))
    (hLq : ∀ x ∈ interior (closedBall z R \ ball z r),
      dirichletBilinearContraction b (A x) (realHessian q x) ≤ S)
    (hInner : ∀ x ∈ sphere z r, m ≤ q x)
    (hOuter : ∀ x ∈ sphere z R, 0 ≤ q x) :
    ∀ x ∈ closedBall z R \ ball z r,
      m * dirichletAnnularBarrier κ R z x + c * (‖x - z‖ ^ 2 - R ^ 2) ≤ q x := by
  let K : Set (E n) := closedBall z R \ ball z r
  let φ := dirichletAnnularBarrier κ R z
  let Q := dirichletQuadraticBarrier R z
  let v : E n → ℝ := m • φ + c • Q
  let F (x : E n) := dirichletHessianContractionLinearMap b (A x)
  have hφ : ContDiff ℝ ∞ φ := contDiff_dirichletAnnularBarrier κ R z
  have hQ : ContDiff ℝ ∞ Q := contDiff_dirichletQuadraticBarrier R z
  have hv : ContDiff ℝ ∞ v := (hφ.const_smul m).add (hQ.const_smul c)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hQ2 : ContDiff ℝ 2 Q := hQ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hK : IsCompact K := (isCompact_closedBall z R).diff isOpen_ball
  have hSign (x : E n) (hx : x ∈ interior K)
      (D : E n →L[ℝ] E n →L[ℝ] ℝ) (hD : ∀ a : E n, D a a ≤ 0) : F x D ≤ 0 := by
    apply dirichletBilinearContraction_nonpos_of_positive b _ D hD
    exact (ContinuousLinearMap.isPositive_iff _).mpr ⟨hSym x hx,
      fun a => (mul_nonneg hell.le (sq_nonneg _)).trans (hCoer x hx a)⟩
  have hBarrier (x : E n) (hx : x ∈ interior K) : 0 < F x (realHessian φ x) := by
    have hxK := interior_subset hx
    have hRadius : r ≤ ‖x - z‖ := by
      exact not_lt.mp (fun hh => hxK.2 (mem_ball.mpr (by simpa only [dist_eq_norm] using hh)))
    change 0 < dirichletBilinearContraction b (A x) (realHessian φ x)
    rw [show φ = dirichletAnnularBarrier κ R z from rfl, realHessian_dirichletAnnularBarrier]
    exact dirichletBilinearContraction_radialExponential_pos b hell hκ hr
      (hNorm x hx) (hCoer x hx) hScale hRadius
  have hLv (x : E n) (hx : x ∈ interior K) : S ≤ F x (realHessian v x) := by
    have hmφ : ContDiffAt ℝ 2 (m • φ) x := hφ2.contDiffAt.const_smul m
    have hcQ : ContDiffAt ℝ 2 (c • Q) x := hQ2.contDiffAt.const_smul c
    rw [show v = m • φ + c • Q from rfl, dirichlet_realHessian_add_C2 hmφ hcQ,
      dirichlet_realHessian_smul_C2 hφ2.contDiffAt m,
      dirichlet_realHessian_smul_C2 hQ2.contDiffAt c,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hTrace := dirichlet_coefficient_trace_lower_bound b (hCoer x hx)
    have hQuad : F x (realHessian Q x) =
        2 * ∑ i : Fin (2 * n), inner ℝ (A x (b i)) (b i) :=
      dirichletBilinearContraction_quadraticBarrier b (A x) R z x
    rw [hQuad]
    have hPos := mul_nonneg hm (hBarrier x hx).le
    have hLow := mul_le_mul_of_nonneg_left hTrace (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc)
    nlinarith only [hPos, hLow, hSourceScale]
  have hBoundary (x : E n) (hx : x ∈ frontier K) : v x ≤ q x := by
    rcases frontier_dirichlet_annulus_subset z r R hx with hR | hrx
    · have hφ0 := dirichletAnnularBarrier_zero_on_sphere κ R z hR
      have hNormR : ‖x - z‖ = R := by simpa only [dist_eq_norm] using mem_sphere.mp hR
      simpa only [v, φ, Q, dirichletQuadraticBarrier, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hφ0, hNormR, sub_self, mul_zero, add_zero] using hOuter x hR
    · have hNormr : ‖x - z‖ = r := by simpa only [dist_eq_norm] using mem_sphere.mp hrx
      have hφ1 := mul_le_mul_of_nonneg_left (dirichletAnnularBarrier_le_one hκ.le R z x) hm
      have hQuad : c * (‖x - z‖ ^ 2 - R ^ 2) ≤ 0 := by
        rw [hNormr]
        apply mul_nonpos_of_nonneg_of_nonpos hc
        have hsq : r ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hr.le (hr.trans hrR).le).mpr hrR.le
        exact sub_nonpos.mpr hsq
      change m * dirichletAnnularBarrier κ R z x + c * (‖x - z‖ ^ 2 - R ^ 2) ≤ q x
      linarith [hInner x hrx]
  exact dirichlet_le_of_linearHessian_le_with_bounded_barrier hK
    hv.continuous.continuousOn hq hφ.continuous.continuousOn
    hv2.contDiffOn hq2 hφ2.contDiffOn F hSign
    (fun x hx => (hLq x hx).trans (hLv x hx)) hBarrier
    (fun x _ => dirichletAnnularBarrier_le_one hκ.le R z x) hBoundary

end KEBall
