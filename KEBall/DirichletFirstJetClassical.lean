import KEBall.DirichletContinuousAEDerivative
import KEBall.DirichletCovectorReconstruction
import KEBall.DirichletHessianBallBounds

/-!
# Recovering the classical first jet and C² potential from a continuous Hessian representative

The potential and its first jet are the original functions.  Equality with
the continuous second-jet representative is first given almost everywhere,
then upgraded to the actual derivative using Lipschitz mollification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff NNReal Topology

noncomputable section

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem hasFDerivAt_dirichlet_firstJet_of_continuous_ae_hessian {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {s : Set (E n)} (hs : IsOpen s) (hSub : s ⊆ unitBall n)
    {H : E n → E n →L[ℝ] E n →L[ℝ] ℝ} (hH : ContinuousOn H s)
    (he : H =ᵐ[(volume : Measure (E n)).restrict s] fderiv ℝ G)
    {x : E n} (hx : x ∈ s) : HasFDerivAt G (H x) x := by
  obtain ⟨W, hW, hGW⟩ := hG.extend_finite_dimension
  have hNear (y : E n) (hy : y ∈ s) : G =ᶠ[𝓝 y] W := by
    filter_upwards [hs.mem_nhds hy] with z hz
    exact hGW (ball_subset_closedBall (hSub hz))
  have hWdiff := ae_restrict_of_ae (s := s) (hW.ae_differentiableAt (μ := volume))
  have hScalar (j : Fin (2 * n)) : HasFDerivAt (fun y => W y (e[n] j))
      ((ContinuousLinearMap.apply ℝ ℝ (e[n] j)).comp (H x)) x := by
    let B : (E n →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (e[n] j)
    let J : E n → E n →L[ℝ] ℝ := fun y => B.comp (H y)
    let Post : (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] (E n →L[ℝ] ℝ) :=
      ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) ℝ B
    have hJC : ContinuousOn J s := Post.continuous.comp_continuousOn hH
    have hJE : J =ᵐ[(volume : Measure (E n)).restrict s] fderiv ℝ (B ∘ W) := by
      filter_upwards [he, hWdiff, ae_restrict_mem (μ := (volume : Measure (E n))) hs.measurableSet]
        with y hyH hyD hyS
      change B.comp (H y) = fderiv ℝ (B ∘ W) y
      rw [hyH, (hNear y hyS).fderiv_eq]
      exact (B.hasFDerivAt.comp y hyD.hasFDerivAt).fderiv.symm
    exact hasFDerivAt_of_dirichlet_continuous_ae_fderiv (B.lipschitz.comp hW) hs hJC hJE hx
  have hDW : HasFDerivAt W (H x) x := hasFDerivAt_dirichlet_covector_of_basis hScalar
  exact (hNear x hx).hasFDerivAt_iff.mpr hDW

theorem contDiffOn_two_of_dirichlet_continuous_ae_hessian {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {s : Set (E n)} (hs : IsOpen s) (hSub : s ⊆ unitBall n)
    {H : E n → E n →L[ℝ] E n →L[ℝ] ℝ} (hH : ContinuousOn H s)
    (he : H =ᵐ[(volume : Measure (E n)).restrict s] fderiv ℝ G) :
    ContDiffOn ℝ 2 w s := by
  have hClass (x : E n) (hx : x ∈ s) : HasFDerivAt G (H x) x :=
    hasFDerivAt_dirichlet_firstJet_of_continuous_ae_hessian hG hs hSub hH he hx
  have hG1 : ContDiffOn ℝ 1 G s := by
    change ContDiffOn ℝ ((0 : ℕ∞ω) + 1) G s
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn).mpr
    refine ⟨by simp, H, ?_, fun x hx => (hClass x hx).hasFDerivWithinAt⟩
    exact contDiffOn_zero.mpr hH
  change ContDiffOn ℝ ((1 : ℕ∞ω) + 1) w s
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn).mpr
  exact ⟨by simp, G, hG1, fun x hx => (hD x (hSub hx)).hasFDerivWithinAt⟩

end KEBall
