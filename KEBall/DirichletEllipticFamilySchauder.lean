import KEBall.DirichletDifferenceQuotientSchauder

/-!
# Uniform interior Schauder bounds for an actual elliptic family

The equation is stated using the real bilinear contraction.  The family
may vary both the coefficient and the unknown.  A common radius is chosen
using only the coefficient Holder bound and the ellipticity constants.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix Metric Set
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped NNReal

namespace KEBall

theorem exists_dirichlet_uniform_schauder_bound_for_elliptic_family {n : ℕ} (hn : 0 < n)
    {I : Type*} (u : I → BoundedContinuousFunction (E n) ℝ)
    (Du : I → BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : I → BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : I → BoundedContinuousFunction (E n) ℝ)
    (A : I → E n → E n →L[ℝ] E n)
    (hu : ∀ i x, HasFDerivAt (u i : E n → ℝ) (Du i x) x)
    (hDu : ∀ i x, HasFDerivAt (Du i : E n → E n →L[ℝ] ℝ) (Hu i x) x)
    (p : E n) (R Ka M Ku Kdu Kf U D F α : ℝ≥0)
    (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hAH : ∀ i, HolderOnWith Ka α (A i) (closedBall p R))
    (hANorm : ∀ i x, x ∈ closedBall p R → ‖A i x‖ ≤ M)
    (hAPos : ∀ i, (dirichletSchauderMatrix (A i p)).PosDef)
    {l : ℝ} (hl : 0 < l)
    (hAEll : ∀ i v, l * ‖v‖ ^ 2 ≤ inner ℝ (A i p v) v)
    (hSource : ∀ i x, x ∈ ball p R →
      dirichletBilinearContraction (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) (A i x) (Hu i x) = f i x)
    (huHold : ∀ i, HolderWith Ku α (u i : E n → ℝ))
    (hDuHold : ∀ i, HolderWith Kdu α (Du i : E n → E n →L[ℝ] ℝ))
    (hHuHold : ∀ i, ∃ KH : ℝ≥0, HolderWith KH α (Hu i : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hfHold : ∀ i, HolderWith Kf α (f i : E n → ℝ))
    (huNorm : ∀ i, ‖u i‖₊ ≤ U) (hDuNorm : ∀ i, ‖Du i‖₊ ≤ D) (hfNorm : ∀ i, ‖f i‖₊ ≤ F) :
    ∃ r : ℝ≥0, 0 < r ∧ r < R ∧ ∃ C : ℝ≥0, ∀ i,
      eContDiffHolderGaugeOn 2 α (closedBall (0 : E n) (1 / 2))
        (dirichletBoundedScaledJet (u i) p r 0 : E n → ℝ) ≤ C := by
  obtain ⟨r, hr, hrR, hCoefficients⟩ := exists_dirichlet_uniform_normalized_schauder_family
    p R Ka α M hR hα hα1 A hAH hANorm hAPos hl hAEll
  let L₀ : ℝ≥0 := Real.toNNReal (Real.sqrt M)
  let L₁ : ℝ≥0 := Real.toNNReal (Real.sqrt l)⁻¹
  have hp : p ∈ closedBall p (R : ℝ) := mem_closedBall_self R.coe_nonneg
  have hSqrt (i : I) :
      ‖(spdSqrtEquiv (dirichletSchauderMatrix (A i p)) (hAPos i) : E n →L[ℝ] E n)‖₊ ≤ L₀ := by
    change ‖(spdSqrtEquiv (dirichletSchauderMatrix (A i p)) (hAPos i) : E n →L[ℝ] E n)‖ ≤ (L₀ : ℝ)
    rw [show (L₀ : ℝ) = Real.sqrt M from Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    exact norm_dirichletSchauderSqrt_le (hAPos i) M.coe_nonneg (hANorm i p hp)
  have hSqrtInv (i : I) :
      ‖((spdSqrtEquiv (dirichletSchauderMatrix (A i p)) (hAPos i)).symm : E n →L[ℝ] E n)‖₊ ≤ L₁ := by
    change ‖((spdSqrtEquiv (dirichletSchauderMatrix (A i p)) (hAPos i)).symm : E n →L[ℝ] E n)‖ ≤ (L₁ : ℝ)
    rw [show (L₁ : ℝ) = (Real.sqrt l)⁻¹ from Real.coe_toNNReal _ (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact norm_dirichletSchauderSqrt_symm_le (hAPos i) hl (hAEll i)
  let F₀ := r ^ 2 * F
  let U₀ := r ^ 0 * U
  let D₀ := r ^ 1 * D
  let Kf₀ := r ^ 2 * (Kf * r ^ (α : ℝ))
  let Ku₀ := r ^ 0 * (Ku * r ^ (α : ℝ))
  let Kdu₀ := r ^ 1 * (Kdu * r ^ (α : ℝ))
  let Ka₀ := Ka * r ^ (α : ℝ)
  let C := 2 * dirichletSchauderEstimateMajorant n α L₀ L₁
    (dirichletUnitBallSourceHolderMajorant n M Ka₀ Kf₀ Kdu₀ Ku₀ F₀ U₀ D₀)
    (dirichletUnitBallSourceSupMajorant n M F₀ U₀ D₀)
    (‖ballCutoffBoundedContinuousFunction (0 : E n)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)‖₊ * U₀)
  refine ⟨r, hr, hrR, C, ?_⟩
  intro i
  obtain ⟨a, haCenter, haOn, haHolder, haNorm, haOsc, haSmall⟩ := hCoefficients i
  have haEq : (fun j k => a j k 0) = dirichletSchauderMatrix (A i p) := by
    ext j k
    exact haCenter j k
  have haPos : Matrix.PosDef (fun j k => a j k 0) := by rw [haEq]; exact hAPos i
  have haL : ‖(spdSqrtEquiv (fun j k => a j k 0) haPos : E n →L[ℝ] E n)‖₊ ≤ L₀ := by
    simpa only [haEq] using! hSqrt i
  have haR : ‖((spdSqrtEquiv (fun j k => a j k 0) haPos).symm : E n →L[ℝ] E n)‖₊ ≤ L₁ := by
    simpa only [haEq] using! hSqrtInv i
  let ui := dirichletBoundedScaledJet (u i) p r 0
  let dui := dirichletBoundedScaledJet (Du i) p r 1
  let Hui := dirichletBoundedScaledJet (Hu i) p r 2
  let fi := dirichletBoundedScaledJet (f i) p r 2
  have hui (x : E n) : HasFDerivAt (ui : E n → ℝ) (dui x) x :=
    hasFDerivAt_dirichletBoundedScaledJet (hu i) p r 0 x
  have hdui (x : E n) : HasFDerivAt (dui : E n → E n →L[ℝ] ℝ) (Hui x) x :=
    hasFDerivAt_dirichletBoundedScaledJet (hDu i) p r 1 x
  have hsource (x : E n) (hx : x ∈ ball (0 : E n) 1) : variableMatrixLap a Hui x = fi x := by
    have hz : p + (r : ℝ) • x ∈ ball p R := by
      rw [mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg r.coe_nonneg]
      exact ((mul_le_of_le_one_right r.coe_nonneg (mem_ball_zero_iff.mp hx).le)).trans_lt hrR
    rw [dirichlet_variableMatrixLap_eq_contraction a _ _
      (fun j k => haOn j k x (ball_subset_closedBall hx)),
      dirichletBoundedScaledJet_apply, dirichletBilinearContraction_smul_right,
      dirichletBoundedScaledJet_apply, smul_eq_mul, hSource i _ hz]
  obtain ⟨KH, hKH⟩ := hHuHold i
  have hSmall : spdLaplacianSchauderDefectConst (fun j k => a j k 0) haPos α
      (∑ _j : Fin (2 * n), ∑ _k : Fin (2 * n), (Ka₀ + Ka₀))
      (∑ _j : Fin (2 * n), ∑ _k : Fin (2 * n), Ka₀) ≤ 1 / 2 := by
    simpa only [haEq] using! haSmall.le
  apply dirichlet_unitBall_interior_schauder_uniform_estimate hn a haPos fi ui dui Hui
    hα hα1 haL haR hui hdui hsource haHolder haOsc haNorm
    (holderWith_dirichletBoundedScaledJet (hfHold i) p r 2)
    (holderWith_dirichletBoundedScaledJet (hDuHold i) p r 1)
    (holderWith_dirichletBoundedScaledJet (huHold i) p r 0)
    (holderWith_dirichletBoundedScaledJet hKH p r 2)
    _ _ _ hSmall
  · exact (nnnorm_dirichletBoundedScaledJet_le _ p r 2).trans
      (mul_le_mul_of_nonneg_left (hfNorm i) (bot_le : (0 : ℝ≥0) ≤ _))
  · exact (nnnorm_dirichletBoundedScaledJet_le _ p r 0).trans
      (mul_le_mul_of_nonneg_left (huNorm i) (bot_le : (0 : ℝ≥0) ≤ _))
  · exact (nnnorm_dirichletBoundedScaledJet_le _ p r 1).trans
      (mul_le_mul_of_nonneg_left (hDuNorm i) (bot_le : (0 : ℝ≥0) ≤ _))

end KEBall
