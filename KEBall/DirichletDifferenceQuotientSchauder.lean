import KEBall.DirichletNormalizedDifferenceEquation
import KEBall.DirichletSchauderHessianGauge

/-!
# A uniform Schauder estimate for the actual determinant quotients

The density, potential and their global jets agree with the original
local data on the indicated physical ball.  The normalization radius and
the resulting C2,alpha bound are chosen before the nonzero quotient step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open InnerProductSpace Matrix Metric Set
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem dirichlet_scaled_quotient_nnnorm_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : BoundedContinuousFunction (E n) F}
    {Df : BoundedContinuousFunction (E n) (E n →L[ℝ] F)}
    (hDf : ∀ x, HasFDerivAt (f : E n → F) (Df x) x)
    (p v : E n) (r : ℝ≥0) (k : ℕ) {h : ℝ} (hh : h ≠ 0) :
    ‖dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient f v h) p r k‖₊ ≤
      r ^ k * (‖Df‖₊ * ‖v‖₊) :=
  (nnnorm_dirichletBoundedScaledJet_le _ p r k).trans
    (mul_le_mul_of_nonneg_left (nnnorm_dirichletBoundedDifferenceQuotient_le hDf v hh)
      (bot_le : (0 : ℝ≥0) ≤ _))

theorem holderWith_dirichlet_scaled_quotient_of_holder_derivative {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : BoundedContinuousFunction (E n) F}
    {Df : BoundedContinuousFunction (E n) (E n →L[ℝ] F)} {K α : ℝ≥0}
    (hDf : ∀ x, HasFDerivAt (f : E n → F) (Df x) x)
    (hDHold : HolderWith K α (Df : E n → E n →L[ℝ] F))
    (p v : E n) (r : ℝ≥0) (k : ℕ) {h : ℝ} (hh : h ≠ 0) :
    HolderWith (r ^ k * ((K * ‖v‖₊) * r ^ (α : ℝ))) α
      (dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient f v h) p r k : E n → F) :=
  holderWith_dirichletBoundedScaledJet (f := dirichletBoundedDifferenceQuotient f v h)
    (holderWith_dirichletDifferenceQuotient_of_holder_derivative hDf hDHold v hh) p r k

theorem exists_dirichlet_uniform_normalized_quotient_schauder_bound {n : ℕ} (hn : 0 < n)
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ)
    (Df : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    (hf : ∀ x, HasFDerivAt (f : E n → ℝ) (Df x) x)
    {KDu KH KDf α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDuH : HolderWith KDu α (Du : E n → E n →L[ℝ] ℝ))
    (hHH : HolderWith KH α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hDfH : HolderWith KDf α (Df : E n → E n →L[ℝ] ℝ))
    (p v : E n) (R : ℝ≥0) (hR : 0 < R)
    (hPos : ∀ x ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) x).PosDef)
    (hEq : ∀ x ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) x).det.re = f x) :
    ∃ r : ℝ≥0, 0 < r ∧ r < R ∧ ∃ C : ℝ≥0,
      ∀ h : ℝ, h ≠ 0 → |h| * ‖v‖ ≤ R →
        eContDiffHolderGaugeOn 2 α (closedBall (0 : E n) (1 / 2))
          (dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient u v h) p r 0 : E n → ℝ) ≤ C := by
  have hCH := holderWith_dirichlet_complexHessian_of_bounded_jets u Du Hu hu hDu hHH
  obtain ⟨Ka, l, M, hl, hM, hBounds⟩ :=
    exists_dirichlet_uniform_difference_quotient_cofactor_bounds p v R _ α hα
      (hCH.holderOnWith _) hPos
  let I := {h : ℝ // |h| * ‖v‖ ≤ R}
  let A (s : I) (x : E n) := dirichletMeanCofactor
    (complexHessian (u : E n → ℝ) x) (complexHessian (u : E n → ℝ) (x + s.val • v))
  let M₀ : ℝ≥0 := Real.toNNReal M
  have hM₀ : (M₀ : ℝ) = M := Real.coe_toNNReal _ hM.le
  have hp : p ∈ closedBall p (R : ℝ) := mem_closedBall_self R.coe_nonneg
  have hAH (s : I) : HolderOnWith Ka α (A s) (closedBall p R) := (hBounds s.val s.property).1
  have hANorm (s : I) (x : E n) (hx : x ∈ closedBall p R) : ‖A s x‖ ≤ M₀ := by
    rw [hM₀]
    exact (hBounds s.val s.property).2.1 x hx
  have hASym (s : I) : ∀ a b : E n, inner ℝ (A s p a) b = inner ℝ (A s p b) a :=
    (hBounds s.val s.property).2.2.1 p hp
  have hAEll (s : I) : ∀ a : E n, l * ‖a‖ ^ 2 ≤ inner ℝ (A s p a) a :=
    (hBounds s.val s.property).2.2.2 p hp
  have hAPos (s : I) : (dirichletSchauderMatrix (A s p)).PosDef :=
    dirichletSchauderMatrix_posDef_of_coercive (hASym s) hl (hAEll s)
  obtain ⟨r, hr, hrR, hCoefficients⟩ := exists_dirichlet_uniform_normalized_schauder_family
    p R Ka α M₀ hR hα hα1 A hAH hANorm hAPos hl hAEll
  let L₀ : ℝ≥0 := Real.toNNReal (Real.sqrt M)
  let L₁ : ℝ≥0 := Real.toNNReal (Real.sqrt l)⁻¹
  have hSqrt (s : I) :
      ‖(spdSqrtEquiv (dirichletSchauderMatrix (A s p)) (hAPos s) : E n →L[ℝ] E n)‖₊ ≤ L₀ := by
    change ‖(spdSqrtEquiv (dirichletSchauderMatrix (A s p)) (hAPos s) : E n →L[ℝ] E n)‖ ≤ (L₀ : ℝ)
    rw [show (L₀ : ℝ) = Real.sqrt M from Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    exact norm_dirichletSchauderSqrt_le (hAPos s) hM.le ((hBounds s.val s.property).2.1 p hp)
  have hSqrtInv (s : I) :
      ‖((spdSqrtEquiv (dirichletSchauderMatrix (A s p)) (hAPos s)).symm : E n →L[ℝ] E n)‖₊ ≤ L₁ := by
    change ‖((spdSqrtEquiv (dirichletSchauderMatrix (A s p)) (hAPos s)).symm : E n →L[ℝ] E n)‖ ≤ (L₁ : ℝ)
    rw [show (L₁ : ℝ) = (Real.sqrt l)⁻¹ from Real.coe_toNNReal _ (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact norm_dirichletSchauderSqrt_symm_le (hAPos s) hl (hAEll s)
  let F₀ := r ^ 2 * (‖Df‖₊ * ‖v‖₊)
  let U₀ := r ^ 0 * (‖Du‖₊ * ‖v‖₊)
  let D₀ := r ^ 1 * (‖Hu‖₊ * ‖v‖₊)
  let Kf₀ := r ^ 2 * ((KDf * ‖v‖₊) * r ^ (α : ℝ))
  let Ku₀ := r ^ 0 * ((KDu * ‖v‖₊) * r ^ (α : ℝ))
  let Kdu₀ := r ^ 1 * ((KH * ‖v‖₊) * r ^ (α : ℝ))
  let Ka₀ := Ka * r ^ (α : ℝ)
  let C := 2 * dirichletSchauderEstimateMajorant n α L₀ L₁
    (dirichletUnitBallSourceHolderMajorant n M₀ Ka₀ Kf₀ Kdu₀ Ku₀ F₀ U₀ D₀)
    (dirichletUnitBallSourceSupMajorant n M₀ F₀ U₀ D₀)
    (‖ballCutoffBoundedContinuousFunction (0 : E n)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)‖₊ * U₀)
  refine ⟨r, hr, hrR, C, ?_⟩
  intro h hh hStep
  let s : I := ⟨h, hStep⟩
  obtain ⟨a, haCenter, haOn, haHolder, haNorm, haOsc, haSmall⟩ := hCoefficients s
  have haEq : (fun i j => a i j 0) = dirichletSchauderMatrix (A s p) := by
    ext i j
    exact haCenter i j
  have haPos : Matrix.PosDef (fun i j => a i j 0) := by rw [haEq]; exact hAPos s
  have haL : ‖(spdSqrtEquiv (fun i j => a i j 0) haPos : E n →L[ℝ] E n)‖₊ ≤ L₀ := by
    simpa only [haEq] using! hSqrt s
  have haR : ‖((spdSqrtEquiv (fun i j => a i j 0) haPos).symm : E n →L[ℝ] E n)‖₊ ≤ L₁ := by
    simpa only [haEq] using! hSqrtInv s
  let uh := dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient u v h) p r 0
  let duh := dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient Du v h) p r 1
  let Huh := dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient Hu v h) p r 2
  let fh := dirichletBoundedScaledJet (dirichletBoundedDifferenceQuotient f v h) p r 2
  have huh (x : E n) : HasFDerivAt (uh : E n → ℝ) (duh x) x :=
    hasFDerivAt_dirichletBoundedScaledJet
      (hasFDerivAt_dirichletBoundedDifferenceQuotient hu v h) p r 0 x
  have hduh (x : E n) : HasFDerivAt (duh : E n → E n →L[ℝ] ℝ) (Huh x) x :=
    hasFDerivAt_dirichletBoundedScaledJet
      (hasFDerivAt_dirichletBoundedDifferenceQuotient hDu v h) p r 1 x
  have hsource (x : E n) (hx : x ∈ ball (0 : E n) 1) : variableMatrixLap a Huh x = fh x :=
    dirichlet_normalized_difference_quotient_equation u Du Hu f hu hDu p v R r hrR.le h hStep hEq a
      haOn x (ball_subset_closedBall hx)
  have hfh : HolderWith Kf₀ α (fh : E n → ℝ) :=
    holderWith_dirichlet_scaled_quotient_of_holder_derivative hf hDfH p v r 2 hh
  have huhHold : HolderWith Ku₀ α (uh : E n → ℝ) :=
    holderWith_dirichlet_scaled_quotient_of_holder_derivative hu hDuH p v r 0 hh
  have hduhHold : HolderWith Kdu₀ α (duh : E n → E n →L[ℝ] ℝ) :=
    holderWith_dirichlet_scaled_quotient_of_holder_derivative hDu hHH p v r 1 hh
  have hHuhHold : HolderWith (r ^ 2 * ((‖h⁻¹‖₊ * (KH + KH)) * r ^ (α : ℝ))) α
      (Huh : E n → E n →L[ℝ] E n →L[ℝ] ℝ) :=
    holderWith_dirichletBoundedScaledJet (f := dirichletBoundedDifferenceQuotient Hu v h)
      (holderWith_dirichletDifferenceQuotient hHH v h) p r 2
  have hSmall : spdLaplacianSchauderDefectConst (fun i j => a i j 0) haPos α
      (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), (Ka₀ + Ka₀))
      (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), Ka₀) ≤ 1 / 2 := by
    simpa only [haEq] using! haSmall.le
  exact dirichlet_unitBall_interior_schauder_uniform_estimate hn a haPos fh uh duh Huh
    hα hα1 haL haR huh hduh hsource haHolder haOsc haNorm hfh hduhHold huhHold hHuhHold
    (dirichlet_scaled_quotient_nnnorm_le hf p v r 2 hh)
    (dirichlet_scaled_quotient_nnnorm_le hu p v r 0 hh)
    (dirichlet_scaled_quotient_nnnorm_le hDu p v r 1 hh) hSmall

end KEBall
