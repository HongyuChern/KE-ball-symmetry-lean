import KEBall.DirichletThirdJetDirectionalHolder
import KEBall.DirichletLocalHolderLinearMap

/-! Local C3 regularity with a Holder bound for the full third jet. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped ComplexOrder Matrix.Norms.Elementwise NNReal

namespace KEBall

theorem exists_dirichlet_local_C3_holder_of_positive_determinant_jets {n : ℕ} (hn : 0 < n)
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
    (p : E n) (R : ℝ≥0) (hR : 0 < R)
    (hPos : ∀ x ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) x).PosDef)
    (hEq : ∀ x ∈ closedBall p (2 * R), (complexHessian (u : E n → ℝ) x).det.re = f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ≥0,
      ContDiffOn ℝ 3 (u : E n → ℝ) (ball p δ) ∧
      HolderOnWith K α (fderiv ℝ (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ)) (ball p δ) := by
  obtain ⟨δ, hδ, K, hHC1, hHolder⟩ := exists_dirichlet_local_C1_holder_clm_of_directions
    (f := (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ)) (p := p) (α := α) (fun i =>
      exists_dirichlet_local_holder_directional_third_jet hn u Du Hu f Df hu hDu hf hα hα1
        hDuH hHH hDfH p (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) R hR hPos hEq)
  have hDUEq : fderiv ℝ (Du : E n → E n →L[ℝ] ℝ) = Hu := funext fun x => (hDu x).fderiv
  have hUEq : fderiv ℝ (u : E n → ℝ) = Du := funext fun x => (hu x).fderiv
  have hDC2 : ContDiffOn ℝ 2 (Du : E n → E n →L[ℝ] ℝ) (ball p δ) := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) isOpen_ball).mpr
    refine ⟨fun x _ => (hDu x).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rwa [hDUEq]
  refine ⟨δ, hδ, K, ?_, hHolder⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 2) isOpen_ball).mpr
  refine ⟨fun x _ => (hu x).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rwa [hUEq]

end KEBall
