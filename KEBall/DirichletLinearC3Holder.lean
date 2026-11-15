import KEBall.DirichletLinearDifferenceSchauder
import KEBall.DirichletThirdJetDirectionalHolder
import KEBall.DirichletLocalHolderLinearMap

/-! The local C3,alpha gain for an actual linear elliptic equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped NNReal

namespace KEBall

theorem exists_dirichlet_linear_holder_directional_third_jet {n : ℕ} (hn : 0 < n)
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ)
    (Df : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (A : BoundedContinuousFunction (E n) (E n →L[ℝ] E n))
    (DA : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] E n))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    (hf : ∀ x, HasFDerivAt (f : E n → ℝ) (Df x) x)
    (hA : ∀ x, HasFDerivAt (A : E n → E n →L[ℝ] E n) (DA x) x)
    {KDu KH KDf KA KDA α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDuH : HolderWith KDu α (Du : E n → E n →L[ℝ] ℝ))
    (hHH : HolderWith KH α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hDfH : HolderWith KDf α (Df : E n → E n →L[ℝ] ℝ))
    (hAH : HolderWith KA α (A : E n → E n →L[ℝ] E n))
    (hDAH : HolderWith KDA α (DA : E n → E n →L[ℝ] E n →L[ℝ] E n))
    (p v : E n) (R : ℝ≥0) (hR : 0 < R)
    (hPos : (dirichletSchauderMatrix (A p)).PosDef)
    {l : ℝ} (hl : 0 < l) (hEll : ∀ z, l * ‖z‖ ^ 2 ≤ inner ℝ (A p z) z)
    (hEq : ∀ x ∈ closedBall p (2 * R), dirichletContractionCLM n (A x) (Hu x) = f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ≥0,
      ContDiffOn ℝ 1 (fun x => Hu x v) (ball p δ) ∧
      HolderOnWith K α (fderiv ℝ (fun x => Hu x v)) (ball p δ) := by
  obtain ⟨r, hr, _, C, hBound⟩ := exists_dirichlet_uniform_linear_quotient_schauder_bound
    hn u Du Hu f Df A DA hu hDu hf hA hα hα1 hDuH hHH hDfH hAH hDAH p v R hR hPos hl hEll hEq
  obtain ⟨h, hh, hlim, hStep⟩ := exists_dirichlet_admissible_quotient_sequence v R hR
  obtain ⟨hC1, hHolder⟩ := dirichlet_C1_holder_normalized_directional_hessian_of_schauder_bound
    u Du Hu hu hDu hα hHH p v r hh hlim (fun i => hBound (h i) (hh i) (hStep i))
  have hr' : (0 : ℝ) < r := hr
  exact ⟨(r : ℝ) * (1 / 4), by positivity, _,
    dirichlet_C1_holder_of_affine_normalization (fun x => Hu x v) p hr' hr'.ne' hC1 hHolder⟩

theorem exists_dirichlet_local_C3_holder_of_linear_elliptic_jets {n : ℕ} (hn : 0 < n)
    (u : BoundedContinuousFunction (E n) ℝ)
    (Du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Hu : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    (f : BoundedContinuousFunction (E n) ℝ)
    (Df : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (A : BoundedContinuousFunction (E n) (E n →L[ℝ] E n))
    (DA : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] E n))
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (Du x) x)
    (hDu : ∀ x, HasFDerivAt (Du : E n → E n →L[ℝ] ℝ) (Hu x) x)
    (hf : ∀ x, HasFDerivAt (f : E n → ℝ) (Df x) x)
    (hA : ∀ x, HasFDerivAt (A : E n → E n →L[ℝ] E n) (DA x) x)
    {KDu KH KDf KA KDA α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDuH : HolderWith KDu α (Du : E n → E n →L[ℝ] ℝ))
    (hHH : HolderWith KH α (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hDfH : HolderWith KDf α (Df : E n → E n →L[ℝ] ℝ))
    (hAH : HolderWith KA α (A : E n → E n →L[ℝ] E n))
    (hDAH : HolderWith KDA α (DA : E n → E n →L[ℝ] E n →L[ℝ] E n))
    (p : E n) (R : ℝ≥0) (hR : 0 < R)
    (hPos : (dirichletSchauderMatrix (A p)).PosDef)
    {l : ℝ} (hl : 0 < l) (hEll : ∀ z, l * ‖z‖ ^ 2 ≤ inner ℝ (A p z) z)
    (hEq : ∀ x ∈ closedBall p (2 * R), dirichletContractionCLM n (A x) (Hu x) = f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ≥0,
      ContDiffOn ℝ 3 (u : E n → ℝ) (ball p δ) ∧
      HolderOnWith K α (fderiv ℝ (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ)) (ball p δ) := by
  obtain ⟨δ, hδ, K, hHC1, hHolder⟩ := exists_dirichlet_local_C1_holder_clm_of_directions
    (f := (Hu : E n → E n →L[ℝ] E n →L[ℝ] ℝ)) (p := p) (α := α) (fun i =>
      exists_dirichlet_linear_holder_directional_third_jet hn u Du Hu f Df A DA hu hDu hf hA hα hα1
        hDuH hHH hDfH hAH hDAH p (EuclideanSpace.basisFun (Fin (2 * n)) ℝ i) R hR hPos hl hEll hEq)
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
