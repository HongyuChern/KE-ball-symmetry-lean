import KEBall.DirichletDifferenceQuotientLimit
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Passing a uniform difference-quotient derivative estimate to C3 regularity

The limit is identified with the actual Hessian applied to a direction.
The remaining analytic input is explicitly the uniform Holder estimate
for the derivative of each first-jet quotient, supplied by Schauder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Metric Set
open DifferentialGeometry.Analysis.Schauder
open scoped NNReal Topology

namespace KEBall

theorem dirichlet_C1_limit_of_uniform_holder_derivatives {n : ℕ} {F I : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {l : Filter I} [NeBot l] {f : I → E n → F} {g : E n → F} {C α : ℝ≥0}
    {p : E n} {r R : ℝ} (hrR : r < R) (hα : 0 < α)
    (hf : ∀ i, ∀ x ∈ ball p R, DifferentiableAt ℝ (f i) x)
    (hDf : ∀ i, HolderOnWith C α (fderiv ℝ (f i)) (ball p R))
    (hlim : TendstoUniformlyOn f g l (ball p R)) :
    ContDiffOn ℝ 1 g (ball p r) ∧ HolderOnWith C α (fderiv ℝ g) (ball p r) := by
  have hSub : ball p r ⊆ ball p R := ball_subset_ball hrR.le
  have hgD := differentiableOn_ball_of_tendstoUniformlyOn_of_holder_fderiv hα hf hDf hlim
  have hDlim := tendstoUniformlyOn_fderiv_ball_of_holderOnWith hrR hα hf hDf hlim
  have hHolder : HolderOnWith C α (fderiv ℝ g) (ball p r) :=
    holderOnWith_of_tendsto (Eventually.of_forall fun i => (hDf i).mono hSub)
      (fun _ hx => hDlim.tendsto_at hx)
  refine ⟨?_, hHolder⟩
  exact (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) isOpen_ball).mpr
    ⟨hgD.mono hSub, by simp, contDiffOn_zero.mpr (hHolder.continuousOn hα)⟩

theorem dirichlet_C1_directional_derivative_of_difference_quotient_estimate {n : ℕ}
    {F I : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E n → F} {D : E n → E n →L[ℝ] F} {K C α : ℝ≥0}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hHolder : HolderWith K α D) (hα : 0 < α)
    (v : E n) {l : Filter I} [NeBot l] {h : I → ℝ}
    (hh : ∀ i, h i ≠ 0) (hlim : Tendsto h l (𝓝 0))
    {p : E n} {r R : ℝ} (hrR : r < R)
    (hEstimate : ∀ i, HolderOnWith C α
      (fderiv ℝ (dirichletDifferenceQuotient f v (h i))) (ball p R)) :
    ContDiffOn ℝ 1 (fun x => D x v) (ball p r) ∧
      HolderOnWith C α (fderiv ℝ (fun x => D x v)) (ball p r) := by
  apply dirichlet_C1_limit_of_uniform_holder_derivatives (l := l)
    (f := fun i => dirichletDifferenceQuotient f v (h i)) (g := fun x => D x v) hrR hα
    (fun i x _ => (hasFDerivAt_dirichletDifferenceQuotient v (h i) x (hD x) (hD _)).differentiableAt)
    hEstimate
  exact (tendstoUniformly_dirichletDifferenceQuotient hD hHolder hα v hh hlim).tendstoUniformlyOn

theorem dirichlet_C3_of_uniform_firstJet_difference_quotient_estimates {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u : E n → F} {Du : E n → E n →L[ℝ] F}
    {Hu : E n → E n →L[ℝ] E n →L[ℝ] F} {K α : ℝ≥0}
    (hu : ∀ x, HasFDerivAt u (Du x) x) (hDu : ∀ x, HasFDerivAt Du (Hu x) x)
    (hHolder : HolderWith K α Hu) (hα : 0 < α)
    {p : E n} {r R : ℝ} (hrR : r < R)
    (hEstimate : ∀ v : E n, ∃ (h : ℕ → ℝ) (C : ℝ≥0),
      (∀ i, h i ≠ 0) ∧ Tendsto h atTop (𝓝 0) ∧
      ∀ i, HolderOnWith C α (fderiv ℝ (dirichletDifferenceQuotient Du v (h i))) (ball p R)) :
    ContDiffOn ℝ 3 u (ball p r) := by
  have hHC1 : ContDiffOn ℝ 1 Hu (ball p r) := by
    apply contDiffOn_clm_apply.mpr
    intro v
    obtain ⟨h, C, hh, hlim, hEst⟩ := hEstimate v
    exact (dirichlet_C1_directional_derivative_of_difference_quotient_estimate
      hDu hHolder hα v hh hlim hrR hEst).1
  have hDUEq : fderiv ℝ Du = Hu := funext fun x => (hDu x).fderiv
  have hUEq : fderiv ℝ u = Du := funext fun x => (hu x).fderiv
  have hDC2 : ContDiffOn ℝ 2 Du (ball p r) := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) isOpen_ball).mpr
    refine ⟨fun x _ => (hDu x).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rwa [hDUEq]
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 2) isOpen_ball).mpr
  refine ⟨fun x _ => (hu x).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rwa [hUEq]

end KEBall
