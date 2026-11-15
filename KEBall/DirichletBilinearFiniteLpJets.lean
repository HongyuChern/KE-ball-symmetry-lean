import KEBall.DirichletFiniteLpJetOperations
import KEBall.DirichletAngularWordLowerJetsLp

/-! Actual Hessian entries and tangential contractions in the finite Lp jet calculus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

theorem dirichlet_fderiv_directional_eq_hessian_on {n : ℕ} {U : Set (E n)}
    (hU : IsOpen U) {u : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    {x : E n} (hx : x ∈ U) (d e : E n) :
    fderiv ℝ (fun y => fderiv ℝ u y d) x e = realHessian u x e d := by
  rw [fderiv_clm_apply
    (((hu.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const d)]
  simp [realHessian]

theorem hasDirichletFiniteLpJets_hessian_of_succ_succ {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {u : E n → ℝ} (hu : HasDirichletFiniteLpJets U μ (k+2) u) (a b : E n) :
    HasDirichletFiniteLpJets U μ k (fun x => realHessian u x a b) := by
  refine ((hu.2 b).2 a).congr hU hμ ?_
  intro x hx
  exact dirichlet_fderiv_directional_eq_hessian_on hU hu.contDiffOn hx b a

theorem hasDirichletFiniteLpJets_succ_succ_of_hessian {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {u : E n → ℝ} (hu : HasDirichletFiniteLpJets U μ 1 u)
    (hH : ∀ a b, HasDirichletFiniteLpJets U μ k (fun x => realHessian u x a b)) :
    HasDirichletFiniteLpJets U μ (k+2) u := by
  refine ⟨hu.1,fun d => ⟨(hu.2 d).zero_order,fun e => ?_⟩⟩
  refine (hH e d).congr hU hμ ?_
  intro x hx
  exact (dirichlet_fderiv_directional_eq_hessian_on hU hu.contDiffOn hx d e).symm

theorem hasDirichletFiniteLpJets_hessian_rotation {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hUB : U ⊆ unitBall n)
    {u : E n → ℝ} (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (S : E n →L[ℝ] E n) (hu : HasDirichletFiniteLpJets U μ (k+1) u)
    (hXu : HasDirichletFiniteLpJets U μ (k+1) (dirichletAngularDerivative S u)) (a : E n) :
    HasDirichletFiniteLpJets U μ k (fun x => realHessian u x (S x) a) := by
  refine ((hXu.2 a).sub hU hμ (hu.2 (S a))).congr hU hμ ?_
  intro x hx
  change fderiv ℝ (dirichletAngularDerivative S u) x a - fderiv ℝ u x (S a) = realHessian u x (S x) a
  rw [fderiv_dirichletAngularDerivative_on_ball huS S (hUB hx)]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
  have hs := (huS.contDiffAt (isOpen_ball.mem_nhds (hUB hx))).isSymmSndFDerivAt (by simp; norm_cast)
  change fderiv ℝ u x (S a) + realHessian u x a (S x) - fderiv ℝ u x (S a) = _
  rw [show realHessian u x a (S x) = realHessian u x (S x) a from hs.eq a (S x)]
  ring

end KEBall
