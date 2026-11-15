import KEBall.DirichletAngularWordLowerJetsLp
import KEBall.DirichletFiniteLpJetAlgebra

/-! All original angular words have genuine classical jets through order two in every finite Lp. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem fderiv_directionalDerivative_eq_realHessian_on_ball {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) {x : E n} (hx : x ∈ unitBall n) (d e : E n) :
    fderiv ℝ (fun y => fderiv ℝ u y d) x e = realHessian u x e d := by
  rw [fderiv_clm_apply
    (((hu.contDiffAt (isOpen_ball.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const d)]
  simp [realHessian]

theorem hasDirichletFiniteLpJets_two_of_hessian {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n))
    (h₀ : DirichletAllFiniteLp ((volume0 n).restrict (unitBall n)) u)
    (h₁ : ∀ p : ℝ≥0∞, p ≠ ⊤ → MemLp (fderiv ℝ u) p ((volume0 n).restrict (unitBall n)))
    (h₂ : ∀ p : ℝ≥0∞, p ≠ ⊤ → MemLp (realHessian u) p ((volume0 n).restrict (unitBall n))) :
    HasDirichletFiniteLpJets (unitBall n) ((volume0 n).restrict (unitBall n)) 2 u := by
  have hD (d : E n) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x d) (unitBall n) :=
    (hu.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hDD (d e : E n) : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ (fun y => fderiv ℝ u y d) x e) (unitBall n) :=
    ((hD d).fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply contDiffOn_const
  refine ⟨⟨hu,h₀⟩,fun d => ⟨⟨hD d,?_⟩,fun e => ⟨hDD d e,?_⟩⟩⟩
  · intro p hp
    refine ((h₁ p hp).norm.const_mul ‖d‖).mono'
      ((hD d).continuousOn.aestronglyMeasurable measurableSet_ball) ?_
    exact Eventually.of_forall (fun x => ((fderiv ℝ u x).le_opNorm d).trans_eq (mul_comm _ _))
  · intro p hp
    refine ((h₂ p hp).norm.const_mul (‖e‖*‖d‖)).mono'
      ((hDD d e).continuousOn.aestronglyMeasurable measurableSet_ball) ?_
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    rw [fderiv_directionalDerivative_eq_realHessian_on_ball hu hx]
    calc
      ‖realHessian u x e d‖ ≤ ‖realHessian u x e‖*‖d‖ := (realHessian u x e).le_opNorm d
      _ ≤ (‖realHessian u x‖*‖e‖)*‖d‖ := mul_le_mul_of_nonneg_right ((realHessian u x).le_opNorm e) (norm_nonneg _)
      _ = (‖e‖*‖d‖)*‖realHessian u x‖ := by ring

theorem hasDirichletFiniteLpJets_two_angularWord_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    HasDirichletFiniteLpJets (unitBall n) ((volume0 n).restrict (unitBall n)) 2
      (dirichletAngularWord R u) := by
  apply hasDirichletFiniteLpJets_two_of_hessian (contDiffOn_dirichletAngularWord_interior huS R)
  · intro p hp
    exact (memLp_angularWord_lower_jets_of_C2_solution_finite hn hu huS hu0 hPos hf hEq R p hp).1
  · intro p hp
    exact (memLp_angularWord_lower_jets_of_C2_solution_finite hn hu huS hu0 hPos hf hEq R p hp).2
  · intro p hp
    refine MemLp.ae_eq ?_ (memLp_withinHessian_angularWord_of_C2_solution_finite
      hn hu huS hu0 hPos hf hEq R p hp)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact dirichletWithinRealHessian_eq_on_ball _ hx

end KEBall
