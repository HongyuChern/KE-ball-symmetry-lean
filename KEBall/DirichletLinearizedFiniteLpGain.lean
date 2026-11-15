import KEBall.DirichletCompactTangentRecovery
import KEBall.DirichletAnnularFiniteLpGain

/-! One genuine derivative gain for a linearized angular equation on an annulus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem hasDirichletComplexFiniteLpJets_withinHessian_of_succ_succ {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hUB : U ⊆ unitBall n)
    {u : E n → ℝ} (hu : HasDirichletFiniteLpJets U μ (k+2) u) (i j : Fin n) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => dirichletWithinComplexHessian u x i j) := by
  refine (hasDirichletComplexFiniteLpJets_complexHessianOfRealBilinear hU hμ
    (hasDirichletFiniteLpJets_hessian_of_succ_succ hU hμ hu) i j).congr hU hμ ?_
  intro x hx
  change complexHessianOfRealBilinear (realHessian u x) i j=
    complexHessianOfRealBilinear (dirichletWithinRealHessian u x) i j
  rw [dirichletWithinRealHessian_eq_on_ball u (hUB hx)]

theorem hasDirichletFiniteLpJets_succ_of_unitary_derivatives_linearized_det {n k : ℕ}
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hUB : U ⊆ unitBall n) (hAway : ∀ x ∈ K, x ≠ 0)
    {u f : E n → ℝ} (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hJet : HasDirichletFiniteLpJets U μ (k+2) u)
    (hX : ∀ S : DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ (k+2) (dirichletAngularDerivative S.val u))
    {A : E n → Matrix (Fin n) (Fin n) ℂ} (hAC : ContinuousOn A K)
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ (k+1) (fun x => A x i j))
    (hPos : ∀ x ∈ K, (A x).PosDef) (hf : HasDirichletFiniteLpJets U μ (k+1) f)
    (hEq : ∀ x ∈ U, ((A x).adjugate * dirichletWithinComplexHessian u x).trace.re=f x) :
    HasDirichletFiniteLpJets U μ (k+3) u := by
  let b := EuclideanSpace.basisFun (Fin (2*n)) ℝ
  let B := realHessian u
  have hContract (S : DirichletUnitaryField n) (a : E n) :
      HasDirichletFiniteLpJets U μ (k+1) (fun x => B x (S.val x) a) :=
    hasDirichletFiniteLpJets_hessian_rotation hU hμ hUB huS S.val hJet (hX S) a
  have hT (a c : E n) : HasDirichletFiniteLpJets U μ (k+1)
      (fun x => dirichletTangentHessianPart B x a c) := by
    apply hasDirichletFiniteLpJets_tangentHessianPart hU hμ b
      (fun x hx => hAway x (hUK hx))
      (hasDirichletFiniteLpJets_inv_norm_sq_compact hU hμ hK hUK hAway)
      (hasDirichletFiniteLpJets_inner_compact hU hμ hK hUK)
    · intro i j v
      exact hContract ⟨dirichletUnitaryRotation (b i) (b j),
        dirichletUnitaryRotation_star _ _,dirichletUnitaryRotation_J _ _⟩ v
    · intro v
      simpa only [JCLM_apply] using hContract
        ⟨JCLM n,JCLM_star n,fun x => by simp only [JCLM_apply]⟩ v
  have hB (a c : E n) : HasDirichletFiniteLpJets U μ (k+1) (fun x => B x a c) := by
    refine hasDirichletFiniteLpJets_realBilinear_of_compact_tangent_linearized_det
      hU hμ hK hUK hAway b ?_ hT hAC hA hPos hf ?_ a c
    · intro x hx v w
      exact ((huS.contDiffAt (isOpen_ball.mem_nhds (hUB hx))).isSymmSndFDerivAt
        (by simp; norm_cast)).eq v w
    · intro x hx
      have he : dirichletWithinComplexHessian u x=complexHessianOfRealBilinear (B x) := by
        change complexHessianOfRealBilinear (dirichletWithinRealHessian u x)=_
        rw [dirichletWithinRealHessian_eq_on_ball u (hUB hx)]
      rw [← he]
      exact hEq x hx
  exact hasDirichletFiniteLpJets_succ_succ_of_hessian (k := k+1) hU hμ (hJet.of_le (by omega)) hB

end KEBall
