import KEBall.DirichletAngularDetLowerJets
import KEBall.DirichletAngularDensityJets
import KEBall.DirichletLinearizedFiniteLpGain

/-! The simultaneous one-order gain for every ordered angular word of the same potential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace KEBall

theorem hasDirichletFiniteLpJets_all_angularWords_step {n k : ℕ} (hn : 0<n)
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hKB : K ⊆ closedUnitBall n) (hUB : U ⊆ unitBall n) (hAway : ∀ x ∈ K, x ≠ 0)
    {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hAll : ∀ m, ∀ R : Fin m → DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ (k+2) (dirichletAngularWord R u))
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x) :
    ∀ m, ∀ R : Fin m → DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ (k+3) (dirichletAngularWord R u) := by
  have hfK : SmoothNear K f := by
    obtain ⟨V,hV,hBV,hfV⟩ := hf
    exact ⟨V,hV,hKB.trans hBV,hfV⟩
  have hX {m : ℕ} (R : Fin m → DirichletUnitaryField n) (S : DirichletUnitaryField n) :
      HasDirichletFiniteLpJets U μ (k+2)
        (dirichletAngularDerivative S.val (dirichletAngularWord R u)) := by
    simpa only [dirichletAngularWord,Fin.cons_zero,Fin.tail_cons] using hAll (m+1) (Fin.cons S R)
  have hBase : HasDirichletFiniteLpJets U μ (k+3) u := by
    refine hasDirichletFiniteLpJets_succ_of_unitary_derivatives_det hU hμ hK hUK hKB hUB hAway
      hu huS (hAll 0 (fun i => i.elim0)) ?_ hPos
      (hasDirichletFiniteLpJets_of_smoothNear_compact hU hμ hK hUK hfK (k+1)) hEq
    intro S
    exact hX (fun i : Fin 0 => i.elim0) S
  let A := dirichletWithinComplexHessian u
  have hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ (k+1) (fun x => A x i j) :=
    hasDirichletComplexFiniteLpJets_withinHessian_of_succ_succ hU hμ hUB hBase
  have hAS : ContDiffOn ℝ ∞ A U := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (contDiffOn_complexHessianOfRealBilinear
      (contDiffOn_dirichletWithinRealHessian_ball huS) i j).mono hUB
  have hAC : ContinuousOn A K := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (contDiffOn_complexHessianOfRealBilinear (r := 0)
      (contDiffOn_zero.mpr ((continuousOn_dirichletWithinRealHessian hu).mono hKB)) i j).continuousOn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro R
    cases m with
    | zero => exact hBase
    | succ m =>
      have hLow : HasDirichletFiniteLpJets U μ (k+1)
          (dirichletAngularDetLowerTerms R dirichletWithinComplexHessian u) := by
        apply hasDirichletFiniteLpJets_dirichletAngularDetLowerTerms R dirichletWithinComplexHessian
          hU hμ hK hUK hAS hAC hA
        intro j hj R' a b
        exact hasDirichletComplexFiniteLpJets_withinHessian_of_succ_succ hU hμ hUB
          (ih j (Nat.lt_succ_of_le hj) R') a b
      have hRight := hasDirichletFiniteLpJets_angularWord_smoothNear (k := k+1)
        hU hμ hK hUK hUB hfK R
      refine hasDirichletFiniteLpJets_succ_of_unitary_derivatives_linearized_det
        hU hμ hK hUK hUB hAway (contDiffOn_dirichletAngularWord_interior huS R)
        (hAll (m+1) R) (hX R) hAC hA (fun x hx => hPos x (hKB hx))
        (hRight.sub hU hμ hLow) ?_
      intro x hx
      have he := interior_angularWord_eq_linearized_det hn huS hEq R (hUB hx)
      exact eq_sub_of_add_eq he

end KEBall
