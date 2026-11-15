import KEBall.DirichletCompactTangentRecovery
import KEBall.DirichletAngularWordFiniteLpJets

/-! A genuine Cartesian derivative gain for the same C2 Monge-Ampere potential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem dirichletWithinRealHessian_symm {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) {x : E n} (hx : x ∈ closedUnitBall n)
    (a b : E n) : dirichletWithinRealHessian u x a b=dirichletWithinRealHessian u x b a := by
  have hU : UniqueDiffOn ℝ (closedUnitBall n) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E n) 1)
      ⟨0,mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩
  have hClosure : x ∈ closure (interior (closedUnitBall n)) := by
    rw [closedUnitBall,interior_closedBall _ (by norm_num),closure_ball _ (by norm_num)]
    exact hx
  exact ((hu x hx).isSymmSndFDerivWithinAt (by norm_num) hU hClosure hx).eq a b

theorem hasDirichletFiniteLpJets_succ_of_unitary_derivatives_det {n k : ℕ}
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hKB : K ⊆ closedUnitBall n) (hUB : U ⊆ unitBall n) (hAway : ∀ x ∈ K, x ≠ 0)
    {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hJet : HasDirichletFiniteLpJets U μ (k+2) u)
    (hX : ∀ S : DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ (k+2) (dirichletAngularDerivative S.val u))
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : HasDirichletFiniteLpJets U μ (k+1) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x) :
    HasDirichletFiniteLpJets U μ (k+3) u := by
  let b := EuclideanSpace.basisFun (Fin (2*n)) ℝ
  let B := dirichletWithinRealHessian u
  have hContract (S : DirichletUnitaryField n) (a : E n) :
      HasDirichletFiniteLpJets U μ (k+1) (fun x => B x (S.val x) a) := by
    refine (hasDirichletFiniteLpJets_hessian_rotation hU hμ hUB huS S.val hJet (hX S) a).congr hU hμ ?_
    intro x hx
    change realHessian u x (S.val x) a=dirichletWithinRealHessian u x (S.val x) a
    rw [dirichletWithinRealHessian_eq_on_ball u (hUB hx)]
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
    refine hasDirichletFiniteLpJets_realBilinear_of_compact_tangent_det hU hμ hK hUK hAway b
      ((continuousOn_dirichletWithinRealHessian hu).mono hKB)
      (fun x hx a c => dirichletWithinRealHessian_symm hu (hKB hx) a c)
      hT hf (fun x hx => hPos x (hKB hx)) ?_ a c
    intro x hx
    change (complexHessianOfRealBilinear (dirichletWithinRealHessian u x)).det.re=f x
    rw [dirichletWithinRealHessian_eq_on_ball u (hUB hx),complexHessianOfRealBilinear_eq
      ((hu.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds (hUB hx)))]
    exact hEq x (hUB hx)
  apply hasDirichletFiniteLpJets_succ_succ_of_hessian (k := k+1) hU hμ (hJet.of_le (by omega))
  intro a c
  refine (hB a c).congr hU hμ ?_
  intro x hx
  exact congrArg (fun H : E n →L[ℝ] E n →L[ℝ] ℝ => H a c)
    (dirichletWithinRealHessian_eq_on_ball u (hUB hx))

theorem hasDirichletFiniteLpJets_three_of_C2_solution_on_annulus {n : ℕ}
    (hn : 0<n) {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hKB : K ⊆ closedUnitBall n) (hUB : U ⊆ unitBall n) (hAway : ∀ x ∈ K, x ≠ 0)
    (hν : μ ≤ (volume0 n).restrict (unitBall n))
    {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x) :
    HasDirichletFiniteLpJets U μ 3 u := by
  have hAll {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
      HasDirichletFiniteLpJets U μ 2 (dirichletAngularWord R u) :=
    ((hasDirichletFiniteLpJets_two_angularWord_of_C2_solution hn hu huS hu0 hPos hf hEq R).mono_measure hν).mono_set hUB
  have huJ : HasDirichletFiniteLpJets U μ 2 u := hAll (fun i : Fin 0 => i.elim0)
  have hX (S : DirichletUnitaryField n) :
      HasDirichletFiniteLpJets U μ 2 (dirichletAngularDerivative S.val u) := by
    simpa only [dirichletAngularWord] using hAll (fun _ : Fin 1 => S)
  have hfK : SmoothNear K f := by
    obtain ⟨V,hV,hBV,hfV⟩ := hf
    exact ⟨V,hV,hKB.trans hBV,hfV⟩
  exact hasDirichletFiniteLpJets_succ_of_unitary_derivatives_det (k := 0)
    hU hμ hK hUK hKB hUB hAway hu huS huJ hX hPos
    (hasDirichletFiniteLpJets_of_smoothNear_compact hU hμ hK hUK hfK 1) hEq

end KEBall
