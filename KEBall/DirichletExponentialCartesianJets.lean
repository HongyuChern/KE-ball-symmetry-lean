import KEBall.DirichletAllOrderCartesianJets
import KEBall.DirichletExponentialAngularLp
import KEBall.DirichletAngularCompositionJets

/-! Simultaneous recovery of all Cartesian jets for a C2 solution with exponential density. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace KEBall

theorem hasDirichletFiniteLpJets_all_angularWords_exponential_step {n k : ℕ} (hn : 0<n)
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hKB : K ⊆ closedUnitBall n) (hUB : U ⊆ unitBall n) (hAway : ∀ x ∈ K, x ≠ 0)
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hAll : ∀ m, ∀ R : Fin m → DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ (k+2) (dirichletAngularWord R u))
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=c * Real.exp (a * u x)) :
    ∀ m, ∀ R : Fin m → DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ (k+3) (dirichletAngularWord R u) := by
  have hH : ContDiff ℝ ∞ (fun z : ℝ => c * Real.exp (a * z)) :=
    contDiff_const.mul ((contDiff_const.mul contDiff_id).exp)
  have hDensity (m : ℕ) (R : Fin m → DirichletUnitaryField n) :
      HasDirichletFiniteLpJets U μ (k+1)
        (dirichletAngularWord R (fun x => c * Real.exp (a * u x))) :=
    (hasDirichletFiniteLpJets_all_angularWords_compact_comp hU hμ hK hUK hUB
      huS (hu.continuousOn.mono hKB) hAll hH m R).of_le (by omega)
  have hX {m : ℕ} (R : Fin m → DirichletUnitaryField n) (S : DirichletUnitaryField n) :
      HasDirichletFiniteLpJets U μ (k+2)
        (dirichletAngularDerivative S.val (dirichletAngularWord R u)) := by
    simpa only [dirichletAngularWord,Fin.cons_zero,Fin.tail_cons] using hAll (m+1) (Fin.cons S R)
  have hBase : HasDirichletFiniteLpJets U μ (k+3) u := by
    refine hasDirichletFiniteLpJets_succ_of_unitary_derivatives_det hU hμ hK hUK hKB hUB hAway
      hu huS (hAll 0 (fun i => i.elim0)) ?_ hPos
      (hDensity 0 (fun i => i.elim0)) hEq
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
      have hRight := hDensity (m+1) R
      refine hasDirichletFiniteLpJets_succ_of_unitary_derivatives_linearized_det
        hU hμ hK hUK hUB hAway (contDiffOn_dirichletAngularWord_interior huS R)
        (hAll (m+1) R) (hX R) hAC hA (fun x hx => hPos x (hKB hx))
        (hRight.sub hU hμ hLow) ?_
      intro x hx
      have he := interior_angularWord_eq_linearized_det hn huS hEq R (hUB hx)
      exact eq_sub_of_add_eq he

theorem hasDirichletFiniteLpJets_all_angularWords_exponential_on_annulus {n : ℕ} (hn : 0<n)
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hKB : K ⊆ closedUnitBall n) (hUB : U ⊆ unitBall n) (hAway : ∀ x ∈ K, x ≠ 0)
    (hν : μ ≤ (volume0 n).restrict (unitBall n))
    {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=c * Real.exp (a * u x))
    (k : ℕ) {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    HasDirichletFiniteLpJets U μ k (dirichletAngularWord R u) := by
  have hIter : ∀ q m, ∀ R : Fin m → DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ (q+2) (dirichletAngularWord R u) := by
    intro q
    induction q with
    | zero =>
      intro j Q
      exact ((hasDirichletFiniteLpJets_two_angularWord_of_exponential_C2_solution hn hu huS hu0 hPos a c hEq Q).mono_measure hν).mono_set hUB
    | succ q ih =>
      exact hasDirichletFiniteLpJets_all_angularWords_exponential_step hn hU hμ hK hUK hKB hUB hAway
        hu huS ih hPos a c hEq
  exact (hIter k m R).of_le (by omega)

theorem hasDirichletFiniteLpJets_all_angularWords_of_exponential_C2_solution {n : ℕ}
    (hn : 0<n) {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=c * Real.exp (a * u x))
    (k : ℕ) {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    HasDirichletFiniteLpJets (unitBall n) ((volume0 n).restrict (unitBall n)) k
      (dirichletAngularWord R u) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let U := dirichletOuterOpenAnnulus n
  let K := dirichletOuterClosedAnnulus n
  let V := ball (0 : E n) (3/4 : ℝ)
  let L := closedBall (0 : E n) (3/4 : ℝ)
  let ν := (volume0 n).restrict (unitBall n)
  let νU := (volume0 n).restrict U
  let νV := (volume0 n).restrict V
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_norm)
  have hV : IsOpen V := isOpen_ball
  have hK : IsCompact K := (isCompact_closedBall (0 : E n) 1).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hUK : U ⊆ K := fun x hx => ⟨ball_subset_closedBall hx.1,(show (1/2 : ℝ)<‖x‖ from hx.2).le⟩
  have hKB : K ⊆ closedUnitBall n := inter_subset_left
  have hUB : U ⊆ unitBall n := inter_subset_left
  have hAway : ∀ x ∈ K, x ≠ 0 := by
    intro x hx he
    have h := hx.2
    norm_num [he] at h
  have hUν : νU ≤ ν := Measure.restrict_mono hUB le_rfl
  have hVB : V ⊆ unitBall n := ball_subset_ball (by norm_num)
  have hVν : νV ≤ ν := Measure.restrict_mono hVB le_rfl
  letI : IsFiniteMeasure νU := isFiniteMeasure_of_le ν hUν
  letI : IsFiniteMeasure νV := isFiniteMeasure_of_le ν hVν
  have hOuter : HasDirichletFiniteLpJets U νU k (dirichletAngularWord R u) :=
    hasDirichletFiniteLpJets_all_angularWords_exponential_on_annulus hn hU
      (ae_restrict_mem hU.measurableSet) hK hUK hKB hUB hAway hUν hu huS hu0 hPos a c hEq k R
  have hLB : L ⊆ unitBall n := closedBall_subset_ball (by norm_num)
  have hNear : SmoothNear L u := ⟨unitBall n,isOpen_ball,hLB,huS⟩
  have hInner : HasDirichletFiniteLpJets V νV k (dirichletAngularWord R u) :=
    hasDirichletFiniteLpJets_angularWord_smoothNear hV (ae_restrict_mem hV.measurableSet)
      (isCompact_closedBall _ _) ball_subset_closedBall hVB hNear R
  have hCover : unitBall n ⊆ U ∪ V := by
    intro x hx
    by_cases hr : (1/2 : ℝ)<‖x‖
    · exact Or.inl ⟨hx,hr⟩
    · apply Or.inr
      exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (le_of_not_gt hr) (by norm_num))
  have hM : ν ≤ νU+νV :=
    (Measure.restrict_mono hCover le_rfl).trans (Measure.restrict_union_le U V)
  exact hasDirichletFiniteLpJets_of_measure_cover isOpen_ball
    (contDiffOn_dirichletAngularWord_interior huS R) hM hOuter hInner

theorem hasDirichletWeakDerivativesL2_all_angularWords_of_exponential_C2_solution {n : ℕ}
    (hn : 0<n) {u : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (a c : ℝ)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=c * Real.exp (a * u x))
    (k : ℕ) {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    HasDirichletWeakDerivativesL2 (dirichletAngularWord R u) k :=
  (hasDirichletFiniteLpJets_all_angularWords_of_exponential_C2_solution hn hu huS hu0 hPos a c hEq k R).weakDerivativesL2 hn

end KEBall
