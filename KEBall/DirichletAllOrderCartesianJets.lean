import KEBall.DirichletAngularWordJetStep
import KEBall.DirichletFiniteLpJetGluing
import KEBall.DirichletFiniteLpJetsWeak

/-! All actual Cartesian orders for all original angular words, with the original measure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
open Filter MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem hasDirichletFiniteLpJets_all_angularWords_on_annulus {n : ℕ} (hn : 0<n)
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hKB : K ⊆ closedUnitBall n) (hUB : U ⊆ unitBall n) (hAway : ∀ x ∈ K, x ≠ 0)
    (hν : μ ≤ (volume0 n).restrict (unitBall n))
    {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x)
    (k : ℕ) {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    HasDirichletFiniteLpJets U μ k (dirichletAngularWord R u) := by
  have hIter : ∀ q m, ∀ R : Fin m → DirichletUnitaryField n,
      HasDirichletFiniteLpJets U μ (q+2) (dirichletAngularWord R u) := by
    intro q
    induction q with
    | zero =>
      intro j Q
      exact ((hasDirichletFiniteLpJets_two_angularWord_of_C2_solution hn hu huS hu0 hPos hf hEq Q).mono_measure hν).mono_set hUB
    | succ q ih =>
      exact hasDirichletFiniteLpJets_all_angularWords_step hn hU hμ hK hUK hKB hUB hAway
        hu huS ih hPos hf hEq
  exact (hIter k m R).of_le (by omega)

theorem hasDirichletFiniteLpJets_all_angularWords_of_C2_solution {n : ℕ}
    (hn : 0<n) {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x)
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
    hasDirichletFiniteLpJets_all_angularWords_on_annulus hn hU
      (ae_restrict_mem hU.measurableSet) hK hUK hKB hUB hAway hUν hu huS hu0 hPos hf hEq k R
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

theorem hasDirichletWeakDerivativesL2_all_angularWords_of_C2_solution {n : ℕ}
    (hn : 0<n) {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x)
    (k : ℕ) {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    HasDirichletWeakDerivativesL2 (dirichletAngularWord R u) k :=
  (hasDirichletFiniteLpJets_all_angularWords_of_C2_solution hn hu huS hu0 hPos hf hEq k R).weakDerivativesL2 hn

end KEBall
