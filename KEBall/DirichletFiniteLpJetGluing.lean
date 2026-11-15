import KEBall.DirichletAnnularFiniteLpGain

/-! Gluing genuine finite Lp derivatives, and a global third-order gain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem DirichletAllFiniteLp.add_measure {n : ℕ} {μ ν : Measure (E n)} {f : E n → ℝ}
    (hμ : DirichletAllFiniteLp μ f) (hν : DirichletAllFiniteLp ν f) :
    DirichletAllFiniteLp (μ+ν) f := by
  intro p hp
  have hm := (hμ p hp).aestronglyMeasurable.add_measure (hν p hp).aestronglyMeasurable
  by_cases hp0 : p=0
  · subst p
    exact ⟨hm,by simp⟩
  · exact (integrable_norm_rpow_iff hm hp0 hp).mp
      (((hμ p hp).integrable_norm_rpow hp0 hp).add_measure
        ((hν p hp).integrable_norm_rpow hp0 hp))

theorem hasDirichletFiniteLpJets_of_measure_cover {n k : ℕ}
    {U V W : Set (E n)} {μ ν ρ : Measure (E n)}
    (hW : IsOpen W) {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f W)
    (hCover : μ ≤ ν+ρ) (hU : HasDirichletFiniteLpJets U ν k f)
    (hV : HasDirichletFiniteLpJets V ρ k f) : HasDirichletFiniteLpJets W μ k f := by
  induction k generalizing f with
  | zero =>
    exact ⟨hf,fun p hp => ((hU.2.add_measure hV.2) p hp).mono_measure hCover⟩
  | succ k ih =>
    refine ⟨⟨hf,fun p hp => ((hU.1.2.add_measure hV.1.2) p hp).mono_measure hCover⟩,fun d => ?_⟩
    exact ih ((hf.fderiv_of_isOpen hW (m := ∞) (by simp)).clm_apply contDiffOn_const)
      (hU.2 d) (hV.2 d)

def dirichletOuterOpenAnnulus (n : ℕ) : Set (E n) := unitBall n ∩ {x | (1/2 : ℝ)<‖x‖}
def dirichletOuterClosedAnnulus (n : ℕ) : Set (E n) := closedUnitBall n ∩ {x | (1/2 : ℝ)≤‖x‖}

theorem hasDirichletFiniteLpJets_three_of_C2_solution {n : ℕ}
    (hn : 0<n) {u f : E n → ℝ} (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n)) (hu0 : ∀ x ∈ unitSphere n, u x=0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re=f x) :
    HasDirichletFiniteLpJets (unitBall n) ((volume0 n).restrict (unitBall n)) 3 u := by
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
  have hOuter : HasDirichletFiniteLpJets U νU 3 u :=
    hasDirichletFiniteLpJets_three_of_C2_solution_on_annulus hn hU
      (ae_restrict_mem hU.measurableSet) hK hUK hKB hUB hAway hUν hu huS hu0 hPos hf hEq
  have hLB : L ⊆ unitBall n := closedBall_subset_ball (by norm_num)
  have hNear : SmoothNear L u := ⟨unitBall n,isOpen_ball,hLB,huS⟩
  have hInner : HasDirichletFiniteLpJets V νV 3 u :=
    hasDirichletFiniteLpJets_of_smoothNear_compact hV (ae_restrict_mem hV.measurableSet)
      (isCompact_closedBall _ _) ball_subset_closedBall hNear 3
  have hCover : unitBall n ⊆ U ∪ V := by
    intro x hx
    by_cases hr : (1/2 : ℝ)<‖x‖
    · exact Or.inl ⟨hx,hr⟩
    · apply Or.inr
      exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (le_of_not_gt hr) (by norm_num))
  have hM : ν ≤ νU+νV :=
    (Measure.restrict_mono hCover le_rfl).trans (Measure.restrict_union_le U V)
  exact hasDirichletFiniteLpJets_of_measure_cover isOpen_ball huS hM hOuter hInner

end KEBall
