import KEBall.DirichletFiniteLpJetInverse

/-! Local and finite algebra operations for actual finite Lp jets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

theorem HasDirichletFiniteLpJets.neg {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f) :
    HasDirichletFiniteLpJets U μ k (fun x => -f x) := by
  simpa only [neg_one_mul] using (HasDirichletFiniteLpJets.const k (-1)).mul hU hμ hf

theorem HasDirichletFiniteLpJets.sub {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {f g : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f)
    (hg : HasDirichletFiniteLpJets U μ k g) :
    HasDirichletFiniteLpJets U μ k (fun x => f x-g x) := by
  simpa only [sub_eq_add_neg] using hf.add hU hμ (hg.neg hU hμ)

theorem HasDirichletFiniteLpJets.pow {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f) (j : ℕ) :
    HasDirichletFiniteLpJets U μ k (fun x => f x^j) := by
  induction j with
  | zero => simpa only [pow_zero] using HasDirichletFiniteLpJets.const (U := U) (μ := μ) k 1
  | succ j ih => simpa only [pow_succ] using ih.mul hU hμ hf

theorem HasDirichletFiniteLpJets.finsetSum {n k : ℕ} {ι : Type*}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (s : Finset ι)
    {f : ι → E n → ℝ} (hf : ∀ i ∈ s, HasDirichletFiniteLpJets U μ k (f i)) :
    HasDirichletFiniteLpJets U μ k (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasDirichletFiniteLpJets.const (U := U) (μ := μ) k 0
  | insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add hU hμ hs

theorem HasDirichletFiniteLpJets.finsetProd {n k : ℕ} {ι : Type*}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (s : Finset ι)
    {f : ι → E n → ℝ} (hf : ∀ i ∈ s, HasDirichletFiniteLpJets U μ k (f i)) :
    HasDirichletFiniteLpJets U μ k (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasDirichletFiniteLpJets.const (U := U) (μ := μ) k 1
  | insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self i s)).mul hU hμ hs

theorem HasDirichletFiniteLpJets.mono_measure {n k : ℕ} {U : Set (E n)} {μ ν : Measure (E n)}
    {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f) (hν : ν ≤ μ) :
    HasDirichletFiniteLpJets U ν k f := by
  induction k generalizing f with
  | zero => exact ⟨hf.1,fun p hp => (hf.2 p hp).mono_measure hν⟩
  | succ k ih => exact ⟨⟨hf.1.1,fun p hp => (hf.1.2 p hp).mono_measure hν⟩,fun d => ih (hf.2 d)⟩

theorem HasDirichletFiniteLpJets.mono_set {n k : ℕ} {U V : Set (E n)} {μ : Measure (E n)}
    {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f) (hV : V ⊆ U) :
    HasDirichletFiniteLpJets V μ k f := by
  induction k generalizing f with
  | zero => exact ⟨hf.1.mono hV,hf.2⟩
  | succ k ih => exact ⟨⟨hf.1.1.mono hV,hf.1.2⟩,fun d => ih (hf.2 d)⟩

theorem hasDirichletFiniteLpJets_of_smoothNear_compact {n : ℕ} {U K : Set (E n)}
    {μ : Measure (E n)} [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (hK : IsCompact K) (hUK : U ⊆ K) {f : E n → ℝ} (hf : SmoothNear K f) (k : ℕ) :
    HasDirichletFiniteLpJets U μ k f := by
  have hBase {g : E n → ℝ} (hg : SmoothNear K g) : HasDirichletFiniteLpJets U μ 0 g := by
    obtain ⟨V,hV,hKV,hgV⟩ := hg
    have hC := hgV.mono hKV
    obtain ⟨C,hCbound⟩ := hK.exists_bound_of_continuousOn hC.continuousOn
    have hMeas := (hC.mono hUK).continuousOn.aestronglyMeasurable (μ := μ) hU.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem hμ] at hMeas
    exact ⟨hC.mono hUK,fun p _ => (memLp_const C).mono' hMeas (hμ.mono (fun x hx => hCbound x (hUK hx)))⟩
  induction k generalizing f with
  | zero => exact hBase hf
  | succ k ih =>
    refine ⟨hBase hf,fun d => ?_⟩
    apply ih
    obtain ⟨V,hV,hKV,hfV⟩ := hf
    exact ⟨V,hV,hKV,(hfV.fderiv_of_isOpen hV (m := ∞) (by simp)).clm_apply contDiffOn_const⟩

end KEBall
