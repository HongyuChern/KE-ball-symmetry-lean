import KEBall.DirichletFiniteLpJetOperations

/-! Real and imaginary parts of actual finite complex jets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000
open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

def HasDirichletComplexFiniteLpJets {n : ℕ} (U : Set (E n)) (μ : Measure (E n))
    (k : ℕ) (f : E n → ℂ) : Prop :=
  HasDirichletFiniteLpJets U μ k (fun x => (f x).re) ∧
  HasDirichletFiniteLpJets U μ k (fun x => (f x).im)

theorem HasDirichletComplexFiniteLpJets.const {n : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (k : ℕ) (c : ℂ) :
    HasDirichletComplexFiniteLpJets U μ k (fun _ => c) :=
  ⟨HasDirichletFiniteLpJets.const k c.re,HasDirichletFiniteLpJets.const k c.im⟩

theorem HasDirichletComplexFiniteLpJets.congr {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f g : E n → ℂ}
    (hf : HasDirichletComplexFiniteLpJets U μ k f) (he : EqOn f g U) :
    HasDirichletComplexFiniteLpJets U μ k g :=
  ⟨hf.1.congr hU hμ (fun x hx => congrArg Complex.re (he hx)),
   hf.2.congr hU hμ (fun x hx => congrArg Complex.im (he hx))⟩

theorem HasDirichletComplexFiniteLpJets.add {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f g : E n → ℂ}
    (hf : HasDirichletComplexFiniteLpJets U μ k f) (hg : HasDirichletComplexFiniteLpJets U μ k g) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => f x+g x) := by
  exact ⟨by simpa only [Complex.add_re] using hf.1.add hU hμ hg.1,
    by simpa only [Complex.add_im] using hf.2.add hU hμ hg.2⟩

theorem HasDirichletComplexFiniteLpJets.neg {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f : E n → ℂ}
    (hf : HasDirichletComplexFiniteLpJets U μ k f) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => -f x) := by
  exact ⟨by simpa only [Complex.neg_re] using hf.1.neg hU hμ,
    by simpa only [Complex.neg_im] using hf.2.neg hU hμ⟩

theorem HasDirichletComplexFiniteLpJets.sub {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f g : E n → ℂ}
    (hf : HasDirichletComplexFiniteLpJets U μ k f) (hg : HasDirichletComplexFiniteLpJets U μ k g) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => f x-g x) := by
  simpa only [sub_eq_add_neg] using hf.add hU hμ (hg.neg hU hμ)

theorem HasDirichletComplexFiniteLpJets.mul {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f g : E n → ℂ}
    (hf : HasDirichletComplexFiniteLpJets U μ k f) (hg : HasDirichletComplexFiniteLpJets U μ k g) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => f x*g x) := by
  exact ⟨by simpa only [Complex.mul_re] using
      (hf.1.mul hU hμ hg.1).sub hU hμ (hf.2.mul hU hμ hg.2),
    by simpa only [Complex.mul_im] using
      (hf.1.mul hU hμ hg.2).add hU hμ (hf.2.mul hU hμ hg.1)⟩

theorem HasDirichletComplexFiniteLpJets.star {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f : E n → ℂ}
    (hf : HasDirichletComplexFiniteLpJets U μ k f) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => star (f x)) := by
  exact ⟨by simpa only [Complex.star_def,Complex.conj_re] using hf.1,
    by simpa only [Complex.star_def,Complex.conj_im] using hf.2.neg hU hμ⟩

theorem HasDirichletFiniteLpJets.ofReal {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => (f x : ℂ)) :=
  ⟨hf,HasDirichletFiniteLpJets.const k 0⟩

theorem HasDirichletComplexFiniteLpJets.finsetSum {n k : ℕ} {ι : Type*}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (s : Finset ι)
    {f : ι → E n → ℂ} (hf : ∀ i ∈ s, HasDirichletComplexFiniteLpJets U μ k (f i)) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasDirichletComplexFiniteLpJets.const (U := U) (μ := μ) k 0
  | insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add hU hμ hs

theorem HasDirichletComplexFiniteLpJets.finsetProd {n k : ℕ} {ι : Type*}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (s : Finset ι)
    {f : ι → E n → ℂ} (hf : ∀ i ∈ s, HasDirichletComplexFiniteLpJets U μ k (f i)) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasDirichletComplexFiniteLpJets.const (U := U) (μ := μ) k 1
  | insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self i s)).mul hU hμ hs

end KEBall
