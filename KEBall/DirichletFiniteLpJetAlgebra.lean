import KEBall.DirichletAllMixedAngularHessianLp

/-! Finite actual directional jets in all finite Lp, with product closure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

def DirichletAllFiniteLp {n : ℕ} (μ : Measure (E n)) (f : E n → ℝ) : Prop :=
  ∀ p : ℝ≥0∞, p ≠ ⊤ → MemLp f p μ

theorem DirichletAllFiniteLp.add {n : ℕ} {μ : Measure (E n)} {f g : E n → ℝ}
    (hf : DirichletAllFiniteLp μ f) (hg : DirichletAllFiniteLp μ g) :
    DirichletAllFiniteLp μ (fun x => f x+g x) := fun p hp => (hf p hp).add (hg p hp)

theorem DirichletAllFiniteLp.mul {n : ℕ} {μ : Measure (E n)} {f g : E n → ℝ}
    (hf : DirichletAllFiniteLp μ f) (hg : DirichletAllFiniteLp μ g) :
    DirichletAllFiniteLp μ (fun x => f x*g x) := by
  intro p hp
  have ht : 2*p ≠ (⊤ : ℝ≥0∞) := ENNReal.mul_ne_top (by norm_num) hp
  letI : ENNReal.HolderTriple (2*p) (2*p) p := ⟨by
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← add_mul]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  exact (hg (2*p) ht).mul' (hf (2*p) ht)

theorem DirichletAllFiniteLp.const {n : ℕ} {μ : Measure (E n)} [IsFiniteMeasure μ] (c : ℝ) :
    DirichletAllFiniteLp μ (fun _ => c) := fun _ _ => memLp_const c

theorem DirichletAllFiniteLp.congr_ae {n : ℕ} {μ : Measure (E n)} {f g : E n → ℝ}
    (hf : DirichletAllFiniteLp μ f) (he : f =ᵐ[μ] g) : DirichletAllFiniteLp μ g :=
  fun p hp => MemLp.ae_eq he (hf p hp)

/-- All genuine classical directional derivatives through the given order have
every finite integrability exponent. Smoothness is only imposed on the open set. -/
def HasDirichletFiniteLpJets {n : ℕ} (U : Set (E n)) (μ : Measure (E n)) :
    ℕ → (E n → ℝ) → Prop
  | 0,f => ContDiffOn ℝ ∞ f U ∧ DirichletAllFiniteLp μ f
  | k+1,f => (ContDiffOn ℝ ∞ f U ∧ DirichletAllFiniteLp μ f) ∧
      ∀ d : E n, HasDirichletFiniteLpJets U μ k (fun x => fderiv ℝ f x d)

theorem HasDirichletFiniteLpJets.zero_order {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f) :
    HasDirichletFiniteLpJets U μ 0 f := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

theorem HasDirichletFiniteLpJets.contDiffOn {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f) : ContDiffOn ℝ ∞ f U :=
  hf.zero_order.1

theorem HasDirichletFiniteLpJets.of_le {n k l : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    {f : E n → ℝ} (hf : HasDirichletFiniteLpJets U μ k f) (hl : l ≤ k) :
    HasDirichletFiniteLpJets U μ l f := by
  induction l generalizing k f with
  | zero => exact hf.zero_order
  | succ l ih =>
    cases k with
    | zero => omega
    | succ k => exact ⟨hf.1,fun d => ih (hf.2 d) (by omega)⟩

theorem HasDirichletFiniteLpJets.congr {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f g : E n → ℝ}
    (hf : HasDirichletFiniteLpJets U μ k f) (he : EqOn f g U) :
    HasDirichletFiniteLpJets U μ k g := by
  induction k generalizing f g with
  | zero => exact ⟨hf.1.congr (fun x hx => (he hx).symm),hf.2.congr_ae (hμ.mono (fun _ hx => he hx))⟩
  | succ k ih =>
    refine ⟨⟨hf.1.1.congr (fun x hx => (he hx).symm),hf.1.2.congr_ae (hμ.mono (fun _ hx => he hx))⟩,?_⟩
    intro d
    apply ih (hf.2 d)
    intro x hx
    have hNear : f =ᶠ[𝓝 x] g := Filter.mem_of_superset (hU.mem_nhds hx) (fun _ hy => he hy)
    exact congrArg (fun L : E n →L[ℝ] ℝ => L d) hNear.fderiv_eq

theorem HasDirichletFiniteLpJets.add {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f g : E n → ℝ}
    (hf : HasDirichletFiniteLpJets U μ k f) (hg : HasDirichletFiniteLpJets U μ k g) :
    HasDirichletFiniteLpJets U μ k (fun x => f x+g x) := by
  induction k generalizing f g with
  | zero => exact ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  | succ k ih =>
    refine ⟨⟨hf.contDiffOn.add hg.contDiffOn,hf.1.2.add hg.1.2⟩,fun d => ?_⟩
    refine (ih (hf.2 d) (hg.2 d)).congr hU hμ ?_
    intro x hx
    change fderiv ℝ f x d + fderiv ℝ g x d = fderiv ℝ (fun y => f y+g y) x d
    rw [fderiv_fun_add ((hf.contDiffOn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      ((hg.contDiffOn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    rfl

theorem HasDirichletFiniteLpJets.mul {n k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) {f g : E n → ℝ}
    (hf : HasDirichletFiniteLpJets U μ k f) (hg : HasDirichletFiniteLpJets U μ k g) :
    HasDirichletFiniteLpJets U μ k (fun x => f x*g x) := by
  induction k generalizing f g with
  | zero => exact ⟨hf.1.mul hg.1,hf.2.mul hg.2⟩
  | succ k ih =>
    refine ⟨⟨hf.contDiffOn.mul hg.contDiffOn,hf.1.2.mul hg.1.2⟩,fun d => ?_⟩
    have h₁ := ih (hf.of_le (Nat.le_succ k)) (hg.2 d)
    have h₂ := ih (hg.of_le (Nat.le_succ k)) (hf.2 d)
    refine (h₁.add hU hμ h₂).congr hU hμ ?_
    intro x hx
    change f x * fderiv ℝ g x d + g x * fderiv ℝ f x d = fderiv ℝ (fun y => f y*g y) x d
    rw [fderiv_fun_mul ((hf.contDiffOn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      ((hg.contDiffOn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    rfl

theorem HasDirichletFiniteLpJets.const {n : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (k : ℕ) (c : ℝ) : HasDirichletFiniteLpJets U μ k (fun _ => c) := by
  induction k generalizing c with
  | zero => exact ⟨contDiffOn_const,DirichletAllFiniteLp.const c⟩
  | succ k ih =>
    refine ⟨⟨contDiffOn_const,DirichletAllFiniteLp.const c⟩,fun d => ?_⟩
    simpa only [fderiv_fun_const,Pi.zero_apply,zero_apply] using ih 0

end KEBall
