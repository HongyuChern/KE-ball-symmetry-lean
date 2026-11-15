import KEBall.DirichletFiniteLpJetOperations
import KEBall.DirichletAngularWordLowerJetsLp

/-! Smooth-near density derivatives use actual ambient derivatives and agree with the original words inside. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

noncomputable def dirichletFullAngularWord {n : ℕ} :
    {m : ℕ} → (Fin m → DirichletUnitaryField n) → (E n → ℝ) → E n → ℝ
  | 0,_,f => f
  | _m+1,R,f => fun x => fderiv ℝ (dirichletFullAngularWord (Fin.tail R) f) x ((R 0).val x)

theorem smoothNear_dirichletFullAngularWord {n m : ℕ} {K : Set (E n)} {f : E n → ℝ}
    (hf : SmoothNear K f) (R : Fin m → DirichletUnitaryField n) :
    SmoothNear K (dirichletFullAngularWord R f) := by
  induction m with
  | zero => exact hf
  | succ m ih =>
    obtain ⟨V,hV,hKV,hfV⟩ := ih (Fin.tail R)
    exact ⟨V,hV,hKV,(hfV.fderiv_of_isOpen hV (m := ∞) (by simp)).clm_apply
      (R 0).val.contDiff.contDiffOn⟩

theorem dirichletFullAngularWord_eq_on_ball {n m : ℕ}
    (R : Fin m → DirichletUnitaryField n) (f : E n → ℝ) :
    EqOn (dirichletFullAngularWord R f) (dirichletAngularWord R f) (unitBall n) := by
  induction m with
  | zero => exact fun _ _ => rfl
  | succ m ih =>
    intro x hx
    rw [dirichletAngularWord,dirichletAngularDerivative_eq_fderiv_on_ball _ _ hx]
    change fderiv ℝ (dirichletFullAngularWord (Fin.tail R) f) x ((R 0).val x)=_
    have he : dirichletFullAngularWord (Fin.tail R) f =ᶠ[𝓝 x] dirichletAngularWord (Fin.tail R) f :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hx) (fun y hy => ih (Fin.tail R) hy)
    rw [he.fderiv_eq]

theorem hasDirichletFiniteLpJets_angularWord_smoothNear {n m k : ℕ}
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hUB : U ⊆ unitBall n) {f : E n → ℝ} (hf : SmoothNear K f)
    (R : Fin m → DirichletUnitaryField n) :
    HasDirichletFiniteLpJets U μ k (dirichletAngularWord R f) := by
  refine (hasDirichletFiniteLpJets_of_smoothNear_compact hU hμ hK hUK
    (smoothNear_dirichletFullAngularWord hf R) k).congr hU hμ ?_
  intro x hx
  exact dirichletFullAngularWord_eq_on_ball R f (hUB hx)

end KEBall
