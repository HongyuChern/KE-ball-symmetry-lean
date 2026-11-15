import KEBall.DirichletComplexFiniteLpJets

/-! Genuine determinant, adjugate and normal-slope finite Lp jets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

theorem hasDirichletComplexFiniteLpJets_det {n m k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A : E n → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j)) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => (A x).det) := by
  classical
  simp only [Matrix.det_apply,Units.smul_def,zsmul_eq_mul]
  apply HasDirichletComplexFiniteLpJets.finsetSum hU hμ
  intro σ _
  apply (HasDirichletComplexFiniteLpJets.const k (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul hU hμ
  exact HasDirichletComplexFiniteLpJets.finsetProd hU hμ Finset.univ (fun i _ => hA (σ i) i)

theorem hasDirichletComplexFiniteLpJets_adjugate {n m k : ℕ} {U : Set (E n)} {μ : Measure (E n)}
    [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A : E n → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j)) (i j : Fin m) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => (A x).adjugate i j) := by
  classical
  simp only [Matrix.adjugate_apply]
  apply hasDirichletComplexFiniteLpJets_det hU hμ
  intro a b
  by_cases h : a=j
  · subst a
    let row : Fin m → ℂ := Pi.single i 1
    change HasDirichletComplexFiniteLpJets U μ k (fun x => ((A x).updateRow j row) j b)
    exact (HasDirichletComplexFiniteLpJets.const k (row b)).congr hU hμ (fun _ _ => by rw [Matrix.updateRow_self])
  · simpa only [Matrix.updateRow_ne h] using hA a b

theorem hasDirichletFiniteLpJets_hermitianRankOneDetSlope {n m k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A : E n → Matrix (Fin m) (Fin m) ℂ} {z : E n → Fin m → ℂ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j))
    (hz : ∀ i, HasDirichletComplexFiniteLpJets U μ k (fun x => z x i)) :
    HasDirichletFiniteLpJets U μ k (fun x => hermitianRankOneDetSlope (A x) (z x)) := by
  have h : HasDirichletComplexFiniteLpJets U μ k
      (fun x => ∑ i, star (z x i) * ∑ j, (A x).adjugate i j * z x j) := by
    apply HasDirichletComplexFiniteLpJets.finsetSum hU hμ
    intro i _
    apply ((hz i).star hU hμ).mul hU hμ
    exact HasDirichletComplexFiniteLpJets.finsetSum hU hμ Finset.univ
      (fun j _ => (hasDirichletComplexFiniteLpJets_adjugate hU hμ hA i j).mul hU hμ (hz j))
  simpa only [hermitianRankOneDetSlope,dotProduct,Matrix.mulVec,Pi.star_apply] using h.1

theorem hasDirichletFiniteLpJets_adjugate_trace {n m k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {A D : E n → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j))
    (hD : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => D x i j)) :
    HasDirichletFiniteLpJets U μ k (fun x => ((A x).adjugate * D x).trace.re) := by
  have h : HasDirichletComplexFiniteLpJets U μ k
      (fun x => ∑ i, ∑ j, (A x).adjugate i j * D x j i) := by
    apply HasDirichletComplexFiniteLpJets.finsetSum hU hμ
    intro i _
    exact HasDirichletComplexFiniteLpJets.finsetSum hU hμ Finset.univ
      (fun j _ => (hasDirichletComplexFiniteLpJets_adjugate hU hμ hA i j).mul hU hμ (hD j i))
  simpa only [Matrix.trace,Matrix.diag,Matrix.mul_apply] using h.1

end KEBall
