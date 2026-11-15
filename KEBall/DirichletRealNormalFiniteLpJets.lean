import KEBall.DirichletNormalFiniteLpJets

/-! The fixed complex-Hessian normalization and recovery of genuine real Hessian entries. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem hasDirichletComplexFiniteLpJets_complexHessianOfRealBilinear {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hB : ∀ a b, HasDirichletFiniteLpJets U μ k (fun x => B x a b)) (i j : Fin n) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => complexHessianOfRealBilinear (B x) i j) := by
  exact (HasDirichletComplexFiniteLpJets.const k ((4 : ℂ)⁻¹)).mul hU hμ
    ((((hB (realDirection i) (realDirection j)).ofReal).add hU hμ
      (hB (imagDirection i) (imagDirection j)).ofReal).add hU hμ
        ((HasDirichletComplexFiniteLpJets.const k Complex.I).mul hU hμ
          (((hB (realDirection i) (imagDirection j)).ofReal).sub hU hμ
            (hB (imagDirection i) (realDirection j)).ofReal)))

theorem hasDirichletComplexFiniteLpJets_complexCoord_compact {n k : ℕ}
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K) (i : Fin n) :
    HasDirichletComplexFiniteLpJets U μ k (fun x => complexCoord x i) := by
  have hRe : ContDiff ℝ ∞ (fun x : E n => (complexCoord x i).re) :=
    Complex.reCLM.contDiff.comp (complexCoordCLM i).contDiff
  have hIm : ContDiff ℝ ∞ (fun x : E n => (complexCoord x i).im) :=
    Complex.imCLM.contDiff.comp (complexCoordCLM i).contDiff
  exact ⟨hasDirichletFiniteLpJets_of_smoothNear_compact hU hμ hK hUK
      ⟨univ,isOpen_univ,subset_univ _,hRe.contDiffOn⟩ k,
    hasDirichletFiniteLpJets_of_smoothNear_compact hU hμ hK hUK
      ⟨univ,isOpen_univ,subset_univ _,hIm.contDiffOn⟩ k⟩

theorem hasDirichletFiniteLpJets_realBilinear_of_rankOne_linearized_det {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (hLin : ∀ a, HasDirichletFiniteLpJets U μ k (fun x => inner ℝ a x))
    (hz : ∀ i, HasDirichletComplexFiniteLpJets U μ k (fun x => star (complexCoord x i)))
    (hAway : ∀ x ∈ U, x ≠ 0)
    {B D : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    {A : E n → Matrix (Fin n) (Fin n) ℂ} {t f : E n → ℝ}
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j))
    (hD : ∀ a b, HasDirichletFiniteLpJets U μ k (fun x => D x a b))
    (hP : ∀ x ∈ U, (A x).PosDef) (hf : HasDirichletFiniteLpJets U μ k f)
    {C : ℝ} (hBound : ∀ x ∈ U,
      ‖(hermitianRankOneDetSlope (A x) (star (complexCoord x)))⁻¹‖ ≤ C)
    (hSplit : ∀ x ∈ U, B x=D x+t x • (innerSL ℝ x).smulRight (innerSL ℝ x))
    (hEq : ∀ x ∈ U, ((A x).adjugate * complexHessianOfRealBilinear (B x)).trace.re=f x)
    (a b : E n) : HasDirichletFiniteLpJets U μ k (fun x => B x a b) := by
  have hz0 (x : E n) (hx : x ∈ U) : star (complexCoord x) ≠ 0 := by
    intro h
    apply hAway x hx
    apply complexCoord_eq_zero_iff.mp
    simpa only [star_star,star_zero] using congrArg star h
  have hs : HasDirichletFiniteLpJets U μ k (fun x => t x/4) := by
    refine hasDirichletFiniteLpJets_of_rankOne_linearized_det (z := fun x => star (complexCoord x)) hU hμ hA
      (hasDirichletComplexFiniteLpJets_complexHessianOfRealBilinear hU hμ hD)
      hz hP hz0 hf hBound ?_
    intro x hx
    have he := complexHessianOfRealBilinear_add_rankOne (D x) x (t x)
    rw [← hSplit x hx] at he
    simpa only [star_star,← he] using hEq x hx
  have ht : HasDirichletFiniteLpJets U μ k t :=
    ((HasDirichletFiniteLpJets.const k (4 : ℝ)).mul hU hμ hs).congr hU hμ
      (fun x _ => by change 4*(t x/4)=t x; ring)
  refine ((hD a b).add hU hμ ((ht.mul hU hμ (hLin a)).mul hU hμ (hLin b))).congr hU hμ ?_
  intro x hx
  change D x a b+t x*inner ℝ a x*inner ℝ b x=B x a b
  rw [hSplit x hx]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    smul_eq_mul,real_inner_comm x a,real_inner_comm x b]
  ring

theorem hasDirichletFiniteLpJets_realBilinear_of_rankOne_det {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (hLin : ∀ a, HasDirichletFiniteLpJets U μ k (fun x => inner ℝ a x))
    (hz : ∀ i, HasDirichletComplexFiniteLpJets U μ k (fun x => star (complexCoord x i)))
    (hAway : ∀ x ∈ U, x ≠ 0)
    {B D : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {t f : E n → ℝ}
    (hD : ∀ a b, HasDirichletFiniteLpJets U μ k (fun x => D x a b))
    (hf : HasDirichletFiniteLpJets U μ k f) (c : ℝ)
    (hP : ∀ x ∈ U, (complexHessianOfRealBilinear
      (D x+c • (innerSL ℝ x).smulRight (innerSL ℝ x))).PosDef)
    {C : ℝ} (hBound : ∀ x ∈ U, ‖(hermitianRankOneDetSlope
      (complexHessianOfRealBilinear (D x+c • (innerSL ℝ x).smulRight (innerSL ℝ x)))
      (star (complexCoord x)))⁻¹‖ ≤ C)
    (hSplit : ∀ x ∈ U, B x=D x+t x • (innerSL ℝ x).smulRight (innerSL ℝ x))
    (hEq : ∀ x ∈ U, (complexHessianOfRealBilinear (B x)).det.re=f x)
    (a b : E n) : HasDirichletFiniteLpJets U μ k (fun x => B x a b) := by
  let P (x : E n) := (innerSL ℝ x).smulRight (innerSL ℝ x)
  let A (x : E n) := complexHessianOfRealBilinear (D x+c • P x)
  have hA (i j : Fin n) : HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j) := by
    apply hasDirichletComplexFiniteLpJets_complexHessianOfRealBilinear hU hμ
    intro v w
    refine ((hD v w).add hU hμ (((HasDirichletFiniteLpJets.const k c).mul hU hμ
      (hLin v)).mul hU hμ (hLin w))).congr hU hμ ?_
    intro x _
    change D x v w+c*inner ℝ v x*inner ℝ w x=(D x+c • P x) v w
    simp only [P,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply,smul_eq_mul,real_inner_comm x v,real_inner_comm x w]
    ring
  have hz0 (x : E n) (hx : x ∈ U) : star (complexCoord x) ≠ 0 := by
    intro h
    apply hAway x hx
    apply complexCoord_eq_zero_iff.mp
    simpa only [star_star,star_zero] using congrArg star h
  have hs : HasDirichletFiniteLpJets U μ k (fun x => (t x-c)/4) := by
    refine hasDirichletFiniteLpJets_of_rankOne_det (z := fun x => star (complexCoord x)) hU hμ hA hz hP hz0 hf hBound ?_
    intro x hx
    have hShift : D x+c • P x+(t x-c) • P x=D x+t x • P x := by
      rw [add_assoc,← add_smul]
      congr 2
      ring
    have he := complexHessianOfRealBilinear_add_rankOne (D x+c • P x) x (t x-c)
    change complexHessianOfRealBilinear (D x+c • P x+(t x-c) • P x)=_ at he
    rw [hShift,← hSplit x hx] at he
    simpa only [A,star_star,← he] using hEq x hx
  have ht : HasDirichletFiniteLpJets U μ k t :=
    (((HasDirichletFiniteLpJets.const k (4 : ℝ)).mul hU hμ hs).add hU hμ
      (HasDirichletFiniteLpJets.const k c)).congr hU hμ
      (fun x _ => by change 4*((t x-c)/4)+c=t x; ring)
  refine ((hD a b).add hU hμ ((ht.mul hU hμ (hLin a)).mul hU hμ (hLin b))).congr hU hμ ?_
  intro x hx
  change D x a b+t x*inner ℝ a x*inner ℝ b x=B x a b
  rw [hSplit x hx]
  simp only [P,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    smul_eq_mul,real_inner_comm x a,real_inner_comm x b]
  ring

end KEBall
