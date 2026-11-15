import KEBall.DirichletTangentFiniteLpJets
import KEBall.DirichletRealNormalFiniteLpJets
import KEBall.DirichletCompactNormalSlope

/-! Compact annular normal recovery with no unproved lower-bound assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 900000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

theorem continuousOn_dirichletHessianNormalCoefficient {n : ℕ} {K : Set (E n)}
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} (hB : ContinuousOn B K)
    (hAway : ∀ x ∈ K, x ≠ 0) :
    ContinuousOn (dirichletHessianNormalCoefficient B) K := by
  exact ((hB.clm_apply continuousOn_id).clm_apply continuousOn_id).div
    (continuous_norm.continuousOn.pow 2 |>.pow 2)
    (fun x hx => pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hAway x hx))))

theorem continuousOn_dirichletHessianNormalRemainder {n : ℕ} {K : Set (E n)}
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} (hB : ContinuousOn B K)
    (hAway : ∀ x ∈ K, x ≠ 0) :
    ContinuousOn (dirichletHessianNormalRemainder B) K := by
  have hR : ContDiffOn ℝ 0 (fun x : E n => (‖x‖^2)⁻¹) K :=
    (contDiff_norm_sq ℝ).contDiffOn.inv
      (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr (hAway x hx)))
  have hL : ContDiffOn ℝ 0 (fun x : E n => innerSL ℝ x) K :=
    (innerSL ℝ (E := E n)).contDiff.contDiffOn
  have hN : ContDiffOn ℝ 0 (dirichletRadialProjectionCLM : E n → E n →L[ℝ] E n) K := by
    refine ((hR.smul hL).smulRight contDiffOn_id).congr fun x _ => ?_
    ext a : 1
    simp [dirichletRadialProjectionCLM,smul_smul]
  have hT : ContDiffOn ℝ 0 (dirichletTangentHessianPart B) K :=
    (contDiffOn_zero.mpr hB).clm_comp (contDiffOn_const.sub hN)
  let F : (E n →L[ℝ] E n →L[ℝ] ℝ) ≃L[ℝ] (E n →L[ℝ] E n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toContinuousLinearEquiv
  have hFlip : ContDiffOn ℝ 0 (fun x => (dirichletTangentHessianPart B x).flip) K :=
    F.contDiff.comp_contDiffOn hT
  exact (hT.add (hFlip.clm_comp hN)).continuousOn

theorem hasDirichletFiniteLpJets_realBilinear_of_compact_tangent_det {n k : ℕ}
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hAway : ∀ x ∈ K, x ≠ 0) (b : OrthonormalBasis (Fin (2*n)) ℝ (E n))
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ} {f : E n → ℝ}
    (hBC : ContinuousOn B K) (hSym : ∀ x ∈ K, ∀ a c, B x a c=B x c a)
    (hT : ∀ a c, HasDirichletFiniteLpJets U μ k (fun x => dirichletTangentHessianPart B x a c))
    (hf : HasDirichletFiniteLpJets U μ k f)
    (hPos : ∀ x ∈ K, (complexHessianOfRealBilinear (B x)).PosDef)
    (hEq : ∀ x ∈ U, (complexHessianOfRealBilinear (B x)).det.re=f x) (a c : E n) :
    HasDirichletFiniteLpJets U μ k (fun x => B x a c) := by
  let D := dirichletHessianNormalRemainder B
  let t := dirichletHessianNormalCoefficient B
  have hLin := hasDirichletFiniteLpJets_inner_compact (k := k) hU hμ hK hUK
  have hInv := hasDirichletFiniteLpJets_inv_norm_sq_compact (k := k) hU hμ hK hUK hAway
  have hD := hasDirichletFiniteLpJets_normalRemainder hU hμ b hInv hLin hT
  have hDC : ContinuousOn D K := continuousOn_dirichletHessianNormalRemainder hBC hAway
  have htC : ContinuousOn t K := continuousOn_dirichletHessianNormalCoefficient hBC hAway
  have hSplit (x : E n) (hx : x ∈ K) : B x=D x+t x • (innerSL ℝ x).smulRight (innerSL ℝ x) :=
    dirichletHessian_normal_split B (hAway x hx) (hSym x hx)
  obtain ⟨d,hd⟩ := exists_positive_realHessian_rankOne_reference hK htC hSplit hPos
  let A (x : E n) := complexHessianOfRealBilinear (D x+d • (innerSL ℝ x).smulRight (innerSL ℝ x))
  let z (x : E n) := star (complexCoord x)
  have hL : ContDiffOn ℝ 0 (fun x : E n => innerSL ℝ x) K :=
    (innerSL ℝ (E := E n)).contDiff.contDiffOn
  have hAC : ContinuousOn A K := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (contDiffOn_complexHessianOfRealBilinear
      ((contDiffOn_zero.mpr hDC).add ((hL.smulRight hL).const_smul d)) i j).continuousOn
  have hzC : ContinuousOn z K := continuousOn_pi.mpr fun i =>
    (Complex.conjCLE.continuous.comp (complexCoordCLM i).continuous).continuousOn
  have hz0 (x : E n) (hx : x ∈ K) : z x ≠ 0 := by
    intro h
    apply hAway x hx
    apply complexCoord_eq_zero_iff.mp
    simpa only [z,star_star,star_zero] using congrArg star h
  obtain ⟨C,_,hC⟩ := exists_uniform_inverse_hermitianRankOneDetSlope hK hAC hzC hd hz0
  exact hasDirichletFiniteLpJets_realBilinear_of_rankOne_det hU hμ hLin
    (fun i => (hasDirichletComplexFiniteLpJets_complexCoord_compact hU hμ hK hUK i).star hU hμ)
    (fun x hx => hAway x (hUK hx)) hD hf d (fun x hx => hd x (hUK hx))
    (fun x hx => hC x (hUK hx)) (fun x hx => hSplit x (hUK hx)) hEq a c

theorem hasDirichletFiniteLpJets_realBilinear_of_compact_tangent_linearized_det {n k : ℕ}
    {U K : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U) (hK : IsCompact K) (hUK : U ⊆ K)
    (hAway : ∀ x ∈ K, x ≠ 0) (b : OrthonormalBasis (Fin (2*n)) ℝ (E n))
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    {A : E n → Matrix (Fin n) (Fin n) ℂ} {f : E n → ℝ}
    (hSym : ∀ x ∈ U, ∀ a c, B x a c=B x c a)
    (hT : ∀ a c, HasDirichletFiniteLpJets U μ k (fun x => dirichletTangentHessianPart B x a c))
    (hAC : ContinuousOn A K)
    (hA : ∀ i j, HasDirichletComplexFiniteLpJets U μ k (fun x => A x i j))
    (hPos : ∀ x ∈ K, (A x).PosDef) (hf : HasDirichletFiniteLpJets U μ k f)
    (hEq : ∀ x ∈ U, ((A x).adjugate * complexHessianOfRealBilinear (B x)).trace.re=f x)
    (a c : E n) : HasDirichletFiniteLpJets U μ k (fun x => B x a c) := by
  let D := dirichletHessianNormalRemainder B
  let t := dirichletHessianNormalCoefficient B
  let z (x : E n) := star (complexCoord x)
  have hLin := hasDirichletFiniteLpJets_inner_compact (k := k) hU hμ hK hUK
  have hInv := hasDirichletFiniteLpJets_inv_norm_sq_compact (k := k) hU hμ hK hUK hAway
  have hD := hasDirichletFiniteLpJets_normalRemainder hU hμ b hInv hLin hT
  have hSplit (x : E n) (hx : x ∈ U) : B x=D x+t x • (innerSL ℝ x).smulRight (innerSL ℝ x) :=
    dirichletHessian_normal_split B (hAway x (hUK hx)) (hSym x hx)
  have hzC : ContinuousOn z K := continuousOn_pi.mpr fun i =>
    (Complex.conjCLE.continuous.comp (complexCoordCLM i).continuous).continuousOn
  have hz0 (x : E n) (hx : x ∈ K) : z x ≠ 0 := by
    intro h
    apply hAway x hx
    apply complexCoord_eq_zero_iff.mp
    simpa only [z,star_star,star_zero] using congrArg star h
  obtain ⟨C,_,hC⟩ := exists_uniform_inverse_hermitianRankOneDetSlope hK hAC hzC hPos hz0
  exact hasDirichletFiniteLpJets_realBilinear_of_rankOne_linearized_det hU hμ hLin
    (fun i => (hasDirichletComplexFiniteLpJets_complexCoord_compact hU hμ hK hUK i).star hU hμ)
    (fun x hx => hAway x (hUK hx)) hA hD (fun x hx => hPos x (hUK hx)) hf
    (fun x hx => hC x (hUK hx)) hSplit hEq a c

end KEBall
