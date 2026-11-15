import KEBall.DirichletBilinearFiniteLpJets
import KEBall.DirichletUnitaryTangents

/-! Finite Lp jets of the actual tangential and radial Hessian decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology
namespace KEBall

noncomputable def dirichletRadialProjectionCLM {n : ℕ} (x : E n) : E n →L[ℝ] E n :=
  (‖x‖ ^ 2)⁻¹ • (innerSL ℝ x).smulRight x

noncomputable def dirichletTangentHessianPart {n : ℕ}
    (B : E n → E n →L[ℝ] E n →L[ℝ] ℝ) (x : E n) :=
  (B x).comp (ContinuousLinearMap.id ℝ (E n) - dirichletRadialProjectionCLM x)

noncomputable def dirichletHessianNormalRemainder {n : ℕ}
    (B : E n → E n →L[ℝ] E n →L[ℝ] ℝ) (x : E n) :=
  dirichletTangentHessianPart B x +
    (dirichletTangentHessianPart B x).flip.comp (dirichletRadialProjectionCLM x)

noncomputable def dirichletHessianNormalCoefficient {n : ℕ}
    (B : E n → E n →L[ℝ] E n →L[ℝ] ℝ) (x : E n) : ℝ :=
  B x x x / (‖x‖ ^ 2) ^ 2

theorem dirichletHessian_normal_split {n : ℕ}
    (B : E n → E n →L[ℝ] E n →L[ℝ] ℝ) {x : E n} (hx : x ≠ 0)
    (hSym : ∀ a b, B x a b = B x b a) :
    B x = dirichletHessianNormalRemainder B x +
      dirichletHessianNormalCoefficient B x • (innerSL ℝ x).smulRight (innerSL ℝ x) := by
  have hNorm : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  ext a b
  simp only [dirichletHessianNormalRemainder,dirichletTangentHessianPart,
    dirichletRadialProjectionCLM,dirichletHessianNormalCoefficient,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,sub_apply,
    ContinuousLinearMap.id_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,smul_eq_mul,smul_smul,map_sub,map_smul]
  rw [hSym b x]
  field_simp
  ring

theorem hasDirichletFiniteLpJets_inner_compact {n k : ℕ} {U K : Set (E n)}
    {μ : Measure (E n)} [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (hK : IsCompact K) (hUK : U ⊆ K) (v : E n) :
    HasDirichletFiniteLpJets U μ k (fun x => inner ℝ v x) :=
  hasDirichletFiniteLpJets_of_smoothNear_compact hU hμ hK hUK
    ⟨univ,isOpen_univ,subset_univ _,(innerSL ℝ v).contDiff.contDiffOn⟩ k

theorem hasDirichletFiniteLpJets_inv_norm_sq_compact {n k : ℕ} {U K : Set (E n)}
    {μ : Measure (E n)} [IsFiniteMeasure μ] (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (hK : IsCompact K) (hUK : U ⊆ K) (hAway : ∀ x ∈ K, x ≠ 0) :
    HasDirichletFiniteLpJets U μ k (fun x => (‖x‖^2)⁻¹) := by
  apply hasDirichletFiniteLpJets_of_smoothNear_compact hU hμ hK hUK _ k
  refine ⟨{x : E n | x ≠ 0},isClosed_singleton.isOpen_compl,hAway,?_⟩
  exact (contDiff_norm_sq ℝ).contDiffOn.inv
    (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

theorem hasDirichletFiniteLpJets_tangentHessianPart {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (b : OrthonormalBasis (Fin (2*n)) ℝ (E n)) (hAway : ∀ x ∈ U, x ≠ 0)
    (hInv : HasDirichletFiniteLpJets U μ k (fun x => (‖x‖^2)⁻¹))
    (hLin : ∀ v : E n, HasDirichletFiniteLpJets U μ k (fun x => inner ℝ v x))
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hRot : ∀ i j a, HasDirichletFiniteLpJets U μ k
      (fun x => B x (dirichletUnitaryRotation (b i) (b j) x) a))
    (hJ : ∀ a, HasDirichletFiniteLpJets U μ k (fun x => B x (J x) a))
    (a c : E n) :
    HasDirichletFiniteLpJets U μ k (fun x => dirichletTangentHessianPart B x a c) := by
  classical
  let H (i : Fin (2*n)) (x : E n) : ℝ :=
    (∑ j, inner ℝ (b j) x * B x (dirichletUnitaryRotation (b i) (b j) x) c) +
      inner ℝ (J (b i)) x * B x (J x) c
  have hH (i : Fin (2*n)) : HasDirichletFiniteLpJets U μ k (H i) := by
    exact (HasDirichletFiniteLpJets.finsetSum hU hμ Finset.univ
      (fun j _ => (hLin (b j)).mul hU hμ (hRot i j c))).add hU hμ
      ((hLin (J (b i))).mul hU hμ (hJ c))
  have hSum := HasDirichletFiniteLpJets.finsetSum hU hμ Finset.univ
    (fun i _ => (HasDirichletFiniteLpJets.const k (inner ℝ (b i) a)).mul hU hμ
      (hInv.mul hU hμ (hH i)))
  refine hSum.congr hU hμ ?_
  intro x hx
  have hNorm : ‖x‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hAway x hx))
  have hEval (i : Fin (2*n)) : dirichletTangentHessianPart B x (b i) c =
      (‖x‖^2)⁻¹ * H i x := by
    have hP : (ContinuousLinearMap.id ℝ (E n) - dirichletRadialProjectionCLM x) (b i) =
        (‖x‖^2)⁻¹ • (‖x‖^2 • b i-inner ℝ (b i) x • x) := by
      simp only [dirichletRadialProjectionCLM,sub_apply,ContinuousLinearMap.id_apply,
        smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
        smul_sub,smul_smul,inv_mul_cancel₀ hNorm,one_smul,real_inner_comm x (b i)]
    change B x ((ContinuousLinearMap.id ℝ (E n)-dirichletRadialProjectionCLM x) (b i)) c = _
    rw [hP,← sum_dirichletUnitaryRotation_eq_tangentProjection b (b i) x]
    simp only [H,map_smul,map_add,map_sum,smul_apply,add_apply,sum_apply,smul_eq_mul]
  change (∑ i, inner ℝ (b i) a * ((‖x‖^2)⁻¹ * H i x)) =
    dirichletTangentHessianPart B x a c
  calc
    _ = dirichletTangentHessianPart B x (∑ i, inner ℝ (b i) a • b i) c := by
      simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,hEval]
    _ = _ := by rw [b.sum_repr']

theorem hasDirichletFiniteLpJets_normalRemainder {n k : ℕ}
    {U : Set (E n)} {μ : Measure (E n)} [IsFiniteMeasure μ]
    (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (b : OrthonormalBasis (Fin (2*n)) ℝ (E n))
    (hInv : HasDirichletFiniteLpJets U μ k (fun x => (‖x‖^2)⁻¹))
    (hLin : ∀ v : E n, HasDirichletFiniteLpJets U μ k (fun x => inner ℝ v x))
    {B : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hT : ∀ a c, HasDirichletFiniteLpJets U μ k
      (fun x => dirichletTangentHessianPart B x a c)) (a c : E n) :
    HasDirichletFiniteLpJets U μ k (fun x => dirichletHessianNormalRemainder B x a c) := by
  have hSum := HasDirichletFiniteLpJets.finsetSum hU hμ Finset.univ
    (fun j _ => (hLin (b j)).mul hU hμ (hT c (b j)))
  refine ((hT a c).add hU hμ ((hInv.mul hU hμ (hLin a)).mul hU hμ hSum)).congr hU hμ ?_
  intro x _
  change dirichletTangentHessianPart B x a c +
    ((‖x‖^2)⁻¹ * inner ℝ a x) * (∑ j, inner ℝ (b j) x * dirichletTangentHessianPart B x c (b j)) = _
  have hSumEq : (∑ j, inner ℝ (b j) x * dirichletTangentHessianPart B x c (b j)) =
      dirichletTangentHessianPart B x c x := by
    calc
      _ = dirichletTangentHessianPart B x c (∑ j, inner ℝ (b j) x • b j) := by
        simp only [map_sum,map_smul,smul_eq_mul]
      _ = _ := by rw [b.sum_repr']
  rw [hSumEq]
  simp only [dirichletHessianNormalRemainder,dirichletRadialProjectionCLM,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,map_smul,smul_eq_mul,
    real_inner_comm x a,mul_assoc]

end KEBall
