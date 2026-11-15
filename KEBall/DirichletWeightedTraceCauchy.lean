import KEBall.DirichletPositiveTraceRatio

/-! The invariant weighted Cauchy inequality for the third derivative tensor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 200000
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace KEBall
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_product_nonneg {M N : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) : 0≤(M*N).trace.re := by
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  change M=Rᴴ*R at hR
  rw [hR,← Matrix.trace_mul_cycle]
  exact (RCLike.nonneg_iff.mp (hN.mul_mul_conjTranspose_same R).trace_nonneg).1

private theorem trace_pair_nonneg {M : Matrix ι ι ℂ} (hM : M.PosSemidef)
    (B : Matrix ι ι ℂ) : 0≤(M*B*M*Bᴴ).trace.re := by
  simpa only [mul_assoc] using trace_product_nonneg hM (hM.mul_mul_conjTranspose_same B)

private theorem trace_pair_re_symm {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (B D : Matrix ι ι ℂ) :
    (M*D*M*Bᴴ).trace.re=(M*B*M*Dᴴ).trace.re := by
  calc
    _ = (D*M*Bᴴ*M).trace.re := by
      simpa only [mul_assoc] using congrArg Complex.re (Matrix.trace_mul_comm M (D*M*Bᴴ))
    _ = ((M*B*M*Dᴴ)ᴴ).trace.re := by
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hM.eq,mul_assoc]
    _ = _ := by simp only [Matrix.trace_conjTranspose,Complex.star_def,Complex.conj_re]

private theorem trace_pair_smul_sub (M B D : Matrix ι ι ℂ) (t : ℝ) :
    (M*(t • B-D)*M*(t • B-D)ᴴ).trace.re=
      t^2*(M*B*M*Bᴴ).trace.re-t*(M*B*M*Dᴴ).trace.re-
        t*(M*D*M*Bᴴ).trace.re+(M*D*M*Dᴴ).trace.re := by
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,star_trivial,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,
    Matrix.trace_sub,Matrix.trace_smul,Complex.sub_re,Complex.real_smul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- Contracting the third derivative tensor in the derivative/column indices
is bounded by its exact inverse-Hessian quadratic form times the Hessian trace. -/
theorem dirichlet_weighted_trace_cauchy [Nonempty ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) (B : ι → Matrix ι ι ℂ) :
    let w : ι → ℂ := fun i => ∑ k, B k i k
    (star w ⬝ᵥ (A⁻¹ *ᵥ w)).re ≤
      A.trace.re * ∑ k, (A⁻¹*B k*A⁻¹*(B k)ᴴ).trace.re := by
  classical
  let M := A⁻¹
  let w : ι → ℂ := fun i => ∑ k, B k i k
  let e (k : ι) : ι → ℂ := Pi.single k 1
  let D (k : ι) : Matrix ι ι ℂ := Matrix.vecMulVec w (fun j => A k j)
  let t := A.trace.re
  let c := (star w ⬝ᵥ (M *ᵥ w)).re
  let Q := ∑ k, (M*B k*M*(B k)ᴴ).trace.re
  have ht : 0<t := dirichlet_posDef_trace_re_pos hA
  have hM : M.PosDef := hA.inv
  have hUnit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hRow (k : ι) : (fun j => A k j) ᵥ* M=e k := by
    funext j
    change (A*M) k j=(Pi.single k (1 : ℂ) : ι → ℂ) j
    rw [Matrix.mul_nonsing_inv A hUnit]
    simp only [Matrix.one_apply,Pi.single_apply]
    by_cases h : k=j
    · subst j; simp
    · simp only [h,Ne.symm h,ite_false]
  have hDM (k : ι) : D k*M=Matrix.vecMulVec w (e k) := by
    dsimp only [D]
    rw [Matrix.vecMulVec_mul,hRow]
  have hMD (k : ι) : M*(D k)ᴴ=Matrix.vecMulVec (e k) (star w) := by
    have h := congrArg Matrix.conjTranspose (hDM k)
    have he : star (e k)=e k := by
      funext i
      simp only [e,Pi.star_apply,Pi.single_apply]
      split_ifs <;> simp
    simpa only [Matrix.conjTranspose_mul,hM.isHermitian.eq,Matrix.conjTranspose_vecMulVec,he] using h
  have hw : (∑ k, B k *ᵥ e k)=w := by
    funext i
    simp only [Finset.sum_apply,e,Matrix.mulVec_single_one,w]
    rfl
  have hCross (k : ι) : (M*B k*M*(D k)ᴴ).trace=
      star w ⬝ᵥ (M *ᵥ (B k *ᵥ e k)) := by
    rw [mul_assoc (M*B k) M,hMD,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,
      dotProduct_comm,← Matrix.mulVec_mulVec]
  have hCrossSum : (∑ k, (M*B k*M*(D k)ᴴ).trace.re)=c := by
    simp_rw [hCross]
    rw [← Complex.re_sum,← dotProduct_sum,← Matrix.mulVec_sum,hw]
  have hCrossSum' : (∑ k, (M*D k*M*(B k)ᴴ).trace.re)=c := by
    simpa only [trace_pair_re_symm hM.isHermitian] using hCrossSum
  have hDVec (k : ι) : D k *ᵥ e k=A k k • w := by
    dsimp only [e]
    rw [Matrix.mulVec_single_one]
    funext i
    simp only [D,Matrix.col_apply,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  have hQuad (k : ι) : (M*D k*M*(D k)ᴴ).trace=
      A k k*(star w ⬝ᵥ (M *ᵥ w)) := by
    rw [mul_assoc (M*D k) M,hMD,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,
      dotProduct_comm,← Matrix.mulVec_mulVec,hDVec,Matrix.mulVec_smul,dotProduct_smul]
    rfl
  have htIm : A.trace.im=0 := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues,← RCLike.ofReal_sum]
    rfl
  have hQuadSum : (∑ k, (M*D k*M*(D k)ᴴ).trace.re)=t*c := by
    simp_rw [hQuad]
    rw [← Complex.re_sum,← Finset.sum_mul]
    change (A.trace*(star w ⬝ᵥ (M *ᵥ w))).re=t*c
    simp only [Complex.mul_re,htIm,zero_mul,sub_zero,t,c]
  have hNonneg : 0≤∑ k, (M*(t • B k-D k)*M*(t • B k-D k)ᴴ).trace.re :=
    Finset.sum_nonneg fun k _ => trace_pair_nonneg hM.posSemidef _
  simp_rw [trace_pair_smul_sub] at hNonneg
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hCrossSum,hCrossSum',hQuadSum] at hNonneg
  change 0≤t^2*Q-t*c-t*c+t*c at hNonneg
  have hProduct : 0≤t*(t*Q-c) := by nlinarith only [hNonneg]
  have h := (mul_nonneg_iff_of_pos_left ht).mp hProduct
  exact sub_nonneg.mp h

end KEBall
