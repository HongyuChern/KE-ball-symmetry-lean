import KEBall.BedfordTaylorCoordinates
import KEBall.LogDetConcavity
import KEBall.SphereMeasure
import KEBall.ComplexMaximum
import KEBall.FiberEnergyGreen
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Matrix.Order

/-! # The real gradient determinant and the complex Hessian -/

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped ContDiff Gradient Matrix ComplexOrder MatrixOrder Topology

namespace KEBall

private theorem det_le_det_of_posSemidef_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosDef) (hBA : (B - A).PosSemidef) :
    A.det ≤ B.det := by
  let S := CFC.sqrt B
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hSq : S * S = B := by
    rw [← sq]
    change CFC.sqrt B ^ 2 = B
    exact CFC.sq_sqrt B hB.posSemidef.nonneg
  have hSD : S.det * S.det = B.det := by rw [← Matrix.det_mul, hSq]
  have hSdet : S.det ≠ 0 := by
    intro h
    rw [h, zero_mul] at hSD
    exact hB.det_pos.ne' hSD.symm
  have hSunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  let T := S⁻¹
  have hT : T.PosSemidef := hS.inv
  have hTB : T * B * T = 1 := by
    rw [← hSq, ← mul_assoc, show T * S = 1 from Matrix.nonsing_inv_mul _ hSunit,
      one_mul, show S * T = 1 from Matrix.mul_nonsing_inv _ hSunit]
  let C := T * A * T
  have hC : C.PosSemidef := by
    simpa only [hT.isHermitian.eq] using hA.mul_mul_conjTranspose_same T
  have hDiff : (1 - C).PosSemidef := by
    have h := hBA.mul_mul_conjTranspose_same T
    rw [hT.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul, hTB] at h
    exact h
  have hEig (i : ι) : hC.isHermitian.eigenvalues i ≤ 1 := by
    let v : ι → ℝ := hC.isHermitian.eigenvectorBasis i
    have hv : C *ᵥ v = hC.isHermitian.eigenvalues i • v :=
      hC.isHermitian.mulVec_eigenvectorBasis i
    have hs : star v ⬝ᵥ v = 1 := by
      rw [dotProduct_comm]
      change (hC.isHermitian.eigenvectorBasis i).ofLp ⬝ᵥ
        star (hC.isHermitian.eigenvectorBasis i).ofLp = 1
      rw [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hC.isHermitian.eigenvectorBasis.orthonormal.1 i]
      simp
    have h := hDiff.dotProduct_mulVec_nonneg v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, dotProduct_sub, dotProduct_smul, hs] at h
    simpa only [smul_eq_mul, mul_one, sub_nonneg] using h
  have hCD : C.det ≤ 1 := by
    rw [hC.isHermitian.det_eq_prod_eigenvalues]
    exact Finset.prod_le_one (fun i _ => hC.eigenvalues_nonneg i) (fun i _ => hEig i)
  have hTD : T.det * B.det * T.det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, hTB, Matrix.det_one]
  have hTpos : 0 < T.det * T.det := by
    have hpos := mul_self_nonneg T.det
    exact lt_of_le_of_ne hpos (by intro h; nlinarith only [hTD, congrArg (fun x => x * B.det) h])
  apply le_of_mul_le_mul_left _ hTpos
  change (T.det * T.det) * A.det ≤ (T.det * T.det) * B.det
  calc
    (T.det * T.det) * A.det = C.det := by simp [C, Matrix.det_mul]; ring
    _ ≤ 1 := hCD
    _ = (T.det * T.det) * B.det := by rw [← hTD]; ring

private theorem det_le_det_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) (hBA : (B - A).PosSemidef) :
    A.det ≤ B.det := by
  have hCont : Continuous (fun t : ℝ => (B + t • (1 : Matrix ι ι ℝ)).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hLim : Tendsto (fun t : ℝ => (B + t • (1 : Matrix ι ι ℝ)).det) (𝓝[>] 0) (𝓝 B.det) := by
    have h : Tendsto (fun t : ℝ => (B + t • (1 : Matrix ι ι ℝ)).det) (𝓝[>] 0)
        (𝓝 (B + (0 : ℝ) • 1).det) := hCont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [zero_smul, add_zero] using h
  apply ge_of_tendsto hLim
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
  have hT : (t • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul (show 0 < t from ht)
  apply det_le_det_of_posSemidef_sub hA (Matrix.PosDef.posSemidef_add hB hT)
  simpa only [add_sub_right_comm] using hBA.add hT.posSemidef

private theorem det_toDual_symm_realification {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    ((InnerProductSpace.toDual ℝ (E n)).symm.toLinearEquiv.toLinearMap ∘ₗ
      (hermitianRealification A).toLinearMap).det =
      (2 : ℝ) ^ (2 * n) * A.det.re ^ 2 := by
  let e := complexCoordinates n
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let M : Matrix (Fin n) (Fin n) ℂ := (2 : ℂ) • A.transpose
  let F := M.toLin b b
  let D := (e.symm.toLinearEquiv : _ →ₗ[ℝ] E n) ∘ₗ (F.restrictScalars ℝ) ∘ₗ
    (e.toLinearEquiv : E n →ₗ[ℝ] _)
  have hD : (InnerProductSpace.toDual ℝ (E n)).symm.toLinearEquiv.toLinearMap ∘ₗ
      (hermitianRealification A).toLinearMap = D := by
    ext v : 1
    apply (InnerProductSpace.toDual ℝ (E n)).injective
    ext w : 1
    have h : ∀ j, (F (e v)) j = (M *ᵥ (complexCoord v)) j := by
      intro j
      have he := M.repr_toLin b b (e v)
      change ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.repr (F (e v))) =
        M *ᵥ ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.repr (e v)) at he
      have hrepr (x : EuclideanSpace ℂ (Fin n)) :
          ⇑((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.repr x) = x.ofLp := by
        funext i
        rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
      have hv : (e v).ofLp = complexCoord v := by funext i; exact complexCoordinates_apply n v i
      rw [hrepr, hrepr, hv] at he
      exact congrFun he j
    change (InnerProductSpace.toDual ℝ (E n))
        ((InnerProductSpace.toDual ℝ (E n)).symm (hermitianRealification A v)) w =
      (InnerProductSpace.toDual ℝ (E n)) (D v) w
    rw [LinearIsometryEquiv.apply_symm_apply]
    change hermitianRealification A v w = inner ℝ (e.symm (F (e v))) w
    rw [← e.inner_map_map, e.apply_symm_apply]
    have hInner (z w : EuclideanSpace ℂ (Fin n)) : inner ℝ z w = (inner ℂ z w).re := by
      rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
      rfl
    rw [hInner, show (inner ℂ (F (e v)) (e w)).re = (inner ℂ (e w) (F (e v))).re from
      inner_re_symm (𝕜 := ℂ) _ _, EuclideanSpace.inner_eq_star_dotProduct, hermitianRealification_apply]
    simp only [dotProduct, Pi.star_apply, h, M, Matrix.mulVec, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show (e w).ofLp i = complexCoord w i from rfl]
    norm_num [Complex.mul_re, Complex.mul_im]
    ring
  have hReal : A.det = (A.det.re : ℂ) := by
    have hd := hA.det_eq_prod_eigenvalues
    rw [← RCLike.ofReal_prod] at hd
    change A.det = (((∏ i, hA.eigenvalues i) : ℝ) : ℂ) at hd
    rw [hd, Complex.ofReal_re]
  rw [hD, show D.det = (F.restrictScalars ℝ).det from LinearMap.det_conj _ e.symm.toLinearEquiv,
    LinearMap.det_restrictScalars, show F.det = M.det from LinearMap.det_toLin b M,
    Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, hReal,
    map_mul, map_pow, Algebra.norm_complex_apply (A.det.re : ℂ), Complex.normSq_ofReal,
    Complex.ofReal_re, show Algebra.norm ℝ (2 : ℂ) = 2 ^ 2 by
      norm_num [Algebra.norm_complex_apply, Complex.normSq_apply], ← pow_mul, pow_two A.det.re]

private noncomputable def bilinearOperator {n : ℕ}
    (L : E n →L[ℝ] E n →L[ℝ] ℝ) : E n →ₗ[ℝ] E n :=
  (InnerProductSpace.toDual ℝ (E n)).symm.toLinearEquiv.toLinearMap ∘ₗ L.toLinearMap

private theorem inner_bilinearOperator {n : ℕ}
    (L : E n →L[ℝ] E n →L[ℝ] ℝ) (v w : E n) :
    inner ℝ (bilinearOperator L v) w = L v w := by
  exact congrFun (congrArg DFunLike.coe
    ((InnerProductSpace.toDual ℝ (E n)).apply_symm_apply (L v))) w

private noncomputable def bilinearMatrix {n : ℕ} (L : E n →L[ℝ] E n →L[ℝ] ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  LinearMap.toMatrix b b (bilinearOperator L)

private theorem bilinearMatrix_isHermitian {n : ℕ} {L : E n →L[ℝ] E n →L[ℝ] ℝ}
    (hL : ∀ v w, L v w = L w v) : (bilinearMatrix L).IsHermitian := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  have h (i j : Fin (2 * n)) : bilinearMatrix L i j = L (b j) (b i) := by
    rw [bilinearMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    change b.repr (bilinearOperator L (b j)) i = _
    rw [b.repr_apply_apply, real_inner_comm, inner_bilinearOperator]
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, h, hL (b i) (b j)]

private theorem dotProduct_bilinearMatrix {n : ℕ} (L : E n →L[ℝ] E n →L[ℝ] ℝ)
    (z : Fin (2 * n) → ℝ) :
    star z ⬝ᵥ (bilinearMatrix L *ᵥ z) = L (WithLp.toLp 2 z) (WithLp.toLp 2 z) := by
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  let v : E n := WithLp.toLp 2 z
  have hrepr (w : E n) : ⇑(b.repr w) = w.ofLp := by
    funext i
    rw [show b = (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis from rfl,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  have h := LinearMap.toMatrix_mulVec_repr b b (bilinearOperator L) v
  rw [hrepr, hrepr] at h
  change bilinearMatrix L *ᵥ z = (bilinearOperator L v).ofLp at h
  rw [h, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    real_inner_comm, inner_bilinearOperator]

theorem complexHessian_posSemidef_of_realHessian_nonneg {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hR : ∀ v, 0 ≤ realHessian u x v v) :
    (complexHessian u x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨MoserTrudinger.complexHessian_isHermitian_of_smooth hu, fun z => ?_⟩
  obtain ⟨v, hv⟩ := complexCoord_surjective (star z)
  have h := add_nonneg (hR v) (hR (J v))
  have hMetric : 0 ≤ realMetricForm u x v v := by
    rw [realMetricForm_eq_average_hessian hu]
    exact div_nonneg h (by norm_num)
  rw [realMetricForm_eq, hermitianRealification_apply, hv] at hMetric
  simp only [Pi.star_apply, star_star] at hMetric
  have hQ := nonneg_of_mul_nonneg_right hMetric (by norm_num : 0 < (2 : ℝ))
  have hRe : 0 ≤ (star z ⬝ᵥ (complexHessian u x *ᵥ z)).re := by
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc, mul_left_comm] using hQ
  exact RCLike.nonneg_iff.mpr
    ⟨hRe, (MoserTrudinger.complexHessian_isHermitian_of_smooth hu).im_star_dotProduct_mulVec_self z⟩

/-- On the real positive-semidefinite locus, the real gradient Jacobian is
bounded by a constant times the square of the complex determinant. -/
theorem abs_det_gradient_le_complexDet_sq {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (complexHessian u x).PosSemidef)
    (hR : ∀ v, 0 ≤ realHessian u x v v) :
    |(fderiv ℝ (∇ u) x).det| ≤ (4 : ℝ) ^ (2 * n) * (complexHessian u x).det.re ^ 2 := by
  let R := realHessian u x
  let H := hermitianRealification (complexHessian u x)
  let A := bilinearMatrix R
  let B := bilinearMatrix ((2 : ℝ) • H)
  have hA : A.PosSemidef := Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨bilinearMatrix_isHermitian (realHessian_symm hu), fun z => by
      rw [show A = bilinearMatrix R from rfl, dotProduct_bilinearMatrix]
      exact hR _⟩
  have hHs (v w : E n) : H v w = H w v := hermitianRealification_symm hp.isHermitian v w
  have hRs (v w : E n) : R v w = R w v := realHessian_symm hu v w
  have hB : B.PosSemidef := Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨bilinearMatrix_isHermitian (fun v w => by simp only [smul_apply, hHs v w]), fun z => by
      rw [show B = bilinearMatrix ((2 : ℝ) • H) from rfl, dotProduct_bilinearMatrix]
      let v : E n := WithLp.toLp 2 z
      change 0 ≤ 2 * hermitianRealification (complexHessian u x) v v
      rw [hermitianRealification_apply]
      have h := hp.re_dotProduct_nonneg (star (complexCoord v))
      change 0 ≤ Complex.re _ at h
      have hQ : 0 ≤ (∑ i : Fin n, ∑ j : Fin n, complexHessian u x i j *
          complexCoord v i * star (complexCoord v j)).re := by
        simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, star_star,
          mul_assoc, mul_left_comm] using h
      positivity⟩
  have hBAEq : B - A = bilinearMatrix ((2 : ℝ) • H - R) := by
    simp only [B, A, bilinearMatrix, bilinearOperator, ContinuousLinearMap.toLinearMap_sub,
      LinearMap.comp_sub, map_sub]
  have hBA : (B - A).PosSemidef := by
    rw [hBAEq, Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨bilinearMatrix_isHermitian (fun v w => by
      simp only [sub_apply, smul_apply, hHs v w, hRs v w]), fun z => ?_⟩
    rw [dotProduct_bilinearMatrix]
    let v : E n := WithLp.toLp 2 z
    change 0 ≤ 2 * H v v - realHessian u x v v
    rw [show H v v = realMetricForm u x v v from (realMetricForm_eq u x v v).symm,
      realMetricForm_eq_average_hessian hu]
    linarith only [hR (J v)]
  have hD : (fderiv ℝ (∇ u) x).toLinearMap = bilinearOperator R := by
    have h := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have h' := ((InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.hasFDerivAt
      (x := fderiv ℝ u x)).comp x h
    change HasFDerivAt (∇ u) _ x at h'
    rw [h'.fderiv]
    rfl
  have hDetA : (fderiv ℝ (∇ u) x).det = A.det := by
    change (fderiv ℝ (∇ u) x).toLinearMap.det = _
    rw [hD]
    exact (LinearMap.det_toMatrix _ _).symm
  have hDetB : B.det = (4 : ℝ) ^ (2 * n) * (complexHessian u x).det.re ^ 2 := by
    rw [show B.det = (bilinearOperator ((2 : ℝ) • H)).det from LinearMap.det_toMatrix _ _]
    have hs : bilinearOperator ((2 : ℝ) • H) = (2 : ℝ) • bilinearOperator H := by
      ext v : 1
      exact (InnerProductSpace.toDual ℝ (E n)).symm.map_smul 2 (H v)
    rw [hs, LinearMap.det_smul, finrank_E,
      show (bilinearOperator H).det = (2 : ℝ) ^ (2 * n) * (complexHessian u x).det.re ^ 2 from
        det_toDual_symm_realification hp.isHermitian, ← mul_assoc, ← mul_pow]
    norm_num
  rw [hDetA, abs_of_nonneg hA.det_nonneg, ← hDetB]
  exact det_le_det_of_posSemidef hA hB hBA

end KEBall
