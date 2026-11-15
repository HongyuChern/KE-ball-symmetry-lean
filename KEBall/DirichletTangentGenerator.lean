import KEBall.DirichletBoundaryHessian

/-! Public, separately checked tangent generator construction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix InnerProductSpace Metric Filter Set
open scoped ComplexConjugate ComplexOrder ContDiff Topology

namespace KEBall

theorem exists_dirichlet_skewHermitianField_of_tangent {n : ℕ} {x v : E n}
    (hx : x ∈ unitSphere n) (hv : inner ℝ x v = 0) :
    ∃ (A : E n →L[ℝ] E n) (M : Matrix (Fin n) (Fin n) ℂ),
      A x = v ∧ ‖A‖ ≤ 3 * ‖v‖ ∧ (∀ y, A (J y) = J (A y)) ∧
      (∀ y, complexCoord (A y) = M *ᵥ complexCoord y) ∧ Mᴴᵀ = -Mᵀ ∧
      ∀ y, inner ℝ y (A y) = 0 := by
  let e := complexCoordinates n
  let X := e x
  let V := e v
  have hX : ‖X‖ = 1 := (e.norm_map x).trans (mem_sphere_zero_iff_norm.mp hx)
  have hReal (y z : E n) : (inner ℂ (e y) (e z)).re = inner ℝ y z := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change ((star (complexCoord y)) ⬝ᵥ complexCoord z).re = _
    rw [complexCoord_pairing]
    simp
  have hRe : (inner ℂ V X).re = 0 := by
    rw [show V = e v from rfl, show X = e x from rfl, hReal, real_inner_comm]
    exact hv
  let t := inner ℂ V X / 2
  have hstar : star (inner ℂ V X) = -inner ℂ V X := by
    apply Complex.ext <;> simp only [Complex.star_def, Complex.conj_re, Complex.neg_re,
      hRe, neg_zero, Complex.conj_im, Complex.neg_im]
  have ht : star t = -t := by simp [t, hstar, neg_div]
  have hXX : inner ℂ X X = 1 := by rw [inner_self_eq_norm_sq_to_K, hX]; norm_num
  let W := V + t • X
  have hWX : inner ℂ W X = t := by
    rw [show W = V + t • X from rfl, inner_add_left, inner_smul_left, hXX, mul_one]
    change inner ℂ V X + star t = t
    rw [ht]
    dsimp [t]
    ring
  let B := rankOne ℂ W X - rankOne ℂ X W
  have hBX : B X = V := by
    simp only [B, _root_.sub_apply, rankOne_apply, hXX, one_smul, hWX, W, add_sub_cancel_right]
  have hBAdj : B.adjoint = -B := by
    simp only [B, map_sub, adjoint_rankOne, neg_sub]
  have hW : ‖W‖ ≤ ‖v‖ + ‖v‖ / 2 := by
    have htNorm : ‖t‖ ≤ ‖V‖ / 2 := by
      have hTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [show t = inner ℂ V X / 2 from rfl, norm_div, hTwo]
      exact div_le_div_of_nonneg_right (by simpa only [hX, mul_one] using norm_inner_le_norm V X)
        (by norm_num)
    have hW' := norm_add_le V (t • X)
    rw [norm_smul, hX, mul_one] at hW'
    exact hW'.trans (by simpa only [V, e.norm_map] using add_le_add_right htNorm ‖V‖)
  have hBNorm : ‖B‖ ≤ 3 * ‖v‖ := by
    have hb := norm_sub_le (rankOne ℂ W X) (rankOne ℂ X W)
    rw [norm_rankOne, norm_rankOne, hX, mul_one, one_mul] at hb
    change ‖B‖ ≤ ‖W‖ + ‖W‖ at hb
    linarith only [hb, hW]
  let A := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((B.restrictScalars ℝ).comp e.toContinuousLinearEquiv.toContinuousLinearMap)
  have hApply (y : E n) : e (A y) = B (e y) := e.apply_symm_apply _
  have hAnorm : ‖A‖ ≤ 3 * ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound A (by positivity) fun y => ?_
    calc
      ‖A y‖ = ‖B (e y)‖ := by rw [← e.norm_map (A y), hApply]
      _ ≤ ‖B‖ * ‖e y‖ := B.le_opNorm _
      _ ≤ (3 * ‖v‖) * ‖y‖ := by
        rw [e.norm_map]
        exact mul_le_mul_of_nonneg_right hBNorm (norm_nonneg y)
  have hJe (y : E n) : e (J y) = Complex.I • e y := by
    ext i
    change complexCoord (J y) i = Complex.I * complexCoord y i
    exact complexCoord_J y i
  let M : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.toEuclideanLin.symm (B : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
  have hM : M.toEuclideanLin = B.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hMAdj : Mᴴ = -M := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, map_neg, hM,
      ContinuousLinearMap.adjoint_toLinearMap, hBAdj]
    rfl
  refine ⟨A, M, e.injective ((hApply x).trans hBX), hAnorm, ?_, ?_, ?_, ?_⟩
  · intro y
    apply e.injective
    rw [hApply, hJe, B.map_smul, hJe, hApply]
  · intro y
    change WithLp.ofLp (e (A y)) = M *ᵥ WithLp.ofLp (e y)
    have hMat := Matrix.ofLp_toLpLin 2 2 M (e y)
    change WithLp.ofLp (M.toEuclideanLin (e y)) = M *ᵥ WithLp.ofLp (e y) at hMat
    rw [hM] at hMat
    exact (congrArg WithLp.ofLp (hApply y)).trans hMat
  · rw [hMAdj, Matrix.transpose_neg]
  · intro y
    rw [← hReal, hApply]
    have h := ContinuousLinearMap.adjoint_inner_right B (e y) (e y)
    rw [hBAdj, _root_.neg_apply, inner_neg_right] at h
    have hReEq := congrArg Complex.re h
    have hSymm : (inner ℂ (B (e y)) (e y)).re = (inner ℂ (e y) (B (e y))).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [Complex.neg_re, hSymm] at hReEq
    linarith only [hReEq]

end KEBall
