import KEBall.DirichletRotations
import KEBall.BedfordTaylorCoordinates
import KEBall.BoundarySchurValues
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Boundary Hessian estimates for the prescribed Dirichlet equation

Skew-Hermitian generators give the mixed estimates in every tangent
direction. The complex Hessian block and its Schur complement then
bound the remaining normal-normal entry.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix InnerProductSpace Metric Filter Set
open scoped ComplexConjugate ComplexOrder ContDiff Topology

namespace KEBall

private theorem exists_skewHermitianField_of_tangent {n : ℕ} {x v : E n}
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

/-- Every unit tangent direction has a mixed normal derivative bound
with constants independent of the choice of boundary point and direction. -/
theorem abs_realHessian_normal_unitTangent_le_of_dirichlet_det {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 ≤ K)
    (hDensity : ∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n)
    (hLog : ∀ x ∈ unitBall n, ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K)
    {x v : E n} (hx : x ∈ unitSphere n) (hv : inner ℝ x v = 0) (hvn : ‖v‖ = 1) :
    |realHessian u x x v| ≤ 2 * b * ((3 * K + 1) / n) := by
  obtain ⟨A, M, hAx, hNorm, hAJ, hA, hM, hTan⟩ := exists_skewHermitianField_of_tangent hx hv
  have h := abs_realHessian_normal_rotation_le_of_dirichlet_det hn hu hf hu0 huP hEq
    ha hb hK hDensity hLog A hAJ M hA hM (fun y _ => hTan y) hx
  rw [hAx] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply add_le_add_left
  rw [mul_comm 3 K]
  apply mul_le_mul_of_nonneg_left _ hK
  simpa only [hvn, mul_one] using hNorm

theorem dirichlet_det_eq_on_closedBall {n : ℕ} {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    (complexHessian u x).det = (f x : ℂ) := by
  obtain ⟨U, hU, hKU, huU⟩ := hu
  have hH : ContinuousOn (complexHessian u) (closedUnitBall n) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (complexHessian_contDiffOn hU huU i j).continuousOn.mono hKU
  have hD : ContinuousOn (fun y => (complexHessian u y).det) (closedUnitBall n) :=
    continuous_id.matrix_det.comp_continuousOn hH
  have hF : ContinuousOn (fun y => (f y : ℂ)) (closedUnitBall n) :=
    Complex.continuous_ofReal.comp_continuousOn fun y hy =>
      (hf.contDiffAt hy).continuousAt.continuousWithinAt
  have he : Set.EqOn (fun y => (complexHessian u y).det) (fun y => (f y : ℂ)) (unitBall n) := by
    intro y hy
    change (complexHessian u y).det = (f y : ℂ)
    rw [posDef_det_eq_ofReal_re (huP y hy), hEq y hy]
  apply Set.EqOn.of_subset_closure he hD hF Metric.ball_subset_closedBall ?_ hx
  rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
  exact Set.Subset.rfl

/-- The determinant fixes the normal entry by its Schur complement
at a sphere point, with the given density as right-hand side. -/
theorem dirichlet_boundary_schur_complement {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (hu0 : ∀ y ∈ unitSphere n, u y = 0)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {x : E n} (hx : x ∈ unitSphere n) (htR : 0 < boundarySlope u x) :
    fderiv ℝ (boundarySlope u) x x / 2 -
      ‖horizontalGradient (boundarySlope u) x‖ ^ 2 / (4 * boundarySlope u x) =
      f x / boundarySlope u x ^ (n - 1) := by
  have ht : (boundarySlope u x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt htR
  have hblock := sphere_complexHessian_block hu hu0 hx
  have hd := borderedScalarMatrix_det (a := boundaryNormalEntry u x) hn ht
    (boundaryNormalComplex_unit hx) (boundaryMixedComplex_orthogonal u hx)
    (boundaryMixedComplex_orthogonal_reverse u hx)
  rw [← hblock, dirichlet_det_eq_on_closedBall hu hf huP hEq (sphere_subset_closedBall hx),
    boundaryMixedComplex_normSq, boundaryNormalEntry] at hd
  push_cast at hd
  have hreal : f x = boundarySlope u x ^ (n - 1) *
      (fderiv ℝ (boundarySlope u) x x / 2 -
        ‖horizontalGradient (boundarySlope u) x‖ ^ 2 / (4 * boundarySlope u x)) := by
    apply Complex.ofReal_injective
    push_cast
    convert hd using 1
    ring
  apply (eq_div_iff (pow_ne_zero _ (ne_of_gt htR))).mpr
  nlinarith [hreal]

theorem norm_horizontalGradient_boundarySlope_le_of_dirichlet_det {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 ≤ K)
    (hDensity : ∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n)
    (hLog : ∀ x ∈ unitBall n, ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K)
    {x : E n} (hx : x ∈ unitSphere n) :
    ‖horizontalGradient (boundarySlope u) x‖ ≤ b * ((3 * K + 1) / n) := by
  let g := horizontalGradient (boundarySlope u) x
  change ‖g‖ ≤ _
  by_cases hg : g = 0
  · rw [hg, norm_zero]
    positivity
  let v := ‖g‖⁻¹ • g
  have hv : inner ℝ x v = 0 := by
    rw [show v = ‖g‖⁻¹ • g from rfl, real_inner_smul_right,
      horizontalGradient_inner_normal (boundarySlope u) hx, mul_zero]
  have hJv : inner ℝ (J x) v = 0 := by
    rw [show v = ‖g‖⁻¹ • g from rfl, real_inner_smul_right,
      horizontalGradient_inner_hopf (boundarySlope u) hx, mul_zero]
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hvn : ‖v‖ = 1 := by
    rw [show v = ‖g‖⁻¹ • g from rfl, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ hgn.ne']
  have hgv : inner ℝ g v = ‖g‖ := by
    rw [show v = ‖g‖⁻¹ • g from rfl, real_inner_smul_right, real_inner_self_eq_norm_sq,
      pow_two, ← mul_assoc, inv_mul_cancel₀ hgn.ne', one_mul]
  have hMixed := abs_realHessian_normal_unitTangent_le_of_dirichlet_det hn hu hf hu0 huP hEq
    ha hb hK hDensity hLog hx hv hvn
  rw [realHessian_symm (hu.contDiffAt (sphere_subset_closedBall hx)) x v,
    sphere_mixed_hessian hu hu0 hx hv, ← inner_horizontalGradient (boundarySlope u) hv hJv,
    show horizontalGradient (boundarySlope u) x = g from rfl, hgv,
    abs_of_nonneg (by positivity)] at hMixed
  linarith only [hMixed]

/-- The normal-normal real Hessian is bounded at the sphere by the
density bounds and the first derivative of the prescribed log density. -/
theorem abs_realHessian_normal_normal_le_of_dirichlet_det {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 ≤ K)
    (hDensity : ∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n)
    (hLog : ∀ x ∈ unitBall n, ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K)
    {x : E n} (hx : x ∈ unitSphere n) :
    |realHessian u x x x| ≤
      2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * ((3 * K + 1) / n)) ^ 2 / (4 * a)) := by
  let s := boundarySlope u x
  let g := horizontalGradient (boundarySlope u) x
  let C := b * ((3 * K + 1) / (n : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hxC : x ∈ closedUnitBall n := sphere_subset_closedBall hx
  have hxCl : x ∈ closure (unitBall n) := by
    rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    exact hxC
  let : NeBot (𝓝[unitBall n] x) := mem_closure_iff_nhdsWithin_neBot.mp hxCl
  have hFt : Tendsto f (𝓝[unitBall n] x) (𝓝 (f x)) :=
    (hf.contDiffAt hxC).continuousAt.continuousWithinAt
  have hFhi : f x ≤ b ^ n := by
    apply le_of_tendsto hFt
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hDensity y hy).2
  have hFlo : a ^ n ≤ f x := by
    apply ge_of_tendsto hFt
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hDensity y hy).1
  have hF : 0 ≤ f x := (pow_nonneg ha.le _).trans hFlo
  have hB := Cegrell.quadratic_and_boundarySlope_bounds hn hu (fun y hy => (huP y hy).posSemidef)
    hu0 ha hb (fun y hy => hEq y hy ▸ hDensity y hy)
  have hs : a ≤ s ∧ s ≤ b := hB.2 x hx
  have hsPos : 0 < s := ha.trans_le hs.1
  have hg : ‖g‖ ≤ C :=
    norm_horizontalGradient_boundarySlope_le_of_dirichlet_det hn hu hf hu0 huP hEq
      ha hb hK hDensity hLog hx
  have hSchur := dirichlet_boundary_schur_complement hn hu hf hu0 huP hEq hx hsPos
  change fderiv ℝ (boundarySlope u) x x / 2 - ‖g‖ ^ 2 / (4 * s) =
    f x / s ^ (n - 1) at hSchur
  have hNormal : realHessian u x x x =
      4 * (f x / s ^ (n - 1) + ‖g‖ ^ 2 / (4 * s)) - 2 * s := by
    have hDs := fderiv_boundarySlope (hu.contDiffAt hxC) x
    have hDu : fderiv ℝ u x x = 2 * s := by dsimp [s, boundarySlope]; ring
    rw [hDu] at hDs
    linarith only [hDs, hSchur]
  have h1 : f x / s ^ (n - 1) ≤ b ^ n / a ^ (n - 1) :=
    div_le_div₀ (pow_nonneg hb.le _) hFhi (pow_pos ha _) (pow_le_pow_left₀ ha.le hs.1 _)
  have h2 : ‖g‖ ^ 2 / (4 * s) ≤ C ^ 2 / (4 * a) :=
    div_le_div₀ (sq_nonneg C) (pow_le_pow_left₀ (norm_nonneg _) hg _) (by positivity)
      (mul_le_mul_of_nonneg_left hs.1 (by norm_num))
  have h01 : 0 ≤ f x / s ^ (n - 1) := by positivity
  have h02 : 0 ≤ ‖g‖ ^ 2 / (4 * s) := by positivity
  have hR : 0 ≤ b ^ n / a ^ (n - 1) + C ^ 2 / (4 * a) := by positivity
  change |realHessian u x x x| ≤ 2 * b + 4 * (b ^ n / a ^ (n - 1) + C ^ 2 / (4 * a))
  rw [hNormal, abs_le]
  exact ⟨by linarith only [hs.2, h01, h02, hR], by linarith only [hsPos, hb, h1, h2]⟩

/-- A bound for the real Hessian in any unit direction at the sphere. -/
theorem abs_realHessian_self_le_on_sphere_of_dirichlet_det {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 ≤ K)
    (hDensity : ∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n)
    (hLog : ∀ x ∈ unitBall n, ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K)
    {x v : E n} (hx : x ∈ unitSphere n) (hv : ‖v‖ = 1) :
    |realHessian u x v v| ≤
      2 * b + 4 * b * ((3 * K + 1) / n) +
        (2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * ((3 * K + 1) / n)) ^ 2 / (4 * a))) := by
  let t := inner ℝ x v
  let T := v - t • x
  let c := (3 * K + 1) / (n : ℝ)
  let N := 2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * c) ^ 2 / (4 * a))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hxN := mem_sphere_zero_iff_norm.mp hx
  have ht : |t| ≤ 1 := by
    simpa only [t, hxN, hv, mul_one] using abs_real_inner_le_norm x v
  have hT : inner ℝ x T = 0 := by
    simp only [T, inner_sub_right, real_inner_smul_right, sphere_inner_self hx,
      mul_one, t, sub_self]
  have hTNorm : ‖T‖ ≤ 1 := by
    have hsq : ‖T‖ ^ 2 = 1 - t ^ 2 := by
      have ht' : inner ℝ v x = t := real_inner_comm _ _
      rw [← real_inner_self_eq_norm_sq, show T = v - t • x from rfl]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        sphere_inner_self hx, real_inner_self_eq_norm_sq v, hv, one_pow, ht',
        show inner ℝ x v = t from rfl]
      ring
    nlinarith only [hsq, sq_nonneg t, norm_nonneg T]
  have hB := Cegrell.quadratic_and_boundarySlope_bounds hn hu (fun y hy => (huP y hy).posSemidef)
    hu0 ha hb (fun y hy => hEq y hy ▸ hDensity y hy)
  have hs := hB.2 x hx
  have hs0 : 0 ≤ boundarySlope u x := ha.le.trans hs.1
  have hTT : |realHessian u x T T| ≤ 2 * b := by
    rw [sphere_tangent_hessian hu hu0 hx hT hT, real_inner_self_eq_norm_sq,
      abs_of_nonneg (by positivity)]
    have hT2 : ‖T‖ ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg T) hTNorm 2
    exact (mul_le_of_le_one_right (by positivity) hT2).trans
      (mul_le_mul_of_nonneg_left hs.2 (by norm_num))
  have hxT : |realHessian u x x T| ≤ 2 * b * c := by
    by_cases hT0 : T = 0
    · rw [hT0, map_zero, abs_zero]
      positivity
    let W := ‖T‖⁻¹ • T
    have hTN := norm_pos_iff.mpr hT0
    have hW : inner ℝ x W = 0 := by
      simp only [W, real_inner_smul_right, hT, mul_zero]
    have hWNorm : ‖W‖ = 1 := by
      rw [show W = ‖T‖⁻¹ • T from rfl, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ hTN.ne']
    have hMixed := abs_realHessian_normal_unitTangent_le_of_dirichlet_det hn hu hf hu0 huP hEq
      ha hb hK hDensity hLog hx hW hWNorm
    have hScale : realHessian u x x T = ‖T‖ * realHessian u x x W := by
      simp only [W, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hTN.ne', one_mul]
    rw [hScale, abs_mul, abs_of_nonneg (norm_nonneg T)]
    exact (mul_le_mul_of_nonneg_left hMixed (norm_nonneg T)).trans
      (mul_le_of_le_one_left (by positivity) hTNorm)
  have hxx : |realHessian u x x x| ≤ N :=
    abs_realHessian_normal_normal_le_of_dirichlet_det hn hu hf hu0 huP hEq
      ha hb hK hDensity hLog hx
  have hMix : |(2 * t) * realHessian u x x T| ≤ 4 * b * c := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hM := mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)) hxT
      (abs_nonneg _) (by positivity)
    nlinarith only [hM]
  have hNor : |t ^ 2 * realHessian u x x x| ≤ N := by
    have hsq : t ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
      simpa only [sq_abs, one_pow] using h
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    exact (mul_le_of_le_one_left (abs_nonneg _) hsq).trans hxx
  have hExpand : realHessian u x v v =
      realHessian u x T T + (2 * t) * realHessian u x x T + t ^ 2 * realHessian u x x x := by
    have hv' : v = T + t • x := (sub_add_cancel v (t • x)).symm
    nth_rw 1 [hv']
    nth_rw 1 [hv']
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
      realHessian_symm (hu.contDiffAt (sphere_subset_closedBall hx)) T x]
    ring
  change |realHessian u x v v| ≤ 2 * b + 4 * b * c + N
  rw [hExpand]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hTT hMix)) hNor)

end KEBall
