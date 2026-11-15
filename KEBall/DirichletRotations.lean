import KEBall.DirichletGradient
import KEBall.GradientBridge
import KEBall.RadialJacobi

/-!
# Differentiating a potential along linear vector fields
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped ContDiff Topology Matrix ComplexOrder

namespace KEBall

private theorem contDiffOn_linearFieldDerivative {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (A : E n →L[ℝ] E n) :
    ContDiffOn ℝ ∞ (fun y => fderiv ℝ u y (A y)) U :=
  (hu.fderiv_of_isOpen hU (by simp)).clm_apply A.contDiff.contDiffOn

private theorem fderiv_linearFieldDerivative {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (A : E n →L[ℝ] E n) (v : E n) :
    fderiv ℝ (fun y => fderiv ℝ u y (A y)) x v =
      realHessian u x v (A x) + fderiv ℝ u x (A v) := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have h := hd.clm_apply (A.hasFDerivAt (x := x))
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, realHessian, add_comm]

/-- The Hessian of a directional derivative along a linear vector field
has the differentiated Hessian and one correction for each argument. -/
theorem realHessian_linearFieldDerivative {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (A : E n →L[ℝ] E n) (v w : E n) :
    realHessian (fun y => fderiv ℝ u y (A y)) x v w =
      realThirdDerivative u x (A x) v w + realHessian u x (A v) w + realHessian u x v (A w) := by
  let R (y : E n) := fderiv ℝ u y (A y)
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hRAt := (contDiffOn_linearFieldDerivative hU hu A).contDiffAt (hU.mem_nhds hx)
  have heq : (fun y => fderiv ℝ R y w) =ᶠ[𝓝 x]
      (fun y => realHessian u y w (A y) + fderiv ℝ u y (A w)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_linearFieldDerivative (hu.contDiffAt (hU.mem_nhds hy)) A w
  have hB := ((realHessian_contDiffAt huAt).differentiableAt (by simp)).hasFDerivAt
  have hA := (hB.clm_apply (hasFDerivAt_const w x)).clm_apply (A.hasFDerivAt (x := x))
  have hdu : DifferentiableAt ℝ (fun y => fderiv ℝ u y (A w)) x :=
    ((huAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hsum := hA.add hdu.hasFDerivAt
  change HasFDerivAt (fun y => realHessian u y w (A y) + fderiv ℝ u y (A w)) _ x at hsum
  change realHessian R x v w = _
  rw [← fderiv_firstDerivative_apply hRAt, heq.fderiv_eq, hsum.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add, fderiv_firstDerivative_apply huAt]
  change realHessian u x w (A v) + realThirdDerivative u x v w (A x) + realHessian u x v (A w) = _
  rw [realThirdDerivative_symm23 hU hu hx v w (A x), realThirdDerivative_symm12 huAt v (A x) w,
    realHessian_symm huAt w (A v)]
  ring

private theorem realHessian_constantFieldDerivative {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (a v w : E n) :
    realHessian (fun y => fderiv ℝ u y a) x v w = realThirdDerivative u x a v w := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hw := (huAt.fderiv_right (m := ∞) (by simp)).clm_apply (g := fun _ => a) contDiffAt_const
  have heq : (fun y => fderiv ℝ (fun z => fderiv ℝ u z a) y w) =ᶠ[𝓝 x]
      fun y => realHessian u y w a := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_firstDerivative_apply (hu.contDiffAt (hU.mem_nhds hy)) w a
  rw [← fderiv_firstDerivative_apply hw, heq.fderiv_eq, fderiv_realHessian_apply huAt,
    realThirdDerivative_symm23 hU hu hx v w a, realThirdDerivative_symm12 huAt v a w]

/-- For a complex-linear vector field, the same derivative identity holds
for the Hermitian form represented in real coordinates. -/
theorem realMetricForm_linearFieldDerivative {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (A : E n →L[ℝ] E n) (hAJ : ∀ y, A (J y) = J (A y)) (v w : E n) :
    realMetricForm (fun y => fderiv ℝ u y (A y)) x v w =
      realMetricForm (fun y => fderiv ℝ u y (A x)) x v w +
      realMetricForm u x (A v) w + realMetricForm u x v (A w) := by
  have huAt := hu.contDiffAt (hU.mem_nhds hx)
  have hRAt := (contDiffOn_linearFieldDerivative hU hu A).contDiffAt (hU.mem_nhds hx)
  have hDAt := (huAt.fderiv_right (m := ∞) (by simp)).clm_apply (g := fun _ => A x) contDiffAt_const
  rw [realMetricForm_eq_average_hessian hRAt, realMetricForm_eq_average_hessian hDAt,
    realMetricForm_eq_average_hessian huAt, realMetricForm_eq_average_hessian huAt]
  simp only [realHessian_linearFieldDerivative hU hu hx, realHessian_constantFieldDerivative hU hu hx, hAJ]
  ring

/-- The real bilinear form of a complex matrix in dot-product notation. -/
theorem hermitianRealification_eq_re_dotProduct {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (v w : E n) :
    hermitianRealification H v w = 2 * ((complexCoord v) ⬝ᵥ (H *ᵥ star (complexCoord w))).re := by
  rw [hermitianRealification_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hermitianRealification_injective {n : ℕ} :
    Function.Injective (@hermitianRealification n) := by
  intro H G heq
  ext i j
  have hre := congrArg (fun (T : E n →L[ℝ] E n →L[ℝ] ℝ) =>
    T (realDirection i) (realDirection j)) heq
  have him := congrArg (fun (T : E n →L[ℝ] E n →L[ℝ] ℝ) =>
    T (realDirection i) (imagDirection j)) heq
  simp only [hermitianRealification_realDirection, hermitianRealification_imagDirection,
    complexCoord_realDirection, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] at hre him
  exact Complex.ext (by linarith only [hre]) (by linarith only [him])

private theorem complexHessian_linearFieldDerivative {n : ℕ} {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {x : E n} (hx : x ∈ U)
    (A : E n →L[ℝ] E n) (hAJ : ∀ y, A (J y) = J (A y))
    (M : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ y, complexCoord (A y) = M *ᵥ complexCoord y) :
    complexHessian (fun y => fderiv ℝ u y (A y)) x =
      complexHessian (fun y => fderiv ℝ u y (A x)) x +
      (Mᵀ * complexHessian u x + complexHessian u x * Mᴴᵀ) := by
  apply hermitianRealification_injective
  ext v w : 2
  rw [← realMetricForm_eq, realMetricForm_linearFieldDerivative hU hu hx A hAJ]
  simp only [realMetricForm_eq, hermitianRealification_eq_re_dotProduct, hA]
  simp only [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  rw [Matrix.star_mulVec, Matrix.mulVec_vecMul]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  ring

/-- A complex skew-Hermitian linear field differentiates the prescribed
log density without introducing a term in the linearized equation. -/
theorem complexLaplacian_skewHermitianField_eq_logDensity {n : ℕ} {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    (A : E n →L[ℝ] E n) (hAJ : ∀ y, A (J y) = J (A y))
    (M : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ y, complexCoord (A y) = M *ᵥ complexCoord y)
    (hM : Mᴴᵀ = -Mᵀ) {x : E n} (hx : x ∈ unitBall n) :
    complexLaplacian u (fun y => fderiv ℝ u y (A y)) x =
      fderiv ℝ (fun y => Real.log (f y)) x (A x) := by
  rw [← complexLaplacian_directionalDerivative_eq_logDensity hu hf huP hEq hx (A x)]
  obtain ⟨U, hU, hsub, huU⟩ := hu
  have hHU := (huP x hx).isUnit
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hHU
  simp only [complexLaplacian_eq_trace,
    complexHessian_linearFieldDerivative hU huU (hsub (ball_subset_closedBall hx)) A hAJ M hA]
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  suffices htrace : ((complexHessian u x)⁻¹ *
      (Mᵀ * complexHessian u x + complexHessian u x * Mᴴᵀ)).trace = 0 by
    rw [htrace, Complex.zero_re, add_zero]
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_cycle' (complexHessian u x)⁻¹ Mᵀ
      (complexHessian u x), ← Matrix.mul_assoc (complexHessian u x) (complexHessian u x)⁻¹,
    ← Matrix.mul_assoc (complexHessian u x)⁻¹ (complexHessian u x),
    Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, Matrix.one_mul,
    hM, Matrix.trace_neg, add_neg_cancel]

/-- The mixed Hessian along a tangential rotation and the outward normal
is controlled by the first derivative of the prescribed log density. -/
theorem abs_realHessian_normal_rotation_le_of_dirichlet_det {n : ℕ} (hn : 0 < n)
    {u f : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hf : SmoothNear (closedUnitBall n) f)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 ≤ K)
    (hDensity : ∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n)
    (hLog : ∀ x ∈ unitBall n, ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K)
    (A : E n →L[ℝ] E n) (hAJ : ∀ y, A (J y) = J (A y))
    (M : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ y, complexCoord (A y) = M *ᵥ complexCoord y)
    (hM : Mᴴᵀ = -Mᵀ) (hTangent : ∀ y ∈ unitSphere n, inner ℝ y (A y) = 0)
    {x : E n} (hx : x ∈ unitSphere n) :
    |realHessian u x x (A x)| ≤ 2 * b * ((K * ‖A‖ + 1) / n) := by
  let R : E n → ℝ := fun y => fderiv ℝ u y (A y)
  let c := (K * ‖A‖ + 1) / (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcN : c * (n : ℝ) = K * ‖A‖ + 1 := div_mul_cancel₀ _ hnR.ne'
  have hR0 (y : E n) (hy : y ∈ unitSphere n) : R y = 0 := by
    rw [show R y = fderiv ℝ u y (A y) from rfl, sphere_fderiv_normal hu hu0 hy, hTangent y hy, mul_zero]
  have hBound := Cegrell.quadratic_and_boundarySlope_bounds hn hu (fun y hy => (huP y hy).posSemidef)
    hu0 ha hb (fun y hy => hEq y hy ▸ hDensity y hy)
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hRU : ContDiffOn ℝ ∞ R U := contDiffOn_linearFieldDerivative hU huU A
  have hMain (s : ℝ) (hs : |s| = 1) : s * realHessian u x x (A x) ≤ 2 * b * c := by
    let w : E n → ℝ := fun y => c * u y - s * R y
    have hWU : ContDiffOn ℝ ∞ w U := (contDiffOn_const.mul huU).sub (contDiffOn_const.mul hRU)
    have hw : SmoothNear (closedUnitBall n) w := ⟨U, hU, hSub, hWU⟩
    have hw0 (y : E n) (hy : y ∈ unitSphere n) : w y = 0 := by
      simp only [w, hu0 y hy, hR0 y hy, mul_zero, sub_self]
    have hL (y : E n) (hy : y ∈ unitBall n) : 0 < complexLaplacian u w y := by
      have hyU := hU.mem_nhds (hSub (ball_subset_closedBall hy))
      have huAt := huU.contDiffAt hyU
      have hRAt := hRU.contDiffAt hyU
      have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (huP y hy).isUnit
      have hAy : ‖A y‖ ≤ ‖A‖ :=
        (A.le_opNorm y).trans (mul_le_of_le_one_right (norm_nonneg _)
          (mem_ball_zero_iff.mp hy).le)
      have hlogAy : |fderiv ℝ (fun z => Real.log (f z)) y (A y)| ≤ K * ‖A‖ := by
        have hp := (fderiv ℝ (fun z => Real.log (f z)) y).le_opNorm (A y)
        rw [Real.norm_eq_abs] at hp
        exact hp.trans (mul_le_mul (hLog y hy) hAy (norm_nonneg _) hK)
      have hss : s * fderiv ℝ (fun z => Real.log (f z)) y (A y) ≤ K * ‖A‖ := by
        exact (le_abs_self _).trans (by rw [abs_mul, hs, one_mul]; exact hlogAy)
      rw [show w = (fun z => c * u z - s * R z) from rfl,
        complexLaplacian_sub_at u (contDiffAt_const.mul huAt) (contDiffAt_const.mul hRAt),
        complexLaplacian_const_mul_at u huAt, complexLaplacian_const_mul_at u hRAt,
        complexLaplacian_self_of_isUnit hdet,
        show complexLaplacian u R y = _ from
          complexLaplacian_skewHermitianField_eq_logDensity ⟨U, hU, hSub, huU⟩ hf huP hEq
            A hAJ M hA hM hy,
        hcN]
      linarith only [hss]
    have hwLe := le_boundary_bound_of_complexLaplacian_pos hw huP hL (fun y hy => (hw0 y hy).le)
    have hxC : x ∈ closedUnitBall n := sphere_subset_closedBall hx
    have hxU := hU.mem_nhds (hSub hxC)
    have huAt := huU.contDiffAt hxU
    have hRAt := hRU.contDiffAt hxU
    have hdu := huAt.differentiableAt (by simp)
    have hdR := hRAt.differentiableAt (by simp)
    have hS := boundarySlope_ge_of_le hx ((hw.contDiffAt hxC).differentiableAt (by simp))
      (differentiableAt_const (c := (0 : ℝ))) hwLe (hw0 x hx)
    simp only [boundarySlope, fderiv_const_apply, zero_apply,
      zero_div] at hS
    have hdw := (hdu.hasFDerivAt.const_mul c).sub (hdR.hasFDerivAt.const_mul s)
    change HasFDerivAt w _ x at hdw
    rw [hdw.fderiv, sub_apply, smul_apply,
      smul_apply, smul_eq_mul, smul_eq_mul,
      show fderiv ℝ R x x = _ from fderiv_linearFieldDerivative huAt A x,
      ← show R x = fderiv ℝ u x (A x) from rfl, hR0 x hx, add_zero] at hS
    have hDu : fderiv ℝ u x x = 2 * boundarySlope u x := by rw [boundarySlope]; ring
    rw [hDu] at hS
    have hUpper := mul_le_mul_of_nonneg_left (hBound.2 x hx).2 hc
    linarith only [hS, hUpper]
  rw [abs_le]
  constructor
  · have hneg := hMain (-1) (by norm_num)
    linarith only [hneg]
  · simpa using hMain 1 (by norm_num)

end KEBall
