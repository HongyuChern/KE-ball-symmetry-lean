import KEBall.DirichletThirdDetEquation

/-! The decomposition of a symmetric third derivative into its tangential
part and its single pure normal entry. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 8

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

private theorem abs_trilinear_le_of_basis {n : ℕ}
    (T : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ) (a b c : E n)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    |T a b c| ≤ ∑ i, ∑ j, ∑ k, |T (e[n] i) (e[n] j) (e[n] k)| := by
  let e := e[n]
  let s (v : E n) (i : Fin (2 * n)) := inner ℝ (e i) v
  have hS (v : E n) (hv : ‖v‖ ≤ 1) (i : Fin (2 * n)) : |s v i| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    exact (norm_inner_le_norm _ _).trans (by rw [e.orthonormal.norm_eq_one, one_mul]; exact hv)
  have he : T a b c =
      ∑ i, ∑ j, ∑ k, (s a i * s b j * s c k) * T (e i) (e j) (e k) := by
    calc
      _ = T (∑ i, s a i • e i) (∑ j, s b j • e j) (∑ k, s c k • e k) := by
        simp only [s, e.sum_repr']
      _ = _ := by
        simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
        calc
          (∑ k, ∑ j, ∑ i, s c k * (s b j * (s a i * T (e i) (e j) (e k)))) =
              ∑ k, ∑ j, ∑ i, (s a i * s b j * s c k) * T (e i) (e j) (e k) := by
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun i _ => by ring
          _ = ∑ k, ∑ i, ∑ j, (s a i * s b j * s c k) * T (e i) (e j) (e k) :=
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
          _ = ∑ i, ∑ k, ∑ j, (s a i * s b j * s c k) * T (e i) (e j) (e k) := Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [he, ← Real.norm_eq_abs]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)))
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀
    (mul_le_one₀ (hS a ha i) (abs_nonneg _) (hS b hb j)) (abs_nonneg _) (hS c hc k))

/-- A symmetric trilinear form is controlled up to the pure normal part by
its evaluations with one argument in the orthogonal complement. -/
theorem abs_trilinear_sub_normal_le {n : ℕ}
    (T : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ)
    (h₁₂ : ∀ a b c, T a b c = T b a c) (h₂₃ : ∀ a b c, T a b c = T a c b)
    (y : E n) (hy : ‖y‖ = 1) (a b c : E n)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    |T a b c - (inner ℝ y a * inner ℝ y b * inner ℝ y c) * T y y y| ≤
      3 * ∑ i, ∑ j, ∑ k, |T (e[n] i - inner ℝ y (e[n] i) • y) (e[n] j) (e[n] k)| := by
  let N : E n →L[ℝ] E n := (innerSL ℝ y).smulRight y
  let P : E n →L[ℝ] E n := ContinuousLinearMap.id ℝ (E n) - N
  let K := ∑ i, ∑ j, ∑ k, |T (P (e[n] i)) (e[n] j) (e[n] k)|
  have hN (v : E n) : ‖N v‖ ≤ ‖v‖ := by
    simp only [N, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul, hy, mul_one]
    exact (norm_inner_le_norm _ _).trans (by rw [hy, one_mul])
  have hP (v : E n) : P v = v - N v := rfl
  have hE : T a b c - T (N a) (N b) (N c) =
      T (P a) b c + T (P b) (N a) c + T (P c) (N a) (N b) := by
    rw [h₁₂ (P b) (N a) c, h₁₂ (P c) (N a) (N b), h₂₃ (N a) (P c) (N b)]
    simp only [hP, map_sub, _root_.sub_apply]
    ring
  have hProj {v w z : E n} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
      |T (P v) w z| ≤ K := abs_trilinear_le_of_basis (T.comp P) v w z hv hw hz
  have hMain : |T a b c - T (N a) (N b) (N c)| ≤ 3 * K := by
    rw [hE]
    exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans
      (add_le_add (hProj ha hb hc) (hProj hb ((hN a).trans ha) hc)))
      (hProj hc ((hN a).trans ha) ((hN b).trans hb))).trans_eq (by ring))
  have hNormal : T (N a) (N b) (N c) =
      (inner ℝ y a * inner ℝ y b * inner ℝ y c) * T y y y := by
    simp only [N, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul, _root_.smul_apply,
      smul_eq_mul]
    ring
  rw [hNormal] at hMain
  exact hMain


private theorem exists_norm_adjugate_le_on_closedBall {n : ℕ} (D : ℝ) :
    ∃ K ≥ (0 : ℝ), ∀ A : Matrix (Fin n) (Fin n) ℂ, ‖A‖ ≤ D → ‖A.adjugate‖ ≤ K := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have hAdj : Continuous (fun A : M => A.adjugate) := continuous_id.matrix_adjugate
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : M) D).exists_bound_of_continuousOn hAdj.continuousOn
  exact ⟨max K 0, le_max_right _ _, fun A hA =>
    (hK A (mem_closedBall_zero_iff.mpr hA)).trans (le_max_left _ _)⟩

private theorem abs_cofactorTrace_le_of_bilinear_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : E n →L[ℝ] E n →L[ℝ] ℝ) {K C : ℝ} (hK : 0 ≤ K)
    (hA : ‖A.adjugate‖ ≤ K) (hB : ∀ a b : E n, ‖a‖ = 1 → ‖b‖ = 1 → |B a b| ≤ C) :
    |(A.adjugate * complexHessianOfRealBilinear B).trace.re| ≤ (n : ℝ) ^ 2 * K * C := by
  have hE (i j : Fin n) : ‖complexHessianOfRealBilinear B i j‖ ≤ C := by
    have hr (k : Fin n) : ‖realDirection k‖ = 1 := by simp [realDirection]
    have hi (k : Fin n) : ‖imagDirection k‖ = 1 := by simp [imagDirection]
    have h₁ := hB _ _ (hr i) (hr j)
    have h₂ := hB _ _ (hi i) (hi j)
    have h₃ := hB _ _ (hr i) (hi j)
    have h₄ := hB _ _ (hi i) (hr j)
    unfold complexHessianOfRealBilinear
    rw [norm_mul, norm_inv, show ‖(4 : ℂ)‖ = 4 from by norm_num]
    have hTriangle :
        ‖(B (realDirection i) (realDirection j) : ℂ) + (B (imagDirection i) (imagDirection j) : ℂ) +
          Complex.I * ((B (realDirection i) (imagDirection j) : ℂ) -
            (B (imagDirection i) (realDirection j) : ℂ))‖ ≤ C + C + (C + C) := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact (norm_add_le _ _).trans (by simpa only [Complex.norm_real, Real.norm_eq_abs] using add_le_add h₁ h₂)
      · rw [norm_mul, Complex.norm_I, one_mul]
        exact (norm_sub_le _ _).trans (by simpa only [Complex.norm_real, Real.norm_eq_abs] using add_le_add h₃ h₄)
    exact (mul_le_mul_of_nonneg_left hTriangle (by norm_num)).trans_eq (by ring)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  calc
    _ ≤ ‖∑ i, ∑ j, A.adjugate i j * complexHessianOfRealBilinear B j i‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖A.adjugate i j * complexHessianOfRealBilinear B j i‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, K * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A.adjugate |>.trans hA)
        (hE j i) (norm_nonneg _) hK
    _ = _ := by simp [Finset.sum_const]; ring

/-- The remainder after removing the pure normal tensor can be inserted
into the linearized determinant to bound that entry. -/
theorem abs_trilinear_normal_le_of_cofactorTrace {n : ℕ}
    (T : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ)
    (h₁₂ : ∀ a b c, T a b c = T b a c) (h₂₃ : ∀ a b c, T a b c = T a c b)
    (y : E n) (hy : ‖y‖ = 1) (A : Matrix (Fin n) (Fin n) ℂ) {K l L : ℝ}
    (hK : 0 ≤ K) (hl : 0 < l) (hA : ‖A.adjugate‖ ≤ K)
    (hPos : l ≤ hermitianRankOneDetSlope A (star (complexCoord y)) / 4)
    (hEq : |(A.adjugate * complexHessianOfRealBilinear (T y)).trace.re| ≤ L) :
    l * |T y y y| ≤ L + (n : ℝ) ^ 2 * K *
      (3 * ∑ i, ∑ j, ∑ k, |T (e[n] i - inner ℝ y (e[n] i) • y) (e[n] j) (e[n] k)|) := by
  let t := T y y y
  let B : E n →L[ℝ] E n →L[ℝ] ℝ :=
    T y - t • (innerSL ℝ y).smulRight (innerSL ℝ y)
  let Q := 3 * ∑ i, ∑ j, ∑ k, |T (e[n] i - inner ℝ y (e[n] i) • y) (e[n] j) (e[n] k)|
  have hB (a b : E n) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : |B a b| ≤ Q := by
    have h := abs_trilinear_sub_normal_le T h₁₂ h₂₃ y hy y a b hy.le ha.le hb.le
    simpa only [B, t, _root_.sub_apply, _root_.smul_apply, smul_eq_mul,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, hy,
      one_pow, one_mul, mul_left_comm, mul_comm] using h
  have hTrace := abs_cofactorTrace_le_of_bilinear_bound A B hK hA hB
  have hSplit : T y = B + t • (innerSL ℝ y).smulRight (innerSL ℝ y) :=
    (sub_add_cancel _ _).symm
  have he : (A.adjugate * complexHessianOfRealBilinear (T y)).trace.re =
      (A.adjugate * complexHessianOfRealBilinear B).trace.re +
        t * (hermitianRankOneDetSlope A (star (complexCoord y)) / 4) := by
    rw [hSplit, complexHessianOfRealBilinear_add_rankOne, Matrix.mul_add, Matrix.trace_add,
      Complex.add_re, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_vecMulVec,
      Matrix.trace_vecMulVec, dotProduct_comm, hermitianRankOneDetSlope, star_star]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have htEq : t * (hermitianRankOneDetSlope A (star (complexCoord y)) / 4) =
      (A.adjugate * complexHessianOfRealBilinear (T y)).trace.re -
        (A.adjugate * complexHessianOfRealBilinear B).trace.re := by linarith only [he]
  calc
    l * |t| ≤ (hermitianRankOneDetSlope A (star (complexCoord y)) / 4) * |t| :=
      mul_le_mul_of_nonneg_right hPos (abs_nonneg _)
    _ = |t * (hermitianRankOneDetSlope A (star (complexCoord y)) / 4)| := by
      rw [abs_mul, abs_of_nonneg (hl.le.trans hPos), mul_comm]
    _ ≤ L + (n : ℝ) ^ 2 * K * Q := by
      rw [htEq]
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add hEq hTrace)


/-- For uniformly elliptic solutions the full third derivative away from the
center is pointwise bounded by the density gradient and tangential entries. -/
theorem exists_abs_realThirdDerivative_le_of_annular_tangential {n : ℕ}
    {a D L r : ℝ} (ha : 0 < a) (hD : 0 < D) (hL : 0 ≤ L) (hr : 0 < r) :
    ∃ C₀ ≥ (0 : ℝ), ∃ C₁ ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, a ^ n ≤ f x) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian u x w w| ≤ D) →
      ∀ x ∈ unitBall n, r ≤ ‖x‖ → ∀ v w z : E n,
        ‖v‖ ≤ 1 → ‖w‖ ≤ 1 → ‖z‖ ≤ 1 →
        |realThirdDerivative u x v w z| ≤ C₀ + C₁ *
          ∑ i, ∑ j, ∑ k, |realThirdDerivative u x
            (‖x‖ ^ 2 • e[n] i - inner ℝ (e[n] i) x • x) (e[n] j) (e[n] k)| := by
  obtain ⟨K, hK, hAdj⟩ := exists_norm_adjugate_le_on_closedBall (n := n) D
  let l := a ^ n * ((D / 2)⁻¹ / 4)
  have hl : 0 < l := by dsimp [l]; positivity
  refine ⟨L / l, by positivity, 3 * (1 + (n : ℝ) ^ 2 * K / l) * (r ^ 2)⁻¹, by positivity, ?_⟩
  intro u f hu hf huP hEq hDen hGrad hBound x hx hrx v w z hv hw hz
  let T := realThirdDerivative u x
  let y := ‖x‖⁻¹ • x
  have hx0 : 0 < ‖x‖ := hr.trans_le hrx
  have hy : ‖y‖ = 1 := by
    rw [show y = ‖x‖⁻¹ • x from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hx0.le), inv_mul_cancel₀ hx0.ne']
  have hS : x = ‖x‖ • y := by
    dsimp only [y]
    rw [smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]
  have hProj (b : E n) :
      b - inner ℝ y b • y = (‖x‖ ^ 2)⁻¹ • (‖x‖ ^ 2 • b - inner ℝ b x • x) := by
    conv_rhs => rw [hS]
    simp only [real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hx0.le, hy, mul_one, smul_sub, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hx0.ne'), one_smul]
    rw [real_inner_comm b y]
    congr 2
    field_simp
  let U := ∑ i, ∑ j, ∑ k, |T (e[n] i - inner ℝ y (e[n] i) • y) (e[n] j) (e[n] k)|
  let V := ∑ i, ∑ j, ∑ k, |T (‖x‖ ^ 2 • e[n] i - inner ℝ (e[n] i) x • x) (e[n] j) (e[n] k)|
  have hU : U = (‖x‖ ^ 2)⁻¹ * V := by
    simp only [U, V, hProj, map_smul, _root_.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖x‖)), Finset.mul_sum]
  have hUV : U ≤ (r ^ 2)⁻¹ * V := by
    rw [hU]
    apply mul_le_mul_of_nonneg_right _ (by dsimp [V]; positivity)
    exact inv_anti₀ (sq_pos_of_pos hr) (pow_le_pow_left₀ hr.le hrx 2)
  have hx' := ball_subset_closedBall hx
  have huAt := hu.contDiffAt hx'
  have h₁₂ := realThirdDerivative_symm12 huAt
  have h₂₃ : ∀ p q s : E n, T p q s = T p s q := by
    obtain ⟨O, hO, hSub, huO⟩ := hu
    exact realThirdDerivative_symm23 hO huO (hSub hx')
  let A := complexHessian u x
  have hA : ‖A.adjugate‖ ≤ K :=
    hAdj _ (norm_complexHessian_le_of_unit_bound huAt hD.le (hBound x hx'))
  let hp := dirichlet_posDef_on_closedBall hu hf huP hEq ha hDen hx'
  let m := a ^ n / (D / 2) ^ (n - 1)
  have hm : 0 < m := by dsimp [m]; positivity
  have hEig (i : Fin n) : m ≤ hp.isHermitian.eigenvalues i ∧ hp.isHermitian.eigenvalues i ≤ D / 2 :=
    complexHessian_eigenvalues_bounds_of_dirichlet_det hu hf huP hEq ha hD hDen
      (fun x hx v hv => (le_abs_self _).trans (hBound x hx v hv)) hx' i
  have hSlope := mul_norm_sq_le_quarter_hermitianRankOneDetSlope hp
    (show a ^ n ≤ A.det.re by dsimp only [A]; rw [hEq x hx]; exact hDen x hx)
    hm (show 0 < D / 2 by positivity) hEig (v := y)
  have hSlope' : l ≤ hermitianRankOneDetSlope A (star (complexCoord y)) / 4 := by
    simpa only [l, hy, one_pow, mul_one] using hSlope
  have hRhs : |(A.adjugate * complexHessianOfRealBilinear (T y)).trace.re| ≤ L := by
    rw [show (A.adjugate * complexHessianOfRealBilinear (T y)).trace.re =
      fderiv ℝ f x y from cofactorTrace_realThirdDerivative_eq_fderiv hu hEq hx y, ← Real.norm_eq_abs]
    exact ((fderiv ℝ f x).le_opNorm y).trans (by rw [hy, mul_one]; exact hGrad x hx')
  have hn := abs_trilinear_normal_le_of_cofactorTrace T h₁₂ h₂₃ y hy A hK hl hA hSlope' hRhs
  have hn' : |T y y y| ≤ (L + (n : ℝ) ^ 2 * K * (3 * U)) / l := by
    apply (le_div_iff₀ hl).mpr
    rwa [mul_comm]
  let c := inner ℝ y v * inner ℝ y w * inner ℝ y z
  have hc₀ (q : E n) (hq : ‖q‖ ≤ 1) : |inner ℝ y q| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    exact (norm_inner_le_norm _ _).trans (by rwa [hy, one_mul])
  have hc : |c| ≤ 1 := by
    simp only [c, abs_mul]
    exact mul_le_one₀ (mul_le_one₀ (hc₀ v hv) (abs_nonneg _) (hc₀ w hw)) (abs_nonneg _) (hc₀ z hz)
  have hC : |c * T y y y| ≤ |T y y y| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hc
  have hSplit := abs_trilinear_sub_normal_le T h₁₂ h₂₃ y hy v w z hv hw hz
  calc
    |T v w z| = |(T v w z - c * T y y y) + c * T y y y| := by rw [sub_add_cancel]
    _ ≤ 3 * U + |T y y y| := (abs_add_le _ _).trans (add_le_add hSplit hC)
    _ ≤ 3 * U + (L + (n : ℝ) ^ 2 * K * (3 * U)) / l := add_le_add_right hn' _
    _ = L / l + (3 * (1 + (n : ℝ) ^ 2 * K / l)) * U := by ring
    _ ≤ L / l + (3 * (1 + (n : ℝ) ^ 2 * K / l)) * ((r ^ 2)⁻¹ * V) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hUV (by positivity)) _
    _ = _ := by change _ = L / l + (3 * (1 + (n : ℝ) ^ 2 * K / l) * (r ^ 2)⁻¹) * V; ring


private theorem sq_sum_three_le {ι : Type*} [Fintype ι] (F : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, |F i j k|) ^ 2 ≤
      (Fintype.card ι : ℝ) ^ 3 * ∑ i, ∑ j, ∑ k, (F i j k) ^ 2 := by
  let G (s : ι × ι × ι) := |F s.1 s.2.1 s.2.2|
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := G)
  simp only [G, Finset.card_univ, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type, sq_abs] at h
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h

/-- The entire third derivative has a uniform square integral on every
annulus of the unit ball with positive inner radius. -/
theorem exists_integral_sq_realThirdDerivative_le_on_annulus {n : ℕ} (hn : 0 < n)
    {a b D L r : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (hL : 0 ≤ L) (hr : 0 < r) :
    ∃ C ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian u x w w| ≤ D) →
      (∫ x in unitBall n ∩ {x | r ≤ ‖x‖}, ∑ i, ∑ j, ∑ k,
        (realThirdDerivative u x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ∂volume0 n) ≤ C := by
  obtain ⟨C₀, hC₀, C₁, hC₁, hPointwise⟩ :=
    exists_abs_realThirdDerivative_le_of_annular_tangential (n := n) ha hD hL hr
  obtain ⟨B, hB, hTan⟩ := exists_integral_sq_realThirdDerivative_tangent_le hn ha hb hD hL
  let M : ℝ := 2 * (n : ℝ)
  let S : Set (E n) := unitBall n ∩ {x | r ≤ ‖x‖}
  let μ := (volume0 n).restrict S
  refine ⟨M ^ 3 * (2 * C₀ ^ 2 + (2 * C₁ ^ 2 * M ^ 3) * (M * B)), by positivity, ?_⟩
  intro u f hu hf hu0 huP hEq hDen hGrad hBound
  let W (i : Fin (2 * n)) (x : E n) := ‖x‖ ^ 2 • e[n] i - inner ℝ (e[n] i) x • x
  let T := realThirdDerivative u
  let p (x : E n) := ∑ i, ∑ j, ∑ k, (T x (e[n] i) (e[n] j) (e[n] k)) ^ 2
  let q (i : Fin (2 * n)) (x : E n) := ∑ j, ∑ k, (T x (W i x) (e[n] j) (e[n] k)) ^ 2
  let Q (x : E n) := ∑ i, q i x
  have hS : MeasurableSet S := measurableSet_ball.inter (isClosed_le continuous_const continuous_norm).measurableSet
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hu : SmoothNear (closedUnitBall n) u := ⟨U, hU, hSub, huU⟩
  have hD₁ := huU.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hD₂ := hD₁.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hT : ContDiffOn ℝ ∞ T U := hD₂.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hC {V : E n → E n} (hV : Continuous V) (j k : Fin (2 * n)) :
      ContinuousOn (fun x => (T x (V x) (e[n] j) (e[n] k)) ^ 2) U :=
    (((hT.continuousOn.clm_apply hV.continuousOn).clm_apply continuousOn_const).clm_apply
      continuousOn_const).pow 2
  have hPC : ContinuousOn p U := continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_finsetSum Finset.univ fun j _ =>
      continuousOn_finsetSum Finset.univ fun k _ => hC continuous_const j k
  have hQC (i : Fin (2 * n)) : ContinuousOn (q i) U := continuousOn_finsetSum Finset.univ fun j _ =>
    continuousOn_finsetSum Finset.univ fun k _ =>
      hC (((continuous_norm.pow 2).smul continuous_const).sub
        ((innerSL ℝ (e[n] i)).continuous.smul continuous_id)) j k
  have hQsumC : ContinuousOn Q U := continuousOn_finsetSum Finset.univ fun i _ => hQC i
  have hI {g : E n → ℝ} (hg : ContinuousOn g U) : IntegrableOn g (unitBall n) (volume0 n) :=
    (hg.mono hSub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hQInt (i : Fin (2 * n)) : (∫ x, q i x ∂μ) ≤ B := by
    refine (setIntegral_mono_set (hI (hQC i)) (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall (show S ⊆ unitBall n from inter_subset_left))).trans ?_
    · dsimp [q]; positivity
    · exact hTan hu hf hu0 huP hEq hDen hGrad hBound i
  have hQsumInt : (∫ x, Q x ∂μ) ≤ M * B := by
    unfold Q
    rw [integral_finsetSum _ (fun i _ => (hI (hQC i)).mono_set inter_subset_left)]
    exact (Finset.sum_le_sum fun i _ => hQInt i).trans_eq (by simp [M, Nat.cast_mul])
  have hPoint : p ≤ᵐ[μ] fun x => M ^ 3 * (2 * C₀ ^ 2 + (2 * C₁ ^ 2 * M ^ 3) * Q x) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) hS] with x hx
    have hx' : x ∈ unitBall n := hx.1
    have hrx : r ≤ ‖x‖ := hx.2
    let H := ∑ i, ∑ j, ∑ k, |T x (W i x) (e[n] j) (e[n] k)|
    have hH : H ^ 2 ≤ M ^ 3 * Q x := by
      simpa only [H, Q, q, M, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using
        sq_sum_three_le (fun i j k => T x (W i x) (e[n] j) (e[n] k))
    have he (i : Fin (2 * n)) : ‖e[n] i‖ ≤ 1 := ((e[n]).orthonormal.norm_eq_one i).le
    have hEntry (i j k : Fin (2 * n)) :
        (T x (e[n] i) (e[n] j) (e[n] k)) ^ 2 ≤ 2 * C₀ ^ 2 + (2 * C₁ ^ 2 * M ^ 3) * Q x := by
      have h := hPointwise hu hf huP hEq (fun y hy => (hDen y hy).1) hGrad hBound x hx' hrx
        (e[n] i) (e[n] j) (e[n] k) (he i) (he j) (he k)
      change |T x (e[n] i) (e[n] j) (e[n] k)| ≤ C₀ + C₁ * H at h
      have hSq := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs] at hSq
      have hH' := mul_le_mul_of_nonneg_left hH (show 0 ≤ 2 * C₁ ^ 2 by positivity)
      nlinarith only [hSq, hH', sq_nonneg (C₀ - C₁ * H)]
    calc
      p x ≤ ∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), ∑ _k : Fin (2 * n),
          (2 * C₀ ^ 2 + (2 * C₁ ^ 2 * M ^ 3) * Q x) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hEntry i j k
      _ = _ := by simp only [M, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
  have hμ : μ.real univ ≤ 1 := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    have h := measureReal_mono (μ := volume0 n) (show S ⊆ unitBall n from inter_subset_left)
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
    change ((volume0 n) S).toReal ≤ ((volume0 n) (unitBall n)).toReal at h
    simpa only [volume0_unitBall n hn, ENNReal.toReal_one] using h
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono (show S ⊆ unitBall n from inter_subset_left)).trans_lt
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_lt_top)
  have hQi : Integrable Q μ := (hI hQsumC).mono_set inter_subset_left
  have h := integral_mono_ae ((hI hPC).mono_set inter_subset_left)
    (((integrable_const (2 * C₀ ^ 2)).add (hQi.const_mul (2 * C₁ ^ 2 * M ^ 3))).const_mul (M ^ 3))
    hPoint
  change (∫ x, p x ∂μ) ≤ (∫ x, M ^ 3 * (2 * C₀ ^ 2 + (2 * C₁ ^ 2 * M ^ 3) * Q x) ∂μ) at h
  rw [integral_const_mul, integral_add (integrable_const (2 * C₀ ^ 2))
    (hQi.const_mul (2 * C₁ ^ 2 * M ^ 3))] at h
  change (∫ x, p x ∂μ) ≤ M ^ 3 * ((∫ _ : E n, 2 * C₀ ^ 2 ∂μ) +
    ∫ x, (2 * C₁ ^ 2 * M ^ 3) * Q x ∂μ) at h
  rw [integral_const, smul_eq_mul, integral_const_mul] at h
  refine h.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity))
  · exact mul_le_of_le_one_left (by positivity) hμ
  · exact mul_le_mul_of_nonneg_left hQsumInt (by positivity)

end KEBall
