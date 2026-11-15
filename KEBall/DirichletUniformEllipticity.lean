import KEBall.DirichletInteriorHessian
import KEBall.FiberEnergyGreen
import KEBall.BedfordTaylorQuadraticTaylorModel

/-!
# Uniform ellipticity of the prescribed Dirichlet equation

A closed-ball Hessian bound and a positive determinant lower bound
bound the eigenvalues of the complex Hessian. Diagonalizing its inverse
identifies explicit ellipticity bounds for the real principal symbol.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix Matrix.Norms.Elementwise Topology

namespace KEBall

private theorem lower_density_on_closedBall {n : ℕ} {f : E n → ℝ}
    (hf : SmoothNear (closedUnitBall n) f) {c : ℝ}
    (hDensity : ∀ y ∈ unitBall n, c ≤ f y) {x : E n} (hx : x ∈ closedUnitBall n) :
    c ≤ f x := by
  have hxCl : x ∈ closure (unitBall n) := by
    rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    exact hx
  have : NeBot (𝓝[unitBall n] x) := mem_closure_iff_nhdsWithin_neBot.mp hxCl
  have hF : Tendsto f (𝓝[unitBall n] x) (𝓝 (f x)) :=
    (hf.contDiffAt hx).continuousAt.continuousWithinAt
  apply ge_of_tendsto hF
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hDensity y hy

/-- The interior positive-definite complex Hessian remains positive definite
up to the sphere when the prescribed density is bounded below. -/
theorem dirichlet_posDef_on_closedBall {n : ℕ} {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {a : ℝ} (ha : 0 < a) (hDensity : ∀ y ∈ unitBall n, a ^ n ≤ f y)
    {x : E n} (hx : x ∈ closedUnitBall n) :
    (complexHessian u x).PosDef := by
  have hxCl : x ∈ closure (unitBall n) := by
    rw [unitBall, closure_ball (0 : E n) (by norm_num : (1 : ℝ) ≠ 0)]
    exact hx
  have : NeBot (𝓝[unitBall n] x) := mem_closure_iff_nhdsWithin_neBot.mp hxCl
  have hFlo := lower_density_on_closedBall hf hDensity hx
  have hDet := dirichlet_det_eq_on_closedBall hu hf huP hEq hx
  have hH : (complexHessian u x).IsHermitian :=
    MoserTrudinger.complexHessian_isHermitian_of_smooth (hu.contDiffAt hx)
  have hHcont (i j : Fin n) : ContinuousAt (fun y => complexHessian u y i j) x := by
    obtain ⟨U, hU, hSub, huU⟩ := hu
    exact ((complexHessian_contDiffOn hU huU i j).contDiffAt (hU.mem_nhds (hSub hx))).continuousAt
  have hNonneg (z : Fin n → ℂ) : 0 ≤ (star z ⬝ᵥ (complexHessian u x *ᵥ z)).re := by
    have hCont : ContinuousAt (fun y => (star z ⬝ᵥ (complexHessian u y *ᵥ z)).re) x := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    have hQ : Tendsto (fun y => (star z ⬝ᵥ (complexHessian u y *ᵥ z)).re)
        (𝓝[unitBall n] x) (𝓝 (star z ⬝ᵥ (complexHessian u x *ᵥ z)).re) :=
      hCont.continuousWithinAt
    apply ge_of_tendsto hQ
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (huP y hy).posSemidef.re_dotProduct_nonneg z
  have hSemi : (complexHessian u x).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
      (fun z => RCLike.nonneg_iff.mpr ⟨hNonneg z, hH.im_star_dotProduct_mulVec_self z⟩)
  apply hSemi.posDef_iff_det_ne_zero.mpr
  rw [hDet]
  exact_mod_cast ((pow_pos ha n).trans_le hFlo).ne'

private theorem complexHessian_eigenvalues_le_of_realHessian {n : ℕ} {u : E n → ℝ}
    {x : E n} (hu : ContDiffAt ℝ ∞ u x) (hA : (complexHessian u x).IsHermitian)
    {D : ℝ} (hD : ∀ v : E n, ‖v‖ = 1 → realHessian u x v v ≤ D) (i : Fin n) :
    hA.eigenvalues i ≤ D / 2 := by
  let z : EuclideanSpace ℂ (Fin n) := hA.eigenvectorBasis i
  obtain ⟨v, hv⟩ := complexCoord_surjective (star z.ofLp)
  have hz : ‖z‖ = 1 := hA.eigenvectorBasis.norm_eq_one i
  have hDot : z.ofLp ⬝ᵥ star z.ofLp = 1 := by
    rw [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hz]
    norm_num
  have hvNorm : ‖v‖ = 1 := by
    have h := sum_star_complexCoord_mul v
    change star (complexCoord v) ⬝ᵥ complexCoord v = _ at h
    rw [hv, star_star, hDot] at h
    have hSq : ‖v‖ ^ 2 = 1 := by
      have hr := congrArg Complex.re h
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] using hr.symm
    nlinarith only [hSq, norm_nonneg v]
  have hMetric : realMetricForm u x v v = 2 * hA.eigenvalues i := by
    rw [realMetricForm_eq, hermitianRealification_eq_re_dotProduct, hv, star_star]
    congr 1
    exact (hA.eigenvalues_eq i).symm
  rw [realMetricForm_eq_average_hessian hu] at hMetric
  have hJ := hD (J v) (by rw [norm_J, hvNorm])
  linarith only [hMetric, hD v hvNorm, hJ]

/-- A second derivative bound and a positive determinant bound confine the
complex Hessian eigenvalues to a uniform positive interval. -/
theorem complexHessian_eigenvalues_bounds_of_dirichlet_det {n : ℕ} {u f : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) (hf : SmoothNear (closedUnitBall n) f)
    (huP : ∀ y ∈ unitBall n, (complexHessian u y).PosDef)
    (hEq : ∀ y ∈ unitBall n, (complexHessian u y).det.re = f y)
    {a D : ℝ} (ha : 0 < a) (hD : 0 < D)
    (hDensity : ∀ y ∈ unitBall n, a ^ n ≤ f y)
    (hSecond : ∀ y ∈ closedUnitBall n, ∀ v : E n, ‖v‖ = 1 → realHessian u y v v ≤ D)
    {x : E n} (hx : x ∈ closedUnitBall n) (i : Fin n) :
    let hA := (dirichlet_posDef_on_closedBall hu hf huP hEq ha hDensity hx).isHermitian
    a ^ n / (D / 2) ^ (n - 1) ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ D / 2 := by
  let hp := dirichlet_posDef_on_closedBall hu hf huP hEq ha hDensity hx
  let hA := hp.isHermitian
  let eigenvalues := hA.eigenvalues
  have hUp (j : Fin n) : eigenvalues j ≤ D / 2 :=
    complexHessian_eigenvalues_le_of_realHessian (hu.contDiffAt hx) hA (hSecond x hx) j
  have hPos (j : Fin n) : 0 < eigenvalues j := hp.eigenvalues_pos j
  have hFlo := lower_density_on_closedBall hf hDensity hx
  have hEqProd : f x = ∏ j : Fin n, eigenvalues j := by
    have he := hA.det_eq_prod_eigenvalues
    rw [dirichlet_det_eq_on_closedBall hu hf huP hEq hx, ← RCLike.ofReal_prod] at he
    exact Complex.ofReal_injective he
  have hProd : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, eigenvalues j) ≤
      (D / 2) ^ (n - 1) := by
    calc
      _ ≤ ∏ _j ∈ (Finset.univ : Finset (Fin n)).erase i, D / 2 :=
        Finset.prod_le_prod (fun j _ => (hPos j).le) (fun j _ => hUp j)
      _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
  change a ^ n / (D / 2) ^ (n - 1) ≤ eigenvalues i ∧ eigenvalues i ≤ D / 2
  refine ⟨(div_le_iff₀ (pow_pos (by positivity) _)).mpr ?_, hUp i⟩
  rw [hEqProd, ← Finset.mul_prod_erase Finset.univ eigenvalues (Finset.mem_univ i)] at hFlo
  exact hFlo.trans (mul_le_mul_of_nonneg_left hProd (hPos i).le)

private theorem inv_eq_unitary_conj_diagonal {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) :
    H⁻¹ = Unitary.conjStarAlgAut ℂ _ hH.isHermitian.eigenvectorUnitary
      (Matrix.diagonal (fun i => ((hH.isHermitian.eigenvalues i)⁻¹ : ℝ) : Fin n → ℂ)) := by
  let e := Unitary.conjStarAlgAut ℂ _ hH.isHermitian.eigenvectorUnitary
  let d : Fin n → ℂ := fun i => hH.isHermitian.eigenvalues i
  let di : Fin n → ℂ := fun i => ((hH.isHermitian.eigenvalues i)⁻¹ : ℝ)
  have he : H = e (Matrix.diagonal d) := hH.isHermitian.spectral_theorem
  change H⁻¹ = e (Matrix.diagonal di)
  apply Matrix.inv_eq_right_inv
  rw [he, ← map_mul, Matrix.diagonal_mul_diagonal]
  have hD : d * di = 1 := by
    funext i
    change (hH.isHermitian.eigenvalues i : ℂ) * ((hH.isHermitian.eigenvalues i)⁻¹ : ℝ) = 1
    have hh : (hH.isHermitian.eigenvalues i : ℂ) ≠ 0 := by
      exact_mod_cast (hH.eigenvalues_pos i).ne'
    rw [Complex.ofReal_inv, mul_inv_cancel₀ hh]
  change e (Matrix.diagonal (d * di)) = 1
  rw [hD]
  change e (Matrix.diagonal (fun _ : Fin n => (1 : ℂ))) = 1
  rw [Matrix.diagonal_one, map_one]

private theorem dotProduct_unitary_conj {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℂ))
    (H : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    star z ⬝ᵥ ((Unitary.conjStarAlgAut ℂ _ U H) *ᵥ z) =
      star (star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z) ⬝ᵥ
        (H *ᵥ (star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z)) := by
  rw [Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- The quadratic form of the inverse complex Hessian has reciprocal
bounds, expressed in the ordinary complex Euclidean coordinates. -/
theorem inverse_complex_quadratic_bounds_of_eigenvalues {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) {l L : ℝ} (hl : 0 < l)
    (hE : ∀ i, l ≤ hH.isHermitian.eigenvalues i ∧ hH.isHermitian.eigenvalues i ≤ L)
    (z : Fin n → ℂ) :
    L⁻¹ * (star z ⬝ᵥ z).re ≤ (star z ⬝ᵥ (H⁻¹ *ᵥ z)).re ∧
      (star z ⬝ᵥ (H⁻¹ *ᵥ z)).re ≤ l⁻¹ * (star z ⬝ᵥ z).re := by
  let U := hH.isHermitian.eigenvectorUnitary
  let v := star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z
  have hzv : star z ⬝ᵥ z = star v ⬝ᵥ v := by
    simpa only [v, map_one, Matrix.one_mulVec] using
      dotProduct_unitary_conj U (1 : Matrix (Fin n) (Fin n) ℂ) z
  have hTerm (d : ℝ) (w : ℂ) :
      (star w * ((d : ℂ) * w)).re = d * Complex.normSq w := by
    have h := Complex.mul_conj w
    rw [show star w * ((d : ℂ) * w) = (d : ℂ) * (w * star w) by ring]
    rw [Complex.star_def, h]
    simp
  have hWeighted :
      (star z ⬝ᵥ (H⁻¹ *ᵥ z)).re =
        ∑ i, (hH.isHermitian.eigenvalues i)⁻¹ * Complex.normSq (v i) := by
    rw [inv_eq_unitary_conj_diagonal hH, dotProduct_unitary_conj]
    change (star v ⬝ᵥ (Matrix.diagonal (fun i => ((hH.isHermitian.eigenvalues i)⁻¹ : ℝ) : Fin n → ℂ) *ᵥ v)).re = _
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum, hTerm]
  have hMass : (star z ⬝ᵥ z).re = ∑ i, Complex.normSq (v i) := by
    rw [hzv]
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.ofReal_one, one_mul] using hTerm 1 (v i)
  rw [hWeighted, hMass, Finset.mul_sum, Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro i _
  · exact mul_le_mul_of_nonneg_right (inv_le_inv₀ ((hH.eigenvalues_pos i).trans_le (hE i).2)
      (hH.eigenvalues_pos i) |>.mpr (hE i).2) (Complex.normSq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (inv_le_inv₀ (hH.eigenvalues_pos i)
      hl |>.mpr (hE i).1) (Complex.normSq_nonneg _)

/-- The principal symbol of the real linearized operator is one quarter of
the inverse complex Hessian quadratic form in complex coordinates. -/
theorem complexLaplacian_rankOne_quadratic {n : ℕ} (u : E n → ℝ) (x v : E n) :
    complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x =
      (star (star (complexCoord v)) ⬝ᵥ ((complexHessian u x)⁻¹ *ᵥ star (complexCoord v))).re / 4 := by
  let q : E n → ℝ := fun y => (inner ℝ v y) ^ 2 / 2
  let L : E n →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (E n) v
  let A : E n →L[ℝ] E n →L[ℝ] ℝ := L.smulRight L
  have he : q = BedfordTaylor.quadraticTaylorModel 0 0 0 A := by
    funext y
    simp [q, BedfordTaylor.quadraticTaylorModel, A, L, InnerProductSpace.toDual_apply_apply, pow_two]
  have hq : ContDiffAt ℝ ∞ q x := by
    rw [he]
    exact (BedfordTaylor.contDiff_quadraticTaylorModel 0 0 0 A).contDiffAt
  have hHess (a b : E n) : realHessian q x a b = inner ℝ v a * inner ℝ v b := by
    change fderiv ℝ (fderiv ℝ q) x a b = _
    rw [← PshLines.realHessian_eq_fderiv, he, BedfordTaylor.realHessian_quadraticTaylorModel]
    simp only [A, ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul, L,
      InnerProductSpace.toDual_apply_apply]
    ring
  have hMat : complexHessian q x =
      (4 : ℂ)⁻¹ • Matrix.vecMulVec (star (complexCoord v)) (complexCoord v) := by
    ext i j
    rw [complexHessian_real_entry hq, hHess, hHess, hHess, hHess]
    simp [complexCoord, realDirection, imagDirection, EuclideanSpace.inner_single_right,
      Matrix.vecMulVec_apply, Pi.star_apply]
    ring_nf
    rw [Complex.I_sq]
    ring
  change complexLaplacian u q x = _
  rw [complexLaplacian_eq_trace, hMat, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, star_star, smul_eq_mul]
  rw [dotProduct_comm ((complexHessian u x)⁻¹ *ᵥ star (complexCoord v)) (complexCoord v)]
  simp [Complex.mul_re, div_eq_mul_inv, mul_comm]

/-- Reciprocal eigenvalue bounds give uniform ellipticity bounds for the
actual linearization evaluated on every real rank-one direction. -/
theorem complexLaplacian_rankOne_bounds {n : ℕ} {u : E n → ℝ} {x : E n}
    (hH : (complexHessian u x).PosDef) {l L : ℝ} (hl : 0 < l)
    (hE : ∀ i, l ≤ hH.isHermitian.eigenvalues i ∧ hH.isHermitian.eigenvalues i ≤ L)
    (v : E n) :
    (L⁻¹ / 4) * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x ∧
      complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x ≤ (l⁻¹ / 4) * ‖v‖ ^ 2 := by
  have h := inverse_complex_quadratic_bounds_of_eigenvalues hH hl hE (star (complexCoord v))
  have hMass : (star (star (complexCoord v)) ⬝ᵥ star (complexCoord v)).re = ‖v‖ ^ 2 := by
    rw [star_star, dotProduct_comm]
    have h := sum_star_complexCoord_mul v
    change star (complexCoord v) ⬝ᵥ complexCoord v = _ at h
    rw [h, Complex.ofReal_re]
  rw [hMass] at h
  rw [complexLaplacian_rankOne_quadratic]
  exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

/-- The density and log-density bounds fix positive ellipticity constants
for every smooth solution in the prescribed Dirichlet family. -/
theorem exists_uniform_ellipticity_of_dirichlet_density_bounds {n : ℕ} (hn : 0 < n)
    {a b K M : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    ∃ l L : ℝ, 0 < l ∧ 0 < L ∧
      ∀ {u f : E n → ℝ}, SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
        (∀ x ∈ unitSphere n, u x = 0) →
        (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
        (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
        (∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n) →
        (∀ x ∈ unitBall n, ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ K) →
        (∀ x ∈ unitBall n, ∀ v : E n, ‖v‖ = 1 →
          -M ≤ realHessian (fun y => Real.log (f y)) x v v) →
        ∀ x ∈ closedUnitBall n, ∀ v : E n,
          l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x ∧
            complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x ≤ L * ‖v‖ ^ 2 := by
  let c := (3 * K + 1) / (n : ℝ)
  let C := 2 * b + 4 * b * c +
    (2 * b + 4 * (b ^ n / a ^ (n - 1) + (b * c) ^ 2 / (4 * a)))
  let D := C + ((M + 1) / (n : ℝ)) * b
  have hD : 0 < D := by
    dsimp [D, C, c]
    positivity
  let lH := a ^ n / (D / 2) ^ (n - 1)
  have hlH : 0 < lH := by dsimp [lH]; positivity
  refine ⟨(D / 2)⁻¹ / 4, lH⁻¹ / 4, by positivity, by positivity, ?_⟩
  intro u f hu hf hu0 huP hEq hDensity hGrad hHess x hx v
  have hB (y : E n) (hy : y ∈ unitSphere n) (w : E n) (hw : ‖w‖ = 1) :
      |realHessian u y w w| ≤ C :=
    abs_realHessian_self_le_on_sphere_of_dirichlet_det hn hu hf hu0 huP hEq
      ha hb hK hDensity hGrad hy hw
  have hSecond (y : E n) (hy : y ∈ closedUnitBall n) (w : E n) (hw : ‖w‖ = 1) :
      realHessian u y w w ≤ D := (le_abs_self _).trans
    (abs_realHessian_self_le_of_dirichlet_det hn hu hf hu0 huP hEq
      ha hb hM hDensity hB hHess y hy w hw)
  have hLower (y : E n) (hy : y ∈ unitBall n) : a ^ n ≤ f y := (hDensity y hy).1
  exact complexLaplacian_rankOne_bounds (dirichlet_posDef_on_closedBall hu hf huP hEq ha hLower hx)
    hlH (complexHessian_eigenvalues_bounds_of_dirichlet_det hu hf huP hEq ha hD hLower hSecond hx) v

end KEBall
