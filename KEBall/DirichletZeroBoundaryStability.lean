import KEBall.DirichletHessianStability
import KEBall.BoundaryConormal

/-! The boundary cofactor sign and an L² stability estimate for the Dirichlet problem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix MatrixOrder Matrix.Norms.Elementwise Topology

namespace KEBall

private theorem inner_cofactorRealField_of_zero_boundary {n : ℕ} (hn : 0 < n)
    {u h : E n → ℝ} (hu : SmoothNear (closedUnitBall n) u)
    (hh : SmoothNear (closedUnitBall n) h)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hh0 : ∀ x ∈ unitSphere n, h x = 0)
    {x : E n} (hx : x ∈ unitSphere n) (hs : 0 < boundarySlope u x)
    (hdet : (complexHessian u x).det ≠ 0) :
    inner ℝ x (cofactorRealField u h x) =
      boundarySlope u x ^ (n - 1) * boundarySlope h x := by
  let c := boundaryNormalComplex x
  let b := boundaryMixedComplex u x
  let A := (complexHessian u x).adjugate
  have ht : (boundarySlope u x : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hAdj : A.mulVec c = (boundarySlope u x : ℂ) ^ (n - 1) •
      (c - (boundarySlope u x : ℂ)⁻¹ • b) := by
    dsimp only [A, b, c]
    have hb := sphere_complexHessian_block hu hu0 hx
    rw [hb] at hdet ⊢
    exact borderedScalarMatrix_adjugate_normal (by omega) ht
      (boundaryNormalComplex_unit hx) (boundaryMixedComplex_orthogonal u hx)
      (boundaryMixedComplex_orthogonal_reverse u hx) hdet
  have hPair : star c ⬝ᵥ (A.mulVec c) = (boundarySlope u x : ℂ) ^ (n - 1) := by
    rw [hAdj, dotProduct_smul, dotProduct_sub, dotProduct_smul]
    rw [show star c ⬝ᵥ c = 1 from boundaryNormalComplex_unit hx,
      show star c ⬝ᵥ b = 0 from boundaryMixedComplex_orthogonal u hx]
    simp
  have hFlux : inner ℝ x (cofactorRealField u h x) =
      (∑ j, (A.mulVec c) j * partialBar j (fun y => (h y : ℂ)) x).re := by
    rw [cofactorRealField, inner_complexVectorReal]
    simp only [cofactorVectorField, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mulVec, dotProduct, c, boundaryNormalComplex, Pi.star_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hFlux]
  simp_rw [sphere_partialBar hh hh0 hx]
  have he : (∑ j, (A.mulVec c) j * ((boundarySlope h x : ℂ) * complexCoord x j)) =
      (boundarySlope h x : ℂ) * (star c ⬝ᵥ (A.mulVec c)) := by
    rw [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [c, boundaryNormalComplex, star_star]
    ring
  rw [he, hPair, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

/-- The integrated cofactor pairing for two zero-boundary potentials
is nonpositive if both normal slopes are positive. -/
theorem integral_cofactor_difference_nonpos_of_zero_boundary {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {u v : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hs : ∀ x ∈ unitSphere n, 0 < boundarySlope u x ∧ 0 < boundarySlope v x)
    (hdet : ∀ x ∈ unitSphere n, (complexHessian u x).det ≠ 0 ∧ (complexHessian v x).det ≠ 0) :
    (∫ x in unitBall n, (((complexHessian u x).adjugate - (complexHessian v x).adjugate) *
        (complexHessian v x - complexHessian u x)).trace.re ∂volume0 n) ≤ 0 := by
  rw [integral_cofactor_difference_eq_boundary hn hU hSub hu hv huP hvP]
  apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
  apply integral_nonpos
  intro θ
  let x := θ.val
  have hx := θ.property
  have hU' : SmoothNear (closedUnitBall n) u := ⟨U, hU, hSub, hu⟩
  have hV' : SmoothNear (closedUnitBall n) v := ⟨U, hU, hSub, hv⟩
  have hh : SmoothNear (closedUnitBall n) (v - u) := ⟨U, hU, hSub, hv.sub hu⟩
  have hh0 (y : E n) (hy : y ∈ unitSphere n) : (v - u) y = 0 := by simp [hu0 y hy, hv0 y hy]
  have he : boundarySlope (v - u) x = boundarySlope v x - boundarySlope u x := by
    have hN := hU.mem_nhds (hSub (sphere_subset_closedBall hx))
    unfold boundarySlope
    rw [fderiv_sub ((hv.contDiffAt hN).differentiableAt (by simp))
      ((hu.contDiffAt hN).differentiableAt (by simp)), _root_.sub_apply]
    ring
  change inner ℝ x (cofactorRealField u (v - u) x - cofactorRealField v (v - u) x) ≤ 0
  rw [inner_sub_right, inner_cofactorRealField_of_zero_boundary hn hU' hh hu0 hh0 hx
    (hs x hx).1 (hdet x hx).1, inner_cofactorRealField_of_zero_boundary hn hV' hh hv0 hh0 hx
    (hs x hx).2 (hdet x hx).2, he, ← sub_mul]
  rcases le_total (boundarySlope u x) (boundarySlope v x) with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (pow_le_pow_left₀ (hs x hx).1.le h _))
      (sub_nonneg.mpr h)
  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (pow_le_pow_left₀ (hs x hx).2.le h _))
      (sub_nonpos.mpr h)


private theorem abs_trace_mul_le_of_norm_bound {n : ℕ}
    (R H : Matrix (Fin n) (Fin n) ℂ) {K : ℝ} (hR : ‖R‖ ≤ K) :
    |(R * H).trace.re| ≤
      (K * (n : ℝ) ^ 2) * Real.sqrt (∑ i, ∑ j, ‖H i j‖ ^ 2) := by
  let q : ℝ := ∑ i, ∑ j, ‖H i j‖ ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hH (i j : Fin n) : ‖H i j‖ ≤ Real.sqrt q := by
    have hle : ‖H i j‖ ^ 2 ≤ q :=
      (Finset.single_le_sum (f := fun l => ‖H i l‖ ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun k => ∑ l, ‖H k l‖ ^ 2)
          (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _)) (Finset.mem_univ i))
    nlinarith only [hle, Real.sq_sqrt hq, norm_nonneg (H i j), Real.sqrt_nonneg q]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  calc
    _ ≤ ‖∑ i, ∑ j, R i j * H j i‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖R i j * H j i‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, K * Real.sqrt q := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm R |>.trans hR)
        (hH j i) (norm_nonneg _) ((norm_nonneg R).trans hR)
    _ = _ := by simp [Finset.sum_const]; ring

/-- For uniformly elliptic smooth Dirichlet solutions with zero boundary data,
the complex Hessian is Lipschitz in the density in the integrated square norm. -/
theorem integral_sq_complexHessian_sub_le_of_zero_boundary {n : ℕ} (hn : 0 < n)
    {U : Set (E n)} (hU : IsOpen U) (hSub : closedUnitBall n ⊆ U)
    {u v : E n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hvP : ∀ x ∈ unitBall n, (complexHessian v x).PosDef)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0) (hv0 : ∀ x ∈ unitSphere n, v x = 0)
    (hs : ∀ x ∈ unitSphere n, 0 < boundarySlope u x ∧ 0 < boundarySlope v x)
    (hdet : ∀ x ∈ unitSphere n, (complexHessian u x).det ≠ 0 ∧ (complexHessian v x).det ≠ 0)
    {a d K : ℝ} (ha : 0 < a) (hd : 0 < d) (hK : 0 ≤ K)
    (hDen : ∀ x ∈ unitBall n, d ≤ (complexHessian u x).det.re)
    (hInv : ∀ x ∈ unitBall n,
      (a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (complexHessian u x)⁻¹ ∧
      (a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (complexHessian v x)⁻¹)
    (hNorm : ∀ x ∈ unitBall n, ‖(complexHessian v x)⁻¹‖ ≤ K) :
    (d * a ^ 2) ^ 2 * (∫ x in unitBall n, ∑ i, ∑ j,
      ‖(complexHessian v x - complexHessian u x) i j‖ ^ 2 ∂volume0 n) ≤
      (K * (n : ℝ) ^ 2) ^ 2 *
        ∫ x in unitBall n, ((complexHessian v x).det.re - (complexHessian u x).det.re) ^ 2 ∂volume0 n := by
  have : NeZero n := ⟨hn.ne'⟩
  let μ := (volume0 n).restrict (unitBall n)
  let A := complexHessian u
  let B := complexHessian v
  let q (x : E n) : ℝ := ∑ i, ∑ j, ‖(B x - A x) i j‖ ^ 2
  let p (x : E n) : ℝ := (((A x).adjugate - (B x).adjugate) * (B x - A x)).trace.re
  let g (x : E n) : ℝ := (B x).det.re - (A x).det.re
  let c : ℝ := d * a ^ 2
  let k : ℝ := K * (n : ℝ) ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hA : ContinuousOn A U := continuousOn_pi.mpr fun i =>
    continuousOn_pi.mpr fun j => (complexHessian_contDiffOn hU hu i j).continuousOn
  have hB : ContinuousOn B U := continuousOn_pi.mpr fun i =>
    continuousOn_pi.mpr fun j => (complexHessian_contDiffOn hU hv i j).continuousOn
  have hQ : ContinuousOn q U := continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_finsetSum Finset.univ fun j _ =>
      ((continuousOn_pi.mp (continuousOn_pi.mp (hB.sub hA) i) j).norm).pow 2
  have hP : ContinuousOn p U := by
    apply Complex.continuous_re.comp_continuousOn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((continuousOn_pi.mp (continuousOn_pi.mp
      (continuous_id.matrix_adjugate.comp_continuousOn hA) i) j).sub
      (continuousOn_pi.mp (continuousOn_pi.mp
        (continuous_id.matrix_adjugate.comp_continuousOn hB) i) j)).mul
          (continuousOn_pi.mp (continuousOn_pi.mp (hB.sub hA) j) i)
  have hG : ContinuousOn g U :=
    ((Complex.continuous_re.comp continuous_id.matrix_det).comp_continuousOn hB).sub
      ((Complex.continuous_re.comp continuous_id.matrix_det).comp_continuousOn hA)
  have hI {w : E n → ℝ} (hw : ContinuousOn w U) : Integrable w μ :=
    (hw.mono hSub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hMono : (fun x => c ^ 2 * q x) ≤ᵐ[μ] fun x => (2 * c) * p x + k ^ 2 * g x ^ 2 := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have hq : 0 ≤ q x := by dsimp [q]; positivity
    have he := posDef_cofactor_difference_trace_ge (huP x hx) (hvP x hx)
      ha.le (hInv x hx).1 (hInv x hx).2
    have hFirst : c * q x ≤ p x + |g x| * (k * Real.sqrt (q x)) := by
      calc
        c * q x ≤ (A x).det.re * a ^ 2 * q x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hDen x hx) (sq_nonneg _)) hq
        _ ≤ p x + g x * ((B x)⁻¹ * (B x - A x)).trace.re := he
        _ ≤ p x + |g x| * (k * Real.sqrt (q x)) := by
          apply add_le_add_right
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (abs_trace_mul_le_of_norm_bound _ _ (hNorm x hx)) (abs_nonneg _)
    have hYoung : 2 * (c * Real.sqrt (q x)) * (k * |g x|) ≤ c ^ 2 * q x + k ^ 2 * g x ^ 2 := by
      have h := sq_nonneg (c * Real.sqrt (q x) - k * |g x|)
      have h₁ : (c * Real.sqrt (q x)) ^ 2 = c ^ 2 * q x := by
        rw [mul_pow, Real.sq_sqrt hq]
      have h₂ : (k * |g x|) ^ 2 = k ^ 2 * g x ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith only [h, h₁, h₂]
    have hScaled := mul_le_mul_of_nonneg_left hFirst (show 0 ≤ 2 * c by positivity)
    have hScaled' : 2 * c ^ 2 * q x ≤ (2 * c) * p x + 2 * (c * Real.sqrt (q x)) * (k * |g x|) := by
      calc
        _ = (2 * c) * (c * q x) := by ring
        _ ≤ (2 * c) * (p x + |g x| * (k * Real.sqrt (q x))) := hScaled
        _ = _ := by ring
    linarith only [hScaled', hYoung]
  have h := integral_mono_ae ((hI hQ).const_mul (c ^ 2))
    (((hI hP).const_mul (2 * c)).add ((hI (hG.pow 2)).const_mul (k ^ 2))) hMono
  change (∫ x, c ^ 2 * q x ∂μ) ≤ (∫ x, (2 * c) * p x + k ^ 2 * g x ^ 2 ∂μ) at h
  have hGSq : ContinuousOn (fun x => g x ^ 2) U := hG.pow 2
  rw [integral_const_mul, integral_add ((hI hP).const_mul (2 * c))
    ((hI hGSq).const_mul (k ^ 2)), integral_const_mul, integral_const_mul] at h
  have hFlux : (∫ x, p x ∂μ) ≤ 0 :=
    integral_cofactor_difference_nonpos_of_zero_boundary hn hU hSub hu hv huP hvP hu0 hv0 hs hdet
  exact h.trans (by linarith only [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * c by positivity) hFlux])

end KEBall
