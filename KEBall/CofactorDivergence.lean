import KEBall.LocalWirtinger
import KEBallProbe.ComplexDeterminant

/-!
# Cofactor divergence in arbitrary finite complex dimension

The matrix is differentiated by the actual constant-direction Wirtinger
operators.  The proof differentiates `G * adjugate G = det G • 1` and uses
Jacobi's formula together with the equality of the mixed row derivatives.
Nonsingularity is required only at the point under consideration.

This is the cofactor convention of KE_Ball_Symmetry_20261012_v4.tex:
`det G * g^{i bar j} = (adjugate G) j i`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators Matrix Matrix.Norms.Elementwise

namespace KEBall
open KEBallProbe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rd_mul_differentiableAt {f h : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (v : E) :
    rd v (fun y => f y * h y) x = rd v f x * h x + f x * rd v h x := by
  simp only [rd, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

lemma dz_mul_differentiableAt {f h : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (a b : E) :
    dz a b (fun y => f y * h y) x = dz a b f x * h x + f x * dz a b h x := by
  unfold dz
  rw [rd_mul_differentiableAt hf hh, rd_mul_differentiableAt hf hh]
  ring

omit [DecidableEq ι] in
lemma rd_sum_differentiableAt {f : ι → E → ℂ} {x : E}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (v : E) :
    rd v (fun y => ∑ i, f i y) x = ∑ i, rd v (f i) x := by
  simp only [rd, fderiv_fun_sum (fun i _ => hf i), _root_.sum_apply]

omit [DecidableEq ι] in
lemma dz_sum_differentiableAt {f : ι → E → ℂ} {x : E}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (a b : E) :
    dz a b (fun y => ∑ i, f i y) x = ∑ i, dz a b (f i) x := by
  unfold dz
  rw [rd_sum_differentiableAt hf, rd_sum_differentiableAt hf]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]

private noncomputable def cofactorDetMultilinear :
    ContinuousMultilinearMap ℂ (fun _ : ι => ι → ℂ) ℂ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

lemma complex_det_differentiableAt (A : Matrix ι ι ℂ) :
    DifferentiableAt ℝ Matrix.det A := by
  exact ((cofactorDetMultilinear.hasFDerivAt A).restrictScalars ℝ).differentiableAt

lemma field_det_differentiableAt {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) :
    DifferentiableAt ℝ (fun y => (G y).det) x := by
  exact (complex_det_differentiableAt (G x)).comp x
    (differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr (hG i))

lemma field_adjugate_differentiableAt {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) (i j : ι) :
    DifferentiableAt ℝ (fun y => (G y).adjugate i j) x := by
  simp_rw [Matrix.adjugate_apply]
  apply field_det_differentiableAt
  intro r k
  by_cases hr : r = j
  · subst r
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simpa only [Matrix.updateRow_ne hr] using hG r k

/-- Jacobi's formula for a real directional derivative of a complex matrix field. -/
lemma rd_det_field {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) (v : E) :
    rd v (fun y => (G y).det) x =
      ∑ i, ∑ j, (G x).adjugate j i * rd v (fun y => G y i j) x := by
  have hdG : HasFDerivAt G
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        fderiv ℝ (fun y => G y i j) x) x :=
    hasFDerivAt_pi.mpr fun i => hasFDerivAt_pi.mpr fun j => (hG i j).hasFDerivAt
  have h := (complex_det_differentiableAt (G x)).hasFDerivAt.comp x hdG
  change HasFDerivAt (fun y => (G y).det)
    ((fderiv ℝ Matrix.det (G x)).comp
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        fderiv ℝ (fun y => G y i j) x)) x at h
  rw [rd, h.fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ Matrix.det (G x)
    (fun i j => fderiv ℝ (fun y => G y i j) x v) = _
  rw [fderiv_real_complex_det]
  simp only [Matrix.trace]
  rw [Finset.sum_comm]
  rfl

/-- Jacobi's formula with precisely the paper's Wirtinger normalization. -/
lemma dz_det_field {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) (a b : E) :
    dz a b (fun y => (G y).det) x =
      ∑ i, ∑ j, (G x).adjugate j i * dz a b (fun y => G y i j) x := by
  unfold dz
  rw [rd_det_field hG, rd_det_field hG]
  calc
    _ = ∑ i, ∑ j, (2 : ℂ)⁻¹ *
        ((G x).adjugate j i * rd a (fun y => G y i j) x -
          Complex.I * ((G x).adjugate j i * rd b (fun y => G y i j) x)) := by
      simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The differentiated adjugate identity.  Its row-commutation hypothesis is
subsequently proved from an actual locally smooth potential. -/
theorem cofactor_divergence_of_commuting_rows {G : E → Matrix ι ι ℂ} {x : E}
    (a b : ι → E)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x)
    (hcomm : ∀ i r k,
      dz (a i) (b i) (fun y => G y r k) x =
        dz (a r) (b r) (fun y => G y i k) x)
    (hunit : IsUnit (G x).det) (j : ι) :
    (∑ i, dz (a i) (b i) (fun y => (G y).adjugate j i) x) = 0 := by
  let V : ι → ℂ := fun k =>
    ∑ i, dz (a i) (b i) (fun y => (G y).adjugate k i) x
  have hC := field_adjugate_differentiableAt hG
  have hdprod (r i : ι) :
      (∑ k, (dz (a i) (b i) (fun y => G y r k) x * (G x).adjugate k i +
        G x r k * dz (a i) (b i) (fun y => (G y).adjugate k i) x)) =
      if r = i then dz (a i) (b i) (fun y => (G y).det) x else 0 := by
    have hprod : (fun y => ∑ k, G y r k * (G y).adjugate k i) =
        if r = i then (fun y => (G y).det) else (fun _ : E => (0 : ℂ)) := by
      funext y
      have heq := congrArg (fun M : Matrix ι ι ℂ => M r i) (Matrix.mul_adjugate (G y))
      by_cases hri : r = i
      · simpa [hri, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using heq
      · simpa [hri, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using heq
    calc
      _ = dz (a i) (b i) (fun y => ∑ k, G y r k * (G y).adjugate k i) x := by
        rw [dz_sum_differentiableAt
          (f := fun k y => G y r k * (G y).adjugate k i)
          (fun k => (hG r k).fun_mul (hC k i))]
        apply Finset.sum_congr rfl
        intro k _
        exact (dz_mul_differentiableAt (hG r k) (hC k i) (a i) (b i)).symm
      _ = _ := by
        rw [hprod]
        split_ifs <;> simp [dz, rd]
  have hrow : (G x) *ᵥ V = 0 := by
    funext r
    have hfirst :
        (∑ i, ∑ k, dz (a i) (b i) (fun y => G y r k) x * (G x).adjugate k i) =
          dz (a r) (b r) (fun y => (G y).det) x := by
      rw [dz_det_field hG]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [hcomm i r k, mul_comm]
    have hsum :
        (∑ i, ∑ k, (dz (a i) (b i) (fun y => G y r k) x * (G x).adjugate k i +
          G x r k * dz (a i) (b i) (fun y => (G y).adjugate k i) x)) =
          dz (a r) (b r) (fun y => (G y).det) x := by
      calc
        _ = ∑ i, if r = i then dz (a i) (b i) (fun y => (G y).det) x else 0 :=
          Finset.sum_congr rfl (fun i _ => hdprod r i)
        _ = _ := by simp
    simp only [Finset.sum_add_distrib] at hsum
    rw [hfirst] at hsum
    have hzero :
        (∑ i, ∑ k, G x r k * dz (a i) (b i) (fun y => (G y).adjugate k i) x) = 0 :=
      add_left_cancel (hsum.trans (add_zero _).symm)
    change (∑ k, G x r k * (∑ i,
      dz (a i) (b i) (fun y => (G y).adjugate k i) x)) = 0
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact hzero
  have hV := congrArg (fun w : ι → ℂ => (G x)⁻¹ *ᵥ w) hrow
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
    Matrix.one_mulVec, Matrix.mulVec_zero] at hV
  exact congrFun hV j

/-- Complex Hessian from the fixed real Frechet derivative convention. -/
noncomputable def wirtingerHessian (a b : ι → E) (f : E → ℂ) (x : E) :
    Matrix ι ι ℂ :=
  fun i k => dz (a i) (b i) (dz (a k) (-b k) f) x

/-- Arbitrary finite-dimensional cofactor divergence, local in the potential.
There is no dimension-two restriction and no global smoothness assumption. -/
theorem cofactor_divergence_at {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (a b : ι → E)
    (hunit : IsUnit (wirtingerHessian a b f x).det) (j : ι) :
    (∑ i, dz (a i) (b i) (fun y => (wirtingerHessian a b f y).adjugate j i) x) = 0 := by
  apply cofactor_divergence_of_commuting_rows a b
  · intro i k
    exact (smoothAt_dz (smoothAt_dz hf (a k) (-b k)) (a i) (b i)).differentiableAt
      (by simp)
  · intro i r k
    exact complex_hessian_third_comm_at hf (a i) (b i) (a r) (b r) (a k) (b k)
  · exact hunit

/-- Open-set form directly usable on the ball or on a neighborhood of its closure. -/
theorem cofactor_divergence_on {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b : ι → E)
    {x : E} (hx : x ∈ U) (hunit : IsUnit (wirtingerHessian a b f x).det) (j : ι) :
    (∑ i, dz (a i) (b i) (fun y => (wirtingerHessian a b f y).adjugate j i) x) = 0 := by
  exact cofactor_divergence_at (hf.contDiffAt (hU.mem_nhds hx)) a b hunit j

#print axioms cofactor_divergence_of_commuting_rows
#print axioms cofactor_divergence_at
#print axioms cofactor_divergence_on

end KEBall
