import KEBall.GradientBridge

/-! The actual complex structure and the real second derivative underlying
the complex Hessian. These identities fix the coordinate normalization. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped ContDiff BigOperators Topology

namespace KEBall
open KEBallProbe

@[simp] theorem J_realIndex {n : ℕ} (x : E n) (j : Fin n) :
    J x (realIndex j) = -x (imagIndex j) := by
  simp [J, realDirection, imagDirection, Pi.single_apply]

@[simp] theorem J_imagIndex {n : ℕ} (x : E n) (j : Fin n) :
    J x (imagIndex j) = x (realIndex j) := by
  simp [J, realDirection, imagDirection, Pi.single_apply]

noncomputable def JCLM (n : ℕ) : E n →L[ℝ] E n :=
  ∑ i : Fin n, (-(EuclideanSpace.proj (imagIndex i)).smulRight (realDirection i) +
    (EuclideanSpace.proj (realIndex i)).smulRight (imagDirection i))

@[simp] theorem JCLM_apply {n : ℕ} (x : E n) : JCLM n x = J x := by
  simp [JCLM, J, neg_smul]

theorem complexCoord_J {n : ℕ} (x : E n) (i : Fin n) :
    complexCoord (J x) i = Complex.I * complexCoord x i := by
  simp only [complexCoord, J_realIndex, J_imagIndex]
  push_cast
  ring_nf
  simp

theorem complexCoord_injective {n : ℕ} : Function.Injective (complexCoord (n := n)) := by
  intro v w hvw
  apply eq_of_sub_eq_zero
  apply complexCoord_eq_zero_iff.mp
  funext i
  change complexCoordCLM i (v - w) = 0
  rw [map_sub]
  change complexCoord v i - complexCoord w i = 0
  rw [congrFun hvw i, sub_self]

@[simp] theorem J_sq {n : ℕ} (x : E n) : J (J x) = -x := by
  apply complexCoord_injective
  funext i
  rw [complexCoord_J, complexCoord_J, complexCoord_neg, ← mul_assoc,
    Complex.I_mul_I, neg_one_mul]

theorem norm_J {n : ℕ} (x : E n) : ‖J x‖ = ‖x‖ := by
  have h : ‖J x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_interleaved, norm_sq_interleaved]
    simp only [J_realIndex, J_imagIndex, neg_sq, add_comm]
  nlinarith [norm_nonneg (J x), norm_nonneg x]

noncomputable def JLinearIsometry (n : ℕ) : E n →ₗᵢ[ℝ] E n where
  toLinearMap := (JCLM n).toLinearMap
  norm_map' x := by simpa using norm_J x

theorem inner_J_J {n : ℕ} (x y : E n) : inner ℝ (J x) (J y) = inner ℝ x y := by
  simpa only [JLinearIsometry, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe,
    JCLM_apply] using (JLinearIsometry n).inner_map_map x y

theorem inner_J_skew {n : ℕ} (x y : E n) : inner ℝ (J x) y = -inner ℝ x (J y) := by
  have h := inner_J_J x (J y)
  rw [J_sq, inner_neg_right] at h
  linarith

noncomputable def realHessian {n : ℕ} (u : E n → ℝ) (x : E n) :
    E n →L[ℝ] E n →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ u) x

theorem realHessian_symm {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    realHessian u x v w = realHessian u x w v :=
  (hu.isSymmSndFDerivAt (by simp; norm_cast)).eq v w

theorem rd_rd_ofReal {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (a b : E n) :
    rd a (rd b (fun y => (u y : ℂ))) x = (realHessian u x a b : ℝ) := by
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y := by
    filter_upwards [(hu.of_le (m := 1) (by simp)).eventually (by simp)] with y hy
    exact hy.differentiableAt one_ne_zero
  have heq : rd b (fun y => (u y : ℂ)) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ u y b : ℂ)) := by
    filter_upwards [hnear] with y hy
    exact rd_ofReal hy b
  change fderiv ℝ (rd b (fun y => (u y : ℂ))) x a = _
  rw [heq.fderiv_eq]
  have hdf := (hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hr := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const b x)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hr
  change HasFDerivAt (fun y => (fderiv ℝ u y b : ℂ)) _ x at hc
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, zero_apply, map_zero,
    zero_add, Complex.ofRealCLM_apply]
  rfl

theorem complexHessian_real_entry {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    complexHessian u x i j = (4 : ℂ)⁻¹ *
      ((realHessian u x (realDirection i) (realDirection j) : ℝ) +
       (realHessian u x (imagDirection i) (imagDirection j) : ℝ) +
       Complex.I * ((realHessian u x (realDirection i) (imagDirection j) : ℝ) -
         (realHessian u x (imagDirection i) (realDirection j) : ℝ))) := by
  have hc : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  change dz (realDirection i) (imagDirection i)
    (dz (realDirection j) (-imagDirection j) (fun y => (u y : ℂ))) x = _
  rw [dz, rd_dz_at hc, rd_dz_at hc]
  simp only [rd_rd_ofReal hu, map_neg]
  push_cast
  ring_nf
  simp
  ring

theorem realLinear_interleaved {n : ℕ} (L : E n →L[ℝ] ℝ) (v : E n) :
    L v = ∑ i : Fin n, (v (realIndex i) * L (realDirection i) +
      v (imagIndex i) * L (imagDirection i)) := by
  nth_rw 1 [← interleaved_decomposition v]
  simp only [map_sum, map_add, map_smul, smul_eq_mul]

theorem realBilinear_left_interleaved {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ)
    (v w : E n) :
    B v w = ∑ i : Fin n, (v (realIndex i) * B (realDirection i) w +
      v (imagIndex i) * B (imagDirection i) w) := by
  nth_rw 1 [← interleaved_decomposition v]
  simp only [map_sum, map_add, map_smul, _root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]

theorem realBilinear_interleaved {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ)
    (v w : E n) : B v w =
    ∑ i : Fin n, ∑ j : Fin n,
      (v (realIndex i) *
        (w (realIndex j) * B (realDirection i) (realDirection j) +
          w (imagIndex j) * B (realDirection i) (imagDirection j)) +
       v (imagIndex i) *
        (w (realIndex j) * B (imagDirection i) (realDirection j) +
          w (imagIndex j) * B (imagDirection i) (imagDirection j))) := by
  rw [realBilinear_left_interleaved]
  apply Finset.sum_congr rfl
  intro i _
  rw [realLinear_interleaved, realLinear_interleaved,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The solution's real metric is exactly the `J`-invariant half of the
ordinary real Hessian, with the convention from the frozen manuscript. -/
theorem realMetricForm_eq_average_hessian {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : E n) :
    realMetricForm u x v w =
      (realHessian u x v w + realHessian u x (J v) (J w)) / 2 := by
  unfold realMetricForm
  simp only [complexHessian_real_entry hu, Complex.re_sum, Finset.mul_sum]
  rw [realBilinear_interleaved, realBilinear_interleaved]
  simp only [J_realIndex, J_imagIndex, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [complexCoord, Complex.mul_re, Complex.mul_im]
  ring

end KEBall
