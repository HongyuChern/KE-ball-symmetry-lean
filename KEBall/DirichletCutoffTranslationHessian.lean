import KEBall.DirichletHessianCompactness
import KEBall.DirichletClassicalComparison

/-! The real Hessian under a cutoff translation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Matrix Metric Set
open scoped ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

private theorem realHessian_comp_at {n : ℕ}
    {u : E n → ℝ} {F : E n → E n} {x : E n}
    (hu : ContDiffAt ℝ 2 u (F x)) (hF : ContDiffAt ℝ 2 F x) (a b : E n) :
    realHessian (u ∘ F) x a b =
      realHessian u (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) +
        fderiv ℝ u (F x) (fderiv ℝ (fderiv ℝ F) x a b) := by
  have hu₁ := hu.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hF₁ := hF.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hFu : Tendsto F (𝓝 x) (𝓝 (F x)) := hF.continuousAt.tendsto
  have he : (fun y => fderiv ℝ (u ∘ F) y b) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u (F y) (fderiv ℝ F y b)) := by
    filter_upwards [hFu.eventually (hu₁.eventually (by simp)), hF₁.eventually (by simp)] with y hy hy'
    have hd := (hy.differentiableAt one_ne_zero).hasFDerivAt.comp y
      (hy'.differentiableAt one_ne_zero).hasFDerivAt
    rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  have hu' := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hF' := ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h₁ := hu'.comp x (hF₁.differentiableAt one_ne_zero).hasFDerivAt
  have h₂ := hF'.clm_apply (hasFDerivAt_const b x)
  have h := h₁.clm_apply h₂
  change HasFDerivAt (fun y => fderiv ℝ u (F y) (fderiv ℝ F y b)) _ x at h
  have hD : fderiv ℝ (fun y => fderiv ℝ (u ∘ F) y b) x a = realHessian (u ∘ F) x a b := by
    have h := ((hu.comp x hF).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [fderiv_clm_apply h (differentiableAt_const b)]
    simp [realHessian, ContinuousLinearMap.flip_apply]
  rw [← hD, he.fderiv_eq, h.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    _root_.zero_apply, map_zero, zero_add, realHessian, add_comm, Function.comp_apply]

/-- A cutoff translation has an explicit second-order error involving only
the gradient and Hessian at the translated point and derivatives of the cutoff. -/
theorem realHessian_cutoffTranslation_at {n : ℕ}
    {u χ : E n → ℝ} {x p : E n} (hχ : ContDiffAt ℝ 2 χ x)
    (hu : ContDiffAt ℝ 2 u (x + χ x • p)) (a b : E n) :
    realHessian (fun y => u (y + χ y • p)) x a b =
      realHessian u (x + χ x • p)
        (a + fderiv ℝ χ x a • p) (b + fderiv ℝ χ x b • p) +
      fderiv ℝ u (x + χ x • p) (realHessian χ x a b • p) := by
  let F (y : E n) := y + χ y • p
  let K : ℝ →L[ℝ] E n := (ContinuousLinearMap.id ℝ ℝ).smulRight p
  have hF : ContDiffAt ℝ 2 F x := contDiffAt_id.add (hχ.smul contDiffAt_const)
  have hD {y : E n} (hy : DifferentiableAt ℝ χ y) :
      fderiv ℝ F y = ContinuousLinearMap.id ℝ (E n) + K.comp (fderiv ℝ χ y) :=
    (hasFDerivAt_id y |>.add (K.hasFDerivAt.comp y hy.hasFDerivAt)).fderiv
  have he : fderiv ℝ F =ᶠ[𝓝 x] fun y => ContinuousLinearMap.id ℝ (E n) + K.comp (fderiv ℝ χ y) := by
    filter_upwards [(hχ.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by simp)] with y hy
    exact hD (hy.differentiableAt one_ne_zero)
  have hχ' := ((hχ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hK := (ContinuousLinearMap.compL ℝ (E n) ℝ (E n) K).hasFDerivAt.comp x hχ'
  have h₂ (v w : E n) : fderiv ℝ (fderiv ℝ F) x v w = realHessian χ x v w • p := by
    have hK' : HasFDerivAt (fun y => K.comp (fderiv ℝ χ y)) _ x := hK
    rw [he.fderiv_eq, (hK'.const_add (ContinuousLinearMap.id ℝ (E n))).fderiv]
    rfl
  have h₁ (v : E n) : fderiv ℝ F x v = v + fderiv ℝ χ x v • p := by
    rw [hD (hχ.differentiableAt (by norm_num))]
    rfl
  exact (realHessian_comp_at (F := F) (x := x) hu hF a b).trans (by rw [h₁, h₁, h₂])


/-- A cutoff translation has a second-order error bounded linearly by the
translation size, with a constant depending only on the first two derivative bounds. -/
theorem abs_realHessian_cutoffTranslation_sub_le {n : ℕ}
    {u χ : E n → ℝ} {x p a b : E n} (hχ : ContDiffAt ℝ 2 χ x)
    (hu : ContDiffAt ℝ 2 u (x + χ x • p))
    {B D K J : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hu₁ : ‖fderiv ℝ u (x + χ x • p)‖ ≤ B) (hu₂ : ‖realHessian u (x + χ x • p)‖ ≤ D)
    (hχ₁ : ‖fderiv ℝ χ x‖ ≤ K) (hχ₂ : ‖realHessian χ x‖ ≤ J)
    (hp : ‖p‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |realHessian (fun y => u (y + χ y • p)) x a b -
      realHessian u (x + χ x • p) a b| ≤ (D * (2 * K + K ^ 2) + B * J) * ‖p‖ := by
  let y := x + χ x • p
  let H := realHessian u y
  let A := fderiv ℝ χ x a
  let C := fderiv ℝ χ x b
  let G := realHessian χ x a b
  have hA : |A| ≤ K := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ χ x).le_opNorm a).trans ((mul_le_of_le_one_right (norm_nonneg _) ha).trans hχ₁)
  have hC : |C| ≤ K := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ χ x).le_opNorm b).trans ((mul_le_of_le_one_right (norm_nonneg _) hb).trans hχ₁)
  have hBil {T : E n →L[ℝ] E n →L[ℝ] ℝ} {k : ℝ} (hk : ‖T‖ ≤ k) (v w : E n) :
      |T v w| ≤ k * ‖v‖ * ‖w‖ := by
    rw [← Real.norm_eq_abs]
    exact ((T v).le_opNorm w).trans (mul_le_mul_of_nonneg_right
      ((T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg v))) (norm_nonneg w))
  have hE : |G| ≤ J := (hBil hχ₂ a b).trans
    ((mul_le_of_le_one_right (mul_nonneg hJ (norm_nonneg _)) hb).trans (mul_le_of_le_one_right hJ ha))
  have hPa : |H p b| ≤ D * ‖p‖ :=
    (hBil hu₂ p b).trans (mul_le_of_le_one_right (by positivity) hb)
  have hPb : |H a p| ≤ D * ‖p‖ :=
    (hBil hu₂ a p).trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hD ha) (norm_nonneg _))
  have hPP : |H p p| ≤ D * ‖p‖ :=
    (hBil hu₂ p p).trans (mul_le_of_le_one_right (by positivity) hp)
  have hG : |fderiv ℝ u y p| ≤ B * ‖p‖ := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ u y).le_opNorm p).trans (mul_le_mul_of_nonneg_right hu₁ (norm_nonneg p))
  have he : realHessian (fun y => u (y + χ y • p)) x a b - H a b =
      A * H p b + C * H a p + (A * C) * H p p + G * fderiv ℝ u y p := by
    rw [realHessian_cutoffTranslation_at hχ hu]
    simp only [H, y, A, C, G, map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  rw [he]
  have hAC : |A * C| ≤ K ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hA hC (abs_nonneg _) hK
  calc
    _ ≤ |A * H p b| + |C * H a p| + |(A * C) * H p p| + |G * fderiv ℝ u y p| :=
      (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans
        (add_le_add_left (abs_add_le _ _) _)) _)
    _ ≤ K * (D * ‖p‖) + K * (D * ‖p‖) + K ^ 2 * (D * ‖p‖) + J * (B * ‖p‖) := by
      simp only [abs_mul] at hAC ⊢
      exact add_le_add (add_le_add (add_le_add (mul_le_mul hA hPa (abs_nonneg _) hK)
        (mul_le_mul hC hPb (abs_nonneg _) hK))
        (mul_le_mul hAC hPP (abs_nonneg _) (sq_nonneg _))) (mul_le_mul hE hG (abs_nonneg _) hJ)
    _ = _ := by ring


private theorem norm_complexHessian_sub_le_of_realHessian_sub {n : ℕ}
    {u v : E n → ℝ} {x y : E n} (hu : ContDiffAt ℝ 2 u x)
    (hv : ContDiffAt ℝ 2 v y) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ a b : E n, ‖a‖ = 1 → ‖b‖ = 1 → |realHessian u x a b - realHessian v y a b| ≤ C) :
    ‖complexHessian u x - complexHessian v y‖ ≤ C := by
  apply (Matrix.norm_le_iff hC).mpr
  intro i j
  let H (a b : E n) : ℝ := realHessian u x a b - realHessian v y a b
  have hr (k : Fin n) : ‖realDirection k‖ = 1 := by simp [realDirection]
  have hi (k : Fin n) : ‖imagDirection k‖ = 1 := by simp [imagDirection]
  have h₁ := hR _ _ (hr i) (hr j)
  have h₂ := hR _ _ (hi i) (hi j)
  have h₃ := hR _ _ (hr i) (hi j)
  have h₄ := hR _ _ (hi i) (hr j)
  have he : (complexHessian u x - complexHessian v y) i j =
      (4 : ℂ)⁻¹ * ((H (realDirection i) (realDirection j) : ℂ) +
        (H (imagDirection i) (imagDirection j) : ℂ) +
        Complex.I * ((H (realDirection i) (imagDirection j) : ℂ) -
          (H (imagDirection i) (realDirection j) : ℂ))) := by
    rw [Matrix.sub_apply, complexHessian_real_entry_C2 hu, complexHessian_real_entry_C2 hv]
    simp only [H, Complex.ofReal_sub]
    ring
  rw [he, norm_mul, norm_inv, show ‖(4 : ℂ)‖ = 4 from by norm_num]
  have hTri :
      ‖(H (realDirection i) (realDirection j) : ℂ) + (H (imagDirection i) (imagDirection j) : ℂ) +
        Complex.I * ((H (realDirection i) (imagDirection j) : ℂ) -
          (H (imagDirection i) (realDirection j) : ℂ))‖ ≤ C + C + (C + C) := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_add_le _ _).trans (by simpa only [H, Complex.norm_real, Real.norm_eq_abs] using add_le_add h₁ h₂)
    · rw [norm_mul, Complex.norm_I, one_mul]
      exact (norm_sub_le _ _).trans (by simpa only [H, Complex.norm_real, Real.norm_eq_abs] using add_le_add h₃ h₄)
  exact (mul_le_mul_of_nonneg_left hTri (by norm_num)).trans_eq (by ring)

/-- The complex Hessian perturbation caused by the cutoff translation is
uniformly linear in the translation size. -/
theorem norm_complexHessian_cutoffTranslation_sub_le {n : ℕ}
    {u χ : E n → ℝ} {x p : E n} (hχ : ContDiffAt ℝ 2 χ x)
    (hu : ContDiffAt ℝ 2 u (x + χ x • p))
    {B D K J : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hu₁ : ‖fderiv ℝ u (x + χ x • p)‖ ≤ B) (hu₂ : ‖realHessian u (x + χ x • p)‖ ≤ D)
    (hχ₁ : ‖fderiv ℝ χ x‖ ≤ K) (hχ₂ : ‖realHessian χ x‖ ≤ J) (hp : ‖p‖ ≤ 1) :
    ‖complexHessian (fun y => u (y + χ y • p)) x - complexHessian u (x + χ x • p)‖ ≤
      (D * (2 * K + K ^ 2) + B * J) * ‖p‖ := by
  have hF : ContDiffAt ℝ 2 (fun y : E n => y + χ y • p) x :=
    contDiffAt_id.add (hχ.smul contDiffAt_const)
  exact norm_complexHessian_sub_le_of_realHessian_sub (hu.comp x hF) hu (by positivity)
    fun a b ha hb => abs_realHessian_cutoffTranslation_sub_le hχ hu hD hK hJ
      hu₁ hu₂ hχ₁ hχ₂ hp ha.le hb.le

end KEBall
