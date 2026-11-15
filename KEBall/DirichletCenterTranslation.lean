import KEBall.DirichletHessianPerturbation
import KEBall.DirichletCutoffTranslationHessian

/-! Uniform estimates for cutoff translations near the center of the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Matrix Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

private noncomputable def centerTranslationBump (n : ℕ) : ContDiffBump (0 : E n) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

noncomputable def dirichletCenterTranslation {n : ℕ} (p x : E n) : E n :=
  x + centerTranslationBump n x • p

theorem dirichletCenterTranslation_eq_add_of_mem_ball {n : ℕ} {p x : E n}
    (hx : x ∈ ball 0 (1 / 4)) : dirichletCenterTranslation p x = x + p := by
  rw [dirichletCenterTranslation, (centerTranslationBump n).one_of_mem_closedBall
    (ball_subset_closedBall hx), one_smul]

private theorem dirichletCenterTranslation_closed {n : ℕ} {p : E n} (hp : ‖p‖ ≤ 1 / 4) :
    MapsTo (dirichletCenterTranslation p) (closedUnitBall n) (closedUnitBall n) := by
  intro x hx
  by_cases h : ‖x‖ ≤ 1 / 2
  · apply mem_closedBall_zero_iff.mpr
    have hχ : ‖centerTranslationBump n x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg ((centerTranslationBump n).nonneg)]
      exact (centerTranslationBump n).le_one
    calc
      _ ≤ ‖x‖ + ‖centerTranslationBump n x‖ * ‖p‖ := by
        rw [← norm_smul]
        exact norm_add_le _ _
      _ ≤ 1 / 2 + 1 * (1 / 4) := add_le_add h (mul_le_mul hχ hp (norm_nonneg _) zero_le_one)
      _ ≤ 1 := by norm_num
  · have hχ : centerTranslationBump n x = 0 :=
      (centerTranslationBump n).zero_of_le_dist (by
        change (1 : ℝ) / 2 ≤ dist x 0
        exact (dist_zero_right x).symm ▸ (lt_of_not_ge h).le)
    simpa only [dirichletCenterTranslation, hχ, zero_smul, add_zero] using hx

private theorem dirichletCenterTranslation_ball {n : ℕ} {p : E n} (hp : ‖p‖ ≤ 1 / 4) :
    MapsTo (dirichletCenterTranslation p) (unitBall n) (unitBall n) := by
  intro x hx
  by_cases h : ‖x‖ ≤ 1 / 2
  · apply mem_ball_zero_iff.mpr
    have hχ : ‖centerTranslationBump n x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg ((centerTranslationBump n).nonneg)]
      exact (centerTranslationBump n).le_one
    calc
      _ ≤ ‖x‖ + ‖centerTranslationBump n x‖ * ‖p‖ := by
        rw [← norm_smul]
        exact norm_add_le _ _
      _ ≤ 1 / 2 + 1 * (1 / 4) := add_le_add h (mul_le_mul hχ hp (norm_nonneg _) zero_le_one)
      _ < 1 := by norm_num
  · have hχ : centerTranslationBump n x = 0 :=
      (centerTranslationBump n).zero_of_le_dist (by
        change (1 : ℝ) / 2 ≤ dist x 0
        exact (dist_zero_right x).symm ▸ (lt_of_not_ge h).le)
    simpa only [dirichletCenterTranslation, hχ, zero_smul, add_zero] using hx

private theorem dirichletCenterTranslation_sphere {n : ℕ} (p : E n) {x : E n}
    (hx : x ∈ unitSphere n) : dirichletCenterTranslation p x = x := by
  have hχ : centerTranslationBump n x = 0 :=
    (centerTranslationBump n).zero_of_le_dist (by
      change (1 : ℝ) / 2 ≤ dist x 0
      rw [dist_zero_right, mem_sphere_zero_iff_norm.mp hx]
      norm_num)
  simp only [dirichletCenterTranslation, hχ, zero_smul, add_zero]

private theorem contDiff_dirichletCenterTranslation {n : ℕ} (p : E n) :
    ContDiff ℝ ∞ (dirichletCenterTranslation p) :=
  contDiff_id.add ((centerTranslationBump n).contDiff.smul contDiff_const)

private theorem SmoothNear.comp_centerTranslation {n : ℕ} {u : E n → ℝ}
    (hu : SmoothNear (closedUnitBall n) u) {p : E n} (hp : ‖p‖ ≤ 1 / 4) :
    SmoothNear (closedUnitBall n) (u ∘ dirichletCenterTranslation p) := by
  obtain ⟨U, hU, hSub, huU⟩ := hu
  let F := dirichletCenterTranslation p
  have hF := contDiff_dirichletCenterTranslation p
  exact ⟨F ⁻¹' U, hU.preimage hF.continuous,
    fun x hx => hSub (dirichletCenterTranslation_closed hp hx),
    huU.comp hF.contDiffOn (fun _ hx => hx)⟩

private theorem exists_centerTranslationBump_derivative_bounds {n : ℕ} :
    ∃ K ≥ (0 : ℝ), ∃ J ≥ (0 : ℝ), ∀ x ∈ closedUnitBall n,
      ‖fderiv ℝ (centerTranslationBump n : E n → ℝ) x‖ ≤ K ∧
      ‖realHessian (centerTranslationBump n : E n → ℝ) x‖ ≤ J := by
  have hχ : ContDiff ℝ ∞ (centerTranslationBump n : E n → ℝ) := (centerTranslationBump n).contDiff
  have hF := (contDiff_infty_iff_fderiv.mp hχ).2
  have hH := hF.continuous_fderiv (by simp)
  have hC := isCompact_closedBall (0 : E n) 1
  obtain ⟨K, hK⟩ := hC.exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨J, hJ⟩ := hC.exists_bound_of_continuousOn hH.continuousOn
  exact ⟨max K 0, le_max_right _ _, max J 0, le_max_right _ _,
    fun x hx => ⟨(hK x hx).trans (le_max_left _ _), (hJ x hx).trans (le_max_left _ _)⟩⟩


/-- Small cutoff translations remain uniformly elliptic and their prescribed
density differs from the original density by at most a constant times the shift. -/
theorem exists_centerTranslation_density_stability {n : ℕ}
    {d b D B L : ℝ} (hd : 0 < d) (hD : 0 < D) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ ε > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ M > (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, d ≤ f x ∧ f x ≤ b) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ u x‖ ≤ B) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ‖realHessian u x‖ ≤ D) →
      ∀ p : E n, ‖p‖ < ε →
      let v := u ∘ dirichletCenterTranslation p
      let g (x : E n) := (complexHessian v x).det.re
      SmoothNear (closedUnitBall n) v ∧ SmoothNear (closedUnitBall n) g ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      (∀ x ∈ unitBall n, d / 2 ≤ g x ∧ g x ≤ b + C) ∧
      (∀ x ∈ unitBall n, |g x - f x| ≤ C * ‖p‖) ∧
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian v x w w| ≤ M) := by
  obtain ⟨K, hK, J, hJ, hχBound⟩ := exists_centerTranslationBump_derivative_bounds (n := n)
  let E₀ := D * (2 * K + K ^ 2) + B * J
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  obtain ⟨δ, hδ, hPD⟩ := exists_posDef_det_re_of_norm_sub_lt (n := n) (D := D) hd
  obtain ⟨A, hA, hDet⟩ := exists_abs_det_re_sub_le_mul_norm_sub (n := n) (D + E₀)
  let ε : ℝ := min (1 / 4) (δ / (E₀ + 1))
  let C : ℝ := A * E₀ + L
  let M : ℝ := D + E₀
  refine ⟨ε, lt_min (by norm_num) (by positivity), C, by dsimp [C]; positivity,
    M, by dsimp [M]; positivity, ?_⟩
  intro u f hu hf hu0 huP huEq hDen hGrad hGradF hHess p hp
  let χ := centerTranslationBump n
  let F := dirichletCenterTranslation p
  let v := u ∘ F
  let g (x : E n) := (complexHessian v x).det.re
  have hp' : ‖p‖ ≤ 1 / 4 := hp.le.trans (min_le_left _ _)
  have hp₁ : ‖p‖ ≤ 1 := hp'.trans (by norm_num)
  have hFC := dirichletCenterTranslation_closed hp'
  have hFB := dirichletCenterTranslation_ball hp'
  have hv : SmoothNear (closedUnitBall n) v := hu.comp_centerTranslation hp'
  have hg : SmoothNear (closedUnitBall n) g := by
    obtain ⟨U, hU, hSub, hvU⟩ := hv
    exact ⟨U, hU, hSub, Complex.reCLM.contDiff.comp_contDiffOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU hvU))⟩
  have hχ (x : E n) : ContDiffAt ℝ 2 (χ : E n → ℝ) x := χ.contDiff.contDiffAt
  have huAt (x : E n) (hx : x ∈ closedUnitBall n) : ContDiffAt ℝ 2 u (F x) :=
    (hu.contDiffAt (hFC hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hH (x : E n) (hx : x ∈ closedUnitBall n) :
      ‖complexHessian v x - complexHessian u (F x)‖ ≤ E₀ * ‖p‖ :=
    norm_complexHessian_cutoffTranslation_sub_le (hχ x) (huAt x hx)
      hB hD.le hK hJ (hGrad (F x) (hFC hx)) (hHess (F x) (hFC hx))
      (hχBound x hx).1 (hχBound x hx).2 hp₁
  have hBase (x : E n) (hx : x ∈ closedUnitBall n) : ‖complexHessian u (F x)‖ ≤ D := by
    apply norm_complexHessian_le_of_unit_bound (hu.contDiffAt (hFC hx)) hD.le
    intro w hw
    rw [← Real.norm_eq_abs]
    exact ((realHessian u (F x) w).le_opNorm w).trans (by
      rw [hw, mul_one]
      exact ((realHessian u (F x)).le_opNorm w).trans (by rw [hw, mul_one]; exact hHess (F x) (hFC hx)))
  have hPert (x : E n) (hx : x ∈ closedUnitBall n) : ‖complexHessian v x‖ ≤ M := by
    have hTri := norm_add_le (complexHessian v x - complexHessian u (F x)) (complexHessian u (F x))
    rw [sub_add_cancel] at hTri
    exact hTri.trans ((add_le_add ((hH x hx).trans (mul_le_of_le_one_right hE₀ hp₁))
      (hBase x hx)).trans_eq (by dsimp [M]; ring))
  have hPD' (x : E n) (hx : x ∈ unitBall n) : (complexHessian v x).PosDef ∧ d / 2 < g x := by
    have hx' := ball_subset_closedBall hx
    have hA' : d ≤ (complexHessian u (F x)).det.re := (hDen (F x) (hFB hx)).1.trans_eq
      (huEq (F x) (hFB hx)).symm
    have hδ' : ‖p‖ * (E₀ + 1) < δ := (lt_div_iff₀ (by positivity : 0 < E₀ + 1)).mp
      (hp.trans_le (min_le_right _ _))
    have hSmall : E₀ * ‖p‖ < δ := by linarith only [hδ', norm_nonneg p]
    exact hPD _ _ (huP (F x) (hFB hx)).posSemidef (hBase x hx') hA'
      (complexHessian_isHermitian_of_C2 ((hv.contDiffAt hx').of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))) ((hH x hx').trans_lt hSmall)
  have hDiff (x : E n) (hx : x ∈ unitBall n) : |g x - f x| ≤ C * ‖p‖ := by
    have hx' := ball_subset_closedBall hx
    have h₁ := hDet (complexHessian u (F x)) (complexHessian v x)
      ((hBase x hx').trans (le_add_of_nonneg_right hE₀)) (hPert x hx')
    change |g x - (complexHessian u (F x)).det.re| ≤
      A * ‖complexHessian v x - complexHessian u (F x)‖ at h₁
    rw [huEq (F x) (hFB hx)] at h₁
    have h₂ := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun y hy => (hf.contDiffAt hy).differentiableAt (by simp)) hGradF
      (convex_closedBall (0 : E n) 1) hx' (hFC hx')
    have hχN : ‖χ x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg χ.nonneg]
      exact χ.le_one
    have hF : ‖F x - x‖ ≤ ‖p‖ := by
      change ‖(x + χ x • p) - x‖ ≤ _
      rw [add_sub_cancel_left, norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) hχN
    rw [Real.norm_eq_abs] at h₂
    exact (abs_sub_le _ _ _).trans ((add_le_add
      (h₁.trans (mul_le_mul_of_nonneg_left (hH x hx') hA))
      (h₂.trans (mul_le_mul_of_nonneg_left hF hL))).trans_eq (by dsimp [C]; ring))
  refine ⟨hv, hg, fun x hx => by change u (dirichletCenterTranslation p x) = 0; rw [dirichletCenterTranslation_sphere p hx]; exact hu0 x hx,
    fun x hx => (hPD' x hx).1, fun x hx => ⟨(hPD' x hx).2.le, ?_⟩, hDiff, ?_⟩
  · have h := (le_abs_self (g x - f x)).trans ((hDiff x hx).trans
      (mul_le_of_le_one_right (by dsimp [C]; positivity) hp₁))
    linarith only [h, (hDen x hx).2]
  · intro x hx w hw
    have h := abs_realHessian_cutoffTranslation_sub_le (hχ x) (huAt x hx)
      hD.le hK hJ (hGrad (F x) (hFC hx)) (hHess (F x) (hFC hx))
      (hχBound x hx).1 (hχBound x hx).2 hp₁ hw.le hw.le
    have hA' : |realHessian u (F x) w w| ≤ D := by
      rw [← Real.norm_eq_abs]
      exact ((realHessian u (F x) w).le_opNorm w).trans (by
        rw [hw, mul_one]
        exact ((realHessian u (F x)).le_opNorm w).trans (by rw [hw, mul_one]; exact hHess (F x) (hFC hx)))
    calc
      |realHessian v x w w| = |(realHessian v x w w - realHessian u (F x) w w) +
          realHessian u (F x) w w| := by rw [sub_add_cancel]
      _ ≤ E₀ * ‖p‖ + D := (abs_add_le _ _).trans (add_le_add h hA')
      _ ≤ M := (add_le_add_left (mul_le_of_le_one_right hE₀ hp₁) D).trans_eq (by dsimp [M]; ring)

end KEBall
