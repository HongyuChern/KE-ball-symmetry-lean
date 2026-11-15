import KEBall.DirichletDiscreteCofactorEquation
import KEBall.DirichletAngularFlow

/-!
# Isometric pullback of real Hessians

Pullback acts in both vector arguments. Its deviation from the identity
has operator norm at most twice the deviation of the underlying rotation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Metric Set
open scoped ContDiff

namespace KEBall

noncomputable def dirichletBilinearPullback {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    E n →L[ℝ] E n →L[ℝ] ℝ :=
  H.bilinearComp R.toContinuousLinearEquiv.toContinuousLinearMap
    R.toContinuousLinearEquiv.toContinuousLinearMap

theorem dirichletBilinearPullback_apply {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (H : E n →L[ℝ] E n →L[ℝ] ℝ) (a b : E n) :
    dirichletBilinearPullback R H a b = H (R a) (R b) := rfl

private theorem norm_pullback_rotation_le_one {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    ‖R.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖R x‖ ≤ 1 * ‖x‖
  rw [R.norm_map, one_mul]

theorem norm_dirichletBilinearPullback_le {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ‖dirichletBilinearPullback R H‖ ≤ ‖H‖ := by
  let L := R.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := norm_pullback_rotation_le_one R
  change ‖((H.comp L).flip.comp L).flip‖ ≤ ‖H‖
  rw [ContinuousLinearMap.opNorm_flip]
  calc
    ‖(H.comp L).flip.comp L‖ ≤ ‖(H.comp L).flip‖ * ‖L‖ :=
      (H.comp L).flip.opNorm_comp_le L
    _ ≤ ‖(H.comp L).flip‖ := mul_le_of_le_one_right (norm_nonneg _) hL
    _ = ‖H.comp L‖ := ContinuousLinearMap.opNorm_flip _
    _ ≤ ‖H‖ * ‖L‖ := H.opNorm_comp_le L
    _ ≤ ‖H‖ := mul_le_of_le_one_right (norm_nonneg _) hL

theorem dirichletBilinearPullback_symm {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    dirichletBilinearPullback R.symm (dirichletBilinearPullback R H) = H := by
  ext a b
  change H (R (R.symm a)) (R (R.symm b)) = H a b
  rw [R.apply_symm_apply, R.apply_symm_apply]

theorem norm_dirichletBilinearPullback {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ‖dirichletBilinearPullback R H‖ = ‖H‖ := by
  apply le_antisymm (norm_dirichletBilinearPullback_le R H)
  have h := norm_dirichletBilinearPullback_le R.symm (dirichletBilinearPullback R H)
  rwa [dirichletBilinearPullback_symm] at h

noncomputable def dirichletBilinearPullbackLinearMap {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] (E n →L[ℝ] E n →L[ℝ] ℝ) where
  toFun := dirichletBilinearPullback R
  map_add' H K := by ext a b; rfl
  map_smul' c H := by ext a b; rfl

noncomputable def dirichletBilinearPullbackCLM {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) :
    (E n →L[ℝ] E n →L[ℝ] ℝ) →L[ℝ] (E n →L[ℝ] E n →L[ℝ] ℝ) :=
  (dirichletBilinearPullbackLinearMap R).toContinuousLinearMap

theorem dirichletBilinearPullbackCLM_apply {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    dirichletBilinearPullbackCLM R H = dirichletBilinearPullback R H := rfl

theorem norm_dirichletBilinearPullbackCLM_le_one {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) :
    ‖dirichletBilinearPullbackCLM R‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro H
  simpa only [dirichletBilinearPullbackCLM_apply, one_mul] using
    norm_dirichletBilinearPullback_le R H

theorem norm_dirichletBilinearPullback_sub_le {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ‖dirichletBilinearPullback R H - H‖ ≤
      2 * ‖R.toContinuousLinearEquiv.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ (E n)‖ * ‖H‖ := by
  let L := R.toContinuousLinearEquiv.toContinuousLinearMap
  let D := L - ContinuousLinearMap.id ℝ (E n)
  change ‖dirichletBilinearPullback R H - H‖ ≤ 2 * ‖D‖ * ‖H‖
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  have hSplit : (dirichletBilinearPullback R H - H) a b =
      H (D a) (R b) + H a (D b) := by
    change H (R a) (R b) - H a b =
      H (L a - a) (R b) + H a (L b - b)
    simp only [map_sub, _root_.sub_apply]
    change H (R a) (R b) - H a b =
      (H (R a) (R b) - H a (R b)) + (H a (R b) - H a b)
    ring
  rw [hSplit]
  calc
    ‖H (D a) (R b) + H a (D b)‖ ≤ ‖H (D a) (R b)‖ + ‖H a (D b)‖ := norm_add_le _ _
    _ ≤ ‖H‖ * ‖D a‖ * ‖R b‖ + ‖H‖ * ‖a‖ * ‖D b‖ :=
      add_le_add (H.le_opNorm₂ _ _) (H.le_opNorm₂ _ _)
    _ ≤ ‖H‖ * (‖D‖ * ‖a‖) * ‖b‖ + ‖H‖ * ‖a‖ * (‖D‖ * ‖b‖) := by
      rw [R.norm_map]
      gcongr
      · exact D.le_opNorm a
      · exact D.le_opNorm b
    _ = (2 * ‖D‖ * ‖H‖ * ‖a‖) * ‖b‖ := by ring

theorem norm_dirichletBilinearPullbackCLM_sub_id_le {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) :
    ‖dirichletBilinearPullbackCLM R -
      ContinuousLinearMap.id ℝ (E n →L[ℝ] E n →L[ℝ] ℝ)‖ ≤
      2 * ‖R.toContinuousLinearEquiv.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ (E n)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro H
  exact norm_dirichletBilinearPullback_sub_le R H

theorem norm_dirichletBilinearPullbackCLM_flow_sub_id_le {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) (t : ℝ) :
    ‖dirichletBilinearPullbackCLM (orthogonalFlow S hS t) -
      ContinuousLinearMap.id ℝ (E n →L[ℝ] E n →L[ℝ] ℝ)‖ ≤
      2 * ‖S‖ * |t| := by
  exact (norm_dirichletBilinearPullbackCLM_sub_id_le (orthogonalFlow S hS t)).trans
    ((mul_le_mul_of_nonneg_left (norm_orthogonalFlow_sub_id_le S hS t) (by norm_num)).trans_eq
      (mul_assoc _ _ _).symm)

theorem norm_dirichletBilinearPullbackCLM_normalized_increment_le {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) {t : ℝ} (ht : t ≠ 0) :
    ‖t⁻¹ • (dirichletBilinearPullbackCLM (orthogonalFlow S hS t) -
      ContinuousLinearMap.id ℝ (E n →L[ℝ] E n →L[ℝ] ℝ))‖ ≤ 2 * ‖S‖ := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    |t|⁻¹ * ‖dirichletBilinearPullbackCLM (orthogonalFlow S hS t) -
        ContinuousLinearMap.id ℝ (E n →L[ℝ] E n →L[ℝ] ℝ)‖
      ≤ |t|⁻¹ * (2 * ‖S‖ * |t|) :=
        mul_le_mul_of_nonneg_left (norm_dirichletBilinearPullbackCLM_flow_sub_id_le S hS t)
          (inv_nonneg.mpr (abs_nonneg t))
    _ = 2 * ‖S‖ := by field_simp

theorem realHessian_comp_eq_dirichletBilinearPullback {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (u : E n → ℝ) (x : E n) :
    realHessian (u ∘ R) x = dirichletBilinearPullback R (realHessian u (R x)) := by
  ext a b
  exact realHessian_comp_linearIsometryEquiv u R x a b

theorem norm_realHessian_comp_orthogonal {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) (u : E n → ℝ) (x : E n) :
    ‖realHessian (u ∘ R) x‖ = ‖realHessian u (R x)‖ := by
  rw [realHessian_comp_eq_dirichletBilinearPullback, norm_dirichletBilinearPullback]

end KEBall
