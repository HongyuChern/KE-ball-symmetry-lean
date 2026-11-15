import KEBall.DirichletSchauderEstimateMajorant
import DifferentialGeometry.Analysis.Schauder.Elliptic.VariableCoefficient.BallInterior

/-!
# The imported interior estimate with a uniform right hand side

All quantities on the right depend only on uniform coefficient, source,
value and first-jet bounds.  Initial Hessian bounds are used only to apply
the estimate, and do not occur in the resulting majorant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Matrix
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped BigOperators NNReal

namespace KEBall

theorem dirichletSchauderConst_mono_source {n : ℕ}
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hA : A.PosDef)
    {α K K' B B' : ℝ≥0} (hα : α < 1) (hK : K ≤ K') (hB : B ≤ B')
    (u : BoundedContinuousFunction (E n) ℝ) :
    spdLaplacianSchauderConst A hA α K B u ≤ spdLaplacianSchauderConst A hA α K' B' u := by
  obtain ⟨k, rfl⟩ := exists_add_of_le hK
  obtain ⟨b, rfl⟩ := exists_add_of_le hB
  rw [spdLaplacianSchauderConst_add_source hα A hA K k B b u]
  exact le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ _)

theorem dirichlet_nnreal_div_one_sub_le {a b δ : ℝ≥0}
    (hab : a ≤ b) (hδ : δ ≤ 1 / 2) : a / (1 - δ) ≤ 2 * b := by
  have hδOne : δ ≤ 1 := hδ.trans (by norm_num)
  have hδReal : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ
  have habReal : (a : ℝ) ≤ b := hab
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_sub hδOne,
    NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat]
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1 - (δ : ℝ))).mpr
  nlinarith [b.coe_nonneg]

noncomputable def dirichletUnitBallSourceSupMajorant (n : ℕ) (M F U D : ℝ≥0) : ℝ≥0 :=
  ‖ballCutoffBoundedContinuousFunction (0 : E n)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)‖₊ * F +
  matrixCutoffCommutatorSupConst (fun _ _ : Fin (2 * n) => M)
    ‖ballCutoffFDerivBoundedContinuousFunction (0 : E n)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)‖₊
    D (Real.toNNReal (ballCutoffFDeriv2Bound (3 / 4) 1)) U

noncomputable def dirichletUnitBallSourceHolderMajorant (n : ℕ)
    (M Ka Kf Kdu Ku F U D : ℝ≥0) : ℝ≥0 :=
  (‖ballCutoffBoundedContinuousFunction (0 : E n)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)‖₊ * Kf +
    F * ballCutoffHolderConst (3 / 4) 1) +
  matrixCutoffCommutatorHolderConst (fun _ _ : Fin (2 * n) => M) (fun _ _ => Ka)
    (ballCutoffFDerivHolderConst (3 / 4) 1) Kdu
    (ballCutoffFDeriv2HolderConst (0 : E n)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)) Ku
    ‖ballCutoffFDerivBoundedContinuousFunction (0 : E n)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)‖₊
    D (Real.toNNReal (ballCutoffFDeriv2Bound (3 / 4) 1)) U

theorem dirichlet_unitBall_source_sup_le {n : ℕ}
    (A : Fin (2 * n) → Fin (2 * n) → ℝ≥0)
    (f u : BoundedContinuousFunction (E n) ℝ)
    (du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    {M F U D : ℝ≥0} (hA : ∀ i j, A i j ≤ M) (hf : ‖f‖₊ ≤ F)
    (hu : ‖u‖₊ ≤ U) (hdu : ‖du‖₊ ≤ D) :
    variableBallCutoffSourceSupConst (0 : E n)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1) A f u du ≤
      dirichletUnitBallSourceSupMajorant n M F U D := by
  unfold variableBallCutoffSourceSupConst variableCutoffSourceSupConst cutoffValueSupConst
    dirichletUnitBallSourceSupMajorant matrixCutoffCommutatorSupConst
  gcongr <;> apply hA

theorem dirichlet_unitBall_source_holder_le {n : ℕ}
    (A : Fin (2 * n) → Fin (2 * n) → ℝ≥0)
    (f u : BoundedContinuousFunction (E n) ℝ)
    (du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (Ka Kf Kdu Ku : ℝ≥0) {M F U D : ℝ≥0}
    (hA : ∀ i j, A i j ≤ M) (hf : ‖f‖₊ ≤ F) (hu : ‖u‖₊ ≤ U) (hdu : ‖du‖₊ ≤ D) :
    variableBallCutoffSourceHolderConst (0 : E n)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
      A (fun _ _ => Ka) Kf Kdu
      (ballCutoffFDeriv2HolderConst (0 : E n)
        (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)) Ku f u du ≤
      dirichletUnitBallSourceHolderMajorant n M Ka Kf Kdu Ku F U D := by
  unfold variableBallCutoffSourceHolderConst variableCutoffSourceHolderConst cutoffValueHolderConst
    dirichletUnitBallSourceHolderMajorant matrixCutoffCommutatorHolderConst
  gcongr <;> apply hA


theorem dirichlet_unitBall_interior_schauder_uniform_estimate {n : ℕ} (hn : 0 < n)
    (a : Fin (2 * n) → Fin (2 * n) → BoundedContinuousFunction (E n) ℝ)
    (hA : Matrix.PosDef (fun i j => a i j 0))
    (f u : BoundedContinuousFunction (E n) ℝ)
    (du : BoundedContinuousFunction (E n) (E n →L[ℝ] ℝ))
    (d2u : BoundedContinuousFunction (E n) (E n →L[ℝ] E n →L[ℝ] ℝ))
    {α L R M Ka Kf Kdu Ku Kd2u F U D : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hL : ‖(spdSqrtEquiv (fun i j => a i j 0) hA : E n →L[ℝ] E n)‖₊ ≤ L)
    (hR : ‖((spdSqrtEquiv (fun i j => a i j 0) hA).symm : E n →L[ℝ] E n)‖₊ ≤ R)
    (hu : ∀ x, HasFDerivAt (u : E n → ℝ) (du x) x)
    (hdu : ∀ x, HasFDerivAt (du : E n → E n →L[ℝ] ℝ) (d2u x) x)
    (hsource : ∀ x ∈ Metric.ball (0 : E n) 1, variableMatrixLap a d2u x = f x)
    (ha : ∀ i j, HolderWith Ka α (a i j : E n → ℝ))
    (homega : ∀ i j x, ‖a i j 0 - a i j x‖ ≤ Ka)
    (hM : ∀ i j, ‖a i j‖₊ ≤ M)
    (hfHolder : HolderWith Kf α (f : E n → ℝ))
    (hduHolder : HolderWith Kdu α (du : E n → E n →L[ℝ] ℝ))
    (huHolder : HolderWith Ku α (u : E n → ℝ))
    (hd2uHolder : HolderWith Kd2u α (d2u : E n → E n →L[ℝ] E n →L[ℝ] ℝ))
    (hfNorm : ‖f‖₊ ≤ F) (huNorm : ‖u‖₊ ≤ U) (hduNorm : ‖du‖₊ ≤ D)
    (hsmall : spdLaplacianSchauderDefectConst (fun i j => a i j 0) hA α
      (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), (Ka + Ka))
      (∑ _i : Fin (2 * n), ∑ _j : Fin (2 * n), Ka) ≤ 1 / 2) :
    eContDiffHolderGaugeOn 2 α (Metric.closedBall (0 : E n) (1 / 2)) (u : E n → ℝ) ≤
      (2 * dirichletSchauderEstimateMajorant n α L R
        (dirichletUnitBallSourceHolderMajorant n M Ka Kf Kdu Ku F U D)
        (dirichletUnitBallSourceSupMajorant n M F U D)
        (‖ballCutoffBoundedContinuousFunction (0 : E n)
          (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)‖₊ * U) : ℝ≥0) := by
  letI : NeZero (2 * n) := ⟨by omega⟩
  have hEstimate := variable_coefficient_ball_interior_schauder_estimate_of_global_small_coefficient_oscillation
    (Md2u := ‖d2u‖₊) (center := (0 : E n)) (rho := (1 / 2 : ℝ)) (r := (3 / 4 : ℝ)) (R := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hα hα1 a 0 hA f u du d2u hu hdu hsource
    (fun _ _ => Ka) (fun _ _ => Ka) ha homega hfHolder hduHolder huHolder hd2uHolder
    (fun x => d2u.norm_coe_le_norm x) (hsmall.trans_lt (by norm_num))
  let χ := ballCutoffBoundedContinuousFunction (0 : E n)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
  have hCut : ‖cutoffValue χ u‖₊ ≤ ‖χ‖₊ * U := by
    have h : ‖cutoffValue χ u‖₊ ≤ ‖χ‖₊ * ‖u‖₊ := norm_cutoffValue_le χ u
    exact h.trans (mul_le_mul le_rfl huNorm (bot_le : (0 : ℝ≥0) ≤ _) (bot_le : (0 : ℝ≥0) ≤ _))
  have hKS := dirichlet_unitBall_source_holder_le (fun i j => ‖a i j‖₊)
    f u du Ka Kf Kdu Ku hM hfNorm huNorm hduNorm
  have hBS := dirichlet_unitBall_source_sup_le (fun i j => ‖a i j‖₊)
    f u du hM hfNorm huNorm hduNorm
  have hNum := (dirichletSchauderConst_mono_source (fun i j => a i j 0) hA hα1 hKS hBS
    (cutoffValue χ u)).trans
      (dirichletSchauderConst_le_majorant (fun i j => a i j 0) hA hα1 hL hR _ _
        (cutoffValue χ u) hCut)
  have hC := dirichlet_nnreal_div_one_sub_le hNum hsmall
  apply hEstimate.trans
  exact_mod_cast hC

end KEBall
