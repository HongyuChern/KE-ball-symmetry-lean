import KEBall.DirichletAngularHessian

/-! Symmetry of third distributional derivatives in constant directions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- The third weak derivative of the potential, tested in three fixed directions. -/
noncomputable def dirichletThirdDerivativeEntry {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d e w : E n) : ℝ :=
  -dirichletHessianEntry u (dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const) e w

theorem dirichletThirdDerivativeEntry_comm₁₂ {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d e w : E n) :
    dirichletThirdDerivativeEntry u ψ d e w = dirichletThirdDerivativeEntry u ψ e d w := by
  let ψd := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
  let ψe := dirichletTestFieldDerivative ψ (fun _ => e) contDiff_const
  have he (x : E n) : fderiv ℝ (ψd : E n → ℝ) x e = fderiv ℝ (ψe : E n → ℝ) x d := by
    have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hs := (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast)
    change fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y d) x e =
      fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y e) x d
    rw [fderiv_clm_apply hd (differentiableAt_const d),
      fderiv_clm_apply hd (differentiableAt_const e)]
    simpa using hs.eq e d
  change -(-(∫ x, fderiv ℝ (ψd : E n → ℝ) x e *
      inner ℝ w ((u : DirichletBallL2Pair n).snd x) ∂ν[n])) =
    -(-(∫ x, fderiv ℝ (ψe : E n → ℝ) x d *
      inner ℝ w ((u : DirichletBallL2Pair n).snd x) ∂ν[n]))
  simp_rw [he]

theorem dirichletThirdDerivativeEntry_comm₂₃ {n : ℕ} (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d e w : E n) :
    dirichletThirdDerivativeEntry u ψ d e w = dirichletThirdDerivativeEntry u ψ d w e := by
  unfold dirichletThirdDerivativeEntry
  rw [dirichletHessianEntry_comm u _ e w]

theorem dirichletThirdDerivativeEntry_eq_integral {n : ℕ} (u : DirichletSobolev n)
    {F : E n → ℝ} (e w : E n)
    (hF : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletHessianEntry u ψ e w = ∫ x, ψ x * F x ∂ν[n])
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (d : E n) :
    dirichletThirdDerivativeEntry u ψ d e w =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * F x ∂ν[n]) := by
  unfold dirichletThirdDerivativeEntry
  rw [hF]
  rfl

end KEBall
