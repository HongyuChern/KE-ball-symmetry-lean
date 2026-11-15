import KEBall.DirichletSobolevRotations
import KEBall.DirichletWeakGradient

/-! The weak Dirichlet equation under orthogonal changes of variables. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set

namespace KEBall

/-- The weak equation on the Dirichlet function–gradient graph. -/
def IsDirichletWeakSolution {n : ℕ} (A : E n → E n →L[ℝ] E n)
    (g : DirichletBallL2 n ℝ) (u : DirichletSobolev n) : Prop :=
  ∀ w : DirichletSobolev n,
    (∫ x in unitBall n, inner ℝ (A x ((u : DirichletBallL2Pair n).snd x))
      ((w : DirichletBallL2Pair n).snd x) ∂volume0 n) =
    ∫ x in unitBall n, g x * ((w : DirichletBallL2Pair n).fst x) ∂volume0 n

/-- The coefficient field transformed by orthogonal pullback. -/
noncomputable def orthogonalPullbackDirichletField {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    (A : E n → E n →L[ℝ] E n) (x : E n) : E n →L[ℝ] E n :=
  R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((A (R x)).comp R.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Orthogonal pullback transports the actual weak equation, including
the coefficient field and the right-hand side. -/
theorem IsDirichletWeakSolution.orthogonalPullback {n : ℕ}
    {A : E n → E n →L[ℝ] E n} {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A g u) (R : E n ≃ₗᵢ[ℝ] E n) :
    IsDirichletWeakSolution (orthogonalPullbackDirichletField R A)
      (dirichletL2Pullback R g) (dirichletSobolevPullback R u) := by
  intro w
  let μ := (volume0 n).restrict (unitBall n)
  let hμ := orthogonal_measurePreserving_dirichletBall R
  let w' := dirichletSobolevPullback R.symm w
  let Q (y : E n) := inner ℝ (A y ((u : DirichletBallL2Pair n).snd y))
    ((w' : DirichletBallL2Pair n).snd y)
  let F (y : E n) := g y * ((w' : DirichletBallL2Pair n).fst y)
  have hOriginal : (∫ y, Q y ∂μ) = ∫ y, F y ∂μ := hu w'
  have hChange (q : E n → ℝ) : (∫ x, q (R x) ∂μ) = ∫ y, q y ∂μ :=
    hμ.integral_comp R.toHomeomorph.toMeasurableEquiv.measurableEmbedding q
  have hLeft :
      (∫ x, inner ℝ (orthogonalPullbackDirichletField R A x
        ((dirichletSobolevPullback R u : DirichletBallL2Pair n).snd x))
        ((w : DirichletBallL2Pair n).snd x) ∂μ) = ∫ x, Q (R x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [dirichletSobolevPullback_gradient_ae R u,
      hμ.quasiMeasurePreserving.tendsto_ae.eventually
        (dirichletSobolevPullback_gradient_ae R.symm w)] with x hu' hw'
    have hw'' : (w' : DirichletBallL2Pair n).snd (R x) =
        R ((w : DirichletBallL2Pair n).snd x) := by
      simpa only [w', LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply] using hw'
    rw [hu']
    change inner ℝ (R.symm (A (R x) (R (R.symm ((u : DirichletBallL2Pair n).snd (R x))))))
      ((w : DirichletBallL2Pair n).snd x) = Q (R x)
    rw [R.apply_symm_apply]
    change _ = inner ℝ (A (R x) ((u : DirichletBallL2Pair n).snd (R x)))
      ((w' : DirichletBallL2Pair n).snd (R x))
    rw [hw'']
    exact (R.inner_map_map
      (R.symm (A (R x) ((u : DirichletBallL2Pair n).snd (R x))))
      ((w : DirichletBallL2Pair n).snd x)).symm.trans (by rw [R.apply_symm_apply])
  have hRight : (∫ x, dirichletL2Pullback R g x * ((w : DirichletBallL2Pair n).fst x) ∂μ) =
      ∫ x, F (R x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [dirichletL2Pullback_ae R g,
      hμ.quasiMeasurePreserving.tendsto_ae.eventually
        (dirichletSobolevPullback_value_ae R.symm w)] with x hg' hw'
    have hw'' : (w' : DirichletBallL2Pair n).fst (R x) =
        (w : DirichletBallL2Pair n).fst x := by
      simpa only [w', LinearIsometryEquiv.symm_apply_apply] using hw'
    change dirichletL2Pullback R g x * ((w : DirichletBallL2Pair n).fst x) =
      g (R x) * ((w' : DirichletBallL2Pair n).fst (R x))
    rw [hg', hw'']
  exact hLeft.trans ((hChange Q).trans (hOriginal.trans ((hChange F).symm.trans hRight.symm)))

end KEBall
