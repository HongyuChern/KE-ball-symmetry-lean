import KEBall.DirichletDirectionalLogDet
import KEBall.DirichletLogDensityModulus
import KEBall.DirichletBallAverages

/-!
# The two-point defect inequality for the actual rough Hessian

The quantifiers are ordered for integration: for almost every second point,
the estimate holds for almost every first point.  The weights are those of
the actual cofactor at the first point, with one fixed direction family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder NNReal

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem dirichlet_hessian_directional_twoPoint_bound {n m : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {g : E n → ℝ}
    (hPos : ∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef)
    (hDet : ∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (g x))
    (v : Fin m → E n) {l U : ℝ} (hl : 0 < l)
    (hFrame : ∀ᵐ x ∂ν[n], ∃ β : Fin m → ℝ, (∀ k, l ≤ β k ∧ β k ≤ U) ∧
      dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x)) =
        ∑ k : Fin m, β k • rankOne ℝ (v k) (v k))
    {K : ℝ≥0} (hLip : LipschitzOnWith K g (closedUnitBall n))
    {D : ℝ} (hD : 0 ≤ D) (hExp : ∀ x ∈ closedUnitBall n, Real.exp (g x) ≤ D)
    {x₀ : E n} {R : ℝ} (hR : 0 < R) (hBall : closedBall x₀ R ⊆ unitBall n)
    (M : Fin m → ℝ)
    (hUpper : ∀ i, ∀ᵐ x ∂dirichletBallProbability x₀ (R / 4), fderiv ℝ G x (v i) (v i) ≤ M i) :
    ∀ j : Fin m, ∀ᵐ y ∂dirichletBallProbability x₀ (R / 4),
      ∀ᵐ x ∂dirichletBallProbability x₀ (R / 4),
        l * (fderiv ℝ G x (v j) (v j) - fderiv ℝ G y (v j) (v j)) ≤
          U * (∑ i : Fin m, (M i - fderiv ℝ G x (v i) (v i))) +
            (2 * D * (K : ℝ)) * R := by
  let μ := dirichletBallProbability x₀ (R / 4)
  have hSmall : ball x₀ (R / 4) ⊆ ball x₀ R := ball_subset_ball (by linarith)
  have hSub : ball x₀ (R / 4) ⊆ unitBall n := hSmall.trans (ball_subset_closedBall.trans hBall)
  have transfer {P : E n → Prop} (h : ∀ᵐ x ∂ν[n], P x) : ∀ᵐ x ∂μ, P x := by
    apply ae_dirichletBallProbability_iff.mpr
    exact ae_restrict_of_ae_restrict_of_subset hSub (ae_volume0_restrict_iff.mp h)
  have hPos' := transfer hPos
  have hDet' := transfer hDet
  have hFrame' := transfer hFrame
  have hUpperAll : ∀ᵐ x ∂μ, ∀ i : Fin m, fderiv ℝ G x (v i) (v i) ≤ M i :=
    ae_all_iff.mpr hUpper
  have hMem : ∀ᵐ x ∂μ, x ∈ ball x₀ (R / 4) :=
    ae_dirichletBallProbability_iff.mpr (ae_restrict_mem measurableSet_ball)
  intro j
  filter_upwards [hPos', hDet', hUpperAll, hMem] with y hyPos hyDet hyUpper hyMem
  filter_upwards [hPos', hDet', hFrame', hUpperAll, hMem] with x hxPos hxDet hxFrame hxUpper hxMem
  obtain ⟨β, hβ, hβRep⟩ := hxFrame
  have hLinear := dirichlet_directional_logdet_comparison (fderiv ℝ G x) (fderiv ℝ G y)
    hxPos hyPos v β hβRep
  rw [hxDet, hyDet, Real.log_exp, Real.log_exp] at hLinear
  have hSource := dirichlet_density_log_twoPoint_bound hLip hD hExp hR.le hBall
    (hSmall hxMem) (hSmall hyMem)
  exact dirichlet_directional_defect_comparison
    (fun i => fderiv ℝ G x (v i) (v i)) (fun i => fderiv ℝ G y (v i) (v i)) M β hl
    (by positivity) hβ hxUpper hyUpper (hLinear.trans hSource) j

end KEBall
