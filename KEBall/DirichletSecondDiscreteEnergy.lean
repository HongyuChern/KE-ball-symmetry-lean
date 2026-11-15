import KEBall.DirichletSecondDiscreteError

/-!
# A second-difference energy inequality for the actual C2 potential

The constants are independent of the nonzero rotation step. The right
side still contains the fourth-power integral of the Hessian of the first
difference; its absorption is not asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_dirichlet_unitary_second_difference_energy_bound {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : ContinuousOn f (closedUnitBall n))
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (hJ : ∀ x, S (J x) = J (S x)) :
    ∃ δ > (0 : ℝ), ∃ A ≥ (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∀ t : ℝ, t ≠ 0 → |t| < δ →
        (∫ x in unitBall n, ∑ i, ∑ j,
          (dirichletWithinRealHessian
            (dirichletOrthogonalDifference (orthogonalFlow S hS t) t
              (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u)) x
                (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
          A * (∫ x in unitBall n,
            (dirichletOrthogonalDifference (orthogonalFlow S hS t) t
              (dirichletOrthogonalDifference (orthogonalFlow S hS t) t f) x) ^ 2 ∂volume0 n) +
          B * (∫ x in unitBall n,
            ‖dirichletWithinRealHessian
              (dirichletOrthogonalDifference (orthogonalFlow S hS t) t u) x‖ ^ 4 ∂volume0 n) := by
  obtain ⟨ε, hε, C₀, hC₀, hEstimate⟩ :=
    exists_dirichlet_closedBall_cofactor_perturbation_estimate hn hu huS hu0 hPos
  obtain ⟨δ, hδ, hClose⟩ := Metric.eventually_nhds_iff.mp
    (eventually_dirichlet_unitary_meanCofactor_close hu S hS hε)
  obtain ⟨K, hK, hError⟩ := exists_integral_dirichlet_second_error_sq_bound hn hu
  refine ⟨δ, hδ, 2 * C₀, by positivity, 2 * C₀ * K, by positivity, ?_⟩
  intro t ht hSmall
  let R := orthogonalFlow S hS t
  let q := dirichletOrthogonalDifference R t u
  let p := dirichletOrthogonalDifference R t q
  let F := dirichletOrthogonalDifference R t (dirichletOrthogonalDifference R t f)
  let e := dirichletSecondDiscreteCofactorError R t u
  let g (x : E n) := F x - e x
  let a (x : E n) := dirichletMeanCofactor (dirichletWithinComplexHessian u x)
    (dirichletUnitaryPulledHessian u S hS t x)
  have hq : ContDiffOn ℝ 2 q (closedUnitBall n) :=
    contDiffOn_dirichletOrthogonalDifference R t hu
  have hp : ContDiffOn ℝ 2 p (closedUnitBall n) :=
    contDiffOn_dirichletOrthogonalDifference R t hq
  have hpS : ContDiffOn ℝ ∞ p (unitBall n) :=
    contDiffOn_dirichletOrthogonalDifference_ball R t
      (contDiffOn_dirichletOrthogonalDifference_ball R t huS)
  have hp0 : ∀ x ∈ unitSphere n, p x = 0 := by
    simpa only [dirichletIteratedOrthogonalDifference] using
      dirichletIteratedOrthogonalDifference_zero_on_sphere R t hu0 2
  have hF : ContinuousOn F (closedUnitBall n) :=
    continuousOn_dirichletOrthogonalDifference R t
      (continuousOn_dirichletOrthogonalDifference R t hf)
  have he : ContinuousOn e (closedUnitBall n) :=
    continuousOn_dirichletSecondDiscreteCofactorError R t hu
  have hg : ContinuousOn g (closedUnitBall n) := hF.sub he
  have hNear := hClose (show dist t 0 < δ by
    simpa only [dist_zero_right, Real.norm_eq_abs] using hSmall)
  have hEnergy :
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian p x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C₀ * ∫ x in unitBall n, (g x) ^ 2 ∂volume0 n := by
    apply hEstimate (q := p) (g := g) (a := a) hp hpS hp0 hg
    · intro x hx
      exact (hNear x (ball_subset_closedBall hx)).le
    · intro x hx
      dsimp only [a, g, F, e, p, q]
      rw [dirichletWithinRealHessian_eq_on_ball _ hx,
        dirichletWithinComplexHessian_eq_on_ball_of_C2 hu hx,
        dirichletUnitaryPulledHessian_eq_on_ball hu S hS t hx,
        dirichletSecondDiscreteCofactorError_eq_on_ball R t hu hx]
      exact dirichlet_unitary_second_difference_determinant_equation R
        (orthogonalFlow_apply_J S hS hJ t) t hu hEq hx
  letI : NeZero n := ⟨hn.ne'⟩
  letI : IsProbabilityMeasure ((volume0 n).restrict (unitBall n)) :=
    volume0_restrict_isProbability n
  have hInt {h : E n → ℝ} (hCont : ContinuousOn h (closedUnitBall n)) :
      IntegrableOn h (unitBall n) (volume0 n) :=
    (dirichlet_memLp_of_continuousOn hn hCont 1).integrable le_rfl
  have hSquare :
      (∫ x in unitBall n, (g x) ^ 2 ∂volume0 n) ≤
        2 * (∫ x in unitBall n, (F x) ^ 2 ∂volume0 n) +
        2 * (∫ x in unitBall n, (e x) ^ 2 ∂volume0 n) := by
    have h := setIntegral_mono_on (hInt (hg.pow 2))
      (hInt (((hF.pow 2).const_mul 2).add ((he.pow 2).const_mul 2)))
      measurableSet_ball (fun x _ => by
        change (F x - e x) ^ 2 ≤ 2 * (F x) ^ 2 + 2 * (e x) ^ 2
        nlinarith only [sq_nonneg (F x + e x)])
    simp only [Pi.add_apply, Pi.pow_apply] at h
    have hAdd := integral_add ((hInt (hF.pow 2)).const_mul 2)
      ((hInt (he.pow 2)).const_mul 2)
    simp only [Pi.pow_apply] at hAdd
    rw [hAdd, integral_const_mul, integral_const_mul] at h
    exact h
  have hE :
      (∫ x in unitBall n, (e x) ^ 2 ∂volume0 n) ≤
        K * ∫ x in unitBall n, ‖dirichletWithinRealHessian q x‖ ^ 4 ∂volume0 n :=
    hError R t ht
  calc
    _ ≤ C₀ * ∫ x in unitBall n, (g x) ^ 2 ∂volume0 n := hEnergy
    _ ≤ C₀ * (2 * (∫ x in unitBall n, (F x) ^ 2 ∂volume0 n) +
        2 * (∫ x in unitBall n, (e x) ^ 2 ∂volume0 n)) :=
      mul_le_mul_of_nonneg_left hSquare hC₀
    _ ≤ C₀ * (2 * (∫ x in unitBall n, (F x) ^ 2 ∂volume0 n) +
        2 * (K * ∫ x in unitBall n, ‖dirichletWithinRealHessian q x‖ ^ 4 ∂volume0 n)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))) hC₀
    _ = _ := by ring

end KEBall
