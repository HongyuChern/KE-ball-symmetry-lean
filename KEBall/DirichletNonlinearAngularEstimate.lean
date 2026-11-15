import KEBall.DirichletAngularStability

/-! Uniform estimates on the third derivative with one angular argument. -/

set_option autoImplicit false

open InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff

set_option maxSynthPendingDepth 8

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_integral_sq_realThirdDerivative_angular_le {n : ℕ} (hn : 0 < n)
    {a b D L : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (hL : 0 ≤ L) :
    ∃ C ≥ (0 : ℝ), ∀ {u f : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) f →
      (∀ x ∈ unitSphere n, u x = 0) →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, (complexHessian u x).det.re = f x) →
      (∀ x ∈ unitBall n, a ^ n ≤ f x ∧ f x ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ‖fderiv ℝ f x‖ ≤ L) →
      (∀ x ∈ closedUnitBall n, ∀ w : E n, ‖w‖ = 1 → |realHessian u x w w| ≤ D) →
      ∀ (R : E n →L[ℝ] E n), star R = -R → (∀ x, R (J x) = J (R x)) →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (realThirdDerivative u x (R x) (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤ C * ‖R‖ ^ 2 := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C, hC, hEst⟩ := exists_integral_sq_realHessian_angularDerivative_le hn ha hb hD hL
  refine ⟨2 * C + 8 * (2 * n : ℝ) ^ 2 * D ^ 2, by positivity, ?_⟩
  intro u f hu hf hu0 huP huEq hDen hGrad hBound R hR hJ
  let w (x : E n) := fderiv ℝ u x (R x)
  let P (x : E n) := ∑ i, ∑ j, (realThirdDerivative u x (R x) (e[n] i) (e[n] j)) ^ 2
  let Q (x : E n) := ∑ i, ∑ j, (realHessian w x (e[n] i) (e[n] j)) ^ 2
  let M := 8 * (2 * n : ℝ) ^ 2 * D ^ 2 * ‖R‖ ^ 2
  let μ := (volume0 n).restrict (unitBall n)
  obtain ⟨U, hU, hSub, huU⟩ := hu
  have hu : SmoothNear (closedUnitBall n) u := ⟨U, hU, hSub, huU⟩
  have hw : ContDiffOn ℝ ∞ w U :=
    (huU.fderiv_of_isOpen hU (by simp)).clm_apply R.contDiff.contDiffOn
  have hHH := (huU.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞) (by simp)
  have hT : ContDiffOn ℝ ∞ (realThirdDerivative u) U :=
    hHH.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hP : ContinuousOn P U := continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_finsetSum Finset.univ fun j _ =>
      (((hT.continuousOn.clm_apply R.continuous.continuousOn).clm_apply continuousOn_const).clm_apply
        continuousOn_const).pow 2
  have hWH := (hw.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞) (by simp)
  have hQ : ContinuousOn Q U := continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_finsetSum Finset.univ fun j _ =>
      ((hWH.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2
  have hI {p : E n → ℝ} (hp : ContinuousOn p U) : Integrable p μ :=
    (hp.mono hSub).integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hPoint : P ≤ᵐ[μ] fun x => 2 * Q x + M := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hx
    have hx' := ball_subset_closedBall hx
    have huAt := hu.contDiffAt hx'
    have hN := norm_realHessian_le_of_unit_test huAt hD.le (hBound x hx')
    have he (i : Fin (2 * n)) : ‖e[n] i‖ = 1 := (e[n]).orthonormal.norm_eq_one i
    have hEntry (z y : E n) :
        |realHessian u x z y| ≤ (D * ‖z‖) * ‖y‖ := by
      rw [← Real.norm_eq_abs]
      exact ((realHessian u x z).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right (((realHessian u x).le_opNorm z).trans
          (mul_le_mul_of_nonneg_right hN (norm_nonneg z))) (norm_nonneg y))
    have hTerm (i j : Fin (2 * n)) :
        (realThirdDerivative u x (R x) (e[n] i) (e[n] j)) ^ 2 ≤
          2 * (realHessian w x (e[n] i) (e[n] j)) ^ 2 + 8 * D ^ 2 * ‖R‖ ^ 2 := by
      let S := realHessian u x (R (e[n] i)) (e[n] j)
      let T := realHessian u x (e[n] i) (R (e[n] j))
      have hS : |S| ≤ D * ‖R‖ := (hEntry _ _).trans (by
        rw [he j, mul_one]
        exact mul_le_mul_of_nonneg_left (by simpa only [he i, mul_one] using R.le_opNorm (e[n] i)) hD.le)
      have hT : |T| ≤ D * ‖R‖ := (hEntry _ _).trans (by
        rw [he i, mul_one]
        exact mul_le_mul_of_nonneg_left (by simpa only [he j, mul_one] using R.le_opNorm (e[n] j)) hD.le)
      have hST : |S + T| ≤ 2 * (D * ‖R‖) :=
        (abs_add_le _ _).trans ((add_le_add hS hT).trans_eq (by ring))
      have hSq : (S + T) ^ 2 ≤ (2 * (D * ‖R‖)) ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hST 2
      have hEq := realHessian_linearFieldDerivative hU huU (hSub hx') R (e[n] i) (e[n] j)
      change realHessian w x (e[n] i) (e[n] j) =
        realThirdDerivative u x (R x) (e[n] i) (e[n] j) + S + T at hEq
      rw [show realThirdDerivative u x (R x) (e[n] i) (e[n] j) =
        realHessian w x (e[n] i) (e[n] j) - (S + T) by linarith only [hEq]]
      nlinarith only [hSq, sq_nonneg (realHessian w x (e[n] i) (e[n] j) + (S + T))]
    change P x ≤ _
    calc
      P x ≤ ∑ i, ∑ j, (2 * (realHessian w x (e[n] i) (e[n] j)) ^ 2 + 8 * D ^ 2 * ‖R‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hTerm i j
      _ = 2 * Q x + M := by
        simp only [Q, M, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have h := integral_mono_ae (hI hP) (((hI hQ).const_mul 2).add (integrable_const M)) hPoint
  change (∫ x, P x ∂μ) ≤ ∫ x, 2 * Q x + M ∂μ at h
  rw [integral_add ((hI hQ).const_mul 2) (integrable_const M),
    integral_const_mul, integral_const, probReal_univ, one_smul] at h
  exact h.trans ((add_le_add_left (mul_le_mul_of_nonneg_left
    (hEst hu hf hu0 huP huEq hDen hGrad hBound R hR hJ) (show (0 : ℝ) ≤ 2 by norm_num)) M).trans_eq
    (by dsimp only [M]; ring))

end KEBall
