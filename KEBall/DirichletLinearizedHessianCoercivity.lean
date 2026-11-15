import KEBall.DirichletAffineEllipticNeighborhood
import KEBall.DirichletRealHessianStability

/-!
# A uniform global L2 Hessian estimate for the determinant linearization

The constant depends only on the dimension, density bounds and real
Hessian bound.  Small affine variations may have a radius depending on
the test function; the estimate constant does not depend on that radius.
The proof uses the existing nonlinear zero-boundary stability and the
actual L2 limit of determinant difference quotients.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem exists_integral_sq_realHessian_le_linearizedDet {n : ℕ} (hn : 0 < n)
    {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    ∃ C ≥ (0 : ℝ), ∀ {u q : E n → ℝ},
      SmoothNear (closedUnitBall n) u → SmoothNear (closedUnitBall n) q →
      (∀ x ∈ unitSphere n, u x = 0) → (∀ x ∈ unitSphere n, q x = 0) →
      (∀ x ∈ closedUnitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ closedUnitBall n,
        a ^ n ≤ (complexHessian u x).det.re ∧ (complexHessian u x).det.re ≤ b ^ n) →
      (∀ x ∈ closedUnitBall n, ‖realHessian u x‖ ≤ D) →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (realHessian q x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * ∫ x in unitBall n, (MoserTrudinger.cofactorContraction u q x) ^ 2 ∂volume0 n := by
  obtain ⟨K, hK, hStab⟩ := exists_integral_sq_complexHessian_sub_le_of_dirichlet_data
    hn (show 0 < a / 2 by positivity) (show 0 < b + 1 by positivity)
      (show 0 < D + 1 by positivity)
  let C : ℝ := (16 * n : ℝ) * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u q hu hq hu0 hq0 huP hDen hHess
  let μ := (volume0 n).restrict (unitBall n)
  let Q : ℝ := ∫ x, ∑ i, ∑ j, (realHessian q x (e[n] i) (e[n] j)) ^ 2 ∂μ
  have hLower : (a / 2) ^ n < a ^ n :=
    pow_lt_pow_left₀ (by linarith) (by positivity) hn.ne'
  have hUpper : b ^ n < (b + 1) ^ n :=
    pow_lt_pow_left₀ (by linarith) hb.le hn.ne'
  have hNear := eventually_dirichlet_affine_elliptic_bounds hu hq huP
    (fun x hx => ⟨hLower.trans_le (hDen x hx).1, (hDen x hx).2.trans_lt hUpper⟩)
    (fun x hx => (hHess x hx).trans_lt (lt_add_one D))
  have hAff (s : ℝ) : SmoothNear (closedUnitBall n) (u + s • q) := by
    obtain ⟨U, hU, hSubU, huU⟩ := hu
    obtain ⟨V, hV, hSubV, hqV⟩ := hq
    exact ⟨U ∩ V, hU.inter hV, subset_inter hSubU hSubV,
      (huU.mono inter_subset_left).add ((hqV.mono inter_subset_right).const_smul s)⟩
  have hDensitySmooth {v : E n → ℝ} (hv : SmoothNear (closedUnitBall n) v) :
      SmoothNear (closedUnitBall n) (fun x => (complexHessian v x).det.re) := by
    obtain ⟨U, hU, hSub, hvU⟩ := hv
    exact ⟨U, hU, hSub, Complex.reCLM.contDiff.comp_contDiffOn
      (matrixField_det_contDiffOn (complexHessian_contDiffOn hU hvU))⟩
  have hDiag {v : E n → ℝ} {x : E n} (h : ‖realHessian v x‖ ≤ D + 1)
      (z : E n) (hz : ‖z‖ = 1) : |realHessian v x z z| ≤ D + 1 := by
    rw [← Real.norm_eq_abs]
    exact ((realHessian v x z).le_opNorm z).trans (by
      rw [hz, mul_one]
      exact ((realHessian v x).le_opNorm z).trans (by rwa [hz, mul_one]))
  let t (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
  have ht (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  have hT : Tendsto t atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => (ht m).ne'⟩
  have hEv := (hT.mono_right nhdsWithin_le_nhds) hNear
  have hBound : ∀ᶠ m in atTop, Q ≤ C *
      ∫ x, (((complexHessian (u + t m • q) x).det.re -
        (complexHessian u x).det.re) / t m) ^ 2 ∂μ := by
    filter_upwards [hEv] with m hm
    have hv0 (x : E n) (hx : x ∈ unitSphere n) : (u + t m • q) x = 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu0 x hx, hq0 x hx,
        mul_zero, add_zero]
    have hComplex := hStab hu (hAff (t m)) (hDensitySmooth hu) (hDensitySmooth (hAff (t m)))
      hu0 hv0 (fun x hx => huP x (ball_subset_closedBall hx))
      (fun x hx => (hm x (ball_subset_closedBall hx)).1) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun x hx => ⟨hLower.le.trans (hDen x (ball_subset_closedBall hx)).1,
        (hDen x (ball_subset_closedBall hx)).2.trans hUpper.le⟩)
      (fun x hx => ⟨(hm x (ball_subset_closedBall hx)).2.1.le,
        (hm x (ball_subset_closedBall hx)).2.2.1.le⟩)
      (fun x hx => hDiag ((hHess x hx).trans (le_add_of_nonneg_right zero_le_one)))
      (fun x hx => hDiag (hm x hx).2.2.2.le)
    have hReal := (integral_sq_realHessian_sub_le_complex hn hu (hAff (t m)) hu0 hv0).trans
      (mul_le_mul_of_nonneg_left hComplex (by positivity : (0 : ℝ) ≤ 16 * n))
    have hLeft : (∫ x, ∑ i, ∑ j,
        ((realHessian (u + t m • q) x - realHessian u x) (e[n] i) (e[n] j)) ^ 2 ∂μ) =
        (t m) ^ 2 * Q := by
      rw [show Q = ∫ x, ∑ i, ∑ j, (realHessian q x (e[n] i) (e[n] j)) ^ 2 ∂μ from rfl,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
      rw [dirichlet_realHessian_affine (hu.contDiffAt (ball_subset_closedBall hx))
        (hq.contDiffAt (ball_subset_closedBall hx)), add_sub_cancel_left]
      simp only [_root_.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
    have hRight : (∫ x, (((complexHessian (u + t m • q) x).det.re -
        (complexHessian u x).det.re) / t m) ^ 2 ∂μ) =
        (t m)⁻¹ ^ 2 * ∫ x,
          ((complexHessian (u + t m • q) x).det.re - (complexHessian u x).det.re) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (((complexHessian (u + t m • q) x).det.re -
          (complexHessian u x).det.re) / t m) ^ 2 =
            (t m)⁻¹ ^ 2 * ((complexHessian (u + t m • q) x).det.re -
              (complexHessian u x).det.re) ^ 2
        rw [div_eq_mul_inv, mul_pow, mul_comm]
    change (∫ x, ∑ i, ∑ j,
        ((realHessian (u + t m • q) x - realHessian u x) (e[n] i) (e[n] j)) ^ 2 ∂μ) ≤ _ at hReal
    rw [hLeft] at hReal
    have hReal' : (t m) ^ 2 * Q ≤ C * ∫ x,
        ((complexHessian (u + t m • q) x).det.re - (complexHessian u x).det.re) ^ 2 ∂μ := by
      simpa only [C, mul_assoc] using hReal
    rw [hRight]
    calc
      Q = (t m)⁻¹ ^ 2 * ((t m) ^ 2 * Q) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ht m).ne', one_pow, one_mul]
      _ ≤ (t m)⁻¹ ^ 2 * (C * ∫ x,
          ((complexHessian (u + t m • q) x).det.re - (complexHessian u x).det.re) ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hReal' (sq_nonneg _)
      _ = _ := by ring
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    ((tendsto_integral_sq_dirichlet_density_slope hn hu hq hT).const_mul C) hBound

end KEBall
