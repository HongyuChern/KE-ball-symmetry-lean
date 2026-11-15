import KEBall.DirichletUniformWeakHarnack
import KEBall.DirichletSmoothSupersolution
import KEBall.DirichletInteriorHessianEquation

/-!
# Pointwise weak Harnack for the actual smooth cofactor equation

The essential infimum is converted to values of the original continuous
function.  The constant is uniform under fixed coefficient bounds and
the radius factor remains `R^(-2n)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions ENNReal Gradient Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem dirichlet_essInf_le_of_continuousOn {n : ℕ}
    {s : Set (E n)} (hs : IsOpen s) {f : E n → ℝ} (hf : ContinuousOn f s)
    (hLo : IsBoundedUnder (· ≥ ·) (ae (volume.restrict s)) f)
    {x : E n} (hx : x ∈ s) : essInf f (volume.restrict s) ≤ f x := by
  have h := dirichlet_continuousOn_nonneg_of_ae (μ := (volume : Measure (E n))) hs
    (hf.sub continuousOn_const) ((ae_essInf_le hLo).mono fun _ h => sub_nonneg.mpr h)
  exact sub_nonneg.mp (h x hx)

theorem dirichlet_essInf_affine_le_of_positive_continuous {n : ℕ}
    {f : E n → ℝ} {x₀ y : E n} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (ball x₀ R))
    (hPos : ∀ x ∈ ball x₀ R, 0 < f x) (hy : y ∈ ball x₀ (R / 4)) :
    essInf (fun z : E n => f (x₀ + R • z))
      (volume.restrict (ball (0 : E n) (1 / 4 : ℝ))) ≤ f y := by
  have hMap (z : E n) (hz : z ∈ ball (0 : E n) (1 / 4 : ℝ)) :
      x₀ + R • z ∈ ball x₀ R := by
    have he := DeGiorgi.affine_preimage_ball_mul (d := 2 * n)
      (x₀ := x₀) (R := R) (ρ := (1 / 4 : ℝ)) hR
    have hQuarter : x₀ + R • z ∈ ball x₀ (R * (1 / 4 : ℝ)) := by
      change z ∈ (fun a => x₀ + R • a) ⁻¹' ball x₀ (R * (1 / 4 : ℝ))
      rw [he]
      exact hz
    exact (ball_subset_ball (by linarith)) hQuarter
  have hCont : ContinuousOn (fun z : E n => f (x₀ + R • z))
      (ball 0 (1 / 4 : ℝ)) :=
    hf.comp (continuous_const.add (continuous_const_smul R)).continuousOn hMap
  have hLo : IsBoundedUnder (· ≥ ·)
      (ae (volume.restrict (ball (0 : E n) (1 / 4 : ℝ))))
      (fun z => f (x₀ + R • z)) := by
    refine ⟨0, ?_⟩
    change ∀ᵐ z ∂(volume.restrict (ball (0 : E n) (1 / 4 : ℝ))), 0 ≤ f (x₀ + R • z)
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with z hz
    exact (hPos _ (hMap z hz)).le
  let z : E n := R⁻¹ • (y - x₀)
  have hz : z ∈ ball 0 (1 / 4 : ℝ) := by
    rw [mem_ball_zero_iff]
    have hny : ‖y - x₀‖ < R / 4 := by simpa only [dist_eq_norm] using mem_ball.mp hy
    calc
      ‖z‖ = R⁻¹ * ‖y - x₀‖ := by
        change ‖R⁻¹ • (y - x₀)‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      _ < R⁻¹ * (R / 4) := mul_lt_mul_of_pos_left hny (inv_pos.mpr hR)
      _ = 1 / 4 := by field_simp [hR.ne']
  have he : x₀ + R • z = y := by simp [z, smul_smul, hR.ne']
  have h := dirichlet_essInf_le_of_continuousOn isOpen_ball hCont hLo hz
  simpa only [he] using h

theorem exists_uniform_smooth_cofactor_pointwise_harnack {n : ℕ} (hn : 2 ≤ n)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E n → ℝ), SmoothNear (closedUnitBall n) u →
      (∀ x ∈ unitBall n, (complexHessian u x).PosDef) →
      (∀ x ∈ unitBall n, ‖dirichletCofactorOperator u x‖ ≤ K) →
      (∀ x ∈ unitBall n, ∀ v : E n,
        c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v) →
      ∀ (q : E n → ℝ), SmoothNear (closedUnitBall n) q →
        (∀ x ∈ unitBall n,
          dirichletBilinearContraction e[n] (dirichletCofactorOperator u x) (realHessian q x) ≤ 0) →
        ∀ (x₀ : E n) (R : ℝ), 0 < R → closedBall x₀ R ⊆ unitBall n →
          (∀ x ∈ ball x₀ R, 0 < q x) → ∀ y ∈ ball x₀ (R / 4),
            (R ^ (2 * n))⁻¹ * (∫ x in ball x₀ (R / 4), |q x|) ≤ C * q y := by
  obtain ⟨C, hC, hH⟩ := exists_uniform_dirichletWeakHarnack_constant hn hc hK
  refine ⟨C, hC, ?_⟩
  intro u hu huP hNorm hEll q hq hL x₀ R hR hBall hPos y hy
  have hAC : ContinuousOn (dirichletCofactorOperator u) (unitBall n) := by
    obtain ⟨U, hU, hSub, huU⟩ := hu
    exact (dirichletCofactorOperator_continuousOn hU huU).mono
      (ball_subset_closedBall.trans hSub)
  have hBound : ∀ᵐ x ∂ν[n], ‖dirichletCofactorOperator u x‖ ≤ K := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact hNorm x hx
  have hA : MemLp (dirichletCofactorOperator u) ⊤ ν[n] :=
    memLp_top_of_bound (hAC.aestronglyMeasurable measurableSet_ball) K hBound
  have hEllAe : ∀ᵐ x ∂ν[n], ∀ v : E n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (dirichletCofactorOperator u x v) v := by
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact hEll x hx
  obtain ⟨hqLp, hGrad⟩ := memLp_dirichlet_smoothNear_gradient (by omega : 0 < n) hq
  have h := hH (dirichletCofactorOperator u) hA hBound hEllAe q (∇ q) hqLp hGrad
    (IsDirichletWeakGradient.of_smoothNear (by omega) hq)
    (dirichlet_smooth_cofactor_weak_supersolution (by omega) hu hq huP hL)
    x₀ R hR hBall (by
      filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
      exact hPos x hx)
  have hqC : ContinuousOn q (ball x₀ R) := by
    intro x hx
    exact (hq.contDiffAt (ball_subset_closedBall (hBall (ball_subset_closedBall hx)))).continuousAt.continuousWithinAt
  exact h.trans (mul_le_mul_of_nonneg_left
    (dirichlet_essInf_affine_le_of_positive_continuous hR hqC hPos hy) hC)

end KEBall
