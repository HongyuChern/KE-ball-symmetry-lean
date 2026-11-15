import KEBall.BedfordTaylorQuadraticTaylorModel
import KEBall.BedfordTaylorSmoothDensityPairing
import KEBall.BedfordTaylorTestMeasure

/-!
# Hessian convergence at points with a quadratic expansion
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace KEBall.BedfordTaylor

open PshLines (translationPairing)
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (complexHessian coordinateVector)
open PshLines.Regularization.HolomorphicPullback (explicitRadialKernel)

variable {n : ℕ}

theorem tendsto_realHessian_radialPairing_of_quadratic_expansion
    (R : ℝ) (hR : 0 < R) {g : ComplexModel n → ℝ} (hg : LocallyIntegrable g volume)
    (x : ComplexModel n) (c : ℝ) (L : ComplexModel n →L[ℝ] ℝ)
    (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (hrem : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0 : ComplexModel n),
      |g (x + h) - c - L h - A h h / 2| ≤ ε * ‖h‖ ^ 2)
    (v w : ComplexModel n) :
    Tendsto (fun j : ℕ => PshLines.realHessian (translationPairing volume g
      (explicitRadialKernel R hR j)) x v w) atTop (𝓝 ((A v w + A w v) / 2)) := by
  obtain ⟨χ, _, hχ⟩ := exists_testFunction_one_on
    (U := (⊤ : Opens (ComplexModel n))) (isCompact_closedBall x 1) (subset_univ _)
  let p := quadraticTaylorModel x c L A
  let q (y : ComplexModel n) := χ y * p y
  have hq : ContDiff ℝ 2 q :=
    (χ.contDiff.mul (contDiff_quadraticTaylorModel x c L A)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hQ : HasCompactSupport q := χ.hasCompactSupport.mul_right
  have hEq : q =ᶠ[𝓝 x] p := by
    filter_upwards [closedBall_mem_nhds x zero_lt_one] with y hy
    change χ y * p y = p y
    rw [hχ hy, Pi.one_apply, one_mul]
  have hEqShift : ∀ᶠ h : ComplexModel n in 𝓝 0, q (x + h) = p (x + h) := by
    have hc : Continuous (fun h : ComplexModel n => x + h) := continuous_const.add continuous_id
    have ht : Tendsto (fun h : ComplexModel n => x + h) (𝓝 0) (𝓝 x) := by
      simpa only [add_zero] using (hc.continuousAt (x := 0)).tendsto
    exact ht.eventually hEq
  apply tendsto_realHessian_radialPairing_of_quadratic_model R hR hg hq hQ
  · intro ε hε
    filter_upwards [hrem ε hε, hEqShift] with h hsmall hEq
    rw [hEq]
    have he : g (x + h) - p (x + h) = g (x + h) - c - L h - A h h / 2 := by
      simp only [p, quadraticTaylorModel, add_sub_cancel_left]
      ring
    rwa [he]
  · filter_upwards [hEq.iteratedFDeriv ℝ 2] with y hy
    have he : PshLines.realHessian q y v w = PshLines.realHessian p y v w :=
      congrArg (fun H => H ![v, w]) hy
    rw [he]
    exact realHessian_quadraticTaylorModel x c L A y v w

theorem tendsto_complexHessian_radialPairing_of_quadratic_expansion
    (R : ℝ) (hR : 0 < R) {g : ComplexModel n → ℝ} (hg : LocallyIntegrable g volume)
    (x : ComplexModel n) (c : ℝ) (L : ComplexModel n →L[ℝ] ℝ)
    (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (hrem : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0 : ComplexModel n),
      |g (x + h) - c - L h - A h h / 2| ≤ ε * ‖h‖ ^ 2) :
    Tendsto (fun j : ℕ => complexHessian (translationPairing volume g
      (explicitRadialKernel R hR j)) x) atTop
      (𝓝 (complexHessian (quadraticTaylorModel x c L A) x)) := by
  let q := quadraticTaylorModel x c L A
  have h (v w : ComplexModel n) :
      Tendsto (fun j : ℕ => PshLines.realHessian (translationPairing volume g
        (explicitRadialKernel R hR j)) x v w) atTop (𝓝 (PshLines.realHessian q x v w)) := by
    rw [realHessian_quadraticTaylorModel]
    exact tendsto_realHessian_radialPairing_of_quadratic_expansion R hR hg x c L A hrem v w
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let v : ComplexModel n := coordinateVector i
  let w : ComplexModel n := coordinateVector j
  unfold complexHessian
  exact (((Complex.continuous_ofReal.tendsto _).comp ((h v w).add (h (Complex.I • v) (Complex.I • w)))).div_const 4).add
    ((tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
      ((h v (Complex.I • w)).sub (h (Complex.I • v) w)))).div_const 4)

end KEBall.BedfordTaylor
