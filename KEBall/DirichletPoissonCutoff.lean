import KEBall.DirichletPoissonGradient
import KEBall.DirichletPoissonProduct
import DifferentialGeometry.Analysis.Schauder.Cutoff.Elliptic.Ball

/-! Localization of the heat-kernel Poisson gradient estimate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 500000

open Filter Metric Set
open scoped ContDiff Laplacian Topology

noncomputable section

namespace KEBall

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Analysis.Schauder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

theorem euclideanLaplacian_ballCutoff (p x : V) (r R : ℝ) :
    Δ (DifferentialGeometry.Analysis.ballCutoff p r R) x =
      ballCutoffLaplacian p r R x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hfirst : fderiv ℝ (DifferentialGeometry.Analysis.ballCutoff p r R) =
      ballCutoffFDeriv p r R := fderiv_ballCutoff p r R
  rw [hfirst, fderiv_ballCutoffFDeriv]
  simpa only [lapEval_apply] using lapEval_ballCutoffFDeriv2 p r R x

/-- The cutoff error has an explicit first-derivative coefficient.  The heat
scale `s` is independent of the support radius `R`, which permits absorption. -/
theorem norm_fderiv_le_of_poisson_cutoff
    {u : V → ℝ} (hu : ContDiff ℝ ∞ u) (p : V)
    {R s A L G : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hAmp : ∀ y ∈ closedBall p R, ‖u y‖ ≤ A)
    (hLap : ∀ y ∈ closedBall p R, ‖Δ u y‖ ≤ L)
    (hGrad : ∀ y ∈ closedBall p R, ‖fderiv ℝ u y‖ ≤ G) :
    ‖fderiv ℝ u p‖ ≤ heatC1 V *
      (A / s + 2 * s * (L + A * ballCutoffLaplacianBound (V := V) (R / 2) R +
        2 * (Module.finrank ℝ V : ℝ) * ballCutoffFDerivBound (R / 2) R * G)) := by
  let chi := DifferentialGeometry.Analysis.ballCutoff p (R / 2) R
  let v : V → ℝ := fun y => chi y * u y
  have hhalf : 0 ≤ R / 2 := by positivity
  have hhalfR : R / 2 < R := by linarith
  have hchi : ContDiff ℝ ∞ chi := ballCutoff_contDiff p (R / 2) R
  have hv : ContDiff ℝ ∞ v := hchi.mul hu
  have hvc : HasCompactSupport v :=
    (ballCutoff_hasCompactSupport (center := p) hhalf hhalfR).mul_right
  have hchiNorm (y : V) : ‖chi y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc p (R / 2) R y).1]
    exact (ballCutoff_mem_Icc p (R / 2) R y).2
  have hD (y : V) : ‖fderiv ℝ chi y‖ ≤ ballCutoffFDerivBound (R / 2) R := by
    rw [show chi = DifferentialGeometry.Analysis.ballCutoff p (R / 2) R from rfl,
      fderiv_ballCutoff]
    exact norm_ballCutoffFDeriv_le hhalf hhalfR y
  have hDelta (y : V) : ‖Δ chi y‖ ≤ ballCutoffLaplacianBound (V := V) (R / 2) R := by
    rw [show chi = DifferentialGeometry.Analysis.ballCutoff p (R / 2) R from rfl,
      euclideanLaplacian_ballCutoff, Real.norm_eq_abs]
    exact abs_ballCutoffLaplacian_le hhalf hhalfR y
  have hvAmp (y : V) : ‖v y‖ ≤ A := by
    by_cases hy : y ∈ closedBall p R
    · calc
        ‖v y‖ = ‖chi y‖ * ‖u y‖ := norm_mul _ _
        _ ≤ 1 * A := mul_le_mul (hchiNorm y) (hAmp y hy) (norm_nonneg _) (by norm_num)
        _ = A := one_mul A
    · have hz : chi y = 0 := ballCutoff_eq_zero_of_le_dist hhalf hhalfR
        (le_of_lt (not_le.mp hy))
      simpa [v, hz] using hA
  let Q := L + A * ballCutoffLaplacianBound (V := V) (R / 2) R +
    2 * (Module.finrank ℝ V : ℝ) * ballCutoffFDerivBound (R / 2) R * G
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg
      (add_nonneg hL (mul_nonneg hA (ballCutoffLaplacianBound_nonneg hhalf hhalfR)))
      (mul_nonneg (mul_nonneg (by positivity) (ballCutoffFDerivBound_nonneg hhalf hhalfR)) hG)
  have hvLap (y : V) : ‖Δ v y‖ ≤ Q := by
    by_cases hy : y ∈ closedBall p R
    · refine (norm_euclideanLaplacian_mul_le hchi hu y).trans ?_
      dsimp [Q]
      have hD0 := ballCutoffFDerivBound_nonneg hhalf hhalfR
      have hD20 := ballCutoffLaplacianBound_nonneg (V := V) hhalf hhalfR
      calc
        _ ≤ 1 * L + A * ballCutoffLaplacianBound (V := V) (R / 2) R +
            2 * (Module.finrank ℝ V : ℝ) * ballCutoffFDerivBound (R / 2) R * G := by
          gcongr
          · exact hchiNorm y
          · exact hLap y hy
          · exact hAmp y hy
          · exact hDelta y
          · exact hD y
          · exact hGrad y hy
        _ = _ := by rw [one_mul]
    · have hd : R < dist y p := not_le.mp hy
      have hzero : v =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have hopen : IsOpen {z : V | R < dist z p} := isOpen_lt continuous_const (continuous_id.dist continuous_const)
        filter_upwards [hopen.mem_nhds hd] with z hz
        simp only [v, show chi z = 0 from ballCutoff_eq_zero_of_le_dist hhalf hhalfR hz.le,
          zero_mul]
      rw [(InnerProductSpace.laplacian_congr_nhds hzero).self_of_nhds]
      simpa using hQ
  have heq : v =ᶠ[𝓝 p] u := by
    filter_upwards [ball_mem_nhds p (half_pos hR)] with y hy
    have hOne : chi y = 1 := ballCutoff_eq_one_of_mem_closedBall hhalf hhalfR
      (ball_subset_closedBall hy)
    simp only [v, hOne, one_mul]
  have h := norm_fderiv_le_of_compactSupport_laplacian_bound hv hvc hA hQ hs hvAmp hvLap p
  rw [heq.fderiv_eq] at h
  exact h

theorem poisson_half_ball_cutoff_bounds {R : ℝ} (hR : 0 < R) :
    ballCutoffFDerivBound (R / 2) R ≤ (4 * CutoffProfile.derivBound + 1) / R ∧
    ballCutoffLaplacianBound (V := V) (R / 2) R ≤
      (CutoffProfile.derivBound * (4 * (Module.finrank ℝ V : ℝ) + 8) + 1) / R ^ 2 := by
  have hd : R ^ 2 - (R / 2) ^ 2 ≠ 0 := by nlinarith [sq_pos_of_pos hR]
  have h1 : ballCutoffFDerivBound (R / 2) R =
      (8 * CutoffProfile.derivBound / 3) / R := by
    unfold ballCutoffFDerivBound
    field_simp [hd, hR.ne']
    <;> ring
  have h2 : ballCutoffLaplacianBound (V := V) (R / 2) R =
      (CutoffProfile.derivBound * ((8 : ℝ) * Module.finrank ℝ V / 3 + 64 / 9)) / R ^ 2 := by
    unfold ballCutoffLaplacianBound
    field_simp [hd, hR.ne']
    <;> ring
  constructor
  · rw [h1, div_le_div_iff_of_pos_right hR]
    nlinarith only [CutoffProfile.derivBound_nonneg]
  · rw [h2, div_le_div_iff_of_pos_right (sq_pos_of_pos hR)]
    nlinarith only [CutoffProfile.derivBound_nonneg,
      mul_nonneg CutoffProfile.derivBound_nonneg (Nat.cast_nonneg (Module.finrank ℝ V))]

end KEBall
