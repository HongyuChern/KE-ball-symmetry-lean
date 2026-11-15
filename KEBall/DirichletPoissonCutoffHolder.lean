import KEBall.DirichletPoissonGradientHolder
import KEBall.DirichletPoissonCutoff

/-! Local first-jet Holder control with an independent heat scale. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter Metric Set
open scoped ContDiff Laplacian Topology

noncomputable section
namespace KEBall

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Analysis.Schauder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

theorem norm_fderiv_sub_le_sqrt_of_poisson_cutoff
    {u : V → ℝ} (hu : ContDiff ℝ ∞ u) (p : V)
    {R s A L G : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hAmp : ∀ z ∈ closedBall p R, ‖u z‖ ≤ A)
    (hLap : ∀ z ∈ closedBall p R, ‖Δ u z‖ ≤ L)
    (hGrad : ∀ z ∈ closedBall p R, ‖fderiv ℝ u z‖ ≤ G)
    {x y : V} (hx : x ∈ ball p (R / 2)) (hy : y ∈ ball p (R / 2)) :
    ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ heatC1 V *
      ((G + A * ballCutoffFDerivBound (R / 2) R) / s +
        4 * (L + A * ballCutoffLaplacianBound (V := V) (R / 2) R +
          2 * (Module.finrank ℝ V : ℝ) * ballCutoffFDerivBound (R / 2) R * G) * s) *
            Real.sqrt ‖x - y‖ := by
  let chi := DifferentialGeometry.Analysis.ballCutoff p (R / 2) R
  let v : V → ℝ := fun z => chi z * u z
  have hhalf : 0 ≤ R / 2 := by positivity
  have hhalfR : R / 2 < R := by linarith
  have hchi : ContDiff ℝ ∞ chi := ballCutoff_contDiff p (R / 2) R
  have hv : ContDiff ℝ ∞ v := hchi.mul hu
  have hvc : HasCompactSupport v :=
    (ballCutoff_hasCompactSupport (center := p) hhalf hhalfR).mul_right
  have hchiNorm (z : V) : ‖chi z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc p (R / 2) R z).1]
    exact (ballCutoff_mem_Icc p (R / 2) R z).2
  have hD0 := ballCutoffFDerivBound_nonneg hhalf hhalfR
  have hD20 := ballCutoffLaplacianBound_nonneg (V := V) hhalf hhalfR
  have hD (z : V) : ‖fderiv ℝ chi z‖ ≤ ballCutoffFDerivBound (R / 2) R := by
    rw [show chi = DifferentialGeometry.Analysis.ballCutoff p (R / 2) R from rfl,
      fderiv_ballCutoff]
    exact norm_ballCutoffFDeriv_le hhalf hhalfR z
  have hDelta (z : V) : ‖Δ chi z‖ ≤ ballCutoffLaplacianBound (V := V) (R / 2) R := by
    rw [show chi = DifferentialGeometry.Analysis.ballCutoff p (R / 2) R from rfl,
      euclideanLaplacian_ballCutoff, Real.norm_eq_abs]
    exact abs_ballCutoffLaplacian_le hhalf hhalfR z
  have hOutside (z : V) (hz : z ∉ closedBall p R) :
      v =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    have hd : R < dist z p := not_le.mp hz
    have hopen : IsOpen {w : V | R < dist w p} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    filter_upwards [hopen.mem_nhds hd] with w hw
    simp only [v, show chi w = 0 from ballCutoff_eq_zero_of_le_dist hhalf hhalfR hw.le,
      zero_mul]
  let Gv : ℝ := G + A * ballCutoffFDerivBound (R / 2) R
  let Lv : ℝ := L + A * ballCutoffLaplacianBound (V := V) (R / 2) R +
    2 * (Module.finrank ℝ V : ℝ) * ballCutoffFDerivBound (R / 2) R * G
  have hGv : 0 ≤ Gv := add_nonneg hG (mul_nonneg hA hD0)
  have hLv : 0 ≤ Lv := by dsimp [Lv]; positivity
  have hvGrad (z : V) : ‖fderiv ℝ v z‖ ≤ Gv := by
    by_cases hz : z ∈ closedBall p R
    · rw [show v = (fun w => chi w * u w) from rfl,
        fderiv_fun_mul (hchi.differentiable (by simp) z) (hu.differentiable (by simp) z)]
      calc
        _ ≤ ‖chi z‖ * ‖fderiv ℝ u z‖ + ‖u z‖ * ‖fderiv ℝ chi z‖ := by
          simpa only [norm_smul] using norm_add_le
            (chi z • fderiv ℝ u z) (u z • fderiv ℝ chi z)
        _ ≤ 1 * G + A * ballCutoffFDerivBound (R / 2) R := by
          gcongr
          · exact hchiNorm z
          · exact hGrad z hz
          · exact hAmp z hz
          · exact hD z
        _ = _ := by dsimp [Gv]; ring
    · rw [(hOutside z hz).fderiv_eq, fderiv_const_apply, norm_zero]
      exact hGv
  have hvLap (z : V) : ‖Δ v z‖ ≤ Lv := by
    by_cases hz : z ∈ closedBall p R
    · refine (norm_euclideanLaplacian_mul_le hchi hu z).trans ?_
      dsimp [Lv]
      calc
        _ ≤ 1 * L + A * ballCutoffLaplacianBound (V := V) (R / 2) R +
            2 * (Module.finrank ℝ V : ℝ) * ballCutoffFDerivBound (R / 2) R * G := by
          gcongr
          · exact hchiNorm z
          · exact hLap z hz
          · exact hAmp z hz
          · exact hDelta z
          · exact hD z
          · exact hGrad z hz
        _ = _ := by rw [one_mul]
    · rw [(InnerProductSpace.laplacian_congr_nhds (hOutside z hz)).self_of_nhds]
      simpa using hLv
  have heq (z : V) (hz : z ∈ ball p (R / 2)) : v =ᶠ[𝓝 z] u := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    have hOne : chi w = 1 := ballCutoff_eq_one_of_mem_closedBall hhalf hhalfR
      (ball_subset_closedBall hw)
    simp only [v, hOne, one_mul]
  have h := norm_fderiv_sub_le_sqrt_of_compactSupport_poisson_scale
    hv hvc hGv hLv hs hvGrad hvLap x y
  rw [(heq x hx).fderiv_eq, (heq y hy).fderiv_eq] at h
  exact h

end KEBall
