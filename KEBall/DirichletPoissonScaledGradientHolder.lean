import KEBall.DirichletPoissonCutoffHolder

/-! A common radius-scaled Holder estimate for the actual first jet. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open Metric Set
open scoped ContDiff Laplacian

namespace KEBall

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Analysis.Schauder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

theorem exists_local_poisson_scaled_gradient_holder_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : V → ℝ), ContDiff ℝ ∞ u →
      ∀ (p : V) (R G L : ℝ), 0 < R → R ≤ 1 → 0 ≤ G → 0 ≤ L →
        (∀ z ∈ closedBall p R, ‖fderiv ℝ u z‖ ≤ G) →
        (∀ z ∈ closedBall p R, ‖Δ u z‖ ≤ L) →
        ∀ x ∈ ball p (R / 2), ∀ y ∈ ball p (R / 2),
          ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤
            (C * (G + L) / Real.sqrt R) * Real.sqrt ‖x - y‖ := by
  let d : ℝ := Module.finrank ℝ V
  let k₁ : ℝ := 4 * CutoffProfile.derivBound + 1
  let k₂ : ℝ := CutoffProfile.derivBound * (4 * d + 8) + 1
  let k : ℝ := 1 + k₁ + 4 * k₂ + 8 * d * k₁
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hC1 := heatC1_nonneg (V := V)
  have hCut := CutoffProfile.derivBound_nonneg
  have hk₁ : 0 ≤ k₁ := by dsimp [k₁]; positivity
  have hk₂ : 0 ≤ k₂ := by dsimp [k₂]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  let C : ℝ := heatC1 V * (k + 4) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u hu p R G L hR hR1 hG hL hGrad hLap x hx y hy
  let s : ℝ := Real.sqrt R
  have hs : 0 < s := Real.sqrt_pos.2 hR
  have hsSq : s ^ 2 = R := Real.sq_sqrt hR.le
  let w : V → ℝ := fun z => u z - u p
  have hw : ContDiff ℝ ∞ w := hu.sub contDiff_const
  have hfirst : fderiv ℝ w = fderiv ℝ u := funext fun z => fderiv_sub_const (u p)
  have hLapEq (z : V) : Δ w z = Δ u z := by
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hfirst]
  have hAmp (z : V) (hz : z ∈ closedBall p R) : ‖w z‖ ≤ G * R := by
    have hMv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun a _ => hu.differentiable (by simp) a) hGrad (convex_closedBall p R)
      (mem_closedBall_self hR.le) hz
    exact hMv.trans (mul_le_mul_of_nonneg_left
      (show ‖z - p‖ ≤ R by simpa only [dist_eq_norm] using mem_closedBall.mp hz) hG)
  have hRaw := norm_fderiv_sub_le_sqrt_of_poisson_cutoff hw p hR hs
    (mul_nonneg hG hR.le) hL hG hAmp
    (fun z hz => by rw [hLapEq]; exact hLap z hz)
    (fun z hz => by rw [hfirst]; exact hGrad z hz) hx hy
  rw [hfirst] at hRaw
  obtain ⟨hCut₁, hCut₂⟩ := poisson_half_ball_cutoff_bounds (V := V) hR
  change ballCutoffFDerivBound (R / 2) R ≤ k₁ / R at hCut₁
  change ballCutoffLaplacianBound (V := V) (R / 2) R ≤ k₂ / R ^ 2 at hCut₂
  have hOne : G + (G * R) * ballCutoffFDerivBound (R / 2) R ≤ (1 + k₁) * G := by
    calc
      _ ≤ G + (G * R) * (k₁ / R) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hCut₁ (mul_nonneg hG hR.le))
      _ = _ := by field_simp [hR.ne'] <;> ring
  have hTwo : L + (G * R) * ballCutoffLaplacianBound (V := V) (R / 2) R +
      2 * d * ballCutoffFDerivBound (R / 2) R * G ≤
        L + (k₂ + 2 * d * k₁) * G / R := by
    calc
      _ ≤ L + (G * R) * (k₂ / R ^ 2) + 2 * d * (k₁ / R) * G := by
        gcongr
      _ = _ := by field_simp [hR.ne'] <;> ring
  have hAlg : (1 + k₁) * G / s + 4 * (L + (k₂ + 2 * d * k₁) * G / R) * s =
      (k * G + 4 * L * R) / s := by
    rw [← hsSq]
    dsimp only [k]
    field_simp [hs.ne']
    ring
  have hNum : k * G + 4 * L * R ≤ (k + 4) * (G + L) := by
    have hLR := mul_le_of_le_one_right hL hR1
    nlinarith only [hLR, mul_nonneg hk hL, hG]
  have hCoef : heatC1 V *
      ((G + (G * R) * ballCutoffFDerivBound (R / 2) R) / s +
        4 * (L + (G * R) * ballCutoffLaplacianBound (V := V) (R / 2) R +
          2 * d * ballCutoffFDerivBound (R / 2) R * G) * s) ≤ C * (G + L) / s := by
    calc
      _ ≤ heatC1 V * ((1 + k₁) * G / s +
          4 * (L + (k₂ + 2 * d * k₁) * G / R) * s) := by
        apply mul_le_mul_of_nonneg_left _ hC1
        exact add_le_add (div_le_div_of_nonneg_right hOne hs.le)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTwo (by norm_num)) hs.le)
      _ = heatC1 V * ((k * G + 4 * L * R) / s) := by rw [hAlg]
      _ ≤ heatC1 V * (((k + 4) * (G + L)) / s) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hNum hs.le) hC1
      _ = (heatC1 V * (k + 4)) * ((G + L) / s) := by ring
      _ ≤ C * ((G + L) / s) := mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (div_nonneg (add_nonneg hG hL) hs.le)
      _ = _ := by ring
  exact hRaw.trans (mul_le_mul_of_nonneg_right hCoef (Real.sqrt_nonneg _))

end KEBall
