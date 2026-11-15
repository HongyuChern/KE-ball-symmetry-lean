import KEBall.DirichletPoissonCutoff

/-! A local Poisson gradient estimate with no gradient term on the right. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open Filter Metric Set
open scoped ContDiff Laplacian Topology

noncomputable section

namespace KEBall

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Analysis.Schauder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

theorem exists_local_poisson_gradient_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : V → ℝ), ContDiff ℝ ∞ u → ∀ (p : V)
      (R A L : ℝ), 0 < R → 0 ≤ A → 0 ≤ L →
      (∀ z ∈ closedBall p R, ‖u z‖ ≤ A) →
      (∀ z ∈ closedBall p R, ‖Δ u z‖ ≤ L) →
      ‖fderiv ℝ u p‖ ≤ C * (A / R + R * L) := by
  let K : ℝ := heatC1 V + 1
  let D : ℝ := 4 * CutoffProfile.derivBound + 1
  let E : ℝ := CutoffProfile.derivBound * (4 * (Module.finrank ℝ V : ℝ) + 8) + 1
  let H : ℝ := 2 + 16 * K * (Module.finrank ℝ V : ℝ) * D
  let C : ℝ := 4 * K * (H + E + 1)
  have hb := CutoffProfile.derivBound_nonneg
  have hK : 0 < K := by dsimp [K]; linarith [heatC1_nonneg (V := V)]
  have hD : 0 < D := by dsimp [D]; linarith [CutoffProfile.derivBound_nonneg]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hH : 2 ≤ H := by
    exact le_add_of_nonneg_right (show 0 ≤ 16 * K * (Module.finrank ℝ V : ℝ) * D by positivity)
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u hu p R A L hR hA hL hAmp hLap
  let w : V → ℝ := fun z => (R - dist z p) * ‖fderiv ℝ u z‖
  have hw : Continuous w :=
    (continuous_const.sub (continuous_id.dist continuous_const)).mul
      (hu.fderiv_right (m := ∞) (by simp)).continuous.norm
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall p R).exists_isMaxOn
    ⟨p, mem_closedBall_self hR.le⟩ hw.continuousOn
  let d := R - dist y p
  let Q := d * ‖fderiv ℝ u y‖
  have hy' : dist y p ≤ R := hy
  have hd0 : 0 ≤ d := sub_nonneg.mpr hy
  have hQ : 0 ≤ Q := mul_nonneg hd0 (norm_nonneg _)
  have hcenter : R * ‖fderiv ℝ u p‖ ≤ Q := by
    have hh : w p ≤ w y := hmax (mem_closedBall_self hR.le)
    simpa only [w, Q, d, dist_self, sub_zero] using hh
  by_cases hd : 0 < d
  · let r := d / 2
    have hr : 0 < r := half_pos hd
    have hrR : r ≤ R := by dsimp [r, d]; linarith [dist_nonneg (x := y) (y := p)]
    have hsub : closedBall y r ⊆ closedBall p R := by
      intro z hz
      have hz' : dist z y ≤ r := hz
      have ht := dist_triangle z y p
      change dist z p ≤ R
      dsimp [r, d] at hz'
      linarith [dist_nonneg (x := y) (y := p)]
    have hlocalG : ∀ z ∈ closedBall y r, ‖fderiv ℝ u z‖ ≤ Q / r := by
      intro z hz
      have hz' : dist z y ≤ r := hz
      have hdist : r ≤ R - dist z p := by
        have ht := dist_triangle z y p
        have hrid : 2 * r = R - dist y p := by dsimp [r, d]; ring
        linarith only [ht, hz', hrid]
      have hm : (R - dist z p) * ‖fderiv ℝ u z‖ ≤ Q := hmax (hsub hz)
      apply (le_div_iff₀ hr).mpr
      calc
        ‖fderiv ℝ u z‖ * r = r * ‖fderiv ℝ u z‖ := mul_comm _ _
        _ ≤ (R - dist z p) * ‖fderiv ℝ u z‖ := mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
        _ ≤ Q := hm
    have hcut := norm_fderiv_le_of_poisson_cutoff hu y hr
      (div_pos hr hHpos) hA hL (div_nonneg hQ hr.le)
      (fun z hz => hAmp z (hsub hz)) (fun z hz => hLap z (hsub hz)) hlocalG
    obtain ⟨hb1, hb2⟩ := poisson_half_ball_cutoff_bounds (V := V) hr
    have hcut' : ‖fderiv ℝ u y‖ ≤ K *
        (A / (r / H) + 2 * (r / H) *
          (L + A * (E / r ^ 2) +
            2 * (Module.finrank ℝ V : ℝ) * (D / r) * (Q / r))) := by
      refine hcut.trans ?_
      have hkC : heatC1 V ≤ K := by dsimp [K]; linarith
      have hDC := ballCutoffFDerivBound_nonneg (show 0 ≤ r / 2 by positivity)
        (show r / 2 < r by linarith)
      have hLC := ballCutoffLaplacianBound_nonneg (V := V)
        (show 0 ≤ r / 2 by positivity) (show r / 2 < r by linarith)
      gcongr
    have hpoly : H * Q ≤ 2 * K * H ^ 2 * A + 4 * K * r ^ 2 * L +
        4 * K * E * A + 8 * K * (Module.finrank ℝ V : ℝ) * D * Q := by
      have hm := mul_le_mul_of_nonneg_left hcut' (show 0 ≤ 2 * r * H by positivity)
      have hl : (2 * r * H) * ‖fderiv ℝ u y‖ = H * Q := by dsimp [r, Q]; ring
      have he : (2 * r * H) * (K *
          (A / (r / H) + 2 * (r / H) *
            (L + A * (E / r ^ 2) +
              2 * (Module.finrank ℝ V : ℝ) * (D / r) * (Q / r)))) =
          2 * K * H ^ 2 * A + 4 * K * r ^ 2 * L +
            4 * K * E * A + 8 * K * (Module.finrank ℝ V : ℝ) * D * Q := by
        field_simp [hr.ne', hHpos.ne']
        <;> ring
      simpa only [hl, he] using hm
    have hsmall : r ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hr.le hR.le).mpr hrR
    have hpoly' : (H / 2) * Q ≤
        (2 * K * H ^ 2 + 4 * K * E) * A + 4 * K * (R ^ 2 * L) := by
      have hRterm := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsmall hL) (show 0 ≤ 4 * K by positivity)
      have hHid : H = 2 + 16 * K * (Module.finrank ℝ V : ℝ) * D := rfl
      have hHQ := congrArg (fun a : ℝ => a * Q) hHid
      nlinarith only [hpoly, hRterm, hQ, hHQ]
    have hcoefA : 2 * K * H ^ 2 + 4 * K * E ≤ (H / 2) * C := by
      have he := mul_nonneg (mul_nonneg hK.le (sub_nonneg.mpr hH)) hE
      have hh := mul_nonneg hK.le hHpos.le
      dsimp [C]
      nlinarith only [he, hh]
    have hcoefL : 4 * K ≤ (H / 2) * C := by
      have hbase : 4 * K ≤ C := by
        have he := mul_nonneg hK.le (add_nonneg hHpos.le hE)
        dsimp [C]
        nlinarith only [he]
      exact hbase.trans (le_mul_of_one_le_left hC.le (by linarith))
    have hQbound : Q ≤ C * (A + R ^ 2 * L) := by
      apply (mul_le_mul_iff_right₀ (show 0 < H / 2 by positivity)).mp
      calc
        _ ≤ (2 * K * H ^ 2 + 4 * K * E) * A + 4 * K * (R ^ 2 * L) := hpoly'
        _ ≤ ((H / 2) * C) * A + ((H / 2) * C) * (R ^ 2 * L) :=
          add_le_add (mul_le_mul_of_nonneg_right hcoefA hA)
            (mul_le_mul_of_nonneg_right hcoefL (by positivity))
        _ = _ := by ring
    have hp := hcenter.trans hQbound
    have hfinal := (le_div_iff₀ hR).mpr (show ‖fderiv ℝ u p‖ * R ≤ C * (A + R ^ 2 * L) by
      simpa only [mul_comm] using hp)
    calc
      _ ≤ C * (A + R ^ 2 * L) / R := hfinal
      _ = C * (A / R + R * L) := by field_simp [hR.ne'] <;> ring
  · have hdEq : d = 0 := le_antisymm (le_of_not_gt hd) hd0
    have hp : ‖fderiv ℝ u p‖ ≤ 0 := by
      have hz : Q = 0 := by simp only [Q, hdEq, zero_mul]
      rw [hz] at hcenter
      exact (mul_le_mul_iff_right₀ hR).mp (by simpa only [mul_zero] using hcenter)
    exact hp.trans (by positivity)

/-- The local estimate only needs oscillation relative to the center, since
subtracting a constant preserves both the gradient and the Laplacian. -/
theorem exists_local_poisson_gradient_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : V → ℝ), ContDiff ℝ ∞ u → ∀ (p : V)
      (R A L : ℝ), 0 < R → 0 ≤ A → 0 ≤ L →
      (∀ z ∈ closedBall p R, ‖u z - u p‖ ≤ A) →
      (∀ z ∈ closedBall p R, ‖Δ u z‖ ≤ L) →
      ‖fderiv ℝ u p‖ ≤ C * (A / R + R * L) := by
  obtain ⟨C, hC, hlocal⟩ := exists_local_poisson_gradient_constant (V := V)
  refine ⟨C, hC, ?_⟩
  intro u hu p R A L hR hA hL hAmp hLap
  have hfirst : fderiv ℝ (fun y => u y - u p) = fderiv ℝ u :=
    funext fun y => fderiv_sub_const (u p)
  have hLap' (z : V) : Δ (fun y => u y - u p) z = Δ u z := by
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hfirst]
  have h := hlocal (fun z => u z - u p) (hu.sub contDiff_const) p R A L hR hA hL hAmp
    (fun z hz => by rw [hLap']; exact hLap z hz)
  simpa only [fderiv_sub_const] using h

end KEBall
