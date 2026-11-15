import KEBall.DirichletHessianGeometricDecay

/-! Monotonicity and component bounds for actual directional essential oscillations. -/

set_option autoImplicit false

open Filter MeasureTheory Metric Set
open scoped BigOperators NNReal

noncomputable section

namespace KEBall

theorem dirichletHessianOscillation_entry_nonneg {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : E n)
    {x₀ : E n} {r : ℝ} (hr : 0 < r) (hBall : ball x₀ r ⊆ unitBall n) :
    0 ≤ essSup (fun x => fderiv ℝ G x v v) (volume.restrict (ball x₀ r)) -
      essInf (fun x => fderiv ℝ G x v v) (volume.restrict (ball x₀ r)) := by
  letI : NeZero ((volume : Measure (E n)).restrict (ball x₀ r)) :=
    ⟨fun h => (measure_ball_pos volume x₀ hr).ne' (Measure.restrict_eq_zero.mp h)⟩
  obtain ⟨x, hxInf, hxSup⟩ :=
    (ae_dirichlet_hessianEntry_between_essential_bounds hG v hBall).exists
  exact sub_nonneg.mpr (hxInf.trans hxSup)

theorem dirichletHessianOscillation_entry_le {n m : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : Fin m → E n)
    {x₀ : E n} {r : ℝ} (hr : 0 < r) (hBall : ball x₀ r ⊆ unitBall n) (j : Fin m) :
    essSup (fun x => fderiv ℝ G x (v j) (v j)) (volume.restrict (ball x₀ r)) -
      essInf (fun x => fderiv ℝ G x (v j) (v j)) (volume.restrict (ball x₀ r)) ≤
        dirichletHessianOscillation G v x₀ r :=
  Finset.single_le_sum (fun i _ => dirichletHessianOscillation_entry_nonneg hG (v i) hr hBall)
    (Finset.mem_univ j)

theorem dirichletHessianOscillation_mono {n m : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : Fin m → E n)
    {x₀ : E n} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hBall : ball x₀ R ⊆ unitBall n) :
    dirichletHessianOscillation G v x₀ r ≤ dirichletHessianOscillation G v x₀ R := by
  letI : NeZero ((volume : Measure (E n)).restrict (ball x₀ r)) :=
    ⟨fun h => (measure_ball_pos volume x₀ hr).ne' (Measure.restrict_eq_zero.mp h)⟩
  have hSub : ball x₀ r ⊆ ball x₀ R := ball_subset_ball hrR
  have hMeas : (volume : Measure (E n)).restrict (ball x₀ r) ≤ volume.restrict (ball x₀ R) :=
    Measure.restrict_mono_set volume hSub
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨hLo, hHi⟩ := boundedUnder_dirichlet_hessianEntry_ball hG (v i) hBall
  obtain ⟨hsLo, hsHi⟩ := boundedUnder_dirichlet_hessianEntry_ball hG (v i) (hSub.trans hBall)
  exact sub_le_sub
    (essSup_mono_measure' hMeas hsLo.isCoboundedUnder_le hHi)
    (essInf_antitone_measure (Measure.absolutelyContinuous_of_le hMeas) hLo hsHi.isCoboundedUnder_ge)

end KEBall
