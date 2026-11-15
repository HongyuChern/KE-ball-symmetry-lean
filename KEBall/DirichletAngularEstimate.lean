import KEBall.DirichletWeakStability

/-! Energy bounds for rotations of a weak Dirichlet solution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem norm_orthogonalCLM_le_one {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    ‖R.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖R x‖ ≤ 1 * ‖x‖
  rw [R.norm_map, one_mul]

private theorem dist_orthogonal_apply_le {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    {x : E n} (hx : x ∈ unitBall n) :
    dist (R x) x ≤ ‖R.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E n)‖ := by
  let P := R.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E n)
  have h : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
  calc
    dist (R x) x = ‖P x‖ := by rw [dist_eq_norm]; rfl
    _ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
    _ ≤ ‖P‖ := mul_le_of_le_one_right (norm_nonneg _) h

/-- The gradient norm is unchanged by orthogonal pullback. -/
theorem norm_dirichletSobolevPullback_gradient {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    (u : DirichletSobolev n) :
    ‖(dirichletSobolevPullback R u : DirichletBallL2Pair n).snd‖ =
      ‖(u : DirichletBallL2Pair n).snd‖ := by
  let g := (u : DirichletBallL2Pair n).snd
  let gr := (dirichletSobolevPullback R u : DirichletBallL2Pair n).snd
  have he : ‖gr‖ = ‖dirichletL2Pullback R g‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [dirichletSobolevPullback_gradient_ae R u, dirichletL2Pullback_ae R g] with x hx hy
    change ‖gr x‖ = ‖dirichletL2Pullback R g x‖
    rw [hx, hy, R.symm.norm_map]
  exact he.trans ((dirichletL2Pullback R).norm_map g)

theorem norm_orthogonalPullbackDirichletField_sub_le {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {A : E n → E n →L[ℝ] E n}
    {K : ℝ≥0} (hLip : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM : ∀ y ∈ closedUnitBall n, ‖A y‖ ≤ M) {x : E n} (hx : x ∈ unitBall n) :
    ‖A x - orthogonalPullbackDirichletField R A x‖ ≤
      ((K : ℝ) + 2 * M) *
        ‖R.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E n)‖ := by
  let P := R.toContinuousLinearEquiv.toContinuousLinearMap
  let Q := R.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let I := ContinuousLinearMap.id ℝ (E n)
  let H := A (R x)
  have hxR : R x ∈ unitBall n := by
    exact mem_ball_zero_iff.mpr (R.norm_map x ▸ mem_ball_zero_iff.mp hx)
  have hH : ‖H‖ ≤ M := hM _ (ball_subset_closedBall hxR)
  have hMove : ‖A x - H‖ ≤ (K : ℝ) * ‖P - I‖ := by
    have h := hLip.dist_le_mul x (ball_subset_closedBall hx) (R x) (ball_subset_closedBall hxR)
    rw [dist_eq_norm, dist_comm x (R x)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (dist_orthogonal_apply_le R hx) K.coe_nonneg)
  have he : H - Q.comp (H.comp P) = Q.comp (((P - I).comp H) - H.comp (P - I)) := by
    ext v
    simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub, I]
    have hQP (w : E n) : Q (P w) = w := R.symm_apply_apply w
    rw [hQP]
    abel
  have hTwist : ‖H - Q.comp (H.comp P)‖ ≤ 2 * M * ‖P - I‖ := by
    rw [he]
    have hQ := norm_orthogonalCLM_le_one R.symm
    have hT := (Q.opNorm_comp_le (((P - I).comp H) - H.comp (P - I))).trans
      (mul_le_of_le_one_left (norm_nonneg _) hQ)
    have hSub := (norm_sub_le ((P - I).comp H) (H.comp (P - I))).trans
      (add_le_add ((P - I).opNorm_comp_le H) (H.opNorm_comp_le (P - I)))
    exact hT.trans (hSub.trans (by
      have hm := mul_le_mul_of_nonneg_right hH (norm_nonneg (P - I))
      nlinarith only [hm]))
  change ‖A x - Q.comp (H.comp P)‖ ≤ _
  rw [← sub_add_sub_cancel (A x) H (Q.comp (H.comp P))]
  exact (norm_add_le _ _).trans ((add_le_add hMove hTwist).trans_eq (by ring))

private theorem norm_dirichletL2Pullback_sub_le {n : ℕ} (hn : 0 < n)
    (R : E n ≃ₗᵢ[ℝ] E n) {g : DirichletBallL2 n ℝ} {G : E n → ℝ}
    (hRep : g =ᵐ[ν[n]] G) {L : ℝ≥0} (hLip : LipschitzOnWith L G (closedUnitBall n)) :
    ‖dirichletL2Pullback R g - g‖ ≤ (L : ℝ) *
      ‖R.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E n)‖ := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let D := ‖R.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E n)‖
  have hAE : ∀ᵐ x ∂ν[n], ‖(dirichletL2Pullback R g - g) x‖ ≤ (L : ℝ) * D := by
    filter_upwards [Lp.coeFn_sub (dirichletL2Pullback R g) g,
      dirichletL2Pullback_ae R g, hRep,
      (orthogonal_measurePreserving_dirichletBall R).quasiMeasurePreserving.tendsto_ae.eventually hRep,
      ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)]
        with x hSub hR hx hRx hBall
    have hBallR : R x ∈ unitBall n :=
      mem_ball_zero_iff.mpr (R.norm_map x ▸ mem_ball_zero_iff.mp hBall)
    rw [hSub, Pi.sub_apply, hR, hx, hRx, ← dist_eq_norm]
    exact (hLip.dist_le_mul (R x) (ball_subset_closedBall hBallR) x (ball_subset_closedBall hBall)).trans
      (mul_le_mul_of_nonneg_left (dist_orthogonal_apply_le R hBall) L.coe_nonneg)
  have h := Lp.norm_le_of_ae_bound (mul_nonneg L.coe_nonneg (norm_nonneg _)) hAE
  simpa [measureUnivNNReal] using h

/-- Bounded coefficients on the closed ball remain essentially bounded
under orthogonal pullback. -/
theorem memLp_orthogonalPullbackDirichletField {n : ℕ}
    (R : E n ≃ₗᵢ[ℝ] E n) {A : E n → E n →L[ℝ] E n}
    (hA : ContinuousOn A (closedUnitBall n)) :
    MemLp (orthogonalPullbackDirichletField R A) ⊤ ν[n] := by
  let B := orthogonalPullbackDirichletField R A
  let P := R.toContinuousLinearEquiv.toContinuousLinearMap
  let Q := R.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hMap : MapsTo R (closedUnitBall n) (closedUnitBall n) := by
    intro x hx
    exact mem_closedBall_zero_iff.mpr (R.norm_map x ▸ mem_closedBall_zero_iff.mp hx)
  have hBC : ContinuousOn B (closedUnitBall n) := by
    have hc : ContinuousOn (fun x => A (R x)) (closedUnitBall n) :=
      hA.comp R.continuous.continuousOn hMap
    have hRight : Continuous (fun T : E n →L[ℝ] E n => T.comp P) :=
      continuous_id.clm_comp_const P
    have hLeft : Continuous (fun T : E n →L[ℝ] E n => Q.comp T) :=
      (ContinuousLinearMap.compL ℝ (E n) (E n) (E n) Q).continuous
    exact hLeft.comp_continuousOn (hRight.comp_continuousOn hc)
  obtain ⟨M', hM'⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hBC
  have hAE := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  change MemLp B ⊤ ν[n]
  refine memLp_top_of_bound ((hBC.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) M' ?_
  exact hAE.mono fun x hx => hM' x (ball_subset_closedBall hx)

/-- Orthogonal increments of a weak solution are bounded in the gradient
norm by the size of the rotation and Lipschitz bounds for the data. -/
theorem norm_dirichletGradient_angular_increment_le {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    {l : ℝ} (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K L : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {G : E n → ℝ} (hRep : g =ᵐ[ν[n]] G)
    (hLipG : LipschitzOnWith L G (closedUnitBall n))
    {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (R : E n ≃ₗᵢ[ℝ] E n) :
    l * ‖((dirichletSobolevPullback R u - u : DirichletSobolev n) : DirichletBallL2Pair n).snd‖ ≤
      ((L : ℝ) / n + ((K : ℝ) + 2 * M) * ‖(u : DirichletBallL2Pair n).snd‖) *
        ‖R.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E n)‖ := by
  let B := orthogonalPullbackDirichletField R A
  let P := R.toContinuousLinearEquiv.toContinuousLinearMap
  let D := ‖P - ContinuousLinearMap.id ℝ (E n)‖
  have hAE := ae_restrict_mem (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)
  have hB : MemLp B ⊤ ν[n] := memLp_orthogonalPullbackDirichletField R hLipA.continuousOn
  have hDiff : ∀ᵐ x ∂ν[n], ‖A x - B x‖ ≤ ((K : ℝ) + 2 * M) * D :=
    hAE.mono fun _ hx => norm_orthogonalPullbackDirichletField_sub_le R hLipA hM hx
  have h := norm_dirichletGradient_sub_le_of_weakSolutions hn hA hB (by dsimp [D]; positivity)
    hE hDiff hu (hu.orthogonalPullback R)
  rw [norm_dirichletSobolevPullback_gradient] at h
  apply h.trans
  have hN := norm_dirichletL2Pullback_sub_le hn R hRep hLipG
  have hD := div_le_div_of_nonneg_right hN (show 0 ≤ (n : ℝ) by positivity)
  change ‖dirichletL2Pullback R g - g‖ / (n : ℝ) + ((K : ℝ) + 2 * M) * D *
      ‖(u : DirichletBallL2Pair n).snd‖ ≤
    ((L : ℝ) / n + ((K : ℝ) + 2 * M) * ‖(u : DirichletBallL2Pair n).snd‖) * D
  exact (add_le_add hD (le_refl _)).trans_eq (by ring)

end KEBall
