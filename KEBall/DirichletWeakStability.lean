import KEBall.DirichletRotatedEquation

/-!
# Energy stability of the weak Dirichlet equation

Changing a bounded coefficient field and the L² right-hand side changes
the weak solution by an amount controlled in the gradient norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private noncomputable def dirichletCoefficientEval (n : ℕ) :
    (E n →L[ℝ] E n) →L[ℝ] E n →L[ℝ] E n :=
  (ContinuousLinearMap.apply (E := E n) ℝ (E n)).flip

/-- Pointwise application of a bounded coefficient field to an L² vector field. -/
noncomputable def dirichletCoefficientAction {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ ν[n]) : DirichletBallL2 n (E n) →L[ℝ] DirichletBallL2 n (E n) :=
  (dirichletCoefficientEval n).holderL ν[n] ⊤ 2 2 (hA.toLp A)

theorem dirichletCoefficientAction_ae {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ ν[n]) (v : DirichletBallL2 n (E n)) :
    dirichletCoefficientAction hA v =ᵐ[ν[n]] fun x => A x (v x) := by
  refine EventuallyEq.trans ((dirichletCoefficientEval n).coeFn_holder (hA.toLp A) v) ?_
  filter_upwards [MemLp.coeFn_toLp hA] with x hx
  change (hA.toLp A) x (v x) = A x (v x)
  rw [hx]

private theorem norm_dirichletCoefficientAction_apply_le {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ ν[n]) {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ᵐ x ∂ν[n], ‖A x‖ ≤ C)
    (v : DirichletBallL2 n (E n)) : ‖dirichletCoefficientAction hA v‖ ≤ C * ‖v‖ := by
  have hEval : ‖dirichletCoefficientEval n‖ ≤ 1 := by
    apply (dirichletCoefficientEval n).opNorm_le_bound₂ (by norm_num)
    intro T x
    simpa only [dirichletCoefficientEval, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.apply_apply, one_mul] using T.le_opNorm x
  have hNorm : ‖hA.toLp A‖ ≤ C := by
    rw [Lp.norm_toLp, eLpNorm_exponent_top]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hBound)).trans_eq
      (ENNReal.toReal_ofReal hC)
  change ‖(dirichletCoefficientEval n).holder 2 (hA.toLp A) v‖ ≤ _
  calc
    _ ≤ ‖dirichletCoefficientEval n‖ * ‖hA.toLp A‖ * ‖v‖ :=
      (dirichletCoefficientEval n).norm_holder_apply_apply_le (hA.toLp A) v
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul hEval hNorm (norm_nonneg _) zero_le_one) (norm_nonneg v)

private theorem integrable_dirichletCoefficient_pairing {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ ν[n]) (v w : DirichletBallL2 n (E n)) :
    Integrable (fun x => inner ℝ (A x (v x)) (w x)) ν[n] := by
  apply (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (dirichletCoefficientAction hA v) w).congr
  filter_upwards [dirichletCoefficientAction_ae hA v] with x hx
  rw [hx]

private theorem integral_dirichletCoefficient_pairing_le {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : MemLp A ⊤ ν[n]) {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ᵐ x ∂ν[n], ‖A x‖ ≤ C)
    (v w : DirichletBallL2 n (E n)) :
    (∫ x, inner ℝ (A x (v x)) (w x) ∂ν[n]) ≤ C * ‖v‖ * ‖w‖ := by
  have he : (∫ x, inner ℝ (A x (v x)) (w x) ∂ν[n]) =
      inner ℝ (dirichletCoefficientAction hA v) w := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletCoefficientAction_ae hA v] with x hx
    rw [hx]
  rw [he]
  exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_dirichletCoefficientAction_apply_le hA hC hBound v) (norm_nonneg w))

/-- The energy bound with the forcing paired directly against the difference. -/
theorem norm_dirichletGradient_sub_le_of_weakSolutions_pairing {n : ℕ}
    {A B : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hB : MemLp B ⊤ ν[n])
    {l δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hDiff : ∀ᵐ x ∂ν[n], ‖A x - B x‖ ≤ δ)
    {f g : DirichletBallL2 n ℝ} {u w : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A f u) (hw : IsDirichletWeakSolution B g w)
    (hWork : inner ℝ (g - f) ((w - u : DirichletSobolev n) : DirichletBallL2Pair n).fst ≤
      C * ‖((w - u : DirichletSobolev n) : DirichletBallL2Pair n).snd‖) :
    l * ‖((w - u : DirichletSobolev n) : DirichletBallL2Pair n).snd‖ ≤
      C + δ * ‖(w : DirichletBallL2Pair n).snd‖ := by
  let z := w - u
  let U := (u : DirichletBallL2Pair n).snd
  let W := (w : DirichletBallL2Pair n).snd
  let Z := (z : DirichletBallL2Pair n).snd
  let p := (z : DirichletBallL2Pair n).fst
  have hZ : Z = W - U := rfl
  have hBA : MemLp (fun x => A x - B x) ⊤ ν[n] := hA.sub hB
  have hPair : (∫ x, inner ℝ (A x (Z x)) (Z x) ∂ν[n]) =
      (∫ x, inner ℝ (B x (W x)) (Z x) ∂ν[n]) -
      (∫ x, inner ℝ (A x (U x)) (Z x) ∂ν[n]) +
      (∫ x, inner ℝ ((A x - B x) (W x)) (Z x) ∂ν[n]) := by
    have hS : Integrable (fun x => inner ℝ (B x (W x)) (Z x) -
        inner ℝ (A x (U x)) (Z x)) ν[n] :=
      (integrable_dirichletCoefficient_pairing hB W Z).sub
        (integrable_dirichletCoefficient_pairing hA U Z)
    rw [← integral_sub (integrable_dirichletCoefficient_pairing hB W Z)
      (integrable_dirichletCoefficient_pairing hA U Z),
      ← integral_add hS (integrable_dirichletCoefficient_pairing hBA W Z)]
    apply integral_congr_ae
    rw [hZ]
    filter_upwards [Lp.coeFn_sub W U] with x hx
    simp only [hx, Pi.sub_apply, map_sub, inner_sub_left, sub_apply]
    ring
  have hData : (∫ x, inner ℝ (B x (W x)) (Z x) ∂ν[n]) -
      (∫ x, inner ℝ (A x (U x)) (Z x) ∂ν[n]) = inner ℝ (g - f) p := by
    rw [show (∫ x, inner ℝ (B x (W x)) (Z x) ∂ν[n]) = ∫ x, g x * p x ∂ν[n] from hw z,
      show (∫ x, inner ℝ (A x (U x)) (Z x) ∂ν[n]) = ∫ x, f x * p x ∂ν[n] from hu z,
      inner_sub_left, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
  have hCoer : l * ‖Z‖ ^ 2 ≤ ∫ x, inner ℝ (A x (Z x)) (Z x) ∂ν[n] := by
    rw [← real_inner_self_eq_norm_sq Z, MeasureTheory.L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    rw [← integral_const_mul]
    have hi : Integrable (fun x => ‖Z x‖ ^ 2) ν[n] := by
      simpa only [real_inner_self_eq_norm_sq] using (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) Z Z)
    apply integral_mono_ae (hi.const_mul l) (integrable_dirichletCoefficient_pairing hA Z Z)
    exact hE.mono (fun x hx => hx (Z x))
  have hPerturb := integral_dirichletCoefficient_pairing_le hBA hδ hDiff W Z
  rw [hPair, hData] at hCoer
  change inner ℝ (g - f) p ≤ C * ‖Z‖ at hWork
  have hFinal : (l * ‖Z‖) * ‖Z‖ ≤ (C + δ * ‖W‖) * ‖Z‖ := by
    nlinarith only [hCoer, hWork, hPerturb]
  change l * ‖Z‖ ≤ C + δ * ‖W‖
  rcases (norm_nonneg Z).lt_or_eq with hpos | hzero
  · exact (mul_le_mul_iff_of_pos_right hpos).mp hFinal
  · rw [← hzero, mul_zero]
    positivity

/-- The difference of two weak solutions has controlled gradient norm
when one coefficient field is uniformly elliptic and the perturbation is
essentially bounded. -/
theorem norm_dirichletGradient_sub_le_of_weakSolutions {n : ℕ} (hn : 0 < n)
    {A B : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hB : MemLp B ⊤ ν[n])
    {l δ : ℝ} (hδ : 0 ≤ δ)
    (hE : ∀ᵐ x ∂ν[n], ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hDiff : ∀ᵐ x ∂ν[n], ‖A x - B x‖ ≤ δ)
    {f g : DirichletBallL2 n ℝ} {u w : DirichletSobolev n}
    (hu : IsDirichletWeakSolution A f u) (hw : IsDirichletWeakSolution B g w) :
    l * ‖((w - u : DirichletSobolev n) : DirichletBallL2Pair n).snd‖ ≤
      ‖g - f‖ / (n : ℝ) + δ * ‖(w : DirichletBallL2Pair n).snd‖ := by
  apply norm_dirichletGradient_sub_le_of_weakSolutions_pairing hA hB hδ (by positivity) hE hDiff hu hw
  let z := w - u
  let Z := (z : DirichletBallL2Pair n).snd
  let p := (z : DirichletBallL2Pair n).fst
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ‖p‖ ≤ ‖Z‖ / (n : ℝ) := by
    have h := dirichletSobolev_poincare hn z
    change (n : ℝ) ^ 2 * ‖p‖ ^ 2 ≤ ‖Z‖ ^ 2 at h
    rw [← mul_pow] at h
    have h' := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp h
    apply (le_div_iff₀ hnR).mpr
    simpa only [mul_comm ‖p‖] using h'
  exact (real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by ring))

end KEBall
