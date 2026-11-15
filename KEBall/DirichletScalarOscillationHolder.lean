import KEBall.DirichletScalarOscillationPower
import KEBall.DirichletBilinearNorm

/-! Pointwise Holder bounds for continuous fields from their actual
directional oscillations.  No representative selection is needed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter MeasureTheory Metric Set
open scoped BigOperators Topology

noncomputable section
namespace KEBall

private theorem scalar_norm_bilinear_sub_le_of_frame {n m : ℕ}
    (D Q : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hD : ∀ a b, D a b = D b a) (hQ : ∀ a b, Q a b = Q b a)
    (v : Fin m → E n)
    (hBasis : ∀ i : Fin (2 * n), ∃ k : Fin m,
      v k = EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)
    (hPairs : ∀ i j : Fin (2 * n), ∃ k : Fin m,
      v k = EuclideanSpace.basisFun (Fin (2 * n)) ℝ i +
        EuclideanSpace.basisFun (Fin (2 * n)) ℝ j)
    {B : ℝ} (h : ∀ k, |D (v k) (v k) - Q (v k) (v k)| ≤ B) :
    ‖D - Q‖ ≤ (2 * n : ℝ) ^ 2 * (3 / 2 * B) := by
  apply norm_dirichlet_bilinear_le_of_entries
  intro i j
  obtain ⟨bi, hbi⟩ := hBasis i
  obtain ⟨bj, hbj⟩ := hBasis j
  obtain ⟨p, hp⟩ := hPairs i j
  have hSym (a b : E n) : (D - Q) a b = (D - Q) b a := by
    simp only [_root_.sub_apply, hD a b, hQ a b]
  have hPol (a b : E n) : (D - Q) a b =
      ((D - Q) (a + b) (a + b) - (D - Q) a a - (D - Q) b b) / 2 := by
    simp only [map_add, ContinuousLinearMap.add_apply, hSym b a]
    ring
  have hDiag (k : Fin m) : |(D - Q) (v k) (v k)| ≤ B := by
    simpa only [_root_.sub_apply] using h k
  rw [hPol, ← hp, ← hbi, ← hbj, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hTri := (abs_sub ((D - Q) (v p) (v p) - (D - Q) (v bi) (v bi))
      ((D - Q) (v bj) (v bj))).trans
    (add_le_add (abs_sub ((D - Q) (v p) (v p)) ((D - Q) (v bi) (v bi))) le_rfl)
  have hpB := hDiag p
  have hiB := hDiag bi
  have hjB := hDiag bj
  linarith

theorem abs_dirichlet_scalar_sub_le_oscillation {n m : ℕ}
    {q : Fin m → E n → ℝ} (hq : ∀ i, ContinuousOn (q i) (closedUnitBall n))
    {x₀ : E n} {r : ℝ} (hr : 0 < r) (hBall : ball x₀ r ⊆ unitBall n)
    (i : Fin m) {x y : E n} (hx : x ∈ ball x₀ r) (hy : y ∈ ball x₀ r) :
    |q i x - q i y| ≤ dirichletScalarFamilyOscillation q x₀ r := by
  have hX := dirichlet_continuous_scalar_between_essential_bounds (hq i) hBall hx
  have hY := dirichlet_continuous_scalar_between_essential_bounds (hq i) hBall hy
  have he := dirichletScalarFamilyOscillation_entry_le hq hr hBall i
  rw [abs_le]
  constructor <;> linarith only [hX.1, hX.2, hY.1, hY.2, he]

theorem dirichlet_scalar_holder_of_oscillation_power {n m : ℕ}
    {q : Fin m → E n → ℝ} (hq : ∀ i, ContinuousOn (q i) (closedUnitBall n))
    {α D : ℝ} (hα : 0 ≤ α) (hD : 0 ≤ D)
    (hPower : ∀ (p : E n) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 →
      closedBall p R₀ ⊆ unitBall n → ∀ r : ℝ, 0 < r → r ≤ R₀ →
        dirichletScalarFamilyOscillation q p r ≤ (D * (4 / R₀ : ℝ) ^ α) * r ^ α)
    {x₀ : E n} {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hBall : closedBall x₀ (2 * R) ⊆ unitBall n)
    (i : Fin m) {x y : E n} (hx : x ∈ ball x₀ (R / 2)) (hy : y ∈ ball x₀ (R / 2)) :
    |q i x - q i y| ≤ (D * (8 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, abs_zero, norm_zero]
    positivity
  let d : ℝ := dist x y
  have hd : 0 < d := dist_pos.mpr hxy
  have hBig : closedBall x₀ R ⊆ unitBall n :=
    (closedBall_subset_closedBall (by linarith)).trans hBall
  have hCenter : closedBall x R ⊆ unitBall n := by
    intro z hz
    apply hBall
    apply mem_closedBall.mpr
    have ht := dist_triangle z x x₀
    have hzR := mem_closedBall.mp hz
    have hxR := mem_ball.mp hx
    linarith only [ht, hzR, hxR, hR]
  have hNorm : ‖x - y‖ = d := (dist_eq_norm x y).symm
  rw [hNorm]
  by_cases hNear : d < R / 2
  · have hr : 0 < 2 * d := by positivity
    have hrR : 2 * d ≤ R := by linarith only [hNear]
    have hSub : ball x (2 * d) ⊆ unitBall n :=
      ball_subset_closedBall.trans ((closedBall_subset_closedBall hrR).trans hCenter)
    have hy' : y ∈ ball x (2 * d) := by
      rw [mem_ball, dist_comm y x]
      change d < 2 * d
      linarith only [hd]
    have hOsc := abs_dirichlet_scalar_sub_le_oscillation hq hr hSub i (mem_ball_self hr) hy'
    have hPow := hPower x R hR hR1 hCenter (2 * d) hr hrR
    refine (hOsc.trans hPow).trans_eq ?_
    rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity),
      mul_assoc, ← Real.mul_rpow (by positivity) hd.le]
    congr 2
    ring
  · have hdR : R / 2 ≤ d := le_of_not_gt hNear
    have hSmall : ball x₀ (R / 2) ⊆ ball x₀ R := ball_subset_ball (by linarith)
    have hOsc := abs_dirichlet_scalar_sub_le_oscillation hq hR
      (ball_subset_closedBall.trans hBig) i (hSmall hx) (hSmall hy)
    have hPow := hPower x₀ R hR hR1 hBig R hR le_rfl
    have hCompare : (4 / R : ℝ) * R ≤ (8 / R : ℝ) * d := by
      have hMul := mul_le_mul_of_nonneg_left hdR (by positivity : 0 ≤ 8 / R)
      have he : (8 / R : ℝ) * (R / 2) = (4 / R : ℝ) * R := by ring
      rwa [he] at hMul
    apply (hOsc.trans hPow).trans
    rw [mul_assoc, ← Real.mul_rpow (by positivity) hR.le,
      mul_assoc, ← Real.mul_rpow (by positivity) hd.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hCompare hα) hD

theorem dirichlet_bilinear_holder_of_directional_oscillation_power {n m : ℕ}
    {P : E n → E n →L[ℝ] E n →L[ℝ] ℝ}
    (hP : ContinuousOn P (closedUnitBall n))
    (hSym : ∀ x ∈ unitBall n, ∀ a b, P x a b = P x b a)
    (v : Fin m → E n)
    (hBasis : ∀ i : Fin (2 * n), ∃ k : Fin m,
      v k = EuclideanSpace.basisFun (Fin (2 * n)) ℝ i)
    (hPairs : ∀ i j : Fin (2 * n), ∃ k : Fin m,
      v k = EuclideanSpace.basisFun (Fin (2 * n)) ℝ i +
        EuclideanSpace.basisFun (Fin (2 * n)) ℝ j)
    {α D : ℝ} (hα : 0 ≤ α) (hD : 0 ≤ D)
    (hPower : ∀ (p : E n) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 →
      closedBall p R₀ ⊆ unitBall n → ∀ r : ℝ, 0 < r → r ≤ R₀ →
        dirichletScalarFamilyOscillation (fun i x => P x (v i) (v i)) p r ≤
          (D * (4 / R₀ : ℝ) ^ α) * r ^ α)
    {x₀ : E n} {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hBall : closedBall x₀ (2 * R) ⊆ unitBall n)
    {x y : E n} (hx : x ∈ ball x₀ (R / 2)) (hy : y ∈ ball x₀ (R / 2)) :
    ‖P x - P y‖ ≤ (((2 * n : ℝ) ^ 2 * (3 / 2 * D)) * (8 / R : ℝ) ^ α) * ‖x - y‖ ^ α := by
  have hSub : ball x₀ (R / 2) ⊆ unitBall n :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hBall)
  have hq (i : Fin m) : ContinuousOn (fun z => P z (v i) (v i)) (closedUnitBall n) :=
    (hP.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hBound (i : Fin m) : |P x (v i) (v i) - P y (v i) (v i)| ≤
      (D * (8 / R : ℝ) ^ α) * ‖x - y‖ ^ α :=
    dirichlet_scalar_holder_of_oscillation_power hq hα hD hPower hR hR1 hBall i hx hy
  exact (scalar_norm_bilinear_sub_le_of_frame (P x) (P y)
    (hSym x (hSub hx)) (hSym y (hSub hy)) v hBasis hPairs hBound).trans_eq (by ring)

end KEBall
