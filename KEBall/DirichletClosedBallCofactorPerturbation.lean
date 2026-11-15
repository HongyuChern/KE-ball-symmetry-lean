import KEBall.DirichletClosedBallCofactorEstimate
import KEBall.DirichletBilinearNorm
import Mathlib.Algebra.Order.Chebyshev

/-!
# Stability of the actual closed-ball Hessian estimate

The reference coefficient is the cofactor of the supplied C2 potential.
A sufficiently small uniform perturbation of that coefficient preserves
the global L2 Hessian estimate. The perturbed coefficient need not have
any derivatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter InnerProductSpace Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace KEBall

local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ

theorem norm_dirichlet_bilinear_sq_le_sum_entries {n : ℕ}
    (H : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ‖H‖ ^ 2 ≤ (2 * n : ℝ) ^ 2 *
      ∑ i, ∑ j, (H (e[n] i) (e[n] j)) ^ 2 := by
  have hNorm := pow_le_pow_left₀ (norm_nonneg H)
    (norm_dirichlet_bilinear_le_sum_entries H) 2
  let f (s : Fin (2 * n) × Fin (2 * n)) := |H (e[n] s.1) (e[n] s.2)|
  have hSum := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
  simp only [f, Fintype.sum_prod_type, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, sq_abs] at hSum
  exact hNorm.trans (by simpa only [pow_two] using hSum)

private theorem exists_positive_quadratic_absorption_scale {T : ℝ} (hT : 0 ≤ T) :
    ∃ ε > (0 : ℝ), T * ε ^ 2 ≤ 1 / 2 := by
  let ε := (2 * T + 1)⁻¹
  have hDen : 0 < 2 * T + 1 := by positivity
  have hε : 0 < ε := inv_pos.mpr hDen
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    exact inv_le_one_of_one_le₀ (by linarith)
  have he : (2 * T + 1) * ε = 1 := mul_inv_cancel₀ hDen.ne'
  have hSq : ε ^ 2 ≤ ε := by nlinarith only [hε1, hε.le]
  refine ⟨ε, hε, (mul_le_mul_of_nonneg_left hSq hT).trans ?_⟩
  nlinarith only [he, hε.le]

theorem exists_dirichlet_closedBall_cofactor_perturbation_estimate {n : ℕ}
    (hn : 0 < n) {u : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef) :
    ∃ ε > (0 : ℝ), ∃ C ≥ (0 : ℝ),
      ∀ {q g : E n → ℝ} {a : E n → E n →L[ℝ] E n},
      ContDiffOn ℝ 2 q (closedUnitBall n) →
      ContDiffOn ℝ ∞ q (unitBall n) →
      (∀ x ∈ unitSphere n, q x = 0) →
      ContinuousOn g (closedUnitBall n) →
      (∀ x ∈ unitBall n,
        ‖dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x) - a x‖ ≤ ε) →
      (∀ x ∈ unitBall n,
        dirichletContractionCLM n (a x) (dirichletWithinRealHessian q x) = g x) →
      (∫ x in unitBall n, ∑ i, ∑ j,
        (dirichletWithinRealHessian q x (e[n] i) (e[n] j)) ^ 2 ∂volume0 n) ≤
        C * ∫ x in unitBall n, (g x) ^ 2 ∂volume0 n := by
  obtain ⟨C₀, hC₀, hRef⟩ := exists_dirichlet_closedBall_cofactor_hessian_estimate
    hn hu huS hu0 hPos
  let K : ℝ := ‖dirichletContractionCLM n‖
  let M : ℝ := K ^ 2 * (2 * n : ℝ) ^ 2
  have hK : 0 ≤ K := norm_nonneg (dirichletContractionCLM n)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨ε, hε, hSmall⟩ := exists_positive_quadratic_absorption_scale
    (show 0 ≤ 2 * C₀ * M by positivity)
  refine ⟨ε, hε, 4 * C₀, by positivity, ?_⟩
  intro q g a hq hqS hq0 hg hClose hEq
  let H := dirichletWithinRealHessian q
  let A (x : E n) := dirichletCofactorOfMatrix (dirichletWithinComplexHessian u x)
  let e (x : E n) := ∑ i, ∑ j, (H x (e[n] i) (e[n] j)) ^ 2
  let l (x : E n) := dirichletContractionCLM n (A x) (H x)
  have hH : ContinuousOn H (closedUnitBall n) :=
    continuousOn_dirichletWithinRealHessian hq
  have hA : ContinuousOn A (closedUnitBall n) :=
    contDiff_dirichletCofactorOfMatrix.continuous.comp_continuousOn
      (continuousOn_dirichletWithinComplexHessian_of_C2 hu)
  have he : ContinuousOn e (closedUnitBall n) :=
    continuousOn_finsetSum Finset.univ fun i _ =>
      continuousOn_finsetSum Finset.univ fun j _ =>
        ((hH.clm_apply continuousOn_const).clm_apply continuousOn_const).pow 2
  have hl : ContinuousOn l (closedUnitBall n) :=
    ((dirichletContractionCLM n).continuous.comp_continuousOn hA).clm_apply hH
  have hInt {f : E n → ℝ} (hf : ContinuousOn f (closedUnitBall n)) :
      IntegrableOn f (unitBall n) (volume0 n) :=
    hf.integrableOn_of_subset_isCompact (isCompact_closedBall _ _) measurableSet_ball
      ball_subset_closedBall (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hPoint (x : E n) (hx : x ∈ unitBall n) :
      (l x) ^ 2 ≤ 2 * (g x) ^ 2 + (2 * M * ε ^ 2) * e x := by
    let c := dirichletContractionCLM n (A x - a x) (H x)
    have hc : |c| ≤ K * ε * ‖H x‖ := by
      have h := (dirichletContractionCLM n).le_opNorm₂ (A x - a x) (H x)
      rw [Real.norm_eq_abs] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hClose x hx) hK) (norm_nonneg _))
    have hcSq := pow_le_pow_left₀ (abs_nonneg c) hc 2
    rw [sq_abs, mul_pow] at hcSq
    have hHSq := mul_le_mul_of_nonneg_left
      (norm_dirichlet_bilinear_sq_le_sum_entries (H x)) (sq_nonneg (K * ε))
    have hC : c ^ 2 ≤ M * ε ^ 2 * e x := by
      calc
        c ^ 2 ≤ (K * ε) ^ 2 * ‖H x‖ ^ 2 := hcSq
        _ ≤ (K * ε) ^ 2 * ((2 * n : ℝ) ^ 2 * e x) := hHSq
        _ = _ := by dsimp [M]; ring
    have hSplit : l x = g x + c := by
      dsimp only [c, l]
      rw [map_sub, _root_.sub_apply, hEq x hx]
      ring
    rw [hSplit]
    nlinarith only [hC, sq_nonneg (g x - c)]
  have hIntegral :
      (∫ x in unitBall n, (l x) ^ 2 ∂volume0 n) ≤
        2 * (∫ x in unitBall n, (g x) ^ 2 ∂volume0 n) +
          (2 * M * ε ^ 2) * ∫ x in unitBall n, e x ∂volume0 n := by
    have h := setIntegral_mono_on (hInt (hl.pow 2))
      (hInt (((hg.pow 2).const_mul 2).add (he.const_mul (2 * M * ε ^ 2))))
      measurableSet_ball hPoint
    simp only [Pi.add_apply, Pi.pow_apply] at h
    have hAdd := integral_add ((hInt (hg.pow 2)).const_mul 2)
      ((hInt he).const_mul (2 * M * ε ^ 2))
    simp only [Pi.pow_apply] at hAdd
    rw [hAdd, integral_const_mul, integral_const_mul] at h
    exact h
  have hEnergy : 0 ≤ ∫ x in unitBall n, e x ∂volume0 n :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hReference := hRef hq hqS hq0
  change (∫ x in unitBall n, e x ∂volume0 n) ≤
    C₀ * ∫ x in unitBall n, (l x) ^ 2 ∂volume0 n at hReference
  have hBound := hReference.trans (mul_le_mul_of_nonneg_left hIntegral hC₀)
  have hMargin := mul_le_mul_of_nonneg_right hSmall hEnergy
  change (∫ x in unitBall n, e x ∂volume0 n) ≤
    (4 * C₀) * ∫ x in unitBall n, (g x) ^ 2 ∂volume0 n
  nlinarith only [hBound, hMargin]

end KEBall

