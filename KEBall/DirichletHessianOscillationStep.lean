import KEBall.DirichletHessianAverageEstimate
import KEBall.DirichletHessianBallBounds
import KEBall.DirichletHessianTwoPoint
import KEBall.DirichletOscillationContraction

/-!
# Oscillation decay for the actual Hessian of a Dirichlet path limit

Every scalar function in this estimate is an entry of `fderiv ℝ G`.
The coefficient representation, log-determinant equation, and weak Harnack
are required for this same first jet.  The theorem does not assume Hessian
continuity, a classical second derivative, or a smooth limit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ComplexOrder NNReal

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

def dirichletHessianOscillation {n m : ℕ}
    (G : E n → E n →L[ℝ] ℝ) (v : Fin m → E n) (x₀ : E n) (R : ℝ) : ℝ :=
  ∑ i : Fin m,
    (essSup (fun x => fderiv ℝ G x (v i) (v i)) (volume.restrict (ball x₀ R)) -
      essInf (fun x => fderiv ℝ G x (v i) (v i)) (volume.restrict (ball x₀ R)))

theorem exists_dirichlet_hessian_oscillation_step_of_frame {n m : ℕ} (hn : 0 < n)
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    (hPos : ∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef)
    (hDet : ∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (g x))
    {c : ℝ} (hc : 0 < c) (hH : HasDirichletHessianWeakHarnack G c)
    (v : Fin m → E n) {l U : ℝ} (hl : 0 < l) (hU : 0 ≤ U)
    (hFrame : ∀ᵐ x ∂ν[n], ∃ β : Fin m → ℝ, (∀ k, l ≤ β k ∧ β k ≤ U) ∧
      dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x)) =
        ∑ k : Fin m, β k • rankOne ℝ (v k) (v k)) :
    ∃ θ C : ℝ, 0 ≤ θ ∧ θ < 1 ∧ 0 ≤ C ∧
      ∀ (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ R ⊆ unitBall n →
        dirichletHessianOscillation G v x₀ (R / 4) ≤
          θ * dirichletHessianOscillation G v x₀ R + C * R := by
  obtain ⟨Kg, Dg, hDg, hLipg, hExpg⟩ := exists_dirichlet_logDensity_lipschitz_exp_bound hg
  obtain ⟨H, hH0, hHV⟩ := exists_dirichlet_hessian_upper_defect_average hn hG hc hH
  choose a ha hEst using fun i : Fin m => hHV (v i)
  let A : ℝ := ∑ i : Fin m, a i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have haA (i : Fin m) : a i ≤ A := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  let N : ℝ := m
  let p : ℝ := (l + N * U) / l
  let K : ℝ := p * H
  let Esrc : ℝ := 2 * Dg * (Kg : ℝ)
  let T : ℝ := p * (N * (H * A))
  let S : ℝ := (N / l) * Esrc
  let C : ℝ := (T + S) / (1 + K)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp : 0 ≤ p := div_nonneg (add_nonneg hl.le (mul_nonneg hN hU)) hl.le
  have hK : 0 ≤ K := mul_nonneg hp hH0
  have hE : 0 ≤ Esrc := by dsimp only [Esrc]; positivity
  have hT : 0 ≤ T := mul_nonneg hp (mul_nonneg hN (mul_nonneg hH0 hA))
  have hS : 0 ≤ S := mul_nonneg (div_nonneg hN hl.le) hE
  have hDen : 0 < 1 + K := by linarith
  have hC : 0 ≤ C := div_nonneg (add_nonneg hT hS) hDen.le
  obtain ⟨hθ0, hθ1⟩ := dirichlet_oscillation_factor hK
  refine ⟨K / (1 + K), C, hθ0, hθ1, hC, ?_⟩
  intro x₀ R hR hR1 hBall
  let μ := dirichletBallProbability x₀ (R / 4)
  let q : Fin m → E n → ℝ := fun i x => fderiv ℝ G x (v i) (v i)
  let M : Fin m → ℝ := fun i => essSup (q i) (volume.restrict (ball x₀ R))
  let b : Fin m → ℝ := fun i => essInf (q i) (volume.restrict (ball x₀ R))
  have hR4 : 0 < R / 4 := by positivity
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_dirichletBallProbability x₀ hR4
  have hSmall : ball x₀ (R / 4) ⊆ ball x₀ R := ball_subset_ball (by linarith)
  have hBig : ball x₀ R ⊆ unitBall n := ball_subset_closedBall.trans hBall
  have hSmallBall : ball x₀ (R / 4) ⊆ unitBall n := hSmall.trans hBig
  have hBoundsBig (i : Fin m) : ∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ R),
      b i ≤ q i x ∧ q i x ≤ M i :=
    ae_dirichlet_hessianEntry_between_essential_bounds hG (v i) hBig
  have hBounds (i : Fin m) : ∀ᵐ x ∂μ, b i ≤ q i x ∧ q i x ≤ M i :=
    ae_dirichletBallProbability_iff.mpr
      (ae_restrict_of_ae_restrict_of_subset hSmall (hBoundsBig i))
  have hInt (i : Fin m) : Integrable (q i) μ :=
    (integrable_dirichletBallProbability_iff hR4).mpr
      (integrableOn_dirichlet_hessianEntry_ball hG (v i) hSmallBall)
  have hUpper (i : Fin m) : ∀ᵐ x ∂μ, q i x ≤ M i := (hBounds i).mono fun _ h => h.2
  have hCompare : ∀ j : Fin m, ∀ᵐ y ∂μ, ∀ᵐ x ∂μ,
      l * (q j x - q j y) ≤ U * (∑ i : Fin m, (M i - q i x)) + Esrc * R :=
    dirichlet_hessian_directional_twoPoint_bound hPos hDet v hl hFrame hLipg hDg.le hExpg
      hR hBall M hUpper
  have hHarnack (i : Fin m) : (∫ x, M i - q i x ∂μ) ≤
      H * (M i - essSup (q i) μ) + H * A * R ^ 2 := by
    have hM : ∀ᵐ x ∂(volume0 n).restrict (ball x₀ R), q i x ≤ M i :=
      ae_volume0_restrict_iff.mpr ((hBoundsBig i).mono fun _ h => h.2)
    have h := hEst i (M i) R x₀ hR hBall hM
    calc
      _ ≤ H * (M i - essSup (q i) μ + a i * R ^ 2) := h
      _ ≤ H * (M i - essSup (q i) μ + A * R ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (haA i) (sq_nonneg R))) hH0
      _ = _ := by ring
  have hContract := dirichlet_essential_oscillation_contraction q b M hInt hBounds hl hU hH0
    hCompare hHarnack
  simp only [Fintype.card_fin] at hContract
  have hOsc : (∑ i : Fin m, (essSup (q i) μ - essInf (q i) μ)) =
      dirichletHessianOscillation G v x₀ (R / 4) := by
    dsimp only [μ, q, dirichletHessianOscillation]
    simp only [essSup_dirichletBallProbability, essInf_dirichletBallProbability]
  change (∑ i : Fin m, (essSup (q i) μ - essInf (q i) μ)) ≤
    K / (1 + K) * dirichletHessianOscillation G v x₀ R +
      (p * (N * (H * A * R ^ 2)) + (N / l) * (Esrc * R)) / (1 + K) at hContract
  rw [hOsc] at hContract
  have hSquare : R ^ 2 ≤ R := by nlinarith
  have hErr : (p * (N * (H * A * R ^ 2)) + (N / l) * (Esrc * R)) / (1 + K) ≤ C * R := by
    calc
      _ = (T * R ^ 2 + S * R) / (1 + K) := by dsimp only [T, S]; ring
      _ ≤ (T * R + S * R) / (1 + K) :=
        div_le_div_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hSquare hT) le_rfl) hDen.le
      _ = _ := by dsimp only [C]; ring
  exact hContract.trans (add_le_add le_rfl hErr)

end KEBall
