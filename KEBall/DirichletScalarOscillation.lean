import KEBall.DirichletOscillationContraction
import KEBall.DirichletHessianOscillationAlgebra
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Uniform oscillation contraction for an actual continuous scalar family.
The functions need not be derivatives of an auxiliary first jet. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 700000

open Filter MeasureTheory Metric Set
open scoped BigOperators Topology

noncomputable section
namespace KEBall

private def scalarBallProbability {n : ℕ} (x : E n) (r : ℝ) : Measure (E n) :=
  (volume (ball x r))⁻¹ • volume.restrict (ball x r)

private theorem scalarBallProbability_isProbability {n : ℕ} (x : E n)
    {r : ℝ} (hr : 0 < r) : IsProbabilityMeasure (scalarBallProbability x r) := by
  constructor
  simp only [scalarBallProbability, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

private theorem ae_scalarBallProbability_iff {n : ℕ} {x : E n} {r : ℝ} {P : E n → Prop} :
    (∀ᵐ y ∂scalarBallProbability x r, P y) ↔
      ∀ᵐ y ∂(volume : Measure (E n)).restrict (ball x r), P y :=
  Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)

private theorem essSup_scalarBallProbability {n : ℕ} (x : E n) (r : ℝ) (f : E n → ℝ) :
    essSup f (scalarBallProbability x r) = essSup f (volume.restrict (ball x r)) := by
  exact essSup_ennreal_smul_measure (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne) f

private theorem essInf_scalarBallProbability {n : ℕ} (x : E n) (r : ℝ) (f : E n → ℝ) :
    essInf f (scalarBallProbability x r) = essInf f (volume.restrict (ball x r)) := by
  unfold essInf scalarBallProbability
  rw [Measure.ae_ennreal_smul_measure_eq (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)]

private theorem integrable_scalarBallProbability_iff {n : ℕ} {x : E n} {r : ℝ}
    (hr : 0 < r) {f : E n → ℝ} :
    Integrable f (scalarBallProbability x r) ↔ IntegrableOn f (ball x r) volume :=
  integrable_inv_smul_measure (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

private theorem scalar_continuousOn_nonneg_of_ae {n : ℕ} {μ : Measure (E n)}
    [μ.IsOpenPosMeasure] {s : Set (E n)} (hs : IsOpen s)
    {f : E n → ℝ} (hf : ContinuousOn f s)
    (ha : ∀ᵐ x ∂μ.restrict s, 0 ≤ f x) : ∀ x ∈ s, 0 ≤ f x := by
  have he : (fun x => max (f x) 0) =ᵐ[μ.restrict s] f :=
    ha.mono fun x hx => max_eq_left hx
  have hPoint := Measure.eqOn_open_of_ae_eq he hs (hf.sup continuousOn_const) hf
  intro x hx
  exact (le_max_right (f x) 0).trans_eq (hPoint hx)

def dirichletScalarFamilyOscillation {n m : ℕ} (q : Fin m → E n → ℝ)
    (x₀ : E n) (R : ℝ) : ℝ :=
  ∑ i : Fin m, (essSup (q i) (volume.restrict (ball x₀ R)) -
    essInf (q i) (volume.restrict (ball x₀ R)))

theorem boundedUnder_dirichlet_continuous_scalar_ball {n : ℕ} {q : E n → ℝ}
    (hq : ContinuousOn q (closedUnitBall n)) {x₀ : E n} {R : ℝ}
    (hBall : ball x₀ R ⊆ unitBall n) :
    IsBoundedUnder (· ≤ ·) (ae (volume.restrict (ball x₀ R))) q ∧
      IsBoundedUnder (· ≥ ·) (ae (volume.restrict (ball x₀ R))) q := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hq
  have hBound : ∀ᵐ x ∂(volume : Measure (E n)).restrict (ball x₀ R), -K ≤ q x ∧ q x ≤ K := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure (E n))) measurableSet_ball] with x hx
    have hKx := hK x (ball_subset_closedBall (hBall hx))
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hKx)
  exact ⟨⟨K, hBound.mono fun _ h => h.2⟩, ⟨-K, hBound.mono fun _ h => h.1⟩⟩

theorem dirichlet_continuous_scalar_between_essential_bounds {n : ℕ} {q : E n → ℝ}
    (hq : ContinuousOn q (closedUnitBall n)) {x₀ : E n} {R : ℝ}
    (hBall : ball x₀ R ⊆ unitBall n) {x : E n} (hx : x ∈ ball x₀ R) :
    essInf q (volume.restrict (ball x₀ R)) ≤ q x ∧
      q x ≤ essSup q (volume.restrict (ball x₀ R)) := by
  obtain ⟨hHi, hLo⟩ := boundedUnder_dirichlet_continuous_scalar_ball hq hBall
  have hqB := hq.mono (hBall.trans ball_subset_closedBall)
  have hLower := scalar_continuousOn_nonneg_of_ae (μ := (volume : Measure (E n)))
    isOpen_ball (hqB.sub continuousOn_const)
    ((ae_essInf_le hLo).mono fun _ h => sub_nonneg.mpr h)
  have hUpper := scalar_continuousOn_nonneg_of_ae (μ := (volume : Measure (E n)))
    isOpen_ball (continuousOn_const.sub hqB)
    ((ae_le_essSup hHi).mono fun _ h => sub_nonneg.mpr h)
  exact ⟨sub_nonneg.mp (hLower x hx), sub_nonneg.mp (hUpper x hx)⟩

theorem dirichlet_defect_mean_le_essential_sup {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {q : X → ℝ}
    (hLo : IsBoundedUnder (· ≥ ·) (ae μ) q)
    {H M A I : ℝ} (hH : 0 < H)
    (hMean : ∀ᵐ y ∂μ, I ≤ H * (M - q y + A)) :
    I ≤ H * (M - essSup q μ + A) := by
  have hUpper : ∀ᵐ y ∂μ, q y ≤ M + A - I / H := by
    filter_upwards [hMean] with y hy
    have he : I / H ≤ M - q y + A :=
      (div_le_iff₀ hH).mpr (by simpa only [mul_comm H] using hy)
    linarith only [he]
  have hs := essSup_le_of_ae_le _ hUpper hLo.isCoboundedUnder_le
  have hm := mul_le_mul_of_nonneg_left hs hH.le
  have hc : I / H * H = I := div_mul_cancel₀ I hH.ne'
  nlinarith only [hm, hc]

theorem exists_uniform_dirichlet_scalar_oscillation_step {n m : ℕ} {J : Type*}
    (q : J → Fin m → E n → ℝ)
    (hq : ∀ j i, ContinuousOn (q j i) (closedUnitBall n))
    {l U E₀ H A : ℝ} (hl : 0 < l) (hU : 0 ≤ U) (hE : 0 ≤ E₀)
    (hH : 0 < H) (hA : 0 ≤ A)
    (hPair : ∀ j x, x ∈ unitBall n → ∀ y, y ∈ unitBall n →
      ∃ β : Fin m → ℝ, (∀ i, l ≤ β i ∧ β i ≤ U) ∧
        (∑ i : Fin m, β i * (q j i x - q j i y)) ≤ E₀ * dist x y)
    (hHarnack : ∀ j i (M : ℝ) (x₀ : E n) (R : ℝ),
      0 < R → closedBall x₀ R ⊆ unitBall n →
      (∀ x ∈ ball x₀ R, q j i x ≤ M) →
      ∀ y ∈ ball x₀ (R / 4),
        (∫ x, M - q j i x ∂((volume (ball x₀ (R / 4)))⁻¹ •
          volume.restrict (ball x₀ (R / 4)))) ≤
          H * (M - q j i y + A * R ^ 2)) :
    ∃ θ C : ℝ, 0 ≤ θ ∧ θ < 1 ∧ 0 ≤ C ∧
      ∀ j (x₀ : E n) (R : ℝ), 0 < R → R ≤ 1 → closedBall x₀ R ⊆ unitBall n →
        dirichletScalarFamilyOscillation (q j) x₀ (R / 4) ≤
          θ * dirichletScalarFamilyOscillation (q j) x₀ R + C * R := by
  let N : ℝ := m
  let p : ℝ := (l + N * U) / l
  let K : ℝ := p * H
  let T : ℝ := p * (N * (H * A))
  let S : ℝ := (N / l) * (2 * E₀)
  let C : ℝ := (T + S) / (1 + K)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp : 0 ≤ p := div_nonneg (add_nonneg hl.le (mul_nonneg hN hU)) hl.le
  have hK : 0 ≤ K := mul_nonneg hp hH.le
  have hT : 0 ≤ T := mul_nonneg hp (mul_nonneg hN (mul_nonneg hH.le hA))
  have hS : 0 ≤ S := mul_nonneg (div_nonneg hN hl.le) (by positivity)
  have hDen : 0 < 1 + K := by linarith
  have hC : 0 ≤ C := div_nonneg (add_nonneg hT hS) hDen.le
  obtain ⟨hθ0, hθ1⟩ := dirichlet_oscillation_factor hK
  refine ⟨K / (1 + K), C, hθ0, hθ1, hC, ?_⟩
  intro j x₀ R hR hR1 hBall
  let μ := scalarBallProbability x₀ (R / 4)
  let M : Fin m → ℝ := fun i => essSup (q j i) (volume.restrict (ball x₀ R))
  let b : Fin m → ℝ := fun i => essInf (q j i) (volume.restrict (ball x₀ R))
  have hR4 : 0 < R / 4 := by positivity
  haveI : IsProbabilityMeasure μ := scalarBallProbability_isProbability x₀ hR4
  have hSmall : ball x₀ (R / 4) ⊆ ball x₀ R := ball_subset_ball (by linarith)
  have hBig : ball x₀ R ⊆ unitBall n := ball_subset_closedBall.trans hBall
  have hSmallBall : ball x₀ (R / 4) ⊆ unitBall n := hSmall.trans hBig
  have hBoundsBig (i : Fin m) (x : E n) (hx : x ∈ ball x₀ R) :
      b i ≤ q j i x ∧ q j i x ≤ M i :=
    dirichlet_continuous_scalar_between_essential_bounds (hq j i) hBig hx
  have hMem : ∀ᵐ x ∂μ, x ∈ ball x₀ (R / 4) :=
    ae_scalarBallProbability_iff.mpr (ae_restrict_mem measurableSet_ball)
  have hBounds (i : Fin m) : ∀ᵐ x ∂μ, b i ≤ q j i x ∧ q j i x ≤ M i := by
    filter_upwards [hMem] with x hx
    exact hBoundsBig i x (hSmall hx)
  have hInt (i : Fin m) : Integrable (q j i) μ := by
    apply (integrable_scalarBallProbability_iff hR4).mpr
    exact ((hq j i).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      (hSmallBall.trans ball_subset_closedBall)
  have hCompare : ∀ k : Fin m, ∀ᵐ y ∂μ, ∀ᵐ x ∂μ,
      l * (q j k x - q j k y) ≤ U * (∑ i : Fin m, (M i - q j i x)) + (2 * E₀) * R := by
    intro k
    filter_upwards [hMem] with y hy
    filter_upwards [hMem] with x hx
    obtain ⟨β, hβ, hLinear⟩ := hPair j x (hSmallBall hx) y (hSmallBall hy)
    have hDist : dist x y ≤ 2 * R := by
      have hxR := mem_ball.mp (hSmall hx)
      have hyR := mem_ball.mp (hSmall hy)
      have ht := dist_triangle x x₀ y
      rw [dist_comm x₀ y] at ht
      linarith only [hxR, hyR, ht]
    have hSource : E₀ * dist x y ≤ (2 * E₀) * R := by
      calc
        _ ≤ E₀ * (2 * R) := mul_le_mul_of_nonneg_left hDist hE
        _ = _ := by ring
    exact dirichlet_directional_defect_comparison (fun i => q j i x) (fun i => q j i y)
      M β hl (by positivity : 0 ≤ (2 * E₀) * R) hβ
      (fun i => (hBoundsBig i x (hSmall hx)).2)
      (fun i => (hBoundsBig i y (hSmall hy)).2) (hLinear.trans hSource) k
  have hAvg (i : Fin m) : (∫ x, M i - q j i x ∂μ) ≤
      H * (M i - essSup (q j i) μ) + H * A * R ^ 2 := by
    have hLo : IsBoundedUnder (· ≥ ·) (ae μ) (q j i) :=
      ⟨b i, (hBounds i).mono fun _ h => h.1⟩
    have hMean : ∀ᵐ y ∂μ, (∫ x, M i - q j i x ∂μ) ≤
        H * (M i - q j i y + A * R ^ 2) := by
      filter_upwards [hMem] with y hy
      exact hHarnack j i (M i) x₀ R hR hBall
        (fun x hx => (hBoundsBig i x hx).2) y hy
    exact (dirichlet_defect_mean_le_essential_sup hLo hH hMean).trans_eq (by ring)
  have hContract := dirichlet_essential_oscillation_contraction (q j) b M hInt hBounds
    hl hU hH.le hCompare hAvg
  simp only [Fintype.card_fin] at hContract
  have hOsc : (∑ i : Fin m, (essSup (q j i) μ - essInf (q j i) μ)) =
      dirichletScalarFamilyOscillation (q j) x₀ (R / 4) := by
    dsimp only [μ, dirichletScalarFamilyOscillation]
    simp only [essSup_scalarBallProbability, essInf_scalarBallProbability]
  change (∑ i : Fin m, (essSup (q j i) μ - essInf (q j i) μ)) ≤
    K / (1 + K) * dirichletScalarFamilyOscillation (q j) x₀ R +
      (p * (N * (H * A * R ^ 2)) + (N / l) * ((2 * E₀) * R)) / (1 + K) at hContract
  rw [hOsc] at hContract
  have hSquare : R ^ 2 ≤ R := by nlinarith
  have hErr : (p * (N * (H * A * R ^ 2)) + (N / l) * ((2 * E₀) * R)) / (1 + K) ≤ C * R := by
    calc
      _ = (T * R ^ 2 + S * R) / (1 + K) := by dsimp only [T, S]; ring
      _ ≤ (T * R + S * R) / (1 + K) :=
        div_le_div_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hSquare hT) le_rfl) hDen.le
      _ = _ := by dsimp only [C]; ring
  exact hContract.trans (add_le_add le_rfl hErr)

end KEBall
