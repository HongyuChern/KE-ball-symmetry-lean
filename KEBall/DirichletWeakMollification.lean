import KEBall.DirichletWeakSobolev
import PshLines.MollifierApproximation

/-! Weak derivatives, convergence and square-integral bounds for mollification on the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Convolution Distributions NNReal Topology
open PshLines (translationPairing contDiff_translationPairing fderiv_translationPairing
  mollify mollify_eq_convolution integrable_translationPairing ae_tendsto_mollify shrinkingBump shrinkingBump_rOut_le tendsto_shrinkingBump_rOut)

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private noncomputable def dirichletTranslatedTest {n : ℕ} {φ : E n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (x : E n)
    (hx : ∀ y ∈ tsupport φ, y + x ∈ unitBall n) : 𝓓B[n] := by
  let e := Homeomorph.addRight (-x)
  have he (y : E n) : e y = y - x := by simp [e, sub_eq_add_neg]
  refine ⟨fun y => φ (y - x), hφ.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
  · simpa only [Function.comp_def, he] using hs.comp_homeomorph e
  · rw [show (fun y => φ (y - x)) = φ ∘ e by simp only [Function.comp_def, he],
      tsupport_comp_eq_preimage]
    intro y hy
    change e y ∈ tsupport φ at hy
    change y ∈ unitBall n
    simpa only [he, sub_add_cancel] using hx (e y) hy

private theorem translationPairing_restrict_eq_indicator {n : ℕ} (f φ : E n → ℝ) :
    translationPairing ν[n] f φ = translationPairing (volume0 n) ((unitBall n).indicator f) φ := by
  funext x
  unfold translationPairing
  rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change (unitBall n).indicator (fun z => f z * φ (z - x)) y =
      (unitBall n).indicator f y * φ (y - x)
    by_cases hy : y ∈ unitBall n
    · rw [indicator_of_mem hy, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]

private theorem volume0_isAddHaarMeasure (n : ℕ) : (volume0 n).IsAddHaarMeasure := by
  unfold volume0
  exact Measure.IsAddHaarMeasure.smul _ (by positivity) ENNReal.ofReal_ne_top

/-- A translated kernel supported in the ball transfers a classical
directional derivative of its pairing to the given weak derivative. -/
theorem fderiv_dirichletTranslationPairing_of_weakDerivative {n : ℕ}
    {f F φ : E n → ℝ} (hf : MemLp f 2 ν[n])
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (d x : E n)
    (hx : ∀ y ∈ tsupport φ, y + x ∈ unitBall n)
    (he : ∀ ψ : 𝓓B[n], (∫ y, ψ y * F y ∂ν[n]) =
      -(∫ y, fderiv ℝ (ψ : E n → ℝ) y d * f y ∂ν[n])) :
    fderiv ℝ (translationPairing ν[n] f φ) x d = translationPairing ν[n] F φ x := by
  let ψ := dirichletTranslatedTest hφ hs x hx
  have hψ (y : E n) : fderiv ℝ (ψ : E n → ℝ) y d = fderiv ℝ φ (y - x) d := by
    have h := (hφ.differentiable (by simp) (y - x)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const x)
    exact congrArg (fun L : E n →L[ℝ] ℝ => L d) h.fderiv
  let : (volume0 n).IsAddLeftInvariant := by
    unfold volume0
    infer_instance
  have hf' : MemLp ((unitBall n).indicator f) 2 (volume0 n) :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr hf
  rw [translationPairing_restrict_eq_indicator f φ,
    fderiv_translationPairing (hf'.locallyIntegrable (by norm_num)) hs (hφ.of_le (by simp)),
    ← translationPairing_restrict_eq_indicator]
  have hp := he ψ
  simp_rw [hψ, mul_comm (fderiv ℝ φ _ d) (f _)] at hp
  change (∫ y, φ (y - x) * F y ∂ν[n]) =
    -(∫ y, f y * fderiv ℝ φ (y - x) d ∂ν[n]) at hp
  simpa only [translationPairing, mul_comm (F _) (φ _)] using hp.symm

/-- On any open region where the translates fit inside the unit ball,
a weak derivative represented by a function becomes the corresponding
iterated derivative of the smooth pairing. -/
theorem iteratedLineDerivative_dirichletTranslationPairing {n : ℕ}
    {f F φ : E n → ℝ} {s : Set (E n)} (hs : IsOpen s)
    (hφ : ContDiff ℝ ∞ φ) (hφS : HasCompactSupport φ)
    (hInside : ∀ x ∈ s, ∀ y ∈ tsupport φ, y + x ∈ unitBall n)
    (ds : List (E n)) (hf : HasDirichletWeakDerivativesL2 f ds.length)
    (he : ∀ ψ : 𝓓B[n], dirichletWeakDerivativeTest f ds ψ = ∫ x, ψ x * F x ∂ν[n]) :
    EqOn (ds.foldr (fun d C x => fderiv ℝ C x d) (translationPairing ν[n] f φ))
      (translationPairing ν[n] F φ) s := by
  induction ds generalizing F with
  | nil =>
      intro x hx
      have h := he (dirichletTranslatedTest hφ hφS x (hInside x hx))
      change (∫ y, φ (y - x) * f y ∂ν[n]) = ∫ y, φ (y - x) * F y ∂ν[n] at h
      simpa only [translationPairing, List.foldr_nil, mul_comm (F _) (φ _),
        mul_comm (f _) (φ _)] using h
  | cons d ds ih =>
      obtain ⟨G, hG, heG⟩ := hf.2 ds (by simp)
      have hf' : HasDirichletWeakDerivativesL2 f ds.length :=
        ⟨hf.1, fun es h => hf.2 es (h.trans (by simp))⟩
      have hEq := ih hf' heG
      have hWeak (ψ : 𝓓B[n]) : (∫ y, ψ y * F y ∂ν[n]) =
          -(∫ y, fderiv ℝ (ψ : E n → ℝ) y d * G y ∂ν[n]) := by
        rw [← he ψ, dirichletWeakDerivativeTest, heG]
        rfl
      intro x hx
      have hNear : _ =ᶠ[𝓝 x] translationPairing ν[n] G φ :=
        Filter.Eventually.mono (hs.mem_nhds hx) fun y hy => hEq hy
      simp only [List.foldr_cons]
      rw [hNear.fderiv_eq]
      exact fderiv_dirichletTranslationPairing_of_weakDerivative hG
        hφ hφS d x (hInside x hx) hWeak

/-- Normalized shrinking kernels converge almost everywhere to a Dirichlet
L² density, using its zero extension as the ambient density. -/
theorem ae_tendsto_dirichletTranslationPairing {n : ℕ} {f : E n → ℝ}
    (hf : MemLp f 2 ν[n]) (R : ℝ) (hR : 0 < R) :
    ∀ᵐ x ∂ν[n], Tendsto (fun j => translationPairing ν[n] f
      ((shrinkingBump R hR j).normed (volume0 n)) x) atTop (𝓝 (f x)) := by
  have := volume0_isAddHaarMeasure n
  have hf' : MemLp ((unitBall n).indicator f) 2 (volume0 n) :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr hf
  have h := ae_tendsto_mollify (volume0 n) (hf'.locallyIntegrable (by norm_num)) R hR
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hBall
  rw [indicator_of_mem hBall] at hx
  simpa only [mollify, ← translationPairing_restrict_eq_indicator] using hx

/-- On any fixed smaller ball, the derivatives of the shrinking-kernel
approximants converge almost everywhere to their weak representatives. -/
theorem ae_tendsto_iteratedLineDerivative_dirichletTranslationPairing {n : ℕ}
    {f F : E n → ℝ} (ds : List (E n)) (hf : HasDirichletWeakDerivativesL2 f ds.length)
    (hF : MemLp F 2 ν[n])
    (he : ∀ ψ : 𝓓B[n], dirichletWeakDerivativeTest f ds ψ = ∫ x, ψ x * F x ∂ν[n])
    (R : ℝ) (hR : 0 < R) {r : ℝ} (hr : r < 1) :
    ∀ᵐ x ∂ν[n], x ∈ ball (0 : E n) r → Tendsto
      (fun j => ds.foldr (fun d C y => fderiv ℝ C y d)
        (translationPairing ν[n] f ((shrinkingBump R hR j).normed (volume0 n))) x)
      atTop (𝓝 (F x)) := by
  have hSmall : ∀ᶠ j in atTop, (shrinkingBump (E := E n) R hR j).rOut < 1 - r :=
    (tendsto_shrinkingBump_rOut R hR).eventually (gt_mem_nhds (sub_pos.mpr hr))
  filter_upwards [ae_tendsto_dirichletTranslationPairing hF R hR] with x hx hBall
  apply hx.congr'
  filter_upwards [hSmall] with j hj
  let φ := shrinkingBump (E := E n) R hR j
  have hInside (z : E n) (hz : z ∈ ball (0 : E n) r)
      (y : E n) (hy : y ∈ tsupport (φ.normed (volume0 n))) : y + z ∈ unitBall n := by
    rw [φ.tsupport_normed_eq, mem_closedBall, dist_zero_right] at hy
    rw [mem_ball, dist_zero_right] at hz
    apply mem_ball_zero_iff.mpr
    exact (norm_add_le _ _).trans_lt (by linarith)
  exact (iteratedLineDerivative_dirichletTranslationPairing isOpen_ball φ.contDiff_normed
    φ.hasCompactSupport_normed hInside ds hf he hBall).symm

private theorem sq_mollify_le_mollify_sq {n : ℕ} {f : E n → ℝ}
    (hf : MemLp f 2 (volume0 n)) (φ : ContDiffBump (0 : E n)) (x : E n) :
    mollify (volume0 n) f φ x ^ 2 ≤ mollify (volume0 n) (fun y => f y ^ 2) φ x := by
  have := volume0_isAddHaarMeasure n
  have hRight : (volume0 n).IsAddRightInvariant := by
    unfold volume0
    infer_instance
  let μ := volume0 n
  let k (y : E n) := φ.normed μ (y - x)
  let m := mollify μ f φ x
  have hk : Integrable k μ := φ.integrable_normed.comp_sub_right x
  have h₀ : (∫ y, k y ∂μ) = 1 := by
    exact (integral_sub_right_eq_self (f := φ.normed μ) (μ := μ) x).trans φ.integral_normed
  have h₁ : Integrable (fun y => f y * k y) μ :=
    integrable_translationPairing (hf.locallyIntegrable (by norm_num))
      φ.hasCompactSupport_normed φ.continuous_normed x
  have h₂ : Integrable (fun y => f y ^ 2 * k y) μ :=
    integrable_translationPairing hf.integrable_sq.locallyIntegrable
      φ.hasCompactSupport_normed φ.continuous_normed x
  have hExpand (y : E n) : (f y - m) ^ 2 * k y =
      f y ^ 2 * k y - (2 * m) * (f y * k y) + m ^ 2 * k y := by ring
  have hnon : 0 ≤ ∫ y, (f y - m) ^ 2 * k y ∂μ :=
    integral_nonneg fun y => mul_nonneg (sq_nonneg _) (φ.nonneg_normed (y - x))
  simp_rw [hExpand] at hnon
  have hSub : Integrable (fun y => f y ^ 2 * k y - 2 * m * (f y * k y)) μ :=
    h₂.sub (h₁.const_mul (2 * m))
  rw [integral_add hSub (hk.const_mul (m ^ 2)),
    integral_sub h₂ (h₁.const_mul (2 * m)), integral_const_mul, integral_const_mul,
    h₀, mul_one] at hnon
  change 0 ≤ mollify μ (fun y => f y ^ 2) φ x - (2 * m) * m + m ^ 2 at hnon
  change m ^ 2 ≤ _
  linarith only [hnon]

/-- Normalized mollification does not increase the square integral on
the whole space. -/
theorem integral_sq_mollify_le {n : ℕ} {f : E n → ℝ}
    (hf : MemLp f 2 (volume0 n)) (φ : ContDiffBump (0 : E n)) :
    Integrable (fun x => mollify (volume0 n) f φ x ^ 2) (volume0 n) ∧
      (∫ x, mollify (volume0 n) f φ x ^ 2 ∂volume0 n) ≤ ∫ x, f x ^ 2 ∂volume0 n := by
  have := volume0_isAddHaarMeasure n
  have hRight : (volume0 n).IsAddRightInvariant := by
    unfold volume0
    infer_instance
  let μ := volume0 n
  have hC : Continuous (mollify μ f φ) :=
    (PshLines.contDiff_mollify μ (hf.locallyIntegrable (by norm_num)) φ
      (n := 0)).continuous
  have hConv := φ.integrable_normed.integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hf.integrable_sq
  have hInt : Integrable (mollify μ (fun y => f y ^ 2) φ) μ := by
    rwa [mollify_eq_convolution]
  have hI : Integrable (fun x => mollify μ f φ x ^ 2) μ := by
    apply hInt.mono' (hC.pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_mollify_le_mollify_sq hf φ x
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ x, mollify μ (fun y => f y ^ 2) φ x ∂μ :=
      integral_mono hI hInt (sq_mollify_le_mollify_sq hf φ)
    _ = _ := by
      rw [mollify_eq_convolution, integral_convolution _ φ.integrable_normed hf.integrable_sq,
        φ.integral_normed]
      simp

/-- If the translated kernels fit in an open subset of the ball, the
square integral of any iterated derivative there is bounded by that of
its weak representative on the unit ball. -/
theorem integral_sq_iteratedLineDerivative_dirichletTranslationPairing_le {n : ℕ}
    {f F : E n → ℝ} {s : Set (E n)} (hs : IsOpen s)
    (φ : ContDiffBump (0 : E n))
    (hInside : ∀ x ∈ s, ∀ y ∈ tsupport (φ.normed (volume0 n)), y + x ∈ unitBall n)
    (ds : List (E n)) (hf : HasDirichletWeakDerivativesL2 f ds.length)
    (hF : MemLp F 2 ((volume0 n).restrict (unitBall n)))
    (he : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ), dirichletWeakDerivativeTest f ds ψ =
      ∫ x in unitBall n, ψ x * F x ∂volume0 n) :
    (∫ x in s, (ds.foldr (fun d C y => fderiv ℝ C y d)
      (translationPairing ((volume0 n).restrict (unitBall n)) f (φ.normed (volume0 n)))) x ^ 2
      ∂volume0 n) ≤ ∫ x in unitBall n, F x ^ 2 ∂volume0 n := by
  let μ := volume0 n
  let I := (unitBall n).indicator F
  have hF' : MemLp I 2 μ := (memLp_indicator_iff_restrict measurableSet_ball).mpr hF
  have : μ.IsAddHaarMeasure := volume0_isAddHaarMeasure n
  have hEq := iteratedLineDerivative_dirichletTranslationPairing hs φ.contDiff_normed
    φ.hasCompactSupport_normed hInside ds hf he
  have hBound := integral_sq_mollify_le hF' φ
  calc
    _ = ∫ x in s, mollify μ I φ x ^ 2 ∂μ := by
      apply setIntegral_congr_fun hs.measurableSet
      intro x hx
      dsimp only
      rw [hEq hx, translationPairing_restrict_eq_indicator]
      rfl
    _ ≤ ∫ x, mollify μ I φ x ^ 2 ∂μ := by
      exact setIntegral_le_integral hBound.1 (Eventually.of_forall fun _ => sq_nonneg _)
    _ ≤ ∫ x, I x ^ 2 ∂μ := hBound.2
    _ = _ := by
      rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change I x ^ 2 = (unitBall n).indicator (fun y => F y ^ 2) x
        by_cases hx : x ∈ unitBall n <;> simp [I, hx]

end KEBall
