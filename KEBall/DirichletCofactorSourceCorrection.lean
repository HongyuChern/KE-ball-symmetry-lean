import KEBall.DirichletWeakDivergenceLimit
import KEBall.DirichletWholeCutoff

/-!
# Removing bounded scalar forcing from the cofactor supersolution

The S055 source was compiled and repaired with Lean 4.33.1 in S056.
Its hypotheses keep the actual distributional column identity, rather than
assuming differentiability of the coefficient field.

The real dimension is `2 * n`. A concave quadratic with coefficient
`F / (4 * n * c)` absorbs a scalar source bounded below by `-F` when the
ellipticity lower bound is `c`. This is the source/scale adapter needed before
one can apply a homogeneous weak Harnack theorem. No weak Harnack theorem is
claimed in this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ContDiff Distributions Gradient Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- The Euclidean trace in the fixed real orthonormal basis. -/
def dirichletRealCoefficientTrace {n : ℕ} (A : E n →L[ℝ] E n) : ℝ :=
  ∑ i : Fin (2 * n), inner ℝ (A (e[n] i)) (e[n] i)

/-- Applying an essentially bounded field to an L² field stays in L². -/
theorem memLp_dirichletCoefficient_apply {n : ℕ}
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    {V : E n → E n} (hV : MemLp V 2 ν[n]) :
    MemLp (fun x => A x (V x)) 2 ν[n] := by
  have h := dirichletCoefficientAction_ae hA (hV.toLp V)
  apply (Lp.memLp (dirichletCoefficientAction hA (hV.toLp V))).ae_eq
  filter_upwards [h, MemLp.coeFn_toLp hV] with x hx hy
  rw [hx, hy]

/-- The rough-coefficient pairing is integrable for genuine L² fields. -/
theorem integrable_dirichletCoefficient_pairing_of_memLp {n : ℕ}
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    {V W : E n → E n} (hV : MemLp V 2 ν[n]) (hW : MemLp W 2 ν[n]) :
    Integrable (fun x => inner ℝ (A x (V x)) (W x)) ν[n] := by
  have hAV := memLp_dirichletCoefficient_apply hA hV
  apply (MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (hAV.toLp (fun x => A x (V x))) (hW.toLp W)).congr
  filter_upwards [MemLp.coeFn_toLp hAV, MemLp.coeFn_toLp hW] with x hx hy
  rw [hx, hy]

theorem memLp_dirichletRealCoefficientTrace {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) :
    MemLp (fun x => dirichletRealCoefficientTrace (A x)) 2 ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  exact memLp_finsetSum Finset.univ fun i _ =>
    (memLp_dirichletCoefficient_apply hA (memLp_const (e[n] i))).inner_const (e[n] i)

theorem realDimension_mul_le_dirichletRealCoefficientTrace {n : ℕ}
    {A : E n →L[ℝ] E n} {c : ℝ}
    (hE : ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    (2 * n : ℝ) * c ≤ dirichletRealCoefficientTrace A := by
  calc
    _ = ∑ _ : Fin (2 * n), c := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      simpa only [OrthonormalBasis.norm_eq_one, one_pow, mul_one] using hE (e[n] i)

/-- Distributional column divergence gives the exact flux of the affine
radial vector field. In particular, no derivative of a merely measurable
coefficient field is introduced. -/
theorem integral_dirichletCoefficient_affine_eq_neg_trace {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    (hDiv : ∀ (v : E n) (φ : 𝓓B[n]),
      (∫ x, inner ℝ (A x v) (∇ (φ : E n → ℝ) x) ∂ν[n]) = 0)
    (x₀ : E n) (ψ : 𝓓B[n]) :
    (∫ x, inner ℝ (A x (x - x₀)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
      -(∫ x, ψ x * dirichletRealCoefficientTrace (A x) ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let b := e[n]
  let c (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (x - x₀)
  have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) :=
    (innerSL ℝ (b i)).contDiff.comp (contDiff_id.sub contDiff_const)
  have hgc (i : Fin (2 * n)) (x : E n) : ∇ (c i) x = b i := by
    have hD := (innerSL ℝ (b i)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const x₀)
    change HasFDerivAt (c i) _ x at hD
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left, hD.fderiv]
    rfl
  have hGrad : MemLp (∇ (ψ : E n → ℝ)) 2 ν[n] :=
    memLp_continuousOn_dirichletBall hn
      (contDiff_euclideanGradient ψ.contDiff).continuous.continuousOn
  let d (i : Fin (2 * n)) (x : E n) := inner ℝ (A x (b i)) (b i)
  have hd (i : Fin (2 * n)) : MemLp (d i) 2 ν[n] :=
    (memLp_dirichletCoefficient_apply hA (memLp_const (b i))).inner_const (b i)
  have hI (i : Fin (2 * n)) : Integrable (fun x => ψ x * d i x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn (hd i)).integrable
      (by norm_num)
  have hJ (i : Fin (2 * n)) : Integrable (fun x =>
      c i x * inner ℝ (A x (b i)) (∇ (ψ : E n → ℝ) x)) ν[n] := by
    have hV : MemLp (fun x => c i x • b i) 2 ν[n] :=
      memLp_continuousOn_dirichletBall hn ((hc i).smul contDiff_const).continuous.continuousOn
    simpa only [map_smul, real_inner_smul_left] using
      integrable_dirichletCoefficient_pairing_of_memLp hA hV hGrad
  have hJi (i : Fin (2 * n)) :
      (∫ x, c i x * inner ℝ (A x (b i)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
        -(∫ x, ψ x * d i x ∂ν[n]) := by
    let φ := dirichletTestMul ψ (hc i)
    have h := hDiv (b i) φ
    have he (x : E n) : inner ℝ (A x (b i)) (∇ (φ : E n → ℝ) x) =
        ψ x * d i x + c i x * inner ℝ (A x (b i)) (∇ (ψ : E n → ℝ) x) := by
      change inner ℝ (A x (b i)) (∇ (fun y => ψ y * c i y) x) = _
      rw [gradient_euclideanCutoff_mul (ψ.contDiff.differentiable (by simp) x)
        ((hc i).differentiable (by simp) x), hgc]
      simp only [inner_add_right, real_inner_smul_right, d]
    simp_rw [he] at h
    rw [integral_add (hI i) (hJ i)] at h
    linarith only [h]
  have hExpand (x : E n) :
      inner ℝ (A x (x - x₀)) (∇ (ψ : E n → ℝ) x) =
        ∑ i : Fin (2 * n), c i x * inner ℝ (A x (b i)) (∇ (ψ : E n → ℝ) x) := by
    calc
      _ = inner ℝ (A x (∑ i, c i x • b i)) (∇ (ψ : E n → ℝ) x) := by
        rw [show (∑ i, c i x • b i) = x - x₀ from b.sum_repr' (x - x₀)]
      _ = _ := by simp only [map_sum, map_smul, sum_inner, real_inner_smul_left]
  simp_rw [hExpand]
  rw [integral_finsetSum _ (fun i _ => hJ i)]
  simp_rw [hJi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hI i)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [dirichletRealCoefficientTrace, Finset.mul_sum, d, b]

/-- The explicit source correction on a ball of radius `R`. -/
def dirichletSourceQuadratic {n : ℕ} (a R : ℝ) (x₀ x : E n) : ℝ :=
  a * (R ^ 2 - ‖x - x₀‖ ^ 2)

theorem contDiff_dirichletSourceQuadratic {n : ℕ} (a R : ℝ) (x₀ : E n) :
    ContDiff ℝ ∞ (dirichletSourceQuadratic a R x₀) :=
  contDiff_const.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)))

theorem gradient_dirichletSourceQuadratic {n : ℕ}
    (a R : ℝ) (x₀ x : E n) :
    ∇ (dirichletSourceQuadratic a R x₀) x = -(2 * a) • (x - x₀) := by
  have hD := ((((hasFDerivAt_id x).sub_const x₀).norm_sq).const_sub (R ^ 2)).const_mul a
  change HasFDerivAt (dirichletSourceQuadratic a R x₀) _ x at hD
  simp only [id_eq] at hD
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, hD.fderiv, real_inner_smul_left]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul]
  ring

theorem dirichletSourceQuadratic_bounds {n : ℕ} {a R : ℝ} (ha : 0 ≤ a)
    (hR : 0 ≤ R) {x₀ x : E n} (hx : x ∈ closedBall x₀ R) :
    0 ≤ dirichletSourceQuadratic a R x₀ x ∧
      dirichletSourceQuadratic a R x₀ x ≤ a * R ^ 2 := by
  have hx' : ‖x - x₀‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hs := pow_le_pow_left₀ (norm_nonneg (x - x₀)) hx' 2
  constructor
  · exact mul_nonneg ha (sub_nonneg.mpr hs)
  · exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) ha

theorem integral_dirichletSourceQuadratic_flux {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    (hDiv : ∀ (v : E n) (φ : 𝓓B[n]),
      (∫ x, inner ℝ (A x v) (∇ (φ : E n → ℝ) x) ∂ν[n]) = 0)
    (a R : ℝ) (x₀ : E n) (ψ : 𝓓B[n]) :
    (∫ x, inner ℝ (A x (∇ (dirichletSourceQuadratic a R x₀) x))
      (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
        2 * a * ∫ x, ψ x * dirichletRealCoefficientTrace (A x) ∂ν[n] := by
  simp_rw [gradient_dirichletSourceQuadratic, map_smul, real_inner_smul_left]
  rw [integral_const_mul, integral_dirichletCoefficient_affine_eq_neg_trace hn hA hDiv]
  ring

/-- A bounded-source upper defect becomes a homogeneous supersolution
after adding the explicit quadratic. `F` is the actual weak gradient of the
Hessian entry, and the corrected field is `-F + grad(q)`.

The statement is about the weak inequality; identifying this field as the
weak gradient of `M - h + q` is a separate linear weak-derivative identity.
No regularity of `A` beyond `L∞` and its distributional column identity is used. -/
theorem upper_defect_quadraticCorrection_homogeneous {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    (hDiv : ∀ (v : E n) (φ : 𝓓B[n]),
      (∫ x, inner ℝ (A x v) (∇ (φ : E n → ℝ) x) ∂ν[n]) = 0)
    {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {F : E n → E n} (hF : MemLp F 2 ν[n])
    {s : E n → ℝ} (hs : MemLp s 2 ν[n])
    (hLower : ∀ᵐ x ∂ν[n], -B ≤ s x)
    (hSub : ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
      (∫ x, inner ℝ (A x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) ≤
        -(∫ x, ψ x * s x ∂ν[n]))
    (R : ℝ) (x₀ : E n) (ψ : 𝓓B[n]) (hψ : ∀ x ∈ unitBall n, 0 ≤ ψ x) :
    0 ≤ ∫ x, inner ℝ
      (A x (-F x + ∇ (dirichletSourceQuadratic (B / (4 * n * c)) R x₀) x))
        (∇ (ψ : E n → ℝ) x) ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let a : ℝ := B / (4 * n * c)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ a := div_nonneg hB (by positivity)
  have hScale : (2 * a) * ((2 * n : ℝ) * c) = B := by
    dsimp only [a]
    field_simp [ne_of_gt hnR, hc.ne']
    <;> ring
  have hG : MemLp (∇ (ψ : E n → ℝ)) 2 ν[n] :=
    memLp_continuousOn_dirichletBall hn
      (contDiff_euclideanGradient ψ.contDiff).continuous.continuousOn
  have hQ : MemLp (∇ (dirichletSourceQuadratic a R x₀)) 2 ν[n] :=
    memLp_continuousOn_dirichletBall hn
      (contDiff_euclideanGradient (contDiff_dirichletSourceQuadratic a R x₀)).continuous.continuousOn
  have hIF := integrable_dirichletCoefficient_pairing_of_memLp hA hF hG
  have hIQ := integrable_dirichletCoefficient_pairing_of_memLp hA hQ hG
  have hIs : Integrable (fun x => ψ x * s x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hs).integrable (by norm_num)
  have hIt : Integrable (fun x => ψ x * dirichletRealCoefficientTrace (A x)) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn
      (memLp_dirichletRealCoefficientTrace hn hA)).integrable (by norm_num)
  have hBalance : 0 ≤ (∫ x, ψ x * s x ∂ν[n]) +
      2 * a * (∫ x, ψ x * dirichletRealCoefficientTrace (A x) ∂ν[n]) := by
    rw [← integral_const_mul, ← integral_add hIs (hIt.const_mul (2 * a))]
    apply integral_nonneg_of_ae
    filter_upwards [hEll, hLower, ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x he hl hx
    have ht := mul_le_mul_of_nonneg_left
      (realDimension_mul_le_dirichletRealCoefficientTrace he) (by positivity : 0 ≤ 2 * a)
    have hb : 0 ≤ s x + 2 * a * dirichletRealCoefficientTrace (A x) := by
      rw [hScale] at ht
      linarith only [hl, ht]
    change (0 : ℝ) ≤ ψ x * s x + 2 * a * (ψ x * dirichletRealCoefficientTrace (A x))
    calc
      0 ≤ ψ x * (s x + 2 * a * dirichletRealCoefficientTrace (A x)) :=
        mul_nonneg (hψ x hx) hb
      _ = ψ x * s x + 2 * a * (ψ x * dirichletRealCoefficientTrace (A x)) := by ring
  have hFlux : (∫ x, inner ℝ
      (A x (-F x + ∇ (dirichletSourceQuadratic a R x₀) x))
        (∇ (ψ : E n → ℝ) x) ∂ν[n]) =
      -(∫ x, inner ℝ (A x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) +
        2 * a * (∫ x, ψ x * dirichletRealCoefficientTrace (A x) ∂ν[n]) := by
    simp_rw [map_add, map_neg, inner_add_left, inner_neg_left]
    have hAdd := integral_add hIF.neg hIQ
    simp only [Pi.neg_apply] at hAdd
    rw [hAdd, integral_neg, integral_dirichletSourceQuadratic_flux hn hA hDiv]
  change 0 ≤ ∫ x, inner ℝ
    (A x (-F x + ∇ (dirichletSourceQuadratic a R x₀) x))
      (∇ (ψ : E n → ℝ) x) ∂ν[n]
  rw [hFlux]
  have h := hSub ψ hψ
  linarith only [h, hBalance]

end KEBall
