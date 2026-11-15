import KEBall.DirichletCofactorSourceCorrection

/-!
# The actual Hessian defect as a homogeneous weak supersolution

The S055 source was compiled and repaired with Lean 4.33.1 in S056.
The statements use the same Lipschitz first jet and L² weak third derivative
as the S053 path limit. In particular, the weak derivative is an explicit
field, not a totalized classical derivative of the nonsmooth Hessian.

This module supplies the input for weak Harnack. It does not assert weak
Harnack, Hessian oscillation decay, or boundary regularity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Distributions ENNReal Gradient NNReal Topology

noncomputable section

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "e[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- An explicitly chosen weak gradient, in the existing normalized measure. -/
def IsDirichletWeakGradient {n : ℕ} (f : E n → ℝ) (F : E n → E n) : Prop :=
  ∀ (j : Fin (2 * n)) (ψ : 𝓓B[n]),
    (∫ x, ψ x * inner ℝ (e[n] j) (F x) ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (e[n] j) * f x ∂ν[n])

/-- The directional Hessian of a Lipschitz first jet is essentially bounded.
This only gives bounded measurable Hessian entries; it gives no continuity. -/
theorem memLp_top_hessianEntry_of_lipschitz_firstJet {n : ℕ}
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v w : E n) :
    MemLp (fun x => fderiv ℝ G x v w) ⊤ ν[n] := by
  have hMeas : Measurable (fun x => fderiv ℝ G x v w) :=
    (ContinuousLinearMap.measurable_apply w).comp (measurable_fderiv_apply_const ℝ G v)
  apply memLp_top_of_bound hMeas.aestronglyMeasurable ((L : ℝ) * ‖v‖ * ‖w‖)
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  have hNorm : ‖fderiv ℝ G x‖ ≤ L :=
    norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hG
  exact ((fderiv ℝ G x v).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (((fderiv ℝ G x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hNorm (norm_nonneg _))) (norm_nonneg _))

/-- The actual log-density Hessian source has a finite bound on the closed
ball. The bound may depend on the fixed direction and the smooth density. -/
theorem exists_bound_logDensity_hessianSource {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) (t : ℝ) (v : E n) :
    MemLp (fun x => Real.exp (t * g x) * (t * realHessian g x v v)) 2 ν[n] ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedUnitBall n,
      |Real.exp (t * g x) * (t * realHessian g x v v)| ≤ B := by
  obtain ⟨U, hU, hSub, hgU⟩ := hg
  have hD : ContinuousOn (fun x => realHessian g x v v) U :=
    (((hgU.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞)
      (by simp)).clm_apply (contDiffOn_const (c := v)) |>.clm_apply
        (contDiffOn_const (c := v))).continuousOn
  have hS : ContinuousOn (fun x => Real.exp (t * g x) * (t * realHessian g x v v))
      (closedUnitBall n) :=
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hgU.continuousOn)).mul
      (continuousOn_const.mul hD)).mono hSub
  refine ⟨memLp_continuousOn_dirichletBall hn hS, ?_⟩
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hS
  exact ⟨|B|, abs_nonneg B, fun x hx => by
    simpa only [Real.norm_eq_abs] using (hB x hx).trans (le_abs_self B)⟩

/-- Smooth functions have their literal classical gradient as a weak
gradient, with the same orientation as the S053 Hessian-gradient identity. -/
theorem IsDirichletWeakGradient.of_smooth {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : ContDiff ℝ ∞ g) :
    IsDirichletWeakGradient g (∇ g) := by
  intro j ψ
  have h := integral_dirichletTest_fieldDerivative_mul_smooth hn ψ hg
    (contDiff_const (c := e[n] j))
  have hDiv (x : E n) :
      dirichletVectorDivergence e[n] (fun _ => e[n] j) x = 0 := by
    simp [dirichletVectorDivergence]
  dsimp only at h
  simp only [hDiv, mul_zero, add_zero] at h
  have hGrad (x : E n) : inner ℝ (e[n] j) (∇ g x) = fderiv ℝ g x (e[n] j) := by
    rw [real_inner_comm, inner_gradient_left]
  simp_rw [hGrad]
  linarith only [h]

/-- Subtracting a weak function from a smooth function preserves the
explicit weak-gradient witness. Integrability is proved before splitting
either of the two integrals. -/
theorem IsDirichletWeakGradient.smooth_sub {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} {F : E n → E n}
    (hWeak : IsDirichletWeakGradient f F) (hf : MemLp f 2 ν[n])
    (hF : MemLp F 2 ν[n]) {g : E n → ℝ} (hg : ContDiff ℝ ∞ g) :
    IsDirichletWeakGradient (fun x => g x - f x) (fun x => ∇ g x - F x) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hWg := IsDirichletWeakGradient.of_smooth hn hg
  have hGg : MemLp (∇ g) 2 ν[n] :=
    memLp_continuousOn_dirichletBall hn (contDiff_euclideanGradient hg).continuous.continuousOn
  have hgg : MemLp g 2 ν[n] := memLp_continuousOn_dirichletBall hn hg.continuous.continuousOn
  intro j ψ
  have hInt {p q : E n → ℝ} (hp : ContinuousOn p (closedUnitBall n))
      (hq : MemLp q 2 ν[n]) : Integrable (fun x => p x * q x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn hp hq).integrable (by norm_num)
  have hDψ : ContinuousOn (fun x => fderiv ℝ (ψ : E n → ℝ) x (e[n] j))
      (closedUnitBall n) :=
    ((ψ.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.continuousOn
  simp only [inner_sub_right, mul_sub]
  rw [integral_sub (hInt ψ.continuous.continuousOn (hGg.const_inner (e[n] j)))
      (hInt ψ.continuous.continuousOn (hF.const_inner (e[n] j))),
    integral_sub (hInt hDψ hgg) (hInt hDψ hf), hWg j ψ, hWeak j ψ]
  ring

/-- The corrected defect and its explicitly chosen weak gradient. -/
def dirichletCorrectedHessianDefect {n : ℕ}
    (G : E n → E n →L[ℝ] ℝ) (v : E n) (M a R : ℝ) (x₀ x : E n) : ℝ :=
  M - fderiv ℝ G x v v + dirichletSourceQuadratic a R x₀ x

def dirichletCorrectedHessianGradient {n : ℕ}
    (F : E n → E n) (a R : ℝ) (x₀ x : E n) : E n :=
  -F x + ∇ (dirichletSourceQuadratic a R x₀) x

/-- Linear weak differentiation identifies the corrected field without
taking a classical derivative of the bounded Hessian representative. -/
theorem isDirichletWeakGradient_correctedHessianDefect {n : ℕ} (hn : 0 < n)
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n)) (v : E n)
    {F : E n → E n} (hF : MemLp F 2 ν[n])
    (hWeak : IsDirichletWeakGradient (fun x => fderiv ℝ G x v v) F)
    (M a R : ℝ) (x₀ : E n) :
    MemLp (dirichletCorrectedHessianDefect G v M a R x₀) 2 ν[n] ∧
    MemLp (dirichletCorrectedHessianGradient F a R x₀) 2 ν[n] ∧
    IsDirichletWeakGradient (dirichletCorrectedHessianDefect G v M a R x₀)
      (dirichletCorrectedHessianGradient F a R x₀) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hf : MemLp (fun x => fderiv ℝ G x v v) 2 ν[n] :=
    (memLp_top_hessianEntry_of_lipschitz_firstJet hG v v).mono_exponent (by simp)
  let q := dirichletSourceQuadratic a R x₀
  let g (x : E n) := M + q x
  have hq : ContDiff ℝ ∞ q := contDiff_dirichletSourceQuadratic a R x₀
  have hg : ContDiff ℝ ∞ g := contDiff_const.add hq
  have he (x : E n) : g x - fderiv ℝ G x v v =
      dirichletCorrectedHessianDefect G v M a R x₀ x := by
    dsimp only [g, q, dirichletCorrectedHessianDefect]
    ring
  have hgrad (x : E n) : ∇ g x = ∇ q x := by
    change (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ (fun y => M + q y) x) = _
    rw [fderiv_const_add]
    rfl
  have hfield (x : E n) : ∇ g x - F x = dirichletCorrectedHessianGradient F a R x₀ x := by
    rw [hgrad]
    change ∇ q x - F x = -F x + ∇ q x
    abel
  have heFun : (fun x => g x - fderiv ℝ G x v v) =
      dirichletCorrectedHessianDefect G v M a R x₀ := funext he
  have hfieldFun : (fun x => ∇ g x - F x) =
      dirichletCorrectedHessianGradient F a R x₀ := funext hfield
  refine ⟨?_, ?_, ?_⟩
  · rw [← heFun]
    exact (memLp_continuousOn_dirichletBall hn hg.continuous.continuousOn).sub hf
  · rw [← hfieldFun]
    exact (memLp_continuousOn_dirichletBall hn
      (contDiff_euclideanGradient hg).continuous.continuousOn).sub hF
  · rw [← heFun, ← hfieldFun]
    exact hWeak.smooth_sub hn hf hF hg

/-- Every actual directional Hessian subsolution from S053 has a bounded
source correction giving a homogeneous weak supersolution. The two L²
memberships and the weak-gradient identity refer to the very same defect.

Nonnegativity on a smaller ball still requires the chosen number `M` to be
an essential upper bound there, as it must when applying weak Harnack. -/
theorem exists_homogeneous_corrected_hessian_defect {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g) (t : ℝ)
    {G : E n → E n →L[ℝ] ℝ} {L : ℝ≥0}
    (hG : LipschitzOnWith L G (closedUnitBall n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n])
    (hDiv : ∀ (v : E n) (φ : 𝓓B[n]),
      (∫ x, inner ℝ (A x v) (∇ (φ : E n → ℝ) x) ∂ν[n]) = 0)
    {c : ℝ} (hc : 0 < c)
    (hEll : ∀ᵐ x ∂ν[n], ∀ v : E n, c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (v : E n) {F : E n → E n} (hF : MemLp F 2 ν[n])
    (hWeak : IsDirichletWeakGradient (fun x => fderiv ℝ G x v v) F)
    (hSub : ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
      (∫ x, inner ℝ (A x (F x)) (∇ (ψ : E n → ℝ) x) ∂ν[n]) ≤
        -(∫ x, ψ x * (Real.exp (t * g x) * (t * realHessian g x v v)) ∂ν[n])) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (M R : ℝ) (x₀ : E n),
      MemLp (dirichletCorrectedHessianDefect G v M (B / (4 * n * c)) R x₀) 2 ν[n] ∧
      MemLp (dirichletCorrectedHessianGradient F (B / (4 * n * c)) R x₀) 2 ν[n] ∧
      IsDirichletWeakGradient
        (dirichletCorrectedHessianDefect G v M (B / (4 * n * c)) R x₀)
        (dirichletCorrectedHessianGradient F (B / (4 * n * c)) R x₀) ∧
      ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
        0 ≤ ∫ x, inner ℝ (A x (dirichletCorrectedHessianGradient F (B / (4 * n * c)) R x₀ x))
          (∇ (ψ : E n → ℝ) x) ∂ν[n] := by
  obtain ⟨hs, B, hB, hBound⟩ := exists_bound_logDensity_hessianSource hn hg t v
  have hLower : ∀ᵐ x ∂ν[n], -B ≤ Real.exp (t * g x) * (t * realHessian g x v v) := by
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    exact (abs_le.mp (hBound x (ball_subset_closedBall hx))).1
  refine ⟨B, hB, fun M R x₀ => ?_⟩
  obtain ⟨hh, hQ, hW⟩ := isDirichletWeakGradient_correctedHessianDefect hn hG v hF hWeak
    M (B / (4 * n * c)) R x₀
  exact ⟨hh, hQ, hW, fun ψ hψ =>
    upper_defect_quadraticCorrection_homogeneous hn hA hDiv hc hB hEll hF hs hLower
      hSub R x₀ ψ hψ⟩

/-- The correction is nonnegative on its ball and bounded by its amplitude
times `R²`. This records the scale needed for the inhomogeneous Harnack term. -/
theorem correctedHessianDefect_nonneg_of_upper_bound {n : ℕ}
    (G : E n → E n →L[ℝ] ℝ) (v : E n) {M a R : ℝ} (ha : 0 ≤ a)
    (hR : 0 ≤ R) {x₀ x : E n} (hx : x ∈ closedBall x₀ R)
    (hM : fderiv ℝ G x v v ≤ M) :
    0 ≤ dirichletCorrectedHessianDefect G v M a R x₀ x ∧
    dirichletCorrectedHessianDefect G v M a R x₀ x ≤
      M - fderiv ℝ G x v v + a * R ^ 2 := by
  have hq := dirichletSourceQuadratic_bounds ha hR hx
  constructor
  · exact add_nonneg (sub_nonneg.mpr hM) hq.1
  · change M - fderiv ℝ G x v v + dirichletSourceQuadratic a R x₀ x ≤
      M - fderiv ℝ G x v v + a * R ^ 2
    linarith only [hq.2]

/-- The full input is obtained from the actual log-density path on a single
limit witness. This is a limit theorem, not a Dirichlet existence or Harnack
theorem: the sequence of smooth path solutions is part of its input. -/
theorem exists_dirichlet_limit_with_harnack_input_of_logDensityPath {n : ℕ} (hn : 0 < n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ (w : E n → ℝ) (G : E n → E n →L[ℝ] ℝ) (L : ℝ≥0),
      ContinuousOn w (closedUnitBall n) ∧
      (∀ x ∈ unitBall n, HasFDerivAt w (G x) x) ∧
      LipschitzOnWith L G (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ᵐ x ∂ν[n], (complexHessianOfRealBilinear (fderiv ℝ G x)).PosDef ∧
        (complexHessianOfRealBilinear (fderiv ℝ G x)).det.re = Real.exp (t₀ * g x)) ∧
      let A (x : E n) := dirichletCofactorOfMatrix (complexHessianOfRealBilinear (fderiv ℝ G x))
      MemLp A ⊤ ν[n] ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (∀ᵐ x ∂ν[n], ∀ v : E n,
          c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v ∧ inner ℝ (A x v) v ≤ C * ‖v‖ ^ 2) ∧
        (∀ (v : E n) (ψ : 𝓓B[n]),
          (∫ x, inner ℝ (A x v) (∇ (ψ : E n → ℝ) x) ∂ν[n]) = 0) ∧
        ∀ v : E n, ∃ F : DirichletBallL2 n (E n),
          IsDirichletWeakGradient (fun x => fderiv ℝ G x v v) F ∧
          ∃ B : ℝ, 0 ≤ B ∧ ∀ (M R : ℝ) (x₀ : E n),
            MemLp (dirichletCorrectedHessianDefect G v M (B / (4 * n * c)) R x₀) 2 ν[n] ∧
            MemLp (dirichletCorrectedHessianGradient F (B / (4 * n * c)) R x₀) 2 ν[n] ∧
            IsDirichletWeakGradient
              (dirichletCorrectedHessianDefect G v M (B / (4 * n * c)) R x₀)
              (dirichletCorrectedHessianGradient F (B / (4 * n * c)) R x₀) ∧
            ∀ ψ : 𝓓B[n], (∀ x ∈ unitBall n, 0 ≤ ψ x) →
              0 ≤ ∫ x, inner ℝ
                (A x (dirichletCorrectedHessianGradient F (B / (4 * n * c)) R x₀ x))
                (∇ (ψ : E n → ℝ) x) ∂ν[n] := by
  obtain ⟨w, G, L, hwC, hD, hLip, hw0, hH, hA, hEllData, hDiv, _, hSecond⟩ :=
    exists_dirichlet_limit_with_divergence_free_cofactor_of_logDensityPath
      hn hg ht hT hu hu0 huP hEq
  obtain ⟨c, C, hc, hC, hEll⟩ := hEllData
  refine ⟨w, G, L, hwC, hD, hLip, hw0, hH, hA, c, C, hc, hC, hEll, hDiv, ?_⟩
  intro v
  obtain ⟨F, hWeak, hSub⟩ := hSecond v
  refine ⟨F, hWeak, ?_⟩
  exact exists_homogeneous_corrected_hessian_defect hn hg t₀ hLip hA hDiv hc
    (hEll.mono fun x hx v => (hx v).1) v (Lp.memLp F) hWeak hSub

end KEBall
