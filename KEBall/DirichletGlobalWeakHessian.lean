import KEBall.DirichletWholeSecondDerivative
import KEBall.DirichletHessianTraceL2

/-! Gluing the interior and boundary estimates for the actual weak Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- On the region where a cutoff equals one, the tested weak gradient
of the localized zero extension agrees with that of the original solution. -/
theorem integral_dirichletCutoff_gradient_on_interior {n : ℕ}
    (u : DirichletSobolev n) (χ ψ : 𝓓(dirichletBallOpens n, ℝ))
    (hχ : ∀ x ∈ closedBall (0 : E n) (1 / 2), χ x = 1)
    (hSupp : tsupport (ψ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2)) (v e : E n) :
    let w := euclideanSobolevCutoff χ (dirichletSobolevZeroExtension n u)
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ e ((w : EuclideanL2Pair n).snd x) ∂volume0 n) =
      ∫ x, fderiv ℝ (ψ : E n → ℝ) x v *
        inner ℝ e ((u : DirichletBallL2Pair n).snd x) ∂ν[n] := by
  let z := dirichletSobolevZeroExtension n u
  let w := euclideanSobolevCutoff χ z
  have hGrad (x : E n) (hx : x ∈ ball (0 : E n) (1 / 2)) : ∇ (χ : E n → ℝ) x = 0 := by
    have he : (χ : E n → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hχ y (ball_subset_closedBall hy)
    apply ext_inner_right ℝ
    intro y
    rw [inner_gradient_left, inner_zero_left, he.fderiv_eq, fderiv_fun_const, Pi.zero_apply, zero_apply]
  rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
  apply integral_congr_ae
  filter_upwards [euclideanSobolevCutoff_gradient_ae χ z,
    dirichletSobolevZeroExtension_gradient_ae u] with x hw hz
  change (z : EuclideanL2Pair n).snd x =
    (unitBall n).indicator (fun y => (u : DirichletBallL2Pair n).snd y) x at hz
  change fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ e ((w : EuclideanL2Pair n).snd x) =
    (unitBall n).indicator (fun y => fderiv ℝ (ψ : E n → ℝ) y v *
      inner ℝ e ((u : DirichletBallL2Pair n).snd y)) x
  by_cases hx : x ∈ tsupport (ψ : E n → ℝ)
  · have hb : x ∈ unitBall n := ψ.tsupport_subset hx
    rw [hw, hz, indicator_of_mem hb, indicator_of_mem hb, hχ x (ball_subset_closedBall (hSupp hx)),
      hGrad x (hSupp hx), one_smul, smul_zero, add_zero]
  · have hD : fderiv ℝ (ψ : E n → ℝ) x v = 0 := by
      rw [fderiv_of_notMem_tsupport ℝ hx, zero_apply]
    by_cases hb : x ∈ unitBall n
    · rw [indicator_of_mem hb, hD, zero_mul, zero_mul]
    · rw [indicator_of_notMem hb, hD, zero_mul]

/-- Every Hessian entry on the interior ball is represented in L². -/
theorem exists_dirichletHessianEntryL2_interior {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x)
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (v e : E n) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2) →
      dirichletHessianEntry u ψ v e = ∫ x, ψ x * F x ∂ν[n] := by
  obtain ⟨χ, B, K, hB, g', hχ, hBE, hLip, hEq⟩ := hu.exists_interior_cutoff hn b hA hSym hE
  obtain ⟨H, hH⟩ := exists_euclideanGradient_weakDerivative hB hl
    (Eventually.of_forall hBE) hLip hEq v
  refine ⟨fun x => inner ℝ e (H x), ((Lp.memLp H).const_inner e).restrict _, fun ψ hSupp => ?_⟩
  let φ : 𝓓((⊤ : Opens (E n)), ℝ) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_univ _⟩
  have hLeft : (∫ x, ψ x * inner ℝ e (H x) ∂ν[n]) =
      ∫ x, φ x * inner ℝ e (H x) ∂volume0 n := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (ψ.tsupport_subset hs)), zero_mul]
  rw [hLeft, hH φ e]
  exact congrArg Neg.neg (integral_dirichletCutoff_gradient_on_interior u χ ψ hχ hSupp v e).symm

/-- A distribution with compatible square-integrable representatives on
the interior ball and the exterior annulus has one on the entire ball. -/
theorem exists_dirichletTestL2_of_interior_annulus {n : ℕ} (hn : 0 < n)
    (T : 𝓓(dirichletBallOpens n, ℝ) → ℝ)
    (hAdd : ∀ ψ φ, T (ψ + φ) = T ψ + T φ) {F₀ F₁ : E n → ℝ}
    (hF₀ : MemLp F₀ 2 ν[n]) (hF₁ : MemLp F₁ 2 ν[n])
    (he₀ : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2) →
      T ψ = ∫ x, ψ x * F₀ x ∂ν[n])
    (he₁ : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ {x | (1 / 8 : ℝ) < ‖x‖} →
      T ψ = ∫ x, ψ x * F₁ x ∂ν[n]) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      T ψ = ∫ x, ψ x * F x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let κ : ContDiffBump (0 : E n) := ⟨1 / 4, 1 / 3, by norm_num, by norm_num⟩
  let κ₁ (x : E n) := 1 - κ x
  have hκ : ContDiff ℝ ∞ (κ : E n → ℝ) := κ.contDiff
  have hκ₁ : ContDiff ℝ ∞ κ₁ := contDiff_const.sub hκ
  have hF₀' : MemLp (fun x => κ x * F₀ x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hκ.continuous.continuousOn hF₀
  have hF₁' : MemLp (fun x => κ₁ x * F₁ x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hκ₁.continuous.continuousOn hF₁
  refine ⟨fun x => κ x * F₀ x + κ₁ x * F₁ x, hF₀'.add hF₁', fun ψ => ?_⟩
  let ψ₀ := dirichletTestMul ψ hκ
  let ψ₁ := dirichletTestMul ψ hκ₁
  have hSupp₀ : tsupport (ψ₀ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2) := by
    apply tsupport_mul_subset_right.trans
    rw [κ.tsupport_eq]
    exact closedBall_subset_ball (show κ.rOut < (1 / 2 : ℝ) by norm_num [κ])
  have hSupp₁ : tsupport (ψ₁ : E n → ℝ) ⊆ {x | (1 / 8 : ℝ) < ‖x‖} := by
    apply tsupport_mul_subset_right.trans
    have hSub : tsupport κ₁ ⊆ (ball (0 : E n) (1 / 4))ᶜ := by
      apply closure_minimal _ isOpen_ball.isClosed_compl
      intro x hx h
      exact hx (by simp [κ₁, κ.one_of_mem_closedBall (ball_subset_closedBall h)])
    intro x hx
    have hNorm : (1 / 4 : ℝ) ≤ ‖x‖ := le_of_not_gt fun h => hSub hx (mem_ball_zero_iff.mpr h)
    exact lt_of_lt_of_le (by norm_num) hNorm
  have hψ : ψ₀ + ψ₁ = ψ := by
    apply TestFunction.ext
    intro x
    change ψ x * κ x + ψ x * (1 - κ x) = ψ x
    ring
  have hI (F : E n → ℝ) (hF : MemLp F 2 ν[n]) :
      Integrable (fun x => ψ x * F x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hF).integrable (by norm_num)
  calc
    _ = T (ψ₀ + ψ₁) := by rw [hψ]
    _ = (∫ x, ψ₀ x * F₀ x ∂ν[n]) + ∫ x, ψ₁ x * F₁ x ∂ν[n] := by
      rw [hAdd, he₀ ψ₀ hSupp₀, he₁ ψ₁ hSupp₁]
    _ = _ := by
      simp only [ψ₀, ψ₁, dirichletTestMul_apply, mul_assoc, mul_add]
      exact (integral_add (hI _ hF₀') (hI _ hF₁')).symm


/-- The weak Hessian entries on the whole ball are represented by actual
L² functions, including at the center and up to the boundary. -/
theorem exists_dirichletHessianEntryL2 {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (i j : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletHessianEntry u ψ (b j) (b i) = ∫ x, ψ x * F x ∂ν[n] := by
  obtain ⟨F₀, hF₀, he₀⟩ :=
    exists_dirichletHessianEntryL2_interior hn b hAc (fun x _ => hSym x) hl hE hu (b j) (b i)
  obtain ⟨F₁, hF₁, he₁⟩ := exists_dirichletHessianEntryL2_on_annulus hn b hA hAc hSym hl hE
    hLipA hM₀ hM hu (r := 1 / 8) (by norm_num) i j
  exact exists_dirichletTestL2_of_interior_annulus hn _ (fun ψ φ =>
    dirichletHessianEntry_add hn u ψ φ (b j) (b i)) hF₀ hF₁ he₀ he₁

end KEBall
