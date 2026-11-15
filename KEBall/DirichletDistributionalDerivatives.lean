import KEBall.DirichletFourthDerivative

/-! Distributional derivatives of arbitrary order and their angular commutator. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Constant-direction differentiation preserves the Dirichlet test space. -/
noncomputable def dirichletTestLineDerivative {n : ℕ} (d : E n) (ψ : 𝓓B[n]) : 𝓓B[n] :=
  dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const

theorem dirichletTestLineDerivative_add {n : ℕ} (d : E n) (ψ φ : 𝓓B[n]) :
    dirichletTestLineDerivative d (ψ + φ) =
      dirichletTestLineDerivative d ψ + dirichletTestLineDerivative d φ := by
  apply TestFunction.ext
  intro x
  change fderiv ℝ (fun y => ψ y + φ y) x d =
    fderiv ℝ (ψ : E n → ℝ) x d + fderiv ℝ (φ : E n → ℝ) x d
  rw [fderiv_fun_add (ψ.contDiff.differentiable (by simp) x)
    (φ.contDiff.differentiable (by simp) x), add_apply]

theorem dirichletTestLineDerivative_comm {n : ℕ} (d e : E n) (ψ : 𝓓B[n]) :
    dirichletTestLineDerivative e (dirichletTestLineDerivative d ψ) =
      dirichletTestLineDerivative d (dirichletTestLineDerivative e ψ) := by
  apply TestFunction.ext
  intro x
  change fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y d) x e =
    fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y e) x d
  have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const d),
    fderiv_clm_apply hd (differentiableAt_const e)]
  simpa using (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast) |>.eq e d

/-- The weak derivative in a list of fixed directions, tested by iterating
integration by parts against a compactly supported test. -/
noncomputable def dirichletWeakDerivativeTest {n : ℕ} (f : E n → ℝ) :
    List (E n) → 𝓓B[n] → ℝ
  | [], ψ => ∫ x, ψ x * f x ∂ν[n]
  | d :: ds, ψ => -dirichletWeakDerivativeTest f ds (dirichletTestLineDerivative d ψ)

/-- Distributional derivatives of the value of a Dirichlet Sobolev element. -/
noncomputable abbrev dirichletDistributionalDerivative {n : ℕ} (u : DirichletSobolev n) :=
  dirichletWeakDerivativeTest ((u : DirichletBallL2Pair n).fst : E n → ℝ)

theorem dirichletWeakDerivativeTest_add_test {n : ℕ} (hn : 0 < n) {f : E n → ℝ} (hf : MemLp f 2 ν[n])
    (ds : List (E n)) (ψ φ : 𝓓B[n]) :
    dirichletWeakDerivativeTest f ds (ψ + φ) =
      dirichletWeakDerivativeTest f ds ψ + dirichletWeakDerivativeTest f ds φ := by
  induction ds generalizing ψ φ with
  | nil =>
      have : NeZero n := ⟨hn.ne'⟩
      have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
      have hI (τ : 𝓓B[n]) : Integrable (fun x => τ x * f x) ν[n] :=
        (memLp_dirichlet_mul_of_continuousOn τ.continuous.continuousOn hf).integrable
          (by norm_num)
      change (∫ x, (ψ x + φ x) * f x ∂ν[n]) =
        (∫ x, ψ x * f x ∂ν[n]) + ∫ x, φ x * f x ∂ν[n]
      simp only [add_mul, integral_add (hI ψ) (hI φ)]
  | cons d ds ih =>
      simp only [dirichletWeakDerivativeTest, dirichletTestLineDerivative_add, ih, neg_add]

theorem dirichletDistributionalDerivative_add {n : ℕ} (hn : 0 < n) (u : DirichletSobolev n)
    (ds : List (E n)) (ψ φ : 𝓓B[n]) :
    dirichletDistributionalDerivative u ds (ψ + φ) =
      dirichletDistributionalDerivative u ds ψ + dirichletDistributionalDerivative u ds φ :=
  dirichletWeakDerivativeTest_add_test hn (Lp.memLp (u : DirichletBallL2Pair n).fst) ds ψ φ

theorem dirichletWeakDerivativeTest_perm {n : ℕ} (f : E n → ℝ)
    {ds es : List (E n)} (h : ds.Perm es) (ψ : 𝓓B[n]) :
    dirichletWeakDerivativeTest f ds ψ = dirichletWeakDerivativeTest f es ψ := by
  induction h generalizing ψ with
  | nil => rfl
  | cons d h ih => simp only [dirichletWeakDerivativeTest, ih]
  | swap d e ds =>
      simp only [dirichletWeakDerivativeTest]
      rw [dirichletTestLineDerivative_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ ψ).trans (ih₂ ψ)

theorem dirichletDistributionalDerivative_perm {n : ℕ} (u : DirichletSobolev n)
    {ds es : List (E n)} (h : ds.Perm es) (ψ : 𝓓B[n]) :
    dirichletDistributionalDerivative u ds ψ = dirichletDistributionalDerivative u es ψ :=
  dirichletWeakDerivativeTest_perm _ h ψ

theorem dirichletDistributionalDerivative_singleton {n : ℕ} (u : DirichletSobolev n)
    (d : E n) (ψ : 𝓓B[n]) :
    dirichletDistributionalDerivative u [d] ψ =
      ∫ x, ψ x * inner ℝ d ((u : DirichletBallL2Pair n).snd x) ∂ν[n] :=
  (dirichletSobolev_integral_weakGradient u ψ d).symm

theorem dirichletDistributionalDerivative_pair {n : ℕ} (u : DirichletSobolev n)
    (d e : E n) (ψ : 𝓓B[n]) :
    dirichletDistributionalDerivative u [d, e] ψ = dirichletHessianEntry u ψ d e := by
  change -dirichletDistributionalDerivative u [e] (dirichletTestLineDerivative d ψ) = _
  rw [dirichletDistributionalDerivative_singleton]
  rfl

theorem dirichletDistributionalDerivative_triple {n : ℕ} (u : DirichletSobolev n)
    (d e v : E n) (ψ : 𝓓B[n]) :
    dirichletDistributionalDerivative u [d, e, v] ψ = dirichletThirdDerivativeEntry u ψ d e v := by
  change -dirichletDistributionalDerivative u [e, v] (dirichletTestLineDerivative d ψ) = _
  rw [dirichletDistributionalDerivative_pair]
  rfl

theorem dirichletDistributionalDerivative_quadruple {n : ℕ} (u : DirichletSobolev n)
    (d e v w : E n) (ψ : 𝓓B[n]) :
    dirichletDistributionalDerivative u [d, e, v, w] ψ =
      dirichletFourthDerivativeEntry u ψ d e v w := by
  change -dirichletDistributionalDerivative u [e, v, w] (dirichletTestLineDerivative d ψ) = _
  rw [dirichletDistributionalDerivative_triple]
  rfl

private theorem dirichletTestLineDerivative_angular {n : ℕ} (d : E n)
    (S : E n →L[ℝ] E n) (ψ : 𝓓B[n]) :
    dirichletTestLineDerivative d (dirichletTestFieldDerivative ψ S S.contDiff) =
      dirichletTestFieldDerivative (dirichletTestLineDerivative d ψ) S S.contDiff +
        dirichletTestLineDerivative (S d) ψ := by
  apply TestFunction.ext
  intro x
  have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hs := (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast)
  change fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y (S y)) x d =
    fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y d) x (S x) + fderiv ℝ (ψ : E n → ℝ) x (S d)
  rw [fderiv_clm_apply hd S.differentiableAt, fderiv_clm_apply hd (differentiableAt_const d)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.fderiv, fderiv_fun_const, Pi.zero_apply, zero_apply, map_zero, zero_add]
  rw [hs.eq d (S x), add_comm]

/-- The lists obtained by replacing one direction at a time by its image
under the linear vector field defining an angular derivative. -/
def dirichletAngularDirectionVariations {n : ℕ} (S : E n →L[ℝ] E n) :
    List (E n) → List (List (E n))
  | [] => []
  | d :: ds => (S d :: ds) :: (dirichletAngularDirectionVariations S ds).map (d :: ·)

private theorem dirichletAngularDirectionVariations_sum_cons {n : ℕ}
    (u : DirichletSobolev n) (d : E n) (ls : List (List (E n))) (ψ : 𝓓B[n]) :
    ((ls.map (d :: ·)).map (fun ds => dirichletDistributionalDerivative u ds ψ)).sum =
      -((ls.map (fun ds =>
        dirichletDistributionalDerivative u ds (dirichletTestLineDerivative d ψ))).sum) := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp only [List.map_cons, List.sum_cons, dirichletWeakDerivativeTest, ih, neg_add]

/-- The angular commutator for an arbitrary number of fixed derivatives.
Each correction comes from differentiating the linear angular field in one
of the fixed directions. -/
theorem dirichletDistributionalDerivative_angular_commutator {n : ℕ} (hn : 0 < n)
    (u v : DirichletSobolev n) (S : E n →L[ℝ] E n)
    (hv : ∀ ψ : 𝓓B[n], (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (ds : List (E n)) (ψ : 𝓓B[n]) :
    -dirichletDistributionalDerivative u ds (dirichletTestFieldDerivative ψ S S.contDiff) =
      dirichletDistributionalDerivative v ds ψ -
        ((dirichletAngularDirectionVariations S ds).map
          (fun es => dirichletDistributionalDerivative u es ψ)).sum := by
  induction ds generalizing ψ with
  | nil =>
      simp only [dirichletAngularDirectionVariations, List.map_nil, List.sum_nil,
        sub_zero, dirichletWeakDerivativeTest]
      exact (hv ψ).symm
  | cons d ds ih =>
      have he := ih (dirichletTestLineDerivative d ψ)
      simp only [dirichletWeakDerivativeTest, dirichletAngularDirectionVariations,
        List.map_cons, List.sum_cons, dirichletAngularDirectionVariations_sum_cons,
        dirichletTestLineDerivative_angular, dirichletDistributionalDerivative_add hn]
      linarith only [he]

end KEBall
