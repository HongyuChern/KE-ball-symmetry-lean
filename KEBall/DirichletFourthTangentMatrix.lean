import KEBall.DirichletFourthTrace

/-! Matrix contractions of tangential fourth weak derivatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem dirichletFourthDerivativeEntry_add {n : ℕ} (hn : 0 < n)
    (u : DirichletSobolev n) (ψ χ : 𝓓B[n]) (d e v w : E n) :
    dirichletFourthDerivativeEntry u (ψ + χ) d e v w =
      dirichletFourthDerivativeEntry u ψ d e v w + dirichletFourthDerivativeEntry u χ d e v w := by
  have hTest : dirichletTestFieldDerivative (ψ + χ) (fun _ => d) contDiff_const =
      dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const +
        dirichletTestFieldDerivative χ (fun _ => d) contDiff_const := by
    apply TestFunction.ext
    intro x
    change fderiv ℝ (fun y => ψ y + χ y) x d =
      fderiv ℝ (ψ : E n → ℝ) x d + fderiv ℝ (χ : E n → ℝ) x d
    rw [fderiv_fun_add (ψ.contDiff.differentiable (by simp) x)
      (χ.contDiff.differentiable (by simp) x), add_apply]
  simp only [dirichletFourthDerivativeEntry, hTest, dirichletThirdDerivativeEntry_add hn, neg_add]

theorem dirichletFourthDerivativeEntry_zero {n : ℕ} (u : DirichletSobolev n)
    (d e v w : E n) : dirichletFourthDerivativeEntry u 0 d e v w = 0 := by
  have h0 (z : E n) : dirichletTestFieldDerivative (0 : 𝓓B[n]) (fun _ => z) contDiff_const = 0 := by
    apply TestFunction.ext
    intro x
    change fderiv ℝ (fun _ : E n => (0 : ℝ)) x z = 0
    simp
  simp [dirichletFourthDerivativeEntry, dirichletThirdDerivativeEntry, h0, dirichletHessianEntry]

private theorem dirichletFourthDerivativeEntry_sum {n : ℕ} {ι : Type*} (hn : 0 < n)
    (u : DirichletSobolev n) (s : Finset ι) (ψ : ι → 𝓓B[n]) (d e v w : E n) :
    dirichletFourthDerivativeEntry u (∑ i ∈ s, ψ i) d e v w =
      ∑ i ∈ s, dirichletFourthDerivativeEntry u (ψ i) d e v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dirichletFourthDerivativeEntry_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, dirichletFourthDerivativeEntry_add hn, ih]

/-- A fourth derivative slice contracted with a smooth matrix followed by
the tangential projection has a square-integrable representative. -/
theorem IsDirichletWeakSolution.exists_dirichletFourthDerivativeSlice_tangentCompL2
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    (d e : Fin (2 * n)) {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      dirichletFourthDerivativeSlice b[n] u ψ (b[n] d) (b[n] e)
        (contDiff_dirichletTangentTensor.clm_comp hB) = ∫ x, ψ x * T x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let b := b[n]
  let P := dirichletTangentTensor (n := n)
  let hP : ContDiff ℝ ∞ P := contDiff_dirichletTangentTensor
  let X (j : Fin (2 * n)) (x : E n) := P x (b j)
  let hX (j : Fin (2 * n)) : ContDiff ℝ ∞ (X j) := hP.clm_apply contDiff_const
  have hTan (i j : Fin (2 * n)) := hu.exists_dirichletFourthDerivative_tangentL2
    hn hA hAc hSym hl hE hLipA hM₀ hM hG hRep i e d (b j)
  choose T hT he using hTan
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hB (b i) (b j)
  have hTerm (i j : Fin (2 * n)) : MemLp (fun x => c i j x * T i j x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hc i j).continuous.continuousOn (hT i j)
  have hSum (i : Fin (2 * n)) : MemLp (fun x => ∑ j, c i j x * T i j x) 2 ν[n] :=
    memLp_finsetSum Finset.univ fun j _ => hTerm i j
  refine ⟨fun x => ∑ i, ∑ j, c i j x * T i j x, memLp_finsetSum Finset.univ (fun i _ => hSum i),
    fun ψ => ?_⟩
  let φ (i j : Fin (2 * n)) := dirichletTestMul ψ (hc i j)
  let τ (i j k : Fin (2 * n)) := dirichletTestMul (φ i j) ((innerSL ℝ (b k)).contDiff.comp (hX j))
  have hField (i j : Fin (2 * n)) :
      (∑ k, dirichletFourthDerivativeEntry u (τ i j k) (b k) (b d) (b e) (b i)) =
        ∫ x, ψ x * (c i j x * T i j x) ∂ν[n] := by
    calc
      _ = ∫ x, φ i j x * T i j x ∂ν[n] := he i j (φ i j)
      _ = _ := by simp only [φ, dirichletTestMul_apply, mul_assoc]
  have hTest (i k : Fin (2 * n)) :
      dirichletTestMul ψ
        (contDiff_dirichletCoefficientEntry (hP.clm_comp hB) (b i) (b k)) =
      ∑ j, τ i j k := by
    apply TestFunction.ext
    intro x
    change ψ x * inner ℝ (b k) (P x (B x (b i))) = (∑ j, τ i j k) x
    rw [← b.sum_repr' (B x (b i)), map_sum, inner_sum]
    let ev : 𝓓B[n] →+ ℝ :=
      { toFun := fun χ => χ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    rw [show (∑ j, τ i j k) x = ∑ j, τ i j k x from map_sum ev _ _]
    simp only [map_smul, real_inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ψ x * (c i j x * _) = (ψ x * c i j x) * _
    rw [mul_assoc]
    rfl
  change dirichletFourthDerivativeSlice b u ψ (b d) (b e) (hP.clm_comp hB) = _
  unfold dirichletFourthDerivativeSlice
  simp_rw [hTest, dirichletFourthDerivativeEntry_sum hn]
  have hSwap :
      (∑ i, ∑ k, ∑ j, dirichletFourthDerivativeEntry u (τ i j k) (b d) (b e) (b k) (b i)) =
        ∑ i, ∑ j, ∑ k, dirichletFourthDerivativeEntry u (τ i j k) (b k) (b d) (b e) (b i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [dirichletFourthDerivativeEntry_comm₂₃ u _ (b d) (b e) (b k) (b i),
      dirichletFourthDerivativeEntry_comm₁₂ u _ (b d) (b k) (b e) (b i)]
  rw [hSwap]
  simp_rw [hField, Finset.mul_sum]
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI (hTerm i j)))]
  exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ (fun j _ => hI (hTerm i j))).symm

end KEBall
