import KEBall.DirichletEllipticWeakSobolev
import KEBall.DirichletAngularWeakSobolev

/-! The annular gain of one order from the angular and elliptic equations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private theorem dirichletMatrixEntry_sum {n : ℕ} {ι : Type*}
    (entry : 𝓓B[n] → E n → E n → ℝ)
    (hZero : ∀ v w, entry 0 v w = 0)
    (hAdd : ∀ ψ φ v w, entry (ψ + φ) v w = entry ψ v w + entry φ v w)
    (s : Finset ι) (ψ : ι → 𝓓B[n]) (v w : E n) :
    entry (∑ i ∈ s, ψ i) v w = ∑ i ∈ s, entry (ψ i) v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hZero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hAdd, ih]

private theorem exists_dirichletMatrixContraction_tangentCompL2 {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (entry : 𝓓B[n] → E n → E n → ℝ)
    (hZero : ∀ v w, entry 0 v w = 0)
    (hAdd : ∀ ψ φ v w, entry (ψ + φ) v w = entry ψ v w + entry φ v w)
    (hTan : ∀ i j : Fin (2 * n), ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (∑ k, entry (dirichletTestMul ψ ((innerSL ℝ (b k)).contDiff.comp
        (contDiff_dirichletTangentTensor.clm_apply (contDiff_const (c := b j))))) (b k) (b i)) =
        ∫ x, ψ x * T x ∂ν[n])
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      dirichletMatrixContraction b entry ψ (contDiff_dirichletTangentTensor.clm_comp hB) =
        ∫ x, ψ x * T x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let P := dirichletTangentTensor (n := n)
  let hP : ContDiff ℝ ∞ P := contDiff_dirichletTangentTensor
  let X (j : Fin (2 * n)) (x : E n) := P x (b j)
  let hX (j : Fin (2 * n)) : ContDiff ℝ ∞ (X j) := hP.clm_apply contDiff_const
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
      (∑ k, entry (τ i j k) (b k) (b i)) =
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
  change dirichletMatrixContraction b entry ψ (hP.clm_comp hB) = _
  unfold dirichletMatrixContraction
  simp_rw [hTest, dirichletMatrixEntry_sum entry hZero hAdd]
  have hSwap :
      (∑ i, ∑ k, ∑ j, entry (τ i j k) (b k) (b i)) =
        ∑ i, ∑ j, ∑ k, entry (τ i j k) (b k) (b i) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hSwap]
  simp_rw [hField, Finset.mul_sum]
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI (hTerm i j)))]
  exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ (fun j _ => hI (hTerm i j))).symm


private theorem dirichletDistributionalDerivative_zero {n : ℕ} (u : DirichletSobolev n)
    (ds : List (E n)) : dirichletDistributionalDerivative u ds 0 = 0 := by
  have hz (d : E n) : dirichletTestLineDerivative d (0 : 𝓓B[n]) = 0 := by
    apply TestFunction.ext
    intro x
    change fderiv ℝ (fun _ : E n => (0 : ℝ)) x d = 0
    simp
  induction ds with
  | nil => simp [dirichletWeakDerivativeTest]
  | cons d ds ih => simp only [dirichletWeakDerivativeTest, hz, ih, neg_zero]

private theorem sum_dirichletDistributionalDerivative_eq_field {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓B[n]) (ds : List (E n))
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (heF : ∀ τ : 𝓓B[n], dirichletDistributionalDerivative u ds τ = ∫ x, τ x * F x ∂ν[n]) :
    (∑ i, dirichletDistributionalDerivative u (b i :: ds)
      (dirichletTestMul ψ ((innerSL ℝ (b i)).contDiff.comp hX))) =
      -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) *
        F x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let D (i : Fin (2 * n)) := dirichletTestLineDerivative (b i)
    (dirichletTestMul ψ ((innerSL ℝ (b i)).contDiff.comp hX))
  have hI (i : Fin (2 * n)) : Integrable (fun x => D i x * F x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn (D i).continuous.continuousOn hF).integrable (by norm_num)
  change (∑ i, -dirichletDistributionalDerivative u ds (D i)) = _
  simp_rw [heF, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun i _ => hI i)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ i, D i x * F x) = _
    rw [← Finset.sum_mul]
    exact congrArg (fun a : ℝ => a * F x) (sum_dirichletTestFieldDerivative_mul_eq b ψ hX x)

/-- One more weak derivative is controlled on every exterior annulus, in
all real directions, when the angular equation provides the preceding order. -/
theorem IsDirichletWeakSolution.exists_dirichletDistributionalDerivativeL2_on_annulus
    {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (k : ℕ) (hU : HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2))
    (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) (k + 1))
    (hAngle : ∀ (S : E n →L[ℝ] E n), star S = -S →
      ∃ v : DirichletSobolev n,
        HasDirichletWeakDerivativesL2 ((v : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2) ∧
        ∀ ψ : 𝓓B[n], (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    {r : ℝ} (hr : 0 < r) (d : E n) (ds : List (E n)) (hds : ds.length = k)
    (i j : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      tsupport (ψ : E n → ℝ) ⊆ {x | r < ‖x‖} →
      dirichletDistributionalDerivative u ((d :: ds) ++ [b j, b i]) ψ =
        ∫ x, ψ x * F x ∂ν[n] := by
  let ls := d :: ds
  let entry (ψ : 𝓓B[n]) (v w : E n) := dirichletDistributionalDerivative u (ls ++ [v, w]) ψ
  have hZero (v w : E n) : entry 0 v w = 0 := dirichletDistributionalDerivative_zero u _
  have hAdd (ψ φ : 𝓓B[n]) (v w : E n) :
      entry (ψ + φ) v w = entry ψ v w + entry φ v w :=
    dirichletDistributionalDerivative_add hn u _ ψ φ
  have hEntrySym (ψ : 𝓓B[n]) (v w : E n) : entry ψ v w = entry ψ w v :=
    dirichletDistributionalDerivative_perm u ((List.Perm.swap w v []).append_left ls) ψ
  obtain ⟨F, hF, heF⟩ := hu.exists_dirichletDistributionalDerivative_matrixL2 hn b hA k hU hg d ds hds
  have hTrace : HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖} hA :=
    ⟨F, hF, fun ψ _ => heF ψ⟩
  let P := dirichletTangentTensor (n := n)
  let X (j : Fin (2 * n)) (x : E n) := P x (b j)
  let hX (j : Fin (2 * n)) : ContDiff ℝ ∞ (X j) :=
    contDiff_dirichletTangentTensor.clm_apply contDiff_const
  have hTan (i j : Fin (2 * n)) : ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (∑ a, entry (dirichletTestMul ψ ((innerSL ℝ (b a)).contDiff.comp (hX j))) (b a) (b i)) =
        ∫ x, ψ x * T x ∂ν[n] := by
    obtain ⟨H, T, hH, hT, he⟩ := exists_dirichletDistributionalDerivative_tangentL2 hn hU hAngle
      (ls ++ [b i]) (by simp [ls, hds]) (b j)
    refine ⟨T, hT, fun ψ => ?_⟩
    have hPerm (a : Fin (2 * n)) (τ : 𝓓B[n]) :
        entry τ (b a) (b i) = dirichletDistributionalDerivative u (b a :: (ls ++ [b i])) τ :=
      dirichletDistributionalDerivative_perm u List.perm_middle τ
    simp_rw [hPerm]
    rw [sum_dirichletDistributionalDerivative_eq_field hn b u ψ (ls ++ [b i]) (hX j)
      hH (fun τ => (he τ).1), (he ψ).2]
    have hDiv (x : E n) : dirichletVectorDivergence b (X j) x =
        (1 - (2 : ℝ) * n) * inner ℝ (b j) x :=
      dirichletVectorDivergence_tangentTensor b (b j) x
    simp_rw [hDiv, mul_comm (ψ _)]
    simp only [X, P, dirichletTangentTensor_apply]
  have hTangent {D : E n → E n →L[ℝ] E n} (hD : ContDiff ℝ ∞ D) :
      HasDirichletMatrixContractionL2On b entry {x | r < ‖x‖}
        (contDiff_dirichletTangentTensor.clm_comp hD) := by
    obtain ⟨T, hT, heT⟩ := exists_dirichletMatrixContraction_tangentCompL2 hn b entry hZero hAdd hTan hD
    exact ⟨T, hT, fun ψ _ => heT ψ⟩
  let B (_ : E n) := rankOne ℝ (b j) (b i)
  let hB : ContDiff ℝ ∞ B := contDiff_const
  have hBAdj : ContDiff ℝ ∞ (fun x => (B x).adjoint) := by
    change ContDiff ℝ ∞ (fun _ : E n => (rankOne ℝ (b j) (b i)).adjoint)
    exact contDiff_const
  obtain ⟨T, hT, heT⟩ := hasDirichletMatrixContractionL2On_annulus hn b entry hAdd hEntrySym
    hA hB hSym hBAdj hl hr hE hTrace hTangent
  exact ⟨T, hT, fun ψ hψ =>
    (dirichletMatrixContraction_rankOne_basis b entry ψ i j hZero).symm.trans (heT ψ hψ)⟩

end KEBall
