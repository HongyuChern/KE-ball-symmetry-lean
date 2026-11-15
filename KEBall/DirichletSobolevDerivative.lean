import KEBall.DirichletSobolevDensity
import KEBall.RealHessian

/-! Bounded coordinate differentiation between Sobolev graphs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private def jetIndexOfList {n k : ℕ} (is : List (Fin (2 * n))) (h : is.length ≤ k) :
    DirichletJetIndex n k :=
  ⟨⟨is.length, Nat.lt_succ_of_le h⟩, is.get⟩

private theorem jetDirections_jetIndexOfList {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (is : List (Fin (2 * n))) (h : is.length ≤ k) :
    dirichletJetDirections b (jetIndexOfList is h) = is.map b := by
  change List.ofFn ((b : Fin (2 * n) → E n) ∘ is.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

private def appendCoordinateIndex {n k : ℕ} (a : Fin (2 * n))
    (i : DirichletJetIndex n k) : DirichletJetIndex n (k + 1) :=
  jetIndexOfList (List.ofFn i.2 ++ [a]) (by simp; omega)

private theorem jetDirections_appendCoordinateIndex {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (a : Fin (2 * n))
    (i : DirichletJetIndex n k) :
    dirichletJetDirections b (appendCoordinateIndex a i) = dirichletJetDirections b i ++ [b a] := by
  rw [appendCoordinateIndex, jetDirections_jetIndexOfList, List.map_append]
  simp only [List.map_cons, List.map_nil, List.map_ofFn, dirichletJetDirections, Function.comp_def]

/-- A coordinate derivative is a bounded linear map from H^(k+1) to H^k. -/
noncomputable def dirichletSobolevJetGraph_derivative {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (a : Fin (2 * n)) :
    dirichletSobolevJetGraph (k := k + 1) b →L[ℝ] dirichletSobolevJetGraph (k := k) b := by
  let j : DirichletJetIndex n (k + 1) := jetIndexOfList [a] (by simp)
  let pr : DirichletJetGraphAmbient n (k + 1) →L[ℝ]
      (DirichletJetIndex n (k + 1) → DirichletBallL2 n ℝ) :=
    ContinuousLinearMap.snd ℝ _ _
  let T : DirichletJetGraphAmbient n (k + 1) →L[ℝ] DirichletJetGraphAmbient n k :=
    (((ContinuousLinearMap.proj j).comp pr).prod
      (ContinuousLinearMap.pi (fun i => (ContinuousLinearMap.proj (appendCoordinateIndex a i)).comp pr)))
  let R := T.comp (dirichletSobolevJetGraph (k := k + 1) b).subtypeL
  refine R.codRestrict _ fun z => ?_
  apply (mem_dirichletSobolevJetGraph_iff b _).mpr
  intro i ψ
  have hD := (mem_dirichletSobolevJetGraph_iff b z.val).mp z.property
  have hSingle (τ : 𝓓B[n]) : dirichletWeakDerivativeTest z.val.1 [b a] τ =
      ∫ x, τ x * z.val.2 j x ∂ν[n] := by
    simpa only [j, jetDirections_jetIndexOfList, List.map_cons, List.map_nil] using hD j τ
  change dirichletWeakDerivativeTest (z.val.2 j) (dirichletJetDirections b i) ψ =
    ∫ x, ψ x * z.val.2 (appendCoordinateIndex a i) x ∂ν[n]
  rw [← dirichletWeakDerivativeTest_append_singleton (b a) hSingle,
    ← jetDirections_appendCoordinateIndex b a i]
  exact hD _ ψ

theorem dirichletSobolevJetGraph_derivative_test {n k : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (a : Fin (2 * n))
    (z : dirichletSobolevJetGraph (k := k + 1) b) (ψ : 𝓓B[n]) :
    dirichletWeakDerivativeTest z.val.1 [b a] ψ =
      ∫ x, ψ x * (dirichletSobolevJetGraph_derivative b a z).val.1 x ∂ν[n] := by
  let j : DirichletJetIndex n (k + 1) := jetIndexOfList [a] (by simp)
  have h := (mem_dirichletSobolevJetGraph_iff b z.val).mp z.property j ψ
  rw [show dirichletJetDirections b j = [b a] by simp [j, jetDirections_jetIndexOfList]] at h
  exact h

/-- For smooth functions the bounded coordinate derivative is the
Sobolev jet of the ordinary coordinate derivative. -/
theorem dirichletSobolevJetGraph_derivative_ofSmooth {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (a : Fin (2 * n))
    {f : E n → ℝ} (hf : ContDiff ℝ ∞ f) :
    dirichletSobolevJetGraph_derivative (k := k) b a
      (dirichletSobolevJetOfSmooth hn b hf) =
      dirichletSobolevJetOfSmooth hn b ((hf.fderiv_right (by simp)).clm_apply
        (contDiff_const (c := b a))) := by
  let j : DirichletJetIndex n (k + 1) := jetIndexOfList [a] (by simp)
  let hD : ContDiff ℝ ∞ (fun x => fderiv ℝ f x (b a)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  apply dirichletSobolevJetGraph_fst_injective hn b
  change (dirichletSobolevJetOfSmooth (k := k + 1) hn b hf).val.2 j =
    (dirichletSobolevJetOfSmooth (k := k) hn b hD).val.1
  apply Lp.ext
  have he := dirichletSobolevJetOfSmooth_snd_ae (k := k + 1) hn b hf j
  rw [show dirichletJetDirections b j = [b a] by simp [j, jetDirections_jetIndexOfList]] at he
  exact he.trans (dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b hD).symm

/-- Real second derivatives in coordinate directions are bounded from H^(k+2)
to H^k. The index order follows the manuscript's real Hessian. -/
noncomputable def dirichletSobolevRealHessianEntry {n k : ℕ}
    (a c : Fin (2 * n)) :
    dirichletSobolevJetGraph (k := k + 2) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) →L[ℝ]
      dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ) :=
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  (dirichletSobolevJetGraph_derivative b a).comp (dirichletSobolevJetGraph_derivative b c)

theorem dirichletSobolevRealHessianEntry_ofSmooth_ae {n k : ℕ} (hn : 0 < n)
    (a c : Fin (2 * n)) {f : E n → ℝ} (hf : ContDiff ℝ ∞ f) :
    let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
    (dirichletSobolevRealHessianEntry (k := k) a c
      (dirichletSobolevJetOfSmooth hn b hf)).val.1 =ᵐ[ν[n]]
      fun x => realHessian f x (b a) (b c) := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  change (dirichletSobolevJetGraph_derivative (k := k) b a
    (dirichletSobolevJetGraph_derivative b c (dirichletSobolevJetOfSmooth hn b hf))).val.1 =ᵐ[ν[n]] _
  rw [dirichletSobolevJetGraph_derivative_ofSmooth hn b c hf,
    dirichletSobolevJetGraph_derivative_ofSmooth]
  refine (dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b _).trans ?_
  exact Eventually.of_forall fun x => by
    have h : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    change fderiv ℝ (fun y => fderiv ℝ f y (b c)) x (b a) = realHessian f x (b a) (b c)
    rw [fderiv_clm_apply h (differentiableAt_const (b c))]
    simp [realHessian]

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

/-- The complex Hessian, represented by its real and imaginary Sobolev
components, is bounded from H^(k+2) to H^k entrywise. -/
noncomputable def dirichletSobolevComplexHessianEntry {n k : ℕ} (i j : Fin n) :
    (CoordinateSobolev n (k + 2)) →L[ℝ] (CoordinateSobolev n k × CoordinateSobolev n k) :=
  ((4 : ℝ)⁻¹ • (dirichletSobolevRealHessianEntry (realIndex i) (realIndex j) +
      dirichletSobolevRealHessianEntry (imagIndex i) (imagIndex j))).prod
  ((4 : ℝ)⁻¹ • (dirichletSobolevRealHessianEntry (realIndex i) (imagIndex j) -
      dirichletSobolevRealHessianEntry (imagIndex i) (realIndex j)))

theorem dirichletSobolevComplexHessianEntry_ofSmooth_ae {n k : ℕ} (hn : 0 < n)
    (i j : Fin n) {f : E n → ℝ} (hf : ContDiff ℝ ∞ f) :
    let z : (CoordinateSobolev n (k + 2)) := dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hf
    let T := dirichletSobolevComplexHessianEntry i j z
    (fun x => (T.1.val.1 x : ℂ) + Complex.I * (T.2.val.1 x : ℂ)) =ᵐ[ν[n]]
      fun x => complexHessian f x i j := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let z : (CoordinateSobolev n (k + 2)) := dirichletSobolevJetOfSmooth hn b hf
  let RR := dirichletSobolevRealHessianEntry (k := k) (realIndex i) (realIndex j) z
  let II := dirichletSobolevRealHessianEntry (k := k) (imagIndex i) (imagIndex j) z
  let RI := dirichletSobolevRealHessianEntry (k := k) (realIndex i) (imagIndex j) z
  let IR := dirichletSobolevRealHessianEntry (k := k) (imagIndex i) (realIndex j) z
  let r := (4 : ℝ)⁻¹
  change (fun x => ((r • (RR.val.1 + II.val.1) : DirichletBallL2 n ℝ) x : ℂ) +
    Complex.I * ((r • (RI.val.1 - IR.val.1) : DirichletBallL2 n ℝ) x : ℂ)) =ᵐ[ν[n]] _
  have hRR := dirichletSobolevRealHessianEntry_ofSmooth_ae (k := k) hn (realIndex i) (realIndex j) hf
  have hII := dirichletSobolevRealHessianEntry_ofSmooth_ae (k := k) hn (imagIndex i) (imagIndex j) hf
  have hRI := dirichletSobolevRealHessianEntry_ofSmooth_ae (k := k) hn (realIndex i) (imagIndex j) hf
  have hIR := dirichletSobolevRealHessianEntry_ofSmooth_ae (k := k) hn (imagIndex i) (realIndex j) hf
  have hBReal (a : Fin n) : b (realIndex a) = realDirection a :=
    EuclideanSpace.basisFun_apply _ _ _
  have hBImag (a : Fin n) : b (imagIndex a) = imagDirection a :=
    EuclideanSpace.basisFun_apply _ _ _
  filter_upwards [hRR, hII, hRI, hIR, Lp.coeFn_add RR.val.1 II.val.1, Lp.coeFn_sub RI.val.1 IR.val.1,
    Lp.coeFn_smul r (RR.val.1 + II.val.1), Lp.coeFn_smul r (RI.val.1 - IR.val.1)]
    with x hrr hii hri hir hAdd hSub hR hI
  change RR.val.1 x = realHessian f x (b (realIndex i)) (b (realIndex j)) at hrr
  change II.val.1 x = realHessian f x (b (imagIndex i)) (b (imagIndex j)) at hii
  change RI.val.1 x = realHessian f x (b (realIndex i)) (b (imagIndex j)) at hri
  change IR.val.1 x = realHessian f x (b (imagIndex i)) (b (realIndex j)) at hir
  rw [complexHessian_real_entry hf.contDiffAt i j, hR, hI]
  simp only [Pi.smul_apply, smul_eq_mul, hAdd, hSub, Pi.add_apply, Pi.sub_apply,
    hrr, hii, hri, hir, hBReal, hBImag, r, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_sub]
  ring

end KEBall
