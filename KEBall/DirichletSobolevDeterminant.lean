import KEBall.DirichletSobolevDerivative
import KEBall.DirichletSobolevProduct

/-! The determinant as a smooth map between Sobolev spaces on the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff BigOperators

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private noncomputable abbrev CoordinateSobolev (n k : ℕ) :=
  dirichletSobolevJetGraph (k := k) (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)

private noncomputable def evalComplexJet {n k : ℕ}
    (z : CoordinateSobolev n k × CoordinateSobolev n k) (x : E n) : ℂ :=
  (z.1.val.1 x : ℂ) + Complex.I * (z.2.val.1 x : ℂ)

private noncomputable def mulComplexJet {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : H →L[ℝ] H →L[ℝ] H) (z w : H × H) : H × H :=
  (B z.1 w.1 - B z.2 w.2, B z.1 w.2 + B z.2 w.1)

private theorem contDiff_mulComplexJet {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (B : H →L[ℝ] H →L[ℝ] H)
    {f g : X → H × H} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => mulComplexJet B (f x) (g x)) := by
  have h₁ := B.contDiff.comp hf.fst
  have h₂ := B.contDiff.comp hf.snd
  exact ((h₁.clm_apply hg.fst).sub (h₂.clm_apply hg.snd)).prodMk
    ((h₁.clm_apply hg.snd).add (h₂.clm_apply hg.fst))

private theorem evalComplexJet_mul {n k : ℕ}
    (B : CoordinateSobolev n k →L[ℝ] CoordinateSobolev n k →L[ℝ] CoordinateSobolev n k)
    (hB : ∀ v w, (B v w).val.1 =ᵐ[ν[n]] fun x => v.val.1 x * w.val.1 x)
    (z w : CoordinateSobolev n k × CoordinateSobolev n k) :
    evalComplexJet (mulComplexJet B z w) =ᵐ[ν[n]] fun x => evalComplexJet z x * evalComplexJet w x := by
  filter_upwards [hB z.1 w.1, hB z.2 w.2, hB z.1 w.2, hB z.2 w.1,
    Lp.coeFn_sub (B z.1 w.1).val.1 (B z.2 w.2).val.1,
    Lp.coeFn_add (B z.1 w.2).val.1 (B z.2 w.1).val.1]
    with x h11 h22 h12 h21 hSub hAdd
  have hr : (evalComplexJet (mulComplexJet B z w) x).re =
      ((B z.1 w.1).val.1 - (B z.2 w.2).val.1 : DirichletBallL2 n ℝ) x := by
    simp [evalComplexJet, mulComplexJet, Complex.mul_re]
  have hi : (evalComplexJet (mulComplexJet B z w) x).im =
      ((B z.1 w.2).val.1 + (B z.2 w.1).val.1 : DirichletBallL2 n ℝ) x := by
    simp [evalComplexJet, mulComplexJet, Complex.mul_im]
  apply Complex.ext
  · rw [hr, hSub]
    simp [evalComplexJet, h11, h22, Complex.mul_re, Complex.mul_im]
  · rw [hi, hAdd]
    simp [evalComplexJet, h12, h21, Complex.mul_im, Complex.mul_re]

private noncomputable def productComplexJet {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : H →L[ℝ] H →L[ℝ] H) (one : H × H) (xs : List (H × H)) : H × H :=
  xs.foldr (mulComplexJet B) one

private theorem contDiff_productComplexJet {X H α : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (B : H →L[ℝ] H →L[ℝ] H) (one : H × H)
    (xs : List α) (v : α → X → H × H) (hv : ∀ i, ContDiff ℝ ∞ (v i)) :
    ContDiff ℝ ∞ (fun x => productComplexJet B one (xs.map (fun i => v i x))) := by
  induction xs with
  | nil => exact contDiff_const
  | cons i xs ih => exact contDiff_mulComplexJet B (hv i) ih

private theorem evalComplexJet_product {n k : ℕ}
    (B : CoordinateSobolev n k →L[ℝ] CoordinateSobolev n k →L[ℝ] CoordinateSobolev n k)
    (hB : ∀ v w, (B v w).val.1 =ᵐ[ν[n]] fun x => v.val.1 x * w.val.1 x)
    (one : CoordinateSobolev n k × CoordinateSobolev n k)
    (hOne : evalComplexJet one =ᵐ[ν[n]] fun _ => 1)
    (xs : List (CoordinateSobolev n k × CoordinateSobolev n k)) :
    evalComplexJet (productComplexJet B one xs) =ᵐ[ν[n]]
      fun x => (xs.map (fun v => evalComplexJet v x)).prod := by
  induction xs with
  | nil => exact hOne
  | cons z zs ih =>
      filter_upwards [evalComplexJet_mul B hB z (productComplexJet B one zs), ih] with x hM hI
      change evalComplexJet (mulComplexJet B z (productComplexJet B one zs)) x =
        evalComplexJet z x * (zs.map (fun v => evalComplexJet v x)).prod
      rw [hM, hI]

/-- The real determinant of the complex Hessian is a smooth Sobolev map
from H^(k+2) to H^k. On smooth functions it is the manuscript's density. -/
theorem exists_contDiff_dirichletSobolevDeterminant {n k : ℕ} (hn : 0 < n)
    (hk : 2 * (2 * n + 1) ≤ k) :
    ∃ F : CoordinateSobolev n (k + 2) → CoordinateSobolev n k, ContDiff ℝ ∞ F ∧
      ∀ (f : E n → ℝ) (hf : ContDiff ℝ ∞ f),
        (F (dirichletSobolevJetOfSmooth hn (EuclideanSpace.basisFun _ ℝ) hf)).val.1
          =ᵐ[ν[n]] fun x => (complexHessian f x).det.re := by
  classical
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let H := CoordinateSobolev n k
  let U := CoordinateSobolev n (k + 2)
  obtain ⟨B, hB⟩ := exists_dirichletSobolevJetGraph_mulCLM (k := k) hn b hk
  let one : H × H := (dirichletSobolevJetOfSmooth hn b (contDiff_const (c := (1 : ℝ))), 0)
  have hOne : evalComplexJet one =ᵐ[ν[n]] fun _ => 1 := by
    filter_upwards [dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b
      (contDiff_const (c := (1 : ℝ))), Lp.coeFn_zero ℝ 2 ν[n]] with x hx hz
    change (one.1.val.1 x : ℂ) + Complex.I * ((0 : DirichletBallL2 n ℝ) x : ℂ) = _
    rw [hx, hz]
    simp
  let P (σ : Equiv.Perm (Fin n)) (u : U) :=
    productComplexJet B one (List.ofFn (fun i => dirichletSobolevComplexHessianEntry (σ i) i u))
  let sign (σ : Equiv.Perm (Fin n)) : ℝ := ((Equiv.Perm.sign σ : ℤˣ) : ℤ)
  let F (u : U) : H := ∑ σ, sign σ • (P σ u).1
  have hSmooth (σ : Equiv.Perm (Fin n)) : ContDiff ℝ ∞ (P σ) := by
    have h := contDiff_productComplexJet B one (List.ofFn (fun i : Fin n => i))
      (fun i => (dirichletSobolevComplexHessianEntry (σ i) i : U → H × H))
      (fun i => (dirichletSobolevComplexHessianEntry (σ i) i).contDiff)
    simpa only [List.map_ofFn, Function.comp_def, P] using h
  refine ⟨F, ContDiff.sum (fun σ _ => (hSmooth σ).fst.const_smul _), fun f hf => ?_⟩
  let u : U := dirichletSobolevJetOfSmooth hn b hf
  have hP (σ : Equiv.Perm (Fin n)) : evalComplexJet (P σ u) =ᵐ[ν[n]]
      fun x => ∏ i, complexHessian f x (σ i) i := by
    have h := evalComplexJet_product B hB one hOne
      (List.ofFn (fun i => dirichletSobolevComplexHessianEntry (σ i) i u))
    have hE : ∀ᵐ x ∂ν[n], ∀ i : Fin n, evalComplexJet
        (dirichletSobolevComplexHessianEntry (σ i) i u) x = complexHessian f x (σ i) i :=
      ae_all_iff.mpr fun i => dirichletSobolevComplexHessianEntry_ofSmooth_ae (k := k) hn (σ i) i hf
    filter_upwards [h, hE] with x hx he
    rw [hx, List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => he i
  have hEval (σ : Equiv.Perm (Fin n)) : (sign σ • (P σ u).1.val.1 : DirichletBallL2 n ℝ) =ᵐ[ν[n]]
      fun x => (sign σ) * (∏ i, complexHessian f x (σ i) i).re := by
    filter_upwards [hP σ, Lp.coeFn_smul (sign σ) (P σ u).1.val.1] with x hx hs
    have hr := congrArg Complex.re hx
    have he : (evalComplexJet (P σ u) x).re = (P σ u).1.val.1 x := by
      simp [evalComplexJet, Complex.mul_re]
    rw [he] at hr
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul, hr]
  have hSum := Lp.coeFn_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun σ => sign σ • (P σ u).1.val.1)
  let first : H →ₗ[ℝ] DirichletBallL2 n ℝ :=
    LinearMap.fst ℝ _ _ ∘ₗ (dirichletSobolevJetGraph (k := k) b).subtype
  change first (∑ σ, sign σ • (P σ u).1) =ᵐ[ν[n]] _
  rw [map_sum]
  simp only [map_smul]
  change ((∑ σ, sign σ • (P σ u).1.val.1 : DirichletBallL2 n ℝ) : E n → ℝ) =ᵐ[ν[n]] _
  filter_upwards [hSum, ae_all_iff.mpr hEval] with x hx hEvalX
  rw [hx, Finset.sum_apply, Matrix.det_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hEvalX σ, Units.smul_def, zsmul_eq_mul]
  simp [sign, Complex.mul_re]

end KEBall
