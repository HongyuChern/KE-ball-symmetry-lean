import KEBall.DirichletWholeWeakGradient

/-! Fourth weak derivatives for the whole-space localized equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)

/-- A smooth coefficient times a vector field with two L² derivatives has
an L² divergence with an L² weak gradient. -/
theorem exists_euclideanGradientDivergence_with_weakGradient {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (U : EuclideanL2 n (E n))
    (hU : ∀ d : E n, ∃ H : EuclideanL2 n (E n), IsEuclideanVectorWeakDerivative U H d ∧
      ∀ e : E n, ∃ J : EuclideanL2 n (E n), IsEuclideanVectorWeakDerivative H J e)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) (hB₀ : MemLp B ⊤ (volume0 n))
    (hB₁ : ∀ d : E n, MemLp (fun x => fderiv ℝ B x d) ⊤ (volume0 n))
    (hB₂ : ∀ d e : E n, MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ B y d) x e) ⊤ (volume0 n)) :
    ∃ f : EuclideanL2 n ℝ, HasEuclideanWeakGradientL2 f ∧ ∀ ψ : 𝓓E[n],
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x (U x)) ∂volume0 n) =
        -(∫ x, ψ x * f x ∂volume0 n) := by
  have hU' (d : E n) := hU d
  choose H hH hJ using hU'
  let D (i : Fin (2 * n)) (x : E n) := fderiv ℝ B x (b i)
  have hD (i : Fin (2 * n)) : ContDiff ℝ ∞ (D i) :=
    (hB.fderiv_right (by simp)).clm_apply contDiff_const
  let P (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (B x (H (b i) x))
  let Q (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (D i x (U x))
  let F (i : Fin (2 * n)) (x : E n) := P i x + Q i x
  have hP (i : Fin (2 * n)) : MemLp (P i) 2 (volume0 n) :=
    memLp_euclideanCoefficient_pairing hB₀ (H (b i)) (b i)
  have hQ (i : Fin (2 * n)) : MemLp (Q i) 2 (volume0 n) :=
    memLp_euclideanCoefficient_pairing (hB₁ (b i)) U (b i)
  have hF (i : Fin (2 * n)) : MemLp (F i) 2 (volume0 n) := (hP i).add (hQ i)
  let f (x : E n) := ∑ i, F i x
  have hf : MemLp f 2 (volume0 n) := memLp_finsetSum Finset.univ fun i _ => hF i
  let f₂ := hf.toLp f
  have hInt (φ : 𝓓E[n]) : (∫ x, φ x * f₂ x ∂volume0 n) = ∫ x, φ x * f x ∂volume0 n := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hf] with x hx
    change φ x * hf.toLp f x = _
    rw [hx]
  refine ⟨f₂, ?_, fun ψ => ?_⟩
  · intro d
    have hDir (i : Fin (2 * n)) : ∃ R : E n → ℝ, MemLp R 2 (volume0 n) ∧ ∀ ψ : 𝓓E[n],
        (∫ x, ψ x * R x ∂volume0 n) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * F i x ∂volume0 n) := by
      obtain ⟨J, heJ⟩ := hJ (b i) d
      let L (x : E n) := inner ℝ (b i) (B x (J x) + fderiv ℝ B x d (H (b i) x))
      let R (x : E n) := inner ℝ (b i)
        (D i x (H d x) + fderiv ℝ (D i) x d (U x))
      have heL := euclideanWeakDerivative_coefficientPair b d (b i) hB hB₀ (hB₁ d)
        (H (b i)) J heJ
      have heR := euclideanWeakDerivative_coefficientPair b d (b i) (hD i) (hB₁ (b i))
        (hB₂ (b i) d) U (H d) (hH d)
      have hL : MemLp L 2 (volume0 n) := heL.1
      have hR : MemLp R 2 (volume0 n) := heR.1
      refine ⟨L + R, hL.add hR, fun ψ => ?_⟩
      let τ : 𝓓E[n] := TestFunction.lineDerivCLM ℝ d ψ
      have hτ (x : E n) : fderiv ℝ (ψ : E n → ℝ) x d = τ x :=
        (euclideanTest_lineDeriv_apply ψ d x).symm
      have h₁ := heL.2 ψ
      have h₂ := heR.2 ψ
      change (∫ x, ψ x * L x ∂volume0 n) = -(∫ x, τ x * P i x ∂volume0 n) at h₁
      change (∫ x, ψ x * R x ∂volume0 n) = -(∫ x, τ x * Q i x ∂volume0 n) at h₂
      simp_rw [hτ, Pi.add_apply, F, mul_add]
      rw [integral_add (integrable_euclideanTest_mul ψ hL) (integrable_euclideanTest_mul ψ hR),
        integral_add (integrable_euclideanTest_mul τ (hP i)) (integrable_euclideanTest_mul τ (hQ i)),
        h₁, h₂, neg_add]
    choose R hR heR using hDir
    let R' (x : E n) := ∑ i, R i x
    have hR' : MemLp R' 2 (volume0 n) := memLp_finsetSum Finset.univ fun i _ => hR i
    refine ⟨hR'.toLp R', fun ψ => ?_⟩
    let τ : 𝓓E[n] := TestFunction.lineDerivCLM ℝ d ψ
    have hτ (x : E n) : fderiv ℝ (ψ : E n → ℝ) x d = τ x :=
      (euclideanTest_lineDeriv_apply ψ d x).symm
    have he : (∫ x, ψ x * hR'.toLp R' x ∂volume0 n) = ∫ x, ψ x * R' x ∂volume0 n := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hR'] with x hx
      rw [hx]
    simp_rw [hτ]
    rw [he, hInt τ]
    simp_rw [R', f, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_euclideanTest_mul ψ (hR i)),
      integral_finsetSum _ (fun i _ => integrable_euclideanTest_mul τ (hF i)),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simpa only [hτ] using heR i ψ
  · rw [hInt ψ, integral_euclideanTest_fderiv_basis b ψ hB₀ U]
    simp_rw [f, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_euclideanTest_mul ψ (hF i)),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he := (euclideanWeakDerivative_coefficientPair b (b i) (b i) hB hB₀ (hB₁ (b i))
      U (H (b i)) (hH (b i))).2 ψ
    simp only [inner_add_right] at he
    simpa only [euclideanTest_lineDeriv_apply, neg_neg] using congrArg Neg.neg he.symm

/-- The gradient of a whole-space solution has three L² weak derivatives
if the forcing has two L² weak derivatives and the coefficients are bounded
with bounded derivatives through order three. -/
theorem IsEuclideanWeakSolution.exists_thirdGradientWeakDerivative {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d e m : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) {hA₀ : MemLp A ⊤ (volume0 n)}
    (hA₁ : ∀ d : E n, MemLp (fun x => fderiv ℝ A x d) ⊤ (volume0 n))
    (hA₂ : ∀ d e : E n, MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ A y d) x e) ⊤ (volume0 n))
    (hA₃ : ∀ d e v : E n, MemLp (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ A z d) y e) x v) ⊤ (volume0 n))
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂volume0 n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLip : LipschitzWith K A)
    {u : EuclideanSobolev n} {g : EuclideanL2 n ℝ} (hu : IsEuclideanWeakSolution hA₀ g u)
    (hg : ∀ v : E n, ∃ gV : EuclideanL2 n ℝ,
      IsEuclideanDirectionalWeakDerivative g gV v ∧ HasEuclideanWeakGradientL2 gV) :
    ∃ H J L : EuclideanL2 n (E n),
      IsEuclideanVectorWeakDerivative (u : EuclideanL2Pair n).snd H d ∧
      IsEuclideanVectorWeakDerivative H J e ∧ IsEuclideanVectorWeakDerivative J L m := by
  let U := (u : EuclideanL2Pair n).snd
  have hU (v : E n) : ∃ H : EuclideanL2 n (E n), IsEuclideanVectorWeakDerivative U H v ∧
      ∀ w : E n, ∃ J : EuclideanL2 n (E n), IsEuclideanVectorWeakDerivative H J w := by
    obtain ⟨gV, hgV, _⟩ := hg v
    obtain ⟨w, _, hw, hW⟩ := hu.exists_weakDerivative_solution b v hA (hA₁ v) (hA₂ v)
      hl hE hLip hgV
    refine ⟨(w : EuclideanL2Pair n).snd, hW, fun z => ?_⟩
    exact exists_euclideanGradient_weakDerivative hA₀ hl hE hLip hw z
  obtain ⟨gD, heD, hgD⟩ := hg d
  obtain ⟨v, _, hv⟩ := exists_euclideanSobolev_weakDerivative hA₀ hl hE hLip hu d
  have hD : ContDiff ℝ ∞ (fun x => fderiv ℝ A x d) :=
    (hA.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨f, hf, heF⟩ := exists_euclideanGradientDivergence_with_weakGradient b U hU
    hD (hA₁ d) (hA₂ d) (hA₃ d)
  have hvEq := hu.weakDerivative_solution_of_divergence b d hA (hA₁ d) heD hv heF
  obtain ⟨gE, heE⟩ := (hgD.add hf) e
  obtain ⟨J, L, heJL⟩ := hvEq.exists_secondGradientWeakDerivative b e m hA (hA₁ e) (hA₂ e)
    hl hE hLip heE
  exact ⟨(v : EuclideanL2Pair n).snd, J, L, hv, fun ψ w => (heJL ψ w).1,
    fun ψ w => (heJL ψ w).2⟩

end KEBall
