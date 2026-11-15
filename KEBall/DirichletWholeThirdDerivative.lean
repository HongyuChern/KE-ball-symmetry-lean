import KEBall.DirichletWholeSecondDerivative

/-! Third weak derivatives of whole-space divergence-form solutions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal

namespace KEBall

local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)

/-- The weak equation on compactly supported tests in the ambient space. -/
theorem IsEuclideanWeakSolution.integral_fderiv_test {n : ℕ}
    {A : E n → E n →L[ℝ] E n} {hA : MemLp A ⊤ (volume0 n)}
    {g : EuclideanL2 n ℝ} {u : EuclideanSobolev n}
    (hu : IsEuclideanWeakSolution hA g u) (ψ : 𝓓E[n]) :
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((u : EuclideanL2Pair n).snd x)) ∂volume0 n) =
      ∫ x, ψ x * g x ∂volume0 n := by
  let w : EuclideanSobolev n := ⟨compactTestL2Graph (volume0 n) ψ,
    subset_closure (LinearMap.mem_range_self (compactTestL2Graph (volume0 n)) ψ)⟩
  let F := euclideanCoefficientAction hA (u : EuclideanL2Pair n).snd
  have he := hu w
  change inner ℝ F (compactTestGradientToL2 (volume0 n) ψ) =
    inner ℝ g (compactTestToL2 (volume0 n) ψ) at he
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at he
  refine Eq.trans ?_ (he.trans ?_)
  · apply integral_congr_ae
    filter_upwards [euclideanCoefficientAction_ae hA (u : EuclideanL2Pair n).snd,
      compactTestGradientToL2_ae (volume0 n) ψ] with x hF hψ
    change F x = _ at hF
    rw [hF, hψ, real_inner_comm, inner_gradient_left]
  · apply integral_congr_ae
    filter_upwards [compactTestToL2_ae (volume0 n) ψ] with x hx
    rw [hx, Real.inner_apply, mul_comm]

/-- A compactly supported smooth scalar test times an ambient L² function is integrable. -/
theorem integrable_euclideanTest_mul {n : ℕ} (ψ : 𝓓E[n]) {f : E n → ℝ}
    (hf : MemLp f 2 (volume0 n)) : Integrable (fun x => ψ x * f x) (volume0 n) := by
  have hψ : MemLp (ψ : E n → ℝ) 2 (volume0 n) :=
    ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  exact memLp_one_iff_integrable.mp (hf.mul' hψ)

theorem euclideanTest_lineDeriv_apply {n : ℕ} (ψ : 𝓓E[n]) (d x : E n) :
    (TestFunction.lineDerivCLM ℝ d ψ : 𝓓E[n]) x = fderiv ℝ (ψ : E n → ℝ) x d := by
  rw [TestFunction.lineDerivCLM_eq_fderivCLM]
  have hψ := TestFunction.fderivCLM_apply_of_le (𝕜 := ℝ) (k := (⊤ : ℕ∞)) ψ (by simp)
  exact congrArg (fun (T : E n →L[ℝ] ℝ) => T d) (congrFun hψ x)

private noncomputable def euclideanTestMul {n : ℕ} (ψ : 𝓓E[n])
    {c : E n → ℝ} (hc : ContDiff ℝ ∞ c) : 𝓓E[n] :=
  ⟨fun x => ψ x * c x, ψ.contDiff.mul hc, ψ.hasCompactSupport.mul_right, subset_univ _⟩

/-- The weak directional derivative of an L² function multiplied by a smooth
bounded coefficient obeys the ordinary product rule. -/
theorem euclideanWeakDerivative_mul {n : ℕ} {f F c : E n → ℝ} (d : E n)
    (hf : MemLp f 2 (volume0 n)) (hF : MemLp F 2 (volume0 n))
    (hc : ContDiff ℝ ∞ c) (hc₀ : MemLp c ⊤ (volume0 n))
    (hc₁ : MemLp (fun x => fderiv ℝ c x d) ⊤ (volume0 n))
    (hWeak : ∀ ψ : 𝓓E[n], (∫ x, ψ x * F x ∂volume0 n) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂volume0 n)) :
    MemLp (fun x => c x * F x + fderiv ℝ c x d * f x) 2 (volume0 n) ∧
    ∀ ψ : 𝓓E[n], (∫ x, ψ x * (c x * F x + fderiv ℝ c x d * f x) ∂volume0 n) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * (c x * f x) ∂volume0 n) := by
  have h₀ : MemLp (fun x => c x * F x) 2 (volume0 n) := hF.mul' hc₀
  have h₁ : MemLp (fun x => fderiv ℝ c x d * f x) 2 (volume0 n) := hf.mul' hc₁
  have h₂ : MemLp (fun x => c x * f x) 2 (volume0 n) := hf.mul' hc₀
  refine ⟨h₀.add h₁, fun ψ => ?_⟩
  let τ := euclideanTestMul ψ hc
  let χ : 𝓓E[n] := TestFunction.lineDerivCLM ℝ d ψ
  have hχ (x : E n) : χ x = fderiv ℝ (ψ : E n → ℝ) x d :=
    euclideanTest_lineDeriv_apply ψ d x
  have hD (x : E n) : fderiv ℝ (τ : E n → ℝ) x d * f x =
      χ x * (c x * f x) + ψ x * (fderiv ℝ c x d * f x) := by
    change fderiv ℝ (fun y => ψ y * c y) x d * f x = _
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (hc.differentiable (by simp) x), hχ]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have h := hWeak τ
  simp_rw [hD, integral_add (integrable_euclideanTest_mul χ h₂)
    (integrable_euclideanTest_mul ψ h₁)] at h
  have hτ (x : E n) : τ x * F x = ψ x * (c x * F x) := by
    change (ψ x * c x) * F x = _
    rw [mul_assoc]
  simp_rw [hτ] at h
  simp_rw [mul_add, integral_add (integrable_euclideanTest_mul ψ h₀)
    (integrable_euclideanTest_mul ψ h₁), ← hχ]
  linarith only [h]

/-- Differentiate a component of a smooth matrix field times a weakly
differentiable vector field. -/
theorem euclideanWeakDerivative_coefficientPair {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d e : E n)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    (hB₀ : MemLp B ⊤ (volume0 n))
    (hB₁ : MemLp (fun x => fderiv ℝ B x d) ⊤ (volume0 n))
    (U H : EuclideanL2 n (E n))
    (hWeak : ∀ (ψ : 𝓓E[n]) (w : E n),
      (∫ x, ψ x * inner ℝ w (H x) ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * inner ℝ w (U x) ∂volume0 n)) :
    let Q (x : E n) := inner ℝ e (B x (H x) + fderiv ℝ B x d (U x))
    MemLp Q 2 (volume0 n) ∧
      ∀ ψ : 𝓓E[n], (∫ x, ψ x * Q x ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * inner ℝ e (B x (U x)) ∂volume0 n) := by
  let L (i : Fin (2 * n)) : (E n →L[ℝ] E n) →L[ℝ] ℝ :=
    (innerSL ℝ e).comp (ContinuousLinearMap.apply ℝ (E n) (b i))
  let c (i : Fin (2 * n)) (x : E n) := L i (B x)
  let D (x : E n) := fderiv ℝ B x d
  let Q (i : Fin (2 * n)) (x : E n) :=
    c i x * inner ℝ (b i) (H x) + L i (D x) * inner ℝ (b i) (U x)
  let P (i : Fin (2 * n)) (x : E n) := c i x * inner ℝ (b i) (U x)
  have hDc (i : Fin (2 * n)) (x : E n) : fderiv ℝ (c i) x d = L i (D x) := by
    change fderiv ℝ ((L i) ∘ B) x d = _
    rw [(L i).hasFDerivAt.comp x (hB.differentiable (by simp) x).hasFDerivAt |>.fderiv]
    rfl
  have hc₀ (i : Fin (2 * n)) : MemLp (c i) ⊤ (volume0 n) := (L i).comp_memLp' hB₀
  have hc₁ (i : Fin (2 * n)) : MemLp (fun x => fderiv ℝ (c i) x d) ⊤ (volume0 n) := by
    simp only [hDc]
    exact (L i).comp_memLp' hB₁
  have hProd (i : Fin (2 * n)) := euclideanWeakDerivative_mul (c := c i) d
    ((Lp.memLp U).const_inner (b i)) ((Lp.memLp H).const_inner (b i))
    ((L i).contDiff.comp hB) (hc₀ i) (hc₁ i) (fun ψ => hWeak ψ (b i))
  have hP (i : Fin (2 * n)) : MemLp (P i) 2 (volume0 n) :=
    ((Lp.memLp U).const_inner (b i)).mul' (hc₀ i)
  have hQ (i : Fin (2 * n)) : MemLp (Q i) 2 (volume0 n) := by
    simpa only [Q, ← hDc] using (hProd i).1
  have hEq (i : Fin (2 * n)) (ψ : 𝓓E[n]) :
      (∫ x, ψ x * Q i x ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * P i x ∂volume0 n) := by
    simpa only [Q, ← hDc, P] using (hProd i).2 ψ
  have hCoord (T : E n →L[ℝ] E n) (y : E n) :
      (∑ i, L i T * inner ℝ (b i) y) = inner ℝ e (T y) := by
    calc
      _ = inner ℝ e (T (∑ i, inner ℝ (b i) y • b i)) := by
        simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
          map_sum, map_smul, inner_sum, real_inner_smul_right]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = _ := by rw [b.sum_repr']
  have hSumP (x : E n) : (∑ i, P i x) = inner ℝ e (B x (U x)) :=
    hCoord (B x) (U x)
  have hSumQ (x : E n) : (∑ i, Q i x) = inner ℝ e (B x (H x) + D x (U x)) := by
    simp only [Q, c, Finset.sum_add_distrib, hCoord, inner_add_right]
  refine ⟨MemLp.ae_eq (Eventually.of_forall hSumQ)
    (memLp_finsetSum Finset.univ fun i _ => hQ i), fun ψ => ?_⟩
  let τ : 𝓓E[n] := TestFunction.lineDerivCLM ℝ d ψ
  have hτ (x : E n) : τ x = fderiv ℝ (ψ : E n → ℝ) x d :=
    euclideanTest_lineDeriv_apply ψ d x
  change (∫ x, ψ x * inner ℝ e (B x (H x) + D x (U x)) ∂volume0 n) =
    -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * inner ℝ e (B x (U x)) ∂volume0 n)
  simp_rw [← hSumP, ← hSumQ, ← hτ, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_euclideanTest_mul ψ (hQ i)),
    integral_finsetSum _ (fun i _ => integrable_euclideanTest_mul τ (hP i)), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simpa only [hτ] using hEq i ψ

theorem memLp_euclideanCoefficient_pairing {n : ℕ}
    {B : E n → E n →L[ℝ] E n} (hB : MemLp B ⊤ (volume0 n))
    (U : EuclideanL2 n (E n)) (e : E n) :
    MemLp (fun x => inner ℝ e (B x (U x))) 2 (volume0 n) := by
  refine MemLp.ae_eq ?_ ((Lp.memLp (euclideanCoefficientAction hB U)).const_inner e)
  filter_upwards [euclideanCoefficientAction_ae hB U] with x hx
  exact congrArg (inner ℝ e) hx

theorem integral_euclideanTest_fderiv_basis {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (ψ : 𝓓E[n])
    {B : E n → E n →L[ℝ] E n} (hB : MemLp B ⊤ (volume0 n))
    (U : EuclideanL2 n (E n)) :
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x (U x)) ∂volume0 n) =
      ∑ i, ∫ x, (TestFunction.lineDerivCLM ℝ (b i) ψ : 𝓓E[n]) x *
        inner ℝ (b i) (B x (U x)) ∂volume0 n := by
  rw [← integral_finsetSum _ (fun i _ => integrable_euclideanTest_mul _ (
    memLp_euclideanCoefficient_pairing hB U (b i)))]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [euclideanTest_lineDeriv_apply]
    let T := fderiv ℝ (ψ : E n → ℝ) x
    calc
      T (B x (U x)) = T (∑ i, inner ℝ (b i) (B x (U x)) • b i) := by rw [b.sum_repr']
      _ = _ := by simp [T, mul_comm]

/-- The divergence of a bounded smooth matrix times a vector field with L²
weak first derivatives is represented in L². -/
theorem exists_euclideanGradientDivergence_L2 {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (U : EuclideanL2 n (E n))
    (hU : ∀ d : E n, ∃ H : EuclideanL2 n (E n), ∀ (ψ : 𝓓E[n]) (e : E n),
      (∫ x, ψ x * inner ℝ e (H x) ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * inner ℝ e (U x) ∂volume0 n))
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    (hB₀ : MemLp B ⊤ (volume0 n))
    (hB₁ : ∀ d : E n, MemLp (fun x => fderiv ℝ B x d) ⊤ (volume0 n)) :
    ∃ f : EuclideanL2 n ℝ, ∀ ψ : 𝓓E[n],
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x (U x)) ∂volume0 n) =
        -(∫ x, ψ x * f x ∂volume0 n) := by
  choose H hH using hU
  let F (i : Fin (2 * n)) (x : E n) :=
    inner ℝ (b i) (B x (H (b i) x) + fderiv ℝ B x (b i) (U x))
  have hPair (i : Fin (2 * n)) := euclideanWeakDerivative_coefficientPair b (b i) (b i)
    hB hB₀ (hB₁ (b i)) U (H (b i)) (hH (b i))
  have hF (i : Fin (2 * n)) : MemLp (F i) 2 (volume0 n) := (hPair i).1
  let f (x : E n) := ∑ i, F i x
  have hf : MemLp f 2 (volume0 n) := memLp_finsetSum Finset.univ fun i _ => hF i
  refine ⟨hf.toLp f, fun ψ => ?_⟩
  have hLp : (∫ x, ψ x * hf.toLp f x ∂volume0 n) = ∫ x, ψ x * f x ∂volume0 n := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hf] with x hx
    rw [hx]
  rw [hLp, integral_euclideanTest_fderiv_basis b ψ hB₀ U]
  simp_rw [f, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_euclideanTest_mul ψ (hF i)), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simpa only [euclideanTest_lineDeriv_apply, neg_neg] using congrArg Neg.neg ((hPair i).2 ψ).symm

private theorem euclideanTest_lineDeriv_comm {n : ℕ} (ψ : 𝓓E[n]) (d e x : E n) :
    fderiv ℝ (TestFunction.lineDerivCLM ℝ e ψ : 𝓓E[n]).toFun x d =
      (TestFunction.lineDerivCLM ℝ e (TestFunction.lineDerivCLM ℝ d ψ : 𝓓E[n]) : 𝓓E[n]) x := by
  rw [euclideanTest_lineDeriv_apply]
  have he : ((TestFunction.lineDerivCLM ℝ e ψ : 𝓓E[n]) : E n → ℝ) =
      fun y => fderiv ℝ (ψ : E n → ℝ) y e := funext (euclideanTest_lineDeriv_apply ψ e)
  have hd : ((TestFunction.lineDerivCLM ℝ d ψ : 𝓓E[n]) : E n → ℝ) =
      fun y => fderiv ℝ (ψ : E n → ℝ) y d := funext (euclideanTest_lineDeriv_apply ψ d)
  change fderiv ℝ ((TestFunction.lineDerivCLM ℝ e ψ : 𝓓E[n]) : E n → ℝ) x d = _
  rw [he, hd]
  have hD := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hD (differentiableAt_const e), fderiv_clm_apply hD (differentiableAt_const d)]
  simpa using (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast) |>.eq d e

/-- The weak derivative of the flux gives the differentiated test identity
for the divergence-form equation. -/
theorem IsEuclideanWeakSolution.integral_fderiv_weakDerivative {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) {hA₀ : MemLp A ⊤ (volume0 n)}
    (hA₁ : MemLp (fun x => fderiv ℝ A x d) ⊤ (volume0 n))
    {u v : EuclideanSobolev n} {g : EuclideanL2 n ℝ}
    (hu : IsEuclideanWeakSolution hA₀ g u)
    (hv : ∀ (ψ : 𝓓E[n]) (e : E n),
      (∫ x, ψ x * inner ℝ e ((v : EuclideanL2Pair n).snd x) ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d *
          inner ℝ e ((u : EuclideanL2Pair n).snd x) ∂volume0 n))
    (ψ : 𝓓E[n]) :
    let η : 𝓓E[n] := TestFunction.lineDerivCLM ℝ d ψ
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((v : EuclideanL2Pair n).snd x)) ∂volume0 n) +
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x (fderiv ℝ A x d ((u : EuclideanL2Pair n).snd x)) ∂volume0 n) =
      -(∫ x, η x * g x ∂volume0 n) := by
  let U := (u : EuclideanL2Pair n).snd
  let V := (v : EuclideanL2Pair n).snd
  let D (x : E n) := fderiv ℝ A x d
  let η : 𝓓E[n] := TestFunction.lineDerivCLM ℝ d ψ
  let χ (i : Fin (2 * n)) : 𝓓E[n] := TestFunction.lineDerivCLM ℝ (b i) ψ
  let ξ (i : Fin (2 * n)) : 𝓓E[n] := TestFunction.lineDerivCLM ℝ (b i) η
  have hTerm (i : Fin (2 * n)) :
      (∫ x, χ i x * inner ℝ (b i) (A x (V x)) ∂volume0 n) +
        (∫ x, χ i x * inner ℝ (b i) (D x (U x)) ∂volume0 n) =
        -(∫ x, ξ i x * inner ℝ (b i) (A x (U x)) ∂volume0 n) := by
    have h := (euclideanWeakDerivative_coefficientPair b d (b i) hA hA₀ hA₁ U V hv).2 (χ i)
    change (∫ x, χ i x * inner ℝ (b i) (A x (V x) + D x (U x)) ∂volume0 n) =
      -(∫ x, fderiv ℝ (χ i : E n → ℝ) x d * inner ℝ (b i) (A x (U x)) ∂volume0 n) at h
    have hξ (x : E n) : fderiv ℝ (χ i : E n → ℝ) x d = ξ i x :=
      euclideanTest_lineDeriv_comm ψ d (b i) x
    have hI₀ : Integrable (fun x => χ i x * inner ℝ (b i) (A x (V x))) (volume0 n) :=
      integrable_euclideanTest_mul (χ i) (memLp_euclideanCoefficient_pairing hA₀ V (b i))
    have hI₁ : Integrable (fun x => χ i x * inner ℝ (b i) (D x (U x))) (volume0 n) :=
      integrable_euclideanTest_mul (χ i) (memLp_euclideanCoefficient_pairing hA₁ U (b i))
    simp only [hξ, inner_add_right, mul_add] at h
    rw [integral_add hI₀ hI₁] at h
    exact h
  change (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x (V x)) ∂volume0 n) +
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x (D x (U x)) ∂volume0 n) =
      -(∫ x, η x * g x ∂volume0 n)
  rw [← hu.integral_fderiv_test η, integral_euclideanTest_fderiv_basis b ψ hA₀ V,
    integral_euclideanTest_fderiv_basis b ψ hA₁ U, integral_euclideanTest_fderiv_basis b η hA₀ U,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hTerm i

/-- Assemble the differentiated equation from the derivative of the forcing
and the divergence of the differentiated coefficient times the gradient. -/
theorem IsEuclideanWeakSolution.weakDerivative_solution_of_divergence {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) {hA₀ : MemLp A ⊤ (volume0 n)}
    (hA₁ : MemLp (fun x => fderiv ℝ A x d) ⊤ (volume0 n))
    {u v : EuclideanSobolev n} {g gD f : EuclideanL2 n ℝ}
    (hu : IsEuclideanWeakSolution hA₀ g u)
    (hg : ∀ ψ : 𝓓E[n], (∫ x, ψ x * gD x ∂volume0 n) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * g x ∂volume0 n))
    (hv : ∀ (ψ : 𝓓E[n]) (e : E n),
      (∫ x, ψ x * inner ℝ e ((v : EuclideanL2Pair n).snd x) ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d *
          inner ℝ e ((u : EuclideanL2Pair n).snd x) ∂volume0 n))
    (hf : ∀ ψ : 𝓓E[n],
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x
        (fderiv ℝ A x d ((u : EuclideanL2Pair n).snd x)) ∂volume0 n) =
        -(∫ x, ψ x * f x ∂volume0 n)) :
    IsEuclideanWeakSolution hA₀ (gD + f) v := by
  refine IsEuclideanWeakSolution.of_test hA₀ _ v fun ψ => ?_
  have h := hu.integral_fderiv_weakDerivative b d hA hA₁ hv ψ
  change (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((v : EuclideanL2Pair n).snd x)) ∂volume0 n) +
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x (fderiv ℝ A x d ((u : EuclideanL2Pair n).snd x)) ∂volume0 n) =
    -(∫ x, (TestFunction.lineDerivCLM ℝ d ψ : 𝓓E[n]) x * g x ∂volume0 n) at h
  simp_rw [euclideanTest_lineDeriv_apply] at h
  rw [← hg ψ, hf ψ] at h
  have hRight : (∫ x, ψ x * (gD + f) x ∂volume0 n) =
      (∫ x, ψ x * gD x ∂volume0 n) + ∫ x, ψ x * f x ∂volume0 n := by
    rw [← integral_add (integrable_euclideanTest_mul ψ (Lp.memLp gD))
      (integrable_euclideanTest_mul ψ (Lp.memLp f))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add gD f] with x hx
    rw [hx, Pi.add_apply, mul_add]
  rw [hRight]
  linarith only [h]

/-- If the forcing has an L² derivative and the coefficient derivatives are
bounded, the derivative in the Sobolev graph solves a whole-space weak equation. -/
theorem IsEuclideanWeakSolution.exists_weakDerivative_solution {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) {hA₀ : MemLp A ⊤ (volume0 n)}
    (hA₁ : MemLp (fun x => fderiv ℝ A x d) ⊤ (volume0 n))
    (hA₂ : ∀ e : E n, MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ A y d) x e) ⊤ (volume0 n))
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂volume0 n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLip : LipschitzWith K A)
    {u : EuclideanSobolev n} {g gD : EuclideanL2 n ℝ}
    (hu : IsEuclideanWeakSolution hA₀ g u)
    (hg : ∀ ψ : 𝓓E[n], (∫ x, ψ x * gD x ∂volume0 n) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * g x ∂volume0 n)) :
    ∃ (v : EuclideanSobolev n) (g' : EuclideanL2 n ℝ),
      IsEuclideanWeakSolution hA₀ g' v ∧
      ∀ (ψ : 𝓓E[n]) (e : E n),
        (∫ x, ψ x * inner ℝ e ((v : EuclideanL2Pair n).snd x) ∂volume0 n) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d *
            inner ℝ e ((u : EuclideanL2Pair n).snd x) ∂volume0 n) := by
  obtain ⟨v, _, hv⟩ := exists_euclideanSobolev_weakDerivative hA₀ hl hE hLip hu d
  have hD : ContDiff ℝ ∞ (fun x => fderiv ℝ A x d) :=
    (hA.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨f, hf⟩ := exists_euclideanGradientDivergence_L2 b (u : EuclideanL2Pair n).snd
    (exists_euclideanGradient_weakDerivative hA₀ hl hE hLip hu) hD hA₁ hA₂
  exact ⟨v, gD + f, hu.weakDerivative_solution_of_divergence b d hA hA₁ hg hv hf, hv⟩

/-- If the forcing has a square-integrable directional weak derivative, the
gradient of the whole-space solution has a square-integrable second weak
derivative in that direction and any other fixed direction. -/
theorem IsEuclideanWeakSolution.exists_secondGradientWeakDerivative {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d v : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A) {hA₀ : MemLp A ⊤ (volume0 n)}
    (hA₁ : MemLp (fun x => fderiv ℝ A x d) ⊤ (volume0 n))
    (hA₂ : ∀ e : E n, MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ A y d) x e) ⊤ (volume0 n))
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂volume0 n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLip : LipschitzWith K A)
    {u : EuclideanSobolev n} {g gD : EuclideanL2 n ℝ}
    (hu : IsEuclideanWeakSolution hA₀ g u)
    (hg : ∀ ψ : 𝓓E[n], (∫ x, ψ x * gD x ∂volume0 n) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * g x ∂volume0 n)) :
    ∃ H J : EuclideanL2 n (E n), ∀ (ψ : 𝓓E[n]) (e : E n),
      ((∫ x, ψ x * inner ℝ e (H x) ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d *
          inner ℝ e ((u : EuclideanL2Pair n).snd x) ∂volume0 n)) ∧
      ((∫ x, ψ x * inner ℝ e (J x) ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ e (H x) ∂volume0 n)) := by
  obtain ⟨w, _, hw, hH⟩ := hu.exists_weakDerivative_solution b d hA hA₁ hA₂ hl hE hLip hg
  obtain ⟨J, hJ⟩ := exists_euclideanGradient_weakDerivative hA₀ hl hE hLip hw v
  exact ⟨(w : EuclideanL2Pair n).snd, J, fun ψ e => ⟨hH ψ e, hJ ψ e⟩⟩

end KEBall
