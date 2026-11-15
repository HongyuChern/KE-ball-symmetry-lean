import KEBall.DirichletWholeWeakSobolev

/-! Finite-order L² regularity for whole-space elliptic solutions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)

theorem iteratedLineDerivative_contDiff {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} (hf : ContDiff ℝ ∞ f)
    (ds : List (E n)) :
    ContDiff ℝ ∞ (ds.foldr (fun d C x => fderiv ℝ C x d) f) := by
  induction ds with
  | nil => exact hf
  | cons d ds ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem memLp_iteratedLineDerivative_compL {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} (L : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hLp : ∀ ds : List (E n), MemLp (ds.foldr (fun d C x => fderiv ℝ C x d) f) ⊤ (volume0 n))
    (ds : List (E n)) :
    MemLp (ds.foldr (fun d C x => fderiv ℝ C x d) (L ∘ f)) ⊤ (volume0 n) := by
  have hEq : (ds.foldr (fun d C x => fderiv ℝ C x d) (L ∘ f)) =
      L ∘ (ds.foldr (fun d C x => fderiv ℝ C x d) f) := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
        simp only [List.foldr_cons, ih]
        funext x
        have hD := (iteratedLineDerivative_contDiff hf ds).differentiable (by simp) x
        rw [(L.hasFDerivAt.comp x hD.hasFDerivAt).fderiv]
        rfl
  rw [hEq]
  exact L.comp_memLp' (hLp ds)

theorem exists_euclideanGradientDivergence_with_weakDerivatives {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (U : EuclideanL2 n (E n)) (k : ℕ)
    (hU : ∀ v : E n, HasEuclideanWeakDerivativesL2 (fun x => inner ℝ v (U x)) (k + 1))
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    (hB₀ : ∀ ds : List (E n), MemLp (ds.foldr (fun d C x => fderiv ℝ C x d) B) ⊤ (volume0 n)) :
    ∃ d : EuclideanL2 n ℝ, HasEuclideanWeakDerivativesL2 (d : E n → ℝ) k ∧
      ∀ ψ : 𝓓E[n], (∫ x, fderiv ℝ (ψ : E n → ℝ) x
        (B x (U x)) ∂(volume0 n)) = -(∫ x, ψ x * d x ∂(volume0 n)) := by
  let V (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (U x)
  have hV (i : Fin (2 * n)) : HasEuclideanWeakDerivativesL2 (V i) (k + 1) := hU (b i)
  let W (j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (U x))
  have hW (j : Fin (2 * n)) : HasEuclideanWeakDerivativesL2 (W j) (k + 1) := by
    let c (i : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
    let L (i : Fin (2 * n)) : (E n →L[ℝ] E n) →L[ℝ] ℝ :=
      (innerSL ℝ (b j)).comp (ContinuousLinearMap.apply ℝ (E n) (b i))
    have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) := (L i).contDiff.comp hB
    have hc₀ (i : Fin (2 * n)) (ds : List (E n)) :
        MemLp (ds.foldr (fun d C x => fderiv ℝ C x d) (c i)) ⊤ (volume0 n) :=
      memLp_iteratedLineDerivative_compL (L i) hB hB₀ ds
    refine (HasEuclideanWeakDerivativesL2.finsetSum Finset.univ fun i _ =>
      (hV i).mul_smooth (hc i) (hc₀ i)).congr (Eventually.of_forall fun x => ?_)
    change (∑ i, c i x * V i x) = inner ℝ (b j) (B x (U x))
    calc
      _ = inner ℝ (b j) (B x (∑ i, V i x • b i)) := by
        simp only [map_sum, map_smul, inner_sum, real_inner_smul_right, c]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = _ := by rw [show (∑ i, V i x • b i) = U x from b.sum_repr' (U x)]
  have hDir (j : Fin (2 * n)) := (hasEuclideanWeakDerivativesL2_succ_iff.mp (hW j)).2 (b j)
  choose F hF heF using hDir
  let D (x : E n) := ∑ j, F j x
  have hD : HasEuclideanWeakDerivativesL2 D k :=
    HasEuclideanWeakDerivativesL2.finsetSum Finset.univ fun j _ => hF j
  let d := hD.1.toLp D
  refine ⟨d, hD.congr (MemLp.coeFn_toLp hD.1).symm, fun ψ => ?_⟩
  have hLp : (∫ x, ψ x * d x ∂volume0 n) = ∫ x, ψ x * D x ∂volume0 n := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hD.1] with x hx
    change ψ x * hD.1.toLp D x = _
    rw [hx]
  rw [hLp, integral_euclideanTest_fderiv_basis b ψ (B := B) (hB₀ []) U]
  simp_rw [D, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_euclideanTest_mul ψ (hF j).1),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    have he := heF j ψ
    change (∫ x, ψ x * F j x ∂volume0 n) =
      -(∫ x, euclideanTestLineDerivative (b j) ψ x * W j x ∂volume0 n) at he
    simpa only [neg_neg] using congrArg Neg.neg he.symm

/-- A weak solution with forcing of order k has an L² gradient of order
k+1, for smooth, bounded coefficients with bounded directional derivatives. -/
theorem IsEuclideanWeakSolution.hasEuclideanWeakGradientDerivativesL2 {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hAc : ContDiff ℝ ∞ A) {hA : MemLp A ⊤ (volume0 n)}
    (hBound : ∀ ds : List (E n),
      MemLp (ds.foldr (fun d C x => fderiv ℝ C x d) A) ⊤ (volume0 n))
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ᵐ x ∂volume0 n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLip : LipschitzWith K A)
    (k : ℕ) {g : EuclideanL2 n ℝ} {u : EuclideanSobolev n} (hu : IsEuclideanWeakSolution hA g u)
    (hg : HasEuclideanWeakDerivativesL2 (g : E n → ℝ) k) (e : E n) :
    HasEuclideanWeakDerivativesL2 (fun x => inner ℝ e ((u : EuclideanL2Pair n).snd x)) (k + 1) := by
  induction k generalizing g u e with
  | zero =>
      refine hasEuclideanWeakDerivativesL2_succ_iff.mpr
        ⟨(Lp.memLp (u : EuclideanL2Pair n).snd).const_inner e, fun d => ?_⟩
      obtain ⟨H, hH⟩ := exists_euclideanGradient_weakDerivative hA hl hE hLip hu d
      refine ⟨fun x => inner ℝ e (H x),
        HasEuclideanWeakDerivativesL2.zero_order ((Lp.memLp H).const_inner e), fun ψ => ?_⟩
      simpa only [euclideanTestLineDerivative, euclideanTest_lineDeriv_apply] using hH ψ e
  | succ k ih =>
      have hg₀ : HasEuclideanWeakDerivativesL2 (g : E n → ℝ) k :=
        ⟨hg.1, fun ds hs => hg.2 ds (hs.trans (Nat.le_succ _))⟩
      have hU (v : E n) := ih hu hg₀ v
      refine hasEuclideanWeakDerivativesL2_succ_iff.mpr
        ⟨(Lp.memLp (u : EuclideanL2Pair n).snd).const_inner e, fun d => ?_⟩
      obtain ⟨F, hF, heF⟩ := (hasEuclideanWeakDerivativesL2_succ_iff.mp hg).2 d
      let gD := hF.1.toLp F
      have hgD : HasEuclideanWeakDerivativesL2 (gD : E n → ℝ) k :=
        hF.congr (MemLp.coeFn_toLp hF.1).symm
      have heD (ψ : 𝓓E[n]) : (∫ x, ψ x * gD x ∂volume0 n) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * g x ∂volume0 n) := by
        calc
          _ = ∫ x, ψ x * F x ∂volume0 n := by
            apply integral_congr_ae
            filter_upwards [MemLp.coeFn_toLp hF.1] with x hx
            change ψ x * hF.1.toLp F x = _
            rw [hx]
          _ = _ := by simpa only [euclideanTestLineDerivative, euclideanTest_lineDeriv_apply] using heF ψ
      obtain ⟨v, _, hv⟩ := exists_euclideanSobolev_weakDerivative hA hl hE hLip hu d
      let B (x : E n) := fderiv ℝ A x d
      have hB : ContDiff ℝ ∞ B := (hAc.fderiv_right (by simp)).clm_apply contDiff_const
      have hB₀ (ds : List (E n)) :
          MemLp (ds.foldr (fun d C x => fderiv ℝ C x d) B) ⊤ (volume0 n) := by
        simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil, B] using hBound (ds ++ [d])
      obtain ⟨D, hD, heD'⟩ := exists_euclideanGradientDivergence_with_weakDerivatives
        b (u : EuclideanL2Pair n).snd k hU hB hB₀
      have hEq := hu.weakDerivative_solution_of_divergence b d hAc (hB₀ []) heD hv heD'
      have hg' := (hgD.add hD).congr (Lp.coeFn_add gD D).symm
      refine ⟨fun x => inner ℝ e ((v : EuclideanL2Pair n).snd x), ih hEq hg' e, fun ψ => ?_⟩
      simpa only [euclideanTestLineDerivative, euclideanTest_lineDeriv_apply] using hv ψ e

end KEBall
