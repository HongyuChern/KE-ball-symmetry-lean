import KEBall.DirichletWeakSobolev

/-! The divergence correction at arbitrary finite orders of L² regularity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- If the potential has weak derivatives through order k+2 in L²,
the divergence of a smooth coefficient times its gradient has them through order k. -/
theorem exists_dirichletGradientDivergence_with_weakDerivatives {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n) (k : ℕ)
    (hu : HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2))
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    ∃ d : DirichletBallL2 n ℝ, HasDirichletWeakDerivativesL2 (d : E n → ℝ) k ∧
      ∀ ψ : 𝓓B[n], (∫ x, fderiv ℝ (ψ : E n → ℝ) x
        (B x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) = -(∫ x, ψ x * d x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let U := (u : DirichletBallL2Pair n).snd
  let V (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (U x)
  have hV (i : Fin (2 * n)) : HasDirichletWeakDerivativesL2 (V i) (k + 1) :=
    hu.of_directionalWeakDerivative ((Lp.memLp U).const_inner (b i)) (b i)
      (fun ψ => dirichletSobolev_integral_weakGradient u ψ (b i))
  let W (j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (U x))
  have hW (j : Fin (2 * n)) : HasDirichletWeakDerivativesL2 (W j) (k + 1) := by
    let c (i : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
    have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) :=
      contDiff_dirichletCoefficientEntry hB (b i) (b j)
    refine (HasDirichletWeakDerivativesL2.finsetSum hn Finset.univ fun i _ =>
      (hV i).mul_smooth hn (hc i)).congr (Eventually.of_forall fun x => ?_)
    change (∑ i, c i x * V i x) = inner ℝ (b j) (B x (U x))
    calc
      _ = inner ℝ (b j) (B x (∑ i, V i x • b i)) := by
        simp only [map_sum, map_smul, inner_sum, real_inner_smul_right, c]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = _ := by rw [show (∑ i, V i x • b i) = U x from b.sum_repr' (U x)]
  have hDir (j : Fin (2 * n)) := (hasDirichletWeakDerivativesL2_succ_iff.mp (hW j)).2 (b j)
  choose F hF heF using hDir
  let D (x : E n) := ∑ j, F j x
  have hD : HasDirichletWeakDerivativesL2 D k :=
    HasDirichletWeakDerivativesL2.finsetSum hn Finset.univ fun j _ => hF j
  let d := hD.1.toLp D
  refine ⟨d, hD.congr (MemLp.coeFn_toLp hD.1).symm, fun ψ => ?_⟩
  let τ (j : Fin (2 * n)) := dirichletTestLineDerivative (b j) ψ
  have hI (φ : 𝓓B[n]) {f : E n → ℝ} (hf : MemLp f 2 ν[n]) :
      Integrable (fun x => φ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hf).integrable (by norm_num)
  have he (x : E n) : fderiv ℝ (ψ : E n → ℝ) x (B x (U x)) = ∑ j, τ j x * W j x := by
    calc
      _ = fderiv ℝ (ψ : E n → ℝ) x (∑ j, W j x • b j) := by
        rw [show (∑ j, W j x • b j) = B x (U x) from b.sum_repr' (B x (U x))]
      _ = _ := by
        simp only [map_sum, map_smul, smul_eq_mul]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hLp : (∫ x, ψ x * d x ∂ν[n]) = ∫ x, ψ x * D x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hD.1] with x hx
    change ψ x * hD.1.toLp D x = _
    rw [hx]
  change (∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x (U x)) ∂ν[n]) =
    -(∫ x, ψ x * d x ∂ν[n])
  rw [hLp]
  simp_rw [he, D, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => hI (τ j) (hW j).1),
    integral_finsetSum _ (fun j _ => hI ψ (hF j).1), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    have h := heF j ψ
    change (∫ x, ψ x * F j x ∂ν[n]) = -(∫ x, τ j x * W j x ∂ν[n]) at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm

end KEBall
