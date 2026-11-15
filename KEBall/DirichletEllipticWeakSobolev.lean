import KEBall.DirichletWeakLeibniz
import KEBall.DirichletMatrixAnnulus

/-! The elliptic matrix contraction at arbitrary finite weak order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

/-- Testing the elliptic equation controls the coefficient contraction of
the next derivative, assuming the preceding order of the potential and
the corresponding derivatives of the forcing are in L². -/
theorem IsDirichletWeakSolution.exists_dirichletDistributionalDerivative_matrixL2
    {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (k : ℕ) (hU : HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 2))
    (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) (k + 1))
    (d : E n) (ds : List (E n)) (hds : ds.length = k) :
    ∃ R : E n → ℝ, MemLp R 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      dirichletMatrixContraction b
        (fun φ v w => dirichletDistributionalDerivative u ((d :: ds) ++ [v, w]) φ) ψ hA =
        ∫ x, ψ x * R x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let f := (u : DirichletBallL2Pair n).fst
  let U := (u : DirichletBallL2Pair n).snd
  let V (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (U x)
  have heV (i : Fin (2 * n)) (ψ : 𝓓B[n]) :
      dirichletWeakDerivativeTest f [b i] ψ = ∫ x, ψ x * V i x ∂ν[n] :=
    dirichletDistributionalDerivative_singleton u (b i) ψ
  have hV (i : Fin (2 * n)) : HasDirichletWeakDerivativesL2 (V i) (k + 1) :=
    hU.of_directionalWeakDerivative ((Lp.memLp U).const_inner (b i)) (b i)
      (fun ψ => dirichletSobolev_integral_weakGradient u ψ (b i))
  have hH (i j : Fin (2 * n)) := (hasDirichletWeakDerivativesL2_succ_iff.mp (hV i)).2 (b j)
  choose F hF heF using hH
  have heH (i j : Fin (2 * n)) (ψ : 𝓓B[n]) :
      dirichletHessianEntry u ψ (b j) (b i) = ∫ x, ψ x * F i j x ∂ν[n] :=
    (heF i j ψ).symm
  have heFF (i j : Fin (2 * n)) (ψ : 𝓓B[n]) :
      dirichletWeakDerivativeTest (V i) [b j] ψ = ∫ x, ψ x * F i j x ∂ν[n] :=
    (heF i j ψ).symm
  have heLong (i j : Fin (2 * n)) (ψ : 𝓓B[n]) :
      dirichletDistributionalDerivative u ((d :: ds) ++ [b j, b i]) ψ =
        dirichletWeakDerivativeTest (F i j) (d :: ds) ψ := by
    change dirichletWeakDerivativeTest f ((d :: ds) ++ [b j, b i]) ψ = _
    rw [show (d :: ds) ++ [b j, b i] = (((d :: ds) ++ [b j]) ++ [b i]) by simp [List.append_assoc],
      dirichletWeakDerivativeTest_append_singleton (b i) (heV i),
      dirichletWeakDerivativeTest_append_singleton (b j) (heFF i j)]
  let a (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (A x (b i))
  have ha (i j : Fin (2 * n)) : ContDiff ℝ ∞ (a i j) :=
    contDiff_dirichletCoefficientEntry hA (b i) (b j)
  let P (i j : Fin (2 * n)) (x : E n) := a i j x * F i j x
  have hP (i j : Fin (2 * n)) : MemLp (P i j) 2 ν[n] := ((hF i j).mul_smooth hn (ha i j)).1
  let H (x : E n) := ∑ i, ∑ j, P i j x
  let C := dirichletDivergenceGradientCorrection b u A
  have hC : HasDirichletWeakDerivativesL2 C (k + 1) := by
    change HasDirichletWeakDerivativesL2 (fun x =>
      ∑ i, dirichletColumnDivergence b A (b i) x * V i x) (k + 1)
    exact HasDirichletWeakDerivativesL2.finsetSum hn Finset.univ fun i _ =>
      (hV i).mul_smooth hn (contDiff_dirichletVectorDivergence b (hA.clm_apply contDiff_const))
  let Q (x : E n) := -(g x) - C x
  have hQ : HasDirichletWeakDerivativesL2 Q (k + 1) := by
    refine ((hg.mul_smooth hn (contDiff_const (c := (-1 : ℝ)))).add hn
      (hC.mul_smooth hn (contDiff_const (c := (-1 : ℝ))))).congr (Eventually.of_forall fun x => ?_)
    change -1 * g x + -1 * C x = -g x - C x
    ring
  have heHQ (ψ : 𝓓B[n]) : (∫ x, ψ x * H x ∂ν[n]) = ∫ x, ψ x * Q x ∂ν[n] := by
    have he := dirichletHessianTrace_eq_integral_of_entries hn b u hA F
      (fun i j => (hF i j).1) heH ψ
    change dirichletHessianTrace b u ψ hA = ∫ x, ψ x * H x ∂ν[n] at he
    rw [← he, hu.dirichletHessianTrace_eq_integral hn b hA]
    have hI {w : E n → ℝ} (hw : MemLp w 2 ν[n]) : Integrable (fun x => ψ x * w x) ν[n] :=
      (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hw).integrable (by norm_num)
    have hNeg : Integrable (fun x => -(ψ x * g x)) ν[n] := (hI (Lp.memLp g)).neg
    change -(∫ x, ψ x * g x ∂ν[n]) - (∫ x, ψ x * C x ∂ν[n]) =
      ∫ x, ψ x * (-(g x) - C x) ∂ν[n]
    simp only [mul_sub, mul_neg, integral_sub hNeg (hI hC.1), integral_neg]
  obtain ⟨G, hG, heG⟩ := hQ.2 (d :: ds) (by simp [hds])
  have hR (i j : Fin (2 * n)) := exists_dirichletWeakDerivativeTest_mul_remainder hn (ha i j) d ds 0
    (show HasDirichletWeakDerivativesL2 (F i j) (0 + ds.length) from by simpa [hds] using hF i j)
  choose R hR₀ heR using hR
  let T (x : E n) := ∑ i, ∑ j, R i j x
  have hT : MemLp T 2 ν[n] := memLp_finsetSum Finset.univ fun i _ =>
    memLp_finsetSum Finset.univ fun j _ => (hR₀ i j).1
  refine ⟨G - T, hG.sub hT, fun ψ => ?_⟩
  have hTest := (dirichletWeakDerivativeTest_congr_tested heHQ (d :: ds) ψ).trans (heG ψ)
  change dirichletWeakDerivativeTest (fun x => ∑ i, ∑ j, P i j x) (d :: ds) ψ = _ at hTest
  rw [dirichletWeakDerivativeTest_finsetSum hn Finset.univ (fun i _ =>
    memLp_finsetSum Finset.univ fun j _ => hP i j)] at hTest
  simp_rw [dirichletWeakDerivativeTest_finsetSum hn Finset.univ (fun j _ => hP _ j)] at hTest
  have heRP (i j : Fin (2 * n)) :
      dirichletWeakDerivativeTest (P i j) (d :: ds) ψ =
        dirichletWeakDerivativeTest (F i j) (d :: ds) (dirichletTestMul ψ (ha i j)) +
          ∫ x, ψ x * R i j x ∂ν[n] := heR i j ψ
  simp_rw [heRP, Finset.sum_add_distrib] at hTest
  have hI {w : E n → ℝ} (hw : MemLp w 2 ν[n]) : Integrable (fun x => ψ x * w x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hw).integrable (by norm_num)
  have hInt : (∫ x, ψ x * T x ∂ν[n]) = ∑ i, ∑ j, ∫ x, ψ x * R i j x ∂ν[n] := by
    simp_rw [T, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI (hR₀ i j).1))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hI (hR₀ i j).1
  unfold dirichletMatrixContraction
  simp_rw [heLong, Pi.sub_apply, mul_sub, integral_sub (hI hG) (hI hT), hInt]
  linarith only [hTest]

end KEBall
