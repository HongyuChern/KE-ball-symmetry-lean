import KEBall.DirichletHessianCoefficient

/-! Distributional integration by parts against a compactly supported vector field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

theorem tsupport_dirichletVectorDivergence_subset {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (X : E n → E n) :
    tsupport (dirichletVectorDivergence b X) ⊆ tsupport X := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra h
  apply hx
  unfold dirichletVectorDivergence
  refine Finset.sum_eq_zero fun j _ => ?_
  have hSub : tsupport (fun y => inner ℝ (b j) (X y)) ⊆ tsupport X :=
    tsupport_comp_subset (g := innerSL ℝ (b j)) (by simp) _
  rw [fderiv_of_notMem_tsupport ℝ (fun hx => h (hSub hx)), zero_apply]

/-- Weak integration by parts with a vector field whose support lies in the ball. -/
theorem dirichletSobolev_integral_gradientField {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    {X : E n → E n} (hX : ContDiff ℝ ∞ X) (hSupp : tsupport X ⊆ unitBall n)
    (ψ : 𝓓((⊤ : Opens (E n)), ℝ)) :
    (∫ x, ψ x * inner ℝ (X x) ((u : DirichletBallL2Pair n).snd x) ∂ν[n]) =
      -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) *
        (u : DirichletBallL2Pair n).fst x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let f := (u : DirichletBallL2Pair n).fst
  let G := (u : DirichletBallL2Pair n).snd
  let c (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (X x)
  have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) := (innerSL ℝ (b i)).contDiff.comp hX
  have hcSupp (i : Fin (2 * n)) : tsupport (c i) ⊆ unitBall n :=
    (tsupport_comp_subset (g := innerSL ℝ (b i)) (by simp) X).trans hSupp
  let χ (i : Fin (2 * n)) : 𝓓(dirichletBallOpens n, ℝ) :=
    ⟨fun x => ψ x * c i x, ψ.contDiff.mul (hc i), ψ.hasCompactSupport.mul_right,
      tsupport_mul_subset_right.trans (hcSupp i)⟩
  let D (i : Fin (2 * n)) := dirichletTestFieldDerivative (χ i) (fun _ => b i) contDiff_const
  have hD (i : Fin (2 * n)) (x : E n) :
      D i x = c i x * fderiv ℝ (ψ : E n → ℝ) x (b i) + ψ x * fderiv ℝ (c i) x (b i) := by
    change fderiv ℝ (fun y => ψ y * c i y) x (b i) = _
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) ((hc i).differentiable (by simp) x)]
    simp [add_comm]
  have hSumD (x : E n) :
      (∑ i, D i x) = fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x := by
    simp_rw [hD, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    congr 1
    calc
      _ = fderiv ℝ (ψ : E n → ℝ) x (∑ i, c i x • b i) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = _ := congrArg (fderiv ℝ (ψ : E n → ℝ) x) (b.sum_repr' (X x))
  have hSumL (x : E n) :
      (∑ i, χ i x * inner ℝ (b i) (G x)) = ψ x * inner ℝ (X x) (G x) := by
    change (∑ i, (ψ x * c i x) * inner ℝ (b i) (G x)) = _
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    calc
      _ = inner ℝ (∑ i, c i x • b i) (G x) := by simp only [sum_inner, real_inner_smul_left]
      _ = _ := congrArg (fun v => inner ℝ v (G x)) (b.sum_repr' (X x))
  have hInt {F : E n → ℝ} (hF : MemLp F 2 ν[n]) (φ : 𝓓(dirichletBallOpens n, ℝ)) :
      Integrable (fun x => φ x * F x) ν[n] :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hF.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hL : (∫ x, ∑ i, χ i x * inner ℝ (b i) (G x) ∂ν[n]) =
      ∫ x, ψ x * inner ℝ (X x) (G x) ∂ν[n] := integral_congr_ae (Eventually.of_forall hSumL)
  have hR : (∫ x, ∑ i, D i x * f x ∂ν[n]) =
      ∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) * f x ∂ν[n] := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (∑ i, D i x * f x) = _
      rw [← Finset.sum_mul, hSumD]
  change (∫ x, ψ x * inner ℝ (X x) (G x) ∂ν[n]) =
    -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (X x) + ψ x * dirichletVectorDivergence b X x) * f x ∂ν[n])
  rw [← hL, ← hR, integral_finsetSum _ (fun i _ => hInt ((Lp.memLp G).const_inner (b i)) (χ i)),
    integral_finsetSum _ (fun i _ => hInt (Lp.memLp f) (D i)), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => dirichletSobolev_integral_weakGradient u (χ i) (b i)

end KEBall
