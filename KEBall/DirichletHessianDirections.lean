import KEBall.DirichletHessianDivergence

/-! Real-direction components of the L² weak Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped Distributions

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

private theorem dirichletHessianEntry_eq_sum_basis {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (v w : E n) :
    dirichletHessianEntry u ψ v w =
      ∑ i, ∑ j, (inner ℝ (b i) w * inner ℝ (b j) v) * dirichletHessianEntry u ψ (b j) (b i) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let G := (u : DirichletBallL2Pair n).snd
  let D (j : Fin (2 * n)) := dirichletTestFieldDerivative ψ (fun _ => b j) contDiff_const
  let c (i j : Fin (2 * n)) := inner ℝ (b i) w * inner ℝ (b j) v
  let F (i j : Fin (2 * n)) (x : E n) := c i j * (D j x * inner ℝ (b i) (G x))
  have hI (i j : Fin (2 * n)) : Integrable (F i j) ν[n] := by
    have h : Integrable (fun x => D j x * inner ℝ (b i) (G x)) ν[n] :=
      (D j).integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
        ((((Lp.memLp G).const_inner (b i)).integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn
          (unitBall n))
    exact h.const_mul _
  have hInner (x : E n) : (∑ i, inner ℝ (b i) w * inner ℝ (b i) (G x)) = inner ℝ w (G x) := by
    calc
      _ = inner ℝ (∑ i, inner ℝ (b i) w • b i) (G x) := by simp only [sum_inner, real_inner_smul_left]
      _ = _ := by rw [b.sum_repr']
  have hDeriv (x : E n) : (∑ j, inner ℝ (b j) v * D j x) = fderiv ℝ (ψ : E n → ℝ) x v := by
    calc
      _ = fderiv ℝ (ψ : E n → ℝ) x (∑ j, inner ℝ (b j) v • b j) := by
        simp only [map_sum, map_smul, smul_eq_mul]
        rfl
      _ = _ := by rw [b.sum_repr']
  have hPoint (x : E n) :
      (∑ i, ∑ j, F i j x) = fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ w (G x) := by
    calc
      _ = (∑ i, inner ℝ (b i) w * inner ℝ (b i) (G x)) * (∑ j, inner ℝ (b j) v * D j x) := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        dsimp [F, c]
        ring
      _ = _ := by rw [hInner, hDeriv, mul_comm]
  unfold dirichletHessianEntry
  have he : (∫ x, fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ w (G x) ∂ν[n]) =
      ∑ i, ∑ j, ∫ x, F i j x ∂ν[n] := by
    calc
      _ = ∫ x, ∑ i, ∑ j, F i j x ∂ν[n] :=
        integral_congr_ae (Eventually.of_forall fun x => (hPoint x).symm)
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact integral_finsetSum _ fun j _ => hI i j
  change -(∫ x, fderiv ℝ (ψ : E n → ℝ) x v * inner ℝ w (G x) ∂ν[n]) =
    ∑ i, ∑ j, c i j * -(∫ x, D j x * inner ℝ (b i) (G x) ∂ν[n])
  rw [he]
  simp_rw [F, integral_const_mul, ← Finset.sum_neg_distrib, neg_mul_eq_mul_neg]

/-- L² representatives of the entries in an orthonormal frame give
an L² representative in every pair of fixed real directions. -/
theorem exists_dirichletHessianEntryL2_of_basis {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hEntries : HasDirichletHessianEntriesL2 b u)
    (v w : E n) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletHessianEntry u ψ v w = ∫ x, ψ x * F x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  unfold HasDirichletHessianEntriesL2 at hEntries
  choose F hF he using hEntries
  let c (i j : Fin (2 * n)) := inner ℝ (b i) w * inner ℝ (b j) v
  have hTerm (i j : Fin (2 * n)) : MemLp (fun x => c i j * F i j x) 2 ν[n] :=
    (hF i j).const_smul (c i j)
  have hSum (i : Fin (2 * n)) : MemLp (fun x => ∑ j, c i j * F i j x) 2 ν[n] :=
    memLp_finsetSum Finset.univ fun j _ => hTerm i j
  refine ⟨fun x => ∑ i, ∑ j, c i j * F i j x, memLp_finsetSum Finset.univ fun i _ => hSum i, ?_⟩
  intro ψ
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  rw [dirichletHessianEntry_eq_sum_basis hn b u ψ v w]
  change (∑ i, ∑ j, c i j * dirichletHessianEntry u ψ (b j) (b i)) =
    ∫ x, ψ x * (∑ i, ∑ j, c i j * F i j x) ∂ν[n]
  simp_rw [he, ← integral_const_mul]
  rw [show (∫ x, ψ x * (∑ i, ∑ j, c i j * F i j x) ∂ν[n]) =
      ∑ i, ∫ x, ψ x * (∑ j, c i j * F i j x) ∂ν[n] from by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => by simpa only [Finset.mul_sum] using hI (hSum i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => hI (hTerm i j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end KEBall
