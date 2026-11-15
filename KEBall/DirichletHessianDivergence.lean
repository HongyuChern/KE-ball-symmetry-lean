import KEBall.DirichletGlobalWeakHessian

/-! Divergence of a smooth matrix times the weak gradient, for an L² Hessian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- Each coordinate entry of the weak Hessian in an orthonormal frame
is represented by a square-integrable function. -/
def HasDirichletHessianEntriesL2 {n : ℕ} (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (u : DirichletSobolev n) : Prop :=
  ∀ i j : Fin (2 * n), ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧
    ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletHessianEntry u ψ (b j) (b i) = ∫ x, ψ x * F x ∂ν[n]

/-- The weak Hessian contracted with a smooth matrix is represented by
the sum of its entries weighted by the matrix coefficients. -/
theorem dirichletHessianTrace_eq_integral_of_entries {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    (F : Fin (2 * n) → Fin (2 * n) → E n → ℝ)
    (hF : ∀ i j, MemLp (F i j) 2 ν[n])
    (he : ∀ i j (ψ : 𝓓(dirichletBallOpens n, ℝ)),
      dirichletHessianEntry u ψ (b j) (b i) = ∫ x, ψ x * F i j x ∂ν[n])
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    dirichletHessianTrace b u ψ hB =
      ∫ x, ψ x * (∑ i, ∑ j, inner ℝ (b j) (B x (b i)) * F i j x) ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hB (b i) (b j)
  have hTerm (i j : Fin (2 * n)) : MemLp (fun x => c i j x * F i j x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hc i j).continuous.continuousOn (hF i j)
  have hSum (i : Fin (2 * n)) : MemLp (fun x => ∑ j, c i j x * F i j x) 2 ν[n] :=
    memLp_finsetSum Finset.univ fun j _ => hTerm i j
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  change (∑ i, ∑ j, dirichletHessianEntry u (dirichletTestMul ψ (hc i j)) (b j) (b i)) =
    ∫ x, ψ x * (∑ i, ∑ j, c i j x * F i j x) ∂ν[n]
  simp_rw [he, dirichletTestMul_apply, mul_assoc]
  rw [show (∫ x, ψ x * (∑ i, ∑ j, c i j x * F i j x) ∂ν[n]) =
      ∑ i, ∫ x, ψ x * (∑ j, c i j x * F i j x) ∂ν[n] from by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => by
      simpa only [Finset.mul_sum] using hI (hSum i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.mul_sum]
  exact (integral_finsetSum _ fun j _ => hI (hTerm i j)).symm

/-- A contraction with smooth coefficients is represented by the weighted
sum of the L² representatives of the Hessian entries. -/
theorem hasDirichletHessianTraceL2_of_entries {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hEntries : HasDirichletHessianEntriesL2 b u)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    HasDirichletHessianTraceL2 b u hB := by
  unfold HasDirichletHessianEntriesL2 at hEntries
  choose F hF he using hEntries
  let c (i j : Fin (2 * n)) (x : E n) := inner ℝ (b j) (B x (b i))
  have hc (i j : Fin (2 * n)) : ContDiff ℝ ∞ (c i j) :=
    contDiff_dirichletCoefficientEntry hB (b i) (b j)
  have hTerm (i j : Fin (2 * n)) : MemLp (fun x => c i j x * F i j x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn (hc i j).continuous.continuousOn (hF i j)
  have hSum (i : Fin (2 * n)) : MemLp (fun x => ∑ j, c i j x * F i j x) 2 ν[n] :=
    memLp_finsetSum Finset.univ fun j _ => hTerm i j
  exact ⟨fun x => ∑ i, ∑ j, c i j x * F i j x,
    memLp_finsetSum Finset.univ (fun i _ => hSum i),
    dirichletHessianTrace_eq_integral_of_entries hn b u hB F hF he⟩

/-- The first-order correction to the matrix contraction in divergence form. -/
noncomputable def dirichletDivergenceGradientCorrection {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (B : E n → E n →L[ℝ] E n) (x : E n) : ℝ :=
  ∑ i, dirichletColumnDivergence b B (b i) x *
    inner ℝ (b i) ((u : DirichletBallL2Pair n).snd x)

/-- The divergence representative is the Hessian contraction plus the
first-order correction from differentiating the coefficient columns. -/
theorem exists_dirichletGradientDivergence_L2_of_trace {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B)
    {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (he : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletHessianTrace b u ψ hB = ∫ x, ψ x * F x ∂ν[n]) :
    ∃ d : DirichletBallL2 n ℝ, d =ᵐ[ν[n]] F + dirichletDivergenceGradientCorrection b u B ∧
      ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
          -(∫ x, ψ x * d x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let U := (u : DirichletBallL2Pair n).snd
  let D (i : Fin (2 * n)) (x : E n) := dirichletColumnDivergence b B (b i) x
  let G := dirichletDivergenceGradientCorrection b u B
  have hD (i : Fin (2 * n)) : ContDiff ℝ ∞ (D i) :=
    contDiff_dirichletVectorDivergence b (hB.clm_apply contDiff_const)
  have hG : MemLp G 2 ν[n] :=
    memLp_finsetSum Finset.univ fun i _ =>
      memLp_dirichlet_mul_of_continuousOn (hD i).continuous.continuousOn
        ((Lp.memLp U).const_inner (b i))
  have hAdd : MemLp (F + G) 2 ν[n] := hF.add hG
  let d := hAdd.toLp (F + G)
  refine ⟨d, MemLp.coeFn_toLp hAdd, fun ψ => ?_⟩
  have hPair {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  have hEq : (∫ x, ψ x * d x ∂ν[n]) = (∫ x, ψ x * F x ∂ν[n]) + ∫ x, ψ x * G x ∂ν[n] := by
    rw [← integral_add (hPair hF) (hPair hG)]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hAdd] with x hx
    change d x = F x + G x at hx
    change ψ x * d x = ψ x * F x + ψ x * G x
    rw [hx, mul_add]
  rw [hEq]
  have h := dirichletHessianTrace_eq_neg_integral hn b hB u ψ
  rw [he ψ] at h
  change (∫ x, ψ x * F x ∂ν[n]) =
    -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x (U x)) ∂ν[n]) - ∫ x, ψ x * G x ∂ν[n] at h
  linarith only [h]

/-- The divergence of a smooth matrix times the gradient is represented in
L² whenever the coordinate weak Hessian is represented in L². -/
theorem exists_dirichletGradientDivergence_L2 {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hEntries : HasDirichletHessianEntriesL2 b u)
    {B : E n → E n →L[ℝ] E n} (hB : ContDiff ℝ ∞ B) :
    ∃ d : DirichletBallL2 n ℝ, ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x (B x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
        -(∫ x, ψ x * d x ∂ν[n]) := by
  obtain ⟨F, hF, he⟩ := hasDirichletHessianTraceL2_of_entries hn b u hEntries hB
  obtain ⟨d, _, hd⟩ := exists_dirichletGradientDivergence_L2_of_trace hn b u hB hF he
  exact ⟨d, hd⟩

end KEBall
