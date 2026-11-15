import KEBall.DirichletWholeRegularity
import KEBall.DirichletWeakSobolev
import KEBall.DirichletWholeForcingExtension

/-! Compactly supported transfer of finite-order weak regularity to the whole space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private theorem integral_mul_ballIndicator {n : ℕ} (p f : E n → ℝ) :
    (∫ x, p x * (unitBall n).indicator f x ∂volume0 n) = ∫ x, p x * f x ∂ν[n] := by
  rw [← integral_indicator (show MeasurableSet (unitBall n) from measurableSet_ball)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change p x * (unitBall n).indicator f x = (unitBall n).indicator (fun x => p x * f x) x
    by_cases hx : x ∈ unitBall n
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

private theorem indicator_mul_add {n : ℕ} (f g : E n → ℝ) :
    (unitBall n).indicator (f + g) = (unitBall n).indicator f + (unitBall n).indicator g := by
  funext x
  by_cases hx : x ∈ unitBall n <;> simp [hx]

/-- Multiplying by a Dirichlet test before extension by zero preserves
weak L² derivatives through every finite order. -/
theorem HasDirichletWeakDerivativesL2.zeroExtension_mul {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} {k : ℕ} (hf : HasDirichletWeakDerivativesL2 f k) (χ : 𝓓B[n]) :
    HasEuclideanWeakDerivativesL2 ((unitBall n).indicator (fun x => χ x * f x)) k := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hMem {f : E n → ℝ} (hF : MemLp f 2 ν[n]) (φ : 𝓓B[n]) :
      MemLp ((unitBall n).indicator (fun x => φ x * f x)) 2 (volume0 n) :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      (memLp_dirichlet_mul_of_continuousOn φ.continuous.continuousOn hF)
  induction k generalizing f χ with
  | zero => exact HasEuclideanWeakDerivativesL2.zero_order (hMem hf.1 χ)
  | succ k ih =>
      obtain ⟨hF, hD⟩ := hasDirichletWeakDerivativesL2_succ_iff.mp hf
      refine hasEuclideanWeakDerivativesL2_succ_iff.mpr ⟨hMem hF χ, fun d => ?_⟩
      obtain ⟨D, hD₀, heD⟩ := hD d
      let dc := dirichletTestFieldDerivative χ (fun _ => d) contDiff_const
      let F := f
      let q (x : E n) := χ x * f x
      have hF₀ : HasDirichletWeakDerivativesL2 f k :=
        ⟨hF, fun ds hs => hf.2 ds (hs.trans (Nat.le_succ _))⟩
      let H (x : E n) := χ x * D x + dc x * f x
      have hH : HasEuclideanWeakDerivativesL2 ((unitBall n).indicator H) k := by
        rw [show H = (fun x => χ x * D x) + (fun x => dc x * f x) from rfl, indicator_mul_add]
        exact (ih hD₀ χ).add (ih hF₀ dc)
      refine ⟨(unitBall n).indicator H, hH, fun ψ => ?_⟩
      change (∫ x, ψ x * (unitBall n).indicator H x ∂volume0 n) =
        -(∫ x, euclideanTestLineDerivative d ψ x * (unitBall n).indicator q x ∂volume0 n)
      simp only [euclideanTestLineDerivative, euclideanTest_lineDeriv_apply]
      rw [integral_mul_ballIndicator, integral_mul_ballIndicator]
      have h₁ : MemLp (fun x => χ x * D x) 2 ν[n] :=
        memLp_dirichlet_mul_of_continuousOn χ.continuous.continuousOn hD₀.1
      have h₂ : MemLp (fun x => dc x * F x) 2 ν[n] :=
        memLp_dirichlet_mul_of_continuousOn dc.continuous.continuousOn hF
      let τ := dirichletTestMul χ ψ.contDiff
      let δ := dirichletTestMul χ
        ((ψ.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := d)))
      have hProduct (x : E n) : fderiv ℝ (τ : E n → ℝ) x d * F x =
          ψ x * (dc x * F x) + δ x * F x := by
        change fderiv ℝ (fun y => χ y * ψ y) x d * F x =
          ψ x * (fderiv ℝ (χ : E n → ℝ) x d * F x) +
            (χ x * fderiv ℝ (ψ : E n → ℝ) x d) * F x
        rw [fderiv_fun_mul (χ.contDiff.differentiable (by simp) x) (ψ.contDiff.differentiable (by simp) x)]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      have hInt (f : E n → ℝ) (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
        (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
      have hδ : Integrable (fun x => δ x * F x) ν[n] :=
        (memLp_dirichlet_mul_of_continuousOn δ.continuous.continuousOn hF).integrable (by norm_num)
      have he := heD τ
      change (∫ x, τ x * D x ∂ν[n]) =
        -(∫ x, fderiv ℝ (τ : E n → ℝ) x d * F x ∂ν[n]) at he
      simp_rw [hProduct] at he
      rw [integral_add (hInt _ h₂) hδ] at he
      simp only [τ, dirichletTestMul_apply] at he
      simp_rw [mul_comm (χ _) (ψ _), mul_assoc] at he
      have hδEq : (∫ x, δ x * F x ∂ν[n]) = ∫ x, fderiv ℝ (ψ : E n → ℝ) x d * q x ∂ν[n] := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change (χ x * fderiv ℝ (ψ : E n → ℝ) x d) * F x = fderiv ℝ (ψ : E n → ℝ) x d * (χ x * F x)
          ring
      rw [hδEq] at he
      simp only [H, mul_add]
      rw [integral_add (hInt _ h₁) (hInt _ h₂)]
      linarith only [he]

/-- The localized forcing keeps the order of the original forcing when the
potential has one additional order of weak regularity. -/
theorem hasEuclideanWeakDerivativesL2_dirichletCutoffForcing {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (k : ℕ)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {u : DirichletSobolev n}
    (hU : HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) (k + 1))
    {g : DirichletBallL2 n ℝ} (hg : HasDirichletWeakDerivativesL2 (g : E n → ℝ) k)
    (χ η : 𝓓B[n]) (hη : ∀ x ∈ tsupport (χ : E n → ℝ), η x = 1)
    (f' : DirichletBallL2 n ℝ) (hf' : f' =ᵐ[ν[n]] dirichletCutoffForcing b A χ g u) :
    HasEuclideanWeakDerivativesL2 (dirichletL2ZeroExtension f' : E n → ℝ) k := by
  let Y (x : E n) := A x (∇ (χ : E n → ℝ) x)
  let C := dirichletVectorDivergence b Y
  let U := (u : DirichletBallL2Pair n).snd
  let V := (u : DirichletBallL2Pair n).fst
  have hY : ContDiff ℝ ∞ Y := hA.clm_apply (contDiff_euclideanGradient χ.contDiff)
  have hC : ContDiff ℝ ∞ C := contDiff_dirichletVectorDivergence b hY
  have hGrad (i : Fin (2 * n)) :
      HasDirichletWeakDerivativesL2 (fun x => inner ℝ (b i) (U x)) k :=
    hU.of_directionalWeakDerivative ((Lp.memLp U).const_inner (b i)) (b i)
      (fun ψ => dirichletSobolev_integral_weakGradient u ψ (b i))
  have hYgrad : HasDirichletWeakDerivativesL2 (fun x => inner ℝ (Y x) (U x)) k := by
    let c (i : Fin (2 * n)) (x : E n) := inner ℝ (b i) (Y x)
    have hc (i : Fin (2 * n)) : ContDiff ℝ ∞ (c i) := (innerSL ℝ (b i)).contDiff.comp hY
    refine (HasDirichletWeakDerivativesL2.finsetSum hn Finset.univ fun i _ =>
      (hGrad i).mul_smooth hn (hc i)).congr (Eventually.of_forall fun x => ?_)
    change (∑ i, c i x * inner ℝ (b i) (U x)) = inner ℝ (Y x) (U x)
    rw [← b.sum_repr' (Y x), sum_inner]
    simp only [real_inner_smul_left, c]
  have hV : HasDirichletWeakDerivativesL2 (V : E n → ℝ) k :=
    ⟨hU.1, fun ds hs => hU.2 ds (hs.trans (Nat.le_succ _))⟩
  have hTerm₁ := hg.mul_smooth hn χ.contDiff
  have hTerm₂ := hYgrad.mul_smooth hn (contDiff_const (c := (-2 : ℝ)))
  have hTerm₃ := hV.mul_smooth hn (hC.neg)
  have hForce : HasDirichletWeakDerivativesL2 (dirichletCutoffForcing b A χ g u) k := by
    refine ((hTerm₁.add hn hTerm₂).add hn hTerm₃).congr (Eventually.of_forall fun x => ?_)
    change χ x * g x + -2 * inner ℝ (Y x) (U x) + (-C x) * V x =
      χ x * g x - 2 * inner ℝ (Y x) (U x) - C x * V x
    ring
  refine (hForce.zeroExtension_mul hn η).congr ?_
  filter_upwards [dirichletL2ZeroExtension_ae f',
    (ae_restrict_iff' (μ := volume0 n) (show MeasurableSet (unitBall n) from measurableSet_ball)).mp hf']
    with x hx hfx
  rw [hx]
  by_cases hb : x ∈ unitBall n
  · rw [indicator_of_mem hb, indicator_of_mem hb, hfx hb]
    by_cases hχ : x ∈ tsupport (χ : E n → ℝ)
    · rw [hη x hχ, one_mul]
    · rw [dirichletCutoffForcing_eq_zero_of_notMem_tsupport b A χ g u hχ, mul_zero]
  · rw [indicator_of_notMem hb, indicator_of_notMem hb]

/-- The localized coefficients have bounded directional derivatives of every
order because each first directional derivative has compact support. -/
theorem memLp_iteratedLineDerivative_of_derivativeSupport {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E n → F} (hf : ContDiff ℝ ∞ f)
    (h₀ : MemLp f ⊤ (volume0 n))
    (hSupp : ∀ d : E n, HasCompactSupport (fun x => fderiv ℝ f x d))
    (ds : List (E n)) :
    MemLp (ds.foldr (fun d C x => fderiv ℝ C x d) f) ⊤ (volume0 n) := by
  have hIter {g : E n → F} (hg : HasCompactSupport g) (ds : List (E n)) :
      HasCompactSupport (ds.foldr (fun d C x => fderiv ℝ C x d) g) := by
    induction ds with
    | nil => exact hg
    | cons d ds ih => exact ih.fderiv_apply ℝ d
  cases ds using List.reverseRecOn with
  | nil => exact h₀
  | append_singleton ds d =>
      have hs := hIter (hSupp d) ds
      apply (iteratedLineDerivative_contDiff hf (ds ++ [d])).continuous.memLp_top_of_hasCompactSupport
      simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using hs

end KEBall
