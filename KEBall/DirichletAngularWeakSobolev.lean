import KEBall.DirichletWeakSobolev

/-! Angular and tangential regularity of derivatives of arbitrary order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

theorem dirichletAngularDirectionVariations_length {n : ℕ} (S : E n →L[ℝ] E n)
    {ds es : List (E n)} (he : es ∈ dirichletAngularDirectionVariations S ds) :
    es.length = ds.length := by
  induction ds generalizing es with
  | nil => simp [dirichletAngularDirectionVariations] at he
  | cons d ds ih =>
      simp only [dirichletAngularDirectionVariations, List.mem_cons, List.mem_map] at he
      rcases he with h | ⟨l, hl, rfl⟩
      · simp [h]
      · simp [ih hl]

private theorem exists_dirichletSumWeakDerivativeTestL2 {n : ℕ} (hn : 0 < n)
    {f : E n → ℝ} {k : ℕ} (hf : HasDirichletWeakDerivativesL2 f k)
    (ls : List (List (E n))) (hLen : ∀ ds ∈ ls, ds.length ≤ k) :
    ∃ R : E n → ℝ, MemLp R 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (ls.map (fun ds => dirichletWeakDerivativeTest f ds ψ)).sum =
        ∫ x, ψ x * R x ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  induction ls with
  | nil => exact ⟨0, MemLp.zero, by simp⟩
  | cons ds ls ih =>
      obtain ⟨F, hF, heF⟩ := hf.2 ds (hLen ds (List.mem_cons.mpr (Or.inl rfl)))
      obtain ⟨G, hG, heG⟩ := ih (fun es hes => hLen es (List.mem_cons.mpr (Or.inr hes)))
      refine ⟨F + G, hF.add hG, fun ψ => ?_⟩
      have hI {w : E n → ℝ} (hw : MemLp w 2 ν[n]) : Integrable (fun x => ψ x * w x) ν[n] :=
        (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hw).integrable (by norm_num)
      simp only [List.map_cons, List.sum_cons, heF, heG, Pi.add_apply, mul_add,
        integral_add (hI hF) (hI hG)]

/-- The commutator estimates the angular derivative of any tested entry
whose order is controlled for both the solution and its angular derivative. -/
theorem exists_dirichletDistributionalDerivative_angularL2 {n : ℕ} (hn : 0 < n)
    {u v : DirichletSobolev n} {k : ℕ}
    (hu : HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) k)
    (hv : HasDirichletWeakDerivativesL2 ((v : DirichletBallL2Pair n).fst : E n → ℝ) k)
    (S : E n →L[ℝ] E n)
    (hAngle : ∀ ψ : 𝓓B[n], (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (ds : List (E n)) (hs : ds.length ≤ k) {F : E n → ℝ}
    (heF : ∀ ψ : 𝓓B[n], dirichletDistributionalDerivative u ds ψ = ∫ x, ψ x * F x ∂ν[n]) :
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      (∫ x, ψ x * T x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * F x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  obtain ⟨V, hV, heV⟩ := hv.2 ds hs
  obtain ⟨R, hR, heR⟩ := exists_dirichletSumWeakDerivativeTestL2 hn hu
    (dirichletAngularDirectionVariations S ds)
    (fun es hes => (dirichletAngularDirectionVariations_length S hes).trans_le hs)
  refine ⟨V - R, hV.sub hR, fun ψ => ?_⟩
  let τ := dirichletTestFieldDerivative ψ S S.contDiff
  have he := dirichletDistributionalDerivative_angular_commutator hn u v S hAngle ds ψ
  change -dirichletDistributionalDerivative u ds τ =
    dirichletDistributionalDerivative v ds ψ - _ at he
  have heV' : dirichletDistributionalDerivative v ds ψ = ∫ x, ψ x * V x ∂ν[n] := heV ψ
  have heR' : ((dirichletAngularDirectionVariations S ds).map
      (fun es => dirichletDistributionalDerivative u es ψ)).sum = ∫ x, ψ x * R x ∂ν[n] :=
    heR ψ
  rw [heF τ, heV', heR'] at he
  have hI {w : E n → ℝ} (hw : MemLp w 2 ν[n]) : Integrable (fun x => ψ x * w x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hw).integrable (by norm_num)
  simp only [Pi.sub_apply, mul_sub, integral_sub (hI hV) (hI hR)]
  exact he.symm

/-- If the angular derivatives preserve weak regularity of order k, the
derivative along any scaled tangent field has an L² representative for
every tested entry of order at most k. -/
theorem exists_dirichletDistributionalDerivative_tangentL2 {n : ℕ} (hn : 0 < n)
    {u : DirichletSobolev n} {k : ℕ}
    (hu : HasDirichletWeakDerivativesL2 ((u : DirichletBallL2Pair n).fst : E n → ℝ) k)
    (hAngle : ∀ (S : E n →L[ℝ] E n), star S = -S →
      ∃ v : DirichletSobolev n,
        HasDirichletWeakDerivativesL2 ((v : DirichletBallL2Pair n).fst : E n → ℝ) k ∧
        ∀ ψ : 𝓓B[n], (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (ds : List (E n)) (hs : ds.length ≤ k) (z : E n) :
    ∃ F T : E n → ℝ, MemLp F 2 ν[n] ∧ MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓B[n],
      dirichletDistributionalDerivative u ds ψ = (∫ x, ψ x * F x ∂ν[n]) ∧
      (∫ x, ψ x * T x ∂ν[n]) =
        -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • z - inner ℝ z x • x) +
          ((1 - (2 : ℝ) * n) * inner ℝ z x) * ψ x) * F x ∂ν[n]) := by
  obtain ⟨F, hF, heF⟩ := hu.2 ds hs
  obtain ⟨T, hT, heT⟩ := exists_memLp_dirichletTangentDerivative hn hF z (fun S hS => by
    obtain ⟨v, hv, he⟩ := hAngle S hS
    exact exists_dirichletDistributionalDerivative_angularL2 hn hu hv S he ds hs heF)
  exact ⟨F, T, hF, hT, fun ψ => ⟨heF ψ, heT ψ⟩⟩

end KEBall
