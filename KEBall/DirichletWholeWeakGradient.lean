import KEBall.DirichletWholeThirdDerivative

/-! First and second weak gradients of whole-space forcing and fluxes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

namespace KEBall

local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)

def IsEuclideanDirectionalWeakDerivative {n : ℕ} (f F : EuclideanL2 n ℝ) (d : E n) : Prop :=
  ∀ ψ : 𝓓E[n], (∫ x, ψ x * F x ∂volume0 n) =
    -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f x ∂volume0 n)

/-- Every directional weak derivative is represented by an L² function. -/
def HasEuclideanWeakGradientL2 {n : ℕ} (f : EuclideanL2 n ℝ) : Prop :=
  ∀ d : E n, ∃ F : EuclideanL2 n ℝ, IsEuclideanDirectionalWeakDerivative f F d

theorem IsEuclideanDirectionalWeakDerivative.add {n : ℕ}
    {f g F G : EuclideanL2 n ℝ} {d : E n}
    (hf : IsEuclideanDirectionalWeakDerivative f F d)
    (hg : IsEuclideanDirectionalWeakDerivative g G d) :
    IsEuclideanDirectionalWeakDerivative (f + g) (F + G) d := by
  intro ψ
  let τ : 𝓓E[n] := TestFunction.lineDerivCLM ℝ d ψ
  have hτ (x : E n) : fderiv ℝ (ψ : E n → ℝ) x d = τ x :=
    (euclideanTest_lineDeriv_apply ψ d x).symm
  have hsum (φ : 𝓓E[n]) (u v : EuclideanL2 n ℝ) :
      (∫ x, φ x * (u + v) x ∂volume0 n) =
        (∫ x, φ x * u x ∂volume0 n) + ∫ x, φ x * v x ∂volume0 n := by
    rw [← integral_add (integrable_euclideanTest_mul φ (Lp.memLp u))
      (integrable_euclideanTest_mul φ (Lp.memLp v))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add u v] with x hx
    rw [hx, Pi.add_apply, mul_add]
  simp_rw [hτ]
  rw [hsum ψ, hsum τ, neg_add]
  have h₁ := hf ψ
  have h₂ := hg ψ
  simp_rw [hτ] at h₁ h₂
  rw [h₁, h₂]

theorem HasEuclideanWeakGradientL2.add {n : ℕ} {f g : EuclideanL2 n ℝ}
    (hf : HasEuclideanWeakGradientL2 f) (hg : HasEuclideanWeakGradientL2 g) :
    HasEuclideanWeakGradientL2 (f + g) := by
  intro d
  obtain ⟨F, hF⟩ := hf d
  obtain ⟨G, hG⟩ := hg d
  exact ⟨F + G, hF.add hG⟩

/-- Directional weak derivatives of an L² vector field, tested componentwise. -/
def IsEuclideanVectorWeakDerivative {n : ℕ} (U H : EuclideanL2 n (E n)) (d : E n) : Prop :=
  ∀ (ψ : 𝓓E[n]) (v : E n),
    (∫ x, ψ x * inner ℝ v (H x) ∂volume0 n) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * inner ℝ v (U x) ∂volume0 n)

end KEBall
