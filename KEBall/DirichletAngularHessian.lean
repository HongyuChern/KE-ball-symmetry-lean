import KEBall.DirichletAngularEquation
import KEBall.DirichletHessianDirections

/-! Angular weak derivatives of the second derivative entries. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- Commuting an angular derivative past two fixed derivatives gives the
two first-order changes of direction in the Hessian entries. -/
theorem dirichletHessianEntry_angular_commutator {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (u v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (e w : E n) :
    let η := dirichletTestFieldDerivative ψ S S.contDiff
    (-dirichletHessianEntry u η e w) =
      dirichletHessianEntry v ψ e w - dirichletHessianEntry u ψ e (S w) -
        dirichletHessianEntry u ψ (S e) w := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let U := (u : DirichletBallL2Pair n).snd
  let V := (v : DirichletBallL2Pair n).snd
  let η := dirichletTestFieldDerivative ψ S S.contDiff
  let ξ := dirichletTestFieldDerivative ψ (fun _ => e) contDiff_const
  let τ := dirichletTestFieldDerivative η (fun _ => e) contDiff_const
  let ζ := dirichletTestFieldDerivative ψ (fun _ => S e) contDiff_const
  have hD (x : E n) : fderiv ℝ (ξ : E n → ℝ) x (S x) = τ x - ζ x := by
    have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hs := (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast)
    change fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y e) x (S x) =
      fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y (S y)) x e -
        fderiv ℝ (ψ : E n → ℝ) x (S e)
    rw [fderiv_clm_apply hd (differentiableAt_const e), fderiv_clm_apply hd S.differentiableAt]
    simp [hs.eq (S x) e]
  have hI (φ : 𝓓(dirichletBallOpens n, ℝ)) {F : E n → ℝ} (hF : MemLp F 2 ν[n]) :
      Integrable (fun x => φ x * F x) ν[n] :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hF.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hU : MemLp (fun x => inner ℝ w (U x)) 2 ν[n] := (Lp.memLp U).const_inner w
  have hV : MemLp (fun x => inner ℝ w (V x)) 2 ν[n] := (Lp.memLp V).const_inner w
  have hSU : MemLp (fun x => inner ℝ (S w) (U x)) 2 ν[n] := (Lp.memLp U).const_inner (S w)
  have h₁ := dirichletSobolev_integral_angularGradientComponent hn S u v hv w ξ
  change (∫ x, ξ x * (inner ℝ w (V x) - inner ℝ (S w) (U x)) ∂ν[n]) =
    -(∫ x, fderiv ℝ (ξ : E n → ℝ) x (S x) * inner ℝ w (U x) ∂ν[n]) at h₁
  simp_rw [mul_sub] at h₁
  rw [integral_sub (hI ξ hV) (hI ξ hSU)] at h₁
  have h₂ : (∫ x, fderiv ℝ (ξ : E n → ℝ) x (S x) * inner ℝ w (U x) ∂ν[n]) =
      (∫ x, τ x * inner ℝ w (U x) ∂ν[n]) - ∫ x, ζ x * inner ℝ w (U x) ∂ν[n] := by
    rw [← integral_sub (hI τ hU) (hI ζ hU)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change fderiv ℝ (ξ : E n → ℝ) x (S x) * inner ℝ w (U x) =
        τ x * inner ℝ w (U x) - ζ x * inner ℝ w (U x)
      rw [hD, sub_mul]
  rw [h₂] at h₁
  change -(-(∫ x, τ x * inner ℝ w (U x) ∂ν[n])) =
    -(∫ x, ξ x * inner ℝ w (V x) ∂ν[n]) - (-(∫ x, ξ x * inner ℝ (S w) (U x) ∂ν[n])) -
      (-(∫ x, ζ x * inner ℝ w (U x) ∂ν[n]))
  linarith only [h₁]

/-- An actual angular weak derivative of a weak Hessian entry, given the
L² Hessians of the potential and of its angular derivative. -/
theorem exists_dirichletHessianEntry_angularDerivative_L2 {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (S : E n →L[ℝ] E n)
    (u v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (hU' : HasDirichletHessianEntriesL2 b u) (hV' : HasDirichletHessianEntriesL2 b v)
    (e w : E n) {F : E n → ℝ}
    (heF : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletHessianEntry u ψ e w = ∫ x, ψ x * F x ∂ν[n]) :
    ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * T x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * F x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  have hU := exists_dirichletHessianEntryL2_of_basis hn b u hU'
  have hV := exists_dirichletHessianEntryL2_of_basis hn b v hV'
  obtain ⟨G, hG, heG⟩ := hV e w
  obtain ⟨H, hH, heH⟩ := hU e (S w)
  obtain ⟨J, hJ, heJ⟩ := hU (S e) w
  refine ⟨G - H - J, (hG.sub hH).sub hJ, fun ψ => ?_⟩
  let η := dirichletTestFieldDerivative ψ S S.contDiff
  have he := dirichletHessianEntry_angular_commutator hn S u v hv ψ e w
  change -dirichletHessianEntry u η e w = _ at he
  rw [heF η, heG ψ, heH ψ, heJ ψ] at he
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  have hGH : Integrable (fun x => ψ x * G x - ψ x * H x) ν[n] := (hI hG).sub (hI hH)
  simp_rw [Pi.sub_apply, mul_sub]
  rw [integral_sub hGH (hI hJ), integral_sub (hI hG) (hI hH)]
  exact he.symm

/-- L² angular derivatives of the forcing give an L² weak derivative of
each Hessian entry in every projected tangent direction. -/
theorem exists_dirichletHessianEntry_tangentDerivative_of_angular_forcing {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hg : ∀ (S : E n →L[ℝ] E n), star S = -S →
      ∃ gS : DirichletBallL2 n ℝ, ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, ψ x * gS x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n]))
    (e w z : E n) :
    ∃ F T : E n → ℝ, MemLp F 2 ν[n] ∧ MemLp T 2 ν[n] ∧
      ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        dirichletHessianEntry u ψ e w = (∫ x, ψ x * F x ∂ν[n]) ∧
        (∫ x, ψ x * T x ∂ν[n]) =
          -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • z - inner ℝ z x • x) +
            ((1 - (2 : ℝ) * n) * inner ℝ z x) * ψ x) * F x ∂ν[n]) := by
  have hU : HasDirichletHessianEntriesL2 b u :=
    exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE hLipA hM₀ hM hu
  obtain ⟨F, hF, heF⟩ := exists_dirichletHessianEntryL2_of_basis hn b u hU e w
  have hAngular (S : E n →L[ℝ] E n) (hS : star S = -S) :
      ∃ T : E n → ℝ, MemLp T 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, ψ x * T x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * F x ∂ν[n]) := by
    obtain ⟨gS, hgS⟩ := hg S hS
    obtain ⟨v, _, hv, _, hV⟩ :=
      exists_dirichletAngularDerivative_with_L2Hessian hn b hA hAc hSym hl hE hLipA hM₀ hM hu S hS hgS
    exact exists_dirichletHessianEntry_angularDerivative_L2 hn b S u v hv hU hV e w heF
  obtain ⟨T, hT, heT⟩ := exists_memLp_dirichletTangentDerivative hn hF z hAngular
  exact ⟨F, T, hF, hT, fun ψ => ⟨heF ψ, heT ψ⟩⟩

/-- For smooth forcing, each weak Hessian entry has an L² weak derivative
in any projected tangent direction on the entire ball. -/
theorem exists_dirichletHessianEntry_tangentDerivative_of_smooth_forcing {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    (e w z : E n) :
    ∃ F T : E n → ℝ, MemLp F 2 ν[n] ∧ MemLp T 2 ν[n] ∧
      ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        dirichletHessianEntry u ψ e w = (∫ x, ψ x * F x ∂ν[n]) ∧
        (∫ x, ψ x * T x ∂ν[n]) =
          -(∫ x, (fderiv ℝ (ψ : E n → ℝ) x (‖x‖ ^ 2 • z - inner ℝ z x • x) +
            ((1 - (2 : ℝ) * n) * inner ℝ z x) * ψ x) * F x ∂ν[n]) := by
  apply exists_dirichletHessianEntry_tangentDerivative_of_angular_forcing hn b hA hAc
    hSym hl hE hLipA hM₀ hM hu ?_ e w z
  intro S hS
  obtain ⟨gS, _, hgS⟩ := exists_dirichletForcing_angularDerivative_of_smooth hn g hG hRep S hS
  exact ⟨gS, hgS⟩

end KEBall
