import KEBall.DirichletWholeForcingExtension
import KEBall.DirichletThirdAnnulus

/-! Interior and global third weak derivatives on the Dirichlet ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "b[" n "]" => EuclideanSpace.basisFun (Fin (2 * n)) ℝ
local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)

/-- If the original forcing has an L² weak gradient, the forcing of
the interior equation has square-integrable first weak derivatives. -/
theorem exists_dirichletCutoffForcing_weakDerivative {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {u : DirichletSobolev n} (hH : HasDirichletHessianEntriesL2 b u)
    {g : DirichletBallL2 n ℝ} (hg : HasDirichletWeakGradientL2 (g : E n → ℝ))
    (χ η : 𝓓(dirichletBallOpens n, ℝ))
    (hη : ∀ x ∈ tsupport (χ : E n → ℝ), (η : E n → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (f' : DirichletBallL2 n ℝ) (hf' : f' =ᵐ[ν[n]] dirichletCutoffForcing b A χ g u) :
    ∃ q : EuclideanL2 n ℝ, ∀ ψ : 𝓓E[n],
      (∫ x, ψ x * q x ∂volume0 n) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * dirichletL2ZeroExtension f' x ∂volume0 n) := by
  let S (x : E n) := χ x * g x
  let Y (x : E n) := A x (∇ (χ : E n → ℝ) x)
  let C := dirichletVectorDivergence b Y
  have hY : ContDiff ℝ ∞ Y := hA.clm_apply (contDiff_euclideanGradient χ.contDiff)
  have hS : MemLp S 2 ν[n] := memLp_dirichlet_mul_of_continuousOn
    χ.continuous.continuousOn (Lp.memLp g)
  have hSWeak : HasDirichletWeakGradientL2 S := hg.mul_smooth hn (Lp.memLp g) χ.contDiff
  have hC : ContDiff ℝ ∞ C := contDiff_dirichletVectorDivergence b hY
  obtain ⟨F, hF, hWeak⟩ := exists_dirichletLocalizedForcing_weakDerivative hn b d u hH hS hSWeak hC hY
  refine exists_euclideanWeakDerivative_of_dirichletZeroExtension d f' hF ?_ η ?_
  · intro ψ
    rw [hWeak ψ]
    congr 1
    apply integral_congr_ae
    filter_upwards [hf'] with x hfx
    change f' x = dirichletCutoffForcing b A χ g u x at hfx
    rw [hfx]
    rfl
  · filter_upwards [hf'] with x hx hne
    have hxs : x ∈ tsupport (χ : E n → ℝ) := by
      by_contra h
      exact hne (hx.trans (dirichletCutoffForcing_eq_zero_of_notMem_tsupport b A χ g u h))
    have he := hη x hxs
    refine ⟨he.eq_of_nhds, ?_⟩
    rw [he.fderiv_eq, fderiv_fun_const, Pi.zero_apply, zero_apply]

/-- The third weak derivatives in the interior of the ball are represented
by square-integrable functions. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeEntryL2_interior_of_weakGradient
    {n : ℕ} (hn : 0 < n) (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x)
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hH : HasDirichletHessianEntriesL2 b u)
    (hg : HasDirichletWeakGradientL2 (g : E n → ℝ)) (d e v : E n) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2) →
      dirichletThirdDerivativeEntry u ψ d e v = ∫ x, ψ x * F x ∂ν[n] := by
  obtain ⟨χ, η, B, K, hB, f', hχ, hη, hBc, hBE, hLip, hD₁, hD₂, hf', hEq⟩ :=
    hu.exists_interior_cutoff_with_forcing hn b hA hSym hE
  obtain ⟨q, hq⟩ := exists_dirichletCutoffForcing_weakDerivative hn b e hA hH
    hg χ η hη f' hf'
  obtain ⟨H, J, hJ⟩ := hEq.exists_secondGradientWeakDerivative b e d hBc (hD₁ e) (hD₂ e)
    hl (Eventually.of_forall hBE) hLip hq
  refine ⟨fun x => inner ℝ v (J x), ((Lp.memLp J).const_inner v).restrict _, fun ψ hSupp => ?_⟩
  let φ : 𝓓E[n] := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_univ _⟩
  let τ := dirichletTestFieldDerivative ψ (fun _ => d) contDiff_const
  let ξ : 𝓓E[n] := ⟨τ, τ.contDiff, τ.hasCompactSupport, subset_univ _⟩
  have hτ : tsupport (τ : E n → ℝ) ⊆ tsupport (ψ : E n → ℝ) := by
    change closure (Function.support (τ : E n → ℝ)) ⊆ tsupport (ψ : E n → ℝ)
    refine closure_minimal ?_ (isClosed_tsupport (ψ : E n → ℝ))
    intro x hx
    by_contra hx'
    apply hx
    change fderiv ℝ (ψ : E n → ℝ) x d = 0
    rw [fderiv_of_notMem_tsupport ℝ hx', zero_apply]
  have hIntegral : (∫ x, ψ x * inner ℝ v (J x) ∂ν[n]) =
      ∫ x, φ x * inner ℝ v (J x) ∂volume0 n := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (ψ.tsupport_subset hs)), zero_mul]
  have hTransfer := integral_dirichletCutoff_gradient_on_interior u χ τ hχ
    (hτ.trans hSupp) e v
  have hξ (x : E n) : fderiv ℝ (φ : E n → ℝ) x d = ξ x := rfl
  rw [hIntegral, (hJ φ v).2]
  simp only [hξ]
  rw [(hJ ξ v).1]
  exact congrArg (fun t : ℝ => - -t) hTransfer.symm

/-- For forcing with an L² weak gradient, all third weak coordinate
derivatives of the Dirichlet solution are in L² on the entire ball. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeEntryL2_of_weakGradient
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hg : HasDirichletWeakGradientL2 (g : E n → ℝ))
    (i j k : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeEntry u ψ (b[n] k) (b[n] j) (b[n] i) = ∫ x, ψ x * F x ∂ν[n] := by
  let b := b[n]
  have hH : HasDirichletHessianEntriesL2 b u :=
    exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE hLipA hM₀ hM hu
  obtain ⟨F₀, hF₀, he₀⟩ := hu.exists_dirichletThirdDerivativeEntryL2_interior_of_weakGradient hn b hAc
    (fun x _ => hSym x) hl hE hH hg (b k) (b j) (b i)
  obtain ⟨F₁, hF₁, he₁⟩ := hu.exists_dirichletThirdDerivativeEntryL2_on_annulus_of_weakGradient hn hA hAc
    hSym hl hE hLipA hM₀ hM hg (r := 1 / 8) (by norm_num) i j k
  exact exists_dirichletTestL2_of_interior_annulus hn _ (fun ψ φ =>
    dirichletThirdDerivativeEntry_add hn u ψ φ (b k) (b j) (b i)) hF₀ hF₁ he₀ he₁

/-- The third weak derivatives in the interior of the ball are represented
by square-integrable functions. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeEntryL2_interior
    {n : ℕ} (hn : 0 < n) (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ x ∈ unitBall n, (A x).adjoint = A x)
    {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hH : HasDirichletHessianEntriesL2 b u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G) (d e v : E n) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      tsupport (ψ : E n → ℝ) ⊆ ball (0 : E n) (1 / 2) →
      dirichletThirdDerivativeEntry u ψ d e v = ∫ x, ψ x * F x ∂ν[n] :=
  hu.exists_dirichletThirdDerivativeEntryL2_interior_of_weakGradient hn b hA hSym hl hE hH
    (HasDirichletWeakGradientL2.of_smooth_ae hn hG hRep) d e v

/-- With smooth coefficients and smooth forcing, all third weak coordinate
derivatives of the Dirichlet solution are in L² on the entire ball. -/
theorem IsDirichletWeakSolution.exists_dirichletThirdDerivativeEntryL2
    {n : ℕ} (hn : 0 < n)
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    (i j k : Fin (2 * n)) :
    ∃ F : E n → ℝ, MemLp F 2 ν[n] ∧ ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      dirichletThirdDerivativeEntry u ψ (b[n] k) (b[n] j) (b[n] i) = ∫ x, ψ x * F x ∂ν[n] :=
  hu.exists_dirichletThirdDerivativeEntryL2_of_weakGradient hn hA hAc hSym hl hE hLipA hM₀ hM
    (HasDirichletWeakGradientL2.of_smooth_ae hn hG hRep) i j k

end KEBall
