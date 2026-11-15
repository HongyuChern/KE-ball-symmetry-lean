import KEBall.DirichletWholeWeakGradient
import KEBall.DirichletDivergenceWeakGradient

/-! Two weak derivatives of the localized whole-space forcing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)
local notation "𝓓E[" n "]" => 𝓓((⊤ : Opens (E n)), ℝ)
local notation "𝓓B[" n "]" => 𝓓(dirichletBallOpens n, ℝ)

private theorem hasEuclideanWeakGradientL2_zeroExtension_mul {n : ℕ} (hn : 0 < n)
    (η : 𝓓B[n]) {F : E n → ℝ} (hF : MemLp F 2 ν[n])
    (hWeak : HasDirichletWeakGradientL2 F) :
    let q (x : E n) := η x * F x
    let hq : MemLp q 2 ν[n] :=
      memLp_dirichlet_mul_of_continuousOn η.continuous.continuousOn hF
    HasEuclideanWeakGradientL2 (dirichletL2ZeroExtension (hq.toLp q)) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let q (x : E n) := η x * F x
  have hq : MemLp q 2 ν[n] := memLp_dirichlet_mul_of_continuousOn η.continuous.continuousOn hF
  change HasEuclideanWeakGradientL2 (dirichletL2ZeroExtension (hq.toLp q))
  intro d
  obtain ⟨D, hD, heD⟩ := hWeak d
  let ηd := dirichletTestFieldDerivative η (fun _ => d) contDiff_const
  let H (x : E n) := η x * D x + ηd x * F x
  have h₁ : MemLp (fun x => η x * D x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn η.continuous.continuousOn hD
  have h₂ : MemLp (fun x => ηd x * F x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn ηd.continuous.continuousOn hF
  have hH : MemLp H 2 ν[n] := h₁.add h₂
  refine ⟨dirichletL2ZeroExtension (hH.toLp H), fun ψ => ?_⟩
  rw [integral_mul_dirichletL2ZeroExtension (hH.toLp H) (ψ : E n → ℝ),
    integral_mul_dirichletL2ZeroExtension (hq.toLp q) (fun x => fderiv ℝ (ψ : E n → ℝ) x d)]
  have hLeft : (∫ x, ψ x * hH.toLp H x ∂ν[n]) = ∫ x, ψ x * H x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hH] with x hx
    rw [hx]
  have hRight : (∫ x, fderiv ℝ (ψ : E n → ℝ) x d * hq.toLp q x ∂ν[n]) =
      ∫ x, fderiv ℝ (ψ : E n → ℝ) x d * q x ∂ν[n] := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hq] with x hx
    rw [hx]
  rw [hLeft, hRight]
  let τ := dirichletTestMul η ψ.contDiff
  let δ := dirichletTestMul η
    ((ψ.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := d)))
  have hProduct (x : E n) : fderiv ℝ (τ : E n → ℝ) x d * F x =
      ψ x * (ηd x * F x) + δ x * F x := by
    change fderiv ℝ (fun y => η y * ψ y) x d * F x =
      ψ x * (fderiv ℝ (η : E n → ℝ) x d * F x) +
        (η x * fderiv ℝ (ψ : E n → ℝ) x d) * F x
    rw [fderiv_fun_mul (η.contDiff.differentiable (by simp) x) (ψ.contDiff.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hInt (f : E n → ℝ) (hf : MemLp f 2 ν[n]) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn hf).integrable (by norm_num)
  have hδ : Integrable (fun x => δ x * F x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn δ.continuous.continuousOn hF).integrable (by norm_num)
  have he := heD τ
  simp_rw [hProduct, integral_add (hInt _ h₂) hδ] at he
  simp only [τ, dirichletTestMul_apply] at he
  simp_rw [mul_comm (η _) (ψ _), mul_assoc] at he
  have hδEq : (∫ x, δ x * F x ∂ν[n]) = ∫ x, fderiv ℝ (ψ : E n → ℝ) x d * q x ∂ν[n] := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (η x * fderiv ℝ (ψ : E n → ℝ) x d) * F x = fderiv ℝ (ψ : E n → ℝ) x d * (η x * F x)
      ring
  rw [hδEq] at he
  simp only [H, mul_add, integral_add (hInt _ h₁) (hInt _ h₂)]
  linarith only [he]

private theorem hasDirichletWeakGradientL2_inner_gradient {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (u : DirichletSobolev n)
    (hH : HasDirichletHessianEntriesL2 b u) (d : E n) :
    HasDirichletWeakGradientL2 (fun x => inner ℝ d ((u : DirichletBallL2Pair n).snd x)) := by
  apply HasDirichletWeakGradientL2.of_basis hn b ((Lp.memLp _).const_inner d)
  intro i
  obtain ⟨F, hF, heF⟩ := exists_dirichletHessianEntryL2_of_basis hn b u hH (b i) d
  exact ⟨F, hF, fun ψ => (heF ψ).symm⟩

/-- A localized Dirichlet forcing for a solution with three L² derivatives
has directional derivatives with L² weak gradients after zero extension. -/
theorem exists_dirichletCutoffForcing_weakDerivative_with_weakGradient
    {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) (d : E n)
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    {u : DirichletSobolev n} (hH : HasDirichletHessianEntriesL2 b u)
    (hT : HasDirichletThirdDerivativeEntriesL2 b u)
    {g : DirichletBallL2 n ℝ} {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) (hRep : g =ᵐ[ν[n]] G)
    (χ η : 𝓓B[n])
    (hη : ∀ x ∈ tsupport (χ : E n → ℝ), (η : E n → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (f' : DirichletBallL2 n ℝ) (hf' : f' =ᵐ[ν[n]] dirichletCutoffForcing b A χ g u) :
    ∃ q : EuclideanL2 n ℝ,
      IsEuclideanDirectionalWeakDerivative (dirichletL2ZeroExtension f') q d ∧
      HasEuclideanWeakGradientL2 q := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let S (x : E n) := χ x * G x
  let Y (x : E n) := A x (∇ (χ : E n → ℝ) x)
  let C := dirichletVectorDivergence b Y
  let ds (x : E n) := fderiv ℝ S x d
  let dc (x : E n) := fderiv ℝ C x d
  let U := (u : DirichletBallL2Pair n).snd
  let V := (u : DirichletBallL2Pair n).fst
  let J (x : E n) := inner ℝ d (U x)
  have hY : ContDiff ℝ ∞ Y := hA.clm_apply (contDiff_euclideanGradient χ.contDiff)
  have hS : ContDiff ℝ ∞ S := χ.contDiff.mul hG
  have hC : ContDiff ℝ ∞ C := contDiff_dirichletVectorDivergence b hY
  have hdc : ContDiff ℝ ∞ dc := (hC.fderiv_right (by simp)).clm_apply contDiff_const
  have hds : ContDiff ℝ ∞ ds := (hS.fderiv_right (by simp)).clm_apply contDiff_const
  have hMem {p : E n → ℝ} (hp : ContDiff ℝ ∞ p) : MemLp p 2 ν[n] :=
    MemLp.ae_eq (Eventually.of_forall fun x => mul_one (p x))
      (memLp_dirichlet_mul_of_continuousOn hp.continuous.continuousOn (memLp_const (1 : ℝ)))
  have heS (ψ : 𝓓B[n]) : (∫ x, ψ x * ds x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * S x ∂ν[n]) := by
    have he := integral_dirichletTest_fieldDerivative_mul_smooth hn ψ hS (contDiff_const (c := d))
    dsimp only at he
    have hz (x : E n) : dirichletVectorDivergence (EuclideanSpace.basisFun (Fin (2 * n)) ℝ)
        (fun _ => d) x = 0 := by simp [dirichletVectorDivergence]
    simp only [hz, mul_zero, add_zero] at he
    have h := congrArg Neg.neg he.symm
    simpa only [neg_neg] using h
  obtain ⟨D, hDW, hD⟩ := exists_dirichletGradientDivergence_with_weakGradient hn b u hH hT
    (contDiff_rankOne_real (contDiff_const (c := d)) hY)
  obtain ⟨hF, heF⟩ := dirichletLocalizedForcing_weakDerivative_of hn b d u
    (hMem hS) (hMem hds) heS hC hY D hD
  let F (x : E n) := ds x - 2 * D x - (C x * J x + dc x * V x)
  change MemLp F 2 ν[n] at hF
  have hV : HasDirichletWeakGradientL2 (V : E n → ℝ) := by
    intro e
    exact ⟨fun x => inner ℝ e (U x), (Lp.memLp U).const_inner e,
      fun ψ => dirichletSobolev_integral_weakGradient u ψ e⟩
  have hJ : MemLp J 2 ν[n] := (Lp.memLp U).const_inner d
  have hA₀ : HasDirichletWeakGradientL2 (fun x => C x * J x) :=
    (hasDirichletWeakGradientL2_inner_gradient hn b u hH d).mul_smooth hn hJ hC
  have hA₁ : HasDirichletWeakGradientL2 (fun x => dc x * V x) :=
    hV.mul_smooth hn (Lp.memLp V) hdc
  have hLp₀ : MemLp (fun x => C x * J x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hC.continuous.continuousOn hJ
  have hLp₁ : MemLp (fun x => dc x * V x) 2 ν[n] :=
    memLp_dirichlet_mul_of_continuousOn hdc.continuous.continuousOn (Lp.memLp V)
  have hC₂ := hA₀.add hn hLp₀ hLp₁ hA₁
  have hC₂Lp := hLp₀.add hLp₁
  have hNegD := hDW.mul_smooth hn (Lp.memLp D) (contDiff_const (c := (-2 : ℝ)))
  have hNegC := hC₂.mul_smooth hn hC₂Lp (contDiff_const (c := (-1 : ℝ)))
  have hdsW := HasDirichletWeakGradientL2.of_smooth_ae hn hds (EventuallyEq.rfl (f := ds))
  have hFW : HasDirichletWeakGradientL2 F := by
    have hSum := hdsW.add hn (hMem hds) ((Lp.memLp D).const_smul (-2 : ℝ)) hNegD
    refine (hSum.add hn ((hMem hds).add ((Lp.memLp D).const_smul (-2 : ℝ)))
      (hC₂Lp.const_smul (-1 : ℝ)) hNegC).congr ?_
    exact Eventually.of_forall fun x => by simp only [F, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hWeak (ψ : 𝓓B[n]) : (∫ x, ψ x * F x ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x d * f' x ∂ν[n]) := by
    rw [heF ψ]
    congr 1
    apply integral_congr_ae
    filter_upwards [hf', hRep] with x hx hgx
    rw [hx]
    simp only [dirichletCutoffForcing, S, Y, C, hgx]
  have hη' : ∀ᵐ x ∂ν[n], f' x ≠ 0 → η x = 1 ∧ fderiv ℝ (η : E n → ℝ) x d = 0 := by
    filter_upwards [hf'] with x hx hne
    have hxs : x ∈ tsupport (χ : E n → ℝ) := by
      by_contra h
      exact hne (hx.trans (dirichletCutoffForcing_eq_zero_of_notMem_tsupport b A χ g u h))
    have he := hη x hxs
    refine ⟨he.eq_of_nhds, ?_⟩
    rw [he.fderiv_eq, fderiv_fun_const, Pi.zero_apply, zero_apply]
  let q (x : E n) := η x * F x
  have hq : MemLp q 2 ν[n] := memLp_dirichlet_mul_of_continuousOn η.continuous.continuousOn hF
  exact ⟨dirichletL2ZeroExtension (hq.toLp q),
    euclideanWeakDerivative_dirichletZeroExtension_mul d f' hF hWeak η hη',
    hasEuclideanWeakGradientL2_zeroExtension_mul hn η hF hFW⟩

end KEBall
