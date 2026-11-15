import KEBall.DirichletHessianDivergence
import KEBall.SecondGreen

/-! Angular differentiation of the actual weak Dirichlet equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions NNReal

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- The first variation of the coefficient field under orthogonal pullback. -/
noncomputable def dirichletAngularCoefficient {n : ℕ} (A : E n → E n →L[ℝ] E n)
    (S : E n →L[ℝ] E n) (x : E n) : E n →L[ℝ] E n :=
  (fderiv ℝ A x (S x) - S.comp (A x)) + (A x).comp S

theorem contDiff_dirichletAngularCoefficient {n : ℕ} {A : E n → E n →L[ℝ] E n}
    (hA : ContDiff ℝ ∞ A) (S : E n →L[ℝ] E n) :
    ContDiff ℝ ∞ (dirichletAngularCoefficient A S) := by
  have hD : ContDiff ℝ ∞ (fun x => fderiv ℝ A x (S x)) :=
    (hA.fderiv_right (m := ∞) (by simp)).clm_apply S.contDiff
  have hL : ContDiff ℝ ∞ (fun x => S.comp (A x)) := contDiff_const.clm_comp hA
  have hR : ContDiff ℝ ∞ (fun x => (A x).comp S) := hA.clm_comp contDiff_const
  exact (hD.sub hL).add hR

private theorem integrable_dirichletTest_fderiv_apply {n : ℕ} (hn : 0 < n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (U : DirichletBallL2 n (E n)) :
    Integrable (fun x => fderiv ℝ (ψ : E n → ℝ) x (A x (U x))) ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let L (x : E n) := (fderiv ℝ (ψ : E n → ℝ) x).comp (A x)
  have hL : Continuous L :=
    ((ψ.contDiff.fderiv_right (m := ∞) (by simp)).continuous.clm_comp hA.continuous)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hL.continuousOn
  have hEv : Continuous (fun p : (E n →L[ℝ] ℝ) × E n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hMeas : AEStronglyMeasurable (fun x => L x (U x)) ν[n] :=
    hEv.comp_aestronglyMeasurable (hL.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable U))
  refine ((Lp.memLp U).of_le_mul hMeas (c := C) ?_).integrable (by norm_num)
  filter_upwards [ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
  exact ((L x).le_opNorm (U x)).trans
    (mul_le_mul_of_nonneg_right (hC x (ball_subset_closedBall hx)) (norm_nonneg _))

private theorem dirichletTest_angularCoefficient_rule {n : ℕ}
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (S : E n →L[ℝ] E n) (e x : E n) :
    let X (y : E n) := A y e
    let χ := dirichletTestFieldDerivative ψ X (hA.clm_apply contDiff_const)
    let η := dirichletTestFieldDerivative ψ S S.contDiff
    fderiv ℝ (χ : E n → ℝ) x (S x) =
      fderiv ℝ (η : E n → ℝ) x (A x e) +
        fderiv ℝ (ψ : E n → ℝ) x ((fderiv ℝ A x (S x) - S.comp (A x)) e) := by
  let dψ := fderiv ℝ (ψ : E n → ℝ)
  have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hX : DifferentiableAt ℝ (fun y => A y e) x :=
    (hA.clm_apply (contDiff_const (c := e))).differentiable (by simp) x
  have hX' : fderiv ℝ (fun y => A y e) x (S x) = fderiv ℝ A x (S x) e := by
    rw [fderiv_clm_apply (hA.differentiable (by simp) x) (differentiableAt_const e)]
    simp
  have hs := (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast)
  change fderiv ℝ (fun y => dψ y (A y e)) x (S x) =
    fderiv ℝ (fun y => dψ y (S y)) x (A x e) +
      dψ x ((fderiv ℝ A x (S x) - S.comp (A x)) e)
  rw [fderiv_clm_apply hd hX, fderiv_clm_apply hd S.differentiableAt]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.fderiv, sub_apply, map_sub, hX', dψ]
  rw [hs.eq (S x) (A x e)]
  ring

set_option maxHeartbeats 900000 in
/-- The coefficient commutator in the equation for the angular derivative. -/
theorem dirichletSobolev_integral_angularEquation {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : ContDiff ℝ ∞ A)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (u v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    let η := dirichletTestFieldDerivative ψ S S.contDiff
    (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((v : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
      -(∫ x, fderiv ℝ (η : E n → ℝ) x (A x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) -
      ∫ x, fderiv ℝ (ψ : E n → ℝ) x
        (dirichletAngularCoefficient A S x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n] := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let U := (u : DirichletBallL2Pair n).snd
  let V := (v : DirichletBallL2Pair n).snd
  let η := dirichletTestFieldDerivative ψ S S.contDiff
  let χ (i : Fin (2 * n)) :=
    dirichletTestFieldDerivative ψ (fun y => A y (b i)) (hA.clm_apply contDiff_const)
  let χS (i : Fin (2 * n)) := dirichletTestFieldDerivative (χ i) S S.contDiff
  let dψ := fderiv ℝ (ψ : E n → ℝ)
  let dη := fderiv ℝ (η : E n → ℝ)
  let B (x : E n) := fderiv ℝ A x (S x) - S.comp (A x)
  let C := dirichletAngularCoefficient A S
  let F (i : Fin (2 * n)) (x : E n) :=
    χ i x * (inner ℝ (b i) (V x) - inner ℝ (S (b i)) (U x))
  let G (i : Fin (2 * n)) (x : E n) := χS i x * inner ℝ (b i) (U x)
  have hI {f : E n → ℝ} (hf : MemLp f 2 ν[n]) (τ : 𝓓(dirichletBallOpens n, ℝ)) :
      Integrable (fun x => τ x * f x) ν[n] :=
    τ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hf.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hIF (i : Fin (2 * n)) : Integrable (F i) ν[n] :=
    hI (((Lp.memLp V).const_inner (b i)).sub ((Lp.memLp U).const_inner (S (b i)))) (χ i)
  have hIG (i : Fin (2 * n)) : Integrable (G i) ν[n] :=
    hI ((Lp.memLp U).const_inner (b i)) (χS i)
  have hZero (i : Fin (2 * n)) : (∫ x, F i x + G i x ∂ν[n]) = 0 := by
    rw [integral_add (hIF i) (hIG i)]
    have he := dirichletSobolev_integral_angularGradientComponent hn S u v hv (b i) (χ i)
    change (∫ x, F i x ∂ν[n]) = -(∫ x, G i x ∂ν[n]) at he
    rw [he, neg_add_cancel]
  have hApply (D : E n →L[ℝ] ℝ) (T : E n →L[ℝ] E n) (y : E n) :
      (∑ i, D (T (b i)) * inner ℝ (b i) y) = D (T y) := by
    calc
      _ = D (T (∑ i, inner ℝ (b i) y • b i)) := by simp [map_sum, map_smul, mul_comm]
      _ = _ := by rw [b.sum_repr']
  have hSkew (e y : E n) : inner ℝ (S e) y = -inner ℝ e (S y) := by
    have he := S.adjoint_inner_left y e
    rw [← ContinuousLinearMap.star_eq_adjoint, hS, neg_apply, inner_neg_left] at he
    linarith only [he]
  have hSumF (x : E n) :
      (∑ i, F i x) = dψ x (A x (V x)) + dψ x (A x (S (U x))) := by
    change (∑ i, dψ x (A x (b i)) * (inner ℝ (b i) (V x) - inner ℝ (S (b i)) (U x))) = _
    simp_rw [hSkew, sub_neg_eq_add, mul_add, Finset.sum_add_distrib, hApply]
  have hSumG (x : E n) :
      (∑ i, G i x) = dη x (A x (U x)) + dψ x (B x (U x)) := by
    change (∑ i, fderiv ℝ (χ i : E n → ℝ) x (S x) * inner ℝ (b i) (U x)) = _
    have hRule (i : Fin (2 * n)) :
        fderiv ℝ (χ i : E n → ℝ) x (S x) = dη x (A x (b i)) + dψ x (B x (b i)) :=
      dirichletTest_angularCoefficient_rule ψ hA S (b i) x
    simp_rw [hRule, add_mul, Finset.sum_add_distrib, hApply]
  have hTotal (x : E n) :
      (∑ i, (F i x + G i x)) = (dψ x (A x (V x)) + dη x (A x (U x))) + dψ x (C x (U x)) := by
    rw [Finset.sum_add_distrib, hSumF, hSumG]
    change _ = (dψ x (A x (V x)) + dη x (A x (U x))) +
      dψ x (B x (U x) + A x (S (U x)))
    rw [map_add]
    ring
  have he :
      (∫ x, (dψ x (A x (V x)) + dη x (A x (U x))) + dψ x (C x (U x)) ∂ν[n]) = 0 := by
    calc
      _ = ∫ x, ∑ i, (F i x + G i x) ∂ν[n] :=
        integral_congr_ae (Eventually.of_forall fun x => (hTotal x).symm)
      _ = ∑ i, ∫ x, F i x + G i x ∂ν[n] := integral_finsetSum _ fun i _ => (hIF i).add (hIG i)
      _ = _ := Finset.sum_eq_zero fun i _ => hZero i
  have hψV : Integrable (fun x => dψ x (A x (V x))) ν[n] :=
    integrable_dirichletTest_fderiv_apply hn ψ hA V
  have hηU : Integrable (fun x => dη x (A x (U x))) ν[n] :=
    integrable_dirichletTest_fderiv_apply hn η hA U
  have hψC : Integrable (fun x => dψ x (C x (U x))) ν[n] :=
    integrable_dirichletTest_fderiv_apply hn ψ (contDiff_dirichletAngularCoefficient hA S) U
  have hSumI : Integrable (fun x => dψ x (A x (V x)) + dη x (A x (U x))) ν[n] := hψV.add hηU
  rw [integral_add hSumI hψC, integral_add hψV hηU] at he
  change (∫ x, dψ x (A x (V x)) ∂ν[n]) =
    -(∫ x, dη x (A x (U x)) ∂ν[n]) - ∫ x, dψ x (C x (U x)) ∂ν[n]
  linarith only [he]

/-- Assemble the forcing of the differentiated equation from its angular
forcing and its coefficient divergence. -/
theorem IsDirichletWeakSolution.angularDerivative_of_forcing {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    {g gS d : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    (hg : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * gS x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n]))
    (v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (hDiv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, fderiv ℝ (ψ : E n → ℝ) x
        (dirichletAngularCoefficient A S x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
        -(∫ x, ψ x * d x ∂ν[n])) :
    IsDirichletWeakSolution A (gS + d) v := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  refine IsDirichletWeakSolution.of_test hA _ v fun ψ => ?_
  let η := dirichletTestFieldDerivative ψ S S.contDiff
  have he := dirichletSobolev_integral_angularEquation hn b hAc S hS u v hv ψ
  change (∫ x, fderiv ℝ (ψ : E n → ℝ) x (A x ((v : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
    -(∫ x, fderiv ℝ (η : E n → ℝ) x (A x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) -
      ∫ x, fderiv ℝ (ψ : E n → ℝ) x
        (dirichletAngularCoefficient A S x ((u : DirichletBallL2Pair n).snd x)) ∂ν[n] at he
  rw [he, hu.integral_fderiv_test η, hDiv ψ]
  have hG : (∫ x, ψ x * gS x ∂ν[n]) = -(∫ x, η x * g x ∂ν[n]) := hg ψ
  have hI (f : DirichletBallL2 n ℝ) : Integrable (fun x => ψ x * f x) ν[n] :=
    (memLp_dirichlet_mul_of_continuousOn ψ.continuous.continuousOn (Lp.memLp f)).integrable (by norm_num)
  rw [← hG, sub_neg_eq_add, ← integral_add (hI gS) (hI d)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add gS d] with x hx
  change ψ x * gS x + ψ x * d x = ψ x * (gS + d) x
  rw [hx, Pi.add_apply, mul_add]

/-- If the forcing has an angular weak derivative in L², differentiating
the Dirichlet equation in that direction gives an L² forcing again. -/
theorem IsDirichletWeakSolution.exists_angularDerivative_forcing {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    {g gS : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (hEntries : HasDirichletHessianEntriesL2 b u)
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    (hg : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * gS x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n]))
    (v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n])) :
    ∃ g' : DirichletBallL2 n ℝ, IsDirichletWeakSolution A g' v := by
  obtain ⟨d, hDiv⟩ := exists_dirichletGradientDivergence_L2 hn b u hEntries
    (contDiff_dirichletAngularCoefficient hAc S)
  exact ⟨gS + d, hu.angularDerivative_of_forcing hn b hA hAc S hS hg v hv hDiv⟩

/-- The angular derivative of a weak solution has a square-integrable
Hessian when the forcing has the corresponding angular derivative in L². -/
theorem exists_dirichletAngularDerivative_with_L2Hessian {n : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {A : E n → E n →L[ℝ] E n} (hA : MemLp A ⊤ ν[n]) (hAc : ContDiff ℝ ∞ A)
    (hSym : ∀ x, (A x).adjoint = A x) {l : ℝ} (hl : 0 < l)
    (hE : ∀ x ∈ unitBall n, ∀ v : E n, l * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    {K : ℝ≥0} (hLipA : LipschitzOnWith K A (closedUnitBall n))
    {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x ∈ closedUnitBall n, ‖A x‖ ≤ M)
    {g gS : DirichletBallL2 n ℝ} {u : DirichletSobolev n} (hu : IsDirichletWeakSolution A g u)
    (S : E n →L[ℝ] E n) (hS : star S = -S)
    (hg : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * gS x ∂ν[n]) = -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n])) :
    ∃ (v : DirichletSobolev n) (g' : DirichletBallL2 n ℝ),
      (∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n])) ∧
      IsDirichletWeakSolution A g' v ∧ HasDirichletHessianEntriesL2 b v := by
  have hAE := (ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)).mono hE
  obtain ⟨v, hv⟩ :=
    exists_dirichletSobolev_angularDerivative_L2 hn hA hl hAE hLipA hM₀ hM hu S hS
  have hEntries := exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE hLipA hM₀ hM hu
  obtain ⟨g', he⟩ := hu.exists_angularDerivative_forcing hn b hA hAc hEntries S hS hg v hv
  exact ⟨v, g', hv, he, exists_dirichletHessianEntryL2 hn b hA hAc hSym hl hE hLipA hM₀ hM he⟩

theorem euclideanDivergence_skew_field {n : ℕ}
    (S : E n →L[ℝ] E n) (hS : star S = -S) (x : E n) :
    euclideanDivergence (S : E n → E n) x = 0 := by
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  unfold euclideanDivergence
  refine Finset.sum_eq_zero fun i _ => ?_
  let L := (EuclideanSpace.proj i : E n →L[ℝ] ℝ).comp S
  change fderiv ℝ (L : E n → ℝ) x (b i) = 0
  rw [L.fderiv]
  change (S (b i)) i = 0
  rw [← EuclideanSpace.basisFun_inner]
  have he := S.adjoint_inner_left (b i) (b i)
  rw [← ContinuousLinearMap.star_eq_adjoint, hS, neg_apply, inner_neg_left,
    real_inner_comm (b i) (S (b i))] at he
  change inner ℝ (b i) (S (b i)) = 0
  linarith only [he]

/-- A smooth representative of the forcing has its actual angular weak
derivative in the normalized L² space of the ball. -/
theorem exists_dirichletForcing_angularDerivative_of_smooth {n : ℕ} (hn : 0 < n)
    (g : DirichletBallL2 n ℝ) {G : E n → ℝ} (hG : ContDiff ℝ ∞ G)
    (hRep : g =ᵐ[ν[n]] G) (S : E n →L[ℝ] E n) (hS : star S = -S) :
    ∃ gS : DirichletBallL2 n ℝ,
      (gS =ᵐ[ν[n]] fun x => fderiv ℝ G x (S x)) ∧
      ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
        (∫ x, ψ x * gS x ∂ν[n]) =
          -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let F (x : E n) := fderiv ℝ G x (S x)
  have hF : Continuous F := (hG.fderiv_right (m := ∞) (by simp)).continuous.clm_apply S.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) 1).exists_bound_of_continuousOn hF.continuousOn
  have hTop : MemLp F ⊤ ν[n] := memLp_top_of_bound hF.aestronglyMeasurable M
    ((ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)).mono fun x hx => hM x (ball_subset_closedBall hx))
  have h₂ : MemLp F 2 ν[n] := hTop.mono_exponent (by simp)
  let gS := h₂.toLp F
  have hAE := MemLp.coeFn_toLp h₂
  refine ⟨gS, hAE, fun ψ => ?_⟩
  let H (x : E n) := ψ x * G x
  let V (x : E n) := H x • S x
  let D (x : E n) := fderiv ℝ (ψ : E n → ℝ) x (S x)
  have hH : ContDiff ℝ ∞ H := ψ.contDiff.mul hG
  have hV : ContDiff ℝ ∞ V := hH.smul S.contDiff
  have hPoint (x : E n) : euclideanDivergence V x = ψ x * F x + D x * G x := by
    have he := euclideanDivergence_smul (hH.differentiable (by simp) x) S.differentiableAt
    change euclideanDivergence V x = H x * euclideanDivergence S x + fderiv ℝ H x (S x) at he
    rw [he, euclideanDivergence_skew_field S hS, mul_zero, zero_add]
    change fderiv ℝ (fun y => ψ y * G y) x (S x) = _
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (hG.differentiable (by simp) x)]
    simp [F, D, mul_comm]
  have hBoundary (θ : Sphere n) : inner ℝ θ.1 (V θ.1) = 0 := by
    have hz : ψ θ.1 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have hb : θ.1 ∈ unitBall n := ψ.tsupport_subset h
      exact (lt_irrefl _ ((mem_sphere_zero_iff_norm.mp θ.2) ▸ mem_ball_zero_iff.mp hb)).elim
    simp [V, H, hz]
  have hZero : (∫ x, euclideanDivergence V x ∂ν[n]) = 0 := by
    have he := integral_unitBall_divergence_normalized hn (hV.of_le (by simp))
    simpa only [hBoundary, integral_zero, mul_zero] using he
  have hD : Continuous D := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).continuous.clm_apply S.continuous
  have hInt₁ : Integrable (fun x => ψ x * F x) ν[n] :=
    ((ψ.continuous.mul hF).continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
      ball_subset_closedBall
  have hInt₂ : Integrable (fun x => D x * G x) ν[n] :=
    ((hD.mul hG.continuous).continuousOn.integrableOn_compact (isCompact_closedBall (0 : E n) 1)).mono_set
      ball_subset_closedBall
  have hZero' : (∫ x, ψ x * F x ∂ν[n]) + (∫ x, D x * G x ∂ν[n]) = 0 := by
    rw [← integral_add hInt₁ hInt₂]
    simpa only [hPoint] using hZero
  have hLeft : (∫ x, ψ x * gS x ∂ν[n]) = ∫ x, ψ x * F x ∂ν[n] :=
    integral_congr_ae (hAE.mono fun x hx => congrArg (fun r : ℝ => ψ x * r) hx)
  have hRight : (∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * g x ∂ν[n]) =
      ∫ x, D x * G x ∂ν[n] := integral_congr_ae (hRep.mono fun x hx => by simp [D, hx])
  rw [hLeft, hRight]
  linarith only [hZero']

end KEBall
