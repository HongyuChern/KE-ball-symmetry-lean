import KEBall.DirichletWeakGradient
import KEBall.DirichletAngularDerivative

/-! Integration by parts along skew linear vector fields on the ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ContDiff Distributions Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

/-- Multiplication of a Dirichlet test function by a smooth scalar field. -/
noncomputable def dirichletTestMul {n : ℕ}
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {m : E n → ℝ} (hm : ContDiff ℝ ∞ m) :
    𝓓(dirichletBallOpens n, ℝ) :=
  ⟨fun x => ψ x * m x, ψ.contDiff.mul hm, ψ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans ψ.tsupport_subset⟩

@[simp] theorem dirichletTestMul_apply {n : ℕ}
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) {m : E n → ℝ} (hm : ContDiff ℝ ∞ m) (x : E n) :
    dirichletTestMul ψ hm x = ψ x * m x := rfl

private theorem skew_inner_diagonal {n : ℕ} (S : E n →L[ℝ] E n)
    (hS : star S = -S) (x : E n) : inner ℝ x (S x) = 0 := by
  have h := S.adjoint_inner_left x x
  change inner ℝ ((star S) x) x = inner ℝ x (S x) at h
  rw [hS, neg_apply, inner_neg_left, real_inner_comm x (S x)] at h
  linarith

/-- Distributional integration by parts along the angular field `x ↦ S x`. -/
theorem dirichletSobolev_integral_angularGradient {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (w : DirichletSobolev n)
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    (∫ x, ψ x * inner ℝ (S x) ((w : DirichletBallL2Pair n).snd x) ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (w : DirichletBallL2Pair n).fst x ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let f := (w : DirichletBallL2Pair n).fst
  let G := (w : DirichletBallL2Pair n).snd
  let L (i : Fin (2 * n)) : E n →L[ℝ] ℝ := (innerSL ℝ (b i)).comp S
  let χ (i : Fin (2 * n)) := dirichletTestMul ψ (L i).contDiff
  let D (i : Fin (2 * n)) : 𝓓(dirichletBallOpens n, ℝ) := TestFunction.lineDerivCLM ℝ (b i) (χ i)
  have hD (i : Fin (2 * n)) (x : E n) :
      D i x = fderiv ℝ (χ i : E n → ℝ) x (b i) := by
    change (TestFunction.lineDerivCLM ℝ (b i) (χ i) : 𝓓(dirichletBallOpens n, ℝ)) x = _
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    exact ((χ i).contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv
  have hDiagonal (i : Fin (2 * n)) : L i (b i) = 0 :=
    skew_inner_diagonal S hS (b i)
  have hProd (i : Fin (2 * n)) (x : E n) :
      D i x = L i x * fderiv ℝ (ψ : E n → ℝ) x (b i) := by
    rw [hD]
    change (fderiv ℝ (fun y => ψ y * L i y) x) (b i) = _
    rw [fderiv_fun_mul (ψ.contDiff.differentiable (by simp) x) (L i).differentiableAt]
    simp [hDiagonal, mul_comm]
  have hIntL (i : Fin (2 * n)) :
      Integrable (fun x => χ i x * inner ℝ (b i) (G x)) ν[n] := by
    have h : Integrable (fun x => inner ℝ (b i) (G x)) ν[n] :=
      (innerSL ℝ (b i)).integrable_comp ((Lp.memLp G).integrable (by norm_num))
    exact (χ i).integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (h.locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hIntR (i : Fin (2 * n)) : Integrable (fun x => D i x * f x) ν[n] :=
    (D i).integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (((Lp.memLp f).integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hL (x : E n) :
      (∑ i, χ i x * inner ℝ (b i) (G x)) = ψ x * inner ℝ (S x) (G x) := by
    change (∑ i, (ψ x * L i x) * inner ℝ (b i) (G x)) = _
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    calc
      _ = inner ℝ (∑ i, inner ℝ (b i) (S x) • b i) (G x) := by
        simp only [sum_inner, real_inner_smul_left]
        rfl
      _ = _ := by rw [b.sum_repr']
  have hR (x : E n) :
      (∑ i, D i x * f x) = fderiv ℝ (ψ : E n → ℝ) x (S x) * f x := by
    simp_rw [hProd]
    rw [← Finset.sum_mul]
    congr 1
    calc
      _ = fderiv ℝ (ψ : E n → ℝ) x (∑ i, inner ℝ (b i) (S x) • b i) := by
        simp only [map_sum, map_smul, smul_eq_mul]
        rfl
      _ = _ := by rw [b.sum_repr']
  have hSumL : (∫ x, ∑ i, χ i x * inner ℝ (b i) (G x) ∂ν[n]) =
      ∫ x, ψ x * inner ℝ (S x) (G x) ∂ν[n] :=
    integral_congr_ae (Eventually.of_forall hL)
  have hSumR : (∫ x, ∑ i, D i x * f x ∂ν[n]) =
      ∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * f x ∂ν[n] :=
    integral_congr_ae (Eventually.of_forall hR)
  change (∫ x, ψ x * inner ℝ (S x) (G x) ∂ν[n]) =
    -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * f x ∂ν[n])
  rw [← hSumL, ← hSumR, integral_finsetSum _ (fun i _ => hIntL i),
    integral_finsetSum _ (fun i _ => hIntR i), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa only [hD] using dirichletSobolev_integral_weakGradient w (χ i) (b i)

/-- The angular weak derivative is the pointwise contraction of the
Dirichlet gradient with the generating vector field, almost everywhere. -/
theorem dirichletSobolev_ae_eq_angularGradient {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (hS : star S = -S) (u v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n])) :
    (fun x => (v : DirichletBallL2Pair n).fst x) =ᵐ[ν[n]]
      (fun x => inner ℝ (S x) ((u : DirichletBallL2Pair n).snd x)) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let f := (v : DirichletBallL2Pair n).fst
  let G := (u : DirichletBallL2Pair n).snd
  let a (x : E n) := inner ℝ (S x) (G x)
  have hf : Integrable f ν[n] := (Lp.memLp f).integrable (by norm_num)
  have hG : Integrable G ν[n] := (Lp.memLp G).integrable (by norm_num)
  have ha : Integrable a ν[n] := by
    apply (hG.norm.const_mul ‖S‖).mono' (S.continuous.aestronglyMeasurable.inner hG.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx
    have hx' := (mem_ball_zero_iff.mp hx).le
    calc
      ‖a x‖ ≤ ‖S x‖ * ‖G x‖ := norm_inner_le_norm _ _
      _ ≤ ‖S‖ * ‖G x‖ := mul_le_mul_of_nonneg_right
        ((S.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) hx')) (norm_nonneg _)
  have hz : ∀ᵐ x ∂ν[n], x ∈ unitBall n → f x - a x = 0 := by
    apply (show IsOpen (unitBall n) from isOpen_ball).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub ha).locallyIntegrable.locallyIntegrableOn (unitBall n))
    intro ψ hψ hs hsub
    let φ : 𝓓(dirichletBallOpens n, ℝ) := ⟨ψ, hψ, hs, hsub⟩
    have hI {g : E n → ℝ} (hg : Integrable g ν[n]) :
        Integrable (fun x => ψ x * g x) ν[n] :=
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
        (hg.locallyIntegrable.locallyIntegrableOn (unitBall n))
    change (∫ x, ψ x * (f x - a x) ∂ν[n]) = 0
    simp_rw [mul_sub]
    rw [integral_sub (hI hf) (hI ha)]
    exact sub_eq_zero.mpr ((hv φ).trans (dirichletSobolev_integral_angularGradient hn S hS u φ).symm)
  filter_upwards [hz, ae_restrict_mem (μ := volume0 n)
    (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hx'
  exact sub_eq_zero.mp (hx hx')

/-- Differentiation of a Dirichlet test function along a smooth vector field. -/
noncomputable def dirichletTestFieldDerivative {n : ℕ}
    (ψ : 𝓓(dirichletBallOpens n, ℝ)) (X : E n → E n)
    (hX : ContDiff ℝ ∞ X) : 𝓓(dirichletBallOpens n, ℝ) := by
  let d (x : E n) := fderiv ℝ (ψ : E n → ℝ) x (X x)
  have hsub : tsupport d ⊆ tsupport (ψ : E n → ℝ) := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    apply (support_fderiv_subset ℝ)
    intro hz
    exact hx (by simp [d, hz])
  exact ⟨d, (ψ.contDiff.fderiv_right (by simp)).clm_apply hX,
    ψ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport d) hsub,
    hsub.trans ψ.tsupport_subset⟩

/-- Every fixed component of the weak gradient has an angular weak derivative.
Its representative is the corresponding component of the angular gradient
minus the first-order term from differentiating the generating field. -/
theorem dirichletSobolev_integral_angularGradientComponent {n : ℕ} (hn : 0 < n)
    (S : E n →L[ℝ] E n) (u v : DirichletSobolev n)
    (hv : ∀ ψ : 𝓓(dirichletBallOpens n, ℝ),
      (∫ x, ψ x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) =
        -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) * (u : DirichletBallL2Pair n).fst x ∂ν[n]))
    (e : E n) (ψ : 𝓓(dirichletBallOpens n, ℝ)) :
    (∫ x, ψ x * (inner ℝ e ((v : DirichletBallL2Pair n).snd x) -
        inner ℝ (S e) ((u : DirichletBallL2Pair n).snd x)) ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψ : E n → ℝ) x (S x) *
        inner ℝ e ((u : DirichletBallL2Pair n).snd x) ∂ν[n]) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  let f := (u : DirichletBallL2Pair n).fst
  let G := (u : DirichletBallL2Pair n).snd
  let H := (v : DirichletBallL2Pair n).snd
  let ψe := dirichletTestFieldDerivative ψ (fun _ => e) contDiff_const
  let ψS := dirichletTestFieldDerivative ψ S S.contDiff
  let ψeS := dirichletTestFieldDerivative ψe S S.contDiff
  let ψSe := dirichletTestFieldDerivative ψ (fun _ => S e) contDiff_const
  have hD (x : E n) : fderiv ℝ (ψS : E n → ℝ) x e = ψeS x + ψSe x := by
    have hd := (ψ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hs := (ψ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp; norm_cast)
    change fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y (S y)) x e =
      fderiv ℝ (fun y => fderiv ℝ (ψ : E n → ℝ) y e) x (S x) +
        fderiv ℝ (ψ : E n → ℝ) x (S e)
    rw [fderiv_clm_apply hd S.differentiableAt, fderiv_clm_apply hd (differentiableAt_const e)]
    simp [hs.eq e (S x), add_comm]
  have hPair (χ : 𝓓(dirichletBallOpens n, ℝ)) {a : E n → ℝ}
      (ha : Integrable a ν[n]) : Integrable (fun x => χ x * a x) ν[n] :=
    χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (ha.locallyIntegrable.locallyIntegrableOn (unitBall n))
  have hf : Integrable f ν[n] := (Lp.memLp f).integrable (by norm_num)
  have hi₁ : Integrable (fun x => ψ x * inner ℝ e (H x)) ν[n] :=
    hPair ψ ((innerSL ℝ e).integrable_comp ((Lp.memLp H).integrable (by norm_num)))
  have hi₂ : Integrable (fun x => ψ x * inner ℝ (S e) (G x)) ν[n] :=
    hPair ψ ((innerSL ℝ (S e)).integrable_comp ((Lp.memLp G).integrable (by norm_num)))
  have hSum : (∫ x, fderiv ℝ (ψS : E n → ℝ) x e * f x ∂ν[n]) =
      (∫ x, ψeS x * f x ∂ν[n]) + (∫ x, ψSe x * f x ∂ν[n]) := by
    rw [← integral_add (hPair ψeS hf) (hPair ψSe hf)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change fderiv ℝ (ψS : E n → ℝ) x e * f x = ψeS x * f x + ψSe x * f x
      rw [hD, add_mul]
  have hV : (∫ x, ψ x * inner ℝ e (H x) ∂ν[n]) = ∫ x, ψeS x * f x ∂ν[n] :=
    (dirichletSobolev_integral_weakGradient v ψ e).trans (by
      change -(∫ x, ψe x * (v : DirichletBallL2Pair n).fst x ∂ν[n]) = _
      rw [hv ψe, neg_neg]
      rfl)
  have hU : (∫ x, ψ x * inner ℝ (S e) (G x) ∂ν[n]) =
      -(∫ x, ψSe x * f x ∂ν[n]) := dirichletSobolev_integral_weakGradient u ψ (S e)
  have hS' : (∫ x, ψS x * inner ℝ e (G x) ∂ν[n]) =
      -(∫ x, fderiv ℝ (ψS : E n → ℝ) x e * f x ∂ν[n]) :=
    dirichletSobolev_integral_weakGradient u ψS e
  change (∫ x, ψ x * (inner ℝ e (H x) - inner ℝ (S e) (G x)) ∂ν[n]) =
    -(∫ x, ψS x * inner ℝ e (G x) ∂ν[n])
  simp_rw [mul_sub]
  rw [integral_sub hi₁ hi₂, hV, hU, hS', hSum, neg_neg, sub_neg_eq_add]

end KEBall
