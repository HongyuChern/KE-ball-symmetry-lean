import KEBall.FiberEnergyVariation
import KEBall.ComplexMaximum

/-!
# Complex cofactor integration by parts on a fiber ball
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Matrix

namespace KEBall.MoserTrudinger

open KEBallProbe

private noncomputable def wirtingerDivergence {n : ℕ} (F : E n → Fin n → ℂ) (x : E n) : ℂ :=
  ∑ i : Fin n, partialZ i (fun y => F y i) x

private theorem integral_wirtingerDivergence_zero {n : ℕ} (hn : 0 < n)
    {F : E n → Fin n → ℂ} (hF : ∀ i, ContDiff ℝ ∞ (fun x => F x i))
    (h0 : ∀ x ∈ unitSphere n, F x = 0) :
    (∫ x in unitBall n, wirtingerDivergence F x ∂volume0 n) = 0 := by
  have hre {V : E n → Fin n → ℂ} (hV : ∀ i, ContDiff ℝ ∞ (fun x => V x i))
      (hV0 : ∀ x ∈ unitSphere n, V x = 0) :
      (∫ x in unitBall n, (wirtingerDivergence V x).re ∂volume0 n) = 0 := by
    have hs : ContDiff ℝ ∞ (fun x => complexVectorReal (V x)) :=
      contDiffOn_univ.mp (complexVectorReal_contDiffOn (fun i => (hV i).contDiffOn))
    have h := integral_unitBall_divergence_normalized hn (hs.of_le (by simp))
    have hd (x : E n) : euclideanDivergence (fun y => complexVectorReal (V y)) x =
        2 * (wirtingerDivergence V x).re :=
      euclideanDivergence_complexVectorReal (fun i => (hV i).differentiable (by simp) x)
    have hzero : (∫ θ : Sphere n, inner ℝ θ.1 (complexVectorReal (V θ.1)) ∂sphere0 n) = 0 := by
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun θ => by simp [hV0 _ θ.2, complexVectorReal]
    simp_rw [hd] at h
    rw [integral_const_mul, hzero, mul_zero] at h
    linarith
  let J : E n → Fin n → ℂ := fun x i => Complex.I * F x i
  have hJ (i : Fin n) : ContDiff ℝ ∞ (fun x => J x i) := contDiff_const.mul (hF i)
  have hJ0 (x : E n) (hx : x ∈ unitSphere n) : J x = 0 := by
    funext i
    simp [J, h0 x hx]
  have hmul (x : E n) : (wirtingerDivergence J x).re = -(wirtingerDivergence F x).im := by
    have he (i : Fin n) :
        partialZ i (fun y => J y i) x = Complex.I * partialZ i (fun y => F y i) x :=
      ComplexMaximumAux.dz_const_mul_differentiableAt ((hF i).differentiable (by simp) x)
        Complex.I (realDirection i) (imagDirection i)
    simp only [wirtingerDivergence, he, ← Finset.mul_sum, Complex.I_mul_re]
  have hi : IntegrableOn (wirtingerDivergence F) (unitBall n) (volume0 n) := by
    have hC : Continuous (wirtingerDivergence F) := by
      apply continuous_finsetSum
      intro i _
      exact (contDiff_iff_contDiffAt.mpr fun _ =>
        smoothAt_dz (hF i).contDiffAt (realDirection i) (imagDirection i)).continuous
    exact hC.continuousOn.integrableOn_of_subset_isCompact
      (isCompact_closedBall _ _) measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  apply Complex.ext
  · change RCLike.re (∫ x in unitBall n, wirtingerDivergence F x ∂volume0 n) = 0
    rw [← integral_re hi]
    exact hre hF h0
  · change RCLike.im (∫ x in unitBall n, wirtingerDivergence F x ∂volume0 n) = 0
    rw [← integral_im hi]
    have h := hre hJ hJ0
    simp_rw [hmul, integral_neg, neg_eq_zero] at h
    exact h

/-- The complex contraction of two first derivatives with the adjugate. -/
noncomputable def cofactorGradientContraction {n : ℕ} (u f h : E n → ℝ) (x : E n) : ℂ :=
  ∑ i : Fin n, partialZ i (fun y => (f y : ℂ)) x * cofactorVectorField u h x i

theorem continuous_cofactorGradientContraction {n : ℕ} {u f h : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    Continuous (cofactorGradientContraction u f h) := by
  have hfc : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  apply continuous_finsetSum
  intro i _
  have hi : ContDiff ℝ ∞ (partialZ i (fun x => (f x : ℂ))) :=
    contDiff_iff_contDiffAt.mpr fun _ => smoothAt_dz hfc.contDiffAt _ _
  exact hi.continuous.mul
    (contDiffOn_univ.mp (cofactorVectorField_contDiffOn isOpen_univ hu.contDiffOn hh.contDiffOn i)).continuous

theorem complexHessian_isHermitian_of_smooth {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) : (complexHessian u x).IsHermitian := by
  have he (i j : Fin n) : complexHessian u x i j =
      ((1 / 4 : ℝ) : ℂ) *
        ((realHessian u x (realDirection i) (realDirection j) : ℝ) +
         (realHessian u x (imagDirection i) (imagDirection j) : ℝ) +
         Complex.I * ((realHessian u x (realDirection i) (imagDirection j) : ℝ) -
           (realHessian u x (imagDirection i) (realDirection j) : ℝ))) := by
    rw [complexHessian_real_entry hu]
    norm_num
  ext i j
  change star (complexHessian u x j i) = complexHessian u x i j
  rw [he j i, he i j, Complex.star_def]
  simp only [map_mul, map_add, map_sub, Complex.conj_ofReal, Complex.conj_I]
  rw [realHessian_symm hu (realDirection j) (realDirection i),
    realHessian_symm hu (imagDirection j) (imagDirection i),
    realHessian_symm hu (realDirection j) (imagDirection i),
    realHessian_symm hu (imagDirection j) (realDirection i)]
  ring

private theorem trace_mul_isReal {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace = ((A * B).trace.re : ℂ) := by
  have h : star ((A * B).trace) = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have hi : (A * B).trace.im = 0 := by
    have he := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at he
    linarith
  exact Complex.ext rfl (by simpa using hi)

/-- Complex integration by parts, retaining the imaginary component of
the mixed gradient pairing. -/
theorem integral_cofactorGradientContraction {n : ℕ} (hn : 0 < n) {u f h : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hf0 : ∀ x ∈ unitSphere n, f x = 0) :
    (∫ x in unitBall n, cofactorGradientContraction u f h x ∂volume0 n) =
      -(∫ x in unitBall n, ((f x * cofactorContraction u h x : ℝ) : ℂ) ∂volume0 n) := by
  let F : E n → Fin n → ℂ := fun x i => (f x : ℂ) * cofactorVectorField u h x i
  have hF' (i : Fin n) : ContDiff ℝ ∞ (fun x => cofactorVectorField u h x i) :=
    contDiffOn_univ.mp (cofactorVectorField_contDiffOn isOpen_univ hu.contDiffOn hh.contDiffOn i)
  have hfc : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hF (i : Fin n) : ContDiff ℝ ∞ (fun x => F x i) := hfc.mul (hF' i)
  have hF0 (x : E n) (hx : x ∈ unitSphere n) : F x = 0 := by
    funext i
    simp [F, hf0 x hx]
  have hDiv := integral_wirtingerDivergence_zero hn hF hF0
  have hpoint (x : E n) (hx : x ∈ unitBall n) :
      wirtingerDivergence F x = cofactorGradientContraction u f h x +
        ((f x * cofactorContraction u h x : ℝ) : ℂ) := by
    have hp (i : Fin n) : partialZ i (fun y => F y i) x =
        partialZ i (fun y => (f y : ℂ)) x * cofactorVectorField u h x i +
          (f x : ℂ) * partialZ i (fun y => cofactorVectorField u h y i) x :=
      dz_mul_differentiableAt (hfc.differentiable (by simp) x) ((hF' i).differentiable (by simp) x)
        (realDirection i) (imagDirection i)
    have hdet : IsUnit (complexHessian u x).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (huP x hx).isUnit
    have hc := Complex.ofRealCLM.contDiff.comp hu
    have hpiola (j : Fin n) :
        (∑ i : Fin n, partialZ i (fun y => (complexHessian u y).adjugate j i) x) = 0 :=
      cofactor_divergence_at hc.contDiffAt realDirection imagDirection hdet j
    unfold wirtingerDivergence cofactorGradientContraction cofactorContraction
    simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_partialZ_cofactorVectorField_of_piola hu.contDiffAt hh.contDiffAt hpiola]
    push_cast
    congr 1
    let A := (complexHessian u x).adjugate
    let B := complexHessian h x
    have he : (∑ i : Fin n, ∑ j : Fin n, A j i * B i j) = (A * B).trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      rw [Finset.sum_comm]
    rw [he, trace_mul_isReal (huP x hx).isHermitian.adjugate
      (complexHessian_isHermitian_of_smooth hh.contDiffAt)]
    simp only [Complex.ofReal_re]
  have hI {g : E n → ℂ} (hg : Continuous g) : IntegrableOn g (unitBall n) (volume0 n) :=
    hg.continuousOn.integrableOn_of_subset_isCompact (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall
      (by rw [volume0_unitBall n hn]; exact ENNReal.one_ne_top)
  have hL := hI (continuous_cofactorGradientContraction hu hf hh)
  have hR : IntegrableOn (fun x => ((f x * cofactorContraction u h x : ℝ) : ℂ))
      (unitBall n) (volume0 n) :=
    Complex.ofRealCLM.integrable_comp (integrable_mul_contraction hn isOpen_univ (subset_univ _)
      hu.contDiffOn hf.contDiffOn hh.contDiffOn)
  rw [setIntegral_congr_fun (show MeasurableSet (unitBall n) from measurableSet_ball) hpoint,
    integral_add hL hR] at hDiv
  exact eq_neg_of_add_eq_zero_left hDiv

end KEBall.MoserTrudinger
