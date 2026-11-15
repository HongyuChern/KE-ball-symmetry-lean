import KEBall.BedfordTaylorSmoothCoefficients
import PshLines.Regularization.HolomorphicPullback

/-!
# Hessians on finite tuples of complex directions

The Hessian on such a tuple is the coordinate Hessian of the affine
holomorphic pullback. This provides its semipositivity even when the
directions are linearly dependent.
-/

set_option autoImplicit false

open Filter Set TopologicalSpace
open scoped ComplexOrder ContDiff Topology

namespace KEBall.BedfordTaylor

open KEBallProbe PshLines
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere
  (coordinateVector complexHessian IsSmoothPshOn isSmoothPshOn_of_psh)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

private theorem rd_rd_real {x : E} (hf : ContDiffAt ℝ ∞ f x) (a b : E) :
    rd a (rd b (fun y => (f y : ℂ))) x = (PshLines.realHessian f x a b : ℂ) := by
  have hf₁ : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  have heq : rd b (fun y => (f y : ℂ)) =ᶠ[𝓝 x] (fun y => (fderiv ℝ f y b : ℂ)) := by
    filter_upwards [hf₁.eventually (by simp)] with y hy
    change fderiv ℝ (fun z => (f z : ℂ)) y b = _
    have hd := Complex.ofRealCLM.hasFDerivAt.comp y (hy.differentiableAt one_ne_zero).hasFDerivAt
    change HasFDerivAt (fun z => (f z : ℂ)) _ y at hd
    rw [hd.fderiv]
    rfl
  change fderiv ℝ (rd b (fun y => (f y : ℂ))) x a = _
  rw [heq.fderiv_eq]
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hr := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const b x)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hr
  change HasFDerivAt (fun y => (fderiv ℝ f y b : ℂ)) _ x at hc
  rw [hc.fderiv, PshLines.realHessian_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, zero_apply, map_zero,
    zero_add, Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply]

variable [NormedSpace ℂ E]

theorem classicalComplexHessianEntry_eq_realHessian {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (a b : E) :
    classicalComplexHessianEntry f a b x =
      ((PshLines.realHessian f x a b +
        PshLines.realHessian f x (Complex.I • a) (Complex.I • b) : ℝ) : ℂ) / 4 +
      Complex.I * ((PshLines.realHessian f x a (Complex.I • b) -
        PshLines.realHessian f x (Complex.I • a) b : ℝ) : ℂ) / 4 := by
  have hfC : ContDiffAt ℝ ∞ (fun y => (f y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  unfold classicalComplexHessianEntry
  rw [dz, rd_dz_at hfC, rd_dz_at hfC]
  simp only [rd_rd_real hf, PshLines.realHessian_eq_fderiv, map_neg]
  push_cast
  ring_nf
  simp
  ring

variable {n k : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}

private noncomputable def directionMap (v : Fin k → ComplexModel n) :
    ComplexModel k →L[ℂ] ComplexModel n :=
  ∑ i, ((ContinuousLinearMap.id ℂ ℂ).smulRight (v i)).comp (EuclideanSpace.proj i)

private theorem directionMap_coordinateVector (v : Fin k → ComplexModel n) (j : Fin k) :
    directionMap v (coordinateVector j) = v j := by
  classical
  simp [directionMap, coordinateVector, apply_ite, Finset.sum_ite_eq']

private theorem realHessian_affine {x : ComplexModel n} (hx : x ∈ Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (A : ComplexModel k →L[ℂ] ComplexModel n)
    (a b : ComplexModel k) :
    PshLines.realHessian (fun y => u (x + A y)) 0 a b =
      PshLines.realHessian u x (A a) (A b) := by
  let s := (fun y : ComplexModel n => x + y) ⁻¹' (Ω : Set (ComplexModel n))
  have hs : IsOpen s := Ω.isOpen.preimage (continuous_const.add continuous_id)
  have hs₀ : 0 ∈ s := by simpa [s] using hx
  have hshift : ContDiffOn ℝ ∞ (fun y => u (x + y)) s :=
    hu.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hy => hy)
  let B := A.restrictScalars ℝ
  have hB₀ : B 0 ∈ s := by rwa [map_zero]
  have hsB := hs.preimage B.continuous
  have h := B.iteratedFDerivWithin_comp_right hshift hs.uniqueDiffOn hsB.uniqueDiffOn hB₀
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [iteratedFDerivWithin_of_isOpen 2 hsB hB₀, iteratedFDerivWithin_of_isOpen 2 hs hB₀,
    iteratedFDeriv_comp_add_left, map_zero, add_zero] at h
  have hab : (fun i => B (![a, b] i)) = ![B a, B b] := by
    ext i
    fin_cases i <;> rfl
  exact (congrArg (fun M => M ![a, b]) h).trans (by
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hab]
    rfl)

/-- Every matrix obtained by evaluating a smooth PSH Hessian on a tuple
of directions is positive semidefinite. -/
theorem posSemidef_classicalComplexHessianEntry
    (hu : IsSmoothPshOn Ω u) {x : ComplexModel n} (hx : x ∈ Ω)
    (v : Fin k → ComplexModel n) :
    (Matrix.of fun i j => classicalComplexHessianEntry u (v i) (v j) x).PosSemidef := by
  let A := directionMap v
  let F : ComplexModel k → ComplexModel n := fun y => x + A y
  let V : Opens (ComplexModel k) :=
    ⟨F ⁻¹' (Ω : Set (ComplexModel n)), Ω.isOpen.preimage (continuous_const.add A.continuous)⟩
  have h₀ : (0 : ComplexModel k) ∈ V := by
    change x + A 0 ∈ Ω
    simpa using hx
  have hF : MapsTo F V Ω := fun _ hy => hy
  have hs : ContDiffOn ℝ ∞ (u ∘ F) V :=
    hu.1.comp (contDiff_const.add (A.restrictScalars ℝ).contDiff).contDiffOn hF
  have hdiff : Differentiable ℂ F :=
    (show ContDiff ℂ ∞ F from contDiff_const.add A.contDiff).differentiable (by simp)
  have hp : PlurisubharmonicOn (fun y => ((u ∘ F) y : EReal)) V :=
    Regularization.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic V.isOpen
      hdiff.differentiableOn hF hu.2.1
  have h := (isSmoothPshOn_of_psh hs hp).2.2 0 h₀
  have hA (j : Fin k) : A (coordinateVector j) = v j := directionMap_coordinateVector v j
  have hAI (j : Fin k) : A (Complex.I • coordinateVector j) = Complex.I • v j := by
    rw [map_smul, hA]
  have heq : complexHessian (u ∘ F) 0 =
      Matrix.of (fun i j => classicalComplexHessianEntry u (v i) (v j) x) := by
    ext i j : 1
    simp only [complexHessian, Matrix.of_apply]
    rw [classicalComplexHessianEntry_eq_realHessian
      (hu.1.contDiffAt (Ω.isOpen.mem_nhds hx))]
    change ((PshLines.realHessian (fun y => u (x + A y)) 0 (coordinateVector i) (coordinateVector j) +
      PshLines.realHessian (fun y => u (x + A y)) 0 (Complex.I • coordinateVector i)
        (Complex.I • coordinateVector j) : ℝ) : ℂ) / 4 +
      Complex.I * ((PshLines.realHessian (fun y => u (x + A y)) 0 (coordinateVector i)
        (Complex.I • coordinateVector j) - PshLines.realHessian (fun y => u (x + A y)) 0
          (Complex.I • coordinateVector i) (coordinateVector j) : ℝ) : ℂ) / 4 = _
    simp only [realHessian_affine hx hu.1 A, hA, hAI]
  rwa [heq] at h

end KEBall.BedfordTaylor
