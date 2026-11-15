import KEBall.BedfordTaylorExteriorDerivative
import KEBall.BedfordTaylorSmoothCoefficients
import KEBall.CofactorDivergence

/-!
# Classical density of the second mixed Hessian

Differentiating the weighted Hessian gives the mixed two-by-two minors.
The terms differentiating the second potential cancel by the closedness
identities for its rows and columns.
-/

set_option autoImplicit false

open Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology

namespace KEBall.BedfordTaylor

open KEBallProbe
open PshLines.FirstPass (ComplexModel)
open PshLines.FirstPass.MongeAmpere (IsSmoothPshOn)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Opens E}

private theorem dz_congr_at {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) (a b : E) :
    dz a b f x = dz a b g x := by
  simp only [dz, rd, (h.fderiv (𝕜 := ℝ)).eq_of_nhds]

private theorem dz_add_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (a b : E) :
    dz a b (fun y => f y + g y) x = dz a b f x + dz a b g x := by
  simp only [dz, rd, fderiv_fun_add (hf.differentiableAt (by simp))
    (hg.differentiableAt (by simp)), add_apply]
  ring

private theorem dz_dz_mul_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (a b c d : E) :
    dz a b (dz c d (fun y => f y * g y)) x =
      dz a b (dz c d f) x * g x + dz c d f x * dz a b g x +
      (dz a b f x * dz c d g x + f x * dz a b (dz c d g) x) := by
  have hf₁ : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  have hg₁ : ContDiffAt ℝ 1 g x := hg.of_le (by simp)
  have heq : dz c d (fun y => f y * g y) =ᶠ[𝓝 x]
      fun y => dz c d f y * g y + f y * dz c d g y := by
    filter_upwards [hf₁.eventually (by simp), hg₁.eventually (by simp)] with y hfy hgy
    exact dz_mul_differentiableAt (hfy.differentiableAt (by simp)) (hgy.differentiableAt (by simp)) c d
  rw [dz_congr_at heq a b, dz_add_at ((smoothAt_dz hf c d).mul hg) (hf.mul (smoothAt_dz hg c d)),
    dz_mul_differentiableAt ((smoothAt_dz hf c d).differentiableAt (by simp))
      (hg.differentiableAt (by simp)),
    dz_mul_differentiableAt (hf.differentiableAt (by simp))
      ((smoothAt_dz hg c d).differentiableAt (by simp))]

variable [NormedSpace ℂ E]

private theorem classicalComplexHessianEntry_row_closed {p : E → ℝ} {x : E}
    (hp : ContDiffAt ℝ ∞ p x) (a b s : E) :
    dz a (Complex.I • a) (classicalComplexHessianEntry p b s) x =
      dz b (Complex.I • b) (classicalComplexHessianEntry p a s) x := by
  exact complex_hessian_third_comm_at (Complex.ofRealCLM.contDiff.contDiffAt.comp x hp)
    a (Complex.I • a) b (Complex.I • b) s (Complex.I • s)

private theorem classicalComplexHessianEntry_column_closed {p : E → ℝ} {x : E}
    (hp : ContDiffOn ℝ ∞ p U) (hx : x ∈ U) (b r s : E) :
    dz r (-(Complex.I • r)) (classicalComplexHessianEntry p b s) x =
      dz s (-(Complex.I • s)) (classicalComplexHessianEntry p b r) x := by
  let f : E → ℂ := fun y => p y
  have hf : ContDiffOn ℝ ∞ f U := Complex.ofRealCLM.contDiff.comp_contDiffOn hp
  have hfAt := hf.contDiffAt (U.isOpen.mem_nhds hx)
  have hcomm : dz r (-(Complex.I • r)) (dz s (-(Complex.I • s)) f) =ᶠ[𝓝 x]
      dz s (-(Complex.I • s)) (dz r (-(Complex.I • r)) f) := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact dz_comm_on U.isOpen hf _ _ _ _ hy
  unfold classicalComplexHessianEntry
  change dz r (-(Complex.I • r)) (dz b (Complex.I • b) (dz s (-(Complex.I • s)) f)) x =
    dz s (-(Complex.I • s)) (dz b (Complex.I • b) (dz r (-(Complex.I • r)) f)) x
  rw [dz_comm_at (smoothAt_dz hfAt s (-(Complex.I • s))) r (-(Complex.I • r)) b (Complex.I • b),
    dz_comm_at (smoothAt_dz hfAt r (-(Complex.I • r))) s (-(Complex.I • s)) b (Complex.I • b)]
  exact dz_congr_at hcomm _ _

/-- The mixed minor obtained by differentiating the determinant of the
sum of two Hessian matrices on the two indicated tuples of directions. -/
noncomputable def smoothMixedHessianDensity (u p : E → ℝ) (v w : Fin 2 → E) (x : E) : ℂ :=
  classicalComplexHessianEntry u (v 0) (w 0) x * classicalComplexHessianEntry p (v 1) (w 1) x -
  classicalComplexHessianEntry u (v 1) (w 0) x * classicalComplexHessianEntry p (v 0) (w 1) x -
  classicalComplexHessianEntry u (v 0) (w 1) x * classicalComplexHessianEntry p (v 1) (w 0) x +
  classicalComplexHessianEntry u (v 1) (w 1) x * classicalComplexHessianEntry p (v 0) (w 0) x

theorem contDiffOn_smoothMixedHessianDensity {u p : E → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hp : ContDiffOn ℝ ∞ p U) (v w : Fin 2 → E) :
    ContDiffOn ℝ ∞ (smoothMixedHessianDensity u p v w) U := by
  have hU := contDiffOn_classicalComplexHessianEntry hu
  have hP := contDiffOn_classicalComplexHessianEntry hp
  exact (((hU (v 0) (w 0)).mul (hP (v 1) (w 1))).sub ((hU (v 1) (w 0)).mul (hP (v 0) (w 1)))).sub
    ((hU (v 0) (w 1)).mul (hP (v 1) (w 0))) |>.add ((hU (v 1) (w 1)).mul (hP (v 0) (w 0)))

private theorem smoothMixedHessianDensity_eq_derivatives {u p : E → ℝ} {x : E}
    (hu : ContDiffOn ℝ ∞ u U) (hp : ContDiffOn ℝ ∞ p U) (hx : x ∈ U) (v w : Fin 2 → E) :
    let F := fun a r b s =>
      dz a (Complex.I • a) (dz r (-(Complex.I • r))
        (fun y => (u y : ℂ) * classicalComplexHessianEntry p b s y)) x
    F (v 0) (w 0) (v 1) (w 1) - F (v 1) (w 0) (v 0) (w 1) -
      F (v 0) (w 1) (v 1) (w 0) + F (v 1) (w 1) (v 0) (w 0) =
      smoothMixedHessianDensity u p v w x := by
  have hf : ContDiffAt ℝ ∞ (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (hu.contDiffAt (U.isOpen.mem_nhds hx))
  have hH (b s : E) : ContDiffAt ℝ ∞ (classicalComplexHessianEntry p b s) x :=
    (contDiffOn_classicalComplexHessianEntry hp b s).contDiffAt (U.isOpen.mem_nhds hx)
  have hprod (a r b s : E) :
      dz a (Complex.I • a) (dz r (-(Complex.I • r))
        (fun y => (u y : ℂ) * classicalComplexHessianEntry p b s y)) x =
      classicalComplexHessianEntry u a r x * classicalComplexHessianEntry p b s x +
        dz r (-(Complex.I • r)) (fun y => (u y : ℂ)) x *
          dz a (Complex.I • a) (classicalComplexHessianEntry p b s) x +
        (dz a (Complex.I • a) (fun y => (u y : ℂ)) x *
          dz r (-(Complex.I • r)) (classicalComplexHessianEntry p b s) x +
          (u x : ℂ) * dz a (Complex.I • a)
            (dz r (-(Complex.I • r)) (classicalComplexHessianEntry p b s)) x) :=
    dz_dz_mul_at hf (hH b s) _ _ _ _
  have hcol (b r s : E) :
      dz r (-(Complex.I • r)) (classicalComplexHessianEntry p b s) =ᶠ[𝓝 x]
        dz s (-(Complex.I • s)) (classicalComplexHessianEntry p b r) := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact classicalComplexHessianEntry_column_closed hp hy b r s
  have hfour (a b r s : E) :
      dz a (Complex.I • a) (dz r (-(Complex.I • r)) (classicalComplexHessianEntry p b s)) x =
        dz a (Complex.I • a) (dz s (-(Complex.I • s)) (classicalComplexHessianEntry p b r)) x :=
    dz_congr_at (hcol b r s) _ _
  dsimp only
  simp only [hprod, smoothMixedHessianDensity]
  rw [classicalComplexHessianEntry_row_closed (hp.contDiffAt (U.isOpen.mem_nhds hx)) (v 0) (v 1) (w 1),
    classicalComplexHessianEntry_row_closed (hp.contDiffAt (U.isOpen.mem_nhds hx)) (v 0) (v 1) (w 0),
    (hcol (v 1) (w 0) (w 1)).eq_of_nhds,
    (hcol (v 0) (w 0) (w 1)).eq_of_nhds,
    hfour (v 0) (v 1) (w 0) (w 1), hfour (v 1) (v 0) (w 0) (w 1)]
  ring

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u p : ComplexModel n → ℝ}

/-- The distributional second mixed Hessian of smooth PSH potentials has
the classical mixed-minor density. -/
theorem secondMixedHessian_integral_of_isSmoothPshOn
    (hu : IsSmoothPshOn Ω u) (hp : IsSmoothPshOn Ω p)
    (v w : Fin 2 → ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    secondMixedHessian (isLocallyBoundedPshOn_of_isSmoothPshOn hu)
        (isLocallyBoundedPshOn_of_isSmoothPshOn hp) v w φ =
      ∫ x, φ x • smoothMixedHessianDensity u p v w x := by
  let g := fun b s x => (u x : ℂ) * classicalComplexHessianEntry p b s x
  let F := fun a r b s => dz a (Complex.I • a) (dz r (-(Complex.I • r)) (g b s))
  have hg (b s : ComplexModel n) : ContDiffOn ℝ ∞ (g b s) Ω :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hu.1).mul
      (contDiffOn_classicalComplexHessianEntry hp.1 b s)
  have hF (a r b s : ComplexModel n) :
      wirtingerDerivative a (Complex.I • a)
          (wirtingerDerivative r (-(Complex.I • r))
            (weightedComplexHessian (isLocallyBoundedPshOn_of_isSmoothPshOn hu)
              (isLocallyBoundedPshOn_of_isSmoothPshOn hp) b s)) φ =
        ∫ x, φ x • F a r b s x := by
    rw [weightedComplexHessian_eq_density_of_isSmoothPshOn hu hp,
      wirtingerDerivative_complexRegularDistribution (hg b s),
      wirtingerDerivative_complexRegularDistribution (smoothOn_dz Ω.isOpen (hg b s) _ _),
      complexRegularDistribution_apply]
  have hi (a r b s : ComplexModel n) : Integrable (fun x => φ x • F a r b s x) := by
    apply φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
    exact locallyIntegrableOn_of_contDiffOn
      (smoothOn_dz Ω.isOpen (smoothOn_dz Ω.isOpen (hg b s) _ _) _ _)
  rw [secondMixedHessian_eq]
  simp only [sub_apply, add_apply, hF]
  let A := fun x => φ x • F (v 0) (w 0) (v 1) (w 1) x
  let B := fun x => φ x • F (v 1) (w 0) (v 0) (w 1) x
  let C := fun x => φ x • F (v 0) (w 1) (v 1) (w 0) x
  let D := fun x => φ x • F (v 1) (w 1) (v 0) (w 0) x
  have hA : Integrable A := hi (v 0) (w 0) (v 1) (w 1)
  have hB : Integrable B := hi (v 1) (w 0) (v 0) (w 1)
  have hC : Integrable C := hi (v 0) (w 1) (v 1) (w 0)
  have hD : Integrable D := hi (v 1) (w 1) (v 0) (w 0)
  change (∫ x, A x) - (∫ x, B x) - (∫ x, C x) + (∫ x, D x) = _
  rw [← integral_sub hA hB]
  change (∫ x, (A - B) x) - (∫ x, C x) + (∫ x, D x) = _
  rw [← integral_sub (hA.sub hB) hC]
  change (∫ x, (A - B - C) x) + (∫ x, D x) = _
  rw [← integral_add ((hA.sub hB).sub hC) hD]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Pi.sub_apply, A, B, C, D, ← smul_sub, ← smul_add]
  by_cases hx : x ∈ Ω
  · exact congrArg (φ x • ·) (smoothMixedHessianDensity_eq_derivatives hu.1 hp.1 hx v w)
  · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
    simp only [hφ, zero_smul]

end KEBall.BedfordTaylor
