import KEBall.DirichletNormalRecovery
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Upgrading the a.e. determinant identity after interior C² regularity

The actual first jet is identified with the derivative of the potential.
Continuity then gives the pointwise determinant equation and strict complex
Hessian positivity on the open ball.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

theorem fderiv_dirichlet_firstJet_eq_realHessian {n : ℕ}
    {w : E n → ℝ} {G : E n → E n →L[ℝ] ℝ}
    (hD : ∀ x ∈ unitBall n, HasFDerivAt w (G x) x)
    {x : E n} (hx : x ∈ unitBall n) :
    fderiv ℝ G x = realHessian w x := by
  have he : G =ᶠ[𝓝 x] fderiv ℝ w := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (hD y hy).fderiv.symm
  exact he.fderiv_eq

theorem continuousOn_complexHessian_of_interior_C2 {n : ℕ} {w : E n → ℝ}
    (hw : ContDiffOn ℝ 2 w (unitBall n)) :
    ContinuousOn (complexHessian w) (unitBall n) := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ w) (unitBall n) :=
    hw.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hDD : ContDiffOn ℝ 0 (realHessian w) (unitBall n) :=
    hD.fderiv_of_isOpen isOpen_ball (by norm_num)
  apply ContinuousOn.congr (f := fun x => complexHessianOfRealBilinear (realHessian w x))
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (contDiffOn_complexHessianOfRealBilinear hDD i j).continuousOn
  · intro x hx
    exact (complexHessianOfRealBilinear_eq (hw.contDiffAt (isOpen_ball.mem_nhds hx))).symm

theorem dirichlet_continuousOn_nonneg_of_ae {n : ℕ} {μ : Measure (E n)}
    [μ.IsOpenPosMeasure] {s : Set (E n)} (hs : IsOpen s)
    {f : E n → ℝ} (hf : ContinuousOn f s)
    (ha : ∀ᵐ x ∂μ.restrict s, 0 ≤ f x) :
    ∀ x ∈ s, 0 ≤ f x := by
  have he : (fun x => max (f x) 0) =ᵐ[μ.restrict s] f :=
    ha.mono fun x hx => max_eq_left hx
  have hPoint := Measure.eqOn_open_of_ae_eq he hs (hf.sup continuousOn_const) hf
  intro x hx
  exact (le_max_right (f x) 0).trans_eq (hPoint hx)

theorem dirichlet_complexHessian_posDef_of_interior_C2_ae {n : ℕ}
    {μ : Measure (E n)} [μ.IsOpenPosMeasure] {w : E n → ℝ}
    (hw : ContDiffOn ℝ 2 w (unitBall n))
    (ha : ∀ᵐ x ∂μ.restrict (unitBall n), (complexHessian w x).PosDef)
    (hd : ∀ x ∈ unitBall n, 0 < (complexHessian w x).det.re) :
    ∀ x ∈ unitBall n, (complexHessian w x).PosDef := by
  have hHC := continuousOn_complexHessian_of_interior_C2 hw
  have hEntry (i j : Fin n) : ContinuousOn (fun x => complexHessian w x i j) (unitBall n) :=
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hHC)
  have hQ (z : Fin n → ℂ) :
      ContinuousOn (fun x => (star z ⬝ᵥ (complexHessian w x *ᵥ z)).re) (unitBall n) := by
    apply Complex.continuous_re.comp_continuousOn
    simp only [dotProduct, Matrix.mulVec]
    exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
      (continuousOn_finsetSum _ fun j _ => (hEntry i j).mul continuousOn_const)
  have hQN (z : Fin n → ℂ) :
      ∀ x ∈ unitBall n, 0 ≤ (star z ⬝ᵥ (complexHessian w x *ᵥ z)).re :=
    dirichlet_continuousOn_nonneg_of_ae isOpen_ball (hQ z)
      (ha.mono fun x hx => hx.posSemidef.re_dotProduct_nonneg z)
  intro x hx
  have hHerm := complexHessian_isHermitian_of_C2 (hw.contDiffAt (isOpen_ball.mem_nhds hx))
  have hPSD : (complexHessian w x).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨hHerm, fun z => ?_⟩
    exact RCLike.nonneg_iff.mpr ⟨hQN z x hx, hHerm.im_star_dotProduct_mulVec_self z⟩
  apply hPSD.posDef_iff_det_ne_zero.mpr
  intro hz
  have := hd x hx
  rw [hz, Complex.zero_re] at this
  exact (lt_irrefl 0) this

end KEBall
