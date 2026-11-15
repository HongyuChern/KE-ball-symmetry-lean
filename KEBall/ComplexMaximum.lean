import KEBall.RealHessian
import KEBall.LogDetConcavity
import PoincareLib.Geometry.Riemannian.ScalarOperators.Extrema

/-!
# The actual complex Laplacian at a local maximum

The real second derivative is restricted to affine lines, using the upstream
one-dimensional second derivative test. The frozen real/complex Hessian
identity then gives the sign of every complex quadratic form. A Gram factor
of the actual inverse Hessian yields the sign of its trace contraction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped ContDiff BigOperators Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace KEBall
open KEBallProbe

/-- The actual real Frechet Hessian is nonpositive on every direction at a
local maximum. Only smoothness at the point is used. -/
theorem realHessian_nonpos_of_isLocalMax {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (hmax : IsLocalMax h x) (v : E n) :
    realHessian h x v v ≤ 0 := by
  let γ : ℝ → E n := fun t => x + t • v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa only [γ, id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add x
  have hγ0 : γ 0 = x := by simp [γ]
  have ht : Tendsto γ (𝓝 0) (𝓝 x) := by
    simpa only [hγ0] using (hγ 0).continuousAt.tendsto
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y := by
    filter_upwards [(hh.of_le (m := 1) (by simp)).eventually (by simp)] with y hy
    exact hy.differentiableAt one_ne_zero
  have heq : deriv (fun t => h (γ t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ h (γ t) v) := by
    filter_upwards [ht.eventually hnear] with t htd
    exact (htd.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hdf := (hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hd := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hdγ : HasDerivAt (fun t => fderiv ℝ h (γ t) v)
      (realHessian h x v v) 0 := by
    have hd' : HasFDerivAt (fun y => fderiv ℝ h y v) ((realHessian h x).flip v) x := by
      simpa [realHessian] using hd
    have hdAt : HasFDerivAt (fun y => fderiv ℝ h y v) ((realHessian h x).flip v) (γ 0) := by
      simpa only [hγ0] using hd' 
    have hcomp := hdAt.comp_hasDerivAt 0 (hγ 0)
    exact hcomp
  have hdd : deriv (deriv (fun t => h (γ t))) 0 = realHessian h x v v := by
    rw [heq.deriv_eq, hdγ.deriv]
  have hmaxγ : IsLocalMax (fun t => h (γ t)) 0 := by
    filter_upwards [ht.eventually hmax] with t ht'
    simpa only [hγ0] using ht'
  have hcont : ContinuousAt (fun t => h (γ t)) 0 := by
    have hc : ContinuousAt h (γ 0) := by simpa only [hγ0] using hh.continuousAt
    exact hc.comp (hγ 0).continuousAt
  exact hdd ▸ PoincareMT.LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax hmaxγ hcont

/-- Interleaved real coordinates realize every complex vector. -/
theorem complexCoord_surjective {n : ℕ} : Function.Surjective (complexCoord (n := n)) := by
  intro z
  refine ⟨∑ i : Fin n, ((z i).re • realDirection i + (z i).im • imagDirection i), ?_⟩
  funext j
  change complexCoordCLM j _ = z j
  simp only [map_sum, map_add, map_smul, complexCoordCLM_apply]
  simp only [complexCoord_realDirection, complexCoord_imagDirection]
  simp [Finset.sum_add_distrib, mul_comm]
  apply Complex.ext <;> simp

/-- Nonpositivity of the actual complex Hessian quadratic form, with the
coordinate order used throughout the manuscript. -/
theorem complexHessian_quadratic_nonpos_of_isLocalMax {n : ℕ} {h : E n → ℝ}
    {x : E n} (hh : ContDiffAt ℝ ∞ h x) (hmax : IsLocalMax h x) (z : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n,
      complexHessian h x i j * z i * star (z j)).re ≤ 0 := by
  obtain ⟨v, rfl⟩ := complexCoord_surjective z
  have hv := realHessian_nonpos_of_isLocalMax hh hmax v
  have hJv := realHessian_nonpos_of_isLocalMax hh hmax (J v)
  have hg : realMetricForm h x v v ≤ 0 := by
    rw [realMetricForm_eq_average_hessian hh]
    linarith
  change 2 * (∑ i : Fin n, ∑ j : Fin n,
    complexHessian h x i j * complexCoord v i * star (complexCoord v j)).re ≤ 0 at hg
  linarith

/-- A positive semidefinite matrix contracts a nonpositive complex quadratic
form to a nonpositive real trace. No simultaneous diagonalization is used. -/
theorem posSemidef_trace_mul_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : ∀ z : ι → ℂ, (∑ i : ι, ∑ j : ι, B i j * z i * star (z j)).re ≤ 0) :
    (A * B).trace.re ≤ 0 := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have htrace : (A * B).trace = (C * B * C.conjTranspose).trace := by
    rw [hC]
    change (C.conjTranspose * C * B).trace = _
    exact (Matrix.trace_mul_cycle C B C.conjTranspose).symm
  rw [htrace]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  apply Finset.sum_nonpos
  intro k _
  have heq : (C * B * C.conjTranspose) k k =
      ∑ i : ι, ∑ j : ι, B i j * C k i * star (C k j) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  exact hB (C k)

/-- Local maximum sign for the concrete complex Laplacian of any positive
complex Hessian. The differential operator is not assumed to have this sign. -/
theorem complexLaplacian_nonpos_of_isLocalMax {n : ℕ} {u h : E n → ℝ} {x : E n}
    (hu : (complexHessian u x).PosDef) (hh : ContDiffAt ℝ ∞ h x)
    (hmax : IsLocalMax h x) : complexLaplacian u h x ≤ 0 := by
  rw [complexLaplacian_eq_trace]
  exact posSemidef_trace_mul_nonpos hu.inv.posSemidef
    (complexHessian_quadratic_nonpos_of_isLocalMax hh hmax)

namespace ComplexMaximumAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma dz_const_mul_differentiableAt {f : X → ℂ} {x : X}
    (hf : DifferentiableAt ℝ f x) (c : ℂ) (a b : X) :
    dz a b (fun y => c * f y) x = c * dz a b f x := by
  unfold dz rd
  rw [fderiv_const_mul hf]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma dz_dz_const_mul_at {f : X → ℂ} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (r : ℂ) (a b c d : X) :
    dz a b (dz c d (fun y => r * f y)) x = r * dz a b (dz c d f) x := by
  have hf₁ : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  have hinner : dz c d (fun y => r * f y) =ᶠ[𝓝 x]
      (fun y => r * dz c d f y) := by
    filter_upwards [hf₁.eventually (by simp)] with y hy
    exact dz_const_mul_differentiableAt (hy.differentiableAt (by simp)) r c d
  rw [LogDetAux.dz_congr_of_eventuallyEq hinner]
  exact dz_const_mul_differentiableAt ((smoothAt_dz hf c d).differentiableAt (by simp)) r a b

end ComplexMaximumAux

@[simp] theorem complexHessian_const {n : ℕ} (c : ℝ) (x : E n) :
    complexHessian (fun _ : E n => c) x = 0 := by
  ext i j
  have hbar : dz (realDirection j) (-imagDirection j) (fun _ : E n => (c : ℂ)) =
      (fun _ : E n => (0 : ℂ)) := by
    funext y
    simp [dz, rd]
  change dz (realDirection i) (imagDirection i)
    (dz (realDirection j) (-imagDirection j) (fun _ : E n => (c : ℂ))) x = 0
  rw [hbar]
  simp [dz, rd]

@[simp] theorem complexLaplacian_const {n : ℕ} (u : E n → ℝ) (c : ℝ) (x : E n) :
    complexLaplacian u (fun _ : E n => c) x = 0 := by
  simp [complexLaplacian_eq_trace]

theorem complexHessian_const_mul_at {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (c : ℝ) :
    complexHessian (fun y => c * h y) x = (c : ℂ) • complexHessian h x := by
  have hc : ContDiffAt ℝ ∞ (fun y => (h y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hh
  ext i j
  change dz (realDirection i) (imagDirection i)
    (dz (realDirection j) (-imagDirection j) (fun y => ((c * h y : ℝ) : ℂ))) x =
      (c : ℂ) * dz (realDirection i) (imagDirection i)
        (dz (realDirection j) (-imagDirection j) (fun y => (h y : ℂ))) x
  simp only [Complex.ofReal_mul]
  exact ComplexMaximumAux.dz_dz_const_mul_at hc _ _ _ _ _

theorem complexLaplacian_const_mul_at {n : ℕ} (u : E n → ℝ) {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (c : ℝ) :
    complexLaplacian u (fun y => c * h y) x = c * complexLaplacian u h x := by
  rw [complexLaplacian_eq_trace, complexHessian_const_mul_at hh, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, complexLaplacian_eq_trace]

end KEBall
