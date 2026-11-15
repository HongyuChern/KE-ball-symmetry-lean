import Drafts.KEBall.ComplexProductLog
import Drafts.KEBall.ConnectionCoordinates

/-!
Stage09 SOURCE_DRAFT_UNCOMPILED.
Conjugation and real-part identities for the actual real Frechet derivative.
All equalities used under a second derivative are neighbourhood equalities.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators

namespace KEBall
open KEBallProbe

namespace WirtingerConjugation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem smoothAt_star {f : X → ℂ} {x : X} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (fun y => star (f y)) x := by
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp x hf

theorem rd_star {f : X → ℂ} {x : X} (hf : DifferentiableAt ℝ f x) (v : X) :
    rd v (fun y => star (f y)) x = star (rd v f x) := by
  have hd := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hf.hasFDerivAt
  change HasFDerivAt (fun y => star (f y)) _ x at hd
  rw [rd, hd.fderiv]
  rfl

theorem dz_star {f : X → ℂ} {x : X} (hf : DifferentiableAt ℝ f x) (a b : X) :
    dz a b (fun y => star (f y)) x = star (dz a (-b) f x) := by
  unfold dz
  rw [rd_star hf, rd_star hf]
  simp [rd, map_neg]
  <;> ring

theorem dz_dz_add {f h : X → ℂ} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hh : ContDiffAt ℝ ∞ h x) (a b c d : X) :
    dz a b (dz c d (fun y => f y + h y)) x =
      dz a b (dz c d f) x + dz a b (dz c d h) x := by
  have heq : dz c d (fun y => f y + h y) =ᶠ[𝓝 x]
      (fun y => dz c d f y + dz c d h y) := by
    filter_upwards [(hf.of_le (m := 1) (by simp)).eventually (by simp),
      (hh.of_le (m := 1) (by simp)).eventually (by simp)] with y hyf hyh
    exact ComplexProductLogAux.dz_add_differentiableAt
      (hyf.differentiableAt (by simp)) (hyh.differentiableAt (by simp)) c d
  rw [LogDetAux.dz_congr_of_eventuallyEq heq]
  exact ComplexProductLogAux.dz_add_differentiableAt
    ((smoothAt_dz hf c d).differentiableAt (by simp))
    ((smoothAt_dz hh c d).differentiableAt (by simp)) a b

end WirtingerConjugation

theorem partialZ_star {n : ℕ} {f : E n → ℂ} {x : E n}
    (hf : DifferentiableAt ℝ f x) (i : Fin n) :
    partialZ i (fun y => star (f y)) x = star (partialBar i f x) :=
  WirtingerConjugation.dz_star hf _ _

theorem partialBar_star {n : ℕ} {f : E n → ℂ} {x : E n}
    (hf : DifferentiableAt ℝ f x) (i : Fin n) :
    partialBar i (fun y => star (f y)) x = star (partialZ i f x) := by
  simpa only [partialBar, partialZ, neg_neg] using
    WirtingerConjugation.dz_star hf (realDirection i) (-imagDirection i)

theorem partialBar_partialBar_ofReal {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ ∞ h x) (i j : Fin n) :
    partialBar i (partialBar j (fun y => (h y : ℂ))) x =
      star (partialZ i (partialZ j (fun y => (h y : ℂ))) x) := by
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hh
  have heq : partialBar j (fun y => (h y : ℂ)) =ᶠ[𝓝 x]
      (fun y => star (partialZ j (fun z => (h z : ℂ)) y)) := by
    filter_upwards [(hh.of_le (m := 1) (by simp)).eventually (by simp)] with y hy
    exact partialBar_ofReal (hy.differentiableAt (by simp)) j
  rw [partialBar_congr_nhds heq]
  exact partialBar_star ((smoothAt_dz hc _ _).differentiableAt (by simp)) i

/-- Cauchy--Riemann equations are used on an open set before differentiating. -/
theorem partialZ_partialBar_eq_zero_of_CR {n : ℕ} {f : E n → ℂ}
    {U : Set (E n)} (hU : IsOpen U)
    (hCR : ∀ y ∈ U, ∀ j : Fin n, partialBar j f y = 0)
    {x : E n} (hx : x ∈ U) (i j : Fin n) :
    partialZ i (partialBar j f) x = 0 := by
  have heq : partialBar j f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hCR y hy j
  rw [partialZ_congr_nhds heq]
  simp [partialZ, dz, rd]

theorem partialZ_partialBar_star_eq_zero_of_CR {n : ℕ} {f : E n → ℂ}
    {U : Set (E n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hCR : ∀ y ∈ U, ∀ j : Fin n, partialBar j f y = 0)
    {x : E n} (hx : x ∈ U) (i j : Fin n) :
    partialZ i (partialBar j (fun y => star (f y))) x = 0 := by
  have hfAt := hf.contDiffAt (hU.mem_nhds hx)
  have hstar := WirtingerConjugation.smoothAt_star hfAt
  have hz : partialZ i (fun y => star (f y)) =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [partialZ_star ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)),
      hCR y hy i, star_zero]
  calc
    _ = partialBar j (partialZ i (fun y => star (f y))) x :=
      dz_comm_at hstar _ _ _ _
    _ = 0 := by
      rw [partialBar_congr_nhds hz]
      simp [partialBar, dz, rd]

/-- The real part has zero actual complex Hessian; this is derived from CR. -/
theorem complexHessian_re_eq_zero_of_CR {n : ℕ} {f : E n → ℂ}
    {U : Set (E n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hCR : ∀ y ∈ U, ∀ j : Fin n, partialBar j f y = 0)
    {x : E n} (hx : x ∈ U) : complexHessian (fun y => (f y).re) x = 0 := by
  have hfAt := hf.contDiffAt (hU.mem_nhds hx)
  have hs := WirtingerConjugation.smoothAt_star hfAt
  have heq : (fun y => ((f y).re : ℂ)) =
      (fun y => (2 : ℂ)⁻¹ * (f y + star (f y))) := by
    funext y
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  ext i j
  change partialZ i (partialBar j (fun y => ((f y).re : ℂ))) x = 0
  rw [heq]
  change dz (realDirection i) (imagDirection i)
    (dz (realDirection j) (-imagDirection j) _) x = 0
  rw [ComplexMaximumAux.dz_dz_const_mul_at (hfAt.add hs),
    WirtingerConjugation.dz_dz_add hfAt hs]
  change (2 : ℂ)⁻¹ * (partialZ i (partialBar j f) x +
    partialZ i (partialBar j (fun y => star (f y))) x) = 0
  rw [partialZ_partialBar_eq_zero_of_CR hU hCR hx,
    partialZ_partialBar_star_eq_zero_of_CR hU hf hCR hx]
  ring

theorem complexHessian_im_eq_zero_of_CR {n : ℕ} {f : E n → ℂ}
    {U : Set (E n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hCR : ∀ y ∈ U, ∀ j : Fin n, partialBar j f y = 0)
    {x : E n} (hx : x ∈ U) : complexHessian (fun y => (f y).im) x = 0 := by
  let g : E n → ℂ := fun y => -Complex.I * f y
  have hg : ContDiffOn ℝ ∞ g U := contDiffOn_const.mul hf
  have hgCR : ∀ y ∈ U, ∀ j : Fin n, partialBar j g y = 0 := by
    intro y hy j
    change dz (realDirection j) (-imagDirection j) (fun z => -Complex.I * f z) y = 0
    rw [ComplexMaximumAux.dz_const_mul_differentiableAt
      ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))]
    change -Complex.I * partialBar j f y = 0
    rw [hCR y hy j]
    ring
  simpa [g, Complex.mul_re] using complexHessian_re_eq_zero_of_CR hU hg hgCR hx

end KEBall
