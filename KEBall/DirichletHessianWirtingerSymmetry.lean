import KEBall.DirichletPositiveTraceRatio
import KEBall.FiberEnergyGreen
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! The exact Kähler derivative identities needed for the logarithmic trace estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 200000
open Filter Matrix
open scoped ContDiff Matrix Matrix.Norms.Elementwise BigOperators ComplexOrder Topology
namespace KEBall
open KEBallProbe

theorem dirichlet_dz_star {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℂ) (a b x : V) :
    dz a (-b) (fun y => star (f y)) x=star (dz a b f x) := by
  simp only [dz,rd,fderiv_star,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    map_neg,starL'_apply,star_mul,star_sub,star_inv₀,star_ofNat]
  simp only [Complex.star_def,Complex.conj_I,map_inv,map_ofNat]
  ring

theorem complexHessian_trace_real_cast {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) :
    (((complexHessian u x).trace.re : ℝ) : ℂ)=(complexHessian u x).trace := by
  rw [(MoserTrudinger.complexHessian_isHermitian_of_smooth hu).trace_eq_sum_eigenvalues,
    ← RCLike.ofReal_sum]
  rfl

theorem partialZ_complexHessian_symm {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (i j k : Fin n) :
    partialZ k (fun y => complexHessian u y i j) x=
      partialZ i (fun y => complexHessian u y k j) x := by
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  exact dz_comm_at (smoothAt_dz hc (realDirection j) (-imagDirection j))
    (realDirection k) (imagDirection k) (realDirection i) (imagDirection i)

theorem partialBar_complexHessian_eq_star_partialZ {n : ℕ} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : E n) (i j k : Fin n) :
    partialBar k (fun y => complexHessian u y i j) x=
      star (partialZ k (fun y => complexHessian u y j i) x) := by
  have he : (fun y => complexHessian u y i j)=(fun y => star (complexHessian u y j i)) := by
    funext y
    have h := congrFun (congrFun (MoserTrudinger.complexHessian_isHermitian_of_smooth
      (hu.contDiffAt (x := y))).eq i) j
    exact h.symm
  rw [he]
  exact dirichlet_dz_star _ _ _ _

theorem partialZ_trace_complexHessian {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    partialZ i (fun y => (complexHessian u y).trace) x=
      ∑ k, partialZ k (fun y => complexHessian u y i k) x := by
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have hd (k : Fin n) : DifferentiableAt ℝ (fun y => complexHessian u y k k) x :=
    (smoothAt_dz (smoothAt_dz hc (realDirection k) (-imagDirection k))
      (realDirection k) (imagDirection k)).differentiableAt (by simp)
  change dz (realDirection i) (imagDirection i) (fun y => ∑ k, complexHessian u y k k) x= _
  rw [dz_sum_differentiableAt hd]
  apply Finset.sum_congr rfl
  intro k _
  exact partialZ_complexHessian_symm hu k k i

private theorem third_wirtinger_rotate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (a b c d e g : V) :
    dz a b (dz c d (dz e g f))=dz e g (dz a b (dz c d f)) := by
  have he : dz c d (dz e g f)=dz e g (dz c d f) :=
    funext fun y => dz_comm hf c d e g y
  rw [he]
  exact funext fun y => dz_comm (smooth_dz hf c d) a b e g y

private theorem fourth_wirtinger_pairs {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (a b c d e g h l : V) :
    dz a b (dz c d (dz e g (dz h l f)))=dz e g (dz h l (dz a b (dz c d f))) := by
  rw [third_wirtinger_rotate (smooth_dz hf h l) a b c d e g,
    third_wirtinger_rotate hf a b c d h l]

theorem complexHessian_trace_commutation {n : ℕ} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : E n) (i j : Fin n) :
    complexHessian (fun y => (complexHessian u y).trace.re) x i j=
      ∑ k, partialZ k (partialBar k (fun y => complexHessian u y i j)) x := by
  have hc : ContDiff ℝ ∞ (fun y => (u y : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have hG (a b : Fin n) : ContDiff ℝ ∞ (fun y => complexHessian u y a b) :=
    smooth_dz (smooth_dz hc (realDirection b) (-imagDirection b))
      (realDirection a) (imagDirection a)
  have hCast : (fun y => (((complexHessian u y).trace.re : ℝ) : ℂ))=
      (fun y => (complexHessian u y).trace) :=
    funext fun y => complexHessian_trace_real_cast hu.contDiffAt
  have hBar : partialBar j (fun y => (complexHessian u y).trace)=
      (fun y => ∑ k, partialBar j (fun z => complexHessian u z k k) y) := by
    funext y
    exact dz_sum_differentiableAt (fun k => (hG k k).differentiable (by simp) y) _ _
  change partialZ i (partialBar j (fun y => (((complexHessian u y).trace.re : ℝ) : ℂ))) x= _
  rw [hCast,hBar]
  change dz (realDirection i) (imagDirection i)
    (fun y => ∑ k, partialBar j (fun z => complexHessian u z k k) y) x= _
  rw [dz_sum_differentiableAt
    (f := fun k y => partialBar j (fun z => complexHessian u z k k) y) (fun k =>
    (smooth_dz (hG k k) (realDirection j) (-imagDirection j)).differentiable (by simp) x)]
  apply Finset.sum_congr rfl
  intro k _
  exact congrFun (fourth_wirtinger_pairs hc (realDirection i) (imagDirection i)
    (realDirection j) (-imagDirection j) (realDirection k) (imagDirection k)
    (realDirection k) (-imagDirection k)) x

end KEBall
