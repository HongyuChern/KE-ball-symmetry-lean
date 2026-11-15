import KEBall.FiberEnergyParameter
import KEBall.ComplexMaximum

/-!
# The mixed entries of the fiber and disc complex Hessian
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace KEBall.MoserTrudinger

open KEBallProbe

/-- Real derivative in a disc direction, holding the fiber variable fixed. -/
noncomputable def discDirectionalDerivative {n : ℕ} (u : E n × E 1 → ℝ) (a : E 1)
    (p : E n × E 1) : ℝ := fderiv ℝ u p (0, a)

theorem discDirectionalDerivative_contDiff {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (a : E 1) : ContDiff ℝ ∞ (discDirectionalDerivative u a) :=
  (hu.fderiv_right (by simp)).clm_apply contDiff_const

private theorem dz_add_differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a b : E) :
    dz a b (fun y => f y + g y) x = dz a b f x + dz a b g x := by
  simp only [dz, rd, fderiv_fun_add hf hg, add_apply]
  ring

private theorem rd_ofReal_discDirectional {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (a : E 1) :
    rd (0, a) (fun p => (u p : ℂ)) = fun p => (discDirectionalDerivative u a p : ℂ) := by
  funext p
  have h := Complex.ofRealCLM.hasFDerivAt.comp p (hu.differentiable (by simp) p).hasFDerivAt
  change HasFDerivAt (fun q => (u q : ℂ)) _ p at h
  change fderiv ℝ (fun q => (u q : ℂ)) p (0, a) = _
  rw [h.fderiv]
  rfl

private theorem dz_discDirectional_eq {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (a : E 1) (z : E n) (w : E 1) (p q : E n) :
    dz (p, 0) (q, 0) (rd (0, a) (fun y => (u y : ℂ))) (z, w) =
      dz p q (fun x => (discDirectionalDerivative u a (x, w) : ℂ)) z := by
  rw [rd_ofReal_discDirectional hu a]
  let L := ContinuousLinearMap.inl ℝ (E n) (E 1)
  let f : E n × E 1 → ℂ := fun y => (discDirectionalDerivative u a y : ℂ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp (discDirectionalDerivative_contDiff hu a)
  have he (x : E n) : ((0, w) : E n × E 1) + L x = (x, w) := by simp [L]
  have h := congrFun (dz_comp_affine (hf.differentiable (by simp)) L (0, w) p q) z
  simp only [he] at h
  exact h.symm

/-- Mixed column of the complex Hessian with a fiber row and a disc column. -/
theorem productComplexHessian_fiber_disc {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : E n) (w : E 1) (i : Fin n) :
    productComplexHessian u z w (Sum.inl i) (Sum.inr 0) =
      (2 : ℂ)⁻¹ * (partialZ i (fun x => (discDirectionalDerivative u (realDirection 0) (x, w) : ℂ)) z +
        Complex.I * partialZ i (fun x => (discDirectionalDerivative u (imagDirection 0) (x, w) : ℂ)) z) := by
  let f : E n × E 1 → ℂ := fun y => (u y : ℂ)
  let a : E n × E 1 := (realDirection i, 0)
  let b : E n × E 1 := (imagDirection i, 0)
  let c : E n × E 1 := (0, realDirection 0)
  let d : E n × E 1 := (0, imagDirection 0)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hu
  have he : dz c (-d) f = fun y => (2 : ℂ)⁻¹ * (rd c f y + Complex.I * rd d f y) := by
    funext y
    simp only [dz, rd, map_neg]
    ring
  have hc : DifferentiableAt ℝ (rd c f) (z, w) :=
    (smoothAt_rd hf.contDiffAt c).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (rd d f) (z, w) :=
    (smoothAt_rd hf.contDiffAt d).differentiableAt (by simp)
  change dz a b (dz c (-d) f) (z, w) = _
  have hd' : DifferentiableAt ℝ (fun y => Complex.I * rd d f y) (z, w) :=
    hd.const_mul Complex.I
  have he' : DifferentiableAt ℝ (fun y => rd c f y + Complex.I * rd d f y) (z, w) :=
    hc.add hd'
  rw [he, ComplexMaximumAux.dz_const_mul_differentiableAt he' (2 : ℂ)⁻¹ a b,
    dz_add_differentiableAt hc hd' a b,
    ComplexMaximumAux.dz_const_mul_differentiableAt hd Complex.I a b]
  dsimp only [a, b, c, d, f]
  rw [dz_discDirectional_eq hu, dz_discDirectional_eq hu]
  rfl

/-- Mixed row of the complex Hessian with a disc row and a fiber column. -/
theorem productComplexHessian_disc_fiber {n : ℕ} {u : E n × E 1 → ℝ}
    (hu : ContDiff ℝ ∞ u) (z : E n) (w : E 1) (j : Fin n) :
    productComplexHessian u z w (Sum.inr 0) (Sum.inl j) =
      (2 : ℂ)⁻¹ * (partialBar j (fun x => (discDirectionalDerivative u (realDirection 0) (x, w) : ℂ)) z -
        Complex.I * partialBar j (fun x => (discDirectionalDerivative u (imagDirection 0) (x, w) : ℂ)) z) := by
  let f : E n × E 1 → ℂ := fun y => (u y : ℂ)
  let a : E n × E 1 := (realDirection j, 0)
  let b : E n × E 1 := (imagDirection j, 0)
  let c : E n × E 1 := (0, realDirection 0)
  let d : E n × E 1 := (0, imagDirection 0)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hu
  change (2 : ℂ)⁻¹ * (rd c (dz a (-b) f) (z, w) - Complex.I * rd d (dz a (-b) f) (z, w)) = _
  rw [rd_dz_comm hf, rd_dz_comm hf]
  dsimp only [a, b, c, d, f]
  have hb : -(imagDirection j, (0 : E 1)) = (-imagDirection j, 0) := by
    ext <;> simp
  rw [hb]
  rw [dz_discDirectional_eq hu, dz_discDirectional_eq hu]
  rfl

end KEBall.MoserTrudinger
