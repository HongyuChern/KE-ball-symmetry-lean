import KEBall.DirichletHigherAngularHessianL2
import KEBall.DirichletMixedAngularPotentialL2

/-! The actual interior angular fields as a Lie-closed space of linear operators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 3
open Filter Metric Set
open scoped ContDiff Topology
namespace KEBall

noncomputable def dirichletInteriorSmoothSpace (n : ℕ) : Submodule ℝ (E n → ℝ) where
  carrier := {u | ContDiffOn ℝ ∞ u (unitBall n)}
  zero_mem' := contDiffOn_const
  add_mem' := fun hu hv => hu.add hv
  smul_mem' := fun c _ hu => hu.const_smul c

noncomputable def dirichletCutAngular {n : ℕ} (S : E n →L[ℝ] E n)
    (u : E n → ℝ) (x : E n) : ℝ := by
  classical
  exact if x ∈ unitBall n then fderiv ℝ u x (S x) else 0

theorem dirichletCutAngular_eq_on_ball {n : ℕ} (S : E n →L[ℝ] E n)
    (u : E n → ℝ) {x : E n} (hx : x ∈ unitBall n) :
    dirichletCutAngular S u x = fderiv ℝ u x (S x) := by
  simp only [dirichletCutAngular, if_pos hx]

theorem contDiffOn_dirichletCutAngular {n : ℕ} {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (unitBall n)) (S : E n →L[ℝ] E n) :
    ContDiffOn ℝ ∞ (dirichletCutAngular S u) (unitBall n) := by
  apply ((hu.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).clm_apply
    S.contDiff.contDiffOn).congr
  intro x hx
  exact dirichletCutAngular_eq_on_ball S u hx

noncomputable def dirichletAngularEnd {n : ℕ} (S : E n →L[ℝ] E n) :
    Module.End ℝ (dirichletInteriorSmoothSpace n) where
  toFun u := ⟨dirichletCutAngular S u.val, contDiffOn_dirichletCutAngular u.property S⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    change dirichletCutAngular S (u.val+v.val) x =
      dirichletCutAngular S u.val x + dirichletCutAngular S v.val x
    by_cases hx : x ∈ unitBall n
    · simp only [dirichletCutAngular_eq_on_ball _ _ hx]
      rw [fderiv_add ((u.property.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
        ((v.property.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))]
      rfl
    · simp only [dirichletCutAngular, if_neg hx, add_zero]
  map_smul' c u := by
    apply Subtype.ext
    funext x
    change dirichletCutAngular S (c • u.val) x = c • dirichletCutAngular S u.val x
    by_cases hx : x ∈ unitBall n
    · simp only [dirichletCutAngular_eq_on_ball _ _ hx]
      rw [fderiv_const_smul ((u.property.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)) c]
      rfl
    · simp only [dirichletCutAngular, if_neg hx, smul_zero]

noncomputable def dirichletAngularRepresentation (n : ℕ) :
    (E n →L[ℝ] E n) →ₗ[ℝ] Module.End ℝ (dirichletInteriorSmoothSpace n) where
  toFun := dirichletAngularEnd
  map_add' S T := by
    ext u x
    change dirichletCutAngular (S+T) u.val x =
      dirichletCutAngular S u.val x + dirichletCutAngular T u.val x
    by_cases hx : x ∈ unitBall n
    · simp [dirichletCutAngular, hx]
    · simp [dirichletCutAngular, hx]
  map_smul' c S := by
    ext u x
    change dirichletCutAngular (c • S) u.val x = c • dirichletCutAngular S u.val x
    by_cases hx : x ∈ unitBall n
    · simp [dirichletCutAngular, hx]
    · simp [dirichletCutAngular, hx]

theorem dirichletAngularEnd_commutator {n : ℕ} (S T : E n →L[ℝ] E n) :
    dirichletAngularEnd S * dirichletAngularEnd T -
      dirichletAngularEnd T * dirichletAngularEnd S = dirichletAngularEnd (T*S-S*T) := by
  ext u x
  change dirichletCutAngular S (dirichletCutAngular T u.val) x -
    dirichletCutAngular T (dirichletCutAngular S u.val) x = dirichletCutAngular (T*S-S*T) u.val x
  by_cases hx : x ∈ unitBall n
  · have he (Q : E n →L[ℝ] E n) : dirichletCutAngular Q u.val =ᶠ[𝓝 x]
        (fun y => fderiv ℝ u.val y (Q y)) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact dirichletCutAngular_eq_on_ball Q u.val hy
    rw [dirichletCutAngular_eq_on_ball _ _ hx, dirichletCutAngular_eq_on_ball _ _ hx,
      dirichletCutAngular_eq_on_ball _ _ hx, (he T).fderiv_eq, (he S).fderiv_eq]
    have hu := u.property.contDiffAt (isOpen_ball.mem_nhds hx)
    rw [dirichlet_fderiv_linearFieldDerivative hu T, dirichlet_fderiv_linearFieldDerivative hu S,
      realHessian_symm hu (T x) (S x)]
    simp only [_root_.sub_apply, ContinuousLinearMap.mul_apply, map_sub]
    ring
  · simp only [dirichletCutAngular, if_neg hx, sub_zero]

noncomputable def dirichletSkewAngularLieSpace (n : ℕ) :
    Submodule ℝ (Module.End ℝ (dirichletInteriorSmoothSpace n)) :=
  (skewAdjoint.submodule ℝ (E n →L[ℝ] E n)).map (dirichletAngularRepresentation n)

theorem dirichletAngularEnd_mem_skewLieSpace {n : ℕ} (S : E n →L[ℝ] E n)
    (hS : star S = -S) : dirichletAngularEnd S ∈ dirichletSkewAngularLieSpace n :=
  Submodule.mem_map.mpr ⟨S, hS, rfl⟩

theorem dirichletSkewAngularLieSpace_commutator {n : ℕ}
    (A : Module.End ℝ (dirichletInteriorSmoothSpace n)) (hA : A ∈ dirichletSkewAngularLieSpace n)
    (B : Module.End ℝ (dirichletInteriorSmoothSpace n)) (hB : B ∈ dirichletSkewAngularLieSpace n) :
    A*B-B*A ∈ dirichletSkewAngularLieSpace n := by
  rcases Submodule.mem_map.mp hA with ⟨S, hS, rfl⟩
  rcases Submodule.mem_map.mp hB with ⟨T, hT, rfl⟩
  change dirichletAngularEnd S * dirichletAngularEnd T -
    dirichletAngularEnd T * dirichletAngularEnd S ∈ _
  rw [dirichletAngularEnd_commutator]
  apply dirichletAngularEnd_mem_skewLieSpace
  change star S = -S at hS
  change star T = -T at hT
  change S.adjoint = -S at hS
  change T.adjoint = -T at hT
  change (T.comp S - S.comp T).adjoint = -(T.comp S - S.comp T)
  rw [map_sub, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hS, hT]
  simp only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, neg_neg]
  abel

theorem dirichletAngularEnd_pow_eq_on_ball {n : ℕ} (S : E n →L[ℝ] E n)
    (u : dirichletInteriorSmoothSpace n) (k : ℕ) :
    EqOn ((dirichletAngularEnd S ^ k) u).val (dirichletInteriorAngularIterate S u.val k) (unitBall n) := by
  induction k with
  | zero => intro x hx; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ']
    change dirichletCutAngular S ((dirichletAngularEnd S ^ k) u).val x =
      fderiv ℝ (dirichletInteriorAngularIterate S u.val k) x (S x)
    rw [dirichletCutAngular_eq_on_ball _ _ hx]
    have he : ((dirichletAngularEnd S ^ k) u).val =ᶠ[𝓝 x]
        dirichletInteriorAngularIterate S u.val k := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact ih hy
    rw [he.fderiv_eq]

end KEBall
