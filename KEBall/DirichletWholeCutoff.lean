import KEBall.DirichletWholeSobolev

/-! Multiplication by a smooth cutoff on the actual whole-space Sobolev graph. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient Topology

namespace KEBall

/-- Multiplication by an essentially bounded scalar field on ambient L². -/
noncomputable def euclideanL2ScalarMul {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : E n → ℝ}
    (hc : MemLp c ⊤ (volume0 n)) : EuclideanL2 n F →L[ℝ] EuclideanL2 n F :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).holderL (volume0 n) ⊤ 2 2 (hc.toLp c)

theorem euclideanL2ScalarMul_ae {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : E n → ℝ}
    (hc : MemLp c ⊤ (volume0 n)) (f : EuclideanL2 n F) :
    euclideanL2ScalarMul hc f =ᵐ[volume0 n] fun x => c x • f x := by
  refine ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).coeFn_holder (hc.toLp c) f).trans ?_
  filter_upwards [MemLp.coeFn_toLp hc] with x hx
  change (hc.toLp c) x • f x = c x • f x
  rw [hx]

/-- Multiplication of an L² scalar function by an essentially bounded vector field. -/
noncomputable def euclideanL2VectorMul {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : E n → F}
    (hc : MemLp c ⊤ (volume0 n)) : EuclideanL2 n ℝ →L[ℝ] EuclideanL2 n F :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip.holderL (volume0 n) ⊤ 2 2 (hc.toLp c)

theorem euclideanL2VectorMul_ae {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : E n → F}
    (hc : MemLp c ⊤ (volume0 n)) (f : EuclideanL2 n ℝ) :
    euclideanL2VectorMul hc f =ᵐ[volume0 n] fun x => f x • c x := by
  refine ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip.coeFn_holder (hc.toLp c) f).trans ?_
  filter_upwards [MemLp.coeFn_toLp hc] with x hx
  change f x • (hc.toLp c) x = f x • c x
  rw [hx]

theorem contDiff_euclideanGradient {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (∇ f) :=
  (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by simp))

theorem hasCompactSupport_euclideanGradient {n : ℕ} {f : E n → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (∇ f) := by
  apply hf.mono'
  intro x hx
  by_contra hx'
  apply hx
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, inner_zero_left, fderiv_of_notMem_tsupport ℝ hx', zero_apply]

private theorem cutoff_memLp {n : ℕ} (χ : 𝓓(dirichletBallOpens n, ℝ)) :
    MemLp (χ : E n → ℝ) ⊤ (volume0 n) :=
  χ.continuous.memLp_top_of_hasCompactSupport χ.hasCompactSupport _

private theorem cutoffGradient_memLp {n : ℕ} (χ : 𝓓(dirichletBallOpens n, ℝ)) :
    MemLp (∇ (χ : E n → ℝ)) ⊤ (volume0 n) :=
  (contDiff_euclideanGradient χ.contDiff).continuous.memLp_top_of_hasCompactSupport
    (hasCompactSupport_euclideanGradient χ.hasCompactSupport) _

private noncomputable def euclideanGraphCutoff {n : ℕ} (χ : 𝓓(dirichletBallOpens n, ℝ)) :
    EuclideanL2Pair n →L[ℝ] EuclideanL2Pair n :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((euclideanL2ScalarMul (cutoff_memLp χ)).comp (WithLp.fstL 2 ℝ _ _)).prod
      (((euclideanL2ScalarMul (cutoff_memLp χ)).comp (WithLp.sndL 2 ℝ _ _)) +
        (euclideanL2VectorMul (cutoffGradient_memLp χ)).comp (WithLp.fstL 2 ℝ _ _)))

private noncomputable def euclideanTestCutoff {n : ℕ} (χ : 𝓓(dirichletBallOpens n, ℝ))
    (φ : 𝓓((⊤ : Opens (E n)), ℝ)) : 𝓓((⊤ : Opens (E n)), ℝ) :=
  ⟨fun x => χ x * φ x, χ.contDiff.mul φ.contDiff, χ.hasCompactSupport.mul_right, subset_univ _⟩

theorem gradient_euclideanCutoff_mul {n : ℕ} {f g : E n → ℝ}
    {x : E n} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ∇ (fun y => f y * g y) x = f x • ∇ g x + g x • ∇ f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradient_left, inner_gradient_left, fderiv_fun_mul hf hg]
  rfl

private theorem euclideanGraphCutoff_test {n : ℕ} (χ : 𝓓(dirichletBallOpens n, ℝ))
    (φ : 𝓓((⊤ : Opens (E n)), ℝ)) :
    euclideanGraphCutoff χ (compactTestL2Graph (volume0 n) φ) =
      compactTestL2Graph (volume0 n) (euclideanTestCutoff χ φ) := by
  let ψ := euclideanTestCutoff χ φ
  let μ := volume0 n
  let f := compactTestToL2 μ φ
  let G := compactTestGradientToL2 μ φ
  let V := euclideanL2ScalarMul (cutoff_memLp χ) G
  let W := euclideanL2VectorMul (cutoffGradient_memLp χ) f
  apply (WithLp.equiv 2 (EuclideanL2 n ℝ × EuclideanL2 n (E n))).injective
  apply Prod.ext
  · change euclideanL2ScalarMul (cutoff_memLp χ) f = compactTestToL2 μ ψ
    apply Lp.ext
    filter_upwards [euclideanL2ScalarMul_ae (cutoff_memLp χ) f, compactTestToL2_ae μ φ,
      compactTestToL2_ae μ ψ] with x hx hf hψ
    rw [hx, hψ]
    change χ x • f x = χ x * φ x
    change f x = φ x at hf
    rw [hf]
    rfl
  · change V + W = compactTestGradientToL2 μ ψ
    apply Lp.ext
    filter_upwards [Lp.coeFn_add V W, euclideanL2ScalarMul_ae (cutoff_memLp χ) G,
      euclideanL2VectorMul_ae (cutoffGradient_memLp χ) f, compactTestToL2_ae μ φ,
      compactTestGradientToL2_ae μ φ, compactTestGradientToL2_ae μ ψ] with x hSum hV hW hf hG hψ
    change V x = χ x • G x at hV
    change W x = f x • ∇ (χ : E n → ℝ) x at hW
    change f x = φ x at hf
    change G x = ∇ (φ : E n → ℝ) x at hG
    rw [hSum, hψ, Pi.add_apply, hV, hW, hf, hG]
    exact (gradient_euclideanCutoff_mul (χ.contDiff.differentiable (by simp) x)
      (φ.contDiff.differentiable (by simp) x)).symm

/-- A smooth cutoff acts on the whole-space Sobolev graph by the product rule. -/
noncomputable def euclideanSobolevCutoff {n : ℕ} (χ : 𝓓(dirichletBallOpens n, ℝ)) :
    EuclideanSobolev n →L[ℝ] EuclideanSobolev n := by
  let T := euclideanGraphCutoff χ
  let P := euclideanSobolevSubmodule n
  apply (T.comp P.subtypeL).codRestrict P
  intro u
  change T u.val ∈ P
  have hClosed : IsClosed (T ⁻¹' (P : Set (EuclideanL2Pair n))) :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hRange : ((compactTestL2Graph (volume0 n) (Ω := ⊤)).range : Set (EuclideanL2Pair n)) ⊆
      T ⁻¹' P := by
    rintro _ ⟨φ, rfl⟩
    change T (compactTestL2Graph (volume0 n) φ) ∈ P
    rw [show T (compactTestL2Graph (volume0 n) φ) = _ from euclideanGraphCutoff_test χ φ]
    exact subset_closure ⟨_, rfl⟩
  exact closure_minimal hRange hClosed u.property

theorem euclideanSobolevCutoff_value_ae {n : ℕ} (χ : 𝓓(dirichletBallOpens n, ℝ))
    (u : EuclideanSobolev n) :
    (euclideanSobolevCutoff χ u : EuclideanL2Pair n).fst =ᵐ[volume0 n]
      fun x => χ x * (u : EuclideanL2Pair n).fst x :=
  euclideanL2ScalarMul_ae (cutoff_memLp χ) (u : EuclideanL2Pair n).fst

theorem euclideanSobolevCutoff_gradient_ae {n : ℕ} (χ : 𝓓(dirichletBallOpens n, ℝ))
    (u : EuclideanSobolev n) :
    (euclideanSobolevCutoff χ u : EuclideanL2Pair n).snd =ᵐ[volume0 n]
      fun x => χ x • (u : EuclideanL2Pair n).snd x +
        (u : EuclideanL2Pair n).fst x • ∇ (χ : E n → ℝ) x := by
  exact (Lp.coeFn_add _ _).trans ((euclideanL2ScalarMul_ae (cutoff_memLp χ)
    (u : EuclideanL2Pair n).snd).add (euclideanL2VectorMul_ae (cutoffGradient_memLp χ)
      (u : EuclideanL2Pair n).fst))

end KEBall
