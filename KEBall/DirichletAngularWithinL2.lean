import KEBall.DirichletMixedAngularPotentialL2
import KEBall.DirichletLogDensitySecondDiscreteHessian

/-!
# The existing within-angular operator and the same actual path limit
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter Matrix MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

theorem dirichletAngularDerivative_eq_fderiv_on_ball {n : ℕ}
    (S : E n →L[ℝ] E n) (u : E n → ℝ) {x : E n} (hx : x ∈ unitBall n) :
    dirichletAngularDerivative S u x = fderiv ℝ u x (S x) := by
  unfold dirichletAngularDerivative
  have hN : closedUnitBall n ∈ 𝓝 x :=
    mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
  exact congrArg (fun L : E n →L[ℝ] ℝ => L (S x))
    (fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := u) hN)

theorem dirichletAngularDerivative_twice_eq_on_ball {n : ℕ}
    (S T : E n →L[ℝ] E n) (u : E n → ℝ) {x : E n} (hx : x ∈ unitBall n) :
    dirichletAngularDerivative S (dirichletAngularDerivative T u) x =
      fderiv ℝ (fun y => fderiv ℝ u y (T y)) x (S x) := by
  rw [dirichletAngularDerivative_eq_fderiv_on_ball S _ hx]
  have he : dirichletAngularDerivative T u =ᶠ[𝓝 x] (fun y => fderiv ℝ u y (T y)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact dirichletAngularDerivative_eq_fderiv_on_ball T u hy
  rw [he.fderiv_eq]

theorem memLp_withinHessian_mixedAngularDerivative_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n))
    (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    (S T : E n →L[ℝ] E n) (hS : star S = -S) (hT : star T = -T)
    (hSJ : ∀ x, S (J x) = J (S x)) (hTJ : ∀ x, T (J x) = J (T x)) :
    MemLp (dirichletWithinRealHessian (dirichletAngularDerivative S (dirichletAngularDerivative T u)))
      2 ((volume0 n).restrict (unitBall n)) := by
  have h := memLp_realHessian_mixedAngularDerivative_of_C2_solution
    hn hu huS hu0 hPos hf hEq S T hS hT hSJ hTJ
  refine MemLp.ae_eq ?_ h
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  rw [dirichletWithinRealHessian_eq_on_ball _ hx]
  have he : dirichletAngularDerivative S (dirichletAngularDerivative T u) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fun z => fderiv ℝ u z (T z)) y (S y)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact dirichletAngularDerivative_twice_eq_on_ball S T u hy
  exact he.fderiv.fderiv_eq.symm

theorem exists_dirichlet_closedBall_limit_with_mixed_angular_hessian_L2
    {n : ℕ} (hn : 2 ≤ n)
    {g : E n → ℝ} (hg : SmoothNear (closedUnitBall n) g)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : ∀ m, t m ∈ Icc (0 : ℝ) 1)
    (hT : Tendsto t atTop (𝓝 t₀))
    {u : ℕ → E n → ℝ} (hu : ∀ m, SmoothNear (closedUnitBall n) (u m))
    (hu0 : ∀ m x, x ∈ unitSphere n → u m x = 0)
    (huP : ∀ m x, x ∈ unitBall n → (complexHessian (u m) x).PosDef)
    (hEq : ∀ m x, x ∈ unitBall n →
      (complexHessian (u m) x).det.re = Real.exp (t m * g x)) :
    ∃ w : E n → ℝ,
      TendstoUniformlyOn u w atTop (closedUnitBall n) ∧
      ContDiffOn ℝ 2 w (closedUnitBall n) ∧ ContDiffOn ℝ ∞ w (unitBall n) ∧
      (∀ x ∈ unitSphere n, w x = 0) ∧
      (∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian w x).PosDef) ∧
      (∀ x ∈ unitBall n, (complexHessian w x).det.re = Real.exp (t₀ * g x)) ∧
      ∀ S T : E n →L[ℝ] E n, star S = -S → star T = -T →
        (∀ x, S (J x) = J (S x)) → (∀ x, T (J x) = J (T x)) →
          MemLp (dirichletWithinRealHessian
            (dirichletAngularDerivative S (dirichletAngularDerivative T w)))
            2 ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨w, hUw, hw, hwS, hw0, hP, hD, hDiscrete⟩ :=
    exists_dirichlet_closedBall_limit_with_uniform_second_discrete_hessian hn hg ht hT hu hu0 huP hEq
  refine ⟨w, hUw, hw, hwS, hw0, hP, hD, ?_⟩
  intro S T hS hT hSJ hTJ
  have hf : SmoothNear (closedUnitBall n) (fun x => Real.exp (t₀ * g x)) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  exact memLp_withinHessian_mixedAngularDerivative_of_C2_solution
    (by omega : 0 < n) hw hwS hw0 hP hf hD S T hS hT hSJ hTJ

end KEBall
