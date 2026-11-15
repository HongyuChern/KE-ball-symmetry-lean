import KEBall.DirichletHigherAngularHessianLp
import KEBall.DirichletLiePowerSpan
import KEBall.DirichletAllMixedAngularHessianL2

/-! Every finite ordered unitary angular word has actual Hessian in every finite Lp. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 3
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff ENNReal Topology
namespace KEBall

noncomputable def dirichletInteriorHessianLpSpace (n : ℕ) (p : ℝ≥0∞) :
    Submodule ℝ (dirichletInteriorSmoothSpace n) where
  carrier := {u | MemLp (realHessian u.val) p ((volume0 n).restrict (unitBall n))}
  zero_mem' := by
    change MemLp (realHessian (0 : E n → ℝ)) p _
    have hz : realHessian (0 : E n → ℝ) = (0 : E n → E n →L[ℝ] E n →L[ℝ] ℝ) := by
      funext x
      simp only [realHessian, fderiv_zero]
    rw [hz]
    exact MemLp.zero
  add_mem' := by
    intro u v hu hv
    change MemLp (realHessian (u.val+v.val)) p _
    refine MemLp.ae_eq ?_ (hu.add hv)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact (dirichlet_realHessian_add_C2
      ((u.property.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      ((v.property.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).symm
  smul_mem' := by
    intro c u hu
    change MemLp (realHessian (c • u.val)) p _
    refine MemLp.ae_eq ?_ (hu.const_smul c)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact (dirichlet_realHessian_smul_C2
      ((u.property.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) c).symm

theorem memLp_withinHessian_angularWord_of_C2_solution_finite {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (dirichletWithinRealHessian (dirichletAngularWord R u))
      p ((volume0 n).restrict (unitBall n)) := by
  let v : dirichletInteriorSmoothSpace n := ⟨u, huS⟩
  let ev : Module.End ℝ (dirichletInteriorSmoothSpace n) →ₗ[ℝ] dirichletInteriorSmoothSpace n :=
    { toFun := fun A => A v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let P := (dirichletInteriorHessianLpSpace n p).comap ev
  have hPure : dirichletLiePowerSpan (dirichletSkewAngularLieSpace n) m ≤ P := by
    apply Submodule.span_le.mpr
    rintro A ⟨Q, hQ, k, _, rfl⟩
    rcases Submodule.mem_map.mp hQ with ⟨S, hS, rfl⟩
    change MemLp (realHessian ((dirichletAngularEnd S ^ k) v).val) p _
    have h := memLp_realHessian_iteratedAngularDerivative_of_C2_solution_finite
      hn hu huS hu0 hPos hf hEq S hS k p hp
    refine MemLp.ae_eq ?_ h
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    have he : ((dirichletAngularEnd S ^ k) v).val =ᶠ[𝓝 x]
        dirichletInteriorAngularIterate S u k := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact dirichletAngularEnd_pow_eq_on_ball S v k hy
    exact he.fderiv.fderiv_eq.symm
  let w := List.ofFn (fun i => dirichletAngularEnd (R i).val)
  have hw : ∀ A ∈ w, A ∈ dirichletSkewAngularLieSpace n := by
    intro A hA
    rcases List.mem_ofFn.mp hA with ⟨i, rfl⟩
    exact dirichletAngularEnd_mem_skewLieSpace (R i).val (R i).property.1
  have hword := dirichlet_lie_word_mem_span_powers (dirichletSkewAngularLieSpace n)
    (fun A hA B hB => dirichletSkewAngularLieSpace_commutator A hA B hB) w hw
  have hl : w.length = m := List.length_ofFn
  rw [hl] at hword
  have hMem := hPure hword
  change MemLp (realHessian (w.prod v).val) p ((volume0 n).restrict (unitBall n)) at hMem
  refine MemLp.ae_eq ?_ hMem
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  rw [dirichletWithinRealHessian_eq_on_ball _ hx]
  have he : (w.prod v).val =ᶠ[𝓝 x] dirichletAngularWord R u := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact dirichletAngularEnd_prod_eq_word_on_ball R v hy
  exact he.fderiv.fderiv_eq

theorem exists_dirichlet_closedBall_limit_with_all_mixed_angular_hessian_finite_Lp
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
      ∀ (p : ℝ≥0∞), p ≠ ⊤ → ∀ (m : ℕ) (R : Fin m → DirichletUnitaryField n),
        MemLp (dirichletWithinRealHessian (dirichletAngularWord R w))
          p ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨w, hUw, hw, hwS, hw0, hP, hD, _⟩ :=
    exists_dirichlet_closedBall_limit_with_all_pure_angular_hessian_L2 hn hg ht hT hu hu0 huP hEq
  refine ⟨w, hUw, hw, hwS, hw0, hP, hD, ?_⟩
  intro p hp m R
  have hf : SmoothNear (closedUnitBall n) (fun x => Real.exp (t₀*g x)) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  exact memLp_withinHessian_angularWord_of_C2_solution_finite (by omega) hw hwS hw0 hP hf hD R p hp

end KEBall
