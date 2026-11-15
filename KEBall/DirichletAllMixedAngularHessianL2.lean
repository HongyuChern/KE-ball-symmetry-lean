import KEBall.DirichletLiePowerSpan
import KEBall.DirichletAngularLieRepresentation

/-! All finite ordered unitary angular words of the actual C2 solution have L2 Hessians. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 3
open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology
namespace KEBall

noncomputable def dirichletInteriorHessianL2Space (n : ℕ) :
    Submodule ℝ (dirichletInteriorSmoothSpace n) where
  carrier := {u | MemLp (realHessian u.val) 2 ((volume0 n).restrict (unitBall n))}
  zero_mem' := by
    change MemLp (realHessian (0 : E n → ℝ)) 2 _
    have hz : realHessian (0 : E n → ℝ) = (0 : E n → E n →L[ℝ] E n →L[ℝ] ℝ) := by
      funext x
      simp only [realHessian, fderiv_zero]
    rw [hz]
    exact MemLp.zero
  add_mem' := by
    intro u v hu hv
    change MemLp (realHessian (u.val+v.val)) 2 _
    refine MemLp.ae_eq ?_ (hu.add hv)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact (dirichlet_realHessian_add_C2
      ((u.property.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      ((v.property.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).symm
  smul_mem' := by
    intro c u hu
    change MemLp (realHessian (c • u.val)) 2 _
    refine MemLp.ae_eq ?_ (hu.const_smul c)
    filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
    exact (dirichlet_realHessian_smul_C2
      ((u.property.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) c).symm

theorem dirichletAngularEnd_prod_eq_word_on_ball {n m : ℕ}
    (R : Fin m → DirichletUnitaryField n) (u : dirichletInteriorSmoothSpace n) :
    EqOn (((List.ofFn (fun i => dirichletAngularEnd (R i).val)).prod) u).val
      (dirichletAngularWord R u.val) (unitBall n) := by
  induction m with
  | zero => intro x hx; rfl
  | succ m ih =>
    intro x hx
    rw [List.ofFn_succ, List.prod_cons]
    change dirichletCutAngular (R 0).val
      (((List.ofFn (fun i => dirichletAngularEnd ((Fin.tail R) i).val)).prod) u).val x =
      dirichletAngularDerivative (R 0).val (dirichletAngularWord (Fin.tail R) u.val) x
    rw [dirichletCutAngular_eq_on_ball _ _ hx, dirichletAngularDerivative_eq_fderiv_on_ball _ _ hx]
    have he : (((List.ofFn (fun i => dirichletAngularEnd ((Fin.tail R) i).val)).prod) u).val
        =ᶠ[𝓝 x] dirichletAngularWord (Fin.tail R) u.val := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact ih (Fin.tail R) hy
    rw [he.fderiv_eq]

theorem memLp_withinHessian_angularWord_of_C2_solution {n : ℕ}
    (hn : 0 < n) {u f : E n → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedUnitBall n)) (huS : ContDiffOn ℝ ∞ u (unitBall n))
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (hPos : ∀ x ∈ closedUnitBall n, (dirichletWithinComplexHessian u x).PosDef)
    (hf : SmoothNear (closedUnitBall n) f)
    (hEq : ∀ x ∈ unitBall n, (complexHessian u x).det.re = f x)
    {m : ℕ} (R : Fin m → DirichletUnitaryField n) :
    MemLp (dirichletWithinRealHessian (dirichletAngularWord R u))
      2 ((volume0 n).restrict (unitBall n)) := by
  let v : dirichletInteriorSmoothSpace n := ⟨u, huS⟩
  let ev : Module.End ℝ (dirichletInteriorSmoothSpace n) →ₗ[ℝ] dirichletInteriorSmoothSpace n :=
    { toFun := fun A => A v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let P := (dirichletInteriorHessianL2Space n).comap ev
  have hPure : dirichletLiePowerSpan (dirichletSkewAngularLieSpace n) m ≤ P := by
    apply Submodule.span_le.mpr
    rintro A ⟨Q, hQ, k, _, rfl⟩
    rcases Submodule.mem_map.mp hQ with ⟨S, hS, rfl⟩
    change MemLp (realHessian ((dirichletAngularEnd S ^ k) v).val) 2 _
    have h := memLp_realHessian_iteratedAngularDerivative_of_C2_solution
      hn hu huS hu0 hPos hf hEq S hS k
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
  change MemLp (realHessian (w.prod v).val) 2 ((volume0 n).restrict (unitBall n)) at hMem
  refine MemLp.ae_eq ?_ hMem
  filter_upwards [ae_restrict_mem (μ := volume0 n) measurableSet_ball] with x hx
  rw [dirichletWithinRealHessian_eq_on_ball _ hx]
  have he : (w.prod v).val =ᶠ[𝓝 x] dirichletAngularWord R u := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact dirichletAngularEnd_prod_eq_word_on_ball R v hy
  exact he.fderiv.fderiv_eq

theorem exists_dirichlet_closedBall_limit_with_all_mixed_angular_hessian_L2
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
      ∀ (m : ℕ) (R : Fin m → DirichletUnitaryField n),
        MemLp (dirichletWithinRealHessian (dirichletAngularWord R w))
          2 ((volume0 n).restrict (unitBall n)) := by
  obtain ⟨w, hUw, hw, hwS, hw0, hP, hD, _⟩ :=
    exists_dirichlet_closedBall_limit_with_all_pure_angular_hessian_L2 hn hg ht hT hu hu0 huP hEq
  refine ⟨w, hUw, hw, hwS, hw0, hP, hD, ?_⟩
  intro m R
  have hf : SmoothNear (closedUnitBall n) (fun x => Real.exp (t₀*g x)) := by
    obtain ⟨U, hU, hSub, hgU⟩ := hg
    exact ⟨U, hU, hSub, (contDiffOn_const.mul hgU).exp⟩
  exact memLp_withinHessian_angularWord_of_C2_solution (by omega) hw hwS hw0 hP hf hD R

end KEBall
