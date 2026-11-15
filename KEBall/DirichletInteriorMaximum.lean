import KEBall.ComplexMaximum
import KEBall.DirichletBilinearContraction
import PshLines.LeviForm

/-!
# Local comparison with only interior second derivatives

The comparison theorem applies on arbitrary compact sets.  Only continuity
is required on the boundary; the Hessian and the elliptic inequality are
used exclusively in the interior.  The C² second derivative test below is
the proof already used in `DirichletClassicalComparison`, with a public name.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace Metric Set
open scoped BigOperators ContDiff Topology

namespace KEBall

theorem dirichlet_realHessian_nonpos_of_isLocalMax_C2 {n : ℕ} {h : E n → ℝ} {x : E n}
    (hh : ContDiffAt ℝ 2 h x) (hmax : IsLocalMax h x) (v : E n) :
    realHessian h x v v ≤ 0 := by
  let γ : ℝ → E n := fun t => x + t • v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa only [γ, id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add x
  have hγ0 : γ 0 = x := by simp [γ]
  have ht : Tendsto γ (𝓝 0) (𝓝 x) := by
    simpa only [hγ0] using (hγ 0).continuousAt.tendsto
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y := by
    filter_upwards [(hh.of_le (m := 1) (by norm_num)).eventually (by simp)] with y hy
    exact hy.differentiableAt one_ne_zero
  have heq : deriv (fun t => h (γ t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ h (γ t) v) := by
    filter_upwards [ht.eventually hnear] with t htd
    exact (htd.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hdf := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hdγ : HasDerivAt (fun t => fderiv ℝ h (γ t) v)
      (realHessian h x v v) 0 := by
    have hd' : HasFDerivAt (fun y => fderiv ℝ h y v) ((realHessian h x).flip v) x := by
      simpa [realHessian] using hd
    have hdAt : HasFDerivAt (fun y => fderiv ℝ h y v) ((realHessian h x).flip v) (γ 0) := by
      simpa only [hγ0] using hd'
    exact hdAt.comp_hasDerivAt 0 (hγ 0)
  have hdd : deriv (deriv (fun t => h (γ t))) 0 = realHessian h x v v := by
    rw [heq.deriv_eq, hdγ.deriv]
  have hmaxγ : IsLocalMax (fun t => h (γ t)) 0 := by
    filter_upwards [ht.eventually hmax] with t ht'
    simpa only [hγ0] using ht'
  have hcont : ContinuousAt (fun t => h (γ t)) 0 := by
    have hc : ContinuousAt h (γ 0) := by simpa only [hγ0] using hh.continuousAt
    exact hc.comp (hγ 0).continuousAt
  exact hdd ▸ PoincareMT.LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax hmaxγ hcont

/-- A positive directional frame gives the sign needed at an interior
maximum of a twice differentiable function. -/
theorem dirichletBilinearContraction_nonpos_of_frame {n m : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    (D : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hD : ∀ v : E n, D v v ≤ 0)
    {A : E n →L[ℝ] E n} (a : Fin m → ℝ) (v : Fin m → E n)
    (ha : ∀ i, 0 ≤ a i)
    (hA : A = ∑ i : Fin m, a i • rankOne ℝ (v i) (v i)) :
    dirichletBilinearContraction b A D ≤ 0 := by
  rw [dirichletBilinearContraction_of_frame b D a v hA]
  exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (ha i) (hD (v i))

/-- The strict maximum principle on a compact set requires no derivatives
of the function on its frontier. -/
theorem dirichlet_le_frontier_of_strict_linearHessian {n : ℕ}
    {K : Set (E n)} (hK : IsCompact K)
    {w : E n → ℝ} (hw : ContinuousOn w K)
    (hw2 : ContDiffOn ℝ 2 w (interior K))
    (F : E n → (E n →L[ℝ] E n →L[ℝ] ℝ) → ℝ)
    (hF : ∀ x ∈ interior K, ∀ D : E n →L[ℝ] E n →L[ℝ] ℝ,
      (∀ v : E n, D v v ≤ 0) → F x D ≤ 0)
    (hL : ∀ x ∈ interior K, 0 < F x (realHessian w x))
    {C : ℝ} (hC : ∀ x ∈ frontier K, w x ≤ C) :
    ∀ x ∈ K, w x ≤ C := by
  intro y hy
  obtain ⟨x, hx, hMax⟩ := hK.exists_isMaxOn ⟨y, hy⟩ hw
  by_cases hxI : x ∈ interior K
  · have hLocal : IsLocalMax w x :=
      hMax.isLocalMax (mem_of_superset (isOpen_interior.mem_nhds hxI) interior_subset)
    have hSign := hF x hxI (realHessian w x)
      (dirichlet_realHessian_nonpos_of_isLocalMax_C2
        (hw2.contDiffAt (isOpen_interior.mem_nhds hxI)) hLocal)
    exact False.elim ((hL x hxI).not_ge hSign)
  · have hxF : x ∈ frontier K := ⟨subset_closure hx, hxI⟩
    exact (hMax hy).trans (hC x hxF)

/-- Operator-valued form of the actual C² Hessian sum rule. -/
theorem dirichlet_realHessian_add_C2 {n : ℕ} {u v : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    realHessian (u + v) x = realHessian u x + realHessian v x := by
  ext a b : 2
  simpa only [PshLines.realHessian_eq_fderiv, realHessian, _root_.add_apply] using
    PshLines.realHessian_add hu hv a b

/-- Operator-valued form of the actual C² Hessian scalar multiplication rule. -/
theorem dirichlet_realHessian_smul_C2 {n : ℕ} {u : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (c : ℝ) :
    realHessian (c • u) x = c • realHessian u x := by
  ext a b : 2
  simpa only [PshLines.realHessian_eq_fderiv, realHessian, _root_.smul_apply,
    smul_eq_mul] using PshLines.realHessian_smul hu c a b

/-- A strict zero-boundary barrier gives the weak maximum principle,
with no coefficient continuity or boundary differentiability assumption. -/
theorem dirichlet_le_frontier_of_linearHessian_nonneg_with_barrier {n : ℕ}
    {K : Set (E n)} (hK : IsCompact K)
    {w b : E n → ℝ} (hw : ContinuousOn w K) (hb : ContinuousOn b K)
    (hw2 : ContDiffOn ℝ 2 w (interior K))
    (hb2 : ContDiffOn ℝ 2 b (interior K))
    (F : E n → (E n →L[ℝ] E n →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ interior K, ∀ D : E n →L[ℝ] E n →L[ℝ] ℝ,
      (∀ v : E n, D v v ≤ 0) → F x D ≤ 0)
    (hLw : ∀ x ∈ interior K, 0 ≤ F x (realHessian w x))
    (hLb : ∀ x ∈ interior K, 0 < F x (realHessian b x))
    (hb0 : ∀ x ∈ frontier K, b x = 0)
    {C : ℝ} (hC : ∀ x ∈ frontier K, w x ≤ C) :
    ∀ x ∈ K, w x ≤ C := by
  have hPerturb (ε : ℝ) (hε : 0 < ε) : ∀ x ∈ K, w x + ε * b x ≤ C := by
    apply dirichlet_le_frontier_of_strict_linearHessian hK
      (hw.add (hb.const_smul ε)) (hw2.add (hb2.const_smul ε)) (fun x => F x) hF
    · intro x hx
      have hbx : ContDiffAt ℝ 2 b x := hb2.contDiffAt (isOpen_interior.mem_nhds hx)
      have hεb : ContDiffAt ℝ 2 (ε • b) x := hbx.const_smul ε
      rw [dirichlet_realHessian_add_C2 (v := ε • b)
        (hw2.contDiffAt (isOpen_interior.mem_nhds hx)) hεb,
        dirichlet_realHessian_smul_C2 hbx ε,
        map_add, map_smul, smul_eq_mul]
      exact add_pos_of_nonneg_of_pos (hLw x hx) (mul_pos hε (hLb x hx))
    · intro x hx
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb0 x hx, mul_zero, add_zero]
        using hC x hx
  intro x hx
  have hT : Tendsto (fun ε : ℝ => w x + ε * b x) (𝓝[>] (0 : ℝ)) (𝓝 (w x)) := by
    have h : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (h.mul_const (b x))
  apply le_of_tendsto hT
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hPerturb ε hε x hx

end KEBall
