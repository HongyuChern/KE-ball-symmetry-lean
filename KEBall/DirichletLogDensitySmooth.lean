import KEBall.DirichletCenterSmooth

/-! Local smoothness on the prescribed log-density path. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

/-- Smooth positive Dirichlet solutions persist for nearby log-density
parameters on the entire closed ball. -/
theorem eventually_exists_posDef_dirichlet_logDensity_smooth {n : ℕ}
    (hn : 0 < n)
    {u g : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hg : ContDiff ℝ ∞ g) (t : ℝ)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : EqOn (fun x => (complexHessian u x).det.re) (fun x => Real.exp (t * g x)) (unitBall n))
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    ∀ᶠ s in 𝓝 t, ∃ v : E n → ℝ, ContDiffOn ℝ ∞ v (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      EqOn (fun x => (complexHessian v x).det.re) (fun x => Real.exp (s * g x)) (unitBall n) := by
  let k := 2 * (2 * n + 1)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let f (p : ℝ × E n) := Real.exp (p.1 * g p.2)
  have hf : ContDiff ℝ ∞ f := (contDiff_fst.mul (hg.comp contDiff_snd)).exp
  have hfS (s : ℝ) : ContDiff ℝ ∞ (fun x => f (s, x)) := ((contDiff_const (c := s)).mul hg).exp
  let q (s : ℝ) := dirichletSobolevJetOfSmooth (k := k) hn b (hfS s)
  have hq : Continuous q := continuous_dirichletSobolevJetOfSmooth_family hn b hf hfS
  have hk : 2 * (2 * n + 1) ≤ k := le_rfl
  obtain ⟨d, G, T, hG, hT, hd, hSol⟩ := exists_smooth_closedBall_posDef_dirichlet_det_localInverse
    hn (k := k) (r := 2) hk le_rfl (by omega) hu hu0 huP ha hl hDensity hElliptic
  have hBase : q t = d := by
    apply dirichletSobolevJetGraph_fst_injective hn b
    apply Lp.ext
    filter_upwards [hd, dirichletSobolevJetOfSmooth_fst_ae hn b (hfS t), ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hD hQ hB
    exact hQ.trans ((hEq hB).symm.trans hD.symm)
  have hqD : Tendsto q (𝓝 t) (𝓝 d) := hBase ▸ hq.continuousAt
  filter_upwards [hqD.eventually hG.eventually_nhds, hqD.eventually hSol.eventually_nhds] with s hsG hsSol
  have hsData := dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hfS s)
  obtain ⟨v, hv, hv0, hvP, hvEq, _⟩ := hsSol.self_of_nhds (fun x => f (s, x))
    (hfS s).continuous.continuousOn hsData.symm
  have hvS := contDiffOn_closedBall_inter_infty_of_smooth_localInverse hn hk (U := ({0} : Set (E n))ᶜ) isClosed_singleton.isOpen_compl
    (by simp) T hT hsG hsSol (hfS s) hv hv0 hvP hvEq hsData (fun _ _ => Real.exp_pos _)
  exact ⟨v, contDiffOn_closedBall_infty_of_smooth_localInverse hn T hT hsG hsSol
    (hfS s) hv hvS hv0 hvP hvEq hsData, hv0, hvP, hvEq⟩

end KEBall
