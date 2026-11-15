import KEBall.DirichletSobolevHessianField
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Continuous Sobolev data from a jointly smooth family of densities. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ComplexOrder ContDiff Topology

namespace KEBall

local notation "ν[" n "]" => Measure.restrict (volume0 n) (unitBall n)

section Parameter

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private noncomputable def spaceLineDerivative {n : ℕ} (d : E n) (f : P × E n → ℝ)
    (p : P × E n) : ℝ :=
  fderiv ℝ f p (0, d)

/-- A directional derivative in the parameter of a density on parameter-space pairs. -/
private noncomputable def dirichletParameterDerivative {n : ℕ} (v : P) (f : P × E n → ℝ) (p : P × E n) : ℝ :=
  fderiv ℝ f p (v, 0)

private theorem contDiff_spaceLineDerivative {n : ℕ} (d : E n) {f : P × E n → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (spaceLineDerivative d f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem contDiff_dirichletParameterDerivative {n : ℕ} (v : P) {f : P × E n → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dirichletParameterDerivative v f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem dirichletParameterDerivative_spaceLineDerivative {n : ℕ} (v : P) (d : E n) {f : P × E n → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    dirichletParameterDerivative v (spaceLineDerivative d f) = spaceLineDerivative d (dirichletParameterDerivative v f) := by
  funext p
  have hD := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p
  have hS := (hf.contDiffAt (x := p)).isSymmSndFDerivAt (by simp; norm_cast)
  change fderiv ℝ (spaceLineDerivative d f) p (v, 0) =
    fderiv ℝ (dirichletParameterDerivative v f) p (0, d)
  rw [show fderiv ℝ (spaceLineDerivative d f) p = (fderiv ℝ (fderiv ℝ f) p).flip (0, d) by
    unfold spaceLineDerivative
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      (hD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, d) p)).fderiv,
    show fderiv ℝ (dirichletParameterDerivative v f) p = (fderiv ℝ (fderiv ℝ f) p).flip (v, 0) by
      unfold dirichletParameterDerivative
      simpa only [ContinuousLinearMap.comp_zero, zero_add] using
        (hD.hasFDerivAt.clm_apply (hasFDerivAt_const (v, 0) p)).fderiv]
  exact hS.eq (v, 0) (0, d)

private theorem contDiff_foldr_spaceLineDerivative {n : ℕ} (ds : List (E n))
    {f : P × E n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ds.foldr spaceLineDerivative f) := by
  induction ds with
  | nil => exact hf
  | cons d ds ih => exact contDiff_spaceLineDerivative d ih

private theorem dirichletParameterDerivative_foldr_spaceLineDerivative {n : ℕ} (v : P) (ds : List (E n))
    {f : P × E n → ℝ} (hf : ContDiff ℝ ∞ f) :
    dirichletParameterDerivative v (ds.foldr spaceLineDerivative f) = ds.foldr spaceLineDerivative (dirichletParameterDerivative v f) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldr_cons]
    rw [dirichletParameterDerivative_spaceLineDerivative v d (contDiff_foldr_spaceLineDerivative ds hf), ih]

private theorem foldr_spaceLineDerivative_eq_slice {n : ℕ} (ds : List (E n))
    {f : P × E n → ℝ} (hf : ContDiff ℝ ∞ f) (t : P) :
    (fun x => (ds.foldr spaceLineDerivative f) (t, x)) =
      ds.foldr (fun d G y => fderiv ℝ G y d) (fun x => f (t, x)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    funext x
    have hD := ((contDiff_foldr_spaceLineDerivative ds hf).differentiable
      (by simp) (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    change fderiv ℝ (ds.foldr spaceLineDerivative f) (t, x) (0, d) =
      fderiv ℝ (ds.foldr (fun d G y => fderiv ℝ G y d) (fun x => f (t, x))) x d
    rw [← ih]
    change _ = fderiv ℝ (ds.foldr spaceLineDerivative f ∘ Prod.mk t) x d
    rw [hD.fderiv]
    rfl

private theorem continuous_lineDerivative_family {n : ℕ} {f : P × E n → ℝ}
    (hf : ContDiff ℝ ∞ f) (ds : List (E n)) :
    Continuous (fun p : P × E n =>
      (ds.foldr (fun d D y => fderiv ℝ D y d) (fun x => f (p.1, x))) p.2) :=
  (contDiff_foldr_spaceLineDerivative ds hf).continuous.congr
    (fun p => congrFun (foldr_spaceLineDerivative_eq_slice ds hf p.1) p.2)

local instance (n : ℕ) : CompactSpace (ClosedBall n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) 1)

omit [NormedSpace ℝ P] in
private theorem eventually_uniform_close_on_closedBall {n : ℕ}
    {Y : Type*} [NormedAddCommGroup Y] {f : P × E n → Y}
    (hf : Continuous f) (t : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 t, ∀ x ∈ closedUnitBall n, ‖f (s, x) - f (t, x)‖ < ε := by
  let O := {p : P × E n | ‖f p - f (t, p.2)‖ < ε}
  have hO : IsOpen O :=
    isOpen_lt (hf.sub (hf.comp (continuous_const.prodMk continuous_snd))).norm continuous_const
  have hSub : ({t} : Set P) ×ˢ closedUnitBall n ⊆ O := by
    rintro ⟨s, x⟩ ⟨hs, _⟩
    have he : s = t := hs
    subst s
    simpa [O] using hε
  obtain ⟨U, V, hU, _, htU, hKV, hUO⟩ := generalized_tube_lemma isCompact_singleton
    (isCompact_closedBall (0 : E n) 1)
    hO hSub
  filter_upwards [hU.mem_nhds (htU (mem_singleton t))] with s hs x hx
  exact hUO ⟨hs, hKV hx⟩

omit [NormedSpace ℝ P] in
private theorem continuous_dirichletBallL2_family {n : ℕ} (hn : 0 < n)
    {f : P × E n → ℝ} (hf : Continuous f)
    (q : P → DirichletBallL2 n ℝ) (hq : ∀ t, q t =ᵐ[ν[n]] fun x => f (t, x)) :
    Continuous q := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_uniform_close_on_closedBall hf t (half_pos hε)] with s hs
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  have hBound : ∀ᵐ x ∂ν[n], ‖(q s - q t : DirichletBallL2 n ℝ) x‖ ≤ ε / 2 := by
    filter_upwards [Lp.coeFn_sub (q s) (q t), hq s, hq t, ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hx hS hT hB
    rw [hx, Pi.sub_apply, hS, hT]
    exact (hs x (ball_subset_closedBall hB)).le
  simpa [measureUnivNNReal, measure_univ] using Lp.norm_le_of_ae_bound (half_pos hε).le hBound

/-- Jointly smooth densities depend continuously on their parameter in
every finite-order Sobolev graph. -/
theorem continuous_dirichletSobolevJetOfSmooth_family {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {f : P × E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (h : ∀ t, ContDiff ℝ ∞ (fun x => f (t, x))) :
    Continuous (fun t => dirichletSobolevJetOfSmooth (k := k) hn b (h t)) := by
  let q (t : P) := dirichletSobolevJetOfSmooth (k := k) hn b (h t)
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun s => ((q s).val.1, (q s).val.2)) (𝓝 t) (𝓝 ((q t).val.1, (q t).val.2))
  rw [nhds_prod_eq]
  apply Tendsto.prodMk
  · exact (continuous_dirichletBallL2_family hn hf.continuous (fun s => (q s).val.1)
      (fun s => dirichletSobolevJetOfSmooth_fst_ae hn b (h s))).continuousAt
  · apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_dirichletBallL2_family hn (continuous_lineDerivative_family hf (dirichletJetDirections b i))
      (fun s => (q s).val.2 i) (fun s => dirichletSobolevJetOfSmooth_snd_ae hn b (h s) i)).continuousAt

/-- Uniform control on the compact ball upgrades the pointwise parameter
derivative to a derivative of the (L^2)-valued density. -/
private theorem hasFDerivAt_dirichletBallL2_family {n : ℕ} (hn : 0 < n)
    {f : P × E n → ℝ} {g : P × E n → P →L[ℝ] ℝ} (hg : Continuous g)
    (hDeriv : ∀ t x, HasFDerivAt (fun s => f (s, x)) (g (t, x)) t)
    (q : P → DirichletBallL2 n ℝ) (p : P →L[ℝ] DirichletBallL2 n ℝ)
    (hq : ∀ t, q t =ᵐ[ν[n]] fun x => f (t, x)) (t : P)
    (hp : ∀ v, p v =ᵐ[ν[n]] fun x => g (t, x) v) :
    HasFDerivAt q p t := by
  have : NeZero n := ⟨hn.ne'⟩
  have : IsProbabilityMeasure ν[n] := volume0_restrict_isProbability n
  apply hasFDerivAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hSub⟩ := Metric.mem_nhds_iff.mp (eventually_uniform_close_on_closedBall hg t hε)
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
  let F := q s - q t - p (s - t)
  change ‖F‖ ≤ ε * ‖s - t‖
  have hRem (x : E n) (hx : x ∈ closedUnitBall n) :
      ‖f (s, x) - f (t, x) - g (t, x) (s - t)‖ ≤ ε * ‖s - t‖ := by
    let a (r : P) := f (r, x) - g (t, x) (r - t)
    have ha (r : P) : HasFDerivAt a (g (r, x) - g (t, x)) r := by
      have hd := (g (t, x)).hasFDerivAt.comp r ((hasFDerivAt_id r).sub_const t)
      rw [show a = (fun s => f (s, x)) - (g (t, x) ∘ fun y => id y - t) by rfl]
      exact (hDeriv r x).sub (by simpa only [ContinuousLinearMap.comp_id] using hd)
    have hm := (convex_ball t δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun r _ => (ha r).hasFDerivWithinAt)
      (fun r hr => (hSub hr x hx).le) (Metric.mem_ball_self hδ) hs
    simpa only [a, sub_self, map_zero, sub_zero, sub_right_comm] using hm
  have hBound : ∀ᵐ x ∂ν[n], ‖F x‖ ≤ ε * ‖s - t‖ := by
    filter_upwards [Lp.coeFn_sub (q s - q t) (p (s - t)), Lp.coeFn_sub (q s) (q t),
      hq s, hq t, hp (s - t), ae_restrict_mem (μ := volume0 n)
        (show MeasurableSet (unitBall n) from measurableSet_ball)]
      with x hF hST hQS hQT hPT hB
    rw [show F = q s - q t - p (s - t) from rfl, hF, Pi.sub_apply, hST,
      Pi.sub_apply, hQS, hQT, hPT]
    exact hRem x (ball_subset_closedBall hB)
  simpa [measureUnivNNReal, measure_univ] using
    Lp.norm_le_of_ae_bound (mul_nonneg hε.le (norm_nonneg _)) hBound

private noncomputable def partialParameter {n : ℕ} (f : P × E n → ℝ) (p : P × E n) :
    P →L[ℝ] ℝ :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ P (E n))

private theorem continuous_partialParameter {n : ℕ} {f : P × E n → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (partialParameter f) :=
  (hf.fderiv_right (m := 0) (by simp)).continuous.clm_comp continuous_const

private theorem hasFDerivAt_partialParameter {n : ℕ} {f : P × E n → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : P) (x : E n) :
    HasFDerivAt (fun s => f (s, x)) (partialParameter f (t, x)) t := by
  exact (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)

variable [FiniteDimensional ℝ P]

private theorem hasFDerivAt_dirichletSobolevJetOfSmooth_family {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n))
    {f : P × E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfS : ∀ t, ContDiff ℝ ∞ (fun x => f (t, x)))
    (hD : ∀ v t, ContDiff ℝ ∞ (fun x => dirichletParameterDerivative v f (t, x))) (t : P) :
    ∃ L : P →L[ℝ] dirichletSobolevJetGraph (k := k) b,
      HasFDerivAt (fun s => dirichletSobolevJetOfSmooth (k := k) hn b (hfS s)) L t ∧
      ∀ v, L v = dirichletSobolevJetOfSmooth hn b (hD v t) := by
  let X := dirichletSobolevJetGraph (k := k) b
  let q (s : P) := dirichletSobolevJetOfSmooth (k := k) hn b (hfS s)
  let p (v : P) : X := dirichletSobolevJetOfSmooth hn b (hD v t)
  let L : P →ₗ[ℝ] X :=
    { toFun := p
      map_add' := fun v w => by
        apply dirichletSobolevJetGraph_fst_injective hn b
        apply Lp.ext
        filter_upwards [dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hD (v + w) t),
          dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hD v t),
          dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hD w t),
          Lp.coeFn_add (p v).val.1 (p w).val.1] with x hVW hV hW hAdd
        change (p (v + w)).val.1 x = ((p v).val.1 + (p w).val.1) x
        rw [hVW, hAdd, Pi.add_apply, hV, hW]
        exact (partialParameter f (t, x)).map_add v w
      map_smul' := fun c v => by
        apply dirichletSobolevJetGraph_fst_injective hn b
        apply Lp.ext
        filter_upwards [dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hD (c • v) t),
          dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hD v t),
          Lp.coeFn_smul c (p v).val.1] with x hCV hV hSmul
        change (p (c • v)).val.1 x = (c • (p v).val.1) x
        rw [hCV, hSmul, Pi.smul_apply, hV]
        exact (partialParameter f (t, x)).map_smul c v }
  let D : P →L[ℝ] X := L.toContinuousLinearMap
  let A := DirichletJetGraphAmbient n k
  let C : X →L[ℝ] A := (dirichletSobolevJetGraph (k := k) b).subtypeL
  let D₁ : P →L[ℝ] DirichletBallL2 n ℝ := (ContinuousLinearMap.fst ℝ _ _).comp (C.comp D)
  let D₂ : P →L[ℝ] (DirichletJetIndex n k → DirichletBallL2 n ℝ) :=
    (ContinuousLinearMap.snd ℝ _ _).comp (C.comp D)
  have hF : HasFDerivAt (fun s => (q s).val.1) D₁ t :=
    hasFDerivAt_dirichletBallL2_family hn (continuous_partialParameter hf)
      (hasFDerivAt_partialParameter hf) (fun s => (q s).val.1) D₁
      (fun s => dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hfS s)) t
      (fun v => dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hD v t))
  have hS : HasFDerivAt (fun s => (q s).val.2) D₂ t := by
    apply hasFDerivAt_pi'.mpr
    intro i
    let ds := dirichletJetDirections b i
    have hG := contDiff_foldr_spaceLineDerivative ds hf
    apply hasFDerivAt_dirichletBallL2_family hn (continuous_partialParameter hG)
      (hasFDerivAt_partialParameter hG)
    · intro s
      rw [foldr_spaceLineDerivative_eq_slice ds hf]
      exact dirichletSobolevJetOfSmooth_snd_ae hn b (hfS s) i
    · intro v
      change (p v).val.2 i =ᵐ[ν[n]] fun x => dirichletParameterDerivative v (ds.foldr spaceLineDerivative f) (t, x)
      rw [dirichletParameterDerivative_foldr_spaceLineDerivative v ds hf,
        foldr_spaceLineDerivative_eq_slice ds (contDiff_dirichletParameterDerivative v hf)]
      exact dirichletSobolevJetOfSmooth_snd_ae hn b (hD v t) i
  have hA : HasFDerivAt (fun s => (q s).val) (C.comp D) t := by
    convert hF.prodMk hS using 1
    ext v : 1
    rfl
  refine ⟨D, hasFDerivAt_iff_isLittleO.mpr ?_, fun _ => rfl⟩
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [(hasFDerivAt_iff_isLittleO.mp hA).bound hc] with s hs
  change ‖(q s - q t - D (s - t)).val‖ ≤ c * ‖s - t‖
  exact hs

/-- Jointly smooth densities give smooth maps from any finite-dimensional
parameter space into a fixed finite-order Sobolev graph. -/
theorem contDiff_dirichletSobolevJetOfSmooth_family {n k : ℕ} (hn : 0 < n)
    (b : OrthonormalBasis (Fin (2 * n)) ℝ (E n)) {f : P × E n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfS : ∀ t, ContDiff ℝ ∞ (fun x => f (t, x))) :
    ContDiff ℝ ∞ (fun t => dirichletSobolevJetOfSmooth (k := k) hn b (hfS t)) := by
  apply contDiff_infty.mpr
  intro m
  induction m generalizing f with
  | zero =>
    exact contDiff_zero.mpr (continuous_dirichletSobolevJetOfSmooth_family hn b hf hfS)
  | succ m ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    have hDS (v : P) (t : P) : ContDiff ℝ ∞ (fun x => dirichletParameterDerivative v f (t, x)) :=
      (contDiff_dirichletParameterDerivative v hf).comp (contDiff_const.prodMk contDiff_id)
    choose L hL hA using hasFDerivAt_dirichletSobolevJetOfSmooth_family (k := k) hn b hf hfS hDS
    refine ⟨fun t => (hL t).differentiableAt, by simp, fun v => ?_⟩
    have he : (fun t => fderiv ℝ (fun s => dirichletSobolevJetOfSmooth (k := k) hn b (hfS s)) t v) =
        fun t => dirichletSobolevJetOfSmooth (k := k) hn b (hDS v t) := by
      funext t
      rw [(hL t).fderiv, hA]
    rw [he]
    exact ih (contDiff_dirichletParameterDerivative v hf) (hDS v)

end Parameter

/-- The log-density path is locally solvable with any prescribed finite regularity at every smooth
uniformly elliptic zero-boundary solution. -/
theorem eventually_exists_closedBall_posDef_dirichlet_logDensity {n r : ℕ} (hn : 0 < n)
    (hr : 2 ≤ r)
    {u g : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hg : ContDiff ℝ ∞ g) (t : ℝ)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : EqOn (fun x => (complexHessian u x).det.re) (fun x => Real.exp (t * g x)) (unitBall n))
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    ∀ᶠ s in 𝓝 t, ∃ v : E n → ℝ, ContDiffOn ℝ (r : ℕ∞ω) v (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      (∀ x ∈ unitBall n, (complexHessian v x).PosDef) ∧
      EqOn (fun x => (complexHessian v x).det.re) (fun x => Real.exp (s * g x)) (unitBall n) := by
  let k := r + 2 * (2 * n + 1)
  let b := EuclideanSpace.basisFun (Fin (2 * n)) ℝ
  let f (p : ℝ × E n) := Real.exp (p.1 * g p.2)
  have hf : ContDiff ℝ ∞ f := (contDiff_fst.mul (hg.comp contDiff_snd)).exp
  have hfS (s : ℝ) : ContDiff ℝ ∞ (fun x => f (s, x)) := ((contDiff_const (c := s)).mul hg).exp
  let q (s : ℝ) := dirichletSobolevJetOfSmooth (k := k) hn b (hfS s)
  have hq : Continuous q := continuous_dirichletSobolevJetOfSmooth_family hn b hf hfS
  obtain ⟨d, hd, h⟩ := eventually_exists_closedBall_posDef_dirichlet_det hn (k := k)
    (Nat.le_add_left _ _) hr (Nat.le_add_right _ _) hu hu0 huP ha hl hDensity hElliptic
  have hBase : q t = d := by
    apply dirichletSobolevJetGraph_fst_injective hn b
    apply Lp.ext
    filter_upwards [hd, dirichletSobolevJetOfSmooth_fst_ae hn b (hfS t), ae_restrict_mem (μ := volume0 n)
      (show MeasurableSet (unitBall n) from measurableSet_ball)] with x hD hQ hB
    exact hQ.trans ((hEq hB).symm.trans hD.symm)
  have hT : Tendsto q (𝓝 t) (𝓝 d) := hBase ▸ hq.continuousAt
  filter_upwards [hT.eventually h] with s hs
  exact hs (fun x => f (s, x)) (hfS s).continuous.continuousOn
    (dirichletSobolevJetOfSmooth_fst_ae (k := k) hn b (hfS s)).symm

/-- The log-density path is locally solvable in C² at every smooth
uniformly elliptic zero-boundary solution. -/
theorem eventually_exists_closedBall_C2_dirichlet_logDensity {n : ℕ} (hn : 0 < n)
    {u g : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hg : ContDiff ℝ ∞ g) (t : ℝ)
    (hu0 : ∀ x ∈ unitSphere n, u x = 0)
    (huP : ∀ x ∈ unitBall n, (complexHessian u x).PosDef)
    (hEq : EqOn (fun x => (complexHessian u x).det.re) (fun x => Real.exp (t * g x)) (unitBall n))
    {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (hDensity : ∀ x ∈ unitBall n, a ≤ (complexHessian u x).det.re)
    (hElliptic : ∀ x ∈ unitBall n, ∀ v : E n,
      l * ‖v‖ ^ 2 ≤ complexLaplacian u (fun y => (inner ℝ v y) ^ 2 / 2) x) :
    ∀ᶠ s in 𝓝 t, ∃ v : E n → ℝ, ContDiffOn ℝ 2 v (closedUnitBall n) ∧
      (∀ x ∈ unitSphere n, v x = 0) ∧
      EqOn (fun x => (complexHessian v x).det.re) (fun x => Real.exp (s * g x)) (unitBall n) := by
  filter_upwards [eventually_exists_closedBall_posDef_dirichlet_logDensity hn
    (r := 2) le_rfl hu hg t hu0 huP hEq ha hl hDensity hElliptic] with s hs
  obtain ⟨v, hv, hv0, _, he⟩ := hs
  exact ⟨v, hv, hv0, he⟩

end KEBall
