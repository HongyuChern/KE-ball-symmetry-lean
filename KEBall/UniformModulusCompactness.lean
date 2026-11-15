import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! A uniform modulus obtained from subsequential uniform compactness. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped Topology

namespace KEBall

/-- Sequential uniform compactness with continuous limits gives a single
modulus for the whole family on a compact metric set. -/
theorem exists_uniform_modulus_of_subseq_uniform_limit
    {X I : Type*} [PseudoMetricSpace X] {S : Set X} (hS : IsCompact S)
    {u : I → X → ℝ}
    (hsub : ∀ i : ℕ → I, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : X → ℝ,
      ContinuousOn v S ∧ TendstoUniformlyOn (fun k => u (i (φ k))) v atTop S) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ i : I, ∀ x ∈ S, ∀ y ∈ S,
      dist x y < δ → dist (u i x) (u i y) < ε := by
  classical
  intro ε hε
  by_contra hno
  push_neg at hno
  have hbad (k : ℕ) := hno (1 / ((k : ℝ) + 1)) (by positivity)
  choose i x hx y hy hd hbad using hbad
  obtain ⟨φ, hφ, v, hvC, hvU⟩ := hsub i
  have he : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, hδv⟩ := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hvC) (ε / 3) he
  have hsmall : ∀ᶠ k in atTop, 1 / ((φ k : ℝ) + 1) < δ :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      hφ.tendsto_atTop).eventually_lt_const hδ
  have hclose := Metric.tendstoUniformlyOn_iff.mp hvU (ε / 3) he
  obtain ⟨k, hkC, hkS⟩ := (hclose.and hsmall).exists
  have hmid := hδv (x (φ k)) (hx (φ k)) (y (φ k)) (hy (φ k))
    ((hd (φ k)).trans hkS)
  have hleft := hkC (x (φ k)) (hx (φ k))
  have hright := hkC (y (φ k)) (hy (φ k))
  have htri₁ := dist_triangle (u (i (φ k)) (x (φ k))) (v (x (φ k)))
    (u (i (φ k)) (y (φ k)))
  have htri₂ := dist_triangle (v (x (φ k))) (v (y (φ k)))
    (u (i (φ k)) (y (φ k)))
  rw [dist_comm (u (i (φ k)) (x (φ k))) (v (x (φ k)))] at htri₁
  have hlt : dist (u (i (φ k)) (x (φ k))) (u (i (φ k)) (y (φ k))) < ε := by
    linarith only [htri₁, htri₂, hleft, hmid, hright]
  exact hlt.not_ge (hbad (φ k))

end KEBall
