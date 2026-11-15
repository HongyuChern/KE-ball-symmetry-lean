import KEBall.Specification
import KEBall.Radial

/-!
# Proved whole-paper directions

Only fully proved targets are declared here. Missing directions are tracked
externally; they are never represented by axioms, placeholder structures,
or theorem declarations with strengthened assumptions.
-/

set_option autoImplicit false

namespace KEBall

/-- The converse direction of Theorem 1.1 for every admissible dimension. -/
theorem radialExistence : RadialExistenceStatement := by
  intro n _ b hb
  exact radial_isSolution n hb

end KEBall
