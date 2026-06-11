import LeanEval.Combinatorics.UnitDistance
import EvalTools.Markers

namespace LeanEval
namespace Combinatorics

/-!
# The uniform-constant Erdős unit-distance conjecture is false

L. Alpöge, *Integral points on norm-one tori and the Erdős unit-distance
exponent* (2026).

The literal negation of Erdős's 1946 conjecture
`ν(n) ≤ n^{1 + C / log log n}`: for every `C > 0` there are arbitrarily
large `n` admitting `n`-point planar sets with more than
`n^{1 + C / log log n}` unit-distance pairs.  Strictly weaker than
`erdos_unit_distance_conjecture_false` (the fixed-power-gain refutation),
and provable without class field theory.
-/

/-- **Alpöge (2026): the uniform-constant form of Erdős's unit-distance
conjecture is false.**  For every `C > 0` and every threshold `N` there
exist `n ≥ N` and a finite `P ⊆ ℝ²` with `|P| = n` and more than
`n^{1 + C / log log n}` unit-distance pairs. -/
@[eval_problem]
theorem erdos_unit_distance_uniform_constant_false :
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))),
        N ≤ n ∧ P.card = n ∧
        (n : ℝ) ^ (1 + C / Real.log (Real.log n)) < (unitDist P : ℝ) := by
  sorry

end Combinatorics
end LeanEval
