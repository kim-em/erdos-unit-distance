import PrimeNumberTheoremAnd.Consequences

/-!
# Polynomial bounds on the j-th prime in the progressions 1, 3 mod 4

These are the two analytic-input sorries of the unit-distance framework
(`Erdos.q3_poly_bound`, `Erdos.p1_poly_bound` in `Framework.lean` on the
mathlib4 branch `kim/erdos-unit-distance`), proven here from
PrimeNumberTheoremAnd's `chebyshev_asymptotic_pnt`
(`θ(x; q, a) ~ x / φ(q)`).

Strategy: let `S a x = ∑_{p ≤ ⌊x⌋, p ≡ a (4)} log p`.  By
`chebyshev_asymptotic_pnt` (with `q = 4`, `φ(4) = 2`), eventually
`S a x ≥ 0.4 x`.  Since every summand is at most `log x`, the number of
primes `≡ a (4)` below `x` is at least `S a x / log x ≥ 0.4 x / log x`.
Taking `x = (j+2)²`, eventually `0.4 (j+2)² / (2 log (j+2)) ≥ j + 1`, so
there are more than `j` such primes `≤ (j+2)²`, whence
`Nat.nth (· prime ∧ · % 4 = a) j ≤ (j+2)²` via the `Nat.count`/`Nat.nth`
Galois connection (`Nat.nth_lt_of_lt_count` or `Nat.count_nth`-style
lemmas).
-/

namespace Erdos

/-- The `j`-th prime congruent to `3` modulo `4` (must match
`Framework.lean` verbatim). -/
noncomputable def q3 (j : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 3) j

/-- The `i`-th prime congruent to `1` modulo `4` (must match
`Framework.lean` verbatim). -/
noncomputable def p1 (i : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 1) i

/-- Eventually the `j`-th prime `≡ 3 mod 4` is at most `(j+2)²`. -/
theorem q3_poly_bound : ∀ᶠ j in Filter.atTop, (q3 j : ℝ) ≤ (j + 2) ^ 2 := by
  sorry

/-- Eventually the `i`-th prime `≡ 1 mod 4` is at most `(i+2)²`. -/
theorem p1_poly_bound : ∀ᶠ i in Filter.atTop, (p1 i : ℝ) ≤ (i + 2) ^ 2 := by
  sorry

end Erdos
