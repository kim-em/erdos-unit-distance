import PrimeNumberTheoremAnd.Consequences
import PntBounds.CountGlue

/-!
# Polynomial bounds on the j-th prime in the progressions 1, 3 mod 4

These are the two analytic-input sorries of the unit-distance framework
(`Erdos.q3_poly_bound`, `Erdos.p1_poly_bound` in `Framework.lean` on the
mathlib4 branch `kim/erdos-unit-distance`), proven here from
PrimeNumberTheoremAnd's `chebyshev_asymptotic_pnt`
(`θ(x; q, a) ~ x / φ(q)`) via the Mathlib-only reduction
`Erdos.nth_le_sq_of_count_ge` of `CountGlue.lean`.
-/

namespace Erdos

open Filter Real Finset

/-- The `j`-th prime congruent to `3` modulo `4` (must match
`Framework.lean` verbatim). -/
noncomputable def q3 (j : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 3) j

/-- The `i`-th prime congruent to `1` modulo `4` (must match
`Framework.lean` verbatim). -/
noncomputable def p1 (i : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 1) i

/-- Chebyshev-type counting lower bound in a primitive class mod 4:
eventually `#{p < x : p prime, p ≡ a mod 4} ≥ x / (4 log x)`.
Sketch: `chebyshev_asymptotic_pnt` gives
`S x := ∑_{p ≤ ⌊x⌋, p ≡ a (4)} log p ~ x/2`, so eventually `S x ≥ 2x/5`;
each summand is at most `log x` and the number of nonzero summands among
`p ≤ n - 1` is `Nat.count _ n`, so
`count n ≥ S (n-1) / log n ≥ (2(n-1)/5) / log n ≥ n / (4 log n)`. -/
theorem count_mod_four_ge {a : ℕ} (ha : a = 1 ∨ a = 3) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / (4 * Real.log x) ≤ Nat.count (fun n => n.Prime ∧ n % 4 = a) x := by
  sorry

/-- Eventually the `j`-th prime `≡ 3 mod 4` is at most `(j+2)²`. -/
theorem q3_poly_bound : ∀ᶠ j in Filter.atTop, (q3 j : ℝ) ≤ ((j : ℝ) + 2) ^ 2 :=
  nth_le_sq_of_count_ge _ (count_mod_four_ge (Or.inr rfl))

/-- Eventually the `i`-th prime `≡ 1 mod 4` is at most `(i+2)²`. -/
theorem p1_poly_bound : ∀ᶠ i in Filter.atTop, (p1 i : ℝ) ≤ ((i : ℝ) + 2) ^ 2 :=
  nth_le_sq_of_count_ge _ (count_mod_four_ge (Or.inl rfl))

end Erdos
