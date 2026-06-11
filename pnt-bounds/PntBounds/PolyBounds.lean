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
  let S : ℝ → ℝ := fun x =>
    ∑ p ∈ Finset.Iic ⌊x⌋₊ with Nat.Prime p, if p % 4 = a then Real.log (p : ℝ) else 0
  have hcheb : Asymptotics.IsEquivalent Filter.atTop S
      (fun x : ℝ => x / (Nat.totient 4 : ℝ)) := by
    exact chebyshev_asymptotic_pnt (by norm_num)
      (by rcases ha with rfl | rfl <;> norm_num)
      (by rcases ha with rfl | rfl <;> norm_num)
  have hSreal : ∀ᶠ x : ℝ in atTop, (2 / 5 : ℝ) * x ≤ S x := by
    have hne : ∀ᶠ x : ℝ in atTop, x / (Nat.totient 4 : ℝ) ≠ 0 := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : x ≠ 0 := by linarith
      norm_num [hx0]
    have ht : Tendsto (S / (fun x : ℝ => x / (Nat.totient 4 : ℝ))) atTop
        (nhds (1 : ℝ)) :=
      (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hcheb
    have hratio : ∀ᶠ x : ℝ in atTop,
        (4 / 5 : ℝ) < (S / (fun x : ℝ => x / (Nat.totient 4 : ℝ))) x :=
      ht.eventually
        (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi (4 / 5 : ℝ) by norm_num))
    filter_upwards [hratio, eventually_ge_atTop (1 : ℝ)] with x hxratio hxge
    have hden : 0 < x / (Nat.totient 4 : ℝ) := by
      have htot : (Nat.totient 4 : ℝ) = 2 := by
        norm_num [show Nat.totient 4 = 2 by decide]
      rw [htot]
      linarith
    have hlt : (4 / 5 : ℝ) * (x / (Nat.totient 4 : ℝ)) < S x := by
      have := (lt_div_iff₀ hden).mp hxratio
      simpa [Pi.div_apply] using this
    have htot : (Nat.totient 4 : ℝ) = 2 := by
      norm_num [show Nat.totient 4 = 2 by decide]
    rw [htot] at hlt
    norm_num at hlt
    linarith
  have hSnat : ∀ᶠ n : ℕ in atTop, (2 / 5 : ℝ) * (n : ℝ) ≤ S n :=
    tendsto_natCast_atTop_atTop.eventually hSreal
  have hsucc : ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) / (4 * Real.log ((n + 1 : ℕ) : ℝ)) ≤
        Nat.count (fun p => p.Prime ∧ p % 4 = a) (n + 1) := by
    filter_upwards [hSnat, eventually_ge_atTop 2] with n hS hn
    have hsum_eq :
        S n =
          ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a),
            Real.log (p : ℝ) := by
      change
        (∑ p ∈ Finset.Iic ⌊(n : ℝ)⌋₊ with Nat.Prime p,
            if p % 4 = a then Real.log (p : ℝ) else 0) =
          ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a),
            Real.log (p : ℝ)
      rw [Nat.floor_natCast]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext p
        simp [and_assoc]
      · intro x hx
        rfl
    have hsum_le :
        S n ≤
          (Nat.count (fun p => p.Prime ∧ p % 4 = a) (n + 1) : ℝ) *
            Real.log ((n + 1 : ℕ) : ℝ) := by
      rw [hsum_eq, Nat.count_eq_card_filter_range]
      have hsum := Finset.sum_le_card_nsmul
        ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a))
        (fun p => Real.log (p : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ)) ?_
      simpa [nsmul_eq_mul] using hsum
      intro p hp
      have hpmem : p ∈ Finset.range (n + 1) ∧ (p.Prime ∧ p % 4 = a) := by
        simpa using hp
      have hpr : p.Prime := hpmem.2.1
      have hple : p ≤ n := Nat.lt_succ_iff.mp (by simpa using hpmem.1)
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      exact Real.log_le_log hp_pos (by exact_mod_cast Nat.le_trans hple (Nat.le_succ n))
    have hlogpos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
    rw [div_le_iff₀ (mul_pos (by norm_num) hlogpos)]
    have hnum : ((n + 1 : ℕ) : ℝ) / 4 ≤ (2 / 5 : ℝ) * (n : ℝ) := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      nlinarith
    nlinarith [hnum, hS, hsum_le]
  rcases Filter.eventually_atTop.mp hsucc with ⟨N, hN⟩
  refine Filter.eventually_atTop.mpr ⟨N + 1, ?_⟩
  intro x hx
  have hxpos : 0 < x := by omega
  have hNx : N ≤ x - 1 := by omega
  have hx' := hN (x - 1) hNx
  have hxsub : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
  simpa [hxsub] using hx'

/-- Eventually the `j`-th prime `≡ 3 mod 4` is at most `(j+2)²`. -/
theorem q3_poly_bound : ∀ᶠ j in Filter.atTop, (q3 j : ℝ) ≤ ((j : ℝ) + 2) ^ 2 :=
  nth_le_sq_of_count_ge _ (count_mod_four_ge (Or.inr rfl))

/-- Eventually the `i`-th prime `≡ 1 mod 4` is at most `(i+2)²`. -/
theorem p1_poly_bound : ∀ᶠ i in Filter.atTop, (p1 i : ℝ) ≤ ((i : ℝ) + 2) ^ 2 :=
  nth_le_sq_of_count_ge _ (count_mod_four_ge (Or.inl rfl))

end Erdos
