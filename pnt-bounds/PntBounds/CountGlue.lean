import Mathlib

/-!
# From prime-counting lower bounds to nth-prime upper bounds

Mathlib-only glue: if eventually `count p x ≥ x / (4 log x)`, then
eventually `nth p j ≤ (j+2)²`.  Combined (in `PolyBounds.lean`) with a
Chebyshev-type lower bound for primes in a fixed residue class mod 4
(from PrimeNumberTheoremAnd), this yields the two analytic-input sorries
`q3_poly_bound`, `p1_poly_bound` of the unit-distance framework.
-/

namespace Erdos

open Filter Real

/-- If eventually `count p x ≥ x / (4 log x)`, then eventually
`nth p j ≤ (j+2)²`.  (Key step: at `x = (j+2)²` the hypothesis gives
`count p x ≥ (j+2)²/(8 log (j+2)) > j` for large `j`, using
`log y ≤ 2√y`; conclude with `Nat.nth_lt_of_lt_count`.) -/
theorem nth_le_sq_of_count_ge (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ᶠ x : ℕ in atTop, (x : ℝ) / (4 * Real.log x) ≤ Nat.count p x) :
    ∀ᶠ j : ℕ in atTop, (Nat.nth p j : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by
  have hx : Tendsto (fun j : ℕ => (j + 2) ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun j => by simp only [id_eq]; nlinarith) tendsto_id
  filter_upwards [hx.eventually h, eventually_ge_atTop 255] with j hcount hj
  set y : ℝ := (j : ℝ) + 2 with hy
  have hy257 : (257 : ℝ) ≤ y := by
    have : (255 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    simp only [hy]; linarith
  have hyx : (((j + 2) ^ 2 : ℕ) : ℝ) = y ^ 2 := by push_cast; ring
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hs2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have hs16 : (16 : ℝ) ≤ Real.sqrt y := by
    have : (16 : ℝ) = Real.sqrt 256 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlogy : Real.log y ≤ 2 * Real.sqrt y := by
    have hsq : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
      Real.log_le_sub_one_of_pos (by nlinarith)
    have hls : Real.log (Real.sqrt y) = Real.log y / 2 :=
      Real.log_sqrt (by linarith)
    linarith [hls ▸ hsq]
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  -- the hypothesis at x = (j+2)²
  have hcount' : y ^ 2 / (8 * Real.log y) ≤ (Nat.count p ((j + 2) ^ 2) : ℝ) := by
    have hlog : Real.log (((j + 2) ^ 2 : ℕ) : ℝ) = 2 * Real.log y := by
      rw [hyx, show y ^ 2 = y * y by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [hlog, hyx] at hcount
    calc y ^ 2 / (8 * Real.log y) = y ^ 2 / (4 * (2 * Real.log y)) := by ring_nf
    _ ≤ _ := hcount
  -- conclude j < count
  have h8 : 8 * Real.log y ≤ y := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.sqrt y - 16 by linarith) hs0]
  have hjy : (j : ℝ) < y ^ 2 / (8 * Real.log y) := by
    rw [lt_div_iff₀ (by positivity)]
    have hjlt : (j : ℝ) < y := by rw [hy]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h8 (Nat.cast_nonneg j : (0 : ℝ) ≤ j),
      mul_lt_mul_of_pos_right hjlt (show (0 : ℝ) < y by linarith)]
  have hjc : j < Nat.count p ((j + 2) ^ 2) := by
    have : (j : ℝ) < (Nat.count p ((j + 2) ^ 2) : ℝ) := lt_of_lt_of_le hjy hcount'
    exact_mod_cast this
  have hnth : Nat.nth p j < (j + 2) ^ 2 := Nat.nth_lt_of_lt_count hjc
  calc (Nat.nth p j : ℝ) ≤ (((j + 2) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnth.le
  _ = y ^ 2 := hyx

end Erdos
