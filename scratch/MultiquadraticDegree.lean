import Mathlib

/-!
# Bridge: square-class descent ⟹ `Kf_finrank`

Fallback decomposition for the multiquadratic-degree theorem
`Module.finrank ℚ (Kf g) = 2 ^ (g + 1)`, assuming the square-class
descent kernel of `SquareClassDescent.lean`.  Steps:

* `q3_not_squareClass`: a prime `≡ 3 mod 4` is not a square times a
  product of smaller such primes (`padicValRat` parity at `q3 n`).
* `sqrt_q3_notMem_tower`: hence `√(q3 n) ∉ ℚ(√q3 0, …, √q3 (n-1))`
  (descent kernel + previous step).
* `sqrtTower_finrank`: the real tower has degree `2^n` (induction;
  each step is a degree-2 simple extension since `X² - q3 n` has no
  root by the previous step).
* `Kf_finrank`: complexify (`IntermediateField.map` along
  `Complex.ofRealHom`, which preserves `finrank`), identify `Kf g` with
  `(complexified tower) ⊔ ℚ(i)`, and double the degree once more since
  `X² + 1` has no root in a subfield of `ℝ`'s image.

The statements below are sorried; they are exact targets for
Aristotle/Codex once `SquareClassDescent.lean` is complete.
-/

namespace Erdos

open IntermediateField

noncomputable def q3 (j : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 3) j

theorem infinite_setOf_q3 : {n | n.Prime ∧ n % 4 = 3}.Infinite := by
  have h : {p : ℕ | p.Prime ∧ p ≡ 3 [MOD 4]}.Infinite :=
    Nat.infinite_setOf_prime_and_modEq (by norm_num) (by decide)
  convert h using 2 with n

theorem q3_spec (j : ℕ) : (q3 j).Prime ∧ q3 j % 4 = 3 :=
  Nat.nth_mem_of_infinite infinite_setOf_q3 j

theorem q3_strictMono : StrictMono q3 :=
  Nat.nth_strictMono infinite_setOf_q3

open IntermediateField

/-- Iterated real quadratic tower `ℚ(√c₀, …, √c_{n-1}) ⊆ ℝ`. -/
noncomputable def sqrtTower (c : ℕ → ℚ) (n : ℕ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ((fun j => Real.sqrt (c j)) '' Set.Iio n)

theorem sqrtTower_zero (c : ℕ → ℚ) : sqrtTower c 0 = ⊥ := by
  simp [sqrtTower]

theorem sqrtTower_succ (c : ℕ → ℚ) (n : ℕ) :
    sqrtTower c (n + 1)
      = (sqrtTower c n) ⊔ IntermediateField.adjoin ℚ {Real.sqrt (c n)} := by
  rw [sqrtTower, sqrtTower, ← IntermediateField.adjoin_union]
  congr 1
  rw [show Set.Iio (n + 1) = Set.Iio n ∪ {n} by ext k; simp only [Set.mem_Iio, Set.mem_union, Set.mem_singleton_iff]; omega]
  rw [Set.image_union, Set.image_singleton]

/-- If `x² ∈ K`, every element of `K ⊔ ℚ(x)` has the form `a + b·x` with
`a, b ∈ K`: the set of such elements is an intermediate field containing
`K` and `x`.  (For closure under inverses: if `a + bx ≠ 0` and
`a² - b²x² ≠ 0` use the conjugate; if `a² = b²x²` then `a + bx ≠ 0` forces
`a = bx`, so `a + bx = 2bx` and `(2bx)⁻¹ = (2bx²)⁻¹·x` with
`(2bx²)⁻¹ ∈ K`.) -/
theorem mem_sup_adjoin_sq {K : IntermediateField ℚ ℝ} {x : ℝ} (hx2 : x ^ 2 ∈ K)
    {y : ℝ} (hy : y ∈ K ⊔ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℝ, a ∈ K ∧ b ∈ K ∧ y = a + b * x := by
  let S : IntermediateField ℚ ℝ :=
    { carrier := {y | ∃ a b : ℝ, a ∈ K ∧ b ∈ K ∧ y = a + b * x}
      zero_mem' := by
        exact ⟨0, 0, zero_mem K, zero_mem K, by simp⟩
      add_mem' := by
        rintro y z ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
        exact ⟨a + c, b + d, add_mem ha hc, add_mem hb hd, by ring⟩
      one_mem' := by
        exact ⟨1, 0, one_mem K, zero_mem K, by simp⟩
      mul_mem' := by
        rintro y z ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
        refine ⟨a * c + (b * d) * x ^ 2, a * d + b * c, ?_, ?_, by ring⟩
        · exact add_mem (mul_mem ha hc) (mul_mem (mul_mem hb hd) hx2)
        · exact add_mem (mul_mem ha hd) (mul_mem hb hc)
      algebraMap_mem' := by
        intro q
        exact ⟨q, 0, SubfieldClass.ratCast_mem K q, zero_mem K, by simp⟩
      inv_mem' := by
        rintro y ⟨a, b, ha, hb, rfl⟩
        by_cases hy0 : a + b * x = 0
        · simpa [hy0] using (show (0 : ℝ) ∈
            ({y | ∃ a b : ℝ, a ∈ K ∧ b ∈ K ∧ y = a + b * x} : Set ℝ) from
              ⟨0, 0, zero_mem K, zero_mem K, by simp⟩)
        · by_cases hD : a ^ 2 - b ^ 2 * x ^ 2 = 0
          · have hprod : (a - b * x) * (a + b * x) = 0 := by
              calc
                (a - b * x) * (a + b * x) = a ^ 2 - b ^ 2 * x ^ 2 := by ring
                _ = 0 := hD
            have hamul : a - b * x = 0 := by
              exact (mul_eq_zero.mp hprod).resolve_right hy0
            have haeq : a = b * x := by linarith
            have hbx : b * x ≠ 0 := by
              intro h
              apply hy0
              rw [haeq, h]
              ring
            have hx0 : x ≠ 0 := by
              intro hx
              apply hbx
              rw [hx, mul_zero]
            have hden : 2 * b * x ^ 2 ≠ 0 := by
              have hb0 : b ≠ 0 := left_ne_zero_of_mul hbx
              exact mul_ne_zero (mul_ne_zero (by norm_num) hb0) (pow_ne_zero 2 hx0)
            refine ⟨0, (2 * b * x ^ 2)⁻¹, zero_mem K, ?_, ?_⟩
            · exact inv_mem (mul_mem (mul_mem (SubfieldClass.ratCast_mem K (2 : ℚ)) hb) hx2)
            · rw [haeq]
              field_simp [hden, hbx]
              ring
          · have hDmem : a ^ 2 - b ^ 2 * x ^ 2 ∈ K := by
              exact sub_mem (pow_mem ha 2) (mul_mem (pow_mem hb 2) hx2)
            refine ⟨a * (a ^ 2 - b ^ 2 * x ^ 2)⁻¹,
              -b * (a ^ 2 - b ^ 2 * x ^ 2)⁻¹, ?_, ?_, ?_⟩
            · exact mul_mem ha (inv_mem hDmem)
            · exact mul_mem (neg_mem hb) (inv_mem hDmem)
            · field_simp [hD, hy0]
              ring }
  exact (show K ⊔ IntermediateField.adjoin ℚ {x} ≤ S from by
    refine sup_le ?_ ?_
    · intro z hz
      exact ⟨z, 0, hz, zero_mem K, by simp⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨0, 1, zero_mem K, one_mem K, by simp⟩) hy

/-- **Square-class descent.**  If `0 < r` is rational with
`√r ∈ ℚ(√c₀, …, √c_{n-1})`, then `r = s² · ∏_{j ∈ T} c j` for some
rational `s` and some `T ⊆ {0, …, n-1}`.

Induction on `n`.  Base: `√r ∈ ⊥` means `√r` is rational, so `r` is a
rational square (`T = ∅`).  Step: write `√r = a + b·√(c n)` with
`a, b ∈ sqrtTower c n` (`mem_sup_adjoin_sq`, `sqrtTower_succ`).
* If `√(c n) ∈ sqrtTower c n`, the sup collapses and the inductive
  hypothesis applies directly.
* Otherwise, squaring gives `r = (a² + b²·c n) + (2ab)·√(c n)`; if
  `ab ≠ 0` we could solve for `√(c n)` over `sqrtTower c n`,
  contradiction.  If `b = 0`, apply the IH to `r`.  If `a = 0`, then
  `√(r·c n) = b·c n ∈ sqrtTower c n`, the IH applies to `r·c n > 0`
  giving `r·c n = s²·∏_{T} c j`, whence
  `r = (s/c n)²·∏_{insert n T} c j`. -/
theorem squareClass_of_sqrt_mem (c : ℕ → ℚ) (hc : ∀ j, 0 < c j) :
    ∀ n, ∀ r : ℚ, 0 < r → (Real.sqrt r : ℝ) ∈ sqrtTower c n →
      ∃ (T : Finset ℕ) (s : ℚ), ↑T ⊆ Set.Iio n ∧
        r = s ^ 2 * ∏ j ∈ T, c j := by
  intro n
  induction n with
  | zero =>
      intro r hr hmem
      rw [sqrtTower_zero, IntermediateField.mem_bot] at hmem
      obtain ⟨s, hs⟩ := hmem
      have h2 : (s : ℚ) ^ 2 = r := by
        have hcast : ((s : ℝ)) ^ 2 = ((r : ℝ)) := by
          rw [show ((s : ℚ) : ℝ) = Real.sqrt r from by exact_mod_cast hs,
            Real.sq_sqrt (by positivity)]
        exact_mod_cast hcast
      exact ⟨∅, s, by simp, by rw [Finset.prod_empty, mul_one, h2]⟩
  | succ n ih =>
      intro r hr hmem
      rw [sqrtTower_succ] at hmem
      by_cases hcn : Real.sqrt (c n) ∈ sqrtTower c n
      · -- the sup collapses into `sqrtTower c n`
        have hcollapse : sqrtTower c n ⊔ IntermediateField.adjoin ℚ {Real.sqrt (c n)}
            = sqrtTower c n := by
          rw [sup_eq_left]
          exact IntermediateField.adjoin_le_iff.mpr (by simpa using hcn)
        rw [hcollapse] at hmem
        obtain ⟨T, s, hT, heq⟩ := ih r hr hmem
        exact ⟨T, s, hT.trans (Set.Iio_subset_Iio n.le_succ), heq⟩
      · have hx2 : (Real.sqrt (c n)) ^ 2 ∈ sqrtTower c n := by
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ (c n : ℝ) by exact_mod_cast (hc n).le)]
          exact SubfieldClass.ratCast_mem _ (c n)
        obtain ⟨a, b, ha, hb, heq⟩ := mem_sup_adjoin_sq hx2 hmem
        have hsq : (r : ℝ) =
            a ^ 2 + b ^ 2 * (c n : ℝ) + 2 * a * b * Real.sqrt (c n) := by
          calc
            (r : ℝ) = (Real.sqrt (r : ℝ)) ^ 2 := by
              rw [Real.sq_sqrt (show 0 ≤ (r : ℝ) by exact_mod_cast hr.le)]
            _ = (a + b * Real.sqrt (c n)) ^ 2 := by rw [heq]
            _ = a ^ 2 + b ^ 2 * (c n : ℝ) + 2 * a * b * Real.sqrt (c n) := by
              have hsqrtc_sq : (Real.sqrt (c n) : ℝ) ^ 2 = (c n : ℝ) := by
                rw [Real.sq_sqrt (show (0 : ℝ) ≤ (c n : ℝ) by exact_mod_cast (hc n).le)]
              nlinarith
        have hcross_eq :
            2 * a * b * Real.sqrt (c n) =
              (r : ℝ) - a ^ 2 - b ^ 2 * (c n : ℝ) := by
          linarith
        have hcross_mem : 2 * a * b * Real.sqrt (c n) ∈ sqrtTower c n := by
          rw [hcross_eq]
          exact sub_mem
            (sub_mem (SubfieldClass.ratCast_mem _ r) (pow_mem ha 2))
            (mul_mem (pow_mem hb 2) (SubfieldClass.ratCast_mem _ (c n)))
        by_cases hab : a * b = 0
        · rcases mul_eq_zero.mp hab with ha0 | hb0
          · have hsqrt_mul_mem : Real.sqrt ((r * c n : ℚ) : ℝ) ∈ sqrtTower c n := by
              have hsqrt_mul :
                  Real.sqrt ((r * c n : ℚ) : ℝ) =
                    Real.sqrt (r : ℝ) * Real.sqrt (c n : ℝ) := by
                rw [Rat.cast_mul]
                exact Real.sqrt_mul (show 0 ≤ (r : ℝ) by exact_mod_cast hr.le) (c n : ℝ)
              rw [hsqrt_mul, heq, ha0, zero_add]
              convert mul_mem hb hx2 using 1
              ring
            obtain ⟨T, s, hT, hmul⟩ :=
              ih (r * c n) (mul_pos hr (hc n)) hsqrt_mul_mem
            have hnT : n ∉ T := by
              intro hn
              have := hT hn
              simp at this
            refine ⟨insert n T, s / c n, ?_, ?_⟩
            · intro j hj
              rw [Finset.mem_coe, Finset.mem_insert] at hj
              rw [Set.mem_Iio]
              rcases hj with rfl | hj
              · omega
              · exact Nat.lt_trans (hT hj) n.lt_succ_self
            · have hcn0 : c n ≠ 0 := (hc n).ne'
              rw [Finset.prod_insert hnT]
              field_simp [hcn0]
              nlinarith [hmul]
          · have hsqrt_mem : (Real.sqrt r : ℝ) ∈ sqrtTower c n := by
              rw [heq, hb0, zero_mul, add_zero]
              exact ha
            obtain ⟨T, s, hT, hres⟩ := ih r hr hsqrt_mem
            exact ⟨T, s, hT.trans (Set.Iio_subset_Iio n.le_succ), hres⟩
        · have hcoef_mem : 2 * a * b ∈ sqrtTower c n := by
            exact mul_mem (mul_mem (SubfieldClass.ratCast_mem _ (2 : ℚ)) ha) hb
          have hcoef_ne : 2 * a * b ≠ 0 := by
            have h2ab : (2 : ℝ) * (a * b) ≠ 0 := mul_ne_zero (by norm_num) hab
            convert h2ab using 1
            ring
          have hsqrt_mem : Real.sqrt (c n) ∈ sqrtTower c n := by
            have hmem' := mul_mem (inv_mem hcoef_mem) hcross_mem
            have hEq :
                (2 * a * b)⁻¹ * (2 * a * b * Real.sqrt (c n)) = Real.sqrt (c n) := by
              rw [← mul_assoc, inv_mul_cancel₀ hcoef_ne, one_mul]
            rw [← hEq]
            exact hmem'
          exact (hcn hsqrt_mem).elim

/-- [valuation parity]  A prime is not a rational square times a product
of distinct other primes: compare `padicValRat (q3 n)` of both sides —
odd on the left, even on the right (`s²` contributes evenly, the distinct
primes contribute `0`). -/
theorem q3_not_squareClass (n : ℕ) (T : Finset ℕ) (hT : ↑T ⊆ Set.Iio n)
    (s : ℚ) : ((q3 n : ℚ)) ≠ s ^ 2 * ∏ j ∈ T, ((q3 j : ℚ)) := by
  sorry

/-- `√(q3 n)` does not lie in the tower generated by the earlier square
roots (descent + valuation parity). -/
theorem sqrt_q3_notMem_tower (n : ℕ) :
    (Real.sqrt (q3 n) : ℝ) ∉ sqrtTower (fun j => (q3 j : ℚ)) n := by
  intro hmem
  obtain ⟨T, s, hT, heq⟩ :=
    squareClass_of_sqrt_mem (fun j => (q3 j : ℚ))
      (fun j => by exact_mod_cast (q3_spec j).1.pos) n (q3 n)
      (by exact_mod_cast (q3_spec n).1.pos) hmem
  exact q3_not_squareClass n T hT s heq

/-- [tower induction]  The real multiquadratic tower has full degree:
each step adjoins a root of the irreducible (no root, degree 2)
polynomial `X² - q3 n`. -/
theorem sqrtTower_finrank (n : ℕ) :
    Module.finrank ℚ (sqrtTower (fun j => (q3 j : ℚ)) n) = 2 ^ n := by
  sorry

/-- The multiquadratic CM field (must match `Framework.lean` verbatim). -/
noncomputable def Kf (g : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g))

/-- [complexify and adjoin `i`]  `Kf g` has degree `2^(g+1)`:
the `ℚ`-algebra map `Complex.ofRealHom` carries `sqrtTower` to an
isomorphic intermediate field of `ℂ` generated by the `(√q3 j : ℂ)`
(`IntermediateField.adjoin_map`); `Kf g` is its sup with `ℚ(i)`
(`adjoin_insert`), and `X² + 1` has no root in the (real-valued) image,
so the degree doubles once more. -/
theorem Kf_finrank (g : ℕ) : Module.finrank ℚ (Kf g) = 2 ^ (g + 1) := by
  sorry

end Erdos
