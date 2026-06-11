import Mathlib

/-!
# Square-class descent for iterated real quadratic extensions

Kernel for the multiquadratic-degree theorem (`Kf_finrank` in the Erdős
unit-distance framework): if `r > 0` is rational and `√r` lies in
`ℚ(√c₀, …, √c_{n-1}) ⊆ ℝ` (with `c_j > 0` rational), then `r` is a
rational square times a product of a subset of the `c_j`.

Structure:
* `mem_sup_adjoin_sq`: if `x² ∈ K` then every element of `K ⊔ ℚ(x)` is
  `a + b·x` with `a, b ∈ K` (the set of such elements is itself an
  intermediate field — closure under inverse is elementary casework).
* `squareClass_of_sqrt_mem`: the descent induction.
-/

namespace Erdos

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
        sorry

end Erdos
