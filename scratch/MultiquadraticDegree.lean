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
  classical
  intro h
  have hp : (q3 n).Prime := (q3_spec n).1
  haveI : Fact (q3 n).Prime := ⟨hp⟩
  have hqn0 : (q3 n : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs0 : s ≠ 0 := by
    intro hs
    apply hqn0
    simpa [hs] using h
  have hval_factor :
      ∀ j ∈ T, padicValRat (q3 n) (q3 j : ℚ) = 0 := by
    intro j hj
    have hjn : j < n := hT (by simpa using hj)
    have hneq : q3 n ≠ q3 j := by
      exact ne_of_gt (q3_strictMono hjn)
    haveI : Fact (q3 j).Prime := ⟨(q3_spec j).1⟩
    rw [padicValRat.of_nat, padicValNat_primes hneq]
    norm_num
  have hprod0 : (∏ j ∈ T, (q3 j : ℚ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      exact_mod_cast (q3_spec j).1.ne_zero)
  have hprodVal_aux :
      ∀ U : Finset ℕ, ↑U ⊆ Set.Iio n →
        padicValRat (q3 n) (∏ j ∈ U, (q3 j : ℚ)) = 0 := by
    intro U
    refine Finset.induction_on U ?base ?step
    · intro hU
      simp [padicValRat.one]
    · intro a U haU ih hU
      have hqa0 : (q3 a : ℚ) ≠ 0 := by exact_mod_cast (q3_spec a).1.ne_zero
      have hUprod0 : (∏ j ∈ U, (q3 j : ℚ)) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr (by
          intro j hj
          exact_mod_cast (q3_spec j).1.ne_zero)
      have ha_lt : a < n := hU (Finset.mem_insert_self a U)
      have hneq : q3 n ≠ q3 a := by
        exact ne_of_gt (q3_strictMono ha_lt)
      haveI : Fact (q3 a).Prime := ⟨(q3_spec a).1⟩
      have hvala : padicValRat (q3 n) (q3 a : ℚ) = 0 := by
        rw [padicValRat.of_nat, padicValNat_primes hneq]
        norm_num
      have ih' : padicValRat (q3 n) (∏ j ∈ U, (q3 j : ℚ)) = 0 := by
        exact ih (by
          intro j hj
          exact hU (by simp [hj]))
      rw [Finset.prod_insert haU, padicValRat.mul hqa0 hUprod0,
        hvala, ih', add_zero]
  have hprodVal : padicValRat (q3 n) (∏ j ∈ T, (q3 j : ℚ)) = 0 :=
    hprodVal_aux T hT
  have hval := congrArg (padicValRat (q3 n)) h
  rw [padicValRat.self hp.one_lt, padicValRat.mul (pow_ne_zero 2 hs0) hprod0,
    padicValRat.pow hs0, hprodVal, add_zero] at hval
  omega

private theorem finrank_adjoin_simple_eq_two_of_sq_mem_notMem
    {E : Type*} [Field E] [Algebra ℚ E] (K : IntermediateField ℚ E) {x : E}
    (hx2 : x ^ 2 ∈ K) (hxK : x ∉ K) :
    Module.finrank K (IntermediateField.adjoin K {x}) = 2 := by
  have hx2_int : IsIntegral K (x ^ 2) := by
    rw [← show algebraMap K E ⟨x ^ 2, hx2⟩ = x ^ 2 from rfl]
    exact isIntegral_algebraMap (R := K) (A := E) (x := ⟨x ^ 2, hx2⟩)
  have hx_int : IsIntegral K x := IsIntegral.of_pow (by norm_num : 0 < 2) hx2_int
  have hfin := IntermediateField.adjoin.finrank hx_int
  have hle : (minpoly K x).natDegree ≤ 2 := by
    let a : K := ⟨x ^ 2, hx2⟩
    have hroot :
        Polynomial.aeval x ((Polynomial.X : Polynomial K) ^ 2 - Polynomial.C a) = 0 := by
      simp [a]
    have hdvd : minpoly K x ∣ ((Polynomial.X : Polynomial K) ^ 2 - Polynomial.C a) :=
      minpoly.dvd K x hroot
    have hpoly_ne : ((Polynomial.X : Polynomial K) ^ 2 - Polynomial.C a) ≠ 0 := by
      intro hzero
      have hdeg := congrArg Polynomial.natDegree hzero
      norm_num at hdeg
    have hdeg_poly :
        (((Polynomial.X : Polynomial K) ^ 2 - Polynomial.C a)).natDegree = 2 := by
      simp
    exact (Polynomial.natDegree_le_of_dvd hdvd hpoly_ne).trans_eq hdeg_poly
  have hpos : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos hx_int
  have hne1 : (minpoly K x).natDegree ≠ 1 := by
    intro hdeg1
    have hfin1 : Module.finrank K (IntermediateField.adjoin K {x}) = 1 := by
      simpa [hfin] using hdeg1
    have hxbot : x ∈ (⊥ : IntermediateField K E) :=
      (IntermediateField.finrank_adjoin_simple_eq_one_iff).mp hfin1
    rw [IntermediateField.mem_bot] at hxbot
    obtain ⟨y, hy⟩ := hxbot
    apply hxK
    rw [← hy]
    exact y.2
  omega

private theorem finrank_sup_adjoin_simple_eq_mul_two
    {E : Type*} [Field E] [Algebra ℚ E] (K : IntermediateField ℚ E) {x : E}
    (hx2 : x ^ 2 ∈ K) (hxK : x ∉ K) :
    Module.finrank ℚ ((K ⊔ IntermediateField.adjoin ℚ ({x} : Set E)) :
      IntermediateField ℚ E) =
      Module.finrank ℚ K * 2 := by
  let L : IntermediateField K E := IntermediateField.adjoin K {x}
  have hL :
      L.restrictScalars ℚ = K ⊔ IntermediateField.adjoin ℚ ({x} : Set E) := by
    simpa [L] using (IntermediateField.restrictScalars_adjoin_eq_sup (F := ℚ) K ({x} : Set E))
  have hfinL : Module.finrank K L = 2 :=
    finrank_adjoin_simple_eq_two_of_sq_mem_notMem K hx2 hxK
  let e : (L.restrictScalars ℚ) ≃ₗ[ℚ] L :=
    { toFun := fun y => ⟨(y : E), y.2⟩
      invFun := fun y => ⟨(y : E), y.2⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl
      map_add' := fun y z => rfl
      map_smul' := fun q y => rfl }
  calc
    Module.finrank ℚ ((K ⊔ IntermediateField.adjoin ℚ ({x} : Set E)) :
      IntermediateField ℚ E)
        = Module.finrank ℚ (L.restrictScalars ℚ) := by rw [hL]
    _ = Module.finrank ℚ L := e.finrank_eq
    _ = Module.finrank ℚ K * Module.finrank K L := by
      rw [Module.finrank_mul_finrank]
    _ = Module.finrank ℚ K * 2 := by rw [hfinL]

/-- `√(q3 n)` does not lie in the tower generated by the earlier square
roots (descent + valuation parity). -/
theorem sqrt_q3_notMem_tower (n : ℕ) :
    (Real.sqrt (q3 n) : ℝ) ∉ sqrtTower (fun j => (q3 j : ℚ)) n := by
  intro hmem
  obtain ⟨T, s, hT, heq⟩ :=
    squareClass_of_sqrt_mem (fun j => (q3 j : ℚ))
      (fun j => by
        show (0 : ℚ) < (q3 j : ℚ)
        exact_mod_cast (q3_spec j).1.pos) n (q3 n)
      (by exact_mod_cast (q3_spec n).1.pos) hmem
  exact q3_not_squareClass n T hT s heq

/-- [tower induction]  The real multiquadratic tower has full degree:
each step adjoins a root of the irreducible (no root, degree 2)
polynomial `X² - q3 n`. -/
theorem sqrtTower_finrank (n : ℕ) :
    Module.finrank ℚ (sqrtTower (fun j => (q3 j : ℚ)) n) = 2 ^ n := by
  induction n with
  | zero =>
      rw [sqrtTower_zero]
      exact IntermediateField.finrank_bot
  | succ n ih =>
      rw [sqrtTower_succ]
      have hx2 :
          (Real.sqrt ((q3 n : ℚ) : ℝ)) ^ 2 ∈
            sqrtTower (fun j => (q3 j : ℚ)) n := by
        rw [Real.sq_sqrt]
        · exact SubfieldClass.ratCast_mem _ (q3 n : ℚ)
        · exact_mod_cast (q3_spec n).1.pos.le
      have hxK :
          Real.sqrt ((q3 n : ℚ) : ℝ) ∉
            sqrtTower (fun j => (q3 j : ℚ)) n := by
        simpa using sqrt_q3_notMem_tower n
      rw [finrank_sup_adjoin_simple_eq_mul_two
        (sqrtTower (fun j => (q3 j : ℚ)) n) hx2 hxK, ih]
      rw [pow_succ]

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
  let φ : ℝ →ₐ[ℚ] ℂ := Complex.ofRealHom.toRatAlgHom
  let Kr : IntermediateField ℚ ℝ := sqrtTower (fun j => (q3 j : ℚ)) g
  let Kc : IntermediateField ℚ ℂ := Kr.map φ
  have hKc_fin : Module.finrank ℚ Kc = 2 ^ g := by
    let e : Kr.toSubalgebra ≃ₐ[ℚ] Kc.toSubalgebra :=
      (Kr.toSubalgebra.equivMapOfInjective φ φ.injective).trans
        (Subalgebra.equivOfEq _ _ (by dsimp [Kc]))
    have hfin : Module.finrank ℚ Kc.toSubalgebra = Module.finrank ℚ Kr.toSubalgebra :=
      e.toLinearEquiv.finrank_eq.symm
    let eKc : Kc.toSubalgebra ≃ₗ[ℚ] Kc :=
      { toFun := fun y => ⟨(y : ℂ), y.2⟩
        invFun := fun y => ⟨(y : ℂ), y.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl
        map_add' := fun y z => rfl
        map_smul' := fun q y => rfl }
    let eKr : Kr.toSubalgebra ≃ₗ[ℚ] Kr :=
      { toFun := fun y => ⟨(y : ℝ), y.2⟩
        invFun := fun y => ⟨(y : ℝ), y.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl
        map_add' := fun y z => rfl
        map_smul' := fun q y => rfl }
    calc
      Module.finrank ℚ Kc = Module.finrank ℚ Kc.toSubalgebra := eKc.finrank_eq.symm
      _ = Module.finrank ℚ Kr.toSubalgebra := hfin
      _ = Module.finrank ℚ Kr := eKr.finrank_eq
      _ = 2 ^ g := by
        dsimp [Kr]
        rw [sqrtTower_finrank]
  have hKc :
      Kc =
        IntermediateField.adjoin ℚ
          ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g) := by
    dsimp [Kc, Kr]
    rw [sqrtTower, IntermediateField.adjoin_map]
    congr 1
    ext z
    constructor
    · rintro ⟨x, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, by simp [φ, RingHom.toRatAlgHom_apply]⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Real.sqrt (q3 j : ℚ), ⟨j, hj, rfl⟩, by
        simp [φ, RingHom.toRatAlgHom_apply]⟩
  have hKf :
      Kf g = Kc ⊔ IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ) := by
    rw [hKc, Kf, ← IntermediateField.adjoin_union]
    congr 1
    ext z
    constructor
    · intro hz
      rw [Set.mem_insert_iff] at hz
      rw [Set.mem_union, Set.mem_singleton_iff]
      tauto
    · intro hz
      rw [Set.mem_union, Set.mem_singleton_iff] at hz
      rw [Set.mem_insert_iff]
      tauto
  have hI2 : Complex.I ^ 2 ∈ Kc := by
    rw [sq, Complex.I_mul_I]
    exact neg_mem (one_mem Kc)
  have hInot : Complex.I ∉ Kc := by
    intro hI
    dsimp [Kc] at hI
    rw [IntermediateField.mem_map] at hI
    obtain ⟨y, hy, hyI⟩ := hI
    have him := congrArg Complex.im hyI
    simp [φ, RingHom.toRatAlgHom_apply] at him
  rw [hKf, finrank_sup_adjoin_simple_eq_mul_two Kc hI2 hInot, hKc_fin]
  rw [pow_succ]

end Erdos
