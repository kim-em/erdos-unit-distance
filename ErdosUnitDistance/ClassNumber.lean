/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Ideal counting, class numbers and unit square classes

In any number field: the count of ideals of bounded norm (by an
injective encoding into bounded-product tuples), the resulting class
number bound `h ≤ |d|·4^deg`, and the index of squares in the unit
group.
-/

open scoped Classical

namespace Erdos

/-! ## Class number and unit bounds (abstract) -/

/-- The set of `n`-tuples of positive naturals with real product at most `X`. -/
def prodLeTuples (n : ℕ) (X : ℝ) : Set (Fin n → ℕ) :=
  {d : Fin n → ℕ | (∀ i, 0 < d i) ∧ (∏ i, (d i : ℝ)) ≤ X}

/-
[elementary] The tuple set is finite.
-/
theorem prodLeTuples_finite (n : ℕ) (X : ℝ) : (prodLeTuples n X).Finite := by
  refine' Set.Finite.subset ( Set.finite_Icc ( 1 : Fin n → ℕ ) ( fun _ => ⌊X⌋₊ ) ) _;
  intro d hd;
  exact ⟨ fun i => Nat.one_le_of_lt ( hd.1 i ), fun i => Nat.le_floor <| le_trans ( mod_cast Finset.single_le_prod' ( fun a _ => Nat.one_le_of_lt ( hd.1 a ) ) ( Finset.mem_univ i ) ) hd.2 ⟩

/-
[elementary] `∑_{j=1}^{N} 1/j² ≤ 2` by telescoping `1/j² ≤ 1/(j(j-1))`.
-/
theorem sum_one_div_sq_le_two (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  -- We'll use the fact that $\sum_{j=1}^N \frac{1}{j^2}$ is a partial sum of a convergent series.
  have h_sum_converge : ∀ N : ℕ, ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / j^2 ≤ Real.pi^2 / 6 := by
    exact fun N => by simpa using sum_le_hasSum ( Finset.Icc 1 N ) ( fun n _hn => by positivity ) ( by simpa using hasSum_zeta_two ) ;
  -- We'll use the fact that $\pi \approx 3.14$ to show that $\frac{\pi^2}{6} < 2$.
  have h_pi_approx : Real.pi < 3.4 := by
    pi_upper_bound [ 7 / 5 ];
  exact le_trans ( h_sum_converge N ) ( by norm_num1 at *; nlinarith [ Real.pi_gt_three ] )

/-
[elementary] The number of `n`-tuples of positive naturals with product at
most `X` is at most `X² · 2ⁿ`.  Proof by induction on `n`: split off the last
coordinate `j ∈ {1,…,⌊X⌋}`, bound the rest by `(X/j)² · 2ⁿ` via the inductive
hypothesis, and sum using `sum_one_div_sq_le_two`.
-/
theorem prodLeTuples_ncard_le (n : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((prodLeTuples n X).ncard : ℝ) ≤ X ^ 2 * 2 ^ n := by
  -- Apply induction on $n$.
  induction' n with n ih generalizing X;
  · norm_num [ prodLeTuples ];
    norm_num [ Set.ncard_univ, hX ];
    linarith [ le_abs_self X ];
  · -- By definition of `prodLeTuples`, we have:
    have h_def : prodLeTuples (n + 1) X = ⋃ j ∈ Finset.Icc 1 (Nat.floor X), (fun e => Fin.snoc e j) '' (prodLeTuples n (X / j)) := by
      ext d; simp [prodLeTuples];
      constructor <;> intro h;
      · refine' ⟨ d ( Fin.last n ), ⟨ h.1 _, Nat.le_floor <| _ ⟩, Fin.init d, _, _ ⟩ <;> simp_all +decide [ Fin.prod_univ_castSucc ];
        · exact le_trans ( le_mul_of_one_le_left ( Nat.cast_nonneg _ ) ( mod_cast Finset.prod_pos fun _ _ => h.1 _ ) ) h.2;
        · exact ⟨ fun i => h.1 _, by rw [ le_div_iff₀ ( Nat.cast_pos.mpr ( h.1 _ ) ) ] ; simpa [ Fin.prod_univ_castSucc, Fin.init ] using h.2 ⟩;
      · rcases h with ⟨ i, hi, x, hx, rfl ⟩ ; simp_all +decide [ Fin.prod_univ_castSucc, Fin.snoc ];
        exact ⟨ fun j => by cases j using Fin.lastCases <;> aesop, by rw [ le_div_iff₀ ( Nat.cast_pos.mpr hi.1 ) ] at hx; linarith ⟩;
    -- Applying the induction hypothesis to each term in the union.
    have h_ind : (prodLeTuples (n + 1) X).ncard ≤ ∑ j ∈ Finset.Icc 1 (Nat.floor X), (prodLeTuples n (X / j)).ncard := by
      rw [h_def];
      induction' ( Finset.Icc 1 ⌊X⌋₊ : Finset ℕ ) using Finset.induction <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ];
      exact le_trans ( Set.ncard_union_le _ _ ) ( add_le_add ( by rw [ Set.ncard_image_of_injective _ fun x y hxy => by simpa [ Fin.snoc ] using hxy ] ) ‹_› );
    refine' le_trans ( Nat.cast_le.mpr h_ind ) _;
    push_cast [ pow_succ' ];
    refine' le_trans ( Finset.sum_le_sum fun i hi => ih <| _ ) _;
    · exact one_le_div ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hi |>.1 ) |>.2 <| Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hi |>.2 );
    · -- We'll use the fact that $\sum_{j=1}^{\lfloor X \rfloor} \frac{1}{j^2} \leq 2$.
      have h_sum : ∑ j ∈ Finset.Icc 1 (Nat.floor X), (1 / (j : ℝ)) ^ 2 ≤ 2 := by
        convert sum_one_div_sq_le_two ⌊X⌋₊ using 1;
        norm_num;
      convert mul_le_mul_of_nonneg_right h_sum ( show 0 ≤ X ^ 2 * 2 ^ n by positivity ) using 1 <;> ring;
      simp +decide only [Finset.mul_sum _ _ _, Finset.sum_mul]

/-! ### Encoding ideals as tuples (for the Rankin-style ideal count)

We encode a nonzero ideal `I` of `𝓞 F` as an `n`-tuple of positive naturals
(`n = [F:ℚ]`) whose product is at most `absNorm I`, injectively.  For a nonzero
prime `P`, `ratBelow P` is the rational prime below `P` and `primeCoord P` is the
index of `P` among the (at most `n`) primes above that rational prime.  The
`i`-th coordinate of the encoding multiplies `(ratBelow P) ^ (mult of P in I)`
over all prime factors `P` of `I` with `primeCoord P = i`. -/
section RankinCount

open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The rational prime below a prime ideal `P` of `𝓞 F`. -/
def ratBelow (P : Ideal (𝓞 F)) : ℕ := Ideal.absNorm (Ideal.under ℤ P)

/-- The coordinate (index in `Fin [F:ℚ]`) assigned to a prime ideal `P`: its
position in the list of primes above the rational prime below `P`. -/
def primeCoord (P : Ideal (𝓞 F)) : ℕ :=
  (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList.idxOf P

/-- The `i`-th coordinate of the tuple encoding the ideal `I`. -/
def encodeIdeal (I : Ideal (𝓞 F)) (i : Fin (Module.finrank ℚ F)) : ℕ :=
  ∏ P ∈ (normalizedFactors I).toFinset.filter (fun P => primeCoord F P = i.val),
    (ratBelow F P) ^ ((normalizedFactors I).count P)

/-
[foundational] The rational prime below a nonzero prime ideal is prime.
-/
theorem ratBelow_prime {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (ratBelow F P).Prime := by
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.span {g} = Ideal.under ℤ P ∧ g ≠ 0 ∧ Prime g := by
    obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.span {g} = Ideal.under ℤ P ∧ g ≠ 0 := by
      have h_nonzero : Ideal.under ℤ P ≠ ⊥ := Ideal.under_ne_bot (A := ℤ) hP0
      obtain ⟨ g, hg ⟩ := IsPrincipalIdealRing.principal ( under ℤ P );
      exact ⟨ g, hg.symm, by aesop ⟩;
    have h_prime : Ideal.IsPrime (Ideal.span {g}) := by
      grind +suggestions;
    rw [ Ideal.span_singleton_prime ] at h_prime <;> aesop;
  convert Int.prime_iff_natAbs_prime.mp hg.2.2 using 1;
  convert Ideal.absNorm_span_singleton g;
  · exact hg.1.symm ▸ rfl;
  · simp +decide [ Algebra.norm ]

/-
[foundational] `under ℤ P` is a nonzero maximal ideal of `ℤ`.
-/
theorem under_ne_bot {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Ideal.under ℤ P ≠ ⊥ :=
  Ideal.under_ne_bot (A := ℤ) hP0

/-
[foundational] The rational prime below `P` is at most `absNorm P`.
-/
theorem ratBelow_le_absNorm {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ratBelow F P ≤ Ideal.absNorm P := by
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.span {g} = Ideal.under ℤ P ∧ g.natAbs.Prime := by
    have hJ_prime : Ideal.IsPrime (Ideal.under ℤ P) := by
      grind +suggestions;
    have hJ_nonzero : Ideal.under ℤ P ≠ ⊥ := under_ne_bot F hP hP0
    have hJ_principal : ∃ g : ℤ, Ideal.under ℤ P = Ideal.span {g} :=
      Submodule.IsPrincipal.principal (Ideal.under ℤ P)
    obtain ⟨ g, hg ⟩ := hJ_principal; use g; simp_all +decide [ Ideal.span_singleton_prime ] ;
    exact Int.prime_iff_natAbs_prime.mp hJ_prime;
  have h_norm : absNorm P = Int.natAbs g ^ (Ideal.inertiaDeg (Ideal.span {g}) P) := by
    convert Ideal.absNorm_eq_pow_inertiaDeg P ( show Prime g from ?_ ) using 1;
    · constructor ; aesop;
    · rw [ Int.prime_iff_natAbs_prime ] ; aesop;
  have h_ratBelow : ratBelow F P = Int.natAbs g := by
    have := congr_arg ( fun I => Ideal.absNorm I ) hg.1; norm_num at this; aesop;
  rw [h_norm];
  refine' le_trans _ ( Nat.pow_le_pow_right hg.2.pos ( show 1 ≤ Ideal.inertiaDeg ( Ideal.span { g } ) P from _ ) );
  · norm_num [ h_ratBelow ];
  · contrapose! hP0; aesop

/-
[foundational] `P` belongs to the finite set of primes above the rational
prime below it.
-/
theorem mem_primesOverFinset_under {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P ∈ IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F) := by
  -- Since P is a prime ideal in O_F, we have that P is maximal in O_F.
  have hP_max : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
  rw [ IsDedekindDomain.mem_primesOverFinset_iff ];
  · constructor;
    · exact hP;
    · constructor;
      rfl;
  · exact under_ne_bot F hP hP0

/-
[foundational] The coordinate of a nonzero prime ideal is `< [F:ℚ]`.
-/
theorem primeCoord_lt {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    primeCoord F P < Module.finrank ℚ F := by
  refine' lt_of_lt_of_le _ _;
  exact ( IsDedekindDomain.primesOverFinset ( Ideal.under ℤ P ) ( 𝓞 F ) ).card;
  · convert List.idxOf_lt_length_iff.mpr _;
    · simp +decide;
    · infer_instance;
    · exact Finset.mem_toList.mpr ( mem_primesOverFinset_under F hP hP0 );
  · convert Ideal.card_primesOverFinset_le_finrank ( 𝓞 F ) ℚ F ( under_ne_bot F hP hP0 ) using 1;
    exact Ideal.IsPrime.isMaximal (IsPrime.under ℤ P) (under_ne_bot F hP hP0)

/-
[foundational] `ratBelow` injectivity: equal `ratBelow` means the primes lie
over the same rational prime, hence have the same `IsDedekindDomain.primesOverFinset`.
-/
theorem under_eq_of_ratBelow_eq {P Q : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) (hr : ratBelow F P = ratBelow F Q) :
    Ideal.under ℤ P = Ideal.under ℤ Q := by
  have hr' : Ideal.absNorm (Ideal.under ℤ P) = Ideal.absNorm (Ideal.under ℤ Q) := by
    exact hr;
  have hr'' : ∀ {J : Ideal ℤ}, J ≠ ⊥ → J.IsPrime → J = Ideal.span {(Ideal.absNorm J : ℤ)} := by
    simp_all +decide;
  rw [ hr'' ( under_ne_bot F hP hP0 ) ( Ideal.isPrime_iff.mpr <| by
    simp +decide [ Ideal.mem_comap, hP.ne_top ];
    exact fun { x y } hxy => hP.mem_or_mem hxy ), hr'' ( under_ne_bot F hQ hQ0 ) ( Ideal.isPrime_iff.mpr <| by
    simp +decide [ Ideal.under ];
    exact ⟨ hQ.ne_top, fun { x y } hxy => hQ.mem_or_mem <| by simpa using hxy ⟩ ), hr' ]

/-
[foundational] Two nonzero primes over the same rational prime with the same
coordinate are equal.
-/
theorem prime_eq_of_coord_eq {P Q : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) (hr : ratBelow F P = ratBelow F Q)
    (hc : primeCoord F P = primeCoord F Q) : P = Q := by
  have h_eq : P ∈ (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList ∧ Q ∈ (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList := by
    have := mem_primesOverFinset_under F hP hP0; have := mem_primesOverFinset_under F hQ hQ0; simp_all +decide [ IsDedekindDomain.primesOverFinset ] ;
    grind +suggestions;
  have h_eq : List.Nodup (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList := by
    exact Finset.nodup_toList _;
  have h_eq : List.idxOf P (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList = List.idxOf Q (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList := by
    convert hc using 1;
    unfold primeCoord;
    rw [ under_eq_of_ratBelow_eq F hP hP0 hQ hQ0 hr ];
  have h_eq : ∀ {l : List (Ideal (𝓞 F))}, List.Nodup l → ∀ {x y : Ideal (𝓞 F)}, x ∈ l → y ∈ l → List.idxOf x l = List.idxOf y l → x = y := by
    intros l hl x y hx hy hxy; induction l <;> simp_all +decide [ List.idxOf_cons ] ;
    grind;
  exact h_eq ‹_› ( by tauto ) ( by tauto ) ( by tauto )

/-
The factors in `normalizedFactors I` are nonzero primes.
-/
theorem isPrime_of_mem_normalizedFactors {I P : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (hP : P ∈ normalizedFactors I) : P.IsPrime ∧ P ≠ ⊥ := by
  grind +suggestions

/-
[foundational] Each coordinate of the encoding of a nonzero ideal is positive.
-/
theorem encodeIdeal_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (i : Fin (Module.finrank ℚ F)) : 0 < encodeIdeal F I i := by
  refine' Finset.prod_pos _;
  simp +zetaDelta at *;
  exact fun P hP hP' => pow_pos ( Nat.Prime.pos ( ratBelow_prime F ( isPrime_of_mem_normalizedFactors F hI hP |>.1 ) ( isPrime_of_mem_normalizedFactors F hI hP |>.2 ) ) ) _

/-
Regrouping: the product of all coordinates is the product over all prime
factors of `(ratBelow P) ^ (mult of P)`.
-/
theorem prod_encodeIdeal_eq {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∏ i, encodeIdeal F I i =
      ∏ P ∈ (normalizedFactors I).toFinset,
        (ratBelow F P) ^ ((normalizedFactors I).count P) := by
  -- By definition of `encodeIdeal`, we can rewrite the product as a sum over the primes in the normalized factors of `I`.
  have h_sum : ∏ i : Fin (Module.finrank ℚ F), encodeIdeal F I i = ∏ P ∈ (normalizedFactors I).toFinset, ∏ i : Fin (Module.finrank ℚ F), if primeCoord F P = i.val then (ratBelow F P) ^ ((normalizedFactors I).count P) else 1 := by
    rw [ Finset.prod_comm, Finset.prod_congr rfl ];
    unfold encodeIdeal;
    simp +decide [ Finset.prod_ite ];
  rw [ h_sum ];
  refine' Finset.prod_congr rfl fun P hP => _;
  rw [ Finset.prod_eq_single ⟨ primeCoord F P, primeCoord_lt F ( isPrime_of_mem_normalizedFactors F hI ( Multiset.mem_toFinset.mp hP ) |>.1 ) ( isPrime_of_mem_normalizedFactors F hI ( Multiset.mem_toFinset.mp hP ) |>.2 ) ⟩ ] <;> aesop

/-
The product of the encoding coordinates is at most `absNorm I`.
-/
theorem prod_encodeIdeal_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∏ i, encodeIdeal F I i ≤ Ideal.absNorm I := by
  rw [ prod_encodeIdeal_eq F hI ];
  have h_prod_le : ∏ P ∈ (normalizedFactors I).toFinset, (Ideal.absNorm P) ^ ((normalizedFactors I).count P) ≤ Ideal.absNorm I := by
    have h_prod_le : ∏ P ∈ (normalizedFactors I).toFinset, (Ideal.absNorm P) ^ ((normalizedFactors I).count P) = Ideal.absNorm (∏ P ∈ (normalizedFactors I).toFinset, P ^ ((normalizedFactors I).count P)) := by
      induction' ( normalizedFactors I ).toFinset using Finset.induction <;> simp_all +decide [ Finset.prod_insert ];
    convert h_prod_le.le using 2;
    convert ( Ideal.prod_normalizedFactors_eq_self hI ) |> Eq.symm;
    rw [ Finset.prod_multiset_count ];
  refine le_trans ?_ h_prod_le
  gcongr with Q hQ
  have hQp := isPrime_of_mem_normalizedFactors F hI (Multiset.mem_toFinset.mp hQ)
  exact ratBelow_le_absNorm F hQp.1 hQp.2

/-
Recovery: the multiplicity of a prime `P` in `I` is the `ratBelow P`-adic
valuation of the `primeCoord P` coordinate of the encoding.
-/
theorem count_eq_padicValNat {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (normalizedFactors I).count P =
      padicValNat (ratBelow F P)
        (encodeIdeal F I ⟨primeCoord F P, primeCoord_lt F hP hP0⟩) := by
  classical
  have hpp : (ratBelow F P).Prime := ratBelow_prime F hP hP0
  have hfact : ∀ Q ∈ (normalizedFactors I).toFinset.filter
      (fun Q => primeCoord F Q = primeCoord F P),
      (ratBelow F Q) ^ ((normalizedFactors I).count Q) ≠ 0 := by
    intro Q hQ
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hQ
    have hQp := isPrime_of_mem_normalizedFactors F hI hQ.1
    exact pow_ne_zero _ (ratBelow_prime F hQp.1 hQp.2).pos.ne'
  rw [eq_comm, ← Nat.factorization_def _ hpp]
  simp only [encodeIdeal]
  rw [Nat.factorization_prod hfact]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single P]
  · rw [hpp.factorization_pow, Finsupp.single_apply]
    simp
  · intro Q hQ hQP
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hQ
    have hQp := isPrime_of_mem_normalizedFactors F hI hQ.1
    have hrb : ratBelow F Q ≠ ratBelow F P := fun h =>
      hQP (prime_eq_of_coord_eq F hQp.1 hQp.2 hP hP0 h hQ.2)
    rw [(ratBelow_prime F hQp.1 hQp.2).factorization_pow, Finsupp.single_apply]
    simp [hrb]
  · intro hPnot
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hPnot
    push_neg at hPnot
    have hPmem : P ∉ normalizedFactors I := fun hmem => (hPnot hmem) rfl
    rw [Multiset.count_eq_zero_of_notMem hPmem]
    simp

/-
[foundational] The encoding is injective on nonzero ideals.
-/
theorem encodeIdeal_injOn :
    Set.InjOn (encodeIdeal F) {I : Ideal (𝓞 F) | I ≠ ⊥} := by
  intro I hI J hJ h_eq
  have h_factors : (normalizedFactors I).toFinset = (normalizedFactors J).toFinset := by
    refine' Finset.Subset.antisymm _ _ <;> intro P hP <;> simp_all +decide;
    · have h_prime : P.IsPrime ∧ P ≠ ⊥ := by
        grind +suggestions;
      have h_count : (normalizedFactors I).count P = (normalizedFactors J).count P := by
        convert count_eq_padicValNat F hI h_prime.1 h_prime.2 using 1;
        rw [ h_eq, count_eq_padicValNat F hJ h_prime.1 h_prime.2 ];
      contrapose! h_count; simp_all +decide [ Multiset.count_eq_zero ] ;
    · have h_prime : P.IsPrime ∧ P ≠ ⊥ := by
        grind +suggestions;
      have h_count : (normalizedFactors I).count P = (normalizedFactors J).count P := by
        have := count_eq_padicValNat F hI h_prime.1 h_prime.2; have := count_eq_padicValNat F hJ h_prime.1 h_prime.2; simp_all +decide [ funext_iff ] ;
      exact Multiset.count_pos.mp ( h_count.symm ▸ Multiset.count_pos.mpr hP );
  have h_multiset : (normalizedFactors I) = (normalizedFactors J) := by
    ext x; by_cases hx : x ∈ (normalizedFactors I).toFinset <;> simp_all +decide [ Multiset.count_eq_zero ] ;
    · have h_count_eq : ∀ P ∈ (normalizedFactors J).toFinset, P.IsPrime ∧ P ≠ ⊥ → (normalizedFactors I).count P = (normalizedFactors J).count P := by
        intros P hP hP_prime
        have h_count_eq : padicValNat (ratBelow F P) (encodeIdeal F I ⟨primeCoord F P, primeCoord_lt F hP_prime.left hP_prime.right⟩) = padicValNat (ratBelow F P) (encodeIdeal F J ⟨primeCoord F P, primeCoord_lt F hP_prime.left hP_prime.right⟩) := by
          rw [h_eq];
        rw [ count_eq_padicValNat F hI hP_prime.left hP_prime.right, count_eq_padicValNat F hJ hP_prime.left hP_prime.right, h_count_eq ];
      apply h_count_eq; simp [hx];
      exact isPrime_of_mem_normalizedFactors F hJ hx;
    · replace h_factors := Finset.ext_iff.mp h_factors x; aesop;
  have h_prod : I = (normalizedFactors I).prod ∧ J = (normalizedFactors J).prod := by
    exact ⟨ (Ideal.prod_normalizedFactors_eq_self hI).symm, (Ideal.prod_normalizedFactors_eq_self hJ).symm ⟩;
  rw [ h_prod.1, h_prod.2, h_multiset ]

end

end RankinCount

open NumberField in
/-- [hard] Injection from nonzero integral ideals of norm `≤ X` into the
`n`-tuples of positive naturals with product `≤ X` (`n = [F:ℚ]`).  Each ideal
`I = ∏_𝔭 𝔭^{v_𝔭}` is encoded by distributing, for every rational prime `p`,
the exponent `v_{𝔭_i}(I)` of the `i`-th prime above `p` into `f(𝔭_i)`
coordinates as the value `p^{v_{𝔭_i}(I)}`; since `∑_{𝔭∣p} e_𝔭 f_𝔭 = [F:ℚ]`
there are at most `n` coordinates used per prime and the resulting tuple has
product `absNorm I`.  The map is injective because the `p`-adic valuations of
the tuple recover all `v_𝔭(I)`, hence `I`. -/
theorem ideal_ncard_le_prodLeTuples_ncard (F : Type) [Field F] [NumberField F]
    {X : ℝ} :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard ≤
      (prodLeTuples (Module.finrank ℚ F) X).ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (encodeIdeal F) ?_ ?_ (prodLeTuples_finite _ _)
  · rintro I ⟨hI0, hIX⟩
    refine ⟨fun i => encodeIdeal_pos F hI0 i, ?_⟩
    calc (∏ i, (encodeIdeal F I i : ℝ))
        = ((∏ i, encodeIdeal F I i : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast prod_encodeIdeal_le_absNorm F hI0
      _ ≤ X := hIX
  · intro I hI J hJ h
    exact encodeIdeal_injOn F hI.1 hJ.1 h

open NumberField in
/-- [HARD] **Rankin-style ideal count.**  In any number field `F` of degree
`n`, the number of nonzero integral ideals of norm at most `X` is at most
`X² · 2^n`.  Sketch: `∑_{N𝔞 ≤ X} 1 ≤ X² ∑_{𝔞} N𝔞⁻²`, and by unique
factorization into primes (with at most `n` primes above each rational `p`,
each of norm `≥ p`), `∑_𝔞 N𝔞⁻² ≤ ∏_{p ≤ X} (1 - p⁻²)⁻ⁿ ≤ ζ(2)ⁿ ≤ 2ⁿ`,
restricting to ideals supported above primes `≤ X`.  This is the main
genuinely-new counting argument needed from the algebraic side. -/
theorem card_ideal_absNorm_le (F : Type) [Field F] [NumberField F]
    {X : ℝ} (hX : 1 ≤ X) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite ∧
      (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
        X ^ 2 * 2 ^ Module.finrank ℚ F := by
  refine ⟨?_, ?_⟩
  · apply Set.Finite.subset (Ideal.finite_setOf_absNorm_le ⌊X⌋₊)
    rintro I ⟨-, hI⟩
    exact Nat.le_floor hI
  · calc ((({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}).ncard : ℝ))
        ≤ ((prodLeTuples (Module.finrank ℚ F) X).ncard : ℝ) := by
          exact_mod_cast ideal_ncard_le_prodLeTuples_ncard F (X := X)
      _ ≤ X ^ 2 * 2 ^ Module.finrank ℚ F := prodLeTuples_ncard_le _ hX

open NumberField in
/-- [medium given `card_ideal_absNorm_le`] **Class number bound.**
`h_F ≤ |d_F| · 4^(deg F)`.  Sketch: by Mathlib's Minkowski-bound theorem
`NumberField.exists_ideal_in_class_of_norm_le`, every ideal class contains
an integral ideal of norm at most `(4/π)^s · (n!/nⁿ) · √|d_F| ≤ √|d_F|`;
classes inject into ideals of norm `≤ √|d_F|`, of which there are at most
`|d_F| · 2ⁿ` by `card_ideal_absNorm_le`. -/
theorem classNumber_le_bound (F : Type) [Field F] [NumberField F] :
    (NumberField.classNumber F : ℝ) ≤
      |(NumberField.discr F : ℝ)| * 4 ^ Module.finrank ℚ F := by
  have := @NumberField.exists_ideal_in_class_of_norm_le F _ _;
  choose f hf using this;
  have h_card : (Set.ncard (Set.image (fun C => (f C : Ideal (𝓞 F))) Set.univ)) ≤ (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) * ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 * |(discr F : ℝ)| * 2 ^ Module.finrank ℚ F := by
    have h_card : (Set.ncard {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces F * ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|)}) ≤ (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) * ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 * |(discr F : ℝ)| * 2 ^ Module.finrank ℚ F := by
      convert card_ideal_absNorm_le F _ |>.2 using 1;
      · ring_nf; norm_num [ Real.sq_sqrt <| abs_nonneg _ ];
      · refine' le_trans _ ( hf 1 |>.2 );
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr ( Ideal.absNorm_ne_zero_of_nonZeroDivisors _ );
    refine le_trans ?_ h_card;
    gcongr;
    · convert card_ideal_absNorm_le F _ |>.1 using 1;
      refine' le_trans _ ( hf 1 |>.2 );
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr ( Ideal.absNorm_ne_zero_of_nonZeroDivisors _ );
    · simp +zetaDelta at *;
      exact Set.range_subset_iff.mpr fun C => ⟨ by intro h; simpa [ h ] using f C |>.2, hf C |>.2 ⟩;
  refine le_trans ?_ ( h_card.trans ?_ );
  · rw [ Set.ncard_image_of_injective _ fun x y hxy => _, Set.ncard_univ ];
    · norm_num [ classNumber ];
    · intro x y hxy; have := hf x; have := hf y; aesop;
  · -- Simplify the right-hand side of the inequality.
    suffices h_simp : (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) * ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 * 2 ^ Module.finrank ℚ F ≤ 4 ^ Module.finrank ℚ F by
      convert mul_le_mul_of_nonneg_left h_simp ( abs_nonneg ( discr F : ℝ ) ) using 1 ; ring;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right ( by positivity ) _ ) ( by positivity ) ) _;
    · exact pow_le_one₀ ( by positivity ) ( div_le_one_of_le₀ ( mod_cast Nat.recOn ( Module.finrank ℚ F ) ( by norm_num ) fun n ihn => by rw [ Nat.factorial_succ, pow_succ' ] ; exact le_trans ( Nat.mul_le_mul_left _ ihn ) ( by gcongr ; linarith ) ) ( by positivity ) );
    · refine' le_trans ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( show ( 4 : ℝ ) / Real.pi ≤ 2 by rw [ div_le_iff₀ ] <;> linarith [ Real.pi_gt_three ] ) _ ) ( by positivity ) ) _;
      rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, ← pow_mul ];
      rw [ ← pow_add ];
      gcongr <;> norm_num;
      have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F; linarith;

/-! ## Class number and unit bounds (abstract) -/

/-
Abstract bound: in a commutative group generated by a finite set `S`, the
subgroup of squares has index at most `2 ^ S.card`.  Sketch: the quotient
`Q := G ⧸ (powMonoidHom 2).range` is an elementary abelian `2`-group (every
element squares to one), hence a `ZMod 2`-vector space spanned by the image of
`S`, so `Nat.card Q = 2 ^ finrank (ZMod 2) Q ≤ 2 ^ S.card`.
-/
lemma index_powMonoidHom_two_le_of_closure {G : Type*} [CommGroup G]
    {S : Finset G} (hS : Subgroup.closure (S : Set G) = ⊤) :
    (MonoidHom.range (powMonoidHom 2 : G →* G)).index ≤ 2 ^ S.card := by
  -- Since $G$ is generated by $S$, every element of $G$ can be written as a product of elements from $S$ and their inverses.
  have h_gen : ∀ g : G, ∃ f : S → ℤ, g = ∏ s : S, s.val ^ f s := by
    intro g
    have h_gen : g ∈ Subgroup.closure (S : Set G) := by
      aesop;
    refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ h_gen;
    · refine' ⟨ fun s => if s = ⟨ x, hx ⟩ then 1 else 0, _ ⟩ ; aesop;
    · exact ⟨ fun _ => 0, by simp +decide ⟩;
    · rintro x y hx hy ⟨ f, rfl ⟩ ⟨ g, rfl ⟩ ; use f + g; simp +decide [ Finset.prod_mul_distrib, zpow_add ] ;
    · rintro x hx ⟨ f, rfl ⟩ ; exact ⟨ -f, by simp +decide [ Finset.prod_inv_distrib ] ⟩ ;
  have h_coset_le : ∀ (g : G), ∃ (f : S → Fin 2), (QuotientGroup.mk g : G ⧸ (powMonoidHom 2 : G →* G).range) = (QuotientGroup.mk (∏ s : S, s.val ^ (f s : ℤ)) : G ⧸ (powMonoidHom 2 : G →* G).range) := by
    intro g
    obtain ⟨f, hf⟩ := h_gen g
    use fun s => ⟨(f s) % 2 |> Int.toNat, by
      grind⟩
    generalize_proofs at *;
    simp +decide [ hf, ← QuotientGroup.mk_prod ];
    rw [ QuotientGroup.eq ];
    refine' ⟨ ∏ s ∈ S.attach, s.val ^ ( - ( f s / 2 ) ), _ ⟩ ; simp +decide [ ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← zpow_add, ← zpow_mul ] ; ring;
    rw [ inv_eq_iff_eq_inv ] ; simp +decide [ ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← zpow_natCast, ← zpow_mul ] ; ring;
    refine' Finset.prod_congr rfl fun x hx => _ ; rw [ max_eq_left ( Int.emod_nonneg _ ( by decide ) ) ] ; rw [ ← zpow_neg, ← zpow_add ] ; ring;
    exact congr_arg _ ( by linarith [ Int.emod_add_mul_ediv ( f x ) 2 ] );
  have h_coset_le : Nat.card (G ⧸ (powMonoidHom 2 : G →* G).range) ≤ Nat.card (S → Fin 2) := by
    have h_coset_le : Function.Surjective (fun f : S → Fin 2 => (QuotientGroup.mk (∏ s : S, s.val ^ (f s : ℤ)) : G ⧸ (powMonoidHom 2 : G →* G).range)) := by
      exact fun x => by obtain ⟨ g, rfl ⟩ := QuotientGroup.mk_surjective x; obtain ⟨ f, hf ⟩ := h_coset_le g; exact ⟨ f, hf ▸ rfl ⟩ ;
    apply_rules [ Nat.card_le_card_of_surjective ];
  aesop

open NumberField in
/-- [medium-hard] **Squares have small index in the unit group.**  By
Dirichlet's unit theorem, `(𝓞 F)ˣ ≅ μ_F × ℤ^rank` with
`rank = r₁ + r₂ - 1 < deg F`, and `μ_F` is finite cyclic of even order, so
`[(𝓞 F)ˣ : ((𝓞 F)ˣ)²] = 2^(rank+1) ≤ 2^(deg F)`.  Mathlib has the unit
theorem (`NumberField.Units.rank`, the `unitLattice` machinery); the index
computation for the squaring map on a finitely generated abelian group
should reduce to standard `Module`/`ZMod` lemmas. -/
theorem units_sq_index_le (F : Type) [Field F] [NumberField F] :
    (MonoidHom.range (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ)).index ≤
      2 ^ Module.finrank ℚ F := by
  refine' le_trans _ ( pow_le_pow_right₀ ( by norm_num ) _ );
  convert Erdos.index_powMonoidHom_two_le_of_closure _;
  exact Finset.image ( fun i => NumberField.Units.fundSystem F i ) Finset.univ ∪ { ( Classical.choose ( IsCyclic.exists_generator ( α := NumberField.Units.torsion F ) ) : NumberField.Units.torsion F ) |> Subtype.val };
  · convert NumberField.Units.closure_fundSystem_sup_torsion_eq_top F using 1;
    refine' le_antisymm _ _ <;> simp +decide [ Subgroup.closure_le, Set.insert_subset_iff ];
    · exact ⟨ Subgroup.mem_sup_right <| Classical.choose_spec ( IsCyclic.exists_generator ( α := NumberField.Units.torsion F ) ) |> fun h => by aesop, Set.range_subset_iff.mpr fun i => Subgroup.mem_sup_left <| Subgroup.subset_closure <| Set.mem_range_self i ⟩;
    · refine' ⟨ Set.range_subset_iff.mpr fun i => Subgroup.subset_closure <| Set.mem_insert_of_mem _ <| Set.mem_range_self _, _ ⟩;
      have := Classical.choose_spec ( IsCyclic.exists_generator ( α := Units.torsion F ) );
      intro x hx; specialize this ⟨ x, hx ⟩ ; obtain ⟨ n, hn ⟩ := this; simp_all +decide [ Subgroup.mem_closure ] ;
      intro K hK; replace hn := congr_arg Subtype.val hn; aesop;
  · refine' le_trans ( Finset.card_union_le _ _ ) _ ; norm_num;
    refine' lt_of_le_of_lt ( Finset.card_image_le ) _;
    rw [Finset.card_univ, Fintype.card_fin]
    have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
    have h3 : 0 < Fintype.card (NumberField.InfinitePlace F) :=
      Fintype.card_pos_iff.mpr ⟨Classical.arbitrary _⟩
    have h4 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    simp only [NumberField.Units.rank]
    omega

end Erdos
