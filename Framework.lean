import Mathlib

/-!
# Framework: the uniform-constant Erdős unit-distance conjecture is false

This file is a sorried skeleton of L. Alpöge's one-page proof (2026,
"Integral points on norm-one tori and the Erdős unit-distance exponent";
see `informal-proof.md` alongside this file) that for every `C > 0` there
are arbitrarily large `n` admitting `n`-point planar sets with more than
`n^(1 + C / log log n)` unit-distance pairs.  This refutes Erdős's 1946
conjecture `ν(n) ≤ n^(1 + C / log log n)` (for an absolute constant `C`).

The proof has three independent layers, reflected in the file structure.

* **Geometric core** (`section GeometricCore`): purely elementary.  Inside
  the "polydisc box" `box r 2 ⊆ (ι → ℂ)` (points whose `i`-th coordinate
  has modulus at most `2 * r i`), an additive subgroup `Λ` is sliced by
  grid pigeonholes.  No measure theory: all packing/doubling bounds are
  proved by partitioning each coordinate disc into small square cells and
  pigeonholing, which loses only absolute constants per coordinate.
  Translating `Λ ∩ box r 1` by an element `z` whose coordinates have
  modulus exactly `r i` lands in `box r 2` at projected distance exactly
  one, producing many unit-distance pairs after projecting to a single
  coordinate.

* **Arithmetic construction** (`section Arithmetic`): in the multiquadratic
  CM field `K = ℚ(i, √q₀, …, √q_{g-1})` (`q_j` the `j`-th prime `≡ 3 mod 4`)
  of degree `2^(g+1)`, the product `m = p_0 ⋯ p_{t-1}` of the first `t`
  primes `≡ 1 mod 4` admits `≥ 2^(t·2^(g-1))` integral ideals `𝔄` with
  `𝔄 · 𝔄∗ = (m)` (one prime chosen per conjugation orbit above each `p_i`).
  Pigeonholing those into a single ideal class (cost `1/h_K`), and the
  resulting generators `y·y∗` into cosets of squares of units of `𝒪_{K⁺}`
  (cost `2^(2^g)`), produces a totally positive `μ ∈ 𝒪_{K⁺}` whose norm
  fibre `Z = {z ∈ 𝔟 : z·z∗ = μ}` is large.  Every `z ∈ Z` has `w(z)² = w(μ)`
  at every infinite place `w` — the repeated unit distance.

* **Assembly** (`section Assembly`): with `d = 2^g` places, the counts are
  `#Z ≥ 2^(t·d/2) / (h_K·2^d)`, `n ≤ (32√m)^(2d)`, and
  `ν ≥ #Z · n / (2·64^d)`, so `log(ν/n) ≫ t·d` while `log n ≪ d·t·log t`
  and `log log n ≍ g`; choosing `g ≈ C·log t` and `t` large wins.  The
  class-number estimate `h_K ≤ |d_K| · 4^(deg K)` (Minkowski bound plus a
  Rankin-style ideal count with `s = 2`) and a polynomial bound on the
  `i`-th prime in the progressions `1, 3 mod 4` are the only analytic
  inputs.

Every `sorry` is annotated with a difficulty guess and a proof sketch.
-/

open scoped Classical

namespace Erdos

/-! ## Unit-distance counting -/

/-- For a finite planar set `P ⊆ ℝ²`, `unitDist P` is the number of
unordered pairs `{x, y} ⊆ P` at Euclidean distance exactly `1`.
(Identical to the definition in the lean-eval problem
`erdos_unit_distance_conjecture_false`.) -/
noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2

/-- The number of *ordered* pairs of distinct points of `P ⊆ ℂ` at
distance exactly `1`.  The geometric core produces planar sets inside `ℂ`;
`exists_euclidean_copy` transports the count to `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def unitPairsC (P : Finset ℂ) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card

/-- [easy] The unit-distance pair count is exactly half the ordered count:
the involution `(x, y) ↦ (y, x)` of `P.offDiag` preserves the distance-one
filter and has no fixed points, so the filtered set has even cardinality.
Sketch: `Finset.card_div_two_eq...`; or directly exhibit the filtered set as
a disjoint union over the swap involution. -/
theorem two_mul_unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * unitDist P = (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card := by
  sorry

/-- The standard real-linear isometry `ℂ ≃ EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def complexToPlane : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

/-- [easy] Transport a finite point set from `ℂ` to the Euclidean plane,
preserving cardinality and the (ordered) unit-distance count.
Sketch: take `Q = P.image complexToPlane`; the image is injective and
`complexToPlane` preserves distances, so the two filtered sets biject;
conclude with `two_mul_unitDist`. -/
theorem exists_euclidean_copy (P : Finset ℂ) :
    ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
      Q.card = P.card ∧ 2 * unitDist Q = unitPairsC P := by
  sorry

/-! ## Geometric core

Everything in this section is about an additive subgroup `Λ ≤ (ι → ℂ)`
(`ι` finite: in the application, the set of infinite places, with
`Fintype.card ι = 2^g`), a "radius vector" `r : ι → ℝ`, and the polydisc
boxes `box r c`.  All bounds are by grid pigeonhole: each coordinate disc
`{‖w‖ ≤ 2 * r i}` is partitioned into at most `(4 * 2/ε)²` half-open square
cells of diameter at most `ε * r i`, so the polydisc splits into at most
`(8/ε)^(2·#ι)` cells, on each of which all pairwise coordinate differences
have modulus at most `ε * r i`. -/

section GeometricCore

variable {ι : Type} [Fintype ι]

/-- The closed polydisc box of polyradius `c • r` in `ι → ℂ`. -/
def box (r : ι → ℝ) (c : ℝ) : Set (ι → ℂ) :=
  {x | ∀ i, ‖x i‖ ≤ c * r i}

omit [Fintype ι] in
theorem box_mono {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {c c' : ℝ} (h : c ≤ c') :
    box r c ⊆ box r c' :=
  fun x hx i => (hx i).trans (by have := hr i; nlinarith)

/-- [medium] **Grid pigeonhole.**  A subset of the polydisc `box r c` whose
distinct elements are `ε`-separated in some coordinate (relative to `r`)
is finite, of cardinality at most `(4 * c / ε) ^ (2 * #ι)`.
Sketch: partition each coordinate disc of radius `c * r i` into half-open
square cells of side `ε * r i / √2`; there are at most
`⌈2√2 * c/ε⌉² ≤ (4c/ε)²` cells per coordinate (using `ε ≤ c`).  Map each
point to its tuple of cell indices: two points with the same tuple differ
by at most `ε * r i` in every coordinate, contradicting separation; so the
map into `ι → (Fin M × Fin M)` is injective. -/
theorem finite_and_card_le_of_separated (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c)
    {S : Set (ι → ℂ)} (hS : S ⊆ box r c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, ε * r i < ‖x i - y i‖) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (4 * c / ε) ^ (2 * Fintype.card ι) := by
  sorry

/-- [easy given `finite_and_card_le_of_separated`] **Lattice points in the
box.**  If every nonzero element of `Λ` escapes the small polydisc
`box r ρ`, then `Λ ∩ box r 2` is finite of cardinality at most
`(8/ρ)^(2·#ι)`.  Sketch: differences of distinct elements of `Λ ∩ box r 2`
are nonzero elements of `Λ`, so the separation hypothesis of the grid
pigeonhole holds with `c = 2`, `ε = ρ`. -/
theorem lattice_inter_box_finite_card (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖) :
    ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite ∧
      (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤
        (8 / ρ) ^ (2 * Fintype.card ι) := by
  sorry

/-- [medium] **Doubling.**  Counting lattice points in the double box loses
at most `64^#ι` against the unit box.  Sketch: partition `box r 2` into at
most `(4·2/1)² = 64` cells per coordinate, of coordinatewise diameter at
most `1 * r i`.  If a cell meets `Λ ∩ box r 2`, fix one such point `x₀`;
every other lattice point `y` of the same cell has `y - x₀ ∈ Λ ∩ box r 1`,
so the cell contains at most `#(Λ ∩ box r 1)` lattice points.  Sum over
cells. -/
theorem ncard_box_two_le_doubling (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ))
    (hfin : ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite) :
    (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤
      64 ^ Fintype.card ι * ((Λ : Set (ι → ℂ)) ∩ box r 1).ncard := by
  sorry

variable (i₀ : ι)

/-- Projection of a polydisc point to the distinguished coordinate `i₀`,
rescaled so that the repeated distance becomes exactly `1`. -/
noncomputable def proj (r : ι → ℝ) (i₀ : ι) (x : ι → ℂ) : ℂ :=
  x i₀ / (r i₀ : ℂ)

/-- [medium] **Translation produces unit distances.**  Let `Z` be a finite
set of elements of `Λ` whose coordinates have modulus *exactly* `r i`.
Then the projection `P ⊆ ℂ` of `Λ ∩ box r 2` to the (rescaled) `i₀`-th
coordinate satisfies `#P = #(Λ ∩ box r 2)` and has at least
`#Z · #(Λ ∩ box r 1)` ordered unit-distance pairs.
Sketch: (1) `proj` is injective on `Λ` by `hinj` (two preimages differ by
an element of `Λ` vanishing at `i₀`), giving the cardinality statement.
(2) For `a ∈ Λ ∩ box r 1` and `z ∈ Z`, the translate `a + z` lies in
`Λ ∩ box r 2` (triangle inequality coordinatewise), and
`dist (proj a) (proj (a + z)) = ‖z i₀‖ / r i₀ = 1`.  The assignment
`(a, z) ↦ (proj a, proj (a + z))` is injective into ordered pairs (recover
`a` from the first component by injectivity, then `z i₀`, then `z`), and
each image pair is a distinct-points pair at distance one. -/
theorem le_unitPairsC_of_translates (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ))
    (hinj : ∀ x ∈ Λ, x i₀ = 0 → x = 0)
    (hfin : ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite)
    (Z : Finset (ι → ℂ)) (hZΛ : ∀ z ∈ Z, z ∈ Λ)
    (hZr : ∀ z ∈ Z, ∀ i, ‖z i‖ = r i) :
    (hfin.toFinset.image (proj r i₀)).card = ((Λ : Set (ι → ℂ)) ∩ box r 2).ncard ∧
      Z.card * ((Λ : Set (ι → ℂ)) ∩ box r 1).ncard ≤
        unitPairsC (hfin.toFinset.image (proj r i₀)) := by
  sorry

/-- [medium, glue] **The geometric core, assembled.**  From a separated
lattice `Λ`, a coordinate-exact set `Z ⊆ Λ`, and an injective coordinate,
produce a planar point set `Q` with `#Q = n` points where
`#Z ≤ n ≤ (8/ρ)^(2·#ι)` and `#Z · n ≤ 2 · 64^#ι · unitDist Q`.
Sketch: combine `lattice_inter_box_finite_card` (finiteness and the upper
bound for `n`), `le_unitPairsC_of_translates`, and
`ncard_box_two_le_doubling`, then transport to the Euclidean plane with
`exists_euclidean_copy`.  For `#Z ≤ n` note `Z ⊆ Λ ∩ box r 2` since
`‖z i‖ = r i ≤ 2 r i`, and `Z` maps injectively into the box (it is inside
it). -/
theorem geometric_core (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖)
    (hinj : ∀ x ∈ Λ, x i₀ = 0 → x = 0)
    (Z : Finset (ι → ℂ)) (hZΛ : ∀ z ∈ Z, z ∈ Λ)
    (hZr : ∀ z ∈ Z, ∀ i, ‖z i‖ = r i) :
    ∃ (n : ℕ) (Q : Finset (EuclideanSpace ℝ (Fin 2))),
      Q.card = n ∧
      Z.card ≤ n ∧
      (n : ℝ) ≤ (8 / ρ) ^ (2 * Fintype.card ι) ∧
      (Z.card : ℝ) * n ≤ 2 * 64 ^ Fintype.card ι * unitDist Q := by
  sorry

end GeometricCore

/-! ## Primes in the progressions `1, 3 mod 4` -/

/-- The `j`-th prime congruent to `3` modulo `4` (zero-indexed):
`q3 0 = 3`, `q3 1 = 7`, `q3 2 = 11`, … -/
noncomputable def q3 (j : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 3) j

/-- The `i`-th prime congruent to `1` modulo `4` (zero-indexed):
`p1 0 = 5`, `p1 1 = 13`, `p1 2 = 17`, … -/
noncomputable def p1 (i : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 1) i

/-- The product `m t = p1 0 * p1 1 * ⋯ * p1 (t-1)` of the first `t` primes
congruent to `1 mod 4`; the repeated unit distance will be (a rescaling of)
a norm-one element above `m t`. -/
noncomputable def m (t : ℕ) : ℕ := ∏ i ∈ Finset.range t, p1 i

/-- [easy] There are infinitely many primes `≡ 3 mod 4`.  Sketch: in
Mathlib as a special case of Dirichlet
(`Nat.forall_exists_prime_gt_and_modEq`), or by the classical elementary
argument. -/
theorem infinite_setOf_q3 : {n | n.Prime ∧ n % 4 = 3}.Infinite := by
  sorry

/-- [easy] There are infinitely many primes `≡ 1 mod 4`. -/
theorem infinite_setOf_p1 : {n | n.Prime ∧ n % 4 = 1}.Infinite := by
  sorry

/-- [easy given infinitude] `q3 j` is prime and `≡ 3 mod 4`
(`Nat.nth_mem_of_infinite`). -/
theorem q3_spec (j : ℕ) : (q3 j).Prime ∧ q3 j % 4 = 3 :=
  Nat.nth_mem_of_infinite infinite_setOf_q3 j

/-- [easy given infinitude] `p1 i` is prime and `≡ 1 mod 4`. -/
theorem p1_spec (i : ℕ) : (p1 i).Prime ∧ p1 i % 4 = 1 :=
  Nat.nth_mem_of_infinite infinite_setOf_p1 i

theorem q3_strictMono : StrictMono q3 :=
  Nat.nth_strictMono infinite_setOf_q3

theorem p1_strictMono : StrictMono p1 :=
  Nat.nth_strictMono infinite_setOf_p1

/-- [HARD — the only quantitative analytic input, together with
`p1_poly_bound`.]  Polynomial growth of the `j`-th prime `≡ 3 mod 4`.
This needs a Chebyshev-type lower bound for primes in the two progressions
mod 4 (`π_{3 mod 4}(x) ≫ x / log x`); the elementary Euclid-style proofs of
infinitude give only exponential bounds, which are *not* sufficient
downstream.  Any polynomial bound works; `(j+2)²` is far from the truth
(`q3 j ∼ 2 j log j`).  In Mathlib, the strongest available route may be via
`Mathlib.NumberTheory.LSeries.PrimesInAP` (Dirichlet) upgraded with a
quantitative argument, or any future PNT-in-AP development. -/
theorem q3_poly_bound : ∀ᶠ j in Filter.atTop, (q3 j : ℝ) ≤ (j + 2) ^ 2 := by
  sorry

/-- [HARD] Polynomial growth of the `i`-th prime `≡ 1 mod 4`.  See
`q3_poly_bound`. -/
theorem p1_poly_bound : ∀ᶠ i in Filter.atTop, (p1 i : ℝ) ≤ (i + 2) ^ 2 := by
  sorry

/-- [easy] `m t ≥ 2^t` (each prime factor is `≥ 5`). -/
theorem m_ge (t : ℕ) : 2 ^ t ≤ m t := by
  sorry

/-- [medium given `p1_poly_bound`] The logarithm of `m t` grows like
`t log t` up to constants: there is `c₁ ≥ 1` with
`log (m t) ≤ c₁ * t * log (t + 2)` for all `t`.  Sketch:
`log (m t) = ∑_{i<t} log (p1 i)`; bound all but finitely many summands by
`2 log (i + 2) ≤ 2 log (t + 2)` using `p1_poly_bound` and absorb the
finitely many exceptions into `c₁`. -/
theorem log_m_le : ∃ c₁ : ℝ, 1 ≤ c₁ ∧
    ∀ t : ℕ, Real.log (m t) ≤ c₁ * t * Real.log (t + 2) := by
  sorry

/-! ## The multiquadratic CM field -/

/-- The multiquadratic CM field `K_g = ℚ(i, √q3 0, …, √q3 (g-1))`, realised
as an intermediate field of `ℚ ⊆ ℂ`.  Note `ℚ(i, √q) = ℚ(i, √-q)`, so this
agrees with the field `ℚ(√-4, √-q₁, …)` of the informal proof; its maximal
totally real subfield is `ℚ(√q3 0, …, √q3 (g-1))` of degree `2^g`. -/
noncomputable def Kf (g : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g))

/-- [easy] `K_g/ℚ` is finite: it is generated by finitely many algebraic
numbers (`i` and the `√q3 j`, `j < g`).
Sketch: `IntermediateField.finiteDimensional_adjoin`; each generator is
integral over ℚ (root of `X² + 1` resp. `X² - q3 j`). -/
theorem Kf_finiteDimensional (g : ℕ) : FiniteDimensional ℚ (Kf g) := by
  sorry

noncomputable instance (g : ℕ) : NumberField (Kf g) :=
  { to_charZero := inferInstance
    to_finiteDimensional := Kf_finiteDimensional g }

/-- [HARD-ish; classical] The multiquadratic field has the full degree
`2^(g+1)`: the `g+1` quadratic generators `i, √q3 0, …, √q3 (g-1)` are
multiplicatively independent modulo squares.  Standard proof: induction on
the number of generators; `√a ∉ ℚ(√b₁, …, √bₖ)` whenever `a` is a nonsquare
product of new primes, by Kummer theory / ramification / explicit descent
on coefficients.  (This is a known nontrivial formalization exercise; cf.
the Galois-theoretic statement that `Gal(K_g/ℚ) ≅ (ℤ/2)^(g+1)`.) -/
theorem Kf_finrank (g : ℕ) : Module.finrank ℚ (Kf g) = 2 ^ (g + 1) := by
  sorry

/-- [medium-easy] `K_g` is totally complex: it contains `i`, and a real
embedding would send `i` to a real square root of `-1`.
Sketch: for `w : InfinitePlace (Kf g)`, if `w` were real, its embedding
`φ : Kf g →+* ℂ` composed with conjugation equals itself; but
`φ ⟨i, _⟩² = -1` forces `φ ⟨i, _⟩ = ±I`, which is not conjugation-fixed. -/
theorem Kf_isTotallyComplex (g : ℕ) : NumberField.IsTotallyComplex (Kf g) := by
  sorry

noncomputable instance (g : ℕ) : NumberField.IsTotallyComplex (Kf g) :=
  Kf_isTotallyComplex g

/-- [medium] `K_g/ℚ` is an abelian Galois extension.  Sketch: it is the
splitting field of `(X² + 1) ∏_j (X² - q3 j)` (each quadratic generator
brings its conjugate `±` partner), and every `σ ∈ Gal` is determined by
signs `σ(√q3 j) = ±√q3 j`, `σ(i) = ±i`, so all elements square to the
identity and the group is elementary abelian. -/
theorem Kf_isAbelianGalois (g : ℕ) : IsAbelianGalois ℚ (Kf g) := by
  sorry

noncomputable instance (g : ℕ) : IsAbelianGalois ℚ (Kf g) :=
  Kf_isAbelianGalois g

/-- `K_g` is a CM field (instance, from Mathlib's
`NumberField.IsCMField.of_isAbelianGalois`). -/
noncomputable example (g : ℕ) : NumberField.IsCMField (Kf g) := inferInstance

/-! ## Class number and unit bounds (abstract) -/

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
  sorry

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
  sorry

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
  sorry

/-- [HARD-ish] **Discriminant bound for the multiquadratic field.**
Sketch: the products `∏_{j ∈ S} γ_j` of the generators
`γ ∈ {i, √q3 0, …, √q3 (g-1)}` over subsets `S` form a ℚ-basis consisting
of algebraic integers; the trace form is diagonal on this basis
(`Tr(b_S b_T) = 0` for `S ≠ T` since some generator changes sign under an
automorphism fixing the rest), with `|Tr(b_S²)| = 2^(g+1) ∏_{j ∈ S} q3 j`
(reading `q3` of the `i`-slot as `4`... any uniform bound suffices).  Hence
`|d_K|` divides the determinant `≤ (4^(g+1) ∏_{j<g} q3 j)^(2^(g+1))`. -/
theorem Kf_discr_le (g : ℕ) :
    |(NumberField.discr (Kf g) : ℝ)| ≤
      (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℝ)) ^ 2 ^ (g + 1) := by
  sorry

/-- [medium given `classNumber_le_bound`, `Kf_discr_le`, `q3_poly_bound`]
Consolidated class-number estimate: `log h_{K_g} ≤ c₀ · 2^g · (g+1) log (g+1)`.
Sketch: combine the three inputs;
`log |d_K| ≤ 2^(g+1) · ((g+1) log 4 + ∑_{j<g} log (q3 j))` and
`∑_{j<g} log (q3 j) ≤ 2 g log (g+2) + O(1)` by `q3_poly_bound`; absorb
small-`g` exceptions into `c₀`. -/
theorem log_classNumber_Kf_le : ∃ c₀ : ℝ, 1 ≤ c₀ ∧
    ∀ g : ℕ, Real.log (NumberField.classNumber (Kf g)) ≤
      c₀ * 2 ^ g * (g + 1) * Real.log (g + 2) := by
  sorry

/-! ## The arithmetic construction -/

section Arithmetic

open NumberField IsCMField

/-- [HARD] **Many conjugate-product ideals above `m`.**  There are at least
`2^(t·2^(g-1))` integral ideals `𝔄` of `𝒪_{K_g}` with `𝔄 · 𝔄∗ = (m t)`
(`∗` = the CM complex conjugation).  Sketch: each `p = p1 i` is odd,
distinct from every `q3 j` (`1 ≢ 3 mod 4`), hence unramified in `K_g`; its
Frobenius is trivial on `i` (`p ≡ 1 mod 4` splits in `ℚ(i)`), hence differs
from complex conjugation `τ`, so `τ` (not in the decomposition group) acts
freely on the `≥ 2^g` primes above `p`, in `≥ 2^(g-1)` orbits `{𝔭, τ𝔭}`.
Choosing one prime from each orbit for each of the `t` rational primes
gives `≥ (2^(2^(g-1)))^t` distinct ideals with `𝔄 𝔄∗ = (m t)` (unique
factorization).  -/
theorem exists_ideal_family (g t : ℕ) (hg : 1 ≤ g) :
    ∃ F : Finset (Ideal (𝓞 (Kf g))),
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤ F.card ∧
      ∀ A ∈ F,
        A * Ideal.map (ringOfIntegersComplexConj (Kf g)) A =
          Ideal.span {(m t : 𝓞 (Kf g))} := by
  sorry

/-- [medium-hard given `exists_ideal_family` and `units_sq_index_le`]
**The norm fibre `Z`.**  There exist a nonzero integral ideal `b`, a
nonzero `μ ∈ K_g` and a finite set `Z` of integers of `K_g`, all lying in
`b`, such that:
* every `z ∈ Z` satisfies `w(z)² = w(μ)` at every infinite place `w`
  (i.e. `z · z∗ = μ`, one archimedean modulus at every place);
* `∏_w w(μ) = (m t)^(2^g) · N(b)`;
* `#Z ≥ 2^(t·2^(g-1)) / (h_K · 2^(2^g))`.

Sketch: pigeonhole the family from `exists_ideal_family` into one ideal
class (`h_K` classes; use `ClassGroup.mk0`); pick an integral ideal `b`
in the inverse class (`ClassGroup.mk0_surjective`); each `𝔄·b = (y_𝔄)` is
principal with `y_𝔄 ∈ b`, and `y_𝔄 y_𝔄∗` generates `(m t)·b·b∗`, so the
ratios are totally positive units of `𝒪_{K⁺}` (totally positive since
`σ(y y∗) = |σ y|² > 0`); pigeonhole over the `≤ 2^(2^g)` square-classes of
units (`units_sq_index_le` for `K⁺`, of degree `2^g`), and set
`z_𝔄 = y_𝔄 ε_𝔄⁻¹`, `μ = z z∗` (common value).  Injectivity of `𝔄 ↦ z_𝔄`:
`(z_𝔄) = 𝔄 b` and Dedekind cancellation.  The norm identity:
`N_{K/ℚ}(μ) = N(m·b·b∗) = (m t)^(2^(g+1)) N(b)²` and
`∏_w w(μ) = √|N_{K/ℚ}(μ)|` (places squared), giving
`(m t)^(2^g) · N(b)`.  The place identity: `w(z)² = w(z) w(z∗) = w(z z∗)`
using `infinitePlace_complexConj`. -/
theorem arithmetic_construction (g t : ℕ) (hg : 1 ≤ g) (ht : 1 ≤ t) :
    ∃ (b : Ideal (𝓞 (Kf g))) (μ : Kf g) (Z : Finset (𝓞 (Kf g))),
      b ≠ ⊥ ∧ μ ≠ 0 ∧
      (∀ z ∈ Z, z ∈ b) ∧
      (∀ z ∈ Z, ∀ w : InfinitePlace (Kf g),
        (w (algebraMap (𝓞 (Kf g)) (Kf g) z)) ^ 2 = w μ) ∧
      (∏ w : InfinitePlace (Kf g), w μ) = (m t : ℝ) ^ 2 ^ g * (Ideal.absNorm b : ℝ) ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤
        (Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := by
  sorry

/-- The coordinatewise-embeddings map `𝒪_{K_g} → (places → ℂ)`, sending
`x` to `(w.embedding x)_w` — one choice of embedding per conjugate pair.
This is the "Minkowski map" whose image of the ideal `b` is the lattice `Λ`
fed to the geometric core. -/
noncomputable def mink (g : ℕ) :
    𝓞 (Kf g) →+* (NumberField.InfinitePlace (Kf g) → ℂ) :=
  RingHom.pi fun w => w.embedding.comp (algebraMap (𝓞 (Kf g)) (Kf g))

/-- [medium given everything above; pure glue]  **Summary of the
construction.**  For all `g t ≥ 1` there is a planar set `Q` with `#Q = n`
points satisfying the three counting estimates that feed the assembly:
`n` is at least `#Z` (first line), at most `(32 √(m t))^(2·2^g)` (second),
and `Q` has at least `#Z · n / (2 · 64^(2^g))` unit-distance pairs (third,
folded with the first into the displayed form).

Sketch: instantiate the geometric core with `ι = InfinitePlace (K_g)`
(`#ι = 2^g` by `IsTotallyComplex.card_infinitePlace` and `Kf_finrank`),
`Λ = mink g '' b`, `r w = √(w μ)`, `ρ = 1/(4·√(m t))`, `i₀` arbitrary, and
`Z' = Z.image (mink g)`.  Hypotheses: `hr` from `μ ≠ 0`; `hinj` since a
field embedding is injective; `hZr` from the place identity and
`norm_embedding_eq`; `hsep`: for `0 ≠ x ∈ b`,
`∏_w w(x)² = |N_{K/ℚ}(x)| ≥ N(b)` (an element of `b` generates a
sub-ideal), while `∏_w (ρ √(w μ))² = ρ^(2^(g+1)) (m t)^(2^g) N(b) < N(b)`,
so not all coordinates can be `≤ ρ r w`. -/
theorem exists_good_pointset (g t : ℕ) (hg : 1 ≤ g) (ht : 1 ≤ t) :
    ∃ (n : ℕ) (Q : Finset (EuclideanSpace ℝ (Fin 2))),
      Q.card = n ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤
        (n : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g ∧
      (n : ℝ) ≤ (32 * Real.sqrt (m t)) ^ (2 * 2 ^ g) ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) * (n : ℝ) ≤
        (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g *
          (2 * 64 ^ 2 ^ g) * unitDist Q := by
  sorry

end Arithmetic

/-! ## Assembly -/

section Assembly

/-- [medium; pure real arithmetic]  **The final counting inequality.**
Suppose `n, ν` (point and unit-pair counts), `h` (class number) and the
parameters `g, t` satisfy the construction estimates below.  If moreover
`t` is large compared to `g log g` and to `log h / 2^g`, and `g` is large
compared to `C log t`, then `ν` beats `n^(1 + C/log log n)`.

The precise sufficient conditions encoded here:
with `d = 2^g`,
* `hpairs` forces `log (ν/n) ≥ (t·d/2)·log 2 - log h - d·log 2 - log 2 - d·log 64`,
  which is `≥ (t·d/4)·log 2` by `hth` (note `hth` gives `log h ≤ d·(t/8 - 8)`);
* `hlower` plus `hth` force `log n ≥ 0.2·t·d`, hence
  `log log n ≥ log d = g·log 2` (using `ht5`);
* `hMn` bounds `log n ≤ d·(log M + 7)`, so by `hgC`
  `C·log n / log log n ≤ C·d·(log M + 7)/(g·log 2) ≤ (t·d/40)·log 2 < (t·d/4)·log 2`.

Stated as a closed implication between real inequalities so that it can be
attacked independently of all geometry and number theory. -/
theorem key_inequality
    {C : ℝ} (hC : 0 < C) {g t : ℕ} {n ν h M : ℝ}
    (hn16 : 16 ≤ n) (hν : 0 < ν) (hh : 1 ≤ h) (hM : 3 ≤ M)
    -- construction estimates (d = 2^g as a real):
    (hlower : (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤ n * h * 2 ^ 2 ^ g)
    (hupper : n ≤ (32 * Real.sqrt M) ^ (2 * 2 ^ g))
    (hpairs : (2 : ℝ) ^ (t * 2 ^ (g - 1)) * n ≤ h * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g) * ν)
    -- size conditions on the parameters:
    (hg1 : 1 ≤ g) (ht5 : 5 ≤ t)
    (hth : (8 : ℝ) * (Real.log h / 2 ^ g + 8) ≤ t)
    (hgC : 40 * C * (Real.log M + 8) ≤ (t : ℝ) * g * Real.log 2 ^ 2)
    -- log M stands in for log (m t) ≤ c₁ t log t; the caller arranges sizes
    (hMn : Real.log n ≤ 2 * 2 ^ g * (Real.log 32 + Real.log M / 2)) :
    n ^ (1 + C / Real.log (Real.log n)) < ν := by
  sorry

/-- **The uniform-constant form of Erdős's unit-distance conjecture is
false** (Alpöge, 2026): for every `C > 0` and every threshold `N` there
exist `n ≥ N` and an `n`-point set `P ⊆ ℝ²` with more than
`n^(1 + C / log log n)` unit-distance pairs.

[medium given everything above; glue + parameter choice]
Sketch: given `C` and `N`, let `c₀, c₁` be the constants of
`log_classNumber_Kf_le` and `log_m_le`.  Choose
`g = ⌈41·C·c₁·log (t+2) / (log 2)²⌉ + 1` and `t` large (depending on
`C, N, c₀, c₁`): then `hgC` holds since `log (m t) + 8 ≤ c₁·(t+8)·log (t+2)`,
and `hth` holds since `log h / 2^g ≤ c₀·(g+1)·log (g+2)` grows only like
`(log t)·(log log t)`.  Use `M = m t`, `h = classNumber (Kf g)`, and the
estimates from `exists_good_pointset`; `n ≥ N` and `n ≥ 16` follow from
the first estimate since `n ≥ 2^(t·2^(g-1)) / (h·2^(2^g)) → ∞` as
`t → ∞` for the chosen `g(t)`. -/
theorem erdos_unit_distance_uniform_constant_false :
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))),
        N ≤ n ∧ P.card = n ∧
        (n : ℝ) ^ (1 + C / Real.log (Real.log n)) < (unitDist P : ℝ) := by
  sorry

end Assembly

end Erdos
