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
  rw [ unitDist, Nat.mul_div_cancel' ];
  -- Since `unitPairsC P` counts the number of ordered pairs `(x, y)` with `x ≠ y` and `dist x y = 1`, we can pair each such pair with `(y, x)`.
  have h_pair : ∃ S : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), {pq ∈ P.offDiag | dist pq.1 pq.2 = 1} = S ∪ S.image Prod.swap ∧ Disjoint S (S.image Prod.swap) := by
    refine' ⟨ Finset.filter ( fun pq => pq.1 0 < pq.2 0 ∨ pq.1 0 = pq.2 0 ∧ pq.1 1 < pq.2 1 ) ( Finset.filter ( fun pq => dist pq.1 pq.2 = 1 ) ( P.offDiag ) ), _, _ ⟩;
    · ext ⟨ x, y ⟩ ; simp +decide [ dist_comm ] ;
      cases lt_trichotomy ( x 0 ) ( y 0 ) <;> cases lt_trichotomy ( x 1 ) ( y 1 ) <;> simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      · aesop;
      · aesop;
      · grind +revert;
      · grind;
    · norm_num [ Finset.disjoint_right ];
      grind;
  obtain ⟨ S, hS₁, hS₂ ⟩ := h_pair; rw [ hS₁, Finset.card_union_of_disjoint hS₂, Finset.card_image_of_injective _ Prod.swap_injective ] ; simp +decide [ ← two_mul ] ;

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
  refine' ⟨ Finset.image ( fun z => complexToPlane z ) P, _, _ ⟩;
  · exact Finset.card_image_of_injective _ complexToPlane.injective;
  · convert two_mul_unitDist ( Finset.image ( fun z => complexToPlane z ) P ) using 1;
    refine' Finset.card_bij ( fun pq hpq => ( complexToPlane pq.1, complexToPlane pq.2 ) ) _ _ _ <;> simp +decide;
    · grind;
    · rintro a b x hx rfl y hy rfl hab h; use x, y; aesop;

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

private lemma cell_index_mem {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri)
    {t : ℝ} (ht : |t| ≤ c * ri) :
    ⌊(t + c * ri) / (ε * ri / Real.sqrt 2)⌋ ∈
      Finset.Icc (0 : ℤ) ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℤ) := by
  refine' Finset.mem_Icc.mpr ⟨ Int.floor_nonneg.mpr _, Int.le_of_lt_add_one ( Int.floor_lt.mpr _ ) ⟩;
  · exact div_nonneg ( by linarith [ abs_le.mp ht ] ) ( by positivity );
  · rw [ div_lt_iff₀ ] <;> norm_num;
    · rw [ ← mul_div_assoc, lt_div_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one ( 2 * Real.sqrt 2 * c / ε ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_pos hε hri, mul_div_cancel₀ ( 2 * Real.sqrt 2 * c ) hε.ne', abs_le.mp ht ];
    · positivity

/-
Helper: two real coordinates with the same cell index differ by less than the
cell side `ε*ri/√2`.
-/
private lemma cell_index_diff {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri)
    {a b : ℝ}
    (h : ⌊(a + c * ri) / (ε * ri / Real.sqrt 2)⌋
        = ⌊(b + c * ri) / (ε * ri / Real.sqrt 2)⌋) :
    |a - b| < ε * ri / Real.sqrt 2 := by
  rw [ Int.floor_eq_iff ] at h;
  rw [ abs_lt ] ; constructor <;> nlinarith [ Int.floor_le ( ( b + c * ri ) / ( ε * ri / Real.sqrt 2 ) ), Int.lt_floor_add_one ( ( b + c * ri ) / ( ε * ri / Real.sqrt 2 ) ), show 0 < ε * ri / Real.sqrt 2 by positivity, mul_div_cancel₀ ( a + c * ri ) ( show ε * ri / Real.sqrt 2 ≠ 0 by positivity ), mul_div_cancel₀ ( b + c * ri ) ( show ε * ri / Real.sqrt 2 ≠ 0 by positivity ) ] ;

/-
Helper: a complex number whose real and imaginary parts are each `< d` in
absolute value has norm `< d * √2`.
-/
private lemma norm_lt_of_re_im_bound {z : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hre : |z.re| < d) (him : |z.im| < d) : ‖z‖ < d * Real.sqrt 2 := by
  rw [ ← Real.sqrt_sq ( show 0 ≤ d by assumption ) ];
  rw [ ← Real.sqrt_mul <| by positivity ] ; refine' Real.sqrt_lt_sqrt _ _;
  · exact Complex.normSq_nonneg _;
  · nlinarith [ abs_lt.mp hre, abs_lt.mp him, Complex.normSq_apply z ]

/-
Helper: the per-axis cell count `⌊2√2 c/ε⌋₊ + 1` is at most `4c/ε`
(using `ε ≤ c`, i.e. `c/ε ≥ 1`).
-/
private lemma cellCount_le {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) :
    ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℝ) + 1 ≤ 4 * c / ε := by
  by_contra h_contra;
  exact h_contra <| by have := Nat.floor_le ( show 0 ≤ 2 * Real.sqrt 2 * c / ε by exact div_nonneg ( mul_nonneg ( mul_nonneg zero_le_two <| Real.sqrt_nonneg _ ) <| by linarith ) <| by linarith ) ; rw [ le_div_iff₀ <| by linarith ] at *; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ ( 2 * Real.sqrt 2 * c ) <| ne_of_gt hε ] ;

/-
[medium] **Grid pigeonhole.**  A subset of the polydisc `box r c` whose
distinct elements are `ε`-separated in some coordinate (relative to `r`)
is finite, of cardinality at most `(4 * c / ε) ^ (2 * #ι)`.
Sketch: partition each coordinate disc of radius `c * r i` into half-open
square cells of side `ε * r i / √2`; there are at most
`⌈2√2 * c/ε⌉² ≤ (4c/ε)²` cells per coordinate (using `ε ≤ c`).  Map each
point to its tuple of cell indices: two points with the same tuple differ
by at most `ε * r i` in every coordinate, contradicting separation; so the
map into `ι → (Fin M × Fin M)` is injective.
-/
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
  -- Let's define the cell map and the finite codomain.
  set δ : ι → ℝ := fun i => ε * r i / Real.sqrt 2
  set K : ℤ := (⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℤ)
  set T : Finset (ι → ℤ × ℤ) := Fintype.piFinset (fun _ : ι => (Finset.Icc (0:ℤ) K) ×ˢ (Finset.Icc (0:ℤ) K));
  -- Define the cell map `g` and show that it maps `S` into `T`.
  set g : (ι → ℂ) → (ι → ℤ × ℤ) := fun x i => (⌊((x i).re + c * r i) / δ i⌋, ⌊((x i).im + c * r i) / δ i⌋)
  have hg : ∀ x ∈ S, g x ∈ T := by
    intro x hx;
    simp +zetaDelta at *;
    intro i; exact ⟨ ⟨ cell_index_mem hε ( hr i ) ( show |( x i |> Complex.re )| ≤ c * r i from by simpa using Complex.abs_re_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.left, cell_index_mem hε ( hr i ) ( show |( x i |> Complex.re )| ≤ c * r i from by simpa using Complex.abs_re_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.right ⟩, ⟨ cell_index_mem hε ( hr i ) ( show |( x i |> Complex.im )| ≤ c * r i from by simpa using Complex.abs_im_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.left, cell_index_mem hε ( hr i ) ( show |( x i |> Complex.im )| ≤ c * r i from by simpa using Complex.abs_im_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.right ⟩ ⟩ ;
  -- Show that `g` is injective on `S`.
  have hg_inj : Set.InjOn g S := by
    intros x hx y hy hxy
    by_contra hxy_ne
    obtain ⟨i, hi⟩ := hsep x hx y hy hxy_ne
    have h_diff : ‖x i - y i‖ < δ i * Real.sqrt 2 := by
      apply norm_lt_of_re_im_bound;
      · exact div_nonneg ( mul_nonneg hε.le ( le_of_lt ( hr i ) ) ) ( Real.sqrt_nonneg _ );
      · simpa [Complex.sub_re] using
          cell_index_diff (c := c) hε (hr i)
            (by simpa using congr_arg Prod.fst (congr_fun hxy i));
      · simpa [Complex.sub_im] using
          cell_index_diff (c := c) hε (hr i)
            (by simpa using congr_arg Prod.snd (congr_fun hxy i));
    rw [ div_mul_cancel₀ _ ( by positivity ) ] at h_diff ; linarith;
  -- Conclude that `S` is finite and its cardinality is bounded by `T.card`.
  have h_finite : S.Finite := by
    exact Set.Finite.of_finite_image ( Set.Finite.subset ( Finset.finite_toSet T ) ( Set.image_subset_iff.mpr hg ) ) hg_inj
  have h_card : (S.ncard : ℝ) ≤ T.card := by
    have := Set.InjOn.ncard_image hg_inj;
    exact_mod_cast this ▸ Set.ncard_le_ncard ( show g '' S ⊆ T from Set.image_subset_iff.mpr hg ) |> le_trans <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ;
  refine ⟨ h_finite, h_card.trans ?_ ⟩;
  convert pow_le_pow_left₀ ( by positivity ) ( cellCount_le hε hεc ) ( 2 * Fintype.card ι ) using 1 ; norm_num [ Finset.card_univ, pow_mul ];
  erw [ Fintype.card_piFinset ] ; norm_num [ pow_mul ];
  norm_cast ; ring_nf!
  rw [ pow_mul' ] ; norm_cast ; ring_nf!

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
  convert finite_and_card_le_of_separated r hr ( show 0 < ρ by linarith ) ( show ρ ≤ 2 by linarith ) ( show ( Λ : Set ( ι → ℂ ) ) ∩ box r 2 ⊆ box r 2 by exact Set.inter_subset_right ) _ using 1;
  · norm_num;
  · exact fun x hx y hy hxy => hsep ( x - y ) ( Λ.sub_mem hx.1 hy.1 ) ( sub_ne_zero_of_ne hxy ) |> fun ⟨ i, hi ⟩ => ⟨ i, by simpa using hi ⟩

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
  -- Let `A := (Λ : Set _) ∩ box r 2` and `B := (Λ : Set _) ∩ box r 1`.
  set A : Set (ι → ℂ) := Λ ∩ box r 2
  set B : Set (ι → ℂ) := Λ ∩ box r 1;
  obtain ⟨sA, hsA⟩ : ∃ sA : Finset (ι → ℂ), A = sA := by
    exact ⟨ hfin.toFinset, hfin.coe_toFinset.symm ⟩
  obtain ⟨sB, hsB⟩ : ∃ sB : Finset (ι → ℂ), B = sB := by
    have hBfin : B.Finite := by
      exact hfin.subset fun x hx => ⟨ hx.1, fun i => le_trans ( hx.2 i ) ( mul_le_mul_of_nonneg_right ( by norm_num ) ( le_of_lt ( hr i ) ) ) ⟩
    exact ⟨hBfin.toFinset, by simp⟩
  simp_all +decide [ Set.ncard_eq_toFinset_card' ];
  -- Apply `Finset.card_le_mul_card_image sA f (B.ncard)` to get `sA.card ≤ B.ncard * (sA.image f).card`.
  have h_card_le_mul_card_image : sA.card ≤ sB.card * (sA.image (fun x => fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋))).card := by
    have h_card_le_mul_card_image : ∀ b ∈ sA.image (fun x => fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)), (sA.filter (fun a => (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) a = b)).card ≤ sB.card := by
      intro b hb
      obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ sA, (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) x₀ = b := by
        aesop
      have h_fiber : ∀ y ∈ sA, (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) y = b → y - x₀ ∈ sB := by
        intro y hy hyb
        have h_diff : ∀ i, ‖(y i - x₀ i)‖ ≤ r i := by
          intro i
          have h_diff_re : |(y i).re - (x₀ i).re| ≤ 2 * r i / 3 := by
            have h_diff_re : ⌊(y i).re / (2 * r i / 3)⌋ = ⌊(x₀ i).re / (2 * r i / 3)⌋ := by
              replace hyb := congr_fun hyb i; replace hx₀ := congr_fun hx₀.2 i; aesop;
            rw [ Int.floor_eq_iff ] at h_diff_re;
            rw [ abs_le ] ; constructor <;> nlinarith [ hr i, Int.floor_le ( ( x₀ i |> Complex.re ) / ( 2 * r i / 3 ) ), Int.lt_floor_add_one ( ( x₀ i |> Complex.re ) / ( 2 * r i / 3 ) ), mul_div_cancel₀ ( ( y i |> Complex.re ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ), mul_div_cancel₀ ( ( x₀ i |> Complex.re ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ] ;
          have h_diff_im : |(y i).im - (x₀ i).im| ≤ 2 * r i / 3 := by
            have h_diff_im : ⌊(y i).im / (2 * r i / 3)⌋ = ⌊(x₀ i).im / (2 * r i / 3)⌋ := by
              replace hyb := congr_fun hyb i; replace hx₀ := congr_fun hx₀.2 i; aesop;
            rw [ Int.floor_eq_iff ] at h_diff_im;
            rw [ abs_le ];
            constructor <;> nlinarith [ hr i, Int.floor_le ( ( x₀ i |> Complex.im ) / ( 2 * r i / 3 ) ), Int.lt_floor_add_one ( ( x₀ i |> Complex.im ) / ( 2 * r i / 3 ) ), mul_div_cancel₀ ( ( y i |> Complex.im ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ), mul_div_cancel₀ ( ( x₀ i |> Complex.im ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ];
          norm_num [ Complex.normSq, Complex.norm_def ] at *;
          exact Real.sqrt_le_iff.mpr ⟨ by linarith [ hr i ], by nlinarith [ abs_le.mp h_diff_re, abs_le.mp h_diff_im ] ⟩;
        exact hsB.subset ⟨ Λ.sub_mem ( hsA.symm.subset hy |>.1 ) ( hsA.symm.subset hx₀.1 |>.1 ), fun i => by simpa using h_diff i ⟩
      have h_fiber_card : (sA.filter (fun a => (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) a = b)).card ≤ (sB.image (fun y => y + x₀)).card := by
        exact Finset.card_le_card fun x hx => Finset.mem_image.mpr ⟨ x - x₀, h_fiber x ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hx |>.2 ), by simp +decide ⟩ ;
      exact h_fiber_card.trans (Finset.card_image_le);
    exact Finset.card_le_mul_card_image sA sB.card h_card_le_mul_card_image
  -- The image of `sA` under `f` is a subset of `T := Fintype.piFinset (fun _ : ι => (Finset.Icc (-3:ℤ) 3) ×ˢ (Finset.Icc (-3:ℤ) 3))`.
  have h_image_subset_T : sA.image (fun x => fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) ⊆ Fintype.piFinset (fun _ : ι => (Finset.Icc (-3:ℤ) 3) ×ˢ (Finset.Icc (-3:ℤ) 3)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simp [Fintype.piFinset];
    refine' ⟨ fun i _ => ( ⌊ ( y i |> Complex.re ) / ( 2 * r i / 3 ) ⌋, ⌊ ( y i |> Complex.im ) / ( 2 * r i / 3 ) ⌋ ), _, _ ⟩ <;> simp +decide;
    intro i
    have h_bound : |(y i).re| ≤ 2 * r i ∧ |(y i).im| ≤ 2 * r i := by
      exact ⟨ le_trans ( Complex.abs_re_le_norm _ ) ( hsA.symm.subset hy |>.2 i ), le_trans ( Complex.abs_im_le_norm _ ) ( hsA.symm.subset hy |>.2 i ) ⟩;
    exact ⟨ ⟨ Int.le_floor.2 <| by norm_num; nlinarith [ abs_le.mp h_bound.1, hr i, mul_div_cancel₀ ( ( y i |> Complex.re ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; nlinarith [ abs_le.mp h_bound.1, hr i, mul_div_cancel₀ ( ( y i |> Complex.re ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ] ⟩, ⟨ Int.le_floor.2 <| by norm_num; nlinarith [ abs_le.mp h_bound.2, hr i, mul_div_cancel₀ ( ( y i |> Complex.im ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; nlinarith [ abs_le.mp h_bound.2, hr i, mul_div_cancel₀ ( ( y i |> Complex.im ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ] ⟩ ⟩;
  -- The cardinality of `T` is `64 ^ Fintype.card ι`.
  have h_card_T : (Fintype.piFinset (fun _ : ι => (Finset.Icc (-3:ℤ) 3) ×ˢ (Finset.Icc (-3:ℤ) 3))).card ≤ 64 ^ Fintype.card ι := by
    simp +decide [ Fintype.piFinset ];
    gcongr ; norm_num;
  exact_mod_cast h_card_le_mul_card_image.trans ( Nat.mul_le_mul_left _ ( Finset.card_le_card h_image_subset_T |> le_trans <| h_card_T ) ) |> le_trans <| by ring_nf; norm_num;

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
  refine' ⟨ _, _ ⟩;
  · rw [ Finset.card_image_of_injOn, ← Set.ncard_coe_finset, hfin.coe_toFinset ];
    intro x hx y hy; specialize hinj ( x - y ) ; simp_all +decide [ sub_eq_zero ] ;
    simp_all +decide [ proj, div_eq_iff, ne_of_gt ( hr i₀ ) ];
    exact fun h => hinj ( Λ.sub_mem hx.1 hy.1 ) h;
  · refine' le_trans _ ( Finset.card_mono _ );
    rotate_left;
    exact Finset.image ( fun p : ( ι → ℂ ) × ( ι → ℂ ) => ( p.2 i₀ / r i₀, ( p.2 + p.1 ) i₀ / r i₀ ) ) ( Z ×ˢ ( hfin.toFinset.filter fun x => ∀ i, ‖x i‖ ≤ r i ) );
    · intro; simp +decide [ dist_eq_norm ] ;
      rintro x y hx hy hxy hy' rfl; simp_all +decide [ proj, box ] ;
      refine' ⟨ ⟨ ⟨ y, ⟨ hy, hxy ⟩, rfl ⟩, ⟨ y + x, ⟨ Λ.add_mem hy ( hZΛ x hx ), fun i => _ ⟩, _ ⟩, _ ⟩, _ ⟩ <;> simp_all +decide [ add_div, ne_of_gt ];
      · exact le_trans ( norm_add_le _ _ ) ( by linarith [ hy' i, hZr x hx i ] );
      · exact fun h => by have := hZr x hx i₀; norm_num [ h ] at this; linarith [ hr i₀ ] ;
      · rw [ abs_of_pos ( hr i₀ ), div_self ( ne_of_gt ( hr i₀ ) ) ];
    · rw [ Finset.card_image_of_injOn ];
      · simp +zetaDelta at *;
        gcongr;
        rw [ ← Set.ncard_coe_finset ];
        fapply Set.ncard_le_ncard;
        · simp +contextual [ Set.subset_def, box ];
          exact fun x hx hx' i => le_trans ( hx' i ) ( le_mul_of_one_le_left ( le_of_lt ( hr i ) ) ( by norm_num ) );
        · exact hfin.toFinset.finite_toSet.subset fun x hx => by aesop;
      · intro p hp q hq h; simp_all +decide [ div_eq_iff, ne_of_gt ( hr _ ) ] ;
        have h_eq : p.1 = q.1 := by
          specialize hinj ( p.1 - q.1 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
          exact hinj ( by simpa using Λ.sub_mem ( hZΛ _ hp.1 ) ( hZΛ _ hq.1 ) ) ( by aesop );
        specialize hinj ( p.2 - q.2 ) ; simp_all +decide [ sub_eq_iff_eq_add ];
        exact Prod.ext h_eq ( hinj ( Λ.sub_mem hp.1.1 hq.2.1.1 ) )

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
  obtain ⟨hfin, hupper⟩ := lattice_inter_box_finite_card r hr Λ hρ0 hρ2 hsep;
  obtain ⟨hcard, hpairs⟩ := le_unitPairsC_of_translates i₀ r hr Λ hinj hfin Z hZΛ hZr;
  obtain ⟨Q, hQcard, hQunit⟩ := exists_euclidean_copy (hfin.toFinset.image (proj r i₀));
  refine' ⟨ Q.card, Q, rfl, _, _, _ ⟩ <;> norm_cast at * <;> simp_all +decide [ mul_comm ];
  · refine' le_trans _ ( Set.ncard_le_ncard ( show ( ↑Z : Set ( ι → ℂ ) ) ⊆ ( Λ : Set ( ι → ℂ ) ) ∩ box r 2 from _ ) hfin );
    · rw [ Set.ncard_coe_finset ];
    · exact fun x hx => ⟨ hZΛ x hx, fun i => by simpa [ hZr x hx i ] using by nlinarith [ hr i ] ⟩;
  · have hdbl := ncard_box_two_le_doubling r hr Λ hfin; norm_cast at *; simp_all +decide ;
    nlinarith [ pow_pos ( by norm_num : ( 0 : ℕ ) < 64 ) ( Fintype.card ι ) ]

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
  have h : {p : ℕ | p.Prime ∧ p ≡ 3 [MOD 4]}.Infinite :=
    Nat.infinite_setOf_prime_and_modEq (by norm_num) (by decide)
  simpa [Nat.ModEq] using h


/-- [easy] There are infinitely many primes `≡ 1 mod 4`.
(Proved by Aristotle, 2026-06-11.) -/
theorem infinite_setOf_p1 : {n | n.Prime ∧ n % 4 = 1}.Infinite :=
  Nat.infinite_setOf_prime_modEq_one <| by decide

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
quantitative argument, or any future PNT-in-AP development.

**Proved** (2026-06-11) in the companion project `pnt-bounds`
(`PntBounds/PolyBounds.lean`, via PrimeNumberTheoremAnd's sorry-free
`chebyshev_asymptotic_pnt` and the Mathlib-only reduction
`nth_le_sq_of_count_ge`); kept as `sorry` here only because Mathlib
cannot depend on PrimeNumberTheoremAnd. -/
theorem q3_poly_bound : ∀ᶠ j in Filter.atTop, (q3 j : ℝ) ≤ (j + 2) ^ 2 := by
  sorry

/-- [HARD] Polynomial growth of the `i`-th prime `≡ 1 mod 4`.  See
`q3_poly_bound` (also proved in the `pnt-bounds` companion project). -/
theorem p1_poly_bound : ∀ᶠ i in Filter.atTop, (p1 i : ℝ) ≤ (i + 2) ^ 2 := by
  sorry

/-- [easy] `m t ≥ 2^t` (each prime factor is `≥ 5`). -/
theorem m_ge (t : ℕ) : 2 ^ t ≤ m t := by
  calc 2 ^ t = ∏ _i ∈ Finset.range t, 2 := by simp
  _ ≤ m t := Finset.prod_le_prod' fun i _ => (p1_spec i).1.two_le

/-- [medium given `p1_poly_bound`] The logarithm of `m t` grows like
`t log t` up to constants: there is `c₁ ≥ 1` with
`log (m t) ≤ c₁ * t * log (t + 2)` for all `t`.  Sketch:
`log (m t) = ∑_{i<t} log (p1 i)`; bound all but finitely many summands by
`2 log (i + 2) ≤ 2 log (t + 2)` using `p1_poly_bound` and absorb the
finitely many exceptions into `c₁`. -/
theorem log_m_le : ∃ c₁ : ℝ, 1 ≤ c₁ ∧
    ∀ t : ℕ, Real.log (m t) ≤ c₁ * t * Real.log (t + 2) := by
  -- Let $N$ be a number such that for all $i \geq N$, $p1(i) \leq (i + 2)^2$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ≥ N, (p1 i : ℝ) ≤ (i + 2) ^ 2 := by
    exact Filter.eventually_atTop.mp ( p1_poly_bound ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun i hi => mod_cast hN i hi ⟩;
  -- Let $S = \sum_{i=0}^{N-1} \log(p1(i))$.
  set S := ∑ i ∈ Finset.range N, Real.log (p1 i) with hS_def
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| p1_spec _ |>.1;
  -- We'll use that $Real.log (m t) \leq S + 2 * t * Real.log (t + 2)$ for all $t$.
  have h_log_m_le : ∀ t : ℕ, Real.log (m t) ≤ S + 2 * t * Real.log (t + 2) := by
    intro t
    have h_log_m_le_step : ∀ i < t, Real.log (p1 i) ≤ 2 * Real.log (t + 2) + (if i < N then Real.log (p1 i) else 0) := by
      intro i hi; split_ifs <;> simp_all +decide ;
      · exact Real.log_nonneg ( by linarith );
      · exact le_trans ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| p1_spec i |>.1 ) <| hN i ‹_› ) <| by rw [ Real.log_pow ] ; norm_num ; gcongr;
    have h_log_m_le_step : Real.log (m t) ≤ ∑ i ∈ Finset.range t, (2 * Real.log (t + 2) + (if i < N then Real.log (p1 i) else 0)) := by
      have hm_log : Real.log (m t) = ∑ i ∈ Finset.range t, Real.log (p1 i) := by
        rw [ ← Real.log_prod ] <;> norm_cast ; norm_num [ m ];
        exact fun i hi => Nat.Prime.ne_zero ( p1_spec i |>.1 );
      rw [hm_log]
      exact Finset.sum_le_sum fun i hi => h_log_m_le_step i ( Finset.mem_range.mp hi );
    simp_all +decide [ Finset.sum_add_distrib, Finset.sum_ite ];
    exact h_log_m_le_step.trans ( by rw [ add_comm ] ; exact add_le_add ( Finset.sum_le_sum_of_subset_of_nonneg ( fun i hi => by aesop ) fun _ _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| by have := p1_spec ‹_›; aesop ) <| by nlinarith );
  refine' ⟨ Max.max 1 ( 2 + S / Real.log 3 ), _, _ ⟩ <;> norm_num;
  intro t; specialize h_log_m_le t; rcases eq_or_ne t 0 <;> simp_all +decide [ mul_assoc ] ;
  · unfold m; norm_num;
  · rw [ max_def ] ; split_ifs <;> nlinarith [ show ( t : ℝ ) * Real.log ( t + 2 ) ≥ Real.log 3 by exact le_trans ( Real.log_le_log ( by positivity ) ( by norm_cast; linarith [ Nat.pos_of_ne_zero ‹_› ] ) ) ( le_mul_of_one_le_left ( Real.log_nonneg ( by linarith ) ) ( mod_cast Nat.one_le_iff_ne_zero.mpr ‹_› ) ), Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ), mul_div_cancel₀ ( ∑ i ∈ Finset.range N, Real.log ( p1 i ) ) ( ne_of_gt ( Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ) ) ) ] ;

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
  refine' IntermediateField.finiteDimensional_adjoin _
  simp +zetaDelta at *
  refine ⟨?_, ?_⟩
  · exact Complex.isIntegral_rat_I
  · intro a ha
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (q3 a : ℚ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
    · norm_num [← Polynomial.C_pow]
      norm_cast
      rw [Real.sq_sqrt <| Nat.cast_nonneg _]
      ring

noncomputable instance (g : ℕ) : NumberField (Kf g) :=
  { to_charZero := inferInstance
    to_finiteDimensional := Kf_finiteDimensional g }

section MultiquadraticDegree

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
    exact IntermediateField.restrictScalars_adjoin_eq_sup ℚ K ({x} : Set E)
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

end MultiquadraticDegree

/-- [medium-easy] `K_g` is totally complex: it contains `i`, and a real
embedding would send `i` to a real square root of `-1`.
Sketch: for `w : InfinitePlace (Kf g)`, if `w` were real, its embedding
`φ : Kf g →+* ℂ` composed with conjugation equals itself; but
`φ ⟨i, _⟩² = -1` forces `φ ⟨i, _⟩ = ±I`, which is not conjugation-fixed. -/
theorem Kf_isTotallyComplex (g : ℕ) : NumberField.IsTotallyComplex (Kf g) := by
  have hI : Complex.I ∈ Kf g :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  refine ⟨fun v => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hreal
  have hφ : NumberField.ComplexEmbedding.conjugate v.embedding = v.embedding :=
    NumberField.ComplexEmbedding.isReal_iff.mp
      (NumberField.InfinitePlace.isReal_iff.mp hreal)
  set x : Kf g := ⟨Complex.I, hI⟩ with hx
  have hx2 : x ^ 2 = -1 := by
    apply Subtype.ext
    push_cast [hx, sq, Complex.I_mul_I]
    ring
  set z : ℂ := v.embedding x with hz
  have key : z ^ 2 = -1 := by
    rw [hz, ← map_pow, hx2, map_neg, map_one]
  have hconj : (starRingEnd ℂ) z = z := by
    have := RingHom.congr_fun hφ x
    simpa [hz, NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hre : z.re ^ 2 = -1 := by
    have h := congrArg Complex.re key
    simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
      Complex.one_re] at h
    rw [← pow_two] at h
    exact h
  nlinarith [sq_nonneg z.re, hre]


noncomputable instance (g : ℕ) : NumberField.IsTotallyComplex (Kf g) :=
  Kf_isTotallyComplex g

theorem Kf_isGalois (g : ℕ) : IsGalois ℚ (Kf g) := by
  apply_rules [ IsGalois.mk ];
  apply_rules [ normal_iff.mpr ];
  intro x
  have h_integral : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have h_splits : (Polynomial.map (algebraMap ℚ (Kf g)) (minpoly ℚ x)).Splits := by
    have h_minpoly : ∀ s ∈ (IntermediateField.adjoin ℚ (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g))).toSubalgebra, (Polynomial.map (algebraMap ℚ (Kf g)) (minpoly ℚ s)).Splits := by
      apply IntermediateField.splits_of_mem_adjoin;
      intro x hx
      have h_minpoly : (Polynomial.map (algebraMap ℚ (Kf g)) (minpoly ℚ x)).Splits := by
        rcases hx with ( rfl | ⟨ j, hj, rfl ⟩ );
        · rw [ show minpoly ℚ Complex.I = Polynomial.X ^ 2 + 1 from ?_ ];
          · rw [ Polynomial.splits_iff_exists_multiset ];
            use {⟨Complex.I, by
              exact IntermediateField.subset_adjoin ℚ _ ( Set.mem_insert _ _ )⟩, ⟨-Complex.I, by
              exact Subalgebra.neg_mem _ ( IntermediateField.subset_adjoin ℚ _ <| Set.mem_insert _ _ )⟩}
            generalize_proofs at *;
            refine' Polynomial.funext fun x => _;
            ext ; norm_num ; ring;
            norm_num [ sub_eq_add_neg ];
            ring;
          · refine' Eq.symm ( minpoly.eq_of_irreducible_of_monic _ _ _ );
            · -- We'll use that $X^2 + 1$ is the cyclotomic polynomial $\Phi_4(X)$.
              have h_cyclotomic : Polynomial.X ^ 2 + 1 = Polynomial.cyclotomic 4 ℚ := by
                rw [ show ( 4 : ℕ ) = 2 ^ 2 by norm_num, Polynomial.cyclotomic_prime_pow_eq_geom_sum ] ; norm_num;
                norm_num;
              exact h_cyclotomic ▸ Polynomial.cyclotomic.irreducible_rat ( by decide );
            · norm_num;
            · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_add_C ] ; norm_num;
        · have h_minpoly : minpoly ℚ ((Real.sqrt (q3 j) : ℝ) : ℂ) = Polynomial.X ^ 2 - Polynomial.C (q3 j : ℚ) := by
            refine' Eq.symm ( minpoly.eq_of_irreducible_of_monic _ _ _ );
            · -- The polynomial $X^2 - q3 j$ is irreducible over $\mathbb{Q}$ because $q3 j$ is not a perfect square.
              have h_irred : ¬∃ (r : ℚ), r^2 = q3 j := by
                have h_not_square : ¬∃ (r : ℤ), r^2 = q3 j := by
                  have := q3_spec j;
                  exact fun ⟨ r, hr ⟩ => by have := congr_arg ( · % 4 ) hr; norm_num [ sq, Int.add_emod, Int.mul_emod ] at this; have := Int.emod_nonneg r four_pos.ne'; have := Int.emod_lt_of_pos r four_pos; interval_cases r % 4 <;> norm_cast at * <;> simp_all +decide ;
                exact fun ⟨ r, hr ⟩ => h_not_square ⟨ r.num, by simpa only [ sq, Rat.mul_self_num, Rat.num_natCast ] using congr_arg Rat.num hr ⟩;
              -- Since $q3 j$ is not a perfect square, the polynomial $X^2 - q3 j$ is irreducible over $\mathbb{Q}$.
              have h_irred : ∀ p q : Polynomial ℚ, p.degree > 0 → q.degree > 0 → p * q = Polynomial.X ^ 2 - Polynomial.C (q3 j : ℚ) → False := by
                intros p q hp hq h_eq
                have h_deg : p.degree = 1 ∧ q.degree = 1 := by
                  have h_deg : p.degree + q.degree = 2 := by
                    rw [ ← Polynomial.degree_mul, h_eq, Polynomial.degree_sub_C ] <;> norm_num;
                  rw [ Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hp ), Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hq ) ] at * ; norm_cast at * ; exact ⟨ by linarith, by linarith ⟩;
                obtain ⟨r, hr⟩ : ∃ r : ℚ, p.eval r = 0 := by
                  exact Polynomial.exists_root_of_degree_eq_one h_deg.1;
                exact h_irred ⟨ r, by replace h_eq := congr_arg ( Polynomial.eval r ) h_eq; norm_num [ hr ] at h_eq; linarith ⟩;
              constructor <;> contrapose! h_irred;
              · exact absurd ( Polynomial.degree_eq_zero_of_isUnit h_irred ) ( by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num );
              · obtain ⟨ a, b, h₁, h₂, h₃ ⟩ := h_irred; exact ⟨ a, b, not_le.mp fun h => h₂ <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by { apply_fun Polynomial.eval 0 at h₁; aesop }, not_le.mp fun h => h₃ <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by { apply_fun Polynomial.eval 0 at h₁; aesop }, h₁.symm, trivial ⟩ ;
            · norm_num [ ← Complex.ofReal_pow ];
            · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
          rw [ h_minpoly, Polynomial.splits_iff_exists_multiset ];
          refine' ⟨ { ⟨ ( Real.sqrt ( q3 j ) : ℝ ) , _ ⟩, ⟨ - ( Real.sqrt ( q3 j ) : ℝ ), _ ⟩ }, _ ⟩ <;> norm_num;
          any_goals exact IntermediateField.subset_adjoin ℚ _ ( Set.mem_insert_of_mem _ <| Set.mem_image_of_mem _ hj );
          refine' Polynomial.funext fun x => _;
          erw [ Polynomial.leadingCoeff_X_pow_sub_C ] <;> norm_num ; ring;
          ext ; norm_num ; ring;
          norm_num [ ← Complex.ofReal_pow ]
      exact ⟨by
      cases hx <;> simp_all +decide [ Complex.ext_iff ];
      · rw [ show x = Complex.I by simpa [ Complex.ext_iff ] using ‹x.re = 0 ∧ x.im = 1› ] ; exact ⟨ Polynomial.X ^ 2 + 1, by exact Polynomial.monic_X_pow_add_C _ two_ne_zero, by norm_num ⟩ ;
      · obtain ⟨ j, hj, hx₁, hx₂ ⟩ := ‹_›; use Polynomial.X ^ 2 - Polynomial.C ( q3 j : ℚ ) ; norm_num [ hx₁, hx₂ ] ; ring;
        exact ⟨ Polynomial.monic_X_pow_sub_C _ two_ne_zero, by rw [ show x = Real.sqrt ( q3 j ) by simp [ Complex.ext_iff, hx₁.symm, hx₂.symm ] ] ; norm_num [ ← Complex.ofReal_pow, Real.sq_sqrt ( Nat.cast_nonneg _ ) ] ⟩, h_minpoly⟩;
    have hx2 := h_minpoly x x.2
    rwa [show minpoly ℚ (x : ℂ) = minpoly ℚ x from
      minpoly.algHom_eq (Kf g).val (Kf g).val.injective x] at hx2
  exact ⟨h_integral, h_splits⟩

/-
[helper] Every ℚ-automorphism of `K_g` is an involution.  Each
generator `x` (`i` or `√q3 j`) satisfies `x² ∈ ℚ`, so `σ x` is a root of
`X² - x²`, hence `σ x = ±x`; therefore `σ (σ x) = x` on generators and
`σ ∘ σ = id` on all of `K_g`.
-/
theorem Kf_aut_involutive (g : ℕ) (σ : Kf g ≃ₐ[ℚ] Kf g) : σ * σ = 1 := by
  have hext : ((σ * σ : Kf g ≃ₐ[ℚ] Kf g) : Kf g →ₐ[ℚ] Kf g)
      = ((1 : Kf g ≃ₐ[ℚ] Kf g) : Kf g →ₐ[ℚ] Kf g) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := Kf g)
      (s := insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g))
      rfl ?_
    intro x hx
    set y : Kf g := ⟨x, (rfl : Kf g = _).ge (IntermediateField.subset_adjoin _ _ hx)⟩
      with hy
    have hsq : ∃ c : ℚ, y ^ 2 = algebraMap ℚ (Kf g) c := by
      rcases hx with rfl | ⟨j, hj, rfl⟩
      · refine ⟨-1, Subtype.ext ?_⟩
        push_cast [hy]
        simp [Complex.I_sq]
      · refine ⟨(q3 j : ℚ), Subtype.ext ?_⟩
        push_cast [hy]
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
        norm_num
    obtain ⟨c, hc⟩ := hsq
    have h1 : (σ y) ^ 2 = y ^ 2 := by
      rw [← map_pow, hc, AlgEquiv.commutes]
    have h2 : σ y = y ∨ σ y = -y := sq_eq_sq_iff_eq_or_eq_neg.mp h1
    show σ (σ y) = y
    rcases h2 with h | h
    · rw [h, h]
    · rw [h, map_neg, h, neg_neg]
  exact AlgEquiv.coe_algHom_injective hext

/-- [medium] `K_g/ℚ` is an abelian Galois extension.  Sketch: it is the
splitting field of `(X² + 1) ∏_j (X² - q3 j)` (each quadratic generator
brings its conjugate `±` partner), and every `σ ∈ Gal` is determined by
signs `σ(√q3 j) = ±√q3 j`, `σ(i) = ±i`, so all elements square to the
identity and the group is elementary abelian. -/
theorem Kf_isAbelianGalois (g : ℕ) : IsAbelianGalois ℚ (Kf g) := by
  haveI := Kf_isGalois g
  refine { is_comm := ⟨fun a b => ?_⟩ }
  exact Commute.of_orderOf_dvd_two
    (fun σ => orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Kf_aut_involutive g σ)) a b


noncomputable instance (g : ℕ) : IsAbelianGalois ℚ (Kf g) :=
  Kf_isAbelianGalois g

/-- `K_g` is a CM field (instance, from Mathlib's
`NumberField.IsCMField.of_isAbelianGalois`). -/
noncomputable example (g : ℕ) : NumberField.IsCMField (Kf g) := inferInstance

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
  · exact ( IsDedekindDomain.primesOverFinset ( Ideal.under ℤ P ) ( 𝓞 F ) ).card;
  · unfold primeCoord
    simpa using List.idxOf_lt_length_iff.mpr
      (Finset.mem_toList.mpr ( mem_primesOverFinset_under F hP hP0 ));
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
    have hPidx :
        List.idxOf P (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList =
          primeCoord F P := rfl
    have hQidx :
        List.idxOf Q (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList =
          primeCoord F Q := by
      unfold primeCoord
      rw [under_eq_of_ratBelow_eq F hP hP0 hQ hQ0 hr]
    simpa [hPidx, hQidx] using hc
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
    rw [h_prod_le]
    have hprod : (∏ P ∈ (normalizedFactors I).toFinset, P ^ ((normalizedFactors I).count P)) = I := by
      rw [← Finset.prod_multiset_count, Ideal.prod_normalizedFactors_eq_self hI]
    rw [hprod]
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

section Multiquadratic

open scoped Classical
open Polynomial Module

/-- Generic fact: in a number field, an element `x` with `x² ∈ ℚ` but `x ∉ ℚ`
has trace zero, because its minimal polynomial is `X² - r`, whose subleading
coefficient vanishes. -/
theorem trace_eq_zero_of_sq_ratCast {K : Type*} [Field K] [NumberField K] {x : K} {r : ℚ}
    (hx2 : x ^ 2 = algebraMap ℚ K r) (hx : x ∉ (algebraMap ℚ K).range) :
    Algebra.trace ℚ K x = 0 := by
  have hmonic : (X ^ 2 - C r).Monic := Polynomial.monic_X_pow_sub_C r (by norm_num)
  have haeval : aeval x (X ^ 2 - C r : ℚ[X]) = 0 := by simp [hx2]
  have hdvd : minpoly ℚ x ∣ (X ^ 2 - C r) := minpoly.dvd ℚ x haeval
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hne : (X ^ 2 - C r : ℚ[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) r
  have hdeg2 : (minpoly ℚ x).natDegree = 2 := by
    have hle : (minpoly ℚ x).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hne
      simpa [Polynomial.natDegree_X_pow_sub_C] using this
    have hge : 2 ≤ (minpoly ℚ x).natDegree := by
      by_contra h
      push_neg at h
      interval_cases hh : (minpoly ℚ x).natDegree
      · exact (minpoly.natDegree_pos hint).ne' hh
      · exact hx (minpoly.natDegree_eq_one_iff.mp hh)
    omega
  have heq : minpoly ℚ x = X ^ 2 - C r :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      (by rw [hdeg2, Polynomial.natDegree_X_pow_sub_C])).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, heq]
  have hnc : (X ^ 2 - C r : ℚ[X]).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos
      (by rw [Polynomial.natDegree_X_pow_sub_C]; norm_num)]
    simp [Polynomial.coeff_X_pow]
  rw [hnc]; simp

/-
Generic fact: if `b` is a `ℚ`-basis of a number field consisting of
algebraic integers, then `|d_K| ≤ |discr b|`.  (The discriminant of any
basis of integers equals `(index)² · d_K`, and the index is a nonzero
integer.)
-/
theorem abs_discr_le_of_basis_isIntegral {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    |(NumberField.discr K : ℚ)| ≤ |Algebra.discr ℚ (b : ι → K)| := by
  -- Let `c := integralBasis K`, a `ℚ`-basis of `K` indexed by `Free.ChooseBasisIndex ℤ (𝓞 K)`.
  set c := NumberField.integralBasis K;
  -- Reindex `c` to `ι` using `e := c.indexEquiv b` and set `c' := c.reindex e`, a basis indexed by `ι` with `Algebra.discr ℚ c' = Algebra.discr ℚ c` (by `Algebra.discr_reindex`), and `Algebra.discr ℚ c = (NumberField.discr K : ℚ)` (by `NumberField.coe_discr`).
  obtain ⟨e, he⟩ : ∃ e : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ ι, True := by
    refine' ⟨ _, trivial ⟩;
    refine' Fintype.equivOfCardEq _;
    have := Module.finrank_eq_card_basis c;
    rw [ ← this, ← Module.finrank_eq_card_basis b ];
  -- Let `P : Matrix ι ι ℚ := c'.toMatrix b`. By `Module.Basis.toMatrix_map_vecMul`, `b = c' ᵥ* P.map (algebraMap ℚ K)`, so by `Algebra.discr_of_matrix_vecMul`, `Algebra.discr ℚ b = P.det ^ 2 * Algebra.discr ℚ c' = P.det ^ 2 * (NumberField.discr K : ℚ)`.
  set P : Matrix ι ι ℚ := c.reindex e |>.toMatrix b
  have hP : Algebra.discr ℚ b = P.det ^ 2 * (NumberField.discr K : ℚ) := by
    have hP : Algebra.discr ℚ b = P.det ^ 2 * Algebra.discr ℚ (c.reindex e) := by
      convert Algebra.discr_of_matrix_vecMul ( c.reindex e ) P using 1;
      convert rfl;
      convert Module.Basis.toMatrix_map_vecMul ( c.reindex e ) b using 1;
    convert hP using 1;
    simp +decide [ Algebra.discr_reindex ];
    exact Or.inl ( NumberField.coe_discr K );
  -- The matrix `P` has integer entries: `P i j = c'.repr (b j) i = c.repr (b j) (e i)`, and since `b j` is integral over ℤ it lies in `(algebraMap (𝓞 K) K).range`, so by `NumberField.integralBasis_repr_apply` each `c.repr (b j) _` is `algebraMap ℤ ℚ` of an integer, i.e. an integer. Hence `P.det` is an integer: `∃ d : ℤ, P.det = (d : ℚ)` (use `IsIntegrallyClosed.isIntegral_iff` together with `IsIntegral.det`, or directly since each entry is in the range of `algebraMap ℤ ℚ`).
  obtain ⟨d, hd⟩ : ∃ d : ℤ, P.det = d := by
    have hP_int : ∀ i j, ∃ d : ℤ, P i j = d := by
      intro i j;
      have hP_int : ∀ j, ∃ d : NumberField.RingOfIntegers K, b j = algebraMap (NumberField.RingOfIntegers K) K d := by
        exact fun j => ⟨ ⟨ b j, hb j ⟩, rfl ⟩;
      obtain ⟨ d, hd ⟩ := hP_int j;
      simp +zetaDelta at *;
      simp +decide [ hd, Basis.toMatrix_apply ];
    choose f hf using hP_int;
    exact ⟨ Matrix.det ( Matrix.of fun i j => f i j ), by simp +decide [ hf, Matrix.det_apply' ] ⟩;
  by_cases hd0 : d = 0 <;> simp_all +decide [ abs_mul ];
  · exact absurd hP (Algebra.discr_not_zero_of_basis ℚ b);
  · exact le_mul_of_one_le_left ( abs_nonneg _ ) ( mod_cast sq_pos_of_ne_zero hd0 )

variable (g : ℕ)

/-- The complex value of the `k`-th generator: `none ↦ i`, `some j ↦ √(q3 j)`. -/
noncomputable def mqGenC : Option (Fin g) → ℂ
  | none => Complex.I
  | some j => ((Real.sqrt (q3 j) : ℝ) : ℂ)

theorem mqGenC_mem (k : Option (Fin g)) : mqGenC g k ∈ Kf g := by
  cases k with
  | none => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  | some j => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨j, j.2, rfl⟩)

/-- The `k`-th generator of `Kf g`. -/
noncomputable def mqGen (k : Option (Fin g)) : Kf g := ⟨mqGenC g k, mqGenC_mem g k⟩

/-- The square of the `k`-th generator, as a rational: `none ↦ -1`, `some j ↦ q3 j`. -/
noncomputable def mqSq : Option (Fin g) → ℚ
  | none => -1
  | some j => (q3 j : ℚ)

/-- The subset-product basis vector `b_S = ∏_{k ∈ S} γ_k`. -/
noncomputable def mqB (S : Finset (Option (Fin g))) : Kf g := ∏ k ∈ S, mqGen g k

/-- The rational value `b_S² = ∏_{k ∈ S} γ_k²`. -/
noncomputable def mqRS (S : Finset (Option (Fin g))) : ℚ := ∏ k ∈ S, mqSq g k

theorem mqGen_sq (k : Option (Fin g)) :
    (mqGen g k) ^ 2 = algebraMap ℚ (Kf g) (mqSq g k) := by
  cases k with
  | none =>
    apply Subtype.ext
    simp only [mqGen, mqGenC, mqSq]
    push_cast
    simp [Complex.I_sq]
  | some j =>
    apply Subtype.ext
    simp only [mqGen, mqGenC, mqSq]
    push_cast
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_cast

theorem mqB_sq (S : Finset (Option (Fin g))) :
    (mqB g S) ^ 2 = algebraMap ℚ (Kf g) (mqRS g S) := by
  unfold mqB mqRS;
  rw [ ← Finset.prod_pow, map_prod ];
  exact Finset.prod_congr rfl fun x hx => mqGen_sq g x

theorem mqGen_isIntegral (k : Option (Fin g)) : IsIntegral ℤ (mqGen g k) := by
  rcases k with ( _ | k );
  · refine' ⟨ Polynomial.X ^ 2 + 1, _, _ ⟩;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_add_C ] ; norm_num;
    · simp +decide [ show ( mqGen g none : Kf g ) = ⟨ Complex.I, _ ⟩ by rfl ];
      exact Subtype.ext ( neg_add_cancel _ );
  · refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( q3 k : ℤ ), _, _ ⟩;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
    · simp +decide [ sub_eq_zero, mqGen_sq ];
      norm_cast

theorem mqB_isIntegral (S : Finset (Option (Fin g))) : IsIntegral ℤ (mqB g S) := by
  simpa [mqB] using
    IsIntegral.prod (s := S) (fun k => mqGen g k) fun k hk => mqGen_isIntegral g k

theorem mqRS_ne_zero (S : Finset (Option (Fin g))) : mqRS g S ≠ 0 := by
  refine' Finset.prod_ne_zero_iff.mpr _;
  rintro ( _ | j ) <;> norm_num [ mqSq ];
  exact fun _ => Nat.Prime.ne_zero ( q3_spec j |>.1 )

theorem mqRS_not_isSquare {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    ¬ IsSquare (mqRS g U) := by
  by_cases hnone : none ∈ U <;> simp_all +decide [ IsSquare ];
  · have h_prod_pos : 0 < ∏ k ∈ U.erase none, (mqSq g k : ℚ) := by
      refine' Finset.prod_pos fun k hk => _;
      cases k <;> simp_all +decide [ mqSq ];
      exact Nat.Prime.pos ( q3_spec _ |>.1 );
    unfold mqRS;
    rw [ ← Finset.insert_erase hnone, Finset.prod_insert ( Finset.notMem_erase _ _ ) ];
    exact fun x hx => by rw [ show mqSq g none = -1 by rfl ] at hx; nlinarith;
  · -- Since `none ∉ U`, all elements of `U` are of the form `some j`. Let `N` be the product of these primes.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, mqRS g U = N ∧ Squarefree N ∧ N ≠ 1 := by
      refine' ⟨ ∏ k ∈ U, k.elim 1 ( fun j => q3 j ), _, _, _ ⟩ <;> norm_num [ mqRS ];
      · refine' Finset.prod_congr rfl fun x hx => _ ; rcases x with ( _ | j ) <;> simp_all +decide [ mqSq ];
      · -- Since the elements of `U` are distinct primes, their product is squarefree.
        have h_squarefree : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) := by
          intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
          exact ⟨ Nat.Coprime.prod_right fun p hp => hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop, hS.1.squarefree ⟩;
        convert h_squarefree _ using 1;
        rotate_left;
        exact Finset.image ( fun k => k.elim 1 fun j => q3 j ) U;
        · simp +zetaDelta at *;
          intro a ha; cases a <;> simp_all +decide [ q3_spec ] ;
        · rw [ Finset.prod_image ];
          intro x hx y hy; cases x <;> cases y <;> simp_all +decide [ q3_strictMono.injective.eq_iff ] ;
          exact fun h => Fin.ext h;
      · obtain ⟨ x, hx ⟩ := hU; use x; cases x <;> simp_all +decide ;
        exact Nat.Prime.ne_one ( q3_spec _ |>.1 );
    intro x hx; have := Rat.isSquare_natCast_iff.mp ( show IsSquare ( N : ℚ ) from ⟨ x, by linarith ⟩ ) ; simp_all +decide [ isSquare_iff_exists_sq ] ;
    rcases this with ⟨ r, rfl ⟩ ; simp_all +decide [ sq, Nat.squarefree_mul_iff ] ;
    tauto

theorem mqB_notMem_range {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    mqB g U ∉ (algebraMap ℚ (Kf g)).range := by
  intro h
  obtain ⟨q, hq⟩ := h
  have hq_sq : q^2 = mqRS g U := by
    apply (RingHom.injective (algebraMap ℚ (Kf g)))
    rw [map_pow, hq, mqB_sq]
  exact (by
  exact mqRS_not_isSquare g hU ⟨ q, by linarith ⟩)

theorem trace_mqB_zero {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    Algebra.trace ℚ (Kf g) (mqB g U) = 0 := by
  apply trace_eq_zero_of_sq_ratCast;
  convert mqB_sq g U;
  convert mqB_notMem_range g hU using 1

theorem trace_mqB_mul_of_ne {S T : Finset (Option (Fin g))} (h : S ≠ T) :
    Algebra.trace ℚ (Kf g) (mqB g S * mqB g T) = 0 := by
  -- Since $S \neq T$, the symmetric difference $S \Delta T$ is nonempty.
  have h_symm_diff_nonempty : (S \ T ∪ T \ S).Nonempty := by
    contrapose! h; aesop;
  -- Using the claim, we have `mqB g S * mqB g T = algebraMap ℚ (Kf g) c * mqB g (S ∆ T)`.
  have h_claim : mqB g S * mqB g T = algebraMap ℚ (Kf g) (∏ k ∈ S ∩ T, mqSq g k) * mqB g (S \ T ∪ T \ S) := by
    have h_claim : mqB g S * mqB g T = (∏ k ∈ S ∪ T, mqGen g k) * (∏ k ∈ S ∩ T, mqGen g k) := by
      simp +decide [ mqB ];
      rw [ ← Finset.prod_union_inter ];
    rw [ h_claim, show S ∪ T = ( S \ T ∪ T \ S ) ∪ ( S ∩ T ) from ?_, Finset.prod_union ];
    · simp +decide [ mul_comm, mqB ];
      rw [ ← mul_assoc, ← Finset.prod_mul_distrib ];
      rw [ mul_comm ] ; congr ; ext ; simp +decide [ ← sq, mqGen_sq ] ;
    · exact Finset.disjoint_left.mpr ( by aesop );
    · grind;
  convert congr_arg ( fun x : Kf g => Algebra.trace ℚ ( Kf g ) x ) h_claim using 1;
  rw [ ← Algebra.smul_def, LinearMap.map_smul, trace_mqB_zero _ h_symm_diff_nonempty, smul_zero ]

theorem trace_mqB_mul_self (S : Finset (Option (Fin g))) :
    Algebra.trace ℚ (Kf g) (mqB g S * mqB g S)
      = (finrank ℚ (Kf g) : ℚ) * mqRS g S := by
  convert congr_arg ( fun x : Kf g => Algebra.trace ℚ ( Kf g ) x ) ( mqB_sq g S ) using 1;
  · rw [ sq ];
  · rw [ Algebra.trace_algebraMap ];
    norm_num [ Algebra.smul_def ]

theorem traceMatrix_mqB :
    Algebra.traceMatrix ℚ (mqB g)
      = Matrix.diagonal (fun S => (finrank ℚ (Kf g) : ℚ) * mqRS g S) := by
  convert Matrix.ext _;
  intro S T; by_cases h : S = T <;> simp +decide [ h, Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_mqB_mul_of_ne, trace_mqB_mul_self ] ;

theorem discr_mqB_ne_zero : Algebra.discr ℚ (mqB g) ≠ 0 := by
  rw [ Algebra.discr_def, traceMatrix_mqB g ];
  simp +zetaDelta at *;
  exact Finset.prod_ne_zero_iff.mpr fun S _ => mul_ne_zero ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Module.finrank_pos ) <| mqRS_ne_zero g S

theorem mqB_linearIndependent : LinearIndependent ℚ (mqB g) := by
  by_contra h
  exact discr_mqB_ne_zero g (Algebra.discr_zero_of_not_linearIndependent ℚ h)

theorem mq_Kf_finrank_le : finrank ℚ (Kf g) ≤ 2 ^ (g + 1) := by
  have h_finite : ∀ s : Finset (Option (Fin g)), (Module.finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) : Set ℂ)))) ≤ 2 ^ s.card := by
    intro s
    induction' s using Finset.induction with a s ha ih;
    · rw [ IntermediateField.adjoin_eq_bot_iff.mpr ] <;> norm_num;
    · -- By the tower law, we have:
      have h_tower : (finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) ∪ {mqGenC g a}) : Set ℂ))) ≤ (finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g)) : Set ℂ))) * (finrank ℚ (IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ))) := by
        have h_tower : (finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) ∪ {mqGenC g a}) : Set ℂ))) ≤ (finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g)) : Set ℂ))) * (finrank ℚ (IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ))) := by
          have h_tower : IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) ∪ {mqGenC g a}) : Set ℂ) = IntermediateField.adjoin ℚ (↑(s.image (mqGenC g)) : Set ℂ) ⊔ IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ) := by
            rw [ ← IntermediateField.adjoin_union ];
            norm_num +zetaDelta at *
          rw [h_tower];
          convert IntermediateField.finrank_sup_le _ _ using 1;
        exact h_tower;
      -- Since $mqGenC g a$ is a root of a polynomial of degree 2 over $\mathbb{Q}$, we have $finrank ℚ (IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ)) ≤ 2$.
      have h_root : finrank ℚ (IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ)) ≤ 2 := by
        have h_root : minpoly ℚ (mqGenC g a) ∣ Polynomial.X ^ 2 - Polynomial.C (mqSq g a : ℚ) := by
          refine' minpoly.dvd ℚ _ _;
          convert sub_eq_zero.mpr ( mqGen_sq g a ) using 1;
          erw [ ← Subtype.coe_inj ] ; aesop;
        rw [ IntermediateField.adjoin.finrank ];
        · exact le_trans ( Polynomial.natDegree_le_of_dvd h_root ( by exact Polynomial.X_pow_sub_C_ne_zero ( by norm_num ) _ ) ) ( by erw [ Polynomial.natDegree_X_pow_sub_C ] );
        · refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( mqSq g a : ℚ ), _, _ ⟩;
          · rw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
          · cases a <;> simp +decide [ mqGenC, mqSq ];
            norm_cast ; norm_num [ Real.sq_sqrt ( Nat.cast_nonneg _ ) ];
      calc
        finrank ℚ (IntermediateField.adjoin ℚ (↑((insert a s).image (mqGenC g)) : Set ℂ))
            = finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) ∪ {mqGenC g a}) : Set ℂ)) := by
          have hset :
              (↑((insert a s).image (mqGenC g)) : Set ℂ) =
                (↑(s.image (mqGenC g) ∪ {mqGenC g a}) : Set ℂ) := by
            simp only [Finset.image_insert, Finset.coe_insert, Finset.coe_union,
              Finset.coe_singleton, Set.union_singleton]
          rw [hset]
        _ ≤ 2 ^ s.card * 2 := h_tower.trans ( Nat.mul_le_mul ih h_root )
        _ = 2 ^ (insert a s).card := by
          rw [ Finset.card_insert_of_notMem ha, pow_succ ]
        _ = 2 ^ (insert a s).card := rfl
  convert h_finite Finset.univ;
  · refine' le_antisymm _ _;
    · simp +decide [ Kf ];
      rintro x ( rfl | ⟨ j, hj, rfl ⟩ ) <;> [ exact IntermediateField.subset_adjoin ℚ _ ⟨ none, rfl ⟩ ; exact IntermediateField.subset_adjoin ℚ _ ⟨ some ⟨ j, hj ⟩, rfl ⟩ ];
    · simp +decide [ Kf ];
      rintro _ ⟨ k, rfl ⟩ ; cases k <;> aesop;
  · refine' le_antisymm _ _ <;> simp +decide [ Kf ];
    · rintro x ( rfl | ⟨ j, hj, rfl ⟩ ) <;> [ exact IntermediateField.subset_adjoin ℚ _ ⟨ none, rfl ⟩ ; exact IntermediateField.subset_adjoin ℚ _ ⟨ some ⟨ j, hj ⟩, rfl ⟩ ];
    · rintro _ ⟨ k, rfl ⟩ ; cases k <;> simp +decide [ mqGenC ] ;
      · exact IntermediateField.subset_adjoin ℚ _ ( Set.mem_insert _ _ );
      · exact IntermediateField.subset_adjoin ℚ _ ( Set.mem_insert_of_mem _ <| Set.mem_image_of_mem _ <| by simp +decide );
  · unfold Kf;
    congr with x ; simp +decide [ mqGenC ];
    constructor;
    · rintro ( rfl | ⟨ j, hj, rfl ⟩ ) <;> [ exact ⟨ none, rfl ⟩ ; exact ⟨ some ⟨ j, hj ⟩, rfl ⟩ ];
    · rintro ⟨ y, rfl ⟩ ; cases y <;> aesop;
  · simp

theorem Kf_card_index : Fintype.card (Finset (Option (Fin g))) = 2 ^ (g + 1) := by
  rw [Fintype.card_finset, Fintype.card_option, Fintype.card_fin]

theorem mq_Kf_finrank_eq : finrank ℚ (Kf g) = 2 ^ (g + 1) := by
  refine le_antisymm (mq_Kf_finrank_le g) ?_
  have h := (mqB_linearIndependent g).fintype_card_le_finrank
  rwa [Kf_card_index] at h

theorem mqRS_abs_le (S : Finset (Option (Fin g))) :
    |mqRS g S| ≤ ∏ j ∈ Finset.range g, (q3 j : ℚ) := by
  -- By definition of `mqRS`, we know that `|mqRS g S| = ∏ k ∈ S, |mqSq g k|`.
  have h_abs : |mqRS g S| = ∏ k ∈ S, |mqSq g k| := by
    rw [ ← Finset.abs_prod, show mqRS g S = ∏ k ∈ S, mqSq g k by rfl ];
  -- Each `|mqSq g k| ≥ 1`: `|mqSq g none| = |(-1)| = 1`, and `|mqSq g (some j)| = (q3 j : ℚ) ≥ 1` since `q3 j` is prime hence `≥ 2 ≥ 1`.
  have h_abs_ge_one : ∀ k : Option (Fin g), 1 ≤ |mqSq g k| := by
    intro k; rcases k with ( _ | j ) <;> norm_num [ mqSq ] ;
    exact Nat.Prime.pos ( q3_spec j |>.1 );
  -- Since `S ⊆ Finset.univ` and every factor is `≥ 1`, by `Finset.prod_le_prod_of_subset_of_one_le'` we get `∏ k ∈ S, |mqSq g k| ≤ ∏ k ∈ Finset.univ, |mqSq g k|`.
  have h_prod_le_prod_univ : ∏ k ∈ S, |mqSq g k| ≤ ∏ k ∈ Finset.univ, |mqSq g k| := by
    rw [ ← Finset.prod_sdiff ( Finset.subset_univ S ) ];
    exact le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => abs_nonneg _ ) ( le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by norm_num ) fun _ _ => h_abs_ge_one _ ) );
  simp_all +decide;
  exact h_prod_le_prod_univ.trans ( by rw [ Finset.prod_range ] ; simp +decide [ mqSq ] )

theorem abs_discr_mqB_le :
    |Algebra.discr ℚ (mqB g)|
      ≤ (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℚ)) ^ 2 ^ (g + 1) := by
  rw [ Algebra.discr_def, traceMatrix_mqB ];
  norm_num [ Finset.abs_prod, abs_mul ];
  refine' le_trans ( Finset.prod_le_prod _ fun x _ => mul_le_mul_of_nonneg_left ( mqRS_abs_le g x ) ( Nat.cast_nonneg _ ) ) _ <;> norm_num [ mq_Kf_finrank_eq ];
  gcongr;
  decide +revert

end Multiquadratic

/-! ## Class number and unit bounds (abstract) -/

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
  classical
  have hli := mqB_linearIndependent g
  have hcard : Fintype.card (Finset (Option (Fin g))) = Module.finrank ℚ (Kf g) := by
    rw [mq_Kf_finrank_eq, Kf_card_index]
  set bas := basisOfLinearIndependentOfCardEqFinrank hli hcard with hbas_def
  have hbas : ⇑bas = mqB g := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hint : ∀ i, IsIntegral ℤ (bas i) := by
    intro i
    rw [show bas i = mqB g i from congrFun hbas i]
    exact mqB_isIntegral g i
  have h1 : |(NumberField.discr (Kf g) : ℚ)| ≤ |Algebra.discr ℚ (mqB g)| := by
    have h := abs_discr_le_of_basis_isIntegral bas hint
    rwa [hbas] at h
  have h2 := abs_discr_mqB_le g
  have h3 : |(NumberField.discr (Kf g) : ℚ)| ≤
      (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℚ)) ^ 2 ^ (g + 1) := le_trans h1 h2
  exact_mod_cast h3

/-- Helper for `log_classNumber_Kf_le`: the degree of `K_g` exceeds `1`.
It is even and positive, since `K_g` is totally complex. -/
theorem Kf_one_lt_finrank (g : ℕ) : 1 < Module.finrank ℚ (Kf g) := by
  -- By definition of $K_g$, it is totally complex, so its degree is even and positive.
  have h_deg : 2 * NumberField.InfinitePlace.nrComplexPlaces (Kf g) = Module.finrank ℚ (Kf g) := by
    rw [ NumberField.IsTotallyComplex.finrank ];
  linarith [ show 0 < NumberField.InfinitePlace.nrComplexPlaces ( Kf g ) from by linarith [ show 0 < Module.finrank ℚ ( Kf g ) from Module.finrank_pos ] ] ;

/-- Helper for `log_classNumber_Kf_le`: a uniform bound on the partial sums
`∑_{j<g} log (q3 j)`, deduced from the polynomial bound `q3_poly_bound`. -/
theorem q3_log_sum_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : ℕ, ∑ j ∈ Finset.range g, Real.log (q3 j) ≤
      C * (g + 1) * Real.log (g + 2) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j ≥ N, (q3 j : ℝ) ≤ (j + 2) ^ 2 := by
    exact Filter.eventually_atTop.mp ( q3_poly_bound );
  refine' ⟨ ( ∑ j ∈ Finset.range N, Real.log ( q3 j ) ) / Real.log 2 + 2, _, _ ⟩;
  · exact add_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => Real.log_nonneg ( mod_cast Nat.Prime.pos ( q3_spec _ |>.1 ) ) ) ( Real.log_nonneg ( by norm_num ) ) ) zero_le_two;
  · intro g
    by_cases hg : g ≤ N;
    · refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hg ) fun _ _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1 ) _;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( show ( g : ℝ ) + 2 ≥ 2 by linarith ) ) ( by exact mul_nonneg ( add_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1 ) <| Real.log_nonneg <| by norm_num ) zero_le_two ) <| by positivity ) );
      nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( ∑ j ∈ Finset.range N, Real.log ( q3 j ) ) ( ne_of_gt ( Real.log_pos one_lt_two ) ), show ( g : ℝ ) + 1 ≥ 1 by linarith, show ( ∑ j ∈ Finset.range N, Real.log ( q3 j ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1 ];
    · -- For the tail $N \le j < g$, we have $\log(q3 j) \le \log((j + 2)^2) = 2 \log(j + 2)$.
      have h_tail : ∑ j ∈ Finset.Ico N g, Real.log (q3 j) ≤ 2 * (g - N) * Real.log (g + 2) := by
        have h_tail : ∀ j ∈ Finset.Ico N g, Real.log (q3 j) ≤ 2 * Real.log (g + 2) := by
          intros j hj
          have h_log_bound : Real.log (q3 j) ≤ Real.log ((j + 2) ^ 2) := by
            exact Real.log_le_log ( Nat.cast_pos.mpr ( Nat.Prime.pos ( q3_spec j |>.1 ) ) ) ( hN j ( Finset.mem_Ico.mp hj |>.1 ) );
          exact h_log_bound.trans ( by rw [ Real.log_pow ] ; norm_num; exact Real.log_le_log ( by positivity ) ( by norm_cast; linarith [ Finset.mem_Ico.mp hj ] ) );
        calc
          ∑ j ∈ Finset.Ico N g, Real.log (q3 j) ≤
              ∑ j ∈ Finset.Ico N g, 2 * Real.log (g + 2) := by
            exact Finset.sum_le_sum h_tail
          _ = 2 * (g - N) * Real.log (g + 2) := by
            simp [Nat.cast_sub (le_of_not_ge hg)]
            ring
      -- For the head $j < N$, we have $\log(q3 j) \le \log(q3 j)$.
      have h_head : ∑ j ∈ Finset.range N, Real.log (q3 j) ≤ (∑ j ∈ Finset.range N, Real.log (q3 j)) / Real.log 2 * (g + 1) * Real.log (g + 2) := by
        rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ( by positivity ) ];
        rw [ mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( by nlinarith [ Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( g:ℝ ) + 2 ≥ 2 ), show ( g:ℝ ) ≥ N + 1 by norm_cast; linarith ] ) ( Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| by have := q3_spec ‹_›; aesop );
      rw [ ← Finset.sum_range_add_sum_Ico _ ( show N ≤ g from le_of_not_ge hg ) ];
      nlinarith [ show 0 ≤ Real.log ( g + 2 ) by exact Real.log_nonneg ( by linarith ), show ( N : ℝ ) ≤ g by norm_cast; linarith ]

/-- Helper for `log_classNumber_Kf_le`: `log |d_{K_g}| ≤ C · 2^g · (g+1) · log (g+2)`,
from the discriminant bound `Kf_discr_le` and `q3_log_sum_le`. -/
theorem log_discr_Kf_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : ℕ, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤
      C * 2 ^ g * (g + 1) * Real.log (g + 2) := by
  -- Let's choose any $C$ such that the inequality holds for $g \geq G$.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ g ≥ 100, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤ C * 2 ^ g * (g + 1) * Real.log (g + 2) := by
    have := q3_log_sum_le;
    obtain ⟨ C, hC₀, hC ⟩ := this; use 2 * ( 2 + C ) ; refine' ⟨ by positivity, fun g hg => _ ⟩ ; have := Kf_discr_le g;
    refine' le_trans ( Real.log_le_log ( _ ) this ) _;
    · exact abs_pos.mpr ( mod_cast NumberField.discr_ne_zero _ );
    · rw [ Real.log_pow, Real.log_mul, Real.log_prod ] <;> norm_cast <;> norm_num;
      · rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] ; ring_nf at *;
        nlinarith [ hC g, show ( 0 : ℝ ) ≤ 2 ^ g by positivity, show ( 0 : ℝ ) ≤ g * 2 ^ g by positivity, show ( 0 : ℝ ) ≤ C * 2 ^ g by positivity, show ( 0 : ℝ ) ≤ C * g * 2 ^ g by positivity, Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( 2 : ℝ ) + g ≥ 2 ) ];
      · exact fun x hx => Nat.Prime.ne_zero ( q3_spec x |>.1 );
      · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| q3_spec i |>.1;
  -- Let's choose any $C$ such that the inequality holds for $g < 100$.
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ g < 100, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤ C' * 2 ^ g * (g + 1) * Real.log (g + 2) := by
    have h_finite : ∃ C' : ℝ, ∀ g < 100, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤ C' * 2 ^ g * (g + 1) * Real.log (g + 2) := by
      have h_discr_bound : ∀ g < 100, ∃ C_g : ℝ, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤ C_g * 2 ^ g * (g + 1) * Real.log (g + 2) := by
        intro g hg; use Real.log |(NumberField.discr (Kf g) : ℝ)| / (2 ^ g * (g + 1) * Real.log (g + 2)); rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div ] ; rw [ le_div_iff₀ ] ; ring_nf ;
        · norm_num;
        · exact mul_pos ( mul_pos ( pow_pos ( by norm_num ) _ ) ( by positivity ) ) ( Real.log_pos ( by linarith ) )
      choose! C' hC' using h_discr_bound;
      use sSup (Set.image C' (Finset.range 100));
      intro g hg; refine le_trans ( hC' g hg ) ?_; gcongr;
      · exact Real.log_nonneg ( by linarith );
      · exact le_csSup ( by exact Set.Finite.bddAbove <| Set.toFinite _ ) <| Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_range.mpr hg;
    exact ⟨ Max.max h_finite.choose 0, le_max_right _ _, fun g hg => le_trans ( h_finite.choose_spec g hg ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ) ⟩;
  exact ⟨ Max.max C C', le_max_of_le_left hC.1, fun g => if hg : g < 100 then le_trans ( hC'.2 g hg ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by positivity ) ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ) else le_trans ( hC.2 g ( le_of_not_gt hg ) ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ) ⟩

/-- Helper for `log_classNumber_Kf_le`: `log h_{K_g} ≤ a · log |d_{K_g}| + b`,
combining the class-number bound `classNumber_le_bound` with the Minkowski
lower bound on the discriminant `NumberField.abs_discr_ge`. -/
theorem log_classNumber_le_log_discr : ∃ a b : ℝ, 0 ≤ a ∧
    ∀ g : ℕ, Real.log (NumberField.classNumber (Kf g)) ≤
      a * Real.log |(NumberField.discr (Kf g) : ℝ)| + b := by
  refine' ⟨ 1 + ( Real.log 4 / Real.log ( 3 * Real.pi / 4 ) ), ( Real.log 4 / Real.log ( 3 * Real.pi / 4 ) ) * Real.log ( 9 / 4 ), _, _ ⟩ <;> norm_num;
  · exact add_nonneg zero_le_one ( div_nonneg ( Real.log_nonneg ( by norm_num ) ) ( Real.log_nonneg ( by linarith [ Real.pi_gt_three ] ) ) );
  · intro g
    have h1 : Real.log (NumberField.classNumber (Kf g)) ≤ Real.log (|NumberField.discr (Kf g)|) + Module.finrank ℚ (Kf g) * Real.log 4 := by
      have h1 : (NumberField.classNumber (Kf g) : ℝ) ≤ |(NumberField.discr (Kf g) : ℝ)| * 4 ^ Module.finrank ℚ (Kf g) := by
        convert classNumber_le_bound ( Kf g ) using 1;
      convert Real.log_le_log ( Nat.cast_pos.mpr <| NumberField.classNumber_pos _ ) h1 using 1;
      rw [ Real.log_mul ( by exact ne_of_gt <| abs_pos.mpr <| mod_cast NumberField.discr_ne_zero _ ) ( by positivity ), Real.log_pow ];
    have h2 : (4 / 9 : ℝ) * (3 * Real.pi / 4) ^ Module.finrank ℚ (Kf g) ≤ |NumberField.discr (Kf g)| := by
      convert NumberField.abs_discr_ge ( Kf_one_lt_finrank g ) using 1;
    have h3 : Real.log (4 / 9) + Module.finrank ℚ (Kf g) * Real.log (3 * Real.pi / 4) ≤ Real.log (|NumberField.discr (Kf g)|) := by
      convert Real.log_le_log ( by positivity ) h2 using 1 ; norm_num [ Real.log_mul, Real.log_pow ];
      norm_num [ abs_mul, abs_of_nonneg, Real.log_nonneg ];
    rw [ show ( 9 / 4 : ℝ ) = ( 4 / 9 ) ⁻¹ by norm_num, Real.log_inv ];
    norm_num [ abs_of_nonneg, Real.log_nonneg ] at *;
    nlinarith [ show 0 < Real.log 4 / Real.log ( 3 * Real.pi / 4 ) by exact div_pos ( Real.log_pos ( by norm_num ) ) ( Real.log_pos ( by linarith [ Real.pi_gt_three ] ) ), mul_div_cancel₀ ( Real.log 4 ) ( ne_of_gt ( Real.log_pos ( by linarith [ Real.pi_gt_three ] : 1 < 3 * Real.pi / 4 ) ) ) ]

/-- [medium given `classNumber_le_bound`, `Kf_discr_le`, `q3_poly_bound`]
Consolidated class-number estimate: `log h_{K_g} ≤ c₀ · 2^g · (g+1) log (g+1)`.
Sketch: combine the three inputs;
`log |d_K| ≤ 2^(g+1) · ((g+1) log 4 + ∑_{j<g} log (q3 j))` and
`∑_{j<g} log (q3 j) ≤ 2 g log (g+2) + O(1)` by `q3_poly_bound`; absorb
small-`g` exceptions into `c₀`. -/
theorem log_classNumber_Kf_le : ∃ c₀ : ℝ, 1 ≤ c₀ ∧
    ∀ g : ℕ, Real.log (NumberField.classNumber (Kf g)) ≤
      c₀ * 2 ^ g * (g + 1) * Real.log (g + 2) := by
  -- Set `c₀ := a * C + |b| / Real.log 2 + 1`.
  obtain ⟨a, b, ha, hab⟩ := log_classNumber_le_log_discr
  obtain ⟨C, hC, hCg⟩ := log_discr_Kf_le
  use a * C + |b| / Real.log 2 + 1;
  refine' ⟨ _, fun g => le_trans ( hab g ) _ ⟩;
  · exact le_add_of_nonneg_left ( add_nonneg ( mul_nonneg ha hC ) ( div_nonneg ( abs_nonneg b ) ( Real.log_nonneg ( by norm_num ) ) ) );
  · -- Since `Real.log 2 ≤ L` and `0 < Real.log 2`, we have `L > 0`.
    have hL_pos : Real.log 2 ≤ 2 ^ g * (g + 1) * Real.log (g + 2) := by
      exact le_trans ( Real.log_le_log ( by norm_num ) ( by linarith ) ) ( le_mul_of_one_le_left ( Real.log_nonneg ( by linarith ) ) ( one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by norm_num ) ) ( by linarith ) ) );
    cases abs_cases b <;> nlinarith [ show 0 ≤ a * C by positivity, show 0 ≤ |b| / Real.log 2 by positivity, mul_div_cancel₀ ( |b| : ℝ ) ( ne_of_gt ( Real.log_pos one_lt_two ) ), hCg g, Real.log_pos one_lt_two ]

/-! ## The arithmetic construction -/

section Arithmetic

open NumberField IsCMField

set_option maxHeartbeats 1000000 in
lemma exists_transversal_family {R : Type*} [CommRing R] [IsDedekindDomain R]
    (σ : R ≃+* R) (S : Finset (Ideal R))
    (hprime : ∀ p ∈ S, p.IsPrime) (hne : ∀ p ∈ S, p ≠ ⊥)
    (hinv : ∀ p ∈ S, Ideal.map σ p ∈ S)
    (hinvol : ∀ p ∈ S, Ideal.map σ (Ideal.map σ p) = p)
    (hfree : ∀ p ∈ S, Ideal.map σ p ≠ p) :
    ∃ G : Finset (Ideal R), 2 ^ (S.card / 2) ≤ G.card ∧
      ∀ A ∈ G, A * Ideal.map σ A = ∏ p ∈ S, p := by
  induction' S using Finset.strongInduction with S ih;
  by_cases hS : S.Nonempty;
  · obtain ⟨p, hp⟩ : ∃ p ∈ S, Ideal.map σ p ∈ S ∧ Ideal.map σ p ≠ p := by
      exact ⟨ hS.choose, hS.choose_spec, hinv _ hS.choose_spec, hfree _ hS.choose_spec ⟩;
    obtain ⟨G', hG'⟩ : ∃ G' : Finset (Ideal R), 2 ^ ((S \ {p, Ideal.map σ p}).card / 2) ≤ G'.card ∧ ∀ A ∈ G', A * Ideal.map σ A = ∏ x ∈ S \ {p, Ideal.map σ p}, x := by
      apply ih (S \ {p, Ideal.map σ p});
      grind +locals;
      · exact fun q hq => hprime q ( Finset.mem_sdiff.mp hq |>.1 );
      · exact fun q hq => hne q ( Finset.mem_sdiff.mp hq |>.1 );
      · grind +revert;
      · exact fun q hq => hinvol q ( Finset.mem_sdiff.mp hq |>.1 );
      · exact fun q hq => hfree q ( Finset.mem_sdiff.mp hq |>.1 );
    refine' ⟨ Finset.image ( fun A => A * p ) G' ∪ Finset.image ( fun A => A * Ideal.map σ p ) G', _, _ ⟩;
    · rw [ Finset.card_union_of_disjoint ];
      · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
        · rw [ show S.card = ( S \ { p, Ideal.map σ p } ).card + 2 from ?_ ];
          · norm_num [ Nat.add_div ] at * ; linarith [ pow_succ' 2 ( ( S \ { p, Ideal.map σ p } ).card / 2 ) ];
          · grind +qlia;
        · exact fun a₁ a₂ h => h.resolve_right ( by specialize hne _ hp.2.1; aesop );
        · exact fun _ _ h => h.resolve_right ( hne p hp.1 );
      · simp +decide [ Finset.disjoint_left, hp ];
        intro a ha x hx h;
        have h_div : p ∣ x := by
          have h_div : p ∣ x * Ideal.map σ p := by
            exact h.symm ▸ dvd_mul_left _ _;
          have h_not_div : ¬(p ∣ Ideal.map σ p) := by
            intro h_div;
            have h_div : Ideal.map σ p ≤ p := by
              exact Ideal.le_of_dvd h_div;
            have h_div : p ≤ Ideal.map σ p := by
              have hmono : Ideal.map σ (Ideal.map σ p) ≤ Ideal.map σ p :=
                Ideal.map_mono h_div
              rwa [hinvol p hp.1] at hmono
            exact hp.2.2 ( le_antisymm ‹_› ‹_› );
          have h_div_x : p ∣ x * Ideal.map σ p → ¬(p ∣ Ideal.map σ p) → p ∣ x := by
            simp +decide [ Ideal.dvd_iff_le ] at *;
            exact fun _ _ => by have := hprime p hp.1; exact this.mul_le.mp h_div |> fun h => h.resolve_right ‹_›;
          exact h_div_x h_div h_not_div;
        have h_div_prod : p ∣ ∏ x ∈ S \ {p, Ideal.map σ p}, x := by
          exact hG'.2 x hx ▸ dvd_mul_of_dvd_left h_div _;
        have h_div_prod : ∀ {T : Finset (Ideal R)}, (∀ q ∈ T, q.IsPrime) → (∀ q ∈ T, q ≠ ⊥) → (∀ q ∈ T, q ≠ p) → ¬(p ∣ ∏ x ∈ T, x) := by
          intros T hT_prime hT_ne_bot hT_ne_p; induction' T using Finset.induction with q T hqT ih; simp_all +decide [ Ideal.dvd_iff_le ] ;
          · exact hprime p hp.1 |> fun h => h.ne_top;
          · rw [ Ideal.dvd_iff_le ] at *;
            contrapose! ih;
            simp_all +decide [ Ideal.mul_le ];
            intro s hs;
            by_cases hq : q ≤ p;
            · have hq_eq_p : q = p := by
                have hq_eq_p : q.IsMaximal := by
                  exact hT_prime.1.isMaximal ( by aesop );
                have := hq_eq_p.1;
                have := this.2;
                exact Classical.not_not.1 fun h => absurd ( this p ( lt_of_le_of_ne hq h ) ) ( by
                  exact hprime p hp.1 |> fun h => h.ne_top );
              tauto;
            · obtain ⟨ r, hr, hr' ⟩ := Set.not_subset.mp hq;
              have := ih r hr s hs;
              exact Or.resolve_left ( hprime p hp.1 |>.mem_or_mem this ) hr';
        grind +qlia;
    · simp +zetaDelta at *;
      rintro A ( ⟨ A', hA', rfl ⟩ | ⟨ A', hA', rfl ⟩ ) <;> simp_all +decide [ mul_assoc, Finset.prod_insert, Finset.prod_singleton ];
      · simp_all +decide [ ← mul_assoc, Ideal.map_mul ];
        rw [ show ( ∏ p ∈ S, p ) = ( ∏ p ∈ S \ { p, Ideal.map σ p }, p ) * p * Ideal.map σ p from ?_ ];
        · rw [ ← hG'.2 A' hA' ] ; ring;
        · rw [ ← Finset.prod_sdiff ( Finset.insert_subset hp.1 ( Finset.singleton_subset_iff.mpr hp.2.1 ) ) ];
          rw [ Finset.prod_pair ( Ne.symm hp.2.2 ) ] ; ring;
      · simp_all +decide [ ← mul_assoc, Ideal.map_mul ];
        rw [ show ∏ p ∈ S, p = ( ∏ p ∈ S \ { p, Ideal.map σ p }, p ) * p * Ideal.map σ p from ?_ ];
        · rw [ ← hG'.2 A' hA' ] ; ring;
        · rw [ ← Finset.prod_sdiff ( Finset.insert_subset hp.1 ( Finset.singleton_subset_iff.mpr hp.2.1 ) ) ];
          rw [ Finset.prod_pair ( Ne.symm hp.2.2 ) ] ; ring;
  · refine' ⟨ { 1 }, _, _ ⟩ <;> simp_all +decide;
    exact Ideal.map_top _


/-
**Real multiquadratic independence.** For a finite set `s` of primes and a squarefree
`d > 1` none of whose prime factors lie in `s`, `√d` is not in the real multiquadratic field
`ℚ(√q : q ∈ s)`. Proven by strong induction on `s`.
-/

theorem Kf_aut_sq (g : ℕ) (σ : Kf g ≃ₐ[ℚ] Kf g) : σ ^ 2 = 1 := by
  have h2 : ∀ x : Kf g, σ (σ x) = x := by
    have h_fixed_subfield : ∀ t : Kf g, (t : ℂ)^2 ∈ Set.range (algebraMap ℚ ℂ) → σ (σ t) = t := by
      intro t ht
      obtain ⟨q, hq⟩ := ht
      have h_sigma_sq_t : (σ t)^2 = t^2 := by
        convert congr_arg ( σ : Kf g → Kf g ) ( show t ^ 2 = ( algebraMap ℚ ( Kf g ) ) q from ?_ ) using 1;
        · simp +decide [ map_pow ];
        · simp_all +decide [ ← Subtype.coe_inj ];
        · exact Subtype.ext <| hq.symm;
      have h_sigma_t_cases : σ t = t ∨ σ t = -t := by
        exact eq_or_eq_neg_of_sq_eq_sq _ _ h_sigma_sq_t;
      cases h_sigma_t_cases <;> simp_all +decide [ sq ];
    have h_adjoin : IntermediateField.adjoin ℚ (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g)) = Kf g := by
      rfl;
    intro x;
    have h_gen : ∀ t ∈ insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g), ∃ t' : Kf g, (t' : ℂ) = t ∧ σ (σ t') = t' := by
      intro t ht
      refine ⟨⟨ t, h_adjoin ▸ IntermediateField.subset_adjoin ℚ _ ht ⟩, rfl, ?_⟩
      rcases ht with rfl | ⟨ j, hj, rfl ⟩
      · exact h_fixed_subfield _ ⟨ -1, by norm_num [ Complex.ext_iff ] ⟩
      · refine h_fixed_subfield _ ⟨ (q3 j : ℚ), ?_ ⟩
        rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg (q3 j))]
        push_cast
        ring
    have h_gen : ∀ t ∈ IntermediateField.adjoin ℚ (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g)), ∃ t' : Kf g, (t' : ℂ) = t ∧ σ (σ t') = t' := by
      intro t ht;
      induction ht using IntermediateField.adjoin_induction;
      · exact h_gen _ ‹_›;
      · exact ⟨ algebraMap ℚ ( Kf g ) ‹_›, by simp +decide, by simp +decide ⟩;
      · rename_i hx hy;
        obtain ⟨ t₁, ht₁, ht₁' ⟩ := hx; obtain ⟨ t₂, ht₂, ht₂' ⟩ := hy; use t₁ + t₂; aesop;
      · rename_i t ht ih;
        obtain ⟨ t', ht', ht'' ⟩ := ih;
        use t'⁻¹;
        aesop;
      · rename_i hx hy;
        obtain ⟨ t₁, ht₁, ht₁' ⟩ := hx; obtain ⟨ t₂, ht₂, ht₂' ⟩ := hy; use t₁ * t₂; aesop;
    obtain ⟨ t', ht₁, ht₂ ⟩ := h_gen x ( h_adjoin.symm ▸ x.2 )
    have : t' = x := Subtype.ext ht₁
    rwa [this] at ht₂
  refine AlgEquiv.ext fun x => ?_
  rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply, h2 x]

/-
An automorphism of `Kf g` fixing each generator `i, √q3 j` is the identity.
-/

theorem Kf_eq_one_of_fixes_gens (g : ℕ) (σ : Kf g ≃ₐ[ℚ] Kf g)
    (h : ∀ t : Kf g, (↑t ∈ insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g))
      → σ t = t) : σ = 1 := by
  -- Let $t \in Kf g$. Since $Kf g$ is generated by $\{i, \sqrt{q3 j} \mid j < g\}$, we can write $t$ as a combination of these generators.
  have h_gen : ∀ t : Kf g, ∃ t' : Kf g, (t' : ℂ) = t ∧ σ t' = t' := by
    have h_ind : ∀ t ∈ IntermediateField.adjoin ℚ (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g)), ∃ t' : Kf g, (t' : ℂ) = t ∧ σ t' = t' := by
      intro t ht;
      induction ht using IntermediateField.adjoin_induction;
      · refine' ⟨ ⟨ _, _ ⟩, rfl, h _ _ ⟩;
        exact IntermediateField.subset_adjoin ℚ _ ‹_›;
        assumption;
      · exact ⟨ ⟨ _, Subalgebra.algebraMap_mem _ _ ⟩, rfl, σ.commutes _ ⟩;
      · rename_i hx hy ihx ihy; obtain ⟨ t₁, rfl, ht₁ ⟩ := ihx; obtain ⟨ t₂, rfl, ht₂ ⟩ := ihy; use t₁ + t₂; simp +decide [ ht₁, ht₂ ] ;
      · rename_i x hx ih; obtain ⟨ t', rfl, ht' ⟩ := ih; use t'⁻¹; aesop;
      · rename_i hx hy;
        obtain ⟨ t₁, ht₁, ht₁' ⟩ := hx; obtain ⟨ t₂, ht₂, ht₂' ⟩ := hy; use t₁ * t₂; aesop;
    exact fun t => h_ind t t.2;
  ext t; specialize h_gen t; aesop;

open scoped NumberField

open NumberField IsCMField in
/-- The key step for unramifiedness: an inertia element `σ` (i.e. `σ • x ≡ x mod P` for all `x`)
fixes any `t` with `t^2 = c ∈ ℤ` provided `p ∤ 4c`.  The alternative `σ t = -t` would give
`2 t ∈ P`, hence `4c ∈ P ∩ ℤ = pℤ`, i.e. `p ∣ 4c`. -/

theorem inertia_fixes_gen (g : ℕ) (p : ℕ)
    (P : Ideal (𝓞 (Kf g))) [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : Kf g ≃ₐ[ℚ] Kf g) (hσ : ∀ x : 𝓞 (Kf g), σ • x - x ∈ P)
    (t : Kf g) (c : ℤ) (hc : (t : ℂ) ^ 2 = (c : ℂ)) (hpc : ¬ (p : ℤ) ∣ 4 * c) :
    σ t = t := by
  -- Since $t^2 = c$, we have $t = \sqrt{c}$ or $t = -\sqrt{c}$. In either case, $\sigma(t) = \pm t$.
  have h_sigma_t : σ t = t ∨ σ t = -t := by
    have h_sigma_t : σ t ^ 2 = t ^ 2 := by
      have h_sigma_sq : σ (t^2) = t^2 := by
        erw [ show t ^ 2 = algebraMap ℤ ( Kf g ) c from Subtype.ext hc ] ; simp +decide [ AlgEquiv.commutes ] ;
      simpa using h_sigma_sq;
    exact eq_or_eq_neg_of_sq_eq_sq _ _ h_sigma_t;
  -- Suppose for contradiction that $\sigma(t) = -t$.
  by_contra h_contra
  have h_neg : σ t = -t := by
    exact h_sigma_t.resolve_left h_contra;
  -- Since $t$ is integral over $\mathbb{Z}$, there exists $xt \in \mathcal{O}_{Kf g}$ such that $xt = t$.
  obtain ⟨xt, hxt⟩ : ∃ xt : 𝓞 (Kf g), (xt : Kf g) = t := by
    refine' ⟨ ⟨ t, _ ⟩, rfl ⟩;
    refine' ⟨ Polynomial.X ^ 2 - Polynomial.C c, _, _ ⟩ <;> norm_num;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
    · erw [ Polynomial.eval₂_C ] ; aesop;
  -- Since $σ • xt = -xt$, we have $σ • xt - xt = -2 * xt$.
  have h_diff : σ • xt - xt = -2 * xt := by
    ext; simp [h_neg, hxt];
    erw [ show ( algebraMap ( 𝓞 ( Kf g ) ) ( Kf g ) ) ( σ • xt ) = σ ( algebraMap ( 𝓞 ( Kf g ) ) ( Kf g ) xt ) from rfl ] ; norm_num [ h_neg, hxt ] ; ring;
    norm_cast;
  -- Since $-2 * xt \in P$, we have $4 * xt^2 \in P$.
  have h_four_xt_sq : 4 * xt^2 ∈ P := by
    have h_four_xt_sq : (-2 * xt) * (-2 * xt) ∈ P := by
      exact P.mul_mem_left _ ( h_diff ▸ hσ xt );
    convert h_four_xt_sq using 1 ; ring;
  -- Since $xt^2 = c$, we have $4 * xt^2 = 4 * c$.
  have h_four_c : 4 * xt^2 = algebraMap ℤ (𝓞 (Kf g)) (4 * c) := by
    ext; simp [hxt, hc];
  have := ‹P.LiesOver ( Ideal.span { ( p : ℤ ) } ) ›.over; simp_all +decide [ Ideal.mem_span_singleton ] ;
  replace this := SetLike.ext_iff.mp this ( 4 * c ) ; simp_all +decide [ Ideal.mem_span_singleton ] ;

/-- Helper bundle of arithmetic facts about `p ≡ 1 mod 4`. -/

theorem p_prime_facts {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (p : ℤ) ≠ 0 ∧ (Ideal.span {(p : ℤ)}) ≠ ⊥ ∧ (Ideal.span {(p : ℤ)}).IsPrime
      ∧ (Ideal.span {(p : ℤ)}).IsMaximal ∧ ¬ (p : ℤ) ∣ 4 := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpz
  have hpprime : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime hpz]; exact_mod_cast Nat.prime_iff_prime_int.mp hp
  have hp4dvd : ¬ (p : ℤ) ∣ 4 := by
    intro h
    have h4 : p ∣ 4 := by exact_mod_cast h
    have hp2 : 2 ≤ p := hp.two_le
    have := Nat.le_of_dvd (by norm_num) h4
    interval_cases p <;> omega
  exact ⟨hpz, hp0, hpprime, hpprime.isMaximal hp0, hp4dvd⟩

/-- The inertia subgroup of any prime over `p ≡ 1 mod 4` is trivial. -/

theorem Kf_inertia_eq_bot (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (P : Ideal (𝓞 (Kf g))) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.inertia (Kf g ≃ₐ[ℚ] Kf g) P = ⊥ := by
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts hp hp4
  rw [eq_bot_iff]
  intro σ hσmem
  have hσ : ∀ x : 𝓞 (Kf g), σ • x - x ∈ P := by
    simpa using AddSubgroup.mem_inertia.mp hσmem
  rw [Subgroup.mem_bot]
  apply Kf_eq_one_of_fixes_gens g σ
  intro t ht
  rcases ht with ht | ⟨j, hj, ht⟩
  · refine inertia_fixes_gen g p P σ hσ t (-1) ?_ ?_
    · rw [ht]; rw [Complex.I_sq]; push_cast; ring
    · simpa using hp4dvd
  · refine inertia_fixes_gen g p P σ hσ t (q3 j) ?_ ?_
    · rw [← ht, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg (q3 j))]; push_cast; ring
    · rw [show (4 * (q3 j : ℤ)) = ((4 * q3 j : ℕ) : ℤ) by push_cast; ring, Int.natCast_dvd_natCast,
        Nat.Prime.dvd_mul hp]
      push_neg
      refine ⟨by simpa using (by exact_mod_cast hp4dvd : ¬ p ∣ (4:ℕ)), ?_⟩
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hp (q3_spec j).1).mp h
      have := (q3_spec j).2
      omega

theorem Kf_ramificationIdxIn_eq_one (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Kf g)) = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts hp hp4
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal := hpmax
  obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))))
  haveI := hPprime
  haveI := hPlies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  haveI : Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanEquivZMod (p : ℤ)).symm.toEquiv
  haveI : Finite (𝓞 (Kf g) ⧸ P) := inferInstance
  letI : Field (ℤ ⧸ Ideal.span {(p : ℤ)}) := Ideal.Quotient.field _
  letI : Field (𝓞 (Kf g) ⧸ P) := Ideal.Quotient.field _
  haveI : Module.Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : PerfectField (ℤ ⧸ Ideal.span {(p : ℤ)}) := PerfectField.ofFinite
  haveI : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) := inferInstance
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := Kf g ≃ₐ[ℚ] Kf g)
        (Ideal.span {(p : ℤ)}) hp0 P, Kf_inertia_eq_bot g p hp hp4 P, Subgroup.card_bot]





/-- The primes of `K_g` lying over the `i`-th prime `≡ 1 mod 4`, as a finset. -/
noncomputable def primesOverP1 (g i : ℕ) : Finset (Ideal (𝓞 (Kf g))) :=
  haveI : (Ideal.span {((p1 i : ℤ))}).IsMaximal :=
    (p_prime_facts (p1_spec i).1 (p1_spec i).2).2.2.2.1
  IsDedekindDomain.primesOverFinset (Ideal.span {((p1 i : ℤ))}) (𝓞 (Kf g))

open scoped Pointwise in
/-- [decomp 1] The common inertia degree of a rational prime `p ≡ 1 mod 4` in
`K_g` is at most `2`: the decomposition group (= stabilizer) has trivial
inertia (`Kf_inertia_eq_bot`), is cyclic modulo inertia (isomorphic to the
residue Galois group, e.g. via `Ideal.Quotient.stabilizerQuotientInertiaEquiv`
or `Ideal.card_stabilizer_eq_card_inertia_mul_finrank`), and has exponent two
(`Kf_aut_sq`), hence order at most `2`. -/
theorem Kf_inertiaDegIn_le_two (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Kf g)) ≤ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsGalois ℚ (Kf g) := Kf_isGalois g
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts hp hp4
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal := hpmax
  obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))))
  haveI := hPprime
  haveI := hPlies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  haveI : Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanEquivZMod (p : ℤ)).symm.toEquiv
  haveI : Finite (𝓞 (Kf g) ⧸ P) := inferInstance
  letI : Field (ℤ ⧸ Ideal.span {(p : ℤ)}) := Ideal.Quotient.field _
  letI : Field (𝓞 (Kf g) ⧸ P) := Ideal.Quotient.field _
  haveI : Module.Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : PerfectField (ℤ ⧸ Ideal.span {(p : ℤ)}) := PerfectField.ofFinite
  haveI : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) := inferInstance
  -- the decomposition group has cardinality e·f = f
  have hcard := Ideal.card_stabilizer_eq (G := Kf g ≃ₐ[ℚ] Kf g) (Ideal.span {(p : ℤ)}) hp0 P
  rw [Kf_ramificationIdxIn_eq_one g p hp hp4, one_mul] at hcard
  rw [← hcard]
  -- the stabilizer is isomorphic to the (cyclic) residue Galois group
  have hquot := Ideal.Quotient.stabilizerQuotientInertiaEquiv
    (G := Kf g ≃ₐ[ℚ] Kf g) (Ideal.span {(p : ℤ)}) P
  have hinbot : Ideal.inertia (Kf g ≃ₐ[ℚ] Kf g) P = ⊥ := Kf_inertia_eq_bot g p hp hp4 P
  have hcard2 : Nat.card (MulAction.stabilizer (Kf g ≃ₐ[ℚ] Kf g) P)
      = Nat.card ((𝓞 (Kf g) ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 (Kf g) ⧸ P)) := by
    have h1 : Nat.card ((Ideal.inertia (Kf g ≃ₐ[ℚ] Kf g) P).subgroupOf
        (MulAction.stabilizer (Kf g ≃ₐ[ℚ] Kf g) P)) = 1 := by
      rw [hinbot, Subgroup.bot_subgroupOf]
      exact Subgroup.card_bot
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (s := (Ideal.inertia (Kf g ≃ₐ[ℚ] Kf g) P).subgroupOf
        (MulAction.stabilizer (Kf g ≃ₐ[ℚ] Kf g) P)), h1, mul_one]
    exact Nat.card_congr hquot.toEquiv
  rw [hcard2]
  -- the residue Galois group is cyclic with exponent two
  have hexp : ∀ x : ((𝓞 (Kf g) ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 (Kf g) ⧸ P)),
      x ^ 2 = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := hquot.surjective x
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective y
    have hσ : σ ^ 2 = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact Kf_aut_sq g (σ : Kf g ≃ₐ[ℚ] Kf g)
    rw [← map_pow, ← QuotientGroup.mk_pow, hσ]
    exact map_one hquot
  have hcyc : IsCyclic ((𝓞 (Kf g) ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 (Kf g) ⧸ P)) :=
    inferInstance
  have hdvd : Nat.card ((𝓞 (Kf g) ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 (Kf g) ⧸ P)) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  exact Nat.le_of_dvd (by norm_num) hdvd

/-- [decomp 2] At least `2^g` primes of `K_g` lie over each rational prime
`p ≡ 1 mod 4`: by the fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` with
`G := Kf g ≃ₐ[ℚ] Kf g`; `Nat.card G = 2^(g+1)` from `IsGalois.card_aut_eq_finrank`
and `Kf_finrank`), `#primesOver · e · f = 2^(g+1)` with `e = 1`
(`Kf_ramificationIdxIn_eq_one`) and `f ≤ 2` (`Kf_inertiaDegIn_le_two`). -/
theorem Kf_card_primesOver_ge (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    2 ^ g ≤ (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))).ncard := by
  haveI : IsGalois ℚ (Kf g) := Kf_isGalois g
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts hp hp4
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal := hpmax
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (p := Ideal.span {(p : ℤ)}) hp0 (𝓞 (Kf g)) (Kf g ≃ₐ[ℚ] Kf g)
  have hG : Nat.card (Kf g ≃ₐ[ℚ] Kf g) = 2 ^ (g + 1) := by
    simpa [Nat.card_eq_fintype_card, Kf_finrank] using IsGalois.card_aut_eq_finrank ℚ (Kf g)
  have he := Kf_ramificationIdxIn_eq_one g p hp hp4
  have hf := Kf_inertiaDegIn_le_two g p hp hp4
  rw [hG, he, one_mul] at hfund
  have h2 : (2 : ℕ) ^ (g + 1) = 2 ^ g * 2 := by rw [pow_succ]
  nlinarith [(Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))).ncard.zero_le,
    Nat.zero_le (Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Kf g)))]

/-- [decomp 3] Complex conjugation moves every prime of `K_g` lying over a
rational prime `p ≡ 1 mod 4`.  Elementary route: if `map conj P = P` then
conjugation induces a ring automorphism of the residue field `κ = 𝓞/P`
fixing the prime field `𝔽_p` pointwise.  Since `p ≡ 1 mod 4`, `-1` is a
square in `ZMod p` (`ZMod.exists_sq_eq_neg_one_iff`), so the two square
roots of `-1` in `κ` already lie in the image of `ZMod p`, hence are fixed
by the induced automorphism; the residue `ī` of `i ∈ 𝓞 (Kf g)` is such a
root, but conjugation sends `i ↦ -i`, so `ī = -ī`, giving `2ī = 0`; `p` is
odd so `ī = 0`, contradicting `ī² = -1 ≠ 0` in `κ`. -/
theorem Kf_conj_primesOver_ne (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (P : Ideal (𝓞 (Kf g)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))) :
    Ideal.map (ringOfIntegersComplexConj (Kf g)) P ≠ P := by
  intro hEq
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : Fact p.Prime := ⟨hp⟩
  -- the imaginary unit as an algebraic integer of `K_g`
  have hImem : Complex.I ∈ Kf g :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  have hiK2 : (⟨Complex.I, hImem⟩ : Kf g) ^ 2 = -1 := by
    ext
    push_cast
    exact Complex.I_sq
  have hint : IsIntegral ℤ (⟨Complex.I, hImem⟩ : Kf g) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C 1,
      Polynomial.monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [hiK2]
  set iO : 𝓞 (Kf g) := ⟨_, hint⟩ with hiOdef
  have hiO2 : iO ^ 2 = -1 := by
    have hK : (iO : Kf g) ^ 2 = -1 := hiK2
    exact_mod_cast hK
  -- conjugation negates the imaginary unit
  have hconjK : NumberField.IsCMField.complexConj (Kf g) (⟨Complex.I, hImem⟩ : Kf g)
      = -(⟨Complex.I, hImem⟩ : Kf g) := by
    have h1 := NumberField.IsCMField.complexEmbedding_complexConj
      (K := Kf g) ((Kf g).val.toRingHom) (⟨Complex.I, hImem⟩ : Kf g)
    apply Subtype.ext
    rw [show ((-(⟨Complex.I, hImem⟩ : Kf g) : Kf g) : ℂ) = -Complex.I from rfl,
      ← Complex.conj_I]
    exact h1
  have hconj_iO : ringOfIntegersComplexConj (Kf g) iO = -iO := by
    have hcoe : ((ringOfIntegersComplexConj (Kf g) iO : 𝓞 (Kf g)) : Kf g)
        = ((-iO : 𝓞 (Kf g)) : Kf g) := by
      rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
      push_cast
      exact_mod_cast hconjK
    exact_mod_cast hcoe
  -- an integer square root of -1 mod p
  obtain ⟨y, hy'⟩ : IsSquare (-1 : ZMod p) :=
    (ZMod.exists_sq_eq_neg_one_iff).mpr (by omega)
  have hy : y ^ 2 = -1 := by rw [pow_two]; exact hy'.symm
  set a : ℤ := (y.val : ℤ) with hadef
  have hpa : (p : ℤ) ∣ a ^ 2 + 1 := by
    have hz : ((a ^ 2 + 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [show ((y.val : ℤ) : ZMod p) = y by push_cast; simp]
      rw [hy]
      ring
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  -- p, hence a² + 1, lies in P
  have hpP : algebraMap ℤ (𝓞 (Kf g)) (p : ℤ) ∈ P := by
    have hmem : ((p : ℤ)) ∈ P.under ℤ := by
      rw [← hPlies.over]
      exact Ideal.mem_span_singleton_self _
    exact hmem
  have haP : algebraMap ℤ (𝓞 (Kf g)) (a ^ 2 + 1) ∈ P := by
    obtain ⟨k, hk⟩ := hpa
    rw [hk, map_mul]
    exact Ideal.mul_mem_right _ _ hpP
  -- the prime P contains iO - a or iO + a
  have hsplit : (iO - algebraMap ℤ _ a) * (iO + algebraMap ℤ _ a) ∈ P := by
    have hfactor : (iO - algebraMap ℤ (𝓞 (Kf g)) a) * (iO + algebraMap ℤ (𝓞 (Kf g)) a)
        = -(algebraMap ℤ (𝓞 (Kf g)) (a ^ 2 + 1)) := by
      have hcast : algebraMap ℤ (𝓞 (Kf g)) (a ^ 2 + 1)
          = (algebraMap ℤ (𝓞 (Kf g)) a) ^ 2 + 1 := by
        push_cast [map_add, map_pow, map_one]
        ring
      rw [hcast]
      linear_combination hiO2
    rw [hfactor]
    exact neg_mem haP
  -- conjugation-stable membership
  have hconjmem : ∀ x ∈ P, ringOfIntegersComplexConj (Kf g) x ∈ P := by
    intro x hx
    rw [← hEq]
    exact Ideal.mem_map_of_mem _ hx
  have hconj_int : ∀ n : ℤ, ringOfIntegersComplexConj (Kf g) (algebraMap ℤ _ n)
      = algebraMap ℤ (𝓞 (Kf g)) n := fun n => by
    simp [algebraMap_int_eq, map_intCast]
  -- in either case, 2·iO ∈ P
  have h2iO : (2 : 𝓞 (Kf g)) * iO ∈ P := by
    rcases hPprime.mem_or_mem hsplit with hc | hc
    · have hcc := hconjmem _ hc
      rw [map_sub, hconj_iO, hconj_int] at hcc
      have := sub_mem hc hcc
      have heq2 : (iO - algebraMap ℤ (𝓞 (Kf g)) a) - (-iO - algebraMap ℤ (𝓞 (Kf g)) a)
          = 2 * iO := by ring
      rwa [heq2] at this
    · have hcc := hconjmem _ hc
      rw [map_add, hconj_iO, hconj_int] at hcc
      have := sub_mem hc hcc
      have heq2 : (iO + algebraMap ℤ (𝓞 (Kf g)) a) - (-iO + algebraMap ℤ (𝓞 (Kf g)) a)
          = 2 * iO := by ring
      rwa [heq2] at this
  -- hence 4 ∈ P, so p ∣ 4: contradiction with p ≡ 1 mod 4
  have h4 : algebraMap ℤ (𝓞 (Kf g)) 4 ∈ P := by
    have hprod : ((2 : 𝓞 (Kf g)) * iO) * ((2 : 𝓞 (Kf g)) * iO) ∈ P :=
      Ideal.mul_mem_left _ _ h2iO
    have heq4 : ((2 : 𝓞 (Kf g)) * iO) * ((2 : 𝓞 (Kf g)) * iO)
        = -(algebraMap ℤ (𝓞 (Kf g)) 4) := by
      have h4c : algebraMap ℤ (𝓞 (Kf g)) 4 = 4 := by norm_num [algebraMap_int_eq]
      rw [h4c]
      linear_combination 4 * hiO2
    rw [heq4] at hprod
    simpa using neg_mem hprod
  have hdvd : (p : ℤ) ∣ 4 := by
    have hmem : (4 : ℤ) ∈ P.under ℤ := h4
    rw [← hPlies.over] at hmem
    exact Ideal.mem_span_singleton.mp hmem
  have hdvd' : p ∣ 4 := by exact_mod_cast hdvd
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using hdvd')
  have hpe : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
  omega

/-- [decomp 4] `(m t)` is the squarefree product of all primes of `K_g`
lying over the `p1 i`, `i < t`: each `(p1 i)` factors as
`∏_{P ∈ primesOverP1 g i} P` with all exponents one
(`Kf_ramificationIdxIn_eq_one`), and `m t = ∏_{i<t} p1 i`. -/
theorem span_p1_eq_prod (g i : ℕ) :
    Ideal.span {((p1 i : ℕ) : 𝓞 (Kf g))} = ∏ P ∈ primesOverP1 g i, P := by
  classical
  haveI : Fact (p1 i).Prime := ⟨(p1_spec i).1⟩
  haveI : IsGalois ℚ (Kf g) := Kf_isGalois g
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ :=
    p_prime_facts (p1_spec i).1 (p1_spec i).2
  haveI : (Ideal.span {((p1 i : ℤ))}).IsMaximal := hpmax
  set I : Ideal (𝓞 (Kf g)) :=
    Ideal.map (algebraMap ℤ (𝓞 (Kf g))) (Ideal.span {(p1 i : ℤ)}) with hI
  have hIspan : I = Ideal.span {((p1 i : ℕ) : 𝓞 (Kf g))} := by
    rw [hI, Ideal.map_span, Set.image_singleton]
    norm_num [algebraMap_int_eq]
  have hIne : I ≠ ⊥ := by
    rw [hIspan, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (p1_spec i).1.ne_zero
  have hmemiff : ∀ {P : Ideal (𝓞 (Kf g))},
      P ∈ primesOverP1 g i ↔ P ∈ Ideal.primesOver (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) :=
    fun {P} => IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 (Kf g))
  have hcount : ∀ P ∈ primesOverP1 g i, (UniqueFactorizationMonoid.normalizedFactors I).count P = 1 := by
    intro P hP
    obtain ⟨hPp, hPlies⟩ := hmemiff.mp hP
    haveI := hPp
    haveI := hPlies
    have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hIne hPp hPne]
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p1 i : ℤ)}) P
      (Kf g ≃ₐ[ℚ] Kf g)]
    exact Kf_ramificationIdxIn_eq_one g (p1 i) (p1_spec i).1 (p1_spec i).2
  have htofin : (UniqueFactorizationMonoid.normalizedFactors I).toFinset = primesOverP1 g i := by
    rw [show primesOverP1 g i
        = IsDedekindDomain.primesOverFinset (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) from rfl]
    rw [IsDedekindDomain.primesOverFinset, UniqueFactorizationMonoid.factors_eq_normalizedFactors]
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors I).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro P
    by_cases hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I
    · exact le_of_eq (hcount P (htofin ▸ Multiset.mem_toFinset.mpr hP))
    · simp [Multiset.count_eq_zero_of_notMem hP]
  have hval : (primesOverP1 g i).val = UniqueFactorizationMonoid.normalizedFactors I := by
    rw [← htofin, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  rw [← hIspan, Finset.prod_eq_multiset_prod]
  rw [hval, Multiset.map_id']
  exact (Ideal.prod_normalizedFactors_eq_self hIne).symm

theorem Kf_span_m_eq_prod (g t : ℕ) :
    Ideal.span {((m t : ℕ) : 𝓞 (Kf g))} =
      ∏ i ∈ Finset.range t, ∏ P ∈ primesOverP1 g i, P := by
  have hcast : ((m t : ℕ) : 𝓞 (Kf g)) = ∏ i ∈ Finset.range t, ((p1 i : ℕ) : 𝓞 (Kf g)) := by
    rw [m]
    push_cast
    rfl
  rw [hcast, ← Ideal.prod_span_singleton]
  exact Finset.prod_congr rfl fun i _ => span_p1_eq_prod g i

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
  classical
  set σ : 𝓞 (Kf g) ≃+* 𝓞 (Kf g) :=
    (ringOfIntegersComplexConj (Kf g)).toRingEquiv with hσdef
  have hσ_eq : ∀ A : Ideal (𝓞 (Kf g)),
      Ideal.map σ A = Ideal.map (ringOfIntegersComplexConj (Kf g)) A := fun A => rfl
  set S : Finset (Ideal (𝓞 (Kf g))) :=
    (Finset.range t).biUnion (fun i => primesOverP1 g i) with hSdef
  have hmem : ∀ {i : ℕ} {P : Ideal (𝓞 (Kf g))}, P ∈ primesOverP1 g i →
      P ∈ Ideal.primesOver (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) := by
    intro i P hP
    obtain ⟨hpz, hp0, hpprime, hpmax, _⟩ := p_prime_facts (p1_spec i).1 (p1_spec i).2
    haveI : (Ideal.span {((p1 i : ℤ))}).IsMaximal := hpmax
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 (Kf g))).mp hP
  have hσ_fix : ∀ n : ℤ, σ.symm (algebraMap ℤ (𝓞 (Kf g)) n) = algebraMap ℤ (𝓞 (Kf g)) n := by
    intro n
    rw [algebraMap_int_eq]
    exact map_intCast (σ.symm : 𝓞 (Kf g) →+* 𝓞 (Kf g)) n
  have hconj_under : ∀ {i : ℕ} {P : Ideal (𝓞 (Kf g))},
      P ∈ Ideal.primesOver (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) →
      Ideal.map σ P ∈ Ideal.primesOver (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) := by
    intro i P hP
    obtain ⟨hPp, hPlies⟩ := hP
    refine ⟨Ideal.map_isPrime_of_equiv σ, ⟨?_⟩⟩
    have hunder : Ideal.under ℤ (Ideal.map σ P) = Ideal.under ℤ P := by
      ext n
      simp only [Ideal.mem_comap]
      rw [← Ideal.comap_symm, Ideal.mem_comap, hσ_fix]
    rw [hunder]
    exact hPlies.over
  have hdisj : ∀ i ∈ Finset.range t, ∀ j ∈ Finset.range t, i ≠ j →
      Disjoint (primesOverP1 g i) (primesOverP1 g j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro P hPi hPj
    obtain ⟨hPp, hPliesi⟩ := hmem hPi
    obtain ⟨_, hPliesj⟩ := hmem hPj
    have hspan : Ideal.span {(p1 i : ℤ)} = Ideal.span {(p1 j : ℤ)} := by
      rw [hPliesi.over, hPliesj.over]
    have hassoc : Associated ((p1 i : ℤ)) ((p1 j : ℤ)) :=
      Ideal.span_singleton_eq_span_singleton.mp hspan
    have hnat : p1 i = p1 j := by
      have := Int.associated_iff_natAbs.mp hassoc
      simpa using this
    exact hij (p1_strictMono.injective hnat)
  have hSprime : ∀ P ∈ S, P.IsPrime := by
    intro P hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_biUnion.mp hP
    exact (hmem hPi).1
  have hSne : ∀ P ∈ S, P ≠ ⊥ := by
    intro P hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨hpz, hp0, _, hpmax, _⟩ := p_prime_facts (p1_spec i).1 (p1_spec i).2
    haveI := (hmem hPi).2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hSinv : ∀ P ∈ S, Ideal.map σ P ∈ S := by
    intro P hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_biUnion.mp hP
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    obtain ⟨hpz, hp0, hpprime, hpmax, _⟩ := p_prime_facts (p1_spec i).1 (p1_spec i).2
    haveI : (Ideal.span {((p1 i : ℤ))}).IsMaximal := hpmax
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 (Kf g))).mpr
      (hconj_under (hmem hPi))
  have hcc : ∀ x : 𝓞 (Kf g), σ (σ x) = x := by
    intro x
    have h1 := NumberField.IsCMField.coe_ringOfIntegersComplexConj (Kf g) (σ x)
    have h2 := NumberField.IsCMField.coe_ringOfIntegersComplexConj (Kf g) x
    have h3 := NumberField.IsCMField.complexConj_apply_apply (Kf g) (x : Kf g)
    have hco : ((σ (σ x) : 𝓞 (Kf g)) : Kf g) = ((x : 𝓞 (Kf g)) : Kf g) := by
      rw [show ((σ (σ x) : 𝓞 (Kf g)) : Kf g)
          = NumberField.IsCMField.complexConj (Kf g) ((σ x : 𝓞 (Kf g)) : Kf g) from h1,
        show ((σ x : 𝓞 (Kf g)) : Kf g)
          = NumberField.IsCMField.complexConj (Kf g) ((x : 𝓞 (Kf g)) : Kf g) from h2, h3]
    exact_mod_cast hco
  have hsymm_self : ∀ y, σ.symm y = σ y := by
    intro y
    apply σ.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hcc y).symm
  have hSinvol : ∀ P ∈ S, Ideal.map σ (Ideal.map σ P) = P := by
    intro P _
    ext x
    rw [← Ideal.comap_symm, ← Ideal.comap_symm, Ideal.mem_comap, Ideal.mem_comap]
    rw [hsymm_self, hsymm_self, hcc x]
  have hSfree : ∀ P ∈ S, Ideal.map σ P ≠ P := by
    intro P hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_biUnion.mp hP
    rw [hσ_eq]
    exact Kf_conj_primesOver_ne g (p1 i) (p1_spec i).1 (p1_spec i).2 P (hmem hPi)
  obtain ⟨G, hGcard, hGprod⟩ :=
    exists_transversal_family σ S hSprime hSne hSinv hSinvol hSfree
  refine ⟨G, ?_, ?_⟩
  · have hScard : t * 2 ^ g ≤ S.card := by
      rw [hSdef, Finset.card_biUnion hdisj]
      calc t * 2 ^ g = ∑ _i ∈ Finset.range t, 2 ^ g := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range t, (primesOverP1 g i).card := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hge := Kf_card_primesOver_ge g (p1 i) (p1_spec i).1 (p1_spec i).2
            obtain ⟨hpz, hp0, hpprime, hpmax, _⟩ :=
              p_prime_facts (p1_spec i).1 (p1_spec i).2
            haveI : (Ideal.span {((p1 i : ℤ))}).IsMaximal := hpmax
            rwa [← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 (Kf g)),
              Set.ncard_coe_finset] at hge
    have hhalf : t * 2 ^ (g - 1) ≤ S.card / 2 := by
      have h2g : 2 ^ g = 2 ^ (g - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [h2g, ← mul_assoc] at hScard
      omega
    calc (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤ (2 : ℝ) ^ (S.card / 2) := by
          exact pow_le_pow_right₀ (by norm_num) hhalf
    _ ≤ G.card := by exact_mod_cast hGcard
  · intro A hA
    rw [← hσ_eq, hGprod A hA, hSdef, Finset.prod_biUnion hdisj]
    exact (Kf_span_m_eq_prod g t).symm

/-
The ideal norm is invariant under the CM complex conjugation.
-/
theorem absNorm_map_conj (g : ℕ) (A : Ideal (𝓞 (Kf g))) :
    Ideal.absNorm (Ideal.map (ringOfIntegersComplexConj (Kf g)) A) = Ideal.absNorm A := by
  have h_card :
      Submodule.cardQuot A =
        Submodule.cardQuot (Ideal.map (ringOfIntegersComplexConj (Kf g)) A) := by
    unfold Submodule.cardQuot AddSubgroup.index
    refine' Nat.card_congr _;
    refine' ( Quotient.congr _ _ );
    exact ( ringOfIntegersComplexConj ( Kf g ) ).toEquiv;
    intro a₁ a₂
    have hiff : ∀ x : 𝓞 (Kf g), x ∈ A ↔
        (ringOfIntegersComplexConj (Kf g)) x ∈ Ideal.map (ringOfIntegersComplexConj (Kf g)) A := by
      intro x
      rw [Ideal.mem_map_iff_of_surjective _ (AlgEquiv.surjective _)]
      exact ⟨fun h => ⟨x, h, rfl⟩,
        by rintro ⟨y, hy, hy'⟩; exact (ringOfIntegersComplexConj (Kf g)).injective hy' ▸ hy⟩
    simp only [QuotientAddGroup.leftRel_apply, Submodule.mem_toAddSubgroup]
    have key := hiff (-a₁ + a₂)
    rw [map_add, map_neg] at key
    simpa using key
  simpa [Ideal.absNorm] using h_card.symm

/-
At every infinite place, `z · conj z` has value `w(z)^2`.
-/
theorem place_mul_conj (g : ℕ) (z : 𝓞 (Kf g)) (w : InfinitePlace (Kf g)) :
    w (algebraMap (𝓞 (Kf g)) (Kf g) (z * ringOfIntegersComplexConj (Kf g) z))
      = (w (algebraMap (𝓞 (Kf g)) (Kf g) z)) ^ 2 := by
  rw [map_mul, map_mul, sq]
  congr 1
  have h : algebraMap (𝓞 (Kf g)) (Kf g) (ringOfIntegersComplexConj (Kf g) z)
      = complexConj (Kf g) (algebraMap (𝓞 (Kf g)) (Kf g) z) :=
    coe_ringOfIntegersComplexConj (Kf g) z
  rw [h, infinitePlace_complexConj]

/-
The absolute norm of `(n)` for a natural number `n` in `𝓞 (Kf g)` is `n^(2^(g+1))`.
-/
theorem absNorm_span_natCast (g : ℕ) (n : ℕ) :
    Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 (Kf g))}) = n ^ 2 ^ (g + 1) := by
  -- By definition of algebra norm, we know that the norm of `n` in `Kf g` is `n^{[Kf g : ℚ]}`.
  have h_norm : Algebra.norm ℤ (n : (𝓞 (Kf g))) = n ^ (Module.finrank ℚ (Kf g)) := by
    erw [ Algebra.norm_apply ];
    erw [ show ( Algebra.lmul ℤ ( 𝓞 ( Kf g ) ) ) n = ( n : ℤ ) • LinearMap.id from ?_ ];
    · erw [ LinearMap.det_smul ] ; norm_num;
      rw [ ← NumberField.RingOfIntegers.rank ];
    · ext; simp [Algebra.lmul];
  convert congr_arg Int.natAbs h_norm using 1;
  · rw [ Ideal.absNorm_span_singleton ];
  · norm_num [ Kf_finrank ]

/-
If `A · conj A = (m)` then `absNorm A = m^(2^g)`.
-/
theorem absNorm_of_mul_conj (g : ℕ) (A : Ideal (𝓞 (Kf g))) (n : ℕ)
    (h : A * Ideal.map (ringOfIntegersComplexConj (Kf g)) A = Ideal.span {((n : ℕ) : 𝓞 (Kf g))}) :
    Ideal.absNorm A = n ^ 2 ^ g := by
  apply_fun Ideal.absNorm at h;
  rw [ Ideal.absNorm.map_mul ] at h;
  rw [ absNorm_map_conj, absNorm_span_natCast ] at h;
  rw [ ← sq_eq_sq₀ ] <;> first | positivity | ring_nf at * ; aesop;

/-- The product of `w(y · conj y)` over all infinite places equals `absNorm (y)`. -/
theorem prod_place_mul_conj (g : ℕ) (y : 𝓞 (Kf g)) :
    ∏ w : InfinitePlace (Kf g),
        w (algebraMap (𝓞 (Kf g)) (Kf g) (y * ringOfIntegersComplexConj (Kf g) y))
      = (Ideal.absNorm (Ideal.span {y}) : ℝ) := by
  have htc := Kf_isTotallyComplex g
  convert NumberField.InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 (Kf g)) (Kf g) y) using 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [place_mul_conj g y w, IsTotallyComplex.mult_eq w]
  · rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
    push_cast [Int.abs_eq_natAbs]
    exact_mod_cast Nat.cast_natAbs (Algebra.norm ℤ y)

/-
Pigeonhole: some fiber of `f` has size at least `s.card / card β`.
-/
theorem exists_fiber_card_ge {α β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (f : α → β) :
    ∃ y : β, s.card ≤ {x ∈ s | f x = y}.card * Fintype.card β := by
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_max_image (Finset.univ : Finset β)
    (fun y => {x ∈ s | f x = y}.card) Finset.univ_nonempty
  refine ⟨y₀, ?_⟩
  calc s.card = ∑ y : β, {x ∈ s | f x = y}.card := by
              rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))]
    _ ≤ ∑ _y : β, {x ∈ s | f x = y₀}.card :=
              Finset.sum_le_sum (fun y _ => hy₀ y (Finset.mem_univ y))
    _ = {x ∈ s | f x = y₀}.card * Fintype.card β := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-
The maximal totally real subfield of `K_g` has degree `2^g` over `ℚ`.
-/
theorem Kf_maximalReal_finrank (g : ℕ) :
    Module.finrank ℚ (maximalRealSubfield (Kf g)) = 2 ^ g := by
  have h1 : Module.finrank ℚ (Kf g) = 2 ^ (g + 1) := Kf_finrank g
  have h2 : Module.finrank (maximalRealSubfield (Kf g)) (Kf g) = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := Module.finrank_mul_finrank ℚ (maximalRealSubfield (Kf g)) (Kf g)
  rw [h1, h2, pow_succ] at h3
  omega

/-
The quotient of the unit group by squares is finite.
-/
theorem units_sq_quot_finite (F : Type) [Field F] [NumberField F] :
    Finite ((𝓞 F)ˣ ⧸ (MonoidHom.range (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ))) := by
  have h_fg : AddGroup.FG (Additive ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range)) := by
    have h_finite_gen : Monoid.FG ((𝓞 F)ˣ) := by
      grind +suggestions;
    convert AddGroup.fg_iff_addMonoid_fg.mpr _;
    obtain ⟨ S, hS ⟩ := h_finite_gen;
    refine' ⟨ S.image ( fun x => QuotientGroup.mk x ), _ ⟩;
    simp_all +decide [ SetLike.ext_iff, AddSubmonoid.mem_closure ];
    intro a S_1 hS_1; obtain ⟨ x, rfl ⟩ := QuotientGroup.mk_surjective a; simp_all +decide [ Set.subset_def, Submonoid.mem_closure ] ;
    specialize hS x ( Submonoid.comap ( QuotientGroup.mk' ( powMonoidHom 2 |> MonoidHom.range ) ) ( AddSubmonoid.toSubmonoid S_1 ) ) ; aesop;
  have h_add_group : ∀ (G : Type) [AddCommGroup G] [AddGroup.FG G], (∀ g : G, 2 • g = 0) → Finite G := by
    intros G _ _ hG
    have h_vector_space : Module (ZMod 2) G := AddCommGroup.zmodModule hG
    have h_finite_dim : FiniteDimensional (ZMod 2) G := by
      have h_fg : Module.Finite (ZMod 2) G := by
        obtain ⟨ s, hs ⟩ := ‹AddGroup.FG G›;
        use s;
        simp_all +decide [ SetLike.ext_iff, AddSubgroup.mem_closure ];
        intro x; specialize hs x ( Submodule.toAddSubgroup ( Submodule.span ( ZMod 2 ) ( s : Set G ) ) ) ; simp_all +decide [ Set.subset_def, Submodule.mem_span ] ;
      lia;
    exact Finite.of_equiv _ ( ( Module.finBasis ( ZMod 2 ) G ).equivFun.symm.toEquiv );
  have hfin : Finite (Additive ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range)) :=
    h_add_group ( Additive ( ( 𝓞 F ) ˣ ⧸ ( powMonoidHom 2 : ( 𝓞 F ) ˣ →* ( 𝓞 F ) ˣ ).range ) ) <| by
      rintro ⟨ a ⟩ ; exact QuotientGroup.eq.mpr ( by aesop )
  exact @Finite.of_equiv ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range)
    (Additive ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range)) hfin Additive.toMul

/-
Pigeonhole over square-classes of real units.
-/
theorem units_square_pigeonhole (g : ℕ) {α : Type*} (F₁ : Finset α)
    (ν : α → (𝓞 (maximalRealSubfield (Kf g)))ˣ) :
    ∃ F₂ : Finset α, F₂ ⊆ F₁ ∧ F₁.card ≤ F₂.card * 2 ^ 2 ^ g ∧
      ∀ A ∈ F₂, ∀ A' ∈ F₂, ∃ δ : (𝓞 (maximalRealSubfield (Kf g)))ˣ, ν A * (ν A')⁻¹ = δ ^ 2 := by
  obtain ⟨y, hy⟩ : ∃ y : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ), F₁.card ≤ (Finset.filter (fun A => QuotientGroup.mk (ν A) = y) F₁).card * 2 ^ 2 ^ g := by
    have h_finite : Finite ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) := by
      convert units_sq_quot_finite ( maximalRealSubfield ( Kf g ) );
    have h_finite : Fintype ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) := by
      exact Fintype.ofFinite _;
    have h_finite : Fintype.card ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) ≤ 2 ^ 2 ^ g := by
      simpa [Subgroup.index_eq_card, Nat.card_eq_fintype_card] using
        (units_sq_index_le ( ↥ ( maximalRealSubfield ( Kf g ) ) ) |>.trans
          (pow_le_pow_right₀ ( by decide ) ( Kf_maximalReal_finrank g |>.le )))
    have := @exists_fiber_card_ge;
    exact Exists.elim ( this F₁ ( fun A => QuotientGroup.mk ( ν A ) ) ) fun y hy => ⟨ y, hy.trans ( Nat.mul_le_mul_left _ h_finite ) ⟩;
  refine' ⟨ _, _, hy, _ ⟩;
  · exact Finset.filter_subset _ _;
  · intro A hA A' hA'
    obtain ⟨δ, hδ⟩ : ∃ δ : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ, (ν A)⁻¹ * (ν A') = δ ^ 2 := by
      have h_eq : (ν A)⁻¹ * ν A' ∈ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ) := by
        rw [ ← QuotientGroup.eq_one_iff ] at * ; aesop;
      exact h_eq.imp fun x hx => by simpa [ sq ] using hx.symm;
    generalize_proofs at *; (
    exact ⟨ δ⁻¹, by simpa [ mul_comm ] using congr_arg Inv.inv hδ ⟩)

/-
Two associate conjugation-fixed integers differ by a unit coming from `K⁺`.
-/
theorem descent_unit (g : ℕ) (a b : 𝓞 (Kf g))
    (ha : ringOfIntegersComplexConj (Kf g) a = a)
    (hb : ringOfIntegersComplexConj (Kf g) b = b) (hb0 : b ≠ 0)
    (hab : Ideal.span {a} = Ideal.span {b}) :
    ∃ u : (𝓞 (maximalRealSubfield (Kf g)))ˣ,
      algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (u : 𝓞 (maximalRealSubfield (Kf g))) * b = a := by
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 (Kf g))ˣ, a = u * b := by
    have := Ideal.span_singleton_eq_span_singleton.mp hab;
    obtain ⟨ u, hu ⟩ := this.symm;
    exact ⟨ u, by rw [ ← hu, mul_comm ] ⟩;
  have h_fixed : (complexConj (Kf g)) (u : Kf g) = (u : Kf g) := by
    have h_conj_u : (ringOfIntegersComplexConj (Kf g)) (u : (𝓞 (Kf g))) = (u : (𝓞 (Kf g))) := by
      simp_all +decide [ ringOfIntegersComplexConj ];
    rw [← coe_ringOfIntegersComplexConj]
    exact congr_arg ( algebraMap ( 𝓞 ( Kf g ) ) ( Kf g ) ) h_conj_u
  have := @Units.complexConj_eq_self_iff ( Kf g );
  obtain ⟨ v, hv ⟩ := this u |>.1 h_fixed;
  refine ⟨v, ?_⟩
  apply RingOfIntegers.ext
  calc ((algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g))
        (v : 𝓞 (maximalRealSubfield (Kf g))) * b : 𝓞 (Kf g)) : Kf g)
      = ((algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g))
          (v : 𝓞 (maximalRealSubfield (Kf g))) : 𝓞 (Kf g)) : Kf g) * (b : Kf g) := by
        push_cast
        ring
  _ = ((u : 𝓞 (Kf g)) : Kf g) * (b : Kf g) := by
        congr 1
  _ = (((u : 𝓞 (Kf g)) * b : 𝓞 (Kf g)) : Kf g) := by
        push_cast
        ring
  _ = (a : Kf g) := by rw [← hu]

/-- Conjugation is involutive on the ring of integers. -/
theorem ringConj_ringConj (g : ℕ) (x : 𝓞 (Kf g)) :
    ringOfIntegersComplexConj (Kf g) (ringOfIntegersComplexConj (Kf g) x) = x := by
  apply RingOfIntegers.ext
  rw [coe_ringOfIntegersComplexConj, coe_ringOfIntegersComplexConj, complexConj_apply_apply]

/-
After pigeonholing, a subfamily with a common `z · conj z = μ`.
-/
set_option maxHeartbeats 1600000 in
theorem norm_constant_subfamily (g : ℕ) {α : Type*} (F₁ : Finset α) (y : α → 𝓞 (Kf g))
    (hy0 : ∀ A ∈ F₁, y A ≠ 0)
    (hassoc : ∀ A ∈ F₁, ∀ A' ∈ F₁,
      Ideal.span {y A * ringOfIntegersComplexConj (Kf g) (y A)}
        = Ideal.span {y A' * ringOfIntegersComplexConj (Kf g) (y A')}) :
    ∃ (F₂ : Finset α) (μ : 𝓞 (Kf g)), F₂ ⊆ F₁ ∧ F₁.card ≤ F₂.card * 2 ^ 2 ^ g ∧
      ∀ A ∈ F₂, ∃ z : 𝓞 (Kf g), Ideal.span {z} = Ideal.span {y A} ∧
        z * ringOfIntegersComplexConj (Kf g) z = μ := by
  by_cases hF₁ : F₁.Nonempty;
  · obtain ⟨A₀, hA₀⟩ : ∃ A₀ ∈ F₁, True := by
      exact ⟨ hF₁.choose, hF₁.choose_spec, trivial ⟩;
    -- For each `A ∈ F₁`, define `U A : (𝓞 (maximalRealSubfield (Kf g)))ˣ` by `descent_unit` with `a := ν A`, `b := ν A₀`.
    have hU : ∀ A ∈ F₁, ∃ U : (𝓞 (maximalRealSubfield (Kf g)))ˣ, algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (U : 𝓞 (maximalRealSubfield (Kf g))) * (y A₀ * ringOfIntegersComplexConj (Kf g) (y A₀)) = y A * ringOfIntegersComplexConj (Kf g) (y A) := by
      intro A hA
      apply descent_unit g (y A * ringOfIntegersComplexConj (Kf g) (y A)) (y A₀ * ringOfIntegersComplexConj (Kf g) (y A₀)) (by
      simp +decide [ ringConj_ringConj ];
      exact mul_comm _ _) (by
      grind +suggestions) (by
      simp_all +decide [ mul_eq_zero ]) (by
      exact hassoc A hA A₀ hA₀.1);
    choose! U hU using hU;
    obtain ⟨F₂, hF₂⟩ := units_square_pigeonhole g F₁ U;
    obtain ⟨A₁, hA₁⟩ : ∃ A₁ ∈ F₂, True := by
      exact Exists.elim ( Finset.card_pos.mp ( by nlinarith [ Finset.card_pos.mpr hF₁, Nat.one_le_pow ( 2 ^ g ) 2 zero_lt_two ] ) ) fun x hx => ⟨ x, hx, trivial ⟩;
    refine' ⟨ F₂, y A₁ * ( ringOfIntegersComplexConj ( Kf g ) ) ( y A₁ ), hF₂.1, hF₂.2.1, fun A hA => _ ⟩;
    obtain ⟨ δ, hδ ⟩ := hF₂.2.2 A hA A₁ hA₁.1;
    refine' ⟨ y A * ( Units.map ( algebraMap ( 𝓞 ( maximalRealSubfield ( Kf g ) ) ) ( 𝓞 ( Kf g ) ) |> RingHom.toMonoidHom ) δ⁻¹ ), _, _ ⟩;
    · refine' le_antisymm _ _ <;> simp +decide [ Ideal.span_singleton_le_span_singleton ];
      exact Ideal.mem_span_singleton.mpr
        ⟨algebraMap _ _ ((δ : (𝓞 (maximalRealSubfield (Kf g)))ˣ) : 𝓞 (maximalRealSubfield (Kf g))),
         by rw [mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]⟩;
    · have hδ_eq : algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (U A) = (algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) δ) ^ 2 * algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (U A₁) := by
        replace hδ := congr_arg ( fun x : ( 𝓞 ( maximalRealSubfield ( Kf g ) ) ) ˣ => ( algebraMap ( 𝓞 ( maximalRealSubfield ( Kf g ) ) ) ( 𝓞 ( Kf g ) ) ) x ) hδ ; simp_all +decide [ mul_assoc, pow_two ];
        simp_all +decide [ ← mul_assoc ];
        rw [ ← hδ, mul_assoc ];
        simp +decide [ ← map_mul ];
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      simp_all +decide [ ← mul_assoc, ← hU A ( hF₂.1 hA ), ← hU A₁ ( hF₂.1 hA₁ ) ];
      simp +decide [ sq, mul_assoc ];
      simp +decide [ ← mul_assoc, ← map_mul ];
  · aesop

/-
Class-group pigeonhole: a subfamily lying in one class, an ideal `b` in the inverse
class, and principal generators `y A` of `A * b`.
-/
theorem stage1 (g : ℕ) (F : Finset (Ideal (𝓞 (Kf g)))) (hF : ∀ A ∈ F, A ≠ ⊥) :
    ∃ (b : Ideal (𝓞 (Kf g))) (F₁ : Finset (Ideal (𝓞 (Kf g)))) (y : Ideal (𝓞 (Kf g)) → 𝓞 (Kf g)),
      b ≠ ⊥ ∧ F₁ ⊆ F ∧ F.card ≤ F₁.card * NumberField.classNumber (Kf g) ∧
      ∀ A ∈ F₁, y A ≠ 0 ∧ Ideal.span {y A} = A * b := by
  -- Define `φ : Ideal (𝓞 (Kf g)) → ClassGroup (𝓞 (Kf g))` by `φ A := if h : A ≠ ⊥ then ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero h⟩ else 1`.
  set φ : Ideal (𝓞 (Kf g)) → ClassGroup (𝓞 (Kf g)) := fun A =>
    if h : A ≠ ⊥ then ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero h⟩ else 1;
  -- By `exists_fiber_card_ge F φ`, there is a class `c` with `F.card ≤ {A ∈ F | φ A = c}.card * Fintype.card (ClassGroup (𝓞 (Kf g)))`.
  obtain ⟨c, hc⟩ : ∃ c : ClassGroup (𝓞 (Kf g)), F.card ≤ (Finset.filter (fun A => φ A = c) F).card * Fintype.card (ClassGroup (𝓞 (Kf g))) := by
    convert exists_fiber_card_ge F φ;
  -- Choose `b' ∈ nonZeroDivisors (Ideal (𝓞 (Kf g)))` with `ClassGroup.mk0 b' = c⁻¹`;
  obtain ⟨b', hb'⟩ : ∃ b' : { x : Ideal (𝓞 (Kf g)) // x ∈ nonZeroDivisors (Ideal (𝓞 (Kf g)) ) }, ClassGroup.mk0 b' = c⁻¹ := by
    have := ClassGroup.mk0_surjective ( c⁻¹ );
    exact this;
  refine' ⟨ b', Finset.filter ( fun A => φ A = c ) F, _ ⟩;
  simp +zetaDelta at *;
  refine' ⟨ _, _, _ ⟩;
  · exact fun h => by simpa [ h ] using b'.2;
  · simpa [NumberField.classNumber] using hc;
  · have h_principal : ∀ A ∈ F, (if h : A = ⊥ then 1 else ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero h⟩) = c → ∃ a : 𝓞 (Kf g), A * b' = Ideal.span {a} ∧ a ≠ 0 := by
      intro A hA hA'; split_ifs at hA' ; simp_all +decide  ;
      have h_principal : ClassGroup.mk0 (⟨A, mem_nonZeroDivisors_of_ne_zero ‹_›⟩ * b') = 1 := by
        convert congr_arg₂ ( · * · ) hA' hb' using 1;
        · convert map_mul ( ClassGroup.mk0 : nonZeroDivisors ( Ideal ( 𝓞 ( Kf g ) ) ) →* ClassGroup ( 𝓞 ( Kf g ) ) ) _ _ using 1;
        · rw [ mul_inv_cancel ];
      rw [ ClassGroup.mk0_eq_one_iff ] at h_principal;
      obtain ⟨ a, ha ⟩ := h_principal;
      refine' ⟨ a, _, _ ⟩ <;> simp_all +decide ;
      intro ha'; simp_all +decide  ;
      exact absurd ha ( by exact fun h => by have := b'.2; simp_all +decide [ nonZeroDivisors ] );
    choose! a ha₁ ha₂ using h_principal;
    exact ⟨ a, fun A hA hA' => ⟨ ha₂ A hA hA', ha₁ A hA hA' ▸ rfl ⟩ ⟩

set_option maxHeartbeats 1600000 in
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
using `infinitePlace_complexConj`.
-/
theorem arithmetic_construction (g t : ℕ) (hg : 1 ≤ g) (ht : 1 ≤ t) :
    ∃ (b : Ideal (𝓞 (Kf g))) (μ : Kf g) (Z : Finset (𝓞 (Kf g))),
      b ≠ ⊥ ∧ μ ≠ 0 ∧
      (∀ z ∈ Z, z ∈ b) ∧
      (∀ z ∈ Z, ∀ w : InfinitePlace (Kf g),
        (w (algebraMap (𝓞 (Kf g)) (Kf g) z)) ^ 2 = w μ) ∧
      (∏ w : InfinitePlace (Kf g), w μ) = (m t : ℝ) ^ 2 ^ g * (Ideal.absNorm b : ℝ) ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤
        (Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := by
  -- Let `conj := ringOfIntegersComplexConj (Kf g)` and `m := m t`.
  set conj := ringOfIntegersComplexConj (Kf g)
  set m := m t;
  -- From `exists_ideal_family g t hg` obtain `F` with `(2:ℝ)^(t*2^(g-1)) ≤ F.card` and `hFm : ∀ A ∈ F, A * Ideal.map conj A = Ideal.span {(m : 𝓞 (Kf g))}`.
  obtain ⟨F, hFcard, hF⟩ := exists_ideal_family g t hg;
  -- Apply `stage1 g F` to get `b, F₁, y` with `b ≠ ⊥`, `F₁ ⊆ F`, `F.card ≤ F₁.card * classNumber (Kf g)`, and `hy : ∀ A ∈ F₁, y A ≠ 0 ∧ Ideal.span {y A} = A * b`.
  obtain ⟨b, F₁, y, hb, hF₁, hF₁card, hy⟩ := stage1 g F (by
  intro A hA hA'; specialize hF A hA; simp_all +decide  ;
  rw [ eq_comm, Ideal.span_singleton_eq_bot ] at hF ; norm_cast at hF;
  exact absurd hF <| ne_of_gt <| Finset.prod_pos fun i hi => Nat.Prime.pos <| p1_spec i |>.1);
  -- Establish `hassoc : ∀ A ∈ F₁, ∀ A' ∈ F₁, Ideal.span {y A * conj (y A)} = Ideal.span {y A' * conj (y A')}` by showing each side equals `Ideal.span {(m : 𝓞 (Kf g))} * (b * Ideal.map conj b)`.
  have hassoc : ∀ A ∈ F₁, ∀ A' ∈ F₁, Ideal.span {y A * conj (y A)} = Ideal.span {y A' * conj (y A')} := by
    intros A hA A' hA'
    have h_eq : Ideal.span {y A * conj (y A)} = Ideal.span {(m : 𝓞 (Kf g))} * (b * Ideal.map conj b) := by
      have h_eq : Ideal.span {y A * conj (y A)} = Ideal.span {y A} * Ideal.map conj (Ideal.span {y A}) := by
        simp +decide [ Ideal.span_singleton_mul_span_singleton, Ideal.map_span ];
      rw [ h_eq, hy A hA |>.2 ];
      rw [ ← hF A ( hF₁ hA ) ];
      rw [ Ideal.map_mul ] ; ring
    have h_eq' : Ideal.span {y A' * conj (y A')} = Ideal.span {(m : 𝓞 (Kf g))} * (b * Ideal.map conj b) := by
      have h_eq' : Ideal.span {y A' * conj (y A')} = Ideal.span {y A'} * Ideal.map conj (Ideal.span {y A'}) := by
        simp +decide [ Ideal.map_span, Ideal.span_singleton_mul_span_singleton ];
      rw [ h_eq', hy A' hA' |>.2, Ideal.map_mul ];
      rw [ ← hF A' ( hF₁ hA' ) ] ; ring
    rw [h_eq, h_eq'];
  -- Apply `norm_constant_subfamily g F₁ y (fun A hA => (hy A hA).1) hassoc` to get `F₂ ⊆ F₁`, `μ₀`, `F₁.card ≤ F₂.card * 2^(2^g)`, and `hz : ∀ A ∈ F₂, ∃ z, Ideal.span {z} = Ideal.span {y A} ∧ z * conj z = μ₀`.
  obtain ⟨F₂, μ₀, hF₂, hF₂card, hz⟩ := norm_constant_subfamily g F₁ y (fun A hA => (hy A hA).1) hassoc;
  -- With `Classical.choose`, define `zf` so that for `A ∈ F₂`: `Ideal.span {zf A} = Ideal.span {y A}` and `zf A * conj (zf A) = μ₀`.
  obtain ⟨zf, hzf⟩ : ∃ zf : Ideal (𝓞 (Kf g)) → 𝓞 (Kf g), ∀ A ∈ F₂, Ideal.span {zf A} = Ideal.span {y A} ∧ zf A * conj (zf A) = μ₀ := by
    exact ⟨ fun A => if hA : A ∈ F₂ then Classical.choose ( hz A hA ) else 0, fun A hA => by simpa [ hA ] using Classical.choose_spec ( hz A hA ) ⟩;
  refine' ⟨ b, algebraMap (𝓞 (Kf g)) (Kf g) μ₀, F₂.image zf, hb, _, _, _, _ ⟩;
  · -- Since $μ₀$ is a product of non-zero elements, it cannot be zero.
    have hμ₀_nonzero : μ₀ ≠ 0 := by
      obtain ⟨A, hA⟩ : ∃ A ∈ F₂, True := by
        contrapose! hFcard;
        simp_all +decide [ Finset.eq_empty_of_forall_notMem hFcard ];
      intro hμ₀_zero
      have hzf_zero : zf A = 0 := by
        simp_all +decide ;
      have := hzf A hA.1; simp_all +decide  ;
      exact hy A ( hF₂ hA ) |>.1 ( by simpa using this.symm );
    intro h
    exact hμ₀_nonzero (IsFractionRing.injective (𝓞 (Kf g)) (Kf g) (by rw [map_zero]; exact h))
  · simp +zetaDelta at *;
    intro A hA;
    have hzfA_in_b : Ideal.span {zf A} ≤ b := by
      rw [ hzf A hA |>.1, hy A ( hF₂ hA ) |>.2 ];
      exact Ideal.mul_le_left
    exact hzfA_in_b <| Ideal.mem_span_singleton_self _;
  · simp +zetaDelta at *;
    intro A hA w; rw [ ← hzf A hA |>.2 ] ; rw [ ← place_mul_conj ] ;
  · refine' ⟨ _, _ ⟩;
    · obtain ⟨A₀, hA₀⟩ : ∃ A₀ ∈ F₂, True := by
        contrapose! hFcard;
        simp_all +decide [ Finset.eq_empty_of_forall_notMem hFcard ];
      have h_norm : Ideal.absNorm (Ideal.span {zf A₀}) = m ^ 2 ^ g * Ideal.absNorm b := by
        have h_norm : Ideal.absNorm A₀ = m ^ 2 ^ g := by
          apply absNorm_of_mul_conj g A₀ m (hF A₀ (hF₁ (hF₂ hA₀.left)));
        grind;
      have h_norm : ∏ w : InfinitePlace (Kf g), w (algebraMap (𝓞 (Kf g)) (Kf g) (zf A₀ * conj (zf A₀))) = (Ideal.absNorm (Ideal.span {zf A₀}) : ℝ) := by
        convert prod_place_mul_conj g ( zf A₀ ) using 1;
      aesop;
    · rw [ Finset.card_image_of_injOn ];
      · norm_cast at *;
        nlinarith [ show 0 < classNumber ( Kf g ) from Nat.pos_of_ne_zero ( by aesop ) ];
      · intro A hA A' hA' h_eq;
        have := hzf A hA; have := hzf A' hA'; simp_all +decide  ;
        have := hy A ( hF₂ hA ) ; have := hy A' ( hF₂ hA' ) ; simp_all +decide  ;

/-- The coordinatewise-embeddings map `𝒪_{K_g} → (places → ℂ)`, sending
`x` to `(w.embedding x)_w` — one choice of embedding per conjugate pair.
This is the "Minkowski map" whose image of the ideal `b` is the lattice `Λ`
fed to the geometric core. -/
noncomputable def mink (g : ℕ) :
    𝓞 (Kf g) →+* (NumberField.InfinitePlace (Kf g) → ℂ) :=
  RingHom.pi fun w => w.embedding.comp (algebraMap (𝓞 (Kf g)) (Kf g))

/-- General degree bound: a field obtained by adjoining a finite set of elements, each
integral of degree at most `2`, has degree at most `2 ^ (number of generators)`. -/
theorem finrank_adjoin_finset_le (s : Finset ℂ)
    (h : ∀ a ∈ s, IsIntegral ℚ a ∧ (minpoly ℚ a).natDegree ≤ 2) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (s : Set ℂ)) ≤ 2 ^ s.card := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.coe_empty, IntermediateField.adjoin_empty, IntermediateField.finrank_bot]
      simp
  | @insert a s ha ih =>
      have hmem : ∀ x ∈ s, IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree ≤ 2 :=
        fun x hx => h x (Finset.mem_insert_of_mem hx)
      have ha2 := h a (Finset.mem_insert_self a s)
      have hsplit : IntermediateField.adjoin ℚ ((insert a s : Finset ℂ) : Set ℂ)
          = IntermediateField.adjoin ℚ ({a} : Set ℂ) ⊔ IntermediateField.adjoin ℚ (s : Set ℂ) := by
        rw [Finset.coe_insert, Set.insert_eq, IntermediateField.adjoin_union]
      have hfa : Module.finrank ℚ (IntermediateField.adjoin ℚ ({a} : Set ℂ)) ≤ 2 :=
        (IntermediateField.adjoin.finrank ha2.1).trans_le ha2.2
      rw [hsplit]
      refine le_trans (IntermediateField.finrank_sup_le _ _) ?_
      calc Module.finrank ℚ (IntermediateField.adjoin ℚ ({a} : Set ℂ))
              * Module.finrank ℚ (IntermediateField.adjoin ℚ (s : Set ℂ))
          ≤ 2 * 2 ^ s.card := Nat.mul_le_mul hfa (ih hmem)
        _ = 2 ^ (insert a s).card := by
            rw [Finset.card_insert_of_notMem ha, pow_succ]; ring

/-- Upper bound on the degree of the multiquadratic field: it is generated over `ℚ`
by the `g+1` elements `i, √q3 0, …, √q3 (g-1)`, each of degree at most `2`. -/
theorem Kf_finrank_le (g : ℕ) : Module.finrank ℚ (Kf g) ≤ 2 ^ (g + 1) := by
  have h_deg : ∀ x ∈ ({Complex.I} ∪ ((fun j => ((Real.sqrt (q3 j):ℝ):ℂ)) '' (Finset.range g) : Set ℂ)), IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree ≤ 2 := by
    intro x hx; cases' hx with hx hx <;> simp_all +decide [ IsIntegral ] ;
    · refine' ⟨ _, _ ⟩;
      · exact ⟨ Polynomial.X ^ 2 + 1, by exact Polynomial.monic_X_pow_add_C _ two_ne_zero, by norm_num ⟩;
      · refine' le_trans ( Polynomial.natDegree_le_of_dvd _ _ ) _;
        exacts [ Polynomial.X ^ 2 + 1, minpoly.dvd ℚ Complex.I <| by norm_num [ Complex.ext_iff, sq ], by exact ne_of_apply_ne ( Polynomial.eval 0 ) <| by norm_num, by erw [ Polynomial.natDegree_X_pow_add_C ] ];
    · obtain ⟨ j, hj, rfl ⟩ := hx;
      -- The minimal polynomial of $\sqrt{q3 j}$ over $\mathbb{Q}$ is $x^2 - q3 j$.
      have h_minpoly : minpoly ℚ (Real.sqrt (q3 j) : ℂ) ∣ Polynomial.X ^ 2 - Polynomial.C (q3 j : ℚ) := by
        refine' minpoly.dvd ℚ _ _;
        norm_num [ ← Complex.ofReal_pow, Real.sq_sqrt ( Nat.cast_nonneg _ ) ];
      refine' ⟨ _, _ ⟩;
      · refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( q3 j : ℚ ), _, _ ⟩;
        · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
        · norm_num [ ← Complex.ofReal_pow ];
      · exact le_trans ( Polynomial.natDegree_le_of_dvd h_minpoly ( Polynomial.X_pow_sub_C_ne_zero ( by norm_num ) _ ) ) ( by erw [ Polynomial.natDegree_X_pow_sub_C ] );
  set F : Finset ℂ :=
    insert Complex.I ((Finset.range g).image fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) with hF
  have hset : (F : Set ℂ)
      = insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g) := by
    simp [hF]
  have hKf : Module.finrank ℚ (Kf g)
      = Module.finrank ℚ (IntermediateField.adjoin ℚ (F : Set ℂ)) := by
    rw [Kf, ← hset]
  have hcard : F.card ≤ g + 1 :=
    (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ (Finset.card_image_le.trans (by simp)))
  rw [hKf]
  refine (finrank_adjoin_finset_le F ?_).trans (Nat.pow_le_pow_right (by norm_num) hcard)
  intro a ha
  refine h_deg a ?_
  simp only [hF, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at ha
  rcases ha with rfl | ⟨j, hj, rfl⟩
  · exact Set.mem_union_left _ rfl
  · exact Set.mem_union_right _ ⟨j, Finset.mem_coe.mpr (Finset.mem_range.mpr hj), rfl⟩

/-- Upper bound on the number of infinite places: `K_g` is totally complex, so the
number of places is `finrank/2 ≤ 2^g`. -/
theorem Kf_card_le (g : ℕ) :
    Fintype.card (NumberField.InfinitePlace (Kf g)) ≤ 2 ^ g := by
  have h_card : Fintype.card (InfinitePlace (Kf g)) * 2 ≤ Module.finrank ℚ (Kf g) := by
    have hplaces :=
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces ( Kf g )
    have hfin : Module.finrank ℚ (Kf g) =
        2 * NumberField.InfinitePlace.nrComplexPlaces (Kf g) :=
      NumberField.IsTotallyComplex.finrank ( Kf g )
    rw [hplaces, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, hfin]
    omega
  linarith [ Kf_finrank_le g, pow_succ' 2 g ]

/-- Coordinate formula for the Minkowski map. -/
theorem mink_apply (g : ℕ) (y : 𝓞 (Kf g)) (w : NumberField.InfinitePlace (Kf g)) :
    mink g y w = w.embedding (algebraMap (𝓞 (Kf g)) (Kf g) y) := rfl

/-- The modulus of a Minkowski coordinate is the value of the place. -/
theorem norm_mink_apply (g : ℕ) (y : 𝓞 (Kf g)) (w : NumberField.InfinitePlace (Kf g)) :
    ‖mink g y w‖ = w (algebraMap (𝓞 (Kf g)) (Kf g) y) := by
  rw [mink_apply]; exact NumberField.InfinitePlace.norm_embedding_eq w _

/-- The Minkowski map is injective. -/
theorem mink_injective (g : ℕ) : Function.Injective (mink g) := by
  intro a c h
  have hi : (Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding
        (algebraMap (𝓞 (Kf g)) (Kf g) a)
      = (Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding
        (algebraMap (𝓞 (Kf g)) (Kf g) c) := by
    have hc := congrFun h (Classical.arbitrary _)
    rwa [mink_apply, mink_apply] at hc
  exact RingOfIntegers.coe_injective
    ((Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding.injective hi)

/-- The product of the squares of the place-values of a nonzero element of an ideal `b`
is at least `absNorm b` (since the principal ideal it generates is contained in `b`). -/
theorem absNorm_le_prod_places (g : ℕ) (b : Ideal (𝓞 (Kf g))) (y : 𝓞 (Kf g))
    (hy : y ∈ b) (hy0 : y ≠ 0) :
    (Ideal.absNorm b : ℝ) ≤
      ∏ w : NumberField.InfinitePlace (Kf g),
        (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 := by
  -- Step 1: Rewrite the product as the absolute norm.
  have h1 : ∏ w : NumberField.InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 = (Ideal.absNorm (Ideal.span {y}) : ℝ) := by
    convert NumberField.InfinitePlace.prod_eq_abs_norm ( algebraMap ( 𝓞 ( Kf g ) ) ( Kf g ) y ) using 1;
    · refine' Finset.prod_congr rfl fun w hw => _;
      have h_complex : w.IsComplex := NumberField.IsTotallyComplex.isComplex w
      rw [ NumberField.InfinitePlace.mult ] ; aesop;
    · have := Algebra.coe_norm_int y; norm_cast at *; aesop;
  refine' h1 ▸ mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) _;
  · simp +decide [ hy0 ];
  · exact Ideal.absNorm_dvd_absNorm_of_le ( Ideal.span_le.mpr ( Set.singleton_subset_iff.mpr hy ) )

/-- **Separation.**  A nonzero element of the ideal `b`, under the Minkowski map, cannot
have all of its coordinates small relative to `ρ √(w μ)` once
`ρ^(2·#places)·(m t)^(2^g) < 1`. -/
theorem mink_sep_aux (g t : ℕ) (b : Ideal (𝓞 (Kf g))) (μ : Kf g) (y : 𝓞 (Kf g))
    (hy : y ∈ b) (hy0 : y ≠ 0)
    (hprod : (∏ w : NumberField.InfinitePlace (Kf g), w μ)
        = (m t : ℝ) ^ 2 ^ g * (Ideal.absNorm b : ℝ))
    (ρ : ℝ)
    (hkey : ρ ^ (2 * Fintype.card (NumberField.InfinitePlace (Kf g)))
        * (m t : ℝ) ^ 2 ^ g < 1) :
    ∃ w : NumberField.InfinitePlace (Kf g),
      ρ * Real.sqrt (w μ) < ‖mink g y w‖ := by
  contrapose! hkey; simp_all +decide;
  -- By combining the results from the contrapositive assumption and the properties of the Minkowski map, we derive a contradiction.
  have h_contradiction : (Ideal.absNorm b : ℝ) ≤ ρ ^ (2 * Fintype.card (InfinitePlace (Kf g))) * (∏ w : InfinitePlace (Kf g), (w μ)) := by
    have h_contradiction : (∏ w : InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2) ≤ (ρ ^ 2) ^ (Fintype.card (InfinitePlace (Kf g))) * (∏ w : InfinitePlace (Kf g), (w μ)) := by
      have h_prod_le : ∀ w : InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 ≤ (ρ * Real.sqrt (w μ)) ^ 2 := by
        exact fun w => by simpa only [ ← norm_mink_apply ] using pow_le_pow_left₀ ( by positivity ) ( hkey w ) 2;
      calc
        (∏ w : InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2) ≤
            ∏ w : InfinitePlace (Kf g), (ρ * Real.sqrt (w μ)) ^ 2 := by
          exact Finset.prod_le_prod ( fun _ _ => sq_nonneg _ ) fun w _ => h_prod_le w
        _ = (ρ ^ 2) ^ (Fintype.card (InfinitePlace (Kf g))) *
            (∏ w : InfinitePlace (Kf g), (w μ)) := by
          simp [mul_pow, Finset.prod_mul_distrib]
    convert le_trans ( absNorm_le_prod_places g b y hy hy0 ) h_contradiction using 1 <;> first | rfl | ring;
  by_cases hb : Ideal.absNorm b = 0 <;> simp_all +decide;
  · rw [ Ideal.absNorm_eq_zero_iff ] at hb ; aesop;
  · nlinarith [ show 0 < ( Ideal.absNorm b : ℝ ) by positivity ]

/-- Real-analysis balancing identity (strict): the chosen radius factor makes the
separation product strictly less than one. -/
theorem rpow_balance_lt {B0 : ℝ} (hB0 : 1 ≤ B0) {d : ℕ} (hd : 1 ≤ d) :
    ((1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ)))) ^ (2 * d) * B0 < 1 := by
  rw [ mul_pow ];
  rw [ ← Real.rpow_natCast _ ( 2 * d ), ← Real.rpow_natCast _ ( 2 * d ), ← Real.rpow_mul ( by positivity ), mul_comm ] ; ring_nf ; norm_num [ show d ≠ 0 by positivity ];
  norm_cast ; norm_num [ mul_comm, Real.rpow_mul ];
  rw [ ← mul_assoc, inv_mul_cancel₀ ( by positivity ), one_mul ] ; exact pow_lt_one₀ ( by positivity ) ( by norm_num ) ( by positivity )

/-- Real-analysis balancing identity (equality) for the box-count upper bound. -/
theorem rpow_balance_le {B0 : ℝ} (hB0 : 1 ≤ B0) {d : ℕ} (hd : 1 ≤ d) :
    (8 / ((1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))))) ^ (2 * d)
      = (256 : ℝ) ^ d * B0 := by
  ring_nf at *;
  norm_num [ pow_mul', ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity : 0 ≤ B0 ), mul_assoc, mul_comm, mul_left_comm ];
  norm_num [ show d ≠ 0 by linarith ];
  norm_num [ Real.rpow_neg_one ]

/-- Box-count upper bound: with `d ≤ 2^g` places, `256^d · M^(2^g) ≤ (32 √M)^(2·2^g)`. -/
theorem box_count_bound {M : ℝ} (hM : 0 ≤ M) {d g : ℕ} (hd : d ≤ 2 ^ g) :
    (256 : ℝ) ^ d * M ^ 2 ^ g ≤ (32 * Real.sqrt M) ^ (2 * 2 ^ g) := by
  rw [ mul_pow, pow_mul ] ; norm_num [ Real.sq_sqrt hM ] ; ring_nf ;
  rw [ pow_mul', Real.sq_sqrt hM ];
  exact mul_le_mul_of_nonneg_left ( le_trans ( pow_le_pow_left₀ ( by norm_num ) ( by norm_num ) _ ) ( pow_le_pow_right₀ ( by norm_num ) hd ) ) ( by positivity )

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
  classical
  obtain ⟨b, μ, Z, hb, hμ, hZb, hZplace, hprodμ, hZcard⟩ :=
    arithmetic_construction g t hg ht
  -- number of infinite places
  set d : ℕ := Fintype.card (NumberField.InfinitePlace (Kf g)) with hd_def
  have hd_le : d ≤ 2 ^ g := Kf_card_le g
  have hd_pos : 1 ≤ d := Fintype.card_pos
  -- `m t ≥ 1`
  have hM1 : (1 : ℝ) ≤ (m t : ℝ) := by
    have : 1 ≤ m t := Finset.one_le_prod' (fun i _ => (p1_spec i).1.pos)
    exact_mod_cast this
  have hM0 : (0 : ℝ) ≤ (m t : ℝ) := by linarith
  set B0 : ℝ := (m t : ℝ) ^ 2 ^ g with hB0_def
  have hB0 : (1 : ℝ) ≤ B0 := by rw [hB0_def]; exact one_le_pow₀ hM1
  have hB0pos : (0 : ℝ) < B0 := lt_of_lt_of_le one_pos hB0
  set ρ : ℝ := (1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))) with hρ_def
  have hρ0 : 0 < ρ := by rw [hρ_def]; positivity
  have hρ2 : ρ ≤ 2 := by
    rw [hρ_def]
    have hle1 : B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos hB0
      apply div_nonpos_of_nonpos_of_nonneg (by norm_num)
      positivity
    nlinarith [Real.rpow_pos_of_pos hB0pos (-(1 : ℝ) / (2 * (d : ℝ)))]
  -- radius vector and distinguished place
  set r : NumberField.InfinitePlace (Kf g) → ℝ := fun w => Real.sqrt (w μ) with hr_def
  have hr : ∀ w, 0 < r w := by
    intro w; rw [hr_def]
    exact Real.sqrt_pos.mpr (NumberField.InfinitePlace.pos_iff.mpr hμ)
  set i0 : NumberField.InfinitePlace (Kf g) := Classical.arbitrary _ with hi0_def
  -- the Minkowski lattice of `b`
  set Λ : AddSubgroup (NumberField.InfinitePlace (Kf g) → ℂ) :=
    AddSubgroup.map ((mink g).toAddMonoidHom) (b.toAddSubgroup) with hΛ_def
  have hΛ_mem : ∀ x, x ∈ Λ ↔ ∃ y ∈ b, mink g y = x := by
    intro x
    rw [hΛ_def, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  set Z' : Finset (NumberField.InfinitePlace (Kf g) → ℂ) := Z.image (mink g) with hZ'_def
  have hZ'card : Z'.card = Z.card := by
    rw [hZ'_def]; exact Finset.card_image_of_injective Z (mink_injective g)
  -- separation hypothesis
  have hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖ := by
    intro x hx hx0
    rw [hΛ_mem] at hx
    obtain ⟨y, hyb, rfl⟩ := hx
    have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (by simp)
    have hkey : ρ ^ (2 * d) * (m t : ℝ) ^ 2 ^ g < 1 := by
      rw [hρ_def, ← hB0_def]; exact rpow_balance_lt hB0 hd_pos
    obtain ⟨w, hw⟩ := mink_sep_aux g t b μ y hyb hy0 hprodμ ρ hkey
    exact ⟨w, hw⟩
  -- injectivity at the distinguished place
  have hinj : ∀ x ∈ Λ, x i0 = 0 → x = 0 := by
    intro x hx hx0
    rw [hΛ_mem] at hx
    obtain ⟨y, hyb, rfl⟩ := hx
    rw [mink_apply] at hx0
    have hz : algebraMap (𝓞 (Kf g)) (Kf g) y = 0 :=
      i0.embedding.injective (by rw [hx0]; simp)
    have hy0 : y = 0 := RingOfIntegers.coe_injective (by rw [hz]; simp)
    rw [hy0]; simp
  -- `Z'` lies in `Λ` and is coordinate-exact
  have hZΛ : ∀ z ∈ Z', z ∈ Λ := by
    intro z hz
    rw [hZ'_def, Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hΛ_mem]; exact ⟨y, hZb y hy, rfl⟩
  have hZr : ∀ z ∈ Z', ∀ i, ‖z i‖ = r i := by
    intro z hz i
    rw [hZ'_def, Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have h2 := hZplace y hy i
    have hnn : 0 ≤ i (algebraMap (𝓞 (Kf g)) (Kf g) y) := apply_nonneg i _
    rw [norm_mink_apply]
    show i (algebraMap (𝓞 (Kf g)) (Kf g) y) = Real.sqrt (i μ)
    rw [← h2, Real.sqrt_sq hnn]
  -- run the geometric core
  obtain ⟨n, Q, hQcard, hZn, hnbound, hpairs⟩ :=
    geometric_core i0 r hr Λ hρ0 hρ2 hsep hinj Z' hZΛ hZr
  have hZnR : (Z.card : ℝ) ≤ (n : ℝ) := by
    have h := hZn; rw [hZ'card] at h; exact_mod_cast h
  refine ⟨n, Q, hQcard, ?_, ?_, ?_⟩
  · -- first counting estimate
    calc (2 : ℝ) ^ (t * 2 ^ (g - 1))
          ≤ (Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := hZcard
      _ ≤ (n : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := by gcongr
  · -- box-count estimate
    have hbox : (8 / ρ) ^ (2 * d) = (256 : ℝ) ^ d * B0 := by
      rw [hρ_def]; exact rpow_balance_le hB0 hd_pos
    calc (n : ℝ) ≤ (8 / ρ) ^ (2 * d) := hnbound
      _ = (256 : ℝ) ^ d * B0 := hbox
      _ = (256 : ℝ) ^ d * (m t : ℝ) ^ 2 ^ g := by rw [hB0_def]
      _ ≤ (32 * Real.sqrt (m t)) ^ (2 * 2 ^ g) := box_count_bound hM0 hd_le
  · -- unit-distance estimate
    have hpairs' : (Z.card : ℝ) * n ≤ 2 * 64 ^ d * unitDist Q := by
      rw [← hZ'card]; exact hpairs
    calc (2 : ℝ) ^ (t * 2 ^ (g - 1)) * (n : ℝ)
          ≤ ((Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g) * (n : ℝ) := by
            gcongr
      _ = (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * ((Z.card : ℝ) * (n : ℝ)) := by
            ring
      _ ≤ (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ d * unitDist Q) := by
            gcongr
      _ ≤ (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g * unitDist Q) := by
            gcongr
            norm_num
      _ = (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g) * unitDist Q := by
            ring


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
    (hg1 : 1 ≤ g) (_ht5 : 5 ≤ t)
    (hth : (8 : ℝ) * (Real.log h / 2 ^ g + 8) ≤ t)
    (hgC : 40 * C * (Real.log M + 8) ≤ (t : ℝ) * g * Real.log 2 ^ 2)
    -- log M stands in for log (m t) ≤ c₁ t log t; the caller arranges sizes
    (hMn : Real.log n ≤ 2 * 2 ^ g * (Real.log 32 + Real.log M / 2)) :
    n ^ (1 + C / Real.log (Real.log n)) < ν := by
  -- Step 0: Rewrite `hth` as `(H)`.
  have hH : Real.log h ≤ (t : ℝ) * 2 ^ g / 8 - 8 * 2 ^ g := by
    nlinarith [ show ( 0 : ℝ ) < 2 ^ g by positivity, div_mul_cancel₀ ( Real.log h ) ( show ( 2 ^ g : ℝ ) ≠ 0 by positivity ) ];
  -- Step 1: Prove `Real.log n ≥ d`.
  have h_log_n_ge_d : Real.log n ≥ 2 ^ g := by
    -- Applying the logarithm to both sides of `hlower`.
    have h_log_lower : Real.log (2 ^ (t * 2 ^ (g - 1))) ≤ Real.log (n * h * 2 ^ (2 ^ g)) := by
      gcongr;
    rcases g with ( _ | g ) <;> simp_all +decide [ pow_succ, mul_assoc ];
    rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] at h_log_lower ; norm_num at *;
    nlinarith [ Real.log_two_gt_d9, show ( t : ℝ ) ≥ 5 by norm_cast, show ( 2 ^ g : ℝ ) ≥ 1 by exact one_le_pow₀ one_le_two, show ( Real.log h : ℝ ) ≥ 0 by exact Real.log_nonneg hh ];
  -- Step 2: Prove `Real.log (Real.log n) ≥ g * Real.log 2`.
  have h_log_log_n_ge_g_log_2 : Real.log (Real.log n) ≥ g * Real.log 2 := by
    simpa using Real.log_le_log ( by positivity ) h_log_n_ge_d;
  -- Step 3: Prove `Real.log ν ≥ Real.log n + (t * 2 ^ g / 4) * Real.log 2`.
  have h_log_nu_ge : Real.log ν ≥ Real.log n + (t * 2 ^ g / 4) * Real.log 2 := by
    have h_log_nu_ge : Real.log ν ≥ Real.log n + (t * 2 ^ g / 2) * Real.log 2 - Real.log h - 7 * 2 ^ g * Real.log 2 - Real.log 2 := by
      have h_log_nu_ge : Real.log (2 ^ (t * 2 ^ (g - 1)) * n) ≤ Real.log (h * 2 ^ (2 ^ g) * (2 * 64 ^ (2 ^ g)) * ν) := by
        exact Real.log_le_log ( by positivity ) hpairs;
      rw [ Real.log_mul, Real.log_mul, Real.log_mul ] at h_log_nu_ge <;> try positivity;
      rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ) ] at h_log_nu_ge ; norm_num at *;
      rw [ show ( 64 : ℝ ) = 2 ^ 6 by norm_num, Real.log_pow ] at h_log_nu_ge ; rcases g with ( _ | g ) <;> norm_num [ pow_succ' ] at * ; linarith;
    have h_log_2_bounds : 1 / 2 < Real.log 2 ∧ Real.log 2 < 1 := by
      exact ⟨ Real.log_two_gt_d9.trans_le' <| by norm_num, Real.log_two_lt_d9.trans_le <| by norm_num ⟩;
    nlinarith [ show ( t : ℝ ) ≥ 5 by norm_cast, show ( 2 : ℝ ) ^ g ≥ 2 by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) hg1 ), mul_le_mul_of_nonneg_left h_log_2_bounds.1.le ( show ( 0 : ℝ ) ≤ 2 ^ g by positivity ), mul_le_mul_of_nonneg_left h_log_2_bounds.2.le ( show ( 0 : ℝ ) ≤ 2 ^ g by positivity ) ];
  -- Step 5: Prove `(t * 2 ^ g / 4) * Real.log 2 > C * Real.log n / Real.log (Real.log n)`.
  have h_term_gt : (t * 2 ^ g / 4) * Real.log 2 > C * Real.log n / Real.log (Real.log n) := by
    -- Using the bounds from `hMn` and `h_log_log_n_ge_g_log_2`, we get:
    have h_bound : C * Real.log n / Real.log (Real.log n) ≤ C * (2 ^ g * (Real.log M + 10)) / (g * Real.log 2) := by
      gcongr;
      · exact mul_nonneg hC.le ( mul_nonneg ( pow_nonneg zero_le_two _ ) ( add_nonneg ( Real.log_nonneg ( by linarith ) ) ( by norm_num ) ) );
      · rw [ show ( 32 : ℝ ) = 2 ^ 5 by norm_num, Real.log_pow ] at hMn ; norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, pow_pos ( zero_lt_two' ℝ ) g ];
    refine lt_of_le_of_lt h_bound ?_;
    rw [ div_lt_iff₀ ( by positivity ) ];
    nlinarith [ show 0 < ( 2 : ℝ ) ^ g by positivity, show 0 < ( t : ℝ ) * 2 ^ g by positivity, show 0 < ( g : ℝ ) * Real.log 2 by positivity, Real.log_pos one_lt_two, Real.log_le_sub_one_of_pos zero_lt_two, mul_le_mul_of_nonneg_left ( show ( Real.log M : ℝ ) ≥ 0 by exact Real.log_nonneg <| by linarith ) <| show 0 ≤ ( 2 : ℝ ) ^ g by positivity ];
  rw [ Real.rpow_def_of_pos ( by positivity ) ];
  rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ] ; ring_nf at * ; linarith

private theorem exists_params (C : ℝ) (hC : 0 < C) (c₀ c₁ : ℝ)
    (hc₀ : 1 ≤ c₀) (hc₁ : 1 ≤ c₁) (N : ℕ) :
    ∃ g t : ℕ, 1 ≤ g ∧ 5 ≤ t ∧
      8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) ≤ (t : ℝ) ∧
      40 * C * (c₁ * (t : ℝ) * Real.log (t + 2) + 8) ≤
        (t : ℝ) * g * Real.log 2 ^ 2 ∧
      Real.log ((max N 16 : ℕ) : ℝ)
          + c₀ * 2 ^ g * (g + 1) * Real.log (g + 2)
          + 2 ^ g * Real.log 2 ≤ (t : ℝ) * 2 ^ (g - 1) * Real.log 2 := by
  -- We need to find $g$ large enough so that $t = T g$ satisfies the required inequalities.
  have h_second : ∃ G : ℕ, ∀ g ≥ G, 40 * C * (c₁ * (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * (Real.log (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2) + 8)) ≤ (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * g * (Real.log 2) ^ 2 := by
    -- We'll use that $Real.log (t + 2) = O(log(g + 2))$ and $t = O(g^2)$ to simplify the inequality.
    have h_simplify : ∃ G : ℕ, ∀ g ≥ G, Real.log (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2) ≤ 2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) := by
      have h_simplify : ∃ G : ℕ, ∀ g ≥ G, Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2 ≤ (g + 2) ^ 2 * (8 * c₀ + 70) := by
        refine' ⟨ 8, fun g hg => _ ⟩ ; ring_nf;
        nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ 69 + c₀ * g * Real.log ( 2 + g ) * 8 + c₀ * Real.log ( 2 + g ) * 8 by exact add_nonneg ( add_nonneg ( by positivity ) ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ) ( by positivity ) ) ) ( mul_nonneg ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ) ( by positivity ) ) ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 2 : ℝ ) + g ), mul_le_mul_of_nonneg_left ( show ( g : ℝ ) ≥ 8 by norm_cast ) ( show 0 ≤ c₀ by positivity ) ];
      obtain ⟨ G, hG ⟩ := h_simplify; use G; intro g hg; have := Real.log_le_log ( by positivity ) ( hG g hg ) ; rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] at this; norm_num at * ; linarith;
    -- Using the simplified inequality, we can bound the term involving the logarithm.
    obtain ⟨G, hG⟩ := h_simplify;
    have h_bound : ∃ G' : ℕ, ∀ g ≥ G', 40 * C * (c₁ * (2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) + 8)) ≤ g * (Real.log 2) ^ 2 := by
      have h_bound : Filter.Tendsto (fun g : ℕ => (40 * C * (c₁ * (2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) + 8))) / (g : ℝ)) Filter.atTop (nhds 0) := by
        -- We can factor out $g$ in the numerator and denominator and use the fact that $\frac{\log(g+2)}{g}$ tends to $0$ as $g$ tends to infinity.
        have h_log_div_g : Filter.Tendsto (fun g : ℕ => (Real.log (g + 2)) / (g : ℝ)) Filter.atTop (nhds 0) := by
          -- We can use the fact that $\frac{\log(g+2)}{g}$ tends to $0$ as $g$ tends to infinity.
          have h_log_div_g : Filter.Tendsto (fun g : ℕ => Real.log (g : ℝ) / (g : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring_nf );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
          -- We can use the fact that $\frac{\log(g+2)}{g} = \frac{\log(g)}{g} + \frac{\log(1 + 2/g)}{g}$.
          have h_log_div_g_split : Filter.Tendsto (fun g : ℕ => (Real.log (g : ℝ) / (g : ℝ)) + (Real.log (1 + 2 / (g : ℝ)) / (g : ℝ))) Filter.atTop (nhds 0) := by
            simpa [div_eq_mul_inv] using h_log_div_g.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) ) ( by norm_num ) ) tendsto_inv_atTop_nhds_zero_nat );
          refine h_log_div_g_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with g hg using by rw [ show ( g : ℝ ) + 2 = g * ( 1 + 2 / g ) by rw [ mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring );
        convert h_log_div_g.const_mul ( 40 * C * c₁ * 2 ) |> Filter.Tendsto.add <| show Filter.Tendsto ( fun g : ℕ => ( 40 * C * c₁ * ( Real.log ( 8 * c₀ + 70 ) + 8 ) ) / ( g : ℝ ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop using 2 <;> ring;
      have := h_bound.eventually ( gt_mem_nhds <| show 0 < Real.log 2 ^ 2 by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ G', hG' ⟩ ; exact ⟨ G' + 1, fun g hg => by have := hG' g ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩ ;
    obtain ⟨ G', hG' ⟩ := h_bound; use Max.max G G'; intros g hg; specialize hG g ( le_trans ( le_max_left _ _ ) hg ) ; specialize hG' g ( le_trans ( le_max_right _ _ ) hg ) ; norm_num at *;
    nlinarith [ show ( 0 : ℝ ) ≤ ⌈8 * ( c₀ * ( g + 1 ) * Real.log ( g + 2 ) + 8 ) + 5⌉₊ * c₁ * C by positivity ];
  obtain ⟨ G, hG ⟩ := h_second;
  -- Choose $g$ large enough so that the third inequality holds.
  obtain ⟨ G', hG' ⟩ : ∃ G' : ℕ, ∀ g ≥ G', Real.log (max N 16) + c₀ * 2 ^ g * (g + 1) * Real.log (g + 2) + 2 ^ g * Real.log 2 ≤ (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * 2 ^ (g - 1) * Real.log 2 := by
    -- Divide both sides by $2^{g-1}$ to simplify the inequality.
    suffices h_div : ∃ G' : ℕ, ∀ g ≥ G', Real.log (max N 16) / 2 ^ (g - 1) + 2 * c₀ * (g + 1) * Real.log (g + 2) + 2 * Real.log 2 ≤ (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * Real.log 2 by
      obtain ⟨ G', hG' ⟩ := h_div; use G' + 1; intros g hg; specialize hG' g ( by linarith ) ; rcases g <;> norm_num [ pow_succ' ] at *;
      rw [ div_add', div_add', div_le_iff₀ ] at hG' <;> first | positivity | linarith;
    -- We'll use that $Real.log (max N 16) / 2 ^ (g - 1)$ tends to $0$ as $g$ tends to infinity.
    have h_log_div : Filter.Tendsto (fun g : ℕ => Real.log (max N 16) / 2 ^ (g - 1)) Filter.atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat 1 );
    -- We'll use that $2 * c₀ * (g + 1) * Real.log (g + 2) + 2 * Real.log 2$ is bounded above.
    have h_bound : ∃ G' : ℕ, ∀ g ≥ G', 2 * c₀ * (g + 1) * Real.log (g + 2) + 2 * Real.log 2 ≤ (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) * Real.log 2 - 2 * Real.log 2 := by
      use 16; intro g hg; ring_nf ;
      have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ show ( g : ℝ ) ≥ 16 by norm_cast, show ( c₀ : ℝ ) * Real.log ( 2 + g ) ≥ 0 by exact mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ), show ( c₀ : ℝ ) * g * Real.log ( 2 + g ) ≥ 0 by exact mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ] ;
    obtain ⟨ G', hG' ⟩ := h_bound;
    have := h_log_div.eventually ( gt_mem_nhds <| show 0 < 2 * Real.log 2 by positivity );
    obtain ⟨ G'', hG'' ⟩ := Filter.eventually_atTop.mp this;
    exact ⟨ Max.max G' G'', fun g hg => by nlinarith [ hG' g ( le_trans ( le_max_left _ _ ) hg ), hG'' g ( le_trans ( le_max_right _ _ ) hg ), Nat.le_ceil ( 8 * ( c₀ * ( g + 1 ) * Real.log ( g + 2 ) + 8 ) + 5 ), Real.log_pos one_lt_two ] ⟩;
  refine' ⟨ G + G' + 1, ⌈8 * ( c₀ * ( G + G' + 1 + 1 ) * Real.log ( G + G' + 1 + 2 ) + 8 ) + 5⌉₊, _, _, _, _, _ ⟩ <;> norm_num;
  · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; nlinarith [ show 0 ≤ c₀ * ( G + G' + 1 + 1 ) * Real.log ( G + G' + 1 + 2 ) by exact mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ] ) );
  · linarith [ Nat.le_ceil ( 8 * ( c₀ * ( G + G' + 1 + 1 ) * Real.log ( G + G' + 1 + 2 ) + 8 ) + 5 ) ];
  · convert le_trans _ ( hG ( G + G' + 1 ) ( by linarith ) ) using 1 <;> first | rfl | (push_cast ; ring);
    gcongr;
    exact le_trans ( le_mul_of_one_le_right ( by positivity ) hc₁ ) ( le_mul_of_one_le_right ( by positivity ) ( Nat.one_le_cast.mpr ( Nat.ceil_pos.mpr ( by nlinarith [ show 0 ≤ c₀ * G * Real.log ( 3 + G + G' ) by exact mul_nonneg ( mul_nonneg ( by positivity ) ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( by linarith ) ), show 0 ≤ c₀ * G' * Real.log ( 3 + G + G' ) by exact mul_nonneg ( mul_nonneg ( by positivity ) ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( by linarith ) ), show 0 ≤ c₀ * Real.log ( 3 + G + G' ) by exact mul_nonneg ( by positivity ) ( Real.log_nonneg ( by linarith ) ) ] ) ) ) );
  · exact_mod_cast hG' ( G + G' + 1 ) ( by linarith )

/-
**The uniform-constant form of Erdős's unit-distance conjecture is
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
`t → ∞` for the chosen `g(t)`.
-/
set_option maxHeartbeats 1000000 in
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
  intro C hC N;
  -- Apply the `exists_params` theorem to obtain the required `g` and `t`.
  obtain ⟨g, t, hg1, ht5, h2, h3, h4⟩ := exists_params C hC (Classical.choose (log_classNumber_Kf_le)) (Classical.choose (log_m_le)) (Classical.choose_spec (log_classNumber_Kf_le)).left (Classical.choose_spec (log_m_le)).left (max N 16);
  obtain ⟨n, Q, hQcard, hL, hU, hP⟩ := exists_good_pointset g t hg1 (by omega : 1 ≤ t);
  -- Prove that $n \geq \max(N, 16)$.
  have hn_ge_max : (max (max N 16) 16 : ℝ) ≤ n := by
    have h_log : Real.log ((max (max N 16) 16 : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ (2 ^ g)) ≤ Real.log (2 ^ (t * 2 ^ (g - 1))) := by
      rw [ Real.log_mul, Real.log_mul ] <;> norm_num;
      · have := Classical.choose_spec ( log_classNumber_Kf_le ) |>.2 g;
        norm_num at * ; linarith;
      · positivity;
      · exact ne_of_gt ( NumberField.classNumber_pos _ );
      · exact ⟨ by positivity, by exact ne_of_gt <| NumberField.classNumber_pos _ ⟩;
    rw [ Real.log_le_log_iff ] at h_log <;> norm_cast at * <;> norm_num at *;
    · constructor <;> nlinarith [ show 0 < NumberField.classNumber ( Kf g ) * 2 ^ 2 ^ g by exact mul_pos ( Nat.cast_pos.mpr ( NumberField.classNumber_pos _ ) ) ( pow_pos ( by norm_num ) _ ), le_max_left N 16, le_max_right N 16 ];
    · grind +qlia;
  refine' ⟨ n, Q, _, hQcard, _ ⟩;
  · exact_mod_cast le_trans ( le_max_of_le_left ( le_max_left _ _ ) ) hn_ge_max;
  · apply_rules [ key_inequality ];
    any_goals linarith [ le_max_left ( max ( N : ℝ ) 16 ) 16, le_max_right ( max ( N : ℝ ) 16 ) 16 ];
    any_goals exact Nat.one_le_cast.mpr ( NumberField.classNumber_pos _ );
    · contrapose! hP;
      exact lt_of_le_of_lt ( mul_nonpos_of_nonneg_of_nonpos ( by positivity ) hP ) ( by exact mul_pos ( by positivity ) ( Nat.cast_pos.mpr ( by linarith [ show n > 0 from Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) hn_ge_max ) ] ) ) );
    · norm_cast;
      exact le_trans ( by decide ) ( m_ge t |> le_trans ( pow_le_pow_right₀ ( by decide ) ht5 ) );
    · have := Classical.choose_spec ( log_classNumber_Kf_le );
      nlinarith [ this.2 g, show ( 0 : ℝ ) < 2 ^ g by positivity, div_mul_cancel₀ ( Real.log ( NumberField.classNumber ( Kf g ) : ℝ ) ) ( show ( 2 : ℝ ) ^ g ≠ 0 by positivity ) ];
    · refine' le_trans _ h3;
      gcongr;
      exact Classical.choose_spec ( log_m_le ) |>.2 t;
    · refine' le_trans ( Real.log_le_log ( by linarith [ le_max_left ( max ( N : ℝ ) 16 ) 16, le_max_right ( max ( N : ℝ ) 16 ) 16 ] ) hU ) _;
      rw [ Real.log_pow, Real.log_mul, Real.log_sqrt ] <;> ring_nf <;> norm_num;
      · linarith;
      · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| p1_spec i |>.1

end Assembly

end Erdos
