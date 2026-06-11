# Integral points on norm-one tori and the Erdős unit-distance exponent

*Transcription of L. Alpöge's one-page proof (2026). Footnotes are inlined
at their reference points in [brackets].*

## Abstract

For finite `P ⊂ ℝ²` write `ν(P)` for the number of unit-distance pairs in
`P` and `ν(n) := max_{#|P|=n} ν(P)`. We disprove the uniform-constant form
`ν(n) ≤ n^{1+O(1/log log n)}` of Erdős's unit-distance conjecture: for
every `C > 0` there are arbitrarily large `n` with `ν(n) > n^{1+C/log log n}`.
The sets are projections, to one complex place, of polydisc boxes in ideals
of multiquadratic CM fields of growing degree; the repeated unit distance is
a single fibre of the relative norm to the maximal totally real subfield,
which we show contains exponentially many elements all of one archimedean
modulus.

## The construction

Let `t → ∞` be the only parameter, and choose any function `B = B(t) → ∞`
with `B = o(t/(log t)²)`. Let `g := ⌊B log t⌋`, so that `g log g = o(t)`.
Let `q_j` and `p_i` be the `j`-th prime `≡ 3 (mod 4)` and the `i`-th prime
`≡ 1 (mod 4)` respectively, and write `m := ∏_{i ≤ t} p_i`. Let

```
K := ℚ(√−4, √−q₁, …, √−q_{g−1}),
```

a multiquadratic CM field of degree `2^g`; write `τ` for complex
conjugation and `K⁺ := K^τ` for its maximal totally real subfield. Then
`log |d_K| ≪ 2^g g log g` and hence `log h_K ≪ 2^g g log g = o(t · 2^g)`.

[Footnote 1: The order `ℤ[√−4, √−q₁, …, √−q_{g−1}] ⊂ 𝒪_K` has discriminant
`O(1)^{2^g} · (∏_j q_j)^{2^{g−1}}`, and `q_j ≪ j log j`; the Minkowski
bound then gives `h_K ≪ √|d_K| (log |d_K|)^{2^g}`.]

Throughout, `σ` ranges over the embeddings `K ↪ ℂ`, `σ₁` is a fixed one,
and a subscript `+` means totally positive.

There are `≫ 2^{Ω(t·2^g)}` integral ideals `𝔄` of `𝒪_K` with
`𝔄 𝔄̄ = m 𝒪_K`.

[Footnote 2: Each `p_i` has Frobenius `≠ τ`, so `τ` acts freely on the
primes above `p_i` in `≥ 2^{g−2}` orbits; an `𝔄` is a choice of one prime
per orbit for each `i`.]

Pigeonhole these into one ideal class and let `𝔟` be an integral ideal in
the inverse class. Then there is a totally positive `μ ∈ 𝒪_{K⁺}` with
`N_{K⁺} μ / N𝔟 = m^{2^{g−1}}` for which the fibre
`Z := {z ∈ 𝔟 : z z̄ = μ}` has

```
#|Z| ≫ 2^{Ω(t·2^g)} · O(1)^{−2^g} / h_K.
```

[Footnote 3: Each `𝔄𝔟` is principal with generator `y_𝔄 ∈ 𝔟`, and the
`y_𝔄 ȳ_𝔄 ∈ 𝒪_{K⁺,+}` all generate `(m) 𝔟 𝔟̄` hence differ by totally
positive units of `𝒪_{K⁺}`; a second pigeonhole over the `≤ 2^{2^{g−1}}`
cosets of `(𝒪_{K⁺}^×)²`, followed by `z_𝔄 := y_𝔄 ε_𝔄^{−1}` with
`ε_𝔄 ∈ 𝒪_{K⁺}^×`, gives the common `μ`.]

Let `𝔅 := {x : max_σ |σ(x)| ≤ 2√σ(μ)}` be the polydisc box, let
`P := σ₁(𝔟 ∩ 𝔅)/√σ₁(μ) ⊂ ℂ`, and write `n := #|P| = #|𝔟 ∩ 𝔅|`.

## Proof

Each `z ∈ Z` has `|σ(z)|² = σ(μ)` at every place, so translation by `z`
maps `𝔟 ∩ ½𝔅` into `𝔟 ∩ 𝔅` at distance exactly 1, giving
`ν(P) ≥ #|Z| · n · O(1)^{−2^g}`.

[Footnote 4: Distinct `(x, z)` give distinct ordered pairs in `P × P`
since `σ₁` is injective, so `ν(P) ≥ ½ #|Z| · #|𝔟 ∩ ½𝔅|`; and
symmetric-convex doubling gives `n ≤ O(1)^{2^g} #|𝔟 ∩ ½𝔅|`: choose
`X ⊆ 𝔟 ∩ 𝔅` maximal with the `x + ¼𝔅`, `x ∈ X`, pairwise disjoint, so
`#|X| ≤ O(1)^{2^g}` by volume; by maximality every `y ∈ 𝔟 ∩ 𝔅` lies in
some `x + ½𝔅`, and `#|𝔟 ∩ (x + ½𝔅)| = #|𝔟 ∩ ½𝔅|`.]

Thus

```
log(ν(P)/n) ≫ t·2^g,    log n ≪ 2^g · t log t,    log log n ≍ g ≍ B log t,
```

the middle since `log m ≍ t log t`, and the right from `n ≥ #|Z|`.

[Footnote 5: For every nonzero `x ∈ 𝔟`,
`∏_σ |σ(x)| = |N_{K/ℚ} x| ≥ N𝔟` forces
`max_σ |σ(x)|/√σ(μ) ≥ m^{−1/2}`; hence distinct `x, y ∈ 𝔟 ∩ 𝔅` have
`x − y ∉ m^{−1/2}𝔅`, so the `x + ½m^{−1/2}𝔅` are pairwise disjoint inside
`O(1)𝔅` and `n ≤ O(1)^{2^g} m^{2^{g−1}}`.]

The `O(1)^{2^g}` factors cost `O(2^g) = o(t·2^g)` on the log scale, so

```
ν(P) ≫ n^{1+c(t)/log log n},    c(t) ≍ g/log t ≍ B(t) → ∞,
```

with `n → ∞`, disproving `ν(n) ≤ n^{1+O(1/log log n)}`. ∎

## Remarks for the formalizer

* The author's commentary: "amusingly this one found a counterexample
  without any serious number theoretic input, i.e. no class field towers,
  just intro number theory stuff. you just adjoin square roots of the first
  many negative prime discriminants (Erdős's ℚ(i) construction being the
  first case) and consider an exponentially longer product of primes
  congruent to 1 mod 4, pigeonhole to get a lot of ideal divisors in the
  same ideal class, and then it's the same rescaling construction as Erdős.
  This doesn't gain a power, 'just' disproves the conjecture."
* The needed ingredients are: splitting of primes `≡ 1 (mod 4)` in
  multiquadratic fields (quadratic reciprocity-level facts), finiteness of
  the class group with the Minkowski-bound estimate
  `h_K ≪ √|d_K| (log |d_K|)^{2^g}`, Dirichlet's unit theorem only through
  the bound `[𝒪_{K⁺}^× : (𝒪_{K⁺}^×)²] ≤ 2^{2^{g−1}}` (rank ≤ `2^{g−1} − 1`
  plus torsion `±1`), two pigeonhole arguments, the prime number theorem in
  arithmetic progressions only through Chebyshev-type bounds
  (`p_i ≍ i log i`, `q_j ≍ j log j` suffice, and even cruder bounds work),
  and elementary lattice-point counting (volume packing) in
  `K ⊗ ℝ ≅ ℂ^{2^{g−1}}`.
* All asymptotic notation must be made explicit with concrete constants, or
  handled via `Filter.atTop` / `Asymptotics` machinery.
* One concrete instantiation that suffices: `B(t) = log t` (so
  `g = ⌊(log t)²⌋`), since then `g log g ≍ (log t)² log log t = o(t)`.
  For a given `C`, take `t` large enough; every quantity is explicit.
