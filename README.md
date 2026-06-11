# The uniform-constant Erdős unit-distance conjecture is false — formalized

A complete, machine-checked Lean 4 formalization of L. Alpöge's one-page
disproof of the uniform-constant form of Erdős's unit-distance conjecture:

> **Theorem** (`Erdos.erdos_unit_distance_uniform_constant_false`).
> For every `C > 0` and every `N` there exist `n ≥ N` and an `n`-point set
> `P ⊆ ℝ²` with more than `n^(1 + C / log log n)` unit-distance pairs.

This is the literal negation of Erdős's 1946 conjecture
`ν(n) ≤ n^(1 + C/log log n)`.  The final axiom audit:

```
'Erdos.erdos_unit_distance_uniform_constant_false' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no extra axioms.  (Note this is *weaker* than the
[lean-eval problem `erdos_unit_distance_conjecture_false`](https://lean-lang.org/eval/problems/erdos_unit_distance_conjecture_false/),
which asks for a fixed power gain `ν(n) ≥ n^(1+δ)` — the OpenAI 2026
construction via class field towers.  Alpöge's one-pager deliberately
trades the power gain for elementary inputs, and that is what is
formalized here.)

## Layout

A single Lake project requiring Mathlib (via the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
pin, currently Lean v4.30.0) and PrimeNumberTheoremAnd itself, whose
`chebyshev_asymptotic_pnt` (sorry-free) is the only analytic input.

The library is organised by subject:

| module | contents |
|---|---|
| `Counting` | unit-distance pair counts; transport `ℂ ≃ ℝ²` |
| `GeometricCore` | grid-pigeonhole packing/doubling in polydiscs; the translation argument |
| `PrimesMod4` | the `j`-th primes `≡ 1, 3 (mod 4)`; polynomial growth from PNT-in-AP; the modulus `m t` |
| `MultiquadraticField` | `K_g = ℚ(i, √q₀, …, √q_{g-1})`: degree `2^(g+1)` by square-class descent; CM structure |
| `ClassNumber` | ideal counting by injective encoding; `h ≤ \|d\|·4^deg`; unit square classes |
| `Discriminant` | diagonal trace form on subset products; `log h_{K_g} = O(2^g·g log g)` |
| `IdealFamily` | unramifiedness, inertia `≤ 2`, conjugation freeness; the `2^(t·2^(g-1))` ideals over `m` |
| `NormFibre` | the two pigeonholes; the fibre `Z = {z ∈ 𝔟 : z·z∗ = μ}` |
| `PointCount` | Minkowski embedding, separation, the planar point set |
| `Main` | the counting assembly and the theorem |

Verify with:

```
lake exe cache get && lake build
```

and then

```lean
import ErdosUnitDistance
#print axioms Erdos.erdos_unit_distance_uniform_constant_false
-- [propext, Classical.choice, Quot.sound]
```

- `informal-proof.md` — a faithful transcription of the informal proof.
- `formalization.yaml` — provenance and resource-usage metadata.

## Independent verification

[kim-em/erdos-unit-distance-comparator](https://github.com/kim-em/erdos-unit-distance-comparator)
checks this library with
[leanprover/comparator](https://github.com/leanprover/comparator): a
Mathlib-only `Challenge.lean` states the theorem, and comparator
certifies — without trusting any proof code here — that the library
proves exactly that statement from the standard axioms, replaying the
proof through the Lean kernel.

## Proof structure

1. **Geometric core** — grid-pigeonhole packing and doubling bounds for
   lattice points in polydiscs of `ℂ^d` (no measure theory), and the
   translation argument producing unit distances after projection to one
   complex coordinate.
2. **Arithmetic construction** — the multiquadratic CM field
   `K = ℚ(i, √q₀, …, √q_{g-1})` (`q_j` the `j`-th prime `≡ 3 mod 4`) of
   degree `2^(g+1)`; for `m` the product of the first `t` primes
   `≡ 1 mod 4`, at least `2^(t·2^(g-1))` ideals `𝔄` with `𝔄𝔄∗ = (m)`
   (unramifiedness, inertia degree `≤ 2` via the exponent-2 Galois group,
   conjugation acting freely on primes, and a transversal count);
   class-group and unit-square-class pigeonholes then produce a norm
   fibre `Z = {z ∈ 𝔟 : z z̄ = μ}` of exponential size, all of one
   archimedean modulus.
3. **Assembly** — explicit-constant bookkeeping: `log(ν/n) ≫ t·2^g`,
   `log n ≪ 2^g·t log t`, `log log n ≍ g`; choosing `g ≈ C log t` and `t`
   large refutes the bound for the given `C`.

## Provenance

Formalized 2026-06-11 (one working day) by an orchestrated ensemble —
Claude (Anthropic), Aristotle (Harmonic), and Codex (OpenAI) — directed
from a single Claude Code session.  See `formalization.yaml` for details
and resource usage.
