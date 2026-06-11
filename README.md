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

- `pnt-bounds/` — the **end-to-end artifact**.  A Lake project depending
  on Mathlib and
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (for a Chebyshev-type bound on primes in progressions mod 4, the only
  analytic input).
  - `PntBounds/Framework.lean` — the full proof (≈3,400 lines).
  - `PntBounds/PolyBounds.lean`, `PntBounds/CountGlue.lean` — the
    `j`-th-prime bounds from `chebyshev_asymptotic_pnt`.

  Verify with:
  ```
  cd pnt-bounds && lake build PntBounds
  ```
  and `#print axioms Erdos.erdos_unit_distance_uniform_constant_false`
  after `import PntBounds.Framework`.

- `ErdosUnitDistance/Framework.lean` — the **main development**, a Lake
  project at the repository root requiring **Mathlib master**.  Identical
  to the end-to-end artifact except that the two prime-growth lemmas
  remain `sorry`ed here (they need PrimeNumberTheoremAnd, whose Mathlib
  pin lags master).  Verify with:
  ```
  lake exe cache get && lake build
  ```

- `informal-proof.md` — a faithful transcription of the informal proof.
- `scratch/` — intermediate developments (square-class descent, the
  ideal-family decomposition, the Rankin count experiments).
- `gen_submissions.py`, `integrate.py`, `drain-queue.sh`, `poll.py` —
  the orchestration tooling used to fan the 27 intermediate lemmas out to
  automated provers and to splice the results back.
- `formalization.yaml` — provenance and resource-usage metadata.

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
