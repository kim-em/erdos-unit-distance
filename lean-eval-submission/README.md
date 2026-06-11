# lean-eval submission bundle (prepared, not yet submitted)

Model name for the leaderboard: **Fable + Aristotle**.

## Status and two blockers needing a decision

1. **Statement mismatch.**  The existing lean-eval problem
   `erdos_unit_distance_conjecture_false` asserts a fixed power gain
   (`∃ δ > 0` with `ν(n) ≥ n^(1+δ)`), which Alpöge's one-page proof —
   and hence our formalization — deliberately does *not* give.  Our
   theorem is the literal negation of Erdős's conjecture (every `C`,
   gain `n^(C/log log n)`).  This bundle therefore contains a **proposed
   companion problem** (`erdos_unit_distance_uniform_constant_false.toml`
   + `UnitDistanceUniformConstantFalse.lean`, in lean-eval's manifest and
   module format, statement matching our proved theorem modulo the
   `unitDist` definition, which is byte-identical to lean-eval's), with
   the formalization as its solution.  The original problem remains open.

2. **Vendoring requirement.**  lean-eval rules require helper code not in
   Mathlib to live inside the submission workspace.  Our proof's only
   external input is `chebyshev_asymptotic_pnt` from
   PrimeNumberTheoremAnd (sorry-free there).  A compliant
   `Submission.lean` therefore needs the relevant PNT development
   vendored under `Submission/` and the whole workspace rebuilt against
   lean-eval's toolchain (v4.30.0-rc2).  This is mechanical but large,
   and not yet done.

## Contents

- `erdos_unit_distance_uniform_constant_false.toml` — problem manifest
  (proposed; `submitter = "Kim Morrison"`).
- `UnitDistanceUniformConstantFalse.lean` — the `@[eval_problem]` module.
- The solution itself is `../ErdosUnitDistance/Framework.lean` (Mathlib
  master; two sorries standing in for the PNT input) together with
  `../pnt-bounds/` (end-to-end, zero sorries, axioms
  `{propext, Classical.choice, Quot.sound}`).
