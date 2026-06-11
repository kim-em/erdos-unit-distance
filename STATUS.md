# Erdős unit-distance formalization — session state (2026-06-11)

Canonical: mathlib4 branch `kim/erdos-unit-distance`, ErdosUnitDistance/Framework.lean
(verify: `lake env lean <abs path>` from /home/kim/worktrees/mathlib4/mathlib4-pr-38292).

## Open sorries (4 warnings in branch)
- q3_poly_bound / p1_poly_bound — PROVED in pnt-bounds/ (PNT-in-AP dependency;
  cannot enter mathlib). Final artifact unification pending.
- exists_ideal_family — Aristotle c0baf58a-93d6-4194-b46e-9beed6ca71b7 (running ~6h).
  Fallback pins if it fails: p1 unramified in Kf; inertia degree ≤ 2 (use proven
  Kf_aut_involutive); conj 𝔭 ≠ 𝔭 via residue field (p ≡ 1 mod 4, i ↦ −i ⟹ 𝔭 ∣ 2i);
  orbit count 2^(g−1); choice family + unique factorization.
- arithmetic_construction — Aristotle 4d397357-4d3b-42da-ad0c-2fd3e5a29c0a (running ~6h).
  Consumes exists_ideal_family + units_sq_index_le (proven) + two pigeonholes.

## Tools
- integrate.py: splice Aristotle solutions back (JOBS dict).
- gen_submissions.py: per-sorry project generator (/tmp/aristotle-jobs).
- drain-queue.sh, poll.py, aristotle-projects.tsv (id↔name map).
- Monitor ba9091adx watches second-wave ids (lines 14+ of tsv); first-batch ids
  must be checked manually (aristotle list --limit 45).

## Post-completion checklist
1. Integrate last two lemmas; port-fix; verify; push.
2. Full-file axiom audit: #print axioms Erdos.erdos_unit_distance_uniform_constant_false
   (expect sorryAx only via the two poly_bounds).
3. Unification: copy Framework into pnt-bounds (or a standalone repo with both deps),
   import PolyBounds proofs, produce sorry-free end-to-end theorem; axiom audit again.
4. README update; announce.
