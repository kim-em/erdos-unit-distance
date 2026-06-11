# Erdős unit-distance formalization — COMPLETE (2026-06-11)

`Erdos.erdos_unit_distance_uniform_constant_false` is fully proved.

    'Erdos.erdos_unit_distance_uniform_constant_false' depends on axioms:
    [propext, Classical.choice, Quot.sound]

- Mathlib-only part: mathlib4 branch `kim/erdos-unit-distance`,
  `ErdosUnitDistance/Framework.lean` (two sorries remain there for
  `q3_poly_bound`/`p1_poly_bound` only because Mathlib cannot depend on
  PrimeNumberTheoremAnd).
- End-to-end artifact: `pnt-bounds/` in this repo
  (`PntBounds/Framework.lean` + `PolyBounds.lean` + `CountGlue.lean`),
  building against PrimeNumberTheoremAnd's Mathlib pin. Verify:

      cd pnt-bounds && lake build PntBounds
      lake env lean <file with: import PntBounds.Framework
                     #print axioms Erdos.erdos_unit_distance_uniform_constant_false>
