/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Realization

/-!
# The concrete Robinson seed-removal map

The finite map first extends a seeded quadrant palette to a pointed-plane palette, then pairs
that palette with the corrected Robinson scaffold. Its computation is primitive recursive.
The correctness argument here is an internal assembly step conditional on the forward forcing
property; no unconditional seed-removal or domino theorem is asserted in this module yet.

## Main definitions

* `forgetSeed`: the concrete seeded-to-unseeded palette transformation.

## References

After [Robinson1971], §7, pp. 201–205 and [JeandelVanier2020], §3.3, Theorem 10, manuscript p. 29.
The assembly follows lean-wang revision `64268a3aaaef3eac65559352ef94f62ab9c00482`,
`Robinson/Scaffold/Routed/PointedPlane.lean:85–100`.
-/

public section

namespace Cslib.WangTile.Robinson

/-- Extend a quadrant seed to a pointed plane and combine it with the concrete scaffold. -/
def forgetSeed (I : SeededInstance) : List WangTile :=
  combine scaffold (pointedExtension I)

/-- The concrete seed-removal map is primitive recursive for the tile-list instance codes. -/
theorem primrec_forgetSeed : Primrec forgetSeed :=
  (primrec_combine scaffold).comp primrec_pointedExtension

/-- Internal assembly step, not unconditional seed removal: the backward construction is
proved here, while the supplied forward forcing property remains to be discharged. -/
private theorem tilesPlane_forgetSeed_iff_of_forces
    (forces : Forces scaffold) (I : SeededInstance) :
    TilesPlane (forgetSeed I) ↔ TilesQuadrant I :=
  tilesPlane_combine_pointedExtension_iff_of_forces_of_realizes forces scaffold_realizes I

end Cslib.WangTile.Robinson
