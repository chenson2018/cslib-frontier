/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Tiling.Reduction
import CslibFrontier.Computability.WangTile.TilesPlaneOfEveryTileOccurs

/-!
# Representability of finite relation algebras: the step from the domino problem

Hirsch and Hodkinson prove that no algorithm decides whether a finite relation algebra is
representable [HirschHodkinson2001], Theorem 8, from the undecidability of the domino problem.
**This file does not prove that theorem.** It proves the implication between the two: if the
domino problem is undecidable, then so is the representation problem for finite relation algebras
given by tables. The undecidability of the domino problem is not proved in this library.

A decision procedure for the representation problem decides the tiling problem in which every
tile must occur, through the reduction `everyTileOccurs_manyOneReducible_isRepresentable`, and
that decides the domino problem by a search over sublists
(`Cslib.WangTile.computablePred_tilesPlane_of_computablePred_everyTileOccurs`).

## Main results

* `Cslib.RelationAlgebra.not_computablePred_isRepresentable_of_not_computablePred_tilesPlane`:
  the conditional step.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.RelationAlgebra

open WangTile

/-- A step towards Theorem 8 of [HirschHodkinson2001], conditional on the undecidability of the
domino problem, and not that theorem: **if** no algorithm decides whether a list of Wang tiles
tiles the plane, then none decides whether a table presents an atom structure whose complex
algebra is representable. The hypothesis is Berger's theorem, which the source cites and this
library does not prove; it is milestone 4 of cslib-frontier issue #5920. -/
theorem not_computablePred_isRepresentable_of_not_computablePred_tilesPlane
    (h : ¬ComputablePred TilesPlane) : ¬ComputablePred AtomTable.IsRepresentable := fun hrep =>
  h <| computablePred_tilesPlane_of_computablePred_everyTileOccurs <|
    ComputablePred.computable_of_manyOneReducible everyTileOccurs_manyOneReducible_isRepresentable
      hrep

end Cslib.RelationAlgebra
