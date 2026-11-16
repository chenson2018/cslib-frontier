/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Tiling.Frame
public import CslibFrontier.Computability.WangTile.EveryTileOccurs
public import CslibFrontier.Foundations.RelationAlgebra.Game

/-!
# Tilings give a winning strategy

Theorem 4 of [HirschHodkinson2001]: if every tile of a list is at the origin of a tiling by the
list, and the first tile matches itself, then ∃ has a winning strategy in the game of `RA(τ)`.

**The proof is not written yet**: the statement below is a `sorry`, being proved separately.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.RelationAlgebra

open WangTile

/-- **Not yet proved; the proof is in progress and this statement is a `sorry`.**

Theorem 4 of [HirschHodkinson2001]: if every position of `L` is at the origin of a tiling by
positions of `L`, and the tile at position `0` matches itself horizontally and vertically, then ∃
has a winning strategy in the game on `tilingFrame L`. The source asks that the tile `T₀` have one
colour on its four edges, used by no other tile; the strategy labels with `T₀` the tile edges
that it does not place in a tiling, for which the two equations suffice. -/
theorem hasWinningStrategy_tilingFrame {L : List WangTile} (hL : 0 < L.length)
    (hrow : L[0].right = L[0].left) (hcol : L[0].top = L[0].bottom) (h : EveryIndexOccurs L) :
    (tilingFrame L).HasWinningStrategy :=
  sorry

end Cslib.RelationAlgebra
