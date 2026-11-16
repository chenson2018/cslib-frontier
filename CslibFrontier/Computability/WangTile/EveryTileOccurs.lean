/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic

/-!
# The tiling problem in which every tile must occur

The tiling problem that Hirsch and Hodkinson reduce to representability of finite relation
algebras asks of a finite set of Wang tiles whether each of its tiles lies at the origin of some
tiling of the plane by the set [HirschHodkinson2001], Section 3. This is not the domino problem:
a set that tiles the plane may contain a tile that no tiling uses.

## Main definitions

* `Cslib.WangTile.EveryTileOccurs`: every tile of a list is at the origin of a tiling by the list.
* `Cslib.WangTile.EveryIndexOccurs`: the same for tilings by positions of the list, the form in
  which the source states the problem.
* `Cslib.WangTile.freshTile`: a tile with one colour on its four edges, used by no tile of the
  list; the source's special tile `T₀`.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

public section

namespace Cslib.WangTile

/-- Every tile of `τ` is at the origin of some tiling of the plane by `τ`. -/
@[expose] def EveryTileOccurs (τ : List WangTile) : Prop :=
  ∀ t ∈ τ, TilesAtOrigin ⟨τ, t⟩

/-- Every position of the list `L` is at the origin of some tiling of the plane by positions of
`L`: there are maps `F : ℤ → ℤ → Fin L.length`, one with `F 0 0 = i` for each position `i`, in
which the tiles at horizontally and vertically adjacent cells match. This is the tiling problem
of [HirschHodkinson2001], Section 3, where the tiles are `T₀, …, Tₖ₋₁` and a tiling is a map to
`{0, …, k - 1}`. -/
@[expose] def EveryIndexOccurs (L : List WangTile) : Prop :=
  ∀ i : Fin L.length, ∃ F : ℤ → ℤ → Fin L.length, F 0 0 = i ∧ ∀ x y,
    L[F x y].right = L[F (x + 1) y].left ∧ L[F x y].top = L[F x (y + 1)].bottom

/-- A tile whose four edges carry one colour, which is larger than every colour of a tile of
`τ`. -/
@[expose] def freshTile (τ : List WangTile) : WangTile :=
  let c := τ.foldr (fun t c => max (max (max t.top t.bottom) (max t.left t.right) + 1) c) 0
  ⟨c, c, c, c⟩

end Cslib.WangTile
