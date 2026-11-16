/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
import Mathlib.Tactic.FinCases

/-!
# Corrected Robinson tiles and their substitution

The corrected Ollinger–Robinson alphabet has 104 component triples. Its thin, thick and black
layers contribute edge-colour digits in bases 4, 4 and 2. The substitution replaces each tile
by a matching square of four tiles, preserves matching across adjacent squares, and reflects
matching of their boundaries. Thin-layer matching determines the parity phases of a tiling.

## Main definitions

* `Components` and `components`: the three layers of each of the 104 tiles.
* `tile` and `tileSet`: the edge-colour interpretation and finite palette.
* `childBlock`: the corrected Figure 16 substitution, with west/east coordinate first.

## Main results

* `child_horizontal`, `child_vertical`: each substitution square matches internally.
* `horizontal_iff_children`, `vertical_iff_children`: boundary matching is preserved and reflected.
* `thin_east`, `thin_north`: the forced neighboring thin-layer phases.

## References

The construction follows [JeandelVanier2020], §3.2, Figures 13–16 and the matching step of
Proposition 8 (pp. 23–26 of the authors' manuscript), using the corrected 104-tile variant.

Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3), revision
`64268a3`, the `Robinson.Closed104.Data`, `Figure16`, `Tiles` and `Recognizability` modules.
Component names and alphabet order
are those of its corrected Figure 13; child indices implement its Figure 16 substitution.
-/

public section
namespace Cslib.WangTile.Robinson

/-- The four thin-layer phases in the corrected Figure 13 alphabet. -/
inductive Thin where
  | a | b | c | d
  deriving DecidableEq

/-- The twenty thick-layer components in the corrected Figure 13 alphabet. -/
inductive Thick where
  | a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p | q | r | s | t
  deriving DecidableEq

/-- The five black-layer components in the corrected Figure 13 alphabet. -/
inductive Black where
  | a | b | c | d | e
  deriving DecidableEq

/-- A corrected Robinson tile's three superimposed component layers. -/
structure Components where
  /-- The thin-layer phase. -/
  thin : Thin
  /-- The thick-layer component. -/
  thick : Thick
  /-- The black-layer component. -/
  black : Black
  deriving DecidableEq

/-- Index in the corrected 104-tile alphabet, in Figure 13 order. -/
abbrev Index := Fin 104

/-- The component triple of a tile in the corrected Figure 13 alphabet. -/
@[expose] def components (index : Index) : Components :=
  match index.val with
  | 0 => ⟨.a, .b, .a⟩
  | 1 => ⟨.a, .c, .a⟩
  | 2 => ⟨.a, .a, .a⟩
  | 3 => ⟨.a, .d, .a⟩
  | 4 => ⟨.b, .b, .a⟩
  | 5 => ⟨.b, .c, .a⟩
  | 6 => ⟨.b, .a, .a⟩
  | 7 => ⟨.b, .d, .a⟩
  | 8 => ⟨.c, .m, .b⟩
  | 9 => ⟨.c, .m, .c⟩
  | 10 => ⟨.c, .i, .b⟩
  | 11 => ⟨.c, .i, .c⟩
  | 12 => ⟨.c, .t, .c⟩
  | 13 => ⟨.c, .e, .c⟩
  | 14 => ⟨.c, .j, .c⟩
  | 15 => ⟨.c, .h, .c⟩
  | 16 => ⟨.c, .l, .b⟩
  | 17 => ⟨.c, .f, .b⟩
  | 18 => ⟨.c, .r, .b⟩
  | 19 => ⟨.c, .g, .b⟩
  | 20 => ⟨.c, .o, .b⟩
  | 21 => ⟨.c, .o, .c⟩
  | 22 => ⟨.c, .k, .b⟩
  | 23 => ⟨.c, .k, .c⟩
  | 24 => ⟨.c, .n, .b⟩
  | 25 => ⟨.c, .n, .c⟩
  | 26 => ⟨.c, .q, .b⟩
  | 27 => ⟨.c, .q, .c⟩
  | 28 => ⟨.c, .p, .b⟩
  | 29 => ⟨.c, .p, .c⟩
  | 30 => ⟨.c, .s, .b⟩
  | 31 => ⟨.c, .s, .c⟩
  | 32 => ⟨.a, .m, .b⟩
  | 33 => ⟨.a, .m, .c⟩
  | 34 => ⟨.a, .i, .b⟩
  | 35 => ⟨.a, .i, .c⟩
  | 36 => ⟨.a, .t, .c⟩
  | 37 => ⟨.a, .e, .c⟩
  | 38 => ⟨.a, .j, .c⟩
  | 39 => ⟨.a, .h, .c⟩
  | 40 => ⟨.a, .l, .b⟩
  | 41 => ⟨.a, .f, .b⟩
  | 42 => ⟨.a, .r, .b⟩
  | 43 => ⟨.a, .g, .b⟩
  | 44 => ⟨.a, .o, .b⟩
  | 45 => ⟨.a, .o, .c⟩
  | 46 => ⟨.a, .k, .b⟩
  | 47 => ⟨.a, .k, .c⟩
  | 48 => ⟨.a, .n, .b⟩
  | 49 => ⟨.a, .n, .c⟩
  | 50 => ⟨.a, .q, .b⟩
  | 51 => ⟨.a, .q, .c⟩
  | 52 => ⟨.a, .p, .b⟩
  | 53 => ⟨.a, .p, .c⟩
  | 54 => ⟨.a, .s, .b⟩
  | 55 => ⟨.a, .s, .c⟩
  | 56 => ⟨.d, .t, .d⟩
  | 57 => ⟨.d, .t, .e⟩
  | 58 => ⟨.d, .e, .d⟩
  | 59 => ⟨.d, .j, .d⟩
  | 60 => ⟨.d, .j, .e⟩
  | 61 => ⟨.d, .h, .e⟩
  | 62 => ⟨.d, .l, .d⟩
  | 63 => ⟨.d, .l, .e⟩
  | 64 => ⟨.d, .f, .d⟩
  | 65 => ⟨.d, .r, .d⟩
  | 66 => ⟨.d, .r, .e⟩
  | 67 => ⟨.d, .g, .e⟩
  | 68 => ⟨.d, .o, .d⟩
  | 69 => ⟨.d, .o, .e⟩
  | 70 => ⟨.d, .k, .d⟩
  | 71 => ⟨.d, .n, .d⟩
  | 72 => ⟨.d, .n, .e⟩
  | 73 => ⟨.d, .q, .e⟩
  | 74 => ⟨.d, .p, .d⟩
  | 75 => ⟨.d, .p, .e⟩
  | 76 => ⟨.d, .s, .d⟩
  | 77 => ⟨.d, .m, .d⟩
  | 78 => ⟨.d, .m, .e⟩
  | 79 => ⟨.d, .i, .e⟩
  | 80 => ⟨.a, .t, .d⟩
  | 81 => ⟨.a, .t, .e⟩
  | 82 => ⟨.a, .e, .d⟩
  | 83 => ⟨.a, .j, .d⟩
  | 84 => ⟨.a, .j, .e⟩
  | 85 => ⟨.a, .h, .e⟩
  | 86 => ⟨.a, .l, .d⟩
  | 87 => ⟨.a, .l, .e⟩
  | 88 => ⟨.a, .f, .d⟩
  | 89 => ⟨.a, .r, .d⟩
  | 90 => ⟨.a, .r, .e⟩
  | 91 => ⟨.a, .g, .e⟩
  | 92 => ⟨.a, .o, .d⟩
  | 93 => ⟨.a, .o, .e⟩
  | 94 => ⟨.a, .k, .d⟩
  | 95 => ⟨.a, .n, .d⟩
  | 96 => ⟨.a, .n, .e⟩
  | 97 => ⟨.a, .q, .e⟩
  | 98 => ⟨.a, .p, .d⟩
  | 99 => ⟨.a, .p, .e⟩
  | 100 => ⟨.a, .s, .d⟩
  | 101 => ⟨.a, .m, .d⟩
  | 102 => ⟨.a, .m, .e⟩
  | 103 => ⟨.a, .i, .e⟩
  | _ => ⟨.a, .b, .a⟩

/-- Superimpose thin, thick and black edge digits with weights 1, 4 and 16. -/
@[expose] def tile (layers : Components) : WangTile :=
  let thin : WangTile := match layers.thin with
    | .a => ⟨1, 2, 2, 1⟩
    | .b => ⟨3, 0, 0, 3⟩
    | .c => ⟨0, 3, 1, 2⟩
    | .d => ⟨2, 1, 3, 0⟩
  let thick : WangTile := match layers.thick with
    | .a => ⟨2, 1, 3, 0⟩
    | .b => ⟨1, 2, 2, 1⟩
    | .c => ⟨0, 3, 1, 2⟩
    | .d => ⟨3, 0, 0, 3⟩
    | .e => ⟨1, 1, 1, 1⟩
    | .f => ⟨0, 0, 1, 1⟩
    | .g => ⟨0, 0, 0, 0⟩
    | .h => ⟨1, 1, 0, 0⟩
    | .i => ⟨3, 3, 0, 0⟩
    | .j => ⟨1, 1, 3, 3⟩
    | .k => ⟨2, 2, 1, 1⟩
    | .l => ⟨0, 0, 2, 2⟩
    | .m => ⟨3, 3, 3, 3⟩
    | .n => ⟨2, 2, 3, 3⟩
    | .o => ⟨2, 2, 2, 2⟩
    | .p => ⟨3, 3, 2, 2⟩
    | .q => ⟨2, 2, 0, 0⟩
    | .r => ⟨0, 0, 3, 3⟩
    | .s => ⟨3, 3, 1, 1⟩
    | .t => ⟨1, 1, 2, 2⟩
  let black : WangTile := match layers.black with
    | .a => ⟨0, 1, 1, 0⟩
    | .b => ⟨1, 0, 0, 0⟩
    | .c => ⟨1, 0, 1, 1⟩
    | .d => ⟨1, 1, 0, 1⟩
    | .e => ⟨0, 0, 0, 1⟩
  ⟨thin.top + 4 * thick.top + 16 * black.top,
    thin.bottom + 4 * thick.bottom + 16 * black.bottom,
    thin.left + 4 * thick.left + 16 * black.left,
    thin.right + 4 * thick.right + 16 * black.right⟩

/-- The 104 corrected tiles, with the component alphabet's order retained. -/
@[expose] def tileSet : List WangTile :=
  (List.finRange 104).map fun index => tile (components index)

/-- Palette membership is witnessed by an index in the corrected alphabet. -/
theorem mem_tileSet {t : WangTile} :
    t ∈ tileSet ↔ ∃ index : Index, tile (components index) = t := by
  simp [tileSet]

/-- Every indexed corrected tile belongs to the concrete palette. -/
theorem tile_components_mem (index : Index) : tile (components index) ∈ tileSet :=
  mem_tileSet.mpr ⟨index, rfl⟩

/-- Figure 16's corrected substitution square; `x = 0` is west and `y = 0` is south. -/
@[expose] def childBlock (parent : Index) (x y : Fin 2) : Index :=
  let square (sw se nw ne : Index) : Index :=
    if y = 0 then (if x = 0 then sw else se) else (if x = 0 then nw else ne)
  match parent.val with
  | 0 => square 0 22 57 4
  | 1 => square 1 20 63 4
  | 2 => square 2 26 69 4
  | 3 => square 3 24 75 4
  | 4 => square 0 17 61 7
  | 5 => square 1 16 67 7
  | 6 => square 2 19 73 7
  | 7 => square 3 18 79 7
  | 8 => square 32 8 76 5
  | 9 => square 33 9 76 5
  | 10 => square 34 10 76 5
  | 11 => square 35 11 76 5
  | 12 => square 36 29 58 5
  | 13 => square 37 31 58 5
  | 14 => square 38 9 58 5
  | 15 => square 39 11 58 5
  | 16 => square 40 28 64 5
  | 17 => square 41 30 64 5
  | 18 => square 42 8 64 5
  | 19 => square 43 10 64 5
  | 20 => square 44 28 70 5
  | 21 => square 45 29 70 5
  | 22 => square 46 30 70 5
  | 23 => square 47 31 70 5
  | 24 => square 48 8 70 5
  | 25 => square 49 9 70 5
  | 26 => square 50 10 70 5
  | 27 => square 51 11 70 5
  | 28 => square 52 28 76 5
  | 29 => square 53 29 76 5
  | 30 => square 54 30 76 5
  | 31 => square 55 31 76 5
  | 32 => square 32 24 74 4
  | 33 => square 33 25 74 4
  | 34 => square 34 26 74 4
  | 35 => square 35 27 74 4
  | 36 => square 36 21 56 4
  | 37 => square 37 23 56 4
  | 38 => square 38 25 56 4
  | 39 => square 39 27 56 4
  | 40 => square 40 20 62 4
  | 41 => square 41 22 62 4
  | 42 => square 42 24 62 4
  | 43 => square 43 26 62 4
  | 44 => square 44 20 68 4
  | 45 => square 45 21 68 4
  | 46 => square 46 22 68 4
  | 47 => square 47 23 68 4
  | 48 => square 48 24 68 4
  | 49 => square 49 25 68 4
  | 50 => square 50 26 68 4
  | 51 => square 51 27 68 4
  | 52 => square 52 20 74 4
  | 53 => square 53 21 74 4
  | 54 => square 54 22 74 4
  | 55 => square 55 23 74 4
  | 56 => square 80 12 59 6
  | 57 => square 81 12 60 6
  | 58 => square 82 13 59 6
  | 59 => square 83 14 59 6
  | 60 => square 84 14 60 6
  | 61 => square 85 15 60 6
  | 62 => square 86 12 65 6
  | 63 => square 87 12 66 6
  | 64 => square 88 13 65 6
  | 65 => square 89 14 65 6
  | 66 => square 90 14 66 6
  | 67 => square 91 15 66 6
  | 68 => square 92 12 71 6
  | 69 => square 93 12 72 6
  | 70 => square 94 13 71 6
  | 71 => square 95 14 71 6
  | 72 => square 96 14 72 6
  | 73 => square 97 15 72 6
  | 74 => square 98 12 77 6
  | 75 => square 99 12 78 6
  | 76 => square 100 13 77 6
  | 77 => square 101 14 77 6
  | 78 => square 102 14 78 6
  | 79 => square 103 15 78 6
  | 80 => square 80 21 56 4
  | 81 => square 81 21 57 4
  | 82 => square 82 23 56 4
  | 83 => square 83 25 56 4
  | 84 => square 84 25 57 4
  | 85 => square 85 27 57 4
  | 86 => square 86 21 62 4
  | 87 => square 87 21 63 4
  | 88 => square 88 23 62 4
  | 89 => square 89 25 62 4
  | 90 => square 90 25 63 4
  | 91 => square 91 27 63 4
  | 92 => square 92 21 68 4
  | 93 => square 93 21 69 4
  | 94 => square 94 23 68 4
  | 95 => square 95 25 68 4
  | 96 => square 96 25 69 4
  | 97 => square 97 27 69 4
  | 98 => square 98 21 74 4
  | 99 => square 99 21 75 4
  | 100 => square 100 23 74 4
  | 101 => square 101 25 74 4
  | 102 => square 102 25 75 4
  | 103 => square 103 27 75 4
  | _ => square 0 22 57 4

/-- The thin-layer phase immediately east of a given phase. -/
@[expose] def phaseEast : Thin → Thin
  | .a => .c | .b => .d | .c => .a | .d => .b

/-- The thin-layer phase immediately north of a given phase. -/
@[expose] def phaseNorth : Thin → Thin
  | .a => .d | .b => .c | .c => .b | .d => .a

private def verifiedAt (parent : Index) : Prop :=
  (∀ x : Fin 2,
    (tile (components (childBlock parent x 0))).top =
      (tile (components (childBlock parent x 1))).bottom) ∧
  (∀ y : Fin 2,
    (tile (components (childBlock parent 0 y))).right =
      (tile (components (childBlock parent 1 y))).left) ∧
  ∀ other : Index,
    ((tile (components parent)).right = (tile (components other)).left ↔
      ∀ y : Fin 2, (tile (components (childBlock parent 1 y))).right =
        (tile (components (childBlock other 0 y))).left) ∧
    ((tile (components parent)).top = (tile (components other)).bottom ↔
      ∀ x : Fin 2, (tile (components (childBlock parent x 1))).top =
        (tile (components (childBlock other x 0))).bottom) ∧
    ((tile (components parent)).right = (tile (components other)).left →
      (components other).thin = phaseEast (components parent).thin) ∧
    ((tile (components parent)).top = (tile (components other)).bottom →
      (components other).thin = phaseNorth (components parent).thin)

private instance (parent : Index) : Decidable (verifiedAt parent) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem check0 : verifiedAt 0 := by decide
private theorem check1 : verifiedAt 1 := by decide
private theorem check2 : verifiedAt 2 := by decide
private theorem check3 : verifiedAt 3 := by decide
private theorem check4 : verifiedAt 4 := by decide
private theorem check5 : verifiedAt 5 := by decide
private theorem check6 : verifiedAt 6 := by decide
private theorem check7 : verifiedAt 7 := by decide
private theorem check8 : verifiedAt 8 := by decide
private theorem check9 : verifiedAt 9 := by decide
private theorem check10 : verifiedAt 10 := by decide
private theorem check11 : verifiedAt 11 := by decide
private theorem check12 : verifiedAt 12 := by decide
private theorem check13 : verifiedAt 13 := by decide
private theorem check14 : verifiedAt 14 := by decide
private theorem check15 : verifiedAt 15 := by decide
private theorem check16 : verifiedAt 16 := by decide
private theorem check17 : verifiedAt 17 := by decide
private theorem check18 : verifiedAt 18 := by decide
private theorem check19 : verifiedAt 19 := by decide
private theorem check20 : verifiedAt 20 := by decide
private theorem check21 : verifiedAt 21 := by decide
private theorem check22 : verifiedAt 22 := by decide
private theorem check23 : verifiedAt 23 := by decide
private theorem check24 : verifiedAt 24 := by decide
private theorem check25 : verifiedAt 25 := by decide
private theorem check26 : verifiedAt 26 := by decide
private theorem check27 : verifiedAt 27 := by decide
private theorem check28 : verifiedAt 28 := by decide
private theorem check29 : verifiedAt 29 := by decide
private theorem check30 : verifiedAt 30 := by decide
private theorem check31 : verifiedAt 31 := by decide
private theorem check32 : verifiedAt 32 := by decide
private theorem check33 : verifiedAt 33 := by decide
private theorem check34 : verifiedAt 34 := by decide
private theorem check35 : verifiedAt 35 := by decide
private theorem check36 : verifiedAt 36 := by decide
private theorem check37 : verifiedAt 37 := by decide
private theorem check38 : verifiedAt 38 := by decide
private theorem check39 : verifiedAt 39 := by decide
private theorem check40 : verifiedAt 40 := by decide
private theorem check41 : verifiedAt 41 := by decide
private theorem check42 : verifiedAt 42 := by decide
private theorem check43 : verifiedAt 43 := by decide
private theorem check44 : verifiedAt 44 := by decide
private theorem check45 : verifiedAt 45 := by decide
private theorem check46 : verifiedAt 46 := by decide
private theorem check47 : verifiedAt 47 := by decide
private theorem check48 : verifiedAt 48 := by decide
private theorem check49 : verifiedAt 49 := by decide
private theorem check50 : verifiedAt 50 := by decide
private theorem check51 : verifiedAt 51 := by decide
private theorem check52 : verifiedAt 52 := by decide
private theorem check53 : verifiedAt 53 := by decide
private theorem check54 : verifiedAt 54 := by decide
private theorem check55 : verifiedAt 55 := by decide
private theorem check56 : verifiedAt 56 := by decide
private theorem check57 : verifiedAt 57 := by decide
private theorem check58 : verifiedAt 58 := by decide
private theorem check59 : verifiedAt 59 := by decide
private theorem check60 : verifiedAt 60 := by decide
private theorem check61 : verifiedAt 61 := by decide
private theorem check62 : verifiedAt 62 := by decide
private theorem check63 : verifiedAt 63 := by decide
private theorem check64 : verifiedAt 64 := by decide
private theorem check65 : verifiedAt 65 := by decide
private theorem check66 : verifiedAt 66 := by decide
private theorem check67 : verifiedAt 67 := by decide
private theorem check68 : verifiedAt 68 := by decide
private theorem check69 : verifiedAt 69 := by decide
private theorem check70 : verifiedAt 70 := by decide
private theorem check71 : verifiedAt 71 := by decide
private theorem check72 : verifiedAt 72 := by decide
private theorem check73 : verifiedAt 73 := by decide
private theorem check74 : verifiedAt 74 := by decide
private theorem check75 : verifiedAt 75 := by decide
private theorem check76 : verifiedAt 76 := by decide
private theorem check77 : verifiedAt 77 := by decide
private theorem check78 : verifiedAt 78 := by decide
private theorem check79 : verifiedAt 79 := by decide
private theorem check80 : verifiedAt 80 := by decide
private theorem check81 : verifiedAt 81 := by decide
private theorem check82 : verifiedAt 82 := by decide
private theorem check83 : verifiedAt 83 := by decide
private theorem check84 : verifiedAt 84 := by decide
private theorem check85 : verifiedAt 85 := by decide
private theorem check86 : verifiedAt 86 := by decide
private theorem check87 : verifiedAt 87 := by decide
private theorem check88 : verifiedAt 88 := by decide
private theorem check89 : verifiedAt 89 := by decide
private theorem check90 : verifiedAt 90 := by decide
private theorem check91 : verifiedAt 91 := by decide
private theorem check92 : verifiedAt 92 := by decide
private theorem check93 : verifiedAt 93 := by decide
private theorem check94 : verifiedAt 94 := by decide
private theorem check95 : verifiedAt 95 := by decide
private theorem check96 : verifiedAt 96 := by decide
private theorem check97 : verifiedAt 97 := by decide
private theorem check98 : verifiedAt 98 := by decide
private theorem check99 : verifiedAt 99 := by decide
private theorem check100 : verifiedAt 100 := by decide
private theorem check101 : verifiedAt 101 := by decide
private theorem check102 : verifiedAt 102 := by decide
private theorem check103 : verifiedAt 103 := by decide

private theorem verified (parent : Index) : verifiedAt parent := by
  fin_cases parent
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41
  · exact check42
  · exact check43
  · exact check44
  · exact check45
  · exact check46
  · exact check47
  · exact check48
  · exact check49
  · exact check50
  · exact check51
  · exact check52
  · exact check53
  · exact check54
  · exact check55
  · exact check56
  · exact check57
  · exact check58
  · exact check59
  · exact check60
  · exact check61
  · exact check62
  · exact check63
  · exact check64
  · exact check65
  · exact check66
  · exact check67
  · exact check68
  · exact check69
  · exact check70
  · exact check71
  · exact check72
  · exact check73
  · exact check74
  · exact check75
  · exact check76
  · exact check77
  · exact check78
  · exact check79
  · exact check80
  · exact check81
  · exact check82
  · exact check83
  · exact check84
  · exact check85
  · exact check86
  · exact check87
  · exact check88
  · exact check89
  · exact check90
  · exact check91
  · exact check92
  · exact check93
  · exact check94
  · exact check95
  · exact check96
  · exact check97
  · exact check98
  · exact check99
  · exact check100
  · exact check101
  · exact check102
  · exact check103

/-- Children in each row of a substituted tile match horizontally. -/
theorem child_horizontal (parent : Index) (y : Fin 2) :
    (tile (components (childBlock parent 0 y))).right =
      (tile (components (childBlock parent 1 y))).left :=
  (verified parent).2.1 y

/-- Children in each column of a substituted tile match vertically. -/
theorem child_vertical (parent : Index) (x : Fin 2) :
    (tile (components (childBlock parent x 0))).top =
      (tile (components (childBlock parent x 1))).bottom :=
  (verified parent).1 x

/-- Parent tiles match horizontally exactly when both substitution boundary edges match. -/
theorem horizontal_iff_children (left right : Index) :
    (tile (components left)).right = (tile (components right)).left ↔
      ∀ y : Fin 2, (tile (components (childBlock left 1 y))).right =
        (tile (components (childBlock right 0 y))).left :=
  ((verified left).2.2 right).1

/-- Parent tiles match vertically exactly when both substitution boundary edges match. -/
theorem vertical_iff_children (lower upper : Index) :
    (tile (components lower)).top = (tile (components upper)).bottom ↔
      ∀ x : Fin 2, (tile (components (childBlock lower x 1))).top =
        (tile (components (childBlock upper x 0))).bottom :=
  ((verified lower).2.2 upper).2.1

/-- Horizontal matching determines the eastern tile's thin-layer phase. -/
theorem thin_east {left right : Index}
    (matching : (tile (components left)).right = (tile (components right)).left) :
    (components right).thin = phaseEast (components left).thin :=
  ((verified left).2.2 right).2.2.1 matching

/-- Vertical matching determines the northern tile's thin-layer phase. -/
theorem thin_north {lower upper : Index}
    (matching : (tile (components lower)).top = (tile (components upper)).bottom) :
    (components upper).thin = phaseNorth (components lower).thin :=
  ((verified lower).2.2 upper).2.2.2 matching

/-- Two eastward phase steps return to the original phase. -/
@[simp] theorem phaseEast_involutive (phase : Thin) : phaseEast (phaseEast phase) = phase := by
  cases phase <;> rfl

/-- Two northward phase steps return to the original phase. -/
@[simp] theorem phaseNorth_involutive (phase : Thin) : phaseNorth (phaseNorth phase) = phase := by
  cases phase <;> rfl

/-- Horizontal and vertical phase propagation commute. -/
theorem phaseEast_phaseNorth_comm (phase : Thin) :
    phaseEast (phaseNorth phase) = phaseNorth (phaseEast phase) := by
  cases phase <;> rfl

end Cslib.WangTile.Robinson
