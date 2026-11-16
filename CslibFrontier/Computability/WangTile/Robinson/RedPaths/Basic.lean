/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Tiles
import Mathlib.Tactic.FinCases

/-!
# Quarter ports and oriented red paths

The corrected Robinson tiles have four quarter sites. Red wires occupy specific lanes and
corners; walks through their ports record the parity of horizontal-to-vertical crossings.
A bounded walk keeps every intermediate port inside its stated rectangle.

## Main definitions

* `Quarters.QuarterIndex`: a tile index and its named quadrant.
* `OrientedRedCycles.CycleOn`: rectangular cycles with their exact inward-facing red lanes.
* `RedShadeGraph.Path`, `RedShadeGraphBoundedPath.BoundedPath`: parity-labelled red walks.

## Main results

* `TileSubdivision.horizontal_iff`, `TileSubdivision.vertical_iff`: exact quarter matching.
* `OrientedRedCycles.CycleOn.refine`: substitution preserves oriented cycles and doubles them.
* `OrientedRedCycles.fixed_cycle`: every twice-substituted tile contains an oriented cycle.

## References

The red-wire construction follows [JeandelVanier2020], §§3.2–3.3, Figures 16–18 (manuscript pp. 26–28).
Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, modules `Closed104.TileSubdivision`, `QuarterGeometry`,
`OrientedRedCycles`, `RedShadeGraph` and `RedShadeGraphBoundedPath`.
The port and crossing parity semantics are unchanged; wire incidence is independent of shades.
-/

public section
namespace Cslib.WangTile.Robinson

@[expose] public section
/-- The four quadrants of a subdivided Wang tile. -/
inductive Quadrant where
  | southwest
  | southeast
  | northwest
  | northeast
deriving DecidableEq, Repr
end

namespace Quadrant

/-- Horizontal coordinate of a quadrant: `false` for west, `true` for east. -/
@[expose] def xBit : Quadrant → Bool
  | southwest => false
  | southeast => true
  | northwest => false
  | northeast => true

/-- Vertical coordinate of a quadrant: `false` for south, `true` for north. -/
@[expose] def yBit : Quadrant → Bool
  | southwest => false
  | southeast => false
  | northwest => true
  | northeast => true

@[expose] def toBits (q : Quadrant) : Bool × Bool :=
  (q.xBit, q.yBit)

@[expose] def ofBits : Bool × Bool → Quadrant
  | (false, false) => southwest
  | (true, false) => southeast
  | (false, true) => northwest
  | (true, true) => northeast

@[expose] def equivBits : Quadrant ≃ Bool × Bool where
  toFun := toBits
  invFun := ofBits
  left_inv := by
    intro q
    cases q <;> rfl
  right_inv := by
    intro bits
    rcases bits with ⟨x, y⟩
    cases x <;> cases y <;> rfl

instance instPrimcodable : Primcodable Quadrant :=
  Primcodable.ofEquiv (Bool × Bool) equivBits

@[expose] def all : List Quadrant :=
  [southwest, southeast, northwest, northeast]

theorem mem_all (q : Quadrant) : q ∈ all := by
  cases q <;> decide

instance : Fintype Quadrant := Fintype.ofList all mem_all

end Quadrant

namespace TileSubdivision

/-- Horizontal macro-edge colors are split by west/east half. -/
@[expose] def horizontalEdgeColor (x : Bool) (color : Nat) : Nat :=
  Nat.pair 0 (Nat.pair (Encodable.encode x) color)

/-- Vertical macro-edge colors are split by south/north half. -/
@[expose] def verticalEdgeColor (y : Bool) (color : Nat) : Nat :=
  Nat.pair 1 (Nat.pair (Encodable.encode y) color)

/-- Internal vertical seam color between west and east quadrants. -/
@[expose] def internalVerticalColor (t : WangTile) (y : Bool) : Nat :=
  Nat.pair 2 (Nat.pair (Encodable.encode y) (Encodable.encode t))

/-- Internal horizontal seam color between south and north quadrants. -/
@[expose] def internalHorizontalColor (t : WangTile) (x : Bool) : Nat :=
  Nat.pair 3 (Nat.pair (Encodable.encode x) (Encodable.encode t))

/-- The quadrant tile of `t` in the 2x2 subdivision. -/
@[expose] def subdivideTileAt (t : WangTile) : Quadrant → WangTile
  | .southwest =>
      { top := internalHorizontalColor t false
        bottom := horizontalEdgeColor false t.bottom
        right := internalVerticalColor t false
        left := verticalEdgeColor false t.left }
  | .southeast =>
      { top := internalHorizontalColor t true
        bottom := horizontalEdgeColor true t.bottom
        right := verticalEdgeColor false t.right
        left := internalVerticalColor t false }
  | .northwest =>
      { top := horizontalEdgeColor false t.top
        bottom := internalHorizontalColor t false
        right := internalVerticalColor t true
        left := verticalEdgeColor true t.left }
  | .northeast =>
      { top := horizontalEdgeColor true t.top
        bottom := internalHorizontalColor t true
        right := verticalEdgeColor true t.right
        left := internalVerticalColor t true }

/-- Matching quarter edges identify internal parents or matching external macro-edges. -/
theorem horizontal_iff (left right : WangTile) (q r : Quadrant) :
    (subdivideTileAt left q).right = (subdivideTileAt right r).left ↔
      match q, r with
      | .southwest, .southeast | .northwest, .northeast => left = right
      | .southeast, .southwest | .northeast, .northwest => left.right = right.left
      | _, _ => False := by
  cases q <;> cases r <;>
    simp [subdivideTileAt, verticalEdgeColor, internalVerticalColor,
      Nat.pair_eq_pair]

/-- The vertical counterpart of quarter-edge matching. -/
theorem vertical_iff (lower upper : WangTile) (q r : Quadrant) :
    (subdivideTileAt lower q).top = (subdivideTileAt upper r).bottom ↔
      match q, r with
      | .southwest, .northwest | .southeast, .northeast => lower = upper
      | .northwest, .southwest | .northeast, .southeast => lower.top = upper.bottom
      | _, _ => False := by
  cases q <;> cases r <;>
    simp [subdivideTileAt, horizontalEdgeColor, internalHorizontalColor,
      Nat.pair_eq_pair]

end TileSubdivision

namespace Quarters

@[expose] public section
/-- A quarter of one indexed tile of the corrected Robinson alphabet. -/
structure QuarterIndex where
  /-- The parent tile. -/
  index : Index
  /-- The quarter occupied in that parent. -/
  quadrant : Quadrant
  deriving DecidableEq
end

/-- The ordinary Wang tile encoding a quarter and its internal seams. -/
@[expose] def quarterTile (site : QuarterIndex) : WangTile :=
  TileSubdivision.subdivideTileAt (tile (components site.index)) site.quadrant

end Quarters

@[expose] public section
/-- The four red lane atoms: east vertical, north horizontal, west vertical, south horizontal. -/
inductive ThickLine where
  | r0 | r1 | r2 | r3
  deriving DecidableEq
end

namespace QuarterGeometry

/-- Membership of a red lane in a thick component; green lanes are omitted. -/
@[expose] def containsLine (component : Thick) (line : ThickLine) : Bool :=
  match line with
  | .r0 => (component matches .e | .h | .j | .t)
  | .r1 => (component matches .e | .f | .k | .s)
  | .r2 => (component matches .f | .g | .l | .r)
  | .r3 => (component matches .g | .h | .i | .q)

/-- Red vertical path in the west (`false`) or east (`true`) half of a tile. -/
@[expose] def redVerticalAt (component : Thick) (east : Bool) : Bool :=
  if east then containsLine component .r0 else containsLine component .r2

/-- Red horizontal path in the south (`false`) or north (`true`) half of a tile. -/
@[expose] def redHorizontalAt (component : Thick) (north : Bool) : Bool :=
  if north then containsLine component .r1 else containsLine component .r3

/-- The quarter occupied by the red turn of a thick corner component. -/
@[expose] def redCorner? : Thick → Option Quadrant
  | .a => some .southeast
  | .b => some .northeast
  | .c => some .northwest
  | .d => some .southwest
  | _ => none

/-- Whether the thick red path occupies a given tile quarter. -/
@[expose] def redAt (component : Thick) (quadrant : Quadrant) : Bool :=
  decide (redCorner? component = some quadrant) ||
    redVerticalAt component quadrant.xBit ||
    redHorizontalAt component quadrant.yBit

/-- Red corner path entering the west edge of this quarter. -/
@[expose] def cornerWest (component : Thick) (quadrant : Quadrant) : Bool :=
  (component, quadrant) matches (.c, .northwest) | (.d, .southwest)

/-- Red corner path entering the east edge of this quarter. -/
@[expose] def cornerEast (component : Thick) (quadrant : Quadrant) : Bool :=
  (component, quadrant) matches (.a, .southeast) | (.b, .northeast)

/-- Red corner path entering the south edge of this quarter. -/
@[expose] def cornerSouth (component : Thick) (quadrant : Quadrant) : Bool :=
  (component, quadrant) matches (.a, .southeast) | (.d, .southwest)

/-- Red corner path entering the north edge of this quarter. -/
@[expose] def cornerNorth (component : Thick) (quadrant : Quadrant) : Bool :=
  (component, quadrant) matches (.b, .northeast) | (.c, .northwest)

@[expose] def hasHorizontal (component : Thick) (quadrant : Quadrant) : Bool :=
  redHorizontalAt component quadrant.yBit

@[expose] def hasVertical (component : Thick) (quadrant : Quadrant) : Bool :=
  redVerticalAt component quadrant.xBit

@[expose] def hasWest (component : Thick) (quadrant : Quadrant) : Bool :=
  hasHorizontal component quadrant || cornerWest component quadrant

@[expose] def hasEast (component : Thick) (quadrant : Quadrant) : Bool :=
  hasHorizontal component quadrant || cornerEast component quadrant

@[expose] def hasSouth (component : Thick) (quadrant : Quadrant) : Bool :=
  hasVertical component quadrant || cornerSouth component quadrant

@[expose] def hasNorth (component : Thick) (quadrant : Quadrant) : Bool :=
  hasVertical component quadrant || cornerNorth component quadrant

/-- The quarter selected by the parity of its coordinates. -/
@[expose] def quadrantAt (x y : Nat) : Quadrant :=
  Quadrant.ofBits (x % 2 == 1, y % 2 == 1)

/-- Thick component at quarter coordinates, grouped by pairs in each direction. -/
@[expose] def componentAt (grid : Nat → Nat → Index) (x y : Nat) : Thick :=
  (components (grid (x / 2) (y / 2))).thick

end QuarterGeometry

namespace RedCycles

/-- Thick component of an indexed tile. -/
abbrev indexThick (index : Index) : Thick := (components index).thick

/-- Simultaneous substitution of an index grid at the quotient and parity coordinates. -/
@[expose] def refineIndexGrid (grid : Nat → Nat → Index) (x y : Nat) : Index :=
  childBlock (grid (x / 2) (y / 2))
    ⟨x % 2, Nat.mod_lt _ (by decide)⟩ ⟨y % 2, Nat.mod_lt _ (by decide)⟩

/-- Substitution at an arbitrary child position. -/
@[simp] theorem refineIndexGrid_child (grid : Nat → Nat → Index) (x y : Nat)
    (dx dy : Fin 2) :
    refineIndexGrid grid (2 * x + dx) (2 * y + dy) = childBlock (grid x y) dx dy := by
  have hx : (2 * x + dx) / 2 = x := by omega
  have hy : (2 * y + dy) / 2 = y := by omega
  have hdx : (2 * x + dx) % 2 = dx := by omega
  have hdy : (2 * y + dy) % 2 = dy := by omega
  simp only [refineIndexGrid, hx, hy, hdx, hdy]

@[simp] private theorem refineIndexGrid_even_even (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x) (2 * y) = childBlock (grid x y) 0 0 := by
  simpa using refineIndexGrid_child grid x y 0 0

@[simp] private theorem refineIndexGrid_odd_even (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x + 1) (2 * y) = childBlock (grid x y) 1 0 := by
  simpa using refineIndexGrid_child grid x y 1 0

@[simp] private theorem refineIndexGrid_even_odd (grid : Nat → Nat → Index) (x y : Nat) :
    refineIndexGrid grid (2 * x) (2 * y + 1) = childBlock (grid x y) 0 1 := by
  simpa using refineIndexGrid_child grid x y 0 1

/-- Iterate simultaneous substitution. -/
@[expose] def iterateRefine : Nat → (Nat → Nat → Index) → Nat → Nat → Index
  | 0, grid => grid
  | level + 1, grid => refineIndexGrid (iterateRefine level grid)

end RedCycles

namespace OrientedRedCycles
open RedCycles QuarterGeometry

/-- A rectangular red cycle with the four inward-facing lane orientations. -/
structure CycleOn (grid : Nat → Nat → Index) (west east south north : Nat) : Prop where
  /-- Positive horizontal extent. -/
  west_lt_east : west < east
  /-- Positive vertical extent. -/
  south_lt_north : south < north
  /-- Southwest inward corner. -/
  southwest : indexThick (grid west south) = .b
  /-- Southeast inward corner. -/
  southeast : indexThick (grid east south) = .c
  /-- Northwest inward corner. -/
  northwest : indexThick (grid west north) = .a
  /-- Northeast inward corner. -/
  northeast : indexThick (grid east north) = .d
  /-- North-facing horizontal lane on the south side. -/
  southLane : ∀ x, west < x → x < east →
    containsLine (indexThick (grid x south)) .r1 = true
  /-- South-facing horizontal lane on the north side. -/
  northLane : ∀ x, west < x → x < east →
    containsLine (indexThick (grid x north)) .r3 = true
  /-- East-facing vertical lane on the west side. -/
  westLane : ∀ y, south < y → y < north →
    containsLine (indexThick (grid west y)) .r0 = true
  /-- West-facing vertical lane on the east side. -/
  eastLane : ∀ y, south < y → y < north →
    containsLine (indexThick (grid east y)) .r2 = true

/-- Substitution preserves each old corner in the southwest child. -/
private theorem corner_child (parent : Index) :
    ∀ corner ∈ [Thick.a, .b, .c, .d], indexThick parent = corner →
      indexThick (childBlock parent 0 0) = corner := by
  revert parent
  decide

/- Finite audit of exact red-lane preservation under substitution. -/
private theorem expansionRules (parent : Index) :
    (containsLine (indexThick parent) .r1 = true →
      containsLine (indexThick ((childBlock parent 0 0))) .r1 = true ∧
      containsLine (indexThick ((childBlock parent 1 0))) .r1 = true) ∧
    (containsLine (indexThick parent) .r3 = true →
      containsLine (indexThick ((childBlock parent 0 0))) .r3 = true ∧
      containsLine (indexThick ((childBlock parent 1 0))) .r3 = true) ∧
    (containsLine (indexThick parent) .r0 = true →
      containsLine (indexThick ((childBlock parent 0 0))) .r0 = true ∧
      containsLine (indexThick ((childBlock parent 0 1))) .r0 = true) ∧
    (containsLine (indexThick parent) .r2 = true →
      containsLine (indexThick ((childBlock parent 0 0))) .r2 = true ∧
      containsLine (indexThick ((childBlock parent 0 1))) .r2 = true) ∧
    (indexThick parent = .b →
      containsLine (indexThick ((childBlock parent 1 0))) .r1 = true) ∧
    (indexThick parent = .a →
      containsLine (indexThick ((childBlock parent 1 0))) .r3 = true) ∧
    (indexThick parent = .b →
      containsLine (indexThick ((childBlock parent 0 1))) .r0 = true) ∧
    (indexThick parent = .c →
      containsLine (indexThick ((childBlock parent 0 1))) .r2 = true) := by
  revert parent
  decide

private theorem r1_children {parent : Index}
    (h : containsLine (indexThick parent) .r1 = true) :
    containsLine (indexThick ((childBlock parent 0 0))) .r1 = true ∧
      containsLine (indexThick ((childBlock parent 1 0))) .r1 = true :=
  (expansionRules parent).1 h

private theorem r3_children {parent : Index}
    (h : containsLine (indexThick parent) .r3 = true) :
    containsLine (indexThick ((childBlock parent 0 0))) .r3 = true ∧
      containsLine (indexThick ((childBlock parent 1 0))) .r3 = true :=
  (expansionRules parent).2.1 h

private theorem r0_children {parent : Index}
    (h : containsLine (indexThick parent) .r0 = true) :
    containsLine (indexThick ((childBlock parent 0 0))) .r0 = true ∧
      containsLine (indexThick ((childBlock parent 0 1))) .r0 = true :=
  (expansionRules parent).2.2.1 h

private theorem r2_children {parent : Index}
    (h : containsLine (indexThick parent) .r2 = true) :
    containsLine (indexThick ((childBlock parent 0 0))) .r2 = true ∧
      containsLine (indexThick ((childBlock parent 0 1))) .r2 = true :=
  (expansionRules parent).2.2.2.1 h

private theorem southeastChild_r1_of_b {parent : Index}
    (h : indexThick parent = .b) :
    containsLine (indexThick ((childBlock parent 1 0))) .r1 = true :=
  (expansionRules parent).2.2.2.2.1 h

private theorem southeastChild_r3_of_a {parent : Index}
    (h : indexThick parent = .a) :
    containsLine (indexThick ((childBlock parent 1 0))) .r3 = true :=
  (expansionRules parent).2.2.2.2.2.1 h

private theorem northwestChild_r0_of_b {parent : Index}
    (h : indexThick parent = .b) :
    containsLine (indexThick ((childBlock parent 0 1))) .r0 = true :=
  (expansionRules parent).2.2.2.2.2.2.1 h

private theorem northwestChild_r2_of_c {parent : Index}
    (h : indexThick parent = .c) :
    containsLine (indexThick ((childBlock parent 0 1))) .r2 = true :=
  (expansionRules parent).2.2.2.2.2.2.2 h

private theorem refinedHorizontalLane
    {grid : Nat → Nat → Index} {west east row : Nat}
    (line : ThickLine)
    (parentLane : ∀ x, west < x → x < east →
      containsLine (indexThick (grid x row)) line = true)
    (children : ∀ {parent : Index},
      containsLine (indexThick parent) line = true →
        containsLine (indexThick ((childBlock parent 0 0))) line = true ∧
        containsLine (indexThick ((childBlock parent 1 0))) line = true)
    (boundary : containsLine
      (indexThick ((childBlock (grid west row) 1 0))) line = true) :
    ∀ x, 2 * west < x → x < 2 * east →
      containsLine (indexThick (refineIndexGrid grid x (2 * row))) line = true := by
  intro x hxWest hxEast
  let parentX := x / 2
  have hmod : x % 2 = 0 ∨ x % 2 = 1 := by
    have hlt := Nat.mod_lt x (by decide : 0 < 2)
    omega
  have hdecomp := Nat.mod_add_div x 2
  rcases hmod with heven | hodd
  · have hx : x = 2 * parentX := by dsimp [parentX]; omega
    rw [hx, refineIndexGrid_even_even]
    exact (children (parentLane parentX (by omega) (by omega))).1
  · have hx : x = 2 * parentX + 1 := by dsimp [parentX]; omega
    by_cases atBoundary : parentX = west
    · rw [hx, refineIndexGrid_odd_even, atBoundary]
      exact boundary
    · rw [hx, refineIndexGrid_odd_even]
      exact (children (parentLane parentX (by omega) (by omega))).2

private theorem refinedVerticalLane
    {grid : Nat → Nat → Index} {south north column : Nat}
    (line : ThickLine)
    (parentLane : ∀ y, south < y → y < north →
      containsLine (indexThick (grid column y)) line = true)
    (children : ∀ {parent : Index},
      containsLine (indexThick parent) line = true →
        containsLine (indexThick ((childBlock parent 0 0))) line = true ∧
        containsLine (indexThick ((childBlock parent 0 1))) line = true)
    (boundary : containsLine
      (indexThick ((childBlock (grid column south) 0 1))) line = true) :
    ∀ y, 2 * south < y → y < 2 * north →
      containsLine (indexThick (refineIndexGrid grid (2 * column) y)) line = true := by
  intro y hySouth hyNorth
  let parentY := y / 2
  have hmod : y % 2 = 0 ∨ y % 2 = 1 := by
    have hlt := Nat.mod_lt y (by decide : 0 < 2)
    omega
  have hdecomp := Nat.mod_add_div y 2
  rcases hmod with heven | hodd
  · have hy : y = 2 * parentY := by dsimp [parentY]; omega
    rw [hy, refineIndexGrid_even_even]
    exact (children (parentLane parentY (by omega) (by omega))).1
  · have hy : y = 2 * parentY + 1 := by dsimp [parentY]; omega
    by_cases atBoundary : parentY = south
    · rw [hy, refineIndexGrid_even_odd, atBoundary]
      exact boundary
    · rw [hy, refineIndexGrid_even_odd]
      exact (children (parentLane parentY (by omega) (by omega))).2

/-- Substitution doubles an oriented red cycle and preserves all four lanes. -/
theorem CycleOn.refine {grid : Nat → Nat → Index}
    {west east south north : Nat}
    (cycle : CycleOn grid west east south north) :
    CycleOn (refineIndexGrid grid)
      (2 * west) (2 * east) (2 * south) (2 * north) where
  west_lt_east := by have := cycle.west_lt_east; omega
  south_lt_north := by have := cycle.south_lt_north; omega
  southwest := by simpa using corner_child (grid west south) .b (by simp) cycle.southwest
  southeast := by simpa using corner_child (grid east south) .c (by simp) cycle.southeast
  northwest := by simpa using corner_child (grid west north) .a (by simp) cycle.northwest
  northeast := by simpa using corner_child (grid east north) .d (by simp) cycle.northeast
  southLane := refinedHorizontalLane .r1 cycle.southLane r1_children
    (southeastChild_r1_of_b cycle.southwest)
  northLane := refinedHorizontalLane .r3 cycle.northLane r3_children
    (southeastChild_r3_of_a cycle.northwest)
  westLane := refinedVerticalLane .r0 cycle.westLane r0_children
    (northwestChild_r0_of_b cycle.southwest)
  eastLane := refinedVerticalLane .r2 cycle.eastLane r2_children
    (northwestChild_r2_of_c cycle.southeast)

/-- Every twice-substituted tile contains the same oriented red board. -/
theorem fixed_cycle (parent : Index) :
    CycleOn (iterateRefine 2 (fun _ _ => parent)) 1 3 1 3 := by
  have checked : ∀ p : Index,
      let g := iterateRefine 2 (fun _ _ => p)
      indexThick (g 1 1) = .b ∧ indexThick (g 3 1) = .c ∧
      indexThick (g 1 3) = .a ∧ indexThick (g 3 3) = .d ∧
      containsLine (indexThick (g 2 1)) .r1 = true ∧
      containsLine (indexThick (g 2 3)) .r3 = true ∧
      containsLine (indexThick (g 1 2)) .r0 = true ∧
      containsLine (indexThick (g 3 2)) .r2 = true := by decide
  obtain ⟨sw, se, nw, ne, s, n, w, e⟩ := checked parent
  refine ⟨by decide, by decide, sw, se, nw, ne, ?_, ?_, ?_, ?_⟩
  all_goals
    intro z hz₁ hz₂
    have : z = 2 := by omega
    subst z
    assumption

/-- Every further substitution preserves the board and scales its coordinates by two. -/
theorem CycleOn.iterateRefine {grid : Nat → Nat → Index} {w e s n : Nat}
    (cycle : CycleOn grid w e s n) (level : Nat) :
    CycleOn (RedCycles.iterateRefine level grid)
      (2 ^ level * w) (2 ^ level * e) (2 ^ level * s) (2 ^ level * n) := by
  induction level with
  | zero => simpa only [RedCycles.iterateRefine, pow_zero, Nat.one_mul] using cycle
  | succ level ih =>
    simpa only [RedCycles.iterateRefine, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using ih.refine

end OrientedRedCycles

namespace RedShadeGraph
open QuarterGeometry

@[expose] public section
/-- A quarter-tile edge at an absolute coordinate. -/
inductive Side where
  | west
  | east
  | south
  | north
deriving DecidableEq, Repr
end

@[expose] public section
structure Port where
  x : Nat
  y : Nat
  side : Side
deriving DecidableEq, Repr
end

/-- Whether the unshaded quarter geometry carries a red wire at a port. -/
@[expose] def portPresent (grid : Nat → Nat → Index) (port : Port) : Bool :=
  let component := componentAt grid port.x port.y
  let quadrant := quadrantAt port.x port.y
  match port.side with
  | .west => hasWest component quadrant
  | .east => hasEast component quadrant
  | .south => hasSouth component quadrant
  | .north => hasNorth component quadrant

/-- One local shade-preserving or shade-reversing connection. -/
inductive Link (indexGrid : Nat → Nat → Index) : Port → Port → Bool → Prop where
  | horizontalMatch (x y : Nat) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x + 1, y, .west⟩ false
  | verticalMatch (x y : Nat) :
      Link indexGrid ⟨x, y, .north⟩ ⟨x, y + 1, .south⟩ false
  | horizontal (x y : Nat)
      (hpath : hasHorizontal
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .east⟩ false
  | vertical (x y : Nat)
      (hpath : hasVertical
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .south⟩ ⟨x, y, .north⟩ false
  | westNorth (x y : Nat)
      (hwest : cornerWest
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hnorth : cornerNorth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .north⟩ false
  | westSouth (x y : Nat)
      (hwest : cornerWest
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hsouth : cornerSouth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .south⟩ false
  | eastNorth (x y : Nat)
      (heast : cornerEast
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hnorth : cornerNorth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x, y, .north⟩ false
  | eastSouth (x y : Nat)
      (heast : cornerEast
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hsouth : cornerSouth
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .east⟩ ⟨x, y, .south⟩ false
  | crossing (x y : Nat)
      (hhorizontal : hasHorizontal
        (componentAt indexGrid x y) (quadrantAt x y) = true)
      (hvertical : hasVertical
        (componentAt indexGrid x y) (quadrantAt x y) = true) :
      Link indexGrid ⟨x, y, .west⟩ ⟨x, y, .south⟩ true
  | symm {first second : Port} {parity : Bool} :
      Link indexGrid first second parity → Link indexGrid second first parity

/-- A finite red-wire walk, labelled by the parity of its crossings. -/
inductive Path (indexGrid : Nat → Nat → Index) : Port → Port → Bool → Prop where
  | refl (port : Port) : Path indexGrid port port false
  | ofLink {first second : Port} {parity : Bool} :
      Link indexGrid first second parity → Path indexGrid first second parity
  | trans {first second third : Port} {firstParity secondParity : Bool} :
      Path indexGrid first second firstParity →
      Path indexGrid second third secondParity →
      Path indexGrid first third (Bool.xor firstParity secondParity)

/-- Reversing a walk preserves its crossing parity. -/
theorem Path.symm {grid : Nat → Nat → Index} {first second : Port} {parity : Bool}
    (path : Path grid first second parity) : Path grid second first parity := by
  induction path with
  | refl port => exact .refl port
  | ofLink link => exact .ofLink (.symm link)
  | trans _ _ ih₁ ih₂ => simpa only [Bool.xor_comm] using Path.trans ih₂ ih₁

end RedShadeGraph

namespace RedShadeGraphBoundedPath
open RedShadeGraph

@[expose] def PortInBounds (port : Port) (width height : Nat) : Prop :=
  port.x < width ∧ port.y < height

inductive BoundedPath (indexGrid : Nat → Nat → Index)
    (width height : Nat) : Port → Port → Bool → Prop where
  | refl (port : Port) (hport : PortInBounds port width height) :
      BoundedPath indexGrid width height port port false
  | ofLink {first second : Port} {parity : Bool}
      (link : Link indexGrid first second parity)
      (hfirst : PortInBounds first width height)
      (hsecond : PortInBounds second width height) :
      BoundedPath indexGrid width height first second parity
  | trans {first second third : Port} {firstParity secondParity : Bool}
      (firstPath : BoundedPath indexGrid width height
        first second firstParity)
      (secondPath : BoundedPath indexGrid width height
        second third secondParity) :
      BoundedPath indexGrid width height first third
        (Bool.xor firstParity secondParity)

theorem BoundedPath.path
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    Path indexGrid first second parity := by
  induction path with
  | refl port _ => exact Path.refl port
  | ofLink link _ _ => exact Path.ofLink link
  | trans _ _ firstIH secondIH => exact Path.trans firstIH secondIH

theorem BoundedPath.first_inBounds
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    PortInBounds first width height := by
  induction path with
  | refl _ hport => exact hport
  | ofLink _ hfirst _ => exact hfirst
  | trans _ _ firstIH _ => exact firstIH

theorem BoundedPath.second_inBounds
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    PortInBounds second width height := by
  induction path with
  | refl _ hport => exact hport
  | ofLink _ _ hsecond => exact hsecond
  | trans _ _ _ secondIH => exact secondIH

end RedShadeGraphBoundedPath
end Cslib.WangTile.Robinson
