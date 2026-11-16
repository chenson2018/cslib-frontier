/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.RedPaths.Certificates

/-!
# Red-wire shades and their propagation

Each red edge of a Robinson quarter carries a light or dark shade. Straight wires and
corners preserve shades; crossings require opposite shades. A locally allowed matching
assignment therefore respects the parity of each red-graph path, and every rectangular
oriented red cycle carries one shade around its boundary.

## Main definitions

* `RedShades.State` and `RedShades.allowedFor`: quarter shades and the local decoration rule.
* `RedShadePaths.ValidShadeGrid`: a locally allowed matching shade assignment.
* `RedShadeCycles.CycleShade`: uniform shades on the inward corners of a rectangular board.
* `RedShadeGraph.ValidPortLabeling`: a parity-consistent labeling with the prescribed incidence.

## Main results

* `RedShadeCycles.CycleOn.exists_cycleShade`: every oriented red cycle has a uniform shade.
* `RedShadeCycles.CycleShade.south_at` and the other side lemmas propagate that shade along
  the complete boundary.
* `RedShadeGraph.Path.sound`: path parity determines shade equality or opposition.
* `RedShadeGraphBoundedPath.BoundedPath.sound`: bounded paths need validity only inside
  their bounding rectangle.
* `RedShadeGraph.ValidPortLabeling.validShadeGrid`: consistent port labels give valid shades.
* `RedShadeGraphCoarsening.valid` and `cycleShade`: coarsening through two substitutions
  preserves matching shade rules and the shade of every oriented cycle.

## References

The shading rules follow [JeandelVanier2020], §3.3, Figures 17–18 (manuscript pp. 24, 26–28).
Prior formalization: [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, modules `Closed104.RedShades`, `RedShadePaths`, `RedShadeCycles` and
`RedShadeGraph`, `RedShadeGraphCoarsening`, `SignalCorridors`, `Signals` and `ShadedSignals`.
These are local decoration and propagation steps of the corrected Robinson scaffold, not the
seed-removal theorem.
-/

public section
namespace Cslib.WangTile.Robinson

namespace RedShades

open Quarters QuarterGeometry

-- Finite downstream checks need the generated equality helpers through ordinary imports.
@[expose] public section
/-- The two shades of a red wire. -/
inductive Shade where
  | light
  | dark
deriving DecidableEq, Repr
end

namespace Shade

/-- Both shades, in light/dark order for finite enumeration. -/
@[expose] def all : List Shade := [.light, .dark]

@[simp] theorem mem_all (shade : Shade) : shade ∈ all := by
  cases shade <;> decide

/-- Exchange the two red-wire shades. -/
@[expose] def opposite : Shade → Shade
  | .light => .dark
  | .dark => .light

@[simp] theorem opposite_opposite (shade : Shade) :
    shade.opposite.opposite = shade := by
  cases shade <;> rfl

theorem eq_opposite_of_ne {first second : Shade} (hne : first ≠ second) :
    second = first.opposite := by
  cases first <;> cases second <;> simp_all [opposite]

end Shade

@[expose] public section
/-- Optional shade carried by each edge of one quarter tile. -/
structure State where
  /-- Shade on the west edge, absent when there is no red wire. -/
  west : Option Shade
  /-- Shade on the east edge. -/
  east : Option Shade
  /-- Shade on the south edge. -/
  south : Option Shade
  /-- Shade on the north edge. -/
  north : Option Shade
deriving DecidableEq, Repr
end

namespace State

/-- Every four-edge shade state, in west/east/south/north order. -/
@[expose] def all : List State :=
  let edgeValues := none :: Shade.all.map some
  edgeValues.flatMap fun west =>
    edgeValues.flatMap fun east =>
      edgeValues.flatMap fun south =>
        edgeValues.map fun north => ⟨west, east, south, north⟩

@[simp] private theorem mem_edgeValues (value : Option Shade) :
    value ∈ (none :: Shade.all.map some) := by
  rcases value with _ | shade
  · simp
  · simp

@[simp] theorem mem_all (state : State) : state ∈ all := by
  rcases state with ⟨west, east, south, north⟩
  simp only [all, List.mem_flatMap, List.mem_map]
  exact ⟨west, mem_edgeValues _, east, mem_edgeValues _, south, mem_edgeValues _,
    north, mem_edgeValues _, rfl⟩

end State

/-- Local rule with the thick component made explicit for proof reuse. -/
@[expose] def allowedFor (component : Thick) (quadrant : Quadrant) (state : State) : Bool :=
  decide (Option.isSome state.west = hasWest component quadrant) &&
    decide (Option.isSome state.east = hasEast component quadrant) &&
    decide (Option.isSome state.south = hasSouth component quadrant) &&
    decide (Option.isSome state.north = hasNorth component quadrant) &&
    (if hasHorizontal component quadrant then decide (state.west = state.east)
      else true) &&
    (if hasVertical component quadrant then decide (state.south = state.north)
      else true) &&
    (if cornerEast component quadrant && cornerSouth component quadrant then
      decide (state.east = state.south) else true) &&
    (if cornerEast component quadrant && cornerNorth component quadrant then
      decide (state.east = state.north) else true) &&
    (if cornerWest component quadrant && cornerSouth component quadrant then
      decide (state.west = state.south) else true) &&
    (if cornerWest component quadrant && cornerNorth component quadrant then
      decide (state.west = state.north) else true) &&
    (if hasHorizontal component quadrant && hasVertical component quadrant then
      decide (state.west ≠ state.south) else true)

/-- Constructor form of the local red-shade rule. -/
theorem allowedFor_of {component : Thick} {quadrant : Quadrant} {state : State}
    (hwest : state.west.isSome = hasWest component quadrant)
    (heast : state.east.isSome = hasEast component quadrant)
    (hsouth : state.south.isSome = hasSouth component quadrant)
    (hnorth : state.north.isSome = hasNorth component quadrant)
    (hhorizontal : hasHorizontal component quadrant = true →
      state.west = state.east)
    (hvertical : hasVertical component quadrant = true →
      state.south = state.north)
    (heastSouth : cornerEast component quadrant = true →
      cornerSouth component quadrant = true → state.east = state.south)
    (heastNorth : cornerEast component quadrant = true →
      cornerNorth component quadrant = true → state.east = state.north)
    (hwestSouth : cornerWest component quadrant = true →
      cornerSouth component quadrant = true → state.west = state.south)
    (hwestNorth : cornerWest component quadrant = true →
      cornerNorth component quadrant = true → state.west = state.north)
    (hcrossing : hasHorizontal component quadrant = true →
      hasVertical component quadrant = true → state.west ≠ state.south) :
    allowedFor component quadrant state = true := by
  simp only [allowedFor, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwest, heast⟩, hsouth⟩, hnorth⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all
  · split <;> simp_all

/-- Local red-path incidence, propagation, corner, and crossing rules. -/
@[expose] def locallyAllowed (site : QuarterIndex) (state : State) : Bool :=
  allowedFor (components site.index).thick site.quadrant state

theorem horizontal_eq_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (hhorizontal : hasHorizontal component quadrant = true) :
    state.west = state.east := by
  simp only [allowedFor, hhorizontal, Bool.and_eq_true,
    decide_eq_true_eq, Bool.true_and, ite_true] at hallowed
  aesop

theorem vertical_eq_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (hvertical : hasVertical component quadrant = true) :
    state.south = state.north := by
  simp only [allowedFor, hvertical, Bool.and_eq_true,
    decide_eq_true_eq, ite_true] at hallowed
  aesop

theorem east_present_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (heast : hasEast component quadrant = true) :
    state.east.isSome = true := by
  simp only [allowedFor, heast, Bool.and_eq_true,
    decide_eq_true_eq] at hallowed
  aesop

theorem west_present_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (hwest : hasWest component quadrant = true) :
    state.west.isSome = true := by
  simp only [allowedFor, hwest, Bool.and_eq_true,
    decide_eq_true_eq] at hallowed
  aesop

theorem south_present_of_allowedFor {component : Thick} {quadrant : Quadrant}
    {state : State} (hallowed : allowedFor component quadrant state = true)
    (hsouth : hasSouth component quadrant = true) :
    state.south.isSome = true := by
  simp only [allowedFor, hsouth, Bool.and_eq_true,
    decide_eq_true_eq] at hallowed
  aesop

theorem west_north_corner_eq_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (hwest : cornerWest component quadrant = true)
    (hnorth : cornerNorth component quadrant = true) :
    state.west = state.north := by
  cases component <;> cases quadrant <;>
    simp_all [allowedFor, cornerWest, cornerNorth]

theorem west_south_corner_eq_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (hwest : cornerWest component quadrant = true)
    (hsouth : cornerSouth component quadrant = true) :
    state.west = state.south := by
  cases component <;> cases quadrant <;>
    simp_all [allowedFor, cornerWest, cornerSouth]

theorem east_north_corner_eq_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (heast : cornerEast component quadrant = true)
    (hnorth : cornerNorth component quadrant = true) :
    state.east = state.north := by
  cases component <;> cases quadrant <;>
    simp_all [allowedFor, cornerEast, cornerNorth]

theorem crossing_opposite_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (hhorizontal : hasHorizontal component quadrant = true)
    (hvertical : hasVertical component quadrant = true) :
    state.west ≠ state.south := by
  simp only [allowedFor, hhorizontal, hvertical, Bool.and_eq_true,
    decide_eq_true_eq, Bool.true_and, ite_true] at hallowed
  aesop

/-- Equality of the two edges of a southeast corner. -/
theorem east_south_corner_eq_of_allowedFor {component : Thick}
    {quadrant : Quadrant} {state : State}
    (hallowed : allowedFor component quadrant state = true)
    (heast : cornerEast component quadrant = true)
    (hsouth : cornerSouth component quadrant = true) :
    state.east = state.south := by
  cases component <;> cases quadrant <;>
    simp_all [allowedFor, cornerEast, cornerSouth]

end RedShades

namespace RedShadePaths

open RedCycles QuarterGeometry

/-- A locally allowed, edge-matching shade assignment over a quarter grid. -/
structure ValidShadeGrid (indexGrid : Nat → Nat → Index)
    (stateGrid : Nat → Nat → RedShades.State) : Prop where
  /-- Every quarter satisfies the local incidence and shade rules. -/
  allowed : ∀ x y,
    RedShades.locallyAllowed
      ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩ (stateGrid x y) = true
  /-- Adjacent quarters agree on horizontal shared edges. -/
  hmatch : ∀ x y, (stateGrid x y).east = (stateGrid (x + 1) y).west
  /-- Adjacent quarters agree on vertical shared edges. -/
  vmatch : ∀ x y, (stateGrid x y).north = (stateGrid x (y + 1)).south

theorem ValidShadeGrid.horizontal_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : hasHorizontal
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).east :=
  RedShades.horizontal_eq_of_allowedFor (valid.allowed x y) hpath

theorem ValidShadeGrid.vertical_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : hasVertical
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).south = (stateGrid x y).north :=
  RedShades.vertical_eq_of_allowedFor (valid.allowed x y) hpath

theorem ValidShadeGrid.east_present
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : hasEast
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).east.isSome = true :=
  RedShades.east_present_of_allowedFor (valid.allowed x y) hpath

theorem ValidShadeGrid.west_present
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : hasWest
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west.isSome = true :=
  RedShades.west_present_of_allowedFor (valid.allowed x y) hpath

theorem ValidShadeGrid.south_present
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : hasSouth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).south.isSome = true :=
  RedShades.south_present_of_allowedFor (valid.allowed x y) hpath

theorem ValidShadeGrid.west_north_corner_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hwest : cornerWest
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hnorth : cornerNorth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).north :=
  RedShades.west_north_corner_eq_of_allowedFor
    (valid.allowed x y) hwest hnorth

theorem ValidShadeGrid.west_south_corner_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hwest : cornerWest
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hsouth : cornerSouth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).south :=
  RedShades.west_south_corner_eq_of_allowedFor
    (valid.allowed x y) hwest hsouth

theorem ValidShadeGrid.east_north_corner_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (heast : cornerEast
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hnorth : cornerNorth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).east = (stateGrid x y).north :=
  RedShades.east_north_corner_eq_of_allowedFor
    (valid.allowed x y) heast hnorth

theorem ValidShadeGrid.crossing_opposite
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hhorizontal : hasHorizontal
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hvertical : hasVertical
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west ≠ (stateGrid x y).south :=
  RedShades.crossing_opposite_of_allowedFor
    (valid.allowed x y) hhorizontal hvertical

/-- Matching edges and transmitting intermediate cells preserve any value
across a one-dimensional corridor. -/
theorem value_across {α β : Type*}
    (state : Nat → α) (outgoing incoming : α → β) (start count : Nat)
    (hmatch : ∀ i, i ≤ count →
      outgoing (state (start + i)) = incoming (state (start + i + 1)))
    (htransmit : ∀ i, i < count →
      incoming (state (start + i + 1)) = outgoing (state (start + i + 1))) :
    outgoing (state start) = incoming (state (start + count + 1)) := by
  induction count with
  | zero => simpa using hmatch 0 (by omega)
  | succ count ih =>
      have hprefix := ih
        (fun i hi => hmatch i (by omega))
        (fun i hi => htransmit i (by omega))
      calc
        outgoing (state start) = incoming (state (start + count + 1)) := hprefix
        _ = outgoing (state (start + count + 1)) := htransmit count (by omega)
        _ = incoming (state (start + (count + 1) + 1)) := by
          simpa [Nat.add_assoc] using hmatch (count + 1) (by omega)


/-- Matching and transmission on an interval identify its two boundary values. -/
theorem value_between {α β : Type*}
    (state : Nat → α) (outgoing incoming : α → β)
    {start finish : Nat} (hlt : start < finish)
    (hmatch : ∀ position, start ≤ position → position < finish →
      outgoing (state position) = incoming (state (position + 1)))
    (htransmit : ∀ position, start < position → position < finish →
      incoming (state position) = outgoing (state position)) :
    outgoing (state start) = incoming (state finish) := by
  have flow := value_across state outgoing incoming start (finish - start - 1)
    (fun offset _ => hmatch (start + offset) (by omega) (by omega))
    (fun offset _ => htransmit (start + offset + 1) (by omega) (by omega))
  have end_eq : start + (finish - start - 1) + 1 = finish := by omega
  simpa only [end_eq] using flow


end RedShadePaths

namespace RedShadeCycles

open RedCycles QuarterGeometry RedShadePaths

/- Parent coordinates refer to tile centers and lanes.  The `quarter*`
coordinates select the inward side of each boundary tile, where the shade
layer actually carries the cycle. -/

@[expose] def quarterWest (west : Nat) : Nat := 2 * west + 1
@[expose] def quarterEast (east : Nat) : Nat := 2 * east
@[expose] def quarterSouth (south : Nat) : Nat := 2 * south + 1
@[expose] def quarterNorth (north : Nat) : Nat := 2 * north

theorem componentAt_double_add (grid : Nat → Nat → Index)
    (x y dx dy : Nat) (hdx : dx < 2) (hdy : dy < 2) :
    componentAt grid (2 * x + dx) (2 * y + dy) =
      indexThick (grid x y) := by
  unfold componentAt
  have hx : (2 * x + dx) / 2 = x := by omega
  have hy : (2 * y + dy) / 2 = y := by omega
  rw [hx, hy]

@[simp] theorem quadrantAt_quarterSouth_yBit (x south : Nat) :
    (quadrantAt x (quarterSouth south)).yBit = true := by
  cases hbit : (x % 2 == 1) <;>
    simp [quadrantAt, quarterSouth, Quadrant.ofBits, Quadrant.yBit, hbit]

@[simp] theorem quadrantAt_quarterNorth_yBit (x north : Nat) :
    (quadrantAt x (quarterNorth north)).yBit = false := by
  cases hbit : (x % 2 == 1) <;>
    simp [quadrantAt, quarterNorth, Quadrant.ofBits, Quadrant.yBit, hbit]

@[simp] theorem quadrantAt_quarterWest_xBit (west y : Nat) :
    (quadrantAt (quarterWest west) y).xBit = true := by
  cases hbit : (y % 2 == 1) <;>
    simp [quadrantAt, quarterWest, Quadrant.ofBits, Quadrant.xBit, hbit]

@[simp] theorem quadrantAt_quarterEast_xBit (east y : Nat) :
    (quadrantAt (quarterEast east) y).xBit = false := by
  cases hbit : (y % 2 == 1) <;>
    simp [quadrantAt, quarterEast, Quadrant.ofBits, Quadrant.xBit, hbit]

theorem CycleOn.southwest_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    cornerEast
        (componentAt grid (quarterWest west) (quarterSouth south))
        (quadrantAt (quarterWest west) (quarterSouth south)) = true ∧
      cornerNorth
        (componentAt grid (quarterWest west) (quarterSouth south))
        (quadrantAt (quarterWest west) (quarterSouth south)) = true := by
  rw [quarterWest, quarterSouth,
    componentAt_double_add grid west south 1 1 (by omega) (by omega),
    cycle.southwest]
  simp [quadrantAt, Quadrant.ofBits,
    cornerEast, cornerNorth]

theorem CycleOn.southeast_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    cornerWest
        (componentAt grid (quarterEast east) (quarterSouth south))
        (quadrantAt (quarterEast east) (quarterSouth south)) = true ∧
      cornerNorth
        (componentAt grid (quarterEast east) (quarterSouth south))
        (quadrantAt (quarterEast east) (quarterSouth south)) = true := by
  rw [quarterEast, quarterSouth,
    show 2 * east = 2 * east + 0 by omega,
    componentAt_double_add grid east south 0 1 (by omega) (by omega),
    cycle.southeast]
  simp [quadrantAt, Quadrant.ofBits,
    cornerWest, cornerNorth]

theorem CycleOn.northeast_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    cornerWest
        (componentAt grid (quarterEast east) (quarterNorth north))
        (quadrantAt (quarterEast east) (quarterNorth north)) = true ∧
      cornerSouth
        (componentAt grid (quarterEast east) (quarterNorth north))
        (quadrantAt (quarterEast east) (quarterNorth north)) = true := by
  rw [quarterEast, quarterNorth,
    show 2 * east = 2 * east + 0 by omega,
    show 2 * north = 2 * north + 0 by omega,
    componentAt_double_add grid east north 0 0 (by omega) (by omega),
    cycle.northeast]
  simp [quadrantAt, Quadrant.ofBits,
    cornerWest, cornerSouth]

theorem CycleOn.northwest_corner
    {grid : Nat → Nat → Index} {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north) :
    cornerEast
        (componentAt grid (quarterWest west) (quarterNorth north))
        (quadrantAt (quarterWest west) (quarterNorth north)) = true ∧
      cornerSouth
        (componentAt grid (quarterWest west) (quarterNorth north))
        (quadrantAt (quarterWest west) (quarterNorth north)) = true := by
  rw [quarterWest, quarterNorth,
    show 2 * north = 2 * north + 0 by omega,
    componentAt_double_add grid west north 1 0 (by omega) (by omega),
    cycle.northwest]
  simp [quadrantAt, Quadrant.ofBits,
    cornerEast, cornerSouth]

theorem CycleOn.south_path
    {grid : Nat → Nat → Index} {west east south north qx : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    hasHorizontal
      (componentAt grid qx (quarterSouth south))
      (quadrantAt qx (quarterSouth south)) = true := by
  have hparentWest : west < qx / 2 := by
    unfold quarterWest at hwest
    omega
  have hparentEast : qx / 2 < east := by
    unfold quarterEast at heast
    omega
  have hline := cycle.southLane (qx / 2) hparentWest hparentEast
  unfold hasHorizontal
  rw [quadrantAt_quarterSouth_yBit]
  simp only [redHorizontalAt]
  unfold componentAt
  have hdivY : quarterSouth south / 2 = south := by
    unfold quarterSouth
    omega
  rw [hdivY]
  exact hline

theorem CycleOn.north_path
    {grid : Nat → Nat → Index} {west east south north qx : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    hasHorizontal
      (componentAt grid qx (quarterNorth north))
      (quadrantAt qx (quarterNorth north)) = true := by
  have hparentWest : west < qx / 2 := by
    unfold quarterWest at hwest
    omega
  have hparentEast : qx / 2 < east := by
    unfold quarterEast at heast
    omega
  have hline := cycle.northLane (qx / 2) hparentWest hparentEast
  unfold hasHorizontal
  rw [quadrantAt_quarterNorth_yBit]
  simp only [redHorizontalAt]
  unfold componentAt
  have hdivY : quarterNorth north / 2 = north := by
    unfold quarterNorth
    omega
  rw [hdivY]
  exact hline

theorem CycleOn.west_path
    {grid : Nat → Nat → Index} {west east south north qy : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    hasVertical
      (componentAt grid (quarterWest west) qy)
      (quadrantAt (quarterWest west) qy) = true := by
  have hparentSouth : south < qy / 2 := by
    unfold quarterSouth at hsouth
    omega
  have hparentNorth : qy / 2 < north := by
    unfold quarterNorth at hnorth
    omega
  have hline := cycle.westLane (qy / 2) hparentSouth hparentNorth
  unfold hasVertical
  rw [quadrantAt_quarterWest_xBit]
  simp only [redVerticalAt]
  unfold componentAt
  have hdivX : quarterWest west / 2 = west := by
    unfold quarterWest
    omega
  rw [hdivX]
  exact hline

theorem CycleOn.east_path
    {grid : Nat → Nat → Index} {west east south north qy : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    hasVertical
      (componentAt grid (quarterEast east) qy)
      (quadrantAt (quarterEast east) qy) = true := by
  have hparentSouth : south < qy / 2 := by
    unfold quarterSouth at hsouth
    omega
  have hparentNorth : qy / 2 < north := by
    unfold quarterNorth at hnorth
    omega
  have hline := cycle.eastLane (qy / 2) hparentSouth hparentNorth
  unfold hasVertical
  rw [quadrantAt_quarterEast_xBit]
  simp only [redVerticalAt]
  unfold componentAt
  have hdivX : quarterEast east / 2 = east := by
    unfold quarterEast
    omega
  rw [hdivX]
  exact hline

/- The four path lemmas turn geometric cycle lanes into transmissive
quarter-level red lines.  Starting from one present corner shade, edge matching
and corner equalities carry it counterclockwise to all four corners. -/

/-- Uniform shade at the four inward quarter corners of an arbitrary board. -/
structure CycleShade (stateGrid : Nat → Nat → RedShades.State)
    (west east south north : Nat) (shade : RedShades.Shade) : Prop where
  southwest : (stateGrid (quarterWest west) (quarterSouth south)).east =
    some shade
  southeast : (stateGrid (quarterEast east) (quarterSouth south)).west =
    some shade
  northeast : (stateGrid (quarterEast east) (quarterNorth north)).west =
    some shade
  northwest : (stateGrid (quarterWest west) (quarterNorth north)).east =
    some shade

/-- A shade on one edge of any oriented board propagates to every corner. -/
theorem CycleOn.cycleShade
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) (shade : RedShades.Shade)
    (hshade :
      (stateGrid (quarterWest west) (quarterSouth south)).east = some shade) :
    CycleShade stateGrid west east south north shade := by
  have hquarterWestEast : quarterWest west < quarterEast east := by
    unfold quarterWest quarterEast
    have := cycle.west_lt_east
    omega
  have hquarterSouthNorth : quarterSouth south < quarterNorth north := by
    unfold quarterSouth quarterNorth
    have := cycle.south_lt_north
    omega
  have hsouth :
      (stateGrid (quarterWest west) (quarterSouth south)).east =
        (stateGrid (quarterEast east) (quarterSouth south)).west := by
    exact value_between (fun x => stateGrid x (quarterSouth south))
      RedShades.State.east RedShades.State.west hquarterWestEast
      (fun x _ _ => valid.hmatch x (quarterSouth south))
      (fun x hw he => valid.horizontal_eq x (quarterSouth south) (CycleOn.south_path cycle hw he))
  have hseNorth :
      (stateGrid (quarterEast east) (quarterSouth south)).north = some shade := by
    rw [← valid.west_north_corner_eq
      (quarterEast east) (quarterSouth south)
      (CycleOn.southeast_corner cycle).1 (CycleOn.southeast_corner cycle).2]
    exact hsouth.symm.trans hshade
  have heast :
      (stateGrid (quarterEast east) (quarterSouth south)).north =
        (stateGrid (quarterEast east) (quarterNorth north)).south := by
    exact value_between (fun y => stateGrid (quarterEast east) y)
      RedShades.State.north RedShades.State.south hquarterSouthNorth
      (fun y _ _ => valid.vmatch (quarterEast east) y)
      (fun y hs hn => valid.vertical_eq (quarterEast east) y (CycleOn.east_path cycle hs hn))
  have hneWest :
      (stateGrid (quarterEast east) (quarterNorth north)).west = some shade := by
    rw [valid.west_south_corner_eq
      (quarterEast east) (quarterNorth north)
      (CycleOn.northeast_corner cycle).1 (CycleOn.northeast_corner cycle).2]
    exact heast.symm.trans hseNorth
  have hnorth :
      (stateGrid (quarterWest west) (quarterNorth north)).east =
        (stateGrid (quarterEast east) (quarterNorth north)).west := by
    exact value_between (fun x => stateGrid x (quarterNorth north))
      RedShades.State.east RedShades.State.west hquarterWestEast
      (fun x _ _ => valid.hmatch x (quarterNorth north))
      (fun x hw he => valid.horizontal_eq x (quarterNorth north) (CycleOn.north_path cycle hw he))
  exact {
    southwest := hshade
    southeast := hsouth.symm.trans hshade
    northeast := hneWest
    northwest := hnorth.trans hneWest
  }

/-- Every oriented red board has one uniform light/dark corner shade. -/
theorem CycleOn.exists_cycleShade
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat}
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) :
    ∃ shade, CycleShade stateGrid west east south north shade := by
  have heast : hasEast
      (componentAt grid (quarterWest west) (quarterSouth south))
      (quadrantAt (quarterWest west) (quarterSouth south)) = true := by
    simp [hasEast, (CycleOn.southwest_corner cycle).1]
  have hpresent := valid.east_present
    (quarterWest west) (quarterSouth south) heast
  rcases hshade :
      (stateGrid (quarterWest west) (quarterSouth south)).east with _ | shade
  · simp [hshade] at hpresent
  · exact ⟨shade, CycleOn.cycleShade cycle valid shade hshade⟩

theorem CycleShade.south_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qx : Nat}
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    (stateGrid qx (quarterSouth south)).west = some shade ∧
      (stateGrid qx (quarterSouth south)).east = some shade := by
  have hflow := value_between (fun x => stateGrid x (quarterSouth south))
    RedShades.State.east RedShades.State.west hwest
    (fun x _ _ => valid.hmatch x (quarterSouth south))
    (fun x hw hx => valid.horizontal_eq x (quarterSouth south)
      (CycleOn.south_path cycle hw (lt_trans hx heast)))
  have hwestShade := hflow.symm.trans shaded.southwest
  exact ⟨hwestShade,
    (valid.horizontal_eq qx (quarterSouth south)
      (CycleOn.south_path cycle hwest heast)).symm.trans hwestShade⟩

theorem CycleShade.north_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qx : Nat}
    (hwest : quarterWest west < qx) (heast : qx < quarterEast east) :
    (stateGrid qx (quarterNorth north)).west = some shade ∧
      (stateGrid qx (quarterNorth north)).east = some shade := by
  have hflow := value_between (fun x => stateGrid x (quarterNorth north))
    RedShades.State.east RedShades.State.west hwest
    (fun x _ _ => valid.hmatch x (quarterNorth north))
    (fun x hw hx => valid.horizontal_eq x (quarterNorth north)
      (CycleOn.north_path cycle hw (lt_trans hx heast)))
  have hwestShade := hflow.symm.trans shaded.northwest
  exact ⟨hwestShade,
    (valid.horizontal_eq qx (quarterNorth north)
      (CycleOn.north_path cycle hwest heast)).symm.trans hwestShade⟩

theorem CycleShade.west_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qy : Nat}
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    (stateGrid (quarterWest west) qy).south = some shade ∧
      (stateGrid (quarterWest west) qy).north = some shade := by
  have hstart :
      (stateGrid (quarterWest west) (quarterSouth south)).north = some shade := by
    rw [← valid.east_north_corner_eq (quarterWest west) (quarterSouth south)
      (CycleOn.southwest_corner cycle).1 (CycleOn.southwest_corner cycle).2]
    exact shaded.southwest
  have hflow := value_between (fun y => stateGrid (quarterWest west) y)
    RedShades.State.north RedShades.State.south hsouth
    (fun y _ _ => valid.vmatch (quarterWest west) y)
    (fun y hs hy => valid.vertical_eq (quarterWest west) y
      (CycleOn.west_path cycle hs (lt_trans hy hnorth)))
  have hsouthShade := hflow.symm.trans hstart
  exact ⟨hsouthShade,
    (valid.vertical_eq (quarterWest west) qy
      (CycleOn.west_path cycle hsouth hnorth)).symm.trans hsouthShade⟩

theorem CycleShade.east_at
    {grid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (shaded : CycleShade stateGrid west east south north shade)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (valid : ValidShadeGrid grid stateGrid) {qy : Nat}
    (hsouth : quarterSouth south < qy) (hnorth : qy < quarterNorth north) :
    (stateGrid (quarterEast east) qy).south = some shade ∧
      (stateGrid (quarterEast east) qy).north = some shade := by
  have hstart :
      (stateGrid (quarterEast east) (quarterSouth south)).north = some shade := by
    rw [← valid.west_north_corner_eq (quarterEast east) (quarterSouth south)
      (CycleOn.southeast_corner cycle).1 (CycleOn.southeast_corner cycle).2]
    exact shaded.southeast
  have hflow := value_between (fun y => stateGrid (quarterEast east) y)
    RedShades.State.north RedShades.State.south hsouth
    (fun y _ _ => valid.vmatch (quarterEast east) y)
    (fun y hs hy => valid.vertical_eq (quarterEast east) y
      (CycleOn.east_path cycle hs (lt_trans hy hnorth)))
  have hsouthShade := hflow.symm.trans hstart
  exact ⟨hsouthShade,
    (valid.vertical_eq (quarterEast east) qy
      (CycleOn.east_path cycle hsouth hnorth)).symm.trans hsouthShade⟩


end RedShadeCycles

namespace RedShadeGraph

open QuarterGeometry RedShadePaths

/-- Shade at the indicated edge port. -/
@[expose] def value (stateGrid : Nat → Nat → RedShades.State) (port : Port) :
    Option RedShades.Shade :=
  match port.side with
  | .west => (stateGrid port.x port.y).west
  | .east => (stateGrid port.x port.y).east
  | .south => (stateGrid port.x port.y).south
  | .north => (stateGrid port.x port.y).north

/-- A locally allowed shade state has exactly the red-graph incidence at each port. -/
theorem value_isSome_eq_portPresent_of_allowed
    {grid : Nat → Nat → Index} {shadeGrid : Nat → Nat → RedShades.State}
    (port : Port)
    (allowed : RedShades.locallyAllowed
      ⟨grid (port.x / 2) (port.y / 2), quadrantAt port.x port.y⟩
      (shadeGrid port.x port.y) = true) :
    (value shadeGrid port).isSome = portPresent grid port := by
  rcases port with ⟨x, y, side⟩
  simp only [RedShades.locallyAllowed, RedShades.allowedFor, Bool.and_eq_true,
    decide_eq_true_eq] at allowed
  rcases allowed.1.1.1.1.1.1.1 with ⟨⟨⟨hw, he⟩, hs⟩, hn⟩
  cases side
  · exact hw
  · exact he
  · exact hs
  · exact hn

/-- Allowed shade states have exactly the red-graph incidence. -/
theorem value_isSome_eq_portPresent
    {grid : Nat → Nat → Index} {shadeGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid grid shadeGrid) (port : Port) :
    (value shadeGrid port).isSome = portPresent grid port :=
  value_isSome_eq_portPresent_of_allowed port (valid.allowed port.x port.y)

/-- Even parity means equal shades; odd parity means opposite present shades. -/
@[expose] def Related (parity : Bool) (first second : Option RedShades.Shade) : Prop :=
  match parity with
  | false => first = second
  | true => ∃ shade, first = some shade ∧ second = some shade.opposite

@[simp] theorem related_false_iff {first second : Option RedShades.Shade} :
    Related false first second ↔ first = second := Iff.rfl

@[simp] theorem related_true_iff {first second : Option RedShades.Shade} :
    Related true first second ↔
      ∃ shade, first = some shade ∧ second = some shade.opposite := Iff.rfl

theorem Related.symm {parity : Bool} {first second : Option RedShades.Shade}
    (relation : Related parity first second) : Related parity second first := by
  cases parity
  · exact Eq.symm relation
  · rcases relation with ⟨shade, rfl, rfl⟩
    exact ⟨shade.opposite, rfl, by simp⟩

theorem Related.trans {first second third : Option RedShades.Shade}
    {firstParity secondParity : Bool}
    (firstRelation : Related firstParity first second)
    (secondRelation : Related secondParity second third) :
    Related (Bool.xor firstParity secondParity) first third := by
  cases firstParity <;> cases secondParity
  · exact Eq.trans firstRelation secondRelation
  · subst second
    exact secondRelation
  · subst second
    exact firstRelation
  · rcases firstRelation with ⟨firstShade, rfl, rfl⟩
    rcases secondRelation with ⟨secondShade, heq, hthird⟩
    simp only [Option.some.injEq] at heq
    subst secondShade
    simpa using Eq.symm hthird

private theorem related_true_of_ne_of_present
    {first second : Option RedShades.Shade}
    (hfirst : first.isSome = true) (hsecond : second.isSome = true)
    (hne : first ≠ second) : Related true first second := by
  rcases first with _ | first
  · simp at hfirst
  rcases second with _ | second
  · simp at hsecond
  refine ⟨first, rfl, congrArg some ?_⟩
  exact RedShades.Shade.eq_opposite_of_ne (by
    intro heq
    apply hne
    exact congrArg some heq)

private theorem Link.sound_on {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State} {region : Nat → Nat → Prop}
    (allowed : ∀ x y, region x y → RedShades.locallyAllowed
      ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩ (stateGrid x y) = true)
    (hmatch : ∀ x y, region x y → region (x + 1) y →
      (stateGrid x y).east = (stateGrid (x + 1) y).west)
    (vmatch : ∀ x y, region x y → region x (y + 1) →
      (stateGrid x y).north = (stateGrid x (y + 1)).south)
    {first second : Port} {parity : Bool} (link : Link indexGrid first second parity) :
    region first.x first.y → region second.x second.y →
      Related parity (value stateGrid first) (value stateGrid second) := by
  induction link with
  | horizontalMatch x y => exact hmatch x y
  | verticalMatch x y => exact vmatch x y
  | horizontal x y hpath =>
      exact fun h _ => RedShades.horizontal_eq_of_allowedFor (allowed x y h) hpath
  | vertical x y hpath =>
      exact fun h _ => RedShades.vertical_eq_of_allowedFor (allowed x y h) hpath
  | westNorth x y hwest hnorth =>
      exact fun h _ => RedShades.west_north_corner_eq_of_allowedFor (allowed x y h) hwest hnorth
  | westSouth x y hwest hsouth =>
      exact fun h _ => RedShades.west_south_corner_eq_of_allowedFor (allowed x y h) hwest hsouth
  | eastNorth x y heast hnorth =>
      exact fun h _ => RedShades.east_north_corner_eq_of_allowedFor (allowed x y h) heast hnorth
  | eastSouth x y heast hsouth =>
      exact fun h _ => RedShades.east_south_corner_eq_of_allowedFor (allowed x y h) heast hsouth
  | crossing x y hhorizontal hvertical =>
      intro h _
      apply related_true_of_ne_of_present
      · exact RedShades.west_present_of_allowedFor (allowed x y h) (by
          change hasWest (componentAt indexGrid x y) (quadrantAt x y) = true
          simp only [hasWest, hhorizontal, Bool.true_or])
      · exact RedShades.south_present_of_allowedFor (allowed x y h) (by
          change hasSouth (componentAt indexGrid x y) (quadrantAt x y) = true
          simp only [hasSouth, hvertical, Bool.true_or])
      · exact RedShades.crossing_opposite_of_allowedFor (allowed x y h) hhorizontal hvertical
  | symm link ih => exact fun hfirst hsecond => Related.symm (ih hsecond hfirst)

theorem Link.sound {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {first second : Port} {parity : Bool}
    (link : Link indexGrid first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) :=
  link.sound_on (region := fun _ _ => True)
    (fun x y _ => valid.allowed x y)
    (fun x y _ _ => valid.hmatch x y) (fun x y _ _ => valid.vmatch x y) trivial trivial

/-- A parity-consistent assignment to all red-graph ports.  Incidence is part
of the data because match links exist independently of whether the shared
edge carries a red wire. -/
structure ValidPortLabeling (indexGrid : Nat → Nat → Index) where
  /-- Optional shade at each quarter-edge port. -/
  label : Port → Option RedShades.Shade
  /-- Labels are present exactly on the geometrically prescribed red edges. -/
  present : ∀ port, (label port).isSome = portPresent indexGrid port
  /-- Every local connection respects its crossing parity. -/
  related : ∀ {first second parity}, Link indexGrid first second parity →
    Related parity (label first) (label second)

namespace ValidPortLabeling

/-- Regroup four labeled ports into the corresponding quarter shade state. -/
@[expose] def stateGrid {indexGrid : Nat → Nat → Index}
    (labeling : ValidPortLabeling indexGrid) :
    Nat → Nat → RedShades.State := fun x y =>
  { west := labeling.label ⟨x, y, .west⟩
    east := labeling.label ⟨x, y, .east⟩
    south := labeling.label ⟨x, y, .south⟩
    north := labeling.label ⟨x, y, .north⟩ }

private theorem ne_of_related_true
    {first second : Option RedShades.Shade}
    (related : Related true first second) : first ≠ second := by
  rcases related with ⟨shade, rfl, rfl⟩
  intro equal
  simp only [Option.some.injEq] at equal
  cases shade <;> contradiction

/-- Port incidence and parity-link consistency are exactly the local shade
tile and edge-matching rules. -/
theorem validShadeGrid {indexGrid : Nat → Nat → Index}
    (labeling : ValidPortLabeling indexGrid) :
    ValidShadeGrid indexGrid labeling.stateGrid := by
  constructor
  · intro x y
    simp only [RedShades.locallyAllowed]
    apply RedShades.allowedFor_of
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .west⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .east⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .south⟩
    · simpa only [stateGrid, portPresent, componentAt] using
        labeling.present ⟨x, y, .north⟩
    · intro hpath
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .east⟩
      exact labeling.related (Link.horizontal x y hpath)
    · intro hpath
      change labeling.label ⟨x, y, .south⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.vertical x y hpath)
    · intro heast hsouth
      change labeling.label ⟨x, y, .east⟩ =
        labeling.label ⟨x, y, .south⟩
      exact labeling.related (Link.eastSouth x y heast hsouth)
    · intro heast hnorth
      change labeling.label ⟨x, y, .east⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.eastNorth x y heast hnorth)
    · intro hwest hsouth
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .south⟩
      exact labeling.related (Link.westSouth x y hwest hsouth)
    · intro hwest hnorth
      change labeling.label ⟨x, y, .west⟩ =
        labeling.label ⟨x, y, .north⟩
      exact labeling.related (Link.westNorth x y hwest hnorth)
    · intro hhorizontal hvertical
      change labeling.label ⟨x, y, .west⟩ ≠
        labeling.label ⟨x, y, .south⟩
      exact ne_of_related_true
        (labeling.related (Link.crossing x y hhorizontal hvertical))
  · intro x y
    change labeling.label ⟨x, y, .east⟩ =
      labeling.label ⟨x + 1, y, .west⟩
    exact labeling.related (Link.horizontalMatch x y)
  · intro x y
    change labeling.label ⟨x, y, .north⟩ =
      labeling.label ⟨x, y + 1, .south⟩
    exact labeling.related (Link.verticalMatch x y)

end ValidPortLabeling

theorem Path.sound {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid)
    {first second : Port} {parity : Bool}
    (path : Path indexGrid first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) := by
  induction path with
  | refl port => rfl
  | ofLink link => exact link.sound valid
  | trans firstPath secondPath firstIH secondIH =>
      exact Related.trans firstIH secondIH


end RedShadeGraph
namespace RedShadeGraphBoundedPath

open RedShadeGraph QuarterGeometry

/-- A bounded red-wire path relates its endpoint shades using only local validity and
matching within the bounding rectangle. -/
theorem BoundedPath.sound {indexGrid : Nat → Nat → Index}
    {stateGrid : Nat → Nat → RedShades.State} {width height : Nat}
    (allowed : ∀ x y, x < width → y < height → RedShades.locallyAllowed
      ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩ (stateGrid x y) = true)
    (hmatch : ∀ x y, x + 1 < width → y < height →
      (stateGrid x y).east = (stateGrid (x + 1) y).west)
    (vmatch : ∀ x y, x < width → y + 1 < height →
      (stateGrid x y).north = (stateGrid x (y + 1)).south)
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    Related parity (value stateGrid first) (value stateGrid second) := by
  induction path with
  | refl port bounds => rfl
  | ofLink link first second =>
      exact link.sound_on (region := fun x y => x < width ∧ y < height)
        (fun x y h => allowed x y h.1 h.2)
        (fun x y _ h => hmatch x y h.1 h.2)
        (fun x y _ h => vmatch x y h.1 h.2) first second
  | trans firstPath secondPath firstIH secondIH => exact Related.trans firstIH secondIH

end RedShadeGraphBoundedPath
namespace Signals
open QuarterGeometry

@[expose] public section
/-- Which side of a vertical red border is the board interior. -/
inductive HorizontalInterior where
  | west
  | east
deriving DecidableEq, Repr
end

@[expose] public section
/-- Which side of a horizontal red border is the board interior. -/
inductive VerticalInterior where
  | south
  | north
deriving DecidableEq, Repr
end

/-- Vertical red boundary through a quarter, if any. -/
@[expose] def verticalInterior? (component : Thick) (quadrant : Quadrant) :
    Option HorizontalInterior :=
  match component, quadrant with
  | .a, .southeast | .b, .northeast => some .east
  | .c, .northwest | .d, .southwest => some .west
  | component, quadrant =>
      if redVerticalAt component quadrant.xBit then
        if quadrant.xBit then some .east else some .west
      else none

/-- Horizontal red boundary through a quarter, if any. -/
@[expose] def horizontalInterior? (component : Thick) (quadrant : Quadrant) :
    Option VerticalInterior :=
  match component, quadrant with
  | .a, .southeast | .d, .southwest => some .south
  | .b, .northeast | .c, .northwest => some .north
  | component, quadrant =>
      if redHorizontalAt component quadrant.yBit then
        if quadrant.yBit then some .north else some .south
      else none

end Signals

namespace ShadedSignals

/-- Shade of the vertical red path through a quarter, if present. -/
@[expose] def verticalShade? (state : RedShades.State) : Option RedShades.Shade :=
  match state.south with
  | some shade => some shade
  | none => state.north

/-- Shade of the horizontal red path through a quarter, if present. -/
@[expose] def horizontalShade? (state : RedShades.State) : Option RedShades.Shade :=
  match state.west with
  | some shade => some shade
  | none => state.east

/-- Selected vertical-border rule with the component made explicit. -/
@[expose] def selectedVerticalFor (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) : Option Signals.HorizontalInterior :=
  if verticalShade? state = some .light then
    Signals.verticalInterior? component quadrant
  else none

/-- Selected horizontal-border rule with the component made explicit. -/
@[expose] def selectedHorizontalFor (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) : Option Signals.VerticalInterior :=
  if horizontalShade? state = some .light then
    Signals.horizontalInterior? component quadrant
  else none

end ShadedSignals


namespace RedShadeGraphCoarsening
open QuarterGeometry RedCycles RedShadePaths RedShadeCycles RedShadeGraph
  RedShadeGraphRefinement

/-- Pull the four shades of a coarse quarter from its refined boundary ports. -/
@[expose] def coarsen (fine : Nat → Nat → RedShades.State) (x y : Nat) : RedShades.State :=
  { west := value fine (refinedPort ⟨x, y, .west⟩)
    east := value fine (refinedPort ⟨x, y, .east⟩)
    south := value fine (refinedPort ⟨x, y, .south⟩)
    north := value fine (refinedPort ⟨x, y, .north⟩) }

/-- A coarsened port reads its corresponding refined port. -/
@[simp] theorem value_coarsen (fine : Nat → Nat → RedShades.State) (port : Port) :
    value (coarsen fine) port = value fine (refinedPort port) := by
  cases port with
  | mk x y side => cases side <;> rfl

/-- Coarsening a valid twice-substituted assignment preserves all shade rules and matches. -/
theorem valid {grid : Nat → Nat → Index} {fine : Nat → Nat → RedShades.State}
    (hfine : ValidShadeGrid (iterateRefine 2 grid) fine) :
    ValidShadeGrid grid (coarsen fine) := by
  let labeling : ValidPortLabeling grid :=
    { label := fun port => value fine (refinedPort port)
      present := fun port =>
        (value_isSome_eq_portPresent hfine _).trans (refinedPort_present grid port)
      related := fun link => (link_refine link).sound hfine }
  exact labeling.validShadeGrid

private theorem coarse_value {grid : Nat → Nat → Index}
    {fine : Nat → Nat → RedShades.State}
    (hfine : ValidShadeGrid (iterateRefine 2 grid) fine)
    (port : Port) (live : portPresent grid port = true)
    {shade : RedShades.Shade} (start : value fine (sparsePort port) = some shade) :
    value (coarsen fine) port = some shade := by
  have relation : value fine (sparsePort port) = value fine (refinedPort port) :=
    (livePortPath grid port live).sound hfine
  rw [value_coarsen]
  exact relation.symm.trans start

/-- A uniformly shaded refined cycle induces the same shade on its coarse ancestor. -/
theorem cycleShade {grid : Nat → Nat → Index} {fine : Nat → Nat → RedShades.State}
    {west east south north : Nat} {shade : RedShades.Shade}
    (hfine : ValidShadeGrid (iterateRefine 2 grid) fine)
    (cycle : OrientedRedCycles.CycleOn grid west east south north)
    (shaded : CycleShade fine (4 * west) (4 * east) (4 * south) (4 * north) shade) :
    CycleShade (coarsen fine) west east south north shade := by
  have apply_port := coarse_value hfine
  constructor
  · apply apply_port ⟨quarterWest west, quarterSouth south, .east⟩
    · have corner := RedShadeCycles.CycleOn.southwest_corner cycle
      simp [portPresent, hasEast, corner.1]
    · simpa [value, sparsePort, sparseCoordinate, quarterWest, quarterSouth,
        Nat.add_div, ← Nat.mul_assoc] using shaded.southwest
  · apply apply_port ⟨quarterEast east, quarterSouth south, .west⟩
    · have corner := RedShadeCycles.CycleOn.southeast_corner cycle
      simp [portPresent, hasWest, corner.1]
    · simpa [value, sparsePort, sparseCoordinate, quarterEast, quarterSouth,
        Nat.add_div, ← Nat.mul_assoc] using shaded.southeast
  · apply apply_port ⟨quarterEast east, quarterNorth north, .west⟩
    · have corner := RedShadeCycles.CycleOn.northeast_corner cycle
      simp [portPresent, hasWest, corner.1]
    · simpa [value, sparsePort, sparseCoordinate, quarterEast, quarterNorth,
        ← Nat.mul_assoc] using shaded.northeast
  · apply apply_port ⟨quarterWest west, quarterNorth north, .east⟩
    · have corner := RedShadeCycles.CycleOn.northwest_corner cycle
      simp [portPresent, hasEast, corner.1]
    · simpa [value, sparsePort, sparseCoordinate, quarterWest, quarterNorth,
        Nat.add_div, ← Nat.mul_assoc] using shaded.northwest

end RedShadeGraphCoarsening

end Cslib.WangTile.Robinson
