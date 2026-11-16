/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.WangTile.Robinson.Shading.Geometry

/-! Ordinary-module clients of quarter subdivision, parity paths and red shading. -/

-- This client contains private fixtures and anonymous examples, not an exported API.
set_option linter.privateModule false

open Cslib.WangTile.Robinson
open QuarterGeometry RedCycles OrientedRedCycles RedShades RedShadePaths RedShadeGraph

/-- A tile with two straight red lanes crossing in its northeast quarter. -/
private def crossingGrid (_ _ : Nat) : Index := 13

/-- Light horizontal lanes and dark vertical lanes form a matching shade assignment. -/
private def crossingShades (x y : Nat) : State :=
  { west := if y % 2 == 1 then some .light else none
    east := if y % 2 == 1 then some .light else none
    south := if x % 2 == 1 then some .dark else none
    north := if x % 2 == 1 then some .dark else none }

private theorem crossing_valid : ValidShadeGrid crossingGrid crossingShades := by
  constructor
  · intro x y
    cases hx : (x % 2 == 1) <;> cases hy : (y % 2 == 1) <;>
      simp [crossingGrid, crossingShades, locallyAllowed, allowedFor, components,
        quadrantAt, Quadrant.ofBits, hasWest, hasEast, hasSouth, hasNorth,
        hasHorizontal, hasVertical, cornerWest, cornerEast, cornerSouth, cornerNorth,
        redHorizontalAt, redVerticalAt, containsLine, Quadrant.xBit, Quadrant.yBit, hx, hy]
  · intro x y; rfl
  · intro x y; rfl

/-- A crossing reverses shade even in an infinite matching grid. -/
example : Related true (some Shade.light) (some Shade.dark) := by
  have path : Path crossingGrid ⟨1, 1, .west⟩ ⟨1, 1, .south⟩ true :=
    .ofLink (.crossing 1 1 (by decide) (by decide))
  exact path.sound crossing_valid

/-- The same crossing remains an odd path after two substitutions. -/
example : Path (iterateRefine 2 crossingGrid)
    (RedShadeGraphRefinement.refinedPort ⟨1, 1, .west⟩)
    (RedShadeGraphRefinement.refinedPort ⟨1, 1, .south⟩) true := by
  apply RedShadeGraphRefinement.path_refine
  exact .ofLink (.crossing 1 1 (by decide) (by decide))

/-- Two crossings cancel their parity; every intermediate port remains in the box. -/
example : RedShadeGraphBoundedPath.BoundedPath crossingGrid 2 2
    ⟨1, 1, .west⟩ ⟨1, 1, .west⟩ false := by
  have link : Link crossingGrid ⟨1, 1, .west⟩ ⟨1, 1, .south⟩ true :=
    .crossing 1 1 (by decide) (by decide)
  exact .trans (.ofLink link ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)
    (.ofLink link.symm ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)

/-- Equal shades at an occupied crossing violate the local rule. -/
example : allowedFor .e .northeast ⟨some .light, some .light, some .light, some .light⟩ =
    false := by decide

/-- Combined signal certificates can decide actual shade states through ordinary imports. -/
example : (⟨some .light, none, none, none⟩ : State) ≠ ⟨some .dark, none, none, none⟩ := by
  decide

/-- Finite equality and ordinary quarter encoding are visible through ordinary imports. -/
example : (⟨1, 1, .west⟩ : Port) ≠ ⟨1, 1, .east⟩ := by decide

example : (TileSubdivision.subdivideTileAt ⟨1, 2, 3, 4⟩ .southwest).right =
    (TileSubdivision.subdivideTileAt ⟨1, 2, 3, 4⟩ .southeast).left := by rfl

/-- Exact macro-edge colours still distinguish incompatible neighboring quarters. -/
example : (TileSubdivision.subdivideTileAt ⟨1, 2, 3, 4⟩ .southeast).right ≠
    (TileSubdivision.subdivideTileAt ⟨1, 2, 5, 4⟩ .southwest).left := by decide

/-- The same oriented board survives arbitrarily many further substitutions. -/
example (n : Nat) : CycleOn
    (iterateRefine n (iterateRefine 2 (fun _ _ => 103)))
    (2 ^ n) (3 * 2 ^ n) (2 ^ n) (3 * 2 ^ n) := by
  simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm] using (fixed_cycle 103).iterateRefine n

/-! A periodic light-square shade grid satisfies all geometry premises together.
This does not claim that its tile indices form a matching Robinson plane. -/

namespace Cslib.WangTile.Robinson.Tests

open QuarterGeometry RedShadePaths RedShadeCycles OrientedRedCycles

private def cornerGrid (x y : Nat) : Index :=
  if y % 2 = 0 then (if x % 2 = 0 then 0 else 1)
  else (if x % 2 = 0 then 2 else 3)

private def cornerShades (x y : Nat) : RedShades.State :=
  match x % 4, y % 4 with
  | 1, 1 => ⟨none, some .light, none, some .light⟩
  | 2, 1 => ⟨some .light, none, none, some .light⟩
  | 1, 2 => ⟨none, some .light, some .light, none⟩
  | 2, 2 => ⟨some .light, none, some .light, none⟩
  | _, _ => ⟨none, none, none, none⟩

private theorem cornerShades_valid : ValidShadeGrid cornerGrid cornerShades where
  allowed x y := by
    have finite : ∀ x y : Fin 4,
        RedShades.locallyAllowed
          ⟨cornerGrid (x.val / 2) (y.val / 2), quadrantAt x.val y.val⟩
          (cornerShades x.val y.val) = true := by decide
    have hx : ((x % 4) / 2) % 2 = (x / 2) % 2 := by omega
    have hy : ((y % 4) / 2) % 2 = (y / 2) % 2 := by omega
    have hx' : (x % 4) % 2 = x % 2 := by omega
    have hy' : (y % 4) % 2 = y % 2 := by omega
    simpa only [cornerGrid, cornerShades, quadrantAt, Nat.mod_mod, hx, hy, hx', hy'] using
      finite ⟨x % 4, Nat.mod_lt _ (by decide)⟩ ⟨y % 4, Nat.mod_lt _ (by decide)⟩
  hmatch x y := by
    have finite : ∀ x y : Fin 4,
        (cornerShades x.val y.val).east = (cornerShades (x.val + 1) y.val).west := by
      decide
    simpa [cornerShades, Nat.add_mod] using
      finite ⟨x % 4, Nat.mod_lt _ (by decide)⟩ ⟨y % 4, Nat.mod_lt _ (by decide)⟩
  vmatch x y := by
    have finite : ∀ x y : Fin 4,
        (cornerShades x.val y.val).north = (cornerShades x.val (y.val + 1)).south := by
      decide
    simpa [cornerShades, Nat.add_mod] using
      finite ⟨x % 4, Nat.mod_lt _ (by decide)⟩ ⟨y % 4, Nat.mod_lt _ (by decide)⟩

private theorem cornerCycle : CycleOn cornerGrid 0 1 0 1 where
  west_lt_east := by decide
  south_lt_north := by decide
  southwest := by decide
  southeast := by decide
  northwest := by decide
  northeast := by decide
  southLane := by intros; omega
  northLane := by intros; omega
  westLane := by intros; omega
  eastLane := by intros; omega

private theorem cornerCycle_light : CycleShade cornerShades 0 1 0 1 .light := by
  constructor <;> decide

example : ∃ (grid : Nat → Nat → Index) (shades : Nat → Nat → RedShades.State),
    ValidShadeGrid grid shades ∧ CycleOn grid 0 1 0 1 ∧
      CycleShade shades 0 1 0 1 .light :=
  ⟨cornerGrid, cornerShades, cornerShades_valid, cornerCycle, cornerCycle_light⟩

example : ShadedObstructionGeometry.Geometry cornerGrid cornerShades 0 1 0 1 :=
  OrientedLightGeometry.CycleShade.geometry cornerCycle_light cornerCycle cornerShades_valid

end Cslib.WangTile.Robinson.Tests
