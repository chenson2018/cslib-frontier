/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Canonical.Patches

/-! Ordinary-import client for canonical boundary signals. The index-zero marker in the
smallest canonical patch is blocked by its outer borders; the marker alone is not a corner. -/

set_option linter.privateModule false

open Cslib.WangTile Cslib.WangTile.Robinson Cslib.WangTile.Robinson.Canonical

private theorem seed_row (x y : ℕ) :
    rowInterior 0 seedNode x y = outerBorder (x % 2) (y % 2) := by
  have h := (BorderState.observations BorderState.seed_admissible
    ⟨x % 2, Nat.mod_lt _ (by decide)⟩ ⟨y % 2, Nat.mod_lt _ (by decide)⟩).1
  simpa [rowInterior, supertileNodeGrid, BorderState.seed] using h.symm

private theorem seed_column (x y : ℕ) :
    columnInterior 0 seedNode x y = outerBorder (y % 2) (x % 2) := by
  have h := (BorderState.observations BorderState.seed_admissible
    ⟨x % 2, Nat.mod_lt _ (by decide)⟩ ⟨y % 2, Nat.mod_lt _ (by decide)⟩).2
  simpa [columnInterior, supertileNodeGrid, BorderState.seed] using h.symm

example : scaffold.role ((canonicalPatch 0 seedNode).tile
    ⟨1, by simp [side]⟩ ⟨1, by simp [side]⟩) = .inactive := by
  rw [scaffold_role]
  change ShadedSignals.routeRole (ShadedSignals.tile (site 0 seedNode 1 1)) = _
  rw [ShadedSignals.routeRole_tile]
  simp [site, side, intervalEdge, previousInterior, nextInterior, seed_row, seed_column,
    outerBorder]

/-- A nonzero child retains the certified selected-border halo. -/
example : (BorderState.seed.refine 2 3).Admissible :=
  BorderState.refine_admissible BorderState.seed_admissible 2 3

/-- Two neighboring children remain compatible across their own expanded block boundary. -/
example :
    HCompatible ((seedNode.child (blockPosition 0 1)).child (blockPosition 3 2))
      ((seedNode.child (blockPosition 1 1)).child (blockPosition 0 2)) :=
  children_hCompatible_boundary (children_hCompatible_within seedNode 0 1) 2
