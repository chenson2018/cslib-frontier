/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Realization

/-! Ordinary-module clients of canonical carrier geometry and pointed-payload realization.
The level-two patch contains an actual unblocked corner at quarter coordinate `(9, 9)`.
A monochrome payload supplies a nonempty pointed plane to the unconditional realization theorem. -/

-- These regression examples intentionally add no public test API.
set_option linter.privateModule false

open Cslib.WangTile Cslib.WangTile.Robinson
open Cslib.WangTile.Robinson.Canonical Cslib.WangTile.Robinson.Carrier

example : rowInterior 2 seedNode 5 6 = some true := by
  rw [rowInterior_seed_eq_selectedBorder 2 5 6 (by decide) (by decide)]
  decide +kernel

example : rowInterior 2 seedNode 12 6 = some false := by
  rw [rowInterior_seed_eq_selectedBorder 2 12 6 (by decide) (by decide)]
  decide +kernel

example : rowInterior 2 seedNode 6 6 = none := by
  rw [rowInterior_seed_eq_selectedBorder 2 6 6 (by decide) (by decide)]
  decide +kernel

example : columnInterior 2 seedNode 6 5 = some true := by
  rw [columnInterior_seed_eq_selectedBorder 2 6 5 (by decide) (by decide)]
  decide +kernel

private theorem canonical_corner :
    scaffold.role ((canonicalAddressing 2).base.tile ⟨9, by decide⟩ ⟨9, by decide⟩) = .corner := by
  change scaffold.role ((canonicalPatch 2 seedNode).tile ⟨9, by decide⟩ ⟨9, by decide⟩) = .corner
  rw [scaffold_role]
  change ShadedSite.routeRole (ShadedSite.tile (site 2 seedNode 9 9)) = .corner
  rw [ShadedSite.routeRole_tile]
  decide +kernel

example : (canonicalAddressing 2).point ⟨9, by decide⟩ ⟨9, by decide⟩ = (0, 0) :=
  (canonicalAddressing 2).corner_zero _ _ canonical_corner

example : TilesPlane (combine scaffold ⟨[⟨3, 3, 3, 3⟩], ⟨3, 3, 3, 3⟩⟩) := by
  apply scaffold_realizes
  refine ⟨fun _ _ => ⟨3, 3, 3, 3⟩, rfl, ?_⟩
  intro x y
  exact ⟨by simp, rfl, rfl⟩
