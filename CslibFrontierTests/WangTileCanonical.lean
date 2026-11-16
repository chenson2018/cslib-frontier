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

-- These regression examples intentionally add no public test API.
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
  change ShadedSite.routeRole (ShadedSite.tile (site 0 seedNode 1 1)) = _
  rw [ShadedSite.routeRole_tile]
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

private theorem parent_refine {fine : IndexPlane} (p : Parent fine)
    (a b : ℤ) (x y : ℕ) :
    refineIndexGrid (fun i j => p.coarse.index (a + i) (b + j)) x y =
      fine.index (p.offsetX.val + 2 * a + x) (p.offsetY.val + 2 * b + y) := by
  change childBlock (p.coarse.index (a + (x / 2 : ℕ)) (b + (y / 2 : ℕ)))
    ⟨x % 2, _⟩ ⟨y % 2, _⟩ = _
  rw [p.children]
  congr 1 <;> dsimp only <;> omega

/-- The coarsening premise holds on an actual infinite scaffold grid with a live red port. -/
example : ∃ (grid : ℕ → ℕ → Index) (fine : ℕ → ℕ → ShadeState),
    ValidShadeGrid (iterateRefine 2 grid) fine ∧
      (value fine cycleSource).isSome = true ∧ ValidShadeGrid grid (coarsen fine) := by
  obtain ⟨P⟩ := (nonempty_plane_iff _).mpr scaffold_tilesPlane
  let D := DecodedPlane.ofPlane P
  let R := QuarterPlane.regroup D.quarterPlane
  obtain ⟨p₁⟩ := nonempty_parent R.parent
  obtain ⟨p₂⟩ := nonempty_parent p₁.coarse
  let grid : ℕ → ℕ → Index := fun x y => p₂.coarse.index x y
  let a : ℤ := p₁.offsetX.val + 2 * p₂.offsetX.val
  let b : ℤ := p₁.offsetY.val + 2 * p₂.offsetY.val
  let fine := fun x y => (D.siteGrid R a b x y).shade
  have refined : iterateRefine 2 grid = fun (x y : ℕ) => R.parent.index (a + x) (b + y) := by
    have first : refineIndexGrid grid =
        fun (x y : ℕ) => p₁.coarse.index (p₂.offsetX.val + x) (p₂.offsetY.val + y) := by
      funext x y
      simpa [grid] using parent_refine p₂ 0 0 x y
    funext x y
    change refineIndexGrid (refineIndexGrid grid) x y = _
    rw [first]
    exact parent_refine p₁ p₂.offsetX.val p₂.offsetY.val x y
  have valid : ValidShadeGrid (iterateRefine 2 grid) fine := by
    rw [refined]
    exact (D.validGrid R a b).shadeValid
  have sourceLive : portPresent (fineGrid (grid 0 0)) cycleSource = true := by
    have south := (fixed_cycle (grid 0 0)).south_path (qx := 4) (by decide) (by decide)
    change hasHorizontal (componentAt (fineGrid (grid 0 0)) 4 3) (quadrantAt 4 3) = true
      at south
    change hasWest (componentAt (fineGrid (grid 0 0)) 4 3) (quadrantAt 4 3) = true
    simp only [hasWest, south, Bool.true_or]
  have live : portPresent (iterateRefine 2 grid) cycleSource = true := by
    have translated := (portPresent_two_block grid 0 0 cycleSource
      (by decide) (by decide)).symm.trans sourceLive
    simpa only [translatePort, Nat.mul_zero, Nat.zero_add] using translated
  exact ⟨grid, fine, valid, (value_isSome_eq_portPresent valid cycleSource).trans live,
    valid.coarsen⟩
