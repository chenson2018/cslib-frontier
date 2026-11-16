/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WangTile.Robinson.Hierarchy
import CslibFrontier.Computability.WangTile.Robinson.Recognizability
import Mathlib.Data.Fin.VecNotation

/-! Ordinary-import clients of the corrected Robinson hierarchy. The concrete four-row patch
checks that the recognition hypotheses are satisfiable. A matching two-by-two patch with no
parent guards the essential one-cell context of that theorem. -/

open Cslib.WangTile
open Cslib.WangTile.Robinson

private def neighborhood : Neighborhood where
  cell i j := (![![6, 67, 7, 66], ![20, 40, 28, 40],
    ![4, 64, 5, 62], ![15, 3, 18, 89]] : Fin 4 → Fin 4 → Index) j i
  horizontal := by decide
  vertical := by decide
  phase := by decide

example : ∃! p : Index,
    childBlock p 0 0 = 40 ∧ childBlock p 1 0 = 28 ∧
      childBlock p 0 1 = 64 ∧ childBlock p 1 1 = 5 :=
  existsUnique_centerParent neighborhood

example : childBlock 16 0 0 = 40 ∧ childBlock 16 1 0 = 28 ∧
    childBlock 16 0 1 = 64 ∧ childBlock 16 1 1 = 5 := by decide

-- These four tiles match, but their isolated block has no substitution parent.
example : (tile (components 0)).right = (tile (components 17)).left ∧
    (tile (components 57)).right = (tile (components 4)).left ∧
    (tile (components 0)).top = (tile (components 57)).bottom ∧
    (tile (components 17)).top = (tile (components 4)).bottom := by decide

example : ¬ ∃ p : Index,
    childBlock p 0 0 = 0 ∧ childBlock p 1 0 = 17 ∧
      childBlock p 0 1 = 57 ∧ childBlock p 1 1 = 4 := by decide

example : TilesPlane tileSet := tilesPlane_tileSet

-- The tower and recurrence apply to a concrete nonempty family of planes.
example : ∃ p : Plane, ∃ x y : ℤ, p.index x y = 103 := by
  obtain ⟨p⟩ := tilesPlane_iff_nonempty_plane.mp tilesPlane_tileSet
  have h := (tower p).every_tile 0 103
  exact ⟨p, by simpa only [(tower p).zero] using h⟩
