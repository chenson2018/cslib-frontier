/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.FreeGrid.Obstruction

/-!
# Filling a gap in a sparse free grid

An empty selected-border assignment makes every line free. Sorting the two sparse lines
at coordinates 5 and 9 must therefore produce adjacent lines. This tests the selection API;
the empty shade assignment is not asserted to be a valid Robinson shading.
-/

namespace Cslib.Tests.WangTile.FreeGrid
open Cslib.WangTile.Robinson
open FreeGrid ShadedPlaneSignalGrid RedShadeCycles

private def emptyShade : RedShades.State := ⟨none, none, none, none⟩

private theorem freeColumn (x : ℕ) :
    IsFreeColumn (fun _ _ => 0) (fun _ _ => emptyShade) 1 8 x := by
  intro y _ _
  simp [ShadedSignals.selectedHorizontalFor, ShadedSignals.horizontalShade?, emptyShade]

private theorem freeRow (y : ℕ) :
    IsFreeRow (fun _ _ => 0) (fun _ _ => emptyShade) 1 8 y := by
  intro x _ _
  simp [ShadedSignals.selectedVerticalFor, ShadedSignals.verticalShade?, emptyShade]

private def sparse (i : Fin 2) : ℕ := 5 + 4 * i.val

private theorem sparse_mono : StrictMono sparse := by
  intro i j hij
  simp only [sparse]
  have := hij
  omega

private noncomputable def filled : ConsecutiveMarkedFreeGrid
    (fun _ _ => 0) (fun _ _ => emptyShade) 1 8 1 8 1 :=
  ConsecutiveMarkedFreeGrid.ofSparse sparse sparse sparse_mono sparse_mono
    (fun i => ⟨by simp only [sparse, quarterWest]; omega,
      by simp only [sparse, quarterEast]; omega, freeColumn _⟩)
    (fun i => ⟨by simp only [sparse, quarterSouth]; omega,
      by simp only [sparse, quarterNorth]; omega, freeRow _⟩)
    (by decide)

/-- Sorting inserts all free lines before selecting the next crossing. -/
public theorem exists_adjacent_columns :
    ∃ g : ConsecutiveMarkedFreeGrid (fun _ _ => 0) (fun _ _ => ⟨none, none, none, none⟩)
      1 8 1 8 1, g.column 1 = g.column 0 + 1 := by
  refine ⟨filled, ?_⟩
  have increasing := filled.column_strictMono (show (0 : Fin 2) < 1 by decide)
  by_contra h
  have gap := filled.noFreeColumnBetween 0 (filled.column 0 + 1)
    (by simp) (by simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one] using
      (show filled.column 0 + 1 < filled.column 1 by omega))
  exact gap (freeColumn _)

end Cslib.Tests.WangTile.FreeGrid
