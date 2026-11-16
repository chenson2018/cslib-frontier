/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Compactness

/-!
# Wang tilings: checked instances

Empty palettes, a monochrome tile, incompatible horizontal edges, and an absent seed exercise
the actual matching predicates through ordinary module imports.
-/

namespace Cslib.Tests.WangTile

open Cslib.WangTile

example : ¬ TilesPlane [] := by
  rintro ⟨f, hf⟩
  simpa using (hf 0 0).1

/-- The tile with colour zero on every edge. -/
@[expose] public def monochrome : WangTile := ⟨0, 0, 0, 0⟩

/-- A single monochrome tile covers the plane. -/
public theorem monochrome_tiles : TilesPlane [monochrome] :=
  ⟨fun _ _ => monochrome, by simp [monochrome]⟩

example : ∀ n, Nonempty (Rectangle [monochrome] (n + 1) (n + 1)) :=
  (tilesPlane_iff_squares [monochrome]).mp monochrome_tiles

private def mismatch : WangTile := ⟨0, 0, 0, 1⟩

example : ¬ TilesPlane [mismatch] := by
  rintro ⟨f, hf⟩
  have h₀ : f 0 0 = mismatch := by simpa using (hf 0 0).1
  have h₁ : f 1 0 = mismatch := by simpa using (hf 1 0).1
  have he := (hf 0 0).2.1
  simp [h₀, h₁, mismatch] at he

example : ¬ TilesQuadrant ⟨[monochrome], mismatch⟩ := by
  rintro ⟨f, hseed, hf⟩
  have hm := (hf 0 0).1
  rw [hseed] at hm
  simp [monochrome, mismatch] at hm

example : TilesQuadrant ⟨[monochrome], monochrome⟩ := by
  apply (tilesQuadrant_iff_seededSquares _).mpr
  intro n
  exact ⟨{
    tile := fun _ _ => monochrome
    mem := by simp
    horizontal := by simp [monochrome]
    vertical := by simp [monochrome]
    corner := rfl }⟩

end Cslib.Tests.WangTile
