/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Routing

/-! Ordinary-module clients of routing: actual addressed squares, extraction from a constant
corner grid, and an absent-seed example separating realization from forcing. -/

-- These are local regression examples, with no test-only public API.
set_option linter.privateModule false

open Cslib Cslib.WangTile

private def zeroTile : WangTile := ⟨0, 0, 0, 0⟩

private def uniformScaffold (role : RouteRole) : RoutedScaffold where
  tiles := [zeroTile]
  role := fun _ => role
  role_primrec := Primrec.const _

private def uniformPlane (role : RouteRole) : Plane (uniformScaffold role).tiles where
  tile := fun _ _ => zeroTile
  mem := fun _ _ => List.mem_cons_self
  horizontal := fun _ _ => rfl
  vertical := fun _ _ => rfl

private def activeAddressing (n : ℕ) : AddressedSquare (uniformScaffold .active) n where
  base := {
    tile := fun _ _ => zeroTile
    mem := fun _ _ => List.mem_cons_self
    horizontal := fun _ _ _ => rfl
    vertical := fun _ _ _ => rfl }
  point := fun i j => (i.val, j.val)
  horizontalSource := fun _ _ => (0, 0)
  verticalSource := fun _ _ => (0, 0)
  corner_zero := fun _ _ h => RouteRole.noConfusion h
  hstep := fun _ _ _ _ _ => by simp [uniformScaffold, RouteRole.horizontalOutgoing]
  vstep := fun _ _ _ _ _ => by simp [uniformScaffold, RouteRole.verticalOutgoing]

/-- Full crossing grids realize any pointed plane, without forcing its seed to occur. -/
example : Realizes (uniformScaffold .active) :=
  realizes_of_addressedSquares fun n => ⟨n, le_rfl, ⟨activeAddressing n⟩⟩

private def cornerGrid (n : ℕ) :
    RoutedGrid (uniformScaffold .corner) (uniformPlane .corner) n where
  column i := i.val
  row j := j.val
  column_strictMono := fun i j h => by
    change (i.val : ℤ) < j.val
    have : i.val < j.val := h
    omega
  row_strictMono := fun i j h => by
    change (i.val : ℤ) < j.val
    have : i.val < j.val := h
    omega
  crossing := fun _ _ => Or.inr rfl
  corner := rfl
  horizontal := fun _ _ _ h₁ h₂ => by simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂; omega
  vertical := fun _ _ _ h₁ h₂ => by simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂; omega

/-- At a seeded monochrome crossing every finite grid extracts a square with that seed. -/
example (n : ℕ) : Nonempty (SeededSquare ⟨[zeroTile], zeroTile⟩ n) := by
  let P : RoutedPlane (uniformScaffold .corner) ⟨[zeroTile], zeroTile⟩ := {
    base := uniformPlane .corner
    payload := fun _ _ => zeroTile
    allowed := fun _ _ => mem_routedPayloads.mpr ⟨List.mem_cons_self, rfl⟩
    horizontal := fun _ _ => rfl
    vertical := fun _ _ => rfl }
  exact ⟨(cornerGrid n).seededSquare P⟩

/-- Realization alone does not remove a seed: an active scaffold accepts a palette whose seed
is absent, so its forward forcing obligation fails. -/
example : ¬ Forces (uniformScaffold .active) := by
  intro forces
  let I : SeededInstance := ⟨[zeroTile], ⟨1, 1, 1, 1⟩⟩
  have combined : TilesPlane (combine (uniformScaffold .active) I) := by
    refine ⟨fun _ _ => layer zeroTile zeroTile, fun _ _ => ⟨?_, rfl, rfl⟩⟩
    exact mem_combine.mpr ⟨zeroTile, List.mem_cons_self, zeroTile,
      mem_routedPayloads.mpr List.mem_cons_self, rfl⟩
  obtain ⟨square⟩ := forces I combined 0
  have hm := square.mem 0 0
  rw [square.corner] at hm
  have he : I.seed = zeroTile := List.mem_singleton.mp hm
  have ht := congrArg WangTile.top he
  simp [I, zeroTile] at ht
