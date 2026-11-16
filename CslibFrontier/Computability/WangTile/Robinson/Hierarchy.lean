/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Tiles
import CslibFrontier.Computability.WangTile.Robinson.Recognizability
import CslibFrontier.Computability.WangTile.Compactness
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FinCases

/-!
# The corrected Robinson substitution hierarchy

The thin layer fixes a parity class of southwest child corners. Local recognizability recovers
one parent at every such corner, and reflection of matching along substituted boundaries makes
the recovered parents a matching plane. Repeating this construction gives a tower. Every tile
occurs at every level, and finite iterated substitution patches establish nonemptiness by
compactness.

## Main definitions

* `Plane`: an indexed matching plane over the corrected 104-tile alphabet.
* `Parent`: a matching substitution parent, with its parity alignment.
* `Tower`: a sequence of substitution parents above a prescribed plane.

## Main results

* `nonempty_parent`: every matching plane has a matching substitution parent.
* `tower`: every matching plane admits a parent tower.
* `Tower.every_tile`: every tile type occurs at every level of any such tower.
* `tilesPlane_tileSet`: the concrete corrected palette tiles the plane.

## References

The substitution hierarchy is the matching and recognition construction of
[JeandelVanier2020], §3.2, Proposition 8, for the corrected 104-tile variant.
Derived from the hierarchy in
[lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3/LeanWang/Robinson/Closed104),
revision `64268a3`. The finite-patch nonemptiness proof and the factorization of the recurrence
certificate through tile 0 are original reorganizations of the substitution argument.
-/

public section

namespace Cslib.WangTile.Robinson

/-- A matching plane indexed by the corrected Robinson alphabet. -/
structure Plane where
  /-- The corrected tile index at an integer lattice point. -/
  index : ℤ → ℤ → Index
  /-- Horizontal neighbours have equal edge colours. -/
  horizontal : ∀ x y, (tile (components (index x y))).right =
    (tile (components (index (x + 1) y))).left
  /-- Vertical neighbours have equal edge colours. -/
  vertical : ∀ x y, (tile (components (index x y))).top =
    (tile (components (index x (y + 1)))).bottom

/-- Indexing by the finite alphabet gives precisely tilings by the concrete palette. -/
theorem tilesPlane_iff_nonempty_plane : TilesPlane tileSet ↔ Nonempty Plane := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    have hm : ∀ x y, ∃ p : Index, tile (components p) = f x y :=
      fun x y => mem_tileSet.mp (hf x y).1
    choose p hp using hm
    exact ⟨⟨p, by simpa only [hp] using fun x y => (hf x y).2.1,
      by simpa only [hp] using fun x y => (hf x y).2.2⟩⟩
  · rintro ⟨p⟩
    exact ⟨fun x y => tile (components (p.index x y)), fun x y =>
      ⟨tile_components_mem _, p.horizontal x y, p.vertical x y⟩⟩

/-- A matching parent of a fine plane, including the alignment of its child blocks. -/
structure Parent (fine : Plane) where
  /-- The matching coarse plane. -/
  coarse : Plane
  /-- Horizontal coordinate of the southwest child of the coarse origin. -/
  offsetX : Fin 2
  /-- Vertical coordinate of the southwest child of the coarse origin. -/
  offsetY : Fin 2
  /-- Substitution reproduces all four children at every coarse lattice point. -/
  children : ∀ (x y : ℤ) (i j : Fin 2), childBlock (coarse.index x y) i j =
    fine.index ((offsetX.val : ℤ) + 2 * x + i.val) ((offsetY.val : ℤ) + 2 * y + j.val)

private theorem thin_even (p : Plane) (x y u v : ℤ) :
    (components (p.index (x + 2 * u) (y + 2 * v))).thin =
      (components (p.index x y)).thin := by
  have east (a b : ℤ) : (components (p.index (a + 2) b)).thin =
      (components (p.index a b)).thin := by
    have h := thin_east (p.horizontal (a + 1) b)
    rw [thin_east (p.horizontal a b)] at h
    simpa only [add_assoc, Int.reduceAdd, phaseEast_involutive] using h
  have north (a b : ℤ) : (components (p.index a (b + 2))).thin =
      (components (p.index a b)).thin := by
    have h := thin_north (p.vertical a (b + 1))
    rw [thin_north (p.vertical a b)] at h
    simpa only [add_assoc, Int.reduceAdd, phaseNorth_involutive] using h
  have hx : Function.Periodic
      (fun a : ℤ => (components (p.index (x + a) (y + 2 * v))).thin) 2 := by
    intro a
    simpa only [← add_assoc] using east (x + a) (y + 2 * v)
  have hy : Function.Periodic (fun b : ℤ => (components (p.index x (y + b))).thin) 2 := by
    intro b
    simpa only [← add_assoc] using north x (y + b)
  calc
    _ = (components (p.index x (y + 2 * v))).thin := by
      simpa only [Int.cast_id, mul_comm, add_zero] using hx.int_mul_eq u
    _ = (components (p.index x y)).thin := by
      simpa only [Int.cast_id, mul_comm, add_zero] using hy.int_mul_eq v

private theorem exists_phase_origin (p : Plane) :
    ∃ x y : Fin 2, (components (p.index x.val y.val)).thin = .a := by
  have he := thin_east (p.horizontal 0 0)
  have hn := thin_north (p.vertical 0 0)
  have hen := thin_north (p.vertical 1 0)
  cases h : (components (p.index 0 0)).thin with
  | a => exact ⟨0, 0, h⟩
  | b =>
    have he' : (components (p.index 1 0)).thin = .d := by
      simpa [h, phaseEast] using he
    exact ⟨1, 1, by simpa [he', phaseNorth] using hen⟩
  | c => exact ⟨1, 0, by simpa [h, phaseEast] using he⟩
  | d => exact ⟨0, 1, by simpa [h, phaseNorth] using hn⟩

private def neighborhood (p : Plane) (x y : ℤ)
    (hphase : (components (p.index x y)).thin = .a) : Neighborhood where
  cell i j := p.index (x + i.val - 1) (y + j.val - 1)
  horizontal i j := by
    have hx : x + (i.val : ℤ) - 1 + 1 = x + (i.succ.val : ℤ) - 1 := by
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega
    simpa only [Fin.val_castSucc, hx] using
      p.horizontal (x + (i.val : ℤ) - 1) (y + (j.val : ℤ) - 1)
  vertical i j := by
    have hy : y + (j.val : ℤ) - 1 + 1 = y + (j.succ.val : ℤ) - 1 := by
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega
    simpa only [Fin.val_castSucc, hy] using
      p.vertical (x + (i.val : ℤ) - 1) (y + (j.val : ℤ) - 1)
  phase := by simpa using hphase

/-- Every matching corrected Robinson plane is a substituted matching plane up to translation. -/
theorem nonempty_parent (fine : Plane) : Nonempty (Parent fine) := by
  classical
  obtain ⟨ox, oy, hphase⟩ := exists_phase_origin fine
  have hlocal (x y : ℤ) : ∃ p : Index, ∀ i j : Fin 2,
      childBlock p i j =
        fine.index ((ox.val : ℤ) + 2 * x + i.val) ((oy.val : ℤ) + 2 * y + j.val) := by
    obtain ⟨p, hp, _⟩ := existsUnique_centerParent
      (neighborhood fine ((ox.val : ℤ) + 2 * x) ((oy.val : ℤ) + 2 * y)
        ((thin_even fine ox.val oy.val x y).trans hphase))
    refine ⟨p, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [neighborhood, add_sub_assoc] using hp.1
    · simpa [neighborhood, add_sub_assoc] using hp.2.2.1
    · simpa [neighborhood, add_sub_assoc] using hp.2.1
    · simpa [neighborhood, add_sub_assoc] using hp.2.2.2
  choose coarse hc using hlocal
  refine ⟨{ coarse := { index := coarse, horizontal := ?_, vertical := ?_ }
            offsetX := ox, offsetY := oy, children := hc }⟩
  · intro x y
    apply (horizontal_iff_children _ _).mpr
    intro j
    rw [hc x y 1 j, hc (x + 1) y 0 j]
    simpa [mul_add, add_assoc] using
      fine.horizontal ((ox.val : ℤ) + 2 * x + 1) ((oy.val : ℤ) + 2 * y + j.val)
  · intro x y
    apply (vertical_iff_children _ _).mpr
    intro i
    rw [hc x y i 1, hc x (y + 1) i 0]
    simpa [mul_add, add_assoc] using
      fine.vertical ((ox.val : ℤ) + 2 * x + i.val) ((oy.val : ℤ) + 2 * y + 1)

/-- A substitution-parent tower above a prescribed indexed plane. -/
structure Tower (base : Plane) where
  /-- The matching plane at each scale. -/
  plane : ℕ → Plane
  /-- Alignment of horizontal child coordinates at each level. -/
  offsetX : ℕ → Fin 2
  /-- Alignment of vertical child coordinates at each level. -/
  offsetY : ℕ → Fin 2
  /-- Level zero is the prescribed plane. -/
  zero : plane 0 = base
  /-- Every adjacent pair of levels is related by the corrected substitution. -/
  children : ∀ (n : ℕ) (x y : ℤ) (i j : Fin 2),
    childBlock ((plane (n + 1)).index x y) i j =
      (plane n).index (((offsetX n).val : ℤ) + 2 * x + i.val)
        (((offsetY n).val : ℤ) + 2 * y + j.val)

private noncomputable def chooseParent (p : Plane) : Parent p :=
  Classical.choice (nonempty_parent p)

private noncomputable def parentPlane (base : Plane) : ℕ → Plane
  | 0 => base
  | n + 1 => (chooseParent (parentPlane base n)).coarse

/-- Repeated desubstitution constructs a parent tower over every matching plane. -/
noncomputable def tower (base : Plane) : Tower base where
  plane := parentPlane base
  offsetX n := (chooseParent (parentPlane base n)).offsetX
  offsetY n := (chooseParent (parentPlane base n)).offsetY
  zero := rfl
  children n := (chooseParent (parentPlane base n)).children

private def bit (code : ℕ) : Fin 2 := ⟨code % 2, Nat.mod_lt _ (by decide)⟩

private def walk : ℕ → Index → ℕ → Index
  | 0, p, _ => p
  | n + 1, p, code => walk n (childBlock p (bit code) (bit (code / 2))) (code / 4)

private def toZero (p : Index) : ℕ := (#[
  0, 3, 3, 3, 0, 12, 12, 12, 12, 12, 12, 12, 12,
  12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
  12, 12, 12, 12, 12, 12, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 12, 12, 12, 12, 12, 12, 12, 12, 12,
  12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
  12, 12, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3
  ] : Array ℕ)[p.val]!

private def fromZero (p : Index) : ℕ := (#[
  0, 13, 14, 15, 768, 832, 896, 960, 335, 330, 334, 331, 384,
  400, 416, 432, 464, 448, 496, 480, 269, 258, 256, 265, 271, 266,
  270, 267, 333, 322, 320, 329, 95, 90, 94, 91, 6, 25, 26,
  27, 29, 7, 31, 30, 77, 18, 1, 73, 79, 74, 78, 75,
  93, 22, 5, 89, 518, 512, 608, 646, 640, 704, 519, 525, 624,
  647, 653, 720, 513, 526, 576, 641, 654, 736, 517, 527, 592, 645,
  655, 752, 134, 2, 38, 166, 10, 11, 135, 141, 39, 167, 173,
  45, 33, 142, 9, 41, 174, 46, 133, 143, 37, 165, 175, 47
  ] : Array ℕ)[p.val]!

private theorem walk_toZero (p : Index) : walk 3 p (toZero p) = 0 := by
  fin_cases p <;> decide

private theorem walk_fromZero (p : Index) : walk 5 0 (fromZero p) = p := by
  fin_cases p <;> decide

private theorem walk_occurs {base : Plane} (t : Tower base) :
    ∀ (depth level : ℕ) (x y : ℤ) (code : ℕ), ∃ u v : ℤ,
      (t.plane level).index u v = walk depth ((t.plane (level + depth)).index x y) code := by
  intro depth
  induction depth with
  | zero => intro level x y code; exact ⟨x, y, rfl⟩
  | succ depth ih =>
    intro level x y code
    obtain ⟨u, v, huv⟩ := ih level
      (((t.offsetX (level + depth)).val : ℤ) + 2 * x + (bit code).val)
      (((t.offsetY (level + depth)).val : ℤ) + 2 * y + (bit (code / 2)).val) (code / 4)
    refine ⟨u, v, ?_⟩
    rw [← t.children] at huv
    simpa only [walk, Nat.add_assoc] using huv

/-- Every corrected tile type occurs at every level of every parent tower. -/
theorem Tower.every_tile {base : Plane} (t : Tower base) (level : ℕ) (target : Index) :
    ∃ x y : ℤ, (t.plane level).index x y = target := by
  let p := (t.plane (level + 5 + 3)).index 0 0
  obtain ⟨x, y, hxy⟩ := walk_occurs t 3 (level + 5) 0 0 (toZero p)
  have hzero : (t.plane (level + 5)).index x y = 0 := hxy.trans (walk_toZero p)
  obtain ⟨u, v, huv⟩ := walk_occurs t 5 level x y (fromZero target)
  exact ⟨u, v, huv.trans (by rw [hzero, walk_fromZero])⟩

private def expansion : ℕ → Index → ℕ → ℕ → Index
  | 0, p, _, _ => p
  | n + 1, p, x, y => childBlock (expansion n p (x / 2) (y / 2)) (bit x) (bit y)

private theorem bit_step (x : ℕ) :
    (bit x = 0 ∧ bit (x + 1) = 1 ∧ (x + 1) / 2 = x / 2) ∨
      (bit x = 1 ∧ bit (x + 1) = 0 ∧ (x + 1) / 2 = x / 2 + 1) := by
  have hm := Nat.mod_lt x (by decide : 0 < 2)
  by_cases h : x % 2 = 0
  · left
    refine ⟨?_, ?_, ?_⟩
    · apply Fin.ext; exact h
    · apply Fin.ext; change (x + 1) % 2 = 1; omega
    · omega
  · right
    refine ⟨?_, ?_, ?_⟩
    · apply Fin.ext; change x % 2 = 1; omega
    · apply Fin.ext; change (x + 1) % 2 = 0; omega
    · omega

private theorem expansion_horizontal (n : ℕ) (p : Index) (x y : ℕ)
    (hx : x + 1 < 2 ^ n) (hy : y < 2 ^ n) :
    (tile (components (expansion n p x y))).right =
      (tile (components (expansion n p (x + 1) y))).left := by
  induction n generalizing x y with
  | zero => simp only [pow_zero] at hx; omega
  | succ n ih =>
    rcases bit_step x with h | h
    · simp only [expansion, h.1, h.2.1, h.2.2]
      exact child_horizontal _ _
    · simp only [expansion, h.1, h.2.1, h.2.2]
      apply (horizontal_iff_children _ _).mp (ih (x / 2) (y / 2) ?_ ?_) (bit y)
      · rw [pow_succ] at hx
        omega
      · rw [pow_succ] at hy
        omega

private theorem expansion_vertical (n : ℕ) (p : Index) (x y : ℕ)
    (hx : x < 2 ^ n) (hy : y + 1 < 2 ^ n) :
    (tile (components (expansion n p x y))).top =
      (tile (components (expansion n p x (y + 1)))).bottom := by
  induction n generalizing x y with
  | zero => simp only [pow_zero] at hy; omega
  | succ n ih =>
    rcases bit_step y with h | h
    · simp only [expansion, h.1, h.2.1, h.2.2]
      exact child_vertical _ _
    · simp only [expansion, h.1, h.2.1, h.2.2]
      apply (vertical_iff_children _ _).mp (ih (x / 2) (y / 2) ?_ ?_) (bit x)
      · rw [pow_succ] at hx
        omega
      · rw [pow_succ] at hy
        omega

private theorem square_bound {n x : ℕ} (h : x < n + 1) : x < 2 ^ n :=
  lt_of_lt_of_le h (Nat.succ_le_of_lt (show n < 2 ^ n from Nat.lt_two_pow_self))

private def square (n : ℕ) : Rectangle tileSet (n + 1) (n + 1) where
  tile i j := tile (components (expansion n 0 i.val j.val))
  mem _i _j := tile_components_mem _
  horizontal i j hi := expansion_horizontal n 0 i.val j.val (square_bound hi)
    (square_bound j.isLt)
  vertical i j hj := expansion_vertical n 0 i.val j.val (square_bound i.isLt)
    (square_bound hj)

/-- The corrected Robinson tile set tiles the whole integer plane. -/
theorem tilesPlane_tileSet : TilesPlane tileSet :=
  (tilesPlane_iff_squares tileSet).mpr fun n => ⟨square n⟩

/-- The indexed matching-plane model is inhabited by the compactness construction. -/
instance : Nonempty Plane := tilesPlane_iff_nonempty_plane.mp tilesPlane_tileSet

end Cslib.WangTile.Robinson
