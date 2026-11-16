/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Shading.Geometry
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat

/-!
# Consecutive marked free lines in Robinson boards

A free line crosses no selected perpendicular light border inside its board. Sorting all
free lines above a marked crossing fills gaps in any sparse family, while retaining its marker.

## Main definitions

* `FreeGrid.ConsecutiveMarkedFreeGrid`: consecutive free rows and columns with a marked
  southwest crossing, indexed by `Fin (n + 1)`.

## References

After lean-wang revision `64268a3`, `Closed104.ShadedConsecutiveFreeGrid`: the semantic free
line predicates are used directly, without a separate Boolean enumeration layer.
-/

public section
namespace Cslib.WangTile.Robinson.FreeGrid

open QuarterGeometry RedShadeCycles ShadedPlaneSignalGrid

/-- Consecutive free rows and columns inside one board, with a marked southwest crossing.
The parameter `n` denotes one less than the number of selected rows and columns. -/
structure ConsecutiveMarkedFreeGrid (indexGrid : ℕ → ℕ → Index)
    (shadeGrid : ℕ → ℕ → RedShades.State) (west east south north n : ℕ) where
  /-- Increasing quarter coordinates of columns. -/
  column : Fin (n + 1) → ℕ
  /-- Increasing quarter coordinates of rows. -/
  row : Fin (n + 1) → ℕ
  /-- Columns are distinct and increasing. -/
  column_strictMono : StrictMono column
  /-- Rows are distinct and increasing. -/
  row_strictMono : StrictMono row
  /-- Columns lie to the right of the west boundary. -/
  column_west : ∀ i, quarterWest west < column i
  /-- Columns lie to the left of the east boundary. -/
  column_east : ∀ i, column i < quarterEast east
  /-- Rows lie above the south boundary. -/
  row_south : ∀ i, quarterSouth south < row i
  /-- Rows lie below the north boundary. -/
  row_north : ∀ i, row i < quarterNorth north
  /-- Selected columns have no horizontal light obstruction. -/
  freeColumn : ∀ i, IsFreeColumn indexGrid shadeGrid south north (column i)
  /-- Selected rows have no vertical light obstruction. -/
  freeRow : ∀ i, IsFreeRow indexGrid shadeGrid west east (row i)
  /-- No unselected free column lies between consecutive selected columns. -/
  noFreeColumnBetween : ∀ (i : Fin n) (k : ℕ),
    column i.castSucc < k → k < column i.succ →
      ¬IsFreeColumn indexGrid shadeGrid south north k
  /-- No unselected free row lies between consecutive selected rows. -/
  noFreeRowBetween : ∀ (i : Fin n) (k : ℕ),
    row i.castSucc < k → k < row i.succ →
      ¬IsFreeRow indexGrid shadeGrid west east k
  /-- The southwest crossing is the northeast quarter of tile zero. -/
  marker : Quarters.QuarterIndex.mk (indexGrid (column 0 / 2) (row 0 / 2))
    (quadrantAt (column 0) (row 0)) = ⟨0, .northeast⟩

/-- Sorting an initial segment preserves its minimum and leaves no gaps. -/
private theorem select_lines {n lo hi : ℕ} {p : ℕ → Prop}
    (f : Fin (n + 1) → ℕ) (hf : StrictMono f)
    (hmem : ∀ i, lo < f i ∧ f i < hi ∧ p (f i)) :
    ∃ g : Fin (n + 1) → ℕ, StrictMono g ∧ g 0 = f 0 ∧
      (∀ i, lo < g i ∧ g i < hi ∧ p (g i)) ∧
      ∀ (i : Fin n) (k : ℕ), g i.castSucc < k → k < g i.succ → ¬p k := by
  classical
  let s := (Finset.Ioo lo hi).filter (fun k => f 0 ≤ k ∧ p k)
  have mem (i : Fin (n + 1)) : f i ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨(hmem i).1, (hmem i).2.1⟩, hf.monotone (Fin.zero_le i), (hmem i).2.2⟩
  have card : n + 1 ≤ s.card := by
    let embed : Fin (n + 1) → s := fun i => ⟨f i, mem i⟩
    have hinj : Function.Injective embed := fun i j h => hf.injective (congrArg Subtype.val h)
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective embed hinj
  let g := s.orderEmbOfCardLe card
  have gmem i := s.orderEmbOfCardLe_mem card i
  have properties i : lo < g i ∧ g i < hi ∧ p (g i) := by
    have h := Finset.mem_filter.mp (gmem i)
    exact ⟨(Finset.mem_Ioo.mp h.1).1, (Finset.mem_Ioo.mp h.1).2, h.2.2⟩
  refine ⟨g, g.strictMono, ?_, properties, ?_⟩
  · apply le_antisymm
    · let j := (s.orderIsoOfFin rfl).symm ⟨f 0, mem 0⟩
      have hj : s.orderEmbOfFin rfl j = f 0 :=
        congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨f 0, mem 0⟩)
      exact ((s.orderEmbOfFin rfl).monotone (show Fin.castLE card 0 ≤ j by
        change 0 ≤ j.val
        exact Nat.zero_le _)).trans_eq hj
    · exact (Finset.mem_filter.mp (gmem 0)).2.1
  · intro i k hl hu hp
    have hk : k ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨(properties i.castSucc).1.trans hl,
        hu.trans (properties i.succ).2.1⟩,
        (Finset.mem_filter.mp (gmem i.castSucc)).2.1.trans hl.le, hp⟩
    let j := (s.orderIsoOfFin rfl).symm ⟨k, hk⟩
    have hj : s.orderEmbOfFin rfl j = k :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨k, hk⟩)
    have lower : Fin.castLE card i.castSucc < j := by
      apply (s.orderEmbOfFin rfl).lt_iff_lt.mp
      exact hl.trans_eq hj.symm
    have upper : j < Fin.castLE card i.succ := by
      apply (s.orderEmbOfFin rfl).lt_iff_lt.mp
      exact hj.trans_lt hu
    simp only [Fin.lt_def, Fin.val_castLE, Fin.val_castSucc, Fin.val_succ] at lower upper
    omega


/-- Fill all gaps in sparse free lines without moving their marked southwest crossing. -/
noncomputable def ConsecutiveMarkedFreeGrid.ofSparse
    {g : ℕ → ℕ → Index} {s : ℕ → ℕ → RedShades.State}
    {west east south north n : ℕ}
    (columns rows : Fin (n + 1) → ℕ)
    (hcolumns : StrictMono columns) (hrows : StrictMono rows)
    (column_mem : ∀ i, quarterWest west < columns i ∧ columns i < quarterEast east ∧
      IsFreeColumn g s south north (columns i))
    (row_mem : ∀ i, quarterSouth south < rows i ∧ rows i < quarterNorth north ∧
      IsFreeRow g s west east (rows i))
    (marker : Quarters.QuarterIndex.mk (g (columns 0 / 2) (rows 0 / 2))
      (quadrantAt (columns 0) (rows 0)) = ⟨0, .northeast⟩) :
    ConsecutiveMarkedFreeGrid g s west east south north n := Classical.choice <| by
  classical
  obtain ⟨c, hc, hc0, cmem, cnext⟩ := select_lines columns hcolumns column_mem
  obtain ⟨r, hr, hr0, rmem, rnext⟩ := select_lines rows hrows row_mem
  exact ⟨{
    column := c, row := r
    column_strictMono := hc, row_strictMono := hr
    column_west := fun i => (cmem i).1
    column_east := fun i => (cmem i).2.1
    row_south := fun i => (rmem i).1
    row_north := fun i => (rmem i).2.1
    freeColumn := fun i => (cmem i).2.2
    freeRow := fun i => (rmem i).2.2
    noFreeColumnBetween := cnext
    noFreeRowBetween := rnext
    marker := by simpa only [hc0, hr0] using marker }⟩

end Cslib.WangTile.Robinson.FreeGrid
