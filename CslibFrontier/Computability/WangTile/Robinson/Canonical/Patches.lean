/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Canonical.Certificates
import CslibFrontier.Computability.WangTile.Compactness

/-!
# Canonical decorated Robinson patches

The selected closed substitution produces matching corrected tiles and shade blocks.
Nearest selected borders determine obstruction signals along each row and column.
Pairing these three layers gives finite scaffold patches of unbounded size.

## Main definitions

* `canonicalPatch`: the decorated square of side `2 * 4^level` below a selected root.

## Main results

* `scaffold_tilesPlane`: the concrete decorated scaffold tiles the plane.

## References

Restructured from [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`: its `ShadedSubstitutionSupertiles`, `ShadedSignalRectangle` and
`ShadedSubstitutionPlane` modules in the corrected Robinson development.
-/

public section

namespace Cslib.WangTile.Robinson.Canonical

open QuarterGeometry

/-- The finite local shade rules needed when decorating a bounded square. -/
private structure ShadeValidOn (indexGrid : ℕ → ℕ → Index)
    (shadeGrid : ℕ → ℕ → RedShades.State) (width height : ℕ) : Prop where
  allowed : ∀ x y, x < width → y < height →
    RedShades.locallyAllowed ⟨indexGrid (x / 2) (y / 2), quadrantAt x y⟩
      (shadeGrid x y) = true
  hmatch : ∀ x y, x + 1 < width → y < height →
    (shadeGrid x y).east = (shadeGrid (x + 1) y).west
  vmatch : ∀ x y, x < width → y + 1 < height →
    (shadeGrid x y).north = (shadeGrid x (y + 1)).south

/-- Position in a `4 x 4` child block, encoded in south-to-north row order. -/
@[expose] def childPosition (x y : Nat) : Fin 16 :=
  blockPosition ⟨x % 4, Nat.mod_lt _ (by decide)⟩ ⟨y % 4, Nat.mod_lt _ (by decide)⟩

/-- Simultaneously replace every node in a grid by its certified child block. -/
private def refineNodeGrid (grid : Nat → Nat → Node) : Nat → Nat → Node :=
  fun x y => (grid (x / 4) (y / 4)).child (childPosition x y)

/-- Tile-and-shade compatibility inside a bounded node rectangle. -/
private structure CompatibleOn (grid : Nat → Nat → Node) (width height : Nat) : Prop where
  hmatch : ∀ x y, x + 1 < width → y < height →
    HCompatible (grid x y) (grid (x + 1) y)
  vmatch : ∀ x y, x < width → y + 1 < height →
    VCompatible (grid x y) (grid x (y + 1))

private theorem CompatibleOn.refine {grid : Nat → Nat → Node} {width height : Nat}
    (compatible : CompatibleOn grid width height) :
    CompatibleOn (refineNodeGrid grid) (4 * width) (4 * height) := by
  constructor
  · intro x y hx hy
    have hxmod : x % 4 < 4 := Nat.mod_lt _ (by decide)
    have hymod : y % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hboundary : x % 4 = 3
    · have hnextDiv : (x + 1) / 4 = x / 4 + 1 := by omega
      have hnextMod : (x + 1) % 4 = 0 := by omega
      have hparentX : x / 4 + 1 < width := by omega
      have hparentY : y / 4 < height := by omega
      have parentMatch := compatible.hmatch (x / 4) (y / 4)
        hparentX hparentY
      have childMatch := children_hCompatible_boundary parentMatch
        ⟨y % 4, hymod⟩
      simpa [refineNodeGrid, childPosition, blockPosition, hboundary,
        hnextDiv, hnextMod] using childMatch
    · have hlocal : x % 4 < 3 := by omega
      have hnextDiv : (x + 1) / 4 = x / 4 := by omega
      have hnextMod : (x + 1) % 4 = x % 4 + 1 := by omega
      have childMatch := children_hCompatible_within (grid (x / 4) (y / 4))
        ⟨x % 4, hlocal⟩ ⟨y % 4, hymod⟩
      simpa [refineNodeGrid, childPosition, blockPosition, hnextDiv,
        hnextMod] using childMatch
  · intro x y hx hy
    have hxmod : x % 4 < 4 := Nat.mod_lt _ (by decide)
    have hymod : y % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hboundary : y % 4 = 3
    · have hnextDiv : (y + 1) / 4 = y / 4 + 1 := by omega
      have hnextMod : (y + 1) % 4 = 0 := by omega
      have hparentX : x / 4 < width := by omega
      have hparentY : y / 4 + 1 < height := by omega
      have parentMatch := compatible.vmatch (x / 4) (y / 4)
        hparentX hparentY
      have childMatch := children_vCompatible_boundary parentMatch
        ⟨x % 4, hxmod⟩
      simpa [refineNodeGrid, childPosition, blockPosition, hboundary,
        hnextDiv, hnextMod] using childMatch
    · have hlocal : y % 4 < 3 := by omega
      have hnextDiv : (y + 1) / 4 = y / 4 := by omega
      have hnextMod : (y + 1) % 4 = y % 4 + 1 := by omega
      have childMatch := children_vCompatible_within (grid (x / 4) (y / 4))
        ⟨x % 4, hxmod⟩ ⟨y % 4, hlocal⟩
      simpa [refineNodeGrid, childPosition, blockPosition, hnextDiv,
        hnextMod] using childMatch

/-- The decorated supertile obtained by repeatedly substituting the selected 4×4 children. -/
@[expose] def supertileNodeGrid : ℕ → Node → ℕ → ℕ → Node
  | 0, root, _, _ => root
  | level + 1, root, x, y =>
      (supertileNodeGrid level root (x / 4) (y / 4)).child (childPosition x y)

/-- Underlying corrected tile at a coordinate in the decorated supertile. -/
@[expose] def supertileIndexGrid (level : Nat) (root : Node) : Nat → Nat → Index :=
  fun x y => (supertileNodeGrid level root x y).parent

/-- Flatten each corrected-tile shade block into its four quarter states. -/
@[expose] def supertileShadeGrid (level : Nat) (root : Node) :
    Nat → Nat → RedShades.State := fun x y =>
  ((supertileNodeGrid level root (x / 2) (y / 2)).block).at (x % 2) (y % 2)

private theorem supertileNodeGrid_compatible (level : Nat) (root : Node) :
    CompatibleOn (supertileNodeGrid level root) (4 ^ level) (4 ^ level) := by
  induction level with
  | zero =>
      constructor <;> intro x y h <;> omega
  | succ level ih =>
      change CompatibleOn (refineNodeGrid (supertileNodeGrid level root))
        (4 ^ (level + 1)) (4 ^ (level + 1))
      simpa only [pow_succ, Nat.mul_comm] using ih.refine

private theorem supertile_validShadeRectangle (level : Nat) (root : Node) :
    ShadeValidOn
      (supertileIndexGrid level root) (supertileShadeGrid level root)
      (2 * 4 ^ level) (2 * 4 ^ level) := by
  constructor
  · intro x y hx hy
    have hxmod : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have hymod : y % 2 < 2 := Nat.mod_lt _ (by decide)
    have allowed := (supertileNodeGrid level root (x / 2) (y / 2)).block_allowed
        ⟨x % 2, hxmod⟩ ⟨y % 2, hymod⟩
    simpa [supertileIndexGrid, supertileShadeGrid,
      quadrantAt, Nat.mod_mod] using allowed
  · intro x y hx hy
    have hxmod : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have hymod : y % 2 < 2 := Nat.mod_lt _ (by decide)
    have hparentY : y / 2 < 4 ^ level := by omega
    by_cases hboundary : x % 2 = 1
    · have hnextDiv : (x + 1) / 2 = x / 2 + 1 := by omega
      have hnextMod : (x + 1) % 2 = 0 := by omega
      have hparentX : x / 2 + 1 < 4 ^ level := by omega
      have compatible := (supertileNodeGrid_compatible level root).hmatch
        (x / 2) (y / 2) hparentX hparentY
      have blockMatch := compatible.2
      simp only [ShadeBlock.hMatches, Bool.and_eq_true,
        decide_eq_true_eq] at blockMatch
      have hyCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hyCases with hyzero | hyone
      · simpa [supertileShadeGrid, ShadeBlock.at,
          hboundary, hnextDiv, hnextMod, hyzero] using blockMatch.1
      · simpa [supertileShadeGrid, ShadeBlock.at,
          hboundary, hnextDiv, hnextMod, hyone] using blockMatch.2
    · have hxzero : x % 2 = 0 := by omega
      have hnextDiv : (x + 1) / 2 = x / 2 := by omega
      have hnextMod : (x + 1) % 2 = 1 := by omega
      have internal := (supertileNodeGrid level root (x / 2) (y / 2)).block_internal
      have hyCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hyCases with hyzero | hyone
      · simpa [supertileShadeGrid, ShadeBlock.at,
          hxzero, hnextDiv, hnextMod, hyzero] using internal.1
      · simpa [supertileShadeGrid, ShadeBlock.at,
          hxzero, hnextDiv, hnextMod, hyone] using internal.2.1
  · intro x y hx hy
    have hxmod : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have hymod : y % 2 < 2 := Nat.mod_lt _ (by decide)
    have hparentX : x / 2 < 4 ^ level := by omega
    by_cases hboundary : y % 2 = 1
    · have hnextDiv : (y + 1) / 2 = y / 2 + 1 := by omega
      have hnextMod : (y + 1) % 2 = 0 := by omega
      have hparentY : y / 2 + 1 < 4 ^ level := by omega
      have compatible := (supertileNodeGrid_compatible level root).vmatch
        (x / 2) (y / 2) hparentX hparentY
      have blockMatch := compatible.2
      simp only [ShadeBlock.vMatches, Bool.and_eq_true,
        decide_eq_true_eq] at blockMatch
      have hxCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hxCases with hxzero | hxone
      · simpa [supertileShadeGrid, ShadeBlock.at,
          hboundary, hnextDiv, hnextMod, hxzero] using blockMatch.1
      · simpa [supertileShadeGrid, ShadeBlock.at,
          hboundary, hnextDiv, hnextMod, hxone] using blockMatch.2
    · have hyzero : y % 2 = 0 := by omega
      have hnextDiv : (y + 1) / 2 = y / 2 := by omega
      have hnextMod : (y + 1) % 2 = 1 := by omega
      have internal := (supertileNodeGrid level root (x / 2) (y / 2)).block_internal
      have hxCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hxCases with hxzero | hxone
      · simpa [supertileShadeGrid, ShadeBlock.at,
          hyzero, hnextDiv, hnextMod, hxzero] using internal.2.2.1
      · simpa [supertileShadeGrid, ShadeBlock.at,
          hyzero, hnextDiv, hnextMod, hxone] using internal.2.2.2

/-- Orientation of the last selected border strictly before an edge. -/
@[expose] def previousInterior (interior : ℕ → Option Bool) : ℕ → Option Bool
  | 0 => none
  | position + 1 => (interior position).orElse fun _ => previousInterior interior position

/-- Orientation of the first selected border in a bounded suffix. -/
@[expose] def nextInterior (interior : ℕ → Option Bool) : ℕ → ℕ → Option Bool
  | _, 0 => none
  | position, fuel + 1 => (interior position).orElse fun _ =>
      nextInterior interior (position + 1) fuel

/-- A selected border remains the previous one until another border occurs. -/
theorem previousInterior_eq_of_none_between
    {interior : ℕ → Option Bool} {border position : ℕ} {orientation : Bool}
    (selected : interior border = some orientation)
    (between : ∀ candidate, border < candidate → candidate < position →
      interior candidate = none) (afterBorder : border < position) :
    previousInterior interior position = some orientation := by
  have startLe : border + 1 ≤ position := by omega
  induction position, startLe using Nat.le_induction with
  | base => simp [previousInterior, selected]
  | succ position _ ih =>
      have previous := ih
        (fun candidate lower upper => between candidate lower (by omega)) (by omega)
      simp [previousInterior, between position (by omega) (by omega), previous]

/-- A bounded suffix has the given first orientation if a border with that orientation occurs
and no opposite border precedes it. -/
theorem nextInterior_eq_of_no_opposite_before
    {interior : ℕ → Option Bool} {position border length : ℕ} {orientation : Bool}
    (selected : interior border = some orientation)
    (noOpposite : ∀ candidate, position ≤ candidate → candidate < border →
      interior candidate ≠ some (!orientation))
    (atMostBorder : position ≤ border) (borderBeforeEnd : border < length) :
    nextInterior interior position (length - position) = some orientation := by
  induction distance : border - position generalizing position with
  | zero =>
      have positionEq : position = border := by omega
      subst position
      have fuelPositive : 0 < length - border := by omega
      obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero fuelPositive.ne'
      rw [fuelEq]
      simp [nextInterior, selected]
  | succ distance ih =>
      have positionBefore : position < border := by omega
      have fuelEq : length - position = length - (position + 1) + 1 := by omega
      rw [fuelEq]
      cases current : interior position with
      | none =>
          simp only [nextInterior, current, Option.orElse_none]
          apply ih (position := position + 1)
          · intro candidate lower upper
            exact noOpposite candidate (by omega) upper
          · omega
          · omega
      | some currentOrientation =>
          cases orientation <;> cases currentOrientation
          · simp [nextInterior, current]
          · exact (noOpposite position le_rfl positionBefore current).elim
          · exact (noOpposite position le_rfl positionBefore current).elim
          · simp [nextInterior, current]

/-- A successful suffix scan witnesses an actual selected border in the scanned interval. -/
theorem exists_interior_of_nextInterior_eq_some
    {interior : ℕ → Option Bool} {position fuel : ℕ} {orientation : Bool}
    (next : nextInterior interior position fuel = some orientation) :
    ∃ candidate, position ≤ candidate ∧ candidate < position + fuel ∧
      interior candidate = some orientation := by
  induction fuel generalizing position with
  | zero => simp [nextInterior] at next
  | succ fuel ih =>
      cases current : interior position with
      | none =>
          simp only [nextInterior, current, Option.orElse_none] at next
          obtain ⟨candidate, lower, upper, selected⟩ := ih next
          exact ⟨candidate, by omega, by omega, selected⟩
      | some currentOrientation =>
          simp only [nextInterior, current, Option.orElse_some] at next
          cases next
          exact ⟨position, le_rfl, by omega, current⟩

/-- Canonical edge flow determined by the nearest selected borders. The clear case is the
interval before a closing border whose previous border is opening or absent. -/
@[expose] def intervalEdge (interior : ℕ → Option Bool) (length position : ℕ) : Signals.Flow :=
  match nextInterior interior position (length - position) with
  | none => .backward
  | some false =>
      if previousInterior interior position = some false then .forward else .none
  | some true =>
      if previousInterior interior position = some true then .backward else .forward

/-- The exact nearest-border condition for a clear edge. -/
theorem intervalEdge_eq_none_iff (interior : ℕ → Option Bool) (length position : ℕ) :
    intervalEdge interior length position = .none ↔
      nextInterior interior position (length - position) = some false ∧
        previousInterior interior position ≠ some false := by
  unfold intervalEdge
  cases hnext : nextInterior interior position (length - position) with
  | none => simp
  | some next =>
      cases next <;> cases hprevious : previousInterior interior position with
      | none => simp
      | some previous => cases previous <;> simp

/-- Every edge between consecutive opening and closing borders is clear. -/
theorem intervalEdge_eq_none_of_between_borders
    {interior : ℕ → Option Bool} {length opening closing position : ℕ}
    (openingBorder : interior opening = some true)
    (closingBorder : interior closing = some false)
    (noBorder : ∀ candidate, opening < candidate → candidate < closing →
      interior candidate = none)
    (afterOpening : opening < position) (atMostClosing : position ≤ closing)
    (closingBeforeEnd : closing < length) :
    intervalEdge interior length position = .none := by
  rw [intervalEdge_eq_none_iff]
  constructor
  · apply nextInterior_eq_of_no_opposite_before closingBorder
      (atMostBorder := atMostClosing) (borderBeforeEnd := closingBeforeEnd)
    intro candidate positionLe beforeClosing
    rw [noBorder candidate (afterOpening.trans_le positionLe) beforeClosing]
    simp
  · rw [previousInterior_eq_of_none_between openingBorder
      (fun candidate lower upper =>
        noBorder candidate lower (upper.trans_le atMostClosing)) afterOpening]
    simp

/-- Nearest-border flows satisfy the one-dimensional local obstruction rule. -/
theorem intervalEdge_allowed (interior : ℕ → Option Bool) (length position : ℕ)
    (hposition : position < length) :
    Signals.flowAllowed (interior position) (intervalEdge interior length position)
      (intervalEdge interior length (position + 1)) = true := by
  have hlength : length - position = length - (position + 1) + 1 := by omega
  cases hcurrent : interior position with
  | none =>
      have hprevious : previousInterior interior (position + 1) =
          previousInterior interior position := by simp [previousInterior, hcurrent]
      have hnext : nextInterior interior position (length - position) =
          nextInterior interior (position + 1) (length - (position + 1)) := by
        rw [hlength]
        simp [nextInterior, hcurrent]
      simp [Signals.flowAllowed, intervalEdge, hprevious, hnext]
  | some current =>
      cases current <;> cases hprevious : previousInterior interior position with
      | none =>
          cases hnext : nextInterior interior (position + 1) (length - (position + 1)) with
          | none =>
              simp [Signals.flowAllowed, intervalEdge, hcurrent,
                hprevious, hnext, hlength, nextInterior]
          | some next =>
              cases next <;> simp [Signals.flowAllowed, intervalEdge, hcurrent,
                hprevious, hnext, hlength, previousInterior, nextInterior]
      | some previous =>
          cases previous <;>
            cases hnext : nextInterior interior (position + 1) (length - (position + 1)) with
            | none =>
                simp [Signals.flowAllowed, intervalEdge, hcurrent,
                  hprevious, hnext, hlength, nextInterior]
            | some next =>
                cases next <;> simp [Signals.flowAllowed, intervalEdge, hcurrent,
                  hprevious, hnext, hlength, previousInterior, nextInterior]

/-- A selected border cannot have clear canonical signal edges on both sides. -/
theorem interior_eq_none_of_adjacent_clear
    (interior : ℕ → Option Bool) {length position : ℕ} (hposition : position < length)
    (hleft : intervalEdge interior length position = .none)
    (hright : intervalEdge interior length (position + 1) = .none) :
    interior position = none := by
  have allowed := intervalEdge_allowed interior length position hposition
  rw [hleft, hright] at allowed
  cases hcurrent : interior position with
  | none => rfl
  | some current => cases current <;> simp [Signals.flowAllowed, hcurrent] at allowed

/-- Side length in quarter tiles of a decorated supertile. -/
@[expose] def side (level : ℕ) : ℕ := 2 * 4 ^ level

/-- Selected vertical-border orientation along a quarter-tile row. -/
@[expose] def rowInterior (level : ℕ) (root : Node) (x y : ℕ) : Option Bool :=
  (supertileNodeGrid level root (x / 2) (y / 2)).rowInterior (x % 2) (y % 2)

/-- Selected horizontal-border orientation along a quarter-tile column. -/
@[expose] def columnInterior (level : ℕ) (root : Node) (x y : ℕ) : Option Bool :=
  (supertileNodeGrid level root (x / 2) (y / 2)).columnInterior (x % 2) (y % 2)

/-- The three-layer canonical site. Its four signal edges use the nearest selected borders. -/
@[expose] def site (level : ℕ) (root : Node) (x y : ℕ) : ShadedSignals.Site where
  quarter := ⟨supertileIndexGrid level root (x / 2) (y / 2), quadrantAt x y⟩
  shade := supertileShadeGrid level root x y
  signal := {
    west := intervalEdge (fun x => rowInterior level root x y) (side level) x
    east := intervalEdge (fun x => rowInterior level root x y) (side level) (x + 1)
    south := intervalEdge (fun y => columnInterior level root x y) (side level) y
    north := intervalEdge (fun y => columnInterior level root x y) (side level) (y + 1) }

private theorem site_allowed (level : ℕ) (root : Node) (x y : ℕ)
    (hx : x < side level) (hy : y < side level) :
    ShadedSignals.locallyAllowed (site level root x y).quarter (site level root x y).shade
      (site level root x y).signal = true := by
  have hh := intervalEdge_allowed (fun x => rowInterior level root x y) (side level) x hx
  have hv := intervalEdge_allowed (fun y => columnInterior level root x y) (side level) y hy
  simpa [ShadedSignals.locallyAllowed, Signals.horizontalAllowed, Signals.verticalAllowed,
    site, rowInterior, columnInterior, Node.rowInterior, Node.columnInterior,
    supertileIndexGrid, supertileShadeGrid, quadrantAt, Nat.mod_mod] using
    Bool.and_eq_true_iff.mpr ⟨hh, hv⟩

private theorem quarter_hmatch (level : ℕ) (root : Node) (x y : ℕ)
    (hx : x + 1 < side level) (hy : y < side level) :
    (Quarters.quarterTile (site level root x y).quarter).right =
      (Quarters.quarterTile (site level root (x + 1) y).quarter).left := by
  have hxmod : x % 2 < 2 := Nat.mod_lt _ (by decide)
  have hymod : y % 2 < 2 := Nat.mod_lt _ (by decide)
  have hyParent : y / 2 < 4 ^ level := by dsimp [side] at hy; omega
  change (TileSubdivision.subdivideTileAt _ _).right =
    (TileSubdivision.subdivideTileAt _ _).left
  rw [TileSubdivision.horizontal_iff]
  by_cases hboundary : x % 2 = 1
  · have hnextDiv : (x + 1) / 2 = x / 2 + 1 := by omega
    have hnextMod : (x + 1) % 2 = 0 := by omega
    have hxParent : x / 2 + 1 < 4 ^ level := by dsimp [side] at hx; omega
    have parentMatch :=
      ((supertileNodeGrid_compatible level root).hmatch
        (x / 2) (y / 2) hxParent hyParent).1
    have hyCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
    rcases hyCases with hyEq | hyEq <;>
      simpa [site, quadrantAt, Quadrant.ofBits, supertileIndexGrid, hboundary,
        hnextDiv, hnextMod, hyEq] using parentMatch
  · have hxzero : x % 2 = 0 := by omega
    have hnextDiv : (x + 1) / 2 = x / 2 := by omega
    have hnextMod : (x + 1) % 2 = 1 := by omega
    have hyCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
    rcases hyCases with hyEq | hyEq <;>
      simp [site, quadrantAt, Quadrant.ofBits, hxzero, hnextDiv, hnextMod, hyEq]

private theorem quarter_vmatch (level : ℕ) (root : Node) (x y : ℕ)
    (hx : x < side level) (hy : y + 1 < side level) :
    (Quarters.quarterTile (site level root x y).quarter).top =
      (Quarters.quarterTile (site level root x (y + 1)).quarter).bottom := by
  have hxmod : x % 2 < 2 := Nat.mod_lt _ (by decide)
  have hymod : y % 2 < 2 := Nat.mod_lt _ (by decide)
  have hxParent : x / 2 < 4 ^ level := by dsimp [side] at hx; omega
  change (TileSubdivision.subdivideTileAt _ _).top =
    (TileSubdivision.subdivideTileAt _ _).bottom
  rw [TileSubdivision.vertical_iff]
  by_cases hboundary : y % 2 = 1
  · have hnextDiv : (y + 1) / 2 = y / 2 + 1 := by omega
    have hnextMod : (y + 1) % 2 = 0 := by omega
    have hyParent : y / 2 + 1 < 4 ^ level := by dsimp [side] at hy; omega
    have parentMatch :=
      ((supertileNodeGrid_compatible level root).vmatch
        (x / 2) (y / 2) hxParent hyParent).1
    have hxCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hxCases with hxEq | hxEq <;>
      simpa [site, quadrantAt, Quadrant.ofBits, supertileIndexGrid, hboundary,
        hnextDiv, hnextMod, hxEq] using parentMatch
  · have hyzero : y % 2 = 0 := by omega
    have hnextDiv : (y + 1) / 2 = y / 2 := by omega
    have hnextMod : (y + 1) % 2 = 1 := by omega
    have hxCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hxCases with hxEq | hxEq <;>
      simp [site, quadrantAt, Quadrant.ofBits, hyzero, hnextDiv, hnextMod, hxEq]

/-- A canonical three-layer patch of the concrete scaffold, with matching edges and local
shade/signal allowance proved from the closed decorated substitution. -/
@[expose] def canonicalPatch (level : ℕ) (root : Node) :
    Rectangle scaffold.tiles (side level) (side level) where
  tile i j := ShadedSignals.tile (site level root i.val j.val)
  mem i j := by
    exact ShadedSignals.tile_mem _
      ((supertile_validShadeRectangle level root).allowed i.val j.val i.isLt j.isLt)
      (site_allowed level root i.val j.val i.isLt j.isLt)
  horizontal i j hi := by
    exact (ShadedSignals.horizontal_iff _ _).mpr
      ⟨quarter_hmatch level root i.val j.val hi j.isLt,
        (supertile_validShadeRectangle level root).hmatch i.val j.val hi j.isLt, rfl⟩
  vertical i j hj := by
    exact (ShadedSignals.vertical_iff _ _).mpr
      ⟨quarter_vmatch level root i.val j.val i.isLt hj,
        (supertile_validShadeRectangle level root).vmatch i.val j.val i.isLt hj, rfl⟩

/-- The concrete decorated Robinson scaffold has a plane tiling, by compactness of its
canonical finite squares. This proves scaffold nonemptiness, not payload realization. -/
theorem scaffold_tilesPlane : TilesPlane scaffold.tiles := by
  apply (tilesPlane_iff_squares _).mpr
  intro n
  have growth : n + 1 ≤ side (n + 1) := by
    have := (Nat.lt_two_pow_self : n + 1 < 2 ^ (n + 1))
    have := Nat.pow_le_pow_left (show 2 ≤ 4 by decide) (n + 1)
    dsimp [side]
    omega
  exact ⟨(canonicalPatch (n + 1) seedNode).crop growth growth⟩

end Cslib.WangTile.Robinson.Canonical
