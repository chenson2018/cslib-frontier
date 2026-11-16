/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Shading.Basic
public import CslibFrontier.Computability.WangTile.Routing
public import CslibFrontier.Computability.WangTile.Robinson.Hierarchy
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FinCases

/-!
# The shaded Robinson signal scaffold

Directed obstruction signals pass unchanged between light borders. At a light border the outer
edge carries a signal and the inner edge may absorb one. Dark wires do not constrain signals.
Clear horizontal and vertical edges determine which payload directions the scaffold carries;
the clear northeast quarter of index zero additionally marks a seeded crossing.

## Main definitions

* `Signals.flowAllowed`: the common one-dimensional transmission and border rule.
* `ShadedSignals.Site`: a quarter with a shade state and an obstruction state.
* `scaffold`: the finite shaded Robinson scaffold with its effective routing decoder.
* `ShadedSignals.Decoded`: the semantic sites of an ordinary scaffold plane.

## Main results

* `ShadedSignals.tile_injective`: the layered encoding recovers every component.
* `ShadedSignals.horizontal_iff`, `ShadedSignals.vertical_iff`: exact matching semantics.
* `ShadedSignals.routeRole_tile`: the local clear-edge description of the routing role.

## References

The signal rules are a step of the seed-removal construction in [JeandelVanier2020],
Section 3.3, pp. 26–29 of the authors' manuscript, using its corrected 104-tile alphabet.
Prior formalization, revision `64268a3`:
[lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3/LeanWang/Robinson/Closed104),
modules `Signals`, `ShadedSignals`, `ShadedSignalRoutingScaffold` and
`ShadedRoutedPlaneDecode`.
-/

public section
namespace Cslib.WangTile.Robinson

namespace Quarters

private def parentAt (block : Fin 13) (offset : Fin 8) : Index :=
  ⟨8 * block.val + offset.val, by omega⟩

private def ParentCodesUnique (block : Fin 13) : Prop :=
  ∀ (offset : Fin 8) (other : Index),
    Robinson.tile (components (parentAt block offset)) = Robinson.tile (components other) →
      parentAt block offset = other

private theorem parentCodesUnique0 : ParentCodesUnique 0 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique1 : ParentCodesUnique 1 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique2 : ParentCodesUnique 2 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique3 : ParentCodesUnique 3 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique4 : ParentCodesUnique 4 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique5 : ParentCodesUnique 5 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique6 : ParentCodesUnique 6 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique7 : ParentCodesUnique 7 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique8 : ParentCodesUnique 8 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique9 : ParentCodesUnique 9 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique10 : ParentCodesUnique 10 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique11 : ParentCodesUnique 11 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide
private theorem parentCodesUnique12 : ParentCodesUnique 12 := by
  simp only [ParentCodesUnique, Robinson.tile, WangTile.mk.injEq]
  decide

private theorem parentCodesUnique (b : Fin 13) : ParentCodesUnique b := by
  fin_cases b
  · exact parentCodesUnique0
  · exact parentCodesUnique1
  · exact parentCodesUnique2
  · exact parentCodesUnique3
  · exact parentCodesUnique4
  · exact parentCodesUnique5
  · exact parentCodesUnique6
  · exact parentCodesUnique7
  · exact parentCodesUnique8
  · exact parentCodesUnique9
  · exact parentCodesUnique10
  · exact parentCodesUnique11
  · exact parentCodesUnique12

private theorem parentTile_injective :
    Function.Injective (fun i : Index => Robinson.tile (components i)) := by
  intro i j h
  let b : Fin 13 := ⟨i.val / 8, by omega⟩
  let k : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have hi : parentAt b k = i := Fin.ext (by dsimp [parentAt, b, k]; omega)
  exact hi.symm.trans (parentCodesUnique b k j (by simpa only [hi] using h))

/-- Quarter edge codes retain the corrected parent index and quadrant. -/
theorem quarterTile_injective : Function.Injective quarterTile := by
  rintro ⟨i, q⟩ ⟨j, r⟩ h
  cases q <;> cases r <;>
    simp_all [quarterTile, TileSubdivision.subdivideTileAt,
      TileSubdivision.horizontalEdgeColor, TileSubdivision.verticalEdgeColor,
      TileSubdivision.internalHorizontalColor, TileSubdivision.internalVerticalColor,
      Nat.pair_eq_pair, parentTile_injective.eq_iff]

/-- A matching plane of quarter sites, before regrouping into corrected parent tiles. -/
structure Plane where
  /-- Quarter site at each integer position. -/
  quarter : ℤ → ℤ → QuarterIndex
  /-- Horizontal matching in the subdivided alphabet. -/
  horizontal : ∀ x y,
    (quarterTile (quarter x y)).right = (quarterTile (quarter (x + 1) y)).left
  /-- Vertical matching in the subdivided alphabet. -/
  vertical : ∀ x y,
    (quarterTile (quarter x y)).top = (quarterTile (quarter x (y + 1))).bottom

private def eastPhase : Quadrant → Quadrant
  | .southwest => .southeast
  | .southeast => .southwest
  | .northwest => .northeast
  | .northeast => .northwest

private def northPhase : Quadrant → Quadrant
  | .southwest => .northwest
  | .southeast => .northeast
  | .northwest => .southwest
  | .northeast => .southeast

private theorem phase_east (P : Plane) (x y : ℤ) :
    (P.quarter (x + 1) y).quadrant = eastPhase (P.quarter x y).quadrant := by
  have h := (TileSubdivision.horizontal_iff
    (Robinson.tile (components (P.quarter x y).index))
    (Robinson.tile (components (P.quarter (x + 1) y).index))
    (P.quarter x y).quadrant (P.quarter (x + 1) y).quadrant).mp (P.horizontal x y)
  cases hl : (P.quarter x y).quadrant <;>
    cases hr : (P.quarter (x + 1) y).quadrant <;> simp_all [eastPhase]

private theorem phase_north (P : Plane) (x y : ℤ) :
    (P.quarter x (y + 1)).quadrant = northPhase (P.quarter x y).quadrant := by
  have h := (TileSubdivision.vertical_iff
    (Robinson.tile (components (P.quarter x y).index))
    (Robinson.tile (components (P.quarter x (y + 1)).index))
    (P.quarter x y).quadrant (P.quarter x (y + 1)).quadrant).mp (P.vertical x y)
  cases hl : (P.quarter x y).quadrant <;>
    cases hr : (P.quarter x (y + 1)).quadrant <;> simp_all [northPhase]

private theorem phase_even (P : Plane) (x y u v : ℤ) :
    (P.quarter (x + 2 * u) (y + 2 * v)).quadrant = (P.quarter x y).quadrant := by
  have ee (q : Quadrant) : eastPhase (eastPhase q) = q := by cases q <;> rfl
  have nn (q : Quadrant) : northPhase (northPhase q) = q := by cases q <;> rfl
  have east (a b : ℤ) : (P.quarter (a + 2) b).quadrant = (P.quarter a b).quadrant := by
    have h := phase_east P (a + 1) b
    rw [phase_east P a b] at h
    simpa only [add_assoc, Int.reduceAdd, ee] using h
  have north (a b : ℤ) : (P.quarter a (b + 2)).quadrant = (P.quarter a b).quadrant := by
    have h := phase_north P a (b + 1)
    rw [phase_north P a b] at h
    simpa only [add_assoc, Int.reduceAdd, nn] using h
  have hx : Function.Periodic
      (fun a : ℤ => (P.quarter (x + a) (y + 2 * v)).quadrant) 2 := by
    intro a
    simpa only [← add_assoc] using east (x + a) (y + 2 * v)
  have hy : Function.Periodic (fun b : ℤ => (P.quarter x (y + b)).quadrant) 2 := by
    intro b
    simpa only [← add_assoc] using north x (y + b)
  calc
    _ = (P.quarter x (y + 2 * v)).quadrant := by
      simpa only [Int.cast_id, mul_comm, add_zero] using hx.int_mul_eq u
    _ = (P.quarter x y).quadrant := by
      simpa only [Int.cast_id, mul_comm, add_zero] using hy.int_mul_eq v

private theorem exists_origin (P : Plane) :
    ∃ x y : ℤ, (P.quarter x y).quadrant = .southwest := by
  have he := phase_east P 0 0
  have hn := phase_north P 0 0
  have hen := phase_north P 1 0
  cases h : (P.quarter 0 0).quadrant with
  | southwest => exact ⟨0, 0, h⟩
  | southeast => exact ⟨1, 0, by simpa [h, eastPhase] using he⟩
  | northwest => exact ⟨0, 1, by simpa [h, northPhase] using hn⟩
  | northeast =>
    have h₁ : (P.quarter 1 0).quadrant = .northwest := by
      simpa [h, eastPhase] using he
    exact ⟨1, 1, by simpa [h₁, northPhase] using hen⟩

private theorem internal_horizontal {a b : QuarterIndex}
    (hphase : a.quadrant.xBit = false)
    (hmatch : (quarterTile a).right = (quarterTile b).left) : a.index = b.index := by
  have h := (TileSubdivision.horizontal_iff (Robinson.tile (components a.index))
    (Robinson.tile (components b.index)) a.quadrant b.quadrant).mp hmatch
  cases ha : a.quadrant <;> cases hb : b.quadrant <;>
    simp_all [Quadrant.xBit, parentTile_injective.eq_iff]

private theorem internal_vertical {a b : QuarterIndex}
    (hphase : a.quadrant.yBit = false)
    (hmatch : (quarterTile a).top = (quarterTile b).bottom) : a.index = b.index := by
  have h := (TileSubdivision.vertical_iff (Robinson.tile (components a.index))
    (Robinson.tile (components b.index)) a.quadrant b.quadrant).mp hmatch
  cases ha : a.quadrant <;> cases hb : b.quadrant <;>
    simp_all [Quadrant.yBit, parentTile_injective.eq_iff]

private theorem block_spec (P : Plane) {x y : ℤ}
    (hphase : (P.quarter x y).quadrant = .southwest) :
    P.quarter x y = ⟨(P.quarter x y).index, .southwest⟩ ∧
    P.quarter (x + 1) y = ⟨(P.quarter x y).index, .southeast⟩ ∧
    P.quarter x (y + 1) = ⟨(P.quarter x y).index, .northwest⟩ ∧
    P.quarter (x + 1) (y + 1) = ⟨(P.quarter x y).index, .northeast⟩ := by
  have he : (P.quarter (x + 1) y).quadrant = .southeast :=
    (phase_east P x y).trans (by rw [hphase]; rfl)
  have hn : (P.quarter x (y + 1)).quadrant = .northwest :=
    (phase_north P x y).trans (by rw [hphase]; rfl)
  have hen : (P.quarter (x + 1) (y + 1)).quadrant = .northeast :=
    (phase_east P x (y + 1)).trans (by rw [hn]; rfl)
  have hie := internal_horizontal (by rw [hphase]; rfl) (P.horizontal x y)
  have hin := internal_vertical (by rw [hphase]; rfl) (P.vertical x y)
  have hien := internal_horizontal (by rw [hn]; rfl) (P.horizontal x (y + 1))
  have eq (q : QuarterIndex) (i : Index) (r : Quadrant)
      (hi : q.index = i) (hr : q.quadrant = r) : q = ⟨i, r⟩ := by
    cases q
    simp_all
  exact ⟨eq _ _ _ rfl hphase, eq _ _ _ hie.symm he,
    eq _ _ _ hin.symm hn, eq _ _ _ (hien.symm.trans hin.symm) hen⟩

/-- An exact regrouping of a quarter plane into matching corrected parent tiles. -/
structure Regrouped (Q : Plane) where
  /-- Southwest corner of the parent at the origin. -/
  origin : ℤ × ℤ
  /-- The matching corrected parent plane. -/
  parent : Robinson.Plane
  /-- All four quarters in every parent block have that parent index and the expected phase. -/
  blocks : ∀ x y,
    Q.quarter (origin.1 + 2 * x) (origin.2 + 2 * y) =
      ⟨parent.index x y, .southwest⟩ ∧
    Q.quarter (origin.1 + 2 * x + 1) (origin.2 + 2 * y) =
      ⟨parent.index x y, .southeast⟩ ∧
    Q.quarter (origin.1 + 2 * x) (origin.2 + 2 * y + 1) =
      ⟨parent.index x y, .northwest⟩ ∧
    Q.quarter (origin.1 + 2 * x + 1) (origin.2 + 2 * y + 1) =
      ⟨parent.index x y, .northeast⟩

/-- Matching subdivision phases fix a global alignment; internal seams recover each parent. -/
noncomputable def regroup (Q : Plane) : Regrouped Q := by
  classical
  let ox := Classical.choose (exists_origin Q)
  let oy := Classical.choose (Classical.choose_spec (exists_origin Q))
  have origin : (Q.quarter ox oy).quadrant = .southwest :=
    Classical.choose_spec (Classical.choose_spec (exists_origin Q))
  let index x y := (Q.quarter (ox + 2 * x) (oy + 2 * y)).index
  have blocks x y := block_spec Q ((phase_even Q ox oy x y).trans origin)
  let parent : Robinson.Plane := {
    index := index
    horizontal := by
      intro x y
      have h := Q.horizontal (ox + 2 * x + 1) (oy + 2 * y)
      have he : ox + 2 * x + 1 + 1 = ox + 2 * (x + 1) := by omega
      rw [(blocks x y).2.1, he, (blocks (x + 1) y).1] at h
      exact (TileSubdivision.horizontal_iff _ _ .southeast .southwest).mp h
    vertical := by
      intro x y
      have h := Q.vertical (ox + 2 * x) (oy + 2 * y + 1)
      have hn : oy + 2 * y + 1 + 1 = oy + 2 * (y + 1) := by omega
      rw [(blocks x y).2.2.1, hn, (blocks x (y + 1)).1] at h
      exact (TileSubdivision.vertical_iff _ _ .northwest .southwest).mp h }
  exact ⟨(ox, oy), parent, blocks⟩

end Quarters


namespace Signals

-- Expose the equality computation used by downstream finite signal certificates.
@[expose] public section
/-- Direction relative to the positive coordinate direction of an edge. -/
inductive Flow where
  | none | forward | backward
  deriving DecidableEq
end

namespace Flow

/-- Numerical signal edge code: no signal, positive signal, negative signal. -/
private def code : Flow → ℕ
  | .none => 0
  | .forward => 1
  | .backward => 2

@[simp] private theorem code_eq_zero {f : Flow} : f.code = 0 ↔ f = .none := by
  cases f <;> simp [code]

/-- Distinct signal directions have distinct edge colours. -/
private theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp_all [code]

private def all : List Flow := [.none, .forward, .backward]

private theorem mem_all (f : Flow) : f ∈ all := by cases f <;> decide

end Flow

/-- Directed obstruction signals on the four edges of a quarter tile. -/
structure State where
  /-- West-edge flow. -/
  west : Flow
  /-- East-edge flow. -/
  east : Flow
  /-- South-edge flow. -/
  south : Flow
  /-- North-edge flow. -/
  north : Flow
  deriving DecidableEq

/-- The state with all four signal directions absent. -/
@[expose] def clearState : State := ⟨.none, .none, .none, .none⟩

private def State.all : List State :=
  Flow.all.flatMap fun west => Flow.all.flatMap fun east =>
    Flow.all.flatMap fun south => Flow.all.map fun north => ⟨west, east, south, north⟩

private theorem State.mem_all (s : State) : s ∈ State.all := by
  cases s
  simp [State.all, Flow.mem_all]

/-- The one-dimensional obstruction rule. A positive interior is east or north. -/
@[expose] def flowAllowed (interior : Option Bool) (before after : Flow) : Bool :=
  match interior with
  | none => decide (before = after)
  | some true => decide (before ≠ .none ∧ after ≠ .forward)
  | some false => decide (after ≠ .none ∧ before ≠ .backward)

/-- Code west as negative and east as positive; absence remains absent. -/
@[expose] def horizontalInteriorCode : Option HorizontalInterior → Option Bool
  | none => none
  | some .west => some false
  | some .east => some true

/-- Code south as negative and north as positive; absence remains absent. -/
@[expose] def verticalInteriorCode : Option VerticalInterior → Option Bool
  | none => none
  | some .south => some false
  | some .north => some true

/-- Apply the common obstruction rule to the two horizontal edges. -/
@[expose] def horizontalAllowed (interior : Option HorizontalInterior) (s : State) : Bool :=
  flowAllowed (horizontalInteriorCode interior) s.west s.east

/-- Apply the common obstruction rule to the two vertical edges. -/
@[expose] def verticalAllowed (interior : Option VerticalInterior) (s : State) : Bool :=
  flowAllowed (verticalInteriorCode interior) s.south s.north

end Signals

namespace ShadedSignals

open Quarters

/-- The horizontal and vertical obstruction rules for the selected light borders. -/
@[expose] def locallyAllowed (quarter : QuarterIndex) (shade : RedShades.State)
    (signal : Signals.State) : Bool :=
  Signals.horizontalAllowed
      (selectedVerticalFor (components quarter.index).thick quarter.quadrant shade) signal &&
    Signals.verticalAllowed
      (selectedHorizontalFor (components quarter.index).thick quarter.quadrant shade) signal

/-- A decorated site has independent quarter, red-shade and obstruction-signal components.
Admissibility is checked when forming the finite palette. -/
structure Site where
  /-- The corrected tile and its quadrant. -/
  quarter : QuarterIndex
  /-- The light/dark decoration of its red paths. -/
  shade : RedShades.State
  /-- Its directed obstruction signals. -/
  signal : Signals.State
  deriving DecidableEq

private def shadeCode : Option RedShades.Shade → ℕ
  | none => 0
  | some .light => 1
  | some .dark => 2

private theorem shadeCode_injective : Function.Injective shadeCode := by
  intro a b h
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · cases b <;> simp [shadeCode] at h
  · cases a <;> simp [shadeCode] at h
  · cases a <;> cases b <;> simp_all [shadeCode]

private def shadeTile (s : RedShades.State) : WangTile :=
  ⟨shadeCode s.north, shadeCode s.south, shadeCode s.west, shadeCode s.east⟩

private def signalTile (s : Signals.State) : WangTile :=
  ⟨s.north.code, s.south.code, s.west.code, s.east.code⟩

/-- Each edge pairs the quarter colour with the shade code, then with the signal code. -/
def tile (s : Site) : WangTile :=
  layer (layer (quarterTile s.quarter) (shadeTile s.shade)) (signalTile s.signal)

private def allSites : List Site :=
  (List.finRange 104).flatMap fun index =>
    Quadrant.all.flatMap fun quadrant =>
      (RedShades.State.all.filter fun shade =>
        RedShades.locallyAllowed ⟨index, quadrant⟩ shade).flatMap fun shade =>
          (Signals.State.all.filter fun signal =>
            locallyAllowed ⟨index, quadrant⟩ shade signal).map fun signal =>
              ⟨⟨index, quadrant⟩, shade, signal⟩

private theorem mem_allSites (s : Site) :
    s ∈ allSites ↔ RedShades.locallyAllowed s.quarter s.shade = true ∧
      locallyAllowed s.quarter s.shade s.signal = true := by
  rcases s with ⟨⟨index, quadrant⟩, shade, signal⟩
  simp [allSites, Quadrant.mem_all, Signals.State.mem_all]

/-- Horizontal matching means quarter matching and equality of both decorations. -/
theorem horizontal_iff (a b : Site) :
    (tile a).right = (tile b).left ↔
      (quarterTile a.quarter).right = (quarterTile b.quarter).left ∧
      a.shade.east = b.shade.west ∧ a.signal.east = b.signal.west := by
  simp [tile, layer, shadeTile, signalTile, Nat.pair_eq_pair,
    shadeCode_injective.eq_iff, Signals.Flow.code_injective.eq_iff, and_assoc]

/-- Vertical matching means quarter matching and equality of both decorations. -/
theorem vertical_iff (a b : Site) :
    (tile a).top = (tile b).bottom ↔
      (quarterTile a.quarter).top = (quarterTile b.quarter).bottom ∧
      a.shade.north = b.shade.south ∧ a.signal.north = b.signal.south := by
  simp [tile, layer, shadeTile, signalTile, Nat.pair_eq_pair,
    shadeCode_injective.eq_iff, Signals.Flow.code_injective.eq_iff, and_assoc]

private theorem shadeTile_injective : Function.Injective shadeTile := by
  rintro ⟨aw, ae, aso, an⟩ ⟨bw, be, bso, bn⟩ h
  simp only [shadeTile, WangTile.mk.injEq, shadeCode_injective.eq_iff] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

private theorem signalTile_injective : Function.Injective signalTile := by
  rintro ⟨aw, ae, aso, an⟩ ⟨bw, be, bso, bn⟩ h
  simp only [signalTile, WangTile.mk.injEq, Signals.Flow.code_injective.eq_iff] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

/-- The finite edge coding retains the quarter and both decoration states. -/
theorem tile_injective : Function.Injective tile := by
  rintro ⟨aq, ash, asi⟩ ⟨bq, bsh, bsi⟩ h
  have hparts := layer_eq_layer_iff.mp h
  have hbase := layer_eq_layer_iff.mp hparts.1
  have hq := Quarters.quarterTile_injective hbase.1
  have hs := shadeTile_injective hbase.2
  have hi := signalTile_injective hparts.2
  cases hq; cases hs; cases hi
  rfl

private def horizontalClear (t : WangTile) : Bool :=
  decide ((Nat.unpair t.left).2 = 0 ∧ (Nat.unpair t.right).2 = 0)

private def verticalClear (t : WangTile) : Bool :=
  decide ((Nat.unpair t.bottom).2 = 0 ∧ (Nat.unpair t.top).2 = 0)

private def quarterLayer (t : WangTile) : WangTile :=
  ⟨(Nat.unpair (Nat.unpair t.top).1).1, (Nat.unpair (Nat.unpair t.bottom).1).1,
    (Nat.unpair (Nat.unpair t.left).1).1, (Nat.unpair (Nat.unpair t.right).1).1⟩

/-- The effective role decoder. Clear crossings at index zero's northeast quarter carry the seed. -/
def routeRole (t : WangTile) : RouteRole :=
  if horizontalClear t then
    if verticalClear t then
      if quarterLayer t = quarterTile ⟨0, .northeast⟩ then .corner else .active
    else .horizontal
  else if verticalClear t then .vertical else .inactive

/-- The local role is computed from the two clear directions and the unique marker quarter. -/
theorem routeRole_tile (s : Site) :
    routeRole (tile s) =
      if s.signal.west = .none ∧ s.signal.east = .none then
        if s.signal.south = .none ∧ s.signal.north = .none then
          if s.quarter = ⟨0, .northeast⟩ then .corner else .active
        else .horizontal
      else if s.signal.south = .none ∧ s.signal.north = .none then .vertical else .inactive := by
  simp [routeRole, horizontalClear, verticalClear, quarterLayer, tile, layer,
    signalTile, Quarters.quarterTile_injective.eq_iff]

/-- A site carries horizontal data exactly when both horizontal signal edges are clear. -/
theorem horizontalCarrier_iff (s : Site) :
    (routeRole (tile s)).horizontalCarrier = true ↔
      s.signal.west = .none ∧ s.signal.east = .none := by
  rw [routeRole_tile]
  split_ifs <;> simp_all [RouteRole.horizontalCarrier]

/-- A site carries vertical data exactly when both vertical signal edges are clear. -/
theorem verticalCarrier_iff (s : Site) :
    (routeRole (tile s)).verticalCarrier = true ↔
      s.signal.south = .none ∧ s.signal.north = .none := by
  rw [routeRole_tile]
  split_ifs <;> simp_all [RouteRole.verticalCarrier]

/-- The unique seeded role is an all-clear northeast quarter of corrected index zero. -/
theorem corner_iff (s : Site) :
    routeRole (tile s) = .corner ↔
      s.signal = Signals.clearState ∧ s.quarter = ⟨0, .northeast⟩ := by
  rcases s with ⟨q, sh, ⟨w, e, so, no⟩⟩
  rw [routeRole_tile]
  simp only [Signals.clearState, Signals.State.mk.injEq]
  split_ifs <;> simp_all

/-- Horizontal wire cells have clear horizontal signals and a blocked vertical direction. -/
theorem horizontal_iff_role (s : Site) :
    routeRole (tile s) = .horizontal ↔
      (s.signal.west = .none ∧ s.signal.east = .none) ∧
        ¬ (s.signal.south = .none ∧ s.signal.north = .none) := by
  rw [routeRole_tile]
  split_ifs <;> simp_all

/-- Vertical wire cells have a blocked horizontal direction and clear vertical signals. -/
theorem vertical_iff_role (s : Site) :
    routeRole (tile s) = .vertical ↔
      ¬ (s.signal.west = .none ∧ s.signal.east = .none) ∧
        s.signal.south = .none ∧ s.signal.north = .none := by
  rw [routeRole_tile]
  split_ifs <;> simp_all

/-- Simultaneous clear directions give a crossing, possibly the seeded crossing. -/
theorem crossing_iff (s : Site) :
    (routeRole (tile s) = .active ∨ routeRole (tile s) = .corner) ↔
      s.signal = Signals.clearState := by
  rcases s with ⟨q, sh, ⟨w, e, so, no⟩⟩
  rw [routeRole_tile]
  simp only [Signals.clearState, Signals.State.mk.injEq]
  split_ifs <;> simp_all

/-- The role decoder is primitive recursive on the given Wang-tile coding. -/
theorem primrec_routeRole : Primrec routeRole := by
  have unpairLeft : Primrec (fun n : ℕ => (Nat.unpair n).1) :=
    Primrec.fst.comp Primrec.unpair
  have unpairRight : Primrec (fun n : ℕ => (Nat.unpair n).2) :=
    Primrec.snd.comp Primrec.unpair
  have hc : Primrec horizontalClear := by
    apply PrimrecPred.decide
    exact (Primrec.eq.comp (unpairRight.comp primrec_left) (Primrec.const 0)).and
      (Primrec.eq.comp (unpairRight.comp primrec_right) (Primrec.const 0))
  have vc : Primrec verticalClear := by
    apply PrimrecPred.decide
    exact (Primrec.eq.comp (unpairRight.comp primrec_bottom) (Primrec.const 0)).and
      (Primrec.eq.comp (unpairRight.comp primrec_top) (Primrec.const 0))
  have hq : Primrec quarterLayer :=
    primrec_mk (unpairLeft.comp (unpairLeft.comp primrec_top))
      (unpairLeft.comp (unpairLeft.comp primrec_bottom))
      (unpairLeft.comp (unpairLeft.comp primrec_left))
      (unpairLeft.comp (unpairLeft.comp primrec_right))
  exact Primrec.ite (Primrec.eq.comp hc (Primrec.const true))
    (Primrec.ite (Primrec.eq.comp vc (Primrec.const true))
      (Primrec.ite (Primrec.eq.comp hq (Primrec.const _))
        (Primrec.const RouteRole.corner) (Primrec.const RouteRole.active))
      (Primrec.const RouteRole.horizontal))
    (Primrec.ite (Primrec.eq.comp vc (Primrec.const true))
      (Primrec.const RouteRole.vertical) (Primrec.const RouteRole.inactive))

end ShadedSignals

/-- The corrected shaded Robinson obstruction scaffold with its effective payload roles. -/
def scaffold : RoutedScaffold where
  tiles := ShadedSignals.allSites.map ShadedSignals.tile
  role := ShadedSignals.routeRole
  role_primrec := ShadedSignals.primrec_routeRole

/-- The scaffold uses the concrete clear-edge role decoder. -/
@[simp] theorem scaffold_role : scaffold.role = ShadedSignals.routeRole := by rfl

namespace ShadedSignals

/-- Scaffold membership is exactly local shade and signal admissibility. -/
theorem mem_scaffold {t : WangTile} :
    t ∈ scaffold.tiles ↔ ∃ s : Site,
      RedShades.locallyAllowed s.quarter s.shade = true ∧
      locallyAllowed s.quarter s.shade s.signal = true ∧ tile s = t := by
  simp [scaffold, mem_allSites, and_assoc]

/-- A locally admissible decorated site belongs to the concrete scaffold. -/
theorem tile_mem (s : Site)
    (hshade : RedShades.locallyAllowed s.quarter s.shade = true)
    (hsignal : locallyAllowed s.quarter s.shade s.signal = true) :
    tile s ∈ scaffold.tiles :=
  mem_scaffold.mpr ⟨s, hshade, hsignal, rfl⟩

/-- The semantic content of a scaffold plane; all components retain their shared-edge rules. -/
structure Decoded (P : Cslib.WangTile.Plane scaffold.tiles) where
  /-- The three components at each position. -/
  site : ℤ → ℤ → Site
  /-- The components encode the original tile. -/
  tile_eq : ∀ x y, tile (site x y) = P.tile x y
  /-- Local shade rules. -/
  shadeAllowed : ∀ x y,
    RedShades.locallyAllowed (site x y).quarter (site x y).shade = true
  /-- Local obstruction rules. -/
  signalAllowed : ∀ x y,
    locallyAllowed (site x y).quarter (site x y).shade (site x y).signal = true
  /-- Quarter and both decoration edges match horizontally. -/
  horizontal : ∀ x y,
    (Quarters.quarterTile (site x y).quarter).right =
        (Quarters.quarterTile (site (x + 1) y).quarter).left ∧
      (site x y).shade.east = (site (x + 1) y).shade.west ∧
      (site x y).signal.east = (site (x + 1) y).signal.west
  /-- Quarter and both decoration edges match vertically. -/
  vertical : ∀ x y,
    (Quarters.quarterTile (site x y).quarter).top =
        (Quarters.quarterTile (site x (y + 1)).quarter).bottom ∧
      (site x y).shade.north = (site x (y + 1)).shade.south ∧
      (site x y).signal.north = (site x (y + 1)).signal.south

/-- Decode any ordinary scaffold plane; no choice of special plane or hierarchy is assumed. -/
noncomputable def decode (P : Cslib.WangTile.Plane scaffold.tiles) : Decoded P := by
  classical
  choose s hs ht he using fun x y => mem_scaffold.mp (P.mem x y)
  refine ⟨s, he, hs, ht, ?_, ?_⟩
  · intro x y
    apply (horizontal_iff _ _).mp
    rw [he, he]
    exact P.horizontal x y
  · intro x y
    apply (vertical_iff _ _).mp
    rw [he, he]
    exact P.vertical x y

end ShadedSignals

namespace ShadedSignals.Decoded

/-- Forget decorations while retaining matching of quarter edges. -/
@[expose] def quarterPlane {P : Cslib.WangTile.Plane scaffold.tiles} (D : ShadedSignals.Decoded P) :
    Quarters.Plane where
  quarter x y := (D.site x y).quarter
  horizontal x y := (D.horizontal x y).1
  vertical x y := (D.vertical x y).1

end ShadedSignals.Decoded

namespace Quarters.Regrouped

/-- Regrouping describes every natural quarter coordinate above any parent origin. -/
theorem quarter_at {Q : Quarters.Plane} (R : Quarters.Regrouped Q)
    (a b : ℤ) (x y : ℕ) :
    Q.quarter (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y) =
      ⟨R.parent.index (a + (x / 2 : ℕ)) (b + (y / 2 : ℕ)),
        QuarterGeometry.quadrantAt x y⟩ := by
  have hx : R.origin.1 + 2 * a + x =
      R.origin.1 + 2 * (a + (x / 2 : ℕ)) + (x % 2 : ℕ) := by omega
  have hy : R.origin.2 + 2 * b + y =
      R.origin.2 + 2 * (b + (y / 2 : ℕ)) + (y % 2 : ℕ) := by omega
  have blocks := R.blocks (a + (x / 2 : ℕ)) (b + (y / 2 : ℕ))
  rw [hx, hy]
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy
  · simpa [hx, hy, QuarterGeometry.quadrantAt, Quadrant.ofBits] using blocks.1
  · simpa [hx, hy, QuarterGeometry.quadrantAt, Quadrant.ofBits] using blocks.2.2.1
  · simpa [hx, hy, QuarterGeometry.quadrantAt, Quadrant.ofBits] using blocks.2.1
  · simpa [hx, hy, QuarterGeometry.quadrantAt, Quadrant.ofBits] using blocks.2.2.2

end Quarters.Regrouped

namespace ShadedSignals

/-- Compatible shade and signal assignments on the natural quarter grid of an indexed plane. -/
structure ValidGrid (indexGrid : ℕ → ℕ → Index)
    (shadeGrid : ℕ → ℕ → RedShades.State) (signalGrid : ℕ → ℕ → Signals.State) : Prop where
  /-- Local incidence, propagation and matching of the shades. -/
  shadeValid : RedShadePaths.ValidShadeGrid indexGrid shadeGrid
  /-- Both signal directions obey the selected light-border rules. -/
  signalAllowed : ∀ x y,
    locallyAllowed ⟨indexGrid (x / 2) (y / 2), QuarterGeometry.quadrantAt x y⟩
      (shadeGrid x y) (signalGrid x y) = true
  /-- Horizontal signal edges match. -/
  horizontal : ∀ x y, (signalGrid x y).east = (signalGrid (x + 1) y).west
  /-- Vertical signal edges match. -/
  vertical : ∀ x y, (signalGrid x y).north = (signalGrid x (y + 1)).south

namespace Decoded

/-- Restrict a decoded plane to natural quarter coordinates above a chosen parent origin. -/
@[expose] def siteGrid {P : Cslib.WangTile.Plane scaffold.tiles} (D : Decoded P)
    (R : Quarters.Regrouped D.quarterPlane) (a b : ℤ) (x y : ℕ) : Site :=
  D.site (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)

/-- Both decorations of an arbitrary decoded plane remain valid on its regrouped quarter grid. -/
theorem validGrid {P : Cslib.WangTile.Plane scaffold.tiles} (D : Decoded P)
    (R : Quarters.Regrouped D.quarterPlane) (a b : ℤ) :
    ValidGrid (fun i j => R.parent.index (a + i) (b + j))
      (fun x y => (D.siteGrid R a b x y).shade)
      (fun x y => (D.siteGrid R a b x y).signal) := by
  have quarter x y :
      (D.siteGrid R a b x y).quarter =
        ⟨R.parent.index (a + (x / 2 : ℕ)) (b + (y / 2 : ℕ)),
          QuarterGeometry.quadrantAt x y⟩ :=
    R.quarter_at a b x y
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y
    have h := D.shadeAllowed (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)
    change RedShades.locallyAllowed (D.siteGrid R a b x y).quarter
      (D.siteGrid R a b x y).shade = true at h
    rwa [quarter] at h
  · intro x y
    simpa [siteGrid, Nat.cast_add, Nat.cast_one, add_assoc] using
      (D.horizontal (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)).2.1
  · intro x y
    simpa [siteGrid, Nat.cast_add, Nat.cast_one, add_assoc] using
      (D.vertical (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)).2.1
  · intro x y
    have h := D.signalAllowed (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)
    change locallyAllowed (D.siteGrid R a b x y).quarter
      (D.siteGrid R a b x y).shade (D.siteGrid R a b x y).signal = true at h
    rwa [quarter] at h
  · intro x y
    simpa [siteGrid, Nat.cast_add, Nat.cast_one, add_assoc] using
      (D.horizontal (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)).2.2
  · intro x y
    simpa [siteGrid, Nat.cast_add, Nat.cast_one, add_assoc] using
      (D.vertical (R.origin.1 + 2 * a + x) (R.origin.2 + 2 * b + y)).2.2

end Decoded
end ShadedSignals

end Cslib.WangTile.Robinson
