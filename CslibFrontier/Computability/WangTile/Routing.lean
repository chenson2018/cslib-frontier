/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Pointed
public import CslibFrontier.Computability.WangTile.Compactness

/-!
# Routed scaffolds and generic seed removal

A finite scaffold assigns a routing role to each tile. Pairing its edge colours with payload
colours lets crossings carry payload tiles and wires transmit one colour. Inactive edges use
zero or a colour occurring in the payload palette.

## Main definitions

* `RouteRole`, `RoutedScaffold`, `combine`: the finite routed construction.
* `Plane`, `RoutedPlane`, `RoutedGrid`: matching planes and finite grids of crossings and wires.
* `AddressedSquare`: a matching scaffold patch with compatible integer payload addresses.
* `Forces`, `Realizes`: the two geometric obligations for seed removal.

## Main results

* `primrec_combine`: the finite combination is primitive recursive.
* `tilesPlane_combine_pointedExtension_iff_of_forces_of_realizes`: the generic seed-removal
  step, conditional on both obligations. This is not the domino undecidability theorem.

## References

Restructured from [lean-wang, revision 64268a3, routed scaffolds](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Scaffold/Routed.lean)
and its `PointedCarrierAddressing` and `PointedPlane` modules. The construction is a step of
the Robinson seed-removal argument [Robinson1971]; no concrete scaffold obligations are assumed
proved here.
-/

public section

namespace Cslib.WangTile

/-- A tile's payload role: unconstrained, a wire, a crossing, or a seeded crossing. -/
inductive RouteRole where
  | inactive | horizontal | vertical | active | corner
  deriving DecidableEq

/-- Finite role coding: no role, or two bits selecting a wire or crossing. -/
def RouteRole.equivCode : RouteRole ≃ Option (Bool × Bool) where
  toFun
    | .inactive => none
    | .horizontal => some (false, false)
    | .vertical => some (false, true)
    | .active => some (true, false)
    | .corner => some (true, true)
  invFun
    | none => .inactive
    | some (false, false) => .horizontal
    | some (false, true) => .vertical
    | some (true, false) => .active
    | some (true, true) => .corner
  left_inv r := by cases r <;> rfl
  right_inv c := by
    rcases c with _ | ⟨a, b⟩
    · rfl
    · cases a <;> cases b <;> rfl

instance : Primcodable RouteRole := Primcodable.ofEquiv _ RouteRole.equivCode

/-- Whether the role prescribes horizontal payload data. -/
@[expose] def RouteRole.horizontalCarrier : RouteRole → Bool
  | .horizontal | .active | .corner => true
  | _ => false

/-- Whether the role prescribes vertical payload data. -/
@[expose] def RouteRole.verticalCarrier : RouteRole → Bool
  | .vertical | .active | .corner => true
  | _ => false

/-- A finite scaffold with a primitive-recursive routing-role decoder. -/
structure RoutedScaffold where
  /-- The finite scaffold alphabet. -/
  tiles : List WangTile
  /-- The payload role attached to a scaffold tile. -/
  role : WangTile → RouteRole
  /-- The decoder is effective on natural-number tile codes. -/
  role_primrec : Primrec role

/-- Pair scaffold and payload colours on each edge, in that order. -/
@[expose] def layer (base payload : WangTile) : WangTile :=
  ⟨Nat.pair base.top payload.top, Nat.pair base.bottom payload.bottom,
    Nat.pair base.left payload.left, Nat.pair base.right payload.right⟩

private def palette (τ : List WangTile) : List ℕ :=
  0 :: τ.flatMap fun t => [t.top, t.bottom, t.left, t.right]

/-- All tiles whose four colours are zero or occur on some payload tile. -/
def completePayloads (τ : List WangTile) : List WangTile :=
  let c := palette τ
  c.flatMap fun top => c.flatMap fun bottom => c.flatMap fun left =>
    c.map fun right => ⟨top, bottom, left, right⟩

/-- Payloads allowed at a scaffold tile. Corners require the seed to belong to the palette. -/
def routedPayloads (S : RoutedScaffold) (I : SeededInstance) (base : WangTile) :
    List WangTile :=
  match S.role base with
  | .inactive => completePayloads I.tiles
  | .horizontal => (completePayloads I.tiles).filter fun p => p.left = p.right
  | .vertical => (completePayloads I.tiles).filter fun p => p.bottom = p.top
  | .active => I.tiles
  | .corner => I.tiles.filter fun p => p = I.seed

/-- Finite routed combination, with scaffold colour first in each `Nat.pair` edge code. -/
def combine (S : RoutedScaffold) (I : SeededInstance) : List WangTile :=
  S.tiles.flatMap fun base => (routedPayloads S I base).map (layer base)

/-- Membership exposes the two finite layers and the local payload constraint. -/
theorem mem_combine {S : RoutedScaffold} {I : SeededInstance} {t : WangTile} :
    t ∈ combine S I ↔ ∃ b ∈ S.tiles, ∃ p ∈ routedPayloads S I b, layer b p = t := by
  simp [combine]

private theorem mem_completePayloads {τ : List WangTile} {p : WangTile} :
    p ∈ completePayloads τ ↔ p.top ∈ palette τ ∧ p.bottom ∈ palette τ ∧
      p.left ∈ palette τ ∧ p.right ∈ palette τ := by
  cases p
  simp [completePayloads]

private theorem mem_completePayloads_of_mem {τ : List WangTile} {p : WangTile}
    (hp : p ∈ τ) : p ∈ completePayloads τ := by
  rw [mem_completePayloads]
  have edges (c : ℕ) (hc : c ∈ [p.top, p.bottom, p.left, p.right]) : c ∈ palette τ :=
    List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩)
  exact ⟨edges _ (by simp), edges _ (by simp), edges _ (by simp), edges _ (by simp)⟩

/-- The local role constraint, with explicit finite colour bounds on inactive edges. -/
theorem mem_routedPayloads {S : RoutedScaffold} {I : SeededInstance} {b p : WangTile} :
    p ∈ routedPayloads S I b ↔
      match S.role b with
      | .inactive => p ∈ completePayloads I.tiles
      | .horizontal => p ∈ completePayloads I.tiles ∧ p.left = p.right
      | .vertical => p ∈ completePayloads I.tiles ∧ p.bottom = p.top
      | .active => p ∈ I.tiles
      | .corner => p ∈ I.tiles ∧ p = I.seed := by
  cases h : S.role b <;> simp [routedPayloads, h]

private theorem primrec_completePayloads : Primrec completePayloads := by
  have hc : Primrec palette :=
    Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_flatMap Primrec.id
      (Primrec₂.mk ((Primrec.list_cons.comp primrec_top
        (Primrec.list_cons.comp primrec_bottom (Primrec.list_cons.comp primrec_left
          (Primrec.list_cons.comp primrec_right (Primrec.const []))))).comp Primrec.snd)))
  unfold completePayloads
  refine Primrec.list_flatMap hc (Primrec₂.mk ?_)
  refine Primrec.list_flatMap (hc.comp Primrec.fst) (Primrec₂.mk ?_)
  refine Primrec.list_flatMap (hc.comp (Primrec.fst.comp Primrec.fst)) (Primrec₂.mk ?_)
  refine Primrec.list_map (hc.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec₂.mk ?_)
  exact primrec_mk (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.snd.comp Primrec.fst) Primrec.snd

/-- The combination can be computed by primitive recursion on the seeded instance code. -/
theorem primrec_combine (S : RoutedScaffold) : Primrec (combine S) := by
  have hp (b : WangTile) : Primrec (fun I => routedPayloads S I b) := by
    cases h : S.role b
    · exact (primrec_completePayloads.comp SeededInstance.primrec_tiles).of_eq
        (by intro I; simp [routedPayloads, h])
    · exact ((Primrec.listFilter (Primrec.eq.comp primrec_left primrec_right)).comp
        (primrec_completePayloads.comp SeededInstance.primrec_tiles)).of_eq
          (by intro I; simp [routedPayloads, h])
    · exact ((Primrec.listFilter (Primrec.eq.comp primrec_bottom primrec_top)).comp
        (primrec_completePayloads.comp SeededInstance.primrec_tiles)).of_eq
          (by intro I; simp [routedPayloads, h])
    · exact SeededInstance.primrec_tiles.of_eq (by intro I; simp [routedPayloads, h])
    · exact ((PrimrecRel.listFilter Primrec.eq).comp SeededInstance.primrec_tiles
        SeededInstance.primrec_seed).of_eq (by intro I; simp [routedPayloads, h])
  have hl (b : WangTile) : Primrec (layer b) :=
    primrec_mk (Primrec₂.natPair.comp (Primrec.const b.top) primrec_top)
      (Primrec₂.natPair.comp (Primrec.const b.bottom) primrec_bottom)
      (Primrec₂.natPair.comp (Primrec.const b.left) primrec_left)
      (Primrec₂.natPair.comp (Primrec.const b.right) primrec_right)
  unfold combine
  induction S.tiles with
  | nil => exact Primrec.const []
  | cons b bs ih =>
    exact Primrec.list_append.comp
      (Primrec.list_map (hp b) (Primrec₂.mk ((hl b).comp Primrec.snd))) ih

/-- A matching plane, bundled for geometric constructions. This uses exactly `TilesPlane`. -/
structure Plane (τ : List WangTile) where
  /-- The tile at integer coordinates. -/
  tile : ℤ → ℤ → WangTile
  /-- Every tile belongs to the palette. -/
  mem : ∀ x y, tile x y ∈ τ
  /-- Horizontal matching. -/
  horizontal : ∀ x y, (tile x y).right = (tile (x + 1) y).left
  /-- Vertical matching. -/
  vertical : ∀ x y, (tile x y).top = (tile x (y + 1)).bottom

/-- The bundled and existential plane predicates describe the same tilings. -/
theorem nonempty_plane_iff (τ : List WangTile) : Nonempty (Plane τ) ↔ TilesPlane τ := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.tile, fun x y => ⟨p.mem x y, p.horizontal x y, p.vertical x y⟩⟩
  · rintro ⟨f, hf⟩
    exact ⟨⟨f, fun x y => (hf x y).1, fun x y => (hf x y).2.1,
      fun x y => (hf x y).2.2⟩⟩

/-- A matching routed plane separated into its scaffold and payload layers. -/
structure RoutedPlane (S : RoutedScaffold) (I : SeededInstance) where
  /-- The underlying scaffold plane. -/
  base : Plane S.tiles
  /-- The payload at each integer position. -/
  payload : ℤ → ℤ → WangTile
  /-- Payloads obey the local role. -/
  allowed : ∀ x y, payload x y ∈ routedPayloads S I (base.tile x y)
  /-- Horizontal payload matching. -/
  horizontal : ∀ x y, (payload x y).right = (payload (x + 1) y).left
  /-- Vertical payload matching. -/
  vertical : ∀ x y, (payload x y).top = (payload x (y + 1)).bottom

/-- Decode the two layers of a combined tiling; edge pairing preserves both matchings. -/
theorem nonempty_routedPlane_of_tilesPlane {S : RoutedScaffold} {I : SeededInstance}
    (h : TilesPlane (combine S I)) : Nonempty (RoutedPlane S I) := by
  classical
  obtain ⟨f, hf⟩ := h
  choose b hb p hp he using fun x y => mem_combine.mp (hf x y).1
  have hh x y := Nat.pair_eq_pair.mp (show
      Nat.pair (b x y).right (p x y).right =
        Nat.pair (b (x + 1) y).left (p (x + 1) y).left by
    simpa only [← he, layer] using (hf x y).2.1)
  have hv x y := Nat.pair_eq_pair.mp (show
      Nat.pair (b x y).top (p x y).top =
        Nat.pair (b x (y + 1)).bottom (p x (y + 1)).bottom by
    simpa only [← he, layer] using (hf x y).2.2)
  exact ⟨⟨⟨b, hb, fun x y => (hh x y).1, fun x y => (hv x y).1⟩,
    p, hp, fun x y => (hh x y).2, fun x y => (hv x y).2⟩⟩

/-- A finite grid whose crossings are linked by horizontal and vertical payload wires. -/
structure RoutedGrid (S : RoutedScaffold) (P : Plane S.tiles) (n : ℕ) where
  /-- Integer positions of consecutive selected columns. -/
  column : Fin (n + 1) → ℤ
  /-- Integer positions of consecutive selected rows. -/
  row : Fin (n + 1) → ℤ
  /-- Columns are strictly ordered. -/
  column_strictMono : StrictMono column
  /-- Rows are strictly ordered. -/
  row_strictMono : StrictMono row
  /-- Each selected intersection carries a payload tile. -/
  crossing : ∀ i j, S.role (P.tile (column i) (row j)) = .active ∨
    S.role (P.tile (column i) (row j)) = .corner
  /-- The southwest intersection carries the seed. -/
  corner : S.role (P.tile (column 0) (row 0)) = .corner
  /-- Every intervening cell on a selected row is a horizontal wire. -/
  horizontal : ∀ (i : Fin n) (j : Fin (n + 1)) (x : ℤ),
    column i.castSucc < x → x < column i.succ →
      S.role (P.tile x (row j)) = .horizontal
  /-- Every intervening cell on a selected column is a vertical wire. -/
  vertical : ∀ (i : Fin (n + 1)) (j : Fin n) (y : ℤ),
    row j.castSucc < y → y < row j.succ →
      S.role (P.tile (column i) y) = .vertical

/-- The logical address on the outgoing horizontal side of a carrier. -/
@[expose] def RouteRole.horizontalOutgoing (role : RouteRole) (point source : ℤ × ℤ) : ℤ × ℤ :=
  match role with
  | .active | .corner => point
  | .horizontal => source
  | _ => (0, 0)

/-- The logical address on the outgoing vertical side of a carrier. -/
@[expose] def RouteRole.verticalOutgoing (role : RouteRole) (point source : ℤ × ℤ) : ℤ × ℤ :=
  match role with
  | .active | .corner => point
  | .vertical => source
  | _ => (0, 0)

/-- A scaffold square with logical crossing and wire addresses. A wire transmits the outgoing
colour of its source. Entering the next crossing advances that address by one in the relevant
axis. Only pairs of cells carrying that axis impose an equation. -/
structure AddressedSquare (S : RoutedScaffold) (n : ℕ) where
  /-- The matching scaffold square, of side `n + 1`. -/
  base : Rectangle S.tiles (n + 1) (n + 1)
  /-- Logical payload coordinate at a crossing. -/
  point : Fin (n + 1) → Fin (n + 1) → ℤ × ℤ
  /-- Logical source of a horizontal wire's transmitted right colour. -/
  horizontalSource : Fin (n + 1) → Fin (n + 1) → ℤ × ℤ
  /-- Logical source of a vertical wire's transmitted top colour. -/
  verticalSource : Fin (n + 1) → Fin (n + 1) → ℤ × ℤ
  /-- All seeded crossings use the pointed payload's origin. -/
  corner_zero : ∀ i j, S.role (base.tile i j) = .corner → point i j = (0, 0)
  /-- Horizontal neighbors agree on the transmitted address. A crossing's incoming address
  is its point minus `(1, 0)`. -/
  hstep : ∀ i j (hi : i.val + 1 < n + 1),
    (S.role (base.tile i j)).horizontalCarrier = true →
    (S.role (base.tile ⟨i.val + 1, hi⟩ j)).horizontalCarrier = true →
    let outgoing := (S.role (base.tile i j)).horizontalOutgoing
      (point i j) (horizontalSource i j)
    match S.role (base.tile ⟨i.val + 1, hi⟩ j) with
    | .active | .corner => point ⟨i.val + 1, hi⟩ j = (outgoing.1 + 1, outgoing.2)
    | .horizontal => horizontalSource ⟨i.val + 1, hi⟩ j = outgoing
    | _ => False
  /-- Vertical neighbors agree on the transmitted address. A crossing's incoming address
  is its point minus `(0, 1)`. -/
  vstep : ∀ i j (hj : j.val + 1 < n + 1),
    (S.role (base.tile i j)).verticalCarrier = true →
    (S.role (base.tile i ⟨j.val + 1, hj⟩)).verticalCarrier = true →
    let outgoing := (S.role (base.tile i j)).verticalOutgoing
      (point i j) (verticalSource i j)
    match S.role (base.tile i ⟨j.val + 1, hj⟩) with
    | .active | .corner => point i ⟨j.val + 1, hj⟩ = (outgoing.1, outgoing.2 + 1)
    | .vertical => verticalSource i ⟨j.val + 1, hj⟩ = outgoing
    | _ => False

/-- Every combined plane yields seeded payload squares of every positive side length. -/
@[expose] def Forces (S : RoutedScaffold) : Prop :=
  ∀ I, TilesPlane (combine S I) → ∀ n, Nonempty (SeededSquare I n)

/-- Every payload plane with the seed at the origin lifts to a combined plane. -/
@[expose] def Realizes (S : RoutedScaffold) : Prop :=
  ∀ I, TilesAtOrigin I → TilesPlane (combine S I)

/-- A generic seed-removal step, not the domino theorem: both geometric obligations remain
hypotheses. Finite extended squares decode to source squares, while a source quadrant extends
to the pointed plane required by realization. -/
theorem tilesPlane_combine_pointedExtension_iff_of_forces_of_realizes
    {S : RoutedScaffold} (forces : Forces S) (realizes : Realizes S) (I : SeededInstance) :
    TilesPlane (combine S (pointedExtension I)) ↔ TilesQuadrant I := by
  constructor
  · intro h
    exact (tilesQuadrant_iff_seededSquares I).mpr fun n =>
      seededSquare_of_pointedExtension (forces _ h n)
  · intro h
    exact realizes _ ((tilesAtOrigin_pointedExtension_iff I).mpr h)

end Cslib.WangTile
