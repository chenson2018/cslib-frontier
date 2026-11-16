/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Tiling.Frame
public import CslibFrontier.Computability.WangTile.EveryTileOccurs
public import CslibFrontier.Foundations.RelationAlgebra.Game
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module

/-!
# Tilings give a winning strategy

Theorem 4 of [HirschHodkinson2001]: if every tile of a list is at the origin of a tiling by the
list, and the first tile matches itself, then ∃ has a winning strategy in the game of `RA(τ)`.

**The proof is not written yet**: the statement below is a `sorry`, being proved separately.

## References

* [R. Hirsch, I. Hodkinson, *Representability is not decidable for finite relation
  algebras*][HirschHodkinson2001]
-/

namespace Cslib.RelationAlgebra

open WangTile

namespace Tiling

open Atom

variable {ι : Type*} {L : List WangTile} {D : Type}

/-! ### Axes and shapes of atoms -/

/-- The axis other than `d`. -/
private def Axis.other : Axis → Axis
  | .one => .two
  | .two => .one

@[simp]
private theorem Axis.other_other (d : Axis) : d.other.other = d := by cases d <;> rfl

private theorem Axis.other_ne (d : Axis) : d.other ≠ d := by cases d <;> simp [Axis.other]

/-- The direction of the tile atoms on the edges that start at a `d`-node: `T₁₂ⁱ` starts at a
`1`-node and its converse at a `2`-node. -/
private def Axis.tileDir : Axis → Direction
  | .one => .forward
  | .two => .reverse

/-- The unit vector of the plane along an axis. -/
private def Axis.vec : Axis → ℤ × ℤ
  | .one => (1, 0)
  | .two => (0, 1)

/-- The colour of the edge of a tile that faces backwards along an axis: left or bottom. -/
private def Axis.back : Axis → WangTile → ℕ
  | .one, t => t.left
  | .two, t => t.bottom

/-- The colour of the edge of a tile that faces forwards along an axis: right or top. -/
private def Axis.front : Axis → WangTile → ℕ
  | .one, t => t.right
  | .two, t => t.top

/-- The steps `±1₁` and `±1₂`. -/
private def Atom.IsStep : Atom ι → Prop
  | step _ _ => True
  | _ => False

/-- The tile atoms and their converses. -/
private def Atom.IsTile : Atom ι → Prop
  | tile _ _ => True
  | _ => False

/-- The displacement of a step: `1` for `+1_d`, `-1` for `-1_d`, and `0` for other atoms. -/
private def Atom.sgn : Atom ι → ℤ
  | step _ .forward => 1
  | step _ .reverse => -1
  | _ => 0

private theorem Atom.isStep_iff {a : Atom ι} : a.IsStep ↔ ∃ d o, a = step d o := by
  cases a <;> simp [Atom.IsStep]

private theorem Atom.isTile_iff {a : Atom ι} : a.IsTile ↔ ∃ i o, a = tile i o := by
  cases a <;> simp [Atom.IsTile]

@[simp]
private theorem Atom.isStep_conv {a : Atom ι} : a.conv.IsStep ↔ a.IsStep := by
  cases a <;> exact .rfl

@[simp]
private theorem Atom.isTile_conv {a : Atom ι} : a.conv.IsTile ↔ a.IsTile := by
  cases a <;> exact .rfl

@[simp]
private theorem Atom.sgn_conv (a : Atom ι) : a.conv.sgn = -a.sgn := by
  cases a with
  | step d o => cases o <;> simp [Atom.sgn, Atom.conv, Direction.flip]
  | _ => simp [Atom.sgn, Atom.conv]

@[simp]
private theorem Atom.isUnit_unit (i : Kind) : (unit i : Atom ι).IsUnit := trivial

private theorem Atom.IsUnit.eq_unit {a : Atom ι} (h : a.IsUnit) : a = unit a.src := by
  cases a <;> first | rfl | exact h.elim

private theorem Atom.conv_eq_iff {a b : Atom ι} : a.conv = b ↔ a = b.conv :=
  ⟨fun h => by rw [← h, conv_conv], fun h => by rw [h, conv_conv]⟩

@[simp]
private theorem Axis.kind_inj {d e : Axis} : d.kind = e.kind ↔ d = e := by
  cases d <;> cases e <;> simp [Axis.kind]

@[simp]
private theorem Axis.kind_ne_zero (d : Axis) : d.kind ≠ .zero := by cases d <;> simp [Axis.kind]

@[simp]
private theorem Axis.zero_ne_kind (d : Axis) : Kind.zero ≠ d.kind := by
  cases d <;> simp [Axis.kind]

@[simp]
private theorem Axis.other_eq_iff {d e : Axis} : d.other = e.other ↔ d = e := by
  cases d <;> cases e <;> simp [Axis.other]

@[simp]
private theorem Axis.other_ne_self (d : Axis) : d.other ≠ d := by cases d <;> simp [Axis.other]

@[simp]
private theorem Axis.self_ne_other (d : Axis) : d ≠ d.other := by cases d <;> simp [Axis.other]

@[simp]
private theorem Axis.tileDir_inj {d e : Axis} : d.tileDir = e.tileDir ↔ d = e := by
  cases d <;> cases e <;> simp [Axis.tileDir]

@[simp]
private theorem Axis.tileDir_flip (d : Axis) : d.tileDir.flip = d.other.tileDir := by
  cases d <;> rfl

@[simp] private theorem Atom.src_unit (i : Kind) : (unit i : Atom ι).src = i := rfl
@[simp] private theorem Atom.tgt_unit (i : Kind) : (unit i : Atom ι).tgt = i := rfl
@[simp] private theorem Atom.src_white (i j : Kind) : (white i j : Atom ι).src = i := rfl
@[simp] private theorem Atom.tgt_white (i j : Kind) : (white i j : Atom ι).tgt = j := rfl
@[simp] private theorem Atom.src_green_forward (d : Axis) :
    (green d .forward : Atom ι).src = .zero := rfl
@[simp] private theorem Atom.tgt_green_forward (d : Axis) :
    (green d .forward : Atom ι).tgt = d.kind := rfl
@[simp] private theorem Atom.src_green_reverse (d : Axis) :
    (green d .reverse : Atom ι).src = d.kind := rfl
@[simp] private theorem Atom.tgt_green_reverse (d : Axis) :
    (green d .reverse : Atom ι).tgt = .zero := rfl
@[simp] private theorem Atom.src_u_forward (d : Axis) : (u d .forward : Atom ι).src = .zero := rfl
@[simp] private theorem Atom.tgt_u_forward (d : Axis) : (u d .forward : Atom ι).tgt = d.kind := rfl
@[simp] private theorem Atom.src_u_reverse (d : Axis) : (u d .reverse : Atom ι).src = d.kind := rfl
@[simp] private theorem Atom.tgt_u_reverse (d : Axis) : (u d .reverse : Atom ι).tgt = .zero := rfl
@[simp] private theorem Atom.src_v_forward (d : Axis) : (v d .forward : Atom ι).src = .zero := rfl
@[simp] private theorem Atom.tgt_v_forward (d : Axis) : (v d .forward : Atom ι).tgt = d.kind := rfl
@[simp] private theorem Atom.src_v_reverse (d : Axis) : (v d .reverse : Atom ι).src = d.kind := rfl
@[simp] private theorem Atom.tgt_v_reverse (d : Axis) : (v d .reverse : Atom ι).tgt = .zero := rfl
@[simp] private theorem Atom.src_step (d : Axis) (o : Direction) :
    (step d o : Atom ι).src = d.kind := rfl
@[simp] private theorem Atom.tgt_step (d : Axis) (o : Direction) :
    (step d o : Atom ι).tgt = d.kind := by cases o <;> rfl
@[simp] private theorem Atom.src_tile (i : ι) (d : Axis) :
    (tile i d.tileDir : Atom ι).src = d.kind := by cases d <;> rfl
@[simp] private theorem Atom.tgt_tile (i : ι) (d : Axis) :
    (tile i d.tileDir : Atom ι).tgt = d.other.kind := by cases d <;> rfl

/-- A tile atom starts at the nodes of some axis. -/
private theorem Direction.exists_tileDir (o : Direction) : ∃ d : Axis, o = d.tileDir := by
  cases o
  · exact ⟨.one, rfl⟩
  · exact ⟨.two, rfl⟩

/-! ### The rules -/

/-- The four shapes of the triangles listed in `Rule`, with rules 2–4 and their duals stated once
for the two axes. -/
private theorem Rule.cases {r s t : Atom (Fin L.length)} (h : Rule L r s t) :
    (r = green .one .reverse ∧ s = green .two .forward ∧ t = white .one .two) ∨
    (∃ d i j, r = tile i d.tileDir ∧ s = tile j d.tileDir.flip ∧ t = step d .reverse ∧
      d.back L[i] ≠ d.front L[j]) ∨
    (∃ d i, r = u d .reverse ∧ s = green d.other .forward ∧ t = tile i d.tileDir ∧ i.val ≠ 0) ∨
    (∃ d o, r = v d .reverse ∧ s = green d .forward ∧ t = step d o) := by
  unfold Rule at h
  split at h
  · exact .inl ⟨rfl, rfl, rfl⟩
  · exact .inr (.inl ⟨.one, _, _, rfl, rfl, rfl, h⟩)
  · exact .inr (.inl ⟨.two, _, _, rfl, rfl, rfl, h⟩)
  · exact .inr (.inr (.inl ⟨.one, _, rfl, rfl, rfl, h⟩))
  · exact .inr (.inr (.inl ⟨.two, _, rfl, rfl, rfl, h⟩))
  · exact .inr (.inr (.inr ⟨.one, _, rfl, rfl, rfl⟩))
  · exact .inr (.inr (.inr ⟨.two, _, rfl, rfl, rfl⟩))
  · exact h.elim

private theorem Rule.not_isUnit {r s t : Atom (Fin L.length)} (h : Rule L r s t) :
    ¬r.IsUnit ∧ ¬s.IsUnit ∧ ¬t.IsUnit := by
  obtain ⟨rfl, rfl, rfl⟩ | ⟨d, i, j, rfl, rfl, rfl, -⟩ | ⟨d, i, rfl, rfl, rfl, -⟩ |
    ⟨d, o, rfl, rfl, rfl⟩ := h.cases <;> simp [Atom.IsUnit]

private theorem rule_u {d : Axis} {i : Fin L.length} (hi : i.val ≠ 0) :
    Rule L (u d .reverse) (green d.other .forward) (tile i d.tileDir) := by
  cases d <;> simpa [Rule, Axis.other, Axis.tileDir] using hi

private theorem rule_v (d : Axis) (o : Direction) :
    Rule L (v d .reverse) (green d .forward) (step d o) := by
  cases d <;> simp [Rule]

/-! ### Typed labellings -/

/-- A labelling of the ordered pairs of nodes by atoms is typed when the kind of node at which a
label starts depends only on the first node, and reversing an edge takes the converse. The kind
of the node `x` is then `(lab x x).src`. -/
private structure Typed (lab : D → D → Atom ι) : Prop where
  src_eq (x y : D) : (lab x y).src = (lab x x).src
  conv_lab (x y : D) : (lab x y).conv = lab y x

private theorem Typed.tgt_eq {lab : D → D → Atom ι} (K : Typed lab) (x y : D) :
    (lab x y).tgt = (lab y y).src := by
  rw [Atom.tgt, K.conv_lab, K.src_eq]

private theorem Typed.src_of_eq {lab : D → D → Atom ι} (K : Typed lab) {x y : D} {a : Atom ι}
    (h : lab x y = a) : (lab x x).src = a.src := by
  rw [← h, K.src_eq x y]

private theorem Typed.tgt_of_eq {lab : D → D → Atom ι} (K : Typed lab) {x y : D} {a : Atom ι}
    (h : lab x y = a) : (lab y y).src = a.tgt := by
  rw [← h, K.tgt_eq]

private theorem Typed.eq_conv {lab : D → D → Atom ι} (K : Typed lab) {x y : D} {a : Atom ι}
    (h : lab x y = a) : lab y x = a.conv := by
  rw [← h, K.conv_lab]

/-! ### Annotated labellings and the invariant -/

variable (L) in
/-- The place of a tile edge in a tiling: the position `seed` of `L` whose tiling is used, and a
cell of the plane. The cell is only meaningful when the seed is not `0`. -/
private structure Cell where
  /-- The tiling used is the one with the tile at this position of `L` at the origin. -/
  seed : Fin L.length
  /-- The cell of the plane. -/
  pos : ℤ × ℤ

variable (L) in
/-- A tiling of the plane by positions of `L` for each position `σ`, with `σ` at the origin, the
one for `0` being constant. -/
private structure Tilings [NeZero L.length] where
  /-- The tiling for the position `σ`. -/
  til : Fin L.length → ℤ × ℤ → Fin L.length
  til_zero (c : ℤ × ℤ) : til 0 c = 0
  til_origin (σ : Fin L.length) : til σ 0 = σ
  til_match (σ : Fin L.length) (c : ℤ × ℤ) (d : Axis) :
    d.front L[til σ c] = d.back L[til σ (c + d.vec)]

/-- The position of `L` at a cell of a tiling. -/
private def Tilings.idx [NeZero L.length] (T : Tilings L) (m : Cell L) : Fin L.length :=
  T.til m.seed m.pos

variable (L D) in
/-- A labelling of the ordered pairs of nodes by atoms, with the bookkeeping that ∃ keeps.

For a `0`-node `h` and an axis `d`, the `d`-nodes `a` with `lab h a = g₀d` are divided into
classes, `root h a` naming the class of `a`, and `pot h a` is an integer that increases by one
along each step `+1_d` between two of them. Each tile edge has a `cell`. -/
private structure Ann where
  /-- The atom on the edge from the first node to the second. -/
  lab : D → D → Atom (Fin L.length)
  /-- `root h a` names the class of `a` among the nodes that `h` sees along a green edge. -/
  root : D → D → D
  /-- `pot h a` is the place of `a` in its class under `h`. -/
  pot : D → D → ℤ
  /-- The place in a tiling of the tile edge between two nodes. -/
  cell : D → D → Cell L

/-- Two distinct nodes of one class under the `0`-node `h`. -/
private structure Twin (lab : D → D → Atom (Fin L.length)) (root : D → D → D) (d : Axis)
    (h a a' : D) : Prop where
  ne : a ≠ a'
  left : lab h a = green d .forward
  right : lab h a' = green d .forward
  root_eq : root h a = root h a'

/-- The condition under which ∃ labels the edge from the `0`-node `h` to `b` with `u₀d`: two
distinct nodes of one class under `h` are joined to `b` by steps. -/
private def UCond (lab : D → D → Atom (Fin L.length)) (root : D → D → D) (d : Axis)
    (h b : D) : Prop :=
  ∃ a a', Twin lab root d h a a' ∧ (lab a b).IsStep ∧ (lab a' b).IsStep

/-- The condition under which ∃ labels the edge from the `0`-node `h` to `y` with a `v` atom: two
distinct nodes of one class under `h` are joined to `y` by tile edges, `wt` saying which edges
are tile edges. -/
private def VCond (lab : D → D → Atom (Fin L.length)) (root : D → D → D) (wt : D → D → Prop)
    (d : Axis) (h y : D) : Prop :=
  ∃ a a', Twin lab root d h a a' ∧ wt a y ∧ wt a' y

/-- The invariant of ∃'s strategy. -/
private structure Good [NeZero L.length] (T : Tilings L) (S : Ann L D) : Prop where
  typed : Typed S.lab
  isUnit_iff (x y : D) : (S.lab x y).IsUnit ↔ x = y
  rule_free (x y w : D) : ¬Rule L (S.lab x y) (S.lab y w) (S.lab x w)
  /-- A step between two nodes that `h` sees joins nodes of one class, and raises `pot`. -/
  step_class {h a b : D} {d e : Axis} : S.lab h a = green d .forward →
    S.lab h b = green d .forward → S.lab a b = step e .forward →
    S.root h a = S.root h b ∧ S.pot h b = S.pot h a + 1
  /-- A node joined by steps to two nodes of one class under `h` is seen by `h` along a green
  edge or along `u`. -/
  u_class {h b : D} {d : Axis} : UCond S.lab S.root d h b →
    S.lab h b = green d .forward ∨ S.lab h b = u d .forward
  /-- A node joined by tile edges to two nodes of one class under `h` is seen by `h` along a
  green edge or along `v`. -/
  v_class {h y : D} {d : Axis} : VCond S.lab S.root (fun a y => (S.lab a y).IsTile) d h y →
    S.lab h y = green d.other .forward ∨ S.lab h y = v d.other .forward
  /-- No second `0`-node sees two nodes of one class under `h`. -/
  apex_unique {h h' a a' : D} {d : Axis} : Twin S.lab S.root d h a a' →
    S.lab h' a = green d .forward → S.lab h' a' = green d .forward → h = h'
  cell_symm (x y : D) : S.cell x y = S.cell y x
  /-- A tile edge is labelled by the position of `L` at its cell. -/
  tile_idx {x y : D} {i : Fin L.length} {o : Direction} : S.lab x y = tile i o →
    i = T.idx (S.cell x y)
  /-- The tile edges from the nodes of one class under `h` to a node that `h` sees lie in one
  tiling, at the cells of a row or column given by `pot`. -/
  cell_class {h a b y : D} {d : Axis} : S.lab h a = green d .forward →
    S.lab h b = green d .forward → S.lab h y = green d.other .forward →
    S.root h a = S.root h b → (S.cell b y).seed = (S.cell a y).seed ∧
      ((S.cell a y).seed ≠ 0 →
        (S.cell b y).pos = (S.cell a y).pos + (S.pot h b - S.pot h a) • d.vec)

/-! ### The response to a move -/

variable (S : Ann L D) in
/-- A move of ∀ that has no witness yet: two nodes `p`, `q` and two atoms `a`, `b` whose product
lies above the label of `(p, q)`. -/
private structure Move where
  /-- The first node of the edge picked. -/
  p : D
  /-- The second node of the edge picked. -/
  q : D
  /-- The atom demanded on the edge from `p` to the new node. -/
  a : Atom (Fin L.length)
  /-- The atom demanded on the edge from the new node to `q`. -/
  b : Atom (Fin L.length)
  legal : Cycle L a b (S.lab p q)
  fresh (w : D) : S.lab p w = a → S.lab w q ≠ b

namespace Move

variable {S : Ann L D} (M : Move S)

/-- The kind of the new node. -/
private def kind : Kind := M.a.tgt

/-- The nodes picked by ∀, whose edges to the new node he labels. -/
private def IsPar (x : D) : Prop := x = M.p ∨ x = M.q

open Classical in
/-- The atom on the edge from an old node to the new node before ∃ labels the edges that ∀ left
unlabelled: the atom demanded by ∀ on the edges from `p` and `q`, and a white atom, which stands
for no label, on the others. -/
private noncomputable def par (x : D) : Atom (Fin L.length) :=
  if x = M.p then M.a else if x = M.q then M.b.conv else white (S.lab x x).src M.kind

private theorem par_p : M.par M.p = M.a := by simp [par]

private theorem par_of_not_isPar {x : D} (h : ¬M.IsPar x) :
    M.par x = white (S.lab x x).src M.kind := by
  have hp : x ≠ M.p := fun hp => h (.inl hp)
  have hq : x ≠ M.q := fun hq => h (.inr hq)
  simp [par, hp, hq]

private theorem isPar_of_par {x : D} (h : ∀ i j, M.par x ≠ white i j) : M.IsPar x := by
  by_contra hx
  exact h _ _ (M.par_of_not_isPar hx)

private theorem isPar_of_isStep {x : D} (h : (M.par x).IsStep) : M.IsPar x :=
  M.isPar_of_par fun i j hw => by simp [hw, Atom.IsStep] at h

private theorem isPar_of_isTile {x : D} (h : (M.par x).IsTile) : M.IsPar x :=
  M.isPar_of_par fun i j hw => by simp [hw, Atom.IsTile] at h

private theorem isPar_of_green {x : D} {d : Axis} {o : Direction} (h : M.par x = green d o) :
    M.IsPar x :=
  M.isPar_of_par fun i j hw => by simp [hw] at h

/-- ∀ labels at most two edges to the new node. -/
private theorem isPar_three {x y w : D} (hx : M.IsPar x) (hy : M.IsPar y) (hw : M.IsPar w) :
    x = y ∨ x = w ∨ y = w := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hw with rfl | rfl <;> simp

/-- Among three of the nodes picked by ∀, two that carry different atoms leave no room for a
third. -/
private theorem eq_of_isPar {x y w : D} (hx : M.IsPar x) (hy : M.IsPar y) (hw : M.IsPar w)
    (hxy : M.par x ≠ M.par y) : w = x ∨ w = y := by
  rcases M.isPar_three hx hy hw with rfl | rfl | rfl
  · exact (hxy rfl).elim
  · exact .inl rfl
  · exact .inr rfl

private theorem par_tgt (x : D) : (M.par x).tgt = M.kind := by
  unfold par
  split_ifs
  · rfl
  · rw [Atom.tgt, conv_conv, kind, M.legal.tgt_eq_src]
  · rfl

end Move

/-! ### The network of a labelling, and the opening positions -/

variable [NeZero L.length] {T : Tilings L} {S : Ann L D}

/-- The atomic network of a labelling that satisfies the invariant. -/
private def Good.network (hS : Good T S) : AtomicNetwork (tilingFrame L) D where
  label := S.lab
  label_mem_id {x y} := hS.isUnit_iff x y
  conv_label := hS.typed.conv_lab
  label_mem_cycles x y w := mem_cycles_tilingFrame.mpr
    { tgt_eq_src := by rw [hS.typed.tgt_eq, hS.typed.src_eq y w]
      src_eq_src := by rw [hS.typed.src_eq, hS.typed.src_eq x w]
      tgt_eq_tgt := by rw [hS.typed.tgt_eq, hS.typed.tgt_eq x w]
      eq_of_isUnit_left h := by rw [(hS.isUnit_iff _ _).mp h]
      eq_of_isUnit_right h := by rw [(hS.isUnit_iff _ _).mp h]
      eq_conv_of_isUnit h := by rw [(hS.isUnit_iff _ _).mp h, hS.typed.conv_lab]
      not_forbidden := by
        simp only [Forbidden, hS.typed.conv_lab]
        rintro (h | h | h | h | h | h) <;> exact hS.rule_free _ _ _ h }

/-- The labelling of two nodes joined by an edge with a given atom. -/
private def Ann.pair (a : Atom (Fin L.length)) : Ann L Bool where
  lab
    | false, false => unit a.src
    | false, true => a
    | true, false => a.conv
    | true, true => unit a.tgt
  root _ y := y
  pot _ _ := 0
  cell _ _ :=
    match a with
    | tile j _ => ⟨j, 0⟩
    | _ => ⟨0, 0⟩

private theorem Ann.good_pair {a : Atom (Fin L.length)} (ha : ¬a.IsUnit) :
    Good T (Ann.pair a) where
  typed :=
    { src_eq x y := by cases x <;> cases y <;> rfl
      conv_lab x y := by cases x <;> cases y <;> first | rfl | exact conv_conv a }
  isUnit_iff x y := by cases x <;> cases y <;> simp [Ann.pair, ha]
  rule_free x y w h := by
    obtain ⟨h₁, h₂, h₃⟩ := h.not_isUnit
    cases x <;> cases y <;> cases w <;> simp [Ann.pair] at h₁ h₂ h₃
  step_class {h x y} _ _ h₁ h₂ h₃ := by
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at h₁ h₂ h₃
  u_class {h b} _ := by
    rintro ⟨x, y, ⟨hne, h₁, h₂, -⟩, -, -⟩
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at hne h₁ h₂
  v_class {h b} _ := by
    rintro ⟨x, y, ⟨hne, h₁, h₂, -⟩, -, -⟩
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at hne h₁ h₂
  apex_unique {h h' x y} _ := by
    rintro ⟨hne, h₁, h₂, -⟩ - -
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at hne h₁ h₂
  cell_symm _ _ := rfl
  tile_idx {x y i o} h := by
    cases x <;> cases y <;> cases a <;> cases o <;>
      simp_all [Ann.pair, Atom.conv, Direction.flip, Tilings.idx, T.til_origin]
  cell_class {h x y z} _ h₁ h₂ h₃ _ := by
    cases h <;> cases x <;> cases y <;> simp [Ann.pair] at h₁ h₂ ⊢

/-- The labelling of a single node with a unit on its loop. -/
private def Ann.single (i : Kind) : Ann L Unit where
  lab _ _ := unit i
  root _ y := y
  pot _ _ := 0
  cell _ _ := ⟨0, 0⟩

private theorem Ann.good_single (i : Kind) : Good T (Ann.single i) where
  typed := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  isUnit_iff _ _ := by simp [Ann.single]
  rule_free _ _ _ h := h.not_isUnit.1 trivial
  step_class h := by simp [Ann.single] at h
  u_class := by
    rintro _ _ _ ⟨x, y, ⟨-, h, -, -⟩, -, -⟩
    simp [Ann.single] at h
  v_class := by
    rintro _ _ _ ⟨x, y, ⟨-, h, -, -⟩, -, -⟩
    simp [Ann.single] at h
  apex_unique := by
    rintro _ _ _ _ _ ⟨-, h, -, -⟩ - -
    simp [Ann.single] at h
  cell_symm _ _ := rfl
  tile_idx h := by simp [Ann.single] at h
  cell_class h := by simp [Ann.single] at h

/-! ### The triangle of a move -/

variable (hS : Good T S)

namespace Move

variable (M : Move S)

include hS in
private theorem par_q : M.par M.q = M.b.conv := by
  by_cases h : M.q = M.p
  · rw [h, par_p, M.legal.eq_conv_of_isUnit ((hS.isUnit_iff _ _).mpr h.symm), conv_conv]
  · simp [par, h]

include hS in
private theorem par_src (x : D) : (M.par x).src = (S.lab x x).src := by
  unfold par
  split_ifs with hp hq
  · rw [hp, M.legal.src_eq_src, hS.typed.src_eq]
  · rw [hq, ← Atom.tgt, M.legal.tgt_eq_tgt, hS.typed.tgt_eq]
  · rfl

include hS in
private theorem par_not_isUnit (x : D) : ¬(M.par x).IsUnit := by
  unfold par
  split_ifs with hp hq
  · intro ha
    refine M.fresh M.p ?_ (M.legal.eq_of_isUnit_left ha)
    rw [ha.eq_unit, M.legal.src_eq_src, hS.typed.src_eq]
    exact ((hS.isUnit_iff _ _).mpr rfl).eq_unit
  · intro hb
    rw [isUnit_conv] at hb
    refine M.fresh M.q (M.legal.eq_of_isUnit_right hb) ?_
    have h₁ : M.b.src = M.b.tgt := by rw [hb.eq_unit]; rfl
    rw [hb.eq_unit, h₁, M.legal.tgt_eq_tgt, hS.typed.tgt_eq]
    exact ((hS.isUnit_iff _ _).mpr rfl).eq_unit
  · exact id

/-- The labelling of the old nodes and the new node `none` before ∃ labels the edges that ∀ left
unlabelled. -/
private noncomputable def preLab : Option D → Option D → Atom (Fin L.length)
  | some x, some y => S.lab x y
  | some x, none => M.par x
  | none, some y => (M.par y).conv
  | none, none => unit M.kind

include hS in
private theorem typed_preLab : Typed M.preLab where
  src_eq x y := by
    rcases x with _ | x <;> rcases y with _ | y
    · rfl
    · exact M.par_tgt y
    · exact M.par_src hS x
    · exact hS.typed.src_eq x y
  conv_lab x y := by
    rcases x with _ | x <;> rcases y with _ | y
    · rfl
    · exact conv_conv _
    · rfl
    · exact hS.typed.conv_lab x y

include hS in
/-- The triangle of ∀'s move, on the two nodes he picked and the new node, is consistent. -/
private theorem tri_free {x y w : Option D} (hx : x = none ∨ x = some M.p ∨ x = some M.q)
    (hy : y = none ∨ y = some M.p ∨ y = some M.q) (hw : w = none ∨ w = some M.p ∨ w = some M.q) :
    ¬Rule L (M.preLab x y) (M.preLab y w) (M.preLab x w) := by
  intro hR
  obtain ⟨h₁, h₂, h₃⟩ := hR.not_isUnit
  have hunit (z : Option D) : (M.preLab z z).IsUnit := by
    rcases z with _ | z
    · trivial
    · exact (hS.isUnit_iff z z).mpr rfl
  have hxy : x ≠ y := fun h => h₁ (h ▸ hunit x)
  have hyw : y ≠ w := fun h => h₂ (h ▸ hunit y)
  have hxw : x ≠ w := fun h => h₃ (h ▸ hunit x)
  have hf := M.legal.not_forbidden
  have hq := M.par_q hS
  have hc := hS.typed.conv_lab M.p M.q
  simp only [Forbidden, not_or] at hf
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl <;>
    first
    | exact hxy rfl
    | exact hyw rfl
    | exact hxw rfl
    | simp only [preLab, par_p, hq, conv_conv, ← hc] at hR
      first
      | exact hf.1 hR
      | exact hf.2.1 hR
      | exact hf.2.2.1 hR
      | exact hf.2.2.2.1 hR
      | exact hf.2.2.2.2.1 hR
      | exact hf.2.2.2.2.2 hR

/-! ### The labels chosen by ∃ -/

open Classical in
/-- The node picked by ∀ that is joined to the new node by a step, when `h` sees it. -/
private noncomputable def stepPar (h : D) : Option D :=
  if hs : ∃ s, (∃ d, S.lab h s = green d .forward) ∧ (M.par s).IsStep then some hs.choose else none

omit [NeZero L.length] in
private theorem stepPar_spec {h s : D} (hs : M.stepPar h = some s) :
    (∃ d, S.lab h s = green d .forward) ∧ (M.par s).IsStep := by
  unfold stepPar at hs
  split_ifs at hs with h'
  obtain rfl := Option.some.inj hs
  exact h'.choose_spec

omit [NeZero L.length] in
private theorem stepPar_eq {h s : D} {d e : Axis} (hh : M.par h = green e .forward)
    (hs : S.lab h s = green d .forward) (hstep : (M.par s).IsStep) : M.stepPar h = some s := by
  have h' : ∃ s, (∃ d, S.lab h s = green d .forward) ∧ (M.par s).IsStep := ⟨s, ⟨d, hs⟩, hstep⟩
  simp only [stepPar, h', ↓reduceDIte, Option.some.injEq]
  have hne : M.par h ≠ M.par s := fun h => by simp [← h, hh, Atom.IsStep] at hstep
  have hc := h'.choose_spec.2
  rcases M.eq_of_isPar (M.isPar_of_green hh) (M.isPar_of_isStep hstep)
    (M.isPar_of_isStep hc) hne with h₁ | h₁
  · rw [h₁, hh] at hc
    simp [Atom.IsStep] at hc
  · exact h₁

open Classical in
/-- The classes after the move. The new node joins the class of the node to which a step joins
it, or starts a class; when the new node is a `0`-node, the nodes it sees are those picked by ∀,
and they form one class when a step joins them. -/
private noncomputable def newRoot : Option D → Option D → Option D
  | some h, some a => some (S.root h a)
  | some h, none => (M.stepPar h).map (S.root h)
  | none, some a => if (S.lab M.p a).IsStep then some M.p else some a
  | none, none => none

/-- The places in the classes after the move. -/
private noncomputable def newPot : Option D → Option D → ℤ
  | some h, some a => S.pot h a
  | some h, none => (M.stepPar h).elim 0 fun s => S.pot h s + (M.par s).sgn
  | none, some a => (S.lab M.p a).sgn
  | none, none => 0

/-- The new node and `x` are seen along green edges by one old node, so that the edge between
them must be a tile edge. -/
private def Apex (x : D) : Prop :=
  ∃ h d, S.lab h x = green d .forward ∧ M.par h = green d.other .forward

/-- The edges that are tile edges once ∃ has answered the move: the old ones, those that ∀ has
labelled with a tile atom and those between two nodes seen by one node. -/
private def WillTile : Option D → Option D → Prop
  | some x, some y => (S.lab x y).IsTile
  | some x, none => (M.par x).IsTile ∨ M.Apex x
  | none, _ => False

/-- The edge from `x₀`, a node of axis `d`, to the new node is constrained to lie at the cell
`m`: either ∀ has labelled with a tile atom the edge from `x₀`, or from a node one step away
from `x₀`, or the new node is one step away from a node joined to `x₀` by a tile edge. -/
private def Anchor (d : Axis) (x₀ : D) (m : Cell L) : Prop :=
  ∃ s, (∃ j o, M.par s = tile j o ∧ (x₀ = s ∨ (S.lab s x₀).IsStep) ∧
      m = ⟨j, (S.lab s x₀).sgn • d.vec⟩) ∨
    ((M.par s).IsStep ∧ (S.lab x₀ s).IsTile ∧
      m = ⟨(S.cell x₀ s).seed, (S.cell x₀ s).pos + (M.par s).sgn • d.other.vec⟩)

/-- The edge from `x` to the new node is constrained to lie at the cell `m`, by a constraint on a
node of the class of `x` under a node that sees the new node. -/
private def Cand (x : D) (m : Cell L) : Prop :=
  ∃ h x₀ e d m₀, M.par h = green e .forward ∧ S.lab h x = green d .forward ∧
    S.lab h x₀ = green d .forward ∧ S.root h x = S.root h x₀ ∧ M.Anchor d x₀ m₀ ∧
    m = ⟨m₀.seed, m₀.pos + (S.pot h x - S.pot h x₀) • d.vec⟩

open Classical in
/-- The cell of the edge from `x` to the new node: a cell to which it is constrained, and
otherwise a cell of the constant tiling. -/
private noncomputable def candCell (x : D) : Cell L :=
  if hc : ∃ m, M.Cand x m then hc.choose else ⟨0, 0⟩

/-- The cell of the edge from `x` to the new node: the origin of the tiling of the tile when ∀
has labelled the edge with a tile atom. -/
private noncomputable def cellAt (x : D) : Cell L :=
  match M.par x with
  | tile j _ => ⟨j, 0⟩
  | _ => M.candCell x

open Classical in
/-- The atom that ∃ puts on an edge from a `0`-node to a node of axis `d`. -/
private noncomputable def apexLabel (d : Axis) (U V : Prop) : Atom (Fin L.length) :=
  if U then u d .forward else if V then v d .forward else white .zero d.kind

/-- The axis of a kind of node other than `0`. -/
private def _root_.Cslib.RelationAlgebra.Tiling.Kind.axis : Kind → Option Axis
  | .zero => none
  | .one => some .one
  | .two => some .two

open Classical in
variable (T) in
/-- The atom that ∃ puts on the edge from `x` to the new node, when ∀ has not labelled it. -/
private noncomputable def exLabel (x : D) : Atom (Fin L.length) :=
  match (S.lab x x).src.axis, M.kind.axis with
  | none, none => white .zero .zero
  | none, some e => apexLabel e (UCond M.preLab M.newRoot e (some x) none)
      (VCond M.preLab M.newRoot M.WillTile e.other (some x) none)
  | some d, none => (apexLabel d (UCond M.preLab M.newRoot d none (some x))
      (VCond M.preLab M.newRoot M.WillTile d.other none (some x))).conv
  | some d, some e =>
    if d = e then white d.kind d.kind
    else if M.Apex x then tile (T.idx (M.candCell x)) d.tileDir else white d.kind e.kind

open Classical in
variable (T) in
/-- The atom on the edge from `x` to the new node. -/
private noncomputable def ext (x : D) : Atom (Fin L.length) :=
  if M.IsPar x then M.par x else M.exLabel T x

variable (T) in
/-- The labelling with which ∃ answers a move, on the old nodes and one new node `none`. -/
private noncomputable def next : Ann L (Option D) where
  lab
    | some x, some y => S.lab x y
    | some x, none => M.ext T x
    | none, some y => (M.ext T y).conv
    | none, none => unit M.kind
  root := M.newRoot
  pot := M.newPot
  cell
    | some x, some y => S.cell x y
    | some x, none => M.cellAt x
    | none, some y => M.cellAt y
    | none, none => ⟨0, 0⟩

@[simp]
private theorem _root_.Cslib.RelationAlgebra.Tiling.Kind.axis_eq_none {k : Kind} :
    k.axis = none ↔ k = .zero := by
  cases k <;> simp [Kind.axis]

@[simp]
private theorem _root_.Cslib.RelationAlgebra.Tiling.Kind.axis_eq_some {k : Kind} {d : Axis} :
    k.axis = some d ↔ k = d.kind := by
  cases k <;> cases d <;> simp [Kind.axis, Axis.kind]

/-- The atoms that ∃ may put on an edge to the new node, with the reason for each. -/
private theorem exLabel_cases (x : D) :
    (∃ i j, M.exLabel T x = white i j) ∨
    (∃ e, M.exLabel T x = u e .forward ∧ UCond M.preLab M.newRoot e (some x) none) ∨
    (∃ e, M.exLabel T x = v e .forward ∧
      VCond M.preLab M.newRoot M.WillTile e.other (some x) none) ∨
    (∃ d, M.exLabel T x = u d .reverse ∧ UCond M.preLab M.newRoot d none (some x)) ∨
    (∃ d, M.exLabel T x = v d .reverse ∧
      VCond M.preLab M.newRoot M.WillTile d.other none (some x)) ∨
    (∃ d : Axis, M.exLabel T x = tile (T.idx (M.candCell x)) d.tileDir ∧ M.Apex x) := by
  unfold exLabel
  split
  · exact .inl ⟨_, _, rfl⟩
  · unfold apexLabel
    split_ifs with hU hV
    · exact .inr (.inl ⟨_, rfl, hU⟩)
    · exact .inr (.inr (.inl ⟨_, rfl, hV⟩))
    · exact .inl ⟨_, _, rfl⟩
  · unfold apexLabel
    split_ifs with hU hV
    · exact .inr (.inr (.inr (.inl ⟨_, rfl, hU⟩)))
    · exact .inr (.inr (.inr (.inr (.inl ⟨_, rfl, hV⟩))))
    · exact .inl ⟨_, _, rfl⟩
  · split_ifs with hde hA
    · exact .inl ⟨_, _, rfl⟩
    · exact .inr (.inr (.inr (.inr (.inr ⟨_, rfl, hA⟩))))
    · exact .inl ⟨_, _, rfl⟩

private theorem exLabel_src (x : D) : (M.exLabel T x).src = (S.lab x x).src := by
  unfold exLabel
  split <;> rename_i hx hk
  · rw [Kind.axis_eq_none] at hx
    simp [hx]
  · rw [Kind.axis_eq_none] at hx
    unfold apexLabel
    split_ifs <;> simp [hx]
  · rw [Kind.axis_eq_some] at hx
    unfold apexLabel
    split_ifs <;> simp [hx, Atom.conv, Direction.flip]
  · rw [Kind.axis_eq_some] at hx
    split_ifs <;> simp [hx]

private theorem exLabel_tgt (x : D) : (M.exLabel T x).tgt = M.kind := by
  unfold exLabel
  split <;> rename_i hx hk
  · rw [Kind.axis_eq_none] at hk
    simp [hk]
  · rw [Kind.axis_eq_some] at hk
    unfold apexLabel
    split_ifs <;> simp [hk]
  · rw [Kind.axis_eq_none] at hk
    unfold apexLabel
    split_ifs <;> simp [hk, Atom.conv, Direction.flip, Atom.tgt]
  · rw [Kind.axis_eq_some] at hk
    rename_i d e
    split_ifs with hde <;> simp [hk, hde]
    cases d <;> cases e <;> simp_all [Axis.other]

private theorem ext_of_isPar {x : D} (h : M.IsPar x) : M.ext T x = M.par x := by simp [ext, h]

private theorem ext_of_not_isPar {x : D} (h : ¬M.IsPar x) : M.ext T x = M.exLabel T x := by
  simp [ext, h]

include hS in
private theorem ext_src (x : D) : (M.ext T x).src = (S.lab x x).src := by
  by_cases h : M.IsPar x
  · rw [M.ext_of_isPar h, M.par_src hS]
  · rw [M.ext_of_not_isPar h, exLabel_src]

private theorem ext_tgt (x : D) : (M.ext T x).tgt = M.kind := by
  by_cases h : M.IsPar x
  · rw [M.ext_of_isPar h, par_tgt]
  · rw [M.ext_of_not_isPar h, exLabel_tgt]

include hS in
private theorem ext_not_isUnit (x : D) : ¬(M.ext T x).IsUnit := by
  by_cases h : M.IsPar x
  · rw [M.ext_of_isPar h]
    exact M.par_not_isUnit hS x
  · rw [M.ext_of_not_isPar h]
    obtain ⟨_, _, h⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ :=
      M.exLabel_cases (T := T) x <;> simp [h, Atom.IsUnit]

/-- ∃ puts no green atom on an edge. -/
private theorem par_of_ext_green {x : D} {d : Axis} {o : Direction} (h : M.ext T x = green d o) :
    M.par x = green d o := by
  by_cases hx : M.IsPar x
  · rwa [M.ext_of_isPar hx] at h
  · rw [M.ext_of_not_isPar hx] at h
    obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ :=
      M.exLabel_cases (T := T) x <;> simp [h'] at h

/-- ∃ puts no step on an edge. -/
private theorem par_of_ext_isStep {x : D} (h : (M.ext T x).IsStep) :
    M.ext T x = M.par x ∧ M.IsPar x := by
  by_cases hx : M.IsPar x
  · exact ⟨M.ext_of_isPar hx, hx⟩
  · rw [M.ext_of_not_isPar hx] at h
    obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ :=
      M.exLabel_cases (T := T) x <;> simp [h', Atom.IsStep] at h

/-- ∃ puts a tile atom only on an edge between two nodes seen by one node, and then the tile at
the cell chosen for the edge. -/
private theorem ext_tile {x : D} {i : Fin L.length} {o : Direction} (h : M.ext T x = tile i o) :
    M.par x = tile i o ∨ ¬M.IsPar x ∧ M.Apex x ∧ i = T.idx (M.candCell x) := by
  by_cases hx : M.IsPar x
  · rw [M.ext_of_isPar hx] at h
    exact .inl h
  · rw [M.ext_of_not_isPar hx] at h
    obtain ⟨_, _, h'⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', -⟩ | ⟨_, h', hA⟩ :=
      M.exLabel_cases (T := T) x <;> simp only [h', reduceCtorEq, tile.injEq] at h
    exact .inr ⟨hx, hA, h.1.symm⟩

private theorem next_lab_some (x y : D) : (M.next T).lab (some x) (some y) = S.lab x y := rfl

private theorem next_lab_p : (M.next T).lab (some M.p) none = M.a := by
  simp [next, M.ext_of_isPar (T := T) (.inl rfl), par_p]

include hS in
private theorem next_lab_q : (M.next T).lab none (some M.q) = M.b := by
  simp [next, M.ext_of_isPar (T := T) (.inr rfl), M.par_q hS]

/-! ### The cells of the new tile edges -/

omit [NeZero L.length] in
/-- A constraint on the cell of a new edge comes from a node picked by ∀ whose edge to the new
node he labelled with a tile atom or a step. -/
private theorem exists_par_of_anchor {d : Axis} {x₀ : D} {m : Cell L} (h : M.Anchor d x₀ m) :
    ∃ s, M.IsPar s ∧ ((M.par s).IsTile ∨ (M.par s).IsStep) := by
  obtain ⟨s, ⟨j, o, hs, -⟩ | ⟨hs, -⟩⟩ := h
  · have hs' : (M.par s).IsTile := by simp [hs, Atom.IsTile]
    exact ⟨s, M.isPar_of_isTile hs', .inl hs'⟩
  · exact ⟨s, M.isPar_of_isStep hs, .inr hs⟩

omit [NeZero L.length] in
/-- When ∀ has labelled an edge to the new node with a tile atom or a step, at most one node sees
the new node along a green edge. -/
private theorem green_par_unique {s h h' : D} {e e' : Axis} {o o' : Direction} (hs : M.IsPar s)
    (hs' : (M.par s).IsTile ∨ (M.par s).IsStep) (hh : M.par h = green e o)
    (hh' : M.par h' = green e' o') : h = h' := by
  have hne : M.par s ≠ M.par h := fun heq => by simp [heq, hh, Atom.IsTile, Atom.IsStep] at hs'
  rcases M.eq_of_isPar hs (M.isPar_of_green hh) (M.isPar_of_green hh') hne with h₁ | h₁
  · simp [← h₁, hh', Atom.IsTile, Atom.IsStep] at hs'
  · exact h₁.symm

include hS in
/-- By rule 3, ∀ cannot pick a `0`-node and a node that it sees along `u`, and ask for a green
edge from the first and a tile other than `T₀` from the second. -/
private theorem par_tile_eq_zero {h s : D} {d e : Axis} {j : Fin L.length} {o : Direction}
    (hu : S.lab h s = u d .forward) (hh : M.par h = green e .forward) (hs : M.par s = tile j o) :
    j = 0 := by
  by_contra hj
  obtain ⟨d', rfl⟩ := o.exists_tileDir
  have hκ : (S.lab s s).src = d.kind := hS.typed.tgt_of_eq hu
  have h₁ : d'.kind = d.kind := by rw [← hκ, ← M.par_src hS s, hs, Atom.src_tile]
  have h₂ : d'.other.kind = M.kind := by rw [← M.par_tgt s, hs, Atom.tgt_tile]
  have h₃ : e.kind = M.kind := by rw [← M.par_tgt h, hh, Atom.tgt_green_forward]
  obtain rfl := Axis.kind_inj.mp h₁
  obtain rfl : e = d'.other := Axis.kind_inj.mp (h₃.trans h₂.symm)
  refine M.tri_free hS (x := some s) (y := some h) (w := none)
    (.inr ((M.isPar_of_isTile (by simp [hs, Atom.IsTile])).imp (congrArg _) (congrArg _)))
    (.inr ((M.isPar_of_green hh).imp (congrArg _) (congrArg _))) (.inl rfl) ?_
  change Rule L (S.lab s h) (M.par h) (M.par s)
  rw [hS.typed.eq_conv hu, hh, hs]
  exact rule_u fun h0 => hj (Fin.ext h0)

include hS in
/-- By rule 4, ∀ cannot pick a `0`-node and a node that it sees along `v`, and ask for a green
edge from the first and a step from the second. -/
private theorem not_isStep_par {h s : D} {d e : Axis} (hv : S.lab h s = v d .forward)
    (hh : M.par h = green e .forward) : ¬(M.par s).IsStep := by
  intro hs
  obtain ⟨e', o, hs'⟩ := Atom.isStep_iff.mp hs
  have hκ : (S.lab s s).src = d.kind := hS.typed.tgt_of_eq hv
  have h₁ : e'.kind = d.kind := by rw [← hκ, ← M.par_src hS s, hs', Atom.src_step]
  have h₂ : e'.kind = M.kind := by rw [← M.par_tgt s, hs', Atom.tgt_step]
  have h₃ : e.kind = M.kind := by rw [← M.par_tgt h, hh, Atom.tgt_green_forward]
  obtain rfl := Axis.kind_inj.mp h₁
  obtain rfl : e = e' := Axis.kind_inj.mp (h₃.trans h₂.symm)
  refine M.tri_free hS (x := some s) (y := some h) (w := none)
    (.inr ((M.isPar_of_isStep hs).imp (congrArg _) (congrArg _)))
    (.inr ((M.isPar_of_green hh).imp (congrArg _) (congrArg _))) (.inl rfl) ?_
  change Rule L (S.lab s h) (M.par h) (M.par s)
  rw [hS.typed.eq_conv hv, hh, hs']
  exact rule_v e o

include hS in
/-- The constraints on the cell of a new edge agree. -/
private theorem cand_unique {x : D} {m m' : Cell L} (hm : M.Cand x m) (hm' : M.Cand x m') :
    m.seed = m'.seed ∧ (m.seed ≠ 0 → m.pos = m'.pos) := by
  obtain ⟨h, x₀, e, d, m₀, hh, hx, hx₀, hr, hA, rfl⟩ := hm
  obtain ⟨h', x₁, e', d', m₁, hh', hx', hx₁, hr', hA', rfl⟩ := hm'
  obtain ⟨s₀, hs₀, hs₀'⟩ := M.exists_par_of_anchor hA
  obtain rfl := M.green_par_unique hs₀ hs₀' hh hh'
  obtain rfl : d = d' := by simpa [hx] using hx'
  have hroot : S.root h x₀ = S.root h x₁ := hr.symm.trans hr'
  obtain ⟨s, hA⟩ := hA
  obtain ⟨s', hA'⟩ := hA'
  have hs : M.IsPar s ∧ ((M.par s).IsTile ∨ (M.par s).IsStep) := by
    rcases hA with ⟨j, o, h₁, -⟩ | ⟨h₁, -⟩
    · have h₂ : (M.par s).IsTile := by simp [h₁, Atom.IsTile]
      exact ⟨M.isPar_of_isTile h₂, .inl h₂⟩
    · exact ⟨M.isPar_of_isStep h₁, .inr h₁⟩
  have hs' : M.IsPar s' ∧ ((M.par s').IsTile ∨ (M.par s').IsStep) := by
    rcases hA' with ⟨j, o, h₁, -⟩ | ⟨h₁, -⟩
    · have h₂ : (M.par s').IsTile := by simp [h₁, Atom.IsTile]
      exact ⟨M.isPar_of_isTile h₂, .inl h₂⟩
    · exact ⟨M.isPar_of_isStep h₁, .inr h₁⟩
  obtain rfl : s = s' := by
    have hne : M.par h ≠ M.par s := fun heq => by
      simp [← heq, hh, Atom.IsTile, Atom.IsStep] at hs
    rcases M.eq_of_isPar (M.isPar_of_green hh) hs.1 hs'.1 hne with h₁ | h₁
    · simp [h₁, hh, Atom.IsTile, Atom.IsStep] at hs'
    · exact h₁.symm
  rcases hA with ⟨j, o, hj, hnear, rfl⟩ | ⟨hstep, htile, rfl⟩ <;>
    rcases hA' with ⟨j', o', hj', hnear', rfl⟩ | ⟨hstep', htile', rfl⟩
  · obtain ⟨rfl, rfl⟩ : j = j' ∧ o = o' := by simpa [hj] using hj'
    refine ⟨rfl, fun hj0 => ?_⟩
    have key : S.pot h x₁ = S.pot h x₀ + ((S.lab s x₁).sgn - (S.lab s x₀).sgn) := by
      by_cases hsg : S.lab h s = green d .forward
      · have aux (y : D) (hy : S.lab h y = green d .forward)
            (hny : y = s ∨ (S.lab s y).IsStep) : S.pot h y = S.pot h s + (S.lab s y).sgn := by
          rcases hny with rfl | hstep
          · rw [((hS.isUnit_iff y y).mpr rfl).eq_unit]
            simp [Atom.sgn]
          · obtain ⟨e₁, o₁, hl⟩ := Atom.isStep_iff.mp hstep
            cases o₁
            · rw [hl, (hS.step_class hsg hy hl).2]
              simp [Atom.sgn]
            · rw [hl, (hS.step_class hy hsg (hS.typed.eq_conv hl)).2]
              simp [Atom.sgn]
        rw [aux x₀ hx₀ hnear, aux x₁ hx₁ hnear']
        ring
      · have h0 : (S.lab s x₀).IsStep := hnear.resolve_left fun h' => hsg (h' ▸ hx₀)
        have h1 : (S.lab s x₁).IsStep := hnear'.resolve_left fun h' => hsg (h' ▸ hx₁)
        by_cases hx01 : x₀ = x₁
        · subst hx01
          ring
        · have hU : UCond S.lab S.root d h s := ⟨x₀, x₁, ⟨hx01, hx₀, hx₁, hroot⟩,
            by rwa [← hS.typed.conv_lab, Atom.isStep_conv],
            by rwa [← hS.typed.conv_lab, Atom.isStep_conv]⟩
          rcases hS.u_class hU with hg | hu
          · exact (hsg hg).elim
          · exact (hj0 (M.par_tile_eq_zero hS hu hh hj)).elim
    simp only [key]
    module
  · simp [hj, Atom.IsStep] at hstep'
  · simp [hj', Atom.IsStep] at hstep
  · by_cases hx01 : x₀ = x₁
    · subst hx01
      exact ⟨rfl, fun _ => rfl⟩
    · have hV : VCond S.lab S.root (fun a y => (S.lab a y).IsTile) d h s :=
        ⟨x₀, x₁, ⟨hx01, hx₀, hx₁, hroot⟩, htile, htile'⟩
      rcases hS.v_class hV with hg | hv
      · obtain ⟨h₁, h₂⟩ := hS.cell_class hx₀ hx₁ hg hroot
        refine ⟨h₁.symm, fun h0 => ?_⟩
        simp only [h₂ h0]
        module
      · exact (M.not_isStep_par hS hv hh hstep).elim

include hS in
private theorem candCell_spec {x : D} {m : Cell L} (hm : M.Cand x m) :
    (M.candCell x).seed = m.seed ∧ (m.seed ≠ 0 → (M.candCell x).pos = m.pos) := by
  have hc : ∃ m, M.Cand x m := ⟨m, hm⟩
  obtain ⟨h₁, h₂⟩ := M.cand_unique hS hm hc.choose_spec
  simp only [candCell, hc, ↓reduceDIte]
  exact ⟨h₁.symm, fun h0 => (h₂ h0).symm⟩

omit [NeZero L.length] in
private theorem candCell_of_not {x : D} (hm : ¬∃ m, M.Cand x m) [NeZero L.length] :
    M.candCell x = ⟨0, 0⟩ := by
  simp [candCell, hm]

include hS in
private theorem good_next : Good T (M.next T) := sorry

end Move

/-! ### The winning strategy -/

variable (T) in
/-- The networks that ∃ plays: those of the labellings that satisfy the invariant, with their
nodes numbered. -/
private def winning (n : ℕ) : Set (AtomicNetwork (tilingFrame L) (Fin n)) :=
  {N | ∃ (D : Type) (S : Ann L D) (hS : Good T S) (e : Fin n ≃ D),
    N = hS.network.comap e.toEmbedding}

private theorem hasWinningStrategy_of_tilings (T : Tilings L) :
    (tilingFrame L).HasWinningStrategy := by
  refine .of_forall_exists_comap_castSucc (winning T) (fun a => ?_) ?_
  · by_cases ha : a.IsUnit
    · refine ⟨1, _, ⟨Unit, _, Ann.good_single a.src, finOneEquiv, rfl⟩, 0, 0, ?_⟩
      exact ha.eq_unit.symm
    · exact ⟨2, _, ⟨Bool, _, Ann.good_pair ha, finTwoEquiv, rfl⟩, 0, 1, rfl⟩
  · rintro n _ ⟨D, S, hS, e, rfl⟩ i j a b hab hfresh
    have hfresh' (w : D) (hw : S.lab (e i) w = a) : S.lab w (e j) ≠ b := by
      simpa [Good.network, hw] using hfresh (e.symm w)
    let M : Move S := ⟨e i, e j, a, b, hab, hfresh'⟩
    refine ⟨_, ⟨Option D, _, M.good_next hS, finSuccEquivLast.trans (Equiv.optionCongr e), rfl⟩,
      ?_, ?_, ?_⟩
    · ext x y
      simp [Good.network, M.next_lab_some]
    · simpa [Good.network] using M.next_lab_p (T := T)
    · simpa [Good.network] using M.next_lab_q hS

end Tiling

open Tiling

/-- Theorem 4 of [HirschHodkinson2001]: if every position of `L` is at the origin of a tiling by
positions of `L`, and the tile at position `0` matches itself horizontally and vertically, then ∃
has a winning strategy in the game on `tilingFrame L`. The source asks that the tile `T₀` have one
colour on its four edges, used by no other tile; the strategy labels with `T₀` the tile edges
that it does not place in a tiling, for which the two equations suffice. -/
public theorem hasWinningStrategy_tilingFrame {L : List WangTile} (hL : 0 < L.length)
    (hrow : L[0].right = L[0].left) (hcol : L[0].top = L[0].bottom) (h : EveryIndexOccurs L) :
    (tilingFrame L).HasWinningStrategy := by
  have : NeZero L.length := ⟨hL.ne'⟩
  choose F hF₀ hF using h
  refine hasWinningStrategy_of_tilings
    { til := fun σ c => if σ = 0 then 0 else F σ c.1 c.2
      til_zero := fun c => by simp
      til_origin := fun σ => by by_cases hσ : σ = 0 <;> simp [hσ, hF₀]
      til_match := fun σ c d => ?_ }
  by_cases hσ : σ = 0
  · cases d <;> simp [hσ, Axis.front, Axis.back, hrow, hcol]
  · cases d
    · simpa [hσ, Axis.front, Axis.back, Axis.vec] using (hF σ c.1 c.2).1
    · simpa [hσ, Axis.front, Axis.back, Axis.vec] using (hF σ c.1 c.2).2

end Cslib.RelationAlgebra
