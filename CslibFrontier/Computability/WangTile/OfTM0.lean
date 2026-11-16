/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
public import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Finite TM0 computations as seeded quadrant tilings

A finite Post–Turing machine is folded onto a one-sided tape, pairing source positions
`-(i + 1)` and `i` at position `i`. A tile records a two-row, three-cell window of its
computation. Position tags force the finite input along the bottom row; a constant tail
completes that row. A seeded quadrant tiling exists exactly when the machine does not halt.
This does not establish undecidability of the unseeded plane domino problem.

## Main definitions

* `Cslib.WangTile.OfTM0.seededInstance`: the finite seeded palette for a machine and input.

## Main results

* `Cslib.WangTile.OfTM0.tilesQuadrant_instance_iff`: seeded quadrant tilings are equivalent
  to nontermination of the given `Turing.TM0` computation.
* `Cslib.WangTile.OfTM0.primrec_seededInstance`: the palette construction for a fixed finite
  machine is primitive recursive in its input.

## References

Adapted from `lean-wang`, revision `64268a3`, `LeanWang/Robinson/Machine/`, including
`UniversalTM0/Folded.lean`. The simulation here applies to arbitrary finite `TM0` machines.
-/

noncomputable section

namespace Cslib.WangTile.OfTM0

private inductive Move where
  | left | right | stay
  deriving DecidableEq

private instance : Fintype Move :=
  ⟨{.left, .right, .stay}, by rintro (_ | _ | _) <;> simp⟩

private def Move.apply : Move → ℕ → ℕ
  | .left, i => i.pred
  | .right, i => i + 1
  | .stay, i => i

/-- A single update of the private one-sided simulation. -/
private structure Action (S Q : Type) where
  write : S
  state : Q
  move : Move
  deriving DecidableEq, Fintype

/-- The private typed target of tape folding. -/
private structure OneMachine (S Q : Type) where
  blank : S
  start : Q
  halt : Q
  step : Q → S → Action S Q

/-- A one-sided simulation configuration. -/
private structure Config (S Q : Type) where
  tape : ℕ → S
  head : ℕ
  state : Q

variable {S Q : Type} [Fintype S] [Fintype Q] [DecidableEq S] [DecidableEq Q]

@[ext] private theorem Config.ext {x y : Config S Q}
    (htape : x.tape = y.tape) (hhead : x.head = y.head) (hstate : x.state = y.state) :
    x = y := by
  cases x
  cases y
  cases htape
  cases hhead
  cases hstate
  rfl

namespace OneMachine

/-- One machine step. Halting configurations are fixed points. -/
private def nextID (M : OneMachine S Q) (c : Config S Q) : Config S Q :=
  if c.state = M.halt then
    c
  else
    let read := c.tape c.head
    let ⟨write, state', move⟩ := M.step c.state read
    { tape := fun i => if i = c.head then write else c.tape i
      head := move.apply c.head
      state := state' }

@[simp]
private theorem nextID_of_halt (M : OneMachine S Q) (c : Config S Q) (h : c.state = M.halt) :
    M.nextID c = c := by
  simp [nextID, h]

private theorem nextID_of_ne_halt {M : OneMachine S Q} {c : Config S Q} (h : c.state ≠ M.halt) :
    M.nextID c =
      let read := c.tape c.head
      let ⟨write, state', move⟩ := M.step c.state read
      { tape := fun i => if i = c.head then write else c.tape i
        head := move.apply c.head
        state := state' } := by
  simp [nextID, h]

private theorem nextID_state_of_ne_halt {M : OneMachine S Q} {c : Config S Q} (h : c.state ≠ M.halt) :
    (M.nextID c).state = (M.step c.state (c.tape c.head)).state := by
  rw [nextID_of_ne_halt h]

private theorem nextID_head_of_ne_halt {M : OneMachine S Q} {c : Config S Q} (h : c.state ≠ M.halt) :
    (M.nextID c).head = (M.step c.state (c.tape c.head)).move.apply c.head := by
  rw [nextID_of_ne_halt h]

private theorem nextID_tape_head_of_ne_halt {M : OneMachine S Q} {c : Config S Q} (h : c.state ≠ M.halt) :
    (M.nextID c).tape c.head = (M.step c.state (c.tape c.head)).write := by
  rw [nextID_of_ne_halt h]
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  simp [hstep]

private theorem nextID_tape_of_ne_head {M : OneMachine S Q} {c : Config S Q} {i : Nat} (hi : i ≠ c.head) :
    (M.nextID c).tape i = c.tape i := by
  by_cases h : c.state = M.halt
  · simp [nextID, h]
  · rw [nextID_of_ne_halt h]
    rcases M.step c.state (c.tape c.head) with ⟨write, state', move⟩
    simp [hi]

end OneMachine

/-- A cell in a local space-time window, including the left boundary marker. -/
private inductive Cell (S Q : Type) where
  | boundary
  | plain (symbol : S)
  | head (state : Q) (symbol : S)
  deriving DecidableEq, Fintype

private instance : Primcodable (Cell S Q) :=
  Primcodable.ofEquiv _ (Fintype.equivFin _)

private def Cell.Mem (M : OneMachine S Q) : Cell S Q → Prop
  | .head q _ => q ≠ M.halt
  | _ => True

private instance (M : OneMachine S Q) (c : Cell S Q) : Decidable (c.Mem M) :=
  match c with
  | .head q _ => inferInstanceAs (Decidable (q ≠ M.halt))
  | .boundary | .plain _ => isTrue trivial
namespace Config

/-- Read one configuration position as a row cell for the space-time diagram. -/
private def cellAt (c : Config S Q) (i : Nat) : Cell S Q :=
  if i = c.head then
    Cell.head c.state (c.tape i)
  else
    Cell.plain (c.tape i)

@[simp]
private theorem cellAt_head (c : Config S Q) :
    c.cellAt c.head = Cell.head c.state (c.tape c.head) := by
  simp [cellAt]

private theorem cellAt_of_ne {c : Config S Q} {i : Nat} (hi : i ≠ c.head) :
    c.cellAt i = Cell.plain (c.tape i) := by
  simp [cellAt, hi]

private theorem cellAt_ne_boundary (c : Config S Q) (i : Nat) :
    c.cellAt i ≠ Cell.boundary := by
  by_cases hi : i = c.head
  · simp [cellAt, hi]
  · simp [cellAt, hi]

/-- The cell immediately left of a position, using a boundary marker at `0`. -/
private def cellAtLeft (c : Config S Q) : Nat → Cell S Q
  | 0 => Cell.boundary
  | i + 1 => c.cellAt i

@[simp]
private theorem cellAtLeft_zero (c : Config S Q) :
    c.cellAtLeft 0 = Cell.boundary :=
  rfl

@[simp]
private theorem cellAtLeft_succ (c : Config S Q) (i : Nat) :
    c.cellAtLeft (i + 1) = c.cellAt i :=
  rfl


private theorem cellAt_mem {M : OneMachine S Q} {c : Config S Q}
    (hstate : c.state ≠ M.halt) (i : ℕ) : (c.cellAt i).Mem M := by
  by_cases hi : i = c.head <;> simp [cellAt, Cell.Mem, hi, hstate]

private theorem cellAtLeft_mem {M : OneMachine S Q} {c : Config S Q}
    (hstate : c.state ≠ M.halt) (i : ℕ) : (c.cellAtLeft i).Mem M := by
  cases i with
  | zero => trivial
  | succ i => exact cellAt_mem hstate i

end Config

private def machineCells (M : OneMachine S Q) : List (Cell S Q) :=
  Finset.univ.toList.filter fun c => decide (c.Mem M)

private theorem mem_machineCells_iff (M : OneMachine S Q) (c : Cell S Q) :
    c ∈ machineCells M ↔ c.Mem M := by
  simp [machineCells]
private def localNextCell? (M : OneMachine S Q) (left center right : Cell S Q) : Option (Cell S Q) :=
  match left, center, right with
  | _, Cell.boundary, _ => none
  | _, Cell.head q a, _ =>
      if _h : q = M.halt then
        none
      else
        let ⟨write, q', move⟩ := M.step q a
        match left, move with
        | Cell.boundary, Move.left =>
            if q' = M.halt then none else some (Cell.head q' write)
        | _, Move.stay =>
            if q' = M.halt then none else some (Cell.head q' write)
        | _, _ => some (Cell.plain write)
  | Cell.head q a, Cell.plain b, _ =>
      if _h : q = M.halt then
        none
      else
        let ⟨_write, q', move⟩ := M.step q a
        match move with
        | Move.right => if q' = M.halt then none else some (Cell.head q' b)
        | Move.left | Move.stay => some (Cell.plain b)
  | _, Cell.plain b, Cell.head q a =>
      if _h : q = M.halt then
        none
      else
        let ⟨_write, q', move⟩ := M.step q a
        match move with
        | Move.left => if q' = M.halt then none else some (Cell.head q' b)
        | Move.right | Move.stay => some (Cell.plain b)
  | Cell.boundary, Cell.plain b, _ =>
      some (Cell.plain b)
  | _, Cell.plain b, _ =>
      some (Cell.plain b)

namespace OneMachine

private theorem localNextCell?_cellAt_or_halt {M : OneMachine S Q} {c : Config S Q} {pos : Nat}
    (hstate : c.state ≠ M.halt) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      if (M.nextID c).state = M.halt ∧ pos = (M.nextID c).head then
        none
      else
        some ((M.nextID c).cellAt pos) := by
  rcases hstep : M.step c.state (c.tape c.head) with ⟨write, state', move⟩
  by_cases hcenter : pos = c.head
  · subst pos
    cases hhead : c.head with
    | zero =>
        cases move <;>
          simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
            Move.apply]
    | succ pred =>
        cases move <;>
          simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
            Move.apply]
  · by_cases hleft : c.head = pos + 1
    · cases hpos : pos with
      | zero =>
          cases move <;>
            simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
              Move.apply]
      | succ pred =>
          have hpred : pred ≠ pred + 1 + 1 := by omega
          cases move <;>
            simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
              Move.apply]
    · by_cases hright : pos = c.head + 1
      · subst pos
        cases hhead : c.head with
        | zero =>
            cases move <;>
              simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
                Move.apply]
        | succ pred =>
            have hpred : pred + 1 + 1 ≠ pred := by omega
            cases move <;>
              simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID, localNextCell?,
                Move.apply]
      · cases hpos : pos with
        | zero =>
            cases hhead : c.head with
            | zero => omega
            | succ pred =>
                cases move <;>
                  (simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID,
                    localNextCell?, Move.apply]
                   try omega)
        | succ posPred =>
            cases hhead : c.head with
            | zero =>
                cases move <;>
                  simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID,
                    localNextCell?, Move.apply]
            | succ headPred =>
                have hleftCell : posPred ≠ headPred + 1 := by omega
                have hcenterCell : posPred ≠ headPred := by omega
                have hrightCell : posPred + 1 + 1 ≠ headPred + 1 := by omega
                have hnewLeft : posPred + 1 ≠ headPred := by omega
                have hnewRight : posPred + 1 ≠ headPred + 1 + 1 := by omega
                cases move <;>
                  simp_all [Config.cellAt, Config.cellAtLeft, OneMachine.nextID,
                    localNextCell?, Move.apply]

private theorem localNextCell?_cellAt {M : OneMachine S Q} {c : Config S Q} {pos : Nat}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).state ≠ M.halt) :
    localNextCell? M (c.cellAtLeft pos) (c.cellAt pos) (c.cellAt (pos + 1)) =
      some ((M.nextID c).cellAt pos) := by
  rw [localNextCell?_cellAt_or_halt hstate]
  simp [OneMachine.nextID, hstate, hnextState]

private theorem localNextCell?_at_next_halt_head {M : OneMachine S Q} {c : Config S Q}
    (hstate : c.state ≠ M.halt)
    (hnextState : (M.step c.state (c.tape c.head)).state = M.halt) :
    localNextCell? M
        (c.cellAtLeft ((M.step c.state (c.tape c.head)).move.apply c.head))
        (c.cellAt ((M.step c.state (c.tape c.head)).move.apply c.head))
        (c.cellAt ((M.step c.state (c.tape c.head)).move.apply c.head + 1)) =
      none := by
  rw [localNextCell?_cellAt_or_halt hstate]
  simp [OneMachine.nextID, hstate, hnextState]

end OneMachine

/-- The two overlapping triples carried by a history tile. -/
private structure History (S Q : Type) where
  prevLeft : Cell S Q
  prevCenter : Cell S Q
  prevRight : Cell S Q
  nextLeft : Cell S Q
  nextCenter : Cell S Q
  nextRight : Cell S Q
  deriving DecidableEq

private def History.equivProd : History S Q ≃
    Cell S Q × Cell S Q × Cell S Q × Cell S Q × Cell S Q × Cell S Q where
  toFun t := (t.prevLeft, t.prevCenter, t.prevRight, t.nextLeft, t.nextCenter, t.nextRight)
  invFun := fun (a, b, c, d, e, f) => ⟨a, b, c, d, e, f⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : Fintype (History S Q) :=
  Fintype.ofEquiv _ History.equivProd.symm

private instance : Primcodable (History S Q) :=
  Primcodable.ofEquiv _ (Fintype.equivFin _)

private def machineHistoryTiles (M : OneMachine S Q) : List (History S Q) :=
  Finset.univ.toList.filter fun t =>
    decide (t.prevLeft.Mem M ∧ t.prevCenter.Mem M ∧ t.prevRight.Mem M ∧
      t.nextLeft.Mem M ∧ t.nextCenter.Mem M ∧ t.nextRight.Mem M ∧
      localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter ∧
      (t.prevLeft = .boundary → t.nextLeft = .boundary))

private theorem mem_machineHistoryTiles_iff (M : OneMachine S Q) (t : History S Q) :
    t ∈ machineHistoryTiles M ↔
      t.prevLeft.Mem M ∧ t.prevCenter.Mem M ∧ t.prevRight.Mem M ∧
      t.nextLeft.Mem M ∧ t.nextCenter.Mem M ∧ t.nextRight.Mem M ∧
      localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter ∧
      (t.prevLeft = .boundary → t.nextLeft = .boundary) := by
  simp only [machineHistoryTiles, List.mem_filter, Finset.mem_toList,
    Finset.mem_univ, true_and, decide_eq_true_eq]
/-- A finite word followed by the machine's blank symbol. -/
private def tape (blank : S) (input : List S) (position : Nat) : S :=
  input[position]?.getD blank

/-- The standard initial configuration carrying a finite input word. -/
private def initialID (M : OneMachine S Q) (input : List S) : Config S Q where
  tape := tape M.blank input
  head := 0
  state := M.start

/-- Run `M` from the finite input word rather than the empty tape. -/
private def run (M : OneMachine S Q) (input : List S) (steps : Nat) : Config S Q :=
  Nat.iterate M.nextID steps (initialID M input)

/-- Halting of `M` on a finite input word. -/
private def Halts (M : OneMachine S Q) (input : List S) : Prop :=
  ∃ steps, (run M input steps).state = M.halt

/-- A halting computation has a first halting time and is nonhalting before
it. -/
private theorem exists_first_halting_time {M : OneMachine S Q} {input : List S}
    (halts : Halts M input) :
    ∃ steps, (run M input steps).state = M.halt ∧
      ∀ previous, previous < steps →
        (run M input previous).state ≠ M.halt := by
  let steps := Nat.find halts
  refine ⟨steps, Nat.find_spec halts, ?_⟩
  intro previous before hhalt
  exact (Nat.not_lt_of_ge (Nat.find_min' halts hhalt)) before

/-- Iterate a machine until its next step enters the absorbing halt state. -/
private def transition (M : OneMachine S Q) (id : Config S Q) : Option (Config S Q) :=
  let next := M.nextID id
  if next.state = M.halt then none else some next

private theorem transition_eq_none_iff (M : OneMachine S Q) (id : Config S Q) :
    transition M id = none ↔ (M.nextID id).state = M.halt := by
  simp [transition]

private theorem mem_transition_nextID {M : OneMachine S Q} {current next : Config S Q}
    (hnext : next ∈ transition M current) :
    next = M.nextID current := by
  by_cases hhalt : (M.nextID current).state = M.halt
  · simp [transition, hhalt] at hnext
  · have hnext' : M.nextID current = next := by
      simpa [transition, hhalt] using hnext
    exact hnext'.symm

@[simp] theorem run_zero (M : OneMachine S Q) (input : List S) :
    run M input 0 = initialID M input :=
  rfl

@[simp] theorem run_succ (M : OneMachine S Q) (input : List S) (steps : Nat) :
    run M input (steps + 1) = M.nextID (run M input steps) := by
  unfold run
  rw [Function.iterate_succ_apply']

@[simp] theorem tape_eq_blank_of_length_le
    {blank : S} {input : List S} {position : Nat}
    (hposition : input.length ≤ position) :
    tape blank input position = blank := by
  simp [tape, List.getElem?_eq_none_iff.mpr hposition]

private theorem run_state_ne_halt_of_not_halts {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input) (steps : Nat) :
    (run M input steps).state ≠ M.halt := by
  intro hhalt
  exact notHalts ⟨steps, hhalt⟩

private theorem run_state_eq_halt_of_le {M : OneMachine S Q} {input : List S}
    {first second : Nat} (hle : first ≤ second)
    (hhalt : (run M input first).state = M.halt) :
    (run M input second).state = M.halt := by
  rcases Nat.exists_eq_add_of_le hle with ⟨extra, rfl⟩
  clear hle
  induction extra with
  | zero => simpa using hhalt
  | succ extra ih =>
      rw [show first + (extra + 1) = first + extra + 1 by omega, run_succ]
      rw [OneMachine.nextID_of_halt M _ ih]
      exact ih

private theorem transition_reaches_run_of_ne_halt {M : OneMachine S Q} {input : List S}
    {steps : Nat} (hne : (run M input steps).state ≠ M.halt) :
    StateTransition.Reaches (transition M)
      (initialID M input) (run M input steps) := by
  induction steps with
  | zero => exact Relation.ReflTransGen.refl
  | succ steps ih =>
      have hprevious : (run M input steps).state ≠ M.halt := by
        intro hhalt
        exact hne (run_state_eq_halt_of_le (Nat.le_succ steps) hhalt)
      have hnextNe : (M.nextID (run M input steps)).state ≠ M.halt := by
        simpa [run_succ] using hne
      have hnext : transition M (run M input steps) =
          some (run M input (steps + 1)) := by
        rw [run_succ]
        simp [transition, hnextNe]
      exact Relation.ReflTransGen.tail (ih hprevious) hnext

private theorem reaches_transition_eq_run {M : OneMachine S Q} {input : List S} {id : Config S Q}
    (hreaches : StateTransition.Reaches (transition M)
      (initialID M input) id) :
    ∃ steps, id = run M input steps := by
  induction hreaches with
  | refl => exact ⟨0, rfl⟩
  | tail hreach hstep ih =>
      rcases ih with ⟨steps, rfl⟩
      have hid := mem_transition_nextID hstep
      refine ⟨steps + 1, ?_⟩
      rw [run_succ]
      exact hid

private theorem transition_eval_dom_iff_halts (M : OneMachine S Q) (input : List S) :
    (StateTransition.eval (transition M) (initialID M input)).Dom ↔
      Halts M input := by
  constructor
  · intro hdom
    rcases Part.dom_iff_mem.1 hdom with ⟨terminal, hterminal⟩
    rcases StateTransition.mem_eval.1 hterminal with ⟨hreaches, hnone⟩
    rcases reaches_transition_eq_run hreaches with ⟨steps, rfl⟩
    refine ⟨steps + 1, ?_⟩
    rw [run_succ]
    exact (transition_eq_none_iff M _).1 hnone
  · intro halts
    rcases exists_first_halting_time halts with
      ⟨steps, hhalt, before⟩
    cases steps with
    | zero =>
        have hinitial : (initialID M input).state = M.halt := by
          simpa using hhalt
        apply Part.dom_iff_mem.2
        refine ⟨initialID M input, StateTransition.mem_eval.2 ⟨?_, ?_⟩⟩
        · exact Relation.ReflTransGen.refl
        · apply (transition_eq_none_iff M _).2
          rw [OneMachine.nextID_of_halt M _ hinitial]
          exact hinitial
    | succ steps =>
        apply Part.dom_iff_mem.2
        refine ⟨run M input steps, StateTransition.mem_eval.2 ⟨?_, ?_⟩⟩
        · exact transition_reaches_run_of_ne_halt (before steps (by omega))
        · apply (transition_eq_none_iff M _).2
          simpa [run_succ] using hhalt

/-- The local cells along a simulation run. -/
private def runCell (M : OneMachine S Q) (input : List S) (time position : ℕ) : Cell S Q :=
  (run M input time).cellAt position

private def runCellLeft (M : OneMachine S Q) (input : List S) (time position : ℕ) : Cell S Q :=
  (run M input time).cellAtLeft position
private theorem runCell_mem {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input)
    (time position : Nat) :
    (runCell M input time position).Mem M := by
  exact Config.cellAt_mem (run_state_ne_halt_of_not_halts notHalts time) position

private theorem runCellLeft_mem {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input)
    (time position : Nat) :
    (runCellLeft M input time position).Mem M := by
  exact Config.cellAtLeft_mem (run_state_ne_halt_of_not_halts notHalts time) position

/-- A local history block cut from two rows of a finite-input run. -/
private def historyTile (M : OneMachine S Q) (input : List S) (time position : Nat) :
    History S Q where
  prevLeft := runCellLeft M input time position
  prevCenter := runCell M input time position
  prevRight := runCell M input time (position + 1)
  nextLeft := runCellLeft M input (time + 1) position
  nextCenter := runCell M input (time + 1) position
  nextRight := runCell M input (time + 1) (position + 1)

private theorem historyTile_hMatches (M : OneMachine S Q) (input : List S)
    (time position : Nat) :
    (historyTile M input time position).prevCenter =
        (historyTile M input time (position + 1)).prevLeft ∧
      (historyTile M input time position).prevRight =
        (historyTile M input time (position + 1)).prevCenter ∧
      (historyTile M input time position).nextCenter =
        (historyTile M input time (position + 1)).nextLeft ∧
      (historyTile M input time position).nextRight =
        (historyTile M input time (position + 1)).nextCenter := by
  simp [historyTile, runCellLeft, runCell, run_succ]

private theorem historyTile_cells_mem {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input)
    (time position : Nat) :
    (historyTile M input time position).prevLeft.Mem M ∧
      (historyTile M input time position).prevCenter.Mem M ∧
      (historyTile M input time position).prevRight.Mem M ∧
      (historyTile M input time position).nextLeft.Mem M ∧
      (historyTile M input time position).nextCenter.Mem M ∧
      (historyTile M input time position).nextRight.Mem M := by
  simp [historyTile, runCellLeft_mem notHalts,
    runCell_mem notHalts]

private theorem historyTile_local_of_state_ne_halt {M : OneMachine S Q} {input : List S}
    {time : Nat}
    (hstate : (run M input time).state ≠ M.halt)
    (hnext : (run M input (time + 1)).state ≠ M.halt)
    (position : Nat) :
    localNextCell? M (historyTile M input time position).prevLeft
        (historyTile M input time position).prevCenter
        (historyTile M input time position).prevRight =
      some (historyTile M input time position).nextCenter := by
  let c := run M input time
  have hstate' : c.state ≠ M.halt := by simpa [c] using hstate
  have hnextState : (M.step c.state (c.tape c.head)).state ≠ M.halt := by
    rw [← OneMachine.nextID_state_of_ne_halt hstate']
    simpa [c, run_succ] using hnext
  simpa [historyTile, runCell, runCellLeft, c, run_succ] using
    OneMachine.localNextCell?_cellAt
      (M := M) (c := c) (pos := position) hstate' hnextState

private theorem historyTile_local {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input) (time position : Nat) :
    localNextCell? M (historyTile M input time position).prevLeft
        (historyTile M input time position).prevCenter
        (historyTile M input time position).prevRight =
      some (historyTile M input time position).nextCenter := by
  exact historyTile_local_of_state_ne_halt
    (run_state_ne_halt_of_not_halts notHalts time)
    (run_state_ne_halt_of_not_halts notHalts (time + 1)) position

private theorem historyTile_boundaryOK (M : OneMachine S Q) (input : List S)
    (time position : Nat) :
    (historyTile M input time position).prevLeft = Cell.boundary →
      (historyTile M input time position).nextLeft = Cell.boundary := by
  cases position with
  | zero => simp [historyTile, runCellLeft]
  | succ position =>
      intro hprev
      have hnot : (run M input time).cellAt position ≠ Cell.boundary :=
        Config.cellAt_ne_boundary (run M input time) position
      exact False.elim (hnot (by
        simpa [historyTile, runCellLeft] using hprev))

private theorem historyTile_mem_machineHistoryTiles {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input)
    (time position : Nat) :
    historyTile M input time position ∈ machineHistoryTiles M := by
  rcases historyTile_cells_mem notHalts time position with
    ⟨hprevLeft, hprevCenter, hprevRight, hnextLeft, hnextCenter, hnextRight⟩
  exact (mem_machineHistoryTiles_iff M _).2
    ⟨hprevLeft, hprevCenter, hprevRight, hnextLeft, hnextCenter, hnextRight,
      historyTile_local notHalts time position, historyTile_boundaryOK M input time position⟩


private theorem localNextCell?_of_mem_machineHistoryTiles {M : OneMachine S Q}
    {t : History S Q} (h : t ∈ machineHistoryTiles M) :
    localNextCell? M t.prevLeft t.prevCenter t.prevRight = some t.nextCenter := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := (mem_machineHistoryTiles_iff M t).mp h
  exact h

private theorem nextLeft_boundary_of_mem_machineHistoryTiles {M : OneMachine S Q}
    {t : History S Q} (h : t ∈ machineHistoryTiles M)
    (hb : t.prevLeft = .boundary) : t.nextLeft = .boundary := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := (mem_machineHistoryTiles_iff M t).mp h
  exact h hb

private theorem prevCenter_not_halt_of_mem_machineHistoryTiles {M : OneMachine S Q}
    {t : History S Q} {a : S} (h : t ∈ machineHistoryTiles M) :
    t.prevCenter ≠ Cell.head M.halt a := by
  obtain ⟨_, hc, _⟩ := (mem_machineHistoryTiles_iff M t).mp h
  intro heq
  simpa [heq, Cell.Mem] using hc

private def Cell.code : Cell S Q → ℕ := Encodable.encode

private theorem Cell.code_injective : Function.Injective (Cell.code (S := S) (Q := Q)) :=
  Encodable.encode_injective
private def pairCellColor (a b : Cell S Q) : Nat :=
  Nat.pair a.code b.code

private theorem pairCellColor_eq_iff {a b c d : Cell S Q} :
    pairCellColor a b = pairCellColor c d ↔ a = c ∧ b = d := by
  unfold pairCellColor
  rw [Nat.pair_eq_pair]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨Cell.code_injective ha, Cell.code_injective hb⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Encode a row triple as one Wang color. -/
private def tripleCellColor (a b c : Cell S Q) : Nat :=
  Nat.pair a.code (Nat.pair b.code c.code)

private theorem tripleCellColor_eq_iff {a b c d e f : Cell S Q} :
    tripleCellColor a b c = tripleCellColor d e f ↔ a = d ∧ b = e ∧ c = f := by
  unfold tripleCellColor
  rw [Nat.pair_eq_pair, Nat.pair_eq_pair]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨Cell.code_injective ha,
      Cell.code_injective hb, Cell.code_injective hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

/-- Encode the two-column overlap of two consecutive local-history tiles. -/
private def overlapCellColor (prev₀ prev₁ next₀ next₁ : Cell S Q) : Nat :=
  Nat.pair (pairCellColor prev₀ prev₁) (pairCellColor next₀ next₁)

private theorem overlapCellColor_eq_iff {a b c d e f g h : Cell S Q} :
    overlapCellColor a b c d = overlapCellColor e f g h ↔
      a = e ∧ b = f ∧ c = g ∧ d = h := by
  unfold overlapCellColor
  rw [Nat.pair_eq_pair, pairCellColor_eq_iff, pairCellColor_eq_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    exact ⟨ha, hb, hc, hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

private def initialRowTag : Nat := 0

private def normalRowTag : Nat := 1

private theorem initialRowTag_ne_normalRowTag :
    initialRowTag ≠ normalRowTag := by
  decide

private def taggedTripleCellColor (tag : Nat) (a b c : Cell S Q) : Nat :=
  Nat.pair tag (tripleCellColor a b c)

private theorem taggedTripleCellColor_eq_iff {tag tag' : Nat}
    {a b c d e f : Cell S Q} :
    taggedTripleCellColor tag a b c = taggedTripleCellColor tag' d e f ↔
      tag = tag' ∧ a = d ∧ b = e ∧ c = f := by
  unfold taggedTripleCellColor
  rw [Nat.pair_eq_pair, tripleCellColor_eq_iff]

private def taggedOverlapCellColor (tag : Nat)
    (prev₀ prev₁ next₀ next₁ : Cell S Q) : Nat :=
  Nat.pair tag (overlapCellColor prev₀ prev₁ next₀ next₁)

private theorem taggedOverlapCellColor_eq_iff {tag tag' : Nat}
    {a b c d e f g h : Cell S Q} :
    taggedOverlapCellColor tag a b c d = taggedOverlapCellColor tag' e f g h ↔
      tag = tag' ∧ a = e ∧ b = f ∧ c = g ∧ d = h := by
  unfold taggedOverlapCellColor
  rw [Nat.pair_eq_pair, overlapCellColor_eq_iff]

private abbrev HMatches (a b : WangTile) : Prop := a.right = b.left
private abbrev VMatches (a b : WangTile) : Prop := a.top = b.bottom

private def horizontalColor (positionTag rowTag : Nat)
    (prevLeft prevRight nextLeft nextRight : Cell S Q) : Nat :=
  Nat.pair positionTag
    (taggedOverlapCellColor rowTag prevLeft prevRight nextLeft nextRight)

private def toWangTile (westTag eastTag rowTag nextRowTag : Nat)
    (tile : History S Q) : WangTile where
  top := taggedTripleCellColor nextRowTag
    tile.nextLeft tile.nextCenter tile.nextRight
  bottom := taggedTripleCellColor rowTag
    tile.prevLeft tile.prevCenter tile.prevRight
  right := horizontalColor eastTag rowTag
    tile.prevCenter tile.prevRight tile.nextCenter tile.nextRight
  left := horizontalColor westTag rowTag
    tile.prevLeft tile.prevCenter tile.nextLeft tile.nextCenter

private theorem hMatches_toWangTile_iff
    (westTag eastTag westTag' eastTag' rowTag nextRowTag rowTag' nextRowTag' : Nat)
    (left right : History S Q) :
    HMatches
        (toWangTile westTag eastTag rowTag nextRowTag left)
        (toWangTile westTag' eastTag' rowTag' nextRowTag' right) ↔
      eastTag = westTag' ∧ rowTag = rowTag' ∧
        left.prevCenter = right.prevLeft ∧
        left.prevRight = right.prevCenter ∧
        left.nextCenter = right.nextLeft ∧
        left.nextRight = right.nextCenter := by
  simp [HMatches, toWangTile, horizontalColor, Nat.pair_eq_pair,
    taggedOverlapCellColor_eq_iff]

private theorem vMatches_toWangTile_iff
    (westTag eastTag westTag' eastTag' rowTag nextRowTag rowTag' nextRowTag' : Nat)
    (lower upper : History S Q) :
    VMatches
        (toWangTile westTag eastTag rowTag nextRowTag lower)
        (toWangTile westTag' eastTag' rowTag' nextRowTag' upper) ↔
      nextRowTag = rowTag' ∧
        lower.nextLeft = upper.prevLeft ∧
        lower.nextCenter = upper.prevCenter ∧
        lower.nextRight = upper.prevRight := by
  simp [VMatches, toWangTile, taggedTripleCellColor_eq_iff]

/- The input-specific palette consists of a finite prefix followed by one
constant blank tile.  The `+ 3` margin covers both the width-three local window
and the possible one-cell head move in the first transition. -/

/-- Past this position, the time-zero local history is a constant blank tail. -/
private def tailPosition (input : List S) : Nat :=
  input.length + 3

private theorem run_zero_cell_eq_plain_blank
    (M : OneMachine S Q) (input : List S) {position : Nat}
    (hlength : input.length ≤ position) (hpositive : 0 < position) :
    (run M input 0).cellAt position = Cell.plain M.blank := by
  simp [run_zero, initialID, Config.cellAt, tape,
    List.getElem?_eq_none_iff.mpr hlength, Nat.ne_of_gt hpositive]

private theorem run_zero_cellLeft_eq_plain_blank
    (M : OneMachine S Q) (input : List S) {position : Nat}
    (hlength : input.length < position) (htwo : 2 ≤ position) :
    (run M input 0).cellAtLeft position = Cell.plain M.blank := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
  simp only [Config.cellAtLeft_succ]
  exact run_zero_cell_eq_plain_blank M input (by omega) (by omega)

private theorem run_one_cell_eq_plain_blank
    (M : OneMachine S Q) (input : List S) {position : Nat}
    (hlength : input.length ≤ position) (htwo : 2 ≤ position) :
    (run M input 1).cellAt position = Cell.plain M.blank := by
  by_cases hhalt : M.start = M.halt
  · have hinitial : (initialID M input).state = M.halt := by
      simpa [initialID] using hhalt
    rw [show 1 = 0 + 1 by omega, run_succ, run_zero,
      OneMachine.nextID_of_halt M _ hinitial]
    exact run_zero_cell_eq_plain_blank M input hlength (by omega)
  · have hstate : (initialID M input).state ≠ M.halt := by
      simpa [initialID] using hhalt
    have hhead : (M.nextID (initialID M input)).head ≤ 1 := by
      rw [OneMachine.nextID_head_of_ne_halt hstate]
      rcases hstep : M.step M.start (tape M.blank input 0) with
        ⟨write, state, move⟩
      change (M.step M.start (tape M.blank input 0)).move.apply 0 ≤ 1
      rw [hstep]
      cases move <;> simp [Move.apply]
    rw [show 1 = 0 + 1 by omega, run_succ, run_zero]
    rw [Config.cellAt_of_ne (by omega : position ≠ (M.nextID (initialID M input)).head)]
    congr 1
    rw [OneMachine.nextID_tape_of_ne_head (by simp [initialID]; omega)]
    exact tape_eq_blank_of_length_le hlength

private theorem run_one_cellLeft_eq_plain_blank
    (M : OneMachine S Q) (input : List S) {position : Nat}
    (hlength : input.length + 1 < position) (hthree : 3 ≤ position) :
    (run M input 1).cellAtLeft position = Cell.plain M.blank := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
  simp only [Config.cellAtLeft_succ]
  exact run_one_cell_eq_plain_blank M input (by omega) (by omega)

private def blankHistoryTile (M : OneMachine S Q) : History S Q where
  prevLeft := .plain M.blank
  prevCenter := .plain M.blank
  prevRight := .plain M.blank
  nextLeft := .plain M.blank
  nextCenter := .plain M.blank
  nextRight := .plain M.blank

private theorem historyTile_zero_eq_blank_of_tailPosition_le
    (M : OneMachine S Q) (input : List S) {position : Nat}
    (hposition : tailPosition input ≤ position) :
    historyTile M input 0 position = blankHistoryTile M := by
  have hp : input.length + 3 ≤ position := by
    simpa [tailPosition] using hposition
  unfold historyTile runCell runCellLeft blankHistoryTile
  simp only [Nat.zero_add]
  rw [run_zero_cellLeft_eq_plain_blank M input (by omega) (by omega)]
  rw [run_zero_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_zero_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cellLeft_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cell_eq_plain_blank M input (by omega) (by omega)]
  rw [run_one_cell_eq_plain_blank M input (by omega) (by omega)]

private theorem historyTile_zero_eq_tail_of_tailPosition_le
    (M : OneMachine S Q) (input : List S) {position : Nat}
    (hposition : tailPosition input ≤ position) :
    historyTile M input 0 position =
      historyTile M input 0 (tailPosition input) := by
  rw [historyTile_zero_eq_blank_of_tailPosition_le M input hposition]
  rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]

private def initialTile (M : OneMachine S Q) (input : List S) (position : Nat) : WangTile :=
  let tail := tailPosition input
  if position < tail then
    toWangTile position (position + 1) initialRowTag normalRowTag
      (historyTile M input 0 position)
  else
    toWangTile tail tail initialRowTag normalRowTag
      (historyTile M input 0 tail)

private def initialTiles (M : OneMachine S Q) (input : List S) : List WangTile :=
  ((List.range (tailPosition input)).map fun position =>
      toWangTile position (position + 1) initialRowTag normalRowTag
        (historyTile M input 0 position)) ++
    [toWangTile (tailPosition input) (tailPosition input)
      initialRowTag normalRowTag
      (historyTile M input 0 (tailPosition input))]

private def normalTiles (M : OneMachine S Q) : List WangTile :=
  (machineHistoryTiles M).map
    (toWangTile 0 0 normalRowTag normalRowTag)

private def tiles (M : OneMachine S Q) (input : List S) : List WangTile :=
  initialTiles M input ++ normalTiles M

private def seed (M : OneMachine S Q) (input : List S) : WangTile :=
  initialTile M input 0

private theorem initialTile_mem (M : OneMachine S Q) (input : List S) (position : Nat) :
    initialTile M input position ∈ initialTiles M input := by
  rw [initialTile]
  split_ifs with hposition
  · rw [initialTiles, List.mem_append]
    left
    rw [List.mem_map]
    exact ⟨position, by simp [hposition], rfl⟩
  · rw [initialTiles, List.mem_append]
    right
    simp

private theorem initialTile_history (M : OneMachine S Q) (input : List S) (position : Nat) :
    let tail := tailPosition input
    initialTile M input position =
      if position < tail then
        toWangTile position (position + 1) initialRowTag normalRowTag
          (historyTile M input 0 position)
      else
        toWangTile tail tail initialRowTag normalRowTag
          (historyTile M input 0 position) := by
  dsimp
  rw [initialTile]
  split_ifs with hposition
  · rfl
  · congr 1
    exact (historyTile_zero_eq_tail_of_tailPosition_le M input (by omega)).symm

private theorem initialTile_hMatches (M : OneMachine S Q) (input : List S) (position : Nat) :
    HMatches (initialTile M input position)
      (initialTile M input (position + 1)) := by
  rw [initialTile_history, initialTile_history]
  by_cases hposition : position + 1 < tailPosition input
  · simp [hposition, show position < tailPosition input by omega,
      hMatches_toWangTile_iff]
    exact historyTile_hMatches M input 0 position
  · have htail : tailPosition input ≤ position + 1 := by omega
    by_cases hbefore : position < tailPosition input
    · have heq : position + 1 = tailPosition input := by omega
      simp [hbefore, heq, hMatches_toWangTile_iff]
      rw [← heq]
      exact historyTile_hMatches M input 0 position
    · simp [hbefore, hposition, hMatches_toWangTile_iff]
      rw [historyTile_zero_eq_tail_of_tailPosition_le M input (by omega :
        tailPosition input ≤ position)]
      rw [historyTile_zero_eq_tail_of_tailPosition_le M input htail]
      rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]
      simp [blankHistoryTile]

/- Soundness: place the actual history tile at `(position, time)`.  Time zero
uses the tagged finite-input row, while all later rows use the fixed normal
palette.  Horizontal and vertical validity are then direct overlap facts. -/

private def runTile (M : OneMachine S Q) (input : List S) (time position : Nat) : WangTile :=
  if time = 0 then initialTile M input position
  else toWangTile 0 0 normalRowTag normalRowTag
    (historyTile M input time position)

private theorem runTile_mem {M : OneMachine S Q} {input : List S}
    (notHalts : ¬ Halts M input)
    (time position : Nat) :
    runTile M input time position ∈ tiles M input := by
  cases time with
  | zero => simp [runTile, tiles, initialTile_mem]
  | succ time =>
      rw [runTile, if_neg (by omega)]
      simp only [tiles, List.mem_append]
      right
      rw [normalTiles, List.mem_map]
      exact ⟨historyTile M input (time + 1) position,
        historyTile_mem_machineHistoryTiles notHalts
          (time + 1) position, rfl⟩

private theorem runTile_hMatches (M : OneMachine S Q) (input : List S)
    (time position : Nat) :
    HMatches (runTile M input time position)
      (runTile M input time (position + 1)) := by
  cases time with
  | zero => simpa [runTile] using initialTile_hMatches M input position
  | succ time =>
      simp [runTile, hMatches_toWangTile_iff]
      exact historyTile_hMatches M input (time + 1) position

private theorem runTile_vMatches (M : OneMachine S Q) (input : List S)
    (time position : Nat) :
    VMatches (runTile M input time position)
      (runTile M input (time + 1) position) := by
  cases time with
  | zero =>
      rw [runTile, if_pos rfl, runTile, if_neg (by omega)]
      rw [initialTile_history]
      split_ifs <;> simp [vMatches_toWangTile_iff, historyTile]
  | succ time =>
      simp [runTile, vMatches_toWangTile_iff, historyTile]

private theorem tilesQuarterWithSeed_of_not_halts
    {M : OneMachine S Q} {input : List S} (notHalts : ¬ Halts M input) :
    TilesQuadrant ⟨tiles M input, seed M input⟩ := by
  refine ⟨fun x y => runTile M input y x, rfl, ?_⟩
  intro x y
  exact ⟨runTile_mem notHalts y x, runTile_hMatches M input y x,
    runTile_vMatches M input y x⟩

/- Completeness starts by classifying every palette member.  The seed fixes
position zero, horizontal tags force its unique successor repeatedly, and the
self-looping tail handles all remaining positions.  Since every legal north
edge is tagged `normal`, vertical matching excludes another initial tile above
the bottom row. -/

private theorem mem_tiles_iff (M : OneMachine S Q) (input : List S) (tile : WangTile) :
    tile ∈ tiles M input ↔
      (∃ position, position < tailPosition input ∧
        toWangTile position (position + 1) initialRowTag normalRowTag
          (historyTile M input 0 position) = tile) ∨
      tile = toWangTile (tailPosition input) (tailPosition input)
          initialRowTag normalRowTag
          (historyTile M input 0 (tailPosition input)) ∨
      ∃ history, history ∈ machineHistoryTiles M ∧
        toWangTile 0 0 normalRowTag normalRowTag history = tile := by
  simp [tiles, initialTiles, normalTiles, List.mem_map]

/-- Every legal tile presents the normal-row tag on its north edge. -/
private theorem northRowTag_eq_normal_of_mem
    {M : OneMachine S Q} {input : List S} {tile : WangTile}
    (member : tile ∈ tiles M input) :
    tile.top.unpair.1 = normalRowTag := by
  rcases (mem_tiles_iff M input tile).1 member with
    ⟨position, _hposition, rfl⟩ | rfl | ⟨history, _hhistory, rfl⟩ <;>
    simp [toWangTile, taggedTripleCellColor]

private theorem next_initialTile_of_hMatches_mem
    (M : OneMachine S Q) (input : List S) (position : Nat) {right : WangTile}
    (hmatch : HMatches (initialTile M input position) right)
    (hmem : right ∈ tiles M input) :
    right = initialTile M input (position + 1) := by
  rcases (mem_tiles_iff M input right).1 hmem with
    ⟨next, hnext, hright⟩ | hright | ⟨history, _hhistory, hright⟩
  · rw [initialTile] at hmatch ⊢
    split_ifs at hmatch with hposition
    · rw [← hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      have heq : next = position + 1 := htags.1.symm
      subst next
      rw [if_pos hnext]
      exact hright.symm
    · rw [← hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      omega
  · rw [initialTile] at hmatch ⊢
    split_ifs at hmatch with hposition
    · rw [hright] at hmatch
      have htags := (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch
      have heq : position + 1 = tailPosition input := htags.1
      rw [if_neg (by omega)]
      exact hright
    · rw [if_neg (by omega)]
      exact hright
  · rw [initialTile] at hmatch
    split_ifs at hmatch <;> rw [← hright] at hmatch
    · exact False.elim (initialRowTag_ne_normalRowTag
        ((hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch).2.1)
    · exact False.elim (initialRowTag_ne_normalRowTag
        ((hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hmatch).2.1)

private theorem seeded_tiling_row_zero_eq
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (seeded : plane (0) (0) = seed M input) :
    ∀ position, plane (position) (0) = initialTile M input position := by
  intro position
  induction position with
  | zero => exact seeded
  | succ position ih =>
      apply next_initialTile_of_hMatches_mem M input position
      · simpa [ih] using (valid (position) (0)).2.1
      · exact (valid (position + 1) (0)).1

private theorem normal_of_vMatches
    (M : OneMachine S Q) (input : List S) {lower upper : WangTile}
    (lowerMem : lower ∈ tiles M input) (upperMem : upper ∈ tiles M input)
    (hmatches : VMatches lower upper) :
    ∃ history, history ∈ machineHistoryTiles M ∧
      toWangTile 0 0 normalRowTag normalRowTag history = upper := by
  have upperRowTag : upper.bottom.unpair.1 = normalRowTag := by
    rw [← hmatches]
    exact northRowTag_eq_normal_of_mem lowerMem
  rcases (mem_tiles_iff M input upper).1 upperMem with
    ⟨upperPosition, _hupperPosition, hupper⟩ | hupper |
      ⟨upperHistory, hupperHistory, hupper⟩
  · have tagEq : initialRowTag = normalRowTag := by
      simpa [← hupper, toWangTile, taggedTripleCellColor] using upperRowTag
    exact (initialRowTag_ne_normalRowTag tagEq).elim
  · have tagEq : initialRowTag = normalRowTag := by
      simpa [hupper, toWangTile, taggedTripleCellColor] using upperRowTag
    exact (initialRowTag_ne_normalRowTag tagEq).elim
  · exact ⟨upperHistory, hupperHistory, hupper⟩

private theorem positive_row_decode
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (time position : Nat) :
    ∃ history, history ∈ machineHistoryTiles M ∧
      toWangTile 0 0 normalRowTag normalRowTag history =
        plane (position) (time + 1) := by
  exact normal_of_vMatches M input
    (valid (position) (time)).1 (valid (position) (time + 1)).1
    ((valid (position) (time)).2.2)

/-- A decoded positive row, represented by a coherent row of local history
tiles whose lower cells are the corresponding machine configuration. -/
private structure IsDecodedHistoryRow (M : OneMachine S Q) (input : List S)
    (plane : Nat → Nat → WangTile) (time : Nat)
    (row : Nat → History S Q) : Prop where
  mem (position : Nat) : row position ∈ machineHistoryTiles M
  encoded (position : Nat) :
    toWangTile 0 0 normalRowTag normalRowTag (row position) =
      plane (position) (time)
  prevCells (position : Nat) :
    (row position).prevLeft = (historyTile M input time position).prevLeft ∧
      (row position).prevCenter = (historyTile M input time position).prevCenter ∧
      (row position).prevRight = (historyTile M input time position).prevRight

private def DecodedHistoryRow (M : OneMachine S Q) (input : List S)
    (plane : Nat → Nat → WangTile) (time : Nat) : Prop :=
  ∃ row, IsDecodedHistoryRow M input plane time row

/- A decoded row remembers more than tile membership: its lower triples equal
the true machine configuration at that time.  Local transition validity fixes
each upper center; overlap with neighboring tiles fixes the upper left and
right cells.  Vertical matching then transfers all three cells to the lower
triple of the next row. -/

private theorem row_one_decoded
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (seeded : plane (0) (0) = seed M input) :
    DecodedHistoryRow M input plane 1 := by
  choose row hrow using fun position => positive_row_decode valid 0 position
  refine ⟨row, ⟨fun position => (hrow position).1,
    fun position => (hrow position).2, ?_⟩⟩
  intro position
  have hbottom := seeded_tiling_row_zero_eq valid seeded position
  have hvertical : VMatches
      (initialTile M input position)
      (toWangTile 0 0 normalRowTag normalRowTag (row position)) := by
    simpa [hbottom, (hrow position).2] using (valid (position) (0)).2.2
  rw [initialTile_history] at hvertical
  split_ifs at hvertical <;>
    have hcells := (vMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hvertical
  all_goals
    exact ⟨by simpa [historyTile] using hcells.2.1.symm,
      by simpa [historyTile] using hcells.2.2.1.symm,
      by simpa [historyTile] using hcells.2.2.2.symm⟩

private theorem positive_row_hMatches_cells
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    {time position : Nat} {left right : History S Q}
    (hleft : toWangTile 0 0 normalRowTag normalRowTag left =
      plane (position) (time + 1))
    (hright : toWangTile 0 0 normalRowTag normalRowTag right =
      plane (position + 1) (time + 1)) :
    left.prevCenter = right.prevLeft ∧
      left.prevRight = right.prevCenter ∧
      left.nextCenter = right.nextLeft ∧
      left.nextRight = right.nextCenter := by
  have hhorizontal : HMatches
      (toWangTile 0 0 normalRowTag normalRowTag left)
      (toWangTile 0 0 normalRowTag normalRowTag right) := by
    simpa [hleft, hright] using (valid (position) (time + 1)).2.1
  exact (hMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hhorizontal |>.2.2

private theorem nextCenter_eq_historyTile_nextCenter_of_prev_cells
    {M : OneMachine S Q} {input : List S} {time position : Nat}
    {tile : History S Q}
    (tileMem : tile ∈ machineHistoryTiles M)
    (hstate : (run M input time).state ≠ M.halt)
    (hnext : (run M input (time + 1)).state ≠ M.halt)
    (hprevLeft : tile.prevLeft = (historyTile M input time position).prevLeft)
    (hprevCenter : tile.prevCenter = (historyTile M input time position).prevCenter)
    (hprevRight : tile.prevRight = (historyTile M input time position).prevRight) :
    tile.nextCenter = (historyTile M input time position).nextCenter := by
  have hlocal := localNextCell?_of_mem_machineHistoryTiles tileMem
  rw [hprevLeft, hprevCenter, hprevRight] at hlocal
  have hrun := historyTile_local_of_state_ne_halt hstate hnext position
  rw [hrun] at hlocal
  exact Option.some.inj hlocal.symm

/-- Local transition validity and horizontal matching determine all three
upper cells of a decoded history row. -/
private theorem next_cells_eq_historyTile_of_decoded_row
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    {time : Nat} {row : Nat → History S Q}
    (decoded : IsDecodedHistoryRow M input plane (time + 1) row)
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state ≠ M.halt)
    (position : Nat) :
    (row position).nextLeft =
        (historyTile M input (time + 1 + 1) position).prevLeft ∧
      (row position).nextCenter =
        (historyTile M input (time + 1 + 1) position).prevCenter ∧
      (row position).nextRight =
        (historyTile M input (time + 1 + 1) position).prevRight := by
  have nextCenter (p : Nat) :
      (row p).nextCenter = (historyTile M input (time + 1) p).nextCenter :=
    nextCenter_eq_historyTile_nextCenter_of_prev_cells
      (decoded.mem p) hstate hnext
      (decoded.prevCells p).1 (decoded.prevCells p).2.1
      (decoded.prevCells p).2.2
  have nextLeft : (row position).nextLeft =
      (historyTile M input (time + 1 + 1) position).prevLeft := by
    cases position with
    | zero =>
        rw [nextLeft_boundary_of_mem_machineHistoryTiles (decoded.mem 0)
          (by simpa [historyTile, runCellLeft] using (decoded.prevCells 0).1)]
        simp [historyTile, runCellLeft]
    | succ predecessor =>
        have hmatches := positive_row_hMatches_cells valid
          (time := time) (position := predecessor)
          (decoded.encoded predecessor) (decoded.encoded (predecessor + 1))
        calc
          (row (Nat.succ predecessor)).nextLeft =
              (row predecessor).nextCenter := by
            simpa [Nat.succ_eq_add_one] using hmatches.2.2.1.symm
          _ = (historyTile M input (time + 1) predecessor).nextCenter :=
            nextCenter predecessor
          _ = (historyTile M input (time + 1 + 1)
              (Nat.succ predecessor)).prevLeft := by
            simp [historyTile, runCellLeft, runCell, Nat.succ_eq_add_one]
  have hmatches := positive_row_hMatches_cells valid
    (time := time) (position := position)
    (decoded.encoded position) (decoded.encoded (position + 1))
  exact ⟨nextLeft,
    by simpa [historyTile] using nextCenter position,
    calc
      (row position).nextRight = (row (position + 1)).nextCenter :=
        hmatches.2.2.2
      _ = (historyTile M input (time + 1) (position + 1)).nextCenter :=
        nextCenter (position + 1)
      _ = (historyTile M input (time + 1 + 1) position).prevRight := by
        simp [historyTile]⟩

private theorem next_row_decoded
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    {time : Nat}
    (hrow : DecodedHistoryRow M input plane (time + 1))
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state ≠ M.halt) :
    DecodedHistoryRow M input plane (time + 1 + 1) := by
  rcases hrow with ⟨lower, decoded⟩
  choose upper hupper using fun position =>
    positive_row_decode valid (time + 1) position
  refine ⟨upper, ⟨fun position => (hupper position).1,
    fun position => (hupper position).2, ?_⟩⟩
  intro position
  have hvertical : VMatches
      (toWangTile 0 0 normalRowTag normalRowTag (lower position))
      (toWangTile 0 0 normalRowTag normalRowTag (upper position)) := by
    simpa [decoded.encoded position, (hupper position).2] using
      (valid (position) (time + 1)).2.2
  have cells := (vMatches_toWangTile_iff _ _ _ _ _ _ _ _ _ _).1 hvertical
  have nextCells := next_cells_eq_historyTile_of_decoded_row
    valid decoded hstate hnext position
  exact ⟨cells.2.1.symm.trans nextCells.1,
    cells.2.2.1.symm.trans nextCells.2.1,
    cells.2.2.2.symm.trans nextCells.2.2⟩

private theorem decoded_row_of_nonhalting_prefix
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (seeded : plane (0) (0) = seed M input) (time : Nat)
    (hprefix : ∀ step, 1 ≤ step → step ≤ time + 1 →
      (run M input step).state ≠ M.halt) :
    DecodedHistoryRow M input plane (time + 1) := by
  induction time with
  | zero => exact row_one_decoded valid seeded
  | succ time ih =>
      exact next_row_decoded valid
        (time := time)
        (ih fun step hstep hbound => hprefix step hstep (by omega))
        (hprefix (time + 1) (by omega) (by omega))
        (hprefix (time + 1 + 1) (by omega) (by omega))

/- At the first halting time, all preceding positive rows can be decoded.  If
halting occurs immediately, row one already contains a forbidden halt head.
Otherwise the tile at the next head position would have to realize a local
transition into `halt`, which the normal palette explicitly omits. -/

private theorem false_of_run_one_halt
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    (valid : ∀ x y, plane x y ∈ tiles M input ∧
      HMatches (plane x y) (plane (x + 1) y) ∧ VMatches (plane x y) (plane x (y + 1)))
    (seeded : plane (0) (0) = seed M input)
    (hhalt : (run M input 1).state = M.halt) : False := by
  let position := (run M input 1).head
  rcases row_one_decoded valid seeded with ⟨row, decoded⟩
  apply prevCenter_not_halt_of_mem_machineHistoryTiles
    (a := (run M input 1).tape (run M input 1).head) (decoded.mem position)
  rw [(decoded.prevCells position).2.1]
  change (run M input 1).cellAt position =
    Cell.head M.halt ((run M input 1).tape (run M input 1).head)
  dsimp only [position]
  rw [Config.cellAt_head, hhalt]

private theorem false_of_next_halt_from_decoded_row
    {M : OneMachine S Q} {input : List S}
    {plane : Nat → Nat → WangTile}
    {time : Nat}
    (hrow : DecodedHistoryRow M input plane (time + 1))
    (hstate : (run M input (time + 1)).state ≠ M.halt)
    (hnext : (run M input (time + 1 + 1)).state = M.halt) : False := by
  let configuration := run M input (time + 1)
  let position :=
    (M.step configuration.state (configuration.tape configuration.head)).move.apply
      configuration.head
  rcases hrow with ⟨row, decoded⟩
  let tile := row position
  have tileMem := decoded.mem position
  have prevCells := decoded.prevCells position
  have hstate' : configuration.state ≠ M.halt := by
    simpa [configuration] using hstate
  have hnextState :
      (M.step configuration.state (configuration.tape configuration.head)).state =
        M.halt := by
    rw [← OneMachine.nextID_state_of_ne_halt hstate']
    simpa [configuration, run_succ] using hnext
  have hlocal := localNextCell?_of_mem_machineHistoryTiles tileMem
  rw [prevCells.1, prevCells.2.1, prevCells.2.2] at hlocal
  have hnone := OneMachine.localNextCell?_at_next_halt_head
    (M := M) (c := configuration) hstate' hnextState
  have hnoneRun :
      localNextCell? M (historyTile M input (time + 1) position).prevLeft
          (historyTile M input (time + 1) position).prevCenter
          (historyTile M input (time + 1) position).prevRight = none := by
    simpa [historyTile, runCell, runCellLeft, configuration, position] using hnone
  rw [hnoneRun] at hlocal
  cases hlocal

private theorem not_tilesQuarterWithSeed_of_halts
    {M : OneMachine S Q} {input : List S} (halts : Halts M input) :
    ¬ TilesQuadrant ⟨tiles M input, seed M input⟩ := by
  rcases exists_first_halting_time halts with ⟨step, hhalt, before⟩
  rintro ⟨plane, seeded, valid⟩
  cases step with
  | zero =>
      apply false_of_run_one_halt valid seeded
      have hinitial : (initialID M input).state = M.halt := by
        simpa [run_zero] using hhalt
      rw [show 1 = 0 + 1 by omega, run_succ, run_zero,
        OneMachine.nextID_of_halt M _ hinitial]
      exact hinitial
  | succ step =>
      cases step with
      | zero =>
          exact false_of_run_one_halt valid seeded (by simpa using hhalt)
      | succ time =>
          have hrow := decoded_row_of_nonhalting_prefix
            valid seeded time (fun k _positive bounded => before k (by omega))
          exact false_of_next_halt_from_decoded_row hrow
            (before (time + 1) (by omega)) (by simpa using hhalt)

private theorem tilesQuarterWithSeed_iff_not_halts
    {M : OneMachine S Q} {input : List S} :
    TilesQuadrant ⟨tiles M input, seed M input⟩ ↔ ¬ Halts M input := by
  constructor
  · intro tiled halts
    exact not_tilesQuarterWithSeed_of_halts halts tiled
  · exact tilesQuarterWithSeed_of_not_halts

end Cslib.WangTile.OfTM0
