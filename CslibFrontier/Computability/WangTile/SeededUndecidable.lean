/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.OfTM0
public import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Universal
public import Mathlib.Computability.Halting

/-!
# Undecidability of seeded-quadrant Wang tiling

There is no algorithm deciding whether a finite palette tiles the natural-number quadrant with
a prescribed southwest tile [Robinson1971, §4, pp. 190–192]. The reduction sends a partial
recursive code to the computation tiles of the fixed universal finite-state `TM0` machine,
initialized with that code's input.
The resulting seeded quadrant is tileable precisely when the code does not halt on zero.
Unlike the source's combined write-and-move instructions, Mathlib's `TM0` writes or moves
in separate steps; tape folding and input tags give an explicit quadrant construction.

This is the **seeded-quadrant** problem. Undecidability of the unseeded integer-plane domino
problem requires a separate seed-removal construction and remains open here.

## Main definitions

* `Cslib.WangTile.seededReduction`: a primitive-recursive map from codes to seeded palettes.

## Main results

* `Cslib.WangTile.tilesQuadrant_seededReduction_iff`: exact correspondence with nonhalting.
* `Cslib.WangTile.not_computablePred_tilesQuadrant`: seeded-quadrant tiling is undecidable.

## References

* [R. M. Robinson, *Undecidability and nonperiodicity for tilings of the plane*][Robinson1971]

The prior formalization is [lean-wang, revision 64268a3, Robinson reduction](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Reduction.lean).
Here the machine and input coding reuse `Turing.TM0.Universal`.
-/

public section

namespace Cslib.WangTile

open Turing.TM0.Universal

open Classical in
/-- Encode a code's run on zero as a seeded-quadrant tiling instance of the fixed universal
machine. Tiles are coded in field order, and an instance as `(tiles, seed)`. -/
noncomputable def seededReduction (c : Nat.Partrec.Code) : SeededInstance :=
  OfTM0.seededInstance M₀' (input (Encodable.encode c))

/-- The map from partial recursive codes to seeded-quadrant instances is primitive recursive. -/
theorem primrec_seededReduction : Primrec seededReduction := by
  classical
  exact (OfTM0.primrec_seededInstance M₀').comp (primrec_input.comp Primrec.encode)

/-- The universal computation tiles a seeded quadrant exactly when the code does not halt. -/
theorem tilesQuadrant_seededReduction_iff (c : Nat.Partrec.Code) :
    TilesQuadrant (seededReduction c) ↔ ¬ (c.eval 0).Dom := by
  classical
  rw [seededReduction, OfTM0.tilesQuadrant_instance_iff, eval_dom_iff,
    Denumerable.ofNat_encode]

/-- **Seeded-quadrant tiling is undecidable** [Robinson1971, §4, pp. 190–192]. This does not
assert undecidability of the unseeded plane domino problem. -/
theorem not_computablePred_tilesQuadrant : ¬ ComputablePred TilesQuadrant := by
  intro h
  have hn : ComputablePred (fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom) :=
    ComputablePred.computable_of_manyOneReducible
      ⟨seededReduction, primrec_seededReduction.to_comp,
        fun c => (tilesQuadrant_seededReduction_iff c).symm⟩ h
  exact ComputablePred.halting_problem 0 (hn.not.of_eq fun _ => not_not)

end Cslib.WangTile
