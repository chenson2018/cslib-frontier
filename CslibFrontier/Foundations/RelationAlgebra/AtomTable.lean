/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RelationAlgebra.Game
public import Mathlib.Computability.Primrec.List
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite relation algebras as tables of atoms

A finite relation algebra is the complex algebra of its atom structure, which is given by finitely
much data: the number of atoms, the converse of each, which of them lie below the identity, and
the triples `(a, b, c)` with `c ≤ a ; b`. An `AtomTable` records these as numbers and lists of
numbers, so that finite relation algebras become the instances of decision problems in the sense
of Mathlib's `ComputablePred` and many-one reducibility.

A table need not describe an atom structure: the lists may be malformed, and the laws of an atom
structure, associativity among them, may fail. `AtomTable.Presents` relates a table to the atom
structure it describes, of which there is at most one.

## Main definitions

* `Cslib.RelationAlgebra.AtomStructure.map`, `Cslib.RelationAlgebra.ComplexAlgebra.mapEquiv`: an
  atom structure with its atoms renamed along a bijection, and the isomorphism of complex
  algebras.
* `Cslib.RelationAlgebra.AtomTable`: tables, coded as tuples `(size, conv, id, cycles)`.
* `Cslib.RelationAlgebra.AtomTable.Presents`: a table presents an atom structure on `Fin size`.
* `Cslib.RelationAlgebra.AtomTable.IsRepresentable`: a table presents an atom structure whose
  complex algebra is representable.

## Main results

* `Cslib.RelationAlgebra.Representation.representable`: a finite relation algebra with a
  representation whose index and base types lie in any universes is representable.
* `Cslib.RelationAlgebraEquiv.representable_iff`: isomorphic finite relation algebras, in any
  universes, are both representable or both not.
* `Cslib.RelationAlgebra.AtomTable.Presents.unique`: a table presents at most one atom structure.
* `Cslib.RelationAlgebra.AtomTable.exists_presents_equiv`: every finite relation algebra is
  isomorphic to the complex algebra of an atom structure presented by a table.
-/

public section

universe u v w

namespace Cslib

open RelationAlgebra

namespace RelationAlgebra

/-- A finite relation algebra that has a representation, with index and base types in any
universes, is representable. For finite algebras this is the `representable_univ` wanted
upstream. -/
theorem Representation.representable {α : Type u} [RelationAlgebra α] [Finite α] {ι : Type v}
    {β : ι → Type w} (r : Representation α ι β) : Representable α := by
  cases nonempty_fintype α
  let : CompleteAtomicRelationAlgebra α :=
    { ‹RelationAlgebra α›, Fintype.toCompleteAtomicBooleanAlgebra α with }
  have e : RelationAlgebraEquiv α (ComplexAlgebra (atomStructure α)) := complexAlgebraEquiv
  exact (representable_iff_hasWinningStrategy α).mpr (Representation.hasWinningStrategy
    ⟨r.hom.comp e.symm.toHom, r.injective.comp (EquivLike.injective e.symm)⟩)

end RelationAlgebra

/-- Isomorphic finite relation algebras are both representable or both not, whatever their
universes. -/
theorem RelationAlgebraEquiv.representable_iff {α : Type u} {β : Type v} [RelationAlgebra α]
    [RelationAlgebra β] [Finite α] (e : RelationAlgebraEquiv α β) :
    Representable α ↔ Representable β := by
  have : Finite β := .of_equiv α e
  exact ⟨fun ⟨_, _, ⟨r⟩⟩ => Representation.representable
      ⟨r.hom.comp e.symm.toHom, r.injective.comp (EquivLike.injective e.symm)⟩,
    fun ⟨_, _, ⟨r⟩⟩ => Representation.representable
      ⟨r.hom.comp e.toHom, r.injective.comp (EquivLike.injective e)⟩⟩

namespace RelationAlgebra

/-! ### Renaming atoms -/

variable {α β : Type*}

/-- The atom structure obtained by renaming the atoms along a bijection. -/
@[expose, simps]
def AtomStructure.map (A : AtomStructure α) (e : α ≃ β) : AtomStructure β where
  conv b := e (A.conv (e.symm b))
  id := e.symm ⁻¹' A.id
  cycles := {c | (e.symm c.1, e.symm c.2.1, e.symm c.2.2) ∈ A.cycles}
  assoc h₁ h₂ :=
    let ⟨q, hq₁, hq₂⟩ := A.assoc h₁ h₂
    ⟨e q, by simpa using hq₁, by simpa using hq₂⟩
  id_cycle_right hs h := e.symm.injective (A.id_cycle_right hs h)
  exists_id_cycle_right r :=
    let ⟨s, hs, h⟩ := A.exists_id_cycle_right (e.symm r)
    ⟨e s, by simpa using hs, by simpa using h⟩
  cycle_left h := by simpa using A.cycle_left h

@[simp]
theorem AtomStructure.map_map_symm (A : AtomStructure α) (e : α ≃ β) :
    (A.map e).map e.symm = A := by
  obtain ⟨conv, id, cycles, _, _, _, _⟩ := A
  simp only [AtomStructure.map, AtomStructure.mk.injEq]
  exact ⟨funext fun a => by simp, Set.ext fun a => by simp, Set.ext fun a => by simp⟩

/-- Renaming the atoms of an atom structure gives an isomorphic complex algebra. -/
def ComplexAlgebra.mapEquiv (A : AtomStructure α) (e : α ≃ β) :
    RelationAlgebraEquiv (ComplexAlgebra A) (ComplexAlgebra (A.map e)) where
  toFun x := ⟨e.symm ⁻¹' x.carrier⟩
  invFun y := ⟨e ⁻¹' y.carrier⟩
  left_inv x := by
    ext a
    change e.symm (e a) ∈ x.carrier ↔ a ∈ x
    rw [e.symm_apply_apply, ComplexAlgebra.mem_carrier]
  right_inv y := by
    ext b
    change e (e.symm b) ∈ y.carrier ↔ b ∈ y
    rw [e.apply_symm_apply, ComplexAlgebra.mem_carrier]
  map_rel_iff' {x y} := by
    refine ⟨fun h a ha => ?_, fun h a ha => h ha⟩
    have : e.symm (e a) ∈ y.carrier :=
      h (a := e a) (show e.symm (e a) ∈ x.carrier by rwa [e.symm_apply_apply])
    rwa [e.symm_apply_apply] at this
  map_mul' x y := by
    ext c
    constructor
    · rintro ⟨r, hr, s, hs, h⟩
      exact ⟨e r, show e.symm (e r) ∈ x.carrier by rwa [e.symm_apply_apply],
        e s, show e.symm (e s) ∈ y.carrier by rwa [e.symm_apply_apply], by simpa using h⟩
    · rintro ⟨r, hr, s, hs, h⟩
      exact ⟨e.symm r, hr, e.symm s, hs, h⟩
  map_star' x := by
    ext c
    change e.symm c ∈ star x ↔ c ∈ star (_ : ComplexAlgebra (A.map e))
    simp only [ComplexAlgebra.mem_star]
    change _ ↔ e.symm (e (A.conv (e.symm c))) ∈ x
    rw [e.symm_apply_apply]

/-! ### Tables -/

/-- A finite atom table with atoms `0, …, size - 1`. -/
structure AtomTable where
  /-- The number of atoms. -/
  size : ℕ
  /-- `conv[a]` is the converse of the atom `a`. -/
  conv : List ℕ
  /-- The identity atoms. -/
  id : List ℕ
  /-- The consistent triples: `(a, b, c)` says `c ≤ a ; b`. -/
  cycles : List (ℕ × ℕ × ℕ)

namespace AtomTable

/-- A table is coded as the tuple `(size, conv, id, cycles)`. -/
@[expose] def equivProd : AtomTable ≃ ℕ × List ℕ × List ℕ × List (ℕ × ℕ × ℕ) where
  toFun t := (t.size, t.conv, t.id, t.cycles)
  invFun := fun (size, conv, id, cycles) => ⟨size, conv, id, cycles⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable AtomTable := Primcodable.ofEquiv _ equivProd

/-- The table `t` presents the atom structure `A` on `Fin t.size`. -/
structure Presents (t : AtomTable) (A : AtomStructure (Fin t.size)) : Prop where
  /-- The converse of each atom is the entry of the list `conv` at its position. -/
  conv (a : Fin t.size) : t.conv[a.val]? = some (A.conv a).val
  /-- The identity atoms are those listed in `id`. -/
  id (a : Fin t.size) : a ∈ A.id ↔ a.val ∈ t.id
  /-- The cycles are the triples listed in `cycles`. -/
  cycles (a b c : Fin t.size) : (a, b, c) ∈ A.cycles ↔ (a.val, b.val, c.val) ∈ t.cycles

/-- A table presents at most one atom structure. -/
theorem Presents.unique {t : AtomTable} {A B : AtomStructure (Fin t.size)} (hA : t.Presents A)
    (hB : t.Presents B) : A = B := by
  have hconv : A.conv = B.conv := funext fun a =>
    Fin.ext (Option.some.inj ((hA.conv a).symm.trans (hB.conv a)))
  have hid : A.id = B.id := Set.ext fun a => (hA.id a).trans (hB.id a).symm
  have hcycles : A.cycles = B.cycles := Set.ext fun ⟨a, b, c⟩ =>
    (hA.cycles a b c).trans (hB.cycles a b c).symm
  cases A
  cases B
  congr

/-- The table presents an atom structure whose complex algebra is representable. This is the
representation problem for finite relation algebras as a predicate on tables; a table that
presents no atom structure is a no-instance. -/
@[expose] def IsRepresentable (t : AtomTable) : Prop :=
  ∃ A : AtomStructure (Fin t.size), t.Presents A ∧ Representable (ComplexAlgebra A)

/-- Every finite relation algebra is isomorphic to the complex algebra of an atom structure that
some table presents. By `RelationAlgebraEquiv.representable_iff` the algebra is representable if
and only if that complex algebra is, so tables cover the representation problem for finite
relation algebras. -/
theorem exists_presents_equiv (α : Type u) [RelationAlgebra α] [Finite α] :
    ∃ (t : AtomTable) (A : AtomStructure (Fin t.size)), t.Presents A ∧
      Nonempty (RelationAlgebraEquiv α (ComplexAlgebra A)) := by
  cases nonempty_fintype α
  let : CompleteAtomicRelationAlgebra α :=
    { ‹RelationAlgebra α›, Fintype.toCompleteAtomicBooleanAlgebra α with }
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin {a : α // IsAtom a}
  let A := (atomStructure α).map e
  refine ⟨⟨n, List.ofFn fun a => (A.conv a).val, A.id.toFinite.toFinset.toList.map Fin.val,
    A.cycles.toFinite.toFinset.toList.map fun c => (c.1.val, c.2.1.val, c.2.2.val)⟩, A,
    ⟨fun a => by simp, fun a => ?_, fun a b c => ?_⟩,
    ⟨complexAlgebraEquiv.trans (ComplexAlgebra.mapEquiv _ e)⟩⟩
  · simpa using ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, h⟩ => Fin.ext h ▸ hb⟩
  · simp only [List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset, Prod.exists,
      Prod.mk.injEq, Fin.val_inj]
    exact ⟨fun h => ⟨a, b, c, h, rfl, rfl, rfl⟩, by rintro ⟨_, _, _, h, rfl, rfl, rfl⟩; exact h⟩

end AtomTable

end RelationAlgebra

end Cslib
