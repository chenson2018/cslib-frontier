/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Undecidable

/-! # The step from the domino problem to representability: the form of the conclusion

The conclusion of `not_computablePred_isRepresentable_of_not_computablePred_tilesPlane` is the
statement proposed for Theorem 8 of Hirsch and Hodkinson in cslib-frontier issue #5920, with the
predicate on tables written out. -/

@[expose] public section

namespace Cslib.Tests.RelationAlgebraUndecidable

open Cslib Cslib.RelationAlgebra Cslib.WangTile

/-- With the undecidability of the domino problem as a hypothesis, the step gives the statement
of the issue as it is written there. -/
example (h : ¬ComputablePred TilesPlane) :
    ¬ComputablePred fun t : AtomTable =>
      ∃ A : AtomStructure (Fin t.size), t.Presents A ∧ Representable (ComplexAlgebra A) :=
  not_computablePred_isRepresentable_of_not_computablePred_tilesPlane h

end Cslib.Tests.RelationAlgebraUndecidable
