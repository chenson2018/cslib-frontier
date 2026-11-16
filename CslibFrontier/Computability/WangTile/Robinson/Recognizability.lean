/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Tiles
import Mathlib.Tactic.FinCases

/-!
# Local recognition of corrected Robinson supertiles

A matching four-by-four neighborhood whose central southwest tile has thin phase `a`
has exactly one substitution parent. The one-cell boundary is essential: an isolated
matching two-by-two block need not have a parent.

## Main results

* `existsUnique_centerParent`: the central block of a `Neighborhood` has a unique parent.

## References

The four-by-four argument is the recognition step in [JeandelVanier2020], Proposition 8
(p. 24 of the authors' manuscript). We use the corrected 104-tile alphabet of the prior
formalization [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
the `Robinson.Closed104.LocalRecognizability` and `FiniteRecognizability` modules. Exact enumeration of
matching rows, including rejected candidates, proves completeness of the finite check.
-/

public section
namespace Cslib.WangTile.Robinson

/-- A matching four-by-four index patch with its central block in substitution phase. -/
structure Neighborhood where
  /-- Tile index at each position, increasing east and north. -/
  cell : Fin 4 → Fin 4 → Index
  /-- Every horizontal shared edge matches. -/
  horizontal : ∀ (i : Fin 3) (j : Fin 4),
    (tile (components (cell i.castSucc j))).right =
      (tile (components (cell i.succ j))).left
  /-- Every vertical shared edge matches. -/
  vertical : ∀ (i : Fin 4) (j : Fin 3),
    (tile (components (cell i j.castSucc))).top =
      (tile (components (cell i j.succ))).bottom
  /-- Thin phase at the southwest position of the central block. -/
  phase : (components (cell 1 1)).thin = .a

private def hFollowers : ℕ → List ℕ
  | 0 | 41 | 46 | 54 => [17, 22, 30]
  | 1 | 40 | 44 | 52 => [16, 20, 28]
  | 2 | 34 | 43 | 50 => [10, 19, 26]
  | 3 | 32 | 42 | 48 => [8, 18, 24]
  | 4 => [58, 64, 70, 76]
  | 5 => [56, 57, 62, 63, 68, 69, 74, 75]
  | 6 => [61, 67, 73, 79]
  | 7 => [59, 60, 65, 66, 71, 72, 77, 78]
  | 8 | 18 | 24 => [32, 42, 48, 83, 84, 89, 90, 95, 96, 101, 102]
  | 9 | 14 | 25 => [2, 33, 38, 49]
  | 10 | 19 | 26 => [34, 43, 50, 85, 91, 97, 103]
  | 11 | 15 | 27 => [3, 35, 39, 51]
  | 12 | 21 | 29 => [0, 36, 45, 53]
  | 13 | 23 | 31 => [1, 37, 47, 55]
  | 16 | 20 | 28 => [40, 44, 52, 80, 81, 86, 87, 92, 93, 98, 99]
  | 17 | 22 | 30 => [41, 46, 54, 82, 88, 94, 100]
  | 33 | 38 | 49 | 83 | 84 | 89 | 90 | 95 | 96 | 101 | 102 => [9, 14, 25]
  | 35 | 39 | 51 | 85 | 91 | 97 | 103 => [11, 15, 27]
  | 36 | 45 | 53 | 80 | 81 | 86 | 87 | 92 | 93 | 98 | 99 => [12, 21, 29]
  | 37 | 47 | 55 | 82 | 88 | 94 | 100 => [13, 23, 31]
  | 56 | 57 | 62 | 63 | 68 | 69 | 74 | 75 => [4]
  | 58 | 64 | 70 | 76 => [5]
  | 59 | 60 | 65 | 66 | 71 | 72 | 77 | 78 => [6]
  | 61 | 67 | 73 | 79 => [7]
  | _ => []

private def vFollowers : ℕ → List ℕ
  | 0 | 81 | 84 | 85 => [57, 60, 61]
  | 1 | 87 | 90 | 91 => [63, 66, 67]
  | 2 | 93 | 96 | 97 => [69, 72, 73]
  | 3 | 99 | 102 | 103 => [75, 78, 79]
  | 4 => [12, 13, 14, 15]
  | 5 => [16, 17, 18, 19]
  | 6 => [20, 21, 22, 23, 24, 25, 26, 27]
  | 7 => [8, 9, 10, 11, 28, 29, 30, 31]
  | 8 | 9 | 10 | 11 | 28 | 29 | 30 | 31 => [5]
  | 12 | 13 | 14 | 15 => [6]
  | 16 | 17 | 18 | 19 => [7]
  | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => [4]
  | 32 | 33 | 34 | 35 | 52 | 53 | 54 | 55 | 98 | 100 | 101 => [74, 76, 77]
  | 36 | 37 | 38 | 39 | 80 | 82 | 83 => [56, 58, 59]
  | 40 | 41 | 42 | 43 | 86 | 88 | 89 => [62, 64, 65]
  | 44 | 45 | 46 | 47 | 48 | 49 | 50 | 51 | 92 | 94 | 95 => [68, 70, 71]
  | 56 | 58 | 59 => [2, 80, 82, 83]
  | 57 | 60 | 61 => [36, 37, 38, 39, 81, 84, 85]
  | 62 | 64 | 65 => [3, 86, 88, 89]
  | 63 | 66 | 67 => [40, 41, 42, 43, 87, 90, 91]
  | 68 | 70 | 71 => [0, 92, 94, 95]
  | 69 | 72 | 73 => [44, 45, 46, 47, 48, 49, 50, 51, 93, 96, 97]
  | 74 | 76 | 77 => [1, 98, 100, 101]
  | 75 | 78 | 79 => [32, 33, 34, 35, 52, 53, 54, 55, 99, 102, 103]
  | _ => []

private def vPredecessors : ℕ → List ℕ
  | 0 | 92 | 94 | 95 => [68, 70, 71]
  | 1 | 98 | 100 | 101 => [74, 76, 77]
  | 2 | 80 | 82 | 83 => [56, 58, 59]
  | 3 | 86 | 88 | 89 => [62, 64, 65]
  | 4 => [20, 21, 22, 23, 24, 25, 26, 27]
  | 5 => [8, 9, 10, 11, 28, 29, 30, 31]
  | 6 => [12, 13, 14, 15]
  | 7 => [16, 17, 18, 19]
  | 8 | 9 | 10 | 11 | 28 | 29 | 30 | 31 => [7]
  | 12 | 13 | 14 | 15 => [4]
  | 16 | 17 | 18 | 19 => [5]
  | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => [6]
  | 32 | 33 | 34 | 35 | 52 | 53 | 54 | 55 | 99 | 102 | 103 => [75, 78, 79]
  | 36 | 37 | 38 | 39 | 81 | 84 | 85 => [57, 60, 61]
  | 40 | 41 | 42 | 43 | 87 | 90 | 91 => [63, 66, 67]
  | 44 | 45 | 46 | 47 | 48 | 49 | 50 | 51 | 93 | 96 | 97 => [69, 72, 73]
  | 56 | 58 | 59 => [36, 37, 38, 39, 80, 82, 83]
  | 57 | 60 | 61 => [0, 81, 84, 85]
  | 62 | 64 | 65 => [40, 41, 42, 43, 86, 88, 89]
  | 63 | 66 | 67 => [1, 87, 90, 91]
  | 68 | 70 | 71 => [44, 45, 46, 47, 48, 49, 50, 51, 92, 94, 95]
  | 69 | 72 | 73 => [2, 93, 96, 97]
  | 74 | 76 | 77 => [32, 33, 34, 35, 52, 53, 54, 55, 98, 100, 101]
  | 75 | 78 | 79 => [3, 99, 102, 103]
  | _ => []

private def phaseA (i : ℕ) : Bool :=
  i < 4 || (32 ≤ i && i < 56) || (80 ≤ i && i < 104)

private def rowCertificate (i : Index) : Prop :=
  hFollowers i.val = ((List.finRange 104).filter fun j =>
    decide ((tile (components i)).right = (tile (components j)).left)).map Fin.val ∧
  vFollowers i.val = ((List.finRange 104).filter fun j =>
    decide ((tile (components i)).top = (tile (components j)).bottom)).map Fin.val ∧
  vPredecessors i.val = ((List.finRange 104).filter fun j =>
    decide ((tile (components j)).top = (tile (components i)).bottom)).map Fin.val ∧
  phaseA i.val = decide ((components i).thin = .a)

private instance (i : Index) : Decidable (rowCertificate i) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem rowCertificate_0 : rowCertificate 0 := by decide
private theorem rowCertificate_1 : rowCertificate 1 := by decide
private theorem rowCertificate_2 : rowCertificate 2 := by decide
private theorem rowCertificate_3 : rowCertificate 3 := by decide
private theorem rowCertificate_4 : rowCertificate 4 := by decide
private theorem rowCertificate_5 : rowCertificate 5 := by decide
private theorem rowCertificate_6 : rowCertificate 6 := by decide
private theorem rowCertificate_7 : rowCertificate 7 := by decide
private theorem rowCertificate_8 : rowCertificate 8 := by decide
private theorem rowCertificate_9 : rowCertificate 9 := by decide
private theorem rowCertificate_10 : rowCertificate 10 := by decide
private theorem rowCertificate_11 : rowCertificate 11 := by decide
private theorem rowCertificate_12 : rowCertificate 12 := by decide
private theorem rowCertificate_13 : rowCertificate 13 := by decide
private theorem rowCertificate_14 : rowCertificate 14 := by decide
private theorem rowCertificate_15 : rowCertificate 15 := by decide
private theorem rowCertificate_16 : rowCertificate 16 := by decide
private theorem rowCertificate_17 : rowCertificate 17 := by decide
private theorem rowCertificate_18 : rowCertificate 18 := by decide
private theorem rowCertificate_19 : rowCertificate 19 := by decide
private theorem rowCertificate_20 : rowCertificate 20 := by decide
private theorem rowCertificate_21 : rowCertificate 21 := by decide
private theorem rowCertificate_22 : rowCertificate 22 := by decide
private theorem rowCertificate_23 : rowCertificate 23 := by decide
private theorem rowCertificate_24 : rowCertificate 24 := by decide
private theorem rowCertificate_25 : rowCertificate 25 := by decide
private theorem rowCertificate_26 : rowCertificate 26 := by decide
private theorem rowCertificate_27 : rowCertificate 27 := by decide
private theorem rowCertificate_28 : rowCertificate 28 := by decide
private theorem rowCertificate_29 : rowCertificate 29 := by decide
private theorem rowCertificate_30 : rowCertificate 30 := by decide
private theorem rowCertificate_31 : rowCertificate 31 := by decide
private theorem rowCertificate_32 : rowCertificate 32 := by decide
private theorem rowCertificate_33 : rowCertificate 33 := by decide
private theorem rowCertificate_34 : rowCertificate 34 := by decide
private theorem rowCertificate_35 : rowCertificate 35 := by decide
private theorem rowCertificate_36 : rowCertificate 36 := by decide
private theorem rowCertificate_37 : rowCertificate 37 := by decide
private theorem rowCertificate_38 : rowCertificate 38 := by decide
private theorem rowCertificate_39 : rowCertificate 39 := by decide
private theorem rowCertificate_40 : rowCertificate 40 := by decide
private theorem rowCertificate_41 : rowCertificate 41 := by decide
private theorem rowCertificate_42 : rowCertificate 42 := by decide
private theorem rowCertificate_43 : rowCertificate 43 := by decide
private theorem rowCertificate_44 : rowCertificate 44 := by decide
private theorem rowCertificate_45 : rowCertificate 45 := by decide
private theorem rowCertificate_46 : rowCertificate 46 := by decide
private theorem rowCertificate_47 : rowCertificate 47 := by decide
private theorem rowCertificate_48 : rowCertificate 48 := by decide
private theorem rowCertificate_49 : rowCertificate 49 := by decide
private theorem rowCertificate_50 : rowCertificate 50 := by decide
private theorem rowCertificate_51 : rowCertificate 51 := by decide
private theorem rowCertificate_52 : rowCertificate 52 := by decide
private theorem rowCertificate_53 : rowCertificate 53 := by decide
private theorem rowCertificate_54 : rowCertificate 54 := by decide
private theorem rowCertificate_55 : rowCertificate 55 := by decide
private theorem rowCertificate_56 : rowCertificate 56 := by decide
private theorem rowCertificate_57 : rowCertificate 57 := by decide
private theorem rowCertificate_58 : rowCertificate 58 := by decide
private theorem rowCertificate_59 : rowCertificate 59 := by decide
private theorem rowCertificate_60 : rowCertificate 60 := by decide
private theorem rowCertificate_61 : rowCertificate 61 := by decide
private theorem rowCertificate_62 : rowCertificate 62 := by decide
private theorem rowCertificate_63 : rowCertificate 63 := by decide
private theorem rowCertificate_64 : rowCertificate 64 := by decide
private theorem rowCertificate_65 : rowCertificate 65 := by decide
private theorem rowCertificate_66 : rowCertificate 66 := by decide
private theorem rowCertificate_67 : rowCertificate 67 := by decide
private theorem rowCertificate_68 : rowCertificate 68 := by decide
private theorem rowCertificate_69 : rowCertificate 69 := by decide
private theorem rowCertificate_70 : rowCertificate 70 := by decide
private theorem rowCertificate_71 : rowCertificate 71 := by decide
private theorem rowCertificate_72 : rowCertificate 72 := by decide
private theorem rowCertificate_73 : rowCertificate 73 := by decide
private theorem rowCertificate_74 : rowCertificate 74 := by decide
private theorem rowCertificate_75 : rowCertificate 75 := by decide
private theorem rowCertificate_76 : rowCertificate 76 := by decide
private theorem rowCertificate_77 : rowCertificate 77 := by decide
private theorem rowCertificate_78 : rowCertificate 78 := by decide
private theorem rowCertificate_79 : rowCertificate 79 := by decide
private theorem rowCertificate_80 : rowCertificate 80 := by decide
private theorem rowCertificate_81 : rowCertificate 81 := by decide
private theorem rowCertificate_82 : rowCertificate 82 := by decide
private theorem rowCertificate_83 : rowCertificate 83 := by decide
private theorem rowCertificate_84 : rowCertificate 84 := by decide
private theorem rowCertificate_85 : rowCertificate 85 := by decide
private theorem rowCertificate_86 : rowCertificate 86 := by decide
private theorem rowCertificate_87 : rowCertificate 87 := by decide
private theorem rowCertificate_88 : rowCertificate 88 := by decide
private theorem rowCertificate_89 : rowCertificate 89 := by decide
private theorem rowCertificate_90 : rowCertificate 90 := by decide
private theorem rowCertificate_91 : rowCertificate 91 := by decide
private theorem rowCertificate_92 : rowCertificate 92 := by decide
private theorem rowCertificate_93 : rowCertificate 93 := by decide
private theorem rowCertificate_94 : rowCertificate 94 := by decide
private theorem rowCertificate_95 : rowCertificate 95 := by decide
private theorem rowCertificate_96 : rowCertificate 96 := by decide
private theorem rowCertificate_97 : rowCertificate 97 := by decide
private theorem rowCertificate_98 : rowCertificate 98 := by decide
private theorem rowCertificate_99 : rowCertificate 99 := by decide
private theorem rowCertificate_100 : rowCertificate 100 := by decide
private theorem rowCertificate_101 : rowCertificate 101 := by decide
private theorem rowCertificate_102 : rowCertificate 102 := by decide
private theorem rowCertificate_103 : rowCertificate 103 := by decide

private theorem rowCertificate_all (i : Index) : rowCertificate i := by
  fin_cases i
  · exact rowCertificate_0
  · exact rowCertificate_1
  · exact rowCertificate_2
  · exact rowCertificate_3
  · exact rowCertificate_4
  · exact rowCertificate_5
  · exact rowCertificate_6
  · exact rowCertificate_7
  · exact rowCertificate_8
  · exact rowCertificate_9
  · exact rowCertificate_10
  · exact rowCertificate_11
  · exact rowCertificate_12
  · exact rowCertificate_13
  · exact rowCertificate_14
  · exact rowCertificate_15
  · exact rowCertificate_16
  · exact rowCertificate_17
  · exact rowCertificate_18
  · exact rowCertificate_19
  · exact rowCertificate_20
  · exact rowCertificate_21
  · exact rowCertificate_22
  · exact rowCertificate_23
  · exact rowCertificate_24
  · exact rowCertificate_25
  · exact rowCertificate_26
  · exact rowCertificate_27
  · exact rowCertificate_28
  · exact rowCertificate_29
  · exact rowCertificate_30
  · exact rowCertificate_31
  · exact rowCertificate_32
  · exact rowCertificate_33
  · exact rowCertificate_34
  · exact rowCertificate_35
  · exact rowCertificate_36
  · exact rowCertificate_37
  · exact rowCertificate_38
  · exact rowCertificate_39
  · exact rowCertificate_40
  · exact rowCertificate_41
  · exact rowCertificate_42
  · exact rowCertificate_43
  · exact rowCertificate_44
  · exact rowCertificate_45
  · exact rowCertificate_46
  · exact rowCertificate_47
  · exact rowCertificate_48
  · exact rowCertificate_49
  · exact rowCertificate_50
  · exact rowCertificate_51
  · exact rowCertificate_52
  · exact rowCertificate_53
  · exact rowCertificate_54
  · exact rowCertificate_55
  · exact rowCertificate_56
  · exact rowCertificate_57
  · exact rowCertificate_58
  · exact rowCertificate_59
  · exact rowCertificate_60
  · exact rowCertificate_61
  · exact rowCertificate_62
  · exact rowCertificate_63
  · exact rowCertificate_64
  · exact rowCertificate_65
  · exact rowCertificate_66
  · exact rowCertificate_67
  · exact rowCertificate_68
  · exact rowCertificate_69
  · exact rowCertificate_70
  · exact rowCertificate_71
  · exact rowCertificate_72
  · exact rowCertificate_73
  · exact rowCertificate_74
  · exact rowCertificate_75
  · exact rowCertificate_76
  · exact rowCertificate_77
  · exact rowCertificate_78
  · exact rowCertificate_79
  · exact rowCertificate_80
  · exact rowCertificate_81
  · exact rowCertificate_82
  · exact rowCertificate_83
  · exact rowCertificate_84
  · exact rowCertificate_85
  · exact rowCertificate_86
  · exact rowCertificate_87
  · exact rowCertificate_88
  · exact rowCertificate_89
  · exact rowCertificate_90
  · exact rowCertificate_91
  · exact rowCertificate_92
  · exact rowCertificate_93
  · exact rowCertificate_94
  · exact rowCertificate_95
  · exact rowCertificate_96
  · exact rowCertificate_97
  · exact rowCertificate_98
  · exact rowCertificate_99
  · exact rowCertificate_100
  · exact rowCertificate_101
  · exact rowCertificate_102
  · exact rowCertificate_103

private theorem mem_hFollowers (i j : Index) :
    j.val ∈ hFollowers i.val ↔
      (tile (components i)).right = (tile (components j)).left := by
  rw [(rowCertificate_all i).1]
  simp [Fin.val_inj]

private theorem mem_vFollowers (i j : Index) :
    j.val ∈ vFollowers i.val ↔
      (tile (components i)).top = (tile (components j)).bottom := by
  rw [(rowCertificate_all i).2.1]
  simp [Fin.val_inj]

private theorem mem_vPredecessors (i j : Index) :
    j.val ∈ vPredecessors i.val ↔
      (tile (components j)).top = (tile (components i)).bottom := by
  rw [(rowCertificate_all i).2.2.1]
  simp [Fin.val_inj]

/-- Internal row search record; integer indices keep its finite evaluator small. -/
private structure Row where
  x0 : ℕ
  x1 : ℕ
  x2 : ℕ
  x3 : ℕ
  deriving DecidableEq

private def rows (a : ℕ) : List Row :=
  (hFollowers a).flatMap fun b => (hFollowers b).flatMap fun c =>
    (hFollowers c).map fun d => ⟨a, b, c, d⟩

private def verticalRows (follow : ℕ → List ℕ) (r : Row) : List Row :=
  (follow r.x0).flatMap fun a =>
    ((hFollowers a).filter fun b => b ∈ follow r.x1).flatMap fun b =>
      ((hFollowers b).filter fun c => c ∈ follow r.x2).flatMap fun c =>
        ((hFollowers c).filter fun d => d ∈ follow r.x3).map fun d => ⟨a, b, c, d⟩

private def Row.horizontal (r : Row) : Prop :=
  r.x1 ∈ hFollowers r.x0 ∧ r.x2 ∈ hFollowers r.x1 ∧ r.x3 ∈ hFollowers r.x2

private def Row.vertical (follow : ℕ → List ℕ) (r u : Row) : Prop :=
  u.x0 ∈ follow r.x0 ∧ u.x1 ∈ follow r.x1 ∧
    u.x2 ∈ follow r.x2 ∧ u.x3 ∈ follow r.x3

private theorem mem_rows (r : Row) : r ∈ rows r.x0 ↔ r.horizontal := by
  rcases r with ⟨a, b, c, d⟩
  simp [rows, Row.horizontal, Row.mk.injEq]

private theorem mem_verticalRows (follow : ℕ → List ℕ) (r u : Row) :
    u ∈ verticalRows follow r ↔ u.horizontal ∧ r.vertical follow u := by
  rcases u with ⟨a, b, c, d⟩
  simp only [verticalRows, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
    List.mem_map, Row.mk.injEq, Row.horizontal, Row.vertical]
  constructor
  · rintro ⟨a', ha, b', ⟨hb, hb'⟩, c', ⟨hc, hc'⟩, d', ⟨hd, hd'⟩, heq⟩
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨⟨hb, hc, hd⟩, ha, hb', hc', hd'⟩
  · rintro ⟨⟨hb, hc, hd⟩, ha, hb', hc', hd'⟩
    exact ⟨a, ha, b, ⟨hb, hb'⟩, c, ⟨hc, hc'⟩, d, ⟨hd, hd'⟩, rfl, rfl, rfl, rfl⟩

private def pairs (a : ℕ) : List (Row × Row) :=
  ((rows a).filter fun r => phaseA r.x1).flatMap fun r =>
    (verticalRows vFollowers r).map fun u => (r, u)

private def extendable (r u : Row) : Bool :=
  !(verticalRows vPredecessors r).isEmpty && !(verticalRows vFollowers u).isEmpty

private def children (p : Index) : Row :=
  ⟨(childBlock p 0 0).val, (childBlock p 1 0).val,
    (childBlock p 0 1).val, (childBlock p 1 1).val⟩

private def center (r u : Row) : Row := ⟨r.x1, r.x2, u.x1, u.x2⟩

private def candidates (r u : Row) : List Index :=
  (List.finRange 104).filter fun i => decide (children i = center r u)

private def check (r u : Row) : Bool := !extendable r u || (candidates r u).length == 1

private def checkBucket (i : ℕ) : Bool := (pairs i).all fun (r, u) => check r u

private theorem bucket_0 : checkBucket 0 = true := by decide
private theorem bucket_1 : checkBucket 1 = true := by decide
private theorem bucket_2 : checkBucket 2 = true := by decide
private theorem bucket_3 : checkBucket 3 = true := by decide
private theorem bucket_4 : checkBucket 4 = true := by decide
private theorem bucket_5 : checkBucket 5 = true := by decide
private theorem bucket_6 : checkBucket 6 = true := by decide
private theorem bucket_7 : checkBucket 7 = true := by decide
private theorem bucket_8 : checkBucket 8 = true := by decide
private theorem bucket_9 : checkBucket 9 = true := by decide
private theorem bucket_10 : checkBucket 10 = true := by decide
private theorem bucket_11 : checkBucket 11 = true := by decide
private theorem bucket_12 : checkBucket 12 = true := by decide
private theorem bucket_13 : checkBucket 13 = true := by decide
private theorem bucket_14 : checkBucket 14 = true := by decide
private theorem bucket_15 : checkBucket 15 = true := by decide
private theorem bucket_16 : checkBucket 16 = true := by decide
private theorem bucket_17 : checkBucket 17 = true := by decide
private theorem bucket_18 : checkBucket 18 = true := by decide
private theorem bucket_19 : checkBucket 19 = true := by decide
private theorem bucket_20 : checkBucket 20 = true := by decide
private theorem bucket_21 : checkBucket 21 = true := by decide
private theorem bucket_22 : checkBucket 22 = true := by decide
private theorem bucket_23 : checkBucket 23 = true := by decide
private theorem bucket_24 : checkBucket 24 = true := by decide
private theorem bucket_25 : checkBucket 25 = true := by decide
private theorem bucket_26 : checkBucket 26 = true := by decide
private theorem bucket_27 : checkBucket 27 = true := by decide
private theorem bucket_28 : checkBucket 28 = true := by decide
private theorem bucket_29 : checkBucket 29 = true := by decide
private theorem bucket_30 : checkBucket 30 = true := by decide
private theorem bucket_31 : checkBucket 31 = true := by decide
private theorem bucket_32 : checkBucket 32 = true := by decide
private theorem bucket_33 : checkBucket 33 = true := by decide
private theorem bucket_34 : checkBucket 34 = true := by decide
private theorem bucket_35 : checkBucket 35 = true := by decide
private theorem bucket_36 : checkBucket 36 = true := by decide
private theorem bucket_37 : checkBucket 37 = true := by decide
private theorem bucket_38 : checkBucket 38 = true := by decide
private theorem bucket_39 : checkBucket 39 = true := by decide
private theorem bucket_40 : checkBucket 40 = true := by decide
private theorem bucket_41 : checkBucket 41 = true := by decide
private theorem bucket_42 : checkBucket 42 = true := by decide
private theorem bucket_43 : checkBucket 43 = true := by decide
private theorem bucket_44 : checkBucket 44 = true := by decide
private theorem bucket_45 : checkBucket 45 = true := by decide
private theorem bucket_46 : checkBucket 46 = true := by decide
private theorem bucket_47 : checkBucket 47 = true := by decide
private theorem bucket_48 : checkBucket 48 = true := by decide
private theorem bucket_49 : checkBucket 49 = true := by decide
private theorem bucket_50 : checkBucket 50 = true := by decide
private theorem bucket_51 : checkBucket 51 = true := by decide
private theorem bucket_52 : checkBucket 52 = true := by decide
private theorem bucket_53 : checkBucket 53 = true := by decide
private theorem bucket_54 : checkBucket 54 = true := by decide
private theorem bucket_55 : checkBucket 55 = true := by decide
private theorem bucket_56 : checkBucket 56 = true := by decide
private theorem bucket_57 : checkBucket 57 = true := by decide
private theorem bucket_58 : checkBucket 58 = true := by decide
private theorem bucket_59 : checkBucket 59 = true := by decide
private theorem bucket_60 : checkBucket 60 = true := by decide
private theorem bucket_61 : checkBucket 61 = true := by decide
private theorem bucket_62 : checkBucket 62 = true := by decide
private theorem bucket_63 : checkBucket 63 = true := by decide
private theorem bucket_64 : checkBucket 64 = true := by decide
private theorem bucket_65 : checkBucket 65 = true := by decide
private theorem bucket_66 : checkBucket 66 = true := by decide
private theorem bucket_67 : checkBucket 67 = true := by decide
private theorem bucket_68 : checkBucket 68 = true := by decide
private theorem bucket_69 : checkBucket 69 = true := by decide
private theorem bucket_70 : checkBucket 70 = true := by decide
private theorem bucket_71 : checkBucket 71 = true := by decide
private theorem bucket_72 : checkBucket 72 = true := by decide
private theorem bucket_73 : checkBucket 73 = true := by decide
private theorem bucket_74 : checkBucket 74 = true := by decide
private theorem bucket_75 : checkBucket 75 = true := by decide
private theorem bucket_76 : checkBucket 76 = true := by decide
private theorem bucket_77 : checkBucket 77 = true := by decide
private theorem bucket_78 : checkBucket 78 = true := by decide
private theorem bucket_79 : checkBucket 79 = true := by decide
private theorem bucket_80 : checkBucket 80 = true := by decide
private theorem bucket_81 : checkBucket 81 = true := by decide
private theorem bucket_82 : checkBucket 82 = true := by decide
private theorem bucket_83 : checkBucket 83 = true := by decide
private theorem bucket_84 : checkBucket 84 = true := by decide
private theorem bucket_85 : checkBucket 85 = true := by decide
private theorem bucket_86 : checkBucket 86 = true := by decide
private theorem bucket_87 : checkBucket 87 = true := by decide
private theorem bucket_88 : checkBucket 88 = true := by decide
private theorem bucket_89 : checkBucket 89 = true := by decide
private theorem bucket_90 : checkBucket 90 = true := by decide
private theorem bucket_91 : checkBucket 91 = true := by decide
private theorem bucket_92 : checkBucket 92 = true := by decide
private theorem bucket_93 : checkBucket 93 = true := by decide
private theorem bucket_94 : checkBucket 94 = true := by decide
private theorem bucket_95 : checkBucket 95 = true := by decide
private theorem bucket_96 : checkBucket 96 = true := by decide
private theorem bucket_97 : checkBucket 97 = true := by decide
private theorem bucket_98 : checkBucket 98 = true := by decide
private theorem bucket_99 : checkBucket 99 = true := by decide
private theorem bucket_100 : checkBucket 100 = true := by decide
private theorem bucket_101 : checkBucket 101 = true := by decide
private theorem bucket_102 : checkBucket 102 = true := by decide
private theorem bucket_103 : checkBucket 103 = true := by decide

private theorem all_buckets (i : Index) : checkBucket i.val = true := by
  fin_cases i
  · exact bucket_0
  · exact bucket_1
  · exact bucket_2
  · exact bucket_3
  · exact bucket_4
  · exact bucket_5
  · exact bucket_6
  · exact bucket_7
  · exact bucket_8
  · exact bucket_9
  · exact bucket_10
  · exact bucket_11
  · exact bucket_12
  · exact bucket_13
  · exact bucket_14
  · exact bucket_15
  · exact bucket_16
  · exact bucket_17
  · exact bucket_18
  · exact bucket_19
  · exact bucket_20
  · exact bucket_21
  · exact bucket_22
  · exact bucket_23
  · exact bucket_24
  · exact bucket_25
  · exact bucket_26
  · exact bucket_27
  · exact bucket_28
  · exact bucket_29
  · exact bucket_30
  · exact bucket_31
  · exact bucket_32
  · exact bucket_33
  · exact bucket_34
  · exact bucket_35
  · exact bucket_36
  · exact bucket_37
  · exact bucket_38
  · exact bucket_39
  · exact bucket_40
  · exact bucket_41
  · exact bucket_42
  · exact bucket_43
  · exact bucket_44
  · exact bucket_45
  · exact bucket_46
  · exact bucket_47
  · exact bucket_48
  · exact bucket_49
  · exact bucket_50
  · exact bucket_51
  · exact bucket_52
  · exact bucket_53
  · exact bucket_54
  · exact bucket_55
  · exact bucket_56
  · exact bucket_57
  · exact bucket_58
  · exact bucket_59
  · exact bucket_60
  · exact bucket_61
  · exact bucket_62
  · exact bucket_63
  · exact bucket_64
  · exact bucket_65
  · exact bucket_66
  · exact bucket_67
  · exact bucket_68
  · exact bucket_69
  · exact bucket_70
  · exact bucket_71
  · exact bucket_72
  · exact bucket_73
  · exact bucket_74
  · exact bucket_75
  · exact bucket_76
  · exact bucket_77
  · exact bucket_78
  · exact bucket_79
  · exact bucket_80
  · exact bucket_81
  · exact bucket_82
  · exact bucket_83
  · exact bucket_84
  · exact bucket_85
  · exact bucket_86
  · exact bucket_87
  · exact bucket_88
  · exact bucket_89
  · exact bucket_90
  · exact bucket_91
  · exact bucket_92
  · exact bucket_93
  · exact bucket_94
  · exact bucket_95
  · exact bucket_96
  · exact bucket_97
  · exact bucket_98
  · exact bucket_99
  · exact bucket_100
  · exact bucket_101
  · exact bucket_102
  · exact bucket_103

private theorem mem_pairs (r u : Row) (hr : r.horizontal)
    (hu : u.horizontal) (hv : r.vertical vFollowers u) (hphase : phaseA r.x1 = true) :
    (r, u) ∈ pairs r.x0 := by
  simp only [pairs, List.mem_flatMap, List.mem_filter, List.mem_map]
  exact ⟨r, ⟨(mem_rows r).mpr hr, hphase⟩, u,
    (mem_verticalRows vFollowers r u).mpr ⟨hu, hv⟩, rfl⟩

private theorem uniqueParent_spec (r u : Row) (hu : (candidates r u).length = 1) :
    ∃! p : Index, children p = center r u := by
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hu
  have hmem (q : Index) : q ∈ candidates r u ↔ children q = center r u := by
    simp [candidates]
  refine ⟨p, (hmem p).mp ?_, ?_⟩
  · rw [hp]; exact List.mem_singleton_self p
  · intro q hq
    have := (hmem q).mpr hq
    simpa only [hp, List.mem_singleton] using this

private theorem bucket_recognition (south r u north : Row)
    (hs : south.horizontal) (hr : r.horizontal) (hu : u.horizontal) (hn : north.horizontal)
    (hsr : r.vertical vPredecessors south) (hru : r.vertical vFollowers u)
    (hun : u.vertical vFollowers north) (ha : phaseA r.x1 = true)
    (hc : checkBucket r.x0 = true) :
    ∃! p : Index, children p = center r u := by
  have hsmem := (mem_verticalRows vPredecessors r south).mpr ⟨hs, hsr⟩
  have hnmem := (mem_verticalRows vFollowers u north).mpr ⟨hn, hun⟩
  have hex : extendable r u = true := by
    have h1 := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨south, hsmem⟩
    have h2 := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨north, hnmem⟩
    simp only [extendable, h1, h2, Bool.not_false, Bool.and_self]
  have hcheck := List.all_eq_true.mp hc (r, u) (mem_pairs r u hr hu hru ha)
  apply uniqueParent_spec r u
  simpa only [check, hex, Bool.not_true, Bool.false_or, beq_iff_eq] using hcheck

/-- The central two-by-two block has a unique substitution parent, with its one-cell context. -/
theorem existsUnique_centerParent (N : Neighborhood) :
    ∃! p : Index,
      childBlock p 0 0 = N.cell 1 1 ∧ childBlock p 1 0 = N.cell 2 1 ∧
      childBlock p 0 1 = N.cell 1 2 ∧ childBlock p 1 1 = N.cell 2 2 := by
  let row (j : Fin 4) : Row :=
    ⟨(N.cell 0 j).val, (N.cell 1 j).val, (N.cell 2 j).val, (N.cell 3 j).val⟩
  have hh (j : Fin 4) : (row j).horizontal :=
    ⟨(mem_hFollowers _ _).mpr (N.horizontal 0 j),
      (mem_hFollowers _ _).mpr (N.horizontal 1 j),
      (mem_hFollowers _ _).mpr (N.horizontal 2 j)⟩
  have hv (j : Fin 3) : (row j.castSucc).vertical vFollowers (row j.succ) :=
    ⟨(mem_vFollowers _ _).mpr (N.vertical 0 j),
      (mem_vFollowers _ _).mpr (N.vertical 1 j),
      (mem_vFollowers _ _).mpr (N.vertical 2 j),
      (mem_vFollowers _ _).mpr (N.vertical 3 j)⟩
  have hi : (row 1).vertical vPredecessors (row 0) :=
    ⟨(mem_vPredecessors _ _).mpr (N.vertical 0 0),
      (mem_vPredecessors _ _).mpr (N.vertical 1 0),
      (mem_vPredecessors _ _).mpr (N.vertical 2 0),
      (mem_vPredecessors _ _).mpr (N.vertical 3 0)⟩
  have ha : phaseA (row 1).x1 = true := by
    rw [(rowCertificate_all (N.cell 1 1)).2.2.2, N.phase]
    rfl
  have hb : checkBucket (row 1).x0 = true := all_buckets (N.cell 0 1)
  have h := bucket_recognition (row 0) (row 1) (row 2) (row 3)
    (hh 0) (hh 1) (hh 2) (hh 3) hi (hv 1) (hv 2) ha hb
  simpa only [children, center, row, Row.mk.injEq, Fin.val_inj] using h

end Cslib.WangTile.Robinson
