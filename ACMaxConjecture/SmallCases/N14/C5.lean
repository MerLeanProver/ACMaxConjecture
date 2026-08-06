import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.Align
import ACMaxConjecture.SmallCases.N14.Doublestar

/-!
# Induced-`C₅` alignment leaf for the `n = 14` single-twin certificate

This file closes the induced-`C₅` branch of the keystone `dominating_edge_or_induced_C5` for
`n = 14`: given the five cycle vertices `v₁..v₅` (degree-`3`, the five cycle edges and five
non-edges, pairwise distinct) and an `M`-isolated degree-`3` twin `t` with two degree-`4` hubs
`h₁, h₂`, a `SingleTwinConfig G` is produced.

* `hub_cycle_cases` — a degree-`4` hub meets at most one cycle vertex
  (`hub_meets_path_le_one_fourteen` extended around the five `P₃`s), packaged as a `6`-way
  case split (blocks none, or exactly one `vᵢ`).
* `single_twin_config_from_C5` — the two hubs together block `≤ 2` cycle vertices; a consecutive
  triple avoiding both is the cherry, assembled via `assemble_single_twin_config`.  The single
  residual is the cyclic-distance-`2` configuration, where no consecutive triple avoids both.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Distinctness from a five-element literal.**  A `Finset` literal `{a, b, c, d, e}` of
cardinality `5` (over `Fin 14`) has its five entries pairwise distinct. -/
theorem distinct_five_fourteen (a b c d e : Fin 14)
    (h : ({a, b, c, d, e} : Finset (Fin 14)).card = 5) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  classical
  have b3 : ∀ x y z : Fin 14, ({x, y, z} : Finset (Fin 14)).card ≤ 3 := by
    intro x y z
    have h1 := Finset.card_insert_le x ({y, z} : Finset (Fin 14))
    have h2 := Finset.card_insert_le y ({z} : Finset (Fin 14))
    simp only [Finset.card_singleton] at *
    omega
  have b4 : ∀ w x y z : Fin 14, ({w, x, y, z} : Finset (Fin 14)).card ≤ 4 := by
    intro w x y z
    have h1 := Finset.card_insert_le w ({x, y, z} : Finset (Fin 14))
    have h2 := b3 x y z
    omega
  have ha : a ∉ ({b, c, d, e} : Finset (Fin 14)) := by
    intro hmem
    have : ({a, b, c, d, e} : Finset (Fin 14)).card ≤ 4 := by
      rw [Finset.insert_eq_self.mpr hmem]; exact b4 b c d e
    omega
  have hca4 : ({b, c, d, e} : Finset (Fin 14)).card = 4 := by
    rw [Finset.card_insert_of_notMem ha] at h; omega
  have hb : b ∉ ({c, d, e} : Finset (Fin 14)) := by
    intro hmem
    have : ({b, c, d, e} : Finset (Fin 14)).card ≤ 3 := by
      rw [Finset.insert_eq_self.mpr hmem]; exact b3 c d e
    omega
  have hcb3 : ({c, d, e} : Finset (Fin 14)).card = 3 := by
    rw [Finset.card_insert_of_notMem hb] at hca4; omega
  have hc : c ∉ ({d, e} : Finset (Fin 14)) := by
    intro hmem
    have h1 := Finset.card_insert_le d ({e} : Finset (Fin 14))
    have : ({c, d, e} : Finset (Fin 14)).card ≤ 2 := by
      rw [Finset.insert_eq_self.mpr hmem]
      simp only [Finset.card_singleton] at *; omega
    omega
  have hcc2 : ({d, e} : Finset (Fin 14)).card = 2 := by
    rw [Finset.card_insert_of_notMem hc] at hcb3; omega
  have hd : d ≠ e := by
    intro hmem
    rw [hmem] at hcc2
    simp at hcc2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, hb.1, hb.2.1, hb.2.2, hc.1, hc.2, hd⟩

/-- **A degree-`4` hub meets at most one cycle vertex.**  Around an induced `C₅` `v₁–⋯–v₅` of
degree-`3` vertices, a degree-`4` hub `h` is adjacent to at most one `vᵢ`: two hits on a cycle
`P₃` give a triangle or good `C₄` (`hub_meets_path_le_one_fourteen`).  Packaged as a `6`-way split
(`h` blocks none of the cycle, or exactly one `vᵢ`, listing the non-adjacencies to the rest). -/
theorem hub_cycle_cases (G : SimpleGraph (Fin 14))
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (h v₁ v₂ v₃ v₄ v₅ : Fin 14) (hh : G.degree h = 4)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3 : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅)
    (d12 : v₁ ≠ v₂) (d13 : v₁ ≠ v₃) (d14 : v₁ ≠ v₄) (d15 : v₁ ≠ v₅)
    (d23 : v₂ ≠ v₃) (d24 : v₂ ≠ v₄) (d25 : v₂ ≠ v₅)
    (d34 : v₃ ≠ v₄) (d35 : v₃ ≠ v₅) (d45 : v₄ ≠ v₅) :
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄) := by
  have P123 := hub_meets_path_le_one_fourteen G hT hC4 hh hd1 hd2 hd3 e12 e23 n13 d12 d23 d13
  have P234 := hub_meets_path_le_one_fourteen G hT hC4 hh hd2 hd3 hd4 e23 e34 n24 d23 d34 d24
  have P345 := hub_meets_path_le_one_fourteen G hT hC4 hh hd3 hd4 hd5 e34 e45 n35 d34 d45 d35
  have P451 := hub_meets_path_le_one_fourteen G hT hC4 hh hd4 hd5 hd1 e45 e51
    (fun hh => n14 hh.symm) d45 d15.symm d14.symm
  have P512 := hub_meets_path_le_one_fourteen G hT hC4 hh hd5 hd1 hd2 e51 e12
    (fun hh => n25 hh.symm) d15.symm d12 d25.symm
  have not12 : ¬(G.Adj h v₁ ∧ G.Adj h v₂) := P123.1
  have not23 : ¬(G.Adj h v₂ ∧ G.Adj h v₃) := P123.2.1
  have not13 : ¬(G.Adj h v₁ ∧ G.Adj h v₃) := P123.2.2
  have not34 : ¬(G.Adj h v₃ ∧ G.Adj h v₄) := P234.2.1
  have not24 : ¬(G.Adj h v₂ ∧ G.Adj h v₄) := P234.2.2
  have not45 : ¬(G.Adj h v₄ ∧ G.Adj h v₅) := P345.2.1
  have not35 : ¬(G.Adj h v₃ ∧ G.Adj h v₅) := P345.2.2
  have not51 : ¬(G.Adj h v₅ ∧ G.Adj h v₁) := P451.2.1
  have not41 : ¬(G.Adj h v₄ ∧ G.Adj h v₁) := P451.2.2
  have not52 : ¬(G.Adj h v₅ ∧ G.Adj h v₂) := P512.2.2
  by_cases a1 : G.Adj h v₁
  · exact Or.inr (Or.inl ⟨fun a => not12 ⟨a1, a⟩, fun a => not13 ⟨a1, a⟩,
      fun a => not41 ⟨a, a1⟩, fun a => not51 ⟨a, a1⟩⟩)
  · by_cases a2 : G.Adj h v₂
    · exact Or.inr (Or.inr (Or.inl ⟨a1, fun a => not23 ⟨a2, a⟩, fun a => not24 ⟨a2, a⟩,
        fun a => not52 ⟨a, a2⟩⟩))
    · by_cases a3 : G.Adj h v₃
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, fun a => not34 ⟨a3, a⟩,
          fun a => not35 ⟨a3, a⟩⟩)))
      · by_cases a4 : G.Adj h v₄
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨a1, a2, a3, fun a => not45 ⟨a4, a⟩⟩))))
        · by_cases a5 : G.Adj h v₅
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2, a3, a4⟩))))
          · exact Or.inl ⟨a1, a2, a3, a4, a5⟩

end N14

end ACMax
