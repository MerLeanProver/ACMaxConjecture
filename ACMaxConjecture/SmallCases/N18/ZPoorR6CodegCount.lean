import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core

/-!
# Shared codegree double-count for the `n = 18` twin certificate

A single reusable finite double-counting identity used by both design halves of the `n = 18`
final core.  It counts the incidences

`(unordered pair {a, b} ⊆ S, common twin t ∈ Iso adjacent to both a and b)`

two ways: grouping by the pair `{a, b}` (LHS, the codegree `|N(a) ∩ N(b) ∩ Iso|`) and grouping by
the twin `t` (RHS, the `t ∈ Iso` with `|N(t) ∩ S| = k` contributing `C(k, 2)` pairs).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- The number of strictly-increasing ordered pairs drawn from a finset `A` is `C(|A|, 2)`. -/
theorem card_offDiag_filter_lt {α : Type*} [LinearOrder α] (A : Finset α) :
    (A.offDiag.filter (fun p => p.1 < p.2)).card = A.card.choose 2 := by
  classical
  have hswap : (A.offDiag.filter (fun p : α × α => ¬ p.1 < p.2)).card
      = (A.offDiag.filter (fun p : α × α => p.1 < p.2)).card := by
    rw [← Finset.card_image_of_injective (A.offDiag.filter (fun p : α × α => p.1 < p.2))
        Prod.swap_injective]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_offDiag, Prod.swap_prod_mk,
      Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, hlt⟩
      exact ⟨b, a, ⟨⟨hb, ha, fun h => hab h.symm⟩, lt_of_le_of_ne (not_lt.1 hlt) (fun h => hab h.symm)⟩,
        rfl, rfl⟩
    · rintro ⟨c, d, ⟨⟨hc, hd, hcd⟩, hlt⟩, rfl, rfl⟩
      exact ⟨⟨hd, hc, fun h => hcd h.symm⟩, not_lt.2 hlt.le⟩
  have hpart := Finset.card_filter_add_card_filter_not (s := A.offDiag)
    (p := fun p : α × α => p.1 < p.2)
  rw [hswap, Finset.offDiag_card] at hpart
  have hmp : A.card * (A.card - 1) = A.card * A.card - A.card := Nat.mul_pred A.card A.card
  rw [Nat.choose_two_right]
  omega

/-- **Codegree double-count.**  Summing the codegrees `|N(a) ∩ N(b) ∩ Iso|` over strictly-ordered
pairs `{a, b} ⊆ S` equals `∑_{t ∈ Iso} C(|N(t) ∩ S|, 2)`. -/
theorem codeg_pair_sum_eq_twin_choose2 (G : SimpleGraph (Fin 18)) (Iso S : Finset (Fin 18)) :
    ∑ p ∈ S.offDiag.filter (fun p => p.1 < p.2),
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
      = ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card).choose 2 := by
  classical
  set r : Fin 18 × Fin 18 → Fin 18 → Prop := fun p tt => G.Adj p.1 tt ∧ G.Adj p.2 tt with hr
  have hLHS : ∀ p : Fin 18 × Fin 18,
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
        = (Finset.bipartiteAbove r Iso p).card := by
    intro p
    congr 1
    ext tt
    simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset, hr]
    tauto
  have hRHS : ∀ t : Fin 18,
      (Finset.bipartiteBelow r (S.offDiag.filter (fun p => p.1 < p.2)) t).card
        = ((G.neighborFinset t ∩ S).card).choose 2 := by
    intro t
    rw [← card_offDiag_filter_lt (G.neighborFinset t ∩ S)]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset, hr]
    constructor
    · rintro ⟨⟨⟨ha, hb, hab⟩, hlt⟩, hta, htb⟩
      exact ⟨⟨⟨G.adj_symm hta, ha⟩, ⟨G.adj_symm htb, hb⟩, hab⟩, hlt⟩
    · rintro ⟨⟨⟨hta, ha⟩, ⟨htb, hb⟩, hab⟩, hlt⟩
      exact ⟨⟨⟨ha, hb, hab⟩, hlt⟩, G.adj_symm hta, G.adj_symm htb⟩
  simp_rw [hLHS]
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r]
  simp_rw [hRHS]

end N18

end ACMax
