import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect

/-!
# The off-diagonal cover inequality for the `n = 18` tight two-hub `e(M) = 1` profiles

This file is the `n = 18` port of `TwinCert17TwoHubTight96`.  It supplies the **sharp off-diagonal
cover inequality** `cover_offDiag_ineq` used to bound the iso-rich degree-`4` hub set `S` in the
tight `e(M) = 1` two-hub residual profiles `(8, 8, 34)`, `(9, 7, 37)`, `(10, 6, 40)` (closed, modulo
one residual `sorry`, in `TwinCert18TwoHubTight`).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Off-diagonal cover inequality.**  If every ordered distinct pair from `S` is either adjacent or
shares a common neighbour in `Iso` (`hcov`), then the off-diagonal of `S` embeds into the union of
the adjacency pairs and the twin neighbourhood off-diagonals, yielding the counting bound. -/
theorem cover_offDiag_ineq (G : SimpleGraph (Fin 18)) (Iso S : Finset (Fin 18))
    (hcov : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b ∨
      (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).Nonempty) :
    S.card * S.card ≤ S.card + (∑ a ∈ S, (G.neighborFinset a ∩ S).card)
      + ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card) := by
  classical
  set A : Finset (Fin 18 × Fin 18) :=
    S.biUnion (fun a => {a} ×ˢ (G.neighborFinset a ∩ S)) with hAdef
  set B : Finset (Fin 18 × Fin 18) :=
    Iso.biUnion (fun t => (G.neighborFinset t ∩ S).offDiag) with hBdef
  have hsub : S.offDiag ⊆ A ∪ B := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨ha, hb, hne⟩ := hp
    rcases hcov p.1 ha p.2 hb hne with hadj | hsh
    · apply Finset.mem_union_left
      rw [hAdef, Finset.mem_biUnion]
      refine ⟨p.1, ha, ?_⟩
      rw [Finset.mem_product, Finset.mem_singleton]
      refine ⟨rfl, ?_⟩
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj, hb⟩
    · apply Finset.mem_union_right
      obtain ⟨t, ht⟩ := hsh
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
      obtain ⟨⟨hta, htb⟩, htIso⟩ := ht
      rw [hBdef, Finset.mem_biUnion]
      refine ⟨t, htIso, ?_⟩
      rw [Finset.mem_offDiag]
      refine ⟨?_, ?_, hne⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hta.symm, ha⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨htb.symm, hb⟩
  have hcardle : S.offDiag.card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)
  have hAcard : A.card ≤ ∑ a ∈ S, (G.neighborFinset a ∩ S).card := by
    refine le_trans Finset.card_biUnion_le ?_
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.card_product, Finset.card_singleton, one_mul]
  have hBcard : B.card ≤ ∑ t ∈ Iso, (G.neighborFinset t ∩ S).offDiag.card :=
    Finset.card_biUnion_le
  have htwin : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).offDiag.card
      = (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card := fun t _ => Finset.offDiag_card _
  rw [Finset.sum_congr rfl htwin] at hBcard
  have hoff : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card _
  rw [hoff] at hcardle
  omega

end N18

end ACMax
