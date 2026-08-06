import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.ZPoorR6CodegCount

/-!
# Shared design-B counting infrastructure for the `r = 6`, `S = 14` core (`n = 18`)

This file hoists the design-`B` counting engine shared by the iso-degree subcases
`s = isoDeg d₁ + isoDeg d₂ ∈ {2, 3, 4}`:

* `card_offDiag_filter_adj_eq_two_mul_S14` — the ordered adjacent off-diagonal count is twice the
  strictly-ordered one;
* `within_sum_eq_two_mul_S14` — the within-`S` handshake `∑_{r ∈ S} |N(r) ∩ S| = 2 · #ord-edges(S)`;
* `designB_rich4_edge_eq_S14` — the codegree engine: for a `4`-set of iso-degree-`2` hubs,
  `#ord-edges + ∑_t C(|N(t) ∩ Rich|, 2) = 6`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- The number of ordered adjacent pairs in `s` is twice the strictly-ordered count. -/
theorem card_offDiag_filter_adj_eq_two_mul_S14 (G : SimpleGraph (Fin 18)) (s : Finset (Fin 18)) :
    (s.offDiag.filter (fun p => G.Adj p.1 p.2)).card
      = 2 * (s.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card := by
  classical
  have hswap : (s.offDiag.filter (fun p : Fin 18 × Fin 18 => ¬ p.1 < p.2 ∧ G.Adj p.1 p.2)).card
      = (s.offDiag.filter (fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2)).card := by
    rw [← Finset.card_image_of_injective
        (s.offDiag.filter (fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2))
        Prod.swap_injective]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_offDiag, Prod.swap_prod_mk,
      Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, hlt, hadj⟩
      exact ⟨b, a, ⟨⟨hb, ha, fun h => hab h.symm⟩,
        lt_of_le_of_ne (not_lt.1 hlt) (fun h => hab h.symm), G.adj_symm hadj⟩, rfl, rfl⟩
    · rintro ⟨c, d, ⟨⟨hc, hd, hcd⟩, hlt, hadj⟩, rfl, rfl⟩
      exact ⟨⟨hd, hc, fun h => hcd h.symm⟩, not_lt.2 hlt.le, G.adj_symm hadj⟩
  have hadjfilt : s.offDiag.filter (fun p => G.Adj p.1 p.2)
      = s.offDiag.filter (fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2)
        ∪ s.offDiag.filter (fun p : Fin 18 × Fin 18 => ¬ p.1 < p.2 ∧ G.Adj p.1 p.2) := by
    ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  have hdisj : Disjoint
      (s.offDiag.filter (fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2))
      (s.offDiag.filter (fun p : Fin 18 × Fin 18 => ¬ p.1 < p.2 ∧ G.Adj p.1 p.2)) := by
    rw [Finset.disjoint_left]; rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_filter] at h1 h2; exact h2.2.1 h1.2.1
  rw [hadjfilt, Finset.card_union_of_disjoint hdisj, hswap]; ring

/-- **Handshake:** the within-`S` degree sum counts ordered adjacent pairs, i.e. twice the
strictly-ordered ones. -/
theorem within_sum_eq_two_mul_S14 (G : SimpleGraph (Fin 18)) (S : Finset (Fin 18)) :
    ∑ r ∈ S, (G.neighborFinset r ∩ S).card
      = 2 * (S.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card := by
  classical
  have hH1 : ∑ r ∈ S, (G.neighborFinset r ∩ S).card
      = (S.offDiag.filter (fun p => G.Adj p.1 p.2)).card := by
    have hoff : S.offDiag.filter (fun p => G.Adj p.1 p.2)
        = (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
      constructor
      · rintro ⟨⟨h1, h2, _⟩, hadj⟩; exact ⟨⟨h1, h2⟩, hadj⟩
      · rintro ⟨⟨h1, h2⟩, hadj⟩; exact ⟨⟨h1, h2, hadj.ne⟩, hadj⟩
    rw [hoff, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have heq : G.neighborFinset r ∩ S = S.filter (fun y => G.Adj r y) := by
      ext b; simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]; tauto
    rw [heq, Finset.card_filter]
  rw [hH1, card_offDiag_filter_adj_eq_two_mul_S14]

/-- **Design B rich-`4` edge equation.**  Let `Rich` be a `4`-element set of iso-degree-`2` hubs.
The codegree double-count makes the number of non-adjacent (hence co-occurring) `Rich`-pairs equal to
`∑_t C(|N(t) ∩ Rich|, 2)`; together with the `6` strictly-ordered pairs this gives
`#ordered-edges + ∑_t C(|N(t) ∩ Rich|, 2) = 6`.  The caller bounds the codegree sum to bound the
edge count. -/
theorem designB_rich4_edge_eq_S14 (G : SimpleGraph (Fin 18)) (Hub Iso Rich : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hcherry : ¬∃ t ∈ Iso, ∃ a b : Fin 18, a ∈ G.neighborFinset t ∧ b ∈ G.neighborFinset t ∧
      a ≠ b ∧ G.Adj a b)
    (hRichsub : Rich ⊆ Hub) (hRichcard : Rich.card = 4)
    (hRich2 : ∀ r ∈ Rich, (G.neighborFinset r ∩ Iso).card = 2) :
    (Rich.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card
      + ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich).card).choose 2 = 6 := by
  classical
  -- The rich-pair dichotomy: codegree is `0` on edges, `1` on non-edges.
  have hdich : ∀ p ∈ Rich.offDiag.filter (fun p => p.1 < p.2),
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
        = if G.Adj p.1 p.2 then 0 else 1 := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨hp1, hp2, hp12⟩, _hlt⟩ := hp
    have hp1Hub : p.1 ∈ Hub := hRichsub hp1
    have hp2Hub : p.2 ∈ Hub := hRichsub hp2
    by_cases hadj : G.Adj p.1 p.2
    · rw [if_pos hadj, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro t ht
      rw [Finset.mem_inter, Finset.mem_inter] at ht
      obtain ⟨⟨ht1, ht2⟩, htIso⟩ := ht
      exact hcherry ⟨t, htIso, p.1, p.2,
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ht1).symm,
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ht2).symm, hp12, hadj⟩
    · rw [if_neg hadj]
      have hle1 := hshare p.1 hp1Hub (hdeg4 p.1 hp1Hub) p.2 hp2Hub (hdeg4 p.2 hp2Hub) hp12 hadj
      rcases Nat.lt_or_ge (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card 1 with h0 | h1
      · exfalso
        have hcard0 : (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card = 0 := by omega
        apply hno2hub
        have heqA : (G.neighborFinset p.1 ∩ Iso) ∩ G.neighborFinset p.2
            = G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso := by
          ext x; simp only [Finset.mem_inter]; tauto
        have heqB : (G.neighborFinset p.2 ∩ Iso) ∩ G.neighborFinset p.1
            = G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso := by
          ext x; simp only [Finset.mem_inter]; tauto
        refine ⟨p.1, p.2, hp1Hub, hp2Hub, hdeg4 p.1 hp1Hub, hdeg4 p.2 hp2Hub, hp12, hadj, ?_, ?_⟩
        · have hh := Finset.card_inter_add_card_sdiff (G.neighborFinset p.1 ∩ Iso)
            (G.neighborFinset p.2)
          rw [heqA, hcard0, hRich2 p.1 hp1] at hh; omega
        · have hh := Finset.card_inter_add_card_sdiff (G.neighborFinset p.2 ∩ Iso)
            (G.neighborFinset p.1)
          rw [heqB, hcard0, hRich2 p.2 hp2] at hh; omega
      · omega
  -- The codegree sum equals the count of non-adjacent (strictly-ordered) `Rich`-pairs.
  have hcodegsum : ∑ p ∈ Rich.offDiag.filter (fun p => p.1 < p.2),
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
      = ((Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => ¬G.Adj p.1 p.2)).card := by
    have hstep : ∑ p ∈ Rich.offDiag.filter (fun p => p.1 < p.2),
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
        = ∑ p ∈ Rich.offDiag.filter (fun p => p.1 < p.2),
            (if G.Adj p.1 p.2 then 0 else 1) := Finset.sum_congr rfl hdich
    rw [hstep, Finset.card_filter]
    exact Finset.sum_congr rfl (fun p _ => by by_cases h : G.Adj p.1 p.2 <;> simp [h])
  have hLtcard : (Rich.offDiag.filter (fun p => p.1 < p.2)).card = 6 := by
    rw [card_offDiag_filter_lt, hRichcard]; decide
  have hnonadj_eq :
      ((Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => ¬G.Adj p.1 p.2)).card
        = ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich).card).choose 2 := by
    rw [← hcodegsum, codeg_pair_sum_eq_twin_choose2 G Iso Rich]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Rich.offDiag.filter (fun p => p.1 < p.2)) (p := fun p => G.Adj p.1 p.2)
  have hfilteq : (Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => G.Adj p.1 p.2)
      = Rich.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2) := Finset.filter_filter _ _ _
  rw [hfilteq] at hpartition
  omega

end N18

end ACMax
