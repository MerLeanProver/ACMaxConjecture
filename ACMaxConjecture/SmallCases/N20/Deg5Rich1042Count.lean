import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5RichCap

/-! # The rich-count dichotomy for the (10,8,42) corner (`n = 20`)

The `(|Hub|, |Iso|, Σ_Hub deg) = (10, 8, 42)` deg-5 corner has eight degree-`4` hubs and two
degree-`5` anchors, with the iso-degree ledger `Σ_Hub isoDeg = 3·|Iso| = 24`.  Around a rich
degree-`4` hub `g` (`isoDeg g ≥ 3`), the iso-cap `isoDeg_le_two_of_nonadj_rich_twenty` bounds
every non-`g`-adjacent degree-`4` hub by `2`, so writing `R` for the set of degree-`4` hubs of
iso-degree `≥ 2` and `Z₀` for the degree-`4` hubs missing `Iso` entirely, the zero-corrected
ledger yields the master inequality `|Z₀| + Σ_{D₄} isoDeg ≤ |R| + 10`.  Since
`Σ_{D₄} isoDeg = 24 − a ≥ 14` (`a ≤ 10` the total anchor iso-degree), the corner splits three
ways: `|R| ≥ 6` (contradicting the blocked world's `|R| ≤ 5` from
`rich_le_five_blocked_1042_twenty`), or `|R| = 5` with the combined bound
`Σ_R isoDeg + Σ_R |N r ∩ R| ≤ 13` (killed by `rich_doublecount_kill_1042_twenty`), or the
anchor-saturated residual: `|R| ∈ {4, 5}`, some degree-`5` anchor has all five neighbours in
`Iso` (`a ≥ 9`), the master inequality, and the failed combined bound at `|R| = 5`. -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The `(10, 8, 42)` two-anchor rich-count dichotomy.**  With `R` the degree-`4` hubs of
iso-degree `≥ 2`: either `6 ≤ |R|`, or `|R| = 5` together with the combined double-count bound
`Σ_R isoDeg + Σ_R |N r ∩ R| ≤ 13`, or the anchor-saturated payload — `|R| ∈ {4, 5}`, an
iso-saturated degree-`5` anchor, `Σ_{D₄} isoDeg ≤ 15` (total anchor iso-degree `≥ 9`), the
master inequality `|Z₀| + Σ_{D₄} isoDeg ≤ |R| + 10` (`Z₀` the degree-`4` hubs with no `Iso`
neighbour), and `|R| = 5 → 14 ≤` the combined count. -/
theorem rich_count_1042_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 8) (hdsum : ∑ w ∈ Hub, G.degree w = 42)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    6 ≤ (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ∨
      ((Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 ∧
        (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
            (G.neighborFinset r ∩ Iso).card)
          + (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
              (G.neighborFinset r
                ∩ Hub.filter (fun h => G.degree h = 4
                  ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 13) ∨
      (((Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 4 ∨
          (Hub.filter (fun h => G.degree h = 4
            ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5) ∧
        (∃ f ∈ Hub, G.degree f = 5 ∧ (G.neighborFinset f ∩ Iso).card = 5) ∧
        (∑ h ∈ Hub.filter (fun h => G.degree h = 4), (G.neighborFinset h ∩ Iso).card) ≤ 15 ∧
        (Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 0)).card
            + (∑ h ∈ Hub.filter (fun h => G.degree h = 4), (G.neighborFinset h ∩ Iso).card)
          ≤ (Hub.filter (fun h => G.degree h = 4
              ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card + 10 ∧
        ((Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 →
          14 ≤ (∑ r ∈ Hub.filter (fun h => G.degree h = 4
                  ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card), (G.neighborFinset r ∩ Iso).card)
            + (∑ r ∈ Hub.filter (fun h => G.degree h = 4
                  ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
                (G.neighborFinset r
                  ∩ Hub.filter (fun h => G.degree h = 4
                    ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card))) := by
  classical
  -- === Degree partition: 8 deg-4 hubs, 2 deg-5 anchors. ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  set D4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
  have hD4sub : D4 ⊆ Hub := by rw [hD4def]; exact Finset.filter_subset _ _
  have hD5sub : D5 ⊆ Hub := by rw [hD5def]; exact Finset.filter_subset _ _
  have hD4deg4 : ∀ h ∈ D4, G.degree h = 4 := by
    intro h hh; rw [hD4def, Finset.mem_filter] at hh; exact hh.2
  have hD5deg5 : ∀ h ∈ D5, G.degree h = 5 := by
    intro h hh; rw [hD5def, Finset.mem_filter] at hh
    rcases hdeg45 h hh.1 with h4 | h5
    · exact absurd h4 hh.2
    · exact h5
  have hcardpart : D4.card + D5.card = 10 := by
    rw [hD4def, hD5def, Finset.card_filter_add_card_filter_not]; exact hHub
  have hsumdeg : (∑ h ∈ D4, G.degree h) + (∑ h ∈ D5, G.degree h) = 42 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hdsum
  have hsum4 : (∑ h ∈ D4, G.degree h) = 4 * D4.card := by
    calc (∑ h ∈ D4, G.degree h) = ∑ _h ∈ D4, 4 :=
          Finset.sum_congr rfl fun h hh => hD4deg4 h hh
      _ = 4 * D4.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum5 : (∑ h ∈ D5, G.degree h) = 5 * D5.card := by
    calc (∑ h ∈ D5, G.degree h) = ∑ _h ∈ D5, 5 :=
          Finset.sum_congr rfl fun h hh => hD5deg5 h hh
      _ = 5 * D5.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hsum4, hsum5] at hsumdeg
  have hD4card : D4.card = 8 := by omega
  have hD5card : D5.card = 2 := by omega
  -- === Iso-degree ledger: `Σ_Hub isoDeg = 24`, split into the two degree classes. ===
  have hisosum24 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 24 := by
    have h := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at h; omega
  have hisosplit : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 24 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hisosum24
  -- === The two anchors and their iso caps. ===
  obtain ⟨f₁, f₂, hf12, hD5pair⟩ := Finset.card_eq_two.mp hD5card
  have hf₁D5 : f₁ ∈ D5 := by rw [hD5pair]; exact Finset.mem_insert_self f₁ {f₂}
  have hf₂D5 : f₂ ∈ D5 := by
    rw [hD5pair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₂)
  have hD5sumpair : (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset f₁ ∩ Iso).card + (G.neighborFinset f₂ ∩ Iso).card := by
    rw [hD5pair, Finset.sum_pair hf12]
  have hf1cap : (G.neighborFinset f₁ ∩ Iso).card ≤ 5 := by
    calc (G.neighborFinset f₁ ∩ Iso).card ≤ (G.neighborFinset f₁).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree f₁ := G.card_neighborFinset_eq_degree f₁
      _ = 5 := hD5deg5 f₁ hf₁D5
  have hf2cap : (G.neighborFinset f₂ ∩ Iso).card ≤ 5 := by
    calc (G.neighborFinset f₂ ∩ Iso).card ≤ (G.neighborFinset f₂).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree f₂ := G.card_neighborFinset_eq_degree f₂
      _ = 5 := hD5deg5 f₂ hf₂D5
  -- === Rewrite the goal filters into `D4` form. ===
  have hgoaleq : (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card))
      = D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hD4def, Finset.filter_filter]
  have hzeroeq : (Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 0))
      = D4.filter (fun h => (G.neighborFinset h ∩ Iso).card = 0) := by
    rw [hD4def, Finset.filter_filter]
  rw [hgoaleq, hzeroeq]
  have hgD4 : g ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hg, hgd⟩
  have hgR : g ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) :=
    Finset.mem_filter.mpr ⟨hgD4, by omega⟩
  -- === The zero-corrected per-hub ledger bound over `D4.erase g`. ===
  have hpt : ∀ h ∈ D4.erase g,
      (G.neighborFinset h ∩ Iso).card
          + (if (G.neighborFinset h ∩ Iso).card = 0 then 1 else 0)
        ≤ 1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
          + (if G.Adj g h then 1 else 0) := by
    intro h hh
    rw [Finset.mem_erase] at hh
    obtain ⟨hne, hhD4⟩ := hh
    have hhHub : h ∈ Hub := hD4sub hhD4
    have hhdeg : G.degree h = 4 := hD4deg4 h hhD4
    by_cases hadj : G.Adj g h
    · have hsplit := nbr_split_three_twenty G Hub Iso hdisj h
      rw [hhdeg] at hsplit
      have hgN : g ∈ G.neighborFinset h ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h g).mpr hadj.symm, hg⟩
      have hbge1 : 1 ≤ (G.neighborFinset h ∩ Hub).card := Finset.card_pos.mpr ⟨g, hgN⟩
      rw [if_pos hadj]
      split_ifs <;> omega
    · have hcap := isoDeg_le_two_of_nonadj_rich_twenty G Hub Iso hshare hno2hub g h hg hhHub
        hgd hhdeg (Ne.symm hne) hadj hgiso
      rw [if_neg hadj]
      split_ifs <;> omega
  have hH3 := Finset.sum_le_sum hpt
  have hLHSeq : (∑ h ∈ D4.erase g, ((G.neighborFinset h ∩ Iso).card
          + (if (G.neighborFinset h ∩ Iso).card = 0 then 1 else 0)))
      = (∑ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card)
        + ((D4.erase g).filter (fun h => (G.neighborFinset h ∩ Iso).card = 0)).card := by
    rw [Finset.sum_add_distrib]
    congr 1
    exact (Finset.card_filter _ _).symm
  have hRHSeq : (∑ h ∈ D4.erase g,
        (1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
          + (if G.Adj g h then 1 else 0)))
      = (D4.erase g).card
        + ((D4.erase g).filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
        + ((D4.erase g).filter (fun h => G.Adj g h)).card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    · congr 1
      exact (Finset.card_filter _ _).symm
    · exact (Finset.card_filter _ _).symm
  rw [hLHSeq, hRHSeq] at hH3
  have hEraseCard : (D4.erase g).card = 7 := by
    rw [Finset.card_erase_of_mem hgD4, hD4card]
  -- === Rich-set bookkeeping: `|R| = |R'| + 1` for `R' = R ∖ {g}`. ===
  have hRerase : (D4.erase g).filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
      = (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase g := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have hRcards : (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
      = ((D4.erase g).filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card + 1 := by
    rw [hRerase, Finset.card_erase_of_mem hgR]
    have hge1 : 1 ≤ (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
      Finset.card_pos.mpr ⟨g, hgR⟩
    omega
  -- === The zero set avoids the rich hub `g`. ===
  have hZerase : ((D4.erase g).filter (fun h => (G.neighborFinset h ∩ Iso).card = 0)).card
      = (D4.filter (fun h => (G.neighborFinset h ∩ Iso).card = 0)).card := by
    have hseteq : (D4.erase g).filter (fun h => (G.neighborFinset h ∩ Iso).card = 0)
        = D4.filter (fun h => (G.neighborFinset h ∩ Iso).card = 0) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hx⟩, hz⟩
        exact ⟨hx, hz⟩
      · rintro ⟨hx, hz⟩
        exact ⟨⟨fun he => by rw [he] at hz; omega, hx⟩, hz⟩
    rw [hseteq]
  -- === `g`'s neighbour split caps the adjacent budget: `A' + isoDeg g ≤ 4`. ===
  have hgsplit := nbr_split_three_twenty G Hub Iso hdisj g
  rw [hgd] at hgsplit
  have hA'sub : (D4.erase g).filter (fun h => G.Adj g h) ⊆ G.neighborFinset g ∩ Hub := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_erase] at hx
    obtain ⟨⟨_, hxD4⟩, hxadj⟩ := hx
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g x).mpr hxadj, hD4sub hxD4⟩
  have hA'card : ((D4.erase g).filter (fun h => G.Adj g h)).card
      ≤ (G.neighborFinset g ∩ Hub).card := Finset.card_le_card hA'sub
  -- === Ledger split at `g`. ===
  have hsumerase : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset g ∩ Iso).card
        + ∑ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card :=
    (Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) hgD4).symm
  -- === The three-way dichotomy. ===
  by_cases h6 : 6 ≤ (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
  · exact Or.inl h6
  by_cases hcomb : (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 ∧
      (∑ r ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset r ∩ Iso).card)
        + (∑ r ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
            (G.neighborFinset r
              ∩ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 13
  · exact Or.inr (Or.inl hcomb)
  refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩)
  · omega
  · have h5or : (G.neighborFinset f₁ ∩ Iso).card = 5
        ∨ (G.neighborFinset f₂ ∩ Iso).card = 5 := by
      omega
    rcases h5or with h5f | h5f
    · exact ⟨f₁, hD5sub hf₁D5, hD5deg5 f₁ hf₁D5, h5f⟩
    · exact ⟨f₂, hD5sub hf₂D5, hD5deg5 f₂ hf₂D5, h5f⟩
  · omega
  · omega
  · intro hR5
    by_contra hlt
    exact hcomb ⟨hR5, by omega⟩

end N20

end ACMax
