import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N16.Dense
import ACMaxConjecture.SmallCases.N16.TwoHubSelect

/-!
# Deg-`5` two-hub corner selection for `n = 16` (`|D| = 9`, `|Hub| = 7`)

This file supplies `two_hub_corner_select_deg5_sixteen`, the hub-pair *selection* lemma for the
`e(M) = 1`, `|Hub| = 7` two-hub corner with one degree-`5` hub `g` (regime
`Hub.card = 7, Iso.card = 7, ∑deg = 29, ∑internal = 4`).

The universal good-`C₄` share bound `nonadj_hubs_share_le_one_iso` **fails** for a non-adjacent
degree-`5`/degree-`4` hub pair sharing two `M`-isolated twins (their `K₂,₂` has degree-sum
`5 + 4 + 3 + 3 = 15 > 14`, hence is *not* a good-`C₄`).  But share `≤ 1` **does** hold among the six
degree-`4` hubs (their `K₂,₂` has `Σ = 14 ≤ 14`, a good-`C₄`, excluded).  We therefore route around
the degree-`5` hub `g`: the selection uses share `≤ 1` **restricted to degree-`4` hub pairs**.

Inspection of the proved `two_hub_corner_select_sixteen` (`TwinCert16TwoHubSelect.lean`) shows its
`hshare` hypothesis is only ever applied to degree-`4` hub pairs (the extremal `K₂,₂` pair and the
`strong_deg4_count_le_two_sixteen` clique members are all degree-`4`).  We re-prove the degree-`4`
clique bound with the degree-`4`-restricted share, then specialise the regime-`(B)` arithmetic.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **Degree-`4` clique bound under the degree-`4`-restricted share.**  The strong degree-`4` hubs
(iso-degree `≥ 3`) form a clique among degree-`4` pairs, so they number `≤ 2`.  Identical to
`strong_deg4_count_le_two_sixteen` but the share hypothesis is restricted to degree-`4` pairs,
allowing a degree-`5` hub in `Hub`. -/
theorem strong_deg4_count_le_two_deg5_sixteen (G : SimpleGraph (Fin 16))
    (Hub Iso : Finset (Fin 16)) (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (key : ∀ a ∈ Hub, ∀ b ∈ Hub, G.degree a = 4 → G.degree b = 4 → a ≠ b → ¬G.Adj a b →
      min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card)
        ≤ (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card + 1) :
    (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
  classical
  set A : Finset (Fin 16) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA
  set B : Finset (Fin 16) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) with hB
  have hAprop : ∀ a ∈ A, a ∈ Hub ∧ G.degree a = 4 ∧ 3 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hA, Finset.mem_filter] at ha; exact ⟨ha.1, ha.2.1, ha.2.2⟩
  have hBA : B ⊆ A := by
    intro x hx; rw [hB, Finset.mem_filter] at hx; rw [hA, Finset.mem_filter]
    exact ⟨hx.1, hx.2.1, by omega⟩
  have hclique : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b := by
    intro a ha b hb hab
    by_contra hnadj
    obtain ⟨haHub, hda, ha3⟩ := hAprop a ha
    obtain ⟨hbHub, hdb, hb3⟩ := hAprop b hb
    have hk := key a haHub b hbHub hda hdb hab hnadj
    have hs := hshare a haHub hda b hbHub hdb hab hnadj
    have : 3 ≤ min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card) :=
      le_min ha3 hb3
    omega
  have hkey : ∀ a ∈ A, A.card - 1 + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    obtain ⟨haHub, hda, _⟩ := hAprop a ha
    have hsub : A.erase a ⊆ G.neighborFinset a ∩ Hub := by
      intro b hb
      have hbA : b ∈ A := Finset.mem_of_mem_erase hb
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have hbHub := (hAprop b hbA).1
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨(hclique a ha b hbA (Ne.symm hba)), hbHub⟩
    have hc1 : A.card - 1 ≤ (G.neighborFinset a ∩ Hub).card := by
      rw [← Finset.card_erase_of_mem ha]; exact Finset.card_le_card hsub
    have hc2 := hub_neighbor_le_sixteen G Hub Iso hdisj a hda
    omega
  rcases Finset.eq_empty_or_nonempty B with hBe | hBne
  · have hBcard : B.card = 0 := by rw [hBe]; rfl
    rcases Finset.eq_empty_or_nonempty A with hAe | ⟨a, ha⟩
    · rw [hAe]; simp [hBcard]
    · obtain ⟨_, _, ha3⟩ := hAprop a ha
      have := hkey a ha
      have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
  · obtain ⟨a, haB⟩ := hBne
    have haA : a ∈ A := hBA haB
    have ha4 : 4 ≤ (G.neighborFinset a ∩ Iso).card := by
      rw [hB, Finset.mem_filter] at haB; exact haB.2.2
    have := hkey a haA
    have hBleA : B.card ≤ A.card := Finset.card_le_card hBA
    have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, haA⟩
    omega

/-- **Hub-pair selection for the `n = 16` `|Hub| = 7` deg-`5` two-hub corner.**  Given the
`|Hub| = 7`, `|Iso| = 7`, `∑deg = 29` (one degree-`5` `g` + six degree-`4`), `∑internal = 4`
regime, with each `M`-isolated twin meeting exactly three hubs (`hiso3`) and the good-`C₄` share
bound holding **for degree-`4` hub pairs** (`hshare`), there exist two non-adjacent degree-`4` hubs
each retaining `≥ 2` private `M`-isolated twins.  Routes around the degree-`5` hub `g` by the
degree-`4` clique bound (`strong_deg4_count_le_two_deg5_sixteen`). -/
theorem two_hub_corner_select_deg5_sixteen (G : SimpleGraph (Fin 16)) (Hub Iso : Finset (Fin 16))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hHub7 : Hub.card = 7) (hIso7 : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 29) :
    ∃ h₁ h₂ : Fin 16, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  have hiso_le : ∀ a : Fin 16, (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
    intro a
    rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
  set F : Finset (Fin 16) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 4) with hFdef
  by_cases hk : 2 ≤ F.card
  · obtain ⟨h₁, hh1F, h₂, hh2F, hne⟩ := Finset.one_lt_card.mp hk
    obtain ⟨hh1, hd1, h1iso4⟩ := Finset.mem_filter.mp hh1F
    obtain ⟨hh2, hd2, h2iso4⟩ := Finset.mem_filter.mp hh2F
    have hsub : ∀ h : Fin 16, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card = 4 →
        G.neighborFinset h ⊆ Iso := by
      intro h hdh hh4
      have hdc : (G.neighborFinset h).card = 4 := by rw [G.card_neighborFinset_eq_degree, hdh]
      have heq : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hdc, hh4]))
      rw [← heq]; exact Finset.inter_subset_right
    have h1sub : G.neighborFinset h₁ ⊆ Iso := hsub h₁ hd1 h1iso4
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      exact Finset.disjoint_left.mp hdisj hh2 (h1sub ((G.mem_neighborFinset h₁ h₂).mpr hadj))
    have hsh : (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 :=
      hshare h₁ hh1 hd1 h₂ hh2 hd2 hne hnadj
    have hsh' : (G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso).card ≤ 1 :=
      hshare h₂ hh2 hd2 h₁ hh1 hd1 (Ne.symm hne) (fun h => hnadj h.symm)
    have hfin := select_finish_sixteen G Iso h₁ h₂ (by omega) (by omega)
    exact ⟨h₁, h₂, hh1, hh2, hd1, hd2, hne, hnadj, hfin.1, hfin.2⟩
  · by_contra hcon
    have key := nogood_of_not_select_sixteen G Hub Iso hcon
    have hmf := strong_deg4_count_le_two_deg5_sixteen G Hub Iso hdisj hshare key
    set m3 : Finset (Fin 16) := Hub.filter (fun h => G.degree h = 4 ∧
      3 ≤ (G.neighborFinset h ∩ Iso).card) with hm3
    set f4 : Finset (Fin 16) := Hub.filter (fun h => G.degree h = 4 ∧
      4 ≤ (G.neighborFinset h ∩ Iso).card) with hf4
    have hisoSum := hub_iso_sum_sixteen G Hub Iso hiso3
    have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
      intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
    set D5 : Finset (Fin 16) := Hub.filter (fun h => G.degree h = 5) with hD5
    have hD5card : D5.card = 1 := by
      have hsplit : ∀ h ∈ Hub, G.degree h = 4 + (if G.degree h = 5 then 1 else 0) := by
        intro h hh; rcases hdeg45 h hh with h4 | h5
        · rw [h4]; simp
        · rw [h5]; simp
      have hss : ∑ h ∈ Hub, G.degree h = 4 * Hub.card + D5.card := by
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
          mul_comm, hD5, Finset.sum_boole, Nat.cast_id]
      rw [hdsum, hHub7] at hss; omega
    obtain ⟨g, hgeq⟩ := Finset.card_eq_one.mp hD5card
    have hgD5 : g ∈ D5 := by rw [hgeq]; exact Finset.mem_singleton_self g
    have hgHub : g ∈ Hub := (Finset.mem_filter.mp hgD5).1
    have hgdeg5 : G.degree g = 5 := (Finset.mem_filter.mp hgD5).2
    set T : Finset (Fin 16) := Hub.erase g with hT
    have hTsub : T ⊆ Hub := Finset.erase_subset _ _
    have hTdeg4 : ∀ v ∈ T, G.degree v = 4 := by
      intro v hv
      have hvHub : v ∈ Hub := hTsub hv
      rcases hdeg45 v hvHub with h4 | h5
      · exact h4
      · exfalso
        have hvD5 : v ∈ D5 := Finset.mem_filter.mpr ⟨hvHub, h5⟩
        rw [hgeq, Finset.mem_singleton] at hvD5
        exact (Finset.ne_of_mem_erase hv) hvD5
    have hT6 : T.card = 6 := by rw [hT, Finset.card_erase_of_mem hgHub, hHub7]
    have hgiso_le : (G.neighborFinset g ∩ Iso).card ≤ 5 := by
      have := hiso_le g; rw [hgdeg5] at this; exact this
    have hTsumsplit : (G.neighborFinset g ∩ Iso).card
        + ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card = 21 := by
      rw [hT, Finset.add_sum_erase Hub (fun v => (G.neighborFinset v ∩ Iso).card) hgHub]
      rw [hisoSum, hIso7]
    have hTsumge : 16 ≤ ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card := by omega
    have hAeq : m3 = T.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hm3, hT]; ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hxHub, hxd4, hx3⟩
        refine ⟨⟨?_, hxHub⟩, hx3⟩
        intro he; rw [he] at hxd4; omega
      · rintro ⟨⟨hxg, hxHub⟩, hx3⟩
        exact ⟨hxHub, hTdeg4 x (Finset.mem_erase.mpr ⟨hxg, hxHub⟩), hx3⟩
    have hBeq : f4 = T.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hf4, hT]; ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hxHub, hxd4, hx4⟩
        refine ⟨⟨?_, hxHub⟩, hx4⟩
        intro he; rw [he] at hxd4; omega
      · rintro ⟨⟨hxg, hxHub⟩, hx4⟩
        exact ⟨hxHub, hTdeg4 x (Finset.mem_erase.mpr ⟨hxg, hxHub⟩), hx4⟩
    have hdecomp : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card
        = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
      intro a ha
      have := hiso_le a; rw [hTdeg4 a ha] at this; split_ifs <;> omega
    have hcong : ∑ a ∈ T, (G.neighborFinset a ∩ Iso).card
        = ∑ a ∈ T, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) :=
      Finset.sum_congr rfl hdecomp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter,
      ← hAeq, ← hBeq] at hcong
    have hn1 : (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 6 := by
      rw [← hT6]; exact Finset.card_le_card (Finset.filter_subset _ _)
    have hu : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 6 := by
      rw [← hT6]; exact Finset.card_le_card (Finset.filter_subset _ _)
    omega

end N16

end ACMax
