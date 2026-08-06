import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5RichCap
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Blocker

/-! # The ledger profile disjunction for the (11,7,45) octahedron corner (`n = 20`) -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The ledger profile.**  In the blocked rigid tie, the `(11,7,45)` ledger
(Σ isoDeg `= 21`, the rich-count dichotomy `rich_count_1041_twenty` +
`rich_le_five_blocked_1041_twenty` pinning `|R| = 5`, and the strong-layer cap
`n₃ + n₄ ≤ 2` via `strong_deg4_count_le_two_deg5_twenty`) confines the unique
deg-`5` hub `f` to isoDeg `∈ {4, 5}`.  Unlike `n = 19` (`|D4| = 9`), the tenth
degree-`4` hub leaves one unit of ledger slack, so isoDeg `f = 4` is possible;
in that case tightness forces every degree-`4` hub to isoDeg `≥ 1` (the five
poor hubs at exactly `1`) and the `≥ 3`/`≥ 4` layer counts to sum to `2`. -/
theorem ledger_profile_1041_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 11) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 20) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hz2 : G.Adj z h₂) (hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z) :
    ∃ f x : Fin 20, f ∈ Hub ∧ G.degree f = 5 ∧
      ((G.neighborFinset f ∩ Iso).card = 5 ∨
        ((G.neighborFinset f ∩ Iso).card = 4 ∧
          (∀ h ∈ Hub, G.degree h = 4 → 1 ≤ (G.neighborFinset h ∩ Iso).card) ∧
          (Hub.filter (fun h => G.degree h = 4 ∧
              3 ≤ (G.neighborFinset h ∩ Iso).card)).card +
            (Hub.filter (fun h => G.degree h = 4 ∧
              4 ≤ (G.neighborFinset h ∩ Iso).card)).card = 2)) ∧
      x ∈ Hub ∧ G.degree x = 4 ∧ 3 ≤ (G.neighborFinset x ∩ Iso).card ∧ x ≠ f := by
  classical
  -- === The rich-count dichotomy: `|R| = 4` saturates the anchor (left profile). ===
  rcases rich_count_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg hdeg5
      hHub hIso hdsum hshare hno2hub g hg hgd hgiso with hRge5 | ⟨-, ⟨f, hfHub, hfd, hfiso5⟩, -⟩
  swap
  · refine ⟨f, g, hfHub, hfd, Or.inl hfiso5, hg, hgd, hgiso, ?_⟩
    intro hgf
    rw [hgf] at hgd
    omega
  -- === Degree partition: 10 deg-4 hubs, 1 deg-5 hub `f`. ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  set D4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
  have hD4deg4 : ∀ h ∈ D4, G.degree h = 4 := by
    intro h hh; rw [hD4def, Finset.mem_filter] at hh; exact hh.2
  have hD5deg5 : ∀ h ∈ D5, G.degree h = 5 := by
    intro h hh; rw [hD5def, Finset.mem_filter] at hh
    rcases hdeg45 h hh.1 with h4 | h5
    · exact absurd h4 hh.2
    · exact h5
  have hcardpart : D4.card + D5.card = 11 := by
    rw [hD4def, hD5def, Finset.card_filter_add_card_filter_not]; exact hHub
  have hsumdeg : (∑ h ∈ D4, G.degree h) + (∑ h ∈ D5, G.degree h) = 45 := by
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
  have hD4card : D4.card = 10 := by omega
  have hD5card : D5.card = 1 := by omega
  obtain ⟨f, hD5single⟩ := Finset.card_eq_one.mp hD5card
  have hfD5 : f ∈ D5 := by rw [hD5single]; exact Finset.mem_singleton_self f
  have hfdeg5 : G.degree f = 5 := hD5deg5 f hfD5
  have hfHub : f ∈ Hub := by
    have h := hfD5; rw [hD5def, Finset.mem_filter] at h; exact h.1
  -- === Iso-degree ledger: `∑_Hub isoDeg = 21`, split off `f`. ===
  have hisosum21 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 21 := by
    have h := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at h; omega
  have hisosplit : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 21 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hisosum21
  have hD5isosum : (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset f ∩ Iso).card := by rw [hD5single, Finset.sum_singleton]
  rw [hD5isosum] at hisosplit
  have hsf5 : (G.neighborFinset f ∩ Iso).card ≤ 5 := by
    calc (G.neighborFinset f ∩ Iso).card ≤ (G.neighborFinset f).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree f := G.card_neighborFinset_eq_degree f
      _ = 5 := hfdeg5
  -- === Rich count `|R| = 5` (dichotomy lower bound + blocked upper bound). ===
  have hRle5 := rich_le_five_blocked_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3
    hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso
    h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock
  have hRDeq : (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card))
      = D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hD4def, Finset.filter_filter]
  rw [hRDeq] at hRge5 hRle5
  have hR2card : (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 := by
    omega
  -- === Strong count `n₃ + 2n₄ ≤ 2` in iso-level filter form. ===
  have key := nogood_of_not_select_twenty G Hub Iso hno2hub
  have hstrong := strong_deg4_count_le_two_deg5_twenty G Hub Iso hdisj hshare key
  have h3eq : (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card))
      = D4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hD4def, Finset.filter_filter]
  have h4eq : (Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card))
      = D4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hD4def, Finset.filter_filter]
  rw [h3eq, h4eq] at hstrong
  -- === The `≥ 1` layer is capped by `|D4| = 10`. ===
  have hn1le : (D4.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ D4.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  -- === Layer-cake identity: `∑_D4 isoDeg = n₁ + n₂ + n₃ + n₄` (isoDeg ≤ 4 on `D4`). ===
  have hSeq : ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card
      = (D4.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card
        + (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
        + (D4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card
        + (D4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
    have hstep : ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card
        = ∑ h ∈ D4, ((if 1 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
            + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
            + (if 3 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro h hh
      have hle4 : (G.neighborFinset h ∩ Iso).card ≤ 4 := by
        calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = G.degree h := G.card_neighborFinset_eq_degree h
          _ = 4 := hD4deg4 h hh
      split_ifs <;> omega
    have hsplit : ∑ h ∈ D4, ((if 1 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
        = (∑ h ∈ D4, (if 1 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
          + (∑ h ∈ D4, (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
          + (∑ h ∈ D4, (if 3 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
          + (∑ h ∈ D4, (if 4 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hc1 : (∑ h ∈ D4, (if 1 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
        = (D4.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
      (Finset.card_filter _ _).symm
    have hc2 : (∑ h ∈ D4, (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
        = (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
      (Finset.card_filter _ _).symm
    have hc3 : (∑ h ∈ D4, (if 3 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
        = (D4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
      (Finset.card_filter _ _).symm
    have hc4 : (∑ h ∈ D4, (if 4 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
        = (D4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
      (Finset.card_filter _ _).symm
    omega
  -- === Endgame: `isoDeg f ∈ {4, 5}`; `= 4` forces the tight tenth-hub profile. ===
  by_cases hf5 : (G.neighborFinset f ∩ Iso).card = 5
  · refine ⟨f, g, hfHub, hfdeg5, Or.inl hf5, hg, hgd, hgiso, ?_⟩
    intro hgf
    rw [hgf] at hgd
    omega
  · have hf4 : (G.neighborFinset f ∩ Iso).card = 4 := by omega
    have hn1eq : (D4.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card = 10 := by
      omega
    have hn34 : (D4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card
        + (D4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)).card = 2 := by omega
    have hD4eq : D4.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card) = D4 := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      omega
    refine ⟨f, g, hfHub, hfdeg5, Or.inr ⟨hf4, ?_, ?_⟩, hg, hgd, hgiso, ?_⟩
    · intro h hh hh4
      have hhD4 : h ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hh, hh4⟩
      have hmem : h ∈ D4.filter (fun h' => 1 ≤ (G.neighborFinset h' ∩ Iso).card) := by
        rw [hD4eq]; exact hhD4
      exact (Finset.mem_filter.mp hmem).2
    · rw [h3eq, h4eq]
      exact hn34
    · intro hgf
      rw [hgf] at hgd
      omega

end N20

end ACMax
