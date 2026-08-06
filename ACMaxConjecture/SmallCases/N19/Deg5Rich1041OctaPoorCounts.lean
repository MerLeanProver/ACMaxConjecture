import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5RichCap
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Blocker

/-!
# The poor-layer counting foundation for the (10,7,41) octahedron residual (`n = 19`)

The deg-`5` analog of `octahedron_poor_counts_nineteen`.  With the rich set
`R := Hub.filter (deg 4 ∧ 2 ≤ isoDeg)` of cardinality `5` (`rich_count_ge_five`
+ `rich_le_five_blocked`), the poor set `P := Hub ∖ R ∖ {f}` has `4` members,
all degree-`4` of isoDeg exactly `1`; the deg-`5` hub `f` (isoDeg `5`) carries
`5` of the `21` `Iso`-incidences, leaving `Σ_R isoDeg = 12`, `Σ_P isoDeg = 4`.
-/

namespace ACMax

open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The poor set `P` and the `Iso`-incidence split.** -/
theorem octahedron_poor_counts_share2_1041_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum17 : Hub.card + Iso.card = 17)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 41)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (_hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (g : Fin 19) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 19) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hz2 : G.Adj z h₂) (_hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 19, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
    (f : Fin 19) (hfHub : f ∈ Hub) (hfd : G.degree f = 5)
    (hfiso5 : (G.neighborFinset f ∩ Iso).card = 5) :
    ((Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1)).card = 4 ∧
      (∀ w ∈ Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1),
        G.degree w = 4 ∧ (G.neighborFinset w ∩ Iso).card = 1) ∧
      (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card) = 12) := by
  classical
  -- === Degree partition: 9 deg-4 hubs, the given deg-5 hub `f`. ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  set D4 : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 19) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
  have hD4deg4 : ∀ h ∈ D4, G.degree h = 4 := by
    intro h hh; rw [hD4def, Finset.mem_filter] at hh; exact hh.2
  have hD5deg5 : ∀ h ∈ D5, G.degree h = 5 := by
    intro h hh; rw [hD5def, Finset.mem_filter] at hh
    rcases hdeg45 h hh.1 with h4 | h5
    · exact absurd h4 hh.2
    · exact h5
  have hcardpart : D4.card + D5.card = 10 := by
    rw [hD4def, hD5def, Finset.card_filter_add_card_filter_not]; exact hHub
  have hsumdeg : (∑ h ∈ D4, G.degree h) + (∑ h ∈ D5, G.degree h) = 41 := by
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
  have hD4card : D4.card = 9 := by omega
  have hD5card : D5.card = 1 := by omega
  -- `f` is the unique deg-`5` hub, so `D5 = {f}`.
  have hfD5 : f ∈ D5 := by
    rw [hD5def, Finset.mem_filter]; exact ⟨hfHub, by omega⟩
  have hD5single : D5 = {f} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hD5card
    rw [ha] at hfD5 ⊢
    rw [Finset.mem_singleton] at hfD5; rw [hfD5]
  -- === Iso-incidence ledger: `∑_Hub isoDeg = 21`, `∑_D4 isoDeg = 16`. ===
  have hisosum21 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 21 := by
    have h := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at h; omega
  have hisosplit : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 21 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hisosum21
  have hD5isosum : (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 5 := by
    rw [hD5single, Finset.sum_singleton]; exact hfiso5
  have hD4iso16 : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card) = 16 := by omega
  -- === Rich lower bound `|R| ≥ 5`. ===
  have hRge5 := rich_count_ge_five_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3
    hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hshare hno2hub g hg hgd hgiso
  -- === Rich upper bound `|R| ≤ 5` (blocker `U`-cover, inlined — never uses `hK23`). ===
  have hRle5 : (Hub.filter (fun h => G.degree h = 4 ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 5 := by
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hpoor
    have hcmem : c ∈ G.neighborFinset h₂ ∩ Iso := by rw [hc]; exact Finset.mem_singleton_self c
    have hcIso : c ∈ Iso := (Finset.mem_inter.mp hcmem).2
    have hcNh₂ : c ∈ G.neighborFinset h₂ := (Finset.mem_inter.mp hcmem).1
    have hh₂c : G.Adj h₂ c := (G.mem_neighborFinset h₂ c).mp hcNh₂
    have hcHub3 : (G.neighborFinset c ∩ Hub).card = 3 := hiso3 c hcIso
    have hh₂inNc : h₂ ∈ G.neighborFinset c ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c h₂).mpr hh₂c.symm, hh₂⟩
    have hzf := zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak
    obtain ⟨_, hzHub2, _⟩ := hzf z hzZ
    have hh₂inNz : h₂ ∈ G.neighborFinset z ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z h₂).mpr hz2, hh₂⟩
    have hh₂Hub2 : (G.neighborFinset h₂ ∩ Hub).card ≤ 2 := by
      have hsplit := nbr_split_three_nineteen G Hub Iso hdisj h₂
      rw [hd₂, hpoor] at hsplit
      have hzInZ : z ∈ G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ z).mpr hz2.symm, hzZ⟩
      have hzge : 1 ≤
          (G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19))).card :=
        Finset.card_pos.mpr ⟨z, hzInZ⟩
      omega
    set U : Finset (Fin 19) :=
      ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)) ∪ (G.neighborFinset h₂ ∩ Hub)
      with hUdef
    have hRsub : (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card))
        ⊆ U.erase h₂ := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxHub, hxdeg, hxiso⟩ := hx
      have hxne : x ≠ h₂ := by rintro rfl; omega
      rw [Finset.mem_erase]
      refine ⟨hxne, ?_⟩
      rw [hUdef]
      rcases hblock x hxHub hxdeg hxiso with hcase1 | hcase2 | hcase3
      · rw [← Finset.nonempty_iff_ne_empty] at hcase1
        obtain ⟨t, ht⟩ := hcase1
        rw [Finset.mem_inter, Finset.mem_inter] at ht
        obtain ⟨⟨htx, hth₂⟩, htIso⟩ := ht
        have htmem : t ∈ G.neighborFinset h₂ ∩ Iso := Finset.mem_inter.mpr ⟨hth₂, htIso⟩
        rw [hc, Finset.mem_singleton] at htmem
        rw [htmem] at htx
        have hxNc : x ∈ G.neighborFinset c :=
          (G.mem_neighborFinset c x).mpr ((G.mem_neighborFinset x c).mp htx).symm
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hxNc, hxHub⟩))
      · have hxNh₂ : x ∈ G.neighborFinset h₂ := (G.mem_neighborFinset h₂ x).mpr hcase2.symm
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxNh₂, hxHub⟩)
      · have hxNz : x ∈ G.neighborFinset z := (G.mem_neighborFinset z x).mpr hcase3.symm
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hxNz, hxHub⟩))
    have hUcard : U.card ≤ 6 := by
      have hAC : ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)).card ≤ 4 := by
        have hkey := Finset.card_union_add_card_inter (G.neighborFinset c ∩ Hub)
          (G.neighborFinset z ∩ Hub)
        have hinter1 : 1 ≤ ((G.neighborFinset c ∩ Hub) ∩ (G.neighborFinset z ∩ Hub)).card :=
          Finset.card_pos.mpr ⟨h₂, Finset.mem_inter.mpr ⟨hh₂inNc, hh₂inNz⟩⟩
        rw [hcHub3, hzHub2] at hkey
        omega
      have hunion := Finset.card_union_le
        ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)) (G.neighborFinset h₂ ∩ Hub)
      rw [hUdef]
      omega
    have hh₂U : h₂ ∈ U := by
      rw [hUdef]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hh₂inNc)
    have hEraseCard : (U.erase h₂).card ≤ 5 := by
      rw [Finset.card_erase_of_mem hh₂U]; omega
    exact le_trans (Finset.card_le_card hRsub) hEraseCard
  -- === `|R| = 5`, `|P| = 4` in `D4`-filter form. ===
  have hRD4eq : (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card))
      = D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hD4def, Finset.filter_filter]
  rw [hRD4eq] at hRge5 hRle5
  have hRcard5 : (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 := by omega
  have hpart_card : (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = D4.card :=
    Finset.card_filter_add_card_filter_not _
  have hPccard : (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 4 := by
    omega
  -- === Sum split over `R ⊔ P` (`P = D4 ∖ R`). ===
  have hpart_sum : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset h ∩ Iso).card) = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not D4 _ _
  -- === `∑_P isoDeg ≤ 4` (each poor hub carries at most one twin). ===
  have hPcsum_le : (∑ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset h ∩ Iso).card) ≤ 4 := by
    have hle : ∀ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset h ∩ Iso).card ≤ 1 := by
      intro h hh; rw [Finset.mem_filter] at hh; omega
    calc (∑ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset h ∩ Iso).card)
        ≤ (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card • 1 :=
          Finset.sum_le_card_nsmul _ _ 1 hle
      _ = 4 := by rw [hPccard, smul_eq_mul, mul_one]
  -- === Strong count `n₃ + n₄ ≤ 2` in `D4`-filter form. ===
  have key := nogood_of_not_select_nineteen G Hub Iso hno2hub
  have hstrong := strong_deg4_count_le_two_deg5_nineteen G Hub Iso hdisj hshare key
  have h3eq : (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card))
      = D4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hD4def, Finset.filter_filter]
  have h4eq : (Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card))
      = D4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hD4def, Finset.filter_filter]
  rw [h3eq, h4eq] at hstrong
  -- === Layer-cake upper bound `∑_R isoDeg ≤ 2·5 + n₃ + n₄ ≤ 12`. ===
  have hRsum_le : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset h ∩ Iso).card) ≤ 12 := by
    have hstep : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset h ∩ Iso).card)
        ≤ ∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (2 + (if 3 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [Finset.mem_filter] at hh
      have hle4 : (G.neighborFinset h ∩ Iso).card ≤ 4 := by
        calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = G.degree h := G.card_neighborFinset_eq_degree h
          _ = 4 := hD4deg4 h hh.1
      split_ifs <;> omega
    have hsplit : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (2 + (if 3 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)))
        = (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card), (2 : ℕ))
          + (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
            (if 3 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
          + (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
            (if 4 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hc0 : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card), (2 : ℕ))
        = 2 * (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hc3 : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (if 3 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
        = ((D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).filter
            (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
      (Finset.card_filter _ _).symm
    have hc4 : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (if 4 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0))
        = ((D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).filter
            (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
      (Finset.card_filter _ _).symm
    have hn3 : ((D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).filter
          (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card))
        = D4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [Finset.filter_filter]
      ext x; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, _, h3⟩; exact ⟨hx, h3⟩
      · rintro ⟨hx, h3⟩; exact ⟨hx, by omega, h3⟩
    have hn4 : ((D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).filter
          (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card))
        = D4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [Finset.filter_filter]
      ext x; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, _, h4⟩; exact ⟨hx, h4⟩
      · rintro ⟨hx, h4⟩; exact ⟨hx, by omega, h4⟩
    rw [hn3] at hc3
    rw [hn4] at hc4
    omega
  -- === Pin the sums: `∑_R isoDeg = 12`, `∑_P isoDeg = 4`. ===
  have hRsum12 : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset h ∩ Iso).card) = 12 := by omega
  have hPcsum4 : (∑ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset h ∩ Iso).card) = 4 := by omega
  -- === The goal's poor set `P` equals `D4.filter (¬ 2 ≤ isoDeg)`. ===
  have hPeq : (Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1))
      = D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    ext x
    simp only [hD4def, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hd, hle⟩; exact ⟨⟨hx, hd⟩, by omega⟩
    · rintro ⟨⟨hx, hd⟩, hlt⟩; exact ⟨hx, hd, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hPeq]; exact hPccard
  · rw [hPeq]
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwD4, hwlt⟩ := hw
    refine ⟨hD4deg4 w hwD4, ?_⟩
    have hmem : w ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) :=
      Finset.mem_filter.mpr ⟨hwD4, hwlt⟩
    have herase := Finset.add_sum_erase
      (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card))
      (fun h => (G.neighborFinset h ∩ Iso).card) hmem
    have herasecard :
        ((D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w).card = 3 := by
      rw [Finset.card_erase_of_mem hmem, hPccard]
    have herasele : (∑ h ∈ (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w,
        (G.neighborFinset h ∩ Iso).card) ≤ 3 := by
      have hle1 : ∀ h ∈ (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w,
          (G.neighborFinset h ∩ Iso).card ≤ 1 := by
        intro h hh; rw [Finset.mem_erase, Finset.mem_filter] at hh; omega
      calc (∑ h ∈ (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w,
            (G.neighborFinset h ∩ Iso).card)
          ≤ ((D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w).card • 1 :=
            Finset.sum_le_card_nsmul _ _ 1 hle1
        _ = 3 := by rw [herasecard, smul_eq_mul, mul_one]
    omega
  · rw [hRD4eq]; exact hRsum12

end N19

end ACMax
