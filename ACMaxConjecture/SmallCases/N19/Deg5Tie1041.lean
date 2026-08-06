import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.R5ResidHelpers
import ACMaxConjecture.SmallCases.N19.Deg5ZSlots
import ACMaxConjecture.SmallCases.N19.Deg5SameZ
import ACMaxConjecture.SmallCases.N19.Deg5Pack

/-! # The `(1,041) `tie-world `Z`-leaf extraction (`n = 19`, deg-5 corner) -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
theorem zleaf_extract_tie_1041_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum17 : Hub.card + Iso.card = 17)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 7)
    (hdsum : ∑ w ∈ Hub, G.degree w = 41)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hnorich : ∀ h ∈ Hub, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card ≤ 2) :
    ∃ h₁ h₂ a b c z : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
  classical
  -- === Degree partition: 9 deg-4 hubs, 1 deg-5 hub. ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  set D4 : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 19) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
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
  -- === Iso-degree ledger: ∑_Hub isoDeg = 21, so ∑_D4 isoDeg ≥ 16. ===
  have hisosum21 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 21 := by
    have h := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at h; omega
  have hisosplit : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 21 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hisosum21
  obtain ⟨r, hD5single⟩ := Finset.card_eq_one.mp hD5card
  have hrD5 : r ∈ D5 := by rw [hD5single]; exact Finset.mem_singleton_self r
  have hrHub : r ∈ Hub := hD5sub hrD5
  have hrdeg5 : G.degree r = 5 := hD5deg5 r hrD5
  have hisor5 : (G.neighborFinset r ∩ Iso).card ≤ 5 := by
    calc (G.neighborFinset r ∩ Iso).card ≤ (G.neighborFinset r).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree r := G.card_neighborFinset_eq_degree r
      _ = 5 := hrdeg5
  have hD5isosum : (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset r ∩ Iso).card := by rw [hD5single, Finset.sum_singleton]
  have hD4isoge : 16 ≤ ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by
    rw [hD5isosum] at hisosplit; omega
  -- === The iso-poor deg-4 hubs: at most two of them. ===
  set poor : Finset (Fin 19) :=
    D4.filter (fun h => (G.neighborFinset h ∩ Iso).card ≤ 1) with hpoordef
  have hpoorcard : poor.card
      = ∑ h ∈ D4, (if (G.neighborFinset h ∩ Iso).card ≤ 1 then 1 else 0) := by
    rw [hpoordef, Finset.card_filter]
  have hkey18 : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card) + poor.card ≤ 18 := by
    rw [hpoorcard, ← Finset.sum_add_distrib]
    calc (∑ h ∈ D4, ((G.neighborFinset h ∩ Iso).card
            + if (G.neighborFinset h ∩ Iso).card ≤ 1 then 1 else 0))
          ≤ ∑ _h ∈ D4, 2 := Finset.sum_le_sum fun h hh => by
            by_cases hc : (G.neighborFinset h ∩ Iso).card ≤ 1
            · rw [if_pos hc]; omega
            · rw [if_neg hc]; have := hnorich h (hD4sub hh) (hD4deg4 h hh); omega
      _ = 18 := by rw [Finset.sum_const, hD4card, smul_eq_mul]
  have hm_le2 : poor.card ≤ 2 := by omega
  have hm_of_zero : ∀ a ∈ D4, (G.neighborFinset a ∩ Iso).card = 0 → poor.card ≤ 1 := by
    intro a haD4 hia0
    have hsub : poor ⊆ {a} := by
      intro h' hh'
      rw [Finset.mem_singleton]
      by_contra hne'
      rw [hpoordef, Finset.mem_filter] at hh'
      obtain ⟨hh'D4, hih'1⟩ := hh'
      have hh'Ea : h' ∈ D4.erase a := Finset.mem_erase.mpr ⟨hne', hh'D4⟩
      have hs1 : (G.neighborFinset a ∩ Iso).card
          + (∑ h ∈ D4.erase a, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) haD4
      have hs2 : (G.neighborFinset h' ∩ Iso).card
          + (∑ h ∈ (D4.erase a).erase h', (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4.erase a, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase (D4.erase a) (fun h => (G.neighborFinset h ∩ Iso).card) hh'Ea
      have hcard7 : ((D4.erase a).erase h').card = 7 := by
        rw [Finset.card_erase_of_mem hh'Ea, Finset.card_erase_of_mem haD4, hD4card]
      have hrest2 : (∑ h ∈ (D4.erase a).erase h', (G.neighborFinset h ∩ Iso).card) ≤ 14 := by
        calc (∑ h ∈ (D4.erase a).erase h', (G.neighborFinset h ∩ Iso).card)
              ≤ ∑ _h ∈ (D4.erase a).erase h', 2 := Finset.sum_le_sum fun h hh => by
                have hhD4 : h ∈ D4 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hh)
                exact hnorich h (hD4sub hhD4) (hD4deg4 h hhD4)
          _ = 14 := by rw [Finset.sum_const, hcard7, smul_eq_mul]
      omega
    calc poor.card ≤ ({a} : Finset (Fin 19)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton a
  -- === The Z-slots and the all-deg-4 M-endpoint. ===
  obtain ⟨z₁, z₂, _, hz1Z, hz2Z, _, _, hnohub⟩ :=
    zslot_skeleton_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg5 hT
  have hzf := zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak
  obtain ⟨_, hz1hub2, _⟩ := hzf z₁ hz1Z
  obtain ⟨_, hz2hub2, _⟩ := hzf z₂ hz2Z
  have extract_pq : ∀ w : Fin 19, (G.neighborFinset w ∩ Hub).card = 2 → ¬ G.Adj r w →
      ∃ p q : Fin 19, p ∈ Hub ∧ q ∈ Hub ∧ G.degree p = 4 ∧ G.degree q = 4 ∧
        p ≠ q ∧ G.Adj w p ∧ G.Adj w q := by
    intro w hw2 hwr
    obtain ⟨p, q, hpqne, hpqeq⟩ := Finset.card_eq_two.mp hw2
    have hpmem : p ∈ G.neighborFinset w ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_self p {q}
    have hqmem : q ∈ G.neighborFinset w ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    obtain ⟨hpadj, hpHub⟩ := Finset.mem_inter.mp hpmem
    obtain ⟨hqadj, hqHub⟩ := Finset.mem_inter.mp hqmem
    rw [G.mem_neighborFinset] at hpadj hqadj
    have hpdeg : G.degree p = 4 := by
      by_contra hpne4
      have hpD5 : p ∈ D5 := by rw [hD5def, Finset.mem_filter]; exact ⟨hpHub, hpne4⟩
      rw [hD5single, Finset.mem_singleton] at hpD5
      exact hwr (by rw [← hpD5]; exact hpadj.symm)
    have hqdeg : G.degree q = 4 := by
      by_contra hqne4
      have hqD5 : q ∈ D5 := by rw [hD5def, Finset.mem_filter]; exact ⟨hqHub, hqne4⟩
      rw [hD5single, Finset.mem_singleton] at hqD5
      exact hwr (by rw [← hqD5]; exact hqadj.symm)
    exact ⟨p, q, hpHub, hqHub, hpdeg, hqdeg, hpqne, hpadj, hqadj⟩
  obtain ⟨z, p, q, hzZ, hpHub, hqHub, hpdeg, hqdeg, hpqne, hzp, hzq⟩ :
      ∃ z p q : Fin 19, z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
        p ∈ Hub ∧ q ∈ Hub ∧ G.degree p = 4 ∧ G.degree q = 4 ∧ p ≠ q ∧
        G.Adj z p ∧ G.Adj z q := by
    by_cases hrz1 : G.Adj r z₁
    · have hrz2 : ¬ G.Adj r z₂ := fun h => hnohub r hrHub ⟨hrz1, h⟩
      obtain ⟨p, q, hpHub, hqHub, hpdeg, hqdeg, hpqne, hzp, hzq⟩ := extract_pq z₂ hz2hub2 hrz2
      exact ⟨z₂, p, q, hz2Z, hpHub, hqHub, hpdeg, hqdeg, hpqne, hzp, hzq⟩
    · obtain ⟨p, q, hpHub, hqHub, hpdeg, hqdeg, hpqne, hzp, hzq⟩ := extract_pq z₁ hz1hub2 hrz1
      exact ⟨z₁, p, q, hz1Z, hpHub, hqHub, hpdeg, hqdeg, hpqne, hzp, hzq⟩
  -- === The same-z pair: non-adjacent, one iso-poor. ===
  obtain ⟨_, _, hpoor_or⟩ :=
    same_z_pair_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hT hC4 hno2hub
      z p q hzZ hpHub hqHub hpdeg hqdeg hpqne hzp hzq
  have hpD4 : p ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hpHub, hpdeg⟩
  have hqD4 : q ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hqHub, hqdeg⟩
  have hpq_iso_ge2 :
      2 ≤ (G.neighborFinset p ∩ Iso).card + (G.neighborFinset q ∩ Iso).card := by
    have he1 : (G.neighborFinset p ∩ Iso).card
        + (∑ h ∈ D4.erase p, (G.neighborFinset h ∩ Iso).card)
        = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
      Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) hpD4
    have hqEp : q ∈ D4.erase p := Finset.mem_erase.mpr ⟨hpqne.symm, hqD4⟩
    have he2 : (G.neighborFinset q ∩ Iso).card
        + (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card)
        = ∑ h ∈ D4.erase p, (G.neighborFinset h ∩ Iso).card :=
      Finset.add_sum_erase (D4.erase p) (fun h => (G.neighborFinset h ∩ Iso).card) hqEp
    have hcard7 : ((D4.erase p).erase q).card = 7 := by
      rw [Finset.card_erase_of_mem hqEp, Finset.card_erase_of_mem hpD4, hD4card]
    have hrest : (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card) ≤ 14 := by
      calc (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card)
            ≤ ∑ _h ∈ (D4.erase p).erase q, 2 := Finset.sum_le_sum fun h hh => by
              have hhD4 : h ∈ D4 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hh)
              exact hnorich h (hD4sub hhD4) (hD4deg4 h hhD4)
        _ = 14 := by rw [Finset.sum_const, hcard7, smul_eq_mul]
    omega
  -- === Choose h₂ ∈ {p, q} with isoDeg h₂ ≥ 1 and isoDeg h₂ + |poor| ≤ 3. ===
  have hchoose_of_poor : ∀ a b : Fin 19, a ∈ Hub → b ∈ Hub → G.degree a = 4 → G.degree b = 4 →
      G.Adj z a → G.Adj z b → (G.neighborFinset a ∩ Iso).card ≤ 1 →
      2 ≤ (G.neighborFinset a ∩ Iso).card + (G.neighborFinset b ∩ Iso).card →
      a ∈ D4 → b ∈ D4 →
      ∃ h₂ : Fin 19, h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧ G.Adj z h₂ ∧
        1 ≤ (G.neighborFinset h₂ ∩ Iso).card ∧
        (G.neighborFinset h₂ ∩ Iso).card + poor.card ≤ 3 := by
    intro a b haHub hbHub hda hdb hza hzb hia1 hsum2 haD4 _hbD4
    by_cases hia0 : (G.neighborFinset a ∩ Iso).card = 0
    · have hib2 : (G.neighborFinset b ∩ Iso).card = 2 := by
        have hble := hnorich b hbHub hdb; omega
      have hm1 : poor.card ≤ 1 := hm_of_zero a haD4 hia0
      exact ⟨b, hbHub, hdb, hzb, by omega, by omega⟩
    · have hia1' : (G.neighborFinset a ∩ Iso).card = 1 := by omega
      exact ⟨a, haHub, hda, hza, by omega, by omega⟩
  obtain ⟨h₂, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hh₂summ⟩ :
      ∃ h₂ : Fin 19, h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧ G.Adj z h₂ ∧
        1 ≤ (G.neighborFinset h₂ ∩ Iso).card ∧
        (G.neighborFinset h₂ ∩ Iso).card + poor.card ≤ 3 := by
    rcases hpoor_or with hp1 | hq1
    · exact hchoose_of_poor p q hpHub hqHub hpdeg hqdeg hzp hzq hp1 hpq_iso_ge2 hpD4 hqD4
    · refine hchoose_of_poor q p hqHub hpHub hqdeg hpdeg hzq hzp hq1 ?_ hqD4 hpD4
      omega
  -- === The exclusion count: a fresh deg-4 hub avoiding z, h₂, and h₂'s twins. ===
  obtain ⟨_, hzhub2, _⟩ := hzf z hzZ
  have hzInterZ : z ∈ G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ z).mpr hzh₂.symm, hzZ⟩
  have hzDeg1 :
      1 ≤ (G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19))).card :=
    Finset.card_pos.mpr ⟨z, hzInterZ⟩
  have hhubDeg : (G.neighborFinset h₂ ∩ Hub).card ≤ 3 - (G.neighborFinset h₂ ∩ Iso).card := by
    have h := nbr_split_three_nineteen G Hub Iso hdisj h₂
    rw [hh₂deg] at h; omega
  have hB3card : ((G.neighborFinset h₂ ∩ Iso).biUnion
      (fun t => (G.neighborFinset t ∩ Hub).erase h₂)).card
      ≤ 2 * (G.neighborFinset h₂ ∩ Iso).card := by
    calc ((G.neighborFinset h₂ ∩ Iso).biUnion
          (fun t => (G.neighborFinset t ∩ Hub).erase h₂)).card
        ≤ ∑ t ∈ G.neighborFinset h₂ ∩ Iso, ((G.neighborFinset t ∩ Hub).erase h₂).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ t ∈ G.neighborFinset h₂ ∩ Iso, 2 := Finset.sum_le_sum fun t ht => by
            have htIso : t ∈ Iso := (Finset.mem_inter.mp ht).2
            have h3card : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t htIso
            have ht2 : t ∈ G.neighborFinset h₂ := (Finset.mem_inter.mp ht).1
            have hh₂t : h₂ ∈ G.neighborFinset t := by
              rw [G.mem_neighborFinset] at ht2 ⊢; exact ht2.symm
            have hh₂mem : h₂ ∈ G.neighborFinset t ∩ Hub :=
              Finset.mem_inter.mpr ⟨hh₂t, hh₂Hub⟩
            have h1 := Finset.card_erase_of_mem hh₂mem
            rw [h3card] at h1; omega
      _ = 2 * (G.neighborFinset h₂ ∩ Iso).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
  set Q : Fin 19 → Prop := fun x => G.Adj x z ∨ G.Adj x h₂ ∨
      (G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso) ≠ ∅ ∨
      (G.neighborFinset x ∩ Iso).card ≤ 1 with hQdef
  have hbadsub : D4.filter Q ⊆
      G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub ∪
        (G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂) ∪
        poor := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxD4, hxQ⟩ := hx
    simp only [hQdef] at hxQ
    have hxHub : x ∈ Hub := hD4sub hxD4
    rcases hxQ with h1 | h2 | h3 | h4
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z x).mpr h1.symm, hxHub⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ x).mpr h2.symm, hxHub⟩)))
    · rw [← Finset.nonempty_iff_ne_empty] at h3
      obtain ⟨t, ht⟩ := h3
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
      obtain ⟨⟨hxt, hh₂t⟩, htIso⟩ := ht
      by_cases hxh₂ : x = h₂
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset z x).mpr (by rw [hxh₂]; exact hzh₂), hxHub⟩)))
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset h₂ t).mpr hh₂t, htIso⟩, ?_⟩
        rw [Finset.mem_erase]
        exact ⟨hxh₂, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset t x).mpr hxt.symm, hxHub⟩⟩
    · exact Finset.mem_union_right _ (by rw [hpoordef, Finset.mem_filter]; exact ⟨hxD4, h4⟩)
  have hbadcard : (D4.filter Q).card ≤ 8 := by
    have hc := Finset.card_le_card hbadsub
    have hu1 := Finset.card_union_le
      (G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub ∪
        (G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂)) poor
    have hu2 := Finset.card_union_le (G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub)
      ((G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂))
    have hu3 := Finset.card_union_le (G.neighborFinset z ∩ Hub) (G.neighborFinset h₂ ∩ Hub)
    omega
  have hcardsum : (D4.filter Q).card + (D4.filter (fun a => ¬ Q a)).card = 9 := by
    rw [Finset.card_filter_add_card_filter_not, hD4card]
  have hgoodne : (D4.filter (fun a => ¬ Q a)).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨x, hx⟩ := hgoodne
  rw [Finset.mem_filter] at hx
  obtain ⟨hxD4, hxnQ⟩ := hx
  simp only [hQdef] at hxnQ
  push Not at hxnQ
  obtain ⟨hxnz, hxnh₂, hxshare, hxiso2⟩ := hxnQ
  have hxHub : x ∈ Hub := hD4sub hxD4
  have hxne : x ≠ h₂ := by
    rintro rfl
    rw [Finset.inter_self, ← Finset.card_eq_zero] at hxshare
    omega
  exact zleaf_pack_share0_nineteen G Hub Iso hiso3 hisodeg3 x h₂ z hxHub hh₂Hub
    (hD4deg4 x hxD4) hh₂deg hzZ hxne hxnh₂ (by omega) hh₂iso1 hxshare hzh₂ hxnz

end N19

end ACMax
