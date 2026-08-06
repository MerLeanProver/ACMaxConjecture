import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.R5ResidHelpers
import ACMaxConjecture.SmallCases.N20.Deg5ZSlots
import ACMaxConjecture.SmallCases.N20.Deg5SameZ
import ACMaxConjecture.SmallCases.N20.Deg5Pack

/-! # The `(11,7,45)` tie-world `Z`-leaf extraction (`n = 20`, deg-5 corner) -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **Tie-world `Z`-leaf extraction, deg-`5` profile `(11,7,45)` (`n = 20`).**  The verbatim
`n = 19` exclusion count (`bad ≤ 5 + isoDeg h₂ + |poor|` with `|poor| ≤ 25 − 21 = 4`) ties
exactly at `10 = |D4|`, so the cap ledger is reworked per-branch: the same-`z` poor hub is
itself `z`-adjacent and absorbed into the `N(z) ∩ Hub` term; an iso-`0` hub loses two cap slots
(`|poor| ≤ 3`); when the unique deg-`5` hub meets an `M`-end its `z`-slot costs an iso-slot
(`isoDeg r ≤ 4`, so `∑_D4 isoDeg ≥ 17`), and when it avoids both `M`-ends the second end's own
poor hub tightens the same-`z` iso lower bound.  Every branch lands at
`bad ≤ 4 + isoDeg h₂ + |poor| ≤ 9 < 10`, extracting a fresh deg-`4` hub for the share-`0`
packer. -/
theorem zleaf_extract_tie_1041_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 11) (hIso : Iso.card = 7)
    (hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hnorich : ∀ h ∈ Hub, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card ≤ 2) :
    ∃ h₁ h₂ a b c z : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
  classical
  -- === Degree partition: 10 deg-4 hubs, 1 deg-5 hub. ===
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
  -- === Iso-degree ledger: ∑_Hub isoDeg = 21, so ∑_D4 isoDeg ≥ 16. ===
  have hisosum21 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 21 := by
    have hc : ∑ w ∈ Iso, (G.neighborFinset w ∩ Hub).card = ∑ _w ∈ Iso, 3 :=
      Finset.sum_congr rfl (fun w hw => hiso3 w hw)
    rw [cross_count_twenty G Hub Iso, hc, Finset.sum_const, hIso, smul_eq_mul]
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
  -- === The iso-poor deg-4 hubs and the subset cap ledger (`isoDeg + [poor] ≤ 2` per hub). ===
  set poor : Finset (Fin 20) :=
    D4.filter (fun h => (G.neighborFinset h ∩ Iso).card ≤ 1) with hpoordef
  have hcap_pair : ∀ A : Finset (Fin 20), A ⊆ D4 →
      (∑ h ∈ A, (G.neighborFinset h ∩ Iso).card)
        + (A.filter (fun h => (G.neighborFinset h ∩ Iso).card ≤ 1)).card ≤ 2 * A.card := by
    intro A hA
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    calc (∑ h ∈ A, ((G.neighborFinset h ∩ Iso).card
            + if (G.neighborFinset h ∩ Iso).card ≤ 1 then 1 else 0))
          ≤ ∑ _h ∈ A, 2 := Finset.sum_le_sum fun h hh => by
            by_cases hc : (G.neighborFinset h ∩ Iso).card ≤ 1
            · rw [if_pos hc]; omega
            · rw [if_neg hc]
              have := hnorich h (hD4sub (hA hh)) (hD4deg4 h (hA hh)); omega
      _ = 2 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hkey20 : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card) + poor.card ≤ 20 := by
    have h := hcap_pair D4 (Finset.Subset.refl D4)
    have hpc : poor.card
        = (D4.filter (fun h => (G.neighborFinset h ∩ Iso).card ≤ 1)).card := by
      rw [hpoordef]
    rw [hD4card] at h
    omega
  have hpoor4 : poor.card ≤ 4 := by omega
  -- === Trick (c): an iso-0 hub loses two cap slots, so `|poor| ≤ 3`. ===
  have hpoor_of_zero : ∀ a ∈ D4, (G.neighborFinset a ∩ Iso).card = 0 → poor.card ≤ 3 := by
    intro a haD4 hia0
    have hapoor : a ∈ poor := by
      rw [hpoordef, Finset.mem_filter]
      exact ⟨haD4, by omega⟩
    have hcape := hcap_pair (D4.erase a) (Finset.erase_subset a D4)
    have hcard9 : (D4.erase a).card = 9 := by
      rw [Finset.card_erase_of_mem haD4, hD4card]
    have hsume : (G.neighborFinset a ∩ Iso).card
        + (∑ h ∈ D4.erase a, (G.neighborFinset h ∩ Iso).card)
        = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
      Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) haD4
    have hpsub : poor.erase a ⊆ (D4.erase a).filter
        (fun h => (G.neighborFinset h ∩ Iso).card ≤ 1) := by
      intro x hx
      rw [Finset.mem_erase] at hx
      obtain ⟨hxa, hxpoor⟩ := hx
      rw [hpoordef, Finset.mem_filter] at hxpoor
      rw [Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨hxa, hxpoor.1⟩, hxpoor.2⟩
    have hple := Finset.card_le_card hpsub
    have hpe : (poor.erase a).card = poor.card - 1 := Finset.card_erase_of_mem hapoor
    have hppos : 1 ≤ poor.card := Finset.card_pos.mpr ⟨a, hapoor⟩
    rw [hcard9] at hcape
    omega
  -- === The chooser: `h₂` z-adjacent, `isoDeg h₂ ≥ 1`, with `isoDeg h₂ + |poor| ≤ 5` and the
  -- absorbed same-`z` poor witness `w` (tricks (b) and (c)). ===
  have hchoose : ∀ z a b : Fin 20, a ∈ Hub → b ∈ Hub → G.degree a = 4 → G.degree b = 4 →
      G.Adj z a → G.Adj z b → a ∈ D4 → (G.neighborFinset a ∩ Iso).card ≤ 1 →
      1 ≤ (G.neighborFinset a ∩ Iso).card + (G.neighborFinset b ∩ Iso).card →
      ∃ h₂ w : Fin 20, h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧ G.Adj z h₂ ∧
        1 ≤ (G.neighborFinset h₂ ∩ Iso).card ∧ w ∈ poor ∧ G.Adj z w ∧
        (G.neighborFinset h₂ ∩ Iso).card + poor.card ≤ 5 := by
    intro z a b haHub hbHub hda hdb hza hzb haD4 hia1 hge1
    have hapoor : a ∈ poor := by
      rw [hpoordef, Finset.mem_filter]
      exact ⟨haD4, hia1⟩
    by_cases hia0 : (G.neighborFinset a ∩ Iso).card = 0
    · have hm3 : poor.card ≤ 3 := hpoor_of_zero a haD4 hia0
      have hible : (G.neighborFinset b ∩ Iso).card ≤ 2 := hnorich b hbHub hdb
      exact ⟨b, a, hbHub, hdb, hzb, by omega, hapoor, hza, by omega⟩
    · exact ⟨a, a, haHub, hda, hza, by omega, hapoor, hza, by omega⟩
  -- === The Z-slots and the M-end hub pairs. ===
  obtain ⟨z₁, z₂, _, hz1Z, hz2Z, _, _, hnohub⟩ :=
    zslot_skeleton_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg5 hT
  have hzf := zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
  obtain ⟨_, hz1hub2, _⟩ := hzf z₁ hz1Z
  obtain ⟨_, hz2hub2, _⟩ := hzf z₂ hz2Z
  have extract_pq : ∀ w : Fin 20, (G.neighborFinset w ∩ Hub).card = 2 → ¬ G.Adj r w →
      ∃ p q : Fin 20, p ∈ Hub ∧ q ∈ Hub ∧ G.degree p = 4 ∧ G.degree q = 4 ∧
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
  -- === Select the working M-end, its deg-4 hub pair, and the absorbed poor witness. ===
  obtain ⟨z, h₂, w, hzZ, hzhub2, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩ :
      ∃ z h₂ w : Fin 20, z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
        (G.neighborFinset z ∩ Hub).card = 2 ∧ h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧ G.Adj z h₂ ∧
        1 ≤ (G.neighborFinset h₂ ∩ Iso).card ∧ w ∈ poor ∧ G.Adj z w ∧
        (G.neighborFinset h₂ ∩ Iso).card + poor.card ≤ 5 := by
    by_cases hrz : G.Adj r z₁ ∨ G.Adj r z₂
    · -- === Trick (a): the deg-5 hub meets an M-end, so isoDeg r ≤ 4 and ∑_D4 isoDeg ≥ 17. ===
      obtain ⟨zn, zf, hznZ, hzfZ, hzfhub2, hrzn, hrzf⟩ :
          ∃ zn zf : Fin 20, zn ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
            zf ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
            (G.neighborFinset zf ∩ Hub).card = 2 ∧ G.Adj r zn ∧ ¬G.Adj r zf := by
        rcases hrz with h1 | h2
        · exact ⟨z₁, z₂, hz1Z, hz2Z, hz2hub2, h1, fun h => hnohub r hrHub ⟨h1, h⟩⟩
        · exact ⟨z₂, z₁, hz2Z, hz1Z, hz1hub2, h2, fun h => hnohub r hrHub ⟨h, h2⟩⟩
      have hsp := nbr_split_three_twenty G Hub Iso hdisj r
      have hznmem : zn ∈ G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso)) :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r zn).mpr hrzn, hznZ⟩
      have hzn1 : 1 ≤ (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
        Finset.card_pos.mpr ⟨zn, hznmem⟩
      have hisor4 : (G.neighborFinset r ∩ Iso).card ≤ 4 := by
        rw [hrdeg5] at hsp; omega
      have hD4ge17 : 17 ≤ ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by
        have h := hisosplit
        rw [hD5isosum] at h
        omega
      obtain ⟨p, q, hpHub, hqHub, hpdeg, hqdeg, hpqne, hzp, hzq⟩ :=
        extract_pq zf hzfhub2 hrzf
      have hpD4 : p ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hpHub, hpdeg⟩
      have hqD4 : q ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hqHub, hqdeg⟩
      obtain ⟨_, _, hpoor_or⟩ :=
        same_z_pair_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hT hC4
          hno2hub zf p q hzfZ hpHub hqHub hpdeg hqdeg hpqne hzp hzq
      have hqEp : q ∈ D4.erase p := Finset.mem_erase.mpr ⟨hpqne.symm, hqD4⟩
      have he1 : (G.neighborFinset p ∩ Iso).card
          + (∑ h ∈ D4.erase p, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) hpD4
      have he2 : (G.neighborFinset q ∩ Iso).card
          + (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4.erase p, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase (D4.erase p) (fun h => (G.neighborFinset h ∩ Iso).card) hqEp
      have hcard8 : ((D4.erase p).erase q).card = 8 := by
        rw [Finset.card_erase_of_mem hqEp, Finset.card_erase_of_mem hpD4, hD4card]
      have hrest : (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card) ≤ 16 := by
        have h := hcap_pair ((D4.erase p).erase q)
          ((Finset.erase_subset q (D4.erase p)).trans (Finset.erase_subset p D4))
        rw [hcard8] at h
        omega
      rcases hpoor_or with hp1 | hq1
      · obtain ⟨h₂, w, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩ :=
          hchoose zf p q hpHub hqHub hpdeg hqdeg hzp hzq hpD4 hp1 (by omega)
        exact ⟨zf, h₂, w, hzfZ, hzfhub2, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩
      · obtain ⟨h₂, w, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩ :=
          hchoose zf q p hqHub hpHub hqdeg hpdeg hzq hzp hqD4 hq1 (by omega)
        exact ⟨zf, h₂, w, hzfZ, hzfhub2, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩
    · -- === Trick (d): the deg-5 hub avoids both M-ends; the second end's poor hub sharpens
      -- the same-`z` iso lower bound at the first end. ===
      rw [not_or] at hrz
      obtain ⟨hnr1, hnr2⟩ := hrz
      obtain ⟨p, q, hpHub, hqHub, hpdeg, hqdeg, hpqne, hzp, hzq⟩ :=
        extract_pq z₁ hz1hub2 hnr1
      obtain ⟨p₂, q₂, hp₂Hub, hq₂Hub, hp₂deg, hq₂deg, hp₂q₂ne, hz₂p₂, hz₂q₂⟩ :=
        extract_pq z₂ hz2hub2 hnr2
      have hpD4 : p ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hpHub, hpdeg⟩
      have hqD4 : q ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hqHub, hqdeg⟩
      obtain ⟨_, _, hpoor_or⟩ :=
        same_z_pair_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hT hC4
          hno2hub z₁ p q hz1Z hpHub hqHub hpdeg hqdeg hpqne hzp hzq
      obtain ⟨_, _, hpoor_or₂⟩ :=
        same_z_pair_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hT hC4
          hno2hub z₂ p₂ q₂ hz2Z hp₂Hub hq₂Hub hp₂deg hq₂deg hp₂q₂ne hz₂p₂ hz₂q₂
      obtain ⟨a₂, ha₂Hub, ha₂deg, hz₂a₂, ha₂iso1⟩ :
          ∃ a₂ : Fin 20, a₂ ∈ Hub ∧ G.degree a₂ = 4 ∧ G.Adj z₂ a₂ ∧
            (G.neighborFinset a₂ ∩ Iso).card ≤ 1 := by
        rcases hpoor_or₂ with h | h
        · exact ⟨p₂, hp₂Hub, hp₂deg, hz₂p₂, h⟩
        · exact ⟨q₂, hq₂Hub, hq₂deg, hz₂q₂, h⟩
      have ha₂D4 : a₂ ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨ha₂Hub, ha₂deg⟩
      have ha₂p : a₂ ≠ p := by
        intro heq
        rw [heq] at hz₂a₂
        exact hnohub p hpHub ⟨hzp.symm, hz₂a₂.symm⟩
      have ha₂q : a₂ ≠ q := by
        intro heq
        rw [heq] at hz₂a₂
        exact hnohub q hqHub ⟨hzq.symm, hz₂a₂.symm⟩
      have hqEp : q ∈ D4.erase p := Finset.mem_erase.mpr ⟨hpqne.symm, hqD4⟩
      have ha₂mem : a₂ ∈ (D4.erase p).erase q :=
        Finset.mem_erase.mpr ⟨ha₂q, Finset.mem_erase.mpr ⟨ha₂p, ha₂D4⟩⟩
      have he1 : (G.neighborFinset p ∩ Iso).card
          + (∑ h ∈ D4.erase p, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) hpD4
      have he2 : (G.neighborFinset q ∩ Iso).card
          + (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4.erase p, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase (D4.erase p) (fun h => (G.neighborFinset h ∩ Iso).card) hqEp
      have he3 : (G.neighborFinset a₂ ∩ Iso).card
          + (∑ h ∈ ((D4.erase p).erase q).erase a₂, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase ((D4.erase p).erase q)
          (fun h => (G.neighborFinset h ∩ Iso).card) ha₂mem
      have hcard7 : (((D4.erase p).erase q).erase a₂).card = 7 := by
        rw [Finset.card_erase_of_mem ha₂mem, Finset.card_erase_of_mem hqEp,
          Finset.card_erase_of_mem hpD4, hD4card]
      have hrest : (∑ h ∈ ((D4.erase p).erase q).erase a₂,
          (G.neighborFinset h ∩ Iso).card) ≤ 14 := by
        have h := hcap_pair (((D4.erase p).erase q).erase a₂)
          ((Finset.erase_subset a₂ ((D4.erase p).erase q)).trans
            ((Finset.erase_subset q (D4.erase p)).trans (Finset.erase_subset p D4)))
        rw [hcard7] at h
        omega
      rcases hpoor_or with hp1 | hq1
      · obtain ⟨h₂, w, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩ :=
          hchoose z₁ p q hpHub hqHub hpdeg hqdeg hzp hzq hpD4 hp1 (by omega)
        exact ⟨z₁, h₂, w, hz1Z, hz1hub2, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩
      · obtain ⟨h₂, w, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩ :=
          hchoose z₁ q p hqHub hpHub hqdeg hpdeg hzq hzp hqD4 hq1 (by omega)
        exact ⟨z₁, h₂, w, hz1Z, hz1hub2, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩
  -- === The exclusion count: a fresh deg-4 hub avoiding z, h₂, h₂'s twins, and poor. ===
  have hzInterZ : z ∈ G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ z).mpr hzh₂.symm, hzZ⟩
  have hzDeg1 :
      1 ≤ (G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))).card :=
    Finset.card_pos.mpr ⟨z, hzInterZ⟩
  have hh₂iso2 : (G.neighborFinset h₂ ∩ Iso).card ≤ 2 := hnorich h₂ hh₂Hub hh₂deg
  have hhubDeg : (G.neighborFinset h₂ ∩ Hub).card ≤ 3 - (G.neighborFinset h₂ ∩ Iso).card := by
    have h := nbr_split_three_twenty G Hub Iso hdisj h₂
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
  set Q : Fin 20 → Prop := fun x => G.Adj x z ∨ G.Adj x h₂ ∨
      (G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso) ≠ ∅ ∨
      (G.neighborFinset x ∩ Iso).card ≤ 1 with hQdef
  have hbadsub : D4.filter Q ⊆
      G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub ∪
        (G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂) ∪
        poor.erase w := by
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
    · by_cases hxw : x = w
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨?_, hxHub⟩)))
        rw [G.mem_neighborFinset, hxw]
        exact hzw
      · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxw, ?_⟩)
        rw [hpoordef, Finset.mem_filter]
        exact ⟨hxD4, h4⟩
  have hwcard : (poor.erase w).card = poor.card - 1 := Finset.card_erase_of_mem hwpoor
  have hpoorpos : 1 ≤ poor.card := Finset.card_pos.mpr ⟨w, hwpoor⟩
  have hbadcard : (D4.filter Q).card ≤ 9 := by
    have hc := Finset.card_le_card hbadsub
    have hu1 := Finset.card_union_le
      (G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub ∪
        (G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂))
      (poor.erase w)
    have hu2 := Finset.card_union_le (G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub)
      ((G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂))
    have hu3 := Finset.card_union_le (G.neighborFinset z ∩ Hub) (G.neighborFinset h₂ ∩ Hub)
    omega
  have hcardsum : (D4.filter Q).card + (D4.filter (fun a => ¬ Q a)).card = 10 := by
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
  exact zleaf_pack_share0_twenty G Hub Iso hiso3 hisodeg3 x h₂ z hxHub hh₂Hub
    (hD4deg4 x hxD4) hh₂deg hzZ hxne hxnh₂ (by omega) hh₂iso1 hxshare hzh₂ hxnz

end N20

end ACMax
