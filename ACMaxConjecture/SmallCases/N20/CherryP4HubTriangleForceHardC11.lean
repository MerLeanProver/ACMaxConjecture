import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub

/-!
# `n = 20` dense-cherry `|D| = 9` (`11` hubs) ISO1 hard-`c` subcase

This file ports the `n = 19` `iso1_hard_c_subcase_nineteen` deficit-`0` kernel to the `n = 20`
`|Dᶜ| = 11` corner, where the `Iso`-incidence budget carries a **deficit `1`** (`∑ B = 16` vs
`∑ isoinc = 15`).  The single unit of slack lands on exactly one hub — `h₅` or one degree-`4`
hub (leaf-incident `A`-hub or cherry-free `F`-hub) — giving the three-way deficit taxonomy
`iso1_hardc11_deficit_h5` / `iso1_hardc11_deficit_A` / `iso1_hardc11_deficit_F`, dispatched by
`iso1_hard_c_subcase_eleven`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **`|D| = 9` ISO1 hard-`c` subcase, Case I — a low-internal-degree deg-`4` partner ⟹
`TwoHubConfig`.**  Verbatim port of `iso1_d9_caseI_twenty` (hub-count independent). -/
theorem iso1_d9_caseI_hardc11 (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (h₁ k : Fin 20)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hth : ¬TwoHubConfig G)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hh1d : G.degree h₁ = 4) (hh1iso : G.neighborFinset h₁ ∩ Dᶜ = ∅)
    (hindep : ∀ x ∈ G.neighborFinset h₁, ∀ y ∈ G.neighborFinset h₁, x ≠ y → ¬G.Adj x y)
    (hisoinc3 : 3 ≤ (G.neighborFinset h₁ ∩ Iso).card)
    (hkDc : k ∈ Dᶜ) (hkne : k ≠ h₁) (hkd : G.degree k = 4)
    (hkint : (G.neighborFinset k ∩ Dᶜ).card ≤ 1) :
    False := by
  classical
  have hN1subD : G.neighborFinset h₁ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [hh1iso] at hmem; exact absurd hmem (Finset.notMem_empty x)
  have hdeg3 : ∀ x ∈ G.neighborFinset h₁, G.degree x = 3 :=
    fun x hx => (hmemD x).mp (hN1subD hx)
  have hnadj1k : ¬G.Adj h₁ k := by
    intro ha
    have : k ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ k).mpr ha, hkDc⟩
    rw [hh1iso] at this; exact absurd this (Finset.notMem_empty k)
  have hshare := isolated_deg4_share_le_one G h₁ k hC4 hh1d hkd (Ne.symm hkne) hnadj1k hdeg3 hindep
  have hkD3 : 3 ≤ (G.neighborFinset k ∩ D).card := by
    have hdisj : Disjoint (G.neighborFinset k ∩ D) (G.neighborFinset k ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr; intro a ha hb
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
    have hunion : (G.neighborFinset k ∩ D) ∪ (G.neighborFinset k ∩ Dᶜ) = G.neighborFinset k := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have hsum : (G.neighborFinset k ∩ D).card + (G.neighborFinset k ∩ Dᶜ).card = G.degree k := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
    omega
  have hpriv_iso : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset k).card := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset k)
    have hsub : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset k
        ⊆ G.neighborFinset h₁ ∩ G.neighborFinset k := by
      intro x hx
      obtain ⟨hxNI, hxNk⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxNI).1, hxNk⟩
    have := Finset.card_le_card hsub
    omega
  have hpriv_leaf : 2 ≤ ((G.neighborFinset k ∩ D) \ G.neighborFinset h₁).card := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset k ∩ D) (G.neighborFinset h₁)
    have hsub : (G.neighborFinset k ∩ D) ∩ G.neighborFinset h₁
        ⊆ G.neighborFinset h₁ ∩ G.neighborFinset k := by
      intro x hx
      obtain ⟨hxND, hxN1⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hxN1, (Finset.mem_inter.mp hxND).1⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨a, haM, b, hbM, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset k).card)
  obtain ⟨haNI, haNk⟩ := Finset.mem_sdiff.mp haM
  obtain ⟨hbNI, hbNk⟩ := Finset.mem_sdiff.mp hbM
  obtain ⟨haN1, haI⟩ := Finset.mem_inter.mp haNI
  obtain ⟨hbN1, hbI⟩ := Finset.mem_inter.mp hbNI
  obtain ⟨c, hcM, d, hdM, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset k ∩ D) \ G.neighborFinset h₁).card)
  obtain ⟨hcND, hcN1⟩ := Finset.mem_sdiff.mp hcM
  obtain ⟨hdND, hdN1⟩ := Finset.mem_sdiff.mp hdM
  obtain ⟨hcNk, hcD⟩ := Finset.mem_inter.mp hcND
  obtain ⟨hdNk, hdD⟩ := Finset.mem_inter.mp hdND
  have hdega : G.degree a = 3 := (hIsoprop a haI).1
  have hdegb : G.degree b = 3 := (hIsoprop b hbI).1
  have hdegc : G.degree c = 3 := (hmemD c).mp hcD
  have hdegd : G.degree d = 3 := (hmemD d).mp hdD
  have hah1 : G.Adj a h₁ := ((G.mem_neighborFinset h₁ a).mp haN1).symm
  have hbh1 : G.Adj b h₁ := ((G.mem_neighborFinset h₁ b).mp hbN1).symm
  have hck : G.Adj c k := ((G.mem_neighborFinset k c).mp hcNk).symm
  have hdk : G.Adj d k := ((G.mem_neighborFinset k d).mp hdNk).symm
  have hn_h1c : ¬G.Adj h₁ c := fun ha => hcN1 ((G.mem_neighborFinset h₁ c).mpr ha)
  have hn_h1d : ¬G.Adj h₁ d := fun ha => hdN1 ((G.mem_neighborFinset h₁ d).mpr ha)
  have hn_ak : ¬G.Adj a k := fun ha => haNk ((G.mem_neighborFinset k a).mpr ha.symm)
  have hn_bk : ¬G.Adj b k := fun ha => hbNk ((G.mem_neighborFinset k b).mpr ha.symm)
  have hn_ac : ¬G.Adj a c := fun ha => (hIsoprop a haI).2 c ha hdegc
  have hn_ad : ¬G.Adj a d := fun ha => (hIsoprop a haI).2 d ha hdegd
  have hn_bc : ¬G.Adj b c := fun ha => (hIsoprop b hbI).2 c ha hdegc
  have hn_bd : ¬G.Adj b d := fun ha => (hIsoprop b hbI).2 d ha hdegd
  have hne_ac : a ≠ c := fun he => haNk (he ▸ hcNk)
  have hne_ad : a ≠ d := fun he => haNk (he ▸ hdNk)
  have hne_bc : b ≠ c := fun he => hbNk (he ▸ hcNk)
  have hne_bd : b ≠ d := fun he => hbNk (he ▸ hdNk)
  exact hth (two_hub_cherry_pair_twenty G h₁ k a b c d hh1d hkd hdega hdegb hdegc hdegd
    hah1 hbh1 hck hdk hnadj1k hn_h1c hn_h1d hn_ak hn_bk hn_ac hn_ad hn_bc hn_bd
    hab hcd hne_ac hne_ad hne_bc hne_bd)

/-- **Mantel for a `5`-element vertex set.**  A `5`-vertex subgraph carrying `≥ 13` internal
incidences (`> 12 = 2·⌊25/4⌋`) contains a triangle. -/
theorem five_edge_triangle (G : SimpleGraph (Fin 20)) (S : Finset (Fin 20))
    (hcard : S.card = 5) (hedge : 13 ≤ ∑ g ∈ S, (G.neighborFinset g ∩ S).card) :
    ∃ a b c : Fin 20, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  by_contra hno
  push Not at hno
  have hdisj : ∀ u v : Fin 20, u ∈ S → v ∈ S → G.Adj u v →
      Disjoint (G.neighborFinset u ∩ S) (G.neighborFinset v ∩ S) := by
    intro u v hu hv huv
    rw [Finset.disjoint_left]
    intro w hwu hwv
    obtain ⟨hwuN, hwS⟩ := Finset.mem_inter.mp hwu
    obtain ⟨hwvN, _⟩ := Finset.mem_inter.mp hwv
    exact hno u v w hu hv hwS huv ((G.mem_neighborFinset u w).mp hwuN)
      ((G.mem_neighborFinset v w).mp hwvN)
  have hedgebound : ∀ u v : Fin 20, u ∈ S → v ∈ S → G.Adj u v →
      (G.neighborFinset u ∩ S).card + (G.neighborFinset v ∩ S).card ≤ 5 := by
    intro u v hu hv huv
    have hun := Finset.card_union_of_disjoint (hdisj u v hu hv huv)
    calc (G.neighborFinset u ∩ S).card + (G.neighborFinset v ∩ S).card
        = ((G.neighborFinset u ∩ S) ∪ (G.neighborFinset v ∩ S)).card := hun.symm
      _ ≤ S.card :=
          Finset.card_le_card (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
      _ = 5 := hcard
  have hex : ∃ a ∈ S, 3 ≤ (G.neighborFinset a ∩ S).card := by
    by_contra hc
    push Not at hc
    have hle : ∑ g ∈ S, (G.neighborFinset g ∩ S).card ≤ ∑ _g ∈ S, 2 :=
      Finset.sum_le_sum (fun g hg => by have := hc g hg; omega)
    rw [Finset.sum_const, hcard, smul_eq_mul] at hle; omega
  obtain ⟨a, haS, had⟩ := hex
  set Na := G.neighborFinset a ∩ S with hNadef
  have hNaS : Na ⊆ S := Finset.inter_subset_right
  have haNa : a ∉ Na := fun h => G.irrefl ((G.mem_neighborFinset a a).mp (Finset.mem_inter.mp h).1)
  have hbNa : ∀ v ∈ Na, (G.neighborFinset v ∩ S).card ≤ 5 - (G.neighborFinset a ∩ S).card := by
    intro v hv
    obtain ⟨hvN, hvS⟩ := Finset.mem_inter.mp hv
    have hav : G.Adj a v := (G.mem_neighborFinset a v).mp hvN
    have := hedgebound a v haS hvS hav; omega
  have hbRest : ∀ w ∈ S \ insert a Na, (G.neighborFinset w ∩ S).card ≤ 3 := by
    intro w hw
    obtain ⟨hwS, hwni⟩ := Finset.mem_sdiff.mp hw
    have hwa : w ≠ a := fun he => hwni (by rw [he]; exact Finset.mem_insert_self a Na)
    have hnwa : ¬G.Adj a w := fun h =>
      hwni (Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a w).mpr h, hwS⟩))
    have hsub : G.neighborFinset w ∩ S ⊆ S \ {a, w} := by
      intro x hx
      obtain ⟨hxN, hxS⟩ := Finset.mem_inter.mp hx
      have hadj := (G.mem_neighborFinset w x).mp hxN
      refine Finset.mem_sdiff.mpr ⟨hxS, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨fun he => hnwa (he ▸ hadj.symm), fun he => G.irrefl (he ▸ hadj)⟩
    have haw2 : ({a, w} : Finset (Fin 20)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hwa]), Finset.card_singleton]
    have hawS : ({a, w} : Finset (Fin 20)) ⊆ S := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl; exacts [haS, hwS]
    have hc : (S \ {a, w}).card = 3 := by
      rw [Finset.card_sdiff_of_subset hawS, hcard, haw2]
    calc (G.neighborFinset w ∩ S).card ≤ (S \ {a, w}).card := Finset.card_le_card hsub
      _ = 3 := hc
  have hins : insert a Na ⊆ S := Finset.insert_subset haS hNaS
  have hsplit : ∑ g ∈ S \ insert a Na, (G.neighborFinset g ∩ S).card
      + ∑ g ∈ insert a Na, (G.neighborFinset g ∩ S).card
      = ∑ g ∈ S, (G.neighborFinset g ∩ S).card := Finset.sum_sdiff hins
  have hins2 : ∑ g ∈ insert a Na, (G.neighborFinset g ∩ S).card
      = (G.neighborFinset a ∩ S).card + ∑ g ∈ Na, (G.neighborFinset g ∩ S).card := by
    rw [Finset.sum_insert haNa]
  have hNacard : Na.card = (G.neighborFinset a ∩ S).card := rfl
  have hsumNa : ∑ g ∈ Na, (G.neighborFinset g ∩ S).card
      ≤ Na.card * (5 - (G.neighborFinset a ∩ S).card) := by
    calc ∑ g ∈ Na, (G.neighborFinset g ∩ S).card
        ≤ ∑ _g ∈ Na, (5 - (G.neighborFinset a ∩ S).card) := Finset.sum_le_sum hbNa
      _ = Na.card * (5 - (G.neighborFinset a ∩ S).card) := by rw [Finset.sum_const, smul_eq_mul]
  have hsumRest : ∑ g ∈ S \ insert a Na, (G.neighborFinset g ∩ S).card
      ≤ (S \ insert a Na).card * 3 := by
    calc ∑ g ∈ S \ insert a Na, (G.neighborFinset g ∩ S).card
        ≤ ∑ _g ∈ S \ insert a Na, 3 := Finset.sum_le_sum hbRest
      _ = (S \ insert a Na).card * 3 := by rw [Finset.sum_const, smul_eq_mul]
  have hinscard : (insert a Na).card = 1 + (G.neighborFinset a ∩ S).card := by
    rw [Finset.card_insert_of_notMem haNa, hNacard]; omega
  have hrestcard : (S \ insert a Na).card = 5 - (1 + (G.neighborFinset a ∩ S).card) := by
    rw [Finset.card_sdiff_of_subset hins, hcard, hinscard]
  have had4 : (G.neighborFinset a ∩ S).card ≤ 4 := by
    have : G.neighborFinset a ∩ S ⊆ S.erase a := by
      intro x hx
      obtain ⟨hxN, hxS⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_erase.mpr ⟨fun he => G.irrefl (he ▸ (G.mem_neighborFinset a x).mp hxN), hxS⟩
    have := Finset.card_le_card this
    rwa [Finset.card_erase_of_mem haS, hcard] at this
  set dd := (G.neighborFinset a ∩ S).card with hdddef
  rw [hNacard] at hsumNa
  rw [hrestcard] at hsumRest
  interval_cases dd <;> omega

set_option maxHeartbeats 2000000 in
/-- **`|D| = 9` (`11` hubs) ISO1 hard-`c` subcase (deficit `1`).**

The `|Dᶜ| = 11` port of `iso1_hard_c_subcase_twenty`: the `Iso`-budget caps sum to
`3 + 4 + 9 = 16` against `∑ isoinc = 15`, a deficit of `1`.  The slack lands on exactly one hub:
`h₅` (`deficit_h5`), a leaf-incident degree-`4` `A`-hub (`deficit_A`), or a cherry-free degree-`4`
`F`-hub (`deficit_F`). -/
theorem iso1_hard_c_subcase_eleven (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ h₁ h₅ : Fin 20)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hclassP : ∀ x : Fin 20, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) (hsv : ¬SingleVertexConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hHub11 : Dᶜ.card = 11) (hIsocard : Iso.card = 5)
    (hdeg5 : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h ≤ 5)
    (hper : ∀ h : Fin 20, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card = 6)
    (hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hh1Dc : h₁ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh1iso : G.neighborFinset h₁ ∩ Dᶜ = ∅)
    (hRc1 : G.Adj h₁ c₁) (hcinc1 : (G.neighborFinset h₁ ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card ≤ 1)
    (hh5Dc : h₅ ∈ Dᶜ) (hh5d : G.degree h₅ = 5) (hh5int0 : G.neighborFinset h₅ ∩ Dᶜ = ∅)
    (hne15 : h₁ ≠ h₅)
    (hdegOth : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → G.degree h = 4)
    (hntri1 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13) :
    False := by
  classical
  set P : Finset (Fin 20) := {L₁, c₁, c₂, L₂} with hPdef
  have hIso_nadj : ∀ t : Fin 20, t ∈ Iso → ∀ w : Fin 20, G.degree w = 3 → ¬G.Adj t w :=
    fun t ht w hw hadj => (hIsoprop t ht).2 w hadj hw
  have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
  have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
  have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
  have hL2nIso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm hc2deg
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
      G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
  have hnc1L2 : ¬G.Adj c₁ L₂ := by
    intro hadj
    have hmem : L₂ ∈ G.neighborFinset c₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ L₂).mpr hadj, hL2D⟩
    rw [hNc1D] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (G.ne_of_adj hac2L2) h.symm
    · exact hL1L2 h.symm
  have hnc2L1 : ¬G.Adj c₂ L₁ := by
    intro hadj
    have hmem : L₁ ∈ G.neighborFinset c₂ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ L₁).mpr hadj, hL1D⟩
    rw [hNc2D] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (G.ne_of_adj hac1L1) h.symm
    · exact hL1L2 h
  have hPnotIso : ∀ x : Fin 20, x ∈ P → x ∉ Iso := by
    intro x hx
    simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hL1nIso
    · exact hc1nIso
    · exact hc2nIso
    · exact hL2nIso
  have hN1subD : G.neighborFinset h₁ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [hh1iso] at hmem; exact absurd hmem (Finset.notMem_empty x)
  have hdeg3N1 : ∀ x : Fin 20, x ∈ G.neighborFinset h₁ → G.degree x = 3 :=
    fun x hx => (hmemD x).mp (hN1subD hx)
  have hc1N1 : c₁ ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ c₁).mpr hRc1
  have hcinc1' : (G.neighborFinset h₁ ∩ P).card = 1 := by
    have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
      Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
    have hpos : 1 ≤ (G.neighborFinset h₁ ∩ P).card := Finset.card_pos.mpr ⟨c₁, hc1mem⟩
    omega
  have hh1int0 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by rw [hh1iso]; exact Finset.card_empty
  have hisoinc3 : (G.neighborFinset h₁ ∩ Iso).card = 3 := by
    have := hper h₁ hh1Dc
    rw [hcinc1', hh1int0, hh1d] at this; omega
  have hN1char : ∀ x : Fin 20, x ∈ G.neighborFinset h₁ → x = c₁ ∨ x ∈ Iso := by
    intro x hx
    have hadj : G.Adj h₁ x := (G.mem_neighborFinset h₁ x).mp hx
    rcases hclassP x (hN1subD hx) with h | h | h | h | h
    · exfalso
      have hL1mem : L₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hsub : ({c₁, L₁} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hL1mem
      have hcard2 : ({c₁, L₁} : Finset (Fin 20)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hac1L1]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · exact Or.inl h
    · exfalso
      have hmem : c₂ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hsub : ({c₁, c₂} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hmem
      have hcard2 : ({c₁, c₂} : Finset (Fin 20)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hc12]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · exfalso
      have hmem : L₂ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hne : c₁ ≠ L₂ := Ne.symm hL2nc1
      have hsub : ({c₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hmem
      have hcard2 : ({c₁, L₂} : Finset (Fin 20)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · exact Or.inr h
  have hindep1 : ∀ x ∈ G.neighborFinset h₁, ∀ y ∈ G.neighborFinset h₁, x ≠ y → ¬G.Adj x y := by
    intro x hx y hy hxy hadj
    rcases hN1char x hx with hxc | hxI
    · rcases hN1char y hy with hyc | hyI
      · exact hxy (hxc.trans hyc.symm)
      · exact hIso_nadj y hyI x (hxc ▸ hc1deg) hadj.symm
    · exact hIso_nadj x hxI y (hdeg3N1 y hy) hadj
  have hnadj1hub : ∀ k : Fin 20, k ∈ Dᶜ → ¬G.Adj h₁ k := by
    intro k hk hadj
    have : k ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ k).mpr hadj, hk⟩
    rw [hh1iso] at this; exact absurd this (Finset.notMem_empty k)
  -- **Case I dichotomy.**
  by_cases hCaseI : ∃ k : Fin 20, k ∈ Dᶜ ∧ k ≠ h₁ ∧ G.degree k = 4
      ∧ (G.neighborFinset k ∩ Dᶜ).card ≤ 1
  · obtain ⟨k, hkDc, hkne, hkd, hkint⟩ := hCaseI
    exact iso1_d9_caseI_hardc11 G D Iso h₁ k hmemD hIsoprop hth hC4 hh1d hh1iso hindep1
      (by rw [hisoinc3]) hkDc hkne hkd hkint
  · -- **Case II.**  Every degree-`4` hub `≠ h₁` has internal degree `≥ 2`.
    push Not at hCaseI
    have hCaseII : ∀ k : Fin 20, k ∈ Dᶜ → k ≠ h₁ → G.degree k = 4 →
        2 ≤ (G.neighborFinset k ∩ Dᶜ).card := by
      intro k hkDc hkne hkd
      have := hCaseI k hkDc hkne hkd; omega
    have hubD_ne : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ L₁ ∧ h ≠ c₁ ∧ h ≠ c₂ ∧ h ≠ L₂ := by
      intro h hh
      have hhD : h ∉ D := Finset.mem_compl.mp hh
      exact ⟨fun he => hhD (he ▸ hL1D), fun he => hhD (he ▸ hc1D),
        fun he => hhD (he ▸ hc2D), fun he => hhD (he ▸ hL2D)⟩
    have hNoTT : ∀ h : Fin 20, h ∈ Dᶜ → (G.neighborFinset h ∩ P).card = 0 →
        (G.neighborFinset h ∩ Iso).card ≤ 1 := by
      intro h hh hcinc0
      by_contra hgt
      push Not at hgt
      have hPempty : G.neighborFinset h ∩ P = ∅ := Finset.card_eq_zero.mp hcinc0
      have hnadjP : ∀ w : Fin 20, w ∈ P → ¬G.Adj h w := by
        intro w hw hadj
        have : w ∈ G.neighborFinset h ∩ P :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h w).mpr hadj, hw⟩
        rw [hPempty] at this; exact absurd this (Finset.notMem_empty w)
      obtain ⟨hnL1, hnc1, hnc2, hnL2⟩ := hubD_ne h hh
      exact htt (twotwin_of_centre_twenty G Iso h L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
        (hdeg5 h hh) hac1L1.symm hc12
        (hnadjP L₁ (by simp [hPdef])) (hnadjP c₁ (by simp [hPdef])) (hnadjP c₂ (by simp [hPdef]))
        hL1nIso hc1nIso hc2nIso hnL1 hnc1 hnc2
        (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2 (by omega))
    set B : Fin 20 → ℕ := fun h => if h = h₁ then 3 else if h = h₅ then 4 else 1 with hBdef
    have hbound : ∀ h : Fin 20, h ∈ Dᶜ → (G.neighborFinset h ∩ Iso).card ≤ B h := by
      intro h hh
      have hdec := hper h hh
      by_cases hh1 : h = h₁
      · have hBh : B h = 3 := by simp only [hBdef, if_pos hh1]
        rw [hBh, hh1]; omega
      · by_cases hh5 : h = h₅
        · have hBh : B h = 4 := by simp only [hBdef, if_neg hh1, if_pos hh5]
          rw [hBh]
          have hdh : G.degree h = 5 := by rw [hh5]; exact hh5d
          rw [hdh] at hdec
          by_cases hc0 : (G.neighborFinset h ∩ P).card = 0
          · have := hNoTT h hh hc0; omega
          · omega
        · have hBh : B h = 1 := by simp only [hBdef, if_neg hh1, if_neg hh5]
          rw [hBh]
          have hd4 := hdegOth h hh hh1 hh5
          rw [hd4] at hdec
          have hint2 := hCaseII h hh hh1 hd4
          by_cases hc0 : (G.neighborFinset h ∩ P).card = 0
          · have := hNoTT h hh hc0; omega
          · omega
    have hsumB : ∑ h ∈ Dᶜ, B h = 16 := by
      have hpt : ∀ h, B h = 1 + ((if h = h₁ then 2 else 0) + (if h = h₅ then 3 else 0)) := by
        intro h
        by_cases hh1 : h = h₁
        · subst hh1; simp [hBdef, hne15]
        · by_cases hh5 : h = h₅
          · subst hh5; simp [hBdef, hh1]
          · simp [hBdef, hh1, hh5]
      simp only [hpt, Finset.sum_add_distrib, Finset.sum_const, hHub11, smul_eq_mul,
        Finset.sum_ite_eq' Dᶜ h₁ (fun _ => (2 : ℕ)),
        Finset.sum_ite_eq' Dᶜ h₅ (fun _ => (3 : ℕ)), hh1Dc, hh5Dc, if_pos]
      omega
    -- **Deficit taxonomy.**  `∑ (B - isoinc) = 1`, so at most one hub is below its cap.
    have hdsum : ∑ h ∈ Dᶜ, (B h - (G.neighborFinset h ∩ Iso).card) = 1 := by
      have hsplit : ∑ h ∈ Dᶜ, ((G.neighborFinset h ∩ Iso).card
          + (B h - (G.neighborFinset h ∩ Iso).card)) = ∑ h ∈ Dᶜ, B h :=
        Finset.sum_congr rfl (fun h hh => Nat.add_sub_cancel' (hbound h hh))
      rw [Finset.sum_add_distrib, hsumIso15, hsumB] at hsplit
      omega
    have hdle : ∀ S : Finset (Fin 20), S ⊆ Dᶜ →
        ∑ h ∈ S, (B h - (G.neighborFinset h ∩ Iso).card) ≤ 1 := by
      intro S hS
      calc ∑ h ∈ S, (B h - (G.neighborFinset h ∩ Iso).card)
          ≤ ∑ h ∈ Dᶜ, (B h - (G.neighborFinset h ∩ Iso).card) :=
            Finset.sum_le_sum_of_subset hS
        _ = 1 := hdsum
    have hd1 : ∀ x : Fin 20, x ∈ Dᶜ → B x - (G.neighborFinset x ∩ Iso).card ≤ 1 := by
      intro x hx
      have := hdle {x} (Finset.singleton_subset_iff.mpr hx)
      rwa [Finset.sum_singleton] at this
    have hd2 : ∀ x y : Fin 20, x ∈ Dᶜ → y ∈ Dᶜ → x ≠ y →
        (B x - (G.neighborFinset x ∩ Iso).card) + (B y - (G.neighborFinset y ∩ Iso).card) ≤ 1 := by
      intro x y hx hy hxy
      have hsub : ({x, y} : Finset (Fin 20)) ⊆ Dᶜ := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl; exacts [hx, hy]
      have := hdle {x, y} hsub
      rwa [Finset.sum_pair hxy] at this
    have hBh1 : B h₁ = 3 := by simp only [hBdef, if_pos rfl]
    have hBh5 : B h₅ = 4 := by simp [hBdef, Ne.symm hne15]
    have hd1h1 : B h₁ - (G.neighborFinset h₁ ∩ Iso).card = 0 := by rw [hBh1, hisoinc3]
    have hh5le : (G.neighborFinset h₅ ∩ Iso).card ≤ 4 := hBh5 ▸ hbound h₅ hh5Dc
    have hh5ge3 : 3 ≤ (G.neighborFinset h₅ ∩ Iso).card := by
      have := hd1 h₅ hh5Dc; rw [hBh5] at this; omega
    -- `h₅` internal degree `0` and `cinc h₅ = 5 - isoinc`.
    have hh5int0c : (G.neighborFinset h₅ ∩ Dᶜ).card = 0 := by
      rw [hh5int0]; exact Finset.card_empty
    have hOthiso1cap : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ →
        B h - (G.neighborFinset h ∩ Iso).card = 0 → (G.neighborFinset h ∩ Iso).card = 1 := by
      intro h hh hh1 hh5 hcap
      have hBh : B h = 1 := by simp only [hBdef, if_neg hh1, if_neg hh5]
      have hle := hbound h hh
      rw [hBh] at hcap hle
      omega
    by_cases hh5cap : (G.neighborFinset h₅ ∩ Iso).card = 4
    · -- **Case A: `h₅` at cap.**  The deficit is on a degree-`4` hub `h*` (`isoinc 0`).
      have hd1h5 : B h₅ - (G.neighborFinset h₅ ∩ Iso).card = 0 := by rw [hBh5, hh5cap]
      -- All degree-`4` hubs except one are at cap; extract the deficit hub.
      have hexists : ∃ h ∈ Dᶜ, 1 ≤ B h - (G.neighborFinset h ∩ Iso).card := by
        by_contra hnone
        push Not at hnone
        have hz : ∑ h ∈ Dᶜ, (B h - (G.neighborFinset h ∩ Iso).card) = 0 :=
          Finset.sum_eq_zero (fun h hh => by have := hnone h hh; omega)
        rw [hz] at hdsum; exact absurd hdsum (by norm_num)
      obtain ⟨hs, hsDc, hsdef⟩ := hexists
      have hs1 : hs ≠ h₁ := by intro he; rw [he] at hsdef; omega
      have hs5 : hs ≠ h₅ := by intro he; rw [he] at hsdef; omega
      have hsd4 : G.degree hs = 4 := hdegOth hs hsDc hs1 hs5
      have hBhs : B hs = 1 := by simp only [hBdef, if_neg hs1, if_neg hs5]
      have hsiso0 : (G.neighborFinset hs ∩ Iso).card = 0 := by
        rw [hBhs] at hsdef; omega
      -- Every OTHER degree-`4` hub is at cap (`isoinc 1`).
      have hOthcap : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → h ≠ hs →
          (G.neighborFinset h ∩ Iso).card = 1 := by
        intro h hh hh1 hh5 hhs
        have hpair := hd2 hs h hsDc hh (Ne.symm hhs)
        rw [hBhs, hsiso0] at hpair
        exact hOthiso1cap h hh hh1 hh5 (by omega)
      by_cases hsleaf : (G.neighborFinset hs ∩ P).card = 0
      · -- **`F`-hub deficit.**  `h₅` at cap, `4` clean `A`-hubs, `5` `F`-hubs (`hs` at `int 4`).
        have hh5iso4 : (G.neighborFinset h₅ ∩ Iso).card = 4 := hh5cap
        have hh5cinc1 : (G.neighborFinset h₅ ∩ P).card = 1 := by
          have hdec := hper h₅ hh5Dc
          rw [hh5iso4, hh5int0c, hh5d] at hdec; omega
        obtain ⟨w5, hw5eq⟩ := Finset.card_eq_one.mp hh5cinc1
        have hw5mem : w5 ∈ G.neighborFinset h₅ ∩ P := by rw [hw5eq]; exact Finset.mem_singleton_self w5
        have hh5w5 : G.Adj h₅ w5 := (G.mem_neighborFinset h₅ w5).mp (Finset.mem_inter.mp hw5mem).1
        have hw5P : w5 ∈ P := (Finset.mem_inter.mp hw5mem).2
        have hh5only : ∀ x : Fin 20, x ∈ P → G.Adj h₅ x → x = w5 := by
          intro x hxP hadj
          have : x ∈ G.neighborFinset h₅ ∩ P :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ x).mpr hadj, hxP⟩
          rw [hw5eq] at this; exact Finset.mem_singleton.mp this
        have hNc1Dc : G.neighborFinset c₁ ∩ Dᶜ = {h₁} := by
          have h1mem : h₁ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₁).mpr hRc1.symm, hh1Dc⟩
          exact (Finset.eq_of_subset_of_card_le
            (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ h1mem)
            (by rw [hc1hub, Finset.card_singleton])).symm
        have hn_h5c1 : ¬G.Adj h₅ c₁ := by
          intro hadj
          have : h₅ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₅).mpr hadj.symm, hh5Dc⟩
          rw [hNc1Dc, Finset.mem_singleton] at this; exact hne15 this.symm
        have hRc2 : G.Adj h₅ c₂ := by
          simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hw5P
          rcases hw5P with rfl | rfl | rfl | rfl
          · exfalso
            have hn_c1 : ¬G.Adj h₅ c₁ := fun ha => (G.ne_of_adj hac1L1) (hh5only c₁ (by simp [hPdef]) ha)
            have hn_c2 : ¬G.Adj h₅ c₂ := fun ha => (Ne.symm hL1nc2) (hh5only c₂ (by simp [hPdef]) ha)
            have hn_L2 : ¬G.Adj h₅ L₂ := fun ha => hL1L2 (hh5only L₂ (by simp [hPdef]) ha).symm
            obtain ⟨_, hne5c1, hne5c2, hne5L2⟩ := hubD_ne h₅ hh5Dc
            exact htt (twotwin_of_centre_twenty G Iso h₅ c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
              (hdeg5 h₅ hh5Dc) hc12 hac2L2 hn_c1 hn_c2 hn_L2 hc1nIso hc2nIso hL2nIso
              hne5c1 hne5c2 hne5L2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) (Ne.symm hL2nc1)
              (by rw [hh5iso4]; norm_num))
          · exact absurd hh5w5 hn_h5c1
          · exact hh5w5
          · exfalso
            have hn_L1 : ¬G.Adj h₅ L₁ := fun ha => hL1L2 (hh5only L₁ (by simp [hPdef]) ha)
            have hn_c1 : ¬G.Adj h₅ c₁ := fun ha => (Ne.symm hL2nc1) (hh5only c₁ (by simp [hPdef]) ha)
            have hn_c2 : ¬G.Adj h₅ c₂ := fun ha => (G.ne_of_adj hac2L2) (hh5only c₂ (by simp [hPdef]) ha)
            obtain ⟨hne5L1, hne5c1, hne5c2, _⟩ := hubD_ne h₅ hh5Dc
            exact htt (twotwin_of_centre_twenty G Iso h₅ L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
              (hdeg5 h₅ hh5Dc) hac1L1.symm hc12 hn_L1 hn_c1 hn_c2 hL1nIso hc1nIso hc2nIso
              hne5L1 hne5c1 hne5c2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2
              (by rw [hh5iso4]; norm_num))
        have hNc2Dc : G.neighborFinset c₂ ∩ Dᶜ = {h₅} := by
          have h5mem : h₅ ∈ G.neighborFinset c₂ ∩ Dᶜ :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ h₅).mpr hRc2.symm, hh5Dc⟩
          exact (Finset.eq_of_subset_of_card_le
            (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ h5mem)
            (by rw [hc2hub, Finset.card_singleton])).symm
        have hnL1L2 : ¬G.Adj L₁ L₂ := by
          intro hadj
          have hdisj : Disjoint (G.neighborFinset L₁ ∩ D) (G.neighborFinset L₁ ∩ Dᶜ) := by
            apply Finset.disjoint_left.mpr; intro a ha hb
            exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
          have hunion : (G.neighborFinset L₁ ∩ D) ∪ (G.neighborFinset L₁ ∩ Dᶜ) = G.neighborFinset L₁ := by
            rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
          have hsplit : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset L₁ ∩ Dᶜ).card = G.degree L₁ := by
            rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
          rw [hL1deg, hL1hub] at hsplit
          have hone : (G.neighborFinset L₁ ∩ D).card = 1 := by omega
          have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩
          have hL2mem : L₂ ∈ G.neighborFinset L₁ ∩ D :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ L₂).mpr hadj, hL2D⟩
          have hsub : ({c₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset L₁ ∩ D := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hc1mem
            · exact hL2mem
          have hcard2 : ({c₁, L₂} : Finset (Fin 20)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [Ne.symm hL2nc1]), Finset.card_singleton]
          have := Finset.card_le_card hsub; rw [hcard2, hone] at this; omega
        have hNh1P : G.neighborFinset h₁ ∩ P = {c₁} := by
          have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P := Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
          exact (Finset.eq_of_subset_of_card_le
            (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hc1mem)
            (by rw [hcinc1', Finset.card_singleton])).symm
        have hNh5P : G.neighborFinset h₅ ∩ P = {c₂} := by
          have hc2mem : c₂ ∈ G.neighborFinset h₅ ∩ P :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ c₂).mpr hRc2, by simp [hPdef]⟩
          exact (Finset.eq_of_subset_of_card_le
            (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hc2mem)
            (by rw [hh5cinc1, Finset.card_singleton])).symm
        -- `A`-hub structure (leaf-incident hubs are clean, `≠ hs`).
        have leafhub : ∀ a Lf : Fin 20, Lf ∈ P → Lf ≠ c₁ → Lf ≠ c₂ →
            a ∈ G.neighborFinset Lf ∩ Dᶜ →
            a ≠ h₁ ∧ a ≠ h₅ ∧ G.degree a = 4 ∧ (G.neighborFinset a ∩ Dᶜ).card = 2 ∧
            G.neighborFinset a ∩ P = {Lf} ∧ (∃ ι : Fin 20, ι ∈ Iso ∧ G.Adj a ι ∧
              G.neighborFinset a ∩ Iso = {ι}) := by
          intro a Lf hLfP hLfc1 hLfc2 ha
          obtain ⟨haN, haDc⟩ := Finset.mem_inter.mp ha
          have haLf : G.Adj a Lf := ((G.mem_neighborFinset Lf a).mp haN).symm
          have hLfmem : Lf ∈ G.neighborFinset a ∩ P :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a Lf).mpr haLf, hLfP⟩
          have ha1 : a ≠ h₁ := by
            intro he; subst he
            have : Lf ∈ G.neighborFinset a ∩ P := hLfmem
            rw [hNh1P, Finset.mem_singleton] at this; exact hLfc1 this
          have ha5 : a ≠ h₅ := by
            intro he; subst he
            have : Lf ∈ G.neighborFinset a ∩ P := hLfmem
            rw [hNh5P, Finset.mem_singleton] at this; exact hLfc2 this
          have hcincpos : 1 ≤ (G.neighborFinset a ∩ P).card := Finset.card_pos.mpr ⟨Lf, hLfmem⟩
          have has : a ≠ hs := by
            intro he; rw [he, hsleaf] at hcincpos; omega
          have hd4 := hdegOth a haDc ha1 ha5
          have hiso1 := hOthcap a haDc ha1 ha5 has
          have hint2 := hCaseII a haDc ha1 hd4
          have hdec := hper a haDc
          rw [hiso1, hd4] at hdec
          have hcinc1a : (G.neighborFinset a ∩ P).card = 1 := by omega
          have hint2a : (G.neighborFinset a ∩ Dᶜ).card = 2 := by omega
          have hNaP : G.neighborFinset a ∩ P = {Lf} :=
            (Finset.eq_of_subset_of_card_le
              (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hLfmem)
              (by rw [hcinc1a, Finset.card_singleton])).symm
          obtain ⟨ι, hιeq⟩ := Finset.card_eq_one.mp hiso1
          have hιmem : ι ∈ G.neighborFinset a ∩ Iso := by rw [hιeq]; exact Finset.mem_singleton_self ι
          obtain ⟨hιN, hιIso⟩ := Finset.mem_inter.mp hιmem
          exact ⟨ha1, ha5, hd4, hint2a, hNaP, ι, hιIso, (G.mem_neighborFinset a ι).mp hιN, hιeq⟩
        have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
        have hL1P : L₁ ∈ P := by simp [hPdef]
        have hL2P : L₂ ∈ P := by simp [hPdef]
        obtain ⟨a1, a2, ha12, haLeq⟩ := Finset.card_eq_two.mp hL1hub
        obtain ⟨b1, b2, hb12, haReq⟩ := Finset.card_eq_two.mp hL2hub
        have hL2c1 : L₂ ≠ c₁ := hL2nc1
        have hL2c2 : L₂ ≠ c₂ := (G.ne_of_adj hac2L2).symm
        have ha1mem : a1 ∈ G.neighborFinset L₁ ∩ Dᶜ := by rw [haLeq]; simp
        have ha2mem : a2 ∈ G.neighborFinset L₁ ∩ Dᶜ := by rw [haLeq]; simp
        have hb1mem : b1 ∈ G.neighborFinset L₂ ∩ Dᶜ := by rw [haReq]; simp
        have hb2mem : b2 ∈ G.neighborFinset L₂ ∩ Dᶜ := by rw [haReq]; simp
        obtain ⟨ha1_1, ha1_5, ha1d, ha1int, ha1NP, ιa1, hιa1I, ha1ι, ha1isoeq⟩ :=
          leafhub a1 L₁ hL1P hL1c1 hL1nc2 ha1mem
        obtain ⟨ha2_1, ha2_5, ha2d, ha2int, ha2NP, ιa2, hιa2I, ha2ι, ha2isoeq⟩ :=
          leafhub a2 L₁ hL1P hL1c1 hL1nc2 ha2mem
        obtain ⟨hb1_1, hb1_5, hb1d, hb1int, hb1NP, ιb1, hιb1I, hb1ι, hb1isoeq⟩ :=
          leafhub b1 L₂ hL2P hL2c1 hL2c2 hb1mem
        obtain ⟨hb2_1, hb2_5, hb2d, hb2int, hb2NP, ιb2, hιb2I, hb2ι, hb2isoeq⟩ :=
          leafhub b2 L₂ hL2P hL2c1 hL2c2 hb2mem
        have ha1Dc : a1 ∈ Dᶜ := (Finset.mem_inter.mp ha1mem).2
        have ha2Dc : a2 ∈ Dᶜ := (Finset.mem_inter.mp ha2mem).2
        have hb1Dc : b1 ∈ Dᶜ := (Finset.mem_inter.mp hb1mem).2
        have hb2Dc : b2 ∈ Dᶜ := (Finset.mem_inter.mp hb2mem).2
        have ha1L1 : G.Adj a1 L₁ := ((G.mem_neighborFinset L₁ a1).mp (Finset.mem_inter.mp ha1mem).1).symm
        have ha2L1 : G.Adj a2 L₁ := ((G.mem_neighborFinset L₁ a2).mp (Finset.mem_inter.mp ha2mem).1).symm
        have hb1L2 : G.Adj b1 L₂ := ((G.mem_neighborFinset L₂ b1).mp (Finset.mem_inter.mp hb1mem).1).symm
        have hb2L2 : G.Adj b2 L₂ := ((G.mem_neighborFinset L₂ b2).mp (Finset.mem_inter.mp hb2mem).1).symm
        have notP : ∀ a Lf : Fin 20, G.neighborFinset a ∩ P = {Lf} →
            ∀ x : Fin 20, x ∈ P → x ≠ Lf → ¬G.Adj a x := by
          intro a Lf hNaP x hxP hxne hadj
          have : x ∈ G.neighborFinset a ∩ P :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a x).mpr hadj, hxP⟩
          rw [hNaP, Finset.mem_singleton] at this; exact hxne this
        have notIso : ∀ a ι : Fin 20, G.neighborFinset a ∩ Iso = {ι} →
            ∀ t : Fin 20, t ∈ Iso → t ≠ ι → ¬G.Adj a t := by
          intro a ι hNaI t htI htne hadj
          have : t ∈ G.neighborFinset a ∩ Iso :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a t).mpr hadj, htI⟩
          rw [hNaI, Finset.mem_singleton] at this; exact htne this
        have crossTwoHub : ∀ a b ιa ιb : Fin 20,
            G.degree a = 4 → G.degree b = 4 →
            G.Adj a L₁ → G.Adj b L₂ → G.neighborFinset a ∩ P = {L₁} → G.neighborFinset b ∩ P = {L₂} →
            ιa ∈ Iso → ιb ∈ Iso → G.Adj a ιa → G.Adj b ιb →
            G.neighborFinset a ∩ Iso = {ιa} → G.neighborFinset b ∩ Iso = {ιb} →
            ¬G.Adj a b → ιa ≠ ιb → False := by
          intro a b ιa ιb had hbd haL1 hbL2 hNaP hNbP hιaI hιbI haιa hbιb hNaI hNbI hnab hιne
          have hdιa : G.degree ιa = 3 := (hIsoprop ιa hιaI).1
          have hdιb : G.degree ιb = 3 := (hIsoprop ιb hιbI).1
          have hnbL1 : ¬G.Adj b L₁ := notP b L₂ hNbP L₁ hL1P hL1L2
          have hnaL2 : ¬G.Adj a L₂ := notP a L₁ hNaP L₂ hL2P (Ne.symm hL1L2)
          exact hth (two_hub_cherry_pair_twenty G a b L₁ ιa L₂ ιb had hbd hL1deg hdιa hL2deg hdιb
            haL1.symm haιa.symm hbL2.symm hbιb.symm hnab hnaL2
            (notIso a ιa hNaI ιb hιbI (Ne.symm hιne))
            (fun h => hnbL1 h.symm)
            (fun h => (notIso b ιb hNbI ιa hιaI hιne) h.symm)
            hnL1L2
            (fun h => hIso_nadj ιb hιbI L₁ hL1deg h.symm)
            (fun h => hIso_nadj ιa hιaI L₂ hL2deg h)
            (fun h => hIso_nadj ιa hιaI ιb hdιb h)
            (fun he => hL1nIso (he ▸ hιaI)) (fun he => hL2nIso (he ▸ hιbI))
            hL1L2 (fun he => hL1nIso (he ▸ hιbI)) (fun he => hL2nIso (he ▸ hιaI)) hιne)
        have h1pairTwoHub : ∀ k Lk ιk : Fin 20, k ∈ Dᶜ → G.degree k = 4 →
            (Lk = L₁ ∨ Lk = L₂) → G.Adj k Lk → ιk ∈ Iso → G.Adj k ιk →
            G.neighborFinset k ∩ Iso = {ιk} → G.neighborFinset k ∩ P = {Lk} →
            ιk ∉ G.neighborFinset h₁ → False := by
          intro k Lk ιk hkDc hkd hLkleaf hkLk hιkI hkιk hNkI hNkP hιk_out
          have hLkP : Lk ∈ P := by rcases hLkleaf with rfl | rfl; exacts [hL1P, hL2P]
          have hLkc1 : Lk ≠ c₁ := by rcases hLkleaf with rfl | rfl; exacts [hL1c1, hL2c1]
          have hLknIso : Lk ∉ Iso := by rcases hLkleaf with rfl | rfl; exacts [hL1nIso, hL2nIso]
          have hLkdeg : G.degree Lk = 3 := by rcases hLkleaf with rfl | rfl; exacts [hL1deg, hL2deg]
          have hdιk : G.degree ιk = 3 := (hIsoprop ιk hιkI).1
          have hkh1 : k ≠ h₁ := by
            intro he
            have : Lk ∈ G.neighborFinset h₁ ∩ P := by
              rw [← he]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset k Lk).mpr hkLk, hLkP⟩
            rw [hNh1P, Finset.mem_singleton] at this; exact hLkc1 this
          have hshare := isolated_deg4_share_le_one G h₁ k hC4 hh1d hkd (Ne.symm hkh1)
            (hnadj1hub k hkDc) hdeg3N1 hindep1
          have hpriv : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset k).card := by
            have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset k)
            have hsub : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset k
                ⊆ G.neighborFinset h₁ ∩ G.neighborFinset k := by
              intro x hx
              obtain ⟨hxNI, hxNk⟩ := Finset.mem_inter.mp hx
              exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxNI).1, hxNk⟩
            have := Finset.card_le_card hsub
            rw [hisoinc3] at hsplit; omega
          obtain ⟨p, hpM, q, hqM, hpq⟩ :=
            Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset k).card)
          obtain ⟨hpNI, hpNk⟩ := Finset.mem_sdiff.mp hpM
          obtain ⟨hqNI, hqNk⟩ := Finset.mem_sdiff.mp hqM
          obtain ⟨hpN1, hpI⟩ := Finset.mem_inter.mp hpNI
          obtain ⟨hqN1, hqI⟩ := Finset.mem_inter.mp hqNI
          have hdp : G.degree p = 3 := (hIsoprop p hpI).1
          have hdq : G.degree q = 3 := (hIsoprop q hqI).1
          have hph1 : G.Adj p h₁ := ((G.mem_neighborFinset h₁ p).mp hpN1).symm
          have hqh1 : G.Adj q h₁ := ((G.mem_neighborFinset h₁ q).mp hqN1).symm
          have hn_h1Lk : ¬G.Adj h₁ Lk := by
            intro ha
            have : Lk ∈ G.neighborFinset h₁ ∩ P :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ Lk).mpr ha, hLkP⟩
            rw [hNh1P, Finset.mem_singleton] at this; exact hLkc1 this
          have hn_h1ιk : ¬G.Adj h₁ ιk := fun ha => hιk_out ((G.mem_neighborFinset h₁ ιk).mpr ha)
          have hιkNk : ιk ∈ G.neighborFinset k := (G.mem_neighborFinset k ιk).mpr hkιk
          exact hth (two_hub_cherry_pair_twenty G h₁ k p q Lk ιk hh1d hkd hdp hdq hLkdeg hdιk
            hph1 hqh1 hkLk.symm hkιk.symm (hnadj1hub k hkDc) hn_h1Lk hn_h1ιk
            (fun ha => hpNk ((G.mem_neighborFinset k p).mpr ha.symm))
            (fun ha => hqNk ((G.mem_neighborFinset k q).mpr ha.symm))
            (fun ha => hIso_nadj p hpI Lk hLkdeg ha)
            (fun ha => hIso_nadj p hpI ιk hdιk ha)
            (fun ha => hIso_nadj q hqI Lk hLkdeg ha)
            (fun ha => hIso_nadj q hqI ιk hdιk ha)
            hpq (fun he => hLknIso (he ▸ hιkI))
            (fun he => hLknIso (he ▸ hpI)) (fun he => hpNk (he ▸ hιkNk))
            (fun he => hLknIso (he ▸ hqI)) (fun he => hqNk (he ▸ hιkNk)))
        have hab11 : a1 ≠ b1 := by
          intro he; exact (notP a1 L₁ ha1NP L₂ hL2P (Ne.symm hL1L2)) (by rw [he]; exact hb1L2)
        have hab12 : a1 ≠ b2 := by
          intro he; exact (notP a1 L₁ ha1NP L₂ hL2P (Ne.symm hL1L2)) (by rw [he]; exact hb2L2)
        have hab21 : a2 ≠ b1 := by
          intro he; exact (notP a2 L₁ ha2NP L₂ hL2P (Ne.symm hL1L2)) (by rw [he]; exact hb1L2)
        have hab22 : a2 ≠ b2 := by
          intro he; exact (notP a2 L₁ ha2NP L₂ hL2P (Ne.symm hL1L2)) (by rw [he]; exact hb2L2)
        set Aset : Finset (Fin 20) := {a1, a2, b1, b2} with hAsetdef
        set Sset : Finset (Fin 20) := insert h₁ (insert h₅ Aset) with hSsetdef
        set Fset : Finset (Fin 20) := Dᶜ \ Sset with hFsetdef
        have hAcard : Aset.card = 4 := by
          rw [hAsetdef]
          rw [Finset.card_insert_of_notMem (by simp [ha12, hab11, hab12]),
            Finset.card_insert_of_notMem (by simp [hab21, hab22]),
            Finset.card_insert_of_notMem (by simp [hb12]), Finset.card_singleton]
        have hh1nA : h₁ ∉ Aset := by
          simp only [hAsetdef, Finset.mem_insert, Finset.mem_singleton]
          push Not; exact ⟨Ne.symm ha1_1, Ne.symm ha2_1, Ne.symm hb1_1, Ne.symm hb2_1⟩
        have hh5nA : h₅ ∉ Aset := by
          simp only [hAsetdef, Finset.mem_insert, Finset.mem_singleton]
          push Not; exact ⟨Ne.symm ha1_5, Ne.symm ha2_5, Ne.symm hb1_5, Ne.symm hb2_5⟩
        have hScard : Sset.card = 6 := by
          rw [hSsetdef, Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert]; push Not; exact ⟨hne15, hh1nA⟩),
            Finset.card_insert_of_notMem hh5nA, hAcard]
        have hSsubDc : Sset ⊆ Dᶜ := by
          rw [hSsetdef]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, hAsetdef] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          exacts [hh1Dc, hh5Dc, ha1Dc, ha2Dc, hb1Dc, hb2Dc]
        have hFcard5 : Fset.card = 5 := by
          have hcs : (Dᶜ \ Sset).card = Dᶜ.card - Sset.card := Finset.card_sdiff_of_subset hSsubDc
          rw [hFsetdef, hcs, hHub11, hScard]
        have hFmem : ∀ f : Fin 20, f ∈ Fset ↔ f ∈ Dᶜ ∧ f ≠ h₁ ∧ f ≠ h₅ ∧
            f ≠ a1 ∧ f ≠ a2 ∧ f ≠ b1 ∧ f ≠ b2 := by
          intro f
          rw [hFsetdef, Finset.mem_sdiff, hSsetdef]
          simp only [Finset.mem_insert, Finset.mem_singleton, hAsetdef]
          constructor
          · rintro ⟨hfDc, hf⟩; push Not at hf; exact ⟨hfDc, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1,
              hf.2.2.2.2.1, hf.2.2.2.2.2⟩
          · rintro ⟨hfDc, h1, h5, ha1, ha2, hb1, hb2⟩
            exact ⟨hfDc, by push Not; exact ⟨h1, h5, ha1, ha2, hb1, hb2⟩⟩
        have hsa1 : hs ≠ a1 := by intro he; rw [he, ha1NP] at hsleaf; simp at hsleaf
        have hsa2 : hs ≠ a2 := by intro he; rw [he, ha2NP] at hsleaf; simp at hsleaf
        have hsb1 : hs ≠ b1 := by intro he; rw [he, hb1NP] at hsleaf; simp at hsleaf
        have hsb2 : hs ≠ b2 := by intro he; rw [he, hb2NP] at hsleaf; simp at hsleaf
        have hsF : hs ∈ Fset := (hFmem hs).mpr ⟨hsDc, hs1, hs5, hsa1, hsa2, hsb1, hsb2⟩
        have hFprop : ∀ f : Fin 20, f ∈ Fset → G.degree f = 4 ∧
            ¬G.Adj f L₁ ∧ ¬G.Adj f c₁ ∧ ¬G.Adj f c₂ := by
          intro f hf
          obtain ⟨hfDc, hf1, hf5, hfa1, hfa2, hfb1, hfb2⟩ := (hFmem f).mp hf
          have hd4 := hdegOth f hfDc hf1 hf5
          have hnfL1 : ¬G.Adj f L₁ := by
            intro ha
            have : f ∈ G.neighborFinset L₁ ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ f).mpr ha.symm, hfDc⟩
            rw [haLeq, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h | h
            exacts [hfa1 h, hfa2 h]
          have hnfc1 : ¬G.Adj f c₁ := by
            intro ha
            have : f ∈ G.neighborFinset c₁ ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ f).mpr ha.symm, hfDc⟩
            rw [hNc1Dc, Finset.mem_singleton] at this; exact hf1 this
          have hnfc2 : ¬G.Adj f c₂ := by
            intro ha
            have : f ∈ G.neighborFinset c₂ ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ f).mpr ha.symm, hfDc⟩
            rw [hNc2Dc, Finset.mem_singleton] at this; exact hf5 this
          exact ⟨hd4, hnfL1, hnfc1, hnfc2⟩
        have hFint3 : ∀ f : Fin 20, f ∈ Fset → f ≠ hs → (G.neighborFinset f ∩ Dᶜ).card = 3 := by
          intro f hf hfs
          obtain ⟨hfDc, hf1, hf5, hfa1, hfa2, hfb1, hfb2⟩ := (hFmem f).mp hf
          obtain ⟨hd4, hnfL1, hnfc1, hnfc2⟩ := hFprop f hf
          have hiso1 := hOthcap f hfDc hf1 hf5 hfs
          have hnfL2 : ¬G.Adj f L₂ := by
            intro ha
            have : f ∈ G.neighborFinset L₂ ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₂ f).mpr ha.symm, hfDc⟩
            rw [haReq, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h | h
            exacts [hfb1 h, hfb2 h]
          have hcinc0 : (G.neighborFinset f ∩ P).card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro x hx
            obtain ⟨hxN, hxP⟩ := Finset.mem_inter.mp hx
            have hadj : G.Adj f x := (G.mem_neighborFinset f x).mp hxN
            simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hxP
            rcases hxP with rfl | rfl | rfl | rfl
            exacts [hnfL1 hadj, hnfc1 hadj, hnfc2 hadj, hnfL2 hadj]
          have hdec := hper f hfDc
          rw [hiso1, hcinc0, hd4] at hdec; omega
        have hsIntF : (G.neighborFinset hs ∩ Dᶜ).card = 4 := by
          have hdec := hper hs hsDc
          rw [hsleaf, hsiso0, hsd4] at hdec; omega
        have hh5isoempty : G.neighborFinset h₅ ∩ Dᶜ = ∅ := hh5int0
        have hnh1h5 : ∀ x : Fin 20, x ∈ Dᶜ → ¬G.Adj x h₁ ∧ ¬G.Adj x h₅ := by
          intro x hx
          refine ⟨fun ha => ?_, fun ha => ?_⟩
          · have : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ x).mpr ha.symm, hx⟩
            rw [hh1iso] at this; exact absurd this (Finset.notMem_empty x)
          · have : x ∈ G.neighborFinset h₅ ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ x).mpr ha.symm, hx⟩
            rw [hh5isoempty] at this; exact absurd this (Finset.notMem_empty x)
        have hAsubS : Aset ⊆ Sset := by
          intro x hx; rw [hSsetdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
        have hAsubDc : Aset ⊆ Dᶜ := hAsubS.trans hSsubDc
        have hFsubDc : Fset ⊆ Dᶜ := by rw [hFsetdef]; exact Finset.sdiff_subset
        have hAFdisj : Disjoint Aset Fset := by
          rw [hFsetdef]
          apply Finset.disjoint_left.mpr
          intro x hxA hxF
          exact (Finset.mem_sdiff.mp hxF).2 (hAsubS hxA)
        have hpartition : ∀ h : Fin 20, h ∈ Dᶜ →
            (G.neighborFinset h ∩ Dᶜ).card
              = (G.neighborFinset h ∩ Aset).card + (G.neighborFinset h ∩ Fset).card := by
          intro h hh
          obtain ⟨hnh1, hnh5⟩ := hnh1h5 h hh
          have hunion : G.neighborFinset h ∩ Dᶜ
              = (G.neighborFinset h ∩ Aset) ∪ (G.neighborFinset h ∩ Fset) := by
            apply Finset.ext; intro x
            simp only [Finset.mem_union, Finset.mem_inter]
            constructor
            · rintro ⟨hxN, hxDc⟩
              have hxSF : x ∈ Sset ∨ x ∈ Fset := by
                rw [hFsetdef]; by_cases hxS : x ∈ Sset
                · exact Or.inl hxS
                · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxDc, hxS⟩)
              rcases hxSF with hxS | hxF
              · rw [hSsetdef, Finset.mem_insert, Finset.mem_insert] at hxS
                rcases hxS with rfl | rfl | hxA
                · exact absurd ((G.mem_neighborFinset h x).mp hxN) hnh1
                · exact absurd ((G.mem_neighborFinset h x).mp hxN) hnh5
                · exact Or.inl ⟨hxN, hxA⟩
              · exact Or.inr ⟨hxN, hxF⟩
            · rintro (⟨hxN, hxA⟩ | ⟨hxN, hxF⟩)
              · exact ⟨hxN, hAsubDc hxA⟩
              · exact ⟨hxN, hFsubDc hxF⟩
          rw [hunion, Finset.card_union_of_disjoint]
          exact Finset.disjoint_left.mpr (fun x hxA hxF =>
            (Finset.disjoint_left.mp hAFdisj) (Finset.mem_inter.mp hxA).2 (Finset.mem_inter.mp hxF).2)
        have hsumF : ∑ f ∈ Fset, (G.neighborFinset f ∩ Dᶜ).card = 16 := by
          have hkey := Finset.add_sum_erase Fset
            (fun f => (G.neighborFinset f ∩ Dᶜ).card) hsF
          have hd : ∑ f ∈ Fset.erase hs, (G.neighborFinset f ∩ Dᶜ).card
              = ∑ _f ∈ Fset.erase hs, 3 := by
            apply Finset.sum_congr rfl
            intro f hf
            obtain ⟨hfne, hfF⟩ := Finset.mem_erase.mp hf
            exact hFint3 f hfF hfne
          rw [hd, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hsF, hFcard5,
            hsIntF] at hkey
          omega
        have hsumA8 : ∑ a ∈ Aset, (G.neighborFinset a ∩ Dᶜ).card = 8 := by
          have hAint : ∀ a ∈ Aset, (G.neighborFinset a ∩ Dᶜ).card = 2 := by
            intro a ha
            rw [hAsetdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at ha
            rcases ha with rfl | rfl | rfl | rfl
            exacts [ha1int, ha2int, hb1int, hb2int]
          rw [Finset.sum_congr rfl hAint, Finset.sum_const, smul_eq_mul, hAcard]
        have hbip : ∑ f ∈ Fset, (G.neighborFinset f ∩ Aset).card
            = ∑ a ∈ Aset, (G.neighborFinset a ∩ Fset).card := by
          have key : ∀ s t : Finset (Fin 20), ∑ f ∈ s, (G.neighborFinset f ∩ t).card
              = ∑ f ∈ s, ∑ a ∈ t, (if G.Adj f a then 1 else 0) := by
            intro s t
            apply Finset.sum_congr rfl; intro f _
            rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
            apply Finset.sum_congr rfl; intro a _
            simp only [G.mem_neighborFinset]
          rw [key Fset Aset, key Aset Fset, Finset.sum_comm]
          apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro f _
          simp only [G.adj_comm]
        have hsumFF : ∑ f ∈ Fset, (G.neighborFinset f ∩ Fset).card
            = 8 + ∑ a ∈ Aset, (G.neighborFinset a ∩ Aset).card := by
          have hF := Finset.sum_congr rfl (fun f (hf : f ∈ Fset) => hpartition f (hFsubDc hf))
          have hA := Finset.sum_congr rfl (fun a (ha : a ∈ Aset) => hpartition a (hAsubDc ha))
          rw [Finset.sum_add_distrib] at hF hA
          rw [hsumF] at hF; rw [hsumA8] at hA
          omega
        have Ftri : 6 ≤ ∑ a ∈ Aset, (G.neighborFinset a ∩ Aset).card → False := by
          intro hge6
          have hsumFF13 : 13 ≤ ∑ f ∈ Fset, (G.neighborFinset f ∩ Fset).card := by
            rw [hsumFF]; omega
          obtain ⟨x, y, z, hxF, hyF, hzF, hxy, hxz, hyz⟩ :=
            five_edge_triangle G Fset hFcard5 hsumFF13
          obtain ⟨hxd, hxL1, hxc1, hxc2⟩ := hFprop x hxF
          obtain ⟨hyd, hyL1, hyc1, hyc2⟩ := hFprop y hyF
          obtain ⟨hzd, hzL1, hzc1, hzc2⟩ := hFprop z hzF
          exact hntri1 ⟨x, y, z, hFsubDc hxF, hFsubDc hyF, hFsubDc hzF, hxy, hxz, hyz,
            ⟨hxL1, hxc1, hxc2⟩, ⟨hyL1, hyc1, hyc2⟩, ⟨hzL1, hzc1, hzc2⟩, by omega⟩
        have hNι : ∀ x y ι : Fin 20, x ≠ h₅ → y ≠ h₅ →
            G.neighborFinset ι = {h₁, x, y} → ¬G.Adj h₅ ι := by
          intro x y ι hxh5 hyh5 hNιeq hadj
          have : h₅ ∈ ({h₁, x, y} : Finset (Fin 20)) := by
            rw [← hNιeq]; exact (G.mem_neighborFinset ι h₅).mpr hadj.symm
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h | h
          exacts [hne15 h.symm, hxh5 h.symm, hyh5 h.symm]
        have hNι_eq : ∀ x y ι : Fin 20, ι ∈ Iso → G.Adj h₁ ι → G.Adj x ι → G.Adj y ι →
            h₁ ≠ x → h₁ ≠ y → x ≠ y → G.neighborFinset ι = {h₁, x, y} := by
          intro x y ι hιI hh1ι hxι hyι hne1x hne1y hxy
          have hcard3 : (G.neighborFinset ι).card = 3 := by
            rw [G.card_neighborFinset_eq_degree]; exact (hIsoprop ι hιI).1
          have hsub : ({h₁, x, y} : Finset (Fin 20)) ⊆ G.neighborFinset ι := by
            intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl
            · exact (G.mem_neighborFinset ι w).mpr hh1ι.symm
            · exact (G.mem_neighborFinset ι w).mpr hxι.symm
            · exact (G.mem_neighborFinset ι w).mpr hyι.symm
          have hc3 : ({h₁, x, y} : Finset (Fin 20)).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [hne1x, hne1y]),
              Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
          exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hc3])).symm
        have hfallback : ∀ a a' b b' ιa ιa' ιb ιb' : Fin 20,
            a ∈ Dᶜ → a' ∈ Dᶜ → b ∈ Dᶜ → b' ∈ Dᶜ →
            a ∈ Aset → a' ∈ Aset → b ∈ Aset → b' ∈ Aset →
            G.degree a = 4 → G.degree a' = 4 → G.degree b = 4 → G.degree b' = 4 →
            a ≠ h₁ → a' ≠ h₁ → b ≠ h₁ →
            G.Adj a L₁ → G.Adj a' L₁ → G.Adj b L₂ → G.Adj b' L₂ →
            G.neighborFinset a ∩ P = {L₁} → G.neighborFinset a' ∩ P = {L₁} →
            G.neighborFinset b ∩ P = {L₂} → G.neighborFinset b' ∩ P = {L₂} →
            ιa ∈ Iso → ιa' ∈ Iso → ιb ∈ Iso → ιb' ∈ Iso →
            G.Adj a ιa → G.Adj a' ιa' → G.Adj b ιb → G.Adj b' ιb' →
            G.neighborFinset a ∩ Iso = {ιa} → G.neighborFinset a' ∩ Iso = {ιa'} →
            G.neighborFinset b ∩ Iso = {ιb} → G.neighborFinset b' ∩ Iso = {ιb'} →
            a ≠ a' → b ≠ b' → a ≠ b → a' ≠ b → a ≠ b' → a' ≠ b' →
            ¬G.Adj a b → ιa = ιb → False := by
          intro a a' b b' ιa ιa' ιb ιb' haDc ha'Dc hbDc hb'Dc haA ha'A hbA hb'A
            had ha'd hbd hb'd hah1 ha'h1 hbh1 haL1 ha'L1 hbL2 hb'L2 haNP ha'NP hbNP hb'NP
            hιaI hιa'I hιbI hιb'I haιa ha'ιa' hbιb hb'ιb' haNI ha'NI hbNI hb'NI
            haa' hbb' hab ha'b hab' ha'b' hnab hιeq
          by_cases hout : ιa ∉ G.neighborFinset h₁ ∨ ιa' ∉ G.neighborFinset h₁ ∨
              ιb ∉ G.neighborFinset h₁ ∨ ιb' ∉ G.neighborFinset h₁
          · rcases hout with h | h | h | h
            · exact h1pairTwoHub a L₁ ιa haDc had (Or.inl rfl) haL1 hιaI haιa haNI haNP h
            · exact h1pairTwoHub a' L₁ ιa' ha'Dc ha'd (Or.inl rfl) ha'L1 hιa'I ha'ιa' ha'NI ha'NP h
            · exact h1pairTwoHub b L₂ ιb hbDc hbd (Or.inr rfl) hbL2 hιbI hbιb hbNI hbNP h
            · exact h1pairTwoHub b' L₂ ιb' hb'Dc hb'd (Or.inr rfl) hb'L2 hιb'I hb'ιb' hb'NI hb'NP h
          · push Not at hout
            obtain ⟨haN1, ha'N1, hbN1, hb'N1⟩ := hout
            have hb'h1 : b' ≠ h₁ := by
              intro he
              have : L₂ ∈ G.neighborFinset h₁ ∩ P := by
                rw [← he]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b' L₂).mpr hb'L2, hL2P⟩
              rw [hNh1P, Finset.mem_singleton] at this; exact hL2c1 this
            have hleaf_ne_h5 : ∀ x : Fin 20, G.Adj x L₁ ∨ G.Adj x L₂ → x ≠ h₅ := by
              intro x hx he
              rcases hx with hx | hx
              · have : L₁ ∈ G.neighborFinset h₅ ∩ P :=
                  Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ L₁).mpr (he ▸ hx), hL1P⟩
                rw [hNh5P, Finset.mem_singleton] at this; exact hL1nc2 this
              · have : L₂ ∈ G.neighborFinset h₅ ∩ P :=
                  Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ L₂).mpr (he ▸ hx), hL2P⟩
                rw [hNh5P, Finset.mem_singleton] at this; exact hL2c2 this
            have hah5 : a ≠ h₅ := hleaf_ne_h5 a (Or.inl haL1)
            have ha'h5 : a' ≠ h₅ := hleaf_ne_h5 a' (Or.inl ha'L1)
            have hbh5 : b ≠ h₅ := hleaf_ne_h5 b (Or.inr hbL2)
            have hb'h5 : b' ≠ h₅ := hleaf_ne_h5 b' (Or.inr hb'L2)
            have hh1ιa : G.Adj h₁ ιa := (G.mem_neighborFinset h₁ ιa).mp haN1
            have hbιa : G.Adj b ιa := by rw [hιeq]; exact hbιb
            have hNιa : G.neighborFinset ιa = {h₁, a, b} :=
              hNι_eq a b ιa hιaI hh1ιa haιa hbιa (Ne.symm hah1) (Ne.symm hbh1) hab
            have hn_h5ιa : ¬G.Adj h₅ ιa := hNι a b ιa hah5 hbh5 hNιa
            have hιa'ne : ιa' ≠ ιa := by
              intro he
              have : a' ∈ ({h₁, a, b} : Finset (Fin 20)) := by
                rw [← hNιa]; exact (G.mem_neighborFinset ιa a').mpr (he ▸ ha'ιa').symm
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with h | h | h
              exacts [ha'h1 h, haa'.symm h, ha'b h]
            have hιb'ne : ιb' ≠ ιa := by
              intro he
              have : b' ∈ ({h₁, a, b} : Finset (Fin 20)) := by
                rw [← hNιa]; exact (G.mem_neighborFinset ιa b').mpr (he ▸ hb'ιb').symm
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with h | h | h
              exacts [hb'h1 h, hab'.symm h, hbb'.symm h]
            by_cases hAB' : G.Adj a b'
            · by_cases hA'B : G.Adj a' b
              · by_cases hιa'b' : ιa' = ιb'
                · have hh1ιa' : G.Adj h₁ ιa' := (G.mem_neighborFinset h₁ ιa').mp ha'N1
                  have hb'ιa' : G.Adj b' ιa' := hιa'b' ▸ hb'ιb'
                  have hNιa' : G.neighborFinset ιa' = {h₁, a', b'} :=
                    hNι_eq a' b' ιa' hιa'I hh1ιa' ha'ιa' hb'ιa' (Ne.symm ha'h1) (Ne.symm hb'h1) ha'b'
                  have hn_h5ιa' : ¬G.Adj h₅ ιa' := hNι a' b' ιa' ha'h5 hb'h5 hNιa'
                  have hpair2 : ({ιa, ιa'} : Finset (Fin 20)) ⊆ Iso := by
                    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl; exacts [hιaI, hιa'I]
                  have hsubT : G.neighborFinset h₅ ∩ Iso ⊆ Iso \ {ιa, ιa'} := by
                    intro x hx
                    obtain ⟨hxN, hxI⟩ := Finset.mem_inter.mp hx
                    refine Finset.mem_sdiff.mpr ⟨hxI, ?_⟩
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    push Not
                    exact ⟨fun he => hn_h5ιa (he ▸ (G.mem_neighborFinset h₅ x).mp hxN),
                      fun he => hn_h5ιa' (he ▸ (G.mem_neighborFinset h₅ x).mp hxN)⟩
                  have hle := Finset.card_le_card hsubT
                  rw [hh5iso4, Finset.card_sdiff_of_subset hpair2, hIsocard,
                    Finset.card_insert_of_notMem (by simp [Ne.symm hιa'ne]), Finset.card_singleton] at hle
                  omega
                · by_cases hA'B' : G.Adj a' b'
                  · apply Ftri
                    have hAeq : Aset = {a, a', b, b'} := by
                      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
                      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl | rfl | rfl
                        exacts [haA, ha'A, hbA, hb'A]
                      · rw [hAcard, Finset.card_insert_of_notMem (by simp [haa', hab, hab']),
                          Finset.card_insert_of_notMem (by simp [ha'b, ha'b']),
                          Finset.card_insert_of_notMem (by simp [hbb']), Finset.card_singleton]
                    have hfa : 1 ≤ (G.neighborFinset a ∩ Aset).card :=
                      Finset.card_pos.mpr ⟨b', Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a b').mpr hAB', hb'A⟩⟩
                    have hfb : 1 ≤ (G.neighborFinset b ∩ Aset).card :=
                      Finset.card_pos.mpr ⟨a', Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b a').mpr hA'B.symm, ha'A⟩⟩
                    have hfa' : 2 ≤ (G.neighborFinset a' ∩ Aset).card := by
                      apply Finset.one_lt_card.mpr
                      exact ⟨b, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a' b).mpr hA'B, hbA⟩,
                        b', Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a' b').mpr hA'B', hb'A⟩, hbb'⟩
                    have hfb' : 2 ≤ (G.neighborFinset b' ∩ Aset).card := by
                      apply Finset.one_lt_card.mpr
                      exact ⟨a, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b' a).mpr hAB'.symm, haA⟩,
                        a', Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b' a').mpr hA'B'.symm, ha'A⟩, haa'⟩
                    rw [hAeq] at hfa hfb hfa' hfb'
                    rw [hAeq, Finset.sum_insert (by simp [haa', hab, hab']),
                      Finset.sum_insert (by simp [ha'b, ha'b']),
                      Finset.sum_insert (by simp [hbb']), Finset.sum_singleton]
                    omega
                  · exact crossTwoHub a' b' ιa' ιb' ha'd hb'd ha'L1 hb'L2 ha'NP hb'NP hιa'I hιb'I
                      ha'ιa' hb'ιb' ha'NI hb'NI hA'B' hιa'b'
              · exact crossTwoHub a' b ιa' ιb ha'd hbd ha'L1 hbL2 ha'NP hbNP hιa'I hιbI
                  ha'ιa' hbιb ha'NI hbNI hA'B (by rw [← hιeq]; exact hιa'ne)
            · exact crossTwoHub a b' ιa ιb' had hb'd haL1 hb'L2 haNP hb'NP hιaI hιb'I
                haιa hb'ιb' haNI hb'NI hAB' (Ne.symm hιb'ne)
        have ha1A : a1 ∈ Aset := by rw [hAsetdef]; simp
        have ha2A : a2 ∈ Aset := by rw [hAsetdef]; simp
        have hb1A : b1 ∈ Aset := by rw [hAsetdef]; simp
        have hb2A : b2 ∈ Aset := by rw [hAsetdef]; simp
        by_cases hAA : G.Adj a1 b1 ∧ G.Adj a1 b2 ∧ G.Adj a2 b1 ∧ G.Adj a2 b2
        · obtain ⟨h11, h12', h21, h22⟩ := hAA
          apply Ftri
          have hf1 : 2 ≤ (G.neighborFinset a1 ∩ Aset).card := Finset.one_lt_card.mpr
            ⟨b1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a1 b1).mpr h11, hb1A⟩,
             b2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a1 b2).mpr h12', hb2A⟩, hb12⟩
          have hf2 : 2 ≤ (G.neighborFinset a2 ∩ Aset).card := Finset.one_lt_card.mpr
            ⟨b1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a2 b1).mpr h21, hb1A⟩,
             b2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a2 b2).mpr h22, hb2A⟩, hb12⟩
          have hf3 : 2 ≤ (G.neighborFinset b1 ∩ Aset).card := Finset.one_lt_card.mpr
            ⟨a1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b1 a1).mpr h11.symm, ha1A⟩,
             a2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b1 a2).mpr h21.symm, ha2A⟩, ha12⟩
          have hf4 : 2 ≤ (G.neighborFinset b2 ∩ Aset).card := Finset.one_lt_card.mpr
            ⟨a1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b2 a1).mpr h12'.symm, ha1A⟩,
             a2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b2 a2).mpr h22.symm, ha2A⟩, ha12⟩
          rw [hAsetdef, Finset.sum_insert (by simp [ha12, hab11, hab12]),
            Finset.sum_insert (by simp [hab21, hab22]),
            Finset.sum_insert (by simp [hb12]), Finset.sum_singleton]
          rw [hAsetdef] at hf1 hf2 hf3 hf4
          omega
        · simp only [not_and_or] at hAA
          rcases hAA with h | h | h | h
          · by_cases hιe : ιa1 = ιb1
            · exact hfallback a1 a2 b1 b2 ιa1 ιa2 ιb1 ιb2 ha1Dc ha2Dc hb1Dc hb2Dc ha1A ha2A hb1A hb2A
                ha1d ha2d hb1d hb2d ha1_1 ha2_1 hb1_1 ha1L1 ha2L1 hb1L2 hb2L2 ha1NP ha2NP hb1NP hb2NP
                hιa1I hιa2I hιb1I hιb2I ha1ι ha2ι hb1ι hb2ι ha1isoeq ha2isoeq hb1isoeq hb2isoeq
                ha12 hb12 hab11 hab21 hab12 hab22 h hιe
            · exact crossTwoHub a1 b1 ιa1 ιb1 ha1d hb1d ha1L1 hb1L2 ha1NP hb1NP hιa1I hιb1I
                ha1ι hb1ι ha1isoeq hb1isoeq h hιe
          · by_cases hιe : ιa1 = ιb2
            · exact hfallback a1 a2 b2 b1 ιa1 ιa2 ιb2 ιb1 ha1Dc ha2Dc hb2Dc hb1Dc ha1A ha2A hb2A hb1A
                ha1d ha2d hb2d hb1d ha1_1 ha2_1 hb2_1 ha1L1 ha2L1 hb2L2 hb1L2 ha1NP ha2NP hb2NP hb1NP
                hιa1I hιa2I hιb2I hιb1I ha1ι ha2ι hb2ι hb1ι ha1isoeq ha2isoeq hb2isoeq hb1isoeq
                ha12 (Ne.symm hb12) hab12 hab22 hab11 hab21 h hιe
            · exact crossTwoHub a1 b2 ιa1 ιb2 ha1d hb2d ha1L1 hb2L2 ha1NP hb2NP hιa1I hιb2I
                ha1ι hb2ι ha1isoeq hb2isoeq h hιe
          · by_cases hιe : ιa2 = ιb1
            · exact hfallback a2 a1 b1 b2 ιa2 ιa1 ιb1 ιb2 ha2Dc ha1Dc hb1Dc hb2Dc ha2A ha1A hb1A hb2A
                ha2d ha1d hb1d hb2d ha2_1 ha1_1 hb1_1 ha2L1 ha1L1 hb1L2 hb2L2 ha2NP ha1NP hb1NP hb2NP
                hιa2I hιa1I hιb1I hιb2I ha2ι ha1ι hb1ι hb2ι ha2isoeq ha1isoeq hb1isoeq hb2isoeq
                (Ne.symm ha12) hb12 hab21 hab11 hab22 hab12 h hιe
            · exact crossTwoHub a2 b1 ιa2 ιb1 ha2d hb1d ha2L1 hb1L2 ha2NP hb1NP hιa2I hιb1I
                ha2ι hb1ι ha2isoeq hb1isoeq h hιe
          · by_cases hιe : ιa2 = ιb2
            · exact hfallback a2 a1 b2 b1 ιa2 ιa1 ιb2 ιb1 ha2Dc ha1Dc hb2Dc hb1Dc ha2A ha1A hb2A hb1A
                ha2d ha1d hb2d hb1d ha2_1 ha1_1 hb2_1 ha2L1 ha1L1 hb2L2 hb1L2 ha2NP ha1NP hb2NP hb1NP
                hιa2I hιa1I hιb2I hιb1I ha2ι ha1ι hb2ι hb1ι ha2isoeq ha1isoeq hb2isoeq hb1isoeq
                (Ne.symm ha12) (Ne.symm hb12) hab22 hab12 hab21 hab11 h hιe
            · exact crossTwoHub a2 b2 ιa2 ιb2 ha2d hb2d ha2L1 hb2L2 ha2NP hb2NP hιa2I hιb2I
                ha2ι hb2ι ha2isoeq hb2isoeq h hιe
      · -- **`A`-hub deficit** (leaf-incident: `cinc(hs) ≥ 1`, `isoinc 0`, `int ≥ 2`).
        -- Re-derive the `h₅`-structure (`hRc2`, `hNc2Dc`) exactly as the `F`-branch.
        have hh5iso4 : (G.neighborFinset h₅ ∩ Iso).card = 4 := hh5cap
        have hh5cinc1 : (G.neighborFinset h₅ ∩ P).card = 1 := by
          have hdec := hper h₅ hh5Dc
          rw [hh5iso4, hh5int0c, hh5d] at hdec; omega
        obtain ⟨w5, hw5eq⟩ := Finset.card_eq_one.mp hh5cinc1
        have hw5mem : w5 ∈ G.neighborFinset h₅ ∩ P := by
          rw [hw5eq]; exact Finset.mem_singleton_self w5
        have hh5w5 : G.Adj h₅ w5 := (G.mem_neighborFinset h₅ w5).mp (Finset.mem_inter.mp hw5mem).1
        have hw5P : w5 ∈ P := (Finset.mem_inter.mp hw5mem).2
        have hh5only : ∀ x : Fin 20, x ∈ P → G.Adj h₅ x → x = w5 := by
          intro x hxP hadj
          have : x ∈ G.neighborFinset h₅ ∩ P :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ x).mpr hadj, hxP⟩
          rw [hw5eq] at this; exact Finset.mem_singleton.mp this
        have hNc1Dc : G.neighborFinset c₁ ∩ Dᶜ = {h₁} := by
          have h1mem : h₁ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₁).mpr hRc1.symm, hh1Dc⟩
          exact (Finset.eq_of_subset_of_card_le
            (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ h1mem)
            (by rw [hc1hub, Finset.card_singleton])).symm
        have hn_h5c1 : ¬G.Adj h₅ c₁ := by
          intro hadj
          have : h₅ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₅).mpr hadj.symm, hh5Dc⟩
          rw [hNc1Dc, Finset.mem_singleton] at this; exact hne15 this.symm
        have hRc2 : G.Adj h₅ c₂ := by
          simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hw5P
          rcases hw5P with rfl | rfl | rfl | rfl
          · exfalso
            have hn_c1 : ¬G.Adj h₅ c₁ :=
              fun ha => (G.ne_of_adj hac1L1) (hh5only c₁ (by simp [hPdef]) ha)
            have hn_c2 : ¬G.Adj h₅ c₂ :=
              fun ha => (Ne.symm hL1nc2) (hh5only c₂ (by simp [hPdef]) ha)
            have hn_L2 : ¬G.Adj h₅ L₂ :=
              fun ha => hL1L2 (hh5only L₂ (by simp [hPdef]) ha).symm
            obtain ⟨_, hne5c1, hne5c2, hne5L2⟩ := hubD_ne h₅ hh5Dc
            exact htt (twotwin_of_centre_twenty G Iso h₅ c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
              (hdeg5 h₅ hh5Dc) hc12 hac2L2 hn_c1 hn_c2 hn_L2 hc1nIso hc2nIso hL2nIso
              hne5c1 hne5c2 hne5L2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) (Ne.symm hL2nc1)
              (by rw [hh5iso4]; norm_num))
          · exact absurd hh5w5 hn_h5c1
          · exact hh5w5
          · exfalso
            have hn_L1 : ¬G.Adj h₅ L₁ :=
              fun ha => hL1L2 (hh5only L₁ (by simp [hPdef]) ha)
            have hn_c1 : ¬G.Adj h₅ c₁ :=
              fun ha => (Ne.symm hL2nc1) (hh5only c₁ (by simp [hPdef]) ha)
            have hn_c2 : ¬G.Adj h₅ c₂ :=
              fun ha => (G.ne_of_adj hac2L2) (hh5only c₂ (by simp [hPdef]) ha)
            obtain ⟨hne5L1, hne5c1, hne5c2, _⟩ := hubD_ne h₅ hh5Dc
            exact htt (twotwin_of_centre_twenty G Iso h₅ L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
              (hdeg5 h₅ hh5Dc) hac1L1.symm hc12 hn_L1 hn_c1 hn_c2 hL1nIso hc1nIso hc2nIso
              hne5L1 hne5c1 hne5c2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2
              (by rw [hh5iso4]; norm_num))
        have hNc2Dc : G.neighborFinset c₂ ∩ Dᶜ = {h₅} := by
          have h5mem : h₅ ∈ G.neighborFinset c₂ ∩ Dᶜ :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ h₅).mpr hRc2.symm, hh5Dc⟩
          exact (Finset.eq_of_subset_of_card_le
            (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ h5mem)
            (by rw [hc2hub, Finset.card_singleton])).symm
        -- `hs` avoids both centres `c₁` (unique hub `h₁ ≠ hs`) and `c₂` (unique hub `h₅ ≠ hs`).
        have hns_c1 : ¬G.Adj hs c₁ := by
          intro hadj
          have : hs ∈ G.neighborFinset c₁ ∩ Dᶜ :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ hs).mpr hadj.symm, hsDc⟩
          rw [hNc1Dc, Finset.mem_singleton] at this; exact hs1 this
        have hns_c2 : ¬G.Adj hs c₂ := by
          intro hadj
          have : hs ∈ G.neighborFinset c₂ ∩ Dᶜ :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ hs).mpr hadj.symm, hsDc⟩
          rw [hNc2Dc, Finset.mem_singleton] at this; exact hs5 this
        -- Hence `hs`'s path-neighbours lie among the two leaves `{L₁, L₂}`.
        have hsub : G.neighborFinset hs ∩ P ⊆ {L₁, L₂} := by
          intro x hx
          obtain ⟨hxN, hxP⟩ := Finset.mem_inter.mp hx
          have hadj : G.Adj hs x := (G.mem_neighborFinset hs x).mp hxN
          simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hxP
          rcases hxP with rfl | rfl | rfl | rfl
          · simp
          · exact absurd hadj hns_c1
          · exact absurd hadj hns_c2
          · simp
        have hcard2LL : ({L₁, L₂} : Finset (Fin 20)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
        -- `hs`'s `isoinc 0` forbids adjacency to any `Iso` vertex.
        have hsNotIso : ∀ x : Fin 20, x ∈ Iso → ¬G.Adj hs x := by
          intro x hxI hadj
          have hmem : x ∈ G.neighborFinset hs ∩ Iso :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset hs x).mpr hadj, hxI⟩
          rw [Finset.card_eq_zero.mp hsiso0] at hmem
          exact absurd hmem (Finset.notMem_empty x)
        -- `h₁`'s only path-neighbour is `c₁`; hence `h₁` avoids both leaves.
        have hNh1P : G.neighborFinset h₁ ∩ P = {c₁} := by
          have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P := Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
          exact (Finset.eq_of_subset_of_card_le
            (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hc1mem)
            (by rw [hcinc1', Finset.card_singleton])).symm
        have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
        have hn_h1L1 : ¬G.Adj h₁ L₁ := by
          intro ha
          have : L₁ ∈ G.neighborFinset h₁ ∩ P :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ L₁).mpr ha, by simp [hPdef]⟩
          rw [hNh1P, Finset.mem_singleton] at this; exact hL1c1 this
        have hn_h1L2 : ¬G.Adj h₁ L₂ := by
          intro ha
          have : L₂ ∈ G.neighborFinset h₁ ∩ P :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ L₂).mpr ha, by simp [hPdef]⟩
          rw [hNh1P, Finset.mem_singleton] at this; exact hL2nc1 this
        -- Extract two of `h₁`'s three `Iso`-twins (`p, q`); by `isoinc 0`, `hs` sees neither.
        obtain ⟨p, hpNI, q, hqNI, hpq⟩ :=
          Finset.one_lt_card.mp (by rw [hisoinc3]; norm_num :
            1 < (G.neighborFinset h₁ ∩ Iso).card)
        obtain ⟨hpN1, hpI⟩ := Finset.mem_inter.mp hpNI
        obtain ⟨hqN1, hqI⟩ := Finset.mem_inter.mp hqNI
        have hdp : G.degree p = 3 := (hIsoprop p hpI).1
        have hdq : G.degree q = 3 := (hIsoprop q hqI).1
        have hph1 : G.Adj p h₁ := ((G.mem_neighborFinset h₁ p).mp hpN1).symm
        have hqh1 : G.Adj q h₁ := ((G.mem_neighborFinset h₁ q).mp hqN1).symm
        by_cases hcinc2 : (G.neighborFinset hs ∩ P).card = 2
        · -- **`cinc(hs) = 2`**: `hs` is adjacent to BOTH leaves — kill via the two-hub cherry
          -- pair (`hs`'s cherry `= {L₁, L₂}`, `h₁`'s cherry `= {p, q}`).
          have hNsP : G.neighborFinset hs ∩ P = {L₁, L₂} :=
            Finset.eq_of_subset_of_card_le hsub (by rw [hcard2LL, hcinc2])
          have hsL1 : G.Adj hs L₁ := by
            have hmem : L₁ ∈ G.neighborFinset hs ∩ P := by rw [hNsP]; simp
            exact (G.mem_neighborFinset hs L₁).mp (Finset.mem_inter.mp hmem).1
          have hsL2 : G.Adj hs L₂ := by
            have hmem : L₂ ∈ G.neighborFinset hs ∩ P := by rw [hNsP]; simp
            exact (G.mem_neighborFinset hs L₂).mp (Finset.mem_inter.mp hmem).1
          exact hth (two_hub_cherry_pair_twenty G hs h₁ L₁ L₂ p q hsd4 hh1d hL1deg hL2deg hdp hdq
            hsL1.symm hsL2.symm hph1 hqh1
            (fun ha => (hnadj1hub hs hsDc) ha.symm)
            (hsNotIso p hpI) (hsNotIso q hqI)
            (fun ha => hn_h1L1 ha.symm) (fun ha => hn_h1L2 ha.symm)
            (fun ha => hIso_nadj p hpI L₁ hL1deg ha.symm)
            (fun ha => hIso_nadj q hqI L₁ hL1deg ha.symm)
            (fun ha => hIso_nadj p hpI L₂ hL2deg ha.symm)
            (fun ha => hIso_nadj q hqI L₂ hL2deg ha.symm)
            hL1L2 hpq
            (fun he => hL1nIso (he ▸ hpI)) (fun he => hL1nIso (he ▸ hqI))
            (fun he => hL2nIso (he ▸ hpI)) (fun he => hL2nIso (he ▸ hqI)))
        · -- **`cinc(hs) = 1` — `deficit_A_cinc1`.**  `hs` is a clean deg-`4` `A`-hub
          -- (`isoinc 0`, `int 3`) incident to exactly one leaf.  The eight remaining deg-`4`
          -- hubs (`≠ h₁, h₅, hs`) each carry one `Iso`-twin (`hOthcap`).  Since `L₁` has only
          -- two hub-neighbours, at least six of these avoid `L₁` (and, being pure, avoid
          -- `c₁, c₂` too); pigeonholing them into the five `Iso` twins yields two hubs `F, F'`
          -- sharing a twin `t`.  Adjacent ⟹ triangle `F–F'–t` (`Σ = 11`, `hT`); non-adjacent
          -- ⟹ `SingleVertexConfig` (`v := t`, cherry `L₁–c₁–c₂`, incidence `0`, `hsv`).
          classical
          have hpurec1 : ∀ x : Fin 20, x ∈ Dᶜ → x ≠ h₁ → ¬G.Adj x c₁ := by
            intro x hxDc hxne1 ha
            have hmem : x ∈ G.neighborFinset c₁ ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ x).mpr ha.symm, hxDc⟩
            rw [hNc1Dc, Finset.mem_singleton] at hmem; exact hxne1 hmem
          have hpurec2 : ∀ x : Fin 20, x ∈ Dᶜ → x ≠ h₅ → ¬G.Adj x c₂ := by
            intro x hxDc hxne5 ha
            have hmem : x ∈ G.neighborFinset c₂ ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ x).mpr ha.symm, hxDc⟩
            rw [hNc2Dc, Finset.mem_singleton] at hmem; exact hxne5 hmem
          have hdeg4ne3 : ∀ u w : Fin 20, G.degree u = 4 → G.degree w = 3 → u ≠ w := by
            intro u w hu hw he; rw [he] at hu; omega
          have hIsone : ∀ u w : Fin 20, u ∈ Iso → w ∉ Iso → u ≠ w :=
            fun u w hu hw he => hw (he ▸ hu)
          have hpurecard : ∀ x : Fin 20, ¬G.Adj x L₁ → ¬G.Adj x c₁ → ¬G.Adj x c₂ →
              (G.neighborFinset x ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card = 0 := by
            intro x hxL1 hxc1 hxc2
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro w hw; rw [Finset.mem_inter] at hw
            obtain ⟨hwN, hwm⟩ := hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
            have hadj := (G.mem_neighborFinset x w).mp hwN
            rcases hwm with rfl | rfl | rfl
            · exact hxL1 hadj
            · exact hxc1 hadj
            · exact hxc2 hadj
          have hScard : 6 ≤ (Dᶜ.filter
              (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ hs ∧ ¬G.Adj h L₁)).card := by
            have hcover : Dᶜ ⊆ (Dᶜ.filter
                (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ hs ∧ ¬G.Adj h L₁))
                ∪ (({h₁, h₅, hs} : Finset (Fin 20)) ∪ (G.neighborFinset L₁ ∩ Dᶜ)) := by
              intro x hx
              by_cases hp : x ≠ h₁ ∧ x ≠ h₅ ∧ x ≠ hs ∧ ¬G.Adj x L₁
              · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hp⟩)
              · refine Finset.mem_union_right _ ?_
                by_cases hx1 : x = h₁
                · exact Finset.mem_union_left _ (by simp [hx1])
                · by_cases hx5 : x = h₅
                  · exact Finset.mem_union_left _ (by simp [hx5])
                  · by_cases hxs : x = hs
                    · exact Finset.mem_union_left _ (by simp [hxs])
                    · have hadj : G.Adj x L₁ := by
                        by_contra hna; exact hp ⟨hx1, hx5, hxs, hna⟩
                      exact Finset.mem_union_right _ (Finset.mem_inter.mpr
                        ⟨(G.mem_neighborFinset L₁ x).mpr hadj.symm, hx⟩)
            have hcard3 : ({h₁, h₅, hs} : Finset (Fin 20)).card ≤ 3 := by
              have h1 := Finset.card_insert_le h₁ ({h₅, hs} : Finset (Fin 20))
              have h2 := Finset.card_insert_le h₅ ({hs} : Finset (Fin 20))
              rw [Finset.card_singleton] at h2; omega
            have hunionR : (({h₁, h₅, hs} : Finset (Fin 20))
                ∪ (G.neighborFinset L₁ ∩ Dᶜ)).card ≤ 5 := by
              have := Finset.card_union_le ({h₁, h₅, hs} : Finset (Fin 20))
                (G.neighborFinset L₁ ∩ Dᶜ)
              rw [hL1hub] at this; omega
            have hcov := Finset.card_le_card hcover
            have hunion := Finset.card_union_le
              (Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ hs ∧ ¬G.Adj h L₁))
              (({h₁, h₅, hs} : Finset (Fin 20)) ∪ (G.neighborFinset L₁ ∩ Dᶜ))
            rw [hHub11] at hcov; omega
          set f : Fin 20 → Fin 20 :=
            fun x => if hx : (G.neighborFinset x ∩ Iso).Nonempty then hx.choose else x
            with hfdef
          have hftwin : ∀ h ∈ Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ hs ∧ ¬G.Adj h L₁),
              G.Adj h (f h) ∧ f h ∈ Iso := by
            intro h hh
            rw [Finset.mem_filter] at hh
            obtain ⟨hhDc, hh1, hh5, hhs, _⟩ := hh
            have hne : (G.neighborFinset h ∩ Iso).Nonempty :=
              Finset.card_pos.mp (by rw [hOthcap h hhDc hh1 hh5 hhs]; norm_num)
            have hmem : f h ∈ G.neighborFinset h ∩ Iso := by
              simp only [hfdef, dif_pos hne]; exact hne.choose_spec
            obtain ⟨hN, hI⟩ := Finset.mem_inter.mp hmem
            exact ⟨(G.mem_neighborFinset h (f h)).mp hN, hI⟩
          obtain ⟨F, hFS, F', hF'S, hFF', hff⟩ :=
            Finset.exists_ne_map_eq_of_card_lt_of_maps_to
              (s := Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ hs ∧ ¬G.Adj h L₁))
              (t := Iso) (f := f) (by rw [hIsocard]; omega)
              (by
                intro h hh
                rw [Finset.mem_coe] at hh
                exact Finset.mem_coe.mpr (hftwin h hh).2)
          have htwI : f F ∈ Iso := (hftwin F hFS).2
          have hAFt : G.Adj F (f F) := (hftwin F hFS).1
          have hAF't : G.Adj F' (f F) := by
            have h := (hftwin F' hF'S).1; rwa [← hff] at h
          rw [Finset.mem_filter] at hFS hF'S
          obtain ⟨hFDc, hFne1, hFne5, _, hFnL1⟩ := hFS
          obtain ⟨hF'Dc, hF'ne1, hF'ne5, _, hF'nL1⟩ := hF'S
          have hdF : G.degree F = 4 := hdegOth F hFDc hFne1 hFne5
          have hdF' : G.degree F' = 4 := hdegOth F' hF'Dc hF'ne1 hF'ne5
          have hdegfF : G.degree (f F) = 3 := (hIsoprop (f F) htwI).1
          by_cases hadjFF' : G.Adj F F'
          · exact hT ⟨F, F', f F, hFF', hdeg4ne3 F' (f F) hdF' hdegfF,
              hdeg4ne3 F (f F) hdF hdegfF, hadjFF', hAF't, hAFt, by omega⟩
          · refine hsv ⟨f F, F, F', L₁, c₁, c₂, hdegfF, hL1deg, hc1deg, hc2deg,
              hAFt.symm, hAF't.symm, hac1L1.symm, hc12, fun h => hnc2L1 h.symm, ?_,
              hFF', hIsone (f F) L₁ htwI hL1nIso, hIsone (f F) c₁ htwI hc1nIso,
              hIsone (f F) c₂ htwI hc2nIso, hdeg4ne3 F L₁ hdF hL1deg,
              hdeg4ne3 F c₁ hdF hc1deg, hdeg4ne3 F c₂ hdF hc2deg,
              hdeg4ne3 F' L₁ hdF' hL1deg, hdeg4ne3 F' c₁ hdF' hc1deg,
              hdeg4ne3 F' c₂ hdF' hc2deg, (G.ne_of_adj hac1L1).symm,
              G.ne_of_adj hc12, hL1nc2⟩
            have hsum0 : (∑ p ∈ ({f F, F, F'} : Finset (Fin 20)),
                (G.neighborFinset p ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card) = 0 := by
              apply Finset.sum_eq_zero
              intro p hp
              simp only [Finset.mem_insert, Finset.mem_singleton] at hp
              rcases hp with rfl | hpF | hpF'
              · exact hpurecard (f F) (hIso_nadj (f F) htwI L₁ hL1deg)
                  (hIso_nadj (f F) htwI c₁ hc1deg) (hIso_nadj (f F) htwI c₂ hc2deg)
              · rw [hpF]
                exact hpurecard F hFnL1 (hpurec1 F hFDc hFne1) (hpurec2 F hFDc hFne5)
              · rw [hpF']
                exact hpurecard F' hF'nL1 (hpurec1 F' hF'Dc hF'ne1) (hpurec2 F' hF'Dc hF'ne5)
            rw [hsum0, if_neg hadjFF']; omega
    · -- **Case B: `h₅` deficit** (`isoinc 3`, `cinc 2`).
      have hh5iso3 : (G.neighborFinset h₅ ∩ Iso).card = 3 := by omega
      have hd1h5 : B h₅ - (G.neighborFinset h₅ ∩ Iso).card = 1 := by rw [hBh5, hh5iso3]
      have hOthcap : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ →
          (G.neighborFinset h ∩ Iso).card = 1 := by
        intro h hh hh1 hh5
        have hpair := hd2 h₅ h hh5Dc hh (Ne.symm hh5)
        rw [hd1h5] at hpair
        exact hOthiso1cap h hh hh1 hh5 (by omega)
      -- `h₅` carries the deficit: `isoinc 3`, `int 0`, hence `cinc h₅ = 2`.
      have hh5cinc2 : (G.neighborFinset h₅ ∩ P).card = 2 := by
        have hdec := hper h₅ hh5Dc
        rw [hh5iso3, hh5int0c, hh5d] at hdec; omega
      have hNc1Dc : G.neighborFinset c₁ ∩ Dᶜ = {h₁} := by
        have h1mem : h₁ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₁).mpr hRc1.symm, hh1Dc⟩
        exact (Finset.eq_of_subset_of_card_le
          (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ h1mem)
          (by rw [hc1hub, Finset.card_singleton])).symm
      have hn_h5c1 : ¬G.Adj h₅ c₁ := by
        intro hadj
        have hmem : h₅ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₅).mpr hadj.symm, hh5Dc⟩
        rw [hNc1Dc, Finset.mem_singleton] at hmem; exact hne15 hmem.symm
      have hSsub : G.neighborFinset h₅ ∩ P ⊆ ({L₁, c₂, L₂} : Finset (Fin 20)) := by
        intro x hx
        obtain ⟨hxN, hxP⟩ := Finset.mem_inter.mp hx
        have hadj : G.Adj h₅ x := (G.mem_neighborFinset h₅ x).mp hxN
        simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hxP
        rcases hxP with rfl | rfl | rfl | rfl
        · simp
        · exact absurd hadj hn_h5c1
        · simp
        · simp
      obtain ⟨hne5L1, hne5c1, hne5c2, hne5L2⟩ := hubD_ne h₅ hh5Dc
      by_cases hAc2 : G.Adj h₅ c₂
      · by_cases hAL1 : G.Adj h₅ L₁
        · -- **Config `{L₁, c₂}`**: good `C₄` `h₅–L₁–c₁–c₂`, `Σ = 14`.
          have hcard4 : ({h₅, L₁, c₁, c₂} : Finset (Fin 20)).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hne5L1, hne5c1, hne5c2]),
              Finset.card_insert_of_notMem (by simp [(G.ne_of_adj hac1L1).symm, hL1nc2]),
              Finset.card_insert_of_notMem (by simp [G.ne_of_adj hc12]), Finset.card_singleton]
          exact hC4 ⟨h₅, L₁, c₁, c₂, hcard4, hAL1, hac1L1.symm, hc12, hAc2.symm, hn_h5c1,
            (fun h => hnc2L1 h.symm), by omega⟩
        · -- second path-neighbour must be `L₂`.
          have hcardcL : ({c₂, L₂} : Finset (Fin 20)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hac2L2]), Finset.card_singleton]
          have hsub2 : G.neighborFinset h₅ ∩ P ⊆ ({c₂, L₂} : Finset (Fin 20)) := by
            intro x hx
            have hxLcL := hSsub hx
            have hadj : G.Adj h₅ x := (G.mem_neighborFinset h₅ x).mp (Finset.mem_inter.mp hx).1
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxLcL ⊢
            rcases hxLcL with rfl | rfl | rfl
            · exact absurd hadj hAL1
            · exact Or.inl rfl
            · exact Or.inr rfl
          have heq2 := Finset.eq_of_subset_of_card_le hsub2 (hcardcL.trans hh5cinc2.symm).le
          have hAL2 : G.Adj h₅ L₂ := by
            have hmem : L₂ ∈ G.neighborFinset h₅ ∩ P := by rw [heq2]; simp
            exact (G.mem_neighborFinset h₅ L₂).mp (Finset.mem_inter.mp hmem).1
          -- **Config `{c₂, L₂}`**: good triangle `h₅–c₂–L₂`, `Σ = 11`.
          exact hT ⟨h₅, c₂, L₂, hne5c2, G.ne_of_adj hac2L2, hne5L2, hAc2, hac2L2, hAL2, by omega⟩
      · -- `¬Adj h₅ c₂`: both leaves are path-neighbours.
        have hcardLL : ({L₁, L₂} : Finset (Fin 20)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
        have hsub3 : G.neighborFinset h₅ ∩ P ⊆ ({L₁, L₂} : Finset (Fin 20)) := by
          intro x hx
          have hxLcL := hSsub hx
          have hadj : G.Adj h₅ x := (G.mem_neighborFinset h₅ x).mp (Finset.mem_inter.mp hx).1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxLcL ⊢
          rcases hxLcL with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact absurd hadj hAc2
          · exact Or.inr rfl
        have heq3 := Finset.eq_of_subset_of_card_le hsub3 (hcardLL.trans hh5cinc2.symm).le
        have hAL1 : G.Adj h₅ L₁ := by
          have hmem : L₁ ∈ G.neighborFinset h₅ ∩ P := by rw [heq3]; simp
          exact (G.mem_neighborFinset h₅ L₁).mp (Finset.mem_inter.mp hmem).1
        have hAL2 : G.Adj h₅ L₂ := by
          have hmem : L₂ ∈ G.neighborFinset h₅ ∩ P := by rw [heq3]; simp
          exact (G.mem_neighborFinset h₅ L₂).mp (Finset.mem_inter.mp hmem).1
        -- **HARD config `{L₁, L₂}`.**  `h₅ ~ L₁, L₂`, `¬h₅ ~ c₂`; witness-guided two-hub chain.
        -- `h₁` avoids both leaves (`cinc h₁ = 1` on `c₁`).
        have hn_h1L1 : ¬G.Adj h₁ L₁ := by
          intro ha
          rcases hN1char L₁ ((G.mem_neighborFinset h₁ L₁).mpr ha) with h | h
          · exact (G.ne_of_adj hac1L1).symm h
          · exact hL1nIso h
        have hn_h1L2 : ¬G.Adj h₁ L₂ := by
          intro ha
          rcases hN1char L₂ ((G.mem_neighborFinset h₁ L₂).mpr ha) with h | h
          · exact hL2nc1 h
          · exact hL2nIso h
        have hn_h1c2 : ¬G.Adj h₁ c₂ := by
          intro ha
          rcases hN1char c₂ ((G.mem_neighborFinset h₁ c₂).mpr ha) with h | h
          · exact (G.ne_of_adj hc12) h.symm
          · exact hc2nIso h
        -- `L₁`'s only `D`-neighbour is `c₁`, so `¬L₁ ~ L₂`.
        have hnL1L2 : ¬G.Adj L₁ L₂ := by
          have hdisj : Disjoint (G.neighborFinset L₁ ∩ D) (G.neighborFinset L₁ ∩ Dᶜ) := by
            apply Finset.disjoint_left.mpr; intro a ha hb
            exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
          have hunion : (G.neighborFinset L₁ ∩ D) ∪ (G.neighborFinset L₁ ∩ Dᶜ)
              = G.neighborFinset L₁ := by
            rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
          have hsplit : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset L₁ ∩ Dᶜ).card
              = G.degree L₁ := by
            rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
          rw [hL1deg, hL1hub] at hsplit
          intro hadj
          have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩
          have hL2mem : L₂ ∈ G.neighborFinset L₁ ∩ D :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ L₂).mpr hadj, hL2D⟩
          have hsub : ({c₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset L₁ ∩ D := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hc1mem
            · exact hL2mem
          have hcard2 : ({c₁, L₂} : Finset (Fin 20)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [Ne.symm hL2nc1]), Finset.card_singleton]
          have := Finset.card_le_card hsub; rw [hcard2] at this; omega
        -- Extract `h₁`'s two `Iso`-twins `p, q`.
        obtain ⟨p, hpNI, q, hqNI, hpq⟩ :=
          Finset.one_lt_card.mp (by rw [hisoinc3]; norm_num :
            1 < (G.neighborFinset h₁ ∩ Iso).card)
        obtain ⟨hpN1, hpI⟩ := Finset.mem_inter.mp hpNI
        obtain ⟨hqN1, hqI⟩ := Finset.mem_inter.mp hqNI
        have hdp : G.degree p = 3 := (hIsoprop p hpI).1
        have hdq : G.degree q = 3 := (hIsoprop q hqI).1
        have hph1 : G.Adj p h₁ := ((G.mem_neighborFinset h₁ p).mp hpN1).symm
        have hqh1 : G.Adj q h₁ := ((G.mem_neighborFinset h₁ q).mp hqN1).symm
        -- Extract `a' :=` `L₁`'s other hub, `b' :=` `L₂`'s other hub, `k :=` `c₂`'s hub.
        have hL1card2 : 1 < (G.neighborFinset L₁ ∩ Dᶜ).card := by rw [hL1hub]; norm_num
        have hL2card2 : 1 < (G.neighborFinset L₂ ∩ Dᶜ).card := by rw [hL2hub]; norm_num
        obtain ⟨a', ha'mem, ha'ne5⟩ := Finset.exists_mem_ne hL1card2 h₅
        obtain ⟨ha'N, ha'Dc⟩ := Finset.mem_inter.mp ha'mem
        have hAa'L1 : G.Adj L₁ a' := (G.mem_neighborFinset L₁ a').mp ha'N
        have ha'ne1 : a' ≠ h₁ := fun he => hn_h1L1 (he ▸ hAa'L1).symm
        have ha'd : G.degree a' = 4 := hdegOth a' ha'Dc ha'ne1 ha'ne5
        obtain ⟨b', hb'mem, hb'ne5⟩ := Finset.exists_mem_ne hL2card2 h₅
        obtain ⟨hb'N, hb'Dc⟩ := Finset.mem_inter.mp hb'mem
        have hAb'L2 : G.Adj L₂ b' := (G.mem_neighborFinset L₂ b').mp hb'N
        have hb'ne1 : b' ≠ h₁ := fun he => hn_h1L2 (he ▸ hAb'L2).symm
        have hb'd : G.degree b' = 4 := hdegOth b' hb'Dc hb'ne1 hb'ne5
        obtain ⟨k, hkeq⟩ := Finset.card_eq_one.mp hc2hub
        have hkmem : k ∈ G.neighborFinset c₂ ∩ Dᶜ := by
          rw [hkeq]; exact Finset.mem_singleton_self _
        obtain ⟨hkN, hkDc⟩ := Finset.mem_inter.mp hkmem
        have hAkc2 : G.Adj c₂ k := (G.mem_neighborFinset c₂ k).mp hkN
        have hkne1 : k ≠ h₁ := fun he => hn_h1c2 (he ▸ hAkc2).symm
        have hkne5 : k ≠ h₅ := fun he => hAc2 (he ▸ hAkc2).symm
        have hkd : G.degree k = 4 := hdegOth k hkDc hkne1 hkne5
        -- Their unique `Iso`-twins `ιa, ιb, ιk`.
        obtain ⟨ιa, hιa_eq⟩ := Finset.card_eq_one.mp (hOthcap a' ha'Dc ha'ne1 ha'ne5)
        have hιamem : ιa ∈ G.neighborFinset a' ∩ Iso := by
          rw [hιa_eq]; exact Finset.mem_singleton_self _
        obtain ⟨hιaN, hιaI⟩ := Finset.mem_inter.mp hιamem
        have hAa'ιa : G.Adj a' ιa := (G.mem_neighborFinset a' ιa).mp hιaN
        obtain ⟨ιb, hιb_eq⟩ := Finset.card_eq_one.mp (hOthcap b' hb'Dc hb'ne1 hb'ne5)
        have hιbmem : ιb ∈ G.neighborFinset b' ∩ Iso := by
          rw [hιb_eq]; exact Finset.mem_singleton_self _
        obtain ⟨hιbN, hιbI⟩ := Finset.mem_inter.mp hιbmem
        have hAb'ιb : G.Adj b' ιb := (G.mem_neighborFinset b' ιb).mp hιbN
        obtain ⟨ιk, hιk_eq⟩ := Finset.card_eq_one.mp (hOthcap k hkDc hkne1 hkne5)
        have hιkmem : ιk ∈ G.neighborFinset k ∩ Iso := by
          rw [hιk_eq]; exact Finset.mem_singleton_self _
        obtain ⟨hιkN, hιkI⟩ := Finset.mem_inter.mp hιkmem
        have hAkιk : G.Adj k ιk := (G.mem_neighborFinset k ιk).mp hιkN
        -- **Reusable kill via a twin `X`-avoidance.**  A twin `r` of `h₁` avoids `X`
        -- whose only `Iso`-neighbour `w` is not an `h₁`-twin.
        have hn_twin : ∀ X w r : Fin 20, G.neighborFinset X ∩ Iso = {w} → ¬G.Adj h₁ w →
            r ∈ G.neighborFinset h₁ → r ∈ Iso → ¬G.Adj r X := by
          intro X w r hXiso hn_h1w hrN1 hrI ha
          have hmem : r ∈ G.neighborFinset X ∩ Iso :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset X r).mpr ha.symm, hrI⟩
          rw [hXiso, Finset.mem_singleton] at hmem
          exact hn_h1w (hmem ▸ (G.mem_neighborFinset h₁ r).mp hrN1)
        -- **Reusable `(h₁, X)` two-hub kill.**  `h₁`'s cherry `{p, q}` against `X`'s cherry
        -- `{u, w}` (`u` a path-leaf, `w = ιX`), valid once `w ∉ N(h₁)`.
        have hkill_h1 : ∀ X u w : Fin 20, G.degree X = 4 → X ∈ Dᶜ → G.degree u = 3 →
            u ∉ Iso → w ∈ Iso → G.Adj u X → G.Adj w X → ¬G.Adj h₁ u → ¬G.Adj h₁ w →
            ¬G.Adj p X → ¬G.Adj q X → False := by
          intro X u w hXd hXDc hud huIso hwIso huX hwX hn_h1u hn_h1w hn_pX hn_qX
          have hwd : G.degree w = 3 := (hIsoprop w hwIso).1
          exact hth (two_hub_cherry_pair_twenty G h₁ X p q u w hh1d hXd hdp hdq hud hwd
            hph1 hqh1 huX hwX (hnadj1hub X hXDc) hn_h1u hn_h1w hn_pX hn_qX
            (hIso_nadj p hpI u hud) (hIso_nadj p hpI w hwd)
            (hIso_nadj q hqI u hud) (hIso_nadj q hqI w hwd)
            hpq (by rintro rfl; exact huIso hwIso) (by rintro rfl; exact huIso hpI)
            (by rintro rfl; exact hn_h1w hph1.symm) (by rintro rfl; exact huIso hqI)
            (by rintro rfl; exact hn_h1w hqh1.symm))
        -- **The obstruction chain.**  Fire `(h₁, a')` / `(h₁, b')` / `(h₁, k)` in order.
        by_cases hba : G.Adj h₁ ιa
        · by_cases hbb : G.Adj h₁ ιb
          · by_cases hbk : G.Adj h₁ ιk
            · -- Fallback: `ιa, ιb, ιk ∈ N(h₁)`.  Nine degree-`4` hubs each carry one
              -- `Iso`-twin; a pigeonhole into the five `Iso` vertices yields two of them
              -- sharing a twin `t`.  If adjacent, the triangle `F–F'–t` (`Σ = 11`) fires;
              -- otherwise the non-adjacent shared-twin pair is the residual **`deficit_h5`
              -- finisher** (`hstuck`): its two common neighbours give a good `C₄` `Σ = 14`
              -- via the global codegree count — deferred to a separate node.
              have hstuck : ∀ F F' t : Fin 20, F ∈ Dᶜ → F' ∈ Dᶜ → G.degree F = 4 →
                  G.degree F' = 4 → F ≠ F' → ¬G.Adj F F' → t ∈ Iso → G.Adj F t → G.Adj F' t →
                  False := by
                intro _ _ _ _ _ _ _ _ _ _ _ _
                -- Ignore the given `F, F', t`; derive `False` from the ambient world.  The only
                -- deg-`4`/`5` vertices touching a path vertex are `h₁, h₅, a', b', k`; every
                -- other deg-`4` hub is *pure* (adjacent to no path vertex).
                have hdeg4ne3 : ∀ u w : Fin 20, G.degree u = 4 → G.degree w = 3 → u ≠ w := by
                  intro u w hu hw he; rw [he] at hu; omega
                have hIsone : ∀ u w : Fin 20, u ∈ Iso → w ∉ Iso → u ≠ w :=
                  fun u w hu hw he => hw (he ▸ hu)
                have hNL1Dc : G.neighborFinset L₁ ∩ Dᶜ = {h₅, a'} := by
                  have hsub : ({h₅, a'} : Finset (Fin 20)) ⊆ G.neighborFinset L₁ ∩ Dᶜ := by
                    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact Finset.mem_inter.mpr
                        ⟨(G.mem_neighborFinset L₁ x).mpr hAL1.symm, hh5Dc⟩
                    · exact ha'mem
                  have hc2 : ({h₅, a'} : Finset (Fin 20)).card = 2 := by
                    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha'ne5]),
                      Finset.card_singleton]
                  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; omega)).symm
                have hNL2Dc : G.neighborFinset L₂ ∩ Dᶜ = {h₅, b'} := by
                  have hsub : ({h₅, b'} : Finset (Fin 20)) ⊆ G.neighborFinset L₂ ∩ Dᶜ := by
                    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact Finset.mem_inter.mpr
                        ⟨(G.mem_neighborFinset L₂ x).mpr hAL2.symm, hh5Dc⟩
                    · exact hb'mem
                  have hc2 : ({h₅, b'} : Finset (Fin 20)).card = 2 := by
                    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hb'ne5]),
                      Finset.card_singleton]
                  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; omega)).symm
                have hpureL1 : ∀ x : Fin 20, x ∈ Dᶜ → x ≠ h₅ → x ≠ a' → ¬G.Adj x L₁ := by
                  intro x hxDc hxne5 hxnea ha
                  have hmem : x ∈ G.neighborFinset L₁ ∩ Dᶜ :=
                    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ x).mpr ha.symm, hxDc⟩
                  rw [hNL1Dc] at hmem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
                  rcases hmem with rfl | rfl
                  · exact hxne5 rfl
                  · exact hxnea rfl
                have hpurec1 : ∀ x : Fin 20, x ∈ Dᶜ → x ≠ h₁ → ¬G.Adj x c₁ := by
                  intro x hxDc hxne1 ha
                  have hmem : x ∈ G.neighborFinset c₁ ∩ Dᶜ :=
                    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ x).mpr ha.symm, hxDc⟩
                  rw [hNc1Dc, Finset.mem_singleton] at hmem; exact hxne1 hmem
                have hpurec2 : ∀ x : Fin 20, x ∈ Dᶜ → x ≠ k → ¬G.Adj x c₂ := by
                  intro x hxDc hxnek ha
                  have hmem : x ∈ G.neighborFinset c₂ ∩ Dᶜ :=
                    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ x).mpr ha.symm, hxDc⟩
                  rw [hkeq, Finset.mem_singleton] at hmem; exact hxnek hmem
                have hpurecard : ∀ x : Fin 20, ¬G.Adj x L₁ → ¬G.Adj x c₁ → ¬G.Adj x c₂ →
                    (G.neighborFinset x ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card = 0 := by
                  intro x hxL1 hxc1 hxc2
                  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
                  intro w hw; rw [Finset.mem_inter] at hw
                  obtain ⟨hwN, hwm⟩ := hw
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
                  have hadj := (G.mem_neighborFinset x w).mp hwN
                  rcases hwm with rfl | rfl | rfl
                  · exact hxL1 hadj
                  · exact hxc1 hadj
                  · exact hxc2 hadj
                -- The twin map: each deg-`4` hub `≠ h₁, h₅` carries a unique `Iso`-twin.
                classical
                set f : Fin 20 → Fin 20 :=
                  fun x => if hx : (G.neighborFinset x ∩ Iso).Nonempty then hx.choose else x
                  with hfdef
                have hftwin : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ →
                    G.Adj h (f h) ∧ f h ∈ Iso := by
                  intro h hhDc hh1 hh5
                  have hne : (G.neighborFinset h ∩ Iso).Nonempty :=
                    Finset.card_pos.mp (by rw [hOthcap h hhDc hh1 hh5]; norm_num)
                  have hmem : f h ∈ G.neighborFinset h ∩ Iso := by
                    simp only [hfdef, dif_pos hne]; exact hne.choose_spec
                  obtain ⟨hN, hI⟩ := Finset.mem_inter.mp hmem
                  exact ⟨(G.mem_neighborFinset h (f h)).mp hN, hI⟩
                -- Six *pure* hubs (avoiding `h₁, h₅, a', b', k`) pigeonhole into five `Iso` twins.
                have hScard6 : 6 ≤ (Dᶜ.filter
                    (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ a' ∧ h ≠ b' ∧ h ≠ k)).card := by
                  have hcover : Dᶜ ⊆ (Dᶜ.filter
                      (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ a' ∧ h ≠ b' ∧ h ≠ k))
                      ∪ ({h₁, h₅, a', b', k} : Finset (Fin 20)) := by
                    intro x hx
                    by_cases hp : x ≠ h₁ ∧ x ≠ h₅ ∧ x ≠ a' ∧ x ≠ b' ∧ x ≠ k
                    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hp⟩)
                    · refine Finset.mem_union_right _ ?_
                      by_contra hxn
                      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxn
                      exact hp hxn
                  have hcard5 : ({h₁, h₅, a', b', k} : Finset (Fin 20)).card ≤ 5 := by
                    have h1 := Finset.card_insert_le h₁ ({h₅, a', b', k} : Finset (Fin 20))
                    have h2 := Finset.card_insert_le h₅ ({a', b', k} : Finset (Fin 20))
                    have h3 := Finset.card_insert_le a' ({b', k} : Finset (Fin 20))
                    have h4 := Finset.card_insert_le b' ({k} : Finset (Fin 20))
                    rw [Finset.card_singleton] at h4; omega
                  have hunion := Finset.card_union_le (Dᶜ.filter
                    (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ a' ∧ h ≠ b' ∧ h ≠ k))
                    ({h₁, h₅, a', b', k} : Finset (Fin 20))
                  have hcov := Finset.card_le_card hcover
                  rw [hHub11] at hcov; omega
                obtain ⟨F, hFT, F', hF'T, hFF', hff⟩ :=
                  Finset.exists_ne_map_eq_of_card_lt_of_maps_to
                    (s := Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ h ≠ a' ∧ h ≠ b' ∧ h ≠ k))
                    (t := Iso) (f := f) (by rw [hIsocard]; omega)
                    (by
                      intro h hh
                      rw [Finset.mem_coe, Finset.mem_filter] at hh
                      exact Finset.mem_coe.mpr (hftwin h hh.1 hh.2.1 hh.2.2.1).2)
                rw [Finset.mem_filter] at hFT hF'T
                obtain ⟨hFDc, hFne1, hFne5, hFnea, hFneb, hFnek⟩ := hFT
                obtain ⟨hF'Dc, hF'ne1, hF'ne5, hF'nea, hF'neb, hF'nek⟩ := hF'T
                have hdF : G.degree F = 4 := hdegOth F hFDc hFne1 hFne5
                have hdF' : G.degree F' = 4 := hdegOth F' hF'Dc hF'ne1 hF'ne5
                have htwI : f F ∈ Iso := (hftwin F hFDc hFne1 hFne5).2
                have hdegfF : G.degree (f F) = 3 := (hIsoprop (f F) htwI).1
                have hAFt : G.Adj F (f F) := (hftwin F hFDc hFne1 hFne5).1
                have hAF't : G.Adj F' (f F) := by
                  have h := (hftwin F' hF'Dc hF'ne1 hF'ne5).1
                  rwa [← hff] at h
                by_cases hadjFF' : G.Adj F F'
                · exact hT ⟨F, F', f F, hFF', hdeg4ne3 F' (f F) hdF' hdegfF,
                    hdeg4ne3 F (f F) hdF hdegfF, hadjFF', hAF't, hAFt, by omega⟩
                · refine hsv ⟨f F, F, F', L₁, c₁, c₂, hdegfF, hL1deg, hc1deg, hc2deg,
                    hAFt.symm, hAF't.symm, hac1L1.symm, hc12, fun h => hnc2L1 h.symm, ?_,
                    hFF', hIsone (f F) L₁ htwI hL1nIso, hIsone (f F) c₁ htwI hc1nIso,
                    hIsone (f F) c₂ htwI hc2nIso, hdeg4ne3 F L₁ hdF hL1deg,
                    hdeg4ne3 F c₁ hdF hc1deg, hdeg4ne3 F c₂ hdF hc2deg,
                    hdeg4ne3 F' L₁ hdF' hL1deg, hdeg4ne3 F' c₁ hdF' hc1deg,
                    hdeg4ne3 F' c₂ hdF' hc2deg, (G.ne_of_adj hac1L1).symm,
                    G.ne_of_adj hc12, hL1nc2⟩
                  have hsum0 : (∑ p ∈ ({f F, F, F'} : Finset (Fin 20)),
                      (G.neighborFinset p ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card) = 0 := by
                    apply Finset.sum_eq_zero
                    intro p hp
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                    rcases hp with rfl | hpF | hpF'
                    · exact hpurecard (f F) (hIso_nadj (f F) htwI L₁ hL1deg)
                        (hIso_nadj (f F) htwI c₁ hc1deg) (hIso_nadj (f F) htwI c₂ hc2deg)
                    · rw [hpF]
                      exact hpurecard F (hpureL1 F hFDc hFne5 hFnea)
                        (hpurec1 F hFDc hFne1) (hpurec2 F hFDc hFnek)
                    · rw [hpF']
                      exact hpurecard F' (hpureL1 F' hF'Dc hF'ne5 hF'nea)
                        (hpurec1 F' hF'Dc hF'ne1) (hpurec2 F' hF'Dc hF'nek)
                  rw [hsum0, if_neg hadjFF']; omega
              have key : ∃ F F' t : Fin 20, F ∈ Dᶜ ∧ F' ∈ Dᶜ ∧ G.degree F = 4 ∧
                  G.degree F' = 4 ∧ F ≠ F' ∧ t ∈ Iso ∧ G.Adj F t ∧ G.Adj F' t := by
                classical
                set f : Fin 20 → Fin 20 :=
                  fun x => if hx : (G.neighborFinset x ∩ Iso).Nonempty then hx.choose else x
                  with hfdef
                have hftwin : ∀ h ∈ Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅),
                    G.Adj h (f h) ∧ f h ∈ Iso := by
                  intro h hh
                  rw [Finset.mem_filter] at hh
                  obtain ⟨hhDc, hh1, hh5⟩ := hh
                  have hne : (G.neighborFinset h ∩ Iso).Nonempty :=
                    Finset.card_pos.mp (by rw [hOthcap h hhDc hh1 hh5]; norm_num)
                  have hmem : f h ∈ G.neighborFinset h ∩ Iso := by
                    simp only [hfdef, dif_pos hne]; exact hne.choose_spec
                  obtain ⟨hN, hI⟩ := Finset.mem_inter.mp hmem
                  exact ⟨(G.mem_neighborFinset h (f h)).mp hN, hI⟩
                have hScard : (Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅)).card = 9 := by
                  have hcompl : Dᶜ.filter (fun h => ¬(h ≠ h₁ ∧ h ≠ h₅)) = {h₁, h₅} := by
                    ext x
                    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
                      not_and, not_not]
                    constructor
                    · rintro ⟨_, hx⟩
                      by_cases hxh1 : x = h₁
                      · exact Or.inl hxh1
                      · exact Or.inr (hx hxh1)
                    · rintro (rfl | rfl)
                      · exact ⟨hh1Dc, fun hne => absurd rfl hne⟩
                      · exact ⟨hh5Dc, fun _ => rfl⟩
                  have hsum := Finset.card_filter_add_card_filter_not (s := Dᶜ)
                    (fun h => h ≠ h₁ ∧ h ≠ h₅)
                  rw [hcompl, hHub11,
                    Finset.card_insert_of_notMem (by simp [hne15]), Finset.card_singleton] at hsum
                  omega
                obtain ⟨F, hFS, F', hF'S, hFF', hff⟩ :=
                  Finset.exists_ne_map_eq_of_card_lt_of_maps_to
                    (s := Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅))
                    (t := Iso) (f := f) (by rw [hIsocard, hScard]; norm_num)
                    (by
                      intro h hh
                      rw [Finset.mem_coe] at hh
                      exact Finset.mem_coe.mpr (hftwin h hh).2)
                have hAFtw := hftwin F hFS
                have hAF'tw := hftwin F' hF'S
                rw [Finset.mem_filter] at hFS hF'S
                obtain ⟨hFDc, hFne1, hFne5⟩ := hFS
                obtain ⟨hF'Dc, hF'ne1, hF'ne5⟩ := hF'S
                refine ⟨F, F', f F, hFDc, hF'Dc, hdegOth F hFDc hFne1 hFne5,
                  hdegOth F' hF'Dc hF'ne1 hF'ne5, hFF', hAFtw.2, hAFtw.1, ?_⟩
                have hadj := hAF'tw.1
                rwa [← hff] at hadj
              obtain ⟨F, F', t, hFDc, hF'Dc, hdF, hdF', hFF', htI, hAFt, hAF't⟩ := key
              by_cases hAFF' : G.Adj F F'
              · exact hT ⟨F, F', t, hFF', G.ne_of_adj hAF't, G.ne_of_adj hAFt, hAFF', hAF't,
                  hAFt, by have := (hIsoprop t htI).1; omega⟩
              · exact hstuck F F' t hFDc hF'Dc hdF hdF' hFF' hAFF' htI hAFt hAF't
            · exact hkill_h1 k c₂ ιk hkd hkDc hc2deg hc2nIso hιkI hAkc2 hAkιk.symm hn_h1c2 hbk
                (hn_twin k ιk p hιk_eq hbk hpN1 hpI) (hn_twin k ιk q hιk_eq hbk hqN1 hqI)
          · exact hkill_h1 b' L₂ ιb hb'd hb'Dc hL2deg hL2nIso hιbI hAb'L2 hAb'ιb.symm hn_h1L2 hbb
              (hn_twin b' ιb p hιb_eq hbb hpN1 hpI) (hn_twin b' ιb q hιb_eq hbb hqN1 hqI)
        · exact hkill_h1 a' L₁ ιa ha'd ha'Dc hL1deg hL1nIso hιaI hAa'L1 hAa'ιa.symm hn_h1L1 hba
            (hn_twin a' ιa p hιa_eq hba hpN1 hpI) (hn_twin a' ιa q hιa_eq hba hqN1 hqI)

end N20

end ACMax
