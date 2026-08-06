import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.Deg5Pack
import ACMaxConjecture.SmallCases.N20.Deg5RichCap
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041OctaStruct

/-!
# The deficit (isoDeg `f = 4`) kill for the share-2 (11,7,45) corner (`n = 20`)

The `isoDeg f = 4` branch of `ledger_profile_1041_twenty`: the unique degree-`5`
hub `f` misses one `Iso` slot, every degree-`4` hub keeps isoDeg `≥ 1`, and the
isoDeg-`≥ 3`/`≥ 4` layer counts sum to `2` (`hn34`).  The bare profile facts are
consistent (a countermodel exists), so the kill leans on the blocked-branch
context: the rigid `2+1+2` octahedron partition
(`octahedron_struct_share2_1041_twenty`, which is `f`-independent) pins the
second hub `r_z` of the `M`-end `z` inside the rich set.  The tight layer count
then forbids the hub edge `g ∼ r_z`: such an edge would force `isoDeg g = 3`,
tightness of `hn34` would produce a second isoDeg-`≥ 3` degree-`4` hub `x`,
the rich cap (`hshare` + `hno2hub`) would force `g ∼ x`, the degree budget of
`g` would identify `x = r_z`, and then `deg r_z = 4` overflows on three twins
plus `z` plus `g`.  With `g` and `r_z` non-adjacent, the rich `Z`-leaf packer
on `(g, r_z, z)` assembles a `TwoHubConfig` — the same exit as the
anchor-saturated `|R| = 4` kill (`anchor_sat_kill_twenty`).
-/

namespace ACMax

open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The deficit kill.**  In the blocked rigid tie of the `(11,7,45)` corner
with the deficit ledger (isoDeg `f = 4`, every degree-`4` hub at isoDeg `≥ 1`,
layer counts `n₃ + n₄ = 2`), the rich packer on `(g, r_z, z)` forces a
`TwoHubConfig`. -/
theorem deficit_kill_1041_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
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
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
    (hR5ge : 5 ≤ (Hub.filter
      (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card)
    (f : Fin 20) (_hfHub : f ∈ Hub) (_hfd : G.degree f = 5)
    (_hf4 : (G.neighborFinset f ∩ Iso).card = 4)
    (_hpoor1 : ∀ h ∈ Hub, G.degree h = 4 → 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hn34 : (Hub.filter (fun h => G.degree h = 4 ∧
        3 ≤ (G.neighborFinset h ∩ Iso).card)).card +
      (Hub.filter (fun h => G.degree h = 4 ∧
        4 ≤ (G.neighborFinset h ∩ Iso).card)).card = 2) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  -- === Step 1: the rigid `2+1+2` octahedron partition (`f`-independent). ===
  obtain ⟨_c, _r_t, r_z, _a, _b, hR5, -, -, -, -, -, -, -, -, hr_zz, -, -, -, -,
      hr_zHub, hr_zd4, -, -, -, -⟩ :=
    octahedron_struct_share2_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
      hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ
      hz2 hgz hg2 hpoor hshared hblock hR5ge
  -- === Step 2: `r_z` is rich — it lies in the pinned rich set. ===
  have hr_zR : r_z ∈ Hub.filter (fun h => G.degree h = 4 ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hR5]
    simp
  have hr_ziso : 2 ≤ (G.neighborFinset r_z ∩ Iso).card := (Finset.mem_filter.mp hr_zR).2.2
  have hzrz : G.Adj z r_z := hr_zz.symm
  have hgne : g ≠ r_z := by
    rintro rfl
    exact hgz hr_zz
  -- === Step 3: `¬G.Adj g r_z` — the deficit layer count forbids the hub edge. ===
  have hngr : ¬G.Adj g r_z := by
    intro hadj
    have hr_znotIso : r_z ∉ Iso := fun hc => Finset.disjoint_left.mp hdisj hr_zHub hc
    have hr_zNg : r_z ∈ G.neighborFinset g := (G.mem_neighborFinset g r_z).mpr hadj
    -- (a) The hub edge caps `isoDeg g` at exactly `3`.
    have hsubg : G.neighborFinset g ∩ Iso ⊆ (G.neighborFinset g).erase r_z := by
      intro t ht
      obtain ⟨htN, htIso⟩ := Finset.mem_inter.mp ht
      exact Finset.mem_erase.mpr ⟨fun he => hr_znotIso (he ▸ htIso), htN⟩
    have hgiso3 : (G.neighborFinset g ∩ Iso).card = 3 := by
      have hcardle := Finset.card_le_card hsubg
      rw [Finset.card_erase_of_mem hr_zNg, G.card_neighborFinset_eq_degree, hgd] at hcardle
      omega
    -- (b) Tightness of the layer count yields a second isoDeg-`≥ 3` hub `x ≠ g`.
    set F3 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4 ∧
      3 ≤ (G.neighborFinset h ∩ Iso).card) with hF3def
    set F4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4 ∧
      4 ≤ (G.neighborFinset h ∩ Iso).card) with hF4def
    have hgF3 : g ∈ F3 := by
      rw [hF3def, Finset.mem_filter]
      exact ⟨hg, hgd, hgiso⟩
    have hgF4 : g ∉ F4 := by
      rw [hF4def, Finset.mem_filter]
      rintro ⟨-, -, h4⟩
      omega
    have hxex : ∃ x ∈ F3, x ≠ g := by
      by_contra hcon
      push Not at hcon
      have hF3eq : F3 = {g} := Finset.Subset.antisymm
        (fun x hx => Finset.mem_singleton.mpr (hcon x hx))
        (Finset.singleton_subset_iff.mpr hgF3)
      have hF3card : F3.card = 1 := by rw [hF3eq]; exact Finset.card_singleton g
      have hF4card : F4.card = 1 := by omega
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hF4card
      have hyF4 : y ∈ F4 := by rw [hy]; exact Finset.mem_singleton_self y
      have hyF3 : y ∈ F3 := by
        rw [hF4def, Finset.mem_filter] at hyF4
        rw [hF3def, Finset.mem_filter]
        exact ⟨hyF4.1, hyF4.2.1, by omega⟩
      rw [hF3eq, Finset.mem_singleton] at hyF3
      rw [hyF3] at hyF4
      exact hgF4 hyF4
    obtain ⟨x, hxF3, hxg⟩ := hxex
    rw [hF3def, Finset.mem_filter] at hxF3
    obtain ⟨hxHub, hxd4, hxiso3⟩ := hxF3
    -- (c) `g ∼ x`: two non-adjacent isoDeg-`≥ 3` hubs violate the rich cap.
    have hgx : G.Adj g x := by
      by_contra hnadj
      have hcap := isoDeg_le_two_of_nonadj_rich_twenty G Hub Iso hshare hno2hub g x hg hxHub
        hgd hxd4 (Ne.symm hxg) hnadj hgiso
      omega
    -- (d) `x = r_z`: a second hub-neighbour would overflow `deg g = 4`.
    have hxrz : x = r_z := by
      by_contra hne
      have hxNg : x ∈ G.neighborFinset g := (G.mem_neighborFinset g x).mpr hgx
      have hxnotIso : x ∉ Iso := fun hc => Finset.disjoint_left.mp hdisj hxHub hc
      have hxni : x ∉ insert r_z (G.neighborFinset g ∩ Iso) := by
        rw [Finset.mem_insert]
        rintro (h | h)
        · exact hne h
        · exact hxnotIso (Finset.mem_inter.mp h).2
      have hrni : r_z ∉ G.neighborFinset g ∩ Iso := fun h =>
        hr_znotIso (Finset.mem_inter.mp h).2
      have hsub : insert x (insert r_z (G.neighborFinset g ∩ Iso)) ⊆ G.neighborFinset g := by
        intro u hu
        rw [Finset.mem_insert, Finset.mem_insert] at hu
        rcases hu with rfl | rfl | hu
        · exact hxNg
        · exact hr_zNg
        · exact (Finset.mem_inter.mp hu).1
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hxni, Finset.card_insert_of_notMem hrni, hgiso3,
        G.card_neighborFinset_eq_degree, hgd] at hcard
      omega
    -- (e) `deg r_z = 4` overflows: three twins plus `z` plus `g`.
    rw [hxrz] at hxiso3
    have hgNrz : g ∈ G.neighborFinset r_z := (G.mem_neighborFinset r_z g).mpr hadj.symm
    have hzNrz : z ∈ G.neighborFinset r_z := (G.mem_neighborFinset r_z z).mpr hr_zz
    have hzns : z ∉ Hub ∪ Iso := (Finset.mem_sdiff.mp hzZ).2
    have hgnotIso : g ∉ Iso := fun hc => Finset.disjoint_left.mp hdisj hg hc
    have hzni : z ∉ insert g (G.neighborFinset r_z ∩ Iso) := by
      rw [Finset.mem_insert]
      rintro (h | h)
      · refine hzns (Finset.mem_union_left _ ?_)
        rw [h]
        exact hg
      · exact hzns (Finset.mem_union_right _ (Finset.mem_inter.mp h).2)
    have hgni : g ∉ G.neighborFinset r_z ∩ Iso := fun h =>
      hgnotIso (Finset.mem_inter.mp h).2
    have hsub : insert z (insert g (G.neighborFinset r_z ∩ Iso)) ⊆ G.neighborFinset r_z := by
      intro u hu
      rw [Finset.mem_insert, Finset.mem_insert] at hu
      rcases hu with rfl | rfl | hu
      · exact hzNrz
      · exact hgNrz
      · exact (Finset.mem_inter.mp hu).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hzni, Finset.card_insert_of_notMem hgni,
      G.card_neighborFinset_eq_degree, hr_zd4] at hcard
    omega
  -- === Step 4: the rich packer on `(g, r_z, z)` assembles the `TwoHubConfig`. ===
  obtain ⟨h₁', h₂', a', b', c', z', hh₁', hh₂', hd₁', hd₂', ha', hb', hc', hzZ', ha1', hb1',
      hc2', hz2', hn12', hn1c', hn1z', hna2', hnb2', hab'⟩ :=
    zleaf_pack_rich_twenty G Hub Iso hiso3 hisodeg3 hshare g r_z z hg hr_zHub hgd hr_zd4 hzZ
      hgne hngr hgiso hr_ziso hzrz hgz
  obtain ⟨hziso0', -, hzdeg3'⟩ :=
    zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak z' hzZ'
  exact Or.inr (Or.inr (Or.inl (two_hub_zleaf_gen_twenty G Hub Iso hiso3 hdisj hisodeg3 h₁'
    h₂' a' b' c' z' hh₁' hh₂' hd₁' hd₂' ha' hb' hc' hzZ' hzdeg3' hziso0' ha1' hb1' hc2' hz2'
    hn12' hn1c' hn1z' hna2' hnb2' hab')))

end N20

end ACMax
