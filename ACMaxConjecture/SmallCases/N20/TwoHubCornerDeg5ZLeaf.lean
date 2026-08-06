import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.ZVertex

/-!
# Profile-agnostic `Z`-leaf two-hub infrastructure (`n = 20`)

This file generalizes the octahedron-specific `Z`-leaf assembler `two_hub_zleaf_twenty`
(hard-wired to `(12, 6, 48)`) so that it also serves the degree-`5` `e(M) = 1` two-hub corners
`(10, 8, 42)` and `(11, 7, 45)`.

Two reusable, axiom-clean pieces:

* `zfacts_deg5_twenty` — the `M`-edge-endpoint structural facts (`deg z = 3`, meets no twin, meets
  exactly two hubs) for **any** `e(M) = 1` partition with `|Hub| + |Iso| = 18` and `Z`-hub leakage
  `≤ 4`.  Unlike `z_two_hub_nbrs_twenty` it does **not** use the rigid handshake `∑_Hub deg = 48`
  (only the leak bound and the twin structure), so it applies verbatim to the deg-`5` profiles.

* `two_hub_zleaf_gen_twenty` — the `Z`-leaf `TwoHubConfig` assembler with the `z`-facts abstracted
  as hypotheses (`deg z = 3`, `N(z) ∩ Iso = ∅`) rather than derived from the octahedron profile.
  Given two non-adjacent degree-`4` hubs, two private twins of the first, one private twin of the
  second, and an `M`-end `z` met by the second and avoided by the first, it packs the
  `TwoHubConfig` with fourth leaf `d = z`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **`M`-edge-endpoint facts for the deg-`5` `e(M) = 1` profiles.**  For any partition with
`|Hub| + |Iso| = 18` (so `|Z| = 2`), isolated twins of degree `3` meeting exactly three hubs, all
degrees `≥ 3`, and `Z`-hub leakage `≤ 4`: every `Z`-vertex `z` meets no twin, meets exactly two
hubs, and has degree `3`. -/
theorem zfacts_deg5_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4) :
    ∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)),
      (G.neighborFinset z ∩ Iso).card = 0 ∧ (G.neighborFinset z ∩ Hub).card = 2 ∧
        G.degree z = 3 := by
  classical
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZeq : Z = (Hub ∪ Iso)ᶜ := by
    rw [hZdef]; ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
  have hUcard : (Hub ∪ Iso).card = 18 := by
    rw [Finset.card_union_of_disjoint hdisj]; exact hsum18
  have hZcard : Z.card = 2 := by
    rw [hZeq, Finset.card_compl, Fintype.card_fin, hUcard]
  -- A twin's neighbourhood lies entirely in `Hub`.
  have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
    intro t ht
    have hcard3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
    have hdt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard3, hdt])
    rw [← heq]; exact Finset.inter_subset_right
  -- Each `Z`-vertex meets no twin.
  have hiso0 : ∀ z ∈ Z, (G.neighborFinset z ∩ Iso).card = 0 := by
    intro z hz
    rw [Finset.card_eq_zero]
    ext x; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hxz hxi
    have hzx : z ∈ G.neighborFinset x := by
      rw [G.mem_neighborFinset, SimpleGraph.adj_comm]; exact (G.mem_neighborFinset _ _).mp hxz
    have hzHub := htwinHub x hxi hzx
    have hznotHub : z ∉ Hub := by
      rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
    exact hznotHub hzHub
  -- Each `Z`-vertex has at most one `Z`-neighbour.
  have hzZle : ∀ z ∈ Z, (G.neighborFinset z ∩ Z).card ≤ 1 := by
    intro z hz
    have hsub : G.neighborFinset z ∩ Z ⊆ Z.erase z := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hz, hZcard] at this; omega
  have hpart : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
      + (G.neighborFinset v ∩ Z).card = G.degree v := fun v =>
    nbr_split_three_twenty G Hub Iso hdisj v
  have hzhub : ∀ z ∈ Z, 2 ≤ (G.neighborFinset z ∩ Hub).card := by
    intro z hz
    have h0 := hiso0 z hz; have hZle := hzZle z hz; have hsp := hpart z; have hd := hdeg3 z
    omega
  -- The `Z`-hub incidence is `≤ 4` (cross-counted from the leak bound).
  have hsum_le4 : ∑ z ∈ Z, (G.neighborFinset z ∩ Hub).card ≤ 4 := by
    rw [← cross_count_twenty G Hub Z]; exact hleak
  intro z hz
  have hhub2 : (G.neighborFinset z ∩ Hub).card = 2 := by
    have hge := hzhub z hz
    have hae := Finset.add_sum_erase Z (fun w => (G.neighborFinset w ∩ Hub).card) hz
    have heraseGe : 2 ≤ ∑ w ∈ Z.erase z, (G.neighborFinset w ∩ Hub).card := by
      have hcardE : (Z.erase z).card = 1 := by rw [Finset.card_erase_of_mem hz, hZcard]
      calc (2 : ℕ) = ∑ _w ∈ Z.erase z, 2 := by
            rw [Finset.sum_const, hcardE, smul_eq_mul, one_mul]
        _ ≤ ∑ w ∈ Z.erase z, (G.neighborFinset w ∩ Hub).card :=
            Finset.sum_le_sum (fun w hw => hzhub w (Finset.mem_of_mem_erase hw))
    omega
  have h0 := hiso0 z hz
  have hZle := hzZle z hz
  have hsp := hpart z
  have hd := hdeg3 z
  exact ⟨h0, hhub2, by omega⟩

/-- **The profile-agnostic `Z`-leaf two-hub assembler.**  Identical to `two_hub_zleaf_twenty` but
with the `M`-end `z`-facts (`deg z = 3`, `N(z) ∩ Iso = ∅`) supplied as hypotheses rather than derived
from the rigid `(12, 6, 48)` handshake, so it also serves the degree-`5` `e(M) = 1` corners.  Packs a
`TwoHubConfig` whose fourth leaf `d = z` is an `M`-edge endpoint (invisible to the `Iso`-only
`hno2hub`). -/
theorem two_hub_zleaf_gen_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (h₁ h₂ a b c z : Fin 20)
    (hh₁Hub : h₁ ∈ Hub) (hh₂Hub : h₂ ∈ Hub)
    (hdh₁ : G.degree h₁ = 4) (hdh₂ : G.degree h₂ = 4)
    (haIso : a ∈ Iso) (hbIso : b ∈ Iso) (hcIso : c ∈ Iso)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hzdeg3 : G.degree z = 3) (hziso0 : (G.neighborFinset z ∩ Iso).card = 0)
    (ha1 : G.Adj a h₁) (hb1 : G.Adj b h₁) (hc2 : G.Adj c h₂) (hz2 : G.Adj z h₂)
    (hn12 : ¬G.Adj h₁ h₂) (hn1c : ¬G.Adj h₁ c) (hn1z : ¬G.Adj h₁ z)
    (hna2 : ¬G.Adj a h₂) (hnb2 : ¬G.Adj b h₂) (hab : a ≠ b) :
    TwoHubConfig G := by
  classical
  have hziso0' : G.neighborFinset z ∩ Iso = ∅ := Finset.card_eq_zero.mp hziso0
  -- `z` meets no twin.
  have hz_notwin : ∀ t ∈ Iso, ¬G.Adj z t := by
    intro t htIso he
    have : t ∈ G.neighborFinset z ∩ Iso :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z t).mpr he, htIso⟩
    rw [hziso0'] at this; exact Finset.notMem_empty t this
  -- Twins meet only hubs, so two twins are never adjacent.
  have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
    intro t ht
    have hcard3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
    have hdt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard3, hdt])
    rw [← heq]; exact Finset.inter_subset_right
  have htwin_nonadj : ∀ s ∈ Iso, ∀ t ∈ Iso, ¬G.Adj s t := by
    intro s hs t ht he
    have : t ∈ Hub := htwinHub s hs ((G.mem_neighborFinset s t).mpr he)
    exact Finset.disjoint_left.mp hdisj this ht
  have hznotHub : z ∉ Hub := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hzZ; exact hzZ.2.1
  have hznotIso : z ∉ Iso := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hzZ; exact hzZ.2.2
  have htwin_notHub : ∀ t ∈ Iso, t ∉ Hub := fun t ht he => Finset.disjoint_left.mp hdisj he ht
  have hda : G.degree a = 3 := hisodeg3 a haIso
  have hdb : G.degree b = 3 := hisodeg3 b hbIso
  have hdc : G.degree c = 3 := hisodeg3 c hcIso
  have hnac : ¬G.Adj a c := htwin_nonadj a haIso c hcIso
  have hnbc : ¬G.Adj b c := htwin_nonadj b hbIso c hcIso
  have hnaz : ¬G.Adj a z := fun he => hz_notwin a haIso he.symm
  have hnbz : ¬G.Adj b z := fun he => hz_notwin b hbIso he.symm
  have ne_h₁h₂ : h₁ ≠ h₂ := fun he => hn1c (he ▸ hc2.symm)
  have ne_h₁a : h₁ ≠ a := fun he => htwin_notHub a haIso (he ▸ hh₁Hub)
  have ne_h₁b : h₁ ≠ b := fun he => htwin_notHub b hbIso (he ▸ hh₁Hub)
  have ne_h₁c : h₁ ≠ c := fun he => htwin_notHub c hcIso (he ▸ hh₁Hub)
  have ne_h₁z : h₁ ≠ z := fun he => hznotHub (he ▸ hh₁Hub)
  have ne_h₂a : h₂ ≠ a := fun he => htwin_notHub a haIso (he ▸ hh₂Hub)
  have ne_h₂b : h₂ ≠ b := fun he => htwin_notHub b hbIso (he ▸ hh₂Hub)
  have ne_h₂c : h₂ ≠ c := fun he => htwin_notHub c hcIso (he ▸ hh₂Hub)
  have ne_h₂z : h₂ ≠ z := fun he => hznotHub (he ▸ hh₂Hub)
  have ne_ac : a ≠ c := fun he => hna2 (he ▸ hc2)
  have ne_bc : b ≠ c := fun he => hnb2 (he ▸ hc2)
  have ne_az : a ≠ z := fun he => hznotIso (he ▸ haIso)
  have ne_bz : b ≠ z := fun he => hznotIso (he ▸ hbIso)
  have ne_cz : c ≠ z := fun he => hznotIso (he ▸ hcIso)
  exact ⟨h₁, h₂, a, b, c, z, hdh₁, hdh₂, hda, hdb, hdc, hzdeg3,
    ha1, hb1, hc2, hz2, hn12, hn1c, hn1z, hna2, hnac, hnaz, hnb2, hnbc, hnbz,
    ne_h₁h₂, ne_h₁a, ne_h₁b, ne_h₁c, ne_h₁z, ne_h₂a, ne_h₂b, ne_h₂c, ne_h₂z,
    hab, ne_ac, ne_az, ne_bc, ne_bz, ne_cz⟩

end N20

end ACMax
