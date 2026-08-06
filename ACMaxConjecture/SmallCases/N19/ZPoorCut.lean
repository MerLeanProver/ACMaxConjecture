import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.R5ResidHelpers

/-!
# The reusable `z`-meets-two-poor cut engine (`n = 19`, `|Hub| = 11`)

This file packages the **no-cross pigeonhole cut** that closes the `z`-meets-two-poor deep regimes
(`r ∈ {6, 7}`) uniformly, generalising the `r = 5` no-cross corner of `TwinCert19R5Resid` to the
larger rich pools (where the pigeonhole has strictly more slack).

The engine `two_poor_zleaf_pigeonhole_nineteen` takes a *poor* hub `gstar` with a single twin
`cstar` met by an `M`-edge endpoint `zz`, whose two hub-neighbours are all *poor* (outside `R`), and a
rich pool `R` of size `≥ 5`.  A pigeonhole over `R` (bad rich hubs are those adjacent to `gstar` or
carrying `cstar`, at most `2 + 2 = 4` of them) supplies a rich hub `r` with two twins `a, b` that,
together with `gstar`, `cstar` and the `Z`-leaf `zz`, form a `TwoHubConfig`.

The cross-edge case is handled per-regime by the axiom-clean `cross_z_hub_c4_false_nineteen` of
`TwinCert19R5ResidHelpers`; this file supplies only the no-cross packing.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **The no-cross `Z`-leaf pigeonhole cut (reusable, `r ∈ {6, 7}`).**  Let `gstar` be a *poor* hub
with `N(gstar) ∩ Iso = {cstar}` met by an `M`-edge endpoint `zz`, whose two hub-neighbours are all
outside the rich pool `R` (`hzz_hubs_poor`).  If `5 ≤ |R|`, a pigeonhole over `R` yields a rich hub
`r` non-adjacent to both `gstar` and `cstar`; its two twins `a, b` are then both non-adjacent to
`gstar` (whose only twin is `cstar`), giving a `TwoHubConfig` with `Z`-leaf `d = zz`. -/
theorem two_poor_zleaf_pigeonhole_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (R : Finset (Fin 19))
    (hRdef : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (gstar zz cstar : Fin 19)
    (hgstarHub : gstar ∈ Hub)
    (hzzZ : zz ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hzz_gstar : G.Adj zz gstar)
    (hgstar_iso1 : G.neighborFinset gstar ∩ Iso = {cstar})
    (hzz_hubs_poor : ∀ h ∈ G.neighborFinset zz ∩ Hub, h ∉ R)
    (hRslack : 5 ≤ R.card) :
    TwoHubConfig G := by
  classical
  have hRsub : R ⊆ Hub := by rw [hRdef]; exact Finset.filter_subset _ _
  have hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hRdef, Finset.mem_filter] at ha; exact ha.2
  -- `cstar` facts.
  have hcstar_mem : cstar ∈ G.neighborFinset gstar ∩ Iso := by
    rw [hgstar_iso1]; exact Finset.mem_singleton_self _
  have hcstarIso : cstar ∈ Iso := (Finset.mem_inter.mp hcstar_mem).2
  have hgstar_cstar : G.Adj gstar cstar :=
    (G.mem_neighborFinset gstar cstar).mp (Finset.mem_inter.mp hcstar_mem).1
  -- `gstar` is poor: iso-degree `1`, so `gstar ∉ R`.
  have hgstar_iso1card : (G.neighborFinset gstar ∩ Iso).card = 1 := by
    rw [hgstar_iso1, Finset.card_singleton]
  have hgstarnotR : gstar ∉ R := by
    rw [hRdef, Finset.mem_filter]; rintro ⟨_, h2⟩; omega
  -- `gstar`'s hub-degree `≤ 2` (degree `4 = 1` iso `+ ≥ 1` `Z` `+` hub).
  have hgstar_hubdeg : (G.neighborFinset gstar ∩ Hub).card ≤ 2 := by
    set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
    have hsp := nbr_split_three_nineteen G Hub Iso hdisj gstar
    rw [← hZdef] at hsp
    have hzzmem : zz ∈ G.neighborFinset gstar ∩ Z :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gstar zz).mpr hzz_gstar.symm, hzzZ⟩
    have hZpos : 1 ≤ (G.neighborFinset gstar ∩ Z).card := Finset.card_pos.mpr ⟨zz, hzzmem⟩
    rw [hdeg4 gstar hgstarHub, hgstar_iso1card] at hsp
    omega
  -- Pigeonhole: a rich `r ∈ R` with `¬ G.Adj gstar r ∧ ¬ G.Adj cstar r`.
  have hexr : ∃ r ∈ R, ¬G.Adj gstar r ∧ ¬G.Adj cstar r := by
    by_contra hcon
    push Not at hcon
    -- Every rich hub is adjacent to `gstar` or carries `cstar`.
    have hsub : R ⊆ (G.neighborFinset gstar ∩ Hub)
        ∪ ((G.neighborFinset cstar ∩ Hub).erase gstar) := by
      intro r hr
      have hrHub : r ∈ Hub := hRsub hr
      by_cases hg : G.Adj gstar r
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gstar r).mpr hg, hrHub⟩)
      · have hc := hcon r hr hg
        refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
        · exact fun he => hgstarnotR (he ▸ hr)
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset cstar r).mpr hc, hrHub⟩
    have hcard := Finset.card_le_card hsub
    have hu := Finset.card_union_le (G.neighborFinset gstar ∩ Hub)
      ((G.neighborFinset cstar ∩ Hub).erase gstar)
    have hcstar_hub3 : (G.neighborFinset cstar ∩ Hub).card = 3 := hiso3 cstar hcstarIso
    have hgstar_in_cstar : gstar ∈ G.neighborFinset cstar ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset cstar gstar).mpr hgstar_cstar.symm, hgstarHub⟩
    have herasecard : ((G.neighborFinset cstar ∩ Hub).erase gstar).card = 2 := by
      rw [Finset.card_erase_of_mem hgstar_in_cstar, hcstar_hub3]
    omega
  obtain ⟨r, hrR, hngr, hncr⟩ := hexr
  have hrHub : r ∈ Hub := hRsub hrR
  have hdr : G.degree r = 4 := hdeg4 r hrHub
  -- Two twins `a, b` of `r`.
  have hr2 : 2 ≤ (G.neighborFinset r ∩ Iso).card := hRrich r hrR
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset r ∩ Iso).card)
  have haIso : a ∈ Iso := (Finset.mem_inter.mp ha).2
  have hbIso : b ∈ Iso := (Finset.mem_inter.mp hb).2
  have har : G.Adj a r := ((G.mem_neighborFinset r a).mp (Finset.mem_inter.mp ha).1).symm
  have hbr : G.Adj b r := ((G.mem_neighborFinset r b).mp (Finset.mem_inter.mp hb).1).symm
  -- `a, b ≠ cstar` (they are neighbours of `r`, but `cstar ≁ r`).
  have hancr : a ≠ cstar := by
    intro he; subst he; exact hncr har
  have hbncr : b ≠ cstar := by
    intro he; subst he; exact hncr hbr
  -- `a, b ≁ gstar` (the only twin of `gstar` is `cstar`).
  have hnagstar : ¬G.Adj a gstar := by
    intro had
    have hain : a ∈ G.neighborFinset gstar ∩ Iso :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gstar a).mpr had.symm, haIso⟩
    rw [hgstar_iso1, Finset.mem_singleton] at hain; exact hancr hain
  have hnbgstar : ¬G.Adj b gstar := by
    intro had
    have hbin : b ∈ G.neighborFinset gstar ∩ Iso :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gstar b).mpr had.symm, hbIso⟩
    rw [hgstar_iso1, Finset.mem_singleton] at hbin; exact hbncr hbin
  -- `r ≁ zz` (the hub-neighbours of `zz` are all outside `R`).
  have hnrzz : ¬G.Adj r zz := by
    intro had
    have hrin : r ∈ G.neighborFinset zz ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset zz r).mpr had.symm, hrHub⟩
    exact hzz_hubs_poor r hrin hrR
  -- Assemble the `Z`-leaf `TwoHubConfig` `(h₁, h₂) = (r, gstar)`, leaves `a, b`, twin `cstar`,
  -- fourth leaf `zz`.
  exact two_hub_zleaf_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
    r gstar a b cstar zz hrHub hgstarHub hdr (hdeg4 gstar hgstarHub) haIso hbIso hcstarIso hzzZ
    har hbr hgstar_cstar.symm hzz_gstar (fun h => hngr h.symm) (fun h => hncr h.symm) hnrzz
    hnagstar hnbgstar hab

/-- **The `z`-side `Z`-leaf cut (reusable, `r ∈ {6, 7}` with `S < r + 9`).**  An `M`-edge endpoint
`z` meets exactly two *poor* hubs `hg1, hg2`; if at least one of them carries a private twin
(`hone`), that hub plays `gstar` with `M`-end `zz = z` (whose two hub-neighbours `{hg1, hg2}` are
both poor) and the rich pool (`5 ≤ |R|`) supplies the `Z`-leaf cut.  The hypothesis `hone` holds
whenever the poor-incidence sum exceeds the capacity of the *other* poor hubs, i.e. `S < r + 9`. -/
theorem z_side_poor_cut_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (z : Fin 19) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hg1 hg2 : Fin 19) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hone : 1 ≤ (G.neighborFinset hg1 ∩ Iso).card ∨ 1 ≤ (G.neighborFinset hg2 ∩ Iso).card)
    (hRcard5 : 5 ≤ (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) :
    TwoHubConfig G := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg1notR : hg1 ∉ R := by rw [hRdef, Finset.mem_filter]; rintro ⟨_, h2⟩; omega
  have hg2notR : hg2 ∉ R := by rw [hRdef, Finset.mem_filter]; rintro ⟨_, h2⟩; omega
  have hzg1 : G.Adj z hg1 := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hg1mem).1
  have hzg2 : G.Adj z hg2 := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hg2mem).1
  obtain ⟨_, hzhub2, _⟩ :=
    z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hz
  have hNz : G.neighborFinset z ∩ Hub = {hg1, hg2} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hg1mem
      · exact hg2mem
    · rw [hzhub2, Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton]
  have hzpoor : ∀ h ∈ G.neighborFinset z ∩ Hub, h ∉ R := by
    intro h hh; rw [hNz, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact hg1notR
    · exact hg2notR
  rcases hone with h1 | h2
  · have h1eq : (G.neighborFinset hg1 ∩ Iso).card = 1 := by omega
    obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp h1eq
    exact two_poor_zleaf_pigeonhole_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak R hRdef hg1 z cstar hg1Hub hz hzg1 hcs hzpoor hRcard5
  · have h2eq : (G.neighborFinset hg2 ∩ Iso).card = 1 := by omega
    obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp h2eq
    exact two_poor_zleaf_pigeonhole_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak R hRdef hg2 z cstar hg2Hub hz hzg2 hcs hzpoor hRcard5

end N19

end ACMax
