import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.R5ResidHelpers
import ACMaxConjecture.SmallCases.N20.ZPoorCut
import ACMaxConjecture.SmallCases.N20.ZPoorR7

/-!
# The all-poor-at-exactly-one residual for the `n = 20` octahedron (`r ∈ {4, 5}`, `S = 6 + r`)

For the rigid all-degree-`4` `(|Hub|, |Iso|) = (12, 6)` profile, the rich pool
`R = {h ∈ Hub : |N(h) ∩ Iso| ≥ 2}` and its iso-incidence sum `S = ∑_R |N ∩ Iso|` satisfy
`S ≥ 6 + r` (the `12 − r` poor hubs absorb at most one of the `18` iso-incidences each).  This
file kills the boundary `S = 6 + r` for `r ∈ {4, 5}` — the worlds where **every poor hub carries
exactly one twin** and the iso-degree-`4` extraction of the rich-count chain fails (designs
`{4,2,2,2}` / `{3,3,2,2}` at `r = 4`, `{3,2,2,2,2}` at `r = 5`).

The dichotomy runs over the four `Z`-hubs (the hub-neighbours of the two `M`-edge endpoints,
pairwise distinct by `no_hub_adj_both_mends_twenty`):

* **all four poor** — each carries exactly one twin `cᵢ`; a column/aggregate double count
  (were `R` covered by `N(gᵢ) ∪ N(cᵢ)` in every column, then `4(r − 2) ≤ ∑_R |N ∩ ZH| ≤ 3r − 6`,
  impossible for `r ≥ 3`) supplies a rich hub avoiding a full column, which packs a `Z`-leaf
  `TwoHubConfig`;
* **some `Z`-hub rich** — the `A3` pool (`≤ 2` rich hubs of iso-degree `≥ 3`,
  `rich_a3_count_le_two_twenty`) is read off the designs: an iso-degree-`4` hub or an adjacent
  iso-degree-`3` pair has a pinned neighbourhood avoiding the rich `Z`-hub and its `M`-end (a
  non-adjacent `3,3`-pair contradicts `hno2hub`); the lone iso-degree-`3` hub of the `r = 5`
  design either avoids them too, or its single non-iso slot is pinned into `{g, z}` and the kill
  routes through the other `M`-end (rich hub there → `Z`-leaf assembly; both poor → the
  `|R| = 5` pigeonhole cut `two_poor_zleaf_pigeonhole_twenty`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The rich-partner `Z`-leaf assembly.**  A hub `h₁` of iso-degree `≥ 3`, non-adjacent to a
rich hub `g` met by an `M`-edge endpoint `zz` and non-adjacent to `zz` itself, packs a `Z`-leaf
`TwoHubConfig`: `h₁` keeps two private twins against `g` and `g` keeps one private twin against
`h₁` (`hshare`), with `zz` as the fourth leaf. -/
theorem rich_partner_zleaf_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (h₁ g zz : Fin 20) (hh₁Hub : h₁ ∈ Hub) (hgHub : g ∈ Hub)
    (hzzZ : zz ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hh₁3 : 3 ≤ (G.neighborFinset h₁ ∩ Iso).card)
    (hg2 : 2 ≤ (G.neighborFinset g ∩ Iso).card)
    (hzzg : G.Adj zz g) (hne : h₁ ≠ g) (hnadj : ¬G.Adj h₁ g) (hnz : ¬G.Adj h₁ zz) :
    TwoHubConfig G := by
  classical
  obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, hna2, hnb2⟩ :=
    exists_two_private_twins_twenty G Hub Iso hshare h₁ g hh₁Hub hgHub
      (hdeg4 h₁ hh₁Hub) (hdeg4 g hgHub) hne hnadj hh₁3
  obtain ⟨c, hcIso, hcg, hch₁⟩ :=
    exists_one_private_twin_twenty G Hub Iso hshare g h₁ hgHub hh₁Hub
      (hdeg4 g hgHub) (hdeg4 h₁ hh₁Hub) hne hnadj hg2
  exact two_hub_zleaf_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
    h₁ g a b c zz hh₁Hub hgHub (hdeg4 h₁ hh₁Hub) (hdeg4 g hgHub) haIso hbIso hcIso hzzZ
    ha1 hb1 hcg hzzg hnadj hch₁ hnz hna2 hnb2 hab

/-- **The poor-one-column `Z`-leaf assembly.**  In the all-poor-at-exactly-one world a poor hub
`gstar` carries a single twin `cstar` and is met by an `M`-edge endpoint `zz`; a rich hub `h`
avoiding `gstar`, `cstar` and `zz` packs a `Z`-leaf `TwoHubConfig` — its two twins are
automatically private, since `gstar`'s only twin is `cstar ∉ N(h)`. -/
theorem poor_one_column_zleaf_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (h gstar cstar zz : Fin 20) (hhHub : h ∈ Hub) (hgstarHub : gstar ∈ Hub)
    (hzzZ : zz ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hzzg : G.Adj zz gstar) (hgiso1 : G.neighborFinset gstar ∩ Iso = {cstar})
    (hh2 : 2 ≤ (G.neighborFinset h ∩ Iso).card)
    (hngh : ¬G.Adj gstar h) (hnch : ¬G.Adj cstar h) (hnhzz : ¬G.Adj h zz) :
    TwoHubConfig G := by
  classical
  have hcstar_mem : cstar ∈ G.neighborFinset gstar ∩ Iso := by
    rw [hgiso1]; exact Finset.mem_singleton_self _
  have hcstarIso : cstar ∈ Iso := (Finset.mem_inter.mp hcstar_mem).2
  have hgstar_cstar : G.Adj gstar cstar :=
    (G.mem_neighborFinset gstar cstar).mp (Finset.mem_inter.mp hcstar_mem).1
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset h ∩ Iso).card)
  have haIso : a ∈ Iso := (Finset.mem_inter.mp ha).2
  have hbIso : b ∈ Iso := (Finset.mem_inter.mp hb).2
  have hah : G.Adj a h := ((G.mem_neighborFinset h a).mp (Finset.mem_inter.mp ha).1).symm
  have hbh : G.Adj b h := ((G.mem_neighborFinset h b).mp (Finset.mem_inter.mp hb).1).symm
  have hanc : a ≠ cstar := fun he => hnch (he ▸ hah)
  have hbnc : b ≠ cstar := fun he => hnch (he ▸ hbh)
  have hnag : ¬G.Adj a gstar := by
    intro had
    have hain : a ∈ G.neighborFinset gstar ∩ Iso :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gstar a).mpr had.symm, haIso⟩
    rw [hgiso1, Finset.mem_singleton] at hain; exact hanc hain
  have hnbg : ¬G.Adj b gstar := by
    intro had
    have hbin : b ∈ G.neighborFinset gstar ∩ Iso :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gstar b).mpr had.symm, hbIso⟩
    rw [hgiso1, Finset.mem_singleton] at hbin; exact hbnc hbin
  exact two_hub_zleaf_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
    h gstar a b cstar zz hhHub hgstarHub (hdeg4 h hhHub) (hdeg4 gstar hgstarHub)
    haIso hbIso hcstarIso hzzZ hah hbh hgstar_cstar.symm hzzg
    (fun hadj => hngh hadj.symm) (fun hadj => hnch hadj.symm) hnhzz hnag hnbg hab

/-- **The all-poor-at-exactly-one residual kill (`r ∈ {4, 5}`, `S = 6 + r`).**  In the rigid
all-degree-`4` `(12, 6)` octahedron world with rich count `r ∈ {4, 5}` and rich iso-incidence
sum exactly `6 + r` (equivalently: every poor hub carries exactly one twin), a boundary cut
configuration (`ZPoorCutConfig`) always exists.  If all four `Z`-hubs are poor, a column double
count over the four `(gᵢ, cᵢ)` pairs produces a rich hub avoiding a full column
(`poor_one_column_zleaf_twenty`); otherwise a rich `Z`-hub is paired against an iso-degree-`≥ 3`
partner extracted from the `S = 6 + r` designs (`rich_partner_zleaf_twenty`), with the `r = 5`
lone iso-degree-`3` corner routed through the other `M`-end and, in the both-poor sub-case, the
`|R| = 5` pigeonhole cut. -/
theorem all_poor_one_resid_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hr45 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 4 ∨
      (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5)
    (hSeq : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card
      = 6 + (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) :
    ZPoorCutConfig G := by
  classical
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 20) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  have hRPcard : R.card + P.card = 12 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub] at this; exact this
  have hsplitRP : (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
      + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
    rw [hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum18
  have hPle1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg; rw [hPdef, Finset.mem_filter] at hg; omega
  -- Every poor hub carries exactly one twin: `∑_P = 18 − S = 12 − r = |P|`, each term `≤ 1`.
  have hpoor1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hgP
    have he := Finset.add_sum_erase P (fun a => (G.neighborFinset a ∩ Iso).card) hgP
    have hrest : ∑ a ∈ P.erase g, (G.neighborFinset a ∩ Iso).card ≤ P.card - 1 := by
      calc ∑ a ∈ P.erase g, (G.neighborFinset a ∩ Iso).card
          ≤ ∑ _a ∈ P.erase g, 1 :=
            Finset.sum_le_sum (fun a ha => hPle1 a (Finset.mem_of_mem_erase ha))
        _ = (P.erase g).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ = P.card - 1 := by rw [Finset.card_erase_of_mem hgP]
    have hgle := hPle1 g hgP
    omega
  -- The two `M`-edge endpoints and their hub-neighbour pairs.
  have hZcard : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)).card = 2 :=
    z_card_two_twenty Hub Iso hdisj hHub hIso
  obtain ⟨z1, z2, hz12, hZpair⟩ := Finset.card_eq_two.mp hZcard
  have hz1Z : z1 ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) := by
    rw [hZpair]; exact Finset.mem_insert_self _ _
  have hz2Z : z2 ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) := by
    rw [hZpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hnoboth : ∀ h ∈ Hub, ¬(G.Adj h z1 ∧ G.Adj h z2) := fun h hh =>
    no_hub_adj_both_mends_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak hT h hh z1 hz1Z z2 hz2Z hz12
  -- **The rich-`Z`-hub engine**: a rich hub `g` met by an `M`-end `zz` (other `M`-end `zo`)
  -- always yields the cut, by the `A3` design analysis.
  have mainB : ∀ g zz zo : Fin 20, g ∈ Hub →
      zz ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) →
      zo ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) → zz ≠ zo →
      (∀ h ∈ Hub, ¬(G.Adj h zz ∧ G.Adj h zo)) → G.Adj zz g →
      2 ≤ (G.neighborFinset g ∩ Iso).card → ZPoorCutConfig G := by
    intro g zz zo hgHub hzzZ hzoZ hzzo hnb hzzg hgrich
    have hzznotHub : zz ∉ Hub := by
      have h := hzzZ; rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h; exact h.2.1
    have hzznotIso : zz ∉ Iso := by
      have h := hzzZ; rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h; exact h.2.2
    have hzonotHub : zo ∉ Hub := by
      have h := hzoZ; rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h; exact h.2.1
    have hzonotIso : zo ∉ Iso := by
      have h := hzoZ; rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h; exact h.2.2
    have hgnotIso : g ∉ Iso := Finset.disjoint_left.mp hdisj hgHub
    -- The iso-degree-`≥ 3` pool `A3` and the design split.
    set A3 : Finset (Fin 20) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      with hA3def
    have hA3subR : A3 ⊆ R := Finset.filter_subset _ _
    have hA3le2 : A3.card ≤ 2 := by
      have heq : A3
          = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hA3def, hRdef, Finset.filter_filter]
        apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_twenty G Hub Iso hdisj hshare hno2hub
    set B : Finset (Fin 20) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card)
      with hBdef
    have hAsplit : (∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card)
        + ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 6 + R.card := by
      rw [hA3def, hBdef,
        Finset.sum_filter_add_sum_filter_not R (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)]
      exact hSeq
    have hBval : ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 2 * B.card := by
      rw [Finset.sum_congr rfl (fun r hr => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hBdef, Finset.mem_filter] at hr
      have h2 : 2 ≤ (G.neighborFinset r ∩ Iso).card := ((hRmem r).mp hr.1).2
      omega
    have hcards : A3.card + B.card = R.card := by
      have := Finset.card_filter_add_card_filter_not (s := R)
        (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      rw [← hA3def, ← hBdef] at this; exact this
    have hTge : 3 * A3.card ≤ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card := by
      calc 3 * A3.card = ∑ _r ∈ A3, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card := by
            apply Finset.sum_le_sum; intro r hr
            rw [hA3def, Finset.mem_filter] at hr; exact hr.2
    have hTle : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ 4 * A3.card := by
      calc ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ ∑ _r ∈ A3, 4 := by
            apply Finset.sum_le_sum; intro r hr
            calc (G.neighborFinset r ∩ Iso).card ≤ (G.neighborFinset r).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = 4 := by
                  rw [G.card_neighborFinset_eq_degree, hdeg4 r (hRsubHub (hA3subR hr))]
        _ = 4 * A3.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hA3cases : (A3.card = 1 ∧ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card = 4)
        ∨ (A3.card = 2 ∧ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card = 6)
        ∨ (A3.card = 1 ∧ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card = 3 ∧ R.card = 5) := by
      rcases hr45 with h4 | h5 <;> omega
    rcases hA3cases with ⟨h1c, hsum4A⟩ | ⟨h2c, hsum6A⟩ | ⟨h1c, hsum3A, hr5⟩
    · -- `{4,2,2,2}`: the lone `A3` hub has iso-degree `4`, non-adjacent to every hub and `zz`.
      obtain ⟨astar, hA3eq⟩ := Finset.card_eq_one.mp h1c
      have hastarA3 : astar ∈ A3 := by rw [hA3eq]; exact Finset.mem_singleton_self _
      have hastarHub : astar ∈ Hub := hRsubHub (hA3subR hastarA3)
      have hastar4 : (G.neighborFinset astar ∩ Iso).card = 4 := by
        have hs : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card
            = (G.neighborFinset astar ∩ Iso).card := by rw [hA3eq, Finset.sum_singleton]
        omega
      have hNastar : G.neighborFinset astar ⊆ Iso := by
        have hd4 : (G.neighborFinset astar).card = 4 := by
          rw [G.card_neighborFinset_eq_degree, hdeg4 astar hastarHub]
        have heq : G.neighborFinset astar ∩ Iso = G.neighborFinset astar :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hd4, hastar4])
        rw [← heq]; exact Finset.inter_subset_right
      have hnzz : ¬G.Adj astar zz := fun h =>
        hzznotIso (hNastar ((G.mem_neighborFinset astar zz).mpr h))
      have hastarg : astar ≠ g := fun he => hnzz (by rw [he]; exact hzzg.symm)
      have hnadjg : ¬G.Adj astar g :=
        iso_deg_four_nonadj_hub_twenty G Hub Iso hdisj hdeg4 astar g hastarHub hgHub hastar4
      exact Or.inl (rich_partner_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
        hisodeg3 hdsum hleak hshare astar g zz hastarHub hgHub hzzZ (by omega) hgrich hzzg
        hastarg hnadjg hnzz)
    · -- `{3,3,2,2}`: the two `A3` hubs have iso-degree exactly `3`.
      obtain ⟨w1, w2, hw12ne, hA3eq⟩ := Finset.card_eq_two.mp h2c
      have hw1A3 : w1 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_self _ _
      have hw2A3 : w2 ∈ A3 := by
        rw [hA3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hw1Hub : w1 ∈ Hub := hRsubHub (hA3subR hw1A3)
      have hw2Hub : w2 ∈ Hub := hRsubHub (hA3subR hw2A3)
      have hw1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card := by
        have h := hw1A3; rw [hA3def, Finset.mem_filter] at h; exact h.2
      have hw2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card := by
        have h := hw2A3; rw [hA3def, Finset.mem_filter] at h; exact h.2
      have hTpair : (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card
          = ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card := by
        rw [hA3eq, Finset.sum_pair hw12ne]
      have hw1eq3 : (G.neighborFinset w1 ∩ Iso).card = 3 := by omega
      have hw2eq3 : (G.neighborFinset w2 ∩ Iso).card = 3 := by omega
      by_cases hw12adj : G.Adj w1 w2
      · -- Adjacent pair: `N(w1) = 3` twins `∪ {w2}`, so `w1 ≁ zz, g` — assemble on `(w1, g)`.
        have hw1sd_eq : (G.neighborFinset w1) \ Iso = {w2} := by
          have hw1d4 : (G.neighborFinset w1).card = 4 := by
            rw [G.card_neighborFinset_eq_degree, hdeg4 w1 hw1Hub]
          have hw1sd1 : ((G.neighborFinset w1) \ Iso).card = 1 := by
            have := Finset.card_sdiff_add_card_inter (G.neighborFinset w1) Iso
            omega
          obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hw1sd1
          have hw2m : w2 ∈ (G.neighborFinset w1) \ Iso := Finset.mem_sdiff.mpr
            ⟨(G.mem_neighborFinset w1 w2).mpr hw12adj, Finset.disjoint_left.mp hdisj hw2Hub⟩
          rw [hu] at hw2m ⊢
          rw [Finset.mem_singleton] at hw2m
          rw [hw2m]
        have hw1only : ∀ x : Fin 20, G.Adj w1 x → x ∉ Iso → x = w2 := by
          intro x hx hxI
          have hmem : x ∈ (G.neighborFinset w1) \ Iso :=
            Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset w1 x).mpr hx, hxI⟩
          rw [hw1sd_eq, Finset.mem_singleton] at hmem; exact hmem
        have hw2sd_eq : (G.neighborFinset w2) \ Iso = {w1} := by
          have hw2d4 : (G.neighborFinset w2).card = 4 := by
            rw [G.card_neighborFinset_eq_degree, hdeg4 w2 hw2Hub]
          have hw2sd1 : ((G.neighborFinset w2) \ Iso).card = 1 := by
            have := Finset.card_sdiff_add_card_inter (G.neighborFinset w2) Iso
            omega
          obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hw2sd1
          have hw1m : w1 ∈ (G.neighborFinset w2) \ Iso := Finset.mem_sdiff.mpr
            ⟨(G.mem_neighborFinset w2 w1).mpr hw12adj.symm, Finset.disjoint_left.mp hdisj hw1Hub⟩
          rw [hu] at hw1m ⊢
          rw [Finset.mem_singleton] at hw1m
          rw [hw1m]
        have hw2only : ∀ x : Fin 20, G.Adj w2 x → x ∉ Iso → x = w1 := by
          intro x hx hxI
          have hmem : x ∈ (G.neighborFinset w2) \ Iso :=
            Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset w2 x).mpr hx, hxI⟩
          rw [hw2sd_eq, Finset.mem_singleton] at hmem; exact hmem
        have hw1nzz : ¬G.Adj w1 zz := fun h =>
          hzznotHub (by rw [hw1only zz h hzznotIso]; exact hw2Hub)
        have hgne2 : g ≠ w2 := by
          rintro rfl
          exact hzznotHub (by rw [hw2only zz hzzg.symm hzznotIso]; exact hw1Hub)
        have hw1neg : w1 ≠ g := by
          rintro rfl
          exact hzznotHub (by rw [hw1only zz hzzg.symm hzznotIso]; exact hw2Hub)
        have hw1ng : ¬G.Adj w1 g := fun h => hgne2 (hw1only g h hgnotIso)
        exact Or.inl (rich_partner_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
          hisodeg3 hdsum hleak hshare w1 g zz hw1Hub hgHub hzzZ hw1ge hgrich hzzg
          hw1neg hw1ng hw1nzz)
      · -- Non-adjacent pair: two iso-degree-`3` hubs contradict `hno2hub` directly.
        exact (two_nonadj_hubs_contra_twenty G Hub Iso hdeg4 hshare hno2hub w1 w2 hw1Hub hw2Hub
          hw12ne hw12adj hw1ge hw2ge).elim
    · -- `{3,2,2,2,2}` (`r = 5`): the lone `A3` hub `w` has iso-degree `3`.
      obtain ⟨w, hA3eq⟩ := Finset.card_eq_one.mp h1c
      have hwA3 : w ∈ A3 := by rw [hA3eq]; exact Finset.mem_singleton_self _
      have hwHub : w ∈ Hub := hRsubHub (hA3subR hwA3)
      have hw3 : (G.neighborFinset w ∩ Iso).card = 3 := by
        have hs : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card
            = (G.neighborFinset w ∩ Iso).card := by rw [hA3eq, Finset.sum_singleton]
        omega
      have hwd4 : (G.neighborFinset w).card = 4 := by
        rw [G.card_neighborFinset_eq_degree, hdeg4 w hwHub]
      have hwsd1 : ((G.neighborFinset w) \ Iso).card = 1 := by
        have := Finset.card_sdiff_add_card_inter (G.neighborFinset w) Iso
        omega
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hwsd1
      have hwonly : ∀ x : Fin 20, G.Adj w x → x ∉ Iso → x = u := by
        intro x hx hxI
        have hmem : x ∈ (G.neighborFinset w) \ Iso :=
          Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset w x).mpr hx, hxI⟩
        rw [hu, Finset.mem_singleton] at hmem; exact hmem
      -- If `w`'s single non-iso slot is pinned into `{g, zz}`, route through the other `M`-end.
      have hroute : (∀ x : Fin 20, G.Adj w x → x ∉ Iso → x = g ∨ x = zz) → ZPoorCutConfig G := by
        intro hpin
        have hwnzo : ¬G.Adj w zo := by
          intro had
          rcases hpin zo had hzonotIso with he | he
          · exact hzonotHub (he.symm ▸ hgHub)
          · exact hzzo he.symm
        obtain ⟨_, hzohub2, _⟩ :=
          z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
            zo hzoZ
        obtain ⟨y1, y2, -, hNzo⟩ := Finset.card_eq_two.mp hzohub2
        have hy1mem : y1 ∈ G.neighborFinset zo ∩ Hub := by
          rw [hNzo]; exact Finset.mem_insert_self _ _
        have hy2mem : y2 ∈ G.neighborFinset zo ∩ Hub := by
          rw [hNzo]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hy1Hub : y1 ∈ Hub := (Finset.mem_inter.mp hy1mem).2
        have hy2Hub : y2 ∈ Hub := (Finset.mem_inter.mp hy2mem).2
        have hzoy1 : G.Adj zo y1 :=
          (G.mem_neighborFinset zo y1).mp (Finset.mem_inter.mp hy1mem).1
        have hzoy2 : G.Adj zo y2 :=
          (G.mem_neighborFinset zo y2).mp (Finset.mem_inter.mp hy2mem).1
        have hkey : ∀ y : Fin 20, y ∈ G.neighborFinset zo ∩ Hub → w ≠ y ∧ ¬G.Adj w y := by
          intro y hy
          have hyHub : y ∈ Hub := (Finset.mem_inter.mp hy).2
          have hzoy : G.Adj zo y := (G.mem_neighborFinset zo y).mp (Finset.mem_inter.mp hy).1
          refine ⟨?_, ?_⟩
          · rintro rfl; exact hwnzo hzoy.symm
          · intro had
            rcases hpin y had (fun hyI => Finset.disjoint_left.mp hdisj hyHub hyI) with he | he
            · exact hnb g hgHub ⟨hzzg.symm, (he ▸ hzoy).symm⟩
            · exact hzznotHub (he ▸ hyHub)
        by_cases hy1rich : 2 ≤ (G.neighborFinset y1 ∩ Iso).card
        · obtain ⟨hne, hnadj⟩ := hkey y1 hy1mem
          exact Or.inl (rich_partner_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
            hisodeg3 hdsum hleak hshare w y1 zo hwHub hy1Hub hzoZ (by omega) hy1rich hzoy1
            hne hnadj hwnzo)
        by_cases hy2rich : 2 ≤ (G.neighborFinset y2 ∩ Iso).card
        · obtain ⟨hne, hnadj⟩ := hkey y2 hy2mem
          exact Or.inl (rich_partner_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
            hisodeg3 hdsum hleak hshare w y2 zo hwHub hy2Hub hzoZ (by omega) hy2rich hzoy2
            hne hnadj hwnzo)
        -- Both `zo`-hubs poor: each carries one twin — the `|R| = 5` pigeonhole cut fires.
        have hzopoorall : ∀ h ∈ G.neighborFinset zo ∩ Hub, h ∉ R := by
          intro h hh hhR
          have h2 := ((hRmem h).mp hhR).2
          rw [hNzo, Finset.mem_insert, Finset.mem_singleton] at hh
          rcases hh with rfl | rfl
          · exact hy1rich h2
          · exact hy2rich h2
        have hy1P : y1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hy1Hub, hy1rich⟩
        obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp (hpoor1 y1 hy1P)
        exact Or.inl (two_poor_zleaf_pigeonhole_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso
          hdsum hdeg3 hisodeg3 hleak R hRdef y1 zo cstar hy1Hub hzoZ hzoy1 hcs hzopoorall
          (by omega))
      by_cases hwg : w = g
      · refine hroute ?_
        intro x hx hxI
        right
        have hwzz : G.Adj w zz := by rw [hwg]; exact hzzg.symm
        have h1 := hwonly x hx hxI
        have h2 := hwonly zz hwzz hzznotIso
        rw [h1, h2]
      · by_cases hwadjg : G.Adj w g
        · refine hroute ?_
          intro x hx hxI
          left
          have h1 := hwonly x hx hxI
          have h2 := hwonly g hwadjg hgnotIso
          rw [h1, h2]
        · by_cases hwadjzz : G.Adj w zz
          · refine hroute ?_
            intro x hx hxI
            right
            have h1 := hwonly x hx hxI
            have h2 := hwonly zz hwadjzz hzznotIso
            rw [h1, h2]
          · exact Or.inl (rich_partner_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
              hisodeg3 hdsum hleak hshare w g zz hwHub hgHub hzzZ (by omega) hgrich hzzg
              hwg hwadjg hwadjzz)
  -- Extract the two hub-neighbour pairs of the two `M`-ends.
  obtain ⟨_, hz1hub2, _⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z1 hz1Z
  obtain ⟨_, hz2hub2, _⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z2 hz2Z
  obtain ⟨g1, g2, hg12, hNz1⟩ := Finset.card_eq_two.mp hz1hub2
  obtain ⟨g3, g4, hg34, hNz2⟩ := Finset.card_eq_two.mp hz2hub2
  have hg1mem : g1 ∈ G.neighborFinset z1 ∩ Hub := by
    rw [hNz1]; exact Finset.mem_insert_self _ _
  have hg2mem : g2 ∈ G.neighborFinset z1 ∩ Hub := by
    rw [hNz1]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hg3mem : g3 ∈ G.neighborFinset z2 ∩ Hub := by
    rw [hNz2]; exact Finset.mem_insert_self _ _
  have hg4mem : g4 ∈ G.neighborFinset z2 ∩ Hub := by
    rw [hNz2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hg1Hub : g1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : g2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg3Hub : g3 ∈ Hub := (Finset.mem_inter.mp hg3mem).2
  have hg4Hub : g4 ∈ Hub := (Finset.mem_inter.mp hg4mem).2
  have hz1g1 : G.Adj z1 g1 := (G.mem_neighborFinset z1 g1).mp (Finset.mem_inter.mp hg1mem).1
  have hz1g2 : G.Adj z1 g2 := (G.mem_neighborFinset z1 g2).mp (Finset.mem_inter.mp hg2mem).1
  have hz2g3 : G.Adj z2 g3 := (G.mem_neighborFinset z2 g3).mp (Finset.mem_inter.mp hg3mem).1
  have hz2g4 : G.Adj z2 g4 := (G.mem_neighborFinset z2 g4).mp (Finset.mem_inter.mp hg4mem).1
  -- Any rich `Z`-hub closes via the engine.
  by_cases hg1rich : 2 ≤ (G.neighborFinset g1 ∩ Iso).card
  · exact mainB g1 z1 z2 hg1Hub hz1Z hz2Z hz12 hnoboth hz1g1 hg1rich
  by_cases hg2rich : 2 ≤ (G.neighborFinset g2 ∩ Iso).card
  · exact mainB g2 z1 z2 hg2Hub hz1Z hz2Z hz12 hnoboth hz1g2 hg2rich
  by_cases hg3rich : 2 ≤ (G.neighborFinset g3 ∩ Iso).card
  · exact mainB g3 z2 z1 hg3Hub hz2Z hz1Z (Ne.symm hz12)
      (fun h hh hpq => hnoboth h hh ⟨hpq.2, hpq.1⟩) hz2g3 hg3rich
  by_cases hg4rich : 2 ≤ (G.neighborFinset g4 ∩ Iso).card
  · exact mainB g4 z2 z1 hg4Hub hz2Z hz1Z (Ne.symm hz12)
      (fun h hh hpq => hnoboth h hh ⟨hpq.2, hpq.1⟩) hz2g4 hg4rich
  -- All four `Z`-hubs are poor, each with exactly one twin `cᵢ`.
  have hg13 : g1 ≠ g3 := by
    rintro rfl
    exact hnoboth _ hg1Hub ⟨hz1g1.symm, hz2g3.symm⟩
  have hg14 : g1 ≠ g4 := by
    rintro rfl
    exact hnoboth _ hg1Hub ⟨hz1g1.symm, hz2g4.symm⟩
  have hg23 : g2 ≠ g3 := by
    rintro rfl
    exact hnoboth _ hg2Hub ⟨hz1g2.symm, hz2g3.symm⟩
  have hg24 : g2 ≠ g4 := by
    rintro rfl
    exact hnoboth _ hg2Hub ⟨hz1g2.symm, hz2g4.symm⟩
  have hg1P : g1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg1Hub, hg1rich⟩
  have hg2P : g2 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg2Hub, hg2rich⟩
  have hg3P : g3 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg3Hub, hg3rich⟩
  have hg4P : g4 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg4Hub, hg4rich⟩
  obtain ⟨c1, hc1⟩ := Finset.card_eq_one.mp (hpoor1 g1 hg1P)
  obtain ⟨c2, hc2⟩ := Finset.card_eq_one.mp (hpoor1 g2 hg2P)
  obtain ⟨c3, hc3⟩ := Finset.card_eq_one.mp (hpoor1 g3 hg3P)
  obtain ⟨c4, hc4⟩ := Finset.card_eq_one.mp (hpoor1 g4 hg4P)
  have hg1notR : g1 ∉ R := fun hR => hg1rich ((hRmem g1).mp hR).2
  have hg2notR : g2 ∉ R := fun hR => hg2rich ((hRmem g2).mp hR).2
  have hg3notR : g3 ∉ R := fun hR => hg3rich ((hRmem g3).mp hR).2
  have hg4notR : g4 ∉ R := fun hR => hg4rich ((hRmem g4).mp hR).2
  -- Rich hubs meet neither `M`-end (both hub slots of each `M`-end are poor).
  have hnR1 : ∀ h ∈ R, ¬G.Adj h z1 := by
    intro h hh had
    have hmem : h ∈ G.neighborFinset z1 ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z1 h).mpr had.symm, hRsubHub hh⟩
    rw [hNz1, Finset.mem_insert, Finset.mem_singleton] at hmem
    have h2 := ((hRmem h).mp hh).2
    rcases hmem with rfl | rfl
    · exact hg1rich h2
    · exact hg2rich h2
  have hnR2 : ∀ h ∈ R, ¬G.Adj h z2 := by
    intro h hh had
    have hmem : h ∈ G.neighborFinset z2 ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z2 h).mpr had.symm, hRsubHub hh⟩
    rw [hNz2, Finset.mem_insert, Finset.mem_singleton] at hmem
    have h2 := ((hRmem h).mp hh).2
    rcases hmem with rfl | rfl
    · exact hg3rich h2
    · exact hg4rich h2
  -- Per-column: the single twin of a poor `Z`-hub meets at most two rich hubs.
  have hcolb : ∀ gi ci : Fin 20, gi ∈ Hub → gi ∉ R → G.neighborFinset gi ∩ Iso = {ci} →
      (G.neighborFinset ci ∩ R).card ≤ 2 := by
    intro gi ci hgiHub hginotR hgiiso
    have hcimem : ci ∈ G.neighborFinset gi ∩ Iso := by
      rw [hgiiso]; exact Finset.mem_singleton_self _
    have hciIso : ci ∈ Iso := (Finset.mem_inter.mp hcimem).2
    have hgici : G.Adj gi ci := (G.mem_neighborFinset gi ci).mp (Finset.mem_inter.mp hcimem).1
    have hci3 : (G.neighborFinset ci ∩ Hub).card = 3 := hiso3 ci hciIso
    have hgiin : gi ∈ G.neighborFinset ci ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset ci gi).mpr hgici.symm, hgiHub⟩
    have hsub : G.neighborFinset ci ∩ R ⊆ (G.neighborFinset ci ∩ Hub).erase gi := by
      intro x hx
      rw [Finset.mem_inter] at hx
      refine Finset.mem_erase.mpr ⟨fun he => hginotR (he ▸ hx.2), ?_⟩
      exact Finset.mem_inter.mpr ⟨hx.1, hRsubHub hx.2⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hgiin, hci3] at hle
    omega
  -- Column lower bound: if every rich hub is covered by column `(gi, ci)` then
  -- `|R| ≤ |N(gi) ∩ R| + 2`.
  have hcol : ∀ gi ci : Fin 20, (∀ h ∈ R, ¬G.Adj gi h → G.Adj ci h) →
      (G.neighborFinset ci ∩ R).card ≤ 2 → R.card ≤ (G.neighborFinset gi ∩ R).card + 2 := by
    intro gi ci hall hcile
    have hsub : R ⊆ (G.neighborFinset gi ∩ R) ∪ (G.neighborFinset ci ∩ R) := by
      intro h hh
      by_cases hadj : G.Adj gi h
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gi h).mpr hadj, hh⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset ci h).mpr (hall h hh hadj), hh⟩)
    have h1 : R.card ≤ (G.neighborFinset gi ∩ R).card + (G.neighborFinset ci ∩ R).card := by
      calc R.card ≤ ((G.neighborFinset gi ∩ R) ∪ (G.neighborFinset ci ∩ R)).card :=
            Finset.card_le_card hsub
        _ ≤ (G.neighborFinset gi ∩ R).card + (G.neighborFinset ci ∩ R).card :=
            Finset.card_union_le _ _
    omega
  -- A surviving `(h, column)` pair assembles the cut.
  by_cases hex1 : ∃ h ∈ R, ¬G.Adj g1 h ∧ ¬G.Adj c1 h
  · obtain ⟨h, hhR, hng, hnc⟩ := hex1
    exact Or.inl (poor_one_column_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
      hisodeg3 hdsum hleak h g1 c1 z1 (hRsubHub hhR) hg1Hub hz1Z hz1g1 hc1
      ((hRmem h).mp hhR).2 hng hnc (hnR1 h hhR))
  by_cases hex2 : ∃ h ∈ R, ¬G.Adj g2 h ∧ ¬G.Adj c2 h
  · obtain ⟨h, hhR, hng, hnc⟩ := hex2
    exact Or.inl (poor_one_column_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
      hisodeg3 hdsum hleak h g2 c2 z1 (hRsubHub hhR) hg2Hub hz1Z hz1g2 hc2
      ((hRmem h).mp hhR).2 hng hnc (hnR1 h hhR))
  by_cases hex3 : ∃ h ∈ R, ¬G.Adj g3 h ∧ ¬G.Adj c3 h
  · obtain ⟨h, hhR, hng, hnc⟩ := hex3
    exact Or.inl (poor_one_column_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
      hisodeg3 hdsum hleak h g3 c3 z2 (hRsubHub hhR) hg3Hub hz2Z hz2g3 hc3
      ((hRmem h).mp hhR).2 hng hnc (hnR2 h hhR))
  by_cases hex4 : ∃ h ∈ R, ¬G.Adj g4 h ∧ ¬G.Adj c4 h
  · obtain ⟨h, hhR, hng, hnc⟩ := hex4
    exact Or.inl (poor_one_column_zleaf_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
      hisodeg3 hdsum hleak h g4 c4 z2 (hRsubHub hhR) hg4Hub hz2Z hz2g4 hc4
      ((hRmem h).mp hhR).2 hng hnc (hnR2 h hhR))
  -- No survivor: the aggregate double count `4(r − 2) ≤ ∑_R |N ∩ ZH| ≤ 3r − 6` is impossible.
  exfalso
  have hall1 : ∀ h ∈ R, ¬G.Adj g1 h → G.Adj c1 h := by
    intro h hh hng
    by_contra hnc
    exact hex1 ⟨h, hh, hng, hnc⟩
  have hall2 : ∀ h ∈ R, ¬G.Adj g2 h → G.Adj c2 h := by
    intro h hh hng
    by_contra hnc
    exact hex2 ⟨h, hh, hng, hnc⟩
  have hall3 : ∀ h ∈ R, ¬G.Adj g3 h → G.Adj c3 h := by
    intro h hh hng
    by_contra hnc
    exact hex3 ⟨h, hh, hng, hnc⟩
  have hall4 : ∀ h ∈ R, ¬G.Adj g4 h → G.Adj c4 h := by
    intro h hh hng
    by_contra hnc
    exact hex4 ⟨h, hh, hng, hnc⟩
  have hlow1 : R.card ≤ (G.neighborFinset g1 ∩ R).card + 2 :=
    hcol g1 c1 hall1 (hcolb g1 c1 hg1Hub hg1notR hc1)
  have hlow2 : R.card ≤ (G.neighborFinset g2 ∩ R).card + 2 :=
    hcol g2 c2 hall2 (hcolb g2 c2 hg2Hub hg2notR hc2)
  have hlow3 : R.card ≤ (G.neighborFinset g3 ∩ R).card + 2 :=
    hcol g3 c3 hall3 (hcolb g3 c3 hg3Hub hg3notR hc3)
  have hlow4 : R.card ≤ (G.neighborFinset g4 ∩ R).card + 2 :=
    hcol g4 c4 hall4 (hcolb g4 c4 hg4Hub hg4notR hc4)
  have hZHsum : ∑ y ∈ ({g1, g2, g3, g4} : Finset (Fin 20)), (G.neighborFinset y ∩ R).card
      = (G.neighborFinset g1 ∩ R).card + (G.neighborFinset g2 ∩ R).card
        + (G.neighborFinset g3 ∩ R).card + (G.neighborFinset g4 ∩ R).card := by
    rw [Finset.sum_insert (by simp [hg12, hg13, hg14]),
      Finset.sum_insert (by simp [hg23, hg24]),
      Finset.sum_insert (by simp [hg34]), Finset.sum_singleton]
    omega
  have hcross : ∑ y ∈ ({g1, g2, g3, g4} : Finset (Fin 20)), (G.neighborFinset y ∩ R).card
      = ∑ h ∈ R, (G.neighborFinset h ∩ ({g1, g2, g3, g4} : Finset (Fin 20))).card :=
    cross_count_twenty G ({g1, g2, g3, g4} : Finset (Fin 20)) R
  have hperh : ∀ h ∈ R, (G.neighborFinset h ∩ ({g1, g2, g3, g4} : Finset (Fin 20))).card
      + (G.neighborFinset h ∩ Iso).card ≤ 4 := by
    intro h hh
    have hsp := nbr_split_three_twenty G Hub Iso hdisj h
    rw [hdeg4 h (hRsubHub hh)] at hsp
    have hsub : G.neighborFinset h ∩ ({g1, g2, g3, g4} : Finset (Fin 20))
        ⊆ G.neighborFinset h ∩ Hub := by
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have hx2 := hx.2
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with rfl | rfl | rfl | rfl
      · exact hg1Hub
      · exact hg2Hub
      · exact hg3Hub
      · exact hg4Hub
    have hle := Finset.card_le_card hsub
    omega
  have hsumle : (∑ h ∈ R, (G.neighborFinset h ∩ ({g1, g2, g3, g4} : Finset (Fin 20))).card)
      + ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card ≤ 4 * R.card := by
    have hstep : ∑ h ∈ R, ((G.neighborFinset h ∩ ({g1, g2, g3, g4} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card) ≤ 4 * R.card := by
      calc ∑ h ∈ R, ((G.neighborFinset h ∩ ({g1, g2, g3, g4} : Finset (Fin 20))).card
            + (G.neighborFinset h ∩ Iso).card)
          ≤ ∑ _h ∈ R, 4 := Finset.sum_le_sum hperh
        _ = 4 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.sum_add_distrib] at hstep
    exact hstep
  rcases hr45 with h4 | h5 <;> omega

end N20

end ACMax
