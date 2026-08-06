import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct
import ACMaxConjecture.SmallCases.N20.OctahedronPoorForce
import ACMaxConjecture.SmallCases.N20.OctaMass

/-!
# Octahedron two-hub corner selector for `n = 20` (`|Hub| = 12`, all degree `4`, `(12, 6, 48)`)

This file supplies **PART A**, `two_hub_corner_select_twenty`, the maximal-hub `e(M) = 1` corner of
the `n = 20` two-hub `s ≤ 2` alignment dichotomy.  The profile is the NEW frontier
`(|Hub|, |Iso|, ∑deg) = (12, 6, 48)` — twelve all-degree-`4` hubs, six `M`-isolated twins, two
`M`-edge endpoints `Z` (`|D| = 8`, `s = 2`, partition `|Hub| + |Iso| + |Z| = 12 + 6 + 2 = 20`).
As at `n = 19`, the bare counting inequality `3·|Iso| + 10·|Hub| ≤ 3·∑deg + 2` evaluates to
`138 ≤ 146` (resp. `144 ≤ 146` at `e(M) = 0`), so the profile is **not** refuted by counting and
must be routed through the octahedron rigidity chain.

## Structure

The conclusion `TwoHubConfig G ∨ StarTriangleConfig G` is, by definition, exactly `ZPoorCutConfig G`
(see `TwinCert20Cert`).  We split on whether a good two-hub opposite-twin pair exists:

* **`hpair`** (a good pair exists): build the `TwoHubConfig` directly from the two private-twin
  pairs (the twins are `M`-isolated, hence degree `3` and mutually non-adjacent by `hisoIndep`).
* **`hno2hub`** (no good pair): the octahedron rigidity chain.  Set
  `R = Hub.filter (2 ≤ isoDeg)` (the rich hubs); the structural foundation forces `|R| = 6`, the
  rich-internal mass `mRR ∈ {4, 6}`, four high twins, and no poor-zero hub.  Then
  `octahedron_poor_layer_force_twenty` yields one of a good triangle (Σ = 11), a good `K₂,₃`
  (Σ = 19), a good `C₄` (Σ = 14), or `ZPoorCutConfig G`.  The three good certificates contradict
  `hT`, `hK23`, `hC4` respectively; the last is the goal.

## The input bundle (`octahedron_inputs_twenty`)

The input bundle to `octahedron_poor_layer_force_twenty` — `hnozero` (no poor-zero hub),
`hRcard : |R| = 6`, `hmass : mRR ∈ {4, 6}`, `hhigh4` (four high twins) — is assembled from the
`|Hub| = 12` structural residual (`octahedron_struct_residual_twenty`: `hnozero`, `|R| = 6`,
`mRR ≠ 10`, via `rich_six_no_iso_zero_twenty` and `octahedron_mass_ne_eight_twenty`) and the
mass-exclusion dichotomy (`octahedron_mass_reduce_twenty`: `mRR ∈ {6, 10}`, with `n₃ = 4` at
`mRR = 6`).  Everything else — the `hpair` `TwoHubConfig` assembly, the clean input derivations
(`htle3`), and the three good-certificate refutations — is proved directly below.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The structural input bundle for the octahedron three-way force (fully proved).**  In the
no-two-hub `(12, 6, 48)` octahedron regime, the rich hubs `R = Hub.filter (2 ≤ isoDeg)` satisfy:
no hub is poor-zero (`hnozero`), `|R| = 6`, the rich-internal ordered mass is `4` or `6`, and at
least four `M`-isolated twins meet all three of their hubs inside `R` (`hhigh4`) — or
`ZPoorCutConfig G` holds outright.

These are exactly the hypotheses of `octahedron_poor_layer_force_twenty` beyond the bare regime.
They are assembled from the `|Hub| = 12` structural residual
(`octahedron_struct_residual_twenty`: `hnozero`, `|R| = 6`, `mRR ≠ 10`) and the mass-exclusion
dichotomy (`octahedron_mass_reduce_twenty`: `mRR ∈ {6, 10}` with four high twins at `6`). -/
theorem octahedron_inputs_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    ((∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) ∧
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 ∧
    ((∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) = 4 ∨
      (∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) = 6) ∧
    4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩
      Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 3)).card)
    ∨ ZPoorCutConfig G := by
  classical
  by_cases hcut : ZPoorCutConfig G
  · exact Or.inr hcut
  refine Or.inl ?_
  -- `R = {h ∈ Hub : 2 ≤ |N h ∩ Iso|}`, the rich hubs.
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hReq
  -- `htle3`: a twin meets `R ⊆ Hub` in at most its three hubs.
  have htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card
        ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _)
            (by rw [hReq]; exact Finset.filter_subset _ _))
      _ = 3 := hiso3 t ht
  -- The `|Hub| = 12` structural residual: `hnozero`, `|R| = 6`, and `mRR ≠ 10`.
  obtain ⟨hnozero, hRcard, hmne10⟩ := octahedron_struct_residual_twenty G Hub Iso hdeg4 hiso3
    hdisj hHub hIso hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hcut
  rw [← hReq] at hRcard hmne10
  -- The mass-exclusion handshake pins `mRR ∈ {4, 6}` with four high twins, or `mRR = 10`.
  rcases octahedron_mass_reduce_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
      hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard htle3 hcut with hgood | hbad
  · exact ⟨hnozero, hRcard, hgood.1, hgood.2⟩
  · exact absurd hbad hmne10

/-- **PART A: the octahedron two-hub corner selector (`|Hub| = 12`, `(12, 6, 48)`).**  Either a good
two-hub opposite-twin configuration exists (`TwoHubConfig`), or the maximal-hub corner realises the
star-triangle cut (`StarTriangleConfig`).  The conclusion is definitionally `ZPoorCutConfig G`.

The `hpair` branch builds the `TwoHubConfig` from two private-twin pairs; the `hno2hub` branch runs
the octahedron three-way force (`octahedron_poor_layer_force_twenty`) and refutes the three good
certificates against `hT`/`hK23`/`hC4`. -/
theorem two_hub_corner_select_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    TwoHubConfig G ∨ StarTriangleConfig G := by
  classical
  -- `Hub`/`Iso` membership and degree-4 facts.
  have hHubnotIso : ∀ x : Fin 20, x ∈ Hub → x ∉ Iso := fun x hx hxI =>
    Finset.disjoint_left.mp hdisj hx hxI
  have hIsonotHub : ∀ x : Fin 20, x ∈ Iso → x ∉ Hub := fun x hx hxH =>
    Finset.disjoint_left.mp hdisj hxH hx
  by_cases hpair : ∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card
  · -- **A good two-hub pair exists.**  Build the `TwoHubConfig`.
    refine Or.inl ?_
    obtain ⟨h₁, h₂, hh1, hh2, hdeg1, hdeg2, hne12, hnadj12, hAcard, hBcard⟩ := hpair
    set A : Finset (Fin 20) := (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ with hAdef
    set B : Finset (Fin 20) := (G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁ with hBdef
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hAcard
    obtain ⟨c, hc, d, hd2, hcd⟩ := Finset.one_lt_card.mp hBcard
    have hAprop : ∀ x : Fin 20, x ∈ A → G.Adj x h₁ ∧ x ∈ Iso ∧ ¬G.Adj x h₂ := by
      intro x hx
      rw [hAdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
      refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
      intro hadj; exact hx.2 ((G.mem_neighborFinset h₂ x).mpr hadj.symm)
    have hBprop : ∀ x : Fin 20, x ∈ B → G.Adj x h₂ ∧ x ∈ Iso ∧ ¬G.Adj x h₁ := by
      intro x hx
      rw [hBdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
      refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
      intro hadj; exact hx.2 ((G.mem_neighborFinset h₁ x).mpr hadj.symm)
    obtain ⟨ha_h₁, ha_iso, ha_nh₂⟩ := hAprop a ha
    obtain ⟨hb_h₁, hb_iso, hb_nh₂⟩ := hAprop b hb
    obtain ⟨hc_h₂, hc_iso, hc_nh₁⟩ := hBprop c hc
    obtain ⟨hd_h₂, hd_iso, hd_nh₁⟩ := hBprop d hd2
    refine ⟨h₁, h₂, a, b, c, d, hdeg1, hdeg2,
      hisodeg3 a ha_iso, hisodeg3 b hb_iso, hisodeg3 c hc_iso, hisodeg3 d hd_iso,
      ha_h₁, hb_h₁, hc_h₂, hd_h₂,
      hnadj12,
      (fun h => hc_nh₁ h.symm), (fun h => hd_nh₁ h.symm),
      ha_nh₂, hisoIndep a ha_iso c hc_iso, hisoIndep a ha_iso d hd_iso,
      hb_nh₂, hisoIndep b hb_iso c hc_iso, hisoIndep b hb_iso d hd_iso,
      hne12,
      (fun e => hIsonotHub a ha_iso (e ▸ hh1)),
      (fun e => hIsonotHub b hb_iso (e ▸ hh1)),
      (fun e => hIsonotHub c hc_iso (e ▸ hh1)),
      (fun e => hIsonotHub d hd_iso (e ▸ hh1)),
      (fun e => hIsonotHub a ha_iso (e ▸ hh2)),
      (fun e => hIsonotHub b hb_iso (e ▸ hh2)),
      (fun e => hIsonotHub c hc_iso (e ▸ hh2)),
      (fun e => hIsonotHub d hd_iso (e ▸ hh2)),
      hab,
      (fun e => hc_nh₁ (e ▸ ha_h₁)), (fun e => hd_nh₁ (e ▸ ha_h₁)),
      (fun e => hc_nh₁ (e ▸ hb_h₁)), (fun e => hd_nh₁ (e ▸ hb_h₁)),
      hcd⟩
  · -- **No good two-hub pair.**  Run the octahedron three-way force.  The goal `TwoHubConfig ∨
    -- StarTriangleConfig` is definitionally `ZPoorCutConfig G`.
    set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
    -- `htle3`: a twin meets `R ⊆ Hub` in at most its three hubs.
    have htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
      intro t ht
      calc (G.neighborFinset t ∩ R).card
          ≤ (G.neighborFinset t ∩ Hub).card :=
            Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _)
              (by rw [hRdef]; exact Finset.filter_subset _ _))
        _ = 3 := hiso3 t ht
    -- The structural input bundle, or directly `ZPoorCutConfig G` (the goal).
    rcases octahedron_inputs_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3 hdsum hleak
        hshare hpair hC4 hK23 hT with ⟨hnozero, hRcard, hmass, hhigh4⟩ | hcutcfg
    on_goal 2 => exact hcutcfg
    -- The octahedron three-way force.
    have hforce := octahedron_poor_layer_force_twenty G Hub Iso R hRdef hdeg4 hiso3 hdisj hHub hIso
      hisodeg3 hdeg3 hdsum hleak hshare hpair hC4 hK23 hT hnozero hRcard hmass hhigh4 htle3
    -- Refute the three good certificates; the last branch is the goal `ZPoorCutConfig G`.
    rcases hforce with (htri | hk23cfg | hc4cfg) | hcut
    · -- Good triangle `{g₁, g₂, t}`, degrees `4 + 4 + 3 = 11`.
      exfalso
      obtain ⟨g₁, g₂, t, hg1, hg2, ht, hg12, hAg12, hAg1t, hAg2t⟩ := htri
      have hg1t : g₁ ≠ t := fun e => hHubnotIso g₁ hg1 (e ▸ ht)
      have hg2t : g₂ ≠ t := fun e => hHubnotIso g₂ hg2 (e ▸ ht)
      exact hT ⟨g₁, g₂, t, hg12, hg2t, hg1t, hAg12, hAg2t, hAg1t, by
        rw [hdeg4 g₁ hg1, hdeg4 g₂ hg2, hisodeg3 t ht]⟩
    · -- Good `K₂,₃` with parts `{a, b}`, `{c, d, t}`, degrees `4·4 + 3 = 19`.
      exfalso
      obtain ⟨a, b, c, d, t, haH, hbH, hcH, hdH, htI,
        hac, had, hat, hbc, hbd, hbt, hnab, hncd, hnct, hndt,
        hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd⟩ := hk23cfg
      have hat' : a ≠ t := fun e => hHubnotIso a haH (e ▸ htI)
      have hbt' : b ≠ t := fun e => hHubnotIso b hbH (e ▸ htI)
      have hct' : c ≠ t := fun e => hHubnotIso c hcH (e ▸ htI)
      have hdt' : d ≠ t := fun e => hHubnotIso d hdH (e ▸ htI)
      refine hK23 ⟨a, b, c, d, t, ?_, hac, had, hat, hbc, hbd, hbt, hnab, hncd, hnct, hndt, ?_⟩
      · rw [Finset.card_insert_of_notMem (by simp [hne_ab, hne_ac, hne_ad, hat']),
          Finset.card_insert_of_notMem (by simp [hne_bc, hne_bd, hbt']),
          Finset.card_insert_of_notMem (by simp [hne_cd, hct']),
          Finset.card_insert_of_notMem (by simp [hdt']), Finset.card_singleton]
      · rw [hdeg4 a haH, hdeg4 b hbH, hdeg4 c hcH, hdeg4 d hdH, hisodeg3 t htI]
    · -- Good `C₄` `r₁–z₁–z₂–r₂–r₁`, degrees `4 + 3 + 3 + 4 = 14`.
      exfalso
      obtain ⟨r₁, r₂, z₁, z₂, hr1H, hr2H, hz1Z, hz2Z, hdz1, hdz2,
        hAr1z1, hAz1z2, hAz2r2, hAr2r1, hnr1z2, hnz1r2, hne_r12, hne_z12⟩ := hc4cfg
      have hzZmem : ∀ z : Fin 20, z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) → z ∉ Hub := by
        intro z hz
        rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
      have hr1z1 : r₁ ≠ z₁ := fun e => hzZmem z₁ hz1Z (e ▸ hr1H)
      have hr1z2 : r₁ ≠ z₂ := fun e => hzZmem z₂ hz2Z (e ▸ hr1H)
      have hr2z1 : r₂ ≠ z₁ := fun e => hzZmem z₁ hz1Z (e ▸ hr2H)
      have hr2z2 : r₂ ≠ z₂ := fun e => hzZmem z₂ hz2Z (e ▸ hr2H)
      refine hC4 ⟨r₁, z₁, z₂, r₂, ?_, hAr1z1, hAz1z2, hAz2r2, hAr2r1, hnr1z2, hnz1r2, ?_⟩
      · rw [Finset.card_insert_of_notMem (by simp [hr1z1, hr1z2, hne_r12]),
          Finset.card_insert_of_notMem (by simp [hne_z12, hr2z1.symm]),
          Finset.card_insert_of_notMem (by simp [hr2z2.symm]), Finset.card_singleton]
      · rw [hdeg4 r₁ hr1H, hdeg4 r₂ hr2H, hdz1, hdz2]
    · -- `ZPoorCutConfig G` is the goal.
      exact hcut

end N20

end ACMax
