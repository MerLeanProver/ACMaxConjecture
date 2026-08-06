import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.RichZdeg
import ACMaxConjecture.SmallCases.N20.OctahedronStruct
import ACMaxConjecture.SmallCases.N20.OctahedronForce

/-!
# Octahedron poor/`Z` counting foundation (`n = 20`, `|Hub| = 12`, HARD CRUX core)

Port of the `n = 19` `TwinCert19OctahedronPoorForce2` cross-layer counting LEAVES to the NEW
`n = 20` `|Hub| = 12` regime.  Over the rigid octahedron (six rich hubs `R`, **six** poor hubs
`P = Hub \ R` — vs five at `n = 19`, since `|Hub| 11 → 12` —, four high `M`-isolated twins, two low
twins, two adjacent `M`-edge endpoints `Z = univ \ (Hub ∪ Iso)`) we pin the cross-layer handshake.

* `octahedron_poor_counts_twenty` — the cross-layer counts: `E(R, Z) = 2`, `E(P, Z) = 2`,
  the ordered rich–poor + rich–rich mass `E(R, P) + E(R, R) = 10` (vs `9` at `n = 19`), the ordered
  poor–poor mass `E(P, P) = E(R, R) + 6` (vs `+ 4`), and each poor hub has exactly three neighbours
  in `R ∪ P ∪ Z`.  **The genuinely-new `|Hub| = 12` arithmetic:** `∑_R isoDeg = 12` (vs `13`, since
  the six poor hubs carry six iso-incidences out of `E(Hub, Iso) = 18`), and the per-poor-layer
  degree sum is `6·4 = 24` (vs `20`).  Uses the compiled `zdeg_split_sharp_twenty`, keeping the
  `ZPoorCutConfig` escape disjunct.
* `octahedron_low_twin_poor_twenty` — the two low twins carry all **six** poor incidences (each
  poor hub meets exactly one low twin; the low twins split the six poor exactly `3 + 3`, since a
  twin meets at most three hubs).  **Fully axiom-clean** (uses only `octahedron_struct_twenty`, no
  threaded hypothesis).

## The DEEP packing (see `TwinCert20OctahedronMassFour`)

With six poor hubs and `mPP = mRR + 6` (`= 12` at the forced `mRR = 6`), the poor layer is a
six-edge bipartite graph on the `3 + 3` low-twin sides: a heavy side-pair (poor-degree sum `≥ 5`)
shares two common poor neighbours — a good `K₂,₃` — and the residual `2`-regular (`C₆`) layer
realises `TwoHubConfig` through the poor `Z`-slot, absorbed by the `ZPoorCutConfig` disjunct.

**Integrality note (load-bearing for the packing).**  At `n = 20` the trace saturation
`(∑_t |N t ∩ R|·(|N t ∩ R| − 1)) + mRR = |R|² − |R| = 30` together with `∑_t |N t ∩ R| = 12` forces
`mRR = 6` under `hhigh4` (the multiset `{n₃ = 4, n₀ = 2}`); `mRR = 4` yields `n₁ + n₂ + 13 = 12`
over `ℕ` and is impossible outright — even simpler than the `n = 19` parity kill.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Octahedron cross-layer counts (LEAF, axiom-clean).**  Over the rigid octahedron the
handshake on the partition `R ⊔ P ⊔ Iso ⊔ Z` (with `P = Hub \ R`, `Z = univ \ (Hub ∪ Iso)`) pins:
`E(R, Z) = 2`, `E(P, Z) = 2`, the ordered rich–poor and rich–rich masses sum to `10`, the ordered
poor–poor mass is the rich–rich mass plus `6`, and every poor hub has exactly three neighbours in
`R ∪ P ∪ Z` (degree `4` minus its single twin).  The `Z`-side counts delegate to the compiled
`zdeg_split_sharp_twenty`, keeping the `ZPoorCutConfig` escape disjunct. -/
theorem octahedron_poor_counts_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
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
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6) :
    ((∑ r ∈ R, (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))).card) = 2 ∧
    (∑ g ∈ Hub \ R, (G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))).card)
        = 2 ∧
    (∑ r ∈ R, (G.neighborFinset r ∩ (Hub \ R)).card)
        + (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 10 ∧
    (∑ g ∈ Hub \ R, (G.neighborFinset g ∩ (Hub \ R)).card)
        = (∑ r ∈ R, (G.neighborFinset r ∩ R).card) + 6 ∧
    (∀ g ∈ Hub \ R, (G.neighborFinset g ∩ R).card + (G.neighborFinset g ∩ (Hub \ R)).card
      + (G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))).card = 3)) ∨
    ZPoorCutConfig G := by
  classical
  by_cases hcut : ZPoorCutConfig G
  · exact Or.inr hcut
  refine Or.inl ?_
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set P : Finset (Fin 20) := Hub \ R with hPdef
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  have hdisjRP : Disjoint R P := by rw [hPdef]; exact Finset.disjoint_sdiff
  have hunion : R ∪ P = Hub := by rw [hPdef]; exact Finset.union_sdiff_of_subset hRsub
  -- Per-hub four-way degree split over `R ⊔ P ⊔ Iso ⊔ Z`.
  have hsplit : ∀ a ∈ Hub, (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
      + (G.neighborFinset a ∩ Iso).card + (G.neighborFinset a ∩ Z).card = 4 := by
    intro a ha
    have hd : G.degree a = 4 := hdeg4 a ha
    have hRP : (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
        = (G.neighborFinset a ∩ Hub).card := by
      rw [← Finset.card_union_of_disjoint
            (Finset.disjoint_left.mpr (fun x hx hx2 =>
              Finset.disjoint_left.mp hdisjRP (Finset.mem_of_mem_inter_right hx)
                (Finset.mem_of_mem_inter_right hx2))),
        ← Finset.inter_union_distrib_left, hunion]
    have hHIZ : (G.neighborFinset a ∩ Hub).card + (G.neighborFinset a ∩ Iso).card
        + (G.neighborFinset a ∩ Z).card = G.degree a := by
      have h1 : (G.neighborFinset a ∩ Hub).card + (G.neighborFinset a \ Hub).card
          = (G.neighborFinset a).card := Finset.card_inter_add_card_sdiff _ _
      have h2 : ((G.neighborFinset a \ Hub) ∩ Iso).card + ((G.neighborFinset a \ Hub) \ Iso).card
          = (G.neighborFinset a \ Hub).card := Finset.card_inter_add_card_sdiff _ _
      have he1 : (G.neighborFinset a \ Hub) ∩ Iso = G.neighborFinset a ∩ Iso := by
        ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨hx, _⟩, hxi⟩; exact ⟨hx, hxi⟩
        · rintro ⟨hx, hxi⟩
          exact ⟨⟨hx, fun hxh => Finset.disjoint_left.mp hdisj hxh hxi⟩, hxi⟩
      have he2 : (G.neighborFinset a \ Hub) \ Iso = G.neighborFinset a ∩ Z := by
        ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, hZdef, Finset.mem_sdiff,
          Finset.mem_univ, true_and, Finset.mem_union, not_or]
        tauto
      rw [he1, he2] at h2
      rw [G.card_neighborFinset_eq_degree] at h1
      omega
    omega
  -- `E(R, Z) = 2` and `E(P, Z) = 2`.
  obtain ⟨hzR2, hzP2⟩ := (zdeg_split_sharp_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
    hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT).resolve_right hcut
  rw [← hReq, ← hZdef] at hzR2
  have hzP2' : ∑ g ∈ P, (G.neighborFinset g ∩ Z).card = 2 := by
    have hPfilter : P = Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hPdef, hReq, Finset.filter_not]
    rw [hPfilter]; exact hzP2
  -- `∑_R |N ∩ Iso| = 12` (the genuinely-new `|Hub| = 12` value: `6 + |R| = 12`).
  have hisoR12 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 12 := by
    have := (octahedron_trace_saturate_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso
      hisodeg3 hshare hno2hub hT hnozero).2
    rw [hRcard] at this; omega
  -- Each poor hub meets exactly one twin.
  have hpoor1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hg
    rw [hPdef, Finset.mem_sdiff] at hg
    obtain ⟨hgHub, hgnR⟩ := hg
    have hge1 : 1 ≤ (G.neighborFinset g ∩ Iso).card := hnozero g hgHub
    have hle1 : (G.neighborFinset g ∩ Iso).card ≤ 1 := by
      by_contra h
      exact hgnR (by rw [hReq, Finset.mem_filter]; exact ⟨hgHub, by omega⟩)
    omega
  -- Sum the split over `R`: `mRR + E(R,P) + 12 + 2 = 24`.
  have hsumR : ∑ a ∈ R, ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
      + (G.neighborFinset a ∩ Iso).card + (G.neighborFinset a ∩ Z).card) = 24 := by
    rw [Finset.sum_congr rfl (fun a ha => hsplit a (hRsub ha)), Finset.sum_const, hRcard,
      smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsumR
  -- Sum the split over `P`: `E(P,R) + E(P,P) + 6 + 2 = 24`.
  have hPcard : P.card = 6 := by
    rw [hPdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub, hHub, hRcard]
  have hPsub : P ⊆ Hub := by rw [hPdef]; exact Finset.sdiff_subset
  have hsumP : ∑ a ∈ P, ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
      + (G.neighborFinset a ∩ Iso).card + (G.neighborFinset a ∩ Z).card) = 24 := by
    rw [Finset.sum_congr rfl (fun a ha => hsplit a (hPsub ha)), Finset.sum_const, hPcard,
      smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsumP
  have hisoP6 : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 6 := by
    rw [Finset.sum_congr rfl (fun g hg => hpoor1 g hg), Finset.sum_const, hPcard, smul_eq_mul,
      mul_one]
  -- `E(R,P) = E(P,R)` cross count.
  have hcrossRP : ∑ a ∈ R, (G.neighborFinset a ∩ P).card
      = ∑ a ∈ P, (G.neighborFinset a ∩ R).card := cross_count_twenty G R P
  refine ⟨hzR2, hzP2', ?_, ?_, ?_⟩
  · omega
  · omega
  · intro g hg
    have h1 := hsplit g (hPsub hg)
    have h2 := hpoor1 g hg
    omega

/-- **Octahedron low-twin poor incidence (LEAF, axiom-clean).**  There are exactly two low twins
`t₁ ≠ t₂` in `Iso`, each meeting at least one poor hub (`P = Hub \ R`); their poor neighbourhoods
are disjoint and together cover all **six** poor hubs with `|N(t₁) ∩ P| + |N(t₂) ∩ P| = 6` (so the
six poor split exactly `3 + 3`, since a twin meets at most three hubs).  Every poor hub meets
exactly one of `t₁`, `t₂`. -/
theorem octahedron_low_twin_poor_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    ∃ t₁ t₂ : Fin 20, t₁ ∈ Iso ∧ t₂ ∈ Iso ∧ t₁ ≠ t₂ ∧
      1 ≤ (G.neighborFinset t₁ ∩ (Hub \ R)).card ∧
      1 ≤ (G.neighborFinset t₂ ∩ (Hub \ R)).card ∧
      (G.neighborFinset t₁ ∩ (Hub \ R)).card + (G.neighborFinset t₂ ∩ (Hub \ R)).card = 6 ∧
      Disjoint (G.neighborFinset t₁ ∩ (Hub \ R)) (G.neighborFinset t₂ ∩ (Hub \ R)) ∧
      ∀ g ∈ Hub \ R, g ∈ G.neighborFinset t₁ ∨ g ∈ G.neighborFinset t₂ := by
  classical
  set P : Finset (Fin 20) := Hub \ R with hPdef
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- Each poor hub meets exactly one twin.
  have hpoor1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hg
    rw [hPdef, Finset.mem_sdiff] at hg
    obtain ⟨hgHub, hgnR⟩ := hg
    have hge1 : 1 ≤ (G.neighborFinset g ∩ Iso).card := hnozero g hgHub
    have hle1 : (G.neighborFinset g ∩ Iso).card ≤ 1 := by
      by_contra h
      exact hgnR (by rw [hReq, Finset.mem_filter]; exact ⟨hgHub, by omega⟩)
    omega
  -- The low-twin set `L` has cardinality two.
  obtain ⟨_, _, _, hLcard⟩ :=
    octahedron_struct_twenty G Hub Iso R hReq hiso3 hHub hIso hnozero hRcard hhigh4 htle3
  set L : Finset (Fin 20) := Iso.filter (fun t => 1 ≤ (G.neighborFinset t ∩ (Hub \ R)).card)
    with hLdef
  obtain ⟨t₁, t₂, hne, hLeq⟩ := Finset.card_eq_two.mp hLcard
  have ht₁L : t₁ ∈ L := by rw [hLeq]; exact Finset.mem_insert_self _ _
  have ht₂L : t₂ ∈ L := by rw [hLeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [hLdef, Finset.mem_filter] at ht₁L ht₂L
  obtain ⟨ht₁Iso, ht₁P⟩ := ht₁L
  obtain ⟨ht₂Iso, ht₂P⟩ := ht₂L
  -- Every poor meets exactly one of `t₁, t₂`: its unique twin lies in `L = {t₁, t₂}`.
  have hcover : ∀ g ∈ P, g ∈ G.neighborFinset t₁ ∨ g ∈ G.neighborFinset t₂ := by
    intro g hg
    have hg1 := hpoor1 g hg
    obtain ⟨t, hteq⟩ := Finset.card_eq_one.mp hg1
    have htmem : t ∈ G.neighborFinset g ∩ Iso := by rw [hteq]; exact Finset.mem_singleton_self _
    rw [Finset.mem_inter, G.mem_neighborFinset] at htmem
    obtain ⟨hgt, htIso⟩ := htmem
    have htL : t ∈ L := by
      rw [hLdef, Finset.mem_filter]
      refine ⟨htIso, ?_⟩
      exact Finset.Nonempty.card_pos
        ⟨g, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hgt.symm, hg⟩⟩
    rw [hLeq, Finset.mem_insert, Finset.mem_singleton] at htL
    rcases htL with rfl | rfl
    · exact Or.inl (G.mem_neighborFinset _ _ |>.mpr hgt.symm)
    · exact Or.inr (G.mem_neighborFinset _ _ |>.mpr hgt.symm)
  -- Disjoint poor neighbourhoods: a shared poor would meet two twins.
  have hdisjP : Disjoint (G.neighborFinset t₁ ∩ P) (G.neighborFinset t₂ ∩ P) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    rw [Finset.mem_inter, G.mem_neighborFinset] at hg1 hg2
    obtain ⟨hgt₁, hgP⟩ := hg1
    obtain ⟨hgt₂, _⟩ := hg2
    have hg1c := hpoor1 g hgP
    have ht₁mem : t₁ ∈ G.neighborFinset g ∩ Iso := by
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hgt₁.symm, ht₁Iso⟩
    have ht₂mem : t₂ ∈ G.neighborFinset g ∩ Iso := by
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hgt₂.symm, ht₂Iso⟩
    exact hne (Finset.card_le_one.mp (le_of_eq hg1c) t₁ ht₁mem t₂ ht₂mem)
  -- Sum of the two poor degrees is six: all poor incidences land on the two low twins.
  have hPcard : P.card = 6 := by
    rw [hPdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub, hHub, hRcard]
  have hsum6 : (G.neighborFinset t₁ ∩ P).card + (G.neighborFinset t₂ ∩ P).card = 6 := by
    have hcoverP : P = (G.neighborFinset t₁ ∩ P) ∪ (G.neighborFinset t₂ ∩ P) := by
      apply Finset.Subset.antisymm
      · intro g hg
        rcases hcover g hg with h | h
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, hg⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h, hg⟩)
      · exact Finset.union_subset (Finset.inter_subset_right) (Finset.inter_subset_right)
    have := Finset.card_union_of_disjoint hdisjP
    rw [← hcoverP, hPcard] at this
    omega
  exact ⟨t₁, t₂, ht₁Iso, ht₂Iso, hne, ht₁P, ht₂P, hsum6, hdisjP, hcover⟩

end N20

end ACMax
