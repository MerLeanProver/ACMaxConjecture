import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.RichZdeg
import ACMaxConjecture.SmallCases.N18.OctahedronStruct
import ACMaxConjecture.SmallCases.N18.OctahedronForce

/-!
# Octahedron poor/`Z` counting and three-way force (`n = 18`, HARD CRUX core)

This file carries the genuine combinatorial content behind
`octahedron_poor_layer_force_eighteen`.  Over the rigid octahedron (six rich hubs `R`, four poor
hubs `P = Hub \ R`, four high `M`-isolated twins, two low twins, two adjacent `M`-edge endpoints
`Z = univ \ (Hub ∪ Iso)`) we pin the cross-layer handshake and force one of three good
sub-configurations.

* `octahedron_poor_counts_eighteen` — the cross-layer counts: `E(R, Z) = E(P, Z) = 2`,
  `E(R, P) + E(R, R) = 8` (ordered mass), `E(P, P) = E(R, R) + 2` (ordered mass), and each poor hub
  has exactly three neighbours in `R ∪ P ∪ Z`.
* `octahedron_low_twin_poor_eighteen` — the two low twins carry all four poor incidences (each poor
  hub meets exactly one low twin; the low twins split the four poor `1 + 3`, `2 + 2`, or `3 + 1`).
* `octahedron_mass_four_absurd_eighteen` — the rich-internal mass `4` is impossible (a forbidden
  two-hub pair of iso-degree-`3` rich hubs always appears).
* `octahedron_poor_force_b_or_c_eighteen` — the three-way force (branch (c), rich–rich mass `4`, is
  discharged via `octahedron_mass_four_absurd_eighteen`).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Octahedron cross-layer counts (LEAF).**  Over the rigid octahedron the handshake on the
partition `R ⊔ P ⊔ Iso ⊔ Z` (with `P = Hub \ R`, `Z = univ \ (Hub ∪ Iso)`) pins:
`E(R, Z) = 2`, `E(P, Z) = 2`, the ordered rich–poor and rich–rich masses sum to `8`, the ordered
poor–poor mass is the rich–rich mass plus `2`, and every poor hub has exactly three neighbours in
`R ∪ P ∪ Z` (degree `4` minus its single twin). -/
theorem octahedron_poor_counts_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6) :
    (∑ r ∈ R, (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18))).card) = 2 ∧
    (∑ g ∈ Hub \ R, (G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18))).card)
        = 2 ∧
    (∑ r ∈ R, (G.neighborFinset r ∩ (Hub \ R)).card)
        + (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 8 ∧
    (∑ g ∈ Hub \ R, (G.neighborFinset g ∩ (Hub \ R)).card)
        = (∑ r ∈ R, (G.neighborFinset r ∩ R).card) + 2 ∧
    (∀ g ∈ Hub \ R, (G.neighborFinset g ∩ R).card + (G.neighborFinset g ∩ (Hub \ R)).card
      + (G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18))).card = 3) := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set P : Finset (Fin 18) := Hub \ R with hPdef
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
  obtain ⟨hzR2, hzP2⟩ := zdeg_split_sharp_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
    hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT
  rw [← hReq, ← hZdef] at hzR2
  have hzP2' : ∑ g ∈ P, (G.neighborFinset g ∩ Z).card = 2 := by
    have hPfilter : P = Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hPdef, hReq, Finset.filter_not]
    rw [hPfilter]; exact hzP2
  -- `∑_R |N ∩ Iso| = 14`.
  have hisoR14 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 14 :=
    (octahedron_trace_saturate_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
      hshare hno2hub hT hRcard hnozero).2
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
  -- Sum the split over `R`: `mRR + E(R,P) + 14 + 2 = 24`.
  have hsumR : ∑ a ∈ R, ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
      + (G.neighborFinset a ∩ Iso).card + (G.neighborFinset a ∩ Z).card) = 24 := by
    rw [Finset.sum_congr rfl (fun a ha => hsplit a (hRsub ha)), Finset.sum_const, hRcard,
      smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsumR
  -- Sum the split over `P`: `E(P,R) + E(P,P) + 4 + 2 = 16`.
  have hPcard : P.card = 4 := by
    rw [hPdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub, hHub, hRcard]
  have hPsub : P ⊆ Hub := by rw [hPdef]; exact Finset.sdiff_subset
  have hsumP : ∑ a ∈ P, ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
      + (G.neighborFinset a ∩ Iso).card + (G.neighborFinset a ∩ Z).card) = 16 := by
    rw [Finset.sum_congr rfl (fun a ha => hsplit a (hPsub ha)), Finset.sum_const, hPcard,
      smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsumP
  have hisoP4 : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 4 := by
    rw [Finset.sum_congr rfl (fun g hg => hpoor1 g hg), Finset.sum_const, hPcard, smul_eq_mul,
      mul_one]
  -- `E(R,P) = E(P,R)` cross count.
  have hcrossRP : ∑ a ∈ R, (G.neighborFinset a ∩ P).card
      = ∑ a ∈ P, (G.neighborFinset a ∩ R).card := cross_count G R P
  refine ⟨hzR2, hzP2', ?_, ?_, ?_⟩
  · omega
  · omega
  · intro g hg
    have h1 := hsplit g (hPsub hg)
    have h2 := hpoor1 g hg
    omega

/-- **Octahedron low-twin poor incidence (LEAF).**  There are exactly two low twins `t₁ ≠ t₂` in
`Iso`, each meeting at least one poor hub (`P = Hub \ R`); their poor neighbourhoods are disjoint and
together cover all four poor hubs with `|N(t₁) ∩ P| + |N(t₂) ∩ P| = 4` (so the four poor split
`1 + 3`, `2 + 2`, or `3 + 1`).  Every poor hub meets exactly one of `t₁`, `t₂`. -/
theorem octahedron_low_twin_poor_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    ∃ t₁ t₂ : Fin 18, t₁ ∈ Iso ∧ t₂ ∈ Iso ∧ t₁ ≠ t₂ ∧
      1 ≤ (G.neighborFinset t₁ ∩ (Hub \ R)).card ∧
      1 ≤ (G.neighborFinset t₂ ∩ (Hub \ R)).card ∧
      (G.neighborFinset t₁ ∩ (Hub \ R)).card + (G.neighborFinset t₂ ∩ (Hub \ R)).card = 4 ∧
      Disjoint (G.neighborFinset t₁ ∩ (Hub \ R)) (G.neighborFinset t₂ ∩ (Hub \ R)) ∧
      ∀ g ∈ Hub \ R, g ∈ G.neighborFinset t₁ ∨ g ∈ G.neighborFinset t₂ := by
  classical
  set P : Finset (Fin 18) := Hub \ R with hPdef
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
    octahedron_struct_eighteen G Hub Iso R hReq hiso3 hHub hIso hnozero hRcard hhigh4 htle3
  set L : Finset (Fin 18) := Iso.filter (fun t => 1 ≤ (G.neighborFinset t ∩ (Hub \ R)).card)
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
    -- `t` is a low twin (it meets the poor `g`), so `t ∈ L = {t₁, t₂}`.
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
  -- Sum of the two poor degrees is four: all poor incidences land on the two low twins.
  have hPcard : P.card = 4 := by
    rw [hPdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub, hHub, hRcard]
  have hsum4 : (G.neighborFinset t₁ ∩ P).card + (G.neighborFinset t₂ ∩ P).card = 4 := by
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
  exact ⟨t₁, t₂, ht₁Iso, ht₂Iso, hne, ht₁P, ht₂P, hsum4, hdisjP, hcover⟩

/-- **Mass-`4` octahedron is impossible (LEAF).**  In the rigid octahedron with no two-hub pair the
ordered rich-internal edge mass cannot be `4`.  The saturation `∑ offDiag + mass = 30` with `mass = 4`
pins the twin rich-degree profile (`n₃ = 4`, `n₂ = 1`, `n₁ = 0`).  Hence any rich hub `x` of
iso-degree `≥ 3` has its three twins' rich partners injecting (disjointly, by share `≤ 1`) onto the
five other rich hubs — all non-adjacent to `x` (else a `4 + 4 + 3` triangle) — so `x` is non-adjacent
to *every* other rich hub and its iso-degree is exactly `3`.  Two such iso-degree-`3` hubs (forced by
`∑ = 14`) are then a non-adjacent degree-`4` pair, each with `≥ 2` private twins: a forbidden
two-hub. -/
theorem octahedron_mass_four_absurd_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso R : Finset (Fin 18))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3)
    (hm4 : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4) : False := by
  classical
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  have hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hReq, Finset.mem_filter] at ha; exact ha.2
  obtain ⟨hsat, h14⟩ := octahedron_trace_saturate_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub
    hIso hisodeg3 hshare hno2hub hT hRcard hnozero
  have hoff : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card = 26 := by omega
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 14 := by
    rw [cross_count G Iso R]; exact h14
  -- Twin rich-degree profile counts.
  set n0 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card with hn0
  set n1 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card with hn1
  set n2 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card with hn2
  set n3 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card with hn3
  have hI : n0 + n1 + n2 + n3 = 6 := by
    rw [hn0, hn1, hn2, hn3, ← hIso, Finset.card_eq_sum_ones Iso]
    simp only [Finset.card_filter]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := htle3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  have hII : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = n1 + 2 * n2 + 3 * n3 := by
    rw [hn1, hn2, hn3]
    simp only [Finset.card_filter, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := htle3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  have hIII : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card = 2 * n2 + 6 * n3 := by
    rw [hn2, hn3]
    simp only [Finset.offDiag_card, Finset.card_filter, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := htle3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  rw [hcross] at hII
  rw [hoff] at hIII
  have hn1z : n1 = 0 := by omega
  have hn2le : n2 ≤ 1 := by omega
  -- No twin meets exactly one rich hub.
  have hF2 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≠ 1 := by
    intro t ht h1
    have hmem : t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1) :=
      Finset.mem_filter.mpr ⟨ht, h1⟩
    have : 1 ≤ n1 := by rw [hn1]; exact Finset.card_pos.mpr ⟨t, hmem⟩
    omega
  -- Key claim: an iso-degree-`≥ 3` rich hub is non-adjacent to every other rich hub, of iso-deg `3`.
  have hclaim : ∀ x ∈ R, 3 ≤ (G.neighborFinset x ∩ Iso).card →
      (G.neighborFinset x ∩ Iso).card = 3 ∧ ∀ r ∈ R, r ≠ x → ¬G.Adj x r := by
    intro x hxR hx3
    set T : Finset (Fin 18) := G.neighborFinset x ∩ Iso with hTdef
    have hxIsoT : T.card = (G.neighborFinset x ∩ Iso).card := rfl
    -- each twin `t ∈ T` contains `x` in its rich-neighbourhood, with rich-degree in `{2, 3}`.
    have hxinNt : ∀ t ∈ T, x ∈ G.neighborFinset t ∩ R := by
      intro t ht
      rw [hTdef, Finset.mem_inter, G.mem_neighborFinset] at ht
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨ht.1.symm, hxR⟩
    have htIso : ∀ t ∈ T, t ∈ Iso := by
      intro t ht; rw [hTdef, Finset.mem_inter] at ht; exact ht.2
    have hrd2 : ∀ t ∈ T, 2 ≤ (G.neighborFinset t ∩ R).card := by
      intro t ht
      have hx := hxinNt t ht
      have hpos : 1 ≤ (G.neighborFinset t ∩ R).card := Finset.card_pos.mpr ⟨x, hx⟩
      have hne1 := hF2 t (htIso t ht)
      omega
    have hrd3 : ∀ t ∈ T, (G.neighborFinset t ∩ R).card ≤ 3 := fun t ht => htle3 t (htIso t ht)
    -- The target set `NA` of other rich hubs non-adjacent to `x`.
    set NA : Finset (Fin 18) := (R.erase x).filter (fun r => ¬G.Adj x r) with hNAdef
    set Sx : Finset (Σ _ : Fin 18, Fin 18) :=
      T.sigma (fun t => (G.neighborFinset t ∩ R).erase x) with hSxdef
    have hSxcard : Sx.card = ∑ t ∈ T, ((G.neighborFinset t ∩ R).erase x).card :=
      Finset.card_sigma _ _
    have hSxsum : Sx.card = ∑ t ∈ T, ((G.neighborFinset t ∩ R).card - 1) := by
      rw [hSxcard]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_erase_of_mem (hxinNt t ht)]
    have hRerase : (R.erase x).card = 5 := by rw [Finset.card_erase_of_mem hxR, hRcard]
    -- General lower bound `3·|T| ≤ ∑ richdeg + 1` (at most one twin meets exactly two rich).
    have hsumlb : 3 * T.card ≤ (∑ t ∈ T, (G.neighborFinset t ∩ R).card) + 1 := by
      have hpt : ∀ t ∈ T, 3 ≤ (G.neighborFinset t ∩ R).card
          + (if (G.neighborFinset t ∩ R).card = 2 then 1 else 0) := by
        intro t ht
        have h2 := hrd2 t ht; have h3 := hrd3 t ht
        split_ifs with h <;> omega
      have hsumpt : (∑ t ∈ T, 3) ≤ ∑ t ∈ T, ((G.neighborFinset t ∩ R).card
          + (if (G.neighborFinset t ∩ R).card = 2 then 1 else 0)) := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib] at hsumpt
      have hind : ∑ t ∈ T, (if (G.neighborFinset t ∩ R).card = 2 then 1 else 0)
          = (T.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card := by
        rw [Finset.card_filter]
      have hsub2 : T.filter (fun t => (G.neighborFinset t ∩ R).card = 2)
          ⊆ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2) := by
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        exact ⟨htIso t ht.1, ht.2⟩
      have hindle : ∑ t ∈ T, (if (G.neighborFinset t ∩ R).card = 2 then 1 else 0) ≤ 1 := by
        rw [hind]
        have := Finset.card_le_card hsub2
        rw [← hn2] at this; omega
      have hTconst : ∑ _t ∈ T, 3 = 3 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hTconst] at hsumpt
      omega
    -- `Sx.card + |T| = ∑ richdeg`.
    have hsplitT : Sx.card + T.card = ∑ t ∈ T, (G.neighborFinset t ∩ R).card := by
      rw [hSxsum, Finset.card_eq_sum_ones T, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht; have := hrd2 t ht; omega
    have hTge : 3 ≤ T.card := by rw [hxIsoT]; exact hx3
    -- The injection `Sx → NA`.
    have hmapsto : ∀ p ∈ Sx, p.2 ∈ NA := by
      intro p hp
      rw [hSxdef, Finset.mem_sigma] at hp
      obtain ⟨htT, hp2⟩ := hp
      rw [Finset.mem_erase, Finset.mem_inter, G.mem_neighborFinset] at hp2
      obtain ⟨hpne, hadj, hpR⟩ := hp2
      rw [hNAdef, Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨hpne, hpR⟩, ?_⟩
      intro hxadj
      have hxt : x ≠ p.1 := by
        intro he
        exact Finset.disjoint_left.mp hdisj (hRsub hxR) (he ▸ htIso p.1 htT)
      have hpt' : p.2 ≠ p.1 := by
        intro he
        exact Finset.disjoint_left.mp hdisj (hRsub hpR) (he ▸ htIso p.1 htT)
      have hxinp1 : G.Adj x p.1 := by
        have := hxinNt p.1 htT
        rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1.symm
      exact hT ⟨x, p.2, p.1, hpne.symm, hpt', hxt, hxadj, hadj.symm, hxinp1, by
        rw [hdeg4 x (hRsub hxR), hdeg4 p.2 (hRsub hpR), hisodeg3 p.1 (htIso p.1 htT)]⟩
    have hinj : Set.InjOn (fun p : Σ _ : Fin 18, Fin 18 => p.2) Sx := by
      intro p hp q hq hpq
      rw [Finset.mem_coe, hSxdef, Finset.mem_sigma] at hp hq
      obtain ⟨hpT, hp2⟩ := hp
      obtain ⟨hqT, hq2⟩ := hq
      rw [Finset.mem_erase, Finset.mem_inter, G.mem_neighborFinset] at hp2 hq2
      obtain ⟨hpne, hpadj, hpR⟩ := hp2
      obtain ⟨hqne, hqadj, hqR⟩ := hq2
      simp only at hpq
      by_contra hne
      have hp1q1 : p.1 ≠ q.1 := fun he => hne (Sigma.ext he (heq_of_eq hpq))
      -- `p.1, q.1 ∈ N(x) ∩ N(p.2) ∩ Iso` with `p.2 ≠ x`: shares two twins ⇒ contradiction.
      have hxNp1 : G.Adj x p.1 := by
        have := hxinNt p.1 hpT
        rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1.symm
      have hxNq1 : G.Adj x q.1 := by
        have := hxinNt q.1 hqT
        rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1.symm
      have hp2x : p.2 ≠ x := hpne
      have hsh : (G.neighborFinset x ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1 := by
        by_cases hxp2 : G.Adj x p.2
        · have hpInNA := hmapsto p (by
            rw [hSxdef, Finset.mem_sigma]
            exact ⟨hpT, by rw [Finset.mem_erase, Finset.mem_inter, G.mem_neighborFinset]
                           exact ⟨hpne, hpadj, hpR⟩⟩)
          rw [hNAdef, Finset.mem_filter] at hpInNA
          exact absurd hxp2 hpInNA.2
        · exact hshare x (hRsub hxR) (hdeg4 x (hRsub hxR)) p.2 (hRsub hpR) (hdeg4 p.2 (hRsub hpR))
            (Ne.symm hp2x) hxp2
      have hp1mem : p.1 ∈ G.neighborFinset x ∩ G.neighborFinset p.2 ∩ Iso := by
        rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
        exact ⟨⟨hxNp1, hpadj.symm⟩, htIso p.1 hpT⟩
      have hq1mem : q.1 ∈ G.neighborFinset x ∩ G.neighborFinset p.2 ∩ Iso := by
        rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
        refine ⟨⟨hxNq1, ?_⟩, htIso q.1 hqT⟩
        rw [hpq]; exact hqadj.symm
      exact hp1q1 (Finset.card_le_one.mp hsh p.1 hp1mem q.1 hq1mem)
    have hSxleNA : Sx.card ≤ NA.card :=
      Finset.card_le_card_of_injOn (fun p => p.2) hmapsto hinj
    have hNAsub : NA ⊆ R.erase x := Finset.filter_subset _ _
    have hNAle : NA.card ≤ 5 := by rw [← hRerase]; exact Finset.card_le_card hNAsub
    -- `|T| = 3` and `Sx.card = 5`, so the image `NA` exhausts `R.erase x`.
    have hT3 : T.card = 3 := by omega
    have hNAeq : NA = R.erase x :=
      Finset.eq_of_subset_of_card_le hNAsub (by omega)
    have hxeq3 : (G.neighborFinset x ∩ Iso).card = 3 := by rw [← hxIsoT]; exact hT3
    refine ⟨hxeq3, ?_⟩
    intro r hrR hrx hadj
    have hrNA : r ∈ NA := by rw [hNAeq]; exact Finset.mem_erase.mpr ⟨hrx, hrR⟩
    rw [hNAdef, Finset.mem_filter] at hrNA
    exact hrNA.2 hadj
  -- All rich iso-degrees are `≤ 3`.
  have hle3R : ∀ x ∈ R, (G.neighborFinset x ∩ Iso).card ≤ 3 := by
    intro x hxR
    by_contra h
    have := (hclaim x hxR (by omega)).1; omega
  -- Exactly two rich hubs have iso-degree `3`.
  have hcount : (R.filter (fun x => (G.neighborFinset x ∩ Iso).card = 3)).card = 2 := by
    have hsplit : ∑ x ∈ R, (G.neighborFinset x ∩ Iso).card
        = ∑ x ∈ R, (2 + (if (G.neighborFinset x ∩ Iso).card = 3 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hxR
      have h2 := hRrich x hxR; have h3 := hle3R x hxR
      split_ifs with h <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_const, hRcard, smul_eq_mul] at hsplit
    have hind : ∑ x ∈ R, (if (G.neighborFinset x ∩ Iso).card = 3 then 1 else 0)
        = (R.filter (fun x => (G.neighborFinset x ∩ Iso).card = 3)).card := by
      rw [Finset.card_filter]
    rw [hind, h14] at hsplit
    omega
  obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.mp hcount
  have hxmem : x ∈ R.filter (fun x => (G.neighborFinset x ∩ Iso).card = 3) := by
    rw [hxyeq]; exact Finset.mem_insert_self _ _
  have hymem : y ∈ R.filter (fun x => (G.neighborFinset x ∩ Iso).card = 3) := by
    rw [hxyeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_filter] at hxmem hymem
  obtain ⟨hxR, hx3⟩ := hxmem
  obtain ⟨hyR, hy3⟩ := hymem
  have hnadj : ¬G.Adj x y := (hclaim x hxR (by omega)).2 y hyR (Ne.symm hxy)
  -- The two iso-degree-`3` hubs form a forbidden two-hub pair.
  have hsh : (G.neighborFinset x ∩ G.neighborFinset y ∩ Iso).card ≤ 1 :=
    hshare x (hRsub hxR) (hdeg4 x (hRsub hxR)) y (hRsub hyR) (hdeg4 y (hRsub hyR)) hxy hnadj
  have hpx : 2 ≤ ((G.neighborFinset x ∩ Iso) \ G.neighborFinset y).card := by
    have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset x ∩ Iso) (G.neighborFinset y)
    have hinter : (G.neighborFinset x ∩ Iso) ∩ G.neighborFinset y
        = G.neighborFinset x ∩ G.neighborFinset y ∩ Iso := Finset.inter_right_comm _ _ _
    rw [hinter] at hkey; omega
  have hpy : 2 ≤ ((G.neighborFinset y ∩ Iso) \ G.neighborFinset x).card := by
    have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset y ∩ Iso) (G.neighborFinset x)
    have hinter : (G.neighborFinset y ∩ Iso) ∩ G.neighborFinset x
        = G.neighborFinset y ∩ G.neighborFinset x ∩ Iso := Finset.inter_right_comm _ _ _
    have hsh' : (G.neighborFinset y ∩ G.neighborFinset x ∩ Iso).card ≤ 1 := by
      rw [Finset.inter_comm (G.neighborFinset y) (G.neighborFinset x)]; exact hsh
    rw [hinter] at hkey; omega
  exact hno2hub ⟨x, y, hRsub hxR, hRsub hyR, hdeg4 x (hRsub hxR), hdeg4 y (hRsub hyR), hxy,
    hnadj, hpx, hpy⟩

/-- **Octahedron poor/`Z` three-way force core (HARD CRUX).**  The rigid octahedron forces one of
three good sub-configurations.  If a low twin meets two adjacent poor hubs we get a triangle (a);
otherwise the rich–rich mass `∈ {4, 6}` decides: mass `6` makes the four poor a `C₄` whose diagonal
pair with a low twin is a `K₂,₃` (b); mass `4` matches the two `Z`-endpoints to two adjacent rich
hubs, a `C₄` `r₁–z₁–z₂–r₂` (c).  Mass `4` is in fact vacuous (`octahedron_mass_four_absurd_eighteen`),
so branch (c)'s rich edge follows from that contradiction. -/
theorem octahedron_poor_force_b_or_c_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso R : Finset (Fin 18))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 6)
    (hmass : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨
      (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    (∃ g₁ g₂ t : Fin 18, g₁ ∈ Hub ∧ g₂ ∈ Hub ∧ t ∈ Iso ∧ g₁ ≠ g₂ ∧
      G.Adj g₁ g₂ ∧ G.Adj g₁ t ∧ G.Adj g₂ t) ∨
    (∃ a b c d t : Fin 18, a ∈ Hub ∧ b ∈ Hub ∧ c ∈ Hub ∧ d ∈ Hub ∧ t ∈ Iso ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a t ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b t ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c t ∧ ¬G.Adj d t ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∨
    (∃ r₁ r₂ z₁ z₂ : Fin 18, r₁ ∈ Hub ∧ r₂ ∈ Hub ∧
      z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)) ∧
      z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)) ∧
      G.degree z₁ = 3 ∧ G.degree z₂ = 3 ∧
      G.Adj r₁ z₁ ∧ G.Adj z₁ z₂ ∧ G.Adj z₂ r₂ ∧ G.Adj r₂ r₁ ∧
      ¬G.Adj r₁ z₂ ∧ ¬G.Adj z₁ r₂ ∧ r₁ ≠ r₂ ∧ z₁ ≠ z₂) := by
  classical
  set P : Finset (Fin 18) := Hub \ R with hPdef
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  have hPsub : P ⊆ Hub := by rw [hPdef]; exact Finset.sdiff_subset
  obtain ⟨hRZ, hPZ, hRPmass, hPPmass, hpoor3⟩ := octahedron_poor_counts_eighteen G Hub Iso R hReq
    hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard
  obtain ⟨t₁, t₂, ht₁Iso, ht₂Iso, htne, ht₁pos, ht₂pos, htsum4, htdisj, htcover⟩ :=
    octahedron_low_twin_poor_eighteen G Hub Iso R hReq hiso3 hHub hIso hnozero hRcard hhigh4 htle3
  set P₁ : Finset (Fin 18) := G.neighborFinset t₁ ∩ P with hP₁def
  set P₂ : Finset (Fin 18) := G.neighborFinset t₂ ∩ P with hP₂def
  -- Branch (a): some low twin meets two adjacent poor hubs.
  by_cases hA1 : ∃ x y : Fin 18, x ∈ P₁ ∧ y ∈ P₁ ∧ G.Adj x y
  · obtain ⟨x, y, hxP₁, hyP₁, hxy⟩ := hA1
    rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset] at hxP₁ hyP₁
    exact Or.inl ⟨x, y, t₁, hPsub hxP₁.2, hPsub hyP₁.2, ht₁Iso, G.ne_of_adj hxy, hxy,
      hxP₁.1.symm, hyP₁.1.symm⟩
  by_cases hA2 : ∃ x y : Fin 18, x ∈ P₂ ∧ y ∈ P₂ ∧ G.Adj x y
  · obtain ⟨x, y, hxP₂, hyP₂, hxy⟩ := hA2
    rw [hP₂def, Finset.mem_inter, G.mem_neighborFinset] at hxP₂ hyP₂
    exact Or.inl ⟨x, y, t₂, hPsub hxP₂.2, hPsub hyP₂.2, ht₂Iso, G.ne_of_adj hxy, hxy,
      hxP₂.1.symm, hyP₂.1.symm⟩
  -- `¬a`: both low twins have independent poor neighbourhoods.
  have hindep1 : ∀ x ∈ P₁, ∀ y ∈ P₁, ¬G.Adj x y :=
    fun x hx y hy hadj => hA1 ⟨x, y, hx, hy, hadj⟩
  have hindep2 : ∀ x ∈ P₂, ∀ y ∈ P₂, ¬G.Adj x y :=
    fun x hx y hy hadj => hA2 ⟨x, y, hx, hy, hadj⟩
  -- `P = P₁ ⊔ P₂`.
  have hcoverP : P = P₁ ∪ P₂ := by
    apply Finset.Subset.antisymm
    · intro g hg
      rcases htcover g hg with h | h
      · exact Finset.mem_union_left _ (by rw [hP₁def, Finset.mem_inter]; exact ⟨h, hg⟩)
      · exact Finset.mem_union_right _ (by rw [hP₂def, Finset.mem_inter]; exact ⟨h, hg⟩)
    · exact Finset.union_subset (by rw [hP₁def]; exact Finset.inter_subset_right)
        (by rw [hP₂def]; exact Finset.inter_subset_right)
  rcases hmass with hm4 | hm6
  · -- Branch (c): rich–rich mass 4.  Matched-`Z` `C₄`  `r₁–z₁–z₂–r₂` (rich edge is one `sorry`).
    right; right
    set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
    have hZrig := octahedron_Z_rigid_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
      hleak
    rw [← hZdef] at hZrig
    obtain ⟨hZcard2, hzfacts, hzadjall⟩ := hZrig
    obtain ⟨z₁, z₂, hzne, hZeq⟩ := Finset.card_eq_two.mp hZcard2
    have hz₁Z : z₁ ∈ Z := by rw [hZeq]; exact Finset.mem_insert_self _ _
    have hz₂Z : z₂ ∈ Z := by rw [hZeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hz₁z₂ : G.Adj z₁ z₂ := hzadjall z₁ hz₁Z z₂ hz₂Z hzne
    obtain ⟨_, _, hdz₁⟩ := hzfacts z₁ hz₁Z
    obtain ⟨_, _, hdz₂⟩ := hzfacts z₂ hz₂Z
    -- Each `Z`-endpoint meets at most one rich hub.
    have hz2rich : ∀ z ∈ Z, (G.neighborFinset z ∩ R).card ≤ 1 := by
      intro z hz
      have hzle := no_z_two_rich_hubs_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
        hdsum hleak hshare hno2hub hC4 hT z hz
      rwa [← hReq] at hzle
    -- `E(R, Z) = 2` splits as `1 + 1` over the two endpoints.
    have hzRsum : (G.neighborFinset z₁ ∩ R).card + (G.neighborFinset z₂ ∩ R).card = 2 := by
      have hc := cross_count G R Z
      rw [hRZ, hZeq, Finset.sum_pair hzne] at hc
      omega
    have hz₁R1 : (G.neighborFinset z₁ ∩ R).card = 1 := by
      have h1 := hz2rich z₁ hz₁Z; have h2 := hz2rich z₂ hz₂Z; omega
    have hz₂R1 : (G.neighborFinset z₂ ∩ R).card = 1 := by
      have h1 := hz2rich z₁ hz₁Z; have h2 := hz2rich z₂ hz₂Z; omega
    obtain ⟨r₁, hr₁eq⟩ := Finset.card_eq_one.mp hz₁R1
    obtain ⟨r₂, hr₂eq⟩ := Finset.card_eq_one.mp hz₂R1
    have hr₁mem : r₁ ∈ G.neighborFinset z₁ ∩ R := by rw [hr₁eq]; exact Finset.mem_singleton_self _
    have hr₂mem : r₂ ∈ G.neighborFinset z₂ ∩ R := by rw [hr₂eq]; exact Finset.mem_singleton_self _
    rw [Finset.mem_inter, G.mem_neighborFinset] at hr₁mem hr₂mem
    obtain ⟨hz₁r₁, hr₁R⟩ := hr₁mem
    obtain ⟨hz₂r₂, hr₂R⟩ := hr₂mem
    have hr₁Hub : r₁ ∈ Hub := hRsub hr₁R
    have hr₂Hub : r₂ ∈ Hub := hRsub hr₂R
    have hz₁nHub : z₁ ∉ Hub := by
      rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz₁Z; exact hz₁Z.2.1
    have hz₂nHub : z₂ ∉ Hub := by
      rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz₂Z; exact hz₂Z.2.1
    -- `r₁ ≠ r₂`: a shared rich hub closes a triangle `z₁–z₂–r` of degree sum `3 + 3 + 4 = 10`.
    have hr₁r₂ne : r₁ ≠ r₂ := by
      intro heq
      exact hT ⟨z₁, z₂, r₁, hzne, (ne_of_mem_of_not_mem hr₁Hub hz₂nHub).symm,
        (ne_of_mem_of_not_mem hr₁Hub hz₁nHub).symm, hz₁z₂, by rw [heq]; exact hz₂r₂, hz₁r₁,
        by rw [hdz₁, hdz₂, hdeg4 r₁ hr₁Hub]; omega⟩
    -- The two diagonals are non-edges (each endpoint meets only its own rich hub).
    have hnr₁z₂ : ¬G.Adj r₁ z₂ := by
      intro h
      have hmem : r₁ ∈ G.neighborFinset z₂ ∩ R := by
        rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨h.symm, hr₁R⟩
      rw [hr₂eq, Finset.mem_singleton] at hmem; exact hr₁r₂ne hmem
    have hnz₁r₂ : ¬G.Adj z₁ r₂ := by
      intro h
      have hmem : r₂ ∈ G.neighborFinset z₁ ∩ R := by
        rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨h, hr₂R⟩
      rw [hr₁eq, Finset.mem_singleton] at hmem; exact hr₁r₂ne hmem.symm
    -- The rich edge `r₂ ~ r₁`.  Branch (c) (rich–rich mass `4`) is in fact vacuous: a mass-`4` rigid
    -- octahedron always contains a forbidden two-hub pair (two iso-degree-`3` rich hubs), so this
    -- case never occurs and the edge follows from the resulting contradiction.
    have hr₂r₁ : G.Adj r₂ r₁ :=
      absurd hm4 (fun hm => octahedron_mass_four_absurd_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj
        hHub hIso hisodeg3 hshare hno2hub hT hnozero hRcard htle3 hm)
    exact ⟨r₁, r₂, z₁, z₂, hr₁Hub, hr₂Hub, hz₁Z, hz₂Z, hdz₁, hdz₂, hz₁r₁.symm, hz₁z₂, hz₂r₂,
      hr₂r₁, hnr₁z₂, hnz₁r₂, hr₁r₂ne, hzne⟩
  · -- Branch (b): rich–rich mass 6 → four poor form a `C₄` → `K₂,₃`.
    right; left
    -- The ordered poor–poor mass is `8`.
    have hPP8 : ∑ g ∈ P, (G.neighborFinset g ∩ P).card = 8 := by rw [hPPmass, hm6]
    -- Each poor in `P₁` has all its poor neighbours in `P₂` (and vice versa).
    have hsub1 : ∀ a ∈ P₁, G.neighborFinset a ∩ P ⊆ P₂ := by
      intro a ha x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      have hxP : x ∈ P := hx.2
      rw [hcoverP, Finset.mem_union] at hxP
      rcases hxP with hx1 | hx2
      · exact absurd hx.1 (hindep1 a ha x hx1)
      · exact hx2
    have hsub2 : ∀ a ∈ P₂, G.neighborFinset a ∩ P ⊆ P₁ := by
      intro a ha x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      have hxP : x ∈ P := hx.2
      rw [hcoverP, Finset.mem_union] at hxP
      rcases hxP with hx1 | hx2
      · exact hx1
      · exact absurd hx.1 (hindep2 a ha x hx2)
    have hdisj12 : Disjoint P₁ P₂ := htdisj
    -- Split the poor–poor mass over `P = P₁ ⊔ P₂`.
    have hsplitsum : ∑ g ∈ P, (G.neighborFinset g ∩ P).card
        = (∑ g ∈ P₁, (G.neighborFinset g ∩ P).card) + ∑ g ∈ P₂, (G.neighborFinset g ∩ P).card := by
      rw [hcoverP, Finset.sum_union hdisj12]
    -- Bound each half by `|P₁|·|P₂|`.
    have hbound1 : ∀ a ∈ P₁, (G.neighborFinset a ∩ P).card ≤ P₂.card :=
      fun a ha => Finset.card_le_card (hsub1 a ha)
    have hbound2 : ∀ a ∈ P₂, (G.neighborFinset a ∩ P).card ≤ P₁.card :=
      fun a ha => Finset.card_le_card (hsub2 a ha)
    have hS1le : ∑ g ∈ P₁, (G.neighborFinset g ∩ P).card ≤ P₁.card * P₂.card := by
      calc ∑ g ∈ P₁, (G.neighborFinset g ∩ P).card ≤ ∑ _g ∈ P₁, P₂.card :=
            Finset.sum_le_sum hbound1
        _ = P₁.card * P₂.card := by rw [Finset.sum_const, smul_eq_mul]
    have hS2le : ∑ g ∈ P₂, (G.neighborFinset g ∩ P).card ≤ P₂.card * P₁.card := by
      calc ∑ g ∈ P₂, (G.neighborFinset g ∩ P).card ≤ ∑ _g ∈ P₂, P₁.card :=
            Finset.sum_le_sum hbound2
        _ = P₂.card * P₁.card := by rw [Finset.sum_const, smul_eq_mul]
    -- `|P₁| = |P₂| = 2` (the `1 + 3` / `3 + 1` splits give mass `≤ 6 < 8`).
    have hsum : P₁.card + P₂.card = 4 := htsum4
    have hbig : 8 ≤ P₁.card * P₂.card + P₂.card * P₁.card := by omega
    have hcard12 : P₁.card = 2 ∧ P₂.card = 2 := by
      rcases (show P₁.card = 1 ∨ P₁.card = 2 ∨ P₁.card = 3 by omega) with h | h | h <;>
        (rw [h] at hbig ⊢; omega)
    obtain ⟨hc1, hc2⟩ := hcard12
    -- Equality forces every poor in `P₁` adjacent to all of `P₂`.
    have hS1val : ∑ g ∈ P₁, (G.neighborFinset g ∩ P).card = 4 := by
      rw [hc1, hc2] at hS1le hS2le; omega
    have heach1 : ∀ a ∈ P₁, (G.neighborFinset a ∩ P).card = P₂.card :=
      (Finset.sum_eq_sum_iff_of_le hbound1).mp
        (by rw [Finset.sum_const, smul_eq_mul, hc1, hc2]; exact hS1val)
    have hfull1 : ∀ a ∈ P₁, G.neighborFinset a ∩ P = P₂ := fun a ha =>
      Finset.eq_of_subset_of_card_le (hsub1 a ha) (heach1 a ha).ge
    -- Extract the two poor of each low twin.
    obtain ⟨a, b, hab, hP₁eq⟩ := Finset.card_eq_two.mp hc1
    obtain ⟨c, d, hcd, hP₂eq⟩ := Finset.card_eq_two.mp hc2
    have haP₁ : a ∈ P₁ := by rw [hP₁eq]; exact Finset.mem_insert_self _ _
    have hbP₁ : b ∈ P₁ := by rw [hP₁eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hcP₂ : c ∈ P₂ := by rw [hP₂eq]; exact Finset.mem_insert_self _ _
    have hdP₂ : d ∈ P₂ := by rw [hP₂eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    -- Adjacencies from `N(a) ∩ P = P₂ = {c, d}`.
    have hac : G.Adj a c := by
      have : c ∈ G.neighborFinset a ∩ P := by rw [hfull1 a haP₁]; exact hcP₂
      rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
    have had : G.Adj a d := by
      have : d ∈ G.neighborFinset a ∩ P := by rw [hfull1 a haP₁]; exact hdP₂
      rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
    have hbc : G.Adj b c := by
      have : c ∈ G.neighborFinset b ∩ P := by rw [hfull1 b hbP₁]; exact hcP₂
      rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
    have hbd : G.Adj b d := by
      have : d ∈ G.neighborFinset b ∩ P := by rw [hfull1 b hbP₁]; exact hdP₂
      rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
    -- `a, b ∈ N(t₁)`; `c, d ∉ N(t₁)`.
    have hat₁ : G.Adj a t₁ := by
      have := haP₁; rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1.symm
    have hbt₁ : G.Adj b t₁ := by
      have := hbP₁; rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1.symm
    have haHub : a ∈ Hub := hPsub (by have := haP₁; rw [hP₁def, Finset.mem_inter] at this; exact this.2)
    have hbHub : b ∈ Hub := hPsub (by have := hbP₁; rw [hP₁def, Finset.mem_inter] at this; exact this.2)
    have hcHub : c ∈ Hub := hPsub (by have := hcP₂; rw [hP₂def, Finset.mem_inter] at this; exact this.2)
    have hdHub : d ∈ Hub := hPsub (by have := hdP₂; rw [hP₂def, Finset.mem_inter] at this; exact this.2)
    have hnct₁ : ¬G.Adj c t₁ := by
      intro h
      have hcP₁ : c ∈ P₁ := by
        rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset]
        refine ⟨h.symm, ?_⟩
        have := hcP₂; rw [hP₂def, Finset.mem_inter] at this; exact this.2
      exact Finset.disjoint_left.mp hdisj12 hcP₁ hcP₂
    have hndt₁ : ¬G.Adj d t₁ := by
      intro h
      have hdP₁ : d ∈ P₁ := by
        rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset]
        refine ⟨h.symm, ?_⟩
        have := hdP₂; rw [hP₂def, Finset.mem_inter] at this; exact this.2
      exact Finset.disjoint_left.mp hdisj12 hdP₁ hdP₂
    have hnab : ¬G.Adj a b := hindep1 a haP₁ b hbP₁
    have hncd : ¬G.Adj c d := hindep2 c hcP₂ d hdP₂
    have hat : a ≠ t₁ := fun he => Finset.disjoint_left.mp hdisj haHub (he ▸ ht₁Iso)
    have hbt : b ≠ t₁ := fun he => Finset.disjoint_left.mp hdisj hbHub (he ▸ ht₁Iso)
    have hct : c ≠ t₁ := fun he => Finset.disjoint_left.mp hdisj hcHub (he ▸ ht₁Iso)
    have hdt : d ≠ t₁ := fun he => Finset.disjoint_left.mp hdisj hdHub (he ▸ ht₁Iso)
    have hac' : a ≠ c := fun he => Finset.disjoint_left.mp hdisj12 haP₁ (he ▸ hcP₂)
    have had' : a ≠ d := fun he => Finset.disjoint_left.mp hdisj12 haP₁ (he ▸ hdP₂)
    have hbc' : b ≠ c := fun he => Finset.disjoint_left.mp hdisj12 hbP₁ (he ▸ hcP₂)
    have hbd' : b ≠ d := fun he => Finset.disjoint_left.mp hdisj12 hbP₁ (he ▸ hdP₂)
    exact ⟨a, b, c, d, t₁, haHub, hbHub, hcHub, hdHub, ht₁Iso, hac, had, hat₁, hbc, hbd, hbt₁,
      hnab, hncd, hnct₁, hndt₁, hab, hac', had', hbc', hbd', hcd⟩

end N18
