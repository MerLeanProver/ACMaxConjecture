import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.NineSevenCount
import ACMaxConjecture.SmallCases.N18.NineSevenEdge
import ACMaxConjecture.SmallCases.N18.NineSevenForce
import ACMaxConjecture.SmallCases.N18.NineSevenPoorTriangle

/-!
# Vacuity of the `(9, 7, 37)` tight profile for `n = 18`

In the `e(M) = 1` two-hub dichotomy the tight profiles are `(9, 7, 37)` and `(10, 6, 40)`.  The
reliability investigation verified that the `(9, 7, 37)` profile hosts **no** no-two-hub graph: a
nine-hub configuration with one degree-`5` hub cannot host the rigid `6 + 4` rich/poor partition
that the no-good-two-hub hypothesis would force.  This file records that vacuity as
`nine_seven_vacuous_eighteen`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The rich-absorber residual core for `(9, 7, 37)` (documented `sorry`).**  This is the headline
theorem specialised to the *only* surviving regime: by `deg5_iso_ge_three_nine_seven` the lone
degree-`5` hub `d` is forced to absorb iso-degree `≥ 3` (hypothesis `hd5`), so the "degree-`5` hub is
poor" branch is already vacuous and we are left with the rich-absorber casework.

Mathematical route (verified vacuous; the residual sub-development is the open kernel here, mirroring
the sibling `(10, 6, 40)` linchpin `rich_edge_ge_four_eighteen`):

Let `S` be the set of *rich* degree-`4` hubs (iso-degree `≥ 2`), `s := |S|`, `M := ∑_S isoDeg`.
* Every share-`0` pair of rich degree-`4` hubs is a good two-hub pair (`private = isoDeg ≥ 2` on each
  side, share `≤ 1` by `hshare`), so by `hno2hub` every share-`0` rich pair is a `G`-edge.
* The edges inside `S` number `≤ (4s − M)/2` (each rich hub keeps `4 − isoDeg ≤ 2` non-iso
  neighbours, and the degree-`5` absorber is non-adjacent to every hub when its iso-degree is `4`/`5`).
* The share-`≥ 1` rich pairs embed into `⋃_{t∈Iso} (N(t) ∩ S)`-pairs, bounded by `∑_t C(m_t, 2)`
  with `m_t := |N(t) ∩ S| ≤ 3`; twins met by the absorber have `m_t ≤ 2`, capping the count via the
  coverage bound `#{m_t = 3} ≤ 7 − isoDeg(d)`.
Combining `C(s, 2) ≤ (4s − M)/2 + ∑_t C(m_t, 2)` refutes the `s ∈ {7, 8}` distributions outright.
The boundary `s = 6, M = 14, isoDeg(d) = 5` gives only equality in the pure edge-count and is closed
by the good-`K₂,₃` exclusion (`hK23`, `Σ = 5 + 4 + 9 = 18 ≤ 19`) on the absorber together with a
degree-`4` hub sharing three twins, plus the good-`C₄` (`hC4`) exclusion on absorber/rich-hub pairs
sharing two twins.  Formalising this residual (a multi-lemma counting development) is left as a single
documented `sorry`, exactly as for the analogous `(10, 6, 40)` core. -/
theorem nine_seven_rich_absorber_false (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 9) (hIso : Iso.card = 7)
    (hdsum : ∑ w ∈ Hub, G.degree w = 37)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (_hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 10)
    (hd5 : 3 ≤ ∑ v ∈ Hub.filter (fun h => ¬ G.degree h = 4), (G.neighborFinset v ∩ Iso).card) :
    False := by
  classical
  -- The rich degree-`4` hubs.
  set S : Finset (Fin 18) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hSdef
  have hSsub : S ⊆ Hub := Finset.filter_subset _ _
  have hSmem : ∀ a, a ∈ S ↔ a ∈ Hub ∧ G.degree a = 4 ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hSdef, Finset.mem_filter]
  have hSdeg4 : ∀ a ∈ S, G.degree a = 4 := fun a ha => ((hSmem a).mp ha).2.1
  have hSrich : ∀ a ∈ S, 2 ≤ (G.neighborFinset a ∩ Iso).card := fun a ha => ((hSmem a).mp ha).2.2
  -- `S` is contained in the eight degree-`4` hubs, so `s ≤ 8`.
  have hSsub4 : S ⊆ Hub.filter (fun h => G.degree h = 4) := by
    intro a ha; rw [Finset.mem_filter]; exact ⟨hSsub ha, hSdeg4 a ha⟩
  have hdeg4card := deg4_card_nine_seven G Hub hdeg hdeg5 hHub hdsum
  have hs8 : S.card ≤ 8 := by rw [← hdeg4card]; exact Finset.card_le_card hSsub4
  -- Extract the lone degree-`5` hub `d`.
  set Rd : Finset (Fin 18) := Hub.filter (fun h => ¬ G.degree h = 4) with hRddef
  have hRdcard : Rd.card = 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := Hub) (fun h => G.degree h = 4)
    rw [hdeg4card, hHub] at h; rw [hRddef]; omega
  obtain ⟨d, hdeq⟩ := Finset.card_eq_one.mp hRdcard
  have hdRd : d ∈ Rd := by rw [hdeq]; exact Finset.mem_singleton_self _
  have hdHub : d ∈ Hub := (Finset.mem_filter.mp hdRd).1
  have hdne4 : ¬ G.degree d = 4 := (Finset.mem_filter.mp hdRd).2
  have hdS : d ∉ S := fun hd => hdne4 (hSdeg4 d hd)
  -- `isoDeg(d) ≥ 3`.
  have hisod3 : 3 ≤ (G.neighborFinset d ∩ Iso).card := by
    have : ∑ v ∈ Rd, (G.neighborFinset v ∩ Iso).card = (G.neighborFinset d ∩ Iso).card := by
      rw [hdeq, Finset.sum_singleton]
    rw [hRddef] at this; rw [this] at hd5; exact hd5
  -- Abbreviations for the counting.
  set M : ℕ := ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card with hMdef
  set n3 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ S).card = 3)).card with hn3def
  -- Each twin meets at most three rich hubs.
  have hmt3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ S).card ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsub)
      _ = 3 := hiso3 t ht
  -- `∑_t m_t = M` (bipartite double count).
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card = M := by
    rw [hMdef]; exact cross_count G Iso S
  -- `Q ≤ M + 3·n3`.
  set Q : ℕ := ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
      - (G.neighborFinset t ∩ S).card) with hQdef
  have hQle : Q ≤ M + 3 * n3 := by
    have hpt : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card
        ≤ (G.neighborFinset t ∩ S).card
          + 3 * (if (G.neighborFinset t ∩ S).card = 3 then 1 else 0) := by
      intro t ht
      have hc3 := hmt3 t ht
      set c := (G.neighborFinset t ∩ S).card with hcv
      interval_cases c <;> simp
    calc Q ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card
              + 3 * (if (G.neighborFinset t ∩ S).card = 3 then 1 else 0)) :=
          Finset.sum_le_sum hpt
      _ = (∑ t ∈ Iso, (G.neighborFinset t ∩ S).card)
            + 3 * ∑ t ∈ Iso, (if (G.neighborFinset t ∩ S).card = 3 then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = M + 3 * n3 := by rw [hcross, hn3def, Finset.card_filter]
  -- Leaf 1: the trace/edge-count inequality.
  have hedge := ninesev_edge_share_le G Hub Iso S hSsub hSdeg4 hSrich hdisj hshare hno2hub
  rw [← hMdef, ← hQdef] at hedge
  -- Leaf 2: the coverage bound.
  have hcov := ninesev_d_coverage G Hub Iso S hSsub hiso3 d hdHub hdS
  rw [← hn3def, hIso] at hcov
  -- The `s ∈ {7, 8}` distributions are refuted; hence `s ≤ 6`.
  have hsle6 : S.card ≤ 6 := by
    by_contra hgt
    push Not at hgt
    interval_cases h : S.card <;> omega
  -- The lone non-degree-`4` hub has degree `5`.
  have hdeg_d5 : G.degree d = 5 := by
    have h4 := hdeg d hdHub; have h5 := hdeg5 d hdHub; omega
  -- Twins are pairwise non-adjacent (each twin's neighbourhood lies in `Hub`).
  have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
    intro t ht
    have hc3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
    have hd3 : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, hisodeg3 t ht]
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hd3, hc3])
    rw [← heq]; exact Finset.inter_subset_right
  have htwnn : ∀ t₁ ∈ Iso, ∀ t₂ ∈ Iso, ¬G.Adj t₁ t₂ := by
    intro t₁ ht₁ t₂ ht₂ hadj
    have : t₂ ∈ Hub := htwinHub t₁ ht₁ ((G.mem_neighborFinset t₁ t₂).mpr hadj)
    exact Finset.disjoint_left.mp hdisj this ht₂
  -- **Good-`K₂,₃` kill on the absorber.**  A degree-`4` hub `h` non-adjacent to `d` and sharing
  -- three `M`-isolated twins with `d` yields a forbidden good-`K₂,₃` (`Σ = 5 + 4 + 9 = 18 ≤ 19`).
  have hKkill : ∀ h ∈ Hub, G.degree h = 4 → ¬G.Adj d h →
      3 ≤ (G.neighborFinset d ∩ G.neighborFinset h ∩ Iso).card → False := by
    intro h hhHub hh4 hdh hsh3
    set W : Finset (Fin 18) := G.neighborFinset d ∩ G.neighborFinset h ∩ Iso with hWdef
    have hWunpack : ∀ x ∈ W, G.Adj d x ∧ G.Adj h x ∧ x ∈ Iso := by
      intro x hx
      rw [hWdef, Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset,
        G.mem_neighborFinset] at hx
      exact ⟨hx.1.1, hx.1.2, hx.2⟩
    obtain ⟨c, hcW⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
    obtain ⟨e, heW1⟩ := Finset.card_pos.mp
      (by rw [Finset.card_erase_of_mem hcW]; omega : 0 < (W.erase c).card)
    obtain ⟨f, hfW2⟩ := Finset.card_pos.mp
      (by rw [Finset.card_erase_of_mem heW1, Finset.card_erase_of_mem hcW]; omega :
        0 < ((W.erase c).erase e).card)
    have hcne : c ≠ e := (Finset.ne_of_mem_erase heW1).symm
    have hef : e ≠ f := (Finset.ne_of_mem_erase hfW2).symm
    have hcf : c ≠ f := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hfW2)).symm
    have heWmem : e ∈ W := Finset.mem_of_mem_erase heW1
    have hfWmem : f ∈ W := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hfW2)
    obtain ⟨hdc, hhc, hcIso⟩ := hWunpack c hcW
    obtain ⟨hde, hhe, heIso⟩ := hWunpack e heWmem
    obtain ⟨hdf, hhf, hfIso⟩ := hWunpack f hfWmem
    -- Pairwise distinctness of the five vertices.
    have hdh' : d ≠ h := by intro he; rw [he, hh4] at hdeg_d5; omega
    have hdc' : d ≠ c := fun he => Finset.disjoint_left.mp hdisj (he ▸ hdHub) hcIso
    have hde' : d ≠ e := fun he => Finset.disjoint_left.mp hdisj (he ▸ hdHub) heIso
    have hdf' : d ≠ f := fun he => Finset.disjoint_left.mp hdisj (he ▸ hdHub) hfIso
    have hhc' : h ≠ c := fun he => Finset.disjoint_left.mp hdisj (he ▸ hhHub) hcIso
    have hhe' : h ≠ e := fun he => Finset.disjoint_left.mp hdisj (he ▸ hhHub) heIso
    have hhf' : h ≠ f := fun he => Finset.disjoint_left.mp hdisj (he ▸ hhHub) hfIso
    have hcard5 : ({d, h, c, e, f} : Finset (Fin 18)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hdh', hdc', hde', hdf']),
        Finset.card_insert_of_notMem (by simp [hhc', hhe', hhf']),
        Finset.card_insert_of_notMem (by simp [hcne, hcf]),
        Finset.card_insert_of_notMem (by simp [hef]), Finset.card_singleton]
    apply hK23
    refine ⟨d, h, c, e, f, hcard5, hdc, hde, hdf, hhc, hhe, hhf, hdh,
      htwnn c hcIso e heIso, htwnn c hcIso f hfIso, htwnn e heIso f hfIso, ?_⟩
    have hsum : G.degree d + G.degree h + G.degree c + G.degree e + G.degree f = 18 := by
      rw [hdeg_d5, hh4, hisodeg3 c hcIso, hisodeg3 e heIso, hisodeg3 f hfIso]
    omega
  -- **Residual pinning to a single configuration.**  The two rich-mass leaves collapse the
  -- surviving regime to `isoDeg(d) = 5`, `s = 6`, `M = 14`.
  have hMub : M ≤ 2 * S.card + 2 :=
    ninesev_rich_mass_le G Hub Iso S hSsub hSdeg4 hSrich hdisj hshare hno2hub
  have hother : ∀ a ∈ Hub, a ≠ d → G.degree a = 4 := by
    intro a haHub hane
    by_contra h4
    have haRd : a ∈ Rd := Finset.mem_filter.mpr ⟨haHub, h4⟩
    rw [hdeq, Finset.mem_singleton] at haRd
    exact hane haRd
  have hMlb : 13 + S.card ≤ M + (G.neighborFinset d ∩ Iso).card :=
    ninesev_mass_lower G Hub Iso S hSsub hiso3 hHub hIso hSmem d hdHub hdS hother
  have hile5 : (G.neighborFinset d ∩ Iso).card ≤ 5 := by
    calc (G.neighborFinset d ∩ Iso).card ≤ (G.neighborFinset d).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree d := G.card_neighborFinset_eq_degree d
      _ = 5 := hdeg_d5
  -- `isoDeg(d) = 5`, `s = 6`, `M = 14` (the only boundary surviving the mass squeeze).
  have hpin : (G.neighborFinset d ∩ Iso).card = 5 ∧ S.card = 6 ∧ M = 14 := by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  obtain ⟨hi5, hs6, hM14⟩ := hpin
  -- **The rigid share-`3` kernel (documented `sorry`).**  The mass squeeze (`hMub`/`hMlb`) pins the
  -- regime to `isoDeg(d) = 5`, `s = 6`, `M = 14` (the unique boundary).  Here the degree-`5` hub `d`
  -- meets all five of its `M`-isolated twins `T_d`; the off-diagonal trace at equality forces
  -- `n₃ = 2`, every rich hub non-adjacent to `d` (all `10` rich hub-incidences fall inside `S`),
  -- the two poor degree-`4` hubs at iso-degree `1`, the two non-`d` twins each meeting three rich
  -- hubs, and four interior `T_d`-pairs realised as non-adjacent rich pairs.  In configs where these
  -- four pairs form a star a share-`3` hub exists outright (`hKkill` closes via good-`K₂,₃`).  The
  -- residual "path/two-triangle" arrangements carry NO share-`3` hub, but are *not* counterexamples:
  -- there the rich hubs being non-adjacent to `d` and to the poor hubs forces each poor hub onto the
  -- two `M`-edge endpoints `Z`, yielding a good triangle `{poor, Z, Z}` (`Σ = 4 + 3 + 3 = 10`)
  -- excluded by `hT`.  So `hexists` holds vacuously in those configs, but proving it needs the
  -- `hT`-route, an `hexists`-vs-`hT` case split on the four-pair arrangement.  This finite
  -- covering-design extraction is the genuine open kernel, left as a single documented `sorry`.
  -- `d` is non-adjacent to every hub (its neighbourhood is the five `M`-isolated twins).
  have hdIso := ninesev_rich_isolated_from_d G Iso d hdeg_d5 hi5
  have hdnadj : ∀ h ∈ Hub, ¬G.Adj d h := by
    intro h hhHub hadj
    exact Finset.disjoint_left.mp hdisj hhHub (hdIso ((G.mem_neighborFinset d h).mpr hadj))
  have hexists : ∃ h ∈ Hub, G.degree h = 4 ∧ ¬G.Adj d h ∧
      3 ≤ (G.neighborFinset d ∩ G.neighborFinset h ∩ Iso).card := by
    by_cases hsh3 : ∃ h ∈ Hub, G.degree h = 4 ∧
        3 ≤ (G.neighborFinset d ∩ G.neighborFinset h ∩ Iso).card
    · -- **Share-`3` branch.**  A degree-`4` hub sharing three of `d`'s twins is the witness.
      obtain ⟨h, hhHub, hh4, hsh⟩ := hsh3
      exact ⟨h, hhHub, hh4, hdnadj h hhHub, hsh⟩
    · -- **No-share-`3` branch.**  The pinned configuration carries a forbidden poor-hub triangle.
      exact absurd (ninesev_poor_hub_triangle_eighteen G Hub Iso S hSsub hSdeg4 hSrich hdisj hHub
        hIso hiso3 hdeg3 hisodeg3 hleak hshare hno2hub hT d hdHub hdS hother hdeg_d5 hi5 hs6 hM14)
        (fun h => h)
  obtain ⟨h, hhHub, hh4, hdh, hsh3⟩ := hexists
  exact hKkill h hhHub hh4 hdh hsh3

/-- **The `(9, 7, 37)` tight profile is vacuous under no-two-hub (`n = 18`).**  Nine hubs of degree
`4`/`5` (`∑deg = 37` forces exactly one degree-`5` hub), seven `M`-isolated twins each meeting three
hubs, no good two-hub pair, and the good-`C₄`/`K₂₃` exclusions are jointly contradictory: the
`21 = 3·7` rich incidences cannot be hosted on nine hubs without a good two-hub pair or a forbidden
sub-configuration.  The lone degree-`5` hub is forced to be *rich* (`deg5_iso_ge_three_nine_seven`),
so the proof reduces to the rich-absorber core `nine_seven_rich_absorber_false`.  Consumed by
`no_two_hub_rigid_eighteen` in the `(9, 7)` branch. -/
theorem nine_seven_vacuous_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 9) (hIso : Iso.card = 7)
    (hdsum : ∑ w ∈ Hub, G.degree w = 37)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
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
      G.degree x + G.degree y + G.degree z ≤ 10) :
    False :=
  nine_seven_rich_absorber_false G Hub Iso hdeg hdeg5 hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
    hleak hshare hno2hub hC4 hK23 hT
    (deg5_iso_ge_three_nine_seven G Hub Iso hdeg hdeg5 hiso3 hdisj hHub hIso hdsum hshare hno2hub)

end N18

end ACMax
