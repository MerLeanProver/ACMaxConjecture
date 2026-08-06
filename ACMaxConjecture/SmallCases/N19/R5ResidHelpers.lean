import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates

/-!
# Reusable cross-edge `C₄` helpers for the `r = 5` octahedron residual (`n = 19`)

The single combinatorial engine these lemmas package is the **`M`-partner good-`C₄`**: in the rigid
`e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (11, 6)` profile the two `M`-edge endpoints
`Z = univ \ (Hub ∪ Iso)` are `z, z'` with `z ∼ z'`, each of degree `3` meeting exactly two hubs and
no twin (`z_two_hub_nbrs_nineteen`), and no hub meets both (`no_hub_adj_both_mends_nineteen`).

If a hub-neighbour `g` of `z` is adjacent to a hub-neighbour `g'` of `z'`, the `4`-cycle
`z – g – g' – z'` is a *good* `C₄` of degree sum `3 + 4 + 4 + 3 = 14`, with both diagonals
(`z ∼ g'`, `g ∼ z'`) forced non-adjacent (each such adjacency would make a hub meet *both* `M`-edge
endpoints).  This contradicts `hC4`.  The contrapositive is the structural fact that drives the
`{2,2,2,3,3}` residual: **no hub-neighbour of `z` is adjacent to any hub-neighbour of `z'`** — the
four `Z`-hubs form an independent set.

These facts are derived purely from the regime hypotheses available to `r5_resid_nineteen`; they do
**not** use `hztwopoor`, so they are non-circular at the `ZMeetsTwoPoorResidual` call site.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **The `M`-partner of `z` is adjacent to it.**  With `Z = univ \ (Hub ∪ Iso)` of cardinality `2`,
`z, z' ∈ Z` distinct, and `z` meeting exactly two hubs and no twin (`z_two_hub_nbrs_nineteen`), the
three-way split leaves `z` exactly one `Z`-neighbour, which—`|Z| = 2`—must be `z'`. -/
theorem mends_adj_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (z : Fin 19) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (z' : Fin 19) (hz' : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hzz' : z ≠ z') :
    G.Adj z z' := by
  classical
  set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZcard : Z.card = 2 := z_card_two_nineteen Hub Iso hdisj hHub hIso
  have hZpair : Z = {z, z'} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hz
      · rw [Finset.mem_singleton] at hx; subst hx; exact hz'
    · rw [hZcard, Finset.card_insert_of_notMem (by simp [hzz']), Finset.card_singleton]
  obtain ⟨_, _, _⟩ :=
    z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hz
  have hzZ1 : (G.neighborFinset z ∩ Z).card = 1 := by
    have hsp := nbr_split_three_nineteen G Hub Iso hdisj z
    rw [← hZdef] at hsp
    obtain ⟨h0, h2, hd⟩ :=
      z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hz
    omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hzZ1
  have humem : u ∈ G.neighborFinset z ∩ Z := by rw [hu]; exact Finset.mem_singleton_self _
  have huZ : u ∈ Z := (Finset.mem_inter.mp humem).2
  have huN : u ∈ G.neighborFinset z := (Finset.mem_inter.mp humem).1
  have huz : u ≠ z := fun he => G.irrefl (by rw [he] at huN; exact (G.mem_neighborFinset z z).mp huN)
  rw [hZpair, Finset.mem_insert, Finset.mem_singleton] at huZ
  rcases huZ with rfl | rfl
  · exact absurd rfl huz
  · exact (G.mem_neighborFinset z u).mp huN

/-- **The `M`-partner good-`C₄` (axiom-clean, no `hztwopoor`).**  If a hub-neighbour `g` of an
`M`-edge endpoint `z` is adjacent to a hub-neighbour `g'` of its `M`-partner `z'`, the `4`-cycle
`z – g – g' – z'` is a good `C₄` of degree sum `3 + 4 + 4 + 3 = 14`, contradicting `hC4`.  Both
diagonals are forced non-adjacent: `z ∼ g'` would make hub `g'` meet both `z, z'`, and `g ∼ z'`
would make hub `g` meet both — each excluded by `no_hub_adj_both_mends_nineteen`. -/
theorem cross_z_hub_c4_false_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (z : Fin 19) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (z' : Fin 19) (hz' : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hzz' : z ≠ z')
    (g g' : Fin 19) (hg : g ∈ Hub) (hg' : g' ∈ Hub)
    (hzg : G.Adj z g) (hz'g' : G.Adj z' g') (hcross : G.Adj g g') :
    False := by
  classical
  -- Degrees of the four vertices.
  obtain ⟨_, _, hzdeg⟩ :=
    z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hz
  obtain ⟨_, _, hz'deg⟩ :=
    z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z' hz'
  have hgdeg : G.degree g = 4 := hdeg4 g hg
  have hg'deg : G.degree g' = 4 := hdeg4 g' hg'
  -- `z, z'` are not hubs; `g, g'` are hubs.
  have hznotHub : z ∉ Hub := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
  have hz'notHub : z' ∉ Hub := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz'; exact hz'.2.1
  -- `g ≠ g'` from the cross adjacency.
  have hgg' : g ≠ g' := G.ne_of_adj hcross
  -- The `M`-edge `z ∼ z'`.
  have hzz'adj : G.Adj z z' :=
    mends_adj_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hz z' hz' hzz'
  -- Diagonal non-adjacencies via `no_hub_adj_both_mends_nineteen`.
  have hnzg' : ¬G.Adj z g' := by
    intro hadj
    exact no_hub_adj_both_mends_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
      hleak hT g' hg' z hz z' hz' hzz' ⟨hadj.symm, hz'g'.symm⟩
  have hngz' : ¬G.Adj g z' := by
    intro hadj
    exact no_hub_adj_both_mends_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
      hleak hT g hg z hz z' hz' hzz' ⟨hzg.symm, hadj⟩
  -- The four vertices are distinct.
  have hcard4 : ({z, g, g', z'} : Finset (Fin 19)).card = 4 := by
    rw [Finset.card_eq_four]
    refine ⟨z, g, g', z', ?_, ?_, hzz', hgg', ?_, ?_, rfl⟩
    · exact fun he => hznotHub (he ▸ hg)
    · exact fun he => hznotHub (he ▸ hg')
    · exact fun he => hz'notHub (he ▸ hg)
    · exact fun he => hz'notHub (he ▸ hg')
  -- Assemble the good `C₄`  `z – g – g' – z'`.
  refine hC4 ⟨z, g, g', z', hcard4, hzg, hcross, hz'g'.symm, hzz'adj.symm, hnzg', hngz', ?_⟩
  rw [hzdeg, hgdeg, hg'deg, hz'deg]

/-- **Two private twins (axiom-clean, reusable).**  A degree-`4` hub `h₁` with `≥ 3` twins, sitting
non-adjacent to another degree-`4` hub `X`, retains `≥ 2` twins not adjacent to `X` (the two share at
most one twin by `hshare`). -/
theorem exists_two_private_twins_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (h₁ X : Fin 19) (hh₁Hub : h₁ ∈ Hub) (hXHub : X ∈ Hub)
    (hdh₁ : G.degree h₁ = 4) (hdX : G.degree X = 4) (hne : h₁ ≠ X) (hnadj : ¬G.Adj h₁ X)
    (htw : 3 ≤ (G.neighborFinset h₁ ∩ Iso).card) :
    ∃ a b : Fin 19, a ∈ Iso ∧ b ∈ Iso ∧ a ≠ b ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ ¬G.Adj a X ∧ ¬G.Adj b X := by
  classical
  have hshare1 : (G.neighborFinset h₁ ∩ G.neighborFinset X ∩ Iso).card ≤ 1 :=
    hshare h₁ hh₁Hub hdh₁ X hXHub hdX hne hnadj
  have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset X)
  have hinter : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset X
      = G.neighborFinset h₁ ∩ G.neighborFinset X ∩ Iso := Finset.inter_right_comm _ _ _
  rw [hinter] at hkey
  have hTge : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset X).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset X).card)
  have hprop : ∀ w ∈ (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset X,
      w ∈ Iso ∧ G.Adj w h₁ ∧ ¬G.Adj w X := by
    intro w hw
    rw [Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hw
    exact ⟨hw.1.2, hw.1.1.symm, fun he => hw.2 he.symm⟩
  obtain ⟨haIso, ha1, haX⟩ := hprop a ha
  obtain ⟨hbIso, hb1, hbX⟩ := hprop b hb
  exact ⟨a, b, haIso, hbIso, hab, ha1, hb1, haX, hbX⟩

/-- **One private twin (axiom-clean, reusable).**  A degree-`4` hub `h₂` with `≥ 2` twins, sitting
non-adjacent to another degree-`4` hub `X`, retains `≥ 1` twin not adjacent to `X`. -/
theorem exists_one_private_twin_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (h₂ X : Fin 19) (hh₂Hub : h₂ ∈ Hub) (hXHub : X ∈ Hub)
    (hdh₂ : G.degree h₂ = 4) (hdX : G.degree X = 4) (hne : X ≠ h₂) (hnadj : ¬G.Adj X h₂)
    (htw : 2 ≤ (G.neighborFinset h₂ ∩ Iso).card) :
    ∃ c : Fin 19, c ∈ Iso ∧ G.Adj c h₂ ∧ ¬G.Adj X c := by
  classical
  have hshare1 : (G.neighborFinset X ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 :=
    hshare X hXHub hdX h₂ hh₂Hub hdh₂ hne hnadj
  have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso) (G.neighborFinset X)
  have hinter : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset X
      = G.neighborFinset X ∩ G.neighborFinset h₂ ∩ Iso := by
    rw [Finset.inter_right_comm, Finset.inter_comm (G.neighborFinset h₂) (G.neighborFinset X)]
  rw [hinter] at hkey
  have hTge : 1 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset X).card := by omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset X).card)
  rw [Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hc
  exact ⟨c, hc.1.2, hc.1.1.symm, hc.2⟩

/-- **The `Z`-leaf two-hub assembler (axiom-clean, reusable).**  Packs a `TwoHubConfig` whose fourth
leaf `d = z` is an `M`-edge endpoint (a `Z`-vertex, invisible to the `Iso`-only `hno2hub`).  The
caller supplies only the *load-bearing* data: two non-adjacent degree-`4` hubs `h₁, h₂`; two distinct
twins `a, b ∈ Iso` of `h₁`, each non-adjacent to `h₂`; a twin `c ∈ Iso` of `h₂` non-adjacent to
`h₁`; and the `M`-end `z ∈ Z` met by `h₂` with `h₁ ≁ z`.  Every remaining `TwoHubConfig`
non-adjacency holds *for free*: `a, b, c ∈ Iso` are pairwise non-adjacent (twins meet only hubs), and
`z ∈ Z` meets no twin, so `a, b ≁ c` and `a, b ≁ z`.  All distinctness is forced by the
`Hub`/`Iso`/`Z` partition together with the supplied adjacencies. -/
theorem two_hub_zleaf_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (h₁ h₂ a b c z : Fin 19)
    (hh₁Hub : h₁ ∈ Hub) (hh₂Hub : h₂ ∈ Hub)
    (hdh₁ : G.degree h₁ = 4) (hdh₂ : G.degree h₂ = 4)
    (haIso : a ∈ Iso) (hbIso : b ∈ Iso) (hcIso : c ∈ Iso)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (ha1 : G.Adj a h₁) (hb1 : G.Adj b h₁) (hc2 : G.Adj c h₂) (hz2 : G.Adj z h₂)
    (hn12 : ¬G.Adj h₁ h₂) (hn1c : ¬G.Adj h₁ c) (hn1z : ¬G.Adj h₁ z)
    (hna2 : ¬G.Adj a h₂) (hnb2 : ¬G.Adj b h₂) (hab : a ≠ b) :
    TwoHubConfig G := by
  classical
  -- `z`-vertex structural facts: degree `3`, meets no twin.
  obtain ⟨hziso0, _, hzdeg3⟩ :=
    z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hzZ
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
  -- Membership-based facts.
  have hznotHub : z ∉ Hub := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hzZ; exact hzZ.2.1
  have hznotIso : z ∉ Iso := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hzZ; exact hzZ.2.2
  -- A twin is not a hub.
  have htwin_notHub : ∀ t ∈ Iso, t ∉ Hub := fun t ht he => Finset.disjoint_left.mp hdisj he ht
  -- Degrees of the three twins.
  have hda : G.degree a = 3 := hisodeg3 a haIso
  have hdb : G.degree b = 3 := hisodeg3 b hbIso
  have hdc : G.degree c = 3 := hisodeg3 c hcIso
  -- Free non-adjacencies.
  have hnac : ¬G.Adj a c := htwin_nonadj a haIso c hcIso
  have hnbc : ¬G.Adj b c := htwin_nonadj b hbIso c hcIso
  have hnaz : ¬G.Adj a z := fun he => hz_notwin a haIso he.symm
  have hnbz : ¬G.Adj b z := fun he => hz_notwin b hbIso he.symm
  -- Distinctness.
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
  -- Assemble the `TwoHubConfig` with `d = z`.
  exact ⟨h₁, h₂, a, b, c, z, hdh₁, hdh₂, hda, hdb, hdc, hzdeg3,
    ha1, hb1, hc2, hz2, hn12, hn1c, hn1z, hna2, hnac, hnaz, hnb2, hnbc, hnbz,
    ne_h₁h₂, ne_h₁a, ne_h₁b, ne_h₁c, ne_h₁z, ne_h₂a, ne_h₂b, ne_h₂c, ne_h₂z,
    hab, ne_ac, ne_az, ne_bc, ne_bz, ne_cz⟩

end N19

end ACMax
