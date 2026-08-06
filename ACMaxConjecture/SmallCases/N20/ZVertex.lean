import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct

/-!
# Basic `Z`-vertex structure lemmas for the `n = 20` no-two-hub partition (bottom layer)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (12, 6)` profile the two `M`-edge
endpoints form `Z = univ \ (Hub ∪ Iso)` (`|Z| = 2`).  These foundational counting lemmas — the
per-vertex three-way degree split, the four hub-incidences carried by `Z`, `|Z| = 2`, the exact
`(2, 0, deg 3)` `Z`-vertex profile, and the no-hub-meets-both-endpoints triangle fix — are used
throughout the rigid analysis (the rich-count chain, the `Z`-poor extraction, and the `r = 6/7`
saturation cluster).

This is the **mechanical port** of the `n = 19` `TwinCert19ZVertex` to `|Hub| = 12`.  Since
`|Iso| = 6` is **unchanged** the leak total is the same: with `∑deg = 48`, the hub-hub edge mass
is `26` (vs `22` at `n = 19`) and the iso-incidence mass is still `18`, so the `Z`-hub mass is
`48 − 26 − 18 = 4` — identical to `n = 19`.  Hence the entire `(2, 0, deg 3)` `Z`-profile carries
over verbatim.  The only changes are `Fin 19 → 20`, `Hub.card 11 → 12`, `∑deg 44 → 48`, and the
hub-hub mass `22 → 26`; the good-triangle threshold stays `≤ 11` (the `{u,v,h}` triangle
sums to `3 + 3 + 4 = 10 ≤ 11`, still excluded).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Per-vertex three-way degree split.**  With `Hub` and `Iso` disjoint and `Z = univ \
(Hub ∪ Iso)`, any vertex `v` has `|N(v) ∩ Hub| + |N(v) ∩ Iso| + |N(v) ∩ Z| = deg v`, since
`Hub ⊔ Iso ⊔ Z` partitions the vertex set. -/
theorem nbr_split_three_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdisj : Disjoint Hub Iso) (v : Fin 20) :
    (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
      + (G.neighborFinset v ∩ (Finset.univ \ (Hub ∪ Iso))).card = G.degree v := by
  classical
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZeq : Z = (Hub ∪ Iso)ᶜ := by
    rw [hZdef]; ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
  have h1 : (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v \ Hub).card
      = (G.neighborFinset v).card := Finset.card_inter_add_card_sdiff _ _
  have h2 : ((G.neighborFinset v \ Hub) ∩ Iso).card + ((G.neighborFinset v \ Hub) \ Iso).card
      = (G.neighborFinset v \ Hub).card := Finset.card_inter_add_card_sdiff _ _
  have he1 : (G.neighborFinset v \ Hub) ∩ Iso = G.neighborFinset v ∩ Iso := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hx, _⟩, hxi⟩; exact ⟨hx, hxi⟩
    · rintro ⟨hx, hxi⟩
      exact ⟨⟨hx, fun hxh => Finset.disjoint_left.mp hdisj hxh hxi⟩, hxi⟩
  have he2 : (G.neighborFinset v \ Hub) \ Iso = G.neighborFinset v ∩ Z := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, hZeq, Finset.mem_compl,
      Finset.mem_union, not_or]
    tauto
  rw [he1, he2] at h2
  rw [G.card_neighborFinset_eq_degree] at h1
  omega

/-- **The two `M`-edge endpoints carry exactly four hub-incidences.**  With `Hub ⊔ Iso ⊔ Z` a
partition of the `20` vertices, every hub degree splits three ways; summing and substituting the
`N3` hub-hub count (`26`) and the iso-incidence count (`18`) against `∑deg = 48` leaves
`∑_{h∈Hub}|N(h) ∩ Z| = 4` — the same as `n = 19` (`48 − 26 − 18 = 4`). -/
theorem zdeg_sum_four_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4) :
    ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card = 4 := by
  classical
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hpart : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
      + (G.neighborFinset v ∩ Z).card = G.degree v := fun v =>
    nbr_split_three_twenty G Hub Iso hdisj v
  have hisosum : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  have hhubsum : ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card = 26 :=
    hub_hub_edge_count_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  have hsumsplit : ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card
      + ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card + ∑ h ∈ Hub, (G.neighborFinset h ∩ Z).card
      = ∑ h ∈ Hub, G.degree h := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun h _ => hpart h)
  rw [hhubsum, hisosum, hdsum] at hsumsplit
  omega

/-- **`|Z| = 2` — there are exactly two `M`-edge endpoints.**  `Z = univ \ (Hub ∪ Iso)` with
`Hub`, `Iso` disjoint of cardinalities `12`, `6`, so `|Z| = 20 − 18 = 2`. -/
theorem z_card_two_twenty (Hub Iso : Finset (Fin 20))
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6) :
    (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)).card = 2 := by
  have hHIcard : (Hub ∪ Iso).card = 18 := by
    rw [Finset.card_union_of_disjoint hdisj, hHub, hIso]
  have hZeq : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) = (Hub ∪ Iso)ᶜ := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
  rw [hZeq, Finset.card_compl, Fintype.card_fin, hHIcard]

/-- **Each `M`-edge endpoint meets exactly two hubs and no twin (`deg z = 3`).**  With the rigid
`(12, 6, 48)` profile, the two `M`-edge endpoints `Z = univ \ (Hub ∪ Iso)` carry exactly four
hub-incidences (`zdeg_sum_four`); cross-counting puts these on the two `Z`-vertices, and each
`Z`-vertex meets `≥ 2` hubs (a twin's neighbourhood lies in `Hub`, so `z` meets no twin; `z` has at
most one `Z`-neighbour and degree `≥ 3`).  Two vertices summing to `4`, each `≥ 2`, gives exactly `2`
each, whence `deg z = 2 + 0 + 1 = 3`. -/
theorem z_two_hub_nbrs_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4) :
    ∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)),
      (G.neighborFinset z ∩ Iso).card = 0 ∧ (G.neighborFinset z ∩ Hub).card = 2 ∧
        G.degree z = 3 := by
  classical
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZeq : Z = (Hub ∪ Iso)ᶜ := by
    rw [hZdef]; ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
  have hZcard : Z.card = 2 := z_card_two_twenty Hub Iso hdisj hHub hIso
  -- The two `M`-edge endpoints carry exactly four hub-incidences (cross-counted onto `Z`).
  have hsum4 : ∑ z ∈ Z, (G.neighborFinset z ∩ Hub).card = 4 := by
    rw [← cross_count_twenty G Hub Z]
    exact zdeg_sum_four_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  -- A twin's neighbourhood lies entirely in `Hub`.
  have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
    intro t ht
    have hcard3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
    have hdt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard3, hdt])
    rw [← heq]; exact Finset.inter_subset_right
  -- Per `Z`-vertex facts: meets no twin, at most one `Z`-neighbour, hence `≥ 2` hubs.
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
  have hzZle : ∀ z ∈ Z, (G.neighborFinset z ∩ Z).card ≤ 1 := by
    intro z hz
    have hsub : G.neighborFinset z ∩ Z ⊆ Z.erase z := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hz, hZcard] at this; omega
  -- Per-vertex three-way degree split.
  have hpart : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
      + (G.neighborFinset v ∩ Z).card = G.degree v := fun v =>
    nbr_split_three_twenty G Hub Iso hdisj v
  have hzhub : ∀ z ∈ Z, 2 ≤ (G.neighborFinset z ∩ Hub).card := by
    intro z hz
    have h0 := hiso0 z hz
    have hZle := hzZle z hz
    have hsp := hpart z
    have hd := hdeg3 z
    omega
  intro z hz
  -- Each `Z`-vertex meets exactly `2` hubs: the sum is `4`, both summands `≥ 2`, `|Z| = 2`.
  have hhub2 : (G.neighborFinset z ∩ Hub).card = 2 := by
    have hge := hzhub z hz
    have hae := Finset.add_sum_erase Z (fun w => (G.neighborFinset w ∩ Hub).card) hz
    have heraseGe : 2 ≤ ∑ w ∈ Z.erase z, (G.neighborFinset w ∩ Hub).card := by
      have hcardE : (Z.erase z).card = 1 := by rw [Finset.card_erase_of_mem hz, hZcard]
      calc (2 : ℕ) = ∑ _w ∈ Z.erase z, 2 := by
            rw [Finset.sum_const, hcardE, smul_eq_mul, one_mul]
        _ ≤ ∑ w ∈ Z.erase z, (G.neighborFinset w ∩ Hub).card :=
            Finset.sum_le_sum (fun w hw => hzhub w (Finset.mem_of_mem_erase hw))
    rw [hsum4] at hae
    omega
  have h0 := hiso0 z hz
  have hZle := hzZle z hz
  have hsp := hpart z
  have hd := hdeg3 z
  refine ⟨h0, hhub2, ?_⟩
  omega

/-- **No hub meets both `M`-edge endpoints (the no-good-triangle fix).**  The two `M`-edge
endpoints `u, v ∈ Z = univ \ (Hub ∪ Iso)` each have degree `3`, meet no `M`-isolated twin and
exactly two hubs (`z_two_hub_nbrs`); their three-way split therefore leaves a single `Z`-incidence,
which—`|Z| = 2`—must be each other, so `u ~ v` is the `M`-edge.  Were a hub `h` adjacent to both,
the triangle `{u, v, h}` would have degree sum `3 + 3 + 4 = 10 ≤ 11`, a good triangle excluded by
`hT`.  Consequently the four `Z`–hub incidences land on four *distinct* hubs. -/
theorem no_hub_adj_both_mends_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (h : Fin 20) (hh : h ∈ Hub)
    (u : Fin 20) (hu : u ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (v : Fin 20) (hv : v ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (huv : u ≠ v) :
    ¬(G.Adj h u ∧ G.Adj h v) := by
  classical
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZcard : Z.card = 2 := z_card_two_twenty Hub Iso hdisj hHub hIso
  -- `Z = {u, v}`.
  have hZpair : Z = {u, v} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hu
      · rw [Finset.mem_singleton] at hx; subst hx; exact hv
    · rw [hZcard, Finset.card_insert_of_notMem (by simp [huv]), Finset.card_singleton]
  -- Each `Z`-vertex meets two hubs, no twin, and has degree `3`.
  obtain ⟨huiso, huhub, hudeg⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak u hu
  -- `u` meets exactly one `Z`-vertex.
  have huZ : (G.neighborFinset u ∩ Z).card = 1 := by
    have hsp := nbr_split_three_twenty G Hub Iso hdisj u
    rw [← hZdef] at hsp; omega
  -- That neighbour is `v`, so `u ~ v` (the `M`-edge).
  have hvinu : v ∈ G.neighborFinset u := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp huZ
    have hwmem : w ∈ G.neighborFinset u ∩ Z := by rw [hw]; exact Finset.mem_singleton_self _
    have hwZ : w ∈ Z := (Finset.mem_inter.mp hwmem).2
    have hwu : w ∈ G.neighborFinset u := (Finset.mem_inter.mp hwmem).1
    have hwneu : w ≠ u := fun he => G.irrefl
      (by rw [he] at hwu; exact (G.mem_neighborFinset u u).mp hwu)
    rw [hZpair, Finset.mem_insert, Finset.mem_singleton] at hwZ
    rcases hwZ with rfl | rfl
    · exact absurd rfl hwneu
    · exact hwu
  have huvadj : G.Adj u v := (G.mem_neighborFinset u v).mp hvinu
  -- `h` is a hub, so distinct from the two `Z`-vertices.
  have hu_notHub : u ∉ Hub := by
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hu; exact hu.2.1
  have hv_notHub : v ∉ Hub := by
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hv; exact hv.2.1
  have hhu : h ≠ u := fun he => hu_notHub (he ▸ hh)
  have hhv : h ≠ v := fun he => hv_notHub (he ▸ hh)
  obtain ⟨_, _, hvdeg⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak v hv
  -- The triangle `{u, v, h}` has degree sum `3 + 3 + 4 = 10 ≤ 11`, excluded by `hT`.
  rintro ⟨hhu_adj, hhv_adj⟩
  have hdsum10 : G.degree u + G.degree v + G.degree h ≤ 11 := by
    rw [hudeg, hvdeg, hdeg4 h hh]; omega
  exact hT ⟨u, v, h, huv, hhv.symm, hhu.symm, huvadj, hhv_adj.symm, hhu_adj.symm, hdsum10⟩

end N20

end ACMax
