import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect

/-!
# Structural foundation for the `n = 20` star-triangle extraction

This file collects the genuinely-clean foundational counting facts used by the star-triangle
dichotomy for the tight `e(M) = 1`, all-degree-`4` profile `(|Hub|, |Iso|, ∑deg) = (12, 6, 48)`
(`Z.card = 2`), the `n = 20` analog of the rigid no-two-hub `n = 18` regime `(10, 6, 40)`.

At `n = 20` *all* `e(M) = 1` tight profiles route through star-triangle; the headline regime here is
the NEW `|Hub| = 12` all-degree-`4` profile.  The structural counting below is `n`-generic given the
regime hypotheses (`Hub.card = 12`, `Iso.card = 6`, `∑_{Hub} deg = 48`); only the regime constants
are threaded.  Note `|Iso| = 6` is *unchanged* from `n = 18`, so the iso-incidence total `3·6 = 18`
and the off-diagonal trace bound `6·6 = 36` carry over verbatim.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **N1 — two non-adjacent rich hubs share exactly one twin.**  The share `≤ 1` bound (`hshare`)
gives `≤ 1`; for the reverse, if two non-adjacent degree-`4` hubs `a, b`, each iso-rich
(`2 ≤ |N(·)∩Iso|`), shared *no* twin, then each would retain `≥ 2` private `M`-isolated twins, a
good two-hub pair contradicting `hno2hub`.  Hence the shared-twin count is exactly `1`. -/
theorem rich_nonadj_share_eq_one_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (a b : Fin 20) (haHub : a ∈ Hub) (hbHub : b ∈ Hub)
    (hda : G.degree a = 4) (hdb : G.degree b = 4) (hab : a ≠ b) (hnadj : ¬G.Adj a b)
    (hae : 2 ≤ (G.neighborFinset a ∩ Iso).card) (hbe : 2 ≤ (G.neighborFinset b ∩ Iso).card) :
    (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card = 1 := by
  classical
  have hle := hshare a haHub hda b hbHub hdb hab hnadj
  have hkeya := Finset.card_sdiff_add_card_inter (G.neighborFinset a ∩ Iso) (G.neighborFinset b)
  have hintera : (G.neighborFinset a ∩ Iso) ∩ G.neighborFinset b
      = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := Finset.inter_right_comm _ _ _
  rw [hintera] at hkeya
  have hkeyb := Finset.card_sdiff_add_card_inter (G.neighborFinset b ∩ Iso) (G.neighborFinset a)
  have hinterb : (G.neighborFinset b ∩ Iso) ∩ G.neighborFinset a
      = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
    rw [Finset.inter_right_comm, Finset.inter_comm (G.neighborFinset b) (G.neighborFinset a)]
  rw [hinterb] at hkeyb
  by_contra hne
  have hzero : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card = 0 := by omega
  exact hno2hub ⟨a, b, haHub, hbHub, hda, hdb, hab, hnadj, by omega, by omega⟩

/-- **N3 — the hubs span exactly `26` hub-hub incidences (`13` edges).**  Each hub's degree splits
over the partition `Hub ⊔ Iso ⊔ Z` (`Z = univ \ (Hub ∪ Iso)`, the two `M`-edge endpoints):
`∑deg = ∑|N∩Hub| + ∑|N∩Iso| + ∑|N∩Z|`.  Here `∑|N∩Iso| = 3·6 = 18`, and the two `Z`-vertices each
meet `≥ 2` hubs (degree `≥ 3`, at most one `Z`-neighbour, no twin neighbour) so `∑|N∩Z| = 4` exactly
(the leak bound caps it at `4`).  Hence `∑|N∩Hub| = 48 − 18 − 4 = 26`. -/
theorem hub_hub_edge_count_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4) :
    ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card = 26 := by
  classical
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- `Z` has exactly two elements.
  have hHIcard : (Hub ∪ Iso).card = 18 := by
    rw [Finset.card_union_of_disjoint hdisj, hHub, hIso]
  have hZeq : Z = (Hub ∪ Iso)ᶜ := by
    rw [hZdef]; ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
  have hZcard : Z.card = 2 := by
    rw [hZeq, Finset.card_compl, Fintype.card_fin, hHIcard]
  -- Per-vertex three-way split of the degree.
  have hpart : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
      + (G.neighborFinset v ∩ Z).card = G.degree v := by
    intro v
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
  -- Iso-incidence sum is `18`.
  have hisosum : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  -- A twin's neighbourhood lies entirely in `Hub`.
  have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
    intro t ht
    have hsub : G.neighborFinset t ∩ Hub ⊆ G.neighborFinset t := Finset.inter_subset_left
    have hcard3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
    have hdt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hdt])
    rw [← heq]; exact Finset.inter_subset_right
  -- Each `Z`-vertex meets `≥ 2` hubs.
  have hzhub : ∀ z ∈ Z, 2 ≤ (G.neighborFinset z ∩ Hub).card := by
    intro z hz
    have hzIso0 : (G.neighborFinset z ∩ Iso).card = 0 := by
      rw [Finset.card_eq_zero]
      ext x; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hxz hxi
      have : z ∈ G.neighborFinset x := by
        rw [G.mem_neighborFinset, SimpleGraph.adj_comm]; exact (G.mem_neighborFinset _ _).mp hxz
      have hzHub := htwinHub x hxi this
      have hznotHub : z ∉ Hub := by
        rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
      exact hznotHub hzHub
    have hzZle : (G.neighborFinset z ∩ Z).card ≤ 1 := by
      have hsub : G.neighborFinset z ∩ Z ⊆ Z.erase z := by
        intro x hx
        rw [Finset.mem_inter, G.mem_neighborFinset] at hx
        exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hz, hZcard] at this; omega
    have := hpart z
    have hd := hdeg3 z
    omega
  -- `Z`-incidence sum is exactly `4`.
  have hZsumge : 4 ≤ ∑ h ∈ Hub, (G.neighborFinset h ∩ Z).card := by
    rw [cross_count_twenty G Hub Z]
    calc 4 = ∑ _z ∈ Z, 2 := by rw [Finset.sum_const, hZcard, smul_eq_mul]
      _ ≤ ∑ z ∈ Z, (G.neighborFinset z ∩ Hub).card := Finset.sum_le_sum hzhub
  have hZsum : ∑ h ∈ Hub, (G.neighborFinset h ∩ Z).card = 4 := by omega
  -- Combine via the per-hub split.
  have hsumsplit : ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card
      + ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card + ∑ h ∈ Hub, (G.neighborFinset h ∩ Z).card
      = ∑ h ∈ Hub, G.degree h := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun h _ => hpart h)
  rw [hisosum, hZsum, hdsum] at hsumsplit
  omega

/-- **N2 — at most two degree-`4` hubs have iso-degree `≥ 3`.**  Two non-adjacent such hubs would
each retain `≥ 2` private twins (share `≤ 1`), a good two-hub pair; so the `a ≥ 3` degree-`4` hubs
form a clique and (`≤ 4 − 3 = 1` hub-neighbour each) number at most `2`.  This is the
`strong_deg4_count_le_two_deg5_twenty` bound specialised through `hno2hub`. -/
theorem rich_a3_count_le_two_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
  classical
  have key := nogood_of_not_select_twenty G Hub Iso hno2hub
  have hmf := strong_deg4_count_le_two_deg5_twenty G Hub Iso hdisj hshare key
  omega

end N20

end ACMax
