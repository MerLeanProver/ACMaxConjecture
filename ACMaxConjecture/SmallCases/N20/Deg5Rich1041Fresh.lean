import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5ZSlots
import ACMaxConjecture.SmallCases.N20.Deg5SameZ
import ACMaxConjecture.SmallCases.N20.Deg5RichCap
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Blocker
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Octa

/-! # The fresh-source saturation kill for the rich (11,7,45) shared-twin corner (`n = 20`) -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- The case-`(iii)` residual: the good `Z`-slot hub `h₂` has isoDeg `1` with its
single twin SHARED with `g`.  Either a fresh degree-`4` source `x` (isoDeg `≥ 2`, off
`h₂`, off `z`, share-`∅` with `h₂`) exists — the `hno2hub`-driven saturation kill — or
the `(11,7,45)` rich-count dichotomy lands in its anchor-saturated `|R| = 4` disjunct,
propagated verbatim for the caller-side `anchor_sat_kill_twenty`, or the rigid `|R| = 5`
tie fires the octahedron dispatcher (`rigid_tie_kill_1041_twenty`), whose live
isoDeg-`f = 4` deficit branch yields the standard 4-way cut-config disjunction. -/
theorem rich_source_share0_1041_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 11) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 20) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hz2 : G.Adj z h₂) (hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1) :
    (∃ x : Fin 20, x ∈ Hub ∧ G.degree x = 4 ∧ 2 ≤ (G.neighborFinset x ∩ Iso).card ∧
      ¬G.Adj x h₂ ∧ ¬G.Adj x z ∧ x ≠ h₂ ∧
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso = ∅) ∨
    ((Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 4 ∧
      (∃ f ∈ Hub, G.degree f = 5 ∧ (G.neighborFinset f ∩ Iso).card = 5) ∧
      (∀ h ∈ Hub, G.degree h = 4 →
        h ∉ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) →
        (G.neighborFinset h ∩ Iso).card = 1)) ∨
    (SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G) := by
  -- An unblocked rich hub is a survivor; otherwise the rich-count dichotomy either
  -- propagates its anchor-saturated `|R| = 4` payload or pins the rigid `|R| = 5` tie,
  -- where the octahedron kill fires.
  by_cases hex : ∃ x : Fin 20, x ∈ Hub ∧ G.degree x = 4 ∧
      2 ≤ (G.neighborFinset x ∩ Iso).card ∧
      ¬(G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
  · obtain ⟨x, hxHub, hxd, hxiso, hxnb⟩ := hex
    push Not at hxnb
    obtain ⟨hxsh, hxh₂, hxz⟩ := hxnb
    have hxne : x ≠ h₂ := by
      rintro rfl; rw [hpoor] at hxiso; omega
    exact Or.inl ⟨x, hxHub, hxd, hxiso, hxh₂, hxz, hxne, hxsh⟩
  · have hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
        2 ≤ (G.neighborFinset x ∩ Iso).card →
        G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z := by
      intro x hxHub hxd hxiso
      by_contra hb
      push Not at hb
      exact hex ⟨x, hxHub, hxd, hxiso, by push Not; exact hb⟩
    rcases rich_count_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg
        hdeg5 hHub hIso hdsum hshare hno2hub g hg hgd hgiso with hR5 | hpayload
    · have hRle := rich_le_five_blocked_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3
        hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso
        h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock
      have hR5eq : (Hub.filter (fun h => G.degree h = 4 ∧
          2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 := by omega
      exact Or.inr (Or.inr (rigid_tie_kill_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3
        hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso
        h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock hR5eq))
    · exact Or.inr (Or.inl hpayload)

end N20

end ACMax
