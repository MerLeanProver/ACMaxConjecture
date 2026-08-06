import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Deg5ZHub1042
import ACMaxConjecture.SmallCases.N20.Deg5Pack
import ACMaxConjecture.SmallCases.N20.Deg5SameZ
import ACMaxConjecture.SmallCases.N20.Deg5Rich1042Blocker
import ACMaxConjecture.SmallCases.N20.Deg5Rich1042Count
import ACMaxConjecture.SmallCases.N20.Deg5Rich1042DoubleCount
import ACMaxConjecture.SmallCases.N20.Deg5Rich1042AnchorSat

/-! # The `(10, 8, 42)` rich-world `Z`-leaf extraction (`n = 20`, deg-5 corner)

The two-degree-`5`-anchor profile `(|Hub|, |Iso|, Σ_Hub deg) = (10, 8, 42)`.  Given a rich
degree-`4` hub `g` (`isoDeg g ≥ 3`), the good-`Z`-hub selector produces a degree-`4` slot hub
`h₂` on an `M`-end `z` avoided by `g`.  The `isoDeg h₂ ≥ 2` and share-`0` branches close through
the rich/share-`0` packers; the blocked share-`1` residual (no fresh degree-`4` source) is killed
by the `T`-incidence count over `T = N(g) ∩ Iso`. -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The blocked share-`1` residual kill for the `(10, 8, 42)` corner.**  When the slot hub `h₂`
carries `isoDeg 1`, shares exactly one twin with the rich hub `g`, and no degree-`4` hub of
`isoDeg ≥ 2` escapes the `{c₀, h₂, z}`-block, the `T = N(g) ∩ Iso` incidence count overflows. -/
theorem blocked_kill_1042_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 8) (hdsum : ∑ w ∈ Hub, G.degree w = 42)
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
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z) :
    False := by
  classical
  have hA : 5 ≥ (Hub.filter (fun h => G.degree h = 4
      ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
    rich_le_five_blocked_1042_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg
      hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2
      hgz hg2 hpoor hshared hblock
  rcases rich_count_1042_twenty G Hub Iso hiso3 hdisj hdeg hdeg5 hHub hIso hdsum hshare
      hno2hub g hg hgd hgiso with h6 | ⟨hR5, hCMB13⟩ | ⟨hR45, hsat, hD4le, hmaster, hCMB⟩
  · omega
  · exact rich_doublecount_kill_1042_twenty G Hub Iso
      (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card))
      hiso3 hisodeg3 hT hshare hno2hub (Finset.filter_subset _ _)
      (fun r hr => (Finset.mem_filter.mp hr).2.1)
      (fun r hr => (Finset.mem_filter.mp hr).2.2) hR5 hCMB13
  · exact anchor_sat_kill_1042_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg
      hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2
      hgz hg2 hpoor hshared hblock hR45 hsat hD4le hmaster hCMB

set_option maxHeartbeats 1000000 in
theorem zleaf_extract_rich_1042_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 8)
    (hdsum : ∑ w ∈ Hub, G.degree w = 42)
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
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    ∃ h₁ h₂ a b c z : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
  obtain ⟨h₂, z, hh₂, hd₂, hzZ, hz2, hgz, hg2, hgh₂, h2ge1⟩ :=
    good_zhub_1042_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg hdeg5
      hHub hIso hdsum hT hshare hno2hub g hg hgd hgiso
  by_cases h2ge2 : 2 ≤ (G.neighborFinset h₂ ∩ Iso).card
  · exact zleaf_pack_rich_twenty G Hub Iso hiso3 hisodeg3 hshare g h₂ z hg hh₂ hgd hd₂
      hzZ hgh₂ hg2 hgiso h2ge2 hz2 hgz
  · have hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1 := by omega
    have hgiso2 : 2 ≤ (G.neighborFinset g ∩ Iso).card := by omega
    rcases Nat.eq_zero_or_pos (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card
      with hsh0 | hshpos
    · exact zleaf_pack_share0_twenty G Hub Iso hiso3 hisodeg3 g h₂ z hg hh₂ hgd hd₂
        hzZ hgh₂ hg2 hgiso2 (by omega) (Finset.card_eq_zero.mp hsh0) hz2 hgz
    · have hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1 := by
        have hsub : G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso
            ⊆ G.neighborFinset h₂ ∩ Iso := by
          intro w hw
          simp only [Finset.mem_inter] at hw ⊢
          exact ⟨hw.1.2, hw.2⟩
        have := Finset.card_le_card hsub
        omega
      by_cases hex : ∃ x : Fin 20, x ∈ Hub ∧ G.degree x = 4 ∧
          2 ≤ (G.neighborFinset x ∩ Iso).card ∧
          ¬(G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
      · obtain ⟨x, hxHub, hxd, hxiso, hxnb⟩ := hex
        push Not at hxnb
        obtain ⟨hxsh, hxh₂, hxz⟩ := hxnb
        have hxne : x ≠ h₂ := by rintro rfl; rw [hpoor] at hxiso; omega
        exact zleaf_pack_share0_twenty G Hub Iso hiso3 hisodeg3 x h₂ z hxHub hh₂ hxd hd₂
          hzZ hxne hxh₂ hxiso (by omega) hxsh hz2 hxz
      · exact absurd (blocked_kill_1042_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3
          hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z
          hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared
          (fun x hxHub hxd hxiso => by
            by_contra hb
            push Not at hb
            exact hex ⟨x, hxHub, hxd, hxiso, by push Not; exact hb⟩)) not_false

end N20

end ACMax
