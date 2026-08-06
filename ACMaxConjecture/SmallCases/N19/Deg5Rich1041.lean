import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.R5ResidHelpers
import ACMaxConjecture.SmallCases.N19.Deg5ZSlots
import ACMaxConjecture.SmallCases.N19.Deg5SameZ
import ACMaxConjecture.SmallCases.N19.Deg5Pack
import ACMaxConjecture.SmallCases.N19.Deg5RichCap
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041ZHub
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Fresh

/-! # The `(1,041) `rich-world `Z`-leaf extraction (`n = 19`, deg-5 corner) -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
theorem zleaf_extract_rich_1041_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum17 : Hub.card + Iso.card = 17)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 7)
    (hdsum : ∑ w ∈ Hub, G.degree w = 41)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 19) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    ∃ h₁ h₂ a b c z : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
  -- Helper A gives a good deg-`4` `Z`-slot hub `h₂` (isoDeg `≥ 1`).  Case on
  -- isoDeg `h₂`: `≥ 2` closes via `zleaf_pack_rich` (`h₁ := g`); `= 1` splits on
  -- the `g`–`h₂` twin-share: share `0` → `zleaf_pack_share0` (`h₁ := g`), share `1`
  -- → Helper B's fresh source `x` → `zleaf_pack_share0` (`h₁ := x`).
  obtain ⟨h₂, z, hh₂, hd₂, hzZ, hz2, hgz, hg2, hgh₂, h2ge1⟩ :=
    good_zhub_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg hdeg5
      hHub hIso hdsum hT hshare hno2hub g hg hgd hgiso
  by_cases h2ge2 : 2 ≤ (G.neighborFinset h₂ ∩ Iso).card
  · exact zleaf_pack_rich_nineteen G Hub Iso hiso3 hisodeg3 hshare g h₂ z hg hh₂ hgd hd₂
      hzZ hgh₂ hg2 hgiso h2ge2 hz2 hgz
  · have hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1 := by omega
    have hgiso2 : 2 ≤ (G.neighborFinset g ∩ Iso).card := by omega
    rcases Nat.eq_zero_or_pos (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card
      with hsh0 | hshpos
    · exact zleaf_pack_share0_nineteen G Hub Iso hiso3 hisodeg3 g h₂ z hg hh₂ hgd hd₂
        hzZ hgh₂ hg2 hgiso2 (by omega) (Finset.card_eq_zero.mp hsh0) hz2 hgz
    · have hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1 := by
        -- the shared twins sit inside `N h₂ ∩ Iso` (card 1), so share `≤ 1`.
        have hsub : G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso
            ⊆ G.neighborFinset h₂ ∩ Iso := by
          intro w hw
          simp only [Finset.mem_inter] at hw ⊢
          exact ⟨hw.1.2, hw.2⟩
        have := Finset.card_le_card hsub
        omega
      obtain ⟨x, hxHub, hxd, hxiso, hxh₂, hxz, hxne, hxsh0⟩ :=
        rich_source_share0_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak
          hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂
          hzZ hz2 hgz hg2 hpoor hshared
      exact zleaf_pack_share0_nineteen G Hub Iso hiso3 hisodeg3 x h₂ z hxHub hh₂ hxd hd₂
        hzZ hxne hxh₂ hxiso (by omega) hxsh0 hz2 hxz

end N19

end ACMax
