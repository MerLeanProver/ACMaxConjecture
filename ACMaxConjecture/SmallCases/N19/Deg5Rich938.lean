import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.R5ResidHelpers
import ACMaxConjecture.SmallCases.N19.Deg5ZSlots
import ACMaxConjecture.SmallCases.N19.Deg5SameZ
import ACMaxConjecture.SmallCases.N19.Deg5Pack
import ACMaxConjecture.SmallCases.N19.Deg5Rich938Select

/-! # The `(9,38) `rich-world `Z`-leaf extraction (`n = 19`, deg-5 corner) -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
theorem zleaf_extract_rich_938_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum17 : Hub.card + Iso.card = 17)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 9) (hIso : Iso.card = 8)
    (hdsum : ∑ w ∈ Hub, G.degree w = 38)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (_hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
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
  -- The tight `(9,8,38)` ledger + the iso-cap give a good deg-`4` `Z`-slot hub
  -- `h₂` (isoDeg `≥ 2`), and `zleaf_pack_rich_nineteen` closes with `h₁ := g`.
  obtain ⟨h₂, z, hh₂, hd₂, h2iso, hzZ, hz2, hgz, hg2⟩ :=
    exists_good_h2z_rich_938_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak
      hdeg hdeg5 hHub hIso hdsum hT hshare hno2hub g hg hgd hgiso
  have hgh₂ : g ≠ h₂ := by rintro rfl; exact hgz hz2.symm
  exact zleaf_pack_rich_nineteen G Hub Iso hiso3 hisodeg3 hshare g h₂ z hg hh₂ hgd hd₂
    hzZ hgh₂ hg2 hgiso h2iso hz2 hgz

end N19

end ACMax
