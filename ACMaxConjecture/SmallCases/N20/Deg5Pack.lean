import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.R5ResidHelpers

/-! # The `Z`-leaf packers (`n = 19`, deg-5 corner): rich and share-`0` witnesses to the 6-tuple -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- Rich packer: `isoDeg h₁ ≥ 3`, `isoDeg h₂ ≥ 2`, non-adjacent, `z` on `h₂` avoided by `h₁`. -/
theorem zleaf_pack_rich_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (_hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (h₁ h₂ z : Fin 20) (hh₁ : h₁ ∈ Hub) (hh₂ : h₂ ∈ Hub)
    (hd₁ : G.degree h₁ = 4) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))) (hne : h₁ ≠ h₂)
    (hn12 : ¬G.Adj h₁ h₂) (h1iso : 3 ≤ (G.neighborFinset h₁ ∩ Iso).card)
    (h2iso : 2 ≤ (G.neighborFinset h₂ ∩ Iso).card)
    (hz2 : G.Adj z h₂) (hn1z : ¬G.Adj h₁ z) :
    ∃ h₁ h₂ a b c z : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
  obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, haX, hbX⟩ :=
    exists_two_private_twins_twenty G Hub Iso hshare h₁ h₂ hh₁ hh₂ hd₁ hd₂ hne hn12 h1iso
  obtain ⟨c, hcIso, hc2, hn1c⟩ :=
    exists_one_private_twin_twenty G Hub Iso hshare h₂ h₁ hh₂ hh₁ hd₂ hd₁ hne hn12 h2iso
  exact ⟨h₁, h₂, a, b, c, z, hh₁, hh₂, hd₁, hd₂, haIso, hbIso, hcIso, hzZ,
    ha1, hb1, hc2, hz2, hn12, hn1c, hn1z, haX, hbX, hab⟩

set_option maxHeartbeats 1000000 in
/-- Share-`0` packer: `isoDeg h₁ ≥ 2`, `isoDeg h₂ ≥ 1`, twin-share `∅`. -/
theorem zleaf_pack_share0_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (_hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (h₁ h₂ z : Fin 20) (hh₁ : h₁ ∈ Hub) (hh₂ : h₂ ∈ Hub)
    (hd₁ : G.degree h₁ = 4) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))) (_hne : h₁ ≠ h₂)
    (hn12 : ¬G.Adj h₁ h₂) (h1iso : 2 ≤ (G.neighborFinset h₁ ∩ Iso).card)
    (h2iso : 1 ≤ (G.neighborFinset h₂ ∩ Iso).card)
    (hsh0 : G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso = ∅)
    (hz2 : G.Adj z h₂) (hn1z : ¬G.Adj h₁ z) :
    ∃ h₁ h₂ a b c z : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset h₁ ∩ Iso).card)
  rw [Finset.mem_inter, G.mem_neighborFinset] at ha hb
  obtain ⟨c, hc⟩ :=
    Finset.card_pos.mp (by omega : 0 < (G.neighborFinset h₂ ∩ Iso).card)
  rw [Finset.mem_inter, G.mem_neighborFinset] at hc
  have hna2 : ¬G.Adj a h₂ := by
    intro he
    have hmem : a ∈ G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := by
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact ⟨⟨ha.1, he.symm⟩, ha.2⟩
    rw [hsh0] at hmem; exact Finset.notMem_empty a hmem
  have hnb2 : ¬G.Adj b h₂ := by
    intro he
    have hmem : b ∈ G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := by
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact ⟨⟨hb.1, he.symm⟩, hb.2⟩
    rw [hsh0] at hmem; exact Finset.notMem_empty b hmem
  have hn1c : ¬G.Adj h₁ c := by
    intro he
    have hmem : c ∈ G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := by
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact ⟨⟨he, hc.1⟩, hc.2⟩
    rw [hsh0] at hmem; exact Finset.notMem_empty c hmem
  exact ⟨h₁, h₂, a, b, c, z, hh₁, hh₂, hd₁, hd₂, ha.2, hb.2, hc.2, hzZ,
    ha.1.symm, hb.1.symm, hc.1.symm, hz2, hn12, hn1c, hn1z, hna2, hnb2, hab⟩

end N20

end ACMax
