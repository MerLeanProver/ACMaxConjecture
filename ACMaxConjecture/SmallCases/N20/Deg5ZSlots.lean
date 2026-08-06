import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.R5ResidHelpers

/-! # The `Z`-slot skeleton for the deg-5 corner (`n = 20`): |Z| = 2, the M-edge, one slot per hub -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- `Z = {z₁, z₂}` with the `M`-edge `z₁∼z₂`, and no hub meets both. -/
theorem zslot_skeleton_deg5_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11) :
    ∃ z₁ z₂ : Fin 20, z₁ ≠ z₂ ∧ z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) = {z₁, z₂} ∧ G.Adj z₁ z₂ ∧
      ∀ h ∈ Hub, ¬(G.Adj h z₁ ∧ G.Adj h z₂) := by
  classical
  have hUcard : (Hub ∪ Iso).card = 18 := by
    rw [Finset.card_union_of_disjoint hdisj]; exact hsum18
  have hZeqc : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) = (Hub ∪ Iso)ᶜ := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
  have hZcard : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)).card = 2 := by
    rw [hZeqc, Finset.card_compl, Fintype.card_fin, hUcard]
  obtain ⟨z₁, z₂, hne, hZeq⟩ := Finset.card_eq_two.mp hZcard
  have hz₁Z : z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) := by
    rw [hZeq]; exact Finset.mem_insert_self z₁ {z₂}
  have hz₂Z : z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) := by
    rw [hZeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self z₂)
  have hfacts := zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
  obtain ⟨h1iso0, h1hub2, h1deg3⟩ := hfacts z₁ hz₁Z
  obtain ⟨_, _, h2deg3⟩ := hfacts z₂ hz₂Z
  have hsplit1 := nbr_split_three_twenty G Hub Iso hdisj z₁
  have hcardZ1 : (G.neighborFinset z₁ ∩ (Finset.univ \ (Hub ∪ Iso))).card = 1 := by
    omega
  have hsub : G.neighborFinset z₁ ∩ (Finset.univ \ (Hub ∪ Iso)) ⊆ {z₂} := by
    intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨hxadj, hxZ⟩ := hx
    rw [G.mem_neighborFinset] at hxadj
    rw [hZeq, Finset.mem_insert, Finset.mem_singleton] at hxZ
    rcases hxZ with rfl | rfl
    · exact absurd hxadj G.irrefl
    · exact Finset.mem_singleton_self _
  have heqZ1 : G.neighborFinset z₁ ∩ (Finset.univ \ (Hub ∪ Iso)) = {z₂} :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcardZ1])
  have hz2mem : z₂ ∈ G.neighborFinset z₁ := by
    have hm : z₂ ∈ G.neighborFinset z₁ ∩ (Finset.univ \ (Hub ∪ Iso)) := by
      rw [heqZ1]; exact Finset.mem_singleton_self z₂
    exact (Finset.mem_inter.mp hm).1
  have hadj12 : G.Adj z₁ z₂ := (G.mem_neighborFinset z₁ z₂).mp hz2mem
  have hz1notHub : z₁ ∉ Hub := by
    have h := hz₁Z
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h; exact h.2.1
  have hz2notHub : z₂ ∉ Hub := by
    have h := hz₂Z
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h; exact h.2.1
  have hnohub : ∀ h ∈ Hub, ¬(G.Adj h z₁ ∧ G.Adj h z₂) := by
    intro h hhub hcontra
    obtain ⟨had1, had2⟩ := hcontra
    have hz1ne : z₁ ≠ h := by rintro rfl; exact hz1notHub hhub
    have hz2ne : z₂ ≠ h := by rintro rfl; exact hz2notHub hhub
    have hdegh : G.degree h ≤ 5 := hdeg5 h hhub
    exact hT ⟨z₁, z₂, h, hne, hz2ne, hz1ne, hadj12, had2.symm, had1.symm, by omega⟩
  exact ⟨z₁, z₂, hne, hz₁Z, hz₂Z, hZeq, hadj12, hnohub⟩

end N20

end ACMax
