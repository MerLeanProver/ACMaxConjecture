import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N15.Core
import ACMaxConjecture.SmallCases.N15.HubTriangleStruct

/-!
# Fully-free hub counting for the `n = 15`, `e(M) = 3`, `|D| = 8` corner

A *fully-free* hub is a degree-`4` hub (`Dᶜ`) non-adjacent to all four path vertices
`L₁, c₁, c₂, L₂`.  This file proves the two counting facts about fully-free hubs consumed by the
triangle-forcing case analysis of `exists_hub_triangle_config_residual`:

* `fully_free_exists`: at least one fully-free hub exists (pigeonhole on the `6 < 7` path
  hub-incidences);
* `fully_free_le_two`: at most two hubs of hub-internal degree `≥ 3` (edge-budget on the `10`
  hub-internal degree total over the `7` hubs).
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **A fully-free hub exists.**  The four path vertices send only `2 + 1 + 1 + 2 = 6` edges to the
seven hubs, so by pigeonhole some hub avoids all of `L₁, c₁, c₂, L₂`. -/
theorem fully_free_exists (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15)) (L₁ c₁ c₂ L₂ : Fin 15)
    (hDc7 : Dᶜ.card = 7)
    (hc1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1) (hc2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2) (hL2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hL1c1 : L₁ ≠ c₁) (hL1c2 : L₁ ≠ c₂) (hL1L2 : L₁ ≠ L₂)
    (hc1c2 : c₁ ≠ c₂) (hc1L2 : c₁ ≠ L₂) (hc2L2 : c₂ ≠ L₂) :
    ∃ f : Fin 15, f ∈ Dᶜ ∧ ¬G.Adj f L₁ ∧ ¬G.Adj f c₁ ∧ ¬G.Adj f c₂ ∧ ¬G.Adj f L₂ := by
  classical
  set S : Finset (Fin 15) := {L₁, c₁, c₂, L₂} with hS
  have hsum : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ S).card = 6 := by
    have hexpand : ∑ w ∈ S, (G.neighborFinset w ∩ Dᶜ).card = 6 := by
      rw [hS, Finset.sum_insert (by simp [hL1c1, hL1c2, hL1L2]),
        Finset.sum_insert (by simp [hc1c2, hc1L2]),
        Finset.sum_insert (by simp [hc2L2]), Finset.sum_singleton]
      omega
    rw [cross_count G Dᶜ S]; exact hexpand
  by_contra hcon
  push Not at hcon
  have hge1 : ∀ w ∈ Dᶜ, 1 ≤ (G.neighborFinset w ∩ S).card := by
    intro w hw
    apply Finset.card_pos.mpr
    by_cases hL1a : G.Adj w L₁
    · exact ⟨L₁, by rw [Finset.mem_inter, G.mem_neighborFinset, hS]; exact ⟨hL1a, by simp⟩⟩
    by_cases hc1a : G.Adj w c₁
    · exact ⟨c₁, by rw [Finset.mem_inter, G.mem_neighborFinset, hS]; exact ⟨hc1a, by simp⟩⟩
    by_cases hc2a : G.Adj w c₂
    · exact ⟨c₂, by rw [Finset.mem_inter, G.mem_neighborFinset, hS]; exact ⟨hc2a, by simp⟩⟩
    · exact ⟨L₂, by
        rw [Finset.mem_inter, G.mem_neighborFinset, hS]
        exact ⟨hcon w hw hL1a hc1a hc2a, by simp⟩⟩
  have hbig : Dᶜ.card • 1 ≤ ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ S).card :=
    Finset.card_nsmul_le_sum Dᶜ (fun w => (G.neighborFinset w ∩ S).card) 1 hge1
  rw [hsum, hDc7, smul_eq_mul] at hbig
  omega

/-- **At most two fully-free hubs.**  Any set `F ⊆ Dᶜ` of hubs each of hub-internal degree `≥ 3`
has `F.card ≤ 2`: three such hubs would need `≥ 9` of the `10` total hub-internal degree, leaving
`≤ 1` for the other four hubs, yet the three contribute at most `6` edges among themselves plus
`≤ 1` edge outward — a total `≤ 7 < 9`. -/
theorem fully_free_le_two (G : SimpleGraph (Fin 15)) (D F : Finset (Fin 15))
    (hFsub : F ⊆ Dᶜ) (hge3 : ∀ g ∈ F, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card)
    (hSum : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 10) :
    F.card ≤ 2 := by
  classical
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨F', hF'sub, hF'card⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ F.card)
  have hF'Dc : F' ⊆ Dᶜ := hF'sub.trans hFsub
  have hge3' : ∀ g ∈ F', 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := fun g hg => hge3 g (hF'sub hg)
  -- lower bound: ∑_{g∈F'} (N g ∩ Dᶜ).card ≥ 9
  have hlow : 9 ≤ ∑ g ∈ F', (G.neighborFinset g ∩ Dᶜ).card := by
    have h := Finset.card_nsmul_le_sum F' (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 hge3'
    rw [hF'card, smul_eq_mul] at h; omega
  -- split each (N g ∩ Dᶜ) = (N g ∩ F') ⊔ (N g ∩ (Dᶜ \ F'))
  have hsplit : ∀ g : Fin 15, (G.neighborFinset g ∩ Dᶜ).card
      = (G.neighborFinset g ∩ F').card + (G.neighborFinset g ∩ (Dᶜ \ F')).card := by
    intro g
    rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
      Finset.union_sdiff_of_subset hF'Dc]
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    rw [Finset.mem_inter] at ha ha'
    exact (Finset.mem_sdiff.mp ha'.2).2 ha.2
  -- ∑_{g∈F'} (N g ∩ F').card ≤ 6
  have hinner : ∑ g ∈ F', (G.neighborFinset g ∩ F').card ≤ 6 := by
    have hb : ∀ g ∈ F', (G.neighborFinset g ∩ F').card ≤ 2 := by
      intro g hg
      have hsub : G.neighborFinset g ∩ F' ⊆ F'.erase g := by
        intro x hx
        rw [Finset.mem_inter, G.mem_neighborFinset] at hx
        exact Finset.mem_erase.mpr ⟨fun e => (G.irrefl (e ▸ hx.1)), hx.2⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hg, hF'card] at this; omega
    calc ∑ g ∈ F', (G.neighborFinset g ∩ F').card ≤ ∑ _g ∈ F', 2 := Finset.sum_le_sum hb
      _ = 6 := by rw [Finset.sum_const, hF'card, smul_eq_mul]
  -- ∑_{g∈F'} (N g ∩ (Dᶜ\F')).card = ∑_{w∈Dᶜ\F'} (N w ∩ F').card ≤ ∑_{w∈Dᶜ\F'} (N w ∩ Dᶜ).card
  have hcross : ∑ g ∈ F', (G.neighborFinset g ∩ (Dᶜ \ F')).card
      = ∑ w ∈ Dᶜ \ F', (G.neighborFinset w ∩ F').card :=
    cross_count G F' (Dᶜ \ F')
  have houter_le : ∑ w ∈ Dᶜ \ F', (G.neighborFinset w ∩ F').card
      ≤ ∑ w ∈ Dᶜ \ F', (G.neighborFinset w ∩ Dᶜ).card := by
    apply Finset.sum_le_sum
    intro w _
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hF'Dc)
  -- ∑_{w∈Dᶜ\F'} (N w ∩ Dᶜ).card = 10 - ∑_{g∈F'} (N g ∩ Dᶜ).card
  have hsdiff : (∑ w ∈ Dᶜ \ F', (G.neighborFinset w ∩ Dᶜ).card)
      + ∑ g ∈ F', (G.neighborFinset g ∩ Dᶜ).card = 10 := by
    rw [Finset.sum_sdiff hF'Dc, hSum]
  -- combine
  have hsumsplit : ∑ g ∈ F', (G.neighborFinset g ∩ Dᶜ).card
      = (∑ g ∈ F', (G.neighborFinset g ∩ F').card)
        + ∑ g ∈ F', (G.neighborFinset g ∩ (Dᶜ \ F')).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun g _ => hsplit g)
  omega

end N15

end ACMax
