import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.ZPoorN3
import ACMaxConjecture.SmallCases.N18.ZPoorR7
import ACMaxConjecture.SmallCases.N18.ZVertex
import ACMaxConjecture.SmallCases.N18.ZPoorSat
import ACMaxConjecture.SmallCases.N18.ZPoorR6Dist
import ACMaxConjecture.SmallCases.N18.ZPoorR6Sat
import ACMaxConjecture.SmallCases.N18.ZPoorR6Poor
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdj
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjBStruct

/-!
# Design B (`{3,3,2,2,2,2}`) rich co-occurrence for the `r = 6`, `S = 14` core (`n = 18`)

With the two iso-degree-`3` rich hubs `w₁, w₂` mutually adjacent and hub-isolated apart from each
other (`designB_w_structure_S14`), every iso-degree-`2` rich hub `r` is non-adjacent to both `w₁`
and `w₂` (their only hub-neighbour is each other).  The share hypothesis `hshare` and the
two-hub-profile hypothesis `hno2hub` then pin the twin overlaps: `r` shares **exactly one** twin
with `w₁` and **exactly one** with `w₂`; and two iso-degree-`2` rich hubs `r, r'` are non-adjacent
**iff** they share a twin.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Design B rich co-occurrence.**  Each iso-degree-`2` rich hub `r` (distinct from `w₁, w₂`)
shares exactly one twin with `w₁` and exactly one with `w₂`; and two iso-degree-`2` rich hubs are
non-adjacent iff they co-occur on a common twin. -/
theorem designB_rich_cooccur_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hcherry : ¬∃ t ∈ Iso, ∃ a b : Fin 18, a ∈ G.neighborFinset t ∧ b ∈ G.neighborFinset t ∧
      a ≠ b ∧ G.Adj a b)
    (w1 w2 : Fin 18)
    (hw1Hub : w1 ∈ Hub) (hw2Hub : w2 ∈ Hub)
    (hadjw : G.Adj w1 w2)
    (hw1hub1 : (G.neighborFinset w1 ∩ Hub).card = 1)
    (hw2hub1 : (G.neighborFinset w2 ∩ Hub).card = 1)
    (hw13 : (G.neighborFinset w1 ∩ Iso).card = 3) (hw23 : (G.neighborFinset w2 ∩ Iso).card = 3) :
    (∀ r ∈ Hub, r ≠ w1 → r ≠ w2 → (G.neighborFinset r ∩ Iso).card = 2 →
        (G.neighborFinset w1 ∩ G.neighborFinset r ∩ Iso).card = 1 ∧
        (G.neighborFinset w2 ∩ G.neighborFinset r ∩ Iso).card = 1) ∧
    (∀ r ∈ Hub, ∀ r' ∈ Hub, r ≠ w1 → r ≠ w2 → r' ≠ w1 → r' ≠ w2 →
        (G.neighborFinset r ∩ Iso).card = 2 → (G.neighborFinset r' ∩ Iso).card = 2 → r ≠ r' →
        (¬G.Adj r r' ↔ 1 ≤ (G.neighborFinset r ∩ G.neighborFinset r' ∩ Iso).card)) := by
  classical
  -- `N(w₁) ∩ Hub = {w₂}` and `N(w₂) ∩ Hub = {w₁}`, so `w₁, w₂` meet no other hub.
  have hw2mem : w2 ∈ G.neighborFinset w1 ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjw, hw2Hub⟩
  have hw1mem : w1 ∈ G.neighborFinset w2 ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjw.symm, hw1Hub⟩
  have hw1set : G.neighborFinset w1 ∩ Hub = {w2} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hw2mem, fun x hx =>
      Finset.card_le_one.mp (le_of_eq hw1hub1) x hx w2 hw2mem⟩
  have hw2set : G.neighborFinset w2 ∩ Hub = {w1} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hw1mem, fun x hx =>
      Finset.card_le_one.mp (le_of_eq hw2hub1) x hx w1 hw1mem⟩
  have hw1nadj : ∀ r ∈ Hub, r ≠ w2 → ¬G.Adj w1 r := by
    intro r hrHub hrne hadj
    have : r ∈ G.neighborFinset w1 ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hrHub⟩
    rw [hw1set, Finset.mem_singleton] at this; exact hrne this
  have hw2nadj : ∀ r ∈ Hub, r ≠ w1 → ¬G.Adj w2 r := by
    intro r hrHub hrne hadj
    have : r ∈ G.neighborFinset w2 ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hrHub⟩
    rw [hw2set, Finset.mem_singleton] at this; exact hrne this
  -- Engine: a non-adjacent pair of hubs each with iso-degree `≥ 2` shares `≥ 1` twin (`hno2hub`).
  have engine : ∀ a ∈ Hub, ∀ b ∈ Hub, a ≠ b → ¬G.Adj a b →
      2 ≤ (G.neighborFinset a ∩ Iso).card → 2 ≤ (G.neighborFinset b ∩ Iso).card →
      1 ≤ (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card := by
    intro a haHub b hbHub hab hnadj ha2 hb2
    by_contra hlt
    have hk0 : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card = 0 := by omega
    have hreA : (G.neighborFinset a ∩ Iso) ∩ G.neighborFinset b
        = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
      ext x; simp only [Finset.mem_inter]; tauto
    have hreB : (G.neighborFinset b ∩ Iso) ∩ G.neighborFinset a
        = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
      ext x; simp only [Finset.mem_inter]; tauto
    have hA := Finset.card_inter_add_card_sdiff (G.neighborFinset a ∩ Iso) (G.neighborFinset b)
    have hB := Finset.card_inter_add_card_sdiff (G.neighborFinset b ∩ Iso) (G.neighborFinset a)
    rw [hreA, hk0] at hA
    rw [hreB, hk0] at hB
    exact hno2hub ⟨a, b, haHub, hbHub, hdeg4 a haHub, hdeg4 b hbHub, hab, hnadj, by omega, by omega⟩
  refine ⟨?_, ?_⟩
  · -- Each rich-`2` hub shares exactly one twin with `w₁` and one with `w₂`.
    intro r hrHub hrw1 hrw2 hr2
    have h1 : 1 ≤ (G.neighborFinset w1 ∩ G.neighborFinset r ∩ Iso).card :=
      engine w1 hw1Hub r hrHub (Ne.symm hrw1) (hw1nadj r hrHub hrw2) (by omega) (by omega)
    have h1' : (G.neighborFinset w1 ∩ G.neighborFinset r ∩ Iso).card ≤ 1 :=
      hshare w1 hw1Hub (hdeg4 w1 hw1Hub) r hrHub (hdeg4 r hrHub) (Ne.symm hrw1)
        (hw1nadj r hrHub hrw2)
    have h2 : 1 ≤ (G.neighborFinset w2 ∩ G.neighborFinset r ∩ Iso).card :=
      engine w2 hw2Hub r hrHub (Ne.symm hrw2) (hw2nadj r hrHub hrw1) (by omega) (by omega)
    have h2' : (G.neighborFinset w2 ∩ G.neighborFinset r ∩ Iso).card ≤ 1 :=
      hshare w2 hw2Hub (hdeg4 w2 hw2Hub) r hrHub (hdeg4 r hrHub) (Ne.symm hrw2)
        (hw2nadj r hrHub hrw1)
    exact ⟨le_antisymm h1' h1, le_antisymm h2' h2⟩
  · -- Two rich-`2` hubs are non-adjacent iff they co-occur on a twin.
    intro r hrHub r' hr'Hub _ _ _ _ hr2 hr'2 hrr'
    constructor
    · intro hnadj
      exact engine r hrHub r' hr'Hub hrr' hnadj (by omega) (by omega)
    · intro hpos hadj
      obtain ⟨t, htmem⟩ := Finset.card_pos.mp hpos
      have htIso : t ∈ Iso := (Finset.mem_inter.mp htmem).2
      have htr : t ∈ G.neighborFinset r := (Finset.mem_inter.mp (Finset.mem_inter.mp htmem).1).1
      have htr' : t ∈ G.neighborFinset r' := (Finset.mem_inter.mp (Finset.mem_inter.mp htmem).1).2
      have hrt : r ∈ G.neighborFinset t :=
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp htr).symm
      have hr't : r' ∈ G.neighborFinset t :=
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp htr').symm
      exact hcherry ⟨t, htIso, r, r', hrt, hr't, hrr', hadj⟩

end N18

end ACMax
