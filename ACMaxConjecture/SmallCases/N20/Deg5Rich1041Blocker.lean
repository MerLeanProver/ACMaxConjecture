import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5RichCap

/-! # The blocker upper bound for the (11,7,45) octahedron corner (`n = 20`) -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **Blocked ⟹ `|R| ≤ 5`.**  If every rich degree-`4` hub is blocked (adjacent
to the shared twin `c`, to `h₂`, or to `z`), the rich set has at most `5`
members: `R ⊆ (N c ∪ N h₂ ∪ N z) ∩ Hub ∖ {h₂}`, of sizes `3 + 2 + 2` minus
overlaps (`z` meets exactly `2` hubs by `zfacts_deg5_twenty`). -/
theorem rich_le_five_blocked_1041_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (_hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (_hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (_hHub : Hub.card = 11) (_hIso : Iso.card = 7) (_hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (_hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (_hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (_hg : g ∈ Hub) (_hgd : G.degree g = 4)
    (_hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 20) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hz2 : G.Adj z h₂) (_hgz : ¬G.Adj g z) (_hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z) :
    5 ≥ (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
  classical
  -- === Extract the unique twin `c` of `h₂`. ===
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hpoor
  have hcmem : c ∈ G.neighborFinset h₂ ∩ Iso := by rw [hc]; exact Finset.mem_singleton_self c
  have hcIso : c ∈ Iso := (Finset.mem_inter.mp hcmem).2
  have hcNh₂ : c ∈ G.neighborFinset h₂ := (Finset.mem_inter.mp hcmem).1
  have hh₂c : G.Adj h₂ c := (G.mem_neighborFinset h₂ c).mp hcNh₂
  have hcHub3 : (G.neighborFinset c ∩ Hub).card = 3 := hiso3 c hcIso
  have hh₂inNc : h₂ ∈ G.neighborFinset c ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c h₂).mpr hh₂c.symm, hh₂⟩
  -- === `z` meets exactly two hubs. ===
  have hzf := zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
  obtain ⟨_, hzHub2, _⟩ := hzf z hzZ
  have hh₂inNz : h₂ ∈ G.neighborFinset z ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z h₂).mpr hz2, hh₂⟩
  -- === `h₂` meets at most two hubs (`deg 4 = 1 iso + Hub + ≥ 1` in `Z`). ===
  have hh₂Hub2 : (G.neighborFinset h₂ ∩ Hub).card ≤ 2 := by
    have hsplit := nbr_split_three_twenty G Hub Iso hdisj h₂
    rw [hd₂, hpoor] at hsplit
    have hzInZ : z ∈ G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ z).mpr hz2.symm, hzZ⟩
    have hzge : 1 ≤ (G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))).card :=
      Finset.card_pos.mpr ⟨z, hzInZ⟩
    omega
  -- === The blocker union `U = (N c ∪ N z ∪ N h₂) ∩ Hub`. ===
  set U : Finset (Fin 20) :=
    ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)) ∪ (G.neighborFinset h₂ ∩ Hub)
    with hUdef
  -- === Every rich hub lies in `U ∖ {h₂}`. ===
  have hRsub : (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card))
      ⊆ U.erase h₂ := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxHub, hxdeg, hxiso⟩ := hx
    have hxne : x ≠ h₂ := by
      rintro rfl
      omega
    rw [Finset.mem_erase]
    refine ⟨hxne, ?_⟩
    rw [hUdef]
    rcases hblock x hxHub hxdeg hxiso with hcase1 | hcase2 | hcase3
    · rw [← Finset.nonempty_iff_ne_empty] at hcase1
      obtain ⟨t, ht⟩ := hcase1
      rw [Finset.mem_inter, Finset.mem_inter] at ht
      obtain ⟨⟨htx, hth₂⟩, htIso⟩ := ht
      have htmem : t ∈ G.neighborFinset h₂ ∩ Iso := Finset.mem_inter.mpr ⟨hth₂, htIso⟩
      rw [hc, Finset.mem_singleton] at htmem
      rw [htmem] at htx
      have hxNc : x ∈ G.neighborFinset c :=
        (G.mem_neighborFinset c x).mpr ((G.mem_neighborFinset x c).mp htx).symm
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hxNc, hxHub⟩))
    · have hxNh₂ : x ∈ G.neighborFinset h₂ := (G.mem_neighborFinset h₂ x).mpr hcase2.symm
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxNh₂, hxHub⟩)
    · have hxNz : x ∈ G.neighborFinset z := (G.mem_neighborFinset z x).mpr hcase3.symm
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨hxNz, hxHub⟩))
  -- === `|U| ≤ 6` (`h₂` overlaps `N c ∩ Hub` and `N z ∩ Hub`). ===
  have hUcard : U.card ≤ 6 := by
    have hAC : ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)).card ≤ 4 := by
      have hkey := Finset.card_union_add_card_inter (G.neighborFinset c ∩ Hub)
        (G.neighborFinset z ∩ Hub)
      have hinter1 : 1 ≤ ((G.neighborFinset c ∩ Hub) ∩ (G.neighborFinset z ∩ Hub)).card :=
        Finset.card_pos.mpr ⟨h₂, Finset.mem_inter.mpr ⟨hh₂inNc, hh₂inNz⟩⟩
      rw [hcHub3, hzHub2] at hkey
      omega
    have hunion := Finset.card_union_le
      ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)) (G.neighborFinset h₂ ∩ Hub)
    rw [hUdef]
    omega
  -- === `h₂ ∈ U`, so erasing it drops the count to `≤ 5`. ===
  have hh₂U : h₂ ∈ U := by
    rw [hUdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hh₂inNc)
  have hEraseCard : (U.erase h₂).card ≤ 5 := by
    rw [Finset.card_erase_of_mem hh₂U]; omega
  exact le_trans (Finset.card_le_card hRsub) hEraseCard

end N20

end ACMax
