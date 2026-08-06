import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.R5ResidHelpers
import ACMaxConjecture.SmallCases.N19.Deg5ZSlots
import ACMaxConjecture.SmallCases.N19.Deg5SameZ
import ACMaxConjecture.SmallCases.N19.Deg5Pack

/-! # The `(9,38) `tie-world `Z`-leaf extraction (`n = 19`, deg-5 corner) -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
theorem zleaf_extract_tie_938_nineteen (G : SimpleGraph (Fin 19))
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
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hnorich : ∀ h ∈ Hub, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card ≤ 2) :
    ∃ h₁ h₂ a b c z : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
  classical
  -- Every hub has degree `4` or `5`.
  have hpd : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
  -- The deg-4 and deg-5 hub sets.
  set D4 : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 5) with hD5def
  have hmemD4 : ∀ w, w ∈ D4 ↔ w ∈ Hub ∧ G.degree w = 4 := by
    intro w; rw [hD4def]; exact Finset.mem_filter
  have hmemD5 : ∀ w, w ∈ D5 ↔ w ∈ Hub ∧ G.degree w = 5 := by
    intro w; rw [hD5def]; exact Finset.mem_filter
  have hcover : D4 ∪ D5 = Hub := by
    ext h; rw [Finset.mem_union, hmemD4, hmemD5]
    constructor
    · rintro (⟨hh, _⟩ | ⟨hh, _⟩) <;> exact hh
    · intro hh; rcases hpd h hh with h4 | h5
      · exact Or.inl ⟨hh, h4⟩
      · exact Or.inr ⟨hh, h5⟩
  have hdisj45 : Disjoint D4 D5 := by
    rw [Finset.disjoint_left]; intro h hd4 hd5
    rw [hmemD4] at hd4; rw [hmemD5] at hd5; omega
  have hcardsum : D4.card + D5.card = 9 := by
    rw [← hHub, ← hcover, Finset.card_union_of_disjoint hdisj45]
  have hdegsum : ∑ w ∈ Hub, G.degree w = 4 * D4.card + 5 * D5.card := by
    rw [← hcover, Finset.sum_union hdisj45]
    have e4 : ∑ w ∈ D4, G.degree w = 4 * D4.card := by
      have h1 : ∑ w ∈ D4, G.degree w = ∑ _w ∈ D4, 4 :=
        Finset.sum_congr rfl (fun w hw => ((hmemD4 w).mp hw).2)
      rw [h1, Finset.sum_const, smul_eq_mul, mul_comm]
    have e5 : ∑ w ∈ D5, G.degree w = 5 * D5.card := by
      have h1 : ∑ w ∈ D5, G.degree w = ∑ _w ∈ D5, 5 :=
        Finset.sum_congr rfl (fun w hw => ((hmemD5 w).mp hw).2)
      rw [h1, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [e4, e5]
  have h38 : 4 * D4.card + 5 * D5.card = 38 := by rw [← hdegsum]; exact hdsum
  have hD4card : D4.card = 7 := by omega
  have hD5card : D5.card = 2 := by omega
  -- Ledger: the total iso-incidence over hubs is `24`.
  have hledger : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 24 := by
    have hc : ∑ w ∈ Iso, (G.neighborFinset w ∩ Hub).card = ∑ _w ∈ Iso, 3 :=
      Finset.sum_congr rfl (fun w hw => hiso3 w hw)
    rw [cross_count_nineteen G Hub Iso, hc, Finset.sum_const, hIso, smul_eq_mul]
  -- Per-hub cap: deg-4 hubs meet `≤ 2` twins (`hnorich`), deg-5 hubs meet `≤ 5`.
  have hcap : ∀ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≤
      (if G.degree h = 4 then 2 else 5) := by
    intro h hh
    split_ifs with h4
    · exact hnorich h hh h4
    · have hsp := nbr_split_three_nineteen G Hub Iso hdisj h
      have hd5 := hdeg5 h hh
      omega
  -- The cap total is also `24`, so every hub sits at its cap.
  have hcapsum : ∑ h ∈ Hub, (if G.degree h = 4 then 2 else 5) = 24 := by
    rw [← hcover, Finset.sum_union hdisj45]
    have e4 : ∑ w ∈ D4, (if G.degree w = 4 then 2 else 5) = 2 * D4.card := by
      have h1 : ∑ w ∈ D4, (if G.degree w = 4 then 2 else 5) = ∑ _w ∈ D4, 2 :=
        Finset.sum_congr rfl (fun w hw => by rw [if_pos ((hmemD4 w).mp hw).2])
      rw [h1, Finset.sum_const, smul_eq_mul, mul_comm]
    have e5 : ∑ w ∈ D5, (if G.degree w = 4 then 2 else 5) = 5 * D5.card := by
      have h1 : ∑ w ∈ D5, (if G.degree w = 4 then 2 else 5) = ∑ _w ∈ D5, 5 :=
        Finset.sum_congr rfl (fun w hw => by
          rw [if_neg (by have := ((hmemD5 w).mp hw).2; omega)])
      rw [h1, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [e4, e5, hD4card, hD5card]
  have hall : ∀ h ∈ Hub, (G.neighborFinset h ∩ Iso).card =
      (if G.degree h = 4 then 2 else 5) := by
    intro h hh
    by_contra hne
    have hlt : (G.neighborFinset h ∩ Iso).card < (if G.degree h = 4 then 2 else 5) :=
      lt_of_le_of_ne (hcap h hh) hne
    have hsum_lt : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card
        < ∑ h ∈ Hub, (if G.degree h = 4 then 2 else 5) :=
      Finset.sum_lt_sum (fun i hi => hcap i hi) ⟨h, hh, hlt⟩
    rw [hledger, hcapsum] at hsum_lt
    exact absurd hsum_lt (lt_irrefl 24)
  have hiso4 : ∀ h ∈ Hub, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card = 2 := by
    intro h hh h4; have := hall h hh; rw [if_pos h4] at this; exact this
  have hiso5 : ∀ h ∈ Hub, G.degree h = 5 → (G.neighborFinset h ∩ Iso).card = 5 := by
    intro h hh h5; have := hall h hh; rw [if_neg (by omega)] at this; exact this
  -- Deg-5 hubs (being iso-full) meet no `z`-vertex.
  have hd5z0 : ∀ h ∈ Hub, G.degree h = 5 →
      (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by
    intro h hh h5
    have hsp := nbr_split_three_nineteen G Hub Iso hdisj h
    have hi := hiso5 h hh h5
    rw [h5] at hsp; omega
  -- The `Z`-skeleton and the two hubs of `z₁`.
  obtain ⟨z₁, -, -, hz₁Z, -, -, -, -⟩ :=
    zslot_skeleton_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg5 hT
  obtain ⟨-, hz1hub2, -⟩ :=
    zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak z₁ hz₁Z
  obtain ⟨p, q, hpq, hpqEq⟩ := Finset.card_eq_two.mp hz1hub2
  have hpMem : p ∈ G.neighborFinset z₁ ∩ Hub := by rw [hpqEq]; exact Finset.mem_insert_self _ _
  have hqMem : q ∈ G.neighborFinset z₁ ∩ Hub := by
    rw [hpqEq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_inter, G.mem_neighborFinset] at hpMem hqMem
  obtain ⟨hzp, hpHub⟩ := hpMem
  obtain ⟨hzq, hqHub⟩ := hqMem
  -- Both hubs of `z₁` are deg-4 (deg-5 hubs meet no `z`).
  have hp4 : G.degree p = 4 := by
    rcases hpd p hpHub with h4 | h5
    · exact h4
    · exfalso
      have hz0 := hd5z0 p hpHub h5
      have hmem : z₁ ∈ G.neighborFinset p ∩ (Finset.univ \ (Hub ∪ Iso)) := by
        rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hzp.symm, hz₁Z⟩
      rw [Finset.card_eq_zero] at hz0; rw [hz0] at hmem
      exact Finset.notMem_empty _ hmem
  have hq4 : G.degree q = 4 := by
    rcases hpd q hqHub with h4 | h5
    · exact h4
    · exfalso
      have hz0 := hd5z0 q hqHub h5
      have hmem : z₁ ∈ G.neighborFinset q ∩ (Finset.univ \ (Hub ∪ Iso)) := by
        rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hzq.symm, hz₁Z⟩
      rw [Finset.card_eq_zero] at hz0; rw [hz0] at hmem
      exact Finset.notMem_empty _ hmem
  -- The same-`z` pair forces one of `p, q` to have iso-degree `≤ 1`; the forced tie makes both
  -- equal `2`, a contradiction.  The tie world is empty, so the goal holds vacuously.
  obtain ⟨-, -, hor⟩ :=
    same_z_pair_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hT hC4 hno2hub
      z₁ p q hz₁Z hpHub hqHub hp4 hq4 hpq hzp hzq
  exfalso
  rcases hor with h | h
  · have := hiso4 p hpHub hp4; omega
  · have := hiso4 q hqHub hq4; omega

end N19

end ACMax
