import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect

/-!
# `n = 19`, `e(M) = 0` maximal-hub corner `(12, 8, 48)` (`|D| = 8`, `|Hub| = 12`)

This file closes the `s = 0`, `|D| = 8` residual of `two_hub_config_twenty`
(`TwinCert20.lean:517`).  There the twelve hubs all have degree `4`, the eight `M`-isolated twins
each meet exactly three hubs, so `∑_{h∈Hub} |N h ∩ Iso| = 3·8 = 24`.  The residual master
inequality only *ties* here (`134 = 134`), so counting alone does not close it; instead we use the
**max-hub selection**:

Let `h*` maximise `a(h) := |N h ∩ Iso|` (so `A := a(h*) ≤ 4`).  Assume no good two-hub pair
(`nogood_of_not_select_twenty`), giving for every non-adjacent hub `b`:
`a(b) = min(A, a(b)) ≤ shared(h*, b) + 1`, where `shared(h*, b) := |N h* ∩ N b ∩ Iso|`.  Then

* `∑_{b ≠ h*} a(b) = 24 − A`  (total iso-degree `24`);
* `∑_{b ≠ h*} shared(h*, b) = 2A`  (cross-count: each of `h*`'s `A` twins meets `3` hubs, i.e. `2`
  besides `h*`);
* adjacent hubs share `0` twins (`hadj0`, an `hT` light triangle `4 + 4 + 3 = 11`), and there are
  `≤ 4 − A` of them (`hub_neighbor_le_twenty`).

Splitting the `b ≠ h*` sum along adjacency to `h*` bounds `24 − A ≤ 23 − A`, a contradiction.  Hence
a good pair exists (`TwoHubConfig` via `pairToTH` at the call site). -/

namespace ACMax

open scoped Classical

namespace N20

/-- **Maximal-hub good-pair selection (`n = 19`, `(12, 8, 48)`).**  Under the `s = 0`, `|D| = 8`
structure (twelve degree-`4` hubs, eight tri-incident twins, adjacent hubs sharing no twin) a good
non-adjacent degree-`4` pair with `≥ 2` private twins on each side exists. -/
theorem two_hub_maxhub_pair_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hHub12 : Hub.card = 12) (hIso8 : Iso.card = 8)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso)
    (hadj0 : ∀ a ∈ Hub, ∀ b ∈ Hub, G.Adj a b →
      (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card = 0) :
    ∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  -- Total iso-degree `= 24`.
  have htot : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 24 := by
    have h := hub_iso_sum_twenty G Hub Iso hiso3; rw [h, hIso8]
  by_contra hcon
  have key := nogood_of_not_select_twenty G Hub Iso hcon
  -- `h*` maximises iso-degree.
  have hHubne : Hub.Nonempty := by rw [← Finset.card_pos, hHub12]; norm_num
  obtain ⟨hs, hsHub, hsmax⟩ :=
    Finset.exists_max_image Hub (fun h => (G.neighborFinset h ∩ Iso).card) hHubne
  set A : ℕ := (G.neighborFinset hs ∩ Iso).card with hAdef
  have hAle4 : A ≤ 4 := by
    rw [hAdef]
    calc (G.neighborFinset hs ∩ Iso).card
        ≤ (G.neighborFinset hs).card := Finset.card_le_card Finset.inter_subset_left
      _ = G.degree hs := G.card_neighborFinset_eq_degree hs
      _ = 4 := hdeg4 hs hsHub
  set S : Finset (Fin 20) := Hub.erase hs with hSdef
  have hScard : S.card = 11 := by rw [hSdef, Finset.card_erase_of_mem hsHub, hHub12]
  -- `φ b := shared(h*, b)`.
  set φ : Fin 20 → ℕ := fun b => (G.neighborFinset hs ∩ G.neighborFinset b ∩ Iso).card with hφ
  -- **(F1)** `∑_{b∈S} a(b) = 24 − A`.
  have hF1 : ∑ b ∈ S, (G.neighborFinset b ∩ Iso).card = 24 - A := by
    have hsplit := Finset.add_sum_erase Hub (fun b => (G.neighborFinset b ∩ Iso).card) hsHub
    rw [htot, ← hAdef] at hsplit
    rw [hSdef]; omega
  -- **(F2)** `∑_{b∈Hub} φ b = 3A`, hence `∑_{b∈S} φ b = 2A`.
  set Y : Finset (Fin 20) := G.neighborFinset hs ∩ Iso with hYdef
  have hYcard : Y.card = A := by rw [hYdef, hAdef]
  have hYsubIso : Y ⊆ Iso := by rw [hYdef]; exact Finset.inter_subset_right
  have hcross : ∑ b ∈ Hub, (G.neighborFinset b ∩ Y).card
      = ∑ p ∈ Y, (G.neighborFinset p ∩ Hub).card := cross_count_twenty G Hub Y
  have hrhs : ∑ p ∈ Y, (G.neighborFinset p ∩ Hub).card = 3 * A := by
    rw [Finset.sum_congr rfl (fun p hp => hiso3 p (hYsubIso hp)), Finset.sum_const, hYcard,
      smul_eq_mul, mul_comm]
  have hφeq : ∀ b : Fin 20, (G.neighborFinset b ∩ Y).card = φ b := by
    intro b
    simp only [hφ, hYdef]
    congr 1
    ext w
    simp only [Finset.mem_inter]
    tauto
  have hHubφ : ∑ b ∈ Hub, φ b = 3 * A := by
    rw [← hrhs, ← hcross]; exact Finset.sum_congr rfl (fun b _ => (hφeq b).symm)
  have hφself : φ hs = A := by
    simp only [hφ]
    rw [Finset.inter_self, ← hAdef]
  have hF2 : ∑ b ∈ S, φ b = 2 * A := by
    have hsplit := Finset.add_sum_erase Hub φ hsHub
    rw [hHubφ, hφself] at hsplit
    rw [hSdef]; omega
  have hAle4' : A ≤ 4 := hAle4
  -- **Adjacency split of `S`.**
  set P : Fin 20 → Prop := fun b => G.Adj hs b with hP
  have hAdjEq : S.filter P = G.neighborFinset hs ∩ Hub := by
    ext b
    simp only [hSdef, hP, Finset.mem_filter, Finset.mem_erase, Finset.mem_inter,
      G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨_, hbHub⟩, hadj⟩; exact ⟨hadj, hbHub⟩
    · rintro ⟨hadj, hbHub⟩; exact ⟨⟨G.ne_of_adj hadj ∘ Eq.symm, hbHub⟩, hadj⟩
  have hadjcard : (S.filter P).card + A ≤ 4 := by
    rw [hAdjEq, hAdef]
    exact hub_neighbor_le_twenty G Hub Iso hdisj hs (hdeg4 hs hsHub)
  -- `a`-sum split.
  have haSplit : ∑ b ∈ S.filter P, (G.neighborFinset b ∩ Iso).card
      + ∑ b ∈ S.filter (fun b => ¬ P b), (G.neighborFinset b ∩ Iso).card
      = ∑ b ∈ S, (G.neighborFinset b ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not S P _
  -- `φ`-sum split.
  have hφSplit : ∑ b ∈ S.filter P, φ b + ∑ b ∈ S.filter (fun b => ¬ P b), φ b = ∑ b ∈ S, φ b :=
    Finset.sum_filter_add_sum_filter_not S P _
  have hcardSplit : (S.filter P).card + (S.filter (fun b => ¬ P b)).card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) P
  -- Adjacent hubs contribute `φ = 0`.
  have hφPzero : ∑ b ∈ S.filter P, φ b = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbS, hadj⟩ := hb
    have hbHub : b ∈ Hub := Finset.mem_of_mem_erase (hSdef ▸ hbS)
    exact hadj0 hs hsHub b hbHub hadj
  -- Adjacent hubs: `a(b) ≤ 4`.
  have haPle : ∑ b ∈ S.filter P, (G.neighborFinset b ∩ Iso).card ≤ 4 * (S.filter P).card := by
    calc ∑ b ∈ S.filter P, (G.neighborFinset b ∩ Iso).card
        ≤ ∑ _b ∈ S.filter P, 4 := by
          apply Finset.sum_le_sum
          intro b hb
          have hbHub : b ∈ Hub := Finset.mem_of_mem_erase (hSdef ▸ (Finset.mem_filter.mp hb).1)
          calc (G.neighborFinset b ∩ Iso).card
              ≤ (G.neighborFinset b).card := Finset.card_le_card Finset.inter_subset_left
            _ = G.degree b := G.card_neighborFinset_eq_degree b
            _ = 4 := hdeg4 b hbHub
      _ = 4 * (S.filter P).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- Non-adjacent hubs: `a(b) ≤ φ b + 1`  (the max-hub `key`).
  have haNle : ∑ b ∈ S.filter (fun b => ¬ P b), (G.neighborFinset b ∩ Iso).card
      ≤ ∑ b ∈ S.filter (fun b => ¬ P b), (φ b + 1) := by
    apply Finset.sum_le_sum
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbS, hnadj⟩ := hb
    have hbHub : b ∈ Hub := Finset.mem_of_mem_erase (hSdef ▸ hbS)
    have hbne : hs ≠ b := (Finset.ne_of_mem_erase (hSdef ▸ hbS)).symm
    have hnadj' : ¬ G.Adj hs b := hnadj
    have hk := key hs hsHub b hbHub (hdeg4 hs hsHub) (hdeg4 b hbHub) hbne hnadj'
    have hmin : min ((G.neighborFinset hs ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card)
        = (G.neighborFinset b ∩ Iso).card :=
      min_eq_right (le_of_le_of_eq (hsmax b hbHub) hAdef)
    rw [hmin] at hk
    -- `hk : a(b) ≤ shared(hs, b) + 1`; `shared(hs,b) = φ b`.
    have hφb : (G.neighborFinset hs ∩ G.neighborFinset b ∩ Iso).card = φ b := rfl
    omega
  have haNsum : ∑ b ∈ S.filter (fun b => ¬ P b), (φ b + 1)
      = (∑ b ∈ S.filter (fun b => ¬ P b), φ b) + (S.filter (fun b => ¬ P b)).card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  -- Assemble: `24 − A ≤ 22 − A`.
  exfalso
  omega

end N20

end ACMax
