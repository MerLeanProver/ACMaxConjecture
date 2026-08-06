import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.HubTriangleStruct
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.BipartiteAvoiderTwoHub

/-!
# The distinct-twin `TwoHubConfig` assembly for the `n = 18` cherry `|A| = 5` `C₅` corner

This file closes the last residual `sorry` in `exists_hub_triangle_config_cherry_residual_eighteen`
(`TwinCert18HubTriangleCherry`): the `|A| = 5` distinct-twin branch, where the five cherry-avoiders
form a triangle-free `C₅`/`K_{2,3}` (each fully free) and the five non-avoiders `S = Dᶜ \ A` carry
`≥ 10` of the `15` isolated-twin incidences.  Every twin meets `≤ 1` avoider (`hdistinct`), so each
of the five twins has `≥ 2` of its three hub-neighbours inside `S`.  A non-adjacent pair of `S`-hubs
each carrying two *private* `M`-isolated twins assembles a `TwoHubConfig` (`dense_two_hub_assemble`).

The extraction splits on `R = {h ∈ S : isoDeg h ≥ 3}`.  Each such hub is *fully internal-free*
(degree `4 = 1` cherry `+ 3` twins `+ 0` hub-internal), so any two `R`-hubs are non-adjacent.  When
`|R| ≥ 2` the pair is immediate; otherwise (`|R| ≤ 1`) the sum `∑_S isoDeg ≤ 11`, and a shared-twin
double count (`cherry_double_count`) over the `≥ 4` hubs of isodegree `≥ 2` produces a non-adjacent
share-`0` pair — the cherry-`≥ 1` bound forces every such hub to have hub-internal degree `≤ 1`, so
the `S`-hubs of isodegree `≥ 2` span `≤ 2` edges, leaving a non-adjacent share-`0` pair.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Distinct-twin `TwoHubConfig` assembly for the `|A| = 5` `C₅` cherry corner.** -/
theorem cherry_C5_distinct_twin_twoHub_eighteen (G : SimpleGraph (Fin 18))
    (D Iso A : Finset (Fin 18)) (x y z : Fin 18)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hIsoD : Iso ⊆ D)
    (hdeg4 : ∀ w : Fin 18, w ∈ Dᶜ → G.degree w = 4)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hAsub : A ⊆ Dᶜ) (hcard5 : A.card = 5) (hIso5 : Iso.card = 5) (hDc10 : Dᶜ.card = 10)
    (_havoid : ∀ g ∈ A, ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z)
    (hScherry : ∀ h : Fin 18, h ∈ Dᶜ → h ∉ A → G.Adj h x ∨ G.Adj h y ∨ G.Adj h z)
    (hsplit4 : ∀ h : Fin 18, h ∈ Dᶜ → (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 18))).card
      + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = 4)
    (hdistinct : ∀ t ∈ Iso, (G.neighborFinset t ∩ A).card ≤ 1)
    (hisoSum : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15) :
    TwoHubConfig G := by
  classical
  set S : Finset (Fin 18) := Dᶜ \ A with hSdef
  have hSsub : S ⊆ Dᶜ := by rw [hSdef]; exact Finset.sdiff_subset
  have hScard : S.card = 5 := by
    have h := Finset.card_sdiff_add_card_inter Dᶜ A
    rw [Finset.inter_eq_right.mpr hAsub, hDc10, hcard5] at h
    rw [hSdef]; omega
  -- Every `S`-hub meets a cherry vertex, so its cherry incidence is `≥ 1`.
  have hcher1 : ∀ h : Fin 18, h ∈ S →
      1 ≤ (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 18))).card := by
    intro h hh
    rw [hSdef, Finset.mem_sdiff] at hh
    obtain ⟨hhDc, hhA⟩ := hh
    rcases hScherry h hhDc hhA with hax | hay | haz
    · exact Finset.card_pos.mpr
        ⟨x, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hax, by simp⟩⟩
    · exact Finset.card_pos.mpr
        ⟨y, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hay, by simp⟩⟩
    · exact Finset.card_pos.mpr
        ⟨z, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨haz, by simp⟩⟩
  -- Hence `isoDeg h + internalDeg h ≤ 3` for every `S`-hub.
  have hisoint : ∀ h : Fin 18, h ∈ S → (G.neighborFinset h ∩ Iso).card
      + (G.neighborFinset h ∩ Dᶜ).card ≤ 3 := by
    intro h hh
    have h4 := hsplit4 h (hSsub hh)
    have h1 := hcher1 h hh
    omega
  -- An `isoDeg = 3` hub has hub-internal degree `0`, hence is non-adjacent to every hub.
  have hinternal0 : ∀ h : Fin 18, h ∈ S → (G.neighborFinset h ∩ Iso).card = 3 →
      ∀ h' : Fin 18, h' ∈ Dᶜ → ¬G.Adj h h' := by
    intro h hh hiso3 h' hh'Dc hadj
    have hle := hisoint h hh
    have hpos : 1 ≤ (G.neighborFinset h ∩ Dᶜ).card :=
      Finset.card_pos.mpr
        ⟨h', by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj, hh'Dc⟩⟩
    omega
  -- An `isoDeg = 2` hub has hub-internal degree `≤ 1`.
  have hint_le1 : ∀ h : Fin 18, h ∈ S → (G.neighborFinset h ∩ Iso).card = 2 →
      (G.neighborFinset h ∩ Dᶜ).card ≤ 1 := by
    intro h hh hiso2
    have hle := hisoint h hh
    omega
  -- Each twin meets `≥ 2` of the five `S`-hubs.
  have hdt : ∀ t : Fin 18, t ∈ Iso → 2 ≤ (G.neighborFinset t ∩ S).card := by
    intro t ht
    have h3 := (iso_three_hub_nbrs G D Iso hIsodef hIsoprop t ht).2
    have hA1 := hdistinct t ht
    have hpart : (G.neighborFinset t ∩ A).card + (G.neighborFinset t ∩ S).card
        = (G.neighborFinset t ∩ Dᶜ).card := by
      rw [hSdef, ← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
        Finset.union_sdiff_of_subset hAsub]
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      rw [Finset.mem_inter] at hw hw'
      exact (Finset.mem_sdiff.mp hw'.2).2 hw.2
    omega
  -- The good-`C₄` shared-twin bound on non-adjacent `S`-hub pairs.
  have hshare1 : ∀ p : Fin 18, p ∈ S → ∀ q : Fin 18, q ∈ S → p ≠ q → ¬G.Adj p q →
      (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card ≤ 1 := by
    intro p hp q hq hpq hnadj
    exact nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4 p q
      (hSsub hp) (hSsub hq) hpq hnadj
  -- Sharp `sdiff` bound: private twins of `p` against `q`.
  have hsd : ∀ p q : Fin 18, (G.neighborFinset p ∩ Iso).card
      - (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card
      ≤ ((G.neighborFinset p ∩ Iso) \ G.neighborFinset q).card := by
    intro p q
    have heq : (G.neighborFinset p ∩ Iso) ∩ G.neighborFinset q
        = G.neighborFinset p ∩ G.neighborFinset q ∩ Iso := by
      ext w; simp only [Finset.mem_inter]; tauto
    have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset p ∩ Iso) (G.neighborFinset q)
    rw [heq] at h2; omega
  -- Twin-incidence sums: `∑_A isoDeg ≤ 5`, hence `∑_S isoDeg ≥ 10`.
  have hAiso_le : ∑ g ∈ A, (G.neighborFinset g ∩ Iso).card ≤ 5 := by
    rw [cross_count G A Iso]
    calc ∑ t ∈ Iso, (G.neighborFinset t ∩ A).card ≤ ∑ _t ∈ Iso, 1 :=
          Finset.sum_le_sum (fun t ht => hdistinct t ht)
      _ = 5 := by rw [Finset.sum_const, hIso5, smul_eq_mul, Nat.mul_one]
  have hSiso_ge : 10 ≤ ∑ h ∈ S, (G.neighborFinset h ∩ Iso).card := by
    have hs := Finset.sum_sdiff (f := fun g => (G.neighborFinset g ∩ Iso).card) hAsub
    rw [hisoSum] at hs
    rw [hSdef]; omega
  -- The good non-adjacent pair, each side carrying two private `M`-isolated twins.
  have hpair : ∃ h₁ ∈ S, ∃ h₂ ∈ S, h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
    set R : Finset (Fin 18) := S.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
    by_cases hRcase : 2 ≤ R.card
    · -- **Case A.**  Two `isoDeg = 3` hubs: both hub-internal-free, hence non-adjacent.
      obtain ⟨h₁, hh1R, h₂, hh2R, hne⟩ := Finset.one_lt_card.mp hRcase
      have hh1n : h₁ ∈ S := Finset.mem_of_mem_filter _ hh1R
      have hh2n : h₂ ∈ S := Finset.mem_of_mem_filter _ hh2R
      have hi1 : (G.neighborFinset h₁ ∩ Iso).card = 3 := by
        have := (Finset.mem_filter.mp hh1R).2; have hle := hisoint h₁ hh1n; omega
      have hi2 : (G.neighborFinset h₂ ∩ Iso).card = 3 := by
        have := (Finset.mem_filter.mp hh2R).2; have hle := hisoint h₂ hh2n; omega
      have hnadj : ¬G.Adj h₁ h₂ := hinternal0 h₁ hh1n hi1 h₂ (hSsub hh2n)
      have hs12 := hshare1 h₁ hh1n h₂ hh2n hne hnadj
      have hs21 := hshare1 h₂ hh2n h₁ hh1n (Ne.symm hne) (fun a => hnadj a.symm)
      refine ⟨h₁, hh1n, h₂, hh2n, hne, hnadj, ?_, ?_⟩
      · have := hsd h₁ h₂; omega
      · have := hsd h₂ h₁; omega
    · -- **Case B.**  At most one `isoDeg = 3` hub, so `∑_S isoDeg ≤ 11`.
      have hRle1 : R.card ≤ 1 := by omega
      set Tval : ℕ := ∑ h ∈ S, (G.neighborFinset h ∩ Iso).card with hTvaldef
      have hT11 : Tval ≤ 11 := by
        have hsplit := Finset.sum_filter_add_sum_filter_not S
          (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) (fun h => (G.neighborFinset h ∩ Iso).card)
        rw [← hRdef, ← hTvaldef] at hsplit
        set NR : Finset (Fin 18) :=
          S.filter (fun h => ¬3 ≤ (G.neighborFinset h ∩ Iso).card) with hNRdef
        have hRsum : (∑ h ∈ R, (G.neighborFinset h ∩ Iso).card) ≤ 3 * R.card := by
          calc (∑ h ∈ R, (G.neighborFinset h ∩ Iso).card) ≤ ∑ _h ∈ R, 3 :=
                Finset.sum_le_sum (fun h hh => by
                  have := hisoint h (Finset.mem_of_mem_filter _ hh); omega)
            _ = 3 * R.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        have hNRsum : (∑ h ∈ NR, (G.neighborFinset h ∩ Iso).card) ≤ 2 * NR.card := by
          calc (∑ h ∈ NR, (G.neighborFinset h ∩ Iso).card) ≤ ∑ _h ∈ NR, 2 :=
                Finset.sum_le_sum (fun h hh => by
                  have := (Finset.mem_filter.mp hh).2; omega)
            _ = 2 * NR.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        have hcardsum : R.card + NR.card = 5 := by
          have h : R.card + NR.card = S.card := Finset.card_filter_add_card_filter_not _
          rw [hScard] at h; exact h
        omega
      -- The `isoDeg ≥ 2` hubs.
      set Q : Finset (Fin 18) := S.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hQdef
      have hQsub : Q ⊆ S := Finset.filter_subset _ _
      by_cases hQ5 : Q.card = 5
      · -- **Sub-case `|Q| = 5`:** every `S`-hub has `isoDeg ≥ 2`.
        have hQeqS : Q = S := Finset.eq_of_subset_of_card_le hQsub (by rw [hScard, hQ5])
        have hiso2 : ∀ p : Fin 18, p ∈ S → 2 ≤ (G.neighborFinset p ∩ Iso).card := by
          intro p hp
          have hpQ : p ∈ Q := by rw [hQeqS]; exact hp
          exact (Finset.mem_filter.mp hpQ).2
        by_contra hcon
        -- No good pair ⟹ every non-adjacent distinct `S`-pair shares a twin.
        have hsg : ∀ p : Fin 18, p ∈ S → ∀ q : Fin 18, q ∈ S → p ≠ q → ¬G.Adj p q →
            1 ≤ (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp q hq hpq hnadj
          by_contra hs0
          rw [not_le, Nat.lt_one_iff] at hs0
          refine hcon ⟨p, hp, q, hq, hpq, hnadj, ?_, ?_⟩
          · have h1 := hsd p q; have h2 := hiso2 p hp; omega
          · have h1 := hsd q p; have h2 := hiso2 q hq
            have hcomm : (G.neighborFinset q ∩ G.neighborFinset p ∩ Iso).card = 0 := by
              rw [show G.neighborFinset q ∩ G.neighborFinset p
                = G.neighborFinset p ∩ G.neighborFinset q from Finset.inter_comm _ _]; exact hs0
            omega
        -- Exact double count: `∑∑ share + 30 = 5·Tval`.
        have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card = Tval :=
          (cross_count G S Iso).symm
        have hsq : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card + 30
            = 5 * Tval := by
          have hper : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card + 6
              = 5 * (G.neighborFinset t ∩ S).card := by
            intro t ht
            have h2 := hdt t ht
            have h3 : (G.neighborFinset t ∩ S).card ≤ 3 := by
              calc (G.neighborFinset t ∩ S).card ≤ (G.neighborFinset t ∩ Dᶜ).card :=
                    Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsub)
                _ = 3 := (iso_three_hub_nbrs G D Iso hIsodef hIsoprop t ht).2
            obtain hd | hd : (G.neighborFinset t ∩ S).card = 2 ∨ (G.neighborFinset t ∩ S).card = 3 :=
              by omega
            · rw [hd]
            · rw [hd]
          have hsum : ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card + 6)
              = ∑ t ∈ Iso, 5 * (G.neighborFinset t ∩ S).card := Finset.sum_congr rfl hper
          rw [Finset.sum_add_distrib, Finset.sum_const, hIso5, smul_eq_mul, ← Finset.mul_sum,
            hcross] at hsum
          omega
        have hexact : (∑ p ∈ S, ∑ q ∈ S,
            (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card) + 30 = 5 * Tval := by
          rw [cherry_double_count G S Iso]; exact hsq
        -- Lower bound: `∑∑ share ≥ 2·Tval + 5`.
        have hrow : ∀ p : Fin 18, p ∈ S → 2 * (G.neighborFinset p ∩ Iso).card + 1
            ≤ ∑ q ∈ S, (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp
          have herase := Finset.add_sum_erase S
            (fun q => (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card) hp
          have hpp : (G.neighborFinset p ∩ G.neighborFinset p ∩ Iso).card
              = (G.neighborFinset p ∩ Iso).card := by rw [Finset.inter_self]
          have hlow : ((S.erase p).filter (fun q => ¬G.Adj p q)).card
              ≤ ∑ q ∈ S.erase p, (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
            rw [Finset.card_filter]
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_erase] at hq
            by_cases hadj : G.Adj p q
            · simp [hadj]
            · simp only [hadj, if_true, not_false_iff]
              exact hsg p hp q (Finset.mem_of_mem_erase (Finset.mem_erase.mpr hq))
                (Ne.symm hq.1) hadj
          have hfcard : 1 + (G.neighborFinset p ∩ Iso).card
              ≤ ((S.erase p).filter (fun q => ¬G.Adj p q)).card := by
            have hcf : ((S.erase p).filter (fun q => G.Adj p q)).card
                + ((S.erase p).filter (fun q => ¬G.Adj p q)).card = (S.erase p).card :=
              Finset.card_filter_add_card_filter_not _
            have heraseC : (S.erase p).card = 4 := by rw [Finset.card_erase_of_mem hp, hScard]
            have hadjle : ((S.erase p).filter (fun q => G.Adj p q)).card
                ≤ (G.neighborFinset p ∩ Dᶜ).card := by
              apply Finset.card_le_card
              intro q hq
              rw [Finset.mem_filter, Finset.mem_erase] at hq
              rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨hq.2, hSsub hq.1.2⟩
            have hii := hisoint p hp
            omega
          omega
        have hlb : 2 * Tval + 5 ≤ ∑ p ∈ S, ∑ q ∈ S,
            (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          have hsumform : ∑ p ∈ S, (2 * (G.neighborFinset p ∩ Iso).card + 1) = 2 * Tval + 5 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hScard, smul_eq_mul,
              ← hTvaldef]
          rw [← hsumform]
          exact Finset.sum_le_sum hrow
        omega
      · -- **Sub-case `|Q| = 4`:** the rigid `isoDeg`-multiset `(1, 2, 2, 2, 3)` (`Tval = 10`).  The
        -- unique `isoDeg = 1` hub `h₀` forces one twin `t₀` to meet a single `Q`-hub, sharpening the
        -- `Q`-double count to `∑_{p,q∈Q} share ≤ 2·T_Q − 1 < 2·T_Q ≤ ∑_{p,q∈Q} share`.
        have hRsubQ : R ⊆ Q := by
          intro a ha
          rw [hQdef, Finset.mem_filter]
          exact ⟨Finset.mem_of_mem_filter _ ha, by have := (Finset.mem_filter.mp ha).2; omega⟩
        -- Per-hub `isoDeg ≤ 1 + [h∈Q] + [h∈R]`, giving `Tval ≤ 5 + |Q| + |R|`.
        have hpt : ∀ h ∈ S, (G.neighborFinset h ∩ Iso).card
            ≤ 1 + ((if h ∈ Q then 1 else 0) + (if h ∈ R then 1 else 0)) := by
          intro h hh
          by_cases hQm : h ∈ Q
          · by_cases hRm : h ∈ R
            · simp only [hQm, hRm, if_true]; have := hisoint h hh; omega
            · simp only [hQm, hRm, if_true, if_false]
              have hnr : ¬3 ≤ (G.neighborFinset h ∩ Iso).card := fun hge =>
                hRm (by rw [hRdef, Finset.mem_filter]; exact ⟨hh, hge⟩)
              omega
          · have hRm : h ∉ R := fun ha => hQm (hRsubQ ha)
            simp only [hQm, hRm, if_false]
            have hnq : ¬2 ≤ (G.neighborFinset h ∩ Iso).card := fun hge =>
              hQm (by rw [hQdef, Finset.mem_filter]; exact ⟨hh, hge⟩)
            omega
        have hbound : Tval ≤ 5 + (Q.card + R.card) := by
          have hsumb : Tval ≤ ∑ h ∈ S,
              (1 + ((if h ∈ Q then 1 else 0) + (if h ∈ R then 1 else 0))) := by
            rw [hTvaldef]; exact Finset.sum_le_sum hpt
          have hev : ∑ h ∈ S, (1 + ((if h ∈ Q then 1 else 0) + (if h ∈ R then 1 else 0)))
              = 5 + (Q.card + R.card) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hScard,
              smul_eq_mul, Finset.sum_boole, Finset.sum_boole, Finset.filter_mem_eq_inter,
              Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hQsub,
              Finset.inter_eq_right.mpr (hRsubQ.trans hQsub)]
            push_cast
            ring
          omega
        have hQcard5 : Q.card ≤ 5 := by rw [← hScard]; exact Finset.card_le_card hQsub
        have hQcard4 : Q.card = 4 := by omega
        have hTval10 : Tval = 10 := by omega
        have hRcard1 : R.card = 1 := by omega
        -- Every twin meets exactly two `S`-hubs.
        have hdt2 : ∀ t : Fin 18, t ∈ Iso → (G.neighborFinset t ∩ S).card = 2 := by
          have hsumdt : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card = 10 := by
            rw [← cross_count G S Iso, ← hTvaldef]; exact hTval10
          intro t ht
          by_contra hne
          have hge3 : 3 ≤ (G.neighborFinset t ∩ S).card := by have := hdt t ht; omega
          have hbig : 11 ≤ ∑ t' ∈ Iso, (G.neighborFinset t' ∩ S).card := by
            rw [← Finset.add_sum_erase Iso (fun t' => (G.neighborFinset t' ∩ S).card) ht]
            have hrest : 8 ≤ ∑ t' ∈ Iso.erase t, (G.neighborFinset t' ∩ S).card := by
              have h := Finset.card_nsmul_le_sum (Iso.erase t)
                (fun t' => (G.neighborFinset t' ∩ S).card) 2
                (fun t' ht' => hdt t' (Finset.mem_of_mem_erase ht'))
              simp only [smul_eq_mul] at h
              rw [Finset.card_erase_of_mem ht, hIso5] at h; omega
            omega
          omega
        -- The unique `isoDeg = 1` hub `h₀` and its twin `t₀`.
        have hSQcard : (S \ Q).card = 1 := by
          have h := Finset.card_sdiff_add_card_inter S Q
          rw [Finset.inter_eq_right.mpr hQsub, hScard, hQcard4] at h
          omega
        obtain ⟨h₀, hh0eq⟩ := Finset.card_eq_one.mp hSQcard
        have hh0mem : h₀ ∈ S \ Q := by rw [hh0eq]; exact Finset.mem_singleton_self h₀
        have hh0S : h₀ ∈ S := (Finset.mem_sdiff.mp hh0mem).1
        have hh0Q : h₀ ∉ Q := (Finset.mem_sdiff.mp hh0mem).2
        have hiso0_le1 : (G.neighborFinset h₀ ∩ Iso).card ≤ 1 := by
          by_contra h; rw [not_le] at h
          exact hh0Q (by rw [hQdef, Finset.mem_filter]; exact ⟨hh0S, by omega⟩)
        have hQsum_ge : 8 ≤ ∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card := by
          have h := Finset.card_nsmul_le_sum Q (fun q => (G.neighborFinset q ∩ Iso).card) 2
            (fun q hq => (Finset.mem_filter.mp hq).2)
          simp only [smul_eq_mul] at h
          rw [hQcard4] at h; omega
        have hQsum_le : ∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card ≤ 8 + R.card := by
          have hptQ : ∀ q ∈ Q, (G.neighborFinset q ∩ Iso).card ≤ 2 + (if q ∈ R then 1 else 0) := by
            intro q hq
            by_cases hRm : q ∈ R
            · simp only [hRm, if_true]; have := hisoint q (hQsub hq); omega
            · simp only [hRm, if_false]
              have hnr : ¬3 ≤ (G.neighborFinset q ∩ Iso).card := fun hge =>
                hRm (by rw [hRdef, Finset.mem_filter]; exact ⟨hQsub hq, hge⟩)
              omega
          calc ∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card
              ≤ ∑ q ∈ Q, (2 + (if q ∈ R then 1 else 0)) := Finset.sum_le_sum hptQ
            _ = 8 + R.card := by
                rw [Finset.sum_add_distrib, Finset.sum_const, hQcard4, smul_eq_mul,
                  Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hRsubQ]
                push_cast; ring
        have hsplitQ : (∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card)
            + (G.neighborFinset h₀ ∩ Iso).card = Tval := by
          have hss := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Iso).card) hQsub
          rw [hh0eq, Finset.sum_singleton] at hss
          rw [hTvaldef]; omega
        have hiso0 : (G.neighborFinset h₀ ∩ Iso).card = 1 := by omega
        obtain ⟨t₀, ht0eq⟩ := Finset.card_eq_one.mp hiso0
        have ht0mem : t₀ ∈ G.neighborFinset h₀ ∩ Iso := by
          rw [ht0eq]; exact Finset.mem_singleton_self t₀
        have ht0adj : G.Adj h₀ t₀ ∧ t₀ ∈ Iso := by
          rw [Finset.mem_inter, G.mem_neighborFinset] at ht0mem; exact ht0mem
        -- `t₀` meets exactly one `Q`-hub.
        have ht0Q1 : (G.neighborFinset t₀ ∩ Q).card = 1 := by
          have hpart : (G.neighborFinset t₀ ∩ Q).card + (G.neighborFinset t₀ ∩ (S \ Q)).card
              = (G.neighborFinset t₀ ∩ S).card := by
            rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
              Finset.union_sdiff_of_subset hQsub]
            apply Finset.disjoint_left.mpr
            intro w hw hw'
            rw [Finset.mem_inter] at hw hw'
            exact (Finset.mem_sdiff.mp hw'.2).2 hw.2
          have hsq1 : (G.neighborFinset t₀ ∩ (S \ Q)).card = 1 := by
            rw [hh0eq, Finset.inter_singleton_of_mem
              ((G.mem_neighborFinset _ _).mpr ht0adj.1.symm), Finset.card_singleton]
          have hsts : (G.neighborFinset t₀ ∩ S).card = 2 := hdt2 t₀ ht0adj.2
          omega
        -- Every twin meets `≤ 2` of the four `Q`-hubs.
        have htQ2 : ∀ t : Fin 18, t ∈ Iso → (G.neighborFinset t ∩ Q).card ≤ 2 := by
          intro t ht
          calc (G.neighborFinset t ∩ Q).card ≤ (G.neighborFinset t ∩ S).card :=
                Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hQsub)
            _ = 2 := hdt2 t ht
        set TQ : ℕ := ∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card with hTQdef
        have hcrossQ : ∑ t ∈ Iso, (G.neighborFinset t ∩ Q).card = TQ :=
          (cross_count G Q Iso).symm
        -- Sharpened double count: `∑_t (N t ∩ Q)² + 1 ≤ 2·TQ`.
        have hRHSle : (∑ t ∈ Iso, (G.neighborFinset t ∩ Q).card * (G.neighborFinset t ∩ Q).card) + 1
            ≤ 2 * TQ := by
          have hsplit_erase : (G.neighborFinset t₀ ∩ Q).card
              + ∑ t ∈ Iso.erase t₀, (G.neighborFinset t ∩ Q).card = TQ := by
            rw [Finset.add_sum_erase Iso (fun t => (G.neighborFinset t ∩ Q).card) ht0adj.2]
            exact hcrossQ
          have hrest : ∑ t ∈ Iso.erase t₀,
              (G.neighborFinset t ∩ Q).card * (G.neighborFinset t ∩ Q).card
              ≤ 2 * ∑ t ∈ Iso.erase t₀, (G.neighborFinset t ∩ Q).card := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro t ht'
            have h2 := htQ2 t (Finset.mem_of_mem_erase ht')
            nlinarith [h2]
          have ht0sq : (G.neighborFinset t₀ ∩ Q).card * (G.neighborFinset t₀ ∩ Q).card = 1 := by
            rw [ht0Q1]
          rw [← Finset.add_sum_erase Iso
            (fun t => (G.neighborFinset t ∩ Q).card * (G.neighborFinset t ∩ Q).card) ht0adj.2]
          omega
        -- No good pair ⟹ every non-adjacent distinct `Q`-pair shares a twin.
        by_contra hcon
        have hsgQ : ∀ p : Fin 18, p ∈ Q → ∀ q : Fin 18, q ∈ Q → p ≠ q → ¬G.Adj p q →
            1 ≤ (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp q hq hpq hnadj
          by_contra hs0
          rw [not_le, Nat.lt_one_iff] at hs0
          have hip := (Finset.mem_filter.mp hp).2
          have hiq := (Finset.mem_filter.mp hq).2
          refine hcon ⟨p, hQsub hp, q, hQsub hq, hpq, hnadj, ?_, ?_⟩
          · have := hsd p q; omega
          · have := hsd q p
            have hcomm : (G.neighborFinset q ∩ G.neighborFinset p ∩ Iso).card = 0 := by
              rw [show G.neighborFinset q ∩ G.neighborFinset p
                = G.neighborFinset p ∩ G.neighborFinset q from Finset.inter_comm _ _]; exact hs0
            omega
        have hrowQ : ∀ p : Fin 18, p ∈ Q → 2 * (G.neighborFinset p ∩ Iso).card
            ≤ ∑ q ∈ Q, (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp
          have herase := Finset.add_sum_erase Q
            (fun q => (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card) hp
          have hpp : (G.neighborFinset p ∩ G.neighborFinset p ∩ Iso).card
              = (G.neighborFinset p ∩ Iso).card := by rw [Finset.inter_self]
          have hlow : ((Q.erase p).filter (fun q => ¬G.Adj p q)).card
              ≤ ∑ q ∈ Q.erase p, (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
            rw [Finset.card_filter]
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_erase] at hq
            by_cases hadj : G.Adj p q
            · simp [hadj]
            · simp only [hadj, if_true, not_false_iff]
              exact hsgQ p hp q (Finset.mem_of_mem_erase (Finset.mem_erase.mpr hq))
                (Ne.symm hq.1) hadj
          have hfcard : (G.neighborFinset p ∩ Iso).card
              ≤ ((Q.erase p).filter (fun q => ¬G.Adj p q)).card := by
            have hcf : ((Q.erase p).filter (fun q => G.Adj p q)).card
                + ((Q.erase p).filter (fun q => ¬G.Adj p q)).card = (Q.erase p).card :=
              Finset.card_filter_add_card_filter_not _
            have heraseC : (Q.erase p).card = 3 := by rw [Finset.card_erase_of_mem hp, hQcard4]
            have hadjle : ((Q.erase p).filter (fun q => G.Adj p q)).card
                ≤ (G.neighborFinset p ∩ Dᶜ).card := by
              apply Finset.card_le_card
              intro q hq
              rw [Finset.mem_filter, Finset.mem_erase] at hq
              rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨hq.2, hSsub (hQsub hq.1.2)⟩
            have hii := hisoint p (hQsub hp)
            omega
          omega
        have hexactQ : (∑ p ∈ Q, ∑ q ∈ Q,
            (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card)
            = ∑ t ∈ Iso, (G.neighborFinset t ∩ Q).card * (G.neighborFinset t ∩ Q).card :=
          cherry_double_count G Q Iso
        have hlbQ : 2 * TQ ≤ ∑ p ∈ Q, ∑ q ∈ Q,
            (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          have hform : ∑ p ∈ Q, 2 * (G.neighborFinset p ∩ Iso).card = 2 * TQ := by
            rw [← Finset.mul_sum, ← hTQdef]
          rw [← hform]
          exact Finset.sum_le_sum hrowQ
        rw [hexactQ] at hlbQ
        omega
  -- Common extraction of the `TwoHubConfig` from the good pair (via `dense_two_hub_assemble`).
  obtain ⟨h₁, hh1n, h₂, hh2n, hne, hnadj, hp1, hp2⟩ := hpair
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hp1
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hp2
  have getmem : ∀ w u v : Fin 18, w ∈ (G.neighborFinset u ∩ Iso) \ G.neighborFinset v →
      G.Adj u w ∧ w ∈ Iso ∧ ¬G.Adj v w := by
    intro w u v hw
    rw [Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hw
    exact ⟨hw.1.1, hw.1.2, fun hadj => hw.2 ((G.mem_neighborFinset _ _).mpr hadj)⟩
  obtain ⟨ha1, haI, ha2⟩ := getmem a h₁ h₂ ha
  obtain ⟨hb1, hbI, hb2⟩ := getmem b h₁ h₂ hb
  obtain ⟨hc1, hcI, hc2⟩ := getmem c h₂ h₁ hc
  obtain ⟨hd1, hdI, hd2⟩ := getmem d h₂ h₁ hd
  have hdh1 : G.degree h₁ = 4 := hdeg4 h₁ (hSsub hh1n)
  have hdh2 : G.degree h₂ = 4 := hdeg4 h₂ (hSsub hh2n)
  exact dense_two_hub_assemble G h₁ h₂ a b c d hdh1 hdh2 (hIsoprop a haI).1 (hIsoprop b hbI).1
    (hIsoprop c hcI).1 (hIsoprop d hdI).1 ha1.symm hb1.symm hc1.symm hd1.symm hnadj
    hc2 hd2 (fun hadj => ha2 hadj.symm) (fun hadj => hb2 hadj.symm)
    (hIsoprop a haI).2 (hIsoprop b hbI).2 hab hcd

end N18

end ACMax
