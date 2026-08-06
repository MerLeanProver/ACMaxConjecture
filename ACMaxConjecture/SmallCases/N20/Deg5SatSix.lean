/-
# ACMAX n = 20 — the six-saturated-hubs anchor kill (deg-5 corner, `(11,7,45)`)

**N1 of the `(11,7,45)` repair**: in the deg-5 corner ledger-tie worlds, the
renumbered n = 19 bookkeeping leaves exactly three surviving corners, and each
of them forces the same local shape: a rich degree-4 hub `g` with `isoDeg g = 3`,
an anchor `f` with `isoDeg f ≥ 4`, and **six** further degree-4 hubs, all
non-adjacent to `g`, each with `isoDeg` exactly `2`.  This file kills that shape
outright (`False`), so `good_zhub_1041_twenty` keeps its original n = 19
conclusion.

The argument (pure counting, no pair-count machinery):

* every `s ∈ S` shares a twin with `g` (else `hno2hub` fires on `(g, s)`);
* double-counting the `3 × 3 = 9` twin–hub incidences of `Tg := N(g) ∩ Iso`
  over `Hub ⊇ {g} ∪ S` pins **exactly one** shared twin per `s` and **zero**
  for the anchor `f`;
* hence `N(f) ∩ Iso = Iso \ Tg` (both have four elements), so `f` is adjacent
  to every twin outside `Tg`;
* fixing `s₀ ∈ S` with twins `{a, b}` (`a ∈ Tg`, `b ∉ Tg`), every other
  `s' ∈ S` is adjacent to `s₀` or meets `{a, b}` (`hno2hub` on `(s₀, s')`),
  which traps the five of them in a set of size `≤ 2 + 1 + 1 = 4` — the twin
  `a` already carries `g, s₀` among its three hubs and `b` carries `f, s₀`.
-/

import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.ZVertex

namespace ACMax

open SimpleGraph Finset

open scoped Classical

namespace N20

/-- **The six-saturated-hubs kill.**  A rich degree-4 hub `g` (three twins), an
anchor `f` with at least four twins, and six degree-4 hubs avoiding `g` with
exactly two twins each cannot coexist over a 7-twin isolated layer. -/
theorem six_saturated_anchor_kill_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 7)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧
      G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g f : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : (G.neighborFinset g ∩ Iso).card = 3)
    (hf : f ∈ Hub) (hfiso : 4 ≤ (G.neighborFinset f ∩ Iso).card)
    (S : Finset (Fin 20)) (hS : S ⊆ Hub) (hScard : S.card = 6)
    (hSdeg : ∀ s ∈ S, G.degree s = 4) (hSg : ∀ s ∈ S, ¬G.Adj g s ∧ s ≠ g)
    (hSiso : ∀ s ∈ S, (G.neighborFinset s ∩ Iso).card = 2) : False := by
  classical
  -- `f` is outside `S ∪ {g}` (its twin count is too large).
  have hfS : f ∉ S := fun hmem => by have := hSiso f hmem; omega
  have hfg : f ≠ g := fun h => by rw [h] at hfiso; omega
  have hgS : g ∉ S := fun hmem => (hSg g hmem).2 rfl
  -- The twin set of `g`.
  set Tg : Finset (Fin 20) := G.neighborFinset g ∩ Iso with hTgdef
  have hTgsub : Tg ⊆ Iso := Finset.inter_subset_right
  have hTgcard : Tg.card = 3 := hgiso
  -- Every `s ∈ S` shares at least one twin with `g`.
  have hshare1 : ∀ s ∈ S, 1 ≤ (G.neighborFinset s ∩ Tg).card := by
    intro s hs
    by_contra hcon
    push Not at hcon
    interval_cases h : (G.neighborFinset s ∩ Tg).card
    have hzero : G.neighborFinset s ∩ Tg = ∅ := Finset.card_eq_zero.mp h
    refine hno2hub ⟨g, s, hg, hS hs, hgd, hSdeg s hs, fun he => (hSg s hs).2 he.symm,
      (hSg s hs).1, ?_, ?_⟩
    · -- `(N g ∩ Iso) \ N s = Tg` entirely: no twin of `g` is seen by `s`.
      have hall : Tg \ G.neighborFinset s = Tg := by
        rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
        intro t ht hts
        exact absurd (Finset.mem_inter.mpr ⟨hts, ht⟩)
          (by rw [hzero]; exact Finset.notMem_empty t)
      rw [← hTgdef, hall, hTgcard]; omega
    · -- `(N s ∩ Iso) \ N g = N s ∩ Iso` entirely.
      have hall : (G.neighborFinset s ∩ Iso) \ G.neighborFinset g
          = G.neighborFinset s ∩ Iso := by
        rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
        intro t ht htg
        have : t ∈ G.neighborFinset s ∩ Tg := by
          rw [hTgdef]
          exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ht).1,
            Finset.mem_inter.mpr ⟨htg, (Finset.mem_inter.mp ht).2⟩⟩
        exact absurd this (by rw [hzero]; exact Finset.notMem_empty t)
      rw [hall, hSiso s hs]
  -- Double count the `9` twin–hub incidences of `Tg`.
  have htotal : ∑ h ∈ Hub, (G.neighborFinset h ∩ Tg).card = 9 := by
    have h1 : ∑ t ∈ Tg, (G.neighborFinset t ∩ Hub).card = 9 := by
      rw [Finset.sum_congr rfl (fun t ht => hiso3 t (hTgsub ht)), Finset.sum_const,
        hTgcard, smul_eq_mul]
    calc ∑ h ∈ Hub, (G.neighborFinset h ∩ Tg).card
        = ∑ t ∈ Tg, (G.neighborFinset t ∩ Hub).card := cross_count_twenty G Hub Tg
      _ = 9 := h1
  -- `g` alone contributes `3`.
  have hgterm : (G.neighborFinset g ∩ Tg).card = 3 := by
    have : Tg ⊆ G.neighborFinset g ∩ Tg := by
      intro t ht
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hTgdef ▸ ht)).1, ht⟩
    have h2 : G.neighborFinset g ∩ Tg ⊆ Tg := Finset.inter_subset_right
    rw [Finset.Subset.antisymm h2 this, hTgcard]
  -- The pigeonhole over `P := insert g S`.
  set P : Finset (Fin 20) := insert g S with hPdef
  have hPsub : P ⊆ Hub := by
    rw [hPdef]; exact Finset.insert_subset hg hS
  have hPsum : 9 ≤ ∑ h ∈ P, (G.neighborFinset h ∩ Tg).card := by
    rw [hPdef, Finset.sum_insert hgS, hgterm]
    have : 6 ≤ ∑ s ∈ S, (G.neighborFinset s ∩ Tg).card := by
      calc 6 = ∑ _s ∈ S, 1 := by rw [Finset.sum_const, hScard, smul_eq_mul]
        _ ≤ ∑ s ∈ S, (G.neighborFinset s ∩ Tg).card := Finset.sum_le_sum hshare1
    omega
  have hsplit : ∑ h ∈ P, (G.neighborFinset h ∩ Tg).card
      + ∑ h ∈ Hub \ P, (G.neighborFinset h ∩ Tg).card = 9 := by
    rw [← htotal]
    have := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Tg).card) hPsub
    omega
  -- The anchor sees no twin of `g`.
  have hfzero : (G.neighborFinset f ∩ Tg).card = 0 := by
    have hfP : f ∉ P := by
      rw [hPdef, Finset.mem_insert]
      push Not
      exact ⟨hfg, hfS⟩
    have hrest : ∑ h ∈ Hub \ P, (G.neighborFinset h ∩ Tg).card = 0 := by omega
    exact (Finset.sum_eq_zero_iff.mp hrest) f (Finset.mem_sdiff.mpr ⟨hf, hfP⟩)
  -- Each `s ∈ S` shares exactly one twin with `g`.
  have hSsum : ∑ s ∈ S, (G.neighborFinset s ∩ Tg).card = 6 := by
    have := hsplit
    rw [hPdef, Finset.sum_insert hgS, hgterm] at this
    have h6 : 6 ≤ ∑ s ∈ S, (G.neighborFinset s ∩ Tg).card := by
      calc 6 = ∑ _s ∈ S, 1 := by rw [Finset.sum_const, hScard, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hshare1
    omega
  -- `N f ∩ Iso = Iso \ Tg` — the anchor covers everything outside `Tg`.
  have hfeq : G.neighborFinset f ∩ Iso = Iso \ Tg := by
    have hsub : G.neighborFinset f ∩ Iso ⊆ Iso \ Tg := by
      intro t ht
      rcases Finset.mem_inter.mp ht with ⟨htf, hti⟩
      refine Finset.mem_sdiff.mpr ⟨hti, fun htg => ?_⟩
      have : t ∈ G.neighborFinset f ∩ Tg := Finset.mem_inter.mpr ⟨htf, htg⟩
      rw [Finset.card_eq_zero.mp hfzero] at this
      exact Finset.notMem_empty t this
    have hc : (Iso \ Tg).card = 4 := by
      have h1 := Finset.card_sdiff_add_card_inter Iso Tg
      have h2 : Iso ∩ Tg = Tg := Finset.inter_eq_right.mpr hTgsub
      rw [h2, hIso, hTgcard] at h1
      omega
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  -- Fix `s₀ ∈ S` and its twin pair `{a, b}`.
  obtain ⟨s₀, hs₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hs₀share : (G.neighborFinset s₀ ∩ Tg).card = 1 := by
    have hone : ∀ s ∈ S, (G.neighborFinset s ∩ Tg).card = 1 := by
      -- six terms, each `≥ 1`, summing to `6`.
      intro s hs
      by_contra hne
      have h2 : 2 ≤ (G.neighborFinset s ∩ Tg).card := by
        have := hshare1 s hs; omega
      have : 7 ≤ ∑ s' ∈ S, (G.neighborFinset s' ∩ Tg).card := by
        rw [← Finset.add_sum_erase _ _ hs]
        have h5 : 5 ≤ ∑ s' ∈ S.erase s, (G.neighborFinset s' ∩ Tg).card := by
          calc 5 = ∑ _s' ∈ S.erase s, 1 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hs, hScard, smul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum (fun s' hs' =>
                hshare1 s' (Finset.mem_of_mem_erase hs'))
        omega
      omega
    exact hone s₀ hs₀
  obtain ⟨a, ha⟩ : (G.neighborFinset s₀ ∩ Tg).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases Finset.mem_inter.mp ha with ⟨has₀, haTg⟩
  have haIso : a ∈ Iso := hTgsub haTg
  -- The second twin `b` lies outside `Tg`.
  have hbex : ((G.neighborFinset s₀ ∩ Iso).erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem
      (Finset.mem_inter.mpr ⟨has₀, haIso⟩), hSiso s₀ hs₀]
    omega
  obtain ⟨b, hb⟩ := hbex
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  rcases Finset.mem_inter.mp (Finset.mem_of_mem_erase hb) with ⟨hbs₀, hbIso⟩
  have hbTg : b ∉ Tg := by
    intro hmem
    have : b ∈ G.neighborFinset s₀ ∩ Tg := Finset.mem_inter.mpr ⟨hbs₀, hmem⟩
    have hsing : G.neighborFinset s₀ ∩ Tg = {a} := by
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hs₀share
      have hac : a ∈ ({c} : Finset (Fin 20)) := hc ▸ ha
      rw [Finset.mem_singleton] at hac
      rw [hc, hac]
    rw [hsing] at this
    exact hba (Finset.mem_singleton.mp this)
  -- `b` is a twin of the anchor.
  have hfb : b ∈ G.neighborFinset f := by
    have : b ∈ Iso \ Tg := Finset.mem_sdiff.mpr ⟨hbIso, hbTg⟩
    rw [← hfeq] at this
    exact (Finset.mem_inter.mp this).1
  -- The twin pair is exactly `{a, b}`.
  have hpair : G.neighborFinset s₀ ∩ Iso = {a, b} := by
    have hsub : ({a, b} : Finset (Fin 20)) ⊆ G.neighborFinset s₀ ∩ Iso := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact Finset.mem_inter.mpr ⟨has₀, haIso⟩
      · rw [Finset.mem_singleton] at ht
        rw [ht]
        exact Finset.mem_inter.mpr ⟨hbs₀, hbIso⟩
    have hc2 : ({a, b} : Finset (Fin 20)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hba.symm]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hSiso s₀ hs₀, hc2])).symm
  -- The trap: every other `s'` lands in a 4-element set.
  set U : Finset (Fin 20) :=
    (G.neighborFinset s₀ ∩ Hub) ∪ ((G.neighborFinset a ∩ Hub).erase g).erase s₀
      ∪ ((G.neighborFinset b ∩ Hub).erase f).erase s₀ with hUdef
  have hcover : S.erase s₀ ⊆ U := by
    intro s' hs'
    have hs'S : s' ∈ S := Finset.mem_of_mem_erase hs'
    have hs'ne : s' ≠ s₀ := Finset.ne_of_mem_erase hs'
    have hs'Hub : s' ∈ Hub := hS hs'S
    by_cases hadj : G.Adj s₀ s'
    · rw [hUdef]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset s₀ s').mpr hadj, hs'Hub⟩))))
    · -- `hno2hub` on `(s₀, s')`: one of the two twins is shared.
      have hkey : a ∈ G.neighborFinset s' ∨ b ∈ G.neighborFinset s' := by
        by_contra hcon
        push Not at hcon
        refine hno2hub ⟨s₀, s', hS hs₀, hs'Hub, hSdeg s₀ hs₀, hSdeg s' hs'S,
          fun he => hs'ne he.symm, hadj, ?_, ?_⟩
        · have hall : (G.neighborFinset s₀ ∩ Iso) \ G.neighborFinset s'
              = G.neighborFinset s₀ ∩ Iso := by
            rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
            intro t ht hts'
            rw [hpair] at ht
            rcases Finset.mem_insert.mp ht with rfl | ht
            · exact hcon.1 hts'
            · rw [Finset.mem_singleton] at ht
              rw [ht] at hts'
              exact hcon.2 hts'
          rw [hall, hSiso s₀ hs₀]
        · -- `s'` keeps both its twins private: it misses both `a` and `b`.
          have hall : (G.neighborFinset s' ∩ Iso) \ G.neighborFinset s₀
              = G.neighborFinset s' ∩ Iso := by
            rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
            intro t ht hts₀
            have : t ∈ G.neighborFinset s₀ ∩ Iso :=
              Finset.mem_inter.mpr ⟨hts₀, (Finset.mem_inter.mp ht).2⟩
            rw [hpair] at this
            rcases Finset.mem_insert.mp this with rfl | hmem
            · exact hcon.1 (Finset.mem_inter.mp ht).1
            · rw [Finset.mem_singleton] at hmem
              rw [hmem] at ht
              exact hcon.2 (Finset.mem_inter.mp ht).1
          rw [hall, hSiso s' hs'S]
      have hs'g : s' ≠ g := (hSg s' hs'S).2
      have hs'f : s' ≠ f := fun he => hfS (he ▸ hs'S)
      rcases hkey with hka | hkb
      · rw [hUdef]
        refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
        refine Finset.mem_erase.mpr ⟨hs'ne, Finset.mem_erase.mpr ⟨hs'g, ?_⟩⟩
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset a s').mpr ((G.mem_neighborFinset s' a).mp hka).symm,
            hs'Hub⟩
      · rw [hUdef]
        refine Finset.mem_union.mpr (Or.inr ?_)
        refine Finset.mem_erase.mpr ⟨hs'ne, Finset.mem_erase.mpr ⟨hs'f, ?_⟩⟩
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset b s').mpr ((G.mem_neighborFinset s' b).mp hkb).symm,
            hs'Hub⟩
  -- Cardinalities: the trap has at most four slots.
  have hUcard : U.card ≤ 4 := by
    have h1 : (G.neighborFinset s₀ ∩ Hub).card ≤ 2 := by
      have := nbr_split_three_twenty G Hub Iso hdisj s₀
      rw [hSiso s₀ hs₀, hSdeg s₀ hs₀] at this
      omega
    have h2 : (((G.neighborFinset a ∩ Hub).erase g).erase s₀).card ≤ 1 := by
      have hga : g ∈ G.neighborFinset a ∩ Hub := by
        refine Finset.mem_inter.mpr ⟨?_, hg⟩
        have : a ∈ G.neighborFinset g := (Finset.mem_inter.mp (hTgdef ▸ haTg)).1
        exact (G.mem_neighborFinset a g).mpr ((G.mem_neighborFinset g a).mp this).symm
      have hs₀a : s₀ ∈ (G.neighborFinset a ∩ Hub).erase g := by
        refine Finset.mem_erase.mpr ⟨(hSg s₀ hs₀).2, Finset.mem_inter.mpr ⟨?_, hS hs₀⟩⟩
        exact (G.mem_neighborFinset a s₀).mpr ((G.mem_neighborFinset s₀ a).mp has₀).symm
      have hca : (G.neighborFinset a ∩ Hub).card = 3 := hiso3 a haIso
      rw [Finset.card_erase_of_mem hs₀a, Finset.card_erase_of_mem hga, hca]
    have h3 : (((G.neighborFinset b ∩ Hub).erase f).erase s₀).card ≤ 1 := by
      have hfb' : f ∈ G.neighborFinset b ∩ Hub := by
        refine Finset.mem_inter.mpr ⟨?_, hf⟩
        exact (G.mem_neighborFinset b f).mpr ((G.mem_neighborFinset f b).mp hfb).symm
      have hs₀b : s₀ ∈ (G.neighborFinset b ∩ Hub).erase f := by
        refine Finset.mem_erase.mpr ⟨fun he => hfS (he ▸ hs₀), Finset.mem_inter.mpr
          ⟨?_, hS hs₀⟩⟩
        exact (G.mem_neighborFinset b s₀).mpr ((G.mem_neighborFinset s₀ b).mp hbs₀).symm
      have hcb : (G.neighborFinset b ∩ Hub).card = 3 := hiso3 b hbIso
      rw [Finset.card_erase_of_mem hs₀b, Finset.card_erase_of_mem hfb', hcb]
    calc U.card ≤ ((G.neighborFinset s₀ ∩ Hub) ∪
          ((G.neighborFinset a ∩ Hub).erase g).erase s₀).card
          + (((G.neighborFinset b ∩ Hub).erase f).erase s₀).card := by
          rw [hUdef]; exact Finset.card_union_le _ _
      _ ≤ (G.neighborFinset s₀ ∩ Hub).card
          + (((G.neighborFinset a ∩ Hub).erase g).erase s₀).card
          + (((G.neighborFinset b ∩ Hub).erase f).erase s₀).card := by
          have := Finset.card_union_le (G.neighborFinset s₀ ∩ Hub)
            (((G.neighborFinset a ∩ Hub).erase g).erase s₀)
          omega
      _ ≤ 4 := by omega
  -- Five hubs cannot fit into four slots.
  have hfive : (S.erase s₀).card = 5 := by
    rw [Finset.card_erase_of_mem hs₀, hScard]
  have := Finset.card_le_card hcover
  omega

end N20

end ACMax
