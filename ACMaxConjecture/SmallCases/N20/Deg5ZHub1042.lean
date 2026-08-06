import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.Deg5ZSlots
import ACMaxConjecture.SmallCases.N20.Deg5RichCap
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041ZHub

/-! # The good z-hub existence for the rich `(10,8,42)` Z-leaf extraction (`n = 20`)

The deg-5 corner profile `(|Hub|, |Iso|, Σ_Hub deg) = (10, 8, 42)`: eight degree-4 hubs, two
degree-5 hubs, iso-ledger `Σ_Hub isoDeg = 24`, `|Z| = 2`.  Given a rich degree-4 hub `g`
(`isoDeg g ≥ 3`), we extract a degree-4 hub `h₂` with `isoDeg h₂ ≥ 1` on an `M`-end `z`
avoided by `g`.  Unlike `n = 19` (one degree-5 hub), the two degree-5 hubs make the pure
ledger tie in two places; both ties are broken by the six-saturated-hubs anchor trap below. -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The six-saturated-hubs anchor kill over an `8`-twin layer.**  A rich degree-`4` hub `g`
with exactly three twins, an anchor `f` with at least four twins, and six degree-`4` hubs
avoiding `g`, each with exactly two twins, cannot coexist over an `8`-twin isolated layer:
the `3·3 = 9` twin–hub incidences of `Tg := N(g) ∩ Iso` pin exactly one shared twin per
saturated hub and none for `f`, so `f`'s `≥ 4` twins fill `Iso \ Tg` up to one slot and some
saturated `s₀` has its outer twin `b` adjacent to `f`; the `hno2hub` trap
`N(s₀) ∪ (N(a) \ {g, s₀}) ∪ (N(b) \ {f, s₀})` then offers only `2 + 1 + 1 = 4` slots for the
other five saturated hubs. -/
theorem six_saturated_anchor_kill_1042_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 8)
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
    have hzero : G.neighborFinset s ∩ Tg = ∅ := Finset.card_eq_zero.mp (by omega)
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
    have hsub1 : Tg ⊆ G.neighborFinset g ∩ Tg := by
      intro t ht
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hTgdef ▸ ht)).1, ht⟩
    have h2 : G.neighborFinset g ∩ Tg ⊆ Tg := Finset.inter_subset_right
    rw [Finset.Subset.antisymm h2 hsub1, hTgcard]
  -- The pigeonhole over `P := insert g S`.
  set P : Finset (Fin 20) := insert g S with hPdef
  have hPsub : P ⊆ Hub := by
    rw [hPdef]; exact Finset.insert_subset hg hS
  have hPsum : 9 ≤ ∑ h ∈ P, (G.neighborFinset h ∩ Tg).card := by
    rw [hPdef, Finset.sum_insert hgS, hgterm]
    have h6 : 6 ≤ ∑ s ∈ S, (G.neighborFinset s ∩ Tg).card := by
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
    have hthis := hsplit
    rw [hPdef, Finset.sum_insert hgS, hgterm] at hthis
    have h6 : 6 ≤ ∑ s ∈ S, (G.neighborFinset s ∩ Tg).card := by
      calc 6 = ∑ _s ∈ S, 1 := by rw [Finset.sum_const, hScard, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hshare1
    omega
  have hone : ∀ s ∈ S, (G.neighborFinset s ∩ Tg).card = 1 := by
    intro s hs
    by_contra hne
    have h2 : 2 ≤ (G.neighborFinset s ∩ Tg).card := by
      have := hshare1 s hs; omega
    have h7 : 7 ≤ ∑ s' ∈ S, (G.neighborFinset s' ∩ Tg).card := by
      rw [← Finset.add_sum_erase _ _ hs]
      have h5 : 5 ≤ ∑ s' ∈ S.erase s, (G.neighborFinset s' ∩ Tg).card := by
        calc 5 = ∑ _s' ∈ S.erase s, 1 := by
              rw [Finset.sum_const, Finset.card_erase_of_mem hs, hScard, smul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum (fun s' hs' =>
              hshare1 s' (Finset.mem_of_mem_erase hs'))
      omega
    omega
  -- Each `s ∈ S` has a twin pair `{a, b}` with `a ∈ Tg` and `b ∉ Tg`.
  have hpairs : ∀ s ∈ S, ∃ a b : Fin 20, a ∈ G.neighborFinset s ∩ Tg ∧
      b ∈ G.neighborFinset s ∩ Iso ∧ b ∉ Tg ∧ G.neighborFinset s ∩ Iso = {a, b} := by
    intro s hs
    obtain ⟨a, haeq⟩ := Finset.card_eq_one.mp (hone s hs)
    have ha : a ∈ G.neighborFinset s ∩ Tg := by
      rw [haeq]; exact Finset.mem_singleton_self a
    have haIso : a ∈ Iso := hTgsub (Finset.mem_inter.mp ha).2
    have haNs : a ∈ G.neighborFinset s ∩ Iso :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1, haIso⟩
    have herase : ((G.neighborFinset s ∩ Iso).erase a).card = 1 := by
      rw [Finset.card_erase_of_mem haNs, hSiso s hs]
    obtain ⟨b, hbeq⟩ := Finset.card_eq_one.mp herase
    have hb : b ∈ (G.neighborFinset s ∩ Iso).erase a := by
      rw [hbeq]; exact Finset.mem_singleton_self b
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbNs : b ∈ G.neighborFinset s ∩ Iso := Finset.mem_of_mem_erase hb
    have hbTg : b ∉ Tg := by
      intro hmem
      have hbin : b ∈ G.neighborFinset s ∩ Tg :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbNs).1, hmem⟩
      rw [haeq] at hbin
      exact hba (Finset.mem_singleton.mp hbin)
    refine ⟨a, b, ha, hbNs, hbTg, ?_⟩
    have hsub : ({a, b} : Finset (Fin 20)) ⊆ G.neighborFinset s ∩ Iso := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact haNs
      · rw [Finset.mem_singleton] at ht
        rw [ht]
        exact hbNs
    have hc2 : ({a, b} : Finset (Fin 20)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hba.symm]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hSiso s hs, hc2])).symm
  -- Some saturated hub has its outer twin adjacent to the anchor.
  have hsel : ∃ s₀ ∈ S, ∃ a b : Fin 20, a ∈ G.neighborFinset s₀ ∩ Tg ∧
      b ∈ G.neighborFinset s₀ ∩ Iso ∧ b ∉ Tg ∧ G.neighborFinset s₀ ∩ Iso = {a, b} ∧
      b ∈ G.neighborFinset f := by
    by_contra hcon
    push Not at hcon
    -- every outer twin lands in `(Iso \ Tg) \ N f`, a set of size `≤ 1` hosting `≤ 3` hubs.
    have hfzero' : G.neighborFinset f ∩ Tg = ∅ := Finset.card_eq_zero.mp hfzero
    have hVcard : ((Iso \ Tg) \ G.neighborFinset f).card ≤ 1 := by
      have hkey := Finset.card_sdiff_add_card_inter (Iso \ Tg) (G.neighborFinset f)
      have hIsoTg : (Iso \ Tg).card = 5 := by
        have := Finset.card_sdiff_add_card_eq_card hTgsub
        omega
      have hsub2 : G.neighborFinset f ∩ Iso ⊆ (Iso \ Tg) ∩ G.neighborFinset f := by
        intro t ht
        rcases Finset.mem_inter.mp ht with ⟨htf, hti⟩
        refine Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hti, fun htg => ?_⟩, htf⟩
        have hmem : t ∈ G.neighborFinset f ∩ Tg := Finset.mem_inter.mpr ⟨htf, htg⟩
        rw [hfzero'] at hmem
        exact Finset.notMem_empty t hmem
      have hint : 4 ≤ ((Iso \ Tg) ∩ G.neighborFinset f).card :=
        le_trans hfiso (Finset.card_le_card hsub2)
      omega
    have hVs : ∀ s ∈ S,
        1 ≤ (G.neighborFinset s ∩ ((Iso \ Tg) \ G.neighborFinset f)).card := by
      intro s hs
      obtain ⟨a, b, ha, hbNs, hbTg, hpaireq⟩ := hpairs s hs
      have hbnf : b ∉ G.neighborFinset f := hcon s hs a b ha hbNs hbTg hpaireq
      have hbmem : b ∈ G.neighborFinset s ∩ ((Iso \ Tg) \ G.neighborFinset f) :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbNs).1,
          Finset.mem_sdiff.mpr
            ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hbNs).2, hbTg⟩, hbnf⟩⟩
      exact Finset.card_pos.mpr ⟨b, hbmem⟩
    have hcnt := cross_count_twenty G S ((Iso \ Tg) \ G.neighborFinset f)
    have hup : ∑ w ∈ (Iso \ Tg) \ G.neighborFinset f, (G.neighborFinset w ∩ S).card
        ≤ 3 := by
      have hle := Finset.sum_le_card_nsmul ((Iso \ Tg) \ G.neighborFinset f)
        (fun w => (G.neighborFinset w ∩ S).card) 3 (fun w hw => by
          have hwIso : w ∈ Iso := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hw).1).1
          have hsub3 : G.neighborFinset w ∩ S ⊆ G.neighborFinset w ∩ Hub := fun x hx =>
            Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hS (Finset.mem_inter.mp hx).2⟩
          calc (G.neighborFinset w ∩ S).card ≤ (G.neighborFinset w ∩ Hub).card :=
                Finset.card_le_card hsub3
            _ = 3 := hiso3 w hwIso)
      rw [smul_eq_mul] at hle
      omega
    have hlow : 6 ≤ ∑ s ∈ S,
        (G.neighborFinset s ∩ ((Iso \ Tg) \ G.neighborFinset f)).card := by
      calc 6 = ∑ _s ∈ S, 1 := by rw [Finset.sum_const, hScard, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum hVs
    omega
  obtain ⟨s₀, hs₀, a, b, ha, hbNs, hbTg, hpair, hfb⟩ := hsel
  rcases Finset.mem_inter.mp ha with ⟨has₀, haTg⟩
  have haIso : a ∈ Iso := hTgsub haTg
  rcases Finset.mem_inter.mp hbNs with ⟨hbs₀, hbIso⟩
  have hba : b ≠ a := fun he => hbTg (he ▸ haTg)
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
        · have hall : (G.neighborFinset s' ∩ Iso) \ G.neighborFinset s₀
              = G.neighborFinset s' ∩ Iso := by
            rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
            intro t ht hts₀
            have hmem : t ∈ G.neighborFinset s₀ ∩ Iso :=
              Finset.mem_inter.mpr ⟨hts₀, (Finset.mem_inter.mp ht).2⟩
            rw [hpair] at hmem
            rcases Finset.mem_insert.mp hmem with rfl | hmem
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
        have hag : a ∈ G.neighborFinset g := (Finset.mem_inter.mp (hTgdef ▸ haTg)).1
        exact (G.mem_neighborFinset a g).mpr ((G.mem_neighborFinset g a).mp hag).symm
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

set_option maxHeartbeats 1000000 in
/-- With the rich hub `g` (`isoDeg ≥ 3`), the `(10,8,42)` ledger + the iso-cap produce a
degree-`4` `Z`-slot hub `h₂` of `isoDeg ≥ 1`, on a `z` avoided by `g` and non-adjacent to `g`.
Case A (`g` meets no `Z`-vertex) closes on the refined `(F, A, C)` partition of the four
`Z`-slot hubs (forced-`0`, `g`-adjacent-capped-`2`, degree-`5`); case B (`g` meets one `M`-end)
dispatches on the degrees of the avoided end's hub pair, the two ledger ties landing in the
six-saturated-hubs anchor kill. -/
theorem good_zhub_1042_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 8) (hdsum : ∑ w ∈ Hub, G.degree w = 42)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    ∃ h₂ z : Fin 20, h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.Adj z h₂ ∧ ¬G.Adj g z ∧ ¬G.Adj g h₂ ∧ g ≠ h₂ ∧
      1 ≤ (G.neighborFinset h₂ ∩ Iso).card := by
  classical
  -- Abbreviation for the `Z`-layer.
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- Degrees are `4` or `5`; the profile splits `10` hubs into `8` of degree `4` and two of `5`.
  have hpd : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := fun h hh => by
    have := hdeg h hh; have := hdeg5 h hh; omega
  set D4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 5) with hD5def
  have hmemD4 : ∀ w, w ∈ D4 ↔ w ∈ Hub ∧ G.degree w = 4 := fun w => by
    rw [hD4def]; exact Finset.mem_filter
  have hmemD5 : ∀ w, w ∈ D5 ↔ w ∈ Hub ∧ G.degree w = 5 := fun w => by
    rw [hD5def]; exact Finset.mem_filter
  have hcover : D4 ∪ D5 = Hub := by
    ext h; rw [Finset.mem_union, hmemD4, hmemD5]
    refine ⟨fun h' => h'.elim (·.1) (·.1), fun hh => ?_⟩
    rcases hpd h hh with h4 | h5
    · exact Or.inl ⟨hh, h4⟩
    · exact Or.inr ⟨hh, h5⟩
  have hdisj45 : Disjoint D4 D5 := by
    rw [Finset.disjoint_left]; intro h hd4 hd5
    rw [hmemD4] at hd4; rw [hmemD5] at hd5; omega
  have hcardsum : D4.card + D5.card = 10 := by
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
  have h42 : 4 * D4.card + 5 * D5.card = 42 := by rw [← hdegsum]; exact hdsum
  have hD4card : D4.card = 8 := by omega
  have hD5card : D5.card = 2 := by omega
  have hD4subHub : D4 ⊆ Hub := by rw [hD4def]; exact Finset.filter_subset _ _
  have hgD4 : g ∈ D4 := (hmemD4 g).mpr ⟨hg, hgd⟩
  -- The two degree-`5` hubs.
  obtain ⟨d₁, d₂, hd12ne, hD5eq⟩ := Finset.card_eq_two.mp hD5card
  -- The iso-incidence ledger: `∑_Hub isoDeg = 3·|Iso| = 24`, split over `D4 ⊔ D5`.
  have hledger : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 24 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  have hpart : ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card
      + ∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card = 24 := by
    rw [← Finset.sum_union hdisj45, hcover]; exact hledger
  have hD5le10 : ∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card ≤ 10 := by
    have hle := Finset.sum_le_card_nsmul D5 (fun x => (G.neighborFinset x ∩ Iso).card) 5
      (fun x hx => by
        have h5 : G.degree x = 5 := ((hmemD5 x).mp hx).2
        calc (G.neighborFinset x ∩ Iso).card ≤ (G.neighborFinset x).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = 5 := by rw [G.card_neighborFinset_eq_degree, h5])
    rw [hD5card] at hle
    simpa using hle
  -- The rich-hub iso-cap, packaged per hub.
  have hcap : ∀ h ∈ Hub, G.degree h = 4 → g ≠ h → ¬G.Adj g h →
      (G.neighborFinset h ∩ Iso).card ≤ 2 := fun h hh h4 hgh hnadj =>
    isoDeg_le_two_of_nonadj_rich_twenty G Hub Iso hshare hno2hub g h hg hh hgd h4 hgh hnadj hgiso
  -- The saturation bound, packaged.
  have hsat : (Hub.filter (fun h => G.degree h = 4 ∧ h ≠ g ∧ ¬G.Adj g h ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 * (G.neighborFinset g ∩ Iso).card :=
    sat_bound_rich_twenty G Hub Iso hisodeg3 hno2hub g hg hgd hgiso
  -- `g`'s three-way split.
  have hgsplit := nbr_split_three_twenty G Hub Iso hdisj g
  rw [← hZdef] at hgsplit
  -- The `Z`-skeleton.
  obtain ⟨z₁, z₂, hz12ne, hz₁Z, hz₂Z, hZeqpair, hadj12, hnob⟩ :=
    zslot_skeleton_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg5 hT
  rw [← hZdef] at hz₁Z hz₂Z
  by_contra hcon
  push Not at hcon
  -- The `g`-meets-`Z` (hard) case, reusable for either endpoint.
  have keyB : ∀ za zb : Fin 20, za ∈ Z → zb ∈ Z → G.Adj g za → ¬G.Adj g zb → False := by
    intro za zb hzaZ hzbZ hgza hgzb
    -- `g` meets `za`, so `zDeg g ≥ 1`, forcing `hubDeg g = 0`, `isoDeg g = 3`.
    have hza_in : za ∈ G.neighborFinset g ∩ Z :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hgza, hzaZ⟩
    have hzdeg_pos : 1 ≤ (G.neighborFinset g ∩ Z).card := Finset.card_pos.mpr ⟨za, hza_in⟩
    have hhubg0 : (G.neighborFinset g ∩ Hub).card = 0 := by
      have hgs := hgsplit; rw [hgd] at hgs; omega
    have hgiso3 : (G.neighborFinset g ∩ Iso).card = 3 := by
      have hgs := hgsplit; rw [hgd] at hgs; omega
    have hgnohub : ∀ h ∈ Hub, ¬G.Adj g h := by
      intro h hh hadj
      have hmem : h ∈ G.neighborFinset g ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh⟩
      rw [Finset.card_eq_zero.mp hhubg0] at hmem
      exact absurd hmem (Finset.notMem_empty h)
    -- Uniform cap on the degree-`4` hubs off `g`.
    have hD4cap : ∀ h ∈ D4, h ≠ g → (G.neighborFinset h ∩ Iso).card ≤ 2 := by
      intro h hh hne
      exact hcap h ((hmemD4 h).mp hh).1 ((hmemD4 h).mp hh).2 (Ne.symm hne)
        (hgnohub h ((hmemD4 h).mp hh).1)
    -- The anchor-kill applier.
    have applyAnchor : ∀ f : Fin 20, f ∈ Hub → 4 ≤ (G.neighborFinset f ∩ Iso).card →
        ∀ S : Finset (Fin 20), S ⊆ Hub → S.card = 6 → (∀ s ∈ S, G.degree s = 4) →
        (∀ s ∈ S, s ≠ g) → (∀ s ∈ S, (G.neighborFinset s ∩ Iso).card = 2) → False := by
      intro f hf hfiso S hSsub hScard hSdeg hSne hSiso
      exact six_saturated_anchor_kill_1042_twenty G Hub Iso hiso3 hdisj hIso hno2hub g f
        hg hgd hgiso3 hf hfiso S hSsub hScard hSdeg
        (fun s hs => ⟨hgnohub s (hSsub hs), hSne s hs⟩) hSiso
    -- The two hubs of the avoided `zb`.
    obtain ⟨_, hzb2, _⟩ :=
      zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak zb hzbZ
    obtain ⟨p, q, hpqne, hpqeq⟩ := Finset.card_eq_two.mp hzb2
    have hpmem : p ∈ G.neighborFinset zb ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_self _ _
    have hqmem : q ∈ G.neighborFinset zb ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_inter, G.mem_neighborFinset] at hpmem hqmem
    obtain ⟨hzbp, hpHub⟩ := hpmem
    obtain ⟨hzbq, hqHub⟩ := hqmem
    have hgp : ¬G.Adj g p := hgnohub p hpHub
    have hgq : ¬G.Adj g q := hgnohub q hqHub
    have hgpne : g ≠ p := by rintro rfl; exact hgzb hzbp.symm
    have hgqne : g ≠ q := by rintro rfl; exact hgzb hzbq.symm
    have hfp : G.degree p = 4 → (G.neighborFinset p ∩ Iso).card = 0 := fun h4 => by
      have := hcon p zb hpHub h4 hzbZ hzbp hgzb hgp hgpne; omega
    have hfq : G.degree q = 4 → (G.neighborFinset q ∩ Iso).card = 0 := fun h4 => by
      have := hcon q zb hqHub h4 hzbZ hzbq hgzb hgq hgqne; omega
    -- The anchored saturation kill: one avoided hub deg-`4` forced-`0`, the other deg-`5`.
    have satKill : ∀ p0 r : Fin 20, p0 ∈ Hub → G.degree p0 = 4 → g ≠ p0 →
        (G.neighborFinset p0 ∩ Iso).card = 0 → r ∈ Hub → G.degree r = 5 →
        G.Adj r zb → False := by
      intro p0 r hp0Hub hp0deg hgp0ne hp0iso0 hrHub hr5 hrzb
      have hp0D4 : p0 ∈ D4 := (hmemD4 p0).mpr ⟨hp0Hub, hp0deg⟩
      have hp0erase : p0 ∈ D4.erase g := Finset.mem_erase.mpr ⟨fun h => hgp0ne h.symm, hp0D4⟩
      have hsum_split : (G.neighborFinset g ∩ Iso).card + ((G.neighborFinset p0 ∩ Iso).card
          + ∑ h ∈ (D4.erase g).erase p0, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by
        have e1 := Finset.add_sum_erase D4 (fun x => (G.neighborFinset x ∩ Iso).card) hgD4
        have e2 := Finset.add_sum_erase (D4.erase g)
          (fun x => (G.neighborFinset x ∩ Iso).card) hp0erase
        omega
      have hsixcard : ((D4.erase g).erase p0).card = 6 := by
        rw [Finset.card_erase_of_mem hp0erase, Finset.card_erase_of_mem hgD4, hD4card]
      have hsixsub : (D4.erase g).erase p0 ⊆ D4 :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hsixne : ∀ h ∈ (D4.erase g).erase p0, h ≠ g := fun h hh =>
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hh)).1
      have hsixcap : ∀ h ∈ (D4.erase g).erase p0, (G.neighborFinset h ∩ Iso).card ≤ 2 :=
        fun h hh => hD4cap h (hsixsub hh) (hsixne h hh)
      have hsixle : ∑ h ∈ (D4.erase g).erase p0, (G.neighborFinset h ∩ Iso).card ≤ 12 := by
        have hle := Finset.sum_le_card_nsmul ((D4.erase g).erase p0)
          (fun x => (G.neighborFinset x ∩ Iso).card) 2 hsixcap
        rw [hsixcard] at hle
        simpa using hle
      -- The other degree-`5` hub is the anchor.
      have hrD5 : r ∈ D5 := (hmemD5 r).mpr ⟨hrHub, hr5⟩
      have hrd : r = d₁ ∨ r = d₂ := by
        have hx := hrD5; rw [hD5eq, Finset.mem_insert, Finset.mem_singleton] at hx; exact hx
      obtain ⟨r', hr'D5, hsumD5⟩ : ∃ r' : Fin 20, r' ∈ D5 ∧
          ∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card
            = (G.neighborFinset r ∩ Iso).card + (G.neighborFinset r' ∩ Iso).card := by
        rcases hrd with h1 | h2
        · refine ⟨d₂, ?_, ?_⟩
          · rw [hD5eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self d₂)
          · rw [hD5eq, Finset.sum_pair hd12ne, h1]
        · refine ⟨d₁, ?_, ?_⟩
          · rw [hD5eq]; exact Finset.mem_insert_self d₁ {d₂}
          · rw [hD5eq, Finset.sum_pair hd12ne, h2]
            omega
      have hr'Hub : r' ∈ Hub := ((hmemD5 r').mp hr'D5).1
      have hr'deg : G.degree r' = 5 := ((hmemD5 r').mp hr'D5).2
      have hr'le5 : (G.neighborFinset r' ∩ Iso).card ≤ 5 := by
        calc (G.neighborFinset r' ∩ Iso).card ≤ (G.neighborFinset r').card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = 5 := by rw [G.card_neighborFinset_eq_degree, hr'deg]
      have hrle4 : (G.neighborFinset r ∩ Iso).card ≤ 4 := by
        have hsp := nbr_split_three_twenty G Hub Iso hdisj r
        rw [← hZdef] at hsp
        have hzin : zb ∈ G.neighborFinset r ∩ Z :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hrzb, hzbZ⟩
        have hpos : 1 ≤ (G.neighborFinset r ∩ Z).card := Finset.card_pos.mpr ⟨zb, hzin⟩
        rw [hr5] at hsp; omega
      -- The exact ledger: `Σ_six = 12`, each member exactly `2`, `isoDeg r' = 5`.
      have hsix12 : ∑ h ∈ (D4.erase g).erase p0, (G.neighborFinset h ∩ Iso).card = 12 := by
        omega
      have hr'4 : 4 ≤ (G.neighborFinset r' ∩ Iso).card := by omega
      have hsix2 : ∀ h ∈ (D4.erase g).erase p0, (G.neighborFinset h ∩ Iso).card = 2 := by
        intro h₀ hh₀
        by_contra hne0
        have hlt : (G.neighborFinset h₀ ∩ Iso).card ≤ 1 := by
          have := hsixcap h₀ hh₀; omega
        have hsp := Finset.add_sum_erase ((D4.erase g).erase p0)
          (fun x => (G.neighborFinset x ∩ Iso).card) hh₀
        have hb : ∑ x ∈ ((D4.erase g).erase p0).erase h₀,
            (G.neighborFinset x ∩ Iso).card ≤ 10 := by
          have hle := Finset.sum_le_card_nsmul (((D4.erase g).erase p0).erase h₀)
            (fun x => (G.neighborFinset x ∩ Iso).card) 2
            (fun x hx => hsixcap x (Finset.mem_of_mem_erase hx))
          rw [Finset.card_erase_of_mem hh₀, hsixcard] at hle
          simpa using hle
        omega
      exact applyAnchor r' hr'Hub hr'4 ((D4.erase g).erase p0)
        (hsixsub.trans hD4subHub) hsixcard
        (fun h hh => ((hmemD4 h).mp (hsixsub hh)).2) hsixne hsix2
    -- Dispatch on the degrees of the two hubs of `zb`.
    rcases hpd p hpHub with hp4 | hp5
    · rcases hpd q hqHub with hq4 | hq5
      · -- Both degree `4`: both forced to `0`; the direct count gives `Σ_D4 ≤ 13 < 14`.
        have hpD4 : p ∈ D4 := (hmemD4 p).mpr ⟨hpHub, hp4⟩
        have hqD4 : q ∈ D4 := (hmemD4 q).mpr ⟨hqHub, hq4⟩
        have hperase : p ∈ D4.erase g := Finset.mem_erase.mpr ⟨fun h => hgpne h.symm, hpD4⟩
        have hqerase2 : q ∈ (D4.erase g).erase p := Finset.mem_erase.mpr
          ⟨hpqne.symm, Finset.mem_erase.mpr ⟨fun h => hgqne h.symm, hqD4⟩⟩
        have hsum6 : (G.neighborFinset g ∩ Iso).card + ((G.neighborFinset p ∩ Iso).card
            + ((G.neighborFinset q ∩ Iso).card
              + ∑ h ∈ ((D4.erase g).erase p).erase q, (G.neighborFinset h ∩ Iso).card))
            = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by
          have e1 := Finset.add_sum_erase D4 (fun x => (G.neighborFinset x ∩ Iso).card) hgD4
          have e2 := Finset.add_sum_erase (D4.erase g)
            (fun x => (G.neighborFinset x ∩ Iso).card) hperase
          have e3 := Finset.add_sum_erase ((D4.erase g).erase p)
            (fun x => (G.neighborFinset x ∩ Iso).card) hqerase2
          omega
        have hR5card : (((D4.erase g).erase p).erase q).card = 5 := by
          rw [Finset.card_erase_of_mem hqerase2, Finset.card_erase_of_mem hperase,
            Finset.card_erase_of_mem hgD4, hD4card]
        have hR5sub : ((D4.erase g).erase p).erase q ⊆ D4 :=
          ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans
            (Finset.erase_subset _ _)
        have hR5bound : ∑ h ∈ ((D4.erase g).erase p).erase q,
            (G.neighborFinset h ∩ Iso).card ≤ 10 := by
          have hle := Finset.sum_le_card_nsmul (((D4.erase g).erase p).erase q)
            (fun x => (G.neighborFinset x ∩ Iso).card) 2 (fun x hx => by
              have hxg : x ≠ g := (Finset.mem_erase.mp
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))).1
              exact hD4cap x (hR5sub hx) hxg)
          rw [hR5card] at hle
          simpa using hle
        have h0p := hfp hp4
        have h0q := hfq hq4
        omega
      · -- `q` degree `5`, `p` degree `4`: the anchored saturation kill on `(p, q)`.
        exact satKill p q hpHub hp4 hgpne (hfp hp4) hqHub hq5 hzbq.symm
    · rcases hpd q hqHub with hq4 | hq5
      · -- `p` degree `5`, `q` degree `4`: the anchored saturation kill on `(q, p)`.
        exact satKill q p hqHub hq4 hgqne (hfq hq4) hpHub hp5 hzbp.symm
      · -- Both hubs of the avoided `zb` are degree `5`: the anchor trap on the seven.
        have hpD5 : p ∈ D5 := (hmemD5 p).mpr ⟨hpHub, hp5⟩
        have hqD5 : q ∈ D5 := (hmemD5 q).mpr ⟨hqHub, hq5⟩
        have hD5pq : ({p, q} : Finset (Fin 20)) = D5 := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hpD5
            · rw [Finset.mem_singleton] at hx
              rw [hx]
              exact hqD5
          · rw [hD5card, Finset.card_pair hpqne]
        have hsumD5pq : ∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card
            = (G.neighborFinset p ∩ Iso).card + (G.neighborFinset q ∩ Iso).card := by
          rw [← hD5pq, Finset.sum_pair hpqne]
        have hple4 : (G.neighborFinset p ∩ Iso).card ≤ 4 := by
          have hsp := nbr_split_three_twenty G Hub Iso hdisj p
          rw [← hZdef] at hsp
          have hzin : zb ∈ G.neighborFinset p ∩ Z :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzbp.symm, hzbZ⟩
          have hpos : 1 ≤ (G.neighborFinset p ∩ Z).card := Finset.card_pos.mpr ⟨zb, hzin⟩
          rw [hp5] at hsp; omega
        have hqle4 : (G.neighborFinset q ∩ Iso).card ≤ 4 := by
          have hsp := nbr_split_three_twenty G Hub Iso hdisj q
          rw [← hZdef] at hsp
          have hzin : zb ∈ G.neighborFinset q ∩ Z :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzbq.symm, hzbZ⟩
          have hpos : 1 ≤ (G.neighborFinset q ∩ Z).card := Finset.card_pos.mpr ⟨zb, hzin⟩
          rw [hq5] at hsp; omega
        -- The seven degree-`4` hubs off `g` and their saturated part.
        have hsum7 : (G.neighborFinset g ∩ Iso).card
            + ∑ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card
            = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
          Finset.add_sum_erase D4 (fun x => (G.neighborFinset x ∩ Iso).card) hgD4
        have hsevencard : (D4.erase g).card = 7 := by
          rw [Finset.card_erase_of_mem hgD4, hD4card]
        set S7 : Finset (Fin 20) := (D4.erase g).filter
          (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hS7def
        set N7 : Finset (Fin 20) := (D4.erase g).filter
          (fun h => ¬2 ≤ (G.neighborFinset h ∩ Iso).card) with hN7def
        have hsplit7 : ∑ h ∈ S7, (G.neighborFinset h ∩ Iso).card
            + ∑ h ∈ N7, (G.neighborFinset h ∩ Iso).card
            = ∑ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card := by
          rw [hS7def, hN7def]
          exact Finset.sum_filter_add_sum_filter_not _ _ _
        have hcards7 : S7.card + N7.card = 7 := by
          rw [hS7def, hN7def, Finset.card_filter_add_card_filter_not]
          exact hsevencard
        have hS7le : ∑ h ∈ S7, (G.neighborFinset h ∩ Iso).card ≤ 2 * S7.card := by
          have hle := Finset.sum_le_card_nsmul S7
            (fun x => (G.neighborFinset x ∩ Iso).card) 2 (fun x hx => by
              have hx7 : x ∈ D4.erase g := by
                rw [hS7def] at hx; exact Finset.mem_of_mem_filter x hx
              exact hD4cap x (Finset.mem_of_mem_erase hx7) (Finset.mem_erase.mp hx7).1)
          rw [smul_eq_mul] at hle
          omega
        have hN7le : ∑ h ∈ N7, (G.neighborFinset h ∩ Iso).card ≤ N7.card := by
          have hle := Finset.sum_le_card_nsmul N7
            (fun x => (G.neighborFinset x ∩ Iso).card) 1 (fun x hx => by
              rw [hN7def, Finset.mem_filter] at hx
              omega)
          rw [smul_eq_mul, mul_one] at hle
          exact hle
        have hS7le6 : S7.card ≤ 6 := by
          have h1 : S7 ⊆ Hub.filter (fun h => G.degree h = 4 ∧ h ≠ g ∧ ¬G.Adj g h ∧
              2 ≤ (G.neighborFinset h ∩ Iso).card) := by
            intro h hh
            rw [hS7def, Finset.mem_filter] at hh
            obtain ⟨hh7, hh2⟩ := hh
            have hhD4 : h ∈ D4 := Finset.mem_of_mem_erase hh7
            have hhHub : h ∈ Hub := ((hmemD4 h).mp hhD4).1
            exact Finset.mem_filter.mpr ⟨hhHub, ((hmemD4 h).mp hhD4).2,
              (Finset.mem_erase.mp hh7).1, hgnohub h hhHub, hh2⟩
          have h2 := Finset.card_le_card h1
          rw [hgiso3] at hsat
          omega
        -- `|S7| = 6` and `isoDeg p = 4` are forced; each `S7`-member is exactly `2`.
        have hS7card6 : S7.card = 6 := by omega
        have hp4' : 4 ≤ (G.neighborFinset p ∩ Iso).card := by omega
        have hS7iso2 : ∀ s ∈ S7, (G.neighborFinset s ∩ Iso).card = 2 := by
          intro s hs
          rw [hS7def, Finset.mem_filter] at hs
          have hle2 := hD4cap s (Finset.mem_of_mem_erase hs.1) (Finset.mem_erase.mp hs.1).1
          omega
        have hS7sub : S7 ⊆ Hub := by
          intro h hh
          rw [hS7def, Finset.mem_filter] at hh
          exact hD4subHub (Finset.mem_of_mem_erase hh.1)
        have hS7deg : ∀ s ∈ S7, G.degree s = 4 := by
          intro s hs
          rw [hS7def, Finset.mem_filter] at hs
          exact ((hmemD4 s).mp (Finset.mem_of_mem_erase hs.1)).2
        have hS7ne : ∀ s ∈ S7, s ≠ g := by
          intro s hs
          rw [hS7def, Finset.mem_filter] at hs
          exact (Finset.mem_erase.mp hs.1).1
        exact applyAnchor p hpHub hp4' S7 hS7sub hS7card6 hS7deg hS7ne hS7iso2
  -- Dispatch on which `Z`-vertices `g` meets.
  by_cases hgz₁ : G.Adj g z₁
  · by_cases hgz₂ : G.Adj g z₂
    · exact hnob g hg ⟨hgz₁, hgz₂⟩
    · exact keyB z₁ z₂ hz₁Z hz₂Z hgz₁ hgz₂
  · by_cases hgz₂ : G.Adj g z₂
    · exact keyB z₂ z₁ hz₂Z hz₁Z hgz₂ hgz₁
    · -- CASE A: `g` meets no `Z`-vertex; the refined `(F, A, C)` ledger closes.
      have hzg0 : (G.neighborFinset g ∩ Z).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_inter, G.mem_neighborFinset] at hx
        have hxpair : x ∈ ({z₁, z₂} : Finset (Fin 20)) := by
          rw [← hZeqpair, ← hZdef]; exact hx.2
        rw [Finset.mem_insert, Finset.mem_singleton] at hxpair
        rcases hxpair with rfl | rfl
        · exact hgz₁ hx.1
        · exact hgz₂ hx.1
      have hisog : (G.neighborFinset g ∩ Hub).card + (G.neighborFinset g ∩ Iso).card = 4 := by
        have hgs := hgsplit; rw [hgd] at hgs; omega
      -- The four `Z`-slot hubs.
      obtain ⟨_, hz1hub2, _⟩ :=
        zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak z₁ hz₁Z
      obtain ⟨_, hz2hub2, _⟩ :=
        zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak z₂ hz₂Z
      set ZH : Finset (Fin 20) := (G.neighborFinset z₁ ∩ Hub) ∪ (G.neighborFinset z₂ ∩ Hub)
        with hZHdef
      have hZHdisj : Disjoint (G.neighborFinset z₁ ∩ Hub) (G.neighborFinset z₂ ∩ Hub) := by
        rw [Finset.disjoint_left]; intro h h1 h2
        rw [Finset.mem_inter, G.mem_neighborFinset] at h1 h2
        exact hnob h h1.2 ⟨h1.1.symm, h2.1.symm⟩
      have hZHcard : ZH.card = 4 := by
        rw [hZHdef, Finset.card_union_of_disjoint hZHdisj, hz1hub2, hz2hub2]
      have hZHsubHub : ZH ⊆ Hub := by
        rw [hZHdef]; intro h hh
        rcases Finset.mem_union.mp hh with h1 | h1 <;> exact (Finset.mem_inter.mp h1).2
      have hgnotZH : g ∉ ZH := by
        rw [hZHdef, Finset.mem_union]; rintro (h1 | h1) <;>
          rw [Finset.mem_inter, G.mem_neighborFinset] at h1
        · exact hgz₁ h1.1.symm
        · exact hgz₂ h1.1.symm
      have hZHz : ∀ h ∈ ZH, 1 ≤ (G.neighborFinset h ∩ Z).card := by
        intro h hh
        rw [hZHdef, Finset.mem_union] at hh
        rcases hh with h1 | h1 <;> rw [Finset.mem_inter, G.mem_neighborFinset] at h1
        · exact Finset.card_pos.mpr ⟨z₁, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr h1.1.symm, hz₁Z⟩⟩
        · exact Finset.card_pos.mpr ⟨z₂, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr h1.1.symm, hz₂Z⟩⟩
      have hZHadj : ∀ h ∈ ZH, G.Adj z₁ h ∨ G.Adj z₂ h := by
        intro h hh
        rw [hZHdef, Finset.mem_union] at hh
        rcases hh with h1 | h1 <;> rw [Finset.mem_inter, G.mem_neighborFinset] at h1
        · exact Or.inl h1.1
        · exact Or.inr h1.1
      -- The `(F, A, C)` partition of the `Z`-slot hubs.
      set F : Finset (Fin 20) := ZH.filter (fun h => G.degree h = 4 ∧ ¬G.Adj g h) with hFdef
      set A : Finset (Fin 20) := ZH.filter (fun h => G.degree h = 4 ∧ G.Adj g h) with hAdef
      set C : Finset (Fin 20) := ZH.filter (fun h => G.degree h = 5) with hCdef
      have hFsubD4 : F ⊆ D4 := by
        intro h hh; rw [hFdef, Finset.mem_filter] at hh
        exact (hmemD4 h).mpr ⟨hZHsubHub hh.1, hh.2.1⟩
      have hAsubD4 : A ⊆ D4 := by
        intro h hh; rw [hAdef, Finset.mem_filter] at hh
        exact (hmemD4 h).mpr ⟨hZHsubHub hh.1, hh.2.1⟩
      have hCsubD5 : C ⊆ D5 := by
        intro h hh; rw [hCdef, Finset.mem_filter] at hh
        exact (hmemD5 h).mpr ⟨hZHsubHub hh.1, hh.2⟩
      have hCle2 : C.card ≤ 2 := by
        have := Finset.card_le_card hCsubD5; omega
      have hFAC4 : 4 ≤ F.card + A.card + C.card := by
        have hZHcover : ZH ⊆ F ∪ A ∪ C := by
          intro h hh
          have hhHub : h ∈ Hub := hZHsubHub hh
          rcases hpd h hhHub with h4 | h5
          · by_cases hadj : G.Adj g h
            · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              rw [hAdef, Finset.mem_filter]; exact ⟨hh, h4, hadj⟩
            · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              rw [hFdef, Finset.mem_filter]; exact ⟨hh, h4, hadj⟩
          · refine Finset.mem_union_right _ ?_
            rw [hCdef, Finset.mem_filter]; exact ⟨hh, h5⟩
        have h1 := Finset.card_le_card hZHcover
        have h2 := Finset.card_union_le (F ∪ A) C
        have h3 := Finset.card_union_le F A
        omega
      -- The forced-`0` sum over `F` (the extraction's negation `hcon` fires on each).
      have hFsum0 : ∑ h ∈ F, (G.neighborFinset h ∩ Iso).card = 0 := by
        apply Finset.sum_eq_zero
        intro h hh
        rw [hFdef, Finset.mem_filter] at hh
        obtain ⟨hhZH, hh4, hhna⟩ := hh
        have hhHub : h ∈ Hub := hZHsubHub hhZH
        have hgh : g ≠ h := fun he => hgnotZH (he ▸ hhZH)
        rcases hZHadj h hhZH with hadj | hadj
        · have := hcon h z₁ hhHub hh4 hz₁Z hadj hgz₁ hhna hgh; omega
        · have := hcon h z₂ hhHub hh4 hz₂Z hadj hgz₂ hhna hgh; omega
      -- The `A`-hubs lose an iso-slot to `g` and one to their `M`-end: `isoDeg ≤ 2`.
      have hAsum : ∑ h ∈ A, (G.neighborFinset h ∩ Iso).card ≤ 2 * A.card := by
        have hle := Finset.sum_le_card_nsmul A (fun x => (G.neighborFinset x ∩ Iso).card) 2
          (fun x hx => by
            rw [hAdef, Finset.mem_filter] at hx
            obtain ⟨hxZH, hx4, hxadj⟩ := hx
            have hsp := nbr_split_three_twenty G Hub Iso hdisj x
            rw [← hZdef] at hsp
            have hz1' := hZHz x hxZH
            have hgin : g ∈ G.neighborFinset x ∩ Hub :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxadj.symm, hg⟩
            have hpos : 1 ≤ (G.neighborFinset x ∩ Hub).card := Finset.card_pos.mpr ⟨g, hgin⟩
            rw [hx4] at hsp; omega)
        rw [smul_eq_mul] at hle
        omega
      -- The `D5` ledger with the `Z`-adjacency loss.
      have hCeq : C = D5.filter (fun h => h ∈ ZH) := by
        ext h
        rw [hCdef, Finset.mem_filter, Finset.mem_filter]
        constructor
        · rintro ⟨hZH', h5⟩
          exact ⟨(hmemD5 h).mpr ⟨hZHsubHub hZH', h5⟩, hZH'⟩
        · rintro ⟨hD5', hZH'⟩
          exact ⟨hZH', ((hmemD5 h).mp hD5').2⟩
      have hD5C : ∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card + C.card ≤ 10 := by
        have hpt : ∀ h ∈ D5, (G.neighborFinset h ∩ Iso).card
            + (if h ∈ ZH then 1 else 0) ≤ 5 := by
          intro h hh
          have hd5h : G.degree h = 5 := ((hmemD5 h).mp hh).2
          by_cases hzh : h ∈ ZH
          · rw [if_pos hzh]
            have hsp := nbr_split_three_twenty G Hub Iso hdisj h
            rw [← hZdef] at hsp
            have hz1' := hZHz h hzh
            rw [hd5h] at hsp; omega
          · rw [if_neg hzh]
            have hle : (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
              Finset.card_le_card Finset.inter_subset_left
            rw [G.card_neighborFinset_eq_degree, hd5h] at hle
            omega
        have hsum := Finset.sum_le_sum hpt
        rw [Finset.sum_add_distrib] at hsum
        have hite : ∑ h ∈ D5, (if h ∈ ZH then 1 else 0) = C.card := by
          rw [Finset.sum_boole, hCeq]
          simp
        rw [hite] at hsum
        have hconst : ∑ _h ∈ D5, 5 = 10 := by rw [Finset.sum_const, hD5card, smul_eq_mul]
        omega
      -- The residual sum decomposition.
      have hFA_sub : A ⊆ D4 \ F := by
        intro h hh
        refine Finset.mem_sdiff.mpr ⟨hAsubD4 hh, fun hhF => ?_⟩
        rw [hAdef, Finset.mem_filter] at hh
        rw [hFdef, Finset.mem_filter] at hhF
        exact hhF.2.2 hh.2.2
      have hgDFA : g ∈ (D4 \ F) \ A := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hgD4, fun hgF => ?_⟩,
          fun hgA => ?_⟩
        · rw [hFdef] at hgF
          exact hgnotZH (Finset.mem_filter.mp hgF).1
        · rw [hAdef] at hgA
          exact hgnotZH (Finset.mem_filter.mp hgA).1
      have e1 : ∑ h ∈ D4 \ F, (G.neighborFinset h ∩ Iso).card
          + ∑ h ∈ F, (G.neighborFinset h ∩ Iso).card
          = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
        Finset.sum_sdiff hFsubD4
      have e2 : ∑ h ∈ (D4 \ F) \ A, (G.neighborFinset h ∩ Iso).card
          + ∑ h ∈ A, (G.neighborFinset h ∩ Iso).card
          = ∑ h ∈ D4 \ F, (G.neighborFinset h ∩ Iso).card :=
        Finset.sum_sdiff hFA_sub
      have e3 : (G.neighborFinset g ∩ Iso).card
          + ∑ h ∈ ((D4 \ F) \ A).erase g, (G.neighborFinset h ∩ Iso).card
          = ∑ h ∈ (D4 \ F) \ A, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase ((D4 \ F) \ A)
          (fun h => (G.neighborFinset h ∩ Iso).card) hgDFA
      have c1 : (D4 \ F).card + F.card = 8 := by
        rw [Finset.card_sdiff_add_card_eq_card hFsubD4, hD4card]
      have c2 : ((D4 \ F) \ A).card + A.card = (D4 \ F).card :=
        Finset.card_sdiff_add_card_eq_card hFA_sub
      have c3 : (((D4 \ F) \ A).erase g).card + 1 = ((D4 \ F) \ A).card :=
        Finset.card_erase_add_one hgDFA
      -- Split the residual by `g`-adjacency: the non-adjacent are capped by the iso-cap,
      -- the adjacent (at most `hubDeg g − |A|` of them) by the degree split.
      have hRsplit := Finset.sum_filter_add_sum_filter_not (((D4 \ F) \ A).erase g)
        (fun h => G.Adj g h) (fun h => (G.neighborFinset h ∩ Iso).card)
      have hRcards : ((((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h)).card
          + ((((D4 \ F) \ A).erase g).filter (fun h => ¬G.Adj g h)).card
          = (((D4 \ F) \ A).erase g).card :=
        Finset.card_filter_add_card_filter_not _
      have hmemR : ∀ h ∈ ((D4 \ F) \ A).erase g, h ∈ Hub ∧ G.degree h = 4 ∧ h ≠ g := by
        intro h hh
        have hhD4 : h ∈ D4 :=
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hh)).1).1
        exact ⟨((hmemD4 h).mp hhD4).1, ((hmemD4 h).mp hhD4).2, (Finset.mem_erase.mp hh).1⟩
      have hRadj : ∑ h ∈ (((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h),
          (G.neighborFinset h ∩ Iso).card
          ≤ 3 * ((((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h)).card := by
        have hle := Finset.sum_le_card_nsmul
          ((((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h))
          (fun x => (G.neighborFinset x ∩ Iso).card) 3 (fun x hx => by
            obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
            obtain ⟨hxHub, hx4, _⟩ := hmemR x hx1
            have hsp := nbr_split_three_twenty G Hub Iso hdisj x
            have hgin : g ∈ G.neighborFinset x ∩ Hub :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hx2.symm, hg⟩
            have hpos : 1 ≤ (G.neighborFinset x ∩ Hub).card := Finset.card_pos.mpr ⟨g, hgin⟩
            rw [hx4] at hsp; omega)
        rw [smul_eq_mul] at hle
        omega
      have hRnon : ∑ h ∈ (((D4 \ F) \ A).erase g).filter (fun h => ¬G.Adj g h),
          (G.neighborFinset h ∩ Iso).card
          ≤ 2 * ((((D4 \ F) \ A).erase g).filter (fun h => ¬G.Adj g h)).card := by
        have hle := Finset.sum_le_card_nsmul
          ((((D4 \ F) \ A).erase g).filter (fun h => ¬G.Adj g h))
          (fun x => (G.neighborFinset x ∩ Iso).card) 2 (fun x hx => by
            obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
            obtain ⟨hxHub, hx4, hxg⟩ := hmemR x hx1
            exact hcap x hxHub hx4 (Ne.symm hxg) hx2)
        rw [smul_eq_mul] at hle
        omega
      -- The `g`-adjacency budget: `A` and the adjacent residual both live in `N(g) ∩ Hub`.
      have hAadj : A.card + ((((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h)).card
          ≤ (G.neighborFinset g ∩ Hub).card := by
        have hdisjAR : Disjoint A
            ((((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h)) := by
          rw [Finset.disjoint_left]
          intro x hxA hxR
          have hx1 := (Finset.mem_filter.mp hxR).1
          exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx1)).2 hxA
        have hsubU : A ∪ (((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h)
            ⊆ G.neighborFinset g ∩ Hub := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rw [hAdef, Finset.mem_filter] at hx
            exact Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset _ _).mpr hx.2.2, hZHsubHub hx.1⟩
          · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
            exact Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset _ _).mpr hx2, (hmemR x hx1).1⟩
        calc A.card + ((((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h)).card
            = (A ∪ (((D4 \ F) \ A).erase g).filter (fun h => G.Adj g h)).card :=
              (Finset.card_union_of_disjoint hdisjAR).symm
          _ ≤ (G.neighborFinset g ∩ Hub).card := Finset.card_le_card hsubU
      omega

end N20

end ACMax
