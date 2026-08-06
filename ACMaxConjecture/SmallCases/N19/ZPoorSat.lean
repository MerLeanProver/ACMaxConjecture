import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct
import ACMaxConjecture.SmallCases.N19.RichCount
import ACMaxConjecture.SmallCases.N19.Align8Helpers
import ACMaxConjecture.SmallCases.N19.ZPoorN3
import ACMaxConjecture.SmallCases.N19.ZPoorR7
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.ZPoorCut

/-!
# The `r = 7`, `S = 15` saturation chain closing the main residual (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (11, 6)` profile with seven rich hubs
and rich iso-incidence sum `S = 15`, the poor incidences concentrate as `(3,3,3,3,3,0)`
(`poor_incidence_concentrates_nineteen`).  This file carries the saturation chain that turns that
design into the good `C₄` kill.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **The ordered adjacent off-diagonal count equals the within-set degree sum.** -/
theorem dadj_eq_sum_nineteen (G : SimpleGraph (Fin 19)) (R : Finset (Fin 19)) :
    (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card
      = ∑ a ∈ R, (G.neighborFinset a ∩ R).card := by
  classical
  set Dadj : Finset (Fin 19 × Fin 19) := R.offDiag.filter (fun p => G.Adj p.1 p.2) with hDdef
  have hmaps : (Dadj : Set (Fin 19 × Fin 19)).MapsTo Prod.fst R := by
    intro p hp
    rw [hDdef, Finset.coe_filter] at hp
    have hpoff : p ∈ R.offDiag := hp.1
    rw [Finset.mem_offDiag] at hpoff
    exact hpoff.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    rw [Finset.mem_filter, hDdef, Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨⟨_, hp2R, _⟩, hadj⟩, hfst⟩ := hp
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨hfst ▸ hadj, hp2R⟩
  · intro p hp q hq hpq
    rw [Finset.mem_filter, hDdef, Finset.mem_filter] at hp hq
    have hp1 : p.1 = a := hp.2
    have hq1 : q.1 = a := hq.2
    exact Prod.ext (hp1.trans hq1.symm) hpq
  · intro b hb
    rw [Finset.mem_inter, G.mem_neighborFinset] at hb
    refine ⟨(a, b), ?_, rfl⟩
    rw [Finset.mem_filter, hDdef, Finset.mem_filter, Finset.mem_offDiag]
    have hne : a ≠ b := fun he => G.irrefl (he ▸ hb.1)
    exact ⟨⟨⟨ha, hb.2, hne⟩, hb.1⟩, rfl⟩

/-- **The non-adjacent rich off-diagonal lies in the twins' traces** (share-`1`). -/
theorem rich_nonadj_biUnion_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso R : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card) :
    (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2))
      ⊆ Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) := by
  classical
  intro p hp
  rw [Finset.mem_filter, Finset.mem_offDiag] at hp
  obtain ⟨⟨hp1R, hp2R, hne⟩, hnadj⟩ := hp
  have hp1Hub := hRHub hp1R
  have hp2Hub := hRHub hp2R
  have hsh1 := rich_nonadj_share_eq_one_nineteen G Hub Iso hshare hno2hub p.1 p.2 hp1Hub hp2Hub
    (hdeg4 p.1 hp1Hub) (hdeg4 p.2 hp2Hub) hne hnadj (hRrich p.1 hp1R) (hRrich p.2 hp2R)
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (by rw [hsh1]; norm_num)
  rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
  obtain ⟨⟨ht1, ht2⟩, htIso⟩ := ht
  rw [Finset.mem_biUnion]
  refine ⟨t, htIso, ?_⟩
  rw [Finset.mem_offDiag]
  refine ⟨?_, ?_, hne⟩
  · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht1.symm, hp1R⟩
  · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht2.symm, hp2R⟩

/-- **NODE 3 — the `M`-partner kill (`r = 7`, `S = 15`).**  An `M`-edge endpoint `z` meeting two
poor hubs `hg₁, hg₂` (residual regime `hres`).  Saturation (NODE 2) forces the `M`-partner `z'` to
meet exactly the iso-degree-`3` rich hub `w` and the third poor hub `g₃ = N(t₆) ∖ {hg₁, hg₂}`; the
three poor hubs form a triangle, and `hg₁ – g₃ – z' – z` is a good `C₄` of degree sum
`4 + 4 + 3 + 3 = 14`, excluded by `hC4`. -/
theorem mpartner_meets_poor_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (_hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (_hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 19) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hg1 : Fin 19) (hg2 : Fin 19) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (_hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr7 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7)
    (hS15 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 15) :
    False := by
  -- **The reusable `Z`-leaf pigeonhole cut (BYPASSES the n = 18 saturation-counting kill).**
  -- The poor side `P = Hub \ R` has `|P| = 11 − 7 = 4` hubs carrying iso-incidence `18 − 15 = 3`;
  -- since each poor hub has iso-degree `≤ 1`, `hg1, hg2` (the two poor hubs `z` meets) cannot BOTH be
  -- iso-degree-`0` (the other two poor hubs absorb at most `2 < 3`).  So one of `hg1, hg2` has a
  -- private twin `c*`; with `zz = z` (whose two hub-neighbours `{hg1, hg2}` are both poor) the
  -- `r = 7` rich pool (`|R| ≥ 5`) admits the `Z`-leaf cut `two_poor_zleaf_pigeonhole_nineteen`,
  -- contradicting `hnocut`.  No `C₄`/saturation/`M`-partner argument is needed.
  classical
  apply hnocut
  refine Or.inl ?_
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsub : R ⊆ Hub := Finset.filter_subset _ _
  set P : Finset (Fin 19) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  -- `|P| = 4` and `∑_P iso = 3`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hPcard : P.card = 4 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub, hr7] at this; omega
  have hPsum : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 3 := by
    have hsp : (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
      rw [hRdef, hPdef, Finset.sum_filter_add_sum_filter_not Hub _]; exact hsum18
    rw [hS15] at hsp; omega
  have hPle1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg; rw [hPdef, Finset.mem_filter] at hg; omega
  -- Hub memberships and poorness of `hg1, hg2`.
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg1P : hg1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg1Hub, by omega⟩
  have hg2P : hg2 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg2Hub, by omega⟩
  have hg1notR : hg1 ∉ R := by rw [hRdef, Finset.mem_filter]; rintro ⟨_, h2⟩; omega
  have hg2notR : hg2 ∉ R := by rw [hRdef, Finset.mem_filter]; rintro ⟨_, h2⟩; omega
  -- `N(z) ∩ Hub = {hg1, hg2}` (both poor).
  obtain ⟨_, hzhub2, _⟩ :=
    z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hz
  have hNz : G.neighborFinset z ∩ Hub = {hg1, hg2} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hg1mem
      · exact hg2mem
    · rw [hzhub2, Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton]
  have hzpoor : ∀ h ∈ G.neighborFinset z ∩ Hub, h ∉ R := by
    intro h hh; rw [hNz, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact hg1notR
    · exact hg2notR
  -- One of `hg1, hg2` has iso-degree `1` (not both `0`).
  have hone : 1 ≤ (G.neighborFinset hg1 ∩ Iso).card ∨ 1 ≤ (G.neighborFinset hg2 ∩ Iso).card := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1z, h2z⟩ := hcon
    -- `∑_P = iso(hg1) + iso(hg2) + ∑_{rest} ≤ 0 + 0 + 2 = 2 < 3`.
    have he1 := Finset.add_sum_erase P (fun g => (G.neighborFinset g ∩ Iso).card) hg1P
    have hg2er : hg2 ∈ P.erase hg1 := Finset.mem_erase.mpr ⟨(Ne.symm hg1ne), hg2P⟩
    have he2 := Finset.add_sum_erase (P.erase hg1)
      (fun g => (G.neighborFinset g ∩ Iso).card) hg2er
    have hrestle : ∑ g ∈ (P.erase hg1).erase hg2, (G.neighborFinset g ∩ Iso).card ≤ 2 := by
      have hcardE : ((P.erase hg1).erase hg2).card = 2 := by
        rw [Finset.card_erase_of_mem hg2er, Finset.card_erase_of_mem hg1P, hPcard]
      calc ∑ g ∈ (P.erase hg1).erase hg2, (G.neighborFinset g ∩ Iso).card
          ≤ ∑ _g ∈ (P.erase hg1).erase hg2, 1 :=
            Finset.sum_le_sum (fun g hg => hPle1 g
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg)))
        _ = 2 := by rw [Finset.sum_const, hcardE, smul_eq_mul, mul_one]
    rw [hPsum] at he1; omega
  -- Pick the `z`-side poor hub `gstar` with a twin and run the engine.
  have hpoorle1 : (G.neighborFinset hg1 ∩ Iso).card ≤ 1 := hg1poor
  have hpoorle2 : (G.neighborFinset hg2 ∩ Iso).card ≤ 1 := hg2poor
  rcases hone with h1 | h2
  · have h1eq : (G.neighborFinset hg1 ∩ Iso).card = 1 := by omega
    obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp h1eq
    exact two_poor_zleaf_pigeonhole_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak R hRdef hg1 z cstar hg1Hub hz
      ((G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1) hcs hzpoor (by omega)
  · have h2eq : (G.neighborFinset hg2 ∩ Iso).card = 1 := by omega
    obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp h2eq
    exact two_poor_zleaf_pigeonhole_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak R hRdef hg2 z cstar hg2Hub hz
      ((G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1) hcs hzpoor (by omega)

end N19

end ACMax
