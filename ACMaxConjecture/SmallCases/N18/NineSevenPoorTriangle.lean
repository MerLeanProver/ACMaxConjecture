import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichZdeg
import ACMaxConjecture.SmallCases.N18.NineSevenForce
import ACMaxConjecture.SmallCases.N18.NineSevenEdge

/-!
# The poor-hub triangle closing the `(9, 7, 37)` rich-absorber residual (`n = 18`)

The mass squeeze pins the surviving `(9, 7, 37)` no-two-hub configuration to `isoDeg(d) = 5`,
`s := |S| = 6`, `M := ∑_{a∈S}|N(a)∩Iso| = 14` (`S` the rich degree-`4` hubs, `d` the lone degree-`5`
hub).  This file closes the residual *without* a share-`3` case split: the off-diagonal trace
inequality, already squeezed to equality, forces every rich hub to have **no** neighbour among the
two `M`-edge endpoints `Z = univ \ (Hub ∪ Iso)` (`ninesev_rich_no_z_neighbor`).  Since `d` is also
non-adjacent to `Z` (`ninesev_rich_isolated_from_d`), the four hub–`Z` incidences land entirely on
the two *poor* degree-`4` hubs, so each poor hub is adjacent to **both** `M`-ends, giving the good
triangle `{poor, z₁, z₂}` (`Σ = 4 + 3 + 3 = 10`) excluded by `hT`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Each `M`-edge endpoint meets exactly two hubs and no twin (`deg z = 3`), `(9, 7)` regime.**
The two `M`-edge endpoints `Z = univ \ (Hub ∪ Iso)` (`|Z| = 18 − 16 = 2`) meet no `M`-isolated twin
(a twin's neighbourhood lies in `Hub`) and at most one other `Z`-vertex, so each meets `≥ 2` hubs.
The leak bound caps the hub–`Z` incidence sum at `4`, and cross-counting forces exactly `2` hubs per
`Z`-vertex (degree `3`). -/
theorem ninesev_z_structure (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 9) (hIso : Iso.card = 7)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4) :
    ∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)),
      (G.neighborFinset z ∩ Iso).card = 0 ∧ (G.neighborFinset z ∩ Hub).card = 2 ∧
        G.degree z = 3 := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZcard : Z.card = 2 := by
    have hHIcard : (Hub ∪ Iso).card = 16 := by
      rw [Finset.card_union_of_disjoint hdisj, hHub, hIso]
    have hZeq : Z = (Hub ∪ Iso)ᶜ := by
      rw [hZdef]; ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
    rw [hZeq, Finset.card_compl, Fintype.card_fin, hHIcard]
  -- A twin's neighbourhood lies entirely in `Hub`.
  have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
    intro t ht
    have hcard3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
    have hdt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard3, hdt])
    rw [← heq]; exact Finset.inter_subset_right
  have hiso0 : ∀ z ∈ Z, (G.neighborFinset z ∩ Iso).card = 0 := by
    intro z hz
    rw [Finset.card_eq_zero]
    ext x; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hxz hxi
    have hzx : z ∈ G.neighborFinset x := by
      rw [G.mem_neighborFinset, SimpleGraph.adj_comm]; exact (G.mem_neighborFinset _ _).mp hxz
    have hzHub := htwinHub x hxi hzx
    have hznotHub : z ∉ Hub := by
      rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
    exact hznotHub hzHub
  have hzZle : ∀ z ∈ Z, (G.neighborFinset z ∩ Z).card ≤ 1 := by
    intro z hz
    have hsub : G.neighborFinset z ∩ Z ⊆ Z.erase z := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hz, hZcard] at this; omega
  have hpart : ∀ v : Fin 18, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
      + (G.neighborFinset v ∩ Z).card = G.degree v := fun v =>
    nbr_split_three_eighteen G Hub Iso hdisj v
  have hzhub : ∀ z ∈ Z, 2 ≤ (G.neighborFinset z ∩ Hub).card := by
    intro z hz
    have h0 := hiso0 z hz
    have hZle := hzZle z hz
    have hsp := hpart z
    have hd := hdeg3 z
    omega
  -- The hub–`Z` incidence sum is exactly `4` (cross-counted onto `Z`, leak caps at `4`).
  have hcross : ∑ z ∈ Z, (G.neighborFinset z ∩ Hub).card
      = ∑ h ∈ Hub, (G.neighborFinset h ∩ Z).card := cross_count G Z Hub
  have hge : 4 ≤ ∑ z ∈ Z, (G.neighborFinset z ∩ Hub).card := by
    calc (4 : ℕ) = ∑ _z ∈ Z, 2 := by rw [Finset.sum_const, hZcard, smul_eq_mul]
      _ ≤ ∑ z ∈ Z, (G.neighborFinset z ∩ Hub).card := Finset.sum_le_sum hzhub
  have hsum4 : ∑ z ∈ Z, (G.neighborFinset z ∩ Hub).card = 4 := by
    rw [hcross] at hge ⊢; omega
  intro z hz
  have hhub2 : (G.neighborFinset z ∩ Hub).card = 2 := by
    have hge2 := hzhub z hz
    have hae := Finset.add_sum_erase Z (fun w => (G.neighborFinset w ∩ Hub).card) hz
    have heraseGe : 2 ≤ ∑ w ∈ Z.erase z, (G.neighborFinset w ∩ Hub).card := by
      have hcardE : (Z.erase z).card = 1 := by rw [Finset.card_erase_of_mem hz, hZcard]
      calc (2 : ℕ) = ∑ _w ∈ Z.erase z, 2 := by
            rw [Finset.sum_const, hcardE, smul_eq_mul, one_mul]
        _ ≤ ∑ w ∈ Z.erase z, (G.neighborFinset w ∩ Hub).card :=
            Finset.sum_le_sum (fun w hw => hzhub w (Finset.mem_of_mem_erase hw))
    rw [hsum4] at hae
    omega
  have h0 := hiso0 z hz
  have hZle := hzZle z hz
  have hsp := hpart z
  have hd := hdeg3 z
  exact ⟨h0, hhub2, by omega⟩

/-- **Rich hubs have no `M`-end neighbour at the pinned boundary.**  At `s = |S| = 6`, `M = 14` and
`n₃ ≤ 2` the off-diagonal trace of `S` is squeezed: `30 = |offDiag S| = D + Dadj`, the non-adjacent
pairs `D ≤ ∑_t(m_t² − m_t) ≤ M + 3·n₃ ≤ 20`, so the adjacent ordered pairs `Dadj ≥ 10`.  But
`Dadj ≤ ∑_{a∈S}|N(a)∩S| ≤ ∑_{a∈S}|N(a)∩Hub| = 24 − M − (rich `Z`-mass) = 10 − (rich `Z`-mass)`,
forcing the rich `Z`-mass to `0`; hence every rich hub is non-adjacent to both `M`-ends. -/
theorem ninesev_rich_no_z_neighbor (G : SimpleGraph (Fin 18)) (Hub Iso S : Finset (Fin 18))
    (hSsub : S ⊆ Hub) (hSdeg4 : ∀ a ∈ S, G.degree a = 4)
    (hSrich : ∀ a ∈ S, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hdisj : Disjoint Hub Iso)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hs6 : S.card = 6)
    (hM14 : ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card = 14)
    (hn3 : (Iso.filter (fun t => (G.neighborFinset t ∩ S).card = 3)).card ≤ 2) :
    ∀ a ∈ S, (G.neighborFinset a ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by
  classical
  -- Each twin meets at most three rich hubs.
  have hmt3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ S).card ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsub)
      _ = 3 := hiso3 t ht
  -- `∑_t m_t = M = 14`.
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card = 14 := by
    rw [cross_count G Iso S]; exact hM14
  -- Off-diagonal split of `S`.
  set Off : Finset (Fin 18 × Fin 18) := S.offDiag with hOffdef
  have hOffcard : Off.card = 30 := by rw [hOffdef, Finset.offDiag_card, hs6]
  set Dadj : Finset (Fin 18 × Fin 18) := Off.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  set D : Finset (Fin 18 × Fin 18) := Off.filter (fun p => ¬G.Adj p.1 p.2) with hDdef
  have hDsplit : D.card + Dadj.card = Off.card := by
    rw [hDdef, hDadjdef, add_comm]; exact Finset.card_filter_add_card_filter_not _
  -- `Dadj ≤ ∑_{a∈S}|N(a)∩S|`.
  have hDadjle : Dadj.card ≤ ∑ a ∈ S, (G.neighborFinset a ∩ S).card := by
    have hmaps : (Dadj : Set (Fin 18 × Fin 18)).MapsTo Prod.fst S := by
      intro p hp
      rw [hDadjdef, Finset.coe_filter] at hp
      have hpoff : p ∈ Off := hp.1
      rw [hOffdef, Finset.mem_offDiag] at hpoff
      exact hpoff.1
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_le_sum
    intro a _
    have hsub : Dadj.filter (fun p => p.1 = a) ⊆ (G.neighborFinset a ∩ S).map
        ⟨fun b => (a, b), fun b₁ b₂ h => by simpa using h⟩ := by
      intro p hp
      rw [Finset.mem_filter, hDadjdef, Finset.mem_filter, hOffdef, Finset.mem_offDiag] at hp
      obtain ⟨⟨⟨_, hp2S, _⟩, hadj⟩, hfst⟩ := hp
      rw [Finset.mem_map]
      refine ⟨p.2, ?_, ?_⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hfst ▸ hadj, hp2S⟩
      · rw [← hfst]
        exact Prod.eta p
    calc (Dadj.filter (fun p => p.1 = a)).card
        ≤ ((G.neighborFinset a ∩ S).map _).card := Finset.card_le_card hsub
      _ = (G.neighborFinset a ∩ S).card := Finset.card_map _
  -- `D ≤ ∑_t (m_t² − m_t)` via the unique shared twin of each non-adjacent rich pair.
  have hDbiU : D ⊆ Iso.biUnion (fun t => (G.neighborFinset t ∩ S).offDiag) := by
    intro p hp
    rw [hDdef, Finset.mem_filter, hOffdef, Finset.mem_offDiag] at hp
    obtain ⟨⟨hp1S, hp2S, hne⟩, hnadj⟩ := hp
    have hp1Hub : p.1 ∈ Hub := hSsub hp1S
    have hp2Hub : p.2 ∈ Hub := hSsub hp2S
    have hsh1 := rich_nonadj_share_eq_one G Hub Iso hshare hno2hub p.1 p.2 hp1Hub hp2Hub
      (hSdeg4 p.1 hp1S) (hSdeg4 p.2 hp2S) hne hnadj (hSrich p.1 hp1S) (hSrich p.2 hp2S)
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (by rw [hsh1]; norm_num)
    rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
    obtain ⟨⟨ht1, ht2⟩, htIso⟩ := ht
    rw [Finset.mem_biUnion]
    refine ⟨t, htIso, ?_⟩
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, hne⟩
    · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht1.symm, hp1S⟩
    · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht2.symm, hp2S⟩
  have hDle : D.card ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
      - (G.neighborFinset t ∩ S).card) := by
    calc D.card ≤ (Iso.biUnion (fun t => (G.neighborFinset t ∩ S).offDiag)).card :=
          Finset.card_le_card hDbiU
      _ ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).offDiag).card := Finset.card_biUnion_le
      _ = ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
            - (G.neighborFinset t ∩ S).card) :=
          Finset.sum_congr rfl (fun t _ => Finset.offDiag_card _)
  -- `∑_t (m_t² − m_t) ≤ M + 3·n₃ ≤ 20`.
  have hQle : ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
      - (G.neighborFinset t ∩ S).card) ≤ 20 := by
    have hpt : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card
        ≤ (G.neighborFinset t ∩ S).card
          + 3 * (if (G.neighborFinset t ∩ S).card = 3 then 1 else 0) := by
      intro t ht
      have hc3 := hmt3 t ht
      set c := (G.neighborFinset t ∩ S).card with hcv
      interval_cases c <;> simp
    calc ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
            - (G.neighborFinset t ∩ S).card)
        ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card
            + 3 * (if (G.neighborFinset t ∩ S).card = 3 then 1 else 0)) := Finset.sum_le_sum hpt
      _ = (∑ t ∈ Iso, (G.neighborFinset t ∩ S).card)
            + 3 * (Iso.filter (fun t => (G.neighborFinset t ∩ S).card = 3)).card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.card_filter]
      _ ≤ 20 := by rw [hcross]; omega
  -- Three-way split summed over `S`: `∑|N∩Hub| + 14 + RichZ = 24`.
  have hHHadd : (∑ a ∈ S, (G.neighborFinset a ∩ Hub).card)
      + 14 + ∑ a ∈ S, (G.neighborFinset a ∩ (Finset.univ \ (Hub ∪ Iso))).card = 24 := by
    have hsplit : (∑ a ∈ S, (G.neighborFinset a ∩ Hub).card)
        + (∑ a ∈ S, (G.neighborFinset a ∩ Iso).card)
        + ∑ a ∈ S, (G.neighborFinset a ∩ (Finset.univ \ (Hub ∪ Iso))).card
        = ∑ a ∈ S, G.degree a := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => nbr_split_three_eighteen G Hub Iso hdisj a)
    have hdeg24 : ∑ a ∈ S, G.degree a = 24 := by
      rw [Finset.sum_congr rfl hSdeg4, Finset.sum_const, hs6, smul_eq_mul]
    rw [hM14, hdeg24] at hsplit; omega
  -- `∑|N∩S| ≤ ∑|N∩Hub|` pointwise.
  have hSHle : ∑ a ∈ S, (G.neighborFinset a ∩ S).card
      ≤ ∑ a ∈ S, (G.neighborFinset a ∩ Hub).card :=
    Finset.sum_le_sum (fun a _ =>
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsub))
  -- The rich `Z`-mass is `0`.
  have hRZ0 : ∑ a ∈ S, (G.neighborFinset a ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by
    omega
  intro a ha
  exact (Finset.sum_eq_zero_iff.mp hRZ0) a ha

/-- **The pinned `(9, 7, 37)` configuration carries a forbidden poor-hub triangle.**  At the unique
boundary `isoDeg(d) = 5`, `|S| = 6`, `M = 14` the lone degree-`5` hub `d` is non-adjacent to the two
`M`-ends (`ninesev_rich_isolated_from_d`) and every rich hub is too (`ninesev_rich_no_z_neighbor`).
Each `M`-end meets exactly two hubs, neither `d` nor rich, so both land on the two *poor* degree-`4`
hubs `P = Hub \ (S ∪ {d})`; whence every poor hub is adjacent to both `M`-ends `z₁ ~ z₂`, giving the
good triangle `{p, z₁, z₂}` of degree sum `4 + 3 + 3 = 10`, excluded by `hT`. -/
theorem ninesev_poor_hub_triangle_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso S : Finset (Fin 18))
    (hSsub : S ⊆ Hub) (hSdeg4 : ∀ a ∈ S, G.degree a = 4)
    (hSrich : ∀ a ∈ S, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 9) (hIso : Iso.card = 7)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 10)
    (d : Fin 18) (hdHub : d ∈ Hub) (hdS : d ∉ S)
    (hother : ∀ a ∈ Hub, a ≠ d → G.degree a = 4) (hdeg_d5 : G.degree d = 5)
    (hi5 : (G.neighborFinset d ∩ Iso).card = 5)
    (hs6 : S.card = 6)
    (hM14 : ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card = 14) :
    False := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- `n₃ ≤ 2` from the coverage bound and `isoDeg(d) = 5`.
  have hcov := ninesev_d_coverage G Hub Iso S hSsub hiso3 d hdHub hdS
  rw [hi5, hIso] at hcov
  have hn3 : (Iso.filter (fun t => (G.neighborFinset t ∩ S).card = 3)).card ≤ 2 := by omega
  -- Rich hubs have no `M`-end neighbour.
  have hrichZ := ninesev_rich_no_z_neighbor G Hub Iso S hSsub hSdeg4 hSrich hdisj hiso3 hshare
    hno2hub hs6 hM14 hn3
  -- `d` is non-adjacent to the `M`-ends.
  have hdIso := ninesev_rich_isolated_from_d G Iso d hdeg_d5 hi5
  -- `Z` structure.
  have hzfacts := ninesev_z_structure G Hub Iso hiso3 hdisj hHub hIso hdeg3 hisodeg3 hleak
  -- `|Z| = 2`; extract the two `M`-ends.
  have hZcard : Z.card = 2 := by
    have hHIcard : (Hub ∪ Iso).card = 16 := by
      rw [Finset.card_union_of_disjoint hdisj, hHub, hIso]
    have hZeq : Z = (Hub ∪ Iso)ᶜ := by
      rw [hZdef]; ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
    rw [hZeq, Finset.card_compl, Fintype.card_fin, hHIcard]
  obtain ⟨z₁, z₂, hz₁₂, hZeq2⟩ := Finset.card_eq_two.mp hZcard
  have hz₁ : z₁ ∈ Z := by rw [hZeq2]; exact Finset.mem_insert_self _ _
  have hz₂ : z₂ ∈ Z := by rw [hZeq2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨h1iso, h1hub, h1deg⟩ := hzfacts z₁ hz₁
  obtain ⟨h2iso, h2hub, h2deg⟩ := hzfacts z₂ hz₂
  -- The `M`-edge `z₁ ~ z₂`.
  have hZadj : G.Adj z₁ z₂ := by
    have hsp := nbr_split_three_eighteen G Hub Iso hdisj z₁
    rw [← hZdef, h1hub, h1iso, h1deg] at hsp
    have hcard1 : (G.neighborFinset z₁ ∩ Z).card = 1 := by omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
    have hwmem : w ∈ G.neighborFinset z₁ ∩ Z := by rw [hw]; exact Finset.mem_singleton_self _
    rw [Finset.mem_inter, G.mem_neighborFinset] at hwmem
    have hwZ : w ∈ Z := hwmem.2
    have hwne : w ≠ z₁ := fun he => G.irrefl (he ▸ hwmem.1)
    rw [hZeq2, Finset.mem_insert, Finset.mem_singleton] at hwZ
    rcases hwZ with rfl | rfl
    · exact absurd rfl hwne
    · exact hwmem.1
  -- The two poor hubs `P = Hub \ (S ∪ {d})`.
  set P : Finset (Fin 18) := Hub \ (S ∪ {d}) with hPdef
  have hSdsub : S ∪ {d} ⊆ Hub := Finset.union_subset hSsub (by simp [hdHub])
  have hPcard : P.card = 2 := by
    have hcard : (S ∪ {d}).card = 7 := by
      rw [Finset.card_union_of_disjoint, hs6, Finset.card_singleton]
      exact Finset.disjoint_singleton_right.mpr hdS
    have hadd : P.card + (S ∪ {d}).card = Hub.card :=
      Finset.card_sdiff_add_card_eq_card hSdsub
    rw [hcard, hHub] at hadd; omega
  -- Each `M`-end's two hub-neighbours are poor.
  have hsubP : ∀ z ∈ Z, G.neighborFinset z ∩ Hub ⊆ P := by
    intro z hz h hh
    rw [Finset.mem_inter, G.mem_neighborFinset] at hh
    obtain ⟨hzh, hhHub⟩ := hh
    have hznotIso : z ∉ Iso := by
      rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.2
    rw [hPdef, Finset.mem_sdiff]
    refine ⟨hhHub, ?_⟩
    rw [Finset.mem_union, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_⟩
    · intro hhS
      have hz0 := hrichZ h hhS
      rw [Finset.card_eq_zero] at hz0
      have : z ∈ G.neighborFinset h ∩ Z := by
        rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hzh.symm, hz⟩
      rw [hz0] at this; exact Finset.notMem_empty z this
    · intro he
      subst he
      have : z ∈ G.neighborFinset h := (G.mem_neighborFinset h z).mpr hzh.symm
      exact hznotIso (hdIso this)
  -- The hub-neighbour sets of `z₁, z₂` are exactly `P`.
  have hP1 : G.neighborFinset z₁ ∩ Hub = P :=
    Finset.eq_of_subset_of_card_le (hsubP z₁ hz₁) (by rw [hPcard, h1hub])
  have hP2 : G.neighborFinset z₂ ∩ Hub = P :=
    Finset.eq_of_subset_of_card_le (hsubP z₂ hz₂) (by rw [hPcard, h2hub])
  -- Pick a poor hub `p`; it is adjacent to both `M`-ends.
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hPcard]; norm_num)
  have hp1 : p ∈ G.neighborFinset z₁ ∩ Hub := by rw [hP1]; exact hp
  have hp2 : p ∈ G.neighborFinset z₂ ∩ Hub := by rw [hP2]; exact hp
  have hpHub : p ∈ Hub := (Finset.mem_inter.mp hp1).2
  have hpadj1 : G.Adj z₁ p := (G.mem_neighborFinset z₁ p).mp (Finset.mem_inter.mp hp1).1
  have hpadj2 : G.Adj z₂ p := (G.mem_neighborFinset z₂ p).mp (Finset.mem_inter.mp hp2).1
  have hpne : p ≠ d := by
    rw [hPdef, Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, not_or] at hp
    exact hp.2.2
  have hpdeg : G.degree p = 4 := hother p hpHub hpne
  -- Distinctness of the triangle vertices.
  have hpz₁ : p ≠ z₁ := by
    intro he; subst he
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz₁; exact hz₁.2.1 hpHub
  have hpz₂ : p ≠ z₂ := by
    intro he; subst he
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz₂; exact hz₂.2.1 hpHub
  -- The forbidden good triangle `{p, z₁, z₂}`.
  exact hT ⟨p, z₁, z₂, hpz₁, hz₁₂, hpz₂, hpadj1.symm, hZadj, hpadj2.symm, by
    rw [hpdeg, h1deg, h2deg]⟩

end N18

end ACMax
