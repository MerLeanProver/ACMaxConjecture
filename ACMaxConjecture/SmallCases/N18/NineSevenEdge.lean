import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct

/-!
# Trace and coverage leaves for the `(9, 7, 37)` rich-absorber residual (`n = 18`)

For the tight `e(M) = 1` profile `(|Hub|, |Iso|, ∑deg) = (9, 7, 37)` the rich degree-`4` hubs are
`S = {h ∈ Hub : G.degree h = 4 ∧ 2 ≤ |N(h) ∩ Iso|}`.  Write `s := |S|`, `M := ∑_{a∈S}|N(a)∩Iso|`
and `m_t := |N(t) ∩ S|` for an `M`-isolated twin `t`.

* `ninesev_edge_share_le` is the trace/edge-count inequality
  `s·s − s + M ≤ 4·s + ∑_t (m_t² − m_t)`.  The ordered off-diagonal pairs of `S` split into
  adjacent pairs (bounded by the internal hub-degree mass `∑_a |N(a)∩S| ≤ 4s − M`) and non-adjacent
  pairs (each sharing a unique twin by `rich_nonadj_share_eq_one`, so embedded into the twins'
  off-diagonal traces).
* `ninesev_d_coverage` is the coverage bound `#{t : m_t = 3} + |N(d) ∩ Iso| ≤ |Iso|` for the lone
  degree-`5` hub `d` (which lies in `Hub` but not in `S`): a twin meeting three rich degree-`4` hubs
  cannot also meet `d`, so the two twin sets are disjoint subsets of `Iso`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Trace/edge-count inequality for the rich degree-`4` hubs.**  With `S` the rich degree-`4`
hubs, `s := |S|`, `M := ∑_{a∈S}|N(a)∩Iso|` and `m_t := |N(t)∩S|`, the ordered off-diagonal pairs of
`S` are bounded by the internal hub-degree mass plus the twins' off-diagonal traces, giving
`s·s − s + M ≤ 4·s + ∑_t (m_t² − m_t)`. -/
theorem ninesev_edge_share_le (G : SimpleGraph (Fin 18)) (Hub Iso S : Finset (Fin 18))
    (hSsub : S ⊆ Hub) (hSdeg4 : ∀ a ∈ S, G.degree a = 4)
    (hSrich : ∀ a ∈ S, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    S.card * S.card - S.card + ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card
      ≤ 4 * S.card + ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card) := by
  classical
  -- Off-diagonal of `S`.
  set Off : Finset (Fin 18 × Fin 18) := S.offDiag with hOffdef
  have hOffcard : Off.card = S.card * S.card - S.card := by rw [hOffdef, Finset.offDiag_card]
  set Dadj : Finset (Fin 18 × Fin 18) := Off.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  set D : Finset (Fin 18 × Fin 18) := Off.filter (fun p => ¬G.Adj p.1 p.2) with hDdef
  have hDsplit : D.card + Dadj.card = Off.card := by
    rw [hDdef, hDadjdef, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  -- `Dadj ≤ ∑_S |N ∩ S|`.
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
  -- Non-adjacent rich pairs embed into the twins' trace off-diagonals.
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
  -- Internal mass plus iso-mass is `≤ 4s`.
  have hmass : ∑ a ∈ S, (G.neighborFinset a ∩ S).card
      + ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card ≤ 4 * S.card := by
    rw [← Finset.sum_add_distrib]
    calc ∑ a ∈ S, ((G.neighborFinset a ∩ S).card + (G.neighborFinset a ∩ Iso).card)
        ≤ ∑ _a ∈ S, 4 := by
          apply Finset.sum_le_sum
          intro a ha
          have hdisjSI : Disjoint (G.neighborFinset a ∩ S) (G.neighborFinset a ∩ Iso) := by
            apply Finset.disjoint_left.mpr
            intro x hx1 hx2
            exact Finset.disjoint_left.mp hdisj (hSsub (Finset.mem_inter.mp hx1).2)
              (Finset.mem_inter.mp hx2).2
          have hun : (G.neighborFinset a ∩ S) ∪ (G.neighborFinset a ∩ Iso) ⊆ G.neighborFinset a := by
            rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
          have hle := Finset.card_le_card hun
          rw [Finset.card_union_of_disjoint hdisjSI, G.card_neighborFinset_eq_degree,
            hSdeg4 a ha] at hle
          exact hle
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← hOffcard, ← hDsplit]
  omega

/-- **Coverage bound for the degree-`5` absorber.**  The lone degree-`5` hub `d` lies in `Hub` but
not in `S` (it has degree `5 ≠ 4`).  A twin meeting three rich degree-`4` hubs has all three of its
hub-neighbours in `S`, hence does not meet `d`; so the twins with `m_t = 3` and the twins adjacent
to `d` are disjoint subsets of `Iso`, giving `#{t : m_t = 3} + |N(d) ∩ Iso| ≤ |Iso|`. -/
theorem ninesev_d_coverage (G : SimpleGraph (Fin 18)) (Hub Iso S : Finset (Fin 18))
    (hSsub : S ⊆ Hub) (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (d : Fin 18) (hdHub : d ∈ Hub) (hdS : d ∉ S) :
    (Iso.filter (fun t => (G.neighborFinset t ∩ S).card = 3)).card
      + (G.neighborFinset d ∩ Iso).card ≤ Iso.card := by
  classical
  set A : Finset (Fin 18) := Iso.filter (fun t => (G.neighborFinset t ∩ S).card = 3) with hAdef
  set B : Finset (Fin 18) := G.neighborFinset d ∩ Iso with hBdef
  have hAsub : A ⊆ Iso := Finset.filter_subset _ _
  have hBsub : B ⊆ Iso := Finset.inter_subset_right
  have hdisjAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro t htA htB
    rw [hAdef, Finset.mem_filter] at htA
    obtain ⟨htIso, ht3⟩ := htA
    -- `N(t) ∩ S = N(t) ∩ Hub` since both have card `3` and the former is a subset.
    have hsub : G.neighborFinset t ∩ S ⊆ G.neighborFinset t ∩ Hub :=
      Finset.inter_subset_inter (Finset.Subset.refl _) hSsub
    have heq : G.neighborFinset t ∩ S = G.neighborFinset t ∩ Hub :=
      Finset.eq_of_subset_of_card_le hsub (by rw [ht3, hiso3 t htIso])
    -- `d ∈ N(t) ∩ Hub` from `htB`, hence `d ∈ N(t) ∩ S`, contradicting `hdS`.
    rw [hBdef, Finset.mem_inter, G.mem_neighborFinset] at htB
    have hdmem : d ∈ G.neighborFinset t ∩ Hub := by
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨(G.adj_comm d t).mp htB.1, hdHub⟩
    rw [← heq, Finset.mem_inter] at hdmem
    exact hdS hdmem.2
  have hunion : (A ∪ B).card ≤ Iso.card :=
    Finset.card_le_card (Finset.union_subset hAsub hBsub)
  rw [Finset.card_union_of_disjoint hdisjAB] at hunion
  exact hunion

end N18

end ACMax
