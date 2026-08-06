import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.TwoHubHub6Deg5

/-!
# The `|D| = 13`, `s = 6` cherry-`P₄` boundary corner (`n = 20`)

The densest `P₄` sibling of `TwinCert20CherryP4D12` (`e(M) = 3`, path
`L₁–c₁–c₂–L₂`).  At `n = 20`, `|D| = 13`: `|J| = 9` `M`-isolated twins with
`27` hub incidences on `7` hubs of total degree `33`; the `P₄` carries
`2+1+1+2 = 6` hub slots, so `∑_Hub hubadj = 33 − 27 − 6 = 0` — the hub graph
is **edgeless**.  A degree-`≤ 5` hub with two twins avoiding one of the induced
`P₃`s (`L₁–c₁–c₂` or `c₁–c₂–L₂`) yields `TwoTwinConfig`; in the complementary
world every hub not touching `c₁`, `c₂`, nor both leaves must have degree `≥ 6`
(its `≤ 1` `B`-slot and `0` hub-edges force `≥ 2` twins against a cherry it
avoids).  But at most `|N(c₁) ∩ Hub| + |N(c₂) ∩ Hub| + |N(L₁) ∩ Hub| = 4` hubs
touch the path, so `≥ 3` hubs weigh `6` and `∑_Hub deg ≥ 4·4 + 6·3 = 34 > 33` —
**infeasible**.
-/

namespace ACMax

open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The `|D| = 13` cherry-`P₄` corner** (`s = 6`, `|Hub| = 7`): the
excess-`4` boundary closes into `TwoTwinConfig` (the complementary "no good
hub" world is vacuous by the edgeless-hub degree ledger). -/
theorem cherry_p4_config_D13_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 20) (D Iso : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (_hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁})
    (_hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) (hD13 : D.card = 13) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  -- STEP 0: path distinctness; `L₁ = L₂` would close a light triangle `c₁–c₂–L₁`.
  have hne_c1c2 : c₁ ≠ c₂ := hc12.ne
  have hne_c1L1 : c₁ ≠ L₁ := hac1L1.ne
  have hne_c2L2 : c₂ ≠ L₂ := hac2L2.ne
  have hL1L2 : L₁ ≠ L₂ := by
    intro heq
    refine hT ⟨c₁, c₂, L₁, hne_c1c2, Ne.symm hL1nc2, hne_c1L1, hc12, ?_, hac1L1, ?_⟩
    · rw [heq]
      exact hac2L2
    · omega
  set Hub : Finset (Fin 20) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v := by
    intro v
    rw [hHubdef]
    simp
  set B : Finset (Fin 20) := {L₁, c₁, c₂, L₂} with hBdef
  have hBsub : B ⊆ D := by
    intro x hx
    rw [hBdef] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hmemD]
    rcases hx with rfl | rfl | rfl | rfl
    · exact hL1deg
    · exact hc1deg
    · exact hc2deg
    · exact hL2deg
  have hBcard : B.card = 4 := by
    rw [hBdef,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hne_c1L1, hL1nc2, hL1L2⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne_c1c2, Ne.symm hL2nc1⟩),
      Finset.card_insert_of_notMem (by
        rw [Finset.mem_singleton]
        exact hne_c2L2),
      Finset.card_singleton]
  set J : Finset (Fin 20) := D \ B with hJdef
  have hJcard : J.card = 9 := by
    rw [hJdef, Finset.card_sdiff_of_subset hBsub, hBcard, hD13]
  -- STEP 1: the residue `J` is `M`-isolated with all three neighbours in `Hub`.
  have hJiso : ∀ v ∈ J, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hJdef, Finset.mem_sdiff] at hv
    obtain ⟨hvD, hvB⟩ := hv
    rw [hBdef] at hvB
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvB
    exact ⟨(hmemD v).mp hvD,
      (hIsoprop v (hisochar v hvD hvB.1 hvB.2.1 hvB.2.2.1 hvB.2.2.2)).2⟩
  have hJ3 : ∀ v ∈ J, (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    have hsub : G.neighborFinset v ⊆ Hub := by
      intro u hu
      rw [G.mem_neighborFinset] at hu
      rw [hmemHub]
      have h1 := (hJiso v hv).2 u hu
      have h2 := h3 u
      omega
    rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, (hJiso v hv).1]
  have hsumJHub : ∑ v ∈ J, (G.neighborFinset v ∩ Hub).card = 27 := by
    rw [Finset.sum_congr rfl hJ3, Finset.sum_const, smul_eq_mul, hJcard]
  have hJzero : ∀ v ∈ J, (G.neighborFinset v ∩ D).card = 0 := by
    intro v hv
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro u hu
    rw [Finset.mem_inter, G.mem_neighborFinset] at hu
    exact (hJiso v hv).2 u hu.1 ((hmemD u).mp hu.2)
  -- the `hs6` forcing: `|N(L₁) ∩ D| + |N(L₂) ∩ D| = 2` with both terms `≥ 1`.
  have hsplit6 : ∑ v ∈ J, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ B, (G.neighborFinset v ∩ D).card = 6 := by
    rw [hJdef, Finset.sum_sdiff hBsub]
    exact hs6
  have hsumJD : ∑ v ∈ J, (G.neighborFinset v ∩ D).card = 0 := Finset.sum_eq_zero hJzero
  have hsumB : ∑ v ∈ B, (G.neighborFinset v ∩ D).card
      = (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset c₁ ∩ D).card
        + (G.neighborFinset c₂ ∩ D).card + (G.neighborFinset L₂ ∩ D).card := by
    rw [hBdef,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hne_c1L1, hL1nc2, hL1L2⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne_c1c2, Ne.symm hL2nc1⟩),
      Finset.sum_insert (by
        rw [Finset.mem_singleton]
        exact hne_c2L2),
      Finset.sum_singleton]
    ring
  have hL1ge : 1 ≤ (G.neighborFinset L₁ ∩ D).card :=
    Finset.card_pos.mpr ⟨c₁, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, (hmemD c₁).mpr hc1deg⟩⟩
  have hL2ge : 1 ≤ (G.neighborFinset L₂ ∩ D).card :=
    Finset.card_pos.mpr ⟨c₂, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, (hmemD c₂).mpr hc2deg⟩⟩
  have hL1D : (G.neighborFinset L₁ ∩ D).card = 1 := by omega
  have hL2D : (G.neighborFinset L₂ ∩ D).card = 1 := by omega
  -- the `D`/`Hub` neighbourhood decomposition and the four `B`-slot counts
  have hdecomp : ∀ w : Fin 20,
      (G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Hub).card = G.degree w := by
    intro w
    have hdisj : Disjoint (G.neighborFinset w ∩ D) (G.neighborFinset w ∩ Hub) :=
      Finset.disjoint_left.mpr (fun a ha ha' => by
        rw [Finset.mem_inter] at ha ha'
        have h1 := (hmemD a).mp ha.2
        have h2 := (hmemHub a).mp ha'.2
        omega)
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left]
    have huniv : D ∪ Hub = Finset.univ := by
      ext u
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      rw [hmemD, hmemHub]
      have := h3 u
      omega
    rw [huniv, Finset.inter_univ, G.card_neighborFinset_eq_degree]
  have hL1Hub : (G.neighborFinset L₁ ∩ Hub).card = 2 := by
    have h := hdecomp L₁
    rw [hL1deg, hL1D] at h
    omega
  have hc1Hub : (G.neighborFinset c₁ ∩ Hub).card = 1 := by
    have h := hdecomp c₁
    rw [hc1deg, hin1] at h
    omega
  have hc2Hub : (G.neighborFinset c₂ ∩ Hub).card = 1 := by
    have h := hdecomp c₂
    rw [hc2deg, hin2] at h
    omega
  have hL2Hub : (G.neighborFinset L₂ ∩ Hub).card = 2 := by
    have h := hdecomp L₂
    rw [hL2deg, hL2D] at h
    omega
  have hsumBHub : ∑ v ∈ B, (G.neighborFinset v ∩ Hub).card = 6 := by
    rw [hBdef,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hne_c1L1, hL1nc2, hL1L2⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne_c1c2, Ne.symm hL2nc1⟩),
      Finset.sum_insert (by
        rw [Finset.mem_singleton]
        exact hne_c2L2),
      Finset.sum_singleton, hL1Hub, hc1Hub, hc2Hub, hL2Hub]
    norm_num
  -- STEP 2: handshake and the two cross counts.
  have hsum72 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 39 := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      hD13]
  have hsplitDc : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]
    exact hsum72
  have hHubeqDc : Hub = Dᶜ := by
    ext u
    rw [hmemHub, Finset.mem_compl, hmemD]
    have := h3 u
    omega
  have hHubdeg : ∑ v ∈ Hub, G.degree v = 33 := by
    rw [hHubeqDc]
    omega
  have hHubcard : Hub.card = 7 := by
    rw [hHubeqDc, Finset.card_compl, Fintype.card_fin, hD13]
  have hcrossJ : ∑ v ∈ Hub, (G.neighborFinset v ∩ J).card = 27 := by
    rw [cross_count_twenty G Hub J]
    exact hsumJHub
  have hcrossB : ∑ v ∈ Hub, (G.neighborFinset v ∩ B).card = 6 := by
    rw [cross_count_twenty G Hub B]
    exact hsumBHub
  -- STEP 3: the good-hub dichotomy.
  by_cases hgood : ∃ k ∈ Hub, G.degree k ≤ 5 ∧ 2 ≤ (G.neighborFinset k ∩ J).card ∧
      ((G.neighborFinset k ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card = 0 ∨
        (G.neighborFinset k ∩ ({c₁, c₂, L₂} : Finset (Fin 20))).card = 0)
  · -- extraction: two twins on `k` against the avoided induced `P₃`.
    obtain ⟨k, hkHub, hk5, hk2J, htriple⟩ := hgood
    have hk4 : 4 ≤ G.degree k := (hmemHub k).mp hkHub
    have hk2J' : 1 < (G.neighborFinset k ∩ J).card := by omega
    obtain ⟨tw₁, htw1mem, tw₂, htw2mem, htw12⟩ := Finset.one_lt_card.mp hk2J'
    rw [Finset.mem_inter] at htw1mem htw2mem
    obtain ⟨htw1N, htw1J⟩ := htw1mem
    obtain ⟨htw2N, htw2J⟩ := htw2mem
    have hAtw1k : G.Adj tw₁ k := ((G.mem_neighborFinset _ _).mp htw1N).symm
    have hAtw2k : G.Adj tw₂ k := ((G.mem_neighborFinset _ _).mp htw2N).symm
    have htw1deg : G.degree tw₁ = 3 := (hJiso tw₁ htw1J).1
    have htw2deg : G.degree tw₂ = 3 := (hJiso tw₂ htw2J).1
    have hntw1 : ∀ x : Fin 20, G.degree x = 3 → ¬G.Adj tw₁ x :=
      fun x hx hadj => (hJiso tw₁ htw1J).2 x hadj hx
    have hntw2 : ∀ x : Fin 20, G.degree x = 3 → ¬G.Adj tw₂ x :=
      fun x hx hadj => (hJiso tw₂ htw2J).2 x hadj hx
    have htw1ne : tw₁ ≠ L₁ ∧ tw₁ ≠ c₁ ∧ tw₁ ≠ c₂ ∧ tw₁ ≠ L₂ := by
      have h := htw1J
      rw [hJdef, Finset.mem_sdiff, hBdef] at h
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using h.2
    have htw2ne : tw₂ ≠ L₁ ∧ tw₂ ≠ c₁ ∧ tw₂ ≠ c₂ ∧ tw₂ ≠ L₂ := by
      have h := htw2J
      rw [hJdef, Finset.mem_sdiff, hBdef] at h
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using h.2
    have hkne : ∀ x : Fin 20, G.degree x = 3 → k ≠ x := by
      intro x hx heq
      have h := hk4
      rw [heq, hx] at h
      omega
    rcases htriple with hz | hz
    · have hnk : ∀ x ∈ ({L₁, c₁, c₂} : Finset (Fin 20)), ¬G.Adj k x := by
        intro x hx hadj
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hz
        exact hz x (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hx⟩)
      exact Or.inr (Or.inl ⟨tw₁, tw₂, k, L₁, c₁, c₂,
        htw1deg, htw2deg, hk5, hL1deg, hc1deg, hc2deg,
        hAtw1k, hAtw2k, hac1L1.symm, hc12,
        hntw1 L₁ hL1deg, hntw1 c₁ hc1deg, hntw1 c₂ hc2deg,
        hntw2 L₁ hL1deg, hntw2 c₁ hc1deg, hntw2 c₂ hc2deg,
        hnk L₁ (by simp), hnk c₁ (by simp), hnk c₂ (by simp),
        htw12, htw1ne.1, htw1ne.2.1, htw1ne.2.2.1,
        htw2ne.1, htw2ne.2.1, htw2ne.2.2.1,
        hkne L₁ hL1deg, hkne c₁ hc1deg, hkne c₂ hc2deg,
        Ne.symm hne_c1L1, hne_c1c2, hL1nc2⟩)
    · have hnk : ∀ x ∈ ({c₁, c₂, L₂} : Finset (Fin 20)), ¬G.Adj k x := by
        intro x hx hadj
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hz
        exact hz x (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hx⟩)
      exact Or.inr (Or.inl ⟨tw₁, tw₂, k, c₁, c₂, L₂,
        htw1deg, htw2deg, hk5, hc1deg, hc2deg, hL2deg,
        hAtw1k, hAtw2k, hc12, hac2L2,
        hntw1 c₁ hc1deg, hntw1 c₂ hc2deg, hntw1 L₂ hL2deg,
        hntw2 c₁ hc1deg, hntw2 c₂ hc2deg, hntw2 L₂ hL2deg,
        hnk c₁ (by simp), hnk c₂ (by simp), hnk L₂ (by simp),
        htw12, htw1ne.2.1, htw1ne.2.2.1, htw1ne.2.2.2,
        htw2ne.2.1, htw2ne.2.2.1, htw2ne.2.2.2,
        hkne c₁ hc1deg, hkne c₂ hc2deg, hkne L₂ hL2deg,
        hne_c1c2, hne_c2L2, Ne.symm hL2nc1⟩)
  -- the blocked world: the edgeless hub graph forces the degree ledger to overflow.
  · exfalso
    push Not at hgood
    -- hub–hub incidences vanish: `∑_Hub e = 33 − 27 − 6 = 0`.
    have hDsplit : ∀ s : Finset (Fin 20),
        (s ∩ D).card = (s ∩ J).card + (s ∩ B).card := by
      intro s
      have hBJ : J ∪ B = D := by rw [hJdef]; exact Finset.sdiff_union_of_subset hBsub
      have hdisj : Disjoint (s ∩ J) (s ∩ B) := by
        rw [hJdef]
        exact Finset.disjoint_left.mpr (fun a ha ha' =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).2).2 (Finset.mem_inter.mp ha').2)
      rw [← hBJ, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisj]
    have hperhub : ∀ h : Fin 20, G.degree h
        = (G.neighborFinset h ∩ J).card + (G.neighborFinset h ∩ B).card
          + (G.neighborFinset h ∩ Hub).card := by
      intro h
      have h1 := hdecomp h
      have h2 := hDsplit (G.neighborFinset h)
      omega
    have hHubHubsum : ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card = 0 := by
      have hcong : ∑ h ∈ Hub, G.degree h
          = ∑ h ∈ Hub, ((G.neighborFinset h ∩ J).card + (G.neighborFinset h ∩ B).card
            + (G.neighborFinset h ∩ Hub).card) :=
        Finset.sum_congr rfl (fun h _ => hperhub h)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hHubdeg, hcrossJ, hcrossB] at hcong
      omega
    -- every hub avoiding `c₁`, `c₂` and both leaves has degree `≥ 6`.
    have hnonU_deg6 : ∀ h : Fin 20, h ∈ Hub → ¬G.Adj h c₁ → ¬G.Adj h c₂ →
        ¬(G.Adj h L₁ ∧ G.Adj h L₂) → 6 ≤ G.degree h := by
      intro h hhHub hnc1 hnc2 hnbl
      by_contra hlt
      push Not at hlt
      have hh5 : G.degree h ≤ 5 := by omega
      have hHubh0 : (G.neighborFinset h ∩ Hub).card = 0 := by
        have hle : (G.neighborFinset h ∩ Hub).card
            ≤ ∑ k ∈ Hub, (G.neighborFinset k ∩ Hub).card :=
          Finset.single_le_sum (f := fun k => (G.neighborFinset k ∩ Hub).card)
            (fun i _ => Nat.zero_le _) hhHub
        omega
      have hsubB : G.neighborFinset h ∩ B ⊆ ({L₁, L₂} : Finset (Fin 20)) := by
        intro x hx
        rw [Finset.mem_inter] at hx
        obtain ⟨hxN, hxB⟩ := hx
        have hadj : G.Adj h x := (G.mem_neighborFinset _ _).mp hxN
        rw [hBdef] at hxB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxB
        rcases hxB with rfl | rfl | rfl | rfl
        · simp
        · exact absurd hadj hnc1
        · exact absurd hadj hnc2
        · simp
      have hB2 : (G.neighborFinset h ∩ B).card ≤ 2 := by
        calc (G.neighborFinset h ∩ B).card
            ≤ ({L₁, L₂} : Finset (Fin 20)).card := Finset.card_le_card hsubB
          _ = 2 := Finset.card_pair hL1L2
      have hd4 : 4 ≤ G.degree h := (hmemHub h).mp hhHub
      have hph := hperhub h
      have hJge2 : 2 ≤ (G.neighborFinset h ∩ J).card := by omega
      have hcherry : (G.neighborFinset h ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card = 0 ∨
          (G.neighborFinset h ∩ ({c₁, c₂, L₂} : Finset (Fin 20))).card = 0 := by
        rw [not_and_or] at hnbl
        rcases hnbl with hnL1 | hnL2
        · refine Or.inl ?_
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rw [Finset.mem_inter] at hx
          obtain ⟨hxN, hxT⟩ := hx
          have hadj : G.Adj h x := (G.mem_neighborFinset _ _).mp hxN
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
          rcases hxT with rfl | rfl | rfl
          · exact hnL1 hadj
          · exact hnc1 hadj
          · exact hnc2 hadj
        · refine Or.inr ?_
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rw [Finset.mem_inter] at hx
          obtain ⟨hxN, hxT⟩ := hx
          have hadj : G.Adj h x := (G.mem_neighborFinset _ _).mp hxN
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
          rcases hxT with rfl | rfl | rfl
          · exact hnc1 hadj
          · exact hnc2 hadj
          · exact hnL2 hadj
      obtain ⟨hz1, hz2⟩ := hgood h hhHub hh5 hJge2
      rcases hcherry with h0 | h0
      · exact hz1 h0
      · exact hz2 h0
    -- the `U`/non-`U` degree ledger: `∑_Hub deg = 33 < 34 ≤ 4|U| + 6|non-U|`.
    set U : Finset (Fin 20) :=
      Hub.filter (fun k => G.Adj k c₁ ∨ G.Adj k c₂ ∨ (G.Adj k L₁ ∧ G.Adj k L₂)) with hUdef
    set NU : Finset (Fin 20) :=
      Hub.filter (fun k => ¬(G.Adj k c₁ ∨ G.Adj k c₂ ∨ (G.Adj k L₁ ∧ G.Adj k L₂)))
      with hNUdef
    have hUNU : U.card + NU.card = 7 := by
      rw [hUdef, hNUdef,
        Finset.card_filter_add_card_filter_not
          (fun k => G.Adj k c₁ ∨ G.Adj k c₂ ∨ (G.Adj k L₁ ∧ G.Adj k L₂))]
      exact hHubcard
    have hUle : U.card ≤ 4 := by
      have hsub : U ⊆ (G.neighborFinset c₁ ∩ Hub) ∪ (G.neighborFinset c₂ ∩ Hub)
          ∪ (G.neighborFinset L₁ ∩ Hub) := by
        intro k hk
        rw [hUdef, Finset.mem_filter] at hk
        obtain ⟨hkHub, hor⟩ := hk
        simp only [Finset.mem_union]
        rcases hor with h | h | ⟨hl1, _hl2⟩
        · exact Or.inl (Or.inl (Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr h.symm, hkHub⟩))
        · exact Or.inl (Or.inr (Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr h.symm, hkHub⟩))
        · exact Or.inr (Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr hl1.symm, hkHub⟩)
      calc U.card ≤ ((G.neighborFinset c₁ ∩ Hub) ∪ (G.neighborFinset c₂ ∩ Hub)
              ∪ (G.neighborFinset L₁ ∩ Hub)).card := Finset.card_le_card hsub
        _ ≤ (G.neighborFinset c₁ ∩ Hub).card + (G.neighborFinset c₂ ∩ Hub).card
              + (G.neighborFinset L₁ ∩ Hub).card := by
            refine (Finset.card_union_le _ _).trans ?_
            exact Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ = 4 := by rw [hc1Hub, hc2Hub, hL1Hub]
    have hsdUNU : ∑ v ∈ U, G.degree v + ∑ v ∈ NU, G.degree v = 33 := by
      rw [hUdef, hNUdef, Finset.sum_filter_add_sum_filter_not Hub _ _]
      exact hHubdeg
    have hUdeg : 4 * U.card ≤ ∑ v ∈ U, G.degree v := by
      have h := Finset.card_nsmul_le_sum U (fun v => G.degree v) 4
        (fun v hv => (hmemHub v).mp (by rw [hUdef, Finset.mem_filter] at hv; exact hv.1))
      simpa [smul_eq_mul, mul_comm] using h
    have hNUdeg : 6 * NU.card ≤ ∑ v ∈ NU, G.degree v := by
      have h := Finset.card_nsmul_le_sum NU (fun v => G.degree v) 6 (fun v hv => by
        rw [hNUdef, Finset.mem_filter] at hv
        obtain ⟨hvHub, hnor⟩ := hv
        rw [not_or, not_or] at hnor
        exact hnonU_deg6 v hvHub hnor.1 hnor.2.1 hnor.2.2)
      simpa [smul_eq_mul, mul_comm] using h
    omega

end N20

end ACMax
