import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.TwoHubHub6Deg5

/-!
# The `|D| = 12`, `s = 6` cherry-`P₄` boundary corner (`n = 19`)

The `P₄` sibling of `TwinCert19CherryP3D12` (`e(M) = 3`, path
`L₁–c₁–c₂–L₂`).  At `|D| = 12`: `|J| = 8` `M`-isolated twins with `24` hub
incidences on `7` hubs of total degree `32`; the `P₄` carries `2+1+1+2 = 6`
hub slots, so the identity gives `Σ_Hub hubadj = 2` (`e_{HH} = 1`).  A
degree-`≤ 5` hub with two twins avoiding one of the induced `P₃`s
(`L₁–c₁–c₂` or `c₁–c₂–L₂`) yields `TwoTwinConfig`; the complementary world
is **infeasible**: a blocked twin-rich hub touches `c₁` or `c₂` (supply
`1 + 1`) or both leaves (`2` slots), so `slots(W) ≥ 2|W| − 2` while the
counting demands `3|W| − slots(W) ≥ 13 − 3h₆` with `h₆ ≤ 2` — impossible.
-/

namespace ACMax

open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The `|D| = 12` cherry-`P₄` corner** (`s = 6`, `|Hub| = 7`): the
excess-`4` boundary closes into `TwoTwinConfig`. -/
theorem cherry_p4_config_D12_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 19) (D Iso : Finset (Fin 19))
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (_hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁})
    (_hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) (hD12 : D.card = 12) :
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
  set Hub : Finset (Fin 19) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 19, v ∈ Hub ↔ 4 ≤ G.degree v := by
    intro v
    rw [hHubdef]
    simp
  set B : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hBdef
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
  set J : Finset (Fin 19) := D \ B with hJdef
  have hJcard : J.card = 8 := by
    rw [hJdef, Finset.card_sdiff_of_subset hBsub, hBcard, hD12]
  -- STEP 1: the residue `J` is `M`-isolated with all three neighbours in `Hub`.
  have hJiso : ∀ v ∈ J, G.degree v = 3 ∧ ∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3 := by
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
  have hsumJHub : ∑ v ∈ J, (G.neighborFinset v ∩ Hub).card = 24 := by
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
  have hdecomp : ∀ w : Fin 19,
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
  have hsum68 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 36 := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      hD12]
  have hsplitDc : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
    rw [Finset.sum_add_sum_compl]
    exact hsum68
  have hHubeqDc : Hub = Dᶜ := by
    ext u
    rw [hmemHub, Finset.mem_compl, hmemD]
    have := h3 u
    omega
  have hHubdeg : ∑ v ∈ Hub, G.degree v = 32 := by
    rw [hHubeqDc]
    omega
  have hHubcard : Hub.card = 7 := by
    rw [hHubeqDc, Finset.card_compl, Fintype.card_fin, hD12]
  have hcrossJ : ∑ v ∈ Hub, (G.neighborFinset v ∩ J).card = 24 := by
    rw [cross_count_nineteen G Hub J]
    exact hsumJHub
  have hcrossB : ∑ v ∈ Hub, (G.neighborFinset v ∩ B).card = 6 := by
    rw [cross_count_nineteen G Hub B]
    exact hsumBHub
  -- STEP 3: the good-hub dichotomy.
  by_cases hgood : ∃ k ∈ Hub, G.degree k ≤ 5 ∧ 2 ≤ (G.neighborFinset k ∩ J).card ∧
      ((G.neighborFinset k ∩ ({L₁, c₁, c₂} : Finset (Fin 19))).card = 0 ∨
        (G.neighborFinset k ∩ ({c₁, c₂, L₂} : Finset (Fin 19))).card = 0)
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
    have hntw1 : ∀ x : Fin 19, G.degree x = 3 → ¬G.Adj tw₁ x :=
      fun x hx hadj => (hJiso tw₁ htw1J).2 x hadj hx
    have hntw2 : ∀ x : Fin 19, G.degree x = 3 → ¬G.Adj tw₂ x :=
      fun x hx hadj => (hJiso tw₂ htw2J).2 x hadj hx
    have htw1ne : tw₁ ≠ L₁ ∧ tw₁ ≠ c₁ ∧ tw₁ ≠ c₂ ∧ tw₁ ≠ L₂ := by
      have h := htw1J
      rw [hJdef, Finset.mem_sdiff, hBdef] at h
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using h.2
    have htw2ne : tw₂ ≠ L₁ ∧ tw₂ ≠ c₁ ∧ tw₂ ≠ c₂ ∧ tw₂ ≠ L₂ := by
      have h := htw2J
      rw [hJdef, Finset.mem_sdiff, hBdef] at h
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using h.2
    have hkne : ∀ x : Fin 19, G.degree x = 3 → k ≠ x := by
      intro x hx heq
      have h := hk4
      rw [heq, hx] at h
      omega
    rcases htriple with hz | hz
    · have hnk : ∀ x ∈ ({L₁, c₁, c₂} : Finset (Fin 19)), ¬G.Adj k x := by
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
    · have hnk : ∀ x ∈ ({c₁, c₂, L₂} : Finset (Fin 19)), ¬G.Adj k x := by
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
  -- the blocked world: LP infeasibility of the slot supply.
  · exfalso
    push Not at hgood
    set Hub5 : Finset (Fin 19) := Hub.filter (fun k => G.degree k ≤ 5) with hHub5def
    set H6 : Finset (Fin 19) := Hub.filter (fun k => ¬G.degree k ≤ 5) with hH6def
    set W : Finset (Fin 19) :=
      Hub5.filter (fun k => 2 ≤ (G.neighborFinset k ∩ J).card) with hWdef
    set A : Finset (Fin 19) :=
      Hub5.filter (fun k => ¬2 ≤ (G.neighborFinset k ∩ J).card) with hAdef
    have hmemW : ∀ k : Fin 19,
        k ∈ W ↔ k ∈ Hub ∧ G.degree k ≤ 5 ∧ 2 ≤ (G.neighborFinset k ∩ J).card := by
      intro k
      rw [hWdef, Finset.mem_filter, hHub5def, Finset.mem_filter]
      exact and_assoc
    have hmemA : ∀ k : Fin 19,
        k ∈ A ↔ k ∈ Hub ∧ G.degree k ≤ 5 ∧ (G.neighborFinset k ∩ J).card ≤ 1 := by
      intro k
      rw [hAdef, Finset.mem_filter, hHub5def, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hh, hd⟩, hj⟩
        exact ⟨hh, hd, by omega⟩
      · rintro ⟨hh, hd, hj⟩
        exact ⟨⟨hh, hd⟩, by omega⟩
    have hmemH6 : ∀ k : Fin 19, k ∈ H6 → 6 ≤ G.degree k := by
      intro k hk
      rw [hH6def, Finset.mem_filter] at hk
      have h := hk.2
      omega
    -- the three-way partition of the seven hubs, cards and degree/incidence sums
    have hcards1 : Hub5.card + H6.card = 7 := by
      rw [hHub5def, hH6def, Finset.card_filter_add_card_filter_not (fun k => G.degree k ≤ 5)]
      exact hHubcard
    have hcards2 : W.card + A.card = Hub5.card := by
      rw [hWdef, hAdef, Finset.card_filter_add_card_filter_not
        (fun k => 2 ≤ (G.neighborFinset k ∩ J).card)]
    have hsJ1 : ∑ v ∈ Hub5, (G.neighborFinset v ∩ J).card
        + ∑ v ∈ H6, (G.neighborFinset v ∩ J).card = 24 := by
      rw [hHub5def, hH6def, Finset.sum_filter_add_sum_filter_not Hub _ _]
      exact hcrossJ
    have hsJ2 : ∑ v ∈ W, (G.neighborFinset v ∩ J).card
        + ∑ v ∈ A, (G.neighborFinset v ∩ J).card
        = ∑ v ∈ Hub5, (G.neighborFinset v ∩ J).card := by
      rw [hWdef, hAdef]
      exact Finset.sum_filter_add_sum_filter_not Hub5 _ _
    have hsd1 : ∑ v ∈ Hub5, G.degree v + ∑ v ∈ H6, G.degree v = 32 := by
      rw [hHub5def, hH6def, Finset.sum_filter_add_sum_filter_not Hub _ _]
      exact hHubdeg
    have hsd2 : ∑ v ∈ W, G.degree v + ∑ v ∈ A, G.degree v = ∑ v ∈ Hub5, G.degree v := by
      rw [hWdef, hAdef]
      exact Finset.sum_filter_add_sum_filter_not Hub5 _ _
    -- per-class bounds
    have hAJ : ∑ v ∈ A, (G.neighborFinset v ∩ J).card ≤ A.card := by
      calc ∑ v ∈ A, (G.neighborFinset v ∩ J).card ≤ ∑ _v ∈ A, 1 :=
            Finset.sum_le_sum (fun v hv => ((hmemA v).mp hv).2.2)
        _ = A.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hH6J : ∑ v ∈ H6, (G.neighborFinset v ∩ J).card ≤ ∑ v ∈ H6, G.degree v :=
      Finset.sum_le_sum (fun v _ => by
        calc (G.neighborFinset v ∩ J).card ≤ (G.neighborFinset v).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = G.degree v := G.card_neighborFinset_eq_degree v)
    have hH6deg : 6 * H6.card ≤ ∑ v ∈ H6, G.degree v := by
      have h := Finset.card_nsmul_le_sum H6 (fun v => G.degree v) 6 hmemH6
      simpa [smul_eq_mul, mul_comm] using h
    have hAdeg : 4 * A.card ≤ ∑ v ∈ A, G.degree v := by
      have h := Finset.card_nsmul_le_sum A (fun v => G.degree v) 4
        (fun v hv => (hmemHub v).mp ((hmemA v).mp hv).1)
      simpa [smul_eq_mul, mul_comm] using h
    have hHub5deg : 4 * Hub5.card ≤ ∑ v ∈ Hub5, G.degree v := by
      have h := Finset.card_nsmul_le_sum Hub5 (fun v => G.degree v) 4
        (fun v hv => (hmemHub v).mp (by
          rw [hHub5def, Finset.mem_filter] at hv
          exact hv.1))
      simpa [smul_eq_mul, mul_comm] using h
    -- the per-`W` neighbourhood split `|N ∩ J| + |N ∩ B| ≤ deg`
    have hWJB : ∑ v ∈ W, (G.neighborFinset v ∩ J).card
        + ∑ v ∈ W, (G.neighborFinset v ∩ B).card ≤ ∑ v ∈ W, G.degree v := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hdisjJB : Disjoint (G.neighborFinset k ∩ J) (G.neighborFinset k ∩ B) :=
        Finset.disjoint_left.mpr (fun a ha ha' => by
          rw [Finset.mem_inter] at ha ha'
          have h := ha.2
          rw [hJdef, Finset.mem_sdiff] at h
          exact h.2 ha'.2)
      calc (G.neighborFinset k ∩ J).card + (G.neighborFinset k ∩ B).card
          = ((G.neighborFinset k ∩ J) ∪ (G.neighborFinset k ∩ B)).card :=
            (Finset.card_union_of_disjoint hdisjJB).symm
        _ ≤ (G.neighborFinset k).card := Finset.card_le_card (by
            intro a ha
            rw [Finset.mem_union] at ha
            rcases ha with h | h
            · exact (Finset.mem_inter.mp h).1
            · exact (Finset.mem_inter.mp h).1)
        _ = G.degree k := G.card_neighborFinset_eq_degree k
    -- the `c`-toucher split of `W` and the supply bound `|C| ≤ 2`
    set C : Finset (Fin 19) := W.filter (fun k => G.Adj k c₁ ∨ G.Adj k c₂) with hCdef
    set NC : Finset (Fin 19) := W.filter (fun k => ¬(G.Adj k c₁ ∨ G.Adj k c₂)) with hNCdef
    have hsplitC : ∑ v ∈ C, (G.neighborFinset v ∩ B).card
        + ∑ v ∈ NC, (G.neighborFinset v ∩ B).card
        = ∑ v ∈ W, (G.neighborFinset v ∩ B).card := by
      rw [hCdef, hNCdef]
      exact Finset.sum_filter_add_sum_filter_not W _ _
    have hcardsC : C.card + NC.card = W.card := by
      rw [hCdef, hNCdef, Finset.card_filter_add_card_filter_not
        (fun k => G.Adj k c₁ ∨ G.Adj k c₂)]
    have hCle2 : C.card ≤ 2 := by
      have hsub : C ⊆ (G.neighborFinset c₁ ∩ Hub) ∪ (G.neighborFinset c₂ ∩ Hub) := by
        intro k hk
        rw [hCdef, Finset.mem_filter] at hk
        obtain ⟨hkW, hadj⟩ := hk
        have hkHub : k ∈ Hub := ((hmemW k).mp hkW).1
        rw [Finset.mem_union]
        rcases hadj with h | h
        · exact Or.inl (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hkHub⟩)
        · exact Or.inr (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hkHub⟩)
      calc C.card ≤ ((G.neighborFinset c₁ ∩ Hub) ∪ (G.neighborFinset c₂ ∩ Hub)).card :=
            Finset.card_le_card hsub
        _ ≤ (G.neighborFinset c₁ ∩ Hub).card + (G.neighborFinset c₂ ∩ Hub).card :=
            Finset.card_union_le _ _
        _ ≤ 2 := by omega
    have hCge : ∀ k ∈ C, 1 ≤ (G.neighborFinset k ∩ B).card := by
      intro k hk
      rw [hCdef, Finset.mem_filter] at hk
      apply Finset.card_pos.mpr
      rcases hk.2 with h | h
      · exact ⟨c₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h, by
          rw [hBdef]; simp⟩⟩
      · exact ⟨c₂, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h, by
          rw [hBdef]; simp⟩⟩
    -- a blocked twin-rich hub missing both centres is adjacent to both leaves
    have hNCge : ∀ k ∈ NC, 2 ≤ (G.neighborFinset k ∩ B).card := by
      intro k hk
      rw [hNCdef, Finset.mem_filter] at hk
      obtain ⟨hkW, hnc⟩ := hk
      obtain ⟨hkHub, hk5, hk2J⟩ := (hmemW k).mp hkW
      obtain ⟨hz1, hz2⟩ := hgood k hkHub hk5 hk2J
      have hL1mem : L₁ ∈ G.neighborFinset k := by
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz1)
        rw [Finset.mem_inter] at hu
        obtain ⟨huN, huT⟩ := hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at huT
        rcases huT with rfl | rfl | rfl
        · exact huN
        · exact absurd ((G.mem_neighborFinset _ _).mp huN) (fun h => hnc (Or.inl h))
        · exact absurd ((G.mem_neighborFinset _ _).mp huN) (fun h => hnc (Or.inr h))
      have hL2mem : L₂ ∈ G.neighborFinset k := by
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz2)
        rw [Finset.mem_inter] at hu
        obtain ⟨huN, huT⟩ := hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at huT
        rcases huT with rfl | rfl | rfl
        · exact absurd ((G.mem_neighborFinset _ _).mp huN) (fun h => hnc (Or.inl h))
        · exact absurd ((G.mem_neighborFinset _ _).mp huN) (fun h => hnc (Or.inr h))
        · exact huN
      have hsub : ({L₁, L₂} : Finset (Fin 19)) ⊆ G.neighborFinset k ∩ B := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hL1mem, by rw [hBdef]; simp⟩
        · exact Finset.mem_inter.mpr ⟨hL2mem, by rw [hBdef]; simp⟩
      calc 2 = ({L₁, L₂} : Finset (Fin 19)).card := by
            rw [Finset.card_insert_of_notMem (by
              rw [Finset.mem_singleton]
              exact hL1L2), Finset.card_singleton]
        _ ≤ _ := Finset.card_le_card hsub
    have hsumCge : C.card ≤ ∑ v ∈ C, (G.neighborFinset v ∩ B).card := by
      have h := Finset.card_nsmul_le_sum C (fun v => (G.neighborFinset v ∩ B).card) 1 hCge
      simpa using h
    have hsumNCge : 2 * NC.card ≤ ∑ v ∈ NC, (G.neighborFinset v ∩ B).card := by
      have h := Finset.card_nsmul_le_sum NC (fun v => (G.neighborFinset v ∩ B).card) 2 hNCge
      simpa [smul_eq_mul, mul_comm] using h
    have hWB6 : ∑ v ∈ W, (G.neighborFinset v ∩ B).card ≤ 6 := by
      calc ∑ v ∈ W, (G.neighborFinset v ∩ B).card
          ≤ ∑ v ∈ Hub, (G.neighborFinset v ∩ B).card :=
            Finset.sum_le_sum_of_subset (fun k hk => ((hmemW k).mp hk).1)
        _ = 6 := hcrossB
    -- the LP: `3|A| + 2|W| ≤ 10`, `|A| + |W| ≥ 5`, `2|W| − 2 ≤ 6` — infeasible.
    omega

end N19

end ACMax
