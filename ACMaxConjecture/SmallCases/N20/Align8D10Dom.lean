import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Align8D10DomA
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.TwoHubHub6Deg5

/-!
# The `|D| = 10`, `e(M) = 5` dominating-edge dichotomy (`n = 20`)

`SingleVertexConfig` or a shared degree-`≤ 5` hub.  The double-star
(`eM5_domedge_leaves_twenty`) leaves `|Iso| = 4` `M`-isolated twins with
`12` hub-incidences over the `10` hubs.  If no degree-`≤ 5` hub carries two
of them, `12 > 10` forces a degree-`6` hub `w`, and the handshake
`Σ_Hub = 72 − 30 = 42 = 6 + 4·9` gives the profile `{6, 4⁹}`: every hub
other than `w` has degree exactly `4`.  The **leaf-coverage pigeonhole**
finishes: blocking `SingleVertexConfig` for an iso `t` with its non-`w`
degree-`4` pair `(h, h′)` requires a pair member adjacent to the leaf `l₁`
of the induced `P₃` `l₁–c₁–c₂`, but `l₁` has only `2` non-centre slots for
the `4` isos, so two isos would share a degree-`4` hub — excluded.  Some
iso's pair misses `l₁`, and `(t, h, h′, l₁–c₁–c₂)` is a
`SingleVertexConfig` with budget `2·0 + 4 + 4 ≤ 8`.
-/

namespace ACMax

open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The dominating-edge dichotomy at `|D| = 10`, `e(M) = 5`:**
`SingleVertexConfig` or a shared degree-`≤ 5` hub with two `M`-isolated
twins. -/
theorem eM5_D10_domedge_sv_or_shared_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hD10 : (Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 10)
    (c₁ c₂ : Fin 20) (hc1D : G.degree c₁ = 3) (hc2D : G.degree c₂ = 3)
    (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 20, G.degree p = 3 → G.degree q = 3 → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card
        = 10) :
    SingleVertexConfig G ∨
    ∃ k tw₁ tw₂ : Fin 20, G.degree k ≤ 5 ∧ tw₁ ≠ tw₂ ∧
      G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ G.Adj tw₁ k ∧ G.Adj tw₂ k ∧
      (∀ w : Fin 20, G.Adj tw₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj tw₂ w → G.degree w ≠ 3) := by
  classical
  obtain ⟨l₁, l₂, l₃, l₄, h12, h13, h14, h23, h24, h36,
      h1c1, h1c2, h2c1, h2c2, h3c1, h3c2, h4c1, h4c2,
      hd1, hd2, hd3, hd4, ha1, -, -, -, hn1, -, -, -, hfull1, hfull2⟩ :=
    eM5_domedge_leaves_twenty G h3 hT hD10 c₁ c₂ hc1D hc2D hc12 hcov hsum10
  by_cases hshared : ∃ k tw₁ tw₂ : Fin 20, G.degree k ≤ 5 ∧ tw₁ ≠ tw₂ ∧
      G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ G.Adj tw₁ k ∧ G.Adj tw₂ k ∧
      (∀ w : Fin 20, G.Adj tw₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj tw₂ w → G.degree w ≠ 3)
  · exact Or.inr hshared
  left
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 20) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  -- the six double-star vertices and the `M`-isolated residue
  set B : Finset (Fin 20) := {c₁, c₂, l₁, l₂, l₃, l₄} with hBdef
  have hBsub : B ⊆ D := by
    intro x hx
    rw [hBdef] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hmemD]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc1D
    · exact hc2D
    · exact hd1
    · exact hd2
    · exact hd3
    · exact hd4
  have hBcard : B.card = 6 := by
    rw [hBdef,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hc12.ne, h1c1.symm, h2c1.symm, h3c1.symm, h4c1.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h1c2.symm, h2c2.symm, h3c2.symm, h4c2.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, h13, h14⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h23, h24⟩),
      Finset.card_insert_of_notMem (by
        rw [Finset.mem_singleton]
        exact h36),
      Finset.card_singleton]
  set Iso : Finset (Fin 20) := D \ B with hIsodef
  have hIsocard : Iso.card = 4 := by
    rw [hIsodef, Finset.card_sdiff_of_subset hBsub, hBcard, hD10]
  -- every `Iso` member is `M`-isolated: its degree-`3` neighbours would violate coverage
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ u : Fin 20, G.Adj v u → G.degree u ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_sdiff] at hv
    obtain ⟨hvD, hvB⟩ := hv
    rw [hBdef] at hvB
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvB
    obtain ⟨hvc1, hvc2, hvl1, hvl2, hvl3, hvl4⟩ := hvB
    have hv3 : G.degree v = 3 := (hmemD v).mp hvD
    refine ⟨hv3, fun u hadj hu3 => ?_⟩
    rcases hcov v u hv3 hu3 hadj with e | e | e | e
    · exact hvc1 e
    · exact hvc2 e
    · subst e
      rcases hfull1 v hadj.symm with e | e | e
      · exact hvc2 e
      · exact hvl1 e
      · exact hvl2 e
    · subst e
      rcases hfull2 v hadj.symm with e | e | e
      · exact hvc1 e
      · exact hvl3 e
      · exact hvl4 e
  have hNsub : ∀ v ∈ Iso, G.neighborFinset v ⊆ Hub := by
    intro v hv u hu
    rw [G.mem_neighborFinset] at hu
    rw [hmemHub]
    have h1 := (hIsoiso v hv).2 u hu
    have h2 := h3 u
    omega
  have hIso3 : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    rw [Finset.inter_eq_left.mpr (hNsub v hv), G.card_neighborFinset_eq_degree,
      (hIsoiso v hv).1]
  have hsumIso : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 12 := by
    rw [Finset.sum_congr rfl hIso3, Finset.sum_const, smul_eq_mul, hIsocard]
  -- the handshake: hub degree-sum `42` over `10` hubs
  have hsum72 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]
    exact hsum72
  have hHubeqDc : Hub = Dᶜ := by
    ext u
    rw [hmemHub, Finset.mem_compl, hmemD]
    have := h3 u
    omega
  have hHubsum : ∑ v ∈ Hub, G.degree v = 42 := by
    rw [hHubeqDc]
    omega
  have hHubcard : Hub.card = 10 := by
    rw [hHubeqDc, Finset.card_compl, Fintype.card_fin, hD10]
  -- no shared degree-`≤ 5` hub ⟹ some hub has degree `≥ 6` (`12 > 10` incidences)
  have hex6 : ∃ w ∈ Hub, 6 ≤ G.degree w := by
    by_contra hcon
    push Not at hcon
    have hHub5 : ∀ u ∈ Hub, G.degree u ≤ 5 := fun u hu => by
      have := hcon u hu
      omega
    have hcount : Hub.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card := by omega
    obtain ⟨k, t₁, t₂, -, hk5, ht12, ht1, ht2, hA1, hA2, hi1, hi2⟩ :=
      shared_hub_le5_from_count_twenty G Iso Hub hIsoiso hHub5 hcount
    exact hshared ⟨k, t₁, t₂, hk5, ht12, ht1, ht2, hA1, hA2, hi1, hi2⟩
  obtain ⟨w, hwHub, hw6⟩ := hex6
  -- every hub other than `w` has degree exactly `4` (`6 + 5 + 4·8 = 43 > 42`)
  have hother4 : ∀ u ∈ Hub, u ≠ w → G.degree u = 4 := by
    intro u hu huw
    by_contra hcon
    have hu5 : 5 ≤ G.degree u := by
      have := (hmemHub u).mp hu
      omega
    have hue : u ∈ Hub.erase w := Finset.mem_erase.mpr ⟨huw, hu⟩
    have hsum1 : ∑ v ∈ Hub, G.degree v = G.degree w + ∑ v ∈ Hub.erase w, G.degree v :=
      (Finset.add_sum_erase _ _ hwHub).symm
    have hsum2 : ∑ v ∈ Hub.erase w, G.degree v
        = G.degree u + ∑ v ∈ (Hub.erase w).erase u, G.degree v :=
      (Finset.add_sum_erase _ _ hue).symm
    have hsum3 : 4 * ((Hub.erase w).erase u).card
        ≤ ∑ v ∈ (Hub.erase w).erase u, G.degree v := by
      calc 4 * ((Hub.erase w).erase u).card
          = ∑ _v ∈ (Hub.erase w).erase u, 4 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ v ∈ (Hub.erase w).erase u, G.degree v := by
            refine Finset.sum_le_sum fun v hv => ?_
            exact (hmemHub v).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv))
    have hcards : ((Hub.erase w).erase u).card = 8 := by
      rw [Finset.card_erase_of_mem hue, Finset.card_erase_of_mem hwHub, hHubcard]
    omega
  -- leaf-coverage pigeonhole on `l₁`: the four disjoint non-`w` pairs cannot all hit
  -- `l₁`'s two hub slots, so some iso's pair misses `l₁` entirely
  have hfind : ∃ t ∈ Iso, ∀ u : Fin 20, G.Adj t u → u ≠ w → ¬G.Adj u l₁ := by
    by_contra hcon
    push Not at hcon
    have hcon' : ∀ v : Fin 20, ∃ u : Fin 20,
        v ∈ Iso → G.Adj v u ∧ u ≠ w ∧ G.Adj u l₁ := by
      intro v
      by_cases hv : v ∈ Iso
      · obtain ⟨u, hu⟩ := hcon v hv
        exact ⟨u, fun _ => hu⟩
      · exact ⟨0, fun hmem => absurd hmem hv⟩
    choose f hf using hcon'
    have hmaps : ∀ v ∈ Iso, f v ∈ (G.neighborFinset l₁).erase c₁ := by
      intro v hv
      obtain ⟨hadj, hnw, hal⟩ := hf v hv
      have hdeg4 : G.degree (f v) = 4 :=
        hother4 (f v) (hNsub v hv ((G.mem_neighborFinset _ _).mpr hadj)) hnw
      refine Finset.mem_erase.mpr ⟨?_, (G.mem_neighborFinset _ _).mpr hal.symm⟩
      intro heq
      rw [heq] at hdeg4
      omega
    have hcard2 : ((G.neighborFinset l₁).erase c₁).card = 2 := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr ha1),
        G.card_neighborFinset_eq_degree, hd1]
    have hlt : ((G.neighborFinset l₁).erase c₁).card < Iso.card := by omega
    obtain ⟨t₁, ht₁, t₂, ht₂, hne12, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
    obtain ⟨hadj1, hnw1, -⟩ := hf t₁ ht₁
    obtain ⟨hadj2, -, -⟩ := hf t₂ ht₂
    have hdeg1 : G.degree (f t₁) = 4 :=
      hother4 (f t₁) (hNsub t₁ ht₁ ((G.mem_neighborFinset _ _).mpr hadj1)) hnw1
    exact hshared ⟨f t₁, t₁, t₂, by omega, hne12, (hIsoiso t₁ ht₁).1, (hIsoiso t₂ ht₂).1,
      hadj1, by rw [heq]; exact hadj2, (hIsoiso t₁ ht₁).2, (hIsoiso t₂ ht₂).2⟩
  obtain ⟨t, htIso, htmiss⟩ := hfind
  have ht3 : G.degree t = 3 := (hIsoiso t htIso).1
  have htiso : ∀ u : Fin 20, G.Adj t u → G.degree u ≠ 3 := (hIsoiso t htIso).2
  -- extract the two non-`w` neighbours of `t`: both degree-`4`, both missing `l₁`
  have hNtcard : (G.neighborFinset t).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, ht3]
  have h2lt : 1 < ((G.neighborFinset t).erase w).card := by
    by_cases hw : w ∈ G.neighborFinset t
    · rw [Finset.card_erase_of_mem hw, hNtcard]
      norm_num
    · rw [Finset.erase_eq_of_notMem hw, hNtcard]
      norm_num
  obtain ⟨k₁, hk1mem, k₂, hk2mem, hk12⟩ := Finset.one_lt_card.mp h2lt
  have hk1Nt : k₁ ∈ G.neighborFinset t := Finset.mem_of_mem_erase hk1mem
  have hk2Nt : k₂ ∈ G.neighborFinset t := Finset.mem_of_mem_erase hk2mem
  have htk1 : G.Adj t k₁ := (G.mem_neighborFinset _ _).mp hk1Nt
  have htk2 : G.Adj t k₂ := (G.mem_neighborFinset _ _).mp hk2Nt
  have hk1w : k₁ ≠ w := Finset.ne_of_mem_erase hk1mem
  have hk2w : k₂ ≠ w := Finset.ne_of_mem_erase hk2mem
  have hdegk1 : G.degree k₁ = 4 := hother4 k₁ (hNsub t htIso hk1Nt) hk1w
  have hdegk2 : G.degree k₂ = 4 := hother4 k₂ (hNsub t htIso hk2Nt) hk2w
  have hk1l1 : ¬G.Adj k₁ l₁ := htmiss k₁ htk1 hk1w
  have hk2l1 : ¬G.Adj k₂ l₁ := htmiss k₂ htk2 hk2w
  -- centre-fullness: neither pair hub touches a centre (all listed neighbours are degree-`3`)
  have hk1c1 : ¬G.Adj k₁ c₁ := by
    intro hadj
    rcases hfull1 k₁ hadj.symm with e | e | e <;> rw [e] at hdegk1 <;> omega
  have hk1c2 : ¬G.Adj k₁ c₂ := by
    intro hadj
    rcases hfull2 k₁ hadj.symm with e | e | e <;> rw [e] at hdegk1 <;> omega
  have hk2c1 : ¬G.Adj k₂ c₁ := by
    intro hadj
    rcases hfull1 k₂ hadj.symm with e | e | e <;> rw [e] at hdegk2 <;> omega
  have hk2c2 : ¬G.Adj k₂ c₂ := by
    intro hadj
    rcases hfull2 k₂ hadj.symm with e | e | e <;> rw [e] at hdegk2 <;> omega
  exact assemble_single_vertex_config G t k₁ k₂ l₁ c₁ c₂ ht3 htiso hdegk1 hdegk2 hk12
    htk1 htk2 hd1 hc1D hc2D ha1 hc12 h1c2 hn1 hk1l1 hk1c1 hk1c2 hk2l1 hk2c1 hk2c2

end N20

end ACMax
