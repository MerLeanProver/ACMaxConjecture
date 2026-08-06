import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.Align
import ACMaxConjecture.SmallCases.N14.TwoHub
import ACMaxConjecture.SmallCases.N14.C5
import ACMaxConjecture.SmallCases.N14.Align6

/-!
# Three-way alignment dichotomy for `e(M) = 2` (`n = 14`)

This file supplies the structural-selection helper feeding the `s = 4` branch of
`exists_twin_signed_cert_fourteen` (in `TwinCert14`).  At `e(M) = 2` (`s = 4`) the matching `M`
on the degree-`3` vertices has exactly two edges; since `M` is `2K₂`-free (`h2k2`), those two edges
share a vertex, so `M` is a single `P₃` cherry `x–y–z`.  The residual graph (`δ ≥ 3`, no good
triangle / `2K₂` / `C₄` / `K_{2,3}`) admits at least one of the three signed-cut configurations
`SingleVertexConfig`, `TwoTwinConfig`, `TwoHubConfig` — the covering combination verified by
enumeration over all `535` such graphs (zero uncovered).

The config predicates are shared with the `s = 6` development (`TwinCert14Align6`).  The dispatch
keystone is `dominating_edge_or_induced_C5`: at `s = 4` the induced-`C₅` branch is impossible (a
`C₅` forces `e(M) ≥ 5`, i.e. `s ≥ 10`), so the structure is the dominating-edge cherry.  At
`e(M) = 2` the residual structure is rigid (`|D| = 8`, six degree-`4` hubs, `e(Hub) = 2`): the
`TwoTwinConfig` path covers the shared-hub-avoids-cherry case, and when the shared hub meets the
cherry the unique cherry-avoiding hub retains `≥ 2` isolated-twin neighbours, again a
`TwoTwinConfig`.  This file is fully proved (no `sorry`).
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Three-way alignment dichotomy at `e(M) = 2` (`s = 4`).**  In the residual regime
(`δ ≥ 3`, no good triangle / `2K₂` / `C₄` / `K_{2,3}`) with `∑_{v∈D}|N v ∩ D| = 4`, the graph
admits one of the three signed-cut configurations.

Dispatch (`dominating_edge_or_induced_C5`): an induced `C₅` of degree-`3` vertices would force
`e(M) ≥ 5` (`s ≥ 10`), contradicting `s = 4`; so `M = G[D]` has a dominating edge (here a `P₃`
cherry).  When the pigeonholed shared hub meets the cherry, the forced rigid structure (`|D| = 8`,
six degree-`4` hubs) supplies a cherry-avoiding hub with `≥ 2` isolated-twin neighbours, giving the
`TwoTwinConfig`.  Fully proved. -/
theorem exists_align_four_config (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 14, ({a, b, c, d, e} : Finset (Fin 14)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 14, G.degree t = 3 ∧ ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3)
    (hs4 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 4) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  -- An `M`-edge exists, since `s = 4 > 0`.
  have hne : ∃ a b : Fin 14, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by
      intro v hv
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact hcon v w hv hw.2 hw.1
    have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := Finset.sum_eq_zero hz
    omega
  rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
  · -- **Dominating-edge branch.**  `M` has a dominating edge `c₁–c₂` (the `P₃` cherry).
    -- We extract a cherry (induced `P₃` of degree-`3` vertices) centred at a dominating endpoint,
    -- and two `M`-isolated twins sharing a degree-`4` hub `h` (pigeonhole, since `≥ 4` twins each
    -- have `≥ 2` degree-`4` hub-neighbours among `≤ 6` hubs).  If that hub avoids the cherry, the
    -- `TwoTwinConfig` is produced; the residual "hub meets cherry" sub-case (another config exists,
    -- enumeration-verified) is the single documented `sorry`.
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hdomprop⟩ := hdom
    obtain ⟨hHub6, hD8⟩ := residual_hub_card_le_six G hm h3
    rw [← hDdef] at hD8
    have hdegD : ∀ v : Fin 14, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
    -- A vertex of the dominating edge has in-`M`-degree `≥ 2` (else `e(M) ≤ 1`, contradicting `4`).
    have hcen : 2 ≤ (G.neighborFinset c₁ ∩ D).card ∨ 2 ≤ (G.neighborFinset c₂ ∩ D).card := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hc2in : c₂ ∈ G.neighborFinset c₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
      have hc1in : c₁ ∈ G.neighborFinset c₂ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
      have h1' : ∀ a ∈ G.neighborFinset c₁ ∩ D, ∀ b ∈ G.neighborFinset c₁ ∩ D, a = b :=
        Finset.card_le_one.mp (by omega)
      have h2' : ∀ a ∈ G.neighborFinset c₂ ∩ D, ∀ b ∈ G.neighborFinset c₂ ∩ D, a = b :=
        Finset.card_le_one.mp (by omega)
      have hzero : ∀ v ∈ D,
          (G.neighborFinset v ∩ D).card ≤ (if v = c₁ ∨ v = c₂ then 1 else 0) := by
        intro v hvD
        by_cases hv : v = c₁ ∨ v = c₂
        · rw [if_pos hv]
          rcases hv with rfl | rfl
          · omega
          · omega
        · rw [if_neg hv, Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          obtain ⟨hvw, hwD⟩ := hw
          have hdom4 := hdomprop v w hvD hwD hvw
          push Not at hv
          rcases hdom4 with e | e | e | e
          · exact hv.1 e
          · exact hv.2 e
          · have hvmem : v ∈ G.neighborFinset c₁ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hvw).symm, hvD⟩
            exact hv.2 (h1' v hvmem c₂ hc2in)
          · have hvmem : v ∈ G.neighborFinset c₂ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hvw).symm, hvD⟩
            exact hv.1 (h2' v hvmem c₁ hc1in)
      have hsumle : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
          ≤ ∑ v ∈ D, (if v = c₁ ∨ v = c₂ then (1 : ℕ) else 0) := Finset.sum_le_sum hzero
      have hrhs : ∑ v ∈ D, (if v = c₁ ∨ v = c₂ then (1 : ℕ) else 0) ≤ 2 := by
        rw [← Finset.card_filter]
        have hsubset : D.filter (fun v => v = c₁ ∨ v = c₂) ⊆ ({c₁, c₂} : Finset (Fin 14)) := by
          intro v hv
          rw [Finset.mem_filter] at hv
          rcases hv.2 with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        calc (D.filter (fun v => v = c₁ ∨ v = c₂)).card
            ≤ ({c₁, c₂} : Finset (Fin 14)).card := Finset.card_le_card hsubset
          _ ≤ 2 := by
              have := Finset.card_insert_le c₁ ({c₂} : Finset (Fin 14))
              simp only [Finset.card_singleton] at this
              omega
      omega
    -- Build the cherry from a degree-`≥ 2` (in `M`) dominating endpoint.
    have mkcherry : ∀ c : Fin 14, c ∈ D → 2 ≤ (G.neighborFinset c ∩ D).card →
        ∃ x y z : Fin 14, x ∈ D ∧ y ∈ D ∧ z ∈ D ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ ¬G.Adj x z := by
      intro c hcD hc2
      obtain ⟨x, hx, z, hz, hxz⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset c ∩ D).card)
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx hz
      obtain ⟨hcx, hxD⟩ := hx
      obtain ⟨hcz, hzD⟩ := hz
      refine ⟨x, c, z, hxD, hcD, hzD, (G.ne_of_adj hcx).symm, G.ne_of_adj hcz, hxz,
        hcx.symm, hcz, ?_⟩
      intro hxzAdj
      exact hT ⟨x, c, z, (G.ne_of_adj hcx).symm, G.ne_of_adj hcz, hxz, hcx.symm, hcz, hxzAdj, by
        rw [hdegD x hxD, hdegD c hcD, hdegD z hzD]; omega⟩
    obtain ⟨x, y, z, hxD, hyD, hzD, hxy_ne, hyz_ne, hxz_ne, hxyA, hyzA, hxzN⟩ :=
      hcen.elim (fun h => mkcherry c₁ hc1D h) (fun h => mkcherry c₂ hc2D h)
    have hdegx : G.degree x = 3 := hdegD x hxD
    have hdegy : G.degree y = 3 := hdegD y hyD
    have hdegz : G.degree z = 3 := hdegD z hzD
    -- The `M`-isolated twin set; at least four twins (`|S| ≤ 3`, `|D| ≥ 8`).
    set Iso : Finset (Fin 14) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
    have hIso4 : 4 ≤ Iso.card := by
      have hnb := nonisolated_component_bound G D hmemD h2k2
      rw [hs4] at hnb
      have hpart := Finset.card_filter_add_card_filter_not (s := D)
        (fun v => (G.neighborFinset v ∩ D).card = 0)
      rw [← hIsodef] at hpart
      omega
    have hIsoprop : ∀ v ∈ Iso,
        G.degree v = 3 ∧ (∀ w : Fin 14, G.Adj v w → G.degree w ≠ 3) := by
      intro v hv
      rw [hIsodef, Finset.mem_filter] at hv
      obtain ⟨hvD, hv0⟩ := hv
      refine ⟨hdegD v hvD, fun w hadj hw3 => ?_⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
      exact hv0 w (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
    -- The degree-`4` hub set has `≤ 6` vertices; each twin has `≥ 2` of them as neighbours.
    set Hub4 : Finset (Fin 14) := Finset.univ.filter (fun h => G.degree h = 4) with hHub4def
    have hHub4card : Hub4.card ≤ 6 := by
      refine le_trans (Finset.card_le_card ?_) hHub6
      intro h hh
      rw [hHub4def, Finset.mem_filter] at hh
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by omega⟩
    have htwo : ∀ v ∈ Iso, 2 ≤ (G.neighborFinset v ∩ Hub4).card := by
      intro v hv
      obtain ⟨hvdeg, hviso⟩ := hIsoprop v hv
      obtain ⟨h₁, h₂, hne, ha1, ha2, hd1, hd2⟩ :=
        isolated_twin_two_deg4_hubs G hm h3 hT hC4 h2k2 v hvdeg hviso
      have hsub : ({h₁, h₂} : Finset (Fin 14)) ⊆ G.neighborFinset v ∩ Hub4 := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha1,
            by rw [hHub4def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hd1⟩⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha2,
            by rw [hHub4def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hd2⟩⟩
      calc 2 = ({h₁, h₂} : Finset (Fin 14)).card := (Finset.card_pair hne).symm
        _ ≤ _ := Finset.card_le_card hsub
    -- Pigeonhole: some degree-`4` hub is adjacent to two distinct twins.
    have hincid : ∃ h ∈ Hub4, 2 ≤ (Iso.filter (fun v => G.Adj v h)).card := by
      by_contra hcon
      push Not at hcon
      have hsum1 : ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card ≤ 6 := by
        calc ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card
            ≤ ∑ _h ∈ Hub4, 1 := Finset.sum_le_sum (fun h hh => by have := hcon h hh; omega)
          _ = Hub4.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ 6 := hHub4card
      have hsum2 : 8 ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
        have hge : 2 * Iso.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
          have := Finset.card_nsmul_le_sum Iso
            (fun v => (G.neighborFinset v ∩ Hub4).card) 2 htwo
          simpa [smul_eq_mul, mul_comm] using this
        omega
      have hswap : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
          = ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card := by
        have hL : ∀ v : Fin 14, (G.neighborFinset v ∩ Hub4).card
            = (Hub4.filter (fun h => G.Adj v h)).card := by
          intro v
          congr 1
          ext h
          simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_filter]
          tauto
        simp_rw [hL, Finset.card_filter]
        rw [Finset.sum_comm]
      omega
    obtain ⟨h, hhHub4, hh2⟩ := hincid
    obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (Iso.filter (fun v => G.Adj v h)).card)
    rw [Finset.mem_filter] at ht1 ht2
    obtain ⟨ht1Iso, hAt1h⟩ := ht1
    obtain ⟨ht2Iso, hAt2h⟩ := ht2
    have hhdeg4 : G.degree h = 4 := by
      rw [hHub4def, Finset.mem_filter] at hhHub4; exact hhHub4.2
    obtain ⟨ht1deg, ht1iso⟩ := hIsoprop t₁ ht1Iso
    obtain ⟨ht2deg, ht2iso⟩ := hIsoprop t₂ ht2Iso
    by_cases havoid : ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z
    · -- The shared hub avoids the cherry: produce `TwoTwinConfig`.
      obtain ⟨hhx, hhy, hhz⟩ := havoid
      right; left
      exact ⟨t₁, t₂, h, x, y, z, ht1deg, ht2deg, by omega, hdegx, hdegy, hdegz,
        hAt1h, hAt2h, hxyA, hyzA,
        (fun hadj => ht1iso x hadj hdegx), (fun hadj => ht1iso y hadj hdegy),
        (fun hadj => ht1iso z hadj hdegz),
        (fun hadj => ht2iso x hadj hdegx), (fun hadj => ht2iso y hadj hdegy),
        (fun hadj => ht2iso z hadj hdegz),
        hhx, hhy, hhz, ht12,
        (by rintro rfl; exact ht1iso y hxyA hdegy),
        (by rintro rfl; exact ht1iso z hyzA hdegz),
        (by rintro rfl; exact ht1iso y hyzA.symm hdegy),
        (by rintro rfl; exact ht2iso y hxyA hdegy),
        (by rintro rfl; exact ht2iso z hyzA hdegz),
        (by rintro rfl; exact ht2iso y hyzA.symm hdegy),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        hxy_ne, hyz_ne, hxz_ne⟩
    · -- **Shared hub meets the cherry.**  At `e(M) = 2` the residual structure is rigid: a double
      -- count forces `|D| = 8`, all six non-`D` vertices of degree exactly `4`, and the three
      -- `M`-non-isolated vertices are exactly the cherry `x, y, z`.  The cherry meets at most five
      -- hubs (`x, z` two each, `y` one), so a sixth, cherry-avoiding hub `h₆` exists; the hub-edge
      -- count `∑_{w∉D}|N w ∩ Dᶜ| = 4` bounds its hub-neighbours by two, leaving `≥ 2` isolated-twin
      -- neighbours — a `TwoTwinConfig` directly (no re-selection needed).
      have hsum48 : ∑ v : Fin 14, G.degree v = 48 := by
        rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
      have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
        rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
      have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 48 := by
        rw [Finset.sum_add_sum_compl]; exact hsum48
      have hpart : ∀ w : Fin 14,
          (G.neighborFinset w ∩ Dᶜ).card + (G.neighborFinset w ∩ D).card = G.degree w := by
        intro w
        have heq : G.neighborFinset w ∩ Dᶜ = G.neighborFinset w \ D := by
          ext a; simp [Finset.mem_sdiff, Finset.mem_compl]
        rw [heq]
        have := Finset.card_sdiff_add_card_inter (G.neighborFinset w) D
        rw [G.card_neighborFinset_eq_degree] at this
        exact this
      have hAs : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
          + ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 3 * D.card := by
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun v _ => hpart v), hsumD]
      have hcross := cross_count_fourteen G D Dᶜ
      have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
        intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
      have hDcle : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dᶜ, G.degree w := by
        apply Finset.sum_le_sum; intro w _
        calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = G.degree w := G.card_neighborFinset_eq_degree w
      have hDcge : 4 * Dᶜ.card ≤ ∑ w ∈ Dᶜ, G.degree w := by
        have := Finset.card_nsmul_le_sum Dᶜ (fun w => G.degree w) 4 hDcdeg
        simpa [smul_eq_mul, mul_comm] using this
      have hcc : D.card + Dᶜ.card = 14 := by
        have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
      have hDcard8 : D.card = 8 := by omega
      have hDccard6 : Dᶜ.card = 6 := by omega
      have hsumDc24 : ∑ w ∈ Dᶜ, G.degree w = 24 := by omega
      have hdeg4all : ∀ w ∈ Dᶜ, G.degree w = 4 := by
        intro w hw
        by_contra hne5
        have hge5 : 5 ≤ G.degree w := by have := hDcdeg w hw; omega
        have hsplit := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
        have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
          have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
            fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
          have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
          simpa [smul_eq_mul, mul_comm] using this
        have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
        omega
      have hsumDcD20 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card = 20 := by
        rw [← hcross]; omega
      have hsumDcDc4 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 4 := by
        have hsumeq : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ Dᶜ).card
            + (G.neighborFinset w ∩ D).card) = ∑ w ∈ Dᶜ, G.degree w :=
          Finset.sum_congr rfl (fun w _ => hpart w)
        rw [Finset.sum_add_distrib] at hsumeq
        omega
      -- The `M`-non-isolated vertices are exactly the cherry `{x, y, z}`.
      have hxyzcard : ({x, y, z} : Finset (Fin 14)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
          Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hsubNI : ({x, y, z} : Finset (Fin 14))
          ⊆ D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [Finset.mem_filter]
        rcases hw with rfl | rfl | rfl
        · exact ⟨hxD, Finset.card_ne_zero.mpr
            ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hxyA, hyD⟩⟩⟩
        · exact ⟨hyD, Finset.card_ne_zero.mpr
            ⟨x, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w x).mpr hxyA.symm, hxD⟩⟩⟩
        · exact ⟨hzD, Finset.card_ne_zero.mpr
            ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hyzA.symm, hyD⟩⟩⟩
      have hNIcard3 : (D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0)).card ≤ 3 := by
        have hnb := nonisolated_component_bound G D hmemD h2k2
        rw [hs4] at hnb; omega
      have hNIeq : ({x, y, z} : Finset (Fin 14))
          = D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
        Finset.eq_of_subset_of_card_le hsubNI (by rw [hxyzcard]; exact hNIcard3)
      have hDsplit : ∀ w : Fin 14, w ∈ D → w ∉ ({x, y, z} : Finset (Fin 14)) →
          (G.neighborFinset w ∩ D).card = 0 := by
        intro w hwD hwxyz
        by_contra hc
        have hmem : w ∈ D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
          Finset.mem_filter.mpr ⟨hwD, hc⟩
        rw [← hNIeq] at hmem
        exact hwxyz hmem
      -- The cherry meets at most five hubs, so a cherry-avoiding hub `h₆` remains.
      have hNxD1 : 1 ≤ (G.neighborFinset x ∩ D).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hxyA, hyD⟩⟩
      have hNzD1 : 1 ≤ (G.neighborFinset z ∩ D).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z y).mpr hyzA.symm, hyD⟩⟩
      have hNyD2 : 2 ≤ (G.neighborFinset y ∩ D).card := by
        have hsub : ({x, z} : Finset (Fin 14)) ⊆ G.neighborFinset y ∩ D := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hxyA.symm, hxD⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hyzA, hzD⟩
        calc 2 = ({x, z} : Finset (Fin 14)).card := (Finset.card_pair hxz_ne).symm
          _ ≤ _ := Finset.card_le_card hsub
      have hNxDc : (G.neighborFinset x ∩ Dᶜ).card ≤ 2 := by
        have := hpart x; rw [hdegx] at this; omega
      have hNyDc : (G.neighborFinset y ∩ Dᶜ).card ≤ 1 := by
        have := hpart y; rw [hdegy] at this; omega
      have hNzDc : (G.neighborFinset z ∩ Dᶜ).card ≤ 2 := by
        have := hpart z; rw [hdegz] at this; omega
      have hBad : (Dᶜ.filter (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)).card ≤ 5 := by
        have hsub : Dᶜ.filter (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)
            ⊆ (G.neighborFinset x ∩ Dᶜ) ∪ (G.neighborFinset y ∩ Dᶜ)
              ∪ (G.neighborFinset z ∩ Dᶜ) := by
          intro w hw; rw [Finset.mem_filter] at hw
          obtain ⟨hwDc, hor⟩ := hw
          rcases hor with hax | hay | haz
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x w).mpr hax.symm, hwDc⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hay.symm, hwDc⟩))
          · exact Finset.mem_union_right _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z w).mpr haz.symm, hwDc⟩)
        have houter := Finset.card_union_le ((G.neighborFinset x ∩ Dᶜ)
          ∪ (G.neighborFinset y ∩ Dᶜ)) (G.neighborFinset z ∩ Dᶜ)
        have hinner := Finset.card_union_le (G.neighborFinset x ∩ Dᶜ) (G.neighborFinset y ∩ Dᶜ)
        refine le_trans (Finset.card_le_card hsub) ?_
        omega
      have hexists : ∃ h6 ∈ Dᶜ, ¬(G.Adj h6 x ∨ G.Adj h6 y ∨ G.Adj h6 z) := by
        by_contra hcon
        push Not at hcon
        have hsub : Dᶜ ⊆ Dᶜ.filter (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z) := by
          intro w hw; exact Finset.mem_filter.mpr ⟨hw, hcon w hw⟩
        have := Finset.card_le_card hsub
        omega
      obtain ⟨h6, hh6Dc, hh6avoid⟩ := hexists
      push Not at hh6avoid
      obtain ⟨hh6x, hh6y, hh6z⟩ := hh6avoid
      have hh6deg4 : G.degree h6 = 4 := hdeg4all h6 hh6Dc
      -- `h₆` has at most two hub-neighbours (symmetry of `∑_{Dᶜ}|N w ∩ Dᶜ| = 4`).
      have hSymm : (G.neighborFinset h6 ∩ Dᶜ).card ≤ 2 := by
        have hsplit := Finset.add_sum_erase Dᶜ
          (fun w => (G.neighborFinset w ∩ Dᶜ).card) hh6Dc
        have hsub : G.neighborFinset h6 ∩ Dᶜ ⊆ Dᶜ.erase h6 := by
          intro w hw; rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hw.1).symm, hw.2⟩
        have hge1 : ∀ w ∈ G.neighborFinset h6 ∩ Dᶜ,
            1 ≤ (G.neighborFinset w ∩ Dᶜ).card := by
          intro w hw; rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          exact Finset.card_pos.mpr ⟨h6,
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w h6).mpr hw.1.symm, hh6Dc⟩⟩
        have hlow : (G.neighborFinset h6 ∩ Dᶜ).card
            ≤ ∑ w ∈ Dᶜ.erase h6, (G.neighborFinset w ∩ Dᶜ).card := by
          calc (G.neighborFinset h6 ∩ Dᶜ).card
              = ∑ _w ∈ G.neighborFinset h6 ∩ Dᶜ, 1 := by
                rw [Finset.sum_const, smul_eq_mul, mul_one]
            _ ≤ ∑ w ∈ G.neighborFinset h6 ∩ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card :=
                Finset.sum_le_sum hge1
            _ ≤ ∑ w ∈ Dᶜ.erase h6, (G.neighborFinset w ∩ Dᶜ).card :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        omega
      have hh6D2 : 2 ≤ (G.neighborFinset h6 ∩ D).card := by
        have := hpart h6; rw [hh6deg4] at this; omega
      obtain ⟨t1, ht1, t2, ht2, ht12ne⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset h6 ∩ D).card)
      rw [Finset.mem_inter, G.mem_neighborFinset] at ht1 ht2
      obtain ⟨hh6t1, ht1D⟩ := ht1
      obtain ⟨hh6t2, ht2D⟩ := ht2
      have ht1nx : t1 ≠ x := fun he => hh6x (he ▸ hh6t1)
      have ht1ny : t1 ≠ y := fun he => hh6y (he ▸ hh6t1)
      have ht1nz : t1 ≠ z := fun he => hh6z (he ▸ hh6t1)
      have ht2nx : t2 ≠ x := fun he => hh6x (he ▸ hh6t2)
      have ht2ny : t2 ≠ y := fun he => hh6y (he ▸ hh6t2)
      have ht2nz : t2 ≠ z := fun he => hh6z (he ▸ hh6t2)
      have ht1iso0 : (G.neighborFinset t1 ∩ D).card = 0 :=
        hDsplit t1 ht1D (by simp [ht1nx, ht1ny, ht1nz])
      have ht2iso0 : (G.neighborFinset t2 ∩ D).card = 0 :=
        hDsplit t2 ht2D (by simp [ht2nx, ht2ny, ht2nz])
      have ht1deg : G.degree t1 = 3 := hdegD t1 ht1D
      have ht2deg : G.degree t2 = 3 := hdegD t2 ht2D
      have ht1iso : ∀ w : Fin 14, G.Adj t1 w → G.degree w ≠ 3 := by
        intro w hadj hw3
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at ht1iso0
        exact ht1iso0 w (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset t1 w).mpr hadj, (hmemD w).mpr hw3⟩)
      have ht2iso : ∀ w : Fin 14, G.Adj t2 w → G.degree w ≠ 3 := by
        intro w hadj hw3
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at ht2iso0
        exact ht2iso0 w (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset t2 w).mpr hadj, (hmemD w).mpr hw3⟩)
      right; left
      exact ⟨t1, t2, h6, x, y, z, ht1deg, ht2deg, by omega, hdegx, hdegy, hdegz,
        hh6t1.symm, hh6t2.symm, hxyA, hyzA,
        (fun ha => ht1iso x ha hdegx), (fun ha => ht1iso y ha hdegy),
        (fun ha => ht1iso z ha hdegz),
        (fun ha => ht2iso x ha hdegx), (fun ha => ht2iso y ha hdegy),
        (fun ha => ht2iso z ha hdegz),
        hh6x, hh6y, hh6z, ht12ne,
        ht1nx, ht1ny, ht1nz, ht2nx, ht2ny, ht2nz,
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        hxy_ne, hyz_ne, hxz_ne⟩
  · -- **Induced-`C₅` branch is impossible at `e(M) = 2`.**  Each cycle vertex has two `D`-neighbours
    -- (its cycle neighbours), so contributes `≥ 2` to `s`; the five together force `s ≥ 10 > 4`.
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_fourteen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 14, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 14)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

end N14

end ACMax
