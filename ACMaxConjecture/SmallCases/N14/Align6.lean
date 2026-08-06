import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.Align
import ACMaxConjecture.SmallCases.N14.TwoHub
import ACMaxConjecture.SmallCases.N14.C5
import ACMaxConjecture.SmallCases.N14.Align6Dense

/-!
# Three-way alignment dichotomy for `e(M) = 3` (`n = 14`)

This file supplies the structural-selection helper feeding the `s = 6` branch of
`exists_twin_signed_cert_fourteen` (in `TwinCert14`).  At `e(M) = 3` the residual graph
(`δ ≥ 3`, no good triangle / `2K₂` / `C₄` / `K_{2,3}`) admits at least one of three signed-cut
configurations — `SingleVertexConfig`, `TwoTwinConfig`, `TwoHubConfig` — the covering combination
verified by enumeration over all 4229 such graphs.

The three config predicates live here (so both this file and `TwinCert14` can reference them).
The dispatch keystone is `dominating_edge_or_induced_C5`: at `s = 6` the induced-`C₅` branch is
impossible (a `C₅` forces `e(M) ≥ 5`), so the structure is the dominating-edge `M` (a claw `K_{1,3}`
or a path `P₄`).  The remaining dominating-edge alignment — selecting a config whose cherry avoids
the shared hub — is the analogue of the `n = 13` `exists_two_hub_or_two_twin_config` development and
is left as the single documented `sorry`.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **The single-vertex signed-cut configuration** for the `e(M) = 3` regime: a degree-`3` vertex
`v` adjacent to two hubs `h₁, h₂`, and a cherry (induced `P₃`) `x–y–z` of degree-`3` vertices, with
the combined cross/hub side condition.  Consumed by `single_vertex_cut_certificate`. -/
def SingleVertexConfig (G : SimpleGraph (Fin 14)) : Prop :=
  ∃ v h₁ h₂ x y z : Fin 14,
    G.degree v = 3 ∧ G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
    G.Adj v h₁ ∧ G.Adj v h₂ ∧ G.Adj x y ∧ G.Adj y z ∧ ¬G.Adj x z ∧
    2 * (∑ p ∈ ({v, h₁, h₂} : Finset (Fin 14)),
        (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 14))).card)
        + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * (if G.Adj h₁ h₂ then 1 else 0) ∧
    h₁ ≠ h₂ ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z ∧
    h₁ ≠ x ∧ h₁ ≠ y ∧ h₁ ≠ z ∧ h₂ ≠ x ∧ h₂ ≠ y ∧ h₂ ≠ z ∧
    x ≠ y ∧ y ≠ z ∧ x ≠ z

/-- **The 2-twin signed-cut configuration** for the `e(M) = 3` regime: two `M`-isolated degree-`3`
twins `t₁, t₂` sharing a hub `h` of degree `≤ 5`, against a cherry `x–y–z` avoiding `h` and the
twins.  Consumed by `two_twin_cut_certificate_fourteen`. -/
def TwoTwinConfig (G : SimpleGraph (Fin 14)) : Prop :=
  ∃ t₁ t₂ h x y z : Fin 14,
    G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.degree h ≤ 5 ∧
    G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
    G.Adj t₁ h ∧ G.Adj t₂ h ∧ G.Adj x y ∧ G.Adj y z ∧
    ¬G.Adj t₁ x ∧ ¬G.Adj t₁ y ∧ ¬G.Adj t₁ z ∧
    ¬G.Adj t₂ x ∧ ¬G.Adj t₂ y ∧ ¬G.Adj t₂ z ∧
    ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z ∧
    t₁ ≠ t₂ ∧ t₁ ≠ x ∧ t₁ ≠ y ∧ t₁ ≠ z ∧ t₂ ≠ x ∧ t₂ ≠ y ∧ t₂ ≠ z ∧
    h ≠ x ∧ h ≠ y ∧ h ≠ z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z

/-- **The two-hub opposite-twin signed-cut configuration** for the `e(M) ≤ 3` regime (identical to
the conclusion of `two_hub_config_fourteen`).  Consumed by `two_hub_opposite_twin_cert`. -/
def TwoHubConfig (G : SimpleGraph (Fin 14)) : Prop :=
  ∃ h₁ h₂ a b c d : Fin 14,
    G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
    G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
    G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj d h₂ ∧
    ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ d ∧
    ¬G.Adj a h₂ ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧
    ¬G.Adj b h₂ ∧ ¬G.Adj b c ∧ ¬G.Adj b d ∧
    h₁ ≠ h₂ ∧ h₁ ≠ a ∧ h₁ ≠ b ∧ h₁ ≠ c ∧ h₁ ≠ d ∧
    h₂ ≠ a ∧ h₂ ≠ b ∧ h₂ ≠ c ∧ h₂ ≠ d ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- **Three-way alignment dichotomy at `e(M) = 3` (`s = 6`).**  In the residual regime
(`δ ≥ 3`, no good triangle / `2K₂` / `C₄` / `K_{2,3}`) with `∑_{v∈D}|N v ∩ D| = 6`, the graph
admits one of the three signed-cut configurations.

Dispatch (`dominating_edge_or_induced_C5`): an induced `C₅` of degree-`3` vertices would force
`e(M) ≥ 5` (`s ≥ 10`), contradicting `s = 6`; so `M = G[D]` has a dominating edge (a claw `K_{1,3}`
or path `P₄`).  The dominating-edge alignment — selecting a config whose cherry avoids the shared
hub, the analogue of the `n = 13` `exists_two_hub_or_two_twin_config` (≈ 3300 lines) — is the single
documented `sorry`. -/
theorem exists_align_six_config (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 14, ({a, b, c, d, e} : Finset (Fin 14)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 14, G.degree t = 3 ∧ ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3)
    (hs6 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 6) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  -- An `M`-edge exists, since `s = 6 > 0`.
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
  · -- **Dominating-edge branch.**  `M` has a dominating edge `c₁–c₂` (claw `K_{1,3}` or path `P₄`).
    -- We extract a cherry (induced `P₃` of degree-`3` vertices) centred at a dominating endpoint,
    -- and two `M`-isolated twins sharing a degree-`4` hub `h` (pigeonhole, since `≥ 4` twins each
    -- have `≥ 2` degree-`4` hub-neighbours among `≤ 6` hubs).  If that hub avoids the cherry, the
    -- `TwoTwinConfig` is produced; the residual "hub meets cherry" sub-case (another config exists,
    -- enumeration-verified) is the single documented `sorry`.
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hdomprop⟩ := hdom
    obtain ⟨hHub6, hD8⟩ := residual_hub_card_le_six G hm h3
    rw [← hDdef] at hD8
    have hdegD : ∀ v : Fin 14, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
    -- A vertex of the dominating edge has in-`M`-degree `≥ 2` (else `e(M) ≤ 1`, contradicting `6`).
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
    -- The `M`-isolated twin set; at least four twins (`|S| ≤ 4`, `|D| ≥ 8`).
    set Iso : Finset (Fin 14) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
    have hIso4 : 4 ≤ Iso.card := by
      have hnb := nonisolated_component_bound G D hmemD h2k2
      rw [hs6] at hnb
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
    · -- **Shared hub meets the cherry.**  A double count pins `|D| ∈ {8, 9}`.  When `|D| = 9` the
      -- five hubs (four of degree `4`, one of degree `5`) are pairwise non-adjacent, so a
      -- cherry-avoiding hub (one exists: the cherry meets `≤ 4` hubs) keeps all but one of its
      -- neighbours in the isolated-twin set, giving a `TwoTwinConfig` directly.  The dense regime
      -- `|D| = 8` (six degree-`4` hubs, `e(Hub) = 3`) is the genuine residual — the analogue of the
      -- `n = 13` `exists_two_hub_or_two_twin_config` — isolated as the single documented `sorry`.
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
      have hsumDcD : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card = 3 * D.card - 6 := by
        rw [← hcross]; omega
      have hD9le : D.card ≤ 9 := by omega
      by_cases hD9 : D.card = 9
      · -- **`|D| = 9`: the five hubs are pairwise non-adjacent.**
        have hDccard5 : Dᶜ.card = 5 := by omega
        have hsumDc21 : ∑ w ∈ Dᶜ, G.degree w = 21 := by omega
        have hsumDcDc0 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 0 := by
          have hsumeq : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ Dᶜ).card
              + (G.neighborFinset w ∩ D).card) = ∑ w ∈ Dᶜ, G.degree w :=
            Finset.sum_congr rfl (fun w _ => hpart w)
          rw [Finset.sum_add_distrib] at hsumeq
          omega
        have hindep : ∀ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 0 := by
          intro w hw
          by_contra hne0
          have hpos : 0 < (G.neighborFinset w ∩ Dᶜ).card := Nat.pos_of_ne_zero hne0
          have hle := Finset.single_le_sum
            (f := fun w => (G.neighborFinset w ∩ Dᶜ).card) (fun i _ => Nat.zero_le _) hw
          omega
        have hdegle5 : ∀ w ∈ Dᶜ, G.degree w ≤ 5 := by
          intro w hw
          by_contra hgt
          rw [not_le] at hgt
          have hsplit := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
          have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
            have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
              fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
            have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
            simpa [smul_eq_mul, mul_comm] using this
          have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
          omega
        set NI : Finset (Fin 14) :=
          D.filter (fun w => ¬(G.neighborFinset w ∩ D).card = 0) with hNIdef
        have hsumNI6 : ∑ w ∈ NI, (G.neighborFinset w ∩ D).card = 6 := by
          have hsplit := Finset.sum_filter_add_sum_filter_not D
            (fun w => ¬(G.neighborFinset w ∩ D).card = 0)
            (fun w => (G.neighborFinset w ∩ D).card)
          rw [hs6] at hsplit
          have hzero : ∑ w ∈ D.filter (fun w => ¬¬(G.neighborFinset w ∩ D).card = 0),
              (G.neighborFinset w ∩ D).card = 0 := by
            apply Finset.sum_eq_zero; intro w hw
            rw [Finset.mem_filter, not_not] at hw; exact hw.2
          rw [hzero, add_zero, ← hNIdef] at hsplit
          exact hsplit
        have hNIcard4 : NI.card ≤ 4 := by
          have hnb := nonisolated_component_bound G D hmemD h2k2
          rw [hs6, ← hNIdef] at hnb; omega
        have hxyzcard : ({x, y, z} : Finset (Fin 14)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
            Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
        have hNxD1 : 1 ≤ (G.neighborFinset x ∩ D).card :=
          Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset x y).mpr hxyA, hyD⟩⟩
        have hNzD1 : 1 ≤ (G.neighborFinset z ∩ D).card :=
          Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset z y).mpr hyzA.symm, hyD⟩⟩
        have hNyD2 : 2 ≤ (G.neighborFinset y ∩ D).card := by
          have hsub : ({x, z} : Finset (Fin 14)) ⊆ G.neighborFinset y ∩ D := by
            intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hxyA.symm, hxD⟩
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hyzA, hzD⟩
          calc 2 = ({x, z} : Finset (Fin 14)).card := (Finset.card_pair hxz_ne).symm
            _ ≤ _ := Finset.card_le_card hsub
        have hsubNI : ({x, y, z} : Finset (Fin 14)) ⊆ NI := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rw [hNIdef, Finset.mem_filter]
          rcases hw with rfl | rfl | rfl
          · exact ⟨hxD, by have := hNxD1; omega⟩
          · exact ⟨hyD, by have := hNyD2; omega⟩
          · exact ⟨hzD, by have := hNzD1; omega⟩
        have hsd1 : (NI \ ({x, y, z} : Finset (Fin 14))).card ≤ 1 := by
          have hinter : NI ∩ ({x, y, z} : Finset (Fin 14)) = ({x, y, z} : Finset (Fin 14)) :=
            Finset.inter_eq_right.mpr hsubNI
          have hcs := Finset.card_sdiff_add_card_inter NI ({x, y, z} : Finset (Fin 14))
          rw [hinter, hxyzcard] at hcs
          omega
        -- Every `NI`-vertex outside the cherry meets the cherry in at most one vertex.
        have hmeet : ∀ c ∈ NI \ ({x, y, z} : Finset (Fin 14)),
            (G.neighborFinset c ∩ D).card ≤ 1 := by
          intro c hc
          rw [Finset.mem_sdiff] at hc
          obtain ⟨hcNI, hcxyz⟩ := hc
          have hcD : c ∈ D := by rw [hNIdef, Finset.mem_filter] at hcNI; exact hcNI.1
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcxyz
          obtain ⟨hcx, hcy, hcz⟩ := hcxyz
          have hsub4 : ({x, y, z, c} : Finset (Fin 14)) ⊆ NI := by
            intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl | rfl
            · exact hsubNI (by simp)
            · exact hsubNI (by simp)
            · exact hsubNI (by simp)
            · exact hcNI
          have hcard4 : ({x, y, z, c} : Finset (Fin 14)).card = 4 :=
            card_four_fourteen x y z c hxy_ne hxz_ne (Ne.symm hcx) hyz_ne
              (Ne.symm hcy) (Ne.symm hcz)
          have hNIeq : NI = ({x, y, z, c} : Finset (Fin 14)) :=
            (Finset.eq_of_subset_of_card_le hsub4 (by rw [hcard4]; exact hNIcard4)).symm
          have hsubnbr : G.neighborFinset c ∩ D ⊆ ({x, y, z} : Finset (Fin 14)) := by
            intro w hw
            rw [Finset.mem_inter, G.mem_neighborFinset] at hw
            obtain ⟨hcw, hwD⟩ := hw
            have hwNI : w ∈ NI := by
              rw [hNIdef, Finset.mem_filter]
              exact ⟨hwD, Finset.card_ne_zero.mpr ⟨c, Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset w c).mpr hcw.symm, hcD⟩⟩⟩
            rw [hNIeq] at hwNI
            simp only [Finset.mem_insert, Finset.mem_singleton] at hwNI
            have hwc : w ≠ c := (G.ne_of_adj hcw).symm
            rcases hwNI with h | h | h | h
            · simp [h]
            · simp [h]
            · simp [h]
            · exact absurd h hwc
          have hdegc : G.degree c = 3 := hdegD c hcD
          have e1 : ¬(G.Adj c x ∧ G.Adj c y) := by
            rintro ⟨h1, h2⟩
            exact hT ⟨c, x, y, hcx, hxy_ne, hcy, h1, hxyA, h2, by omega⟩
          have e2 : ¬(G.Adj c y ∧ G.Adj c z) := by
            rintro ⟨h1, h2⟩
            exact hT ⟨c, y, z, hcy, hyz_ne, hcz, h1, hyzA, h2, by omega⟩
          have e3 : ¬(G.Adj c x ∧ G.Adj c z) := by
            rintro ⟨h1, h2⟩
            by_cases hcyA : G.Adj c y
            · exact hT ⟨c, x, y, hcx, hxy_ne, hcy, h1, hxyA, hcyA, by omega⟩
            · exact hC4 ⟨c, x, y, z,
                card_four_fourteen c x y z hcx hcy hcz hxy_ne hxz_ne hyz_ne,
                h1, hxyA, hyzA, h2.symm, hcyA, hxzN, by omega⟩
          by_contra hcon
          rw [not_le] at hcon
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcon
          have haxyz := hsubnbr ha
          have hbxyz := hsubnbr hb
          rw [Finset.mem_inter, G.mem_neighborFinset] at ha hb
          obtain ⟨ha1, -⟩ := ha
          obtain ⟨hb1, -⟩ := hb
          simp only [Finset.mem_insert, Finset.mem_singleton] at haxyz hbxyz
          rcases haxyz with rfl | rfl | rfl <;> rcases hbxyz with rfl | rfl | rfl
          · exact hab rfl
          · exact e1 ⟨ha1, hb1⟩
          · exact e3 ⟨ha1, hb1⟩
          · exact e1 ⟨hb1, ha1⟩
          · exact hab rfl
          · exact e2 ⟨ha1, hb1⟩
          · exact e3 ⟨hb1, ha1⟩
          · exact e2 ⟨hb1, ha1⟩
          · exact hab rfl
        -- The cherry meets at most four hubs, so a cherry-avoiding hub remains.
        have hcherry5 : 5 ≤ (G.neighborFinset x ∩ D).card + (G.neighborFinset y ∩ D).card
            + (G.neighborFinset z ∩ D).card := by
          have hsum3 : (G.neighborFinset x ∩ D).card + (G.neighborFinset y ∩ D).card
              + (G.neighborFinset z ∩ D).card
              = ∑ c ∈ ({x, y, z} : Finset (Fin 14)), (G.neighborFinset c ∩ D).card := by
            rw [Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
              Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton, add_assoc]
          have hsd := Finset.sum_sdiff (f := fun c => (G.neighborFinset c ∩ D).card) hsubNI
          rw [hsumNI6] at hsd
          have hrest1 : ∑ c ∈ NI \ ({x, y, z} : Finset (Fin 14)),
              (G.neighborFinset c ∩ D).card ≤ 1 := by
            calc ∑ c ∈ NI \ ({x, y, z} : Finset (Fin 14)), (G.neighborFinset c ∩ D).card
                ≤ ∑ _c ∈ NI \ ({x, y, z} : Finset (Fin 14)), 1 := Finset.sum_le_sum hmeet
              _ = (NI \ ({x, y, z} : Finset (Fin 14))).card := by
                  rw [Finset.sum_const, smul_eq_mul, mul_one]
              _ ≤ 1 := hsd1
          omega
        have hNxDc : (G.neighborFinset x ∩ Dᶜ).card + (G.neighborFinset x ∩ D).card = 3 := by
          have := hpart x; rw [hdegx] at this; exact this
        have hNyDc : (G.neighborFinset y ∩ Dᶜ).card + (G.neighborFinset y ∩ D).card = 3 := by
          have := hpart y; rw [hdegy] at this; exact this
        have hNzDc : (G.neighborFinset z ∩ Dᶜ).card + (G.neighborFinset z ∩ D).card = 3 := by
          have := hpart z; rw [hdegz] at this; exact this
        have hBad : (Dᶜ.filter (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)).card ≤ 4 := by
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
        have hexists : ∃ hb ∈ Dᶜ, ¬(G.Adj hb x ∨ G.Adj hb y ∨ G.Adj hb z) := by
          by_contra hcon
          push Not at hcon
          have hsub : Dᶜ ⊆ Dᶜ.filter (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z) := by
            intro w hw; exact Finset.mem_filter.mpr ⟨hw, hcon w hw⟩
          have := Finset.card_le_card hsub
          omega
        obtain ⟨hb, hhbDc, hhbavoid⟩ := hexists
        push Not at hhbavoid
        obtain ⟨hhbx, hhby, hhbz⟩ := hhbavoid
        have hhbdeg4 : 4 ≤ G.degree hb := hDcdeg hb hhbDc
        -- `hb` lies in an independent hub, so its neighbours are all in `D`.
        have hindep_hb : (G.neighborFinset hb ∩ Dᶜ).card = 0 := hindep hb hhbDc
        have hNhbsubD : G.neighborFinset hb ⊆ D := by
          intro w hw
          by_contra hwD
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hindep_hb
          exact hindep_hb w (Finset.mem_inter.mpr ⟨hw, Finset.mem_compl.mpr hwD⟩)
        have hNhbD : (G.neighborFinset hb ∩ D).card = G.degree hb := by
          rw [Finset.inter_eq_left.mpr hNhbsubD, G.card_neighborFinset_eq_degree]
        have hhbsplit : G.neighborFinset hb ∩ D
            ⊆ (G.neighborFinset hb ∩ Iso) ∪ (NI \ ({x, y, z} : Finset (Fin 14))) := by
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          obtain ⟨hhbw, hwD⟩ := hw
          by_cases hwIso : w ∈ Iso
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset hb w).mpr hhbw, hwIso⟩)
          · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
            · rw [hNIdef, Finset.mem_filter]
              refine ⟨hwD, fun h0 => hwIso ?_⟩
              rw [hIsodef, Finset.mem_filter]; exact ⟨hwD, h0⟩
            · intro hwxyz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hwxyz
              rcases hwxyz with rfl | rfl | rfl
              · exact hhbx hhbw
              · exact hhby hhbw
              · exact hhbz hhbw
        have hIso2 : 2 ≤ (G.neighborFinset hb ∩ Iso).card := by
          have hcardun := Finset.card_le_card hhbsplit
          have huni := Finset.card_union_le (G.neighborFinset hb ∩ Iso)
            (NI \ ({x, y, z} : Finset (Fin 14)))
          omega
        obtain ⟨s1, hs1, s2, hs2, hs12⟩ :=
          Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset hb ∩ Iso).card)
        rw [Finset.mem_inter, G.mem_neighborFinset] at hs1 hs2
        obtain ⟨hhbs1, hs1Iso⟩ := hs1
        obtain ⟨hhbs2, hs2Iso⟩ := hs2
        obtain ⟨hs1deg, hs1iso⟩ := hIsoprop s1 hs1Iso
        obtain ⟨hs2deg, hs2iso⟩ := hIsoprop s2 hs2Iso
        have hs1nx : s1 ≠ x := by
          rintro rfl; rw [hIsodef, Finset.mem_filter] at hs1Iso; have := hs1Iso.2; omega
        have hs1ny : s1 ≠ y := by
          rintro rfl; rw [hIsodef, Finset.mem_filter] at hs1Iso; have := hs1Iso.2; omega
        have hs1nz : s1 ≠ z := by
          rintro rfl; rw [hIsodef, Finset.mem_filter] at hs1Iso; have := hs1Iso.2; omega
        have hs2nx : s2 ≠ x := by
          rintro rfl; rw [hIsodef, Finset.mem_filter] at hs2Iso; have := hs2Iso.2; omega
        have hs2ny : s2 ≠ y := by
          rintro rfl; rw [hIsodef, Finset.mem_filter] at hs2Iso; have := hs2Iso.2; omega
        have hs2nz : s2 ≠ z := by
          rintro rfl; rw [hIsodef, Finset.mem_filter] at hs2Iso; have := hs2Iso.2; omega
        right; left
        exact ⟨s1, s2, hb, x, y, z, hs1deg, hs2deg, hdegle5 hb hhbDc, hdegx, hdegy, hdegz,
          hhbs1.symm, hhbs2.symm, hxyA, hyzA,
          (fun ha => hs1iso x ha hdegx), (fun ha => hs1iso y ha hdegy),
          (fun ha => hs1iso z ha hdegz),
          (fun ha => hs2iso x ha hdegx), (fun ha => hs2iso y ha hdegy),
          (fun ha => hs2iso z ha hdegz),
          hhbx, hhby, hhbz, hs12,
          hs1nx, hs1ny, hs1nz, hs2nx, hs2ny, hs2nz,
          (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
          hxy_ne, hyz_ne, hxz_ne⟩
      · -- **`|D| = 8`: six degree-`4` hubs with `e(Hub) = 3`.**  The genuine dense residual, handled
        -- by the self-contained `exists_align_six_config_dense` (file `TwinCert14Align6Dense`).
        exact exists_align_six_config_dense G hm h3 hT h2k2 hC4 hK23 hiso hs6 (by rw [← hDdef]; omega)
  · -- **Induced-`C₅` branch is impossible at `e(M) = 3`.**  Each cycle vertex has two `D`-neighbours
    -- (its cycle neighbours), so contributes `≥ 2` to `s`; the five together force `s ≥ 10 > 6`.
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
