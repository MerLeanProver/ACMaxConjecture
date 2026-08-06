import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N15.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N15.Dense
import ACMaxConjecture.SmallCases.N15.Align8Helpers
import ACMaxConjecture.SmallCases.N15.TwoHubSelectD4
import ACMaxConjecture.SmallCases.N15.HubTriangle

/-!
# Structural-alignment dichotomies for the `n = 15` twin certificate (open pieces)

This file isolates the *genuinely-new* combinatorial-enumeration content of the `n = 15`
twin-based signed-cut dichotomy.  The boundary certificates and `_to_cut` wrappers are fully
proved in `TwinCert15Cert`; what remains is the **structural-selection** step: from the residual
hypotheses (`δ ≥ 3`, no good triangle / `2K₂` / `C₄` / `K_{2,3}`, an `M`-isolated degree-`3`
vertex) and the value of `e(M)`, produce one of the three signed-cut configurations.

Mirroring the proved `n = 14` development (`two_hub_config_fourteen`, `exists_align_four_config`,
`exists_align_six_config`, `halign8`), the selection splits on `s := ∑_{v∈D}|N v ∩ D| = 2·e(M)`,
which `eM_le_five` bounds by `10` and `eM_even` shows even, so `s ∈ {0, 2, 4, 6, 8, 10}`:

* `two_hub_config_fifteen` (`s ≤ 2`, `e(M) ≤ 1`): the two-hub opposite-twin configuration.
* `exists_align_four_config_fifteen` (`s = 4`, `e(M) = 2`): the three-way dichotomy.
* `exists_align_six_config_fifteen` (`s = 6`, `e(M) = 3`): the three-way dichotomy.
* `halign8_fifteen` (`s ≥ 8`, `e(M) ≥ 4`): the three-way dichotomy.

Each is a documented `sorry`; the precise per-`e(M)` decomposition and the `n = 15`-specific
cardinality deltas (vs `n = 14`) are recorded in the individual docstrings below.
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **Refined handshake for `n = 15`.**  The degree-`3` set `D` and the hub set `Hub = {4 ≤ deg}`
partition `Fin 15`, and the degree-sum identity `∑ deg = 52` with the cross-count
`cross_count` and minimum hub-degree `4` give `6·|D| ≤ 52 + s` where
`s = ∑_{v∈D}|N v ∩ D| = 2·e(M)`.  Hence `e(M) = 3` forces `|D| ≤ 9` (i.e. `6 ≤ |Hub|`). -/
theorem handshake_fifteen (G : SimpleGraph (Fin 15)) (hm : G.edgeFinset.card = 26)
    (h3 : ∀ v : Fin 15, 3 ≤ G.degree v) :
    (Finset.univ.filter (fun w => G.degree w = 3)).card
        + (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card = 15
      ∧ 6 * (Finset.univ.filter (fun w => G.degree w = 3)).card
          ≤ 52 + ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
            (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 15) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 15, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hHubnotD : ∀ x : Fin 15, x ∈ Hub → x ∉ D := by
    intro x hx hxD; have := (hmemHub x).mp hx; have := (hmemD x).mp hxD; omega
  have hDH : ∀ v : Fin 15, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub :=
    Finset.disjoint_left.mpr (fun v hv hv' => hHubnotD v hv' hv)
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard15 : D.card + Hub.card = 15 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  refine ⟨hcard15, ?_⟩
  have hsum : ∑ v : Fin 15, G.degree v = 52 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 52 := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hsplitD : ∀ v ∈ D,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    have hdeg : (G.neighborFinset v).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, (hmemD v).mp hv]
    have hu : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
    have hdj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
      Finset.disjoint_left.mpr (fun a ha hb =>
        (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
    have hc := Finset.card_union_of_disjoint hdj
    rw [hu, hdeg] at hc; omega
  have hAs : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitD, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card := cross_count G D Hub
  have hAle : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Hub, G.degree w := by
    apply Finset.sum_le_sum
    intro w _
    calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree w := G.card_neighborFinset_eq_degree w
  rw [hcross] at hAs
  omega

/-- **Shared degree-`4` hub of two `M`-isolated twins (`n = 15`, `|Hub| ≥ 6`, `|Iso| ≥ 4`).**
Pigeonhole: each `M`-isolated degree-`3` twin meets at least two degree-`4` hubs
(`isolated_twin_two_deg4_hubs`), so the `M`-isolated set carries `≥ 2·|Iso| ≥ 8 > 7 ≥ |Hub₄|`
twin–hub incidences and some degree-`4` hub is adjacent to two distinct twins
(`shared_deg4_hub_from_count_fifteen`).  This is the dominant `TwoTwin` selection step feeding the
dense assembly lemmas. -/
theorem exists_shared_deg4_hub_fifteen (G : SimpleGraph (Fin 15))
    (hm : G.edgeFinset.card = 26) (h3 : ∀ v : Fin 15, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (h2k2 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hHub6 : 6 ≤ (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card)
    (hIso4 : 4 ≤ ((Finset.univ.filter (fun w => G.degree w = 3)).filter
      (fun v => (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card
        = 0)).card) :
    ∃ h t₁ t₂ : Fin 15, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 15, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 15, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Iso : Finset (Fin 15) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  set Hub4 : Finset (Fin 15) := Finset.univ.filter (fun h => G.degree h = 4) with hHub4def
  have hdegD : ∀ v : Fin 15, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hHub4deg : ∀ h ∈ Hub4, G.degree h = 4 := by
    intro h hh; rw [hHub4def, Finset.mem_filter] at hh; exact hh.2
  have hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 15, G.Adj v w → G.degree w ≠ 3) := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨hdegD v hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hHub4le : Hub4.card ≤ 7 := by
    have hsub : Hub4 ⊆ Finset.univ.filter (fun v => 4 ≤ G.degree v) := by
      intro h hh; rw [hHub4def, Finset.mem_filter] at hh
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by omega⟩
    exact le_trans (Finset.card_le_card hsub) (residual_hub_card_le_seven G hm h3).1
  have htwo : ∀ v ∈ Iso, 2 ≤ (G.neighborFinset v ∩ Hub4).card := by
    intro v hv
    obtain ⟨hvdeg, hviso⟩ := hIsoprop v hv
    obtain ⟨h₁, h₂, hne, ha1, ha2, hd1, hd2⟩ :=
      isolated_twin_two_deg4_hubs G hm h3 hHub6 hT hC4 h2k2 v hvdeg hviso
    have hsub : ({h₁, h₂} : Finset (Fin 15)) ⊆ G.neighborFinset v ∩ Hub4 := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha1,
          by rw [hHub4def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hd1⟩⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha2,
          by rw [hHub4def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hd2⟩⟩
    calc 2 = ({h₁, h₂} : Finset (Fin 15)).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
    have hge : 2 * Iso.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
      have := Finset.card_nsmul_le_sum Iso (fun v => (G.neighborFinset v ∩ Hub4).card) 2 htwo
      simpa [smul_eq_mul, mul_comm] using this
    have : 4 ≤ Iso.card := by rw [hIsodef, hDdef] at hIso4 ⊢; exact hIso4
    omega
  exact shared_deg4_hub_from_count_fifteen G Iso Hub4 hIsoprop hHub4deg hcount

/-- **Two-hub opposite-twin selection for `n = 15`, `e(M) ≤ 1` (open: structural selection).**
In the `e(M) ≤ 1` regime (`s ≤ 2`) there is no degree-`3` cherry through two hubs, so the
two-hub opposite-twin cut is always available.  Ported from `two_hub_config_fourteen`; the
`n = 15` deltas are the cardinalities: with `|V| = 15`, `e(G) = 26` the residual splits as
`|Hub| ∈ {6, 7}`, `|Iso| ∈ {6, 7, 8}` (vs `n = 14`'s `|Hub| ∈ {5, 6}`, `|Iso| = 6` at
`e(M) = 1`).  The selection (`each_iso_three_hubs` + a hub-pair double count bounded by `hK23`,
splitting on `|Hub|`) yields two non-adjacent degree-`4` hubs each keeping `≥ 2` private isolated
twins; the larger `|Iso|` only adds slack.
DECOMPOSITION: port `two_hub_config_fourteen` (TwinCert14TwoHub.lean:443) and its selection
helpers `each_iso_three_hubs`, `residual_hub_card_le_seven`, `two_isolated_twins`; replace the
`|Hub| ∈ {5,6}` split with `|Hub| ∈ {6,7}`. -/
theorem two_hub_config_fifteen (G : SimpleGraph (Fin 15))
    (hm : G.edgeFinset.card = 26) (h3 : ∀ v : Fin 15, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (_hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 15, ({a, b, c, d, e} : Finset (Fin 15)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 15, G.degree t = 3 ∧ ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3)
    (hle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 2) :
    TwoHubConfig G := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 15) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 15, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hHubnotD : ∀ x : Fin 15, x ∈ Hub → x ∉ D := by
    intro x hx hxD; have := (hmemHub x).mp hx; have := (hmemD x).mp hxD; omega
  set Iso : Finset (Fin 15) := D.filter (fun x => (G.neighborFinset x ∩ D).card = 0) with hIsodef
  have hIsomem : ∀ x : Fin 15, x ∈ Iso ↔ x ∈ D ∧ (G.neighborFinset x ∩ D).card = 0 := by
    intro x; rw [hIsodef, Finset.mem_filter]
  have hisoD : ∀ x : Fin 15, x ∈ Iso → x ∈ D := fun x hx => ((hIsomem x).mp hx).1
  have hisoNoD : ∀ x y : Fin 15, x ∈ Iso → y ∈ D → ¬G.Adj x y := by
    intro x y hx hy hadj
    obtain ⟨_, hx0⟩ := (hIsomem x).mp hx
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hx0
    exact hx0 y (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hadj, hy⟩)
  -- **Good-`K_{2,3}` share bound.**  A non-adjacent pair of degree-`≤ 4` vertices shares at most
  -- two `M`-isolated twins (three would form a good `K_{2,3}` of degree-sum `≤ 17 ≤ 18`).
  have hshareLem : ∀ h₁ h₂ : Fin 15, G.degree h₁ ≤ 4 → G.degree h₂ ≤ 4 →
      h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2 := by
    intro h₁ h₂ hd1 hd2 hne hnadj
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcon
    have hmem : ∀ x : Fin 15, x ∈ G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso →
        G.Adj h₁ x ∧ G.Adj h₂ x ∧ x ∈ Iso := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hx
      exact ⟨hx.1.1, hx.1.2, hx.2⟩
    obtain ⟨ha1, ha2, haIso⟩ := hmem a ha
    obtain ⟨hb1, hb2, hbIso⟩ := hmem b hb
    obtain ⟨hc1, hc2, hcIso⟩ := hmem c hc
    have haD := hisoD a haIso
    have hbD := hisoD b hbIso
    have hcD := hisoD c hcIso
    have hnab : ¬G.Adj a b := hisoNoD a b haIso hbD
    have hnac : ¬G.Adj a c := hisoNoD a c haIso hcD
    have hnbc : ¬G.Adj b c := hisoNoD b c hbIso hcD
    have h1a : h₁ ≠ a := G.ne_of_adj ha1
    have h1b : h₁ ≠ b := G.ne_of_adj hb1
    have h1c : h₁ ≠ c := G.ne_of_adj hc1
    have h2a : h₂ ≠ a := G.ne_of_adj ha2
    have h2b : h₂ ≠ b := G.ne_of_adj hb2
    have h2c : h₂ ≠ c := G.ne_of_adj hc2
    refine hK23 ⟨h₁, h₂, a, b, c,
      card_five_fifteen h₁ h₂ a b c hne h1a h1b h1c h2a h2b h2c hab hac hbc,
      ha1, hb1, hc1, ha2, hb2, hc2, hnadj, hnab, hnac, hnbc, ?_⟩
    have hda3 : G.degree a = 3 := (hmemD a).mp haD
    have hdb3 : G.degree b = 3 := (hmemD b).mp hbD
    have hdc3 : G.degree c = 3 := (hmemD c).mp hcD
    omega
  -- **Handshake forced split** (`|D| ∈ {8, 9}`): `|D| = 8 ⇒ |Hub| = 7`, all hubs degree `4`;
  -- `|D| = 9 ⇒ |Hub| = 6`.
  have hsum : ∑ v : Fin 15, G.degree v = 52 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hDH : ∀ v : Fin 15, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub :=
    Finset.disjoint_left.mpr (fun v hv hv' => hHubnotD v hv' hv)
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard15 : D.card + Hub.card = 15 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 52 := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hsplitD : ∀ v ∈ D,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    have hdeg : (G.neighborFinset v).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, (hmemD v).mp hv]
    have hu : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
    have hdj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
      Finset.disjoint_left.mpr (fun a ha hb =>
        (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
    have hc := Finset.card_union_of_disjoint hdj
    rw [hu, hdeg] at hc; omega
  have hsplitHub : ∀ w ∈ Hub,
      (G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Hub).card = G.degree w := by
    intro w hw
    have hdeg : (G.neighborFinset w).card = G.degree w := G.card_neighborFinset_eq_degree w
    have hu : (G.neighborFinset w ∩ D) ∪ (G.neighborFinset w ∩ Hub) = G.neighborFinset w := by
      rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
    have hdj : Disjoint (G.neighborFinset w ∩ D) (G.neighborFinset w ∩ Hub) :=
      Finset.disjoint_left.mpr (fun a ha hb =>
        (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
    have hc := Finset.card_union_of_disjoint hdj
    rw [hu, hdeg] at hc; omega
  have hSsumD : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitD, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hSsumHub : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card
      + ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = ∑ w ∈ Hub, G.degree w := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitHub]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card := cross_count G D Hub
  have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
    have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
    have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul, mul_comm] using h
  have hsD : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2 := by rw [hDdef]; exact hle
  have hforced : (D.card = 8 ∧ Hub.card = 7 ∧ ∀ h ∈ Hub, G.degree h = 4) ∨
      (D.card = 9 ∧ Hub.card = 6) := by
    have hD89 : D.card = 8 ∨ D.card = 9 := by
      have hge : 8 ≤ D.card := by omega
      have hle9 : D.card ≤ 9 := by omega
      omega
    rcases hD89 with h8 | h9
    · refine Or.inl ⟨h8, by omega, ?_⟩
      have hHub7 : Hub.card = 7 := by omega
      have hsumHubdeg : ∑ w ∈ Hub, G.degree w = 28 := by omega
      intro w hw
      have hge := (hmemHub w).mp hw
      have hiso := Finset.add_sum_erase Hub (fun v => G.degree v) hw
      have herase : 4 * (Hub.erase w).card ≤ ∑ v ∈ Hub.erase w, G.degree v := by
        have hb : ∀ x ∈ Hub.erase w, 4 ≤ G.degree x := fun i hi =>
          (hmemHub i).mp (Finset.mem_of_mem_erase hi)
        have h := Finset.card_nsmul_le_sum (Hub.erase w) (fun v => G.degree v) 4 hb
        simpa [smul_eq_mul, mul_comm] using h
      have hec : (Hub.erase w).card = Hub.card - 1 := Finset.card_erase_of_mem hw
      omega
    · exact Or.inr ⟨h9, by omega⟩
  -- **Hub-pair selection.**  Two non-adjacent degree-`4` hubs each keeping `≥ 2` private isolated
  -- twins.
  have hpair : ∃ h₁ h₂ : Fin 15, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
    by_cases hs0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0
    · -- **`e(M) = 0`: `M` edgeless, every twin isolated.**
      have hzero : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 :=
        (Finset.sum_eq_zero_iff).mp hs0
      have hDiso : ∀ v : Fin 15, v ∈ D → v ∈ Iso := fun v hv =>
        (hIsomem v).mpr ⟨hv, hzero v hv⟩
      -- With `s = 0`, the cross sum equals `3|D|`, ruling out `|D| = 9`.
      have hsplitD0 : ∀ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 := by
        intro v hv; have := hsplitD v hv; have := hzero v hv; omega
      have hcrossD : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
        rw [Finset.sum_congr rfl hsplitD0, Finset.sum_const, smul_eq_mul, mul_comm]
      have hcrossND : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card = 3 * D.card := by
        rw [← hcross]; exact hcrossD
      have heq : 6 * D.card + (∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card) = 52 := by
        have h1 := hsumpart
        rw [hsumD, ← hSsumHub, hcrossND] at h1; omega
      obtain ⟨hD8, hHub7, hdeg4⟩ : D.card = 8 ∧ Hub.card = 7 ∧ ∀ h ∈ Hub, G.degree h = 4 := by
        rcases hforced with h | ⟨h9, _⟩
        · exact h
        · exfalso; rw [h9] at heq; omega
      -- Hub-internal incidences sum to `4`, so at least three hubs have hub-degree `0`.
      have hHubInt : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 4 := by
        rw [hD8] at heq; omega
      set Z : Finset (Fin 15) := Hub.filter (fun h => (G.neighborFinset h ∩ Hub).card = 0)
        with hZdef
      have hZcard : 2 < Z.card := by
        set NZ : Finset (Fin 15) := Hub.filter (fun h => ¬ (G.neighborFinset h ∩ Hub).card = 0)
          with hNZdef
        have hpart : Z.card + NZ.card = Hub.card :=
          Finset.card_filter_add_card_filter_not (s := Hub)
            (p := fun h => (G.neighborFinset h ∩ Hub).card = 0)
        have hNZge : NZ.card ≤ ∑ w ∈ NZ, (G.neighborFinset w ∩ Hub).card := by
          have h := Finset.card_nsmul_le_sum NZ
            (fun w => (G.neighborFinset w ∩ Hub).card) 1
            (fun w hw => by
              have := (Finset.mem_filter.mp hw).2; omega)
          simpa using h
        have hZsum0 : ∑ w ∈ Z, (G.neighborFinset w ∩ Hub).card = 0 :=
          Finset.sum_eq_zero (fun w hw => (Finset.mem_filter.mp hw).2)
        have hsplit : ∑ w ∈ Z, (G.neighborFinset w ∩ Hub).card
            + ∑ w ∈ NZ, (G.neighborFinset w ∩ Hub).card
            = ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card := by
          rw [hZdef, hNZdef, Finset.sum_filter_add_sum_filter_not]
        rw [hZsum0, hHubInt] at hsplit
        omega
      obtain ⟨h₁, hh1Z, h₂, hh2Z, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < Z.card)
      have hh1 : h₁ ∈ Hub := (Finset.mem_filter.mp hh1Z).1
      have hh2 : h₂ ∈ Hub := (Finset.mem_filter.mp hh2Z).1
      have hh1z : (G.neighborFinset h₁ ∩ Hub).card = 0 := (Finset.mem_filter.mp hh1Z).2
      have hh2z : (G.neighborFinset h₂ ∩ Hub).card = 0 := (Finset.mem_filter.mp hh2Z).2
      -- A hub of hub-degree `0` has all neighbours in `Iso` (degree `4`).
      have hNiso : ∀ w : Fin 15, w ∈ Hub → (G.neighborFinset w ∩ Hub).card = 0 →
          (G.neighborFinset w ∩ Iso).card = 4 := by
        intro w hw hwz
        have hsubD : G.neighborFinset w ⊆ D := by
          intro x hx
          rcases hDH x with hxD | hxH
          · exact hxD
          · exfalso
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hwz
            exact hwz x (Finset.mem_inter.mpr ⟨hx, hxH⟩)
        have hsubIso : G.neighborFinset w ⊆ Iso := fun x hx => hDiso x (hsubD hx)
        rw [Finset.inter_eq_left.mpr hsubIso, G.card_neighborFinset_eq_degree, hdeg4 w hw]
      have hI1 := hNiso h₁ hh1 hh1z
      have hI2 := hNiso h₂ hh2 hh2z
      have hd1 : G.degree h₁ ≤ 4 := by rw [hdeg4 h₁ hh1]
      have hd2 : G.degree h₂ ≤ 4 := by rw [hdeg4 h₂ hh2]
      have hnadj12 : ¬G.Adj h₁ h₂ := by
        intro hadj
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hh1z
        exact hh1z h₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr hadj, hh2⟩)
      refine ⟨h₁, h₂, hh1, hh2, hdeg4 h₁ hh1, hdeg4 h₂ hh2, hne12, hnadj12, ?_, ?_⟩
      · have hshare := hshareLem h₁ h₂ hd1 hd2 hne12 hnadj12
        have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
          (G.neighborFinset h₂)
        have hreord : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
            = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := Finset.inter_right_comm _ _ _
        rw [hreord] at hkey; omega
      · have hshare := hshareLem h₂ h₁ hd2 hd1 (Ne.symm hne12) (fun h => hnadj12 h.symm)
        have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso)
          (G.neighborFinset h₁)
        have hreord : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset h₁
            = G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso := Finset.inter_right_comm _ _ _
        rw [hreord] at hkey; omega
    · -- **`e(M) = 1` (`s = 2`): the two-hub selection corner.**  Here `s = 2` (even, `≤ 2`, `≠ 0`),
      -- so `M` is a single edge and `|Iso| ≥ 6`.  The residual is `|Hub| = 7, |Iso| = 6` (all hubs
      -- degree `4`, `e(Hub) = 3`) OR `|Hub| = 6, |Iso| = 7` (one degree-`5` hub, `e(Hub) = 0`).  The
      -- selection of two NON-ADJACENT degree-`4` hubs each retaining `≥ 2` private isolated twins is
      -- the genuine pigeonhole corner: it needs the strong/weak iso-degree split and the
      -- adjacency-bounded low-share pair-count of the `n = 14` `two_hub_corner_select` chain,
      -- generalized to `|Hub| ∈ {6, 7}`, `|Iso| ∈ {6, 7}` and the degree-`5` hub.  Wired to the
      -- fully-proved `two_hub_corner_select_fifteen` selection lemma.
      have hD8ge : 8 ≤ D.card := by rcases hforced with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      have hD9le : D.card ≤ 9 := by rcases hforced with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      -- **`s = 2` exactly.**  The non-isolated set `S` of `M = G[D]` has `|S| = 2`.
      set S : Finset (Fin 15) := D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) with hSdef
      have hScompl : Iso.card + S.card = D.card := by
        rw [hIsodef, hSdef]
        exact Finset.card_filter_add_card_filter_not (s := D)
          (p := fun v => (G.neighborFinset v ∩ D).card = 0)
      have hSle : 2 * S.card ≤ (∑ v ∈ D, (G.neighborFinset v ∩ D).card) + 2 := by
        rw [hSdef]; exact nonisolated_component_bound G D hmemD h2k2
      have hexists : ∃ v ∈ D, (G.neighborFinset v ∩ D).card ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hs0 (Finset.sum_eq_zero hcon)
      obtain ⟨v0, hv0D, hv0ne⟩ := hexists
      have hv0S : v0 ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hv0D, hv0ne⟩
      obtain ⟨w0, hw0mem⟩ := Finset.card_ne_zero.mp hv0ne
      have hw0D : w0 ∈ D := (Finset.mem_inter.mp hw0mem).2
      have hadj0 : G.Adj v0 w0 := (G.mem_neighborFinset v0 w0).mp (Finset.mem_inter.mp hw0mem).1
      have hw0S : w0 ∈ S := by
        rw [hSdef, Finset.mem_filter]
        refine ⟨hw0D, ?_⟩
        exact Finset.card_ne_zero.mpr
          ⟨v0, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w0 v0).mpr hadj0.symm, hv0D⟩⟩
      have hvw0ne : v0 ≠ w0 := G.ne_of_adj hadj0
      have hSge : 2 ≤ S.card := by
        have hsub : ({v0, w0} : Finset (Fin 15)) ⊆ S := by
          intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h
          · rw [h]; exact hv0S
          · rw [h]; exact hw0S
        calc 2 = ({v0, w0} : Finset (Fin 15)).card := by rw [Finset.card_pair hvw0ne]
          _ ≤ S.card := Finset.card_le_card hsub
      have hScard : S.card = 2 := by omega
      have hs2 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 2 := by omega
      -- **Hub-internal incidence identity** `∑_{w∈Hub}|N w ∩ Hub| + 6·|D| = 54`.
      have hHubInt : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card + 6 * D.card = 54 := by omega
      -- **Hypotheses of `two_hub_corner_select_fifteen`.**
      have hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h := fun h hh => (hmemHub h).mp hh
      have hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5 := by
        intro h hh
        have e1 := Finset.add_sum_erase Hub (fun v => G.degree v) hh
        have hge : 4 * (Hub.erase h).card ≤ ∑ v ∈ Hub.erase h, G.degree v := by
          have hb : ∀ x ∈ Hub.erase h, 4 ≤ G.degree x := fun i hi =>
            (hmemHub i).mp (Finset.mem_of_mem_erase hi)
          have h2 := Finset.card_nsmul_le_sum (Hub.erase h) (fun v => G.degree v) 4 hb
          simpa [smul_eq_mul, mul_comm] using h2
        have hc : (Hub.erase h).card = Hub.card - 1 := Finset.card_erase_of_mem hh
        omega
      have hpairdeg : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ →
          G.degree h₁ + G.degree h₂ ≤ 9 := by
        intro h₁ hh1 h₂ hh2 hne
        have hh2e : h₂ ∈ Hub.erase h₁ := Finset.mem_erase.mpr ⟨Ne.symm hne, hh2⟩
        have e1 := Finset.add_sum_erase Hub (fun v => G.degree v) hh1
        have e2 := Finset.add_sum_erase (Hub.erase h₁) (fun v => G.degree v) hh2e
        have hge : 4 * ((Hub.erase h₁).erase h₂).card
            ≤ ∑ v ∈ (Hub.erase h₁).erase h₂, G.degree v := by
          have hb : ∀ x ∈ (Hub.erase h₁).erase h₂, 4 ≤ G.degree x := fun i hi =>
            (hmemHub i).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
          have h := Finset.card_nsmul_le_sum ((Hub.erase h₁).erase h₂)
            (fun v => G.degree v) 4 hb
          simpa [smul_eq_mul, mul_comm] using h
        have hc1 : (Hub.erase h₁).card = Hub.card - 1 := Finset.card_erase_of_mem hh1
        have hc2 : ((Hub.erase h₁).erase h₂).card = (Hub.erase h₁).card - 1 :=
          Finset.card_erase_of_mem hh2e
        omega
      have hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3 := fun t ht =>
        each_iso_three_hubs G D Hub hmemD hmemHub h3 t (hisoD t ht) ((hIsomem t).mp ht).2
      have hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b := fun a ha b hb =>
        hisoNoD a b ha (hisoD b hb)
      have hdisjHI : Disjoint Hub Iso := by
        rw [Finset.disjoint_left]
        intro x hxH hxI
        exact (Finset.disjoint_left.mp hdisj) (hisoD x hxI) hxH
      have hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
          (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2 := by
        intro h₁ hh1 h₂ hh2 hne hnadj
        by_contra hcon
        rw [not_le] at hcon
        obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcon
        have hmem : ∀ x : Fin 15, x ∈ G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso →
            G.Adj h₁ x ∧ G.Adj h₂ x ∧ x ∈ Iso := by
          intro x hx
          rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hx
          exact ⟨hx.1.1, hx.1.2, hx.2⟩
        obtain ⟨ha1, ha2, haIso⟩ := hmem a ha
        obtain ⟨hb1, hb2, hbIso⟩ := hmem b hb
        obtain ⟨hc1, hc2, hcIso⟩ := hmem c hc
        have haD := hisoD a haIso
        have hbD := hisoD b hbIso
        have hcD := hisoD c hcIso
        have hnab : ¬G.Adj a b := hisoNoD a b haIso hbD
        have hnac : ¬G.Adj a c := hisoNoD a c haIso hcD
        have hnbc : ¬G.Adj b c := hisoNoD b c hbIso hcD
        have h1a : h₁ ≠ a := G.ne_of_adj ha1
        have h1b : h₁ ≠ b := G.ne_of_adj hb1
        have h1c : h₁ ≠ c := G.ne_of_adj hc1
        have h2a : h₂ ≠ a := G.ne_of_adj ha2
        have h2b : h₂ ≠ b := G.ne_of_adj hb2
        have h2c : h₂ ≠ c := G.ne_of_adj hc2
        refine hK23 ⟨h₁, h₂, a, b, c,
          card_five_fifteen h₁ h₂ a b c hne h1a h1b h1c h2a h2b h2c hab hac hbc,
          ha1, hb1, hc1, ha2, hb2, hc2, hnadj, hnab, hnac, hnbc, ?_⟩
        have hda3 : G.degree a = 3 := (hmemD a).mp haD
        have hdb3 : G.degree b = 3 := (hmemD b).mp hbD
        have hdc3 : G.degree c = 3 := (hmemD c).mp hcD
        have hpd := hpairdeg h₁ hh1 h₂ hh2 hne
        omega
      -- **Regime split** and call.
      rcases hforced with ⟨hD8, hHub7, hdeg4all⟩ | ⟨hD9, hHub6⟩
      · have hIso6 : Iso.card = 6 := by omega
        exact two_hub_corner_select_fifteen G Hub Iso hdeg hdeg5 (by omega) hiso3 hisoIndep
          hshare hdisjHI (Or.inl ⟨hHub7, hIso6, hdeg4all⟩)
      · have hIso7 : Iso.card = 7 := by omega
        have hHub0 : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 0 := by omega
        have hdsum : ∑ w ∈ Hub, G.degree w = 25 := by omega
        exact two_hub_corner_select_fifteen G Hub Iso hdeg hdeg5 (by omega) hiso3 hisoIndep
          hshare hdisjHI (Or.inr ⟨hHub6, hIso7, hHub0, hdsum⟩)
  obtain ⟨h₁, h₂, hh1, hh2, hdeg1, hdeg2, hne12, hnadj12, hAcard, hBcard⟩ := hpair
  set A : Finset (Fin 15) := (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ with hAdef
  set B : Finset (Fin 15) := (G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁ with hBdef
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hAcard
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hBcard
  have hAprop : ∀ x : Fin 15, x ∈ A → G.Adj x h₁ ∧ x ∈ Iso ∧ ¬G.Adj x h₂ := by
    intro x hx
    rw [hAdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
    refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
    intro hadj; exact hx.2 ((G.mem_neighborFinset h₂ x).mpr hadj.symm)
  have hBprop : ∀ x : Fin 15, x ∈ B → G.Adj x h₂ ∧ x ∈ Iso ∧ ¬G.Adj x h₁ := by
    intro x hx
    rw [hBdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
    refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
    intro hadj; exact hx.2 ((G.mem_neighborFinset h₁ x).mpr hadj.symm)
  obtain ⟨ha_h₁, ha_iso, ha_nh₂⟩ := hAprop a ha
  obtain ⟨hb_h₁, hb_iso, hb_nh₂⟩ := hAprop b hb
  obtain ⟨hc_h₂, hc_iso, hc_nh₁⟩ := hBprop c hc
  obtain ⟨hd_h₂, hd_iso, hd_nh₁⟩ := hBprop d hd
  have haD := hisoD a ha_iso
  have hbD := hisoD b hb_iso
  have hcD := hisoD c hc_iso
  have hdD := hisoD d hd_iso
  exact ⟨h₁, h₂, a, b, c, d, hdeg1, hdeg2,
    (hmemD a).mp haD, (hmemD b).mp hbD, (hmemD c).mp hcD, (hmemD d).mp hdD,
    ha_h₁, hb_h₁, hc_h₂, hd_h₂,
    hnadj12,
    (fun h => hc_nh₁ h.symm), (fun h => hd_nh₁ h.symm),
    ha_nh₂, hisoNoD a c ha_iso hcD, hisoNoD a d ha_iso hdD,
    hb_nh₂, hisoNoD b c hb_iso hcD, hisoNoD b d hb_iso hdD,
    hne12,
    (fun e => hHubnotD h₁ hh1 (by rw [e]; exact haD)),
    (fun e => hHubnotD h₁ hh1 (by rw [e]; exact hbD)),
    (fun e => hHubnotD h₁ hh1 (by rw [e]; exact hcD)),
    (fun e => hHubnotD h₁ hh1 (by rw [e]; exact hdD)),
    (fun e => hHubnotD h₂ hh2 (by rw [e]; exact haD)),
    (fun e => hHubnotD h₂ hh2 (by rw [e]; exact hbD)),
    (fun e => hHubnotD h₂ hh2 (by rw [e]; exact hcD)),
    (fun e => hHubnotD h₂ hh2 (by rw [e]; exact hdD)),
    hab,
    (fun e => hc_nh₁ (e ▸ ha_h₁)), (fun e => hd_nh₁ (e ▸ ha_h₁)),
    (fun e => hc_nh₁ (e ▸ hb_h₁)), (fun e => hd_nh₁ (e ▸ hb_h₁)),
    hcd⟩

/-- **Three-way alignment dichotomy for `n = 15`, `e(M) = 2` (open: structural selection).**
At `s = 4` the matching `M` is a single `P₃` cherry; the verified covering combination over the
residual graphs is `SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig`.  Ported from
`exists_align_four_config` (TwinCert14Align4.lean:41).  For `n = 15` the dichotomy is essentially
`TwoTwin`-only: a degree-`4` hub with `≥ 2` `M`-isolated twins plus a cherry it avoids, assembled
by `dense_two_twin_assemble`, with `isolated_twin_two_deg4_hubs` (needs `|Hub| ≥ 6`) supplying the
hub.  EXCEPTION: `|Hub| = 5` (`|D| = 10`, forces `e(M) ≥ 4`, so not reached at `e(M) = 2`).
DECOMPOSITION: port `exists_align_four_config` together with the dense-twin helpers
`config_from_fat_dom` (claw) and `thin_eM_formula` (P₄) it invokes. -/
theorem exists_align_four_config_fifteen (G : SimpleGraph (Fin 15))
    (hm : G.edgeFinset.card = 26) (h3 : ∀ v : Fin 15, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 15, ({a, b, c, d, e} : Finset (Fin 15)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 15, G.degree t = 3 ∧ ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3)
    (hs4 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 4) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hdegD : ∀ v : Fin 15, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  -- **Cardinalities.**  `|D| ∈ {8, 9}`, `|Hub| ∈ {6, 7}`, `|Iso| ≥ 5`.
  obtain ⟨hHub7, hD8⟩ := residual_hub_card_le_seven G hm h3
  obtain ⟨hpart, hhand⟩ := handshake_fifteen G hm h3
  rw [← hDdef] at hD8 hpart hhand
  rw [hs4] at hhand
  have hHub6 : 6 ≤ (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card := by omega
  have hIso4 : 4 ≤ (D.filter
      (fun v => (G.neighborFinset v ∩ D).card = 0)).card := by
    have hnb := nonisolated_component_bound G D hmemD h2k2
    rw [hs4] at hnb
    have hpartIso := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    omega
  obtain ⟨k, t₁, t₂, hkdeg4, ht12, ht1deg, ht2deg, hAt1k, hAt2k, ht1iso, ht2iso⟩ :=
    exists_shared_deg4_hub_fifteen G hm h3 hT hC4 h2k2 hHub6 (by rw [hDdef] at hIso4; exact hIso4)
  -- An `M`-edge exists, since `s = 4 > 0`.
  have hne : ∃ a b : Fin 15, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
  · -- **Dominating-edge branch.**  `M` is a single `P₃` cherry; build it from the centre and feed
    -- the shared hub to `dense_two_twin_assemble` when the hub avoids the cherry.  The "hub meets
    -- cherry" sub-case (a re-selected cherry-avoiding hub, the `n = 14` `|D| ∈ {8,9}` rigid count)
    -- is the single documented `sorry`.
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hdomprop⟩ := hdom
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
        have hsubset : D.filter (fun v => v = c₁ ∨ v = c₂) ⊆ ({c₁, c₂} : Finset (Fin 15)) := by
          intro v hv
          rw [Finset.mem_filter] at hv
          rcases hv.2 with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        calc (D.filter (fun v => v = c₁ ∨ v = c₂)).card
            ≤ ({c₁, c₂} : Finset (Fin 15)).card := Finset.card_le_card hsubset
          _ ≤ 2 := by
              have := Finset.card_insert_le c₁ ({c₂} : Finset (Fin 15))
              simp only [Finset.card_singleton] at this
              omega
      omega
    have mkcherry : ∀ c : Fin 15, c ∈ D → 2 ≤ (G.neighborFinset c ∩ D).card →
        ∃ x y z : Fin 15, x ∈ D ∧ y ∈ D ∧ z ∈ D ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
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
    by_cases havoid : ¬G.Adj k x ∧ ¬G.Adj k y ∧ ¬G.Adj k z
    · obtain ⟨hkx, hky, hkz⟩ := havoid
      exact Or.inr (Or.inl (dense_two_twin_assemble G t₁ t₂ k x y z ht1deg ht2deg hkdeg4
        hdegx hdegy hdegz hAt1k hAt2k hxyA hyzA ht1iso ht2iso hkx hky hkz ht12
        hxy_ne hyz_ne hxz_ne))
    · -- **Shared hub meets the cherry.**  Rigid residual: `|D| ∈ {8, 9}`, the cherry `{x, y, z}` is
      -- the full `M`-non-isolated set, and a cherry-avoiding hub `h₆` with `≥ 2` `D`-neighbours
      -- yields a `TwoTwinConfig` directly.  The `n = 14` symmetry bound is too weak at `|D| = 8`
      -- (hub-internal sum `8`), so the cherry-avoiding hub is selected by a refined internal-edge
      -- count: assuming every cherry-avoiding hub has `≤ 1` `D`-neighbour forces
      -- `|A|·(7 - |A|) ≤ ∑_{Dᶜ}|N ∩ Dᶜ|`, contradicting `2 ≤ |A| ≤ 5` (`|D| = 8`) / `1 ≤ |A| ≤ 4`
      -- (`|D| = 9`).
      have hsum52 : ∑ v : Fin 15, G.degree v = 52 := by
        rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
      have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
        rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
      have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 52 := by
        rw [Finset.sum_add_sum_compl]; exact hsum52
      have hpartw : ∀ w : Fin 15,
          (G.neighborFinset w ∩ Dᶜ).card + (G.neighborFinset w ∩ D).card = G.degree w := by
        intro w
        have heq : G.neighborFinset w ∩ Dᶜ = G.neighborFinset w \ D := by
          ext a; simp [Finset.mem_sdiff, Finset.mem_compl]
        rw [heq]
        have := Finset.card_sdiff_add_card_inter (G.neighborFinset w) D
        rw [G.card_neighborFinset_eq_degree] at this
        exact this
      have hAsdc : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
          + ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 3 * D.card := by
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun v _ => hpartw v), hsumDdeg]
      have hcross := cross_count G D Dᶜ
      have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
        intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
      have hcc : D.card + Dᶜ.card = 15 := by
        have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
      have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 52 - 3 * D.card := by
        rw [hsumDdeg] at hsumsplit; omega
      have hDcD : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card = 3 * D.card - 4 := by
        rw [← hcross]; rw [hs4] at hAsdc; omega
      have hDcDc : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 56 - 6 * D.card := by
        have hsumeq : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ Dᶜ).card + (G.neighborFinset w ∩ D).card)
            = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hpartw w)
        rw [Finset.sum_add_distrib] at hsumeq
        omega
      have hD89 : D.card = 8 ∨ D.card = 9 := by omega
      have hdeg5all : ∀ w ∈ Dᶜ, G.degree w ≤ 5 := by
        intro w hw
        have hsplit := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
        have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
          have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
            fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
          have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
          simpa [smul_eq_mul, mul_comm] using this
        have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
        omega
      -- The `M`-non-isolated vertices are exactly the cherry `{x, y, z}`.
      have hxyzcard : ({x, y, z} : Finset (Fin 15)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
          Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hsubNI : ({x, y, z} : Finset (Fin 15))
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
      have hNIeq : ({x, y, z} : Finset (Fin 15))
          = D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
        Finset.eq_of_subset_of_card_le hsubNI (by rw [hxyzcard]; exact hNIcard3)
      have hDsplit : ∀ w : Fin 15, w ∈ D → w ∉ ({x, y, z} : Finset (Fin 15)) →
          (G.neighborFinset w ∩ D).card = 0 := by
        intro w hwD hwxyz
        by_contra hc
        have hmem : w ∈ D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
          Finset.mem_filter.mpr ⟨hwD, hc⟩
        rw [← hNIeq] at hmem
        exact hwxyz hmem
      -- `|N x ∩ D| = 1` (only `y`), so `x` meets exactly two hubs.
      have hNxD1 : 1 ≤ (G.neighborFinset x ∩ D).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hxyA, hyD⟩⟩
      have hNxDle : (G.neighborFinset x ∩ D).card ≤ 1 := by
        have hsub : G.neighborFinset x ∩ D ⊆ ({y} : Finset (Fin 15)) := by
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          obtain ⟨hxw, hwD⟩ := hw
          have hwNI : w ∈ ({x, y, z} : Finset (Fin 15)) := by
            rw [hNIeq, Finset.mem_filter]
            exact ⟨hwD, Finset.card_ne_zero.mpr ⟨x, Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxD⟩⟩⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwNI
          rcases hwNI with rfl | rfl | rfl
          · exact (G.irrefl hxw).elim
          · exact Finset.mem_singleton_self _
          · exact absurd hxw hxzN
        calc (G.neighborFinset x ∩ D).card ≤ ({y} : Finset (Fin 15)).card :=
              Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton _
      have hNxDcexact : (G.neighborFinset x ∩ Dᶜ).card = 2 := by
        have := hpartw x; rw [hdegx] at this; omega
      -- Bad := hubs meeting the cherry; `2 ≤ |Bad| ≤ 5`.
      set Bad : Finset (Fin 15) :=
        Dᶜ.filter (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z) with hBaddef
      set A : Finset (Fin 15) :=
        Dᶜ.filter (fun w => ¬(G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)) with hAdef
      have hAsubDc : A ⊆ Dᶜ := by rw [hAdef]; exact Finset.filter_subset _ _
      have hNyD2 : 2 ≤ (G.neighborFinset y ∩ D).card := by
        have hsub : ({x, z} : Finset (Fin 15)) ⊆ G.neighborFinset y ∩ D := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hxyA.symm, hxD⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hyzA, hzD⟩
        calc 2 = ({x, z} : Finset (Fin 15)).card := (Finset.card_pair hxz_ne).symm
          _ ≤ _ := Finset.card_le_card hsub
      have hNxDc : (G.neighborFinset x ∩ Dᶜ).card ≤ 2 := by omega
      have hNyDc : (G.neighborFinset y ∩ Dᶜ).card ≤ 1 := by
        have := hpartw y; rw [hdegy] at this; omega
      have hNzD1 : 1 ≤ (G.neighborFinset z ∩ D).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z y).mpr hyzA.symm, hyD⟩⟩
      have hNzDc : (G.neighborFinset z ∩ Dᶜ).card ≤ 2 := by
        have := hpartw z; rw [hdegz] at this; omega
      have hBad : Bad.card ≤ 5 := by
        have hsub : Bad ⊆ (G.neighborFinset x ∩ Dᶜ) ∪ (G.neighborFinset y ∩ Dᶜ)
            ∪ (G.neighborFinset z ∩ Dᶜ) := by
          intro w hw; rw [hBaddef, Finset.mem_filter] at hw
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
      have hBad2 : 2 ≤ Bad.card := by
        have hsub : G.neighborFinset x ∩ Dᶜ ⊆ Bad := by
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          rw [hBaddef, Finset.mem_filter]
          exact ⟨hw.2, Or.inl hw.1.symm⟩
        calc 2 = (G.neighborFinset x ∩ Dᶜ).card := hNxDcexact.symm
          _ ≤ _ := Finset.card_le_card hsub
      have hArel : A.card + Bad.card = Dᶜ.card := by
        rw [hAdef, hBaddef]
        rw [add_comm]
        exact Finset.card_filter_add_card_filter_not (s := Dᶜ)
          (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)
      -- Cherry-avoiding hub with `≥ 2` `D`-neighbours.
      have hexists : ∃ h6 ∈ Dᶜ, ¬(G.Adj h6 x ∨ G.Adj h6 y ∨ G.Adj h6 z) ∧
          2 ≤ (G.neighborFinset h6 ∩ D).card := by
        by_contra hcon
        push Not at hcon
        have hAge3 : ∀ h ∈ A, 3 ≤ (G.neighborFinset h ∩ Dᶜ).card := by
          intro h hh
          have hhmem := hh
          rw [hAdef, Finset.mem_filter] at hhmem
          obtain ⟨hhDc, hhavoid⟩ := hhmem
          rw [not_or, not_or] at hhavoid
          have hcnt := hcon h hhDc hhavoid
          have hdg := hDcdeg h hhDc
          have := hpartw h
          omega
        have hsumAge : 3 * A.card ≤ ∑ h ∈ A, (G.neighborFinset h ∩ Dᶜ).card := by
          have := Finset.card_nsmul_le_sum A (fun h => (G.neighborFinset h ∩ Dᶜ).card) 3 hAge3
          simpa [smul_eq_mul, mul_comm] using this
        have hAunionBad : A ∪ Bad = Dᶜ := by
          rw [hAdef, hBaddef, Finset.union_comm]
          exact Finset.filter_union_filter_not_eq _ Dᶜ
        have hAdisjBad : Disjoint A Bad := by
          rw [hAdef, hBaddef]
          exact (Finset.disjoint_filter_filter_not Dᶜ Dᶜ
            (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)).symm
        have hperh : ∀ h : Fin 15, (G.neighborFinset h ∩ Dᶜ).card
            = (G.neighborFinset h ∩ A).card + (G.neighborFinset h ∩ Bad).card := by
          intro h
          rw [← hAunionBad, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
            (hAdisjBad.mono Finset.inter_subset_right Finset.inter_subset_right)]
        have hSAsplit : ∑ h ∈ A, (G.neighborFinset h ∩ Dᶜ).card
            = ∑ h ∈ A, (G.neighborFinset h ∩ A).card
              + ∑ h ∈ A, (G.neighborFinset h ∩ Bad).card := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun h _ => hperh h)
        have hAAle : ∀ h ∈ A, (G.neighborFinset h ∩ A).card ≤ A.card - 1 := by
          intro h hh
          have hsub : G.neighborFinset h ∩ A ⊆ A.erase h := by
            intro w hw; rw [Finset.mem_inter, G.mem_neighborFinset] at hw
            exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hw.1).symm, hw.2⟩
          calc (G.neighborFinset h ∩ A).card ≤ (A.erase h).card := Finset.card_le_card hsub
            _ = A.card - 1 := Finset.card_erase_of_mem hh
        have hSAA : ∑ h ∈ A, (G.neighborFinset h ∩ A).card ≤ A.card * (A.card - 1) := by
          calc ∑ h ∈ A, (G.neighborFinset h ∩ A).card
              ≤ ∑ _h ∈ A, (A.card - 1) := Finset.sum_le_sum hAAle
            _ = A.card * (A.card - 1) := by rw [Finset.sum_const, smul_eq_mul]
        have hSAB : ∑ h ∈ A, (G.neighborFinset h ∩ Bad).card
            ≤ ∑ w ∈ Bad, (G.neighborFinset w ∩ Dᶜ).card := by
          rw [cross_count G A Bad]
          apply Finset.sum_le_sum
          intro w _
          exact Finset.card_le_card
            (Finset.inter_subset_inter (Finset.Subset.refl _) hAsubDc)
        have hpartition : ∑ w ∈ Bad, (G.neighborFinset w ∩ Dᶜ).card
            + ∑ h ∈ A, (G.neighborFinset h ∩ Dᶜ).card = 56 - 6 * D.card := by
          rw [hBaddef, hAdef, Finset.sum_filter_add_sum_filter_not Dᶜ
            (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)
            (fun w => (G.neighborFinset w ∩ Dᶜ).card)]
          exact hDcDc
        set k := A.card with hk
        clear_value k
        have hklo : 1 ≤ k := by omega
        have hkhi : k ≤ 5 := by omega
        interval_cases k <;> omega
      obtain ⟨h6, hh6Dc, hh6avoid, hh6D2⟩ := hexists
      push Not at hh6avoid
      obtain ⟨hh6x, hh6y, hh6z⟩ := hh6avoid
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
      have hw1deg : G.degree t1 = 3 := hdegD t1 ht1D
      have hw2deg : G.degree t2 = 3 := hdegD t2 ht2D
      have hw1iso : ∀ w : Fin 15, G.Adj t1 w → G.degree w ≠ 3 := by
        intro w hadj hw3
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at ht1iso0
        exact ht1iso0 w (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset t1 w).mpr hadj, (hmemD w).mpr hw3⟩)
      have hw2iso : ∀ w : Fin 15, G.Adj t2 w → G.degree w ≠ 3 := by
        intro w hadj hw3
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at ht2iso0
        exact ht2iso0 w (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset t2 w).mpr hadj, (hmemD w).mpr hw3⟩)
      right; left
      exact ⟨t1, t2, h6, x, y, z, hw1deg, hw2deg, hdeg5all h6 hh6Dc, hdegx, hdegy, hdegz,
        hh6t1.symm, hh6t2.symm, hxyA, hyzA,
        (fun ha => hw1iso x ha hdegx), (fun ha => hw1iso y ha hdegy),
        (fun ha => hw1iso z ha hdegz),
        (fun ha => hw2iso x ha hdegx), (fun ha => hw2iso y ha hdegy),
        (fun ha => hw2iso z ha hdegz),
        hh6x, hh6y, hh6z, ht12ne,
        ht1nx, ht1ny, ht1nz, ht2nx, ht2ny, ht2nz,
        (by rintro rfl; exact (Finset.mem_compl.mp hh6Dc) hxD),
        (by rintro rfl; exact (Finset.mem_compl.mp hh6Dc) hyD),
        (by rintro rfl; exact (Finset.mem_compl.mp hh6Dc) hzD),
        hxy_ne, hyz_ne, hxz_ne⟩
  · -- **Induced-`C₅` branch is impossible at `e(M) = 2`.**  Each cycle vertex has two `D`-neighbours,
    -- so contributes `≥ 2` to `s`; the five together force `s ≥ 10 > 4`.
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_fifteen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 15, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 15)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

/-- **Three-way alignment dichotomy for `n = 15`, `e(M) = 3` (open: structural selection).**
At `s = 6` (`M` a single `P₄` or a `P₃ + K₂`) the covering combination is again
`SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig`.  Ported from `exists_align_six_config`
(TwinCert14Align6.lean:80) and its dense branch `exists_align_six_config_dense`
(TwinCert14Align6Dense.lean:248).  For `n = 15` the dominant route is `TwoTwin` via
`dense_two_twin_assemble`.  EXCEPTION: the `|Hub| = 7, e(M) = 3, P₄` corner where a few graphs
require `SingleVertex`/`TwoHub` rather than `TwoTwin` (use the full three-way fallback there).
DECOMPOSITION: port `exists_align_six_config` + `exists_align_six_config_dense` and the
`hub_meets_path_le_one_fifteen` / `nonisolated_component_bound` structure lemmas. -/
theorem exists_align_six_config_fifteen (G : SimpleGraph (Fin 15))
    (hm : G.edgeFinset.card = 26) (h3 : ∀ v : Fin 15, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 15, ({a, b, c, d, e} : Finset (Fin 15)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 15, G.degree t = 3 ∧ ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3)
    (hs6 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 6) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hdegD : ∀ v : Fin 15, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  -- **Cardinalities.**  `|D| ∈ {8, 9}`, `|Hub| ∈ {6, 7}`, `|Iso| ≥ 4`.
  obtain ⟨hHub7, hD8⟩ := residual_hub_card_le_seven G hm h3
  obtain ⟨hpart, hhand⟩ := handshake_fifteen G hm h3
  rw [← hDdef] at hD8 hpart hhand
  rw [hs6] at hhand
  have hHub6 : 6 ≤ (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card := by omega
  have hIso4 : 4 ≤ (D.filter
      (fun v => (G.neighborFinset v ∩ D).card = 0)).card := by
    have hnb := nonisolated_component_bound G D hmemD h2k2
    rw [hs6] at hnb
    have hpartIso := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    omega
  obtain ⟨k, t₁, t₂, hkdeg4, ht12, ht1deg, ht2deg, hAt1k, hAt2k, ht1iso, ht2iso⟩ :=
    exists_shared_deg4_hub_fifteen G hm h3 hT hC4 h2k2 hHub6 (by rw [hDdef] at hIso4; exact hIso4)
  -- An `M`-edge exists, since `s = 6 > 0`.
  have hne : ∃ a b : Fin 15, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
  · -- **Dominating-edge branch.**  A claw (`K_{1,3}`, fat centre) lands `TwoTwinConfig` via
    -- `claw_shared_two_twin_fifteen`; the `P₄` case (both dominating endpoints have in-`M`-degree
    -- `2`) is the single documented `sorry` (the analogue of the `n = 14` `P₄` global hub count).
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
    by_cases hc1three : 3 ≤ (G.neighborFinset c₁ ∩ D).card
    · exact Or.inr (Or.inl (claw_shared_two_twin_fifteen G D hmemD hT hC4 c₁ t₁ t₂ k hc1D
        hc1three ht1deg ht2deg hkdeg4 ht12 hAt1k hAt2k ht1iso ht2iso))
    · by_cases hc2three : 3 ≤ (G.neighborFinset c₂ ∩ D).card
      · exact Or.inr (Or.inl (claw_shared_two_twin_fifteen G D hmemD hT hC4 c₂ t₁ t₂ k hc2D
          hc2three ht1deg ht2deg hkdeg4 ht12 hAt1k hAt2k ht1iso ht2iso))
      · -- **`P₄` case.**  Both dominating endpoints have in-`M`-degree `2`; the degree-`3` subgraph
        -- is the path `L₁–c₁–c₂–L₂`.  For `|D| = 9` (`|Hub| = 6`) the hub-internal sum is `4`, so a
        -- cherry-avoiding hub carries two `M`-isolated twins (`TwoTwinConfig`).  The `|D| = 8`
        -- (`|Hub| = 7`) corner has hub-internal sum `10`, too loose for the `TwoTwin` count, and
        -- needs the `SingleVertex`/`TwoHub` route — the single documented `sorry`.
        classical
        set Iso : Finset (Fin 15) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)
          with hIsodef
        have hIsoprop : ∀ v ∈ Iso,
            G.degree v = 3 ∧ (∀ w : Fin 15, G.Adj v w → G.degree w ≠ 3) := by
          intro v hv
          rw [hIsodef, Finset.mem_filter] at hv
          obtain ⟨hvD, hv0⟩ := hv
          refine ⟨hdegD v hvD, fun w hadj hw3 => ?_⟩
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
          exact hv0 w (Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
        have hsum52 : ∑ v : Fin 15, G.degree v = 52 := by
          rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
        have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
          rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul,
            mul_comm]
        have hcc : D.card + Dᶜ.card = 15 := by
          have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
        have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 52 := by
          rw [Finset.sum_add_sum_compl]; exact hsum52
        have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
          intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
        have hD89 : D.card = 8 ∨ D.card = 9 := by omega
        have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 52 - 3 * D.card := by
          rw [hsumDt] at hsumsplit; omega
        have hdeg5all : ∀ w ∈ Dᶜ, G.degree w ≤ 5 := by
          intro w hw
          have hsplit := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
          have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
            have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
              fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
            have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
            simpa [smul_eq_mul, mul_comm] using this
          have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
          omega
        -- In-`M`-degrees of the dominating endpoints are both `2` (path leaves `L₁`, `L₂`).
        have hform := thin_eM_formula_fifteen G D c₁ c₂ hc1D hc2D hc12 hcov
        rw [hs6] at hform
        have hin1 : (G.neighborFinset c₁ ∩ D).card = 2 := by omega
        have hin2 : (G.neighborFinset c₂ ∩ D).card = 2 := by omega
        have hc1deg : G.degree c₁ = 3 := hdegD c₁ hc1D
        have hc2deg : G.degree c₂ = 3 := hdegD c₂ hc2D
        have hc2mem1 : c₂ ∈ G.neighborFinset c₁ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
        have hc1mem2 : c₁ ∈ G.neighborFinset c₂ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
        have herase1 : ((G.neighborFinset c₁ ∩ D).erase c₂).card = 1 := by
          rw [Finset.card_erase_of_mem hc2mem1, hin1]
        have herase2 : ((G.neighborFinset c₂ ∩ D).erase c₁).card = 1 := by
          rw [Finset.card_erase_of_mem hc1mem2, hin2]
        obtain ⟨L₁, hL1eq⟩ := Finset.card_eq_one.mp herase1
        obtain ⟨L₂, hL2eq⟩ := Finset.card_eq_one.mp herase2
        have hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁} := by
          rw [← Finset.insert_erase hc2mem1, hL1eq]
        have hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂} := by
          rw [← Finset.insert_erase hc1mem2, hL2eq]
        have hL1mem : L₁ ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by rw [hL1eq]; simp
        rw [Finset.mem_erase] at hL1mem
        obtain ⟨hL1nc2, hL1ND⟩ := hL1mem
        obtain ⟨hL1N, hL1D⟩ := Finset.mem_inter.mp hL1ND
        have hac1L1 : G.Adj c₁ L₁ := (G.mem_neighborFinset _ _).mp hL1N
        have hL1deg : G.degree L₁ = 3 := hdegD L₁ hL1D
        have hL2mem : L₂ ∈ (G.neighborFinset c₂ ∩ D).erase c₁ := by rw [hL2eq]; simp
        rw [Finset.mem_erase] at hL2mem
        obtain ⟨hL2nc1, hL2ND⟩ := hL2mem
        obtain ⟨hL2N, hL2D⟩ := Finset.mem_inter.mp hL2ND
        have hac2L2 : G.Adj c₂ L₂ := (G.mem_neighborFinset _ _).mp hL2N
        have hL2deg : G.degree L₂ = 3 := hdegD L₂ hL2D
        have hnL1c2 : ¬G.Adj L₁ c₂ := fun hadj =>
          hT ⟨c₁, L₁, c₂, hac1L1.ne, hL1nc2, hc12.ne, hac1L1, hadj, hc12, by omega⟩
        have hnc1L2 : ¬G.Adj c₁ L₂ := fun hadj =>
          hT ⟨c₂, L₂, c₁, hac2L2.ne, hL2nc1, hc12.ne.symm, hac2L2, hadj.symm, hc12.symm, by omega⟩
        have hisochar : ∀ w : Fin 15, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso := by
          intro w hwD hwL1 hwc1 hwc2 hwL2
          rw [hIsodef, Finset.mem_filter]
          refine ⟨hwD, ?_⟩
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro u hu
          rw [Finset.mem_inter, G.mem_neighborFinset] at hu
          obtain ⟨hwu, huD⟩ := hu
          rcases hcov w u hwD huD hwu with e | e | e | e
          · exact hwc1 e
          · exact hwc2 e
          · have hmem : w ∈ G.neighborFinset c₁ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hwu).symm, hwD⟩
            rw [hNc1D] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h'
            · exact hwc2 h'
            · exact hwL1 h'
          · have hmem : w ∈ G.neighborFinset c₂ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hwu).symm, hwD⟩
            rw [hNc2D] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h'
            · exact hwc1 h'
            · exact hwL2 h'
        have hdegsplit : ∀ v : Fin 15,
            (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
          intro v
          have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) := by
            apply Finset.disjoint_left.mpr
            intro a ha ha'
            rw [Finset.mem_inter] at ha ha'
            exact (Finset.mem_compl.mp ha'.2) ha.2
          have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ)
              = G.neighborFinset v := by
            rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
          rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
        have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
            = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count G D Dᶜ
        have hsumD_NHub : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card = 3 * D.card - 6 := by
          have hcong : ∑ v ∈ D, ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
              = ∑ v ∈ D, G.degree v :=
            Finset.sum_congr rfl (fun v _ => hdegsplit v)
          rw [Finset.sum_add_distrib, hs6, hsumDt] at hcong
          omega
        have hSumHubInt : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 58 - 6 * D.card := by
          have hcong : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card)
              = ∑ w ∈ Dᶜ, G.degree w :=
            Finset.sum_congr rfl (fun w _ => hdegsplit w)
          rw [Finset.sum_add_distrib, ← hcross, hsumD_NHub, hsumDcdeg] at hcong
          omega
        rcases hD89 with hD8eq | hD9eq
        · -- **`|D| = 8` (`|Hub| = 7`) corner.**  Seven hubs all of degree `4`, hub-internal sum
          -- `10` (`5` hub-hub edges).  Dispatch on the three signed-cut configs in order; when all
          -- three fail, the residual hub-triangle existence (`exists_hub_triangle_config_residual`)
          -- supplies `HubTriangleConfig`.
          have hdeg4all : ∀ w : Fin 15, w ∈ Dᶜ → G.degree w = 4 := by
            intro w hw
            have hsplit := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
            have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
              have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
                fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
              have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
              simpa [smul_eq_mul, mul_comm] using this
            have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
            have hsum28 : ∑ v ∈ Dᶜ, G.degree v = 28 := by rw [hsumDcdeg, hD8eq]
            have hd4 := hDcdeg w hw
            rw [hsum28] at hsplit
            omega
          by_cases hsv : SingleVertexConfig G
          · exact Or.inl hsv
          by_cases htt : TwoTwinConfig G
          · exact Or.inr (Or.inl htt)
          by_cases hth : TwoHubConfig G
          · exact Or.inr (Or.inr (Or.inl hth))
          · exact Or.inr (Or.inr (Or.inr (exists_hub_triangle_config_residual G D Iso L₁ c₁ c₂ L₂
              hT hC4 hK23 hmemD hIsodef hIsoprop hisochar hcov hNc1D hNc2D
              hc1deg hc2deg hL1deg hL2deg hac1L1 hc12 hac2L2 hnL1c2 hnc1L2
              hL1nc2 hL2nc1 hdeg4all hSumHubInt hD8eq hsv htt hth)))
        · -- **`|D| = 9` (`|Hub| = 6`) corner.**  Hub-internal sum `4`; cherry-avoiding hub carries
          -- two `M`-isolated twins.
          have hDccard6 : Dᶜ.card = 6 := by omega
          have hint3 : ∀ g : Fin 15, g ∈ Dᶜ →
              (G.neighborFinset g ∩ D ⊆ G.neighborFinset g ∩ Iso) →
              (G.neighborFinset g ∩ Iso).card ≤ 1 →
              3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
            intro g hg hsub htw
            have hc := le_trans (Finset.card_le_card hsub) htw
            have hds := hdegsplit g
            have hdg := hDcdeg g hg
            omega
          have hint2 : ∀ (g a : Fin 15), g ∈ Dᶜ →
              (G.neighborFinset g ∩ D ⊆ insert a (G.neighborFinset g ∩ Iso)) →
              (G.neighborFinset g ∩ Iso).card ≤ 1 →
              2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
            intro g a hg hsub htw
            have hc := Finset.card_le_card hsub
            have hc2 := Finset.card_insert_le a (G.neighborFinset g ∩ Iso)
            have hds := hdegsplit g
            have hdg := hDcdeg g hg
            omega
          have hwin : ∃ g : Fin 15, g ∈ Dᶜ ∧
              ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) ∧
              2 ≤ (G.neighborFinset g ∩ Iso).card := by
            by_contra hcon
            have htwle : ∀ g : Fin 15, g ∈ Dᶜ →
                ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                  (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
                (G.neighborFinset g ∩ Iso).card ≤ 1 := by
              intro g hg hav
              by_contra hcard
              exact hcon ⟨g, hg, hav, by omega⟩
            have hsub1 : ∀ g : Fin 15, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ →
                G.neighborFinset g ∩ D ⊆ insert L₂ (G.neighborFinset g ∩ Iso) := by
              intro g hgL1 hgc1 hgc2 w hw
              rw [Finset.mem_inter, G.mem_neighborFinset] at hw
              obtain ⟨hgw, hwD⟩ := hw
              by_cases hwL2 : w = L₂
              · rw [hwL2]; exact Finset.mem_insert_self _ _
              · have hwL1 : w ≠ L₁ := fun e => hgL1 (e ▸ hgw)
                have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
                have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
                exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr
                  ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩)
            have hsub1' : ∀ g : Fin 15, ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
                G.neighborFinset g ∩ D ⊆ insert L₁ (G.neighborFinset g ∩ Iso) := by
              intro g hgc1 hgc2 hgL2 w hw
              rw [Finset.mem_inter, G.mem_neighborFinset] at hw
              obtain ⟨hgw, hwD⟩ := hw
              by_cases hwL1 : w = L₁
              · rw [hwL1]; exact Finset.mem_insert_self _ _
              · have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
                have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
                have hwL2 : w ≠ L₂ := fun e => hgL2 (e ▸ hgw)
                exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr
                  ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩)
            have hsub2 : ∀ g : Fin 15, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
                G.neighborFinset g ∩ D ⊆ G.neighborFinset g ∩ Iso := by
              intro g hgL1 hgc1 hgc2 hgL2 w hw
              rw [Finset.mem_inter, G.mem_neighborFinset] at hw
              obtain ⟨hgw, hwD⟩ := hw
              have hwL1 : w ≠ L₁ := fun e => hgL1 (e ▸ hgw)
              have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
              have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
              have hwL2 : w ≠ L₂ := fun e => hgL2 (e ▸ hgw)
              exact Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩
            set P : Finset (Fin 15) := Dᶜ.filter
              (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hPdef
            set Q : Finset (Fin 15) := Dᶜ.filter
              (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hQdef
            set R : Finset (Fin 15) := Dᶜ.filter
              (fun g => (¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) with hRdef
            have hpt : ∀ g ∈ Dᶜ,
                (if (¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) then (1 : ℕ) else 0)
                  + (if (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) then (1 : ℕ) else 0)
                  + (if ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) then (1 : ℕ) else 0)
                  ≤ (G.neighborFinset g ∩ Dᶜ).card := by
              intro g hg
              by_cases ha1 : (¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) <;>
                by_cases ha2 : (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)
              · rw [if_pos ha1, if_pos ha2, if_pos (Or.inl ha1)]
                obtain ⟨hgL1, hgc1, hgc2⟩ := ha1
                obtain ⟨_, _, hgL2⟩ := ha2
                have hi3 := hint3 g hg (hsub2 g hgL1 hgc1 hgc2 hgL2)
                  (htwle g hg (Or.inl ⟨hgL1, hgc1, hgc2⟩))
                omega
              · rw [if_pos ha1, if_neg ha2, if_pos (Or.inl ha1)]
                obtain ⟨hgL1, hgc1, hgc2⟩ := ha1
                have hi2 := hint2 g L₂ hg (hsub1 g hgL1 hgc1 hgc2)
                  (htwle g hg (Or.inl ⟨hgL1, hgc1, hgc2⟩))
                omega
              · rw [if_neg ha1, if_pos ha2, if_pos (Or.inr ha2)]
                obtain ⟨hgc1, hgc2, hgL2⟩ := ha2
                have hi2 := hint2 g L₁ hg (hsub1' g hgc1 hgc2 hgL2)
                  (htwle g hg (Or.inr ⟨hgc1, hgc2, hgL2⟩))
                omega
              · rw [if_neg ha1, if_neg ha2, if_neg (not_or.mpr ⟨ha1, ha2⟩)]
                omega
            have hP6 : P.card = ∑ g ∈ Dᶜ,
                (if (¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) then (1 : ℕ) else 0) := by
              rw [hPdef, Finset.card_filter]
            have hQ6 : Q.card = ∑ g ∈ Dᶜ,
                (if (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) then (1 : ℕ) else 0) := by
              rw [hQdef, Finset.card_filter]
            have hR6 : R.card = ∑ g ∈ Dᶜ,
                (if ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                      (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) then (1 : ℕ) else 0) := by
              rw [hRdef, Finset.card_filter]
            have hPQR6 : P.card + Q.card + R.card ≤ 58 - 6 * D.card := by
              rw [hP6, hQ6, hR6, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              calc ∑ g ∈ Dᶜ, _ ≤ ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card :=
                    Finset.sum_le_sum hpt
                _ = 58 - 6 * D.card := hSumHubInt
            have hcc1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1 := by
              have := hdegsplit c₁; rw [hc1deg, hin1] at this; omega
            have hcc2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1 := by
              have := hdegsplit c₂; rw [hc2deg, hin2] at this; omega
            have hcL1 : (G.neighborFinset L₁ ∩ Dᶜ).card ≤ 2 := by
              have hp := hdegsplit L₁
              have hpos : 1 ≤ (G.neighborFinset L₁ ∩ D).card := Finset.card_pos.mpr
                ⟨c₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩⟩
              rw [hL1deg] at hp; omega
            have hcL2 : (G.neighborFinset L₂ ∩ Dᶜ).card ≤ 2 := by
              have hp := hdegsplit L₂
              have hpos : 1 ≤ (G.neighborFinset L₂ ∩ D).card := Finset.card_pos.mpr
                ⟨c₂, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩⟩
              rw [hL2deg] at hp; omega
            have hPcard : 2 ≤ P.card := by
              have hsubP : Dᶜ \ P ⊆ (G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₁ ∩ Dᶜ)
                  ∪ (G.neighborFinset c₂ ∩ Dᶜ) := by
                intro g hg
                obtain ⟨hgDc, hgnP⟩ := Finset.mem_sdiff.mp hg
                rw [hPdef] at hgnP
                have hnav : ¬(¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) :=
                  fun hpred => hgnP (Finset.mem_filter.mpr ⟨hgDc, hpred⟩)
                have hor : G.Adj g L₁ ∨ G.Adj g c₁ ∨ G.Adj g c₂ := by
                  by_contra hc; push Not at hc; exact hnav ⟨hc.1, hc.2.1, hc.2.2⟩
                rcases hor with h | h | h
                · exact Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
                · exact Finset.mem_union_left _ (Finset.mem_union_right _
                    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
                · exact Finset.mem_union_right _
                    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)
              have hubcard : (Dᶜ \ P).card ≤ 4 := by
                refine le_trans (Finset.card_le_card hsubP) ?_
                refine le_trans (Finset.card_union_le _ _) ?_
                have h1 := Finset.card_union_le (G.neighborFinset L₁ ∩ Dᶜ)
                  (G.neighborFinset c₁ ∩ Dᶜ)
                omega
              have hle := Finset.card_le_card_sdiff_add_card (s := Dᶜ) (t := P)
              omega
            have hQcard : 2 ≤ Q.card := by
              have hsubQ : Dᶜ \ Q ⊆ (G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ)
                  ∪ (G.neighborFinset L₂ ∩ Dᶜ) := by
                intro g hg
                obtain ⟨hgDc, hgnQ⟩ := Finset.mem_sdiff.mp hg
                rw [hQdef] at hgnQ
                have hnav : ¬(¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) :=
                  fun hpred => hgnQ (Finset.mem_filter.mpr ⟨hgDc, hpred⟩)
                have hor : G.Adj g c₁ ∨ G.Adj g c₂ ∨ G.Adj g L₂ := by
                  by_contra hc; push Not at hc; exact hnav ⟨hc.1, hc.2.1, hc.2.2⟩
                rcases hor with h | h | h
                · exact Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
                · exact Finset.mem_union_left _ (Finset.mem_union_right _
                    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
                · exact Finset.mem_union_right _
                    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)
              have hubcard : (Dᶜ \ Q).card ≤ 4 := by
                refine le_trans (Finset.card_le_card hsubQ) ?_
                refine le_trans (Finset.card_union_le _ _) ?_
                have h1 := Finset.card_union_le (G.neighborFinset c₁ ∩ Dᶜ)
                  (G.neighborFinset c₂ ∩ Dᶜ)
                omega
              have hle := Finset.card_le_card_sdiff_add_card (s := Dᶜ) (t := Q)
              omega
            have hRPQ : R = P ∪ Q := by rw [hRdef, hPdef, hQdef, Finset.filter_or]
            have hPleR : P.card ≤ R.card :=
              Finset.card_le_card (by rw [hRPQ]; exact Finset.subset_union_left)
            omega
          obtain ⟨g, hgDc, havoid, hg2⟩ := hwin
          obtain ⟨s1, hs1m, s2, hs2m, hs12⟩ :=
            Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset g ∩ Iso).card)
          rw [Finset.mem_inter, G.mem_neighborFinset] at hs1m hs2m
          obtain ⟨hgs1, hs1Iso⟩ := hs1m
          obtain ⟨hgs2, hs2Iso⟩ := hs2m
          obtain ⟨hs1deg, hs1iso⟩ := hIsoprop s1 hs1Iso
          obtain ⟨hs2deg, hs2iso⟩ := hIsoprop s2 hs2Iso
          right; left
          rcases havoid with ⟨hgL1, hgc1, hgc2⟩ | ⟨hgc1, hgc2, hgL2⟩
          · exact ⟨s1, s2, g, L₁, c₁, c₂, hs1deg, hs2deg, hdeg5all g hgDc,
              hL1deg, hc1deg, hc2deg, hgs1.symm, hgs2.symm, hac1L1.symm, hc12,
              (fun ha => hs1iso L₁ ha hL1deg), (fun ha => hs1iso c₁ ha hc1deg),
              (fun ha => hs1iso c₂ ha hc2deg),
              (fun ha => hs2iso L₁ ha hL1deg), (fun ha => hs2iso c₁ ha hc1deg),
              (fun ha => hs2iso c₂ ha hc2deg),
              hgL1, hgc1, hgc2, hs12,
              (by rintro rfl; exact hs1iso c₁ hac1L1.symm hc1deg),
              (by rintro rfl; exact hs1iso c₂ hc12 hc2deg),
              (by rintro rfl; exact hs1iso c₁ hc12.symm hc1deg),
              (by rintro rfl; exact hs2iso c₁ hac1L1.symm hc1deg),
              (by rintro rfl; exact hs2iso c₂ hc12 hc2deg),
              (by rintro rfl; exact hs2iso c₁ hc12.symm hc1deg),
              (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hL1D),
              (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc1D),
              (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc2D),
              hac1L1.symm.ne, hc12.ne, hL1nc2⟩
          · exact ⟨s1, s2, g, c₁, c₂, L₂, hs1deg, hs2deg, hdeg5all g hgDc,
              hc1deg, hc2deg, hL2deg, hgs1.symm, hgs2.symm, hc12, hac2L2,
              (fun ha => hs1iso c₁ ha hc1deg), (fun ha => hs1iso c₂ ha hc2deg),
              (fun ha => hs1iso L₂ ha hL2deg),
              (fun ha => hs2iso c₁ ha hc1deg), (fun ha => hs2iso c₂ ha hc2deg),
              (fun ha => hs2iso L₂ ha hL2deg),
              hgc1, hgc2, hgL2, hs12,
              (by rintro rfl; exact hs1iso c₂ hc12 hc2deg),
              (by rintro rfl; exact hs1iso L₂ hac2L2 hL2deg),
              (by rintro rfl; exact hs1iso c₂ hac2L2.symm hc2deg),
              (by rintro rfl; exact hs2iso c₂ hc12 hc2deg),
              (by rintro rfl; exact hs2iso L₂ hac2L2 hL2deg),
              (by rintro rfl; exact hs2iso c₂ hac2L2.symm hc2deg),
              (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc1D),
              (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc2D),
              (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hL2D),
              hc12.ne, hac2L2.ne, hL2nc1.symm⟩
  · -- **Induced-`C₅` branch is impossible at `e(M) = 3`.**  Each cycle vertex has two `D`-neighbours,
    -- so contributes `≥ 2` to `s`; the five together force `s ≥ 10 > 6`.
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_fifteen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 15, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 15)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

/-- **Three-way alignment dichotomy for `n = 15`, `e(M) ≥ 4` (open: structural selection).**
At `s ≥ 8` (so `s ∈ {8, 10}`, i.e. `e(M) ∈ {4, 5}`) the covering combination is
`SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig`.  Ported from `halign8`
(TwinCert14Align8.lean:803).  `n = 15` EXCEPTION: `|Hub| = 5` (`|D| = 10`, `e(M) ≥ 4`) where an
isolated twin may meet two degree-`5` hubs — route around `isolated_twin_two_deg4_hubs` and use a
degree-`5` shared hub in `two_twin_cut_certificate_fifteen` (which permits degree `≤ 5`).
DECOMPOSITION: port `halign8`; add the `|Hub| = 5` deg-`5`-shared-hub sub-branch via
`dense_two_twin_assemble` generalized to `deg h ≤ 5`. -/
theorem halign8_fifteen (G : SimpleGraph (Fin 15))
    (hm : G.edgeFinset.card = 26) (h3 : ∀ v : Fin 15, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 15, ({a, b, c, d, e} : Finset (Fin 15)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 15, G.degree t = 3 ∧ ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3)
    (hge : 8 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 15, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  obtain ⟨t, ht3, htiso⟩ := hiso
  have htcard : (G.neighborFinset t).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, ht3]
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp htcard
  have htp : G.Adj t p := by
    have : p ∈ G.neighborFinset t := by rw [hset]; simp
    exact (G.mem_neighborFinset _ _).mp this
  have htq : G.Adj t q := by
    have : q ∈ G.neighborFinset t := by rw [hset]; simp
    exact (G.mem_neighborFinset _ _).mp this
  have htr : G.Adj t r := by
    have : r ∈ G.neighborFinset t := by rw [hset]; simp
    exact (G.mem_neighborFinset _ _).mp this
  by_cases hall : G.degree p = 4 ∧ G.degree q = 4 ∧ G.degree r = 4
  · obtain ⟨hp4', hq4', hr4'⟩ := hall
    have hne : ∃ a b : Fin 15, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
    · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
      by_cases hsum10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10
      · obtain ⟨hin1, hin2⟩ :=
          dom_centres_indeg3 G D c₁ c₂ hc1D hc2D hc12 hindle hcov hsum10
        exact Or.inl (single_vertex_doublestar_count G D hmemD hT hC4 t p q r
          ht3 htiso hp4' hq4' hr4' hpq hpr hqr htp htq htr c₁ c₂ hc1D hc2D hc12 hin1 hin2 hcov)
      · -- `∑ = 8` (`e(M) = 4`): the dominating `(3, 2)` double-star.  One centre is a fat centre
        -- (in-`M`-degree `3`); a shared degree-`4` hub of two `M`-isolated twins lands `TwoTwinConfig`.
        have hform := thin_eM_formula_fifteen G D c₁ c₂ hc1D hc2D hc12 hcov
        have hsle1 := hindle c₁ hc1D
        have hsle2 := hindle c₂ hc2D
        have hs8 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 8 := by omega
        have hshare : ∃ h t₁ t₂ : Fin 15, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
            G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
            (∀ w : Fin 15, G.Adj t₁ w → G.degree w ≠ 3) ∧
            (∀ w : Fin 15, G.Adj t₂ w → G.degree w ≠ 3) := by
          by_cases hg5 : ∃ g : Fin 15, 5 ≤ G.degree g
          · obtain ⟨g, hg5'⟩ := hg5
            exact shared_deg4_hub_deg5_fifteen G hm h3 hT hC4 h2k2 g hg5'
          · push Not at hg5
            exact shared_deg4_hub_nodeg5_fifteen G hm h3 h2k2 (fun v => by have := hg5 v; omega) hs8
        obtain ⟨k, tw1, tw2, hkdeg4, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso,
          htw2iso⟩ := hshare
        exact Or.inr (Or.inl (dom_fat_centre_two_twin_fifteen G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12
          hcov hge hindle k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso))
    · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
        e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
      exact Or.inl (single_vertex_config_from_C5_three_hubs G hT hC4 t p q r
        ht3 htiso hp4' hq4' hr4' hpq hpr hqr htp htq htr v₁ v₂ v₃ v₄ v₅
        ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
        ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
        e12 e23 e34 e45 e51 n13 n14 n24 n25 n35)
  · -- A hub of `t` has degree `≥ 5`: the degree-`5`-hub residual.  By `single_twin_deg5_structure`
    -- there is a unique degree-`5` hub `g` and four degree-`4` hubs; a pigeonhole on the three
    -- `M`-isolated twins forces two to share a degree-`4` hub `k`.  The residual graph then has a
    -- dominating edge (fat centre, claw) or an induced `C₅`; either feeds `TwoTwinConfig`.
    have hpge4 : 4 ≤ G.degree p := by have := htiso p htp; have := h3 p; omega
    have hqge4 : 4 ≤ G.degree q := by have := htiso q htq; have := h3 q; omega
    have hrge4 : 4 ≤ G.degree r := by have := htiso r htr; have := h3 r; omega
    have hg5 : ∃ g : Fin 15, 5 ≤ G.degree g := by
      by_contra hcon
      push Not at hcon
      exact hall ⟨by have := hcon p; omega, by have := hcon q; omega, by have := hcon r; omega⟩
    obtain ⟨g, hg5'⟩ := hg5
    obtain ⟨k, tw1, tw2, hkdeg4, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso,
      htw2iso⟩ := shared_deg4_hub_deg5_fifteen G hm h3 hT hC4 h2k2 g hg5'
    have hne : ∃ a b : Fin 15, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
    · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
      exact Or.inr (Or.inl (dom_fat_centre_two_twin_fifteen G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12
        hcov hge hindle k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso))
    · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
        e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
      exact Or.inr (Or.inl (c5_shared_two_twin_fifteen G hT hC4 k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg
        hAtw1k hAtw2k htw1iso htw2iso v₁ v₂ v₃ v₄ v₅
        ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
        ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
        e12 e23 e34 e45 e51 n13 n14 n24 n25 n35))


end N15

end ACMax
