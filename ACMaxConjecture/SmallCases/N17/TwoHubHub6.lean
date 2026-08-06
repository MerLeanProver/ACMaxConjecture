import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Dense
import ACMaxConjecture.SmallCases.N17.Align8Helpers
import ACMaxConjecture.SmallCases.N17.TwoHubHub6Deg5

/-!
# `n = 17`, `|D| = 11`, `|Hub| = 6` corner selector

The `|D| = 11`, `|Hub| = 6` regime that the dense alignment dispatcher (`halign8_seventeen`) needs.
By the handshake the residual degree-excess over the six hubs is `60 − 33 = 27` over `6` hubs, i.e.
excess `3`; so the hubs are at most three degree-`5` (or one degree-`6` plus a degree-`5`, etc.).

Unlike `n = 16`, the deg-`4` shared-hub pigeonhole diverges for `n = 17` (degree sum `60` is divisible
by `3`), so the assembly routes through the deg-`≤ 5` shared hub of `TwinCert17TwoHubHub6Deg5`:

* **dominating-edge branch (fully proved):** `shared_hub_le5_eM5_seventeen` (strict because
  `|Hub| = 6`) supplies a deg-`≤ 5` hub shared by two `M`-isolated twins, and
  `dom_fat_centre_two_twin_le5_seventeen` closes the `TwoTwin` cut for any `s ∈ {8, 10}`;
* **induced-`C₅` branch:** an induced `C₅` in `M` forces `e(M) = 5` (`s = 10`).  If the cherry's
  three hub-neighbours are all degree `4`, `single_vertex_config_from_C5_three_hubs` gives a
  `SingleVertex` cut; otherwise `two_twin_eM5_seventeen` gives the `TwoTwin` cut.

This selector is therefore proved unconditionally; the only residual `sorry` of the development sits
inside `two_twin_eM5_seventeen` (the deg-`≤ 5` induced-`C₅` sub-case, which needs a deg-`≤ 5`
analogue of `hub_cycle_cases_seventeen`).
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **`|D| = 11`, `|Hub| = 6` four-way alignment selector for `n = 17` (`e(M) ≥ 4`).**
In the dense (`s := ∑_{v∈D}|N v ∩ D| ≥ 8`) `|Hub| = 6` residual, the alignment dichotomy
`TwoHubConfig ∨ SingleVertexConfig ∨ TwoTwinConfig ∨ HubTriangleConfig` holds.  The dominating-edge
branch yields a `TwoTwin` cut via the deg-`≤ 5` shared hub; an induced `C₅` (forcing `e(M) = 5`)
yields a `SingleVertex` cut (all-deg-`4` cherry) or a `TwoTwin` cut (`two_twin_eM5_seventeen`). -/
theorem two_hub_or_single_vertex_hub6_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 17, ({a, b, c, d, e} : Finset (Fin 17)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hiso : ∃ t : Fin 17, G.degree t = 3 ∧ ∀ w : Fin 17, G.Adj t w → G.degree w ≠ 3)
    (hD11 : (Finset.univ.filter (fun w : Fin 17 => G.degree w = 3)).card = 11)
    (hHub6 : (Finset.univ.filter (fun v : Fin 17 => 4 ≤ G.degree v)).card = 6)
    (hge : 8 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card) :
    TwoHubConfig G ∨ SingleVertexConfig G ∨ TwoTwinConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 17) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 17, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  have hsumle : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 10 :=
    eM_le_five G D hmemD hT hC4 h2k2
  obtain ⟨t, ht3, htiso⟩ := hiso
  have htcard : (G.neighborFinset t).card = 3 := by rw [G.card_neighborFinset_eq_degree, ht3]
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp htcard
  have htp : G.Adj t p := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  have htq : G.Adj t q := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  have htr : G.Adj t r := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  have hne : ∃ a b : Fin 17, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
  · -- **Dominating-edge branch (TwoTwin, fully proved).**  The deg-`≤ 5` shared hub from
    -- `shared_hub_le5_eM5` (strict because `|Hub| = 6`) drives the deg-`≤ 5` fat-centre cut.
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
    obtain ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
      shared_hub_le5_eM5_seventeen G hm h3 h2k2 (by rw [← hDdef]; exact hD11)
        (by rw [← hDdef]; exact hsumle)
    have hkge4 : 4 ≤ G.degree k := by have := htw1iso k hAtw1k; have := h3 k; omega
    exact Or.inr (Or.inr (Or.inl (dom_fat_centre_two_twin_le5_seventeen G D hmemD hT hC4 c₁ c₂
      hc1D hc2D hc12 hcov hge hindle k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg hAtw1k hAtw2k
      htw1iso htw2iso)))
  · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
    by_cases hall : G.degree p = 4 ∧ G.degree q = 4 ∧ G.degree r = 4
    · -- **All cherry-hubs degree `4` (SingleVertex, fully proved).**
      obtain ⟨hp4, hq4, hr4⟩ := hall
      exact Or.inr (Or.inl (single_vertex_config_from_C5_three_hubs G hT hC4 t p q r
        ht3 htiso hp4 hq4 hr4 hpq hpr hqr htp htq htr v₁ v₂ v₃ v₄ v₅
        ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
        ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
        e12 e23 e34 e45 e51 n13 n14 n24 n25 n35))
    · -- **Degree-`≥ 5` cherry-hub with an induced `C₅` (TwoTwin).**  The `C₅` forces `e(M) = 5`
      -- (`s = 10`); routed through `two_twin_eM5_seventeen` whose deg-`≤ 5` `C₅` sub-case is the
      -- single documented `sorry` of this development.
      have hsum10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10 := by
        refine le_antisymm hsumle ?_
        obtain ⟨_, d13, d14, _, _, d24, d25, _, d35, _⟩ :=
          distinct_five_seventeen v₁ v₂ v₃ v₄ v₅ hcard5
        have two_nbrs : ∀ a b c : Fin 17, G.Adj a b → G.Adj a c → b ∈ D → c ∈ D → b ≠ c →
            2 ≤ (G.neighborFinset a ∩ D).card := by
          intro a b c hab hac hbD hcD hbc
          have hsub : ({b, c} : Finset (Fin 17)) ⊆ G.neighborFinset a ∩ D := by
            intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab, hbD⟩
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac, hcD⟩
          have hbc2 : ({b, c} : Finset (Fin 17)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
          calc 2 = ({b, c} : Finset (Fin 17)).card := hbc2.symm
            _ ≤ _ := Finset.card_le_card hsub
        set C : Finset (Fin 17) := {v₁, v₂, v₃, v₄, v₅} with hCdef
        have hCsub : C ⊆ D := by
          intro w hw; rw [hCdef] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
        have hCge : ∀ v ∈ C, 2 ≤ (G.neighborFinset v ∩ D).card := by
          intro v hv; rw [hCdef] at hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with h | h | h | h | h <;> rw [h]
          · exact two_nbrs v₁ v₂ v₅ e12 e51.symm hv2D hv5D d25
          · exact two_nbrs v₂ v₁ v₃ e12.symm e23 hv1D hv3D d13
          · exact two_nbrs v₃ v₂ v₄ e23.symm e34 hv2D hv4D d24
          · exact two_nbrs v₄ v₃ v₅ e34.symm e45 hv3D hv5D d35
          · exact two_nbrs v₅ v₄ v₁ e45.symm e51 hv4D hv1D d14.symm
        have hCcard : C.card = 5 := by rw [hCdef]; exact hcard5
        have hCsum : 10 ≤ ∑ v ∈ C, (G.neighborFinset v ∩ D).card := by
          calc 10 = 2 * C.card := by rw [hCcard]
            _ = ∑ _v ∈ C, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
            _ ≤ _ := Finset.sum_le_sum hCge
        calc 10 ≤ ∑ v ∈ C, (G.neighborFinset v ∩ D).card := hCsum
          _ ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
              Finset.sum_le_sum_of_subset_of_nonneg hCsub (fun _ _ _ => Nat.zero_le _)
      exact Or.inr (Or.inr (Or.inl
        (two_twin_eM5_seventeen G hm h3 hT h2k2 hC4 hHub6 (by rw [← hDdef]; exact hsum10))))

end N17

end ACMax
