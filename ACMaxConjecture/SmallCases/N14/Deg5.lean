import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.Align
import ACMaxConjecture.SmallCases.N14.Doublestar

/-!
# Degree-`5` cluster foundations and double-star alignment for `n = 14`

This file collects the structural foundations for the residual deg-`5` regime of the single-twin
alignment (`single_twin_deg5_core` in `TwinCert14`), where the working `M`-isolated twin has a
degree-`5` hub-neighbour.

* `single_twin_deg5_structure` — pure handshake/excess counting: in the deg-`5` regime there are
  exactly `|D| = 9` degree-`3` vertices, `|Hub| = 5` hubs, a *unique* degree-`5` vertex `g`, and all
  other hubs have degree exactly `4`.

Both are sorry-free structural foundations; the deg-`5` alignment is now routed through the
`TwoTwinConfig` branch of `halign8` (`TwinCert14Align8`), so the former single-twin perfect-cover
selector (`single_twin_doublestar_two_hubs_gen`) has been removed as superseded dead code.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Degree-`5` structure theorem.**  In the deg-`5` regime (`∑ degrees = 48`, minimum degree `3`,
`e(M) ≤ 5` so `∑_{v∈D}|N v ∩ D| ≤ 10`, and a vertex `g` of degree `≥ 5`): the excess over `3` is
`48 − 42 = 6`; the double count gives `|D| ≤ 9`, and `g`'s excess `≥ 2` pushes `|D| ≥ 9`, so
`|D| = 9` and `|Hub| = 5`.  The hub-degree sum is `21 = 5 + 4·4`, forcing `g` to have degree exactly
`5` and every other hub degree exactly `4`. -/
theorem single_twin_deg5_structure (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (heM : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 10)
    (g : Fin 14) (hg5 : 5 ≤ G.degree g) :
    (Finset.univ.filter (fun w => G.degree w = 3)).card = 9 ∧
      (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card = 5 ∧
      G.degree g = 5 ∧
      ∀ w : Fin 14, G.degree w ≠ 3 → w ≠ g → G.degree w = 4 := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hsum : ∑ v : Fin 14, G.degree v = 48 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumDc : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 48 := by
    rw [Finset.sum_add_sum_compl]; exact hsum
  have hcc : D.card + Dᶜ.card = 14 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h
    exact h
  have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
    intro w hw
    rw [Finset.mem_compl, hmemD] at hw
    have := h3 w; omega
  -- Double count `D → Dᶜ` edges to bound `|D| ≤ 9`.
  have hkey : ∀ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card + (G.neighborFinset v ∩ D).card
      = G.degree v := by
    intro v _
    have heq : G.neighborFinset v ∩ Dᶜ = G.neighborFinset v \ D := by
      ext w; simp [Finset.mem_sdiff, Finset.mem_compl]
    rw [heq]
    have := Finset.card_sdiff_add_card_inter (G.neighborFinset v) D
    rw [G.card_neighborFinset_eq_degree] at this
    exact this
  have hAs : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
      + ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 3 * D.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hkey, hsumD]
  have hcross := cross_count_fourteen G D Dᶜ
  have hAle : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dᶜ, G.degree w := by
    apply Finset.sum_le_sum
    intro w _
    calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree w := G.card_neighborFinset_eq_degree w
  have hDcard : D.card ≤ 9 := by
    rw [hcross] at hAs
    omega
  -- `g` lies in `Dᶜ`.
  have hgDc : g ∈ Dᶜ := by rw [Finset.mem_compl, hmemD]; omega
  have hsplitg : ∑ v ∈ Dᶜ, G.degree v = G.degree g + ∑ v ∈ Dᶜ.erase g, G.degree v :=
    (Finset.add_sum_erase _ (fun v => G.degree v) hgDc).symm
  have hrest : 4 * (Dᶜ.erase g).card ≤ ∑ v ∈ Dᶜ.erase g, G.degree v := by
    have hb : ∀ x ∈ Dᶜ.erase g, 4 ≤ G.degree x := fun x hx =>
      hDcdeg x (Finset.mem_of_mem_erase hx)
    have h := Finset.card_nsmul_le_sum (Dᶜ.erase g) (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul, mul_comm] using h
  have hcg : (Dᶜ.erase g).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hgDc
  -- `|D| ≥ 9` from `g`'s excess, hence `|D| = 9`, `|Dᶜ| = 5`.
  have hD9 : D.card = 9 := by omega
  have hDc5 : Dᶜ.card = 5 := by omega
  -- `g` has degree exactly `5`.
  have hdg5 : G.degree g = 5 := by omega
  -- Hub filter equals `Dᶜ`.
  have hHub : Finset.univ.filter (fun v => 4 ≤ G.degree v) = Dᶜ := by
    ext w
    rw [Finset.mem_filter, Finset.mem_compl]
    simp only [Finset.mem_univ, true_and]
    rw [hmemD]
    have := h3 w
    omega
  -- Every other hub has degree exactly `4`.
  have hother : ∀ w : Fin 14, G.degree w ≠ 3 → w ≠ g → G.degree w = 4 := by
    intro w hw3 hwg
    have hwDc : w ∈ Dᶜ := by rw [Finset.mem_compl, hmemD]; exact hw3
    have hwe : w ∈ Dᶜ.erase g := Finset.mem_erase.mpr ⟨hwg, hwDc⟩
    have hsplitw : ∑ v ∈ Dᶜ.erase g, G.degree v
        = G.degree w + ∑ v ∈ (Dᶜ.erase g).erase w, G.degree v :=
      (Finset.add_sum_erase _ (fun v => G.degree v) hwe).symm
    have hrest2 : 4 * ((Dᶜ.erase g).erase w).card
        ≤ ∑ v ∈ (Dᶜ.erase g).erase w, G.degree v := by
      have hb : ∀ x ∈ (Dᶜ.erase g).erase w, 4 ≤ G.degree x := fun x hx =>
        hDcdeg x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      have h := Finset.card_nsmul_le_sum ((Dᶜ.erase g).erase w) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hcw : ((Dᶜ.erase g).erase w).card = (Dᶜ.erase g).card - 1 :=
      Finset.card_erase_of_mem hwe
    have := hDcdeg w hwDc
    omega
  refine ⟨hD9, ?_, hdg5, hother⟩
  rw [hHub]; exact hDc5

end N14

end ACMax
