import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubHub6Deg5

/-!
# The `|D| = 10`, `e(M) = 5` induced-`C₅` shared-hub extraction (`n = 19`)

The `C₅` covers all ten `M`-incidences, so the `M`-isolated population has
`|Iso| = |D| − 5 = 5` members carrying `15` hub-incidences.  The handshake
(`Σ_Hub deg = 68 − 30 = 38` over `9` hubs) allows at most one degree-`≥ 6`
hub (`h₆ ≤ 1`) with `Σ_{H6} deg ≤ 2 + 4h₆`, so the degree-`≤ 5` hubs receive
at least `13 − 4h₆ > 9 − h₆ = |Hub₅|` incidences — the pigeonhole
`shared_hub_le5_from_count_nineteen` extracts a degree-`≤ 5` hub with two
distinct `M`-isolated twins.
-/

namespace ACMax

open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The `|D| = 10` induced-`C₅` shared-hub extraction.** -/
theorem eM5_D10_c5_shared_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hD10 : (Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card = 10)
    (v₁ v₂ v₃ v₄ v₅ : Fin 19)
    (hv1D : G.degree v₁ = 3) (hv2D : G.degree v₂ = 3) (hv3D : G.degree v₃ = 3)
    (hv4D : G.degree v₄ = 3) (hv5D : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w : Fin 19 => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card
        = 10) :
    ∃ k tw₁ tw₂ : Fin 19, G.degree k ≤ 5 ∧ tw₁ ≠ tw₂ ∧
      G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ G.Adj tw₁ k ∧ G.Adj tw₂ k ∧
      (∀ w : Fin 19, G.Adj tw₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 19, G.Adj tw₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 19) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 19, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub5 : Finset (Fin 19) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v ∧ G.degree v ≤ 5) with hHub5def
  have hmemHub5 : ∀ v : Fin 19, v ∈ Hub5 ↔ 4 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    intro v; rw [hHub5def]; simp
  set H6 : Finset (Fin 19) := Finset.univ.filter (fun v => 6 ≤ G.degree v) with hH6def
  have hmemH6 : ∀ v : Fin 19, v ∈ H6 ↔ 6 ≤ G.degree v := by intro v; rw [hH6def]; simp
  set Iso : Finset (Fin 19) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  -- `Iso.card ≥ |D| − 5 = 5`: the induced `C₅` is exactly the `M`-non-isolated set.
  have hIsoge : D.card - 5 ≤ Iso.card := by
    have hnon5 := nonIso_le_five_of_C5_nineteen G D v₁ v₂ v₃ v₄ v₅
      ((hmemD v₁).mpr hv1D) ((hmemD v₂).mpr hv2D) ((hmemD v₃).mpr hv3D) ((hmemD v₄).mpr hv4D)
      ((hmemD v₅).mpr hv5D) hcard5 e12 e23 e34 e45 e51 hsum10
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  -- Handshake: `Σ_Hub deg = 68 − 30 = 38` over `|Hub| = 9` hubs.
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum68 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
    rw [Finset.sum_add_sum_compl]; exact hsum68
  have hHubsum : ∑ v ∈ Hub, G.degree v = 68 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 19 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  -- Split `Hub` into `Hub₅` (deg `≤ 5`) and `H6` (deg `≥ 6`).
  have hHub5sub : ∀ v ∈ Hub5, 4 ≤ G.degree v := fun v hv => ((hmemHub5 v).mp hv).1
  have hH6ge : ∀ v ∈ H6, 6 ≤ G.degree v := fun v hv => (hmemH6 v).mp hv
  have hmemIso : ∀ v : Fin 19, v ∈ Iso ↔ v ∈ D ∧ (G.neighborFinset v ∩ D).card = 0 := by
    intro v; rw [hIsodef, Finset.mem_filter]
  have hdisjHub : Disjoint Hub5 H6 :=
    Finset.disjoint_left.mpr (fun a ha ha' => by
      rw [hmemHub5] at ha; rw [hmemH6] at ha'; omega)
  have huHub : Hub5 ∪ H6 = Hub := by
    ext w; rw [Finset.mem_union, hmemHub5, hmemH6, hmemHub]; omega
  have hHubpart : Hub5.card + H6.card = Hub.card := by
    rw [← huHub, Finset.card_union_of_disjoint hdisjHub]
  have hHub5degsum : 4 * Hub5.card ≤ ∑ v ∈ Hub5, G.degree v := by
    have := Finset.card_nsmul_le_sum Hub5 (fun v => G.degree v) 4 hHub5sub
    simpa [smul_eq_mul, mul_comm] using this
  have hH6degsum : 6 * H6.card ≤ ∑ v ∈ H6, G.degree v := by
    have := Finset.card_nsmul_le_sum H6 (fun v => G.degree v) 6 hH6ge
    simpa [smul_eq_mul, mul_comm] using this
  have hDcdegsplit : ∑ v ∈ Hub5, G.degree v + ∑ v ∈ H6, G.degree v = ∑ v ∈ Hub, G.degree v := by
    rw [← Finset.sum_union hdisjHub, huHub]
  -- Each `M`-isolated twin carries three hub incidences.
  have hsumHub3 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := by
    rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hmemIso] at hv
    exact each_iso_three_hubs G D Hub hmemD hmemHub h3 v hv.1 hv.2
  have hvsplit : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card + (G.neighborFinset v ∩ H6).card
      = (G.neighborFinset v ∩ Hub).card := by
    intro v _
    have hdisj : Disjoint (G.neighborFinset v ∩ Hub5) (G.neighborFinset v ∩ H6) :=
      Finset.disjoint_left.mpr (fun a ha ha' => by
        rw [Finset.mem_inter] at ha ha'
        rw [hmemHub5] at ha; rw [hmemH6] at ha'; omega)
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, huHub]
  have hsumsplit : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card
      + ∑ v ∈ Iso, (G.neighborFinset v ∩ H6).card = 3 * Iso.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hvsplit, hsumHub3]
  have hcrossH6 : ∑ v ∈ Iso, (G.neighborFinset v ∩ H6).card
      = ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card := cross_count_nineteen G Iso H6
  have hH6degbound : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ H6, G.degree h := by
    apply Finset.sum_le_sum
    intro h _
    calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h := G.card_neighborFinset_eq_degree h
  -- `Σ_{Iso}|N ∩ Hub₅| ≥ 13 − 4h₆ > 9 − h₆ = |Hub₅|` since `h₆ ≤ 1`.
  have hcount : Hub5.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card := by omega
  have hHub5deg : ∀ h ∈ Hub5, G.degree h ≤ 5 := fun h hh => ((hmemHub5 h).mp hh).2
  obtain ⟨h, t₁, t₂, _, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩ :=
    shared_hub_le5_from_count_nineteen G Iso Hub5 hIsoiso hHub5deg hcount
  exact ⟨h, t₁, t₂, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩

end N19

end ACMax
