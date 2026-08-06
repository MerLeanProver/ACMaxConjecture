import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.SignedCut
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N16.Dense
import ACMaxConjecture.SmallCases.N16.Align8Helpers
import ACMaxConjecture.SmallCases.N16.TwoHubSelect
import ACMaxConjecture.SmallCases.N16.TwoHubDeg5
import ACMaxConjecture.SmallCases.N16.TwoHubHub6Deg5
import ACMaxConjecture.SmallCases.N16.HubTriangle
import ACMaxConjecture.SmallCases.N16.HubTriangleCherry
import ACMaxConjecture.SmallCases.N16.Hub7P4

/-!
# Existence of a twin signed-cut certificate for `n = 16` (structural assembly)

This file assembles the `n = 16` twin signed-cut certificate from the proved boundary
certificates (`TwinCert16Cert`) and the structural-alignment dichotomies, mirroring the proved
`n = 15` `exists_twin_signed_cert_fifteen`.  It is specialised to `Fin 16`,
`edgeFinset.card = 28`, and the residual good-`C₄` threshold `≤ 14` (the bound the
`Fintype.card`-keyed `algConn_le_two_of_good_C4` delivers for `Fintype.card V = 16`).

In the sparse-hub residual (`δ ≥ 3`, no good triangle, no induced `2K₂` on degree-`3` vertices, no
good `C₄`, no good `K_{2,3}`, with an `M`-isolated degree-`3` vertex) one produces an explicit
signed cut `P, N` with `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`, fed to `algConn_le_two_of_signed`.

The assembly case-splits on `s := ∑_{v∈D}|N v ∩ D| = 2·e(M)` (`D` the degree-`3` set), which
`eM_le_five` bounds by `10` and `eM_even` shows even, so `s ∈ {0, 2, 4, 6, 8, 10}`.  Each branch
dispatches to one of the alignment dichotomies and then to the corresponding `_to_cut`
certificate.  Unlike `n = 15` (whose `e(M) = 2` and `e(M) ≥ 4` branches were three-way), every
non-trivial branch here is a **four-way** dichotomy
`SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig ∨ HubTriangleConfig`, because the `|Hub| = 8`
all-degree-`4` `P₄` corner new to `n = 16` is verified to require the hub-triangle configuration.
The four alignment dichotomies (`two_hub_config_sixteen`, `exists_align_four_config_sixteen`,
`exists_align_six_config_sixteen`, `halign8_sixteen`) are all proved (axiom-clean), so
`acmax_conjecture_sixteen` depends only on `propext`, `Classical.choice`, `Quot.sound`.

`n = 16` cardinality specifics: `|Hub| ∈ {5, 6, 7, 8}` (`|Hub| = 5 ⟹ e(M) = 5` forced;
`|Hub| = 8` is the all-degree-`4` regime new to `n = 16`) and `|D| ∈ {8, 9, 10, 11}`.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **Refined handshake for `n = 16`.**  The degree-`3` set `D` and the hub set `Hub = {4 ≤ deg}`
partition `Fin 16`, and the degree-sum identity `∑ deg = 56` with the cross-count
`cross_count` and minimum hub-degree `4` give `6·|D| ≤ 56 + s` where
`s = ∑_{v∈D}|N v ∩ D| = 2·e(M)`. -/
theorem handshake_sixteen (G : SimpleGraph (Fin 16)) (hm : G.edgeFinset.card = 28)
    (h3 : ∀ v : Fin 16, 3 ≤ G.degree v) :
    (Finset.univ.filter (fun w => G.degree w = 3)).card
        + (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card = 16
      ∧ 6 * (Finset.univ.filter (fun w => G.degree w = 3)).card
          ≤ 56 + ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
            (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 16) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 16, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hHubnotD : ∀ x : Fin 16, x ∈ Hub → x ∉ D := by
    intro x hx hxD; have := (hmemHub x).mp hx; have := (hmemD x).mp hxD; omega
  have hDH : ∀ v : Fin 16, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub :=
    Finset.disjoint_left.mpr (fun v hv hv' => hHubnotD v hv' hv)
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard16 : D.card + Hub.card = 16 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  refine ⟨hcard16, ?_⟩
  have hsum : ∑ v : Fin 16, G.degree v = 56 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 56 := by
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

/-- **Two-hub opposite-twin selection for `n = 16`, `e(M) ≤ 1` (open: structural selection).**
In the `e(M) ≤ 1` regime (`s ≤ 2`) there is no degree-`3` cherry through two hubs, so the two-hub
opposite-twin cut is always available.  Ported from `two_hub_config_fifteen`; the `n = 16` deltas
are the cardinalities: with `|V| = 16`, `e(G) = 28` the residual splits across `|Hub| ∈ {6, 7, 8}`,
`|Iso| ∈ {6, 7, 8}`.  The selection (`each_iso_three_hubs` + a hub-pair double count bounded by
`hK23`, splitting on `|Hub|`) yields two non-adjacent degree-`4` hubs each keeping `≥ 2` private
`M`-isolated twins.
DECOMPOSITION: port `two_hub_config_fifteen` (TwinCert15Align.lean:178) and its selection helpers
`each_iso_three_hubs`, `residual_hub_card_le_eight`, `two_isolated_twins`; replace the
`|Hub| ∈ {6, 7}` split with `|Hub| ∈ {6, 7, 8}`. -/
theorem two_hub_config_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 16, ({a, b, c, d, e} : Finset (Fin 16)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 16, G.degree t = 3 ∧ ∀ w : Fin 16, G.Adj t w → G.degree w ≠ 3)
    (hle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 2) :
    TwoHubConfig G := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 16) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 16, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hHubnotD : ∀ x : Fin 16, x ∈ Hub → x ∉ D := by
    intro x hx hxD; have := (hmemHub x).mp hx; have := (hmemD x).mp hxD; omega
  set Iso : Finset (Fin 16) := D.filter (fun x => (G.neighborFinset x ∩ D).card = 0) with hIsodef
  have hIsomem : ∀ x : Fin 16, x ∈ Iso ↔ x ∈ D ∧ (G.neighborFinset x ∩ D).card = 0 := by
    intro x; rw [hIsodef, Finset.mem_filter]
  have hisoD : ∀ x : Fin 16, x ∈ Iso → x ∈ D := fun x hx => ((hIsomem x).mp hx).1
  have hisoNoD : ∀ x y : Fin 16, x ∈ Iso → y ∈ D → ¬G.Adj x y := by
    intro x y hx hy hadj
    obtain ⟨_, hx0⟩ := (hIsomem x).mp hx
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hx0
    exact hx0 y (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hadj, hy⟩)
  have hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3) := by
    intro v hv
    refine ⟨(hmemD v).mp (hisoD v hv), fun w hadj hw3 => ?_⟩
    exact hisoNoD v w hv ((hmemD w).mpr hw3) hadj
  -- **Handshake bookkeeping.**
  have hDH : ∀ v : Fin 16, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub :=
    Finset.disjoint_left.mpr (fun v hv hv' => hHubnotD v hv' hv)
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard16 : D.card + Hub.card = 16 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  have hHubDc : ∀ w : Fin 16, w ∈ Hub ↔ w ∈ Dᶜ := by
    intro w; rw [Finset.mem_compl, hmemD, hmemHub]
    constructor
    · intro h he; omega
    · intro _; have := h3 w; omega
  have hsum : ∑ v : Fin 16, G.degree v = 56 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 56 := by
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
  set s : ℕ := ∑ v ∈ D, (G.neighborFinset v ∩ D).card with hsdef
  have hSsumD : s + ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
    rw [hsdef, ← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitD, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hSsumHub : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card
      + ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = ∑ w ∈ Hub, G.degree w := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitHub]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card := cross_count G D Hub
  have hIntEq : (∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card) + 6 * D.card = 56 + s := by
    have h1 := hsumpart; rw [hsumD] at h1; omega
  have hD8 : 8 ≤ D.card := by
    have h := (residual_hub_card_le_eight G hm h3).2; rwa [← hDdef] at h
  have heven : Even s := by rw [hsdef]; exact eM_even G D
  have hle2 : s ≤ 2 := by rw [hsdef, hDdef]; exact hle
  have hd89 : D.card = 8 ∨ D.card = 9 := by
    have hnn : 0 ≤ ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card := Nat.zero_le _
    omega
  -- **Hub-pair selection** (two non-adjacent degree-`4` hubs with `≥ 2` private isolated twins).
  have hpair : ∃ h₁ h₂ : Fin 16, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
    rcases hd89 with hd8 | hd9
    · -- **`|D| = 8 ⟹ |Hub| = 8`, all hubs degree `4` (regimes A and C).**
      have hHub8 : Hub.card = 8 := by omega
      have hsumHubdeg : ∑ w ∈ Hub, G.degree w = 32 := by rw [hsumD, hd8] at hsumpart; omega
      have hdeg4all : ∀ h ∈ Hub, G.degree h = 4 := by
        intro w hw
        have hge := (hmemHub w).mp hw
        have herase := Finset.add_sum_erase Hub (fun v => G.degree v) hw
        have hb : 4 * (Hub.erase w).card ≤ ∑ v ∈ Hub.erase w, G.degree v := by
          have hbb : ∀ x ∈ Hub.erase w, 4 ≤ G.degree x := fun i hi =>
            (hmemHub i).mp (Finset.mem_of_mem_erase hi)
          have h := Finset.card_nsmul_le_sum (Hub.erase w) (fun v => G.degree v) 4 hbb
          simpa [smul_eq_mul, mul_comm] using h
        have hec : (Hub.erase w).card = Hub.card - 1 := Finset.card_erase_of_mem hw
        omega
      have hdeg4Dc : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4 := fun w hw =>
        hdeg4all w ((hHubDc w).mpr hw)
      have hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
          (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 := by
        intro h₁ hh1 h₂ hh2 hne hnadj
        exact nonadj_hubs_share_le_one_iso G D Iso hC4 (fun x hx => hisoD x hx) hIsoprop
          hdeg4Dc h₁ h₂ ((hHubDc h₁).mp hh1) ((hHubDc h₂).mp hh2) hne hnadj
      have hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h := fun h hh => (hmemHub h).mp hh
      have hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5 := fun h hh => by
        have := hdeg4all h hh; omega
      have hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3 := fun t ht =>
        each_iso_three_hubs G D Hub hmemD hmemHub h3 t (hisoD t ht) ((hIsomem t).mp ht).2
      have hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b := fun a ha b hb =>
        hisoNoD a b ha (hisoD b hb)
      have hdisjHI : Disjoint Hub Iso := by
        rw [Finset.disjoint_left]; intro x hxH hxI
        exact (Finset.disjoint_left.mp hdisj) (hisoD x hxI) hxH
      have hintval : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 8 + s := by omega
      rcases (by obtain ⟨k, hk⟩ := heven; omega : s = 0 ∨ s = 2) with hs0 | hs2
      · -- **Regime A: `e(M) = 0`, `|Iso| = 8`.**
        have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by rw [← hsdef]; exact hs0
        have hIsoeqD : Iso = D := by
          ext v; rw [hIsomem]
          exact ⟨fun h => h.1, fun hvD => ⟨hvD, (Finset.sum_eq_zero_iff).mp hsum0 v hvD⟩⟩
        have hIso8 : Iso.card = 8 := by rw [hIsoeqD]; omega
        exact two_hub_corner_select_sixteen G Hub Iso hdeg hdeg5 hiso3 hisoIndep hshare hdisjHI
          (Or.inl ⟨hHub8, hIso8, hdeg4all, by omega⟩)
      · -- **Regime C: `e(M) = 1`, `|Iso| = 6`.**
        set S : Finset (Fin 16) := D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0)
          with hSdef
        have hScompl : Iso.card + S.card = D.card := by
          rw [hIsodef, hSdef]
          exact Finset.card_filter_add_card_filter_not (s := D)
            (p := fun v => (G.neighborFinset v ∩ D).card = 0)
        have hSle : 2 * S.card ≤ s + 2 := by
          rw [hSdef, hsdef]; exact nonisolated_component_bound G D hmemD h2k2
        have hexists : ∃ v ∈ D, (G.neighborFinset v ∩ D).card ≠ 0 := by
          by_contra hcon; push Not at hcon
          have hz : s = 0 := by rw [hsdef]; exact Finset.sum_eq_zero hcon
          omega
        obtain ⟨v0, hv0D, hv0ne⟩ := hexists
        have hv0S : v0 ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hv0D, hv0ne⟩
        obtain ⟨w0, hw0mem⟩ := Finset.card_ne_zero.mp hv0ne
        have hw0D : w0 ∈ D := (Finset.mem_inter.mp hw0mem).2
        have hadj0 : G.Adj v0 w0 := (G.mem_neighborFinset v0 w0).mp (Finset.mem_inter.mp hw0mem).1
        have hw0S : w0 ∈ S := by
          rw [hSdef, Finset.mem_filter]
          exact ⟨hw0D, Finset.card_ne_zero.mpr
            ⟨v0, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w0 v0).mpr hadj0.symm, hv0D⟩⟩⟩
        have hvw0ne : v0 ≠ w0 := G.ne_of_adj hadj0
        have hSge : 2 ≤ S.card := by
          have hsub : ({v0, w0} : Finset (Fin 16)) ⊆ S := by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with h | h
            · rw [h]; exact hv0S
            · rw [h]; exact hw0S
          calc 2 = ({v0, w0} : Finset (Fin 16)).card := by rw [Finset.card_pair hvw0ne]
            _ ≤ S.card := Finset.card_le_card hsub
        have hIso6 : Iso.card = 6 := by omega
        exact two_hub_corner_select_sixteen G Hub Iso hdeg hdeg5 hiso3 hisoIndep hshare hdisjHI
          (Or.inr (Or.inr ⟨hHub8, hIso6, hdeg4all, by omega⟩))
    · -- **`|D| = 9 ⟹ |Hub| = 7` (deg-`5` hub regime).**  Exactly one degree-`5` hub.  Split on
      -- `e(M)`: at `s = 2` (`|Iso| = 7`) the deg-`5`-aware selector handles it; at `s = 0`
      -- (`|Iso| = 9`, a genuinely new `n = 16` corner absent for `n = 15`) two degree-`4`
      -- hub-isolated hubs supply the cut directly.
      have hHub7 : Hub.card = 7 := by omega
      have hdsum : ∑ w ∈ Hub, G.degree w = 29 := by rw [hsumD, hd9] at hsumpart; omega
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
      have hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3 := fun t ht =>
        each_iso_three_hubs G D Hub hmemD hmemHub h3 t (hisoD t ht) ((hIsomem t).mp ht).2
      have hdisjHI : Disjoint Hub Iso := by
        rw [Finset.disjoint_left]; intro x hxH hxI
        exact (Finset.disjoint_left.mp hdisj) (hisoD x hxI) hxH
      -- **Degree-`4` share bound** (a non-adjacent degree-`4` pair shares `≤ 1` twin, else a good
      -- `C₄` of degree-sum `4 + 3 + 4 + 3 = 14`).
      have hshare4 : ∀ p ∈ Hub, G.degree p = 4 → ∀ q ∈ Hub, G.degree q = 4 → p ≠ q →
          ¬G.Adj p q → (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card ≤ 1 := by
        intro p hp hdp q hq hdq hpq hnpq
        by_contra hgt
        rw [not_le] at hgt
        obtain ⟨t₁, ht1, t₂, ht2, h12⟩ := Finset.one_lt_card.mp hgt
        have unpack : ∀ t : Fin 16, t ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso →
            G.Adj p t ∧ G.Adj q t ∧ t ∈ Iso := by
          intro t ht
          rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
          exact ⟨ht.1.1, ht.1.2, ht.2⟩
        obtain ⟨ha1, hb1, hI1⟩ := unpack t₁ ht1
        obtain ⟨ha2, hb2, hI2⟩ := unpack t₂ ht2
        have htw_nonadj : ¬G.Adj t₁ t₂ := hisoNoD t₁ t₂ hI1 (hisoD t₂ hI2)
        have hpne : ∀ t : Fin 16, t ∈ Iso → p ≠ t ∧ q ≠ t := by
          intro t ht
          have htD : t ∈ D := hisoD t ht
          exact ⟨fun e => hHubnotD p hp (by rw [e]; exact htD),
            fun e => hHubnotD q hq (by rw [e]; exact htD)⟩
        obtain ⟨hpt1, hqt1⟩ := hpne t₁ hI1
        obtain ⟨hpt2, hqt2⟩ := hpne t₂ hI2
        apply hC4
        refine ⟨p, t₁, q, t₂, ?_, ha1, hb1.symm, hb2, ha2.symm, hnpq, htw_nonadj, ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hpt1, hpq, hpt2]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hqt1, h12]),
            Finset.card_insert_of_notMem (by simp [hqt2]), Finset.card_singleton]
        · have e3 := (hIsoprop t₁ hI1).1
          have e4 := (hIsoprop t₂ hI2).1
          omega
      by_cases hs0 : s = 0
      · -- **`e(M) = 0` (`|Iso| = 9`): two degree-`4` hub-isolated hubs supply the cut.**
        have hsumzero : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by rw [← hsdef]; exact hs0
        have hsum0 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 :=
          (Finset.sum_eq_zero_iff).mp hsumzero
        have hDiso : ∀ v : Fin 16, v ∈ D → v ∈ Iso := fun v hv =>
          (hIsomem v).mpr ⟨hv, hsum0 v hv⟩
        have hHubInt : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 2 := by omega
        set Z : Finset (Fin 16) := Hub.filter (fun h => (G.neighborFinset h ∩ Hub).card = 0)
          with hZdef
        have hZcard : 5 ≤ Z.card := by
          set NZ : Finset (Fin 16) :=
            Hub.filter (fun h => ¬ (G.neighborFinset h ∩ Hub).card = 0) with hNZdef
          have hpart : Z.card + NZ.card = Hub.card :=
            Finset.card_filter_add_card_filter_not (s := Hub)
              (p := fun h => (G.neighborFinset h ∩ Hub).card = 0)
          have hNZge : NZ.card ≤ ∑ w ∈ NZ, (G.neighborFinset w ∩ Hub).card := by
            have h := Finset.card_nsmul_le_sum NZ (fun w => (G.neighborFinset w ∩ Hub).card) 1
              (fun w hw => by have := (Finset.mem_filter.mp hw).2; omega)
            simpa using h
          have hZsum0 : ∑ w ∈ Z, (G.neighborFinset w ∩ Hub).card = 0 :=
            Finset.sum_eq_zero (fun w hw => (Finset.mem_filter.mp hw).2)
          have hsplit : ∑ w ∈ Z, (G.neighborFinset w ∩ Hub).card
              + ∑ w ∈ NZ, (G.neighborFinset w ∩ Hub).card
              = ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card := by
            rw [hZdef, hNZdef, Finset.sum_filter_add_sum_filter_not]
          rw [hZsum0, hHubInt] at hsplit
          omega
        set D5 : Finset (Fin 16) := Hub.filter (fun h => G.degree h = 5) with hD5def
        have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
          intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
        have hD5card : D5.card = 1 := by
          have hsplit : ∀ h ∈ Hub, G.degree h = 4 + (if G.degree h = 5 then 1 else 0) := by
            intro h hh; rcases hdeg45 h hh with h4 | h5
            · rw [h4]; simp
            · rw [h5]; simp
          have hss : ∑ h ∈ Hub, G.degree h = 4 * Hub.card + D5.card := by
            rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
              smul_eq_mul, mul_comm, hD5def, Finset.sum_boole, Nat.cast_id]
          rw [hdsum, hHub7] at hss; omega
        have hZ4card : 2 ≤ (Z.filter (fun h => G.degree h = 4)).card := by
          have hpart2 : (Z.filter (fun h => G.degree h = 4)).card
              + (Z.filter (fun h => ¬ G.degree h = 4)).card = Z.card :=
            Finset.card_filter_add_card_filter_not (s := Z) (p := fun h => G.degree h = 4)
          have hZ5sub : Z.filter (fun h => ¬ G.degree h = 4) ⊆ D5 := by
            intro x hx
            rw [Finset.mem_filter] at hx
            obtain ⟨hxZ, hx4⟩ := hx
            have hxHub : x ∈ Hub := by rw [hZdef] at hxZ; exact (Finset.mem_filter.mp hxZ).1
            have := hdeg45 x hxHub
            rw [hD5def, Finset.mem_filter]; exact ⟨hxHub, by omega⟩
          have hle1 : (Z.filter (fun h => ¬ G.degree h = 4)).card ≤ 1 := by
            rw [← hD5card]; exact Finset.card_le_card hZ5sub
          omega
        obtain ⟨h₁, hh1Z4, h₂, hh2Z4, hne12⟩ :=
          Finset.one_lt_card.mp (by omega : 1 < (Z.filter (fun h => G.degree h = 4)).card)
        have hh1Z : h₁ ∈ Z := (Finset.mem_filter.mp hh1Z4).1
        have hd1 : G.degree h₁ = 4 := (Finset.mem_filter.mp hh1Z4).2
        have hh2Z : h₂ ∈ Z := (Finset.mem_filter.mp hh2Z4).1
        have hd2 : G.degree h₂ = 4 := (Finset.mem_filter.mp hh2Z4).2
        have hh1 : h₁ ∈ Hub := by rw [hZdef] at hh1Z; exact (Finset.mem_filter.mp hh1Z).1
        have hh2 : h₂ ∈ Hub := by rw [hZdef] at hh2Z; exact (Finset.mem_filter.mp hh2Z).1
        have hh1z : (G.neighborFinset h₁ ∩ Hub).card = 0 := by
          rw [hZdef] at hh1Z; exact (Finset.mem_filter.mp hh1Z).2
        have hh2z : (G.neighborFinset h₂ ∩ Hub).card = 0 := by
          rw [hZdef] at hh2Z; exact (Finset.mem_filter.mp hh2Z).2
        have hNiso : ∀ w : Fin 16, (G.neighborFinset w ∩ Hub).card = 0 →
            (G.neighborFinset w ∩ Iso).card = G.degree w := by
          intro w hwz
          have hsubD : G.neighborFinset w ⊆ D := by
            intro x hx
            rcases hDH x with hxD | hxH
            · exact hxD
            · exfalso
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hwz
              exact hwz x (Finset.mem_inter.mpr ⟨hx, hxH⟩)
          have hsubIso : G.neighborFinset w ⊆ Iso := fun x hx => hDiso x (hsubD hx)
          rw [Finset.inter_eq_left.mpr hsubIso, G.card_neighborFinset_eq_degree]
        have hI1 : (G.neighborFinset h₁ ∩ Iso).card = 4 := by rw [hNiso h₁ hh1z, hd1]
        have hI2 : (G.neighborFinset h₂ ∩ Iso).card = 4 := by rw [hNiso h₂ hh2z, hd2]
        have hnadj12 : ¬G.Adj h₁ h₂ := by
          intro hadj
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hh1z
          exact hh1z h₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr hadj, hh2⟩)
        have hsh12 := hshare4 h₁ hh1 hd1 h₂ hh2 hd2 hne12 hnadj12
        have hsh21 := hshare4 h₂ hh2 hd2 h₁ hh1 hd1 (Ne.symm hne12) (fun h => hnadj12 h.symm)
        refine ⟨h₁, h₂, hh1, hh2, hd1, hd2, hne12, hnadj12, ?_, ?_⟩
        · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
            (G.neighborFinset h₂)
          have hreord : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
              = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso :=
            Finset.inter_right_comm _ _ _
          rw [hreord] at hkey; omega
        · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso)
            (G.neighborFinset h₁)
          have hreord : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset h₁
              = G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso :=
            Finset.inter_right_comm _ _ _
          rw [hreord] at hkey; omega
      · -- **`e(M) = 1` (`s = 2`, `|Iso| = 7`): the deg-`5`-aware two-hub selector.**
        have hs2 : s = 2 := by obtain ⟨k, hk⟩ := heven; omega
        set S : Finset (Fin 16) := D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0)
          with hSdef
        have hScompl : Iso.card + S.card = D.card := by
          rw [hIsodef, hSdef]
          exact Finset.card_filter_add_card_filter_not (s := D)
            (p := fun v => (G.neighborFinset v ∩ D).card = 0)
        have hSle : 2 * S.card ≤ s + 2 := by
          rw [hSdef, hsdef]; exact nonisolated_component_bound G D hmemD h2k2
        have hexists : ∃ v ∈ D, (G.neighborFinset v ∩ D).card ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply hs0
          rw [hsdef]; exact Finset.sum_eq_zero hcon
        obtain ⟨v0, hv0D, hv0ne⟩ := hexists
        have hv0S : v0 ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hv0D, hv0ne⟩
        obtain ⟨w0, hw0mem⟩ := Finset.card_ne_zero.mp hv0ne
        have hw0D : w0 ∈ D := (Finset.mem_inter.mp hw0mem).2
        have hadj0 : G.Adj v0 w0 := (G.mem_neighborFinset v0 w0).mp (Finset.mem_inter.mp hw0mem).1
        have hw0S : w0 ∈ S := by
          rw [hSdef, Finset.mem_filter]
          exact ⟨hw0D, Finset.card_ne_zero.mpr
            ⟨v0, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w0 v0).mpr hadj0.symm, hv0D⟩⟩⟩
        have hvw0ne : v0 ≠ w0 := G.ne_of_adj hadj0
        have hSge : 2 ≤ S.card := by
          have hsub : ({v0, w0} : Finset (Fin 16)) ⊆ S := by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with h | h
            · rw [h]; exact hv0S
            · rw [h]; exact hw0S
          calc 2 = ({v0, w0} : Finset (Fin 16)).card := by rw [Finset.card_pair hvw0ne]
            _ ≤ S.card := Finset.card_le_card hsub
        have hIso7 : Iso.card = 7 := by omega
        exact two_hub_corner_select_deg5_sixteen G Hub Iso hdeg hdeg5 hiso3 hshare4 hdisjHI
          hHub7 hIso7 hdsum
  obtain ⟨h₁, h₂, hh1, hh2, hdeg1, hdeg2, hne12, hnadj12, hAcard, hBcard⟩ := hpair
  set A : Finset (Fin 16) := (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ with hAdef
  set B : Finset (Fin 16) := (G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁ with hBdef
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hAcard
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hBcard
  have hAprop : ∀ x : Fin 16, x ∈ A → G.Adj x h₁ ∧ x ∈ Iso ∧ ¬G.Adj x h₂ := by
    intro x hx
    rw [hAdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
    refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
    intro hadj; exact hx.2 ((G.mem_neighborFinset h₂ x).mpr hadj.symm)
  have hBprop : ∀ x : Fin 16, x ∈ B → G.Adj x h₂ ∧ x ∈ Iso ∧ ¬G.Adj x h₁ := by
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

/-- **Four-way alignment dichotomy for `n = 16`, `e(M) = 2` (main `TwoTwin` route landed).**
At `s = 4` the matching `M` is a single `P₃` cherry; the covering combination over the residual
graphs is `SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig ∨ HubTriangleConfig`.  Ported from
`exists_align_four_config_fifteen` (TwinCert15Align.lean:596).  At `e(M) = 2` the cardinalities are
`|D| ∈ {8, 9, 10}`, `|Hub| ∈ {6, 7, 8}`.
**LANDED (sorry-free, all of `e(M) = 2`):** the `|D| = 9` (`|Hub| = 7`) `TwoTwin` route (a
cherry-avoiding hub with `≥ 2` `D`-neighbours fed to the `TwoTwin` existential), the induced-`C₅`
impossibility branch, and the two corners GENUINELY NEW for `n = 16`: `|D| = 8 ⟹ |Hub| = 8`
all-degree-`4`, closed by the `P₃`-cherry **hub-triangle** residual
(`exists_hub_triangle_config_cherry_residual_sixteen`) after a `by_cases` cascade through the three
signed-cut configs; and `|D| = 10 ⟹ |Hub| = 6`, where the hubs are pairwise non-adjacent
(`∑_{Dᶜ}|N ∩ Dᶜ| = 0`), the cherry sends `5` edges into `Dᶜ` and the degree excess is `2`, so `≥ 2`
degree-`4` hubs avoid all but one cherry vertex — two such non-adjacent hubs with iso-degree `≥ 3`
and the `C₄` share bound give `TwoHubConfig`.  Note `hK23` is superfluous at `e(M) = 2`. -/
theorem exists_align_four_config_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 16, ({a, b, c, d, e} : Finset (Fin 16)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (_hiso : ∃ t : Fin 16, G.degree t = 3 ∧ ∀ w : Fin 16, G.Adj t w → G.degree w ≠ 3)
    (hs4 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 4) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hdegD : ∀ v : Fin 16, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hD8 : 8 ≤ D.card := by
    have h := (residual_hub_card_le_eight G hm h3).2; rwa [← hDdef] at h
  have hhand := (handshake_sixteen G hm h3).2
  rw [← hDdef, hs4] at hhand
  -- An `M`-edge exists, since `s = 4 > 0`.
  have hne : ∃ a b : Fin 16, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
  · -- **Dominating-edge branch.**
    by_cases h9 : D.card = 9
    · -- **`|D| = 9` (`|Hub| = 7`): TwoTwin via the cherry-avoiding hub.**
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
          have hsubset : D.filter (fun v => v = c₁ ∨ v = c₂) ⊆ ({c₁, c₂} : Finset (Fin 16)) := by
            intro v hv
            rw [Finset.mem_filter] at hv
            rcases hv.2 with rfl | rfl
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          calc (D.filter (fun v => v = c₁ ∨ v = c₂)).card
              ≤ ({c₁, c₂} : Finset (Fin 16)).card := Finset.card_le_card hsubset
            _ ≤ 2 := by
                have := Finset.card_insert_le c₁ ({c₂} : Finset (Fin 16))
                simp only [Finset.card_singleton] at this
                omega
        omega
      have mkcherry : ∀ c : Fin 16, c ∈ D → 2 ≤ (G.neighborFinset c ∩ D).card →
          ∃ x y z : Fin 16, x ∈ D ∧ y ∈ D ∧ z ∈ D ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
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
      -- **Cherry-avoiding hub with `≥ 2` `D`-neighbours.**  Rigid residual count.
      have hsum56 : ∑ v : Fin 16, G.degree v = 56 := by
        rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
      have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
        rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
      have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 56 := by
        rw [Finset.sum_add_sum_compl]; exact hsum56
      have hpartw : ∀ w : Fin 16,
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
      have hcc : D.card + Dᶜ.card = 16 := by
        have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
      have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 56 - 3 * D.card := by
        rw [hsumDdeg] at hsumsplit; omega
      have hDcD : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card = 3 * D.card - 4 := by
        rw [← hcross]; rw [hs4] at hAsdc; omega
      have hDcDc : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 60 - 6 * D.card := by
        have hsumeq : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ Dᶜ).card + (G.neighborFinset w ∩ D).card)
            = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hpartw w)
        rw [Finset.sum_add_distrib] at hsumeq
        omega
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
      have hxyzcard : ({x, y, z} : Finset (Fin 16)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
          Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hsubNI : ({x, y, z} : Finset (Fin 16))
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
      have hNIeq : ({x, y, z} : Finset (Fin 16))
          = D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
        Finset.eq_of_subset_of_card_le hsubNI (by rw [hxyzcard]; exact hNIcard3)
      have hDsplit : ∀ w : Fin 16, w ∈ D → w ∉ ({x, y, z} : Finset (Fin 16)) →
          (G.neighborFinset w ∩ D).card = 0 := by
        intro w hwD hwxyz
        by_contra hc
        have hmem : w ∈ D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
          Finset.mem_filter.mpr ⟨hwD, hc⟩
        rw [← hNIeq] at hmem
        exact hwxyz hmem
      have hNxD1 : 1 ≤ (G.neighborFinset x ∩ D).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hxyA, hyD⟩⟩
      have hNxDle : (G.neighborFinset x ∩ D).card ≤ 1 := by
        have hsub : G.neighborFinset x ∩ D ⊆ ({y} : Finset (Fin 16)) := by
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          obtain ⟨hxw, hwD⟩ := hw
          have hwNI : w ∈ ({x, y, z} : Finset (Fin 16)) := by
            rw [hNIeq, Finset.mem_filter]
            exact ⟨hwD, Finset.card_ne_zero.mpr ⟨x, Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxD⟩⟩⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwNI
          rcases hwNI with rfl | rfl | rfl
          · exact (G.irrefl hxw).elim
          · exact Finset.mem_singleton_self _
          · exact absurd hxw hxzN
        calc (G.neighborFinset x ∩ D).card ≤ ({y} : Finset (Fin 16)).card :=
              Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton _
      have hNxDcexact : (G.neighborFinset x ∩ Dᶜ).card = 2 := by
        have := hpartw x; rw [hdegx] at this; omega
      set Bad : Finset (Fin 16) :=
        Dᶜ.filter (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z) with hBaddef
      set A : Finset (Fin 16) :=
        Dᶜ.filter (fun w => ¬(G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)) with hAdef
      have hAsubDc : A ⊆ Dᶜ := by rw [hAdef]; exact Finset.filter_subset _ _
      have hNyD2 : 2 ≤ (G.neighborFinset y ∩ D).card := by
        have hsub : ({x, z} : Finset (Fin 16)) ⊆ G.neighborFinset y ∩ D := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hxyA.symm, hxD⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hyzA, hzD⟩
        calc 2 = ({x, z} : Finset (Fin 16)).card := (Finset.card_pair hxz_ne).symm
          _ ≤ _ := Finset.card_le_card hsub
      have hNyDc : (G.neighborFinset y ∩ Dᶜ).card ≤ 1 := by
        have := hpartw y; rw [hdegy] at this; omega
      have hNzD1 : 1 ≤ (G.neighborFinset z ∩ D).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset z y).mpr hyzA.symm, hyD⟩⟩
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
        rw [hAdef, hBaddef, add_comm]
        exact Finset.card_filter_add_card_filter_not (s := Dᶜ)
          (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)
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
        have hperh : ∀ h : Fin 16, (G.neighborFinset h ∩ Dᶜ).card
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
            + ∑ h ∈ A, (G.neighborFinset h ∩ Dᶜ).card = 60 - 6 * D.card := by
          rw [hBaddef, hAdef, Finset.sum_filter_add_sum_filter_not Dᶜ
            (fun w => G.Adj w x ∨ G.Adj w y ∨ G.Adj w z)
            (fun w => (G.neighborFinset w ∩ Dᶜ).card)]
          exact hDcDc
        set k := A.card with hk
        clear_value k
        have hklo : 1 ≤ k := by omega
        have hkhi : k ≤ 6 := by omega
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
      have hw1iso : ∀ w : Fin 16, G.Adj t1 w → G.degree w ≠ 3 := by
        intro w hadj hw3
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at ht1iso0
        exact ht1iso0 w (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset t1 w).mpr hadj, (hmemD w).mpr hw3⟩)
      have hw2iso : ∀ w : Fin 16, G.Adj t2 w → G.degree w ≠ 3 := by
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
    · -- **`|D| ∈ {8, 10}` corners (new for `n = 16`).**  Rebuild the cherry `x–y–z` (centre `y`),
      -- the `M`-isolated set `Iso`, and the centred covering data, then split on `|D|`.
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
          have hsubset : D.filter (fun v => v = c₁ ∨ v = c₂) ⊆ ({c₁, c₂} : Finset (Fin 16)) := by
            intro v hv
            rw [Finset.mem_filter] at hv
            rcases hv.2 with rfl | rfl
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          calc (D.filter (fun v => v = c₁ ∨ v = c₂)).card
              ≤ ({c₁, c₂} : Finset (Fin 16)).card := Finset.card_le_card hsubset
            _ ≤ 2 := by
                have := Finset.card_insert_le c₁ ({c₂} : Finset (Fin 16))
                simp only [Finset.card_singleton] at this
                omega
        omega
      have mkcherry : ∀ c : Fin 16, c ∈ D → 2 ≤ (G.neighborFinset c ∩ D).card →
          ∃ x y z : Fin 16, x ∈ D ∧ y ∈ D ∧ z ∈ D ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
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
      have hsum56 : ∑ v : Fin 16, G.degree v = 56 := by
        rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
      have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
        rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
      have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 56 := by
        rw [Finset.sum_add_sum_compl]; exact hsum56
      have hpartw : ∀ w : Fin 16,
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
      have hcc : D.card + Dᶜ.card = 16 := by
        have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
      have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 56 - 3 * D.card := by
        rw [hsumDdeg] at hsumsplit; omega
      have hDcDc : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 60 - 6 * D.card := by
        have hsumeq : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ Dᶜ).card + (G.neighborFinset w ∩ D).card)
            = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hpartw w)
        rw [Finset.sum_add_distrib] at hsumeq
        omega
      have hxyzcard : ({x, y, z} : Finset (Fin 16)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
          Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hsubNI : ({x, y, z} : Finset (Fin 16))
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
      have hNIeq : ({x, y, z} : Finset (Fin 16))
          = D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
        Finset.eq_of_subset_of_card_le hsubNI (by rw [hxyzcard]; exact hNIcard3)
      have hDsplit : ∀ w : Fin 16, w ∈ D → w ∉ ({x, y, z} : Finset (Fin 16)) →
          (G.neighborFinset w ∩ D).card = 0 := by
        intro w hwD hwxyz
        by_contra hc
        have hmem : w ∈ D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
          Finset.mem_filter.mpr ⟨hwD, hc⟩
        rw [← hNIeq] at hmem
        exact hwxyz hmem
      set Iso : Finset (Fin 16) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)
        with hIsodef
      have hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3) := by
        intro v hv
        rw [hIsodef, Finset.mem_filter] at hv
        obtain ⟨hvD, hv0⟩ := hv
        refine ⟨hdegD v hvD, fun w hadj hw3 => ?_⟩
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
        exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
      have hisoD : ∀ v : Fin 16, v ∈ Iso → v ∈ D := by
        intro v hv; rw [hIsodef, Finset.mem_filter] at hv; exact hv.1
      have hisoNoD : ∀ a b : Fin 16, a ∈ Iso → b ∈ D → ¬G.Adj a b := by
        intro a b ha hb hadj; exact (hIsoprop a ha).2 b hadj (hdegD b hb)
      have hisochar : ∀ w : Fin 16, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso := by
        intro w hwD hwx hwy hwz
        rw [hIsodef, Finset.mem_filter]
        exact ⟨hwD, hDsplit w hwD (by simp [hwx, hwy, hwz])⟩
      have hcov : ∀ p q : Fin 16, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y := by
        intro p q hpD hqD hpq
        have hpNI : p ∈ ({x, y, z} : Finset (Fin 16)) := by
          rw [hNIeq, Finset.mem_filter]
          exact ⟨hpD, Finset.card_ne_zero.mpr
            ⟨q, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p q).mpr hpq, hqD⟩⟩⟩
        have hqNI : q ∈ ({x, y, z} : Finset (Fin 16)) := by
          rw [hNIeq, Finset.mem_filter]
          exact ⟨hqD, Finset.card_ne_zero.mpr
            ⟨p, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset q p).mpr hpq.symm, hpD⟩⟩⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpNI hqNI
        rcases hpNI with rfl | rfl | rfl
        · rcases hqNI with rfl | rfl | rfl
          · exact (G.irrefl hpq).elim
          · exact Or.inr rfl
          · exact absurd hpq hxzN
        · exact Or.inl rfl
        · rcases hqNI with rfl | rfl | rfl
          · exact absurd hpq.symm hxzN
          · exact Or.inr rfl
          · exact (G.irrefl hpq).elim
      have hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 16)) := by
        apply Finset.Subset.antisymm
        · intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          obtain ⟨hyw, hwD⟩ := hw
          have hwNI : w ∈ ({x, y, z} : Finset (Fin 16)) := by
            rw [hNIeq, Finset.mem_filter]
            exact ⟨hwD, Finset.card_ne_zero.mpr
              ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hyw.symm, hyD⟩⟩⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwNI ⊢
          rcases hwNI with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact (G.irrefl hyw).elim
          · exact Or.inr rfl
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hxyA.symm, hxD⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hyzA, hzD⟩
      by_cases hD8eq : D.card = 8
      · -- **`|D| = 8` (`|Hub| = 8`, all degree `4`): hub-triangle residual.**
        have hdeg4all : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4 := by
          intro w hw
          have hspl := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
          have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
            have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
              fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
            have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
            simpa [smul_eq_mul, mul_comm] using this
          have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
          have hsum32 : ∑ v ∈ Dᶜ, G.degree v = 32 := by rw [hsumDcdeg, hD8eq]
          have hd4 := hDcdeg w hw
          rw [hsum32] at hspl
          omega
        by_cases hsv : SingleVertexConfig G
        · exact Or.inl hsv
        by_cases htt : TwoTwinConfig G
        · exact Or.inr (Or.inl htt)
        by_cases hth : TwoHubConfig G
        · exact Or.inr (Or.inr (Or.inl hth))
        · exact Or.inr (Or.inr (Or.inr
            (exists_hub_triangle_config_cherry_residual_sixteen G D Iso x y z hmemD hIsodef
              hIsoprop hisochar hcov hNyD hdegx hdegy hdegz hxyA hyzA hxzN hxz_ne hdeg4all
              hD8eq hsv htt hth)))
      · -- **`|D| = 10` (`|Hub| = 6`): two-hub via two degree-`4` cherry-light hubs.**  The hubs are
        -- pairwise non-adjacent (`∑_{Dᶜ}|N ∩ Dᶜ| = 0`).  The cherry sends only `5` edges into `Dᶜ`,
        -- so `≤ 2` hubs carry `≥ 2` cherry-neighbours; the degree excess `∑deg − 24 = 2` leaves
        -- `≤ 2` hubs of degree `> 4`.  Hence `≥ 2` degree-`4` hubs avoid all but one cherry vertex,
        -- giving iso-degree `≥ 3` and (with the `C₄` share bound) `≥ 2` private isolated twins each.
        have hD10 : D.card = 10 := by omega
        have hDc6 : Dᶜ.card = 6 := by omega
        have hindep : ∀ g : Fin 16, g ∈ Dᶜ → (G.neighborFinset g ∩ Dᶜ).card = 0 := by
          intro g hg
          have h0 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 0 := by
            have := hDcDc; rw [hD10] at this; omega
          exact (Finset.sum_eq_zero_iff.mp h0) g hg
        have hcherryD : ({x, y, z} : Finset (Fin 16)) ⊆ D := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact hxD
          · exact hyD
          · exact hzD
        have hIsoCHdisj : Disjoint Iso ({x, y, z} : Finset (Fin 16)) := by
          rw [Finset.disjoint_left]
          intro a haIso haCH
          obtain ⟨_, hano⟩ := hIsoprop a haIso
          simp only [Finset.mem_insert, Finset.mem_singleton] at haCH
          rcases haCH with rfl | rfl | rfl
          · exact hano y hxyA hdegy
          · exact hano x hxyA.symm hdegx
          · exact hano y hyzA.symm hdegy
        have hIsoCHunion : Iso ∪ ({x, y, z} : Finset (Fin 16)) = D := by
          apply Finset.Subset.antisymm
          · exact Finset.union_subset (fun v hv => hisoD v hv) hcherryD
          · intro w hwD
            by_cases hw : w ∈ ({x, y, z} : Finset (Fin 16))
            · exact Finset.mem_union_right _ hw
            · refine Finset.mem_union_left _ ?_
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
              exact hisochar w hwD hw.1 hw.2.1 hw.2.2
        have hDpart : ∀ g : Fin 16, (G.neighborFinset g ∩ Iso).card
            + (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 16))).card
            = (G.neighborFinset g ∩ D).card := by
          intro g
          rw [← hIsoCHunion, Finset.inter_union_distrib_left,
            Finset.card_union_of_disjoint
              (Finset.disjoint_left.mpr (fun a ha hb =>
                (Finset.disjoint_left.mp hIsoCHdisj)
                  (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2))]
        have hNxD : G.neighborFinset x ∩ D = ({y} : Finset (Fin 16)) := by
          apply Finset.Subset.antisymm
          · intro w hw
            rw [Finset.mem_inter, G.mem_neighborFinset] at hw
            obtain ⟨hxw, hwD⟩ := hw
            have hwNI : w ∈ ({x, y, z} : Finset (Fin 16)) := by
              rw [hNIeq, Finset.mem_filter]
              exact ⟨hwD, Finset.card_ne_zero.mpr
                ⟨x, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxD⟩⟩⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hwNI ⊢
            rcases hwNI with rfl | rfl | rfl
            · exact (G.irrefl hxw).elim
            · rfl
            · exact absurd hxw hxzN
          · intro w hw
            rw [Finset.mem_singleton] at hw; subst w
            exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hxyA, hyD⟩
        have hNzD : G.neighborFinset z ∩ D = ({y} : Finset (Fin 16)) := by
          apply Finset.Subset.antisymm
          · intro w hw
            rw [Finset.mem_inter, G.mem_neighborFinset] at hw
            obtain ⟨hzw, hwD⟩ := hw
            have hwNI : w ∈ ({x, y, z} : Finset (Fin 16)) := by
              rw [hNIeq, Finset.mem_filter]
              exact ⟨hwD, Finset.card_ne_zero.mpr
                ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w z).mpr hzw.symm, hzD⟩⟩⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hwNI ⊢
            rcases hwNI with rfl | rfl | rfl
            · exact absurd hzw.symm hxzN
            · rfl
            · exact (G.irrefl hzw).elim
          · intro w hw
            rw [Finset.mem_singleton] at hw; subst w
            exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z y).mpr hyzA.symm, hyD⟩
        have hNxDc : (G.neighborFinset x ∩ Dᶜ).card = 2 := by
          have h := hpartw x; rw [hNxD, Finset.card_singleton, hdegx] at h; omega
        have hNzDc : (G.neighborFinset z ∩ Dᶜ).card = 2 := by
          have h := hpartw z; rw [hNzD, Finset.card_singleton, hdegz] at h; omega
        have hNyDc : (G.neighborFinset y ∩ Dᶜ).card = 1 := by
          have h := hpartw y; rw [hNyD, Finset.card_pair hxz_ne, hdegy] at h; omega
        have hcrossCH := cross_count G Dᶜ ({x, y, z} : Finset (Fin 16))
        have hsum_cross :
            ∑ v ∈ Dᶜ, (G.neighborFinset v ∩ ({x, y, z} : Finset (Fin 16))).card = 5 := by
          have he : ∑ w ∈ ({x, y, z} : Finset (Fin 16)), (G.neighborFinset w ∩ Dᶜ).card
              = (G.neighborFinset x ∩ Dᶜ).card + (G.neighborFinset y ∩ Dᶜ).card
                + (G.neighborFinset z ∩ Dᶜ).card := by
            rw [Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
              Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton, add_assoc]
          rw [hcrossCH, he]; omega
        set CB : Finset (Fin 16) :=
          Dᶜ.filter (fun g => 2 ≤ (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 16))).card)
          with hCBdef
        have hCBle : CB.card ≤ 2 := by
          have hb : 2 * CB.card
              ≤ ∑ v ∈ Dᶜ, (G.neighborFinset v ∩ ({x, y, z} : Finset (Fin 16))).card := by
            calc 2 * CB.card = ∑ _g ∈ CB, 2 := by
                  rw [Finset.sum_const, smul_eq_mul, mul_comm]
              _ ≤ ∑ g ∈ CB, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 16))).card :=
                  Finset.sum_le_sum (fun g hg => (Finset.mem_filter.mp hg).2)
              _ ≤ ∑ v ∈ Dᶜ, (G.neighborFinset v ∩ ({x, y, z} : Finset (Fin 16))).card :=
                  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          omega
        set ND4 : Finset (Fin 16) := Dᶜ.filter (fun g => G.degree g ≠ 4) with hND4def
        have hND4sub : ND4 ⊆ Dᶜ := by rw [hND4def]; exact Finset.filter_subset _ _
        have hND4le : ND4.card ≤ 2 := by
          have hexcess : ∑ v ∈ Dᶜ, G.degree v = 26 := by rw [hsumDcdeg, hD10]
          have hge : 5 * ND4.card ≤ ∑ v ∈ ND4, G.degree v := by
            have hb : ∀ v ∈ ND4, 5 ≤ G.degree v := by
              intro v hv
              rw [hND4def, Finset.mem_filter] at hv
              have := hDcdeg v hv.1; omega
            have := Finset.card_nsmul_le_sum ND4 (fun v => G.degree v) 5 hb
            simpa [smul_eq_mul, mul_comm] using this
          have hge2 : 4 * (Dᶜ \ ND4).card ≤ ∑ v ∈ Dᶜ \ ND4, G.degree v := by
            have hb : ∀ v ∈ Dᶜ \ ND4, 4 ≤ G.degree v := by
              intro v hv; exact hDcdeg v (Finset.mem_sdiff.mp hv).1
            have := Finset.card_nsmul_le_sum (Dᶜ \ ND4) (fun v => G.degree v) 4 hb
            simpa [smul_eq_mul, mul_comm] using this
          have hsplitsum : ∑ v ∈ Dᶜ \ ND4, G.degree v + ∑ v ∈ ND4, G.degree v
              = ∑ v ∈ Dᶜ, G.degree v := Finset.sum_sdiff hND4sub
          have hcards : (Dᶜ \ ND4).card + ND4.card = Dᶜ.card :=
            Finset.card_sdiff_add_card_eq_card hND4sub
          omega
        have hGoodcard : 2 ≤ (Dᶜ \ (CB ∪ ND4)).card := by
          have hUsub : CB ∪ ND4 ⊆ Dᶜ := Finset.union_subset
            (by rw [hCBdef]; exact Finset.filter_subset _ _) hND4sub
          have hUle : (CB ∪ ND4).card ≤ 4 := le_trans (Finset.card_union_le _ _) (by omega)
          have hc := Finset.card_sdiff_add_card_eq_card hUsub
          omega
        have hgoodprop : ∀ g : Fin 16, g ∈ Dᶜ \ (CB ∪ ND4) →
            g ∈ Dᶜ ∧ G.degree g = 4 ∧ 3 ≤ (G.neighborFinset g ∩ Iso).card := by
          intro g hg
          rw [Finset.mem_sdiff, Finset.mem_union] at hg
          obtain ⟨hgDc, hgnU⟩ := hg
          have hgnCB : g ∉ CB := fun h => hgnU (Or.inl h)
          have hgnND4 : g ∉ ND4 := fun h => hgnU (Or.inr h)
          have hgdeg4 : G.degree g = 4 := by
            by_contra h; exact hgnND4 (by rw [hND4def, Finset.mem_filter]; exact ⟨hgDc, h⟩)
          have hgch1 : (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 16))).card ≤ 1 := by
            by_contra h
            exact hgnCB (by rw [hCBdef, Finset.mem_filter]; exact ⟨hgDc, by omega⟩)
          refine ⟨hgDc, hgdeg4, ?_⟩
          have hND : (G.neighborFinset g ∩ D).card = 4 := by
            have h := hpartw g; rw [hindep g hgDc] at h; omega
          have hpart := hDpart g
          omega
        obtain ⟨h₁, hh1, h₂, hh2, hne12⟩ :=
          Finset.one_lt_card.mp (by omega : 1 < (Dᶜ \ (CB ∪ ND4)).card)
        obtain ⟨hh1Dc, hd1, h1iso3⟩ := hgoodprop h₁ hh1
        obtain ⟨hh2Dc, hd2, h2iso3⟩ := hgoodprop h₂ hh2
        have hnadj12 : ¬G.Adj h₁ h₂ := by
          intro hadj
          have h0 := hindep h₁ hh1Dc
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
          exact h0 h₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr hadj, hh2Dc⟩)
        have hshare4 : ∀ p ∈ Dᶜ, G.degree p = 4 → ∀ q ∈ Dᶜ, G.degree q = 4 → p ≠ q →
            ¬G.Adj p q → (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card ≤ 1 := by
          intro p hp _hdp q hq _hdq _hpq hnpq
          by_contra hgt
          rw [not_le] at hgt
          obtain ⟨t₁, ht1, t₂, ht2, h12⟩ := Finset.one_lt_card.mp hgt
          have unpack : ∀ t : Fin 16, t ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso →
              G.Adj p t ∧ G.Adj q t ∧ t ∈ Iso := by
            intro t ht
            rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset,
              G.mem_neighborFinset] at ht
            exact ⟨ht.1.1, ht.1.2, ht.2⟩
          obtain ⟨ha1, hb1, hI1⟩ := unpack t₁ ht1
          obtain ⟨ha2, hb2, hI2⟩ := unpack t₂ ht2
          have htw_nonadj : ¬G.Adj t₁ t₂ := hisoNoD t₁ t₂ hI1 (hisoD t₂ hI2)
          have hpne : ∀ t : Fin 16, t ∈ Iso → p ≠ t ∧ q ≠ t := by
            intro t ht
            have htD : t ∈ D := hisoD t ht
            exact ⟨fun e => (Finset.mem_compl.mp hp) (by rw [e]; exact htD),
              fun e => (Finset.mem_compl.mp hq) (by rw [e]; exact htD)⟩
          obtain ⟨hpt1, hqt1⟩ := hpne t₁ hI1
          obtain ⟨hpt2, hqt2⟩ := hpne t₂ hI2
          apply hC4
          refine ⟨p, t₁, q, t₂, ?_, ha1, hb1.symm, hb2, ha2.symm, hnpq, htw_nonadj, ?_⟩
          · rw [Finset.card_insert_of_notMem (by simp [hpt1, _hpq, hpt2]),
              Finset.card_insert_of_notMem (by simp [Ne.symm hqt1, h12]),
              Finset.card_insert_of_notMem (by simp [hqt2]), Finset.card_singleton]
          · have e3 := (hIsoprop t₁ hI1).1
            have e4 := (hIsoprop t₂ hI2).1
            omega
        have hsh12 := hshare4 h₁ hh1Dc hd1 h₂ hh2Dc hd2 hne12 hnadj12
        have hsh21 := hshare4 h₂ hh2Dc hd2 h₁ hh1Dc hd1 (Ne.symm hne12) (fun h => hnadj12 h.symm)
        set A : Finset (Fin 16) := (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ with hAdef
        set B : Finset (Fin 16) := (G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁ with hBdef
        have hAcard : 2 ≤ A.card := by
          have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
            (G.neighborFinset h₂)
          have hreord : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
              = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso :=
            Finset.inter_right_comm _ _ _
          rw [hreord] at hkey; rw [hAdef]; omega
        have hBcard : 2 ≤ B.card := by
          have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso)
            (G.neighborFinset h₁)
          have hreord : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset h₁
              = G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso :=
            Finset.inter_right_comm _ _ _
          rw [hreord] at hkey; rw [hBdef]; omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hAcard
        obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hBcard
        have hAprop : ∀ u : Fin 16, u ∈ A → G.Adj u h₁ ∧ u ∈ Iso ∧ ¬G.Adj u h₂ := by
          intro u hu
          rw [hAdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hu
          refine ⟨hu.1.1.symm, hu.1.2, ?_⟩
          intro hadj; exact hu.2 ((G.mem_neighborFinset h₂ u).mpr hadj.symm)
        have hBprop : ∀ u : Fin 16, u ∈ B → G.Adj u h₂ ∧ u ∈ Iso ∧ ¬G.Adj u h₁ := by
          intro u hu
          rw [hBdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hu
          refine ⟨hu.1.1.symm, hu.1.2, ?_⟩
          intro hadj; exact hu.2 ((G.mem_neighborFinset h₁ u).mpr hadj.symm)
        obtain ⟨ha_h₁, ha_iso, ha_nh₂⟩ := hAprop a ha
        obtain ⟨hb_h₁, hb_iso, hb_nh₂⟩ := hAprop b hb
        obtain ⟨hc_h₂, hc_iso, hc_nh₁⟩ := hBprop c hc
        obtain ⟨hd_h₂, hd_iso, hd_nh₁⟩ := hBprop d hd
        have haD := hisoD a ha_iso
        have hbD := hisoD b hb_iso
        have hcD := hisoD c hc_iso
        have hdD := hisoD d hd_iso
        exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, a, b, c, d, hd1, hd2,
          (hmemD a).mp haD, (hmemD b).mp hbD, (hmemD c).mp hcD, (hmemD d).mp hdD,
          ha_h₁, hb_h₁, hc_h₂, hd_h₂,
          hnadj12,
          (fun h => hc_nh₁ h.symm), (fun h => hd_nh₁ h.symm),
          ha_nh₂, hisoNoD a c ha_iso hcD, hisoNoD a d ha_iso hdD,
          hb_nh₂, hisoNoD b c hb_iso hcD, hisoNoD b d hb_iso hdD,
          hne12,
          (fun e => (Finset.mem_compl.mp hh1Dc) (by rw [e]; exact haD)),
          (fun e => (Finset.mem_compl.mp hh1Dc) (by rw [e]; exact hbD)),
          (fun e => (Finset.mem_compl.mp hh1Dc) (by rw [e]; exact hcD)),
          (fun e => (Finset.mem_compl.mp hh1Dc) (by rw [e]; exact hdD)),
          (fun e => (Finset.mem_compl.mp hh2Dc) (by rw [e]; exact haD)),
          (fun e => (Finset.mem_compl.mp hh2Dc) (by rw [e]; exact hbD)),
          (fun e => (Finset.mem_compl.mp hh2Dc) (by rw [e]; exact hcD)),
          (fun e => (Finset.mem_compl.mp hh2Dc) (by rw [e]; exact hdD)),
          hab,
          (fun e => hc_nh₁ (e ▸ ha_h₁)), (fun e => hd_nh₁ (e ▸ ha_h₁)),
          (fun e => hc_nh₁ (e ▸ hb_h₁)), (fun e => hd_nh₁ (e ▸ hb_h₁)),
          hcd⟩))
  · -- **Induced-`C₅` branch is impossible at `e(M) = 2`.**
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_sixteen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 16, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 16)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

/-- **Four-way alignment dichotomy for `n = 16`, `e(M) = 3` (open: structural selection).**
At `s = 6` the matching `M` has three edges; the verified covering combination is
`SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig ∨ HubTriangleConfig`.  Ported from
`exists_align_six_config_fifteen` (TwinCert15Align.lean:1038), which is already four-way; the
`n = 16` deltas are the cardinalities `|D| ∈ {8, 9, 10}`, `|Hub| ∈ {6, 7, 8}` and the
`dominating_edge_or_induced_C5` keystone supplying either the dominating-edge twin pair or the
induced `C₅` feeding the hub-triangle branch.
DECOMPOSITION: port `exists_align_six_config_fifteen` with its `M`-double-star structure analysis
and the `dominating_edge_or_induced_C5` keystone; carry over the hub-triangle branch unchanged. -/
theorem exists_align_six_config_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 16, ({a, b, c, d, e} : Finset (Fin 16)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 16, G.degree t = 3 ∧ ∀ w : Fin 16, G.Adj t w → G.degree w ≠ 3)
    (hs6 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 6) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hdegD : ∀ v : Fin 16, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hindle : ∀ x : Fin 16, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  -- **Cardinalities.**  `|D| ∈ {8, 9, 10}`, `|Hub| ∈ {6, 7, 8}`.
  obtain ⟨hHub8, hD8le⟩ := residual_hub_card_le_eight G hm h3
  obtain ⟨hpart, hhand⟩ := handshake_sixteen G hm h3
  rw [← hDdef] at hD8le hpart hhand
  rw [hs6] at hhand
  -- A shared degree-`4` hub of two `M`-isolated twins (available at all `|D|` since `s = 6 ≤ 8`).
  have hs8le : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 8 := by omega
  have hshare : ∃ h t₁ t₂ : Fin 16, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 16, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 16, G.Adj t₂ w → G.degree w ≠ 3) := by
    by_cases hg5 : ∃ g : Fin 16, 5 ≤ G.degree g
    · obtain ⟨g, hg5'⟩ := hg5
      exact shared_deg4_hub_deg5_sixteen G hm h3 hT hC4 h2k2 hs8le g hg5'
    · push Not at hg5
      exact shared_deg4_hub_nodeg5_sixteen G hm h3 h2k2 (fun v => by have := hg5 v; omega) hs8le
  obtain ⟨k, t₁, t₂, hkdeg4, ht12, ht1deg, ht2deg, hAt1k, hAt2k, ht1iso, ht2iso⟩ := hshare
  -- An `M`-edge exists, since `s = 6 > 0`.
  have hne : ∃ a b : Fin 16, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
  · -- **Dominating-edge branch.**  A fat centre (in-`M`-degree `3`) lands `TwoTwinConfig` via
    -- `claw_shared_two_twin_sixteen`; the `P₄` case (both endpoints in-`M`-degree `2`) splits on
    -- `|D|`: `|D| = 8` (`|Hub| = 8`) is the all-degree-`4` hub-triangle corner; `|D| ∈ {9, 10}` is
    -- the degree-`5`/`6` corner closed separately.
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
    by_cases hc1three : 3 ≤ (G.neighborFinset c₁ ∩ D).card
    · exact Or.inr (Or.inl (claw_shared_two_twin_sixteen G D hmemD hT hC4 c₁ t₁ t₂ k hc1D
        hc1three ht1deg ht2deg hkdeg4 ht12 hAt1k hAt2k ht1iso ht2iso))
    · by_cases hc2three : 3 ≤ (G.neighborFinset c₂ ∩ D).card
      · exact Or.inr (Or.inl (claw_shared_two_twin_sixteen G D hmemD hT hC4 c₂ t₁ t₂ k hc2D
          hc2three ht1deg ht2deg hkdeg4 ht12 hAt1k hAt2k ht1iso ht2iso))
      · -- **`P₄` case.**  Both endpoints have in-`M`-degree `2`; the degree-`3` subgraph is the
        -- path `L₁–c₁–c₂–L₂`.
        set Iso : Finset (Fin 16) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)
          with hIsodef
        have hIsoprop : ∀ v ∈ Iso,
            G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3) := by
          intro v hv
          rw [hIsodef, Finset.mem_filter] at hv
          obtain ⟨hvD, hv0⟩ := hv
          refine ⟨hdegD v hvD, fun w hadj hw3 => ?_⟩
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
          exact hv0 w (Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
        have hsum56 : ∑ v : Fin 16, G.degree v = 56 := by
          rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
        have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
          rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul,
            mul_comm]
        have hcc : D.card + Dᶜ.card = 16 := by
          have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
        have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 56 := by
          rw [Finset.sum_add_sum_compl]; exact hsum56
        have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
          intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
        have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 56 - 3 * D.card := by
          rw [hsumDt] at hsumsplit; omega
        -- In-`M`-degrees of the endpoints are both `2` (path leaves `L₁`, `L₂`).
        have hform := thin_eM_formula_sixteen G D c₁ c₂ hc1D hc2D hc12 hcov
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
        have hisochar : ∀ w : Fin 16, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso := by
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
        by_cases hD8eq : D.card = 8
        · -- **`|D| = 8` (`|Hub| = 8`) corner.**  All eight hubs have degree `4`; the residual
          -- hub-triangle existence supplies `HubTriangleConfig` when the three signed-cut configs
          -- fail.
          have hdeg4all : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4 := by
            intro w hw
            have hspl := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
            have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
              have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
                fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
              have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
              simpa [smul_eq_mul, mul_comm] using this
            have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
            have hsum32 : ∑ v ∈ Dᶜ, G.degree v = 32 := by rw [hsumDcdeg, hD8eq]
            have hd4 := hDcdeg w hw
            rw [hsum32] at hspl
            omega
          by_cases hsv : SingleVertexConfig G
          · exact Or.inl hsv
          by_cases htt : TwoTwinConfig G
          · exact Or.inr (Or.inl htt)
          by_cases hth : TwoHubConfig G
          · exact Or.inr (Or.inr (Or.inl hth))
          · exact Or.inr (Or.inr (Or.inr (exists_hub_triangle_config_residual_sixteen G D Iso
              L₁ c₁ c₂ L₂ hT hC4 hK23 hmemD hIsodef hIsoprop hisochar hcov hNc1D hNc2D
              hc1deg hc2deg hL1deg hL2deg hac1L1 hc12 hac2L2 hnL1c2 hnc1L2
              hL1nc2 hL2nc1 hdeg4all hD8eq hsv htt hth)))
        · -- **`|D| ∈ {9, 10}` `P₄` corner (degree-`5`/degree-`6` regime, `|Hub| ∈ {6, 7}`).**  Both
          -- endpoints have in-`M`-degree `2`, so neither the fat-centre claw nor the
          -- double-star single-vertex selection applies; the cherry-avoiding-hub two-twin count
          -- (`|D| = 9`) and the `|Hub| = 6` selector (`|D| = 10`) close this separately.
          by_cases hD10 : D.card = 10
          · -- **`|D| = 10` (`|Hub| = 6`) corner.**  Six hubs, hub-internal sum `2`; a degree-`≤ 5`
            -- cherry-avoiding hub carries two `M`-isolated twins (`TwoTwinConfig`).  The degree-`6`
            -- hub (at most one, by `∑_{Dᶜ}deg = 26`) is routed around by restricting the avoider
            -- pigeonhole to degree-`≤ 5` hubs.
            have hdegsplit : ∀ v : Fin 16,
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
              have hcong : ∑ v ∈ D,
                  ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
                  = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hdegsplit v)
              rw [Finset.sum_add_distrib, hs6, hsumDt] at hcong
              omega
            have hSumHubInt : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 62 - 6 * D.card := by
              have hcong : ∑ w ∈ Dᶜ,
                  ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card)
                  = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hdegsplit w)
              rw [Finset.sum_add_distrib, ← hcross, hsumD_NHub, hsumDcdeg] at hcong
              omega
            have hDc6 : Dᶜ.card = 6 := by omega
            have hsum26 : ∑ w ∈ Dᶜ, G.degree w = 26 := by rw [hsumDcdeg, hD10]
            have hH6le : (Dᶜ.filter (fun w => 6 ≤ G.degree w)).card ≤ 1 := by
              by_contra hge2
              push Not at hge2
              obtain ⟨a, ham, b, hbm, hab⟩ :=
                Finset.one_lt_card.mp (by omega :
                  1 < (Dᶜ.filter (fun w => 6 ≤ G.degree w)).card)
              rw [Finset.mem_filter] at ham hbm
              have ha' := Finset.add_sum_erase Dᶜ (fun v => G.degree v) ham.1
              have hbin : b ∈ Dᶜ.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbm.1⟩
              have hb' := Finset.add_sum_erase (Dᶜ.erase a) (fun v => G.degree v) hbin
              have hrest : 4 * ((Dᶜ.erase a).erase b).card
                  ≤ ∑ v ∈ (Dᶜ.erase a).erase b, G.degree v := by
                have hbnd : ∀ i ∈ (Dᶜ.erase a).erase b, 4 ≤ G.degree i :=
                  fun i hi => hDcdeg i
                    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
                have := Finset.card_nsmul_le_sum ((Dᶜ.erase a).erase b)
                  (fun v => G.degree v) 4 hbnd
                simpa [smul_eq_mul, mul_comm] using this
              have hc1 : (Dᶜ.erase a).card = Dᶜ.card - 1 := Finset.card_erase_of_mem ham.1
              have hc2 : ((Dᶜ.erase a).erase b).card = (Dᶜ.erase a).card - 1 :=
                Finset.card_erase_of_mem hbin
              omega
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
            have hint3 : ∀ g : Fin 16, g ∈ Dᶜ →
                (G.neighborFinset g ∩ D ⊆ G.neighborFinset g ∩ Iso) →
                (G.neighborFinset g ∩ Iso).card ≤ 1 →
                3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
              intro g hg hsub htw
              have hc := le_trans (Finset.card_le_card hsub) htw
              have hds := hdegsplit g
              have hdg := hDcdeg g hg
              omega
            have hint2 : ∀ (g a : Fin 16), g ∈ Dᶜ →
                (G.neighborFinset g ∩ D ⊆ insert a (G.neighborFinset g ∩ Iso)) →
                (G.neighborFinset g ∩ Iso).card ≤ 1 →
                2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
              intro g a hg hsub htw
              have hc := Finset.card_le_card hsub
              have hc2 := Finset.card_insert_le a (G.neighborFinset g ∩ Iso)
              have hds := hdegsplit g
              have hdg := hDcdeg g hg
              omega
            have hwin : ∃ g : Fin 16, g ∈ Dᶜ ∧ G.degree g ≤ 5 ∧
                ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                  (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) ∧
                2 ≤ (G.neighborFinset g ∩ Iso).card := by
              by_contra hcon
              have htwle : ∀ g : Fin 16, g ∈ Dᶜ → G.degree g ≤ 5 →
                  ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                    (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
                  (G.neighborFinset g ∩ Iso).card ≤ 1 := by
                intro g hg hg5 hav
                by_contra hcard
                exact hcon ⟨g, hg, hg5, hav, by omega⟩
              have hsub1 : ∀ g : Fin 16, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ →
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
              have hsub1' : ∀ g : Fin 16, ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
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
              have hsub2 : ∀ g : Fin 16, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
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
              set P : Finset (Fin 16) := Dᶜ.filter
                (fun g => G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hPdef
              set Q : Finset (Fin 16) := Dᶜ.filter
                (fun g => G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hQdef
              set R : Finset (Fin 16) := P ∪ Q with hRdef
              have hpt : ∀ g ∈ Dᶜ,
                  (if (G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂)
                    then (1 : ℕ) else 0)
                    + (if (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)
                        then (1 : ℕ) else 0)
                    + (if ((G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                          (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂))
                        then (1 : ℕ) else 0)
                    ≤ (G.neighborFinset g ∩ Dᶜ).card := by
                intro g hg
                by_cases ha1 : (G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) <;>
                  by_cases ha2 : (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)
                · rw [if_pos ha1, if_pos ha2, if_pos (Or.inl ha1)]
                  obtain ⟨hg5, hgL1, hgc1, hgc2⟩ := ha1
                  obtain ⟨_, _, _, hgL2⟩ := ha2
                  have hi3 := hint3 g hg (hsub2 g hgL1 hgc1 hgc2 hgL2)
                    (htwle g hg hg5 (Or.inl ⟨hgL1, hgc1, hgc2⟩))
                  omega
                · rw [if_pos ha1, if_neg ha2, if_pos (Or.inl ha1)]
                  obtain ⟨hg5, hgL1, hgc1, hgc2⟩ := ha1
                  have hi2 := hint2 g L₂ hg (hsub1 g hgL1 hgc1 hgc2)
                    (htwle g hg hg5 (Or.inl ⟨hgL1, hgc1, hgc2⟩))
                  omega
                · rw [if_neg ha1, if_pos ha2, if_pos (Or.inr ha2)]
                  obtain ⟨hg5, hgc1, hgc2, hgL2⟩ := ha2
                  have hi2 := hint2 g L₁ hg (hsub1' g hgc1 hgc2 hgL2)
                    (htwle g hg hg5 (Or.inr ⟨hgc1, hgc2, hgL2⟩))
                  omega
                · rw [if_neg ha1, if_neg ha2, if_neg (not_or.mpr ⟨ha1, ha2⟩)]
                  omega
              have hP6 : P.card = ∑ g ∈ Dᶜ,
                  (if (G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂)
                    then (1 : ℕ) else 0) := by
                rw [hPdef, Finset.card_filter]
              have hQ6 : Q.card = ∑ g ∈ Dᶜ,
                  (if (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)
                    then (1 : ℕ) else 0) := by
                rw [hQdef, Finset.card_filter]
              have hR6 : R.card = ∑ g ∈ Dᶜ,
                  (if ((G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                        (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂))
                    then (1 : ℕ) else 0) := by
                rw [hRdef, ← Finset.filter_or, Finset.card_filter]
              have hPQR6 : P.card + Q.card + R.card ≤ 62 - 6 * D.card := by
                rw [hP6, hQ6, hR6, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                calc ∑ g ∈ Dᶜ, _ ≤ ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card :=
                      Finset.sum_le_sum hpt
                  _ = 62 - 6 * D.card := hSumHubInt
              have hPcard : 1 ≤ P.card := by
                have hsubP : Dᶜ \ P ⊆ (Dᶜ.filter (fun w => 6 ≤ G.degree w))
                    ∪ (G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₁ ∩ Dᶜ)
                    ∪ (G.neighborFinset c₂ ∩ Dᶜ) := by
                  intro g hg
                  obtain ⟨hgDc, hgnP⟩ := Finset.mem_sdiff.mp hg
                  rw [hPdef] at hgnP
                  have hnav : ¬(G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) :=
                    fun hpred => hgnP (Finset.mem_filter.mpr ⟨hgDc, hpred⟩)
                  by_cases hg6 : 6 ≤ G.degree g
                  · exact Finset.mem_union_left _ (Finset.mem_union_left _
                      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgDc, hg6⟩)))
                  · have hg5 : G.degree g ≤ 5 := by omega
                    have hor : G.Adj g L₁ ∨ G.Adj g c₁ ∨ G.Adj g c₂ := by
                      by_contra hc; push Not at hc; exact hnav ⟨hg5, hc.1, hc.2.1, hc.2.2⟩
                    rcases hor with h | h | h
                    · exact Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _
                          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)))
                    · exact Finset.mem_union_left _ (Finset.mem_union_right _
                        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
                    · exact Finset.mem_union_right _
                        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)
                have hubcard : (Dᶜ \ P).card ≤ 5 := by
                  refine le_trans (Finset.card_le_card hsubP) ?_
                  refine le_trans (Finset.card_union_le _ _) ?_
                  have h1 := Finset.card_union_le ((Dᶜ.filter (fun w => 6 ≤ G.degree w))
                    ∪ (G.neighborFinset L₁ ∩ Dᶜ)) (G.neighborFinset c₁ ∩ Dᶜ)
                  have h2 := Finset.card_union_le (Dᶜ.filter (fun w => 6 ≤ G.degree w))
                    (G.neighborFinset L₁ ∩ Dᶜ)
                  omega
                have hle := Finset.card_le_card_sdiff_add_card (s := Dᶜ) (t := P)
                omega
              have hQcard : 1 ≤ Q.card := by
                have hsubQ : Dᶜ \ Q ⊆ (Dᶜ.filter (fun w => 6 ≤ G.degree w))
                    ∪ (G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ)
                    ∪ (G.neighborFinset L₂ ∩ Dᶜ) := by
                  intro g hg
                  obtain ⟨hgDc, hgnQ⟩ := Finset.mem_sdiff.mp hg
                  rw [hQdef] at hgnQ
                  have hnav : ¬(G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) :=
                    fun hpred => hgnQ (Finset.mem_filter.mpr ⟨hgDc, hpred⟩)
                  by_cases hg6 : 6 ≤ G.degree g
                  · exact Finset.mem_union_left _ (Finset.mem_union_left _
                      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgDc, hg6⟩)))
                  · have hg5 : G.degree g ≤ 5 := by omega
                    have hor : G.Adj g c₁ ∨ G.Adj g c₂ ∨ G.Adj g L₂ := by
                      by_contra hc; push Not at hc; exact hnav ⟨hg5, hc.1, hc.2.1, hc.2.2⟩
                    rcases hor with h | h | h
                    · exact Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _
                          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)))
                    · exact Finset.mem_union_left _ (Finset.mem_union_right _
                        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
                    · exact Finset.mem_union_right _
                        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)
                have hubcard : (Dᶜ \ Q).card ≤ 5 := by
                  refine le_trans (Finset.card_le_card hsubQ) ?_
                  refine le_trans (Finset.card_union_le _ _) ?_
                  have h1 := Finset.card_union_le ((Dᶜ.filter (fun w => 6 ≤ G.degree w))
                    ∪ (G.neighborFinset c₁ ∩ Dᶜ)) (G.neighborFinset c₂ ∩ Dᶜ)
                  have h2 := Finset.card_union_le (Dᶜ.filter (fun w => 6 ≤ G.degree w))
                    (G.neighborFinset c₁ ∩ Dᶜ)
                  omega
                have hle := Finset.card_le_card_sdiff_add_card (s := Dᶜ) (t := Q)
                omega
              have hPleR : P.card ≤ R.card :=
                Finset.card_le_card (by rw [hRdef]; exact Finset.subset_union_left)
              omega
            obtain ⟨g, hgDc, hg5, havoid, hg2⟩ := hwin
            obtain ⟨s1, hs1m, s2, hs2m, hs12⟩ :=
              Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset g ∩ Iso).card)
            rw [Finset.mem_inter, G.mem_neighborFinset] at hs1m hs2m
            obtain ⟨hgs1, hs1Iso⟩ := hs1m
            obtain ⟨hgs2, hs2Iso⟩ := hs2m
            obtain ⟨hs1deg, hs1iso⟩ := hIsoprop s1 hs1Iso
            obtain ⟨hs2deg, hs2iso⟩ := hIsoprop s2 hs2Iso
            right; left
            rcases havoid with ⟨hgL1, hgc1, hgc2⟩ | ⟨hgc1, hgc2, hgL2⟩
            · exact ⟨s1, s2, g, L₁, c₁, c₂, hs1deg, hs2deg, hg5,
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
            · exact ⟨s1, s2, g, c₁, c₂, L₂, hs1deg, hs2deg, hg5,
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
          · -- **`|D| = 9` (`|Hub| = 7`) `P₄` corner (genuinely new for `n = 16`).**  With `|D| = 9`
            -- every hub has degree `≤ 5`, so the hub-internal `P/Q/R` count of the `|D| = 10` sibling
            -- sharpens to `|P|, |Q|, |R| ≥ 3` against `∑_{Dᶜ}|N ∩ Dᶜ| = 8`, a contradiction; this
            -- yields the cherry-avoiding degree-`≤ 5` hub with two `M`-isolated twins, which assembles
            -- into `TwoTwinConfig` via `shared_deg4_hub_avoids_p4_cherry_sixteen`.
            have hD9 : D.card = 9 := by omega
            exact Or.inr (Or.inl (shared_deg4_hub_avoids_p4_cherry_sixteen G hm h3 hT hC4
              L₁ c₁ c₂ L₂ Iso hIsoprop hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2
              hL1nc2 hL2nc1 hin1 hin2 hs6 hD9))
  · -- **Induced-`C₅` branch is impossible at `e(M) = 3`.**  Each cycle vertex has two `D`-neighbours,
    -- so contributes `≥ 2` to `s`; the five together force `s ≥ 10 > 6`.
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_sixteen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 16, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 16)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

/-- **Four-way alignment dichotomy for `n = 16`, `e(M) ≥ 4` (open: structural selection).**
At `s ≥ 8` the matching `M` is dense; the verified covering combination is
`SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig ∨ HubTriangleConfig`.  Ported from
`halign8_fifteen` (TwinCert15Align.lean:1536), upgraded to four-way to cover the `|Hub| = 8`
all-degree-`4` `P₄` corner.  Here `e(M) ∈ {4, 5}`, `|D| ∈ {9, 10, 11}`, `|Hub| ∈ {5, 6, 7}`
(`|Hub| = 5 ⟹ e(M) = 5` forced).
DECOMPOSITION: port `halign8_fifteen` with the dense-`M` `2K₂`-free structure theorem
(`ind_2K2`/general triangle-free-`2K₂`) selecting the single-vertex cut; add the hub-triangle
branch for the all-degree-`4` corner. -/
theorem halign8_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 16, ({a, b, c, d, e} : Finset (Fin 16)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 16, G.degree t = 3 ∧ ∀ w : Fin 16, G.Adj t w → G.degree w ≠ 3)
    (hge : 8 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 16, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
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
    have hne : ∃ a b : Fin 16, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
      · have hs8 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 8 := by
          have hle := eM_le_five G D hmemD hT hC4 h2k2
          rcases eM_even G D with ⟨m, hm'⟩
          omega
        have hshare : ∃ h t₁ t₂ : Fin 16, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
            G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
            (∀ w : Fin 16, G.Adj t₁ w → G.degree w ≠ 3) ∧
            (∀ w : Fin 16, G.Adj t₂ w → G.degree w ≠ 3) := by
          by_cases hg5 : ∃ g : Fin 16, 5 ≤ G.degree g
          · obtain ⟨g, hg5'⟩ := hg5
            exact shared_deg4_hub_deg5_sixteen G hm h3 hT hC4 h2k2 hs8 g hg5'
          · push Not at hg5
            exact shared_deg4_hub_nodeg5_sixteen G hm h3 h2k2
              (fun v => by have := hg5 v; omega) hs8
        obtain ⟨k, tw1, tw2, hkdeg4, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso,
          htw2iso⟩ := hshare
        exact Or.inr (Or.inl (dom_fat_centre_two_twin_sixteen G D hmemD hT hC4 c₁ c₂ hc1D hc2D
          hc12 hcov hge hindle k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso
          htw2iso))
    · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
        e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
      exact Or.inl (single_vertex_config_from_C5_three_hubs G hT hC4 t p q r
        ht3 htiso hp4' hq4' hr4' hpq hpr hqr htp htq htr v₁ v₂ v₃ v₄ v₅
        ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
        ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
        e12 e23 e34 e45 e51 n13 n14 n24 n25 n35)
  · -- **A neighbour of the `M`-isolated twin `t` has degree `≥ 5`.**  A degree-`5` hub exists.
    have hpge4 : 4 ≤ G.degree p := by have := htiso p htp; have := h3 p; omega
    have hqge4 : 4 ≤ G.degree q := by have := htiso q htq; have := h3 q; omega
    have hrge4 : 4 ≤ G.degree r := by have := htiso r htr; have := h3 r; omega
    have hg5 : ∃ g : Fin 16, 5 ≤ G.degree g := by
      by_contra hcon
      push Not at hcon
      exact hall ⟨by have := hcon p; omega, by have := hcon q; omega, by have := hcon r; omega⟩
    obtain ⟨g, hg5'⟩ := hg5
    by_cases hsum10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10
    · -- **`e(M) = 5` (`s = 10`) with a degree-`≥ 5` hub on the `M`-isolated twin.**  Here the
      -- `≤ 8` budget that `shared_deg4_hub_deg5_sixteen` needs fails, and the single-vertex
      -- double-star/`C₅` routes require all three twin-neighbours to be degree-`4` (the `hall`
      -- branch).  The deg-`≤ 5` shared-hub (double-star) / deg-`4` shared-hub (`C₅`) route of
      -- `two_twin_eM5_sixteen` closes the corner.
      exact Or.inr (Or.inl (two_twin_eM5_sixteen G hm h3 hT h2k2 hC4 g hg5' hsum10))
    · have hs8 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 8 := by
        have hle := eM_le_five G D hmemD hT hC4 h2k2
        rcases eM_even G D with ⟨m, hm'⟩
        omega
      obtain ⟨k, tw1, tw2, hkdeg4, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso,
        htw2iso⟩ := shared_deg4_hub_deg5_sixteen G hm h3 hT hC4 h2k2 hs8 g hg5'
      have hne : ∃ a b : Fin 16, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
        exact Or.inr (Or.inl (dom_fat_centre_two_twin_sixteen G D hmemD hT hC4 c₁ c₂ hc1D hc2D
          hc12 hcov hge hindle k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso
          htw2iso))
      · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
          e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
        exact Or.inr (Or.inl (c5_shared_two_twin_sixteen G hT hC4 k tw1 tw2 hkdeg4 htw12 htw1deg
          htw2deg hAtw1k hAtw2k htw1iso htw2iso v₁ v₂ v₃ v₄ v₅
          ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
          ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
          e12 e23 e34 e45 e51 n13 n14 n24 n25 n35))

/-- **Twin signed-cut existence for `n = 16` (structural assembly).**  In the sparse-hub residual
(`δ ≥ 3`, no good triangle, no induced `2K₂` on degree-3 vertices, no good `C₄` of degree-sum
`≤ 14`, no good `K_{2,3}`, with an `M`-isolated degree-3 vertex) there is a signed cut `P, N` with
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  Assembled by case-splitting on `s = 2·e(M)` and dispatching
each branch to its alignment dichotomy and `_to_cut` certificate (`TwinCert16Cert`). -/
theorem exists_twin_signed_cert_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 16, ({a, b, c, d, e} : Finset (Fin 16)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 16, G.degree t = 3 ∧ ∀ w : Fin 16, G.Adj t w → G.degree w ≠ 3) :
    ∃ P N : Finset (Fin 16), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set s : ℕ := ∑ v ∈ D, (G.neighborFinset v ∩ D).card with hsdef
  have heven : Even s := by rw [hsdef]; exact eM_even G D
  have hle10 : s ≤ 10 := by rw [hsdef]; exact eM_le_five G D hmemD hT hC4 h2k2
  rcases Nat.lt_or_ge s 4 with hlt4 | hge4
  · -- `e(M) ≤ 1` (`s < 4`, sharpened to `s ≤ 2` by evenness): two-hub opposite-twin cut.
    have hle2 : s ≤ 2 := by obtain ⟨k, hk⟩ := heven; omega
    exact twoHubConfig_to_cut G (two_hub_config_sixteen G hm h3 hT h2k2 hC4 hK23 hiso hle2)
  · -- `e(M) ≥ 2` (`s ≥ 4`): four-way alignment dichotomy, split by the value of `e(M)`.
    by_cases hle4 : s ≤ 4
    · -- `e(M) = 2` (`s = 4`).
      have hs4 : s = 4 := by omega
      have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨
          HubTriangleConfig G :=
        exists_align_four_config_sixteen G hm h3 hT h2k2 hC4 hK23 hiso hs4
      rcases halign with hsv | htt | hth | hht
      · exact singleVertexConfig_to_cut G hsv
      · exact twoTwinConfig_to_cut G htt
      · exact twoHubConfig_to_cut G hth
      · exact hubTriangleConfig_to_cut G hht
    · by_cases hle6 : s ≤ 6
      · -- `e(M) = 3` (`s = 6`).
        have hs6 : s = 6 := by obtain ⟨k, hk⟩ := heven; omega
        have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨
            HubTriangleConfig G :=
          exists_align_six_config_sixteen G hm h3 hT h2k2 hC4 hK23 hiso hs6
        rcases halign with hsv | htt | hth | hht
        · exact singleVertexConfig_to_cut G hsv
        · exact twoTwinConfig_to_cut G htt
        · exact twoHubConfig_to_cut G hth
        · exact hubTriangleConfig_to_cut G hht
      · -- `e(M) ≥ 4` (`s ≥ 8`).
        have hge8 : 8 ≤ s := by obtain ⟨k, hk⟩ := heven; omega
        have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨
            HubTriangleConfig G :=
          halign8_sixteen G hm h3 hT h2k2 hC4 hK23 hiso hge8
        rcases halign with hsv | htt | hth | hht
        · exact singleVertexConfig_to_cut G hsv
        · exact twoTwinConfig_to_cut G htt
        · exact twoHubConfig_to_cut G hth
        · exact hubTriangleConfig_to_cut G hht

end N16

end ACMax
