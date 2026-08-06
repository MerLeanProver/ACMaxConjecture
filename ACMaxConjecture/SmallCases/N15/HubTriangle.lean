import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N15.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N15.HubTriangleStruct
import ACMaxConjecture.SmallCases.N15.HubTriangleFF
import ACMaxConjecture.SmallCases.N15.HubTriangleTwoHub

/-!
# Hub-triangle existence for the `n = 15`, `e(M) = 3`, `|D| = 8` residual corner

This file isolates the single remaining structural obligation of the `n = 15` twin-based
signed-cut dichotomy: the **hub-triangle existence** in the `|D| = 8` (`|Hub| = 7`) corner of
`exists_align_six_config_fifteen` (`TwinCert15Align`), reached after the
`SingleVertex`/`TwoTwin`/`TwoHub` routes have all been excluded.

## The residual configuration (verified by direct construction: 60152 graphs, 0 uncovered)

* `D` = the degree-`3` vertices, `|D| = 8`; `Dᶜ` = the seven hubs, all of degree exactly `4`
  (`hdeg4`).
* `e(M) = 3`: the degree-`3` subgraph is the path `L₁–c₁–c₂–L₂` (`hac1L1`, `hc12`, `hac2L2`,
  with `c₁, c₂` having in-`M`-degree `2` — `hNc1D : N(c₁) ∩ D = {c₂, L₁}`,
  `hNc2D : N(c₂) ∩ D = {c₁, L₂}`), plus `|Iso| = 4` `M`-isolated degree-`3` twins (`Iso`).
* `e(Hub) = 5` hub-hub edges (`hSumHubInt : ∑_{w ∈ Dᶜ} |N(w) ∩ Dᶜ| = 58 - 6·|D| = 10`).
* `(W)` (derived in-proof from `htt : ¬TwoTwinConfig`): no hub avoiding a cherry (`{L₁,c₁,c₂}` or
  `{c₁,c₂,L₂}`) has `≥ 2` `M`-isolated-twin neighbours.
* `(A)` (derived in-proof from `hsv : ¬SingleVertexConfig`): no `M`-isolated twin `t` has two
  hub-neighbours `p ≠ q` both avoiding a common cherry.
* `hth : ¬TwoHubConfig` — the third negation, needed for the conditional to hold.

## The target and why it holds

`HubTriangleConfig G`: three pairwise-adjacent hubs `h₁, h₂, h₃` (a triangle in the `5`-edge
hub-hub graph) all non-adjacent to one cherry; their degree sum is `12 ≤ 13` automatically.

The following facts are rigorously established (and guide the remaining case analysis):

1. **Each cherry has `≥ 3` avoiding hubs.**  Cherry `{L₁,c₁,c₂}` receives only `2+1+1 = 4`
   hub-incidences (`L₁` has `2` hub-neighbours; `c₁, c₂` one each, by `hNc1D`/`hNc2D`), so `≥ 3`
   of the seven hubs avoid it; symmetrically for `{c₁,c₂,L₂}`.
2. **Every fully-free hub** (non-adjacent to all of `L₁,c₁,c₂,L₂`) **has hub-internal-degree
   `≥ 3`.**  It avoids cherry `{L₁,c₁,c₂}`, so `hwin` forces `≤ 1` `Iso`-neighbour; with `0`
   path-neighbours and degree `4`, at least `3` of its edges are hub-hub.
3. **At most `2` fully-free hubs.**  Three would force `≥ 4` edges among `3` vertices (impossible),
   since `∑ hub-internal-degree = 10`.
4. Each `free1`/`free2` hub has hub-internal-degree `≥ 2` (`hwin`: `≤ 1` `Iso`-neighbour; `≤ 1`
   neighbour among the single leaf `L₂`/`L₁`).

**TRIANGLE FORCING (now fully proved).**  When neither cherry has an avoider triangle, a
contradiction follows (`core_triangle_force_twohub`, via `hub_triangle_from_structure` in
`TwinCert15HubTriangleIsoRich`).  The argument is a case split on the number of *fully-free* hubs
(degree-`4` hubs avoiding all four path vertices), of which there are `1` or `2`: with one, the
`≥ 3` avoiders of each cherry overlap only in that hub, spanning `≥ 5` hubs of total hub-internal
degree `≥ 11 > 10`; with two, an edge count forces them adjacent and carrying every hub-edge, so an
avoider outside the pair is a common neighbour — a triangle.  No `decide` is used (the seven hubs
are abstract).
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **Hub-triangle existence in the `|D| = 8`, `e(M) = 3`, `P₄` residual corner.**  Under the
residual hypotheses (seven degree-`4` hubs, `5` hub-hub edges, `M = P₄` `L₁–c₁–c₂–L₂` with four
`M`-isolated twins, and the falsity of the `TwoTwin`-assembly condition `hwin` and the
`SingleVertex`-apex condition `hCaseA`), the graph contains three pairwise-adjacent hubs avoiding a
cherry, packaged as `HubTriangleConfig G`.  See the module docstring for the proof roadmap; the
triangle-forcing case analysis is discharged by `core_triangle_force_twohub`. -/
theorem exists_hub_triangle_config_residual (G : SimpleGraph (Fin 15))
    (D Iso : Finset (Fin 15)) (L₁ c₁ c₂ L₂ : Fin 15)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 15, ({a, b, c, d, e} : Finset (Fin 15)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 15, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 15, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hcov : ∀ p q : Fin 15, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁})
    (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3)
    (hL1deg : G.degree L₁ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hdeg4 : ∀ w : Fin 15, w ∈ Dᶜ → G.degree w = 4)
    (hSumHubInt : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 58 - 6 * D.card)
    (hD8 : D.card = 8)
    (hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  have hL1D : L₁ ∈ D := (hmemD L₁).mpr hL1deg
  have hc1D : c₁ ∈ D := (hmemD c₁).mpr hc1deg
  have hc2D : c₂ ∈ D := (hmemD c₂).mpr hc2deg
  have hL2D : L₂ ∈ D := (hmemD L₂).mpr hL2deg
  -- **(W) [from `¬TwoTwinConfig`].**  Any hub avoiding a cherry has `≤ 1` `M`-isolated-twin
  -- neighbour: two such twins plus the hub and the cherry assemble a `TwoTwinConfig`.
  have hW : ∀ g : Fin 15, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hgDc havoid
    by_contra hge2
    push Not at hge2
    obtain ⟨s1, hs1m, s2, hs2m, hs12⟩ := Finset.one_lt_card.mp hge2
    rw [Finset.mem_inter, G.mem_neighborFinset] at hs1m hs2m
    obtain ⟨hgs1, hs1Iso⟩ := hs1m
    obtain ⟨hgs2, hs2Iso⟩ := hs2m
    obtain ⟨hs1deg, hs1iso⟩ := hIsoprop s1 hs1Iso
    obtain ⟨hs2deg, hs2iso⟩ := hIsoprop s2 hs2Iso
    have hgdeg5 : G.degree g ≤ 5 := by have := hdeg4 g hgDc; omega
    apply htt
    rcases havoid with ⟨hgL1, hgc1, hgc2⟩ | ⟨hgc1, hgc2, hgL2⟩
    · exact ⟨s1, s2, g, L₁, c₁, c₂, hs1deg, hs2deg, hgdeg5,
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
    · exact ⟨s1, s2, g, c₁, c₂, L₂, hs1deg, hs2deg, hgdeg5,
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
  -- **(A) [from `¬SingleVertexConfig`].**  No `M`-isolated twin has two hub-neighbours both
  -- avoiding a common cherry: such a twin (apex) plus the two hubs and the cherry assemble a
  -- `SingleVertexConfig`.
  have hA : ∀ t : Fin 15, t ∈ Iso → ∀ p q : Fin 15, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q c₂) ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)) := by
    intro t htIso p q hpq htp htq havoid
    have htiso_prop : ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3 := (hIsoprop t htIso).2
    have htdeg : G.degree t = 3 := (hIsoprop t htIso).1
    have hpDc : p ∈ Dᶜ :=
      Finset.mem_compl.mpr (fun hpD => htiso_prop p htp ((hmemD p).mp hpD))
    have hqDc : q ∈ Dᶜ :=
      Finset.mem_compl.mpr (fun hqD => htiso_prop q htq ((hmemD q).mp hqD))
    have hdp : G.degree p = 4 := hdeg4 p hpDc
    have hdq : G.degree q = 4 := hdeg4 q hqDc
    apply hsv
    rcases havoid with ⟨hpL1, hpc1, hpc2, hqL1, hqc1, hqc2⟩ |
      ⟨hpc1, hpc2, hpL2, hqc1, hqc2, hqL2⟩
    · have hsum0 : ∑ w ∈ ({t, p, q} : Finset (Fin 15)),
          (G.neighborFinset w ∩ ({L₁, c₁, c₂} : Finset (Fin 15))).card = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_inter, G.mem_neighborFinset] at ha
        obtain ⟨hadj, hmem⟩ := ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw hmem
        rcases hw with rfl | rfl | rfl <;> rcases hmem with rfl | rfl | rfl
        · exact htiso_prop _ hadj hL1deg
        · exact htiso_prop _ hadj hc1deg
        · exact htiso_prop _ hadj hc2deg
        · exact hpL1 hadj
        · exact hpc1 hadj
        · exact hpc2 hadj
        · exact hqL1 hadj
        · exact hqc1 hadj
        · exact hqc2 hadj
      exact ⟨t, p, q, L₁, c₁, c₂, htdeg, hL1deg, hc1deg, hc2deg, htp, htq,
        hac1L1.symm, hc12, hnL1c2, (by rw [hsum0, hdp, hdq]; omega), hpq,
        (fun e => htiso_prop c₁ (by rw [e]; exact hac1L1.symm) hc1deg),
        (fun e => htiso_prop c₂ (by rw [e]; exact hc12) hc2deg),
        (fun e => htiso_prop c₁ (by rw [e]; exact hc12.symm) hc1deg),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        hac1L1.ne', hc12.ne, hL1nc2⟩
    · have hsum0 : ∑ w ∈ ({t, p, q} : Finset (Fin 15)),
          (G.neighborFinset w ∩ ({c₁, c₂, L₂} : Finset (Fin 15))).card = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_inter, G.mem_neighborFinset] at ha
        obtain ⟨hadj, hmem⟩ := ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw hmem
        rcases hw with rfl | rfl | rfl <;> rcases hmem with rfl | rfl | rfl
        · exact htiso_prop _ hadj hc1deg
        · exact htiso_prop _ hadj hc2deg
        · exact htiso_prop _ hadj hL2deg
        · exact hpc1 hadj
        · exact hpc2 hadj
        · exact hpL2 hadj
        · exact hqc1 hadj
        · exact hqc2 hadj
        · exact hqL2 hadj
      exact ⟨t, p, q, c₁, c₂, L₂, htdeg, hc1deg, hc2deg, hL2deg, htp, htq,
        hc12, hac2L2, hnc1L2, (by rw [hsum0, hdp, hdq]; omega), hpq,
        (fun e => htiso_prop c₂ (by rw [e]; exact hc12) hc2deg),
        (fun e => htiso_prop c₁ (by rw [e]; exact hc12.symm) hc1deg),
        (fun e => htiso_prop c₂ (by rw [e]; exact hac2L2.symm) hc2deg),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        hc12.ne, hac2L2.ne, hL2nc1.symm⟩
  -- Basic distinctness facts among the four path vertices.
  have hL1nc1 : L₁ ≠ c₁ := hac1L1.ne'
  have hc1nc2 : c₁ ≠ c₂ := hc12.ne
  have hc2nL2 : c₂ ≠ L₂ := hac2L2.ne
  have hL2nc2 : L₂ ≠ c₂ := hac2L2.ne'
  have hc1nL2 : c₁ ≠ L₂ := hL2nc1.symm
  have hL1nL2 : L₁ ≠ L₂ := fun e => hnc1L2 (e ▸ hac1L1)
  -- Hubs (`Dᶜ`) are disjoint from the path vertices (`D`).
  have hubne : ∀ g : Fin 15, g ∈ Dᶜ → g ≠ L₁ ∧ g ≠ c₁ ∧ g ≠ c₂ ∧ g ≠ L₂ := by
    intro g hg
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact (Finset.mem_compl.mp hg) hL1D
    · exact (Finset.mem_compl.mp hg) hc1D
    · exact (Finset.mem_compl.mp hg) hc2D
    · exact (Finset.mem_compl.mp hg) hL2D
  -- The seven hubs (`Dᶜ.card = 7`) and the four `M`-isolated twins (`Iso.card = 4`).
  obtain ⟨hDc7, hIso4⟩ := hub_struct G D Iso L₁ c₁ c₂ L₂ hIsodef hisochar hL1D hc1D hc2D hL2D
    hac1L1 hc12 hac2L2 hnc1L2 hL1nc2 hL2nc1 hD8
  -- Path hub-incidence counts: `c₁, c₂` one hub-neighbour each; `L₁, L₂` two each.
  obtain ⟨hcard_c1, hcard_c2, hcard_L1, hcard_L2⟩ :=
    path_hub_incidence G D L₁ c₁ c₂ L₂ hcov hNc1D hNc2D hL1D hc1D hL2D hc2D hac1L1 hac2L2
      hnL1c2 hnc1L2 hc1deg hc2deg hL1deg hL2deg hL1nc1 hL1nc2 hL2nc1 hL2nc2
  -- `hSumHubInt` specialises to `= 10` here.
  have hSum10 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 10 := by rw [hSumHubInt, hD8]
  -- **Branch 1: a triangle of cherry-`{L₁,c₁,c₂}` avoiders ⇒ `HubTriangleConfig` directly.**
  by_cases htri1 : ∃ a b c : Fin 15, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂)
  · obtain ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨haL1, hac1, hac2⟩, ⟨hbL1, hbc1, hbc2⟩, ⟨hcL1, hcc1, hcc2⟩⟩ := htri1
    obtain ⟨haneL1, hanec1, hanec2, _⟩ := hubne a haDc
    obtain ⟨hbneL1, hbnec1, hbnec2, _⟩ := hubne b hbDc
    obtain ⟨hcneL1, hcnec1, hcnec2, _⟩ := hubne c hcDc
    exact ⟨a, b, c, L₁, c₁, c₂, hL1deg, hc1deg, hc2deg, hab, hac, hbc,
      hac1L1.symm, hc12, haL1, hac1, hac2, hbL1, hbc1, hbc2, hcL1, hcc1, hcc2,
      (by have := hdeg4 a haDc; have := hdeg4 b hbDc; have := hdeg4 c hcDc; omega),
      haneL1, hanec1, hanec2, hbneL1, hbnec1, hbnec2, hcneL1, hcnec1, hcnec2,
      hL1nc1, hc1nc2, hL1nc2⟩
  -- **Branch 2: a triangle of cherry-`{c₁,c₂,L₂}` avoiders ⇒ `HubTriangleConfig` directly.**
  by_cases htri2 : ∃ a b c : Fin 15, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)
  · obtain ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩⟩ := htri2
    obtain ⟨_, hanec1, hanec2, haneL2⟩ := hubne a haDc
    obtain ⟨_, hbnec1, hbnec2, hbneL2⟩ := hubne b hbDc
    obtain ⟨_, hcnec1, hcnec2, hcneL2⟩ := hubne c hcDc
    exact ⟨a, b, c, c₁, c₂, L₂, hc1deg, hc2deg, hL2deg, hab, hac, hbc,
      hc12, hac2L2, hac1, hac2, haL2, hbc1, hbc2, hbL2, hcc1, hcc2, hcL2,
      (by have := hdeg4 a haDc; have := hdeg4 b hbDc; have := hdeg4 c hcDc; omega),
      hanec1, hanec2, haneL2, hbnec1, hbnec2, hbneL2, hcnec1, hcnec2, hcneL2,
      hc1nc2, hc2nL2, hc1nL2⟩
  -- **Branch 3: no avoider triangle for either cherry ⇒ contradiction via `TwoHubConfig`.**
  exfalso
  exact core_triangle_force_twohub G D Iso L₁ c₁ c₂ L₂ hT hC4 hK23 hmemD hIsodef hIsoprop
    hisochar hcov hNc1D hNc2D hc1deg hc2deg hL1deg hL2deg hac1L1 hc12 hac2L2 hnL1c2 hnc1L2
    hL1nc2 hL2nc1 hdeg4 hD8 hth hL1D hc1D hc2D hL2D hW hA hDc7 hIso4 hcard_c1 hcard_c2
    hcard_L1 hcard_L2 hSum10 htri1 htri2

end N15

end ACMax
