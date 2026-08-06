import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N16.HubTriangleStruct
import ACMaxConjecture.SmallCases.N16.HubTriangleActive
import ACMaxConjecture.SmallCases.N16.HubTriangleFF
import ACMaxConjecture.SmallCases.N16.HubTriangleIsoRich

/-!
# Hub-triangle existence for the `n = 15`, `e(M) = 3`, `|D| = 8` residual corner

This file isolates the hub-triangle existence obligation in the `|D| = 8` (`|Hub| = 8`,
all-degree-`4`) corner of `exists_align_six_config_sixteen` (`TwinCert16`), reached after the
`SingleVertex`/`TwoTwin`/`TwoHub` routes have all been excluded.  It is the `n = 16` port of
`TwinCert15HubTriangle*` (`n = 15`, `|Hub| = 7`).

## The residual configuration

* `D` = the degree-`3` vertices, `|D| = 8`; `Dᶜ` = the **eight** hubs, all of degree exactly `4`
  (`hdeg4`).
* `e(M) = 3`: the degree-`3` subgraph is the path `L₁–c₁–c₂–L₂` (`hac1L1`, `hc12`, `hac2L2`,
  with `c₁, c₂` having in-`M`-degree `2` — `hNc1D : N(c₁) ∩ D = {c₂, L₁}`,
  `hNc2D : N(c₂) ∩ D = {c₁, L₂}`), plus `|Iso| = 4` `M`-isolated degree-`3` twins (`Iso`).
* `e(Hub) = 7` hub-hub edges (`∑_{w ∈ Dᶜ} |N(w) ∩ Dᶜ| = 14`, derived in-proof from the per-hub
  split `path(g) + iso(g) + int(g) = 4` over the eight hubs: `4·8 − 6 − 12 = 14`).
* `(W)` (derived in-proof from `htt : ¬TwoTwinConfig`): no hub avoiding a cherry (`{L₁,c₁,c₂}` or
  `{c₁,c₂,L₂}`) has `≥ 2` `M`-isolated-twin neighbours.
* `(A)` (derived in-proof from `hsv : ¬SingleVertexConfig`): no `M`-isolated twin `t` has two
  hub-neighbours `p ≠ q` both avoiding a common cherry.
* `hth : ¬TwoHubConfig` — the third negation.

## The target

`HubTriangleConfig G`: three pairwise-adjacent hubs `h₁, h₂, h₃` (a triangle in the `7`-edge
hub-hub graph) all non-adjacent to one cherry; their degree sum is `12 ≤ 13` automatically.

## Status (`n = 16` delta from `n = 15`)

The two **direct** branches (an avoider triangle for either cherry yields `HubTriangleConfig`
immediately) and all the structural counting (`TwinCert16HubTriangleStruct`: eight hubs, `≥ 4`
avoiders per cherry, `∑ int = 14`) are fully proved here.  The single remaining obligation is the
**no-avoider-triangle ⇒ contradiction** core `core_triangle_force_sixteen`, which carries one
documented `sorry`: the `n = 15` fully-free case-split does not port because the looser budget
`∑ int = 14` (vs `10`) admits `|FF| ∈ {2,3,4}`.  See `core_triangle_force_sixteen` for the
replacement-argument roadmap (share-`≤ 1`, `hA`, `K₄ − e` among weak hubs).
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **No avoider triangle ⇒ contradiction (the `n = 16` combinatorial core).**  Under the residual
hypotheses for the `n = 16`, `|D| = 8`, `|Hub| = 8` corner, the assumption that neither cherry
admits a triangle of pairwise-adjacent avoiding hubs (`htri1`, `htri2`) is contradictory.

**OPEN (single documented `sorry`).**  This is the one genuinely new obligation for `n = 16`: the
`n = 15` proof (`hub_triangle_from_structure`, `TwinCert15HubTriangleIsoRich`) does **not** port.
The `n = 15` argument case-splits on the number of *fully-free* hubs (degree-`4` hubs avoiding all
four path vertices), which the budget `∑ int = 10` forces to be `1` or `2`, giving a clean
two-case forcing.  For `n = 16` the budget is `∑ int = 14` (eight hubs, `e(Hub) = 7`), under which
`|FF| ∈ {2, 3, 4}` and non-adjacent fully-free pairs and residual hub-edges all become possible —
every branch of the `n = 15` case-split fails to close.

The replacement argument (to be supplied) uses the structural facts already available:
* `cherry_avoiders_ge_four`: each cherry has `≥ 4` avoiders (vs `≥ 3` for `n = 15`);
* `avoider_internal_ge_two` / `fully_free_internal_ge_three`: avoider/`FF` internal degrees;
* the inclusion–exclusion `2|A1| + 2|A2| − |FF| ≤ 14` over `A1 ∪ A2` (forcing `|FF| ≥ 2`);
* `nonadj_hubs_share_le_one_iso` (the `n = 16` good-`C₄` `Σ ≤ 14` bound): two non-adjacent hubs
  share `≤ 1` `M`-isolated twin, constraining how the `12` iso-incidences distribute;
* `hA` (from `¬SingleVertexConfig`): each twin's three hub-neighbours contain `≤ 1` `A1`-hub and
  `≤ 1` `A2`-hub.
The target is a `K₄ − e` (hence a triangle) among the weak (avoider) hubs, contradicting `htri2`.
See the orchestrator decomposition note for the proposed sub-lemma split. -/
theorem core_triangle_force_sixteen (G : SimpleGraph (Fin 16))
    (D Iso : Finset (Fin 16)) (L₁ c₁ c₂ L₂ : Fin 16)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 16, ({a, b, c, d, e} : Finset (Fin 16)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 16, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hcov : ∀ p q : Fin 16, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3)
    (hL1deg : G.degree L₁ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hdeg4 : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4)
    (hD8 : D.card = 8) (hth : ¬TwoHubConfig G)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hW : ∀ g : Fin 16, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hA : ∀ t : Fin 16, t ∈ Iso → ∀ p q : Fin 16, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q c₂) ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)))
    (hDc8 : Dᶜ.card = 8) (hIso4 : Iso.card = 4)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hSum14 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 14)
    (htri1 : ¬∃ a b c : Fin 16, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂))
    (htri2 : ¬∃ a b c : Fin 16, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)) :
    False := by
  classical
  -- Distinctness among the four path vertices.
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hc1L2 : c₁ ≠ L₂ := hL2nc1.symm
  have hL1L2 : L₁ ≠ L₂ := by rintro rfl; exact hnc1L2 hac1L1
  -- Path / Iso partition of `D`, giving the classification of every `D`-vertex.
  obtain ⟨hDeq, _hdisj⟩ :=
    path_iso_partition G D Iso L₁ c₁ c₂ L₂ hIsodef hisochar hL1D hc1D hc2D hL2D hac1L1 hc12 hac2L2
  have hclassP : ∀ x : Fin 16, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    rw [← hDeq] at hx
    rcases Finset.mem_union.mp hx with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h; tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  -- The two cherry-avoider sets and the fully-free set `FF = A1 ∩ A2`.
  set A1 := Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hA1def
  set A2 := Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hA2def
  set FF := A1 ∩ A2 with hFFdef
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsubA1 : FF ⊆ A1 := by rw [hFFdef]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFFdef]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dᶜ := hFFsubA1.trans hA1sub
  -- Avoider internal degree `≥ 2`; fully-free internal degree `≥ 3`.
  have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgL1, hgc1, hgc2⟩ := hg
    refine avoider_internal_ge_two G D Iso g L₂ (hdeg4 g hgDc)
      (hW g hgDc (Or.inl ⟨hgL1, hgc1, hgc2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgc1, hgc2, hgL2⟩ := hg
    refine avoider_internal_ge_two G D Iso g L₁ (hdeg4 g hgDc)
      (hW g hgDc (Or.inr ⟨hgc1, hgc2, hgL2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨hgDc, hgL1, hgc1, hgc2⟩ := hgA1
    obtain ⟨_, _, _, hgL2⟩ := hgA2
    refine fully_free_internal_ge_three G D Iso g (hdeg4 g hgDc)
      (hW g hgDc (Or.inl ⟨hgL1, hgc1, hgc2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact h
  -- Each cherry has `≥ 4` avoiders.
  obtain ⟨hA1card, hA2card⟩ :=
    cherry_avoiders_ge_four G D L₁ c₁ c₂ L₂ hDc8 hcard_c1 hcard_c2 hcard_L1 hcard_L2
  rw [← hA1def] at hA1card
  rw [← hA2def] at hA2card
  -- Inclusion–exclusion budget: `|FF| ∈ {2, 3, 4}`.
  obtain ⟨hFFlb, hFFub⟩ :=
    active_hub_budget_sixteen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card)
      hA1sub hA2sub hFFdef hA1card hA2card hA1int hA2int hFFint hSum14
  -- Dispatch on `|FF|`.
  have hFFcases : FF.card = 4 ∨ FF.card = 2 ∨ FF.card = 3 := by omega
  rcases hFFcases with hFF4 | hFF23
  · -- **`|FF| = 4`:** a Mantel triangle among the four fully-free hubs (all in `A2`).
    obtain ⟨a, b, c, haFF, hbFF, hcFF, hab, hac, hbc⟩ :=
      ff_four_triangle G Dᶜ FF hFFsub hFF4 hFFint hSum14
    have getA2 : ∀ g : Fin 16, g ∈ FF →
        g ∈ Dᶜ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
      intro g hg
      have hgA2 := hFFsubA2 hg
      rw [hA2def, Finset.mem_filter] at hgA2
      exact hgA2
    obtain ⟨haDc, hac1, hac2, haL2⟩ := getA2 a haFF
    obtain ⟨hbDc, hbc1, hbc2, hbL2⟩ := getA2 b hbFF
    obtain ⟨hcDc, hcc1, hcc2, hcL2⟩ := getA2 c hcFF
    exact htri2 ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩⟩
  · -- **`|FF| ∈ {2, 3}`: discharged by the inactive-hub argument.**  `iso_rich_force_sixteen`
    -- (`TwinCert16HubTriangleIsoRich`) closes `|FF| = 2` via the share-`≤ 1` bound on two
    -- non-adjacent `iso = 3` inactive hubs; the `|FF| = 3` sub-case carries the single remaining
    -- documented `sorry` (see its docstring — the contradiction needs a `TwoHubConfig` extraction).
    exact iso_rich_force_sixteen G D Iso L₁ c₁ c₂ L₂ hT hC4 hK23 hmemD hIsodef hIsoprop
      hisochar hcov hNc1D hNc2D hc1deg hc2deg hL1deg hL2deg hac1L1 hc12 hac2L2 hnL1c2 hnc1L2
      hL1nc2 hL2nc1 hdeg4 hD8 hth hL1D hc1D hc2D hL2D hW hA hDc8 hIso4 hcard_c1 hcard_c2
      hcard_L1 hcard_L2 hSum14 htri1 htri2

/-- **Hub-triangle existence in the `n = 16`, `|D| = 8`, `e(M) = 3`, `P₄` residual corner.**  Under
the residual hypotheses (eight degree-`4` hubs, `7` hub-hub edges, `M = P₄` `L₁–c₁–c₂–L₂` with four
`M`-isolated twins, and the falsity of `SingleVertexConfig`/`TwoTwinConfig`/`TwoHubConfig`), the
graph contains three pairwise-adjacent hubs avoiding a cherry, packaged as `HubTriangleConfig G`.
The two direct branches are fully proved; the no-avoider-triangle case is discharged by
`core_triangle_force_sixteen` (carrying one documented `sorry`, see its docstring). -/
theorem exists_hub_triangle_config_residual_sixteen (G : SimpleGraph (Fin 16))
    (D Iso : Finset (Fin 16)) (L₁ c₁ c₂ L₂ : Fin 16)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 16, ({a, b, c, d, e} : Finset (Fin 16)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 16, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hcov : ∀ p q : Fin 16, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁})
    (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3)
    (hL1deg : G.degree L₁ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hdeg4 : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4)
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
  have hW : ∀ g : Fin 16, g ∈ Dᶜ →
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
  have hA : ∀ t : Fin 16, t ∈ Iso → ∀ p q : Fin 16, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q c₂) ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)) := by
    intro t htIso p q hpq htp htq havoid
    have htiso_prop : ∀ w : Fin 16, G.Adj t w → G.degree w ≠ 3 := (hIsoprop t htIso).2
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
    · have hsum0 : ∑ w ∈ ({t, p, q} : Finset (Fin 16)),
          (G.neighborFinset w ∩ ({L₁, c₁, c₂} : Finset (Fin 16))).card = 0 := by
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
    · have hsum0 : ∑ w ∈ ({t, p, q} : Finset (Fin 16)),
          (G.neighborFinset w ∩ ({c₁, c₂, L₂} : Finset (Fin 16))).card = 0 := by
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
  have hubne : ∀ g : Fin 16, g ∈ Dᶜ → g ≠ L₁ ∧ g ≠ c₁ ∧ g ≠ c₂ ∧ g ≠ L₂ := by
    intro g hg
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact (Finset.mem_compl.mp hg) hL1D
    · exact (Finset.mem_compl.mp hg) hc1D
    · exact (Finset.mem_compl.mp hg) hc2D
    · exact (Finset.mem_compl.mp hg) hL2D
  -- The eight hubs (`Dᶜ.card = 8`) and the four `M`-isolated twins (`Iso.card = 4`).
  obtain ⟨hDc8, hIso4⟩ := hub_struct G D Iso L₁ c₁ c₂ L₂ hIsodef hisochar hL1D hc1D hc2D hL2D
    hac1L1 hc12 hac2L2 hnc1L2 hL1nc2 hL2nc1 hD8
  -- Path hub-incidence counts: `c₁, c₂` one hub-neighbour each; `L₁, L₂` two each.
  obtain ⟨hcard_c1, hcard_c2, hcard_L1, hcard_L2⟩ :=
    path_hub_incidence G D L₁ c₁ c₂ L₂ hcov hNc1D hNc2D hL1D hc1D hL2D hc2D hac1L1 hac2L2
      hnL1c2 hnc1L2 hc1deg hc2deg hL1deg hL2deg hL1nc1 hL1nc2 hL2nc1 hL2nc2
  -- Hub-internal-degree total: `∑ int = 4·8 − 6 − 12 = 14` (the `n = 16` delta from `n = 15`'s
  -- `10`), derived from the per-hub split `path(g) + iso(g) + int(g) = 4`.
  obtain ⟨hsumP, hsumI, hper⟩ :=
    residual_incidence_sums G D Iso L₁ c₁ c₂ L₂ hIsodef hIsoprop hisochar hL1D hc1D hc2D hL2D
      hac1L1 hc12 hac2L2 hnc1L2 hdeg4 hcard_c1 hcard_c2 hcard_L1 hcard_L2 hIso4 hL1nc2 hL2nc1
  have hSum14 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 14 := by
    have htot : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 16))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ _g ∈ Dᶜ, 4 := Finset.sum_congr rfl hper
    rw [Finset.sum_const, smul_eq_mul, hDc8, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hsumP, hsumI] at htot
    omega
  -- **Branch 1: a triangle of cherry-`{L₁,c₁,c₂}` avoiders ⇒ `HubTriangleConfig` directly.**
  by_cases htri1 : ∃ a b c : Fin 16, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
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
  by_cases htri2 : ∃ a b c : Fin 16, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
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
  -- **Branch 3: no avoider triangle for either cherry ⇒ contradiction.**
  exfalso
  exact core_triangle_force_sixteen G D Iso L₁ c₁ c₂ L₂ hT hC4 hK23 hmemD hIsodef hIsoprop
    hisochar hcov hNc1D hNc2D hc1deg hc2deg hL1deg hL2deg hac1L1 hc12 hac2L2 hnL1c2 hnc1L2
    hL1nc2 hL2nc1 hdeg4 hD8 hth hL1D hc1D hc2D hL2D hW hA hDc8 hIso4 hcard_c1 hcard_c2
    hcard_L1 hcard_L2 hSum14 htri1 htri2

end N16

end ACMax
