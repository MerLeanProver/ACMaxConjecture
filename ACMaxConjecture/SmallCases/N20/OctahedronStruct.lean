import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.ZVertex

/-!
# Octahedron structure layer (`n = 20`, `|Hub| = 12`, reusable)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (12, 6)` no-two-hub profile that has
been pinned to the rigid **octahedron** (six rich hubs `R` with internal matching mass, the high
`M`-isolated twins meeting three rich each, every twin meeting at most three rich), this file records
the structural leaf the poor/`Z` cert builds on — the **mechanical port** of the `n = 19`
`TwinCert19OctahedronStruct` to `|Hub| = 12`.

* `octahedron_struct_twenty` — the poor layer: exactly **six** poor hubs `Hub \ R` (vs five at
  `n = 19`, since `|Hub| 11 → 12`), each of iso-degree `1`; exactly four high twins (meeting three
  rich); exactly two low twins (carrying the **six** poor incidences).  A pure
  handshake/double-count argument.  **NOTE the only genuinely-new `|Hub| = 12` arithmetic:**
  `E(Hub \ R, Iso) = 6` (vs `5` at `n = 19`), so `E(R, Iso) = 18 − 6 = 12` (vs `13`); the
  high-twin count `4` and low-twin count `2` are unchanged because `|Iso| = 6` is unchanged.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Octahedron poor-layer structure (LEAF).**  From the rigid octahedron fields and the `(12, 6)`
profile: there are exactly six poor hubs `Hub \ R`, each of iso-degree `1`; exactly four high twins
meeting three rich hubs each; and exactly two low twins carrying at least one poor incidence.  The
argument is a double count: `E(Hub \ R, Iso) = 6` (each poor meets one twin) and
`E(Hub, Iso) = 18`, so `E(R, Iso) = 12`; with at least four twins meeting three rich each and every
twin meeting at most three rich, exactly four twins are high and the remaining two carry the six
poor incidences. -/
theorem octahedron_struct_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    (Hub \ R).card = 6 ∧
    (∀ g ∈ Hub \ R, (G.neighborFinset g ∩ Iso).card = 1) ∧
    (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card = 4 ∧
    (Iso.filter (fun t => 1 ≤ (G.neighborFinset t ∩ (Hub \ R)).card)).card = 2 := by
  classical
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- |Hub \ R| = 6.
  have hPcard : (Hub \ R).card = 6 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub, hHub, hRcard]
  -- Each poor hub meets exactly one twin.
  have hpoor1 : ∀ g ∈ Hub \ R, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hg
    rw [Finset.mem_sdiff] at hg
    obtain ⟨hgHub, hgnR⟩ := hg
    have hge1 : 1 ≤ (G.neighborFinset g ∩ Iso).card := hnozero g hgHub
    have hle1 : (G.neighborFinset g ∩ Iso).card ≤ 1 := by
      by_contra h
      exact hgnR (by rw [hReq, Finset.mem_filter]; exact ⟨hgHub, by omega⟩)
    omega
  -- Per-twin: rich + poor incidences sum to three.
  have hsplit : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card
      + (G.neighborFinset t ∩ (Hub \ R)).card = 3 := by
    intro t ht
    have h1 : (G.neighborFinset t ∩ Hub) ∩ R = G.neighborFinset t ∩ R := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hRsub]
    have h2 : (G.neighborFinset t ∩ Hub) \ R = G.neighborFinset t ∩ (Hub \ R) :=
      Finset.inter_sdiff_assoc _ _ _
    have h3 := Finset.card_inter_add_card_sdiff (G.neighborFinset t ∩ Hub) R
    rw [h1, h2, hiso3 t ht] at h3
    exact h3
  -- E(Hub \ R, Iso) = 6.
  have hSP : ∑ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ R)).card = 6 := by
    rw [cross_count_twenty G Iso (Hub \ R), Finset.sum_congr rfl (fun g hg => hpoor1 g hg),
      Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  -- E(Hub, Iso) = 18, hence E(R, Iso) = 12.
  have hsum18 : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
      + ∑ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ R)).card = 18 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t ht => hsplit t ht),
      Finset.sum_const, hIso, smul_eq_mul]
  have hSR : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card) = 12 := by omega
  -- Exactly four high twins.
  set A : Finset (Fin 20) := Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3) with hAdef
  have hAsumeq : ∑ t ∈ A, (G.neighborFinset t ∩ R).card = 3 * A.card := by
    rw [Finset.sum_congr rfl (fun t ht => (Finset.mem_filter.mp ht).2), Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hAle : ∑ t ∈ A, (G.neighborFinset t ∩ R).card
      ≤ ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hAcard : A.card = 4 := by
    rw [hAsumeq, hSR] at hAle
    omega
  -- Exactly two low twins.
  have hBeq : Iso.filter (fun t => 1 ≤ (G.neighborFinset t ∩ (Hub \ R)).card)
      = Iso.filter (fun t => ¬ ((G.neighborFinset t ∩ R).card = 3)) := by
    apply Finset.filter_congr
    intro t ht
    have hs := hsplit t ht
    have h3 := htle3 t ht
    omega
  have hcompl := Finset.card_filter_add_card_filter_not
    (s := Iso) (p := fun t => (G.neighborFinset t ∩ R).card = 3)
  rw [← hAdef] at hcompl
  have hBcard : (Iso.filter (fun t => 1 ≤ (G.neighborFinset t ∩ (Hub \ R)).card)).card = 2 := by
    rw [hBeq, hIso] at *
    omega
  exact ⟨hPcard, hpoor1, hAcard, hBcard⟩

end N20

end ACMax
