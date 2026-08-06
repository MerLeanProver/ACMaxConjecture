import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.RichZdeg

/-!
# Octahedron structure layer (`n = 18`, reusable)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` no-two-hub profile that has
been pinned to the rigid **octahedron** (six rich hubs `R` with internal matching mass `4` or `6`,
four high `M`-isolated twins meeting three rich each, every twin meeting at most three rich), this
file records the two structural leaves the poor/`Z` cert builds on.

* `octahedron_struct_eighteen` — the poor layer: exactly four poor hubs `Hub \ R`, each of iso-degree
  `1`; exactly four high twins (meeting three rich); exactly two low twins (carrying the four poor
  incidences).  A pure handshake/double-count argument.
* `octahedron_Z_rigid_eighteen` — the `Z` layer: exactly two `M`-edge endpoints, mutually adjacent,
  each meeting exactly two hubs and of degree `3`.  A thin wrapper over `z_two_hub_nbrs_eighteen`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Octahedron poor-layer structure (LEAF).**  From the rigid octahedron fields and the `(10, 6)`
profile: there are exactly four poor hubs `Hub \ R`, each of iso-degree `1`; exactly four high twins
meeting three rich hubs each; and exactly two low twins carrying at least one poor incidence.  The
argument is a double count: `E(Hub \ R, Iso) = 4` (each poor meets one twin) and
`E(Hub, Iso) = 18`, so `E(R, Iso) = 14`; with at least four twins meeting three rich each and every
twin meeting at most three rich, exactly four twins are high and the remaining two carry the four
poor incidences. -/
theorem octahedron_struct_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    (Hub \ R).card = 4 ∧
    (∀ g ∈ Hub \ R, (G.neighborFinset g ∩ Iso).card = 1) ∧
    (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card = 4 ∧
    (Iso.filter (fun t => 1 ≤ (G.neighborFinset t ∩ (Hub \ R)).card)).card = 2 := by
  classical
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- |Hub \ R| = 4.
  have hPcard : (Hub \ R).card = 4 := by
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
  -- E(Hub \ R, Iso) = 4.
  have hSP : ∑ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ R)).card = 4 := by
    rw [cross_count G Iso (Hub \ R), Finset.sum_congr rfl (fun g hg => hpoor1 g hg),
      Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  -- E(Hub, Iso) = 18, hence E(R, Iso) = 14.
  have hsum18 : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
      + ∑ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ R)).card = 18 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t ht => hsplit t ht),
      Finset.sum_const, hIso, smul_eq_mul]
  have hSR : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card) = 14 := by omega
  -- Exactly four high twins.
  set A : Finset (Fin 18) := Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3) with hAdef
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

/-- **Octahedron `Z`-layer rigidity (LEAF).**  From the `(10, 6, 40)` profile there are exactly two
`M`-edge endpoints `Z = univ \ (Hub ∪ Iso)`; each meets exactly two hubs and no twin (so has degree
`3`), and the two endpoints are mutually adjacent (the `M`-edge). -/
theorem octahedron_Z_rigid_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4) :
    (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)).card = 2 ∧
    (∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)),
      (G.neighborFinset z ∩ Hub).card = 2 ∧ (G.neighborFinset z ∩ Iso).card = 0 ∧
        G.degree z = 3) ∧
    (∀ z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)),
      ∀ z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)), z₁ ≠ z₂ → G.Adj z₁ z₂) := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZcard : Z.card = 2 := z_card_two_eighteen Hub Iso hdisj hHub hIso
  have hzfacts := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  refine ⟨hZcard, ?_, ?_⟩
  · intro z hz
    obtain ⟨h0, h2, h3⟩ := hzfacts z hz
    exact ⟨h2, h0, h3⟩
  · intro z₁ hz₁ z₂ hz₂ hne
    obtain ⟨h0, h2, h3⟩ := hzfacts z₁ hz₁
    have hsp := nbr_split_three_eighteen G Hub Iso hdisj z₁
    have hzZcard : (G.neighborFinset z₁ ∩ Z).card = 1 := by
      rw [← hZdef] at hsp
      omega
    have hsub : G.neighborFinset z₁ ∩ Z ⊆ Z.erase z₁ := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    have hEcard : (Z.erase z₁).card = 1 := by rw [Finset.card_erase_of_mem hz₁, hZcard]
    have heq : G.neighborFinset z₁ ∩ Z = Z.erase z₁ :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hEcard, hzZcard])
    have hz₂mem : z₂ ∈ G.neighborFinset z₁ ∩ Z := by
      rw [heq]; exact Finset.mem_erase.mpr ⟨hne.symm, hz₂⟩
    rw [Finset.mem_inter, G.mem_neighborFinset] at hz₂mem
    exact hz₂mem.1

end N18

end ACMax
