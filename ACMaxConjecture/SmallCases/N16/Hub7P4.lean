import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N16.Dense
import ACMaxConjecture.SmallCases.N16.Hub7P4Count

/-!
# `n = 16`, `|D| = 9`, `|Hub| = 7`, `e(M) = 3` (`s = 6`) `P₄` corner

The genuinely new `P₄` corner of the `e(M) = 3` dominating-edge branch
(`exists_align_six_config_sixteen`, TwinCert16.lean): the residual degree-`3` graph is the path
`L₁–c₁–c₂–L₂` whose dominating edge `c₁–c₂` has both endpoints of in-`M`-degree `2`, so neither the
fat-centre claw nor the double-star single-vertex selection applies.  Here `|D| = 9`, `|Hub| = 7`
(one degree-`5` hub `g` plus six degree-`4` hubs, `∑_{Hub} deg = 29`), `|Iso| = 9 − 4 = 5`.

The naive cherry-avoiding-hub pigeonhole (used at `|D| = 10`) is too loose: the hub-internal sum
`∑_{Dᶜ}|N ∩ Dᶜ| = 62 − 6·9 = 8` equals the avoider bound, so it cannot exclude all of `Dᶜ`.  The
fix ROUTES AROUND the single degree-`5` hub `g` by counting twin-incidences onto the SIX degree-`4`
hubs only: the `5` `M`-isolated twins each meet `3` hubs, so `∑_{Iso}|N ∩ Hub| = 15`; subtracting
`g`'s `≤ 5` leaves `≥ 10` incidences on the six degree-`4` hubs (`cross_count`), whence
`shared_deg4_hub_from_count_sixteen` yields a degree-`4` hub with `≥ 2` twins.  Among the two `P₄`
cherries `L₁–c₁–c₂` and `c₁–c₂–L₂`, a degree-`4` hub meets `≤ 1` vertex of each cherry-`P₃`
(`hub_meets_path_le_one_sixteen`); the refined incidence/hub-internal-edge accounting then forces a
degree-`4` hub that AVOIDS one full cherry while carrying two twins, which assembles into
`TwoTwinConfig` exactly as in the `|D| = 10` sibling.

The selector `shared_deg4_hub_avoids_p4_cherry_sixteen` carries the full, faithful
`TwoTwinConfig` assembly.  The cherry-avoiding-hub *existence* (`hwin`) is supplied by
`p4_hub4_cherry_avoider_sixteen` (TwinCert16Hub7P4Count.lean): with `|D| = 9` every hub has degree
`≤ 5`, so the `|D| = 10` hub-internal `P/Q/R` count sharpens to `|P|, |Q|, |R| ≥ 3` against the
hub-internal bound `∑_{Dᶜ}|N ∩ Dᶜ| = 8`, giving `9 ≤ 8`, a contradiction.  No `sorry` remains.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **`P₄` cherry-avoiding shared degree-`4` hub two-twin cut (`n = 16`, `|D| = 9`, `|Hub| = 7`).**
For the `e(M) = 3` dominating-edge `P₄` corner `L₁–c₁–c₂–L₂` with `|D| = 9` (one degree-`5` hub),
a degree-`≤ 5` hub that avoids one of the two `P₄` cherries and carries two `M`-isolated twins
assembles into `TwoTwinConfig`.  The existence of that cherry-avoiding hub (`hwin`) is supplied by
`p4_hub4_cherry_avoider_sixteen` via the hub-internal `P/Q/R` count; the assembly into
`TwoTwinConfig` is fully proved here. -/
theorem shared_deg4_hub_avoids_p4_cherry_sixteen (G : SimpleGraph (Fin 16))
    (_hm : G.edgeFinset.card = 28) (_h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 16) (Iso : Finset (Fin 16))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3)
    (_hisochar : ∀ w : Fin 16, w ∈ Finset.univ.filter (fun u : Fin 16 => G.degree u = 3) →
      w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (_hin1 : (G.neighborFinset c₁ ∩
      Finset.univ.filter (fun u : Fin 16 => G.degree u = 3)).card = 2)
    (_hin2 : (G.neighborFinset c₂ ∩
      Finset.univ.filter (fun u : Fin 16 => G.degree u = 3)).card = 2)
    (hs6 : ∑ v ∈ Finset.univ.filter (fun u : Fin 16 => G.degree u = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun u : Fin 16 => G.degree u = 3)).card = 6)
    (_hD9 : (Finset.univ.filter (fun u : Fin 16 => G.degree u = 3)).card = 9) :
    TwoTwinConfig G := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun u : Fin 16 => G.degree u = 3) with hDdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hL1D : L₁ ∈ D := (hmemD L₁).mpr hL1deg
  have hc1D : c₁ ∈ D := (hmemD c₁).mpr hc1deg
  have hc2D : c₂ ∈ D := (hmemD c₂).mpr hc2deg
  have hL2D : L₂ ∈ D := (hmemD L₂).mpr hL2deg
  -- **Cherry-avoiding degree-`≤ 5` hub with two `M`-isolated twins.**  Supplied by the
  -- hub-internal `P/Q/R` count `p4_hub4_cherry_avoider_sixteen`: with `|D| = 9` every hub has
  -- degree `≤ 5`, so the cherry-avoider counts satisfy `|P|, |Q|, |R| ≥ 3` against the
  -- hub-internal bound `∑_{Dᶜ}|N ∩ Dᶜ| = 8`, a contradiction (`9 ≤ 8`).
  have hwin : ∃ g : Fin 16, g ∈ Dᶜ ∧ G.degree g ≤ 5 ∧
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) ∧
      2 ≤ (G.neighborFinset g ∩ Iso).card :=
    p4_hub4_cherry_avoider_sixteen G _hm _h3 L₁ c₁ c₂ L₂ D Iso hmemD _hisochar
      hL1deg hL2deg hac1L1 hac2L2 hc1D hc2D _hin1 _hin2 hs6 _hD9
  obtain ⟨g, hgDc, hg5, havoid, hg2⟩ := hwin
  obtain ⟨s1, hs1m, s2, hs2m, hs12⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset g ∩ Iso).card)
  rw [Finset.mem_inter, G.mem_neighborFinset] at hs1m hs2m
  obtain ⟨hgs1, hs1Iso⟩ := hs1m
  obtain ⟨hgs2, hs2Iso⟩ := hs2m
  obtain ⟨hs1deg, hs1iso⟩ := hIsoprop s1 hs1Iso
  obtain ⟨hs2deg, hs2iso⟩ := hIsoprop s2 hs2Iso
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

end N16

end ACMax
