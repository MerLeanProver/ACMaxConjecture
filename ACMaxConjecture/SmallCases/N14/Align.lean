import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.SignedCut
import ACMaxConjecture.SmallCases.N14.Core

/-!
# Single-twin alignment helpers for `n = 14`

This file supplies the structural-selection helpers feeding `single_twin_cut_certificate`
(in `TwinCert14`).  The central reusable lemma `hub_meets_path_le_one_fourteen` bounds how
many vertices of an induced `P₃` a degree-`4` hub can meet (a triangle or good `C₄` otherwise),
ported from the `n = 13` development (`TwinCert13Core.hub_meets_path_le_one`).
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Hub meets an induced `P₃` in at most one vertex.**  A degree-`4` hub `h` cannot be adjacent
to two vertices of a degree-`3` induced path `x–y–z`: two adjacent hits give a good triangle
(degree-sum `≤ 10`, ruled out by `hT`); the distance-`2` hit `x, z` gives a good `C₄`
`h–x–y–z–h` (degree-sum `≤ 13`, ruled out by `hC4`). -/
theorem hub_meets_path_le_one_fourteen (G : SimpleGraph (Fin 14))
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    {h x y z : Fin 14} (hh : G.degree h = 4)
    (hx : G.degree x = 3) (hy : G.degree y = 3) (hz : G.degree z = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : ¬G.Adj x z)
    (hne_xy : x ≠ y) (hne_yz : y ≠ z) (hne_xz : x ≠ z) :
    ¬(G.Adj h x ∧ G.Adj h y) ∧ ¬(G.Adj h y ∧ G.Adj h z) ∧ ¬(G.Adj h x ∧ G.Adj h z) := by
  have hne_hx : h ≠ x := by intro e; subst e; omega
  have hne_hy : h ≠ y := by intro e; subst e; omega
  have hne_hz : h ≠ z := by intro e; subst e; omega
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hhx, hhy⟩
    exact hT ⟨h, x, y, hne_hx, hne_xy, hne_hy, hhx, hxy, hhy, by omega⟩
  · rintro ⟨hhy, hhz⟩
    exact hT ⟨h, y, z, hne_hy, hne_yz, hne_hz, hhy, hyz, hhz, by omega⟩
  · rintro ⟨hhx, hhz⟩
    by_cases hhy : G.Adj h y
    · exact hT ⟨h, x, y, hne_hx, hne_xy, hne_hy, hhx, hxy, hhy, by omega⟩
    · exact hC4 ⟨h, x, y, z,
        card_four_fourteen h x y z hne_hx hne_hy hne_hz hne_xy hne_xz hne_yz,
        hhx, hxy, hyz, hhz.symm, hhy, hxz, by omega⟩

/-- **Every `M`-isolated twin has two degree-`4` hubs.**  From `∑ degrees = 48`, minimum degree
`3` and `e(M) ≤ 5` (so `∑_{v∈D}|N v ∩ D| ≤ 10`), a double count gives `|D| ≤ 9`, hence the hub set
`Dᶜ` has `≥ 5` vertices with total degree-excess `6`; therefore at most one vertex has degree `≥ 5`.
An `M`-isolated degree-`3` twin `t` has its `3` neighbours all of degree `≥ 4`, so at least two of
them have degree exactly `4`. -/
theorem isolated_twin_two_deg4_hubs (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (t : Fin 14) (ht3 : G.degree t = 3)
    (htiso : ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3) :
    ∃ h₁ h₂ : Fin 14, h₁ ≠ h₂ ∧ G.Adj t h₁ ∧ G.Adj t h₂ ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hsum : ∑ v : Fin 14, G.degree v = 48 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have heM10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 10 :=
    eM_le_five G D hmemD hT hC4 h2k2
  -- `∑_{v ∈ D} deg v = 3·|D|`.
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  -- `∑_{v ∈ Dᶜ} deg v = 48 − 3·|D|`, packaged additively.
  have hsumDc : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 48 := by
    rw [Finset.sum_add_sum_compl]; exact hsum
  -- Double count `D → Dᶜ` edges.
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
  -- Cross count and bound.
  have hcross := cross_count_fourteen G D Dᶜ
  have hAle : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dᶜ, G.degree w := by
    apply Finset.sum_le_sum
    intro w _
    calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree w := G.card_neighborFinset_eq_degree w
  -- Hence `|D| ≤ 9`.
  have hDcard : D.card ≤ 9 := by
    rw [hcross] at hAs
    omega
  have hcc : D.card + Dᶜ.card = 14 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h
    exact h
  -- `|Dᶜ| ≥ 5`.
  have hDccard : 5 ≤ Dᶜ.card := by omega
  -- Additive degree-excess: `∑_{Dᶜ} deg = 3·|Dᶜ| + 6`.
  have hexcess : ∑ v ∈ Dᶜ, G.degree v = 3 * Dᶜ.card + 6 := by omega
  -- Every `Dᶜ` vertex has degree `≥ 4`.
  have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
    intro w hw
    rw [Finset.mem_compl, hmemD] at hw
    have := h3 w; omega
  -- No two neighbours of `t` both have degree `≥ 5`.
  have key : ∀ a b : Fin 14, a ≠ b → G.Adj t a → G.Adj t b →
      ¬(5 ≤ G.degree a ∧ 5 ≤ G.degree b) := by
    rintro a b hab hta htb ⟨ha5, hb5⟩
    have haDc : a ∈ Dᶜ := by rw [Finset.mem_compl, hmemD]; exact htiso a hta
    have hbDc : b ∈ Dᶜ := by rw [Finset.mem_compl, hmemD]; exact htiso b htb
    have hsplit1 : ∑ v ∈ Dᶜ, G.degree v
        = G.degree a + ∑ v ∈ Dᶜ.erase a, G.degree v :=
      (Finset.add_sum_erase _ (fun v => G.degree v) haDc).symm
    have hbera : b ∈ Dᶜ.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbDc⟩
    have hsplit2 : ∑ v ∈ Dᶜ.erase a, G.degree v
        = G.degree b + ∑ v ∈ (Dᶜ.erase a).erase b, G.degree v :=
      (Finset.add_sum_erase _ (fun v => G.degree v) hbera).symm
    have hrest : 4 * ((Dᶜ.erase a).erase b).card
        ≤ ∑ v ∈ (Dᶜ.erase a).erase b, G.degree v := by
      have hb : ∀ x ∈ (Dᶜ.erase a).erase b, 4 ≤ G.degree x := fun x hx =>
        hDcdeg x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      have h := Finset.card_nsmul_le_sum ((Dᶜ.erase a).erase b) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hc1 : (Dᶜ.erase a).card = Dᶜ.card - 1 := Finset.card_erase_of_mem haDc
    have hc2 : ((Dᶜ.erase a).erase b).card = (Dᶜ.erase a).card - 1 :=
      Finset.card_erase_of_mem hbera
    omega
  -- Extract `t`'s three neighbours.
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
  have hp4 : G.degree p = 4 ∨ 5 ≤ G.degree p := by
    have := h3 p; have := htiso p htp; omega
  have hq4 : G.degree q = 4 ∨ 5 ≤ G.degree q := by
    have := h3 q; have := htiso q htq; omega
  have hr4 : G.degree r = 4 ∨ 5 ≤ G.degree r := by
    have := h3 r; have := htiso r htr; omega
  rcases hp4 with hp | hp
  · rcases hq4 with hq | hq
    · exact ⟨p, q, hpq, htp, htq, hp, hq⟩
    · rcases hr4 with hr | hr
      · exact ⟨p, r, hpr, htp, htr, hp, hr⟩
      · exact absurd ⟨hq, hr⟩ (key q r hqr htq htr)
  · rcases hq4 with hq | hq
    · rcases hr4 with hr | hr
      · exact ⟨q, r, hqr, htq, htr, hq, hr⟩
      · exact absurd ⟨hp, hr⟩ (key p r hpr htp htr)
    · exact absurd ⟨hp, hq⟩ (key p q hpq htp htq)

end N14

end ACMax
