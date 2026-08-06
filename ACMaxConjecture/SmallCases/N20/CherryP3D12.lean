import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.TwoHubHub6Deg5

/-!
# The `|D| = 12`, `s = 4` cherry-`P₃` boundary corner (`n = 20`)

The `n = 20` boundary (`6·12 = 72 ≤ 72 + 4`).  With the cherry `x–y–z`
(`e(M) = 2`, centre `y`), `|D| = 12` leaves `|Iso| = 9` `M`-isolated twins
carrying `27` hub incidences on `|Hub| = 8` hubs of total degree `36`, and the
cherry carries exactly `5` hub slots (`2 + 1 + 2`).  The incidence identity
`27 + 5 + 2e_{HH} = 36` forces `e_{HH} = 2` (unlike the `n = 19` analogue with
no hub–hub edges).  A degree-`≤ 5` cherry-avoiding hub with two `M`-isolated
twins yields `TwoTwinConfig` against the cherry directly; the complementary
"no such hub" world is **infeasible**: the five cherry slots leave `≥ 3`
slot-free hubs, while `∑ deg = 36` (each `≥ 4`) admits `≤ 2` hubs of degree
`≥ 6`, so some slot-free hub `L` has degree `≤ 5`.  The missing-good-hub
hypothesis then caps its twins at `1`, forcing `e(L) ≥ 3`; but with
`∑_Hub e = 4` its three hub-neighbours already push `∑_Hub e ≥ 6 > 4`.
-/

namespace ACMax

open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The `|D| = 12` cherry-`P₃` corner** (`s = 4`, `|Hub| = 8`): the
excess-`4` boundary closes into `TwoTwinConfig` (the complementary "no good
hub" world is vacuous by a hub-edge count). -/
theorem cherry_p3_config_D12_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (D Iso : Finset (Fin 20)) (x y z : Fin 20)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 20)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 12) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set C : Finset (Fin 20) := {x, y, z} with hCdef
  set Hub : Finset (Fin 20) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v := by
    intro v; rw [hHubdef]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum72 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplitDDc : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]; exact hsum72
  have hHubsum : ∑ v ∈ Hub, G.degree v = 36 := by
    rw [hHubeqDc]; rw [hsumD, hDcard] at hsplitDDc; omega
  have hHubcard : Hub.card = 8 := by
    rw [hHubeqDc, Finset.card_compl, Fintype.card_fin, hDcard]
  have hxD : x ∈ D := (hmemD x).mpr hdegx
  have hyD : y ∈ D := (hmemD y).mpr hdegy
  have hzD : z ∈ D := (hmemD z).mpr hdegz
  have hCsubD : C ⊆ D := by
    rw [hCdef]
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxD
    · exact hyD
    · exact hzD
  have hCcard : C.card = 3 := by
    rw [hCdef, Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
      Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
  set J : Finset (Fin 20) := D \ C with hJdef
  have hJcard : J.card = 9 := by
    rw [hJdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hCsubD, hDcard, hCcard]
  have hJne : ∀ v ∈ J, v ≠ x ∧ v ≠ y ∧ v ≠ z := by
    intro v hv
    rw [hJdef, Finset.mem_sdiff, hCdef] at hv
    have hvC := hv.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvC
    push Not at hvC
    exact hvC
  have hJD : ∀ v ∈ J, v ∈ D := by
    intro v hv
    rw [hJdef, Finset.mem_sdiff] at hv
    exact hv.1
  have hJIso : ∀ v ∈ J, v ∈ Iso := by
    intro v hv
    obtain ⟨hvx, hvy, hvz⟩ := hJne v hv
    exact hisochar v (hJD v hv) hvx hvy hvz
  have hJdeg : ∀ v ∈ J, G.degree v = 3 := fun v hv => (hIsoprop v (hJIso v hv)).1
  have hJiso : ∀ v ∈ J, ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3 :=
    fun v hv => (hIsoprop v (hJIso v hv)).2
  have hJ3 : ∀ v ∈ J, (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    have hsub : G.neighborFinset v ⊆ Hub := by
      intro w hw
      rw [G.mem_neighborFinset] at hw
      rw [hmemHub]
      have h1 := hJiso v hv w hw
      have h2 := h3 w
      omega
    rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, hJdeg v hv]
  have hJsum : ∑ v ∈ J, (G.neighborFinset v ∩ Hub).card = 27 := by
    rw [Finset.sum_congr rfl hJ3, Finset.sum_const, smul_eq_mul, hJcard]
  have hsplitND : ∀ v : Fin 20,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = G.degree v := by
    intro v
    have h1 : G.neighborFinset v ∩ Hub = G.neighborFinset v \ D := by
      rw [hHubeqDc]
      ext w
      simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
    rw [h1, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
  have hNxD : G.neighborFinset x ∩ D = {y} := by
    ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hadj, hwD⟩
      rcases hcov x w hxD hwD hadj with e | e
      · exact absurd e hxy_ne
      · exact e
    · rintro rfl
      exact ⟨hxyA, hyD⟩
  have hNzD : G.neighborFinset z ∩ D = {y} := by
    ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hadj, hwD⟩
      rcases hcov z w hzD hwD hadj with e | e
      · exact absurd e (Ne.symm hyz_ne)
      · exact e
    · rintro rfl
      exact ⟨hyzA.symm, hyD⟩
  have hNxHub : (G.neighborFinset x ∩ Hub).card = 2 := by
    have h1 := hsplitND x
    rw [hNxD, Finset.card_singleton, hdegx] at h1
    omega
  have hNzHub : (G.neighborFinset z ∩ Hub).card = 2 := by
    have h1 := hsplitND z
    rw [hNzD, Finset.card_singleton, hdegz] at h1
    omega
  have hxzcard : ({x, z} : Finset (Fin 20)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hxz_ne]), Finset.card_singleton]
  have hNyHub : (G.neighborFinset y ∩ Hub).card = 1 := by
    have h1 := hsplitND y
    rw [hNyD, hxzcard, hdegy] at h1
    omega
  have hCsum : ∑ w ∈ C, (G.neighborFinset w ∩ Hub).card = 5 := by
    rw [hCdef, Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
      Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton, hNxHub, hNyHub, hNzHub]
    omega
  have hisoTot : ∑ h ∈ Hub, (G.neighborFinset h ∩ J).card = 27 := by
    rw [cross_count_twenty G Hub J]
    exact hJsum
  have hslotTot : ∑ h ∈ Hub, (G.neighborFinset h ∩ C).card = 5 := by
    rw [cross_count_twenty G Hub C]
    exact hCsum
  have hJunion : J ∪ C = D := by
    rw [hJdef]
    exact Finset.sdiff_union_of_subset hCsubD
  have hJCdisj : Disjoint J C := by
    rw [hJdef]
    exact Finset.sdiff_disjoint
  have hDJC : ∀ s : Finset (Fin 20), (s ∩ D).card = (s ∩ J).card + (s ∩ C).card := by
    intro s
    rw [← hJunion, Finset.inter_union_distrib_left]
    exact Finset.card_union_of_disjoint
      (hJCdisj.mono Finset.inter_subset_right Finset.inter_subset_right)
  have hperhub : ∀ h ∈ Hub, G.degree h = (G.neighborFinset h ∩ J).card
      + (G.neighborFinset h ∩ C).card + (G.neighborFinset h ∩ Hub).card := by
    intro h _
    have h1 := hsplitND h
    have h2 := hDJC (G.neighborFinset h)
    omega
  have hsumkey : ∑ h ∈ Hub, G.degree h = ∑ h ∈ Hub, ((G.neighborFinset h ∩ J).card
      + (G.neighborFinset h ∩ C).card + (G.neighborFinset h ∩ Hub).card) :=
    Finset.sum_congr rfl hperhub
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hHubsum, hisoTot, hslotTot] at hsumkey
  have hsumHH : ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card = 4 := by omega
  by_cases hshared : ∃ k ∈ Hub, G.degree k ≤ 5 ∧ (G.neighborFinset k ∩ C).card = 0 ∧
      2 ≤ (G.neighborFinset k ∩ J).card
  · obtain ⟨k, hkHub, hk5, hkC0, hkJ2⟩ := hshared
    obtain ⟨tw₁, htw1m, tw₂, htw2m, htw12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset k ∩ J).card)
    obtain ⟨htw1N, htw1J⟩ := Finset.mem_inter.mp htw1m
    obtain ⟨htw2N, htw2J⟩ := Finset.mem_inter.mp htw2m
    have hAktw1 : G.Adj k tw₁ := (G.mem_neighborFinset _ _).mp htw1N
    have hAktw2 : G.Adj k tw₂ := (G.mem_neighborFinset _ _).mp htw2N
    obtain ⟨htw1x, htw1y, htw1z⟩ := hJne tw₁ htw1J
    obtain ⟨htw2x, htw2y, htw2z⟩ := hJne tw₂ htw2J
    have htw1deg : G.degree tw₁ = 3 := hJdeg tw₁ htw1J
    have htw2deg : G.degree tw₂ = 3 := hJdeg tw₂ htw2J
    have hn1x : ¬G.Adj tw₁ x := fun ha => hJiso tw₁ htw1J x ha hdegx
    have hn1y : ¬G.Adj tw₁ y := fun ha => hJiso tw₁ htw1J y ha hdegy
    have hn1z : ¬G.Adj tw₁ z := fun ha => hJiso tw₁ htw1J z ha hdegz
    have hn2x : ¬G.Adj tw₂ x := fun ha => hJiso tw₂ htw2J x ha hdegx
    have hn2y : ¬G.Adj tw₂ y := fun ha => hJiso tw₂ htw2J y ha hdegy
    have hn2z : ¬G.Adj tw₂ z := fun ha => hJiso tw₂ htw2J z ha hdegz
    have hkCempty : G.neighborFinset k ∩ C = ∅ := Finset.card_eq_zero.mp hkC0
    have hkC : ∀ w : Fin 20, w ∈ C → ¬G.Adj k w := by
      intro w hwC hadj
      have hmem : w ∈ G.neighborFinset k ∩ C :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hwC⟩
      rw [hkCempty] at hmem
      exact absurd hmem (Finset.notMem_empty w)
    have hxC : x ∈ C := by rw [hCdef]; exact Finset.mem_insert_self x {y, z}
    have hyC : y ∈ C := by
      rw [hCdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self y {z})
    have hzC : z ∈ C := by
      rw [hCdef]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
    have hk4 : 4 ≤ G.degree k := (hmemHub k).mp hkHub
    have hkx : k ≠ x := by rintro rfl; omega
    have hky : k ≠ y := by rintro rfl; omega
    have hkz : k ≠ z := by rintro rfl; omega
    exact Or.inr (Or.inl ⟨tw₁, tw₂, k, x, y, z, htw1deg, htw2deg, hk5, hdegx, hdegy, hdegz,
      hAktw1.symm, hAktw2.symm, hxyA, hyzA, hn1x, hn1y, hn1z, hn2x, hn2y, hn2z,
      hkC x hxC, hkC y hyC, hkC z hzC, htw12, htw1x, htw1y, htw1z, htw2x, htw2y, htw2z,
      hkx, hky, hkz, hxy_ne, hyz_ne, hxz_ne⟩)
  · exfalso
    push Not at hshared
    -- No good hub ⟹ every slot-free degree-`≤ 5` hub has `≤ 1` twin, hence `e ≥ 3`; the five
    -- cherry slots leave `≥ 3` slot-free hubs, while `∑ deg = 36` (each `≥ 4`) permits `≤ 2` hubs
    -- of degree `≥ 6`, so some slot-free hub `L` has degree `≤ 5` and `e(L) ≥ 3`, forcing
    -- `∑_Hub e ≥ e(L) + |N(L) ∩ Hub| ≥ 6 > 4`.
    set Hfree : Finset (Fin 20) :=
      Hub.filter (fun h => ¬1 ≤ (G.neighborFinset h ∩ C).card) with hHfreedef
    have hfreesub : Hfree ⊆ Hub := Finset.filter_subset _ _
    have hfree0 : ∀ h ∈ Hfree, (G.neighborFinset h ∩ C).card = 0 := by
      intro h hh
      rw [hHfreedef, Finset.mem_filter] at hh
      omega
    have hfreecard : 3 ≤ Hfree.card := by
      have hle : (Hub \ Hfree).card
          ≤ ∑ h ∈ Hub \ Hfree, (G.neighborFinset h ∩ C).card := by
        calc (Hub \ Hfree).card = ∑ _h ∈ Hub \ Hfree, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ h ∈ Hub \ Hfree, (G.neighborFinset h ∩ C).card := by
              refine Finset.sum_le_sum fun h hh => ?_
              simp only [hHfreedef, Finset.mem_sdiff, Finset.mem_filter, not_and,
                not_not] at hh
              exact hh.2 hh.1
      have hsdiffsum : ∑ h ∈ Hub \ Hfree, (G.neighborFinset h ∩ C).card
          ≤ ∑ h ∈ Hub, (G.neighborFinset h ∩ C).card :=
        Finset.sum_le_sum_of_subset Finset.sdiff_subset
      rw [hslotTot] at hsdiffsum
      have hcardsdiff : (Hub \ Hfree).card + Hfree.card = 8 := by
        rw [Finset.card_sdiff_add_card_eq_card hfreesub, hHubcard]
      omega
    obtain ⟨L, hLHub, hLslot0, hL5⟩ :
        ∃ L ∈ Hub, (G.neighborFinset L ∩ C).card = 0 ∧ G.degree L ≤ 5 := by
      by_contra hcon
      push Not at hcon
      have hbig : ∀ h ∈ Hfree, 6 ≤ G.degree h := by
        intro h hh
        have := hcon h (hfreesub hh) (hfree0 h hh)
        omega
      have hfreeb : 6 * Hfree.card ≤ ∑ h ∈ Hfree, G.degree h := by
        have := Finset.card_nsmul_le_sum Hfree (fun h => G.degree h) 6 hbig
        simpa [smul_eq_mul, mul_comm] using this
      have hrestb : 4 * (Hub \ Hfree).card ≤ ∑ h ∈ Hub \ Hfree, G.degree h := by
        have := Finset.card_nsmul_le_sum (Hub \ Hfree) (fun h => G.degree h) 4
          (fun h hh => (hmemHub h).mp (Finset.mem_sdiff.mp hh).1)
        simpa [smul_eq_mul, mul_comm] using this
      have hsplit : ∑ h ∈ Hub \ Hfree, G.degree h + ∑ h ∈ Hfree, G.degree h
          = ∑ h ∈ Hub, G.degree h := Finset.sum_sdiff hfreesub
      have hcardsdiff : (Hub \ Hfree).card + Hfree.card = 8 := by
        rw [Finset.card_sdiff_add_card_eq_card hfreesub, hHubcard]
      rw [hHubsum] at hsplit
      omega
    have hLj : (G.neighborFinset L ∩ J).card < 2 := hshared L hLHub hL5 hLslot0
    have hLe : 3 ≤ (G.neighborFinset L ∩ Hub).card := by
      have hp := hperhub L hLHub
      have hlow := (hmemHub L).mp hLHub
      omega
    have hnbr : ∀ h ∈ G.neighborFinset L ∩ Hub, 1 ≤ (G.neighborFinset h ∩ Hub).card := by
      intro h hh
      obtain ⟨hhN, _⟩ := Finset.mem_inter.mp hh
      have hadj : G.Adj h L := ((G.mem_neighborFinset _ _).mp hhN).symm
      exact Finset.card_pos.mpr ⟨L, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hadj, hLHub⟩⟩
    have hdisj : Disjoint ({L} : Finset (Fin 20)) (G.neighborFinset L ∩ Hub) := by
      rw [Finset.disjoint_singleton_left]
      exact fun hmem => G.irrefl ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hmem).1)
    have hunionsub : ({L} : Finset (Fin 20)) ∪ (G.neighborFinset L ∩ Hub) ⊆ Hub := by
      intro h hh
      rw [Finset.mem_union] at hh
      rcases hh with h' | h'
      · rw [Finset.mem_singleton] at h'; exact h' ▸ hLHub
      · exact (Finset.mem_inter.mp h').2
    have hsumub : (G.neighborFinset L ∩ Hub).card
        + ∑ h ∈ G.neighborFinset L ∩ Hub, (G.neighborFinset h ∩ Hub).card
        ≤ ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card := by
      have h : ∑ h ∈ ({L} : Finset (Fin 20)) ∪ (G.neighborFinset L ∩ Hub),
          (G.neighborFinset h ∩ Hub).card
          ≤ ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card :=
        Finset.sum_le_sum_of_subset hunionsub
      rwa [Finset.sum_union hdisj, Finset.sum_singleton] at h
    have hnbrsum : (G.neighborFinset L ∩ Hub).card
        ≤ ∑ h ∈ G.neighborFinset L ∩ Hub, (G.neighborFinset h ∩ Hub).card := by
      calc (G.neighborFinset L ∩ Hub).card
          = ∑ _h ∈ G.neighborFinset L ∩ Hub, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ h ∈ G.neighborFinset L ∩ Hub, (G.neighborFinset h ∩ Hub).card :=
            Finset.sum_le_sum hnbr
    omega

end N20

end ACMax
