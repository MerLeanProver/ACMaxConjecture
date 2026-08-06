import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.TwoHubHub6Deg5

/-!
# The `|D| = 12`, `s = 4` cherry-`P₃` boundary corner (`n = 19`)

The new `n = 19` boundary (`6·12 = 72 = 68 + 4`; no `n = 18` analogue).  With
the cherry `x–y–z` (`e(M) = 2`, centre `y`), `|D| = 12` leaves `|Iso| = 9`
`M`-isolated twins carrying `27` hub incidences on `|Hub| = 7` hubs of total
degree `32`, and the cherry carries exactly `5` hub slots (`2 + 1 + 2`).  The
incidence identity `27 + 5 + 2e_{HH} = 32` forces **no hub–hub edges at
all**.  Dichotomy: a degree-`≤ 5` cherry-avoiding hub with two `M`-isolated
twins yields `TwoTwinConfig` against the cherry directly; otherwise the
slot/avoider LP kills `h₆ ∈ {0, 1}` and forces the exact `{6, 6, 4⁵}` tie —
every degree-`4` hub carries one cherry slot and three twins — whence any two
degree-`4` hubs (non-adjacent since `e_{HH} = 0`, sharing `≤ 1` twin by
`hC4`) assemble a `TwoHubConfig`.
-/

namespace ACMax

open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The `|D| = 12` cherry-`P₃` corner** (`s = 4`, `|Hub| = 7`): the
excess-`4` boundary closes into `TwoTwinConfig ∨ TwoHubConfig`. -/
theorem cherry_p3_config_D12_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (D Iso : Finset (Fin 19)) (x y z : Fin 19)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 19, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 19)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 12) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set C : Finset (Fin 19) := {x, y, z} with hCdef
  set Hub : Finset (Fin 19) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 19, v ∈ Hub ↔ 4 ≤ G.degree v := by
    intro v; rw [hHubdef]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum68 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplitDDc : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
    rw [Finset.sum_add_sum_compl]; exact hsum68
  have hHubsum : ∑ v ∈ Hub, G.degree v = 32 := by
    rw [hHubeqDc]; rw [hsumD, hDcard] at hsplitDDc; omega
  have hHubcard : Hub.card = 7 := by
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
  set J : Finset (Fin 19) := D \ C with hJdef
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
  have hJiso : ∀ v ∈ J, ∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3 :=
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
  have hsplitND : ∀ v : Fin 19,
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
  have hxzcard : ({x, z} : Finset (Fin 19)).card = 2 := by
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
    rw [cross_count_nineteen G Hub J]
    exact hJsum
  have hslotTot : ∑ h ∈ Hub, (G.neighborFinset h ∩ C).card = 5 := by
    rw [cross_count_nineteen G Hub C]
    exact hCsum
  have hJunion : J ∪ C = D := by
    rw [hJdef]
    exact Finset.sdiff_union_of_subset hCsubD
  have hJCdisj : Disjoint J C := by
    rw [hJdef]
    exact Finset.sdiff_disjoint
  have hDJC : ∀ s : Finset (Fin 19), (s ∩ D).card = (s ∩ J).card + (s ∩ C).card := by
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
  have hsumHH : ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card = 0 := by omega
  have hHH0 : ∀ h ∈ Hub, (G.neighborFinset h ∩ Hub).card = 0 :=
    fun h hh => Finset.sum_eq_zero_iff.mp hsumHH h hh
  have hnoHH : ∀ h₁ h₂ : Fin 19, h₁ ∈ Hub → h₂ ∈ Hub → ¬G.Adj h₁ h₂ := by
    intro h₁ h₂ hh₁ hh₂ hadj
    have h0 := hHH0 h₁ hh₁
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
    exact h0 h₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh₂⟩)
  have hpart : ∀ h ∈ Hub,
      (G.neighborFinset h ∩ J).card + (G.neighborFinset h ∩ C).card = G.degree h := by
    intro h hh
    have h1 := hsplitND h
    have h2 := hDJC (G.neighborFinset h)
    have h0 := hHH0 h hh
    omega
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
    have hkC : ∀ w : Fin 19, w ∈ C → ¬G.Adj k w := by
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
  · push Not at hshared
    have hslots1 : ∀ h ∈ Hub, G.degree h ≤ 5 → 1 ≤ (G.neighborFinset h ∩ C).card := by
      intro h hh hle
      by_contra hcon
      push Not at hcon
      have h0 : (G.neighborFinset h ∩ C).card = 0 := by omega
      have hlt := hshared h hh hle h0
      have hp := hpart h hh
      have h4 := (hmemHub h).mp hh
      omega
    set Hub5 : Finset (Fin 19) := Hub.filter (fun h => G.degree h ≤ 5) with hHub5def
    set H6 : Finset (Fin 19) := Hub.filter (fun h => ¬G.degree h ≤ 5) with hH6def
    have hmemHub5 : ∀ h : Fin 19, h ∈ Hub5 ↔ h ∈ Hub ∧ G.degree h ≤ 5 := by
      intro h; rw [hHub5def]; exact Finset.mem_filter
    have hmemH6 : ∀ h : Fin 19, h ∈ H6 ↔ h ∈ Hub ∧ ¬G.degree h ≤ 5 := by
      intro h; rw [hH6def]; exact Finset.mem_filter
    have hcardsplit : Hub5.card + H6.card = 7 := by
      rw [hHub5def, hH6def, Finset.card_filter_add_card_filter_not, hHubcard]
    have hdegsplit : ∑ h ∈ Hub5, G.degree h + ∑ h ∈ H6, G.degree h = 32 := by
      rw [hHub5def, hH6def, Finset.sum_filter_add_sum_filter_not, hHubsum]
    have hslotsplit : ∑ h ∈ Hub5, (G.neighborFinset h ∩ C).card
        + ∑ h ∈ H6, (G.neighborFinset h ∩ C).card = 5 := by
      rw [hHub5def, hH6def, Finset.sum_filter_add_sum_filter_not, hslotTot]
    have hHub5sub : ∀ h ∈ Hub5, h ∈ Hub := fun h hh => ((hmemHub5 h).mp hh).1
    have hHub5lb : 4 * Hub5.card ≤ ∑ h ∈ Hub5, G.degree h := by
      calc 4 * Hub5.card = ∑ _h ∈ Hub5, 4 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ h ∈ Hub5, G.degree h :=
            Finset.sum_le_sum fun h hh => (hmemHub h).mp (hHub5sub h hh)
    have hH6lb : 6 * H6.card ≤ ∑ h ∈ H6, G.degree h := by
      calc 6 * H6.card = ∑ _h ∈ H6, 6 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ h ∈ H6, G.degree h := by
            refine Finset.sum_le_sum fun h hh => ?_
            have := ((hmemH6 h).mp hh).2
            omega
    have hslotlb : Hub5.card ≤ ∑ h ∈ Hub5, (G.neighborFinset h ∩ C).card := by
      calc Hub5.card = ∑ _h ∈ Hub5, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ h ∈ Hub5, (G.neighborFinset h ∩ C).card :=
            Finset.sum_le_sum fun h hh =>
              hslots1 h ((hmemHub5 h).mp hh).1 ((hmemHub5 h).mp hh).2
    have hn5 : Hub5.card = 5 := by omega
    have hS5 : ∑ h ∈ Hub5, G.degree h = 20 := by omega
    have hs5sum : ∑ h ∈ Hub5, (G.neighborFinset h ∩ C).card = 5 := by omega
    have hdeg4 : ∀ h ∈ Hub5, G.degree h = 4 := by
      intro h hh
      have h1 : G.degree h + ∑ v ∈ Hub5.erase h, G.degree v = 20 :=
        (Finset.add_sum_erase _ (fun v => G.degree v) hh).trans hS5
      have h2 : 4 * (Hub5.erase h).card ≤ ∑ v ∈ Hub5.erase h, G.degree v := by
        calc 4 * (Hub5.erase h).card = ∑ _v ∈ Hub5.erase h, 4 := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ v ∈ Hub5.erase h, G.degree v :=
              Finset.sum_le_sum fun v hv =>
                (hmemHub v).mp (hHub5sub v (Finset.mem_of_mem_erase hv))
      have h3c : (Hub5.erase h).card = 4 := by
        rw [Finset.card_erase_of_mem hh, hn5]
      have h4 := (hmemHub h).mp (hHub5sub h hh)
      omega
    have hslots1each : ∀ h ∈ Hub5, (G.neighborFinset h ∩ C).card = 1 := by
      intro h hh
      have h1 : (G.neighborFinset h ∩ C).card
          + ∑ v ∈ Hub5.erase h, (G.neighborFinset v ∩ C).card = 5 :=
        (Finset.add_sum_erase _ (fun v => (G.neighborFinset v ∩ C).card) hh).trans hs5sum
      have h2 : (Hub5.erase h).card ≤ ∑ v ∈ Hub5.erase h, (G.neighborFinset v ∩ C).card := by
        calc (Hub5.erase h).card = ∑ _v ∈ Hub5.erase h, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ v ∈ Hub5.erase h, (G.neighborFinset v ∩ C).card := by
              refine Finset.sum_le_sum fun v hv => ?_
              have hvm := (hmemHub5 v).mp (Finset.mem_of_mem_erase hv)
              exact hslots1 v hvm.1 hvm.2
      have h3c : (Hub5.erase h).card = 4 := by
        rw [Finset.card_erase_of_mem hh, hn5]
      have h4 := hslots1 h ((hmemHub5 h).mp hh).1 ((hmemHub5 h).mp hh).2
      omega
    have hiso3each : ∀ h ∈ Hub5, (G.neighborFinset h ∩ J).card = 3 := by
      intro h hh
      have hp := hpart h (hHub5sub h hh)
      have h1 := hslots1each h hh
      have h2 := hdeg4 h hh
      omega
    have hcommon : ∀ h h' : Fin 19, h ∈ Hub5 → h' ∈ Hub5 → h ≠ h' →
        ((G.neighborFinset h ∩ J) ∩ G.neighborFinset h').card ≤ 1 := by
      intro h h' hh hh' hne
      by_contra hcon
      push Not at hcon
      obtain ⟨t, htm, t', htm', htt'⟩ := Finset.one_lt_card.mp hcon
      obtain ⟨htNJ, htN'⟩ := Finset.mem_inter.mp htm
      obtain ⟨htN, htJ⟩ := Finset.mem_inter.mp htNJ
      obtain ⟨ht'NJ, ht'N'⟩ := Finset.mem_inter.mp htm'
      obtain ⟨ht'N, ht'J⟩ := Finset.mem_inter.mp ht'NJ
      have hAht : G.Adj h t := (G.mem_neighborFinset _ _).mp htN
      have hAh't : G.Adj h' t := (G.mem_neighborFinset _ _).mp htN'
      have hAht' : G.Adj h t' := (G.mem_neighborFinset _ _).mp ht'N
      have hAh't' : G.Adj h' t' := (G.mem_neighborFinset _ _).mp ht'N'
      have htdeg : G.degree t = 3 := hJdeg t htJ
      have ht'deg : G.degree t' = 3 := hJdeg t' ht'J
      have hd4 : G.degree h = 4 := hdeg4 h hh
      have hd4' : G.degree h' = 4 := hdeg4 h' hh'
      have hntt' : ¬G.Adj t t' := fun ha => hJiso t htJ t' ha ht'deg
      have hnhh' : ¬G.Adj h h' := hnoHH h h' (hHub5sub h hh) (hHub5sub h' hh')
      have hth : t ≠ h := by rintro rfl; omega
      have hth' : t ≠ h' := by rintro rfl; omega
      have ht'h : t' ≠ h := by rintro rfl; omega
      have ht'h' : t' ≠ h' := by rintro rfl; omega
      exact hC4 ⟨t, h, t', h',
        card_four_nineteen t h t' h' hth htt' hth' (Ne.symm ht'h) hne ht'h',
        hAht.symm, hAht', hAh't'.symm, hAh't, hntt', hnhh', by omega⟩
    have hpriv : ∀ h h' : Fin 19, h ∈ Hub5 → h' ∈ Hub5 → h ≠ h' →
        2 ≤ ((G.neighborFinset h ∩ J) \ G.neighborFinset h').card := by
      intro h h' hh hh' hne
      have h1 := hiso3each h hh
      have h2 := hcommon h h' hh hh' hne
      have h3s := Finset.card_sdiff_add_card_inter (G.neighborFinset h ∩ J)
        (G.neighborFinset h')
      omega
    obtain ⟨h₁, hh₁, h₂, hh₂, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < Hub5.card)
    have hp12 : 2 ≤ ((G.neighborFinset h₁ ∩ J) \ G.neighborFinset h₂).card :=
      hpriv h₁ h₂ hh₁ hh₂ hne12
    have hp21 : 2 ≤ ((G.neighborFinset h₂ ∩ J) \ G.neighborFinset h₁).card :=
      hpriv h₂ h₁ hh₂ hh₁ (Ne.symm hne12)
    obtain ⟨a, ham, b, hbm, hab⟩ := Finset.one_lt_card.mp
      (by omega : 1 < ((G.neighborFinset h₁ ∩ J) \ G.neighborFinset h₂).card)
    obtain ⟨c, hcm, d, hdm, hcd⟩ := Finset.one_lt_card.mp
      (by omega : 1 < ((G.neighborFinset h₂ ∩ J) \ G.neighborFinset h₁).card)
    obtain ⟨haNJ, haN2⟩ := Finset.mem_sdiff.mp ham
    obtain ⟨haN1, haJ⟩ := Finset.mem_inter.mp haNJ
    obtain ⟨hbNJ, hbN2⟩ := Finset.mem_sdiff.mp hbm
    obtain ⟨hbN1, hbJ⟩ := Finset.mem_inter.mp hbNJ
    obtain ⟨hcNJ, hcN1⟩ := Finset.mem_sdiff.mp hcm
    obtain ⟨hcN2, hcJ⟩ := Finset.mem_inter.mp hcNJ
    obtain ⟨hdNJ, hdN1⟩ := Finset.mem_sdiff.mp hdm
    obtain ⟨hdN2, hdJ⟩ := Finset.mem_inter.mp hdNJ
    have hA1a : G.Adj h₁ a := (G.mem_neighborFinset _ _).mp haN1
    have hA1b : G.Adj h₁ b := (G.mem_neighborFinset _ _).mp hbN1
    have hA2c : G.Adj h₂ c := (G.mem_neighborFinset _ _).mp hcN2
    have hA2d : G.Adj h₂ d := (G.mem_neighborFinset _ _).mp hdN2
    have hna2 : ¬G.Adj h₂ a := fun ha => haN2 ((G.mem_neighborFinset _ _).mpr ha)
    have hnb2 : ¬G.Adj h₂ b := fun ha => hbN2 ((G.mem_neighborFinset _ _).mpr ha)
    have hnc1 : ¬G.Adj h₁ c := fun ha => hcN1 ((G.mem_neighborFinset _ _).mpr ha)
    have hnd1 : ¬G.Adj h₁ d := fun ha => hdN1 ((G.mem_neighborFinset _ _).mpr ha)
    have hadeg : G.degree a = 3 := hJdeg a haJ
    have hbdeg : G.degree b = 3 := hJdeg b hbJ
    have hcdeg : G.degree c = 3 := hJdeg c hcJ
    have hddeg : G.degree d = 3 := hJdeg d hdJ
    have hd41 : G.degree h₁ = 4 := hdeg4 h₁ hh₁
    have hd42 : G.degree h₂ = 4 := hdeg4 h₂ hh₂
    have hnh12 : ¬G.Adj h₁ h₂ := hnoHH h₁ h₂ (hHub5sub h₁ hh₁) (hHub5sub h₂ hh₂)
    have hnac : ¬G.Adj a c := fun ha => hJiso a haJ c ha hcdeg
    have hnad : ¬G.Adj a d := fun ha => hJiso a haJ d ha hddeg
    have hnbc : ¬G.Adj b c := fun ha => hJiso b hbJ c ha hcdeg
    have hnbd : ¬G.Adj b d := fun ha => hJiso b hbJ d ha hddeg
    have h1a : h₁ ≠ a := by rintro rfl; omega
    have h1b : h₁ ≠ b := by rintro rfl; omega
    have h1c : h₁ ≠ c := by rintro rfl; omega
    have h1d : h₁ ≠ d := by rintro rfl; omega
    have h2a : h₂ ≠ a := by rintro rfl; omega
    have h2b : h₂ ≠ b := by rintro rfl; omega
    have h2c : h₂ ≠ c := by rintro rfl; omega
    have h2d : h₂ ≠ d := by rintro rfl; omega
    have hac : a ≠ c := by rintro rfl; exact hna2 hA2c
    have had : a ≠ d := by rintro rfl; exact hna2 hA2d
    have hbc : b ≠ c := by rintro rfl; exact hnb2 hA2c
    have hbd : b ≠ d := by rintro rfl; exact hnb2 hA2d
    exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, a, b, c, d, hd41, hd42, hadeg, hbdeg, hcdeg, hddeg,
      hA1a.symm, hA1b.symm, hA2c.symm, hA2d.symm, hnh12, hnc1, hnd1,
      fun ha => hna2 ha.symm, hnac, hnad, fun ha => hnb2 ha.symm, hnbc, hnbd,
      hne12, h1a, h1b, h1c, h1d, h2a, h2b, h2c, h2d, hab, hac, had, hbc, hbd, hcd⟩))

end N19

end ACMax
