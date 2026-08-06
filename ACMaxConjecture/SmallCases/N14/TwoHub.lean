import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.TwoHubSelect

/-!
# Two-hub opposite-twin configuration for the `n = 14` residual (`e(M) ≤ 3` branch)

This file supplies the structural-selection lemma `two_hub_config_fourteen`, the `e(M) ≤ 3`
("two-hub") branch of the `n = 14` twin-certificate dichotomy.  It is the analogue of the `n = 13`
`node_A_config` (`TwinCert13TwoHub`), but the `n = 14` numerics differ: the handshake no longer
forces the clean `[4⁵, 3⁸]` degree sequence.  Instead `two_hub_forced_split` shows the residual is
EITHER `|D| = 8, |Hub| = 6` (all hubs degree `4`) OR `|D| = 9, |Hub| = 5`.

Contents:

* `two_hub_forced_split` — the `|D| ∈ {8, 9}` handshake dichotomy (fully proved);
* `each_iso_three_hubs` — every `M`-isolated degree-3 twin has its three neighbours all in `Hub`
  (fully proved);
* `two_hub_config_fourteen` — the two non-adjacent degree-4 hubs with two private isolated twins
  each.  The final hub-pair *selection* (a double-count pigeonhole, sensitive to the `|Hub| = 6`
  vs `|Hub| = 5` split and to adjacent hub pairs) is left as the one documented `sorry`; the
  surrounding structural set-up and the boundary assembly are fully proved.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Handshake dichotomy for the `n = 14` two-hub residual (fully proved).**  With `24` edges,
minimum degree `3`, and `∑_{v∈D}|N v ∩ D| ≤ 6` (i.e. `e(M) ≤ 3`), the degree-3 set `D` and the hub
set `Hub` satisfy either `|D| = 8, |Hub| = 6` with every hub of degree exactly `4`, or
`|D| = 9, |Hub| = 5`. -/
theorem two_hub_forced_split (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (D Hub : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (hmemHub : ∀ v : Fin 14, v ∈ Hub ↔ 4 ≤ G.degree v)
    (hle : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 6) :
    (D.card = 8 ∧ Hub.card = 6 ∧ ∀ h ∈ Hub, G.degree h = 4) ∨
      (D.card = 9 ∧ Hub.card = 5) := by
  classical
  have hsum : ∑ v : Fin 14, G.degree v = 48 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hDH : ∀ v : Fin 14, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub := by
    rw [Finset.disjoint_left]; intro v hv hv'
    have := (hmemD v).mp hv; have := (hmemHub v).mp hv'; omega
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard14 : D.card + Hub.card = 14 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 48 := by
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
  have hSsumD : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitD, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hSsumHub : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card
      + ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = ∑ w ∈ Hub, G.degree w := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitHub]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card := cross_count_fourteen G D Hub
  have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
    have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
    have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul, mul_comm] using h
  have hD89 : D.card = 8 ∨ D.card = 9 := by omega
  rcases hD89 with h8 | h9
  · refine Or.inl ⟨h8, by omega, ?_⟩
    have hHub6 : Hub.card = 6 := by omega
    have hsumHubdeg : ∑ w ∈ Hub, G.degree w = 24 := by omega
    intro w hw
    have hge := (hmemHub w).mp hw
    have hiso := Finset.add_sum_erase Hub (fun v => G.degree v) hw
    have herase : 4 * (Hub.erase w).card ≤ ∑ v ∈ Hub.erase w, G.degree v := by
      have hb : ∀ x ∈ Hub.erase w, 4 ≤ G.degree x := fun i hi =>
        (hmemHub i).mp (Finset.mem_of_mem_erase hi)
      have h := Finset.card_nsmul_le_sum (Hub.erase w) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hec : (Hub.erase w).card = Hub.card - 1 := Finset.card_erase_of_mem hw
    omega
  · exact Or.inr ⟨h9, by omega⟩

/-- **Each `M`-isolated twin meets exactly three hubs (fully proved).**  An `M`-isolated degree-3
twin `t` (`(N t ∩ D).card = 0`) has all three of its neighbours in `Hub`, so
`(N t ∩ Hub).card = 3`. -/
theorem each_iso_three_hubs (G : SimpleGraph (Fin 14)) (D Hub : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (hmemHub : ∀ v : Fin 14, v ∈ Hub ↔ 4 ≤ G.degree v)
    (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (t : Fin 14) (htD : t ∈ D) (htiso : (G.neighborFinset t ∩ D).card = 0) :
    (G.neighborFinset t ∩ Hub).card = 3 := by
  classical
  have hDH : ∀ v : Fin 14, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hsub : G.neighborFinset t ⊆ Hub := by
    intro x hx
    rcases hDH x with hxD | hxH
    · exfalso
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at htiso
      exact htiso x (Finset.mem_inter.mpr ⟨hx, hxD⟩)
    · exact hxH
  rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, (hmemD t).mp htD]

/-- **Non-adjacent hubs share at most two isolated twins (fully proved).**  If `h₁ ≠ h₂` are two
non-adjacent vertices of degree `≤ 4` then they have at most two common `M`-isolated degree-3
neighbours: three such common neighbours `a, b, c` are pairwise non-adjacent (isolated twins are
`M`-independent) and non-adjacent to `h₁, h₂`, giving a good `K_{2,3}` with parts `{h₁, h₂}` and
`{a, b, c}` of degree-sum `≤ 4 + 4 + 3 + 3 + 3 = 17 ≤ 18`, contradicting `hK23`. -/
theorem nonadj_hub_pair_share_le_two (G : SimpleGraph (Fin 14)) (D Iso : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (hisoD : ∀ x : Fin 14, x ∈ Iso → x ∈ D)
    (hisoNoD : ∀ x y : Fin 14, x ∈ Iso → y ∈ D → ¬G.Adj x y)
    (hK23 : ¬∃ a b c d e : Fin 14, ({a, b, c, d, e} : Finset (Fin 14)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (h₁ h₂ : Fin 14) (hd1 : G.degree h₁ ≤ 4) (hd2 : G.degree h₂ ≤ 4)
    (hne : h₁ ≠ h₂) (hnadj : ¬G.Adj h₁ h₂) :
    (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcon
  have hmem : ∀ x : Fin 14, x ∈ G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso →
      G.Adj h₁ x ∧ G.Adj h₂ x ∧ x ∈ Iso := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  obtain ⟨ha1, ha2, haIso⟩ := hmem a ha
  obtain ⟨hb1, hb2, hbIso⟩ := hmem b hb
  obtain ⟨hc1, hc2, hcIso⟩ := hmem c hc
  have haD := hisoD a haIso
  have hbD := hisoD b hbIso
  have hcD := hisoD c hcIso
  have hnab : ¬G.Adj a b := hisoNoD a b haIso hbD
  have hnac : ¬G.Adj a c := hisoNoD a c haIso hcD
  have hnbc : ¬G.Adj b c := hisoNoD b c hbIso hcD
  have h1a : h₁ ≠ a := G.ne_of_adj ha1
  have h1b : h₁ ≠ b := G.ne_of_adj hb1
  have h1c : h₁ ≠ c := G.ne_of_adj hc1
  have h2a : h₂ ≠ a := G.ne_of_adj ha2
  have h2b : h₂ ≠ b := G.ne_of_adj hb2
  have h2c : h₂ ≠ c := G.ne_of_adj hc2
  refine hK23 ⟨h₁, h₂, a, b, c,
    card_five_fourteen h₁ h₂ a b c hne h1a h1b h1c h2a h2b h2c hab hac hbc,
    ha1, hb1, hc1, ha2, hb2, hc2, hnadj, hnab, hnac, hnbc, ?_⟩
  have : G.degree a = 3 := (hmemD a).mp haD
  have : G.degree b = 3 := (hmemD b).mp hbD
  have : G.degree c = 3 := (hmemD c).mp hcD
  omega

/-- **Single-component bound for the non-isolated set of `M = G[D]` (fully proved).**  Twice the
number of `M`-non-isolated degree-3 vertices is at most `∑_{v∈D}|N v ∩ D| + 2 = 2·e(M) + 2`.  The
proof is the `2K₂`-free single-component argument of `two_isolated_twins`: the non-isolated set is a
single connected component of `M`, so it has at most `e(M) + 1` vertices. -/
theorem nonisolated_component_bound (G : SimpleGraph (Fin 14)) (D : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d) :
    2 * (D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0)).card
      ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card + 2 := by
  classical
  set S : Finset (Fin 14) := D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) with hSdef
  set M : SimpleGraph (Fin 14) :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ D ∧ b ∈ D
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun a h => G.irrefl h.1⟩ } with hMdef
  have hMadj : ∀ a b : Fin 14, M.Adj a b ↔ G.Adj a b ∧ a ∈ D ∧ b ∈ D := fun _ _ => Iff.rfl
  have hSmem : ∀ v : Fin 14, v ∈ S ↔ v ∈ D ∧ ∃ w : Fin 14, G.Adj v w ∧ w ∈ D := by
    intro v
    rw [hSdef, Finset.mem_filter]
    refine and_congr_right (fun _ => ?_)
    rw [← ne_eq, Finset.card_ne_zero]
    simp only [Finset.Nonempty, Finset.mem_inter, G.mem_neighborFinset]
  have hsupp : M.support = (↑S : Set (Fin 14)) := by
    ext v
    rw [SimpleGraph.mem_support, Finset.mem_coe, hSmem]
    constructor
    · rintro ⟨w, hadj, hvD, hwD⟩; exact ⟨hvD, w, hadj, hwD⟩
    · rintro ⟨hvD, w, hadj, hwD⟩; exact ⟨w, hadj, hvD, hwD⟩
  have hMdeg : ∀ v : Fin 14,
      M.degree v = if v ∈ D then (G.neighborFinset v ∩ D).card else 0 := by
    intro v
    have hd : M.degree v = (M.neighborFinset v).card := rfl
    rw [hd]
    by_cases hvD : v ∈ D
    · simp only [hvD, if_true]
      congr 1
      ext w
      rw [SimpleGraph.mem_neighborFinset, hMadj, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hvD, h.2⟩⟩
    · simp only [hvD, if_false]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, hMadj] at hw
      exact hvD hw.2.1
  have hsumM : ∑ v : Fin 14, M.degree v = ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
    simp_rw [hMdeg]
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe]; simp
  · have hVne : Nonempty ↥M.support := by
      obtain ⟨x, hx⟩ := hSne
      exact ⟨⟨x, by rw [hsupp]; exact Finset.mem_coe.mpr hx⟩⟩
    have radj : ∀ {a b : Fin 14} (ha : a ∈ M.support) (hb : b ∈ M.support),
        M.Adj a b → (M.induce M.support).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b ha hb hab
      exact (SimpleGraph.induce_adj.mpr hab).reachable
    have hpre : (M.induce M.support).Preconnected := by
      intro u v
      set a : Fin 14 := (↑u : Fin 14) with hadef
      set b : Fin 14 := (↑v : Fin 14) with hbdef
      obtain ⟨a', haa'⟩ := u.2
      obtain ⟨b', hbb'⟩ := v.2
      replace haa' : M.Adj a a' := haa'
      replace hbb' : M.Adj b b' := hbb'
      have ha'supp : a' ∈ M.support := haa'.mem_support_right
      have hb'supp : b' ∈ M.support := hbb'.mem_support_right
      have hA := (hMadj a a').mp haa'
      have hB := (hMadj b b').mp hbb'
      have haD : a ∈ D := hA.2.1
      have ha'D : a' ∈ D := hA.2.2
      have hbD : b ∈ D := hB.2.1
      have hb'D : b' ∈ D := hB.2.2
      by_cases hab : a = b
      · have huv : u = v := Subtype.ext hab
        rw [huv]
      by_cases hab' : a = b'
      · have hadj : M.Adj a b := by
          rw [← hab'] at hbb'; exact hbb'.symm
        exact radj u.2 v.2 hadj
      by_cases ha'b : a' = b
      · have hadj : M.Adj a b := by rw [ha'b] at haa'; exact haa'
        exact radj u.2 v.2 hadj
      by_cases ha'b' : a' = b'
      · have hUV : (⟨a', ha'supp⟩ : ↥M.support) = ⟨b', hb'supp⟩ := Subtype.ext ha'b'
        exact (radj u.2 ha'supp haa').trans (hUV ▸ (radj v.2 hb'supp hbb').symm)
      · have hcard4 : ({a, a', b, b'} : Finset (Fin 14)).card = 4 :=
          card_four_fourteen a a' b b' haa'.ne hab hab' ha'b ha'b' hbb'.ne
        have hcross : G.Adj a b ∨ G.Adj a b' ∨ G.Adj a' b ∨ G.Adj a' b' := by
          by_contra hc
          simp only [not_or] at hc
          exact h2k2 ⟨a, a', b, b', hcard4,
            (hmemD a).mp haD, (hmemD a').mp ha'D, (hmemD b).mp hbD, (hmemD b').mp hb'D,
            hA.1, hB.1, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
        rcases hcross with h | h | h | h
        · exact radj u.2 v.2 ((hMadj a b).mpr ⟨h, haD, hbD⟩)
        · exact (radj u.2 hb'supp ((hMadj a b').mpr ⟨h, haD, hb'D⟩)).trans
            (radj v.2 hb'supp hbb').symm
        · exact (radj u.2 ha'supp haa').trans
            (radj ha'supp v.2 ((hMadj a' b).mpr ⟨h, ha'D, hbD⟩))
        · exact ((radj u.2 ha'supp haa').trans
            (radj ha'supp hb'supp ((hMadj a' b').mpr ⟨h, ha'D, hb'D⟩))).trans
            (radj v.2 hb'supp hbb').symm
    have hconn : (M.induce M.support).Connected := by
      have := hVne
      exact ⟨hpre⟩
    have hbound := hconn.card_vert_le_card_edgeSet_add_one
    have hns : Nat.card ↥M.support = S.card := by
      rw [hsupp, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hes : Nat.card (M.induce M.support).edgeSet = M.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
        SimpleGraph.card_edgeFinset_induce_support]
    rw [hns, hes] at hbound
    have hh := M.sum_degrees_eq_twice_card_edges
    rw [hsumM] at hh
    omega

/-- **Exactly six `M`-isolated twins at `e(M) = 1` (fully proved).**  With `|D| = 8`, `M` `2K₂`-free,
`∑_{v∈D}|N v ∩ D| ≤ 2` and `∑_{v∈D}|N v ∩ D| ≠ 0` (i.e. `e(M) = 1`, a single `M`-edge), the
non-isolated set is exactly the two endpoints of that edge, so exactly `6` of the eight degree-`3`
vertices are `M`-isolated. -/
theorem iso_card_eq_six (G : SimpleGraph (Fin 14)) (D : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hD8 : D.card = 8)
    (hpos : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≠ 0)
    (hle : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2) :
    (D.filter (fun x => (G.neighborFinset x ∩ D).card = 0)).card = 6 := by
  classical
  have hpart : (D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)).card
      + (D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0)).card = D.card :=
    Finset.card_filter_add_card_filter_not (s := D)
      (p := fun v => (G.neighborFinset v ∩ D).card = 0)
  have hbound := nonisolated_component_bound G D hmemD h2k2
  have hge2 : 2 ≤ (D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0)).card := by
    obtain ⟨v, hvD, hvne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
    obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp hvne
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hvw, hwD⟩ := hw
    have hvNI : v ∈ D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) :=
      Finset.mem_filter.mpr ⟨hvD, hvne⟩
    have hwNI : w ∈ D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) :=
      Finset.mem_filter.mpr ⟨hwD, Finset.card_ne_zero.mpr
        ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvw.symm, hvD⟩⟩⟩
    have hvwne : v ≠ w := G.ne_of_adj hvw
    have hsub : ({v, w} : Finset (Fin 14)) ⊆
        D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hvNI
      · exact hwNI
    calc 2 = ({v, w} : Finset (Fin 14)).card := (Finset.card_pair hvwne).symm
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-- **Handshake refinement for the `n = 14` two-hub residual with `e(M) ≤ 2` (fully proved).**
With `24` edges, minimum degree `3` and `∑_{v∈D}|N v ∩ D| ≤ 4` (i.e. `e(M) ≤ 2`), the
`|D| = 9, |Hub| = 5` branch of `two_hub_forced_split` is excluded, so `|D| = 8`, `|Hub| = 6`,
every hub has degree exactly `4`, and `∑_{w∈Hub}|N w ∩ Hub| = ∑_{v∈D}|N v ∩ D|` (i.e.
`e(Hub) = e(M)`). -/
theorem two_hub_forced_six (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (D Hub : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (hmemHub : ∀ v : Fin 14, v ∈ Hub ↔ 4 ≤ G.degree v)
    (hle : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 4) :
    D.card = 8 ∧ Hub.card = 6 ∧ (∀ h ∈ Hub, G.degree h = 4) ∧
      ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card
        = ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
  classical
  have hsum : ∑ v : Fin 14, G.degree v = 48 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hDH : ∀ v : Fin 14, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub := by
    rw [Finset.disjoint_left]; intro v hv hv'
    have := (hmemD v).mp hv; have := (hmemHub v).mp hv'; omega
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 48 := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
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
  have hSsumD : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitD, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hSsumHub : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card
      + ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = ∑ w ∈ Hub, G.degree w := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitHub]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card := cross_count_fourteen G D Hub
  have hkey : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card + 6 * D.card
      = 48 + ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by omega
  rcases two_hub_forced_split G hm h3 D Hub hmemD hmemHub (by omega) with
    ⟨hD8, hHub6, hdeg4⟩ | ⟨hD9, hHub5⟩
  · exact ⟨hD8, hHub6, hdeg4, by omega⟩
  · exfalso; omega

/-- **Two-hub opposite-twin configuration (`e(M) ≤ 1` branch for `n = 14`).**  Hypothesis `hle`
says `∑_{v∈D}|N v ∩ D| ≤ 2`, i.e. `e(M) ≤ 1` (no `P₃` cherry).  One selects two non-adjacent
degree-4 hubs `h₁ ≠ h₂` and four `M`-isolated degree-3 twins `a, b` (private to `h₁`) and `c, d`
(private to `h₂`) for the two-hub opposite-twin cut.  At `e(M) = 0` the matching is edgeless
(`|Iso| = 8`); at `e(M) = 1` the single edge forces `|Iso| = 6` (`iso_card_eq_six`), so the hub-pair
selection runs the `|Iso| = 6` route of `two_hub_pair_select_fourteen` and the false `|Iso| = 5`
two-hub corner (`iso5_lowprofile_pair`) is never reached.  This lemma is now **`sorry`-free**. -/
theorem two_hub_config_fourteen (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (_hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 14, ({a, b, c, d, e} : Finset (Fin 14)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (_hiso : ∃ t : Fin 14, G.degree t = 3 ∧ ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3)
    (hle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 2) :
    ∃ h₁ h₂ a b c d : Fin 14,
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj d h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ d ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧
      ¬G.Adj b h₂ ∧ ¬G.Adj b c ∧ ¬G.Adj b d ∧
      h₁ ≠ h₂ ∧ h₁ ≠ a ∧ h₁ ≠ b ∧ h₁ ≠ c ∧ h₁ ≠ d ∧
      h₂ ≠ a ∧ h₂ ≠ b ∧ h₂ ≠ c ∧ h₂ ≠ d ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 14) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 14, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hHubnotD : ∀ x : Fin 14, x ∈ Hub → x ∉ D := by
    intro x hx hxD; have := (hmemHub x).mp hx; have := (hmemD x).mp hxD; omega
  set Iso : Finset (Fin 14) := D.filter (fun x => (G.neighborFinset x ∩ D).card = 0) with hIsodef
  have hIsomem : ∀ x : Fin 14, x ∈ Iso ↔ x ∈ D ∧ (G.neighborFinset x ∩ D).card = 0 := by
    intro x; rw [hIsodef, Finset.mem_filter]
  have hisoD : ∀ x : Fin 14, x ∈ Iso → x ∈ D := fun x hx => ((hIsomem x).mp hx).1
  have hisoNoD : ∀ x y : Fin 14, x ∈ Iso → y ∈ D → ¬G.Adj x y := by
    intro x y hx hy hadj
    obtain ⟨_, hx0⟩ := (hIsomem x).mp hx
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hx0
    exact hx0 y (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hadj, hy⟩)
  -- **Hub-pair selection (the one documented `sorry`).**  The forced split
  -- (`two_hub_forced_split`) gives `|Hub| ∈ {5, 6}` with at least four degree-4 hubs; every
  -- isolated twin meets exactly three hubs (`each_iso_three_hubs`); a double count over hub-pairs
  -- (`∑ |N h₁ ∩ N h₂ ∩ Iso| = 3|Iso|`) together with the good-`K_{2,3}` bound (`hK23` forbids a
  -- non-adjacent hub-pair sharing `≥ 3` isolated twins) yields two non-adjacent degree-4 hubs each
  -- retaining `≥ 2` private isolated twins.  The case analysis on `|Hub| = 6` (where hubs may be
  -- adjacent, `e(Hub) = e(M)`) vs `|Hub| = 5` is the remaining structural work.
  have hpair : ∃ h₁ h₂ : Fin 14, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
    by_cases hs0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0
    · -- **`e(M) = 0`: `M` edgeless, every twin isolated; clean hub pair.**
      have hzero : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 :=
        (Finset.sum_eq_zero_iff).mp hs0
      have hDiso : ∀ v : Fin 14, v ∈ D → v ∈ Iso := fun v hv =>
        (hIsomem v).mpr ⟨hv, hzero v hv⟩
      have hDH : ∀ v : Fin 14, v ∈ D ∨ v ∈ Hub := fun v => by
        rcases Nat.lt_or_ge (G.degree v) 4 with h | h
        · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
        · exact Or.inr ((hmemHub v).mpr h)
      have hdisj : Disjoint D Hub :=
        Finset.disjoint_left.mpr (fun v hv hv' => hHubnotD v hv' hv)
      have hunion : D ∪ Hub = Finset.univ := by
        ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
      have hsum : ∑ v : Fin 14, G.degree v = 48 := by
        rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
      have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
        rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
          mul_comm]
      have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 48 := by
        rw [← Finset.sum_union hdisj, hunion]; exact hsum
      have hsplitD : ∀ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 := by
        intro v hv
        have hdeg : (G.neighborFinset v).card = 3 := by
          rw [G.card_neighborFinset_eq_degree, (hmemD v).mp hv]
        have hu : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
          rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
        have hdj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
          Finset.disjoint_left.mpr (fun a ha hb =>
            (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
        have hc := Finset.card_union_of_disjoint hdj
        rw [hu, hdeg] at hc
        have := hzero v hv; omega
      have hcrossD : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
        rw [Finset.sum_congr rfl hsplitD, Finset.sum_const, smul_eq_mul, mul_comm]
      have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
          = ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card := cross_count_fourteen G D Hub
      have hcrossND : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card = 3 * D.card := by
        rw [← hcross]; exact hcrossD
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
      have hSsumHub : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card
          + ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = ∑ w ∈ Hub, G.degree w := by
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitHub]
      have heq : 6 * D.card + (∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card) = 48 := by
        have h1 := hsumpart
        rw [hsumD, ← hSsumHub, hcrossND] at h1; omega
      rcases two_hub_forced_split G hm h3 D Hub hmemD hmemHub (by omega) with
        ⟨hD8, hHub6, hdeg4⟩ | ⟨hD9, _⟩
      · have hS2 : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 0 := by omega
        have hnhub0 : ∀ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 0 :=
          (Finset.sum_eq_zero_iff).mp hS2
        have hNiso : ∀ w : Fin 14, w ∈ Hub → (G.neighborFinset w ∩ Iso).card = 4 := by
          intro w hw
          have hwH0 := hnhub0 w hw
          have hsubD : G.neighborFinset w ⊆ D := by
            intro x hx
            rcases hDH x with hxD | hxH
            · exact hxD
            · exfalso
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hwH0
              exact hwH0 x (Finset.mem_inter.mpr ⟨hx, hxH⟩)
          have hsubIso : G.neighborFinset w ⊆ Iso := fun x hx => hDiso x (hsubD hx)
          rw [Finset.inter_eq_left.mpr hsubIso, G.card_neighborFinset_eq_degree, hdeg4 w hw]
        obtain ⟨h₁, h₂, hh1, hh2, hne12⟩ := Finset.one_lt_card_iff.mp (by rw [hHub6]; norm_num)
        have hd1 : G.degree h₁ ≤ 4 := by rw [hdeg4 h₁ hh1]
        have hd2 : G.degree h₂ ≤ 4 := by rw [hdeg4 h₂ hh2]
        have hnadj12 : ¬G.Adj h₁ h₂ := by
          intro hadj
          have hwH0 := hnhub0 h₁ hh1
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hwH0
          exact hwH0 h₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr hadj, hh2⟩)
        refine ⟨h₁, h₂, hh1, hh2, hdeg4 h₁ hh1, hdeg4 h₂ hh2, hne12, hnadj12, ?_, ?_⟩
        · have hshare := nonadj_hub_pair_share_le_two G D Iso hmemD hisoD hisoNoD hK23 h₁ h₂
            hd1 hd2 hne12 hnadj12
          have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
            (G.neighborFinset h₂)
          have hI4 := hNiso h₁ hh1
          have hreord : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
              = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := Finset.inter_right_comm _ _ _
          rw [hreord] at hkey; omega
        · have hshare := nonadj_hub_pair_share_le_two G D Iso hmemD hisoD hisoNoD hK23 h₂ h₁
            hd2 hd1 (Ne.symm hne12) (fun h => hnadj12 h.symm)
          have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso)
            (G.neighborFinset h₁)
          have hI4 := hNiso h₂ hh2
          have hreord : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset h₁
              = G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso := Finset.inter_right_comm _ _ _
          rw [hreord] at hkey; omega
      · exfalso; omega
    · -- **`e(M) ∈ {1, 2, 3}` (`s ∈ {2, 4, 6}`).**
      by_cases hs4 : (∑ v ∈ D, (G.neighborFinset v ∩ D).card) ≤ 4
      · -- **`e(M) = 1` (`s = 2`).**  The structural set-up is fully proved here:
        -- `two_hub_forced_six` forces `|D| = 8`, `|Hub| = 6`, every hub degree `4`, and
        -- `∑_{w∈Hub}|N w ∩ Hub| = s` (so `e(Hub) = e(M) = 1`); since `e(M) = 1` (`hle : s ≤ 2`,
        -- `hs0 : s ≠ 0`), `iso_card_eq_six` gives `|Iso| = 6` exactly (so the false `|Iso| = 5`
        -- two-hub corner is unreachable); `each_iso_three_hubs` gives every isolated twin exactly
        -- three hub neighbours.
        obtain ⟨hD8, hHub6, hdeg4, hHubsum⟩ :=
          two_hub_forced_six G hm h3 D Hub hmemD hmemHub hs4
        have hIso6 : Iso.card = 6 := by
          rw [hIsodef]; exact iso_card_eq_six G D hmemD h2k2 hD8 hs0 hle
        have hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3 := fun t ht =>
          each_iso_three_hubs G D Hub hmemD hmemHub h3 t (hisoD t ht) ((hIsomem t).mp ht).2
        -- **Hub-pair selection** (delegated to `two_hub_pair_select_fourteen`).  The hub-edge
        -- equality `hHubsum` and `hs4` give `e(Hub) ≤ 2`; `hisoNoD`/`hisoD` give the twins'
        -- `M`-independence; `nonadj_hub_pair_share_le_two` gives the good-`K_{2,3}` share bound.
        exact two_hub_pair_select_fourteen G Hub Iso hHub6 hdeg4 (by rw [hHubsum]; exact hs4)
          hIso6 hiso3 (fun a ha b hb => hisoNoD a b ha (hisoD b hb))
          (fun h₁ hh1 h₂ hh2 hne hnadj => nonadj_hub_pair_share_le_two G D Iso hmemD hisoD hisoNoD
            hK23 h₁ h₂ (hdeg4 h₁ hh1).le (hdeg4 h₂ hh2).le hne hnadj)
      · -- **`s ≥ 6` is excluded.**  The hypothesis `hle : s ≤ 2` makes this branch (`¬ s ≤ 4`)
        -- contradictory, so the former `s = 6` two-hub corner is no longer reached here (the `s = 4`
        -- and `s = 6` regimes are now handled by the alignment dichotomies in `TwinCert14`).
        exfalso; omega
  obtain ⟨h₁, h₂, hh1, hh2, hdeg1, hdeg2, hne12, hnadj12, hAcard, hBcard⟩ := hpair
  set A : Finset (Fin 14) := (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ with hAdef
  set B : Finset (Fin 14) := (G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁ with hBdef
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hAcard
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hBcard
  have hAprop : ∀ x : Fin 14, x ∈ A → G.Adj x h₁ ∧ x ∈ Iso ∧ ¬G.Adj x h₂ := by
    intro x hx
    rw [hAdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
    refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
    intro hadj; exact hx.2 ((G.mem_neighborFinset h₂ x).mpr hadj.symm)
  have hBprop : ∀ x : Fin 14, x ∈ B → G.Adj x h₂ ∧ x ∈ Iso ∧ ¬G.Adj x h₁ := by
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

end N14

end ACMax
