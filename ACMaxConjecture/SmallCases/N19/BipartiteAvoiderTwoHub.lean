import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.Core

/-!
# Shared distinct-twin `TwoHubConfig` machinery for the `n = 19` bipartite-avoider residuals

The three `n = 19` hub-triangle bipartite-avoider residuals (`P₄` `|D| = 9` `|FF| = 4` `C₄`-plus-
apexes, the `C₅`/`K_{2,3}` five-avoider cherry corner, and the fat-star `|FF| = 6` `K_{3,3}` corner)
all share the same closing step: a triangle-free set of degree-`4` hubs, just above the good-`C₄` /
good-`K_{2,3}` thresholds, forces — via a shared-twin double count — two *non-adjacent* degree-`4`
hubs each carrying two **private** `M`-isolated twins, which assemble a `TwoHubConfig`
(`dense_two_hub_assemble`) and contradict `¬TwoHubConfig`.

This file collects the genuinely shared, configuration-independent counting lemma
`cherry_double_count` (the double count of pairwise shared twins as `∑_t (deg_S t)²`), reused by all
three corners.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Shared-twin double count.**  For any hub set `S` and twin set `Iso`, the double sum over
ordered hub pairs of their shared-twin count equals the sum over twins of the square of the twin's
`S`-degree.  This is the bookkeeping identity behind every distinct-twin `TwoHubConfig` extraction. -/
theorem cherry_double_count (G : SimpleGraph (Fin 19)) (S Iso : Finset (Fin 19)) :
    ∑ h ∈ S, ∑ h' ∈ S, (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card
      = ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card := by
  classical
  have hcard : ∀ h h' : Fin 19,
      (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card
        = ∑ t ∈ Iso, (if G.Adj h t ∧ G.Adj h' t then 1 else 0) := by
    intro h h'
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hh : G.Adj h t ∧ G.Adj h' t
    · simp only [Finset.mem_inter, G.mem_neighborFinset, hh.1, hh.2, and_self, if_pos]
    · rw [if_neg, if_neg hh]
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact hh
  have hSdeg : ∀ t : Fin 19, (G.neighborFinset t ∩ S).card
      = ∑ h ∈ S, (if G.Adj h t then 1 else 0) := by
    intro t
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun h _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
  simp_rw [hcard]
  have key : ∀ h ∈ S,
      (∑ h' ∈ S, ∑ t ∈ Iso, (if G.Adj h t ∧ G.Adj h' t then 1 else 0))
        = ∑ t ∈ Iso, ∑ h' ∈ S, (if G.Adj h t ∧ G.Adj h' t then 1 else 0) :=
    fun h _ => Finset.sum_comm
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [hSdeg, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  refine Finset.sum_congr rfl (fun h' _ => ?_)
  by_cases h1 : G.Adj h t <;> by_cases h2 : G.Adj h' t <;> simp [h1, h2]

/-- **Cherry-twin `TwoHubConfig` assembler (leaves need NOT be `M`-isolated).**  Generalises
`dense_two_hub_assemble`: two distinct non-adjacent degree-`4` hubs `h₁, h₂`, each with two *private*
degree-`3` leaves (`a, b` of `h₁`; `c, d` of `h₂`), assemble into a `TwoHubConfig` **provided the
four cross non-adjacencies** `¬G.Adj a c, ¬G.Adj a d, ¬G.Adj b c, ¬G.Adj b d` are supplied directly.
Unlike `dense_two_hub_assemble`, the leaves `a, b` are NOT required to be `M`-isolated (`Iso`); they
may be *cherry* (`P₄`) vertices.  This is the assembler underlying the corrected `n = 19` ISO1
cherry-twin route: on the excess-`11` boundary the isolated degree-`4` hub carries only `2`
`Iso`-neighbours, so at least one leaf on each side must be a cherry vertex, and the cross
non-adjacency `¬G.Adj a c` etc. must come from the cherry `P₄` structure (a cherry vertex meets a
degree-`3` vertex only along a `P₄` edge) rather than from the `Iso` property. -/
theorem two_hub_cherry_pair_nineteen (G : SimpleGraph (Fin 19)) (h₁ h₂ a b c d : Fin 19)
    (hdegh1 : G.degree h₁ = 4) (hdegh2 : G.degree h₂ = 4)
    (hdega : G.degree a = 3) (hdegb : G.degree b = 3)
    (hdegc : G.degree c = 3) (hdegd : G.degree d = 3)
    (hah1 : G.Adj a h₁) (hbh1 : G.Adj b h₁) (hch2 : G.Adj c h₂) (hdh2 : G.Adj d h₂)
    (hnadj : ¬G.Adj h₁ h₂)
    (hn_h1c : ¬G.Adj h₁ c) (hn_h1d : ¬G.Adj h₁ d)
    (hn_ah2 : ¬G.Adj a h₂) (hn_bh2 : ¬G.Adj b h₂)
    (hn_ac : ¬G.Adj a c) (hn_ad : ¬G.Adj a d) (hn_bc : ¬G.Adj b c) (hn_bd : ¬G.Adj b d)
    (hne_ab : a ≠ b) (hne_cd : c ≠ d)
    (hne_ac : a ≠ c) (hne_ad : a ≠ d) (hne_bc : b ≠ c) (hne_bd : b ≠ d) :
    TwoHubConfig G := by
  refine ⟨h₁, h₂, a, b, c, d, hdegh1, hdegh2, hdega, hdegb, hdegc, hdegd,
    hah1, hbh1, hch2, hdh2, hnadj, hn_h1c, hn_h1d, hn_ah2, hn_ac, hn_ad, hn_bh2, hn_bc, hn_bd,
    (by rintro rfl; exact hn_ah2 hah1),
    (by rintro rfl; exact G.irrefl hah1), (by rintro rfl; exact G.irrefl hbh1),
    (by rintro rfl; exact hnadj hch2), (by rintro rfl; exact hnadj hdh2),
    (by rintro rfl; exact hnadj hah1.symm), (by rintro rfl; exact hnadj hbh1.symm),
    (by rintro rfl; exact G.irrefl hch2), (by rintro rfl; exact G.irrefl hdh2),
    hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd⟩

/-- **Isolated-hub pairwise `C₄` share bound (corrects the "no pointwise-share" blocker).**
If `h₁` is a degree-`4` hub whose neighbourhood is an *independent set of degree-`3` vertices*
(which is exactly the situation of the `n = 19` ISO1 kernel: an internally-isolated degree-`4` hub
has neighbours `{L₁, L₂, b, e}` with `b, e ∈ Iso` meeting no degree-`3` vertex and `L₁, L₂`
non-adjacent, so **all** pairs of its neighbours are non-adjacent), then any *other* non-adjacent
degree-`4` hub `h₂` shares **at most one** neighbour with `h₁`.  Two shared neighbours `x, y` would
be non-adjacent (independence) and give the induced good `C₄` `h₁–x–h₂–y` of degree sum
`4 + 3 + 4 + 3 = 14 ≤ 14`, excluded by `hC4`.

This is the crucial observation the earlier ISO1 attempt missed: the general "two hubs may share
adjacent cherry vertices" obstruction to a pointwise share bound does **not** apply once one of the
two hubs is *internally isolated*, because then its neighbourhood is forced to be independent. -/
theorem isolated_deg4_share_le_one (G : SimpleGraph (Fin 19)) (h₁ h₂ : Fin 19)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hh1deg : G.degree h₁ = 4) (hh2deg : G.degree h₂ = 4) (hne : h₁ ≠ h₂)
    (hnadj : ¬G.Adj h₁ h₂)
    (hdeg3 : ∀ x ∈ G.neighborFinset h₁, G.degree x = 3)
    (hindep : ∀ x ∈ G.neighborFinset h₁, ∀ y ∈ G.neighborFinset h₁, x ≠ y → ¬G.Adj x y) :
    (G.neighborFinset h₁ ∩ G.neighborFinset h₂).card ≤ 1 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨x, hxmem, y, hymem, hxy⟩ := Finset.one_lt_card.mp hcon
  obtain ⟨hxN1, hxN2⟩ := Finset.mem_inter.mp hxmem
  obtain ⟨hyN1, hyN2⟩ := Finset.mem_inter.mp hymem
  -- Adjacencies of the `C₄` `h₁–x–h₂–y`.
  have hax1 : G.Adj h₁ x := (G.mem_neighborFinset h₁ x).mp hxN1
  have hay1 : G.Adj h₁ y := (G.mem_neighborFinset h₁ y).mp hyN1
  have hax2 : G.Adj x h₂ := ((G.mem_neighborFinset h₂ x).mp hxN2).symm
  have hay2 : G.Adj y h₂ := ((G.mem_neighborFinset h₂ y).mp hyN2).symm
  have hnxy : ¬G.Adj x y := hindep x hxN1 y hyN1 hxy
  -- Degrees.
  have hxd : G.degree x = 3 := hdeg3 x hxN1
  have hyd : G.degree y = 3 := hdeg3 y hyN1
  -- Distinctness of `{h₁, x, h₂, y}`.
  have hh1x : h₁ ≠ x := G.ne_of_adj hax1
  have hh1y : h₁ ≠ y := G.ne_of_adj hay1
  have hxh2 : x ≠ h₂ := G.ne_of_adj hax2
  have hyh2 : y ≠ h₂ := G.ne_of_adj hay2
  have hcard4 : ({h₁, x, h₂, y} : Finset (Fin 19)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hh1x, hne, hh1y]),
      Finset.card_insert_of_notMem (by simp [hxh2, hxy]),
      Finset.card_insert_of_notMem (by simp [hyh2.symm]), Finset.card_singleton]
  exact hC4 ⟨h₁, x, h₂, y, hcard4, hax1, hax2, hay2.symm, hay1.symm, hnadj, hnxy, by
    rw [hh1deg, hh2deg, hxd, hyd]⟩

/-- **Sharp counting dichotomy closing the ISO1 near-`K₅` kernel (`n = 19`, `|D| = 9`).**
The `10` hubs (`Hub = Dᶜ`) split as nine degree-`4` plus one degree-`5` hub `h₅`; the internally
isolated degree-`4` hub `h₁` meets both cherry leaves (`2 ≤ cinc h₁`) so `isoinc h₁ ≤ 2`; and the
total `Iso`-incidence is `15`.  Then EITHER some hub has NO cherry neighbour and at least two
`Iso`-neighbours (the centre of a `TwoTwinConfig`), OR some degree-`4` hub other than `h₁` has
internal degree `≤ 1` (the partner producing a `TwoHubConfig`).

This is the corrected forcing: the "balanced" configuration (all eight other degree-`4` hubs of
internal degree `2`) is excluded NOT by the near-`K₅` design but by pure counting against
`¬TwoTwinConfig`.  Under the negation of both disjuncts every degree-`4` hub `≠ h₁` has
`isoinc ≤ 1`, so `15 = ∑ isoinc ≤ 2 + isoinc h₅ + 8`, forcing `isoinc h₅ = 5`; but then `h₅` has no
cherry neighbour and five `Iso`-neighbours — the first disjunct — a contradiction.  Hence the
`14 < 15` deficit closes it. -/
theorem iso1_intdeg_dichotomy_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso Cherry : Finset (Fin 19)) (h₁ h₅ : Fin 19)
    (hHubcard : Hub.card = 10)
    (h1mem : h₁ ∈ Hub) (h5mem : h₅ ∈ Hub) (hne15 : h₁ ≠ h₅)
    (hdeg1 : G.degree h₁ = 4) (hdeg5 : G.degree h₅ = 5)
    (hdegOth : ∀ h ∈ Hub, h ≠ h₁ → h ≠ h₅ → G.degree h = 4)
    (hdecomp : ∀ h ∈ Hub,
      (G.neighborFinset h ∩ Cherry).card + (G.neighborFinset h ∩ Iso).card
        + (G.neighborFinset h ∩ Hub).card = G.degree h)
    (hsumIso : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 15)
    (h1cinc : 2 ≤ (G.neighborFinset h₁ ∩ Cherry).card)
    (h1int : (G.neighborFinset h₁ ∩ Hub).card = 0) :
    (∃ h ∈ Hub, (G.neighborFinset h ∩ Cherry).card = 0
        ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)
      ∨ (∃ h ∈ Hub, h ≠ h₁ ∧ G.degree h = 4 ∧ (G.neighborFinset h ∩ Hub).card ≤ 1) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hno1', hno2'⟩ := hcon
  -- Unpack the two negated disjuncts into per-hub arrows to `False`.
  have hno1 : ∀ h ∈ Hub, (G.neighborFinset h ∩ Cherry).card = 0 →
      2 ≤ (G.neighborFinset h ∩ Iso).card → False := by
    intro h hm hc hi; exact hno1' ⟨h, hm, hc, hi⟩
  have hno2 : ∀ h ∈ Hub, h ≠ h₁ → G.degree h = 4 →
      (G.neighborFinset h ∩ Hub).card ≤ 1 → False := by
    intro h hm hne hd hn; exact hno2' ⟨h, hm, hne, hd, hn⟩
  -- Per-hub `Iso`-incidence bound `isoinc h ≤ (if h = h₁ then 2 else if h = h₅ then 4 else 1)`.
  set B : Fin 19 → ℕ := fun h => if h = h₁ then 2 else if h = h₅ then 4 else 1 with hB
  have hbound : ∀ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≤ B h := by
    intro h hm
    have hdec := hdecomp h hm
    by_cases hh1 : h = h₁
    · subst hh1
      simp only [hB, if_pos rfl]
      rw [h1int, hdeg1] at hdec; omega
    · by_cases hh5 : h = h₅
      · simp only [hB, if_neg hh1, if_pos hh5]
        have hdh : G.degree h = 5 := by rw [hh5]; exact hdeg5
        rw [hdh] at hdec
        by_contra hgt
        push Not at hgt
        -- isoinc h ≥ 5 ⟹ cinc = intdeg = 0, contradicting `hno1`.
        have hc0 : (G.neighborFinset h ∩ Cherry).card = 0 := by omega
        exact hno1 h hm hc0 (by omega)
      · simp only [hB, if_neg hh1, if_neg hh5]
        have hd4 := hdegOth h hm hh1 hh5
        rw [hd4] at hdec
        have hn2 : 2 ≤ (G.neighborFinset h ∩ Hub).card := by
          by_contra hlt; push Not at hlt
          exact hno2 h hm hh1 hd4 (by omega)
        by_contra hgt; push Not at hgt
        have hc0 : (G.neighborFinset h ∩ Cherry).card = 0 := by omega
        exact hno1 h hm hc0 (by omega)
  -- Sum the bound: `15 = ∑ isoinc ≤ ∑ B = 14`.
  have hsumB : ∑ h ∈ Hub, B h = 14 := by
    have hpt : ∀ h, B h = 1 + ((if h = h₁ then 1 else 0) + (if h = h₅ then 3 else 0)) := by
      intro h
      by_cases hh1 : h = h₁
      · subst hh1; simp [hB, hne15]
      · by_cases hh5 : h = h₅
        · subst hh5; simp [hB, hh1]
        · simp [hB, hh1, hh5]
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_const, hHubcard, smul_eq_mul,
      Finset.sum_ite_eq' Hub h₁ (fun _ => (1 : ℕ)),
      Finset.sum_ite_eq' Hub h₅ (fun _ => (3 : ℕ)), h1mem, h5mem, if_pos]
    omega
  have hle : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ Hub, B h :=
    Finset.sum_le_sum hbound
  rw [hsumIso, hsumB] at hle
  omega

/-- **A cherry-free centre with two `Iso`-twins is a `TwoTwinConfig`.**  Abstract assembler: a vertex
`hc` (degree `≤ 5`) with at least two `Iso`-neighbours, non-adjacent to a `P₃` `x–y–z` of degree-`3`
non-`Iso` vertices, yields a `TwoTwinConfig` (twins = two `Iso`-neighbours, star centre `hc`, cherry
`x–y–z`).  The three cross non-adjacencies of each twin follow from `Iso`-isolation. -/
theorem twotwin_of_centre_nineteen (G : SimpleGraph (Fin 19))
    (Iso : Finset (Fin 19)) (hc x y z : Fin 19)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hxdeg : G.degree x = 3) (hydeg : G.degree y = 3) (hzdeg : G.degree z = 3)
    (hcdeg : G.degree hc ≤ 5)
    (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hnhcx : ¬G.Adj hc x) (hnhcy : ¬G.Adj hc y) (hnhcz : ¬G.Adj hc z)
    (hxIso : x ∉ Iso) (hyIso : y ∉ Iso) (hzIso : z ∉ Iso)
    (hcx : hc ≠ x) (hcy : hc ≠ y) (hcz : hc ≠ z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (h2iso : 2 ≤ (G.neighborFinset hc ∩ Iso).card) :
    TwoTwinConfig G := by
  classical
  have hIso_nadj : ∀ t : Fin 19, t ∈ Iso → ∀ w : Fin 19, G.degree w = 3 → ¬G.Adj t w :=
    fun t ht w hw hadj => (hIsoprop t ht).2 w hadj hw
  obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset hc ∩ Iso).card)
  obtain ⟨ht1N, ht1Iso⟩ := Finset.mem_inter.mp ht1
  obtain ⟨ht2N, ht2Iso⟩ := Finset.mem_inter.mp ht2
  have hAdj_ct1 : G.Adj hc t₁ := (G.mem_neighborFinset hc t₁).mp ht1N
  have hAdj_ct2 : G.Adj hc t₂ := (G.mem_neighborFinset hc t₂).mp ht2N
  have hdegt1 : G.degree t₁ = 3 := (hIsoprop t₁ ht1Iso).1
  have hdegt2 : G.degree t₂ = 3 := (hIsoprop t₂ ht2Iso).1
  exact ⟨t₁, t₂, hc, x, y, z, hdegt1, hdegt2, hcdeg, hxdeg, hydeg, hzdeg,
    hAdj_ct1.symm, hAdj_ct2.symm, hxy, hyz,
    (fun ha => hIso_nadj t₁ ht1Iso x hxdeg ha), (fun ha => hIso_nadj t₁ ht1Iso y hydeg ha),
    (fun ha => hIso_nadj t₁ ht1Iso z hzdeg ha),
    (fun ha => hIso_nadj t₂ ht2Iso x hxdeg ha), (fun ha => hIso_nadj t₂ ht2Iso y hydeg ha),
    (fun ha => hIso_nadj t₂ ht2Iso z hzdeg ha),
    hnhcx, hnhcy, hnhcz, ht12,
    (fun he => hxIso (he ▸ ht1Iso)), (fun he => hyIso (he ▸ ht1Iso)),
    (fun he => hzIso (he ▸ ht1Iso)),
    (fun he => hxIso (he ▸ ht2Iso)), (fun he => hyIso (he ▸ ht2Iso)),
    (fun he => hzIso (he ▸ ht2Iso)),
    hcx, hcy, hcz, hxy_ne, hyz_ne, hxz_ne⟩

end N19

end ACMax
