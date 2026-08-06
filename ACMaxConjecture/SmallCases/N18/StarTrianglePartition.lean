import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.HubTriangleFF
import ACMaxConjecture.SmallCases.N18.StarTriangle
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.RichEdge
import ACMaxConjecture.SmallCases.N18.RichNoZero
import ACMaxConjecture.SmallCases.N18.RichZdeg
import ACMaxConjecture.SmallCases.N18.StarTriangleNineSeven

/-!
# The star-triangle extraction from the rigid `n = 18` partition

This file supplies the **clean combinatorial kernel** of the `n = 18` star-triangle dichotomy for
the tight `e(M) = 1`, `(|Hub|, |Iso|, ∑deg) = (10, 6, 40)` profile.

Given the *rigid partition structure* of a no-two-hub configuration — verified to hold for both
no-two-hub isomorphism classes — namely:

* all ten hubs have degree `4`;
* the hubs split as `Hub = R ⊔ P` with `|R| = 6` *rich* hubs (iso-degree `≥ 2`) and `|P| = 4`
  *poor* hubs (iso-degree exactly `1`);
* there are **no** rich–poor hub edges (`E(R, P) = 0`);
* each `M`-isolated twin meets exactly three hubs and `∑_{g∈P}|N(g)∩P| ≥ 10`,

this file proves `starTriangle_of_rigid_eighteen`: such a configuration always contains a
`StarTriangleConfig` (a rich hub centre with two twins, plus a totally non-adjacent poor
hub-triangle).  The proof is a Mantel-`4` triangle inside the four poor hubs, followed by a
*bad-twin* pigeonhole: the three poor triangle vertices have only three twins between them, so the
twins lying on the triangle absorb at most `2·3 = 6` of the `14` rich incidences, leaving `≥ 8` for
the `6` rich hubs and hence a rich hub with two twins avoiding the triangle.

The two genuinely-hard structural inputs (the partition `|R| = 6 ∧ |P| = 4` and `E(R, P) = 0`) are
NOT proved here; they are covering-design facts that resist the abstract `N1`/`N2`/`N3` budget and
are left to dedicated nodes.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **All ten hubs have degree `4` (tight `(10, 6, 40)` profile).**  Every hub has degree `≥ 4`
(`hdeg`) and the ten hub degrees sum to `40`; erasing any one hub leaves nine hubs summing to
`≥ 4·9 = 36`, so the erased hub has degree `≤ 40 − 36 = 4`, hence exactly `4`. -/
theorem all_hub_deg_four_eighteen (G : SimpleGraph (Fin 18)) (Hub : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hcard : Hub.card = 10)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40) :
    ∀ h ∈ Hub, G.degree h = 4 := by
  classical
  intro h₀ hh₀
  have hsplit : G.degree h₀ + ∑ h ∈ Hub.erase h₀, G.degree h = ∑ h ∈ Hub, G.degree h :=
    Finset.add_sum_erase Hub (fun h => G.degree h) hh₀
  have hge : 4 * (Hub.erase h₀).card ≤ ∑ h ∈ Hub.erase h₀, G.degree h := by
    calc 4 * (Hub.erase h₀).card = ∑ _h ∈ Hub.erase h₀, 4 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ h ∈ Hub.erase h₀, G.degree h :=
            Finset.sum_le_sum (fun h hh => hdeg h (Finset.mem_of_mem_erase hh))
  rw [Finset.card_erase_of_mem hh₀, hcard] at hge
  have hh4 := hdeg h₀ hh₀
  omega

/-- **Star-triangle extraction from the rigid partition (`|Hub| = 10`, `|Iso| = 6`).**  Given the
all-degree-`4` rich/poor partition `Hub = R ⊔ P` (`|R| = 6`, `|P| = 4`), every poor hub of
iso-degree exactly `1`, no rich–poor hub edge (`hERP`), each twin meeting exactly three hubs of
degree `3`, and the poor-internal edge mass `≥ 10`, the configuration contains a
`StarTriangleConfig`. -/
theorem starTriangle_of_rigid_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R P : Finset (Fin 18))
    (hHub : Hub = R ∪ P) (hdisjRP : Disjoint R P) (hdisjHI : Disjoint Hub Iso)
    (hRcard : R.card = 6) (hPcard : P.card = 4) (hIsocard : Iso.card = 6)
    (hRdeg : ∀ h ∈ R, G.degree h = 4) (hPdeg : ∀ g ∈ P, G.degree g = 4)
    (hPpoor : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1)
    (htwin3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (htwindeg : ∀ t ∈ Iso, G.degree t = 3)
    (hERP : ∀ r ∈ R, ∀ g ∈ P, ¬G.Adj r g)
    (hpoor_edges : 10 ≤ ∑ g ∈ P, (G.neighborFinset g ∩ P).card) :
    StarTriangleConfig G := by
  classical
  -- **Mantel-`4` triangle inside the four poor hubs.**
  obtain ⟨a, b, c, haP, hbP, hcP, hAab, hAac, hAbc⟩ :=
    mantel_four_triangle G P hPcard hpoor_edges
  have aHub : a ∈ Hub := by rw [hHub]; exact Finset.mem_union_right _ haP
  have bHub : b ∈ Hub := by rw [hHub]; exact Finset.mem_union_right _ hbP
  have cHub : c ∈ Hub := by rw [hHub]; exact Finset.mem_union_right _ hcP
  -- **Total rich iso-incidences `= 14`.**
  have hsumHub : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have h := hub_iso_sum_eighteen G Hub Iso htwin3
    rw [hIsocard] at h; omega
  have hsplit : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card
      = ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card := by
    rw [hHub, Finset.sum_union hdisjRP]
  have hsumP : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 4 := by
    have heq : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = ∑ _g ∈ P, 1 :=
      Finset.sum_congr rfl (fun g hg => hPpoor g hg)
    rw [heq, Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  have hRiso14 : ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card = 14 := by omega
  have hcrossR : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 14 := by
    rw [cross_count G Iso R]; exact hRiso14
  -- **Bad twins (those touching the triangle) carry `≤ 2` rich incidences each.**
  set pBad : Fin 18 → Prop := fun t => G.Adj t a ∨ G.Adj t b ∨ G.Adj t c with hpBaddef
  have hBadpt : ∀ t ∈ Iso.filter pBad, (G.neighborFinset t ∩ R).card ≤ 2 := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htIso, hadj⟩ := ht
    have hpart : (G.neighborFinset t ∩ R).card + (G.neighborFinset t ∩ P).card
        = (G.neighborFinset t ∩ Hub).card := by
      rw [hHub, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisjRP (Finset.mem_inter.mp hx1).2 (Finset.mem_inter.mp hx2).2
    have hP1 : 1 ≤ (G.neighborFinset t ∩ P).card := by
      rcases hadj with h | h | h
      · exact Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h, haP⟩⟩
      · exact Finset.card_pos.mpr ⟨b, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h, hbP⟩⟩
      · exact Finset.card_pos.mpr ⟨c, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h, hcP⟩⟩
    rw [htwin3 t htIso] at hpart
    omega
  -- **At most three bad twins.**
  have hfiltercard : ∀ v ∈ P, (Iso.filter (fun t => G.Adj t v)).card = 1 := by
    intro v hv
    have heq : Iso.filter (fun t => G.Adj t v) = G.neighborFinset v ∩ Iso := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset, SimpleGraph.adj_comm]
      tauto
    rw [heq]; exact hPpoor v hv
  have hBadsub : Iso.filter pBad ⊆ Iso.filter (fun t => G.Adj t a)
      ∪ Iso.filter (fun t => G.Adj t b) ∪ Iso.filter (fun t => G.Adj t c) := by
    intro t ht
    rw [Finset.mem_filter, hpBaddef] at ht
    obtain ⟨htIso, hp⟩ := ht
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases hp with h | h | h
    · exact Or.inl (Or.inl ⟨htIso, h⟩)
    · exact Or.inl (Or.inr ⟨htIso, h⟩)
    · exact Or.inr ⟨htIso, h⟩
  have hBadcard : (Iso.filter pBad).card ≤ 3 := by
    have h1 := Finset.card_le_card hBadsub
    have h2 := Finset.card_union_le
      (Iso.filter (fun t => G.Adj t a) ∪ Iso.filter (fun t => G.Adj t b))
      (Iso.filter (fun t => G.Adj t c))
    have h3 := Finset.card_union_le
      (Iso.filter (fun t => G.Adj t a)) (Iso.filter (fun t => G.Adj t b))
    have ha1 := hfiltercard a haP
    have hb1 := hfiltercard b hbP
    have hc1 := hfiltercard c hcP
    omega
  have hBadsum : ∑ t ∈ Iso.filter pBad, (G.neighborFinset t ∩ R).card ≤ 6 := by
    calc ∑ t ∈ Iso.filter pBad, (G.neighborFinset t ∩ R).card
        ≤ ∑ _t ∈ Iso.filter pBad, 2 := Finset.sum_le_sum hBadpt
      _ = 2 * (Iso.filter pBad).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 6 := by omega
  -- **Good twins carry `≥ 8` rich incidences.**
  have hsumsplit : ∑ t ∈ Iso.filter pBad, (G.neighborFinset t ∩ R).card
      + ∑ t ∈ Iso.filter (fun t => ¬pBad t), (G.neighborFinset t ∩ R).card
      = ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card :=
    Finset.sum_filter_add_sum_filter_not Iso pBad _
  have hGoodsum : 8 ≤ ∑ t ∈ Iso.filter (fun t => ¬pBad t), (G.neighborFinset t ∩ R).card := by
    rw [hcrossR] at hsumsplit; omega
  have hcrossGood : ∑ h ∈ R, (G.neighborFinset h ∩ Iso.filter (fun t => ¬pBad t)).card
      = ∑ t ∈ Iso.filter (fun t => ¬pBad t), (G.neighborFinset t ∩ R).card :=
    cross_count G R (Iso.filter (fun t => ¬pBad t))
  have hRGood8 : 8 ≤ ∑ h ∈ R, (G.neighborFinset h ∩ Iso.filter (fun t => ¬pBad t)).card := by
    rw [hcrossGood]; exact hGoodsum
  -- **Pigeonhole: a rich hub with two good twins.**
  obtain ⟨h, hhR, hh2⟩ : ∃ h ∈ R, 2 ≤ (G.neighborFinset h ∩ Iso.filter (fun t => ¬pBad t)).card := by
    by_contra hcon
    push Not at hcon
    have hle : ∑ h ∈ R, (G.neighborFinset h ∩ Iso.filter (fun t => ¬pBad t)).card
        ≤ ∑ _h ∈ R, 1 := Finset.sum_le_sum (fun h hh => by have := hcon h hh; omega)
    rw [Finset.sum_const, hRcard, smul_eq_mul, mul_one] at hle
    omega
  obtain ⟨t₁, ht₁, t₂, ht₂, hne12⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset h ∩ Iso.filter (fun t => ¬pBad t)).card)
  -- **Unpack the two good twins.**
  rw [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_filter] at ht₁ ht₂
  obtain ⟨hAht1, ht1Iso, hnp1⟩ := ht₁
  obtain ⟨hAht2, ht2Iso, hnp2⟩ := ht₂
  rw [hpBaddef] at hnp1 hnp2
  push Not at hnp1 hnp2
  -- **Assemble the `StarTriangleConfig`.**
  refine ⟨h, t₁, t₂, a, b, c, hRdeg h hhR, htwindeg t₁ ht1Iso, htwindeg t₂ ht2Iso,
    hPdeg a haP, hPdeg b hbP, hPdeg c hcP, hAht1, hAht2, hAab, hAac, hAbc,
    hERP h hhR a haP, hERP h hhR b hbP, hERP h hhR c hcP,
    hnp1.1, hnp1.2.1, hnp1.2.2, hnp2.1, hnp2.2.1, hnp2.2.2, hne12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun he => Finset.disjoint_left.mp hdisjRP hhR (he ▸ haP)
  · exact fun he => Finset.disjoint_left.mp hdisjRP hhR (he ▸ hbP)
  · exact fun he => Finset.disjoint_left.mp hdisjRP hhR (he ▸ hcP)
  · exact fun he => Finset.disjoint_left.mp hdisjHI aHub (he ▸ ht1Iso)
  · exact fun he => Finset.disjoint_left.mp hdisjHI bHub (he ▸ ht1Iso)
  · exact fun he => Finset.disjoint_left.mp hdisjHI cHub (he ▸ ht1Iso)
  · exact fun he => Finset.disjoint_left.mp hdisjHI aHub (he ▸ ht2Iso)
  · exact fun he => Finset.disjoint_left.mp hdisjHI bHub (he ▸ ht2Iso)
  · exact fun he => Finset.disjoint_left.mp hdisjHI cHub (he ▸ ht2Iso)

/-- **Rich internal edge bound (`r = 6`).**  With all hubs degree `4`, each twin meeting three
hubs, `N3` (`18` hub-hub incidences), and every hub meeting `≥ 1` twin (`no_iso_zero`), the six rich
hubs `R = {h : 2 ≤ |N(h) ∩ Iso|}` span at most `4` internal edges, i.e.
`∑_{r∈R}|N(r) ∩ R| ≤ 8`.  The poor hubs carry iso-degree exactly `1`, so `∑_R isoDeg = 14`; each rich
hub keeps `≤ 4 − a(r)` hub-neighbours, and the `N3` incidence budget pins the rich-internal share. -/
theorem rich_edge_le_four_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) :
    ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 8 := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  -- `∑_R Zdeg ≥ 2` from the rigid `Z`-distribution.
  obtain ⟨hzR, _⟩ := zdeg_split_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT
  rw [← hRdef, ← hZdef] at hzR
  -- `|P| = 4`.
  have hPcard : P.card = 4 := by
    have := Finset.card_filter_add_card_filter_not (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
      (s := Hub)
    rw [← hRdef, ← hPdef, hHub, hr6] at this; omega
  -- `∑_R isoDeg = 14`: total `18`, poor side `= |P| = 4`.
  have hiso18 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hisoP : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 4 := by
    have heq : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = ∑ _g ∈ P, 1 := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgHub : g ∈ Hub := (Finset.filter_subset _ _) hg
      rw [hPdef, Finset.mem_filter] at hg
      have := hnozero g hgHub
      omega
    rw [heq, Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  have hisoR : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 14 := by
    have hsplit : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
      rw [hRdef, hPdef,
        Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
      exact hiso18
    omega
  -- Per-hub three-way split summed over `R`.
  have hdegsum : ∑ r ∈ R, G.degree r = 24 := by
    have heq : ∑ r ∈ R, G.degree r = ∑ _r ∈ R, 4 :=
      Finset.sum_congr rfl (fun r hr => hdeg4 r (hRsubHub hr))
    rw [heq, Finset.sum_const, hr6, smul_eq_mul]
  have hsplit3 : ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card
      + ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card + ∑ r ∈ R, (G.neighborFinset r ∩ Z).card
      = ∑ r ∈ R, G.degree r := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => nbr_split_three_eighteen G Hub Iso hdisj r)
  -- `∑_R |N ∩ Hub| = 24 − 14 − Zdeg ≤ 8`.
  have hhubR : ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card ≤ 8 := by
    rw [hdegsum, hisoR] at hsplit3; omega
  -- `∑_R |N ∩ R| ≤ ∑_R |N ∩ Hub|`.
  calc ∑ r ∈ R, (G.neighborFinset r ∩ R).card
      ≤ ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card := by
        apply Finset.sum_le_sum
        intro r _
        exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsubHub)
    _ ≤ 8 := hhubR

/-- **No rich–poor hub edge (`E(R, P) = 0`).**  For the all-degree-`4` `(10, 6)` profile with the
rigid rich count `r = 6`, no iso-degree-`0` hub, and the `Z`-distribution `2 ≤ ∑_R Zdeg`, a rich hub
`r` (iso-degree `≥ 2`) is never adjacent to a poor hub `g` (iso-degree `1`): such an edge, together
with `N1`/`hC4`/`hK23`, forces a good two-hub pair or a forbidden cycle.  Here
`R = {h : 2 ≤ |N(h) ∩ Iso|}` and `P` is its complement in `Hub`. -/
theorem rich_poor_no_edge_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) :
    ∀ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
      ∀ g ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card), ¬G.Adj r g := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hPsubHub : P ⊆ Hub := Finset.filter_subset _ _
  have hunion : R ∪ P = Hub := Finset.filter_union_filter_not_eq _ Hub
  have hdisjRP : Disjoint R P := Finset.disjoint_filter_filter_not Hub Hub _
  have hPcard : P.card = 4 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) (s := Hub)
    rw [← hRdef, ← hPdef, hHub] at hsplit; omega
  -- `∑_R a = 14`: total `18`, poor side `= |P| = 4`.
  have hiso18 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hisoP : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 4 := by
    have heq : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = ∑ _g ∈ P, 1 := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgHub : g ∈ Hub := hPsubHub hg
      rw [hPdef, Finset.mem_filter] at hg
      have := hnozero g hgHub; omega
    rw [heq, Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  have hisoR : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 14 := by
    have hsplit : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
      rw [hRdef, hPdef,
        Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
      exact hiso18
    omega
  -- `z_R ≥ 2` from the rigid `Z`-distribution.
  obtain ⟨hzR, _⟩ := zdeg_split_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT
  rw [← hRdef, ← hZdef] at hzR
  -- Rich-degree handshake `∑_R|N∩Hub| + 14 + z_R = 24`.
  have hdeg24 : ∑ r ∈ R, G.degree r = 24 := by
    rw [Finset.sum_congr rfl (fun r hr => hdeg4 r (hRsubHub hr)), Finset.sum_const, hr6,
      smul_eq_mul]
  have hsplit3 : ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card
      + ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card + ∑ r ∈ R, (G.neighborFinset r ∩ Z).card = 24 := by
    have hcong : ∑ r ∈ R, ((G.neighborFinset r ∩ Hub).card + (G.neighborFinset r ∩ Iso).card
        + (G.neighborFinset r ∩ Z).card) = ∑ r ∈ R, G.degree r :=
      Finset.sum_congr rfl (fun r _ => nbr_split_three_eighteen G Hub Iso hdisj r)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdeg24] at hcong; exact hcong
  -- `∑_R|N∩Hub| = ∑_R|N∩R| + ∑_R|N∩P|`.
  have hHubsplit : ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card
      = ∑ r ∈ R, (G.neighborFinset r ∩ R).card + ∑ r ∈ R, (G.neighborFinset r ∩ P).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← hunion, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
    exact Finset.disjoint_left.mpr (fun x hx1 hx2 =>
      Finset.disjoint_left.mp hdisjRP (Finset.mem_inter.mp hx1).2 (Finset.mem_inter.mp hx2).2)
  -- The rich internal edge mass is pinned at `8`.
  have hle := rich_edge_le_four_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT hr6 hnozero
  have hge := rich_edge_ge_four_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT hr6 hnozero
  rw [← hRdef] at hle hge
  -- Hence `∑_R|N∩P| = 0`.
  have hRP0 : ∑ r ∈ R, (G.neighborFinset r ∩ P).card = 0 := by
    rw [hisoR] at hsplit3; omega
  -- Conclude: no rich–poor hub edge.
  intro r hr g hg hadj
  have hrP0 : (G.neighborFinset r ∩ P).card = 0 :=
    (Finset.sum_eq_zero_iff.mp hRP0) r hr
  rw [Finset.card_eq_zero] at hrP0
  have hgmem : g ∈ G.neighborFinset r ∩ P :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r g).mpr hadj, hg⟩
  rw [hrP0] at hgmem
  exact Finset.notMem_empty g hgmem

/-- **The rigid rich/poor partition of a no-two-hub `(10, 6)` configuration (`n = 18`).**  From the
all-degree-`4` profile, the rich count `r = 6` (`rich_count_le_seven`, `rich_count_ge_six`,
`rich_count_ne_seven`), `no_iso_zero`, `rich_edge_le_four`, `N3`, and `hC4`, the hub set splits as
`Hub = R ⊔ P` with `|R| = 6` rich hubs, `|P| = 4` poor hubs of iso-degree exactly `1`, no rich–poor
hub edge (`E(R, P) = 0`), and poor-internal edge mass `≥ 10`. -/
theorem rich_poor_partition_assemble_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    ∃ R P : Finset (Fin 18), Hub = R ∪ P ∧ Disjoint R P ∧ R.card = 6 ∧ P.card = 4 ∧
      Iso.card = 6 ∧ (∀ h ∈ R, G.degree h = 4) ∧ (∀ g ∈ P, G.degree g = 4) ∧
      (∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1) ∧
      (∀ r ∈ R, ∀ g ∈ P, ¬G.Adj r g) ∧
      10 ≤ ∑ g ∈ P, (G.neighborFinset g ∩ P).card := by
  classical
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  -- The rich count is exactly `6`.
  have hle7 := rich_count_le_seven_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  have hge6 := rich_count_ge_six_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  have hne7 := rich_count_ne_seven_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hisodeg3
    hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT
  rw [← hRdef] at hle7 hge6 hne7
  have hr6 : R.card = 6 := by omega
  -- No hub has iso-degree `0`.
  have hnozero := no_iso_zero_hub_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT
  -- `R ⊔ P = Hub`, disjoint, with `|P| = 4`.
  have hunion : R ∪ P = Hub := Finset.filter_union_filter_not_eq _ Hub
  have hdisjRP : Disjoint R P := Finset.disjoint_filter_filter_not Hub Hub _
  have hPcard : P.card = 4 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) (s := Hub)
    rw [← hRdef, ← hPdef, hHub] at hsplit; omega
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hPsubHub : P ⊆ Hub := Finset.filter_subset _ _
  -- Poor hubs have iso-degree exactly `1`.
  have hPpoor : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hg
    have hgHub : g ∈ Hub := hPsubHub hg
    rw [hPdef, Finset.mem_filter] at hg
    have h1 := hnozero g hgHub
    omega
  -- **`E(R, P) = 0`**: no rich–poor hub edge.
  have hERP : ∀ r ∈ R, ∀ g ∈ P, ¬G.Adj r g :=
    rich_poor_no_edge_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3 hdsum hleak
      hshare hno2hub hC4 hK23 hT hr6 hnozero
  -- **`∑_P Zdeg ≤ 2`** from the rigid `Z`-distribution.
  obtain ⟨_, hzP⟩ := zdeg_split_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT
  rw [← hPdef] at hzP
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- **Poor-internal edge mass `≥ 10`**: `∑_P |N ∩ P| = ∑_P |N ∩ Hub| = 16 − 4 − Zdeg ≥ 10`.
  have hpoormass : 10 ≤ ∑ g ∈ P, (G.neighborFinset g ∩ P).card := by
    -- Each poor hub has no rich neighbour, so `|N ∩ Hub| = |N ∩ P|`.
    have hgP_eq : ∀ g ∈ P, (G.neighborFinset g ∩ P).card = (G.neighborFinset g ∩ Hub).card := by
      intro g hg
      have hsplit : (G.neighborFinset g ∩ R).card + (G.neighborFinset g ∩ P).card
          = (G.neighborFinset g ∩ Hub).card := by
        rw [← hunion, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
        exact Finset.disjoint_left.mpr (fun x hx1 hx2 =>
          Finset.disjoint_left.mp hdisjRP (Finset.mem_inter.mp hx1).2 (Finset.mem_inter.mp hx2).2)
      have hR0 : (G.neighborFinset g ∩ R).card = 0 := by
        rw [Finset.card_eq_zero]
        ext x
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
        intro hxN hxR
        exact hERP x hxR g hg ((G.mem_neighborFinset g x).mp hxN |>.symm)
      omega
    -- Three-way split summed over `P`.
    have hdegsumP : ∑ g ∈ P, G.degree g = 16 := by
      have heq : ∑ g ∈ P, G.degree g = ∑ _g ∈ P, 4 :=
        Finset.sum_congr rfl (fun g hg => hdeg4 g (hPsubHub hg))
      rw [heq, Finset.sum_const, hPcard, smul_eq_mul]
    have hsplit3P : ∑ g ∈ P, (G.neighborFinset g ∩ Hub).card
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card + ∑ g ∈ P, (G.neighborFinset g ∩ Z).card
        = ∑ g ∈ P, G.degree g := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun g _ => nbr_split_three_eighteen G Hub Iso hdisj g)
    have hisoP : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 4 := by
      have heq : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = ∑ _g ∈ P, 1 :=
        Finset.sum_congr rfl (fun g hg => hPpoor g hg)
      rw [heq, Finset.sum_const, hPcard, smul_eq_mul, mul_one]
    have hmasseq : ∑ g ∈ P, (G.neighborFinset g ∩ P).card
        = ∑ g ∈ P, (G.neighborFinset g ∩ Hub).card := Finset.sum_congr rfl hgP_eq
    rw [hdegsumP, hisoP] at hsplit3P
    rw [hmasseq]; omega
  exact ⟨R, P, hunion.symm, hdisjRP, hr6, hPcard, hIso,
    fun h hh => hdeg4 h (hRsubHub hh), fun g hg => hdeg4 g (hPsubHub hg), hPpoor, hERP, hpoormass⟩

/-- **The rigid rich/poor partition of a no-two-hub configuration (`n = 18`, tight `e(M) = 1`).**
For both tight profiles `(9, 7, 37)` and `(10, 6, 40)`, the absence of a good two-hub pair forces
the hub set to split as `Hub = R ⊔ P` with `|R| = 6` rich hubs (iso-degree `≥ 2`, here all
degree-`4`) and `|P| = 4` poor hubs (degree-`4`, iso-degree exactly `1`), with no rich–poor hub edge
and poor-internal edge mass `≥ 10`.

The `(9, 7, 37)` profile is dispatched as vacuous (`nine_seven_vacuous_eighteen`); the `(10, 6, 40)`
profile reduces, via `all_hub_deg_four_eighteen`, to the rich/poor partition assembled in
`rich_poor_partition_assemble_eighteen`. -/
theorem no_two_hub_rigid_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hregime :
      (Hub.card = 9 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 37 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 10 ∧ Iso.card = 6 ∧ ∑ w ∈ Hub, G.degree w = 40 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11))
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) :
    ∃ R P : Finset (Fin 18), Hub = R ∪ P ∧ Disjoint R P ∧ R.card = 6 ∧ P.card = 4 ∧
      Iso.card = 6 ∧ (∀ h ∈ R, G.degree h = 4) ∧ (∀ g ∈ P, G.degree g = 4) ∧
      (∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1) ∧
      (∀ r ∈ R, ∀ g ∈ P, ¬G.Adj r g) ∧
      10 ≤ ∑ g ∈ P, (G.neighborFinset g ∩ P).card := by
  classical
  rcases hregime with ⟨hHub9, hIso7, hdsum9, hdeg3, hisodeg3, hleak, hT⟩ |
      ⟨hHub10, hIso6, hdsum10, hdeg3, hisodeg3, hleak, hT⟩
  · -- **`(9, 7, 37)` profile is vacuous.**  `nine_seven_vacuous_eighteen` consumes the `≤ 10`
    -- good-triangle form, derived from the threaded `≤ 11` hypothesis by a trivial bridge.
    have hT10 : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
        G.degree x + G.degree y + G.degree z ≤ 10 :=
      fun ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, hsum⟩ =>
        hT ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, by omega⟩
    exact absurd (nine_seven_vacuous_eighteen G Hub Iso hdeg hdeg5 hiso3 hdisj hHub9 hIso7
      hdsum9 hdeg3 hisodeg3 hleak hshare hno2hub hC4 hK23 hT10) (fun h => h)
  · -- **`(10, 6, 40)` profile: all hubs degree `4`, then the rigid partition.**
    have hdeg4 : ∀ h ∈ Hub, G.degree h = 4 :=
      all_hub_deg_four_eighteen G Hub hdeg hHub10 hdsum10
    -- The Core-1 path (`zdeg_split_sharp`, `rich_edge_ge_four`, `rich_poor_no_edge`) needs the
    -- *full* good-triangle threshold `11` (a degree-`11` triangle `{deg-4 hub, deg-4 hub, deg-3
    -- vertex}` must be excluded).  The two-hub selector chain now threads the unbridged `≤ 11`
    -- hypothesis (`hT`) all the way down, so it is supplied directly.
    exact rich_poor_partition_assemble_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub10 hIso6
      hisodeg3 hdeg3 hdsum10 hleak hshare hno2hub hC4 hK23 hT

end N18

end ACMax
