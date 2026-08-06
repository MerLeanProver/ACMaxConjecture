import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.HubTriangleStruct

/-!
# `|FF|`-dispatch triangle forcing for the `n = 17`, `e(M) = 3`, `|D| = 8` hub-triangle corner

This file closes the genuinely new `n = 17` obligation `core_triangle_force_seventeen` by a
case-split on the fully-free hub count `|FF| ∈ {2, 3, 4, 5, 6}` (from `active_hub_budget_seventeen`).

The driving new ingredient (the `n = 17` analogue of the `n = 16` share argument) is the
*isolated-twin incidence bound*: from `hA` (no `M`-isolated twin has two hub-neighbours both
avoiding a common cherry) each twin has at most one neighbour in each avoider set `A1`, `A2`, so
`∑_{A1} iso ≤ 4` and `∑_{A2} iso ≤ 4` (`iso_incidence_le_four`).  Combined with the iso total
`∑_{Dᶜ} iso = 12` this forces a large iso-mass on the inactive hubs `B = Dᶜ \ (A1 ∪ A2)`:
`∑_B iso ≥ 4 + ∑_{FF} iso`.

* `|FF| = 6`: `∑_{FF} iso ≤ 4` and `iso + int = 4` per fully-free hub force `∑_{FF} int ≥ 20 > 18`,
  impossible.  (Pure counting — no `K_{3,3}` analysis needed.)
* `|FF| = 2`: the budget forces `|B| = 1`, so `∑_B iso = iso(h) ≤ 3 < 4`, impossible.
* `|FF| = 3`: the budget forces `|B| = 2` with `∑_B iso ≥ 6`, so both inactive hubs carry `iso = 3`,
  hence `int = 0`; being non-adjacent they share `≥ 2` twins, contradicting
  `nonadj_hubs_share_le_one_iso` (share `≤ 1`).
* `|FF| ∈ {4, 5}`: the extremal fully-free corners.  `|FF| = 4` splits on `∑_FF int ∈ {12, 13, 14}`
  (`12`: two iso-`3` non-adjacent inactive hubs via `inactive_iso8_false`; `13`: a `TwoHubConfig`
  via `ff3_extract_twohub_seventeen`; `14`: a Mantel-`4` triangle via `mantel_four_triangle`).
  `|FF| = 5` (`|B| = 4`, `A1 = A2 = FF`) forces `∑_FF int ≥ 16`, hence `∑_FF(N ∩ FF) ≥ 14`, a
  Mantel-`5` triangle via `mantel_five_triangle`.  Both Mantel triangles lie in `A2`, contradicting
  `htri2`.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Isolated-twin incidence bound.**  If every `M`-isolated twin has at most one neighbour in a
hub set `A`, then the total iso-incidence over `A` is at most `|Iso| = 4`. -/
theorem iso_incidence_le_four (G : SimpleGraph (Fin 17)) (Iso A : Finset (Fin 17))
    (hIso4 : Iso.card = 4)
    (hbound : ∀ t ∈ Iso, (G.neighborFinset t ∩ A).card ≤ 1) :
    (∑ g ∈ A, (G.neighborFinset g ∩ Iso).card) ≤ 4 := by
  classical
  rw [cross_count G A Iso]
  calc (∑ t ∈ Iso, (G.neighborFinset t ∩ A).card)
      ≤ ∑ _t ∈ Iso, 1 := Finset.sum_le_sum hbound
    _ = Iso.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    _ = 4 := hIso4

/-- **Two non-adjacent iso-`3` hubs are impossible.**  Two distinct non-adjacent degree-`4` hubs
each with all three `M`-isolated twins as neighbours would share `≥ 2` twins (as `|Iso| = 4`),
contradicting the good-`C₄` share bound `nonadj_hubs_share_le_one_iso`. -/
theorem two_iso3_nonadj_false (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4) (hIso4 : Iso.card = 4)
    (h₁ h₂ : Fin 17) (hh1Dc : h₁ ∈ Dᶜ) (hh2Dc : h₂ ∈ Dᶜ) (hh12 : h₁ ≠ h₂)
    (hnadj : ¬G.Adj h₁ h₂)
    (hiso1 : (G.neighborFinset h₁ ∩ Iso).card = 3)
    (hiso2 : (G.neighborFinset h₂ ∩ Iso).card = 3) :
    False := by
  classical
  have hshare := nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4
    h₁ h₂ hh1Dc hh2Dc hh12 hnadj
  have hsub1 : G.neighborFinset h₁ ∩ Iso ⊆ Iso := Finset.inter_subset_right
  have hsub2 : G.neighborFinset h₂ ∩ Iso ⊆ Iso := Finset.inter_subset_right
  have hunion_le : ((G.neighborFinset h₁ ∩ Iso) ∪ (G.neighborFinset h₂ ∩ Iso)).card ≤ 4 := by
    calc ((G.neighborFinset h₁ ∩ Iso) ∪ (G.neighborFinset h₂ ∩ Iso)).card
        ≤ Iso.card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
      _ = 4 := hIso4
  have hincl := Finset.card_union_add_card_inter
    (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂ ∩ Iso)
  have hinter_eq : (G.neighborFinset h₁ ∩ Iso) ∩ (G.neighborFinset h₂ ∩ Iso)
      = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
    rw [Finset.inter_inter_inter_comm, Finset.inter_self]
  rw [hiso1, hiso2, hinter_eq] at hincl
  omega

/-- **Fully-free internal-edge lower bound.**  For `FF ⊆ Dᶜ` with total `Dᶜ`-internal degree `18`,
the in-`FF` edge mass is `∑_{FF}(N ∩ FF) ≥ 2·∑_{FF}(N ∩ Dᶜ) − 18` (the leak out of `FF` is bounded
by the residual `Dᶜ`-internal degree `18 − ∑_{FF}(N ∩ Dᶜ)` via the bipartite cross count). -/
theorem ff_internal_edge_lb (G : SimpleGraph (Fin 17)) (Dc FF : Finset (Fin 17))
    (hFFsub : FF ⊆ Dc)
    (hSum : ∑ w ∈ Dc, (G.neighborFinset w ∩ Dc).card = 18) :
    2 * (∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card)
      ≤ (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) + 18 := by
  classical
  have hsplit : ∀ g : Fin 17, (G.neighborFinset g ∩ Dc).card
      = (G.neighborFinset g ∩ FF).card + (G.neighborFinset g ∩ (Dc \ FF)).card := by
    intro g
    rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
      Finset.union_sdiff_of_subset hFFsub]
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    rw [Finset.mem_inter] at ha ha'
    exact (Finset.mem_sdiff.mp ha'.2).2 ha.2
  have hsdiff : (∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ Dc).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card = 18 := by
    rw [Finset.sum_sdiff hFFsub, hSum]
  have hcross : ∑ g ∈ FF, (G.neighborFinset g ∩ (Dc \ FF)).card
      = ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ FF).card :=
    cross_count G FF (Dc \ FF)
  have hleak_le : ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ FF).card
      ≤ ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ Dc).card := by
    apply Finset.sum_le_sum
    intro w _
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hFFsub)
  have hFFFFsum : (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ (Dc \ FF)).card
      = ∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun g _ => (hsplit g).symm)
  omega

/-- **Degree-sum Mantel bound.**  If `FF` contains no triangle and `v ∈ FF`, then the in-`FF` edge
mass is bounded by the star/leak count around `v`: with `k = |N v ∩ FF|`, the neighbourhood of `v`
is independent (else a triangle), pinning `∑_{FF}(N ∩ FF) ≤ k + k·(|FF| − k) + (|FF| − 1 − k)·
(|FF| − 1)`. -/
theorem mantel_bound (G : SimpleGraph (Fin 17)) (FF : Finset (Fin 17)) (v : Fin 17)
    (hvFF : v ∈ FF)
    (htri : ¬∃ a b c : Fin 17, a ∈ FF ∧ b ∈ FF ∧ c ∈ FF ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) :
    (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card)
      ≤ (G.neighborFinset v ∩ FF).card
        + (G.neighborFinset v ∩ FF).card * (FF.card - (G.neighborFinset v ∩ FF).card)
        + (FF.card - 1 - (G.neighborFinset v ∩ FF).card) * (FF.card - 1) := by
  classical
  set N := G.neighborFinset v ∩ FF with hNdef
  have hNsubFF : N ⊆ FF := Finset.inter_subset_right
  have hvnotN : v ∉ N := by
    rw [hNdef, Finset.mem_inter, G.mem_neighborFinset]
    exact fun h => G.irrefl h.1
  have hivNsub : insert v N ⊆ FF := Finset.insert_subset hvFF hNsubFF
  have hivNcard : (insert v N).card = N.card + 1 := by
    rw [Finset.card_insert_of_notMem hvnotN]
  have hNlt : N.card + 1 ≤ FF.card := by
    have := Finset.card_le_card hivNsub; rwa [hivNcard] at this
  have hRcard : (FF \ insert v N).card = FF.card - 1 - N.card := by
    have := Finset.card_sdiff_add_card_eq_card hivNsub
    rw [hivNcard] at this; omega
  have hpart : (∑ g ∈ FF \ insert v N, (G.neighborFinset g ∩ FF).card)
      + ∑ g ∈ insert v N, (G.neighborFinset g ∩ FF).card
      = ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card := Finset.sum_sdiff hivNsub
  have hinsert : (∑ g ∈ insert v N, (G.neighborFinset g ∩ FF).card)
      = N.card + ∑ g ∈ N, (G.neighborFinset g ∩ FF).card := by
    rw [Finset.sum_insert hvnotN, ← hNdef]
  have hfle : ∀ g ∈ FF, (G.neighborFinset g ∩ FF).card ≤ FF.card - 1 := by
    intro g hg
    have hsub : G.neighborFinset g ∩ FF ⊆ FF.erase g := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem hg] at this
  have hNbd : ∀ g ∈ N, (G.neighborFinset g ∩ FF).card ≤ FF.card - N.card := by
    intro g hg
    have hgFF : g ∈ FF := hNsubFF hg
    have hgadjv : G.Adj v g := by
      rw [hNdef, Finset.mem_inter, G.mem_neighborFinset] at hg; exact hg.1
    have hsub : G.neighborFinset g ∩ FF ⊆ insert v (FF \ insert v N) := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      obtain ⟨hxadj, hxFF⟩ := hx
      by_cases hxv : x = v
      · subst hxv; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        rw [Finset.mem_sdiff]
        refine ⟨hxFF, ?_⟩
        intro hxin
        rw [Finset.mem_insert] at hxin
        rcases hxin with rfl | hxN
        · exact hxv rfl
        · have hvx : G.Adj v x := by
            rw [hNdef, Finset.mem_inter, G.mem_neighborFinset] at hxN; exact hxN.1
          exact htri ⟨v, g, x, hvFF, hgFF, hxFF, hgadjv, hvx, hxadj⟩
    calc (G.neighborFinset g ∩ FF).card
        ≤ (insert v (FF \ insert v N)).card := Finset.card_le_card hsub
      _ ≤ (FF \ insert v N).card + 1 := Finset.card_insert_le _ _
      _ = (FF.card - 1 - N.card) + 1 := by rw [hRcard]
      _ = FF.card - N.card := by omega
  have hsumN : (∑ g ∈ N, (G.neighborFinset g ∩ FF).card) ≤ N.card * (FF.card - N.card) := by
    calc (∑ g ∈ N, (G.neighborFinset g ∩ FF).card)
        ≤ ∑ _g ∈ N, (FF.card - N.card) := Finset.sum_le_sum hNbd
      _ = N.card * (FF.card - N.card) := by rw [Finset.sum_const, smul_eq_mul]
  have hsumR : (∑ g ∈ FF \ insert v N, (G.neighborFinset g ∩ FF).card)
      ≤ (FF.card - 1 - N.card) * (FF.card - 1) := by
    have hRsubFF : FF \ insert v N ⊆ FF := Finset.sdiff_subset
    calc (∑ g ∈ FF \ insert v N, (G.neighborFinset g ∩ FF).card)
        ≤ ∑ _g ∈ FF \ insert v N, (FF.card - 1) :=
          Finset.sum_le_sum (fun g hg => hfle g (hRsubFF hg))
      _ = (FF \ insert v N).card * (FF.card - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ = (FF.card - 1 - N.card) * (FF.card - 1) := by rw [hRcard]
  omega

/-- **Mantel triangle on four fully-free hubs.**  A `4`-vertex set with in-set edge mass
`∑(N ∩ FF) ≥ 10 > 2·⌊16/4⌋` contains a triangle. -/
theorem mantel_four_triangle (G : SimpleGraph (Fin 17)) (FF : Finset (Fin 17))
    (hcard : FF.card = 4)
    (hedge : 10 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) :
    ∃ a b c : Fin 17, a ∈ FF ∧ b ∈ FF ∧ c ∈ FF ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  by_contra htri
  obtain ⟨v, hvFF, hvk⟩ : ∃ v ∈ FF, 3 ≤ (G.neighborFinset v ∩ FF).card := by
    by_contra hcon
    push Not at hcon
    have hb : (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) ≤ ∑ _g ∈ FF, 2 :=
      Finset.sum_le_sum (fun g hg => by have := hcon g hg; omega)
    rw [Finset.sum_const, hcard, smul_eq_mul] at hb
    omega
  have hkle : (G.neighborFinset v ∩ FF).card ≤ FF.card - 1 := by
    have hsub : G.neighborFinset v ∩ FF ⊆ FF.erase v := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem hvFF] at this
  have hbound := mantel_bound G FF v hvFF htri
  rw [hcard] at hbound hkle
  set k := (G.neighborFinset v ∩ FF).card with hk
  interval_cases k
  omega

/-- **Mantel triangle on five fully-free hubs.**  A `5`-vertex set with in-set edge mass
`∑(N ∩ FF) ≥ 14 > 2·⌊25/4⌋` contains a triangle. -/
theorem mantel_five_triangle (G : SimpleGraph (Fin 17)) (FF : Finset (Fin 17))
    (hcard : FF.card = 5)
    (hedge : 14 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) :
    ∃ a b c : Fin 17, a ∈ FF ∧ b ∈ FF ∧ c ∈ FF ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  by_contra htri
  obtain ⟨v, hvFF, hvk⟩ : ∃ v ∈ FF, 3 ≤ (G.neighborFinset v ∩ FF).card := by
    by_contra hcon
    push Not at hcon
    have hb : (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) ≤ ∑ _g ∈ FF, 2 :=
      Finset.sum_le_sum (fun g hg => by have := hcon g hg; omega)
    rw [Finset.sum_const, hcard, smul_eq_mul] at hb
    omega
  have hkle : (G.neighborFinset v ∩ FF).card ≤ FF.card - 1 := by
    have hsub : G.neighborFinset v ∩ FF ⊆ FF.erase v := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem hvFF] at this
  have hbound := mantel_bound G FF v hvFF htri
  rw [hcard] at hbound hkle
  set k := (G.neighborFinset v ∩ FF).card with hk
  interval_cases k <;> omega

/-- **Three inactive hubs with iso-mass `≥ 8` ⇒ contradiction.**  If `|B| = 3` inactive hubs (each
touching a cherry, so `path ≥ 1`) carry total iso-incidence `≥ 8`, two of them carry the maximal
`iso = 3`, hence `int = 0` (internally isolated) and so are non-adjacent — a `two_iso3_nonadj_false`
contradiction. -/
theorem inactive_iso8_false (G : SimpleGraph (Fin 17)) (D Iso B P : Finset (Fin 17))
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4) (hIso4 : Iso.card = 4)
    (hBsub : B ⊆ Dᶜ) (hBcard : B.card = 3)
    (hper : ∀ g : Fin 17, g ∈ Dᶜ →
      (G.neighborFinset g ∩ P).card + (G.neighborFinset g ∩ Iso).card
        + (G.neighborFinset g ∩ Dᶜ).card = 4)
    (hpath1 : ∀ h : Fin 17, h ∈ B → 1 ≤ (G.neighborFinset h ∩ P).card)
    (hisoB8 : 8 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card) :
    False := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, hBeq⟩ := Finset.card_eq_three.mp hBcard
  have hxB : x ∈ B := by rw [hBeq]; simp
  have hyB : y ∈ B := by rw [hBeq]; simp
  have hzB : z ∈ B := by rw [hBeq]; simp
  have hxDc : x ∈ Dᶜ := hBsub hxB
  have hyDc : y ∈ Dᶜ := hBsub hyB
  have hzDc : z ∈ Dᶜ := hBsub hzB
  have hint0 : ∀ u : Fin 17, u ∈ B → (G.neighborFinset u ∩ Iso).card = 3 →
      (G.neighborFinset u ∩ Dᶜ).card = 0 := by
    intro u huB hu3
    have hp := hper u (hBsub huB)
    have hpa := hpath1 u huB
    omega
  have hnadj : ∀ u w : Fin 17, w ∈ Dᶜ → (G.neighborFinset u ∩ Dᶜ).card = 0 →
      ¬G.Adj u w := by
    intro u w hwDc hu0 hadj
    have hmem : w ∈ G.neighborFinset u ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hwDc⟩
    rw [Finset.card_eq_zero] at hu0
    rw [hu0] at hmem; exact (Finset.notMem_empty _) hmem
  have hisox3 : (G.neighborFinset x ∩ Iso).card ≤ 3 := by
    have hp := hper x hxDc; have hpa := hpath1 x hxB; omega
  have hisoy3 : (G.neighborFinset y ∩ Iso).card ≤ 3 := by
    have hp := hper y hyDc; have hpa := hpath1 y hyB; omega
  have hisoz3 : (G.neighborFinset z ∩ Iso).card ≤ 3 := by
    have hp := hper z hzDc; have hpa := hpath1 z hzB; omega
  have hisosum3 : (G.neighborFinset x ∩ Iso).card + (G.neighborFinset y ∩ Iso).card
      + (G.neighborFinset z ∩ Iso).card = ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by
    rw [hBeq, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, add_assoc]
  have hpair : ((G.neighborFinset x ∩ Iso).card = 3 ∧ (G.neighborFinset y ∩ Iso).card = 3)
      ∨ ((G.neighborFinset x ∩ Iso).card = 3 ∧ (G.neighborFinset z ∩ Iso).card = 3)
      ∨ ((G.neighborFinset y ∩ Iso).card = 3 ∧ (G.neighborFinset z ∩ Iso).card = 3) := by
    omega
  rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact two_iso3_nonadj_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso4 x y hxDc hyDc hxy
      (hnadj x y hyDc (hint0 x hxB e1)) e1 e2
  · exact two_iso3_nonadj_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso4 x z hxDc hzDc hxz
      (hnadj x z hzDc (hint0 x hxB e1)) e1 e2
  · exact two_iso3_nonadj_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso4 y z hyDc hzDc hyz
      (hnadj y z hzDc (hint0 y hyB e1)) e1 e2

/-- **`|FF| = 4`, `∑_FF int = 13` ⇒ `TwoHubConfig` (hence contradiction).**  Port of the `n = 16`
`ff3_extract_twohub`: from the budget-tight inactive-hub data (`|B| = 3`, `∑_B int ≤ 1`,
`∑_B iso ≥ 7`), construct a `TwoHubConfig G`, contradicting `¬TwoHubConfig`. -/
theorem ff3_extract_twohub_seventeen (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (L₁ c₁ c₂ L₂ : Fin 17) (B : Finset (Fin 17))
    (hth : ¬TwoHubConfig G)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4)
    (hDdeg3 : ∀ v : Fin 17, v ∈ D → G.degree v = 3)
    (hDeq : ({L₁, c₁, c₂, L₂} : Finset (Fin 17)) ∪ Iso = D)
    (hBsub : B ⊆ Dᶜ) (hBcard : B.card = 3)
    (hBint1 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) ≤ 1)
    (hBiso7 : 7 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card)
    (hper : ∀ g : Fin 17, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4)
    (hpath1 : ∀ h : Fin 17, h ∈ B →
      1 ≤ (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))).card) :
    False := by
  classical
  set P : Finset (Fin 17) := {L₁, c₁, c₂, L₂} with hPdef
  have hisole3 : ∀ h ∈ B, (G.neighborFinset h ∩ Iso).card ≤ 3 := by
    intro h hh
    have hp := hper h (hBsub hh)
    have hpa := hpath1 h hh
    omega
  have hex1 : ∃ h ∈ B, (G.neighborFinset h ∩ Iso).card = 3 := by
    by_contra hcon
    push Not at hcon
    have hle2 : ∀ h ∈ B, (G.neighborFinset h ∩ Iso).card ≤ 2 := by
      intro h hh
      have h3 := hisole3 h hh
      have hne := hcon h hh
      omega
    have hsum := Finset.sum_le_sum hle2
    rw [Finset.sum_const, hBcard, smul_eq_mul] at hsum
    omega
  obtain ⟨h₁, hh1B, hiso1⟩ := hex1
  have hh1Dc : h₁ ∈ Dᶜ := hBsub hh1B
  have hp1 := hper h₁ hh1Dc
  have hpa1 := hpath1 h₁ hh1B
  have hint1_eq : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by omega
  have hpath1_eq : (G.neighborFinset h₁ ∩ P).card = 1 := by omega
  have hex2 : ∃ h ∈ B.erase h₁, (G.neighborFinset h ∩ Dᶜ).card = 0 := by
    by_contra hcon
    push Not at hcon
    have hge : ∀ h ∈ B.erase h₁, 1 ≤ (G.neighborFinset h ∩ Dᶜ).card :=
      fun h hh => Nat.one_le_iff_ne_zero.mpr (hcon h hh)
    have hsub : B.erase h₁ ⊆ B := Finset.erase_subset _ _
    have hsumge : (B.erase h₁).card
        ≤ ∑ g ∈ B.erase h₁, (G.neighborFinset g ∩ Dᶜ).card := by
      calc (B.erase h₁).card = ∑ _g ∈ B.erase h₁, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum hge
    have hcarderase : (B.erase h₁).card = 2 := by
      rw [Finset.card_erase_of_mem hh1B, hBcard]
    have hsumle : ∑ g ∈ B.erase h₁, (G.neighborFinset g ∩ Dᶜ).card
        ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card :=
      Finset.sum_le_sum_of_subset hsub
    omega
  obtain ⟨h₂, hh2erase, hint2⟩ := hex2
  have hh2B : h₂ ∈ B := Finset.mem_of_mem_erase hh2erase
  have hh12 : h₁ ≠ h₂ := (Finset.ne_of_mem_erase hh2erase).symm
  have hh2Dc : h₂ ∈ Dᶜ := hBsub hh2B
  have hnadj : ¬G.Adj h₁ h₂ := by
    intro hadj
    have hmem : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh2Dc⟩
    rw [Finset.card_eq_zero] at hint1_eq
    rw [hint1_eq] at hmem
    exact (Finset.notMem_empty _) hmem
  have hshare := nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4
    h₁ h₂ hh1Dc hh2Dc hh12 hnadj
  have hh1notD : h₁ ∉ D := Finset.mem_compl.mp hh1Dc
  have hh2notD : h₂ ∉ D := Finset.mem_compl.mp hh2Dc
  have hT1part := Finset.card_sdiff_add_card_inter
    (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂)
  have hT1int : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
      = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [hT1int, hiso1] at hT1part
  have hT1card : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card := by omega
  obtain ⟨a, haT, b, hbT, hab⟩ := Finset.one_lt_card.mp (by omega : 1 <
    ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card)
  have ha_props := Finset.mem_sdiff.mp haT
  have haNI := Finset.mem_inter.mp ha_props.1
  have haNh1 : G.Adj h₁ a := (G.mem_neighborFinset _ _).mp haNI.1
  have haIso : a ∈ Iso := haNI.2
  have ha_nadj_h2 : ¬G.Adj h₂ a :=
    fun hadj => ha_props.2 ((G.mem_neighborFinset _ _).mpr hadj)
  have hb_props := Finset.mem_sdiff.mp hbT
  have hbNI := Finset.mem_inter.mp hb_props.1
  have hbNh1 : G.Adj h₁ b := (G.mem_neighborFinset _ _).mp hbNI.1
  have hbIso : b ∈ Iso := hbNI.2
  have hb_nadj_h2 : ¬G.Adj h₂ b :=
    fun hadj => hb_props.2 ((G.mem_neighborFinset _ _).mpr hadj)
  have hN2D : G.neighborFinset h₂ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₂ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [Finset.card_eq_zero] at hint2
    rw [hint2] at hmem
    exact (Finset.notMem_empty _) hmem
  have hScard : (G.neighborFinset h₂ ∩ G.neighborFinset h₁).card ≤ 2 := by
    have hSsubD : G.neighborFinset h₂ ∩ G.neighborFinset h₁ ⊆ D :=
      (Finset.inter_subset_left).trans hN2D
    have hSsubPI : G.neighborFinset h₂ ∩ G.neighborFinset h₁ ⊆ P ∪ Iso := by
      rw [hPdef, hDeq]; exact hSsubD
    have hdecomp : G.neighborFinset h₂ ∩ G.neighborFinset h₁
        = ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P)
          ∪ ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso) := by
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hSsubPI]
    have hle := Finset.card_union_le
      ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P)
      ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso)
    have hpathpart : ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P).card ≤ 1 := by
      have hsub : (G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P
          ⊆ G.neighborFinset h₁ ∩ P := by
        intro x hx
        rw [Finset.mem_inter] at hx ⊢
        exact ⟨(Finset.mem_inter.mp hx.1).2, hx.2⟩
      calc ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P).card
          ≤ (G.neighborFinset h₁ ∩ P).card := Finset.card_le_card hsub
        _ = 1 := hpath1_eq
    have hisopart : ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso).card ≤ 1 := by
      have heq : (G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso
          = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
        rw [Finset.inter_comm (G.neighborFinset h₂) (G.neighborFinset h₁)]
      rw [heq]; exact hshare
    rw [hdecomp]; omega
  have hN2card : (G.neighborFinset h₂).card = 4 := by
    rw [G.card_neighborFinset_eq_degree]; exact hdeg4 h₂ hh2Dc
  have hC2part := Finset.card_sdiff_add_card_inter
    (G.neighborFinset h₂) (G.neighborFinset h₁)
  rw [hN2card] at hC2part
  have hC2card : 2 ≤ (G.neighborFinset h₂ \ G.neighborFinset h₁).card := by omega
  obtain ⟨c, hcC, d, hdC, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 <
    (G.neighborFinset h₂ \ G.neighborFinset h₁).card)
  have hc_props := Finset.mem_sdiff.mp hcC
  have hcNh2 : G.Adj h₂ c := (G.mem_neighborFinset _ _).mp hc_props.1
  have hcnh1 : c ∉ G.neighborFinset h₁ := hc_props.2
  have hc_nadj_h1 : ¬G.Adj h₁ c :=
    fun hadj => hcnh1 ((G.mem_neighborFinset _ _).mpr hadj)
  have hcD : c ∈ D := hN2D hc_props.1
  have hcdeg : G.degree c = 3 := hDdeg3 c hcD
  have hd_props := Finset.mem_sdiff.mp hdC
  have hdNh2 : G.Adj h₂ d := (G.mem_neighborFinset _ _).mp hd_props.1
  have hdnh1 : d ∉ G.neighborFinset h₁ := hd_props.2
  have hd_nadj_h1 : ¬G.Adj h₁ d :=
    fun hadj => hdnh1 ((G.mem_neighborFinset _ _).mpr hadj)
  have hdD : d ∈ D := hN2D hd_props.1
  have hddeg : G.degree d = 3 := hDdeg3 d hdD
  have hadeg : G.degree a = 3 := (hIsoprop a haIso).1
  have hbdeg : G.degree b = 3 := (hIsoprop b hbIso).1
  have ha_nadj_c : ¬G.Adj a c := fun hadj => (hIsoprop a haIso).2 c hadj hcdeg
  have ha_nadj_d : ¬G.Adj a d := fun hadj => (hIsoprop a haIso).2 d hadj hddeg
  have hb_nadj_c : ¬G.Adj b c := fun hadj => (hIsoprop b hbIso).2 c hadj hcdeg
  have hb_nadj_d : ¬G.Adj b d := fun hadj => (hIsoprop b hbIso).2 d hadj hddeg
  have haD : a ∈ D := hIsoD haIso
  have hbD : b ∈ D := hIsoD hbIso
  have haNh1mem : a ∈ G.neighborFinset h₁ := (G.mem_neighborFinset _ _).mpr haNh1
  have hbNh1mem : b ∈ G.neighborFinset h₁ := (G.mem_neighborFinset _ _).mpr hbNh1
  exact hth ⟨h₁, h₂, a, b, c, d,
    hdeg4 h₁ hh1Dc, hdeg4 h₂ hh2Dc, hadeg, hbdeg, hcdeg, hddeg,
    haNh1.symm, hbNh1.symm, hcNh2.symm, hdNh2.symm,
    hnadj, hc_nadj_h1, hd_nadj_h1,
    (fun hadj => ha_nadj_h2 hadj.symm), ha_nadj_c, ha_nadj_d,
    (fun hadj => hb_nadj_h2 hadj.symm), hb_nadj_c, hb_nadj_d,
    hh12,
    (fun e => hh1notD (e ▸ haD)), (fun e => hh1notD (e ▸ hbD)),
    (fun e => hh1notD (e ▸ hcD)), (fun e => hh1notD (e ▸ hdD)),
    (fun e => hh2notD (e ▸ haD)), (fun e => hh2notD (e ▸ hbD)),
    (fun e => hh2notD (e ▸ hcD)), (fun e => hh2notD (e ▸ hdD)),
    hab, (fun e => hcnh1 (e ▸ haNh1mem)), (fun e => hdnh1 (e ▸ haNh1mem)),
    (fun e => hcnh1 (e ▸ hbNh1mem)), (fun e => hdnh1 (e ▸ hbNh1mem)), hcd⟩

/-- **No avoider triangle ⇒ contradiction (the `n = 17` `|FF|`-dispatch core).**  Full replacement
for `core_triangle_force_seventeen`: dispatches on `|FF| ∈ {2, 3, 4, 5, 6}`, closing `|FF| = 2`,
`|FF| = 3` and `|FF| = 6` by the isolated-twin incidence / share counting, and `|FF| ∈ {4, 5}` by
the extremal-corner analysis (`∑_FF int` case-split, `TwoHubConfig` extraction, and Mantel-`4`/`5`
triangles inside `FF ⊆ A2` contradicting `htri2`). -/
theorem iso_rich_force_seventeen (G : SimpleGraph (Fin 17))
    (D Iso : Finset (Fin 17)) (L₁ c₁ c₂ L₂ : Fin 17)
    (_hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 17, ({a, b, c, d, e} : Finset (Fin 17)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (_hcov : ∀ p q : Fin 17, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (_hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (_hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (_hc1deg : G.degree c₁ = 3) (_hc2deg : G.degree c₂ = 3)
    (_hL1deg : G.degree L₁ = 3) (_hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (_hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4)
    (_hD8 : D.card = 8) (_hth : ¬TwoHubConfig G)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hW : ∀ g : Fin 17, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hA : ∀ t : Fin 17, t ∈ Iso → ∀ p q : Fin 17, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q c₂) ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)))
    (hDc9 : Dᶜ.card = 9) (hIso4 : Iso.card = 4)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hSum18 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 18)
    (_htri1 : ¬∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂))
    (_htri2 : ¬∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)) :
    False := by
  classical
  -- Path / Iso partition of `D`.
  obtain ⟨hDeq, _hdisj⟩ :=
    path_iso_partition G D Iso L₁ c₁ c₂ L₂ hIsodef hisochar hL1D hc1D hc2D hL2D hac1L1 hc12 hac2L2
  have hclassP : ∀ x : Fin 17, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    rw [← hDeq] at hx
    rcases Finset.mem_union.mp hx with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h; tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  -- The two cherry-avoider sets and `FF = A1 ∩ A2`.
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
  -- Each cherry has `≥ 5` avoiders.
  obtain ⟨hA1card, hA2card⟩ :=
    cherry_avoiders_ge_five G D L₁ c₁ c₂ L₂ hDc9 hcard_c1 hcard_c2 hcard_L1 hcard_L2
  rw [← hA1def] at hA1card
  rw [← hA2def] at hA2card
  -- Inclusion–exclusion budget: `|FF| ∈ {2, 3, 4, 5, 6}`.
  obtain ⟨hFFlb, hFFub⟩ :=
    active_hub_budget_seventeen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card)
      hA1sub hA2sub hFFdef hA1card hA2card hA1int hA2int hFFint hSum18
  -- Residual incidence sums (path / iso totals and the per-hub split).
  obtain ⟨_hsumP, hsumI, hper⟩ :=
    residual_incidence_sums G D Iso L₁ c₁ c₂ L₂ hIsodef hIsoprop hisochar hL1D hc1D hc2D hL2D
      hac1L1 hc12 hac2L2 hnc1L2 hdeg4 hcard_c1 hcard_c2 hcard_L1 hcard_L2 hIso4 hL1nc2 hL2nc1
  -- The inactive hubs `B = Dᶜ \ (A1 ∪ A2)` and the internal-degree budget.
  set B := Dᶜ \ (A1 ∪ A2) with hBdef
  have hUsub : A1 ∪ A2 ⊆ Dᶜ := Finset.union_subset hA1sub hA2sub
  have hBpart : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card)
      + ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Dᶜ).card = 18 := by
    rw [hBdef, Finset.sum_sdiff hUsub, hSum18]
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := Finset.union_sdiff_self_eq_union
  have hABsplit : (∑ g ∈ A1, (G.neighborFinset g ∩ Dᶜ).card)
      + ∑ g ∈ A2 \ A1, (G.neighborFinset g ∩ Dᶜ).card
      = ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Dᶜ).card := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  have hA1split : (∑ g ∈ A1 \ FF, (G.neighborFinset g ∩ Dᶜ).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card
      = ∑ g ∈ A1, (G.neighborFinset g ∩ Dᶜ).card := Finset.sum_sdiff hFFsubA1
  have hFFsum_ge : 3 * FF.card ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card := by
    have := Finset.card_nsmul_le_sum FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA1mf_ge : 2 * (A1 \ FF).card
      ≤ ∑ g ∈ A1 \ FF, (G.neighborFinset g ∩ Dᶜ).card := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) (fun g => (G.neighborFinset g ∩ Dᶜ).card) 2
      (fun g hg => hA1int g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA2mA1_ge : 2 * (A2 \ A1).card
      ≤ ∑ g ∈ A2 \ A1, (G.neighborFinset g ∩ Dᶜ).card := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) (fun g => (G.neighborFinset g ∩ Dᶜ).card) 2
      (fun g hg => hA2int g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA1FFinter : (A1 ∩ FF).card = FF.card := by
    rw [Finset.inter_eq_right.mpr hFFsubA1]
  have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
    rw [← hA1FFinter]; exact Finset.card_sdiff_add_card_inter A1 FF
  have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFFdef, Finset.inter_comm]
  have hA2mA1card : (A2 \ A1).card + FF.card = A2.card := by
    rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
  have hUcard : (A1 ∪ A2).card + FF.card = A1.card + A2.card := by
    rw [hFFdef]; exact Finset.card_union_add_card_inter A1 A2
  have hBcard_eq : B.card + (A1 ∪ A2).card = Dᶜ.card := by
    rw [hBdef, Finset.card_sdiff_add_card, Finset.union_eq_left.mpr hUsub]
  -- Iso-incidence facts: each twin has `≤ 1` neighbour in `A1` and in `A2`.
  have hisoA1bd : ∀ t ∈ Iso, (G.neighborFinset t ∩ A1).card ≤ 1 := by
    intro t htIso
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
    rw [Finset.mem_inter, G.mem_neighborFinset] at hp hq
    obtain ⟨htp, hpA1⟩ := hp
    obtain ⟨htq, hqA1⟩ := hq
    rw [hA1def, Finset.mem_filter] at hpA1 hqA1
    obtain ⟨_, hpL1, hpc1, hpc2⟩ := hpA1
    obtain ⟨_, hqL1, hqc1, hqc2⟩ := hqA1
    exact hA t htIso p q hpq htp htq (Or.inl ⟨hpL1, hpc1, hpc2, hqL1, hqc1, hqc2⟩)
  have hisoA2bd : ∀ t ∈ Iso, (G.neighborFinset t ∩ A2).card ≤ 1 := by
    intro t htIso
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
    rw [Finset.mem_inter, G.mem_neighborFinset] at hp hq
    obtain ⟨htp, hpA2⟩ := hp
    obtain ⟨htq, hqA2⟩ := hq
    rw [hA2def, Finset.mem_filter] at hpA2 hqA2
    obtain ⟨_, hpc1, hpc2, hpL2⟩ := hpA2
    obtain ⟨_, hqc1, hqc2, hqL2⟩ := hqA2
    exact hA t htIso p q hpq htp htq (Or.inr ⟨hpc1, hpc2, hpL2, hqc1, hqc2, hqL2⟩)
  have hisoA1le : (∑ g ∈ A1, (G.neighborFinset g ∩ Iso).card) ≤ 4 :=
    iso_incidence_le_four G Iso A1 hIso4 hisoA1bd
  have hisoA2le : (∑ g ∈ A2, (G.neighborFinset g ∩ Iso).card) ≤ 4 :=
    iso_incidence_le_four G Iso A2 hIso4 hisoA2bd
  -- Iso-mass redistribution: `∑_B iso ≥ 4 + ∑_FF iso`.
  have hIsoUnionInter : (∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Iso).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card
      = (∑ g ∈ A1, (G.neighborFinset g ∩ Iso).card)
        + ∑ g ∈ A2, (G.neighborFinset g ∩ Iso).card := by
    rw [hFFdef]; exact Finset.sum_union_inter
  have hIsoBpart : (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card)
      + ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Iso).card = 12 := by
    rw [hBdef, Finset.sum_sdiff hUsub, hsumI]
  -- Fully-free path-freeness: `path(g) = 0`, so `iso(g) + int(g) = 4` summed over `FF`.
  have hFFpath0 : ∀ g ∈ FF,
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))).card = 0 := by
    intro g hg
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hgA1
    obtain ⟨_, _, _, hgL2⟩ := hgA2
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact hgL1 hadj
    · exact hgc1 hadj
    · exact hgc2 hadj
    · exact hgL2 hadj
  have hFFsum4 : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card = 4 * FF.card := by
    have hcongr : ∀ g ∈ FF, (G.neighborFinset g ∩ Iso).card
        + (G.neighborFinset g ∩ Dᶜ).card = 4 := by
      intro g hg
      have hp := hper g (hFFsub hg)
      have h0 := hFFpath0 g hg
      omega
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  have hintFFle : (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) ≤ 18 := by
    rw [← hSum18]
    exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  -- Each inactive hub touches a cherry (`path ≥ 1`), hence carries `iso ≤ 3`.
  have hpath1 : ∀ h ∈ B,
      1 ≤ (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))).card := by
    intro h hh
    rw [hBdef, Finset.mem_sdiff] at hh
    obtain ⟨hhDc, hhU⟩ := hh
    have hhA1 : h ∉ A1 := fun hmem => hhU (Finset.mem_union_left _ hmem)
    have hpred : ¬(¬G.Adj h L₁ ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h c₂) := by
      intro hp
      exact hhA1 (by rw [hA1def, Finset.mem_filter]; exact ⟨hhDc, hp⟩)
    apply Finset.card_pos.mpr
    push Not at hpred
    by_cases h1 : G.Adj h L₁
    · exact ⟨L₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, by simp⟩⟩
    · by_cases h2 : G.Adj h c₁
      · exact ⟨c₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2, by simp⟩⟩
      · exact ⟨c₂, Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr (hpred h1 h2), by simp⟩⟩
  have hisoB_le : (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card) ≤ 3 * B.card := by
    have hle : ∀ g ∈ B, (G.neighborFinset g ∩ Iso).card ≤ 3 := by
      intro g hg
      have hgDc : g ∈ Dᶜ := (Finset.mem_sdiff.mp (hBdef ▸ hg)).1
      have hp := hper g hgDc
      have hpa := hpath1 g hg
      omega
    calc (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card) ≤ ∑ _g ∈ B, 3 := Finset.sum_le_sum hle
      _ = 3 * B.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- Dispatch on `|FF|`.
  have hFFcases : FF.card = 2 ∨ FF.card = 3 ∨ FF.card = 4 ∨ FF.card = 5 ∨ FF.card = 6 := by omega
  rcases hFFcases with hFF | hFF | hFF | hFF | hFF
  · -- **`|FF| = 2`:** budget forces `|B| = 1`, but `∑_B iso ≥ 4 > 3 = 3·|B|`.
    exfalso; omega
  · -- **`|FF| = 3`:** budget forces `|B| = 2`, both inactive hubs `iso = 3`, share contradiction.
    have hBcard : B.card = 2 := by omega
    have hisoB6 : 6 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
    obtain ⟨h₁, h₂, hh12, hBeq⟩ := Finset.card_eq_two.mp hBcard
    have hh1B : h₁ ∈ B := by rw [hBeq]; simp
    have hh2B : h₂ ∈ B := by rw [hBeq]; simp
    have hh1Dc : h₁ ∈ Dᶜ := (Finset.mem_sdiff.mp (hBdef ▸ hh1B)).1
    have hh2Dc : h₂ ∈ Dᶜ := (Finset.mem_sdiff.mp (hBdef ▸ hh2B)).1
    have hisosum : (G.neighborFinset h₁ ∩ Iso).card + (G.neighborFinset h₂ ∩ Iso).card
        = ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by rw [hBeq, Finset.sum_pair hh12]
    have hp1 := hper h₁ hh1Dc
    have hp2 := hper h₂ hh2Dc
    have hpa1 := hpath1 h₁ hh1B
    have hpa2 := hpath1 h₂ hh2B
    have hiso1 : (G.neighborFinset h₁ ∩ Iso).card = 3 := by omega
    have hiso2 : (G.neighborFinset h₂ ∩ Iso).card = 3 := by omega
    have hint1 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by omega
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      have hmem : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh2Dc⟩
      rw [Finset.card_eq_zero] at hint1
      rw [hint1] at hmem; exact (Finset.notMem_empty _) hmem
    exact two_iso3_nonadj_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso4 h₁ h₂ hh1Dc hh2Dc hh12
      hnadj hiso1 hiso2
  · -- **`|FF| = 4`.**  The `|B| = 2` sub-case (`|A1| + |A2| = 11`) is a pure-counting
    -- contradiction (`∑_B iso ≥ 8 > 6 = 3·|B|`).  The extremal `(5,5)` sub-case
    -- (`|A1| = |A2| = 5`, `|B| = 3`) splits on `∑_FF int ∈ {12, 13, 14}`: `12` ⇒ two iso-`3`
    -- non-adjacent hubs, `13` ⇒ a `TwoHubConfig`, `14` ⇒ a Mantel-`4` triangle inside `FF`.
    have hBcase : B.card = 2 ∨ B.card = 3 := by omega
    rcases hBcase with hBc | hBc
    · exfalso; omega
    · -- `|B| = 3`: `|A1| = |A2| = 5`, split on `∑_FF int ∈ {12, 13, 14}`.
      have hBsub : B ⊆ Dᶜ := by rw [hBdef]; exact Finset.sdiff_subset
      have hUcard6 : (A1 ∪ A2).card = 6 := by omega
      have hA1eq : A1.card = 5 := by omega
      have hA2eq : A2.card = 5 := by omega
      have hA1mfc : (A1 \ FF).card = 1 := by omega
      have hA2mA1c : (A2 \ A1).card = 1 := by omega
      have hScase : (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 12
          ∨ (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 13
          ∨ (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 14 := by omega
      rcases hScase with hS | hS | hS
      · -- `∑_FF int = 12`: `∑_FF iso = 4`, `∑_B iso ≥ 8` ⇒ two iso-`3` non-adjacent hubs.
        have hisoB8 : 8 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
        exact inactive_iso8_false G D Iso B ({L₁, c₁, c₂, L₂}) hC4 hIsoD hIsoprop hdeg4 hIso4
          hBsub hBc hper hpath1 hisoB8
      · -- `∑_FF int = 13`: `∑_B int ≤ 1`, `∑_B iso ≥ 7` ⇒ `TwoHubConfig`.
        have hBint1 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) ≤ 1 := by omega
        have hBiso7 : 7 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
        exact ff3_extract_twohub_seventeen G D Iso L₁ c₁ c₂ L₂ B _hth hC4 hIsoD hIsoprop hdeg4
          (fun v hv => (hmemD v).mp hv) hDeq hBsub hBc hBint1 hBiso7 hper hpath1
      · -- `∑_FF int = 14`: `∑_FF(N ∩ FF) ≥ 10` ⇒ Mantel-`4` triangle, contradicting `htri2`.
        have hedge : 10 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card := by
          have hlb := ff_internal_edge_lb G Dᶜ FF hFFsub hSum18
          omega
        obtain ⟨a, b, c, haFF, hbFF, hcFF, hab, hac, hbc⟩ :=
          mantel_four_triangle G FF hFF hedge
        have getA2 : ∀ g : Fin 17, g ∈ FF →
            g ∈ Dᶜ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
          intro g hg
          have hgA2 := hFFsubA2 hg
          rw [hA2def, Finset.mem_filter] at hgA2; exact hgA2
        obtain ⟨haDc, hac1, hac2, haL2⟩ := getA2 a haFF
        obtain ⟨hbDc, hbc1, hbc2, hbL2⟩ := getA2 b hbFF
        obtain ⟨hcDc, hcc1, hcc2, hcL2⟩ := getA2 c hcFF
        exact _htri2 ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
          ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩⟩
  · -- **`|FF| = 5`.**  The generic `|B| = 3` sub-case forces both `∑_B int = 0` and `∑_B iso ≥ 8`,
    -- so two of the three inactive hubs carry `iso = 3` and (being internally isolated) are
    -- non-adjacent — a share contradiction.  The extremal `(5,5)` sub-case (`A1 = A2 = FF`,
    -- `|B| = 4`) closes by a Mantel-`5` triangle inside `FF` (`e(FF) ≥ 7`).
    have hBcase : B.card = 3 ∨ B.card = 4 := by omega
    rcases hBcase with hBc | hBc
    · -- `|B| = 3`: `∑_B int = 0`, `∑_B iso ≥ 8` ⇒ two iso-`3` non-adjacent inactive hubs.
      have hisoFFle : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card) ≤ 4 :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg hFFsubA1 (fun _ _ _ => Nat.zero_le _))
          hisoA1le
      have hintB0 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) = 0 := by omega
      have hisoB8 : 8 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
      obtain ⟨x, y, z, hxy, hxz, hyz, hBeq⟩ := Finset.card_eq_three.mp hBc
      have hxB : x ∈ B := by rw [hBeq]; simp
      have hyB : y ∈ B := by rw [hBeq]; simp
      have hzB : z ∈ B := by rw [hBeq]; simp
      have hxDc : x ∈ Dᶜ := (Finset.mem_sdiff.mp (hBdef ▸ hxB)).1
      have hyDc : y ∈ Dᶜ := (Finset.mem_sdiff.mp (hBdef ▸ hyB)).1
      have hzDc : z ∈ Dᶜ := (Finset.mem_sdiff.mp (hBdef ▸ hzB)).1
      -- Each inactive hub here is internally isolated, so pairwise non-adjacent.
      have hnadj : ∀ u v : Fin 17, u ∈ B → v ∈ B → v ∈ Dᶜ →
          (G.neighborFinset u ∩ Dᶜ).card = 0 → ¬G.Adj u v := by
        intro u v _ _ hvDc huint hadj
        have hmem : v ∈ G.neighborFinset u ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hvDc⟩
        rw [Finset.card_eq_zero] at huint
        rw [huint] at hmem; exact (Finset.notMem_empty _) hmem
      have hintx : (G.neighborFinset x ∩ Dᶜ).card = 0 := by
        have hsum3 : (G.neighborFinset x ∩ Dᶜ).card + (G.neighborFinset y ∩ Dᶜ).card
            + (G.neighborFinset z ∩ Dᶜ).card = ∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card := by
          rw [hBeq, Finset.sum_insert (by simp [hxy, hxz]),
            Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, add_assoc]
        omega
      have hinty : (G.neighborFinset y ∩ Dᶜ).card = 0 := by
        have hsum3 : (G.neighborFinset x ∩ Dᶜ).card + (G.neighborFinset y ∩ Dᶜ).card
            + (G.neighborFinset z ∩ Dᶜ).card = ∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card := by
          rw [hBeq, Finset.sum_insert (by simp [hxy, hxz]),
            Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, add_assoc]
        omega
      have hintz : (G.neighborFinset z ∩ Dᶜ).card = 0 := by
        have hsum3 : (G.neighborFinset x ∩ Dᶜ).card + (G.neighborFinset y ∩ Dᶜ).card
            + (G.neighborFinset z ∩ Dᶜ).card = ∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card := by
          rw [hBeq, Finset.sum_insert (by simp [hxy, hxz]),
            Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, add_assoc]
        omega
      -- Iso-values sum to `≥ 8`, each `≤ 3`, so at least two equal `3`.
      have hisox3 : (G.neighborFinset x ∩ Iso).card ≤ 3 := by
        have hp := hper x hxDc; have hpa := hpath1 x hxB; omega
      have hisoy3 : (G.neighborFinset y ∩ Iso).card ≤ 3 := by
        have hp := hper y hyDc; have hpa := hpath1 y hyB; omega
      have hisoz3 : (G.neighborFinset z ∩ Iso).card ≤ 3 := by
        have hp := hper z hzDc; have hpa := hpath1 z hzB; omega
      have hisosum3 : (G.neighborFinset x ∩ Iso).card + (G.neighborFinset y ∩ Iso).card
          + (G.neighborFinset z ∩ Iso).card = ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by
        rw [hBeq, Finset.sum_insert (by simp [hxy, hxz]),
          Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, add_assoc]
      have hpair : ((G.neighborFinset x ∩ Iso).card = 3 ∧ (G.neighborFinset y ∩ Iso).card = 3)
          ∨ ((G.neighborFinset x ∩ Iso).card = 3 ∧ (G.neighborFinset z ∩ Iso).card = 3)
          ∨ ((G.neighborFinset y ∩ Iso).card = 3 ∧ (G.neighborFinset z ∩ Iso).card = 3) := by
        omega
      rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact two_iso3_nonadj_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso4 x y hxDc hyDc hxy
          (hnadj x y hxB hyB hyDc hintx) e1 e2
      · exact two_iso3_nonadj_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso4 x z hxDc hzDc hxz
          (hnadj x z hxB hzB hzDc hintx) e1 e2
      · exact two_iso3_nonadj_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso4 y z hyDc hzDc hyz
          (hnadj y z hyB hzB hzDc hinty) e1 e2
    · -- `|B| = 4`: `A1 = A2 = FF`, `∑_FF iso ≤ 4` ⇒ `∑_FF int ≥ 16` ⇒ `∑_FF(N ∩ FF) ≥ 14`,
      -- a Mantel-`5` triangle inside `FF ⊆ A2`, contradicting `htri2`.
      have hisoFFle : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card) ≤ 4 :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg hFFsubA1 (fun _ _ _ => Nat.zero_le _))
          hisoA1le
      have hFFint16 : 16 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card := by omega
      have hedge : 14 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card := by
        have hlb := ff_internal_edge_lb G Dᶜ FF hFFsub hSum18
        omega
      obtain ⟨a, b, c, haFF, hbFF, hcFF, hab, hac, hbc⟩ :=
        mantel_five_triangle G FF hFF hedge
      have getA2 : ∀ g : Fin 17, g ∈ FF →
          g ∈ Dᶜ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
        intro g hg
        have hgA2 := hFFsubA2 hg
        rw [hA2def, Finset.mem_filter] at hgA2; exact hgA2
      obtain ⟨haDc, hac1, hac2, haL2⟩ := getA2 a haFF
      obtain ⟨hbDc, hbc1, hbc2, hbL2⟩ := getA2 b hbFF
      obtain ⟨hcDc, hcc1, hcc2, hcL2⟩ := getA2 c hcFF
      exact _htri2 ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
        ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩⟩
  · -- **`|FF| = 6`:** `∑_FF iso ≤ 4` and `iso + int = 4` per fully-free hub force
    -- `∑_FF int ≥ 20 > 18 = ∑_Dᶜ int`, impossible.  (Pure counting.)
    have hisoFFle : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card) ≤ 4 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hFFsubA1 (fun _ _ _ => Nat.zero_le _))
        hisoA1le
    exfalso; omega

end N17

end ACMax
