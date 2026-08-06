import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.HubTriangleStruct

/-!
# `|FF|`-dispatch triangle forcing for the `n = 20`, `e(M) = 3`, `|D| = 8` hub-triangle corner

This file closes the genuinely new `n = 20` obligation `core_triangle_force_twenty` by a
case-split on the fully-free hub count `|FF| ∈ {2, …, 10}` (from `active_hub_budget_twenty`).

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
  via `ff3_extract_twohub_twenty`; `14`: a Mantel-`4` triangle via `mantel_four_triangle`).
  `|FF| = 5` (`|B| = 4`, `A1 = A2 = FF`) forces `∑_FF int ≥ 16`, hence `∑_FF(N ∩ FF) ≥ 14`, a
  Mantel-`5` triangle via `mantel_five_triangle`.  Both Mantel triangles lie in `A2`, contradicting
  `htri2`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Isolated-twin incidence bound.**  If every `M`-isolated twin has at most one neighbour in a
hub set `A`, then the total iso-incidence over `A` is at most `|Iso| = 4`. -/
theorem iso_incidence_le_four (G : SimpleGraph (Fin 20)) (Iso A : Finset (Fin 20))
    (hIso4 : Iso.card = 4)
    (hbound : ∀ t ∈ Iso, (G.neighborFinset t ∩ A).card ≤ 1) :
    (∑ g ∈ A, (G.neighborFinset g ∩ Iso).card) ≤ 4 := by
  classical
  rw [cross_count_twenty G A Iso]
  calc (∑ t ∈ Iso, (G.neighborFinset t ∩ A).card)
      ≤ ∑ _t ∈ Iso, 1 := Finset.sum_le_sum hbound
    _ = Iso.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    _ = 4 := hIso4

/-- **Two non-adjacent iso-`3` hubs are impossible.**  Two distinct non-adjacent degree-`4` hubs
each with all three `M`-isolated twins as neighbours would share `≥ 2` twins (as `|Iso| = 4`),
contradicting the good-`C₄` share bound `nonadj_hubs_share_le_one_iso`. -/
theorem two_iso3_nonadj_false (G : SimpleGraph (Fin 20)) (D Iso : Finset (Fin 20))
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 20, w ∈ Dᶜ → G.degree w = 4) (hIso4 : Iso.card = 4)
    (h₁ h₂ : Fin 20) (hh1Dc : h₁ ∈ Dᶜ) (hh2Dc : h₂ ∈ Dᶜ) (hh12 : h₁ ≠ h₂)
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

/-- **Degree-sum Mantel bound.**  If `FF` contains no triangle and `v ∈ FF`, then the in-`FF` edge
mass is bounded by the star/leak count around `v`: with `k = |N v ∩ FF|`, the neighbourhood of `v`
is independent (else a triangle), pinning `∑_{FF}(N ∩ FF) ≤ k + k·(|FF| − k) + (|FF| − 1 − k)·
(|FF| − 1)`. -/
theorem mantel_bound (G : SimpleGraph (Fin 20)) (FF : Finset (Fin 20)) (v : Fin 20)
    (hvFF : v ∈ FF)
    (htri : ¬∃ a b c : Fin 20, a ∈ FF ∧ b ∈ FF ∧ c ∈ FF ∧
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

/-- **Mantel triangle on five fully-free hubs.**  A `5`-vertex set with in-set edge mass
`∑(N ∩ FF) ≥ 14 > 2·⌊25/4⌋` contains a triangle. -/
theorem mantel_five_triangle (G : SimpleGraph (Fin 20)) (FF : Finset (Fin 20))
    (hcard : FF.card = 5)
    (hedge : 14 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) :
    ∃ a b c : Fin 20, a ∈ FF ∧ b ∈ FF ∧ c ∈ FF ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
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
theorem inactive_iso8_false (G : SimpleGraph (Fin 20)) (D Iso B P : Finset (Fin 20))
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 20, w ∈ Dᶜ → G.degree w = 4) (hIso4 : Iso.card = 4)
    (hBsub : B ⊆ Dᶜ) (hBcard : B.card = 3)
    (hper : ∀ g : Fin 20, g ∈ Dᶜ →
      (G.neighborFinset g ∩ P).card + (G.neighborFinset g ∩ Iso).card
        + (G.neighborFinset g ∩ Dᶜ).card = 4)
    (hpath1 : ∀ h : Fin 20, h ∈ B → 1 ≤ (G.neighborFinset h ∩ P).card)
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
  have hint0 : ∀ u : Fin 20, u ∈ B → (G.neighborFinset u ∩ Iso).card = 3 →
      (G.neighborFinset u ∩ Dᶜ).card = 0 := by
    intro u huB hu3
    have hp := hper u (hBsub huB)
    have hpa := hpath1 u huB
    omega
  have hnadj : ∀ u w : Fin 20, w ∈ Dᶜ → (G.neighborFinset u ∩ Dᶜ).card = 0 →
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
theorem ff3_extract_twohub_twenty (G : SimpleGraph (Fin 20)) (D Iso : Finset (Fin 20))
    (L₁ c₁ c₂ L₂ : Fin 20) (B : Finset (Fin 20))
    (hth : ¬TwoHubConfig G)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 20, w ∈ Dᶜ → G.degree w = 4)
    (hDdeg3 : ∀ v : Fin 20, v ∈ D → G.degree v = 3)
    (hDeq : ({L₁, c₁, c₂, L₂} : Finset (Fin 20)) ∪ Iso = D)
    (hBsub : B ⊆ Dᶜ) (hBcard : B.card = 3)
    (hBint1 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) ≤ 1)
    (hBiso7 : 7 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card)
    (hper : ∀ g : Fin 20, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4)
    (hpath1 : ∀ h : Fin 20, h ∈ B →
      1 ≤ (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card) :
    False := by
  classical
  set P : Finset (Fin 20) := {L₁, c₁, c₂, L₂} with hPdef
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

/-- **No avoider triangle ⇒ contradiction (the `n = 20` `|FF|`-dispatch core).**  Full replacement
for `core_triangle_force_twenty`: dispatches on `|FF| ∈ {2, …, 10}` (`active_hub_budget_twenty`).
The budget `∑ int = 30` over twelve hubs (avoiders `≥ 8`) makes the *small* fully-free counts
collapse by the `|B|` bound (`|FF| ∈ {2, 3, 4, 5}`, since `2 ≤ |B| ≤ |FF| − 4`) and the *large*
ones by the fully-free internal budget (`|FF| ∈ {9, 10}`, `∑_FF int ≥ 4|FF| − 4 > 30`).  The three
remaining corners reduce via the iso-mass redistribution `∑_B iso ≥ 4 + ∑_FF iso`: `|FF| = 6`
(`|B| = 2`, both inactive hubs iso-`3`, `two_iso3_nonadj_false`), `|FF| = 7` (`|B| = 3`,
`∑_FF int ∈ {24, 25, 26}`, closed by `inactive_iso8_false` / `ff3_extract_twohub_twenty`), and
`|FF| = 8`.  The genuinely-new boundary is `|FF| = 8`, `|B| = 4` (`A1 = A2 = FF`): the avoider mass
is exactly the triangle-free Mantel-`8` extremal `K_{4,4}` (mass `32`), so the packing/Mantel
argument loses all slack.  This corner is **CLOSED** (no `sorry`) by threading the top-level
good-triangle threshold `≤ 11` (`hT`): extracting the two common `L₁,L₂`-neighbours `r, s ∈ B`,
a single case-split closes it — `r ≁ s` fires the good-`C₄` `L₁–r–L₂–s` (`Σ = 14`, `hC4`), and
`r ~ s` fires the degree-`11` good triangle `{r, s, L₁}` (`Σ = 4 + 4 + 3 = 11`, `hT`). -/
theorem iso_rich_force_twenty (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ : Fin 20)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hcov : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (_hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (_hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3)
    (hL1deg : G.degree L₁ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hdeg4 : ∀ w : Fin 20, w ∈ Dᶜ → G.degree w = 4)
    (_hD8 : D.card = 8) (_hth : ¬TwoHubConfig G)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hW : ∀ g : Fin 20, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hA : ∀ t : Fin 20, t ∈ Iso → ∀ p q : Fin 20, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q c₂) ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)))
    (hDc9 : Dᶜ.card = 12) (hIso4 : Iso.card = 4)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hSum18 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 30)
    (_htri1 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂))
    (_htri2 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)) :
    False := by
  classical
  -- Path / Iso partition of `D`.
  obtain ⟨hDeq, _hdisj⟩ :=
    path_iso_partition G D Iso L₁ c₁ c₂ L₂ hIsodef hisochar hL1D hc1D hc2D hL2D hac1L1 hc12 hac2L2
  have hclassP : ∀ x : Fin 20, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
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
    cherry_avoiders_ge_six G D L₁ c₁ c₂ L₂ hDc9 hcard_c1 hcard_c2 hcard_L1 hcard_L2
  rw [← hA1def] at hA1card
  rw [← hA2def] at hA2card
  -- Inclusion–exclusion budget: `|FF| ∈ {2, 3, 4, 5, 6}`.
  obtain ⟨hFFlb, hFFub⟩ :=
    active_hub_budget_twenty Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card)
      hA1sub hA2sub hFFdef hA1card hA2card hA1int hA2int hFFint hSum18
  -- Residual incidence sums (path / iso totals and the per-hub split).
  obtain ⟨hsumP, hsumI, hper⟩ :=
    residual_incidence_sums G D Iso L₁ c₁ c₂ L₂ hIsodef hIsoprop hisochar hL1D hc1D hc2D hL2D
      hac1L1 hc12 hac2L2 hnc1L2 hdeg4 hcard_c1 hcard_c2 hcard_L1 hcard_L2 hIso4 hL1nc2 hL2nc1
  -- The inactive hubs `B = Dᶜ \ (A1 ∪ A2)` and the internal-degree budget.
  set B := Dᶜ \ (A1 ∪ A2) with hBdef
  have hUsub : A1 ∪ A2 ⊆ Dᶜ := Finset.union_subset hA1sub hA2sub
  have hBpart : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card)
      + ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Dᶜ).card = 30 := by
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
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card = 0 := by
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
  have hintFFle : (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) ≤ 30 := by
    rw [← hSum18]
    exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  -- Each inactive hub touches a cherry (`path ≥ 1`), hence carries `iso ≤ 3`.
  have hpath1 : ∀ h ∈ B,
      1 ≤ (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card := by
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
  -- Global iso bound on `FF`: `∑_FF iso ≤ ∑_{A1} iso ≤ 4`.
  have hisoFFle : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card) ≤ 4 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hFFsubA1 (fun _ _ _ => Nat.zero_le _))
      hisoA1le
  have hBsub : B ⊆ Dᶜ := by rw [hBdef]; exact Finset.sdiff_subset
  have getA2 : ∀ g : Fin 20, g ∈ FF →
      g ∈ Dᶜ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
    intro g hg
    have hgA2 := hFFsubA2 hg
    rw [hA2def, Finset.mem_filter] at hgA2; exact hgA2
  -- Dispatch on `|FF|`.  With `Dᶜ.card = 12`, `∑ int = 30` and avoiders `≥ 8`, the iso bound
  -- forces `|B| ≥ 2` and the internal budget forces `|B| ≤ |FF| − 4`, so the non-vacuous
  -- fully-free counts are `|FF| ∈ {6, 7, 8}`; `|FF| ∈ {2, 3, 4, 5}` collapse via the `|B|` bound
  -- and `|FF| ∈ {9, 10}` via the fully-free internal budget `∑_FF int ≥ 4|FF| − 4 > 30`.
  have hFFcases : FF.card = 2 ∨ FF.card = 3 ∨ FF.card = 4 ∨ FF.card = 5 ∨ FF.card = 6
      ∨ FF.card = 7 ∨ FF.card = 8 ∨ FF.card = 9 ∨ FF.card = 10 := by omega
  rcases hFFcases with hFF | hFF | hFF | hFF | hFF | hFF | hFF | hFF | hFF
  · -- **`|FF| = 2`:** `|B| ≤ −2` is impossible (`|B| ≥ 2`).
    exfalso; omega
  · -- **`|FF| = 3`:** `|B| ≤ −1` but `|B| ≥ 2`.
    exfalso; omega
  · -- **`|FF| = 4`:** `|B| ≤ 0` but `|B| ≥ 2`.
    exfalso; omega
  · -- **`|FF| = 5`:** `|B| ≤ 1` but `|B| ≥ 2` (the denser `n = 20` budget kills this corner).
    exfalso; omega
  · -- **`|FF| = 6`:** the budget forces `|B| = 2` with `∑_FF int = 22`, so both inactive hubs
    -- carry `iso = 3` and are internally isolated — a `two_iso3_nonadj_false` contradiction.
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
  · -- **`|FF| = 7`:** `|B| ∈ {2, 3}`.  `|B| = 2` collapses (`∑_B iso ≥ 8 > 6 = 3·|B|`).
    -- `|B| = 3` splits on `∑_FF int ∈ {24, 25, 26}`.
    have hBcase : B.card = 2 ∨ B.card = 3 := by omega
    rcases hBcase with hBc | hBc
    · -- `|B| = 2`: `∑_FF int = 24`, `∑_B iso ≥ 8 > 6`, impossible.
      exfalso; omega
    · -- `|B| = 3`: `∑_FF int ∈ {24, 25, 26}`.
      have hScase : (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 24
          ∨ (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 25
          ∨ (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 26 := by omega
      rcases hScase with hS | hS | hS
      · -- `∑_FF int = 24`: `∑_B iso ≥ 8` ⇒ two iso-`3` non-adjacent inactive hubs.
        have hisoB8 : 8 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
        exact inactive_iso8_false G D Iso B ({L₁, c₁, c₂, L₂}) hC4 hIsoD hIsoprop hdeg4 hIso4
          hBsub hBc hper hpath1 hisoB8
      · -- `∑_FF int = 25`: `∑_B int ≤ 1`, `∑_B iso ≥ 7` ⇒ `TwoHubConfig`.
        have hBint1 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) ≤ 1 := by omega
        have hBiso7 : 7 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
        exact ff3_extract_twohub_twenty G D Iso L₁ c₁ c₂ L₂ B _hth hC4 hIsoD hIsoprop hdeg4
          (fun v hv => (hmemD v).mp hv) hDeq hBsub hBc hBint1 hBiso7 hper hpath1
      · -- `∑_FF int = 26`: `∑_B int = 0`.  The two extra avoider hubs `C = (A1 ∪ A2) \ FF` each
        -- touch an `L`-cherry (`A1 \ A2 ⇒ ~L₂`, `A2 \ A1 ⇒ ~L₁`), so `∑_C path ≥ |C| = 2`; with the
        -- path total `6` this forces `∑_B path ≤ 4`, and the per-hub identity (`∑_B int = 0`) then
        -- gives `∑_B iso ≥ 12 − 4 = 8` — two inactive hubs are iso-`3` and non-adjacent
        -- (`inactive_iso8_false`).
        have hFFsub_union : FF ⊆ A1 ∪ A2 := hFFsubA1.trans Finset.subset_union_left
        have hCpath : ∀ g ∈ (A1 ∪ A2) \ FF,
            1 ≤ (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card := by
          intro g hg
          rw [Finset.mem_sdiff, Finset.mem_union] at hg
          obtain ⟨hgU, hgnFF⟩ := hg
          apply Finset.card_pos.mpr
          by_cases hgA1 : g ∈ A1
          · have hgnA2 : g ∉ A2 :=
              fun h => hgnFF (by rw [hFFdef]; exact Finset.mem_inter.mpr ⟨hgA1, h⟩)
            rw [hA1def, Finset.mem_filter] at hgA1
            obtain ⟨hgDc, _, hgc1, hgc2⟩ := hgA1
            have hgL2 : G.Adj g L₂ := by
              by_contra h
              exact hgnA2 (by rw [hA2def, Finset.mem_filter]; exact ⟨hgDc, hgc1, hgc2, h⟩)
            exact ⟨L₂, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hgL2, by simp⟩⟩
          · have hgA2 : g ∈ A2 := hgU.resolve_left hgA1
            rw [hA2def, Finset.mem_filter] at hgA2
            obtain ⟨hgDc, hgc1, hgc2, _⟩ := hgA2
            have hgL1 : G.Adj g L₁ := by
              by_contra h
              exact hgA1 (by rw [hA1def, Finset.mem_filter]; exact ⟨hgDc, h, hgc1, hgc2⟩)
            exact ⟨L₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hgL1, by simp⟩⟩
        have hUpath : (∑ g ∈ B, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} :
              Finset (Fin 20))).card)
            + ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} :
              Finset (Fin 20))).card = 6 := by
          rw [hBdef, Finset.sum_sdiff hUsub]; exact hsumP
        have hFFpath_zero : (∑ g ∈ FF, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} :
              Finset (Fin 20))).card) = 0 :=
          Finset.sum_eq_zero (fun g hg => hFFpath0 g hg)
        have hUpathsplit : (∑ g ∈ (A1 ∪ A2) \ FF, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} :
              Finset (Fin 20))).card)
            + ∑ g ∈ FF, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
            = ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} :
              Finset (Fin 20))).card := Finset.sum_sdiff hFFsub_union
        have hUcard9 : (A1 ∪ A2).card = 9 := by
          have h := hBcard_eq; rw [hBc, hDc9] at h; omega
        have hCcard : ((A1 ∪ A2) \ FF).card = 2 := by
          have h := Finset.card_sdiff_add_card_eq_card hFFsub_union
          rw [hUcard9, hFF] at h; omega
        have hCpath_ge : 2 ≤ ∑ g ∈ (A1 ∪ A2) \ FF, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} :
              Finset (Fin 20))).card := by
          have hge := Finset.card_nsmul_le_sum ((A1 ∪ A2) \ FF)
            (fun g => (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card) 1
            (fun g hg => hCpath g hg)
          rw [hCcard] at hge; simpa using hge
        have hBper : (∑ g ∈ B, ((G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} :
              Finset (Fin 20))).card + (G.neighborFinset g ∩ Iso).card
              + (G.neighborFinset g ∩ Dᶜ).card)) = 4 * B.card := by
          rw [Finset.sum_congr rfl (fun g hg => hper g (hBsub hg)), Finset.sum_const,
            smul_eq_mul, Nat.mul_comm]
        have hBsplit : (∑ g ∈ B, ((G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} :
              Finset (Fin 20))).card + (G.neighborFinset g ∩ Iso).card
              + (G.neighborFinset g ∩ Dᶜ).card))
            = (∑ g ∈ B, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card)
              + (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card)
              + ∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hSB0 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) = 0 := by omega
        have hisoB8 : 8 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by
          rw [hBc] at hBper; omega
        exact inactive_iso8_false G D Iso B ({L₁, c₁, c₂, L₂}) hC4 hIsoD hIsoprop hdeg4 hIso4
          hBsub hBc hper hpath1 hisoB8
  · -- **`|FF| = 8`:** `|B| ∈ {2, 3, 4}`.  `|B| = 2` collapses; `|B| = 3` forces `∑_FF int = 28`
    -- (`∑_B iso ≥ 8`, `inactive_iso8_false`); `|B| = 4` (`A1 = A2 = FF`) is the genuinely-new
    -- `K_{4,4}` boundary corner (`∑_FF(N ∩ FF)` only reaches `32`, the triangle-free Mantel-`8`
    -- extremal, while a Mantel-`8` triangle needs `≥ 33`).
    have hBcase : B.card = 2 ∨ B.card = 3 ∨ B.card = 4 := by omega
    rcases hBcase with hBc | hBc | hBc
    · -- `|B| = 2`: budget impossible.
      exfalso; omega
    · -- `|B| = 3`: `∑_FF int = 28`, `∑_B iso ≥ 8` ⇒ two iso-`3` non-adjacent inactive hubs.
      have hisoB8 : 8 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
      exact inactive_iso8_false G D Iso B ({L₁, c₁, c₂, L₂}) hC4 hIsoD hIsoprop hdeg4 hIso4
        hBsub hBc hper hpath1 hisoB8
    · -- **`|B| = 4` (`A1 = A2 = FF`): the genuine excess-`11` boundary, CLOSED by threading the
      -- top-level good-triangle `≤ 11` cut.**  With `A1 = A2 = FF`, every path-hub edge lands in
      -- `B`; the middle vertices `c₁, c₂` each have a single `B`-neighbour `w₁, w₂` touching no
      -- other path vertex (triangle `Σ = 10` / good-`C₄`), so `N(L₁) ∩ Dᶜ` and `N(L₂) ∩ Dᶜ`
      -- (each `2` hubs) both equal `B \ {w₁, w₂}` (only `2` hubs), forcing two common hubs `r, s`
      -- each adjacent to `L₁` and `L₂`.  Then a single case-split closes it, *sub-budget
      -- independently*: if `r ≁ s` the good-`C₄` `L₁–r–L₂–s` (`Σ = 14`) fires against `hC4`; if
      -- `r ~ s` the good triangle `{r, s, L₁}` (`Σ = 4 + 4 + 3 = 11`) fires against the threaded
      -- `hT` (`≤ 11`).  (At `n = 18` the `r ~ s` branch instead forced a Mantel-`6` triangle, but
      -- at `n = 19` the avoider mass parity-pins `FF = K_{3,4}` exactly at the triangle-free
      -- Mantel-`7` extremal `24`, so the `≤ 11` good triangle is the only available kill.)
      exfalso
      have hcardU : (A1 ∪ A2).card = 8 := by
        have h := hBcard_eq; rw [hBc, hDc9] at h; omega
      have hFFsub_union : FF ⊆ A1 ∪ A2 := hFFsubA1.trans Finset.subset_union_left
      have hUFF : FF = A1 ∪ A2 :=
        Finset.eq_of_subset_of_card_le hFFsub_union (le_of_eq (hcardU.trans hFF.symm))
      have hDcneD : ∀ a b : Fin 20, a ∈ Dᶜ → b ∈ D → a ≠ b :=
        fun a b ha hb e => (Finset.mem_compl.mp ha) (e ▸ hb)
      have hmemB : ∀ h : Fin 20, h ∈ Dᶜ → h ∉ FF → h ∈ B := by
        intro h hhDc hhFF
        rw [hBdef, Finset.mem_sdiff]
        exact ⟨hhDc, fun hm => hhFF (by rw [← hUFF] at hm; exact hm)⟩
      have hadjL1_B : ∀ h : Fin 20, h ∈ Dᶜ → G.Adj L₁ h → h ∈ B := by
        intro h hhDc hadj
        refine hmemB h hhDc (fun hFFm => ?_)
        have h1 := hFFsubA1 hFFm; rw [hA1def, Finset.mem_filter] at h1
        exact h1.2.1 hadj.symm
      have hadjL2_B : ∀ h : Fin 20, h ∈ Dᶜ → G.Adj L₂ h → h ∈ B := by
        intro h hhDc hadj
        refine hmemB h hhDc (fun hFFm => ?_)
        have h1 := hFFsubA2 hFFm; rw [hA2def, Finset.mem_filter] at h1
        exact h1.2.2.2 hadj.symm
      have hadjc1_B : ∀ h : Fin 20, h ∈ Dᶜ → G.Adj c₁ h → h ∈ B := by
        intro h hhDc hadj
        refine hmemB h hhDc (fun hFFm => ?_)
        have h1 := hFFsubA1 hFFm; rw [hA1def, Finset.mem_filter] at h1
        exact h1.2.2.1 hadj.symm
      have hadjc2_B : ∀ h : Fin 20, h ∈ Dᶜ → G.Adj c₂ h → h ∈ B := by
        intro h hhDc hadj
        refine hmemB h hhDc (fun hFFm => ?_)
        have h1 := hFFsubA1 hFFm; rw [hA1def, Finset.mem_filter] at h1
        exact h1.2.2.2 hadj.symm
      -- Triangle helper (`Σ = 3 + 3 + 4 = 10 ≤ 11`).
      have htri10 : ∀ u v w : Fin 20, G.Adj u v → G.Adj v w → G.Adj u w →
          G.degree u = 3 → G.degree v = 3 → G.degree w = 4 → False := by
        intro u v w a1 a2 a3 d1 d2 d3
        exact hT ⟨u, v, w, a1.ne, a2.ne, a3.ne, a1, a2, a3, by omega⟩
      -- The single `B`-neighbour `w₁` of `c₁`.
      have hNc1eqB : G.neighborFinset c₁ ∩ Dᶜ ⊆ B := by
        intro h hh
        rw [Finset.mem_inter, G.mem_neighborFinset] at hh
        exact hadjc1_B h hh.2 hh.1
      obtain ⟨w₁, hw1eq⟩ := Finset.card_eq_one.mp hcard_c1
      have hw1mem : w₁ ∈ G.neighborFinset c₁ ∩ Dᶜ := by
        rw [hw1eq]; exact Finset.mem_singleton_self _
      have hw1c1 : G.Adj c₁ w₁ := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw1mem).1
      have hw1Dc : w₁ ∈ Dᶜ := (Finset.mem_inter.mp hw1mem).2
      have hw1B : w₁ ∈ B := hNc1eqB hw1mem
      have hw1deg : G.degree w₁ = 4 := hdeg4 w₁ hw1Dc
      have hw1L1 : ¬G.Adj w₁ L₁ := fun h =>
        htri10 L₁ c₁ w₁ hac1L1.symm hw1c1 h.symm hL1deg hc1deg hw1deg
      have hw1c2 : ¬G.Adj w₁ c₂ := fun h =>
        htri10 c₂ c₁ w₁ hc12.symm hw1c1 h.symm hc2deg hc1deg hw1deg
      have hw1L2 : ¬G.Adj w₁ L₂ := by
        intro h
        by_cases hwc2 : G.Adj w₁ c₂
        · exact hw1c2 hwc2
        · apply hC4
          refine ⟨c₁, w₁, L₂, c₂, ?_, hw1c1, h, hac2L2.symm, hc12.symm, hnc1L2, hwc2, by omega⟩
          rw [Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨G.ne_of_adj hw1c1, hL2nc1.symm, hc12.ne⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨h.ne, hDcneD w₁ c₂ hw1Dc hc2D⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_singleton]; exact (G.ne_of_adj hac2L2).symm),
              Finset.card_singleton]
      -- The single `B`-neighbour `w₂` of `c₂`.
      obtain ⟨w₂, hw2eq⟩ := Finset.card_eq_one.mp hcard_c2
      have hw2mem : w₂ ∈ G.neighborFinset c₂ ∩ Dᶜ := by
        rw [hw2eq]; exact Finset.mem_singleton_self _
      have hw2c2 : G.Adj c₂ w₂ := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw2mem).1
      have hw2Dc : w₂ ∈ Dᶜ := (Finset.mem_inter.mp hw2mem).2
      have hw2B : w₂ ∈ B := hadjc2_B w₂ hw2Dc hw2c2
      have hw2deg : G.degree w₂ = 4 := hdeg4 w₂ hw2Dc
      have hw2L2 : ¬G.Adj w₂ L₂ := fun h =>
        htri10 L₂ c₂ w₂ hac2L2.symm hw2c2 h.symm hL2deg hc2deg hw2deg
      have hw2c1 : ¬G.Adj w₂ c₁ := fun h =>
        htri10 c₁ c₂ w₂ hc12 hw2c2 h.symm hc1deg hc2deg hw2deg
      have hw2L1 : ¬G.Adj w₂ L₁ := by
        intro h
        by_cases hwc1 : G.Adj w₂ c₁
        · exact hw2c1 hwc1
        · apply hC4
          refine ⟨c₂, w₂, L₁, c₁, ?_, hw2c2, h, hac1L1.symm, hc12,
            fun ha => hnL1c2 ha.symm, hwc1, by omega⟩
          rw [Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨G.ne_of_adj hw2c2, hL1nc2.symm, hc12.ne'⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨h.ne, hDcneD w₂ c₁ hw2Dc hc1D⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_singleton]; exact (G.ne_of_adj hac1L1).symm),
              Finset.card_singleton]
      -- `N(L₁) ∩ Dᶜ` and `N(L₂) ∩ Dᶜ` both equal `B \ {w₁, w₂}` (the `2` remaining hubs).
      have hw12ne : w₁ ≠ w₂ := fun e => hw2c1 (by rw [← e]; exact hw1c1.symm)
      have hNL1B : G.neighborFinset L₁ ∩ Dᶜ ⊆ B \ {w₁, w₂} := by
        intro h hh
        rw [Finset.mem_inter, G.mem_neighborFinset] at hh
        rw [Finset.mem_sdiff]
        refine ⟨hadjL1_B h hh.2 hh.1, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun e => hw1L1 (by rw [← e]; exact hh.1.symm),
          fun e => hw2L1 (by rw [← e]; exact hh.1.symm)⟩
      have hNL2B : G.neighborFinset L₂ ∩ Dᶜ ⊆ B \ {w₁, w₂} := by
        intro h hh
        rw [Finset.mem_inter, G.mem_neighborFinset] at hh
        rw [Finset.mem_sdiff]
        refine ⟨hadjL2_B h hh.2 hh.1, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun e => hw1L2 (by rw [← e]; exact hh.1.symm),
          fun e => hw2L2 (by rw [← e]; exact hh.1.symm)⟩
      have hBw12card : (B \ {w₁, w₂}).card = 2 := by
        have hw12sub : ({w₁, w₂} : Finset (Fin 20)) ⊆ B := by
          intro h hh; simp only [Finset.mem_insert, Finset.mem_singleton] at hh
          rcases hh with rfl | rfl <;> assumption
        have hcard12 : ({w₁, w₂} : Finset (Fin 20)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [hw12ne]), Finset.card_singleton]
        have h := Finset.card_sdiff_add_card_inter B ({w₁, w₂} : Finset (Fin 20))
        rw [Finset.inter_eq_right.mpr hw12sub, hcard12, hBc] at h
        omega
      have hNL1eq : G.neighborFinset L₁ ∩ Dᶜ = B \ {w₁, w₂} :=
        Finset.eq_of_subset_of_card_le hNL1B (by rw [hBw12card, hcard_L1])
      have hNL2eq : G.neighborFinset L₂ ∩ Dᶜ = B \ {w₁, w₂} :=
        Finset.eq_of_subset_of_card_le hNL2B (by rw [hBw12card, hcard_L2])
      -- Extract the two common hubs `r, s`, each adjacent to `L₁` and `L₂`.
      obtain ⟨r, s, hrs, hrsEq⟩ := Finset.card_eq_two.mp hBw12card
      have hrBw : r ∈ B \ {w₁, w₂} := by rw [hrsEq]; simp
      have hsBw : s ∈ B \ {w₁, w₂} := by rw [hrsEq]; simp
      have hrNL1 : r ∈ G.neighborFinset L₁ ∩ Dᶜ := by rw [hNL1eq]; exact hrBw
      have hsNL1 : s ∈ G.neighborFinset L₁ ∩ Dᶜ := by rw [hNL1eq]; exact hsBw
      have hrNL2 : r ∈ G.neighborFinset L₂ ∩ Dᶜ := by rw [hNL2eq]; exact hrBw
      have hsNL2 : s ∈ G.neighborFinset L₂ ∩ Dᶜ := by rw [hNL2eq]; exact hsBw
      have hrL1 : G.Adj L₁ r := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hrNL1).1
      have hsL1 : G.Adj L₁ s := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hsNL1).1
      have hrL2 : G.Adj L₂ r := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hrNL2).1
      have hsL2 : G.Adj L₂ s := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hsNL2).1
      have hrDc : r ∈ Dᶜ := (Finset.mem_inter.mp hrNL1).2
      have hsDc : s ∈ Dᶜ := (Finset.mem_inter.mp hsNL1).2
      -- `¬G.Adj L₁ L₂` (the only `D`–`D` edges pass through `c₁` / `c₂`).
      have hL1L2 : ¬G.Adj L₁ L₂ := by
        intro hadj
        rcases hcov L₁ L₂ hL1D hL2D hadj with h | h | h | h
        · exact (G.ne_of_adj hac1L1).symm h
        · exact hL1nc2 h
        · exact hL2nc1 h
        · exact (G.ne_of_adj hac2L2).symm h
      have hL1L2ne : L₁ ≠ L₂ := fun e => hnc1L2 (e ▸ hac1L1)
      have hL1r : L₁ ≠ r := fun e => (Finset.mem_compl.mp hrDc) (e ▸ hL1D)
      have hL1s : L₁ ≠ s := fun e => (Finset.mem_compl.mp hsDc) (e ▸ hL1D)
      have hL2r : L₂ ≠ r := fun e => (Finset.mem_compl.mp hrDc) (e ▸ hL2D)
      have hL2s : L₂ ≠ s := fun e => (Finset.mem_compl.mp hsDc) (e ▸ hL2D)
      by_cases hrsadj : G.Adj r s
      · -- `r ~ s`: the good triangle `{r, s, L₁}` (`Σ = 4 + 4 + 3 = 11`) fires against `hT`.
        exact hT ⟨r, s, L₁, hrsadj.ne, (G.ne_of_adj hsL1).symm, (G.ne_of_adj hrL1).symm,
          hrsadj, hsL1.symm, hrL1.symm, by
            have := hdeg4 r hrDc; have := hdeg4 s hsDc; omega⟩
      · -- `r ≁ s`: the good `C₄` `L₁–r–L₂–s` (`Σ = 14`) fires against `hC4`.
        apply hC4
        refine ⟨L₁, r, L₂, s, ?_, hrL1, hrL2.symm, hsL2, hsL1.symm, hL1L2, hrsadj, by
          have := hdeg4 r hrDc; have := hdeg4 s hsDc; omega⟩
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hL1r, hL1L2ne, hL1s⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨Ne.symm hL2r, hrs⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]; exact hL2s),
            Finset.card_singleton]
  · -- **`|FF| = 9`:** `∑_FF iso ≤ 4` and `iso + int = 4` per fully-free hub force
    -- `∑_FF int ≥ 32 > 30 = ∑_Dᶜ int`, impossible.  (Pure counting.)
    exfalso; omega
  · -- **`|FF| = 10`:** `∑_FF iso ≤ 4` and `iso + int = 4` per fully-free hub force
    -- `∑_FF int ≥ 36 > 30 = ∑_Dᶜ int`, impossible.  (Pure counting.)
    exfalso; omega

end N20

end ACMax
