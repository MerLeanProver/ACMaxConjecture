import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.N17.TwoHubSelect

/-!
# The tight `(9, 6, 36)` two-hub `e(M) = 1` profile for `n = 17`

This file closes the tight `e(M) = 1` two-hub residual profile
`(|Hub|, |Iso|, ∑deg) = (9, 6, 36)` left open by `two_hub_select_eM1_tight_seventeen` in
`TwinCert17TwoHubTight`.

In this profile the handshake forces all nine hubs to have degree `4` (there is no degree-`5` hub to
absorb iso-incidences).  The sharp off-diagonal cover inequality `cover_offDiag_ineq` together with
the loose bounds `Q ≤ 6·|Iso|` and `E ≤ 3·|S| − 9` (where `S` is the set of iso-rich degree-`4`
hubs) refutes the cases `|S| ∈ {8, 9}` outright, and the threshold decomposition pins `|S| ≥ 7`, so
`|S| = 7` is the only surviving cardinality.

The residual `|S| = 7` case is closed using the threaded global hypotheses `h3` (minimum degree `3`)
and `hisodeg` (each `M`-isolated twin has degree `3`, hence all its neighbours in `Hub`).  The
iso-degree threshold count (`hmf`) pins `I_S = 16`, whence `Q ≤ 30` and `E = 12`, so every `S`-vertex
has all its neighbours inside `S ∪ Iso` (no edges to the two low hubs `Hub \ S` or the two `M`-edge
endpoints).  With `hNI` forcing the two `M`-edge endpoints `u, v` to be adjacent, of degree `3`, and
to have exactly two hub-neighbours each — necessarily the two low hubs — a low hub `ℓ` is adjacent to
both `u` and `v`, giving a triangle `{ℓ, u, v}` of degree sum `4 + 3 + 3 = 10` excluded by `hT`. -/

namespace ACMax

open scoped Classical

namespace N17

/-- **Off-diagonal cover inequality.**  If every ordered distinct pair from `S` is either adjacent or
shares a common neighbour in `Iso` (`hcov`), then the off-diagonal of `S` embeds into the union of
the adjacency pairs and the twin neighbourhood off-diagonals, yielding the counting bound. -/
theorem cover_offDiag_ineq (G : SimpleGraph (Fin 17)) (Iso S : Finset (Fin 17))
    (hcov : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b ∨
      (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).Nonempty) :
    S.card * S.card ≤ S.card + (∑ a ∈ S, (G.neighborFinset a ∩ S).card)
      + ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card) := by
  classical
  set A : Finset (Fin 17 × Fin 17) :=
    S.biUnion (fun a => {a} ×ˢ (G.neighborFinset a ∩ S)) with hAdef
  set B : Finset (Fin 17 × Fin 17) :=
    Iso.biUnion (fun t => (G.neighborFinset t ∩ S).offDiag) with hBdef
  have hsub : S.offDiag ⊆ A ∪ B := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨ha, hb, hne⟩ := hp
    rcases hcov p.1 ha p.2 hb hne with hadj | hsh
    · apply Finset.mem_union_left
      rw [hAdef, Finset.mem_biUnion]
      refine ⟨p.1, ha, ?_⟩
      rw [Finset.mem_product, Finset.mem_singleton]
      refine ⟨rfl, ?_⟩
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj, hb⟩
    · apply Finset.mem_union_right
      obtain ⟨t, ht⟩ := hsh
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
      obtain ⟨⟨hta, htb⟩, htIso⟩ := ht
      rw [hBdef, Finset.mem_biUnion]
      refine ⟨t, htIso, ?_⟩
      rw [Finset.mem_offDiag]
      refine ⟨?_, ?_, hne⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hta.symm, ha⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨htb.symm, hb⟩
  have hcardle : S.offDiag.card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)
  have hAcard : A.card ≤ ∑ a ∈ S, (G.neighborFinset a ∩ S).card := by
    refine le_trans Finset.card_biUnion_le ?_
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.card_product, Finset.card_singleton, one_mul]
  have hBcard : B.card ≤ ∑ t ∈ Iso, (G.neighborFinset t ∩ S).offDiag.card :=
    Finset.card_biUnion_le
  have htwin : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).offDiag.card
      = (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card := fun t _ => Finset.offDiag_card _
  rw [Finset.sum_congr rfl htwin] at hBcard
  have hoff : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card _
  rw [hoff] at hcardle
  omega

/-- **Tight `(9, 6, 36)` two-hub `e(M) = 1` residual.**  All nine hubs have degree `4`.  The cover
inequality refutes `|S| ∈ {8, 9}` (iso-rich degree-`4` hubs) and the threshold decomposition forces
`|S| ≥ 7`; the residual `|S| = 7` case is closed via `hmf` (`I_S = 16`, `E = 12`, neighbourhood
saturation) together with `h3`, `hisodeg`, `hNI`, which build a triangle `{ℓ, u, v}` of degree sum
`4 + 3 + 3 = 10` on a low hub and the two `M`-edge endpoints, excluded by `hT`.  Hence a good
non-adjacent degree-`4` pair exists. -/
theorem two_hub_select_eM1_96_tight (G : SimpleGraph (Fin 17)) (Hub Iso : Finset (Fin 17))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (h3 : ∀ v : Fin 17, 3 ≤ G.degree v) (hisodeg : ∀ t ∈ Iso, G.degree t = 3)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h9 : Hub.card = 9) (h6 : Iso.card = 6) (h36 : ∑ w ∈ Hub, G.degree w = 36)
    (hNI : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4) :
    ∃ h₁ h₂ : Fin 17, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select_seventeen G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_seventeen G Hub Iso hdisj hshare key
  have hisosum := hub_iso_sum_seventeen G Hub Iso hiso3
  set S : Finset (Fin 17) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hSdef
  have hcov : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b ∨
      (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).Nonempty := by
    intro a ha b hb hab
    rw [hSdef, Finset.mem_filter] at ha hb
    by_cases hadj : G.Adj a b
    · exact Or.inl hadj
    · refine Or.inr ?_
      have hk := key a ha.1 b hb.1 ha.2.1 hb.2.1 hab hadj
      have hmin : 2 ≤ min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card) :=
        le_min ha.2.2 hb.2.2
      rw [← Finset.card_pos]
      omega
  have hCI := cover_offDiag_ineq G Iso S hcov
  set T4 : Finset (Fin 17) := Hub.filter (fun h => G.degree h = 4) with hT4def
  set T5 : Finset (Fin 17) := Hub.filter (fun h => ¬ G.degree h = 4) with hT5def
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
  have hSsubHub : S ⊆ Hub := by rw [hSdef]; exact Finset.filter_subset _ _
  have hSsubT4 : S ⊆ T4 := by
    rw [hSdef, hT4def]; intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  have hcardsplit : T4.card + T5.card = Hub.card :=
    Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
  have hT5deg5 : ∀ v ∈ T5, G.degree v = 5 := by
    intro v hv; rw [hT5def, Finset.mem_filter] at hv
    rcases hdeg45 v hv.1 with h | h
    · exact absurd h hv.2
    · exact h
  have hdegsumsplit : ∑ v ∈ T4, G.degree v + ∑ v ∈ T5, G.degree v = ∑ w ∈ Hub, G.degree w :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hT4deg : ∑ v ∈ T4, G.degree v = 4 * T4.card := by
    rw [hT4def, Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hT5deg : ∑ v ∈ T5, G.degree v = 5 * T5.card := by
    rw [Finset.sum_congr rfl (fun x hx => hT5deg5 x hx), Finset.sum_const, smul_eq_mul, mul_comm]
  -- All nine hubs have degree `4`.
  have hT5card0 : T5.card = 0 := by
    rw [h9] at hcardsplit; rw [hT4deg, hT5deg, h36] at hdegsumsplit; omega
  have hT4card9 : T4.card = 9 := by omega
  have hisosplit : ∑ v ∈ T4, (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ T5, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hT5iso0 : ∑ v ∈ T5, (G.neighborFinset v ∩ Iso).card = 0 := by
    have hc : T5.card = 0 := hT5card0
    rw [Finset.card_eq_zero] at hc; rw [hc]; simp
  have hT4iso18 : ∑ v ∈ T4, (G.neighborFinset v ∩ Iso).card = 18 := by
    rw [h6] at hisosum; omega
  -- `S ⊆ T4` and each non-`S` member of `T4` has iso-degree `≤ 1`.
  have hT4le4 : ∀ a ∈ T4, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    have hd : G.degree a = 4 := by rw [hT4def, Finset.mem_filter] at ha; exact ha.2
    calc (G.neighborFinset a ∩ Iso).card
        ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
      _ = G.degree a := G.card_neighborFinset_eq_degree a
      _ = 4 := hd
  -- Threshold decomposition forces `|S| ≥ 7`.
  have hdecomp : ∀ a ∈ T4, (G.neighborFinset a ∩ Iso).card
      = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
    intro a ha; have := hT4le4 a ha; split_ifs <;> omega
  have hcong := Finset.sum_congr rfl hdecomp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter]
    at hcong
  have hSeqT4 : S = T4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hSdef, hT4def, Finset.filter_filter]
  have h1le : (T4.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 9 := by
    rw [← hT4card9]; exact Finset.card_le_card (Finset.filter_subset _ _)
  have h3eq : T4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hT4def, Finset.filter_filter]
  have h4eq : T4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)
      = Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hT4def, Finset.filter_filter]
  have hScard_ge : 7 ≤ S.card := by
    rw [hSeqT4]; rw [hT4iso18, h3eq, h4eq] at hcong; omega
  have hScard_le : S.card ≤ 9 := by rw [← hT4card9]; exact Finset.card_le_card hSsubT4
  -- Loose bound on `Q`.
  have hQ : ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
      - (G.neighborFinset t ∩ S).card) ≤ 36 := by
    have hkey : ∀ c : ℕ, c ≤ 3 → c * c - c ≤ 6 := by
      intro c hc; interval_cases c <;> decide
    have hpt : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card ≤ 6 := by
      intro t ht
      have hc3 : (G.neighborFinset t ∩ S).card ≤ 3 := by
        calc (G.neighborFinset t ∩ S).card
            ≤ (G.neighborFinset t ∩ Hub).card :=
              Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsubHub)
          _ = 3 := hiso3 t ht
      exact hkey _ hc3
    calc ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
          - (G.neighborFinset t ∩ S).card)
        ≤ ∑ _t ∈ Iso, 6 := Finset.sum_le_sum hpt
      _ = 36 := by rw [Finset.sum_const, smul_eq_mul, h6]
  -- `E + I_S ≤ 4·|S|`.
  have hEI : (∑ a ∈ S, (G.neighborFinset a ∩ S).card)
      + (∑ a ∈ S, (G.neighborFinset a ∩ Iso).card) ≤ 4 * S.card := by
    have hpt : ∀ a ∈ S, (G.neighborFinset a ∩ S).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
      intro a ha
      have hda : G.degree a = 4 := by
        rw [hSdef, Finset.mem_filter] at ha; exact ha.2.1
      have hsub : (G.neighborFinset a ∩ S).card ≤ (G.neighborFinset a ∩ Hub).card :=
        Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsubHub)
      have hnb := hub_neighbor_le_seventeen G Hub Iso hdisj a hda
      omega
    have hsum : ∑ a ∈ S, ((G.neighborFinset a ∩ S).card + (G.neighborFinset a ∩ Iso).card)
        ≤ ∑ _a ∈ S, 4 := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm] at hsum
    exact hsum
  -- `I_S ≥ 9 + |S|`.
  have hISge : 9 + S.card ≤ ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card := by
    have hsdiff : ∑ a ∈ T4 \ S, (G.neighborFinset a ∩ Iso).card
        + ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card = 18 := by
      rw [Finset.sum_sdiff hSsubT4]; exact hT4iso18
    have hle1 : ∀ a ∈ T4 \ S, (G.neighborFinset a ∩ Iso).card ≤ 1 := by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      have haT4 := ha.1
      have hd : G.degree a = 4 := by rw [hT4def, Finset.mem_filter] at haT4; exact haT4.2
      have haHub : a ∈ Hub := (Finset.mem_filter.mp haT4).1
      by_contra hgt
      push Not at hgt
      have hmem : a ∈ S := by
        rw [hSdef]; exact Finset.mem_filter.mpr ⟨haHub, hd, by omega⟩
      exact ha.2 hmem
    have hdle : ∑ a ∈ T4 \ S, (G.neighborFinset a ∩ Iso).card ≤ (T4 \ S).card := by
      calc ∑ a ∈ T4 \ S, (G.neighborFinset a ∩ Iso).card
          ≤ ∑ _a ∈ T4 \ S, 1 := Finset.sum_le_sum hle1
        _ = (T4 \ S).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hcardadd : (T4 \ S).card + S.card = T4.card :=
      Finset.card_sdiff_add_card_eq_card hSsubT4
    omega
  -- Combine: the cover inequality rules out `|S| ∈ {8, 9}`, leaving `|S| = 7`.
  have hSval : S.card = 7 := by
    rcases (by omega : S.card = 7 ∨ S.card = 8 ∨ S.card = 9) with h | h | h
    · exact h
    · exfalso; rw [h] at hCI hEI hISge; omega
    · exfalso; rw [h] at hCI hEI hISge; omega
  -- **Residual `|S| = 7`.**  Pin `I_S = 16` via the iso-degree threshold count `hmf`.
  have hT4le4S : ∀ a ∈ S, (G.neighborFinset a ∩ Iso).card ≤ 4 := fun a ha =>
    hT4le4 a (hSsubT4 ha)
  have hge2S : ∀ a ∈ S, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hSdef, Finset.mem_filter] at ha; exact ha.2.2
  have hge3 : S.filter (fun a => 3 ≤ (G.neighborFinset a ∩ Iso).card)
      = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hSdef, Finset.filter_filter]; ext x
    simp only [Finset.mem_filter]; constructor
    · rintro ⟨hx, ⟨hd, _⟩, h3'⟩; exact ⟨hx, hd, h3'⟩
    · rintro ⟨hx, hd, h3'⟩; exact ⟨hx, ⟨hd, by omega⟩, h3'⟩
  have hge4 : S.filter (fun a => 4 ≤ (G.neighborFinset a ∩ Iso).card)
      = Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hSdef, Finset.filter_filter]; ext x
    simp only [Finset.mem_filter]; constructor
    · rintro ⟨hx, ⟨hd, _⟩, h4'⟩; exact ⟨hx, hd, h4'⟩
    · rintro ⟨hx, hd, h4'⟩; exact ⟨hx, ⟨hd, by omega⟩, h4'⟩
  have hdec : ∀ a ∈ S, (G.neighborFinset a ∩ Iso).card
      = 2 + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
    intro a ha; have := hge2S a ha; have := hT4le4S a ha; split_ifs <;> omega
  have hdsum := Finset.sum_congr rfl hdec
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    ← Finset.card_filter, ← Finset.card_filter, hSval, hge3, hge4] at hdsum
  have hIS16 : ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card = 16 := by
    rw [hSval] at hISge; omega
  -- `Q ≤ 30` from the distribution `∑ c_t = 16`, `c_t ≤ 3`.
  have hc3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ S).card
        ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsubHub)
      _ = 3 := hiso3 t ht
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card = 16 := by
    rw [cross_count G Iso S]; exact hIS16
  have hesum : ∑ t ∈ Iso, (3 - (G.neighborFinset t ∩ S).card) = 2 := by
    have hpt : ∀ t ∈ Iso, (3 - (G.neighborFinset t ∩ S).card) + (G.neighborFinset t ∩ S).card = 3 :=
      fun t ht => by have := hc3 t ht; omega
    have h18 := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, h6, hcross] at h18
    omega
  have hele2 : ∀ t ∈ Iso, (3 - (G.neighborFinset t ∩ S).card) ≤ 2 := by
    intro t ht
    have := Finset.single_le_sum
      (f := fun t => 3 - (G.neighborFinset t ∩ S).card) (fun i _ => Nat.zero_le _) ht
    omega
  -- `∑ e_t * c_t + ∑ e_t * e_t = 3 * ∑ e_t = 6` and `∑ e_t * e_t ≤ 4`.
  have hee : ∑ t ∈ Iso, (3 - (G.neighborFinset t ∩ S).card) * (3 - (G.neighborFinset t ∩ S).card)
      ≤ 4 := by
    calc ∑ t ∈ Iso, (3 - (G.neighborFinset t ∩ S).card) * (3 - (G.neighborFinset t ∩ S).card)
        ≤ ∑ t ∈ Iso, 2 * (3 - (G.neighborFinset t ∩ S).card) :=
          Finset.sum_le_sum (fun t ht => Nat.mul_le_mul_right _ (hele2 t ht))
      _ = 2 * ∑ t ∈ Iso, (3 - (G.neighborFinset t ∩ S).card) := by rw [Finset.mul_sum]
      _ = 4 := by rw [hesum]
  have hcc : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card ≤ 46 := by
    have hid : ∀ t ∈ Iso,
        (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
          + 6 * (3 - (G.neighborFinset t ∩ S).card)
          = 9 + (3 - (G.neighborFinset t ∩ S).card) * (3 - (G.neighborFinset t ∩ S).card) := by
      intro t ht
      have hle : (G.neighborFinset t ∩ S).card ≤ 3 := hc3 t ht
      set c := (G.neighborFinset t ∩ S).card with hcv
      clear_value c
      interval_cases c <;> rfl
    have hsumid := Finset.sum_congr rfl hid
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      smul_eq_mul, h6, hesum] at hsumid
    -- hsumid : ∑ cc + 6 * 2 = 9 * 6 + ∑ ee
    omega
  have hcsq : ∀ t : Fin 17, (G.neighborFinset t ∩ S).card ≤
      (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card := by
    intro t
    rcases Nat.eq_zero_or_pos (G.neighborFinset t ∩ S).card with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  have hQ30 : ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
      - (G.neighborFinset t ∩ S).card) ≤ 30 := by
    rw [Finset.sum_tsub_distrib Iso (fun t _ => hcsq t), hcross]
    omega
  -- Cover inequality `49 ≤ 7 + E + Q` with `Q ≤ 30` forces `E ≥ 12`; `hEI` forces `E ≤ 12`.
  have hEval : ∑ a ∈ S, (G.neighborFinset a ∩ S).card = 12 := by
    rw [hSval] at hCI hEI; rw [hIS16] at hEI; omega
  -- **Structure.**  The two `M`-edge endpoints `low = univ \ (Hub ∪ Iso)`.
  set low : Finset (Fin 17) := Finset.univ \ (Hub ∪ Iso) with hlowdef
  have hHIcard : (Hub ∪ Iso).card = 15 := by
    rw [Finset.card_union_of_disjoint hdisj, h9, h6]
  have hlowcard : low.card = 2 := by
    have h := hHIcard
    rw [hlowdef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  -- Partition of each neighbourhood into `Hub`, `Iso`, `low`.
  have hpart : ∀ a : Fin 17, (G.neighborFinset a ∩ low).card
      + ((G.neighborFinset a ∩ Hub).card + (G.neighborFinset a ∩ Iso).card) = G.degree a := by
    intro a
    have hsplit : (G.neighborFinset a ∩ (Hub ∪ Iso)).card
        = (G.neighborFinset a ∩ Hub).card + (G.neighborFinset a ∩ Iso).card := by
      rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj))]
    have hlowinter : G.neighborFinset a ∩ low = G.neighborFinset a \ (Hub ∪ Iso) := by
      rw [hlowdef]; ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    rw [hlowinter, ← hsplit, ← G.card_neighborFinset_eq_degree]
    exact Finset.card_sdiff_add_card_inter _ _
  -- `∑ deg = 28` over `S`.
  have hSdeg : ∑ a ∈ S, G.degree a = 28 := by
    have hd4 : ∀ a ∈ S, G.degree a = 4 :=
      fun a ha => by rw [hSdef, Finset.mem_filter] at ha; exact ha.2.1
    rw [Finset.sum_congr rfl hd4, Finset.sum_const, smul_eq_mul, hSval]
  have hsumpart : ∑ a ∈ S, (G.neighborFinset a ∩ low).card
      + (∑ a ∈ S, (G.neighborFinset a ∩ Hub).card + ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card)
      = 28 := by
    rw [← hSdeg, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => hpart a)
  have hEle : ∑ a ∈ S, (G.neighborFinset a ∩ S).card
      ≤ ∑ a ∈ S, (G.neighborFinset a ∩ Hub).card :=
    Finset.sum_le_sum (fun a _ => Finset.card_le_card
      (Finset.inter_subset_inter (Finset.Subset.refl _) hSsubHub))
  have hSlow0 : ∑ a ∈ S, (G.neighborFinset a ∩ low).card = 0 := by
    rw [hIS16] at hsumpart; omega
  have hSlowzero : ∀ a ∈ S, (G.neighborFinset a ∩ low).card = 0 := by
    intro a ha
    have := Finset.single_le_sum
      (f := fun a => (G.neighborFinset a ∩ low).card) (fun i _ => Nat.zero_le _) ha
    omega
  -- Twins have all neighbours in `Hub`, so `low` vertices have no `Iso` neighbour.
  have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
    intro t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by rw [G.card_neighborFinset_eq_degree, hisodeg t ht, hiso3 t ht])
    rw [← heq]; exact Finset.inter_subset_right
  have hlowIso : ∀ w ∈ low, (G.neighborFinset w ∩ Iso).card = 0 := by
    intro w hw
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, G.mem_neighborFinset] at hx
    have hwHub : w ∈ Hub := htwinHub x hx.2 ((G.mem_neighborFinset x w).mpr hx.1.symm)
    rw [hlowdef, Finset.mem_sdiff] at hw
    exact hw.2 (Finset.mem_union_left _ hwHub)
  -- Each `low` vertex meets `low` in `≤ 1` and `Hub` in `≥ 2` neighbours.
  have hwlow1 : ∀ w ∈ low, (G.neighborFinset w ∩ low).card ≤ 1 := by
    intro w hw
    have hsub : G.neighborFinset w ∩ low ⊆ low \ {w} := by
      intro x hx; rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨hx.2, fun heq => ?_⟩
      rw [heq] at hx; exact G.irrefl ((G.mem_neighborFinset w w).mp hx.1)
    have hc : (low \ {w}).card = 1 := by
      have := hlowcard
      rw [Finset.card_sdiff, Finset.singleton_inter_of_mem hw, Finset.card_singleton]
      omega
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hc)
  have hwHub2 : ∀ w ∈ low, 2 ≤ (G.neighborFinset w ∩ Hub).card := by
    intro w hw
    have hpw := hpart w
    have hiso0 := hlowIso w hw
    have := hwlow1 w hw
    have := h3 w
    omega
  have hlowsum : ∑ w ∈ low, (G.neighborFinset w ∩ Hub).card ≤ 4 := by
    rw [← cross_count G Hub low]; exact hNI
  obtain ⟨u, v, huv, hlowuv⟩ := Finset.card_eq_two.mp hlowcard
  have hu_low : u ∈ low := by rw [hlowuv]; exact Finset.mem_insert_self _ _
  have hv_low : v ∈ low := by rw [hlowuv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hsumuv : (G.neighborFinset u ∩ Hub).card + (G.neighborFinset v ∩ Hub).card ≤ 4 := by
    rw [hlowuv, Finset.sum_pair huv] at hlowsum; exact hlowsum
  have huHub2 : (G.neighborFinset u ∩ Hub).card = 2 := by
    have := hwHub2 u hu_low; have := hwHub2 v hv_low; omega
  have hvHub2 : (G.neighborFinset v ∩ Hub).card = 2 := by
    have := hwHub2 u hu_low; have := hwHub2 v hv_low; omega
  -- The hub-neighbours of `u`, `v` avoid `S`, hence equal `Hub \ S`.
  have hHSdiff : (Hub \ S).card = 2 := by
    have := Finset.card_sdiff_add_card_eq_card hSsubHub
    rw [h9, hSval] at this; omega
  have hsubL : ∀ w ∈ low, G.neighborFinset w ∩ Hub ⊆ Hub \ S := by
    intro w hw h hh
    rw [Finset.mem_inter] at hh
    rw [Finset.mem_sdiff]
    refine ⟨hh.2, ?_⟩
    intro hhS
    have hadj : G.Adj h w := ((G.mem_neighborFinset w h).mp hh.1).symm
    have hmem : w ∈ G.neighborFinset h ∩ low := by
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj, hw⟩
    have hz := hSlowzero h hhS
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hz
    exact hz w hmem
  have huEq : G.neighborFinset u ∩ Hub = Hub \ S :=
    Finset.eq_of_subset_of_card_le (hsubL u hu_low) (by rw [hHSdiff, huHub2])
  have hvEq : G.neighborFinset v ∩ Hub = Hub \ S :=
    Finset.eq_of_subset_of_card_le (hsubL v hv_low) (by rw [hHSdiff, hvHub2])
  -- Pick a hub `ℓ ∈ Hub \ S`; it is adjacent to both `u` and `v`.
  obtain ⟨ℓ, hℓ⟩ := Finset.card_pos.mp (by rw [hHSdiff]; norm_num : 0 < (Hub \ S).card)
  have hℓHub : ℓ ∈ Hub := (Finset.mem_sdiff.mp hℓ).1
  have hℓu : ℓ ∈ G.neighborFinset u ∩ Hub := by rw [huEq]; exact hℓ
  have hℓv : ℓ ∈ G.neighborFinset v ∩ Hub := by rw [hvEq]; exact hℓ
  have hAℓu : G.Adj ℓ u :=
    ((G.mem_neighborFinset u ℓ).mp (Finset.mem_inter.mp hℓu).1).symm
  have hAℓv : G.Adj ℓ v :=
    ((G.mem_neighborFinset v ℓ).mp (Finset.mem_inter.mp hℓv).1).symm
  -- Degrees of `u`, `v` (each `3`) and `u ~ v`.
  have hudeg : G.degree u = 3 ∧ (G.neighborFinset u ∩ low).card = 1 := by
    have hpu := hpart u
    rw [huHub2, hlowIso u hu_low] at hpu
    have := hwlow1 u hu_low; have := h3 u; omega
  have hvdeg : G.degree v = 3 := by
    have hpv := hpart v
    rw [hvHub2, hlowIso v hv_low] at hpv
    have := hwlow1 v hv_low; have := h3 v; omega
  -- `u ~ v` from the `low` structure (`deg u = 3`, exactly one `low` neighbour).
  have hAuv : G.Adj u v := by
    have huNlow : (G.neighborFinset u ∩ low).card = 1 := hudeg.2
    have hsub : G.neighborFinset u ∩ low ⊆ {v} := by
      intro x hx; rw [Finset.mem_inter, hlowuv] at hx
      rw [Finset.mem_singleton]
      rcases Finset.mem_insert.mp hx.2 with h | h
      · exfalso; rw [h] at hx; exact G.irrefl ((G.mem_neighborFinset u u).mp hx.1)
      · exact Finset.mem_singleton.mp h
    have : G.neighborFinset u ∩ low = {v} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [huNlow, Finset.card_singleton])
    have hvmem : v ∈ G.neighborFinset u ∩ low := by rw [this]; exact Finset.mem_singleton_self _
    exact (G.mem_neighborFinset u v).mp (Finset.mem_inter.mp hvmem).1
  -- Degree of `ℓ` is `4` (no degree-`5` hub).
  have hℓdeg : G.degree ℓ = 4 := by
    rcases hdeg45 ℓ hℓHub with h | h
    · exact h
    · exfalso
      have hmem : ℓ ∈ T5 := by rw [hT5def, Finset.mem_filter]; exact ⟨hℓHub, by omega⟩
      rw [Finset.card_eq_zero] at hT5card0
      rw [hT5card0] at hmem; exact Finset.notMem_empty _ hmem
  -- Distinctness: `ℓ ∈ Hub`, `u, v ∈ low` (disjoint from `Hub`).
  have hℓ_not_low : ℓ ∉ low := by
    rw [hlowdef]; simp only [Finset.mem_sdiff, not_and, not_not]
    intro _; exact Finset.mem_union_left _ hℓHub
  have hℓu_ne : ℓ ≠ u := fun h => hℓ_not_low (h ▸ hu_low)
  have hℓv_ne : ℓ ≠ v := fun h => hℓ_not_low (h ▸ hv_low)
  have hudeg3 : G.degree u = 3 := hudeg.1
  exact hT ⟨ℓ, u, v, hℓu_ne, huv, hℓv_ne, hAℓu, hAuv, hAℓv, by omega⟩

end N17

end ACMax
