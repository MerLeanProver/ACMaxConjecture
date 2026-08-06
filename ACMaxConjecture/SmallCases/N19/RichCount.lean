import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates

/-!
# Abstract rich-hub count bounds for the rigid `n = 19` no-two-hub partition

For the tight `e(M) = 1`, all-degree-`4` profile `(|Hub|, |Iso|) = (11, 6)` (the NEW `n = 19`
`|Hub| = 11` regime, the analog of the rigid `n = 18` `(10, 6)` partition), the *rich* hubs are
those meeting `≥ 2` `M`-isolated twins.  This file pins the rich count `r := |R|` using only abstract
counting (`N1` = `rich_nonadj_share_eq_one_nineteen`, `N2` = `rich_a3_count_le_two_nineteen`, the
all-degree-`4` fact, and the no-two-hub hypothesis).

* `rich_count_le_seven_nineteen` (`r ≤ 7`): ports **mechanically** from `n = 18` — `|Iso| = 6` is
  unchanged, so every non-adjacent rich pair has a **unique** common `M`-isolated twin (`N1`) and the
  ordered non-adjacent rich pairs embed into `⋃_t (N(t) ∩ R)²ᵒᶠᶠ`, bounded by `6·(3² − 3) = 36`;
  `r = 8` would force `≥ 8² − 3·8 = 40` such pairs.  **Axiom-clean.**
* `rich_count_ge_six_nineteen` (`r ≥ 6`): the strong bound the star-triangle partition will consume
  downstream.  At `|Hub| = 11` the `n = 18` architecture **genuinely breaks**: there `|Hub| = 10`
  gave `∑_R ≥ 8 + r` and the iso-degree-`4`-hub extraction forced `r ≥ 6`; at `|Hub| = 11` this
  degrades to `∑_R ≥ 7 + r`, and the multiset `{2,2,2,3,3}` (r = 5, no iso-degree-`4` hub) is
  counting-consistent, so the extraction no longer fires.  Closing this is genuinely-new `|Hub| = 11`
  regime work (octahedron / z-meets-2-poor rigidity) — left as **ONE documented `sorry`**.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- `k ≤ 3 ⟹ k² − k ≤ 6` (the off-diagonal cardinality of a `≤ 3`-element twin trace). -/
theorem offdiag_trace_le_six_nineteen (k : ℕ) (hk : k ≤ 3) : k * k - k ≤ 6 := by
  interval_cases k <;> decide

/-- **`r ≤ 7` — abstract rich-count upper bound.**  With all hubs degree `4` and each `M`-isolated
twin meeting exactly three hubs, the rich hubs `R = {h : 2 ≤ |N(h) ∩ Iso|}` satisfy `|R| ≤ 7`.
Ports mechanically from `n = 18` since `|Iso| = 6` is unchanged. -/
theorem rich_count_le_seven_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 7 := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set r : ℕ := R.card with hrdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hr11 : r ≤ 11 := by rw [hrdef, ← hHub]; exact Finset.card_le_card hRsubHub
  -- Membership facts for `R`.
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  -- Each rich hub has `≤ 2` hub-neighbours inside `R`.
  have hRnbr : ∀ a ∈ R, (G.neighborFinset a ∩ R).card ≤ 2 := by
    intro a ha
    obtain ⟨haHub, hae⟩ := (hRmem a).mp ha
    have hd4 : (G.neighborFinset a).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hdeg4 a haHub]
    have hdisjNR : Disjoint (G.neighborFinset a ∩ R) (G.neighborFinset a ∩ Iso) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj (hRsubHub (Finset.mem_inter.mp hx1).2)
        (Finset.mem_inter.mp hx2).2
    have hun : (G.neighborFinset a ∩ R) ∪ (G.neighborFinset a ∩ Iso) ⊆ G.neighborFinset a := by
      rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
    have hle := Finset.card_le_card hun
    rw [Finset.card_union_of_disjoint hdisjNR, hd4] at hle
    omega
  -- Off-diagonal of `R`.
  set Off : Finset (Fin 19 × Fin 19) := R.offDiag with hOffdef
  have hOffcard : Off.card = r * r - r := by rw [hOffdef, Finset.offDiag_card]
  set Dadj : Finset (Fin 19 × Fin 19) := Off.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  set D : Finset (Fin 19 × Fin 19) := Off.filter (fun p => ¬G.Adj p.1 p.2) with hDdef
  have hDsplit : D.card + Dadj.card = Off.card := by
    rw [hDdef, hDadjdef, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  -- Upper bound on `Dadj`: `≤ 2r` via fibering on the first coordinate.
  have hDadjle : Dadj.card ≤ 2 * r := by
    have hmaps : (Dadj : Set (Fin 19 × Fin 19)).MapsTo Prod.fst R := by
      intro p hp
      rw [hDadjdef, Finset.coe_filter] at hp
      have hpoff : p ∈ Off := hp.1
      rw [hOffdef, Finset.mem_offDiag] at hpoff
      exact hpoff.1
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc ∑ a ∈ R, (Dadj.filter (fun p => p.1 = a)).card
        ≤ ∑ _a ∈ R, 2 := by
          apply Finset.sum_le_sum
          intro a ha
          have hsub : Dadj.filter (fun p => p.1 = a) ⊆ (G.neighborFinset a ∩ R).map
              ⟨fun b => (a, b), fun b₁ b₂ h => by simpa using h⟩ := by
            intro p hp
            rw [Finset.mem_filter, hDadjdef, Finset.mem_filter, hOffdef,
              Finset.mem_offDiag] at hp
            obtain ⟨⟨⟨hp1R, hp2R, _⟩, hadj⟩, hfst⟩ := hp
            rw [Finset.mem_map]
            refine ⟨p.2, ?_, ?_⟩
            · rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨hfst ▸ hadj, hp2R⟩
            · rw [← hfst]
              exact Prod.eta p
          calc (Dadj.filter (fun p => p.1 = a)).card
              ≤ ((G.neighborFinset a ∩ R).map _).card := Finset.card_le_card hsub
            _ = (G.neighborFinset a ∩ R).card := Finset.card_map _
            _ ≤ 2 := hRnbr a ha
      _ = 2 * r := by rw [Finset.sum_const, smul_eq_mul, hrdef, mul_comm]
  -- Upper bound on `D`: each non-adjacent rich pair lies in a twin's off-diagonal trace.
  have hDbiU : D ⊆ Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) := by
    intro p hp
    rw [hDdef, Finset.mem_filter, hOffdef, Finset.mem_offDiag] at hp
    obtain ⟨⟨hp1R, hp2R, hne⟩, hnadj⟩ := hp
    obtain ⟨hp1Hub, hp1e⟩ := (hRmem p.1).mp hp1R
    obtain ⟨hp2Hub, hp2e⟩ := (hRmem p.2).mp hp2R
    have hsh1 := rich_nonadj_share_eq_one_nineteen G Hub Iso hshare hno2hub p.1 p.2 hp1Hub hp2Hub
      (hdeg4 p.1 hp1Hub) (hdeg4 p.2 hp2Hub) hne hnadj hp1e hp2e
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (by rw [hsh1]; norm_num)
    rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
    obtain ⟨⟨ht1, ht2⟩, htIso⟩ := ht
    rw [Finset.mem_biUnion]
    refine ⟨t, htIso, ?_⟩
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, hne⟩
    · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht1.symm, hp1R⟩
    · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht2.symm, hp2R⟩
  have hDle : D.card ≤ 36 := by
    calc D.card ≤ (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card :=
          Finset.card_le_card hDbiU
      _ ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).offDiag).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ Iso, 6 := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.offDiag_card]
          have hk3 : (G.neighborFinset t ∩ R).card ≤ 3 := by
            calc (G.neighborFinset t ∩ R).card
                ≤ (G.neighborFinset t ∩ Hub).card :=
                  Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsubHub)
              _ = 3 := hiso3 t ht
          exact offdiag_trace_le_six_nineteen _ hk3
      _ = 36 := by rw [Finset.sum_const, hIso, smul_eq_mul]
  -- Combine: `r*r - r = D + Dadj ≤ 36 + 2r`, ruling out `r ≥ 8`.
  interval_cases r <;> omega

/-- **`r ≥ 6` — the strong rich-count lower bound (the star-triangle partition input).**

The `n = 18` proof (`rich_count_ge_six_eighteen`) reached `r ≥ 6` from `∑_R ≥ 8 + r` (forced by
`|Hub| = 10`) followed by an iso-degree-`4`-hub extraction and a two-hub contradiction.  At the
NEW `n = 19` `|Hub| = 11` regime this **genuinely breaks**: `|Hub| = 11` only gives `∑_R ≥ 7 + r`
(see `rich_count_ge_three_nineteen`), and the iso-degree multiset `{2,2,2,3,3}` (`r = 5`, no
iso-degree-`4` hub) is counting-consistent, so the extraction never fires.

The residual `r = 5`, `∑_R isoDeg = 12` is **threaded as a hypothesis** `hoct5` (rather than left as a
raw `sorry`), keeping this lemma fully axiom-clean.  `hoct5` is exactly the `r = 5` octahedron
residual that the deeper `z`-meets-2-poor / poor-`Z` layout layer (`TwinCert19OctahedronPoorForce`,
above `TwinCert19RichZdeg` in the import order) discharges; it **cannot be invoked here** because the
import DAG is `RichZdeg → RichCount` and `OctahedronPoorForce → RichZdeg`, so calling the octahedron
force from `RichCount` would be a cycle.

* **Why `r = 5`, `S = 12` is the unique residual.**  With `∑_R ≥ 7 + r` (poor side `≤ 11 − r`,
  every poor hub iso-degree `≤ 1`) and `N2` (`rich_a3_count_le_two_nineteen`, `≤ 2` rich hubs of
  iso-degree `≥ 3`) capping `S ≤ 2r + 2`, one gets `r ≥ 3`.  For `r ∈ {3, 4}` and for `r = 5` with
  `S ∈ {13, 14}` the profile **forces an iso-degree-`4` hub `a` together with a second
  iso-degree-`≥ 3` hub `b`** (else `S ≤ 2r + 2` collapses to `r = 5, S = 12`); then `a` has
  `N(a) ⊆ Iso` (non-adjacent to every hub) and `a, b` each keep `≥ 2` private twins (share `≤ 1`),
  a good two-hub pair contradicting `hno2hub` — the exact `n = 18` extraction.  The **only** survivor
  is `r = 5`, `S = 12`: the multisets `{2,2,2,3,3}` (no iso-degree-`4` hub) and `{4,2,2,2,2}` (an
  iso-degree-`4` hub but no second iso-degree-`≥ 3` hub), neither killed by the extraction.
* **Why pure counting / certs are insufficient there.**  The handshake `E(R,P) + z_R = 2a` is
  satisfiable for every `a`, and an exhaustive construction search (468 distinct realisations,
  recorded in `TwinCert19OctahedronForce`) confirms the bipartite incidence + `hshare` + `hno2hub`
  admit `{2,2,2,3,3}` with **no good triangle / C₄ / K₂,₃ at the incidence level**.  Excluding it
  requires the per-subcase poor/`Z` layout layer.

Closing the threaded `hoct5` is the job of `TwinCert19OctahedronPoorForce` /
`TwinCert19RichZdeg` / the `z`-meets-2-poor dispatch. -/
theorem rich_count_ge_six_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hoct5 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 →
      (∑ a ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset a ∩ Iso).card) = 12 → ZPoorCutConfig G) :
    6 ≤ (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ∨ ZPoorCutConfig G := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  -- iso-degree bounded by `4` everywhere on `Hub`.
  have hisole4 : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    calc (G.neighborFinset a ∩ Iso).card ≤ (G.neighborFinset a).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 a ha]
  rcases Nat.lt_or_ge R.card 6 with hlt | hge6
  on_goal 2 => exact Or.inl hge6
  refine Or.inr ?_
  set r : ℕ := R.card with hrdef
  have hr5 : r ≤ 5 := by omega
  set S : ℕ := ∑ a ∈ R, (G.neighborFinset a ∩ Iso).card with hSdef
  -- Total iso-incidences = 18.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- Split over `R` and its complement in `Hub`.
  have hsplit : S
      + ∑ a ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset a ∩ Iso).card
      = ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card := by
    rw [hSdef, hRdef]
    exact Finset.sum_filter_add_sum_filter_not Hub _ _
  -- Poor hubs carry iso-degree `≤ 1`, so `≤ |Hub \ R| = 11 - r`.
  have hpoorle : ∑ a ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset a ∩ Iso).card ≤ 11 - r := by
    have hcardP : (Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 11 - r := by
      have := Finset.card_filter_add_card_filter_not (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
        (s := Hub)
      rw [← hRdef] at this; rw [hHub] at this; omega
    calc ∑ a ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset a ∩ Iso).card
        ≤ ∑ _a ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card), 1 := by
          apply Finset.sum_le_sum
          intro a ha; rw [Finset.mem_filter] at ha; omega
      _ = 11 - r := by rw [Finset.sum_const, smul_eq_mul, mul_one, hcardP]
  have hRlower : 7 + r ≤ S := by omega
  -- `N2`: at most two rich hubs have iso-degree `≥ 3`.
  have hN2 : (R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
    have heq : R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hRdef, Finset.filter_filter]; apply Finset.filter_congr
      intro a ha; constructor
      · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
      · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
    rw [heq]
    exact rich_a3_count_le_two_nineteen G Hub Iso hdisj hshare hno2hub
  -- The unique residual: `r = 5`, `S = 12`.  Everything else admits the `n = 18` extraction.
  by_cases hres5 : r = 5 ∧ S = 12
  · exact hoct5 hres5.1 hres5.2
  · push Not at hres5  -- `hres5 : r = 5 → S ≠ 12`
    -- Extract an iso-degree-`4` rich hub `a`.
    obtain ⟨a, haR, ha4⟩ : ∃ a ∈ R, (G.neighborFinset a ∩ Iso).card = 4 := by
      by_contra hcon
      push Not at hcon
      have hbound : S
          ≤ ∑ a ∈ R, (2 + if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
        rw [hSdef]
        apply Finset.sum_le_sum
        intro a ha
        have h2 := ((hRmem a).mp ha).2
        have h4 : (G.neighborFinset a ∩ Iso).card ≤ 4 := hisole4 a (hRsubHub ha)
        have hne4 := hcon a ha
        split_ifs with h3 <;> omega
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.card_filter] at hbound
      have hr5val : r = 5 := by omega
      exact hres5 hr5val (by omega)
    obtain ⟨haHub, _⟩ := (hRmem a).mp haR
    -- `N(a) ⊆ Iso`.
    have haIso : G.neighborFinset a ⊆ Iso := by
      have hd4 : (G.neighborFinset a).card = 4 := by
        rw [G.card_neighborFinset_eq_degree, hdeg4 a haHub]
      have heq : G.neighborFinset a ∩ Iso = G.neighborFinset a :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hd4, ha4])
      rw [← heq]; exact Finset.inter_subset_right
    -- Extract a second iso-degree-`≥ 3` rich hub `b ≠ a`.
    obtain ⟨b, hbR, hbne, hb3⟩ : ∃ b ∈ R, b ≠ a ∧ 3 ≤ (G.neighborFinset b ∩ Iso).card := by
      by_contra hcon
      push Not at hcon
      have hbound : S ≤ ∑ x ∈ R, (2 + if x = a then 2 else 0) := by
        rw [hSdef]
        apply Finset.sum_le_sum
        intro x hx
        by_cases hxa : x = a
        · subst hxa; rw [if_pos rfl]; have := hisole4 x (hRsubHub hx); omega
        · rw [if_neg hxa]; have := hcon x hx hxa; omega
      have hif : ∑ x ∈ R, (if x = a then (2 : ℕ) else 0) = 2 := by
        rw [Finset.sum_ite_eq' R a (fun _ => (2 : ℕ)), if_pos haR]
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hif] at hbound
      have hr5val : r = 5 := by omega
      exact hres5 hr5val (by omega)
    obtain ⟨hbHub, _⟩ := (hRmem b).mp hbR
    -- `a` is non-adjacent to `b`.
    have hnadj : ¬G.Adj a b := by
      intro hadj
      have hbN : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hadj
      exact Finset.disjoint_left.mp hdisj hbHub (haIso hbN)
    -- Share `≤ 1`; private twins on each side.
    have hsh : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card ≤ 1 :=
      hshare a haHub (hdeg4 a haHub) b hbHub (hdeg4 b hbHub) hbne.symm hnadj
    have hpa : 2 ≤ ((G.neighborFinset a ∩ Iso) \ G.neighborFinset b).card := by
      have hk := Finset.card_sdiff_add_card_inter (G.neighborFinset a ∩ Iso) (G.neighborFinset b)
      have hi : (G.neighborFinset a ∩ Iso) ∩ G.neighborFinset b
          = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := Finset.inter_right_comm _ _ _
      rw [hi] at hk; rw [ha4] at hk; omega
    have hpb : 2 ≤ ((G.neighborFinset b ∩ Iso) \ G.neighborFinset a).card := by
      have hk := Finset.card_sdiff_add_card_inter (G.neighborFinset b ∩ Iso) (G.neighborFinset a)
      have hi : (G.neighborFinset b ∩ Iso) ∩ G.neighborFinset a
          = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
        rw [Finset.inter_right_comm, Finset.inter_comm (G.neighborFinset b) (G.neighborFinset a)]
      rw [hi] at hk; omega
    exact (hno2hub ⟨a, b, haHub, hbHub, hdeg4 a haHub, hdeg4 b hbHub, Ne.symm hbne, hnadj,
      hpa, hpb⟩).elim

end N19

end ACMax
