import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.PairCount

/-!
# Hub-pair selection for the `n = 14` two-hub iso-degree-`4` **corner**

This file supplies the corner (`at most one hub of iso-degree 4`) selection feeding
`two_hub_pair_select_fourteen` (in `TwinCert14TwoHubSelect`).  All three declarations are now
`sorry`-free: the selection is only invoked at `e(M) = 1` (`|Iso| = 6` exactly), so the former
`|Iso| = 5` residual (the false `iso5_lowprofile_pair` corner) is unreachable and has been removed.

* `exists_hub_pair_share_le_one_fourteen` (**NODE A**) — a clean double-count pigeonhole: given a
  hub set with `5 ≤ |Hub|`, each isolated twin meeting `≤ 3` hubs, and `|Iso| ≤ 6`, two distinct
  hubs share at most one isolated twin.  (Generalises the `n = 13` `exists_hub_pair_low_share`:
  `Hub.card = 6 ⇒ 5 ≤ Hub.card` and the per-twin `= 3` weakens to `≤ 3`, so it applies to any
  big-hub *subset*.)
* `two_hub_corner_select` (**NODE B1 + wiring**) — applies NODE A to the `≥ 3`-iso-degree hubs and,
  whenever the resulting low-share pair is **non-adjacent**, extracts the two private-twin bounds.
  The remaining configurations are deferred to `two_hub_corner_b2`.
* `two_hub_corner_b2` — the `(4,3,3,3,3,2)` profile pigeonhole at `|Iso| = 6` (`hIso6`): five strong
  hubs and one weak degree-`2` hub, yielding a non-adjacent strong-strong low-share pair.  Now fully
  proved (the `|Iso| = 5` branch is excluded by the `Iso.card = 6` hypothesis).
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **NODE A — low-share hub pair (double count).**  For a hub set with `5 ≤ |Hub|`, where every
isolated twin meets at most three hubs (`hiso3`) and `|Iso| ≤ 6` (`hIso6`), the ordered double
count `∑_{h₁,h₂∈Hub}|N h₁ ∩ N h₂ ∩ Iso| ≤ 3·∑_{h}|N h ∩ Iso| ≤ 9|Iso|`, while its diagonal is
`∑_{h}|N h ∩ Iso| = ∑_{t}|N t ∩ Hub| ≤ 3|Iso| ≤ 18`.  If every distinct pair shared `≥ 2`, each row
would exceed its diagonal by `2·(|Hub|−1) ≥ 8`, forcing `∑_{h}|N h∩Iso| ≥ 4|Hub| ≥ 20 > 18`.  Hence
some distinct pair shares at most one isolated twin. -/
theorem exists_hub_pair_share_le_one_fourteen (G : SimpleGraph (Fin 14))
    (Hub Iso : Finset (Fin 14)) (hHub5 : 5 ≤ Hub.card)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card ≤ 3)
    (hIso6 : Iso.card ≤ 6) :
    ∃ h₁ h₂ : Fin 14, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ h₁ ≠ h₂ ∧
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 := by
  classical
  set T : ℕ := ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card with hTdef
  have hT_eq : T = ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card := by
    rw [hTdef]; exact cross_count_fourteen G Hub Iso
  have hT_le : T ≤ 3 * Iso.card := by
    rw [hT_eq]
    calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
        ≤ ∑ _t ∈ Iso, 3 := Finset.sum_le_sum (fun t ht => hiso3 t ht)
      _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hUpper : ∑ h₁ ∈ Hub, ∑ h₂ ∈ Hub,
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 3 * T := by
    have hrow : ∀ h₁ ∈ Hub,
        ∑ h₂ ∈ Hub, (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card
          ≤ 3 * (G.neighborFinset h₁ ∩ Iso).card := by
      intro h₁ _
      have hset : ∀ h₂ : Fin 14, G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso
          = G.neighborFinset h₂ ∩ (G.neighborFinset h₁ ∩ Iso) := by
        intro h₂
        rw [Finset.inter_comm (G.neighborFinset h₁) (G.neighborFinset h₂), Finset.inter_assoc]
      rw [Finset.sum_congr rfl (fun h₂ _ => by rw [hset h₂]),
        cross_count_fourteen G Hub (G.neighborFinset h₁ ∩ Iso)]
      calc ∑ t ∈ (G.neighborFinset h₁ ∩ Iso), (G.neighborFinset t ∩ Hub).card
          ≤ ∑ _t ∈ (G.neighborFinset h₁ ∩ Iso), 3 :=
            Finset.sum_le_sum (fun t ht => hiso3 t (Finset.mem_inter.mp ht).2)
        _ = 3 * (G.neighborFinset h₁ ∩ Iso).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
    calc ∑ h₁ ∈ Hub, ∑ h₂ ∈ Hub,
          (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card
        ≤ ∑ h₁ ∈ Hub, 3 * (G.neighborFinset h₁ ∩ Iso).card := Finset.sum_le_sum hrow
      _ = 3 * T := by rw [← Finset.mul_sum, ← hTdef]
  by_contra hcon
  push Not at hcon
  have hge2 : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ →
      2 ≤ (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
    intro h₁ hh₁ h₂ hh₂ hne; have := hcon h₁ h₂ hh₁ hh₂ hne; omega
  have hLower : T + Hub.card * 8 ≤ ∑ h₁ ∈ Hub, ∑ h₂ ∈ Hub,
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
    have hper : ∀ h₁ ∈ Hub,
        (G.neighborFinset h₁ ∩ Iso).card + 8
          ≤ ∑ h₂ ∈ Hub, (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
      intro h₁ hh₁
      have hdiagh : (G.neighborFinset h₁ ∩ G.neighborFinset h₁ ∩ Iso).card
          = (G.neighborFinset h₁ ∩ Iso).card := by rw [Finset.inter_self]
      have hisol := Finset.add_sum_erase Hub
        (fun h₂ => (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card) hh₁
      have herasege : 2 * (Hub.erase h₁).card
          ≤ ∑ h₂ ∈ Hub.erase h₁, (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
        have hb : ∀ h₂ ∈ Hub.erase h₁,
            2 ≤ (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
          intro h₂ hh₂
          exact hge2 h₁ hh₁ h₂ (Finset.mem_of_mem_erase hh₂)
            (Ne.symm (Finset.ne_of_mem_erase hh₂))
        have h := Finset.card_nsmul_le_sum (Hub.erase h₁)
          (fun h₂ => (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card) 2 hb
        simpa [smul_eq_mul, mul_comm] using h
      have hec : 4 ≤ (Hub.erase h₁).card := by
        rw [Finset.card_erase_of_mem hh₁]; omega
      rw [hdiagh] at hisol
      omega
    have hsplit : ∑ h₁ ∈ Hub, ((G.neighborFinset h₁ ∩ Iso).card + 8) = T + Hub.card * 8 := by
      rw [Finset.sum_add_distrib, ← hTdef, Finset.sum_const, smul_eq_mul]
    rw [← hsplit]; exact Finset.sum_le_sum hper
  omega

/-- **KEY counting lemma — many low-share hub pairs (exact double count).**  In the iso-degree
corner with six hubs (`hHub6`), every isolated twin meeting exactly three hubs (`hiso3`) and
`|Iso| ≤ 6` (`hIso6`), the ordered off-diagonal share double count is exact:
`∑_{(h₁,h₂)∈Hub.offDiag}|N h₁∩N h₂∩Iso| = 9|Iso| − 3|Iso| = 6|Iso| ≤ 36` (each twin sits in
`3·2 = 6` ordered hub pairs).  Since each ordered pair of share `≥ 2` contributes `≥ 2`, at most
`18` ordered pairs have share `≥ 2`, so at least `30 − 18 = 12` of the `30` ordered off-diagonal
hub pairs share at most one isolated twin. -/
theorem two_hub_corner_pair_count (G : SimpleGraph (Fin 14)) (Hub Iso : Finset (Fin 14))
    (hHub6 : Hub.card = 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hIso6 : Iso.card ≤ 6) :
    12 ≤ (Hub.offDiag.filter
      (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1)).card := by
  classical
  let F : Fin 14 → Fin 14 → ℕ :=
    fun a b => (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
  show 12 ≤ (Hub.offDiag.filter (fun p => F p.1 p.2 ≤ 1)).card
  have hT : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 3 * Iso.card := by
    rw [cross_count_fourteen G Hub Iso]
    calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
        = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
      _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hrow : ∀ a : Fin 14, ∑ b ∈ Hub, F a b = 3 * (G.neighborFinset a ∩ Iso).card := by
    intro a
    have hset : ∀ b : Fin 14, F a b = (G.neighborFinset b ∩ (G.neighborFinset a ∩ Iso)).card := by
      intro b
      show (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
        = (G.neighborFinset b ∩ (G.neighborFinset a ∩ Iso)).card
      rw [Finset.inter_comm (G.neighborFinset a) (G.neighborFinset b), Finset.inter_assoc]
    rw [Finset.sum_congr rfl (fun b _ => hset b),
      cross_count_fourteen G Hub (G.neighborFinset a ∩ Iso)]
    calc ∑ t ∈ (G.neighborFinset a ∩ Iso), (G.neighborFinset t ∩ Hub).card
        = ∑ _t ∈ (G.neighborFinset a ∩ Iso), 3 :=
          Finset.sum_congr rfl (fun t ht => hiso3 t (Finset.mem_inter.mp ht).2)
      _ = 3 * (G.neighborFinset a ∩ Iso).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hprod : ∑ p ∈ Hub ×ˢ Hub, F p.1 p.2 = 9 * Iso.card := by
    rw [Finset.sum_product', Finset.sum_congr rfl (fun a _ => hrow a), ← Finset.mul_sum, hT]
    ring
  have hdiagval : ∀ a : Fin 14, F a a = (G.neighborFinset a ∩ Iso).card := by
    intro a
    show (G.neighborFinset a ∩ G.neighborFinset a ∩ Iso).card = (G.neighborFinset a ∩ Iso).card
    rw [Finset.inter_self]
  have hdiagsum : ∑ p ∈ Hub.diag, F p.1 p.2 = 3 * Iso.card := by
    rw [Finset.diag, Finset.sum_map]
    change ∑ a ∈ Hub, F a a = _
    rw [Finset.sum_congr rfl (fun a _ => hdiagval a), hT]
  have hsplit : ∑ p ∈ Hub.diag, F p.1 p.2 + ∑ p ∈ Hub.offDiag, F p.1 p.2
      = ∑ p ∈ Hub ×ˢ Hub, F p.1 p.2 := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag Hub), Finset.diag_union_offDiag]
  have hoffsum : ∑ p ∈ Hub.offDiag, F p.1 p.2 = 6 * Iso.card := by
    rw [hdiagsum, hprod] at hsplit; omega
  have hcard : Hub.offDiag.card = 30 := by rw [Finset.offDiag_card, hHub6]
  have hsplit2 : (Hub.offDiag.filter (fun p => F p.1 p.2 ≤ 1)).card
      + (Hub.offDiag.filter (fun p => ¬ F p.1 p.2 ≤ 1)).card = Hub.offDiag.card :=
    Finset.card_filter_add_card_filter_not (s := Hub.offDiag) (fun p => F p.1 p.2 ≤ 1)
  have hcompl_le : 2 * (Hub.offDiag.filter (fun p => ¬ F p.1 p.2 ≤ 1)).card ≤ 6 * Iso.card := by
    have hstep : ∑ p ∈ Hub.offDiag.filter (fun p => ¬ F p.1 p.2 ≤ 1), F p.1 p.2 ≤ 6 * Iso.card := by
      calc ∑ p ∈ Hub.offDiag.filter (fun p => ¬ F p.1 p.2 ≤ 1), F p.1 p.2
          ≤ ∑ p ∈ Hub.offDiag, F p.1 p.2 :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 6 * Iso.card := hoffsum
    have hlb : 2 * (Hub.offDiag.filter (fun p => ¬ F p.1 p.2 ≤ 1)).card
        ≤ ∑ p ∈ Hub.offDiag.filter (fun p => ¬ F p.1 p.2 ≤ 1), F p.1 p.2 := by
      have h := Finset.card_nsmul_le_sum (Hub.offDiag.filter (fun p => ¬ F p.1 p.2 ≤ 1))
        (fun p => F p.1 p.2) 2 (fun p hp => by have := (Finset.mem_filter.mp hp).2; omega)
      simpa [smul_eq_mul, mul_comm] using h
    omega
  omega

/-- **B2 residual.**  Splits on the number of **iso-degree-`4`** hubs.

* `2 ≤` such hubs (`hn4`): *clean, fully proved.*  Two distinct hubs `h₁, h₂` with
  `|N hᵢ ∩ Iso| = 4 = deg hᵢ` have `N hᵢ ⊆ Iso`; if they were adjacent both would lie in `Iso`,
  contradicting `hisoIndep`, so the pair is **non-adjacent** and `hshare` bounds their shared
  twins by `2`.  Then `private = |N hᵢ| − share = 4 − share ≥ 2` on each side
  (`Finset.card_sdiff_add_card_inter`).
* `≤ 1` such hub (`¬ hn4`): split again on whether **every hub is iso-degree `≥ 3`**.
  * *All hubs strong* (`hallstrong`): *clean, fully proved.*  `two_hub_corner_pair_count` gives
    `≥ 12` ordered low-share off-diagonal pairs and `hub_offDiag_adj_le_four` bounds the adjacent
    ones by `4`, so the non-adjacent low-share set is nonempty; its endpoints are both strong, each
    keeping `private = |N hᵢ ∩ Iso| − share ≥ 3 − 1 = 2` (`Finset.card_sdiff_add_card_inter`).
  * *Some weak hub* (`¬ hallstrong`, iso-degree `≤ 2`): `|Iso| = 6` (hypothesis `hIso6`), *clean,
    fully proved.*  The profile is forced to `(4,3,3,3,3,2)` (`≤ 1` iso-degree-`4` hub plus
    `∑ isoDeg = 18`): five strong hubs `S` and one weak hub `w` of iso-degree `2`.  Summing
    `per_vertex_share_sum_erase` over `S` and subtracting the `w`-column gives the exact
    strong-strong off-diagonal share `∑_{S.offDiag} = 28`, so `filter_le_one_card_ge` yields `≥ 6`
    low-share strong pairs; `hub_offDiag_adj_le_four` removes the `≤ 4` adjacent ones, leaving a
    non-adjacent strong-strong low-share pair with `private ≥ 3 − 1 = 2` each.  (The former
    `|Iso| = 5` residual is excluded: this corner is reached only at `e(M) = 1`, where `|Iso| = 6`.)
-/
theorem two_hub_corner_b2 (G : SimpleGraph (Fin 14)) (Hub Iso : Finset (Fin 14))
    (_hHub6 : Hub.card = 6)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (_hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 4)
    (hIso6 : Iso.card = 6)
    (_hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b)
    (hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2) :
    ∃ h₁ h₂ : Fin 14, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_cases hn4 : 1 < (Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4)).card
  · obtain ⟨h₁, hh₁, h₂, hh₂, hne⟩ := Finset.one_lt_card.mp hn4
    rw [Finset.mem_filter] at hh₁ hh₂
    obtain ⟨hh₁Hub, hh₁4⟩ := hh₁
    obtain ⟨hh₂Hub, hh₂4⟩ := hh₂
    have hsub : ∀ h : Fin 14, h ∈ Hub → (G.neighborFinset h ∩ Iso).card = 4 →
        G.neighborFinset h ⊆ Iso := by
      intro h hhHub hh4
      have hdeg : (G.neighborFinset h).card = 4 := by
        rw [G.card_neighborFinset_eq_degree]; exact hdeg4 h hhHub
      have heq : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hdeg, hh4]))
      rw [← heq]; exact Finset.inter_subset_right
    have hN1 : G.neighborFinset h₁ ⊆ Iso := hsub h₁ hh₁Hub hh₁4
    have hN2 : G.neighborFinset h₂ ⊆ Iso := hsub h₂ hh₂Hub hh₂4
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      have h2iso : h₂ ∈ Iso := hN1 (by rw [G.mem_neighborFinset]; exact hadj)
      have h1iso : h₁ ∈ Iso := hN2 (by rw [G.mem_neighborFinset]; exact hadj.symm)
      exact hisoIndep h₁ h1iso h₂ h2iso hadj
    have hsh : (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2 :=
      hshare h₁ hh₁Hub h₂ hh₂Hub hne hnadj
    refine ⟨h₁, h₂, hh₁Hub, hh₂Hub, hdeg4 h₁ hh₁Hub, hdeg4 h₂ hh₂Hub, hne, hnadj, ?_, ?_⟩
    · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
        (G.neighborFinset h₂)
      have hinter : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
          = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := Finset.inter_right_comm _ _ _
      rw [hinter, hh₁4] at hkey
      omega
    · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso)
        (G.neighborFinset h₁)
      have hinter : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset h₁
          = G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso := Finset.inter_right_comm _ _ _
      have hsh2 : (G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso).card ≤ 2 := by
        rw [Finset.inter_comm (G.neighborFinset h₂) (G.neighborFinset h₁)]; exact hsh
      rw [hinter, hh₂4] at hkey
      omega
  · by_cases hallstrong : ∀ h ∈ Hub, 3 ≤ (G.neighborFinset h ∩ Iso).card
    · -- Every hub has iso-degree `≥ 3`.  `two_hub_corner_pair_count` gives `≥ 12` ordered
      -- low-share off-diagonal pairs, `hub_offDiag_adj_le_four` bounds the adjacent ones by `4`, so
      -- a non-adjacent low-share pair exists; both endpoints are strong, keeping `≥ 3 − 1 = 2`
      -- private isolated twins each.
      have hcount := two_hub_corner_pair_count G Hub Iso _hHub6 _hiso3 (le_of_eq hIso6)
      have hadjle := hub_offDiag_adj_le_four G Hub _hHubsum
      have hne : ((Hub.offDiag.filter
          (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1)) \
          (Hub.offDiag.filter (fun p => G.Adj p.1 p.2))).Nonempty := by
        rw [← Finset.card_pos]
        have hge := Finset.le_card_sdiff
          (Hub.offDiag.filter (fun p => G.Adj p.1 p.2))
          (Hub.offDiag.filter
            (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1))
        omega
      obtain ⟨p, hp⟩ := hne
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨hpoff, hpsh⟩, hpadj⟩ := hp
      obtain ⟨hp1Hub, hp2Hub, hp12⟩ := Finset.mem_offDiag.mp hpoff
      have hnadj : ¬G.Adj p.1 p.2 := fun h => hpadj ⟨hpoff, h⟩
      have ha3 : 3 ≤ (G.neighborFinset p.1 ∩ Iso).card := hallstrong p.1 hp1Hub
      have hb3 : 3 ≤ (G.neighborFinset p.2 ∩ Iso).card := hallstrong p.2 hp2Hub
      refine ⟨p.1, p.2, hp1Hub, hp2Hub, hdeg4 p.1 hp1Hub, hdeg4 p.2 hp2Hub, hp12, hnadj, ?_, ?_⟩
      · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset p.1 ∩ Iso)
          (G.neighborFinset p.2)
        have hinter : (G.neighborFinset p.1 ∩ Iso) ∩ G.neighborFinset p.2
            = G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso := Finset.inter_right_comm _ _ _
        rw [hinter] at hkey
        omega
      · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset p.2 ∩ Iso)
          (G.neighborFinset p.1)
        have hinter : (G.neighborFinset p.2 ∩ Iso) ∩ G.neighborFinset p.1
            = G.neighborFinset p.2 ∩ G.neighborFinset p.1 ∩ Iso := Finset.inter_right_comm _ _ _
        have hsh2 : (G.neighborFinset p.2 ∩ G.neighborFinset p.1 ∩ Iso).card ≤ 1 := by
          rw [Finset.inter_comm (G.neighborFinset p.2) (G.neighborFinset p.1)]; exact hpsh
        rw [hinter] at hkey
        omega
    · -- Some weak hub (iso-degree `≤ 2`).  Pin `|Iso| ∈ {5,6}` and close `|Iso| = 6`.
      have hdle4 : ∀ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≤ 4 := by
        intro h hh
        have hle : (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
        rwa [G.card_neighborFinset_eq_degree, hdeg4 h hh] at hle
      have hsum : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 3 * Iso.card := by
        rw [cross_count_fourteen G Hub Iso]
        calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
            = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => _hiso3 t ht)
          _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      -- `|Iso| = 6` (forced by hypothesis): profile pinned to `(4,3,3,3,3,2)` — five strong hubs,
      -- one weak of degree 2.  (The `|Iso| = 5` corner is excluded: this branch is only reached
      -- for `e(M) = 1`, where `|Iso| = 6`, so the false `iso5_lowprofile_pair` residual is gone.)
      · have hI6 : Iso.card = 6 := hIso6
        set S : Finset (Fin 14) :=
          Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hSdef
        set W : Finset (Fin 14) :=
          Hub.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hWdef
        have hSsub : S ⊆ Hub := by rw [hSdef]; exact Finset.filter_subset _ _
        have hWsub : W ⊆ Hub := by rw [hWdef]; exact Finset.filter_subset _ _
        have hSge3 : ∀ h ∈ S, 3 ≤ (G.neighborFinset h ∩ Iso).card := by
          intro h hh; rw [hSdef, Finset.mem_filter] at hh; exact hh.2
        have hWle2 : ∀ h ∈ W, (G.neighborFinset h ∩ Iso).card ≤ 2 := by
          intro h hh; rw [hWdef, Finset.mem_filter] at hh; omega
        have hSW : S.card + W.card = 6 := by
          rw [hSdef, hWdef, Finset.card_filter_add_card_filter_not, _hHub6]
        have hsumsplit : ∑ h ∈ S, (G.neighborFinset h ∩ Iso).card
            + ∑ h ∈ W, (G.neighborFinset h ∩ Iso).card = 18 := by
          rw [hSdef, hWdef, Finset.sum_filter_add_sum_filter_not, hsum, hI6]
        have hd4le1 : (Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4)).card ≤ 1 :=
          Nat.not_lt.mp hn4
        have hSsumle : ∑ h ∈ S, (G.neighborFinset h ∩ Iso).card ≤ 3 * S.card + 1 := by
          have hpt : ∀ h ∈ S, (G.neighborFinset h ∩ Iso).card
              ≤ 3 + (if (G.neighborFinset h ∩ Iso).card = 4 then 1 else 0) := by
            intro h hh
            have hb := hdle4 h (hSsub hh)
            by_cases hc : (G.neighborFinset h ∩ Iso).card = 4
            · simp [hc]
            · rw [if_neg hc]; omega
          have hsubf : (S.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4)).card
              ≤ (Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ hSsub)
          calc ∑ h ∈ S, (G.neighborFinset h ∩ Iso).card
              ≤ ∑ h ∈ S, (3 + if (G.neighborFinset h ∩ Iso).card = 4 then 1 else 0) :=
                Finset.sum_le_sum hpt
            _ = 3 * S.card
                + (S.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4)).card := by
                rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm,
                  Finset.sum_boole, Nat.cast_id]
            _ ≤ 3 * S.card + 1 := by omega
        have hWsumle : ∑ h ∈ W, (G.neighborFinset h ∩ Iso).card ≤ 2 * W.card := by
          calc ∑ h ∈ W, (G.neighborFinset h ∩ Iso).card
              ≤ ∑ _h ∈ W, 2 := Finset.sum_le_sum hWle2
            _ = 2 * W.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        have hWne : W.Nonempty := by
          have hns := hallstrong
          rw [not_forall] at hns
          obtain ⟨h, hh⟩ := hns
          rw [Classical.not_imp] at hh
          exact ⟨h, by rw [hWdef, Finset.mem_filter]; exact ⟨hh.1, hh.2⟩⟩
        have hWpos : 1 ≤ W.card := Finset.card_pos.mpr hWne
        have hS5 : S.card = 5 := by omega
        have hW1 : W.card = 1 := by omega
        obtain ⟨w, hWeq⟩ := Finset.card_eq_one.mp hW1
        have hwW : w ∈ W := by rw [hWeq]; exact Finset.mem_singleton_self w
        have hwHub : w ∈ Hub := hWsub hwW
        have hWsing : ∑ h ∈ W, (G.neighborFinset h ∩ Iso).card
            = (G.neighborFinset w ∩ Iso).card := by rw [hWeq, Finset.sum_singleton]
        have hdw2 : (G.neighborFinset w ∩ Iso).card = 2 := by
          have hwle := hWle2 w hwW; omega
        have hSd16 : ∑ h ∈ S, (G.neighborFinset h ∩ Iso).card = 16 := by omega
        have hSeq : S = Hub.erase w := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            rw [Finset.mem_erase]
            refine ⟨?_, hSsub hx⟩
            intro hxw; subst hxw
            have := hSge3 x hx; omega
          · rw [Finset.card_erase_of_mem hwHub, _hHub6, hS5]
        have hwnS : w ∉ S := by rw [hSeq, Finset.mem_erase]; simp
        have hHubins : Hub = insert w S := by rw [hSeq, Finset.insert_erase hwHub]
        have hwcolS : ∑ x ∈ S, (G.neighborFinset w ∩ G.neighborFinset x ∩ Iso).card = 4 := by
          rw [hSeq, per_vertex_share_sum_erase G Hub Iso _hiso3 w hwHub, hdw2]
        have hSoff : ∑ p ∈ S.offDiag,
            (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card = 28 := by
          have hinner : ∀ v ∈ S, ∑ x ∈ S.erase v,
              (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
              + (G.neighborFinset v ∩ G.neighborFinset w ∩ Iso).card
              = 2 * (G.neighborFinset v ∩ Iso).card := by
            intro v hv
            have hvHub := hSsub hv
            have hfull := per_vertex_share_sum_erase G Hub Iso _hiso3 v hvHub
            have hvne : v ≠ w := by
              intro h; subst h; have := hSge3 v hv; omega
            have hev : Hub.erase v = insert w (S.erase v) := by
              rw [hHubins, Finset.erase_insert_of_ne (Ne.symm hvne)]
            rw [hev, Finset.sum_insert (by
              rw [Finset.mem_erase]; rintro ⟨_, hwS⟩; exact hwnS hwS)] at hfull
            omega
          have hsum2 := Finset.sum_congr rfl hinner
          rw [Finset.sum_add_distrib] at hsum2
          have hSdd : ∑ v ∈ S, 2 * (G.neighborFinset v ∩ Iso).card = 32 := by
            rw [← Finset.mul_sum]; omega
          have hvw : ∑ v ∈ S, (G.neighborFinset v ∩ G.neighborFinset w ∩ Iso).card = 4 := by
            rw [Finset.sum_congr rfl (fun v _ => by
              rw [show G.neighborFinset v ∩ G.neighborFinset w
                = G.neighborFinset w ∩ G.neighborFinset v from Finset.inter_comm _ _])]
            exact hwcolS
          rw [sum_offDiag_erase S
            (fun a b => (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card)]
          omega
        have hSoffcard : S.offDiag.card = 20 := by rw [Finset.offDiag_card, hS5]
        have hcount := filter_le_one_card_ge S.offDiag
          (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card) 28 (le_of_eq hSoff)
        have hoffsub : S.offDiag ⊆ Hub.offDiag := by
          intro p hp
          rw [Finset.mem_offDiag] at hp ⊢
          exact ⟨hSsub hp.1, hSsub hp.2.1, hp.2.2⟩
        have hadj : (S.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 4 :=
          le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hoffsub))
            (hub_offDiag_adj_le_four G Hub _hHubsum)
        have hne : ((S.offDiag.filter
            (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1)) \
            (S.offDiag.filter (fun p => G.Adj p.1 p.2))).Nonempty := by
          rw [← Finset.card_pos]
          have hge := Finset.le_card_sdiff
            (S.offDiag.filter (fun p => G.Adj p.1 p.2))
            (S.offDiag.filter
              (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1))
          omega
        obtain ⟨p, hp⟩ := hne
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hp
        obtain ⟨⟨hpoff, hpsh⟩, hpadj⟩ := hp
        obtain ⟨hp1S, hp2S, hp12⟩ := Finset.mem_offDiag.mp hpoff
        have hp1Hub : p.1 ∈ Hub := hSsub hp1S
        have hp2Hub : p.2 ∈ Hub := hSsub hp2S
        have hnadj : ¬G.Adj p.1 p.2 := fun h => hpadj ⟨hpoff, h⟩
        have ha3 : 3 ≤ (G.neighborFinset p.1 ∩ Iso).card := hSge3 p.1 hp1S
        have hb3 : 3 ≤ (G.neighborFinset p.2 ∩ Iso).card := hSge3 p.2 hp2S
        refine ⟨p.1, p.2, hp1Hub, hp2Hub, hdeg4 p.1 hp1Hub, hdeg4 p.2 hp2Hub, hp12, hnadj, ?_, ?_⟩
        · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset p.1 ∩ Iso)
            (G.neighborFinset p.2)
          have hinter : (G.neighborFinset p.1 ∩ Iso) ∩ G.neighborFinset p.2
              = G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso := Finset.inter_right_comm _ _ _
          rw [hinter] at hkey
          omega
        · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset p.2 ∩ Iso)
            (G.neighborFinset p.1)
          have hinter : (G.neighborFinset p.2 ∩ Iso) ∩ G.neighborFinset p.1
              = G.neighborFinset p.2 ∩ G.neighborFinset p.1 ∩ Iso := Finset.inter_right_comm _ _ _
          have hsh2 : (G.neighborFinset p.2 ∩ G.neighborFinset p.1 ∩ Iso).card ≤ 1 := by
            rw [Finset.inter_comm (G.neighborFinset p.2) (G.neighborFinset p.1)]; exact hpsh
          rw [hinter] at hkey
          omega

/-- **NODE B1 + corner wiring.**  In the iso-degree-`4` corner (`|Iso| ≤ 6`, `hIso6`), let `S` be
the hubs of iso-degree `≥ 3`.  When `5 ≤ |S|`, NODE A yields two distinct hubs of `S` sharing at
most one isolated twin; if that pair is **non-adjacent**, each side keeps `≥ 3 − 1 = 2` private
isolated twins (`Finset.card_sdiff_add_card_inter`), giving the configuration.  The residual
cases (`< 5` big hubs, or the pair is a hub-edge) are delegated to `two_hub_corner_b2`. -/
theorem two_hub_corner_select (G : SimpleGraph (Fin 14)) (Hub Iso : Finset (Fin 14))
    (hHub6 : Hub.card = 6)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 4)
    (hIso6 : Iso.card = 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b)
    (hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2) :
    ∃ h₁ h₂ : Fin 14, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  set S : Finset (Fin 14) := Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hSdef
  have hSsub : S ⊆ Hub := by rw [hSdef]; exact Finset.filter_subset _ _
  by_cases hbig5 : 5 ≤ S.card
  · obtain ⟨a, b, haS, hbS, hab, hsh1⟩ :=
      exists_hub_pair_share_le_one_fourteen G S Iso hbig5
        (fun t ht => le_trans (Finset.card_le_card
          (Finset.inter_subset_inter (Finset.Subset.refl _) hSsub)) (le_of_eq (hiso3 t ht)))
        (le_of_eq hIso6)
    have haHub : a ∈ Hub := hSsub haS
    have hbHub : b ∈ Hub := hSsub hbS
    have ha3 : 3 ≤ (G.neighborFinset a ∩ Iso).card := by
      have h := haS; rw [hSdef, Finset.mem_filter] at h; exact h.2
    have hb3 : 3 ≤ (G.neighborFinset b ∩ Iso).card := by
      have h := hbS; rw [hSdef, Finset.mem_filter] at h; exact h.2
    by_cases hadj : G.Adj a b
    · exact two_hub_corner_b2 G Hub Iso hHub6 hdeg4 hHubsum hIso6 hiso3 hisoIndep hshare
    · refine ⟨a, b, haHub, hbHub, hdeg4 a haHub, hdeg4 b hbHub, hab, hadj, ?_, ?_⟩
      · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset a ∩ Iso)
          (G.neighborFinset b)
        have hreord : (G.neighborFinset a ∩ Iso) ∩ G.neighborFinset b
            = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := Finset.inter_right_comm _ _ _
        rw [hreord] at hkey
        omega
      · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset b ∩ Iso)
          (G.neighborFinset a)
        have hreord : (G.neighborFinset b ∩ Iso) ∩ G.neighborFinset a
            = G.neighborFinset b ∩ G.neighborFinset a ∩ Iso := Finset.inter_right_comm _ _ _
        rw [hreord] at hkey
        have hsh2 : (G.neighborFinset b ∩ G.neighborFinset a ∩ Iso).card ≤ 1 := by
          rw [show G.neighborFinset b ∩ G.neighborFinset a
              = G.neighborFinset a ∩ G.neighborFinset b from Finset.inter_comm _ _]
          exact hsh1
        omega
  · exact two_hub_corner_b2 G Hub Iso hHub6 hdeg4 hHubsum hIso6 hiso3 hisoIndep hshare

end N14

end ACMax
