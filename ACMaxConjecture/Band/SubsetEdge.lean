import ACMaxConjecture.Band.Edge
import ACMaxConjecture.Band.Rows
import ACMaxConjecture.Counting.V9Discharge

/-!
# The EDGE band-discharge subset wrapper and kill (B5-edge / B6-edge)

This file is the *even-girth EDGE* twin of the vertex-ball (SUM) subset wrapper (`Band.Subset`).  It
lands the census-free subset/`2`-core wrapper for the Alon–Hoory–Linial even-girth Moore refutation
(nodes B5/B6 of the band discharge): it instantiates the abstract girth bound `ahl_edge_girth_bound`
(`Band.Edge`) at the
induced graph on the `2`-core of a subset `S`, producing a short cycle inside `S` in the exact
`ZMod k` cyclic-map form demanded by the tier-9 kill.  It mirrors the SUM wrapper's plumbing exactly
(no component descent — the AM–GM walk count and the two-sided injectivity are global sums, so the
`2`-core alone suffices).

## The `v`-transport

The EDGE side condition `t·v^(s+1) < (v + 2t)^(s+1) − v^(s+1)` is verified at `v = S.card`, but the
`2`-core shrinks to `v' = S'.card ≤ v`.  The genuinely-new arithmetic step is the **`v`-transport**
`edge_side_transport`: clearing the monus with the geometric identity (`geom_sum₂_mul_of_ge`) turns
the difference into `v^(s+1) < 2·Σ_{k<s+1}(v + 2t)^k v^(s−k)`, whose per-term comparison reduces to
`v' ≤ v` and `((v + 2t)v')^k ≤ ((v' + 2t)v)^k` (both `⟺ v' ≤ v`) plus `Nat.pow_le_pow_left`; a
cross-multiplied cancellation finishes — no `nlinarith`, matching the doc's `0/9000`-violation
verification.

## Contents

* **`edge_side_transport`** — the `v`-transport of the EDGE (difference-form) side condition from
  `v` to `v' ≤ v`.
* **`ahl_edge_girth_subset`** — the subset wrapper: a nonempty `S` with edge excess
  `2|S| + 2t ≤ pairs(S)` meeting the EDGE side condition
  `t·|S|^((L+1)/2) < (|S| + 2t)^((L+1)/2) − |S|^((L+1)/2)` (`6 ≤ L`) carries a cycle of length
  `3 ≤ k ≤ L` inside `S`, in the `ZMod k` cyclic-map form.
* **`starved_v9_kill_ahl_edge`** — the B6-edge kill: a never-firing starved census on `55 ≤ n`
  meeting the EDGE side condition at `S = V₉` cannot exist.
-/

namespace ACMax

open SimpleGraph Finset
open scoped Classical

/-- **The `v`-transport of the EDGE side condition.**  In difference form
`t·v^m < (v + 2t)^m − v^m`, the condition descends from `v` to any `v' ≤ v`.  Both sides are cleared
of the monus by the geometric identity `Σ_{k<m}(v + 2t)^k v^(m−1−k)·2t = (v + 2t)^m − v^m`
(`geom_sum₂_mul_of_ge`); the resulting `v^m < 2·Σ` transports term-by-term, each summand comparison
(after peeling `2·v'^(m−1−k) v^(m−1−k)`) reducing to `v' ≤ v` and
`((v + 2t)v')^k ≤ ((v' + 2t)v)^k`, and a cross-multiplied cancellation finishes. -/
theorem edge_side_transport {t m v v' : ℕ} (ht : 1 ≤ t) (hm : 1 ≤ m) (hvv' : v' ≤ v)
    (hQ : t * v ^ m < (v + 2 * t) ^ m - v ^ m) :
    t * v' ^ m < (v' + 2 * t) ^ m - v' ^ m := by
  set Sv := ∑ k ∈ Finset.range m, (v + 2 * t) ^ k * v ^ (m - 1 - k) with hSvdef
  set Sv' := ∑ k ∈ Finset.range m, (v' + 2 * t) ^ k * v' ^ (m - 1 - k) with hSv'def
  have hgeomv : Sv * (2 * t) = (v + 2 * t) ^ m - v ^ m := by
    rw [hSvdef]
    have h := geom_sum₂_mul_of_ge (show v ≤ v + 2 * t by omega) m
    rw [show v + 2 * t - v = 2 * t by omega] at h
    exact h
  have hgeomv' : Sv' * (2 * t) = (v' + 2 * t) ^ m - v' ^ m := by
    rw [hSv'def]
    have h := geom_sum₂_mul_of_ge (show v' ≤ v' + 2 * t by omega) m
    rw [show v' + 2 * t - v' = 2 * t by omega] at h
    exact h
  have hQ2 : v ^ m < 2 * Sv := by
    have hlt : t * v ^ m < t * (2 * Sv) := by
      calc t * v ^ m
          < (v + 2 * t) ^ m - v ^ m := hQ
        _ = Sv * (2 * t) := hgeomv.symm
        _ = t * (2 * Sv) := by ring
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hXM : v' ^ m * (2 * Sv) ≤ v ^ m * (2 * Sv') := by
    calc v' ^ m * (2 * Sv)
        = ∑ k ∈ Finset.range m, v' ^ m * 2 * ((v + 2 * t) ^ k * v ^ (m - 1 - k)) := by
          rw [hSvdef, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ ≤ ∑ k ∈ Finset.range m, v ^ m * 2 * ((v' + 2 * t) ^ k * v' ^ (m - 1 - k)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hklt : k < m := Finset.mem_range.mp hk
          have hpk : v' ^ m = v' ^ (k + 1) * v' ^ (m - 1 - k) := by
            rw [← pow_add]; congr 1; omega
          have hqk : v ^ m = v ^ (k + 1) * v ^ (m - 1 - k) := by
            rw [← pow_add]; congr 1; omega
          have hbase : (v + 2 * t) * v' ≤ (v' + 2 * t) * v := by
            calc (v + 2 * t) * v' = v * v' + 2 * t * v' := by ring
              _ ≤ v * v' + 2 * t * v :=
                  Nat.add_le_add_left (Nat.mul_le_mul (le_refl (2 * t)) hvv') _
              _ = (v' + 2 * t) * v := by ring
          have hbasek : ((v + 2 * t) * v') ^ k ≤ ((v' + 2 * t) * v) ^ k :=
            Nat.pow_le_pow_left hbase k
          have hAB : v' * ((v + 2 * t) * v') ^ k ≤ v * ((v' + 2 * t) * v) ^ k :=
            Nat.mul_le_mul hvv' hbasek
          have keyL : v' ^ m * 2 * ((v + 2 * t) ^ k * v ^ (m - 1 - k))
              = 2 * (v' ^ (m - 1 - k) * v ^ (m - 1 - k)) * (v' * ((v + 2 * t) * v') ^ k) := by
            rw [mul_pow, hpk]; ring
          have keyR : v ^ m * 2 * ((v' + 2 * t) ^ k * v' ^ (m - 1 - k))
              = 2 * (v' ^ (m - 1 - k) * v ^ (m - 1 - k)) * (v * ((v' + 2 * t) * v) ^ k) := by
            rw [mul_pow, hqk]; ring
          rw [keyL, keyR]
          exact Nat.mul_le_mul (le_refl _) hAB
      _ = v ^ m * (2 * Sv') := by
          rw [hSv'def, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
  have hSv'pos : 0 < Sv' := by
    rw [hSv'def]
    apply Finset.sum_pos'
    · intro i _; exact Nat.zero_le _
    · refine ⟨m - 1, Finset.mem_range.mpr (by omega), ?_⟩
      rw [show m - 1 - (m - 1) = 0 by omega, pow_zero, mul_one]
      exact Nat.one_le_pow _ _ (by omega)
  have hYpos : 0 < 2 * Sv' := Nat.mul_pos (by norm_num) hSv'pos
  have hcombine : 2 * Sv * v' ^ m < 2 * Sv * (2 * Sv') := by
    calc 2 * Sv * v' ^ m
        = v' ^ m * (2 * Sv) := by ring
      _ ≤ v ^ m * (2 * Sv') := hXM
      _ < 2 * Sv * (2 * Sv') := mul_lt_mul_of_pos_right hQ2 hYpos
  have hfin : v' ^ m < 2 * Sv' := Nat.lt_of_mul_lt_mul_left hcombine
  calc t * v' ^ m
      < t * (2 * Sv') := mul_lt_mul_of_pos_left hfin (by omega)
    _ = Sv' * (2 * t) := by ring
    _ = (v' + 2 * t) ^ m - v' ^ m := hgeomv'

/-- **The EDGE band-discharge subset wrapper.**  For a nonempty `S : Finset (Fin n)` with edge
excess `2|S| + 2t ≤ pairs(S)` (i.e. the induced graph on `S` has `≥ |S| + t` edges) meeting the
even-girth EDGE Moore side condition `t·|S|^((L+1)/2) < (|S| + 2t)^((L+1)/2) − |S|^((L+1)/2)` with
`6 ≤ L`, there is a cycle of length `3 ≤ k ≤ L` inside `S`, given as an injective cyclic map
`c : ZMod k → Fin n`.  Assembly (mirrors `ahl_ball_girth_subset`, calling `ahl_edge_girth_bound`):
extract the minimum-degree-`2` `2`-core `S'` (`two_core_aux`), transport the side condition from
`|S|` to `|S'|` (`edge_side_transport`), instantiate `ahl_edge_girth_bound` at the induced graph on
`S'` — the degree bound `D ≥ 2(|S'| + t)` supplies the term-wise monotonicity — then lift the short
`2`-core cycle to `G` (`Embedding.induce`, `Walk.map`) and convert with `cycle_walk_to_zmod`.  The
girth budget is honest: the collision consumes girth `> 2s + 1` with `s + 1 = (L + 1)/2`, and
`2s + 1 ≤ L` for both parities of `L`. -/
theorem ahl_edge_girth_subset {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (t L : ℕ)
    (_hSne : S.Nonempty) (hL6 : 6 ≤ L)
    (hexc : 2 * S.card + 2 * t ≤ ((S ×ˢ S).filter (fun q : Fin n × Fin n => G.Adj q.1 q.2)).card)
    (hside : t * S.card ^ ((L + 1) / 2)
      < (S.card + 2 * t) ^ ((L + 1) / 2) - S.card ^ ((L + 1) / 2)) :
    ∃ k : ℕ, 3 ≤ k ∧ k ≤ L ∧
      ∃ c : ZMod k → Fin n, Function.Injective c ∧
        (∀ i : ZMod k, G.Adj (c i) (c (i + 1))) ∧ (∀ i : ZMod k, c i ∈ S) := by
  classical
  set s : ℕ := (L - 1) / 2 with hsdef
  have hs1 : s + 1 = (L + 1) / 2 := by omega
  rw [← hs1] at hside
  -- The side condition forces a positive excess.
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at hside
    · exact h
  -- Extract the minimum-within-degree-`2` `2`-core carrying the excess.
  have hpairs' : 2 * S.card + 2 * t ≤ edgeSumWithin G S := by
    rw [edgeSumWithin_eq_pairs]; exact hexc
  obtain ⟨S', hS'sub, hS'ne, hS'min, hS'inv⟩ := two_core_aux G ht1 S hpairs'
  -- Transport the (difference-form) side condition from `S.card` to `S'.card ≤ S.card`.
  have hside' : t * S'.card ^ (s + 1) < (S'.card + 2 * t) ^ (s + 1) - S'.card ^ (s + 1) :=
    edge_side_transport ht1 (by omega) (Finset.card_le_card hS'sub) hside
  -- The induced graph on the `2`-core.
  set H : SimpleGraph (↥(↑S' : Set (Fin n))) := G.induce (↑S' : Set (Fin n)) with hHdef
  have : Nonempty (↥(↑S' : Set (Fin n))) := (Finset.coe_nonempty.mpr hS'ne).to_subtype
  have hcardV' : Fintype.card (↥(↑S' : Set (Fin n))) = S'.card := by
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  have hDS : edgeSumWithin G S' = 2 * H.edgeFinset.card := by
    rw [edgeSumWithin_eq_pairs]; exact induced_pairs_eq_two_mul_edges G S'
  have hsumdeg : ∑ w, H.degree w = edgeSumWithin G S' := by
    rw [H.sum_degrees_eq_twice_card_edges, hDS]
  have hDge : 2 * (S'.card + t) ≤ ∑ w, H.degree w := by rw [hsumdeg]; omega
  have hδ2 : ∀ w : ↥(↑S' : Set (Fin n)), 2 ≤ H.degree w := by
    intro w
    have hh : H.degree w = degWithin G S' w.val := induce_degree_eq_degWithin G S' w
    rw [hh]
    exact hS'min w.val (Finset.mem_coe.mp w.2)
  -- Clear `t` from the difference form via the geometric identity at `v' = S'.card`.
  have hgeomv' : (∑ k ∈ Finset.range (s + 1), (S'.card + 2 * t) ^ k * S'.card ^ (s - k)) * (2 * t)
      = (S'.card + 2 * t) ^ (s + 1) - S'.card ^ (s + 1) := by
    have h := geom_sum₂_mul_of_ge (show S'.card ≤ S'.card + 2 * t by omega) (s + 1)
    rw [show S'.card + 2 * t - S'.card = 2 * t by omega, show s + 1 - 1 = s by omega] at h
    exact h
  have hQv' : S'.card ^ (s + 1)
      < 2 * ∑ k ∈ Finset.range (s + 1), (S'.card + 2 * t) ^ k * S'.card ^ (s - k) := by
    have hlt : t * S'.card ^ (s + 1)
        < t * (2 * ∑ k ∈ Finset.range (s + 1), (S'.card + 2 * t) ^ k * S'.card ^ (s - k)) := by
      calc t * S'.card ^ (s + 1)
          < (S'.card + 2 * t) ^ (s + 1) - S'.card ^ (s + 1) := hside'
        _ = (∑ k ∈ Finset.range (s + 1), (S'.card + 2 * t) ^ k * S'.card ^ (s - k)) * (2 * t) :=
            hgeomv'.symm
        _ = t * (2 * ∑ k ∈ Finset.range (s + 1), (S'.card + 2 * t) ^ k * S'.card ^ (s - k)) := by
            ring
    exact Nat.lt_of_mul_lt_mul_left hlt
  -- The EDGE Moore bound is violated on `H`, forcing a short `H`-cycle.
  have hbig : Fintype.card (↥(↑S' : Set (Fin n))) ^ (s + 1)
      < 2 * ∑ k ∈ Finset.range (s + 1),
          ((∑ w, H.degree w) - Fintype.card (↥(↑S' : Set (Fin n)))) ^ k
            * Fintype.card (↥(↑S' : Set (Fin n))) ^ (s - k) := by
    rw [hcardV']
    calc S'.card ^ (s + 1)
        < 2 * ∑ k ∈ Finset.range (s + 1), (S'.card + 2 * t) ^ k * S'.card ^ (s - k) := hQv'
      _ ≤ 2 * ∑ k ∈ Finset.range (s + 1),
            ((∑ w, H.degree w) - S'.card) ^ k * S'.card ^ (s - k) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro k _
          have hd2 : S'.card + 2 * t ≤ (∑ w, H.degree w) - S'.card := by omega
          have hd2k : (S'.card + 2 * t) ^ k ≤ ((∑ w, H.degree w) - S'.card) ^ k :=
            Nat.pow_le_pow_left hd2 k
          exact Nat.mul_le_mul (le_refl 2) (Nat.mul_le_mul hd2k (le_refl _))
  obtain ⟨u, wc, hwcyc, hwlen⟩ := ahl_edge_girth_bound hδ2 hbig
  -- Lift the short cycle from `H` to `G` and convert to the `ZMod` cyclic-map form.
  set emb := Embedding.induce (G := G) (↑S' : Set (Fin n)) with hembdef
  have hwc2 : (wc.map emb.toHom).IsCycle := hwcyc.map emb.injective
  have hsupp : ∀ x ∈ (wc.map emb.toHom).support, x ∈ S := by
    intro x hx
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact hS'sub (Finset.mem_coe.mp y.2)
  obtain ⟨hk3, hex⟩ := cycle_walk_to_zmod hwc2 hsupp
  refine ⟨(wc.map emb.toHom).length, hk3, ?_, hex⟩
  rw [SimpleGraph.Walk.length_map]
  omega

/-- **B6-edge — the EDGE tier-9 kill.**  A never-firing starved census (`m = 2(n−2)`, `δ ≥ 3`) on
`55 ≤ n` with the positivity window `X + 3·|V₉ᶜ| + 4 ≤ n` (`hpos`), meeting the EDGE Moore side
condition `hMoore` at `S = V₉` with the honest excess `t₉ = n − 4 − X − 3·|V₉ᶜ|`, cannot exist.
Clone of `starved_v9_kill_of_import` with `hMoore` swapped for the EDGE side condition and `hGEB`
deleted: the size and density rows feed the excess `t₉` and `hMoore` to `ahl_edge_girth_subset` at
`S = V₉`, producing a short `V₉`-cycle (`3 ≤ k ≤ L`, `9L ≤ n + 8`) that `v9_girth` forbids. -/
theorem starved_v9_kill_ahl_edge {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hlo : 55 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 4 ≤ n)
    (L : ℕ) (hL6 : 6 ≤ L) (hLn : 9 * L ≤ n + 8)
    (hMoore : (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card) * (v9Set G).card ^ ((L + 1) / 2)
      < ((v9Set G).card + 2 * (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card)) ^ ((L + 1) / 2)
        - (v9Set G).card ^ ((L + 1) / 2)) : False := by
  set t9 : ℕ := n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card with ht9def
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRcard : (v9Set G)ᶜ.card ≤ excessX n G :=
    le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hexc : 2 * (v9Set G).card + 2 * t9 ≤ v9Pairs G := by
    have hq := v9_density_row_quant G (by omega) hm
    rw [ht9def]
    omega
  have hne : (v9Set G).Nonempty := by
    rw [← Finset.card_pos]
    have hsize := v9_size_row G
    omega
  obtain ⟨k, hk3, hkL, c, hcinj, hadj, hmem⟩ :=
    ahl_edge_girth_subset G (v9Set G) t9 L hne hL6 hexc hMoore
  have : NeZero k := ⟨by omega⟩
  exact v9_girth G hm h3 hnf hk3 (by omega) c hcinj hadj hmem

end ACMax
