import ACMaxConjecture.Islands.Ball
import ACMaxConjecture.Islands.Rows
import ACMaxConjecture.Counting.StarvedCensus
import ACMaxConjecture.Counting.Windows

/-!
# IB4 + IB6: the island band is dead, and `hIslands` discharges

This file lands the last leaves of the **island attack** (§3–4): the whole Moore-extremal band
`48 ≤ n ≤ 63` dies by pure counting plus the usable-far-pair dichotomy, and the seven island
verdicts `hIslands` that `acmax_conjecture_narrow` consumes are discharged outright.

* **IB4** `island_band_dead` — a never-firing starved census (`m = 2(n−2)`, `δ ≥ 3`, `hs0`,
  `¬ algConn ≤ 2`) on `48 ≤ n ≤ 63` is impossible.  `by_cases HasUsableFarPair`: the spread
  branch fires `hasUsableFarPair_algConn_le_two`, contradicting `hnf`; the compact branch
  (`¬HasUsableFarPair`) collides two ledgers.  **Row A** is the landed choke
  `7·slots_p_row + p_choke_row_unconditional`; **row B** is the far-pair count
  `n ≤ (40 + X) + 5X + h` (`twin_ball_le` + `island_nonusable_cover`, available whenever
  `h + 3·n_g < 8` supplies an `untouched_twin_exists`).  With the class ledger
  `heavy_class_ledger` (`h + h₆₊ + 3·n_g ≤ X`), the disjointness `heavy_class_disjoint`
  (`h₆₊ + n_g ≤ h`) and the (linearized) giant bound `giant_excess_bound`, `omega` finds the
  system integer-infeasible for every `48 ≤ n ≤ 63`.
* **IB6** `hIslands_discharged` — for each island `m ∈ {50,…,54, 62, 63}` the per-graph
  `Counting.FinalNarrow` dispatch (`algConn_completeBipartite_two`; low-degree test vector;
  `M`-edge moat; else the never-firing starved census) closes via IB4.
* **IB6b** `acmax_conjecture_of_starved_only` — feeding IB6 into `acmax_conjecture_narrow`
  leaves the single narrow girth residual `hStarved55`.

Everything is `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ACMax

open scoped Classical
open SimpleGraph Finset

/-- **IB5a — the heavy class ledger.**  The total degree excess `X` dominates a weighted
count of the heavy classes: each heavy (`deg ≥ 5`) contributes `≥ 1`, each non-giant
degree-`≥ 6` hub a further `≥ 1`, and each giant (`n + 15 < 9·deg`, hence `deg ≥ 8` at
`n ≥ 48`) a further `≥ 3`.  So `h + h₆₊ + 3·n_g ≤ X`. -/
theorem heavy_class_ledger {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 48 ≤ n) :
    (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card
      + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h))).card
      + 3 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card
      ≤ excessX n G := by
  classical
  have hE6 : ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h)))
      = (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).filter
          (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h)) := by
    ext x
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    omega
  have hEg : ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h))
      = (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).filter
          (fun h => n + 15 < 9 * G.degree h) := by
    ext x
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    omega
  rw [hE6, hEg, excessX, Finset.card_eq_sum_ones, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  split_ifs <;> omega

/-- **IB5b — the heavy classes are disjoint.**  The non-giant degree-`≥ 6` hubs and the giants
are disjoint subsets of the heavies (`deg ≥ 5`), so `h₆₊ + n_g ≤ h`. -/
theorem heavy_class_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 48 ≤ n) :
    ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h))).card
      + ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card
      ≤ (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card := by
  classical
  have hdisj : Disjoint
      ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h)))
      ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_filter] at hx hy
    exact hx.2.2 hy.2
  rw [← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_union] at hx
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ x, ?_⟩
  rcases hx with h6 | hg
  · rw [Finset.mem_filter] at h6
    obtain ⟨_, h6a, _⟩ := h6
    omega
  · rw [Finset.mem_filter, mem_hubSet] at hg
    obtain ⟨hd4, hgg⟩ := hg
    omega

/-- **IB4a — the arithmetic core of the island kill.**  The census counting rows, the far-pair
count (row B, available when `h + 3·n_g < 8`), the class ledgers and the giant bound are jointly
integer-infeasible for every `48 ≤ n ≤ 63`.  The excess `X` is bounded (`X ≤ 15`, from hoarding
and the ledger), so `interval_cases n <;> interval_cases X <;> omega` closes the finite grid — the
per-case `omega` splits the remaining giant count `n_g` itself. -/
theorem island_arith (n X h t4 p h6 ng : ℕ)
    (hn48 : 48 ≤ n) (hn63 : n ≤ 63)
    (hslots : 24 + 2 * X ≤ t4 + p + h6 + 4 * ng)
    (hpc : 7 * t4 + 8 * p + 3 * X + 32 ≤ 4 * n)
    (hgi : ng * (n - 20) ≤ 9 * X)
    (hho : 3 * X + 32 ≤ n + 3 * ng)
    (hled : h + h6 + 3 * ng ≤ X)
    (hdis : h6 + ng ≤ h)
    (hB : h + 3 * ng < 8 → n ≤ 40 + 6 * X + h) : False := by
  have hX15 : X ≤ 15 := by omega
  by_cases hc : h + 3 * ng < 8
  · have hBrow := hB hc
    interval_cases n <;> interval_cases X <;> omega
  · interval_cases n <;> interval_cases X <;> omega

/-- **IB4 — the island band is dead.**  A never-firing starved census (`m = 2(n−2)`, `δ ≥ 3`,
`hs0`, `¬ algConn ≤ 2`) cannot exist for `48 ≤ n ≤ 63`.  On the compact cell
(`¬HasUsableFarPair`) rows A (choke) and B (far-pair count) plus the class ledgers are
integer-infeasible (`island_arith`); on the spread cell the usable far pair fires. -/
theorem island_band_dead {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn48 : 48 ≤ n) (hn63 : n ≤ 63)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    False := by
  classical
  by_cases hfar : HasUsableFarPair G
  · exact hnf (hasUsableFarPair_algConn_le_two G h3 hfar)
  · -- compact cell: assemble the counting rows and hand them to the arithmetic core
    have hsl := slots_p_row G (by omega) hm h3 hnf hs0
    have hpc := p_choke_row_unconditional (by omega) G hm h3 hs0 hnf
    have hgi := giant_excess_bound G (by omega)
    have hho := hoarding_law G (by omega) hm h3 hnf hs0
    have hledger := heavy_class_ledger G (by omega)
    have hdisj := heavy_class_disjoint G (by omega)
    -- row B, available when an untouched twin exists
    have hB : (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card
          + 3 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card < 8 →
        n ≤ 40 + 6 * excessX n G
          + (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card := by
      intro hc
      obtain ⟨t, ht, hnbr⟩ := untouched_twin_exists G (by omega) hm h3 hnf hs0 hc
      have hu := island_sigma_usable G h3 t ht hnbr
      have hball : (closeSet G t).card ≤ 40 + excessX n G :=
        twin_ball_le G t ht
          (fun w hadj => hnbr w ((SimpleGraph.mem_neighborFinset G t w).mpr hadj))
      have hcov := island_nonusable_cover G h3 hfar t hu
      omega
    exact island_arith n (excessX n G) _ _ _ _ _ hn48 hn63 hsl hpc hgi hho hledger hdisj hB

/-- **IB6 — `hIslands` discharged.**  For each Moore-extremal island `m ∈ {50,…,54, 62, 63}`,
`K_{2,m−2}` realizes `λ₂ = 2` and every graph on `Fin m` with `2(m−2)` edges has `algConn ≤ 2`.
The upper bound mirrors the `Counting.FinalNarrow` per-graph dispatch, closing the never-firing
starved census by `island_band_dead`. -/
theorem hIslands_discharged : ∀ (m : ℕ) [Nonempty (Fin m)],
    m ∈ ({50, 51, 52, 53, 54, 62, 63} : Finset ℕ) →
    algConn (completeBipartiteGraph (Fin 2) (Fin (m - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin m), G.edgeFinset.card = 2 * (m - 2) → algConn G ≤ 2 := by
  intro m _inst hmem
  have hrange : 50 ≤ m ∧ m ≤ 63 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  obtain ⟨hm50, hm63⟩ := hrange
  refine ⟨algConn_completeBipartite_two m (by omega), fun G hm => ?_⟩
  rcases Classical.em (∃ v : Fin m, G.degree v ≤ 2) with hlow | hlow
  · let : DecidableEq (Fin m) := fun a b => Classical.propDecidable (a = b)
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [Finset.sdiff_nonempty]
    intro hsub
    have huniv : (Finset.univ : Finset (Fin m)).card ≤ (insert u (G.neighborFinset u)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at huniv
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    omega
  · let : DecidableEq (Fin m) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin m, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    by_cases hMedge : ∃ v w : Fin m, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w
    · obtain ⟨u, p, hu, hp, hadj⟩ := hMedge
      exact medge_moat_fires (by omega) G hm h3 u p hadj hu hp
    · have hs0 : ∀ v w : Fin m, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
        s0_of_no_medge G hMedge
      by_contra hnf
      exact island_band_dead G (by omega) (by omega) hm h3 hnf hs0

/-- **IB6b — the ACMAX conjecture from the starved residual alone.**  With the seven island
verdicts discharged internally (`hIslands_discharged`), the narrow capstone
`acmax_conjecture_narrow` needs only the single narrow girth residual `hStarved55`: every
order `n ≥ 4` satisfies the full conjecture. -/
theorem acmax_conjecture_of_starved_only
    (hStarved55 : ∀ (m : ℕ) [Nonempty (Fin m)] (G : SimpleGraph (Fin m)),
        55 ≤ m → m ≤ 122 → m ≠ 62 → m ≠ 63 →
        G.edgeFinset.card = 2 * (m - 2) → (∀ v : Fin m, 3 ≤ G.degree v) →
        ¬ algConn G ≤ 2 →
        (∀ v w : Fin m, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) → False) :
    ∀ (n : ℕ) [Nonempty (Fin n)], 4 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  acmax_conjecture_narrow hIslands_discharged hStarved55

end ACMax
