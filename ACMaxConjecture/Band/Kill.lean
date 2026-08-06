import ACMaxConjecture.Band.Subset
import ACMaxConjecture.Counting.V9Discharge

/-!
# B6-sum — the SUM tier-9 kill (`starved_v9_kill_ahl_sum`)

This file lands node B6-sum of the band discharge: the SUM-form specialization of the rebased tier-9
kill `starved_v9_kill_of_import` (`Counting.V9Tier`).  The abstract girth import
`GirthExcessBound`/`hMoore` (the SQRT side condition) is replaced by the census-free SUM subset
wrapper `ahl_ball_girth_subset` (`Band.Subset`) at `S = V₉`, `t = t₉ = n − 4 − X − 3h`,
so the kill's remaining side condition is the pure-ℕ SUM Moore inequality
`t₉(|V₉| − 1)|V₉|^(L/2) < (|V₉| + t₉)((|V₉| + 2t₉)^(L/2) − |V₉|^(L/2))`.  The assembly is otherwise a
verbatim clone of the template: the size and density rows feed the honest excess `t₉` and the SUM
wrapper produces a short `V₉`-cycle (`3 ≤ k ≤ L`, `9L ≤ n + 8`) that `v9_girth` forbids.

Everything is `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ACMax

open Finset
open scoped Classical

/-- **B6-sum — the SUM tier-9 kill.**  A never-firing starved census (`m = 2(n−2)`, `δ ≥ 3`,
`¬ algConn ≤ 2`) on `55 ≤ n` with the positivity window `hpos` (`X + 3h + 4 ≤ n`) and the pure-ℕ
SUM Moore side condition at `S = V₉`, `t = t₉ = n − 4 − X − 3h`, `ℓ = ⌊L/2⌋`, cannot exist.
Assembly (verbatim clone of `starved_v9_kill_of_import`, `hMoore`/`hGEB` swapped for the SUM subset
wrapper `ahl_ball_girth_subset`): the size and density rows feed the honest excess `t₉`, the SUM
wrapper produces a short `V₉`-cycle (`3 ≤ k ≤ L`, `9L ≤ n + 8`), and `v9_girth` forbids it. -/
theorem starved_v9_kill_ahl_sum {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hlo : 55 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 4 ≤ n)
    (L : ℕ) (hL6 : 6 ≤ L) (hLn : 9 * L ≤ n + 8)
    (hside : (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card) * ((v9Set G).card - 1)
          * (v9Set G).card ^ (L / 2)
        < ((v9Set G).card + (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card))
          * (((v9Set G).card + 2 * (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card)) ^ (L / 2)
            - (v9Set G).card ^ (L / 2))) : False := by
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
    ahl_ball_girth_subset G (v9Set G) t9 L hne hL6 hexc hside
  have : NeZero k := ⟨by omega⟩
  exact v9_girth G hm h3 hnf hk3 (by omega) c hcinj hadj hmem

end ACMax
