import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConnK2
import ACMaxConjecture.Cuts.SignedCut
import ACMaxConjecture.Cuts.LowDegreeVertex
import ACMaxConjecture.Reduction.Residual
import ACMaxConjecture.Counting.Moats
import ACMaxConjecture.Counting.ResidualInterface
import ACMaxConjecture.Counting.XBoundAssembly
import ACMaxConjecture.Counting.Quotient
import ACMaxConjecture.Counting.StarvedCensus
import ACMaxConjecture.Counting.V9Discharge
import ACMaxConjecture.Counting.V9DischargeSharp
import ACMaxConjecture.SmallCases.SmallCases
import ACMaxConjecture.SmallCases.CaseN5
import ACMaxConjecture.SmallCases.CaseN6N7
import ACMaxConjecture.SmallCases.CaseN8
import ACMaxConjecture.SmallCases.CaseN9
import ACMaxConjecture.SmallCases.CaseN10
import ACMaxConjecture.SmallCases.CaseN11
import ACMaxConjecture.SmallCases.Cases12To20


/-!
# The finite-range window dispatch and the narrow capstone

Closes the finite range of the ACMAX conjecture and assembles the narrow
capstone. The small orders and the mid range are discharged by the moat paradigm
and the starved census; the whole conjecture is then banked from a strictly
smaller input set (no tier-18 girth import, import-free above `n = 123`).

## Main results

* `z1_fires`, `z1_forced_of_le_31` — the `Z1` star-moat (a degree-4 hub with two
  degree-3 twins) and its forcing count on `8 ≤ n ≤ 31`.
* `upperBound_moat` — the upper bound on the moat window `21 ≤ n ≤ 31`
  (dispatch on `δ ≤ 2` / `M`-edge / `Z1`-forcing).
* `starved_owner_choke_32_49`, `starved_band_kill_32_49`, `upperBound_range_49`,
  `acmax_conjecture_range_49` — the widened starved band and the continuous
  verdict on `21 ≤ n ≤ 49`.
* `acmax_conjecture_narrow` — the narrow assembly of Kolokolnikov Conjecture 1.5
  over every `n ≥ 4`, from the banked per-order theorems (`n ≤ 20`), the
  finite-range dispatch, the uniform `n ≥ 123` starved-census kill, and the two
  residual hypotheses `hIslands` (the seven Moore-extremal islands) and
  `hStarved55` (the narrow girth residual on `55 ≤ n ≤ 122`).
-/

/-! ## The window-34 discharge

For a `ResidualCore` graph on `23 ≤ n ≤ 34`, split on the presence of an `M`-edge:
present ⟹ `medge_moat_fires`; absent ⟹ the shared-hub stars are forced. On
`23 ≤ n ≤ 31` the E1 count `z1_forced_of_le_31` forces `Z1` with no heavy
hypothesis (negating `Z1` starves the degree-4 hubs and the incidence total forces
`n ≥ 32`); on `32 ≤ n ≤ 34` the heavy witness forces `Z1 ∨ Z3`. `Z1` fires at
`n ≥ 21`, closing the feared `23 ≤ n ≤ 29` gap at the source. -/

namespace ACMax

open scoped Classical

/-- **`Z1` fires.**  A degree-`4` hub owning `≥ 2` degree-`3` twins closes the graph at every
`n ≥ 21` — extract two distinct twins and feed `z1_star_moat_fires`. -/
theorem z1_fires {n : ℕ} [Nonempty (Fin n)] (hn : 21 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hZ1 : ∃ h : Fin n, G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ deg3Set G).card) :
    algConn G ≤ 2 := by
  obtain ⟨h, hdh, htw⟩ := hZ1
  obtain ⟨t₁, t₂, ht1mem, ht2mem, ht12⟩ :=
    Finset.one_lt_card_iff.mp (by omega : 1 < (G.neighborFinset h ∩ deg3Set G).card)
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_deg3Set] at ht1mem ht2mem
  exact z1_star_moat_fires hn G hm h3 h t₁ t₂ hdh ht1mem.1 ht2mem.1 ht1mem.2 ht2mem.2 ht12

/-! ## The moat window `21 ≤ n ≤ 31`

Closes the moat window `21 ≤ n ≤ 31` (in particular `n = 21, 22`) by the moat
dispatch: `δ ≤ 2` via the low-degree-vertex test vector; `δ ≥ 3` with an `M`-edge
via `medge_moat_fires`; `δ ≥ 3` with no `M`-edge via the `Z1`-only forcing count
`z1_forced_of_le_31` (valid on `8 ≤ n ≤ 31`), killed by `z1_fires`. The
`λ₂(K_{2,n-2}) = 2` half reuses `algConn_completeBipartite_two`. -/

/-- **E1 — the `Z1`-only forcing count on `8 ≤ n ≤ 31`.**  On the `e(M) = 0` census world
(`m = 2(n−2)`, `δ ≥ 3`, no degree-`3`–degree-`3` edge), a degree-`4` hub owning `≥ 2` degree-`3`
twins (`Z1`) is forced.  Negating `Z1` caps every degree-`4` hub at `tₕ ≤ 1`; summing the
per-hub bound `tₕ ≤ (deg h − 3) + 3·[deg h ≥ 5]` against the incidence total
`∑_{Hub} tₕ = 3·|D₃|`, the excess ledger `∑_{Hub}(deg − 3) ≤ n − 8`, `|D₃| = 8 + X` and the
refund `n₅₊ ≤ X` gives `24 + 3X ≤ (n − 8) + 3X`, i.e. `n ≥ 32`, contradicting `n ≤ 31`.  This is
`z1_forced_le_31` with its lower bound relaxed to `8 ≤ n`, reaching `n = 21, 22`. -/
theorem z1_forced_of_le_31 {n : ℕ} (hn8 : 8 ≤ n) (hn31 : n ≤ 31)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    ∃ h : Fin n, G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ deg3Set G).card := by
  classical
  by_contra hnZ1
  have cap4 : ∀ h : Fin n, G.degree h = 4 → (G.neighborFinset h ∩ deg3Set G).card ≤ 1 := by
    intro h hd
    by_contra hlt
    exact hnZ1 ⟨h, hd, by omega⟩
  have hEq : deg3Set G = isoTwins G := deg3_eq_isoTwins_of_s0 G hs0
  have hsum : ∑ h ∈ hubSet G, (G.neighborFinset h ∩ deg3Set G).card = 3 * (deg3Set G).card := by
    have key := twin_incidence_total G h3
    rw [← hEq] at key
    refine Eq.trans ?_ key
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    ext x
    simp [Finset.mem_inter]
  set c : ℕ := (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card with hc
  have hfilt_eq : (hubSet G).filter (fun h => 5 ≤ G.degree h)
      = Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v) := by
    ext v
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have hptbound : ∀ h ∈ hubSet G, (G.neighborFinset h ∩ deg3Set G).card
      ≤ (G.degree h - 3) + 3 * (if 5 ≤ G.degree h then 1 else 0) := by
    intro h hh
    have hge4 : 4 ≤ G.degree h := mem_hubSet.mp hh
    have htle : (G.neighborFinset h ∩ deg3Set G).card ≤ G.degree h := by
      calc (G.neighborFinset h ∩ deg3Set G).card
          ≤ (G.neighborFinset h).card := Finset.card_le_card Finset.inter_subset_left
        _ = G.degree h := G.card_neighborFinset_eq_degree h
    by_cases hd4 : G.degree h = 4
    · rw [if_neg (by omega)]; have := cap4 h hd4; omega
    · have hge5 : 5 ≤ G.degree h := by omega
      rw [if_pos hge5]; omega
  have hsum_le : ∑ h ∈ hubSet G, (G.neighborFinset h ∩ deg3Set G).card
      ≤ ∑ h ∈ hubSet G, ((G.degree h - 3) + 3 * (if 5 ≤ G.degree h then 1 else 0)) :=
    Finset.sum_le_sum hptbound
  have hc_sum : ∑ h ∈ hubSet G, 3 * (if 5 ≤ G.degree h then 1 else 0) = 3 * c := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.card_filter, hfilt_eq]
  rw [Finset.sum_add_distrib, hc_sum] at hsum_le
  have hexcess_hub : ∑ h ∈ hubSet G, (G.degree h - 3) ≤ n - 8 := by
    have hfull : ∑ v : Fin n, (G.degree v - 3) = n - 8 := total_excess_eq (by omega) G hm h3
    calc ∑ h ∈ hubSet G, (G.degree h - 3)
        ≤ ∑ v : Fin n, (G.degree v - 3) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = n - 8 := hfull
  have hn3 : (deg3Set G).card = 8 + excessX n G :=
    deg3_card_eq_eight_add_excess n G (by omega) hm h3
  have hcX : c ≤ excessX n G := by
    rw [hc, excessX]
    calc (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card
        = ∑ _v ∈ Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v), 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v), (G.degree v - 4) := by
          apply Finset.sum_le_sum
          intro v hv
          have := (Finset.mem_filter.mp hv).2
          omega
  omega

/-- **The moat upper bound on `21 ≤ n ≤ 31`.**  Every `G` on `Fin n` with `2(n−2)` edges has
`algConn G ≤ 2`, by the three-way moat dispatch: low-degree vertex, `M`-edge moat, or the forced
`Z1` shared-hub star. -/
theorem upperBound_moat {n : ℕ} [Nonempty (Fin n)] (hn21 : 21 ≤ n) (hn31 : n ≤ 31)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2)) :
    algConn G ≤ 2 := by
  rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
  · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hle : (Finset.univ : Finset (Fin n)).card ≤ (insert u (G.neighborFinset u)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hle
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    omega
  · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    by_cases hMedge : ∃ v w : Fin n, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w
    · obtain ⟨u, p, hu, hp, hadj⟩ := hMedge
      exact medge_moat_fires (by omega) G hm h3 u p hadj hu hp
    · have hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
        s0_of_no_medge G hMedge
      exact z1_fires (by omega) G hm h3 (z1_forced_of_le_31 (by omega) hn31 G hm h3 hs0)

end ACMax



/-! ## The continuous range `21 ≤ n ≤ 49`

Assembles the moat window `upperBound_moat` with the starved band
`32 ≤ n ≤ 49` into a single verdict. The starved band kill is widened from
`35 ≤ n ≤ 49` to `32 ≤ n ≤ 49` — every owner-choke ingredient is `n`-generic well
below 35, and the closing `interval_cases` count still closes at `n ∈ {32,33,34}`
(where the hoarding and giant-census rows force `n_g = X = 0` and the choke caps
`7·t₄ < 7·24`), giving `starved_band_kill_32_49`. The verdict
`acmax_conjecture_range_49` dispatches on `δ ≤ 2` / `M`-edge / starved band. -/

namespace ACMax

open Finset
open scoped Classical

/-- **The starved owner-choke, widened to `32 ≤ n ≤ 49`.**  Identical to
`starved_owner_choke_35_49` but with the closing `interval_cases n <;> omega` run over the wider
window; the extra rows `n ∈ {32, 33, 34}` close because hoarding forces `X ≤ n_g`, the giant
census forces `(n − 20)·n_g ≤ 9X`, together pinning `n_g = X = 0`, which collides the slots row
(`t₄ ≥ 24`) with the choke (`7·t₄ ≤ 4n − 32`). -/
theorem starved_owner_choke_32_49 {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn32 : 32 ≤ n) (hn49 : n ≤ 49)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hchoke : 7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
                (G.neighborFinset h ∩ isoTwins G).card)
              + 3 * excessX n G + 32 ≤ 4 * n) :
    algConn G ≤ 2 := by
  by_contra hnf
  have hsl := slots_law G (by omega) hm h3 hnf hs0
  have hho := hoarding_law G (by omega) hm h3 hnf hs0
  have hgi := giant_excess_bound G (by omega)
  have hhX := heavy_le_excess G
  interval_cases n <;> omega

/-- **The starved band kill, widened to `32 ≤ n ≤ 49`.**  Identical to `starved_band_kill_35_49`
but routed through `starved_owner_choke_32_49`; a never-firing starved census on `32 ≤ n ≤ 49`
cannot exist, so the graph fires: `algConn G ≤ 2`. -/
theorem starved_band_kill_32_49 {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn32 : 32 ≤ n) (hn49 : n ≤ 49)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    algConn G ≤ 2 := by
  by_contra hnf
  have hcap : ∀ h : Fin n, G.degree h = 4 → (G.neighborFinset h ∩ isoTwins G).card ≤ 1 := by
    intro h hh
    have hc := starved_cap G hm h3 hnf h (by rw [hh]; omega)
    rw [hh] at hc
    omega
  have hindep : ∀ o₁ o₂ : Fin n, G.degree o₁ = 4 → G.degree o₂ = 4 →
      (G.neighborFinset o₁ ∩ isoTwins G).Nonempty →
      (G.neighborFinset o₂ ∩ isoTwins G).Nonempty → o₁ ≠ o₂ → ¬ G.Adj o₁ o₂ := by
    intro o₁ o₂ ho1 ho2 hn1 hn2 _hne
    obtain ⟨t₁, ht1⟩ := hn1
    obtain ⟨t₂, ht2⟩ := hn2
    rw [Finset.mem_inter, G.mem_neighborFinset] at ht1 ht2
    exact owner_independence (by omega) G hm h3 hnf o₁ o₂ t₁ t₂ ho1 ho2 ht1.1
      (mem_isoTwins.mp ht1.2).1 ht2.1 (mem_isoTwins.mp ht2.2).1
  exact absurd (starved_owner_choke_32_49 G hn32 hn49 hm h3 hs0
    (choke_count (by omega) G hm h3 hs0 hcap hindep)) hnf

/-- **The moat/choke upper bound on the continuous range `21 ≤ n ≤ 49`.**  Every `G` on `Fin n`
with `2(n−2)` edges has `algConn G ≤ 2`: below `32` this is `upperBound_moat`; on `32 ≤ n ≤ 49`
the graph is dispatched by minimum degree — low-degree test vector, `M`-edge moat, or the widened
starved band kill. -/
theorem upperBound_range_49 {n : ℕ} [Nonempty (Fin n)] (hn21 : 21 ≤ n) (hn49 : n ≤ 49)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2)) :
    algConn G ≤ 2 := by
  by_cases hle31 : n ≤ 31
  · exact upperBound_moat hn21 hle31 G hm
  · have hn32 : 32 ≤ n := by omega
    rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
    · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
      obtain ⟨u, hdeg⟩ := hlow
      refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
      rw [Finset.sdiff_nonempty]
      intro hsub
      have hle : (Finset.univ : Finset (Fin n)).card ≤ (insert u (G.neighborFinset u)).card :=
        Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at hle
      have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
        calc (insert u (G.neighborFinset u)).card
            ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
          _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
          _ ≤ 3 := by omega
      omega
    · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
      simp only [not_exists, not_le] at hlow
      have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by have := hlow v; omega
      by_cases hMedge : ∃ v w : Fin n, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w
      · obtain ⟨u, p, hu, hp, hadj⟩ := hMedge
        exact medge_moat_fires (by omega) G hm h3 u p hadj hu hp
      · have hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
          s0_of_no_medge G hMedge
        exact starved_band_kill_32_49 G hn32 hn49 hm h3 hs0

/-- **The ACMAX conjecture on the continuous range `21 ≤ n ≤ 49`.**  `K_{2,n-2}` is the maximizer
(`λ₂ = 2`) and every `G` with `2(n−2)` edges has `algConn G ≤ 2`. -/
theorem acmax_conjecture_range_49 {n : ℕ} [Nonempty (Fin n)]
    (hn21 : 21 ≤ n) (hn49 : n ≤ 49) :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two n (by omega), fun G hm => upperBound_range_49 hn21 hn49 G hm⟩

end ACMax



/-! ## The narrow capstone

The assembly of Kolokolnikov Conjecture 1.5 over every `n ≥ 4` uses one continuous
structural dispatch.  The small orders `4 ≤ n ≤ 20` are discharged by the banked
per-order theorems; `21 ≤ n ≤ 49` is the moat/choke range; the islands
`{50..54, 62, 63}` are handled separately; and every other order `n ≥ 55` is
split by graph structure into a low-degree certificate, an `M`-edge moat, or a
starved census.  The starved branch is killed directly by `starved_dead_ge_123`
for every `n ≥ 123`, leaving only the finite AHL window `55 ≤ n ≤ 122`
(`hStarved55`).  The equality clause `λ₂(K_{2,n-2}) = 2` is
`algConn_completeBipartite_two`. -/

namespace ACMax

open scoped Classical

/-- **The narrow capstone — the general ACMAX conjecture on every order `n ≥ 4`.**  The small
orders `4 ≤ m ≤ 20` are discharged **internally** by citing the seventeen banked per-order
theorems `acmax_conjecture_four … acmax_conjecture_twenty`, so only **two** hypotheses remain: the
seven Moore-extremal islands `{50, 51, 52, 53, 54, 62, 63}` (`hIslands`) and the single narrow
girth residual `hStarved55` — the impossibility of a never-firing starved census on the finite
window `55 ≤ m ≤ 122` minus the islands `{62, 63}`.  Every order `n ≥ 4` then satisfies the full
conjecture: `K_{2,n-2}` is the maximizer (`λ₂ = 2`) and every graph on `Fin n` with exactly
`2(n−2)` edges has `algConn ≤ 2`.  Above the finite window the same structural dispatch continues
without a separate large-`n` branch: every starved census with `n ≥ 123` is killed directly by
`starved_dead_ge_123` (`Counting.V9DischargeSharp`). -/
theorem acmax_conjecture_narrow
    (hIslands : ∀ (m : ℕ) [Nonempty (Fin m)],
        m ∈ ({50, 51, 52, 53, 54, 62, 63} : Finset ℕ) →
        algConn (completeBipartiteGraph (Fin 2) (Fin (m - 2))) = 2 ∧
          ∀ G : SimpleGraph (Fin m), G.edgeFinset.card = 2 * (m - 2) → algConn G ≤ 2)
    (hStarved55 : ∀ (m : ℕ) [Nonempty (Fin m)] (G : SimpleGraph (Fin m)),
        55 ≤ m → m ≤ 122 → m ≠ 62 → m ≠ 63 →
        G.edgeFinset.card = 2 * (m - 2) → (∀ v : Fin m, 3 ≤ G.degree v) →
        ¬ algConn G ≤ 2 →
        (∀ v w : Fin m, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) → False) :
    ∀ (n : ℕ) [Nonempty (Fin n)], 4 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 := by
  intro n _inst hn4
  by_cases h20 : n ≤ 20
  · -- `4 ≤ n ≤ 20`: cite the seventeen banked per-order theorems directly.
    interval_cases n
    · exact acmax_conjecture_four
    · exact acmax_conjecture_five
    · exact acmax_conjecture_six
    · exact acmax_conjecture_seven
    · exact acmax_conjecture_eight
    · exact acmax_conjecture_nine
    · exact acmax_conjecture_ten
    · exact acmax_conjecture_eleven
    · exact acmax_conjecture_twelve
    · exact acmax_conjecture_thirteen
    · exact acmax_conjecture_fourteen
    · exact acmax_conjecture_fifteen
    · exact acmax_conjecture_sixteen
    · exact acmax_conjecture_seventeen
    · exact acmax_conjecture_eighteen
    · exact acmax_conjecture_nineteen
    · exact acmax_conjecture_twenty
  by_cases h49 : n ≤ 49
  · exact acmax_conjecture_range_49 (by omega) h49
  refine ⟨algConn_completeBipartite_two n (by omega), fun G hm => ?_⟩
  by_cases hisland : n ∈ ({50, 51, 52, 53, 54, 62, 63} : Finset ℕ)
  · exact (hIslands n hisland).2 G hm
  have h55 : 55 ≤ n := by
    by_contra hlt
    exact hisland (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
  have hne62 : n ≠ 62 := fun h => hisland (by rw [h]; decide)
  have hne63 : n ≠ 63 := fun h => hisland (by rw [h]; decide)
  rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
  · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [Finset.sdiff_nonempty]
    intro hsub
    have huniv : (Finset.univ : Finset (Fin n)).card ≤ (insert u (G.neighborFinset u)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at huniv
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    omega
  · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    by_cases hMedge : ∃ v w : Fin n, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w
    · obtain ⟨u, p, hu, hp, hadj⟩ := hMedge
      exact medge_moat_fires (by omega) G hm h3 u p hadj hu hp
    · have hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
        s0_of_no_medge G hMedge
      by_contra hnf
      by_cases h123 : 123 ≤ n
      · exact starved_dead_ge_123 G h123 hm h3 hnf hs0
      · exact hStarved55 n G h55 (by omega) hne62 hne63 hm h3 hnf hs0

end ACMax
