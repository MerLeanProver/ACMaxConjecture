import ACMaxConjecture.Counting.StarvedCensus
import ACMaxConjecture.Counting.CompactCell

/-!
# The island rows: the untouched twin, its σ-usability, and the far-side ledger

Three of the leaf rows of the **island attack** (§3–4): the pure-counting pieces that, with the
twin-rooted level-sharp ball (`Islands.Ball`) and the landed census rows, close the band
`48 ≤ n ≤ 63` import-free.

* **IB2** `untouched_twin_exists` — the *touch-count* form.  Every heavy hub (`deg ≥ 5`)
  hosts at most `deg − 3` `M`-isolated twins (`starved_cap`, giants credited `+3`), so the
  heavy-touched twins number at most `X + h + 3·n_g` (`cap_sum_le`).  There are `8 + X`
  twins (`deg3_card_eq_eight_add_excess`), hence whenever `h + 3·n_g < 8` some twin has **no
  degree-`≥ 5` neighbour**.  The touch-count avoids the naive excess-pigeonhole (which ties at
  the `n = 62` deg-`7` cell).
* **IB3** `island_sigma_usable` — the localized `σ`-usability.  A degree-`3` vertex all of
  whose neighbours have degree `≤ 4` has `sigS = Σ σ(deg) ≤ 3·σ(4) = 3/2 ≤ 2` (`σ(4) = 1/2`),
  so it is `σ`-usable.  Hypothesis on `N(t)` only.
* **IB5** `island_nonusable_cover` — the far-side class ledger the band kill consumes.  On the
  compact cell (`¬HasUsableFarPair`) with a usable anchor `t`, every vertex outside the
  radius-`3` ball of `t` is non-usable (`nonusable_of_far`), splitting into the heavy set
  (`h` vertices) and the non-usable lights (`≤ 5·X`, `card_nonusable_light_le`); hence
  `n ≤ |closeSet t| + 5·X + h`.  Combined with the ball bound `|closeSet t| ≤ 40 + X` this is
  row B `n ≤ 40 + 6X + h`.

Every row is `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ACMax

open Finset
open scoped Classical

/-- **IB2 — the untouched twin exists (touch-count form).**  In a never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`), the number of `M`-isolated twins with a degree-`≥ 5` neighbour
is at most `X + h + 3·n_g` (heavy caps plus the `3`-per-giant credit, `cap_sum_le`), while the
twins number `8 + X`.  So if `h + 3·n_g < 8` (with `h` = heavies, `n_g` = giants) there is a
degree-`3` vertex all of whose neighbours have degree `≤ 4`. -/
theorem untouched_twin_exists {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn : 8 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hlt : (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card
        + 3 * ((hubSet G).filter (fun w => n + 15 < 9 * G.degree w)).card < 8) :
    ∃ t : Fin n, G.degree t = 3 ∧ ∀ w ∈ G.neighborFinset t, G.degree w ≤ 4 := by
  set S := Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v) with hS
  set Gi := (hubSet G).filter (fun w => n + 15 < 9 * G.degree w) with hGi
  have htwin : (isoTwins G).card = 8 + excessX n G := by
    rw [← deg3_eq_isoTwins_of_s0 G hs0, deg3_card_eq_eight_add_excess n G (by omega) hm h3]
  have hSsub : S ⊆ hubSet G := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    exact mem_hubSet.mpr (by omega)
  by_contra hcon
  push Not at hcon
  -- every twin is hosted by a heavy neighbour, so lies in the heavy-biUnion of twin slots
  have hsub : isoTwins G ⊆ S.biUnion (fun w => G.neighborFinset w ∩ isoTwins G) := by
    intro t ht
    obtain ⟨w, hw, hwd⟩ := hcon t (mem_isoTwins.mp ht).1
    refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
    · rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ w, by omega⟩
    · rw [Finset.mem_inter]
      refine ⟨?_, ht⟩
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      exact hw.symm
  have hcard1 : (isoTwins G).card ≤ ∑ w ∈ S, (G.neighborFinset w ∩ isoTwins G).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcap := cap_sum_le G hm h3 hnf S hSsub
  have hexc : (∑ w ∈ S, (G.degree w - 4)) = excessX n G := by
    rw [hS]; rfl
  have hdeg3 : ∑ w ∈ S, (G.degree w - 3) = excessX n G + S.card := by
    have hpt : ∀ w ∈ S, G.degree w - 3 = (G.degree w - 4) + 1 := by
      intro w hw; rw [hS, Finset.mem_filter] at hw; omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      mul_one, hexc]
  have hgiant : (S.filter (fun w => n + 15 < 9 * G.degree w)).card ≤ Gi.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hGi, Finset.mem_filter]
    exact ⟨hSsub hx.1, hx.2⟩
  rw [hdeg3] at hcap
  omega

/-- **IB3 — the untouched twin is σ-usable (localized).**  A degree-`3` vertex `t` whose
neighbours all have degree `≤ 4` has each slot value `σ(deg w) ≤ σ(4) = 1/2`, so
`sigS G t ≤ 3·(1/2) = 3/2 ≤ 2`: it is `σ`-usable.  Hypothesis touches only `N(t)`. -/
theorem island_sigma_usable {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (t : Fin n) (ht : G.degree t = 3)
    (hnbr : ∀ w ∈ G.neighborFinset t, G.degree w ≤ 4) :
    sigS G t ≤ 2 := by
  have hb : ∀ w ∈ G.neighborFinset t, sigma (G.degree w) ≤ (1 : ℝ) / 2 := by
    intro w hw
    calc sigma (G.degree w) ≤ sigma 4 := sigma_le_of_le (h3 w) (hnbr w hw)
      _ = 1 / 2 := sigma_four
  have hsum : sigS G t ≤ (G.neighborFinset t).card • ((1 : ℝ) / 2) := by
    unfold sigS
    exact Finset.sum_le_card_nsmul _ _ _ hb
  have hcard : (G.neighborFinset t).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact ht
  rw [hcard, nsmul_eq_mul] at hsum
  norm_num at hsum
  linarith

/-- **IB5 — the far-side class ledger.**  On the compact cell (`¬HasUsableFarPair`) with a
usable anchor `t` (`sigS G t ≤ 2`), every vertex outside the radius-`3` ball of `t` is
non-usable (`nonusable_of_far`); splitting the non-usable population into heavies (`h`) and
non-usable lights (`≤ 5·X`, `card_nonusable_light_le`) gives
`n ≤ |closeSet G t| + 5·X + h`. -/
theorem island_nonusable_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hcpt : ¬HasUsableFarPair G)
    (t : Fin n) (hu : sigS G t ≤ 2) :
    n ≤ (closeSet G t).card + 5 * excessX n G
        + (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card := by
  have hcover : (Finset.univ : Finset (Fin n)) ⊆
      closeSet G t
        ∪ Finset.univ.filter (fun v : Fin n => G.degree v ≤ 4 ∧ 2 < sigS G v)
        ∪ Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v) := by
    intro v _
    by_cases hc : v ∈ closeSet G t
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
    · have hs := nonusable_of_far G hcpt t hu v hc
      by_cases hd : G.degree v ≤ 4
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hd, hs⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩)
  have hsplit : n ≤ (closeSet G t).card
      + (Finset.univ.filter (fun v : Fin n => G.degree v ≤ 4 ∧ 2 < sigS G v)).card
      + (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (closeSet G t
            ∪ Finset.univ.filter (fun v : Fin n => G.degree v ≤ 4 ∧ 2 < sigS G v)
            ∪ Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card :=
          Finset.card_le_card hcover
      _ ≤ (closeSet G t
            ∪ Finset.univ.filter
                (fun v : Fin n => G.degree v ≤ 4 ∧ 2 < sigS G v)).card
          + (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card :=
          Finset.card_union_le _ _
      _ ≤ (closeSet G t).card
          + (Finset.univ.filter
              (fun v : Fin n => G.degree v ≤ 4 ∧ 2 < sigS G v)).card
          + (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hlight := card_nonusable_light_le G h3
  omega

end ACMax
