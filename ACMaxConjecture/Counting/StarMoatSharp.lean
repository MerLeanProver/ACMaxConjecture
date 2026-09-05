import Mathlib
import ACMaxConjecture.Counting.Moats
import ACMaxConjecture.Counting.SparseCore
import ACMaxConjecture.Counting.TripleCensus
import ACMaxConjecture.Counting.DecoratedC4

/-!
# The sharpened `Z1` star moat

`star_moat_fires` (`Counting/Moats`) fires a degree-`d` hub carrying `d − 2` degree-`3` twins
whenever `9d ≤ n + 15`, which at `d = 4` gives only `n ≥ 21`. That threshold is not
intrinsic: it bounds the outer boundary `∂₂ = e(F, S₂)` from the moat side alone,

  `∂₂ ≤ Σ_F (deg − 1) = E_F + 2|F|`,

and then charging `E_F` against the whole excess budget `n − 8`.  The bulk side is never counted.

This file adds the missing bulk count. Writing `E_F`, `E₂` for the excess carried by the moat `F`
and the bulk
`S₂`, the two sides say

  `∂₂ ≤ E_F + 2f`     (moat side, as before)
  `∂₂ + P₂ = 3|S₂| + E₂` (bulk side: every `S₂`-vertex sends its degree into `F ⊎ S₂`)

with `P₂` the ordered adjacent pairs inside `S₂`. Under `hs0` the degree-`3` vertices of `S₂` are
pairwise non-adjacent, so every `S₂`-edge has an endpoint of degree at least `4` and
`P₂ ≤ 8·E₂`. For `n ≥ 16`, combining this estimate with the moat ledger either fires the
original cut or exposes a sparse bulk core, which supplies another cut certificate. The five
remaining orders `10 ≤ n ≤ 15` have rigid excess profiles; the same ledgers, supplemented by
triangle and decorated-`C₄` certificates at the tight corners, close them directly.
-/

namespace ACMax

open Finset
open scoped Classical

/-- **The bulk-side pair bound.**  In a starved census (`hs0`: no degree-`3`–degree-`3` edge), the
ordered adjacent pairs inside any set `T` are at most `8·E_T`, where `E_T = Σ_T (deg − 3)`: every
adjacent pair inside `T` has an endpoint of degree `≥ 4`, there are at most `E_T` such vertices in
`T`, and each has degree at most `3 + (deg − 3)`. -/
theorem pairs_le_eight_excess {n : ℕ} (G : SimpleGraph (Fin n))
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (T : Finset (Fin n)) :
    ((T ×ˢ T).filter (fun q => G.Adj q.1 q.2)).card ≤ 8 * ∑ v ∈ T, (G.degree v - 3) := by
  classical
  set A : Finset (Fin n) := T.filter (fun v => 4 ≤ G.degree v) with hA
  set B : Finset (Fin n) := T.filter (fun v => ¬ (4 ≤ G.degree v)) with hB
  set E : ℕ := ∑ v ∈ T, (G.degree v - 3) with hE
  -- the ordered-pair count as a slice sum
  have hcnt : ∀ (X Y : Finset (Fin n)),
      ((X ×ˢ Y).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ X, (G.neighborFinset a ∩ Y).card := by
    intro X Y
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ Y = Y.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- `A ⊎ B = T`
  have hAB : ∑ v ∈ A, (G.neighborFinset v ∩ T).card + ∑ v ∈ B, (G.neighborFinset v ∩ T).card
      = ∑ v ∈ T, (G.neighborFinset v ∩ T).card := by
    rw [hA, hB]
    exact Finset.sum_filter_add_sum_filter_not T _ _
  -- a degree-`3` vertex of `T` has all its `T`-neighbours in `A`
  have hBslice : ∀ v ∈ B, G.neighborFinset v ∩ T = G.neighborFinset v ∩ A := by
    intro v hv
    rw [hB, Finset.mem_filter] at hv
    have hv3 : G.degree v = 3 := by have := h3 v; omega
    ext x
    simp only [Finset.mem_inter, hA, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hxT⟩
      refine ⟨hx, hxT, ?_⟩
      by_contra hlt
      have hx3 : G.degree x = 3 := by have := h3 x; omega
      exact hs0 v x hv3 hx3 ((G.mem_neighborFinset v x).mp hx)
    · rintro ⟨hx, hxT, _⟩; exact ⟨hx, hxT⟩
  -- transpose the `B`-half onto `A`
  have hBA : ∑ v ∈ B, (G.neighborFinset v ∩ T).card ≤ ∑ v ∈ A, (G.neighborFinset v ∩ T).card := by
    calc ∑ v ∈ B, (G.neighborFinset v ∩ T).card
        = ∑ v ∈ B, (G.neighborFinset v ∩ A).card :=
          Finset.sum_congr rfl (fun v hv => by rw [hBslice v hv])
      _ = ∑ w ∈ A, (G.neighborFinset w ∩ B).card := cross_count G B A
      _ ≤ ∑ w ∈ A, (G.neighborFinset w ∩ T).card := by
          refine Finset.sum_le_sum (fun w _ => Finset.card_le_card ?_)
          exact Finset.inter_subset_inter_left (by rw [hB]; exact Finset.filter_subset _ _)
  -- the `A`-half against the excess
  have hAcard : A.card ≤ E := by
    rw [hE, hA]
    calc (T.filter (fun v => 4 ≤ G.degree v)).card
        = ∑ _v ∈ T.filter (fun v => 4 ≤ G.degree v), 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ v ∈ T.filter (fun v => 4 ≤ G.degree v), (G.degree v - 3) := by
          refine Finset.sum_le_sum (fun v hv => ?_)
          have := (Finset.mem_filter.mp hv).2; omega
      _ ≤ ∑ v ∈ T, (G.degree v - 3) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hAexc : ∑ v ∈ A, (G.degree v - 3) ≤ E :=
    Finset.sum_le_sum_of_subset (by rw [hA]; exact Finset.filter_subset _ _)
  have hAdeg : ∑ v ∈ A, (G.neighborFinset v ∩ T).card ≤ 3 * A.card + E := by
    calc ∑ v ∈ A, (G.neighborFinset v ∩ T).card
        ≤ ∑ v ∈ A, G.degree v := by
          refine Finset.sum_le_sum (fun v _ => ?_)
          rw [← G.card_neighborFinset_eq_degree]
          exact Finset.card_le_card Finset.inter_subset_left
      _ = ∑ v ∈ A, ((G.degree v - 3) + 3) :=
          Finset.sum_congr rfl (fun v _ => by have := h3 v; omega)
      _ = (∑ v ∈ A, (G.degree v - 3)) + 3 * A.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ 3 * A.card + E := by omega
  rw [hcnt T T]
  omega

set_option maxHeartbeats 2000000 in
/-- **The sparse-core `Z1` star moat.** A degree-`4` hub with two distinct degree-`3`
neighbors fires at every `n ≥ 10` in the starved regime. Above order fifteen an
excessive bulk boundary produces a sparse core; the lower endpoints are closed
by their rigid incidence censuses. -/
theorem z1_star_moat_fires_core {n : ℕ} [Nonempty (Fin n)] (hn : 10 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (h t₁ t₂ : Fin n) (hdh : G.degree h = 4) (ht1 : G.Adj h t₁) (ht2 : G.Adj h t₂)
    (hd1 : G.degree t₁ = 3) (hd2 : G.degree t₂ = 3) (ht12 : t₁ ≠ t₂) :
    algConn G ≤ 2 := by
  classical
  letI : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hht1 : h ≠ t₁ := ht1.ne
  have hht2 : h ≠ t₂ := ht2.ne
  set S₁ : Finset (Fin n) := {h, t₁, t₂} with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  -- the ordered-pair counting helpers
  have hcnt : ∀ (X Y : Finset (Fin n)),
      ((X ×ˢ Y).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ X, (G.neighborFinset a ∩ Y).card := by
    intro X Y
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ Y = Y.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  have htrans : ∀ (X Y : Finset (Fin n)),
      ((X ×ˢ Y).filter (fun q => G.Adj q.1 q.2)).card
        = ((Y ×ˢ X).filter (fun q => G.Adj q.1 q.2)).card := by
    intro X Y
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- `|S₁| = 3`
  have hS1card : S₁.card = 3 := by
    rw [hS1def, Finset.card_insert_of_notMem (by simp [hht1, hht2]),
      Finset.card_insert_of_notMem (by simp [ht12]), Finset.card_singleton]
  have hS1ne : S₁.Nonempty := ⟨h, by rw [hS1def]; exact Finset.mem_insert_self _ _⟩
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin, Finset.card_union_of_disjoint hdisjS1F]
  -- every `S₁`-slice leaves at most two edges
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ 2 := by
    intro x hx
    rw [hS1def, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · -- `x = h`: both twins `t₁, t₂` sit inside `S₁`, and `deg h = 4`
      have hpart : (G.neighborFinset x ∩ S₁).card + (G.neighborFinset x \ S₁).card
          = G.degree x := by
        rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
      have hy : t₁ ∈ G.neighborFinset x ∩ S₁ := by
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨ht1, by rw [hS1def]; simp⟩
      have hz : t₂ ∈ G.neighborFinset x ∩ S₁ := by
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨ht2, by rw [hS1def]; simp⟩
      have h2 : 1 < (G.neighborFinset x ∩ S₁).card :=
        Finset.one_lt_card_iff.mpr ⟨t₁, t₂, hy, hz, ht12⟩
      omega
    · -- `x = t₁`: its neighbours `h` is in `S₁`, and `deg = 3`
      have hpart : (G.neighborFinset x ∩ S₁).card + (G.neighborFinset x \ S₁).card
          = G.degree x := by
        rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
      have hmem : h ∈ G.neighborFinset x ∩ S₁ := by
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨ht1.symm, by rw [hS1def]; simp⟩
      have := Finset.card_pos.mpr ⟨h, hmem⟩
      omega
    · have hpart : (G.neighborFinset x ∩ S₁).card + (G.neighborFinset x \ S₁).card
          = G.degree x := by
        rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
      have hmem : h ∈ G.neighborFinset x ∩ S₁ := by
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨ht2.symm, by rw [hS1def]; simp⟩
      have := Finset.card_pos.mpr ⟨h, hmem⟩
      omega
  -- `|F| ≤ 6` and `∂₁ ≤ 6`
  have hFcard : F.card ≤ 6 := by
    have hFsub : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    calc F.card ≤ (S₁.biUnion (fun x => G.neighborFinset x \ S₁)).card :=
          Finset.card_le_card hFsub
      _ ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ S₁, 2 := Finset.sum_le_sum hslice
      _ = 6 := by rw [Finset.sum_const, smul_eq_mul, hS1card]
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 6 := by
    rw [hcnt S₁ F]
    have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ 2 := by
      intro a ha
      refine le_trans (Finset.card_le_card ?_) (hslice a ha)
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      have hxF := hx.2
      rw [hFdef, Finset.mem_sdiff] at hxF
      exact hxF.2
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ ∑ _a ∈ S₁, 2 := Finset.sum_le_sum hterm
      _ = 6 := by rw [Finset.sum_const, smul_eq_mul, hS1card]
  -- the excess ledger, split over `S₁ ⊎ F ⊎ S₂`
  have hE1 : ∑ v ∈ S₁, (G.degree v - 3) = 1 := by
    rw [hS1def, Finset.sum_insert (by simp [hht1, hht2]),
      Finset.sum_insert (by simp [ht12]), Finset.sum_singleton, hdh, hd1, hd2]
    omega
  have hexc : (∑ v ∈ F, (G.degree v - 3)) + (∑ v ∈ S₂, (G.degree v - 3)) + 1 = n - 8 := by
    have htot : ∑ v : Fin n, (G.degree v - 3) = n - 8 := total_excess_eq (by omega) G hm h3
    have hsplitc : (∑ v ∈ S₁ ∪ F, (G.degree v - 3)) + (∑ v ∈ S₂, (G.degree v - 3))
        = ∑ v : Fin n, (G.degree v - 3) := by
      rw [hS2def]; exact Finset.sum_add_sum_compl _ _
    have hsplitu : ∑ v ∈ S₁ ∪ F, (G.degree v - 3)
        = (∑ v ∈ S₁, (G.degree v - 3)) + ∑ v ∈ F, (G.degree v - 3) :=
      Finset.sum_union hdisjS1F
    omega
  -- no `S₁`–`S₂` edge, and `(S₁ ∪ S₂)ᶜ = F`
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ v ∈ S₂, ¬G.Adj a v := by
    intro a ha v hv hadj
    rw [hS2def, Finset.mem_compl] at hv
    have hvnotS1 : v ∉ S₁ := fun hh => hv (Finset.mem_union_left F hh)
    apply hv
    refine Finset.mem_union_right S₁ ?_
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hvnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a v).mpr hadj⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hv
      obtain ⟨hvS1, hvS2⟩ := hv
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hvS2
      rcases hvS2 with hh | hh
      · exact absurd hh hvS1
      · exact hh
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hv,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hv⟩
  have hFbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
    intro w hw
    obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
      have hwF := hw
      rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
      obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
      exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
    have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
    have haS2 : a ∉ S₂ := by
      rw [hS2def, Finset.mem_compl, not_not]
      exact Finset.mem_union_left F haS1
    have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl
      exact haS2 hx.2
    calc (G.neighborFinset w ∩ S₂).card ≤ ((G.neighborFinset w).erase a).card :=
          Finset.card_le_card hsub
      _ = G.degree w - 1 := by
          rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
  -- **moat side**: `∂₂ ≤ E_F + 2·|F|`
  have hmoat : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card
      ≤ (∑ w ∈ F, (G.degree w - 3)) + 2 * F.card := by
    rw [htrans S₂ F, hcnt F S₂]
    calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ ∑ w ∈ F, (G.degree w - 1) :=
          Finset.sum_le_sum hFbound
      _ = ∑ w ∈ F, ((G.degree w - 3) + 2) :=
          Finset.sum_congr rfl (fun w _ => by have := h3 w; omega)
      _ = (∑ w ∈ F, (G.degree w - 3)) + 2 * F.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- **bulk side**: `∂₂ + P₂ = 3·|S₂| + E₂`
  have hbulk : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card
        + ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card
      = 3 * S₂.card + ∑ v ∈ S₂, (G.degree v - 3) := by
    rw [hcnt S₂ F, hcnt S₂ S₂, ← Finset.sum_add_distrib]
    have hpt : ∀ v ∈ S₂,
        (G.neighborFinset v ∩ F).card + (G.neighborFinset v ∩ S₂).card = G.degree v := by
      intro v hv
      have hsplitv : G.neighborFinset v ∩ (F ∪ S₂) = G.neighborFinset v := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
        by_contra hcon
        push Not at hcon
        have hxS1 : x ∈ S₁ := by
          have hx2 : x ∉ S₂ := hcon.2
          rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hx2
          rcases hx2 with hh | hh
          · exact hh
          · exact absurd hh hcon.1
        exact hnc x hxS1 v hv (G.adj_symm ((G.mem_neighborFinset v x).mp hx))
      have hdisjFS2 : Disjoint (G.neighborFinset v ∩ F) (G.neighborFinset v ∩ S₂) := by
        rw [Finset.disjoint_left]
        intro a haF haS2
        rw [Finset.mem_inter] at haF haS2
        have : a ∈ S₁ ∪ F := Finset.mem_union_right S₁ haF.2
        rw [hS2def, Finset.mem_compl] at haS2
        exact haS2.2 this
      have := Finset.card_union_of_disjoint hdisjFS2
      rw [← Finset.inter_union_distrib_left, hsplitv, G.card_neighborFinset_eq_degree] at this
      omega
    rw [Finset.sum_congr rfl hpt]
    have : ∑ v ∈ S₂, G.degree v = ∑ v ∈ S₂, ((G.degree v - 3) + 3) :=
      Finset.sum_congr rfl (fun v _ => by have := h3 v; omega)
    rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    omega
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos]
    omega
  by_cases hcheap : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₂.card
  · refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
    rw [hFeq, hS1card]
    nlinarith [he1, hcheap, Nat.zero_le S₂.card]
  · by_cases hlarge : 2 * ∑ v ∈ S₂, (G.degree v - 3) < internalPairCount G S₂
    · obtain ⟨T, hTsub, hTne, hTslice⟩ :=
        exists_sparse_core_of_twice_excess_lt_pairs G h3 S₂ hlarge
      have hdisjT : Disjoint S₁ T := hdisj.mono_right hTsub
      have hncT : ∀ u ∈ S₁, ∀ v ∈ T, ¬G.Adj u v :=
        fun u hu v hv => hnc u hu v (hTsub hv)
      exact algConn_le_two_of_sparse_core_clusters G S₁ T hS1ne hTne hdisjT hncT
        hslice hTslice
    · by_cases hn11 : n ≤ 11
      · have hpairle : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card
            ≤ 2 * ∑ v ∈ S₂, (G.degree v - 3) := by
          simpa [internalPairCount] using (not_lt.mp hlarge)
        have hEFEB : (∑ v ∈ F, (G.degree v - 3)) +
            (∑ v ∈ S₂, (G.degree v - 3)) = n - 9 := by
          omega
        set A : Finset (Fin n) := G.neighborFinset h \ S₁ with hAdef
        set C : Finset (Fin n) := G.neighborFinset t₁ \ S₁ with hCdef
        set D : Finset (Fin n) := G.neighborFinset t₂ \ S₁ with hDdef
        have hhS1 : h ∈ S₁ := by rw [hS1def]; simp
        have ht1S1 : t₁ ∈ S₁ := by rw [hS1def]; simp
        have ht2S1 : t₂ ∈ S₁ := by rw [hS1def]; simp
        have hAcard : A.card = 2 := by
          have hinterSub : G.neighborFinset h ∩ S₁ ⊆ S₁.erase h := by
            intro x hx
            rw [Finset.mem_inter] at hx
            rw [Finset.mem_erase]
            refine ⟨?_, hx.2⟩
            rintro rfl
            exact G.irrefl ((G.mem_neighborFinset _ _).mp hx.1)
          have hinterLe : (G.neighborFinset h ∩ S₁).card ≤ 2 := by
            calc
              (G.neighborFinset h ∩ S₁).card ≤ (S₁.erase h).card :=
                Finset.card_le_card hinterSub
              _ = 2 := by rw [Finset.card_erase_of_mem hhS1, hS1card]
          have hpart : (G.neighborFinset h ∩ S₁).card + A.card = G.degree h := by
            rw [hAdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
          have houtLe : A.card ≤ 2 := by simpa [hAdef] using hslice h hhS1
          omega
        have hCcard : C.card = 2 := by
          have hinterSub : G.neighborFinset t₁ ∩ S₁ ⊆ {h} := by
            intro x hx
            rw [Finset.mem_inter] at hx
            have hadj : G.Adj t₁ x := (G.mem_neighborFinset t₁ x).mp hx.1
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hx
            rcases hx.2 with hxh | hxt1 | hxt2
            · simp [hxh]
            · exfalso
              exact G.ne_of_adj hadj hxt1.symm
            · exfalso
              exact hs0 t₁ t₂ hd1 hd2 (by simpa [hxt2] using hadj)
          have hinterLe : (G.neighborFinset t₁ ∩ S₁).card ≤ 1 :=
            (Finset.card_le_card hinterSub).trans_eq (Finset.card_singleton h)
          have hpart : (G.neighborFinset t₁ ∩ S₁).card + C.card = G.degree t₁ := by
            rw [hCdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
          have houtLe : C.card ≤ 2 := by simpa [hCdef] using hslice t₁ ht1S1
          omega
        have hFsplit : F = A ∪ C ∪ D := by
          ext x
          constructor
          · intro hxF
            rw [hFdef, Finset.mem_sdiff] at hxF
            obtain ⟨hxbi, hxnot⟩ := hxF
            rw [Finset.mem_biUnion] at hxbi
            obtain ⟨p, hp, hpx⟩ := hxbi
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hp
            rw [Finset.mem_union, Finset.mem_union]
            rcases hp with rfl | rfl | rfl
            · exact Or.inl (Or.inl (by
                rw [hAdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩))
            · exact Or.inl (Or.inr (by
                rw [hCdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩))
            · exact Or.inr (by
                rw [hDdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩)
          · intro hx
            rw [Finset.mem_union, Finset.mem_union] at hx
            rw [hFdef, Finset.mem_sdiff]
            rcases hx with (hxA | hxC) | hxD
            · have hxA' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hxA
              rw [Finset.mem_sdiff] at hxA'
              exact ⟨Finset.mem_biUnion.mpr ⟨h, hhS1, hxA'.1⟩, hxA'.2⟩
            · have hxC' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hxC
              rw [Finset.mem_sdiff] at hxC'
              exact ⟨Finset.mem_biUnion.mpr ⟨t₁, ht1S1, hxC'.1⟩, hxC'.2⟩
            · have hxD' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hxD
              rw [Finset.mem_sdiff] at hxD'
              exact ⟨Finset.mem_biUnion.mpr ⟨t₂, ht2S1, hxD'.1⟩, hxD'.2⟩
        set K : Finset (Fin n) := C ∪ D with hKdef
        have hFAK : F = A ∪ K := by
          rw [hFsplit, hKdef, Finset.union_assoc]
        have hCsubK : C ⊆ K := by rw [hKdef]; exact Finset.subset_union_left
        have hKsubF : K ⊆ F := by rw [hFAK]; exact Finset.subset_union_right
        have hCadj : ∀ x ∈ C, G.Adj t₁ x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hx
          exact (G.mem_neighborFinset t₁ x).mp (Finset.mem_sdiff.mp hx').1
        have hDadj : ∀ x ∈ D, G.Adj t₂ x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hx
          exact (G.mem_neighborFinset t₂ x).mp (Finset.mem_sdiff.mp hx').1
        have hKdeg : ∀ x ∈ K, 4 ≤ G.degree x := by
          intro x hx
          rw [hKdef, Finset.mem_union] at hx
          rcases hx with hxC | hxD
          · by_contra hnot
            have hdx : G.degree x = 3 := by have := h3 x; omega
            exact hs0 t₁ x hd1 hdx (hCadj x hxC)
          · by_contra hnot
            have hdx : G.degree x = 3 := by have := h3 x; omega
            exact hs0 t₂ x hd2 hdx (hDadj x hxD)
        have hKexc : K.card ≤ ∑ x ∈ K, (G.degree x - 3) := by
          calc
            K.card = ∑ _x ∈ K, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
            _ ≤ ∑ x ∈ K, (G.degree x - 3) :=
              Finset.sum_le_sum (fun x hx => by have := hKdeg x hx; omega)
        have hKexcF : ∑ x ∈ K, (G.degree x - 3) ≤
            ∑ x ∈ F, (G.degree x - 3) :=
          Finset.sum_le_sum_of_subset hKsubF
        have hKtwo : 2 ≤ K.card := by
          calc
            2 = C.card := hCcard.symm
            _ ≤ K.card := Finset.card_le_card hCsubK
        have hAKle := Finset.card_union_le A K
        have hFAKcard : F.card = (A ∪ K).card := congrArg Finset.card hFAK
        exfalso
        omega
      by_cases hn12 : n = 12
      · subst n
        have hpairle : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card
            ≤ 2 * ∑ v ∈ S₂, (G.degree v - 3) := by
          simpa [internalPairCount] using (not_lt.mp hlarge)
        have hEFEB : (∑ v ∈ F, (G.degree v - 3)) +
            (∑ v ∈ S₂, (G.degree v - 3)) = 3 := by
          omega
        have hFge5 : 5 ≤ F.card := by omega
        set A : Finset (Fin 12) := G.neighborFinset h \ S₁ with hAdef
        set C : Finset (Fin 12) := G.neighborFinset t₁ \ S₁ with hCdef
        set D : Finset (Fin 12) := G.neighborFinset t₂ \ S₁ with hDdef
        have hhS1 : h ∈ S₁ := by rw [hS1def]; simp
        have ht1S1 : t₁ ∈ S₁ := by rw [hS1def]; simp
        have ht2S1 : t₂ ∈ S₁ := by rw [hS1def]; simp
        have hAcard : A.card = 2 := by
          have hinterSub : G.neighborFinset h ∩ S₁ ⊆ S₁.erase h := by
            intro x hx
            rw [Finset.mem_inter] at hx
            rw [Finset.mem_erase]
            refine ⟨?_, hx.2⟩
            rintro rfl
            exact G.irrefl ((G.mem_neighborFinset _ _).mp hx.1)
          have hinterLe : (G.neighborFinset h ∩ S₁).card ≤ 2 := by
            calc
              (G.neighborFinset h ∩ S₁).card ≤ (S₁.erase h).card :=
                Finset.card_le_card hinterSub
              _ = 2 := by rw [Finset.card_erase_of_mem hhS1, hS1card]
          have hpart : (G.neighborFinset h ∩ S₁).card + A.card = G.degree h := by
            rw [hAdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
          have houtLe : A.card ≤ 2 := by simpa [hAdef] using hslice h hhS1
          omega
        have hCcard : C.card = 2 := by
          have hinterSub : G.neighborFinset t₁ ∩ S₁ ⊆ {h} := by
            intro x hx
            rw [Finset.mem_inter] at hx
            have hadj : G.Adj t₁ x := (G.mem_neighborFinset t₁ x).mp hx.1
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hx
            rcases hx.2 with hxh | hxt1 | hxt2
            · simp [hxh]
            · exfalso
              exact G.ne_of_adj hadj hxt1.symm
            · exfalso
              exact hs0 t₁ t₂ hd1 hd2 (by simpa [hxt2] using hadj)
          have hinterLe : (G.neighborFinset t₁ ∩ S₁).card ≤ 1 :=
            (Finset.card_le_card hinterSub).trans_eq (Finset.card_singleton h)
          have hpart : (G.neighborFinset t₁ ∩ S₁).card + C.card = G.degree t₁ := by
            rw [hCdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
          have houtLe : C.card ≤ 2 := by simpa [hCdef] using hslice t₁ ht1S1
          omega
        have hDcard : D.card = 2 := by
          have hinterSub : G.neighborFinset t₂ ∩ S₁ ⊆ {h} := by
            intro x hx
            rw [Finset.mem_inter] at hx
            have hadj : G.Adj t₂ x := (G.mem_neighborFinset t₂ x).mp hx.1
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hx
            rcases hx.2 with hxh | hxt1 | hxt2
            · simp [hxh]
            · exfalso
              exact hs0 t₂ t₁ hd2 hd1 (by simpa [hxt1] using hadj)
            · exfalso
              exact G.ne_of_adj hadj hxt2.symm
          have hinterLe : (G.neighborFinset t₂ ∩ S₁).card ≤ 1 :=
            (Finset.card_le_card hinterSub).trans_eq (Finset.card_singleton h)
          have hpart : (G.neighborFinset t₂ ∩ S₁).card + D.card = G.degree t₂ := by
            rw [hDdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
          have houtLe : D.card ≤ 2 := by simpa [hDdef] using hslice t₂ ht2S1
          omega
        have hFsplit : F = A ∪ C ∪ D := by
          ext x
          constructor
          · intro hxF
            rw [hFdef, Finset.mem_sdiff] at hxF
            obtain ⟨hxbi, hxnot⟩ := hxF
            rw [Finset.mem_biUnion] at hxbi
            obtain ⟨p, hp, hpx⟩ := hxbi
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hp
            rw [Finset.mem_union, Finset.mem_union]
            rcases hp with rfl | rfl | rfl
            · exact Or.inl (Or.inl (by
                rw [hAdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩))
            · exact Or.inl (Or.inr (by
                rw [hCdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩))
            · exact Or.inr (by
                rw [hDdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩)
          · intro hx
            rw [Finset.mem_union, Finset.mem_union] at hx
            rw [hFdef, Finset.mem_sdiff]
            rcases hx with (hxA | hxC) | hxD
            · have hxA' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hxA
              rw [Finset.mem_sdiff] at hxA'
              exact ⟨Finset.mem_biUnion.mpr ⟨h, hhS1, hxA'.1⟩, hxA'.2⟩
            · have hxC' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hxC
              rw [Finset.mem_sdiff] at hxC'
              exact ⟨Finset.mem_biUnion.mpr ⟨t₁, ht1S1, hxC'.1⟩, hxC'.2⟩
            · have hxD' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hxD
              rw [Finset.mem_sdiff] at hxD'
              exact ⟨Finset.mem_biUnion.mpr ⟨t₂, ht2S1, hxD'.1⟩, hxD'.2⟩
        set K : Finset (Fin 12) := C ∪ D with hKdef
        have hFAK : F = A ∪ K := by
          rw [hFsplit, hKdef, Finset.union_assoc]
        have hAsubF : A ⊆ F := by
          rw [hFAK]
          exact Finset.subset_union_left
        have hCsubF : C ⊆ F := by
          rw [hFsplit]
          exact fun x hx => Finset.mem_union_left D (Finset.mem_union_right A hx)
        have hDsubF : D ⊆ F := by
          rw [hFsplit]
          exact fun x hx => Finset.mem_union_right (A ∪ C) hx
        have hKsubF : K ⊆ F := by
          rw [hFAK]
          exact Finset.subset_union_right
        have hAadj : ∀ x ∈ A, G.Adj h x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hx
          exact (G.mem_neighborFinset h x).mp (Finset.mem_sdiff.mp hx').1
        have hCadj : ∀ x ∈ C, G.Adj t₁ x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hx
          exact (G.mem_neighborFinset t₁ x).mp (Finset.mem_sdiff.mp hx').1
        have hDadj : ∀ x ∈ D, G.Adj t₂ x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hx
          exact (G.mem_neighborFinset t₂ x).mp (Finset.mem_sdiff.mp hx').1
        have hKdeg : ∀ x ∈ K, 4 ≤ G.degree x := by
          intro x hx
          rw [hKdef, Finset.mem_union] at hx
          rcases hx with hxC | hxD
          · by_contra hnot
            have hdx : G.degree x = 3 := by have := h3 x; omega
            exact hs0 t₁ x hd1 hdx (hCadj x hxC)
          · by_contra hnot
            have hdx : G.degree x = 3 := by have := h3 x; omega
            exact hs0 t₂ x hd2 hdx (hDadj x hxD)
        have hKexc : K.card ≤ ∑ x ∈ K, (G.degree x - 3) := by
          calc
            K.card = ∑ _x ∈ K, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
            _ ≤ ∑ x ∈ K, (G.degree x - 3) :=
              Finset.sum_le_sum (fun x hx => by have := hKdeg x hx; omega)
        have hKexcF : ∑ x ∈ K, (G.degree x - 3) ≤
            ∑ x ∈ F, (G.degree x - 3) :=
          Finset.sum_le_sum_of_subset hKsubF
        have hKle3 : K.card ≤ 3 := by omega
        have hAKle := Finset.card_union_le A K
        have hFAKcard : F.card = (A ∪ K).card := congrArg Finset.card hFAK
        have hF5 : F.card = 5 := by omega
        have hB4 : S₂.card = 4 := by omega
        have hKcard : K.card = 3 := by omega
        have hdisjAK : Disjoint A K :=
          Finset.card_union_eq_card_add_card.mp (by rw [← hFAK, hF5, hAcard, hKcard])
        have hEFsplit : ∑ x ∈ F, (G.degree x - 3) =
            (∑ x ∈ A, (G.degree x - 3)) + ∑ x ∈ K, (G.degree x - 3) := by
          rw [hFAK, Finset.sum_union hdisjAK]
        have hEB0 : ∑ x ∈ S₂, (G.degree x - 3) = 0 := by omega
        have hEF3 : ∑ x ∈ F, (G.degree x - 3) = 3 := by omega
        have hAexc0 : ∑ x ∈ A, (G.degree x - 3) = 0 := by omega
        have hBdegree3 : ∀ b ∈ S₂, G.degree b = 3 := by
          intro b hb
          have hterm : G.degree b - 3 ≤ ∑ x ∈ S₂, (G.degree x - 3) :=
            Finset.single_le_sum (fun x _ => Nat.zero_le (G.degree x - 3)) hb
          have := h3 b
          omega
        obtain ⟨a₁, a₂, ha12, hAeq⟩ := Finset.card_eq_two.mp hAcard
        have ha1A : a₁ ∈ A := by rw [hAeq]; simp
        have ha1F := hAsubF ha1A
        have hAdegree3 : ∀ x ∈ A, G.degree x = 3 := by
          intro x hx
          have hterm : G.degree x - 3 ≤ ∑ y ∈ A, (G.degree y - 3) :=
            Finset.single_le_sum (fun y _ => Nat.zero_le (G.degree y - 3)) hx
          have := h3 x
          omega
        have hAOneS1 : ∀ x ∈ A, (G.neighborFinset x ∩ S₁).card = 1 := by
          intro x hxA
          have hdx := hAdegree3 x hxA
          have hsub : G.neighborFinset x ∩ S₁ ⊆ {h} := by
            intro y hy
            rw [Finset.mem_inter] at hy
            have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy.1
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hy
            rcases hy.2 with hyh | hyt1 | hyt2
            · simp [hyh]
            · exfalso
              exact hs0 x t₁ hdx hd1 (by simpa [hyt1] using hxy)
            · exfalso
              exact hs0 x t₂ hdx hd2 (by simpa [hyt2] using hxy)
          have hle : (G.neighborFinset x ∩ S₁).card ≤ 1 := by
            simpa using Finset.card_le_card hsub
          have hhmem : h ∈ G.neighborFinset x ∩ S₁ := by
            rw [Finset.mem_inter, G.mem_neighborFinset]
            exact ⟨(hAadj x hxA).symm, hhS1⟩
          have hpos := Finset.card_pos.mpr ⟨h, hhmem⟩
          omega
        have hANoB : ∀ x ∈ A, (G.neighborFinset x ∩ S₂).card = 0 := by
          intro x hxA
          rw [Finset.card_eq_zero]
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨b, hb⟩
          obtain ⟨hbN, hbS₂⟩ := Finset.mem_inter.mp hb
          exact hs0 x b (hAdegree3 x hxA) (hBdegree3 b hbS₂)
            ((G.mem_neighborFinset x b).mp hbN)
        have hdisjLayer : Disjoint (S₁ ∪ F) S₂ := by
          rw [Finset.disjoint_left]
          intro x hxSF hxB
          rw [hS2def, Finset.mem_compl] at hxB
          exact hxB hxSF
        have hcover : S₁ ∪ F ∪ S₂ = Finset.univ := by
          ext x
          simp only [Finset.mem_union, Finset.mem_univ, iff_true]
          by_cases hx1 : x ∈ S₁
          · exact Or.inl (Or.inl hx1)
          by_cases hxF : x ∈ F
          · exact Or.inl (Or.inr hxF)
          · exact Or.inr (by
              rw [hS2def, Finset.mem_compl, Finset.mem_union, not_or]
              exact ⟨hx1, hxF⟩)
        have hpartition : ∀ x ∈ F,
            (G.neighborFinset x ∩ S₁).card + (G.neighborFinset x ∩ F).card +
              (G.neighborFinset x ∩ S₂).card = G.degree x := by
          intro x hxF
          have hdisj12 : Disjoint (G.neighborFinset x ∩ S₁)
              (G.neighborFinset x ∩ F) :=
            hdisjS1F.mono Finset.inter_subset_right Finset.inter_subset_right
          have hdisj123 : Disjoint
              ((G.neighborFinset x ∩ S₁) ∪ (G.neighborFinset x ∩ F))
              (G.neighborFinset x ∩ S₂) := by
            apply hdisjLayer.mono _ Finset.inter_subset_right
            intro y hy
            rw [Finset.mem_union] at hy
            rcases hy with hy1 | hyF
            · exact Finset.mem_union_left F (Finset.mem_inter.mp hy1).2
            · exact Finset.mem_union_right S₁ (Finset.mem_inter.mp hyF).2
          have hunion : (G.neighborFinset x ∩ S₁) ∪ (G.neighborFinset x ∩ F) ∪
              (G.neighborFinset x ∩ S₂) = G.neighborFinset x := by
            rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left,
              hcover, Finset.inter_univ]
          rw [← Finset.card_union_of_disjoint hdisj12,
            ← Finset.card_union_of_disjoint hdisj123, hunion,
            G.card_neighborFinset_eq_degree]
        have ha1Int2 : (G.neighborFinset a₁ ∩ F).card = 2 := by
          have hp := hpartition a₁ ha1F
          have hone := hAOneS1 a₁ ha1A
          have hzero := hANoB a₁ ha1A
          have hdx := hAdegree3 a₁ ha1A
          omega
        have hPB0 : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card = 0 := by
          omega
        have hq12 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card = 12 := by
          omega
        have hhInc : 2 ≤ (G.neighborFinset h ∩ F).card := by
          calc
            2 = A.card := hAcard.symm
            _ ≤ (G.neighborFinset h ∩ F).card := Finset.card_le_card (by
              intro x hxA
              exact Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset h x).mpr (hAadj x hxA), hAsubF hxA⟩)
        have ht1Inc : 2 ≤ (G.neighborFinset t₁ ∩ F).card := by
          calc
            2 = C.card := hCcard.symm
            _ ≤ (G.neighborFinset t₁ ∩ F).card := Finset.card_le_card (by
              intro x hxC
              exact Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset t₁ x).mpr (hCadj x hxC), hCsubF hxC⟩)
        have ht2Inc : 2 ≤ (G.neighborFinset t₂ ∩ F).card := by
          calc
            2 = D.card := hDcard.symm
            _ ≤ (G.neighborFinset t₂ ∩ F).card := Finset.card_le_card (by
              intro x hxD
              exact Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset t₂ x).mpr (hDadj x hxD), hDsubF hxD⟩)
        have he1eq : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card = 6 := by
          apply Nat.le_antisymm he1
          rw [hcnt S₁ F, hS1def,
            Finset.sum_insert (by simp [hht1, hht2]),
            Finset.sum_insert (by simp [ht12]), Finset.sum_singleton]
          omega
        have hSF1 : ∑ x ∈ F, (G.neighborFinset x ∩ S₁).card = 6 := by
          rw [← hcnt F S₁, ← htrans S₁ F]
          exact he1eq
        have hSF2 : ∑ x ∈ F, (G.neighborFinset x ∩ S₂).card = 12 := by
          rw [← hcnt F S₂, ← htrans S₂ F]
          exact hq12
        have hdegF : ∑ x ∈ F, G.degree x = 18 := by
          have hre : ∑ x ∈ F, G.degree x =
              ∑ x ∈ F, ((G.degree x - 3) + 3) :=
            Finset.sum_congr rfl (fun x _ => by have := h3 x; omega)
          rw [hre, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            Nat.mul_comm, hEF3, hF5]
        have hPF0 : internalPairCount G F = 0 := by
          rw [internalPairCount_eq_sum]
          have hsumPart :
              (∑ x ∈ F, (G.neighborFinset x ∩ S₁).card) +
                (∑ x ∈ F, (G.neighborFinset x ∩ F).card) +
                ∑ x ∈ F, (G.neighborFinset x ∩ S₂).card =
                  ∑ x ∈ F, G.degree x := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl hpartition
          omega
        have htwice := twice_internal_degree_le_internalPairCount G F ha1F
        exfalso
        omega
      by_cases hn13 : n = 13
      · subst n
        have hpairle : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card
            ≤ 2 * ∑ v ∈ S₂, (G.degree v - 3) := by
          simpa [internalPairCount] using (not_lt.mp hlarge)
        have hEFEB : (∑ v ∈ F, (G.degree v - 3)) +
            (∑ v ∈ S₂, (G.degree v - 3)) = 4 := by
          omega
        have hF6 : F.card = 6 := by omega
        have hB4 : S₂.card = 4 := by omega
        set A : Finset (Fin 13) := G.neighborFinset h \ S₁ with hAdef
        set C : Finset (Fin 13) := G.neighborFinset t₁ \ S₁ with hCdef
        set D : Finset (Fin 13) := G.neighborFinset t₂ \ S₁ with hDdef
        have hhS1 : h ∈ S₁ := by rw [hS1def]; simp
        have ht1S1 : t₁ ∈ S₁ := by rw [hS1def]; simp
        have ht2S1 : t₂ ∈ S₁ := by rw [hS1def]; simp
        have hAle : A.card ≤ 2 := by simpa [hAdef] using hslice h hhS1
        have hCle : C.card ≤ 2 := by simpa [hCdef] using hslice t₁ ht1S1
        have hDle : D.card ≤ 2 := by simpa [hDdef] using hslice t₂ ht2S1
        have hFsplit : F = A ∪ C ∪ D := by
          ext x
          constructor
          · intro hxF
            rw [hFdef, Finset.mem_sdiff] at hxF
            obtain ⟨hxbi, hxnot⟩ := hxF
            rw [Finset.mem_biUnion] at hxbi
            obtain ⟨p, hp, hpx⟩ := hxbi
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hp
            rw [Finset.mem_union, Finset.mem_union]
            rcases hp with rfl | rfl | rfl
            · exact Or.inl (Or.inl (by
                rw [hAdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩))
            · exact Or.inl (Or.inr (by
                rw [hCdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩))
            · exact Or.inr (by
                rw [hDdef, Finset.mem_sdiff]
                exact ⟨hpx, hxnot⟩)
          · intro hx
            rw [Finset.mem_union, Finset.mem_union] at hx
            rw [hFdef, Finset.mem_sdiff]
            rcases hx with (hxA | hxC) | hxD
            · have hxA' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hxA
              rw [Finset.mem_sdiff] at hxA'
              exact ⟨Finset.mem_biUnion.mpr ⟨h, hhS1, hxA'.1⟩, hxA'.2⟩
            · have hxC' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hxC
              rw [Finset.mem_sdiff] at hxC'
              exact ⟨Finset.mem_biUnion.mpr ⟨t₁, ht1S1, hxC'.1⟩, hxC'.2⟩
            · have hxD' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hxD
              rw [Finset.mem_sdiff] at hxD'
              exact ⟨Finset.mem_biUnion.mpr ⟨t₂, ht2S1, hxD'.1⟩, hxD'.2⟩
        have htriplecard : (A ∪ C ∪ D).card = 6 := by rw [← hFsplit, hF6]
        have hACle := Finset.card_union_le A C
        have hACDle := Finset.card_union_le (A ∪ C) D
        have hAcard : A.card = 2 := by omega
        have hCcard : C.card = 2 := by omega
        have hDcard : D.card = 2 := by omega
        have hACcard : (A ∪ C).card = 4 := by omega
        have hdisjAC : Disjoint A C :=
          Finset.card_union_eq_card_add_card.mp (by omega)
        have hdisjACD : Disjoint (A ∪ C) D :=
          Finset.card_union_eq_card_add_card.mp (by omega)
        have hAsubF : A ⊆ F := by
          rw [hFsplit]
          exact fun x hx => Finset.mem_union_left D (Finset.mem_union_left C hx)
        have hCsubF : C ⊆ F := by
          rw [hFsplit]
          exact fun x hx => Finset.mem_union_left D (Finset.mem_union_right A hx)
        have hDsubF : D ⊆ F := by
          rw [hFsplit]
          exact fun x hx => Finset.mem_union_right (A ∪ C) hx
        have hAadj : ∀ x ∈ A, G.Adj h x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hx
          exact (G.mem_neighborFinset h x).mp (Finset.mem_sdiff.mp hx').1
        have hCadj : ∀ x ∈ C, G.Adj t₁ x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hx
          exact (G.mem_neighborFinset t₁ x).mp (Finset.mem_sdiff.mp hx').1
        have hDadj : ∀ x ∈ D, G.Adj t₂ x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hx
          exact (G.mem_neighborFinset t₂ x).mp (Finset.mem_sdiff.mp hx').1
        have hCdeg : ∀ x ∈ C, 4 ≤ G.degree x := by
          intro x hx
          by_contra hnot
          have hdx : G.degree x = 3 := by have := h3 x; omega
          exact hs0 t₁ x hd1 hdx (hCadj x hx)
        have hDdeg : ∀ x ∈ D, 4 ≤ G.degree x := by
          intro x hx
          by_contra hnot
          have hdx : G.degree x = 3 := by have := h3 x; omega
          exact hs0 t₂ x hd2 hdx (hDadj x hx)
        have hCexc : 2 ≤ ∑ x ∈ C, (G.degree x - 3) := by
          calc
            2 = ∑ _x ∈ C, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one, hCcard]
            _ ≤ ∑ x ∈ C, (G.degree x - 3) :=
              Finset.sum_le_sum (fun x hx => by have := hCdeg x hx; omega)
        have hDexc : 2 ≤ ∑ x ∈ D, (G.degree x - 3) := by
          calc
            2 = ∑ _x ∈ D, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one, hDcard]
            _ ≤ ∑ x ∈ D, (G.degree x - 3) :=
              Finset.sum_le_sum (fun x hx => by have := hDdeg x hx; omega)
        have hEFsplit : ∑ x ∈ F, (G.degree x - 3) =
            (∑ x ∈ A, (G.degree x - 3)) +
            (∑ x ∈ C, (G.degree x - 3)) +
            ∑ x ∈ D, (G.degree x - 3) := by
          rw [hFsplit, Finset.sum_union hdisjACD, Finset.sum_union hdisjAC]
        have hEB0 : ∑ x ∈ S₂, (G.degree x - 3) = 0 := by omega
        have hEF4 : ∑ x ∈ F, (G.degree x - 3) = 4 := by omega
        have hAexc0 : ∑ x ∈ A, (G.degree x - 3) = 0 := by omega
        have hBdegree3 : ∀ b ∈ S₂, G.degree b = 3 := by
          intro b hb
          have hterm : G.degree b - 3 ≤ ∑ x ∈ S₂, (G.degree x - 3) :=
            Finset.single_le_sum (fun x _ => Nat.zero_le (G.degree x - 3)) hb
          have := h3 b
          omega
        obtain ⟨a₁, a₂, ha12, hAeq⟩ := Finset.card_eq_two.mp hAcard
        have ha1A : a₁ ∈ A := by rw [hAeq]; simp
        have ha2A : a₂ ∈ A := by rw [hAeq]; simp
        have ha1F := hAsubF ha1A
        have ha2F := hAsubF ha2A
        have hAdegree3 : ∀ x ∈ A, G.degree x = 3 := by
          intro x hx
          have hterm : G.degree x - 3 ≤ ∑ y ∈ A, (G.degree y - 3) :=
            Finset.single_le_sum (fun y _ => Nat.zero_le (G.degree y - 3)) hx
          have := h3 x
          omega
        have hAOneS1 : ∀ x ∈ A, (G.neighborFinset x ∩ S₁).card = 1 := by
          intro x hxA
          have hdx := hAdegree3 x hxA
          have hsub : G.neighborFinset x ∩ S₁ ⊆ {h} := by
            intro y hy
            rw [Finset.mem_inter] at hy
            have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy.1
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hy
            rcases hy.2 with hyh | hyt1 | hyt2
            · simp [hyh]
            · exfalso
              exact hs0 x t₁ hdx hd1 (by simpa [hyt1] using hxy)
            · exfalso
              exact hs0 x t₂ hdx hd2 (by simpa [hyt2] using hxy)
          have hle : (G.neighborFinset x ∩ S₁).card ≤ 1 := by
            simpa using Finset.card_le_card hsub
          have hhmem : h ∈ G.neighborFinset x ∩ S₁ := by
            rw [Finset.mem_inter, G.mem_neighborFinset]
            exact ⟨(hAadj x hxA).symm, hhS1⟩
          have hpos := Finset.card_pos.mpr ⟨h, hhmem⟩
          omega
        have hANoB : ∀ x ∈ A, (G.neighborFinset x ∩ S₂).card = 0 := by
          intro x hxA
          rw [Finset.card_eq_zero]
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨b, hb⟩
          obtain ⟨hbN, hbS₂⟩ := Finset.mem_inter.mp hb
          exact hs0 x b (hAdegree3 x hxA) (hBdegree3 b hbS₂)
            ((G.mem_neighborFinset x b).mp hbN)
        have hdisjLayer : Disjoint (S₁ ∪ F) S₂ := by
          rw [Finset.disjoint_left]
          intro x hxSF hxB
          rw [hS2def, Finset.mem_compl] at hxB
          exact hxB hxSF
        have hcover : S₁ ∪ F ∪ S₂ = Finset.univ := by
          ext x
          simp only [Finset.mem_union, Finset.mem_univ, iff_true]
          by_cases hx1 : x ∈ S₁
          · exact Or.inl (Or.inl hx1)
          by_cases hxF : x ∈ F
          · exact Or.inl (Or.inr hxF)
          · exact Or.inr (by
              rw [hS2def, Finset.mem_compl, Finset.mem_union, not_or]
              exact ⟨hx1, hxF⟩)
        have hpartition : ∀ x ∈ F,
            (G.neighborFinset x ∩ S₁).card + (G.neighborFinset x ∩ F).card +
              (G.neighborFinset x ∩ S₂).card = G.degree x := by
          intro x hxF
          have hdisj12 : Disjoint (G.neighborFinset x ∩ S₁)
              (G.neighborFinset x ∩ F) :=
            hdisjS1F.mono Finset.inter_subset_right Finset.inter_subset_right
          have hdisj123 : Disjoint
              ((G.neighborFinset x ∩ S₁) ∪ (G.neighborFinset x ∩ F))
              (G.neighborFinset x ∩ S₂) := by
            apply hdisjLayer.mono _ Finset.inter_subset_right
            intro y hy
            rw [Finset.mem_union] at hy
            rcases hy with hy1 | hyF
            · exact Finset.mem_union_left F (Finset.mem_inter.mp hy1).2
            · exact Finset.mem_union_right S₁ (Finset.mem_inter.mp hyF).2
          have hunion : (G.neighborFinset x ∩ S₁) ∪ (G.neighborFinset x ∩ F) ∪
              (G.neighborFinset x ∩ S₂) = G.neighborFinset x := by
            rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left,
              hcover, Finset.inter_univ]
          rw [← Finset.card_union_of_disjoint hdisj12,
            ← Finset.card_union_of_disjoint hdisj123, hunion,
            G.card_neighborFinset_eq_degree]
        have hAInt2 : ∀ x ∈ A, (G.neighborFinset x ∩ F).card = 2 := by
          intro x hxA
          have hp := hpartition x (hAsubF hxA)
          have hone := hAOneS1 x hxA
          have hzero := hANoB x hxA
          have hdx := hAdegree3 x hxA
          omega
        have hPB0 : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card = 0 := by
          omega
        have hq12 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card = 12 := by
          omega
        have hhInc : 2 ≤ (G.neighborFinset h ∩ F).card := by
          calc
            2 = A.card := hAcard.symm
            _ ≤ (G.neighborFinset h ∩ F).card := Finset.card_le_card (by
              intro x hxA
              exact Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset h x).mpr (hAadj x hxA), hAsubF hxA⟩)
        have ht1Inc : 2 ≤ (G.neighborFinset t₁ ∩ F).card := by
          calc
            2 = C.card := hCcard.symm
            _ ≤ (G.neighborFinset t₁ ∩ F).card := Finset.card_le_card (by
              intro x hxC
              exact Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset t₁ x).mpr (hCadj x hxC), hCsubF hxC⟩)
        have ht2Inc : 2 ≤ (G.neighborFinset t₂ ∩ F).card := by
          calc
            2 = D.card := hDcard.symm
            _ ≤ (G.neighborFinset t₂ ∩ F).card := Finset.card_le_card (by
              intro x hxD
              exact Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset t₂ x).mpr (hDadj x hxD), hDsubF hxD⟩)
        have he1eq : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card = 6 := by
          apply Nat.le_antisymm he1
          rw [hcnt S₁ F, hS1def,
            Finset.sum_insert (by simp [hht1, hht2]),
            Finset.sum_insert (by simp [ht12]), Finset.sum_singleton]
          omega
        have hSF1 : ∑ x ∈ F, (G.neighborFinset x ∩ S₁).card = 6 := by
          rw [← hcnt F S₁, ← htrans S₁ F]
          exact he1eq
        have hSF2 : ∑ x ∈ F, (G.neighborFinset x ∩ S₂).card = 12 := by
          rw [← hcnt F S₂, ← htrans S₂ F]
          exact hq12
        have hdegF : ∑ x ∈ F, G.degree x = 22 := by
          have hre : ∑ x ∈ F, G.degree x =
              ∑ x ∈ F, ((G.degree x - 3) + 3) :=
            Finset.sum_congr rfl (fun x _ => by have := h3 x; omega)
          rw [hre, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            Nat.mul_comm, hEF4, hF6]
        have hPF4 : internalPairCount G F = 4 := by
          rw [internalPairCount_eq_sum]
          have hsumPart :
              (∑ x ∈ F, (G.neighborFinset x ∩ S₁).card) +
                (∑ x ∈ F, (G.neighborFinset x ∩ F).card) +
                ∑ x ∈ F, (G.neighborFinset x ∩ S₂).card =
                  ∑ x ∈ F, G.degree x := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl hpartition
          omega
        have ha1Int := hAInt2 a₁ ha1A
        have ha2Int := hAInt2 a₂ ha2A
        have ha2Le := internal_degree_le_one_of_pairCount_eq_twice_at
          G F ha1F ha2F ha12 (by rw [hPF4, ha1Int])
        exfalso
        omega
      by_cases hn14 : n = 14
      · subst n
        have hpairle : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card
            ≤ 2 * ∑ v ∈ S₂, (G.degree v - 3) := by
          simpa [internalPairCount] using (not_lt.mp hlarge)
        have hEFEB : (∑ v ∈ F, (G.degree v - 3)) +
            (∑ v ∈ S₂, (G.degree v - 3)) = 5 := by
          omega
        have hF6 : F.card = 6 := by omega
        have hB5 : S₂.card = 5 := by omega
        set A : Finset (Fin 14) := G.neighborFinset h \ S₁ with hAdef
        set C : Finset (Fin 14) := G.neighborFinset t₁ \ S₁ with hCdef
        set D : Finset (Fin 14) := G.neighborFinset t₂ \ S₁ with hDdef
        have hhS1 : h ∈ S₁ := by rw [hS1def]; simp
        have ht1S1 : t₁ ∈ S₁ := by rw [hS1def]; simp
        have ht2S1 : t₂ ∈ S₁ := by rw [hS1def]; simp
        have hAcard : A.card = 2 := by
          have hinterSub : G.neighborFinset h ∩ S₁ ⊆ S₁.erase h := by
            intro x hx
            rw [Finset.mem_inter] at hx
            rw [Finset.mem_erase]
            refine ⟨?_, hx.2⟩
            rintro rfl
            exact G.irrefl ((G.mem_neighborFinset _ _).mp hx.1)
          have hinterLe : (G.neighborFinset h ∩ S₁).card ≤ 2 := by
            calc
              (G.neighborFinset h ∩ S₁).card ≤ (S₁.erase h).card :=
                Finset.card_le_card hinterSub
              _ = 2 := by rw [Finset.card_erase_of_mem hhS1, hS1card]
          have hpart : (G.neighborFinset h ∩ S₁).card + A.card = G.degree h := by
            rw [hAdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
          have houtLe : A.card ≤ 2 := by simpa [hAdef] using hslice h hhS1
          omega
        have hCcard : C.card = 2 := by
          have hinterSub : G.neighborFinset t₁ ∩ S₁ ⊆ {h} := by
            intro x hx
            rw [Finset.mem_inter] at hx
            have hadj : G.Adj t₁ x := (G.mem_neighborFinset t₁ x).mp hx.1
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hx
            rcases hx.2 with hxh | hxt1 | hxt2
            · simp [hxh]
            · exfalso
              exact G.ne_of_adj hadj hxt1.symm
            · exfalso
              exact hs0 t₁ t₂ hd1 hd2 (by simpa [hxt2] using hadj)
          have hinterLe : (G.neighborFinset t₁ ∩ S₁).card ≤ 1 :=
            (Finset.card_le_card hinterSub).trans_eq (Finset.card_singleton h)
          have hpart : (G.neighborFinset t₁ ∩ S₁).card + C.card = G.degree t₁ := by
            rw [hCdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
          have houtLe : C.card ≤ 2 := by simpa [hCdef] using hslice t₁ ht1S1
          omega
        have hDcard : D.card = 2 := by
          have hinterSub : G.neighborFinset t₂ ∩ S₁ ⊆ {h} := by
            intro x hx
            rw [Finset.mem_inter] at hx
            have hadj : G.Adj t₂ x := (G.mem_neighborFinset t₂ x).mp hx.1
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hx
            rcases hx.2 with hxh | hxt1 | hxt2
            · simp [hxh]
            · exfalso
              exact hs0 t₂ t₁ hd2 hd1 (by simpa [hxt1] using hadj)
            · exfalso
              exact G.ne_of_adj hadj hxt2.symm
          have hinterLe : (G.neighborFinset t₂ ∩ S₁).card ≤ 1 :=
            (Finset.card_le_card hinterSub).trans_eq (Finset.card_singleton h)
          have hpart : (G.neighborFinset t₂ ∩ S₁).card + D.card = G.degree t₂ := by
            rw [hDdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
          have houtLe : D.card ≤ 2 := by simpa [hDdef] using hslice t₂ ht2S1
          omega
        have hFsplit : F = A ∪ C ∪ D := by
          ext x
          constructor
          · intro hxF
            rw [hFdef, Finset.mem_sdiff] at hxF
            obtain ⟨hxbi, hxnot⟩ := hxF
            rw [Finset.mem_biUnion] at hxbi
            obtain ⟨p, hp, hpx⟩ := hxbi
            rw [hS1def, Finset.mem_insert, Finset.mem_insert,
              Finset.mem_singleton] at hp
            rw [Finset.mem_union, Finset.mem_union]
            rcases hp with rfl | rfl | rfl
            · exact Or.inl (Or.inl (by rw [hAdef, Finset.mem_sdiff]; exact ⟨hpx, hxnot⟩))
            · exact Or.inl (Or.inr (by rw [hCdef, Finset.mem_sdiff]; exact ⟨hpx, hxnot⟩))
            · exact Or.inr (by rw [hDdef, Finset.mem_sdiff]; exact ⟨hpx, hxnot⟩)
          · intro hx
            rw [Finset.mem_union, Finset.mem_union] at hx
            rw [hFdef, Finset.mem_sdiff]
            rcases hx with (hxA | hxC) | hxD
            · have hxA' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hxA
              rw [Finset.mem_sdiff] at hxA'
              exact ⟨Finset.mem_biUnion.mpr ⟨h, hhS1, hxA'.1⟩, hxA'.2⟩
            · have hxC' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hxC
              rw [Finset.mem_sdiff] at hxC'
              exact ⟨Finset.mem_biUnion.mpr ⟨t₁, ht1S1, hxC'.1⟩, hxC'.2⟩
            · have hxD' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hxD
              rw [Finset.mem_sdiff] at hxD'
              exact ⟨Finset.mem_biUnion.mpr ⟨t₂, ht2S1, hxD'.1⟩, hxD'.2⟩
        have htriplecard : (A ∪ C ∪ D).card = 6 := by rw [← hFsplit, hF6]
        have hACcard : (A ∪ C).card = 4 := by
          have hACle := Finset.card_union_le A C
          have hACDle := Finset.card_union_le (A ∪ C) D
          omega
        have hdisjAC : Disjoint A C :=
          Finset.card_union_eq_card_add_card.mp (by omega)
        have hdisjACD : Disjoint (A ∪ C) D :=
          Finset.card_union_eq_card_add_card.mp (by omega)
        have hAsubF : A ⊆ F := by
          rw [hFsplit]
          exact fun x hx => Finset.mem_union_left D (Finset.mem_union_left C hx)
        have hCsubF : C ⊆ F := by
          rw [hFsplit]
          exact fun x hx => Finset.mem_union_left D (Finset.mem_union_right A hx)
        have hDsubF : D ⊆ F := by
          rw [hFsplit]
          exact fun x hx => Finset.mem_union_right (A ∪ C) hx
        have hCadj : ∀ x ∈ C, G.Adj t₁ x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hx
          exact (G.mem_neighborFinset t₁ x).mp (Finset.mem_sdiff.mp hx').1
        have hDadj : ∀ x ∈ D, G.Adj t₂ x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hx
          exact (G.mem_neighborFinset t₂ x).mp (Finset.mem_sdiff.mp hx').1
        have hCdeg : ∀ x ∈ C, 4 ≤ G.degree x := by
          intro x hx
          by_contra hnot
          have hdx : G.degree x = 3 := by have := h3 x; omega
          exact hs0 t₁ x hd1 hdx (hCadj x hx)
        have hDdeg : ∀ x ∈ D, 4 ≤ G.degree x := by
          intro x hx
          by_contra hnot
          have hdx : G.degree x = 3 := by have := h3 x; omega
          exact hs0 t₂ x hd2 hdx (hDadj x hx)
        have hCexc : 2 ≤ ∑ x ∈ C, (G.degree x - 3) := by
          calc
            2 = ∑ _x ∈ C, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one, hCcard]
            _ ≤ ∑ x ∈ C, (G.degree x - 3) :=
              Finset.sum_le_sum (fun x hx => by have := hCdeg x hx; omega)
        have hDexc : 2 ≤ ∑ x ∈ D, (G.degree x - 3) := by
          calc
            2 = ∑ _x ∈ D, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one, hDcard]
            _ ≤ ∑ x ∈ D, (G.degree x - 3) :=
              Finset.sum_le_sum (fun x hx => by have := hDdeg x hx; omega)
        have hEFsplit : ∑ x ∈ F, (G.degree x - 3) =
            (∑ x ∈ A, (G.degree x - 3)) +
            (∑ x ∈ C, (G.degree x - 3)) +
            ∑ x ∈ D, (G.degree x - 3) := by
          rw [hFsplit, Finset.sum_union hdisjACD, Finset.sum_union hdisjAC]
        have hEBle : (∑ v ∈ S₂, (G.degree v - 3)) ≤ 1 := by omega
        obtain ⟨a₁, a₂, ha12, hAeq⟩ := Finset.card_eq_two.mp hAcard
        have ha1A : a₁ ∈ A := by rw [hAeq]; simp
        have ha2A : a₂ ∈ A := by rw [hAeq]; simp
        have hAadj : ∀ x ∈ A, G.Adj h x := by
          intro x hx
          have hx' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hx
          exact (G.mem_neighborFinset h x).mp (Finset.mem_sdiff.mp hx').1
        have hmemA : ∀ x ∈ F, G.Adj h x → x ∈ A := by
          intro x hxF hx
          rw [hAdef, Finset.mem_sdiff]
          exact ⟨(G.mem_neighborFinset h x).mpr hx,
            Finset.disjoint_right.mp hdisjS1F hxF⟩
        have hmemC : ∀ x ∈ F, G.Adj t₁ x → x ∈ C := by
          intro x hxF hx
          rw [hCdef, Finset.mem_sdiff]
          exact ⟨(G.mem_neighborFinset t₁ x).mpr hx,
            Finset.disjoint_right.mp hdisjS1F hxF⟩
        have hmemD : ∀ x ∈ F, G.Adj t₂ x → x ∈ D := by
          intro x hxF hx
          rw [hDdef, Finset.mem_sdiff]
          exact ⟨(G.mem_neighborFinset t₂ x).mpr hx,
            Finset.disjoint_right.mp hdisjS1F hxF⟩
        have hdisjAD : Disjoint A D := by
          rw [Finset.disjoint_left]
          intro x hxA hxD
          exact Finset.disjoint_left.mp hdisjACD (Finset.mem_union_left C hxA) hxD
        have hdisjCD : Disjoint C D := by
          rw [Finset.disjoint_left]
          intro x hxC hxD
          exact Finset.disjoint_left.mp hdisjACD (Finset.mem_union_right A hxC) hxD
        have hOneS1 : ∀ x ∈ F, (G.neighborFinset x ∩ S₁).card = 1 := by
          intro x hxF
          have hgroups : x ∈ A ∨ x ∈ C ∨ x ∈ D := by
            have hx := hxF
            rw [hFsplit, Finset.mem_union, Finset.mem_union] at hx
            rcases hx with (hxA | hxC) | hxD
            · exact Or.inl hxA
            · exact Or.inr (Or.inl hxC)
            · exact Or.inr (Or.inr hxD)
          rcases hgroups with hxA | hxC | hxD
          · have hsub : G.neighborFinset x ∩ S₁ ⊆ {h} := by
              intro y hy
              rw [Finset.mem_inter] at hy
              have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy.1
              rw [hS1def, Finset.mem_insert, Finset.mem_insert,
                Finset.mem_singleton] at hy
              rcases hy.2 with hyh | hyt1 | hyt2
              · simp [hyh]
              · exfalso
                exact Finset.disjoint_left.mp hdisjAC hxA
                  (hmemC x hxF (by simpa [hyt1] using hxy.symm))
              · exfalso
                exact Finset.disjoint_left.mp hdisjAD hxA
                  (hmemD x hxF (by simpa [hyt2] using hxy.symm))
            have hle := Finset.card_le_card hsub
            have hhmem : h ∈ G.neighborFinset x ∩ S₁ := by
              rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨(G.adj_symm (hAadj x hxA)), hhS1⟩
            have hpos := Finset.card_pos.mpr ⟨h, hhmem⟩
            have hle1 : (G.neighborFinset x ∩ S₁).card ≤ 1 := by simpa using hle
            omega
          · have hsub : G.neighborFinset x ∩ S₁ ⊆ {t₁} := by
              intro y hy
              rw [Finset.mem_inter] at hy
              have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy.1
              rw [hS1def, Finset.mem_insert, Finset.mem_insert,
                Finset.mem_singleton] at hy
              rcases hy.2 with hyh | hyt1 | hyt2
              · exfalso
                exact Finset.disjoint_left.mp hdisjAC
                  (hmemA x hxF (by simpa [hyh] using hxy.symm)) hxC
              · simp [hyt1]
              · exfalso
                exact Finset.disjoint_left.mp hdisjCD hxC
                  (hmemD x hxF (by simpa [hyt2] using hxy.symm))
            have hle := Finset.card_le_card hsub
            have htmem : t₁ ∈ G.neighborFinset x ∩ S₁ := by
              rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨(G.adj_symm (hCadj x hxC)), ht1S1⟩
            have hpos := Finset.card_pos.mpr ⟨t₁, htmem⟩
            have hle1 : (G.neighborFinset x ∩ S₁).card ≤ 1 := by simpa using hle
            omega
          · have hsub : G.neighborFinset x ∩ S₁ ⊆ {t₂} := by
              intro y hy
              rw [Finset.mem_inter] at hy
              have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy.1
              rw [hS1def, Finset.mem_insert, Finset.mem_insert,
                Finset.mem_singleton] at hy
              rcases hy.2 with hyh | hyt1 | hyt2
              · exfalso
                exact Finset.disjoint_left.mp hdisjAD
                  (hmemA x hxF (by simpa [hyh] using hxy.symm)) hxD
              · exfalso
                exact Finset.disjoint_left.mp hdisjCD
                  (hmemC x hxF (by simpa [hyt1] using hxy.symm)) hxD
              · simp [hyt2]
            have hle := Finset.card_le_card hsub
            have htmem : t₂ ∈ G.neighborFinset x ∩ S₁ := by
              rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨(G.adj_symm (hDadj x hxD)), ht2S1⟩
            have hpos := Finset.card_pos.mpr ⟨t₂, htmem⟩
            have hle1 : (G.neighborFinset x ∩ S₁).card ≤ 1 := by simpa using hle
            omega
        have hdisjLayer : Disjoint (S₁ ∪ F) S₂ := by
          rw [Finset.disjoint_left]
          intro x hxSF hxB
          rw [hS2def, Finset.mem_compl] at hxB
          exact hxB hxSF
        have hcover : S₁ ∪ F ∪ S₂ = Finset.univ := by
          ext x
          simp only [Finset.mem_union, Finset.mem_univ, iff_true]
          by_cases hx1 : x ∈ S₁
          · exact Or.inl (Or.inl hx1)
          by_cases hxF : x ∈ F
          · exact Or.inl (Or.inr hxF)
          · exact Or.inr (by
              rw [hS2def, Finset.mem_compl, Finset.mem_union, not_or]
              exact ⟨hx1, hxF⟩)
        have hpartition : ∀ x ∈ F,
            (G.neighborFinset x ∩ S₁).card + (G.neighborFinset x ∩ F).card +
              (G.neighborFinset x ∩ S₂).card = G.degree x := by
          intro x hxF
          have hdisj12 : Disjoint (G.neighborFinset x ∩ S₁)
              (G.neighborFinset x ∩ F) :=
            hdisjS1F.mono Finset.inter_subset_right Finset.inter_subset_right
          have hdisj123 : Disjoint
              ((G.neighborFinset x ∩ S₁) ∪ (G.neighborFinset x ∩ F))
              (G.neighborFinset x ∩ S₂) := by
            apply hdisjLayer.mono _ Finset.inter_subset_right
            intro y hy
            rw [Finset.mem_union] at hy
            rcases hy with hy1 | hyF
            · exact Finset.mem_union_left F (Finset.mem_inter.mp hy1).2
            · exact Finset.mem_union_right S₁ (Finset.mem_inter.mp hyF).2
          have hunion : (G.neighborFinset x ∩ S₁) ∪ (G.neighborFinset x ∩ F) ∪
              (G.neighborFinset x ∩ S₂) = G.neighborFinset x := by
            rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left,
              hcover, Finset.inter_univ]
          rw [← Finset.card_union_of_disjoint hdisj12,
            ← Finset.card_union_of_disjoint hdisj123, hunion,
            G.card_neighborFinset_eq_degree]
        have hqsum : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card =
            ∑ x ∈ F, (G.neighborFinset x ∩ S₂).card := by
          rw [htrans S₂ F, hcnt F S₂]
        have hFledger : internalPairCount G F +
            ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card =
              ∑ x ∈ F, (G.degree x - 1) := by
          rw [internalPairCount_eq_sum, hqsum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun x hx => by
            have hp := hpartition x hx
            have hone := hOneS1 x hx
            omega)
        have hdegSum : ∑ x ∈ F, (G.degree x - 1) =
            (∑ x ∈ F, (G.degree x - 3)) + 2 * F.card := by
          calc
            ∑ x ∈ F, (G.degree x - 1) =
                ∑ x ∈ F, ((G.degree x - 3) + 2) :=
                  Finset.sum_congr rfl (fun x _ => by have := h3 x; omega)
            _ = (∑ x ∈ F, (G.degree x - 3)) + 2 * F.card := by
                  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        obtain ⟨kB, hkB⟩ := internalPairCount_eq_two_mul G S₂
        have hPBeven : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card = 2 * kB := by
          simpa [internalPairCount] using hkB
        set H : Finset (Fin 14) := S₂.filter (fun v => 4 ≤ G.degree v) with hHdef
        have hHsub : H ⊆ S₂ := by rw [hHdef]; exact Finset.filter_subset _ _
        have hHcard : H.card ≤ ∑ v ∈ S₂, (G.degree v - 3) := by
          calc
            H.card = ∑ _v ∈ H, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
            _ ≤ ∑ v ∈ H, (G.degree v - 3) := by
              refine Finset.sum_le_sum (fun v hv => ?_)
              have hv' : v ∈ S₂.filter (fun w => 4 ≤ G.degree w) := by
                simpa [hHdef] using hv
              have := (Finset.mem_filter.mp hv').2
              omega
            _ ≤ ∑ v ∈ S₂, (G.degree v - 3) :=
              Finset.sum_le_sum_of_subset hHsub
        have hdegree3High : ∀ x ∈ F, G.degree x = 3 →
            G.neighborFinset x ∩ S₂ ⊆ H := by
          intro x hxF hdx b hb
          rw [Finset.mem_inter] at hb
          have hadj : G.Adj x b := (G.mem_neighborFinset x b).mp hb.1
          have hdb4 : 4 ≤ G.degree b := by
            by_contra hnot
            have hdb : G.degree b = 3 := by have := h3 b; omega
            exact hs0 x b hdx hdb hadj
          rw [hHdef, Finset.mem_filter]
          exact ⟨hb.2, hdb4⟩
        let eF : ℕ := ∑ x ∈ F, (G.degree x - 3)
        let eB : ℕ := ∑ v ∈ S₂, (G.degree v - 3)
        let pB : ℕ := ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card
        let q : ℕ := ((S₂ ×ˢ F).filter (fun r => G.Adj r.1 r.2)).card
        let pF : ℕ := internalPairCount G F
        have harith1 : eF + eB = 5 := by simpa [eF, eB] using hEFEB
        have harith2 : eB ≤ 1 := by simpa [eB] using hEBle
        have harith3 : q + pB = 15 + eB := by
          simpa [q, pB, eB, hB5] using hbulk
        have harith4 : pB ≤ 2 * eB := by simpa [pB, eB] using hpairle
        have harith5 : pB = 2 * kB := by simpa [pB] using hPBeven
        have harith6 : pF + q = eF + 12 := by
          calc
            pF + q = ∑ x ∈ F, (G.degree x - 1) := by simpa [pF, q] using hFledger
            _ = eF + 12 := by rw [hdegSum, hF6]
        have profile_arithmetic : ∀ (ef eb pb qb pf k : ℕ),
            ef + eb = 5 → eb ≤ 1 → qb + pb = 15 + eb → pb ≤ 2 * eb →
            pb = 2 * k → pf + qb = ef + 12 →
            (eb = 0 ∧ pb = 0 ∧ qb = 15 ∧ pf = 2) ∨
            (eb = 1 ∧ pb = 0 ∧ qb = 16 ∧ pf = 0) ∨
            (eb = 1 ∧ pb = 2 ∧ qb = 14 ∧ pf = 2) := by
          intro ef eb pb qb pf k h1 h2 h3 h4 h5 h6
          omega
        have hprofiles :
            ((∑ v ∈ S₂, (G.degree v - 3)) = 0 ∧
              ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card = 0 ∧
              ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card = 15 ∧
              internalPairCount G F = 2) ∨
            ((∑ v ∈ S₂, (G.degree v - 3)) = 1 ∧
              ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card = 0 ∧
              ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card = 16 ∧
              internalPairCount G F = 0) ∨
            ((∑ v ∈ S₂, (G.degree v - 3)) = 1 ∧
              ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card = 2 ∧
              ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card = 14 ∧
              internalPairCount G F = 2) := by
          change (eB = 0 ∧ pB = 0 ∧ q = 15 ∧ pF = 2) ∨
            (eB = 1 ∧ pB = 0 ∧ q = 16 ∧ pF = 0) ∨
            (eB = 1 ∧ pB = 2 ∧ q = 14 ∧ pF = 2)
          exact profile_arithmetic eF eB pB q pF kB harith1 harith2 harith3 harith4
            harith5 harith6
        rcases hprofiles with hprof0 | hprof10 | hprof12
        · obtain ⟨hEB0, hPB0, hq15, hPF2⟩ := hprof0
          have hEF5 : ∑ x ∈ F, (G.degree x - 3) = 5 := by omega
          have hAexcLe : ∑ x ∈ A, (G.degree x - 3) ≤ 1 := by omega
          have hAexcPair : (G.degree a₁ - 3) + (G.degree a₂ - 3) =
              ∑ x ∈ A, (G.degree x - 3) := by
            rw [hAeq, Finset.sum_insert (by simpa using ha12), Finset.sum_singleton]
          obtain ⟨a, haA, hda⟩ : ∃ a ∈ A, G.degree a = 3 := by
            by_cases ha1deg : G.degree a₁ = 3
            · exact ⟨a₁, ha1A, ha1deg⟩
            by_cases ha2deg : G.degree a₂ = 3
            · exact ⟨a₂, ha2A, ha2deg⟩
            have ha1ge : 4 ≤ G.degree a₁ := by have := h3 a₁; omega
            have ha2ge : 4 ≤ G.degree a₂ := by have := h3 a₂; omega
            exfalso
            omega
          have haF : a ∈ F := hAsubF haA
          have hH0 : H.card = 0 :=
            Nat.eq_zero_of_le_zero (hHcard.trans_eq hEB0)
          have haB0 : (G.neighborFinset a ∩ S₂).card = 0 := by
            have hsub := hdegree3High a haF hda
            have hle := Finset.card_le_card hsub
            omega
          have haInt2 : (G.neighborFinset a ∩ F).card = 2 := by
            have hp := hpartition a haF
            have hone := hOneS1 a haF
            omega
          have htwice := twice_internal_degree_le_internalPairCount G F haF
          exfalso
          omega
        · obtain ⟨hEB1, hPB0, hq16, hPF0⟩ := hprof10
          have hEF4 : ∑ x ∈ F, (G.degree x - 3) = 4 := by omega
          have hAexc0 : ∑ x ∈ A, (G.degree x - 3) = 0 := by omega
          have ha1deg : G.degree a₁ = 3 := by
            have hterm : G.degree a₁ - 3 ≤ ∑ x ∈ A, (G.degree x - 3) :=
              Finset.single_le_sum (fun x _ => Nat.zero_le (G.degree x - 3)) ha1A
            have := h3 a₁
            omega
          have ha1F := hAsubF ha1A
          have ha1Int : (G.neighborFinset a₁ ∩ F).card = 0 := by
            rw [internalPairCount_eq_sum] at hPF0
            have hterm : (G.neighborFinset a₁ ∩ F).card ≤
                ∑ x ∈ F, (G.neighborFinset x ∩ F).card :=
              Finset.single_le_sum
                (f := fun x => (G.neighborFinset x ∩ F).card)
                (fun x _ => Nat.zero_le _) ha1F
            omega
          have ha1B : (G.neighborFinset a₁ ∩ S₂).card = 2 := by
            have hp := hpartition a₁ ha1F
            have hone := hOneS1 a₁ ha1F
            omega
          have hsub := hdegree3High a₁ ha1F ha1deg
          have htwoH : 2 ≤ H.card := by
            calc
              2 = (G.neighborFinset a₁ ∩ S₂).card := ha1B.symm
              _ ≤ H.card := Finset.card_le_card hsub
          exfalso
          omega
        · obtain ⟨hEB1, hPB2, hq14, hPF2⟩ := hprof12
          have hEF4 : ∑ x ∈ F, (G.degree x - 3) = 4 := by omega
          have hAexc0 : ∑ x ∈ A, (G.degree x - 3) = 0 := by omega
          have ha1deg : G.degree a₁ = 3 := by
            have hterm : G.degree a₁ - 3 ≤ ∑ x ∈ A, (G.degree x - 3) :=
              Finset.single_le_sum (fun x _ => Nat.zero_le (G.degree x - 3)) ha1A
            have := h3 a₁
            omega
          have ha2deg : G.degree a₂ = 3 := by
            have hterm : G.degree a₂ - 3 ≤ ∑ x ∈ A, (G.degree x - 3) :=
              Finset.single_le_sum (fun x _ => Nat.zero_le (G.degree x - 3)) ha2A
            have := h3 a₂
            omega
          have ha1F := hAsubF ha1A
          have ha2F := hAsubF ha2A
          have hHle : H.card ≤ 1 := hHcard.trans_eq hEB1
          have ha1BLe : (G.neighborFinset a₁ ∩ S₂).card ≤ 1 := by
            exact (Finset.card_le_card (hdegree3High a₁ ha1F ha1deg)).trans hHle
          have ha2BLe : (G.neighborFinset a₂ ∩ S₂).card ≤ 1 := by
            exact (Finset.card_le_card (hdegree3High a₂ ha2F ha2deg)).trans hHle
          have ha1IntPos : 0 < (G.neighborFinset a₁ ∩ F).card := by
            have hp := hpartition a₁ ha1F
            have hone := hOneS1 a₁ ha1F
            omega
          have ha2IntPos : 0 < (G.neighborFinset a₂ ∩ F).card := by
            have hp := hpartition a₂ ha2F
            have hone := hOneS1 a₂ ha2F
            omega
          have ha12adj : G.Adj a₁ a₂ :=
            adj_of_internalPairCount_eq_two G F ha1F ha2F ha12
              ha1IntPos ha2IntPos hPF2
          apply order14_sparse_triangle_fires G h a₁ a₂
          · exact hAadj a₁ ha1A
          · exact ha12adj
          · exact hAadj a₂ ha2A
          · rw [hdh, ha1deg, ha2deg]
      have hn15 : n = 15 := by
        by_contra hne
        have hn16 : 16 ≤ n := by omega
        apply hlarge
        rw [internalPairCount]
        omega
      subst n
      have hpairle : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card
          ≤ 2 * ∑ v ∈ S₂, (G.degree v - 3) := by
        simpa [internalPairCount] using (not_lt.mp hlarge)
      have hEFEB : (∑ v ∈ F, (G.degree v - 3)) +
          (∑ v ∈ S₂, (G.degree v - 3)) = 6 := by
        omega
      have hF6 : F.card = 6 := by
        omega
      have hB6 : S₂.card = 6 := by
        omega
      have hqeq : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card =
          18 - ∑ v ∈ S₂, (G.degree v - 3) := by
        omega
      have hPeq : ((S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2)).card =
          2 * ∑ v ∈ S₂, (G.degree v - 3) := by
        omega
      have hqsum : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card =
          ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card := by
        rw [htrans S₂ F, hcnt F S₂]
      have hdegSum : ∑ w ∈ F, (G.degree w - 1) =
          (∑ w ∈ F, (G.degree w - 3)) + 2 * F.card := by
        calc
          ∑ w ∈ F, (G.degree w - 1) =
              ∑ w ∈ F, ((G.degree w - 3) + 2) :=
                Finset.sum_congr rfl (fun w _ => by have := h3 w; omega)
          _ = (∑ w ∈ F, (G.degree w - 3)) + 2 * F.card := by
                rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      have hFsumEq : (∑ w ∈ F, (G.neighborFinset w ∩ S₂).card) =
          ∑ w ∈ F, (G.degree w - 1) := by
        omega
      have hFexact : ∀ w ∈ F,
          (G.neighborFinset w ∩ S₂).card = G.degree w - 1 := by
        intro w hw
        apply Nat.le_antisymm (hFbound w hw)
        by_contra hnot
        have hstrict : (G.neighborFinset w ∩ S₂).card < G.degree w - 1 := by omega
        have hsumlt : (∑ v ∈ F, (G.neighborFinset v ∩ S₂).card) <
            ∑ v ∈ F, (G.degree v - 1) :=
          Finset.sum_lt_sum (fun v hv => hFbound v hv) ⟨w, hw, hstrict⟩
        omega
      set A : Finset (Fin 15) := G.neighborFinset h \ S₁ with hAdef
      set C : Finset (Fin 15) := G.neighborFinset t₁ \ S₁ with hCdef
      set D : Finset (Fin 15) := G.neighborFinset t₂ \ S₁ with hDdef
      have hhS1 : h ∈ S₁ := by rw [hS1def]; simp
      have ht1S1 : t₁ ∈ S₁ := by rw [hS1def]; simp
      have ht2S1 : t₂ ∈ S₁ := by rw [hS1def]; simp
      have hAcard : A.card = 2 := by
        have hinterSub : G.neighborFinset h ∩ S₁ ⊆ S₁.erase h := by
          intro x hx
          rw [Finset.mem_inter] at hx
          rw [Finset.mem_erase]
          refine ⟨?_, hx.2⟩
          rintro rfl
          exact G.irrefl ((G.mem_neighborFinset _ _).mp hx.1)
        have hinterLe : (G.neighborFinset h ∩ S₁).card ≤ 2 := by
          calc
            (G.neighborFinset h ∩ S₁).card ≤ (S₁.erase h).card :=
              Finset.card_le_card hinterSub
            _ = 2 := by rw [Finset.card_erase_of_mem hhS1, hS1card]
        have hpart : (G.neighborFinset h ∩ S₁).card + A.card = G.degree h := by
          rw [hAdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
        have houtLe : A.card ≤ 2 := by simpa [hAdef] using hslice h hhS1
        omega
      have hCcard : C.card = 2 := by
        have hinterSub : G.neighborFinset t₁ ∩ S₁ ⊆ {h} := by
          intro x hx
          rw [Finset.mem_inter] at hx
          have hadj : G.Adj t₁ x := (G.mem_neighborFinset t₁ x).mp hx.1
          rw [hS1def, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx.2 with hxh | hxt1 | hxt2
          · simp [hxh]
          · exfalso
            exact G.ne_of_adj hadj hxt1.symm
          · exfalso
            exact hs0 t₁ t₂ hd1 hd2 (by simpa [hxt2] using hadj)
        have hinterLe : (G.neighborFinset t₁ ∩ S₁).card ≤ 1 :=
          (Finset.card_le_card hinterSub).trans_eq (Finset.card_singleton h)
        have hpart : (G.neighborFinset t₁ ∩ S₁).card + C.card = G.degree t₁ := by
          rw [hCdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
        have houtLe : C.card ≤ 2 := by simpa [hCdef] using hslice t₁ ht1S1
        omega
      have hDcard : D.card = 2 := by
        have hinterSub : G.neighborFinset t₂ ∩ S₁ ⊆ {h} := by
          intro x hx
          rw [Finset.mem_inter] at hx
          have hadj : G.Adj t₂ x := (G.mem_neighborFinset t₂ x).mp hx.1
          rw [hS1def, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx.2 with hxh | hxt1 | hxt2
          · simp [hxh]
          · exfalso
            exact hs0 t₂ t₁ hd2 hd1 (by simpa [hxt1] using hadj)
          · exfalso
            exact G.ne_of_adj hadj hxt2.symm
        have hinterLe : (G.neighborFinset t₂ ∩ S₁).card ≤ 1 :=
          (Finset.card_le_card hinterSub).trans_eq (Finset.card_singleton h)
        have hpart : (G.neighborFinset t₂ ∩ S₁).card + D.card = G.degree t₂ := by
          rw [hDdef, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
        have houtLe : D.card ≤ 2 := by simpa [hDdef] using hslice t₂ ht2S1
        omega
      have hFsplit : F = A ∪ C ∪ D := by
        ext x
        constructor
        · intro hxF
          rw [hFdef, Finset.mem_sdiff] at hxF
          obtain ⟨hxbi, hxnot⟩ := hxF
          rw [Finset.mem_biUnion] at hxbi
          obtain ⟨p, hp, hpx⟩ := hxbi
          rw [hS1def, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_singleton] at hp
          rw [Finset.mem_union, Finset.mem_union]
          rcases hp with rfl | rfl | rfl
          · exact Or.inl (Or.inl (by rw [hAdef, Finset.mem_sdiff]; exact ⟨hpx, hxnot⟩))
          · exact Or.inl (Or.inr (by rw [hCdef, Finset.mem_sdiff]; exact ⟨hpx, hxnot⟩))
          · exact Or.inr (by rw [hDdef, Finset.mem_sdiff]; exact ⟨hpx, hxnot⟩)
        · intro hx
          rw [Finset.mem_union, Finset.mem_union] at hx
          rw [hFdef, Finset.mem_sdiff]
          rcases hx with (hxA | hxC) | hxD
          · have hxA' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hxA
            rw [Finset.mem_sdiff] at hxA'
            exact ⟨Finset.mem_biUnion.mpr ⟨h, hhS1, hxA'.1⟩, hxA'.2⟩
          · have hxC' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hxC
            rw [Finset.mem_sdiff] at hxC'
            exact ⟨Finset.mem_biUnion.mpr ⟨t₁, ht1S1, hxC'.1⟩, hxC'.2⟩
          · have hxD' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hxD
            rw [Finset.mem_sdiff] at hxD'
            exact ⟨Finset.mem_biUnion.mpr ⟨t₂, ht2S1, hxD'.1⟩, hxD'.2⟩
      have htriplecard : (A ∪ C ∪ D).card = 6 := by rw [← hFsplit, hF6]
      have hACcard : (A ∪ C).card = 4 := by
        have hACle := Finset.card_union_le A C
        have hACDle := Finset.card_union_le (A ∪ C) D
        omega
      have hdisjAC : Disjoint A C :=
        Finset.card_union_eq_card_add_card.mp (by omega)
      have hdisjACD : Disjoint (A ∪ C) D :=
        Finset.card_union_eq_card_add_card.mp (by omega)
      obtain ⟨a₁, a₂, ha12, hAeq⟩ := Finset.card_eq_two.mp hAcard
      obtain ⟨c₁, c₂, hc12, hCeq⟩ := Finset.card_eq_two.mp hCcard
      obtain ⟨d₁, d₂, hd12, hDeq⟩ := Finset.card_eq_two.mp hDcard
      have hAsubF : A ⊆ F := by
        rw [hFsplit]
        exact fun x hx => Finset.mem_union_left D (Finset.mem_union_left C hx)
      have hCsubF : C ⊆ F := by
        rw [hFsplit]
        exact fun x hx => Finset.mem_union_left D (Finset.mem_union_right A hx)
      have hDsubF : D ⊆ F := by
        rw [hFsplit]
        exact fun x hx => Finset.mem_union_right (A ∪ C) hx
      have ha1A : a₁ ∈ A := by rw [hAeq]; simp
      have ha2A : a₂ ∈ A := by rw [hAeq]; simp
      have hc1C : c₁ ∈ C := by rw [hCeq]; simp
      have hc2C : c₂ ∈ C := by rw [hCeq]; simp
      have hd1D : d₁ ∈ D := by rw [hDeq]; simp
      have hd2D : d₂ ∈ D := by rw [hDeq]; simp
      have hAadj : ∀ x ∈ A, G.Adj h x := by
        intro x hx
        have hx' : x ∈ G.neighborFinset h \ S₁ := by simpa [hAdef] using hx
        exact (G.mem_neighborFinset h x).mp (Finset.mem_sdiff.mp hx').1
      have hCadj : ∀ x ∈ C, G.Adj t₁ x := by
        intro x hx
        have hx' : x ∈ G.neighborFinset t₁ \ S₁ := by simpa [hCdef] using hx
        exact (G.mem_neighborFinset t₁ x).mp (Finset.mem_sdiff.mp hx').1
      have hDadj : ∀ x ∈ D, G.Adj t₂ x := by
        intro x hx
        have hx' : x ∈ G.neighborFinset t₂ \ S₁ := by simpa [hDdef] using hx
        exact (G.mem_neighborFinset t₂ x).mp (Finset.mem_sdiff.mp hx').1
      have hCdeg : ∀ x ∈ C, 4 ≤ G.degree x := by
        intro x hx
        by_contra hnot
        have hdx : G.degree x = 3 := by have := h3 x; omega
        exact hs0 t₁ x hd1 hdx (hCadj x hx)
      have hDdeg : ∀ x ∈ D, 4 ≤ G.degree x := by
        intro x hx
        by_contra hnot
        have hdx : G.degree x = 3 := by have := h3 x; omega
        exact hs0 t₂ x hd2 hdx (hDadj x hx)
      have hCexc : 2 ≤ ∑ x ∈ C, (G.degree x - 3) := by
        calc
          2 = ∑ _x ∈ C, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one, hCcard]
          _ ≤ ∑ x ∈ C, (G.degree x - 3) := by
            exact Finset.sum_le_sum (fun x hx => by have := hCdeg x hx; omega)
      have hDexc : 2 ≤ ∑ x ∈ D, (G.degree x - 3) := by
        calc
          2 = ∑ _x ∈ D, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one, hDcard]
          _ ≤ ∑ x ∈ D, (G.degree x - 3) := by
            exact Finset.sum_le_sum (fun x hx => by have := hDdeg x hx; omega)
      have hEFsplit : ∑ x ∈ F, (G.degree x - 3) =
          (∑ x ∈ A, (G.degree x - 3)) +
          (∑ x ∈ C, (G.degree x - 3)) +
          ∑ x ∈ D, (G.degree x - 3) := by
        rw [hFsplit, Finset.sum_union hdisjACD, Finset.sum_union hdisjAC]
      set H : Finset (Fin 15) := S₂.filter (fun v => 4 ≤ G.degree v) with hHdef
      have hHsub : H ⊆ S₂ := by rw [hHdef]; exact Finset.filter_subset _ _
      have hHcard : H.card ≤ ∑ v ∈ S₂, (G.degree v - 3) := by
        calc
          H.card = ∑ _v ∈ H, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ v ∈ H, (G.degree v - 3) := by
            refine Finset.sum_le_sum (fun v hv => ?_)
            have hv4 : 4 ≤ G.degree v := by
              have hv' : v ∈ S₂.filter (fun w => 4 ≤ G.degree w) := by simpa [hHdef] using hv
              exact (Finset.mem_filter.mp hv').2
            omega
          _ ≤ ∑ v ∈ S₂, (G.degree v - 3) :=
            Finset.sum_le_sum_of_subset hHsub
      have hEBle : (∑ v ∈ S₂, (G.degree v - 3)) ≤ 2 := by
        omega
      have hdisjFS2 : Disjoint F S₂ := by
        rw [Finset.disjoint_left]
        intro x hxF hxB
        rw [hS2def, Finset.mem_compl] at hxB
        exact hxB (Finset.mem_union_right S₁ hxF)
      have hdegree3High : ∀ x ∈ F, G.degree x = 3 →
          G.neighborFinset x ∩ S₂ ⊆ H := by
        intro x hxF hdx b hb
        rw [Finset.mem_inter] at hb
        have hadj : G.Adj x b := (G.mem_neighborFinset x b).mp hb.1
        have hdb4 : 4 ≤ G.degree b := by
          by_contra hnot
          have hdb : G.degree b = 3 := by have := h3 b; omega
          exact hs0 x b hdx hdb hadj
        rw [hHdef, Finset.mem_filter]
        exact ⟨hb.2, hdb4⟩
      have hEBcases : (∑ v ∈ S₂, (G.degree v - 3)) = 2 ∨
          (∑ v ∈ S₂, (G.degree v - 3)) = 1 ∨
          (∑ v ∈ S₂, (G.degree v - 3)) = 0 := by
        omega
      rcases hEBcases with hEB2 | hEB1 | hEB0
      · have hEF4 : ∑ x ∈ F, (G.degree x - 3) = 4 := by omega
        have hAexc0 : ∑ x ∈ A, (G.degree x - 3) = 0 := by omega
        have hAdegree3 : ∀ x ∈ A, G.degree x = 3 := by
          intro x hxA
          have hterm : G.degree x - 3 ≤ ∑ y ∈ A, (G.degree y - 3) :=
            Finset.single_le_sum (fun y _ => Nat.zero_le (G.degree y - 3)) hxA
          have := h3 x
          omega
        have hANeq : ∀ x ∈ A, G.neighborFinset x ∩ S₂ = H := by
          intro x hxA
          have hxF := hAsubF hxA
          have hdx := hAdegree3 x hxA
          have hsub := hdegree3High x hxF hdx
          have hcard2 : (G.neighborFinset x ∩ S₂).card = 2 := by
            rw [hFexact x hxF, hdx]
          apply Finset.eq_of_subset_of_card_le hsub
          omega
        have hHcard2 : H.card = 2 := by
          have hsub := hdegree3High a₁ (hAsubF ha1A) (hAdegree3 a₁ ha1A)
          have hcard2 : (G.neighborFinset a₁ ∩ S₂).card = 2 := by
            rw [hFexact a₁ (hAsubF ha1A), hAdegree3 a₁ ha1A]
          have := Finset.card_le_card hsub
          omega
        have hHexc : ∑ b ∈ H, (G.degree b - 3) = 2 := by
          have hlower : H.card ≤ ∑ b ∈ H, (G.degree b - 3) := by
            calc
              H.card = ∑ _b ∈ H, 1 := by
                rw [Finset.sum_const, smul_eq_mul, mul_one]
              _ ≤ ∑ b ∈ H, (G.degree b - 3) := by
                refine Finset.sum_le_sum (fun b hb => ?_)
                have hb' : b ∈ S₂.filter (fun v => 4 ≤ G.degree v) := by
                  simpa [hHdef] using hb
                have := (Finset.mem_filter.mp hb').2
                omega
          have hupper : ∑ b ∈ H, (G.degree b - 3) ≤
              ∑ b ∈ S₂, (G.degree b - 3) :=
            Finset.sum_le_sum_of_subset hHsub
          omega
        obtain ⟨b₁, b₂, hb12, hHeq⟩ := Finset.card_eq_two.mp hHcard2
        have hb1H : b₁ ∈ H := by rw [hHeq]; simp
        have hb2H : b₂ ∈ H := by rw [hHeq]; simp
        have hb1ge : 4 ≤ G.degree b₁ := by
          have hb' : b₁ ∈ S₂.filter (fun v => 4 ≤ G.degree v) := by
            simpa [hHdef] using hb1H
          exact (Finset.mem_filter.mp hb').2
        have hb2ge : 4 ≤ G.degree b₂ := by
          have hb' : b₂ ∈ S₂.filter (fun v => 4 ≤ G.degree v) := by
            simpa [hHdef] using hb2H
          exact (Finset.mem_filter.mp hb').2
        have hHexcPair : (G.degree b₁ - 3) + (G.degree b₂ - 3) = 2 := by
          rw [hHeq, Finset.sum_insert (by simpa using hb12),
            Finset.sum_singleton] at hHexc
          exact hHexc
        have hb1deg : G.degree b₁ = 4 := by omega
        have hb2deg : G.degree b₂ = 4 := by omega
        have hHdegree4 : ∀ b ∈ H, G.degree b = 4 := by
          intro b hb
          rw [hHeq, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact hb1deg
          · exact hb2deg
        have hdisj_hA : Disjoint ({h} : Finset (Fin 15)) A :=
          hdisjS1F.mono (Finset.singleton_subset_iff.mpr hhS1) hAsubF
        have hdisj_hH : Disjoint ({h} : Finset (Fin 15)) H :=
          hdisj.mono (Finset.singleton_subset_iff.mpr hhS1) hHsub
        have hdisj_AH : Disjoint A H := hdisjFS2.mono hAsubF hHsub
        have hdisj_hA_H : Disjoint (({h} : Finset (Fin 15)) ∪ A) H := by
          rw [Finset.disjoint_left]
          intro x hx hxH
          rw [Finset.mem_union] at hx
          rcases hx with hxh | hxA
          · exact Finset.disjoint_left.mp hdisj_hH hxh hxH
          · exact Finset.disjoint_left.mp hdisj_AH hxA hxH
        set Q : Finset (Fin 15) := ({h} : Finset (Fin 15)) ∪ A ∪ H with hQdef
        have hQcard : Q.card = 5 := by
          rw [hQdef, Finset.card_union_of_disjoint hdisj_hA_H,
            Finset.card_union_of_disjoint hdisj_hA, Finset.card_singleton,
            hAcard, hHcard2]
        have hhQ : h ∈ Q := by rw [hQdef]; simp
        have hhout : (G.neighborFinset h \ Q).card ≤ 2 := by
          have hsub : A ⊆ G.neighborFinset h ∩ Q := by
            intro x hxA
            rw [Finset.mem_inter]
            exact ⟨(G.mem_neighborFinset h x).mpr (hAadj x hxA),
              by rw [hQdef]; exact Finset.mem_union_left H (Finset.mem_union_right {h} hxA)⟩
          have hout := neighbor_sdiff_card_add_le_degree G Q A h hsub
          omega
        have hAout : ∀ x ∈ A, (G.neighborFinset x \ Q).card = 0 := by
          intro x hxA
          have hKcard : (({h} : Finset (Fin 15)) ∪ H).card = 3 := by
            rw [Finset.card_union_of_disjoint hdisj_hH, Finset.card_singleton, hHcard2]
          have hsub : ({h} : Finset (Fin 15)) ∪ H ⊆ G.neighborFinset x ∩ Q := by
            intro y hy
            rw [Finset.mem_union] at hy
            rw [Finset.mem_inter]
            rcases hy with hyh | hyH
            · have hyEq : y = h := Finset.mem_singleton.mp hyh
              subst y
              exact ⟨(G.mem_neighborFinset x h).mpr (G.adj_symm (hAadj x hxA)), hhQ⟩
            · have hyN : y ∈ G.neighborFinset x ∩ S₂ := by
                rw [hANeq x hxA]
                exact hyH
              exact ⟨(Finset.mem_inter.mp hyN).1,
                by rw [hQdef]; exact Finset.mem_union_right ({h} ∪ A) hyH⟩
          have hout := neighbor_sdiff_card_add_le_degree G Q (({h} : Finset (Fin 15)) ∪ H)
            x hsub
          have hdx := hAdegree3 x hxA
          omega
        have hHout : ∀ b ∈ H, (G.neighborFinset b \ Q).card ≤ 2 := by
          intro b hbH
          have hsub : A ⊆ G.neighborFinset b ∩ Q := by
            intro x hxA
            have hbN : b ∈ G.neighborFinset x ∩ S₂ := by
              rw [hANeq x hxA]
              exact hbH
            rw [Finset.mem_inter]
            exact ⟨(G.mem_neighborFinset b x).mpr
                (G.adj_symm ((G.mem_neighborFinset x b).mp (Finset.mem_inter.mp hbN).1)),
              by rw [hQdef]; exact Finset.mem_union_left H (Finset.mem_union_right {h} hxA)⟩
          have hout := neighbor_sdiff_card_add_le_degree G Q A b hsub
          have hdb := hHdegree4 b hbH
          omega
        have hAsumOut : ∑ x ∈ A, (G.neighborFinset x \ Q).card = 0 := by
          exact Finset.sum_eq_zero (fun x hx => hAout x hx)
        have hHsumOut : ∑ b ∈ H, (G.neighborFinset b \ Q).card ≤ 4 := by
          calc
            ∑ b ∈ H, (G.neighborFinset b \ Q).card ≤ ∑ _b ∈ H, 2 :=
              Finset.sum_le_sum hHout
            _ = 4 := by rw [Finset.sum_const, smul_eq_mul, hHcard2]
        have hQsum : ∑ v ∈ Q, (G.neighborFinset v \ Q).card ≤ 6 := by
          have hsplit : ∑ v ∈ Q, (G.neighborFinset v \ Q).card =
              (G.neighborFinset h \ Q).card +
                (∑ x ∈ A, (G.neighborFinset x \ Q).card) +
                ∑ b ∈ H, (G.neighborFinset b \ Q).card := by
            rw [hQdef, Finset.sum_union hdisj_hA_H, Finset.sum_union hdisj_hA,
              Finset.sum_singleton]
          omega
        exact algConn_le_two_of_order15_cluster_sum G Q ⟨h, hhQ⟩ (Or.inl hQcard) (by omega)
      · have hAdeg : ∀ x ∈ A, 4 ≤ G.degree x := by
          intro x hxA
          by_contra hnot
          have hdx : G.degree x = 3 := by have := h3 x; omega
          have hxF : x ∈ F := hAsubF hxA
          have hslice2 : (G.neighborFinset x ∩ S₂).card = 2 := by
            rw [hFexact x hxF, hdx]
          have hsubH := hdegree3High x hxF hdx
          have htwoH : 2 ≤ H.card := by
            calc
              2 = (G.neighborFinset x ∩ S₂).card := hslice2.symm
              _ ≤ H.card := Finset.card_le_card hsubH
          omega
        have hAexc : 2 ≤ ∑ x ∈ A, (G.degree x - 3) := by
          calc
            2 = ∑ _x ∈ A, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one, hAcard]
            _ ≤ ∑ x ∈ A, (G.degree x - 3) := by
              exact Finset.sum_le_sum (fun x hx => by have := hAdeg x hx; omega)
        exfalso
        omega
      · have hEF6 : ∑ x ∈ F, (G.degree x - 3) = 6 := by
          calc
            ∑ x ∈ F, (G.degree x - 3) =
                (∑ x ∈ F, (G.degree x - 3)) + 0 := (Nat.add_zero _).symm
            _ = (∑ x ∈ F, (G.degree x - 3)) +
                ∑ x ∈ S₂, (G.degree x - 3) := by rw [hEB0]
            _ = 6 := hEFEB
        have hH0 : H.card = 0 :=
          Nat.eq_zero_of_le_zero (hHcard.trans_eq hEB0)
        have hFge4 : ∀ x ∈ F, 4 ≤ G.degree x := by
          intro x hxF
          by_contra hnot
          have hdx : G.degree x = 3 := by
            have hlt : G.degree x < 4 := Nat.lt_of_not_ge hnot
            have hle : G.degree x ≤ 3 := Nat.le_of_lt_succ hlt
            exact Nat.le_antisymm hle (h3 x)
          have hslice2 : (G.neighborFinset x ∩ S₂).card = 2 := by
            rw [hFexact x hxF, hdx]
          have hsub := hdegree3High x hxF hdx
          have := Finset.card_le_card hsub
          omega
        have hFdegree4 : ∀ x ∈ F, G.degree x = 4 := by
          intro x hxF
          by_contra hne
          have hstrict : 1 < G.degree x - 3 := by have := hFge4 x hxF; omega
          have hsumlt : (∑ _y ∈ F, 1) < ∑ y ∈ F, (G.degree y - 3) :=
            Finset.sum_lt_sum (fun y hy => by have := hFge4 y hy; omega) ⟨x, hxF, hstrict⟩
          have hones : ∑ _y ∈ F, 1 = 6 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one, hF6]
          omega
        have hBdegree3 : ∀ b ∈ S₂, G.degree b = 3 := by
          intro b hb
          have hterm : G.degree b - 3 ≤ ∑ y ∈ S₂, (G.degree y - 3) :=
            Finset.single_le_sum (fun y _ => Nat.zero_le (G.degree y - 3)) hb
          have := h3 b
          omega
        have hPempty : (S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2) = ∅ := by
          apply Finset.card_eq_zero.mp
          omega
        have hBindep : ∀ b ∈ S₂, ∀ c ∈ S₂, ¬G.Adj b c := by
          intro b hb c hc hbc
          have hp : (b, c) ∈ (S₂ ×ˢ S₂).filter (fun q => G.Adj q.1 q.2) := by
            rw [Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨hb, hc⟩, hbc⟩
          rw [hPempty] at hp
          simp at hp
        have hBneighborsF : ∀ b ∈ S₂, G.neighborFinset b ⊆ F := by
          intro b hb x hxN
          have hbx : G.Adj b x := (G.mem_neighborFinset b x).mp hxN
          by_cases hxB : x ∈ S₂
          · exact (hBindep b hb x hxB hbx).elim
          · rw [hS2def, Finset.mem_compl, not_not] at hxB
            rw [Finset.mem_union] at hxB
            rcases hxB with hxS1 | hxF
            · exact (hnc x hxS1 b hb (G.adj_symm hbx)).elim
            · exact hxF
        have hcol : ∀ b ∈ S₂,
            (if G.Adj a₁ b then 1 else 0) + (if G.Adj a₂ b then 1 else 0) +
              (if G.Adj c₁ b then 1 else 0) + (if G.Adj c₂ b then 1 else 0) +
              (if G.Adj d₁ b then 1 else 0) + (if G.Adj d₂ b then 1 else 0) = 3 := by
          intro b hb
          have hsumF : ∑ x ∈ F, (if G.Adj x b then 1 else 0) = 3 := by
            rw [← Finset.card_filter]
            have heq : F.filter (fun x => G.Adj x b) = G.neighborFinset b := by
              ext x
              simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
              constructor
              · rintro ⟨hxF, hxb⟩
                exact G.adj_symm hxb
              · intro hbx
                exact ⟨hBneighborsF b hb ((G.mem_neighborFinset b x).mpr hbx), G.adj_symm hbx⟩
            rw [heq, G.card_neighborFinset_eq_degree, hBdegree3 b hb]
          rw [hFsplit, Finset.sum_union hdisjACD, Finset.sum_union hdisjAC,
            hAeq, hCeq, hDeq,
            Finset.sum_insert (by simpa using ha12), Finset.sum_singleton,
            Finset.sum_insert (by simpa using hc12), Finset.sum_singleton,
            Finset.sum_insert (by simpa using hd12), Finset.sum_singleton] at hsumF
          omega
        have hrow : ∀ x ∈ F,
            (S₂.filter fun b => G.Adj x b).card = 3 := by
          intro x hxF
          have heq : S₂.filter (fun b => G.Adj x b) = G.neighborFinset x ∩ S₂ := by
            ext b
            simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
            exact and_comm
          rw [heq, hFexact x hxF, hFdegree4 x hxF]
        have hrepeat := six_binary_columns_force_repeated_pair S₂
          (fun b => G.Adj a₁ b) (fun b => G.Adj a₂ b)
          (fun b => G.Adj c₁ b) (fun b => G.Adj c₂ b)
          (fun b => G.Adj d₁ b) (fun b => G.Adj d₂ b)
          hB6 hcol (hrow a₁ (hAsubF ha1A)) (hrow a₂ (hAsubF ha2A))
        have hdisjLayer : Disjoint (S₁ ∪ F) S₂ := by
          rw [Finset.disjoint_left]
          intro x hxSF hxB
          rw [hS2def, Finset.mem_compl] at hxB
          exact hxB hxSF
        have fireSame : ∀ (p x y : Fin 15), p ∈ S₁ → x ∈ F → y ∈ F → x ≠ y →
            G.degree p ≤ 4 → G.Adj p x → G.Adj p y →
            2 ≤ (S₂.filter fun b => G.Adj x b ∧ G.Adj y b).card → algConn G ≤ 2 := by
          intro p x y hpS hxF hyF hxy hdp hpx hpy hrep
          have htwo : 1 < (S₂.filter fun b => G.Adj x b ∧ G.Adj y b).card := by omega
          obtain ⟨b₁, b₂, hb1, hb2, hb12⟩ := Finset.one_lt_card_iff.mp htwo
          have hb1' := Finset.mem_filter.mp hb1
          have hb2' := Finset.mem_filter.mp hb2
          set X : Finset (Fin 15) := {x, y} with hXdef
          set B : Finset (Fin 15) := {b₁, b₂} with hBdef
          have hXcard : X.card = 2 := by simp [hXdef, hxy]
          have hBcard : B.card = 2 := by simp [hBdef, hb12]
          have hXsub : X ⊆ F := by
            intro z hz
            rw [hXdef, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hxF
            · exact hyF
          have hBsub : B ⊆ S₂ := by
            intro z hz
            rw [hBdef, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hb1'.1
            · exact hb2'.1
          have hpX : Disjoint ({p} : Finset (Fin 15)) X :=
            hdisjS1F.mono (Finset.singleton_subset_iff.mpr hpS) hXsub
          have hpXB : Disjoint (({p} : Finset (Fin 15)) ∪ X) B := by
            apply hdisjLayer.mono _ hBsub
            intro z hz
            rw [Finset.mem_union] at hz
            rcases hz with hzp | hzX
            · have hzp' : z = p := Finset.mem_singleton.mp hzp
              subst z
              exact Finset.mem_union_left F hpS
            · exact Finset.mem_union_right S₁ (hXsub hzX)
          have hSfive : ({p, x, y, b₁, b₂} : Finset (Fin 15)).card = 5 := by
            have hcard : ((({p} : Finset (Fin 15)) ∪ X) ∪ B).card = 5 := by
              rw [Finset.card_union_of_disjoint hpXB, Finset.card_union_of_disjoint hpX,
                Finset.card_singleton, hXcard, hBcard]
            have heq : ({p, x, y, b₁, b₂} : Finset (Fin 15)) =
                (({p} : Finset (Fin 15)) ∪ X) ∪ B := by
              simp only [Finset.insert_eq, hXdef, hBdef, Finset.union_assoc]
            rw [heq]
            exact hcard
          have hpB : Disjoint ({p} : Finset (Fin 15)) B :=
            hdisj.mono (Finset.singleton_subset_iff.mpr hpS) hBsub
          have hpbb : ({p, b₁, b₂} : Finset (Fin 15)).card = 3 := by
            have hcard : (({p} : Finset (Fin 15)) ∪ B).card = 3 := by
              rw [Finset.card_union_of_disjoint hpB, Finset.card_singleton, hBcard]
            have heq : ({p, b₁, b₂} : Finset (Fin 15)) =
                ({p} : Finset (Fin 15)) ∪ B := by
              simp only [Finset.insert_eq, hBdef]
            rw [heq]
            exact hcard
          exact decorated_c4_same_parent_fires G p x y b₁ b₂ hSfive
            (by simpa [hXdef] using hXcard) hpbb hdp
            (by rw [hFdegree4 x hxF]) (by rw [hFdegree4 y hyF])
            (by rw [hBdegree3 b₁ hb1'.1]) (by rw [hBdegree3 b₂ hb2'.1])
            hpx hpy hb1'.2.1 hb2'.2.1 hb1'.2.2 hb2'.2.2
        have fireAdjacent : ∀ (p q x y : Fin 15), p ∈ S₁ → q ∈ S₁ →
            x ∈ F → y ∈ F → x ≠ y → G.degree p ≤ 4 → G.degree q ≤ 3 →
            G.Adj p q → G.Adj p x → G.Adj q y →
            2 ≤ (S₂.filter fun b => G.Adj x b ∧ G.Adj y b).card → algConn G ≤ 2 := by
          intro p q x y hpS hqS hxF hyF hxy hdp hdq hpq hpx hqy hrep
          have htwo : 1 < (S₂.filter fun b => G.Adj x b ∧ G.Adj y b).card := by omega
          obtain ⟨b₁, b₂, hb1, hb2, hb12⟩ := Finset.one_lt_card_iff.mp htwo
          have hb1' := Finset.mem_filter.mp hb1
          have hb2' := Finset.mem_filter.mp hb2
          set P : Finset (Fin 15) := {p, q} with hPdef
          set X : Finset (Fin 15) := {x, y} with hXdef
          set B : Finset (Fin 15) := {b₁, b₂} with hBdef
          have hPcard : P.card = 2 := by simp [hPdef, G.ne_of_adj hpq]
          have hXcard : X.card = 2 := by simp [hXdef, hxy]
          have hBcard : B.card = 2 := by simp [hBdef, hb12]
          have hPsub : P ⊆ S₁ := by
            intro z hz
            rw [hPdef, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hpS
            · exact hqS
          have hXsub : X ⊆ F := by
            intro z hz
            rw [hXdef, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hxF
            · exact hyF
          have hBsub : B ⊆ S₂ := by
            intro z hz
            rw [hBdef, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hb1'.1
            · exact hb2'.1
          have hPX : Disjoint P X := hdisjS1F.mono hPsub hXsub
          have hPXB : Disjoint (P ∪ X) B := by
            apply hdisjLayer.mono _ hBsub
            intro z hz
            rw [Finset.mem_union] at hz
            rcases hz with hzP | hzX
            · exact Finset.mem_union_left F (hPsub hzP)
            · exact Finset.mem_union_right S₁ (hXsub hzX)
          have hSsix : ({p, q, x, y, b₁, b₂} : Finset (Fin 15)).card = 6 := by
            have hcard : ((P ∪ X) ∪ B).card = 6 := by
              rw [Finset.card_union_of_disjoint hPXB, Finset.card_union_of_disjoint hPX,
                hPcard, hXcard, hBcard]
            have heq : ({p, q, x, y, b₁, b₂} : Finset (Fin 15)) =
                (P ∪ X) ∪ B := by
              simp only [Finset.insert_eq, hPdef, hXdef, hBdef, Finset.union_assoc]
            rw [heq]
            exact hcard
          have hqxDisj : Disjoint ({q} : Finset (Fin 15)) {x} :=
            hdisjS1F.mono (Finset.singleton_subset_iff.mpr hqS)
              (Finset.singleton_subset_iff.mpr hxF)
          have hpyDisj : Disjoint ({p} : Finset (Fin 15)) {y} :=
            hdisjS1F.mono (Finset.singleton_subset_iff.mpr hpS)
              (Finset.singleton_subset_iff.mpr hyF)
          have hqx : ({q, x} : Finset (Fin 15)).card = 2 := by
            rw [Finset.insert_eq, Finset.card_union_of_disjoint hqxDisj,
              Finset.card_singleton, Finset.card_singleton]
          have hpy : ({p, y} : Finset (Fin 15)).card = 2 := by
            rw [Finset.insert_eq, Finset.card_union_of_disjoint hpyDisj,
              Finset.card_singleton, Finset.card_singleton]
          have hpB : Disjoint ({p} : Finset (Fin 15)) B :=
            hdisj.mono (Finset.singleton_subset_iff.mpr hpS) hBsub
          have hqB : Disjoint ({q} : Finset (Fin 15)) B :=
            hdisj.mono (Finset.singleton_subset_iff.mpr hqS) hBsub
          have hpbb : ({p, b₁, b₂} : Finset (Fin 15)).card = 3 := by
            have hcard : (({p} : Finset (Fin 15)) ∪ B).card = 3 := by
              rw [Finset.card_union_of_disjoint hpB, Finset.card_singleton, hBcard]
            have heq : ({p, b₁, b₂} : Finset (Fin 15)) =
                ({p} : Finset (Fin 15)) ∪ B := by
              simp only [Finset.insert_eq, hBdef]
            rw [heq]
            exact hcard
          have hqbb : ({q, b₁, b₂} : Finset (Fin 15)).card = 3 := by
            have hcard : (({q} : Finset (Fin 15)) ∪ B).card = 3 := by
              rw [Finset.card_union_of_disjoint hqB, Finset.card_singleton, hBcard]
            have heq : ({q, b₁, b₂} : Finset (Fin 15)) =
                ({q} : Finset (Fin 15)) ∪ B := by
              simp only [Finset.insert_eq, hBdef]
            rw [heq]
            exact hcard
          exact decorated_c4_adjacent_parents_fires G p q x y b₁ b₂ hSsix hqx hpy hpbb
            hqbb (by simpa [hXdef] using hXcard) hdp hdq
            (by rw [hFdegree4 x hxF]) (by rw [hFdegree4 y hyF])
            (by rw [hBdegree3 b₁ hb1'.1]) (by rw [hBdegree3 b₂ hb2'.1])
            hpq hpx hqy hb1'.2.1 hb2'.2.1 hb1'.2.2 hb2'.2.2
        rcases hrepeat with hAA | hrepeat
        · exact fireSame h a₁ a₂ hhS1 (hAsubF ha1A) (hAsubF ha2A) ha12
            (by omega) (hAadj a₁ ha1A) (hAadj a₂ ha2A) hAA
        rcases hrepeat with hCC | hrepeat
        · exact fireSame t₁ c₁ c₂ ht1S1 (hCsubF hc1C) (hCsubF hc2C) hc12
            (by omega) (hCadj c₁ hc1C) (hCadj c₂ hc2C) hCC
        rcases hrepeat with hDD | hrepeat
        · exact fireSame t₂ d₁ d₂ ht2S1 (hDsubF hd1D) (hDsubF hd2D) hd12
            (by omega) (hDadj d₁ hd1D) (hDadj d₂ hd2D) hDD
        have hneAC : ∀ a ∈ A, ∀ c ∈ C, a ≠ c := by
          intro a ha c hc hac
          subst c
          exact Finset.disjoint_left.mp hdisjAC ha hc
        rcases hrepeat with hAC11 | hrepeat
        · exact fireAdjacent h t₁ a₁ c₁ hhS1 ht1S1 (hAsubF ha1A) (hCsubF hc1C)
            (hneAC a₁ ha1A c₁ hc1C) (by omega) (by omega) ht1
            (hAadj a₁ ha1A) (hCadj c₁ hc1C) hAC11
        rcases hrepeat with hAC12 | hrepeat
        · exact fireAdjacent h t₁ a₁ c₂ hhS1 ht1S1 (hAsubF ha1A) (hCsubF hc2C)
            (hneAC a₁ ha1A c₂ hc2C) (by omega) (by omega) ht1
            (hAadj a₁ ha1A) (hCadj c₂ hc2C) hAC12
        rcases hrepeat with hAC21 | hrepeat
        · exact fireAdjacent h t₁ a₂ c₁ hhS1 ht1S1 (hAsubF ha2A) (hCsubF hc1C)
            (hneAC a₂ ha2A c₁ hc1C) (by omega) (by omega) ht1
            (hAadj a₂ ha2A) (hCadj c₁ hc1C) hAC21
        rcases hrepeat with hAC22 | hrepeat
        · exact fireAdjacent h t₁ a₂ c₂ hhS1 ht1S1 (hAsubF ha2A) (hCsubF hc2C)
            (hneAC a₂ ha2A c₂ hc2C) (by omega) (by omega) ht1
            (hAadj a₂ ha2A) (hCadj c₂ hc2C) hAC22
        have hdisjAD : Disjoint A D := by
          rw [Finset.disjoint_left]
          intro x hxA hxD
          exact Finset.disjoint_left.mp hdisjACD (Finset.mem_union_left C hxA) hxD
        have hneAD : ∀ a ∈ A, ∀ d ∈ D, a ≠ d := by
          intro a ha d hd had
          subst d
          exact Finset.disjoint_left.mp hdisjAD ha hd
        rcases hrepeat with hAD11 | hrepeat
        · exact fireAdjacent h t₂ a₁ d₁ hhS1 ht2S1 (hAsubF ha1A) (hDsubF hd1D)
            (hneAD a₁ ha1A d₁ hd1D) (by omega) (by omega) ht2
            (hAadj a₁ ha1A) (hDadj d₁ hd1D) hAD11
        rcases hrepeat with hAD12 | hrepeat
        · exact fireAdjacent h t₂ a₁ d₂ hhS1 ht2S1 (hAsubF ha1A) (hDsubF hd2D)
            (hneAD a₁ ha1A d₂ hd2D) (by omega) (by omega) ht2
            (hAadj a₁ ha1A) (hDadj d₂ hd2D) hAD12
        rcases hrepeat with hAD21 | hAD22
        · exact fireAdjacent h t₂ a₂ d₁ hhS1 ht2S1 (hAsubF ha2A) (hDsubF hd1D)
            (hneAD a₂ ha2A d₁ hd1D) (by omega) (by omega) ht2
            (hAadj a₂ ha2A) (hDadj d₁ hd1D) hAD21
        · exact fireAdjacent h t₂ a₂ d₂ hhS1 ht2S1 (hAsubF ha2A) (hDsubF hd2D)
            (hneAD a₂ ha2A d₂ hd2D) (by omega) (by omega) ht2
            (hAadj a₂ ha2A) (hDadj d₂ hd2D) hAD22

/-- Compatibility form of the sharpened shared-hub theorem. -/
theorem z1_star_moat_fires_sharp {n : ℕ} [Nonempty (Fin n)] (hn : 10 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (h t₁ t₂ : Fin n) (hdh : G.degree h = 4) (ht1 : G.Adj h t₁) (ht2 : G.Adj h t₂)
    (hd1 : G.degree t₁ = 3) (hd2 : G.degree t₂ = 3) (ht12 : t₁ ≠ t₂) :
    algConn G ≤ 2 :=
  z1_star_moat_fires_core (by omega) G hm h3 hs0 h t₁ t₂ hdh ht1 ht2 hd1 hd2 ht12

end ACMax
