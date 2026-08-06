import ACMaxConjecture.Base
import ACMaxConjecture.Counting.CompactCell
import ACMaxConjecture.Counting.DoubleStar
import ACMaxConjecture.Counting.StarvedCensus
import ACMaxConjecture.Counting.SqrtGirth


/-!
# The tier-9 girth vocabulary of the starved census

The `V₉ = {v : deg v ≤ 4}` population (twins and sea together) and the census-free girth import
it feeds.  On the window boundary the deg-4-only sea has excess `O(1)`, but including the twins
turns the honest excess into `t₉ = n − 4 − X − 3h = Θ(n)` (`X = excessX`, `h = #heavies`), which
the SQRT girth bound consumes.

This module carries the vocabulary and the girth import only.  The kill itself is run twice
downstream, at two different moat thresholds:

* `Band/` runs it on the low band `64 ≤ n ≤ 122` against the kernel-`decide` side condition;
* `Counting.V9DischargeSharp` runs it import-free for every `n ≥ 123`, at the bulk-credited
  moat radius of `Counting.MoatSharp`.

The former `n ≥ 1100` dispatch that lived here (`starved_dead_ge_1100` and its `moore_strip_arith`
strip arithmetic) has been removed: `starved_dead_ge_123` subsumes it.

## Main results

* `v9_size_row`, `v9_density_row_quant` — the tight size row `n ≤ |V₉| + X` and the
  honest quantitative excess `v9Pairs ≥ 2|V₉| + 2·t₉`.
* `v9_short_cycle_fires`, `v9_girth` — the direct deg-`≤ 4` instance of
  `master_cycle_fires` (a `V₉`-cycle with `9k ≤ n + 8` fires), so a never-firing
  graph has no short `V₉`-cycle.
* `GirthExcessBound`, `girth_excess_bound_holds` — the census-free girth import and
  its unconditional proof, assembling the SQRT cluster with a component descent.
* `starved_v9_kill_of_import` — the rebased tier-9 kill, parametric in the girth import.
-/

namespace ACMax

open Finset
open scoped Classical

/-- **The honest tier-9 population `V₉`**: the degree-`≤ 4` vertices (the twins `deg 3` together
with the sea `deg 4`).  Its complement is exactly the heavies `{deg ≥ 5}`, so `V₉` is almost
everything and its internal excess is `Θ(n)`. -/
noncomputable def v9Set {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => G.degree v ≤ 4)

/-- Membership in the tier-9 population. -/
theorem mem_v9Set {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} :
    v ∈ v9Set G ↔ G.degree v ≤ 4 := by
  unfold v9Set; simp

open Classical in
/-- **Ordered adjacent pairs within `V₉`** (twice the number of internal tier-9 edges);
`2·|V₉| < v9Pairs G` is the density row "average tier-9 degree `> 2`". -/
noncomputable def v9Pairs {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ((v9Set G ×ˢ v9Set G).filter (fun q => G.Adj q.1 q.2)).card

/-- **The tier-9 size row.**  `n ≤ |V₉| + X` (`X = excessX n G`): `Fin n` partitions as
`V₉ ⊔ V₉ᶜ` with `V₉ᶜ ⊆ {deg ≥ 5}`, so `|V₉ᶜ| ≤ |heavies| ≤ X` (`heavy_le_excess`).  The twins
and sea are all inside `V₉`, so the size row is tight (`|V₉| ≥ n − X`, not `n − 8 − 2X`). -/
theorem v9_size_row {n : ℕ} (G : SimpleGraph (Fin n)) :
    n ≤ (v9Set G).card + excessX n G := by
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRcard : (v9Set G)ᶜ.card ≤ excessX n G :=
    le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hcardsum : (v9Set G).card + (v9Set G)ᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  omega

/-- **The tier-9 quantitative density row** (the honest `t₉ = Θ(n)`).  On a census graph
(`m = 2(n−2)`, `n ≥ 2`) the internal tier-9 pairs satisfy
`2|V₉| + 2n ≤ v9Pairs + 2X + 6h + 8` (`X = excessX n G`, `h = |V₉ᶜ|`), i.e.
`v9Pairs ≥ 2|V₉| + 2·t₉` with the honest excess `t₉ = n − 4 − X − 3h`.  The twins are inside
`V₉`, so the only leakage is to `V₉ᶜ ⊆ heavies`: the total-degree identity `∑ deg = 4n − 8`
(`residual_degree_sum`) and the bipartite `cross_count` give `v9Pairs ≥ 4n − 8 − 2∑_R deg`, and
`∑_R deg = ∑_R(deg − 4) + 4h ≤ X + 4h`. -/
theorem v9_density_row_quant {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) :
    2 * (v9Set G).card + 2 * n
      ≤ v9Pairs G + 2 * excessX n G + 6 * (v9Set G)ᶜ.card + 8 := by
  have hL : ∀ v : Fin n, (G.neighborFinset v ∩ v9Set G).card
      = ∑ w ∈ v9Set G, (if G.Adj v w then 1 else 0) := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
  have hSP : v9Pairs G = ∑ v ∈ v9Set G, (G.neighborFinset v ∩ v9Set G).card := by
    unfold v9Pairs
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun a _ => (hL a).symm)
  have hpartv : ∀ v ∈ v9Set G,
      (G.neighborFinset v ∩ v9Set G).card + (G.neighborFinset v \ v9Set G).card
        = G.degree v := by
    intro v _
    rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
  have hsumV : v9Pairs G + ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
      = ∑ v ∈ v9Set G, G.degree v := by
    rw [hSP, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpartv
  have hsdiff : ∀ v : Fin n, G.neighborFinset v \ v9Set G
      = G.neighborFinset v ∩ (v9Set G)ᶜ := by
    intro v; ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
  have hLeave : ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
      ≤ ∑ w ∈ (v9Set G)ᶜ, G.degree w := by
    calc ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
        = ∑ v ∈ v9Set G, (G.neighborFinset v ∩ (v9Set G)ᶜ).card :=
          Finset.sum_congr rfl (fun v _ => by rw [hsdiff v])
      _ = ∑ w ∈ (v9Set G)ᶜ, (G.neighborFinset w ∩ v9Set G).card :=
          cross_count G (v9Set G) (v9Set G)ᶜ
      _ ≤ ∑ w ∈ (v9Set G)ᶜ, G.degree w :=
          Finset.sum_le_sum (fun w _ => by
            rw [← G.card_neighborFinset_eq_degree]
            exact Finset.card_le_card Finset.inter_subset_left)
  have htot : ∑ v : Fin n, G.degree v = 4 * n - 8 := residual_degree_sum n hn G hm
  have hsplit : (∑ v ∈ v9Set G, G.degree v) + ∑ w ∈ (v9Set G)ᶜ, G.degree w
      = ∑ v : Fin n, G.degree v := Finset.sum_add_sum_compl (v9Set G) (fun v => G.degree v)
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRexc : ∑ w ∈ (v9Set G)ᶜ, (G.degree w - 4) ≤ excessX n G := by
    unfold excessX
    exact Finset.sum_le_sum_of_subset hRsub
  have hRdeg : ∑ w ∈ (v9Set G)ᶜ, G.degree w
      = (∑ w ∈ (v9Set G)ᶜ, (G.degree w - 4)) + 4 * (v9Set G)ᶜ.card := by
    have hpt : ∀ w ∈ (v9Set G)ᶜ, G.degree w = (G.degree w - 4) + 4 := by
      intro w hw
      rw [Finset.mem_compl, mem_v9Set] at hw
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcardsum : (v9Set G).card + (v9Set G)ᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  omega

/-- **N2 — the tier-9 cycle certificate.**  A census graph (`m = 2(n−2)`, `δ ≥ 3`) with an
injective cyclic map `c : ZMod k → Fin n` (`k ≥ 3`, `c i ~ c (i+1)`) of *degree-`≤ 4`* vertices
fires the two-cluster moat whenever `9k ≤ n + 8`.  The direct mixed deg-`3`/`4` instance of
`master_cycle_fires`: each `deg (c i) ≤ 4` gives the tie `Σ deg (c i) ≤ 4k`, and the threshold
`3·Σ(deg (c i) − 1) ≤ 3·(3k) = 9k ≤ n + 8`. -/
theorem v9_short_cycle_fires {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (c : ZMod k → Fin n)
    (hcinj : Function.Injective c) (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hdeg : ∀ i : ZMod k, G.degree (c i) ≤ 4) (hn : 9 * k ≤ n + 8) :
    algConn G ≤ 2 := by
  refine master_cycle_fires hk G hm h3 c hcinj hadj ?_ ?_
  · calc ∑ i : ZMod k, G.degree (c i)
        ≤ ∑ _i : ZMod k, 4 := Finset.sum_le_sum (fun i _ => hdeg i)
      _ = 4 * k := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
  · have hp : (∑ i : ZMod k, (G.degree (c i) - 1)) ≤ 3 * k := by
      calc ∑ i : ZMod k, (G.degree (c i) - 1)
          ≤ ∑ _i : ZMod k, 3 := Finset.sum_le_sum (fun i _ => by have := hdeg i; omega)
        _ = 3 * k := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
    omega

/-- **`v9_girth` — the tier-9 girth of the honest population.**  In a never-firing census
(`m = 2(n−2)`, `δ ≥ 3`, `hnf : ¬ algConn G ≤ 2`), the population `V₉` contains *no* cycle of
length `k` with `9k ≤ n + 8` (girth `> (n+8)/9` on `V₉`).  Any injective cyclic map into `V₉` of
such length fires `v9_short_cycle_fires`, contradicting `hnf`. -/
theorem v9_girth {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hk : 3 ≤ k) (hkn : 9 * k ≤ n + 8) (c : ZMod k → Fin n)
    (hcinj : Function.Injective c) (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hmem : ∀ i : ZMod k, c i ∈ v9Set G) : False :=
  hnf (v9_short_cycle_fires hk G hm h3 c hcinj hadj (fun i => mem_v9Set.mp (hmem i)) hkn)

/-- **N3 — the census-free girth import (SW5′).**  The single graph-generic girth surface that
replaces the falsified `AHLSeaTier9`/`AHLSeaTier18` bylines: quantified over an *arbitrary*
*nonempty* subset `S : Finset (Fin n)` and its excess `t` (no `seaSet`, no `excessX` — nothing
census; the `S.Nonempty` guard closes the vacuous `S = ∅, t = 0` slot where both side conditions
hold but no cycle can land), it says a subgraph on `S` with excess `2|S| + 2t ≤ pairs(S)`
(i.e. `e(S) ≥ |S| + t`) that also meets the
strength-specific Moore side condition — here the self-provable **SQRT** form
`2|S|² ≤ (L − 5)²·t` (§4.1: `girth ≤ |S|·√(2/t) + 5`) — contains a cycle of length `3 ≤ k ≤ L`
inside `S`.  Threaded as a hypothesis and discharged externally (SQRT self-proved covers
`n ≥ ~1071`; the tight band `55 ≤ n ≤ 476` needs the AHL strength, N8); never proved here. -/
def GirthExcessBound (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (S : Finset (Fin n)) (t L : ℕ), S.Nonempty → 6 ≤ L →
    2 * S.card + 2 * t ≤ ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card →
    2 * S.card ^ 2 ≤ (L - 5) ^ 2 * t →
    ∃ k : ℕ, 3 ≤ k ∧ k ≤ L ∧
      ∃ c : ZMod k → Fin n, Function.Injective c ∧
        (∀ i : ZMod k, G.Adj (c i) (c (i + 1))) ∧ (∀ i : ZMod k, c i ∈ S)

/-- **N4 — the rebased tier-9 kill.**  A never-firing starved census (`m = 2(n−2)`, `δ ≥ 3`) on
`55 ≤ n` with the honest *positivity* window `X + 3·|V₉ᶜ| + 4 ≤ n` (`hpos`; its only role is
`t₉ = n − 4 − X − 3h ≥ 0` and `V₉` nonempty — strictly weaker than the old density guard
`4X + 4 < n`, so the whole band (b) `n ≤ 4X + 4` now enters), given the census-free girth import
`hGEB`, cannot exist.  Assembly (mirrors `starved_tier_kill_of_AHL`, but on the honest `V₉` tier): the
size and density rows feed the honest excess `t₉ = n − 4 − X − 3h` and the strength-specific Moore
side condition `hMoore` to `hGEB` at `S = V₉`, producing a short `V₉`-cycle (`3 ≤ k ≤ L`,
`9L ≤ n + 8`) that `v9_girth` forbids.  `hMoore` is the discharge N9 (SQRT form shown, covering
`n ≥ ~1071`; the AHL strength reaches `55 ≤ n ≤ 476`), threaded not proved; `L` is the tier-9
length target `⌊(n+8)/9⌋`. -/
theorem starved_v9_kill_of_import {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hlo : 55 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 4 ≤ n)
    (L : ℕ) (hL6 : 6 ≤ L) (hLn : 9 * L ≤ n + 8)
    (hMoore : 2 * (v9Set G).card ^ 2
      ≤ (L - 5) ^ 2 * (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card))
    (hGEB : GirthExcessBound n G) : False := by
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
  obtain ⟨k, hk3, hkL, c, hcinj, hadj, hmem⟩ := hGEB (v9Set G) t9 L hne hL6 hexc hMoore
  have : NeZero k := ⟨by omega⟩
  exact v9_girth G hm h3 hnf hk3 (by omega) c hcinj hadj hmem

end ACMax



/-! ## The SQRT discharge of `GirthExcessBound`

Assembles the SQRT girth cluster into `girth_excess_bound_holds : ∀ n G,
GirthExcessBound n G`. The one new ingredient is the **component descent**: after
extracting a min-degree-2 core (`two_core_aux`), a mediant/pigeonhole selects a
component `C` on which `sqrt_double_count` gives `|C|·(1+2r) + 2·t_C·r² ≤ |C|²`,
colliding with the SQRT side condition to force a short cycle that lifts back to
`G`. `starved_v9_kill_sqrt` is the rebased kill with this import discharged. -/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*}

/-- **Induced degree equals the within-`S` degree.**  For `w ∈ S`, the degree of `w` in the induced
subgraph `G.induce ↑S` is exactly `degWithin G S w`. -/
theorem induce_degree_eq_degWithin [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (w : (↑S : Set V)) :
    (G.induce (↑S : Set V)).degree w = degWithin G S w.val := by
  rw [degWithin, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun (u : (↑S : Set V)) _ => (u : V)) ?_ ?_ ?_
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj] at hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_coe.mp u.2, hu⟩
  · intro u1 _ u2 _ heq
    exact Subtype.ext heq
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨⟨z, Finset.mem_coe.mpr hz.1⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
    exact hz.2

/-- **Component degree preservation.**  In a graph `H`, the degree of a vertex `u` in the induced
graph on its connected component's support equals its degree in `H`, since every neighbour of `u`
lies in the same component. -/
theorem degree_induce_supp_eq [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (C : H.ConnectedComponent) (u : (C.supp : Set V)) :
    (H.induce (C.supp : Set V)).degree u = H.degree u.val := by
  have hsub : H.neighborSet u.val ⊆ C.supp := fun w hw => C.mem_supp_of_adj_mem_supp u.2 hw
  exact SimpleGraph.degree_induce_of_neighborSet_subset hsub

/-- **Component size as a fibre.**  The number of vertices in a connected component `C` equals the
number of vertices mapping to `C` under `connectedComponentMk`. -/
theorem card_supp_eq_fiber [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent] (C : H.ConnectedComponent) :
    Fintype.card C.supp
      = (Finset.univ.filter (fun v => H.connectedComponentMk v = C)).card := by
  rw [← Set.toFinset_card]
  congr 1
  ext v
  simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    ConnectedComponent.mem_supp_iff]

/-- **Component degree sum.**  Summing `H.degree` over the vertices of a connected component `C`
equals twice the edge count of `C.toSimpleGraph`, via the component handshake and degree
preservation. -/
theorem sum_degree_component_eq [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableEq H.ConnectedComponent] (C : H.ConnectedComponent) :
    ∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v
      = 2 * (H.induce (C.supp : Set V)).edgeFinset.card := by
  have hstep : (∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v)
      = ∑ a : {v // v ∈ C.supp}, H.degree (a : V) := by
    apply Finset.sum_subtype
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ConnectedComponent.mem_supp_iff]
  rw [hstep, ← (H.induce (C.supp : Set V)).sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl (fun a _ => (degree_induce_supp_eq H C a).symm)

/-- **The mediant pigeonhole.**  Given nonneg fibre sizes `nc` and excesses `tc` over a nonempty
finite index with total size `N` and total excess `≥ t`, some index `C` satisfies
`nc C² · t ≤ N² · tc C`.  Otherwise summing the strict reverse inequalities collides with
`∑ nc² ≤ (∑ nc)² = N²`. -/
theorem exists_mediant_component {κ : Type*} [Fintype κ] (nc tc : κ → ℕ) {N t : ℕ}
    (hne : (Finset.univ : Finset κ).Nonempty) (hN : ∑ C : κ, nc C = N)
    (ht : t ≤ ∑ C : κ, tc C) :
    ∃ C : κ, nc C ^ 2 * t ≤ N ^ 2 * tc C := by
  by_contra hcon
  push Not at hcon
  have hsq : ∑ C : κ, nc C ^ 2 ≤ N ^ 2 := by
    have h1 : ∑ C : κ, nc C ^ 2 ≤ ∑ C : κ, nc C * N := by
      apply Finset.sum_le_sum
      intro C _
      have hle : nc C ≤ N := by
        rw [← hN]
        exact Finset.single_le_sum (fun D _ => Nat.zero_le _) (Finset.mem_univ C)
      calc nc C ^ 2 = nc C * nc C := pow_two (nc C)
        _ ≤ nc C * N := by gcongr
    calc ∑ C : κ, nc C ^ 2 ≤ ∑ C : κ, nc C * N := h1
      _ = (∑ C : κ, nc C) * N := by rw [Finset.sum_mul]
      _ = N * N := by rw [hN]
      _ = N ^ 2 := (pow_two N).symm
  have hsum : N ^ 2 * ∑ C : κ, tc C < t * ∑ C : κ, nc C ^ 2 := by
    have hlt : ∑ C : κ, N ^ 2 * tc C < ∑ C : κ, nc C ^ 2 * t :=
      Finset.sum_lt_sum_of_nonempty hne (fun C _ => hcon C)
    calc N ^ 2 * ∑ C : κ, tc C = ∑ C : κ, N ^ 2 * tc C := by rw [Finset.mul_sum]
      _ < ∑ C : κ, nc C ^ 2 * t := hlt
      _ = t * ∑ C : κ, nc C ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun C _ => by ring)
  have hbad : N ^ 2 * t < N ^ 2 * t := by
    calc N ^ 2 * t ≤ N ^ 2 * ∑ C : κ, tc C := by gcongr
      _ < t * ∑ C : κ, nc C ^ 2 := hsum
      _ ≤ t * N ^ 2 := by gcongr
      _ = N ^ 2 * t := by ring
  exact absurd hbad (lt_irrefl _)

/-- **The SQRT discharge.**  `GirthExcessBound` holds for every `n` and `G`.  Given a nonempty `S`
with `2|S| + 2t ≤ pairs(S)` (edge excess `t`) and the SQRT side condition `2|S|² ≤ (L−5)²·t` with
`6 ≤ L`, there is a cycle of length `3 ≤ k ≤ L` inside `S`.  Assembly: extract the min-degree-`2`
`2`-core (`two_core_aux`), pick the excess-carrying component (`exists_mediant_component`), collide
`sqrt_double_count` with the side condition (`r = ⌊(L−1)/2⌋`), and lift the resulting short cycle
through the two induced-graph embeddings to `G` via `cycle_walk_to_zmod`. -/
theorem girth_excess_bound_holds (n : ℕ) (G : SimpleGraph (Fin n)) : GirthExcessBound n G := by
  classical
  intro S t L hSne hL6 hpairs hside
  have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  -- The side condition forces a positive excess.
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · exfalso
      have hz : 2 * S.card ^ 2 ≤ 0 := by simpa using hside
      have hpos : 0 < S.card ^ 2 := pow_pos hScard1 2
      omega
    · exact h
  -- Rewrite the pair count as the within-`S` degree sum, then extract the `2`-core.
  have hpairs' : 2 * S.card + 2 * t ≤ edgeSumWithin G S := by
    rw [edgeSumWithin_eq_pairs]; exact hpairs
  obtain ⟨S', hS'sub, hS'ne, hS'min, hS'inv⟩ := two_core_aux G ht1 S hpairs'
  set H : SimpleGraph (↥(↑S' : Set (Fin n))) := G.induce (↑S' : Set (Fin n)) with hHdef
  have : Nonempty (↥(↑S' : Set (Fin n))) := (Finset.coe_nonempty.mpr hS'ne).to_subtype
  have : DecidableEq H.ConnectedComponent := Classical.decEq _
  have hcardV' : Fintype.card (↥(↑S' : Set (Fin n))) = S'.card := by
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  set NN : ℕ := Fintype.card (↥(↑S' : Set (Fin n))) with hNNdef
  have hHexc : NN + t ≤ H.edgeFinset.card := by
    have hDS : edgeSumWithin G S' = 2 * H.edgeFinset.card := by
      rw [edgeSumWithin_eq_pairs]; exact induced_pairs_eq_two_mul_edges G S'
    rw [hcardV']; omega
  have hHmin : ∀ w : ↥(↑S' : Set (Fin n)), 2 ≤ H.degree w := by
    intro w
    have hh : H.degree w = degWithin G S' w.val := induce_degree_eq_degWithin G S' w
    rw [hh]
    exact hS'min w.val (Finset.mem_coe.mp w.2)
  -- Component partition data.
  have hnc_le_ec : ∀ C : H.ConnectedComponent,
      Fintype.card C.supp ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by
    intro C
    have hkey := sum_degree_component_eq H C
    have hconst : ∑ _v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), (2 : ℕ)
        = 2 * Fintype.card C.supp := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm, card_supp_eq_fiber H C]
    have hge : 2 * Fintype.card C.supp
        ≤ ∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v := by
      rw [← hconst]
      exact Finset.sum_le_sum (fun v _ => hHmin v)
    rw [hkey] at hge
    omega
  have hcard_sum : ∑ C : H.ConnectedComponent, Fintype.card C.supp = NN := by
    have hfw := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (↥(↑S' : Set (Fin n)))))
      (t := (Finset.univ : Finset H.ConnectedComponent))
      (f := H.connectedComponentMk) (fun v _ => Finset.mem_univ _)
    simp only [Finset.card_univ] at hfw
    rw [hNNdef, hfw]
    exact Finset.sum_congr rfl (fun C _ => card_supp_eq_fiber H C)
  have hedge_part : ∑ C : H.ConnectedComponent,
      (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card = H.edgeFinset.card := by
    have hfib := Finset.sum_fiberwise (Finset.univ : Finset (↥(↑S' : Set (Fin n))))
      H.connectedComponentMk (fun v => H.degree v)
    have hhand := H.sum_degrees_eq_twice_card_edges
    have h2 : ∑ C : H.ConnectedComponent,
          2 * (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card
        = 2 * H.edgeFinset.card := by
      rw [← hhand, ← hfib]
      exact Finset.sum_congr rfl (fun C _ => (sum_degree_component_eq H C).symm)
    rw [← Finset.mul_sum] at h2
    omega
  have htc_sum : t ≤ ∑ C : H.ConnectedComponent,
      ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp) := by
    have hsplit : (∑ C : H.ConnectedComponent,
          ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp))
          + ∑ C : H.ConnectedComponent, Fintype.card C.supp
        = ∑ C : H.ConnectedComponent,
          (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun C _ => Nat.sub_add_cancel (hnc_le_ec C))
    rw [hcard_sum, hedge_part] at hsplit
    omega
  have hne : (Finset.univ : Finset H.ConnectedComponent).Nonempty := Finset.univ_nonempty
  -- Select the excess-carrying component via the mediant.
  obtain ⟨C, hmed⟩ := exists_mediant_component
    (fun C : H.ConnectedComponent => Fintype.card C.supp)
    (fun C : H.ConnectedComponent =>
      (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp)
    hne hcard_sum htc_sum
  have hmed2 : Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n)))) ^ 2 * t
      ≤ NN ^ 2 * ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card
        - Fintype.card C.supp) := hmed
  have : Nonempty (C.supp : Set (↥(↑S' : Set (Fin n)))) :=
    (SimpleGraph.ConnectedComponent.nonempty_supp C).to_subtype
  -- Set `r = ⌊(L−1)/2⌋`, so `2r + 1 ≤ L` and `L − 2 ≤ 2r`.
  set r := (L - 1) / 2 with hrdef
  have hr2L : 2 * r + 1 ≤ L := by omega
  have hrL2 : L - 2 ≤ 2 * r := by omega
  -- No cycle of length `≤ 2r+1` collides with the SQRT side condition, so a short cycle exists.
  have hcyc : ∃ (u : (C.supp : Set (↥(↑S' : Set (Fin n)))))
      (w : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Walk u u),
      w.IsCycle ∧ w.length ≤ 2 * r + 1 := by
    by_contra hcon
    push Not at hcon
    have hg : ∀ (u : (C.supp : Set (↥(↑S' : Set (Fin n)))))
        (w : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Walk u u),
        w.IsCycle → 2 * r + 1 < w.length := fun u w hw => hcon u w hw
    have hmin_C : ∀ u : (C.supp : Set (↥(↑S' : Set (Fin n)))),
        2 ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).degree u := by
      intro u
      rw [degree_induce_supp_eq H C u]
      exact hHmin u.val
    have hconn_C : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Connected :=
      SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
    have hle := hnc_le_ec C
    have hexc_C : Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n))))
        + ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp)
        ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by omega
    have hsqrt := sqrt_double_count (H.induce (C.supp : Set (↥(↑S' : Set (Fin n)))))
      hmin_C hg hconn_C hexc_C
    -- Abbreviations for the arithmetic collision.
    set nc := Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n)))) with hncval
    set ec := (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card with hecval
    have hncpos : 0 < nc := Fintype.card_pos
    have hsqrt2 : 2 * (ec - nc) * r ^ 2 ≤ nc ^ 2 := le_trans (Nat.le_add_left _ _) hsqrt
    have key1 : 2 * r ^ 2 * (nc ^ 2 * t) ≤ NN ^ 2 * nc ^ 2 := by
      calc 2 * r ^ 2 * (nc ^ 2 * t) ≤ 2 * r ^ 2 * (NN ^ 2 * (ec - nc)) :=
              Nat.mul_le_mul (le_refl (2 * r ^ 2)) hmed2
        _ = NN ^ 2 * (2 * (ec - nc) * r ^ 2) := by ring
        _ ≤ NN ^ 2 * nc ^ 2 := Nat.mul_le_mul (le_refl (NN ^ 2)) hsqrt2
    have key2 : 2 * r ^ 2 * t ≤ NN ^ 2 := by
      have hmul : (2 * r ^ 2 * t) * nc ^ 2 ≤ NN ^ 2 * nc ^ 2 := by
        calc (2 * r ^ 2 * t) * nc ^ 2 = 2 * r ^ 2 * (nc ^ 2 * t) := by ring
          _ ≤ NN ^ 2 * nc ^ 2 := key1
      exact Nat.le_of_mul_le_mul_right hmul (pow_pos hncpos 2)
    have hNleS : NN ≤ S.card := by
      rw [hcardV']; exact Finset.card_le_card hS'sub
    have hfinal : (4 * r ^ 2) * t ≤ (L - 5) ^ 2 * t := by
      calc (4 * r ^ 2) * t = 2 * (2 * r ^ 2 * t) := by ring
        _ ≤ 2 * NN ^ 2 := by gcongr
        _ ≤ 2 * S.card ^ 2 := by gcongr
        _ ≤ (L - 5) ^ 2 * t := hside
    have hfinal2 : 4 * r ^ 2 ≤ (L - 5) ^ 2 := Nat.le_of_mul_le_mul_right hfinal ht1
    have hsq_le : (L - 2) ^ 2 ≤ 4 * r ^ 2 := by
      calc (L - 2) ^ 2 ≤ (2 * r) ^ 2 := Nat.pow_le_pow_left hrL2 2
        _ = 4 * r ^ 2 := by ring
    have hcollide : (L - 2) ^ 2 ≤ (L - 5) ^ 2 := le_trans hsq_le hfinal2
    have ha : 1 ≤ L - 5 := by omega
    have hexpand : L - 2 = (L - 5) + 3 := by omega
    rw [hexpand] at hcollide
    nlinarith [hcollide, ha]
  -- Lift the short cycle from the component graph to `G` and convert to `ZMod`.
  obtain ⟨u, w, hwcyc, hwlen⟩ := hcyc
  set w1 := w.map
    (SimpleGraph.Embedding.induce (G := H) (C.supp : Set (↥(↑S' : Set (Fin n))))).toHom with hw1def
  set w2 := w1.map (SimpleGraph.Embedding.induce (G := G) (↑S' : Set (Fin n))).toHom with hw2def
  have hw1cyc : w1.IsCycle := by
    rw [hw1def]
    exact hwcyc.map
      (SimpleGraph.Embedding.induce (G := H) (C.supp : Set (↥(↑S' : Set (Fin n))))).injective
  have hw2cyc : w2.IsCycle := by
    rw [hw2def]
    exact hw1cyc.map (SimpleGraph.Embedding.induce (G := G) (↑S' : Set (Fin n))).injective
  have hlen : w2.length = w.length := by
    rw [hw2def, hw1def, SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_map]
  have hsupp : ∀ x ∈ w2.support, x ∈ S := by
    intro x hx
    rw [hw2def, SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact hS'sub (Finset.mem_coe.mp y.2)
  obtain ⟨hk3, hex⟩ := cycle_walk_to_zmod hw2cyc hsupp
  exact ⟨w2.length, hk3, by omega, hex⟩

end ACMax
