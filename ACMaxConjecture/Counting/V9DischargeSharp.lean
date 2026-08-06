import ACMaxConjecture.Counting.V9Discharge
import ACMaxConjecture.Counting.MoatSharp

/-!
# The import-free starved kill at `n ≥ 123` (bulk-credited moat)

`Counting/V9Discharge.lean` closes the starved census import-free from `n ≥ 388`, at ball radius
`r = ⌊(⌊(n+8)/9⌋ − 1)/2⌋` — the radius the *old* moat threshold `9k ≤ n + 8` allows.

`Counting/MoatSharp.lean` sharpens that threshold to `12k + X ≤ 2n` by keeping the bulk excess
`Σ_{S₂}(deg − 3)` that `master_cycle_fires` discards.  The admissible radius rises to

  `r = ⌊(2n − X − 12)/24⌋`,

and re-running the same discharge with it drops the import-free threshold from `388` to **`123`**.

**Why `123`.**  The integer condition `|V₉|² < |V₉|(2r+1) + t₉(3r² − r)` holds on the whole
counting region from `n = 111` upward; the discharge below makes the same two relaxations as the
`388` route — `r` replaced by its uniform lower bound (`24r ≥ 2n − X − 35`, dropping `⌊·⌋`) and the
region replaced by an `H`-monotone endpoint — landing the *proved* threshold at `123`.

**Route.**  Unlike the `388` version, the radius now depends on `X`, so the excess term carries
`A = 2N − X − 35` rather than an `X`-free square.  Both `t₉` and `A` are bounded below by `X`-free
linear forms that are *simultaneously* tight at `X = X_max`, so pushing `X` to the master maximum
costs nothing:  `10·t₉ ≥ 6N + 160 − 23H` and `10·A ≥ 16N + 7H − 150`.  What remains is a two-
variable cubic that is monotone decreasing in `H` (every `H`-coefficient is negative at `N ≥ 123`),
so its minimum sits at `17H = 4N − 200`; there `4913·gap − cubic` splits *exactly* as a sum of
three manifestly non-negative products, and `strip_cubic_sharp` closes.
-/

namespace ACMax

open Finset
open scoped Classical

/-! ## Sharpened prerequisites (bulk-credited variants of the `V9Discharge` rows) -/

/-- **The tier-9 quantitative density row** (the honest `t₉ = Θ(n)`).  On a census graph
(`m = 2(n−2)`, `n ≥ 2`) the internal tier-9 pairs satisfy
`2|V₉| + 2n ≤ v9Pairs + 2X + 6h + 8` (`X = excessX n G`, `h = |V₉ᶜ|`), i.e.
`v9Pairs ≥ 2|V₉| + 2·t₉` with the honest excess `t₉ = n − 4 − X − 3h`.  The twins are inside
`V₉`, so the only leakage is to `V₉ᶜ ⊆ heavies`: the total-degree identity `∑ deg = 4n − 8`
(`residual_degree_sum`) and the bipartite `cross_count` give `v9Pairs ≥ 4n − 8 − 2∑_R deg`, and
`∑_R deg = ∑_R(deg − 4) + 4h ≤ X + 4h`. -/
theorem v9_density_row_quant_sharp {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
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

/-- **N3 — the census-free girth import (SW5′).**  The single graph-generic girth surface that
replaces the falsified `AHLSeaTier9`/`AHLSeaTier18` bylines: quantified over an *arbitrary*
*nonempty* subset `S : Finset (Fin n)` and its excess `t` (no `seaSet`, no `excessX` — nothing
census; the `S.Nonempty` guard closes the vacuous `S = ∅, t = 0` slot where both side conditions
hold but no cycle can land), it says a subgraph on `S` with excess `2|S| + 2t ≤ pairs(S)`
(i.e. `e(S) ≥ |S| + t`) that also meets the
strength-specific Moore side condition — here the self-provable **SQRT** form, stated at the ball
*radius* `r` rather than at a cycle-length target, as

  `|S|² < |S|·(2r + 1) + t·(3r² − r)`

— contains a cycle of length `3 ≤ k ≤ 2r + 1` inside `S`.  This is the exact negation of the
`sqrt_double_count_sharp` conclusion transported from the `2`-core to `S`, so no strength is thrown away
between the ball count and the side condition: the older shape `2|S|² ≤ (L − 5)²·t` is the same
inequality after discarding the `|S|(2r+1)` ball term, weakening the level floor `|L_i| ≥ deg` to
`≥ 2`, and rounding `2r ≥ L − 2` down to `L − 5`.  Recovering those three losses is what moves the
import-free floor from `n ≥ 1071` to `n ≥ 379`.  Threaded as a hypothesis and discharged externally
(the AHL strength, N8, reaches further down the band); never proved here. -/
def GirthExcessBoundSharp (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (S : Finset (Fin n)) (t r : ℕ), S.Nonempty → 1 ≤ t → 1 ≤ r →
    2 * S.card + 2 * t ≤ ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card →
    S.card ^ 2 < S.card * (2 * r + 1) + t * (3 * r ^ 2 - r) →
    ∃ k : ℕ, 3 ≤ k ∧ k ≤ 2 * r + 1 ∧
      ∃ c : ZMod k → Fin n, Function.Injective c ∧
        (∀ i : ZMod k, G.Adj (c i) (c (i + 1))) ∧ (∀ i : ZMod k, c i ∈ S)

end ACMax


/-! ## The SQRT discharge of `GirthExcessBoundSharp`

Assembles the SQRT girth cluster into `girth_excess_bound_holds_sharp : ∀ n G,
GirthExcessBoundSharp n G`. The one new ingredient is the **component descent**: after
extracting a min-degree-2 core (`two_core_aux`), a mediant/pigeonhole selects a
component `C` on which `sqrt_double_count_sharp` gives `|C|·(1+2r) + 2·t_C·r² ≤ |C|²`,
colliding with the SQRT side condition to force a short cycle that lifts back to
`G`. `starved_v9_kill_sqrt` is the rebased kill with this import discharged. -/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*}

/-- **The SQRT discharge.**  `GirthExcessBoundSharp` holds for every `n` and `G`.  Given a nonempty `S`
with `2|S| + 2t ≤ pairs(S)` (edge excess `t`) and the SQRT side condition `2|S|² ≤ (L−5)²·t` with
`6 ≤ L`, there is a cycle of length `3 ≤ k ≤ L` inside `S`.  Assembly: extract the min-degree-`2`
`2`-core (`two_core_aux`), pick the excess-carrying component (`exists_mediant_component`), collide
`sqrt_double_count_sharp` with the side condition (`r = ⌊(L−1)/2⌋`), and lift the resulting short cycle
through the two induced-graph embeddings to `G` via `cycle_walk_to_zmod`. -/
theorem girth_excess_bound_holds_sharp (n : ℕ) (G : SimpleGraph (Fin n)) : GirthExcessBoundSharp n G := by
  classical
  intro S t r hSne ht1 hr1 hpairs hside
  have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
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
    have hsqrt := sqrt_double_count_sharp (H.induce (C.supp : Set (↥(↑S' : Set (Fin n)))))
      hmin_C hg hconn_C hexc_C
    -- Abbreviations for the arithmetic collision.
    set nc := Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n)))) with hncval
    set ec := (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card with hecval
    set w : ℕ := 3 * r ^ 2 - r with hwdef
    have hncpos : 0 < nc := Fintype.card_pos
    have hncNN : nc ≤ NN := by
      rw [← hcard_sum]
      exact Finset.single_le_sum (f := fun D : H.ConnectedComponent => Fintype.card D.supp)
        (fun D _ => Nat.zero_le _) (Finset.mem_univ C)
    have hNleS : NN ≤ S.card := by
      rw [hcardV']; exact Finset.card_le_card hS'sub
    -- (i) Multiply the component ball count by `NN²` and feed in the mediant, so that the
    -- component excess `ec − nc` is replaced by the global excess `t`.
    have key1 : NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t) ≤ NN ^ 2 * nc ^ 2 := by
      have hstep : w * (nc ^ 2 * t) ≤ NN ^ 2 * ((ec - nc) * w) := by
        calc w * (nc ^ 2 * t) ≤ w * (NN ^ 2 * (ec - nc)) := Nat.mul_le_mul_left w hmed2
          _ = NN ^ 2 * ((ec - nc) * w) := by ring
      calc NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t)
          ≤ NN ^ 2 * (nc * (1 + 2 * r)) + NN ^ 2 * ((ec - nc) * w) := by
            have hcomm : NN ^ 2 * (nc * (2 * r + 1)) = NN ^ 2 * (nc * (1 + 2 * r)) := by ring
            rw [hcomm]
            exact Nat.add_le_add_left hstep _
        _ = NN ^ 2 * (nc * (1 + 2 * r) + (ec - nc) * w) := by ring
        _ ≤ NN ^ 2 * nc ^ 2 := Nat.mul_le_mul_left _ hsqrt
    -- (ii) Trade one factor `NN` for `nc` in the ball term and cancel `nc²`.
    have key2 : NN * (2 * r + 1) + t * w ≤ NN ^ 2 := by
      have hmul : (NN * (2 * r + 1) + t * w) * nc ^ 2 ≤ NN ^ 2 * nc ^ 2 := by
        have hswap : NN * (2 * r + 1) * nc ^ 2 ≤ NN ^ 2 * (nc * (2 * r + 1)) := by
          have e1 : NN * (2 * r + 1) * nc ^ 2 = (nc * (2 * r + 1)) * (nc * NN) := by ring
          have e2 : NN ^ 2 * (nc * (2 * r + 1)) = (nc * (2 * r + 1)) * (NN * NN) := by ring
          rw [e1, e2]
          gcongr
        have hrest : t * w * nc ^ 2 = w * (nc ^ 2 * t) := by ring
        calc (NN * (2 * r + 1) + t * w) * nc ^ 2
            = NN * (2 * r + 1) * nc ^ 2 + t * w * nc ^ 2 := by ring
          _ ≤ NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t) := by
              rw [hrest]; exact Nat.add_le_add_right hswap _
          _ ≤ NN ^ 2 * nc ^ 2 := key1
      exact Nat.le_of_mul_le_mul_right hmul (pow_pos hncpos 2)
    -- (iii) Transport `NN ↦ |S|`: `x ↦ x² − x(2r+1)` is monotone above `(2r+1)/2`, and `key2`
    -- itself forces `2r + 1 ≤ NN`.
    have hNNpos : 0 < NN := lt_of_lt_of_le hncpos hncNN
    have h2r1 : 2 * r + 1 ≤ NN := by
      have h : NN * (2 * r + 1) ≤ NN * NN := by
        calc NN * (2 * r + 1) ≤ NN * (2 * r + 1) + t * w := Nat.le_add_right _ _
          _ ≤ NN ^ 2 := key2
          _ = NN * NN := by ring
      exact Nat.le_of_mul_le_mul_left h hNNpos
    have hmono : NN ^ 2 + S.card * (2 * r + 1) ≤ S.card ^ 2 + NN * (2 * r + 1) := by
      obtain ⟨d, hd⟩ : ∃ d, S.card = NN + d := ⟨S.card - NN, by omega⟩
      have h1 : d * (2 * r + 1) ≤ d * NN := Nat.mul_le_mul_left d h2r1
      rw [hd]
      nlinarith [h1]
    -- (iv) Collide with the side condition.
    omega
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


/-! ## The honest heavy budget

The one counting row that lives here rather than in `Counting.StarvedCensus`: the heavy budget
`h + h₆₊ + 4·n_g ≤ X`, which the `MASTER′` assembly consumes.  The `n ≥ 388` dispatch that this
section used to carry has been superseded by `Counting.V9DischargeSharp` (`starved_dead_ge_123`),
which runs the same collision at the bulk-credited moat radius of `Counting.MoatSharp`.
-/

namespace ACMax

open Finset
open scoped Classical

/-- **The honest heavy budget** (D1′).  At `n ≥ 57` the total excess `X = excessX n G` dominates
`h + h₆₊ + 4·n_g`, where `h = |V₉ᶜ|` counts the heavies (`deg ≥ 5`), `h₆₊` the non-giant
deg-`≥6` hubs and `n_g` the giants (`n + 15 < 9·deg`).  Each deg-`≥5` vertex spends `deg − 4 ≥ 1`
excess (that is `h`), each deg-`≥6` non-giant an extra `1` (so `2 ≤ deg − 4`), and each giant
(`deg ≥ 9` already at `n ≥ 57`) an extra `4` (so `5 ≤ deg − 4`).

The giant credit is `4` — exactly what the `MASTER′` assembly consumes (`28·n_g ≤ 7·4·n_g`).  It
used to be `119`, which forced `n ≥ 1100` on this row alone and so on the whole import-free band;
`4` costs the assembly nothing and holds from `n = 57`. -/
theorem heavy_full_budget_sharp {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 57 ≤ n) :
    (v9Set G)ᶜ.card
      + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h))).card
      + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card
      ≤ excessX n G := by
  have hhub : hubSet G = Finset.univ.filter (fun v => 4 ≤ G.degree v) := rfl
  have hexc : excessX n G = ∑ v ∈ hubSet G, (G.degree v - 4) := by
    unfold excessX
    rw [hhub]
    refine Finset.sum_subset ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      omega
    · intro v hv hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv2
      omega
  have hcard5 : (v9Set G)ᶜ.card = ((hubSet G).filter (fun v => 5 ≤ G.degree v)).card := by
    congr 1
    ext v
    simp only [Finset.mem_compl, mem_v9Set, Finset.mem_filter, mem_hubSet]
    omega
  rw [hexc, hcard5, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  rw [mem_hubSet] at hv
  split_ifs <;> omega

/-! ## The arithmetic core -/

/-- **The sharp strip cubic.**  The single-variable inequality the `n ≥ 123` region arithmetic
bottoms out at, after `X` is pushed to its master maximum and `H` to the end of its range.
Substituting `N = 123 + u` makes every coefficient non-negative
(`1068496017 + 1122649307u + 11552736u² + 20700u³`), which is what `nlinarith` finds. -/
theorem strip_cubic_sharp {N : ℤ} (hN : 123 ≤ N) :
    779812849 * N + 755972700 < 20700 * N ^ 3 + 3914436 * N ^ 2 := by
  have hu : (0 : ℤ) ≤ N - 123 := by linarith
  nlinarith [hu, mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]

/-- **The two-variable core.**  After both `X`-eliminations the target is a cubic in `(N, H)`:

  `4608000·(N−H)² < 38400·(N−H)·(Q+120) + 23·P·Q²`,  `P = 6N+160−23H`, `Q = 16N+7H−150`.

Every `H`-coefficient of the gap is negative at `N ≥ 123`, so the minimum is at `17H = 4N − 200`,
and `4913·gap − cubic` is *identically* `289(M−17H)(−c₁) + 17(M²−(17H)²)(−c₂) + (M³−(17H)³)·25921`
with `M = 4N − 200`, `−c₁ = 104512N² − 11944120N + 18478500 ≥ 0` (its larger root is `≈ 112.7`)
and `−c₂ = 111734N + 3585580 ≥ 0`.  So `linarith` closes on those three products plus the cubic. -/
theorem moore_strip_twovar_sharp {N H : ℤ} (hN : 123 ≤ N) (hH : 0 ≤ H)
    (hs : 17 * H ≤ 4 * N - 200) :
    4608000 * (N - H) ^ 2
      < 38400 * ((N - H) * (16 * N + 7 * H - 30))
        + 23 * ((6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2) := by
  have hd : (0 : ℤ) ≤ (4 * N - 200) - 17 * H := by linarith
  have hHm : (0 : ℤ) ≤ 17 * H := by linarith
  have hnc1 : (0 : ℤ) ≤ 104512 * N ^ 2 - 11944120 * N + 18478500 := by nlinarith [hN]
  have hnc2 : (0 : ℤ) ≤ 111734 * N + 3585580 := by linarith
  have hsq : (0 : ℤ) ≤ (4 * N - 200) ^ 2 + 17 * H * (4 * N - 200) + (17 * H) ^ 2 := by
    nlinarith [hHm, hd, sq_nonneg (4 * N - 200), sq_nonneg (17 * H)]
  have e1 := mul_nonneg hd hnc1
  have e2 := mul_nonneg (mul_nonneg hd (by linarith : (0 : ℤ) ≤ (4 * N - 200) + 17 * H)) hnc2
  have e3 := mul_nonneg (mul_nonneg hd hsq) (by norm_num : (0 : ℤ) ≤ 25921)
  have hcub := strip_cubic_sharp hN
  linarith [e1, e2, e3, hcub]

/-- **The `R`-free core of the sharp strip discharge.**  On the counting region
(`0 ≤ H ≤ X`, `10X + 7H ≤ 4N − 200`) at `N ≥ 123`,

  `4608·(N−H)² < 384·(N−H)·(2N−X−23) + 23·(N−4−X−3H)·(2N−X−35)²`.

Both `X`-dependent factors are pushed to the master maximum simultaneously — `10·t ≥ 6N+160−23H`
and `10·A ≥ 16N+7H−150`, equalities together at `X = X_max` — and `moore_strip_twovar_sharp`
closes what is left. -/
theorem moore_strip_core_sharp {N X H : ℤ} (hN : 123 ≤ N) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hmaster : 10 * X + 7 * H ≤ 4 * N - 200) :
    4608 * (N - H) ^ 2
      < 384 * ((N - H) * (2 * N - X - 23))
        + 23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2) := by
  have h17 : 17 * H ≤ 4 * N - 200 := by linarith
  have hvpos : (0 : ℤ) ≤ N - H := by linarith
  have hPpos : (0 : ℤ) ≤ 6 * N + 160 - 23 * H := by linarith
  have hQpos : (0 : ℤ) ≤ 16 * N + 7 * H - 150 := by linarith
  have hP : 6 * N + 160 - 23 * H ≤ 10 * (N - 4 - X - 3 * H) := by linarith
  have hQ : 16 * N + 7 * H - 150 ≤ 10 * (2 * N - X - 35) := by linarith
  -- the ball factor, pushed to the master maximum
  have hA : 38400 * ((N - H) * (16 * N + 7 * H - 30))
      ≤ 1000 * (384 * ((N - H) * (2 * N - X - 23))) := by nlinarith [hvpos, hQ]
  -- the excess factor, pushed to the master maximum
  have hQ2 : (16 * N + 7 * H - 150) ^ 2 ≤ (10 * (2 * N - X - 35)) ^ 2 := by
    nlinarith [hQpos, hQ]
  have hmul : (6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2
      ≤ (10 * (N - 4 - X - 3 * H)) * (10 * (2 * N - X - 35)) ^ 2 :=
    mul_le_mul hP hQ2 (sq_nonneg _) (by linarith)
  have hB : 23 * ((6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2)
      ≤ 1000 * (23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2)) := by nlinarith [hmul]
  have htv := moore_strip_twovar_sharp hN hH h17
  linarith [hA, hB, htv]

/-- **The sharp strip Moore arithmetic.**  On the counting region, `MASTER′` together with
`H ≤ X`, `N ≥ 123` and the sharpened radius bound `2N − X − 35 ≤ 24R` forces the SQRT side
condition

  `(N − H)² < (N − H)(2R + 1) + (N − 4 − X − 3H)(3R² − R)`.

Route: `moore_strip_core_sharp` supplies the `R`-free inequality; then `12(2R+1) ≥ 2N−X−23`
upgrades the ball term and `23(2N−X−35)² ≤ 4608(3R²−R)` the excess term (from `(2N−X−35)² ≤
576R²` and `23R² ≤ 8(3R²−R)`, the latter by `R ≥ 8`), both by the same factor `4608 = 384·12`. -/
theorem moore_strip_arith_sharp {N X H R : ℤ} (hN : 123 ≤ N)
    (hH : 0 ≤ H) (hHX : H ≤ X) (hR : 2 * N - X - 35 ≤ 24 * R)
    (hmaster : 10 * X + 7 * H ≤ 4 * N - 200) :
    (N - H) ^ 2 < (N - H) * (2 * R + 1) + (N - 4 - X - 3 * H) * (3 * R ^ 2 - R) := by
  have hR8 : (8 : ℤ) ≤ R := by omega
  have hvpos : (0 : ℤ) ≤ N - H := by linarith
  have hq : (0 : ℤ) ≤ N - 4 - X - 3 * H := by linarith
  have hApos : (0 : ℤ) ≤ 2 * N - X - 35 := by linarith
  have hcore := moore_strip_core_sharp hN hH hHX hmaster
  -- the ball term: `12(2R + 1) = 24R + 12 ≥ 2N − X − 23`
  have hball : (N - H) * (2 * N - X - 23) ≤ 12 * ((N - H) * (2 * R + 1)) := by
    nlinarith [hvpos, hR]
  -- the excess term
  have hsq : (2 * N - X - 35) ^ 2 ≤ 576 * R ^ 2 := by nlinarith [hR, hApos]
  have hRR : 23 * R ^ 2 ≤ 8 * (3 * R ^ 2 - R) := by nlinarith [hR8]
  have hexc : 23 * (2 * N - X - 35) ^ 2 ≤ 4608 * (3 * R ^ 2 - R) := by nlinarith [hsq, hRR]
  have hB : 23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2)
      ≤ 4608 * ((N - 4 - X - 3 * H) * (3 * R ^ 2 - R)) := by nlinarith [hq, hexc]
  linarith [hcore, hball, hB]

/-! ## The graph-level dispatch -/

/-- **The sharpened tier-9 girth.**  In a never-firing starved census, `V₉` contains no cycle of
length `k` with `12k + X ≤ 2n` — against `9k ≤ n + 8` for `v9_girth`. -/
theorem v9_girth_sharp {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hk : 3 ≤ k) (hn8 : 8 ≤ n) (hkn : 12 * k + excessX n G ≤ 2 * n) (c : ZMod k → Fin n)
    (hcinj : Function.Injective c) (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hmem : ∀ i : ZMod k, c i ∈ v9Set G) : False :=
  hnf (v9_short_cycle_fires_sharp hk G hm h3 c hcinj hadj
    (fun i => mem_v9Set.mp (hmem i)) hn8 hkn)

/-- **The rebased tier-9 kill at the sharpened moat obligation.**  Identical to
`starved_v9_kill_sqrt` except that the moat obligation is `12(2r+1) + X ≤ 2n` rather than
`9(2r+1) ≤ n + 8`: the cycle the ball count produces has length at most `2r + 1`, and a `V₉`-cycle
that short fires `v9_short_cycle_fires_sharp`. -/
theorem starved_v9_kill_sharp {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hlo : 55 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 5 ≤ n)
    (r : ℕ) (hr1 : 1 ≤ r) (hrn : 12 * (2 * r + 1) + excessX n G ≤ 2 * n)
    (hMoore : (v9Set G).card ^ 2
      < (v9Set G).card * (2 * r + 1)
        + (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card) * (3 * r ^ 2 - r)) : False := by
  set t9 : ℕ := n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card with ht9def
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRcard : (v9Set G)ᶜ.card ≤ excessX n G :=
    le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hexc : 2 * (v9Set G).card + 2 * t9 ≤ v9Pairs G := by
    have hq := v9_density_row_quant_sharp G (by omega) hm
    rw [ht9def]
    omega
  have ht1 : 1 ≤ t9 := by rw [ht9def]; omega
  have hne : (v9Set G).Nonempty := by
    rw [← Finset.card_pos]
    have hsize := v9_size_row G
    omega
  obtain ⟨k, hk3, hkr, c, hcinj, hadj, hmem⟩ :=
    girth_excess_bound_holds_sharp n G (v9Set G) t9 r hne ht1 hr1 hexc hMoore
  have : NeZero k := ⟨by omega⟩
  exact v9_girth_sharp G hm h3 hnf hk3 (by omega) (by omega) c hcinj hadj hmem

/-- **D3′ — the import-free starved kill at `n ≥ 123`.**  A never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) on `123 ≤ n` cannot exist, with no external girth byline.  Same
single branch as `starved_dead_ge_388`, run at the bulk-credited radius
`r = ⌊(2n − X − 12)/24⌋` and discharged by `moore_strip_arith_sharp`. -/
theorem starved_dead_ge_123 {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn : 123 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) : False := by
  have hD1 := slots_p_row G (by omega) hm h3 hnf hs0
  have hPC := p_choke_row_unconditional (by omega) G hm h3 hs0 hnf
  have hbud := heavy_full_budget_sharp G (by omega)
  have hMaster : 10 * excessX n G + 7 * (v9Set G)ᶜ.card ≤ 4 * n - 200 := by omega
  have hhX : (v9Set G)ᶜ.card ≤ excessX n G := by
    have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
      intro v hv
      rw [Finset.mem_compl, mem_v9Set] at hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
    exact le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 5 ≤ n := by omega
  -- the bulk-credited ball radius `r = ⌊(2n − X − 12)/24⌋`
  set Xe := excessX n G with hXe
  set Hc := (v9Set G)ᶜ.card with hHc
  have hr1 : 1 ≤ (2 * n - Xe - 12) / 24 := by omega
  have hrn : 12 * (2 * ((2 * n - Xe - 12) / 24) + 1) + Xe ≤ 2 * n := by omega
  have hr24 : 2 * n - Xe - 35 ≤ 24 * ((2 * n - Xe - 12) / 24) := by omega
  have hVhh : (v9Set G).card + Hc = n := by
    rw [hHc, Finset.card_add_card_compl, Fintype.card_fin]
  have hMoore : (v9Set G).card ^ 2
      < (v9Set G).card * (2 * ((2 * n - Xe - 12) / 24) + 1)
        + (n - 4 - Xe - 3 * Hc)
          * (3 * ((2 * n - Xe - 12) / 24) ^ 2 - ((2 * n - Xe - 12) / 24)) := by
    set Vc := (v9Set G).card with hVc
    set Rl := (2 * n - Xe - 12) / 24 with hRl
    -- make the radius opaque: `omega` must not reason under the nested `⌊·⌋`
    clear_value Rl
    clear hRl
    obtain ⟨q, hq⟩ : ∃ q, n = 4 + Xe + 3 * Hc + q := ⟨n - (4 + Xe + 3 * Hc), by omega⟩
    have e1 : n - 4 - Xe - 3 * Hc = q := by omega
    have e2 : Vc = 4 + Xe + 2 * Hc + q := by omega
    have hkey := moore_strip_arith_sharp (N := (n : ℤ)) (X := (Xe : ℤ)) (H := (Hc : ℤ))
      (R := (Rl : ℤ)) (by exact_mod_cast hn) (Int.natCast_nonneg _)
      (Nat.cast_le.mpr hhX) (by omega) (by omega)
    have hnZ : (n : ℤ) = 4 + (Xe : ℤ) + 3 * (Hc : ℤ) + (q : ℤ) := by exact_mod_cast hq
    have ea : (n : ℤ) - (Hc : ℤ) = 4 + (Xe : ℤ) + 2 * (Hc : ℤ) + (q : ℤ) := by rw [hnZ]; ring
    have eb : (n : ℤ) - 4 - (Xe : ℤ) - 3 * (Hc : ℤ) = (q : ℤ) := by rw [hnZ]; ring
    rw [ea, eb] at hkey
    have hle : Rl ≤ 3 * Rl ^ 2 :=
      calc Rl = Rl * 1 := (Nat.mul_one Rl).symm
        _ ≤ Rl * (3 * Rl) := Nat.mul_le_mul_left Rl (by omega)
        _ = 3 * Rl ^ 2 := by ring
    set w := 3 * Rl ^ 2 - Rl with hwdef
    have hw : 3 * Rl ^ 2 = w + Rl := by rw [hwdef, Nat.sub_add_cancel hle]
    have hwZ : (3 : ℤ) * (Rl : ℤ) ^ 2 - (Rl : ℤ) = (w : ℤ) := by
      have hcast : ((3 * Rl ^ 2 : ℕ) : ℤ) = ((w + Rl : ℕ) : ℤ) := by exact_mod_cast hw
      push_cast at hcast
      linarith
    rw [hwZ] at hkey
    rw [e1, e2]
    exact_mod_cast hkey
  exact starved_v9_kill_sharp G (by omega) hm h3 hnf hpos ((2 * n - Xe - 12) / 24) hr1 hrn hMoore

end ACMax
