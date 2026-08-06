import ACMaxConjecture.Reduction.Residual
import ACMaxConjecture.Counting.FarPair
import ACMaxConjecture.Counting.DoubleStar


/-!
# Slot far-pair certificates and the compact-cell vocabulary

The slot function `σ(d) = (d−3)/(d−2)` turns the weighted double-star test vector
into a local certificate.  If two non-adjacent vertices have disjoint
neighbourhoods and their combined slot cost is nonpositive, then
`algConn G ≤ 2`.  The cross-free specialization is packaged as
`algConn_le_two_of_usable_far_pair` and `HasUsableFarPair`.

The final section supplies only the compact-cell vocabulary used downstream:
the degree excess `excessX`, the radius-three set `closeSet`, and the bound on
light non-usable degree-three vertices.  Stronger covering statements formerly
developed in this module were not part of the final theorem's dependency
closure and have been removed.
-/

namespace ACMax

open scoped Classical
open Finset

variable {V : Type*} [Fintype V]

/-! ## The `σ` ecology quantities -/

/-- The **slot value function** `σ(d) = (d−3)/(d−2)`: the per-slot worst-case
surplus of a degree-`d` neighbour used as a leak carrier.  `σ(3) = 0`,
`σ(4) = 1/2`, `σ(5) = 2/3`, `σ(6) = 3/4`, `σ → 1`. -/
noncomputable def sigma (d : ℕ) : ℝ := ((d : ℝ) - 3) / ((d : ℝ) - 2)

/-- The **mass factor** `c_u = 1 + Σ_{w∈N(u)} 1/(deg w − 2)`. -/
noncomputable def cW (G : SimpleGraph V) (u : V) : ℝ :=
  1 + ∑ w ∈ G.neighborFinset u, (1 : ℝ) / ((G.degree w : ℝ) - 2)

/-- The **`σ`-sum** `Σσ_u = Σ_{w∈N(u)} σ(deg w)`. -/
noncomputable def sigS (G : SimpleGraph V) (u : V) : ℝ :=
  ∑ w ∈ G.neighborFinset u, sigma (G.degree w)

/-! ### `σ` arithmetic (`L-FB-2` real-valued facts) -/

theorem sigma_four : sigma 4 = 1 / 2 := by norm_num [sigma]

/-- `σ` is monotone on `d ≥ 3`: `σ(d) = 1 − 1/(d−2)`. -/
theorem sigma_le_of_le {c d : ℕ} (hc : 3 ≤ c) (hcd : c ≤ d) : sigma c ≤ sigma d := by
  unfold sigma
  have hc3 : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hcd' : (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcd
  have hc2 : (0 : ℝ) < (c : ℝ) - 2 := by linarith
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  have hcne : ((c : ℝ) - 2) ≠ 0 := ne_of_gt hc2
  have hdne : ((d : ℝ) - 2) ≠ 0 := ne_of_gt hd2
  have keyc : ((c : ℝ) - 3) / ((c : ℝ) - 2) = 1 - 1 / ((c : ℝ) - 2) := by
    field_simp; ring
  have keyd : ((d : ℝ) - 3) / ((d : ℝ) - 2) = 1 - 1 / ((d : ℝ) - 2) := by
    field_simp; ring
  rw [keyc, keyd]
  have : 1 / ((d : ℝ) - 2) ≤ 1 / ((c : ℝ) - 2) :=
    one_div_le_one_div_of_le hc2 (by linarith)
  linarith

/-! ## `cW` positivity -/

/-- The mass factor is at least `1` on a graph of minimum degree `≥ 3`. -/
theorem one_le_cW (G : SimpleGraph V) (u : V) (hmin : ∀ w : V, 3 ≤ G.degree w) :
    1 ≤ cW G u := by
  unfold cW
  have hnn : 0 ≤ ∑ w ∈ G.neighborFinset u, (1 : ℝ) / ((G.degree w : ℝ) - 2) := by
    apply Finset.sum_nonneg
    intro w _
    have hd : (3 : ℝ) ≤ (G.degree w : ℝ) := by exact_mod_cast hmin w
    apply div_nonneg <;> linarith
  linarith

theorem cW_pos (G : SimpleGraph V) (u : V) (hmin : ∀ w : V, 3 ≤ G.degree w) :
    0 < cW G u :=
  lt_of_lt_of_le one_pos (one_le_cW G u hmin)

/-! ## `L-FB-1`: the slot far-pair certificate -/

/-- **The per-slot identity.**  With slot weight `p = au/(d−2)` and worst-case
leak `d − 1`, the slot cost equals `2·p² + au²·σ(d)`. -/
theorem slot_pointwise (au : ℝ) (d : ℕ) (hd : 3 ≤ d) :
    (au - au / ((d : ℝ) - 2)) ^ 2 + ((d : ℝ) - 1) * (au / ((d : ℝ) - 2)) ^ 2
      = 2 * (au / ((d : ℝ) - 2)) ^ 2 + au ^ 2 * sigma d := by
  unfold sigma
  have h3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2 : ((d : ℝ) - 2) ≠ 0 := by intro hc; linarith
  field_simp
  ring

/-- **`L-FB-1` — the slot far-pair certificate (general cross form).**  A far
pair `u ≠ v` (not adjacent, no common neighbour) in a graph of minimum degree
`≥ 3` whose *slot value*

  `c_v²·(Σσ_u − 2) + c_u²·(Σσ_v − 2) + Σ_{w∈N(u),w'∈N(v)} [w ~ w']·(p_w + q_{w'})² ≤ 0`

certifies `algConn G ≤ 2`.  Instance of `algConn_le_two_of_weighted_double_star`
with slot weights `p_w = c_v/(deg w − 2)`, `q_{w'} = c_u/(deg w' − 2)`. -/
theorem algConn_le_two_of_slot_far_pair [Nonempty V] (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hcap : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    (hmin : ∀ w : V, 3 ≤ G.degree w)
    (hslot :
      (cW G v) ^ 2 * (sigS G u - 2) + (cW G u) ^ 2 * (sigS G v - 2)
        + (∑ w ∈ G.neighborFinset u, ∑ w' ∈ G.neighborFinset v,
            (if G.Adj w w' then
              (cW G v / ((G.degree w : ℝ) - 2) + cW G u / ((G.degree w' : ℝ) - 2)) ^ 2
             else 0))
        ≤ 0) :
    algConn G ≤ 2 := by
  classical
  have hauPos : 0 < cW G v := cW_pos G v hmin
  have havPos : 0 < cW G u := cW_pos G u hmin
  -- degree-2 shift positive
  have hdpos : ∀ w : V, (0 : ℝ) < (G.degree w : ℝ) - 2 := by
    intro w
    have h3 : (3 : ℝ) ≤ (G.degree w : ℝ) := by exact_mod_cast hmin w
    linarith
  refine algConn_le_two_of_weighted_double_star G u v (cW G v) (cW G u)
    (fun w => cW G v / ((G.degree w : ℝ) - 2)) (fun w => cW G u / ((G.degree w : ℝ) - 2))
    hne huv hcap hauPos ?_ ?_ ?_ ?_
  · -- hp
    intro w _; exact div_nonneg hauPos.le (hdpos w).le
  · -- hq
    intro w _; exact div_nonneg havPos.le (hdpos w).le
  · -- balance
    have e1 : ∑ w ∈ G.neighborFinset u, cW G v / ((G.degree w : ℝ) - 2)
        = cW G v * ∑ w ∈ G.neighborFinset u, (1 : ℝ) / ((G.degree w : ℝ) - 2) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; ring
    have e2 : ∑ w ∈ G.neighborFinset v, cW G u / ((G.degree w : ℝ) - 2)
        = cW G u * ∑ w ∈ G.neighborFinset v, (1 : ℝ) / ((G.degree w : ℝ) - 2) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; ring
    rw [e1, e2]
    unfold cW
    ring
  -- the quadratic bound
  -- leak bounds: card ≤ deg w - 1
  have hleakU : (∑ w ∈ G.neighborFinset u,
        ((G.neighborFinset w \ insert u (G.neighborFinset v)).card : ℝ)
          * (cW G v / ((G.degree w : ℝ) - 2)) ^ 2)
      ≤ ∑ w ∈ G.neighborFinset u,
          ((G.degree w : ℝ) - 1) * (cW G v / ((G.degree w : ℝ) - 2)) ^ 2 := by
    apply Finset.sum_le_sum
    intro w hw
    have humem : u ∈ G.neighborFinset w :=
      (G.mem_neighborFinset w u).mpr (G.adj_symm ((G.mem_neighborFinset u w).mp hw))
    have hsub : G.neighborFinset w \ insert u (G.neighborFinset v)
        ⊆ G.neighborFinset w \ {u} :=
      Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self u _))
    have hcard : (G.neighborFinset w \ insert u (G.neighborFinset v)).card
        ≤ G.degree w - 1 := by
      calc (G.neighborFinset w \ insert u (G.neighborFinset v)).card
          ≤ (G.neighborFinset w \ {u}).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            have hin : (G.neighborFinset w ∩ ({u} : Finset V)).card = 1 := by
              rw [Finset.inter_singleton_of_mem humem, Finset.card_singleton]
            have hadd := Finset.card_sdiff_add_card_inter (G.neighborFinset w)
              ({u} : Finset V)
            rw [SimpleGraph.card_neighborFinset_eq_degree] at hadd
            omega
    have hge1 : 1 ≤ G.degree w := by
      have := Finset.card_pos.mpr ⟨u, humem⟩
      rwa [SimpleGraph.card_neighborFinset_eq_degree] at this
    have hcast : ((G.neighborFinset w \ insert u (G.neighborFinset v)).card : ℝ)
        ≤ (G.degree w : ℝ) - 1 := by
      have h1 : ((G.neighborFinset w \ insert u (G.neighborFinset v)).card : ℝ)
          ≤ ((G.degree w - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard
      rwa [Nat.cast_sub hge1, Nat.cast_one] at h1
    exact mul_le_mul_of_nonneg_right hcast (by positivity)
  have hleakV : (∑ w ∈ G.neighborFinset v,
        ((G.neighborFinset w \ insert v (G.neighborFinset u)).card : ℝ)
          * (cW G u / ((G.degree w : ℝ) - 2)) ^ 2)
      ≤ ∑ w ∈ G.neighborFinset v,
          ((G.degree w : ℝ) - 1) * (cW G u / ((G.degree w : ℝ) - 2)) ^ 2 := by
    apply Finset.sum_le_sum
    intro w hw
    have hvmem : v ∈ G.neighborFinset w :=
      (G.mem_neighborFinset w v).mpr (G.adj_symm ((G.mem_neighborFinset v w).mp hw))
    have hsub : G.neighborFinset w \ insert v (G.neighborFinset u)
        ⊆ G.neighborFinset w \ {v} :=
      Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self v _))
    have hcard : (G.neighborFinset w \ insert v (G.neighborFinset u)).card
        ≤ G.degree w - 1 := by
      calc (G.neighborFinset w \ insert v (G.neighborFinset u)).card
          ≤ (G.neighborFinset w \ {v}).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            have hin : (G.neighborFinset w ∩ ({v} : Finset V)).card = 1 := by
              rw [Finset.inter_singleton_of_mem hvmem, Finset.card_singleton]
            have hadd := Finset.card_sdiff_add_card_inter (G.neighborFinset w)
              ({v} : Finset V)
            rw [SimpleGraph.card_neighborFinset_eq_degree] at hadd
            omega
    have hge1 : 1 ≤ G.degree w := by
      have := Finset.card_pos.mpr ⟨v, hvmem⟩
      rwa [SimpleGraph.card_neighborFinset_eq_degree] at this
    have hcast : ((G.neighborFinset w \ insert v (G.neighborFinset u)).card : ℝ)
        ≤ (G.degree w : ℝ) - 1 := by
      have h1 : ((G.neighborFinset w \ insert v (G.neighborFinset u)).card : ℝ)
          ≤ ((G.degree w - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard
      rwa [Nat.cast_sub hge1, Nat.cast_one] at h1
    exact mul_le_mul_of_nonneg_right hcast (by positivity)
  -- per-slot identities collapse centre + full leak into 2·p² + c_v²·σ
  have hidU : ∑ w ∈ G.neighborFinset u,
        ((cW G v - cW G v / ((G.degree w : ℝ) - 2)) ^ 2
          + ((G.degree w : ℝ) - 1) * (cW G v / ((G.degree w : ℝ) - 2)) ^ 2)
      = ∑ w ∈ G.neighborFinset u,
          (2 * (cW G v / ((G.degree w : ℝ) - 2)) ^ 2 + (cW G v) ^ 2 * sigma (G.degree w)) := by
    apply Finset.sum_congr rfl
    intro w _
    exact slot_pointwise (cW G v) (G.degree w) (hmin w)
  have hidV : ∑ w ∈ G.neighborFinset v,
        ((cW G u - cW G u / ((G.degree w : ℝ) - 2)) ^ 2
          + ((G.degree w : ℝ) - 1) * (cW G u / ((G.degree w : ℝ) - 2)) ^ 2)
      = ∑ w ∈ G.neighborFinset v,
          (2 * (cW G u / ((G.degree w : ℝ) - 2)) ^ 2 + (cW G u) ^ 2 * sigma (G.degree w)) := by
    apply Finset.sum_congr rfl
    intro w _
    exact slot_pointwise (cW G u) (G.degree w) (hmin w)
  -- expand the collapsed sums
  have hsplitU :
      (∑ w ∈ G.neighborFinset u, (cW G v - cW G v / ((G.degree w : ℝ) - 2)) ^ 2)
        + (∑ w ∈ G.neighborFinset u,
            ((G.degree w : ℝ) - 1) * (cW G v / ((G.degree w : ℝ) - 2)) ^ 2)
      = 2 * (∑ w ∈ G.neighborFinset u, (cW G v / ((G.degree w : ℝ) - 2)) ^ 2)
          + (cW G v) ^ 2 * sigS G u := by
    rw [← Finset.sum_add_distrib, hidU, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    rfl
  have hsplitV :
      (∑ w ∈ G.neighborFinset v, (cW G u - cW G u / ((G.degree w : ℝ) - 2)) ^ 2)
        + (∑ w ∈ G.neighborFinset v,
            ((G.degree w : ℝ) - 1) * (cW G u / ((G.degree w : ℝ) - 2)) ^ 2)
      = 2 * (∑ w ∈ G.neighborFinset v, (cW G u / ((G.degree w : ℝ) - 2)) ^ 2)
          + (cW G u) ^ 2 * sigS G v := by
    rw [← Finset.sum_add_distrib, hidV, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    rfl
  -- final linear combination (the cross sum matches hslot literally)
  have hdist_u : (cW G v) ^ 2 * (sigS G u - 2)
      = (cW G v) ^ 2 * sigS G u - 2 * (cW G v) ^ 2 := by ring
  have hdist_v : (cW G u) ^ 2 * (sigS G v - 2)
      = (cW G u) ^ 2 * sigS G v - 2 * (cW G u) ^ 2 := by ring
  linarith [hsplitU, hsplitV, hslot, hleakU, hleakV, hdist_u, hdist_v]

/-- **`L-FB-1` — cross-free (distance-`≥ 4`) corollary.**  When there is no edge
between `N(u)` and `N(v)` the cross term vanishes, and the criterion reduces to
`c_v²·(Σσ_u − 2) + c_u²·(Σσ_v − 2) ≤ 0`. -/
theorem algConn_le_two_of_slot_far_pair_far [Nonempty V] (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hcap : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    (hmin : ∀ w : V, 3 ≤ G.degree w)
    (hfar : ∀ w w' : V, G.Adj u w → G.Adj v w' → ¬G.Adj w w')
    (hslot0 : (cW G v) ^ 2 * (sigS G u - 2) + (cW G u) ^ 2 * (sigS G v - 2) ≤ 0) :
    algConn G ≤ 2 := by
  apply algConn_le_two_of_slot_far_pair G u v hne huv hcap hmin
  have hz : (∑ w ∈ G.neighborFinset u, ∑ w' ∈ G.neighborFinset v,
      (if G.Adj w w' then
        (cW G v / ((G.degree w : ℝ) - 2) + cW G u / ((G.degree w' : ℝ) - 2)) ^ 2
       else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    apply Finset.sum_eq_zero
    intro w' hw'
    exact if_neg (hfar w w' ((G.mem_neighborFinset u w).mp hw)
      ((G.mem_neighborFinset v w').mp hw'))
  rw [hz]; linarith

/-- **`L-FB-1` — the `hslot_both` workhorse form.**  A cross-free far pair each of
whose ends is `σ`-usable (`Σσ ≤ 2`) fires.  This is the exact form that makes
every clean carrier / `Δ ≤ 5` degree-3 end usable. -/
theorem algConn_le_two_of_slot_far_pair_both [Nonempty V] (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hcap : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    (hmin : ∀ w : V, 3 ≤ G.degree w)
    (hfar : ∀ w w' : V, G.Adj u w → G.Adj v w' → ¬G.Adj w w')
    (hu : sigS G u ≤ 2) (hv : sigS G v ≤ 2) :
    algConn G ≤ 2 := by
  apply algConn_le_two_of_slot_far_pair_far G u v hne huv hcap hmin hfar
  nlinarith [sq_nonneg (cW G v), sq_nonneg (cW G u), hu, hv]

/-! ## The slot-far-pair packaging and the fat-side assembly -/

/-! ## The spread half: the usable-far-pair firing law

The *spread* (large-diameter) half of the fat side. The workhorse
`algConn_le_two_of_usable_far_pair` is the cross-free instance of the slot
far-pair certificate: two `σ`-usable vertices (`sigS ≤ 2`) at distance `≥ 4`
close, the slot value collapsing to `c_v²·(Σσ_u − 2) + c_u²·(Σσ_v − 2) ≤ 0`. This
strengthens the all-degree-`≤ 4` far-pair law to every usable profile.
`spread_fat_close` discharges any fat `ResidualCore` graph carrying such a pair,
so `HasUsableFarPair` reduces the open input to the compact boundary only. -/

/-- **`L-USABLE-FAR` — usable clean far pair fires.**  Two vertices `u ≠ v` at
distance `≥ 4` (not adjacent, no common neighbour `hcap`, and no `N(u)`–`N(v)`
edge `hfar`) in a graph of minimum degree `≥ 3`, both of whose `σ`-sums are usable
(`sigS ≤ 2`), certify `algConn G ≤ 2`.

Instance of the cross-free slot certificate `algConn_le_two_of_slot_far_pair_both`
(`GeneralFatSide`): with no cross edges the slot value is
`c_v²·(Σσ_u − 2) + c_u²·(Σσ_v − 2)`, which is `≤ 0` precisely when both ends are
usable.  Strengthens `algConn_le_two_of_far_pair_deg4` from the `Δ ≤ 4` ball to
*every* usable degree profile; tight at the `(5,5,5)` σ-tie (value `= 2`). -/
theorem algConn_le_two_of_usable_far_pair [Nonempty V] (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hcap : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    (hfar : ∀ w w' : V, G.Adj u w → G.Adj v w' → ¬G.Adj w w')
    (hmin : ∀ w : V, 3 ≤ G.degree w)
    (hu : sigS G u ≤ 2) (hv : sigS G v ≤ 2) :
    algConn G ≤ 2 :=
  algConn_le_two_of_slot_far_pair_both G u v hne huv hcap hmin hfar hu hv

/-! ## The `HasUsableFarPair` packaging + spread closer -/

/-- **A usable clean far pair exists.**  `G` has two vertices at distance `≥ 4`
(combinatorially: `u ≠ v`, `¬Adj u v`, no common neighbour, no `N(u)`–`N(v)` edge)
each of which is `σ`-usable.  This is the exact *spread* witness: present on every
diameter-`≥ 4` "buried" world and absent on every diameter-`3` compact cell
inhabitant. -/
def HasUsableFarPair (G : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ ¬G.Adj u v ∧ (∀ w : V, ¬(G.Adj u w ∧ G.Adj v w)) ∧
    (∀ w w' : V, G.Adj u w → G.Adj v w' → ¬G.Adj w w') ∧
    sigS G u ≤ 2 ∧ sigS G v ≤ 2

/-- A usable clean far pair closes the graph (given `δ ≥ 3`). -/
theorem hasUsableFarPair_algConn_le_two [Nonempty V] (G : SimpleGraph V)
    (hmin : ∀ w : V, 3 ≤ G.degree w) (h : HasUsableFarPair G) : algConn G ≤ 2 := by
  obtain ⟨u, v, hne, huv, hcap, hfar, hu, hv⟩ := h
  exact algConn_le_two_of_usable_far_pair G u v hne huv hcap hfar hmin hu hv

/-! ## σ-profile suppression lemmas

Sharp bounds on the σ-sum `sigS G u = Σ_{w∈N(u)} σ(deg w)` in a min-degree-3
world: `usable_deg3_of_light` (a degree-3 vertex with all neighbours of degree
`≤ 5` is usable) and `nonusable_deg3_structure` (a non-usable degree-3 vertex has
all three neighbours of degree `≥ 4`, one of degree `≥ 6`, and two of degree
`≥ 5`). -/

/-! ### σ arithmetic on the profile intervals -/

/-- σ is monotone on `d ≥ 3` (restatement of `sigma_le_of_le` in the
frontier-facing name). -/
theorem sigma_mono {d e : ℕ} (hd : 3 ≤ d) (hde : d ≤ e) : sigma d ≤ sigma e :=
  sigma_le_of_le hd hde

end ACMax

/-! ## The parametric compact-covering theorem

On the compact cell (`¬HasUsableFarPair G`), every vertex outside the radius-3
ball around a usable vertex `u₀` is non-usable. Non-usable light (degree `≤ 4`)
vertices each have a heavy neighbour, so number at most `5·X`, and the heavy
vertices number at most `X`, where `X = ∑_{deg v ≥ 5} (deg v − 4)` is the total
degree excess. Since every degree is at most `4 + X`, the radius-3 ball gives the
covering bound `n ≤ 1 + (4+X) + (4+X)² + (4+X)³ + 6·X` (`compact_covering`): a
compact `ResidualCore` world is finite in `n` for each fixed excess `X`. -/

namespace ACMax

open scoped Classical
open Finset

variable {n : ℕ}

/-- The **total degree excess** `X = ∑_{deg v ≥ 5} (deg v − 4)` (ℕ-valued;
the truncated subtraction is exact since every summand has degree ≥ 5). -/
noncomputable def excessX (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => 5 ≤ G.degree v), (G.degree v - 4)

/-- The **radius-3 combinatorial ball** around `u₀`: `u₀` together with its
neighbours, second neighbours, and third neighbours. -/
noncomputable def closeSet (G : SimpleGraph (Fin n)) (u₀ : Fin n) : Finset (Fin n) :=
  insert u₀ (G.neighborFinset u₀
    ∪ (G.neighborFinset u₀).biUnion (fun w => G.neighborFinset w)
    ∪ ((G.neighborFinset u₀).biUnion (fun w => G.neighborFinset w)).biUnion
        (fun w => G.neighborFinset w))

/-- The centre is in the ball. -/
theorem mem_closeSet_self (G : SimpleGraph (Fin n)) (u₀ : Fin n) :
    u₀ ∈ closeSet G u₀ := by
  unfold closeSet
  exact Finset.mem_insert_self _ _

/-- A neighbour of `u₀` is in the ball. -/
theorem mem_closeSet_of_adj (G : SimpleGraph (Fin n)) {u₀ v : Fin n}
    (h : G.Adj u₀ v) : v ∈ closeSet G u₀ := by
  unfold closeSet
  exact Finset.mem_insert_of_mem <| Finset.mem_union_left _ <|
    Finset.mem_union_left _ <| (SimpleGraph.mem_neighborFinset G u₀ v).mpr h

/-- A second neighbour of `u₀` is in the ball. -/
theorem mem_closeSet_of_adj_adj (G : SimpleGraph (Fin n)) {u₀ w v : Fin n}
    (h1 : G.Adj u₀ w) (h2 : G.Adj w v) : v ∈ closeSet G u₀ := by
  unfold closeSet
  exact Finset.mem_insert_of_mem <| Finset.mem_union_left _ <|
    Finset.mem_union_right _ <| Finset.mem_biUnion.mpr
      ⟨w, (SimpleGraph.mem_neighborFinset G u₀ w).mpr h1,
        (SimpleGraph.mem_neighborFinset G w v).mpr h2⟩

/-- A third neighbour of `u₀` is in the ball. -/
theorem mem_closeSet_of_adj_adj_adj (G : SimpleGraph (Fin n)) {u₀ w x v : Fin n}
    (h1 : G.Adj u₀ w) (h2 : G.Adj w x) (h3 : G.Adj x v) : v ∈ closeSet G u₀ := by
  unfold closeSet
  exact Finset.mem_insert_of_mem <| Finset.mem_union_right _ <|
    Finset.mem_biUnion.mpr
      ⟨x, Finset.mem_biUnion.mpr
          ⟨w, (SimpleGraph.mem_neighborFinset G u₀ w).mpr h1,
            (SimpleGraph.mem_neighborFinset G w x).mpr h2⟩,
        (SimpleGraph.mem_neighborFinset G x v).mpr h3⟩

/-- **Vertices outside the ball are far**: `v ∉ closeSet G u₀` yields the four
combinatorial distance-`≥ 4` conditions of a clean far pair. -/
theorem far_of_not_mem_closeSet (G : SimpleGraph (Fin n)) (u₀ v : Fin n)
    (hv : v ∉ closeSet G u₀) :
    v ≠ u₀ ∧ ¬G.Adj u₀ v ∧ (∀ w, ¬(G.Adj u₀ w ∧ G.Adj v w)) ∧
      (∀ w w', G.Adj u₀ w → G.Adj v w' → ¬G.Adj w w') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact hv (mem_closeSet_self G v)
  · intro h
    exact hv (mem_closeSet_of_adj G h)
  · rintro w ⟨h1, h2⟩
    exact hv (mem_closeSet_of_adj_adj G h1 h2.symm)
  · intro w w' h1 h2 h3
    exact hv (mem_closeSet_of_adj_adj_adj G h1 h3 h2.symm)

/-- **On the compact cell, far vertices are non-usable**: with no usable far
pair and `u₀` usable, every vertex outside the ball has `sigS > 2`. -/
theorem nonusable_of_far (G : SimpleGraph (Fin n))
    (hcpt : ¬HasUsableFarPair G) (u₀ : Fin n) (hu₀ : sigS G u₀ ≤ 2)
    (v : Fin n) (hv : v ∉ closeSet G u₀) :
    2 < sigS G v := by
  by_contra h
  push Not at h
  obtain ⟨hne, hadj, hcap, hfar⟩ := far_of_not_mem_closeSet G u₀ v hv
  exact hcpt ⟨u₀, v, hne.symm, hadj, hcap, hfar, hu₀, h⟩

/-- **Non-usable light vertices see a heavy vertex**: if `deg v ≤ 4` and
`sigS v > 2`, some neighbour has degree ≥ 5 (else all `σ`-terms are ≤ 1/2 and
the sum is ≤ 4·(1/2) = 2). -/
theorem nonusable_light_has_heavy_nbr (G : SimpleGraph (Fin n))
    (h3 : ∀ w, 3 ≤ G.degree w) (v : Fin n) (hd : G.degree v ≤ 4)
    (h : 2 < sigS G v) :
    ∃ w ∈ G.neighborFinset v, 5 ≤ G.degree w := by
  by_contra hno
  push Not at hno
  have hterm : ∀ w ∈ G.neighborFinset v, sigma (G.degree w) ≤ (1 : ℝ) / 2 := by
    intro w hw
    have h4 : G.degree w ≤ 4 := by have := hno w hw; omega
    calc sigma (G.degree w) ≤ sigma 4 := sigma_mono (h3 w) h4
      _ = 1 / 2 := sigma_four
  have hb : sigS G v ≤ 2 := by
    calc sigS G v
        = ∑ w ∈ G.neighborFinset v, sigma (G.degree w) := by rw [sigS]
      _ ≤ (G.neighborFinset v).card • ((1 : ℝ) / 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (G.degree v : ℝ) * (1 / 2) := by
          rw [nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ 4 * (1 / 2) := by
          have h4 : (G.degree v : ℝ) ≤ 4 := by exact_mod_cast hd
          linarith
      _ = 2 := by norm_num
  linarith

/-- **The non-usable light population is at most `5·X`**: each such vertex is a
neighbour of a heavy vertex, and `∑_{heavy w} deg w ≤ 5·∑_{heavy w} (deg w − 4)`. -/
theorem card_nonusable_light_le (G : SimpleGraph (Fin n))
    (h3 : ∀ w, 3 ≤ G.degree w) :
    (Finset.univ.filter (fun v : Fin n => G.degree v ≤ 4 ∧ 2 < sigS G v)).card
      ≤ 5 * excessX n G := by
  have hsub : Finset.univ.filter (fun v : Fin n => G.degree v ≤ 4 ∧ 2 < sigS G v)
      ⊆ (Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w)).biUnion
          (fun w => G.neighborFinset w) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨w, hw, hw5⟩ := nonusable_light_has_heavy_nbr G h3 v hv.1 hv.2
    refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hw5
    · rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      exact hw.symm
  calc (Finset.univ.filter (fun v : Fin n => G.degree v ≤ 4 ∧ 2 < sigS G v)).card
      ≤ ((Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w)).biUnion
          (fun w => G.neighborFinset w)).card := Finset.card_le_card hsub
    _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w),
          (G.neighborFinset w).card := Finset.card_biUnion_le
    _ = ∑ w ∈ Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w),
          G.degree w :=
        Finset.sum_congr rfl (fun w _ => SimpleGraph.card_neighborFinset_eq_degree G w)
    _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w),
          5 * (G.degree w - 4) :=
        Finset.sum_le_sum (fun w hw => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          omega)
    _ = 5 * excessX n G := by rw [excessX, Finset.mul_sum]


end ACMax
