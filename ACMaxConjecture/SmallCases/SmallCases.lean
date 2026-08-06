import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.Reductions
import ACMaxConjecture.Spectral.AlgConnK2

/-!
# Small cases `n = 4 … 20` — the per-order base of the ACMAX conjecture

This chapter proves Kolokolnikov's Conjecture 1.5 for every fixed order `4 ≤ n ≤ 20`:
`K_{2,n-2}` attains algebraic connectivity `2`, and every graph on `Fin n` with `2(n-2)`
edges has `algConn G ≤ 2`.  Each order is packaged as a theorem
`acmax_conjecture_<n>` (`acmax_conjecture_four … acmax_conjecture_twenty`); this entry
module supplies `n = 4` and the chapter overview, and each larger order lives in its own
`CaseN<n>.lean` (with a `N<n>/` subdirectory of certificate machinery from `n = 12` on).

## Role in the general theorem

These orders are the base of the whole development.  `Counting/Windows.lean` consumes them
directly at the `n ≤ 20` branch of `acmax_conjecture_narrow`: the per-order theorems discharge
every order up to `20`, while the moat/starved-census machinery handles the `21 ≤ n ≤ 49`
window and the import-free large-`n` kills take over above it.  There is no spectral or
eigenvector computation anywhere below `n = 21`; every order closes with an explicit test
vector or a combinatorial cut certificate fed through Courant–Fischer.

## Common architecture

For each order the bound `algConn G ≤ 2` is exhibited by a witness `x ⊥ 𝟙` with
`xᵀ L x ≤ 2‖x‖²` (`Spectral/`).  Two witness families suffice:
* **test vectors** — a single low-degree vertex (`δ ≤ 2`,
  `algConn_le_two_of_low_degree_vertex`) or an induced `2K₂` (`algConn_le_two_of_ind_2K2`);
* **cut certificates** (`Cuts/`) — balanced, weighted and signed `±1` cuts, together with the
  good-`triangle` / `C₄` / `K_{2,3}` sparse cuts.

From `n = 12` on, the `δ ≥ 3` residual (a triangle-free graph whose degree-3 subgraph has an
isolated vertex) is closed by a per-order **TwinCert development** (`N<n>/`).  These share one
paradigm: split on the hub set `Hub = {v : 4 ≤ deg v}` and on the `M`-edge structure of the
degree-3 subgraph, then discharge each regime by a **twin-signed cut** — a `±1` cut `P/N` built
from an `M`-isolated degree-3 twin, two of its degree-4 hubs, and an aligned `P₃` — supplied by
`exists_twin_signed_cert_<n>`.  The alignment and the existence of the certificate are forced by
hub dichotomies (two-hub / two-twin / single-vertex / hub-triangle configurations) whose
difficulty grows sharply with `n` as the handshake slack `∑ deg − 3n` shrinks.

## Per-order map (distinctive difficulty)

* `n = 4`  (this file) — `K_{2,2}`; `4 < 6` edges give a non-adjacent pair of degree-sum `≤ 4`.
* `n = 5`  (`CaseN5`) — complement count: `Gᶜ` (`4` edges) has an edge of degree-sum `≥ 4`.
* `n = 6, 7` (`CaseN6N7`) — uniform low-degree vertex (`2·2(n-2) < 3n` forces `δ ≤ 2`).
* `n = 8`  (`CaseN8`) — first `δ ≥ 3` order; `3`-regular, closed by a balanced cut.
* `n = 9`  (`CaseN9`) — where the `±1`-cut method provably fails; induced `2K₂` on `[4,3⁸]`.
* `n = 10` (`CaseN10`) — `[4,4,3⁸]`; a degree-sparse triangle or an induced `2K₂`.
* `n = 11` (`CaseN11`) — first isolated-degree-3 residual; the dedicated `2K₂`-free cut.
* `n = 12` (`N12/`) — first TwinCert order; sparse-hub residual via a constructed twin signed cut.
* `n = 13` (`N13/`) — `e(M)` case-split; keystone: `M` is a dominating edge or a `C₅`.
* `n = 14` (`N14/`) — the two-hub / three-way single-vertex ∨ two-twin ∨ two-hub dichotomy.
* `n = 15` (`N15/`) — needs a 4th cut: the hub-triangle (three mutually-adjacent hubs).
* `n = 16` (`N16/`) — good-`C₄` threshold falls to `≤ 14` (share `≤ 1`), collapsing a cluster.
* `n = 17` (`N17/`) — excess-9 boundary (`60 = 3·20`, no slack); cherry corners + a Mantel step.
* `n = 18` (`N18/`) — hardest; a 5th star-triangle construction and the rigid octahedron structure.
* `n = 19` (`N19/`) — deg-5 rich/poor `Z`-hub dispatch over the octahedron poor-layer certificates.
* `n = 20` (`N20/`) — the frontier order; good-triangle threshold `≤ 11`, same octahedron toolbox.

Reference: T. Kolokolnikov, *Maximizing algebraic connectivity for certain families of graphs*,
arXiv:1412.6147, Conjecture 1.5.
-/

namespace ACMax

open scoped Classical

/-- Upper bound clause for `n = 4`. -/
theorem upperBound_four (G : SimpleGraph (Fin 4)) (hm : G.edgeFinset.card = 4) :
    algConn G ≤ 2 := by
  classical
  -- `G` is not the complete graph, since `⊤` on `Fin 4` has `6` edges.
  have hne : ∃ u v : Fin 4, u ≠ v ∧ ¬ G.Adj u v := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    -- If every distinct pair is adjacent, each vertex has degree `3`, so the
    -- degree sum is `12`; but the handshake lemma forces it to be `2 * 4 = 8`.
    have hdeg3 : ∀ w : Fin 4, G.degree w = 3 := by
      intro w
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      have hnb : G.neighborFinset w = Finset.univ.erase w := by
        ext z
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ,
          and_true]
        constructor
        · intro hz; exact (G.ne_of_adj hz).symm
        · intro hz; exact h w z (Ne.symm hz)
      rw [hnb, Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ,
        Fintype.card_fin]
    have hsum : ∑ w : Fin 4, G.degree w = 12 := by simp [hdeg3]
    have hhand := G.sum_degrees_eq_twice_card_edges
    rw [hsum, hm] at hhand
    norm_num at hhand
  obtain ⟨u, v, huv, hadj⟩ := hne
  apply algConn_le_two_of_nonadj_pair G u v huv hadj
  -- Each endpoint of the non-adjacent pair has degree `≤ 2`.
  have hdu : G.degree u ≤ 2 := by
    have hsub : G.neighborFinset u ⊆ Finset.univ \ {u, v} := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, true_and, not_or]
      refine ⟨?_, ?_⟩
      · intro hwu; rw [hwu] at hw; exact G.irrefl hw
      · intro hwv; rw [hwv] at hw; exact hadj hw
    calc G.degree u = (G.neighborFinset u).card := rfl
      _ ≤ (Finset.univ \ {u, v} : Finset (Fin 4)).card := Finset.card_le_card hsub
      _ ≤ 2 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        have : ({u, v} : Finset (Fin 4)).card = 2 := Finset.card_pair huv
        omega
  have hdv : G.degree v ≤ 2 := by
    have hsub : G.neighborFinset v ⊆ Finset.univ \ {u, v} := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, true_and, not_or]
      refine ⟨?_, ?_⟩
      · intro hwu; rw [hwu] at hw; exact hadj hw.symm
      · intro hwv; rw [hwv] at hw; exact G.irrefl hw
    calc G.degree v = (G.neighborFinset v).card := rfl
      _ ≤ (Finset.univ \ {u, v} : Finset (Fin 4)).card := Finset.card_le_card hsub
      _ ≤ 2 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        have : ({u, v} : Finset (Fin 4)).card = 2 := Finset.card_pair huv
        omega
  omega

/-- The full ACMAX conjecture for `n = 4` (`K_{2,2}` is the maximizer; bound `2`). -/
theorem acmax_conjecture_four :
    algConn (completeBipartiteGraph (Fin 2) (Fin 2)) = 2 ∧
      ∀ G : SimpleGraph (Fin 4), G.edgeFinset.card = 4 → algConn G ≤ 2 := by
  refine ⟨?_, fun G hm => upperBound_four G hm⟩
  exact algConn_completeBipartite_two 4 (by norm_num)

end ACMax
