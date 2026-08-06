import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.WeightedCut
import ACMaxConjecture.Cuts.TriangleFree2K2
import ACMaxConjecture.InternalEdgesEven
import ACMaxConjecture.TwoRegular2K2

/-!
# The no-`2K₂` cut bound for `n = 11`

The single remaining piece to close `n = 11`: a connected, no-good-triangle graph on `Fin 11`
with `δ ≥ 3`, `∑ deg = 36` (so degree sequence `[4,4,4,3⁸]`) whose degree-3 subgraph contains
**no** induced `2K₂` is certified by the weighted cut

  `A = (degree-4 vertices) ∪ (degree-3 vertices adjacent to ≥ 2 degree-4 vertices)`.

Writing `t = |Aᶜ|` (degree-3 vertices with ≤ 1 degree-4 neighbour) and
`S = ∑_{v ∈ Aᶜ} |N(v) ∩ Aᶜ| = 2·e(Aᶜ)`, one has `cut(A) = 3t − S`, so the weighted-cut inequality
`11·cut(A) ≤ 2|A||Aᶜ|` reduces to the edge-density bound `11·S ≥ t(11 + 2t)`.  The whole argument,
that bound included, is carried out here from first principles — no external enumeration and no
`sorry`.  The `2K₂`-free degree-3 subgraph `D = Hubᶜ` is triangle-free, so the induced-`2K₂`
extraction `exists_induced_2K2_of_triangleFree_smalldeg` forces an isolated `D`-vertex, pinning
`|Hub| = 3` and `2 ≤ t ≤ 7`; every `Aᶜ`-vertex then has `≥ 2` internal neighbours (`S ≥ 2t`), and
for `t ∈ {6, 7}` the parity of `S` together with `exists_2K2_of_two_regular_triangleFree` forces
one extra internal edge (`S ≥ 2t + 2`).

`algConn_le_two_of_2K2free_cut` is the resulting certificate; it is verified axiom-clean.
-/

namespace ACMax

open scoped Classical

/-- No-`2K₂` residual cut certificate for `n = 11`. -/
theorem algConn_le_two_of_2K2free_cut (G : SimpleGraph (Fin 11))
    (hm : G.edgeFinset.card = 18) (h3 : ∀ v : Fin 11, 3 ≤ G.degree v)
    (_hconn : G.Connected)
    (hT : ¬ ∃ x y z : Fin 11, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hno2k2 : ¬ ∃ a b c d : Fin 11, ({a, b, c, d} : Finset (Fin 11)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) :
    algConn G ≤ 2 := by
  let : DecidableEq (Fin 11) := fun a b => Classical.propDecidable (a = b)
  -- `∑ deg = 36` from `m = 18`.
  have hsum : ∑ v : Fin 11, G.degree v = 36 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  -- The hubs (degree `≥ 4`) and the cut set `A`.
  set Hub : Finset (Fin 11) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  set A : Finset (Fin 11) :=
    Hub ∪ Finset.univ.filter
      (fun v => G.degree v = 3 ∧ 2 ≤ (G.neighborFinset v ∩ Hub).card) with hAdef
  -- Membership characterizations.
  have hmemHub : ∀ v : Fin 11, v ∈ Hub ↔ 4 ≤ G.degree v := by
    intro v; rw [hHubdef]; simp
  have hmemA : ∀ v : Fin 11, v ∈ A ↔
      (4 ≤ G.degree v) ∨ (G.degree v = 3 ∧ 2 ≤ (G.neighborFinset v ∩ Hub).card) := by
    intro v; rw [hAdef, Finset.mem_union, hmemHub]; simp [hHubdef]
  have hmemAc : ∀ v : Fin 11, v ∈ Aᶜ ↔
      G.degree v = 3 ∧ (G.neighborFinset v ∩ Hub).card ≤ 1 := by
    intro v
    rw [Finset.mem_compl, hmemA]
    have hd := h3 v
    constructor
    · intro hv
      push Not at hv
      obtain ⟨h1, h2⟩ := hv
      have : G.degree v = 3 := by omega
      exact ⟨this, by have := h2 this; omega⟩
    · rintro ⟨hdeg, hk⟩
      push Not
      refine ⟨by omega, fun _ => by omega⟩
  -- Every vertex of `Aᶜ` has degree exactly `3`.
  have hAcdeg : ∀ v : Fin 11, v ∈ Aᶜ → G.degree v = 3 := fun v hv => ((hmemAc v).mp hv).1
  -- `Hub` has at most three vertices.
  have hnotHubDeg : ∀ v : Fin 11, v ∉ Hub → G.degree v = 3 := by
    intro v hv
    rw [hmemHub] at hv
    have := h3 v; omega
  have hHubcompl : Hub.card + Hubᶜ.card = 11 := by
    have h := Finset.card_add_card_compl Hub; rwa [Fintype.card_fin] at h
  have hHubc : ∑ v ∈ Hubᶜ, G.degree v = 3 * Hubᶜ.card := by
    rw [Finset.sum_congr rfl (fun v hv => hnotHubDeg v (Finset.mem_compl.mp hv)),
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hHubpart : ∑ v ∈ Hub, G.degree v + ∑ v ∈ Hubᶜ, G.degree v = 36 := by
    rw [Finset.sum_add_sum_compl]; exact hsum
  have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
    have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
    have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul, mul_comm] using h
  -- `∑_{Hub} deg = 3 + 3·|Hub|`, hence `1 ≤ |Hub| ≤ 3`.
  have hHubsum : ∑ v ∈ Hub, G.degree v = 3 + 3 * Hub.card := by omega
  have hHubcard : Hub.card ≤ 3 := by omega
  have hHubpos : 1 ≤ Hub.card := by
    rcases Nat.eq_zero_or_pos Hub.card with h0 | h1
    · rw [h0] at hHubsum
      have : ∑ v ∈ Hub, G.degree v = 0 := by
        rw [Finset.card_eq_zero.mp h0]; simp
      omega
    · exact h1
  -- `D = Hubᶜ` are the degree-3 vertices; `|D| ≥ 8`.
  have hDcard : 8 ≤ Hubᶜ.card := by omega
  -- Indicator form of an in-set neighbourhood count.
  have hcardInter : ∀ (a : Fin 11) (C : Finset (Fin 11)),
      (G.neighborFinset a ∩ C).card = ∑ c ∈ C, (if G.Adj a c then 1 else 0) := by
    intro a C
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun c _ => by simp only [SimpleGraph.mem_neighborFinset])
  -- Symmetric cross-count between two sets.
  have hcross : ∀ (B C : Finset (Fin 11)),
      ∑ a ∈ B, (G.neighborFinset a ∩ C).card
        = ∑ c ∈ C, (G.neighborFinset c ∩ B).card := by
    intro B C
    simp_rw [hcardInter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
      (fun a _ => by rw [SimpleGraph.adj_comm]))
  -- The cut equals the `Aᶜ`-side count of cross edges.
  set t : ℕ := Aᶜ.card with htdef
  set S : ℕ := ∑ v ∈ Aᶜ, (G.neighborFinset v ∩ Aᶜ).card with hSdef
  set cut : ℕ := ∑ a ∈ A, (G.neighborFinset a \ A).card with hcutdef
  have hcutAc : cut = ∑ v ∈ Aᶜ, (G.neighborFinset v ∩ A).card := by
    rw [hcutdef]
    have hsd : ∀ a ∈ A, (G.neighborFinset a \ A).card = (G.neighborFinset a ∩ Aᶜ).card := by
      intro a _; rw [Finset.sdiff_eq_inter_compl]
    rw [Finset.sum_congr rfl hsd]
    exact hcross A Aᶜ
  -- `cut + S = 3 t`: each `Aᶜ` vertex has degree 3, split between `A` and `Aᶜ`.
  have hcutS : cut + S = 3 * t := by
    have hterm : ∀ v ∈ Aᶜ,
        (G.neighborFinset v ∩ A).card + (G.neighborFinset v ∩ Aᶜ).card = 3 := by
      intro v hv
      have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset v) A
      rw [Finset.sdiff_eq_inter_compl] at hpart
      rw [hpart, SimpleGraph.card_neighborFinset_eq_degree, hAcdeg v hv]
    rw [hcutAc, hSdef, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm,
      Finset.sum_const, smul_eq_mul, htdef, mul_comm]
  -- The structural edge-density bound.  Here `S = ∑_{v ∈ Aᶜ} |N v ∩ Aᶜ| = 2·e(Aᶜ)` is twice the
  -- number of edges internal to `Aᶜ`, and `t = |Aᶜ|`.  The required inequality `11·S ≥ 11t + 2t²`
  -- is exactly the weighted-cut bound `11·cut(A) ≤ 2|A||Aᶜ|` rewritten via `cut = 3t − S`.
  --
  -- It is proved BELOW from first principles.  The "no-`2K₂` ⇒ dense-`Aᶜ`" skeleton:
  --   * the degree-3 subgraph `D = Hubᶜ` is triangle-free (from `hT`, see `hDtri`) with `|D| = 8`;
  --     `exists_induced_2K2_of_triangleFree_smalldeg`, whose `2K₂` conclusion is barred by
  --     `hno2k2`, then forces a degree-3 vertex `w` isolated in `D` (`hiso`/`hwiso`).  Its three
  --     neighbours are all hubs (`hwHub`), forcing `Hub.card = 3` (`hHub3`); Hub–`D` edge counting
  --     gives `2 ≤ t` (`hge2`) and the isolated `w ∈ A` gives `t ≤ 7` (`htle`).
  --   * the density estimate `11t + 2t² ≤ 11S` (`hdensity`) then follows: every `Aᶜ`-vertex has
  --     `≥ 2` internal neighbours (`hperv`, giving `S ≥ 2t`), and for `t ∈ {6, 7}` the evenness of
  --     `S` plus "`2`-regular triangle-free ⇒ induced `2K₂`" force one extra edge (`S ≥ 2t + 2`).
  -- `D = Hubᶜ` is exactly the degree-3 vertex set.
  have hmemD : ∀ v : Fin 11, v ∈ Hubᶜ ↔ G.degree v = 3 := by
    intro v
    rw [Finset.mem_compl, hmemHub]
    have := h3 v; omega
  -- In-`D` degrees are at most `3` (since total degree is `3`).
  have hDmax : ∀ a ∈ Hubᶜ, (G.neighborFinset a ∩ Hubᶜ).card ≤ 3 := by
    intro a ha
    calc (G.neighborFinset a ∩ Hubᶜ).card
        ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
      _ = G.degree a := G.card_neighborFinset_eq_degree a
      _ = 3 := (hmemD a).mp ha
  -- `D` is triangle-free: a triangle of degree-3 vertices has degree-sum `9 ≤ 10` (a good triangle).
  have hDtri : ∀ a ∈ Hubᶜ, ∀ b ∈ Hubᶜ, ∀ c ∈ Hubᶜ,
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) := by
    rintro a ha b hb c hc ⟨hab, hbc, hac⟩
    refine hT ⟨a, b, c, G.ne_of_adj hab, G.ne_of_adj hbc, G.ne_of_adj hac,
      hab, hbc, hac, ?_⟩
    have da := (hmemD a).mp ha
    have db := (hmemD b).mp hb
    have dc := (hmemD c).mp hc
    omega
  -- There is a degree-3 vertex isolated within `D`: otherwise every `D`-vertex has an in-`D`
  -- neighbour and `exists_induced_2K2_of_triangleFree_smalldeg` produces an induced `2K₂` on
  -- degree-3 vertices, contradicting `hno2k2`.
  have hiso : ∃ w ∈ Hubᶜ, (G.neighborFinset w ∩ Hubᶜ).card = 0 := by
    by_contra hcon
    push Not at hcon
    have hmin : ∀ a ∈ Hubᶜ, 1 ≤ (G.neighborFinset a ∩ Hubᶜ).card := by
      intro a ha; have := hcon a ha; omega
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hcard4, hab, hcd, hac, had, hbc, hbd⟩ :=
      exists_induced_2K2_of_triangleFree_smalldeg G Hubᶜ hDtri hmin hDmax hDcard
    refine hno2k2 ⟨a, b, c, d, ?_, (hmemD a).mp ha, (hmemD b).mp hb,
      (hmemD c).mp hc, (hmemD d).mp hd, hab, hcd, hac, had, hbc, hbd⟩
    convert hcard4 using 2
    ext x; simp
  obtain ⟨w, hwD, hwiso⟩ := hiso
  -- The isolated vertex `w` has all three of its neighbours in `Hub`, so `|Hub| ≥ 3`, forcing
  -- `Hub.card = 3`.
  have hwHub : (G.neighborFinset w ∩ Hub).card = 3 := by
    have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset w) Hub
    rw [Finset.sdiff_eq_inter_compl] at hpart
    rw [hwiso, SimpleGraph.card_neighborFinset_eq_degree, (hmemD w).mp hwD] at hpart
    omega
  have hHub3 : Hub.card = 3 := by
    have h1 : (G.neighborFinset w ∩ Hub).card ≤ Hub.card :=
      Finset.card_le_card Finset.inter_subset_right
    omega
  -- The isolated vertex `w` is adjacent to all three hubs, hence has `≥ 2` hub-neighbours, so
  -- `w ∈ A` (in fact `w ∉ Aᶜ`); thus `Aᶜ ⊆ Hubᶜ \ {w}` and `t ≤ 7`.
  have hwA : w ∈ A := by
    rw [hmemA]; exact Or.inr ⟨(hmemD w).mp hwD, by have := hwHub; omega⟩
  have hwnAc : w ∉ Aᶜ := by rw [Finset.mem_compl]; exact fun h => h hwA
  have htle : t ≤ 7 := by
    rw [htdef]
    have hsub : Aᶜ ⊆ Hubᶜ.erase w := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro rfl; exact hwnAc hx
      · rw [Finset.mem_compl, hmemHub]
        have := (hmemAc x).mp hx; omega
    calc Aᶜ.card ≤ (Hubᶜ.erase w).card := Finset.card_le_card hsub
      _ = Hubᶜ.card - 1 := Finset.card_erase_of_mem hwD
      _ ≤ 7 := by omega
  -- `Hubᶜ.card = 8` (`= 11 − 3`).
  have hDcard8 : Hubᶜ.card = 8 := by omega
  -- `Aᶜ ⊆ Hubᶜ` (every `Aᶜ` vertex has degree 3).
  have hAcsubD : Aᶜ ⊆ Hubᶜ := by
    intro x hx
    rw [Finset.mem_compl, hmemHub]
    have := (hmemAc x).mp hx; omega
  -- Lower bound `2 ≤ t`.  The `8 − t` vertices of `Hubᶜ \ Aᶜ` lie in `A`, hence each has
  -- `≥ 2` hub-neighbours, while the total hub–`D` incidence is `≤ ∑_{Hub} deg = 12`.
  have hge2 : 2 ≤ t := by
    have hsub : ∀ v ∈ Hubᶜ \ Aᶜ, 2 ≤ (G.neighborFinset v ∩ Hub).card := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      obtain ⟨hvD, hvAc⟩ := hv
      have hvA : v ∈ A := by simpa using hvAc
      have hdeg := (hmemD v).mp hvD
      rcases (hmemA v).mp hvA with h4 | ⟨_, h2⟩
      · omega
      · exact h2
    have hlow : 2 * (Hubᶜ \ Aᶜ).card
        ≤ ∑ v ∈ Hubᶜ \ Aᶜ, (G.neighborFinset v ∩ Hub).card := by
      have h := Finset.card_nsmul_le_sum (Hubᶜ \ Aᶜ)
        (fun v => (G.neighborFinset v ∩ Hub).card) 2 hsub
      simpa [smul_eq_mul, mul_comm] using h
    have hupp : ∑ v ∈ Hubᶜ \ Aᶜ, (G.neighborFinset v ∩ Hub).card
        ≤ ∑ v ∈ Hubᶜ, (G.neighborFinset v ∩ Hub).card :=
      Finset.sum_le_sum_of_subset Finset.sdiff_subset
    have htot : ∑ v ∈ Hubᶜ, (G.neighborFinset v ∩ Hub).card ≤ 12 := by
      rw [hcross Hubᶜ Hub]
      calc ∑ u ∈ Hub, (G.neighborFinset u ∩ Hubᶜ).card
          ≤ ∑ u ∈ Hub, (G.neighborFinset u).card :=
            Finset.sum_le_sum (fun u _ => Finset.card_le_card Finset.inter_subset_left)
        _ = ∑ u ∈ Hub, G.degree u :=
            Finset.sum_congr rfl (fun u _ => G.card_neighborFinset_eq_degree u)
        _ = 3 + 3 * Hub.card := hHubsum
        _ = 12 := by rw [hHub3]
    have hcardsdiff : (Hubᶜ \ Aᶜ).card + t = 8 := by
      rw [htdef, ← hDcard8]
      exact Finset.card_sdiff_add_card_eq_card hAcsubD
    omega
  -- The structural edge-density bound `11·S ≥ 11t + 2t²`, equivalently `e(Aᶜ) ≥ t(11+2t)/22`.
  --
  -- With the structure now in hand (`Hub.card = 3`, `2 ≤ t ≤ 7`, an isolated degree-3 vertex `w`
  -- adjacent to all three hubs), the "no-`2K₂` ⇒ dense-`Aᶜ`" estimate is proved in two steps:
  --   * every `Aᶜ` vertex has `≥ 2` neighbours inside `Aᶜ` (`hperv`): an `Aᶜ` vertex with `≤ 1`
  --     internal neighbour has a neighbour `p ∈ A ∩ D` adjacent to two hubs, and the degree-3 edge
  --     `{v,p}` extends to an induced `2K₂` on degree-3 vertices, contradicting `hno2k2`; this
  --     gives `S ≥ 2t`;
  --   * for `t ∈ {6, 7}` one further internal edge is forced (`S ≥ 2t + 2`, `hSge2`).
  -- The in-`D` degree sum is at least `12`: `∑_{D} deg_D = 24 − (hub–D edges) ≥ 24 − 12`.
  have hSatleast12 : 12 ≤ ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ Hubᶜ).card := by
    have hsumsplit : ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ Hub).card
        + ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ Hubᶜ).card = 24 := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ w ∈ Hubᶜ,
          (G.neighborFinset w ∩ Hub).card + (G.neighborFinset w ∩ Hubᶜ).card = 3 := by
        intro w hw
        have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset w) Hub
        rw [Finset.sdiff_eq_inter_compl] at hpart
        rw [hpart, SimpleGraph.card_neighborFinset_eq_degree, (hmemD w).mp hw]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
      omega
    have hhubD : ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ Hub).card ≤ 12 := by
      rw [hcross Hubᶜ Hub]
      calc ∑ u ∈ Hub, (G.neighborFinset u ∩ Hubᶜ).card
          ≤ ∑ u ∈ Hub, (G.neighborFinset u).card :=
            Finset.sum_le_sum (fun u _ => Finset.card_le_card Finset.inter_subset_left)
        _ = ∑ u ∈ Hub, G.degree u :=
            Finset.sum_congr rfl (fun u _ => G.card_neighborFinset_eq_degree u)
        _ = 3 + 3 * Hub.card := hHubsum
        _ = 12 := by rw [hHub3]
    omega
  -- Every `Aᶜ` vertex has `≥ 2` neighbours inside `Aᶜ`.  Suppose not: then `v` has a degree-3
  -- "leaf" neighbour `u` (`≥ 2` hubs, only `D`-neighbour `v`), and `C = insert v (N v ∩ D)`
  -- is a vertex cover of the degree-3 subgraph (any uncovered edge would extend `{v,u}` to an
  -- induced `2K₂`).  Counting `∑_{D} deg_D` against this cover yields `≤ 11 < 12`, contradiction.
  have hperv : ∀ v ∈ Aᶜ, 2 ≤ (G.neighborFinset v ∩ Aᶜ).card := by
    intro v hv
    by_contra hlt
    push Not at hlt
    have hv3 : G.degree v = 3 := ((hmemAc v).mp hv).1
    have hvHub : (G.neighborFinset v ∩ Hub).card ≤ 1 := ((hmemAc v).mp hv).2
    have hvD : v ∈ Hubᶜ := hAcsubD hv
    have hvsplit : (G.neighborFinset v ∩ Hub).card
        + (G.neighborFinset v ∩ Hubᶜ).card = 3 := by
      have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset v) Hub
      rw [Finset.sdiff_eq_inter_compl] at hpart
      rw [hpart, SimpleGraph.card_neighborFinset_eq_degree, hv3]
    have hdv3 : (G.neighborFinset v ∩ Hubᶜ).card ≤ 3 := hDmax v hvD
    have hZeq : (G.neighborFinset v ∩ Hubᶜ) ∩ Aᶜ = G.neighborFinset v ∩ Aᶜ := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hAcsubD]
    -- A degree-3 vertex `p` adjacent to `v` with `≥ 2` hub-neighbours has only `v` inside `D`.
    have hleaf : ∀ p, p ∈ G.neighborFinset v ∩ Hubᶜ → p ∉ Aᶜ →
        G.neighborFinset p ∩ Hubᶜ = {v} := by
      intro p hp hpAc
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hp
      obtain ⟨hvp, hpD⟩ := hp
      have hpA : p ∈ A := by
        by_contra h; exact hpAc (Finset.mem_compl.mpr h)
      have hp2hub : 2 ≤ (G.neighborFinset p ∩ Hub).card := by
        rcases (hmemA p).mp hpA with h4 | ⟨_, h2⟩
        · have := (hmemD p).mp hpD; omega
        · exact h2
      have hpsplit : (G.neighborFinset p ∩ Hub).card
          + (G.neighborFinset p ∩ Hubᶜ).card = 3 := by
        have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset p) Hub
        rw [Finset.sdiff_eq_inter_compl] at hpart
        rw [hpart, SimpleGraph.card_neighborFinset_eq_degree, (hmemD p).mp hpD]
      have hvin : v ∈ G.neighborFinset p ∩ Hubᶜ := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hvp.symm, hvD⟩
      have hcard1 : (G.neighborFinset p ∩ Hubᶜ).card = 1 := by
        have hpos := Finset.card_pos.mpr ⟨v, hvin⟩
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
      rw [ha] at hvin ⊢
      rw [Finset.mem_singleton] at hvin
      rw [hvin]
    -- A leaf neighbour `u` of `v` exists (since `< 2` of `v`'s `≥ 2` `D`-neighbours are in `Aᶜ`).
    have hUne : 0 < ((G.neighborFinset v ∩ Hubᶜ) \ Aᶜ).card := by
      have hcardsd := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ Hubᶜ) Aᶜ
      rw [hZeq] at hcardsd
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hUne
    rw [Finset.mem_sdiff] at hu
    obtain ⟨huNvD, huAc⟩ := hu
    have hu_leaf : G.neighborFinset u ∩ Hubᶜ = {v} := hleaf u huNvD huAc
    have huNv : G.Adj v u := by
      have := (Finset.mem_inter.mp huNvD).1
      rwa [SimpleGraph.mem_neighborFinset] at this
    have huD : u ∈ Hubᶜ := (Finset.mem_inter.mp huNvD).2
    set C : Finset (Fin 11) := insert v (G.neighborFinset v ∩ Hubᶜ) with hCdef
    have hmemC : ∀ x, x ∈ C ↔ x = v ∨ x ∈ G.neighborFinset v ∩ Hubᶜ := by
      intro x; rw [hCdef, Finset.mem_insert]
    have hCsub : C ⊆ Hubᶜ := by
      intro x hx
      rcases (hmemC x).mp hx with h | h
      · exact h ▸ hvD
      · exact (Finset.mem_inter.mp h).2
    have huC : u ∈ C := (hmemC u).mpr (Or.inr huNvD)
    -- `C` is a vertex cover of the degree-3 subgraph.
    have hcover : ∀ x, x ∈ Hubᶜ → ∀ y, y ∈ Hubᶜ → G.Adj x y → x ∈ C ∨ y ∈ C := by
      intro x hxD y hyD hxy
      by_contra hcon
      push Not at hcon
      obtain ⟨hxC, hyC⟩ := hcon
      have hxv : x ≠ v := fun h => hxC ((hmemC x).mpr (Or.inl h))
      have hyv : y ≠ v := fun h => hyC ((hmemC y).mpr (Or.inl h))
      have hxnv : ¬ G.Adj v x := fun h => hxC ((hmemC x).mpr (Or.inr (by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨h, hxD⟩)))
      have hynv : ¬ G.Adj v y := fun h => hyC ((hmemC y).mpr (Or.inr (by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨h, hyD⟩)))
      have hxu : ¬ G.Adj u x := by
        intro h
        have hxin : x ∈ G.neighborFinset u ∩ Hubᶜ := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨h, hxD⟩
        rw [hu_leaf, Finset.mem_singleton] at hxin
        exact hxv hxin
      have hyu : ¬ G.Adj u y := by
        intro h
        have hyin : y ∈ G.neighborFinset u ∩ Hubᶜ := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨h, hyD⟩
        rw [hu_leaf, Finset.mem_singleton] at hyin
        exact hyv hyin
      have hcard4 : ({v, u, x, y} : Finset (Fin 11)).card = 4 := by
        have e1 : v ≠ u := G.ne_of_adj huNv
        have e2 : v ≠ x := fun h => hxv h.symm
        have e3 : v ≠ y := fun h => hyv h.symm
        have e4 : u ≠ x := fun h => hxC ((hmemC x).mpr (Or.inr (h ▸ huNvD)))
        have e5 : u ≠ y := fun h => hyC ((hmemC y).mpr (Or.inr (h ▸ huNvD)))
        have e6 : x ≠ y := G.ne_of_adj hxy
        rw [Finset.card_insert_of_notMem (by simp [e1, e2, e3]),
            Finset.card_insert_of_notMem (by simp [e4, e5]),
            Finset.card_insert_of_notMem (by simp [e6]), Finset.card_singleton]
      refine hno2k2 ⟨v, u, x, y, ?_, hv3, (hmemD u).mp huD, (hmemD x).mp hxD,
        (hmemD y).mp hyD, huNv, hxy, hxnv, hynv, hxu, hyu⟩
      convert hcard4 using 2
      ext z; simp
    -- Refined cover: an uncovered vertex's `D`-neighbours lie in `N v ∩ Aᶜ`.
    have hcover2 : ∀ w, w ∈ Hubᶜ → w ∉ C →
        G.neighborFinset w ∩ Hubᶜ ⊆ G.neighborFinset v ∩ Aᶜ := by
      intro w hwD hwC z hz
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
      obtain ⟨hwz, hzD⟩ := hz
      have hzC : z ∈ C := (hcover w hwD z hzD hwz).resolve_left hwC
      have hzv : z ≠ v := by
        rintro rfl
        exact hwC ((hmemC w).mpr (Or.inr (by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨hwz.symm, hwD⟩)))
      have hzNv : z ∈ G.neighborFinset v ∩ Hubᶜ := ((hmemC z).mp hzC).resolve_left hzv
      have hzAc : z ∈ Aᶜ := by
        by_contra hzAc
        have hl := hleaf z hzNv hzAc
        have hwin : w ∈ G.neighborFinset z ∩ Hubᶜ := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨hwz.symm, hwD⟩
        rw [hl, Finset.mem_singleton] at hwin
        exact hwC ((hmemC w).mpr (Or.inl hwin))
      rw [Finset.mem_inter]
      exact ⟨(Finset.mem_inter.mp hzNv).1, hzAc⟩
    -- Counting the in-`D` degree sum against the cover.
    have hout : ∑ w ∈ Hubᶜ \ C, (G.neighborFinset w ∩ Hubᶜ).card
        ≤ 3 * (G.neighborFinset v ∩ Aᶜ).card := by
      have hcong : ∀ w ∈ Hubᶜ \ C,
          (G.neighborFinset w ∩ Hubᶜ).card
            = (G.neighborFinset w ∩ (G.neighborFinset v ∩ Aᶜ)).card := by
        intro w hw
        rw [Finset.mem_sdiff] at hw
        congr 1
        apply Finset.Subset.antisymm
        · intro z hz
          rw [Finset.mem_inter]
          exact ⟨(Finset.mem_inter.mp hz).1, hcover2 w hw.1 hw.2 hz⟩
        · intro z hz
          rw [Finset.mem_inter] at hz ⊢
          exact ⟨hz.1, hAcsubD (Finset.mem_inter.mp hz.2).2⟩
      rw [Finset.sum_congr rfl hcong]
      calc ∑ w ∈ Hubᶜ \ C, (G.neighborFinset w ∩ (G.neighborFinset v ∩ Aᶜ)).card
          ≤ ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ (G.neighborFinset v ∩ Aᶜ)).card :=
            Finset.sum_le_sum_of_subset Finset.sdiff_subset
        _ = ∑ z ∈ G.neighborFinset v ∩ Aᶜ, (G.neighborFinset z ∩ Hubᶜ).card :=
            hcross Hubᶜ (G.neighborFinset v ∩ Aᶜ)
        _ ≤ ∑ _z ∈ G.neighborFinset v ∩ Aᶜ, 3 :=
            Finset.sum_le_sum (fun z hz => hDmax z (hAcsubD (Finset.mem_inter.mp hz).2))
        _ = 3 * (G.neighborFinset v ∩ Aᶜ).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hvnotin : v ∉ G.neighborFinset v ∩ Hubᶜ := fun h => by
      have hAdj : G.Adj v v := by
        have := (Finset.mem_inter.mp h).1
        rwa [SimpleGraph.mem_neighborFinset] at this
      exact hAdj.ne rfl
    have hinner : ∑ w ∈ G.neighborFinset v ∩ Hubᶜ, (G.neighborFinset w ∩ Hubᶜ).card
        ≤ (G.neighborFinset v ∩ Hubᶜ).card + 2 * (G.neighborFinset v ∩ Aᶜ).card := by
      rw [← Finset.sum_inter_add_sum_sdiff (G.neighborFinset v ∩ Hubᶜ) Aᶜ
            (fun w => (G.neighborFinset w ∩ Hubᶜ).card)]
      have hAcpart : ∑ w ∈ (G.neighborFinset v ∩ Hubᶜ) ∩ Aᶜ,
          (G.neighborFinset w ∩ Hubᶜ).card ≤ 3 * (G.neighborFinset v ∩ Aᶜ).card := by
        calc ∑ w ∈ (G.neighborFinset v ∩ Hubᶜ) ∩ Aᶜ, (G.neighborFinset w ∩ Hubᶜ).card
            ≤ ∑ _w ∈ (G.neighborFinset v ∩ Hubᶜ) ∩ Aᶜ, 3 :=
              Finset.sum_le_sum (fun w hw =>
                hDmax w (Finset.mem_inter.mp (Finset.mem_inter.mp hw).1).2)
          _ = 3 * (G.neighborFinset v ∩ Aᶜ).card := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm, hZeq]
      have hleafpart : ∑ w ∈ (G.neighborFinset v ∩ Hubᶜ) \ Aᶜ,
          (G.neighborFinset w ∩ Hubᶜ).card = ((G.neighborFinset v ∩ Hubᶜ) \ Aᶜ).card := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl (fun w hw => ?_)
        rw [Finset.mem_sdiff] at hw
        rw [hleaf w hw.1 hw.2, Finset.card_singleton]
      have hcards := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ Hubᶜ) Aᶜ
      rw [hZeq] at hcards
      rw [hleafpart]
      omega
    have hinC : ∑ w ∈ C, (G.neighborFinset w ∩ Hubᶜ).card
        ≤ 2 * (G.neighborFinset v ∩ Hubᶜ).card + 2 * (G.neighborFinset v ∩ Aᶜ).card := by
      rw [hCdef, Finset.sum_insert hvnotin]
      linarith [hinner]
    have hsplitsum : ∑ w ∈ Hubᶜ \ C, (G.neighborFinset w ∩ Hubᶜ).card
        + ∑ w ∈ C, (G.neighborFinset w ∩ Hubᶜ).card
        = ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ Hubᶜ).card :=
      Finset.sum_sdiff hCsub
    omega
  -- `S ≥ 2t` from the per-vertex bound, closing `t ≤ 5`.
  have hSge : 2 * t ≤ S := by
    rw [hSdef, htdef]
    have h := Finset.card_nsmul_le_sum Aᶜ
      (fun v => (G.neighborFinset v ∩ Aᶜ).card) 2 hperv
    simpa [smul_eq_mul, mul_comm] using h
  have hdensity : 11 * t + 2 * t * t ≤ 11 * S := by
    rcases Nat.lt_or_ge t 6 with htlt | htge
    · have htle5 : t ≤ 5 := by omega
      have hsq : t * t ≤ 5 * t := Nat.mul_le_mul htle5 (le_refl t)
      rw [mul_assoc]
      generalize hq : t * t = q at hsq ⊢
      omega
    · -- `t ∈ {6, 7}`: the densest cases need one extra internal edge `S ≥ 2t + 2`.
      -- Write `S = 2t + N₃` where `N₃` counts the `Aᶜ` vertices of internal degree `3` (each `Aᶜ`
      -- vertex has internal degree `2` or `3` by `hperv` and `hAcdeg`).  `S = ∑_{Aᶜ}|N v ∩ Aᶜ|` is
      -- even (`hSeven`, twice the number of edges internal to `Aᶜ`), so `N₃ = S − 2t` is even.  If
      -- `Aᶜ` were `2`-regular (`N₃ = 0`) it would be a disjoint union of triangle-free cycles on
      -- `t ∈ {6, 7}` vertices, i.e. `C₆` or `C₇`, each containing two vertex-disjoint non-adjacent
      -- edges — an induced `2K₂` on degree-3 vertices barred by `hno2k2`, extracted by
      -- `exists_2K2_of_two_regular_triangleFree`.  Hence `N₃ ≥ 1`, and by parity `N₃ ≥ 2`, giving
      -- `S ≥ 2t + 2`.
      have hSge2 : 2 * t + 2 ≤ S := by
        have hSeven : Even S := by rw [hSdef]; exact ACMax.sum_inDegree_even G Aᶜ
        by_contra hcon
        push Not at hcon
        obtain ⟨k, hk⟩ := hSeven
        have hSeq : S = 2 * t := by omega
        have hle : ∀ v ∈ Aᶜ, (G.neighborFinset v ∩ Aᶜ).card ≤ 2 := by
          intro v₀ hv₀
          by_contra hc
          push Not at hc
          have hsplit : S = (G.neighborFinset v₀ ∩ Aᶜ).card
              + ∑ v ∈ Aᶜ.erase v₀, (G.neighborFinset v ∩ Aᶜ).card := by
            rw [hSdef]; exact (Finset.add_sum_erase Aᶜ _ hv₀).symm
          have hlow : 2 * (Aᶜ.erase v₀).card
              ≤ ∑ v ∈ Aᶜ.erase v₀, (G.neighborFinset v ∩ Aᶜ).card := by
            have h := Finset.card_nsmul_le_sum (Aᶜ.erase v₀)
              (fun v => (G.neighborFinset v ∩ Aᶜ).card) 2
              (fun v hv => hperv v (Finset.mem_of_mem_erase hv))
            simpa [smul_eq_mul, mul_comm] using h
          have hcard_erase : (Aᶜ.erase v₀).card = t - 1 := by
            rw [htdef]; exact Finset.card_erase_of_mem hv₀
          omega
        have hreg : ∀ v ∈ Aᶜ, (G.neighborFinset v ∩ Aᶜ).card = 2 :=
          fun v hv => le_antisymm (hle v hv) (hperv v hv)
        have hActri : ∀ a ∈ Aᶜ, ∀ b ∈ Aᶜ, ∀ c ∈ Aᶜ,
            ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) :=
          fun a ha b hb c hc => hDtri a (hAcsubD ha) b (hAcsubD hb) c (hAcsubD hc)
        have htge' : 6 ≤ Aᶜ.card := by rw [← htdef]; exact htge
        obtain ⟨a, ha, b, hb, c, hc, d, hd, hcard4, hab, hcd, hac, had, hbc, hbd⟩ :=
          ACMax.exists_2K2_of_two_regular_triangleFree G Aᶜ hActri hreg htge'
        refine hno2k2 ⟨a, b, c, d, ?_, hAcdeg a ha, hAcdeg b hb, hAcdeg c hc,
          hAcdeg d hd, hab, hcd, hac, had, hbc, hbd⟩
        convert hcard4 using 2
        ext x; simp
      have hq : t * t ≤ 7 * t := Nat.mul_le_mul htle (le_refl t)
      rw [mul_assoc]
      generalize t * t = q at hq ⊢
      omega
  -- Upper bound on hub–`D` edges: `≤ ∑_{Hub} deg = 3 + 3·|Hub|`.
  have hHubD_le : ∑ v ∈ Hubᶜ, (G.neighborFinset v ∩ Hub).card ≤ 3 + 3 * Hub.card := by
    rw [hcross Hubᶜ Hub]
    calc ∑ u ∈ Hub, (G.neighborFinset u ∩ Hubᶜ).card
        ≤ ∑ u ∈ Hub, (G.neighborFinset u).card :=
          Finset.sum_le_sum (fun u _ => Finset.card_le_card Finset.inter_subset_left)
      _ = ∑ u ∈ Hub, G.degree u :=
          Finset.sum_congr rfl (fun u _ => G.card_neighborFinset_eq_degree u)
      _ = 3 + 3 * Hub.card := hHubsum
  -- `A` is nonempty: it contains every hub.
  have hA : A.Nonempty := by
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hHubpos
    exact ⟨u, by rw [hmemA]; exact Or.inl ((hmemHub u).mp hu)⟩
  -- `Aᶜ` is nonempty: otherwise every degree-3 vertex has `≥ 2` hub-neighbours, forcing
  -- `2·|D| ≤ 3 + 3·|Hub|`, i.e. `16 ≤ 12`.
  have hAcne : Aᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hge : ∀ v ∈ Hubᶜ, 2 ≤ (G.neighborFinset v ∩ Hub).card := by
      intro v hv
      have hdeg := hnotHubDeg v (Finset.mem_compl.mp hv)
      have hvnotAc : v ∉ Aᶜ := by rw [hempty]; exact Finset.notMem_empty v
      rw [hmemAc] at hvnotAc
      push Not at hvnotAc
      have := hvnotAc hdeg; omega
    have hlow : 2 * Hubᶜ.card ≤ ∑ v ∈ Hubᶜ, (G.neighborFinset v ∩ Hub).card := by
      have h := Finset.card_nsmul_le_sum Hubᶜ
        (fun v => (G.neighborFinset v ∩ Hub).card) 2 hge
      simpa [smul_eq_mul, mul_comm] using h
    omega
  refine algConn_le_two_of_weighted_cut G A hA hAcne ?_
  rw [Fintype.card_fin]
  have hpt : A.card + t = 11 := by
    rw [htdef]
    have h := Finset.card_add_card_compl A; rwa [Fintype.card_fin] at h
  have hkey : A.card * t + t * t = 11 * t := by
    have h := congrArg (· * t) hpt
    simpa [add_mul] using h
  -- Arithmetic: `11·cut ≤ 2·|A|·t` from `cut + S = 3t`, density and `|A| + t = 11`.
  show 11 * cut ≤ 2 * (A.card * t)
  linarith [hcutS, hdensity, hkey]

end ACMax
