import ACMaxConjecture.Base
import ACMaxConjecture.InternalEdgesEven
import ACMaxConjecture.SmallCases.N12.Core

/-!
# Existence of a twin signed-cut certificate for `n = 12`

This file isolates the genuine open structural core of the `n = 12` case of the ACMAX
conjecture: in the residual regime (`δ ≥ 3`, no good triangle, an isolated degree-3 vertex,
no induced `2K₂` on degree-3 vertices, `e(D) ≤ 5`, no good `C₄`, no good `K_{2,3}`), the graph
admits an explicit *twin* certificate — an `M`-isolated degree-3 vertex `t` with two degree-4
hub-neighbours `h₁, h₂`, together with a `P₃` `x–y–z` of degree-3 vertices, all aligned so the
cross adjacencies vanish.  Feeding this certificate to `algConn_le_two_of_signed` closes the case.

The proof proceeds in four steps (see `exists_twin_signed_cert_twelve`):
1. **Isolated twin / degree sequence.**  From the isolated degree-3 vertex `t`, the hub set
   `Hub = filter (4 ≤ deg)` and the degree-3 set partition the vertices, the handshake forces
   `Hub.card ≤ 4`, and `t`'s three neighbours lie in `Hub`, so `Hub.card ∈ {3, 4}`.
2. **`M` is a double-star** (triangle/`C₄`/`2K₂`-free, max-degree `≤ 3`, `e(M) ∈ {4,5}`).
3. **Alignment via `hK23`** (the key clean step).
4. **Assembly** of the certificate.

Step 1's degree-partition counting is proved here.  The double-star characterisation of `M`
(step 2) together with the `hK23`-alignment and assembly (steps 3, 4) is the single remaining
`sorry` — the genuine open structural core of the `n = 12` case (verified only empirically).
-/

namespace ACMax

open scoped Classical

namespace N12

/-- **Structural core (the lone `sorry`).**  In the `n = 12` residual regime the degree-3
subgraph `M` is a double star: there are two adjacent degree-3 *centres* `c₁, c₂` whose every
neighbour has degree 3, a degree-3 *leaf* adjacent to `c₁` (and distinct from `c₂`) whose two
non-centre neighbours are distinct, non-adjacent degree-4 *hubs* `g₁, g₂` (and `leaf` has no
other degree-4 neighbour), together with two distinct *isolated twins* `tw₁, tw₂` of degree 3
all of whose neighbours have degree 4.  This double-star characterisation is the genuine open
structural core of the `n = 12` case (verified only empirically). -/
theorem M_double_star (G : SimpleGraph (Fin 12))
    (hm : G.edgeFinset.card = 20) (h3 : ∀ v : Fin 12, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 12, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (heD : ¬12 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card)
    (hC4 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 12, ({a, b, c, d, e} : Finset (Fin 12)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 17)
    (hiso : ∃ t : Fin 12, G.degree t = 3 ∧ ∀ w : Fin 12, G.Adj t w → G.degree w ≠ 3) :
    ∃ c₁ c₂ leaf tw₁ tw₂ g₁ g₂ : Fin 12,
      G.degree c₁ = 3 ∧ G.degree c₂ = 3 ∧ G.Adj c₁ c₂ ∧
        (∀ w : Fin 12, G.Adj c₁ w → G.degree w = 3) ∧
        (∀ w : Fin 12, G.Adj c₂ w → G.degree w = 3) ∧
        G.degree leaf = 3 ∧ G.Adj c₁ leaf ∧ leaf ≠ c₂ ∧
        G.Adj leaf g₁ ∧ G.Adj leaf g₂ ∧ g₁ ≠ g₂ ∧ ¬G.Adj g₁ g₂ ∧
        G.degree g₁ = 4 ∧ G.degree g₂ = 4 ∧
        (∀ w : Fin 12, G.Adj leaf w → G.degree w = 4 → w = g₁ ∨ w = g₂) ∧
        G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ tw₁ ≠ tw₂ ∧
        (∀ w : Fin 12, G.Adj tw₁ w → G.degree w = 4) ∧
        (∀ w : Fin 12, G.Adj tw₂ w → G.degree w = 4) := by
  classical
  -- **Step 1.**  Degree sequence `[4,4,4,4,3⁸]`.
  have hsum : ∑ v : Fin 12, G.degree v = 40 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  set D : Finset (Fin 12) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 12) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 12, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 12, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hDH : ∀ v : Fin 12, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub := by
    rw [Finset.disjoint_left]; intro v hv hv'
    have := (hmemD v).mp hv; have := (hmemHub v).mp hv'; omega
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard12 : D.card + Hub.card = 12 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 40 := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
    have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
    have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul, mul_comm] using h
  have hHubsum : ∑ v ∈ Hub, G.degree v = 4 + 3 * Hub.card := by
    rw [hsumD] at hsumpart; omega
  have hHubcard4 : Hub.card ≤ 4 := by omega
  -- Cross-count machinery (in-set neighbourhood as an indicator sum).
  have hcardInter : ∀ (a : Fin 12) (C : Finset (Fin 12)),
      (G.neighborFinset a ∩ C).card = ∑ c ∈ C, (if G.Adj a c then 1 else 0) := by
    intro a C
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun c _ => by simp only [SimpleGraph.mem_neighborFinset])
  have hcross : ∀ (B C : Finset (Fin 12)),
      ∑ a ∈ B, (G.neighborFinset a ∩ C).card = ∑ c ∈ C, (G.neighborFinset c ∩ B).card := by
    intro B C; simp_rw [hcardInter]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
      (fun a _ => by rw [SimpleGraph.adj_comm]))
  -- Each vertex splits its neighbourhood between `D` and `Hub`.
  have hsplitD : ∀ v : Fin 12,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = G.degree v := by
    intro v
    have hdj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) := by
      rw [Finset.disjoint_left]; intro a ha ha'
      rw [Finset.mem_inter] at ha ha'
      exact (Finset.disjoint_left.mp hdisj ha.2) ha'.2
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      ext a
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases hDH a with hd | hh
        · exact Or.inl ⟨h, hd⟩
        · exact Or.inr ⟨h, hh⟩
    rw [← Finset.card_union_of_disjoint hdj, hun, G.card_neighborFinset_eq_degree]
  have hsumDsplit : (∑ v ∈ D, (G.neighborFinset v ∩ D).card)
      + (∑ v ∈ D, (G.neighborFinset v ∩ Hub).card) = 3 * D.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun v _ => hsplitD v)]; exact hsumD
  have hcrossbound : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card ≤ 4 + 3 * Hub.card := by
    rw [hcross D Hub]
    calc ∑ h ∈ Hub, (G.neighborFinset h ∩ D).card
        ≤ ∑ h ∈ Hub, G.degree h := Finset.sum_le_sum (fun h _ => by
          rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left)
      _ = 4 + 3 * Hub.card := hHubsum
  -- `heD` (now phrased over `D`) bounds the in-`D` degree sum, forcing `Hub.card = 4`.
  have hHub4 : Hub.card = 4 := by omega
  have hD8 : D.card = 8 := by omega
  have hHubsum16 : ∑ v ∈ Hub, G.degree v = 16 := by omega
  have hHubdeg4 : ∀ v : Fin 12, v ∈ Hub → G.degree v = 4 := by
    intro v hv
    by_contra hne
    have h5 : 5 ≤ G.degree v := by have := (hmemHub v).mp hv; omega
    have hrest : 4 * (Hub.erase v).card ≤ ∑ u ∈ Hub.erase v, G.degree u := by
      have h := Finset.card_nsmul_le_sum (Hub.erase v) (fun u => G.degree u) 4
        (fun u hu => (hmemHub u).mp (Finset.mem_of_mem_erase hu))
      simpa [smul_eq_mul, mul_comm] using h
    have hsplit : G.degree v + ∑ u ∈ Hub.erase v, G.degree u = ∑ u ∈ Hub, G.degree u :=
      Finset.add_sum_erase Hub (fun u => G.degree u) hv
    have hcarderase : (Hub.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv, hHub4]
    omega
  -- **Step 2.**  `2·e(D) = ∑_{v∈D}(N v ∩ D) = 8 + 2·e_H`, with `e_H ≤ 1` (so `e(D) ∈ {4,5}`).
  have hsumHubsplit : (∑ v ∈ Hub, (G.neighborFinset v ∩ D).card)
      + (∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card) = 16 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun v _ => hsplitD v)]; exact hHubsum16
  have heDH : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ v ∈ Hub, (G.neighborFinset v ∩ D).card := hcross D Hub
  have hsumDsplit8 : (∑ v ∈ D, (G.neighborFinset v ∩ D).card)
      + (∑ v ∈ D, (G.neighborFinset v ∩ Hub).card) = 24 := by rw [hsumDsplit, hD8]
  have hsDD : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      = 8 + ∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card := by omega
  have heHbound : ∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card ≤ 3 := by omega
  -- **Steps 3–5 (the genuine open structural core — the lone remaining `sorry`).**
  -- Steps 1–2 above are fully proved: `Hub.card = 4`, every hub has degree `4`, `D.card = 8`
  -- (degree sequence `[4,4,4,4,3⁸]`), and `∑_{v∈D}(N v ∩ D).card = 8 + 2·e_H` with `e_H ≤ 1`
  -- (`hsDD`, `heHbound`), i.e. `e(D) = 4 + e_H ∈ {4,5}`.  What remains is the double-star
  -- characterisation of the degree-3 subgraph `M = G[D]`, the `hK23`-alignment and assembly:
  --   • Step 3: `M` is triangle-free (`hT`), `C₄`-free (`hC4`), `2K₂`-free (`h2k2`) with
  --     max-degree `≤ 3`, so its unique non-trivial edge component is a star, a double-star, or
  --     `C₅` (a `2K₂`-free, girth-`≥5`, max-degree-`≤3` connected graph).
  --   • Step 4: exclude `C₅` and `e(D) = 4`, pinning to the `e(D) = 5` double-star with two
  --     adjacent in-`M`-degree-3 centres (the `C₅` and `e(D)=4` variants each yield a *good*
  --     `K_{2,3}`/`C₄`, contradicting `hK23`/`hC4`).
  --   • Step 5: extract the two centres `c₁,c₂`, a leaf with its two non-adjacent degree-4 hubs
  --     `g₁,g₂`, and the two isolated twins `tw₁,tw₂`, discharging every output conjunct.
  -- This structural classification is verified only empirically (exhaustive `nauty` enumeration:
  -- the residual is a single graph) and is the genuine open core of the `n = 12` case.
  -- **Foundation (now proved): `e(M) = 4 + e_H` with `e_H ∈ {0,1}`, so `e(M) ∈ {4,5}`.**
  -- `hDDval` below pins `∑_{v∈D}(N v ∩ D).card ∈ {8, 10}` (i.e. `e(M) ∈ {4,5}`) using the
  -- evenness of an internal-degree sum (`sum_inDegree_even`).  The remaining `sorry` is the
  -- structural classification + alignment + assembly (steps 3–5 above).
  have hevenE : Even (∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card) := by
    convert sum_inDegree_even G Hub using 3 with v
    ext a; simp only [Finset.mem_inter]
  have hevenDD : Even (∑ v ∈ D, (G.neighborFinset v ∩ D).card) := by
    convert sum_inDegree_even G D using 3 with v
    ext a; simp only [Finset.mem_inter]
  have hEval : ∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card = 0
      ∨ ∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card = 2 := by
    obtain ⟨k, hk⟩ := hevenE; omega
  have hDDval : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 8
      ∨ ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10 := by
    rcases hEval with h | h <;> rw [hsDD, h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- **Steps 3–5 (assembly via the structural core lemmas).**
  have hHmem : ∀ v : Fin 12, v ∈ Hub ↔ G.degree v = 4 := by
    intro v
    constructor
    · intro hv; exact hHubdeg4 v hv
    · intro hv; exact (hmemHub v).mpr (by omega)
  have hR : Residual G D Hub := ⟨hmemD, hHmem, hDH, hD8, hHub4⟩
  rcases hDDval with h8 | h10
  · exact (eM_four_no_residual G D Hub hR hT h2k2 hC4 hK23 h8 (by omega)).elim
  · by_cases hc : ∃ u ∈ D, (G.neighborFinset u ∩ D).card = 3
    · exact eM_five_extract G D Hub hR hT h2k2 hC4 hK23 h10 (by omega) hc
    · push Not at hc
      have hc2 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2 := by
        intro v hv
        have hne := hc v hv
        have hle : (G.neighborFinset v ∩ D).card ≤ G.degree v := by
          rw [← G.card_neighborFinset_eq_degree]
          exact Finset.card_le_card Finset.inter_subset_left
        have hdv := (hmemD v).mp hv
        omega
      exact (eM_five_C5_no_residual G D Hub hR hT h2k2 hC4 hK23 h10 (by omega) hc2).elim

/-- In the `n = 12` residual regime, the graph admits a twin signed-cut certificate:
an `M`-isolated degree-3 vertex `t` with two degree-4 hub-neighbours `h₁, h₂`, a `P₃`
`x–y–z` of degree-3 vertices, with all cross adjacencies between `{t, h₁, h₂}` and `{x, y, z}`
absent. -/
theorem exists_twin_signed_cert_twelve (G : SimpleGraph (Fin 12))
    (hm : G.edgeFinset.card = 20) (h3 : ∀ v : Fin 12, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 12, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (heD : ¬12 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card)
    (hC4 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 12, ({a, b, c, d, e} : Finset (Fin 12)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 17)
    (hiso : ∃ t : Fin 12, G.degree t = 3 ∧ ∀ w : Fin 12, G.Adj t w → G.degree w ≠ 3) :
    ∃ t h₁ h₂ x y z : Fin 12,
      G.degree t = 3 ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
        G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
        G.Adj t h₁ ∧ G.Adj t h₂ ∧ G.Adj x y ∧ G.Adj y z ∧
        ¬G.Adj t x ∧ ¬G.Adj t y ∧ ¬G.Adj t z ∧
        ¬G.Adj h₁ x ∧ ¬G.Adj h₁ y ∧ ¬G.Adj h₁ z ∧
        ¬G.Adj h₂ x ∧ ¬G.Adj h₂ y ∧ ¬G.Adj h₂ z ∧
        h₁ ≠ h₂ ∧ t ≠ x ∧ t ≠ y ∧ t ≠ z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  classical
  -- **Step 2 (double star).**  Extract the named centres, leaf, hubs and twins of `M`.
  obtain ⟨c₁, c₂, leaf, tw₁, tw₂, g₁, g₂,
      hc₁deg, hc₂deg, hc₁c₂, hc₁hub, hc₂hub,
      hleafdeg, hc₁leaf, hleafc₂ne, hleafg₁, hleafg₂, hg₁g₂ne, hg₁g₂nadj, hg₁deg, hg₂deg,
      hleafhubs, htw₁deg, htw₂deg, htw₁₂ne, htw₁hub, htw₂hub⟩ :=
    M_double_star G hm h3 hT h2k2 heD hC4 hK23 hiso
  -- **Step 3 (alignment).**  The two twins cannot both be adjacent to both leaf-hubs `g₁, g₂`,
  -- else `{g₁, g₂} ∪ {tw₁, tw₂, leaf}` is a good `K_{2,3}` of degree-sum `4+4+3+3+3 = 17`.
  have hnot : ¬(G.Adj tw₁ g₁ ∧ G.Adj tw₁ g₂ ∧ G.Adj tw₂ g₁ ∧ G.Adj tw₂ g₂) := by
    rintro ⟨ht1g1, ht1g2, ht2g1, ht2g2⟩
    have hnt12 : ¬G.Adj tw₁ tw₂ := by intro h; have := htw₁hub tw₂ h; omega
    have hnt1l : ¬G.Adj tw₁ leaf := by intro h; have := htw₁hub leaf h; omega
    have hnt2l : ¬G.Adj tw₂ leaf := by intro h; have := htw₂hub leaf h; omega
    have e_g1t1 : g₁ ≠ tw₁ := by intro h; rw [h] at hg₁deg; omega
    have e_g1t2 : g₁ ≠ tw₂ := by intro h; rw [h] at hg₁deg; omega
    have e_g1l : g₁ ≠ leaf := by intro h; rw [h] at hg₁deg; omega
    have e_g2t1 : g₂ ≠ tw₁ := by intro h; rw [h] at hg₂deg; omega
    have e_g2t2 : g₂ ≠ tw₂ := by intro h; rw [h] at hg₂deg; omega
    have e_g2l : g₂ ≠ leaf := by intro h; rw [h] at hg₂deg; omega
    have e_t1l : tw₁ ≠ leaf := by
      intro h; subst h; have := htw₁hub c₁ hc₁leaf.symm; omega
    have e_t2l : tw₂ ≠ leaf := by
      intro h; subst h; have := htw₂hub c₁ hc₁leaf.symm; omega
    have h1 : g₁ ∉ ({g₂, tw₁, tw₂, leaf} : Finset (Fin 12)) := by
      simp [hg₁g₂ne, e_g1t1, e_g1t2, e_g1l]
    have h2 : g₂ ∉ ({tw₁, tw₂, leaf} : Finset (Fin 12)) := by
      simp [e_g2t1, e_g2t2, e_g2l]
    have h3' : tw₁ ∉ ({tw₂, leaf} : Finset (Fin 12)) := by simp [htw₁₂ne, e_t1l]
    have hcard5 : ({g₁, g₂, tw₁, tw₂, leaf} : Finset (Fin 12)).card = 5 := by
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3', Finset.card_pair e_t2l]
    exact hK23 ⟨g₁, g₂, tw₁, tw₂, leaf, hcard5, ht1g1.symm, ht2g1.symm, hleafg₁.symm,
      ht1g2.symm, ht2g2.symm, hleafg₂.symm, hg₁g₂nadj, hnt12, hnt1l, hnt2l, by omega⟩
  -- So some twin `tw` misses at least one of `g₁, g₂`; select it (degree 3, all hubs).
  have hcase : ¬(G.Adj tw₁ g₁ ∧ G.Adj tw₁ g₂) ∨ ¬(G.Adj tw₂ g₁ ∧ G.Adj tw₂ g₂) := by
    by_contra h; push Not at h; exact hnot ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  obtain ⟨tw, htwdeg, htwhub, hnotboth⟩ :
      ∃ tw : Fin 12, G.degree tw = 3 ∧ (∀ w : Fin 12, G.Adj tw w → G.degree w = 4) ∧
        ¬(G.Adj tw g₁ ∧ G.Adj tw g₂) := by
    rcases hcase with hc | hc
    · exact ⟨tw₁, htw₁deg, htw₁hub, hc⟩
    · exact ⟨tw₂, htw₂deg, htw₂hub, hc⟩
  -- `tw` meets `{g₁, g₂}` at most once, so it has two distinct hub-neighbours off `{g₁, g₂}`.
  have hScard : (G.neighborFinset tw).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]; exact htwdeg
  have hinter : (G.neighborFinset tw ∩ {g₁, g₂}).card ≤ 1 := by
    by_contra hcc
    push Not at hcc
    have hsub : G.neighborFinset tw ∩ ({g₁, g₂} : Finset (Fin 12)) ⊆ {g₁, g₂} :=
      Finset.inter_subset_right
    have hpair : ({g₁, g₂} : Finset (Fin 12)).card = 2 := Finset.card_pair hg₁g₂ne
    have heq : G.neighborFinset tw ∩ ({g₁, g₂} : Finset (Fin 12)) = {g₁, g₂} :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hg₁S : g₁ ∈ G.neighborFinset tw := by
      have hmm : g₁ ∈ G.neighborFinset tw ∩ ({g₁, g₂} : Finset (Fin 12)) := by rw [heq]; simp
      exact (Finset.mem_inter.mp hmm).1
    have hg₂S : g₂ ∈ G.neighborFinset tw := by
      have hmm : g₂ ∈ G.neighborFinset tw ∩ ({g₁, g₂} : Finset (Fin 12)) := by rw [heq]; simp
      exact (Finset.mem_inter.mp hmm).1
    exact hnotboth ⟨(G.mem_neighborFinset _ _).mp hg₁S, (G.mem_neighborFinset _ _).mp hg₂S⟩
  have hsdiff : 1 < (G.neighborFinset tw \ ({g₁, g₂} : Finset (Fin 12))).card := by
    have h := Finset.card_sdiff_add_card_inter (G.neighborFinset tw)
      ({g₁, g₂} : Finset (Fin 12))
    omega
  obtain ⟨h₁, hh₁mem, h₂, hh₂mem, hne12⟩ := Finset.one_lt_card.mp hsdiff
  rw [Finset.mem_sdiff] at hh₁mem hh₂mem
  obtain ⟨hh₁S, hh₁ng⟩ := hh₁mem
  obtain ⟨hh₂S, hh₂ng⟩ := hh₂mem
  have hadj_th₁ : G.Adj tw h₁ := (G.mem_neighborFinset _ _).mp hh₁S
  have hadj_th₂ : G.Adj tw h₂ := (G.mem_neighborFinset _ _).mp hh₂S
  have hdh₁ : G.degree h₁ = 4 := htwhub h₁ hadj_th₁
  have hdh₂ : G.degree h₂ = 4 := htwhub h₂ hadj_th₂
  have hadjleafc₁ : G.Adj leaf c₁ := hc₁leaf.symm
  -- **Step 4 (assembly).**  Cross non-adjacencies between `{tw, h₁, h₂}` and `{leaf, c₁, c₂}`.
  have hntl : ¬G.Adj tw leaf := by intro h; have := htwhub leaf h; omega
  have hntc₁ : ¬G.Adj tw c₁ := by intro h; have := htwhub c₁ h; omega
  have hntc₂ : ¬G.Adj tw c₂ := by intro h; have := htwhub c₂ h; omega
  have hh₁nl : ¬G.Adj h₁ leaf := by
    intro h; rcases hleafhubs h₁ h.symm hdh₁ with rfl | rfl
    · exact hh₁ng (by simp)
    · exact hh₁ng (by simp)
  have hh₂nl : ¬G.Adj h₂ leaf := by
    intro h; rcases hleafhubs h₂ h.symm hdh₂ with rfl | rfl
    · exact hh₂ng (by simp)
    · exact hh₂ng (by simp)
  have hh₁nc₁ : ¬G.Adj h₁ c₁ := by intro h; have := hc₁hub h₁ h.symm; omega
  have hh₁nc₂ : ¬G.Adj h₁ c₂ := by intro h; have := hc₂hub h₁ h.symm; omega
  have hh₂nc₁ : ¬G.Adj h₂ c₁ := by intro h; have := hc₁hub h₂ h.symm; omega
  have hh₂nc₂ : ¬G.Adj h₂ c₂ := by intro h; have := hc₂hub h₂ h.symm; omega
  have e_tx : tw ≠ leaf := by intro h; subst h; exact hntc₁ hadjleafc₁
  have e_ty : tw ≠ c₁ := by intro h; subst h; exact hntc₂ hc₁c₂
  have e_tz : tw ≠ c₂ := by intro h; subst h; exact hntc₁ hc₁c₂.symm
  exact ⟨tw, h₁, h₂, leaf, c₁, c₂,
    htwdeg, hdh₁, hdh₂, hleafdeg, hc₁deg, hc₂deg,
    hadj_th₁, hadj_th₂, hadjleafc₁, hc₁c₂,
    hntl, hntc₁, hntc₂,
    hh₁nl, hh₁nc₁, hh₁nc₂,
    hh₂nl, hh₂nc₁, hh₂nc₂,
    hne12, e_tx, e_ty, e_tz, hadjleafc₁.ne, hc₁c₂.ne, hleafc₂ne⟩

end N12

end ACMax
