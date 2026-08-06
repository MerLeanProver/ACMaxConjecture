import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core

/-!
# Corrected non-isolated 3-way dichotomy for the `n = 20` twin certificate

Under `2K₂`-freeness of `M = G[D]` (`h2k2`, in the form taken by
`nonisolated_component_bound`) and the edge budget `∑_{v∈D}|N v ∩ D| ≤ 6`, the set `S` of
`M`-non-isolated degree-3 vertices satisfies `|S| ≤ 4` (single-component bound).  At `|S| = 4`
the induced shape on `S` is pinned by parity and the per-vertex budget: a perfect matching is an
induced `2K₂` (excluded by `h2k2`), so `S` carries either an `M`-degree-3 star centre or an
induced path `a-b-c-d` with `M`-degree profile `(1, 2, 2, 1)`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- Cardinality of `N(v) ∩ D` as a sum of adjacency indicators over a superset `{x, y, z} ⊆ D`
of pairwise-distinct vertices. -/
theorem card_inter_eq_ite_sum_twenty (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (v x y z : Fin 20) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (hsub : G.neighborFinset v ∩ D ⊆ {x, y, z}) :
    (G.neighborFinset v ∩ D).card =
      (if G.Adj v x then 1 else 0) + (if G.Adj v y then 1 else 0) +
        (if G.Adj v z then 1 else 0) := by
  have heq : G.neighborFinset v ∩ D
      = ({x, y, z} : Finset (Fin 20)).filter (fun w => G.Adj v w) := by
    ext w
    constructor
    · intro hw
      exact Finset.mem_filter.mpr ⟨hsub hw,
        (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw).1⟩
    · intro hw
      obtain ⟨hwmem, hadj⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwmem
      rcases hwmem with rfl | rfl | rfl
      · exact hxD
      · exact hyD
      · exact hzD
  rw [heq, Finset.card_filter, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
  exact (add_assoc _ _ _).symm

/-- **Corrected 3-way non-isolated dichotomy (`n = 20`).**  If `M = G[D]` is induced-`2K₂`-free
and `∑_{v∈D}|N v ∩ D| ≤ 6`, then either at most `3` vertices of `D` are `M`-non-isolated, or
some vertex of `D` has `M`-degree `3` (star centre), or the non-isolated set is an induced path
`a-b-c-d` with `M`-degree profile `(1, 2, 2, 1)`. -/
theorem nonisolated_le_three_or_star_or_path (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (h2k2 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 6) :
    (D.filter (fun v => (G.neighborFinset v ∩ D).card ≠ 0)).card ≤ 3 ∨
    (∃ c : Fin 20, c ∈ D ∧ (G.neighborFinset c ∩ D).card = 3) ∨
    (∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      a ∈ D ∧ b ∈ D ∧ c ∈ D ∧ d ∈ D ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b d ∧
      (G.neighborFinset a ∩ D).card = 1 ∧ (G.neighborFinset b ∩ D).card = 2 ∧
      (G.neighborFinset c ∩ D).card = 2 ∧ (G.neighborFinset d ∩ D).card = 1) := by
  classical
  set S : Finset (Fin 20) := D.filter (fun v => (G.neighborFinset v ∩ D).card ≠ 0) with hSdef
  have hbound : 2 * S.card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card + 2 := by
    have h := nonisolated_component_bound G D hmemD h2k2
    have heq : D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) = S := by
      rw [hSdef]
    rwa [heq] at h
  by_cases hS3 : S.card ≤ 3
  · exact Or.inl hS3
  · have hScard : S.card = 4 := by omega
    obtain ⟨a, haS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have h3card : (S.erase a).card = 3 := by rw [Finset.card_erase_of_mem haS, hScard]
    obtain ⟨b, c, d, hbc, hbd, hcd, herase⟩ := Finset.card_eq_three.mp h3card
    have hbea : b ∈ S.erase a := by rw [herase]; simp
    have hcea : c ∈ S.erase a := by rw [herase]; simp
    have hdea : d ∈ S.erase a := by rw [herase]; simp
    have hbS : b ∈ S := Finset.mem_of_mem_erase hbea
    have hcS : c ∈ S := Finset.mem_of_mem_erase hcea
    have hdS : d ∈ S := Finset.mem_of_mem_erase hdea
    have hab : a ≠ b := (Finset.ne_of_mem_erase hbea).symm
    have hac : a ≠ c := (Finset.ne_of_mem_erase hcea).symm
    have had : a ≠ d := (Finset.ne_of_mem_erase hdea).symm
    have hSeq : S = {a, b, c, d} := by rw [← Finset.insert_erase haS, herase]
    have hmemS : ∀ v : Fin 20, v ∈ S → v ∈ D ∧ (G.neighborFinset v ∩ D).card ≠ 0 := by
      intro v hv
      rw [hSdef] at hv
      simpa using Finset.mem_filter.mp hv
    obtain ⟨haD, ha0⟩ := hmemS a haS
    obtain ⟨hbD, hb0⟩ := hmemS b hbS
    obtain ⟨hcD, hc0⟩ := hmemS c hcS
    obtain ⟨hdD, hd0⟩ := hmemS d hdS
    have hclosure : ∀ w v : Fin 20, v ∈ S → G.Adj v w → w ∈ D → w ∈ S := by
      intro w v hvS hadj hwD
      have hvD : v ∈ D := (hmemS v hvS).1
      rw [hSdef, Finset.mem_filter]
      exact ⟨hwD, Finset.card_ne_zero_of_mem (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hvD⟩)⟩
    have hsuba : G.neighborFinset a ∩ D ⊆ ({b, c, d} : Finset (Fin 20)) := by
      intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj a w := (G.mem_neighborFinset _ _).mp hwN
      have hwS : w ∈ S := hclosure w a haS hadj hwD
      rw [hSeq] at hwS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwS ⊢
      rcases hwS with rfl | h
      · exact absurd hadj G.irrefl
      · exact h
    have hsubb : G.neighborFinset b ∩ D ⊆ ({a, c, d} : Finset (Fin 20)) := by
      intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj b w := (G.mem_neighborFinset _ _).mp hwN
      have hwS : w ∈ S := hclosure w b hbS hadj hwD
      rw [hSeq] at hwS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwS ⊢
      rcases hwS with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hadj G.irrefl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hsubc : G.neighborFinset c ∩ D ⊆ ({a, b, d} : Finset (Fin 20)) := by
      intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj c w := (G.mem_neighborFinset _ _).mp hwN
      have hwS : w ∈ S := hclosure w c hcS hadj hwD
      rw [hSeq] at hwS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwS ⊢
      rcases hwS with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd hadj G.irrefl
      · exact Or.inr (Or.inr rfl)
    have hsubd : G.neighborFinset d ∩ D ⊆ ({a, b, c} : Finset (Fin 20)) := by
      intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj d w := (G.mem_neighborFinset _ _).mp hwN
      have hwS : w ∈ S := hclosure w d hdS hadj hwD
      rw [hSeq] at hwS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwS ⊢
      rcases hwS with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd hadj G.irrefl
    have hna := card_inter_eq_ite_sum_twenty G D a b c d hbc hbd hcd hbD hcD hdD hsuba
    have hnb := card_inter_eq_ite_sum_twenty G D b a c d hac had hcd haD hcD hdD hsubb
    have hnc := card_inter_eq_ite_sum_twenty G D c a b d hab had hbd haD hbD hdD hsubc
    have hnd := card_inter_eq_ite_sum_twenty G D d a b c hab hac hbc haD hbD hcD hsubd
    simp only [G.adj_comm b a] at hnb
    simp only [G.adj_comm c a, G.adj_comm c b] at hnc
    simp only [G.adj_comm d a, G.adj_comm d b, G.adj_comm d c] at hnd
    have hsum : (G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card +
        (G.neighborFinset c ∩ D).card + (G.neighborFinset d ∩ D).card ≤ 6 := by
      have hle : ∑ v ∈ S, (G.neighborFinset v ∩ D).card
          ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
        refine Finset.sum_le_sum_of_subset ?_
        rw [hSdef]
        exact Finset.filter_subset _ _
      have hexp : ∑ v ∈ S, (G.neighborFinset v ∩ D).card
          = (G.neighborFinset a ∩ D).card + ((G.neighborFinset b ∩ D).card +
            ((G.neighborFinset c ∩ D).card + (G.neighborFinset d ∩ D).card)) := by
        rw [hSeq, Finset.sum_insert (by simp [hab, hac, had]),
          Finset.sum_insert (by simp [hbc, hbd]), Finset.sum_insert (by simp [hcd]),
          Finset.sum_singleton]
      omega
    have hdega : G.degree a = 3 := (hmemD a).mp haD
    have hdegb : G.degree b = 3 := (hmemD b).mp hbD
    have hdegc : G.degree c = 3 := (hmemD c).mp hcD
    have hdegd : G.degree d = 3 := (hmemD d).mp hdD
    by_cases Hab : G.Adj a b <;> by_cases Hac : G.Adj a c <;> by_cases Had : G.Adj a d <;>
        by_cases Hbc : G.Adj b c <;> by_cases Hbd : G.Adj b d <;> by_cases Hcd : G.Adj c d <;>
        simp only [Hab, Hac, Had, Hbc, Hbd, Hcd, if_true, if_false] at hna hnb hnc hnd <;>
      first
      | omega
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Hcd : G.Adj c d
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hbc : ¬G.Adj b c
         guard_hyp Hbd : ¬G.Adj b d
         exact absurd ⟨a, b, c, d, card_four_twenty a b c d hab hac had hbc hbd hcd,
           hdega, hdegb, hdegc, hdegd, Hab, Hcd, Hac, Had, Hbc, Hbd⟩ h2k2)
      | (guard_hyp Hac : G.Adj a c
         guard_hyp Hbd : G.Adj b d
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hbc : ¬G.Adj b c
         guard_hyp Hcd : ¬G.Adj c d
         exact absurd ⟨a, c, b, d, card_four_twenty a c b d hac hab had hbc.symm hcd hbd,
           hdega, hdegc, hdegb, hdegd, Hac, Hbd, Hab, Had, fun h => Hbc h.symm, Hcd⟩ h2k2)
      | (guard_hyp Had : G.Adj a d
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Hbd : ¬G.Adj b d
         guard_hyp Hcd : ¬G.Adj c d
         exact absurd ⟨a, d, b, c, card_four_twenty a d b c had hab hac hbd.symm hcd.symm hbc,
           hdega, hdegd, hdegb, hdegc, Had, Hbc, Hab, Hac, fun h => Hbd h.symm,
           fun h => Hcd h.symm⟩ h2k2)
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Hac : G.Adj a c
         guard_hyp Had : G.Adj a d
         guard_hyp Hbc : ¬G.Adj b c
         guard_hyp Hbd : ¬G.Adj b d
         guard_hyp Hcd : ¬G.Adj c d
         exact Or.inr (Or.inl ⟨a, haD, by omega⟩))
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hbd : G.Adj b d
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hcd : ¬G.Adj c d
         exact Or.inr (Or.inl ⟨b, hbD, by omega⟩))
      | (guard_hyp Hac : G.Adj a c
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hcd : G.Adj c d
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hbd : ¬G.Adj b d
         exact Or.inr (Or.inl ⟨c, hcD, by omega⟩))
      | (guard_hyp Had : G.Adj a d
         guard_hyp Hbd : G.Adj b d
         guard_hyp Hcd : G.Adj c d
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Hbc : ¬G.Adj b c
         exact Or.inr (Or.inl ⟨d, hdD, by omega⟩))
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Hac : G.Adj a c
         guard_hyp Hbd : G.Adj b d
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hbc : ¬G.Adj b c
         guard_hyp Hcd : ¬G.Adj c d
         exact Or.inr (Or.inr ⟨c, a, b, d,
           card_four_twenty c a b d hac.symm hbc.symm hcd hab had hbd,
           hcD, haD, hbD, hdD, Hac.symm, Hab, Hbd, fun h => Hbc h.symm, Hcd, Had,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Hac : G.Adj a c
         guard_hyp Hcd : G.Adj c d
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hbc : ¬G.Adj b c
         guard_hyp Hbd : ¬G.Adj b d
         exact Or.inr (Or.inr ⟨b, a, c, d,
           card_four_twenty b a c d hab.symm hbc hbd hac had hcd,
           hbD, haD, hcD, hdD, Hab.symm, Hac, Hcd, Hbc, Hbd, Had,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Had : G.Adj a d
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Hbd : ¬G.Adj b d
         guard_hyp Hcd : ¬G.Adj c d
         exact Or.inr (Or.inr ⟨d, a, b, c,
           card_four_twenty d a b c had.symm hbd.symm hcd.symm hab hac hbc,
           hdD, haD, hbD, hcD, Had.symm, Hab, Hbc, fun h => Hbd h.symm, fun h => Hcd h.symm, Hac,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Had : G.Adj a d
         guard_hyp Hcd : G.Adj c d
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Hbc : ¬G.Adj b c
         guard_hyp Hbd : ¬G.Adj b d
         exact Or.inr (Or.inr ⟨b, a, d, c,
           card_four_twenty b a d c hab.symm hbd hbc had hac hcd.symm,
           hbD, haD, hdD, hcD, Hab.symm, Had, Hcd.symm, Hbd, Hbc, Hac,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hcd : G.Adj c d
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hbd : ¬G.Adj b d
         exact Or.inr (Or.inr ⟨a, b, c, d,
           card_four_twenty a b c d hab hac had hbc hbd hcd,
           haD, hbD, hcD, hdD, Hab, Hbc, Hcd, Hac, Had, Hbd,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hab : G.Adj a b
         guard_hyp Hbd : G.Adj b d
         guard_hyp Hcd : G.Adj c d
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hbc : ¬G.Adj b c
         exact Or.inr (Or.inr ⟨a, b, d, c,
           card_four_twenty a b d c hab had hac hbd hbc hcd.symm,
           haD, hbD, hdD, hcD, Hab, Hbd, Hcd.symm, Had, Hac, Hbc,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hac : G.Adj a c
         guard_hyp Had : G.Adj a d
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Hbd : ¬G.Adj b d
         guard_hyp Hcd : ¬G.Adj c d
         exact Or.inr (Or.inr ⟨d, a, c, b,
           card_four_twenty d a c b had.symm hcd.symm hbd.symm hac hab hbc.symm,
           hdD, haD, hcD, hbD, Had.symm, Hac, Hbc.symm, fun h => Hcd h.symm,
           fun h => Hbd h.symm, Hab,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hac : G.Adj a c
         guard_hyp Had : G.Adj a d
         guard_hyp Hbd : G.Adj b d
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Hbc : ¬G.Adj b c
         guard_hyp Hcd : ¬G.Adj c d
         exact Or.inr (Or.inr ⟨c, a, d, b,
           card_four_twenty c a d b hac.symm hcd hbc.symm had hab hbd.symm,
           hcD, haD, hdD, hbD, Hac.symm, Had, Hbd.symm, Hcd, fun h => Hbc h.symm, Hab,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hac : G.Adj a c
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hbd : G.Adj b d
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hcd : ¬G.Adj c d
         exact Or.inr (Or.inr ⟨a, c, b, d,
           card_four_twenty a c b d hac hab had hbc.symm hcd hbd,
           haD, hcD, hbD, hdD, Hac, Hbc.symm, Hbd, Hab, Had, Hcd,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Hac : G.Adj a c
         guard_hyp Hbd : G.Adj b d
         guard_hyp Hcd : G.Adj c d
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Had : ¬G.Adj a d
         guard_hyp Hbc : ¬G.Adj b c
         exact Or.inr (Or.inr ⟨a, c, d, b,
           card_four_twenty a c d b hac had hab hcd hbc.symm hbd.symm,
           haD, hcD, hdD, hbD, Hac, Hcd, Hbd.symm, Had, Hab, fun h => Hbc h.symm,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Had : G.Adj a d
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hbd : G.Adj b d
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Hcd : ¬G.Adj c d
         exact Or.inr (Or.inr ⟨a, d, b, c,
           card_four_twenty a d b c had hab hac hbd.symm hcd.symm hbc,
           haD, hdD, hbD, hcD, Had, Hbd.symm, Hbc, Hab, Hac, fun h => Hcd h.symm,
           by omega, by omega, by omega, by omega⟩))
      | (guard_hyp Had : G.Adj a d
         guard_hyp Hbc : G.Adj b c
         guard_hyp Hcd : G.Adj c d
         guard_hyp Hab : ¬G.Adj a b
         guard_hyp Hac : ¬G.Adj a c
         guard_hyp Hbd : ¬G.Adj b d
         exact Or.inr (Or.inr ⟨a, d, c, b,
           card_four_twenty a d c b had hac hab hcd.symm hbd.symm hbc.symm,
           haD, hdD, hcD, hbD, Had, Hcd.symm, Hbc.symm, Hac, Hab, fun h => Hbd h.symm,
           by omega, by omega, by omega, by omega⟩))

end N20

end ACMax
