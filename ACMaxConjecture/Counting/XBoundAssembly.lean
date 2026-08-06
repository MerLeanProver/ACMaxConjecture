import ACMaxConjecture.Counting.CompactCell
import ACMaxConjecture.Counting.DoubleStar

/-!
# Degree-3/excess handshake

For a graph with minimum degree three and `2(n - 2)` edges, the number of
degree-3 vertices is exactly eight plus the total degree excess above four.
-/

namespace ACMax

open scoped Classical
open Finset

/-- The degree-3 population has cardinality `8 + excessX n G`. -/
theorem deg3_card_eq_eight_add_excess (n : ℕ) (G : SimpleGraph (Fin n))
    (hn : 2 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v, 3 ≤ G.degree v) :
    (deg3Set G).card = 8 + excessX n G := by
  classical
  have hsum : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hsum8 : ∑ v : Fin n, G.degree v + 8 = 4 * n := by omega
  set D3 := Finset.univ.filter fun v : Fin n => G.degree v = 3 with hD3
  set D4 := Finset.univ.filter fun v : Fin n => G.degree v = 4 with hD4
  set D5 := Finset.univ.filter fun v : Fin n => 5 ≤ G.degree v with hD5
  have hcard : D3.card + D4.card + D5.card = n := by
    have hpt : ∀ v : Fin n,
        (if G.degree v = 3 then 1 else 0) +
          (if G.degree v = 4 then 1 else 0) +
          (if 5 ≤ G.degree v then 1 else 0) = 1 := by
      intro v
      have := h3 v
      split_ifs <;> omega
    calc
      D3.card + D4.card + D5.card =
          ∑ v : Fin n, ((if G.degree v = 3 then 1 else 0) +
            (if G.degree v = 4 then 1 else 0) +
            (if 5 ≤ G.degree v then 1 else 0)) := by
        simp only [hD3, hD4, hD5, Finset.card_filter, ← Finset.sum_add_distrib]
      _ = ∑ _v : Fin n, 1 := Finset.sum_congr rfl fun v _ => hpt v
      _ = n := by simp
  have hdegsum : ∑ v : Fin n, G.degree v =
      3 * D3.card + 4 * D4.card + ∑ v ∈ D5, G.degree v := by
    have hpt : ∀ v : Fin n, G.degree v =
        3 * (if G.degree v = 3 then 1 else 0) +
          4 * (if G.degree v = 4 then 1 else 0) +
          (if 5 ≤ G.degree v then G.degree v else 0) := by
      intro v
      have := h3 v
      split_ifs <;> omega
    calc
      ∑ v : Fin n, G.degree v =
          ∑ v : Fin n, (3 * (if G.degree v = 3 then 1 else 0) +
            4 * (if G.degree v = 4 then 1 else 0) +
            (if 5 ≤ G.degree v then G.degree v else 0)) :=
        Finset.sum_congr rfl fun v _ => hpt v
      _ = 3 * D3.card + 4 * D4.card + ∑ v ∈ D5, G.degree v := by
        simp only [hD3, hD4, hD5, Finset.card_filter, Finset.sum_filter,
          Finset.mul_sum, mul_ite, mul_one, mul_zero, ← Finset.sum_add_distrib]
  have hex : excessX n G + 4 * D5.card = ∑ v ∈ D5, G.degree v := by
    have h4 : ∀ v ∈ D5, G.degree v - 4 + 4 = G.degree v := by
      intro v hv
      have : 5 ≤ G.degree v := (Finset.mem_filter.mp hv).2
      omega
    calc
      excessX n G + 4 * D5.card =
          ∑ v ∈ D5, (G.degree v - 4) + ∑ _v ∈ D5, 4 := by
        rw [excessX, ← hD5, Finset.sum_const, smul_eq_mul, mul_comm]
      _ = ∑ v ∈ D5, (G.degree v - 4 + 4) := Finset.sum_add_distrib.symm
      _ = ∑ v ∈ D5, G.degree v := Finset.sum_congr rfl h4
  have hd3 : (deg3Set G).card = D3.card := by rw [deg3Set, ← hD3]
  omega

end ACMax
