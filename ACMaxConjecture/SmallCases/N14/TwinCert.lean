import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.SignedCut
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.Align
import ACMaxConjecture.SmallCases.N14.Doublestar
import ACMaxConjecture.SmallCases.N14.Deg5
import ACMaxConjecture.SmallCases.N14.C5
import ACMaxConjecture.SmallCases.N14.TwoHub
import ACMaxConjecture.SmallCases.N14.Align4
import ACMaxConjecture.SmallCases.N14.Align6
import ACMaxConjecture.SmallCases.N14.Align8

/-!
# Existence of a twin signed-cut certificate for `n = 14` (structural stub)

This file states the structural-existence lemma for the `n = 14` sparse-hub residual.  In that
regime (`δ ≥ 3`, no good triangle, an isolated degree-3 vertex, no induced `2K₂` on degree-3
vertices, no good `C₄`, no good `K_{2,3}`) one expects an explicit signed cut
`P, N` with `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`, fed to `algConn_le_two_of_signed`.

The construction of that cut (the twin-based structural dichotomy, mirroring `TwinCert13`) is the
single remaining open piece for `n = 14`; its proof is left as a documented `sorry`.  Everything
upstream in `CaseN14` is fully proved and relies only on this existence statement.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Two-hub opposite-twin cut assembly (boundary arithmetic, fully proved).**  Given two
distinct degree-4 hubs `h₁, h₂` with `h₁ ≁ h₂`, and four distinct degree-3 `M`-isolated twins
distinct degree-4 hubs `h₁, h₂` with `h₁ ≁ h₂`, and four distinct degree-3 `M`-isolated twins
`a, b` adjacent to `h₁` but not `h₂`, and `c, d` adjacent to `h₂` but not `h₁`, with all six
vertices distinct and the twins pairwise non-adjacent to the opposite hub and to one another's
"column", the two-hub cut `P = {h₁, a, b}`, `N = {h₂, c, d}` satisfies
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term vanishes and the boundary counts give
`0 + (2 + 2 + (deg h₁ − 2)) + (2 + 2 + (deg h₂ − 2)) = deg h₁ + deg h₂ + 4 = 12`. -/
theorem two_hub_opposite_twin_cert (G : SimpleGraph (Fin 14)) (h₁ h₂ a b c d : Fin 14)
    (hdegh₁ : G.degree h₁ = 4) (hdegh₂ : G.degree h₂ = 4)
    (hdega : G.degree a = 3) (hdegb : G.degree b = 3)
    (hdegc : G.degree c = 3) (hdegd : G.degree d = 3)
    (hadj_ah₁ : G.Adj a h₁) (hadj_bh₁ : G.Adj b h₁)
    (hadj_ch₂ : G.Adj c h₂) (hadj_dh₂ : G.Adj d h₂)
    (hn_h₁h₂ : ¬G.Adj h₁ h₂) (hn_h₁c : ¬G.Adj h₁ c) (hn_h₁d : ¬G.Adj h₁ d)
    (hn_ah₂ : ¬G.Adj a h₂) (hn_ac : ¬G.Adj a c) (hn_ad : ¬G.Adj a d)
    (hn_bh₂ : ¬G.Adj b h₂) (hn_bc : ¬G.Adj b c) (hn_bd : ¬G.Adj b d)
    (ne_h₁h₂ : h₁ ≠ h₂)
    (ne_h₁a : h₁ ≠ a) (ne_h₁b : h₁ ≠ b) (ne_h₁c : h₁ ≠ c) (ne_h₁d : h₁ ≠ d)
    (ne_h₂a : h₂ ≠ a) (ne_h₂b : h₂ ≠ b) (ne_h₂c : h₂ ≠ c) (ne_h₂d : h₂ ≠ d)
    (ne_ab : a ≠ b) (ne_ac : a ≠ c) (ne_ad : a ≠ d)
    (ne_bc : b ≠ c) (ne_bd : b ≠ d) (ne_cd : c ≠ d) :
    ∃ P N : Finset (Fin 14), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have hPcard : ({h₁, a, b} : Finset (Fin 14)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₁a, ne_h₁b]),
        Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
  have hNcard : ({h₂, c, d} : Finset (Fin 14)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₂c, ne_h₂d]),
        Finset.card_insert_of_notMem (by simp [ne_cd]), Finset.card_singleton]
  have hdisjPN : Disjoint ({h₁, a, b} : Finset (Fin 14)) ({h₂, c, d} : Finset (Fin 14)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;>
      first
      | exact ne_h₁h₂ rfl | exact ne_h₁c rfl | exact ne_h₁d rfl
      | exact ne_h₂a rfl.symm | exact ne_ac rfl | exact ne_ad rfl
      | exact ne_h₂b rfl.symm | exact ne_bc rfl | exact ne_bd rfl
  -- Cross term `e(P, N) = 0`.
  have hPN_h₁ : (G.neighborFinset h₁ ∩ ({h₂, c, d} : Finset (Fin 14))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn_h₁h₂ hadj
    · exact hn_h₁c hadj
    · exact hn_h₁d hadj
  have hPN_a : (G.neighborFinset a ∩ ({h₂, c, d} : Finset (Fin 14))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn_ah₂ hadj
    · exact hn_ac hadj
    · exact hn_ad hadj
  have hPN_b : (G.neighborFinset b ∩ ({h₂, c, d} : Finset (Fin 14))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn_bh₂ hadj
    · exact hn_bc hadj
    · exact hn_bd hadj
  -- Boundary `\` bounds.  `h₁` has two neighbours (`a, b`) inside `P ∪ N`.
  have hh₁_le : (G.neighborFinset h₁ \
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({a, b} : Finset (Fin 14)) ⊆
        G.neighborFinset h₁ ∩ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hadj_ah₁.symm, by simp⟩
      · exact ⟨hadj_bh₁.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₁ ∩
        (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card := by
      have h2 : ({a, b} : Finset (Fin 14)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
      calc 2 = ({a, b} : Finset (Fin 14)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁)
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegh₁] at hsd
    omega
  have hh₂_le : (G.neighborFinset h₂ \
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({c, d} : Finset (Fin 14)) ⊆
        G.neighborFinset h₂ ∩ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hadj_ch₂.symm, by simp⟩
      · exact ⟨hadj_dh₂.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₂ ∩
        (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card := by
      have h2 : ({c, d} : Finset (Fin 14)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_cd]), Finset.card_singleton]
      calc 2 = ({c, d} : Finset (Fin 14)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂)
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegh₂] at hsd
    omega
  have ha_le : (G.neighborFinset a \
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₁} : Finset (Fin 14)) ⊆
        G.neighborFinset a ∩ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_ah₁, by simp⟩
    have hge : 1 ≤ (G.neighborFinset a ∩
        (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₁} : Finset (Fin 14)).card := (Finset.card_singleton h₁).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset a)
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdega] at hsd
    omega
  have hb_le : (G.neighborFinset b \
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₁} : Finset (Fin 14)) ⊆
        G.neighborFinset b ∩ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_bh₁, by simp⟩
    have hge : 1 ≤ (G.neighborFinset b ∩
        (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₁} : Finset (Fin 14)).card := (Finset.card_singleton h₁).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset b)
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegb] at hsd
    omega
  have hc_le : (G.neighborFinset c \
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₂} : Finset (Fin 14)) ⊆
        G.neighborFinset c ∩ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_ch₂, by simp⟩
    have hge : 1 ≤ (G.neighborFinset c ∩
        (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₂} : Finset (Fin 14)).card := (Finset.card_singleton h₂).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset c)
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegc] at hsd
    omega
  have hd_le : (G.neighborFinset d \
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₂} : Finset (Fin 14)) ⊆
        G.neighborFinset d ∩ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_dh₂, by simp⟩
    have hge : 1 ≤ (G.neighborFinset d ∩
        (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₂} : Finset (Fin 14)).card := (Finset.card_singleton h₂).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset d)
      (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegd] at hsd
    omega
  refine ⟨({h₁, a, b} : Finset (Fin 14)), ({h₂, c, d} : Finset (Fin 14)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({h₁, a, b} : Finset (Fin 14)),
      (G.neighborFinset p ∩ ({h₂, c, d} : Finset (Fin 14))).card
      = (G.neighborFinset h₁ ∩ ({h₂, c, d} : Finset (Fin 14))).card
        + (G.neighborFinset a ∩ ({h₂, c, d} : Finset (Fin 14))).card
        + (G.neighborFinset b ∩ ({h₂, c, d} : Finset (Fin 14))).card := by
    rw [Finset.sum_insert (by simp [ne_h₁a, ne_h₁b]),
        Finset.sum_insert (by simp [ne_ab]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({h₁, a, b} : Finset (Fin 14)),
      (G.neighborFinset p \ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card
      = (G.neighborFinset h₁ \ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card
        + (G.neighborFinset a \ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card
        + (G.neighborFinset b \ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card := by
    rw [Finset.sum_insert (by simp [ne_h₁a, ne_h₁b]),
        Finset.sum_insert (by simp [ne_ab]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({h₂, c, d} : Finset (Fin 14)),
      (G.neighborFinset q \ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card
      = (G.neighborFinset h₂ \ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card
        + (G.neighborFinset c \ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card
        + (G.neighborFinset d \ (({h₁, a, b} : Finset (Fin 14)) ∪ {h₂, c, d})).card := by
    rw [Finset.sum_insert (by simp [ne_h₂c, ne_h₂d]),
        Finset.sum_insert (by simp [ne_cd]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_h₁, hPN_a, hPN_b]
  omega


/-- **Single-vertex-cut assembly (boundary arithmetic, fully proved).**  Generalizes
`single_twin_cut_certificate_gen`: the apex `v` of `P = {v, h₁, h₂}` need NOT be an `M`-isolated
twin — it is *any* degree-`3` vertex adjacent to `h₁, h₂` — and the cross term `e(P, N)` may be
positive.  Given a cherry (induced `P₃`) `x–y–z` of degree-`3` vertices and the combined side
condition `2·e(P,N) + deg h₁ + deg h₂ ≤ 8 + 2·[h₁∼h₂]` (where `e(P,N) = ∑_{p∈P}|N p ∩ N|` is the
actual cross-edge count), the single-vertex cut `P = {v, h₁, h₂}`, `N = {x, y, z}` satisfies
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The proof uses the global degree-sum identity
`4·e(P,N) + e(P,Z) + e(N,Z) = 2·e(P,N) + ∑_P deg + ∑_N deg − 2·e_in(P) − 2·e_in(N)` (the cross
count `e(P,N) = e(N,P)` via `cross_count_fourteen`), with `∑_P deg = 3 + deg h₁ + deg h₂`,
`∑_N deg = 9`, `e_in(P) ≥ 2 + [h₁∼h₂]`, `e_in(N) = 2`, closing by the side condition. -/
theorem single_vertex_cut_certificate (G : SimpleGraph (Fin 14)) (v h₁ h₂ x y z : Fin 14)
    (hdegv : G.degree v = 3)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hadj_vh₁ : G.Adj v h₁) (hadj_vh₂ : G.Adj v h₂)
    (hadj_xy : G.Adj x y) (hadj_yz : G.Adj y z) (_hnadj_xz : ¬G.Adj x z)
    (hside : 2 * (∑ p ∈ ({v, h₁, h₂} : Finset (Fin 14)),
        (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 14))).card)
        + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * (if G.Adj h₁ h₂ then 1 else 0))
    (ne_h₁h₂ : h₁ ≠ h₂)
    (ne_vx : v ≠ x) (ne_vy : v ≠ y) (ne_vz : v ≠ z)
    (ne_h₁x : h₁ ≠ x) (ne_h₁y : h₁ ≠ y) (ne_h₁z : h₁ ≠ z)
    (ne_h₂x : h₂ ≠ x) (ne_h₂y : h₂ ≠ y) (ne_h₂z : h₂ ≠ z)
    (ne_xy : x ≠ y) (ne_yz : y ≠ z) (ne_xz : x ≠ z) :
    ∃ P N : Finset (Fin 14), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have ne_vh₁ : v ≠ h₁ := G.ne_of_adj hadj_vh₁
  have ne_vh₂ : v ≠ h₂ := G.ne_of_adj hadj_vh₂
  set ind : ℕ := (if G.Adj h₁ h₂ then 1 else 0) with hind
  have hPcard : ({v, h₁, h₂} : Finset (Fin 14)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_vh₁, ne_vh₂]),
        Finset.card_insert_of_notMem (by simp [ne_h₁h₂]), Finset.card_singleton]
  have hNcard : ({x, y, z} : Finset (Fin 14)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_xy, ne_xz]),
        Finset.card_insert_of_notMem (by simp [ne_yz]), Finset.card_singleton]
  have hdisjPN : Disjoint ({v, h₁, h₂} : Finset (Fin 14)) ({x, y, z} : Finset (Fin 14)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact ne_vx rfl | exact ne_vy rfl | exact ne_vz rfl
      | exact ne_h₁x rfl | exact ne_h₁y rfl | exact ne_h₁z rfl
      | exact ne_h₂x rfl | exact ne_h₂y rfl | exact ne_h₂z rfl
  have decomp : ∀ w : Fin 14,
      (G.neighborFinset w ∩ ({v, h₁, h₂} : Finset (Fin 14))).card
        + (G.neighborFinset w ∩ ({x, y, z} : Finset (Fin 14))).card
        + (G.neighborFinset w \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card
      = G.degree w := by
    intro w
    have hdj : Disjoint (G.neighborFinset w ∩ ({v, h₁, h₂} : Finset (Fin 14)))
        (G.neighborFinset w ∩ ({x, y, z} : Finset (Fin 14))) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hdisjPN) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have h1 : (G.neighborFinset w ∩ ({v, h₁, h₂} : Finset (Fin 14))).card
        + (G.neighborFinset w ∩ ({x, y, z} : Finset (Fin 14))).card
        = (G.neighborFinset w ∩ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card := by
      rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdj]
    have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset w)
      (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree] at h2
    omega
  have hcc := cross_count_fourteen G ({v, h₁, h₂} : Finset (Fin 14)) ({x, y, z} : Finset (Fin 14))
  have e_crossP : ∑ p ∈ ({v, h₁, h₂} : Finset (Fin 14)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 14))).card
      = (G.neighborFinset v ∩ ({x, y, z} : Finset (Fin 14))).card
        + (G.neighborFinset h₁ ∩ ({x, y, z} : Finset (Fin 14))).card
        + (G.neighborFinset h₂ ∩ ({x, y, z} : Finset (Fin 14))).card := by
    rw [Finset.sum_insert (by simp [ne_vh₁, ne_vh₂]),
        Finset.sum_insert (by simp [ne_h₁h₂]), Finset.sum_singleton]; ring
  have e_crossN : ∑ q ∈ ({x, y, z} : Finset (Fin 14)),
      (G.neighborFinset q ∩ ({v, h₁, h₂} : Finset (Fin 14))).card
      = (G.neighborFinset x ∩ ({v, h₁, h₂} : Finset (Fin 14))).card
        + (G.neighborFinset y ∩ ({v, h₁, h₂} : Finset (Fin 14))).card
        + (G.neighborFinset z ∩ ({v, h₁, h₂} : Finset (Fin 14))).card := by
    rw [Finset.sum_insert (by simp [ne_xy, ne_xz]),
        Finset.sum_insert (by simp [ne_yz]), Finset.sum_singleton]; ring
  have e_Pout : ∑ p ∈ ({v, h₁, h₂} : Finset (Fin 14)),
      (G.neighborFinset p \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card
      = (G.neighborFinset v \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card
        + (G.neighborFinset h₁ \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card
        + (G.neighborFinset h₂ \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_vh₁, ne_vh₂]),
        Finset.sum_insert (by simp [ne_h₁h₂]), Finset.sum_singleton]; ring
  have e_Nout : ∑ q ∈ ({x, y, z} : Finset (Fin 14)),
      (G.neighborFinset q \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card
      = (G.neighborFinset x \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card
        + (G.neighborFinset y \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card
        + (G.neighborFinset z \ (({v, h₁, h₂} : Finset (Fin 14)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_xy, ne_xz]),
        Finset.sum_insert (by simp [ne_yz]), Finset.sum_singleton]; ring
  have hpv : 2 ≤ (G.neighborFinset v ∩ ({v, h₁, h₂} : Finset (Fin 14))).card := by
    have hsub : ({h₁, h₂} : Finset (Fin 14)) ⊆
        G.neighborFinset v ∩ ({v, h₁, h₂} : Finset (Fin 14)) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_vh₁, by simp⟩
      · exact ⟨hadj_vh₂, by simp⟩
    have h2 : ({h₁, h₂} : Finset (Fin 14)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [ne_h₁h₂]), Finset.card_singleton]
    calc 2 = ({h₁, h₂} : Finset (Fin 14)).card := h2.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hph1 : 1 + ind ≤ (G.neighborFinset h₁ ∩ ({v, h₁, h₂} : Finset (Fin 14))).card := by
    by_cases hadj12 : G.Adj h₁ h₂
    · have hs1 : ind = 1 := by rw [hind]; simp [hadj12]
      have hsub : ({v, h₂} : Finset (Fin 14)) ⊆
          G.neighborFinset h₁ ∩ ({v, h₁, h₂} : Finset (Fin 14)) := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rw [Finset.mem_inter, G.mem_neighborFinset]
        rcases ha with rfl | rfl
        · exact ⟨hadj_vh₁.symm, by simp⟩
        · exact ⟨hadj12, by simp⟩
      have h2 : ({v, h₂} : Finset (Fin 14)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_vh₂]), Finset.card_singleton]
      rw [hs1]
      calc 1 + 1 = ({v, h₂} : Finset (Fin 14)).card := by rw [h2]
        _ ≤ _ := Finset.card_le_card hsub
    · have hs0 : ind = 0 := by rw [hind]; simp [hadj12]
      rw [hs0]
      have hsub : ({v} : Finset (Fin 14)) ⊆
          G.neighborFinset h₁ ∩ ({v, h₁, h₂} : Finset (Fin 14)) := by
        intro a ha
        rw [Finset.mem_singleton] at ha; subst ha
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨hadj_vh₁.symm, by simp⟩
      calc 1 + 0 = ({v} : Finset (Fin 14)).card := by simp
        _ ≤ _ := Finset.card_le_card hsub
  have hph2 : 1 + ind ≤ (G.neighborFinset h₂ ∩ ({v, h₁, h₂} : Finset (Fin 14))).card := by
    by_cases hadj12 : G.Adj h₁ h₂
    · have hs1 : ind = 1 := by rw [hind]; simp [hadj12]
      have hsub : ({v, h₁} : Finset (Fin 14)) ⊆
          G.neighborFinset h₂ ∩ ({v, h₁, h₂} : Finset (Fin 14)) := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rw [Finset.mem_inter, G.mem_neighborFinset]
        rcases ha with rfl | rfl
        · exact ⟨hadj_vh₂.symm, by simp⟩
        · exact ⟨hadj12.symm, by simp⟩
      have h2 : ({v, h₁} : Finset (Fin 14)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_vh₁]), Finset.card_singleton]
      rw [hs1]
      calc 1 + 1 = ({v, h₁} : Finset (Fin 14)).card := by rw [h2]
        _ ≤ _ := Finset.card_le_card hsub
    · have hs0 : ind = 0 := by rw [hind]; simp [hadj12]
      rw [hs0]
      have hsub : ({v} : Finset (Fin 14)) ⊆
          G.neighborFinset h₂ ∩ ({v, h₁, h₂} : Finset (Fin 14)) := by
        intro a ha
        rw [Finset.mem_singleton] at ha; subst ha
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨hadj_vh₂.symm, by simp⟩
      calc 1 + 0 = ({v} : Finset (Fin 14)).card := by simp
        _ ≤ _ := Finset.card_le_card hsub
  have hnx : 1 ≤ (G.neighborFinset x ∩ ({x, y, z} : Finset (Fin 14))).card := by
    have hsub : ({y} : Finset (Fin 14)) ⊆ G.neighborFinset x ∩ ({x, y, z} : Finset (Fin 14)) := by
      intro a ha; rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj_xy, by simp⟩
    calc 1 = ({y} : Finset (Fin 14)).card := (Finset.card_singleton y).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hny : 2 ≤ (G.neighborFinset y ∩ ({x, y, z} : Finset (Fin 14))).card := by
    have hsub : ({x, z} : Finset (Fin 14)) ⊆
        G.neighborFinset y ∩ ({x, y, z} : Finset (Fin 14)) := by
      intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_xy.symm, by simp⟩
      · exact ⟨hadj_yz, by simp⟩
    have h2 : ({x, z} : Finset (Fin 14)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [ne_xz]), Finset.card_singleton]
    calc 2 = ({x, z} : Finset (Fin 14)).card := h2.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hnz : 1 ≤ (G.neighborFinset z ∩ ({x, y, z} : Finset (Fin 14))).card := by
    have hsub : ({y} : Finset (Fin 14)) ⊆ G.neighborFinset z ∩ ({x, y, z} : Finset (Fin 14)) := by
      intro a ha; rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj_yz.symm, by simp⟩
    calc 1 = ({y} : Finset (Fin 14)).card := (Finset.card_singleton y).symm
      _ ≤ _ := Finset.card_le_card hsub
  have dv := decomp v; have dh1 := decomp h₁; have dh2 := decomp h₂
  have dx := decomp x; have dy := decomp y; have dz := decomp z
  rw [hdegv] at dv; rw [hdegx] at dx; rw [hdegy] at dy; rw [hdegz] at dz
  rw [e_crossP, e_crossN] at hcc
  rw [e_crossP] at hside
  refine ⟨({v, h₁, h₂} : Finset (Fin 14)), ({x, y, z} : Finset (Fin 14)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  rw [e_crossP, e_Pout, e_Nout, hPcard]
  omega

/-- **2-twin-cut assembly for `n = 14` (boundary arithmetic, fully proved).**  Port of the `n = 13`
`two_twin_cut_certificate`: two distinct `M`-isolated degree-`3` twins `t₁, t₂` sharing a common hub
`h` of degree `≤ 5`, and a `P₃` `x–y–z` of degree-`3` vertices with `h` (and the twins) non-adjacent
to all of `x, y, z`.  The 2-twin cut `P = {t₁, t₂, h}`, `N = {x, y, z}` satisfies
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term vanishes and the boundary counts give
`0 + (2 + 2 + (deg h − 2)) + (2 + 1 + 2) = deg h + 7 ≤ 12`. -/
theorem two_twin_cut_certificate_fourteen (G : SimpleGraph (Fin 14)) (t₁ t₂ h x y z : Fin 14)
    (hdegt₁ : G.degree t₁ = 3) (hdegt₂ : G.degree t₂ = 3) (hdegh : G.degree h ≤ 5)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hadj_t₁h : G.Adj t₁ h) (hadj_t₂h : G.Adj t₂ h)
    (hadj_xy : G.Adj x y) (hadj_yz : G.Adj y z)
    (hnt₁_x : ¬G.Adj t₁ x) (hnt₁_y : ¬G.Adj t₁ y) (hnt₁_z : ¬G.Adj t₁ z)
    (hnt₂_x : ¬G.Adj t₂ x) (hnt₂_y : ¬G.Adj t₂ y) (hnt₂_z : ¬G.Adj t₂ z)
    (hnh_x : ¬G.Adj h x) (hnh_y : ¬G.Adj h y) (hnh_z : ¬G.Adj h z)
    (ne_t₁t₂ : t₁ ≠ t₂)
    (ne_t₁x : t₁ ≠ x) (ne_t₁y : t₁ ≠ y) (ne_t₁z : t₁ ≠ z)
    (ne_t₂x : t₂ ≠ x) (ne_t₂y : t₂ ≠ y) (ne_t₂z : t₂ ≠ z)
    (ne_hx : h ≠ x) (ne_hy : h ≠ y) (ne_hz : h ≠ z)
    (ne_xy : x ≠ y) (ne_yz : y ≠ z) (ne_xz : x ≠ z) :
    ∃ P N : Finset (Fin 14), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have ne_t₁h : t₁ ≠ h := G.ne_of_adj hadj_t₁h
  have ne_t₂h : t₂ ≠ h := G.ne_of_adj hadj_t₂h
  have hPcard : ({t₁, t₂, h} : Finset (Fin 14)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.card_insert_of_notMem (by simp [ne_t₂h]), Finset.card_singleton]
  have hNcard : ({x, y, z} : Finset (Fin 14)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_xy, ne_xz]),
        Finset.card_insert_of_notMem (by simp [ne_yz]), Finset.card_singleton]
  have hdisjPN : Disjoint ({t₁, t₂, h} : Finset (Fin 14)) ({x, y, z} : Finset (Fin 14)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact ne_t₁x rfl | exact ne_t₁y rfl | exact ne_t₁z rfl
      | exact ne_t₂x rfl | exact ne_t₂y rfl | exact ne_t₂z rfl
      | exact ne_hx rfl | exact ne_hy rfl | exact ne_hz rfl
  have hPN_t₁ : (G.neighborFinset t₁ ∩ ({x, y, z} : Finset (Fin 14))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt₁_x hadj
    · exact hnt₁_y hadj
    · exact hnt₁_z hadj
  have hPN_t₂ : (G.neighborFinset t₂ ∩ ({x, y, z} : Finset (Fin 14))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt₂_x hadj
    · exact hnt₂_y hadj
    · exact hnt₂_z hadj
  have hPN_h : (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 14))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnh_x hadj
    · exact hnh_y hadj
    · exact hnh_z hadj
  have ht₁_le : (G.neighborFinset t₁ \
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({h} : Finset (Fin 14)) ⊆
        G.neighborFinset t₁ ∩ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_t₁h, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₁ ∩
        (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card := by
      calc 1 = ({h} : Finset (Fin 14)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₁)
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegt₁] at hsd
    omega
  have ht₂_le : (G.neighborFinset t₂ \
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({h} : Finset (Fin 14)) ⊆
        G.neighborFinset t₂ ∩ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_t₂h, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₂ ∩
        (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card := by
      calc 1 = ({h} : Finset (Fin 14)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₂)
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegt₂] at hsd
    omega
  have hh_le : (G.neighborFinset h \
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card ≤ 3 := by
    have hsub : ({t₁, t₂} : Finset (Fin 14)) ⊆
        G.neighborFinset h ∩ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_t₁h.symm, by simp⟩
      · exact ⟨hadj_t₂h.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h ∩
        (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card := by
      have h2 : ({t₁, t₂} : Finset (Fin 14)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_t₁t₂]), Finset.card_singleton]
      calc 2 = ({t₁, t₂} : Finset (Fin 14)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h)
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hx_le : (G.neighborFinset x \
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({y} : Finset (Fin 14)) ⊆
        G.neighborFinset x ∩ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_xy, by simp⟩
    have hge : 1 ≤ (G.neighborFinset x ∩
        (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card := by
      calc 1 = ({y} : Finset (Fin 14)).card := (Finset.card_singleton y).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegx] at hsd
    omega
  have hy_le : (G.neighborFinset y \
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card ≤ 1 := by
    have hsub : ({x, z} : Finset (Fin 14)) ⊆
        G.neighborFinset y ∩ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_xy.symm, by simp⟩
      · exact ⟨hadj_yz, by simp⟩
    have hge : 2 ≤ (G.neighborFinset y ∩
        (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card := by
      have h2 : ({x, z} : Finset (Fin 14)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_xz]), Finset.card_singleton]
      calc 2 = ({x, z} : Finset (Fin 14)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegy] at hsd
    omega
  have hz_le : (G.neighborFinset z \
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({y} : Finset (Fin 14)) ⊆
        G.neighborFinset z ∩ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_yz.symm, by simp⟩
    have hge : 1 ≤ (G.neighborFinset z ∩
        (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card := by
      calc 1 = ({y} : Finset (Fin 14)).card := (Finset.card_singleton y).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
      (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegz] at hsd
    omega
  refine ⟨({t₁, t₂, h} : Finset (Fin 14)), ({x, y, z} : Finset (Fin 14)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({t₁, t₂, h} : Finset (Fin 14)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 14))).card
      = (G.neighborFinset t₁ ∩ ({x, y, z} : Finset (Fin 14))).card
        + (G.neighborFinset t₂ ∩ ({x, y, z} : Finset (Fin 14))).card
        + (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 14))).card := by
    rw [Finset.sum_insert (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.sum_insert (by simp [ne_t₂h]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({t₁, t₂, h} : Finset (Fin 14)),
      (G.neighborFinset p \ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card
      = (G.neighborFinset t₁ \ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card
        + (G.neighborFinset t₂ \ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card
        + (G.neighborFinset h \ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.sum_insert (by simp [ne_t₂h]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({x, y, z} : Finset (Fin 14)),
      (G.neighborFinset q \ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card
      = (G.neighborFinset x \ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card
        + (G.neighborFinset y \ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card
        + (G.neighborFinset z \ (({t₁, t₂, h} : Finset (Fin 14)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_xy, ne_xz]),
        Finset.sum_insert (by simp [ne_yz]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_t₁, hPN_t₂, hPN_h]
  omega

/-- **Single-vertex config yields the signed cut.**  Unpacks a `SingleVertexConfig` and feeds it to
`single_vertex_cut_certificate`. -/
theorem singleVertexConfig_to_cut (G : SimpleGraph (Fin 14)) (h : SingleVertexConfig G) :
    ∃ P N : Finset (Fin 14), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨v, h₁, h₂, x, y, z, hdegv, hdegx, hdegy, hdegz, hadj_vh₁, hadj_vh₂, hadj_xy, hadj_yz,
    hnadj_xz, hside, ne_h₁h₂, ne_vx, ne_vy, ne_vz, ne_h₁x, ne_h₁y, ne_h₁z, ne_h₂x, ne_h₂y, ne_h₂z,
    ne_xy, ne_yz, ne_xz⟩ := h
  exact single_vertex_cut_certificate G v h₁ h₂ x y z hdegv hdegx hdegy hdegz hadj_vh₁ hadj_vh₂
    hadj_xy hadj_yz hnadj_xz hside ne_h₁h₂ ne_vx ne_vy ne_vz ne_h₁x ne_h₁y ne_h₁z ne_h₂x ne_h₂y
    ne_h₂z ne_xy ne_yz ne_xz

/-- **2-twin config yields the signed cut.**  Unpacks a `TwoTwinConfig` and feeds it to
`two_twin_cut_certificate_fourteen`. -/
theorem twoTwinConfig_to_cut (G : SimpleGraph (Fin 14)) (h : TwoTwinConfig G) :
    ∃ P N : Finset (Fin 14), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨t₁, t₂, hh, x, y, z, hdegt₁, hdegt₂, hdegh, hdegx, hdegy, hdegz, hadj_t₁h, hadj_t₂h,
    hadj_xy, hadj_yz, hnt₁_x, hnt₁_y, hnt₁_z, hnt₂_x, hnt₂_y, hnt₂_z, hnh_x, hnh_y, hnh_z,
    ne_t₁t₂, ne_t₁x, ne_t₁y, ne_t₁z, ne_t₂x, ne_t₂y, ne_t₂z, ne_hx, ne_hy, ne_hz,
    ne_xy, ne_yz, ne_xz⟩ := h
  exact two_twin_cut_certificate_fourteen G t₁ t₂ hh x y z hdegt₁ hdegt₂ hdegh hdegx hdegy hdegz
    hadj_t₁h hadj_t₂h hadj_xy hadj_yz hnt₁_x hnt₁_y hnt₁_z hnt₂_x hnt₂_y hnt₂_z hnh_x hnh_y hnh_z
    ne_t₁t₂ ne_t₁x ne_t₁y ne_t₁z ne_t₂x ne_t₂y ne_t₂z ne_hx ne_hy ne_hz ne_xy ne_yz ne_xz

/-- **Two-hub config yields the signed cut.**  Unpacks a `TwoHubConfig` and feeds it to
`two_hub_opposite_twin_cert`. -/
theorem twoHubConfig_to_cut (G : SimpleGraph (Fin 14)) (h : TwoHubConfig G) :
    ∃ P N : Finset (Fin 14), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨h₁, h₂, a, b, c, d, hdegh₁, hdegh₂, hdega, hdegb, hdegc, hdegd,
    hadj_ah₁, hadj_bh₁, hadj_ch₂, hadj_dh₂,
    hn_h₁h₂, hn_h₁c, hn_h₁d, hn_ah₂, hn_ac, hn_ad, hn_bh₂, hn_bc, hn_bd,
    ne_h₁h₂, ne_h₁a, ne_h₁b, ne_h₁c, ne_h₁d, ne_h₂a, ne_h₂b, ne_h₂c, ne_h₂d,
    ne_ab, ne_ac, ne_ad, ne_bc, ne_bd, ne_cd⟩ := h
  exact two_hub_opposite_twin_cert G h₁ h₂ a b c d hdegh₁ hdegh₂ hdega hdegb hdegc hdegd
    hadj_ah₁ hadj_bh₁ hadj_ch₂ hadj_dh₂ hn_h₁h₂ hn_h₁c hn_h₁d hn_ah₂ hn_ac hn_ad
    hn_bh₂ hn_bc hn_bd ne_h₁h₂ ne_h₁a ne_h₁b ne_h₁c ne_h₁d ne_h₂a ne_h₂b ne_h₂c ne_h₂d
    ne_ab ne_ac ne_ad ne_bc ne_bd ne_cd

/-- **Structural-existence stub for `n = 14`.**  Same hypothesis shape as
`exists_twin_signed_cert_thirteen`, with `Fin 14`, `hm : edgeFinset.card = 24`, and the `n = 14`
good-`C₄` (degree-sum `≤ 13`) and good-`K_{2,3}` (degree-sum `≤ 18`) predicates.  Concludes the
existence of a signed cut `P, N` with `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The proof dispatches
on `e(M) = (∑_{v∈D}|N v ∩ D|)/2`:
* `e(M) ≥ 4` (`s ≥ 8`): the *three-way* alignment dichotomy `halign8`
  (`SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig`), replacing the single-twin config (which is
  unprovable for the ≈ 91 degree-`5` graphs whose degree-`5` hub is adjacent to no degree-`4` hub).
* `e(M) ≤ 2` (`s ≤ 4`): two-hub opposite-twin cut, via `two_hub_config_fourteen`.
* `e(M) = 3` (`s = 6`): the two-hub cut is no longer always available (≈ 46 of the 4229 residual
  graphs admit no two-hub cut), so we dispatch on a *three-way* alignment dichotomy
  `SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig` — the verified covering combination — feeding
  `single_vertex_cut_certificate`, `two_twin_cut_certificate_fourteen`, or `two_hub_opposite_twin_cert`.
All three boundary certificates and the full dispatch skeleton are proved; the structural-selection
helpers (`halign8`, the `s = 6` three-way `halign` dichotomy) carry the documented `sorry`s. -/
theorem exists_twin_signed_cert_fourteen (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 14, ({a, b, c, d, e} : Finset (Fin 14)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (_hiso : ∃ t : Fin 14, G.degree t = 3 ∧ ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3) :
    ∃ P N : Finset (Fin 14), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set s : ℕ := ∑ v ∈ D, (G.neighborFinset v ∩ D).card with hsdef
  rcases Nat.lt_or_ge s 8 with hlt | hge
  · -- `e(M) ≤ 3`.  Evenness sharpens `s < 8` to `s ∈ {0, 2, 4, 6}`.
    have heven : Even s := by rw [hsdef]; exact eM_even G D
    by_cases hle2 : s ≤ 2
    · -- `e(M) ≤ 1` (`s ≤ 2`): NO `P₃` cherry, so the two-hub opposite-twin cut is available.  At
      -- `e(M) = 0` the matching is edgeless (`|Iso| = 8`); at `e(M) = 1` the single edge forces
      -- `|Iso| = 6` exactly, so the (now sorry-free) two-hub machinery applies WITHOUT the false
      -- `|Iso| = 5` corner that broke for `e(M) = 2`.
      obtain ⟨h₁, h₂, a, b, c, d, hdegh₁, hdegh₂, hdega, hdegb, hdegc, hdegd,
        hadj_ah₁, hadj_bh₁, hadj_ch₂, hadj_dh₂,
        hn_h₁h₂, hn_h₁c, hn_h₁d, hn_ah₂, hn_ac, hn_ad, hn_bh₂, hn_bc, hn_bd,
        ne_h₁h₂, ne_h₁a, ne_h₁b, ne_h₁c, ne_h₁d, ne_h₂a, ne_h₂b, ne_h₂c, ne_h₂d,
        ne_ab, ne_ac, ne_ad, ne_bc, ne_bd, ne_cd⟩ :=
        two_hub_config_fourteen G hm h3 hT h2k2 hC4 hK23 _hiso hle2
      exact two_hub_opposite_twin_cert G h₁ h₂ a b c d hdegh₁ hdegh₂ hdega hdegb hdegc hdegd
        hadj_ah₁ hadj_bh₁ hadj_ch₂ hadj_dh₂ hn_h₁h₂ hn_h₁c hn_h₁d hn_ah₂ hn_ac hn_ad
        hn_bh₂ hn_bc hn_bd ne_h₁h₂ ne_h₁a ne_h₁b ne_h₁c ne_h₁d ne_h₂a ne_h₂b ne_h₂c ne_h₂d
        ne_ab ne_ac ne_ad ne_bc ne_bd ne_cd
    · by_cases hle4 : s ≤ 4
      · -- `e(M) = 2` (`s = 4`).  `M` is a single `P₃` cherry; the two-hub cut is no longer always
        -- available, so we dispatch on the *three-way* alignment dichotomy
        -- `SingleVertexConfig ∨ TwoTwinConfig ∨ TwoHubConfig` (the verified covering combination over
        -- all 535 such graphs), feeding each configuration's fully-proved boundary certificate.
        have hs4 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 4 := by
          obtain ⟨k, hk⟩ := heven
          rw [← hsdef]; omega
        have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G :=
          exists_align_four_config G hm h3 hT h2k2 hC4 hK23 _hiso hs4
        rcases halign with hsv | htt | hth
        · exact singleVertexConfig_to_cut G hsv
        · exact twoTwinConfig_to_cut G htt
        · exact twoHubConfig_to_cut G hth
      · -- `e(M) = 3` (`s = 6`).  Here the two-hub cut is NOT always available (≈ 46 of the 4229
        -- residual graphs admit no two-hub cut); the verified covering combination is
        -- single-vertex + 2-twin + two-hub.  Dispatch on which configuration is present and feed the
        -- corresponding fully-proved boundary certificate.
        -- **Three-way alignment dichotomy (the documented `sorry`).**  At `e(M) = 3` the residual
        -- graph (`δ ≥ 3`, no good triangle / `2K₂` / `C₄` / `K_{2,3}`) admits at least one of the
        -- three signed-cut configurations.  This was verified by enumeration to cover all 4229 such
        -- graphs with zero uncovered; the alignment proof (the analogue of the `n = 13`
        -- `exists_two_hub_or_two_twin_config`) is the single remaining open piece for `s = 6`.
        have hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6 := by
          obtain ⟨k, hk⟩ := heven
          rw [← hsdef]; omega
        have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G :=
          exists_align_six_config G hm h3 hT h2k2 hC4 hK23 _hiso hs6
        rcases halign with hsv | htt | hth
        · exact singleVertexConfig_to_cut G hsv
        · exact twoTwinConfig_to_cut G htt
        · exact twoHubConfig_to_cut G hth
  · -- `e(M) ≥ 4` (`s ≥ 8`).  Three-way alignment dichotomy (single-vertex + 2-twin + two-hub),
    -- replacing the single-twin config (unprovable for the ≈ 91 degree-`5` graphs whose degree-`5`
    -- hub is adjacent to no degree-`4` hub, so no single-twin pair is valid).  Dispatch on `halign8`
    -- and feed each configuration's fully-proved boundary certificate.
    have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G :=
      halign8 G hm h3 hT h2k2 hC4 hK23 _hiso hge
    rcases halign with hsv | htt | hth
    · exact singleVertexConfig_to_cut G hsv
    · exact twoTwinConfig_to_cut G htt
    · exact twoHubConfig_to_cut G hth

end N14

end ACMax
