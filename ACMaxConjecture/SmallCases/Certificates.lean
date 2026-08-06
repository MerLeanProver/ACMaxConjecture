import ACMaxConjecture.Base
import ACMaxConjecture.Reduction.Residual

/-!
# Generic signed-cut boundary certificates

Every certificate here is local: it depends only on six distinguished vertices
and the boundary inequality
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  Neither the graph order nor its total
edge count appears.  The former per-order copies for `n = 15,16,17,18` are
therefore one theorem over an arbitrary finite vertex type.

Contents (all axiom-clean):

* the three config predicates `SingleVertexConfig`, `TwoTwinConfig`, `TwoHubConfig`;
* the three boundary certificates `single_vertex_cut_certificate`, `two_hub_opposite_twin_cert`,
  `two_twin_cut_certificate`;
* `dense_two_twin_assemble` (packaging two isolated twins + a hub + a cherry into `TwoTwinConfig`);
* the `_to_cut` wrappers feeding each config to its certificate.
-/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The single-vertex signed-cut configuration** for the `e(M) = 3` regime: a degree-`3` vertex
`v` adjacent to two hubs `h₁, h₂`, and a cherry (induced `P₃`) `x–y–z` of degree-`3` vertices, with
the combined cross/hub side condition.  Consumed by `single_vertex_cut_certificate`. -/
def SingleVertexConfig (G : SimpleGraph (V)) : Prop :=
  ∃ v h₁ h₂ x y z : V,
    G.degree v = 3 ∧ G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
    G.Adj v h₁ ∧ G.Adj v h₂ ∧ G.Adj x y ∧ G.Adj y z ∧ ¬G.Adj x z ∧
    2 * (∑ p ∈ ({v, h₁, h₂} : Finset (V)),
        (G.neighborFinset p ∩ ({x, y, z} : Finset (V))).card)
        + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * (if G.Adj h₁ h₂ then 1 else 0) ∧
    h₁ ≠ h₂ ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z ∧
    h₁ ≠ x ∧ h₁ ≠ y ∧ h₁ ≠ z ∧ h₂ ≠ x ∧ h₂ ≠ y ∧ h₂ ≠ z ∧
    x ≠ y ∧ y ≠ z ∧ x ≠ z

/-- **The 2-twin signed-cut configuration** for the `e(M) = 3` regime: two `M`-isolated degree-`3`
twins `t₁, t₂` sharing a hub `h` of degree `≤ 5`, against a cherry `x–y–z` avoiding `h` and the
twins.  Consumed by `two_twin_cut_certificate`. -/
def TwoTwinConfig (G : SimpleGraph (V)) : Prop :=
  ∃ t₁ t₂ h x y z : V,
    G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.degree h ≤ 5 ∧
    G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
    G.Adj t₁ h ∧ G.Adj t₂ h ∧ G.Adj x y ∧ G.Adj y z ∧
    ¬G.Adj t₁ x ∧ ¬G.Adj t₁ y ∧ ¬G.Adj t₁ z ∧
    ¬G.Adj t₂ x ∧ ¬G.Adj t₂ y ∧ ¬G.Adj t₂ z ∧
    ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z ∧
    t₁ ≠ t₂ ∧ t₁ ≠ x ∧ t₁ ≠ y ∧ t₁ ≠ z ∧ t₂ ≠ x ∧ t₂ ≠ y ∧ t₂ ≠ z ∧
    h ≠ x ∧ h ≠ y ∧ h ≠ z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z

/-- **The two-hub opposite-twin signed-cut configuration** for the `e(M) ≤ 3` regime.
Consumed by `two_hub_opposite_twin_cert`. -/
def TwoHubConfig (G : SimpleGraph (V)) : Prop :=
  ∃ h₁ h₂ a b c d : V,
    G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
    G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
    G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj d h₂ ∧
    ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ d ∧
    ¬G.Adj a h₂ ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧
    ¬G.Adj b h₂ ∧ ¬G.Adj b c ∧ ¬G.Adj b d ∧
    h₁ ≠ h₂ ∧ h₁ ≠ a ∧ h₁ ≠ b ∧ h₁ ≠ c ∧ h₁ ≠ d ∧
    h₂ ≠ a ∧ h₂ ≠ b ∧ h₂ ≠ c ∧ h₂ ≠ d ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- **Single-vertex-cut assembly (boundary arithmetic, fully proved).**  Generalizes
`single_twin_cut_certificate_gen`: the apex `v` of `P = {v, h₁, h₂}` need NOT be an `M`-isolated
twin — it is *any* degree-`3` vertex adjacent to `h₁, h₂` — and the cross term `e(P, N)` may be
positive.  Given a cherry (induced `P₃`) `x–y–z` of degree-`3` vertices and the combined side
condition `2·e(P,N) + deg h₁ + deg h₂ ≤ 8 + 2·[h₁∼h₂]` (where `e(P,N) = ∑_{p∈P}|N p ∩ N|` is the
actual cross-edge count), the single-vertex cut `P = {v, h₁, h₂}`, `N = {x, y, z}` satisfies
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The proof uses the global degree-sum identity
`4·e(P,N) + e(P,Z) + e(N,Z) = 2·e(P,N) + ∑_P deg + ∑_N deg − 2·e_in(P) − 2·e_in(N)` (the cross
count `e(P,N) = e(N,P)` via `cross_count`), with `∑_P deg = 3 + deg h₁ + deg h₂`,
`∑_N deg = 9`, `e_in(P) ≥ 2 + [h₁∼h₂]`, `e_in(N) = 2`, closing by the side condition. -/
theorem single_vertex_cut_certificate (G : SimpleGraph (V)) (v h₁ h₂ x y z : V)
    (hdegv : G.degree v = 3)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hadj_vh₁ : G.Adj v h₁) (hadj_vh₂ : G.Adj v h₂)
    (hadj_xy : G.Adj x y) (hadj_yz : G.Adj y z) (_hnadj_xz : ¬G.Adj x z)
    (hside : 2 * (∑ p ∈ ({v, h₁, h₂} : Finset (V)),
        (G.neighborFinset p ∩ ({x, y, z} : Finset (V))).card)
        + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * (if G.Adj h₁ h₂ then 1 else 0))
    (ne_h₁h₂ : h₁ ≠ h₂)
    (ne_vx : v ≠ x) (ne_vy : v ≠ y) (ne_vz : v ≠ z)
    (ne_h₁x : h₁ ≠ x) (ne_h₁y : h₁ ≠ y) (ne_h₁z : h₁ ≠ z)
    (ne_h₂x : h₂ ≠ x) (ne_h₂y : h₂ ≠ y) (ne_h₂z : h₂ ≠ z)
    (ne_xy : x ≠ y) (ne_yz : y ≠ z) (ne_xz : x ≠ z) :
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have ne_vh₁ : v ≠ h₁ := G.ne_of_adj hadj_vh₁
  have ne_vh₂ : v ≠ h₂ := G.ne_of_adj hadj_vh₂
  set ind : ℕ := (if G.Adj h₁ h₂ then 1 else 0) with hind
  have hPcard : ({v, h₁, h₂} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_vh₁, ne_vh₂]),
        Finset.card_insert_of_notMem (by simp [ne_h₁h₂]), Finset.card_singleton]
  have hNcard : ({x, y, z} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_xy, ne_xz]),
        Finset.card_insert_of_notMem (by simp [ne_yz]), Finset.card_singleton]
  have hdisjPN : Disjoint ({v, h₁, h₂} : Finset (V)) ({x, y, z} : Finset (V)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact ne_vx rfl | exact ne_vy rfl | exact ne_vz rfl
      | exact ne_h₁x rfl | exact ne_h₁y rfl | exact ne_h₁z rfl
      | exact ne_h₂x rfl | exact ne_h₂y rfl | exact ne_h₂z rfl
  have decomp : ∀ w : V,
      (G.neighborFinset w ∩ ({v, h₁, h₂} : Finset (V))).card
        + (G.neighborFinset w ∩ ({x, y, z} : Finset (V))).card
        + (G.neighborFinset w \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card
      = G.degree w := by
    intro w
    have hdj : Disjoint (G.neighborFinset w ∩ ({v, h₁, h₂} : Finset (V)))
        (G.neighborFinset w ∩ ({x, y, z} : Finset (V))) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hdisjPN) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have h1 : (G.neighborFinset w ∩ ({v, h₁, h₂} : Finset (V))).card
        + (G.neighborFinset w ∩ ({x, y, z} : Finset (V))).card
        = (G.neighborFinset w ∩ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card := by
      rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdj]
    have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset w)
      (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree] at h2
    omega
  have hcc := cross_count G ({v, h₁, h₂} : Finset (V)) ({x, y, z} : Finset (V))
  have e_crossP : ∑ p ∈ ({v, h₁, h₂} : Finset (V)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (V))).card
      = (G.neighborFinset v ∩ ({x, y, z} : Finset (V))).card
        + (G.neighborFinset h₁ ∩ ({x, y, z} : Finset (V))).card
        + (G.neighborFinset h₂ ∩ ({x, y, z} : Finset (V))).card := by
    rw [Finset.sum_insert (by simp [ne_vh₁, ne_vh₂]),
        Finset.sum_insert (by simp [ne_h₁h₂]), Finset.sum_singleton]; ring
  have e_crossN : ∑ q ∈ ({x, y, z} : Finset (V)),
      (G.neighborFinset q ∩ ({v, h₁, h₂} : Finset (V))).card
      = (G.neighborFinset x ∩ ({v, h₁, h₂} : Finset (V))).card
        + (G.neighborFinset y ∩ ({v, h₁, h₂} : Finset (V))).card
        + (G.neighborFinset z ∩ ({v, h₁, h₂} : Finset (V))).card := by
    rw [Finset.sum_insert (by simp [ne_xy, ne_xz]),
        Finset.sum_insert (by simp [ne_yz]), Finset.sum_singleton]; ring
  have e_Pout : ∑ p ∈ ({v, h₁, h₂} : Finset (V)),
      (G.neighborFinset p \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card
      = (G.neighborFinset v \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset h₁ \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset h₂ \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_vh₁, ne_vh₂]),
        Finset.sum_insert (by simp [ne_h₁h₂]), Finset.sum_singleton]; ring
  have e_Nout : ∑ q ∈ ({x, y, z} : Finset (V)),
      (G.neighborFinset q \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card
      = (G.neighborFinset x \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset y \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset z \ (({v, h₁, h₂} : Finset (V)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_xy, ne_xz]),
        Finset.sum_insert (by simp [ne_yz]), Finset.sum_singleton]; ring
  have hpv : 2 ≤ (G.neighborFinset v ∩ ({v, h₁, h₂} : Finset (V))).card := by
    have hsub : ({h₁, h₂} : Finset (V)) ⊆
        G.neighborFinset v ∩ ({v, h₁, h₂} : Finset (V)) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_vh₁, by simp⟩
      · exact ⟨hadj_vh₂, by simp⟩
    have h2 : ({h₁, h₂} : Finset (V)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [ne_h₁h₂]), Finset.card_singleton]
    calc 2 = ({h₁, h₂} : Finset (V)).card := h2.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hph1 : 1 + ind ≤ (G.neighborFinset h₁ ∩ ({v, h₁, h₂} : Finset (V))).card := by
    by_cases hadj12 : G.Adj h₁ h₂
    · have hs1 : ind = 1 := by rw [hind]; simp [hadj12]
      have hsub : ({v, h₂} : Finset (V)) ⊆
          G.neighborFinset h₁ ∩ ({v, h₁, h₂} : Finset (V)) := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rw [Finset.mem_inter, G.mem_neighborFinset]
        rcases ha with rfl | rfl
        · exact ⟨hadj_vh₁.symm, by simp⟩
        · exact ⟨hadj12, by simp⟩
      have h2 : ({v, h₂} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_vh₂]), Finset.card_singleton]
      rw [hs1]
      calc 1 + 1 = ({v, h₂} : Finset (V)).card := by rw [h2]
        _ ≤ _ := Finset.card_le_card hsub
    · have hs0 : ind = 0 := by rw [hind]; simp [hadj12]
      rw [hs0]
      have hsub : ({v} : Finset (V)) ⊆
          G.neighborFinset h₁ ∩ ({v, h₁, h₂} : Finset (V)) := by
        intro a ha
        rw [Finset.mem_singleton] at ha; subst ha
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨hadj_vh₁.symm, by simp⟩
      calc 1 + 0 = ({v} : Finset (V)).card := by simp
        _ ≤ _ := Finset.card_le_card hsub
  have hph2 : 1 + ind ≤ (G.neighborFinset h₂ ∩ ({v, h₁, h₂} : Finset (V))).card := by
    by_cases hadj12 : G.Adj h₁ h₂
    · have hs1 : ind = 1 := by rw [hind]; simp [hadj12]
      have hsub : ({v, h₁} : Finset (V)) ⊆
          G.neighborFinset h₂ ∩ ({v, h₁, h₂} : Finset (V)) := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rw [Finset.mem_inter, G.mem_neighborFinset]
        rcases ha with rfl | rfl
        · exact ⟨hadj_vh₂.symm, by simp⟩
        · exact ⟨hadj12.symm, by simp⟩
      have h2 : ({v, h₁} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_vh₁]), Finset.card_singleton]
      rw [hs1]
      calc 1 + 1 = ({v, h₁} : Finset (V)).card := by rw [h2]
        _ ≤ _ := Finset.card_le_card hsub
    · have hs0 : ind = 0 := by rw [hind]; simp [hadj12]
      rw [hs0]
      have hsub : ({v} : Finset (V)) ⊆
          G.neighborFinset h₂ ∩ ({v, h₁, h₂} : Finset (V)) := by
        intro a ha
        rw [Finset.mem_singleton] at ha; subst ha
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨hadj_vh₂.symm, by simp⟩
      calc 1 + 0 = ({v} : Finset (V)).card := by simp
        _ ≤ _ := Finset.card_le_card hsub
  have hnx : 1 ≤ (G.neighborFinset x ∩ ({x, y, z} : Finset (V))).card := by
    have hsub : ({y} : Finset (V)) ⊆ G.neighborFinset x ∩ ({x, y, z} : Finset (V)) := by
      intro a ha; rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj_xy, by simp⟩
    calc 1 = ({y} : Finset (V)).card := (Finset.card_singleton y).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hny : 2 ≤ (G.neighborFinset y ∩ ({x, y, z} : Finset (V))).card := by
    have hsub : ({x, z} : Finset (V)) ⊆
        G.neighborFinset y ∩ ({x, y, z} : Finset (V)) := by
      intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_xy.symm, by simp⟩
      · exact ⟨hadj_yz, by simp⟩
    have h2 : ({x, z} : Finset (V)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [ne_xz]), Finset.card_singleton]
    calc 2 = ({x, z} : Finset (V)).card := h2.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hnz : 1 ≤ (G.neighborFinset z ∩ ({x, y, z} : Finset (V))).card := by
    have hsub : ({y} : Finset (V)) ⊆ G.neighborFinset z ∩ ({x, y, z} : Finset (V)) := by
      intro a ha; rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj_yz.symm, by simp⟩
    calc 1 = ({y} : Finset (V)).card := (Finset.card_singleton y).symm
      _ ≤ _ := Finset.card_le_card hsub
  have dv := decomp v; have dh1 := decomp h₁; have dh2 := decomp h₂
  have dx := decomp x; have dy := decomp y; have dz := decomp z
  rw [hdegv] at dv; rw [hdegx] at dx; rw [hdegy] at dy; rw [hdegz] at dz
  rw [e_crossP, e_crossN] at hcc
  rw [e_crossP] at hside
  refine ⟨({v, h₁, h₂} : Finset (V)), ({x, y, z} : Finset (V)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  rw [e_crossP, e_Pout, e_Nout, hPcard]
  omega

/-- An aligned degree-three vertex, two degree-four hubs, and a degree-three
cherry give a signed cut.  This is the compact interface used by the `n = 12`
residual proof. -/
theorem aligned_single_vertex_cut_certificate (G : SimpleGraph (V)) (t h₁ h₂ x y z : V)
    (hdegt : G.degree t = 3) (hdegh₁ : G.degree h₁ = 4) (hdegh₂ : G.degree h₂ = 4)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hadj_th₁ : G.Adj t h₁) (hadj_th₂ : G.Adj t h₂)
    (hadj_xy : G.Adj x y) (hadj_yz : G.Adj y z) (hnadj_xz : ¬G.Adj x z)
    (hnt_x : ¬G.Adj t x) (hnt_y : ¬G.Adj t y) (hnt_z : ¬G.Adj t z)
    (hnh₁_x : ¬G.Adj h₁ x) (hnh₁_y : ¬G.Adj h₁ y) (hnh₁_z : ¬G.Adj h₁ z)
    (hnh₂_x : ¬G.Adj h₂ x) (hnh₂_y : ¬G.Adj h₂ y) (hnh₂_z : ¬G.Adj h₂ z)
    (ne_h₁h₂ : h₁ ≠ h₂) (ne_tx : t ≠ x) (ne_ty : t ≠ y) (ne_tz : t ≠ z)
    (ne_xy : x ≠ y) (ne_yz : y ≠ z) (ne_xz : x ≠ z) :
    ∃ P N : Finset V, Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  have ne_th₁ : t ≠ h₁ := by rintro rfl; omega
  have ne_th₂ : t ≠ h₂ := by rintro rfl; omega
  have ne_h₁x : h₁ ≠ x := by rintro rfl; omega
  have ne_h₁y : h₁ ≠ y := by rintro rfl; omega
  have ne_h₁z : h₁ ≠ z := by rintro rfl; omega
  have ne_h₂x : h₂ ≠ x := by rintro rfl; omega
  have ne_h₂y : h₂ ≠ y := by rintro rfl; omega
  have ne_h₂z : h₂ ≠ z := by rintro rfl; omega
  have cross_t :
      (G.neighborFinset t ∩ ({x, y, z} : Finset V)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    rcases ha with ⟨hadj, hmem⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt_x hadj
    · exact hnt_y hadj
    · exact hnt_z hadj
  have cross_h₁ :
      (G.neighborFinset h₁ ∩ ({x, y, z} : Finset V)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    rcases ha with ⟨hadj, hmem⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnh₁_x hadj
    · exact hnh₁_y hadj
    · exact hnh₁_z hadj
  have cross_h₂ :
      (G.neighborFinset h₂ ∩ ({x, y, z} : Finset V)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    rcases ha with ⟨hadj, hmem⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnh₂_x hadj
    · exact hnh₂_y hadj
    · exact hnh₂_z hadj
  have hside : 2 * (∑ p ∈ ({t, h₁, h₂} : Finset V),
      (G.neighborFinset p ∩ ({x, y, z} : Finset V)).card)
      + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * (if G.Adj h₁ h₂ then 1 else 0) := by
    rw [Finset.sum_insert (by simp [ne_th₁, ne_th₂]),
      Finset.sum_insert (by simp [ne_h₁h₂]), Finset.sum_singleton,
      cross_t, cross_h₁, cross_h₂, hdegh₁, hdegh₂]
    omega
  exact single_vertex_cut_certificate G t h₁ h₂ x y z
    hdegt hdegx hdegy hdegz hadj_th₁ hadj_th₂ hadj_xy hadj_yz hnadj_xz hside
    ne_h₁h₂ ne_tx ne_ty ne_tz ne_h₁x ne_h₁y ne_h₁z ne_h₂x ne_h₂y ne_h₂z
    ne_xy ne_yz ne_xz

/-- **Two-hub opposite-twin cut assembly (boundary arithmetic, fully proved).**  Given two
distinct degree-4 hubs `h₁, h₂` with `h₁ ≁ h₂`, and four distinct degree-3 `M`-isolated twins
`a, b` adjacent to `h₁` but not `h₂`, and `c, d` adjacent to `h₂` but not `h₁`, with all six
vertices distinct and the twins pairwise non-adjacent to the opposite hub and to one another's
"column", the two-hub cut `P = {h₁, a, b}`, `N = {h₂, c, d}` satisfies
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term vanishes and the boundary counts give
`0 + (2 + 2 + (deg h₁ − 2)) + (2 + 2 + (deg h₂ − 2)) = deg h₁ + deg h₂ + 4 = 12`. -/
theorem two_hub_opposite_twin_cert (G : SimpleGraph (V)) (h₁ h₂ a b c d : V)
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
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have hPcard : ({h₁, a, b} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₁a, ne_h₁b]),
        Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
  have hNcard : ({h₂, c, d} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₂c, ne_h₂d]),
        Finset.card_insert_of_notMem (by simp [ne_cd]), Finset.card_singleton]
  have hdisjPN : Disjoint ({h₁, a, b} : Finset (V)) ({h₂, c, d} : Finset (V)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;>
      first
      | exact ne_h₁h₂ rfl | exact ne_h₁c rfl | exact ne_h₁d rfl
      | exact ne_h₂a rfl.symm | exact ne_ac rfl | exact ne_ad rfl
      | exact ne_h₂b rfl.symm | exact ne_bc rfl | exact ne_bd rfl
  -- Cross term `e(P, N) = 0`.
  have hPN_h₁ : (G.neighborFinset h₁ ∩ ({h₂, c, d} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn_h₁h₂ hadj
    · exact hn_h₁c hadj
    · exact hn_h₁d hadj
  have hPN_a : (G.neighborFinset a ∩ ({h₂, c, d} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn_ah₂ hadj
    · exact hn_ac hadj
    · exact hn_ad hadj
  have hPN_b : (G.neighborFinset b ∩ ({h₂, c, d} : Finset (V))).card = 0 := by
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
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({a, b} : Finset (V)) ⊆
        G.neighborFinset h₁ ∩ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hadj_ah₁.symm, by simp⟩
      · exact ⟨hadj_bh₁.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₁ ∩
        (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card := by
      have h2 : ({a, b} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
      calc 2 = ({a, b} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁)
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegh₁] at hsd
    omega
  have hh₂_le : (G.neighborFinset h₂ \
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({c, d} : Finset (V)) ⊆
        G.neighborFinset h₂ ∩ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hadj_ch₂.symm, by simp⟩
      · exact ⟨hadj_dh₂.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₂ ∩
        (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card := by
      have h2 : ({c, d} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_cd]), Finset.card_singleton]
      calc 2 = ({c, d} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂)
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegh₂] at hsd
    omega
  have ha_le : (G.neighborFinset a \
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₁} : Finset (V)) ⊆
        G.neighborFinset a ∩ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_ah₁, by simp⟩
    have hge : 1 ≤ (G.neighborFinset a ∩
        (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₁} : Finset (V)).card := (Finset.card_singleton h₁).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset a)
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdega] at hsd
    omega
  have hb_le : (G.neighborFinset b \
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₁} : Finset (V)) ⊆
        G.neighborFinset b ∩ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_bh₁, by simp⟩
    have hge : 1 ≤ (G.neighborFinset b ∩
        (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₁} : Finset (V)).card := (Finset.card_singleton h₁).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset b)
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegb] at hsd
    omega
  have hc_le : (G.neighborFinset c \
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₂} : Finset (V)) ⊆
        G.neighborFinset c ∩ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_ch₂, by simp⟩
    have hge : 1 ≤ (G.neighborFinset c ∩
        (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₂} : Finset (V)).card := (Finset.card_singleton h₂).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset c)
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegc] at hsd
    omega
  have hd_le : (G.neighborFinset d \
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₂} : Finset (V)) ⊆
        G.neighborFinset d ∩ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_dh₂, by simp⟩
    have hge : 1 ≤ (G.neighborFinset d ∩
        (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₂} : Finset (V)).card := (Finset.card_singleton h₂).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset d)
      (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegd] at hsd
    omega
  refine ⟨({h₁, a, b} : Finset (V)), ({h₂, c, d} : Finset (V)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({h₁, a, b} : Finset (V)),
      (G.neighborFinset p ∩ ({h₂, c, d} : Finset (V))).card
      = (G.neighborFinset h₁ ∩ ({h₂, c, d} : Finset (V))).card
        + (G.neighborFinset a ∩ ({h₂, c, d} : Finset (V))).card
        + (G.neighborFinset b ∩ ({h₂, c, d} : Finset (V))).card := by
    rw [Finset.sum_insert (by simp [ne_h₁a, ne_h₁b]),
        Finset.sum_insert (by simp [ne_ab]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({h₁, a, b} : Finset (V)),
      (G.neighborFinset p \ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card
      = (G.neighborFinset h₁ \ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card
        + (G.neighborFinset a \ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card
        + (G.neighborFinset b \ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card := by
    rw [Finset.sum_insert (by simp [ne_h₁a, ne_h₁b]),
        Finset.sum_insert (by simp [ne_ab]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({h₂, c, d} : Finset (V)),
      (G.neighborFinset q \ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card
      = (G.neighborFinset h₂ \ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card
        + (G.neighborFinset c \ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card
        + (G.neighborFinset d \ (({h₁, a, b} : Finset (V)) ∪ {h₂, c, d})).card := by
    rw [Finset.sum_insert (by simp [ne_h₂c, ne_h₂d]),
        Finset.sum_insert (by simp [ne_cd]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_h₁, hPN_a, hPN_b]
  omega

/-- **2-twin-cut assembly for `n = 17` (boundary arithmetic, fully proved).**  Port of the `n = 17`
`two_twin_cut_certificate`: two distinct `M`-isolated degree-`3` twins `t₁, t₂` sharing a common hub
`h` of degree `≤ 5`, and a `P₃` `x–y–z` of degree-`3` vertices with `h` (and the twins) non-adjacent
to all of `x, y, z`.  The 2-twin cut `P = {t₁, t₂, h}`, `N = {x, y, z}` satisfies
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term vanishes and the boundary counts give
`0 + (2 + 2 + (deg h − 2)) + (2 + 1 + 2) = deg h + 7 ≤ 12`. -/
theorem two_twin_cut_certificate (G : SimpleGraph (V)) (t₁ t₂ h x y z : V)
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
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have ne_t₁h : t₁ ≠ h := G.ne_of_adj hadj_t₁h
  have ne_t₂h : t₂ ≠ h := G.ne_of_adj hadj_t₂h
  have hPcard : ({t₁, t₂, h} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.card_insert_of_notMem (by simp [ne_t₂h]), Finset.card_singleton]
  have hNcard : ({x, y, z} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_xy, ne_xz]),
        Finset.card_insert_of_notMem (by simp [ne_yz]), Finset.card_singleton]
  have hdisjPN : Disjoint ({t₁, t₂, h} : Finset (V)) ({x, y, z} : Finset (V)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact ne_t₁x rfl | exact ne_t₁y rfl | exact ne_t₁z rfl
      | exact ne_t₂x rfl | exact ne_t₂y rfl | exact ne_t₂z rfl
      | exact ne_hx rfl | exact ne_hy rfl | exact ne_hz rfl
  have hPN_t₁ : (G.neighborFinset t₁ ∩ ({x, y, z} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt₁_x hadj
    · exact hnt₁_y hadj
    · exact hnt₁_z hadj
  have hPN_t₂ : (G.neighborFinset t₂ ∩ ({x, y, z} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt₂_x hadj
    · exact hnt₂_y hadj
    · exact hnt₂_z hadj
  have hPN_h : (G.neighborFinset h ∩ ({x, y, z} : Finset (V))).card = 0 := by
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
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({h} : Finset (V)) ⊆
        G.neighborFinset t₁ ∩ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_t₁h, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₁ ∩
        (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card := by
      calc 1 = ({h} : Finset (V)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₁)
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegt₁] at hsd
    omega
  have ht₂_le : (G.neighborFinset t₂ \
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({h} : Finset (V)) ⊆
        G.neighborFinset t₂ ∩ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_t₂h, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₂ ∩
        (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card := by
      calc 1 = ({h} : Finset (V)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₂)
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegt₂] at hsd
    omega
  have hh_le : (G.neighborFinset h \
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card ≤ 3 := by
    have hsub : ({t₁, t₂} : Finset (V)) ⊆
        G.neighborFinset h ∩ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_t₁h.symm, by simp⟩
      · exact ⟨hadj_t₂h.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h ∩
        (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card := by
      have h2 : ({t₁, t₂} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_t₁t₂]), Finset.card_singleton]
      calc 2 = ({t₁, t₂} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h)
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hx_le : (G.neighborFinset x \
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({y} : Finset (V)) ⊆
        G.neighborFinset x ∩ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_xy, by simp⟩
    have hge : 1 ≤ (G.neighborFinset x ∩
        (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card := by
      calc 1 = ({y} : Finset (V)).card := (Finset.card_singleton y).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegx] at hsd
    omega
  have hy_le : (G.neighborFinset y \
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card ≤ 1 := by
    have hsub : ({x, z} : Finset (V)) ⊆
        G.neighborFinset y ∩ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_xy.symm, by simp⟩
      · exact ⟨hadj_yz, by simp⟩
    have hge : 2 ≤ (G.neighborFinset y ∩
        (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card := by
      have h2 : ({x, z} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_xz]), Finset.card_singleton]
      calc 2 = ({x, z} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegy] at hsd
    omega
  have hz_le : (G.neighborFinset z \
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({y} : Finset (V)) ⊆
        G.neighborFinset z ∩ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_yz.symm, by simp⟩
    have hge : 1 ≤ (G.neighborFinset z ∩
        (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card := by
      calc 1 = ({y} : Finset (V)).card := (Finset.card_singleton y).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
      (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegz] at hsd
    omega
  refine ⟨({t₁, t₂, h} : Finset (V)), ({x, y, z} : Finset (V)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({t₁, t₂, h} : Finset (V)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (V))).card
      = (G.neighborFinset t₁ ∩ ({x, y, z} : Finset (V))).card
        + (G.neighborFinset t₂ ∩ ({x, y, z} : Finset (V))).card
        + (G.neighborFinset h ∩ ({x, y, z} : Finset (V))).card := by
    rw [Finset.sum_insert (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.sum_insert (by simp [ne_t₂h]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({t₁, t₂, h} : Finset (V)),
      (G.neighborFinset p \ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card
      = (G.neighborFinset t₁ \ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset t₂ \ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset h \ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.sum_insert (by simp [ne_t₂h]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({x, y, z} : Finset (V)),
      (G.neighborFinset q \ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card
      = (G.neighborFinset x \ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset y \ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset z \ (({t₁, t₂, h} : Finset (V)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_xy, ne_xz]),
        Finset.sum_insert (by simp [ne_yz]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_t₁, hPN_t₂, hPN_h]
  omega

omit [DecidableEq V] in
/-- **Two-twin assembly.**  Two `M`-isolated degree-`3` twins `t₁, t₂` sharing a degree-`4` hub `h`
that avoids a cherry `x–y–z` package into the `TwoTwinConfig` existential. -/
theorem dense_two_twin_assemble (G : SimpleGraph (V)) (t₁ t₂ h x y z : V)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3) (hhdeg4 : G.degree h = 4)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h) (hxyA : G.Adj x y) (hyzA : G.Adj y z)
    (ht1iso : ∀ w : V, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : V, G.Adj t₂ w → G.degree w ≠ 3)
    (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z)
    (ht12 : t₁ ≠ t₂) (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z) :
    ∃ t₁' t₂' h' x' y' z' : V,
      G.degree t₁' = 3 ∧ G.degree t₂' = 3 ∧ G.degree h' ≤ 5 ∧
      G.degree x' = 3 ∧ G.degree y' = 3 ∧ G.degree z' = 3 ∧
      G.Adj t₁' h' ∧ G.Adj t₂' h' ∧ G.Adj x' y' ∧ G.Adj y' z' ∧
      ¬G.Adj t₁' x' ∧ ¬G.Adj t₁' y' ∧ ¬G.Adj t₁' z' ∧
      ¬G.Adj t₂' x' ∧ ¬G.Adj t₂' y' ∧ ¬G.Adj t₂' z' ∧
      ¬G.Adj h' x' ∧ ¬G.Adj h' y' ∧ ¬G.Adj h' z' ∧
      t₁' ≠ t₂' ∧ t₁' ≠ x' ∧ t₁' ≠ y' ∧ t₁' ≠ z' ∧ t₂' ≠ x' ∧ t₂' ≠ y' ∧ t₂' ≠ z' ∧
      h' ≠ x' ∧ h' ≠ y' ∧ h' ≠ z' ∧ x' ≠ y' ∧ y' ≠ z' ∧ x' ≠ z' := by
  exact ⟨t₁, t₂, h, x, y, z, ht1deg, ht2deg, by omega, hdegx, hdegy, hdegz,
    hAt1h, hAt2h, hxyA, hyzA,
    (fun hadj => ht1iso x hadj hdegx), (fun hadj => ht1iso y hadj hdegy),
    (fun hadj => ht1iso z hadj hdegz),
    (fun hadj => ht2iso x hadj hdegx), (fun hadj => ht2iso y hadj hdegy),
    (fun hadj => ht2iso z hadj hdegz),
    hhx, hhy, hhz, ht12,
    (by rintro rfl; exact ht1iso y hxyA hdegy),
    (by rintro rfl; exact ht1iso z hyzA hdegz),
    (by rintro rfl; exact ht1iso y hyzA.symm hdegy),
    (by rintro rfl; exact ht2iso y hxyA hdegy),
    (by rintro rfl; exact ht2iso z hyzA hdegz),
    (by rintro rfl; exact ht2iso y hyzA.symm hdegy),
    (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
    hxy_ne, hyz_ne, hxz_ne⟩

/-- **The hub-triangle signed-cut configuration** for the `e(M) = 3`, `|Hub| = 7` corner: three
pairwise-adjacent hubs `h₁, h₂, h₃` (a triangle) of combined degree `≤ 13`, against a cherry
(induced `P₃`) `x–y–z` of degree-`3` vertices that all three hubs avoid.  The triangle's three
internal edges absorb `6` of the boundary; `e(P, N) = 0`; so the boundary total is
`(∑ deg hubs) − 6 + 5 = (∑ deg hubs) − 1 ≤ 12`.  Consumed by `hub_triangle_cut_certificate`. -/
def HubTriangleConfig (G : SimpleGraph (V)) : Prop :=
  ∃ h₁ h₂ h₃ x y z : V,
    G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
    G.Adj h₁ h₂ ∧ G.Adj h₁ h₃ ∧ G.Adj h₂ h₃ ∧
    G.Adj x y ∧ G.Adj y z ∧
    ¬G.Adj h₁ x ∧ ¬G.Adj h₁ y ∧ ¬G.Adj h₁ z ∧
    ¬G.Adj h₂ x ∧ ¬G.Adj h₂ y ∧ ¬G.Adj h₂ z ∧
    ¬G.Adj h₃ x ∧ ¬G.Adj h₃ y ∧ ¬G.Adj h₃ z ∧
    G.degree h₁ + G.degree h₂ + G.degree h₃ ≤ 13 ∧
    h₁ ≠ x ∧ h₁ ≠ y ∧ h₁ ≠ z ∧ h₂ ≠ x ∧ h₂ ≠ y ∧ h₂ ≠ z ∧
    h₃ ≠ x ∧ h₃ ≠ y ∧ h₃ ≠ z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z

/-- **Hub-triangle cut assembly (boundary arithmetic, fully proved).**  Three pairwise-adjacent
hubs `h₁, h₂, h₃` (a triangle) of combined degree `≤ 13`, and a `P₃` `x–y–z` of degree-`3` vertices
with all three hubs non-adjacent to all of `x, y, z`.  The hub-triangle cut `P = {h₁, h₂, h₃}`,
`N = {x, y, z}` satisfies `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term vanishes; each hub
has `≥ 2` internal (triangle) edges, so `e(P,Z) ≤ (∑ deg hubs) − 6`, and `e(N,Z) ≤ 5`, giving
`(∑ deg hubs) − 1 ≤ 12`. -/
theorem hub_triangle_cut_certificate (G : SimpleGraph (V)) (h₁ h₂ h₃ x y z : V)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hadj_12 : G.Adj h₁ h₂) (hadj_13 : G.Adj h₁ h₃) (hadj_23 : G.Adj h₂ h₃)
    (hadj_xy : G.Adj x y) (hadj_yz : G.Adj y z)
    (hn1_x : ¬G.Adj h₁ x) (hn1_y : ¬G.Adj h₁ y) (hn1_z : ¬G.Adj h₁ z)
    (hn2_x : ¬G.Adj h₂ x) (hn2_y : ¬G.Adj h₂ y) (hn2_z : ¬G.Adj h₂ z)
    (hn3_x : ¬G.Adj h₃ x) (hn3_y : ¬G.Adj h₃ y) (hn3_z : ¬G.Adj h₃ z)
    (hside : G.degree h₁ + G.degree h₂ + G.degree h₃ ≤ 13)
    (ne_h₁x : h₁ ≠ x) (ne_h₁y : h₁ ≠ y) (ne_h₁z : h₁ ≠ z)
    (ne_h₂x : h₂ ≠ x) (ne_h₂y : h₂ ≠ y) (ne_h₂z : h₂ ≠ z)
    (ne_h₃x : h₃ ≠ x) (ne_h₃y : h₃ ≠ y) (ne_h₃z : h₃ ≠ z)
    (ne_xy : x ≠ y) (ne_yz : y ≠ z) (ne_xz : x ≠ z) :
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have ne_h₁h₂ : h₁ ≠ h₂ := G.ne_of_adj hadj_12
  have ne_h₁h₃ : h₁ ≠ h₃ := G.ne_of_adj hadj_13
  have ne_h₂h₃ : h₂ ≠ h₃ := G.ne_of_adj hadj_23
  have hPcard : ({h₁, h₂, h₃} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₁h₂, ne_h₁h₃]),
        Finset.card_insert_of_notMem (by simp [ne_h₂h₃]), Finset.card_singleton]
  have hNcard : ({x, y, z} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_xy, ne_xz]),
        Finset.card_insert_of_notMem (by simp [ne_yz]), Finset.card_singleton]
  have hdisjPN : Disjoint ({h₁, h₂, h₃} : Finset (V)) ({x, y, z} : Finset (V)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact ne_h₁x rfl | exact ne_h₁y rfl | exact ne_h₁z rfl
      | exact ne_h₂x rfl | exact ne_h₂y rfl | exact ne_h₂z rfl
      | exact ne_h₃x rfl | exact ne_h₃y rfl | exact ne_h₃z rfl
  have hPN_h₁ : (G.neighborFinset h₁ ∩ ({x, y, z} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn1_x hadj
    · exact hn1_y hadj
    · exact hn1_z hadj
  have hPN_h₂ : (G.neighborFinset h₂ ∩ ({x, y, z} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn2_x hadj
    · exact hn2_y hadj
    · exact hn2_z hadj
  have hPN_h₃ : (G.neighborFinset h₃ ∩ ({x, y, z} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn3_x hadj
    · exact hn3_y hadj
    · exact hn3_z hadj
  have hh1_le : (G.neighborFinset h₁ \
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card + 2 ≤ G.degree h₁ := by
    have hsub : ({h₂, h₃} : Finset (V)) ⊆
        G.neighborFinset h₁ ∩ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_12, by simp⟩
      · exact ⟨hadj_13, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₁ ∩
        (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card := by
      have h2 : ({h₂, h₃} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_h₂h₃]), Finset.card_singleton]
      calc 2 = ({h₂, h₃} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁)
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hh2_le : (G.neighborFinset h₂ \
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card + 2 ≤ G.degree h₂ := by
    have hsub : ({h₁, h₃} : Finset (V)) ⊆
        G.neighborFinset h₂ ∩ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_12.symm, by simp⟩
      · exact ⟨hadj_23, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₂ ∩
        (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card := by
      have h2 : ({h₁, h₃} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_h₁h₃]), Finset.card_singleton]
      calc 2 = ({h₁, h₃} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂)
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hh3_le : (G.neighborFinset h₃ \
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card + 2 ≤ G.degree h₃ := by
    have hsub : ({h₁, h₂} : Finset (V)) ⊆
        G.neighborFinset h₃ ∩ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_13.symm, by simp⟩
      · exact ⟨hadj_23.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₃ ∩
        (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card := by
      have h2 : ({h₁, h₂} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_h₁h₂]), Finset.card_singleton]
      calc 2 = ({h₁, h₂} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₃)
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hx_le : (G.neighborFinset x \
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({y} : Finset (V)) ⊆
        G.neighborFinset x ∩ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_xy, by simp⟩
    have hge : 1 ≤ (G.neighborFinset x ∩
        (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card := by
      calc 1 = ({y} : Finset (V)).card := (Finset.card_singleton y).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegx] at hsd
    omega
  have hy_le : (G.neighborFinset y \
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card ≤ 1 := by
    have hsub : ({x, z} : Finset (V)) ⊆
        G.neighborFinset y ∩ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_xy.symm, by simp⟩
      · exact ⟨hadj_yz, by simp⟩
    have hge : 2 ≤ (G.neighborFinset y ∩
        (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card := by
      have h2 : ({x, z} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_xz]), Finset.card_singleton]
      calc 2 = ({x, z} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegy] at hsd
    omega
  have hz_le : (G.neighborFinset z \
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({y} : Finset (V)) ⊆
        G.neighborFinset z ∩ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_yz.symm, by simp⟩
    have hge : 1 ≤ (G.neighborFinset z ∩
        (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card := by
      calc 1 = ({y} : Finset (V)).card := (Finset.card_singleton y).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
      (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegz] at hsd
    omega
  refine ⟨({h₁, h₂, h₃} : Finset (V)), ({x, y, z} : Finset (V)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({h₁, h₂, h₃} : Finset (V)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (V))).card
      = (G.neighborFinset h₁ ∩ ({x, y, z} : Finset (V))).card
        + (G.neighborFinset h₂ ∩ ({x, y, z} : Finset (V))).card
        + (G.neighborFinset h₃ ∩ ({x, y, z} : Finset (V))).card := by
    rw [Finset.sum_insert (by simp [ne_h₁h₂, ne_h₁h₃]),
        Finset.sum_insert (by simp [ne_h₂h₃]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({h₁, h₂, h₃} : Finset (V)),
      (G.neighborFinset p \ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card
      = (G.neighborFinset h₁ \ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset h₂ \ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset h₃ \ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_h₁h₂, ne_h₁h₃]),
        Finset.sum_insert (by simp [ne_h₂h₃]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({x, y, z} : Finset (V)),
      (G.neighborFinset q \ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card
      = (G.neighborFinset x \ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset y \ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card
        + (G.neighborFinset z \ (({h₁, h₂, h₃} : Finset (V)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_xy, ne_xz]),
        Finset.sum_insert (by simp [ne_yz]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_h₁, hPN_h₂, hPN_h₃]
  omega

/-- **Hub-triangle config yields the signed cut.**  Unpacks a `HubTriangleConfig` and feeds it to
`hub_triangle_cut_certificate`. -/
theorem hubTriangleConfig_to_cut (G : SimpleGraph (V)) (h : HubTriangleConfig G) :
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨h₁, h₂, h₃, x, y, z, hdegx, hdegy, hdegz, hadj_12, hadj_13, hadj_23, hadj_xy, hadj_yz,
    hn1_x, hn1_y, hn1_z, hn2_x, hn2_y, hn2_z, hn3_x, hn3_y, hn3_z, hside,
    ne_h₁x, ne_h₁y, ne_h₁z, ne_h₂x, ne_h₂y, ne_h₂z, ne_h₃x, ne_h₃y, ne_h₃z,
    ne_xy, ne_yz, ne_xz⟩ := h
  exact hub_triangle_cut_certificate G h₁ h₂ h₃ x y z hdegx hdegy hdegz hadj_12 hadj_13 hadj_23
    hadj_xy hadj_yz hn1_x hn1_y hn1_z hn2_x hn2_y hn2_z hn3_x hn3_y hn3_z hside
    ne_h₁x ne_h₁y ne_h₁z ne_h₂x ne_h₂y ne_h₂z ne_h₃x ne_h₃y ne_h₃z ne_xy ne_yz ne_xz

/-- **Single-vertex config yields the signed cut.**  Unpacks a `SingleVertexConfig` and feeds it to
`single_vertex_cut_certificate`. -/
theorem singleVertexConfig_to_cut (G : SimpleGraph (V)) (h : SingleVertexConfig G) :
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
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
`two_twin_cut_certificate`. -/
theorem twoTwinConfig_to_cut (G : SimpleGraph (V)) (h : TwoTwinConfig G) :
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨t₁, t₂, hh, x, y, z, hdegt₁, hdegt₂, hdegh, hdegx, hdegy, hdegz, hadj_t₁h, hadj_t₂h,
    hadj_xy, hadj_yz, hnt₁_x, hnt₁_y, hnt₁_z, hnt₂_x, hnt₂_y, hnt₂_z, hnh_x, hnh_y, hnh_z,
    ne_t₁t₂, ne_t₁x, ne_t₁y, ne_t₁z, ne_t₂x, ne_t₂y, ne_t₂z, ne_hx, ne_hy, ne_hz,
    ne_xy, ne_yz, ne_xz⟩ := h
  exact two_twin_cut_certificate G t₁ t₂ hh x y z hdegt₁ hdegt₂ hdegh hdegx hdegy hdegz
    hadj_t₁h hadj_t₂h hadj_xy hadj_yz hnt₁_x hnt₁_y hnt₁_z hnt₂_x hnt₂_y hnt₂_z hnh_x hnh_y hnh_z
    ne_t₁t₂ ne_t₁x ne_t₁y ne_t₁z ne_t₂x ne_t₂y ne_t₂z ne_hx ne_hy ne_hz ne_xy ne_yz ne_xz

/-- **Two-hub config yields the signed cut.**  Unpacks a `TwoHubConfig` and feeds it to
`two_hub_opposite_twin_cert`. -/
theorem twoHubConfig_to_cut (G : SimpleGraph (V)) (h : TwoHubConfig G) :
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
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


end ACMax
