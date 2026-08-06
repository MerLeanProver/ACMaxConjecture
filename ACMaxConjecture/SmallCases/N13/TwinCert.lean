import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.SignedCut
import ACMaxConjecture.SmallCases.N13.Core
import ACMaxConjecture.SmallCases.N13.TwoHub

/-!
# Existence of a twin signed-cut certificate for `n = 13`

This file assembles the `n = 13` signed-cut certificate from a structural dichotomy on the
degree-3 subgraph `M = G[D]`.  In the residual regime (`δ ≥ 3`, no good triangle, an isolated
degree-3 vertex, no induced `2K₂` on degree-3 vertices, no good `C₄`, no good `K_{2,3}`) one of
two explicit signed cuts is present (`exists_two_hub_or_two_twin_config`), fed to
`algConn_le_two_of_signed`:

* `e(M) = 2` (a single induced `P₃`, forcing degree sequence `[4⁵, 3⁸]` and pairwise
  non-adjacent degree-4 hubs): the **two-hub opposite-twin cut** `P = {h₁, a, b}`,
  `N = {h₂, c, d}` with `h₁ ≠ h₂` two hubs and `a, b` (resp. `c, d`) `M`-isolated twins adjacent
  to `h₁` (resp. `h₂`) but not the opposite hub (`two_hub_opposite_twin_cert`);
* `e(M) ≥ 3`: the **2-twin cut** `P = {t₁, t₂, h}` (two `M`-isolated twins and a common hub `h`)
  against `N = {x, y, z}`, a `P₃` `x–y–z` of `M` avoiding `h` (`two_twin_cut_certificate`).

In each case the boundary counts give `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`, so `algConn G ≤ 2`.

The prior `exists_aligned_P3` (pick the hub first, then align a `P₃` to it) is FALSE — at
`e(M) = 2` every hub meets the unique `P₃` — and has been removed in favour of this dichotomy.
The existence of one of the two configurations (`exists_two_hub_or_two_twin_config`) is now fully
proved: the `e(M) ≥ 3` regime is closed by the structural alignment leaves in `TwinCert13Align`
(`config_from_C5`, `config_from_fat_dom`, `config_from_thin_dom`), so `n = 13` is axiom-clean.
-/

namespace ACMax

open scoped Classical

namespace N13

/-- **2-twin-cut assembly (boundary arithmetic, fully proved).**  Given two distinct `M`-isolated
degree-3 twins `t₁, t₂` sharing a common hub `h` of degree `≤ 5`, and a `P₃` `x–y–z` of degree-3
vertices with `h` (and the twins) non-adjacent to all of `x, y, z`, the 2-twin cut
`P = {t₁, t₂, h}`, `N = {x, y, z}` satisfies `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term
vanishes and the boundary counts give `0 + (2 + 2 + (deg h − 2)) + (2 + 1 + 2) = deg h + 7 ≤ 12`. -/
theorem two_twin_cut_certificate (G : SimpleGraph (Fin 13)) (t₁ t₂ h x y z : Fin 13)
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
    ∃ P N : Finset (Fin 13), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have ne_t₁h : t₁ ≠ h := G.ne_of_adj hadj_t₁h
  have ne_t₂h : t₂ ≠ h := G.ne_of_adj hadj_t₂h
  have hPcard : ({t₁, t₂, h} : Finset (Fin 13)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.card_insert_of_notMem (by simp [ne_t₂h]), Finset.card_singleton]
  have hNcard : ({x, y, z} : Finset (Fin 13)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_xy, ne_xz]),
        Finset.card_insert_of_notMem (by simp [ne_yz]), Finset.card_singleton]
  have hdisjPN : Disjoint ({t₁, t₂, h} : Finset (Fin 13)) ({x, y, z} : Finset (Fin 13)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact ne_t₁x rfl | exact ne_t₁y rfl | exact ne_t₁z rfl
      | exact ne_t₂x rfl | exact ne_t₂y rfl | exact ne_t₂z rfl
      | exact ne_hx rfl | exact ne_hy rfl | exact ne_hz rfl
  have hPN_t₁ : (G.neighborFinset t₁ ∩ ({x, y, z} : Finset (Fin 13))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt₁_x hadj
    · exact hnt₁_y hadj
    · exact hnt₁_z hadj
  have hPN_t₂ : (G.neighborFinset t₂ ∩ ({x, y, z} : Finset (Fin 13))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt₂_x hadj
    · exact hnt₂_y hadj
    · exact hnt₂_z hadj
  have hPN_h : (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 13))).card = 0 := by
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
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({h} : Finset (Fin 13)) ⊆
        G.neighborFinset t₁ ∩ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_t₁h, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₁ ∩
        (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card := by
      calc 1 = ({h} : Finset (Fin 13)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₁)
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegt₁] at hsd
    omega
  have ht₂_le : (G.neighborFinset t₂ \
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({h} : Finset (Fin 13)) ⊆
        G.neighborFinset t₂ ∩ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_t₂h, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₂ ∩
        (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card := by
      calc 1 = ({h} : Finset (Fin 13)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₂)
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegt₂] at hsd
    omega
  have hh_le : (G.neighborFinset h \
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card ≤ 3 := by
    have hsub : ({t₁, t₂} : Finset (Fin 13)) ⊆
        G.neighborFinset h ∩ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_t₁h.symm, by simp⟩
      · exact ⟨hadj_t₂h.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h ∩
        (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card := by
      have h2 : ({t₁, t₂} : Finset (Fin 13)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_t₁t₂]), Finset.card_singleton]
      calc 2 = ({t₁, t₂} : Finset (Fin 13)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h)
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hx_le : (G.neighborFinset x \
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({y} : Finset (Fin 13)) ⊆
        G.neighborFinset x ∩ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_xy, by simp⟩
    have hge : 1 ≤ (G.neighborFinset x ∩
        (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card := by
      calc 1 = ({y} : Finset (Fin 13)).card := (Finset.card_singleton y).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegx] at hsd
    omega
  have hy_le : (G.neighborFinset y \
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card ≤ 1 := by
    have hsub : ({x, z} : Finset (Fin 13)) ⊆
        G.neighborFinset y ∩ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z}) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact ⟨hadj_xy.symm, by simp⟩
      · exact ⟨hadj_yz, by simp⟩
    have hge : 2 ≤ (G.neighborFinset y ∩
        (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card := by
      have h2 : ({x, z} : Finset (Fin 13)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_xz]), Finset.card_singleton]
      calc 2 = ({x, z} : Finset (Fin 13)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegy] at hsd
    omega
  have hz_le : (G.neighborFinset z \
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card ≤ 2 := by
    have hsub : ({y} : Finset (Fin 13)) ⊆
        G.neighborFinset z ∩ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z}) := by
      intro a ha
      rw [Finset.mem_singleton] at ha; subst ha
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_yz.symm, by simp⟩
    have hge : 1 ≤ (G.neighborFinset z ∩
        (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card := by
      calc 1 = ({y} : Finset (Fin 13)).card := (Finset.card_singleton y).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
      (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})
    rw [G.card_neighborFinset_eq_degree, hdegz] at hsd
    omega
  refine ⟨({t₁, t₂, h} : Finset (Fin 13)), ({x, y, z} : Finset (Fin 13)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({t₁, t₂, h} : Finset (Fin 13)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 13))).card
      = (G.neighborFinset t₁ ∩ ({x, y, z} : Finset (Fin 13))).card
        + (G.neighborFinset t₂ ∩ ({x, y, z} : Finset (Fin 13))).card
        + (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 13))).card := by
    rw [Finset.sum_insert (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.sum_insert (by simp [ne_t₂h]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({t₁, t₂, h} : Finset (Fin 13)),
      (G.neighborFinset p \ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card
      = (G.neighborFinset t₁ \ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card
        + (G.neighborFinset t₂ \ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card
        + (G.neighborFinset h \ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_t₁t₂, ne_t₁h]),
        Finset.sum_insert (by simp [ne_t₂h]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({x, y, z} : Finset (Fin 13)),
      (G.neighborFinset q \ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card
      = (G.neighborFinset x \ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card
        + (G.neighborFinset y \ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card
        + (G.neighborFinset z \ (({t₁, t₂, h} : Finset (Fin 13)) ∪ {x, y, z})).card := by
    rw [Finset.sum_insert (by simp [ne_xy, ne_xz]),
        Finset.sum_insert (by simp [ne_yz]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_t₁, hPN_t₂, hPN_h]
  omega

/-- **Signed cut for the `n = 13` sparse-hub residual (assembly).**  The structural dichotomy
`exists_two_hub_or_two_twin_config` supplies either a two-hub opposite-twin configuration
(`e(M) = 2`) or a two-twin configuration (`e(M) ≥ 3`); the corresponding fully-proved boundary
arithmetic (`two_hub_opposite_twin_cert` / `two_twin_cut_certificate`) yields a signed cut with
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`. -/
theorem exists_twin_signed_cert_thirteen (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 13, ({a, b, c, d, e} : Finset (Fin 13)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (_hiso : ∃ t : Fin 13, G.degree t = 3 ∧ ∀ w : Fin 13, G.Adj t w → G.degree w ≠ 3) :
    ∃ P N : Finset (Fin 13), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  -- **Assembly from the structural-existence dichotomy.**  In the residual one of two explicit
  -- signed-cut configurations is present (`exists_two_hub_or_two_twin_config`, the lone open
  -- structural core, nauty-verified): a two-hub opposite-twin configuration (`e(M) = 2` regime,
  -- forced degree sequence `[4⁵, 3⁸]`) handled by `two_hub_opposite_twin_cert`, or a two-twin
  -- configuration (`e(M) ≥ 3` regime) handled by `two_twin_cut_certificate`.  Both boundary
  -- arithmetics are fully proved; only the configuration EXISTENCE is assumed.
  rcases exists_two_hub_or_two_twin_config G hm h3 hT h2k2 hC4 hK23 _hiso with
    ⟨h₁, h₂, a, b, c, d, dh₁, dh₂, da, db, dc, dd, aah₁, abh₁, ach₂, adh₂,
      nh₁h₂, nh₁c, nh₁d, nah₂, nac, nad, nbh₂, nbc, nbd,
      eh₁h₂, eh₁a, eh₁b, eh₁c, eh₁d, eh₂a, eh₂b, eh₂c, eh₂d,
      eab, eac, ead, ebc, ebd, ecd⟩
    | ⟨t₁, t₂, h, x, y, z, dt₁, dt₂, dh, dx, dy, dz, at₁h, at₂h, axy, ayz,
      nt₁x, nt₁y, nt₁z, nt₂x, nt₂y, nt₂z, nhx, nhy, nhz,
      et₁t₂, et₁x, et₁y, et₁z, et₂x, et₂y, et₂z, ehx, ehy, ehz, exy, eyz, exz⟩
  · exact two_hub_opposite_twin_cert G h₁ h₂ a b c d dh₁ dh₂ da db dc dd
      aah₁ abh₁ ach₂ adh₂ nh₁h₂ nh₁c nh₁d nah₂ nac nad nbh₂ nbc nbd
      eh₁h₂ eh₁a eh₁b eh₁c eh₁d eh₂a eh₂b eh₂c eh₂d eab eac ead ebc ebd ecd
  · exact two_twin_cut_certificate G t₁ t₂ h x y z dt₁ dt₂ dh dx dy dz
      at₁h at₂h axy ayz nt₁x nt₁y nt₁z nt₂x nt₂y nt₂z nhx nhy nhz
      et₁t₂ et₁x et₁y et₁z et₂x et₂y et₂z ehx ehy ehz exy eyz exz

end N13

end ACMax
