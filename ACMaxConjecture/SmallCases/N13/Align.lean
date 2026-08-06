import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.SignedCut
import ACMaxConjecture.SmallCases.N13.Struct
import ACMaxConjecture.SmallCases.N13.Core

/-!
# Path-avoiding alignment leaves for the `n = 13` residual (`e(M) ≥ 3` regime)

This file closes the structural alignment for `n = 13`: given the keystone dichotomy
`dominating_edge_or_induced_C5`, in each branch a degree-`≤ 5` hub shared by two `M`-isolated
degree-3 twins avoids a chosen induced `P₃` `x–y–z` of degree-3 vertices, yielding the two-twin
configuration consumed by `two_twin_cut_certificate`.

* `config_from_C5` — the induced `C₅` branch (hub meets `≤ 1` cycle vertex; the rest are a cherry).
* `config_from_fat_dom` — a dominating centre of in-`M`-degree `3` (hub meets `≤ 1` of its three
  `D`-neighbours; two free ones form the cherry around the centre).
* `config_from_thin_dom` — the `M = P₄` thin dominating edge (counting forces a free hub off the
  path with two twin neighbours).
-/

namespace ACMax

open scoped Classical

namespace N13

/-- **The two-twin signed-cut configuration** sought in the `e(M) ≥ 3` regime: two `M`-isolated
degree-3 twins `t₁, t₂` sharing a degree-`≤ 5` hub `h`, an induced `P₃` `x–y–z` of degree-3
vertices avoided by `h`, with the twins (being `M`-isolated) non-adjacent to and distinct from the
path. -/
abbrev TwoTwinConfig (G : SimpleGraph (Fin 13)) : Prop :=
  ∃ t₁ t₂ h x y z : Fin 13,
    G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.degree h ≤ 5 ∧
    G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
    G.Adj t₁ h ∧ G.Adj t₂ h ∧ G.Adj x y ∧ G.Adj y z ∧
    ¬G.Adj t₁ x ∧ ¬G.Adj t₁ y ∧ ¬G.Adj t₁ z ∧
    ¬G.Adj t₂ x ∧ ¬G.Adj t₂ y ∧ ¬G.Adj t₂ z ∧
    ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z ∧
    t₁ ≠ t₂ ∧ t₁ ≠ x ∧ t₁ ≠ y ∧ t₁ ≠ z ∧ t₂ ≠ x ∧ t₂ ≠ y ∧ t₂ ≠ z ∧
    h ≠ x ∧ h ≠ y ∧ h ≠ z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z

/-- **Distinctness from a five-element literal.**  A `Finset` literal `{a, b, c, d, e}` of
cardinality `5` has its five entries pairwise distinct. -/
theorem distinct_five (a b c d e : Fin 13)
    (h : ({a, b, c, d, e} : Finset (Fin 13)).card = 5) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  classical
  have b3 : ∀ x y z : Fin 13, ({x, y, z} : Finset (Fin 13)).card ≤ 3 := by
    intro x y z
    have h1 := Finset.card_insert_le x ({y, z} : Finset (Fin 13))
    have h2 := Finset.card_insert_le y ({z} : Finset (Fin 13))
    simp only [Finset.card_singleton] at *
    omega
  have b4 : ∀ w x y z : Fin 13, ({w, x, y, z} : Finset (Fin 13)).card ≤ 4 := by
    intro w x y z
    have h1 := Finset.card_insert_le w ({x, y, z} : Finset (Fin 13))
    have h2 := b3 x y z
    omega
  have ha : a ∉ ({b, c, d, e} : Finset (Fin 13)) := by
    intro hmem
    have : ({a, b, c, d, e} : Finset (Fin 13)).card ≤ 4 := by
      rw [Finset.insert_eq_self.mpr hmem]; exact b4 b c d e
    omega
  have hca4 : ({b, c, d, e} : Finset (Fin 13)).card = 4 := by
    rw [Finset.card_insert_of_notMem ha] at h; omega
  have hb : b ∉ ({c, d, e} : Finset (Fin 13)) := by
    intro hmem
    have : ({b, c, d, e} : Finset (Fin 13)).card ≤ 3 := by
      rw [Finset.insert_eq_self.mpr hmem]; exact b3 c d e
    omega
  have hcb3 : ({c, d, e} : Finset (Fin 13)).card = 3 := by
    rw [Finset.card_insert_of_notMem hb] at hca4; omega
  have hc : c ∉ ({d, e} : Finset (Fin 13)) := by
    intro hmem
    have h1 := Finset.card_insert_le d ({e} : Finset (Fin 13))
    have : ({c, d, e} : Finset (Fin 13)).card ≤ 2 := by
      rw [Finset.insert_eq_self.mpr hmem]
      simp only [Finset.card_singleton] at *; omega
    omega
  have hcc2 : ({d, e} : Finset (Fin 13)).card = 2 := by
    rw [Finset.card_insert_of_notMem hc] at hcb3; omega
  have hd : d ≠ e := by
    intro hmem
    rw [hmem] at hcc2
    simp at hcc2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, hb.1, hb.2.1, hb.2.2, hc.1, hc.2, hd⟩

/-- **Two-twin configuration assembly.**  From two `M`-isolated degree-3 twins `t₁ ≠ t₂` sharing a
degree-`≤ 5` hub `h`, and an induced `P₃` `x–y–z` of degree-3 vertices avoided by `h`, the full
two-twin configuration follows: the twins are non-adjacent to and distinct from the path (they have
no degree-3 neighbour), and `h ≠ x, y, z` (its degree is `≠ 3`, being a twin's neighbour). -/
theorem assemble_two_twin_config (G : SimpleGraph (Fin 13))
    (t₁ t₂ h x y z : Fin 13)
    (ht₁3 : G.degree t₁ = 3) (ht₁iso : ∀ w : Fin 13, G.Adj t₁ w → G.degree w ≠ 3)
    (ht₂3 : G.degree t₂ = 3) (ht₂iso : ∀ w : Fin 13, G.Adj t₂ w → G.degree w ≠ 3)
    (hne12 : t₁ ≠ t₂) (hdh : G.degree h ≤ 5)
    (hat₁ : G.Adj t₁ h) (hat₂ : G.Adj t₂ h)
    (hx3 : G.degree x = 3) (hy3 : G.degree y = 3) (hz3 : G.degree z = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : x ≠ z)
    (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z) :
    TwoTwinConfig G := by
  exact ⟨t₁, t₂, h, x, y, z, ht₁3, ht₂3, hdh, hx3, hy3, hz3,
    hat₁, hat₂, hxy, hyz,
    (fun a => ht₁iso x a hx3), (fun a => ht₁iso y a hy3), (fun a => ht₁iso z a hz3),
    (fun a => ht₂iso x a hx3), (fun a => ht₂iso y a hy3), (fun a => ht₂iso z a hz3),
    hhx, hhy, hhz, hne12,
    (fun e => ht₁iso y (e ▸ hxy) hy3), (fun e => ht₁iso x (e ▸ hxy.symm) hx3),
    (fun e => ht₁iso y (e ▸ hyz.symm) hy3),
    (fun e => ht₂iso y (e ▸ hxy) hy3), (fun e => ht₂iso x (e ▸ hxy.symm) hx3),
    (fun e => ht₂iso y (e ▸ hyz.symm) hy3),
    (fun e => ht₁iso h hat₁ (by rw [e]; exact hx3)),
    (fun e => ht₁iso h hat₁ (by rw [e]; exact hy3)),
    (fun e => ht₁iso h hat₁ (by rw [e]; exact hz3)),
    hxy.ne, hyz.ne, hxz⟩

/-- **`C₅` branch.**  Given an induced `C₅` `v₁–⋯–v₅` of degree-3 vertices and two `M`-isolated
degree-3 twins, a shared degree-4 hub `h` of the twins meets at most one cycle vertex (two adjacent
hits give a good triangle via `hT`, two distance-2 hits a good `C₄` via `hC4`; both packaged in
`hub_meets_path_le_one`); a consecutive triple avoiding that vertex is the cherry. -/
theorem config_from_C5 (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (htwins : ∃ t₁ t₂ : Fin 13, t₁ ≠ t₂ ∧ G.degree t₁ = 3 ∧
      (∀ w : Fin 13, G.Adj t₁ w → G.degree w ≠ 3) ∧ G.degree t₂ = 3 ∧
      (∀ w : Fin 13, G.Adj t₂ w → G.degree w ≠ 3))
    (v₁ v₂ v₃ v₄ v₅ : Fin 13)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3' : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 13)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅) :
    TwoTwinConfig G := by
  obtain ⟨t₁, t₂, hne12, ht₁3, ht₁iso, ht₂3, ht₂iso⟩ := htwins
  have ht₁iso4 : ∀ w : Fin 13, G.Adj t₁ w → 4 ≤ G.degree w := fun w hw => by
    have := ht₁iso w hw; have := h3 w; omega
  have ht₂iso4 : ∀ w : Fin 13, G.Adj t₂ w → 4 ≤ G.degree w := fun w hw => by
    have := ht₂iso w hw; have := h3 w; omega
  obtain ⟨h, hdeg4, hat₁, hat₂⟩ :=
    exists_shared_deg4_hub G hm h3 t₁ t₂ ht₁3 ht₂3 ht₁iso4 ht₂iso4
  obtain ⟨d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ :=
    distinct_five v₁ v₂ v₃ v₄ v₅ hcard5
  have P123 := hub_meets_path_le_one G hT hC4 hdeg4 hd1 hd2 hd3' e12 e23 n13 d12 d23 d13
  have P234 := hub_meets_path_le_one G hT hC4 hdeg4 hd2 hd3' hd4 e23 e34 n24 d23 d34 d24
  have P345 := hub_meets_path_le_one G hT hC4 hdeg4 hd3' hd4 hd5 e34 e45 n35 d34 d45 d35
  have P451 := hub_meets_path_le_one G hT hC4 hdeg4 hd4 hd5 hd1 e45 e51
    (fun hh => n14 hh.symm) d45 d15.symm d14.symm
  have P512 := hub_meets_path_le_one G hT hC4 hdeg4 hd5 hd1 hd2 e51 e12
    (fun hh => n25 hh.symm) d15.symm d12 d25.symm
  have not12 : ¬(G.Adj h v₁ ∧ G.Adj h v₂) := P123.1
  have not23 : ¬(G.Adj h v₂ ∧ G.Adj h v₃) := P123.2.1
  have not13 : ¬(G.Adj h v₁ ∧ G.Adj h v₃) := P123.2.2
  have not34 : ¬(G.Adj h v₃ ∧ G.Adj h v₄) := P234.2.1
  have not24 : ¬(G.Adj h v₂ ∧ G.Adj h v₄) := P234.2.2
  have not45 : ¬(G.Adj h v₄ ∧ G.Adj h v₅) := P345.2.1
  have not35 : ¬(G.Adj h v₃ ∧ G.Adj h v₅) := P345.2.2
  have not41 : ¬(G.Adj h v₄ ∧ G.Adj h v₁) := P451.2.2
  have not52 : ¬(G.Adj h v₅ ∧ G.Adj h v₂) := P512.2.2
  have hdh : G.degree h ≤ 5 := by omega
  by_cases ha1 : G.Adj h v₁
  · exact assemble_two_twin_config G t₁ t₂ h v₂ v₃ v₄ ht₁3 ht₁iso ht₂3 ht₂iso hne12 hdh
      hat₁ hat₂ hd2 hd3' hd4 e23 e34 d24
      (fun hv => not12 ⟨ha1, hv⟩) (fun hv => not13 ⟨ha1, hv⟩) (fun hv => not41 ⟨hv, ha1⟩)
  · by_cases ha2 : G.Adj h v₂
    · exact assemble_two_twin_config G t₁ t₂ h v₃ v₄ v₅ ht₁3 ht₁iso ht₂3 ht₂iso hne12 hdh
        hat₁ hat₂ hd3' hd4 hd5 e34 e45 d35
        (fun hv => not23 ⟨ha2, hv⟩) (fun hv => not24 ⟨ha2, hv⟩) (fun hv => not52 ⟨hv, ha2⟩)
    · by_cases ha3 : G.Adj h v₃
      · exact assemble_two_twin_config G t₁ t₂ h v₄ v₅ v₁ ht₁3 ht₁iso ht₂3 ht₂iso hne12 hdh
          hat₁ hat₂ hd4 hd5 hd1 e45 e51 d14.symm
          (fun hv => not34 ⟨ha3, hv⟩) (fun hv => not35 ⟨ha3, hv⟩) ha1
      · by_cases ha4 : G.Adj h v₄
        · exact assemble_two_twin_config G t₁ t₂ h v₅ v₁ v₂ ht₁3 ht₁iso ht₂3 ht₂iso hne12 hdh
            hat₁ hat₂ hd5 hd1 hd2 e51 e12 d25.symm
            (fun hv => not45 ⟨ha4, hv⟩) ha1 ha2
        · exact assemble_two_twin_config G t₁ t₂ h v₁ v₂ v₃ ht₁3 ht₁iso ht₂3 ht₂iso hne12 hdh
            hat₁ hat₂ hd1 hd2 hd3' e12 e23 d13 ha1 ha2 ha3

/-- **Fat dominating-centre branch.**  A degree-3 centre `c` whose three neighbours `n₁, n₂, n₃`
are all degree-3 (in-`M`-degree `3`) has no hub neighbour, so a shared degree-4 hub `h` of two
`M`-isolated twins is non-adjacent to `c`.  Then `h` meets at most one of `n₁, n₂, n₃` (two hits
form an induced `C₄` `h–nᵢ–c–nⱼ–h` of degree-sum `13`, ruled out by `hC4`); two free neighbours and
`c` form the cherry `nᵢ–c–nⱼ`. -/
theorem config_from_fat_dom (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (htwins : ∃ t₁ t₂ : Fin 13, t₁ ≠ t₂ ∧ G.degree t₁ = 3 ∧
      (∀ w : Fin 13, G.Adj t₁ w → G.degree w ≠ 3) ∧ G.degree t₂ = 3 ∧
      (∀ w : Fin 13, G.Adj t₂ w → G.degree w ≠ 3))
    (c n₁ n₂ n₃ : Fin 13) (hc3 : G.degree c = 3)
    (hd1 : G.degree n₁ = 3) (hd2 : G.degree n₂ = 3) (hd3' : G.degree n₃ = 3)
    (ne12 : n₁ ≠ n₂) (ne13 : n₁ ≠ n₃) (ne23 : n₂ ≠ n₃)
    (a1 : G.Adj c n₁) (a2 : G.Adj c n₂) (a3 : G.Adj c n₃)
    (hcnbhd : ∀ w : Fin 13, G.Adj c w → w = n₁ ∨ w = n₂ ∨ w = n₃) :
    TwoTwinConfig G := by
  obtain ⟨t₁, t₂, htne, ht₁3, ht₁iso, ht₂3, ht₂iso⟩ := htwins
  have ht₁iso4 : ∀ w : Fin 13, G.Adj t₁ w → 4 ≤ G.degree w := fun w hw => by
    have := ht₁iso w hw; have := h3 w; omega
  have ht₂iso4 : ∀ w : Fin 13, G.Adj t₂ w → 4 ≤ G.degree w := fun w hw => by
    have := ht₂iso w hw; have := h3 w; omega
  obtain ⟨h, hdeg4, hat₁, hat₂⟩ :=
    exists_shared_deg4_hub G hm h3 t₁ t₂ ht₁3 ht₂3 ht₁iso4 ht₂iso4
  have hdh : G.degree h ≤ 5 := by omega
  have hhc : ¬G.Adj h c := by
    intro hadj
    rcases hcnbhd h hadj.symm with e | e | e <;> rw [e] at hdeg4 <;> omega
  have hmeet : ∀ i j : Fin 13, G.degree i = 3 → G.degree j = 3 →
      G.Adj c i → G.Adj c j → i ≠ j → ¬(G.Adj h i ∧ G.Adj h j) := by
    rintro i j hi3 hj3 ci cj hij ⟨hhi, hhj⟩
    have nij : ¬G.Adj i j := fun aij =>
      hT ⟨c, i, j, ci.ne, hij, cj.ne, ci, aij, cj, by omega⟩
    exact hC4 ⟨h, i, c, j,
      card_four_thirteen h i c j (by rintro rfl; omega) (by rintro rfl; omega)
        (by rintro rfl; omega) ci.ne.symm hij cj.ne,
      hhi, ci.symm, cj, hhj.symm, hhc, nij, by omega⟩
  have not12 := hmeet n₁ n₂ hd1 hd2 a1 a2 ne12
  have not13 := hmeet n₁ n₃ hd1 hd3' a1 a3 ne13
  have not23 := hmeet n₂ n₃ hd2 hd3' a2 a3 ne23
  by_cases hb1 : G.Adj h n₁
  · exact assemble_two_twin_config G t₁ t₂ h n₂ c n₃ ht₁3 ht₁iso ht₂3 ht₂iso htne hdh
      hat₁ hat₂ hd2 hc3 hd3' a2.symm a3 ne23
      (fun hv => not12 ⟨hb1, hv⟩) hhc (fun hv => not13 ⟨hb1, hv⟩)
  · by_cases hb2 : G.Adj h n₂
    · exact assemble_two_twin_config G t₁ t₂ h n₁ c n₃ ht₁3 ht₁iso ht₂3 ht₂iso htne hdh
        hat₁ hat₂ hd1 hc3 hd3' a1.symm a3 ne13
        hb1 hhc (fun hv => not23 ⟨hb2, hv⟩)
    · exact assemble_two_twin_config G t₁ t₂ h n₁ c n₂ ht₁3 ht₁iso ht₂3 ht₂iso htne hdh
        hat₁ hat₂ hd1 hc3 hd2 a1.symm a2 ne12 hb1 hhc hb2

/-- **`e(M)` formula in a dominating-edge case.**  When every `M`-edge meets the edge `{c₁, c₂}`,
`∑_{v∈D}|N v ∩ D| = 2·e(M) = 2·inM(c₁) + 2·inM(c₂) − 2` (the shared edge `c₁c₂` is double-counted),
written additively to avoid `ℕ` subtraction. -/
theorem thin_eM_formula (G : SimpleGraph (Fin 13)) (D : Finset (Fin 13))
    (c₁ c₂ : Fin 13) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 13, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    ∑ v ∈ D, (G.neighborFinset v ∩ D).card + 2
      = 2 * (G.neighborFinset c₁ ∩ D).card + 2 * (G.neighborFinset c₂ ∩ D).card := by
  classical
  have hc2mem : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have hpos1 : 1 ≤ (G.neighborFinset c₁ ∩ D).card := Finset.card_pos.mpr ⟨c₂, hc2mem⟩
  have hpos2 : 1 ≤ (G.neighborFinset c₂ ∩ D).card := Finset.card_pos.mpr ⟨c₁, hc1mem⟩
  have hsub : ({c₁, c₂} : Finset (Fin 13)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl; exacts [hc1D, hc2D]
  have hsplit :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
        + ∑ v ∈ ({c₁, c₂} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_sdiff hsub
  have hpair : ∑ v ∈ ({c₁, c₂} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
      = (G.neighborFinset c₁ ∩ D).card + (G.neighborFinset c₂ ∩ D).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hScong :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
        = ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 13)),
          (G.neighborFinset v ∩ ({c₁, c₂} : Finset (Fin 13))).card := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_sdiff] at hv
    obtain ⟨hvD, hvnot⟩ := hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvnot
    congr 1
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hvw : G.Adj v w := (G.mem_neighborFinset _ _).mp hwN
      rcases hcov v w hvD hwD hvw with e | e | e | e
      · exact absurd e hvnot.1
      · exact absurd e hvnot.2
      · exact Finset.mem_inter.mpr ⟨hwN, by rw [e]; simp⟩
      · exact Finset.mem_inter.mpr ⟨hwN, by rw [e]; simp⟩
    · intro w hw
      obtain ⟨hwN, hwm⟩ := Finset.mem_inter.mp hw
      exact Finset.mem_inter.mpr ⟨hwN, hsub hwm⟩
  rw [hScong,
    cross_count_thirteen G (D \ ({c₁, c₂} : Finset (Fin 13)))
      ({c₁, c₂} : Finset (Fin 13))] at hsplit
  have hpair2 : ∑ w ∈ ({c₁, c₂} : Finset (Fin 13)),
        (G.neighborFinset w ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card
      = (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card
        + (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have he1 : (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card
      = (G.neighborFinset c₁ ∩ D).card - 1 := by
    have hset : G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))
        = (G.neighborFinset c₁ ∩ D).erase c₂ := by
      apply Finset.Subset.antisymm
      · intro w hw
        obtain ⟨hwN, hwS⟩ := Finset.mem_inter.mp hw
        rw [Finset.mem_sdiff] at hwS
        obtain ⟨hwD, hwnot⟩ := hwS
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwnot
        exact Finset.mem_erase.mpr ⟨hwnot.2, Finset.mem_inter.mpr ⟨hwN, hwD⟩⟩
      · intro w hw
        rw [Finset.mem_erase] at hw
        obtain ⟨hwc2, hwND⟩ := hw
        obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hwND
        have hwc1 : w ≠ c₁ := fun e => by
          rw [e] at hwN; exact G.irrefl ((G.mem_neighborFinset _ _).mp hwN)
        exact Finset.mem_inter.mpr ⟨hwN,
          Finset.mem_sdiff.mpr ⟨hwD, by simp [hwc1, hwc2]⟩⟩
    rw [hset, Finset.card_erase_of_mem hc2mem]
  have he2 : (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card
      = (G.neighborFinset c₂ ∩ D).card - 1 := by
    have hset : G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))
        = (G.neighborFinset c₂ ∩ D).erase c₁ := by
      apply Finset.Subset.antisymm
      · intro w hw
        obtain ⟨hwN, hwS⟩ := Finset.mem_inter.mp hw
        rw [Finset.mem_sdiff] at hwS
        obtain ⟨hwD, hwnot⟩ := hwS
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwnot
        exact Finset.mem_erase.mpr ⟨hwnot.1, Finset.mem_inter.mpr ⟨hwN, hwD⟩⟩
      · intro w hw
        rw [Finset.mem_erase] at hw
        obtain ⟨hwc1, hwND⟩ := hw
        obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hwND
        have hwc2 : w ≠ c₂ := fun e => by
          rw [e] at hwN; exact G.irrefl ((G.mem_neighborFinset _ _).mp hwN)
        exact Finset.mem_inter.mpr ⟨hwN,
          Finset.mem_sdiff.mpr ⟨hwD, by simp [hwc1, hwc2]⟩⟩
    rw [hset, Finset.card_erase_of_mem hc1mem]
  rw [hpair2, hpair, he1, he2] at hsplit
  omega

/-- **Thin dominating-edge branch (`M = P₄`).**  When the dominating edge `{c₁, c₂}` has both
endpoints of in-`M`-degree exactly `2`, the degree-3 subgraph is a `P₄` `L₁–c₁–c₂–L₂`.  Counting
forces `|D| = 8`, `|Hub| = 5` and exactly one edge inside `Hub`; the `≤ 4` hubs touching the path
`L₁–c₁–c₂` leave a free degree-4 hub `f`, which (having `≤ 1` hub-neighbour) has `≥ 3` degree-3
neighbours, at most one of which is `L₂`, yielding two `M`-isolated twins for the cherry
`L₁–c₁–c₂`. -/
theorem config_from_thin_dom (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (D : Finset (Fin 13)) (hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3)
    (c₁ c₂ : Fin 13) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hdom : ∀ p q : Fin 13, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    TwoTwinConfig G := by
  classical
  set Hub : Finset (Fin 13) := Finset.univ.filter (fun w => 4 ≤ G.degree w) with hHubdef
  have hmemHub : ∀ v : Fin 13, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hDHpart : ∀ x : Fin 13, x ∈ D ∨ x ∈ Hub := fun x => by
    rcases Nat.lt_or_ge (G.degree x) 4 with h | h
    · exact Or.inl ((hmemD x).mpr (by have := h3 x; omega))
    · exact Or.inr ((hmemHub x).mpr h)
  have hdisjDH : Disjoint D Hub := by
    rw [Finset.disjoint_left]; intro x hx hx'
    have := (hmemD x).mp hx; have := (hmemHub x).mp hx'; omega
  have hunionDH : D ∪ Hub = Finset.univ := by
    ext x; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDHpart x
  have hcard13 : D.card + Hub.card = 13 := by
    have h := Finset.card_union_of_disjoint hdisjDH
    rw [hunionDH, Finset.card_univ, Fintype.card_fin] at h; omega
  have hsum44 : ∑ v : Fin 13, G.degree v = 44 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hDeq : D = Finset.univ.filter (fun w => G.degree w = 3) := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmemD v]
  have hD8 : 8 ≤ D.card := by rw [hDeq]; exact (residual_hub_card_le_five G hm h3).2
  have hc1deg : G.degree c₁ = 3 := (hmemD c₁).mp hc1D
  have hc2deg : G.degree c₂ = 3 := (hmemD c₂).mp hc2D
  -- Extract the path leaves `L₁` (of `c₁`) and `L₂` (of `c₂`).
  have hc2mem1 : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem2 : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have herase1 : ((G.neighborFinset c₁ ∩ D).erase c₂).card = 1 := by
    rw [Finset.card_erase_of_mem hc2mem1, hin1]
  have herase2 : ((G.neighborFinset c₂ ∩ D).erase c₁).card = 1 := by
    rw [Finset.card_erase_of_mem hc1mem2, hin2]
  obtain ⟨L₁, hL1eq⟩ := Finset.card_eq_one.mp herase1
  obtain ⟨L₂, hL2eq⟩ := Finset.card_eq_one.mp herase2
  have hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁} := by
    rw [← Finset.insert_erase hc2mem1, hL1eq]
  have hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂} := by
    rw [← Finset.insert_erase hc1mem2, hL2eq]
  have hL1mem : L₁ ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by rw [hL1eq]; simp
  rw [Finset.mem_erase] at hL1mem
  obtain ⟨hL1nc2, hL1ND⟩ := hL1mem
  obtain ⟨hL1N, hL1D⟩ := Finset.mem_inter.mp hL1ND
  have hac1L1 : G.Adj c₁ L₁ := (G.mem_neighborFinset _ _).mp hL1N
  have hL1nc1 : L₁ ≠ c₁ := fun e => G.irrefl (e ▸ hac1L1)
  have hL1deg : G.degree L₁ = 3 := (hmemD L₁).mp hL1D
  have hnL1c2 : ¬G.Adj L₁ c₂ := fun hadj =>
    hT ⟨c₁, L₁, c₂, hac1L1.ne, hL1nc2, hc12.ne, hac1L1, hadj, hc12, by omega⟩
  -- `N L₁ ∩ D = {c₁}`, so `inM L₁ = 1`.
  have hNL1D : G.neighborFinset L₁ ∩ D = {c₁} := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj L₁ w := (G.mem_neighborFinset _ _).mp hwN
      rcases hdom L₁ w hL1D hwD hadj with e | e | e | e
      · exact absurd e hL1nc1
      · exact absurd e hL1nc2
      · rw [e]; simp
      · exact absurd (e ▸ hadj) hnL1c2
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩
  -- `M`-isolation away from the path.
  have hiso_char : ∀ w : Fin 13, w ∈ D → w ≠ c₁ → w ≠ c₂ → w ≠ L₁ → w ≠ L₂ →
      ∀ u : Fin 13, G.Adj w u → G.degree u ≠ 3 := by
    intro w hwD hwc1 hwc2 hwL1 hwL2 u huw hu3
    have huD : u ∈ D := (hmemD u).mpr hu3
    rcases hdom w u hwD huD huw with e | e | e | e
    · exact hwc1 e
    · exact hwc2 e
    · have : w ∈ G.neighborFinset c₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ huw).symm, hwD⟩
      rw [hNc1D] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact hwc2 h
      · exact hwL1 h
    · have : w ∈ G.neighborFinset c₂ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ huw).symm, hwD⟩
      rw [hNc2D] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact hwc1 h
      · exact hwL2 h
  -- Degree split `deg v = |N v ∩ D| + |N v ∩ Hub|`.
  have hdegsplit : ∀ v : Fin 13,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
      (hdisjDH.mono_left Finset.inter_subset_right).mono_right Finset.inter_subset_right
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hunionDH, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  -- The counting equations feeding `omega`.
  have hSinM : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6 := by
    have := thin_eM_formula G D c₁ c₂ hc1D hc2D hc12 hdom
    rw [hin1, hin2] at this; omega
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplitD : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = ∑ v ∈ D, G.degree v := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun v _ => hdegsplit v)
  have hsplitH : ∑ u ∈ Hub, (G.neighborFinset u ∩ D).card
      + ∑ u ∈ Hub, (G.neighborFinset u ∩ Hub).card = ∑ u ∈ Hub, G.degree u := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun u _ => hdegsplit u)
  have hAll : ∑ v ∈ D, G.degree v + ∑ u ∈ Hub, G.degree u = 44 := by
    rw [← Finset.sum_union hdisjDH, hunionDH]; exact hsum44
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ u ∈ Hub, (G.neighborFinset u ∩ D).card := cross_count_thirteen G D Hub
  rw [hSinM, hsumDdeg] at hsplitD
  rw [hsumDdeg] at hAll
  have hDcard : D.card = 8 := by omega
  have hHubcard : Hub.card = 5 := by omega
  have hInner2 : ∑ u ∈ Hub, (G.neighborFinset u ∩ Hub).card = 2 := by omega
  have hSdegH20 : ∑ u ∈ Hub, G.degree u = 20 := by omega
  -- Cardinalities of the path-touching hub sets.
  set A1 : Finset (Fin 13) := G.neighborFinset L₁ ∩ Hub with hA1def
  set A2 : Finset (Fin 13) := G.neighborFinset c₁ ∩ Hub with hA2def
  set A3 : Finset (Fin 13) := G.neighborFinset c₂ ∩ Hub with hA3def
  have hNL1Dcard : (G.neighborFinset L₁ ∩ D).card = 1 := by rw [hNL1D]; simp
  have hA1card : A1.card = 2 := by
    have := hdegsplit L₁; rw [hNL1Dcard, hL1deg, ← hA1def] at this; omega
  have hA2card : A2.card = 1 := by
    have := hdegsplit c₁; rw [hin1, hc1deg, ← hA2def] at this; omega
  have hA3card : A3.card = 1 := by
    have := hdegsplit c₂; rw [hin2, hc2deg, ← hA3def] at this; omega
  have hUcard : (A1 ∪ A2 ∪ A3).card ≤ 4 := by
    calc (A1 ∪ A2 ∪ A3).card ≤ (A1 ∪ A2).card + A3.card := Finset.card_union_le _ _
      _ ≤ (A1.card + A2.card) + A3.card := by
          have := Finset.card_union_le A1 A2; omega
      _ = 4 := by rw [hA1card, hA2card, hA3card]
  have hfree : 0 < (Hub \ (A1 ∪ A2 ∪ A3)).card := by
    have := Finset.card_le_card_sdiff_add_card (s := Hub) (t := A1 ∪ A2 ∪ A3)
    omega
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hfree
  rw [Finset.mem_sdiff] at hf
  obtain ⟨hf_in, hf_notU⟩ := hf
  simp only [Finset.mem_union, not_or] at hf_notU
  obtain ⟨⟨hfnA1, hfnA2⟩, hfnA3⟩ := hf_notU
  have hf_nL1 : ¬G.Adj L₁ f := fun a =>
    hfnA1 (hA1def ▸ Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr a, hf_in⟩)
  have hf_nc1 : ¬G.Adj c₁ f := fun a =>
    hfnA2 (hA2def ▸ Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr a, hf_in⟩)
  have hf_nc2 : ¬G.Adj c₂ f := fun a =>
    hfnA3 (hA3def ▸ Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr a, hf_in⟩)
  have hf4le : 4 ≤ G.degree f := (hmemHub f).mp hf_in
  -- `deg f = 4`.
  have hfdeg4 : G.degree f = 4 := by
    have hsum_erase : G.degree f + ∑ u ∈ Hub.erase f, G.degree u = ∑ u ∈ Hub, G.degree u :=
      Finset.add_sum_erase _ (fun u => G.degree u) hf_in
    have herasege : 4 * (Hub.erase f).card ≤ ∑ u ∈ Hub.erase f, G.degree u := by
      have hb : ∀ u ∈ Hub.erase f, 4 ≤ G.degree u := fun u hu =>
        (hmemHub u).mp (Finset.mem_of_mem_erase hu)
      have h := Finset.card_nsmul_le_sum (Hub.erase f) (fun u => G.degree u) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    have herasecard : (Hub.erase f).card = 4 := by
      rw [Finset.card_erase_of_mem hf_in, hHubcard]
    rw [herasecard] at herasege
    omega
  -- `f` has at most one hub-neighbour.
  have hfHub1 : (G.neighborFinset f ∩ Hub).card ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcon
    obtain ⟨hpN, hpHub⟩ := Finset.mem_inter.mp hp
    obtain ⟨hqN, hqHub⟩ := Finset.mem_inter.mp hq
    have hfp : G.Adj f p := (G.mem_neighborFinset _ _).mp hpN
    have hfq : G.Adj f q := (G.mem_neighborFinset _ _).mp hqN
    have hfnep : f ≠ p := hfp.ne
    have hfneq : f ≠ q := hfq.ne
    have hsubset : ({f, p, q} : Finset (Fin 13)) ⊆ Hub := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl; exacts [hf_in, hpHub, hqHub]
    have hle := Finset.sum_le_sum_of_subset (f := fun u => (G.neighborFinset u ∩ Hub).card) hsubset
    rw [hInner2] at hle
    have hexp : ∑ u ∈ ({f, p, q} : Finset (Fin 13)), (G.neighborFinset u ∩ Hub).card
        = (G.neighborFinset f ∩ Hub).card + (G.neighborFinset p ∩ Hub).card
          + (G.neighborFinset q ∩ Hub).card := by
      rw [Finset.sum_insert (by simp [hfnep, hfneq]), Finset.sum_insert (by simp [hpq]),
        Finset.sum_singleton, ← add_assoc]
    have hpge1 : 1 ≤ (G.neighborFinset p ∩ Hub).card :=
      Finset.card_pos.mpr ⟨f, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hfp.symm, hf_in⟩⟩
    have hqge1 : 1 ≤ (G.neighborFinset q ∩ Hub).card :=
      Finset.card_pos.mpr ⟨f, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hfq.symm, hf_in⟩⟩
    rw [hexp] at hle
    omega
  -- `f` has `≥ 3` degree-3 neighbours.
  have hfD3 : 3 ≤ (G.neighborFinset f ∩ D).card := by have := hdegsplit f; omega
  -- Two twins among them (discarding `L₂`).
  have herasecard : 2 ≤ ((G.neighborFinset f ∩ D).erase L₂).card := by
    rcases em (L₂ ∈ G.neighborFinset f ∩ D) with hmem | hmem
    · have := Finset.card_erase_add_one hmem; omega
    · rw [Finset.erase_eq_of_notMem hmem]; omega
  obtain ⟨t₁, ht₁mem, t₂, ht₂mem, ht12⟩ := Finset.one_lt_card.mp herasecard
  have htprop : ∀ t : Fin 13, t ∈ (G.neighborFinset f ∩ D).erase L₂ →
      G.Adj f t ∧ G.degree t = 3 ∧ (∀ u : Fin 13, G.Adj t u → G.degree u ≠ 3) := by
    intro t ht
    rw [Finset.mem_erase] at ht
    obtain ⟨htL2, htND⟩ := ht
    obtain ⟨htN, htD⟩ := Finset.mem_inter.mp htND
    have hadjft : G.Adj f t := (G.mem_neighborFinset _ _).mp htN
    have htnc1 : t ≠ c₁ := fun e => hf_nc1 ((e ▸ hadjft).symm)
    have htnc2 : t ≠ c₂ := fun e => hf_nc2 ((e ▸ hadjft).symm)
    have htnL1 : t ≠ L₁ := fun e => hf_nL1 ((e ▸ hadjft).symm)
    exact ⟨hadjft, (hmemD t).mp htD, hiso_char t htD htnc1 htnc2 htnL1 htL2⟩
  obtain ⟨haf1, ht₁3, ht₁iso⟩ := htprop t₁ ht₁mem
  obtain ⟨haf2, ht₂3, ht₂iso⟩ := htprop t₂ ht₂mem
  exact assemble_two_twin_config G t₁ t₂ f L₁ c₁ c₂ ht₁3 ht₁iso ht₂3 ht₂iso ht12
    (by omega) haf1.symm haf2.symm hL1deg hc1deg hc2deg hac1L1.symm hc12 hL1nc2
    (fun a => hf_nL1 a.symm) (fun a => hf_nc1 a.symm) (fun a => hf_nc2 a.symm)

end N13

end ACMax
