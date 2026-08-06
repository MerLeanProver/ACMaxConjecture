import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.Dense

/-!
# Deg-`≤ 5` induced-`C₅` two-twin assembly (`n = 18`)

This file ports the induced-`C₅` shared-hub machinery of `TwinCert19Dense` to a hub of degree `4`
*or* `5`, as required by the `e(M) = 5`, `|Hub| = 6` corner of `n = 18` (where the degree-`4`
shared-hub pigeonhole only ties).

* `dense_two_twin_assemble_le5_nineteen` — bundle a deg-`≤ 5` hub with two twins and an avoided
  cherry into a `TwoTwinConfig` (moved here from `TwinCert19TwoHubHub6Deg5`).
* `hub_meets_cycle_dist2_le5_nineteen` — a deg-`≤ 5` hub cannot meet two cycle vertices at
  cycle-distance `2` *unless* it also meets the vertex between them (else an induced `C₄` of degree
  sum `≤ 14`, excluded by `hC4`).
* `hub_cycle_cases_le5_nineteen` — from the five distance-`2` constraints, either the hub avoids a
  consecutive triple of the cycle (a cherry) or it hits a consecutive triple.
* `c5_shared_two_twin_le5_nineteen` — wraps the cases: the cherry branch assembles a
  `TwoTwinConfig` with `k`; the deg-`5` hub hitting three *consecutive* cycle vertices (degree sum
  `5 + 3 + 3 = 11 > 10`, escaping `hT`, and not an induced `C₄`) is closed via `hnonk`, which
  supplies a *different* deg-`≤ 5` hub `h ≠ k` (with two twins) that avoids the hit cherry.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Two-twin bundle assembly with a deg-`≤ 5` hub (`n = 18`).**  Port of `dense_two_twin_assemble`
permitting the hub `h` to have degree `4` or `5` (the two-twin cut certificate allows `deg h ≤ 5`).
The hub being a genuine hub (`4 ≤ deg h`) supplies the `h ≠ x/y/z` distinctnesses. -/
theorem dense_two_twin_assemble_le5_nineteen (G : SimpleGraph (Fin 19)) (t₁ t₂ h x y z : Fin 19)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hhge4 : 4 ≤ G.degree h) (hhle5 : G.degree h ≤ 5)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h) (hxyA : G.Adj x y) (hyzA : G.Adj y z)
    (ht1iso : ∀ w : Fin 19, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 19, G.Adj t₂ w → G.degree w ≠ 3)
    (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z)
    (ht12 : t₁ ≠ t₂) (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z) :
    TwoTwinConfig G := by
  exact ⟨t₁, t₂, h, x, y, z, ht1deg, ht2deg, hhle5, hdegx, hdegy, hdegz,
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

/-- **A deg-`≤ 5` hub avoids distance-`2` cycle hits without the middle (`n = 18`).**  Around an
induced `C₅` of degree-`3` vertices, a deg-`≤ 5` hub `h` adjacent to two vertices `x`, `z` of an
induced path `x ∼ y ∼ z` (`¬ x ∼ z`) must also be adjacent to `y`: otherwise `h ∼ x ∼ y ∼ z ∼ h`
is an induced `C₄` of degree sum `deg h + 9 ≤ 14`, excluded by `hC4`. -/
theorem hub_meets_cycle_dist2_le5_nineteen (G : SimpleGraph (Fin 19))
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    {h x y z : Fin 19} (hhge4 : 4 ≤ G.degree h) (hhle5 : G.degree h ≤ 5)
    (hx : G.degree x = 3) (hy : G.degree y = 3) (hz : G.degree z = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : ¬G.Adj x z)
    (hne_xy : x ≠ y) (hne_yz : y ≠ z) (hne_xz : x ≠ z) :
    ¬(G.Adj h x ∧ G.Adj h z ∧ ¬G.Adj h y) := by
  rintro ⟨hhx, hhz, hhy⟩
  have hne_hx : h ≠ x := by intro e; subst e; omega
  have hne_hy : h ≠ y := by intro e; subst e; omega
  have hne_hz : h ≠ z := by intro e; subst e; omega
  exact hC4 ⟨h, x, y, z,
    card_four_nineteen h x y z hne_hx hne_hy hne_hz hne_xy hne_xz hne_yz,
    hhx, hxy, hyz, hhz.symm, hhy, hxz, by omega⟩

/-- **Cycle-hit cases for a deg-`≤ 5` hub (`n = 18`).**  Around an induced `C₅` `v₁–⋯–v₅` of
degree-`3` vertices, a deg-`≤ 5` hub `h` either avoids three consecutive cycle vertices (one of five
cherries) or hits three consecutive cycle vertices.  The distance-`2` constraints
(`hub_meets_cycle_dist2_le5_nineteen`) rule out every other pattern. -/
theorem hub_cycle_cases_le5_nineteen (G : SimpleGraph (Fin 19))
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (h v₁ v₂ v₃ v₄ v₅ : Fin 19) (hhge4 : 4 ≤ G.degree h) (hhle5 : G.degree h ≤ 5)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3 : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅)
    (d12 : v₁ ≠ v₂) (d13 : v₁ ≠ v₃) (d14 : v₁ ≠ v₄) (d15 : v₁ ≠ v₅)
    (d23 : v₂ ≠ v₃) (d24 : v₂ ≠ v₄) (d25 : v₂ ≠ v₅)
    (d34 : v₃ ≠ v₄) (d35 : v₃ ≠ v₅) (d45 : v₄ ≠ v₅) :
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₃) ∨
    (¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄) ∨
    (¬G.Adj h v₃ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₄ ∧ ¬G.Adj h v₅ ∧ ¬G.Adj h v₁) ∨
    (¬G.Adj h v₅ ∧ ¬G.Adj h v₁ ∧ ¬G.Adj h v₂) ∨
    (G.Adj h v₁ ∧ G.Adj h v₂ ∧ G.Adj h v₃) ∨
    (G.Adj h v₂ ∧ G.Adj h v₃ ∧ G.Adj h v₄) ∨
    (G.Adj h v₃ ∧ G.Adj h v₄ ∧ G.Adj h v₅) ∨
    (G.Adj h v₄ ∧ G.Adj h v₅ ∧ G.Adj h v₁) ∨
    (G.Adj h v₅ ∧ G.Adj h v₁ ∧ G.Adj h v₂) := by
  have C234 := hub_meets_cycle_dist2_le5_nineteen G hC4 hhge4 hhle5 hd2 hd3 hd4 e23 e34 n24
    d23 d34 d24
  have C345 := hub_meets_cycle_dist2_le5_nineteen G hC4 hhge4 hhle5 hd3 hd4 hd5 e34 e45 n35
    d34 d45 d35
  have C451 := hub_meets_cycle_dist2_le5_nineteen G hC4 hhge4 hhle5 hd4 hd5 hd1 e45 e51
    (fun a => n14 a.symm) d45 d15.symm d14.symm
  have C512 := hub_meets_cycle_dist2_le5_nineteen G hC4 hhge4 hhle5 hd5 hd1 hd2 e51 e12
    (fun a => n25 a.symm) d15.symm d12 d25.symm
  have C123 := hub_meets_cycle_dist2_le5_nineteen G hC4 hhge4 hhle5 hd1 hd2 hd3 e12 e23 n13
    d12 d23 d13
  by_cases a1 : G.Adj h v₁
  · by_cases a2 : G.Adj h v₂
    · by_cases a3 : G.Adj h v₃
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, a3⟩)))))
      · by_cases a4 : G.Adj h v₄
        · exact absurd ⟨a2, a4, a3⟩ C234
        · by_cases a5 : G.Adj h v₅
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr ⟨a5, a1, a2⟩))))))))
          · exact Or.inr (Or.inr (Or.inl ⟨a3, a4, a5⟩))
    · by_cases a3 : G.Adj h v₃
      · exact absurd ⟨a1, a3, a2⟩ C123
      · by_cases a4 : G.Adj h v₄
        · by_cases a5 : G.Adj h v₅
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl ⟨a4, a5, a1⟩))))))))
          · exact absurd ⟨a4, a1, a5⟩ C451
        · exact Or.inr (Or.inl ⟨a2, a3, a4⟩)
  · by_cases a2 : G.Adj h v₂
    · by_cases a3 : G.Adj h v₃
      · by_cases a4 : G.Adj h v₄
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a2, a3, a4⟩))))))
        · by_cases a5 : G.Adj h v₅
          · exact absurd ⟨a3, a5, a4⟩ C345
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a4, a5, a1⟩)))
      · by_cases a4 : G.Adj h v₄
        · exact absurd ⟨a2, a4, a3⟩ C234
        · by_cases a5 : G.Adj h v₅
          · exact absurd ⟨a5, a2, a1⟩ C512
          · exact Or.inr (Or.inr (Or.inl ⟨a3, a4, a5⟩))
    · by_cases a3 : G.Adj h v₃
      · by_cases a4 : G.Adj h v₄
        · by_cases a5 : G.Adj h v₅
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨a3, a4, a5⟩)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a5, a1, a2⟩))))
        · by_cases a5 : G.Adj h v₅
          · exact absurd ⟨a3, a5, a4⟩ C345
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a4, a5, a1⟩)))
      · exact Or.inl ⟨a1, a2, a3⟩

/-- **A second hub avoids a degree-`3` vertex with two degree-`3` neighbours (`n = 18`).**  If a
degree-`3` vertex `a` has two distinct degree-`3` neighbours `x, y` and is adjacent to a hub `k`
(`4 ≤ deg k`), then `k` is its *only* hub neighbour: any other hub `h ≠ k` (`4 ≤ deg h`) is
non-adjacent to `a` (else `{x, y, k, h}` would be four distinct neighbours of the degree-`3`
vertex `a`). -/
theorem hub_not_adj_deg3_two_deg3_nbrs (G : SimpleGraph (Fin 19)) (h k a x y : Fin 19)
    (hkh : k ≠ h) (hk4 : 4 ≤ G.degree k) (hh4 : 4 ≤ G.degree h)
    (hax : G.Adj a x) (hay : G.Adj a y) (hak : G.Adj a k)
    (hdega : G.degree a = 3) (hdegx : G.degree x = 3) (hdegy : G.degree y = 3)
    (hxy : x ≠ y) : ¬G.Adj h a := by
  classical
  intro hha
  have hxk : x ≠ k := by intro e; rw [e] at hdegx; omega
  have hxh : x ≠ h := by intro e; rw [e] at hdegx; omega
  have hyk : y ≠ k := by intro e; rw [e] at hdegy; omega
  have hyh : y ≠ h := by intro e; rw [e] at hdegy; omega
  have hsub : ({x, y, k, h} : Finset (Fin 19)) ⊆ G.neighborFinset a := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hax
    · exact (G.mem_neighborFinset _ _).mpr hay
    · exact (G.mem_neighborFinset _ _).mpr hak
    · exact (G.mem_neighborFinset _ _).mpr hha.symm
  have hcard : ({x, y, k, h} : Finset (Fin 19)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxk, hxh]),
        Finset.card_insert_of_notMem (by simp [hyk, hyh]),
        Finset.card_insert_of_notMem (by simp [hkh]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hcard, G.card_neighborFinset_eq_degree, hdega] at hle
  omega

/-- **Induced-`C₅` two-twin assembly with a deg-`≤ 5` hub (`n = 18`).**  A hub `k` of degree `4` or
`5` adjacent to two distinct `M`-isolated degree-`3` twins, together with an induced `C₅` of
degree-`3` vertices, yields a `TwoTwinConfig`.  When `k` avoids a consecutive cycle triple
(`hub_cycle_cases_le5_nineteen`), `k` itself anchors the cut.  When `k` *hits* three consecutive
cycle vertices `vᵢ–vᵢ₊₁–vᵢ₊₂`, those three vertices have `k` as their unique hub neighbour, so the
deg-`≤ 5` hub `h ≠ k` supplied by `hnonk` (with two `M`-isolated twins) avoids that cherry and
anchors the cut instead.  (`hT` is unused: the deg-`5` triangle `k–vᵢ–vᵢ₊₁` has degree sum
`11 > 10`, so `hT` does not apply to it.) -/
theorem c5_shared_two_twin_le5_nineteen (G : SimpleGraph (Fin 19))
    (_hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (k t₁ t₂ : Fin 19) (hkge4 : 4 ≤ G.degree k) (hkle5 : G.degree k ≤ 5) (ht12 : t₁ ≠ t₂)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hAt1k : G.Adj t₁ k) (hAt2k : G.Adj t₂ k)
    (ht1iso : ∀ w : Fin 19, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 19, G.Adj t₂ w → G.degree w ≠ 3)
    (hnonk : ∀ a b c : Fin 19, G.degree a = 3 → G.degree b = 3 → G.degree c = 3 →
      G.Adj k a → G.Adj k b → G.Adj k c → G.Adj a b → G.Adj b c →
      a ≠ b → b ≠ c → a ≠ c →
      ∃ h tt₁ tt₂ : Fin 19, h ≠ k ∧ 4 ≤ G.degree h ∧ G.degree h ≤ 5 ∧ tt₁ ≠ tt₂ ∧
        G.degree tt₁ = 3 ∧ G.degree tt₂ = 3 ∧ G.Adj tt₁ h ∧ G.Adj tt₂ h ∧
        (∀ w : Fin 19, G.Adj tt₁ w → G.degree w ≠ 3) ∧
        (∀ w : Fin 19, G.Adj tt₂ w → G.degree w ≠ 3))
    (v₁ v₂ v₃ v₄ v₅ : Fin 19)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3 : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅) :
    TwoTwinConfig G := by
  obtain ⟨d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ :=
    distinct_five_nineteen v₁ v₂ v₃ v₄ v₅ hcard5
  have hB := hub_cycle_cases_le5_nineteen G hC4 k v₁ v₂ v₃ v₄ v₅ hkge4 hkle5 hd1 hd2 hd3 hd4 hd5
    e12 e23 e34 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  rcases hB with ⟨p1, p2, p3⟩ | ⟨p2, p3, p4⟩ | ⟨p3, p4, p5⟩ | ⟨p4, p5, p1⟩ | ⟨p5, p1, p2⟩ | hHit
  · exact dense_two_twin_assemble_le5_nineteen G t₁ t₂ k v₁ v₂ v₃ ht1deg ht2deg hkge4 hkle5
      hd1 hd2 hd3 hAt1k hAt2k e12 e23 ht1iso ht2iso p1 p2 p3 ht12 d12 d23 d13
  · exact dense_two_twin_assemble_le5_nineteen G t₁ t₂ k v₂ v₃ v₄ ht1deg ht2deg hkge4 hkle5
      hd2 hd3 hd4 hAt1k hAt2k e23 e34 ht1iso ht2iso p2 p3 p4 ht12 d23 d34 d24
  · exact dense_two_twin_assemble_le5_nineteen G t₁ t₂ k v₃ v₄ v₅ ht1deg ht2deg hkge4 hkle5
      hd3 hd4 hd5 hAt1k hAt2k e34 e45 ht1iso ht2iso p3 p4 p5 ht12 d34 d45 d35
  · exact dense_two_twin_assemble_le5_nineteen G t₁ t₂ k v₄ v₅ v₁ ht1deg ht2deg hkge4 hkle5
      hd4 hd5 hd1 hAt1k hAt2k e45 e51 ht1iso ht2iso p4 p5 p1 ht12 d45 d15.symm d14.symm
  · exact dense_two_twin_assemble_le5_nineteen G t₁ t₂ k v₅ v₁ v₂ ht1deg ht2deg hkge4 hkle5
      hd5 hd1 hd2 hAt1k hAt2k e51 e12 ht1iso ht2iso p5 p1 p2 ht12 d15.symm d12 d25.symm
  · -- **Deg-`5` hub `k` adjacent to three *consecutive* `C₅` vertices.**  Here `k` hits the cherry
    -- `vᵢ–vᵢ₊₁–vᵢ₊₂`, so `k` itself cannot anchor the two-twin cut.  Instead `hnonk` produces a
    -- *different* deg-`≤ 5` hub `h ≠ k` with two `M`-isolated twins; since each hit cycle vertex has
    -- `k` as its unique hub neighbour (`hub_not_adj_deg3_two_deg3_nbrs`), `h` avoids that cherry, and
    -- `dense_two_twin_assemble_le5_nineteen` closes.
    rcases hHit with ⟨ha1, ha2, ha3⟩ | ⟨ha2, ha3, ha4⟩ | ⟨ha3, ha4, ha5⟩ | ⟨ha4, ha5, ha1⟩ |
      ⟨ha5, ha1, ha2⟩
    · obtain ⟨h, s₁, s₂, hhk, hh4, hh5, hs12, hs1d, hs2d, hAs1, hAs2, hs1iso, hs2iso⟩ :=
        hnonk v₁ v₂ v₃ hd1 hd2 hd3 ha1 ha2 ha3 e12 e23 d12 d23 d13
      have nh1 := hub_not_adj_deg3_two_deg3_nbrs G h k v₁ v₂ v₅ hhk.symm hkge4 hh4 e12 e51.symm
        ha1.symm hd1 hd2 hd5 d25
      have nh2 := hub_not_adj_deg3_two_deg3_nbrs G h k v₂ v₁ v₃ hhk.symm hkge4 hh4 e12.symm e23
        ha2.symm hd2 hd1 hd3 d13
      have nh3 := hub_not_adj_deg3_two_deg3_nbrs G h k v₃ v₂ v₄ hhk.symm hkge4 hh4 e23.symm e34
        ha3.symm hd3 hd2 hd4 d24
      exact dense_two_twin_assemble_le5_nineteen G s₁ s₂ h v₁ v₂ v₃ hs1d hs2d hh4 hh5
        hd1 hd2 hd3 hAs1 hAs2 e12 e23 hs1iso hs2iso nh1 nh2 nh3 hs12 d12 d23 d13
    · obtain ⟨h, s₁, s₂, hhk, hh4, hh5, hs12, hs1d, hs2d, hAs1, hAs2, hs1iso, hs2iso⟩ :=
        hnonk v₂ v₃ v₄ hd2 hd3 hd4 ha2 ha3 ha4 e23 e34 d23 d34 d24
      have nh2 := hub_not_adj_deg3_two_deg3_nbrs G h k v₂ v₁ v₃ hhk.symm hkge4 hh4 e12.symm e23
        ha2.symm hd2 hd1 hd3 d13
      have nh3 := hub_not_adj_deg3_two_deg3_nbrs G h k v₃ v₂ v₄ hhk.symm hkge4 hh4 e23.symm e34
        ha3.symm hd3 hd2 hd4 d24
      have nh4 := hub_not_adj_deg3_two_deg3_nbrs G h k v₄ v₃ v₅ hhk.symm hkge4 hh4 e34.symm e45
        ha4.symm hd4 hd3 hd5 d35
      exact dense_two_twin_assemble_le5_nineteen G s₁ s₂ h v₂ v₃ v₄ hs1d hs2d hh4 hh5
        hd2 hd3 hd4 hAs1 hAs2 e23 e34 hs1iso hs2iso nh2 nh3 nh4 hs12 d23 d34 d24
    · obtain ⟨h, s₁, s₂, hhk, hh4, hh5, hs12, hs1d, hs2d, hAs1, hAs2, hs1iso, hs2iso⟩ :=
        hnonk v₃ v₄ v₅ hd3 hd4 hd5 ha3 ha4 ha5 e34 e45 d34 d45 d35
      have nh3 := hub_not_adj_deg3_two_deg3_nbrs G h k v₃ v₂ v₄ hhk.symm hkge4 hh4 e23.symm e34
        ha3.symm hd3 hd2 hd4 d24
      have nh4 := hub_not_adj_deg3_two_deg3_nbrs G h k v₄ v₃ v₅ hhk.symm hkge4 hh4 e34.symm e45
        ha4.symm hd4 hd3 hd5 d35
      have nh5 := hub_not_adj_deg3_two_deg3_nbrs G h k v₅ v₄ v₁ hhk.symm hkge4 hh4 e45.symm e51
        ha5.symm hd5 hd4 hd1 d14.symm
      exact dense_two_twin_assemble_le5_nineteen G s₁ s₂ h v₃ v₄ v₅ hs1d hs2d hh4 hh5
        hd3 hd4 hd5 hAs1 hAs2 e34 e45 hs1iso hs2iso nh3 nh4 nh5 hs12 d34 d45 d35
    · obtain ⟨h, s₁, s₂, hhk, hh4, hh5, hs12, hs1d, hs2d, hAs1, hAs2, hs1iso, hs2iso⟩ :=
        hnonk v₄ v₅ v₁ hd4 hd5 hd1 ha4 ha5 ha1 e45 e51 d45 d15.symm d14.symm
      have nh4 := hub_not_adj_deg3_two_deg3_nbrs G h k v₄ v₃ v₅ hhk.symm hkge4 hh4 e34.symm e45
        ha4.symm hd4 hd3 hd5 d35
      have nh5 := hub_not_adj_deg3_two_deg3_nbrs G h k v₅ v₄ v₁ hhk.symm hkge4 hh4 e45.symm e51
        ha5.symm hd5 hd4 hd1 d14.symm
      have nh1 := hub_not_adj_deg3_two_deg3_nbrs G h k v₁ v₅ v₂ hhk.symm hkge4 hh4 e51.symm e12
        ha1.symm hd1 hd5 hd2 d25.symm
      exact dense_two_twin_assemble_le5_nineteen G s₁ s₂ h v₄ v₅ v₁ hs1d hs2d hh4 hh5
        hd4 hd5 hd1 hAs1 hAs2 e45 e51 hs1iso hs2iso nh4 nh5 nh1 hs12 d45 d15.symm d14.symm
    · obtain ⟨h, s₁, s₂, hhk, hh4, hh5, hs12, hs1d, hs2d, hAs1, hAs2, hs1iso, hs2iso⟩ :=
        hnonk v₅ v₁ v₂ hd5 hd1 hd2 ha5 ha1 ha2 e51 e12 d15.symm d12 d25.symm
      have nh5 := hub_not_adj_deg3_two_deg3_nbrs G h k v₅ v₄ v₁ hhk.symm hkge4 hh4 e45.symm e51
        ha5.symm hd5 hd4 hd1 d14.symm
      have nh1 := hub_not_adj_deg3_two_deg3_nbrs G h k v₁ v₅ v₂ hhk.symm hkge4 hh4 e51.symm e12
        ha1.symm hd1 hd5 hd2 d25.symm
      have nh2 := hub_not_adj_deg3_two_deg3_nbrs G h k v₂ v₁ v₃ hhk.symm hkge4 hh4 e12.symm e23
        ha2.symm hd2 hd1 hd3 d13
      exact dense_two_twin_assemble_le5_nineteen G s₁ s₂ h v₅ v₁ v₂ hs1d hs2d hh4 hh5
        hd5 hd1 hd2 hAs1 hAs2 e51 e12 hs1iso hs2iso nh5 nh1 nh2 hs12 d15.symm d12 d25.symm

end N19

end ACMax
