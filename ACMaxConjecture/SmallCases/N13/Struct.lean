import ACMaxConjecture.Base

/-!
# Keystone structural classification for the `n = 13` twin certificate

The degree-3 subgraph `M = G[D]` of an `n = 13` ACMAX residual is triangle-free, `C₄`-free and
`2K₂`-free, with every vertex of `G`-degree (hence in-`M`-degree) at most `3`.  This file proves
the keystone dichotomy: if `M` has at least one edge, then EITHER `M` has a *dominating edge*
`c₁–c₂` (every `M`-edge meets `{c₁, c₂}`) OR `M` contains an induced `C₅` of degree-3 vertices
that carries *all* of `M`'s edges.

The consumer `eM_le_five` in `TwinCert13Core` reads off `e(M) ≤ 5` from this structure; the
two-twin/two-hub signed-cut configurations are assembled in `TwinCert13TwoHub`.
-/

namespace ACMax

open scoped Classical

namespace N13

/-- Cardinality of an explicit 4-element set with pairwise-distinct entries. -/
theorem card_four_thirteen (a b c d : Fin 13)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset (Fin 13)).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

/-- Cardinality of an explicit 5-element set with pairwise-distinct entries. -/
theorem card_five_thirteen (a b c d e : Fin 13)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ({a, b, c, d, e} : Finset (Fin 13)).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]),
      Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]

/-- **Spider domination (in-`M`-degree-3 case).**  If a degree-3 vertex `v` has all three of its
`G`-neighbours `a, b, c` in `D` (so in-`M`-degree `3`), then `M` has a dominating edge `{v, s}`:
at most one of `a, b, c` carries an extra `M`-edge (two would force an induced `2K₂`/`C₄`), so the
edge from `v` to that special neighbour covers every `M`-edge. -/
theorem d3_dominating (G : SimpleGraph (Fin 13)) (D : Finset (Fin 13))
    (hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (v a b c : Fin 13) (hvD : v ∈ D) (haD : a ∈ D) (hbD : b ∈ D) (hcD : c ∈ D)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcharv : ∀ w : Fin 13, G.Adj v w → w ∈ D → w = a ∨ w = b ∨ w = c) :
    ∃ c₁ c₂ : Fin 13, c₁ ∈ D ∧ c₂ ∈ D ∧ G.Adj c₁ c₂ ∧
      ∀ p q : Fin 13, p ∈ D → q ∈ D → G.Adj p q →
        p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂ := by
  classical
  have hdeg3 : ∀ x : Fin 13, x ∈ D → G.degree x = 3 := fun x hx => (hmemD x).mp hx
  have tri : ∀ x y z : Fin 13, x ∈ D → y ∈ D → z ∈ D → x ≠ y → y ≠ z → x ≠ z →
      G.Adj x y → G.Adj y z → G.Adj x z → False := by
    intro x y z hx hy hz hxy hyz hxz axy ayz axz
    exact hT ⟨x, y, z, hxy, hyz, hxz, axy, ayz, axz, by
      rw [hdeg3 x hx, hdeg3 y hy, hdeg3 z hz]; omega⟩
  have c4 : ∀ x y z w : Fin 13, x ∈ D → y ∈ D → z ∈ D → w ∈ D →
      ({x, y, z, w} : Finset (Fin 13)).card = 4 →
      G.Adj x y → G.Adj y z → G.Adj z w → G.Adj w x → ¬G.Adj x z → ¬G.Adj y w → False := by
    intro x y z w hx hy hz hw hcard xy yz zw wx nxz nyw
    exact hC4 ⟨x, y, z, w, hcard, xy, yz, zw, wx, nxz, nyw, by
      rw [hdeg3 x hx, hdeg3 y hy, hdeg3 z hz, hdeg3 w hw]; omega⟩
  have k2 : ∀ x y z w : Fin 13, x ∈ D → y ∈ D → z ∈ D → w ∈ D →
      ({x, y, z, w} : Finset (Fin 13)).card = 4 →
      G.Adj x y → G.Adj z w → ¬G.Adj x z → ¬G.Adj x w → ¬G.Adj y z → ¬G.Adj y w → False := by
    intro x y z w hx hy hz hw hcard xy zw nxz nxw nyz nyw
    exact h2k2 ⟨x, y, z, w, hcard, hdeg3 x hx, hdeg3 y hy, hdeg3 z hz, hdeg3 w hw,
      xy, zw, nxz, nxw, nyz, nyw⟩
  have hvna : v ≠ a := G.ne_of_adj hva
  have hvnb : v ≠ b := G.ne_of_adj hvb
  have hvnc : v ≠ c := G.ne_of_adj hvc
  have hnab : ¬G.Adj a b := fun h => tri v a b hvD haD hbD hvna hab hvnb hva h hvb
  have hnac : ¬G.Adj a c := fun h => tri v a c hvD haD hcD hvna hac hvnc hva h hvc
  have hnbc : ¬G.Adj b c := fun h => tri v b c hvD hbD hcD hvnb hbc hvnc hvb h hvc
  -- Every `M`-edge meets the star `{v, a, b, c}`.
  have hit4 : ∀ p q : Fin 13, p ∈ D → q ∈ D → G.Adj p q →
      p ∈ ({v, a, b, c} : Finset (Fin 13)) ∨ q ∈ ({v, a, b, c} : Finset (Fin 13)) := by
    intro p q hp hq hpq
    by_contra hcon
    push Not at hcon
    obtain ⟨hpnot, hqnot⟩ := hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpnot hqnot
    obtain ⟨hpv, hpa, hpb, hpc⟩ := hpnot
    obtain ⟨hqv, hqa, hqb, hqc⟩ := hqnot
    have hnvp : ¬G.Adj v p := fun h => by
      rcases hcharv p h hp with h' | h' | h'
      exacts [hpa h', hpb h', hpc h']
    have hnvq : ¬G.Adj v q := fun h => by
      rcases hcharv q h hq with h' | h' | h'
      exacts [hqa h', hqb h', hqc h']
    have notwo : ∀ w : Fin 13, w ∈ D → w ≠ v → w ≠ a → w ≠ b → w ≠ c →
        ¬(G.Adj a w ∧ G.Adj b w) ∧ ¬(G.Adj a w ∧ G.Adj c w) ∧ ¬(G.Adj b w ∧ G.Adj c w) := by
      intro w hwD hwv hwa hwb hwc
      have hnvw : ¬G.Adj v w := fun h => by
        rcases hcharv w h hwD with h' | h' | h'
        exacts [hwa h', hwb h', hwc h']
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨haw, hbw⟩
        exact c4 v a w b hvD haD hwD hbD
          (card_four_thirteen v a w b hvna (Ne.symm hwv) hvnb (Ne.symm hwa) hab hwb)
          hva haw hbw.symm hvb.symm hnvw hnab
      · rintro ⟨haw, hcw⟩
        exact c4 v a w c hvD haD hwD hcD
          (card_four_thirteen v a w c hvna (Ne.symm hwv) hvnc (Ne.symm hwa) hac hwc)
          hva haw hcw.symm hvc.symm hnvw hnac
      · rintro ⟨hbw, hcw⟩
        exact c4 v b w c hvD hbD hwD hcD
          (card_four_thirteen v b w c hvnb (Ne.symm hwv) hvnc (Ne.symm hwb) hbc hwc)
          hvb hbw hcw.symm hvc.symm hnvw hnbc
    have hgeta : G.Adj a p ∨ G.Adj a q := by
      by_contra hh; push Not at hh
      exact k2 v a p q hvD haD hp hq
        (card_four_thirteen v a p q hvna (Ne.symm hpv) (Ne.symm hqv) (Ne.symm hpa)
          (Ne.symm hqa) hpq.ne)
        hva hpq hnvp hnvq hh.1 hh.2
    have hgetb : G.Adj b p ∨ G.Adj b q := by
      by_contra hh; push Not at hh
      exact k2 v b p q hvD hbD hp hq
        (card_four_thirteen v b p q hvnb (Ne.symm hpv) (Ne.symm hqv) (Ne.symm hpb)
          (Ne.symm hqb) hpq.ne)
        hvb hpq hnvp hnvq hh.1 hh.2
    have hgetc : G.Adj c p ∨ G.Adj c q := by
      by_contra hh; push Not at hh
      exact k2 v c p q hvD hcD hp hq
        (card_four_thirteen v c p q hvnc (Ne.symm hpv) (Ne.symm hqv) (Ne.symm hpc)
          (Ne.symm hqc) hpq.ne)
        hvc hpq hnvp hnvq hh.1 hh.2
    have hpw := notwo p hp hpv hpa hpb hpc
    have hqw := notwo q hq hqv hqa hqb hqc
    rcases hgeta with hap | haq <;> rcases hgetb with hbp | hbq <;> rcases hgetc with hcp | hcq
    · exact hpw.1 ⟨hap, hbp⟩
    · exact hpw.1 ⟨hap, hbp⟩
    · exact hpw.2.1 ⟨hap, hcp⟩
    · exact hqw.2.2 ⟨hbq, hcq⟩
    · exact hpw.2.2 ⟨hbp, hcp⟩
    · exact hqw.2.1 ⟨haq, hcq⟩
    · exact hqw.1 ⟨haq, hbq⟩
    · exact hqw.1 ⟨haq, hbq⟩
  -- At most one of `a, b, c` has an extra `M`-neighbour.
  have key : ∀ s t r : Fin 13, s ∈ D → t ∈ D → r ∈ D → s ≠ t → s ≠ r → t ≠ r →
      G.Adj v s → G.Adj v t → G.Adj v r →
      (∀ w : Fin 13, G.Adj v w → w ∈ D → w = s ∨ w = t ∨ w = r) →
      ¬((∃ w, w ∈ D ∧ w ≠ v ∧ G.Adj s w) ∧ (∃ w, w ∈ D ∧ w ≠ v ∧ G.Adj t w)) := by
    intro s t r hsD htD hrD hst hsr htr hvs hvt hvr cv
    rintro ⟨⟨p, hpD, hpv, hsp⟩, ⟨q, hqD, hqv, htq⟩⟩
    have hnst : ¬G.Adj s t := fun h =>
      tri v s t hvD hsD htD (G.ne_of_adj hvs) hst (G.ne_of_adj hvt) hvs h hvt
    have hnsr : ¬G.Adj s r := fun h =>
      tri v s r hvD hsD hrD (G.ne_of_adj hvs) hsr (G.ne_of_adj hvr) hvs h hvr
    have hntr : ¬G.Adj t r := fun h =>
      tri v t r hvD htD hrD (G.ne_of_adj hvt) htr (G.ne_of_adj hvr) hvt h hvr
    have hps : p ≠ s := fun h => by rw [h] at hsp; exact G.irrefl hsp
    have hpt : p ≠ t := fun h => by rw [h] at hsp; exact hnst hsp
    have hpr : p ≠ r := fun h => by rw [h] at hsp; exact hnsr hsp
    have hqt : q ≠ t := fun h => by rw [h] at htq; exact G.irrefl htq
    have hqs : q ≠ s := fun h => by rw [h] at htq; exact hnst htq.symm
    have hqr : q ≠ r := fun h => by rw [h] at htq; exact hntr htq
    have hnvp : ¬G.Adj v p := fun h => by
      rcases cv p h hpD with h' | h' | h'
      exacts [hps h', hpt h', hpr h']
    have hnvq : ¬G.Adj v q := fun h => by
      rcases cv q h hqD with h' | h' | h'
      exacts [hqs h', hqt h', hqr h']
    have hpqne : p ≠ q := by
      rintro rfl
      exact c4 v s p t hvD hsD hpD htD
        (card_four_thirteen v s p t (G.ne_of_adj hvs) (Ne.symm hpv) (G.ne_of_adj hvt)
          (Ne.symm hps) hst hpt)
        hvs hsp htq.symm hvt.symm hnvp hnst
    by_cases hpq : G.Adj p q
    · have hnrp : ¬G.Adj r p := fun h =>
        c4 v s p r hvD hsD hpD hrD
          (card_four_thirteen v s p r (G.ne_of_adj hvs) (Ne.symm hpv) (G.ne_of_adj hvr)
            (Ne.symm hps) hsr hpr)
          hvs hsp h.symm hvr.symm hnvp hnsr
      have hnrq : ¬G.Adj r q := fun h =>
        c4 v t q r hvD htD hqD hrD
          (card_four_thirteen v t q r (G.ne_of_adj hvt) (Ne.symm hqv) (G.ne_of_adj hvr)
            (Ne.symm hqt) htr hqr)
          hvt htq h.symm hvr.symm hnvq hntr
      exact k2 v r p q hvD hrD hpD hqD
        (card_four_thirteen v r p q (G.ne_of_adj hvr) (Ne.symm hpv) (Ne.symm hqv)
          (Ne.symm hpr) (Ne.symm hqr) hpqne)
        hvr hpq hnvp hnvq hnrp hnrq
    · have hnsq : ¬G.Adj s q := fun h =>
        c4 v s q t hvD hsD hqD htD
          (card_four_thirteen v s q t (G.ne_of_adj hvs) (Ne.symm hqv) (G.ne_of_adj hvt)
            (Ne.symm hqs) hst hqt)
          hvs h htq.symm hvt.symm hnvq hnst
      have hnpt : ¬G.Adj p t := fun h =>
        c4 v t p s hvD htD hpD hsD
          (card_four_thirteen v t p s (G.ne_of_adj hvt) (Ne.symm hpv) (G.ne_of_adj hvs)
            (Ne.symm hpt) (Ne.symm hst) hps)
          hvt h.symm hsp.symm hvs.symm hnvp (fun e => hnst e.symm)
      exact k2 s p t q hsD hpD htD hqD
        (card_four_thirteen s p t q (Ne.symm hps) hst (Ne.symm hqs) hpt hpqne (Ne.symm hqt))
        hsp htq hnst hnsq hnpt hpq
  -- Domination from a chosen centre `s` whose two sibling neighbours have no extra edges.
  have dom4 : ∀ s : Fin 13, s ∈ ({a, b, c} : Finset (Fin 13)) →
      (∀ t : Fin 13, t ∈ ({a, b, c} : Finset (Fin 13)) → t ≠ s →
        ∀ w : Fin 13, G.Adj t w → w ∈ D → w = v) →
      ∃ c₁ c₂ : Fin 13, c₁ ∈ D ∧ c₂ ∈ D ∧ G.Adj c₁ c₂ ∧
        ∀ p q : Fin 13, p ∈ D → q ∈ D → G.Adj p q → p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂ := by
    intro s hs hns
    have hsD : s ∈ D := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl <;> assumption
    have hvs : G.Adj v s := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl <;> assumption
    refine ⟨v, s, hvD, hsD, hvs, ?_⟩
    intro p q hp hq hpq
    rcases hit4 p q hp hq hpq with hph | hqh
    · rw [Finset.mem_insert] at hph
      rcases hph with rfl | hpabc
      · exact Or.inl rfl
      · by_cases hpsq : p = s
        · exact Or.inr (Or.inl hpsq)
        · exact Or.inr (Or.inr (Or.inl (hns p hpabc hpsq q hpq hq)))
    · rw [Finset.mem_insert] at hqh
      rcases hqh with rfl | hqabc
      · exact Or.inr (Or.inr (Or.inl rfl))
      · by_cases hqsq : q = s
        · exact Or.inr (Or.inr (Or.inr hqsq))
        · exact Or.inl (hns q hqabc hqsq p hpq.symm hp)
  -- Select the special neighbour.
  have nab := key a b c haD hbD hcD hab hac hbc hva hvb hvc hcharv
  have nac := key a c b haD hcD hbD hac hab (Ne.symm hbc) hva hvc hvb
    (fun w hw hwD => by rcases hcharv w hw hwD with h | h | h <;> tauto)
  have nbc := key b c a hbD hcD haD hbc (Ne.symm hab) (Ne.symm hac) hvb hvc hva
    (fun w hw hwD => by rcases hcharv w hw hwD with h | h | h <;> tauto)
  by_cases ea : ∃ w, w ∈ D ∧ w ≠ v ∧ G.Adj a w
  · by_cases eb : ∃ w, w ∈ D ∧ w ≠ v ∧ G.Adj b w
    · exact absurd ⟨ea, eb⟩ nab
    · by_cases ec : ∃ w, w ∈ D ∧ w ≠ v ∧ G.Adj c w
      · exact absurd ⟨ea, ec⟩ nac
      · refine dom4 a (by simp) ?_
        intro t ht hta w htw hwD
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact absurd rfl hta
        · by_contra hwv; exact eb ⟨w, hwD, hwv, htw⟩
        · by_contra hwv; exact ec ⟨w, hwD, hwv, htw⟩
  · by_cases eb : ∃ w, w ∈ D ∧ w ≠ v ∧ G.Adj b w
    · by_cases ec : ∃ w, w ∈ D ∧ w ≠ v ∧ G.Adj c w
      · exact absurd ⟨eb, ec⟩ nbc
      · refine dom4 b (by simp) ?_
        intro t ht htb w htw hwD
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · by_contra hwv; exact ea ⟨w, hwD, hwv, htw⟩
        · exact absurd rfl htb
        · by_contra hwv; exact ec ⟨w, hwD, hwv, htw⟩
    · refine dom4 c (by simp) ?_
      intro t ht htc w htw hwD
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · by_contra hwv; exact ea ⟨w, hwD, hwv, htw⟩
      · by_contra hwv; exact eb ⟨w, hwD, hwv, htw⟩
      · exact absurd rfl htc

/-- **Keystone dichotomy for `M = G[D]`.**  If the degree-3 subgraph `M` (triangle-free,
`C₄`-free, `2K₂`-free, max-degree `≤ 3`) has at least one edge, then EITHER it has a *dominating
edge* `c₁–c₂` (every `M`-edge meets `{c₁, c₂}`) OR it contains an induced `C₅` of degree-3
vertices carrying all of `M`'s edges. -/
theorem dominating_edge_or_induced_C5 (G : SimpleGraph (Fin 13)) (D : Finset (Fin 13))
    (hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hne : ∃ a b : Fin 13, a ∈ D ∧ b ∈ D ∧ G.Adj a b) :
    (∃ c₁ c₂ : Fin 13, c₁ ∈ D ∧ c₂ ∈ D ∧ G.Adj c₁ c₂ ∧
      ∀ p q : Fin 13, p ∈ D → q ∈ D → G.Adj p q →
        p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    ∨ (∃ v₁ v₂ v₃ v₄ v₅ : Fin 13,
        v₁ ∈ D ∧ v₂ ∈ D ∧ v₃ ∈ D ∧ v₄ ∈ D ∧ v₅ ∈ D ∧
        ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 13)).card = 5 ∧
        G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧ G.Adj v₃ v₄ ∧ G.Adj v₄ v₅ ∧ G.Adj v₅ v₁ ∧
        ¬G.Adj v₁ v₃ ∧ ¬G.Adj v₁ v₄ ∧ ¬G.Adj v₂ v₄ ∧ ¬G.Adj v₂ v₅ ∧ ¬G.Adj v₃ v₅ ∧
        ∀ p q : Fin 13, p ∈ D → q ∈ D → G.Adj p q →
          p = v₁ ∨ p = v₂ ∨ p = v₃ ∨ p = v₄ ∨ p = v₅) := by
  classical
  have hdeg3 : ∀ x : Fin 13, x ∈ D → G.degree x = 3 := fun x hx => (hmemD x).mp hx
  have hindle : ∀ x : Fin 13, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := hdeg3 x hx
  have tri : ∀ x y z : Fin 13, x ∈ D → y ∈ D → z ∈ D → x ≠ y → y ≠ z → x ≠ z →
      G.Adj x y → G.Adj y z → G.Adj x z → False := by
    intro x y z hx hy hz hxy hyz hxz axy ayz axz
    exact hT ⟨x, y, z, hxy, hyz, hxz, axy, ayz, axz, by
      rw [hdeg3 x hx, hdeg3 y hy, hdeg3 z hz]; omega⟩
  have c4 : ∀ x y z w : Fin 13, x ∈ D → y ∈ D → z ∈ D → w ∈ D →
      ({x, y, z, w} : Finset (Fin 13)).card = 4 →
      G.Adj x y → G.Adj y z → G.Adj z w → G.Adj w x → ¬G.Adj x z → ¬G.Adj y w → False := by
    intro x y z w hx hy hz hw hcard xy yz zw wx nxz nyw
    exact hC4 ⟨x, y, z, w, hcard, xy, yz, zw, wx, nxz, nyw, by
      rw [hdeg3 x hx, hdeg3 y hy, hdeg3 z hz, hdeg3 w hw]; omega⟩
  have k2 : ∀ x y z w : Fin 13, x ∈ D → y ∈ D → z ∈ D → w ∈ D →
      ({x, y, z, w} : Finset (Fin 13)).card = 4 →
      G.Adj x y → G.Adj z w → ¬G.Adj x z → ¬G.Adj x w → ¬G.Adj y z → ¬G.Adj y w → False := by
    intro x y z w hx hy hz hw hcard xy zw nxz nxw nyz nyw
    exact h2k2 ⟨x, y, z, w, hcard, hdeg3 x hx, hdeg3 y hy, hdeg3 z hz, hdeg3 w hw,
      xy, zw, nxz, nxw, nyz, nyw⟩
  -- Case split on the existence of an in-`M`-degree-3 vertex.
  by_cases hd3 : ∃ v : Fin 13, v ∈ D ∧ 3 ≤ (G.neighborFinset v ∩ D).card
  · obtain ⟨v, hvD, hv3⟩ := hd3
    have hv3' : (G.neighborFinset v ∩ D).card = 3 := le_antisymm (hindle v hvD) hv3
    obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hv3'
    have hmem : ∀ w : Fin 13, w ∈ ({a, b, c} : Finset (Fin 13)) →
        G.Adj v w ∧ w ∈ D := by
      intro w hw
      have : w ∈ G.neighborFinset v ∩ D := by rw [hset]; exact hw
      exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp this).1,
        (Finset.mem_inter.mp this).2⟩
    obtain ⟨hva, haD⟩ := hmem a (by simp)
    obtain ⟨hvb, hbD⟩ := hmem b (by simp)
    obtain ⟨hvc, hcD⟩ := hmem c (by simp)
    have hcharv : ∀ w : Fin 13, G.Adj v w → w ∈ D → w = a ∨ w = b ∨ w = c := by
      intro w hvw hwD
      have : w ∈ G.neighborFinset v ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvw, hwD⟩
      rw [hset] at this; simpa using this
    exact Or.inl (d3_dominating G D hmemD hT hC4 h2k2 v a b c hvD haD hbD hcD hva hvb hvc
      hab hac hbc hcharv)
  · -- All in-`M`-degrees are `≤ 2`.
    push Not at hd3
    have hle2 : ∀ v : Fin 13, v ∈ D → (G.neighborFinset v ∩ D).card ≤ 2 := by
      intro v hv; have := hd3 v hv; omega
    obtain ⟨a0, b0, ha0, hb0, hab0⟩ := hne
    by_cases h2 : ∃ y : Fin 13, y ∈ D ∧ (G.neighborFinset y ∩ D).card = 2
    · obtain ⟨y, hyD, hy2⟩ := h2
      obtain ⟨x, z, hxz, hyset⟩ := Finset.card_eq_two.mp hy2
      have hxmem : x ∈ G.neighborFinset y ∩ D := by rw [hyset]; simp
      have hzmem : z ∈ G.neighborFinset y ∩ D := by rw [hyset]; simp
      have hxD : x ∈ D := (Finset.mem_inter.mp hxmem).2
      have hzD : z ∈ D := (Finset.mem_inter.mp hzmem).2
      have hyx : G.Adj y x := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hxmem).1
      have hyz : G.Adj y z := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hzmem).1
      have hynx : y ≠ x := G.ne_of_adj hyx
      have hynz : y ≠ z := G.ne_of_adj hyz
      have hnxz : ¬G.Adj x z := fun h => tri y x z hyD hxD hzD hynx hxz hynz hyx h hyz
      have hchary : ∀ w : Fin 13, G.Adj y w → w ∈ D → w = x ∨ w = z := by
        intro w hyw hwD
        have : w ∈ G.neighborFinset y ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hyw, hwD⟩
        rw [hyset] at this; simpa using this
      -- Domination from a no-extra sibling.
      have dom_gen : ∀ n1 n2 : Fin 13, n1 ∈ D → n2 ∈ D → n1 ≠ n2 → G.Adj y n1 → G.Adj y n2 →
          (∀ w : Fin 13, G.Adj y w → w ∈ D → w = n1 ∨ w = n2) →
          (∀ w : Fin 13, G.Adj n2 w → w ∈ D → w = y) →
          ∃ c₁ c₂ : Fin 13, c₁ ∈ D ∧ c₂ ∈ D ∧ G.Adj c₁ c₂ ∧
            ∀ p q : Fin 13, p ∈ D → q ∈ D → G.Adj p q →
              p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂ := by
        intro n1 n2 hn1 hn2 hn12 hyn1 hyn2 chary' charn2
        refine ⟨y, n1, hyD, hn1, hyn1, ?_⟩
        intro p q hp hq hpq
        by_contra hcon
        push Not at hcon
        obtain ⟨hpy, hpn1, hqy, hqn1⟩ := hcon
        have hpn2 : p ≠ n2 := by rintro rfl; exact hqy (charn2 q hpq hq)
        have hqn2 : q ≠ n2 := by rintro rfl; exact hpy (charn2 p hpq.symm hp)
        have hn2p : ¬G.Adj n2 p := fun h => hpy (charn2 p h hp)
        have hn2q : ¬G.Adj n2 q := fun h => hqy (charn2 q h hq)
        have hyp : ¬G.Adj y p := fun h => by
          rcases chary' p h hp with h' | h'; exacts [hpn1 h', hpn2 h']
        have hyq : ¬G.Adj y q := fun h => by
          rcases chary' q h hq with h' | h'; exacts [hqn1 h', hqn2 h']
        exact k2 n2 y p q hn2 hyD hp hq
          (card_four_thirteen n2 y p q (G.ne_of_adj hyn2).symm (Ne.symm hpn2) (Ne.symm hqn2)
            (Ne.symm hpy) (Ne.symm hqy) hpq.ne)
          hyn2.symm hpq hn2p hn2q hyp hyq
      by_cases hze : ∃ w : Fin 13, w ∈ D ∧ w ≠ y ∧ G.Adj z w
      · by_cases hxe : ∃ w : Fin 13, w ∈ D ∧ w ≠ y ∧ G.Adj x w
        · -- Both siblings have an extra neighbour: an induced `C₅` forms.
          obtain ⟨x', hx'D, hx'y, hxx'⟩ := hxe
          obtain ⟨z', hz'D, hz'y, hzz'⟩ := hze
          -- Saturated neighbourhoods of `x` and `z`.
          have hxfull : G.neighborFinset x ∩ D = ({y, x'} : Finset (Fin 13)) := by
            have hsub : ({y, x'} : Finset (Fin 13)) ⊆ G.neighborFinset x ∩ D := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hyx.symm, hyD⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxx', hx'D⟩
            have hc2 : ({y, x'} : Finset (Fin 13)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx'y]), Finset.card_singleton]
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 x hxD)).symm
          have hcharx : ∀ w : Fin 13, G.Adj x w → w ∈ D → w = y ∨ w = x' := by
            intro w hxw hwD
            have : w ∈ G.neighborFinset x ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw, hwD⟩
            rw [hxfull] at this; simpa using this
          have hzfull : G.neighborFinset z ∩ D = ({y, z'} : Finset (Fin 13)) := by
            have hsub : ({y, z'} : Finset (Fin 13)) ⊆ G.neighborFinset z ∩ D := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hyz.symm, hyD⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzz', hz'D⟩
            have hc2 : ({y, z'} : Finset (Fin 13)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm hz'y]), Finset.card_singleton]
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 z hzD)).symm
          have hcharz : ∀ w : Fin 13, G.Adj z w → w ∈ D → w = y ∨ w = z' := by
            intro w hzw hwD
            have : w ∈ G.neighborFinset z ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzw, hwD⟩
            rw [hzfull] at this; simpa using this
          -- Distinctness among the five vertices.
          have hnyx' : ¬G.Adj y x' := by
            intro h; rcases hchary x' h hx'D with h' | h'
            · rw [h'] at hxx'; exact G.irrefl hxx'
            · rw [h'] at hxx'; exact hnxz hxx'
          have hnyz' : ¬G.Adj y z' := by
            intro h; rcases hchary z' h hz'D with h' | h'
            · rw [h'] at hzz'; exact hnxz hzz'.symm
            · rw [h'] at hzz'; exact G.irrefl hzz'
          have hx'z : x' ≠ z := fun e => hnxz (e ▸ hxx')
          have hxz' : x ≠ z' := by rintro rfl; exact hnxz hzz'.symm
          have hx'z' : x' ≠ z' := by
            rintro rfl
            have hzx' : G.Adj z x' := hzz'
            exact c4 x x' z y hxD hx'D hzD hyD
              (card_four_thirteen x x' z y (G.ne_of_adj hxx') hxz (Ne.symm hynx) hx'z hx'y
                (Ne.symm hynz))
              hxx' hzx'.symm hyz.symm hyx hnxz (fun h => hnyx' h.symm)
          have hnxz' : ¬G.Adj x z' := by
            intro h; rcases hcharx z' h hz'D with e | e
            · exact hz'y e
            · exact hx'z' e.symm
          have hnx'z : ¬G.Adj x' z := by
            intro h; rcases hcharz x' h.symm hx'D with e | e
            · exact hx'y e
            · exact hx'z' e
          have hadjx'z' : G.Adj x' z' := by
            by_contra hn
            exact k2 x x' z z' hxD hx'D hzD hz'D
              (card_four_thirteen x x' z z' (G.ne_of_adj hxx') hxz hxz' hx'z hx'z'
                (G.ne_of_adj hzz'))
              hxx' hzz' hnxz hnxz' hnx'z hn
          -- Saturated neighbourhoods of `x'` and `z'` (closing the `C₅`).
          have hx'full : G.neighborFinset x' ∩ D = ({x, z'} : Finset (Fin 13)) := by
            have hsub : ({x, z'} : Finset (Fin 13)) ⊆ G.neighborFinset x' ∩ D := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxx'.symm, hxD⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjx'z', hz'D⟩
            have hc2 : ({x, z'} : Finset (Fin 13)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [hxz']), Finset.card_singleton]
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 x' hx'D)).symm
          have hcharx' : ∀ w : Fin 13, G.Adj x' w → w ∈ D → w = x ∨ w = z' := by
            intro w hx'w hwD
            have : w ∈ G.neighborFinset x' ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hx'w, hwD⟩
            rw [hx'full] at this; simpa using this
          have hz'full : G.neighborFinset z' ∩ D = ({z, x'} : Finset (Fin 13)) := by
            have hsub : ({z, x'} : Finset (Fin 13)) ⊆ G.neighborFinset z' ∩ D := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzz'.symm, hzD⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjx'z'.symm, hx'D⟩
            have hc2 : ({z, x'} : Finset (Fin 13)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx'z]), Finset.card_singleton]
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 z' hz'D)).symm
          have hcharz' : ∀ w : Fin 13, G.Adj z' w → w ∈ D → w = z ∨ w = x' := by
            intro w hz'w hwD
            have : w ∈ G.neighborFinset z' ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hz'w, hwD⟩
            rw [hz'full] at this; simpa using this
          refine Or.inr ⟨x, y, z, z', x', hxD, hyD, hzD, hz'D, hx'D, ?_,
            hyx.symm, hyz, hzz', hadjx'z'.symm, hxx'.symm,
            hnxz, hnxz', hnyz', hnyx', fun h => hnx'z h.symm, ?_⟩
          · exact card_five_thirteen x y z z' x' (Ne.symm hynx) hxz hxz' (G.ne_of_adj hxx')
              hynz (Ne.symm hz'y) (Ne.symm hx'y) (G.ne_of_adj hzz') (Ne.symm hx'z)
              (Ne.symm hx'z')
          · -- Every `M`-edge lies inside the five-vertex `C₅`.
            intro p q hp hq hpq
            by_contra hpnot
            push Not at hpnot
            obtain ⟨hpx, hpy, hpz, hpz', hpx'⟩ := hpnot
            -- `q` cannot lie in the cycle either (its neighbourhood is closed).
            have hqnot : q ≠ x ∧ q ≠ y ∧ q ≠ z ∧ q ≠ z' ∧ q ≠ x' := by
              refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
              · rcases hcharx p hpq.symm hp with e | e
                exacts [hpy e, hpx' e]
              · rcases hchary p hpq.symm hp with e | e
                exacts [hpx e, hpz e]
              · rcases hcharz p hpq.symm hp with e | e
                exacts [hpy e, hpz' e]
              · rcases hcharz' p hpq.symm hp with e | e
                exacts [hpz e, hpx' e]
              · rcases hcharx' p hpq.symm hp with e | e
                exacts [hpx e, hpz' e]
            obtain ⟨hqx, hqy, hqz, hqz', hqx'⟩ := hqnot
            -- `x–y` together with `p–q` would form an induced `2K₂`.
            have hnxp : ¬G.Adj x p := fun h => by
              rcases hcharx p h hp with e | e; exacts [hpy e, hpx' e]
            have hnxq : ¬G.Adj x q := fun h => by
              rcases hcharx q h hq with e | e; exacts [hqy e, hqx' e]
            have hnyp : ¬G.Adj y p := fun h => by
              rcases hchary p h hp with e | e; exacts [hpx e, hpz e]
            have hnyq : ¬G.Adj y q := fun h => by
              rcases hchary q h hq with e | e; exacts [hqx e, hqz e]
            exact k2 x y p q hxD hyD hp hq
              (card_four_thirteen x y p q (Ne.symm hynx) (Ne.symm hpx) (Ne.symm hqx)
                (Ne.symm hpy) (Ne.symm hqy) hpq.ne)
              hyx.symm hpq hnxp hnxq hnyp hnyq
        · -- `x` has no extra neighbour: `{y, z}` dominates.
          refine Or.inl (dom_gen z x hzD hxD (Ne.symm hxz) hyz hyx
            (fun w hw hwD => Or.symm (hchary w hw hwD))
            (fun w hxw hwD => by by_contra hwy; exact hxe ⟨w, hwD, hwy, hxw⟩))
      · -- `z` has no extra neighbour: `{y, x}` dominates.
        refine Or.inl (dom_gen x z hxD hzD hxz hyx hyz hchary
          (fun w hzw hwD => by by_contra hwy; exact hze ⟨w, hwD, hwy, hzw⟩))
    · -- No in-`M`-degree-2 vertex: `M` is a single edge.
      have hle1 : ∀ v : Fin 13, v ∈ D → (G.neighborFinset v ∩ D).card ≤ 1 := by
        intro v hv
        rcases Nat.lt_or_ge ((G.neighborFinset v ∩ D).card) 2 with h | h
        · omega
        · exact absurd ⟨v, hv, le_antisymm (hle2 v hv) h⟩ h2
      have ha0full : G.neighborFinset a0 ∩ D = ({b0} : Finset (Fin 13)) := by
        have hsub : ({b0} : Finset (Fin 13)) ⊆ G.neighborFinset a0 ∩ D := by
          intro w hw; rw [Finset.mem_singleton] at hw; subst hw
          exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab0, hb0⟩
        exact (Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_singleton]; exact hle1 a0 ha0)).symm
      have hb0full : G.neighborFinset b0 ∩ D = ({a0} : Finset (Fin 13)) := by
        have hsub : ({a0} : Finset (Fin 13)) ⊆ G.neighborFinset b0 ∩ D := by
          intro w hw; rw [Finset.mem_singleton] at hw; subst hw
          exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab0.symm, ha0⟩
        exact (Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_singleton]; exact hle1 b0 hb0)).symm
      have hchara0 : ∀ w : Fin 13, G.Adj a0 w → w ∈ D → w = b0 := by
        intro w haw hwD
        have : w ∈ G.neighborFinset a0 ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haw, hwD⟩
        rw [ha0full, Finset.mem_singleton] at this; exact this
      have hcharb0 : ∀ w : Fin 13, G.Adj b0 w → w ∈ D → w = a0 := by
        intro w hbw hwD
        have : w ∈ G.neighborFinset b0 ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hbw, hwD⟩
        rw [hb0full, Finset.mem_singleton] at this; exact this
      refine Or.inl ⟨a0, b0, ha0, hb0, hab0, ?_⟩
      intro p q hp hq hpq
      by_contra hcon
      push Not at hcon
      obtain ⟨hpa0, hpb0, hqa0, hqb0⟩ := hcon
      have hna0p : ¬G.Adj a0 p := fun h => hpb0 (hchara0 p h hp)
      have hna0q : ¬G.Adj a0 q := fun h => hqb0 (hchara0 q h hq)
      have hnb0p : ¬G.Adj b0 p := fun h => hpa0 (hcharb0 p h hp)
      have hnb0q : ¬G.Adj b0 q := fun h => hqa0 (hcharb0 q h hq)
      exact k2 a0 b0 p q ha0 hb0 hp hq
        (card_four_thirteen a0 b0 p q hab0.ne (Ne.symm hpa0) (Ne.symm hqa0) (Ne.symm hpb0)
          (Ne.symm hqb0) hpq.ne)
        hab0 hpq hna0p hna0q hnb0p hnb0q

end N13

end ACMax
