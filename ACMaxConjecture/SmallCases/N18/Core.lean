import ACMaxConjecture.Base

/-!
# Structural / regime core lemmas for the `n = 18` twin certificate

Ported from the proved `n = 17` development (`TwinCert17Core`).
In the `n = 18` residual the graph has `32` edges, minimum degree `3`, and
(by `residual_hub_card_le_ten`) the hub set `Hub = filter (4 ≤ deg)` has `Hub.card ≤ 10` while the
degree-3 set `D = filter (deg = 3)` has `8 ≤ D.card`.  The total degree-excess over `3` is
`64 − 54 = 10`, giving the handshake `e(M) = 22 − 3·|Hub| + e_H` and `|Hub| ∈ {6, 7, 8, 9, 10}`.

The good-`C₄` residual threshold is `≤ 14` for `n = 18` (same as `n = 17`), so the `hC4`
hypotheses carry `≤ 14` here; the good-`K_{2,3}` threshold is `≤ 19`.

All lemmas are axiom-clean ports; the boundary/structure arithmetic is `n`-independent except for
`residual_hub_card_le_ten` (handshake constants).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- Cardinality of an explicit 4-element set with pairwise-distinct entries. -/
theorem card_four_eighteen (a b c d : Fin 18)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset (Fin 18)).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

/-- Cardinality of an explicit 5-element set with pairwise-distinct entries. -/
theorem card_five_eighteen (a b c d e : Fin 18)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ({a, b, c, d, e} : Finset (Fin 18)).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]),
      Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]

/-- **Spider domination (in-`M`-degree-3 case).**  If a degree-3 vertex `v` has all three of its
`G`-neighbours `a, b, c` in `D` (so in-`M`-degree `3`), then `M` has a dominating edge `{v, s}`:
at most one of `a, b, c` carries an extra `M`-edge (two would force an induced `2K₂`/`C₄`), so the
edge from `v` to that special neighbour covers every `M`-edge. -/
theorem d3_dominating (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18))
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (h2k2 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (v a b c : Fin 18) (hvD : v ∈ D) (haD : a ∈ D) (hbD : b ∈ D) (hcD : c ∈ D)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcharv : ∀ w : Fin 18, G.Adj v w → w ∈ D → w = a ∨ w = b ∨ w = c) :
    ∃ c₁ c₂ : Fin 18, c₁ ∈ D ∧ c₂ ∈ D ∧ G.Adj c₁ c₂ ∧
      ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q →
        p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂ := by
  classical
  have hdeg3 : ∀ x : Fin 18, x ∈ D → G.degree x = 3 := fun x hx => (hmemD x).mp hx
  have tri : ∀ x y z : Fin 18, x ∈ D → y ∈ D → z ∈ D → x ≠ y → y ≠ z → x ≠ z →
      G.Adj x y → G.Adj y z → G.Adj x z → False := by
    intro x y z hx hy hz hxy hyz hxz axy ayz axz
    exact hT ⟨x, y, z, hxy, hyz, hxz, axy, ayz, axz, by
      rw [hdeg3 x hx, hdeg3 y hy, hdeg3 z hz]; omega⟩
  have c4 : ∀ x y z w : Fin 18, x ∈ D → y ∈ D → z ∈ D → w ∈ D →
      ({x, y, z, w} : Finset (Fin 18)).card = 4 →
      G.Adj x y → G.Adj y z → G.Adj z w → G.Adj w x → ¬G.Adj x z → ¬G.Adj y w → False := by
    intro x y z w hx hy hz hw hcard xy yz zw wx nxz nyw
    exact hC4 ⟨x, y, z, w, hcard, xy, yz, zw, wx, nxz, nyw, by
      rw [hdeg3 x hx, hdeg3 y hy, hdeg3 z hz, hdeg3 w hw]; omega⟩
  have k2 : ∀ x y z w : Fin 18, x ∈ D → y ∈ D → z ∈ D → w ∈ D →
      ({x, y, z, w} : Finset (Fin 18)).card = 4 →
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
  have hit4 : ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q →
      p ∈ ({v, a, b, c} : Finset (Fin 18)) ∨ q ∈ ({v, a, b, c} : Finset (Fin 18)) := by
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
    have notwo : ∀ w : Fin 18, w ∈ D → w ≠ v → w ≠ a → w ≠ b → w ≠ c →
        ¬(G.Adj a w ∧ G.Adj b w) ∧ ¬(G.Adj a w ∧ G.Adj c w) ∧ ¬(G.Adj b w ∧ G.Adj c w) := by
      intro w hwD hwv hwa hwb hwc
      have hnvw : ¬G.Adj v w := fun h => by
        rcases hcharv w h hwD with h' | h' | h'
        exacts [hwa h', hwb h', hwc h']
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨haw, hbw⟩
        exact c4 v a w b hvD haD hwD hbD
          (card_four_eighteen v a w b hvna (Ne.symm hwv) hvnb (Ne.symm hwa) hab hwb)
          hva haw hbw.symm hvb.symm hnvw hnab
      · rintro ⟨haw, hcw⟩
        exact c4 v a w c hvD haD hwD hcD
          (card_four_eighteen v a w c hvna (Ne.symm hwv) hvnc (Ne.symm hwa) hac hwc)
          hva haw hcw.symm hvc.symm hnvw hnac
      · rintro ⟨hbw, hcw⟩
        exact c4 v b w c hvD hbD hwD hcD
          (card_four_eighteen v b w c hvnb (Ne.symm hwv) hvnc (Ne.symm hwb) hbc hwc)
          hvb hbw hcw.symm hvc.symm hnvw hnbc
    have hgeta : G.Adj a p ∨ G.Adj a q := by
      by_contra hh; push Not at hh
      exact k2 v a p q hvD haD hp hq
        (card_four_eighteen v a p q hvna (Ne.symm hpv) (Ne.symm hqv) (Ne.symm hpa)
          (Ne.symm hqa) hpq.ne)
        hva hpq hnvp hnvq hh.1 hh.2
    have hgetb : G.Adj b p ∨ G.Adj b q := by
      by_contra hh; push Not at hh
      exact k2 v b p q hvD hbD hp hq
        (card_four_eighteen v b p q hvnb (Ne.symm hpv) (Ne.symm hqv) (Ne.symm hpb)
          (Ne.symm hqb) hpq.ne)
        hvb hpq hnvp hnvq hh.1 hh.2
    have hgetc : G.Adj c p ∨ G.Adj c q := by
      by_contra hh; push Not at hh
      exact k2 v c p q hvD hcD hp hq
        (card_four_eighteen v c p q hvnc (Ne.symm hpv) (Ne.symm hqv) (Ne.symm hpc)
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
  have key : ∀ s t r : Fin 18, s ∈ D → t ∈ D → r ∈ D → s ≠ t → s ≠ r → t ≠ r →
      G.Adj v s → G.Adj v t → G.Adj v r →
      (∀ w : Fin 18, G.Adj v w → w ∈ D → w = s ∨ w = t ∨ w = r) →
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
        (card_four_eighteen v s p t (G.ne_of_adj hvs) (Ne.symm hpv) (G.ne_of_adj hvt)
          (Ne.symm hps) hst hpt)
        hvs hsp htq.symm hvt.symm hnvp hnst
    by_cases hpq : G.Adj p q
    · have hnrp : ¬G.Adj r p := fun h =>
        c4 v s p r hvD hsD hpD hrD
          (card_four_eighteen v s p r (G.ne_of_adj hvs) (Ne.symm hpv) (G.ne_of_adj hvr)
            (Ne.symm hps) hsr hpr)
          hvs hsp h.symm hvr.symm hnvp hnsr
      have hnrq : ¬G.Adj r q := fun h =>
        c4 v t q r hvD htD hqD hrD
          (card_four_eighteen v t q r (G.ne_of_adj hvt) (Ne.symm hqv) (G.ne_of_adj hvr)
            (Ne.symm hqt) htr hqr)
          hvt htq h.symm hvr.symm hnvq hntr
      exact k2 v r p q hvD hrD hpD hqD
        (card_four_eighteen v r p q (G.ne_of_adj hvr) (Ne.symm hpv) (Ne.symm hqv)
          (Ne.symm hpr) (Ne.symm hqr) hpqne)
        hvr hpq hnvp hnvq hnrp hnrq
    · have hnsq : ¬G.Adj s q := fun h =>
        c4 v s q t hvD hsD hqD htD
          (card_four_eighteen v s q t (G.ne_of_adj hvs) (Ne.symm hqv) (G.ne_of_adj hvt)
            (Ne.symm hqs) hst hqt)
          hvs h htq.symm hvt.symm hnvq hnst
      have hnpt : ¬G.Adj p t := fun h =>
        c4 v t p s hvD htD hpD hsD
          (card_four_eighteen v t p s (G.ne_of_adj hvt) (Ne.symm hpv) (G.ne_of_adj hvs)
            (Ne.symm hpt) (Ne.symm hst) hps)
          hvt h.symm hsp.symm hvs.symm hnvp (fun e => hnst e.symm)
      exact k2 s p t q hsD hpD htD hqD
        (card_four_eighteen s p t q (Ne.symm hps) hst (Ne.symm hqs) hpt hpqne (Ne.symm hqt))
        hsp htq hnst hnsq hnpt hpq
  -- Domination from a chosen centre `s` whose two sibling neighbours have no extra edges.
  have dom4 : ∀ s : Fin 18, s ∈ ({a, b, c} : Finset (Fin 18)) →
      (∀ t : Fin 18, t ∈ ({a, b, c} : Finset (Fin 18)) → t ≠ s →
        ∀ w : Fin 18, G.Adj t w → w ∈ D → w = v) →
      ∃ c₁ c₂ : Fin 18, c₁ ∈ D ∧ c₂ ∈ D ∧ G.Adj c₁ c₂ ∧
        ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q → p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂ := by
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
theorem dominating_edge_or_induced_C5 (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18))
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (h2k2 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hne : ∃ a b : Fin 18, a ∈ D ∧ b ∈ D ∧ G.Adj a b) :
    (∃ c₁ c₂ : Fin 18, c₁ ∈ D ∧ c₂ ∈ D ∧ G.Adj c₁ c₂ ∧
      ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q →
        p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    ∨ (∃ v₁ v₂ v₃ v₄ v₅ : Fin 18,
        v₁ ∈ D ∧ v₂ ∈ D ∧ v₃ ∈ D ∧ v₄ ∈ D ∧ v₅ ∈ D ∧
        ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 18)).card = 5 ∧
        G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧ G.Adj v₃ v₄ ∧ G.Adj v₄ v₅ ∧ G.Adj v₅ v₁ ∧
        ¬G.Adj v₁ v₃ ∧ ¬G.Adj v₁ v₄ ∧ ¬G.Adj v₂ v₄ ∧ ¬G.Adj v₂ v₅ ∧ ¬G.Adj v₃ v₅ ∧
        ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q →
          p = v₁ ∨ p = v₂ ∨ p = v₃ ∨ p = v₄ ∨ p = v₅) := by
  classical
  have hdeg3 : ∀ x : Fin 18, x ∈ D → G.degree x = 3 := fun x hx => (hmemD x).mp hx
  have hindle : ∀ x : Fin 18, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := hdeg3 x hx
  have tri : ∀ x y z : Fin 18, x ∈ D → y ∈ D → z ∈ D → x ≠ y → y ≠ z → x ≠ z →
      G.Adj x y → G.Adj y z → G.Adj x z → False := by
    intro x y z hx hy hz hxy hyz hxz axy ayz axz
    exact hT ⟨x, y, z, hxy, hyz, hxz, axy, ayz, axz, by
      rw [hdeg3 x hx, hdeg3 y hy, hdeg3 z hz]; omega⟩
  have c4 : ∀ x y z w : Fin 18, x ∈ D → y ∈ D → z ∈ D → w ∈ D →
      ({x, y, z, w} : Finset (Fin 18)).card = 4 →
      G.Adj x y → G.Adj y z → G.Adj z w → G.Adj w x → ¬G.Adj x z → ¬G.Adj y w → False := by
    intro x y z w hx hy hz hw hcard xy yz zw wx nxz nyw
    exact hC4 ⟨x, y, z, w, hcard, xy, yz, zw, wx, nxz, nyw, by
      rw [hdeg3 x hx, hdeg3 y hy, hdeg3 z hz, hdeg3 w hw]; omega⟩
  have k2 : ∀ x y z w : Fin 18, x ∈ D → y ∈ D → z ∈ D → w ∈ D →
      ({x, y, z, w} : Finset (Fin 18)).card = 4 →
      G.Adj x y → G.Adj z w → ¬G.Adj x z → ¬G.Adj x w → ¬G.Adj y z → ¬G.Adj y w → False := by
    intro x y z w hx hy hz hw hcard xy zw nxz nxw nyz nyw
    exact h2k2 ⟨x, y, z, w, hcard, hdeg3 x hx, hdeg3 y hy, hdeg3 z hz, hdeg3 w hw,
      xy, zw, nxz, nxw, nyz, nyw⟩
  -- Case split on the existence of an in-`M`-degree-3 vertex.
  by_cases hd3 : ∃ v : Fin 18, v ∈ D ∧ 3 ≤ (G.neighborFinset v ∩ D).card
  · obtain ⟨v, hvD, hv3⟩ := hd3
    have hv3' : (G.neighborFinset v ∩ D).card = 3 := le_antisymm (hindle v hvD) hv3
    obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hv3'
    have hmem : ∀ w : Fin 18, w ∈ ({a, b, c} : Finset (Fin 18)) →
        G.Adj v w ∧ w ∈ D := by
      intro w hw
      have : w ∈ G.neighborFinset v ∩ D := by rw [hset]; exact hw
      exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp this).1,
        (Finset.mem_inter.mp this).2⟩
    obtain ⟨hva, haD⟩ := hmem a (by simp)
    obtain ⟨hvb, hbD⟩ := hmem b (by simp)
    obtain ⟨hvc, hcD⟩ := hmem c (by simp)
    have hcharv : ∀ w : Fin 18, G.Adj v w → w ∈ D → w = a ∨ w = b ∨ w = c := by
      intro w hvw hwD
      have : w ∈ G.neighborFinset v ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvw, hwD⟩
      rw [hset] at this; simpa using this
    exact Or.inl (d3_dominating G D hmemD hT hC4 h2k2 v a b c hvD haD hbD hcD hva hvb hvc
      hab hac hbc hcharv)
  · -- All in-`M`-degrees are `≤ 2`.
    push Not at hd3
    have hle2 : ∀ v : Fin 18, v ∈ D → (G.neighborFinset v ∩ D).card ≤ 2 := by
      intro v hv; have := hd3 v hv; omega
    obtain ⟨a0, b0, ha0, hb0, hab0⟩ := hne
    by_cases h2 : ∃ y : Fin 18, y ∈ D ∧ (G.neighborFinset y ∩ D).card = 2
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
      have hchary : ∀ w : Fin 18, G.Adj y w → w ∈ D → w = x ∨ w = z := by
        intro w hyw hwD
        have : w ∈ G.neighborFinset y ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hyw, hwD⟩
        rw [hyset] at this; simpa using this
      -- Domination from a no-extra sibling.
      have dom_gen : ∀ n1 n2 : Fin 18, n1 ∈ D → n2 ∈ D → n1 ≠ n2 → G.Adj y n1 → G.Adj y n2 →
          (∀ w : Fin 18, G.Adj y w → w ∈ D → w = n1 ∨ w = n2) →
          (∀ w : Fin 18, G.Adj n2 w → w ∈ D → w = y) →
          ∃ c₁ c₂ : Fin 18, c₁ ∈ D ∧ c₂ ∈ D ∧ G.Adj c₁ c₂ ∧
            ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q →
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
          (card_four_eighteen n2 y p q (G.ne_of_adj hyn2).symm (Ne.symm hpn2) (Ne.symm hqn2)
            (Ne.symm hpy) (Ne.symm hqy) hpq.ne)
          hyn2.symm hpq hn2p hn2q hyp hyq
      by_cases hze : ∃ w : Fin 18, w ∈ D ∧ w ≠ y ∧ G.Adj z w
      · by_cases hxe : ∃ w : Fin 18, w ∈ D ∧ w ≠ y ∧ G.Adj x w
        · -- Both siblings have an extra neighbour: an induced `C₅` forms.
          obtain ⟨x', hx'D, hx'y, hxx'⟩ := hxe
          obtain ⟨z', hz'D, hz'y, hzz'⟩ := hze
          -- Saturated neighbourhoods of `x` and `z`.
          have hxfull : G.neighborFinset x ∩ D = ({y, x'} : Finset (Fin 18)) := by
            have hsub : ({y, x'} : Finset (Fin 18)) ⊆ G.neighborFinset x ∩ D := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hyx.symm, hyD⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxx', hx'D⟩
            have hc2 : ({y, x'} : Finset (Fin 18)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx'y]), Finset.card_singleton]
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 x hxD)).symm
          have hcharx : ∀ w : Fin 18, G.Adj x w → w ∈ D → w = y ∨ w = x' := by
            intro w hxw hwD
            have : w ∈ G.neighborFinset x ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw, hwD⟩
            rw [hxfull] at this; simpa using this
          have hzfull : G.neighborFinset z ∩ D = ({y, z'} : Finset (Fin 18)) := by
            have hsub : ({y, z'} : Finset (Fin 18)) ⊆ G.neighborFinset z ∩ D := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hyz.symm, hyD⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzz', hz'D⟩
            have hc2 : ({y, z'} : Finset (Fin 18)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm hz'y]), Finset.card_singleton]
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 z hzD)).symm
          have hcharz : ∀ w : Fin 18, G.Adj z w → w ∈ D → w = y ∨ w = z' := by
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
              (card_four_eighteen x x' z y (G.ne_of_adj hxx') hxz (Ne.symm hynx) hx'z hx'y
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
              (card_four_eighteen x x' z z' (G.ne_of_adj hxx') hxz hxz' hx'z hx'z'
                (G.ne_of_adj hzz'))
              hxx' hzz' hnxz hnxz' hnx'z hn
          -- Saturated neighbourhoods of `x'` and `z'` (closing the `C₅`).
          have hx'full : G.neighborFinset x' ∩ D = ({x, z'} : Finset (Fin 18)) := by
            have hsub : ({x, z'} : Finset (Fin 18)) ⊆ G.neighborFinset x' ∩ D := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxx'.symm, hxD⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjx'z', hz'D⟩
            have hc2 : ({x, z'} : Finset (Fin 18)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [hxz']), Finset.card_singleton]
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 x' hx'D)).symm
          have hcharx' : ∀ w : Fin 18, G.Adj x' w → w ∈ D → w = x ∨ w = z' := by
            intro w hx'w hwD
            have : w ∈ G.neighborFinset x' ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hx'w, hwD⟩
            rw [hx'full] at this; simpa using this
          have hz'full : G.neighborFinset z' ∩ D = ({z, x'} : Finset (Fin 18)) := by
            have hsub : ({z, x'} : Finset (Fin 18)) ⊆ G.neighborFinset z' ∩ D := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzz'.symm, hzD⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjx'z'.symm, hx'D⟩
            have hc2 : ({z, x'} : Finset (Fin 18)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx'z]), Finset.card_singleton]
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 z' hz'D)).symm
          have hcharz' : ∀ w : Fin 18, G.Adj z' w → w ∈ D → w = z ∨ w = x' := by
            intro w hz'w hwD
            have : w ∈ G.neighborFinset z' ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hz'w, hwD⟩
            rw [hz'full] at this; simpa using this
          refine Or.inr ⟨x, y, z, z', x', hxD, hyD, hzD, hz'D, hx'D, ?_,
            hyx.symm, hyz, hzz', hadjx'z'.symm, hxx'.symm,
            hnxz, hnxz', hnyz', hnyx', fun h => hnx'z h.symm, ?_⟩
          · exact card_five_eighteen x y z z' x' (Ne.symm hynx) hxz hxz' (G.ne_of_adj hxx')
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
              (card_four_eighteen x y p q (Ne.symm hynx) (Ne.symm hpx) (Ne.symm hqx)
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
      have hle1 : ∀ v : Fin 18, v ∈ D → (G.neighborFinset v ∩ D).card ≤ 1 := by
        intro v hv
        rcases Nat.lt_or_ge ((G.neighborFinset v ∩ D).card) 2 with h | h
        · omega
        · exact absurd ⟨v, hv, le_antisymm (hle2 v hv) h⟩ h2
      have ha0full : G.neighborFinset a0 ∩ D = ({b0} : Finset (Fin 18)) := by
        have hsub : ({b0} : Finset (Fin 18)) ⊆ G.neighborFinset a0 ∩ D := by
          intro w hw; rw [Finset.mem_singleton] at hw; subst hw
          exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab0, hb0⟩
        exact (Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_singleton]; exact hle1 a0 ha0)).symm
      have hb0full : G.neighborFinset b0 ∩ D = ({a0} : Finset (Fin 18)) := by
        have hsub : ({a0} : Finset (Fin 18)) ⊆ G.neighborFinset b0 ∩ D := by
          intro w hw; rw [Finset.mem_singleton] at hw; subst hw
          exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab0.symm, ha0⟩
        exact (Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_singleton]; exact hle1 b0 hb0)).symm
      have hchara0 : ∀ w : Fin 18, G.Adj a0 w → w ∈ D → w = b0 := by
        intro w haw hwD
        have : w ∈ G.neighborFinset a0 ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haw, hwD⟩
        rw [ha0full, Finset.mem_singleton] at this; exact this
      have hcharb0 : ∀ w : Fin 18, G.Adj b0 w → w ∈ D → w = a0 := by
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
        (card_four_eighteen a0 b0 p q hab0.ne (Ne.symm hpa0) (Ne.symm hqa0) (Ne.symm hpb0)
          (Ne.symm hqb0) hpq.ne)
        hab0 hpq hna0p hna0q hnb0p hnb0q


/-- **Bipartite double count.**  For any two vertex sets, the number of `X→Y` incidences equals
the number of `Y→X` incidences. -/
theorem cross_count (G : SimpleGraph (Fin 18)) (X Y : Finset (Fin 18)) :
    ∑ v ∈ X, (G.neighborFinset v ∩ Y).card = ∑ w ∈ Y, (G.neighborFinset w ∩ X).card := by
  have hL : ∀ v : Fin 18, (G.neighborFinset v ∩ Y).card
      = ∑ w ∈ Y, (if G.Adj v w then 1 else 0) := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
  have hR : ∀ w : Fin 18, (G.neighborFinset w ∩ X).card
      = ∑ v ∈ X, (if G.Adj v w then 1 else 0) := by
    intro w
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl
      (fun v _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
  simp_rw [hL, hR]
  exact Finset.sum_comm

/-- **NODE 1 — edge bound for `M = G[D]` (structural).**  The degree-3 subgraph `M` is
triangle-free (`hT`), `C₄`-free (`hC4`) and `2K₂`-free (`h2k2`) with max in-`M`-degree `≤ 3`
(every `D`-vertex has degree `3`).  A `2K₂`-free graph has all its edges in one component; with
girth `≥ 5` (triangle + `C₄`-free) and max-degree `≤ 3` that component is a double-star (`≤ 5`
edges) or `C₅` (`5` edges), so `e(M) ≤ 5`, i.e. `∑_{v∈D}|N v ∩ D| = 2·e(M) ≤ 10`. -/
theorem eM_le_five (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18))
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (h2k2 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d) :
    ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 10 := by
  classical
  have hindle : ∀ x : Fin 18, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  by_cases hne : ∃ a b : Fin 18, a ∈ D ∧ b ∈ D ∧ G.Adj a b
  · rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hA | hB
    · -- **Dominating edge.**
      obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hA
      have hsub : ({c₁, c₂} : Finset (Fin 18)) ⊆ D := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl; exacts [hc1D, hc2D]
      have hsplit :
          ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 18)), (G.neighborFinset v ∩ D).card
            + ∑ v ∈ ({c₁, c₂} : Finset (Fin 18)), (G.neighborFinset v ∩ D).card
          = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
        Finset.sum_sdiff hsub
      have hpair : ∑ v ∈ ({c₁, c₂} : Finset (Fin 18)), (G.neighborFinset v ∩ D).card
          = (G.neighborFinset c₁ ∩ D).card + (G.neighborFinset c₂ ∩ D).card := by
        rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
      have hScong :
          ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 18)), (G.neighborFinset v ∩ D).card
            = ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 18)),
              (G.neighborFinset v ∩ ({c₁, c₂} : Finset (Fin 18))).card := by
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
        cross_count G (D \ ({c₁, c₂} : Finset (Fin 18)))
          ({c₁, c₂} : Finset (Fin 18))] at hsplit
      have hpair2 : ∑ w ∈ ({c₁, c₂} : Finset (Fin 18)),
            (G.neighborFinset w ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))).card
          = (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))).card
            + (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))).card := by
        rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
      have hb1 : (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))).card ≤ 2 := by
        have hss : G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))
            ⊆ (G.neighborFinset c₁ ∩ D).erase c₂ := by
          intro w hw
          obtain ⟨hwN, hwS⟩ := Finset.mem_inter.mp hw
          rw [Finset.mem_sdiff] at hwS
          obtain ⟨hwD, hwnot⟩ := hwS
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwnot
          rw [Finset.mem_erase]
          exact ⟨hwnot.2, Finset.mem_inter.mpr ⟨hwN, hwD⟩⟩
        have hc2mem : c₂ ∈ G.neighborFinset c₁ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
        calc (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))).card
            ≤ ((G.neighborFinset c₁ ∩ D).erase c₂).card := Finset.card_le_card hss
          _ = (G.neighborFinset c₁ ∩ D).card - 1 := Finset.card_erase_of_mem hc2mem
          _ ≤ 2 := by have := hindle c₁ hc1D; omega
      have hb2 : (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))).card ≤ 2 := by
        have hss : G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))
            ⊆ (G.neighborFinset c₂ ∩ D).erase c₁ := by
          intro w hw
          obtain ⟨hwN, hwS⟩ := Finset.mem_inter.mp hw
          rw [Finset.mem_sdiff] at hwS
          obtain ⟨hwD, hwnot⟩ := hwS
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwnot
          rw [Finset.mem_erase]
          exact ⟨hwnot.1, Finset.mem_inter.mpr ⟨hwN, hwD⟩⟩
        have hc1mem : c₁ ∈ G.neighborFinset c₂ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
        calc (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 18)))).card
            ≤ ((G.neighborFinset c₂ ∩ D).erase c₁).card := Finset.card_le_card hss
          _ = (G.neighborFinset c₂ ∩ D).card - 1 := Finset.card_erase_of_mem hc1mem
          _ ≤ 2 := by have := hindle c₂ hc2D; omega
      have hi1 := hindle c₁ hc1D
      have hi2 := hindle c₂ hc2D
      rw [hpair2, hpair] at hsplit
      omega
    · -- **Induced `C₅` carrying all edges.**
      obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1, hv2, hv3, hv4, hv5, hcard5,
        e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, hcov⟩ := hB
      have nbhd : ∀ u na nb o1 o2 : Fin 18, ¬G.Adj u o1 → ¬G.Adj u o2 →
          (∀ w : Fin 18, w ∈ D → G.Adj u w →
            w = u ∨ w = na ∨ w = nb ∨ w = o1 ∨ w = o2) →
          (G.neighborFinset u ∩ D).card ≤ 2 := by
        intro u na nb o1 o2 hno1 hno2 hucov
        have hss : G.neighborFinset u ∩ D ⊆ ({na, nb} : Finset (Fin 18)) := by
          intro w hw
          obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
          have huw : G.Adj u w := (G.mem_neighborFinset _ _).mp hwN
          rcases hucov w hwD huw with e | e | e | e | e
          · exact absurd (e ▸ huw) G.irrefl
          · rw [e]; simp
          · rw [e]; simp
          · exact absurd (e ▸ huw) hno1
          · exact absurd (e ▸ huw) hno2
        calc (G.neighborFinset u ∩ D).card ≤ ({na, nb} : Finset (Fin 18)).card :=
              Finset.card_le_card hss
          _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
      have hbound : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 18)),
          (G.neighborFinset v ∩ D).card ≤ 2 := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact nbhd v v₂ v₅ v₃ v₄ n13 n14
            (fun w hwD hvw => by have := hcov w v hwD hv1 hvw.symm; tauto)
        · exact nbhd v v₁ v₃ v₄ v₅ n24 n25
            (fun w hwD hvw => by have := hcov w v hwD hv2 hvw.symm; tauto)
        · exact nbhd v v₂ v₄ v₁ v₅ (fun h => n13 h.symm) n35
            (fun w hwD hvw => by have := hcov w v hwD hv3 hvw.symm; tauto)
        · exact nbhd v v₃ v₅ v₁ v₂ (fun h => n14 h.symm) (fun h => n24 h.symm)
            (fun w hwD hvw => by have := hcov w v hwD hv4 hvw.symm; tauto)
        · exact nbhd v v₄ v₁ v₂ v₃ (fun h => n25 h.symm) (fun h => n35 h.symm)
            (fun w hwD hvw => by have := hcov w v hwD hv5 hvw.symm; tauto)
      have hC5sub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 18)) ⊆ D := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        exacts [hv1, hv2, hv3, hv4, hv5]
      have hsplit :
          ∑ v ∈ D \ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 18)), (G.neighborFinset v ∩ D).card
            + ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 18)), (G.neighborFinset v ∩ D).card
          = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
        Finset.sum_sdiff hC5sub
      have hiso : ∑ v ∈ D \ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 18)),
          (G.neighborFinset v ∩ D).card = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [Finset.mem_sdiff] at hv
        obtain ⟨hvD, hvnot⟩ := hv
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
        have hvw : G.Adj v w := (G.mem_neighborFinset _ _).mp hwN
        have hin := hcov v w hvD hwD hvw
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvnot
        rcases hin with e | e | e | e | e
        exacts [hvnot.1 e, hvnot.2.1 e, hvnot.2.2.1 e, hvnot.2.2.2.1 e, hvnot.2.2.2.2 e]
      have hC5sum : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 18)),
          (G.neighborFinset v ∩ D).card ≤ 10 := by
        have h1 := Finset.sum_le_sum hbound
        rw [Finset.sum_const, smul_eq_mul, hcard5] at h1
        omega
      rw [hiso, zero_add] at hsplit
      omega
  · -- **No edge.**
    push Not at hne
    have hzero : ∀ v : Fin 18, v ∈ D → (G.neighborFinset v ∩ D).card = 0 := by
      intro v hv
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact hne v w hv hw.2 hw.1
    calc ∑ v ∈ D, (G.neighborFinset v ∩ D).card
        = ∑ _v ∈ D, 0 := Finset.sum_congr rfl (fun v hv => hzero v hv)
      _ ≤ 10 := by simp


/-- **Degree-partition bound for the `n = 18` residual (fully proved).**  With `32` edges and
minimum degree `3` on `18` vertices, the hub set `Hub = filter (4 ≤ deg)` has `Hub.card ≤ 10` and
the degree-3 set `D = filter (deg = 3)` has `8 ≤ D.card` (handshake:
`4·|Hub| ≤ ∑_{Hub} deg = 10 + 3·|Hub|`). -/
theorem residual_hub_card_le_ten (G : SimpleGraph (Fin 18)) (hm : G.edgeFinset.card = 32)
    (h3 : ∀ v : Fin 18, 3 ≤ G.degree v) :
    (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card ≤ 10 ∧
      8 ≤ (Finset.univ.filter (fun w => G.degree w = 3)).card := by
  classical
  have hsum : ∑ v : Fin 18, G.degree v = 64 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  set D : Finset (Fin 18) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 18) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 18, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hDH : ∀ v : Fin 18, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub := by
    rw [Finset.disjoint_left]; intro v hv hv'
    have := (hmemD v).mp hv; have := (hmemHub v).mp hv'; omega
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard18 : D.card + Hub.card = 18 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 64 := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
    have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
    have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul, mul_comm] using h
  rw [hsumD] at hsumpart
  omega


/-- **`∑_{v∈D}|N v ∩ D|` is even (handshake on `M = G[D]`).**  This sum is `2·e(M)`, twice the
edge count of the induced degree-3 subgraph. -/
theorem eM_even (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18)) :
    Even (∑ v ∈ D, (G.neighborFinset v ∩ D).card) := by
  classical
  set M : SimpleGraph (Fin 18) :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ D ∧ b ∈ D
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun a h => G.irrefl h.1⟩ } with hMdef
  have hMadj : ∀ a b : Fin 18, M.Adj a b ↔ G.Adj a b ∧ a ∈ D ∧ b ∈ D := fun _ _ => Iff.rfl
  have hMdeg : ∀ v : Fin 18,
      M.degree v = if v ∈ D then (G.neighborFinset v ∩ D).card else 0 := by
    intro v
    have hd : M.degree v = (M.neighborFinset v).card := rfl
    rw [hd]
    by_cases hvD : v ∈ D
    · simp only [hvD, if_true]
      congr 1
      ext w
      rw [SimpleGraph.mem_neighborFinset, hMadj, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hvD, h.2⟩⟩
    · simp only [hvD, if_false]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, hMadj] at hw
      exact hvD hw.2.1
  have hsumM : ∑ v : Fin 18, M.degree v = ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
    simp_rw [hMdeg]
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [← hsumM]
  exact ⟨M.edgeFinset.card, by rw [M.sum_degrees_eq_twice_card_edges]; ring⟩

/-- **Each `M`-isolated twin meets exactly three hubs (fully proved).**  An `M`-isolated degree-3
twin `t` (`(N t ∩ D).card = 0`) has all three of its neighbours in `Hub`, so
`(N t ∩ Hub).card = 3`. -/
theorem each_iso_three_hubs (G : SimpleGraph (Fin 18)) (D Hub : Finset (Fin 18))
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hmemHub : ∀ v : Fin 18, v ∈ Hub ↔ 4 ≤ G.degree v)
    (h3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (t : Fin 18) (htD : t ∈ D) (htiso : (G.neighborFinset t ∩ D).card = 0) :
    (G.neighborFinset t ∩ Hub).card = 3 := by
  classical
  have hDH : ∀ v : Fin 18, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hsub : G.neighborFinset t ⊆ Hub := by
    intro x hx
    rcases hDH x with hxD | hxH
    · exfalso
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at htiso
      exact htiso x (Finset.mem_inter.mpr ⟨hx, hxD⟩)
    · exact hxH
  rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, (hmemD t).mp htD]

/-- **Single-component bound for the non-isolated set of `M = G[D]` (fully proved).**  Twice the
number of `M`-non-isolated degree-3 vertices is at most `∑_{v∈D}|N v ∩ D| + 2 = 2·e(M) + 2`.  The
proof is the `2K₂`-free single-component argument of `two_isolated_twins`: the non-isolated set is a
single connected component of `M`, so it has at most `e(M) + 1` vertices. -/
theorem nonisolated_component_bound (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18))
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (h2k2 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d) :
    2 * (D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0)).card
      ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card + 2 := by
  classical
  set S : Finset (Fin 18) := D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) with hSdef
  set M : SimpleGraph (Fin 18) :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ D ∧ b ∈ D
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun a h => G.irrefl h.1⟩ } with hMdef
  have hMadj : ∀ a b : Fin 18, M.Adj a b ↔ G.Adj a b ∧ a ∈ D ∧ b ∈ D := fun _ _ => Iff.rfl
  have hSmem : ∀ v : Fin 18, v ∈ S ↔ v ∈ D ∧ ∃ w : Fin 18, G.Adj v w ∧ w ∈ D := by
    intro v
    rw [hSdef, Finset.mem_filter]
    refine and_congr_right (fun _ => ?_)
    rw [← ne_eq, Finset.card_ne_zero]
    simp only [Finset.Nonempty, Finset.mem_inter, G.mem_neighborFinset]
  have hsupp : M.support = (↑S : Set (Fin 18)) := by
    ext v
    rw [SimpleGraph.mem_support, Finset.mem_coe, hSmem]
    constructor
    · rintro ⟨w, hadj, hvD, hwD⟩; exact ⟨hvD, w, hadj, hwD⟩
    · rintro ⟨hvD, w, hadj, hwD⟩; exact ⟨w, hadj, hvD, hwD⟩
  have hMdeg : ∀ v : Fin 18,
      M.degree v = if v ∈ D then (G.neighborFinset v ∩ D).card else 0 := by
    intro v
    have hd : M.degree v = (M.neighborFinset v).card := rfl
    rw [hd]
    by_cases hvD : v ∈ D
    · simp only [hvD, if_true]
      congr 1
      ext w
      rw [SimpleGraph.mem_neighborFinset, hMadj, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hvD, h.2⟩⟩
    · simp only [hvD, if_false]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, hMadj] at hw
      exact hvD hw.2.1
  have hsumM : ∑ v : Fin 18, M.degree v = ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
    simp_rw [hMdeg]
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe]; simp
  · have hVne : Nonempty ↥M.support := by
      obtain ⟨x, hx⟩ := hSne
      exact ⟨⟨x, by rw [hsupp]; exact Finset.mem_coe.mpr hx⟩⟩
    have radj : ∀ {a b : Fin 18} (ha : a ∈ M.support) (hb : b ∈ M.support),
        M.Adj a b → (M.induce M.support).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b ha hb hab
      exact (SimpleGraph.induce_adj.mpr hab).reachable
    have hpre : (M.induce M.support).Preconnected := by
      intro u v
      set a : Fin 18 := (↑u : Fin 18) with hadef
      set b : Fin 18 := (↑v : Fin 18) with hbdef
      obtain ⟨a', haa'⟩ := u.2
      obtain ⟨b', hbb'⟩ := v.2
      replace haa' : M.Adj a a' := haa'
      replace hbb' : M.Adj b b' := hbb'
      have ha'supp : a' ∈ M.support := haa'.mem_support_right
      have hb'supp : b' ∈ M.support := hbb'.mem_support_right
      have hA := (hMadj a a').mp haa'
      have hB := (hMadj b b').mp hbb'
      have haD : a ∈ D := hA.2.1
      have ha'D : a' ∈ D := hA.2.2
      have hbD : b ∈ D := hB.2.1
      have hb'D : b' ∈ D := hB.2.2
      by_cases hab : a = b
      · have huv : u = v := Subtype.ext hab
        rw [huv]
      by_cases hab' : a = b'
      · have hadj : M.Adj a b := by
          rw [← hab'] at hbb'; exact hbb'.symm
        exact radj u.2 v.2 hadj
      by_cases ha'b : a' = b
      · have hadj : M.Adj a b := by rw [ha'b] at haa'; exact haa'
        exact radj u.2 v.2 hadj
      by_cases ha'b' : a' = b'
      · have hUV : (⟨a', ha'supp⟩ : ↥M.support) = ⟨b', hb'supp⟩ := Subtype.ext ha'b'
        exact (radj u.2 ha'supp haa').trans (hUV ▸ (radj v.2 hb'supp hbb').symm)
      · have hcard4 : ({a, a', b, b'} : Finset (Fin 18)).card = 4 :=
          card_four_eighteen a a' b b' haa'.ne hab hab' ha'b ha'b' hbb'.ne
        have hcross : G.Adj a b ∨ G.Adj a b' ∨ G.Adj a' b ∨ G.Adj a' b' := by
          by_contra hc
          simp only [not_or] at hc
          exact h2k2 ⟨a, a', b, b', hcard4,
            (hmemD a).mp haD, (hmemD a').mp ha'D, (hmemD b).mp hbD, (hmemD b').mp hb'D,
            hA.1, hB.1, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
        rcases hcross with h | h | h | h
        · exact radj u.2 v.2 ((hMadj a b).mpr ⟨h, haD, hbD⟩)
        · exact (radj u.2 hb'supp ((hMadj a b').mpr ⟨h, haD, hb'D⟩)).trans
            (radj v.2 hb'supp hbb').symm
        · exact (radj u.2 ha'supp haa').trans
            (radj ha'supp v.2 ((hMadj a' b).mpr ⟨h, ha'D, hbD⟩))
        · exact ((radj u.2 ha'supp haa').trans
            (radj ha'supp hb'supp ((hMadj a' b').mpr ⟨h, ha'D, hb'D⟩))).trans
            (radj v.2 hb'supp hbb').symm
    have hconn : (M.induce M.support).Connected := by
      have := hVne
      exact ⟨hpre⟩
    have hbound := hconn.card_vert_le_card_edgeSet_add_one
    have hns : Nat.card ↥M.support = S.card := by
      rw [hsupp, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hes : Nat.card (M.induce M.support).edgeSet = M.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
        SimpleGraph.card_edgeFinset_induce_support]
    rw [hns, hes] at hbound
    have hh := M.sum_degrees_eq_twice_card_edges
    rw [hsumM] at hh
    omega

/-- **Hub meets an induced `P₃` in at most one vertex.**  A degree-`4` hub `h` cannot be adjacent
to two vertices of a degree-`3` induced path `x–y–z`: two adjacent hits give a good triangle
(degree-sum `≤ 10`, ruled out by `hT`); the distance-`2` hit `x, z` gives a good `C₄`
`h–x–y–z–h` (degree-sum `13 ≤ 14`, ruled out by `hC4`). -/
theorem hub_meets_path_le_one_eighteen (G : SimpleGraph (Fin 18))
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    {h x y z : Fin 18} (hh : G.degree h = 4)
    (hx : G.degree x = 3) (hy : G.degree y = 3) (hz : G.degree z = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : ¬G.Adj x z)
    (hne_xy : x ≠ y) (hne_yz : y ≠ z) (hne_xz : x ≠ z) :
    ¬(G.Adj h x ∧ G.Adj h y) ∧ ¬(G.Adj h y ∧ G.Adj h z) ∧ ¬(G.Adj h x ∧ G.Adj h z) := by
  have hne_hx : h ≠ x := by intro e; subst e; omega
  have hne_hy : h ≠ y := by intro e; subst e; omega
  have hne_hz : h ≠ z := by intro e; subst e; omega
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hhx, hhy⟩
    exact hT ⟨h, x, y, hne_hx, hne_xy, hne_hy, hhx, hxy, hhy, by omega⟩
  · rintro ⟨hhy, hhz⟩
    exact hT ⟨h, y, z, hne_hy, hne_yz, hne_hz, hhy, hyz, hhz, by omega⟩
  · rintro ⟨hhx, hhz⟩
    by_cases hhy : G.Adj h y
    · exact hT ⟨h, x, y, hne_hx, hne_xy, hne_hy, hhx, hxy, hhy, by omega⟩
    · exact hC4 ⟨h, x, y, z,
        card_four_eighteen h x y z hne_hx hne_hy hne_hz hne_xy hne_xz hne_yz,
        hhx, hxy, hyz, hhz.symm, hhy, hxz, by omega⟩

/-- **Non-adjacent hubs share at most one isolated twin (`n = 18`, good-`C₄` `Σ ≤ 14`).**  Two
common `M`-isolated-twin neighbours `t₁, t₂` of two non-adjacent degree-`4` hubs `h₁, h₂` form an
induced `C₄` `h₁–t₁–h₂–t₂–h₁` (the two twins are non-adjacent, the two hubs are non-adjacent) of
degree sum `4 + 3 + 4 + 3 = 14 ≤ 14`, contradicting the `n = 18` good-`C₄` hypothesis `hC4`.  This
sharper `≤ 1` bound (a twin-hub-twin-hub `C₄` has `Σ = 14`, included at the `n = 18` good-`C₄`
threshold `≤ 14`); at a threshold `≤ 13` it would fail. -/
theorem nonadj_hubs_share_le_one_iso (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 18, w ∈ Dᶜ → G.degree w = 4)
    (h₁ h₂ : Fin 18) (h1Dc : h₁ ∈ Dᶜ) (h2Dc : h₂ ∈ Dᶜ) (hne : h₁ ≠ h₂)
    (hnadj : ¬G.Adj h₁ h₂) :
    ((G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso).card ≤ 1 := by
  classical
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨t₁, ht1, t₂, ht2, h12⟩ := Finset.one_lt_card.mp hgt
  have unpack : ∀ t : Fin 18, t ∈ (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso →
      G.Adj h₁ t ∧ G.Adj h₂ t ∧ t ∈ Iso := by
    intro t ht
    rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
    exact ⟨ht.1.1, ht.1.2, ht.2⟩
  obtain ⟨ha1, hb1, hI1⟩ := unpack t₁ ht1
  obtain ⟨ha2, hb2, hI2⟩ := unpack t₂ ht2
  have htw_nonadj : ¬G.Adj t₁ t₂ := fun hst => (hIsoprop t₁ hI1).2 t₂ hst ((hIsoprop t₂ hI2).1)
  have hti_ne : ∀ t : Fin 18, t ∈ Iso → h₁ ≠ t ∧ h₂ ≠ t := by
    intro t ht
    have htD : t ∈ D := hIsoD ht
    exact ⟨fun e => (Finset.mem_compl.mp h1Dc) (e ▸ htD),
      fun e => (Finset.mem_compl.mp h2Dc) (e ▸ htD)⟩
  obtain ⟨hh1t1, hh2t1⟩ := hti_ne t₁ hI1
  obtain ⟨hh1t2, hh2t2⟩ := hti_ne t₂ hI2
  apply hC4
  -- Induced `C₄` `h₁–t₁–h₂–t₂–h₁` with diagonals `h₁–h₂` and `t₁–t₂` absent.
  refine ⟨h₁, t₁, h₂, t₂, ?_, ha1, hb1.symm, hb2, ha2.symm, hnadj, htw_nonadj, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hh1t1, hne, hh1t2]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hh2t1, h12]),
      Finset.card_insert_of_notMem (by simp [hh2t2]), Finset.card_singleton]
  · have e1 := hdeg4 h₁ h1Dc
    have e2 := hdeg4 h₂ h2Dc
    have e3 := (hIsoprop t₁ hI1).1
    have e4 := (hIsoprop t₂ hI2).1
    omega

end N18

end ACMax
