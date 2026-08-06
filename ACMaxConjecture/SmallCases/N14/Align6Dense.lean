import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.Align
import ACMaxConjecture.SmallCases.N14.TwoHub
import ACMaxConjecture.SmallCases.N14.C5

/-!
# The dense `|D| = 8` residual of the `e(M) = 3` alignment (`n = 14`)

This file closes the genuinely residual `|D| = 8` regime of `exists_align_six_config`
(`TwinCert14Align6`).  In that regime the degree sequence is rigid: six degree-`4` hubs with
`e(Hub) = 3`, four `M`-isolated degree-`3` twins (each with exactly three hub-neighbours, so `12`
twin–hub edges), and four non-isolated degree-`3` vertices inducing a claw `K_{1,3}` or a path
`P₄`.  A cherry (induced `P₃`) of degree-`3` vertices is selected inside the non-isolated set; each
degree-`4` hub meets the cherry in at most one vertex, and a structural cascade produces one of the
three signed-cut configurations `SingleVertexConfig`, `TwoTwinConfig`, `TwoHubConfig`.

The three config predicates are spelled out here as raw existentials so the file can be imported by
`TwinCert14Align6` without a cycle; they are definitionally the `def`s there.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Two-twin assembly.**  Two `M`-isolated degree-`3` twins `t₁, t₂` sharing a degree-`4` hub `h`
that avoids a cherry `x–y–z` package into the `TwoTwinConfig` existential. -/
theorem dense_two_twin_assemble (G : SimpleGraph (Fin 14)) (t₁ t₂ h x y z : Fin 14)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3) (hhdeg4 : G.degree h = 4)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h) (hxyA : G.Adj x y) (hyzA : G.Adj y z)
    (ht1iso : ∀ w : Fin 14, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 14, G.Adj t₂ w → G.degree w ≠ 3)
    (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z)
    (ht12 : t₁ ≠ t₂) (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z) :
    ∃ t₁' t₂' h' x' y' z' : Fin 14,
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

/-- **`e(M)` formula in a dominating-edge case (`n = 14`).**  When every `M`-edge meets the edge
`{c₁, c₂}`, `∑_{v∈D}|N v ∩ D| = 2·inM(c₁) + 2·inM(c₂) − 2` (the shared edge `c₁c₂` is
double-counted), written additively to avoid `ℕ` subtraction.  Port of the `n = 13`
`thin_eM_formula`. -/
theorem thin_eM_formula_fourteen (G : SimpleGraph (Fin 14)) (D : Finset (Fin 14))
    (c₁ c₂ : Fin 14) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 14, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    ∑ v ∈ D, (G.neighborFinset v ∩ D).card + 2
      = 2 * (G.neighborFinset c₁ ∩ D).card + 2 * (G.neighborFinset c₂ ∩ D).card := by
  classical
  have hc2mem : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have hsub : ({c₁, c₂} : Finset (Fin 14)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl; exacts [hc1D, hc2D]
  have hsplit :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 14)), (G.neighborFinset v ∩ D).card
        + ∑ v ∈ ({c₁, c₂} : Finset (Fin 14)), (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_sdiff hsub
  have hpair : ∑ v ∈ ({c₁, c₂} : Finset (Fin 14)), (G.neighborFinset v ∩ D).card
      = (G.neighborFinset c₁ ∩ D).card + (G.neighborFinset c₂ ∩ D).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hScong :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 14)), (G.neighborFinset v ∩ D).card
        = ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 14)),
          (G.neighborFinset v ∩ ({c₁, c₂} : Finset (Fin 14))).card := by
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
    cross_count_fourteen G (D \ ({c₁, c₂} : Finset (Fin 14)))
      ({c₁, c₂} : Finset (Fin 14))] at hsplit
  have hpair2 : ∑ w ∈ ({c₁, c₂} : Finset (Fin 14)),
        (G.neighborFinset w ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card
      = (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card
        + (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have he1 : (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card
      = (G.neighborFinset c₁ ∩ D).card - 1 := by
    have hset : G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))
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
  have he2 : (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card
      = (G.neighborFinset c₂ ∩ D).card - 1 := by
    have hset : G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))
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
  have hpos1 : 1 ≤ (G.neighborFinset c₁ ∩ D).card := Finset.card_pos.mpr ⟨c₂, hc2mem⟩
  have hpos2 : 1 ≤ (G.neighborFinset c₂ ∩ D).card := Finset.card_pos.mpr ⟨c₁, hc1mem⟩
  omega

/-- **Dense `|D| = 8` residual of the `e(M) = 3` three-way alignment dichotomy.**  Self-contained
analogue of `exists_align_six_config`, specialised to `|D| = 8`: it derives the rigid dense regime
and produces one of the three signed-cut configurations. -/
theorem exists_align_six_config_dense (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 14, ({a, b, c, d, e} : Finset (Fin 14)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 14, G.degree t = 3 ∧ ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3)
    (hs6 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 6)
    (hD8card : (Finset.univ.filter (fun w => G.degree w = 3)).card = 8) :
    (∃ v h₁ h₂ x y z : Fin 14,
      G.degree v = 3 ∧ G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
      G.Adj v h₁ ∧ G.Adj v h₂ ∧ G.Adj x y ∧ G.Adj y z ∧ ¬G.Adj x z ∧
      2 * (∑ p ∈ ({v, h₁, h₂} : Finset (Fin 14)),
          (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 14))).card)
          + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * (if G.Adj h₁ h₂ then 1 else 0) ∧
      h₁ ≠ h₂ ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z ∧
      h₁ ≠ x ∧ h₁ ≠ y ∧ h₁ ≠ z ∧ h₂ ≠ x ∧ h₂ ≠ y ∧ h₂ ≠ z ∧
      x ≠ y ∧ y ≠ z ∧ x ≠ z) ∨
    (∃ t₁ t₂ h x y z : Fin 14,
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.degree h ≤ 5 ∧
      G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
      G.Adj t₁ h ∧ G.Adj t₂ h ∧ G.Adj x y ∧ G.Adj y z ∧
      ¬G.Adj t₁ x ∧ ¬G.Adj t₁ y ∧ ¬G.Adj t₁ z ∧
      ¬G.Adj t₂ x ∧ ¬G.Adj t₂ y ∧ ¬G.Adj t₂ z ∧
      ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z ∧
      t₁ ≠ t₂ ∧ t₁ ≠ x ∧ t₁ ≠ y ∧ t₁ ≠ z ∧ t₂ ≠ x ∧ t₂ ≠ y ∧ t₂ ≠ z ∧
      h ≠ x ∧ h ≠ y ∧ h ≠ z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z) ∨
    (∃ h₁ h₂ a b c d : Fin 14,
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj d h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ d ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧
      ¬G.Adj b h₂ ∧ ¬G.Adj b c ∧ ¬G.Adj b d ∧
      h₁ ≠ h₂ ∧ h₁ ≠ a ∧ h₁ ≠ b ∧ h₁ ≠ c ∧ h₁ ≠ d ∧
      h₂ ≠ a ∧ h₂ ≠ b ∧ h₂ ≠ c ∧ h₂ ≠ d ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hne : ∃ a b : Fin 14, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by
      intro v hv
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact hcon v w hv hw.2 hw.1
    have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := Finset.sum_eq_zero hz
    omega
  rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
  · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hdomprop⟩ := hdom
    obtain ⟨hHub6, hD8⟩ := residual_hub_card_le_six G hm h3
    rw [← hDdef] at hD8
    have hdegD : ∀ v : Fin 14, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
    -- A vertex of the dominating edge has in-`M`-degree `≥ 2` (else `e(M) ≤ 1`, contradicting `6`).
    have hcen : 2 ≤ (G.neighborFinset c₁ ∩ D).card ∨ 2 ≤ (G.neighborFinset c₂ ∩ D).card := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hc2in : c₂ ∈ G.neighborFinset c₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
      have hc1in : c₁ ∈ G.neighborFinset c₂ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
      have h1' : ∀ a ∈ G.neighborFinset c₁ ∩ D, ∀ b ∈ G.neighborFinset c₁ ∩ D, a = b :=
        Finset.card_le_one.mp (by omega)
      have h2' : ∀ a ∈ G.neighborFinset c₂ ∩ D, ∀ b ∈ G.neighborFinset c₂ ∩ D, a = b :=
        Finset.card_le_one.mp (by omega)
      have hzero : ∀ v ∈ D,
          (G.neighborFinset v ∩ D).card ≤ (if v = c₁ ∨ v = c₂ then 1 else 0) := by
        intro v hvD
        by_cases hv : v = c₁ ∨ v = c₂
        · rw [if_pos hv]
          rcases hv with rfl | rfl
          · omega
          · omega
        · rw [if_neg hv, Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          obtain ⟨hvw, hwD⟩ := hw
          have hdom4 := hdomprop v w hvD hwD hvw
          push Not at hv
          rcases hdom4 with e | e | e | e
          · exact hv.1 e
          · exact hv.2 e
          · have hvmem : v ∈ G.neighborFinset c₁ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hvw).symm, hvD⟩
            exact hv.2 (h1' v hvmem c₂ hc2in)
          · have hvmem : v ∈ G.neighborFinset c₂ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hvw).symm, hvD⟩
            exact hv.1 (h2' v hvmem c₁ hc1in)
      have hsumle : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
          ≤ ∑ v ∈ D, (if v = c₁ ∨ v = c₂ then (1 : ℕ) else 0) := Finset.sum_le_sum hzero
      have hrhs : ∑ v ∈ D, (if v = c₁ ∨ v = c₂ then (1 : ℕ) else 0) ≤ 2 := by
        rw [← Finset.card_filter]
        have hsubset : D.filter (fun v => v = c₁ ∨ v = c₂) ⊆ ({c₁, c₂} : Finset (Fin 14)) := by
          intro v hv
          rw [Finset.mem_filter] at hv
          rcases hv.2 with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        calc (D.filter (fun v => v = c₁ ∨ v = c₂)).card
            ≤ ({c₁, c₂} : Finset (Fin 14)).card := Finset.card_le_card hsubset
          _ ≤ 2 := by
              have := Finset.card_insert_le c₁ ({c₂} : Finset (Fin 14))
              simp only [Finset.card_singleton] at this
              omega
      omega
    -- The `M`-isolated twin set; at least four twins (`|S| ≤ 4`, `|D| ≥ 8`).
    set Iso : Finset (Fin 14) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
    have hIso4 : 4 ≤ Iso.card := by
      have hnb := nonisolated_component_bound G D hmemD h2k2
      rw [hs6] at hnb
      have hpart := Finset.card_filter_add_card_filter_not (s := D)
        (fun v => (G.neighborFinset v ∩ D).card = 0)
      rw [← hIsodef] at hpart
      omega
    have hIsoprop : ∀ v ∈ Iso,
        G.degree v = 3 ∧ (∀ w : Fin 14, G.Adj v w → G.degree w ≠ 3) := by
      intro v hv
      rw [hIsodef, Finset.mem_filter] at hv
      obtain ⟨hvD, hv0⟩ := hv
      refine ⟨hdegD v hvD, fun w hadj hw3 => ?_⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
      exact hv0 w (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
    -- The degree-`4` hub set has `≤ 6` vertices; each twin has `≥ 2` of them as neighbours.
    set Hub4 : Finset (Fin 14) := Finset.univ.filter (fun h => G.degree h = 4) with hHub4def
    have hHub4card : Hub4.card ≤ 6 := by
      refine le_trans (Finset.card_le_card ?_) hHub6
      intro h hh
      rw [hHub4def, Finset.mem_filter] at hh
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by omega⟩
    have htwo : ∀ v ∈ Iso, 2 ≤ (G.neighborFinset v ∩ Hub4).card := by
      intro v hv
      obtain ⟨hvdeg, hviso⟩ := hIsoprop v hv
      obtain ⟨h₁, h₂, hne, ha1, ha2, hd1, hd2⟩ :=
        isolated_twin_two_deg4_hubs G hm h3 hT hC4 h2k2 v hvdeg hviso
      have hsub : ({h₁, h₂} : Finset (Fin 14)) ⊆ G.neighborFinset v ∩ Hub4 := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha1,
            by rw [hHub4def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hd1⟩⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha2,
            by rw [hHub4def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hd2⟩⟩
      calc 2 = ({h₁, h₂} : Finset (Fin 14)).card := (Finset.card_pair hne).symm
        _ ≤ _ := Finset.card_le_card hsub
    -- Pigeonhole: some degree-`4` hub is adjacent to two distinct twins.
    have hincid : ∃ h ∈ Hub4, 2 ≤ (Iso.filter (fun v => G.Adj v h)).card := by
      by_contra hcon
      push Not at hcon
      have hsum1 : ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card ≤ 6 := by
        calc ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card
            ≤ ∑ _h ∈ Hub4, 1 := Finset.sum_le_sum (fun h hh => by have := hcon h hh; omega)
          _ = Hub4.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ 6 := hHub4card
      have hsum2 : 8 ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
        have hge : 2 * Iso.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
          have := Finset.card_nsmul_le_sum Iso
            (fun v => (G.neighborFinset v ∩ Hub4).card) 2 htwo
          simpa [smul_eq_mul, mul_comm] using this
        omega
      have hswap : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
          = ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card := by
        have hL : ∀ v : Fin 14, (G.neighborFinset v ∩ Hub4).card
            = (Hub4.filter (fun h => G.Adj v h)).card := by
          intro v
          congr 1
          ext h
          simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_filter]
          tauto
        simp_rw [hL, Finset.card_filter]
        rw [Finset.sum_comm]
      omega
    obtain ⟨h, hhHub4, hh2⟩ := hincid
    obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (Iso.filter (fun v => G.Adj v h)).card)
    rw [Finset.mem_filter] at ht1 ht2
    obtain ⟨ht1Iso, hAt1h⟩ := ht1
    obtain ⟨ht2Iso, hAt2h⟩ := ht2
    have hhdeg4 : G.degree h = 4 := by
      rw [hHub4def, Finset.mem_filter] at hhHub4; exact hhHub4.2
    obtain ⟨ht1deg, ht1iso⟩ := hIsoprop t₁ ht1Iso
    obtain ⟨ht2deg, ht2iso⟩ := hIsoprop t₂ ht2Iso
    -- **Dispatch on the dominating-edge structure: claw (`K_{1,3}`) vs path (`P₄`).**  In the claw
    -- case the centre `c` is hub-free, the shared-twin hub `h` meets at most one leaf, and the two
    -- avoided leaves form a cherry around `c`, landing `TwoTwinConfig` directly.
    have claw_case : ∀ c : Fin 14, c ∈ D → 3 ≤ (G.neighborFinset c ∩ D).card →
        ∃ t₁' t₂' h' x' y' z' : Fin 14,
          G.degree t₁' = 3 ∧ G.degree t₂' = 3 ∧ G.degree h' ≤ 5 ∧
          G.degree x' = 3 ∧ G.degree y' = 3 ∧ G.degree z' = 3 ∧
          G.Adj t₁' h' ∧ G.Adj t₂' h' ∧ G.Adj x' y' ∧ G.Adj y' z' ∧
          ¬G.Adj t₁' x' ∧ ¬G.Adj t₁' y' ∧ ¬G.Adj t₁' z' ∧
          ¬G.Adj t₂' x' ∧ ¬G.Adj t₂' y' ∧ ¬G.Adj t₂' z' ∧
          ¬G.Adj h' x' ∧ ¬G.Adj h' y' ∧ ¬G.Adj h' z' ∧
          t₁' ≠ t₂' ∧ t₁' ≠ x' ∧ t₁' ≠ y' ∧ t₁' ≠ z' ∧ t₂' ≠ x' ∧ t₂' ≠ y' ∧ t₂' ≠ z' ∧
          h' ≠ x' ∧ h' ≠ y' ∧ h' ≠ z' ∧ x' ≠ y' ∧ y' ≠ z' ∧ x' ≠ z' := by
      intro c hcD hcge
      have hc3 : G.degree c = 3 := hdegD c hcD
      have hle : (G.neighborFinset c ∩ D).card ≤ 3 := by
        calc (G.neighborFinset c ∩ D).card ≤ (G.neighborFinset c).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = G.degree c := G.card_neighborFinset_eq_degree c
          _ = 3 := hc3
      have heq3 : (G.neighborFinset c ∩ D).card = 3 := le_antisymm hle hcge
      obtain ⟨n₁, n₂, n₃, hne12, hne13, hne23, hset⟩ := Finset.card_eq_three.mp heq3
      have hcardeq : (G.neighborFinset c).card = (G.neighborFinset c ∩ D).card := by
        rw [G.card_neighborFinset_eq_degree, hc3, heq3]
      have hNsubeq : G.neighborFinset c ∩ D = G.neighborFinset c :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq hcardeq)
      have hmem_i : ∀ w : Fin 14, w ∈ ({n₁, n₂, n₃} : Finset (Fin 14)) → G.Adj c w ∧ w ∈ D := by
        intro w hw
        have hw' : w ∈ G.neighborFinset c ∩ D := hset ▸ hw
        exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw').1,
          (Finset.mem_inter.mp hw').2⟩
      obtain ⟨a1, hn1D⟩ := hmem_i n₁ (by simp)
      obtain ⟨a2, hn2D⟩ := hmem_i n₂ (by simp)
      obtain ⟨a3, hn3D⟩ := hmem_i n₃ (by simp)
      have hd1 : G.degree n₁ = 3 := hdegD n₁ hn1D
      have hd2 : G.degree n₂ = 3 := hdegD n₂ hn2D
      have hd3 : G.degree n₃ = 3 := hdegD n₃ hn3D
      have hcnbhd : ∀ w : Fin 14, G.Adj c w → w = n₁ ∨ w = n₂ ∨ w = n₃ := by
        intro w hw
        have hw' : w ∈ G.neighborFinset c ∩ D := by
          rw [hNsubeq]; exact (G.mem_neighborFinset _ _).mpr hw
        rw [hset] at hw'; simpa using hw'
      have hhc : ¬G.Adj h c := by
        intro hadj
        rcases hcnbhd h hadj.symm with e | e | e <;> rw [e] at hhdeg4 <;> omega
      have hmeet : ∀ i j : Fin 14, G.degree i = 3 → G.degree j = 3 →
          G.Adj c i → G.Adj c j → i ≠ j → ¬(G.Adj h i ∧ G.Adj h j) := by
        rintro i j hi3 hj3 ci cj hij ⟨hhi, hhj⟩
        have nij : ¬G.Adj i j := fun aij =>
          hT ⟨c, i, j, ci.ne, hij, cj.ne, ci, aij, cj, by omega⟩
        exact hC4 ⟨h, i, c, j,
          card_four_fourteen h i c j (by rintro rfl; omega) (by rintro rfl; omega)
            (by rintro rfl; omega) ci.ne.symm hij cj.ne,
          hhi, ci.symm, cj, hhj.symm, hhc, nij, by omega⟩
      have not12 := hmeet n₁ n₂ hd1 hd2 a1 a2 hne12
      have not13 := hmeet n₁ n₃ hd1 hd3 a1 a3 hne13
      have not23 := hmeet n₂ n₃ hd2 hd3 a2 a3 hne23
      by_cases hb1 : G.Adj h n₁
      · exact dense_two_twin_assemble G t₁ t₂ h n₂ c n₃ ht1deg ht2deg hhdeg4
          hd2 hc3 hd3 hAt1h hAt2h a2.symm a3 ht1iso ht2iso
          (fun hv => not12 ⟨hb1, hv⟩) hhc (fun hv => not13 ⟨hb1, hv⟩) ht12
          a2.symm.ne a3.ne hne23
      · by_cases hb2 : G.Adj h n₂
        · exact dense_two_twin_assemble G t₁ t₂ h n₁ c n₃ ht1deg ht2deg hhdeg4
            hd1 hc3 hd3 hAt1h hAt2h a1.symm a3 ht1iso ht2iso
            hb1 hhc (fun hv => not23 ⟨hb2, hv⟩) ht12 a1.symm.ne a3.ne hne13
        · exact dense_two_twin_assemble G t₁ t₂ h n₁ c n₂ ht1deg ht2deg hhdeg4
            hd1 hc3 hd2 hAt1h hAt2h a1.symm a2 ht1iso ht2iso
            hb1 hhc hb2 ht12 a1.symm.ne a2.ne hne12
    by_cases hc1three : 3 ≤ (G.neighborFinset c₁ ∩ D).card
    · exact Or.inr (Or.inl (claw_case c₁ hc1D hc1three))
    · by_cases hc2three : 3 ≤ (G.neighborFinset c₂ ∩ D).card
      · exact Or.inr (Or.inl (claw_case c₂ hc2D hc2three))
      · -- **`P₄` case.**  Both dominating endpoints have in-`M`-degree `2`; the degree-3 subgraph
        -- is the path `L₁–c₁–c₂–L₂`.  The two cherries are `L₁–c₁–c₂` and `c₁–c₂–L₂`.  A global
        -- count over the six degree-`4` hubs (each `M`-isolated twin has three hub-neighbours, so
        -- there are twelve twin–hub edges and `∑ |N h ∩ Hub| = 6`) shows that some hub avoiding one
        -- of the two cherries carries two `M`-isolated twins: assuming the contrary, every hub
        -- avoiding a cherry has internal degree `≥ 2` (`≥ 3` if it avoids both), and a weight count
        -- forces both cherry-avoiding sets to coincide as two hubs of internal degree `3`, which is
        -- impossible since all other hubs would then have internal degree `0`.
        classical
        push Not at hc1three hc2three
        -- Hub (`= Dᶜ`) degree facts.
        have hsum48 : ∑ v : Fin 14, G.degree v = 48 := by
          rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
        have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
          rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
        have hcc : D.card + Dᶜ.card = 14 := by
          have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
        have hDccard : Dᶜ.card = 6 := by omega
        have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 48 := by
          rw [Finset.sum_add_sum_compl]; exact hsum48
        have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
          intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
        have hDcdeg4 : ∀ w ∈ Dᶜ, G.degree w = 4 := by
          intro w hw
          by_contra hne4
          have hgt : 5 ≤ G.degree w := by have := hDcdeg w hw; omega
          have hsplit := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
          have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
            have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
              fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
            have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
            simpa [smul_eq_mul, mul_comm] using this
          have hec : (Dᶜ.erase w).card = 5 := by rw [Finset.card_erase_of_mem hw, hDccard]
          rw [hec] at hrest
          omega
        -- In-`M`-degrees of the dominating endpoints are both `2`.
        have hform := thin_eM_formula_fourteen G D c₁ c₂ hc1D hc2D hc12 hdomprop
        rw [hs6] at hform
        have hin1 : (G.neighborFinset c₁ ∩ D).card = 2 := by omega
        have hin2 : (G.neighborFinset c₂ ∩ D).card = 2 := by omega
        have hc1deg : G.degree c₁ = 3 := hdegD c₁ hc1D
        have hc2deg : G.degree c₂ = 3 := hdegD c₂ hc2D
        -- Path leaves `L₁` (of `c₁`) and `L₂` (of `c₂`).
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
        have hL1deg : G.degree L₁ = 3 := hdegD L₁ hL1D
        have hL2mem : L₂ ∈ (G.neighborFinset c₂ ∩ D).erase c₁ := by rw [hL2eq]; simp
        rw [Finset.mem_erase] at hL2mem
        obtain ⟨hL2nc1, hL2ND⟩ := hL2mem
        obtain ⟨hL2N, hL2D⟩ := Finset.mem_inter.mp hL2ND
        have hac2L2 : G.Adj c₂ L₂ := (G.mem_neighborFinset _ _).mp hL2N
        have hL2deg : G.degree L₂ = 3 := hdegD L₂ hL2D
        -- Both cherries are induced `P₃`s.
        have hnL1c2 : ¬G.Adj L₁ c₂ := fun hadj =>
          hT ⟨c₁, L₁, c₂, hac1L1.ne, hL1nc2, hc12.ne, hac1L1, hadj, hc12, by omega⟩
        have hnc1L2 : ¬G.Adj c₁ L₂ := fun hadj =>
          hT ⟨c₂, L₂, c₁, hac2L2.ne, hL2nc1, hc12.ne.symm, hac2L2, hadj.symm, hc12.symm, by omega⟩
        -- `M`-isolation away from the path.
        have hisochar : ∀ w : Fin 14, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso := by
          intro w hwD hwL1 hwc1 hwc2 hwL2
          rw [hIsodef, Finset.mem_filter]
          refine ⟨hwD, ?_⟩
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro u hu
          rw [Finset.mem_inter, G.mem_neighborFinset] at hu
          obtain ⟨hwu, huD⟩ := hu
          rcases hdomprop w u hwD huD hwu with e | e | e | e
          · exact hwc1 e
          · exact hwc2 e
          · have hmem : w ∈ G.neighborFinset c₁ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hwu).symm, hwD⟩
            rw [hNc1D] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h'
            · exact hwc2 h'
            · exact hwL1 h'
          · have hmem : w ∈ G.neighborFinset c₂ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hwu).symm, hwD⟩
            rw [hNc2D] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h'
            · exact hwc1 h'
            · exact hwL2 h'
        -- Degree split `deg v = |N v ∩ D| + |N v ∩ Dᶜ|`.
        have hdegsplit : ∀ v : Fin 14,
            (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
          intro v
          have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) := by
            apply Finset.disjoint_left.mpr
            intro a ha ha'
            rw [Finset.mem_inter] at ha ha'
            exact (Finset.mem_compl.mp ha'.2) ha.2
          have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
            rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
          rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
        -- `∑_{h∈Hub} |N h ∩ Hub| = 6`.
        have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
            = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count_fourteen G D Dᶜ
        have hsumD_NHub : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card = 18 := by
          have hcong : ∑ v ∈ D, ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
              = ∑ v ∈ D, 3 :=
            Finset.sum_congr rfl (fun v hv => by rw [hdegsplit v, hdegD v hv])
          rw [Finset.sum_add_distrib, hs6, Finset.sum_const, hD8card, smul_eq_mul] at hcong
          omega
        have hSumHubInt : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 6 := by
          have hcong : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card)
              = ∑ w ∈ Dᶜ, 4 :=
            Finset.sum_congr rfl (fun w hw => by rw [hdegsplit w, hDcdeg4 w hw])
          rw [Finset.sum_add_distrib, Finset.sum_const, hDccard, smul_eq_mul, ← hcross,
            hsumD_NHub] at hcong
          omega
        -- **The winning hub.**
        have hwin : ∃ g : Fin 14, g ∈ Dᶜ ∧
            ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
              (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) ∧
            2 ≤ (G.neighborFinset g ∩ Iso).card := by
          by_contra hcon
          have htwle : ∀ g : Fin 14, g ∈ Dᶜ →
              ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
              (G.neighborFinset g ∩ Iso).card ≤ 1 := by
            intro g hg hav
            by_contra hcard
            exact hcon ⟨g, hg, hav, by omega⟩
          have hsub1 : ∀ g : Fin 14, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ →
              G.neighborFinset g ∩ D ⊆ insert L₂ (G.neighborFinset g ∩ Iso) := by
            intro g hgL1 hgc1 hgc2 w hw
            rw [Finset.mem_inter, G.mem_neighborFinset] at hw
            obtain ⟨hgw, hwD⟩ := hw
            by_cases hwL2 : w = L₂
            · rw [hwL2]; exact Finset.mem_insert_self _ _
            · have hwL1 : w ≠ L₁ := fun e => hgL1 (e ▸ hgw)
              have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
              have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
              exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩)
          have hsub1' : ∀ g : Fin 14, ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
              G.neighborFinset g ∩ D ⊆ insert L₁ (G.neighborFinset g ∩ Iso) := by
            intro g hgc1 hgc2 hgL2 w hw
            rw [Finset.mem_inter, G.mem_neighborFinset] at hw
            obtain ⟨hgw, hwD⟩ := hw
            by_cases hwL1 : w = L₁
            · rw [hwL1]; exact Finset.mem_insert_self _ _
            · have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
              have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
              have hwL2 : w ≠ L₂ := fun e => hgL2 (e ▸ hgw)
              exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩)
          have hsub2 : ∀ g : Fin 14, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
              G.neighborFinset g ∩ D ⊆ G.neighborFinset g ∩ Iso := by
            intro g hgL1 hgc1 hgc2 hgL2 w hw
            rw [Finset.mem_inter, G.mem_neighborFinset] at hw
            obtain ⟨hgw, hwD⟩ := hw
            have hwL1 : w ≠ L₁ := fun e => hgL1 (e ▸ hgw)
            have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
            have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
            have hwL2 : w ≠ L₂ := fun e => hgL2 (e ▸ hgw)
            exact Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩
          have hint2 : ∀ (g a : Fin 14), g ∈ Dᶜ →
              (G.neighborFinset g ∩ D ⊆ insert a (G.neighborFinset g ∩ Iso)) →
              (G.neighborFinset g ∩ Iso).card ≤ 1 →
              2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
            intro g a hg hsub htw
            have hc := Finset.card_le_card hsub
            have hc2 := Finset.card_insert_le a (G.neighborFinset g ∩ Iso)
            have hds := hdegsplit g; rw [hDcdeg4 g hg] at hds; omega
          have hint3 : ∀ g : Fin 14, g ∈ Dᶜ →
              (G.neighborFinset g ∩ D ⊆ G.neighborFinset g ∩ Iso) →
              (G.neighborFinset g ∩ Iso).card ≤ 1 →
              3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
            intro g hg hsub htw
            have hc := le_trans (Finset.card_le_card hsub) htw
            have hds := hdegsplit g; rw [hDcdeg4 g hg] at hds; omega
          set P : Finset (Fin 14) := Dᶜ.filter
            (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hPdef
          set Q : Finset (Fin 14) := Dᶜ.filter
            (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hQdef
          set R : Finset (Fin 14) := Dᶜ.filter
            (fun g => (¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
              (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) with hRdef
          have hpt : ∀ g ∈ Dᶜ,
              (if (¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) then (1 : ℕ) else 0)
                + (if (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) then (1 : ℕ) else 0)
                + (if ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                      (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) then (1 : ℕ) else 0)
                ≤ (G.neighborFinset g ∩ Dᶜ).card := by
            intro g hg
            by_cases ha1 : (¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) <;>
              by_cases ha2 : (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)
            · rw [if_pos ha1, if_pos ha2, if_pos (Or.inl ha1)]
              obtain ⟨hgL1, hgc1, hgc2⟩ := ha1
              obtain ⟨_, _, hgL2⟩ := ha2
              have hi3 := hint3 g hg (hsub2 g hgL1 hgc1 hgc2 hgL2)
                (htwle g hg (Or.inl ⟨hgL1, hgc1, hgc2⟩))
              omega
            · rw [if_pos ha1, if_neg ha2, if_pos (Or.inl ha1)]
              obtain ⟨hgL1, hgc1, hgc2⟩ := ha1
              have hi2 := hint2 g L₂ hg (hsub1 g hgL1 hgc1 hgc2)
                (htwle g hg (Or.inl ⟨hgL1, hgc1, hgc2⟩))
              omega
            · rw [if_neg ha1, if_pos ha2, if_pos (Or.inr ha2)]
              obtain ⟨hgc1, hgc2, hgL2⟩ := ha2
              have hi2 := hint2 g L₁ hg (hsub1' g hgc1 hgc2 hgL2)
                (htwle g hg (Or.inr ⟨hgc1, hgc2, hgL2⟩))
              omega
            · rw [if_neg ha1, if_neg ha2, if_neg (not_or.mpr ⟨ha1, ha2⟩)]
              omega
          have hP6 : P.card = ∑ g ∈ Dᶜ,
              (if (¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) then (1 : ℕ) else 0) := by
            rw [hPdef, Finset.card_filter]
          have hQ6 : Q.card = ∑ g ∈ Dᶜ,
              (if (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) then (1 : ℕ) else 0) := by
            rw [hQdef, Finset.card_filter]
          have hR6 : R.card = ∑ g ∈ Dᶜ,
              (if ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                    (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) then (1 : ℕ) else 0) := by
            rw [hRdef, Finset.card_filter]
          have hPQR6 : P.card + Q.card + R.card ≤ 6 := by
            rw [hP6, hQ6, hR6, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            calc ∑ g ∈ Dᶜ, _ ≤ ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card :=
                  Finset.sum_le_sum hpt
              _ = 6 := hSumHubInt
          have hcc1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1 := by
            have := hdegsplit c₁; rw [hc1deg, hin1] at this; omega
          have hcc2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1 := by
            have := hdegsplit c₂; rw [hc2deg, hin2] at this; omega
          have hcL1 : (G.neighborFinset L₁ ∩ Dᶜ).card ≤ 2 := by
            have hp := hdegsplit L₁
            have hpos : 1 ≤ (G.neighborFinset L₁ ∩ D).card := Finset.card_pos.mpr
              ⟨c₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩⟩
            rw [hL1deg] at hp; omega
          have hcL2 : (G.neighborFinset L₂ ∩ Dᶜ).card ≤ 2 := by
            have hp := hdegsplit L₂
            have hpos : 1 ≤ (G.neighborFinset L₂ ∩ D).card := Finset.card_pos.mpr
              ⟨c₂, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩⟩
            rw [hL2deg] at hp; omega
          have hPcard : 2 ≤ P.card := by
            have hsubP : Dᶜ \ P ⊆ (G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₁ ∩ Dᶜ)
                ∪ (G.neighborFinset c₂ ∩ Dᶜ) := by
              intro g hg
              obtain ⟨hgDc, hgnP⟩ := Finset.mem_sdiff.mp hg
              rw [hPdef] at hgnP
              have hnav : ¬(¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) :=
                fun hpred => hgnP (Finset.mem_filter.mpr ⟨hgDc, hpred⟩)
              have hor : G.Adj g L₁ ∨ G.Adj g c₁ ∨ G.Adj g c₂ := by
                by_contra hc; push Not at hc; exact hnav hc
              rcases hor with h | h | h
              · exact Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
              · exact Finset.mem_union_left _ (Finset.mem_union_right _
                  (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
              · exact Finset.mem_union_right _
                  (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)
            have hubcard : (Dᶜ \ P).card ≤ 4 := by
              refine le_trans (Finset.card_le_card hsubP) ?_
              refine le_trans (Finset.card_union_le _ _) ?_
              have h1 := Finset.card_union_le (G.neighborFinset L₁ ∩ Dᶜ)
                (G.neighborFinset c₁ ∩ Dᶜ)
              omega
            have hle := Finset.card_le_card_sdiff_add_card (s := Dᶜ) (t := P)
            omega
          have hQcard : 2 ≤ Q.card := by
            have hsubQ : Dᶜ \ Q ⊆ (G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ)
                ∪ (G.neighborFinset L₂ ∩ Dᶜ) := by
              intro g hg
              obtain ⟨hgDc, hgnQ⟩ := Finset.mem_sdiff.mp hg
              rw [hQdef] at hgnQ
              have hnav : ¬(¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) :=
                fun hpred => hgnQ (Finset.mem_filter.mpr ⟨hgDc, hpred⟩)
              have hor : G.Adj g c₁ ∨ G.Adj g c₂ ∨ G.Adj g L₂ := by
                by_contra hc; push Not at hc; exact hnav hc
              rcases hor with h | h | h
              · exact Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
              · exact Finset.mem_union_left _ (Finset.mem_union_right _
                  (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
              · exact Finset.mem_union_right _
                  (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)
            have hubcard : (Dᶜ \ Q).card ≤ 4 := by
              refine le_trans (Finset.card_le_card hsubQ) ?_
              refine le_trans (Finset.card_union_le _ _) ?_
              have h1 := Finset.card_union_le (G.neighborFinset c₁ ∩ Dᶜ)
                (G.neighborFinset c₂ ∩ Dᶜ)
              omega
            have hle := Finset.card_le_card_sdiff_add_card (s := Dᶜ) (t := Q)
            omega
          have hRPQ : R = P ∪ Q := by rw [hRdef, hPdef, hQdef, Finset.filter_or]
          have hcardunion : R.card + (P ∩ Q).card = P.card + Q.card := by
            rw [hRPQ]; exact Finset.card_union_add_card_inter P Q
          have hInterLeP : (P ∩ Q).card ≤ P.card := Finset.card_le_card Finset.inter_subset_left
          have hInterLeQ : (P ∩ Q).card ≤ Q.card := Finset.card_le_card Finset.inter_subset_right
          have hPcard2 : P.card = 2 := by omega
          have hIcard2 : (P ∩ Q).card = 2 := by omega
          have hPeqI : P ∩ Q = P :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
          have hQeqI : P ∩ Q = Q :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
          have hPQ : P = Q := by rw [← hPeqI, hQeqI]
          obtain ⟨p₁, p₂, hp12, hPeq2⟩ := Finset.card_eq_two.mp hPcard2
          have hp1Pm : p₁ ∈ P := by rw [hPeq2]; simp
          have hp2Pm : p₂ ∈ P := by rw [hPeq2]; simp
          have hp1Qm : p₁ ∈ Q := hPQ ▸ hp1Pm
          have hp2Qm : p₂ ∈ Q := hPQ ▸ hp2Pm
          have hp1memP := Finset.mem_filter.mp (hPdef ▸ hp1Pm)
          have hp1Dc := hp1memP.1
          have hp1L1 := hp1memP.2.1
          have hp1c1 := hp1memP.2.2.1
          have hp1c2 := hp1memP.2.2.2
          have hp1L2 := (Finset.mem_filter.mp (hQdef ▸ hp1Qm)).2.2.2
          have hp2memP := Finset.mem_filter.mp (hPdef ▸ hp2Pm)
          have hp2Dc := hp2memP.1
          have hp2L1 := hp2memP.2.1
          have hp2c1 := hp2memP.2.2.1
          have hp2c2 := hp2memP.2.2.2
          have hp2L2 := (Finset.mem_filter.mp (hQdef ▸ hp2Qm)).2.2.2
          have hp1int3 : 3 ≤ (G.neighborFinset p₁ ∩ Dᶜ).card :=
            hint3 p₁ hp1Dc (hsub2 p₁ hp1L1 hp1c1 hp1c2 hp1L2)
              (htwle p₁ hp1Dc (Or.inl ⟨hp1L1, hp1c1, hp1c2⟩))
          have hp2int3 : 3 ≤ (G.neighborFinset p₂ ∩ Dᶜ).card :=
            hint3 p₂ hp2Dc (hsub2 p₂ hp2L1 hp2c1 hp2c2 hp2L2)
              (htwle p₂ hp2Dc (Or.inl ⟨hp2L1, hp2c1, hp2c2⟩))
          have hpairsub : ({p₁, p₂} : Finset (Fin 14)) ⊆ Dᶜ := by
            intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl; exacts [hp1Dc, hp2Dc]
          have hsd : ∑ g ∈ Dᶜ \ ({p₁, p₂} : Finset (Fin 14)), (G.neighborFinset g ∩ Dᶜ).card
              + ∑ g ∈ ({p₁, p₂} : Finset (Fin 14)), (G.neighborFinset g ∩ Dᶜ).card
              = ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card := Finset.sum_sdiff hpairsub
          have hpairsum : ∑ g ∈ ({p₁, p₂} : Finset (Fin 14)), (G.neighborFinset g ∩ Dᶜ).card
              = (G.neighborFinset p₁ ∩ Dᶜ).card + (G.neighborFinset p₂ ∩ Dᶜ).card :=
            Finset.sum_pair hp12
          rw [hpairsum, hSumHubInt] at hsd
          have hp1int_eq : (G.neighborFinset p₁ ∩ Dᶜ).card = 3 := by omega
          have hzero : ∑ g ∈ Dᶜ \ ({p₁, p₂} : Finset (Fin 14)),
              (G.neighborFinset g ∩ Dᶜ).card = 0 := by omega
          have hq0 : ∀ q ∈ Dᶜ \ ({p₁, p₂} : Finset (Fin 14)),
              (G.neighborFinset q ∩ Dᶜ).card = 0 := Finset.sum_eq_zero_iff.mp hzero
          have hsubp2 : G.neighborFinset p₁ ∩ Dᶜ ⊆ ({p₂} : Finset (Fin 14)) := by
            intro q hq
            rw [Finset.mem_inter, G.mem_neighborFinset] at hq
            obtain ⟨hp1q, hqDc⟩ := hq
            have hqp1 : q ≠ p₁ := fun e => G.irrefl (e ▸ hp1q)
            by_cases hqp2 : q = p₂
            · rw [hqp2]; exact Finset.mem_singleton_self _
            · exfalso
              have hqsdiff : q ∈ Dᶜ \ ({p₁, p₂} : Finset (Fin 14)) := by
                rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
                exact ⟨hqDc, fun h => h.elim hqp1 hqp2⟩
              have h0 := hq0 q hqsdiff
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
              exact h0 p₁ (Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset _ _).mpr hp1q.symm, hp1Dc⟩)
          have hfin : (G.neighborFinset p₁ ∩ Dᶜ).card ≤ 1 := by
            refine le_trans (Finset.card_le_card hsubp2) ?_; simp
          omega
        obtain ⟨g, hgDc, havoid, hg2⟩ := hwin
        obtain ⟨s1, hs1m, s2, hs2m, hs12⟩ :=
          Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset g ∩ Iso).card)
        rw [Finset.mem_inter, G.mem_neighborFinset] at hs1m hs2m
        obtain ⟨hgs1, hs1Iso⟩ := hs1m
        obtain ⟨hgs2, hs2Iso⟩ := hs2m
        obtain ⟨hs1deg, hs1iso⟩ := hIsoprop s1 hs1Iso
        obtain ⟨hs2deg, hs2iso⟩ := hIsoprop s2 hs2Iso
        rcases havoid with ⟨hgL1, hgc1, hgc2⟩ | ⟨hgc1, hgc2, hgL2⟩
        · exact Or.inr (Or.inl (dense_two_twin_assemble G s1 s2 g L₁ c₁ c₂ hs1deg hs2deg
            (hDcdeg4 g hgDc) hL1deg hc1deg hc2deg hgs1.symm hgs2.symm hac1L1.symm hc12
            hs1iso hs2iso hgL1 hgc1 hgc2 hs12 hac1L1.symm.ne hc12.ne hL1nc2))
        · exact Or.inr (Or.inl (dense_two_twin_assemble G s1 s2 g c₁ c₂ L₂ hs1deg hs2deg
            (hDcdeg4 g hgDc) hc1deg hc2deg hL2deg hgs1.symm hgs2.symm hc12 hac2L2
            hs1iso hs2iso hgc1 hgc2 hgL2 hs12 hc12.ne hac2L2.ne hL2nc1.symm))
  · exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_fourteen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 14, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 14)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

end N14

end ACMax
