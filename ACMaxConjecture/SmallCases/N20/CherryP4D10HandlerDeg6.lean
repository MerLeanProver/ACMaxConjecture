import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub

/-!
# `n = 20` dense-cherry `|D| = 10` (`10` hubs) deg-`6`-hub `Iso`-`4` handler

The `|Dᶜ| = 10` `P₄`-cherry residual in which the excess is concentrated on a *single* degree-`6`
hub `h₆` carrying at least four `Iso`-twins (`hh6iso4`), the other nine hubs being degree-`4`.  The
degree-`6` hub *escapes* the `TwoTwinConfig` cap (which needs centre degree `≤ 5`), so the usual
saturation ledger of `d10_clean_force_twenty` / `d10_exc_force_twenty` breaks and the world needs a
dedicated argument, split on whether `h₆` is adjacent to *all* of `Iso` (`isoinc h₆ = 6`) or not.

**Low-hog branch (`isoinc h₆ ≤ 5`).**  The two `c`-slots `x₁ :=` `c₁`'s unique hub and
`x₂ :=` `c₂`'s unique hub are the only degree-`4` hubs adjacent to a `c`-vertex; the `Iso`-ledger
`∑ isoinc = 18` with `isoinc h₆ ≤ 5` and the per-class caps (avoiders `≤ 1`, double-leaf `≤ 1`)
force `isoinc x₁ + isoinc x₂ ≥ 5`, so one `c`-slot is internally isolated with three twins and the
pair assembles a `TwoHubConfig`, contradicting `hth`.

**Full-hog branch (`Iso ⊆ N h₆`).**  Then `h₆` is internally isolated with `cinc = 0`, every
degree-`4` hub with `≥ 3` twins gives a good `K₂,₃` (`hK23`), so all are `≤ 2`; the twelve remaining
twin-slots saturate into six disjoint same-twin degree-`4` pairs, the ledger forces a double-leaf
hub of internal degree `0`, and `int-0` `TwoHubConfig`s against it exhaust its two twins — one
partner is left, firing `hth` (or a good pair firing `hT`/`hsv`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Low-hog branch (`isoinc h₆ ≤ 5`).**  The `c`-slot `Iso`-ledger forces a `TwoHubConfig`. -/
private theorem d10_deg6_iso_lowhog (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ h₆ : Fin 20)
    (_hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL1D : L₁ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hDc10 : Dᶜ.card = 10)
    (hper : ∀ h : Fin 20, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (hsumIso : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 18)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hh6Dc : h₆ ∈ Dᶜ) (_hh6d : G.degree h₆ = 6)
    (hh6iso4 : 4 ≤ (G.neighborFinset h₆ ∩ Iso).card)
    (hh6iso5 : (G.neighborFinset h₆ ∩ Iso).card ≤ 5)
    (hdegOth : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₆ → G.degree h = 4) :
    False := by
  classical
  set P : Finset (Fin 20) := {L₁, c₁, c₂, L₂} with hPdef
  -- Structural preamble.
  have hIso_nadj : ∀ t : Fin 20, t ∈ Iso → ∀ w : Fin 20, G.degree w = 3 → ¬G.Adj t w :=
    fun t ht w hw hadj => (hIsoprop t ht).2 w hadj hw
  have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
  have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
  have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
  have hL2nIso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm hc2deg
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
      G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
  have hnL1L2 : ¬G.Adj L₁ L₂ := by
    intro hadj
    have hdisj : Disjoint (G.neighborFinset L₁ ∩ D) (G.neighborFinset L₁ ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr; intro a ha hb
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
    have hunion : (G.neighborFinset L₁ ∩ D) ∪ (G.neighborFinset L₁ ∩ Dᶜ)
        = G.neighborFinset L₁ := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have hsum : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset L₁ ∩ Dᶜ).card
        = G.degree L₁ := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
    rw [hL1hub, hL1deg] at hsum
    have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩
    have hL2mem : L₂ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ L₂).mpr hadj, hL2D⟩
    have hle1 : (G.neighborFinset L₁ ∩ D).card ≤ 1 := by omega
    exact hL2nc1 ((Finset.card_le_one.mp hle1 c₁ hc1mem L₂ hL2mem).symm)
  have hubD_ne : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ L₁ ∧ h ≠ c₁ ∧ h ≠ c₂ ∧ h ≠ L₂ := by
    intro h hh
    have hhD : h ∉ D := Finset.mem_compl.mp hh
    exact ⟨fun he => hhD (he ▸ hL1D), fun he => hhD (he ▸ hc1D),
      fun he => hhD (he ▸ hc2D), fun he => hhD (he ▸ hL2D)⟩
  -- `c₁`'s / `c₂`'s unique hub.
  obtain ⟨x₁, hx1eq⟩ := Finset.card_eq_one.mp hc1hub
  obtain ⟨x₂, hx2eq⟩ := Finset.card_eq_one.mp hc2hub
  have hx1mem : x₁ ∈ G.neighborFinset c₁ ∩ Dᶜ := by rw [hx1eq]; exact Finset.mem_singleton_self _
  have hx2mem : x₂ ∈ G.neighborFinset c₂ ∩ Dᶜ := by rw [hx2eq]; exact Finset.mem_singleton_self _
  have hx1Dc : x₁ ∈ Dᶜ := (Finset.mem_inter.mp hx1mem).2
  have hx2Dc : x₂ ∈ Dᶜ := (Finset.mem_inter.mp hx2mem).2
  have hax1c1 : G.Adj x₁ c₁ := ((G.mem_neighborFinset c₁ x₁).mp (Finset.mem_inter.mp hx1mem).1).symm
  have hax2c2 : G.Adj x₂ c₂ := ((G.mem_neighborFinset c₂ x₂).mp (Finset.mem_inter.mp hx2mem).1).symm
  have hc1uniq : ∀ g : Fin 20, g ∈ Dᶜ → G.Adj g c₁ → g = x₁ := by
    intro g hg hadj
    have : g ∈ G.neighborFinset c₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ g).mpr hadj.symm, hg⟩
    rw [hx1eq, Finset.mem_singleton] at this; exact this
  have hc2uniq : ∀ g : Fin 20, g ∈ Dᶜ → G.Adj g c₂ → g = x₂ := by
    intro g hg hadj
    have : g ∈ G.neighborFinset c₂ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ g).mpr hadj.symm, hg⟩
    rw [hx2eq, Finset.mem_singleton] at this; exact this
  -- **Ledger sets.**
  set Sc : Finset (Fin 20) :=
    (Dᶜ.erase h₆).filter (fun h => G.Adj h c₁ ∨ G.Adj h c₂) with hScdef
  set restS : Finset (Fin 20) :=
    (Dᶜ.erase h₆).filter (fun h => ¬(G.Adj h c₁ ∨ G.Adj h c₂)) with hrestdef
  set Sd : Finset (Fin 20) :=
    restS.filter (fun h => G.Adj h L₁ ∧ G.Adj h L₂) with hSddef
  have hcard9 : (Dᶜ.erase h₆).card = 9 := by rw [Finset.card_erase_of_mem hh6Dc, hDc10]
  have hpartSc : Sc.card + restS.card = 9 := by
    rw [hScdef, hrestdef, ← hcard9]
    exact Finset.card_filter_add_card_filter_not (fun h => G.Adj h c₁ ∨ G.Adj h c₂)
  have hsum_erase : (∑ h ∈ Dᶜ.erase h₆, (G.neighborFinset h ∩ Iso).card)
      = 18 - (G.neighborFinset h₆ ∩ Iso).card := by
    have h := Finset.add_sum_erase Dᶜ (fun h => (G.neighborFinset h ∩ Iso).card) hh6Dc
    rw [hsumIso] at h; omega
  have hsum_split : (∑ h ∈ Sc, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ restS, (G.neighborFinset h ∩ Iso).card)
      = ∑ h ∈ Dᶜ.erase h₆, (G.neighborFinset h ∩ Iso).card := by
    rw [hScdef, hrestdef]
    exact Finset.sum_filter_add_sum_filter_not (Dᶜ.erase h₆)
      (fun h => G.Adj h c₁ ∨ G.Adj h c₂) _
  -- **Cap on `Sc`:** each `c`-slot has `isoinc ≤ 3`.
  have hSc_le : ∑ h ∈ Sc, (G.neighborFinset h ∩ Iso).card ≤ 3 * Sc.card := by
    rw [Nat.mul_comm]
    apply Finset.sum_le_card_nsmul
    intro h hh
    rw [hScdef, Finset.mem_filter] at hh
    obtain ⟨hherase, hor⟩ := hh
    have hhDc := Finset.mem_of_mem_erase hherase
    have hcinc1 : 1 ≤ (G.neighborFinset h ∩ P).card := by
      rcases hor with h1 | h2
      · exact Finset.card_pos.mpr ⟨c₁, Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset h c₁).mpr h1, by simp [hPdef]⟩⟩
      · exact Finset.card_pos.mpr ⟨c₂, Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset h c₂).mpr h2, by simp [hPdef]⟩⟩
    have hd4 := hdegOth h hhDc (Finset.ne_of_mem_erase hherase)
    have := hper h hhDc; rw [hd4] at this; omega
  have hSc_le2 : Sc.card ≤ 2 := by
    have hsub : Sc ⊆ (G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ) := by
      intro h hh
      rw [hScdef, Finset.mem_filter] at hh
      obtain ⟨hherase, hor⟩ := hh
      have hhDc := Finset.mem_of_mem_erase hherase
      rcases hor with h1 | h2
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h).mpr h1.symm, hhDc⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ h).mpr h2.symm, hhDc⟩)
    have hle := Finset.card_le_card hsub
    have hu := Finset.card_union_le (G.neighborFinset c₁ ∩ Dᶜ) (G.neighborFinset c₂ ∩ Dᶜ)
    rw [hc1hub, hc2hub] at hu; omega
  -- **Cap on `restS`:** `isoinc ≤ 1 + [double-leaf]`.
  have hrest_bound : ∀ h ∈ restS, (G.neighborFinset h ∩ Iso).card
      ≤ 1 + (if G.Adj h L₁ ∧ G.Adj h L₂ then 1 else 0) := by
    intro h hh
    rw [hrestdef, Finset.mem_filter] at hh
    obtain ⟨hherase, hnc⟩ := hh
    push Not at hnc
    obtain ⟨hnhc1, hnhc2⟩ := hnc
    have hhDc := Finset.mem_of_mem_erase hherase
    have hd4 := hdegOth h hhDc (Finset.ne_of_mem_erase hherase)
    obtain ⟨hne_L1, hne_c1, hne_c2, hne_L2⟩ := hubD_ne h hhDc
    by_cases hbL : G.Adj h L₁ ∧ G.Adj h L₂
    · rw [if_pos hbL]
      have hcinc2 : 2 ≤ (G.neighborFinset h ∩ P).card := by
        have hsub : ({L₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset h ∩ P := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h w).mpr hbL.1, by simp [hPdef]⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h w).mpr hbL.2, by simp [hPdef]⟩
        have h2 : ({L₁, L₂} : Finset (Fin 20)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
        calc 2 = ({L₁, L₂} : Finset (Fin 20)).card := h2.symm
          _ ≤ _ := Finset.card_le_card hsub
      have := hper h hhDc; rw [hd4] at this; omega
    · rw [if_neg hbL]
      have hiso1 : (G.neighborFinset h ∩ Iso).card ≤ 1 := by
        by_contra hgt; push Not at hgt
        by_cases hhL1 : G.Adj h L₁
        · have hnhL2 : ¬G.Adj h L₂ := by tauto
          exact htt (twotwin_of_centre_twenty G Iso h c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
            (by omega) hc12 hac2L2 hnhc1 hnhc2 hnhL2 hc1nIso hc2nIso hL2nIso
            hne_c1 hne_c2 hne_L2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) (Ne.symm hL2nc1)
            (by omega))
        · exact htt (twotwin_of_centre_twenty G Iso h L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
            (by omega) hac1L1.symm hc12 hhL1 hnhc1 hnhc2 hL1nIso hc1nIso hc2nIso
            hne_L1 hne_c1 hne_c2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2
            (by omega))
      omega
  have hSrest_le : ∑ h ∈ restS, (G.neighborFinset h ∩ Iso).card ≤ restS.card + Sd.card := by
    have hle := Finset.sum_le_sum hrest_bound
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one,
      ← Finset.card_filter, ← hSddef] at hle
    exact hle
  -- **Double-leaf cap `|Sd| ≤ 1`.**
  have hSd_le1 : Sd.card ≤ 1 := by
    by_contra hgt; push Not at hgt
    obtain ⟨y₁, hy1, y₂, hy2, hy12⟩ := Finset.one_lt_card.mp hgt
    rw [hSddef, Finset.mem_filter, hrestdef, Finset.mem_filter] at hy1 hy2
    obtain ⟨⟨hy1erase, _⟩, hy1L1, hy1L2⟩ := hy1
    obtain ⟨⟨hy2erase, _⟩, hy2L1, hy2L2⟩ := hy2
    have hdy1 := hdegOth y₁ (Finset.mem_of_mem_erase hy1erase) (Finset.ne_of_mem_erase hy1erase)
    have hdy2 := hdegOth y₂ (Finset.mem_of_mem_erase hy2erase) (Finset.ne_of_mem_erase hy2erase)
    by_cases hadj : G.Adj y₁ y₂
    · exact hT ⟨y₁, y₂, L₁, hy12, G.ne_of_adj hy2L1, G.ne_of_adj hy1L1,
        hadj, hy2L1, hy1L1, by omega⟩
    · have hcard4 : ({y₁, L₁, y₂, L₂} : Finset (Fin 20)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hy1L1, hy12, G.ne_of_adj hy1L2]),
          Finset.card_insert_of_notMem (by simp [Ne.symm (G.ne_of_adj hy2L1), hL1L2]),
          Finset.card_insert_of_notMem (by simp [G.ne_of_adj hy2L2]), Finset.card_singleton]
      exact hC4 ⟨y₁, L₁, y₂, L₂, hcard4, hy1L1, hy2L1.symm, hy2L2, hy1L2.symm,
        hadj, hnL1L2, by omega⟩
  -- **Combine the ledger:** `|Sc| = 2` and `∑_Sc isoinc ≥ 5`.
  have hSc2 : Sc.card = 2 := by omega
  have hSc_ge5 : 5 ≤ ∑ h ∈ Sc, (G.neighborFinset h ∩ Iso).card := by omega
  -- **`Sc = {x₁, x₂}` with `x₁ ≠ x₂`, both degree-`4`.**
  have hSc_sub : Sc ⊆ {x₁, x₂} := by
    intro h hh
    rw [hScdef, Finset.mem_filter] at hh
    obtain ⟨hherase, hor⟩ := hh
    have hhDc := Finset.mem_of_mem_erase hherase
    rcases hor with h1 | h2
    · rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl (hc1uniq h hhDc h1)
    · rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (hc2uniq h hhDc h2)
  have hx12 : x₁ ≠ x₂ := by
    intro he
    have hpaircard : ({x₁, x₂} : Finset (Fin 20)).card ≤ 1 := by
      rw [he]; simp
    have := Finset.card_le_card hSc_sub
    omega
  have hSc_eq : Sc = {x₁, x₂} := by
    apply Finset.eq_of_subset_of_card_le hSc_sub
    rw [hSc2, Finset.card_insert_of_notMem (by simp [hx12]), Finset.card_singleton]
  have hx1ne6 : x₁ ≠ h₆ := by
    have : x₁ ∈ Sc := by rw [hSc_eq]; simp
    rw [hScdef, Finset.mem_filter] at this
    exact Finset.ne_of_mem_erase this.1
  have hx2ne6 : x₂ ≠ h₆ := by
    have : x₂ ∈ Sc := by rw [hSc_eq]; simp
    rw [hScdef, Finset.mem_filter] at this
    exact Finset.ne_of_mem_erase this.1
  have hdx1 : G.degree x₁ = 4 := hdegOth x₁ hx1Dc hx1ne6
  have hdx2 : G.degree x₂ = 4 := hdegOth x₂ hx2Dc hx2ne6
  have hsum_pair : (∑ h ∈ Sc, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset x₁ ∩ Iso).card + (G.neighborFinset x₂ ∩ Iso).card := by
    rw [hSc_eq, Finset.sum_pair hx12]
  rw [hsum_pair] at hSc_ge5
  -- **Local non-adjacencies of the `c`-slots.**
  have hnx1c2 : ¬G.Adj x₁ c₂ := fun ha => hx12 (hc2uniq x₁ hx1Dc ha)
  have hnx2c1 : ¬G.Adj x₂ c₁ := fun ha => hx12.symm (hc1uniq x₂ hx2Dc ha)
  have hnx1L1 : ¬G.Adj x₁ L₁ := by
    intro ha
    exact hT ⟨x₁, c₁, L₁, G.ne_of_adj hax1c1, G.ne_of_adj hac1L1, G.ne_of_adj ha,
      hax1c1, hac1L1, ha, by omega⟩
  have hnx2L2 : ¬G.Adj x₂ L₂ := by
    intro ha
    exact hT ⟨x₂, c₂, L₂, G.ne_of_adj hax2c2, G.ne_of_adj hac2L2, G.ne_of_adj ha,
      hax2c2, hac2L2, ha, by omega⟩
  -- **Per-slot `isoinc ≤ 3` and `cinc ≥ 1`.**
  have hcinc_x1 : 1 ≤ (G.neighborFinset x₁ ∩ P).card :=
    Finset.card_pos.mpr ⟨c₁, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x₁ c₁).mpr hax1c1, by simp [hPdef]⟩⟩
  have hcinc_x2 : 1 ≤ (G.neighborFinset x₂ ∩ P).card :=
    Finset.card_pos.mpr ⟨c₂, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x₂ c₂).mpr hax2c2, by simp [hPdef]⟩⟩
  have hiso_x1_le3 : (G.neighborFinset x₁ ∩ Iso).card ≤ 3 := by
    have := hper x₁ hx1Dc; rw [hdx1] at this; omega
  have hiso_x2_le3 : (G.neighborFinset x₂ ∩ Iso).card ≤ 3 := by
    have := hper x₂ hx2Dc; rw [hdx2] at this; omega
  -- **The `TwoHubConfig` assembler for one isolated `c`-slot.**
  have finish : ∀ ki ko cv b c d : Fin 20,
      G.degree ki = 4 → G.degree ko = 4 → ¬G.Adj ki ko →
      G.Adj cv ki → G.degree cv = 3 → cv ∉ Iso → ¬G.Adj cv ko →
      b ∈ Iso → G.Adj b ki → ¬G.Adj b ko →
      c ∈ Iso → G.Adj c ko → ¬G.Adj c ki →
      d ∈ Iso → G.Adj d ko → ¬G.Adj d ki → c ≠ d → False := by
    intro ki ko cv b c d hki hko hnkiko hcvki hcvdeg hcvIso hcvko hbIso hbki hbko
      hcIso hcko hcki hdIso hdko hdki hcd
    apply hth
    have hdb : G.degree b = 3 := (hIsoprop b hbIso).1
    have hdc : G.degree c = 3 := (hIsoprop c hcIso).1
    have hdd : G.degree d = 3 := (hIsoprop d hdIso).1
    have hcvb : cv ≠ b := fun h => hcvIso (h ▸ hbIso)
    have hcvc : cv ≠ c := fun h => hcvIso (h ▸ hcIso)
    have hcvd' : cv ≠ d := fun h => hcvIso (h ▸ hdIso)
    have hbc : b ≠ c := fun h => hcki (h ▸ hbki)
    have hbd : b ≠ d := fun h => hdki (h ▸ hbki)
    have hn_cvc : ¬G.Adj cv c := fun ha => hIso_nadj c hcIso cv hcvdeg ha.symm
    have hn_cvd : ¬G.Adj cv d := fun ha => hIso_nadj d hdIso cv hcvdeg ha.symm
    have hn_bc : ¬G.Adj b c := fun ha => hIso_nadj b hbIso c hdc ha
    have hn_bd : ¬G.Adj b d := fun ha => hIso_nadj b hbIso d hdd ha
    exact two_hub_cherry_pair_twenty G ki ko cv b c d hki hko hcvdeg hdb hdc hdd
      hcvki hbki hcko hdko hnkiko (fun h => hcki h.symm) (fun h => hdki h.symm) hcvko hbko
      hn_cvc hn_cvd hn_bc hn_bd hcvb hcd hcvc hcvd' hbc hbd
  -- **Extraction of private twins for an isolated slot `ko` with iso-3 and partner `ki` iso-≥2.**
  have solve : ∀ ki ko cv : Fin 20, G.degree ki = 4 → G.degree ko = 4 → ki ≠ ko →
      G.Adj cv ki → G.degree cv = 3 → cv ∉ Iso → ¬G.Adj cv ko →
      (G.neighborFinset ko ∩ Iso).card = 3 → (G.neighborFinset ko ∩ Dᶜ) = ∅ →
      2 ≤ (G.neighborFinset ki ∩ Iso).card → ¬G.Adj ki ko → False := by
    intro ki ko cv hki hko hkine hcvki hcvdeg hcvIso hcvko hiso3 hkoiso0 hki2 hnkiko
    -- share `≤ 1`.
    have hshare : (G.neighborFinset ko ∩ G.neighborFinset ki ∩ Iso).card ≤ 1 := by
      by_contra hgt; push Not at hgt
      obtain ⟨t, ht, t', ht', htt'⟩ := Finset.one_lt_card.mp hgt
      obtain ⟨htko_ki, htIso⟩ := Finset.mem_inter.mp ht
      obtain ⟨ht'ko_ki, ht'Iso⟩ := Finset.mem_inter.mp ht'
      obtain ⟨htko, htki⟩ := Finset.mem_inter.mp htko_ki
      obtain ⟨ht'ko, ht'ki⟩ := Finset.mem_inter.mp ht'ko_ki
      have hAdj_kot : G.Adj ko t := (G.mem_neighborFinset ko t).mp htko
      have hAdj_kit : G.Adj ki t := (G.mem_neighborFinset ki t).mp htki
      have hAdj_kot' : G.Adj ko t' := (G.mem_neighborFinset ko t').mp ht'ko
      have hAdj_kit' : G.Adj ki t' := (G.mem_neighborFinset ki t').mp ht'ki
      have hdt : G.degree t = 3 := (hIsoprop t htIso).1
      have hdt' : G.degree t' = 3 := (hIsoprop t' ht'Iso).1
      have hntt' : ¬G.Adj t t' := hIso_nadj t htIso t' hdt'
      have hcard4 : ({ko, t, ki, t'} : Finset (Fin 20)).card = 4 := by
        rw [Finset.card_insert_of_notMem
            (by simp [G.ne_of_adj hAdj_kot, Ne.symm hkine, G.ne_of_adj hAdj_kot']),
          Finset.card_insert_of_notMem (by simp [Ne.symm (G.ne_of_adj hAdj_kit), htt']),
          Finset.card_insert_of_notMem (by simp [G.ne_of_adj hAdj_kit']),
          Finset.card_singleton]
      exact hC4 ⟨ko, t, ki, t', hcard4, hAdj_kot, hAdj_kit.symm, hAdj_kit', hAdj_kot'.symm,
        (fun ha => hnkiko ha.symm), hntt', by rw [hki, hko, hdt, hdt']⟩
    -- private twins of `ko` (`≥ 2`).
    have hinter_le : ((G.neighborFinset ko ∩ Iso) ∩ G.neighborFinset ki).card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) hshare
      intro w hw
      obtain ⟨hwkoI, hwki⟩ := Finset.mem_inter.mp hw
      obtain ⟨hwko, hwI⟩ := Finset.mem_inter.mp hwkoI
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hwko, hwki⟩, hwI⟩
    have hpriv_ko : 2 ≤ ((G.neighborFinset ko ∩ Iso) \ G.neighborFinset ki).card := by
      have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset ko ∩ Iso)
        (G.neighborFinset ki)
      rw [hiso3] at hsplit; omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp
      (show 1 < ((G.neighborFinset ko ∩ Iso) \ G.neighborFinset ki).card from by omega)
    obtain ⟨hckoI, hcnki⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨hdkoI, hdnki⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨hcko, hcIso⟩ := Finset.mem_inter.mp hckoI
    obtain ⟨hdko, hdIso⟩ := Finset.mem_inter.mp hdkoI
    -- private twin of `ki` (`≥ 1`).
    have hinter_le' : ((G.neighborFinset ki ∩ Iso) ∩ G.neighborFinset ko).card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) hshare
      intro w hw
      obtain ⟨hwkiI, hwko⟩ := Finset.mem_inter.mp hw
      obtain ⟨hwki, hwI⟩ := Finset.mem_inter.mp hwkiI
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hwko, hwki⟩, hwI⟩
    have hpriv_ki : 1 ≤ ((G.neighborFinset ki ∩ Iso) \ G.neighborFinset ko).card := by
      have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset ki ∩ Iso)
        (G.neighborFinset ko)
      omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp
      (show 0 < ((G.neighborFinset ki ∩ Iso) \ G.neighborFinset ko).card from by omega)
    obtain ⟨hbkiI, hbnko⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hbki, hbIso⟩ := Finset.mem_inter.mp hbkiI
    exact finish ki ko cv b c d hki hko hnkiko hcvki hcvdeg hcvIso hcvko
      hbIso ((G.mem_neighborFinset ki b).mp hbki).symm
      (fun ha => hbnko ((G.mem_neighborFinset ko b).mpr ha.symm))
      hcIso ((G.mem_neighborFinset ko c).mp hcko).symm
      (fun ha => hcnki ((G.mem_neighborFinset ki c).mpr ha.symm))
      hdIso ((G.mem_neighborFinset ko d).mp hdko).symm
      (fun ha => hdnki ((G.mem_neighborFinset ki d).mpr ha.symm)) hcd
  -- **Dispatch on which slot is iso-3.**
  have hiso_x1_int0 : (G.neighborFinset x₁ ∩ Iso).card = 3 → G.neighborFinset x₁ ∩ Dᶜ = ∅ := by
    intro h3
    have := hper x₁ hx1Dc; rw [hdx1, h3] at this
    exact Finset.card_eq_zero.mp (by omega)
  have hiso_x2_int0 : (G.neighborFinset x₂ ∩ Iso).card = 3 → G.neighborFinset x₂ ∩ Dᶜ = ∅ := by
    intro h3
    have := hper x₂ hx2Dc; rw [hdx2, h3] at this
    exact Finset.card_eq_zero.mp (by omega)
  by_cases hx1three : (G.neighborFinset x₁ ∩ Iso).card = 3
  · -- `x₁` isolated (iso-3); partner `x₂` iso-≥2.
    have hnadj : ¬G.Adj x₂ x₁ := by
      intro ha
      have hmem : x₂ ∈ G.neighborFinset x₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x₁ x₂).mpr ha.symm, hx2Dc⟩
      rw [hiso_x1_int0 hx1three] at hmem; exact absurd hmem (Finset.notMem_empty x₂)
    exact solve x₂ x₁ c₂ hdx2 hdx1 hx12.symm hax2c2.symm hc2deg hc2nIso
      (fun ha => hnx1c2 ha.symm) hx1three (hiso_x1_int0 hx1three) (by omega) hnadj
  · -- Then `x₂` iso-3, isolated; partner `x₁` iso-≥2.
    have hx2three : (G.neighborFinset x₂ ∩ Iso).card = 3 := by omega
    have hnadj : ¬G.Adj x₁ x₂ := by
      intro ha
      have hmem : x₁ ∈ G.neighborFinset x₂ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x₂ x₁).mpr ha.symm, hx1Dc⟩
      rw [hiso_x2_int0 hx2three] at hmem; exact absurd hmem (Finset.notMem_empty x₁)
    exact solve x₁ x₂ c₁ hdx1 hdx2 hx12 hax1c1.symm hc1deg hc1nIso
      (fun ha => hnx2c1 ha.symm) hx2three (hiso_x2_int0 hx2three) (by omega) hnadj

/-- **Full-hog branch (`Iso ⊆ N h₆`).**  `h₆` is internally isolated with `cinc = 0`; the `K₂,₃`
cap pins every degree-`4` hub to `Iso`-incidence `≤ 2`, the ledger ties `x₁, x₂` and a double-leaf
hub `DL` to `isoinc = 2`; a `TwoHubConfig` (`DL` against a non-sharing `c`-slot) or a good pair
(`hT`/`hsv`) closes it. -/
private theorem d10_deg6_iso_fullhog (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ h₆ : Fin 20)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL1D : L₁ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) (hsv : ¬SingleVertexConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hDc10 : Dᶜ.card = 10) (hIsocard : Iso.card = 6)
    (hper : ∀ h : Fin 20, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (hsumIso : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 18)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hh6Dc : h₆ ∈ Dᶜ) (hh6d : G.degree h₆ = 6)
    (hh6iso6 : Iso ⊆ G.neighborFinset h₆)
    (hdegOth : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₆ → G.degree h = 4) :
    False := by
  classical
  set P : Finset (Fin 20) := {L₁, c₁, c₂, L₂} with hPdef
  -- Structural preamble (shared with the low-hog branch).
  have hIso_nadj : ∀ t : Fin 20, t ∈ Iso → ∀ w : Fin 20, G.degree w = 3 → ¬G.Adj t w :=
    fun t ht w hw hadj => (hIsoprop t ht).2 w hadj hw
  have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
  have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
  have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
  have hL2nIso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm hc2deg
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
      G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
  have hnL1L2 : ¬G.Adj L₁ L₂ := by
    intro hadj
    have hdisj : Disjoint (G.neighborFinset L₁ ∩ D) (G.neighborFinset L₁ ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr; intro a ha hb
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
    have hunion : (G.neighborFinset L₁ ∩ D) ∪ (G.neighborFinset L₁ ∩ Dᶜ)
        = G.neighborFinset L₁ := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have hsum : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset L₁ ∩ Dᶜ).card
        = G.degree L₁ := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
    rw [hL1hub, hL1deg] at hsum
    have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩
    have hL2mem : L₂ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ L₂).mpr hadj, hL2D⟩
    have hle1 : (G.neighborFinset L₁ ∩ D).card ≤ 1 := by omega
    exact hL2nc1 ((Finset.card_le_one.mp hle1 c₁ hc1mem L₂ hL2mem).symm)
  have hubD_ne : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ L₁ ∧ h ≠ c₁ ∧ h ≠ c₂ ∧ h ≠ L₂ := by
    intro h hh
    have hhD : h ∉ D := Finset.mem_compl.mp hh
    exact ⟨fun he => hhD (he ▸ hL1D), fun he => hhD (he ▸ hc1D),
      fun he => hhD (he ▸ hc2D), fun he => hhD (he ▸ hL2D)⟩
  -- **`h₆` is `Iso`-saturated: `isoinc h₆ = 6`, `cinc h₆ = 0`, internally isolated.**
  have hh6iso : (G.neighborFinset h₆ ∩ Iso).card = 6 := by
    have hsub : G.neighborFinset h₆ ∩ Iso = Iso :=
      Finset.inter_eq_right.mpr hh6iso6
    rw [hsub, hIsocard]
  have hh6int0 : G.neighborFinset h₆ ∩ Dᶜ = ∅ := by
    have := hper h₆ hh6Dc; rw [hh6iso, hh6d] at this
    exact Finset.card_eq_zero.mp (by omega)
  have hh6nadj : ∀ g : Fin 20, g ∈ Dᶜ → ¬G.Adj h₆ g := by
    intro g hg ha
    have : g ∈ G.neighborFinset h₆ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₆ g).mpr ha, hg⟩
    rw [hh6int0] at this; exact absurd this (Finset.notMem_empty g)
  have hIsoNh6 : ∀ t : Fin 20, t ∈ Iso → G.Adj h₆ t :=
    fun t ht => (G.mem_neighborFinset h₆ t).mp (hh6iso6 ht)
  -- **`K₂,₃` cap: every degree-`4` hub has `Iso`-incidence `≤ 2`.**
  have hK23cap : ∀ g : Fin 20, g ∈ Dᶜ → g ≠ h₆ → (G.neighborFinset g ∩ Iso).card ≤ 2 := by
    intro g hgDc hgne6
    by_contra hgt; push Not at hgt
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
      (show 3 ≤ (G.neighborFinset g ∩ Iso).card from by omega)
    obtain ⟨t1, t2, t3, h12, h13, h23, hTeq⟩ := Finset.card_eq_three.mp hTcard
    have hmem : ∀ t : Fin 20, t ∈ ({t1, t2, t3} : Finset (Fin 20)) →
        G.Adj g t ∧ t ∈ Iso := by
      intro t ht
      have htT : t ∈ G.neighborFinset g ∩ Iso := hTsub (hTeq ▸ ht)
      exact ⟨(G.mem_neighborFinset g t).mp (Finset.mem_inter.mp htT).1,
        (Finset.mem_inter.mp htT).2⟩
    obtain ⟨hgt1, ht1I⟩ := hmem t1 (by simp)
    obtain ⟨hgt2, ht2I⟩ := hmem t2 (by simp)
    obtain ⟨hgt3, ht3I⟩ := hmem t3 (by simp)
    have hdg := hdegOth g hgDc hgne6
    have hd1 := (hIsoprop t1 ht1I).1
    have hd2 := (hIsoprop t2 ht2I).1
    have hd3 := (hIsoprop t3 ht3I).1
    have hcard5 : ({h₆, g, t1, t2, t3} : Finset (Fin 20)).card = 5 := by
      have hne6g : h₆ ≠ g := by intro he; rw [he, hdg] at hh6d; omega
      have hne6t1 : h₆ ≠ t1 := by intro he; rw [he, hd1] at hh6d; omega
      have hne6t2 : h₆ ≠ t2 := by intro he; rw [he, hd2] at hh6d; omega
      have hne6t3 : h₆ ≠ t3 := by intro he; rw [he, hd3] at hh6d; omega
      have hgt1' : g ≠ t1 := by intro he; rw [he, hd1] at hdg; omega
      have hgt2' : g ≠ t2 := by intro he; rw [he, hd2] at hdg; omega
      have hgt3' : g ≠ t3 := by intro he; rw [he, hd3] at hdg; omega
      rw [Finset.card_insert_of_notMem (by simp [hne6g, hne6t1, hne6t2, hne6t3]),
        Finset.card_insert_of_notMem (by simp [hgt1', hgt2', hgt3']),
        Finset.card_insert_of_notMem (by simp [h12, h13]),
        Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    exact hK23 ⟨h₆, g, t1, t2, t3, hcard5, hIsoNh6 t1 ht1I, hIsoNh6 t2 ht2I, hIsoNh6 t3 ht3I,
      hgt1, hgt2, hgt3, hh6nadj g hgDc, hIso_nadj t1 ht1I t2 hd2, hIso_nadj t1 ht1I t3 hd3,
      hIso_nadj t2 ht2I t3 hd3, by rw [hh6d, hdg, hd1, hd2, hd3]⟩
  -- **`h₆` avoids the cherry vertices (`cinc h₆ = 0`).**
  have hh6c0 : (G.neighborFinset h₆ ∩ P).card = 0 := by
    have := hper h₆ hh6Dc
    rw [hh6iso, hh6d, Finset.card_eq_zero.mpr hh6int0] at this; omega
  have hh6nc1 : ¬G.Adj h₆ c₁ := by
    intro ha
    have : c₁ ∈ G.neighborFinset h₆ ∩ P :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₆ c₁).mpr ha, by simp [hPdef]⟩
    rw [Finset.card_eq_zero.mp hh6c0] at this; exact absurd this (Finset.notMem_empty c₁)
  have hh6nc2 : ¬G.Adj h₆ c₂ := by
    intro ha
    have : c₂ ∈ G.neighborFinset h₆ ∩ P :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₆ c₂).mpr ha, by simp [hPdef]⟩
    rw [Finset.card_eq_zero.mp hh6c0] at this; exact absurd this (Finset.notMem_empty c₂)
  -- **`c₁`'s / `c₂`'s unique hub, both degree-`4`.**
  obtain ⟨x₁, hx1eq⟩ := Finset.card_eq_one.mp hc1hub
  obtain ⟨x₂, hx2eq⟩ := Finset.card_eq_one.mp hc2hub
  have hx1mem : x₁ ∈ G.neighborFinset c₁ ∩ Dᶜ := by rw [hx1eq]; exact Finset.mem_singleton_self _
  have hx2mem : x₂ ∈ G.neighborFinset c₂ ∩ Dᶜ := by rw [hx2eq]; exact Finset.mem_singleton_self _
  have hx1Dc : x₁ ∈ Dᶜ := (Finset.mem_inter.mp hx1mem).2
  have hx2Dc : x₂ ∈ Dᶜ := (Finset.mem_inter.mp hx2mem).2
  have hax1c1 : G.Adj x₁ c₁ := ((G.mem_neighborFinset c₁ x₁).mp (Finset.mem_inter.mp hx1mem).1).symm
  have hax2c2 : G.Adj x₂ c₂ := ((G.mem_neighborFinset c₂ x₂).mp (Finset.mem_inter.mp hx2mem).1).symm
  have hc1uniq : ∀ g : Fin 20, g ∈ Dᶜ → G.Adj g c₁ → g = x₁ := by
    intro g hg hadj
    have : g ∈ G.neighborFinset c₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ g).mpr hadj.symm, hg⟩
    rw [hx1eq, Finset.mem_singleton] at this; exact this
  have hc2uniq : ∀ g : Fin 20, g ∈ Dᶜ → G.Adj g c₂ → g = x₂ := by
    intro g hg hadj
    have : g ∈ G.neighborFinset c₂ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ g).mpr hadj.symm, hg⟩
    rw [hx2eq, Finset.mem_singleton] at this; exact this
  have hx1ne6 : x₁ ≠ h₆ := fun he => hh6nc1 (he ▸ hax1c1)
  have hx2ne6 : x₂ ≠ h₆ := fun he => hh6nc2 (he ▸ hax2c2)
  have hdx1 : G.degree x₁ = 4 := hdegOth x₁ hx1Dc hx1ne6
  have hdx2 : G.degree x₂ = 4 := hdegOth x₂ hx2Dc hx2ne6
  have hx12 : x₁ ≠ x₂ := by
    intro he
    exact hT ⟨x₁, c₁, c₂, G.ne_of_adj hax1c1, G.ne_of_adj hc12, G.ne_of_adj (he ▸ hax2c2),
      hax1c1, hc12, he ▸ hax2c2, by omega⟩
  have hnx1c2 : ¬G.Adj x₁ c₂ := fun ha => hx12 (hc2uniq x₁ hx1Dc ha)
  have hnx2c1 : ¬G.Adj x₂ c₁ := fun ha => hx12.symm (hc1uniq x₂ hx2Dc ha)
  have hnx1L1 : ¬G.Adj x₁ L₁ := by
    intro ha
    exact hT ⟨x₁, c₁, L₁, G.ne_of_adj hax1c1, G.ne_of_adj hac1L1, G.ne_of_adj ha,
      hax1c1, hac1L1, ha, by omega⟩
  have hnx2L2 : ¬G.Adj x₂ L₂ := by
    intro ha
    exact hT ⟨x₂, c₂, L₂, G.ne_of_adj hax2c2, G.ne_of_adj hac2L2, G.ne_of_adj ha,
      hax2c2, hac2L2, ha, by omega⟩
  -- **Ledger tie.**  Classes `Uc = {x₁, x₂}`, `Ud` (double-leaf, `≤ 1`), `Av` (avoiders).
  set Uc : Finset (Fin 20) :=
    (Dᶜ.erase h₆).filter (fun h => G.Adj h c₁ ∨ G.Adj h c₂) with hUcdef
  set Ud : Finset (Fin 20) :=
    (Dᶜ.erase h₆).filter (fun h => ¬(G.Adj h c₁ ∨ G.Adj h c₂) ∧ G.Adj h L₁ ∧ G.Adj h L₂)
    with hUddef
  have hcard9 : (Dᶜ.erase h₆).card = 9 := by rw [Finset.card_erase_of_mem hh6Dc, hDc10]
  have hsum_erase : (∑ h ∈ Dᶜ.erase h₆, (G.neighborFinset h ∩ Iso).card) = 12 := by
    have h := Finset.add_sum_erase Dᶜ (fun h => (G.neighborFinset h ∩ Iso).card) hh6Dc
    rw [hsumIso, hh6iso] at h; omega
  -- Per-hub cap `B h = if U-class then 2 else 1`.
  set B : Fin 20 → ℕ := fun h => if (G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂)
    then 2 else 1 with hBdef
  have hbound : ∀ h ∈ Dᶜ.erase h₆, (G.neighborFinset h ∩ Iso).card ≤ B h := by
    intro h hh
    have hhDc := Finset.mem_of_mem_erase hh
    have hne6 := Finset.ne_of_mem_erase hh
    have hd4 := hdegOth h hhDc hne6
    have hcap2 := hK23cap h hhDc hne6
    by_cases hU : (G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂)
    · simp only [hBdef, if_pos hU]; exact hcap2
    · simp only [hBdef, if_neg hU]
      push Not at hU
      obtain ⟨hnc, hnLL⟩ := hU
      obtain ⟨hnc1, hnc2⟩ := hnc
      obtain ⟨hne_L1, hne_c1, hne_c2, hne_L2⟩ := hubD_ne h hhDc
      by_contra hgt; push Not at hgt
      by_cases hhL1 : G.Adj h L₁
      · have hnhL2 : ¬G.Adj h L₂ := hnLL hhL1
        exact htt (twotwin_of_centre_twenty G Iso h c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
          (by omega) hc12 hac2L2 hnc1 hnc2 hnhL2 hc1nIso hc2nIso hL2nIso
          hne_c1 hne_c2 hne_L2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) (Ne.symm hL2nc1)
          (by omega))
      · exact htt (twotwin_of_centre_twenty G Iso h L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
          (by omega) hac1L1.symm hc12 hhL1 hnc1 hnc2 hL1nIso hc1nIso hc2nIso
          hne_L1 hne_c1 hne_c2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2
          (by omega))
  have hUc2 : Uc.card = 2 := by
    have hsub : Uc ⊆ (G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ) := by
      intro h hh
      rw [hUcdef, Finset.mem_filter] at hh
      obtain ⟨hherase, hor⟩ := hh
      have hhDc := Finset.mem_of_mem_erase hherase
      rcases hor with h1 | h2
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h).mpr h1.symm, hhDc⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ h).mpr h2.symm, hhDc⟩)
    have hle := Finset.card_le_card hsub
    have hu := Finset.card_union_le (G.neighborFinset c₁ ∩ Dᶜ) (G.neighborFinset c₂ ∩ Dᶜ)
    rw [hc1hub, hc2hub] at hu
    have hx1Uc : x₁ ∈ Uc := by
      rw [hUcdef, Finset.mem_filter]
      exact ⟨Finset.mem_erase.mpr ⟨hx1ne6, hx1Dc⟩, Or.inl hax1c1⟩
    have hx2Uc : x₂ ∈ Uc := by
      rw [hUcdef, Finset.mem_filter]
      exact ⟨Finset.mem_erase.mpr ⟨hx2ne6, hx2Dc⟩, Or.inr hax2c2⟩
    have hge : 2 ≤ Uc.card := by
      have hpair : ({x₁, x₂} : Finset (Fin 20)) ⊆ Uc := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hx1Uc
        · exact hx2Uc
      have hc := Finset.card_le_card hpair
      rw [Finset.card_insert_of_notMem (by simp [hx12]), Finset.card_singleton] at hc; omega
    omega
  have hUd1 : Ud.card ≤ 1 := by
    by_contra hgt; push Not at hgt
    obtain ⟨y₁, hy1, y₂, hy2, hy12⟩ := Finset.one_lt_card.mp hgt
    rw [hUddef, Finset.mem_filter] at hy1 hy2
    obtain ⟨hy1erase, _, hy1L1, hy1L2⟩ := hy1
    obtain ⟨hy2erase, _, hy2L1, hy2L2⟩ := hy2
    have hdy1 := hdegOth y₁ (Finset.mem_of_mem_erase hy1erase) (Finset.ne_of_mem_erase hy1erase)
    have hdy2 := hdegOth y₂ (Finset.mem_of_mem_erase hy2erase) (Finset.ne_of_mem_erase hy2erase)
    by_cases hadj : G.Adj y₁ y₂
    · exact hT ⟨y₁, y₂, L₁, hy12, G.ne_of_adj hy2L1, G.ne_of_adj hy1L1,
        hadj, hy2L1, hy1L1, by omega⟩
    · have hcard4 : ({y₁, L₁, y₂, L₂} : Finset (Fin 20)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hy1L1, hy12, G.ne_of_adj hy1L2]),
          Finset.card_insert_of_notMem (by simp [Ne.symm (G.ne_of_adj hy2L1), hL1L2]),
          Finset.card_insert_of_notMem (by simp [G.ne_of_adj hy2L2]), Finset.card_singleton]
      exact hC4 ⟨y₁, L₁, y₂, L₂, hcard4, hy1L1, hy2L1.symm, hy2L2, hy1L2.symm,
        hadj, hnL1L2, by omega⟩
  -- `∑ B = 9 + |Uc| + |Ud|`; combined with `∑ isoinc = 12` and caps, force `|Ud| = 1`, tie.
  have hdisjUcUd : Disjoint Uc Ud := by
    rw [Finset.disjoint_left]
    intro h hUc hUd
    rw [hUcdef, Finset.mem_filter] at hUc
    rw [hUddef, Finset.mem_filter] at hUd
    exact hUd.2.1 hUc.2
  have hUCeq : (Dᶜ.erase h₆).filter
      (fun h => (G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂)) = Uc ∪ Ud := by
    rw [hUcdef, hUddef]
    ext h
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hm, hC⟩
      by_cases hcc : G.Adj h c₁ ∨ G.Adj h c₂
      · exact Or.inl ⟨hm, hcc⟩
      · exact Or.inr ⟨hm, hcc, hC.resolve_left hcc⟩
    · rintro (⟨hm, hcc⟩ | ⟨hm, hcc, hLL⟩)
      · exact ⟨hm, Or.inl hcc⟩
      · exact ⟨hm, Or.inr hLL⟩
  have hsumB : (∑ h ∈ Dᶜ.erase h₆, B h) = 9 + (Uc.card + Ud.card) := by
    have hpt : ∀ h : Fin 20, B h
        = 1 + (if (G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂) then 1 else 0) := by
      intro h
      by_cases hC : (G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂)
      · simp only [hBdef, if_pos hC]
      · simp only [hBdef, if_neg hC]
    rw [Finset.sum_congr rfl (fun h _ => hpt h), Finset.sum_add_distrib, Finset.sum_const,
      hcard9, smul_eq_mul, Nat.mul_one, ← Finset.card_filter, hUCeq,
      Finset.card_union_of_disjoint hdisjUcUd]
  have hle := Finset.sum_le_sum hbound
  rw [hsum_erase, hsumB] at hle
  have hUdge1 : 1 ≤ Ud.card := by omega
  have hUd1eq : Ud.card = 1 := le_antisymm hUd1 hUdge1
  -- Deficit `0`: every `Uc`/`Ud` hub is at `isoinc = 2`, every avoider at `isoinc = 1`.
  have hdsum : ∑ h ∈ Dᶜ.erase h₆, (B h - (G.neighborFinset h ∩ Iso).card) = 0 := by
    have hsplit : ∑ h ∈ Dᶜ.erase h₆,
        ((G.neighborFinset h ∩ Iso).card + (B h - (G.neighborFinset h ∩ Iso).card))
        = ∑ h ∈ Dᶜ.erase h₆, B h :=
      Finset.sum_congr rfl (fun h hh => Nat.add_sub_cancel' (hbound h hh))
    rw [Finset.sum_add_distrib, hsum_erase, hsumB, hUc2, hUd1eq] at hsplit
    omega
  have hcap0 : ∀ h ∈ Dᶜ.erase h₆, B h - (G.neighborFinset h ∩ Iso).card = 0 :=
    fun h hh => (Finset.sum_eq_zero_iff.mp hdsum) h hh
  have hisoU : ∀ h ∈ Dᶜ.erase h₆, (G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂) →
      (G.neighborFinset h ∩ Iso).card = 2 := by
    intro h hh hU
    have hBh : B h = 2 := by simp only [hBdef, if_pos hU]
    have := hcap0 h hh; have := hbound h hh; rw [hBh] at *; omega
  have hisoAv : ∀ h ∈ Dᶜ.erase h₆, ¬((G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂)) →
      (G.neighborFinset h ∩ Iso).card = 1 := by
    intro h hh hU
    have hBh : B h = 1 := by simp only [hBdef, if_neg hU]
    have hz := hcap0 h hh; have hb := hbound h hh; rw [hBh] at hz hb; omega
  -- Extract the double-leaf hub `DL`.
  obtain ⟨DL, hDLUd⟩ := Finset.card_eq_one.mp hUd1eq
  have hDLmem : DL ∈ Ud := by rw [hDLUd]; exact Finset.mem_singleton_self _
  rw [hUddef, Finset.mem_filter] at hDLmem
  obtain ⟨hDLerase, hDLnc, hDLL1, hDLL2⟩ := hDLmem
  have hDLDc := Finset.mem_of_mem_erase hDLerase
  have hDLne6 := Finset.ne_of_mem_erase hDLerase
  have hdDL : G.degree DL = 4 := hdegOth DL hDLDc hDLne6
  have hDLiso2 : (G.neighborFinset DL ∩ Iso).card = 2 :=
    hisoU DL hDLerase (Or.inr ⟨hDLL1, hDLL2⟩)
  have hx1iso2 : (G.neighborFinset x₁ ∩ Iso).card = 2 :=
    hisoU x₁ (Finset.mem_erase.mpr ⟨hx1ne6, hx1Dc⟩) (Or.inl (Or.inl hax1c1))
  have hx2iso2 : (G.neighborFinset x₂ ∩ Iso).card = 2 :=
    hisoU x₂ (Finset.mem_erase.mpr ⟨hx2ne6, hx2Dc⟩) (Or.inl (Or.inr hax2c2))
  -- `DL` is internally isolated (`cinc DL = 2`, `isoinc DL = 2` ⟹ `intdeg DL = 0`).
  have hDLint0 : G.neighborFinset DL ∩ Dᶜ = ∅ := by
    have hcinc2 : 2 ≤ (G.neighborFinset DL ∩ P).card := by
      have hsub : ({L₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset DL ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset DL w).mpr hDLL1, by simp [hPdef]⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset DL w).mpr hDLL2, by simp [hPdef]⟩
      have h2 : ({L₁, L₂} : Finset (Fin 20)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
      calc 2 = ({L₁, L₂} : Finset (Fin 20)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have := hper DL hDLDc; rw [hdDL, hDLiso2] at this
    exact Finset.card_eq_zero.mp (by omega)
  have hnDLg : ∀ g : Fin 20, g ∈ Dᶜ → ¬G.Adj DL g := by
    intro g hg ha
    have : g ∈ G.neighborFinset DL ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset DL g).mpr ha, hg⟩
    rw [hDLint0] at this; exact absurd this (Finset.notMem_empty g)
  -- **`finish2`: two non-adjacent isoinc-`2` hubs with disjoint twins ⟹ `TwoHubConfig`.**
  have finish2 : ∀ p q : Fin 20, G.degree p = 4 → G.degree q = 4 → ¬G.Adj p q →
      (G.neighborFinset p ∩ Iso).card = 2 → (G.neighborFinset q ∩ Iso).card = 2 →
      (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso) = ∅ → False := by
    intro p q hp hq hnpq hp2 hq2 hsh0
    apply hth
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < (G.neighborFinset p ∩ Iso).card by
      omega)
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp (show 1 < (G.neighborFinset q ∩ Iso).card by
      omega)
    obtain ⟨haN, haI⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbN, hbI⟩ := Finset.mem_inter.mp hb
    obtain ⟨hcN, hcI⟩ := Finset.mem_inter.mp hc
    obtain ⟨hdN, hdI⟩ := Finset.mem_inter.mp hd
    have hpriv : ∀ w : Fin 20, w ∈ G.neighborFinset p → w ∈ Iso → w ∉ G.neighborFinset q := by
      intro w hwp hwI hwq
      have : w ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso :=
        Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hwp, hwq⟩, hwI⟩
      rw [hsh0] at this; exact absurd this (Finset.notMem_empty w)
    have hpriv' : ∀ w : Fin 20, w ∈ G.neighborFinset q → w ∈ Iso → w ∉ G.neighborFinset p := by
      intro w hwq hwI hwp
      have : w ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso :=
        Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hwp, hwq⟩, hwI⟩
      rw [hsh0] at this; exact absurd this (Finset.notMem_empty w)
    have hda : G.degree a = 3 := (hIsoprop a haI).1
    have hdb : G.degree b = 3 := (hIsoprop b hbI).1
    have hdc : G.degree c = 3 := (hIsoprop c hcI).1
    have hdd : G.degree d = 3 := (hIsoprop d hdI).1
    have hac : a ≠ c := fun he => hpriv a haN haI (he ▸ hcN)
    have had : a ≠ d := fun he => hpriv a haN haI (he ▸ hdN)
    have hbc : b ≠ c := fun he => hpriv b hbN hbI (he ▸ hcN)
    have hbd : b ≠ d := fun he => hpriv b hbN hbI (he ▸ hdN)
    exact two_hub_cherry_pair_twenty G p q a b c d hp hq hda hdb hdc hdd
      ((G.mem_neighborFinset p a).mp haN).symm ((G.mem_neighborFinset p b).mp hbN).symm
      ((G.mem_neighborFinset q c).mp hcN).symm ((G.mem_neighborFinset q d).mp hdN).symm hnpq
      (fun ha' => hpriv' c hcN hcI ((G.mem_neighborFinset p c).mpr ha'))
      (fun ha' => hpriv' d hdN hdI ((G.mem_neighborFinset p d).mpr ha'))
      (fun ha' => hpriv a haN haI ((G.mem_neighborFinset q a).mpr ha'.symm))
      (fun ha' => hpriv b hbN hbI ((G.mem_neighborFinset q b).mpr ha'.symm))
      (fun ha' => hIso_nadj a haI c hdc ha') (fun ha' => hIso_nadj a haI d hdd ha')
      (fun ha' => hIso_nadj b hbI c hdc ha') (fun ha' => hIso_nadj b hbI d hdd ha')
      hab hcd hac had hbc hbd
  -- **Endgame.**
  have hnL1c2 : ¬G.Adj L₁ c₂ := by
    intro hadj
    have hmem : L₁ ∈ G.neighborFinset c₂ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ L₁).mpr hadj.symm, hL1D⟩
    rw [hNc2D] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (G.ne_of_adj hac1L1) h.symm
    · exact hL1L2 h
  have hd4ne3 : ∀ u w : Fin 20, G.degree u = 4 → G.degree w = 3 → u ≠ w :=
    fun u w hu hw he => by rw [he, hw] at hu; omega
  set Av : Finset (Fin 20) := (Dᶜ.erase h₆).filter
    (fun h => ¬((G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂))) with hAvdef
  have hAvsub : Av ⊆ Dᶜ.erase h₆ := by rw [hAvdef]; exact Finset.filter_subset _ _
  have hAvprop : ∀ a : Fin 20, a ∈ Av → a ∈ Dᶜ ∧ G.degree a = 4 ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂ := by
    intro a ha
    rw [hAvdef, Finset.mem_filter] at ha
    push Not at ha
    obtain ⟨herase, hnc, _⟩ := ha
    obtain ⟨hnc1, hnc2⟩ := hnc
    exact ⟨Finset.mem_of_mem_erase herase, hdegOth a (Finset.mem_of_mem_erase herase)
      (Finset.ne_of_mem_erase herase), hnc1, hnc2⟩
  have hAviso1 : ∀ a : Fin 20, a ∈ Av → (G.neighborFinset a ∩ Iso).card = 1 := by
    intro a ha
    rw [hAvdef, Finset.mem_filter] at ha
    exact hisoAv a ha.1 ha.2
  have hAvcard : Av.card = 6 := by
    have hpart : ((Dᶜ.erase h₆).filter (fun h => (G.Adj h c₁ ∨ G.Adj h c₂) ∨
        (G.Adj h L₁ ∧ G.Adj h L₂))).card + Av.card = 9 := by
      rw [hAvdef, ← hcard9]
      exact Finset.card_filter_add_card_filter_not
        (fun h => (G.Adj h c₁ ∨ G.Adj h c₂) ∨ (G.Adj h L₁ ∧ G.Adj h L₂))
    rw [hUCeq, Finset.card_union_of_disjoint hdisjUcUd, hUc2, hUd1eq] at hpart; omega
  -- Each `Iso` twin has exactly two degree-`4` carriers.
  have hNtsubD : ∀ t : Fin 20, t ∈ Iso → G.neighborFinset t ⊆ Dᶜ := by
    intro t htI w hw
    rw [Finset.mem_compl]; intro hwD
    exact (hIsoprop t htI).2 w ((G.mem_neighborFinset t w).mp hw) ((hmemD w).mp hwD)
  have htcarrier : ∀ t : Fin 20, t ∈ Iso → (G.neighborFinset t ∩ (Dᶜ.erase h₆)).card = 2 := by
    intro t htI
    have hh6mem : h₆ ∈ G.neighborFinset t := (G.mem_neighborFinset t h₆).mpr (hIsoNh6 t htI).symm
    have heq : G.neighborFinset t ∩ (Dᶜ.erase h₆) = (G.neighborFinset t).erase h₆ := by
      ext w; simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨hw, hwne, _⟩; exact ⟨hwne, hw⟩
      · rintro ⟨hwne, hw⟩; exact ⟨hw, hwne, hNtsubD t htI hw⟩
    rw [heq, Finset.card_erase_of_mem hh6mem, G.card_neighborFinset_eq_degree, (hIsoprop t htI).1]
  have hAvcarr_le : ∀ t : Fin 20, t ∈ Iso → (G.neighborFinset t ∩ Av).card ≤ 2 := by
    intro t htI
    calc (G.neighborFinset t ∩ Av).card
        ≤ (G.neighborFinset t ∩ (Dᶜ.erase h₆)).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hAvsub)
      _ = 2 := htcarrier t htI
  -- Bipartite double count: `∑_{t∈Iso} |N t ∩ Av| = |Av| = 6`.
  have hdouble : (∑ t ∈ Iso, (G.neighborFinset t ∩ Av).card) = 6 := by
    have h1 : ∀ t : Fin 20, (G.neighborFinset t ∩ Av).card
        = ∑ a ∈ Av, (if G.Adj t a then 1 else 0) := by
      intro t
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
      exact Finset.sum_congr rfl (fun a _ => by simp only [G.mem_neighborFinset])
    have h2 : ∀ a : Fin 20, (G.neighborFinset a ∩ Iso).card
        = ∑ t ∈ Iso, (if G.Adj t a then 1 else 0) := by
      intro a
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
      exact Finset.sum_congr rfl (fun t _ => by
        simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
    calc (∑ t ∈ Iso, (G.neighborFinset t ∩ Av).card)
        = ∑ t ∈ Iso, ∑ a ∈ Av, (if G.Adj t a then 1 else 0) := by simp_rw [h1]
      _ = ∑ a ∈ Av, ∑ t ∈ Iso, (if G.Adj t a then 1 else 0) := Finset.sum_comm
      _ = ∑ a ∈ Av, (G.neighborFinset a ∩ Iso).card := by simp_rw [h2]
      _ = 6 := by rw [Finset.sum_congr rfl hAviso1, Finset.sum_const, hAvcard]; rfl
  -- `≤ 1` avoider is adjacent to `L₁`.
  have hL1av : ∀ a₁ a₂ : Fin 20, a₁ ∈ Av → a₂ ∈ Av → G.Adj a₁ L₁ → G.Adj a₂ L₁ → a₁ = a₂ := by
    intro a₁ a₂ h1 h2 hadj1 hadj2
    by_contra hne
    have hDLne1 : DL ≠ a₁ := by
      intro he; rw [hAvdef, Finset.mem_filter] at h1
      exact h1.2 (Or.inr ⟨he ▸ hDLL1, he ▸ hDLL2⟩)
    have hDLne2 : DL ≠ a₂ := by
      intro he; rw [hAvdef, Finset.mem_filter] at h2
      exact h2.2 (Or.inr ⟨he ▸ hDLL1, he ▸ hDLL2⟩)
    have hsub : ({DL, a₁, a₂} : Finset (Fin 20)) ⊆ G.neighborFinset L₁ ∩ Dᶜ := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw
      · rw [hw]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ DL).mpr hDLL1.symm, hDLDc⟩
      · rw [hw]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ a₁).mpr hadj1.symm,
          (hAvprop a₁ h1).1⟩
      · rw [hw]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ a₂).mpr hadj2.symm,
          (hAvprop a₂ h2).1⟩
    have hc3 : ({DL, a₁, a₂} : Finset (Fin 20)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hDLne1, hDLne2]),
        Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have := Finset.card_le_card hsub; rw [hc3, hL1hub] at this; omega
  have htwin_uniq : ∀ a s s' : Fin 20, a ∈ Av → s ∈ Iso → s' ∈ Iso →
      G.Adj a s → G.Adj a s' → s = s' := by
    intro a s s' ha hs hs' has has'
    by_contra hne
    have hsub : ({s, s'} : Finset (Fin 20)) ⊆ G.neighborFinset a ∩ Iso := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a w).mpr has, hs⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a w).mpr has', hs'⟩
    have hc2 : ({s, s'} : Finset (Fin 20)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have := Finset.card_le_card hsub; rw [hc2, hAviso1 a ha] at this; omega
  -- **Good-pair kill (`K-a`): two avoiders sharing a twin, both avoiding cherry-`1`.**
  have kill_pair : ∀ a b t : Fin 20, a ∈ Av → b ∈ Av → a ≠ b → t ∈ Iso →
      G.Adj a t → G.Adj b t → ¬G.Adj a L₁ → ¬G.Adj b L₁ → False := by
    intro a b t ha hb hab htI hat hbt haL1 hbL1
    obtain ⟨haDc, hda, hac1, hac2⟩ := hAvprop a ha
    obtain ⟨hbDc, hdb, hbc1, hbc2⟩ := hAvprop b hb
    have hdt : G.degree t = 3 := (hIsoprop t htI).1
    by_cases hadj : G.Adj a b
    · exact hT ⟨a, b, t, hab, G.ne_of_adj hbt, G.ne_of_adj hat, hadj, hbt, hat, by omega⟩
    · apply hsv
      have hsum0 : (∑ p ∈ ({t, a, b} : Finset (Fin 20)),
          (G.neighborFinset p ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        obtain ⟨hwN, hwm⟩ := Finset.mem_inter.mp hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
        have hadjw := (G.mem_neighborFinset p w).mp hwN
        rcases hp with rfl | rfl | rfl <;> rcases hwm with rfl | rfl | rfl
        · exact hIso_nadj p htI w hL1deg hadjw
        · exact hIso_nadj p htI w hc1deg hadjw
        · exact hIso_nadj p htI w hc2deg hadjw
        · exact haL1 hadjw
        · exact hac1 hadjw
        · exact hac2 hadjw
        · exact hbL1 hadjw
        · exact hbc1 hadjw
        · exact hbc2 hadjw
      refine ⟨t, a, b, L₁, c₁, c₂, hdt, hL1deg, hc1deg, hc2deg, hat.symm, hbt.symm,
        hac1L1.symm, hc12, hnL1c2, ?_, hab,
        (fun he => hL1nIso (he ▸ htI)), (fun he => hc1nIso (he ▸ htI)),
        (fun he => hc2nIso (he ▸ htI)), hd4ne3 a L₁ hda hL1deg, hd4ne3 a c₁ hda hc1deg,
        hd4ne3 a c₂ hda hc2deg, hd4ne3 b L₁ hdb hL1deg, hd4ne3 b c₁ hdb hc1deg,
        hd4ne3 b c₂ hdb hc2deg, (G.ne_of_adj hac1L1).symm, G.ne_of_adj hc12, hL1nc2⟩
      rw [hsum0, if_neg hadj]; omega
  -- Dispatch: a vanishing `DL`-share gives `finish2`; else the good-pair fallback.
  by_cases hs1 : (G.neighborFinset DL ∩ G.neighborFinset x₁ ∩ Iso) = ∅
  · exact finish2 DL x₁ hdDL hdx1 (hnDLg x₁ hx1Dc) hDLiso2 hx1iso2 hs1
  · by_cases hs2 : (G.neighborFinset DL ∩ G.neighborFinset x₂ ∩ Iso) = ∅
    · exact finish2 DL x₂ hdDL hdx2 (hnDLg x₂ hx2Dc) hDLiso2 hx2iso2 hs2
    · -- Both shares nonempty: `DL`'s two twins are `U`-shared; two avoider pairs remain.
      obtain ⟨p₁, hp1⟩ := Finset.nonempty_iff_ne_empty.mpr hs1
      obtain ⟨p₂, hp2⟩ := Finset.nonempty_iff_ne_empty.mpr hs2
      obtain ⟨hp1DLx1, hp1I⟩ := Finset.mem_inter.mp hp1
      obtain ⟨hp1DL, hp1x1⟩ := Finset.mem_inter.mp hp1DLx1
      obtain ⟨hp2DLx2, hp2I⟩ := Finset.mem_inter.mp hp2
      obtain ⟨hp2DL, hp2x2⟩ := Finset.mem_inter.mp hp2DLx2
      have hAp1DL : G.Adj DL p₁ := (G.mem_neighborFinset DL p₁).mp hp1DL
      have hAp1x1 : G.Adj x₁ p₁ := (G.mem_neighborFinset x₁ p₁).mp hp1x1
      have hAp2DL : G.Adj DL p₂ := (G.mem_neighborFinset DL p₂).mp hp2DL
      have hAp2x2 : G.Adj x₂ p₂ := (G.mem_neighborFinset x₂ p₂).mp hp2x2
      have hDLAv : DL ∉ Av := by
        intro h; rw [hAvdef, Finset.mem_filter] at h; exact h.2 (Or.inr ⟨hDLL1, hDLL2⟩)
      have hx1Av : x₁ ∉ Av := by
        intro h; rw [hAvdef, Finset.mem_filter] at h; exact h.2 (Or.inl (Or.inl hax1c1))
      have hx2Av : x₂ ∉ Av := by
        intro h; rw [hAvdef, Finset.mem_filter] at h; exact h.2 (Or.inl (Or.inr hax2c2))
      have hDLnx1 : DL ≠ x₁ := fun hde => hDLnc (Or.inl (hde ▸ hax1c1))
      have hDLnx2 : DL ≠ x₂ := fun hde => hDLnc (Or.inr (hde ▸ hax2c2))
      have hh6nDL : h₆ ≠ DL := fun he => hDLne6 he.symm
      have hh6nx1 : h₆ ≠ x₁ := fun he => hx1ne6 he.symm
      have hh6nx2 : h₆ ≠ x₂ := fun he => hx2ne6 he.symm
      have hp12 : p₁ ≠ p₂ := by
        intro he
        have hsub : ({h₆, DL, x₁, x₂} : Finset (Fin 20)) ⊆ G.neighborFinset p₁ := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact (G.mem_neighborFinset p₁ w).mpr (hIsoNh6 p₁ hp1I).symm
          · exact (G.mem_neighborFinset p₁ w).mpr hAp1DL.symm
          · exact (G.mem_neighborFinset p₁ w).mpr hAp1x1.symm
          · exact (G.mem_neighborFinset p₁ w).mpr (he ▸ hAp2x2).symm
        have hc4 : ({h₆, DL, x₁, x₂} : Finset (Fin 20)).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp [hh6nDL, hh6nx1, hh6nx2]),
            Finset.card_insert_of_notMem (by simp [hDLnx1, hDLnx2]),
            Finset.card_insert_of_notMem (by simp [hx12]), Finset.card_singleton]
        have := Finset.card_le_card hsub
        rw [hc4, G.card_neighborFinset_eq_degree, (hIsoprop p₁ hp1I).1] at this; omega
      -- `p₁, p₂` carry no avoider (their carriers are `DL` and a `c`-slot).
      have hNpAv0 : ∀ p k : Fin 20, p ∈ Iso → G.Adj DL p → G.Adj k p →
          h₆ ≠ k → DL ≠ k → k ∉ Av → G.neighborFinset p ∩ Av = ∅ := by
        intro p k hpI hDLp hkp hh6k hDLk hkAv
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        obtain ⟨haN, haAv⟩ := Finset.mem_inter.mp ha
        have hane6 : a ≠ h₆ := Finset.ne_of_mem_erase (hAvsub haAv)
        have hsub : ({h₆, DL, k} : Finset (Fin 20)) ⊆ G.neighborFinset p := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact (G.mem_neighborFinset p w).mpr (hIsoNh6 p hpI).symm
          · exact (G.mem_neighborFinset p w).mpr hDLp.symm
          · exact (G.mem_neighborFinset p w).mpr hkp.symm
        have hc3 : ({h₆, DL, k} : Finset (Fin 20)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hh6nDL, hh6k]),
            Finset.card_insert_of_notMem (by simp [hDLk]), Finset.card_singleton]
        have hpeq : G.neighborFinset p = {h₆, DL, k} :=
          (Finset.eq_of_subset_of_card_le hsub
            (by rw [hc3, G.card_neighborFinset_eq_degree, (hIsoprop p hpI).1])).symm
        rw [hpeq] at haN
        simp only [Finset.mem_insert, Finset.mem_singleton] at haN
        rcases haN with rfl | rfl | rfl
        · exact hane6 rfl
        · exact hDLAv haAv
        · exact hkAv haAv
      have hNp1Av0 : G.neighborFinset p₁ ∩ Av = ∅ :=
        hNpAv0 p₁ x₁ hp1I hAp1DL hAp1x1 hh6nx1 hDLnx1 hx1Av
      have hNp2Av0 : G.neighborFinset p₂ ∩ Av = ∅ :=
        hNpAv0 p₂ x₂ hp2I hAp2DL hAp2x2 hh6nx2 hDLnx2 hx2Av
      -- The other four twins carry all six avoider slots: `≥ 2` have two carriers.
      have hp12sub : ({p₁, p₂} : Finset (Fin 20)) ⊆ Iso := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hp1I
        · exact hp2I
      have hsumsplit : (∑ t ∈ Iso \ {p₁, p₂}, (G.neighborFinset t ∩ Av).card)
          + (∑ t ∈ ({p₁, p₂} : Finset (Fin 20)), (G.neighborFinset t ∩ Av).card) = 6 := by
        rw [Finset.sum_sdiff hp12sub]; exact hdouble
      have hp12sum0 : (∑ t ∈ ({p₁, p₂} : Finset (Fin 20)), (G.neighborFinset t ∩ Av).card) = 0 := by
        rw [Finset.sum_pair hp12, Finset.card_eq_zero.mpr hNp1Av0,
          Finset.card_eq_zero.mpr hNp2Av0]
      have hsumR : (∑ t ∈ Iso \ {p₁, p₂}, (G.neighborFinset t ∩ Av).card) = 6 := by omega
      have hRcard : (Iso \ {p₁, p₂}).card = 4 := by
        have hh := Finset.card_sdiff_add_card_eq_card hp12sub
        rw [hIsocard, Finset.card_insert_of_notMem (by simp [hp12]), Finset.card_singleton] at hh
        omega
      set BigT : Finset (Fin 20) :=
        (Iso \ {p₁, p₂}).filter (fun t => 2 ≤ (G.neighborFinset t ∩ Av).card) with hBigTdef
      have hBig2 : 2 ≤ BigT.card := by
        have hb : ∀ t ∈ Iso \ {p₁, p₂}, (G.neighborFinset t ∩ Av).card
            ≤ 1 + (if 2 ≤ (G.neighborFinset t ∩ Av).card then 1 else 0) := by
          intro t ht
          have hle2 := hAvcarr_le t (Finset.mem_sdiff.mp ht).1
          by_cases h2 : 2 ≤ (G.neighborFinset t ∩ Av).card
          · rw [if_pos h2]; omega
          · rw [if_neg h2]; omega
        have hle := Finset.sum_le_sum hb
        rw [hsumR, Finset.sum_add_distrib, Finset.sum_const, hRcard, smul_eq_mul, Nat.mul_one,
          ← Finset.card_filter, ← hBigTdef] at hle
        omega
      obtain ⟨r, hr, r', hr', hrr'⟩ := Finset.one_lt_card.mp (by omega : 1 < BigT.card)
      rw [hBigTdef, Finset.mem_filter] at hr hr'
      obtain ⟨hrIso', hrbig⟩ := hr
      obtain ⟨hr'Iso', hr'big⟩ := hr'
      have hrI : r ∈ Iso := (Finset.mem_sdiff.mp hrIso').1
      have hr'I : r' ∈ Iso := (Finset.mem_sdiff.mp hr'Iso').1
      obtain ⟨a, ha, b, hb, hab⟩ :=
        Finset.one_lt_card.mp (show 1 < (G.neighborFinset r ∩ Av).card from by omega)
      obtain ⟨a', ha', b', hb', ha'b'⟩ :=
        Finset.one_lt_card.mp (show 1 < (G.neighborFinset r' ∩ Av).card from by omega)
      obtain ⟨haN, haAv⟩ := Finset.mem_inter.mp ha
      obtain ⟨hbN, hbAv⟩ := Finset.mem_inter.mp hb
      obtain ⟨ha'N, ha'Av⟩ := Finset.mem_inter.mp ha'
      obtain ⟨hb'N, hb'Av⟩ := Finset.mem_inter.mp hb'
      have hAar : G.Adj a r := ((G.mem_neighborFinset r a).mp haN).symm
      have hAbr : G.Adj b r := ((G.mem_neighborFinset r b).mp hbN).symm
      have hAa'r' : G.Adj a' r' := ((G.mem_neighborFinset r' a').mp ha'N).symm
      have hAb'r' : G.Adj b' r' := ((G.mem_neighborFinset r' b').mp hb'N).symm
      by_cases hrL1 : G.Adj a L₁ ∨ G.Adj b L₁
      · have ha'nL1 : ¬G.Adj a' L₁ := by
          intro hcon
          rcases hrL1 with hz | hz
          · exact hrr' (htwin_uniq a' r r' ha'Av hrI hr'I
              (hL1av a a' haAv ha'Av hz hcon ▸ hAar) hAa'r')
          · exact hrr' (htwin_uniq a' r r' ha'Av hrI hr'I
              (hL1av b a' hbAv ha'Av hz hcon ▸ hAbr) hAa'r')
        have hb'nL1 : ¬G.Adj b' L₁ := by
          intro hcon
          rcases hrL1 with hz | hz
          · exact hrr' (htwin_uniq b' r r' hb'Av hrI hr'I
              (hL1av a b' haAv hb'Av hz hcon ▸ hAar) hAb'r')
          · exact hrr' (htwin_uniq b' r r' hb'Av hrI hr'I
              (hL1av b b' hbAv hb'Av hz hcon ▸ hAbr) hAb'r')
        exact kill_pair a' b' r' ha'Av hb'Av ha'b' hr'I hAa'r' hAb'r' ha'nL1 hb'nL1
      · push Not at hrL1
        exact kill_pair a b r haAv hbAv hab hrI hAar hAbr hrL1.1 hrL1.2

/-- **`|D| = 10` (`10` hubs) deg-`6`-hub `Iso`-`4` handler.**  The `n = 20` `P₄`-cherry residual with
a single degree-`6` hub `h₆` carrying `≥ 4` `Iso`-twins and nine degree-`4` hubs is empty:  dispatch
on whether `h₆` is adjacent to *all* of `Iso` (`isoinc h₆ = 6`, the full-hog branch) or not (the
low-hog branch). -/
theorem d10_deg6_isofour_handler_twenty (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ h₆ : Fin 20)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (_hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (_hclassP : ∀ x : Fin 20, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) (hsv : ¬SingleVertexConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hDc10 : Dᶜ.card = 10) (hIsocard : Iso.card = 6)
    (hper : ∀ h : Fin 20, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (_hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card = 6)
    (hsumIso : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 18)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hh6Dc : h₆ ∈ Dᶜ) (hh6d : G.degree h₆ = 6)
    (hh6iso4 : 4 ≤ (G.neighborFinset h₆ ∩ Iso).card)
    (hdegOth : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₆ → G.degree h = 4) :
    False := by
  by_cases h6 : (G.neighborFinset h₆ ∩ Iso).card = 6
  · have hInterEq : G.neighborFinset h₆ ∩ Iso = Iso :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hIsocard]; omega)
    have hsub : Iso ⊆ G.neighborFinset h₆ := by rw [← hInterEq]; exact Finset.inter_subset_left
    exact d10_deg6_iso_fullhog G D Iso L₁ c₁ c₂ L₂ h₆ hmemD hIsoprop hL1deg hc1deg hc2deg hL2deg
      hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hc1D hc2D hL1D hL2D htt hth hsv hT hC4 hK23
      hDc10 hIsocard hper hsumIso hc1hub hc2hub hL1hub hL2hub hh6Dc hh6d hsub hdegOth
  · have h5 : (G.neighborFinset h₆ ∩ Iso).card ≤ 5 := by
      have hle : (G.neighborFinset h₆ ∩ Iso).card ≤ Iso.card :=
        Finset.card_le_card Finset.inter_subset_right
      rw [hIsocard] at hle; omega
    exact d10_deg6_iso_lowhog G D Iso L₁ c₁ c₂ L₂ h₆ hmemD hIsoprop hL1deg hc1deg hc2deg hL2deg
      hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hc1D hc2D hL1D hL2D htt hth hT hC4
      hDc10 hper hsumIso hc1hub hc2hub hL1hub hL2hub hh6Dc hh6d hh6iso4 h5 hdegOth

end N20

end ACMax
