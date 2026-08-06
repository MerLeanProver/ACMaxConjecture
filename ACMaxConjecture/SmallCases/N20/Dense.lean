import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates

/-!
# Dense `TwoTwin`-existence core for the `n = 18` twin certificate

Ported from the proved `n = 14` development (`TwinCert14Align6Dense`, `TwinCert14Align8`,
`TwinCert14C5`).  These are the reusable core lemmas that the `n = 18` alignment dichotomies
(`exists_align_four/six_config_twenty`, `halign8_twenty`) all call: the verified `n = 18`
dichotomy is `TwoTwin`-dominant — a degree-`4` hub with `≥ 2` `M`-isolated twins plus a cherry it
avoids package into a `TwoTwinConfig`.

Contents (all axiom-clean):

* `thin_eM_formula_twenty` — the dominating-edge `e(M)` formula `∑ + 2 = 2·inM(c₁) + 2·inM(c₂)`
  (structural, `n`-independent up to the ambient `cross_count_twenty`);
* `distinct_five_twenty` / `hub_cycle_cases_twenty` — the induced-`C₅` geometry helpers;
* `shared_deg4_hub_from_count_twenty` — pigeonhole producing a shared degree-`4` hub;
* `claw_shared_two_twin_twenty` — fat claw centre + shared hub ⇒ `TwoTwinConfig`.

The geometric/cherry-avoidance arguments port verbatim; only the cardinality bookkeeping changes
(`Fin 20`, the `cross_count_twenty` / `card_four_twenty` / `hub_meets_path_le_one_twenty` /
`dense_two_twin_assemble` ports).  The `TwoTwinConfig`-producing lemmas are kept GENERAL over
the `M`-shape data (centre / leaves / cherry as explicit arguments) so the align dichotomies can
each supply their own structure.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **`e(M)` formula in a dominating-edge case (`n = 18`).**  When every `M`-edge meets the edge
`{c₁, c₂}`, `∑_{v∈D}|N v ∩ D| = 2·inM(c₁) + 2·inM(c₂) − 2` (the shared edge `c₁c₂` is
double-counted), written additively to avoid `ℕ` subtraction.  Structural port of
`thin_eM_formula_fourteen`; the underlying handshake `e(M) = 22 − 3·|Hub| + e_H` is `n`-sensitive
but enters only through the calling dichotomy, not this identity. -/
theorem thin_eM_formula_twenty (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (c₁ c₂ : Fin 20) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    ∑ v ∈ D, (G.neighborFinset v ∩ D).card + 2
      = 2 * (G.neighborFinset c₁ ∩ D).card + 2 * (G.neighborFinset c₂ ∩ D).card := by
  classical
  have hc2mem : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have hsub : ({c₁, c₂} : Finset (Fin 20)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl; exacts [hc1D, hc2D]
  have hsplit :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
        + ∑ v ∈ ({c₁, c₂} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_sdiff hsub
  have hpair : ∑ v ∈ ({c₁, c₂} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
      = (G.neighborFinset c₁ ∩ D).card + (G.neighborFinset c₂ ∩ D).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hScong :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
        = ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 20)),
          (G.neighborFinset v ∩ ({c₁, c₂} : Finset (Fin 20))).card := by
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
    cross_count_twenty G (D \ ({c₁, c₂} : Finset (Fin 20)))
      ({c₁, c₂} : Finset (Fin 20))] at hsplit
  have hpair2 : ∑ w ∈ ({c₁, c₂} : Finset (Fin 20)),
        (G.neighborFinset w ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card
      = (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card
        + (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have he1 : (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card
      = (G.neighborFinset c₁ ∩ D).card - 1 := by
    have hset : G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))
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
  have he2 : (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card
      = (G.neighborFinset c₂ ∩ D).card - 1 := by
    have hset : G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))
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

/-- **Distinctness from a five-element literal (`n = 18`).**  A `Finset` literal `{a, b, c, d, e}`
of cardinality `5` over `Fin 20` has its five entries pairwise distinct.  Port of
`distinct_five_fourteen`. -/
theorem distinct_five_twenty (a b c d e : Fin 20)
    (h : ({a, b, c, d, e} : Finset (Fin 20)).card = 5) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  classical
  have b3 : ∀ x y z : Fin 20, ({x, y, z} : Finset (Fin 20)).card ≤ 3 := by
    intro x y z
    have h1 := Finset.card_insert_le x ({y, z} : Finset (Fin 20))
    have h2 := Finset.card_insert_le y ({z} : Finset (Fin 20))
    simp only [Finset.card_singleton] at *
    omega
  have b4 : ∀ w x y z : Fin 20, ({w, x, y, z} : Finset (Fin 20)).card ≤ 4 := by
    intro w x y z
    have h1 := Finset.card_insert_le w ({x, y, z} : Finset (Fin 20))
    have h2 := b3 x y z
    omega
  have ha : a ∉ ({b, c, d, e} : Finset (Fin 20)) := by
    intro hmem
    have : ({a, b, c, d, e} : Finset (Fin 20)).card ≤ 4 := by
      rw [Finset.insert_eq_self.mpr hmem]; exact b4 b c d e
    omega
  have hca4 : ({b, c, d, e} : Finset (Fin 20)).card = 4 := by
    rw [Finset.card_insert_of_notMem ha] at h; omega
  have hb : b ∉ ({c, d, e} : Finset (Fin 20)) := by
    intro hmem
    have : ({b, c, d, e} : Finset (Fin 20)).card ≤ 3 := by
      rw [Finset.insert_eq_self.mpr hmem]; exact b3 c d e
    omega
  have hcb3 : ({c, d, e} : Finset (Fin 20)).card = 3 := by
    rw [Finset.card_insert_of_notMem hb] at hca4; omega
  have hc : c ∉ ({d, e} : Finset (Fin 20)) := by
    intro hmem
    have h1 := Finset.card_insert_le d ({e} : Finset (Fin 20))
    have : ({c, d, e} : Finset (Fin 20)).card ≤ 2 := by
      rw [Finset.insert_eq_self.mpr hmem]
      simp only [Finset.card_singleton] at *; omega
    omega
  have hcc2 : ({d, e} : Finset (Fin 20)).card = 2 := by
    rw [Finset.card_insert_of_notMem hc] at hcb3; omega
  have hd : d ≠ e := by
    intro hmem
    rw [hmem] at hcc2
    simp at hcc2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, hb.1, hb.2.1, hb.2.2, hc.1, hc.2, hd⟩

/-- **A degree-`4` hub meets at most one cycle vertex (`n = 18`).**  Around an induced `C₅`
`v₁–⋯–v₅` of degree-`3` vertices, a degree-`4` hub `h` is adjacent to at most one `vᵢ`: two hits on
a cycle `P₃` give a triangle or good `C₄` (`hub_meets_path_le_one_twenty`).  Packaged as a `6`-way
split.  Port of `hub_cycle_cases`. -/
theorem hub_cycle_cases_twenty (G : SimpleGraph (Fin 20))
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (h v₁ v₂ v₃ v₄ v₅ : Fin 20) (hh : G.degree h = 4)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3 : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e36 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅)
    (d12 : v₁ ≠ v₂) (d13 : v₁ ≠ v₃) (d14 : v₁ ≠ v₄) (d15 : v₁ ≠ v₅)
    (d23 : v₂ ≠ v₃) (d24 : v₂ ≠ v₄) (d25 : v₂ ≠ v₅)
    (d36 : v₃ ≠ v₄) (d35 : v₃ ≠ v₅) (d45 : v₄ ≠ v₅) :
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₄ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₅) ∨
    (¬G.Adj h v₁ ∧ ¬G.Adj h v₂ ∧ ¬G.Adj h v₃ ∧ ¬G.Adj h v₄) := by
  have P123 := hub_meets_path_le_one_twenty G hT hC4 hh hd1 hd2 hd3 e12 e23 n13 d12 d23 d13
  have P234 := hub_meets_path_le_one_twenty G hT hC4 hh hd2 hd3 hd4 e23 e36 n24 d23 d36 d24
  have P345 := hub_meets_path_le_one_twenty G hT hC4 hh hd3 hd4 hd5 e36 e45 n35 d36 d45 d35
  have P451 := hub_meets_path_le_one_twenty G hT hC4 hh hd4 hd5 hd1 e45 e51
    (fun hh => n14 hh.symm) d45 d15.symm d14.symm
  have P512 := hub_meets_path_le_one_twenty G hT hC4 hh hd5 hd1 hd2 e51 e12
    (fun hh => n25 hh.symm) d15.symm d12 d25.symm
  have not12 : ¬(G.Adj h v₁ ∧ G.Adj h v₂) := P123.1
  have not23 : ¬(G.Adj h v₂ ∧ G.Adj h v₃) := P123.2.1
  have not13 : ¬(G.Adj h v₁ ∧ G.Adj h v₃) := P123.2.2
  have not36 : ¬(G.Adj h v₃ ∧ G.Adj h v₄) := P234.2.1
  have not24 : ¬(G.Adj h v₂ ∧ G.Adj h v₄) := P234.2.2
  have not45 : ¬(G.Adj h v₄ ∧ G.Adj h v₅) := P345.2.1
  have not35 : ¬(G.Adj h v₃ ∧ G.Adj h v₅) := P345.2.2
  have not51 : ¬(G.Adj h v₅ ∧ G.Adj h v₁) := P451.2.1
  have not41 : ¬(G.Adj h v₄ ∧ G.Adj h v₁) := P451.2.2
  have not52 : ¬(G.Adj h v₅ ∧ G.Adj h v₂) := P512.2.2
  by_cases a1 : G.Adj h v₁
  · exact Or.inr (Or.inl ⟨fun a => not12 ⟨a1, a⟩, fun a => not13 ⟨a1, a⟩,
      fun a => not41 ⟨a, a1⟩, fun a => not51 ⟨a, a1⟩⟩)
  · by_cases a2 : G.Adj h v₂
    · exact Or.inr (Or.inr (Or.inl ⟨a1, fun a => not23 ⟨a2, a⟩, fun a => not24 ⟨a2, a⟩,
        fun a => not52 ⟨a, a2⟩⟩))
    · by_cases a3 : G.Adj h v₃
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, fun a => not36 ⟨a3, a⟩,
          fun a => not35 ⟨a3, a⟩⟩)))
      · by_cases a4 : G.Adj h v₄
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨a1, a2, a3, fun a => not45 ⟨a4, a⟩⟩))))
        · by_cases a5 : G.Adj h v₅
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2, a3, a4⟩))))
          · exact Or.inl ⟨a1, a2, a3, a4, a5⟩

/-- **Shared degree-`4` hub by pigeonhole (`n = 18`).**  If the degree-`4` hub set `Hub4` carries
strictly more twin-incidences from the `M`-isolated set `Iso` than it has vertices, some hub is
adjacent to two distinct `M`-isolated degree-`3` twins.  Pure pigeonhole; for `n = 18` the calling
dichotomy adapts the count to `|Hub| ∈ {6, 7, 8, 9}` and its degree-`4` subset.  Port of
`shared_deg4_hub_from_count`. -/
theorem shared_deg4_hub_from_count_twenty (G : SimpleGraph (Fin 20)) (Iso Hub4 : Finset (Fin 20))
    (hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3)
    (hHub4deg : ∀ h ∈ Hub4, G.degree h = 4)
    (hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card) :
    ∃ h t₁ t₂ : Fin 20, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  have hincid : ∃ h ∈ Hub4, 2 ≤ (Iso.filter (fun v => G.Adj v h)).card := by
    by_contra hcon
    push Not at hcon
    have hsum1 : ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card ≤ Hub4.card := by
      calc ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card
          ≤ ∑ _h ∈ Hub4, 1 := Finset.sum_le_sum (fun h hh => by have := hcon h hh; omega)
        _ = Hub4.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hswap : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
        = ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card := by
      have hL : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub4).card
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
  obtain ⟨ht1deg, ht1iso⟩ := hIsoiso t₁ ht1Iso
  obtain ⟨ht2deg, ht2iso⟩ := hIsoiso t₂ ht2Iso
  exact ⟨h, t₁, t₂, hHub4deg h hhHub4, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1iso, ht2iso⟩

/-- **Fat-dominating claw assembly (`n = 18`).**  A degree-`3` centre `c` whose three neighbours
are all degree-`3` (in-`M`-degree `3`, hence hub-free), together with a degree-`4` hub `h` adjacent
to two distinct `M`-isolated degree-`3` twins `t₁, t₂`, yields a `TwoTwinConfig`: `h` meets at most
one of `c`'s neighbours (two hits form an induced `C₄`), so two free neighbours and `c` form a
cherry avoiding `h`.  Port of `claw_shared_two_twin`. -/
theorem claw_shared_two_twin_twenty (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (c t₁ t₂ h : Fin 20) (hcD : c ∈ D)
    (hcge : 3 ≤ (G.neighborFinset c ∩ D).card)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3) (hhdeg4 : G.degree h = 4)
    (ht12 : t₁ ≠ t₂) (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h)
    (ht1iso : ∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3) :
    TwoTwinConfig G := by
  classical
  have hdegD : ∀ v : Fin 20, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
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
  have hmem_i : ∀ w : Fin 20, w ∈ ({n₁, n₂, n₃} : Finset (Fin 20)) → G.Adj c w ∧ w ∈ D := by
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
  have hcnbhd : ∀ w : Fin 20, G.Adj c w → w = n₁ ∨ w = n₂ ∨ w = n₃ := by
    intro w hw
    have hw' : w ∈ G.neighborFinset c ∩ D := by
      rw [hNsubeq]; exact (G.mem_neighborFinset _ _).mpr hw
    rw [hset] at hw'; simpa using hw'
  have hhc : ¬G.Adj h c := by
    intro hadj
    rcases hcnbhd h hadj.symm with e | e | e <;> rw [e] at hhdeg4 <;> omega
  have hmeet : ∀ i j : Fin 20, G.degree i = 3 → G.degree j = 3 →
      G.Adj c i → G.Adj c j → i ≠ j → ¬(G.Adj h i ∧ G.Adj h j) := by
    rintro i j hi3 hj3 ci cj hij ⟨hhi, hhj⟩
    have nij : ¬G.Adj i j := fun aij =>
      hT ⟨c, i, j, ci.ne, hij, cj.ne, ci, aij, cj, by omega⟩
    exact hC4 ⟨h, i, c, j,
      card_four_twenty h i c j (by rintro rfl; omega) (by rintro rfl; omega)
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

end N20

end ACMax
