import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.CherryCore

/-!
# `n = 19`, `e(M) = 3` (`s = 6`), `P₄`-cherry corner: the `{c₁,c₂}`-avoider count

The genuinely-new counting leaf for the `P₄`-cherry corners (`TwinCert19CherryP4.lean`).  Using the
two-vertex cherry `K = {c₁,c₂}` (each centre meets exactly one hub) the avoider count closes, with
the leak through the two leaves `L₁,L₂` bounded by `∑_{w∈Dᶜ}|N w ∩ {L₁,L₂}| ≤ 4` and absorbed by the
strict pigeonhole margin (`3·|HubA| > Int + 4` at `|D| ∈ {9,10,11}`).
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **`{c₁,c₂}`-avoider with two `M`-isolated twins (`n = 19`, `P₄` corner).**  For the path
`L₁–c₁–c₂–L₂` residual with `|D| ∈ {9,10,11}`, there is a degree-`≤ 5` hub `h` avoiding both centres
`c₁, c₂` and carrying two distinct `M`-isolated twins `t₁, t₂ ∈ Iso`. -/
theorem p4_c1c2_avoider_two_twin_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 19) (D Iso : Finset (Fin 19))
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11) :
    (∃ h t₁ t₂ : Fin 19, h ∈ Dᶜ ∧ G.degree h ≤ 5 ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h c₂ ∧
      t₁ ≠ t₂ ∧ t₁ ∈ Iso ∧ t₂ ∈ Iso ∧ G.Adj h t₁ ∧ G.Adj h t₂) ∨
    (SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G) := by
  classical
  -- Path distinctness.
  have hc1L1 : c₁ ≠ L₁ := G.ne_of_adj hac1L1
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hL1L2 : L₁ ≠ L₂ := by
    intro e
    exact hT ⟨c₁, c₂, L₁, hc1c2, fun e2 => hL1nc2 e2.symm, hc1L1, hc12,
      by rw [e]; exact hac2L2, hac1L1, by omega⟩
  have hL1c1 : L₁ ≠ c₁ := hc1L1.symm
  have hc1L2 : c₁ ≠ L₂ := fun e => hL2nc1 e.symm
  have hc2L1 : c₂ ≠ L₁ := fun e => hL1nc2 e.symm
  -- Membership in `D`.
  have hc1D : c₁ ∈ D := (hmemD c₁).mpr hc1deg
  have hc2D : c₂ ∈ D := (hmemD c₂).mpr hc2deg
  have hL1D : L₁ ∈ D := (hmemD L₁).mpr hL1deg
  have hL2D : L₂ ∈ D := (hmemD L₂).mpr hL2deg
  have hIsoD : ∀ v : Fin 19, v ∈ Iso → v ∈ D := fun v hv => (hmemD v).mpr (hIsoprop v hv).1
  -- Path vertices are not `M`-isolated.
  have hc1Iso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 c₂ hc12 (by rw [hc2deg])
  have hc2Iso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm (by rw [hc1deg])
  have hL1Iso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm (by rw [hc1deg])
  have hL2Iso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm (by rw [hc2deg])
  -- Per-vertex `D`/`Dᶜ` degree split.
  have hsplit : ∀ v : Fin 19,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha' =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp ha').2) (Finset.mem_inter.mp ha).2)
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  have hc1Dc : (G.neighborFinset c₁ ∩ Dᶜ).card = 1 := by have := hsplit c₁; omega
  have hc2Dc : (G.neighborFinset c₂ ∩ Dᶜ).card = 1 := by have := hsplit c₂; omega
  -- Degree sums.
  have hsum60 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 68 - 3 * D.card := by
    have hh : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 68 := by
      rw [Finset.sum_add_sum_compl]; exact hsum60
    omega
  have hDc_card : Dᶜ.card = 19 - D.card := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  have hDcdeg : ∀ w : Fin 19, w ∈ Dᶜ → 4 ≤ G.degree w := by
    intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
  -- `D = {L₁,c₁,c₂,L₂} ∪ Iso`.
  set path : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hpathdef
  have hpathsub : path ⊆ D := by
    intro w hw
    simp only [hpathdef, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hDeq : D = path ∪ Iso := by
    apply Finset.Subset.antisymm
    · intro w hw
      by_cases hwL1 : w = L₁
      · subst hwL1; exact Finset.mem_union_left _ (by simp [hpathdef])
      by_cases hwc1 : w = c₁
      · subst hwc1; exact Finset.mem_union_left _ (by simp [hpathdef])
      by_cases hwc2 : w = c₂
      · subst hwc2; exact Finset.mem_union_left _ (by simp [hpathdef])
      by_cases hwL2 : w = L₂
      · subst hwL2; exact Finset.mem_union_left _ (by simp [hpathdef])
      exact Finset.mem_union_right _ (hisochar w hw hwL1 hwc1 hwc2 hwL2)
    · intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hpathsub hw
      · exact hIsoD w hw
  have hpathIsodisj : Disjoint path Iso := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [hpathdef, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hL1Iso hw'
    · exact hc1Iso hw'
    · exact hc2Iso hw'
    · exact hL2Iso hw'
  -- `|N L₁ ∩ D| = 1` and `|N L₂ ∩ D| = 1`.
  have hIso0 : ∀ v : Fin 19, v ∈ Iso → (G.neighborFinset v ∩ D).card = 0 := by
    intro v hv
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    exact (hIsoprop v hv).2 w hw.1 ((hmemD w).mp hw.2)
  have hsumpath : ∑ v ∈ path, (G.neighborFinset v ∩ D).card = 6 := by
    have hsumsplit : ∑ v ∈ path, (G.neighborFinset v ∩ D).card
        + ∑ v ∈ Iso, (G.neighborFinset v ∩ D).card
        = ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
      rw [hDeq]; exact (Finset.sum_union hpathIsodisj).symm
    rw [Finset.sum_congr rfl (fun v hv => hIso0 v hv), Finset.sum_const, smul_eq_mul,
      mul_zero, add_zero] at hsumsplit
    rw [hsumsplit]; exact hs6
  have hpathexpand : ∑ v ∈ path, (G.neighborFinset v ∩ D).card
      = (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset c₁ ∩ D).card
        + (G.neighborFinset c₂ ∩ D).card + (G.neighborFinset L₂ ∩ D).card := by
    rw [hpathdef, Finset.sum_insert (by simp [hL1c1, hL1nc2, hL1L2]),
      Finset.sum_insert (by simp [hc1c2, hc1L2]),
      Finset.sum_insert (by simp [hc2L2]), Finset.sum_singleton]
    ring
  have hL1ge : 1 ≤ (G.neighborFinset L₁ ∩ D).card :=
    Finset.card_pos.mpr ⟨c₁, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩⟩
  have hL2ge : 1 ≤ (G.neighborFinset L₂ ∩ D).card :=
    Finset.card_pos.mpr ⟨c₂, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset L₂ c₂).mpr hac2L2.symm, hc2D⟩⟩
  have hL1Dc : (G.neighborFinset L₁ ∩ Dᶜ).card = 2 := by
    rw [hpathexpand, hin1, hin2] at hsumpath; have := hsplit L₁; omega
  have hL2Dc : (G.neighborFinset L₂ ∩ Dᶜ).card = 2 := by
    rw [hpathexpand, hin1, hin2] at hsumpath; have := hsplit L₂; omega
  -- Internal sum `∑_{Dᶜ}|N w ∩ Dᶜ| = 74 − 6|D|`.
  set Int : ℕ := 74 - 6 * D.card with hIntdef
  have hcrossDDc : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
      = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count_nineteen G D Dᶜ
  have hsumD_Dc : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card = 3 * D.card - 6 := by
    have hcong : ∑ v ∈ D, ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
        = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hsplit v)
    rw [Finset.sum_add_distrib, hs6, hsumDdeg] at hcong; omega
  have hIntval : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = Int := by
    have hcong : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card)
        = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hsplit w)
    rw [Finset.sum_add_distrib, ← hcrossDDc, hsumD_Dc, hsumDcdeg] at hcong
    rw [hIntdef]; omega
  -- The "bad" hubs and `HubA = Dᶜ \ Bad`.
  set Bad : Finset (Fin 19) :=
    Dᶜ.filter (fun w => G.Adj w c₁ ∨ G.Adj w c₂ ∨ 6 ≤ G.degree w) with hBaddef
  set HubA : Finset (Fin 19) := Dᶜ \ Bad with hHubAdef
  have hBadsub : Bad ⊆ Dᶜ := Finset.filter_subset _ _
  have hfc1 : (Dᶜ.filter (fun w => G.Adj w c₁)).card ≤ 1 := by
    have heq : Dᶜ.filter (fun w => G.Adj w c₁) = G.neighborFinset c₁ ∩ Dᶜ := by
      ext w; simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
    rw [heq, hc1Dc]
  have hfc2 : (Dᶜ.filter (fun w => G.Adj w c₂)).card ≤ 1 := by
    have heq : Dᶜ.filter (fun w => G.Adj w c₂) = G.neighborFinset c₂ ∩ Dᶜ := by
      ext w; simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
    rw [heq, hc2Dc]
  set Big : Finset (Fin 19) := Dᶜ.filter (fun w => 6 ≤ G.degree w) with hBigdef
  have hBigsub : Big ⊆ Dᶜ := Finset.filter_subset _ _
  have hnbig : 2 * Big.card ≤ D.card - 8 := by
    have h1 : 6 * Big.card ≤ ∑ w ∈ Big, G.degree w := by
      have := Finset.card_nsmul_le_sum Big (fun w => G.degree w) 6
        (fun w hw => (Finset.mem_filter.mp hw).2)
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have h2 : 4 * (Dᶜ \ Big).card ≤ ∑ w ∈ Dᶜ \ Big, G.degree w := by
      have := Finset.card_nsmul_le_sum (Dᶜ \ Big) (fun w => G.degree w) 4
        (fun w hw => hDcdeg w (Finset.mem_sdiff.mp hw).1)
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hsplitB : ∑ w ∈ Dᶜ \ Big, G.degree w + ∑ w ∈ Big, G.degree w = 68 - 3 * D.card := by
      rw [Finset.sum_sdiff hBigsub]; exact hsumDcdeg
    have hcardB : (Dᶜ \ Big).card + Big.card = 19 - D.card := by
      rw [Finset.card_sdiff_add_card_eq_card hBigsub]; exact hDc_card
    omega
  have hBadsub2 : Bad ⊆ (Dᶜ.filter (fun w => G.Adj w c₁) ∪ Dᶜ.filter (fun w => G.Adj w c₂))
      ∪ Big := by
    intro w hw
    rw [hBaddef, Finset.mem_filter] at hw
    obtain ⟨hwDc, hor⟩ := hw
    rcases hor with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwDc, h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwDc, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwDc, h⟩)
  have hBadle : Bad.card ≤ 2 + Big.card := by
    have hu1 := Finset.card_union_le (Dᶜ.filter (fun w => G.Adj w c₁)
      ∪ Dᶜ.filter (fun w => G.Adj w c₂)) Big
    have hu2 := Finset.card_union_le (Dᶜ.filter (fun w => G.Adj w c₁))
      (Dᶜ.filter (fun w => G.Adj w c₂))
    have := Finset.card_le_card hBadsub2
    omega
  have hHubAcard : HubA.card + Bad.card = Dᶜ.card := by
    rw [hHubAdef]; exact Finset.card_sdiff_add_card_eq_card hBadsub
  -- Every `HubA` hub avoids `c₁,c₂` and has degree `≤ 5`.
  have hHubA_props : ∀ h : Fin 19, h ∈ HubA →
      h ∈ Dᶜ ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h c₂ ∧ G.degree h ≤ 5 := by
    intro h hh
    rw [hHubAdef, Finset.mem_sdiff] at hh
    obtain ⟨hhDc, hhnBad⟩ := hh
    refine ⟨hhDc, ?_, ?_, ?_⟩
    · intro ha; exact hhnBad (by rw [hBaddef, Finset.mem_filter]; exact ⟨hhDc, Or.inl ha⟩)
    · intro ha; exact hhnBad (by rw [hBaddef, Finset.mem_filter]; exact ⟨hhDc, Or.inr (Or.inl ha)⟩)
    · by_contra hc
      exact hhnBad (by rw [hBaddef, Finset.mem_filter]; exact ⟨hhDc, Or.inr (Or.inr (by omega))⟩)
  have hHubAdeg5 : ∀ h : Fin 19, h ∈ HubA → G.degree h ≤ 5 := fun h hh => (hHubA_props h hh).2.2.2
  have hHubAsub : HubA ⊆ Dᶜ := by rw [hHubAdef]; exact Finset.sdiff_subset
  -- Per-hub Iso count for `HubA` hubs.
  have hHubA_iso : ∀ h : Fin 19, h ∈ HubA →
      (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card
        + (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card = G.degree h := by
    intro h hh
    obtain ⟨_, hhnc1, hhnc2, _⟩ := hHubA_props h hh
    have hpartD : (G.neighborFinset h ∩ path).card + (G.neighborFinset h ∩ Iso).card
        = (G.neighborFinset h ∩ D).card := by
      have hdisj : Disjoint (G.neighborFinset h ∩ path) (G.neighborFinset h ∩ Iso) :=
        Finset.disjoint_left.mpr (fun w hw hw' =>
          (Finset.disjoint_left.mp hpathIsodisj (Finset.mem_inter.mp hw).2)
            (Finset.mem_inter.mp hw').2)
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, ← hDeq]
    have hpathleaf :
        G.neighborFinset h ∩ path = G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19)) := by
      ext w
      simp only [hpathdef, Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hadj, rfl | rfl | rfl | rfl⟩
        · exact ⟨hadj, Or.inl rfl⟩
        · exact absurd hadj hhnc1
        · exact absurd hadj hhnc2
        · exact ⟨hadj, Or.inr rfl⟩
      · rintro ⟨hadj, rfl | rfl⟩
        · exact ⟨hadj, Or.inl rfl⟩
        · exact ⟨hadj, Or.inr (Or.inr (Or.inr rfl))⟩
    have hd2 := hsplit h
    rw [hpathleaf] at hpartD
    omega
  have hsumIso : ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card
      + ∑ h ∈ HubA, (G.neighborFinset h ∩ Dᶜ).card
      + ∑ h ∈ HubA, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card
      = ∑ h ∈ HubA, G.degree h := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hHubA_iso
  have hdegAge : 4 * HubA.card ≤ ∑ h ∈ HubA, G.degree h := by
    have := Finset.card_nsmul_le_sum HubA (fun h => G.degree h) 4
      (fun h hh => hDcdeg h (hHubAsub hh))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hDcsumle : ∑ h ∈ HubA, (G.neighborFinset h ∩ Dᶜ).card ≤ Int := by
    rw [← hIntval]; exact Finset.sum_le_sum_of_subset hHubAsub
  have hleakle : ∑ h ∈ HubA, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card ≤ 4 := by
    have hfull : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card = 4 := by
      rw [cross_count_nineteen G Dᶜ ({L₁, L₂} : Finset (Fin 19)),
        Finset.sum_insert (by simp [hL1L2]), Finset.sum_singleton, hL1Dc, hL2Dc]
    calc ∑ h ∈ HubA, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card
        ≤ ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card :=
          Finset.sum_le_sum_of_subset hHubAsub
      _ = 4 := hfull
  -- The pigeonhole margin is only NON-strict (`3·|HubA| ≥ Int + 4` TIES at `|D| ∈ {9,10}`
  -- with `|Bad| = 2`, `|Big| = 0`, `|HubA| = 8`, `Int = 20`); the strict form is FALSE
  -- (realizable tie graphs verified by direct construction, `scratchpad/p4tie_*`).
  have hge : HubA.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card := by
    have hcross : ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card
        = ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card := cross_count_nineteen G Iso HubA
    rw [hcross]
    have hHubAge : Dᶜ.card ≤ HubA.card + 2 + Big.card := by omega
    rw [hDc_card] at hHubAge
    omega
  by_cases hex : ∃ h ∈ HubA, 2 ≤ (G.neighborFinset h ∩ Iso).card
  · -- A twin-rich avoider exists: the LEFT conclusion.
    obtain ⟨h, hhHubA, h2⟩ := hex
    obtain ⟨hhDc, hhnc1, hhnc2, hhdeg5⟩ := hHubA_props h hhHubA
    obtain ⟨t₁, t₂, ht₁, ht₂, ht12⟩ := Finset.one_lt_card_iff.mp h2
    rw [Finset.mem_inter, G.mem_neighborFinset] at ht₁ ht₂
    exact Or.inl ⟨h, t₁, t₂, hhDc, hhdeg5, hhnc1, hhnc2, ht12, ht₁.2, ht₂.2,
      ht₁.1, ht₂.1⟩
  · -- **THE TIE** (every avoider carries exactly one twin): the count forces full
    -- equality — every `HubA` hub has degree `4` and exactly one `Iso` twin, the
    -- internal sum saturates, and all four leaf slots land in `HubA`.  The rigid
    -- structure yields a `TwoHubConfig` (leaf-hub pairs) or `SingleVertexConfig`
    -- (verified on 110/110 tie realizations by direct construction).
    push Not at hex
    right
    -- STEP 1 (tightness): the tie forces equality throughout the counting chain.
    have hisole : ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card ≤ HubA.card := by
      calc ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ HubA, 1 :=
            Finset.sum_le_sum fun h hh => by have := hex h hh; omega
        _ = HubA.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hisoeq : ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card = HubA.card := by
      have hcross : ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card
          = ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card := cross_count_nineteen G Iso HubA
      rw [hcross] at hge
      omega
    -- `|D| = 11` dies (`3·|HubA| ≤ Int + 4` fails); `|D| ∈ {9, 10}` ties exactly.
    have hDcase : (D.card = 9 ∧ HubA.card = 8) ∨
        (D.card = 10 ∧ HubA.card = 6 ∧ Bad.card = 3 ∧ Big.card = 1) := by omega
    have hSdeg : ∑ h ∈ HubA, G.degree h = 4 * HubA.card := by omega
    have hSdc : ∑ h ∈ HubA, (G.neighborFinset h ∩ Dᶜ).card = Int := by omega
    have hSleaf : ∑ h ∈ HubA, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card = 4 := by
      omega
    -- Pointwise consequences on `HubA`: degree exactly `4`, exactly one twin.
    have hdeg4A : ∀ h ∈ HubA, G.degree h = 4 := by
      intro h hh
      have h1 : G.degree h + ∑ v ∈ HubA.erase h, G.degree v = 4 * HubA.card :=
        (Finset.add_sum_erase _ (fun v => G.degree v) hh).trans hSdeg
      have h2 : 4 * (HubA.erase h).card ≤ ∑ v ∈ HubA.erase h, G.degree v := by
        calc 4 * (HubA.erase h).card = ∑ _v ∈ HubA.erase h, 4 := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ v ∈ HubA.erase h, G.degree v :=
              Finset.sum_le_sum fun v hv => hDcdeg v (hHubAsub (Finset.mem_of_mem_erase hv))
      have h3 : (HubA.erase h).card + 1 = HubA.card := by
        rw [Finset.card_erase_of_mem hh]
        have h4 : 1 ≤ HubA.card := Finset.card_pos.mpr ⟨h, hh⟩
        omega
      have h5 := hDcdeg h (hHubAsub hh)
      omega
    have hiso1 : ∀ h ∈ HubA, (G.neighborFinset h ∩ Iso).card = 1 := by
      intro h hh
      have h1 : (G.neighborFinset h ∩ Iso).card
          + ∑ v ∈ HubA.erase h, (G.neighborFinset v ∩ Iso).card = HubA.card :=
        (Finset.add_sum_erase _ (fun v => (G.neighborFinset v ∩ Iso).card) hh).trans hisoeq
      have h2 : ∑ v ∈ HubA.erase h, (G.neighborFinset v ∩ Iso).card ≤ (HubA.erase h).card := by
        calc ∑ v ∈ HubA.erase h, (G.neighborFinset v ∩ Iso).card ≤ ∑ _v ∈ HubA.erase h, 1 :=
              Finset.sum_le_sum fun v hv => by
                have := hex v (Finset.mem_of_mem_erase hv)
                omega
          _ = (HubA.erase h).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      have h3 : (HubA.erase h).card + 1 = HubA.card := by
        rw [Finset.card_erase_of_mem hh]
        have h4 : 1 ≤ HubA.card := Finset.card_pos.mpr ⟨h, hh⟩
        omega
      have h5 := hex h hh
      omega
    -- The `Bad` hubs carry no leaf slot and no `Dᶜ`-edge (their sums saturate to `0`).
    have hfull : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card = 4 := by
      rw [cross_count_nineteen G Dᶜ ({L₁, L₂} : Finset (Fin 19)),
        Finset.sum_insert (by simp [hL1L2]), Finset.sum_singleton, hL1Dc, hL2Dc]
    have hBadsplitL : ∑ h ∈ HubA, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card
        + ∑ w ∈ Bad, (G.neighborFinset w ∩ ({L₁, L₂} : Finset (Fin 19))).card
        = ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 19))).card := by
      rw [hHubAdef]
      exact Finset.sum_sdiff hBadsub
    have hBadleaf : ∀ w ∈ Bad, (G.neighborFinset w ∩ ({L₁, L₂} : Finset (Fin 19))).card = 0 :=
      Finset.sum_eq_zero_iff.mp (by omega)
    have hBadsplitD : ∑ h ∈ HubA, (G.neighborFinset h ∩ Dᶜ).card
        + ∑ w ∈ Bad, (G.neighborFinset w ∩ Dᶜ).card
        = ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Dᶜ).card := by
      rw [hHubAdef]
      exact Finset.sum_sdiff hBadsub
    have hBadDc : ∀ w ∈ Bad, (G.neighborFinset w ∩ Dᶜ).card = 0 :=
      Finset.sum_eq_zero_iff.mp (by omega)
    -- `N L₁ ∩ D = {c₁}`, so the cherry `L₁–c₁–c₂` is induced.
    have hL1Deq : G.neighborFinset L₁ ∩ D = {c₁} := by
      have hcard : (G.neighborFinset L₁ ∩ D).card = 1 := by
        have := hsplit L₁
        omega
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
      have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩
      rw [hu] at hc1mem ⊢
      rw [Finset.mem_singleton] at hc1mem
      rw [hc1mem]
    have hnL1c2 : ¬G.Adj L₁ c₂ := by
      intro ha
      have hmem : c₂ ∈ G.neighborFinset L₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha, hc2D⟩
      rw [hL1Deq, Finset.mem_singleton] at hmem
      exact hc1c2 hmem.symm
    rcases hDcase with ⟨hD9, hH8⟩ | ⟨hD10, hH6, hBad3, hBig1⟩
    · -- `|D| = 9`, `|HubA| = 8`, `|Iso| = 5`: dropping the two `L₁`-hubs leaves twin-incidence
      -- `8 − 2 = 6 > 5 = |Iso|`, so some twin meets two `L₁`-avoiding degree-`4` hubs — a
      -- `SingleVertexConfig` against the cherry `L₁–c₁–c₂` (all slots vanish, budget `8 ≤ 8`).
      obtain ⟨p, q, hpq, hPQ⟩ := Finset.card_eq_two.mp hL1Dc
      have hpmem : p ∈ G.neighborFinset L₁ ∩ Dᶜ := by
        rw [hPQ]
        exact Finset.mem_insert_self _ _
      have hqmem : q ∈ G.neighborFinset L₁ ∩ Dᶜ := by
        rw [hPQ]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
      have hpDc : p ∈ Dᶜ := (Finset.mem_inter.mp hpmem).2
      have hqDc : q ∈ Dᶜ := (Finset.mem_inter.mp hqmem).2
      have hpL1 : G.Adj L₁ p := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hpmem).1
      have hqL1 : G.Adj L₁ q := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hqmem).1
      have hpHubA : p ∈ HubA := by
        rw [hHubAdef, Finset.mem_sdiff]
        refine ⟨hpDc, fun hpBad => ?_⟩
        have h0 := hBadleaf p hpBad
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
        exact h0 L₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hpL1.symm,
          Finset.mem_insert_self _ _⟩)
      have hqHubA : q ∈ HubA := by
        rw [hHubAdef, Finset.mem_sdiff]
        refine ⟨hqDc, fun hqBad => ?_⟩
        have h0 := hBadleaf q hqBad
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
        exact h0 L₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hqL1.symm,
          Finset.mem_insert_self _ _⟩)
      have hPQsub : ({p, q} : Finset (Fin 19)) ⊆ HubA := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hpHubA
        · rw [Finset.mem_singleton] at hw
          subst hw
          exact hqHubA
      have hpq2 : ∑ v ∈ Iso, (G.neighborFinset v ∩ ({p, q} : Finset (Fin 19))).card = 2 := by
        rw [cross_count_nineteen G Iso ({p, q} : Finset (Fin 19)),
          Finset.sum_insert (by simp [hpq]), Finset.sum_singleton,
          hiso1 p hpHubA, hiso1 q hqHubA]
      have hIsosum : ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card = 8 := by
        rw [cross_count_nineteen G Iso HubA, hisoeq, hH8]
      have hsplitv : ∀ v : Fin 19,
          (G.neighborFinset v ∩ (HubA \ ({p, q} : Finset (Fin 19)))).card
            + (G.neighborFinset v ∩ ({p, q} : Finset (Fin 19))).card
            = (G.neighborFinset v ∩ HubA).card := by
        intro v
        have hdisj : Disjoint (G.neighborFinset v ∩ (HubA \ ({p, q} : Finset (Fin 19))))
            (G.neighborFinset v ∩ ({p, q} : Finset (Fin 19))) :=
          Finset.disjoint_left.mpr fun w hw hw' =>
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp hw).2).2 (Finset.mem_inter.mp hw').2
        rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left,
          Finset.sdiff_union_of_subset hPQsub]
      have hrest : ∑ v ∈ Iso, (G.neighborFinset v ∩ (HubA \ ({p, q} : Finset (Fin 19)))).card
          = 6 := by
        have hs : ∑ v ∈ Iso, ((G.neighborFinset v ∩ (HubA \ ({p, q} : Finset (Fin 19)))).card
            + (G.neighborFinset v ∩ ({p, q} : Finset (Fin 19))).card)
            = ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card :=
          Finset.sum_congr rfl fun v _ => hsplitv v
        rw [Finset.sum_add_distrib, hpq2, hIsosum] at hs
        omega
      have hIsocard : Iso.card = 5 := by
        have h1 : D.card = path.card + Iso.card := by
          rw [hDeq]
          exact Finset.card_union_of_disjoint hpathIsodisj
        have h2 : path.card = 4 := by
          rw [hpathdef]
          exact card_four_nineteen L₁ c₁ c₂ L₂ hL1c1 hL1nc2 hL1L2 hc1c2 hc1L2 hc2L2
        omega
      have hpig : ∃ v ∈ Iso,
          2 ≤ (G.neighborFinset v ∩ (HubA \ ({p, q} : Finset (Fin 19)))).card := by
        by_contra hcon
        push Not at hcon
        have hle : ∑ v ∈ Iso, (G.neighborFinset v ∩ (HubA \ ({p, q} : Finset (Fin 19)))).card
            ≤ 5 := by
          calc ∑ v ∈ Iso, (G.neighborFinset v ∩ (HubA \ ({p, q} : Finset (Fin 19)))).card
              ≤ ∑ _v ∈ Iso, 1 := Finset.sum_le_sum fun v hv => by
                have := hcon v hv
                omega
            _ = Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
            _ = 5 := hIsocard
        omega
      obtain ⟨v, hvIso, hv2⟩ := hpig
      obtain ⟨h₁, hh₁m, h₂, hh₂m, hne12⟩ := Finset.one_lt_card.mp
        (by omega : 1 < (G.neighborFinset v ∩ (HubA \ ({p, q} : Finset (Fin 19)))).card)
      obtain ⟨hh₁N, hh₁R⟩ := Finset.mem_inter.mp hh₁m
      obtain ⟨hh₁A, hh₁pq⟩ := Finset.mem_sdiff.mp hh₁R
      obtain ⟨hh₂N, hh₂R⟩ := Finset.mem_inter.mp hh₂m
      obtain ⟨hh₂A, hh₂pq⟩ := Finset.mem_sdiff.mp hh₂R
      have hAvh1 : G.Adj v h₁ := (G.mem_neighborFinset _ _).mp hh₁N
      have hAvh2 : G.Adj v h₂ := (G.mem_neighborFinset _ _).mp hh₂N
      have hvdeg : G.degree v = 3 := (hIsoprop v hvIso).1
      have hd41 : G.degree h₁ = 4 := hdeg4A h₁ hh₁A
      have hd42 : G.degree h₂ = 4 := hdeg4A h₂ hh₂A
      have hnh1L1 : ¬G.Adj h₁ L₁ := fun ha => hh₁pq (by
        rw [← hPQ]
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha.symm, hHubAsub hh₁A⟩)
      have hnh2L1 : ¬G.Adj h₂ L₁ := fun ha => hh₂pq (by
        rw [← hPQ]
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha.symm, hHubAsub hh₂A⟩)
      have hslotv : (G.neighborFinset v ∩ ({L₁, c₁, c₂} : Finset (Fin 19))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        obtain ⟨hwN, hwC⟩ := Finset.mem_inter.mp hw
        have hadj := (G.mem_neighborFinset _ _).mp hwN
        have hwdeg : G.degree w = 3 := by
          rcases Finset.mem_insert.mp hwC with rfl | hwC
          · exact hL1deg
          rcases Finset.mem_insert.mp hwC with rfl | hwC
          · exact hc1deg
          rw [Finset.mem_singleton] at hwC
          subst hwC
          exact hc2deg
        exact (hIsoprop v hvIso).2 w hadj hwdeg
      have hsloth : ∀ h : Fin 19, h ∈ HubA → ¬G.Adj h L₁ →
          (G.neighborFinset h ∩ ({L₁, c₁, c₂} : Finset (Fin 19))).card = 0 := by
        intro h hhA hnL1
        obtain ⟨_, hnc1, hnc2, _⟩ := hHubA_props h hhA
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        obtain ⟨hwN, hwC⟩ := Finset.mem_inter.mp hw
        have hadj := (G.mem_neighborFinset _ _).mp hwN
        rcases Finset.mem_insert.mp hwC with rfl | hwC
        · exact hnL1 hadj
        rcases Finset.mem_insert.mp hwC with rfl | hwC
        · exact hnc1 hadj
        rw [Finset.mem_singleton] at hwC
        subst hwC
        exact hnc2 hadj
      have hvh1 : v ≠ h₁ := by
        rintro rfl
        omega
      have hvh2 : v ≠ h₂ := by
        rintro rfl
        omega
      have hslotsum : ∑ w ∈ ({v, h₁, h₂} : Finset (Fin 19)),
          (G.neighborFinset w ∩ ({L₁, c₁, c₂} : Finset (Fin 19))).card = 0 := by
        rw [Finset.sum_insert (by simp [hvh1, hvh2]), Finset.sum_insert (by simp [hne12]),
          Finset.sum_singleton, hslotv, hsloth h₁ hh₁A hnh1L1, hsloth h₂ hh₂A hnh2L1]
        omega
      have hbudget : 2 * (∑ w ∈ ({v, h₁, h₂} : Finset (Fin 19)),
          (G.neighborFinset w ∩ ({L₁, c₁, c₂} : Finset (Fin 19))).card)
          + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * (if G.Adj h₁ h₂ then 1 else 0) := by
        rw [hslotsum, hd41, hd42]
        split <;> omega
      have hvL1 : v ≠ L₁ := fun e => hL1Iso (e ▸ hvIso)
      have hvc1 : v ≠ c₁ := fun e => hc1Iso (e ▸ hvIso)
      have hvc2 : v ≠ c₂ := fun e => hc2Iso (e ▸ hvIso)
      have h1L1 : h₁ ≠ L₁ := by
        rintro rfl
        omega
      have h1c1 : h₁ ≠ c₁ := by
        rintro rfl
        omega
      have h1c2 : h₁ ≠ c₂ := by
        rintro rfl
        omega
      have h2L1 : h₂ ≠ L₁ := by
        rintro rfl
        omega
      have h2c1 : h₂ ≠ c₁ := by
        rintro rfl
        omega
      have h2c2 : h₂ ≠ c₂ := by
        rintro rfl
        omega
      exact Or.inl ⟨v, h₁, h₂, L₁, c₁, c₂, hvdeg, hL1deg, hc1deg, hc2deg,
        hAvh1, hAvh2, hac1L1.symm, hc12, hnL1c2, hbudget, hne12, hvL1, hvc1, hvc2,
        h1L1, h1c1, h1c2, h2L1, h2c1, h2c2, hL1c1, hc1c2, hL1nc2⟩
    · -- `|D| = 10`: `Bad = {b₁, b₂, B}` with the two centre-hubs `b₁, b₂` forced to degree
      -- `4` (Σ_Bad deg = 14, big hub ≥ 6), so each carries exactly `3` twins; they share at
      -- most one twin (two shared twins close a `Σ = 14` C4 `t–b₁–t'–b₂`), so disjoint twin
      -- pairs exist: a `TwoHubConfig` on `b₁, b₂`.
      obtain ⟨b₁, hb1eq⟩ := Finset.card_eq_one.mp hc1Dc
      obtain ⟨b₂, hb2eq⟩ := Finset.card_eq_one.mp hc2Dc
      have hb1mem : b₁ ∈ G.neighborFinset c₁ ∩ Dᶜ := by
        rw [hb1eq]
        exact Finset.mem_singleton_self b₁
      have hb2mem : b₂ ∈ G.neighborFinset c₂ ∩ Dᶜ := by
        rw [hb2eq]
        exact Finset.mem_singleton_self b₂
      have hb1Dc : b₁ ∈ Dᶜ := (Finset.mem_inter.mp hb1mem).2
      have hb2Dc : b₂ ∈ Dᶜ := (Finset.mem_inter.mp hb2mem).2
      have hAc1b1 : G.Adj c₁ b₁ := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hb1mem).1
      have hAc2b2 : G.Adj c₂ b₂ := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hb2mem).1
      have hb1Bad : b₁ ∈ Bad := by
        rw [hBaddef, Finset.mem_filter]
        exact ⟨hb1Dc, Or.inl hAc1b1.symm⟩
      have hb2Bad : b₂ ∈ Bad := by
        rw [hBaddef, Finset.mem_filter]
        exact ⟨hb2Dc, Or.inr (Or.inl hAc2b2.symm)⟩
      have hf1eq : Dᶜ.filter (fun w => G.Adj w c₁) = {b₁} := by
        rw [← hb1eq]
        ext w
        simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
      have hf2eq : Dᶜ.filter (fun w => G.Adj w c₂) = {b₂} := by
        rw [← hb2eq]
        ext w
        simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
      have hBadsub3 : Bad ⊆ ({b₁, b₂} : Finset (Fin 19)) ∪ Big := by
        intro w hw
        have hw2 := hBadsub2 hw
        rw [hf1eq, hf2eq] at hw2
        rcases Finset.mem_union.mp hw2 with h | h
        · rcases Finset.mem_union.mp h with h | h
          · rw [Finset.mem_singleton] at h
            subst h
            exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
          · rw [Finset.mem_singleton] at h
            subst h
            exact Finset.mem_union_left _
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        · exact Finset.mem_union_right _ h
      have hb12 : b₁ ≠ b₂ := by
        intro e
        have h1 := Finset.card_le_card hBadsub3
        have h2 := Finset.card_union_le ({b₁, b₂} : Finset (Fin 19)) Big
        have h3 : ({b₁, b₂} : Finset (Fin 19)).card ≤ 1 := by
          rw [e, Finset.pair_eq_singleton]
          exact le_of_eq (Finset.card_singleton _)
        omega
      obtain ⟨B, hBeq⟩ := Finset.card_eq_one.mp hBig1
      have hBBig : B ∈ Big := by
        rw [hBeq]
        exact Finset.mem_singleton_self B
      have hBmem := hBBig
      rw [hBigdef, Finset.mem_filter] at hBmem
      obtain ⟨hBDc, hBdeg⟩ := hBmem
      have hBBad : B ∈ Bad := by
        rw [hBaddef, Finset.mem_filter]
        exact ⟨hBDc, Or.inr (Or.inr hBdeg)⟩
      have hpair2 : ({b₁, b₂} : Finset (Fin 19)).card = 2 := Finset.card_pair hb12
      have hBb1 : B ≠ b₁ := by
        intro e
        have hsub : Bad ⊆ ({b₁, b₂} : Finset (Fin 19)) := by
          intro w hw
          rcases Finset.mem_union.mp (hBadsub3 hw) with h | h
          · exact h
          · rw [hBeq, Finset.mem_singleton] at h
            subst h
            rw [e]
            exact Finset.mem_insert_self _ _
        have h1 := Finset.card_le_card hsub
        omega
      have hBb2 : B ≠ b₂ := by
        intro e
        have hsub : Bad ⊆ ({b₁, b₂} : Finset (Fin 19)) := by
          intro w hw
          rcases Finset.mem_union.mp (hBadsub3 hw) with h | h
          · exact h
          · rw [hBeq, Finset.mem_singleton] at h
            subst h
            rw [e]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have h1 := Finset.card_le_card hsub
        omega
      have htripcard : ({b₁, b₂, B} : Finset (Fin 19)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hb12, Ne.symm hBb1]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hBb2]), Finset.card_singleton]
      have hBadEq : Bad = ({b₁, b₂, B} : Finset (Fin 19)) := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact hb1Bad
          · exact hb2Bad
          · exact hBBad
        · rw [htripcard]
          omega
      have hsumBadHubA : ∑ h ∈ HubA, G.degree h + ∑ w ∈ Bad, G.degree w
          = ∑ w ∈ Dᶜ, G.degree w := by
        rw [hHubAdef]
        exact Finset.sum_sdiff hBadsub
      have hsumtrip : G.degree b₁ + G.degree b₂ + G.degree B = 14 := by
        have h1 : ∑ w ∈ ({b₁, b₂, B} : Finset (Fin 19)), G.degree w
            = ∑ w ∈ Bad, G.degree w := by rw [hBadEq]
        rw [Finset.sum_insert (by simp [hb12, Ne.symm hBb1]),
          Finset.sum_insert (by simp [Ne.symm hBb2]), Finset.sum_singleton] at h1
        rw [hSdeg, hH6, hsumDcdeg, hD10] at hsumBadHubA
        omega
      have hdegb1 : G.degree b₁ = 4 := by
        have h1 := hDcdeg b₁ hb1Dc
        have h2 := hDcdeg b₂ hb2Dc
        omega
      have hdegb2 : G.degree b₂ = 4 := by
        have h1 := hDcdeg b₁ hb1Dc
        have h2 := hDcdeg b₂ hb2Dc
        omega
      have hb1noDc : ∀ w : Fin 19, w ∈ Dᶜ → ¬G.Adj b₁ w := by
        intro w hw hadj
        have h0 := hBadDc b₁ hb1Bad
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
        exact h0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hw⟩)
      have hnb1b2 : ¬G.Adj b₁ b₂ := hb1noDc b₂ hb2Dc
      have hb1nc2 : ¬G.Adj b₁ c₂ := by
        intro hadj
        have hm : b₁ ∈ G.neighborFinset c₂ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hb1Dc⟩
        rw [hb2eq, Finset.mem_singleton] at hm
        exact hb12 hm
      have hb2nc1 : ¬G.Adj b₂ c₁ := by
        intro hadj
        have hm : b₂ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hb2Dc⟩
        rw [hb1eq, Finset.mem_singleton] at hm
        exact hb12 hm.symm
      have hnoleaf : ∀ w : Fin 19, w ∈ Bad → ∀ x : Fin 19,
          x ∈ ({L₁, L₂} : Finset (Fin 19)) → ¬G.Adj w x := by
        intro w hw x hx hadj
        have h0 := hBadleaf w hw
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
        exact h0 x (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hx⟩)
      have hpartD : ∀ w : Fin 19, (G.neighborFinset w ∩ path).card
          + (G.neighborFinset w ∩ Iso).card = (G.neighborFinset w ∩ D).card := by
        intro w
        have hdisj : Disjoint (G.neighborFinset w ∩ path) (G.neighborFinset w ∩ Iso) :=
          Finset.disjoint_left.mpr fun u hu hu' =>
            (Finset.disjoint_left.mp hpathIsodisj (Finset.mem_inter.mp hu).2)
              (Finset.mem_inter.mp hu').2
        rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, ← hDeq]
      have hb1path : G.neighborFinset b₁ ∩ path = {c₁} := by
        ext w
        simp only [hpathdef, Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hadj, h | h | h | h⟩
          · rw [h] at hadj
            exact absurd hadj (hnoleaf b₁ hb1Bad L₁ (Finset.mem_insert_self _ _))
          · exact h
          · rw [h] at hadj
            exact absurd hadj hb1nc2
          · rw [h] at hadj
            exact absurd hadj
              (hnoleaf b₁ hb1Bad L₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        · rintro rfl
          exact ⟨hAc1b1.symm, Or.inr (Or.inl rfl)⟩
      have hb2path : G.neighborFinset b₂ ∩ path = {c₂} := by
        ext w
        simp only [hpathdef, Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hadj, h | h | h | h⟩
          · rw [h] at hadj
            exact absurd hadj (hnoleaf b₂ hb2Bad L₁ (Finset.mem_insert_self _ _))
          · rw [h] at hadj
            exact absurd hadj hb2nc1
          · exact h
          · rw [h] at hadj
            exact absurd hadj
              (hnoleaf b₂ hb2Bad L₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        · rintro rfl
          exact ⟨hAc2b2.symm, Or.inr (Or.inr (Or.inl rfl))⟩
      have hb1Dc0 : (G.neighborFinset b₁ ∩ Dᶜ).card = 0 := hBadDc b₁ hb1Bad
      have hb2Dc0 : (G.neighborFinset b₂ ∩ Dᶜ).card = 0 := hBadDc b₂ hb2Bad
      have hb1Iso3 : (G.neighborFinset b₁ ∩ Iso).card = 3 := by
        have h1 := hsplit b₁
        have h2 := hpartD b₁
        have h3 : (G.neighborFinset b₁ ∩ path).card = 1 := by
          rw [hb1path]
          exact Finset.card_singleton c₁
        omega
      have hb2Iso3 : (G.neighborFinset b₂ ∩ Iso).card = 3 := by
        have h1 := hsplit b₂
        have h2 := hpartD b₂
        have h3 : (G.neighborFinset b₂ ∩ path).card = 1 := by
          rw [hb2path]
          exact Finset.card_singleton c₂
        omega
      have hshared : ((G.neighborFinset b₁ ∩ Iso) ∩ (G.neighborFinset b₂ ∩ Iso)).card ≤ 1 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨t, htm, t', htm', htt'⟩ := Finset.one_lt_card.mp hcon
        obtain ⟨htb1, htb2⟩ := Finset.mem_inter.mp htm
        obtain ⟨htN1, htIso⟩ := Finset.mem_inter.mp htb1
        obtain ⟨htN2, -⟩ := Finset.mem_inter.mp htb2
        obtain ⟨ht'b1, ht'b2⟩ := Finset.mem_inter.mp htm'
        obtain ⟨ht'N1, ht'Iso⟩ := Finset.mem_inter.mp ht'b1
        obtain ⟨ht'N2, -⟩ := Finset.mem_inter.mp ht'b2
        have hA1t : G.Adj b₁ t := (G.mem_neighborFinset _ _).mp htN1
        have hA2t : G.Adj b₂ t := (G.mem_neighborFinset _ _).mp htN2
        have hA1t' : G.Adj b₁ t' := (G.mem_neighborFinset _ _).mp ht'N1
        have hA2t' : G.Adj b₂ t' := (G.mem_neighborFinset _ _).mp ht'N2
        have htdeg : G.degree t = 3 := (hIsoprop t htIso).1
        have ht'deg : G.degree t' = 3 := (hIsoprop t' ht'Iso).1
        have hntt' : ¬G.Adj t t' := fun ha => (hIsoprop t htIso).2 t' ha ht'deg
        have htb1ne : t ≠ b₁ := by
          rintro rfl
          omega
        have htb2ne : t ≠ b₂ := by
          rintro rfl
          omega
        have ht'b1ne : t' ≠ b₁ := by
          rintro rfl
          omega
        have ht'b2ne : t' ≠ b₂ := by
          rintro rfl
          omega
        exact hC4 ⟨t, b₁, t', b₂,
          card_four_nineteen t b₁ t' b₂ htb1ne htt' htb2ne (Ne.symm ht'b1ne) hb12 ht'b2ne,
          hA1t.symm, hA1t', hA2t'.symm, hA2t, hntt', hnb1b2, by omega⟩
      have hpriv1 : 2 ≤ ((G.neighborFinset b₁ ∩ Iso) \ (G.neighborFinset b₂ ∩ Iso)).card := by
        have h1 := Finset.card_sdiff_add_card_inter (G.neighborFinset b₁ ∩ Iso)
          (G.neighborFinset b₂ ∩ Iso)
        omega
      have hpriv2 : 2 ≤ ((G.neighborFinset b₂ ∩ Iso) \ (G.neighborFinset b₁ ∩ Iso)).card := by
        have h1 := Finset.card_sdiff_add_card_inter (G.neighborFinset b₂ ∩ Iso)
          (G.neighborFinset b₁ ∩ Iso)
        rw [Finset.inter_comm (G.neighborFinset b₂ ∩ Iso)] at h1
        omega
      obtain ⟨a, ham, b, hbm, hab⟩ := Finset.one_lt_card.mp (by omega :
        1 < ((G.neighborFinset b₁ ∩ Iso) \ (G.neighborFinset b₂ ∩ Iso)).card)
      obtain ⟨c, hcm, d, hdm, hcd⟩ := Finset.one_lt_card.mp (by omega :
        1 < ((G.neighborFinset b₂ ∩ Iso) \ (G.neighborFinset b₁ ∩ Iso)).card)
      obtain ⟨haNI, haN2⟩ := Finset.mem_sdiff.mp ham
      obtain ⟨haN1, haIso⟩ := Finset.mem_inter.mp haNI
      obtain ⟨hbNI, hbN2⟩ := Finset.mem_sdiff.mp hbm
      obtain ⟨hbN1, hbIso⟩ := Finset.mem_inter.mp hbNI
      obtain ⟨hcNI, hcN1⟩ := Finset.mem_sdiff.mp hcm
      obtain ⟨hcN2, hcIso⟩ := Finset.mem_inter.mp hcNI
      obtain ⟨hdNI, hdN1⟩ := Finset.mem_sdiff.mp hdm
      obtain ⟨hdN2, hdIso⟩ := Finset.mem_inter.mp hdNI
      have hA1a : G.Adj b₁ a := (G.mem_neighborFinset _ _).mp haN1
      have hA1b : G.Adj b₁ b := (G.mem_neighborFinset _ _).mp hbN1
      have hA2c : G.Adj b₂ c := (G.mem_neighborFinset _ _).mp hcN2
      have hA2d : G.Adj b₂ d := (G.mem_neighborFinset _ _).mp hdN2
      have hadeg : G.degree a = 3 := (hIsoprop a haIso).1
      have hbdeg : G.degree b = 3 := (hIsoprop b hbIso).1
      have hcdeg : G.degree c = 3 := (hIsoprop c hcIso).1
      have hddeg : G.degree d = 3 := (hIsoprop d hdIso).1
      have hna2 : ¬G.Adj b₂ a := fun ha =>
        haN2 (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha, haIso⟩)
      have hnb2 : ¬G.Adj b₂ b := fun ha =>
        hbN2 (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha, hbIso⟩)
      have hnc1 : ¬G.Adj b₁ c := fun ha =>
        hcN1 (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha, hcIso⟩)
      have hnd1 : ¬G.Adj b₁ d := fun ha =>
        hdN1 (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha, hdIso⟩)
      have hnac : ¬G.Adj a c := fun ha => (hIsoprop a haIso).2 c ha hcdeg
      have hnad : ¬G.Adj a d := fun ha => (hIsoprop a haIso).2 d ha hddeg
      have hnbc : ¬G.Adj b c := fun ha => (hIsoprop b hbIso).2 c ha hcdeg
      have hnbd : ¬G.Adj b d := fun ha => (hIsoprop b hbIso).2 d ha hddeg
      have h1a : b₁ ≠ a := by
        rintro rfl
        omega
      have h1b : b₁ ≠ b := by
        rintro rfl
        omega
      have h1c : b₁ ≠ c := by
        rintro rfl
        omega
      have h1d : b₁ ≠ d := by
        rintro rfl
        omega
      have h2a : b₂ ≠ a := by
        rintro rfl
        omega
      have h2b : b₂ ≠ b := by
        rintro rfl
        omega
      have h2c : b₂ ≠ c := by
        rintro rfl
        omega
      have h2d : b₂ ≠ d := by
        rintro rfl
        omega
      have hac : a ≠ c := by
        rintro rfl
        exact haN2 hcNI
      have had : a ≠ d := by
        rintro rfl
        exact haN2 hdNI
      have hbc : b ≠ c := by
        rintro rfl
        exact hbN2 hcNI
      have hbd : b ≠ d := by
        rintro rfl
        exact hbN2 hdNI
      exact Or.inr (Or.inr (Or.inl ⟨b₁, b₂, a, b, c, d, hdegb1, hdegb2,
        hadeg, hbdeg, hcdeg, hddeg, hA1a.symm, hA1b.symm, hA2c.symm, hA2d.symm,
        hnb1b2, hnc1, hnd1, fun ha => hna2 ha.symm, hnac, hnad,
        fun ha => hnb2 ha.symm, hnbc, hnbd,
        hb12, h1a, h1b, h1c, h1d, h2a, h2b, h2c, h2d, hab, hac, had, hbc, hbd, hcd⟩))

/-- **Safe-hub `P₄` cherry assembly (`n = 19`).**  A degree-`≤ 5` hub `h` avoiding both centres
`c₁, c₂` and at least one leaf (`hcase`), carrying two distinct `M`-isolated twins `t₁, t₂`, gives a
`TwoTwinConfig` against whichever sub-path cherry (`L₁–c₁–c₂` or `c₁–c₂–L₂`) it avoids. -/
theorem safe_hub_two_twin_p4_nineteen (G : SimpleGraph (Fin 19))
    (Iso : Finset (Fin 19)) (L₁ c₁ c₂ L₂ h t₁ t₂ : Fin 19)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3)
    (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hhdeg : G.degree h ≤ 5) (hhc1 : ¬G.Adj h c₁) (hhc2 : ¬G.Adj h c₂)
    (hhne_L1 : h ≠ L₁) (hhne_c1 : h ≠ c₁) (hhne_c2 : h ≠ c₂) (hhne_L2 : h ≠ L₂)
    (hcase : ¬G.Adj h L₁ ∨ ¬G.Adj h L₂)
    (ht1Iso : t₁ ∈ Iso) (ht2Iso : t₂ ∈ Iso) (ht12 : t₁ ≠ t₂)
    (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h) :
    TwoTwinConfig G := by
  rcases hcase with hnL1 | hnL2
  · exact twotwin_assemble_cherry_nineteen G Iso L₁ c₁ c₂ h t₁ t₂ hIsoprop
      hL1deg hc1deg hc2deg hac1L1.symm hc12 hac1L1.symm.ne hc12.ne hL1nc2 hhdeg
      hnL1 hhc1 hhc2 hhne_L1 hhne_c1 hhne_c2 ht1Iso ht2Iso ht12 hAt1h hAt2h
  · exact twotwin_assemble_cherry_nineteen G Iso c₁ c₂ L₂ h t₁ t₂ hIsoprop
      hc1deg hc2deg hL2deg hc12 hac2L2 hc12.ne hac2L2.ne (Ne.symm hL2nc1) hhdeg
      hhc1 hhc2 hnL2 hhne_c1 hhne_c2 hhne_L2 ht1Iso ht2Iso ht12 hAt1h hAt2h

end N19

end ACMax
