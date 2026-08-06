import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.CherryCore

/-!
# `n = 18`, `e(M) = 3` (`s = 6`), `P₄`-cherry corner: the `{c₁,c₂}`-avoider count

The genuinely-new counting leaf for the `P₄`-cherry corners (`TwinCert18CherryP4.lean`).  Using the
two-vertex cherry `K = {c₁,c₂}` (each centre meets exactly one hub) the avoider count closes, with
the leak through the two leaves `L₁,L₂` bounded by `∑_{w∈Dᶜ}|N w ∩ {L₁,L₂}| ≤ 4` and absorbed by the
strict pigeonhole margin (`3·|HubA| > Int + 4` at `|D| ∈ {9,10,11}`).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **`{c₁,c₂}`-avoider with two `M`-isolated twins (`n = 18`, `P₄` corner).**  For the path
`L₁–c₁–c₂–L₂` residual with `|D| ∈ {9,10,11}`, there is a degree-`≤ 5` hub `h` avoiding both centres
`c₁, c₂` and carrying two distinct `M`-isolated twins `t₁, t₂ ∈ Iso`. -/
theorem p4_c1c2_avoider_two_twin_eighteen (G : SimpleGraph (Fin 18))
    (hm : G.edgeFinset.card = 32) (h3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (L₁ c₁ c₂ L₂ : Fin 18) (D Iso : Finset (Fin 18))
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11) :
    ∃ h t₁ t₂ : Fin 18, h ∈ Dᶜ ∧ G.degree h ≤ 5 ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h c₂ ∧
      t₁ ≠ t₂ ∧ t₁ ∈ Iso ∧ t₂ ∈ Iso ∧ G.Adj h t₁ ∧ G.Adj h t₂ := by
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
  have hIsoD : ∀ v : Fin 18, v ∈ Iso → v ∈ D := fun v hv => (hmemD v).mpr (hIsoprop v hv).1
  -- Path vertices are not `M`-isolated.
  have hc1Iso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 c₂ hc12 (by rw [hc2deg])
  have hc2Iso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm (by rw [hc1deg])
  have hL1Iso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm (by rw [hc1deg])
  have hL2Iso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm (by rw [hc2deg])
  -- Per-vertex `D`/`Dᶜ` degree split.
  have hsplit : ∀ v : Fin 18,
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
  have hsum60 : ∑ v : Fin 18, G.degree v = 64 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 64 - 3 * D.card := by
    have hh : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 64 := by
      rw [Finset.sum_add_sum_compl]; exact hsum60
    omega
  have hDc_card : Dᶜ.card = 18 - D.card := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  have hDcdeg : ∀ w : Fin 18, w ∈ Dᶜ → 4 ≤ G.degree w := by
    intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
  -- `D = {L₁,c₁,c₂,L₂} ∪ Iso`.
  set path : Finset (Fin 18) := {L₁, c₁, c₂, L₂} with hpathdef
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
  have hIso0 : ∀ v : Fin 18, v ∈ Iso → (G.neighborFinset v ∩ D).card = 0 := by
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
  -- Internal sum `∑_{Dᶜ}|N w ∩ Dᶜ| = 70 − 6|D|`.
  set Int : ℕ := 70 - 6 * D.card with hIntdef
  have hcrossDDc : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
      = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count G D Dᶜ
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
  set Bad : Finset (Fin 18) :=
    Dᶜ.filter (fun w => G.Adj w c₁ ∨ G.Adj w c₂ ∨ 6 ≤ G.degree w) with hBaddef
  set HubA : Finset (Fin 18) := Dᶜ \ Bad with hHubAdef
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
  set Big : Finset (Fin 18) := Dᶜ.filter (fun w => 6 ≤ G.degree w) with hBigdef
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
    have hsplitB : ∑ w ∈ Dᶜ \ Big, G.degree w + ∑ w ∈ Big, G.degree w = 64 - 3 * D.card := by
      rw [Finset.sum_sdiff hBigsub]; exact hsumDcdeg
    have hcardB : (Dᶜ \ Big).card + Big.card = 18 - D.card := by
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
  have hHubA_props : ∀ h : Fin 18, h ∈ HubA →
      h ∈ Dᶜ ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h c₂ ∧ G.degree h ≤ 5 := by
    intro h hh
    rw [hHubAdef, Finset.mem_sdiff] at hh
    obtain ⟨hhDc, hhnBad⟩ := hh
    refine ⟨hhDc, ?_, ?_, ?_⟩
    · intro ha; exact hhnBad (by rw [hBaddef, Finset.mem_filter]; exact ⟨hhDc, Or.inl ha⟩)
    · intro ha; exact hhnBad (by rw [hBaddef, Finset.mem_filter]; exact ⟨hhDc, Or.inr (Or.inl ha)⟩)
    · by_contra hc
      exact hhnBad (by rw [hBaddef, Finset.mem_filter]; exact ⟨hhDc, Or.inr (Or.inr (by omega))⟩)
  have hHubAdeg5 : ∀ h : Fin 18, h ∈ HubA → G.degree h ≤ 5 := fun h hh => (hHubA_props h hh).2.2.2
  have hHubAsub : HubA ⊆ Dᶜ := by rw [hHubAdef]; exact Finset.sdiff_subset
  -- Per-hub Iso count for `HubA` hubs.
  have hHubA_iso : ∀ h : Fin 18, h ∈ HubA →
      (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card
        + (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 18))).card = G.degree h := by
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
        G.neighborFinset h ∩ path = G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 18)) := by
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
      + ∑ h ∈ HubA, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 18))).card
      = ∑ h ∈ HubA, G.degree h := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hHubA_iso
  have hdegAge : 4 * HubA.card ≤ ∑ h ∈ HubA, G.degree h := by
    have := Finset.card_nsmul_le_sum HubA (fun h => G.degree h) 4
      (fun h hh => hDcdeg h (hHubAsub hh))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hDcsumle : ∑ h ∈ HubA, (G.neighborFinset h ∩ Dᶜ).card ≤ Int := by
    rw [← hIntval]; exact Finset.sum_le_sum_of_subset hHubAsub
  have hleakle : ∑ h ∈ HubA, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 18))).card ≤ 4 := by
    have hfull : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 18))).card = 4 := by
      rw [cross_count G Dᶜ ({L₁, L₂} : Finset (Fin 18)),
        Finset.sum_insert (by simp [hL1L2]), Finset.sum_singleton, hL1Dc, hL2Dc]
    calc ∑ h ∈ HubA, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 18))).card
        ≤ ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ ({L₁, L₂} : Finset (Fin 18))).card :=
          Finset.sum_le_sum_of_subset hHubAsub
      _ = 4 := hfull
  have hstrict : HubA.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card := by
    have hcross : ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card
        = ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card := cross_count G Iso HubA
    rw [hcross]
    have hkey : 3 * HubA.card > Int + 4 := by
      have hHubAge : Dᶜ.card ≤ HubA.card + 2 + Big.card := by omega
      rw [hDc_card] at hHubAge
      omega
    omega
  obtain ⟨h, t₁, t₂, hhHubA, _hd5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1no, ht2no⟩ :=
    shared_hub_le5_from_count_eighteen G Iso HubA hIsoprop hHubAdeg5 hstrict
  obtain ⟨hhDc, hhnc1, hhnc2, hhdeg5⟩ := hHubA_props h hhHubA
  have htwinIso : ∀ t : Fin 18, G.degree t = 3 → (∀ w : Fin 18, G.Adj t w → G.degree w ≠ 3) →
      t ∈ Iso := by
    intro t htdeg htno
    have htD : t ∈ D := (hmemD t).mpr htdeg
    apply hisochar t htD
    · intro e; subst e; exact htno c₁ hac1L1.symm hc1deg
    · intro e; subst e; exact htno c₂ hc12 hc2deg
    · intro e; subst e; exact htno c₁ hc12.symm hc1deg
    · intro e; subst e; exact htno c₂ hac2L2.symm hc2deg
  exact ⟨h, t₁, t₂, hhDc, hhdeg5, hhnc1, hhnc2, ht12,
    htwinIso t₁ ht1deg ht1no, htwinIso t₂ ht2deg ht2no, hAt1h.symm, hAt2h.symm⟩

/-- **Safe-hub `P₄` cherry assembly (`n = 18`).**  A degree-`≤ 5` hub `h` avoiding both centres
`c₁, c₂` and at least one leaf (`hcase`), carrying two distinct `M`-isolated twins `t₁, t₂`, gives a
`TwoTwinConfig` against whichever sub-path cherry (`L₁–c₁–c₂` or `c₁–c₂–L₂`) it avoids. -/
theorem safe_hub_two_twin_p4_eighteen (G : SimpleGraph (Fin 18))
    (Iso : Finset (Fin 18)) (L₁ c₁ c₂ L₂ h t₁ t₂ : Fin 18)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
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
  · exact twotwin_assemble_cherry_eighteen G Iso L₁ c₁ c₂ h t₁ t₂ hIsoprop
      hL1deg hc1deg hc2deg hac1L1.symm hc12 hac1L1.symm.ne hc12.ne hL1nc2 hhdeg
      hnL1 hhc1 hhc2 hhne_L1 hhne_c1 hhne_c2 ht1Iso ht2Iso ht12 hAt1h hAt2h
  · exact twotwin_assemble_cherry_eighteen G Iso c₁ c₂ L₂ h t₁ t₂ hIsoprop
      hc1deg hc2deg hL2deg hc12 hac2L2 hc12.ne hac2L2.ne (Ne.symm hL2nc1) hhdeg
      hhc1 hhc2 hnL2 hhne_c1 hhne_c2 hhne_L2 ht1Iso ht2Iso ht12 hAt1h hAt2h

end N18

end ACMax
