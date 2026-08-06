import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.TwoHubHub6Deg5

/-!
# Shared `n = 17` cherry-corner extraction helpers

This file packages the `TwoHubConfig` extraction that is reused across the `P₃`/`P₄` cherry
corners (`TwinCert17CherryP3.lean`, `TwinCert17CherryP4.lean`).  Given two distinct non-adjacent
degree-`4` hubs that share at most one `M`-isolated twin yet each carry `≥ 3` such twins, the
`A`/`B` private-twin extraction (a port of `TwinCert16.lean:1388-1443`) assembles a `TwoHubConfig`.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Cherry-avoiding hub assembly into `TwoTwinConfig` (`n = 17`).**  A degree-`≤ 5` hub `h`
avoiding the cherry `x–y–z` (centre `y`) and carrying two distinct `M`-isolated degree-`3` twins
`t₁, t₂` yields a `TwoTwinConfig`: the twins are non-adjacent to every cherry vertex (they have no
degree-`3` neighbour) and `h` avoids the cherry by hypothesis. -/
theorem twotwin_assemble_cherry_seventeen (G : SimpleGraph (Fin 17))
    (Iso : Finset (Fin 17)) (x y z h t₁ t₂ : Fin 17)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hhdeg : G.degree h ≤ 5) (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z)
    (hhxne : h ≠ x) (hhyne : h ≠ y) (hhzne : h ≠ z)
    (ht1Iso : t₁ ∈ Iso) (ht2Iso : t₂ ∈ Iso) (ht12 : t₁ ≠ t₂)
    (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h) :
    TwoTwinConfig G := by
  classical
  obtain ⟨ht1deg, ht1no⟩ := hIsoprop t₁ ht1Iso
  obtain ⟨ht2deg, ht2no⟩ := hIsoprop t₂ ht2Iso
  have ht1x : ¬G.Adj t₁ x := fun ha => ht1no x ha (by rw [hdegx])
  have ht1y : ¬G.Adj t₁ y := fun ha => ht1no y ha (by rw [hdegy])
  have ht1z : ¬G.Adj t₁ z := fun ha => ht1no z ha (by rw [hdegz])
  have ht2x : ¬G.Adj t₂ x := fun ha => ht2no x ha (by rw [hdegx])
  have ht2y : ¬G.Adj t₂ y := fun ha => ht2no y ha (by rw [hdegy])
  have ht2z : ¬G.Adj t₂ z := fun ha => ht2no z ha (by rw [hdegz])
  have ht1xne : t₁ ≠ x := fun e => ht1no y (e ▸ hxyA) (by rw [hdegy])
  have ht1yne : t₁ ≠ y := fun e => ht1no x (e ▸ hxyA.symm) (by rw [hdegx])
  have ht1zne : t₁ ≠ z := fun e => ht1no y (e ▸ hyzA.symm) (by rw [hdegy])
  have ht2xne : t₂ ≠ x := fun e => ht2no y (e ▸ hxyA) (by rw [hdegy])
  have ht2yne : t₂ ≠ y := fun e => ht2no x (e ▸ hxyA.symm) (by rw [hdegx])
  have ht2zne : t₂ ≠ z := fun e => ht2no y (e ▸ hyzA.symm) (by rw [hdegy])
  exact ⟨t₁, t₂, h, x, y, z, ht1deg, ht2deg, hhdeg, hdegx, hdegy, hdegz,
    hAt1h, hAt2h, hxyA, hyzA,
    ht1x, ht1y, ht1z, ht2x, ht2y, ht2z, hhx, hhy, hhz,
    ht12, ht1xne, ht1yne, ht1zne, ht2xne, ht2yne, ht2zne,
    hhxne, hhyne, hhzne, hxy_ne, hyz_ne, hxz_ne⟩

/-- **Safe-hub `P₄` cherry assembly (`n = 17`).**  A degree-`≤ 5` hub `h` avoiding both centres
`c₁, c₂` and at least one leaf (`hcase`), carrying two distinct `M`-isolated twins `t₁, t₂`, gives a
`TwoTwinConfig` against whichever sub-path cherry (`L₁–c₁–c₂` or `c₁–c₂–L₂`) it avoids. -/
theorem safe_hub_two_twin_p4_seventeen (G : SimpleGraph (Fin 17))
    (Iso : Finset (Fin 17)) (L₁ c₁ c₂ L₂ h t₁ t₂ : Fin 17)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
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
  · exact twotwin_assemble_cherry_seventeen G Iso L₁ c₁ c₂ h t₁ t₂ hIsoprop
      hL1deg hc1deg hc2deg hac1L1.symm hc12 hac1L1.symm.ne hc12.ne hL1nc2 hhdeg
      hnL1 hhc1 hhc2 hhne_L1 hhne_c1 hhne_c2 ht1Iso ht2Iso ht12 hAt1h hAt2h
  · exact twotwin_assemble_cherry_seventeen G Iso c₁ c₂ L₂ h t₁ t₂ hIsoprop
      hc1deg hc2deg hL2deg hc12 hac2L2 hc12.ne hac2L2.ne (Ne.symm hL2nc1) hhdeg
      hhc1 hhc2 hnL2 hhne_c1 hhne_c2 hhne_L2 ht1Iso ht2Iso ht12 hAt1h hAt2h

/-- **Raw cherry-avoiding two-twin assembly (`n = 17`).**  Identical conclusion to
`twotwin_assemble_cherry_seventeen`, but the two twins are supplied through their raw degree-`3`
plus no-degree-`3`-neighbour facts (as produced by `shared_hub_le5_from_count_seventeen`) rather than
membership in an `Iso` set. -/
theorem twotwin_assemble_cherry_raw_seventeen (G : SimpleGraph (Fin 17))
    (x y z h t₁ t₂ : Fin 17)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hhdeg : G.degree h ≤ 5) (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z)
    (hhxne : h ≠ x) (hhyne : h ≠ y) (hhzne : h ≠ z)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3) (ht12 : t₁ ≠ t₂)
    (ht1no : ∀ w : Fin 17, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2no : ∀ w : Fin 17, G.Adj t₂ w → G.degree w ≠ 3)
    (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h) :
    TwoTwinConfig G := by
  classical
  have ht1x : ¬G.Adj t₁ x := fun ha => ht1no x ha (by rw [hdegx])
  have ht1y : ¬G.Adj t₁ y := fun ha => ht1no y ha (by rw [hdegy])
  have ht1z : ¬G.Adj t₁ z := fun ha => ht1no z ha (by rw [hdegz])
  have ht2x : ¬G.Adj t₂ x := fun ha => ht2no x ha (by rw [hdegx])
  have ht2y : ¬G.Adj t₂ y := fun ha => ht2no y ha (by rw [hdegy])
  have ht2z : ¬G.Adj t₂ z := fun ha => ht2no z ha (by rw [hdegz])
  have ht1xne : t₁ ≠ x := fun e => ht1no y (e ▸ hxyA) (by rw [hdegy])
  have ht1yne : t₁ ≠ y := fun e => ht1no x (e ▸ hxyA.symm) (by rw [hdegx])
  have ht1zne : t₁ ≠ z := fun e => ht1no y (e ▸ hyzA.symm) (by rw [hdegy])
  have ht2xne : t₂ ≠ x := fun e => ht2no y (e ▸ hxyA) (by rw [hdegy])
  have ht2yne : t₂ ≠ y := fun e => ht2no x (e ▸ hxyA.symm) (by rw [hdegx])
  have ht2zne : t₂ ≠ z := fun e => ht2no y (e ▸ hyzA.symm) (by rw [hdegy])
  exact ⟨t₁, t₂, h, x, y, z, ht1deg, ht2deg, hhdeg, hdegx, hdegy, hdegz,
    hAt1h, hAt2h, hxyA, hyzA,
    ht1x, ht1y, ht1z, ht2x, ht2y, ht2z, hhx, hhy, hhz,
    ht12, ht1xne, ht1yne, ht1zne, ht2xne, ht2yne, ht2zne,
    hhxne, hhyne, hhzne, hxy_ne, hyz_ne, hxz_ne⟩

/-- **Corrected cherry-avoiding pigeonhole (`n = 17`).**  Given the full hub set `FullHub`, its
degree-`4`/`5` part `Hub5`, the cherry-vertex set `K`, and the `M`-isolated set `Iso`, with the
per-hub degree decomposition `|N h ∩ K| + |N h ∩ Iso| + |N h ∩ FullHub| = deg h` (`h ∈ Hub5`), the
cherry incidence bound `∑_{Hub5}|N ∩ K| ≤ C`, and the internal sum `∑_{FullHub}|N ∩ FullHub| = Int`,
a cherry-avoiding degree-`≤ 5` hub carries two `M`-isolated twins whenever the arithmetic
side-condition `hclose` rules out the "every avoider has `≤ 1` twin" tie.  The tie forces
`a := |avoiders|` to satisfy `|Hub5| ≤ a + C`, `3a ≤ Int` and `6a ≤ a(a−1) + Int` (the last from the
within-avoider edge bound), so any `hclose` discharging those closes the corner. -/
theorem cherry_avoider_pigeonhole_seventeen (G : SimpleGraph (Fin 17))
    (Iso K FullHub Hub5 : Finset (Fin 17)) (C Int : ℕ) (hHub5sub : Hub5 ⊆ FullHub)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hHubdeg4 : ∀ h : Fin 17, h ∈ Hub5 → 4 ≤ G.degree h)
    (hHubdeg5 : ∀ h : Fin 17, h ∈ Hub5 → G.degree h ≤ 5)
    (hdecomp : ∀ h : Fin 17, h ∈ Hub5 → (G.neighborFinset h ∩ K).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ FullHub).card = G.degree h)
    (hCinc : ∑ h ∈ Hub5, (G.neighborFinset h ∩ K).card ≤ C)
    (hIntinc : ∑ h ∈ FullHub, (G.neighborFinset h ∩ FullHub).card = Int)
    (hclose : ∀ a : ℕ, Hub5.card ≤ a + C → 3 * a ≤ Int → 6 * a ≤ a * (a - 1) + Int → False) :
    ∃ h t₁ t₂ : Fin 17, h ∈ Hub5 ∧ (∀ k : Fin 17, k ∈ K → ¬G.Adj h k) ∧
      G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧ G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧
      G.Adj t₁ h ∧ G.Adj t₂ h ∧ (∀ w : Fin 17, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 17, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set HubA : Finset (Fin 17) := Hub5.filter (fun h => (G.neighborFinset h ∩ K).card = 0)
    with hHubAdef
  set HubM : Finset (Fin 17) :=
    Hub5.filter (fun h => ¬(G.neighborFinset h ∩ K).card = 0) with hHubMdef
  have hHubA5 : HubA ⊆ Hub5 := Finset.filter_subset _ _
  have hHubM5 : HubM ⊆ Hub5 := Finset.filter_subset _ _
  have hHubAsub : HubA ⊆ FullHub := fun x hx => hHub5sub (hHubA5 hx)
  have hpart : HubA.card + HubM.card = Hub5.card := by
    rw [hHubAdef, hHubMdef]; exact Finset.card_filter_add_card_filter_not _
  have hAvoidK : ∀ h : Fin 17, h ∈ HubA → (G.neighborFinset h ∩ K).card = 0 := by
    intro h hh; rw [hHubAdef, Finset.mem_filter] at hh; exact hh.2
  -- `|HubM| ≤ C`: each meeter has `≥ 1` cherry-incidence and the total is `≤ C`.
  have hMle : HubM.card ≤ C := by
    have h1 : HubM.card ≤ ∑ h ∈ HubM, (G.neighborFinset h ∩ K).card := by
      rw [Finset.card_eq_sum_ones HubM]
      apply Finset.sum_le_sum
      intro h hh
      rw [hHubMdef, Finset.mem_filter] at hh
      omega
    have h2 : ∑ h ∈ HubM, (G.neighborFinset h ∩ K).card
        ≤ ∑ h ∈ Hub5, (G.neighborFinset h ∩ K).card := Finset.sum_le_sum_of_subset hHubM5
    omega
  -- Strict pigeonhole on the avoiders.
  have hstrict : HubA.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card := by
    by_contra hle
    rw [not_lt] at hle
    set a : ℕ := HubA.card with hadef
    set Rest : Finset (Fin 17) := FullHub \ HubA with hRestdef
    have hcrossIso : ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card
        = ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card := cross_count G Iso HubA
    have hIA : ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card ≤ a := by rw [← hcrossIso]; exact hle
    have hdegA : ∑ h ∈ HubA, G.degree h
        = ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card
          + ∑ h ∈ HubA, (G.neighborFinset h ∩ FullHub).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      have hd := hdecomp h (hHubA5 hh)
      rw [hAvoidK h hh] at hd
      omega
    have hdegAge : 4 * a ≤ ∑ h ∈ HubA, G.degree h := by
      have := Finset.card_nsmul_le_sum HubA (fun h => G.degree h) 4
        (fun h hh => hHubdeg4 h (hHubA5 hh))
      simpa [smul_eq_mul, hadef, Nat.mul_comm] using this
    set IntA : ℕ := ∑ h ∈ HubA, (G.neighborFinset h ∩ FullHub).card with hIntAdef
    have hIntA3a : 3 * a ≤ IntA := by rw [hIntAdef] at *; omega
    have hIntAle : IntA ≤ Int := by
      rw [hIntAdef, ← hIntinc]; exact Finset.sum_le_sum_of_subset hHubAsub
    have h3aInt : 3 * a ≤ Int := le_trans hIntA3a hIntAle
    -- Within-avoider edge bound, splitting `FullHub = HubA ⊔ Rest`.
    have hsplitFull : ∀ h : Fin 17, h ∈ HubA → (G.neighborFinset h ∩ FullHub).card
        = (G.neighborFinset h ∩ HubA).card + (G.neighborFinset h ∩ Rest).card := by
      intro h _
      have hdisj : Disjoint (G.neighborFinset h ∩ HubA) (G.neighborFinset h ∩ Rest) :=
        Finset.disjoint_left.mpr (fun w hw hw' => by
          have h1 := (Finset.mem_inter.mp hw).2
          have h2 := (Finset.mem_inter.mp hw').2
          rw [hRestdef, Finset.mem_sdiff] at h2
          exact h2.2 h1)
      have hun : (G.neighborFinset h ∩ HubA) ∪ (G.neighborFinset h ∩ Rest)
          = G.neighborFinset h ∩ FullHub := by
        rw [← Finset.inter_union_distrib_left, hRestdef, Finset.union_sdiff_of_subset hHubAsub]
      rw [← Finset.card_union_of_disjoint hdisj, hun]
    have hIntAeq : IntA = ∑ h ∈ HubA, (G.neighborFinset h ∩ HubA).card
        + ∑ h ∈ HubA, (G.neighborFinset h ∩ Rest).card := by
      rw [hIntAdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hsplitFull
    have hAAle : ∑ h ∈ HubA, (G.neighborFinset h ∩ HubA).card ≤ a * (a - 1) := by
      have hbound : ∀ h : Fin 17, h ∈ HubA → (G.neighborFinset h ∩ HubA).card ≤ a - 1 := by
        intro h hh
        have hsub : G.neighborFinset h ∩ HubA ⊆ HubA.erase h := by
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          rw [Finset.mem_erase]
          exact ⟨fun e => (G.irrefl (e ▸ hw.1)), hw.2⟩
        calc (G.neighborFinset h ∩ HubA).card ≤ (HubA.erase h).card := Finset.card_le_card hsub
          _ = a - 1 := by rw [Finset.card_erase_of_mem hh, hadef]
      calc ∑ h ∈ HubA, (G.neighborFinset h ∩ HubA).card ≤ ∑ _h ∈ HubA, (a - 1) :=
            Finset.sum_le_sum hbound
        _ = a * (a - 1) := by rw [Finset.sum_const, smul_eq_mul, hadef]
    have hAMcross : ∑ h ∈ HubA, (G.neighborFinset h ∩ Rest).card
        = ∑ h ∈ Rest, (G.neighborFinset h ∩ HubA).card := cross_count G HubA Rest
    have hAMle : ∑ h ∈ HubA, (G.neighborFinset h ∩ Rest).card ≤ Int - IntA := by
      rw [hAMcross]
      have hb1 : ∑ h ∈ Rest, (G.neighborFinset h ∩ HubA).card
          ≤ ∑ h ∈ Rest, (G.neighborFinset h ∩ FullHub).card :=
        Finset.sum_le_sum (fun h _ => Finset.card_le_card
          (fun w hw => Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hw).1, hHubAsub (Finset.mem_inter.mp hw).2⟩))
      have hsum : ∑ h ∈ Rest, (G.neighborFinset h ∩ FullHub).card
          + ∑ h ∈ HubA, (G.neighborFinset h ∩ FullHub).card = Int := by
        rw [hRestdef, ← hIntinc]; exact Finset.sum_sdiff hHubAsub
      rw [hIntAdef]; omega
    have h2IntA : 2 * IntA ≤ a * (a - 1) + Int := by
      have : IntA ≤ a * (a - 1) + (Int - IntA) := by rw [hIntAeq]; omega
      omega
    have h6a : 6 * a ≤ a * (a - 1) + Int := by omega
    have hHa : Hub5.card ≤ a + C := by rw [← hpart, hadef]; omega
    exact hclose a hHa h3aInt h6a
  -- Extract the shared avoider hub with two twins.
  obtain ⟨h, t₁, t₂, hhHubA, _hd5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1no, ht2no⟩ :=
    shared_hub_le5_from_count_seventeen G Iso HubA hIsoprop
      (fun h hh => hHubdeg5 h (hHubA5 hh)) hstrict
  refine ⟨h, t₁, t₂, hHubA5 hhHubA, ?_, hHubdeg5 h (hHubA5 hhHubA), ht12, ht1deg, ht2deg,
    hAt1h, hAt2h, ht1no, ht2no⟩
  intro k hk hadj
  have h0 := hAvoidK h hhHubA
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
  exact h0 k (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h k).mpr hadj, hk⟩)

/-- **`P₃`-cherry two-twin wrapper (`n = 17`).**  Packages the full hub-incidence counting for the
`e(M) = 2` (`P₃` cherry `x–y–z`) regime and feeds it to `cherry_avoider_pigeonhole_seventeen`: with
`FullHub = Dᶜ`, the deg-`≤ 5` part `Hub5`, cherry incidence `≤ 5` and internal sum `64 − 6|D|`, the
caller-supplied `hclose` produces a cherry-avoiding degree-`≤ 5` hub with two `M`-isolated twins,
yielding a `TwoTwinConfig`. -/
theorem p3_cherry_two_twin_seventeen (G : SimpleGraph (Fin 17)) (D Iso Hub5 : Finset (Fin 17))
    (x y z : Fin 17) (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 17, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 17)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hHub5sub : Hub5 ⊆ Dᶜ) (hHub5deg5 : ∀ h : Fin 17, h ∈ Hub5 → G.degree h ≤ 5)
    (hDle : D.card ≤ 10)
    (hclose : ∀ a : ℕ, Hub5.card ≤ a + 5 → 3 * a ≤ 64 - 6 * D.card →
      6 * a ≤ a * (a - 1) + (64 - 6 * D.card) → False) :
    TwoTwinConfig G := by
  classical
  have hdegD : ∀ v : Fin 17, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hxD : x ∈ D := (hmemD x).mpr hdegx
  have hyD : y ∈ D := (hmemD y).mpr hdegy
  have hzD : z ∈ D := (hmemD z).mpr hdegz
  -- `N x ∩ D = {y}` and `N z ∩ D = {y}`.
  have hNxD : G.neighborFinset x ∩ D = ({y} : Finset (Fin 17)) := by
    apply Finset.Subset.antisymm
    · intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      rcases hcov x w hxD hw.2 hw.1 with e | e
      · exact absurd e hxy_ne
      · rw [Finset.mem_singleton, e]
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst w
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hxyA, hyD⟩
  have hNzD : G.neighborFinset z ∩ D = ({y} : Finset (Fin 17)) := by
    apply Finset.Subset.antisymm
    · intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      rcases hcov z w hzD hw.2 hw.1 with e | e
      · exact absurd e hyz_ne.symm
      · rw [Finset.mem_singleton, e]
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst w
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z y).mpr hyzA.symm, hyD⟩
  have hIsoD : ∀ v : Fin 17, v ∈ Iso → v ∈ D := fun v hv => (hmemD v).mpr (hIsoprop v hv).1
  have hxIso : x ∉ Iso := fun h => (hIsoprop x h).2 y hxyA (by rw [hdegy])
  have hyIso : y ∉ Iso := fun h => (hIsoprop y h).2 x hxyA.symm (by rw [hdegx])
  have hzIso : z ∉ Iso := fun h => (hIsoprop z h).2 y hyzA.symm (by rw [hdegy])
  -- `{x,y,z} ∪ Iso = D`.
  have hKIso : ({x, y, z} : Finset (Fin 17)) ∪ Iso = D := by
    apply Finset.Subset.antisymm
    · intro w hw
      rw [Finset.mem_union] at hw
      rcases hw with hw | hw
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      · exact hIsoD w hw
    · intro w hw
      by_cases hwx : w = x
      · subst hwx; simp
      by_cases hwy : w = y
      · subst hwy; simp
      by_cases hwz : w = z
      · subst hwz; simp
      exact Finset.mem_union_right _ (hisochar w hw hwx hwy hwz)
  -- `{x,y,z}` and `Iso` are disjoint.
  have hKIsodisj : Disjoint ({x, y, z} : Finset (Fin 17)) Iso :=
    Finset.disjoint_left.mpr (fun w hw hw' => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxIso hw'
      · exact hyIso hw'
      · exact hzIso hw')
  -- Per-vertex `D`/`Dᶜ` degree split.
  have hsplit : ∀ v : Fin 17,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha' =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp ha').2) (Finset.mem_inter.mp ha).2)
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  -- `∑_{v∈D} |N v ∩ D| = 4`.
  have hother0 : ∀ v : Fin 17, v ∈ D → v ∉ ({x, y, z} : Finset (Fin 17)) →
      (G.neighborFinset v ∩ D).card = 0 := by
    intro v hvD hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    have hvIso := hisochar v hvD hv.1 hv.2.1 hv.2.2
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    exact (hIsoprop v hvIso).2 w hw.1 ((hmemD w).mp hw.2)
  have hxyz_sub : ({x, y, z} : Finset (Fin 17)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hsumD_in : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 4 := by
    rw [← Finset.sum_subset hxyz_sub (fun v hv hnv => hother0 v hv hnv),
      Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
      Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton,
      hNxD, hNyD, hNzD, Finset.card_pair hxz_ne, Finset.card_singleton]
    rfl
  -- Degree sums.
  have hsum60 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w + 3 * D.card = 60 := by
    have hh : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 60 := by
      rw [Finset.sum_add_sum_compl]; exact hsum60
    rw [hsumDdeg] at hh; omega
  -- Internal sum `∑_{Dᶜ}|N ∩ Dᶜ| = 64 − 6|D|`.
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
      = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count G D Dᶜ
  have hDcD : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card + 4 = 3 * D.card := by
    have hcongD : ∑ v ∈ D, ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
        = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hsplit v)
    rw [Finset.sum_add_distrib, hsumD_in, hsumDdeg] at hcongD
    omega
  have hIntinc : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 64 - 6 * D.card := by
    have hcongDc : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card)
        = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hsplit w)
    rw [Finset.sum_add_distrib] at hcongDc
    omega
  -- Cherry incidence `∑_{Hub5}|N ∩ {x,y,z}| ≤ 5`.
  have hKcardx : (G.neighborFinset x ∩ Dᶜ).card = 2 := by
    have := hsplit x; rw [hNxD, hdegx, Finset.card_singleton] at this; omega
  have hKcardy : (G.neighborFinset y ∩ Dᶜ).card = 1 := by
    have := hsplit y; rw [hNyD, hdegy, Finset.card_pair hxz_ne] at this; omega
  have hKcardz : (G.neighborFinset z ∩ Dᶜ).card = 2 := by
    have := hsplit z; rw [hNzD, hdegz, Finset.card_singleton] at this; omega
  have hCfull : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ ({x, y, z} : Finset (Fin 17))).card = 5 := by
    have hcc := cross_count G Dᶜ ({x, y, z} : Finset (Fin 17))
    rw [hcc, Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
      Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton, hKcardx, hKcardy, hKcardz]
    rfl
  have hCinc : ∑ h ∈ Hub5, (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 17))).card ≤ 5 := by
    rw [← hCfull]; exact Finset.sum_le_sum_of_subset hHub5sub
  -- Per-hub degree decomposition.
  have hdecomp : ∀ h : Fin 17, h ∈ Hub5 → (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 17))).card
      + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h := by
    intro h _
    have hd1 : (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 17))).card
        + (G.neighborFinset h ∩ Iso).card = (G.neighborFinset h ∩ D).card := by
      have hdisj : Disjoint (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 17)))
          (G.neighborFinset h ∩ Iso) :=
        Finset.disjoint_left.mpr (fun w hw hw' =>
          (Finset.disjoint_left.mp hKIsodisj (Finset.mem_inter.mp hw).2)
            (Finset.mem_inter.mp hw').2)
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, hKIso]
    have hd2 := hsplit h
    omega
  have hHubdeg4 : ∀ h : Fin 17, h ∈ Hub5 → 4 ≤ G.degree h := by
    intro h hh
    have hhDc : h ∈ Dᶜ := hHub5sub hh
    rw [Finset.mem_compl, hmemD] at hhDc; have := h3 h; omega
  obtain ⟨h, t₁, t₂, hhHub5, havoid, hhdeg5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1no, ht2no⟩ :=
    cherry_avoider_pigeonhole_seventeen G Iso ({x, y, z} : Finset (Fin 17)) Dᶜ Hub5 5
      (64 - 6 * D.card) hHub5sub hIsoprop hHubdeg4 hHub5deg5 hdecomp hCinc hIntinc hclose
  have hhDc : h ∈ Dᶜ := hHub5sub hhHub5
  have hhx : ¬G.Adj h x := havoid x (by simp)
  have hhy : ¬G.Adj h y := havoid y (by simp)
  have hhz : ¬G.Adj h z := havoid z (by simp)
  have hhxne : h ≠ x := fun e => (Finset.mem_compl.mp hhDc) (e ▸ hxD)
  have hhyne : h ≠ y := fun e => (Finset.mem_compl.mp hhDc) (e ▸ hyD)
  have hhzne : h ≠ z := fun e => (Finset.mem_compl.mp hhDc) (e ▸ hzD)
  exact twotwin_assemble_cherry_raw_seventeen G x y z h t₁ t₂ hdegx hdegy hdegz hxyA hyzA
    hxy_ne hyz_ne hxz_ne hhdeg5 hhx hhy hhz hhxne hhyne hhzne ht1deg ht2deg ht12 ht1no ht2no
    hAt1h hAt2h

end N17

end ACMax
