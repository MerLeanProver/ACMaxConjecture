import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.TwoHubHub6Deg5

/-!
# Shared `n = 20` cherry-corner extraction helpers

This file packages the `TwoTwinConfig`/`TwoHubConfig`/`HubTriangleConfig` extraction reused across
the `e(M) = 2` (`P₃` cherry `x–y–z`, centre `y`) alignment corners
(`TwinCert20CherryP3.lean`).  Ported from the axiom-clean `n = 19` development
(`TwinCert19CherryCore.lean`); the `n = 20` deltas are `34 → 36` edges, `68 → 72` total degree, the
internal sum `72 − 6|D| → 76 − 6|D|`, and `cross_count_nineteen → cross_count_twenty`.

The cherry-avoiding pigeonhole here additionally returns a *dense-avoider triangle* in the tie
branch (the `n = 20` `|D| = 10` corner needs it: there the arithmetic does not exclude the
four-avoider tie, but the within-avoider edge bound forces `≥ 5` edges on the four avoiders, hence a
hub triangle → `HubTriangleConfig`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Cherry-avoiding hub assembly into `TwoTwinConfig` (`n = 20`).**  A degree-`≤ 5` hub `h`
avoiding the cherry `x–y–z` (centre `y`) and carrying two distinct `M`-isolated degree-`3` twins
`t₁, t₂` yields a `TwoTwinConfig`. -/
theorem twotwin_assemble_cherry_twenty (G : SimpleGraph (Fin 20))
    (Iso : Finset (Fin 20)) (x y z h t₁ t₂ : Fin 20)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
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

/-- **Raw cherry-avoiding two-twin assembly (`n = 20`).**  Identical conclusion to
`twotwin_assemble_cherry_twenty`, but the two twins are supplied through their raw degree-`3`
plus no-degree-`3`-neighbour facts rather than membership in an `Iso` set. -/
theorem twotwin_assemble_cherry_raw_twenty (G : SimpleGraph (Fin 20))
    (x y z h t₁ t₂ : Fin 20)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hhdeg : G.degree h ≤ 5) (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z)
    (hhxne : h ≠ x) (hhyne : h ≠ y) (hhzne : h ≠ z)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3) (ht12 : t₁ ≠ t₂)
    (ht1no : ∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2no : ∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3)
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

/-- **Cherry-avoiding dichotomy (`n = 20`).**  Same counting hypotheses as
`cherry_avoider_pigeonhole_twenty`, but with no arithmetic side condition: either a cherry-avoiding
degree-`≤ 5` hub carries two `M`-isolated twins (the `TwoTwinConfig` route), or the avoider set `S`
is dense, satisfying `Hub5.card ≤ S.card + C`, `3·|S| ≤ Int`, and the within-avoider edge bound
`6·|S| ≤ ∑_{h∈S}|N h ∩ S| + Int` (the route to a hub triangle). -/
theorem cherry_avoider_or_dense_twenty (G : SimpleGraph (Fin 20))
    (Iso K FullHub Hub5 : Finset (Fin 20)) (C Int : ℕ) (hHub5sub : Hub5 ⊆ FullHub)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hHubdeg4 : ∀ h : Fin 20, h ∈ Hub5 → 4 ≤ G.degree h)
    (hHubdeg5 : ∀ h : Fin 20, h ∈ Hub5 → G.degree h ≤ 5)
    (hdecomp : ∀ h : Fin 20, h ∈ Hub5 → (G.neighborFinset h ∩ K).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ FullHub).card = G.degree h)
    (hCinc : ∑ h ∈ Hub5, (G.neighborFinset h ∩ K).card ≤ C)
    (hIntinc : ∑ h ∈ FullHub, (G.neighborFinset h ∩ FullHub).card = Int) :
    (∃ h t₁ t₂ : Fin 20, h ∈ Hub5 ∧ (∀ k : Fin 20, k ∈ K → ¬G.Adj h k) ∧
        G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧ G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧
        G.Adj t₁ h ∧ G.Adj t₂ h ∧ (∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3) ∧
        (∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3)) ∨
      (∃ S : Finset (Fin 20), S ⊆ Hub5 ∧ (∀ h : Fin 20, h ∈ S → ∀ k : Fin 20, k ∈ K → ¬G.Adj h k) ∧
        Hub5.card ≤ S.card + C ∧ 3 * S.card ≤ Int ∧
        6 * S.card ≤ (∑ h ∈ S, (G.neighborFinset h ∩ S).card) + Int ∧
        (∀ h : Fin 20, h ∈ Hub5 → (∀ k : Fin 20, k ∈ K → ¬G.Adj h k) → h ∈ S)) := by
  classical
  set HubA : Finset (Fin 20) := Hub5.filter (fun h => (G.neighborFinset h ∩ K).card = 0)
    with hHubAdef
  have hHubA5 : HubA ⊆ Hub5 := Finset.filter_subset _ _
  have hHubAsub : HubA ⊆ FullHub := fun x hx => hHub5sub (hHubA5 hx)
  have hpart : HubA.card + (Hub5.filter (fun h => ¬(G.neighborFinset h ∩ K).card = 0)).card
      = Hub5.card := by rw [hHubAdef]; exact Finset.card_filter_add_card_filter_not _
  have hAvoidK : ∀ h : Fin 20, h ∈ HubA → (G.neighborFinset h ∩ K).card = 0 := by
    intro h hh; rw [hHubAdef, Finset.mem_filter] at hh; exact hh.2
  have hAvoid : ∀ h : Fin 20, h ∈ HubA → ∀ k : Fin 20, k ∈ K → ¬G.Adj h k := by
    intro h hh k hk hadj
    have h0 := hAvoidK h hh
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
    exact h0 k (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h k).mpr hadj, hk⟩)
  have hMle : (Hub5.filter (fun h => ¬(G.neighborFinset h ∩ K).card = 0)).card ≤ C := by
    have h1 : (Hub5.filter (fun h => ¬(G.neighborFinset h ∩ K).card = 0)).card
        ≤ ∑ h ∈ Hub5.filter (fun h => ¬(G.neighborFinset h ∩ K).card = 0),
            (G.neighborFinset h ∩ K).card := by
      rw [Finset.card_eq_sum_ones _]
      apply Finset.sum_le_sum
      intro h hh
      rw [Finset.mem_filter] at hh
      omega
    have h2 : ∑ h ∈ Hub5.filter (fun h => ¬(G.neighborFinset h ∩ K).card = 0),
          (G.neighborFinset h ∩ K).card
        ≤ ∑ h ∈ Hub5, (G.neighborFinset h ∩ K).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  by_cases hstrict : HubA.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card
  · obtain ⟨h, t₁, t₂, hhHubA, _hd5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1no, ht2no⟩ :=
      shared_hub_le5_from_count_twenty G Iso HubA hIsoprop
        (fun h hh => hHubdeg5 h (hHubA5 hh)) hstrict
    exact Or.inl ⟨h, t₁, t₂, hHubA5 hhHubA, hAvoid h hhHubA, hHubdeg5 h (hHubA5 hhHubA),
      ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1no, ht2no⟩
  · rw [not_lt] at hstrict
    have hmax : ∀ h : Fin 20, h ∈ Hub5 → (∀ k : Fin 20, k ∈ K → ¬G.Adj h k) → h ∈ HubA := by
      intro h hh hnoK
      rw [hHubAdef, Finset.mem_filter]
      refine ⟨hh, ?_⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact hnoK w hw.2 hw.1
    refine Or.inr ⟨HubA, hHubA5, hAvoid, by omega, ?_, ?_, hmax⟩
    · set a : ℕ := HubA.card with hadef
      have hcrossIso : ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card
          = ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso HubA
      have hIA : ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card ≤ a := by
        rw [← hcrossIso]; exact hstrict
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
      have hIntAle : ∑ h ∈ HubA, (G.neighborFinset h ∩ FullHub).card ≤ Int := by
        rw [← hIntinc]; exact Finset.sum_le_sum_of_subset hHubAsub
      omega
    · -- `6·a ≤ ∑_{HubA}|N ∩ HubA| + Int`.
      set a : ℕ := HubA.card with hadef
      set Rest : Finset (Fin 20) := FullHub \ HubA with hRestdef
      set IntA : ℕ := ∑ h ∈ HubA, (G.neighborFinset h ∩ FullHub).card with hIntAdef
      have hcrossIso : ∑ v ∈ Iso, (G.neighborFinset v ∩ HubA).card
          = ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso HubA
      have hIA : ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card ≤ a := by
        rw [← hcrossIso]; exact hstrict
      have hdegA : ∑ h ∈ HubA, G.degree h
          = ∑ h ∈ HubA, (G.neighborFinset h ∩ Iso).card + IntA := by
        rw [hIntAdef, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro h hh
        have hd := hdecomp h (hHubA5 hh)
        rw [hAvoidK h hh] at hd
        omega
      have hdegAge : 4 * a ≤ ∑ h ∈ HubA, G.degree h := by
        have := Finset.card_nsmul_le_sum HubA (fun h => G.degree h) 4
          (fun h hh => hHubdeg4 h (hHubA5 hh))
        simpa [smul_eq_mul, hadef, Nat.mul_comm] using this
      have hIntA3a : 3 * a ≤ IntA := by omega
      have hsplitFull : ∀ h : Fin 20, h ∈ HubA → (G.neighborFinset h ∩ FullHub).card
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
      have hAMcross : ∑ h ∈ HubA, (G.neighborFinset h ∩ Rest).card
          = ∑ h ∈ Rest, (G.neighborFinset h ∩ HubA).card := cross_count_twenty G HubA Rest
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
      have hIntAle : IntA ≤ Int := by
        rw [hIntAdef, ← hIntinc]; exact Finset.sum_le_sum_of_subset hHubAsub
      omega

/-- **`P₃`-cherry alignment dichotomy (`n = 20`).**  Packages the hub-incidence counting for the
`e(M) = 2` (`P₃` cherry `x–y–z`) regime and feeds it to `cherry_avoider_or_dense_twenty`: either a
cherry-avoiding degree-`≤ 5` hub carries two `M`-isolated twins (`TwoTwinConfig`), or the
cherry-avoiding hub set `S ⊆ Hub5` is dense, with `Hub5.card ≤ |S| + 5`, `3|S| ≤ 76 − 6|D|` and the
within-avoider edge bound `6|S| ≤ ∑_{h∈S}|N h ∩ S| + (76 − 6|D|)`.  The dense branch routes (for
`|D| = 10`) to a hub triangle, and is arithmetically impossible for `|D| ∈ {11, 12}`. -/
theorem p3_cherry_dichotomy_twenty (G : SimpleGraph (Fin 20)) (D Iso Hub5 : Finset (Fin 20))
    (x y z : Fin 20) (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 20)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hHub5sub : Hub5 ⊆ Dᶜ) (hHub5deg5 : ∀ h : Fin 20, h ∈ Hub5 → G.degree h ≤ 5) :
    TwoTwinConfig G ∨
      (∃ S : Finset (Fin 20), S ⊆ Hub5 ∧
        (∀ h : Fin 20, h ∈ S → ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z) ∧
        Hub5.card ≤ S.card + 5 ∧ 3 * S.card ≤ 76 - 6 * D.card ∧
        6 * S.card ≤ (∑ h ∈ S, (G.neighborFinset h ∩ S).card) + (76 - 6 * D.card) ∧
        (∀ h : Fin 20, h ∈ Hub5 → ¬G.Adj h x → ¬G.Adj h y → ¬G.Adj h z → h ∈ S)) := by
  classical
  have hdegD : ∀ v : Fin 20, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hxD : x ∈ D := (hmemD x).mpr hdegx
  have hyD : y ∈ D := (hmemD y).mpr hdegy
  have hzD : z ∈ D := (hmemD z).mpr hdegz
  have hNxD : G.neighborFinset x ∩ D = ({y} : Finset (Fin 20)) := by
    apply Finset.Subset.antisymm
    · intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      rcases hcov x w hxD hw.2 hw.1 with e | e
      · exact absurd e hxy_ne
      · rw [Finset.mem_singleton, e]
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst w
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hxyA, hyD⟩
  have hNzD : G.neighborFinset z ∩ D = ({y} : Finset (Fin 20)) := by
    apply Finset.Subset.antisymm
    · intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      rcases hcov z w hzD hw.2 hw.1 with e | e
      · exact absurd e hyz_ne.symm
      · rw [Finset.mem_singleton, e]
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst w
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z y).mpr hyzA.symm, hyD⟩
  have hIsoD : ∀ v : Fin 20, v ∈ Iso → v ∈ D := fun v hv => (hmemD v).mpr (hIsoprop v hv).1
  have hxIso : x ∉ Iso := fun h => (hIsoprop x h).2 y hxyA (by rw [hdegy])
  have hyIso : y ∉ Iso := fun h => (hIsoprop y h).2 x hxyA.symm (by rw [hdegx])
  have hzIso : z ∉ Iso := fun h => (hIsoprop z h).2 y hyzA.symm (by rw [hdegy])
  have hKIso : ({x, y, z} : Finset (Fin 20)) ∪ Iso = D := by
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
  have hKIsodisj : Disjoint ({x, y, z} : Finset (Fin 20)) Iso :=
    Finset.disjoint_left.mpr (fun w hw hw' => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxIso hw'
      · exact hyIso hw'
      · exact hzIso hw')
  have hsplit : ∀ v : Fin 20,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha' =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp ha').2) (Finset.mem_inter.mp ha).2)
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  have hother0 : ∀ v : Fin 20, v ∈ D → v ∉ ({x, y, z} : Finset (Fin 20)) →
      (G.neighborFinset v ∩ D).card = 0 := by
    intro v hvD hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    have hvIso := hisochar v hvD hv.1 hv.2.1 hv.2.2
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    exact (hIsoprop v hvIso).2 w hw.1 ((hmemD w).mp hw.2)
  have hxyz_sub : ({x, y, z} : Finset (Fin 20)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hsumD_in : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 4 := by
    rw [← Finset.sum_subset hxyz_sub (fun v hv hnv => hother0 v hv hnv),
      Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
      Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton,
      hNxD, hNyD, hNzD, Finset.card_pair hxz_ne, Finset.card_singleton]
    rfl
  have hsum72 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w + 3 * D.card = 72 := by
    have hh : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 72 := by
      rw [Finset.sum_add_sum_compl]; exact hsum72
    rw [hsumDdeg] at hh; omega
  have hDcD : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card + 4 = 3 * D.card := by
    have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
        = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count_twenty G D Dᶜ
    have hcongD : ∑ v ∈ D, ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
        = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hsplit v)
    rw [Finset.sum_add_distrib, hsumD_in, hsumDdeg] at hcongD
    omega
  have hIntinc : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 76 - 6 * D.card := by
    have hcongDc : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card)
        = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hsplit w)
    rw [Finset.sum_add_distrib] at hcongDc
    omega
  have hKcardx : (G.neighborFinset x ∩ Dᶜ).card = 2 := by
    have := hsplit x; rw [hNxD, hdegx, Finset.card_singleton] at this; omega
  have hKcardy : (G.neighborFinset y ∩ Dᶜ).card = 1 := by
    have := hsplit y; rw [hNyD, hdegy, Finset.card_pair hxz_ne] at this; omega
  have hKcardz : (G.neighborFinset z ∩ Dᶜ).card = 2 := by
    have := hsplit z; rw [hNzD, hdegz, Finset.card_singleton] at this; omega
  have hCfull : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ ({x, y, z} : Finset (Fin 20))).card = 5 := by
    have hcc := cross_count_twenty G Dᶜ ({x, y, z} : Finset (Fin 20))
    rw [hcc, Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
      Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton, hKcardx, hKcardy, hKcardz]
    rfl
  have hCinc : ∑ h ∈ Hub5, (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 20))).card ≤ 5 := by
    rw [← hCfull]; exact Finset.sum_le_sum_of_subset hHub5sub
  have hdecomp : ∀ h : Fin 20, h ∈ Hub5 → (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 20))).card
      + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h := by
    intro h _
    have hd1 : (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card = (G.neighborFinset h ∩ D).card := by
      have hdisj : Disjoint (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 20)))
          (G.neighborFinset h ∩ Iso) :=
        Finset.disjoint_left.mpr (fun w hw hw' =>
          (Finset.disjoint_left.mp hKIsodisj (Finset.mem_inter.mp hw).2)
            (Finset.mem_inter.mp hw').2)
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, hKIso]
    have hd2 := hsplit h
    omega
  have hHubdeg4 : ∀ h : Fin 20, h ∈ Hub5 → 4 ≤ G.degree h := by
    intro h hh
    have hhDc : h ∈ Dᶜ := hHub5sub hh
    rw [Finset.mem_compl, hmemD] at hhDc; have := h3 h; omega
  rcases cherry_avoider_or_dense_twenty G Iso ({x, y, z} : Finset (Fin 20)) Dᶜ Hub5 5
      (76 - 6 * D.card) hHub5sub hIsoprop hHubdeg4 hHub5deg5 hdecomp hCinc hIntinc with hhub | hdense
  · obtain ⟨h, t₁, t₂, hhHub5, havoid, hhdeg5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1no, ht2no⟩ :=
      hhub
    have hhDc : h ∈ Dᶜ := hHub5sub hhHub5
    have hhx : ¬G.Adj h x := havoid x (by simp)
    have hhy : ¬G.Adj h y := havoid y (by simp)
    have hhz : ¬G.Adj h z := havoid z (by simp)
    have hhxne : h ≠ x := fun e => (Finset.mem_compl.mp hhDc) (e ▸ hxD)
    have hhyne : h ≠ y := fun e => (Finset.mem_compl.mp hhDc) (e ▸ hyD)
    have hhzne : h ≠ z := fun e => (Finset.mem_compl.mp hhDc) (e ▸ hzD)
    exact Or.inl (twotwin_assemble_cherry_raw_twenty G x y z h t₁ t₂ hdegx hdegy hdegz hxyA hyzA
      hxy_ne hyz_ne hxz_ne hhdeg5 hhx hhy hhz hhxne hhyne hhzne ht1deg ht2deg ht12 ht1no ht2no
      hAt1h hAt2h)
  · obtain ⟨S, hSsub, hSavoid, hScard, hS3, hS6, hSmax⟩ := hdense
    refine Or.inr ⟨S, hSsub, fun h hh => ⟨hSavoid h hh x (by simp), hSavoid h hh y (by simp),
      hSavoid h hh z (by simp)⟩, hScard, hS3, hS6, ?_⟩
    intro h hh hx hy hz
    refine hSmax h hh (fun k hk => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz

end N20

end ACMax
