import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.CherryCore

/-!
# `n = 18`, `e(M) = 2` (`P₃` cherry) alignment corners for `|D| ∈ {9, 10, 11}`

These helper lemmas close the `P₃`-cherry residual of `exists_align_four_config_eighteen`
(`ACMaxConjecture/TwinCert18.lean`).  At `s = 4`, `e(M) = 2`, the matching `M` is the single cherry
`x–y–z` (centre `y`); the `M`-isolated degree-`3` vertices form `Iso = D \ {x, y, z}` and every other
degree-`3` vertex is one of `x, y, z`.  The internal hub sum is `∑_{Dᶜ}|N ∩ Dᶜ| = 68 − 6|D|`, so

* `|D| = 11` (`|Hub| = 7`, internal `2`): every avoider has `≥ 2` twins — `TwoTwinConfig`.
* `|D| = 10` (`|Hub| = 8`, internal `8`): the dense-avoider tie is impossible — `TwoTwinConfig`.
* `|D| = 9`  (`|Hub| = 9`, internal `14`): either a cherry-avoiding deg-`≤ 5` hub carries two
  twins (`TwoTwinConfig`), or the four avoiders are dense (`≥ 5` internal edges), giving a hub
  triangle of combined degree `≤ 13` — `HubTriangleConfig`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **`P₃`-cherry `|D| = 11` corner (`n = 18`, `e(M) = 2`).**  `|Hub| = 7`, internal sum `2`; the
dense-avoider branch needs `3|S| ≤ 2` yet `|S| ≥ 1`, impossible, so the dichotomy yields a
`TwoTwinConfig`. -/
theorem cherry_p3_config_D11_eighteen (G : SimpleGraph (Fin 18))
    (hm : G.edgeFinset.card = 32) (h3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (D Iso : Finset (Fin 18)) (x y z : Fin 18)
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 18)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 11) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hsum64 : ∑ v : Fin 18, G.degree v = 64 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDc : ∑ w ∈ Dᶜ, G.degree w = 31 := by
    have h : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 64 := by
      rw [Finset.sum_add_sum_compl]; exact hsum64
    rw [hsumDdeg, hDcard] at h; omega
  have hDc7 : Dᶜ.card = 7 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  set Hub5 : Finset (Fin 18) := Dᶜ.filter (fun w => G.degree w ≤ 5) with hHub5def
  set H6 : Finset (Fin 18) := Dᶜ.filter (fun w => ¬G.degree w ≤ 5) with hH6def
  have hHub5sub : Hub5 ⊆ Dᶜ := Finset.filter_subset _ _
  have hHub5deg5 : ∀ h : Fin 18, h ∈ Hub5 → G.degree h ≤ 5 :=
    fun h hh => (Finset.mem_filter.mp hh).2
  have hpart : Hub5.card + H6.card = Dᶜ.card := by
    rw [hHub5def, hH6def]; exact Finset.card_filter_add_card_filter_not _
  have hsplitdeg : ∑ w ∈ Hub5, G.degree w + ∑ w ∈ H6, G.degree w = ∑ w ∈ Dᶜ, G.degree w := by
    rw [hHub5def, hH6def]; exact Finset.sum_filter_add_sum_filter_not Dᶜ _ _
  have hH6sum : 6 * H6.card ≤ ∑ w ∈ H6, G.degree w := by
    have := Finset.card_nsmul_le_sum H6 (fun w => G.degree w) 6
      (fun w hw => by have hw2 := Finset.mem_filter.mp hw; omega)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hHub5sum : 4 * Hub5.card ≤ ∑ w ∈ Hub5, G.degree w := by
    have := Finset.card_nsmul_le_sum Hub5 (fun w => G.degree w) 4
      (fun w hw => by
        have hwc : w ∈ Dᶜ := hHub5sub hw
        rw [Finset.mem_compl, hmemD] at hwc; have := h3 w; omega)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hHub5ge6 : 6 ≤ Hub5.card := by omega
  rcases p3_cherry_dichotomy_eighteen G D Iso Hub5 x y z hm h3 hmemD hIsoprop hisochar hcov hNyD
      hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne hHub5sub hHub5deg5 with htt | hdense
  · exact Or.inr (Or.inl htt)
  · exfalso
    obtain ⟨S, _hSsub, _hSavoid, hScard, hS3, _hS6⟩ := hdense
    rw [hDcard] at hS3
    omega

/-- **`P₃`-cherry `|D| = 10` corner (`n = 18`, `e(M) = 2`).**  `|Hub| = 8`, internal sum `8`; the
dense-avoider tie forces `|S| = 2` with `∑_{h∈S}|N h ∩ S| ≥ 4`, impossible since two vertices span
`≤ 2` directed edges, so the dichotomy yields a `TwoTwinConfig`. -/
theorem cherry_p3_two_hub_D10_eighteen (G : SimpleGraph (Fin 18))
    (hm : G.edgeFinset.card = 32) (h3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (D Iso : Finset (Fin 18)) (x y z : Fin 18)
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 18)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 10) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hsum64 : ∑ v : Fin 18, G.degree v = 64 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDc : ∑ w ∈ Dᶜ, G.degree w = 34 := by
    have h : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 64 := by
      rw [Finset.sum_add_sum_compl]; exact hsum64
    rw [hsumDdeg, hDcard] at h; omega
  have hDc8 : Dᶜ.card = 8 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  set Hub5 : Finset (Fin 18) := Dᶜ.filter (fun w => G.degree w ≤ 5) with hHub5def
  set H6 : Finset (Fin 18) := Dᶜ.filter (fun w => ¬G.degree w ≤ 5) with hH6def
  have hHub5sub : Hub5 ⊆ Dᶜ := Finset.filter_subset _ _
  have hHub5deg5 : ∀ h : Fin 18, h ∈ Hub5 → G.degree h ≤ 5 :=
    fun h hh => (Finset.mem_filter.mp hh).2
  have hpart : Hub5.card + H6.card = Dᶜ.card := by
    rw [hHub5def, hH6def]; exact Finset.card_filter_add_card_filter_not _
  have hsplitdeg : ∑ w ∈ Hub5, G.degree w + ∑ w ∈ H6, G.degree w = ∑ w ∈ Dᶜ, G.degree w := by
    rw [hHub5def, hH6def]; exact Finset.sum_filter_add_sum_filter_not Dᶜ _ _
  have hH6sum : 6 * H6.card ≤ ∑ w ∈ H6, G.degree w := by
    have := Finset.card_nsmul_le_sum H6 (fun w => G.degree w) 6
      (fun w hw => by have hw2 := Finset.mem_filter.mp hw; omega)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hHub5sum : 4 * Hub5.card ≤ ∑ w ∈ Hub5, G.degree w := by
    have := Finset.card_nsmul_le_sum Hub5 (fun w => G.degree w) 4
      (fun w hw => by
        have hwc : w ∈ Dᶜ := hHub5sub hw
        rw [Finset.mem_compl, hmemD] at hwc; have := h3 w; omega)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hHub5ge7 : 7 ≤ Hub5.card := by omega
  rcases p3_cherry_dichotomy_eighteen G D Iso Hub5 x y z hm h3 hmemD hIsoprop hisochar hcov hNyD
      hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne hHub5sub hHub5deg5 with htt | hdense
  · exact Or.inr (Or.inl htt)
  · exfalso
    obtain ⟨S, _hSsub, _hSavoid, hScard, hS3, hS6⟩ := hdense
    rw [hDcard] at hS3 hS6
    have hScard2 : S.card = 2 := by omega
    have hbnd : ∑ h ∈ S, (G.neighborFinset h ∩ S).card ≤ 2 := by
      calc ∑ h ∈ S, (G.neighborFinset h ∩ S).card ≤ ∑ _h ∈ S, 1 := by
            apply Finset.sum_le_sum
            intro h hh
            have hsub : G.neighborFinset h ∩ S ⊆ S.erase h := by
              intro w hw
              rw [Finset.mem_inter, G.mem_neighborFinset] at hw
              exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hw.1), hw.2⟩
            calc (G.neighborFinset h ∩ S).card ≤ (S.erase h).card := Finset.card_le_card hsub
              _ = 1 := by rw [Finset.card_erase_of_mem hh, hScard2]
        _ = 2 := by rw [Finset.sum_const, hScard2, smul_eq_mul, mul_one]
    omega

/-- **`P₃`-cherry `|D| = 9` corner (`n = 18`, `e(M) = 2`).**  `|Hub| = 9` (all degree-`≤ 5`),
internal sum `14`.  The dichotomy either gives a cherry-avoiding deg-`≤ 5` hub with two twins
(`TwoTwinConfig`), or four dense avoiders with `≥ 10` internal directed edges; the latter contain a
hub triangle of combined degree `≤ 37 − 4·6 = 13`, all avoiding the cherry — `HubTriangleConfig`. -/
theorem cherry_p3_config_D9_eighteen (G : SimpleGraph (Fin 18))
    (hm : G.edgeFinset.card = 32) (h3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (D Iso : Finset (Fin 18)) (x y z : Fin 18)
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 18)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 9) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hsum64 : ∑ v : Fin 18, G.degree v = 64 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDc : ∑ w ∈ Dᶜ, G.degree w = 37 := by
    have h : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 64 := by
      rw [Finset.sum_add_sum_compl]; exact hsum64
    rw [hsumDdeg, hDcard] at h; omega
  have hDc9 : Dᶜ.card = 9 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  -- All nine hubs have degree `≤ 5` (excess `1`).
  have hdeg5all : ∀ w : Fin 18, w ∈ Dᶜ → G.degree w ≤ 5 := by
    intro w hw
    have hspl := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
    have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
      have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i := fun i hi => by
        have hic : i ∈ Dᶜ := Finset.mem_of_mem_erase hi
        rw [Finset.mem_compl, hmemD] at hic; have := h3 i; omega
      have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using this
    have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
    rw [hsumDc] at hspl
    omega
  rcases p3_cherry_dichotomy_eighteen G D Iso Dᶜ x y z hm h3 hmemD hIsoprop hisochar hcov hNyD
      hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne (Finset.Subset.refl _) hdeg5all
    with htt | hdense
  · exact Or.inr (Or.inl htt)
  · obtain ⟨S, hSsub, hSavoid, hScard, hS3, hS6⟩ := hdense
    rw [hDcard] at hS3 hS6
    rw [hDc9] at hScard
    have hScard4 : S.card = 4 := by omega
    have hdense10 : 10 ≤ ∑ h ∈ S, (G.neighborFinset h ∩ S).card := by
      rw [hScard4] at hS6; omega
    obtain ⟨h₁, h₂, h₃, hh1S, hh2S, hh3S, hne12, hne13, hne23, hA12, hA13, hA23⟩ :=
      four_set_triangle_eighteen G S hScard4 hdense10
    have hh1Dc : h₁ ∈ Dᶜ := hSsub hh1S
    have hh2Dc : h₂ ∈ Dᶜ := hSsub hh2S
    have hh3Dc : h₃ ∈ Dᶜ := hSsub hh3S
    obtain ⟨hn1x, hn1y, hn1z⟩ := hSavoid h₁ hh1S
    obtain ⟨hn2x, hn2y, hn2z⟩ := hSavoid h₂ hh2S
    obtain ⟨hn3x, hn3y, hn3z⟩ := hSavoid h₃ hh3S
    have hxD : x ∈ D := (hmemD x).mpr hdegx
    have hyD : y ∈ D := (hmemD y).mpr hdegy
    have hzD : z ∈ D := (hmemD z).mpr hdegz
    have hnehd : ∀ h : Fin 18, h ∈ Dᶜ → ∀ d : Fin 18, d ∈ D → h ≠ d :=
      fun h hh d hd e => (Finset.mem_compl.mp hh) (e ▸ hd)
    -- Combined degree of the triangle is `≤ 13`: the other six hubs contribute `≥ 24` of `37`.
    have hTsub : ({h₁, h₂, h₃} : Finset (Fin 18)) ⊆ Dᶜ := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have hTcard : ({h₁, h₂, h₃} : Finset (Fin 18)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne12, hne13]),
        Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]
    have hsdiff : ∑ w ∈ Dᶜ \ ({h₁, h₂, h₃} : Finset (Fin 18)), G.degree w
        + ∑ w ∈ ({h₁, h₂, h₃} : Finset (Fin 18)), G.degree w = ∑ w ∈ Dᶜ, G.degree w :=
      Finset.sum_sdiff hTsub
    have hTval : ∑ w ∈ ({h₁, h₂, h₃} : Finset (Fin 18)), G.degree w
        = G.degree h₁ + G.degree h₂ + G.degree h₃ := by
      rw [Finset.sum_insert (by simp [hne12, hne13]),
        Finset.sum_insert (by simp [hne23]), Finset.sum_singleton]; ring
    have hcardsdiff : (Dᶜ \ ({h₁, h₂, h₃} : Finset (Fin 18))).card = 6 := by
      have hkey := Finset.card_sdiff_add_card_inter Dᶜ ({h₁, h₂, h₃} : Finset (Fin 18))
      have hinter : Dᶜ ∩ ({h₁, h₂, h₃} : Finset (Fin 18)) = ({h₁, h₂, h₃} : Finset (Fin 18)) :=
        Finset.inter_eq_right.mpr hTsub
      rw [hinter, hTcard, hDc9] at hkey; omega
    have hge24 : 4 * 6 ≤ ∑ w ∈ Dᶜ \ ({h₁, h₂, h₃} : Finset (Fin 18)), G.degree w := by
      have := Finset.card_nsmul_le_sum (Dᶜ \ ({h₁, h₂, h₃} : Finset (Fin 18)))
        (fun w => G.degree w) 4 (fun w hw => by
          have hwc : w ∈ Dᶜ := (Finset.mem_sdiff.mp hw).1
          rw [Finset.mem_compl, hmemD] at hwc; have := h3 w; omega)
      rw [hcardsdiff] at this
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hsideeq : G.degree h₁ + G.degree h₂ + G.degree h₃ ≤ 13 := by
      rw [hsumDc, hTval] at hsdiff; omega
    exact Or.inr (Or.inr (Or.inr
      ⟨h₁, h₂, h₃, x, y, z, hdegx, hdegy, hdegz, hA12, hA13, hA23, hxyA, hyzA,
        hn1x, hn1y, hn1z, hn2x, hn2y, hn2z, hn3x, hn3y, hn3z, hsideeq,
        hnehd h₁ hh1Dc x hxD, hnehd h₁ hh1Dc y hyD, hnehd h₁ hh1Dc z hzD,
        hnehd h₂ hh2Dc x hxD, hnehd h₂ hh2Dc y hyD, hnehd h₂ hh2Dc z hzD,
        hnehd h₃ hh3Dc x hxD, hnehd h₃ hh3Dc y hyD, hnehd h₃ hh3Dc z hzD,
        hxy_ne, hyz_ne, hxz_ne⟩))

end N18

end ACMax
