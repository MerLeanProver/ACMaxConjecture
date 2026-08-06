import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.CherryCore
import ACMaxConjecture.SmallCases.N19.CherryP4HubTriangleShare
import ACMaxConjecture.SmallCases.N19.Align8Helpers
import ACMaxConjecture.SmallCases.N19.BipartiteAvoiderTwoHub

/-!
# `n = 19`, `e(M) = 2` (`P₃` cherry) alignment corners for `|D| ∈ {9, 10, 11}`

These helper lemmas close the `P₃`-cherry residual of `exists_align_four_config_nineteen`
(`ACMaxConjecture/TwinCert19.lean`).  At `s = 4`, `e(M) = 2`, the matching `M` is the single cherry
`x–y–z` (centre `y`); the `M`-isolated degree-`3` vertices form `Iso = D \ {x, y, z}` and every other
degree-`3` vertex is one of `x, y, z`.  The internal hub sum is `∑_{Dᶜ}|N ∩ Dᶜ| = 68 − 6|D|`, so

* `|D| = 11` (`|Hub| = 8`, internal `2`): every avoider has `≥ 2` twins — `TwoTwinConfig`.
* `|D| = 10` (`|Hub| = 9`, internal `8`): the dense-avoider tie is impossible — `TwoTwinConfig`.
* `|D| = 9`  (`|Hub| = 10`, internal `14`): either a cherry-avoiding deg-`≤ 5` hub carries two
  twins (`TwoTwinConfig`), or the four avoiders are dense (`≥ 5` internal edges), giving a hub
  triangle of combined degree `≤ 13` — `HubTriangleConfig`.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **`P₃`-cherry `|D| = 11` corner (`n = 19`, `e(M) = 2`).**  `|Hub| = 8`, internal sum `2`; the
dense-avoider branch needs `3|S| ≤ 2` yet `|S| ≥ 1`, impossible, so the dichotomy yields a
`TwoTwinConfig`. -/
theorem cherry_p3_config_D11_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (D Iso : Finset (Fin 19)) (x y z : Fin 19)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 19, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 19)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 11) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hsum64 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDc : ∑ w ∈ Dᶜ, G.degree w = 35 := by
    have h : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 68 := by
      rw [Finset.sum_add_sum_compl]; exact hsum64
    rw [hsumDdeg, hDcard] at h; omega
  have hDc8 : Dᶜ.card = 8 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  set Hub5 : Finset (Fin 19) := Dᶜ.filter (fun w => G.degree w ≤ 5) with hHub5def
  set H6 : Finset (Fin 19) := Dᶜ.filter (fun w => ¬G.degree w ≤ 5) with hH6def
  have hHub5sub : Hub5 ⊆ Dᶜ := Finset.filter_subset _ _
  have hHub5deg5 : ∀ h : Fin 19, h ∈ Hub5 → G.degree h ≤ 5 :=
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
  rcases p3_cherry_dichotomy_nineteen G D Iso Hub5 x y z hm h3 hmemD hIsoprop hisochar hcov hNyD
      hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne hHub5sub hHub5deg5 with htt | hdense
  · exact Or.inr (Or.inl htt)
  · exfalso
    -- `|Hub| = 8`, internal sum `6`: the dense avoider set is forced to `|S| = 2`, but the
    -- within-avoider edge bound then needs `≥ 6` directed edges on two vertices, impossible.
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

/-- **`P₃`-cherry `|D| = 10` corner (`n = 19`, `e(M) = 2`).**  `|Hub| = 9`, internal sum `8`; the
dense-avoider tie forces `|S| = 2` with `∑_{h∈S}|N h ∩ S| ≥ 4`, impossible since two vertices span
`≤ 2` directed edges, so the dichotomy yields a `TwoTwinConfig`. -/
theorem cherry_p3_two_hub_D10_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (D Iso : Finset (Fin 19)) (x y z : Fin 19)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 19, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 19)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 10) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hsum68 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDc : ∑ w ∈ Dᶜ, G.degree w = 38 := by
    have h : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 68 := by
      rw [Finset.sum_add_sum_compl]; exact hsum68
    rw [hsumDdeg, hDcard] at h; omega
  have hDc9 : Dᶜ.card = 9 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  have hDcdeg4 : ∀ w : Fin 19, w ∈ Dᶜ → 4 ≤ G.degree w := by
    intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
  set Hub5 : Finset (Fin 19) := Dᶜ.filter (fun w => G.degree w ≤ 5) with hHub5def
  set H6 : Finset (Fin 19) := Dᶜ.filter (fun w => ¬G.degree w ≤ 5) with hH6def
  have hHub5sub : Hub5 ⊆ Dᶜ := Finset.filter_subset _ _
  have hHub5deg5 : ∀ h : Fin 19, h ∈ Hub5 → G.degree h ≤ 5 :=
    fun h hh => (Finset.mem_filter.mp hh).2
  have hpart : Hub5.card + H6.card = Dᶜ.card := by
    rw [hHub5def, hH6def]; exact Finset.card_filter_add_card_filter_not _
  have hsplitdeg : ∑ w ∈ Hub5, G.degree w + ∑ w ∈ H6, G.degree w = ∑ w ∈ Dᶜ, G.degree w := by
    rw [hHub5def, hH6def]; exact Finset.sum_filter_add_sum_filter_not Dᶜ _ _
  have hH6sum : 6 * H6.card ≤ ∑ w ∈ H6, G.degree w := by
    have := Finset.card_nsmul_le_sum H6 (fun w => G.degree w) 6
      (fun w hw => by have hw2 := Finset.mem_filter.mp hw; omega)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hHub5sum4 : 4 * Hub5.card ≤ ∑ w ∈ Hub5, G.degree w := by
    have := Finset.card_nsmul_le_sum Hub5 (fun w => G.degree w) 4
      (fun w hw => hDcdeg4 w (hHub5sub hw))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hHub5ge8 : 8 ≤ Hub5.card := by
    rw [hDc9] at hpart; rw [hsumDc] at hsplitdeg; omega
  rcases p3_cherry_dichotomy_nineteen G D Iso Hub5 x y z hm h3
      hmemD hIsoprop hisochar hcov hNyD hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne
      hHub5sub hHub5deg5 with htt | hdense
  · exact Or.inr (Or.inl htt)
  · -- Dense cherry-avoiding branch.  `Int = 12`, `|Hub5| ∈ {8, 9}`, so `|S| ∈ {3, 4}` and `S` is
    -- complete (`K₃`/`K₄`).  We extract a within-`S` triangle of combined degree `≤ 13` (dropping
    -- the maximum-degree vertex of the `K₄`, or all-degree-`4` for the `K₃`), feeding it to
    -- `HubTriangleConfig`.
    obtain ⟨S, hSsub, hSavoid, hScard, hS3, hS6⟩ := hdense
    rw [hDcard] at hS3 hS6
    have hSsubDc : S ⊆ Dᶜ := fun w hw => hHub5sub (hSsub hw)
    have hScard_le4 : S.card ≤ 4 := by omega
    have hScard_ge3 : 3 ≤ S.card := by omega
    -- `S` is complete: each `|N h ∩ S| = |S| − 1`.
    have hScompl : ∀ a : Fin 19, a ∈ S → ∀ b : Fin 19, b ∈ S → a ≠ b → G.Adj a b := by
      intro a ha b hb hab
      by_contra hnadj
      have hbound : ∀ h : Fin 19, h ∈ S → (G.neighborFinset h ∩ S).card ≤ S.card - 1 := by
        intro h hh
        have hsub : G.neighborFinset h ∩ S ⊆ S.erase h := by
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hw.1), hw.2⟩
        calc (G.neighborFinset h ∩ S).card ≤ (S.erase h).card := Finset.card_le_card hsub
          _ = S.card - 1 := Finset.card_erase_of_mem hh
      have hboundA : (G.neighborFinset a ∩ S).card ≤ S.card - 2 := by
        have hsub : G.neighborFinset a ∩ S ⊆ (S.erase a).erase b := by
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hw.1), hw.2⟩⟩
          rintro rfl; exact hnadj hw.1
        calc (G.neighborFinset a ∩ S).card ≤ ((S.erase a).erase b).card := Finset.card_le_card hsub
          _ = S.card - 2 := by
              rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨fun e => hab e.symm, hb⟩),
                Finset.card_erase_of_mem ha]; omega
      have hsplit : ∑ h ∈ S, (G.neighborFinset h ∩ S).card
          = (G.neighborFinset a ∩ S).card + ∑ h ∈ S.erase a, (G.neighborFinset h ∩ S).card :=
        (Finset.add_sum_erase S _ ha).symm
      have hrest : ∑ h ∈ S.erase a, (G.neighborFinset h ∩ S).card ≤ (S.card - 1) * (S.card - 1) := by
        calc ∑ h ∈ S.erase a, (G.neighborFinset h ∩ S).card ≤ ∑ _h ∈ S.erase a, (S.card - 1) :=
              Finset.sum_le_sum (fun h hh => hbound h (Finset.mem_of_mem_erase hh))
          _ = (S.card - 1) * (S.card - 1) := by
              rw [Finset.sum_const, Finset.card_erase_of_mem ha, smul_eq_mul]
      -- `S.card ∈ {3,4}`: the directed-edge lower bound is violated.
      rcases (show S.card = 3 ∨ S.card = 4 from by omega) with hSc | hSc <;>
        (rw [hSc] at hboundA hrest hS6; omega)
    -- Extract a triangle `h₁,h₂,h₃ ∈ S` of combined degree `≤ 13`.
    have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨m, hmS, hmmax⟩ := Finset.exists_max_image S (fun v => G.degree v) hSnonempty
    -- The triangle is `S` itself (`|S| = 3`) or `S.erase m` (`|S| = 4`).
    have hkey : ∃ h₁ h₂ h₃ : Fin 19, h₁ ∈ S ∧ h₂ ∈ S ∧ h₃ ∈ S ∧
        h₁ ≠ h₂ ∧ h₁ ≠ h₃ ∧ h₂ ≠ h₃ ∧ G.Adj h₁ h₂ ∧ G.Adj h₁ h₃ ∧ G.Adj h₂ h₃ ∧
        G.degree h₁ + G.degree h₂ + G.degree h₃ ≤ 13 := by
      have hassemble : ∀ a b c : Fin 19, a ∈ S → b ∈ S → c ∈ S → a ≠ b → a ≠ c → b ≠ c →
          G.degree a + G.degree b + G.degree c ≤ 13 →
          ∃ h₁ h₂ h₃ : Fin 19, h₁ ∈ S ∧ h₂ ∈ S ∧ h₃ ∈ S ∧
            h₁ ≠ h₂ ∧ h₁ ≠ h₃ ∧ h₂ ≠ h₃ ∧ G.Adj h₁ h₂ ∧ G.Adj h₁ h₃ ∧ G.Adj h₂ h₃ ∧
            G.degree h₁ + G.degree h₂ + G.degree h₃ ≤ 13 :=
        fun a b c haS hbS hcS hab hac hbc hd =>
          ⟨a, b, c, haS, hbS, hcS, hab, hac, hbc, hScompl a haS b hbS hab,
            hScompl a haS c hcS hac, hScompl b hbS c hcS hbc, hd⟩
      by_cases hS4 : S.card = 4
      · -- `K₄`: triangle `T = S.erase m`, combined degree `= ∑_S deg − deg m ≤ 13`.
        have hTcard : (S.erase m).card = 3 := by rw [Finset.card_erase_of_mem hmS, hS4]
        obtain ⟨h₁, h₂, h₃, hne12, hne13, hne23, hTeq⟩ := Finset.card_eq_three.mp hTcard
        have hh1S : h₁ ∈ S := Finset.mem_of_mem_erase (by rw [hTeq]; simp)
        have hh2S : h₂ ∈ S := Finset.mem_of_mem_erase (by rw [hTeq]; simp)
        have hh3S : h₃ ∈ S := Finset.mem_of_mem_erase (by rw [hTeq]; simp)
        -- combined degree of the triangle `= ∑_S − deg m`
        have hsumS : ∑ v ∈ S, G.degree v = G.degree m + (G.degree h₁ + G.degree h₂ + G.degree h₃) := by
          rw [← Finset.add_sum_erase S _ hmS, hTeq, Finset.sum_insert (by simp [hne12, hne13]),
            Finset.sum_insert (by simp [hne23]), Finset.sum_singleton]; omega
        -- `∑_S deg ≤ 18` (other 5 hubs of `Dᶜ` have degree `≥ 4`)
        have hsumSle : ∑ v ∈ S, G.degree v ≤ 18 := by
          have hsdiff : ∑ w ∈ Dᶜ \ S, G.degree w + ∑ w ∈ S, G.degree w = ∑ w ∈ Dᶜ, G.degree w :=
            Finset.sum_sdiff hSsubDc
          have hcardsdiff : (Dᶜ \ S).card = 5 := by
            have h := Finset.card_sdiff_add_card_inter Dᶜ S
            rw [Finset.inter_eq_right.mpr hSsubDc, hDc9, hS4] at h; omega
          have hge : 4 * 5 ≤ ∑ w ∈ Dᶜ \ S, G.degree w := by
            have := Finset.card_nsmul_le_sum (Dᶜ \ S) (fun w => G.degree w) 4
              (fun w hw => hDcdeg4 w (Finset.mem_sdiff.mp hw).1)
            rw [hcardsdiff] at this; simpa [smul_eq_mul, Nat.mul_comm] using this
          rw [hsumDc] at hsdiff; omega
        -- `4 · deg m ≥ ∑_S` (m is the maximum)
        have hmaxsum : ∑ v ∈ S, G.degree v ≤ 4 * G.degree m := by
          calc ∑ v ∈ S, G.degree v ≤ ∑ _v ∈ S, G.degree m := Finset.sum_le_sum (fun v hv => hmmax v hv)
            _ = 4 * G.degree m := by rw [Finset.sum_const, hS4, smul_eq_mul]
        exact hassemble h₁ h₂ h₃ hh1S hh2S hh3S hne12 hne13 hne23 (by omega)
      · -- `|S| = 3`: `K₃`, all degree `4` (since `Hub5.card = 8` forces all-degree-`4`).
        have hS3' : S.card = 3 := by omega
        -- `Hub5.card = 8`, so exactly one degree-`≥ 6` hub, the rest degree `4`.
        have hHub5eq8 : Hub5.card = 8 := by omega
        have hHub5all4 : ∀ w : Fin 19, w ∈ Hub5 → G.degree w = 4 := by
          have hH6card1 : H6.card = 1 := by rw [hDc9] at hpart; omega
          have hsumHub5 : ∑ w ∈ Hub5, G.degree w ≤ 32 := by
            have hH6ge6 : 6 ≤ ∑ w ∈ H6, G.degree w := by
              have := Finset.card_nsmul_le_sum H6 (fun w => G.degree w) 6
                (fun w hw => by have hw2 := Finset.mem_filter.mp hw; omega)
              rw [hH6card1] at this; simpa [smul_eq_mul] using this
            rw [hsumDc] at hsplitdeg; omega
          intro w hw
          have hge4 : 4 ≤ G.degree w := hDcdeg4 w (hHub5sub hw)
          have hrest : 4 * (Hub5.erase w).card ≤ ∑ v ∈ Hub5.erase w, G.degree v := by
            have := Finset.card_nsmul_le_sum (Hub5.erase w) (fun v => G.degree v) 4
              (fun v hv => hDcdeg4 v (hHub5sub (Finset.mem_of_mem_erase hv)))
            simpa [smul_eq_mul, Nat.mul_comm] using this
          have hspl := Finset.add_sum_erase Hub5 (fun v => G.degree v) hw
          have hec : (Hub5.erase w).card = 7 := by rw [Finset.card_erase_of_mem hw, hHub5eq8]
          rw [hec] at hrest; omega
        obtain ⟨h₁, h₂, h₃, hne12, hne13, hne23, hSeq⟩ := Finset.card_eq_three.mp hS3'
        have hh1S : h₁ ∈ S := by rw [hSeq]; simp
        have hh2S : h₂ ∈ S := by rw [hSeq]; simp
        have hh3S : h₃ ∈ S := by rw [hSeq]; simp
        refine hassemble h₁ h₂ h₃ hh1S hh2S hh3S hne12 hne13 hne23 ?_
        rw [hHub5all4 h₁ (hSsub hh1S), hHub5all4 h₂ (hSsub hh2S), hHub5all4 h₃ (hSsub hh3S)]
        norm_num
    obtain ⟨h₁, h₂, h₃, hh1S, hh2S, hh3S, hne12, hne13, hne23, hA12, hA13, hA23, hsideeq⟩ := hkey
    obtain ⟨hn1x, hn1y, hn1z⟩ := hSavoid h₁ hh1S
    obtain ⟨hn2x, hn2y, hn2z⟩ := hSavoid h₂ hh2S
    obtain ⟨hn3x, hn3y, hn3z⟩ := hSavoid h₃ hh3S
    have hxD : x ∈ D := (hmemD x).mpr hdegx
    have hyD : y ∈ D := (hmemD y).mpr hdegy
    have hzD : z ∈ D := (hmemD z).mpr hdegz
    have hnehd : ∀ h : Fin 19, h ∈ Dᶜ → ∀ d : Fin 19, d ∈ D → h ≠ d :=
      fun h hh d hd e => (Finset.mem_compl.mp hh) (e ▸ hd)
    have hh1Dc : h₁ ∈ Dᶜ := hSsubDc hh1S
    have hh2Dc : h₂ ∈ Dᶜ := hSsubDc hh2S
    have hh3Dc : h₃ ∈ Dᶜ := hSsubDc hh3S
    exact Or.inr (Or.inr (Or.inr
      ⟨h₁, h₂, h₃, x, y, z, hdegx, hdegy, hdegz, hA12, hA13, hA23, hxyA, hyzA,
        hn1x, hn1y, hn1z, hn2x, hn2y, hn2z, hn3x, hn3y, hn3z, hsideeq,
        hnehd h₁ hh1Dc x hxD, hnehd h₁ hh1Dc y hyD, hnehd h₁ hh1Dc z hzD,
        hnehd h₂ hh2Dc x hxD, hnehd h₂ hh2Dc y hyD, hnehd h₂ hh2Dc z hzD,
        hnehd h₃ hh3Dc x hxD, hnehd h₃ hh3Dc y hyD, hnehd h₃ hh3Dc z hzD,
        hxy_ne, hyz_ne, hxz_ne⟩))

set_option maxHeartbeats 8000000 in
/-- **`P₃`-cherry `|D| = 9` corner (`n = 19`, `e(M) = 2`).**  `|Hub| = 10` (all degree-`≤ 5`),
internal sum `14`.  The dichotomy either gives a cherry-avoiding deg-`≤ 5` hub with two twins
(`TwoTwinConfig`), or four dense avoiders with `≥ 10` internal directed edges; the latter contain a
hub triangle of combined degree `≤ 37 − 4·6 = 13`, all avoiding the cherry — `HubTriangleConfig`. -/
theorem cherry_p3_config_D9_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (D Iso : Finset (Fin 19)) (x y z : Fin 19)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 19, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 19)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 9)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hsum64 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumDc : ∑ w ∈ Dᶜ, G.degree w = 41 := by
    have h : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 68 := by
      rw [Finset.sum_add_sum_compl]; exact hsum64
    rw [hsumDdeg, hDcard] at h; omega
  have hDc10 : Dᶜ.card = 10 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  -- All nine hubs have degree `≤ 5` (excess `1`).
  have hdeg5all : ∀ w : Fin 19, w ∈ Dᶜ → G.degree w ≤ 5 := by
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
  rcases p3_cherry_dichotomy_nineteen G D Iso Dᶜ x y z hm h3 hmemD hIsoprop hisochar hcov hNyD
      hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne (Finset.Subset.refl _) hdeg5all
    with htt | hdense
  · exact Or.inr (Or.inl htt)
  · -- Dense cherry-avoiding branch.  `|D| = 9`, `|Hub| = 10` (all degree `≤ 5`, exactly one degree-`5`
    -- hub, nine degree-`4`), internal sum `≥ 6|S| − 18`.  The dichotomy returns `S ⊆ Dᶜ` with every
    -- `h ∈ S` cherry-avoiding and `|S| ∈ {5, 6}`.  Either `S` contains a triangle (`→ HubTriangleConfig`,
    -- the triangle has combined degree `≤ 13` since at most one of its three hubs is degree-`5`), or
    -- `S` is triangle-free (extremal `K_{2,3}`/`K_{3,3}`), routed to `TwoHubConfig`.
    obtain ⟨S, hSsub, hSavoid, hScard, hS3, hS6⟩ := hdense
    rw [hDcard] at hS3 hS6
    have hScard_ge5 : 5 ≤ S.card := by rw [hDc10] at hScard; omega
    have hScard_le6 : S.card ≤ 6 := by omega
    have hSsubDc : S ⊆ Dᶜ := hSsub
    have hDcdeg4 : ∀ w : Fin 19, w ∈ Dᶜ → 4 ≤ G.degree w := by
      intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
    by_cases htri : ∃ h₁ h₂ h₃ : Fin 19, h₁ ∈ S ∧ h₂ ∈ S ∧ h₃ ∈ S ∧
        h₁ ≠ h₂ ∧ h₁ ≠ h₃ ∧ h₂ ≠ h₃ ∧ G.Adj h₁ h₂ ∧ G.Adj h₁ h₃ ∧ G.Adj h₂ h₃
    · -- **Triangle branch → `HubTriangleConfig`.**  Three pairwise-adjacent cherry-avoiding hubs of
      -- combined degree `≤ 13` (at most one is the unique degree-`5` hub, the other nine are degree-`4`).
      obtain ⟨h₁, h₂, h₃, hh1S, hh2S, hh3S, hne12, hne13, hne23, hA12, hA13, hA23⟩ := htri
      have hh1Dc : h₁ ∈ Dᶜ := hSsubDc hh1S
      have hh2Dc : h₂ ∈ Dᶜ := hSsubDc hh2S
      have hh3Dc : h₃ ∈ Dᶜ := hSsubDc hh3S
      set T : Finset (Fin 19) := {h₁, h₂, h₃} with hTdef
      have hTsubDc : T ⊆ Dᶜ := by
        rw [hTdef]; intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      have hTcard : T.card = 3 := by
        rw [hTdef, Finset.card_insert_of_notMem (by simp [hne12, hne13]),
          Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]
      have hsumT : ∑ w ∈ T, G.degree w = G.degree h₁ + G.degree h₂ + G.degree h₃ := by
        rw [hTdef, Finset.sum_insert (by simp [hne12, hne13]),
          Finset.sum_insert (by simp [hne23]), Finset.sum_singleton]; ring
      have hsdiff : ∑ w ∈ Dᶜ \ T, G.degree w + ∑ w ∈ T, G.degree w = ∑ w ∈ Dᶜ, G.degree w :=
        Finset.sum_sdiff hTsubDc
      have hcardsdiff : (Dᶜ \ T).card = 7 := by
        have h := Finset.card_sdiff_add_card_inter Dᶜ T
        rw [Finset.inter_eq_right.mpr hTsubDc, hDc10, hTcard] at h; omega
      have hge : 4 * 7 ≤ ∑ w ∈ Dᶜ \ T, G.degree w := by
        have := Finset.card_nsmul_le_sum (Dᶜ \ T) (fun w => G.degree w) 4
          (fun w hw => hDcdeg4 w (Finset.mem_sdiff.mp hw).1)
        rw [hcardsdiff] at this; simpa [smul_eq_mul, Nat.mul_comm] using this
      have hsideeq : G.degree h₁ + G.degree h₂ + G.degree h₃ ≤ 13 := by
        rw [hsumDc] at hsdiff; omega
      obtain ⟨hn1x, hn1y, hn1z⟩ := hSavoid h₁ hh1S
      obtain ⟨hn2x, hn2y, hn2z⟩ := hSavoid h₂ hh2S
      obtain ⟨hn3x, hn3y, hn3z⟩ := hSavoid h₃ hh3S
      have hxD : x ∈ D := (hmemD x).mpr hdegx
      have hyD : y ∈ D := (hmemD y).mpr hdegy
      have hzD : z ∈ D := (hmemD z).mpr hdegz
      have hnehd : ∀ h : Fin 19, h ∈ Dᶜ → ∀ d : Fin 19, d ∈ D → h ≠ d :=
        fun h hh d hd e => (Finset.mem_compl.mp hh) (e ▸ hd)
      exact Or.inr (Or.inr (Or.inr
        ⟨h₁, h₂, h₃, x, y, z, hdegx, hdegy, hdegz, hA12, hA13, hA23, hxyA, hyzA,
          hn1x, hn1y, hn1z, hn2x, hn2y, hn2z, hn3x, hn3y, hn3z, hsideeq,
          hnehd h₁ hh1Dc x hxD, hnehd h₁ hh1Dc y hyD, hnehd h₁ hh1Dc z hzD,
          hnehd h₂ hh2Dc x hxD, hnehd h₂ hh2Dc y hyD, hnehd h₂ hh2Dc z hzD,
          hnehd h₃ hh3Dc x hxD, hnehd h₃ hh3Dc y hyD, hnehd h₃ hh3Dc z hzD,
          hxy_ne, hyz_ne, hxz_ne⟩))
    · -- **Triangle-free branch → `TwoTwinConfig ∨ TwoHubConfig` via the slot/twin/hub ledger.**
      -- `J = D \ {x, y, z}` holds `6` `M`-isolated twins with `18` hub incidences, the cherry
      -- holds `5` hub slots (`2 + 1 + 2`), and `∑_{Dᶜ} deg = 41` forces `∑_{Dᶜ}|N ∩ Dᶜ| = 18`.
      -- ESCAPE: a hub with no cherry slot and `≥ 2` twins yields `TwoTwinConfig` directly.
      -- Otherwise every avoider carries `≤ 1` twin, so `∑_S |N ∩ Dᶜ| ≥ 3|S|` squeezes
      -- `∑_T |N ∩ Dᶜ| ≤ 18 − 3|S|` on `T = Dᶜ \ S`.  At `|S| = 6` (and in the slot-free-`T`-hub
      -- corner of `|S| = 5`) four `T`-hubs of total degree `17` carry all five slots with no
      -- hub-hub edges, so two degree-`4` slot-`1` hubs have `3` twins each and share `≤ 1`
      -- (`nonadj_deg4_hubs_share_le_one_iso_pointwise` via `hC4`) → `dense_two_hub_assemble`.
      -- At `|S| = 5` all five `T`-hubs carry exactly one slot; an internally-isolated degree-`4`
      -- hub `h₁` (three twins) pairs with a degree-`4` hub `h₂` of internal degree `≤ 1`: share
      -- `0` or three twins on `h₂` assemble directly, and at share `1` either the shared slot
      -- fires a good `C₄` (`Σ = 3+4+3+4 = 14`) or `h₂`'s twin/slot leaf pair closes via
      -- `two_hub_cherry_pair_nineteen`.
      set C : Finset (Fin 19) := {x, y, z} with hCdef
      have hxD : x ∈ D := (hmemD x).mpr hdegx
      have hyD : y ∈ D := (hmemD y).mpr hdegy
      have hzD : z ∈ D := (hmemD z).mpr hdegz
      have hCsubD : C ⊆ D := by
        rw [hCdef]
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hxD
        · exact hyD
        · exact hzD
      have hCcard : C.card = 3 := by
        rw [hCdef, Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
          Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      set J : Finset (Fin 19) := D \ C with hJdef
      have hJcard : J.card = 6 := by
        rw [hJdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hCsubD, hDcard, hCcard]
      have hJne : ∀ v ∈ J, v ≠ x ∧ v ≠ y ∧ v ≠ z := by
        intro v hv
        rw [hJdef, Finset.mem_sdiff, hCdef] at hv
        have hvC := hv.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvC
        push Not at hvC
        exact hvC
      have hJD : ∀ v ∈ J, v ∈ D := by
        intro v hv
        rw [hJdef, Finset.mem_sdiff] at hv
        exact hv.1
      have hJIso : ∀ v ∈ J, v ∈ Iso := by
        intro v hv
        obtain ⟨hvx, hvy, hvz⟩ := hJne v hv
        exact hisochar v (hJD v hv) hvx hvy hvz
      have hJdeg : ∀ v ∈ J, G.degree v = 3 := fun v hv => (hIsoprop v (hJIso v hv)).1
      have hJiso : ∀ v ∈ J, ∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3 :=
        fun v hv => (hIsoprop v (hJIso v hv)).2
      have hJ3 : ∀ v ∈ J, (G.neighborFinset v ∩ Dᶜ).card = 3 := by
        intro v hv
        have hsub : G.neighborFinset v ⊆ Dᶜ := by
          intro w hw
          rw [G.mem_neighborFinset] at hw
          rw [Finset.mem_compl, hmemD]
          exact hJiso v hv w hw
        rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, hJdeg v hv]
      have hJsum : ∑ v ∈ J, (G.neighborFinset v ∩ Dᶜ).card = 18 := by
        rw [Finset.sum_congr rfl hJ3, Finset.sum_const, smul_eq_mul, hJcard]
      have hsplitND : ∀ v : Fin 19,
          (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
        intro v
        have h1 : G.neighborFinset v ∩ Dᶜ = G.neighborFinset v \ D := by
          ext w
          simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
        rw [h1, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
      have hNxD : G.neighborFinset x ∩ D = {y} := by
        ext w
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨hadj, hwD⟩
          rcases hcov x w hxD hwD hadj with e | e
          · exact absurd e hxy_ne
          · exact e
        · rintro rfl
          exact ⟨hxyA, hyD⟩
      have hNzD : G.neighborFinset z ∩ D = {y} := by
        ext w
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨hadj, hwD⟩
          rcases hcov z w hzD hwD hadj with e | e
          · exact absurd e (Ne.symm hyz_ne)
          · exact e
        · rintro rfl
          exact ⟨hyzA.symm, hyD⟩
      have hNxHub : (G.neighborFinset x ∩ Dᶜ).card = 2 := by
        have h1 := hsplitND x
        rw [hNxD, Finset.card_singleton, hdegx] at h1
        omega
      have hNzHub : (G.neighborFinset z ∩ Dᶜ).card = 2 := by
        have h1 := hsplitND z
        rw [hNzD, Finset.card_singleton, hdegz] at h1
        omega
      have hxzcard : ({x, z} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hxz_ne]), Finset.card_singleton]
      have hNyHub : (G.neighborFinset y ∩ Dᶜ).card = 1 := by
        have h1 := hsplitND y
        rw [hNyD, hxzcard, hdegy] at h1
        omega
      have hCsum : ∑ w ∈ C, (G.neighborFinset w ∩ Dᶜ).card = 5 := by
        rw [hCdef, Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
          Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton, hNxHub, hNyHub, hNzHub]
        omega
      have hisoTot : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ J).card = 18 := by
        rw [cross_count_nineteen G Dᶜ J]
        exact hJsum
      have hslotTot : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ C).card = 5 := by
        rw [cross_count_nineteen G Dᶜ C]
        exact hCsum
      have hJunion : J ∪ C = D := by
        rw [hJdef]
        exact Finset.sdiff_union_of_subset hCsubD
      have hJCdisj : Disjoint J C := by
        rw [hJdef]
        exact Finset.sdiff_disjoint
      have hDJC : ∀ s : Finset (Fin 19), (s ∩ D).card = (s ∩ J).card + (s ∩ C).card := by
        intro s
        rw [← hJunion, Finset.inter_union_distrib_left]
        exact Finset.card_union_of_disjoint
          (hJCdisj.mono Finset.inter_subset_right Finset.inter_subset_right)
      have hperhub : ∀ v : Fin 19, G.degree v = (G.neighborFinset v ∩ J).card
          + (G.neighborFinset v ∩ C).card + (G.neighborFinset v ∩ Dᶜ).card := by
        intro v
        have h1 := hsplitND v
        have h2 := hDJC (G.neighborFinset v)
        omega
      have hsumkey : ∑ h ∈ Dᶜ, G.degree h = ∑ h ∈ Dᶜ, ((G.neighborFinset h ∩ J).card
          + (G.neighborFinset h ∩ C).card + (G.neighborFinset h ∩ Dᶜ).card) :=
        Finset.sum_congr rfl (fun h _ => hperhub h)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumDc, hisoTot, hslotTot] at hsumkey
      have hsumHH : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Dᶜ).card = 18 := by omega
      by_cases hesc : ∃ k ∈ Dᶜ, (G.neighborFinset k ∩ C).card = 0 ∧
          2 ≤ (G.neighborFinset k ∩ J).card
      · -- ESCAPE: a slot-free hub with two `M`-isolated twins against the cherry.
        obtain ⟨k, hkDc, hkC0, hkJ2⟩ := hesc
        obtain ⟨tw₁, htw1m, tw₂, htw2m, htw12⟩ :=
          Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset k ∩ J).card)
        obtain ⟨htw1N, htw1J⟩ := Finset.mem_inter.mp htw1m
        obtain ⟨htw2N, htw2J⟩ := Finset.mem_inter.mp htw2m
        have hAktw1 : G.Adj k tw₁ := (G.mem_neighborFinset _ _).mp htw1N
        have hAktw2 : G.Adj k tw₂ := (G.mem_neighborFinset _ _).mp htw2N
        obtain ⟨htw1x, htw1y, htw1z⟩ := hJne tw₁ htw1J
        obtain ⟨htw2x, htw2y, htw2z⟩ := hJne tw₂ htw2J
        have htw1deg : G.degree tw₁ = 3 := hJdeg tw₁ htw1J
        have htw2deg : G.degree tw₂ = 3 := hJdeg tw₂ htw2J
        have hn1x : ¬G.Adj tw₁ x := fun ha => hJiso tw₁ htw1J x ha hdegx
        have hn1y : ¬G.Adj tw₁ y := fun ha => hJiso tw₁ htw1J y ha hdegy
        have hn1z : ¬G.Adj tw₁ z := fun ha => hJiso tw₁ htw1J z ha hdegz
        have hn2x : ¬G.Adj tw₂ x := fun ha => hJiso tw₂ htw2J x ha hdegx
        have hn2y : ¬G.Adj tw₂ y := fun ha => hJiso tw₂ htw2J y ha hdegy
        have hn2z : ¬G.Adj tw₂ z := fun ha => hJiso tw₂ htw2J z ha hdegz
        have hkCempty : G.neighborFinset k ∩ C = ∅ := Finset.card_eq_zero.mp hkC0
        have hkC : ∀ w : Fin 19, w ∈ C → ¬G.Adj k w := by
          intro w hwC hadj
          have hmem : w ∈ G.neighborFinset k ∩ C :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hwC⟩
          rw [hkCempty] at hmem
          exact absurd hmem (Finset.notMem_empty w)
        have hxC : x ∈ C := by rw [hCdef]; exact Finset.mem_insert_self x {y, z}
        have hyC : y ∈ C := by
          rw [hCdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self y {z})
        have hzC : z ∈ C := by
          rw [hCdef]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
        have hk4 : 4 ≤ G.degree k := hDcdeg4 k hkDc
        have hkx : k ≠ x := by rintro rfl; omega
        have hky : k ≠ y := by rintro rfl; omega
        have hkz : k ≠ z := by rintro rfl; omega
        exact Or.inr (Or.inl ⟨tw₁, tw₂, k, x, y, z, htw1deg, htw2deg, hdeg5all k hkDc,
          hdegx, hdegy, hdegz, hAktw1.symm, hAktw2.symm, hxyA, hyzA,
          hn1x, hn1y, hn1z, hn2x, hn2y, hn2z, hkC x hxC, hkC y hyC, hkC z hzC,
          htw12, htw1x, htw1y, htw1z, htw2x, htw2y, htw2z,
          hkx, hky, hkz, hxy_ne, hyz_ne, hxz_ne⟩)
      · push Not at hesc
        have hIsoD : Iso ⊆ D := fun v hv => (hmemD v).mpr (hIsoprop v hv).1
        -- Good-`C₄` pointwise share bound, restricted to the `J`-twins.
        have hshareJ : ∀ p q : Fin 19, p ∈ Dᶜ → q ∈ Dᶜ → p ≠ q → ¬G.Adj p q →
            G.degree p = 4 → G.degree q = 4 →
            ((G.neighborFinset p ∩ J) ∩ G.neighborFinset q).card ≤ 1 := by
          intro p q hpDc hqDc hpq hnadj hdp hdq
          have hsub : (G.neighborFinset p ∩ J) ∩ G.neighborFinset q
              ⊆ (G.neighborFinset p ∩ G.neighborFinset q) ∩ Iso := by
            intro w hw
            simp only [Finset.mem_inter] at hw ⊢
            exact ⟨⟨hw.1.1, hw.2⟩, hJIso w hw.1.2⟩
          calc ((G.neighborFinset p ∩ J) ∩ G.neighborFinset q).card
              ≤ ((G.neighborFinset p ∩ G.neighborFinset q) ∩ Iso).card :=
                Finset.card_le_card hsub
            _ ≤ 1 := nonadj_deg4_hubs_share_le_one_iso_pointwise G D Iso hC4 hIsoD hIsoprop
                p q hpDc hqDc hdp hdq hpq hnadj
        -- Two private `J`-twins on each side assemble a `TwoHubConfig`.
        have hprivpair : ∀ p q : Fin 19, p ∈ Dᶜ → q ∈ Dᶜ → p ≠ q → ¬G.Adj p q →
            G.degree p = 4 → G.degree q = 4 →
            2 ≤ ((G.neighborFinset p ∩ J) \ G.neighborFinset q).card →
            2 ≤ ((G.neighborFinset q ∩ J) \ G.neighborFinset p).card → TwoHubConfig G := by
          intro p q hpDc hqDc hpq hnadj hdp hdq hp2 hq2
          obtain ⟨a, ham, b, hbm, hab⟩ := Finset.one_lt_card.mp (by omega : 1 <
            ((G.neighborFinset p ∩ J) \ G.neighborFinset q).card)
          obtain ⟨c, hcm, d, hdm, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 <
            ((G.neighborFinset q ∩ J) \ G.neighborFinset p).card)
          obtain ⟨haNJ, haNq⟩ := Finset.mem_sdiff.mp ham
          obtain ⟨haN, haJ⟩ := Finset.mem_inter.mp haNJ
          obtain ⟨hbNJ, hbNq⟩ := Finset.mem_sdiff.mp hbm
          obtain ⟨hbN, hbJ⟩ := Finset.mem_inter.mp hbNJ
          obtain ⟨hcNJ, hcNp⟩ := Finset.mem_sdiff.mp hcm
          obtain ⟨hcN, hcJ⟩ := Finset.mem_inter.mp hcNJ
          obtain ⟨hdNJ, hdNp⟩ := Finset.mem_sdiff.mp hdm
          obtain ⟨hdN, hdJ⟩ := Finset.mem_inter.mp hdNJ
          exact dense_two_hub_assemble G p q a b c d hdp hdq (hJdeg a haJ) (hJdeg b hbJ)
            (hJdeg c hcJ) (hJdeg d hdJ)
            ((G.mem_neighborFinset _ _).mp haN).symm ((G.mem_neighborFinset _ _).mp hbN).symm
            ((G.mem_neighborFinset _ _).mp hcN).symm ((G.mem_neighborFinset _ _).mp hdN).symm
            hnadj
            (fun ha => hcNp ((G.mem_neighborFinset _ _).mpr ha))
            (fun ha => hdNp ((G.mem_neighborFinset _ _).mpr ha))
            (fun ha => haNq ((G.mem_neighborFinset _ _).mpr ha.symm))
            (fun ha => hbNq ((G.mem_neighborFinset _ _).mpr ha.symm))
            (hJiso a haJ) (hJiso b hbJ) hab hcd
        -- Two non-adjacent degree-`4` hubs with `≥ 3` twins each: share `≤ 1` leaves `2` privates.
        have hclassic : ∀ p q : Fin 19, p ∈ Dᶜ → q ∈ Dᶜ → p ≠ q → ¬G.Adj p q →
            G.degree p = 4 → G.degree q = 4 → 3 ≤ (G.neighborFinset p ∩ J).card →
            3 ≤ (G.neighborFinset q ∩ J).card → TwoHubConfig G := by
          intro p q hpDc hqDc hpq hnadj hdp hdq hp3 hq3
          have hs1 := hshareJ p q hpDc hqDc hpq hnadj hdp hdq
          have hs2 := hshareJ q p hqDc hpDc (Ne.symm hpq) (fun ha => hnadj ha.symm) hdq hdp
          have hsd1 := Finset.card_sdiff_add_card_inter (G.neighborFinset p ∩ J)
            (G.neighborFinset q)
          have hsd2 := Finset.card_sdiff_add_card_inter (G.neighborFinset q ∩ J)
            (G.neighborFinset p)
          exact hprivpair p q hpDc hqDc hpq hnadj hdp hdq (by omega) (by omega)
        -- The escape failed: every cherry-avoiding hub carries at most one twin.
        have hSslots0 : ∀ h ∈ S, (G.neighborFinset h ∩ C).card = 0 := by
          intro h hh
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset, hCdef] at hw
          obtain ⟨hadj, hwC⟩ := hw
          obtain ⟨hnx, hny, hnz⟩ := hSavoid h hh
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwC
          rcases hwC with rfl | rfl | rfl
          · exact hnx hadj
          · exact hny hadj
          · exact hnz hadj
        have hStw1 : ∀ h ∈ S, (G.neighborFinset h ∩ J).card ≤ 1 := by
          intro h hh
          have hlt := hesc h (hSsubDc hh) (hSslots0 h hh)
          omega
        have hStwsum : ∑ h ∈ S, (G.neighborFinset h ∩ J).card ≤ S.card := by
          have h1 := Finset.sum_le_card_nsmul S
            (fun h => (G.neighborFinset h ∩ J).card) 1 hStw1
          simpa using h1
        have hSdeg4lb : 4 * S.card ≤ ∑ h ∈ S, G.degree h := by
          have h1 := Finset.card_nsmul_le_sum S (fun h => G.degree h) 4
            (fun h hh => hDcdeg4 h (hSsubDc hh))
          simpa [smul_eq_mul, Nat.mul_comm] using h1
        set T : Finset (Fin 19) := Dᶜ \ S with hTdef
        have hTsub : T ⊆ Dᶜ := by
          rw [hTdef]
          exact Finset.sdiff_subset
        have hTcard : T.card + S.card = 10 := by
          rw [hTdef]
          have h := Finset.card_sdiff_add_card_inter Dᶜ S
          rw [Finset.inter_eq_right.mpr hSsubDc, hDc10] at h
          omega
        have hdegST : ∑ h ∈ T, G.degree h + ∑ h ∈ S, G.degree h = 41 := by
          rw [hTdef]
          exact (Finset.sum_sdiff hSsubDc).trans hsumDc
        have hslST : ∑ h ∈ T, (G.neighborFinset h ∩ C).card
            + ∑ h ∈ S, (G.neighborFinset h ∩ C).card = 5 := by
          rw [hTdef]
          exact (Finset.sum_sdiff hSsubDc).trans hslotTot
        have hhaST : ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card
            + ∑ h ∈ S, (G.neighborFinset h ∩ Dᶜ).card = 18 := by
          rw [hTdef]
          exact (Finset.sum_sdiff hSsubDc).trans hsumHH
        have hSsl0 : ∑ h ∈ S, (G.neighborFinset h ∩ C).card = 0 :=
          Finset.sum_eq_zero hSslots0
        have hTsl5 : ∑ h ∈ T, (G.neighborFinset h ∩ C).card = 5 := by omega
        have hSdegsum : ∑ h ∈ S, G.degree h
            = ∑ h ∈ S, (G.neighborFinset h ∩ J).card
              + ∑ h ∈ S, (G.neighborFinset h ∩ C).card
              + ∑ h ∈ S, (G.neighborFinset h ∩ Dᶜ).card := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun h _ => hperhub h)
        -- Four internally-isolated hubs of total degree `≤ 17` carrying all five slots
        -- always contain two degree-`4` slot-`1` hubs, each with three twins.
        have hfour : ∀ T' : Finset (Fin 19), (∀ h ∈ T', h ∈ Dᶜ) → T'.card = 4 →
            ∑ h ∈ T', G.degree h ≤ 17 →
            ∑ h ∈ T', (G.neighborFinset h ∩ C).card = 5 →
            (∀ h ∈ T', (G.neighborFinset h ∩ Dᶜ).card = 0) → TwoHubConfig G := by
          intro T' hT'sub hT'card hT'deg hT'sl hT'ha
          have hsl1 : ∀ h ∈ T', 1 ≤ (G.neighborFinset h ∩ C).card := by
            intro h hh
            by_contra hcon
            push Not at hcon
            have h0 : (G.neighborFinset h ∩ C).card = 0 := by omega
            have hlt := hesc h (hT'sub h hh) h0
            have hp := hperhub h
            have h4 := hDcdeg4 h (hT'sub h hh)
            have hz := hT'ha h hh
            omega
          have hcards : (T'.filter (fun h => G.degree h = 4
              ∧ (G.neighborFinset h ∩ C).card = 1)).card
              + (T'.filter (fun h => ¬(G.degree h = 4
                ∧ (G.neighborFinset h ∩ C).card = 1))).card = T'.card :=
            Finset.card_filter_add_card_filter_not _
          have hsumsplit : ∑ h ∈ T'.filter (fun h => G.degree h = 4
              ∧ (G.neighborFinset h ∩ C).card = 1),
                (G.degree h + (G.neighborFinset h ∩ C).card)
              + ∑ h ∈ T'.filter (fun h => ¬(G.degree h = 4
                ∧ (G.neighborFinset h ∩ C).card = 1)),
                (G.degree h + (G.neighborFinset h ∩ C).card)
              = ∑ h ∈ T', (G.degree h + (G.neighborFinset h ∩ C).card) :=
            Finset.sum_filter_add_sum_filter_not T' _ _
          have htot : ∑ h ∈ T', (G.degree h + (G.neighborFinset h ∩ C).card)
              = ∑ h ∈ T', G.degree h + ∑ h ∈ T', (G.neighborFinset h ∩ C).card :=
            Finset.sum_add_distrib
          have hlbB : 5 * (T'.filter (fun h => G.degree h = 4
              ∧ (G.neighborFinset h ∩ C).card = 1)).card
              ≤ ∑ h ∈ T'.filter (fun h => G.degree h = 4
                ∧ (G.neighborFinset h ∩ C).card = 1),
                (G.degree h + (G.neighborFinset h ∩ C).card) := by
            have hb : ∀ h ∈ T'.filter (fun h => G.degree h = 4
                ∧ (G.neighborFinset h ∩ C).card = 1),
                5 ≤ G.degree h + (G.neighborFinset h ∩ C).card := by
              intro h hh
              obtain ⟨_, hd, hs⟩ := Finset.mem_filter.mp hh
              omega
            have h1 := Finset.card_nsmul_le_sum (T'.filter (fun h => G.degree h = 4
                ∧ (G.neighborFinset h ∩ C).card = 1))
              (fun h => G.degree h + (G.neighborFinset h ∩ C).card) 5 hb
            simpa [smul_eq_mul, Nat.mul_comm] using h1
          have hlbN : 6 * (T'.filter (fun h => ¬(G.degree h = 4
              ∧ (G.neighborFinset h ∩ C).card = 1))).card
              ≤ ∑ h ∈ T'.filter (fun h => ¬(G.degree h = 4
                ∧ (G.neighborFinset h ∩ C).card = 1)),
                (G.degree h + (G.neighborFinset h ∩ C).card) := by
            have hb : ∀ h ∈ T'.filter (fun h => ¬(G.degree h = 4
                ∧ (G.neighborFinset h ∩ C).card = 1)),
                6 ≤ G.degree h + (G.neighborFinset h ∩ C).card := by
              intro h hh
              obtain ⟨hhT', hnot⟩ := Finset.mem_filter.mp hh
              have h4 := hDcdeg4 h (hT'sub h hhT')
              have h5 := hdeg5all h (hT'sub h hhT')
              have hs := hsl1 h hhT'
              by_cases hd : G.degree h = 4
              · have hne1 : (G.neighborFinset h ∩ C).card ≠ 1 := fun he => hnot ⟨hd, he⟩
                omega
              · omega
            have h1 := Finset.card_nsmul_le_sum (T'.filter (fun h => ¬(G.degree h = 4
                ∧ (G.neighborFinset h ∩ C).card = 1)))
              (fun h => G.degree h + (G.neighborFinset h ∩ C).card) 6 hb
            simpa [smul_eq_mul, Nat.mul_comm] using h1
          obtain ⟨p, hpm, q, hqm, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 <
            (T'.filter (fun h => G.degree h = 4
              ∧ (G.neighborFinset h ∩ C).card = 1)).card)
          obtain ⟨hpT', hdp, hsp⟩ := Finset.mem_filter.mp hpm
          obtain ⟨hqT', hdq, hsq⟩ := Finset.mem_filter.mp hqm
          have hpDc : p ∈ Dᶜ := hT'sub p hpT'
          have hqDc : q ∈ Dᶜ := hT'sub q hqT'
          have hnadjpq : ¬G.Adj p q := by
            intro hadj
            have h0 := hT'ha p hpT'
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
            exact h0 q (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hqDc⟩)
          have htwp : (G.neighborFinset p ∩ J).card = 3 := by
            have hper := hperhub p
            have hz := hT'ha p hpT'
            omega
          have htwq : (G.neighborFinset q ∩ J).card = 3 := by
            have hper := hperhub q
            have hz := hT'ha q hqT'
            omega
          exact hclassic p q hpDc hqDc hpq hnadjpq hdp hdq (by omega) (by omega)
        by_cases hk0 : ∃ k ∈ T, (G.neighborFinset k ∩ C).card = 0
        · -- (A) a slot-free `T`-hub `k`: the ledger pins `|S| = 5`, `∑_S deg = 20`, `deg k = 4`,
          -- and the other four `T`-hubs are internally isolated with all five slots, `∑ deg = 17`.
          obtain ⟨k, hkT, hkC0⟩ := hk0
          have hkDc : k ∈ Dᶜ := hTsub hkT
          have hktw : (G.neighborFinset k ∩ J).card < 2 := hesc k hkDc hkC0
          have hkha3 : 3 ≤ (G.neighborFinset k ∩ Dᶜ).card := by
            have hp := hperhub k
            have h4 := hDcdeg4 k hkDc
            omega
          have hkha_le : (G.neighborFinset k ∩ Dᶜ).card
              ≤ ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card :=
            Finset.single_le_sum (f := fun v => (G.neighborFinset v ∩ Dᶜ).card)
              (fun v _ => Nat.zero_le _) hkT
          have hScard5 : S.card = 5 := by omega
          have hSdeg20 : ∑ h ∈ S, G.degree h = 20 := by omega
          have hTha3 : ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card = 3 := by omega
          have hkha_eq : (G.neighborFinset k ∩ Dᶜ).card = 3 := by omega
          have hkdeg : G.degree k = 4 := by
            have hp := hperhub k
            have h4 := hDcdeg4 k hkDc
            omega
          have hsumha : (G.neighborFinset k ∩ Dᶜ).card
              + ∑ h ∈ T.erase k, (G.neighborFinset h ∩ Dᶜ).card
              = ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card :=
            Finset.add_sum_erase T (fun v => (G.neighborFinset v ∩ Dᶜ).card) hkT
          have hrestha : ∀ h ∈ T.erase k, (G.neighborFinset h ∩ Dᶜ).card = 0 := by
            have hz : ∑ h ∈ T.erase k, (G.neighborFinset h ∩ Dᶜ).card = 0 := by omega
            exact fun h hh => Finset.sum_eq_zero_iff.mp hz h hh
          have hsumdeg : G.degree k + ∑ h ∈ T.erase k, G.degree h = ∑ h ∈ T, G.degree h :=
            Finset.add_sum_erase T (fun v => G.degree v) hkT
          have hsumsl : (G.neighborFinset k ∩ C).card
              + ∑ h ∈ T.erase k, (G.neighborFinset h ∩ C).card
              = ∑ h ∈ T, (G.neighborFinset h ∩ C).card :=
            Finset.add_sum_erase T (fun v => (G.neighborFinset v ∩ C).card) hkT
          have hkcard : (T.erase k).card = 4 := by
            rw [Finset.card_erase_of_mem hkT]
            omega
          exact Or.inr (Or.inr (Or.inl (hfour (T.erase k)
            (fun h hh => hTsub (Finset.mem_of_mem_erase hh)) hkcard (by omega) (by omega)
            hrestha)))
        · push Not at hk0
          rcases (by omega : S.card = 6 ∨ S.card = 5) with hS6c | hS5
          · -- (B) `|S| = 6`: the ledger forces `∑_S deg = 24`, so the four `T`-hubs are
            -- internally isolated of total degree `17` and carry all five cherry slots.
            have hSha18 : ∑ h ∈ S, (G.neighborFinset h ∩ Dᶜ).card = 18 := by omega
            have hTha0sum : ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card = 0 := by omega
            have hTha0 : ∀ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card = 0 :=
              fun h hh => Finset.sum_eq_zero_iff.mp hTha0sum h hh
            have hSdeg24 : ∑ h ∈ S, G.degree h = 24 := by omega
            exact Or.inr (Or.inr (Or.inl (hfour T (fun h hh => hTsub hh) (by omega)
              (by omega) hTsl5 hTha0)))
          · -- (C) `|S| = 5`: all five `T`-hubs carry exactly one cherry slot each.
            have hT5 : T.card = 5 := by omega
            have hsl1T : ∀ h ∈ T, 1 ≤ (G.neighborFinset h ∩ C).card := by
              intro h hh
              have := hk0 h hh
              omega
            have hsl1each : ∀ h ∈ T, (G.neighborFinset h ∩ C).card = 1 := by
              intro h hh
              have hsp : (G.neighborFinset h ∩ C).card
                  + ∑ v ∈ T.erase h, (G.neighborFinset v ∩ C).card
                  = ∑ v ∈ T, (G.neighborFinset v ∩ C).card :=
                Finset.add_sum_erase T (fun v => (G.neighborFinset v ∩ C).card) hh
              have hrest : (T.erase h).card
                  ≤ ∑ v ∈ T.erase h, (G.neighborFinset v ∩ C).card := by
                have h1 := Finset.card_nsmul_le_sum (T.erase h)
                  (fun v => (G.neighborFinset v ∩ C).card) 1
                  (fun v hv => hsl1T v (Finset.mem_of_mem_erase hv))
                simpa using h1
              have hec : (T.erase h).card = 4 := by
                rw [Finset.card_erase_of_mem hh, hT5]
              have h1s := hsl1T h hh
              omega
            have hThale : ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card ≤ 3 := by omega
            have hdeg5uniq : ∀ p : Fin 19, p ∈ Dᶜ → ∀ q : Fin 19, q ∈ Dᶜ → p ≠ q →
                G.degree p = 5 → G.degree q = 5 → False := by
              intro p hp q hq hpq hd5p hd5q
              have hsp1 : G.degree p + ∑ v ∈ Dᶜ.erase p, G.degree v
                  = ∑ v ∈ Dᶜ, G.degree v :=
                Finset.add_sum_erase Dᶜ (fun v => G.degree v) hp
              have hqe : q ∈ Dᶜ.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩
              have hsp2 : G.degree q + ∑ v ∈ (Dᶜ.erase p).erase q, G.degree v
                  = ∑ v ∈ Dᶜ.erase p, G.degree v :=
                Finset.add_sum_erase (Dᶜ.erase p) (fun v => G.degree v) hqe
              have hrest : 4 * ((Dᶜ.erase p).erase q).card
                  ≤ ∑ v ∈ (Dᶜ.erase p).erase q, G.degree v := by
                have h1 := Finset.card_nsmul_le_sum ((Dᶜ.erase p).erase q)
                  (fun v => G.degree v) 4
                  (fun v hv => hDcdeg4 v
                    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv)))
                simpa [smul_eq_mul, Nat.mul_comm] using h1
              have hc2 : ((Dᶜ.erase p).erase q).card = 8 := by
                rw [Finset.card_erase_of_mem hqe, Finset.card_erase_of_mem hp, hDc10]
              rw [hsumDc] at hsp1
              omega
            -- An internally-isolated degree-`4` `T`-hub `h₁` exists (twins `3`).
            have hgood : ∃ h₁ ∈ T, G.degree h₁ = 4 ∧ (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by
              by_contra hcon
              push Not at hcon
              have hcover : ∀ h ∈ T, G.degree h = 5
                  ∨ 1 ≤ (G.neighborFinset h ∩ Dᶜ).card := by
                intro h hh
                have h4 := hDcdeg4 h (hTsub hh)
                have h5 := hdeg5all h (hTsub hh)
                by_cases hd : G.degree h = 4
                · have h1 := hcon h hh hd
                  omega
                · omega
              have hsub2 : T ⊆ T.filter (fun h => G.degree h = 5)
                  ∪ T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Dᶜ).card) := by
                intro h hh
                rcases hcover h hh with h5 | hha
                · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hh, h5⟩)
                · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hh, hha⟩)
              have hF5 : (T.filter (fun h => G.degree h = 5)).card ≤ 1 := by
                by_contra hc2
                push Not at hc2
                obtain ⟨p, hpm, q, hqm, hpq⟩ := Finset.one_lt_card.mp hc2
                obtain ⟨hpT, hp5⟩ := Finset.mem_filter.mp hpm
                obtain ⟨hqT, hq5⟩ := Finset.mem_filter.mp hqm
                exact hdeg5uniq p (hTsub hpT) q (hTsub hqT) hpq hp5 hq5
              have hFha : (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Dᶜ).card)).card
                  ≤ ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card := by
                calc (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Dᶜ).card)).card
                    ≤ ∑ h ∈ T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Dᶜ).card),
                        (G.neighborFinset h ∩ Dᶜ).card := by
                      have h1 := Finset.card_nsmul_le_sum
                        (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Dᶜ).card))
                        (fun h => (G.neighborFinset h ∩ Dᶜ).card) 1
                        (fun h hh => (Finset.mem_filter.mp hh).2)
                      simpa using h1
                  _ ≤ ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card :=
                      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
              have hcardle : T.card ≤ (T.filter (fun h => G.degree h = 5)).card
                  + (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Dᶜ).card)).card := by
                calc T.card ≤ (T.filter (fun h => G.degree h = 5)
                    ∪ T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Dᶜ).card)).card :=
                      Finset.card_le_card hsub2
                  _ ≤ _ := Finset.card_union_le _ _
              omega
            obtain ⟨h₁, hh₁T, hd₁, hha₁⟩ := hgood
            -- A second degree-`4` `T`-hub `h₂` of internal degree `≤ 1` exists (twins `≥ 2`).
            have hgood2 : ∃ h₂ ∈ T.erase h₁, G.degree h₂ = 4 ∧
                (G.neighborFinset h₂ ∩ Dᶜ).card ≤ 1 := by
              by_contra hcon
              push Not at hcon
              have hcover : ∀ h ∈ T.erase h₁, G.degree h = 5
                  ∨ 2 ≤ (G.neighborFinset h ∩ Dᶜ).card := by
                intro h hh
                have hhT := Finset.mem_of_mem_erase hh
                have h4 := hDcdeg4 h (hTsub hhT)
                have h5 := hdeg5all h (hTsub hhT)
                by_cases hd : G.degree h = 4
                · have h1 := hcon h hh hd
                  omega
                · omega
              have hsub2 : T.erase h₁ ⊆ (T.erase h₁).filter (fun h => G.degree h = 5)
                  ∪ (T.erase h₁).filter (fun h => 2 ≤ (G.neighborFinset h ∩ Dᶜ).card) := by
                intro h hh
                rcases hcover h hh with h5 | hha
                · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hh, h5⟩)
                · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hh, hha⟩)
              have hF5 : ((T.erase h₁).filter (fun h => G.degree h = 5)).card ≤ 1 := by
                by_contra hc2
                push Not at hc2
                obtain ⟨p, hpm, q, hqm, hpq⟩ := Finset.one_lt_card.mp hc2
                obtain ⟨hpT, hp5⟩ := Finset.mem_filter.mp hpm
                obtain ⟨hqT, hq5⟩ := Finset.mem_filter.mp hqm
                exact hdeg5uniq p (hTsub (Finset.mem_of_mem_erase hpT)) q
                  (hTsub (Finset.mem_of_mem_erase hqT)) hpq hp5 hq5
              have hsum2 : (G.neighborFinset h₁ ∩ Dᶜ).card
                  + ∑ h ∈ T.erase h₁, (G.neighborFinset h ∩ Dᶜ).card
                  = ∑ h ∈ T, (G.neighborFinset h ∩ Dᶜ).card :=
                Finset.add_sum_erase T (fun v => (G.neighborFinset v ∩ Dᶜ).card) hh₁T
              have hFha : 2 * ((T.erase h₁).filter
                  (fun h => 2 ≤ (G.neighborFinset h ∩ Dᶜ).card)).card
                  ≤ ∑ h ∈ T.erase h₁, (G.neighborFinset h ∩ Dᶜ).card := by
                calc 2 * ((T.erase h₁).filter
                    (fun h => 2 ≤ (G.neighborFinset h ∩ Dᶜ).card)).card
                    ≤ ∑ h ∈ (T.erase h₁).filter
                        (fun h => 2 ≤ (G.neighborFinset h ∩ Dᶜ).card),
                        (G.neighborFinset h ∩ Dᶜ).card := by
                      have h1 := Finset.card_nsmul_le_sum ((T.erase h₁).filter
                          (fun h => 2 ≤ (G.neighborFinset h ∩ Dᶜ).card))
                        (fun h => (G.neighborFinset h ∩ Dᶜ).card) 2
                        (fun h hh => (Finset.mem_filter.mp hh).2)
                      simpa [smul_eq_mul, Nat.mul_comm] using h1
                  _ ≤ ∑ h ∈ T.erase h₁, (G.neighborFinset h ∩ Dᶜ).card :=
                      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
              have hec : (T.erase h₁).card = 4 := by
                rw [Finset.card_erase_of_mem hh₁T, hT5]
              have hcardle : (T.erase h₁).card
                  ≤ ((T.erase h₁).filter (fun h => G.degree h = 5)).card
                  + ((T.erase h₁).filter
                    (fun h => 2 ≤ (G.neighborFinset h ∩ Dᶜ).card)).card := by
                calc (T.erase h₁).card ≤ ((T.erase h₁).filter (fun h => G.degree h = 5)
                    ∪ (T.erase h₁).filter
                      (fun h => 2 ≤ (G.neighborFinset h ∩ Dᶜ).card)).card :=
                      Finset.card_le_card hsub2
                  _ ≤ _ := Finset.card_union_le _ _
              omega
            obtain ⟨h₂, hh₂e, hd₂, hha₂⟩ := hgood2
            have hh₂T : h₂ ∈ T := Finset.mem_of_mem_erase hh₂e
            have hne12 : h₂ ≠ h₁ := (Finset.mem_erase.mp hh₂e).1
            have hh₁Dc : h₁ ∈ Dᶜ := hTsub hh₁T
            have hh₂Dc : h₂ ∈ Dᶜ := hTsub hh₂T
            have hnadj12 : ¬G.Adj h₁ h₂ := by
              intro hadj
              have h0 := hha₁
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
              exact h0 h₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh₂Dc⟩)
            have htw₁ : (G.neighborFinset h₁ ∩ J).card = 3 := by
              have hper := hperhub h₁
              have hs := hsl1each h₁ hh₁T
              omega
            have htw₂ : 2 ≤ (G.neighborFinset h₂ ∩ J).card := by
              have hper := hperhub h₂
              have hs := hsl1each h₂ hh₂T
              omega
            rcases (by omega : 3 ≤ (G.neighborFinset h₂ ∩ J).card
                ∨ (G.neighborFinset h₂ ∩ J).card = 2) with htw₂3 | htw₂2
            · exact Or.inr (Or.inr (Or.inl (hclassic h₁ h₂ hh₁Dc hh₂Dc (Ne.symm hne12)
                hnadj12 hd₁ hd₂ (by omega) htw₂3)))
            · by_cases hsJ0 : ((G.neighborFinset h₁ ∩ J) ∩ G.neighborFinset h₂).card = 0
              · -- share `0`: the private twins are the full twin sets (`3` and `2`).
                have hsymmJ : (G.neighborFinset h₂ ∩ J) ∩ G.neighborFinset h₁
                    = (G.neighborFinset h₁ ∩ J) ∩ G.neighborFinset h₂ := by
                  ext w
                  simp only [Finset.mem_inter]
                  constructor
                  · rintro ⟨⟨hw1, hw2⟩, hw3⟩
                    exact ⟨⟨hw3, hw2⟩, hw1⟩
                  · rintro ⟨⟨hw1, hw2⟩, hw3⟩
                    exact ⟨⟨hw3, hw2⟩, hw1⟩
                have hsd1 := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ J)
                  (G.neighborFinset h₂)
                have hsd2 := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ J)
                  (G.neighborFinset h₁)
                rw [hsymmJ] at hsd2
                exact Or.inr (Or.inr (Or.inl (hprivpair h₁ h₂ hh₁Dc hh₂Dc (Ne.symm hne12)
                  hnadj12 hd₁ hd₂ (by omega) (by omega))))
              · -- share exactly one twin `t`.
                have hsJ1 : ((G.neighborFinset h₁ ∩ J) ∩ G.neighborFinset h₂).card = 1 := by
                  have hle := hshareJ h₁ h₂ hh₁Dc hh₂Dc (Ne.symm hne12) hnadj12 hd₁ hd₂
                  omega
                obtain ⟨t, htm⟩ := Finset.card_eq_one.mp hsJ1
                have htmem : t ∈ (G.neighborFinset h₁ ∩ J) ∩ G.neighborFinset h₂ := by
                  rw [htm]
                  exact Finset.mem_singleton_self t
                obtain ⟨htNJ, htN₂⟩ := Finset.mem_inter.mp htmem
                obtain ⟨htN₁, htJ⟩ := Finset.mem_inter.mp htNJ
                have hAh₁t : G.Adj h₁ t := (G.mem_neighborFinset _ _).mp htN₁
                have hAh₂t : G.Adj h₂ t := (G.mem_neighborFinset _ _).mp htN₂
                have htdeg : G.degree t = 3 := hJdeg t htJ
                have htw₂mem : t ∈ G.neighborFinset h₂ ∩ J := Finset.mem_inter.mpr ⟨htN₂, htJ⟩
                have huex : ((G.neighborFinset h₂ ∩ J).erase t).card = 1 := by
                  rw [Finset.card_erase_of_mem htw₂mem, htw₂2]
                obtain ⟨u, hum⟩ := Finset.card_eq_one.mp huex
                have humem : u ∈ (G.neighborFinset h₂ ∩ J).erase t := by
                  rw [hum]
                  exact Finset.mem_singleton_self u
                have hut : u ≠ t := (Finset.mem_erase.mp humem).1
                obtain ⟨huN₂, huJ⟩ := Finset.mem_inter.mp (Finset.mem_of_mem_erase humem)
                have hAh₂u : G.Adj h₂ u := (G.mem_neighborFinset _ _).mp huN₂
                have hnAh₁u : ¬G.Adj h₁ u := by
                  intro hadj
                  have hu2 : u ∈ (G.neighborFinset h₁ ∩ J) ∩ G.neighborFinset h₂ :=
                    Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
                      ⟨(G.mem_neighborFinset _ _).mpr hadj, huJ⟩, huN₂⟩
                  rw [htm, Finset.mem_singleton] at hu2
                  exact hut hu2
                have hslh₂ : (G.neighborFinset h₂ ∩ C).card = 1 := hsl1each h₂ hh₂T
                obtain ⟨c₂, hc₂m⟩ := Finset.card_eq_one.mp hslh₂
                have hc₂mem : c₂ ∈ G.neighborFinset h₂ ∩ C := by
                  rw [hc₂m]
                  exact Finset.mem_singleton_self c₂
                obtain ⟨hc₂N, hc₂C⟩ := Finset.mem_inter.mp hc₂mem
                have hAh₂c₂ : G.Adj h₂ c₂ := (G.mem_neighborFinset _ _).mp hc₂N
                have hc₂C' := hc₂C
                rw [hCdef] at hc₂C'
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc₂C'
                have hc₂deg : G.degree c₂ = 3 := by
                  rcases hc₂C' with rfl | rfl | rfl
                  · exact hdegx
                  · exact hdegy
                  · exact hdegz
                have hJneC : ∀ v ∈ J, v ≠ c₂ := by
                  intro v hv
                  obtain ⟨hvx, hvy, hvz⟩ := hJne v hv
                  rcases hc₂C' with rfl | rfl | rfl
                  · exact hvx
                  · exact hvy
                  · exact hvz
                by_cases hAh₁c₂ : G.Adj h₁ c₂
                · -- `h₁, h₂` share the twin `t` AND the slot `c₂`: good `C₄`, excluded.
                  exfalso
                  apply hC4
                  refine ⟨c₂, h₁, t, h₂, ?_, hAh₁c₂.symm, hAh₁t, hAh₂t.symm, hAh₂c₂, ?_,
                    hnadj12, ?_⟩
                  · exact card_four_nineteen c₂ h₁ t h₂ (by rintro rfl; omega)
                      (Ne.symm (hJneC t htJ)) (by rintro rfl; omega) (by rintro rfl; omega)
                      (Ne.symm hne12) (by rintro rfl; omega)
                  · exact fun ha => hJiso t htJ c₂ ha.symm hc₂deg
                  · omega
                · -- otherwise assemble with the `h₂`-leaves `u` (twin) and `c₂` (slot).
                  have hsd1 := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ J)
                    (G.neighborFinset h₂)
                  obtain ⟨a, ham, b, hbm, hab⟩ := Finset.one_lt_card.mp (by omega : 1 <
                    ((G.neighborFinset h₁ ∩ J) \ G.neighborFinset h₂).card)
                  obtain ⟨haNJ, haN₂⟩ := Finset.mem_sdiff.mp ham
                  obtain ⟨haN₁, haJ⟩ := Finset.mem_inter.mp haNJ
                  obtain ⟨hbNJ, hbN₂⟩ := Finset.mem_sdiff.mp hbm
                  obtain ⟨hbN₁, hbJ⟩ := Finset.mem_inter.mp hbNJ
                  exact Or.inr (Or.inr (Or.inl (two_hub_cherry_pair_nineteen G h₁ h₂ a b u c₂
                    hd₁ hd₂ (hJdeg a haJ) (hJdeg b hbJ) (hJdeg u huJ) hc₂deg
                    ((G.mem_neighborFinset _ _).mp haN₁).symm
                    ((G.mem_neighborFinset _ _).mp hbN₁).symm
                    hAh₂u.symm hAh₂c₂.symm hnadj12 hnAh₁u hAh₁c₂
                    (fun ha => haN₂ ((G.mem_neighborFinset _ _).mpr ha.symm))
                    (fun ha => hbN₂ ((G.mem_neighborFinset _ _).mpr ha.symm))
                    (fun ha => hJiso a haJ u ha (hJdeg u huJ))
                    (fun ha => hJiso a haJ c₂ ha hc₂deg)
                    (fun ha => hJiso b hbJ u ha (hJdeg u huJ))
                    (fun ha => hJiso b hbJ c₂ ha hc₂deg)
                    hab (hJneC u huJ)
                    (by rintro rfl; exact hnAh₁u ((G.mem_neighborFinset _ _).mp haN₁))
                    (hJneC a haJ)
                    (by rintro rfl; exact hnAh₁u ((G.mem_neighborFinset _ _).mp hbN₁))
                    (hJneC b hbJ))))

end N19

end ACMax
