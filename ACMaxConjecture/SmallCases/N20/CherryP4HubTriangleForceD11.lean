import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleWA

/-!
# The `n = 20`, `P₄`-cherry `|D| = 11` hub-triangle force kill (standalone leaf)

At `n = 20` with `|D| = 11` the hub set `Dᶜ` has `9` hubs, `∑_{Dᶜ} deg = 39`, and internal edge
total `∑_{Dᶜ} (N ∩ Dᶜ).card = 12`.  The two cherry-avoider sets `A₁` (avoiding `{L₁, c₁, c₂}`) and
`A₂` (avoiding `{c₁, c₂, L₂}`) each have `≥ 5` hubs, with internal degree `≥ 2` on avoiders and
`≥ 3` on the fully-free set `FF = A₁ ∩ A₂`.

* **Clean case** (every hub has degree `≤ 5`): the budget `∑_{Dᶜ} int = 12 < 15 = 3·5` is
  impossible for two size-`≥ 5` avoider sets with the internal-degree bounds (`budget_contra_gen`).
* **Exceptional case** (some hub has degree `≥ 6`): the budget forces `|FF| ≥ 5`
  (`ff_card_ge_of_budget`), and combined with `3·|FF \ {h₆}| ≤ 12` this pins the four
  degree-`≤ 5` fully-free hubs to internal degree exactly `3`, all internal mass concentrated on
  them, so they form a `K₄`.  Any three of them are pairwise-adjacent degree-`4` hubs avoiding the
  cherry with degree sum `12 ≤ 13`, contradicting `hntri1`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **All-degree-`≤ 5` budget contradiction.**  Two avoider sets `A₁`, `A₂` of size `≥ m` with
internal degree `≥ 2` (and `≥ 3` on `FF = A₁ ∩ A₂`) inside a hub set `Dc` of internal total `S`
force `S ≥ 3m`; if `S < 3m` this is impossible. -/
theorem budget_contra_gen (Dc A1 A2 FF : Finset (Fin 20)) (f : Fin 20 → ℕ) (m S : ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : m ≤ A1.card) (hA2card : m ≤ A2.card)
    (hint2 : ∀ g ∈ A1, 2 ≤ f g) (hint2' : ∀ g ∈ A2, 2 ≤ f g) (hFFint : ∀ g ∈ FF, 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = S) (hlt : S < 3 * m) : False := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hUle : ∑ g ∈ A1 ∪ A2, f g ≤ S := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := Finset.union_sdiff_self_eq_union
  have hUsplit : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hA1mf_ge : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) f 2
      (fun g hg => hint2 g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFF_ge : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
    have := Finset.card_sdiff_add_card_inter A1 FF
    rwa [Finset.inter_eq_right.mpr hFFsubA1] at this
  have hA2mA1_ge : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) f 2
      (fun g hg => hint2' g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFF, Finset.inter_comm]
  have hA2mA1card : (A2 \ A1).card + FF.card = A2.card := by
    rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  omega

/-- **Budget floor on the fully-free set (exceptional hub `h₆`).**  Two avoider sets `A₁`, `A₂`
of size `≥ 5` with internal degree `≥ 2` off `h₆` (and `≥ 3` on `FF = A₁ ∩ A₂` off `h₆`) inside a
hub set `Dc` of internal total `12` force `|FF| ≥ 5`.  (Dropping the single exceptional hub `h₆`
costs at most `3`, so `12 ≥ 2(|A₁| + |A₂|) − |FF| − 3 ≥ 17 − |FF|`.) -/
theorem ff_card_ge_of_budget (Dc A1 A2 FF : Finset (Fin 20)) (f : Fin 20 → ℕ) (h6 : Fin 20)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : 5 ≤ A1.card) (hA2card : 5 ≤ A2.card)
    (hint2 : ∀ g ∈ A1, g ≠ h6 → 2 ≤ f g) (hint2' : ∀ g ∈ A2, g ≠ h6 → 2 ≤ f g)
    (hFFint : ∀ g ∈ FF, g ≠ h6 → 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = 12) : 5 ≤ FF.card := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  set U := A1 ∪ A2 with hUdef
  have hUle : ∑ g ∈ U, f g ≤ 12 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hFFsubU : FF ⊆ U := hFFsubA1.trans Finset.subset_union_left
  set Ue := U.erase h6 with hUedef
  set FFe := FF.erase h6 with hFFedef
  have hFFeU : FFe ⊆ Ue := by
    rw [hFFedef, hUedef]; exact Finset.erase_subset_erase _ hFFsubU
  have hUeU : Ue ⊆ U := Finset.erase_subset _ _
  have hdrop : ∑ g ∈ Ue, f g ≤ ∑ g ∈ U, f g :=
    Finset.sum_le_sum_of_subset_of_nonneg hUeU (fun _ _ _ => Nat.zero_le _)
  have hUe2 : ∀ g ∈ Ue, 2 ≤ f g := by
    intro g hg
    have hgne : g ≠ h6 := Finset.ne_of_mem_erase hg
    have hgU : g ∈ U := hUeU hg
    rcases Finset.mem_union.mp hgU with hg1 | hg2
    · exact hint2 g hg1 hgne
    · exact hint2' g hg2 hgne
  have hFFe3 : ∀ g ∈ FFe, 3 ≤ f g := by
    intro g hg
    exact hFFint g (Finset.mem_of_mem_erase hg) (Finset.ne_of_mem_erase hg)
  have hsplit : (∑ g ∈ Ue \ FFe, f g) + ∑ g ∈ FFe, f g = ∑ g ∈ Ue, f g :=
    Finset.sum_sdiff hFFeU
  have hdiff_ge : 2 * (Ue \ FFe).card ≤ ∑ g ∈ Ue \ FFe, f g := by
    have := Finset.card_nsmul_le_sum (Ue \ FFe) f 2
      (fun g hg => hUe2 g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFFe_ge : 3 * FFe.card ≤ ∑ g ∈ FFe, f g := by
    have := Finset.card_nsmul_le_sum FFe f 3 hFFe3
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hdiffcard : (Ue \ FFe).card + FFe.card = Ue.card := by
    have := Finset.card_sdiff_add_card_inter Ue FFe
    rwa [Finset.inter_eq_right.mpr hFFeU] at this
  have hUecard : Ue.card + 1 ≥ U.card := by
    rw [hUedef]
    by_cases hh6 : h6 ∈ U
    · rw [Finset.card_erase_of_mem hh6]; omega
    · rw [Finset.erase_eq_of_notMem hh6]; omega
  have hFFecard : FFe.card + 1 ≥ FF.card := by
    rw [hFFedef]
    by_cases hh6 : h6 ∈ FF
    · rw [Finset.card_erase_of_mem hh6]; omega
    · rw [Finset.erase_eq_of_notMem hh6]; omega
  have hUcard : U.card + FF.card = A1.card + A2.card := by
    rw [hUdef, hFF]; exact Finset.card_union_add_card_inter A1 A2
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  have hA1leU : A1.card ≤ U.card := Finset.card_le_card Finset.subset_union_left
  omega

/-- **The `n = 20`, `P₄`-cherry `|D| = 11` hub-triangle force kill.**  Under the residual structural
counts (`Dᶜ.card = 9`, `∑ deg = 39`, `∑ int = 12`, per-hub degree decomposition, the cherry hub
counts), `¬TwoTwinConfig`, and the falsity of a pairwise-adjacent cherry-avoiding hub triangle of
degree sum `≤ 13` (`hntri1`), the corner is contradictory. -/
theorem iso_rich_force_p4_d11_twenty (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ : Fin 20)
    (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G)
    (hntri1 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hDccard : Dᶜ.card = 9)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hsumdeg : ∑ g ∈ Dᶜ, G.degree g = 39)
    (hsumInternal : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 12)
    (hper : ∀ g : Fin 20, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = G.degree g) :
    False := by
  classical
  set P : Finset (Fin 20) := {L₁, c₁, c₂, L₂} with hPdef
  have hge4 : ∀ g : Fin 20, g ∈ Dᶜ → 4 ≤ G.degree g := by
    intro g hg
    have hgD : g ∉ D := Finset.mem_compl.mp hg
    have hne3 : G.degree g ≠ 3 := fun he => hgD ((hmemD g).mpr he)
    have := h3 g
    omega
  have hW := cherry_p4_W_facts_twenty G D Iso L₁ c₁ c₂ L₂ hIsoprop hL1deg hc1deg hc2deg hL2deg
    hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hL1D hc1D hc2D hL2D htt
  have hclassP : ∀ x : Fin 20, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    by_cases h1 : x = L₁
    · exact Or.inl h1
    by_cases h2 : x = c₁
    · exact Or.inr (Or.inl h2)
    by_cases h3' : x = c₂
    · exact Or.inr (Or.inr (Or.inl h3'))
    by_cases h4 : x = L₂
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hisochar x hx h1 h2 h3' h4))))
  set A1 := Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hA1def
  set A2 := Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hA2def
  set FF := A1 ∩ A2 with hFFdef
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsubA1 : FF ⊆ A1 := by rw [hFFdef]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFFdef]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dᶜ := hFFsubA1.trans hA1sub
  have hA1c5 : 5 ≤ A1.card := by
    have h := avoiders_ge_gen G D L₁ c₁ c₂ (by rw [hL1hub, hc1hub, hc2hub])
    rw [← hA1def, hDccard] at h; omega
  have hA2c5 : 5 ≤ A2.card := by
    have h := avoiders_ge_gen G D c₁ c₂ L₂ (by rw [hc1hub, hc2hub, hL2hub])
    rw [← hA2def, hDccard] at h; omega
  have hclassA1 : ∀ g : Fin 20, g ∈ A1 → ∀ x : Fin 20, G.Adj g x → x ∈ D → x = L₂ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hclassA2 : ∀ g : Fin 20, g ∈ A2 → ∀ x : Fin 20, G.Adj g x → x ∈ D → x = L₁ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨_, hgc1, hgc2, hgL2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hclassFF : ∀ g : Fin 20, g ∈ FF → ∀ x : Fin 20, G.Adj g x → x ∈ D → x ∈ Iso := by
    intro g hg x hadj hxD
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hgA1
    obtain ⟨_, _, _, hgL2⟩ := hgA2
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact h
  have getA1pred : ∀ g : Fin 20, g ∈ A1 →
      ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ := by
    intro g hg; rw [hA1def, Finset.mem_filter] at hg; exact hg.2
  have getA2pred : ∀ g : Fin 20, g ∈ A2 →
      ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
    intro g hg; rw [hA2def, Finset.mem_filter] at hg; exact hg.2
  by_cases hex6 : ∃ h6 : Fin 20, h6 ∈ Dᶜ ∧ 6 ≤ G.degree h6
  · -- **Exceptional case**: a hub of degree `≥ 6`.
    obtain ⟨h6, hh6Dc, hh6deg⟩ := hex6
    have herase : G.degree h6 + ∑ x ∈ Dᶜ.erase h6, G.degree x = 39 := by
      have h := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hh6Dc
      rw [hsumdeg] at h; exact h
    have hother5 : ∀ g : Fin 20, g ∈ Dᶜ → g ≠ h6 → G.degree g ≤ 5 := by
      intro g hg hgne
      have hub := hub_deg_upper_pt (Dᶜ.erase h6) (fun v => G.degree v)
        (∑ x ∈ Dᶜ.erase h6, G.degree x)
        (fun x hx => hge4 x (Finset.mem_of_mem_erase hx)) rfl g (Finset.mem_erase.mpr ⟨hgne, hg⟩)
      rw [Finset.card_erase_of_mem hh6Dc, hDccard] at hub
      omega
    have hA1int : ∀ g ∈ A1, g ≠ h6 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg hgne
      exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
        (hW g (hA1sub hg) (hother5 g (hA1sub hg) hgne) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
    have hA2int : ∀ g ∈ A2, g ≠ h6 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg hgne
      exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
        (hW g (hA2sub hg) (hother5 g (hA2sub hg) hgne) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
    have hFFint : ∀ g ∈ FF, g ≠ h6 → 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg hgne
      exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
        (hW g (hFFsub hg) (hother5 g (hFFsub hg) hgne)
          (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
    have hFFge5 : 5 ≤ FF.card := ff_card_ge_of_budget Dᶜ A1 A2 FF
      (fun g => (G.neighborFinset g ∩ Dᶜ).card) h6 hA1sub hA2sub hFFdef hA1c5 hA2c5
      hA1int hA2int hFFint hsumInternal
    set FF5 := FF.erase h6 with hFF5def
    have hFF5sub : FF5 ⊆ Dᶜ := (Finset.erase_subset _ _).trans hFFsub
    have hFF5card_ge : 4 ≤ FF5.card := by
      rw [hFF5def]
      by_cases hh6FF : h6 ∈ FF
      · rw [Finset.card_erase_of_mem hh6FF]; omega
      · rw [Finset.erase_eq_of_notMem hh6FF]; omega
    have hFF5int : ∀ g ∈ FF5, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact hFFint g (Finset.mem_of_mem_erase hg) (Finset.ne_of_mem_erase hg)
    have hFF5sum_ge : 3 * FF5.card ≤ ∑ g ∈ FF5, (G.neighborFinset g ∩ Dᶜ).card := by
      have := Finset.card_nsmul_le_sum FF5 (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 hFF5int
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hFF5sum_le : ∑ g ∈ FF5, (G.neighborFinset g ∩ Dᶜ).card ≤ 12 := by
      rw [← hsumInternal]
      exact Finset.sum_le_sum_of_subset_of_nonneg hFF5sub (fun _ _ _ => Nat.zero_le _)
    have hFF5card4 : FF5.card = 4 := by omega
    have hFF5sum12 : ∑ g ∈ FF5, (G.neighborFinset g ∩ Dᶜ).card = 12 := by omega
    have hcompl_sum : ∑ g ∈ Dᶜ \ FF5, (G.neighborFinset g ∩ Dᶜ).card = 0 := by
      have hsplit : (∑ g ∈ Dᶜ \ FF5, (G.neighborFinset g ∩ Dᶜ).card)
          + ∑ g ∈ FF5, (G.neighborFinset g ∩ Dᶜ).card
          = ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card := Finset.sum_sdiff hFF5sub
      rw [hsumInternal, hFF5sum12] at hsplit; omega
    have hzero : ∀ w ∈ Dᶜ \ FF5, (G.neighborFinset w ∩ Dᶜ).card = 0 :=
      fun w hw => (Finset.sum_eq_zero_iff.mp hcompl_sum) w hw
    have heq_all : ∀ g ∈ FF5, G.neighborFinset g ∩ Dᶜ = FF5.erase g := by
      intro g hg
      have hsub : G.neighborFinset g ∩ Dᶜ ⊆ FF5.erase g := by
        intro w hw
        rw [Finset.mem_inter] at hw
        obtain ⟨hwN, hwDc⟩ := hw
        have hwadj : G.Adj g w := (G.mem_neighborFinset g w).mp hwN
        refine Finset.mem_erase.mpr ⟨(G.ne_of_adj hwadj).symm, ?_⟩
        by_contra hwFF5
        have hwsdiff : w ∈ Dᶜ \ FF5 := Finset.mem_sdiff.mpr ⟨hwDc, hwFF5⟩
        have hzw : (G.neighborFinset w ∩ Dᶜ).card = 0 := hzero w hwsdiff
        have hgN : g ∈ G.neighborFinset w ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w g).mpr hwadj.symm, hFF5sub hg⟩
        rw [Finset.card_eq_zero] at hzw
        rw [hzw] at hgN
        exact Finset.notMem_empty g hgN
      have hcard_le : (FF5.erase g).card ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        have h3g := hFF5int g hg
        rw [Finset.card_erase_of_mem hg, hFF5card4]; omega
      exact Finset.eq_of_subset_of_card_le hsub hcard_le
    have hint3 : ∀ g ∈ FF5, (G.neighborFinset g ∩ Dᶜ).card = 3 := by
      intro g hg
      rw [heq_all g hg, Finset.card_erase_of_mem hg, hFF5card4]
    have hadj_all : ∀ g ∈ FF5, ∀ g' ∈ FF5, g ≠ g' → G.Adj g g' := by
      intro g hg g' hg' hne
      have hmem : g' ∈ G.neighborFinset g ∩ Dᶜ := by
        rw [heq_all g hg]; exact Finset.mem_erase.mpr ⟨hne.symm, hg'⟩
      exact (G.mem_neighborFinset g g').mp (Finset.mem_inter.mp hmem).1
    have hdeg4 : ∀ g ∈ FF5, G.degree g = 4 := by
      intro g hg
      have hgFF := Finset.mem_of_mem_erase hg
      have hgne := Finset.ne_of_mem_erase hg
      have hgDc := hFF5sub hg
      have hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1 :=
        hW g hgDc (hother5 g hgDc hgne) (Or.inl (getA1pred g (hFFsubA1 hgFF)))
      have hP0 : (G.neighborFinset g ∩ P).card = 0 := by
        rw [Finset.card_eq_zero]
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_inter, G.mem_neighborFinset] at hx
        obtain ⟨hadjx, hxP⟩ := hx
        obtain ⟨hgL1, hgc1, hgc2⟩ := getA1pred g (hFFsubA1 hgFF)
        obtain ⟨_, _, hgL2⟩ := getA2pred g (hFFsubA2 hgFF)
        rw [hPdef] at hxP
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
        rcases hxP with rfl | rfl | rfl | rfl
        · exact hgL1 hadjx
        · exact hgc1 hadjx
        · exact hgc2 hadjx
        · exact hgL2 hadjx
      have hperg := hper g hgDc
      have hi3 := hint3 g hg
      have hge4g := hge4 g hgDc
      omega
    have h2lt : 2 < FF5.card := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h2lt
    exact hntri1 ⟨a, b, c, hFF5sub ha, hFF5sub hb, hFF5sub hc,
      hadj_all a ha b hb hab, hadj_all a ha c hc hac, hadj_all b hb c hc hbc,
      getA1pred a (hFFsubA1 (Finset.mem_of_mem_erase ha)),
      getA1pred b (hFFsubA1 (Finset.mem_of_mem_erase hb)),
      getA1pred c (hFFsubA1 (Finset.mem_of_mem_erase hc)),
      by have e1 := hdeg4 a ha; have e2 := hdeg4 b hb; have e3 := hdeg4 c hc; omega⟩
  · -- **Clean case**: every hub has degree `≤ 5`.
    push Not at hex6
    have hdeg5 : ∀ g : Fin 20, g ∈ Dᶜ → G.degree g ≤ 5 := by
      intro g hg; have := hex6 g hg; omega
    have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
        (hW g (hA1sub hg) (hdeg5 g (hA1sub hg)) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
    have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
        (hW g (hA2sub hg) (hdeg5 g (hA2sub hg)) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
    have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
        (hW g (hFFsub hg) (hdeg5 g (hFFsub hg)) (Or.inl (getA1pred g (hFFsubA1 hg))))
        (hclassFF g hg)
    exact budget_contra_gen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 5 12
      hA1sub hA2sub hFFdef hA1c5 hA2c5 hA1int hA2int hFFint hsumInternal (by omega)

end N20

end ACMax
