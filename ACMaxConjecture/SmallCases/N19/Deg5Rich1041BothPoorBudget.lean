import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5RichCap
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Blocker
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041OctaPoorCounts

/-! # CASE C both-poor: the budget foundation (`n = 19`)

Derives the poor/`Z` budget for the both-poor regime: the 4th poor hub `w`
(deg 4, isoDeg 1, adjacent to `p` or `q`), `deg z = 3`, and the rich–rich edge
bound `e_RR ≤ 1` (`∑_R richDeg ≤ 2`).  The provable foundation of the both-poor
config kill (`octahedron_both_poor_core`). -/

namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The both-poor budget.**  Extracts the 4th poor hub and the edge counts. -/
theorem octahedron_both_poor_budget_1041_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum17 : Hub.card + Iso.card = 17)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 41)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 19) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 19) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hz2 : G.Adj z h₂) (hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 19, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
    (f x : Fin 19) (hfHub : f ∈ Hub) (hfd : G.degree f = 5)
    (hfiso5 : (G.neighborFinset f ∩ Iso).card = 5)
    (_hxHub : x ∈ Hub) (_hxd : G.degree x = 4)
    (_hxiso3 : 3 ≤ (G.neighborFinset x ∩ Iso).card) (_hxf : x ≠ f)
    (_hnadj : ¬G.Adj x f)
    (_hsh : ¬ 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card)
    (hstruct : ∃ c r_t r_z a b : Fin 19,
      Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)
        = ({g, r_t, r_z, a, b} : Finset (Fin 19)) ∧
      ({g, r_t, r_z, a, b} : Finset (Fin 19)).card = 5 ∧
      c ∈ Iso ∧ G.Adj g c ∧ G.Adj h₂ c ∧ G.Adj r_t c ∧
      G.neighborFinset c ∩ Hub = ({h₂, g, r_t} : Finset (Fin 19)) ∧
      G.neighborFinset z ∩ Hub = ({h₂, r_z} : Finset (Fin 19)) ∧
      G.neighborFinset h₂ ∩ Hub = ({a, b} : Finset (Fin 19)) ∧
      G.Adj r_z z ∧ G.Adj a h₂ ∧ G.Adj b h₂ ∧
      r_t ∈ Hub ∧ G.degree r_t = 4 ∧ r_z ∈ Hub ∧ G.degree r_z = 4 ∧
      a ∈ Hub ∧ G.degree a = 4 ∧ b ∈ Hub ∧ G.degree b = 4)
    (z' p q : Fin 19)
    (hz'Z : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hzz' : G.Adj z z') (_hz'deg3 : G.degree z' = 3)
    (_hz'iso0 : (G.neighborFinset z' ∩ Iso).card = 0)
    (hNz'eq : G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 19)))
    (hp : p ∈ Hub) (hq : q ∈ Hub) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hpq : p ≠ q) (hz'p : G.Adj z' p) (hz'q : G.Adj z' q)
    (hnpq : ¬G.Adj p q)
    (_hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0)
    (hppoor : (G.neighborFinset p ∩ Iso).card ≤ 1)
    (hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1)
    (hph₂ : p ≠ h₂) (_hpr_z : p ≠ r_z) (hqh₂ : q ≠ h₂) (_hqr_z : q ≠ r_z) :
    (∃ w : Fin 19, w ∈ Hub ∧ w ≠ h₂ ∧ w ≠ p ∧ w ≠ q ∧ w ≠ f ∧ G.degree w = 4 ∧
      (G.neighborFinset w ∩ Iso).card = 1 ∧ (G.Adj p w ∨ G.Adj q w)) ∧
    G.degree z = 3 ∧
    (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Hub.filter
        (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 2 := by
  classical
  -- === Node-2 counting: |P| = 4, P-members deg 4 isoDeg 1, ∑_R isoDeg = 12. ===
  obtain ⟨hP4, hPfacts, hRiso12⟩ := octahedron_poor_counts_share2_1041_nineteen G Hub Iso
    hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hshare hno2hub hC4 hT
    g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock f hfHub hfd hfiso5
  -- === Structure extraction. ===
  obtain ⟨_c, r_t, r_z, a, b, hReq, hRcard5, _hcIso, _hgc, _hh₂c, _hr_tc, _hNc, hNz, hNh₂,
    hr_zz, _hah₂, _hbh₂, _hr_tHub, _hr_td4, _hr_zHub, _hr_zd4, _haHub, _had4, _hbHub, _hbd4⟩ :=
    hstruct
  -- === deg z = 3 (goal part 2). ===
  have hzf := zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak
  obtain ⟨_, _, hz_deg3⟩ := hzf z hzZ
  -- === Abbreviations. ===
  set R : Finset (Fin 19) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 19) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1) with hPdef
  set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- === R basics. ===
  have hRcard : R.card = 5 := by rw [hReq]; exact hRcard5
  have hRdeg4 : ∀ r ∈ R, G.degree r = 4 := by
    intro r hr; rw [hRdef, Finset.mem_filter] at hr; exact hr.2.1
  have hr_zR : r_z ∈ R := by rw [hReq]; simp
  have haR : a ∈ R := by rw [hReq]; simp
  have hbR : b ∈ R := by rw [hReq]; simp
  have haiso2 : 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    have h := haR; rw [hRdef, Finset.mem_filter] at h; exact h.2.2
  have hbiso2 : 2 ≤ (G.neighborFinset b ∩ Iso).card := by
    have h := hbR; rw [hRdef, Finset.mem_filter] at h; exact h.2.2
  have hr_ziso2 : 2 ≤ (G.neighborFinset r_z ∩ Iso).card := by
    have h := hr_zR; rw [hRdef, Finset.mem_filter] at h; exact h.2.2
  -- === Membership in P. ===
  have hh₂P : h₂ ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hh₂, hd₂, le_of_eq hpoor⟩
  have hpP : p ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hp, hdp, hppoor⟩
  have hqP : q ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hq, hdq, hqpoor⟩
  -- === Not-in-R / not-in-P facts. ===
  have hanotP : a ∉ P := by rw [hPdef, Finset.mem_filter]; push Not; intro _ _; omega
  have hbnotP : b ∉ P := by rw [hPdef, Finset.mem_filter]; push Not; intro _ _; omega
  have hr_znotP : r_z ∉ P := by rw [hPdef, Finset.mem_filter]; push Not; intro _ _; omega
  have hh₂notR : h₂ ∉ R := by rw [hRdef, Finset.mem_filter]; push Not; intro _ _; omega
  have hpnotR : p ∉ R := by rw [hRdef, Finset.mem_filter]; push Not; intro _ _; omega
  have hqnotR : q ∉ R := by rw [hRdef, Finset.mem_filter]; push Not; intro _ _; omega
  -- === Extract the 4th poor hub w. ===
  have h₂notpq : h₂ ∉ ({p, q} : Finset (Fin 19)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hph₂.symm, hqh₂.symm⟩
  have h3sub : ({h₂, p, q} : Finset (Fin 19)) ⊆ P := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hh₂P
    · exact hpP
    · exact hqP
  have h3card : ({h₂, p, q} : Finset (Fin 19)).card = 3 := by
    rw [Finset.card_insert_of_notMem h₂notpq, Finset.card_pair hpq]
  have hdiffcard : (P \ ({h₂, p, q} : Finset (Fin 19))).card = 1 := by
    rw [Finset.card_sdiff_of_subset h3sub, hP4, h3card]
  obtain ⟨w, hw⟩ : (P \ ({h₂, p, q} : Finset (Fin 19))).Nonempty := by
    rw [← Finset.card_pos, hdiffcard]; norm_num
  rw [Finset.mem_sdiff] at hw
  obtain ⟨hwP, hwni⟩ := hw
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwni
  obtain ⟨hwh₂, hwp, hwq⟩ := hwni
  have hwfacts := hPfacts w hwP
  have hwHub : w ∈ Hub := by
    have h := hwP; rw [hPdef, Finset.mem_filter] at h; exact h.1
  have hwf : w ≠ f := by rintro rfl; have h1 := hwfacts.1; omega
  -- === Z = {z, z'}. ===
  have hzz'ne : z ≠ z' := G.ne_of_adj hzz'
  have hZcard : Z.card = 2 := by
    rw [hZdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        Finset.card_union_of_disjoint hdisj, hHub, hIso]
  have hZeq2 : Z = ({z, z'} : Finset (Fin 19)) := by
    have hsub : ({z, z'} : Finset (Fin 19)) ⊆ Z := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzZ
      · exact hz'Z
    have hcard2 : ({z, z'} : Finset (Fin 19)).card = 2 := Finset.card_pair hzz'ne
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  -- === f has no hub neighbour. ===
  have hfhub0 : (G.neighborFinset f ∩ Hub).card = 0 := by
    have hs := nbr_split_three_nineteen G Hub Iso hdisj f
    rw [hfd, hfiso5] at hs; omega
  have hfempty : G.neighborFinset f ∩ Hub = ∅ := Finset.card_eq_zero.mp hfhub0
  have hfnoHub : ∀ h ∈ Hub, ¬G.Adj f h := by
    intro h hh hadj
    have hmem : h ∈ G.neighborFinset f ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset f h).mpr hadj, hh⟩
    rw [hfempty] at hmem; exact Finset.notMem_empty h hmem
  -- === Degree partition: the deg-5 hub is unique (= f). ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  have hD5card1 : (Hub.filter (fun h => ¬ G.degree h = 4)).card = 1 := by
    have hcardpart : (Hub.filter (fun h => G.degree h = 4)).card
        + (Hub.filter (fun h => ¬ G.degree h = 4)).card = 10 := by
      rw [Finset.card_filter_add_card_filter_not]; exact hHub
    have hsumeq : (∑ h ∈ Hub.filter (fun h => G.degree h = 4), G.degree h)
        + (∑ h ∈ Hub.filter (fun h => ¬ G.degree h = 4), G.degree h) = 41 := by
      rw [Finset.sum_filter_add_sum_filter_not]; exact hdsum
    have h4deg : ∀ h ∈ Hub.filter (fun h => G.degree h = 4), G.degree h = 4 :=
      fun h hh => (Finset.mem_filter.mp hh).2
    have h5deg : ∀ h ∈ Hub.filter (fun h => ¬ G.degree h = 4), G.degree h = 5 := by
      intro h hh; rw [Finset.mem_filter] at hh
      rcases hdeg45 h hh.1 with h4 | h5
      · exact absurd h4 hh.2
      · exact h5
    have h4sum : (∑ h ∈ Hub.filter (fun h => G.degree h = 4), G.degree h)
        = 4 * (Hub.filter (fun h => G.degree h = 4)).card := by
      rw [Finset.sum_congr rfl h4deg, Finset.sum_const, smul_eq_mul, mul_comm]
    have h5sum : (∑ h ∈ Hub.filter (fun h => ¬ G.degree h = 4), G.degree h)
        = 5 * (Hub.filter (fun h => ¬ G.degree h = 4)).card := by
      rw [Finset.sum_congr rfl h5deg, Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hfD5mem : f ∈ Hub.filter (fun h => ¬ G.degree h = 4) :=
    Finset.mem_filter.mpr ⟨hfHub, by omega⟩
  have hD5eqf : Hub.filter (fun h => ¬ G.degree h = 4) = {f} := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hD5card1
    rw [hx] at hfD5mem ⊢
    rw [Finset.mem_singleton] at hfD5mem; rw [hfD5mem]
  -- === Hub = R ∪ P ∪ {f} with the three parts disjoint. ===
  have hHubeq : Hub = R ∪ P ∪ {f} := by
    apply Finset.Subset.antisymm
    · intro h hh
      rcases hdeg45 h hh with hd4 | hd5
      · by_cases hiso : 2 ≤ (G.neighborFinset h ∩ Iso).card
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (by rw [hRdef, Finset.mem_filter]; exact ⟨hh, hd4, hiso⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (by rw [hPdef, Finset.mem_filter]; exact ⟨hh, hd4, by omega⟩))
      · have hhf : h = f := by
          have hmem5 : h ∈ Hub.filter (fun h => ¬ G.degree h = 4) :=
            Finset.mem_filter.mpr ⟨hh, by omega⟩
          rw [hD5eqf, Finset.mem_singleton] at hmem5; exact hmem5
        rw [hhf]; exact Finset.mem_union_right _ (Finset.mem_singleton_self f)
    · intro h hh
      rw [Finset.mem_union, Finset.mem_union] at hh
      rcases hh with (hR | hP) | hf
      · rw [hRdef, Finset.mem_filter] at hR; exact hR.1
      · rw [hPdef, Finset.mem_filter] at hP; exact hP.1
      · rw [Finset.mem_singleton] at hf; rw [hf]; exact hfHub
  have hRPdisj : Disjoint R P := by
    rw [Finset.disjoint_left]; intro x hxR hxP
    rw [hRdef, Finset.mem_filter] at hxR; rw [hPdef, Finset.mem_filter] at hxP; omega
  have hRPfdisj : Disjoint (R ∪ P) ({f} : Finset (Fin 19)) := by
    rw [Finset.disjoint_left]; intro x hx hxf
    rw [Finset.mem_singleton] at hxf; subst hxf
    rw [Finset.mem_union] at hx
    rcases hx with hR | hP
    · rw [hRdef, Finset.mem_filter] at hR; obtain ⟨_, hd, _⟩ := hR; omega
    · rw [hPdef, Finset.mem_filter] at hP; obtain ⟨_, hd, _⟩ := hP; omega
  -- === Per-vertex hub split into R, P, {f}. ===
  have hlem : ∀ (s A B : Finset (Fin 19)), Disjoint A B →
      (s ∩ (A ∪ B)).card = (s ∩ A).card + (s ∩ B).card := by
    intro s A B hAB
    rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB)
  have hpart3 : ∀ h : Fin 19, (G.neighborFinset h ∩ Hub).card
      = (G.neighborFinset h ∩ R).card + (G.neighborFinset h ∩ P).card
        + (G.neighborFinset h ∩ {f}).card := by
    intro h; rw [hHubeq, hlem _ _ _ hRPfdisj, hlem _ _ _ hRPdisj]
  -- === nbr split sums over R and P. ===
  have hsplitR : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card)
      + (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
      + (∑ r ∈ R, (G.neighborFinset r ∩ Z).card) = ∑ r ∈ R, G.degree r := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => nbr_split_three_nineteen G Hub Iso hdisj r)
  have hsplitP : (∑ x ∈ P, (G.neighborFinset x ∩ Hub).card)
      + (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card)
      + (∑ x ∈ P, (G.neighborFinset x ∩ Z).card) = ∑ x ∈ P, G.degree x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => nbr_split_three_nineteen G Hub Iso hdisj x)
  -- === Degree / iso sums over R and P. ===
  have hRdeg20 : (∑ r ∈ R, G.degree r) = 20 := by
    have h4 : (∑ r ∈ R, G.degree r) = 4 * R.card := by
      rw [Finset.sum_congr rfl (fun r hr => hRdeg4 r hr), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h4, hRcard]
  have hPdeg16 : (∑ x ∈ P, G.degree x) = 16 := by
    have h4 : (∑ x ∈ P, G.degree x) = 4 * P.card := by
      rw [Finset.sum_congr rfl (fun x hx => (hPfacts x hx).1), Finset.sum_const, smul_eq_mul,
          mul_comm]
    rw [h4, hP4]
  have hPiso4 : (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card) = 4 := by
    have h1 : (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card) = 1 * P.card := by
      rw [Finset.sum_congr rfl (fun x hx => (hPfacts x hx).2), Finset.sum_const, smul_eq_mul,
          mul_comm]
    rw [h1, hP4]
  -- === z-attachment: ∑_R zDeg = 1, ∑_P zDeg = 3 (cross count over Z = {z, z'}). ===
  have hRz1 : (∑ r ∈ R, (G.neighborFinset r ∩ Z).card) = 1 := by
    rw [cross_count_nineteen G R Z, hZeq2, Finset.sum_pair hzz'ne]
    have hNzR : G.neighborFinset z ∩ R = {r_z} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨hxNz, hxR⟩
        have hxHub : x ∈ Hub := by
          have h := hxR; rw [hRdef, Finset.mem_filter] at h; exact h.1
        have hmem : x ∈ G.neighborFinset z ∩ Hub := Finset.mem_inter.mpr ⟨hxNz, hxHub⟩
        rw [hNz] at hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact absurd hxR hh₂notR
        · rfl
      · intro hx; rw [hx]; exact ⟨(G.mem_neighborFinset z r_z).mpr hr_zz.symm, hr_zR⟩
    have hNz'R : G.neighborFinset z' ∩ R = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
      rw [Finset.mem_inter] at hx; obtain ⟨hxNz', hxR⟩ := hx
      have hxHub : x ∈ Hub := by
        have h := hxR; rw [hRdef, Finset.mem_filter] at h; exact h.1
      have hmem : x ∈ G.neighborFinset z' ∩ Hub := Finset.mem_inter.mpr ⟨hxNz', hxHub⟩
      rw [hNz'eq] at hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact absurd hxR hpnotR
      · exact absurd hxR hqnotR
    rw [hNzR, hNz'R, Finset.card_singleton, Finset.card_empty]
  have hPz3 : (∑ x ∈ P, (G.neighborFinset x ∩ Z).card) = 3 := by
    rw [cross_count_nineteen G P Z, hZeq2, Finset.sum_pair hzz'ne]
    have hNzP : G.neighborFinset z ∩ P = {h₂} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨hxNz, hxP⟩
        have hxHub : x ∈ Hub := by
          have h := hxP; rw [hPdef, Finset.mem_filter] at h; exact h.1
        have hmem : x ∈ G.neighborFinset z ∩ Hub := Finset.mem_inter.mpr ⟨hxNz, hxHub⟩
        rw [hNz] at hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · rfl
        · exact absurd hxP hr_znotP
      · intro hx; rw [hx]; exact ⟨(G.mem_neighborFinset z h₂).mpr hz2, hh₂P⟩
    have hNz'P : G.neighborFinset z' ∩ P = {p, q} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxNz', hxP⟩
        have hxHub : x ∈ Hub := by
          have h := hxP; rw [hPdef, Finset.mem_filter] at h; exact h.1
        have hmem : x ∈ G.neighborFinset z' ∩ Hub := Finset.mem_inter.mpr ⟨hxNz', hxHub⟩
        rw [hNz'eq] at hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        exact hmem
      · intro hx
        rcases hx with hx | hx
        · rw [hx]; exact ⟨(G.mem_neighborFinset z' p).mpr hz'p, hpP⟩
        · rw [hx]; exact ⟨(G.mem_neighborFinset z' q).mpr hz'q, hqP⟩
    rw [hNzP, hNz'P, Finset.card_singleton, Finset.card_pair hpq]
  -- === Hub-degree sums over R and P. ===
  have hRhub7 : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card) = 7 := by omega
  have hPhub9 : (∑ x ∈ P, (G.neighborFinset x ∩ Hub).card) = 9 := by omega
  -- === The {f}-column vanishes; split each hub sum into R- and P-parts. ===
  have hRf0sum : (∑ r ∈ R, (G.neighborFinset r ∩ {f}).card) = 0 := by
    rw [Finset.sum_eq_zero]; intro r hr
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro x hx
    rw [Finset.mem_inter, Finset.mem_singleton] at hx; obtain ⟨hxNr, hxf⟩ := hx
    have hrHub : r ∈ Hub := by have h := hr; rw [hRdef, Finset.mem_filter] at h; exact h.1
    rw [hxf] at hxNr
    exact hfnoHub r hrHub ((G.mem_neighborFinset r f).mp hxNr).symm
  have hPf0sum : (∑ x ∈ P, (G.neighborFinset x ∩ {f}).card) = 0 := by
    rw [Finset.sum_eq_zero]; intro x hx
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro y hy
    rw [Finset.mem_inter, Finset.mem_singleton] at hy; obtain ⟨hyNx, hyf⟩ := hy
    have hxHub : x ∈ Hub := by have h := hx; rw [hPdef, Finset.mem_filter] at h; exact h.1
    rw [hyf] at hyNx
    exact hfnoHub x hxHub ((G.mem_neighborFinset x f).mp hyNx).symm
  have hAexp : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card)
      = (∑ r ∈ R, (G.neighborFinset r ∩ R).card)
        + (∑ r ∈ R, (G.neighborFinset r ∩ P).card) := by
    rw [Finset.sum_congr rfl (fun r _ => hpart3 r), Finset.sum_add_distrib, Finset.sum_add_distrib,
        hRf0sum, add_zero]
  have hBexp : (∑ x ∈ P, (G.neighborFinset x ∩ Hub).card)
      = (∑ x ∈ P, (G.neighborFinset x ∩ R).card)
        + (∑ x ∈ P, (G.neighborFinset x ∩ P).card) := by
    rw [Finset.sum_congr rfl (fun x _ => hpart3 x), Finset.sum_add_distrib, Finset.sum_add_distrib,
        hPf0sum, add_zero]
  have hcross : (∑ r ∈ R, (G.neighborFinset r ∩ P).card)
      = ∑ x ∈ P, (G.neighborFinset x ∩ R).card := cross_count_nineteen G R P
  -- === P = {h₂, p, q, w} and the poor–poor edge structure. ===
  have hcard4 : ({h₂, p, q, w} : Finset (Fin 19)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hph₂.symm, hqh₂.symm, Ne.symm hwh₂⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hpq, Ne.symm hwp⟩),
        Finset.card_pair (Ne.symm hwq)]
  have hPeq4 : P = ({h₂, p, q, w} : Finset (Fin 19)) := by
    have hsub : ({h₂, p, q, w} : Finset (Fin 19)) ⊆ P := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hh₂P
      · exact hpP
      · exact hqP
      · exact hwP
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hh₂noP : ∀ x ∈ P, ¬ G.Adj h₂ x := by
    intro x hxP hadj
    have hxHub : x ∈ Hub := by have h := hxP; rw [hPdef, Finset.mem_filter] at h; exact h.1
    have hmem : x ∈ G.neighborFinset h₂ ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ x).mpr hadj, hxHub⟩
    rw [hNh₂] at hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hanotP hxP
    · exact hbnotP hxP
  have hNh₂P : G.neighborFinset h₂ ∩ P = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
    rw [Finset.mem_inter] at hx
    exact hh₂noP x hx.2 ((G.mem_neighborFinset h₂ x).mp hx.1)
  have hNpP : G.neighborFinset p ∩ P = G.neighborFinset p ∩ ({w} : Finset (Fin 19)) := by
    rw [hPeq4]; ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxNp, hx4⟩
      refine ⟨hxNp, ?_⟩
      have hpx : G.Adj p x := (G.mem_neighborFinset p x).mp hxNp
      rcases hx4 with rfl | rfl | rfl | rfl
      · exact absurd hpx.symm (hh₂noP p hpP)
      · exact ((G.ne_of_adj hpx) rfl).elim
      · exact absurd hpx hnpq
      · rfl
    · rintro ⟨hxNp, rfl⟩; exact ⟨hxNp, Or.inr (Or.inr (Or.inr rfl))⟩
  have hNqP : G.neighborFinset q ∩ P = G.neighborFinset q ∩ ({w} : Finset (Fin 19)) := by
    rw [hPeq4]; ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxNq, hx4⟩
      refine ⟨hxNq, ?_⟩
      have hqx : G.Adj q x := (G.mem_neighborFinset q x).mp hxNq
      rcases hx4 with rfl | rfl | rfl | rfl
      · exact absurd hqx.symm (hh₂noP q hqP)
      · exact absurd hqx.symm hnpq
      · exact ((G.ne_of_adj hqx) rfl).elim
      · rfl
    · rintro ⟨hxNq, rfl⟩; exact ⟨hxNq, Or.inr (Or.inr (Or.inr rfl))⟩
  have hNwP : G.neighborFinset w ∩ P = G.neighborFinset w ∩ ({p, q} : Finset (Fin 19)) := by
    rw [hPeq4]; ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxNw, hx4⟩
      refine ⟨hxNw, ?_⟩
      have hwx : G.Adj w x := (G.mem_neighborFinset w x).mp hxNw
      rcases hx4 with rfl | rfl | rfl | rfl
      · exact absurd hwx.symm (hh₂noP w hwP)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact ((G.ne_of_adj hwx) rfl).elim
    · rintro ⟨hxNw, (rfl | rfl)⟩
      · exact ⟨hxNw, Or.inr (Or.inl rfl)⟩
      · exact ⟨hxNw, Or.inr (Or.inr (Or.inl rfl))⟩
  have hNpPcard : (G.neighborFinset p ∩ P).card = (if G.Adj p w then 1 else 0) := by
    rw [hNpP]
    by_cases hpw : G.Adj p w
    · rw [Finset.inter_singleton_of_mem ((G.mem_neighborFinset p w).mpr hpw),
          Finset.card_singleton, if_pos hpw]
    · rw [Finset.inter_singleton_of_notMem (fun hm => hpw ((G.mem_neighborFinset p w).mp hm)),
          Finset.card_empty, if_neg hpw]
  have hNqPcard : (G.neighborFinset q ∩ P).card = (if G.Adj q w then 1 else 0) := by
    rw [hNqP]
    by_cases hqw : G.Adj q w
    · rw [Finset.inter_singleton_of_mem ((G.mem_neighborFinset q w).mpr hqw),
          Finset.card_singleton, if_pos hqw]
    · rw [Finset.inter_singleton_of_notMem (fun hm => hqw ((G.mem_neighborFinset q w).mp hm)),
          Finset.card_empty, if_neg hqw]
  have hNwPcard : (G.neighborFinset w ∩ P).card
      = (if G.Adj p w then 1 else 0) + (if G.Adj q w then 1 else 0) := by
    rw [hNwP]
    by_cases hpw : G.Adj p w <;> by_cases hqw : G.Adj q w
    · have hpNw : p ∈ G.neighborFinset w := (G.mem_neighborFinset w p).mpr hpw.symm
      have hqNw : q ∈ G.neighborFinset w := (G.mem_neighborFinset w q).mpr hqw.symm
      have heq : G.neighborFinset w ∩ ({p, q} : Finset (Fin 19)) = {p, q} :=
        Finset.inter_eq_right.mpr (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hpNw
          · exact hqNw)
      rw [heq, Finset.card_pair hpq, if_pos hpw, if_pos hqw]
    · have hpNw : p ∈ G.neighborFinset w := (G.mem_neighborFinset w p).mpr hpw.symm
      have hqnNw : q ∉ G.neighborFinset w :=
        fun hm => hqw ((G.mem_neighborFinset w q).mp hm).symm
      have heq : G.neighborFinset w ∩ ({p, q} : Finset (Fin 19)) = {p} := by
        ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxNw, rfl | rfl⟩
          · rfl
          · exact absurd hxNw hqnNw
        · rintro rfl; exact ⟨hpNw, Or.inl rfl⟩
      rw [heq, Finset.card_singleton, if_pos hpw, if_neg hqw]
    · have hqNw : q ∈ G.neighborFinset w := (G.mem_neighborFinset w q).mpr hqw.symm
      have hpnNw : p ∉ G.neighborFinset w :=
        fun hm => hpw ((G.mem_neighborFinset w p).mp hm).symm
      have heq : G.neighborFinset w ∩ ({p, q} : Finset (Fin 19)) = {q} := by
        ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxNw, rfl | rfl⟩
          · exact absurd hxNw hpnNw
          · rfl
        · rintro rfl; exact ⟨hqNw, Or.inr rfl⟩
      rw [heq, Finset.card_singleton, if_neg hpw, if_pos hqw]
    · have hpnNw : p ∉ G.neighborFinset w :=
        fun hm => hpw ((G.mem_neighborFinset w p).mp hm).symm
      have hqnNw : q ∉ G.neighborFinset w :=
        fun hm => hqw ((G.mem_neighborFinset w q).mp hm).symm
      have heq : G.neighborFinset w ∩ ({p, q} : Finset (Fin 19)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
        rw [Finset.mem_inter] at hx; obtain ⟨hxNw, hx2⟩ := hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
        rcases hx2 with rfl | rfl
        · exact hpnNw hxNw
        · exact hqnNw hxNw
      rw [heq, Finset.card_empty, if_neg hpw, if_neg hqw]
  -- === ∑_P |N·∩P| = 2·[p~w] + 2·[q~w]. ===
  have h₂notpqw : h₂ ∉ ({p, q, w} : Finset (Fin 19)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hph₂.symm, hqh₂.symm, Ne.symm hwh₂⟩
  have pnotqw : p ∉ ({q, w} : Finset (Fin 19)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hpq, Ne.symm hwp⟩
  have qnotw : q ∉ ({w} : Finset (Fin 19)) := by
    simp only [Finset.mem_singleton]; exact Ne.symm hwq
  have hePPval : (∑ x ∈ P, (G.neighborFinset x ∩ P).card)
      = 2 * (if G.Adj p w then 1 else 0) + 2 * (if G.Adj q w then 1 else 0) := by
    have hexp : (∑ x ∈ P, (G.neighborFinset x ∩ P).card)
        = ∑ x ∈ ({h₂, p, q, w} : Finset (Fin 19)), (G.neighborFinset x ∩ P).card :=
      Finset.sum_congr hPeq4 (fun x _ => rfl)
    rw [hexp, Finset.sum_insert h₂notpqw, Finset.sum_insert pnotqw, Finset.sum_insert qnotw,
        Finset.sum_singleton]
    simp only [hNh₂P, Finset.card_empty, hNpPcard, hNqPcard, hNwPcard]
    ring
  -- === The edge exists and the rich–rich bound holds. ===
  have hedge : G.Adj p w ∨ G.Adj q w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hnpw, hnqw⟩ := hcon
    rw [if_neg hnpw, if_neg hnqw] at hePPval
    omega
  have hbound : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) ≤ 2 := by
    have ha1 : (if G.Adj p w then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
    have hb1 : (if G.Adj q w then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
    omega
  exact ⟨⟨w, hwHub, hwh₂, hwp, hwq, hwf, hwfacts.1, hwfacts.2, hedge⟩, hz_deg3, hbound⟩

end N19

end ACMax
