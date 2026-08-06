import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5RichCap
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Blocker
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041OctaPoorCounts

/-! # CASE C both-poor: the budget foundation (`n = 20`)

Derives the poor/`Z` budget for the both-poor regime at `n = 20`, where the
poor set `P` has FIVE members and the poor-counts foundation is disjunctive.
World (i) (`Σ_R = 11`, all five poor hubs at isoDeg `1`): a poor hub `w` with
isoDeg `1` meets `{p, q}` and `∑_R richDeg ≤ 6` (`e_RR ≤ 3`).  World (ii)
(`Σ_R = 12`, one isoDeg-`0` poor hub): `∑_R richDeg ≤ 4` (`e_RR ≤ 2`) plus a
dichotomy — either a poor hub with isoDeg `1` meets `{p, q}` (the `n = 19`
shape), or the isoDeg-`0` hub `w` is adjacent to BOTH `p` and `q`, no other
poor hub meets `{p, q}`, and the rich layer has NO internal edges at all
(`∑_R richDeg = 0`).  The provable foundation of the both-poor config kill. -/

namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 4000000 in
/-- **The both-poor budget (`n = 20`, disjunctive).**  Extracts a `{p, q}`-attached
poor hub and the per-world rich–rich edge budgets. -/
theorem octahedron_both_poor_budget_1041_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 11) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 20) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hz2 : G.Adj z h₂) (hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
    (hR5ge : 5 ≤ (Hub.filter
      (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card)
    (f x : Fin 20) (hfHub : f ∈ Hub) (hfd : G.degree f = 5)
    (hfiso5 : (G.neighborFinset f ∩ Iso).card = 5)
    (_hxHub : x ∈ Hub) (_hxd : G.degree x = 4)
    (_hxiso3 : 3 ≤ (G.neighborFinset x ∩ Iso).card) (_hxf : x ≠ f)
    (_hnadj : ¬G.Adj x f)
    (_hsh : ¬ 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card)
    (hstruct : ∃ c r_t r_z a b : Fin 20,
      Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)
        = ({g, r_t, r_z, a, b} : Finset (Fin 20)) ∧
      ({g, r_t, r_z, a, b} : Finset (Fin 20)).card = 5 ∧
      c ∈ Iso ∧ G.Adj g c ∧ G.Adj h₂ c ∧ G.Adj r_t c ∧
      G.neighborFinset c ∩ Hub = ({h₂, g, r_t} : Finset (Fin 20)) ∧
      G.neighborFinset z ∩ Hub = ({h₂, r_z} : Finset (Fin 20)) ∧
      G.neighborFinset h₂ ∩ Hub = ({a, b} : Finset (Fin 20)) ∧
      G.Adj r_z z ∧ G.Adj a h₂ ∧ G.Adj b h₂ ∧
      r_t ∈ Hub ∧ G.degree r_t = 4 ∧ r_z ∈ Hub ∧ G.degree r_z = 4 ∧
      a ∈ Hub ∧ G.degree a = 4 ∧ b ∈ Hub ∧ G.degree b = 4)
    (z' p q : Fin 20)
    (hz'Z : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hzz' : G.Adj z z') (_hz'deg3 : G.degree z' = 3)
    (_hz'iso0 : (G.neighborFinset z' ∩ Iso).card = 0)
    (hNz'eq : G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 20)))
    (hp : p ∈ Hub) (hq : q ∈ Hub) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hpq : p ≠ q) (hz'p : G.Adj z' p) (hz'q : G.Adj z' q)
    (hnpq : ¬G.Adj p q)
    (_hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0)
    (hppoor : (G.neighborFinset p ∩ Iso).card ≤ 1)
    (hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1)
    (hph₂ : p ≠ h₂) (_hpr_z : p ≠ r_z) (hqh₂ : q ≠ h₂) (_hqr_z : q ≠ r_z) :
    ((Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1)).card = 5 ∧
      (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card) = 11 ∧
      (∀ x ∈ Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1),
        (G.neighborFinset x ∩ Iso).card = 1) ∧
      (∃ w : Fin 20, w ∈ Hub ∧ w ≠ h₂ ∧ w ≠ p ∧ w ≠ q ∧ w ≠ f ∧ G.degree w = 4 ∧
        (G.neighborFinset w ∩ Iso).card = 1 ∧ (G.Adj p w ∨ G.Adj q w)) ∧
      G.degree z = 3 ∧
      (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Hub.filter
          (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 6) ∨
    ((Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1)).card = 5 ∧
      (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card) = 12 ∧
      (∃ h₀ ∈ Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1),
        (G.neighborFinset h₀ ∩ Iso).card = 0 ∧
        ∀ x ∈ Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1) \
          ({h₀} : Finset (Fin 20)), (G.neighborFinset x ∩ Iso).card = 1) ∧
      G.degree z = 3 ∧
      (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Hub.filter
          (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 4 ∧
      ((∃ w : Fin 20, w ∈ Hub ∧ w ≠ h₂ ∧ w ≠ p ∧ w ≠ q ∧ w ≠ f ∧ G.degree w = 4 ∧
          (G.neighborFinset w ∩ Iso).card = 1 ∧ (G.Adj p w ∨ G.Adj q w)) ∨
        (∃ w : Fin 20, w ∈ Hub ∧ w ≠ h₂ ∧ w ≠ p ∧ w ≠ q ∧ w ≠ f ∧ G.degree w = 4 ∧
          (G.neighborFinset w ∩ Iso).card = 0 ∧ G.Adj p w ∧ G.Adj q w ∧
          (∀ x ∈ Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1),
            x ≠ w → (G.neighborFinset x ∩ Iso).card = 1 ∧ ¬G.Adj p x ∧ ¬G.Adj q x) ∧
          (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
            (G.neighborFinset r ∩ Hub.filter
              (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) = 0))) := by
  classical
  -- === Node-2 counting (disjunctive at n = 20): |P| = 5, ∑_R isoDeg ∈ {11, 12}. ===
  have hPoorCounts := octahedron_poor_counts_share2_1041_twenty G Hub Iso
    hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hshare hno2hub hC4 hT
    g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock hR5ge f hfHub hfd hfiso5
  -- === Structure extraction. ===
  obtain ⟨_c, r_t, r_z, a, b, hReq, hRcard5, _hcIso, _hgc, _hh₂c, _hr_tc, _hNc, hNz, hNh₂,
    hr_zz, _hah₂, _hbh₂, _hr_tHub, _hr_td4, _hr_zHub, _hr_zd4, _haHub, _had4, _hbHub, _hbd4⟩ :=
    hstruct
  -- === deg z = 3. ===
  have hzf := zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
  obtain ⟨_, _, hz_deg3⟩ := hzf z hzZ
  -- === Abbreviations. ===
  set R : Finset (Fin 20) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 20) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1) with hPdef
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- === |P| = 5 in both worlds. ===
  have hP5 : P.card = 5 := by
    rcases hPoorCounts with ⟨h5, _, _⟩ | ⟨h5, _, _⟩ <;> exact h5
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
  -- === The two extra poor hubs w₁, w₂. ===
  have h₂notpq : h₂ ∉ ({p, q} : Finset (Fin 20)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hph₂.symm, hqh₂.symm⟩
  have h3sub : ({h₂, p, q} : Finset (Fin 20)) ⊆ P := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hh₂P
    · exact hpP
    · exact hqP
  have h3card : ({h₂, p, q} : Finset (Fin 20)).card = 3 := by
    rw [Finset.card_insert_of_notMem h₂notpq, Finset.card_pair hpq]
  have hdiffcard : (P \ ({h₂, p, q} : Finset (Fin 20))).card = 2 := by
    rw [Finset.card_sdiff_of_subset h3sub, hP5, h3card]
  obtain ⟨w₁, w₂, hw12ne, hdiffeq⟩ := Finset.card_eq_two.mp hdiffcard
  have hw₁mem : w₁ ∈ P \ ({h₂, p, q} : Finset (Fin 20)) := by
    rw [hdiffeq]; exact Finset.mem_insert_self w₁ {w₂}
  have hw₂mem : w₂ ∈ P \ ({h₂, p, q} : Finset (Fin 20)) := by
    rw [hdiffeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w₂)
  have hw₁P : w₁ ∈ P := (Finset.mem_sdiff.mp hw₁mem).1
  have hw₂P : w₂ ∈ P := (Finset.mem_sdiff.mp hw₂mem).1
  have hPeq5 : P = ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by
    have h1 : ({h₂, p, q} : Finset (Fin 20)) ∪ (P \ ({h₂, p, q} : Finset (Fin 20))) = P :=
      Finset.union_sdiff_of_subset h3sub
    rw [hdiffeq] at h1
    rw [← h1]
    ext y
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]
  -- === Generic poor-hub facts. ===
  have hPHub : ∀ u ∈ P, u ∈ Hub := by
    intro u hu; rw [hPdef, Finset.mem_filter] at hu; exact hu.1
  have hPdeg4 : ∀ u ∈ P, G.degree u = 4 := by
    intro u hu; rw [hPdef, Finset.mem_filter] at hu; exact hu.2.1
  have hPiso1 : ∀ u ∈ P, (G.neighborFinset u ∩ Iso).card ≤ 1 := by
    intro u hu; rw [hPdef, Finset.mem_filter] at hu; exact hu.2.2
  -- === Z = {z, z'}. ===
  have hzz'ne : z ≠ z' := G.ne_of_adj hzz'
  have hZcard : Z.card = 2 := by
    rw [hZdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, Finset.card_union_of_disjoint hdisj, hHub, hIso]
  have hZeq2 : Z = ({z, z'} : Finset (Fin 20)) := by
    have hsub : ({z, z'} : Finset (Fin 20)) ⊆ Z := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzZ
      · exact hz'Z
    have hcard2 : ({z, z'} : Finset (Fin 20)).card = 2 := Finset.card_pair hzz'ne
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  -- === f has no hub neighbour. ===
  have hfhub0 : (G.neighborFinset f ∩ Hub).card = 0 := by
    have hs := nbr_split_three_twenty G Hub Iso hdisj f
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
        + (Hub.filter (fun h => ¬ G.degree h = 4)).card = 11 := by
      rw [Finset.card_filter_add_card_filter_not]; exact hHub
    have hsumeq : (∑ h ∈ Hub.filter (fun h => G.degree h = 4), G.degree h)
        + (∑ h ∈ Hub.filter (fun h => ¬ G.degree h = 4), G.degree h) = 45 := by
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
  have hRPfdisj : Disjoint (R ∪ P) ({f} : Finset (Fin 20)) := by
    rw [Finset.disjoint_left]; intro x hx hxf
    rw [Finset.mem_singleton] at hxf; subst hxf
    rw [Finset.mem_union] at hx
    rcases hx with hR | hP
    · rw [hRdef, Finset.mem_filter] at hR; obtain ⟨_, hd, _⟩ := hR; omega
    · rw [hPdef, Finset.mem_filter] at hP; obtain ⟨_, hd, _⟩ := hP; omega
  -- === Per-vertex hub split into R, P, {f}. ===
  have hlem : ∀ (s A B : Finset (Fin 20)), Disjoint A B →
      (s ∩ (A ∪ B)).card = (s ∩ A).card + (s ∩ B).card := by
    intro s A B hAB
    rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB)
  have hpart3 : ∀ h : Fin 20, (G.neighborFinset h ∩ Hub).card
      = (G.neighborFinset h ∩ R).card + (G.neighborFinset h ∩ P).card
        + (G.neighborFinset h ∩ {f}).card := by
    intro h; rw [hHubeq, hlem _ _ _ hRPfdisj, hlem _ _ _ hRPdisj]
  -- === nbr split sums over R and P. ===
  have hsplitR : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card)
      + (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
      + (∑ r ∈ R, (G.neighborFinset r ∩ Z).card) = ∑ r ∈ R, G.degree r := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => nbr_split_three_twenty G Hub Iso hdisj r)
  have hsplitP : (∑ x ∈ P, (G.neighborFinset x ∩ Hub).card)
      + (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card)
      + (∑ x ∈ P, (G.neighborFinset x ∩ Z).card) = ∑ x ∈ P, G.degree x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => nbr_split_three_twenty G Hub Iso hdisj x)
  -- === Degree / iso sums over R and P. ===
  have hRdeg20 : (∑ r ∈ R, G.degree r) = 20 := by
    have h4 : (∑ r ∈ R, G.degree r) = 4 * R.card := by
      rw [Finset.sum_congr rfl (fun r hr => hRdeg4 r hr), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h4, hRcard]
  have hPdeg20 : (∑ x ∈ P, G.degree x) = 20 := by
    have h4 : (∑ x ∈ P, G.degree x) = 4 * P.card := by
      rw [Finset.sum_congr rfl (fun x hx => hPdeg4 x hx), Finset.sum_const, smul_eq_mul,
          mul_comm]
    rw [h4, hP5]
  -- === z-attachment: ∑_R zDeg = 1, ∑_P zDeg = 3 (cross count over Z = {z, z'}). ===
  have hRz1 : (∑ r ∈ R, (G.neighborFinset r ∩ Z).card) = 1 := by
    rw [cross_count_twenty G R Z, hZeq2, Finset.sum_pair hzz'ne]
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
    rw [cross_count_twenty G P Z, hZeq2, Finset.sum_pair hzz'ne]
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
      = ∑ x ∈ P, (G.neighborFinset x ∩ R).card := cross_count_twenty G R P
  -- === h₂ is P-isolated. ===
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
  have htermh₂ : (G.neighborFinset h₂ ∩ P).card = 0 := by rw [hNh₂P]; exact Finset.card_empty
  -- === Small-set cardinality helper. ===
  have hle3 : ∀ u v t : Fin 20, ({u, v, t} : Finset (Fin 20)).card ≤ 3 := by
    intro u v t
    have h1 := Finset.card_insert_le u ({v, t} : Finset (Fin 20))
    have h2 := Finset.card_insert_le v ({t} : Finset (Fin 20))
    have h3 := Finset.card_singleton t
    omega
  -- === The five-term P-column decomposition. ===
  have hsumPP : (∑ u ∈ P, (G.neighborFinset u ∩ P).card)
      = (G.neighborFinset h₂ ∩ P).card + (G.neighborFinset p ∩ P).card
        + (G.neighborFinset q ∩ P).card + (G.neighborFinset w₁ ∩ P).card
        + (G.neighborFinset w₂ ∩ P).card := by
    have h1 := Finset.sum_sdiff (f := fun u => (G.neighborFinset u ∩ P).card) h3sub
    rw [hdiffeq] at h1
    simp only [Finset.sum_pair hw12ne, Finset.sum_insert h₂notpq,
      Finset.sum_insert (Finset.notMem_singleton.mpr hpq), Finset.sum_singleton] at h1
    omega
  -- === Per-vertex P-degree caps: p, q see only {w₁, w₂}; w₁, w₂ avoid h₂. ===
  have hcapp : (G.neighborFinset p ∩ P).card ≤ 2 := by
    have hsub' : G.neighborFinset p ∩ P ⊆ ({w₁, w₂} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      obtain ⟨hadj, hyP⟩ := hy
      have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
      rcases hy5 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj.symm (hh₂noP p hpP)
      · exact absurd rfl (G.ne_of_adj hadj)
      · exact absurd hadj hnpq
      · exact Or.inl rfl
      · exact Or.inr rfl
    calc (G.neighborFinset p ∩ P).card ≤ ({w₁, w₂} : Finset (Fin 20)).card :=
          Finset.card_le_card hsub'
      _ = 2 := Finset.card_pair hw12ne
  have hcapq : (G.neighborFinset q ∩ P).card ≤ 2 := by
    have hsub' : G.neighborFinset q ∩ P ⊆ ({w₁, w₂} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      obtain ⟨hadj, hyP⟩ := hy
      have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
      rcases hy5 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj.symm (hh₂noP q hqP)
      · exact absurd hadj.symm hnpq
      · exact absurd rfl (G.ne_of_adj hadj)
      · exact Or.inl rfl
      · exact Or.inr rfl
    calc (G.neighborFinset q ∩ P).card ≤ ({w₁, w₂} : Finset (Fin 20)).card :=
          Finset.card_le_card hsub'
      _ = 2 := Finset.card_pair hw12ne
  have hcapw₁ : (G.neighborFinset w₁ ∩ P).card ≤ 3 := by
    have hsub' : G.neighborFinset w₁ ∩ P ⊆ ({p, q, w₂} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      obtain ⟨hadj, hyP⟩ := hy
      have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
      rcases hy5 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj.symm (hh₂noP w₁ hw₁P)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl (G.ne_of_adj hadj)
      · exact Or.inr (Or.inr rfl)
    exact le_trans (Finset.card_le_card hsub') (hle3 p q w₂)
  have hcapw₂ : (G.neighborFinset w₂ ∩ P).card ≤ 3 := by
    have hsub' : G.neighborFinset w₂ ∩ P ⊆ ({p, q, w₁} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      obtain ⟨hadj, hyP⟩ := hy
      have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
      rcases hy5 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj.symm (hh₂noP w₂ hw₂P)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd rfl (G.ne_of_adj hadj)
    exact le_trans (Finset.card_le_card hsub') (hle3 p q w₁)
  have hPP10 : (∑ u ∈ P, (G.neighborFinset u ∩ P).card) ≤ 10 := by omega
  -- === If no poor hub meets {p, q}, the P-column nearly vanishes. ===
  have hnoedge_small : (∀ y ∈ P, ¬G.Adj p y ∧ ¬G.Adj q y) →
      (∑ u ∈ P, (G.neighborFinset u ∩ P).card) ≤ 2 := by
    intro hno
    have htp : (G.neighborFinset p ∩ P).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      exact (hno y hy.2).1 hy.1
    have htq : (G.neighborFinset q ∩ P).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      exact (hno y hy.2).2 hy.1
    have htw₁ : (G.neighborFinset w₁ ∩ P).card ≤ 1 := by
      have hsub' : G.neighborFinset w₁ ∩ P ⊆ ({w₂} : Finset (Fin 20)) := by
        intro y hy
        rw [Finset.mem_inter, G.mem_neighborFinset] at hy
        obtain ⟨hadj, hyP⟩ := hy
        have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
        rcases hy5 with rfl | rfl | rfl | rfl | rfl
        · exact absurd hadj.symm (hh₂noP w₁ hw₁P)
        · exact absurd hadj.symm ((hno w₁ hw₁P).1)
        · exact absurd hadj.symm ((hno w₁ hw₁P).2)
        · exact absurd rfl (G.ne_of_adj hadj)
        · rfl
      calc (G.neighborFinset w₁ ∩ P).card ≤ ({w₂} : Finset (Fin 20)).card :=
            Finset.card_le_card hsub'
        _ = 1 := Finset.card_singleton w₂
    have htw₂ : (G.neighborFinset w₂ ∩ P).card ≤ 1 := by
      have hsub' : G.neighborFinset w₂ ∩ P ⊆ ({w₁} : Finset (Fin 20)) := by
        intro y hy
        rw [Finset.mem_inter, G.mem_neighborFinset] at hy
        obtain ⟨hadj, hyP⟩ := hy
        have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
        rcases hy5 with rfl | rfl | rfl | rfl | rfl
        · exact absurd hadj.symm (hh₂noP w₂ hw₂P)
        · exact absurd hadj.symm ((hno w₂ hw₂P).1)
        · exact absurd hadj.symm ((hno w₂ hw₂P).2)
        · rfl
        · exact absurd rfl (G.ne_of_adj hadj)
      calc (G.neighborFinset w₂ ∩ P).card ≤ ({w₁} : Finset (Fin 20)).card :=
            Finset.card_le_card hsub'
        _ = 1 := Finset.card_singleton w₁
    omega
  -- === World split on the disjunctive poor counts. ===
  rcases hPoorCounts with ⟨_, hall1, hRiso11⟩ | ⟨_, hh₀clause, hRiso12⟩
  · -- === World (i): all five poor hubs at isoDeg 1, Σ_R = 11. ===
    have hPiso5 : (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card) = 5 := by
      have h1 : (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card) = 1 * P.card := by
        rw [Finset.sum_congr rfl (fun x hx => hall1 x hx), Finset.sum_const, smul_eq_mul,
            mul_comm]
      rw [h1, hP5]
    have hRhub8 : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card) = 8 := by omega
    have hPhub12 : (∑ x ∈ P, (G.neighborFinset x ∩ Hub).card) = 12 := by omega
    have hRRlink : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) + 4
        = ∑ u ∈ P, (G.neighborFinset u ∩ P).card := by omega
    obtain ⟨w, hwP, hpqw⟩ : ∃ y ∈ P, G.Adj p y ∨ G.Adj q y := by
      by_contra hcon
      push Not at hcon
      have := hnoedge_small hcon
      omega
    have hwh₂ : w ≠ h₂ := by
      rintro rfl
      rcases hpqw with h | h
      · exact hh₂noP p hpP h.symm
      · exact hh₂noP q hqP h.symm
    have hwp : w ≠ p := by
      rintro rfl
      rcases hpqw with h | h
      · exact (G.ne_of_adj h) rfl
      · exact hnpq h.symm
    have hwq : w ≠ q := by
      rintro rfl
      rcases hpqw with h | h
      · exact hnpq h
      · exact (G.ne_of_adj h) rfl
    have hwf : w ≠ f := by
      rintro rfl
      have hd := hPdeg4 w hwP
      omega
    exact Or.inl ⟨hP5, hRiso11, hall1,
      ⟨w, hPHub w hwP, hwh₂, hwp, hwq, hwf, hPdeg4 w hwP, hall1 w hwP, hpqw⟩,
      hz_deg3, by omega⟩
  · -- === World (ii): one isoDeg-0 poor hub h₀, Σ_R = 12. ===
    obtain ⟨h₀, hh₀P, hh₀iso0, hrest1⟩ := hh₀clause
    have hPiso4 : (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card) = 4 := by
      have hsplit0 : (∑ u ∈ P \ ({h₀} : Finset (Fin 20)), (G.neighborFinset u ∩ Iso).card)
          + (G.neighborFinset h₀ ∩ Iso).card
          = ∑ u ∈ P, (G.neighborFinset u ∩ Iso).card := by
        have h := Finset.sum_sdiff (f := fun u => (G.neighborFinset u ∩ Iso).card)
          (Finset.singleton_subset_iff.mpr hh₀P)
        simpa using h
      have hrest : (∑ u ∈ P \ ({h₀} : Finset (Fin 20)), (G.neighborFinset u ∩ Iso).card)
          = 1 * (P \ ({h₀} : Finset (Fin 20))).card := by
        rw [Finset.sum_congr rfl (fun u hu => hrest1 u hu), Finset.sum_const, smul_eq_mul,
            mul_comm]
      have hcard4 : (P \ ({h₀} : Finset (Fin 20))).card = 4 := by
        have h := Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hh₀P)
        rw [Finset.card_singleton] at h
        omega
      omega
    have hRhub7 : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card) = 7 := by omega
    have hPhub13 : (∑ x ∈ P, (G.neighborFinset x ∩ Hub).card) = 13 := by omega
    have hRRlink : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) + 6
        = ∑ u ∈ P, (G.neighborFinset u ∩ P).card := by omega
    have hRRle4 : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) ≤ 4 := by omega
    obtain ⟨y₀, hy₀P, hpqy₀⟩ : ∃ y ∈ P, G.Adj p y ∨ G.Adj q y := by
      by_contra hcon
      push Not at hcon
      have := hnoedge_small hcon
      omega
    by_cases hgood : ∃ y ∈ P, (G.neighborFinset y ∩ Iso).card = 1 ∧ (G.Adj p y ∨ G.Adj q y)
    · -- (ii-a): a poor hub with isoDeg 1 meets {p, q} — the n = 19 shape.
      obtain ⟨w, hwP, hwiso1, hpqw⟩ := hgood
      have hwh₂ : w ≠ h₂ := by
        rintro rfl
        rcases hpqw with h | h
        · exact hh₂noP p hpP h.symm
        · exact hh₂noP q hqP h.symm
      have hwp : w ≠ p := by
        rintro rfl
        rcases hpqw with h | h
        · exact (G.ne_of_adj h) rfl
        · exact hnpq h.symm
      have hwq : w ≠ q := by
        rintro rfl
        rcases hpqw with h | h
        · exact hnpq h
        · exact (G.ne_of_adj h) rfl
      have hwf : w ≠ f := by
        rintro rfl
        have hd := hPdeg4 w hwP
        omega
      exact Or.inr ⟨hP5, hRiso12, ⟨h₀, hh₀P, hh₀iso0, hrest1⟩, hz_deg3, hRRle4,
        Or.inl ⟨w, hPHub w hwP, hwh₂, hwp, hwq, hwf, hPdeg4 w hwP, hwiso1, hpqw⟩⟩
    · -- (ii-b): every {p, q}-attached poor hub is the isoDeg-0 hub h₀.
      push Not at hgood
      have hrestPQ : ∀ u ∈ P, u ≠ h₀ →
          (G.neighborFinset u ∩ Iso).card = 1 ∧ ¬G.Adj p u ∧ ¬G.Adj q u := by
        intro u huP hune
        have hu1 : (G.neighborFinset u ∩ Iso).card = 1 :=
          hrest1 u (Finset.mem_sdiff.mpr ⟨huP, Finset.notMem_singleton.mpr hune⟩)
        exact ⟨hu1, hgood u huP hu1⟩
      have hy₀iso0 : (G.neighborFinset y₀ ∩ Iso).card = 0 := by
        by_contra hne0
        have h1 : (G.neighborFinset y₀ ∩ Iso).card = 1 := by
          have := hPiso1 y₀ hy₀P
          omega
        obtain ⟨hnp, hnq⟩ := hgood y₀ hy₀P h1
        rcases hpqy₀ with h | h
        · exact hnp h
        · exact hnq h
      have hy₀h₀ : h₀ = y₀ := by
        by_contra hne
        have h1 := (hrestPQ y₀ hy₀P (fun hh => hne hh.symm)).1
        omega
      subst hy₀h₀
      have hh₀h₂ : h₀ ≠ h₂ := by
        rintro rfl
        omega
      have hh₀p : h₀ ≠ p := by
        rintro rfl
        rcases hpqy₀ with h | h
        · exact (G.ne_of_adj h) rfl
        · exact hnpq h.symm
      have hh₀q : h₀ ≠ q := by
        rintro rfl
        rcases hpqy₀ with h | h
        · exact hnpq h
        · exact (G.ne_of_adj h) rfl
      have hh₀f : h₀ ≠ f := by
        rintro rfl
        have hd := hPdeg4 h₀ hh₀P
        omega
      have hh₀mem : h₀ ∈ ({w₁, w₂} : Finset (Fin 20)) := by
        rw [← hdiffeq, Finset.mem_sdiff]
        refine ⟨hh₀P, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hh₀h₂, hh₀p, hh₀q⟩
      -- The symmetric forcing core: u the isoDeg-0 hub, v the other extra poor hub.
      have hcore : ∀ u v : Fin 20, u ≠ v →
          P \ ({h₂, p, q} : Finset (Fin 20)) = ({u, v} : Finset (Fin 20)) →
          u ∈ P → v ∈ P → (G.neighborFinset v ∩ Iso).card = 1 →
          (∑ x ∈ P, (G.neighborFinset x ∩ P).card)
            = (G.neighborFinset h₂ ∩ P).card + (G.neighborFinset p ∩ P).card
              + (G.neighborFinset q ∩ P).card + (G.neighborFinset u ∩ P).card
              + (G.neighborFinset v ∩ P).card →
          G.Adj p u ∧ G.Adj q u ∧
            (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 0 := by
        intro u v huv hPuv huP hvP hviso1 hsum
        have hPuv5 : P = ({h₂, p, q, u, v} : Finset (Fin 20)) := by
          have h1 : ({h₂, p, q} : Finset (Fin 20))
              ∪ (P \ ({h₂, p, q} : Finset (Fin 20))) = P :=
            Finset.union_sdiff_of_subset h3sub
          rw [hPuv] at h1
          rw [← h1]
          ext yy
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]
        obtain ⟨hnpv, hnqv⟩ := hgood v hvP hviso1
        have htv : (G.neighborFinset v ∩ P).card ≤ 1 := by
          have hsub' : G.neighborFinset v ∩ P ⊆ ({u} : Finset (Fin 20)) := by
            intro yy hyy
            rw [Finset.mem_inter, G.mem_neighborFinset] at hyy
            obtain ⟨hadj, hyyP⟩ := hyy
            have hyy5 : yy ∈ ({h₂, p, q, u, v} : Finset (Fin 20)) := by
              rw [← hPuv5]; exact hyyP
            simp only [Finset.mem_insert, Finset.mem_singleton] at hyy5 ⊢
            rcases hyy5 with rfl | rfl | rfl | rfl | rfl
            · exact absurd hadj.symm (hh₂noP v hvP)
            · exact absurd hadj.symm hnpv
            · exact absurd hadj.symm hnqv
            · rfl
            · exact absurd rfl (G.ne_of_adj hadj)
          calc (G.neighborFinset v ∩ P).card ≤ ({u} : Finset (Fin 20)).card :=
                Finset.card_le_card hsub'
            _ = 1 := Finset.card_singleton u
        have hsubp : G.neighborFinset p ∩ P ⊆ ({u} : Finset (Fin 20)) := by
          intro yy hyy
          rw [Finset.mem_inter, G.mem_neighborFinset] at hyy
          obtain ⟨hadj, hyyP⟩ := hyy
          have hyy5 : yy ∈ ({h₂, p, q, u, v} : Finset (Fin 20)) := by
            rw [← hPuv5]; exact hyyP
          simp only [Finset.mem_insert, Finset.mem_singleton] at hyy5 ⊢
          rcases hyy5 with rfl | rfl | rfl | rfl | rfl
          · exact absurd hadj.symm (hh₂noP p hpP)
          · exact absurd rfl (G.ne_of_adj hadj)
          · exact absurd hadj hnpq
          · rfl
          · exact absurd hadj hnpv
        have hsubq : G.neighborFinset q ∩ P ⊆ ({u} : Finset (Fin 20)) := by
          intro yy hyy
          rw [Finset.mem_inter, G.mem_neighborFinset] at hyy
          obtain ⟨hadj, hyyP⟩ := hyy
          have hyy5 : yy ∈ ({h₂, p, q, u, v} : Finset (Fin 20)) := by
            rw [← hPuv5]; exact hyyP
          simp only [Finset.mem_insert, Finset.mem_singleton] at hyy5 ⊢
          rcases hyy5 with rfl | rfl | rfl | rfl | rfl
          · exact absurd hadj.symm (hh₂noP q hqP)
          · exact absurd hadj.symm hnpq
          · exact absurd rfl (G.ne_of_adj hadj)
          · rfl
          · exact absurd hadj hnqv
        have htp : (G.neighborFinset p ∩ P).card ≤ 1 := by
          calc (G.neighborFinset p ∩ P).card ≤ ({u} : Finset (Fin 20)).card :=
                Finset.card_le_card hsubp
            _ = 1 := Finset.card_singleton u
        have htq : (G.neighborFinset q ∩ P).card ≤ 1 := by
          calc (G.neighborFinset q ∩ P).card ≤ ({u} : Finset (Fin 20)).card :=
                Finset.card_le_card hsubq
            _ = 1 := Finset.card_singleton u
        have hucap : (G.neighborFinset u ∩ P).card ≤ 3 := by
          have hsub' : G.neighborFinset u ∩ P ⊆ ({p, q, v} : Finset (Fin 20)) := by
            intro yy hyy
            rw [Finset.mem_inter, G.mem_neighborFinset] at hyy
            obtain ⟨hadj, hyyP⟩ := hyy
            have hyy5 : yy ∈ ({h₂, p, q, u, v} : Finset (Fin 20)) := by
              rw [← hPuv5]; exact hyyP
            simp only [Finset.mem_insert, Finset.mem_singleton] at hyy5 ⊢
            rcases hyy5 with rfl | rfl | rfl | rfl | rfl
            · exact absurd hadj.symm (hh₂noP u huP)
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact absurd rfl (G.ne_of_adj hadj)
            · exact Or.inr (Or.inr rfl)
          exact le_trans (Finset.card_le_card hsub') (hle3 p q v)
        have hpu : G.Adj p u := by
          by_contra hnpu
          have htp0 : (G.neighborFinset p ∩ P).card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro yy hyy
            have hyyu : yy ∈ ({u} : Finset (Fin 20)) := hsubp hyy
            rw [Finset.mem_singleton] at hyyu
            subst hyyu
            rw [Finset.mem_inter, G.mem_neighborFinset] at hyy
            exact hnpu hyy.1
          omega
        have hqu : G.Adj q u := by
          by_contra hnqu
          have htq0 : (G.neighborFinset q ∩ P).card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro yy hyy
            have hyyu : yy ∈ ({u} : Finset (Fin 20)) := hsubq hyy
            rw [Finset.mem_singleton] at hyyu
            subst hyyu
            rw [Finset.mem_inter, G.mem_neighborFinset] at hyy
            exact hnqu hyy.1
          omega
        exact ⟨hpu, hqu, by omega⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh₀mem
      rcases hh₀mem with heq | heq
      · -- h₀ = w₁: the other extra poor hub is w₂.
        have hviso1 : (G.neighborFinset w₂ ∩ Iso).card = 1 :=
          (hrestPQ w₂ hw₂P (by rw [heq]; exact hw12ne.symm)).1
        obtain ⟨hpw, hqw, hRR0⟩ := hcore h₀ w₂ (by rw [heq]; exact hw12ne)
          (by rw [heq]; exact hdiffeq) hh₀P hw₂P hviso1 (by rw [heq]; exact hsumPP)
        exact Or.inr ⟨hP5, hRiso12, ⟨h₀, hh₀P, hh₀iso0, hrest1⟩, hz_deg3, hRRle4,
          Or.inr ⟨h₀, hPHub h₀ hh₀P, hh₀h₂, hh₀p, hh₀q, hh₀f, hPdeg4 h₀ hh₀P, hh₀iso0,
            hpw, hqw, hrestPQ, hRR0⟩⟩
      · -- h₀ = w₂: the other extra poor hub is w₁.
        have hviso1 : (G.neighborFinset w₁ ∩ Iso).card = 1 :=
          (hrestPQ w₁ hw₁P (by rw [heq]; exact hw12ne)).1
        obtain ⟨hpw, hqw, hRR0⟩ := hcore h₀ w₁ (by rw [heq]; exact hw12ne.symm)
          (by rw [heq, hdiffeq]; exact Finset.pair_comm w₁ w₂) hh₀P hw₁P hviso1 (by
            rw [heq]
            omega)
        exact Or.inr ⟨hP5, hRiso12, ⟨h₀, hh₀P, hh₀iso0, hrest1⟩, hz_deg3, hRRle4,
          Or.inr ⟨h₀, hPHub h₀ hh₀P, hh₀h₂, hh₀p, hh₀q, hh₀f, hPdeg4 h₀ hh₀P, hh₀iso0,
            hpw, hqw, hrestPQ, hRR0⟩⟩

end N20

end ACMax
