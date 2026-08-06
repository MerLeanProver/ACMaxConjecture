import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub

/-! # CASE C both-poor: the World-(ii) kill (`n = 20`)

Kills World (ii) of the both-poor budget at `n = 20` (`Σ_R isoDeg = 12`, one
isoDeg-`0` poor hub, `∑_R richDeg ≤ 4`).  The shared-twin double count
(`cherry_double_count`) with every non-adjacent rich pair sharing at least one
twin (`hno2hub`) gives `∑_t k_t² ≥ 12 + 20 - 4 = 28 > 24 = 2 ∑_t k_t`, forcing
at least TWO twins whose three hub-neighbours all lie in the rich layer `R`.
Neither is the structural twin `c`: its hub-neighbourhood is the rigid
`{h₂, g, r_t}` and `h₂` is poor, so `|N c ∩ R| ≤ 2`.  All three twins avoid
the degree-`5` hub `f` (`f ∉ R` and `f ∉ {h₂, g, r_t}` by degree), leaving
`isoDeg f ≤ 7 - 3 = 4 < 5` and contradicting `hfiso5`.  This closes World (ii)
uniformly, without touching the `(ii-a)`/`(ii-b)` dichotomy. -/

namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **CASE C both-poor World-(ii) kill.**  In the `Σ_R isoDeg = 12` world the
shared-twin double count forces two full-`R` twins, which together with the
structural twin `c` starve the degree-`5` hub `f` of its five
`Iso`-neighbours. -/
theorem octahedron_both_poor_world_ii_1041_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hdisj : Disjoint Hub Iso) (_hsum18 : Hub.card + Iso.card = 18)
    (_hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (_hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (_hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (_hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (_hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (_hHub : Hub.card = 11) (hIso : Iso.card = 7) (_hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (_hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (_hg : g ∈ Hub) (hgd : G.degree g = 4)
    (_hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 20) (_hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (_hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (_hz2 : G.Adj z h₂) (_hgz : ¬G.Adj g z) (_hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (_hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (_hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
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
    (_hz'Z : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (_hzz' : G.Adj z z') (_hz'deg3 : G.degree z' = 3)
    (_hz'iso0 : (G.neighborFinset z' ∩ Iso).card = 0)
    (_hNz'eq : G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 20)))
    (_hp : p ∈ Hub) (_hq : q ∈ Hub) (_hdp : G.degree p = 4) (_hdq : G.degree q = 4)
    (_hpq : p ≠ q) (_hz'p : G.Adj z' p) (_hz'q : G.Adj z' q)
    (_hnpq : ¬G.Adj p q)
    (_hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0)
    (_hppoor : (G.neighborFinset p ∩ Iso).card ≤ 1)
    (_hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1)
    (_hph₂ : p ≠ h₂) (_hqh₂ : q ≠ h₂)
    (_hP5 : (Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1)).card
      = 5)
    (hRiso12 : (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Iso).card) = 12)
    (_hh₀ : ∃ h₀ ∈ Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1),
      (G.neighborFinset h₀ ∩ Iso).card = 0 ∧
      ∀ x ∈ Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1) \
        ({h₀} : Finset (Fin 20)), (G.neighborFinset x ∩ Iso).card = 1)
    (_hzdeg : G.degree z = 3)
    (heRR : (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Hub.filter
        (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 4)
    (_hdich : (∃ w : Fin 20, w ∈ Hub ∧ w ≠ h₂ ∧ w ≠ p ∧ w ≠ q ∧ w ≠ f ∧ G.degree w = 4 ∧
        (G.neighborFinset w ∩ Iso).card = 1 ∧ (G.Adj p w ∨ G.Adj q w)) ∨
      (∃ w : Fin 20, w ∈ Hub ∧ w ≠ h₂ ∧ w ≠ p ∧ w ≠ q ∧ w ≠ f ∧ G.degree w = 4 ∧
        (G.neighborFinset w ∩ Iso).card = 0 ∧ G.Adj p w ∧ G.Adj q w ∧
        (∀ x ∈ Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1),
          x ≠ w → (G.neighborFinset x ∩ Iso).card = 1 ∧ ¬G.Adj p x ∧ ¬G.Adj q x) ∧
        (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset r ∩ Hub.filter
            (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) = 0)) :
    False := by
  classical
  -- === Structure extraction. ===
  obtain ⟨c, r_t, _r_z, _a, _b, hReq, hRcard5, hcIso, _hgc, _hh₂c, _hr_tc, hNc, _hNz, _hNh₂,
    _hr_zz, _hah₂, _hbh₂, _hr_tHub, hr_td4, _hr_zHub, _hr_zd4, _haHub, _had4, _hbHub,
    _hbd4⟩ := hstruct
  -- === The rich layer R. ===
  set R : Finset (Fin 20) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRcard : R.card = 5 := by rw [hReq]; exact hRcard5
  have hRsub : R ⊆ Hub := by rw [hRdef]; exact Finset.filter_subset _ _
  have hRdeg4 : ∀ r ∈ R, G.degree r = 4 := by
    intro r hr; rw [hRdef, Finset.mem_filter] at hr; exact hr.2.1
  have hRiso2 : ∀ r ∈ R, 2 ≤ (G.neighborFinset r ∩ Iso).card := by
    intro r hr; rw [hRdef, Finset.mem_filter] at hr; exact hr.2.2
  -- === Card of `N u ∩ S` as a sum of adjacency indicators over `S`. ===
  have hcardInter : ∀ (u : Fin 20) (S : Finset (Fin 20)),
      (G.neighborFinset u ∩ S).card = ∑ v ∈ S, (if G.Adj u v then (1 : ℕ) else 0) := by
    intro u S
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun v _ => by simp only [G.mem_neighborFinset])
  -- === Incidence double count `Iso`–`R`: ∑_t k_t = 12. ===
  have hksum : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card) = 12 := by
    have hinc : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
        = ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card := by
      calc (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
          = ∑ t ∈ Iso, ∑ r ∈ R, (if G.Adj t r then (1 : ℕ) else 0) :=
            Finset.sum_congr rfl (fun t _ => hcardInter t R)
        _ = ∑ r ∈ R, ∑ t ∈ Iso, (if G.Adj t r then (1 : ℕ) else 0) := Finset.sum_comm
        _ = ∑ r ∈ R, ∑ t ∈ Iso, (if G.Adj r t then (1 : ℕ) else 0) :=
            Finset.sum_congr rfl (fun r _ =>
              Finset.sum_congr rfl (fun t _ => by rw [SimpleGraph.adj_comm]))
        _ = ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card :=
            Finset.sum_congr rfl (fun r _ => (hcardInter r Iso).symm)
    rw [hinc, hRiso12]
  -- === Each twin meets `R` in at most `3`. ===
  have hk3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card
        ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsub)
      _ = 3 := hiso3 t ht
  -- === Non-adjacent rich pairs share at least one twin (else `hno2hub` fires). ===
  have hshare_ge1 : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ¬G.Adj u v →
      1 ≤ (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
    intro u hu v hv hne hnadjuv
    by_contra hcon
    rw [not_le, Nat.lt_one_iff] at hcon
    have hpu : ((G.neighborFinset u ∩ Iso) ∩ G.neighborFinset v).card = 0 := by
      rw [Finset.inter_right_comm]; exact hcon
    have hpv : ((G.neighborFinset v ∩ Iso) ∩ G.neighborFinset u).card = 0 := by
      rw [Finset.inter_right_comm, Finset.inter_comm (G.neighborFinset v) (G.neighborFinset u)]
      exact hcon
    have hpu2 : 2 ≤ ((G.neighborFinset u ∩ Iso) \ G.neighborFinset v).card := by
      have := Finset.card_inter_add_card_sdiff (G.neighborFinset u ∩ Iso) (G.neighborFinset v)
      rw [hpu] at this
      have h2 := hRiso2 u hu
      omega
    have hpv2 : 2 ≤ ((G.neighborFinset v ∩ Iso) \ G.neighborFinset u).card := by
      have := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ Iso) (G.neighborFinset u)
      rw [hpv] at this
      have h2 := hRiso2 v hv
      omega
    exact hno2hub ⟨u, v, hRsub hu, hRsub hv, hRdeg4 u hu, hRdeg4 v hv, hne, hnadjuv, hpu2, hpv2⟩
  -- === Per-row lower bound: the row `u` contributes `isoDeg u + 4 - richDeg u`. ===
  have hrow : ∀ u ∈ R,
      (G.neighborFinset u ∩ Iso).card + 4
        ≤ (∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
          + (G.neighborFinset u ∩ R).card := by
    intro u hu
    have hsplit : (∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        = (G.neighborFinset u ∩ Iso).card
          + ∑ v ∈ R.erase u, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
      rw [← Finset.add_sum_erase R _ hu, Finset.inter_self]
    have hadjcard : (∑ v ∈ R.erase u, (if G.Adj u v then (1 : ℕ) else 0))
        = (G.neighborFinset u ∩ R).card := by
      rw [hcardInter u R,
        ← Finset.sum_erase R
          (by simp [SimpleGraph.irrefl] : (if G.Adj u u then (1 : ℕ) else 0) = 0)]
    have hNN4 : (∑ v ∈ R.erase u, (if ¬G.Adj u v then (1 : ℕ) else 0))
        + (G.neighborFinset u ∩ R).card = 4 := by
      have hpt : ∀ v : Fin 20,
          (if ¬G.Adj u v then (1 : ℕ) else 0) + (if G.Adj u v then (1 : ℕ) else 0) = 1 := by
        intro v; by_cases h : G.Adj u v <;> simp [h]
      have hsum1 : (∑ v ∈ R.erase u,
          ((if ¬G.Adj u v then (1 : ℕ) else 0) + (if G.Adj u v then (1 : ℕ) else 0)))
          = (R.erase u).card := by
        rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_const, smul_eq_mul, mul_one]
      rw [Finset.sum_add_distrib, hadjcard, Finset.card_erase_of_mem hu, hRcard] at hsum1
      omega
    have hge : (∑ v ∈ R.erase u, (if ¬G.Adj u v then (1 : ℕ) else 0))
        ≤ ∑ v ∈ R.erase u, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
      apply Finset.sum_le_sum
      intro v hv
      by_cases h : G.Adj u v
      · rw [if_neg (not_not_intro h)]
        exact Nat.zero_le _
      · rw [if_pos h]
        exact hshare_ge1 u hu v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv).symm h
    omega
  -- === Master: `32 ≤ D + e_RR`, hence `28 ≤ D`. ===
  have hmaster : 32
      ≤ (∑ u ∈ R, ∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        + (∑ u ∈ R, (G.neighborFinset u ∩ R).card) := by
    have hsum := Finset.sum_le_sum hrow
    simp only [Finset.sum_add_distrib] at hsum
    rw [hRiso12] at hsum
    have hconst : (∑ _x ∈ R, (4 : ℕ)) = 20 := by
      rw [Finset.sum_const, hRcard]; rfl
    rw [hconst] at hsum
    omega
  -- === The shared-twin double count identity and the LP upper bound. ===
  have hDC := cherry_double_count G R Iso
  have hDub : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card)
      ≤ 24 + 3 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card := by
    have hsq : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
        ≤ 2 * (G.neighborFinset t ∩ R).card
          + 3 * (if (G.neighborFinset t ∩ R).card = 3 then 1 else 0) := by
      intro t ht
      have hle := hk3 t ht
      rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1
          ∨ (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
        with h | h | h | h <;> rw [h] <;> decide
    calc (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card)
        ≤ ∑ t ∈ Iso, (2 * (G.neighborFinset t ∩ R).card
            + 3 * (if (G.neighborFinset t ∩ R).card = 3 then 1 else 0)) := Finset.sum_le_sum hsq
      _ = 2 * (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
            + 3 * (∑ t ∈ Iso, (if (G.neighborFinset t ∩ R).card = 3 then (1 : ℕ) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 24 + 3 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card := by
          rw [hksum, Finset.sum_boole, Nat.cast_id]
  -- === At least two twins have `k = 3`; extract them. ===
  have ha3 : 2 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card := by omega
  obtain ⟨t₁, ht₁, t₂, ht₂, hne12⟩ := Finset.one_lt_card.mp (by omega :
    1 < (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
  have ht₁I : t₁ ∈ Iso := (Finset.mem_filter.mp ht₁).1
  have ht₂I : t₂ ∈ Iso := (Finset.mem_filter.mp ht₂).1
  have hA1card : (G.neighborFinset t₁ ∩ R).card = 3 := (Finset.mem_filter.mp ht₁).2
  have hA2card : (G.neighborFinset t₂ ∩ R).card = 3 := (Finset.mem_filter.mp ht₂).2
  -- === Full-`R` twins avoid `f`. ===
  have hfnotadj : ∀ t : Fin 20, t ∈ Iso → (G.neighborFinset t ∩ R).card = 3 → ¬G.Adj f t := by
    intro t htI htk hadj
    have hfull : G.neighborFinset t ∩ R = G.neighborFinset t ∩ Hub := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.inter_subset_inter (Finset.Subset.refl _) hRsub
      · have h1 := hiso3 t htI
        omega
    have hfmem : f ∈ G.neighborFinset t ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset t f).mpr hadj.symm, hfHub⟩
    rw [← hfull] at hfmem
    have hf4 := hRdeg4 f (Finset.mem_inter.mp hfmem).2
    omega
  -- === The structural twin `c` has at most two `R`-neighbours. ===
  have hh₂notR : h₂ ∉ R := by
    rw [hRdef, Finset.mem_filter]
    rintro ⟨-, -, hge2⟩
    omega
  have hcR2 : (G.neighborFinset c ∩ R).card ≤ 2 := by
    have hsub : G.neighborFinset c ∩ R ⊆ ({g, r_t} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter] at hy
      have hyHub : y ∈ G.neighborFinset c ∩ Hub :=
        Finset.mem_inter.mpr ⟨hy.1, hRsub hy.2⟩
      rw [hNc] at hyHub
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyHub ⊢
      rcases hyHub with rfl | rfl | rfl
      · exact absurd hy.2 hh₂notR
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hpair := Finset.card_insert_le g ({r_t} : Finset (Fin 20))
    have hsing := Finset.card_singleton r_t
    have hle := Finset.card_le_card hsub
    omega
  have hct₁ : c ≠ t₁ := by rintro rfl; omega
  have hct₂ : c ≠ t₂ := by rintro rfl; omega
  -- === `f` avoids `c` as well (its hub-neighbourhood is `{h₂, g, r_t}`). ===
  have hfnotc : ¬G.Adj f c := by
    intro hadj
    have hfmem : f ∈ G.neighborFinset c ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c f).mpr hadj.symm, hfHub⟩
    rw [hNc] at hfmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfmem
    rcases hfmem with rfl | rfl | rfl <;> omega
  -- === Starvation: `f` needs five `Iso`-neighbours among the remaining four. ===
  have hsub3 : ({t₁, t₂, c} : Finset (Fin 20)) ⊆ Iso := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ht₁I
    · exact ht₂I
    · exact hcIso
  have hcard3 : ({t₁, t₂, c} : Finset (Fin 20)).card = 3 := by
    have hnot : t₁ ∉ ({t₂, c} : Finset (Fin 20)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne12, fun h => hct₁ h.symm⟩
    rw [Finset.card_insert_of_notMem hnot, Finset.card_pair (fun h => hct₂ h.symm)]
  have hNfsub : G.neighborFinset f ∩ Iso ⊆ Iso \ ({t₁, t₂, c} : Finset (Fin 20)) := by
    intro y hy
    rw [Finset.mem_inter] at hy
    have hadj : G.Adj f y := (G.mem_neighborFinset f y).mp hy.1
    rw [Finset.mem_sdiff]
    refine ⟨hy.2, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact hfnotadj t₁ ht₁I hA1card (h ▸ hadj)
    · exact hfnotadj t₂ ht₂I hA2card (h ▸ hadj)
    · exact hfnotc (h ▸ hadj)
  have hcs : (Iso \ ({t₁, t₂, c} : Finset (Fin 20))).card = 4 := by
    rw [Finset.card_sdiff_of_subset hsub3, hIso, hcard3]
  have hle := Finset.card_le_card hNfsub
  omega

end N20

end ACMax
