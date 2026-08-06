import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf

/-! # The anchor-saturated residual kill for the (10,8,42) corner (`n = 20`)

Node D of the blocked `(|Hub|, |Iso|, Σ_Hub deg) = (10, 8, 42)` cluster: the third disjunct of
`rich_count_1042_twenty` — `|R| ∈ {4, 5}`, an iso-saturated degree-`5` anchor,
`Σ_{D₄} isoDeg ≤ 15`, and the master inequality — is impossible in the blocked world.

The kill: the anchor share `s = |N f ∩ N f' ∩ Iso|` is capped at `2` by `hK23`
(`5 + 5 + 3·3 = 19`; the saturated anchor is non-adjacent to everything in `Hub`), so the two
anchors cover all of `Iso` up to at most one twin.  The `g`–`h₂` shared twin `c` carries the hub
slots `{g, h₂, w₃}`, and the blocked structure confines `R ∖ {g}` to `{w₃} ∪ (N h₂ ∩ Hub) ∪ {w}`
(`w` the second hub of the `M`-end `z`), of capacity `1 + 2 + 1`.  At `|R| = 4` the master
inequality forces both anchors saturated, so every twin is anchor-covered (`k_t ≤ 2`), `w₃` is an
anchor and `k_c = 1`; the exact shared-twin double count gives `2n₂ + ERR = 12` while
`2n₂ + 1 ≤ Σk = 10`, so `ERR ≥ 4` — but the degree-slot ledger `ERR + q + Σ isoDeg + Σz ≤ 16`
with `q ≥ 2`, `Σz ≥ 1` caps `ERR ≤ 3`.  At `|R| = 5` the capacity count forces `w₃ ∈ R`, so `c`
is anchor-uncovered, pinning `isoDeg f' = 4`, `s = 2`, `Σ_{D₄} = 15`; coverage off `c` gives
`k_t ≤ 2` and `n₂ ≤ 6`, whence `ERR = 20 − 2n₂ ≥ 8` against the slot cap `ERR ≤ 6`. -/

namespace ACMax

open scoped Classical

namespace N20

/-- **The anchor-anchor high-share `K₂,₃` kill.**  Two distinct non-adjacent degree-`5` hubs
sharing `≥ 3` twins of degree `3` form a forbidden `K₂,₃` of degree sum `5 + 5 + 3·3 = 19`. -/
theorem anchor_share_k23_1042_twenty (G : SimpleGraph (Fin 20)) (Iso : Finset (Fin 20))
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hisoHub : ∀ t ∈ Iso, ∀ w : Fin 20, G.Adj t w → w ∉ Iso)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (x f : Fin 20) (hxd : G.degree x = 5) (hfd : G.degree f = 5) (hxf : x ≠ f)
    (hnadj : ¬G.Adj x f)
    (hshare3 : 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card) :
    False := by
  classical
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hshare3
  obtain ⟨c, d, e, hcd, hce, hde, hTeq⟩ := Finset.card_eq_three.mp hTcard
  have hmem : ∀ w ∈ ({c, d, e} : Finset (Fin 20)),
      G.Adj x w ∧ G.Adj f w ∧ w ∈ Iso := by
    intro w hw
    have hwT : w ∈ T := hTeq ▸ hw
    have := hTsub hwT
    rw [Finset.mem_inter, Finset.mem_inter] at this
    exact ⟨(G.mem_neighborFinset _ _).mp this.1.1,
      (G.mem_neighborFinset _ _).mp this.1.2, this.2⟩
  obtain ⟨hxc, hfc, hcIso⟩ := hmem c (by simp)
  obtain ⟨hxd', hfd', hdIso⟩ := hmem d (by simp)
  obtain ⟨hxe, hfe, heIso⟩ := hmem e (by simp)
  have hncd : ¬G.Adj c d := fun h => hisoHub c hcIso d h hdIso
  have hnce : ¬G.Adj c e := fun h => hisoHub c hcIso e h heIso
  have hnde : ¬G.Adj d e := fun h => hisoHub d hdIso e h heIso
  have hc3 : G.degree c = 3 := hisodeg3 c hcIso
  have hd3 : G.degree d = 3 := hisodeg3 d hdIso
  have he3 : G.degree e = 3 := hisodeg3 e heIso
  have hxc' : x ≠ c := by intro h; rw [h, hc3] at hxd; omega
  have hxd'' : x ≠ d := by intro h; rw [h, hd3] at hxd; omega
  have hxe' : x ≠ e := by intro h; rw [h, he3] at hxd; omega
  have hfc' : f ≠ c := by intro h; rw [h, hc3] at hfd; omega
  have hfd'' : f ≠ d := by intro h; rw [h, hd3] at hfd; omega
  have hfe' : f ≠ e := by intro h; rw [h, he3] at hfd; omega
  have hcard5 : ({x, f, c, d, e} : Finset (Fin 20)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hxf, hxc', hxd'', hxe']),
      Finset.card_insert_of_notMem (by simp [hfc', hfd'', hfe']),
      Finset.card_insert_of_notMem (by simp [hcd, hce]),
      Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]
  exact hK23 ⟨x, f, c, d, e, hcard5, hxc, hxd', hxe, hfc, hfd', hfe, hnadj,
    hncd, hnce, hnde, by rw [hxd, hfd, hc3, hd3, he3]⟩

/-- **The exact rich square identity.**  In the no-two-hub world a non-adjacent pair of rich
degree-`4` hubs shares exactly one twin (`hno2hub` forces `≥ 1`, `hshare` caps at `1`) and an
adjacent pair shares none (`hT`: the triangle `{u, v, t}` has degree sum `4 + 4 + 3 = 11`), so
the shared-twin double count collapses to the exact identity
`Σ_t k_t² + Σ_r |N r ∩ R| + |R| = Σ_r isoDeg r + |R|²`. -/
theorem rich_square_identity_1042_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso R : Finset (Fin 20))
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRsub : R ⊆ Hub) (hRdeg4 : ∀ r ∈ R, G.degree r = 4)
    (hRiso2 : ∀ r ∈ R, 2 ≤ (G.neighborFinset r ∩ Iso).card) :
    (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card)
        + (∑ u ∈ R, (G.neighborFinset u ∩ R).card) + R.card
      = (∑ u ∈ R, (G.neighborFinset u ∩ Iso).card) + R.card * R.card := by
  classical
  have hcardInter : ∀ (u : Fin 20) (S : Finset (Fin 20)),
      (G.neighborFinset u ∩ S).card = ∑ v ∈ S, (if G.Adj u v then (1 : ℕ) else 0) := by
    intro u S
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun v _ => by simp only [G.mem_neighborFinset])
  -- Exact pair shares: `0` on adjacent pairs, `1` on non-adjacent pairs.
  have hpairshare : ∀ u ∈ R, ∀ v ∈ R, u ≠ v →
      (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card
        = if G.Adj u v then 0 else 1 := by
    intro u hu v hv huv
    by_cases hadj : G.Adj u v
    · rw [if_pos hadj, Finset.card_eq_zero]
      by_contra hne
      obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      rw [Finset.mem_inter, Finset.mem_inter] at ht
      have hut : G.Adj u t := (G.mem_neighborFinset _ _).mp ht.1.1
      have hvt : G.Adj v t := (G.mem_neighborFinset _ _).mp ht.1.2
      have ht3 : G.degree t = 3 := hisodeg3 t ht.2
      have hdegsum : G.degree u + G.degree v + G.degree t ≤ 11 := by
        have h1 := hRdeg4 u hu
        have h2 := hRdeg4 v hv
        omega
      exact hT ⟨u, v, t, huv, hvt.ne, hut.ne, hadj, hvt, hut, hdegsum⟩
    · rw [if_neg hadj]
      have hle : (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card ≤ 1 :=
        hshare u (hRsub hu) (hRdeg4 u hu) v (hRsub hv) (hRdeg4 v hv) huv hadj
      have hge : 1 ≤ (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
        by_contra hcon
        rw [not_le, Nat.lt_one_iff] at hcon
        have hpu : ((G.neighborFinset u ∩ Iso) ∩ G.neighborFinset v).card = 0 := by
          rw [Finset.inter_right_comm]; exact hcon
        have hpv : ((G.neighborFinset v ∩ Iso) ∩ G.neighborFinset u).card = 0 := by
          rw [Finset.inter_right_comm,
            Finset.inter_comm (G.neighborFinset v) (G.neighborFinset u)]
          exact hcon
        have hpu2 : 2 ≤ ((G.neighborFinset u ∩ Iso) \ G.neighborFinset v).card := by
          have hkey := Finset.card_inter_add_card_sdiff (G.neighborFinset u ∩ Iso)
            (G.neighborFinset v)
          rw [hpu] at hkey
          have h2 := hRiso2 u hu
          omega
        have hpv2 : 2 ≤ ((G.neighborFinset v ∩ Iso) \ G.neighborFinset u).card := by
          have hkey := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ Iso)
            (G.neighborFinset u)
          rw [hpv] at hkey
          have h2 := hRiso2 v hv
          omega
        exact hno2hub ⟨u, v, hRsub hu, hRsub hv, hRdeg4 u hu, hRdeg4 v hv, huv, hadj,
          hpu2, hpv2⟩
      omega
  -- Row identity: `Σ_v share(u, v) + |N u ∩ R| + 1 = isoDeg u + |R|`.
  have hrow : ∀ u ∈ R,
      (∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
          + (G.neighborFinset u ∩ R).card + 1
        = (G.neighborFinset u ∩ Iso).card + R.card := by
    intro u hu
    have hsplit : (∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        = (G.neighborFinset u ∩ Iso).card
          + ∑ v ∈ R.erase u, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
      rw [← Finset.add_sum_erase R _ hu, Finset.inter_self]
    have hoffsum : (∑ v ∈ R.erase u, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        = ∑ v ∈ R.erase u, (if G.Adj u v then (0 : ℕ) else 1) :=
      Finset.sum_congr rfl (fun v hv => hpairshare u hu v (Finset.mem_of_mem_erase hv)
        (Finset.ne_of_mem_erase hv).symm)
    have hadjcard : (∑ v ∈ R.erase u, (if G.Adj u v then (1 : ℕ) else 0))
        = (G.neighborFinset u ∩ R).card := by
      rw [hcardInter u R,
        ← Finset.sum_erase R
          (by simp [SimpleGraph.irrefl] : (if G.Adj u u then (1 : ℕ) else 0) = 0)]
    have hone : ∀ v ∈ R.erase u,
        (if G.Adj u v then (0 : ℕ) else 1) + (if G.Adj u v then (1 : ℕ) else 0) = 1 := by
      intro v _
      by_cases h : G.Adj u v <;> simp [h]
    have hsum1 : (∑ v ∈ R.erase u,
        ((if G.Adj u v then (0 : ℕ) else 1) + (if G.Adj u v then (1 : ℕ) else 0)))
        = (R.erase u).card := by
      rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.sum_add_distrib] at hsum1
    have hcardE : (R.erase u).card + 1 = R.card := by
      rw [Finset.card_erase_of_mem hu]
      have hpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨u, hu⟩
      omega
    omega
  -- Sum the rows and apply the shared-twin double count.
  have hL : (∑ u ∈ R, ((∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        + (G.neighborFinset u ∩ R).card + 1))
      = (∑ u ∈ R, ∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        + (∑ u ∈ R, (G.neighborFinset u ∩ R).card) + R.card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      mul_one]
  have hR' : (∑ u ∈ R, ((G.neighborFinset u ∩ Iso).card + R.card))
      = (∑ u ∈ R, (G.neighborFinset u ∩ Iso).card) + R.card * R.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  have hkey : (∑ u ∈ R, ∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        + (∑ u ∈ R, (G.neighborFinset u ∩ R).card) + R.card
      = (∑ u ∈ R, (G.neighborFinset u ∩ Iso).card) + R.card * R.card := by
    rw [← hL, ← hR']
    exact Finset.sum_congr rfl hrow
  rw [cherry_double_count G R Iso] at hkey
  exact hkey


set_option maxHeartbeats 1000000 in
/-- **The anchor-saturated residual kill for the `(10, 8, 42)` corner.**  In the blocked world
(the iso-degree-`1` slot hub `h₂` on the `M`-end `z`, sharing exactly one twin with the rich hub
`g`, every rich degree-`4` hub blocked through `{c, h₂, z}`), the anchor-saturated payload of
`rich_count_1042_twenty` — `|R| ∈ {4, 5}`, an iso-saturated degree-`5` anchor,
`Σ_{D₄} isoDeg ≤ 15`, the master inequality, and the failed combined bound at `|R| = 5` — is
impossible. -/
theorem anchor_sat_kill_1042_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 8) (hdsum : ∑ w ∈ Hub, G.degree w = 42)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
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
    (hz2 : G.Adj z h₂) (_hgz : ¬G.Adj g z) (_hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
    (hR45 : (Hub.filter (fun h => G.degree h = 4
          ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 4
      ∨ (Hub.filter (fun h => G.degree h = 4
          ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5)
    (hsat : ∃ f ∈ Hub, G.degree f = 5 ∧ (G.neighborFinset f ∩ Iso).card = 5)
    (hD4le : (∑ h ∈ Hub.filter (fun h => G.degree h = 4),
      (G.neighborFinset h ∩ Iso).card) ≤ 15)
    (hmaster : (Hub.filter (fun h => G.degree h = 4
          ∧ (G.neighborFinset h ∩ Iso).card = 0)).card
        + (∑ h ∈ Hub.filter (fun h => G.degree h = 4), (G.neighborFinset h ∩ Iso).card)
      ≤ (Hub.filter (fun h => G.degree h = 4
          ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card + 10)
    (_hCMB : (Hub.filter (fun h => G.degree h = 4
          ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 →
      14 ≤ (∑ r ∈ Hub.filter (fun h => G.degree h = 4
              ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card), (G.neighborFinset r ∩ Iso).card)
        + (∑ r ∈ Hub.filter (fun h => G.degree h = 4
              ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
            (G.neighborFinset r
              ∩ Hub.filter (fun h => G.degree h = 4
                ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card)) :
    False := by
  classical
  -- === Degree partition: eight deg-4 hubs, two deg-5 anchors. ===
  obtain ⟨f, hfHub, hfd, hfsat⟩ := hsat
  set D4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh
    have h1 := hdeg h hh
    have h2 := hdeg5 h hh
    omega
  have hD4sub : D4 ⊆ Hub := by rw [hD4def]; exact Finset.filter_subset _ _
  have hD5sub : D5 ⊆ Hub := by rw [hD5def]; exact Finset.filter_subset _ _
  have hD4deg4 : ∀ h ∈ D4, G.degree h = 4 := by
    intro h hh
    rw [hD4def, Finset.mem_filter] at hh
    exact hh.2
  have hD5deg5 : ∀ h ∈ D5, G.degree h = 5 := by
    intro h hh
    rw [hD5def, Finset.mem_filter] at hh
    rcases hdeg45 h hh.1 with h4 | h5
    · exact absurd h4 hh.2
    · exact h5
  have hcardpart : D4.card + D5.card = 10 := by
    rw [hD4def, hD5def, Finset.card_filter_add_card_filter_not]
    exact hHub
  have hsumdeg : (∑ h ∈ D4, G.degree h) + (∑ h ∈ D5, G.degree h) = 42 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]
    exact hdsum
  have hsum4 : (∑ h ∈ D4, G.degree h) = 4 * D4.card := by
    calc (∑ h ∈ D4, G.degree h) = ∑ _h ∈ D4, 4 :=
          Finset.sum_congr rfl fun h hh => hD4deg4 h hh
      _ = 4 * D4.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum5 : (∑ h ∈ D5, G.degree h) = 5 * D5.card := by
    calc (∑ h ∈ D5, G.degree h) = ∑ _h ∈ D5, 5 :=
          Finset.sum_congr rfl fun h hh => hD5deg5 h hh
      _ = 5 * D5.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hsum4, hsum5] at hsumdeg
  have hD4card : D4.card = 8 := by omega
  have hD5card : D5.card = 2 := by omega
  -- === The second anchor `f'`. ===
  have hfD5 : f ∈ D5 := by
    rw [hD5def, Finset.mem_filter]
    exact ⟨hfHub, by omega⟩
  have herase1 : (D5.erase f).card = 1 := by
    rw [Finset.card_erase_of_mem hfD5, hD5card]
  obtain ⟨f', hf'eq⟩ := Finset.card_eq_one.mp herase1
  have hf'mem : f' ∈ D5.erase f := by
    rw [hf'eq]
    exact Finset.mem_singleton_self f'
  have hf'D5 : f' ∈ D5 := Finset.mem_of_mem_erase hf'mem
  have hff' : f ≠ f' := (Finset.ne_of_mem_erase hf'mem).symm
  have hf'Hub : f' ∈ Hub := hD5sub hf'D5
  have hf'd : G.degree f' = 5 := hD5deg5 f' hf'D5
  have hD5pair : D5 = {f, f'} := by
    rw [← Finset.insert_erase hfD5, hf'eq]
  -- === Saturation: `N f ⊆ Iso`, so `f` is non-adjacent to every hub. ===
  have hNfIso : G.neighborFinset f ⊆ Iso := by
    have hcard : (G.neighborFinset f).card = 5 := by
      rw [G.card_neighborFinset_eq_degree]
      exact hfd
    have heq : G.neighborFinset f ∩ Iso = G.neighborFinset f :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    rw [← heq]
    exact Finset.inter_subset_right
  have hnadjff' : ¬G.Adj f f' := by
    intro hadj
    have hf'Iso : f' ∈ Iso := hNfIso ((G.mem_neighborFinset f f').mpr hadj)
    exact Finset.disjoint_left.mp hdisj hf'Hub hf'Iso
  -- === Twin facts: a twin's neighbourhood lies in `Hub`. ===
  have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
    intro t ht
    have hcard3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
    have hdt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]
      exact hisodeg3 t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    rw [← heq]
    exact Finset.inter_subset_right
  have hisoHub : ∀ t ∈ Iso, ∀ y : Fin 20, G.Adj t y → y ∉ Iso := by
    intro t ht y hadj hyIso
    have hyHub : y ∈ Hub := htwinHub t ht ((G.mem_neighborFinset t y).mpr hadj)
    exact Finset.disjoint_left.mp hdisj hyHub hyIso
  -- === `hK23` caps the anchor share at `2`. ===
  have hshareanch : (G.neighborFinset f ∩ G.neighborFinset f' ∩ Iso).card ≤ 2 := by
    by_contra hcon
    exact anchor_share_k23_1042_twenty G Iso hK23 hisoHub hisodeg3 f f' hfd hf'd hff'
      hnadjff' (by omega)
  -- === The iso-degree ledger `Σ_Hub isoDeg = 24`. ===
  have hisosum24 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 24 := by
    have h := hub_iso_sum_twenty G Hub Iso hiso3
    rw [hIso] at h
    omega
  have hisosplit : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 24 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]
    exact hisosum24
  have hD5sumpair : (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset f ∩ Iso).card + (G.neighborFinset f' ∩ Iso).card := by
    rw [hD5pair, Finset.sum_pair hff']
  have hf'cap : (G.neighborFinset f' ∩ Iso).card ≤ 5 := by
    calc (G.neighborFinset f' ∩ Iso).card ≤ (G.neighborFinset f').card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree f' := G.card_neighborFinset_eq_degree f'
      _ = 5 := hf'd
  -- === Union/intersection bookkeeping for the two anchor twin-sets. ===
  have hunioncard : ((G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso).card
        + (G.neighborFinset f ∩ G.neighborFinset f' ∩ Iso).card
      = (G.neighborFinset f ∩ Iso).card + (G.neighborFinset f' ∩ Iso).card := by
    have hkey := Finset.card_union_add_card_inter (G.neighborFinset f ∩ Iso)
      (G.neighborFinset f' ∩ Iso)
    have hU : (G.neighborFinset f ∩ Iso) ∪ (G.neighborFinset f' ∩ Iso)
        = (G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso := by
      ext y
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    have hI : (G.neighborFinset f ∩ Iso) ∩ (G.neighborFinset f' ∩ Iso)
        = G.neighborFinset f ∩ G.neighborFinset f' ∩ Iso := by
      ext y
      simp only [Finset.mem_inter]
      tauto
    rw [hU, hI] at hkey
    omega
  -- === The shared twin `c` (the unique twin of `h₂`, adjacent to `g`). ===
  obtain ⟨c, hceq⟩ := Finset.card_eq_one.mp hpoor
  have hcmem : c ∈ G.neighborFinset h₂ ∩ Iso := by
    rw [hceq]
    exact Finset.mem_singleton_self c
  have hcIso : c ∈ Iso := (Finset.mem_inter.mp hcmem).2
  have hch₂ : G.Adj h₂ c := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hcmem).1
  have hcNg : c ∈ G.neighborFinset g := by
    obtain ⟨y, hyeq⟩ := Finset.card_eq_one.mp hshared
    have hymem : y ∈ G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso := by
      rw [hyeq]
      exact Finset.mem_singleton_self y
    rw [Finset.mem_inter, Finset.mem_inter] at hymem
    have hyc : y = c := by
      have hy2 : y ∈ G.neighborFinset h₂ ∩ Iso :=
        Finset.mem_inter.mpr ⟨hymem.1.2, hymem.2⟩
      rw [hceq, Finset.mem_singleton] at hy2
      exact hy2
    rw [← hyc]
    exact hymem.1.1
  have hgc : G.Adj g c := (G.mem_neighborFinset _ _).mp hcNg
  have hgne2 : g ≠ h₂ := by
    intro he
    rw [he, hpoor] at hgiso
    omega
  -- === `c`'s three hub slots: `{g, h₂, w₃}`. ===
  have hcHub3 : (G.neighborFinset c ∩ Hub).card = 3 := hiso3 c hcIso
  have hgNc : g ∈ G.neighborFinset c ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hgc.symm, hg⟩
  have hh₂Nc : h₂ ∈ G.neighborFinset c ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hch₂.symm, hh₂⟩
  have hpairsub : ({g, h₂} : Finset (Fin 20)) ⊆ G.neighborFinset c ∩ Hub := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hgNc
    · exact hh₂Nc
  have hpaircard : ({g, h₂} : Finset (Fin 20)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hgne2]), Finset.card_singleton]
  have hw₃card : ((G.neighborFinset c ∩ Hub) \ {g, h₂}).card = 1 := by
    have hsd := Finset.card_sdiff_of_subset hpairsub
    rw [hcHub3, hpaircard] at hsd
    omega
  obtain ⟨w₃, hw₃eq⟩ := Finset.card_eq_one.mp hw₃card
  have hNcHub : G.neighborFinset c ∩ Hub = {g, h₂, w₃} := by
    have h1 : ({g, h₂} : Finset (Fin 20)) ∪ ((G.neighborFinset c ∩ Hub) \ {g, h₂})
        = G.neighborFinset c ∩ Hub := Finset.union_sdiff_of_subset hpairsub
    rw [hw₃eq] at h1
    rw [← h1]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- === The `M`-end `z` meets exactly two hubs: `{h₂, w}`. ===
  have hzf := zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
  obtain ⟨-, hzHub2, -⟩ := hzf z hzZ
  have hh₂Nz : h₂ ∈ G.neighborFinset z ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hz2, hh₂⟩
  have hwcard : ((G.neighborFinset z ∩ Hub) \ {h₂}).card = 1 := by
    have hsd := Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hh₂Nz)
    rw [hzHub2, Finset.card_singleton] at hsd
    omega
  obtain ⟨w, hweq⟩ := Finset.card_eq_one.mp hwcard
  have hwmem : w ∈ (G.neighborFinset z ∩ Hub) \ {h₂} := by
    rw [hweq]
    exact Finset.mem_singleton_self w
  have hNzHub : G.neighborFinset z ∩ Hub = {h₂, w} := by
    have h1 : ({h₂} : Finset (Fin 20)) ∪ ((G.neighborFinset z ∩ Hub) \ {h₂})
        = G.neighborFinset z ∩ Hub :=
      Finset.union_sdiff_of_subset (Finset.singleton_subset_iff.mpr hh₂Nz)
    rw [hweq] at h1
    rw [← h1]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  -- === `h₂` meets at most two hubs. ===
  have hh₂split := nbr_split_three_twenty G Hub Iso hdisj h₂
  have hzZmem : z ∈ G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso)) :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hz2.symm, hzZ⟩
  have hh₂HubLe : (G.neighborFinset h₂ ∩ Hub).card ≤ 2 := by
    have hzpos : 1 ≤ (G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
      Finset.card_pos.mpr ⟨z, hzZmem⟩
    rw [hd₂, hpoor] at hh₂split
    omega
  -- === The rich set `R`. ===
  set R : Finset (Fin 20) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsub : R ⊆ Hub := by
    rw [hRdef]
    exact Finset.filter_subset _ _
  have hRdeg4 : ∀ r ∈ R, G.degree r = 4 := by
    intro r hr
    rw [hRdef, Finset.mem_filter] at hr
    exact hr.2.1
  have hRiso2 : ∀ r ∈ R, 2 ≤ (G.neighborFinset r ∩ Iso).card := by
    intro r hr
    rw [hRdef, Finset.mem_filter] at hr
    exact hr.2.2
  have hgR : g ∈ R := by
    rw [hRdef, Finset.mem_filter]
    exact ⟨hg, hgd, by omega⟩
  have hh₂R : h₂ ∉ R := by
    rw [hRdef, Finset.mem_filter]
    rintro ⟨-, -, hcon⟩
    omega
  -- === Anchor-detection at `c` and the deg-5 twin cap. ===
  have hw₃aux : ∀ e : Fin 20, e ∈ Hub → G.degree e = 5 → c ∈ G.neighborFinset e →
      G.degree w₃ = 5 := by
    intro e heHub hed hce
    have heNc : e ∈ G.neighborFinset c ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp hce).symm, heHub⟩
    rw [hNcHub] at heNc
    simp only [Finset.mem_insert, Finset.mem_singleton] at heNc
    rcases heNc with he | he | he
    · rw [he] at hed
      omega
    · rw [he] at hed
      omega
    · rw [← he]
      exact hed
  have hk2aux : ∀ e : Fin 20, e ∈ Hub → G.degree e = 5 → ∀ t ∈ Iso,
      t ∈ G.neighborFinset e → (G.neighborFinset t ∩ R).card ≤ 2 := by
    intro e heHub hed t ht hte
    have heNt : e ∈ G.neighborFinset t ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp hte).symm, heHub⟩
    have hsub : G.neighborFinset t ∩ R ⊆ (G.neighborFinset t ∩ Hub).erase e := by
      intro y hy
      have hyR : y ∈ R := (Finset.mem_inter.mp hy).2
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).1, hRsub hyR⟩⟩
      intro he
      have hyd := hRdeg4 y hyR
      rw [he, hed] at hyd
      omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem heNt, hiso3 t ht] at hcard
    omega
  -- === Blocking: every non-`g` rich hub lies in `{w₃} ∪ (N h₂ ∩ Hub) ∪ {w}`. ===
  have hRcover : ∀ x ∈ R.erase g, x = w₃ ∨ x ∈ G.neighborFinset h₂ ∩ Hub ∨ x = w := by
    intro x hx
    have hxne : x ≠ g := Finset.ne_of_mem_erase hx
    have hxR : x ∈ R := Finset.mem_of_mem_erase hx
    have hxHub : x ∈ Hub := hRsub hxR
    have hxd : G.degree x = 4 := hRdeg4 x hxR
    have hxiso : 2 ≤ (G.neighborFinset x ∩ Iso).card := hRiso2 x hxR
    have hxh₂ : x ≠ h₂ := by
      intro he
      rw [he, hpoor] at hxiso
      omega
    rcases hblock x hxHub hxd hxiso with hb | hb | hb
    · left
      rw [← Finset.nonempty_iff_ne_empty] at hb
      obtain ⟨t, ht⟩ := hb
      rw [Finset.mem_inter, Finset.mem_inter] at ht
      have htc : t = c := by
        have ht2 : t ∈ G.neighborFinset h₂ ∩ Iso := Finset.mem_inter.mpr ⟨ht.1.2, ht.2⟩
        rw [hceq, Finset.mem_singleton] at ht2
        exact ht2
      have hxc : G.Adj x c := by
        rw [← htc]
        exact (G.mem_neighborFinset _ _).mp ht.1.1
      have hxNc : x ∈ G.neighborFinset c ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxc.symm, hxHub⟩
      rw [hNcHub] at hxNc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxNc
      rcases hxNc with he | he | he
      · exact absurd he hxne
      · exact absurd he hxh₂
      · exact he
    · right; left
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb.symm, hxHub⟩
    · right; right
      have hxNz : x ∈ G.neighborFinset z ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb.symm, hxHub⟩
      rw [hNzHub] at hxNz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxNz
      rcases hxNz with he | he
      · exact absurd he hxh₂
      · exact he
  -- === Rich/poor split of the deg-4 iso ledger. ===
  have hReqD4 : D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) = R := by
    rw [hRdef, hD4def, Finset.filter_filter]
  have hD4split := Finset.sum_filter_add_sum_filter_not D4
    (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    (fun h => (G.neighborFinset h ∩ Iso).card)
  rw [hReqD4] at hD4split
  have hD4cardsplit : (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = D4.card :=
    Finset.card_filter_add_card_filter_not _
  rw [hReqD4, hD4card] at hD4cardsplit
  have hpoorsum : (Hub.filter (fun h => G.degree h = 4
        ∧ (G.neighborFinset h ∩ Iso).card = 0)).card = 0 →
      (∑ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset h ∩ Iso).card)
        = (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
    intro hZ0
    rw [Finset.card_eq_zero] at hZ0
    have hone : ∀ x ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset x ∩ Iso).card = 1 := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxle : (G.neighborFinset x ∩ Iso).card ≤ 1 := by
        have hnot := hx.2
        omega
      have hxne0 : (G.neighborFinset x ∩ Iso).card ≠ 0 := by
        intro h0
        have hxZ0 : x ∈ Hub.filter (fun h => G.degree h = 4
            ∧ (G.neighborFinset h ∩ Iso).card = 0) := by
          have hxD4 := hx.1
          rw [hD4def, Finset.mem_filter] at hxD4
          rw [Finset.mem_filter]
          exact ⟨hxD4.1, hxD4.2, h0⟩
        rw [hZ0] at hxZ0
        exact absurd hxZ0 (Finset.notMem_empty x)
      omega
    rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one]
  -- === The exact square identity, the transpose, and the pointwise square split. ===
  have hsq := rich_square_identity_1042_twenty G Hub Iso R hisodeg3 hT hshare hno2hub
    hRsub hRdeg4 hRiso2
  have htrans : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
      = ∑ u ∈ R, (G.neighborFinset u ∩ Iso).card := cross_count_twenty G Iso R
  have hsqsum_of : (∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 2) →
      (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card)
        = (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
          + 2 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card := by
    intro hk2
    have hsqpt : ∀ t ∈ Iso,
        (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
          = (G.neighborFinset t ∩ R).card
            + 2 * (if (G.neighborFinset t ∩ R).card = 2 then 1 else 0) := by
      intro t ht
      have h2 := hk2 t ht
      rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1
          ∨ (G.neighborFinset t ∩ R).card = 2 by omega) with h | h | h <;>
        rw [h] <;> decide
    rw [Finset.sum_congr rfl hsqpt, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_boole, Nat.cast_id]
  -- === The degree-slot ledger over `R`. ===
  have hslot : ∀ x ∈ R,
      (G.neighborFinset x ∩ R).card + (if G.Adj x h₂ then 1 else 0)
          + (G.neighborFinset x ∩ Iso).card
          + (G.neighborFinset x ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 := by
    intro x hx
    have hsplit := nbr_split_three_twenty G Hub Iso hdisj x
    rw [hRdeg4 x hx] at hsplit
    have hhub : (G.neighborFinset x ∩ R).card + (if G.Adj x h₂ then 1 else 0)
        ≤ (G.neighborFinset x ∩ Hub).card := by
      by_cases hadj : G.Adj x h₂
      · rw [if_pos hadj]
        have hins : insert h₂ (G.neighborFinset x ∩ R) ⊆ G.neighborFinset x ∩ Hub := by
          intro y hy
          rw [Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh₂⟩
          · exact Finset.mem_inter.mpr
              ⟨(Finset.mem_inter.mp hy).1, hRsub (Finset.mem_inter.mp hy).2⟩
        have hcard := Finset.card_le_card hins
        rw [Finset.card_insert_of_notMem
          (fun hmem => hh₂R (Finset.mem_inter.mp hmem).2)] at hcard
        omega
      · rw [if_neg hadj, add_zero]
        exact Finset.card_le_card
          (Finset.inter_subset_inter (Finset.Subset.refl _) hRsub)
    omega
  have hslotsum : (∑ x ∈ R, (G.neighborFinset x ∩ R).card)
        + (R.filter (fun x => G.Adj x h₂)).card
        + (∑ x ∈ R, (G.neighborFinset x ∩ Iso).card)
        + (∑ x ∈ R, (G.neighborFinset x ∩ (Finset.univ \ (Hub ∪ Iso))).card)
      ≤ 4 * R.card := by
    have hsum := Finset.sum_le_sum hslot
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul, mul_comm R.card 4] at hsum
    have hfil : (∑ x ∈ R, (if G.Adj x h₂ then (1 : ℕ) else 0))
        = (R.filter (fun x => G.Adj x h₂)).card := by
      rw [Finset.sum_boole, Nat.cast_id]
    rw [hfil] at hsum
    exact hsum
  -- === The two payload cases. ===
  rcases hR45 with hR4 | hR5
  · -- === Case `|R| = 4`: both anchors saturated. ===
    rw [hR4] at hmaster
    have hD4ge : 14 ≤ ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by omega
    have hD4eq : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card) = 14 := by omega
    have hZ0card : (Hub.filter (fun h => G.degree h = 4
        ∧ (G.neighborFinset h ∩ Iso).card = 0)).card = 0 := by omega
    have hf'sat : (G.neighborFinset f' ∩ Iso).card = 5 := by omega
    have hSUM : (∑ h ∈ R, (G.neighborFinset h ∩ Iso).card) = 10 := by
      have hps := hpoorsum hZ0card
      omega
    -- Full coverage of `Iso` by the two anchors.
    have hcover : ∀ t ∈ Iso, t ∈ G.neighborFinset f ∪ G.neighborFinset f' := by
      have hUge : 8 ≤ ((G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso).card := by omega
      have hUeq : (G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso = Iso :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      intro t ht
      have htU : t ∈ (G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso := by
        rw [hUeq]
        exact ht
      exact (Finset.mem_inter.mp htU).1
    have hk2 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 2 := by
      intro t ht
      rcases Finset.mem_union.mp (hcover t ht) with h | h
      · exact hk2aux f hfHub hfd t ht h
      · exact hk2aux f' hf'Hub hf'd t ht h
    -- `w₃` is an anchor, so `N c ∩ R = {g}` and `k_c = 1`.
    have hw₃anchor : G.degree w₃ = 5 := by
      rcases Finset.mem_union.mp (hcover c hcIso) with h | h
      · exact hw₃aux f hfHub hfd h
      · exact hw₃aux f' hf'Hub hf'd h
    have hw₃notR : w₃ ∉ R := by
      intro hcon
      have hd4 := hRdeg4 w₃ hcon
      omega
    have hNcR : G.neighborFinset c ∩ R = {g} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        have hxR : x ∈ R := (Finset.mem_inter.mp hx).2
        have hxHub : x ∈ G.neighborFinset c ∩ Hub :=
          Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hRsub hxR⟩
        rw [hNcHub] at hxHub
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxHub
        rcases hxHub with he | he | he
        · exact he
        · exact absurd (he ▸ hxR) hh₂R
        · exact absurd (he ▸ hxR) hw₃notR
      · intro hx
        rw [hx]
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hgNc).1, hgR⟩
    have hkc1 : (G.neighborFinset c ∩ R).card = 1 := by
      rw [hNcR, Finset.card_singleton]
    -- The count chain: `Σk = 10`, `Σk² = Σk + 2n₂`, `2n₂ + 1 ≤ Σk` ⟹ `ERR ≥ 4`.
    have hktot : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card) = 10 := by
      rw [htrans]
      exact hSUM
    have hsqsum := hsqsum_of hk2
    have hcnot : c ∉ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2) := by
      rw [Finset.mem_filter]
      rintro ⟨-, hcon⟩
      omega
    have hsumlow : 2 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card + 1
        ≤ ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card := by
      have hsub : insert c (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2))
          ⊆ Iso := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact hcIso
        · exact (Finset.mem_filter.mp hx).1
      have hle := Finset.sum_le_sum_of_subset hsub
        (f := fun t => (G.neighborFinset t ∩ R).card)
      rw [Finset.sum_insert hcnot] at hle
      have hfil2 : (∑ t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2),
          (G.neighborFinset t ∩ R).card)
          = 2 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card := by
        have htwo : ∀ t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2),
            (G.neighborFinset t ∩ R).card = 2 := fun t ht => (Finset.mem_filter.mp ht).2
        rw [Finset.sum_congr rfl htwo, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hfil2, hkc1] at hle
      omega
    -- Blocking capacity: `w ∈ R`, at least two rich hubs on `h₂`, one on `z`.
    have herasecard : (R.erase g).card = 3 := by
      rw [Finset.card_erase_of_mem hgR, hR4]
    have hwR : w ∈ R := by
      by_contra hwnR
      have hsub : R.erase g ⊆ G.neighborFinset h₂ ∩ Hub := by
        intro x hx
        rcases hRcover x hx with h | h | h
        · exact absurd (h ▸ Finset.mem_of_mem_erase hx) hw₃notR
        · exact h
        · exact absurd (h ▸ Finset.mem_of_mem_erase hx) hwnR
      have hcard := Finset.card_le_card hsub
      rw [herasecard] at hcard
      omega
    have hq2 : 2 ≤ (R.filter (fun y => G.Adj y h₂)).card := by
      have hqsub : (R.erase g) \ {w} ⊆ R.filter (fun y => G.Adj y h₂) := by
        intro x hx
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
        rcases hRcover x hx.1 with h | h | h
        · exact absurd (h ▸ Finset.mem_of_mem_erase hx.1) hw₃notR
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_of_mem_erase hx.1,
            ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h).1).symm⟩
        · exact absurd h hx.2
      have hcard := Finset.card_le_card hqsub
      have hsd := Finset.card_sdiff_add_card (R.erase g) {w}
      have hun : (R.erase g).card ≤ ((R.erase g) ∪ {w}).card :=
        Finset.card_le_card Finset.subset_union_left
      rw [Finset.card_singleton] at hsd
      omega
    have hzsum : 1 ≤ ∑ x ∈ R, (G.neighborFinset x ∩ (Finset.univ \ (Hub ∪ Iso))).card := by
      have hzw : z ∈ G.neighborFinset w ∩ (Finset.univ \ (Hub ∪ Iso)) := by
        refine Finset.mem_inter.mpr ⟨?_, hzZ⟩
        rw [G.mem_neighborFinset]
        exact ((G.mem_neighborFinset _ _).mp
          (Finset.mem_inter.mp (Finset.mem_sdiff.mp hwmem).1).1).symm
      calc (1 : ℕ) ≤ (G.neighborFinset w ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
            Finset.card_pos.mpr ⟨z, hzw⟩
        _ ≤ ∑ x ∈ R, (G.neighborFinset x ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
            Finset.single_le_sum
              (f := fun x => (G.neighborFinset x ∩ (Finset.univ \ (Hub ∪ Iso))).card)
              (fun x _ => Nat.zero_le _) hwR
    rw [hR4] at hsq hslotsum
    omega
  · -- === Case `|R| = 5`: `w₃ ∈ R`, `c` anchor-uncovered. ===
    rw [hR5] at hmaster
    have herasecard : (R.erase g).card = 4 := by
      rw [Finset.card_erase_of_mem hgR, hR5]
    have hw₃R : w₃ ∈ R := by
      by_contra hw₃nR
      have hsub : R.erase g ⊆ insert w (G.neighborFinset h₂ ∩ Hub) := by
        intro x hx
        rcases hRcover x hx with h | h | h
        · exact absurd (h ▸ Finset.mem_of_mem_erase hx) hw₃nR
        · exact Finset.mem_insert_of_mem h
        · rw [h]
          exact Finset.mem_insert_self _ _
      have hcard := Finset.card_le_card hsub
      have hins := Finset.card_insert_le w (G.neighborFinset h₂ ∩ Hub)
      rw [herasecard] at hcard
      omega
    have hw₃d4 : G.degree w₃ = 4 := hRdeg4 w₃ hw₃R
    have hcuncov : c ∉ G.neighborFinset f ∪ G.neighborFinset f' := by
      intro hc
      have h5 : G.degree w₃ = 5 := by
        rcases Finset.mem_union.mp hc with h | h
        · exact hw₃aux f hfHub hfd h
        · exact hw₃aux f' hf'Hub hf'd h
      omega
    have hUsub : (G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso ⊆ Iso.erase c := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_erase]
      exact ⟨fun he => hcuncov (he ▸ hx.1), hx.2⟩
    have hUle : ((G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso).card ≤ 7 := by
      have hle := Finset.card_le_card hUsub
      have hec := Finset.card_erase_of_mem hcIso
      omega
    have hf'iso4 : (G.neighborFinset f' ∩ Iso).card ≤ 4 := by omega
    have hD4eq : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card) = 15 := by omega
    have hZ0card : (Hub.filter (fun h => G.degree h = 4
        ∧ (G.neighborFinset h ∩ Iso).card = 0)).card = 0 := by omega
    have hs2 : (G.neighborFinset f ∩ G.neighborFinset f' ∩ Iso).card = 2 := by omega
    have hUeq7 : ((G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso).card = 7 := by omega
    have hSUM : (∑ h ∈ R, (G.neighborFinset h ∩ Iso).card) = 12 := by
      have hps := hpoorsum hZ0card
      omega
    -- Coverage off `c`.
    have hUeqset : (G.neighborFinset f ∪ G.neighborFinset f') ∩ Iso = Iso.erase c := by
      apply Finset.eq_of_subset_of_card_le hUsub
      have hec := Finset.card_erase_of_mem hcIso
      omega
    have hcover5 : ∀ t ∈ Iso, t ≠ c → t ∈ G.neighborFinset f ∪ G.neighborFinset f' := by
      intro t ht htc
      have hte : t ∈ Iso.erase c := Finset.mem_erase.mpr ⟨htc, ht⟩
      rw [← hUeqset] at hte
      exact (Finset.mem_inter.mp hte).1
    have hkcle : (G.neighborFinset c ∩ R).card ≤ 2 := by
      have hsub : G.neighborFinset c ∩ R ⊆ (G.neighborFinset c ∩ Hub).erase h₂ := by
        intro y hy
        have hyR : y ∈ R := (Finset.mem_inter.mp hy).2
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).1, hRsub hyR⟩⟩
        intro he
        exact hh₂R (he ▸ hyR)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hh₂Nc, hcHub3] at hcard
      omega
    have hk2 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 2 := by
      intro t ht
      by_cases htc : t = c
      · rw [htc]
        exact hkcle
      · rcases Finset.mem_union.mp (hcover5 t ht htc) with h | h
        · exact hk2aux f hfHub hfd t ht h
        · exact hk2aux f' hf'Hub hf'd t ht h
    -- Double-anchor twins carry `k ≤ 1`, so `n₂ ≤ 6`.
    have hA2k1 : ∀ t ∈ G.neighborFinset f ∩ G.neighborFinset f' ∩ Iso,
        (G.neighborFinset t ∩ R).card ≤ 1 := by
      intro t ht
      rw [Finset.mem_inter, Finset.mem_inter] at ht
      have htIso : t ∈ Iso := ht.2
      have hfNt : f ∈ G.neighborFinset t ∩ Hub := Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ht.1.1).symm, hfHub⟩
      have hf'Nt : f' ∈ G.neighborFinset t ∩ Hub := Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ht.1.2).symm, hf'Hub⟩
      have hsub : G.neighborFinset t ∩ R
          ⊆ ((G.neighborFinset t ∩ Hub).erase f).erase f' := by
        intro y hy
        have hyR : y ∈ R := (Finset.mem_inter.mp hy).2
        have hyd := hRdeg4 y hyR
        rw [Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).1, hRsub hyR⟩⟩
        · intro he
          rw [he, hf'd] at hyd
          omega
        · intro he
          rw [he, hfd] at hyd
          omega
      have hcard := Finset.card_le_card hsub
      have hf'in : f' ∈ (G.neighborFinset t ∩ Hub).erase f :=
        Finset.mem_erase.mpr ⟨hff'.symm, hf'Nt⟩
      rw [Finset.card_erase_of_mem hf'in, Finset.card_erase_of_mem hfNt,
        hiso3 t htIso] at hcard
      omega
    have hn₂le : (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card ≤ 6 := by
      have hn₂sub : Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)
          ⊆ Iso \ (G.neighborFinset f ∩ G.neighborFinset f' ∩ Iso) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [Finset.mem_sdiff]
        refine ⟨ht.1, fun hcon => ?_⟩
        have hle1 := hA2k1 t hcon
        omega
      have hcard := Finset.card_le_card hn₂sub
      have hsd := Finset.card_sdiff_of_subset (Finset.inter_subset_right :
        G.neighborFinset f ∩ G.neighborFinset f' ∩ Iso ⊆ Iso)
      omega
    -- Slot count: at least two rich hubs adjacent to `h₂`.
    have hq2 : 2 ≤ (R.filter (fun y => G.Adj y h₂)).card := by
      have hqsub : (R.erase g) \ {w₃, w} ⊆ R.filter (fun y => G.Adj y h₂) := by
        intro x hx
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx
        obtain ⟨hmem, hnot⟩ := hx
        rw [not_or] at hnot
        rcases hRcover x hmem with h | h | h
        · exact absurd h hnot.1
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_of_mem_erase hmem,
            ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h).1).symm⟩
        · exact absurd h hnot.2
      have hcard := Finset.card_le_card hqsub
      have hsd := Finset.card_sdiff_add_card (R.erase g) {w₃, w}
      have hun : (R.erase g).card ≤ ((R.erase g) ∪ {w₃, w}).card :=
        Finset.card_le_card Finset.subset_union_left
      have hpc : ({w₃, w} : Finset (Fin 20)).card ≤ 2 := by
        have hle := Finset.card_insert_le w₃ ({w} : Finset (Fin 20))
        rw [Finset.card_singleton] at hle
        omega
      omega
    -- Assemble: `ERR = 20 − 2n₂ ≥ 8` against the slot cap `ERR ≤ 6`.
    have hktot : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card) = 12 := by
      rw [htrans]
      exact hSUM
    have hsqsum := hsqsum_of hk2
    rw [hR5] at hsq hslotsum
    omega

end N20

end ACMax
