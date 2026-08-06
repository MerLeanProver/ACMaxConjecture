import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.OctahedronForce
import ACMaxConjecture.SmallCases.N20.OctahedronPoorForce2

/-!
# Excluding the residual rich-internal mass `mRR = 10` (`n = 20`, `(12, 6, 48)`)

`octahedron_mass_reduce_twenty` pins the rich-internal ordered mass `mRR ∈ {6, 10}` for the clean
no-two-hub `|Hub| = 12` octahedron.  The `mRR = 6` branch carries the four-high-twins input
`hhigh4 = (n₃ ≥ 4)` consumed by the octahedron poor-layer force; the `mRR = 10` branch is the
residual `n₃ = 3` profile, with twin rich-degree multiset `(n₃, n₂, n₁, n₀) = (3, 1, 1, 1)`.

The documented circularity (cf. `octahedron_struct_residual_twenty`) is that branch (b) of
`octahedron_poor_force_b_or_c_twenty` extracts its good `K₂,₃` only through
`octahedron_low_twin_poor_twenty`, which itself demands `hhigh4 = n₃ ≥ 4` — exactly what `mRR = 10`
fails to supply.  This file **breaks the circle** by reading the certificate directly off the
`n₃ = 3` trace structure, with no appeal to `hhigh4` or the low-twin lemma:

* The profile forces `n₀ = 1`: there is one twin `t₀` meeting **no** rich hub, hence (by `hiso3`)
  meeting exactly three poor hubs `Q = N(t₀) ∩ P`, `|Q| = 3`.
* `octahedron_poor_counts_twenty` gives the poor-internal ordered mass
  `∑_{g∈P} |N g ∩ P| = mRR + 6 = 16`, i.e. **eight** undirected poor edges among the six poor hubs.
* If two vertices of `Q` are adjacent, `{p₁, t₀, p₂}` is a good triangle of degree sum
  `4 + 3 + 4 = 11` (`hT`).  Otherwise `Q` is independent, so with `A = ∑_{w∈P\Q} |N w ∩ Q|` the
  mass splits as `16 = A + ∑_{w∈P\Q} |N w ∩ P|`; each poor hub has at most three neighbours in `P`
  (its fourth slot is its twin), so `∑_{w∈P\Q} |N w ∩ P| ≤ 9` and `A ≥ 7 > 2·3`.  Hence one of the
  three poor hubs outside `Q`, say `w`, is adjacent to all of `Q`, giving the good `K₂,₃`
  `{t₀, w | Q}` of degree sum `3 + 4 + 4·3 = 19` (`hK23`).

Either way the no-good-certificate hypotheses are contradicted, so `mRR ≠ 10`.  (The theorem keeps
its legacy `n = 19` name `octahedron_mass_ne_eight_twenty`; at `n = 20` the excluded residual mass
is `10`.)  The lemma is fully axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The residual rich-internal mass `mRR = 10` is impossible (LEAF, axiom-clean).**  For the clean
no-two-hub `|Hub| = 12` octahedron (`R = {h : 2 ≤ |N h ∩ Iso|}`, `|R| = 6`, every hub meets a twin),
the rich-internal ordered edge mass `∑_{r∈R} |N r ∩ R|` is not `10`.  Breaks the `n₃ = 3`
circularity by extracting a good triangle or `K₂,₃` directly from the zero-rich twin `t₀`.  (Legacy
`n = 19` name: there the residual mass was `8`.) -/
theorem octahedron_mass_ne_eight_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso R : Finset (Fin 20))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3)
    (hcut : ¬ ZPoorCutConfig G) :
    (∑ r ∈ R, (G.neighborFinset r ∩ R).card) ≠ 10 := by
  classical
  intro hm10
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- Trace saturation and the rich iso-incidence value `= 12`.
  obtain ⟨hsat, h12⟩ := octahedron_trace_saturate_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj hHub
    hIso hisodeg3 hshare hno2hub hT hnozero
  rw [hRcard] at hsat h12
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 12 := by
    rw [cross_count_twenty G Iso R]; omega
  -- Twin rich-degree profile counts.
  set n0 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card with hn0
  set n1 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card with hn1
  set n2 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card with hn2
  set n3 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card with hn3
  have hI : n0 + n1 + n2 + n3 = 6 := by
    rw [hn0, hn1, hn2, hn3, ← hIso, Finset.card_eq_sum_ones Iso]
    simp only [Finset.card_filter]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := htle3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  have hII : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = n1 + 2 * n2 + 3 * n3 := by
    rw [hn1, hn2, hn3]
    simp only [Finset.card_filter, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := htle3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  have hIII : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card = 2 * n2 + 6 * n3 := by
    rw [hn2, hn3]
    simp only [Finset.offDiag_card, Finset.card_filter, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := htle3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  rw [hcross] at hII
  rw [hIII] at hsat
  -- The `(3, 1, 1, 1)` profile: `n₀ = 1`, so there is a twin meeting no rich hub.
  obtain ⟨t₀, ht₀mem⟩ := Finset.card_pos.mp (show 0 < n0 by omega)
  rw [Finset.mem_filter] at ht₀mem
  obtain ⟨ht₀Iso, ht₀R0⟩ := ht₀mem
  -- Poor-internal ordered mass `∑_{g∈P} |N g ∩ P| = mRR + 6 = 16`.
  set P : Finset (Fin 20) := Hub \ R with hPdef
  have hunion : R ∪ P = Hub := by rw [hPdef]; exact Finset.union_sdiff_of_subset hRsub
  have hdisjRP : Disjoint R P := by rw [hPdef]; exact Finset.disjoint_sdiff
  obtain ⟨_, _, _, hPP, hpoor3⟩ := (octahedron_poor_counts_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj
    hHub hIso hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard).resolve_right hcut
  have hPP16 : ∑ g ∈ P, (G.neighborFinset g ∩ P).card = 16 := by
    rw [hPdef, hPP, hm10]
  have hPcard : P.card = 6 := by
    rw [hPdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub, hHub, hRcard]
  -- `t₀` meets no rich hub: `N t₀ ∩ R = ∅`, so its three hub-neighbours are all poor.
  have ht₀Hub : (G.neighborFinset t₀ ∩ Hub).card = 3 := hiso3 t₀ ht₀Iso
  set Q : Finset (Fin 20) := G.neighborFinset t₀ ∩ P with hQdef
  have hQsubP : Q ⊆ P := by rw [hQdef]; exact Finset.inter_subset_right
  have hQcard : Q.card = 3 := by
    have hsplit : (G.neighborFinset t₀ ∩ R).card + (G.neighborFinset t₀ ∩ P).card
        = (G.neighborFinset t₀ ∩ Hub).card := by
      rw [← Finset.card_union_of_disjoint
            (Finset.disjoint_left.mpr (fun x hx hx2 =>
              Finset.disjoint_left.mp hdisjRP (Finset.mem_of_mem_inter_right hx)
                (Finset.mem_of_mem_inter_right hx2))),
        ← Finset.inter_union_distrib_left, hunion]
    rw [ht₀R0, ht₀Hub] at hsplit
    rw [hQdef]; omega
  -- Membership facts for `Q`.
  have hQadj : ∀ q ∈ Q, G.Adj t₀ q := by
    intro q hq; rw [hQdef, Finset.mem_inter, G.mem_neighborFinset] at hq; exact hq.1
  have hQHub : ∀ q ∈ Q, q ∈ Hub := by
    intro q hq; have := hQsubP hq; rw [hPdef, Finset.mem_sdiff] at this; exact this.1
  have hQdeg4 : ∀ q ∈ Q, G.degree q = 4 := fun q hq => hdeg4 q (hQHub q hq)
  have ht₀notHub : t₀ ∉ Hub := fun h => Finset.disjoint_left.mp hdisj h ht₀Iso
  have ht₀neQ : ∀ q ∈ Q, t₀ ≠ q := by
    intro q hq he; apply ht₀notHub; rw [he]; exact hQHub q hq
  obtain ⟨q1, q2, q3, hq12, hq13, hq23, hQeq⟩ := Finset.card_eq_three.mp hQcard
  have hq1Q : q1 ∈ Q := by rw [hQeq]; exact Finset.mem_insert_self _ _
  have hq2Q : q2 ∈ Q := by rw [hQeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hq3Q : q3 ∈ Q := by
    rw [hQeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- **Case 1.** Two vertices of `Q` are adjacent: a good triangle of degree sum `11`.
  by_cases hQedge : ∃ p1 ∈ Q, ∃ p2 ∈ Q, p1 ≠ p2 ∧ G.Adj p1 p2
  · obtain ⟨p1, hp1, p2, hp2, hp1p2, hadj⟩ := hQedge
    apply hT
    refine ⟨p1, t₀, p2, ?_, ht₀neQ p2 hp2, hp1p2, (hQadj p1 hp1).symm, hQadj p2 hp2, hadj, ?_⟩
    · intro he; exact ht₀neQ p1 hp1 he.symm
    · have : G.degree p1 + G.degree t₀ + G.degree p2 = 11 := by
        rw [hQdeg4 p1 hp1, hisodeg3 t₀ ht₀Iso, hQdeg4 p2 hp2]
      omega
  · -- **Case 2.** `Q` is independent.  Double-count the poor-internal mass to force a `K₂,₃`.
    have hQindep : ∀ p1 ∈ Q, ∀ p2 ∈ Q, p1 ≠ p2 → ¬G.Adj p1 p2 := by
      intro p1 hp1 p2 hp2 hne hadj; exact hQedge ⟨p1, hp1, p2, hp2, hne, hadj⟩
    -- For `g ∈ Q`, `N g ∩ Q = ∅`.
    have hQinterEmpty : ∀ g ∈ Q, (G.neighborFinset g ∩ Q).card = 0 := by
      intro g hg
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact hQindep g hg x hx.2 (G.ne_of_adj hx.1) hx.1
    set Pq : Finset (Fin 20) := P \ Q with hPqdef
    have hPqcard : Pq.card = 3 := by
      rw [hPqdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hQsubP, hPcard, hQcard]
    have hPQunion : Q ∪ Pq = P := by rw [hPqdef]; exact Finset.union_sdiff_of_subset hQsubP
    have hPQdisj : Disjoint Q Pq := by rw [hPqdef]; exact Finset.disjoint_sdiff
    -- Pointwise: `|N g ∩ P| = |N g ∩ Q| + |N g ∩ Pq|`.
    have hsplitP : ∀ g : Fin 20, (G.neighborFinset g ∩ P).card
        = (G.neighborFinset g ∩ Q).card + (G.neighborFinset g ∩ Pq).card := by
      intro g
      rw [← Finset.card_union_of_disjoint
            (Finset.disjoint_left.mpr (fun x hx hx2 =>
              Finset.disjoint_left.mp hPQdisj (Finset.mem_of_mem_inter_right hx)
                (Finset.mem_of_mem_inter_right hx2))),
        ← Finset.inter_union_distrib_left, hPQunion]
    -- `A + B = 16` where `A = ∑_{P} |N · ∩ Q|`, `B = ∑_{P} |N · ∩ Pq|`.
    have hAB : (∑ g ∈ P, (G.neighborFinset g ∩ Q).card)
        + (∑ g ∈ P, (G.neighborFinset g ∩ Pq).card) = 16 := by
      rw [← Finset.sum_add_distrib, ← hPP16]
      exact Finset.sum_congr rfl (fun g _ => (hsplitP g).symm)
    -- `A = ∑_{Pq} |N · ∩ Q|`: the `Q`-part of `A` vanishes.
    have hAeq : ∑ g ∈ P, (G.neighborFinset g ∩ Q).card
        = ∑ g ∈ Pq, (G.neighborFinset g ∩ Q).card := by
      rw [← hPQunion, Finset.sum_union hPQdisj, Finset.sum_eq_zero (fun g hg => hQinterEmpty g hg),
        zero_add]
    -- `B = ∑_{Pq} |N · ∩ P|` (cross count `P ↔ Pq`).
    have hBeq : ∑ g ∈ P, (G.neighborFinset g ∩ Pq).card
        = ∑ w ∈ Pq, (G.neighborFinset w ∩ P).card := cross_count_twenty G P Pq
    -- Per-poor cap: `|N w ∩ P| ≤ 3` (the fourth slot is the poor hub's twin).
    have hwle3 : ∀ w ∈ Pq, (G.neighborFinset w ∩ P).card ≤ 3 := by
      intro w hw
      have hw' := hw
      rw [hPqdef] at hw'
      have hwP := (Finset.mem_sdiff.mp hw').1
      rw [hPdef] at hwP ⊢
      have h3 := hpoor3 w hwP
      omega
    have hB9 : ∑ w ∈ Pq, (G.neighborFinset w ∩ P).card ≤ 9 := by
      calc ∑ w ∈ Pq, (G.neighborFinset w ∩ P).card ≤ ∑ _w ∈ Pq, 3 := Finset.sum_le_sum hwle3
        _ = 9 := by rw [Finset.sum_const, hPqcard, smul_eq_mul]
    -- Hence `A ≥ 7`.
    have hA7 : 7 ≤ ∑ w ∈ Pq, (G.neighborFinset w ∩ Q).card := by
      rw [hAeq, hBeq] at hAB; omega
    -- Pigeonhole over `Pq = {w₁, w₂, w₃}`: some `w` is adjacent to all of `Q`.
    obtain ⟨w1, w2, w3, hw12, hw13, hw23, hPqeq⟩ := Finset.card_eq_three.mp hPqcard
    have hw1Pq : w1 ∈ Pq := by rw [hPqeq]; exact Finset.mem_insert_self _ _
    have hw2Pq : w2 ∈ Pq := by
      rw [hPqeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hw3Pq : w3 ∈ Pq := by
      rw [hPqeq]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hsum3 : ∑ w ∈ Pq, (G.neighborFinset w ∩ Q).card = (G.neighborFinset w1 ∩ Q).card
        + ((G.neighborFinset w2 ∩ Q).card + (G.neighborFinset w3 ∩ Q).card) := by
      rw [hPqeq, Finset.sum_insert (by simp [hw12, hw13]),
        Finset.sum_insert (by simp [hw23]), Finset.sum_singleton]
    have hw1le : (G.neighborFinset w1 ∩ Q).card ≤ 3 := by
      rw [← hQcard]; exact Finset.card_le_card Finset.inter_subset_right
    have hw2le : (G.neighborFinset w2 ∩ Q).card ≤ 3 := by
      rw [← hQcard]; exact Finset.card_le_card Finset.inter_subset_right
    have hw3le : (G.neighborFinset w3 ∩ Q).card ≤ 3 := by
      rw [← hQcard]; exact Finset.card_le_card Finset.inter_subset_right
    have hwfull : ∃ w ∈ Pq, (G.neighborFinset w ∩ Q).card = 3 := by
      by_cases h1 : (G.neighborFinset w1 ∩ Q).card = 3
      · exact ⟨w1, hw1Pq, h1⟩
      by_cases h2 : (G.neighborFinset w2 ∩ Q).card = 3
      · exact ⟨w2, hw2Pq, h2⟩
      exact ⟨w3, hw3Pq, by omega⟩
    obtain ⟨w, hwPq, hwfull3⟩ := hwfull
    have hwadj : ∀ q ∈ Q, G.Adj w q := by
      have heqQ : G.neighborFinset w ∩ Q = Q :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (le_of_eq (by rw [hQcard, hwfull3]))
      intro q hq
      have hmem : q ∈ G.neighborFinset w ∩ Q := by rw [heqQ]; exact hq
      rw [Finset.mem_inter, G.mem_neighborFinset] at hmem; exact hmem.1
    have hwP : w ∈ P := by
      have := hwPq; rw [hPqdef, Finset.mem_sdiff] at this; exact this.1
    have hwnotQ : w ∉ Q := by
      have := hwPq; rw [hPqdef, Finset.mem_sdiff] at this; exact this.2
    have hwHub : w ∈ Hub := by rw [hPdef, Finset.mem_sdiff] at hwP; exact hwP.1
    -- `t₀ ≁ w`: `w ∈ P` but `w ∉ Q = N t₀ ∩ P`.
    have ht₀w : ¬G.Adj t₀ w := by
      intro hadj
      exact hwnotQ (by rw [hQdef, Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj, hwP⟩)
    have ht₀new : t₀ ≠ w := by intro he; apply ht₀notHub; rw [he]; exact hwHub
    have hwneq : ∀ q ∈ Q, w ≠ q := by intro q hq he; apply hwnotQ; rw [he]; exact hq
    have hcard5 : ({t₀, w, q1, q2, q3} : Finset (Fin 20)).card = 5 := by
      have hwq1 : w ≠ q1 := hwneq q1 hq1Q
      have hwq2 : w ≠ q2 := hwneq q2 hq2Q
      have hwq3 : w ≠ q3 := hwneq q3 hq3Q
      have ht1 : t₀ ≠ q1 := ht₀neQ q1 hq1Q
      have ht2 : t₀ ≠ q2 := ht₀neQ q2 hq2Q
      have ht3 : t₀ ≠ q3 := ht₀neQ q3 hq3Q
      rw [Finset.card_insert_of_notMem (by simp [ht₀new, ht1, ht2, ht3]),
          Finset.card_insert_of_notMem (by simp [hwq1, hwq2, hwq3]),
          Finset.card_insert_of_notMem (by simp [hq12, hq13]),
          Finset.card_insert_of_notMem (by simp [hq23]), Finset.card_singleton]
    refine absurd ⟨t₀, w, q1, q2, q3, hcard5, hQadj q1 hq1Q, hQadj q2 hq2Q, hQadj q3 hq3Q,
      hwadj q1 hq1Q, hwadj q2 hq2Q, hwadj q3 hq3Q, ht₀w,
      hQindep q1 hq1Q q2 hq2Q hq12, hQindep q1 hq1Q q3 hq3Q hq13, hQindep q2 hq2Q q3 hq3Q hq23, ?_⟩
      hK23
    have : G.degree t₀ + G.degree w + G.degree q1 + G.degree q2 + G.degree q3 = 19 := by
      rw [hisodeg3 t₀ ht₀Iso, hdeg4 w hwHub, hQdeg4 q1 hq1Q, hQdeg4 q2 hq2Q, hQdeg4 q3 hq3Q]
    omega

end N20

end ACMax
