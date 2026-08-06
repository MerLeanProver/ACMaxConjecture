import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5RichCap
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Blocker
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041OctaPoorCounts
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041BothPoorBudget
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041BothPoorWorldI
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041BothPoorWorldII

/-! # CASE C, both-poor regime: `z'` meets two poor hubs (`n = 20`)

The `z'`-meets-poor / share-0 residual where BOTH of `z'`'s two hubs `{p,q}`
are poor (`isoDeg ≤ 1`, hence `∈ P`).  At `n = 20` the poor set has FIVE
members and the budget (`octahedron_both_poor_budget_1041_twenty`) is
disjunctive.  World (i) (`Σ_R = 11`, all five poor hubs at isoDeg `1`,
`e_RR ≤ 3`) dies by `octahedron_both_poor_world_i_1041_twenty`; World (ii)
(`Σ_R = 12`, one isoDeg-`0` poor hub, `e_RR ≤ 2` plus the attachment
dichotomy) dies by `octahedron_both_poor_world_ii_1041_twenty`. -/

namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **CASE C, both-poor regime.** -/
theorem octahedron_both_poor_force_share2_1041_twenty (G : SimpleGraph (Fin 20))
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
    (hz2 : G.Adj z h₂) (hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
    (f x : Fin 20) (hfHub : f ∈ Hub) (hfd : G.degree f = 5)
    (hfiso5 : (G.neighborFinset f ∩ Iso).card = 5)
    (hxHub : x ∈ Hub) (hxd : G.degree x = 4)
    (hxiso3 : 3 ≤ (G.neighborFinset x ∩ Iso).card) (hxf : x ≠ f)
    (hnadj : ¬G.Adj x f)
    (hsh : ¬ 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card)
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
    (hzz' : G.Adj z z') (hz'deg3 : G.degree z' = 3)
    (hz'iso0 : (G.neighborFinset z' ∩ Iso).card = 0)
    (hNz'eq : G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 20)))
    (hp : p ∈ Hub) (hq : q ∈ Hub) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hpq : p ≠ q) (hz'p : G.Adj z' p) (hz'q : G.Adj z' q)
    (hnpq : ¬G.Adj p q)
    (hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0)
    (hppoor : (G.neighborFinset p ∩ Iso).card ≤ 1)
    (hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1)
    (hph₂ : p ≠ h₂) (hpr_z : p ≠ r_z) (hqh₂ : q ≠ h₂) (hqr_z : q ≠ r_z) :
    False := by
  classical
  -- === Structure extraction (keeping `hstruct` for the downstream calls). ===
  have hstruct' := hstruct
  obtain ⟨c, r_t, r_z, a, b, hRfilter, hRcard5, hcIso, hgc, hh₂c, hr_tc, hNc, hNz, hNh₂,
    hr_zz, hah₂, hbh₂, hr_tHub, hr_td, hr_zHub, hr_zd, haHub, had, hbHub, hbd⟩ := hstruct'
  -- === `|R| ≥ 5` from the rigid five-element rich filter. ===
  have hR5ge : 5 ≤ (Hub.filter
      (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
    rw [hRfilter]; omega
  -- === Structural `p ≠ r_z`, `q ≠ r_z` (poor hubs are not rich). ===
  have hr_zR : r_z ∈ Hub.filter
      (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hRfilter]; simp
  have hpr_z' : p ≠ r_z := by
    rintro rfl
    have h2 := (Finset.mem_filter.mp hr_zR).2.2
    omega
  have hqr_z' : q ≠ r_z := by
    rintro rfl
    have h2 := (Finset.mem_filter.mp hr_zR).2.2
    omega
  -- === The two-world budget disjunction. ===
  rcases octahedron_both_poor_budget_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3
      hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂
      hzZ hz2 hgz hg2 hpoor hshared hblock hR5ge f x hfHub hfd hfiso5 hxHub hxd hxiso3 hxf
      hnadj hsh hstruct z' p q hz'Z hzz' hz'deg3 hz'iso0 hNz'eq hp hq hdp hdq hpq hz'p hz'q
      hnpq hshare0 hppoor hqpoor hph₂ hpr_z hqh₂ hqr_z with
    ⟨hP5, hRiso11, hall1, hw, hzdeg, heRR⟩ | ⟨hP5, hRiso12, hh₀, hzdeg, heRR, hdich⟩
  · -- === World (i): `isoDeg g = 3` (Σ_R = 11 over five ≥-2 entries), then the kill. ===
    have hgS : g ∈ ({g, r_t, r_z, a, b} : Finset (Fin 20)) := by simp
    have hRiso11' : (∑ r ∈ ({g, r_t, r_z, a, b} : Finset (Fin 20)),
        (G.neighborFinset r ∩ Iso).card) = 11 := by
      rw [← hRfilter]; exact hRiso11
    have hsplit : (G.neighborFinset g ∩ Iso).card
        + (∑ r ∈ (({g, r_t, r_z, a, b} : Finset (Fin 20)).erase g),
          (G.neighborFinset r ∩ Iso).card) = 11 := by
      rw [← hRiso11']
      exact Finset.add_sum_erase _ (fun r => (G.neighborFinset r ∩ Iso).card) hgS
    have hcardErase : (({g, r_t, r_z, a, b} : Finset (Fin 20)).erase g).card = 4 := by
      rw [Finset.card_erase_of_mem hgS, hRcard5]
    have hrest8 : 8 ≤ ∑ r ∈ (({g, r_t, r_z, a, b} : Finset (Fin 20)).erase g),
        (G.neighborFinset r ∩ Iso).card := by
      have hle := Finset.card_nsmul_le_sum
        (({g, r_t, r_z, a, b} : Finset (Fin 20)).erase g)
        (fun r => (G.neighborFinset r ∩ Iso).card) 2 (fun r hr => by
          have hrR : r ∈ Hub.filter
              (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
            rw [hRfilter]; exact Finset.mem_of_mem_erase hr
          exact (Finset.mem_filter.mp hrR).2.2)
      rw [hcardErase, smul_eq_mul] at hle
      omega
    have hg3 : (G.neighborFinset g ∩ Iso).card = 3 := by omega
    exact octahedron_both_poor_world_i_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3
      hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂
      hzZ hz2 hgz hg2 hpoor f hfHub hfd hfiso5 c r_t r_z a b hRfilter hRcard5 hcIso hgc hh₂c
      hr_tc hNc hNz hNh₂ hr_zz hah₂ hbh₂ hr_tHub hr_td hr_zHub hr_zd haHub had hbHub hbd
      z' p q hz'Z hzz' hz'deg3 hz'iso0 hNz'eq hp hq hdp hdq hpq hz'p hz'q hnpq hshare0
      hppoor hqpoor hph₂ hpr_z' hqh₂ hqr_z' hP5 hall1 hRiso11 hw hzdeg heRR hg3
  · -- === World (ii): the compiled world-(ii) kill. ===
    exact octahedron_both_poor_world_ii_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3
      hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂
      hzZ hz2 hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub hxd hxiso3 hxf hnadj hsh
      hstruct z' p q hz'Z hzz' hz'deg3 hz'iso0 hNz'eq hp hq hdp hdq hpq hz'p hz'q hnpq hshare0
      hppoor hqpoor hph₂ hqh₂ hP5 hRiso12 hh₀ hzdeg heRR hdich

end N20

end ACMax
