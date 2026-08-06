import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core

/-!
# The high-share K₂,₃ kill for the (10,8,42) octahedron corner (`n = 20`)

The clean sub-case of the rigid-tie kill: a degree-`4` hub `x` and the
degree-`5` hub `f`, non-adjacent, sharing `≥ 3` `Iso` twins, form a forbidden
`K₂,₃` of degree sum `4 + 5 + 3·3 = 18 ≤ 19` (`hK23`).  The three shared twins
are pairwise non-adjacent because `Iso` vertices meet only hubs.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The high-share K₂,₃ kill.**  A degree-`4` hub `x` and the degree-`5` hub
`f`, non-adjacent, sharing `≥ 3` `Iso` twins, are contradictory. -/
theorem highshare_k23_1041_twenty (G : SimpleGraph (Fin 20)) (Iso : Finset (Fin 20))
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hisoHub : ∀ t ∈ Iso, ∀ w : Fin 20, G.Adj t w → w ∉ Iso)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (x f : Fin 20) (hxd : G.degree x = 4) (hfd : G.degree f = 5)
    (hnadj : ¬G.Adj x f)
    (hshare3 : 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card) :
    False := by
  classical
  -- Extract a 3-element subset of the common twins.
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
  -- The three twins are pairwise non-adjacent (Iso meets only hubs).
  have hncd : ¬G.Adj c d := fun h => hisoHub c hcIso d h hdIso
  have hnce : ¬G.Adj c e := fun h => hisoHub c hcIso e h heIso
  have hnde : ¬G.Adj d e := fun h => hisoHub d hdIso e h heIso
  -- distinctness: degrees separate `x` (4), `f` (5), and `c,d,e` (3).
  have hc3 : G.degree c = 3 := hisodeg3 c hcIso
  have hd3 : G.degree d = 3 := hisodeg3 d hdIso
  have he3 : G.degree e = 3 := hisodeg3 e heIso
  have hxf : x ≠ f := by intro h; rw [h, hfd] at hxd; omega
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
    hncd, hnce, hnde, by rw [hxd, hfd, hc3, hd3, he3]; omega⟩

end N20

end ACMax
