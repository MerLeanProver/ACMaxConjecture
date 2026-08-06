import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub

/-!
# `n = 20` P₃-cherry residual: the `x`–`z` `TwoHubConfig` kill and its selector

Two leaf helpers for the `n = 20` P₃-cherry residual dispatch.

* `two_hub_xz_cherry_kill_twenty` wraps the shared assembler `two_hub_cherry_pair_twenty` with the
  cherry-endpoint members `(a, b) = (x, b)`, `(c, d) = (z, d)`: given two non-adjacent degree-`4`
  hubs `h₁, h₂`, each carrying a degree-`3` cherry leaf plus a degree-`3` partner, with the full
  cross non-adjacency pattern, it produces a `TwoHubConfig`.
* `xz_deg4_nonadj_pair_twenty` is the pure-`Finset` matching-existence leaf: from two disjoint
  `2`-element hub sets `X, Z ⊆ Dc` whose members each have at most one `Dc`-neighbour and at most one
  degree-`5` vertex in total, it extracts a degree-`4` hub in each side that are non-adjacent.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The `x`–`z` P₃-cherry `TwoHubConfig` kill.**  Two non-adjacent degree-`4` hubs `h₁, h₂`, each
carrying a degree-`3` cherry endpoint (`x` on `h₁`, `z` on `h₂`) and a degree-`3` partner (`b` on
`h₁`, `d` on `h₂`), with the complete cross non-adjacency pattern, assemble into a `TwoHubConfig`.
This is `two_hub_cherry_pair_twenty` with `(a, b) = (x, b)`, `(c, d) = (z, d)`. -/
theorem two_hub_xz_cherry_kill_twenty (G : SimpleGraph (Fin 20)) (x z h₁ h₂ b d : Fin 20)
    (hxz : ¬G.Adj x z) (hxdeg : G.degree x = 3) (hzdeg : G.degree z = 3)
    (hd1 : G.degree h₁ = 4) (hd2 : G.degree h₂ = 4)
    (hbdeg : G.degree b = 3) (hddeg : G.degree d = 3)
    (hxh1 : G.Adj x h₁) (hbh1 : G.Adj b h₁) (hzh2 : G.Adj z h₂) (hdh2 : G.Adj d h₂)
    (hn12 : ¬G.Adj h₁ h₂) (hnxh2 : ¬G.Adj x h₂) (hnzh1 : ¬G.Adj z h₁)
    (hnbh2 : ¬G.Adj b h₂) (hndh1 : ¬G.Adj d h₁) (hnxd : ¬G.Adj x d)
    (hnbz : ¬G.Adj b z) (hnbd : ¬G.Adj b d)
    (hxb : x ≠ b) (hzd : z ≠ d) :
    TwoHubConfig G :=
  two_hub_cherry_pair_twenty G h₁ h₂ x b z d hd1 hd2 hxdeg hbdeg hzdeg hddeg
    hxh1 hbh1 hzh2 hdh2 hn12
    (fun h => hnzh1 h.symm) (fun h => hndh1 h.symm)
    hnxh2 hnbh2 hxz hnxd hnbz hnbd
    hxb hzd
    (by rintro rfl; exact hnzh1 hxh1) (by rintro rfl; exact hndh1 hxh1)
    (by rintro rfl; exact hnzh1 hbh1) (by rintro rfl; exact hndh1 hbh1)

/-- **The `x`–`z` non-adjacent degree-`4` selector (matching leaf).**  Two disjoint `2`-element hub
sets `X, Z ⊆ Dc`, each member meeting `Dc` in at most one neighbour and having degree `4` or `5`,
with at most one degree-`5` vertex across `X ∪ Z`, admit a degree-`4` hub `h₁ ∈ X` and a degree-`4`
hub `h₂ ∈ Z` that are non-adjacent.  With `≤ 1` degree-`5` vertex, one whole side is all-degree-`4`;
its member forced non-adjacent to a degree-`4` hub on the other side (each hub having `≤ 1`
`Dc`-neighbour, hence `≤ 1` neighbour in the opposite `2`-set). -/
theorem xz_deg4_nonadj_pair_twenty (G : SimpleGraph (Fin 20)) (Dc X Z : Finset (Fin 20))
    (hX : X ⊆ Dc) (hZ : Z ⊆ Dc) (hXcard : X.card = 2) (hZcard : Z.card = 2)
    (hdisj : Disjoint X Z)
    (hint : ∀ h ∈ X ∪ Z, (G.neighborFinset h ∩ Dc).card ≤ 1)
    (hdeg : ∀ h ∈ X ∪ Z, G.degree h = 4 ∨ G.degree h = 5)
    (hfive : ((X ∪ Z).filter (fun h => G.degree h = 5)).card ≤ 1) :
    ∃ h₁ ∈ X, ∃ h₂ ∈ Z, G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ ¬G.Adj h₁ h₂ := by
  classical
  -- A hub with ≤ 1 `Dc`-neighbour meets a `2`-set of `Dc` in ≤ 1 vertex, so misses one.
  have key : ∀ (h : Fin 20) (Q : Finset (Fin 20)), Q ⊆ Dc → Q.card = 2 →
      (G.neighborFinset h ∩ Dc).card ≤ 1 → ∃ q ∈ Q, ¬G.Adj h q := by
    intro h Q hQsub hQcard hh
    by_contra hcon
    push Not at hcon
    have hsub : Q ⊆ G.neighborFinset h ∩ Dc := by
      intro q hq
      rw [Finset.mem_inter]
      exact ⟨(G.mem_neighborFinset h q).mpr (hcon q hq), hQsub hq⟩
    have hle := Finset.card_le_card hsub
    rw [hQcard] at hle
    omega
  -- Any `2`-subset of `X ∪ Z` contains a degree-`4` vertex (at most one degree-`5` overall).
  have side4 : ∀ P : Finset (Fin 20), P ⊆ X ∪ Z → P.card = 2 → ∃ p ∈ P, G.degree p = 4 := by
    intro P hPsub hPcard
    by_contra hcon
    push Not at hcon
    have hPfilter : P ⊆ (X ∪ Z).filter (fun h => G.degree h = 5) := by
      intro p hp
      rw [Finset.mem_filter]
      exact ⟨hPsub hp, (hdeg p (hPsub hp)).resolve_left (hcon p hp)⟩
    have hle := Finset.card_le_card hPfilter
    rw [hPcard] at hle
    omega
  have hX4 : ∃ x ∈ X, G.degree x = 4 :=
    side4 X (fun a ha => Finset.mem_union.mpr (Or.inl ha)) hXcard
  have hZ4 : ∃ z ∈ Z, G.degree z = 4 :=
    side4 Z (fun a ha => Finset.mem_union.mpr (Or.inr ha)) hZcard
  -- One whole side is all-degree-`4`, else two degree-`5` vertices contradict `hfive`.
  have hside : (∀ h ∈ X, G.degree h = 4) ∨ (∀ h ∈ Z, G.degree h = 4) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨hx, hxX, hxdeg⟩, ⟨hz, hzZ, hzdeg⟩⟩ := hcon
    have hx5 : G.degree hx = 5 :=
      (hdeg hx (Finset.mem_union.mpr (Or.inl hxX))).resolve_left hxdeg
    have hz5 : G.degree hz = 5 :=
      (hdeg hz (Finset.mem_union.mpr (Or.inr hzZ))).resolve_left hzdeg
    have hxf : hx ∈ (X ∪ Z).filter (fun h => G.degree h = 5) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_union.mpr (Or.inl hxX), hx5⟩
    have hzf : hz ∈ (X ∪ Z).filter (fun h => G.degree h = 5) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_union.mpr (Or.inr hzZ), hz5⟩
    have hne : hx ≠ hz := by
      intro h; subst h
      exact (Finset.disjoint_left.mp hdisj hxX) hzZ
    have h1lt : 1 < ((X ∪ Z).filter (fun h => G.degree h = 5)).card :=
      Finset.one_lt_card.mpr ⟨hx, hxf, hz, hzf, hne⟩
    omega
  rcases hside with hXall | hZall
  · obtain ⟨z₀, hz₀Z, hz₀deg⟩ := hZ4
    obtain ⟨h₁, hh₁X, hnadj⟩ := key z₀ X hX hXcard (hint z₀ (Finset.mem_union.mpr (Or.inr hz₀Z)))
    exact ⟨h₁, hh₁X, z₀, hz₀Z, hXall h₁ hh₁X, hz₀deg, fun h => hnadj h.symm⟩
  · obtain ⟨x₀, hx₀X, hx₀deg⟩ := hX4
    obtain ⟨h₂, hh₂Z, hnadj⟩ := key x₀ Z hZ hZcard (hint x₀ (Finset.mem_union.mpr (Or.inl hx₀X)))
    exact ⟨x₀, hx₀X, h₂, hh₂Z, hx₀deg, hZall h₂ hh₂Z, hnadj⟩

end N20

end ACMax
