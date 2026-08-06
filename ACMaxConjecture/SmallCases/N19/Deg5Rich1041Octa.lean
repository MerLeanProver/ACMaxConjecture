import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5ZSlots
import ACMaxConjecture.SmallCases.N19.Deg5RichCap
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041OctaKill
import ACMaxConjecture.SmallCases.N19.Deg5SameZ
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N19.R5ResidHelpers
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Ledger
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041K23

/-! # The rigid-tie octahedron kill for the (10,7,41) case-(iii) corner (`n = 19`)

The `n = 19` deg-`5` analog of the proven `n = 18` octahedron kill
(`no_share0_forces_octahedron_eighteen` + `octahedron_poor_cert_eighteen`,
`TwinCert18RichEdgeExtract`).  In the rigid `|A| = 5` tie where every rich
deg-`4` hub is blocked (adjacent to the shared twin `c`, to `h₂`, or to `z`),
the octahedron/`K₂,₂,₂` covering-design forces a forbidden `K₂,₃` (`hK23`) or
`Iso`-two-hub (`hno2hub`) — a contradiction.  The deg-`5` hub `f` (isoDeg `5`)
sharpens the trace bound relative to `n = 18`. -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The rigid-tie kill.**  If every rich degree-`4` hub is blocked, the
`(10,7,41)` rigid octahedron is contradictory. -/
theorem rigid_tie_kill_1041_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
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
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
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
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z) :
    False := by
  classical
  -- === Step 1: the pinned ledger.  `f` deg-5 isoDeg-5, `x` deg-4 isoDeg-≥3. ===
  obtain ⟨f, x, hfHub, hfd, hfiso5, hxHub, hxd, hxiso3, hxf⟩ :=
    ledger_profile_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg hdeg5
      hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2
      hpoor hshared hblock
  -- === Step 2: `Iso` is independent (each `Iso` vertex meets only hubs). ===
  have hisoHub : ∀ t ∈ Iso, ∀ w : Fin 19, G.Adj t w → w ∉ Iso := by
    intro t ht w hadj hwIso
    have h3 := hiso3 t ht
    have hcard : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard, h3])
    have hwHub : w ∈ Hub := by
      have hwN : w ∈ G.neighborFinset t ∩ Hub := by
        rw [heq]; exact (G.mem_neighborFinset t w).mpr hadj
      exact (Finset.mem_inter.mp hwN).2
    exact Finset.disjoint_left.mp hdisj hwHub hwIso
  -- === Step 3: `f` meets no hub (isoDeg 5 = deg 5), so `¬G.Adj x f`. ===
  have hfnohub : (G.neighborFinset f ∩ Hub).card = 0 := by
    have h := nbr_split_three_nineteen G Hub Iso hdisj f
    rw [hfd, hfiso5] at h; omega
  have hnadj : ¬G.Adj x f := by
    intro hadj
    have hxInter : x ∈ G.neighborFinset f ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset f x).mpr hadj.symm, hxHub⟩
    rw [Finset.card_eq_zero] at hfnohub
    rw [hfnohub] at hxInter
    exact absurd hxInter (Finset.notMem_empty x)
  -- === Step 4: dispatch on the shared-twin count of `x` with `f`. ===
  by_cases hsh : 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card
  · -- High share: a forbidden `K₂,₃`.
    exact highshare_k23_1041_nineteen G Iso hK23 hisoHub hisodeg3 x f hxd hfd hnadj hsh
  · -- Low share (`≤ 2`): the covering-design octahedron (dedicated sub-node).
    exact octahedron_share2_kill_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak
      hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2
      hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub hxd hxiso3 hxf hnadj hsh

end N19

end ACMax
