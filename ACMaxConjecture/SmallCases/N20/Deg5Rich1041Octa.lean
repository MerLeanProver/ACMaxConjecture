import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5ZSlots
import ACMaxConjecture.SmallCases.N20.Deg5RichCap
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041OctaKill
import ACMaxConjecture.SmallCases.N20.Deg5SameZ
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N20.R5ResidHelpers
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Ledger
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041K23
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Deficit

/-! # The rigid-tie octahedron dispatcher for the (11,7,45) case-(iii) corner (`n = 20`)

The `n = 20` deg-`5` analog of the proven `n = 19` octahedron kill
(`rigid_tie_kill_1041_nineteen`, `TwinCert19Deg5Rich1041Octa`).  In the rigid
`|R| = 5` tie where every rich deg-`4` hub is blocked (adjacent to the shared
twin `c`, to `h₂`, or to `z`), the ledger profile
(`ledger_profile_1041_twenty`) pins the unique deg-`5` hub `f` at isoDeg
`∈ {4, 5}`.  The isoDeg-`5` branch is contradictory: the octahedron/`K₂,₂,₂`
covering design forces a forbidden `K₂,₃` (`hK23`) or `Iso`-two-hub
(`hno2hub`).  Unlike `n = 19`, the isoDeg-`4` deficit branch is LIVE (the
tenth degree-`4` hub leaves one unit of ledger slack): there the rich packer
(`deficit_kill_1041_twenty`) assembles a cut configuration, so the dispatcher
concludes the standard 4-way config disjunction rather than `False`. -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The rigid-tie dispatcher.**  If every rich degree-`4` hub is blocked and
the `(11,7,45)` rigid tie holds (`|R| = 5`), the octahedron world either is
contradictory (isoDeg `f = 5`) or yields a cut configuration (isoDeg `f = 4`). -/
theorem rigid_tie_kill_1041_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
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
    (hR5eq : (Hub.filter (fun h => G.degree h = 4 ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  -- === Step 0: the rigid tie in its `≥ 5` form, for the two kill branches. ===
  have hR5ge : 5 ≤ (Hub.filter (fun h => G.degree h = 4 ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card)).card := hR5eq.ge
  -- === Step 1: the pinned ledger.  `f` deg-5 isoDeg ∈ {4,5}, `x` deg-4 isoDeg-≥3. ===
  obtain ⟨f, x, hfHub, hfd, hprof, hxHub, hxd, hxiso3, hxf⟩ :=
    ledger_profile_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg hdeg5
      hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2
      hpoor hshared hblock
  rcases hprof with hfiso5 | ⟨hf4, hpoor1, hn34⟩
  · -- === The isoDeg `f = 5` profile: the octahedron kill chain, a contradiction. ===
    -- Step 2: `Iso` is independent (each `Iso` vertex meets only hubs).
    have hisoHub : ∀ t ∈ Iso, ∀ w : Fin 20, G.Adj t w → w ∉ Iso := by
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
    -- Step 3: `f` meets no hub (isoDeg 5 = deg 5), so `¬G.Adj x f`.
    have hfnohub : (G.neighborFinset f ∩ Hub).card = 0 := by
      have h := nbr_split_three_twenty G Hub Iso hdisj f
      rw [hfd, hfiso5] at h; omega
    have hnadj : ¬G.Adj x f := by
      intro hadj
      have hxInter : x ∈ G.neighborFinset f ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset f x).mpr hadj.symm, hxHub⟩
      rw [Finset.card_eq_zero] at hfnohub
      rw [hfnohub] at hxInter
      exact absurd hxInter (Finset.notMem_empty x)
    -- Step 4: dispatch on the shared-twin count of `x` with `f`.
    by_cases hsh : 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card
    · -- High share: a forbidden `K₂,₃`.
      exact (highshare_k23_1041_twenty G Iso hK23 hisoHub hisodeg3 x f hxd hfd hnadj
        hsh).elim
    · -- Low share (`≤ 2`): the covering-design octahedron (dedicated sub-node).
      exact (octahedron_share2_kill_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3
        hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂
        hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock hR5ge f x hfHub hfd hfiso5 hxHub hxd hxiso3
        hxf hnadj hsh).elim
  · -- === The isoDeg `f = 4` deficit profile: the LIVE world, a cut configuration. ===
    exact deficit_kill_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg
      hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2
      hgz hg2 hpoor hshared hblock hR5ge f hfHub hfd hf4 hpoor1 hn34

end N20

end ACMax
