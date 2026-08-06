import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct
import ACMaxConjecture.SmallCases.N19.RichCount
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.ZPoorDispatch

/-!
# The rigid `Z`-distribution for the `n = 19` no-two-hub partition

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (11, 6)` profile, the two `M`-edge
endpoints form the set `Z = univ \ (Hub ∪ Iso)` (`|Z| = 2`).  Each hub's degree splits as
`|N ∩ Hub| + |N ∩ Iso| + |N ∩ Z| = 4`; summing over the eleven hubs and using `N3`
(`∑|N ∩ Hub| = 22`) and `∑|N ∩ Iso| = 18` gives `∑_{Hub}|N ∩ Z| = 4` — the **same** `Z`-hub mass
as `n = 18` (`44 − 22 − 18 = 4`), since `|Iso| = 6` is unchanged.

The headline `zdeg_split_nineteen` pins how those four `Z`-incidences distribute across the
rich/poor partition: at least two land on rich hubs (`2 ≤ ∑_R Zdeg`) and at most two on poor hubs
(`∑_P Zdeg ≤ 2`).  This feeds both the rich-internal edge bound `E(R, R) ≤ 4` and the
poor-internal edge mass.

This is the **mechanical port** of the `n = 18` `TwinCert18RichZdeg` to `|Hub| = 11`.  The only
profile changes are `Fin 18 → 19`, `Hub.card 10 → 11`, `∑deg 40 → 44`, and the hub-hub mass
`18 → 22`; the thresholds (good-tri `≤ 11`, good-`C₄` `≤ 14`, good-`K₂₃` `≤ 19`) and the `Z`-profile
(`(2, 0, deg 3)`, four hub-incidences) are identical.

## Dependence on the deep `z`-meets-2-poor regime

The `n = 18` proof of `z_two_poor_hubs_false` delegates its hard residual (two poor hubs that are
adjacent or share no `M`-isolated twin) to `z_meets_two_poor_forces_two_hub_eighteen`, the global
two-hub extraction in `TwinCert18ZPoorDispatch` — built on the whole `rich_count` / `rich_six` /
`rich_seven` ZPoor cluster.  That cluster is **not yet ported** to `n = 19` (the `|Hub| = 11`
analog has 5 poor hubs vs 4, 468 incidence-level survivors).  So here the residual is **threaded as
a hypothesis** `hztwopoor` (the precise statement of `z_meets_two_poor_forces_two_hub_nineteen`),
which keeps every lemma in this file fully axiom-clean.  The local good-`C₄` sub-case (non-adjacent
poor hubs sharing a twin) is proved here directly.  Once the ZPoor cluster is ported,
`hztwopoor` is discharged by `z_meets_two_poor_forces_two_hub_nineteen` and these lemmas become
hypothesis-free.

The single foundation lemma `no_z_two_rich_hubs_nineteen` does **not** touch the deep regime and is
ported axiom-clean with no extra hypothesis.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- The threaded residual delegation: the global two-hub extraction for an `M`-edge endpoint that
meets two *poor* hubs in the residual regime (adjacent, or sharing no `M`-isolated twin).  This is
exactly the conclusion of `z_meets_two_poor_forces_two_hub_nineteen`, deferred to the not-yet-ported
`z`-meets-2-poor / ZPoor cluster. -/
abbrev ZMeetsTwoPoorResidual (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19)) : Prop :=
  ∀ (z : Fin 19), z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) →
    ∀ (hg1 hg2 : Fin 19), hg1 ≠ hg2 →
      hg1 ∈ G.neighborFinset z ∩ Hub → hg2 ∈ G.neighborFinset z ∩ Hub →
      (G.neighborFinset hg1 ∩ Iso).card ≤ 1 → (G.neighborFinset hg2 ∩ Iso).card ≤ 1 →
      (G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0) →
      ZPoorCutConfig G

/-- **Two poor hubs through one `M`-edge endpoint are impossible (GLOBAL CORE).**  An `M`-edge
endpoint `z` meets exactly two hubs (`z_two_hub_nbrs`).  If both were *poor* (iso-degree `≤ 1`), the
no-good-`C₄`/`K₂₃` and no-good-two-hub structure would be violated: when the two poor hubs share an
`M`-isolated twin and are non-adjacent one reads off a good `C₄` (`t–poor–z–poor`, `∑deg = 14`); the
residual (distinct twins / adjacent poor hubs) needs a global two-hub extraction among the rich hubs.

The local good-`C₄` sub-case (non-adjacent poor hubs sharing a twin) is proved here directly via
`hC4`; the distinct-twin / adjacent-poor residual is delegated to the threaded hypothesis
`hztwopoor` (`= z_meets_two_poor_forces_two_hub_nineteen`, the not-yet-ported global extraction). -/
theorem z_two_poor_hubs_false_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (z : Fin 19) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hg1 : Fin 19) (hg2 : Fin 19) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1) :
    ZPoorCutConfig G := by
  classical
  have hztwopoor : ZMeetsTwoPoorResidual G Hub Iso :=
    z_meets_two_poor_forces_two_hub_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
      hdsum hleak hshare hno2hub hC4 hK23 hT
  obtain ⟨hziso0, _, hzdeg3⟩ := z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum
    hdeg3 hisodeg3 hleak z hz
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hzg1 : G.Adj z hg1 := (G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1
  have hzg2 : G.Adj z hg2 := (G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1
  have hznotHub : z ∉ Hub := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
  have hznotIso : z ∉ Iso := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.2
  have hzg1ne : z ≠ hg1 := fun he => hznotHub (he ▸ hg1Hub)
  have hzg2ne : z ≠ hg2 := fun he => hznotHub (he ▸ hg2Hub)
  by_cases hadj : G.Adj hg1 hg2
  · -- Adjacent poor hubs: residual, delegated to the global two-hub extraction.
    exact hztwopoor z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor (Or.inl hadj)
  · by_cases hsh : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0
    · -- Non-adjacent poor hubs sharing no twin: residual, delegated globally.
      exact hztwopoor z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor (Or.inr hsh)
    · -- Non-adjacent poor hubs sharing a twin `t`: the good `C₄`  `t–hg1–z–hg2`.
      have hsh1 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 1 := by
        have hle := hshare hg1 hg1Hub (hdeg4 hg1 hg1Hub) hg2 hg2Hub (hdeg4 hg2 hg2Hub) hg1ne hadj
        omega
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hsh1
      have htmem : t ∈ G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso := by
        rw [ht]; exact Finset.mem_singleton_self _
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at htmem
      obtain ⟨⟨htg1, htg2⟩, htIso⟩ := htmem
      have hziso0' : G.neighborFinset z ∩ Iso = ∅ := Finset.card_eq_zero.mp hziso0
      have htznadj : ¬G.Adj z t := by
        intro he
        have : t ∈ G.neighborFinset z ∩ Iso :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z t).mpr he, htIso⟩
        rw [hziso0'] at this; exact Finset.notMem_empty t this
      have htnotHub : t ∉ Hub := fun he => Finset.disjoint_left.mp hdisj he htIso
      have htg1ne : t ≠ hg1 := fun he => htnotHub (he ▸ hg1Hub)
      have htg2ne : t ≠ hg2 := fun he => htnotHub (he ▸ hg2Hub)
      have htzne : t ≠ z := fun he => hznotIso (he ▸ htIso)
      refine (hC4 ⟨t, hg1, z, hg2, ?_, htg1.symm, hzg1.symm, hzg2, htg2, fun h => htznadj h.symm,
        hadj, ?_⟩).elim
      · rw [Finset.card_eq_four]
        exact ⟨t, hg1, z, hg2, htg1ne, htzne, htg2ne, hzg1ne.symm, hg1ne, hzg2ne, rfl⟩
      · rw [hisodeg3 t htIso, hdeg4 hg1 hg1Hub, hzdeg3, hdeg4 hg2 hg2Hub]

/-- **Each `M`-edge endpoint meets at least one rich hub.**  An endpoint `z` of the `M`-edge has
degree `3`: one `M`-edge to its partner plus exactly two hubs (it meets no `M`-isolated twin, and at
most one other `Z`-vertex).  Were both of those two hubs *poor* (iso-degree `≤ 1`), the no-good-`C₄`
and no-good-two-hub structure would be violated (`z_two_poor_hubs_false`).  Hence `z` meets a rich
hub. -/
theorem each_z_meets_rich_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    ∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)),
      1 ≤ (G.neighborFinset z ∩ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ∨
        ZPoorCutConfig G := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  intro z hz
  obtain ⟨_, hhub2, _⟩ := z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3
    hisodeg3 hleak z hz
  by_cases h1 : 1 ≤ (G.neighborFinset z ∩ R).card
  · exact Or.inl h1
  refine Or.inr ?_
  have hR0 : (G.neighborFinset z ∩ R).card = 0 := by omega
  -- Extract the two distinct hubs `z` meets.
  obtain ⟨g1, g2, hg1ne, hseteq⟩ := Finset.card_eq_two.mp hhub2
  have hg1mem : g1 ∈ G.neighborFinset z ∩ Hub := by rw [hseteq]; exact Finset.mem_insert_self _ _
  have hg2mem : g2 ∈ G.neighborFinset z ∩ Hub := by
    rw [hseteq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  -- Both hubs are poor: a rich one would put `z` adjacent to `R`, contradicting `hR0`.
  have hpoor : ∀ g ∈ G.neighborFinset z ∩ Hub, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg
    by_contra hge
    push Not at hge
    have hgR : g ∈ G.neighborFinset z ∩ R := by
      rw [Finset.mem_inter] at hg ⊢
      exact ⟨hg.1, by rw [hRdef, Finset.mem_filter]; exact ⟨hg.2, hge⟩⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hR0
    exact hR0 g hgR
  exact z_two_poor_hubs_false_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT z hz g1 g2 hg1ne hg1mem hg2mem
    (hpoor g1 hg1mem) (hpoor g2 hg2mem)

/-- **The rigid `Z`-distribution (`2 ≤ ∑_R Zdeg`, `∑_P Zdeg ≤ 2`).**  The two `M`-edge endpoints
`Z = univ \ (Hub ∪ Iso)` carry exactly four hub-incidences (`zdeg_sum_four`); each endpoint meets a
rich hub (`each_z_meets_rich`), so at least two of the four land on rich hubs, leaving at most two on
poor hubs.  Here `R = {h : 2 ≤ |N(h) ∩ Iso|}` and `P` is its complement in `Hub`. -/
theorem zdeg_split_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    (2 ≤ ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card ∧
    ∑ g ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 2) ∨ ZPoorCutConfig G := by
  classical
  set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 19) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  by_cases hcut : ZPoorCutConfig G
  · exact Or.inr hcut
  refine Or.inl ?_
  have hZcard : Z.card = 2 := z_card_two_nineteen Hub Iso hdisj hHub hIso
  have hsum4 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Z).card = 4 :=
    zdeg_sum_four_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  have hsplit : ∑ r ∈ R, (G.neighborFinset r ∩ Z).card
      + ∑ g ∈ P, (G.neighborFinset g ∩ Z).card = 4 := by
    rw [hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum4
  have hrichge : 2 ≤ ∑ r ∈ R, (G.neighborFinset r ∩ Z).card := by
    have hcross : ∑ r ∈ R, (G.neighborFinset r ∩ Z).card
        = ∑ z ∈ Z, (G.neighborFinset z ∩ R).card := cross_count_nineteen G R Z
    rw [hcross]
    have hez : ∀ z ∈ Z, 1 ≤ (G.neighborFinset z ∩ R).card := by
      intro z hz
      rcases each_z_meets_rich_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3 hdsum
        hleak hshare hno2hub hC4 hK23 hT z hz with h | hc
      · exact h
      · exact absurd hc hcut
    calc (2 : ℕ) = ∑ _z ∈ Z, 1 := by rw [Finset.sum_const, hZcard, smul_eq_mul, mul_one]
      _ ≤ ∑ z ∈ Z, (G.neighborFinset z ∩ R).card := Finset.sum_le_sum hez
  exact ⟨hrichge, by omega⟩

/-- **No `M`-edge endpoint meets two rich hubs (the sharp `≤ 11` fix).**  An endpoint `z` of the
`M`-edge meets exactly two hubs (`z_two_hub_nbrs`).  Were *both* rich (iso-degree `≥ 2`), there are
two cases.  If the two rich hubs `g₁, g₂` are adjacent, the triangle `{z, g₁, g₂}` has degree sum
`3 + 4 + 4 = 11 ≤ 11`, a good triangle excluded by `hT` (threshold `11`, the `n = 19` value).  If
they are non-adjacent, they share exactly one `M`-isolated twin `t` (`rich_nonadj_share_eq_one`);
then `t–g₁–z–g₂` is an induced good `C₄` of degree sum `3 + 4 + 3 + 4 = 14 ≤ 14` excluded by `hC4`
(`z` meets no twin, so `t ≁ z`).  Hence `z` meets at most one rich hub.

This foundation lemma does **not** touch the deep `z`-meets-2-poor regime — it is fully axiom-clean
with no threaded hypothesis. -/
theorem no_z_two_rich_hubs_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    ∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)),
      (G.neighborFinset z ∩ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 1 := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  intro z hz
  obtain ⟨hziso0, hzhub2, hzdeg3⟩ := z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum
    hdeg3 hisodeg3 hleak z hz
  by_contra hgt
  push Not at hgt
  -- `z` meets two distinct rich hubs `g₁, g₂`; both lie in the two-element set `N(z) ∩ Hub`.
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hsubHub : (G.neighborFinset z ∩ R) ⊆ (G.neighborFinset z ∩ Hub) :=
    Finset.inter_subset_inter (Finset.Subset.refl _) hRsubHub
  obtain ⟨g₁, hg1, g₂, hg2, hg12⟩ := Finset.one_lt_card.mp hgt
  have hg1Hub : g₁ ∈ Hub := hRsubHub (Finset.mem_inter.mp hg1).2
  have hg2Hub : g₂ ∈ Hub := hRsubHub (Finset.mem_inter.mp hg2).2
  have hg1rich : 2 ≤ (G.neighborFinset g₁ ∩ Iso).card := by
    have := (Finset.mem_filter.mp (Finset.mem_inter.mp hg1).2).2; exact this
  have hg2rich : 2 ≤ (G.neighborFinset g₂ ∩ Iso).card := by
    have := (Finset.mem_filter.mp (Finset.mem_inter.mp hg2).2).2; exact this
  have hzg1 : G.Adj z g₁ := (G.mem_neighborFinset z g₁).mp (Finset.mem_inter.mp hg1).1
  have hzg2 : G.Adj z g₂ := (G.mem_neighborFinset z g₂).mp (Finset.mem_inter.mp hg2).1
  have hznotHub : z ∉ Hub := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
  have hzg1ne : z ≠ g₁ := fun he => hznotHub (he ▸ hg1Hub)
  have hzg2ne : z ≠ g₂ := fun he => hznotHub (he ▸ hg2Hub)
  by_cases hadj : G.Adj g₁ g₂
  · -- Adjacent rich hubs: the triangle `{z, g₁, g₂}` has degree sum `11`.
    refine hT ⟨z, g₁, g₂, hzg1ne, hg12, hzg2ne, hzg1, hadj, hzg2, ?_⟩
    rw [hzdeg3, hdeg4 g₁ hg1Hub, hdeg4 g₂ hg2Hub]
  · -- Non-adjacent rich hubs share exactly one twin `t`; `t–g₁–z–g₂` is a good `C₄`.
    have hsh : (G.neighborFinset g₁ ∩ G.neighborFinset g₂ ∩ Iso).card = 1 :=
      rich_nonadj_share_eq_one_nineteen G Hub Iso hshare hno2hub g₁ g₂ hg1Hub hg2Hub
        (hdeg4 g₁ hg1Hub) (hdeg4 g₂ hg2Hub) hg12 hadj hg1rich hg2rich
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hsh
    have htmem : t ∈ G.neighborFinset g₁ ∩ G.neighborFinset g₂ ∩ Iso := by
      rw [ht]; exact Finset.mem_singleton_self _
    rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at htmem
    obtain ⟨⟨htg1, htg2⟩, htIso⟩ := htmem
    -- `z` meets no twin, so `t ≁ z`.
    have hziso0' : G.neighborFinset z ∩ Iso = ∅ := Finset.card_eq_zero.mp hziso0
    have htznadj : ¬G.Adj z t := by
      intro he
      have : t ∈ G.neighborFinset z ∩ Iso :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z t).mpr he, htIso⟩
      rw [hziso0'] at this; exact Finset.notMem_empty t this
    -- `z ∉ Iso` and `t ∈ Iso`, so the four vertices are distinct.
    have hznotIso : z ∉ Iso := by
      rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.2
    have htnotHub : t ∉ Hub := fun he => Finset.disjoint_left.mp hdisj he htIso
    have htg1ne : t ≠ g₁ := fun he => htnotHub (he ▸ hg1Hub)
    have htg2ne : t ≠ g₂ := fun he => htnotHub (he ▸ hg2Hub)
    have htzne : t ≠ z := fun he => hznotIso (he ▸ htIso)
    -- Assemble the good `C₄`  `{t, g₁, z, g₂}`.
    refine hC4 ⟨t, g₁, z, g₂, ?_, htg1.symm, hzg1.symm, hzg2, htg2, fun h => htznadj h.symm,
      hadj, ?_⟩
    · rw [Finset.card_eq_four]
      exact ⟨t, g₁, z, g₂, htg1ne, htzne, htg2ne, hzg1ne.symm, hg12, hzg2ne, rfl⟩
    · rw [hisodeg3 t htIso, hdeg4 g₁ hg1Hub, hzdeg3, hdeg4 g₂ hg2Hub]

/-- **The sharp `Z`-distribution (`z_R = 2`, `z_P = 2`) under the good-triangle threshold `11`.**
The two `M`-edge endpoints carry exactly four hub-incidences (`zdeg_sum_four`).  Each meets *at most*
one rich hub (`no_z_two_rich_hubs`, using `hT ≤ 11`), so `z_R ≤ 2`; each meets *at least* one
(`each_z_meets_rich`), so `z_R ≥ 2`.  Hence `z_R = 2` and `z_P = 4 − 2 = 2`.  Here
`R = {h : 2 ≤ |N(h) ∩ Iso|}` and `P` is its complement in `Hub`.  For `|Hub| = 11` (`5` poor hubs),
this **pins `z_R = 2`** — exactly as at `n = 18`: the `Z`-hub mass (`4`) and the per-endpoint
rich/poor split are unchanged because `|Iso| = 6` and `|Z| = 2` carry over verbatim.

The rich-side ≥ bound is threaded through `hztwopoor` (the not-yet-ported `z`-meets-2-poor
extraction); the ≤ bound is fully axiom-clean. -/
theorem zdeg_split_sharp_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    (∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card = 2 ∧
    ∑ g ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso))).card = 2) ∨ ZPoorCutConfig G := by
  classical
  set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 19) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  by_cases hcut : ZPoorCutConfig G
  · exact Or.inr hcut
  refine Or.inl ?_
  have hZcard : Z.card = 2 := z_card_two_nineteen Hub Iso hdisj hHub hIso
  -- `z_R + z_P = 4`.
  have hsum4 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Z).card = 4 :=
    zdeg_sum_four_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  have hsplit : ∑ r ∈ R, (G.neighborFinset r ∩ Z).card
      + ∑ g ∈ P, (G.neighborFinset g ∩ Z).card = 4 := by
    rw [hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum4
  -- `z_R ≥ 2` (each endpoint meets a rich hub).
  obtain ⟨hzRge, _⟩ := (zdeg_split_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT).resolve_right hcut
  rw [← hRdef, ← hZdef] at hzRge
  -- `z_R ≤ 2` (no endpoint meets two rich hubs).
  have hzRle : ∑ r ∈ R, (G.neighborFinset r ∩ Z).card ≤ 2 := by
    have hcross : ∑ r ∈ R, (G.neighborFinset r ∩ Z).card
        = ∑ z ∈ Z, (G.neighborFinset z ∩ R).card := cross_count_nineteen G R Z
    rw [hcross]
    have hez : ∀ z ∈ Z, (G.neighborFinset z ∩ R).card ≤ 1 :=
      no_z_two_rich_hubs_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3 hdsum
        hleak hshare hno2hub hC4 hT
    calc ∑ z ∈ Z, (G.neighborFinset z ∩ R).card ≤ ∑ _z ∈ Z, 1 := Finset.sum_le_sum hez
      _ = 2 := by rw [Finset.sum_const, hZcard, smul_eq_mul, mul_one]
  exact ⟨by omega, by omega⟩

end N19

end ACMax
