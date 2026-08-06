import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct

/-!
# Octahedron forcing core for the rich count crux (`n = 19`, `|Hub| = 11`)

Port of the `n = 18` `TwinCert18OctahedronForce` LEAF (`octahedron_trace_saturate_eighteen`) to the
NEW `n = 19` `|Hub| = 11` regime.  The single saturation lemma here is the genuinely-reusable
`K₂,₂,₂` trace-saturation; it is stated **general in `|R|`** (the n = 18 file hard-coded `R.card = 6`)
so it applies both to the rigid `r = 6` octahedron downstream *and* to the `r = 5` `{2,2,2,3,3}`
residual that `rich_count_ge_six_twenty` must exclude.

Writing `m = ∑_{r∈R} |N r ∩ R|` for the ordered rich-internal edge mass, the lemma closes

  `(∑_{t∈Iso} |N t ∩ R|·(|N t ∩ R| − 1)) + m = |R.offDiag| = |R|² − |R|`

(every non-adjacent rich pair shares *exactly* one twin via `rich_nonadj_share_eq_one_twenty`, and
every adjacent rich pair shares none by the good-triangle exclusion `hT`, so the twins' rich
off-diagonals biject onto the non-adjacent ordered rich pairs and the mass bijects onto the adjacent
ones), together with the rich iso-incidence sum

  `∑_{r∈R} |N r ∩ Iso| = 7 + |R|`

(total `18`, poor side `= |Hub| − |R| = 11 − |R|` with every poor hub of iso-degree exactly `1`).

* `octahedron_trace_saturate_twenty` — LEAF, axiom-clean.

**`mass_excl` is intentionally NOT ported.**  The n = 18 `octahedron_mass_excl_eighteen` pins the
handshake `m + E(R, P) + z_R = 8` via `z_R = 2` (`zdeg_split_sharp_eighteen` from the heavy
`TwinCert18RichZdeg` chain).  At `n = 19` `|Hub| = 11` the `r = 5` `{2,2,2,3,3}` residual has
`m + E(R, P) + z_R = 8` (`∑deg_R = 20`, `S = 12`) with **no contradiction available from the
handshake alone** — excluding it needs the per-subcase poor/`Z` layout layer (the analog of
`TwinCert18OctahedronPoorForce`).  See `rich_count_ge_six_twenty` for the documented residual.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Octahedron trace saturation (LEAF, general `|R|`).**  Under the no-two-hub hypothesis every
non-adjacent rich pair shares *exactly* one twin (`rich_nonadj_share_eq_one_twenty`) and (by the
good-triangle exclusion `hT`) no adjacent rich pair shares a twin: so the twins' rich off-diagonals
biject onto the non-adjacent ordered rich pairs and the rich-internal mass bijects onto the adjacent
ones.  Hence the ordered trace plus the mass equals `|R.offDiag| = |R|² − |R|`.  The rich
iso-incidence sum is `7 + |R|` (total `18`, poor side `= 11 − |R|`). -/
theorem octahedron_trace_saturate_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso R : Finset (Fin 20))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) :
    (∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card)
        + ∑ r ∈ R, (G.neighborFinset r ∩ R).card = R.card * R.card - R.card ∧
    ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 6 + R.card := by
  classical
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  have hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hReq, Finset.mem_filter] at ha; exact ha.2
  set Dadj : Finset (Fin 20 × Fin 20) := R.offDiag.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  set Dnadj : Finset (Fin 20 × Fin 20) := R.offDiag.filter (fun p => ¬G.Adj p.1 p.2) with hDnadjdef
  set K : ℕ := R.card * R.card - R.card with hKdef
  have hpart : Dadj.card + Dnadj.card = K := by
    rw [hDadjdef, hDnadjdef, Finset.card_filter_add_card_filter_not, Finset.offDiag_card, hKdef]
  -- Sigma sets whose cards are the two sums.
  set Sq := Iso.sigma (fun t => (G.neighborFinset t ∩ R).offDiag) with hSqdef
  have hSqcard : Sq.card = ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card :=
    Finset.card_sigma _ _
  set Se := R.sigma (fun r => G.neighborFinset r ∩ R) with hSedef
  have hSecard : Se.card = ∑ r ∈ R, (G.neighborFinset r ∩ R).card := Finset.card_sigma _ _
  -- `∑ offDiag = Dnadj.card`: each non-adjacent rich pair has a unique shared twin (bijection).
  have hq_eq : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card) = Dnadj.card := by
    rw [← hSqcard]
    apply Finset.card_nbij (fun x => x.2)
    · -- MapsTo
      intro x hx
      rw [Finset.mem_coe, hSqdef, Finset.mem_sigma] at hx
      obtain ⟨htIso, hp⟩ := hx
      rw [Finset.mem_offDiag] at hp
      obtain ⟨h1, h2, hne⟩ := hp
      rw [Finset.mem_inter, G.mem_neighborFinset] at h1 h2
      obtain ⟨ht1, h1R⟩ := h1
      obtain ⟨ht2, h2R⟩ := h2
      rw [Finset.mem_coe, hDnadjdef, Finset.mem_filter, Finset.mem_offDiag]
      refine ⟨⟨h1R, h2R, hne⟩, ?_⟩
      intro hadj
      have ht1ne : x.1 ≠ x.2.1 := fun he =>
        Finset.disjoint_left.mp hdisj (hRsub h1R) (he ▸ htIso)
      have ht2ne : x.1 ≠ x.2.2 := fun he =>
        Finset.disjoint_left.mp hdisj (hRsub h2R) (he ▸ htIso)
      refine hT ⟨x.2.1, x.2.2, x.1, hne, ht2ne.symm, ht1ne.symm, hadj, ht2.symm, ht1.symm, ?_⟩
      rw [hdeg4 x.2.1 (hRsub h1R), hdeg4 x.2.2 (hRsub h2R), hisodeg3 x.1 htIso]
    · -- InjOn: the shared twin of a non-adjacent rich pair is unique.
      intro x hx y hy hxy
      rw [Finset.mem_coe, hSqdef, Finset.mem_sigma] at hx hy
      obtain ⟨hxIso, hxp⟩ := hx
      obtain ⟨hyIso, hyp⟩ := hy
      rw [Finset.mem_offDiag] at hxp hyp
      obtain ⟨hx1, hx2, hxne⟩ := hxp
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx1 hx2
      obtain ⟨hxt1, hx1R⟩ := hx1
      obtain ⟨hxt2, hx2R⟩ := hx2
      have hp : x.2 = y.2 := hxy
      have hya : y.2.1 = x.2.1 := by rw [hp]
      have hyb : y.2.2 = x.2.2 := by rw [hp]
      have hnadj : ¬G.Adj x.2.1 x.2.2 := by
        intro hadj
        have ht1ne : x.1 ≠ x.2.1 := fun he =>
          Finset.disjoint_left.mp hdisj (hRsub hx1R) (he ▸ hxIso)
        have ht2ne : x.1 ≠ x.2.2 := fun he =>
          Finset.disjoint_left.mp hdisj (hRsub hx2R) (he ▸ hxIso)
        refine hT ⟨x.2.1, x.2.2, x.1, hxne, ht2ne.symm, ht1ne.symm, hadj, hxt2.symm, hxt1.symm, ?_⟩
        rw [hdeg4 x.2.1 (hRsub hx1R), hdeg4 x.2.2 (hRsub hx2R), hisodeg3 x.1 hxIso]
      have hsh := hshare x.2.1 (hRsub hx1R) (hdeg4 x.2.1 (hRsub hx1R)) x.2.2 (hRsub hx2R)
        (hdeg4 x.2.2 (hRsub hx2R)) hxne hnadj
      obtain ⟨hy1, hy2, _⟩ := hyp
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy1 hy2
      obtain ⟨hyt1, _⟩ := hy1
      obtain ⟨hyt2, _⟩ := hy2
      have hxmem : x.1 ∈ G.neighborFinset x.2.1 ∩ G.neighborFinset x.2.2 ∩ Iso := by
        rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
        exact ⟨⟨hxt1.symm, hxt2.symm⟩, hxIso⟩
      have hymem : y.1 ∈ G.neighborFinset x.2.1 ∩ G.neighborFinset x.2.2 ∩ Iso := by
        rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
        rw [hya] at hyt1; rw [hyb] at hyt2
        exact ⟨⟨hyt1.symm, hyt2.symm⟩, hyIso⟩
      have hxy1 : x.1 = y.1 := by
        rcases Finset.card_le_one.mp hsh x.1 hxmem y.1 hymem with h; exact h
      exact Sigma.ext hxy1 (heq_of_eq hp)
    · -- SurjOn: every non-adjacent rich pair is realised by its shared twin.
      intro p hp
      rw [Finset.mem_coe, hDnadjdef, Finset.mem_filter, Finset.mem_offDiag] at hp
      obtain ⟨⟨h1R, h2R, hne⟩, hnadj⟩ := hp
      have hsh := rich_nonadj_share_eq_one_twenty G Hub Iso hshare hno2hub p.1 p.2 (hRsub h1R)
        (hRsub h2R) (hdeg4 p.1 (hRsub h1R)) (hdeg4 p.2 (hRsub h2R)) hne hnadj
        (hRrich p.1 h1R) (hRrich p.2 h2R)
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hsh
      have htmem : t ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso := by
        rw [ht]; exact Finset.mem_singleton_self _
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at htmem
      obtain ⟨⟨ht1, ht2⟩, htIso⟩ := htmem
      refine ⟨⟨t, p⟩, ?_, rfl⟩
      rw [Finset.mem_coe, hSqdef, Finset.mem_sigma, Finset.mem_offDiag]
      refine ⟨htIso, ?_, ?_, hne⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht1.symm, h1R⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht2.symm, h2R⟩
  -- `m = Dadj.card`: the rich-internal mass realises each adjacent ordered rich pair (bijection).
  have hm_eq : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = Dadj.card := by
    rw [← hSecard]
    apply Finset.card_nbij (fun x => ((x.1, x.2) : Fin 20 × Fin 20))
    · intro x hx
      rw [Finset.mem_coe, hSedef, Finset.mem_sigma, Finset.mem_inter, G.mem_neighborFinset] at hx
      obtain ⟨h1R, hadj, h2R⟩ := hx
      rw [Finset.mem_coe, hDadjdef, Finset.mem_filter, Finset.mem_offDiag]
      exact ⟨⟨h1R, h2R, G.ne_of_adj hadj⟩, hadj⟩
    · intro x hx y hy hxy
      simp only [Prod.mk.injEq] at hxy
      exact Sigma.ext hxy.1 (heq_of_eq hxy.2)
    · intro p hp
      rw [Finset.mem_coe, hDadjdef, Finset.mem_filter, Finset.mem_offDiag] at hp
      obtain ⟨⟨h1R, h2R, _⟩, hadj⟩ := hp
      refine ⟨⟨p.1, p.2⟩, ?_, rfl⟩
      rw [Finset.mem_coe, hSedef, Finset.mem_sigma, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨h1R, hadj, h2R⟩
  -- The two equalities combine with `hpart` to `= K = |R|² − |R|`.
  refine ⟨by omega, ?_⟩
  -- The rich iso-incidence sum is `7 + |R|`.
  set P : Finset (Fin 20) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hPsubHub : P ⊆ Hub := Finset.filter_subset _ _
  have hPcard : P.card = 12 - R.card := by
    have hs := Finset.card_filter_add_card_filter_not
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) (s := Hub)
    rw [← hReq, ← hPdef, hHub] at hs; omega
  have hPpoor : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hg
    have hgHub : g ∈ Hub := hPsubHub hg
    rw [hPdef, Finset.mem_filter] at hg
    have := hnozero g hgHub; omega
  have hiso18 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  have hisoP : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 12 - R.card := by
    have heq : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = ∑ _g ∈ P, 1 :=
      Finset.sum_congr rfl (fun g hg => hPpoor g hg)
    rw [heq, Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  have hsp : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card
      + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
    rw [hReq, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hiso18
  -- `|R| ≤ 11` so `7 + |R| = 18 - (11 - |R|)`.
  have hRle : R.card ≤ 12 := by rw [← hHub]; exact Finset.card_le_card hRsub
  omega

end N20

end ACMax
