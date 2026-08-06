import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichZdeg

/-!
# Octahedron forcing core for the rich–poor edge crux (`n = 18`)

This file isolates the two genuinely-new counting facts that drive
`no_share0_forces_octahedron_eighteen` (the assembly lives in `TwinCert18RichEdgeExtract`).

Writing `m = ∑_{r∈R} |N r ∩ R|` for the ordered rich-internal edge mass, and `n_k` for the number
of `M`-isolated twins meeting exactly `k` rich hubs, the assembly closes the linear system

  `n₃ + n₂ + n₁ + n₀ = 6`,   `3n₃ + 2n₂ + n₁ = 14`,   `6n₃ + 2n₂ = 30 − m`

(`14` is the rich iso-incidence sum, `30 − m` the saturated trace).  Trace-consistency leaves
`m ∈ {4, 6, 8, 10}` (with `n₃ = 4` for `m ∈ {4, 6}`), and the handshake below kills `m ∈ {8, 10}`.

* `octahedron_trace_saturate_eighteen` — LEAF.  Saturation: the per-twin off-diagonal rich trace
  plus the rich-internal mass equals `|R.offDiag| = 30` *with equality* (every non-adjacent rich pair
  shares exactly one twin via `rich_nonadj_share_eq_one`), together with the rich iso-sum `= 14`.
* `octahedron_mass_excl_eighteen` — the handshake `m + E(R, P) = 8`; a bad rich–poor edge gives
  `E(R, P) ≥ 1`, so `m ≤ 7`, excluding `m ∈ {8, 10}`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Octahedron trace saturation (LEAF).**  Under the no-two-hub hypothesis every non-adjacent rich
pair shares *exactly* one twin (`rich_nonadj_share_eq_one`), so the injections of
`rich_twin_trace_le_eighteen` are bijections: the twins' rich off-diagonals saturate the non-adjacent
ordered rich pairs and the rich-internal mass saturates the adjacent ones.  Hence the ordered trace
plus the mass equals `|R.offDiag| = 30`.  The rich iso-incidence sum is `14` (total `18`, poor side
`= |P| = 4`). -/
theorem octahedron_trace_saturate_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso R : Finset (Fin 18))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hRcard : R.card = 6) (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) :
    (∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card)
        + ∑ r ∈ R, (G.neighborFinset r ∩ R).card = 30 ∧
    ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 14 := by
  classical
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  have hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hReq, Finset.mem_filter] at ha; exact ha.2
  set Dadj : Finset (Fin 18 × Fin 18) := R.offDiag.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  set Dnadj : Finset (Fin 18 × Fin 18) := R.offDiag.filter (fun p => ¬G.Adj p.1 p.2) with hDnadjdef
  have hpart : Dadj.card + Dnadj.card = 30 := by
    rw [hDadjdef, hDnadjdef, Finset.card_filter_add_card_filter_not, Finset.offDiag_card, hRcard]
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
      have hsh := rich_nonadj_share_eq_one G Hub Iso hshare hno2hub p.1 p.2 (hRsub h1R) (hRsub h2R)
        (hdeg4 p.1 (hRsub h1R)) (hdeg4 p.2 (hRsub h2R)) hne hnadj (hRrich p.1 h1R) (hRrich p.2 h2R)
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
    apply Finset.card_nbij (fun x => ((x.1, x.2) : Fin 18 × Fin 18))
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
  -- The two equalities combine with `hpart` to `= 30`.
  refine ⟨by omega, ?_⟩
  -- The rich iso-incidence sum is `14`.
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hPsubHub : P ⊆ Hub := Finset.filter_subset _ _
  have hPcard : P.card = 4 := by
    have hs := Finset.card_filter_add_card_filter_not
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) (s := Hub)
    rw [← hReq, ← hPdef, hHub, hRcard] at hs; omega
  have hPpoor : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hg
    have hgHub : g ∈ Hub := hPsubHub hg
    rw [hPdef, Finset.mem_filter] at hg
    have := hnozero g hgHub; omega
  have hiso18 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hisoP : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 4 := by
    have heq : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = ∑ _g ∈ P, 1 :=
      Finset.sum_congr rfl (fun g hg => hPpoor g hg)
    rw [heq, Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  have hsp : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card
      + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
    rw [hReq, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hiso18
  omega

/-- **Octahedron mass exclusion (handshake).**  The degree sum over the six rich hubs splits as
`∑_{r∈R} deg r = m + E(R, P) + S + z_R` where `m = ∑_{r∈R}|N r ∩ R|`, `E(R, P) = ∑_{r∈R}|N r ∩ P|`,
`S = ∑_{r∈R}|N r ∩ Iso| = 14` and `z_R = ∑_{r∈R}|N r ∩ Z| = 2` (`zdeg_split_sharp_eighteen`).  As
`∑ deg = 24` this reads `m + E(R, P) = 8`.  A bad rich–poor edge `r ~ g` gives `E(R, P) ≥ 1`, so
`m ≤ 7`: hence `m ≠ 8` and `m ≠ 10`. -/
theorem octahedron_mass_excl_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso R : Finset (Fin 18))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hRcard : R.card = 6) (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (r g : Fin 18) (hrR : r ∈ R) (hgHub : g ∈ Hub)
    (hgr : ¬ 2 ≤ (G.neighborFinset g ∩ Iso).card) (hadj : G.Adj r g) :
    (∑ r ∈ R, (G.neighborFinset r ∩ R).card) ≠ 8 ∧
    (∑ r ∈ R, (G.neighborFinset r ∩ R).card) ≠ 10 := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- `g ∈ P` (poor) and `r ∈ R`, so the bad edge contributes to `E(R, P)`.
  have hgP : g ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hgHub, hgr⟩
  have hdisjRP : Disjoint R P := by
    rw [hReq, hPdef]; exact Finset.disjoint_filter_filter_not Hub Hub _
  have hunion : R ∪ P = Hub := by
    rw [hReq, hPdef]; exact Finset.filter_union_filter_not_eq _ Hub
  -- Per-rich-hub four-way degree split over the partition `R ⊔ P ⊔ Iso ⊔ Z`.
  have hsplit : ∀ a ∈ R, (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
      + (G.neighborFinset a ∩ Iso).card + (G.neighborFinset a ∩ Z).card = 4 := by
    intro a ha
    have hd : G.degree a = 4 := hdeg4 a (hRsub ha)
    have hRP : (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
        = (G.neighborFinset a ∩ Hub).card := by
      rw [← Finset.card_union_of_disjoint
            (Finset.disjoint_left.mpr (fun x hx hx2 =>
              Finset.disjoint_left.mp hdisjRP (Finset.mem_of_mem_inter_right hx)
                (Finset.mem_of_mem_inter_right hx2))),
        ← Finset.inter_union_distrib_left, hunion]
    have hHIZ : (G.neighborFinset a ∩ Hub).card + (G.neighborFinset a ∩ Iso).card
        + (G.neighborFinset a ∩ Z).card = G.degree a := by
      have h1 : (G.neighborFinset a ∩ Hub).card + (G.neighborFinset a \ Hub).card
          = (G.neighborFinset a).card := Finset.card_inter_add_card_sdiff _ _
      have h2 : ((G.neighborFinset a \ Hub) ∩ Iso).card + ((G.neighborFinset a \ Hub) \ Iso).card
          = (G.neighborFinset a \ Hub).card := Finset.card_inter_add_card_sdiff _ _
      have he1 : (G.neighborFinset a \ Hub) ∩ Iso = G.neighborFinset a ∩ Iso := by
        ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨hx, _⟩, hxi⟩; exact ⟨hx, hxi⟩
        · rintro ⟨hx, hxi⟩
          exact ⟨⟨hx, fun hxh => Finset.disjoint_left.mp hdisj hxh hxi⟩, hxi⟩
      have he2 : (G.neighborFinset a \ Hub) \ Iso = G.neighborFinset a ∩ Z := by
        ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, hZdef, Finset.mem_sdiff,
          Finset.mem_univ, true_and, Finset.mem_union, not_or]
        tauto
      rw [he1, he2] at h2
      rw [G.card_neighborFinset_eq_degree] at h1
      omega
    omega
  have hsum24 : ∑ a ∈ R, ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ P).card
      + (G.neighborFinset a ∩ Iso).card + (G.neighborFinset a ∩ Z).card) = 24 := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_const, hRcard, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum24
  -- `S = ∑_R |N ∩ Iso| = 14`.
  have hisoR : ∑ a ∈ R, (G.neighborFinset a ∩ Iso).card = 14 :=
    (octahedron_trace_saturate_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
      hshare hno2hub hT hRcard hnozero).2
  -- `z_R = ∑_R |N ∩ Z| = 2`.
  obtain ⟨hzR2, _⟩ := zdeg_split_sharp_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
    hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT
  rw [← hReq, ← hZdef] at hzR2
  -- `E(R, P) ≥ 1` from the bad edge.
  have hERPpos : 1 ≤ ∑ a ∈ R, (G.neighborFinset a ∩ P).card := by
    have hterm : 1 ≤ (G.neighborFinset r ∩ P).card :=
      Finset.Nonempty.card_pos
        ⟨g, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj, hgP⟩⟩
    calc 1 ≤ (G.neighborFinset r ∩ P).card := hterm
      _ ≤ ∑ a ∈ R, (G.neighborFinset a ∩ P).card :=
          Finset.single_le_sum (f := fun a => (G.neighborFinset a ∩ P).card)
            (fun a _ => Nat.zero_le _) hrR
  omega

end N18

end ACMax
