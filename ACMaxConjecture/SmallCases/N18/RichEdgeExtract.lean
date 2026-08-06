import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.OctahedronStruct
import ACMaxConjecture.SmallCases.N18.OctahedronPoorForce
import ACMaxConjecture.SmallCases.N18.OctahedronForce

/-!
# Octahedron extraction for the rich–poor edge crux (`n = 18`)

This file isolates the genuine covering-design frontier of the tight `e(M) = 1`, all-degree-`4`,
`(|Hub|, |Iso|) = (10, 6)` profile.  A *bad* rich–poor edge `r ~ g` (with `g` poor of iso-degree
`1`, whose unique twin `t` misses `r`) together with `|R| = 6` and the no-two-hub hypothesis forces
the rigid **octahedron**: the six rich hubs carry a perfect matching `E(R, R) = 3`, four `M`-isolated
twins meet three rich hubs each (a `K₂,₂,₂` triangle-decomposition), the remaining two twins meet one
rich and two poor hubs, and every non-adjacent rich pair shares exactly one twin (so the two-hub
technique is provably insufficient).  The octahedron is killed only by a good cert that depends on
the poor/`Z` layout (a triangle `≤ 11`, a `K₂,₃ ≤ 19`, or a `C₄ ≤ 14`).

* `no_share0_forces_octahedron_eighteen` — the `K₂,₂,₂` pair-cover forcing (1 documented `sorry`).
* `octahedron_poor_cert_eighteen` — the three-way poor/`Z` cert forcing (1 documented `sorry`).
* `two_hub_or_cert_from_rp_edge_eighteen` — master wiring: assemble to a contradiction.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The rigid octahedron structure** of a no-two-hub `(10, 6)` configuration that carries a bad
rich–poor edge.  The six rich hubs `R` span a near-perfect matching (`E(R, R) ∈ {2, 3}`, i.e. ordered
internal mass `4` or `6`); at least four `M`-isolated twins meet exactly three rich hubs each (the
`K₂,₂,₂` triangle-decomposition), and every twin meets at most three rich hubs (so the `≤ 2` remaining
twins carry the poor incidences). -/
def OctahedronRigid (G : SimpleGraph (Fin 18)) (Iso R : Finset (Fin 18)) : Prop :=
  R.card = 6 ∧
  ((∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨ (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6) ∧
  4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card ∧
  ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3

/-- **The octahedron forcing (HARD — 1 documented `sorry`).**  A bad rich–poor edge `r ~ g` (with `g`
poor of iso-degree `1`, whose unique `M`-isolated twin `t` misses `r`) together with `|R| = 6` and the
no-two-hub hypothesis forces the rigid octahedron.  The `K₂,₂,₂` pair-cover counting (each
non-adjacent rich pair shares exactly one twin via `rich_nonadj_share_eq_one`, the twins' rich
off-diagonals saturate the `30` ordered rich pairs by `rich_twin_trace_le_eighteen`, pinning four
twins onto rich triples and the matching mass to `{2, 3}`) is the remaining `sorry`. -/
theorem no_share0_forces_octahedron_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
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
    (r g t : Fin 18) (hrR : r ∈ R) (hgHub : g ∈ Hub)
    (_hg1 : (G.neighborFinset g ∩ Iso).card = 1) (hgr : ¬ 2 ≤ (G.neighborFinset g ∩ Iso).card)
    (hadj : G.Adj r g) (_htIso : t ∈ Iso) (_hgt : G.Adj g t) (_hrt : ¬G.Adj r t) :
    OctahedronRigid G Iso R := by
  classical
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- Each `M`-isolated twin meets at most three rich hubs (degree-`3`, all neighbours in `Hub`).
  have hf3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsub)
      _ = 3 := hiso3 t ht
  -- The twin counts by number of rich hubs met.
  set n0 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card with hn0
  set n1 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card with hn1
  set n2 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card with hn2
  set n3 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card with hn3
  -- `n₀ + n₁ + n₂ + n₃ = 6`.
  have hI : (6 : ℕ) = n0 + n1 + n2 + n3 := by
    rw [hn0, hn1, hn2, hn3, ← hIso, Finset.card_eq_sum_ones Iso]
    simp only [Finset.card_filter]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := hf3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  -- `∑_t |N t ∩ R| = n₁ + 2n₂ + 3n₃`.
  have hII : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = n1 + 2 * n2 + 3 * n3 := by
    rw [hn1, hn2, hn3]
    simp only [Finset.card_filter, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := hf3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  -- `∑_t |N t ∩ R|·(|N t ∩ R| − 1) = 2n₂ + 6n₃` (off-diagonal trace).
  have hIII : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card = 2 * n2 + 6 * n3 := by
    rw [hn2, hn3]
    simp only [Finset.offDiag_card, Finset.card_filter, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hb := hf3 t ht
    rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1 ∨
        (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
      with h | h | h | h <;> simp [h]
  -- Saturation `(∑ offDiag) + m = 30` and the rich iso-sum `= 14`.
  obtain ⟨hsat, h14⟩ := octahedron_trace_saturate_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub
    hIso hisodeg3 hshare hno2hub hT hRcard hnozero
  -- Cross-count: `∑_t |N t ∩ R| = ∑_r |N r ∩ Iso| = 14`.
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 14 := by
    rw [cross_count G Iso R]; exact h14
  -- Mass exclusion: `m ≠ 8 ∧ m ≠ 10`.
  obtain ⟨hne8, hne10⟩ := octahedron_mass_excl_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso
    hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hRcard hnozero r g hrR hgHub hgr hadj
  -- The linear system pins `n₃ = 4` and `m ∈ {4, 6}`.
  refine ⟨hRcard, ?_, ?_, hf3⟩
  · omega
  · omega

/-- **The octahedron poor/`Z` cert (HARD — 1 documented `sorry`).**  The rigid octahedron is killed by
a good cert that depends on the poor/`Z` layout: either two adjacent poor hubs share a low twin
(triangle `4 + 4 + 3 = 11`), or the four poor hubs form a `C₄` and a low twin with two diagonal poor
hubs gives a `K₂,₃` (`Σ = 4 + 4 + 3 + 4 + 4 = 19`), or two `Z`-attached rich hubs are matched
(rich–`Z`–`Z`–rich `C₄`, `Σ = 4 + 3 + 3 + 4 = 14`).  The poor-`C₄` forcing is the remaining `sorry`. -/
theorem octahedron_poor_cert_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
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
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hocta : OctahedronRigid G Iso R) :
    (∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) ∨
    (∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) ∨
    (∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14) := by
  classical
  obtain ⟨hRcard, hmass, hhigh4, htle3⟩ := hocta
  rcases octahedron_poor_layer_force_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso
      hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard hmass hhigh4 htle3 with
    ⟨g₁, g₂, t, hg₁, hg₂, ht, hne, hadj, hgt₁, hgt₂⟩ |
    ⟨a, b, c, d, t, ha, hb, hc, hd, ht, hac, had, hat, hbc, hbd, hbt,
      hnab, hncd, hnct, hndt, habne, hacne, hadne, hbcne, hbdne, hcdne⟩ |
    ⟨r₁, r₂, z₁, z₂, hr₁, hr₂, hz₁, hz₂, hdz₁, hdz₂, hadj1, hadjz, hadj2, hadjr,
      hnr₁z₂, hnz₁r₂, hr₁r₂, hz₁z₂⟩
  · -- (a) two adjacent poor hubs sharing a low twin → good triangle `{g₁, g₂, t}`.
    left
    have hg₁t : g₁ ≠ t := by rintro rfl; exact Finset.disjoint_left.mp hdisj hg₁ ht
    have hg₂t : g₂ ≠ t := by rintro rfl; exact Finset.disjoint_left.mp hdisj hg₂ ht
    refine ⟨g₁, g₂, t, hne, hg₂t, hg₁t, hadj, hgt₂, hgt₁, ?_⟩
    rw [hdeg4 g₁ hg₁, hdeg4 g₂ hg₂, hisodeg3 t ht]
  · -- (b) the four poor hubs form a `C₄`, a low twin meets a diagonal pair → good `K₂,₃`.
    right; left
    have hat' : a ≠ t := by rintro rfl; exact Finset.disjoint_left.mp hdisj ha ht
    have hbt' : b ≠ t := by rintro rfl; exact Finset.disjoint_left.mp hdisj hb ht
    have hct' : c ≠ t := by rintro rfl; exact Finset.disjoint_left.mp hdisj hc ht
    have hdt' : d ≠ t := by rintro rfl; exact Finset.disjoint_left.mp hdisj hd ht
    refine ⟨a, b, c, d, t,
      card_five_eighteen a b c d t habne hacne hadne hat' hbcne hbdne hbt' hcdne hct' hdt',
      hac, had, hat, hbc, hbd, hbt, hnab, hncd, hnct, hndt, ?_⟩
    rw [hdeg4 a ha, hdeg4 b hb, hdeg4 c hc, hdeg4 d hd, hisodeg3 t ht]
  · -- (c) two matched rich hubs are the two `Z`-attachments → good `C₄`  `r₁–z₁–z₂–r₂`.
    right; right
    have hz₁nH : z₁ ∉ Hub := by
      rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz₁; exact hz₁.2.1
    have hz₂nH : z₂ ∉ Hub := by
      rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz₂; exact hz₂.2.1
    have hr₁z₁ : r₁ ≠ z₁ := by rintro rfl; exact hz₁nH hr₁
    have hr₁z₂ : r₁ ≠ z₂ := by rintro rfl; exact hz₂nH hr₁
    have hr₂z₁ : r₂ ≠ z₁ := by rintro rfl; exact hz₁nH hr₂
    have hr₂z₂ : r₂ ≠ z₂ := by rintro rfl; exact hz₂nH hr₂
    refine ⟨r₁, z₁, z₂, r₂, ?_, hadj1, hadjz, hadj2, hadjr, hnr₁z₂, hnz₁r₂, ?_⟩
    · rw [Finset.card_eq_four]
      exact ⟨r₁, z₁, z₂, r₂, hr₁z₁, hr₁z₂, hr₁r₂, hz₁z₂, hr₂z₁.symm, hr₂z₂.symm, rfl⟩
    · rw [hdeg4 r₁ hr₁, hdz₁, hdz₂, hdeg4 r₂ hr₂]

/-- **Master wiring: the bad rich–poor edge is contradictory.**  Assembling the octahedron forcing
with the poor/`Z` cert, a bad rich–poor edge in a no-two-hub `(10, 6)` configuration yields a good
triangle, `K₂,₃`, or `C₄`, each excluded by `hT`, `hK23`, `hC4`. -/
theorem two_hub_or_cert_from_rp_edge_eighteen (G : SimpleGraph (Fin 18))
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
    (r g t : Fin 18) (hrR : r ∈ R) (hgHub : g ∈ Hub)
    (hg1 : (G.neighborFinset g ∩ Iso).card = 1) (hgr : ¬ 2 ≤ (G.neighborFinset g ∩ Iso).card)
    (hadj : G.Adj r g) (htIso : t ∈ Iso) (hgt : G.Adj g t) (hrt : ¬G.Adj r t) :
    False := by
  have hocta : OctahedronRigid G Iso R :=
    no_share0_forces_octahedron_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
      hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hRcard hnozero r g t hrR hgHub hg1 hgr hadj
      htIso hgt hrt
  rcases octahedron_poor_cert_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
      hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hocta with htri | hk23 | hc4
  · exact hT htri
  · exact hK23 hk23
  · exact hC4 hc4

end N18

end ACMax
