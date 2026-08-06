import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.RichZdeg
import ACMaxConjecture.SmallCases.N20.OctahedronStruct
import ACMaxConjecture.SmallCases.N20.OctahedronForce
import ACMaxConjecture.SmallCases.N20.OctahedronPoorForce2

/-!
# Octahedron mass-`4` absurdity and three-way force (`n = 20`, `|Hub| = 12`, HARD CRUX core)

This file carries the genuinely-new `|Hub| = 12` content behind
`octahedron_poor_layer_force_twenty`.  Over the rigid octahedron (six rich hubs `R`, **six** poor
hubs `P = Hub \ R`, four high `M`-isolated twins, two low twins, two adjacent `M`-edge endpoints
`Z = univ \ (Hub ∪ Iso)`) the rich-internal mass `mRR ∈ {4, 6}` is decided and either a good
sub-configuration or a `ZPoorCutConfig` is forced.

* `octahedron_mass_four_absurd_twenty` — the rich-internal mass `4` is impossible outright.
  The trace saturation `(∑_t offDiag) + mRR = |R|² − |R| = 30` with `∑_t |N t ∩ R| = 12` forces the
  twin rich-degree profile `n₀ + n₁ + n₂ + n₃ = 6`, `n₁ + 2 n₂ + 3 n₃ = 12`, `2 n₂ + 6 n₃ = 26`;
  the last gives `n₂ + 3 n₃ = 13`, so `n₁ + n₂ + 13 = 12` — impossible over `ℕ`.  Even simpler
  than the `n = 19` parity kill (`3 n₃ = 13`).
* `octahedron_poor_force_b_or_c_twenty` — the force.  Branch (a): a low twin meeting two adjacent
  poor hubs yields a good triangle `4 + 4 + 3 = 11`.  Otherwise mass `4` is killed
  (`octahedron_mass_four_absurd_twenty`) and mass `6` makes the ordered poor–poor mass `12`, so the
  six poor (split `3 + 3` over the two low twins) carry exactly six cross edges.  **The
  genuinely-new `|Hub| = 12` dichotomy:** if some same-side poor pair has poor-degree sum `≥ 5`,
  the two share `≥ 2` common neighbours on the size-`3` far side (`5 − 3 = 2`), a good `K₂,₃` of
  degree sum `4·4 + 3 = 19` — branch (b).  In the residual the poor layer is `2`-regular (a `C₆`):
  then a poor hub `p` carries a `Z`-slot `z₀` (its four slots being twin + two poor + `z₀`, with no
  rich neighbour), and `⟨rich hub avoiding `Z` + its two twins | p + low twin + z₀⟩` is a
  `TwoHubConfig` with one `Z`-leaf, contradicting `hcut : ¬ZPoorCutConfig G`.  (Branch (c), the
  matched-`Z` rich `C₄`, is vacuous because mass `4` never occurs.)
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Mass-`4` octahedron is impossible (LEAF, `n = 20`).**  In the rigid `|Hub| = 12`
octahedron the ordered rich-internal edge mass cannot be `4`.  The saturation `∑ offDiag + mRR = 30`
with `∑ offDiag = 2 n₂ + 6 n₃` and the cross count `n₁ + 2 n₂ + 3 n₃ = 12` force `n₂ + 3 n₃ = 13`,
whence `n₁ + n₂ + 13 = 12` — a direct contradiction over `ℕ`.  No two-hub extraction is needed
(cf. `octahedron_mass_four_absurd_eighteen`). -/
theorem octahedron_mass_four_absurd_twenty (G : SimpleGraph (Fin 20))
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
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3)
    (hm4 : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4) : False := by
  classical
  obtain ⟨hsat, h13⟩ := octahedron_trace_saturate_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj hHub
    hIso hisodeg3 hshare hno2hub hT hnozero
  rw [hRcard] at hsat h13
  -- `∑ offDiag = 30 − mRR = 26` and `∑ cross = 12`.
  have hoff : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card = 26 := by omega
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
  rw [hoff] at hIII
  -- `n₂ + 3 n₃ = 13` yet `n₁ + 2 n₂ + 3 n₃ = 12`: no solution over `ℕ`.
  omega

/-- **Octahedron poor/`Z` force core (`n = 20`, HARD CRUX).**  The rigid `|Hub| = 12` octahedron
forces a good sub-configuration or a `ZPoorCutConfig`.  Branch (a): a low twin meeting two adjacent
poor hubs is a triangle.  Otherwise mass `4` is impossible (`octahedron_mass_four_absurd_twenty`),
so mass `6` makes the ordered poor–poor mass `12`; the six poor split `3 + 3` over the two low
twins and carry six cross edges.  A same-side pair of poor-degree sum `≥ 5` shares `≥ 2` common
neighbours on the size-`3` far side — a good `K₂,₃` (b).  In the residual `2`-regular (`C₆`) poor
layer a poor hub `p` carries a `Z`-slot `z₀` and no rich neighbour, and a rich hub avoiding `Z`
plus its two twins against `p`, `p`'s low twin and `z₀` is a `TwoHubConfig` (one `Z`-leaf) —
contradicting `hcut`.  Branch (c) (matched-`Z` `C₄`) never occurs since mass `4` is vacuous. -/
theorem octahedron_poor_force_b_or_c_twenty (G : SimpleGraph (Fin 20))
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
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 6)
    (hmass : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨
      (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    ((∃ g₁ g₂ t : Fin 20, g₁ ∈ Hub ∧ g₂ ∈ Hub ∧ t ∈ Iso ∧ g₁ ≠ g₂ ∧
      G.Adj g₁ g₂ ∧ G.Adj g₁ t ∧ G.Adj g₂ t) ∨
    (∃ a b c d t : Fin 20, a ∈ Hub ∧ b ∈ Hub ∧ c ∈ Hub ∧ d ∈ Hub ∧ t ∈ Iso ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a t ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b t ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c t ∧ ¬G.Adj d t ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∨
    (∃ r₁ r₂ z₁ z₂ : Fin 20, r₁ ∈ Hub ∧ r₂ ∈ Hub ∧
      z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.degree z₁ = 3 ∧ G.degree z₂ = 3 ∧
      G.Adj r₁ z₁ ∧ G.Adj z₁ z₂ ∧ G.Adj z₂ r₂ ∧ G.Adj r₂ r₁ ∧
      ¬G.Adj r₁ z₂ ∧ ¬G.Adj z₁ r₂ ∧ r₁ ≠ r₂ ∧ z₁ ≠ z₂)) ∨ ZPoorCutConfig G := by
  classical
  by_cases hcut : ZPoorCutConfig G
  · exact Or.inr hcut
  refine Or.inl ?_
  set P : Finset (Fin 20) := Hub \ R with hPdef
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  have hPsub : P ⊆ Hub := by rw [hPdef]; exact Finset.sdiff_subset
  -- **Generic `K₂,₃` extractor.**  Given two same-side poor hubs `a ≠ b` met by a low twin `t`
  -- whose poor neighbourhoods land in the size-`3` far side `B` with card sum `≥ 5`, the pair
  -- shares `≥ 2` common neighbours on `B`, giving the good `K₂,₃`.
  have key : ∀ a b : Fin 20, ∀ B : Finset (Fin 20), ∀ t : Fin 20, t ∈ Iso → a ≠ b →
      B.card = 3 → a ∈ Hub → b ∈ Hub → B ⊆ Hub → G.Adj a t → G.Adj b t → ¬G.Adj a b →
      (∀ x ∈ B, ∀ y ∈ B, ¬G.Adj x y) → (∀ g ∈ B, ¬G.Adj g t) → a ∉ B → b ∉ B →
      G.neighborFinset a ∩ P ⊆ B → G.neighborFinset b ∩ P ⊆ B →
      5 ≤ (G.neighborFinset a ∩ P).card + (G.neighborFinset b ∩ P).card →
      (∃ a' b' c d t' : Fin 20, a' ∈ Hub ∧ b' ∈ Hub ∧ c ∈ Hub ∧ d ∈ Hub ∧ t' ∈ Iso ∧
        G.Adj a' c ∧ G.Adj a' d ∧ G.Adj a' t' ∧ G.Adj b' c ∧ G.Adj b' d ∧ G.Adj b' t' ∧
        ¬G.Adj a' b' ∧ ¬G.Adj c d ∧ ¬G.Adj c t' ∧ ¬G.Adj d t' ∧
        a' ≠ b' ∧ a' ≠ c ∧ a' ≠ d ∧ b' ≠ c ∧ b' ≠ d ∧ c ≠ d) := by
    intro a b B t htIso hab hBcard haHub hbHub hBHub hat hbt hnab hBindep hBnt haB hbB hXB hYB
      hsum5
    have hunion : ((G.neighborFinset a ∩ P) ∪ (G.neighborFinset b ∩ P)).card ≤ 3 :=
      le_trans (Finset.card_le_card (Finset.union_subset hXB hYB)) hBcard.le
    have hci := Finset.card_union_add_card_inter (G.neighborFinset a ∩ P)
      (G.neighborFinset b ∩ P)
    obtain ⟨c, d, hc, hd, hcd⟩ := Finset.one_lt_card_iff.mp
      (by omega : 1 < ((G.neighborFinset a ∩ P) ∩ (G.neighborFinset b ∩ P)).card)
    rw [Finset.mem_inter] at hc hd
    have hcB : c ∈ B := hXB hc.1
    have hdB : d ∈ B := hXB hd.1
    have hac : G.Adj a c := by
      have h := hc.1; rw [Finset.mem_inter, G.mem_neighborFinset] at h; exact h.1
    have hbc : G.Adj b c := by
      have h := hc.2; rw [Finset.mem_inter, G.mem_neighborFinset] at h; exact h.1
    have had : G.Adj a d := by
      have h := hd.1; rw [Finset.mem_inter, G.mem_neighborFinset] at h; exact h.1
    have hbd : G.Adj b d := by
      have h := hd.2; rw [Finset.mem_inter, G.mem_neighborFinset] at h; exact h.1
    refine ⟨a, b, c, d, t, haHub, hbHub, hBHub hcB, hBHub hdB, htIso, hac, had,
      hat, hbc, hbd, hbt, hnab, hBindep c hcB d hdB,
      hBnt c hcB, hBnt d hdB, hab, ?_, ?_, ?_, ?_, hcd⟩
    · exact fun h => haB (h ▸ hcB)
    · exact fun h => haB (h ▸ hdB)
    · exact fun h => hbB (h ▸ hcB)
    · exact fun h => hbB (h ▸ hdB)
  -- Cross-layer counts and the two low twins.
  obtain ⟨hRZ, hPZ, hRPmass, hPPmass, hpoor3⟩ := (octahedron_poor_counts_twenty G Hub Iso R hReq
    hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero
    hRcard).resolve_right hcut
  obtain ⟨t₁, t₂, ht₁Iso, ht₂Iso, -, -, -, htsum6, htdisj, htcover⟩ :=
    octahedron_low_twin_poor_twenty G Hub Iso R hReq hiso3 hHub hIso hnozero hRcard hhigh4 htle3
  set P₁ : Finset (Fin 20) := G.neighborFinset t₁ ∩ P with hP₁def
  set P₂ : Finset (Fin 20) := G.neighborFinset t₂ ∩ P with hP₂def
  -- Branch (a): some low twin meets two adjacent poor hubs.
  by_cases hA1 : ∃ x y : Fin 20, x ∈ P₁ ∧ y ∈ P₁ ∧ G.Adj x y
  · obtain ⟨x, y, hxP₁, hyP₁, hxy⟩ := hA1
    rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset] at hxP₁ hyP₁
    exact Or.inl ⟨x, y, t₁, hPsub hxP₁.2, hPsub hyP₁.2, ht₁Iso, G.ne_of_adj hxy, hxy,
      hxP₁.1.symm, hyP₁.1.symm⟩
  by_cases hA2 : ∃ x y : Fin 20, x ∈ P₂ ∧ y ∈ P₂ ∧ G.Adj x y
  · obtain ⟨x, y, hxP₂, hyP₂, hxy⟩ := hA2
    rw [hP₂def, Finset.mem_inter, G.mem_neighborFinset] at hxP₂ hyP₂
    exact Or.inl ⟨x, y, t₂, hPsub hxP₂.2, hPsub hyP₂.2, ht₂Iso, G.ne_of_adj hxy, hxy,
      hxP₂.1.symm, hyP₂.1.symm⟩
  -- `¬a`: both low twins have independent poor neighbourhoods.
  have hindep1 : ∀ x ∈ P₁, ∀ y ∈ P₁, ¬G.Adj x y :=
    fun x hx y hy hadj => hA1 ⟨x, y, hx, hy, hadj⟩
  have hindep2 : ∀ x ∈ P₂, ∀ y ∈ P₂, ¬G.Adj x y :=
    fun x hx y hy hadj => hA2 ⟨x, y, hx, hy, hadj⟩
  -- `P = P₁ ⊔ P₂`.
  have hcoverP : P = P₁ ∪ P₂ := by
    apply Finset.Subset.antisymm
    · intro g hg
      rcases htcover g hg with h | h
      · exact Finset.mem_union_left _ (by rw [hP₁def, Finset.mem_inter]; exact ⟨h, hg⟩)
      · exact Finset.mem_union_right _ (by rw [hP₂def, Finset.mem_inter]; exact ⟨h, hg⟩)
    · exact Finset.union_subset (by rw [hP₁def]; exact Finset.inter_subset_right)
        (by rw [hP₂def]; exact Finset.inter_subset_right)
  rcases hmass with hm4 | hm6
  · -- Branch (c): rich–rich mass `4` is vacuous (parity), so this case is impossible.
    exact absurd hm4 (fun hm => octahedron_mass_four_absurd_twenty G Hub Iso R hReq hdeg4 hiso3
      hdisj hHub hIso hisodeg3 hshare hno2hub hT hnozero hRcard htle3 hm)
  · -- Rich–rich mass `6` → the six poor carry six cross edges (`3 + 3` split).
    -- The ordered poor–poor mass is `12`.
    have hPP12 : ∑ g ∈ P, (G.neighborFinset g ∩ P).card = 12 := by rw [hPPmass, hm6]
    -- Each poor in `P₁` has all its poor neighbours in `P₂` (and vice versa).
    have hsub1 : ∀ a ∈ P₁, G.neighborFinset a ∩ P ⊆ P₂ := by
      intro a ha x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      have hxP : x ∈ P := hx.2
      rw [hcoverP, Finset.mem_union] at hxP
      rcases hxP with hx1 | hx2
      · exact absurd hx.1 (hindep1 a ha x hx1)
      · exact hx2
    have hsub2 : ∀ a ∈ P₂, G.neighborFinset a ∩ P ⊆ P₁ := by
      intro a ha x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      have hxP : x ∈ P := hx.2
      rw [hcoverP, Finset.mem_union] at hxP
      rcases hxP with hx1 | hx2
      · exact hx1
      · exact absurd hx.1 (hindep2 a ha x hx2)
    -- `N(g) ∩ P = N(g) ∩ P₂` for `g ∈ P₁` (resp. `P₁` for `g ∈ P₂`).
    have he₁eq : ∑ g ∈ P₁, (G.neighborFinset g ∩ P).card
        = ∑ g ∈ P₁, (G.neighborFinset g ∩ P₂).card := by
      apply Finset.sum_congr rfl
      intro g hg
      congr 1
      apply Finset.Subset.antisymm
      · intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hsub1 g hg hx⟩
      · intro x hx
        rw [Finset.mem_inter] at hx
        refine Finset.mem_inter.mpr ⟨hx.1, ?_⟩
        have := hx.2; rw [hP₂def, Finset.mem_inter] at this; exact this.2
    have he₂eq : ∑ g ∈ P₂, (G.neighborFinset g ∩ P).card
        = ∑ g ∈ P₂, (G.neighborFinset g ∩ P₁).card := by
      apply Finset.sum_congr rfl
      intro g hg
      congr 1
      apply Finset.Subset.antisymm
      · intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hsub2 g hg hx⟩
      · intro x hx
        rw [Finset.mem_inter] at hx
        refine Finset.mem_inter.mpr ⟨hx.1, ?_⟩
        have := hx.2; rw [hP₁def, Finset.mem_inter] at this; exact this.2
    have hcc : ∑ g ∈ P₁, (G.neighborFinset g ∩ P₂).card
        = ∑ g ∈ P₂, (G.neighborFinset g ∩ P₁).card := cross_count_twenty G P₁ P₂
    -- Split the poor–poor mass over `P = P₁ ⊔ P₂`; the two halves are equal, so each is `6`.
    have hsplit : (∑ g ∈ P₁, (G.neighborFinset g ∩ P).card)
        + (∑ g ∈ P₂, (G.neighborFinset g ∩ P).card) = 12 := by
      rw [← Finset.sum_union htdisj, ← hcoverP]; exact hPP12
    have he₁ : ∑ g ∈ P₁, (G.neighborFinset g ∩ P).card = 6 := by
      have hs := hsplit; rw [he₁eq, he₂eq, hcc] at hs
      rw [he₁eq, hcc]; omega
    have he₂ : ∑ g ∈ P₂, (G.neighborFinset g ∩ P).card = 6 := by
      have hs := hsplit; rw [he₁eq, he₂eq, hcc] at hs
      rw [he₂eq]; omega
    -- Cards: each poor side has `≤ 3` (twin meets `≤ 3` hubs); sum `6` ⟹ split `3 + 3`.
    have hP₁Hub : P₁ ⊆ Hub := by rw [hP₁def]; exact Finset.inter_subset_right.trans hPsub
    have hP₂Hub : P₂ ⊆ Hub := by rw [hP₂def]; exact Finset.inter_subset_right.trans hPsub
    have hP₁le3 : P₁.card ≤ 3 := by
      have hsub : P₁ ⊆ G.neighborFinset t₁ ∩ Hub := by
        rw [hP₁def]; exact Finset.inter_subset_inter (Finset.Subset.refl _) hPsub
      calc P₁.card ≤ (G.neighborFinset t₁ ∩ Hub).card := Finset.card_le_card hsub
        _ = 3 := hiso3 t₁ ht₁Iso
    have hP₂le3 : P₂.card ≤ 3 := by
      have hsub : P₂ ⊆ G.neighborFinset t₂ ∩ Hub := by
        rw [hP₂def]; exact Finset.inter_subset_inter (Finset.Subset.refl _) hPsub
      calc P₂.card ≤ (G.neighborFinset t₂ ∩ Hub).card := Finset.card_le_card hsub
        _ = 3 := hiso3 t₂ ht₂Iso
    have hsum6' : P₁.card + P₂.card = 6 := htsum6
    have hc₁ : P₁.card = 3 := by omega
    have hc₂ : P₂.card = 3 := by omega
    -- Twin-side adjacency and big-side non-adjacency facts.
    have hSt1 : ∀ g ∈ P₁, G.Adj g t₁ := by
      intro g hg; rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset] at hg; exact hg.1.symm
    have hSt2 : ∀ g ∈ P₂, G.Adj g t₂ := by
      intro g hg; rw [hP₂def, Finset.mem_inter, G.mem_neighborFinset] at hg; exact hg.1.symm
    have hBnt1 : ∀ g ∈ P₂, ¬G.Adj g t₁ := by
      intro g hg hadj
      have hgP₁ : g ∈ P₁ := by
        rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset]
        refine ⟨hadj.symm, ?_⟩
        rw [hP₂def, Finset.mem_inter] at hg; exact hg.2
      exact Finset.disjoint_left.mp htdisj hgP₁ hg
    have hBnt2 : ∀ g ∈ P₁, ¬G.Adj g t₂ := by
      intro g hg hadj
      have hgP₂ : g ∈ P₂ := by
        rw [hP₂def, Finset.mem_inter, G.mem_neighborFinset]
        refine ⟨hadj.symm, ?_⟩
        rw [hP₁def, Finset.mem_inter] at hg; exact hg.2
      exact Finset.disjoint_left.mp htdisj hg hgP₂
    -- Heavy same-side pair (poor-degree sum `≥ 5`) → good `K₂,₃` (branch (b)).
    by_cases hheavy₁ : ∃ a ∈ P₁, ∃ b ∈ P₁, a ≠ b ∧
        5 ≤ (G.neighborFinset a ∩ P).card + (G.neighborFinset b ∩ P).card
    · obtain ⟨a, ha, b, hb, hab, hsum⟩ := hheavy₁
      exact Or.inr (Or.inl (key a b P₂ t₁ ht₁Iso hab hc₂ (hP₁Hub ha) (hP₁Hub hb) hP₂Hub
        (hSt1 a ha) (hSt1 b hb) (hindep1 a ha b hb) hindep2 hBnt1
        (Finset.disjoint_left.mp htdisj ha) (Finset.disjoint_left.mp htdisj hb)
        (hsub1 a ha) (hsub1 b hb) hsum))
    by_cases hheavy₂ : ∃ a ∈ P₂, ∃ b ∈ P₂, a ≠ b ∧
        5 ≤ (G.neighborFinset a ∩ P).card + (G.neighborFinset b ∩ P).card
    · obtain ⟨a, ha, b, hb, hab, hsum⟩ := hheavy₂
      exact Or.inr (Or.inl (key a b P₁ t₂ ht₂Iso hab hc₁ (hP₂Hub ha) (hP₂Hub hb) hP₁Hub
        (hSt2 a ha) (hSt2 b hb) (hindep2 a ha b hb) hindep1 hBnt2
        (Finset.disjoint_right.mp htdisj ha) (Finset.disjoint_right.mp htdisj hb)
        (hsub2 a ha) (hsub2 b hb) hsum))
    -- Residual: no heavy pair, so the poor layer is `2`-regular (the `C₆` tie); extract a
    -- `TwoHubConfig` through the poor `Z`-slot, contradicting `hcut`.
    exfalso
    push Not at hheavy₁ hheavy₂
    -- Every poor hub has exactly two poor neighbours.
    have hside : ∀ Q : Finset (Fin 20), Q.card = 3 →
        (∑ g ∈ Q, (G.neighborFinset g ∩ P).card) = 6 →
        (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b →
          (G.neighborFinset a ∩ P).card + (G.neighborFinset b ∩ P).card < 5) →
        ∀ g ∈ Q, (G.neighborFinset g ∩ P).card = 2 := by
      intro Q hQ3 hQsum hQpair g hg
      obtain ⟨x, y, z, hxy, hxz, hyz, hQeq⟩ := Finset.card_eq_three.mp hQ3
      subst hQeq
      rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
        Finset.sum_singleton] at hQsum
      have hxm : x ∈ ({x, y, z} : Finset (Fin 20)) := by simp
      have hym : y ∈ ({x, y, z} : Finset (Fin 20)) := by simp
      have hzm : z ∈ ({x, y, z} : Finset (Fin 20)) := by simp
      have h1 := hQpair x hxm y hym hxy
      have h2 := hQpair x hxm z hzm hxz
      have h3 := hQpair y hym z hzm hyz
      rcases Finset.mem_insert.mp hg with rfl | hg'
      · omega
      rcases Finset.mem_insert.mp hg' with rfl | hg''
      · omega
      rw [Finset.mem_singleton] at hg''
      subst hg''
      omega
    have hall2 : ∀ g ∈ P, (G.neighborFinset g ∩ P).card = 2 := by
      intro g hg
      have hg' : g ∈ P₁ ∪ P₂ := by rw [← hcoverP]; exact hg
      rcases Finset.mem_union.mp hg' with hg₁ | hg₂
      · exact hside P₁ hc₁ he₁ hheavy₁ g hg₁
      · exact hside P₂ hc₂ he₂ hheavy₂ g hg₂
    set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
    -- Some poor hub `p` carries a `Z`-slot; it then has no rich neighbour.
    obtain ⟨p, hpP, hpZ1⟩ : ∃ p ∈ P, 1 ≤ (G.neighborFinset p ∩ Z).card := by
      by_contra h
      push Not at h
      have hzero : ∀ g ∈ P, (G.neighborFinset g ∩ Z).card = 0 := by
        intro g hg
        have := h g hg
        omega
      rw [Finset.sum_eq_zero hzero] at hPZ
      omega
    have hpHub : p ∈ Hub := hPsub hpP
    have hpnotR : p ∉ R := by
      have h := hpP
      rw [hPdef, Finset.mem_sdiff] at h
      exact h.2
    have hp2 : (G.neighborFinset p ∩ P).card = 2 := hall2 p hpP
    have hpsplit := hpoor3 p hpP
    rw [← hPdef] at hpsplit
    have hpR0 : (G.neighborFinset p ∩ R).card = 0 := by omega
    obtain ⟨z₀, hz₀mem⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset p ∩ Z).card)
    rw [Finset.mem_inter] at hz₀mem
    have hpz₀ : G.Adj p z₀ := (G.mem_neighborFinset _ _).mp hz₀mem.1
    have hz₀Z : z₀ ∈ Z := hz₀mem.2
    -- `z₀` has degree `3` (the `Z`-vertex profile) and is neither a hub nor a twin.
    obtain ⟨-, -, hz₀deg⟩ := z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak z₀ hz₀Z
    have hz₀nHub : z₀ ∉ Hub := by
      have h := hz₀Z
      rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at h
      exact h.2.1
    have hz₀nIso : z₀ ∉ Iso := by
      have h := hz₀Z
      rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at h
      exact h.2.2
    -- Twin neighbourhoods lie in `Hub`.
    have htwinHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
      intro t ht
      have hcard3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
      have hdt : (G.neighborFinset t).card = 3 := by
        rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t ht
      have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard3, hdt])
      rw [← heq]; exact Finset.inter_subset_right
    -- A `3`-poor low twin has no rich neighbour.
    have hlowR : ∀ t : Fin 20, t ∈ Iso → (G.neighborFinset t ∩ P).card = 3 →
        ∀ r' ∈ R, ¬G.Adj t r' := by
      intro t ht h3 r' hr' hadj
      have hHub3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
      have hsubPH : G.neighborFinset t ∩ P ⊆ G.neighborFinset t ∩ Hub :=
        Finset.inter_subset_inter (Finset.Subset.refl _) hPsub
      have heq : G.neighborFinset t ∩ P = G.neighborFinset t ∩ Hub :=
        Finset.eq_of_subset_of_card_le hsubPH (by omega)
      have hr'mem : r' ∈ G.neighborFinset t ∩ Hub := by
        rw [Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨hadj, hRsub hr'⟩
      rw [← heq, Finset.mem_inter] at hr'mem
      have hr'P := hr'mem.2
      rw [hPdef, Finset.mem_sdiff] at hr'P
      exact hr'P.2 hr'
    -- Every rich hub has exactly two twins (`∑_R isoDeg = 12`, each `≥ 2`).
    have hisoR12 : ∑ r' ∈ R, (G.neighborFinset r' ∩ Iso).card = 12 := by
      have h := (octahedron_trace_saturate_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso
        hisodeg3 hshare hno2hub hT hnozero).2
      rw [hRcard] at h
      omega
    have hrich2 : ∀ r' ∈ R, (G.neighborFinset r' ∩ Iso).card = 2 := by
      intro r' hr'
      have hge2 : ∀ w ∈ R, 2 ≤ (G.neighborFinset w ∩ Iso).card := by
        intro w hw
        rw [hReq, Finset.mem_filter] at hw
        exact hw.2
      have hae := Finset.add_sum_erase R (fun w => (G.neighborFinset w ∩ Iso).card) hr'
      have herase : 10 ≤ ∑ w ∈ R.erase r', (G.neighborFinset w ∩ Iso).card := by
        have hcardE : (R.erase r').card = 5 := by rw [Finset.card_erase_of_mem hr', hRcard]
        calc (10 : ℕ) = ∑ _w ∈ R.erase r', 2 := by simp [Finset.sum_const, hcardE]
          _ ≤ ∑ w ∈ R.erase r', (G.neighborFinset w ∩ Iso).card :=
              Finset.sum_le_sum (fun w hw => hge2 w (Finset.mem_of_mem_erase hw))
      rw [hisoR12] at hae
      have h2 := hge2 r' hr'
      omega
    -- A rich hub avoiding `Z` (only two of the six rich carry the two rich `Z`-incidences).
    obtain ⟨r, hrR, hrZ0⟩ : ∃ r ∈ R, (G.neighborFinset r ∩ Z).card = 0 := by
      by_contra h
      push Not at h
      have hge1 : ∀ w ∈ R, 1 ≤ (G.neighborFinset w ∩ Z).card := by
        intro w hw
        have := h w hw
        omega
      have h6 : 6 ≤ ∑ w ∈ R, (G.neighborFinset w ∩ Z).card := by
        calc (6 : ℕ) = ∑ _w ∈ R, 1 := by simp [Finset.sum_const, hRcard]
          _ ≤ ∑ w ∈ R, (G.neighborFinset w ∩ Z).card := Finset.sum_le_sum hge1
      rw [hRZ] at h6
      omega
    obtain ⟨a, b, habne, habeq⟩ := Finset.card_eq_two.mp (hrich2 r hrR)
    have hamem : a ∈ G.neighborFinset r ∩ Iso := by
      rw [habeq]; exact Finset.mem_insert_self _ _
    have hbmem : b ∈ G.neighborFinset r ∩ Iso := by
      rw [habeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have haIso : a ∈ Iso := (Finset.mem_inter.mp hamem).2
    have hbIso : b ∈ Iso := (Finset.mem_inter.mp hbmem).2
    have hra : G.Adj r a := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hamem).1
    have hrb : G.Adj r b := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hbmem).1
    have hrHub : r ∈ Hub := hRsub hrR
    -- Assemble the two-hub configuration `⟨r; a, b | p; c, z₀⟩` where `c` is `p`'s low twin.
    have hassemble : ∀ c : Fin 20, c ∈ Iso → G.Adj c p →
        (G.neighborFinset c ∩ P).card = 3 → False := by
      intro c hcIso hcp hc3
      -- `p` meets exactly one twin.
      have hpoor1p : (G.neighborFinset p ∩ Iso).card = 1 := by
        have hge1 : 1 ≤ (G.neighborFinset p ∩ Iso).card := hnozero p hpHub
        have hle1 : (G.neighborFinset p ∩ Iso).card ≤ 1 := by
          by_contra hcon
          exact hpnotR (by rw [hReq, Finset.mem_filter]; exact ⟨hpHub, by omega⟩)
        omega
      -- Non-adjacencies.
      have hnrp : ¬G.Adj r p := by
        intro hadj
        have hmem : r ∈ G.neighborFinset p ∩ R := by
          rw [Finset.mem_inter, G.mem_neighborFinset]
          exact ⟨hadj.symm, hrR⟩
        rw [Finset.card_eq_zero] at hpR0
        rw [hpR0] at hmem
        exact absurd hmem (Finset.notMem_empty r)
      have hnrc : ¬G.Adj r c := fun hadj => hlowR c hcIso hc3 r hrR hadj.symm
      have hnrz : ¬G.Adj r z₀ := by
        intro hadj
        have hmem : z₀ ∈ G.neighborFinset r ∩ Z := by
          rw [Finset.mem_inter, G.mem_neighborFinset]
          exact ⟨hadj, hz₀Z⟩
        rw [Finset.card_eq_zero] at hrZ0
        rw [hrZ0] at hmem
        exact absurd hmem (Finset.notMem_empty z₀)
      have hnap : ¬G.Adj a p := by
        intro hadj
        have ha' : a ∈ G.neighborFinset p ∩ Iso := by
          rw [Finset.mem_inter, G.mem_neighborFinset]
          exact ⟨hadj.symm, haIso⟩
        have hc' : c ∈ G.neighborFinset p ∩ Iso := by
          rw [Finset.mem_inter, G.mem_neighborFinset]
          exact ⟨hcp.symm, hcIso⟩
        have hacq : a = c := Finset.card_le_one.mp (le_of_eq hpoor1p) a ha' c hc'
        exact hlowR c hcIso hc3 r hrR (hacq ▸ hra.symm)
      have hnbp : ¬G.Adj b p := by
        intro hadj
        have hb' : b ∈ G.neighborFinset p ∩ Iso := by
          rw [Finset.mem_inter, G.mem_neighborFinset]
          exact ⟨hadj.symm, hbIso⟩
        have hc' : c ∈ G.neighborFinset p ∩ Iso := by
          rw [Finset.mem_inter, G.mem_neighborFinset]
          exact ⟨hcp.symm, hcIso⟩
        have hbcq : b = c := Finset.card_le_one.mp (le_of_eq hpoor1p) b hb' c hc'
        exact hlowR c hcIso hc3 r hrR (hbcq ▸ hrb.symm)
      have hnac : ¬G.Adj a c := fun hadj => Finset.disjoint_left.mp hdisj
        (htwinHub a haIso ((G.mem_neighborFinset _ _).mpr hadj)) hcIso
      have hnaz : ¬G.Adj a z₀ := fun hadj =>
        hz₀nHub (htwinHub a haIso ((G.mem_neighborFinset _ _).mpr hadj))
      have hnbc : ¬G.Adj b c := fun hadj => Finset.disjoint_left.mp hdisj
        (htwinHub b hbIso ((G.mem_neighborFinset _ _).mpr hadj)) hcIso
      have hnbz : ¬G.Adj b z₀ := fun hadj =>
        hz₀nHub (htwinHub b hbIso ((G.mem_neighborFinset _ _).mpr hadj))
      -- Distinctness.
      have hrp' : r ≠ p := fun he => hpnotR (he ▸ hrR)
      have hra' : r ≠ a := fun he => Finset.disjoint_left.mp hdisj hrHub (he ▸ haIso)
      have hrb' : r ≠ b := fun he => Finset.disjoint_left.mp hdisj hrHub (he ▸ hbIso)
      have hrc' : r ≠ c := fun he => Finset.disjoint_left.mp hdisj hrHub (he ▸ hcIso)
      have hrz' : r ≠ z₀ := fun he => hz₀nHub (he ▸ hrHub)
      have hpa' : p ≠ a := fun he => Finset.disjoint_left.mp hdisj hpHub (he ▸ haIso)
      have hpb' : p ≠ b := fun he => Finset.disjoint_left.mp hdisj hpHub (he ▸ hbIso)
      have hpc' : p ≠ c := fun he => Finset.disjoint_left.mp hdisj hpHub (he ▸ hcIso)
      have hpz' : p ≠ z₀ := fun he => hz₀nHub (he ▸ hpHub)
      have hac' : a ≠ c := fun he => hlowR c hcIso hc3 r hrR (he ▸ hra.symm)
      have haz' : a ≠ z₀ := fun he => hz₀nIso (he ▸ haIso)
      have hbc' : b ≠ c := fun he => hlowR c hcIso hc3 r hrR (he ▸ hrb.symm)
      have hbz' : b ≠ z₀ := fun he => hz₀nIso (he ▸ hbIso)
      have hcz' : c ≠ z₀ := fun he => hz₀nIso (he ▸ hcIso)
      exact hcut (Or.inl ⟨r, p, a, b, c, z₀, hdeg4 r hrHub, hdeg4 p hpHub, hisodeg3 a haIso,
        hisodeg3 b hbIso, hisodeg3 c hcIso, hz₀deg, hra.symm, hrb.symm, hcp, hpz₀.symm,
        hnrp, hnrc, hnrz, hnap, hnac, hnaz, hnbp, hnbc, hnbz,
        hrp', hra', hrb', hrc', hrz', hpa', hpb', hpc', hpz', habne, hac', haz', hbc', hbz',
        hcz'⟩)
    -- `p`'s low twin: `htcover` sends `p` to `t₁` or `t₂`, each of poor degree three.
    rcases htcover p hpP with hpt | hpt
    · have h3 : (G.neighborFinset t₁ ∩ P).card = 3 := by rw [← hP₁def]; exact hc₁
      exact hassemble t₁ ht₁Iso ((G.mem_neighborFinset _ _).mp hpt) h3
    · have h3 : (G.neighborFinset t₂ ∩ P).card = 3 := by rw [← hP₂def]; exact hc₂
      exact hassemble t₂ ht₂Iso ((G.mem_neighborFinset _ _).mp hpt) h3

end N20

end ACMax
