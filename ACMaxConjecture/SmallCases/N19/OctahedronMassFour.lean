import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.RichZdeg
import ACMaxConjecture.SmallCases.N19.OctahedronStruct
import ACMaxConjecture.SmallCases.N19.OctahedronForce
import ACMaxConjecture.SmallCases.N19.OctahedronPoorForce2

/-!
# Octahedron mass-`4` absurdity and three-way force (`n = 19`, `|Hub| = 11`, HARD CRUX core)

This file carries the genuinely-new `|Hub| = 11` content behind
`octahedron_poor_layer_force_nineteen`.  Over the rigid octahedron (six rich hubs `R`, **five** poor
hubs `P = Hub \ R`, four high `M`-isolated twins, two low twins, two adjacent `M`-edge endpoints
`Z = univ \ (Hub ∪ Iso)`) the rich-internal mass `mRR ∈ {4, 6}` is decided and one of three good
sub-configurations is forced.

* `octahedron_mass_four_absurd_nineteen` — the rich-internal mass `4` is impossible **by parity**.
  The trace saturation `(∑_t offDiag) + mRR = |R|² − |R| = 30` with `∑_t |N t ∩ R| = 13` forces the
  twin rich-degree profile `n₀ + n₁ + n₂ + n₃ = 6`, `n₁ + 2 n₂ + 3 n₃ = 13`, `2 n₂ + 6 n₃ = 26`;
  this gives `n₁ = n₂ = 0` and the non-integer `3 n₃ = 13`, contradiction.  This is a SIMPLIFICATION
  over `n = 18`, where mass `4` needed the elaborate two-hub extraction
  `octahedron_mass_four_absurd_eighteen` (here the `30 = 3·10` saturation has integer slack only at
  `mRR = 6`).
* `octahedron_poor_force_b_or_c_nineteen` — the three-way force.  Branch (a): a low twin meeting two
  adjacent poor hubs yields a good triangle `4 + 4 + 3 = 11`.  Otherwise mass `4` is killed
  (`octahedron_mass_four_absurd_nineteen`) and mass `6` makes the ordered poor–poor mass `10`, so the
  five poor (split `2 + 3` over the two low twins) carry exactly five cross edges; the two poor on the
  size-`2` low twin share `≥ 2` common neighbours among the size-`3` side (`5 − 3 = 2`), giving a good
  `K₂,₃` of degree sum `4 + 4 + 4 + 4 + 3 = 19`.  (Branch (c), the matched-`Z` rich `C₄`, is vacuous
  here precisely because mass `4` never occurs.)
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Mass-`4` octahedron is impossible (LEAF, `n = 19`, parity).**  In the rigid `|Hub| = 11`
octahedron the ordered rich-internal edge mass cannot be `4`.  The saturation `∑ offDiag + mRR = 30`
with `∑ offDiag = 2 n₂ + 6 n₃` and the cross count `n₁ + 2 n₂ + 3 n₃ = 13` force `n₁ = n₂ = 0` and the
non-integer `3 n₃ = 13` — a direct contradiction.  No two-hub extraction is needed (cf.
`octahedron_mass_four_absurd_eighteen`). -/
theorem octahedron_mass_four_absurd_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso R : Finset (Fin 19))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3)
    (hm4 : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4) : False := by
  classical
  obtain ⟨hsat, h13⟩ := octahedron_trace_saturate_nineteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub
    hIso hisodeg3 hshare hno2hub hT hnozero
  rw [hRcard] at hsat h13
  -- `∑ offDiag = 30 − mRR = 26` and `∑ cross = 13`.
  have hoff : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card = 26 := by omega
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 13 := by
    rw [cross_count_nineteen G Iso R]; exact h13
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
  -- `n₁ + n₂ = 0` and `3 n₃ = 13`: no integer solution.
  omega

/-- **Octahedron poor/`Z` three-way force core (`n = 19`, HARD CRUX).**  The rigid `|Hub| = 11`
octahedron forces one of three good sub-configurations.  Branch (a): a low twin meeting two adjacent
poor hubs is a triangle.  Otherwise mass `4` is impossible (`octahedron_mass_four_absurd_nineteen`),
so mass `6` makes the ordered poor–poor mass `10`; the five poor split `2 + 3` over the two low twins
and carry five cross edges, so the size-`2` side's two poor share `≥ 2` common neighbours on the
size-`3` side — a good `K₂,₃` (b).  Branch (c) (matched-`Z` `C₄`) never occurs since mass `4` is
vacuous. -/
theorem octahedron_poor_force_b_or_c_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso R : Finset (Fin 19))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v)
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
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 6)
    (hmass : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨
      (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    ((∃ g₁ g₂ t : Fin 19, g₁ ∈ Hub ∧ g₂ ∈ Hub ∧ t ∈ Iso ∧ g₁ ≠ g₂ ∧
      G.Adj g₁ g₂ ∧ G.Adj g₁ t ∧ G.Adj g₂ t) ∨
    (∃ a b c d t : Fin 19, a ∈ Hub ∧ b ∈ Hub ∧ c ∈ Hub ∧ d ∈ Hub ∧ t ∈ Iso ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a t ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b t ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c t ∧ ¬G.Adj d t ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∨
    (∃ r₁ r₂ z₁ z₂ : Fin 19, r₁ ∈ Hub ∧ r₂ ∈ Hub ∧
      z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
      z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
      G.degree z₁ = 3 ∧ G.degree z₂ = 3 ∧
      G.Adj r₁ z₁ ∧ G.Adj z₁ z₂ ∧ G.Adj z₂ r₂ ∧ G.Adj r₂ r₁ ∧
      ¬G.Adj r₁ z₂ ∧ ¬G.Adj z₁ r₂ ∧ r₁ ≠ r₂ ∧ z₁ ≠ z₂)) ∨ ZPoorCutConfig G := by
  classical
  by_cases hcut : ZPoorCutConfig G
  · exact Or.inr hcut
  refine Or.inl ?_
  set P : Finset (Fin 19) := Hub \ R with hPdef
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  have hPsub : P ⊆ Hub := by rw [hPdef]; exact Finset.sdiff_subset
  -- **Generic `K₂,₃` extractor.**  Given a size-`2` poor side `S` met by a low twin `t` and a size-`3`
  -- poor side `B`, with the five-edge bipartite incidence `∑_{S} |N ∩ P| = 5`, the two poor of `S`
  -- share `≥ 2` common neighbours on `B`, giving the good `K₂,₃`.
  have key : ∀ S B : Finset (Fin 19), ∀ t : Fin 19, t ∈ Iso → S.card = 2 → B.card = 3 →
      S ⊆ Hub → B ⊆ Hub → (∀ g ∈ S, G.Adj g t) → (∀ g ∈ B, ¬G.Adj g t) →
      (∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y) → (∀ x ∈ B, ∀ y ∈ B, ¬G.Adj x y) →
      Disjoint S B → (∀ g ∈ S, G.neighborFinset g ∩ P ⊆ B) →
      (∑ g ∈ S, (G.neighborFinset g ∩ P).card) = 5 →
      (∃ a b c d t' : Fin 19, a ∈ Hub ∧ b ∈ Hub ∧ c ∈ Hub ∧ d ∈ Hub ∧ t' ∈ Iso ∧
        G.Adj a c ∧ G.Adj a d ∧ G.Adj a t' ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b t' ∧
        ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c t' ∧ ¬G.Adj d t' ∧
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) := by
    intro S B t htIso hScard hBcard hSHub hBHub hSt hBnt hSindep hBindep hSBdisj hSsubB hSsum5
    obtain ⟨a, b, hab, hSeq⟩ := Finset.card_eq_two.mp hScard
    have haS : a ∈ S := by rw [hSeq]; exact Finset.mem_insert_self _ _
    have hbS : b ∈ S := by rw [hSeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hXB : G.neighborFinset a ∩ P ⊆ B := hSsubB a haS
    have hYB : G.neighborFinset b ∩ P ⊆ B := hSsubB b hbS
    have hsum5 : (G.neighborFinset a ∩ P).card + (G.neighborFinset b ∩ P).card = 5 := by
      have h := hSsum5; rw [hSeq, Finset.sum_pair hab] at h; exact h
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
    refine ⟨a, b, c, d, t, hSHub haS, hSHub hbS, hBHub hcB, hBHub hdB, htIso, hac, had,
      hSt a haS, hbc, hbd, hSt b hbS, hSindep a haS b hbS, hBindep c hcB d hdB,
      hBnt c hcB, hBnt d hdB, hab, ?_, ?_, ?_, ?_, hcd⟩
    · exact fun h => Finset.disjoint_left.mp hSBdisj haS (h ▸ hcB)
    · exact fun h => Finset.disjoint_left.mp hSBdisj haS (h ▸ hdB)
    · exact fun h => Finset.disjoint_left.mp hSBdisj hbS (h ▸ hcB)
    · exact fun h => Finset.disjoint_left.mp hSBdisj hbS (h ▸ hdB)
  -- Cross-layer counts and the two low twins.
  obtain ⟨hRZ, hPZ, hRPmass, hPPmass, hpoor3⟩ := (octahedron_poor_counts_nineteen G Hub Iso R hReq
    hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero
    hRcard).resolve_right hcut
  obtain ⟨t₁, t₂, ht₁Iso, ht₂Iso, htne, ht₁pos, ht₂pos, htsum5, htdisj, htcover⟩ :=
    octahedron_low_twin_poor_nineteen G Hub Iso R hReq hiso3 hHub hIso hnozero hRcard hhigh4 htle3
  set P₁ : Finset (Fin 19) := G.neighborFinset t₁ ∩ P with hP₁def
  set P₂ : Finset (Fin 19) := G.neighborFinset t₂ ∩ P with hP₂def
  -- Branch (a): some low twin meets two adjacent poor hubs.
  by_cases hA1 : ∃ x y : Fin 19, x ∈ P₁ ∧ y ∈ P₁ ∧ G.Adj x y
  · obtain ⟨x, y, hxP₁, hyP₁, hxy⟩ := hA1
    rw [hP₁def, Finset.mem_inter, G.mem_neighborFinset] at hxP₁ hyP₁
    exact Or.inl ⟨x, y, t₁, hPsub hxP₁.2, hPsub hyP₁.2, ht₁Iso, G.ne_of_adj hxy, hxy,
      hxP₁.1.symm, hyP₁.1.symm⟩
  by_cases hA2 : ∃ x y : Fin 19, x ∈ P₂ ∧ y ∈ P₂ ∧ G.Adj x y
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
    exact absurd hm4 (fun hm => octahedron_mass_four_absurd_nineteen G Hub Iso R hReq hdeg4 hiso3
      hdisj hHub hIso hisodeg3 hshare hno2hub hT hnozero hRcard htle3 hm)
  · -- Branch (b): rich–rich mass `6` → five poor carry five cross edges → `K₂,₃`.
    right; left
    -- The ordered poor–poor mass is `10`.
    have hPP10 : ∑ g ∈ P, (G.neighborFinset g ∩ P).card = 10 := by rw [hPPmass, hm6]
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
        = ∑ g ∈ P₂, (G.neighborFinset g ∩ P₁).card := cross_count_nineteen G P₁ P₂
    -- Split the poor–poor mass over `P = P₁ ⊔ P₂`; the two halves are equal, so each is `5`.
    have hsplit : (∑ g ∈ P₁, (G.neighborFinset g ∩ P).card)
        + (∑ g ∈ P₂, (G.neighborFinset g ∩ P).card) = 10 := by
      rw [← Finset.sum_union htdisj, ← hcoverP]; exact hPP10
    have he₁ : ∑ g ∈ P₁, (G.neighborFinset g ∩ P).card = 5 := by
      have hs := hsplit; rw [he₁eq, he₂eq, hcc] at hs
      rw [he₁eq, hcc]; omega
    have he₂ : ∑ g ∈ P₂, (G.neighborFinset g ∩ P).card = 5 := by
      have hs := hsplit; rw [he₁eq, he₂eq, hcc] at hs
      rw [he₂eq]; omega
    -- Cards: each poor side has `≤ 3` (twin meets `≤ 3` hubs) and `≥ 1`; sum `5` ⟹ split `2 + 3`.
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
    have hsum5' : P₁.card + P₂.card = 5 := htsum5
    have h1pos : 1 ≤ P₁.card := ht₁pos
    have h2pos : 1 ≤ P₂.card := ht₂pos
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
    -- The `2 + 3` split: feed the size-`2` side to the `K₂,₃` extractor.
    rcases (show (P₁.card = 2 ∧ P₂.card = 3) ∨ (P₁.card = 3 ∧ P₂.card = 2) by omega)
      with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
    · exact key P₁ P₂ t₁ ht₁Iso hc1 hc2 hP₁Hub hP₂Hub hSt1 hBnt1 hindep1 hindep2 htdisj hsub1 he₁
    · exact key P₂ P₁ t₂ ht₂Iso hc2 hc1 hP₂Hub hP₁Hub hSt2 hBnt2 hindep2 hindep1 htdisj.symm hsub2 he₂

end N19

end ACMax
