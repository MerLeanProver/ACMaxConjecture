import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.OctahedronForce
import ACMaxConjecture.SmallCases.N19.OctahedronMassFour
import ACMaxConjecture.SmallCases.N19.OctahedronPoorForce2
import ACMaxConjecture.SmallCases.N19.OctaMassNe8
import ACMaxConjecture.SmallCases.N19.OctaMassNoZero

/-!
# Octahedron mass-exclusion handshake (`n = 19`, `|Hub| = 11`, `(11, 6, 44)`)

This file isolates the **mass-exclusion handshake** for the clean `(11, 6, 44)` octahedron — the
genuinely-new `|Hub| = 11` content that pins the rich-internal ordered edge mass
`mRR = ∑_{r∈R} |N r ∩ R|` to `{4, 6}` (and simultaneously yields the four-high-twins input
`hhigh4`).  It is the analog of the `n = 18` `octahedron_mass_excl_eighteen`, but here the
exclusion of `mRR = 8` cannot be done by the bare handshake `mRR ≤ 9` alone (`n = 18` had
`mRR ≤ 7`).  Instead the handshake is *combined* with the trace saturation to pin the twin
rich-degree profile.

## The recomputed handshake for `(11, 6, 44)`

With `|Hub| = 11`, `R + P = 11`, `|Iso| = 6`, `|Z| = 2` and `R.card = 6` we have `P.card = 5`.
Every poor hub has iso-degree exactly `1` (`hnozero` plus the `< 2` poor definition), so the rich
iso-incidence sum is

  `S = ∑_{r∈R} |N r ∩ Iso| = 18 − |P| = 18 − 5 = 13   (= 7 + |R|)`.

The degree sum over the six rich hubs (`6·4 = 24`) splits over the partition `R ⊔ P ⊔ Iso ⊔ Z` as

  `mRR + E(R, P) + S + E(R, Z) = 24`,  with `S = 13`, `E(R, Z) = 2`  ⟹  `mRR + E(R, P) = 9`

(this is exactly `octahedron_poor_counts_nineteen`'s `hRPmass`).  Since `E(R, P) ≥ 0` this gives
`mRR ≤ 9`.

## The trace saturation pins `mRR ∈ {6, 8}` and `n₃`

Writing `n_k` for the number of `M`-isolated twins meeting exactly `k` rich hubs, the saturation
`(∑_t |N t ∩ R|·(|N t ∩ R| − 1)) + mRR = |R|² − |R| = 30` with the cross count
`∑_t |N t ∩ R| = S = 13` gives the linear system

  `n₀ + n₁ + n₂ + n₃ = 6`,   `n₁ + 2 n₂ + 3 n₃ = 13`,   `2 n₂ + 6 n₃ = 30 − mRR`.

Over `ℕ` with `mRR ≤ 9` the **only** solutions are

  `mRR = 6 : (n₃, n₂, n₁, n₀) = (4, 0, 1, 1)`  and  `mRR = 8 : (n₃, n₂, n₁, n₀) = (3, 2, 0, 1)`

(`mRR = 4` is the non-integer `3 n₃ = 13`, excluded; `mRR ∈ {10, 12, 14}` violate `mRR ≤ 9`).  At
`mRR = 6` we get `n₃ = 4` (the four high twins `hhigh4`); at `mRR = 8` we get `n₃ = 3` (one short of
`hhigh4`).  Hence the dichotomy below: either the good mass `mRR ∈ {4, 6}` with four high twins, or
the residual `mRR = 8`.

`octahedron_mass_reduce_nineteen` is **axiom-clean**: it derives this dichotomy from
`octahedron_trace_saturate_nineteen` (LEAF) and `octahedron_poor_counts_nineteen` (the cross-layer
handshake), via `omega`.  The remaining `mRR = 8` exclusion (equivalently the four-high-twins input)
is the residual the surrounding octahedron poor-layout layer must kill.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Octahedron mass-exclusion dichotomy (LEAF, `n = 19`, `(11, 6, 44)`).**  In the clean no-two-hub
`|Hub| = 11` octahedron with `R.card = 6` and `hnozero`, the rich-internal ordered mass
`mRR = ∑_{r∈R} |N r ∩ R|` together with the four-high-twins count is pinned:

* either `mRR ∈ {4, 6}` **and** at least four `M`-isolated twins meet all three of their hubs inside
  `R` (the good octahedron — exactly the bundle `octahedron_poor_layer_force_nineteen` consumes),
* or `mRR = 8` (the residual `n₃ = 3` profile).

The proof is the handshake `mRR + E(R, P) = 9` (`octahedron_poor_counts_nineteen`) giving `mRR ≤ 9`,
combined with the trace saturation `∑_t |N t ∩ R|·(|N t ∩ R| − 1) + mRR = 30` and the cross count
`∑_t |N t ∩ R| = 13` (`octahedron_trace_saturate_nineteen`), discharged by `omega`. -/
theorem octahedron_mass_reduce_nineteen (G : SimpleGraph (Fin 19))
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
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3)
    (hcut : ¬ ZPoorCutConfig G) :
    (((∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨
        (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6) ∧
      4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    ∨ (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 8 := by
  classical
  -- Trace saturation: `∑offDiag + mRR = 30` and the rich iso-incidence sum `= 13`.
  obtain ⟨hsat, h13⟩ := octahedron_trace_saturate_nineteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub
    hIso hisodeg3 hshare hno2hub hT hnozero
  rw [hRcard] at hsat h13
  -- Cross count: `∑_t |N t ∩ R| = ∑_r |N r ∩ Iso| = 13`.
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 13 := by
    rw [cross_count_nineteen G Iso R]; exact h13
  -- Handshake: `E(R, P) + mRR = 9`, hence `mRR ≤ 9`.
  obtain ⟨_, _, hRPmass, _, _⟩ := (octahedron_poor_counts_nineteen G Hub Iso R hReq hdeg4 hiso3
    hdisj hHub hIso hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard).resolve_right
    hcut
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
  rw [hIII] at hsat
  -- `mRR = ∑_r |N r ∩ R|`.  From `hRPmass` (`E(R,P) + mRR = 9`) we get `mRR ≤ 9`; with the trace
  -- system this forces `mRR ∈ {6, 8}` and pins `n₃` (`= 4` at `6`, `= 3` at `8`).
  set m : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ R).card with hmdef
  -- `hRPmass : E(R,P) + m = 9`, `hsat : (2 n₂ + 6 n₃) + m = 30`, `hII : 13 = n₁ + 2 n₂ + 3 n₃`.
  have hm68 : m = 6 ∨ m = 8 := by omega
  rcases hm68 with hm6 | hm8
  · exact Or.inl ⟨Or.inr hm6, by omega⟩
  · exact Or.inr hm8

/-- **The `|Hub| = 11` octahedron structural residual (now fully proved, axiom-clean).**  In the
no-two-hub clean octahedron with `¬ ZPoorCutConfig G`, the rich hubs
`R = {h ∈ Hub : 2 ≤ |N h ∩ Iso|}` satisfy: no hub is poor-zero (`hnozero`), `|R| = 6`, and the
rich-internal ordered mass is not `8`.

* **`mRR ≠ 8` — PROVED (axiom-clean).**  `octahedron_mass_reduce_nineteen` pins the only residual
  mass to `8` (the `n₃ = 3` twin profile `(n₃, n₂, n₁, n₀) = (3, 2, 0, 1)`).  The documented
  circularity — branch (b) of `octahedron_poor_force_b_or_c_nineteen` needs
  `octahedron_low_twin_poor_nineteen`, which needs `hhigh4 = n₃ ≥ 4`, exactly what `mRR = 8` fails to
  supply — is **broken** in `octahedron_mass_ne_eight_nineteen` (`TwinCert19OctaMassNe8`).  It reads
  the certificate directly off the `n₀ = 1` zero-rich twin `t₀`: with the six poor edges forced by
  `∑_{P} |N ∩ P| = mRR + 4 = 12`, either two of `t₀`'s three poor neighbours are adjacent (a good
  triangle, degree sum `11`, contradicting `hT`) or a fourth poor hub is adjacent to all three (a
  good `K₂,₃`, degree sum `19`, contradicting `hK23`).  No appeal to `hhigh4`.

* **`hnozero` + `|R| = 6` — PROVED (axiom-clean, `rich_six_no_iso_zero_nineteen` in
  `TwinCert19OctaMassNoZero`).**  `|R| ∈ {6, 7}` (`rich_count_ge_six_nineteen` via `r5_resid_nineteen`,
  `rich_count_le_seven_nineteen`); `|R| ≠ 7` via the mechanical `rich_count_ne_seven_nineteen` trace
  port (the `n = 18` `S ≥ 15` is unused — only `z_R ≥ 2` and `Off.card = 42` drive the contradiction).
  For `hnozero`: an iso-degree-`0` hub `h₀` has `|N(h₀) ∩ Hub| + |N(h₀) ∩ Z| = 4`.  If it meets both
  `M`-edge endpoints (`|N(h₀) ∩ Z| = 2`), the triangle `{h₀, z₁, z₂}` has degree sum
  `4 + 3 + 3 = 10 ≤ 11` — a good triangle excluded by `hT`.  Otherwise `|N(h₀) ∩ Hub| ≥ 3` forces
  `S = ∑_R isoDeg ≥ 14`, so some rich hub `h₁` has iso-degree `≥ 3` (hub-degree `≤ 1`); pairing it with
  a rich hub `h₂` met by an `M`-edge endpoint `z` (`each_z_meets_rich_nineteen`, `h₁ ≁ z, h₂` by the
  degree count) assembles a `Z`-leaf `TwoHubConfig` (`two_hub_zleaf_nineteen`) — a `ZPoorCutConfig`,
  contradicting `hcut`.

Everything downstream (`octahedron_inputs_nineteen`, `two_hub_corner_select_nineteen`) is clean glue
over the bundle. -/
theorem octahedron_struct_residual_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
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
    (hcut : ¬ ZPoorCutConfig G) :
    (∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) ∧
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 ∧
    (∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card)
      ≠ 8 := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hReq
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- `N t ∩ R ⊆ N t ∩ Hub`, so every twin meets at most three rich hubs.
  have htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsub)
      _ = 3 := hiso3 t ht
  -- **The remaining counting gap (single documented `sorry`): no poor-zero hub and `|R| = 6`.**
  -- Unlike `n = 18` (`|P| = 4` pins each poor hub to iso-degree exactly `1`), the fifth poor hub at
  -- `|Hub| = 11` leaves slack `S ∈ {13, 14}` that bare counting cannot close; the `r = 6`/`r = 7`,
  -- `S = 14` cases route through the (now axiom-clean) z-meets-2-poor cut machinery
  -- (`TwinCert19ZPoorDispatch`), whose assembly into this `hnozero ∧ |R| = 6` bundle is the only
  -- step not yet ported.
  have hpre : (∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) ∧ R.card = 6 :=
    rich_six_no_iso_zero_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3 hdsum
      hleak hshare hno2hub hC4 hK23 hT hcut
  obtain ⟨hnozero, hRcard⟩ := hpre
  refine ⟨hnozero, hRcard, ?_⟩
  -- `mRR ≠ 8` is now genuinely proved (the `n₃ = 3` circularity is broken in `TwinCert19OctaMassNe8`).
  exact octahedron_mass_ne_eight_nineteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
    hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard htle3 hcut

end N19

end ACMax
