import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.OctahedronForce
import ACMaxConjecture.SmallCases.N20.OctahedronMassFour
import ACMaxConjecture.SmallCases.N20.OctahedronPoorForce2
import ACMaxConjecture.SmallCases.N20.OctaMassNe8
import ACMaxConjecture.SmallCases.N20.OctaMassNoZero

/-!
# Octahedron mass-exclusion handshake (`n = 20`, `|Hub| = 12`, `(12, 6, 48)`)

This file isolates the **mass-exclusion handshake** for the clean `(12, 6, 48)` octahedron — the
genuinely-new `|Hub| = 12` content that pins the rich-internal ordered edge mass
`mRR = ∑_{r∈R} |N r ∩ R|` to `{4, 6}` (and simultaneously yields the four-high-twins input
`hhigh4`).  It is the analog of the `n = 19` `octahedron_mass_reduce_nineteen`, but the sixth poor
hub shifts the whole ±1 chain: the rich iso-incidence sum drops to `S = 12`, the handshake budget
grows to `mRR + E(R, P) = 10`, and the excluded residual mass moves from `8` to `10`.

## The recomputed handshake for `(12, 6, 48)`

With `|Hub| = 12`, `R + P = 12`, `|Iso| = 6`, `|Z| = 2` and `R.card = 6` we have `P.card = 6`.
Every poor hub has iso-degree exactly `1` (`hnozero` plus the `< 2` poor definition), so the rich
iso-incidence sum is

  `S = ∑_{r∈R} |N r ∩ Iso| = 18 − |P| = 18 − 6 = 12   (= 6 + |R|)`.

The degree sum over the six rich hubs (`6·4 = 24`) splits over the partition `R ⊔ P ⊔ Iso ⊔ Z` as

  `mRR + E(R, P) + S + E(R, Z) = 24`,  with `S = 12`, `E(R, Z) = 2`  ⟹  `mRR + E(R, P) = 10`

(this is exactly `octahedron_poor_counts_twenty`'s `hRPmass`).  Since `E(R, P) ≥ 0` this gives
`mRR ≤ 10`.

## The trace saturation pins `mRR ∈ {6, 10}` and `n₃`

Writing `n_k` for the number of `M`-isolated twins meeting exactly `k` rich hubs, the saturation
`(∑_t |N t ∩ R|·(|N t ∩ R| − 1)) + mRR = |R|² − |R| = 30` with the cross count
`∑_t |N t ∩ R| = S = 12` gives the linear system

  `n₀ + n₁ + n₂ + n₃ = 6`,   `n₁ + 2 n₂ + 3 n₃ = 12`,   `2 n₂ + 6 n₃ = 30 − mRR`.

Over `ℕ` with `mRR ≤ 10` the **only** solutions are

  `mRR = 6 : (n₃, n₂, n₁, n₀) = (4, 0, 0, 2)`  and  `mRR = 10 : (n₃, n₂, n₁, n₀) = (3, 1, 1, 1)`

(`mRR ∈ {4, 8}` have no `ℕ`-solution — `n₁ + n₂ = mRR/2 − 3` forces `mRR ≥ 6`, and `mRR = 8` needs
the non-integer `3 n₃ ∈ {10, 11}`; odd `mRR` breaks parity; `mRR ∈ {12, 14}` violate `mRR ≤ 10`).
At `mRR = 6` we get `n₃ = 4` (the four high twins `hhigh4`); at `mRR = 10` we get `n₃ = 3` (one
short of `hhigh4`).  Hence the dichotomy below: either the good mass `mRR ∈ {4, 6}` with four high
twins, or the residual `mRR = 10`.

`octahedron_mass_reduce_twenty` is **axiom-clean**: it derives this dichotomy from
`octahedron_trace_saturate_twenty` (LEAF) and `octahedron_poor_counts_twenty` (the cross-layer
handshake), via `omega`.  The remaining `mRR = 10` exclusion (equivalently the four-high-twins
input) is the residual the surrounding octahedron poor-layout layer must kill.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Octahedron mass-exclusion dichotomy (LEAF, `n = 20`, `(12, 6, 48)`).**  In the clean no-two-hub
`|Hub| = 12` octahedron with `R.card = 6` and `hnozero`, the rich-internal ordered mass
`mRR = ∑_{r∈R} |N r ∩ R|` together with the four-high-twins count is pinned:

* either `mRR ∈ {4, 6}` **and** at least four `M`-isolated twins meet all three of their hubs inside
  `R` (the good octahedron — exactly the bundle `octahedron_poor_layer_force_twenty` consumes),
* or `mRR = 10` (the residual `n₃ = 3` profile).

The proof is the handshake `mRR + E(R, P) = 10` (`octahedron_poor_counts_twenty`) giving
`mRR ≤ 10`, combined with the trace saturation `∑_t |N t ∩ R|·(|N t ∩ R| − 1) + mRR = 30` and the
cross count `∑_t |N t ∩ R| = 12` (`octahedron_trace_saturate_twenty`), discharged by `omega`. -/
theorem octahedron_mass_reduce_twenty (G : SimpleGraph (Fin 20))
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
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) (hRcard : R.card = 6)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3)
    (hcut : ¬ ZPoorCutConfig G) :
    (((∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨
        (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6) ∧
      4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    ∨ (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 10 := by
  classical
  -- Trace saturation: `∑offDiag + mRR = 30` and the rich iso-incidence sum `= 12`.
  obtain ⟨hsat, h12⟩ := octahedron_trace_saturate_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj hHub
    hIso hisodeg3 hshare hno2hub hT hnozero
  rw [hRcard] at hsat h12
  -- Cross count: `∑_t |N t ∩ R| = ∑_r |N r ∩ Iso| = 12`.
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 12 := by
    rw [cross_count_twenty G Iso R]; exact h12
  -- Handshake: `E(R, P) + mRR = 10`, hence `mRR ≤ 10`.
  obtain ⟨_, _, hRPmass, _, _⟩ := (octahedron_poor_counts_twenty G Hub Iso R hReq hdeg4 hiso3
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
  -- `mRR = ∑_r |N r ∩ R|`.  From `hRPmass` (`E(R,P) + mRR = 10`) we get `mRR ≤ 10`; with the trace
  -- system this forces `mRR ∈ {6, 10}` and pins `n₃` (`= 4` at `6`, `= 3` at `10`).
  set m : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ R).card with hmdef
  -- `hRPmass : E(R,P) + m = 10`, `hsat : (2 n₂ + 6 n₃) + m = 30`, `hII : 12 = n₁ + 2 n₂ + 3 n₃`.
  have hm610 : m = 6 ∨ m = 10 := by omega
  rcases hm610 with hm6 | hm10
  · exact Or.inl ⟨Or.inr hm6, by omega⟩
  · exact Or.inr hm10

/-- **The `|Hub| = 12` octahedron structural residual (now fully proved, axiom-clean).**  In the
no-two-hub clean octahedron with `¬ ZPoorCutConfig G`, the rich hubs
`R = {h ∈ Hub : 2 ≤ |N h ∩ Iso|}` satisfy: no hub is poor-zero (`hnozero`), `|R| = 6`, and the
rich-internal ordered mass is not `10`.

* **`mRR ≠ 10` — PROVED (axiom-clean).**  `octahedron_mass_reduce_twenty` pins the only residual
  mass to `10` (the `n₃ = 3` twin profile `(n₃, n₂, n₁, n₀) = (3, 1, 1, 1)`).  The documented
  circularity — branch (b) of `octahedron_poor_force_b_or_c_twenty` needs
  `octahedron_low_twin_poor_twenty`, which needs `hhigh4 = n₃ ≥ 4`, exactly what `mRR = 10` fails to
  supply — is **broken** in `octahedron_mass_ne_eight_twenty` (`TwinCert20OctaMassNe8`).  It reads
  the certificate directly off the `n₀ = 1` zero-rich twin `t₀`: with the eight poor edges forced
  by `∑_{P} |N ∩ P| = mRR + 6 = 16`, either two of `t₀`'s three poor neighbours are adjacent (a
  good triangle, degree sum `11`, contradicting `hT`) or one of the three poor hubs outside
  `Q = N(t₀) ∩ P` is adjacent to all of `Q` (a good `K₂,₃`, degree sum `19`, contradicting
  `hK23`).  No appeal to `hhigh4`.

* **`hnozero` + `|R| = 6` — PROVED (axiom-clean, `rich_six_no_iso_zero_twenty` in
  `TwinCert20OctaMassNoZero`).**  `|R| ∈ {6, 7}` (`rich_count_ge_six_twenty` via `r5_resid_twenty`
  and the all-poor-at-one boundary `all_poor_one_resid_twenty`, `rich_count_le_seven_twenty`);
  `|R| ≠ 7` via the mechanical `rich_count_ne_seven_twenty` trace port.  For `hnozero`: an
  iso-degree-`0` hub `h₀` has `|N(h₀) ∩ Hub| + |N(h₀) ∩ Z| = 4`.  If it meets both `M`-edge
  endpoints (`|N(h₀) ∩ Z| = 2`), the triangle `{h₀, z₁, z₂}` has degree sum `4 + 3 + 3 = 10 ≤ 11` —
  a good triangle excluded by `hT`.  The complementary case (`|N(h₀) ∩ Hub| ≥ 3`, the sixth-poor-hub
  residual) is killed inside `TwinCert20OctaMassNoZero` via the `Z`-leaf/`ZPoorCutConfig` machinery,
  contradicting `hcut`.

Everything downstream (`octahedron_inputs_twenty`, `two_hub_corner_select_twenty`) is clean glue
over the bundle. -/
theorem octahedron_struct_residual_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
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
    (hcut : ¬ ZPoorCutConfig G) :
    (∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) ∧
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 ∧
    (∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card)
      ≠ 10 := by
  classical
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hReq
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- `N t ∩ R ⊆ N t ∩ Hub`, so every twin meets at most three rich hubs.
  have htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsub)
      _ = 3 := hiso3 t ht
  -- The `hnozero ∧ |R| = 6` bundle, fully proved at `|Hub| = 12` in `TwinCert20OctaMassNoZero`.
  have hpre : (∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) ∧ R.card = 6 :=
    rich_six_no_iso_zero_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hisodeg3 hdeg3 hdsum
      hleak hshare hno2hub hC4 hK23 hT hcut
  obtain ⟨hnozero, hRcard⟩ := hpre
  refine ⟨hnozero, hRcard, ?_⟩
  -- `mRR ≠ 10` is genuinely proved (the `n₃ = 3` circularity is broken in `TwinCert20OctaMassNe8`).
  exact octahedron_mass_ne_eight_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
    hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard htle3 hcut

end N20

end ACMax
