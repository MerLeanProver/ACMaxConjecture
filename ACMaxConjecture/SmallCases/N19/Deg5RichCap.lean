import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core

/-!
# The rich-hub iso-cap (`n = 19`, deg-5 corner)

The reusable ledger ingredient the bare degree counting misses: if `g` is a
degree-`4` hub with `≥ 3` `Iso` twins ("rich"), then **every** degree-`4` hub
`h` non-adjacent to `g` has at most `2` `Iso` twins.  Otherwise both `g` and `h`
keep `≥ 3 − 1 = 2` private twins (share `≤ 1` by `hshare`), and the two form the
forbidden `hno2hub` pair.  This cap is what closes the `Σ isoDeg` ledger in the
rich `Z`-leaf extractions — pure degree caps allow a spurious
`Σ isoDeg = 24` assignment.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **The rich-hub iso-cap.**  A degree-`4` hub `h` non-adjacent to a rich
degree-`4` hub `g` (`isoDeg g ≥ 3`) has `isoDeg h ≤ 2`. -/
theorem isoDeg_le_two_of_nonadj_rich_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g h : Fin 19) (hg : g ∈ Hub) (hh : h ∈ Hub)
    (hgd : G.degree g = 4) (hhd : G.degree h = 4) (hgh : g ≠ h)
    (hnadj : ¬G.Adj g h) (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    (G.neighborFinset h ∩ Iso).card ≤ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon : 3 ≤ isoDeg h`.
  have hshare1 : (G.neighborFinset g ∩ G.neighborFinset h ∩ Iso).card ≤ 1 :=
    hshare g hg hgd h hh hhd hgh hnadj
  -- private twins of `g` off `h`: `≥ 3 − 1 = 2`.
  have hgpriv : 2 ≤ ((G.neighborFinset g ∩ Iso) \ G.neighborFinset h).card := by
    have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset g ∩ Iso)
      (G.neighborFinset h)
    have hinter : (G.neighborFinset g ∩ Iso) ∩ G.neighborFinset h
        = G.neighborFinset g ∩ G.neighborFinset h ∩ Iso := Finset.inter_right_comm _ _ _
    rw [hinter] at hkey
    omega
  -- private twins of `h` off `g`: `≥ 3 − 1 = 2` (share is symmetric).
  have hshare1' : (G.neighborFinset h ∩ G.neighborFinset g ∩ Iso).card ≤ 1 := by
    have : G.neighborFinset h ∩ G.neighborFinset g ∩ Iso
        = G.neighborFinset g ∩ G.neighborFinset h ∩ Iso := by
      rw [Finset.inter_comm (G.neighborFinset h) (G.neighborFinset g)]
    rw [this]; exact hshare1
  have hhpriv : 2 ≤ ((G.neighborFinset h ∩ Iso) \ G.neighborFinset g).card := by
    have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h ∩ Iso)
      (G.neighborFinset g)
    have hinter : (G.neighborFinset h ∩ Iso) ∩ G.neighborFinset g
        = G.neighborFinset h ∩ G.neighborFinset g ∩ Iso := Finset.inter_right_comm _ _ _
    rw [hinter] at hkey
    omega
  exact hno2hub ⟨g, h, hg, hh, hgd, hhd, hgh, hnadj, hgpriv, hhpriv⟩

end N19

end ACMax
