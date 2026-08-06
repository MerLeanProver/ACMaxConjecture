import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5ZSlots
import ACMaxConjecture.SmallCases.N19.Deg5SameZ

/-!
# The second `M`-endpoint `z'` for the share-2 (10,7,41) octahedron (`n = 19`)

`|Z| = 2` (two `M`-edge endpoints); given `z` with `N z ∩ Hub = {h₂, r_z}`,
the other endpoint `z'` (deg `3`, meets no `Iso`) meets exactly two degree-`4`
hubs `{p, q}` disjoint from `{h₂, r_z}` (no hub meets both `z`, `z'`, else the
triangle `{z, z', h}` of degree sum `3 + 3 + ≤5 ≤ 11` fires `hT`), and one of
`p, q` is iso-poor (`same_z_pair`).
-/

namespace ACMax

open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The second `M`-endpoint and its two hubs.** -/
theorem octahedron_second_mend_share2_1041_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum17 : Hub.card + Iso.card = 17)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (_hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 41)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧ G.Adj a b ∧ G.Adj b c ∧
      G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧ 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (f : Fin 19) (hfHub : f ∈ Hub) (hfd : G.degree f = 5)
    (hfiso5 : (G.neighborFinset f ∩ Iso).card = 5)
    (z h₂ r_z : Fin 19) (_hh₂ : h₂ ∈ Hub) (_hr_z : r_z ∈ Hub)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hNz : G.neighborFinset z ∩ Hub = ({h₂, r_z} : Finset (Fin 19))) :
    ∃ z' p q : Fin 19, z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧ z' ≠ z ∧
      G.Adj z z' ∧ G.degree z' = 3 ∧ (G.neighborFinset z' ∩ Iso).card = 0 ∧
      G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 19)) ∧
      p ∈ Hub ∧ q ∈ Hub ∧ G.degree p = 4 ∧ G.degree q = 4 ∧ p ≠ q ∧
      G.Adj z' p ∧ G.Adj z' q ∧ p ≠ h₂ ∧ p ≠ r_z ∧ q ≠ h₂ ∧ q ≠ r_z ∧ ¬G.Adj p q ∧
      ((G.neighborFinset p ∩ Iso).card ≤ 1 ∨ (G.neighborFinset q ∩ Iso).card ≤ 1) := by
  classical
  -- Step 1: the `Z`-slot skeleton — `Z = {z₁, z₂}`, `z₁ ∼ z₂`, no hub meets both.
  obtain ⟨z₁, z₂, hne12, hz₁Z, hz₂Z, hZeq, hadj12, hnohub⟩ :=
    zslot_skeleton_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg5 hT
  have hzmem : z = z₁ ∨ z = z₂ := by
    have hm : z ∈ ({z₁, z₂} : Finset (Fin 19)) := hZeq ▸ hzZ
    rwa [Finset.mem_insert, Finset.mem_singleton] at hm
  -- Match `z` to one endpoint; `z'` is the other, adjacent to `z`, met by no common hub.
  obtain ⟨z', hz'Z, hz'ne, hzz'adj, hnohub'⟩ :
      ∃ z', z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧ z' ≠ z ∧ G.Adj z z' ∧
        ∀ h ∈ Hub, ¬(G.Adj h z ∧ G.Adj h z') := by
    rcases hzmem with h | h
    · subst h
      exact ⟨z₂, hz₂Z, hne12.symm, hadj12, hnohub⟩
    · subst h
      exact ⟨z₁, hz₁Z, hne12, hadj12.symm, fun h hh hc => hnohub h hh ⟨hc.2, hc.1⟩⟩
  -- Step 2: `z'` facts — deg `3`, meets no `Iso`, meets exactly two hubs.
  obtain ⟨hz'iso0, hz'hub2, hz'deg3⟩ :=
    zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak z' hz'Z
  -- Step 3: name the two hubs `p, q` of `z'`.
  obtain ⟨p, q, hpq, hpqeq⟩ := Finset.card_eq_two.mp hz'hub2
  have hpmem : p ∈ G.neighborFinset z' ∩ Hub := by
    rw [hpqeq]; exact Finset.mem_insert_self p {q}
  have hqmem : q ∈ G.neighborFinset z' ∩ Hub := by
    rw [hpqeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hp : p ∈ Hub := (Finset.mem_inter.mp hpmem).2
  have hq : q ∈ Hub := (Finset.mem_inter.mp hqmem).2
  have hz'p : G.Adj z' p := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hpmem).1
  have hz'q : G.Adj z' q := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hqmem).1
  -- Step 4: `deg p = deg q = 4`.  First, `f`'s neighbourhood lies in `Iso`.
  have hfNcard : (G.neighborFinset f).card = 5 := by
    rw [G.card_neighborFinset_eq_degree]; exact hfd
  have hNfIso : G.neighborFinset f ∩ Iso = G.neighborFinset f :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hfNsubIso : G.neighborFinset f ⊆ Iso := by
    rw [← hNfIso]; exact Finset.inter_subset_right
  have hz'notIso : z' ∉ Iso := by
    have hnu := (Finset.mem_sdiff.mp hz'Z).2
    exact fun hc => hnu (Finset.mem_union_right _ hc)
  -- `p, q` meet `z' ∈ Z ∌ Iso`, but `f` meets only `Iso`, so `p ≠ f` and `q ≠ f`.
  have hpf : p ≠ f := by
    intro he
    have : z' ∈ G.neighborFinset f := by rw [G.mem_neighborFinset, ← he]; exact hz'p.symm
    exact hz'notIso (hfNsubIso this)
  have hqf : q ≠ f := by
    intro he
    have : z' ∈ G.neighborFinset f := by rw [G.mem_neighborFinset, ← he]; exact hz'q.symm
    exact hz'notIso (hfNsubIso this)
  -- Two distinct deg-`5` hubs would push `∑_{Hub} deg ≥ 5 + 5 + 4·8 = 42 > 41`.
  have hdeg4 : ∀ v : Fin 19, v ∈ Hub → v ≠ f → G.degree v = 4 := by
    intro v hvHub hvf
    have hvle : G.degree v ≤ 5 := hdeg5 v hvHub
    have hvge : 4 ≤ G.degree v := hdeg v hvHub
    by_contra hne4
    have hv5 : G.degree v = 5 := by omega
    have hsplitf : ∑ w ∈ Hub, G.degree w = G.degree f + ∑ w ∈ Hub.erase f, G.degree w :=
      (Finset.add_sum_erase _ (fun w => G.degree w) hfHub).symm
    have hvef : v ∈ Hub.erase f := Finset.mem_erase.mpr ⟨hvf, hvHub⟩
    have hsplitv : ∑ w ∈ Hub.erase f, G.degree w
        = G.degree v + ∑ w ∈ (Hub.erase f).erase v, G.degree w :=
      (Finset.add_sum_erase _ (fun w => G.degree w) hvef).symm
    have hrest : 4 * ((Hub.erase f).erase v).card
        ≤ ∑ w ∈ (Hub.erase f).erase v, G.degree w := by
      have hb : ∀ x ∈ (Hub.erase f).erase v, 4 ≤ G.degree x := fun x hx =>
        hdeg x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      have h := Finset.card_nsmul_le_sum ((Hub.erase f).erase v) (fun w => G.degree w) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hcardef : (Hub.erase f).card = Hub.card - 1 := Finset.card_erase_of_mem hfHub
    have hcardefv : ((Hub.erase f).erase v).card = (Hub.erase f).card - 1 :=
      Finset.card_erase_of_mem hvef
    omega
  have hdp : G.degree p = 4 := hdeg4 p hp hpf
  have hdq : G.degree q = 4 := hdeg4 q hq hqf
  -- Step 5: `p, q ∉ {h₂, r_z}` — the latter meet `z`, so a common hub would meet `z, z'`.
  have hh₂mem : h₂ ∈ G.neighborFinset z ∩ Hub := by
    rw [hNz]; exact Finset.mem_insert_self h₂ {r_z}
  have hr_zmem : r_z ∈ G.neighborFinset z ∩ Hub := by
    rw [hNz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self r_z)
  have hAzh₂ : G.Adj z h₂ := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hh₂mem).1
  have hAzr_z : G.Adj z r_z := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hr_zmem).1
  have hph₂ : p ≠ h₂ := by
    intro he; apply hnohub' p hp; exact ⟨he ▸ hAzh₂.symm, hz'p.symm⟩
  have hpr_z : p ≠ r_z := by
    intro he; apply hnohub' p hp; exact ⟨he ▸ hAzr_z.symm, hz'p.symm⟩
  have hqh₂ : q ≠ h₂ := by
    intro he; apply hnohub' q hq; exact ⟨he ▸ hAzh₂.symm, hz'q.symm⟩
  have hqr_z : q ≠ r_z := by
    intro he; apply hnohub' q hq; exact ⟨he ▸ hAzr_z.symm, hz'q.symm⟩
  -- Step 6: `p, q` are non-adjacent and one is iso-poor.
  obtain ⟨hnpq, _, hisopoor⟩ :=
    same_z_pair_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hT hC4 hno2hub
      z' p q hz'Z hp hq hdp hdq hpq hz'p hz'q
  -- Step 7: assemble.
  exact ⟨z', p, q, hz'Z, hz'ne, hzz'adj, hz'deg3, hz'iso0, hpqeq, hp, hq, hdp, hdq, hpq,
    hz'p, hz'q, hph₂, hpr_z, hqh₂, hqr_z, hnpq, hisopoor⟩

end N19

end ACMax
