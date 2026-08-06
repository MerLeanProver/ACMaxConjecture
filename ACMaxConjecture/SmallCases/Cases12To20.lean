import ACMaxConjecture.SmallCases.Dispatcher
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.Cut2K2Free12
import ACMaxConjecture.SmallCases.N12.TwinCert
import ACMaxConjecture.SmallCases.N13.TwinCert
import ACMaxConjecture.SmallCases.N14.TwinCert
import ACMaxConjecture.SmallCases.N15.TwinCert
import ACMaxConjecture.SmallCases.N16.TwinCert
import ACMaxConjecture.SmallCases.N17.TwinCert
import ACMaxConjecture.SmallCases.N18.TwinCert
import ACMaxConjecture.SmallCases.N19.TwinCert
import ACMaxConjecture.SmallCases.N20.TwinCert
import ACMaxConjecture.Spectral.AlgConnK2

/-!
# The finite ACMAX cases `12 ≤ n ≤ 20`

The shared dispatcher proves all reductions that do not depend on the order.
Each wrapper below contains only its three numerical thresholds and its final
structural certificate.
-/

namespace ACMax

open scoped Classical

private theorem algConn_le_two_of_hasSignedCut {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (h : HasSignedCut G) : algConn G ≤ 2 := by
  obtain ⟨P, N, hd, hc, hpos, hcond⟩ := h
  exact algConn_le_two_of_signed G P N hd hc hpos hcond

namespace N12

theorem upperBound_twelve (G : SimpleGraph (Fin 12)) (hm : G.edgeFinset.card = 20) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 12 10 13 17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  by_cases heD : 12 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card
  · exact algConn_le_two_of_2K2free_cut_twelve G hm h3 hT
      (by convert h2k2) (by convert heD)
  · obtain ⟨t, h₁, h₂, x, y, z, hdegt, hdegh₁, hdegh₂, hdegx, hdegy, hdegz,
        hadj_th₁, hadj_th₂, hadj_xy, hadj_yz,
        hnt_x, hnt_y, hnt_z,
        hnh₁_x, hnh₁_y, hnh₁_z, hnh₂_x, hnh₂_y, hnh₂_z,
        ne_h₁h₂, ne_tx, ne_ty, ne_tz, ne_xy, ne_yz, ne_xz⟩ :=
      exists_twin_signed_cert_twelve G hm h3 hT
        (by convert h2k2) (by convert heD) (by convert hC4) (by convert hK23) hiso
    have hnadj_xz : ¬G.Adj x z := by
      intro hxz
      apply hT
      exact ⟨x, y, z, ne_xy, ne_yz, ne_xz, hadj_xy, hadj_yz, hxz, by omega⟩
    have hcert : HasSignedCut G := by
      unfold HasSignedCut
      convert aligned_single_vertex_cut_certificate G t h₁ h₂ x y z
        hdegt hdegh₁ hdegh₂ hdegx hdegy hdegz hadj_th₁ hadj_th₂ hadj_xy hadj_yz
        hnadj_xz hnt_x hnt_y hnt_z hnh₁_x hnh₁_y hnh₁_z hnh₂_x hnh₂_y hnh₂_z
        ne_h₁h₂ ne_tx ne_ty ne_tz ne_xy ne_yz ne_xz
    exact algConn_le_two_of_hasSignedCut G hcert

end N12

namespace N13

theorem upperBound_thirteen (G : SimpleGraph (Fin 13)) (hm : G.edgeFinset.card = 22) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 13 10 13 18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  have hcert : HasSignedCut G := by
    unfold HasSignedCut
    convert exists_twin_signed_cert_thirteen G hm h3 hT
      (by convert h2k2) (by convert hC4) (by convert hK23) hiso
  exact algConn_le_two_of_hasSignedCut G hcert

end N13

namespace N14

theorem upperBound_fourteen (G : SimpleGraph (Fin 14)) (hm : G.edgeFinset.card = 24) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 14 10 13 18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  have hcert : HasSignedCut G := by
    unfold HasSignedCut
    convert exists_twin_signed_cert_fourteen G hm h3 hT
      (by convert h2k2) (by convert hC4) (by convert hK23) hiso
  exact algConn_le_two_of_hasSignedCut G hcert

end N14

namespace N15

theorem upperBound_fifteen (G : SimpleGraph (Fin 15)) (hm : G.edgeFinset.card = 26) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 15 10 13 18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  have hcert : HasSignedCut G := by
    unfold HasSignedCut
    convert exists_twin_signed_cert_fifteen G hm h3 hT
      (by convert h2k2) (by convert hC4) (by convert hK23) hiso
  exact algConn_le_two_of_hasSignedCut G hcert

end N15

namespace N16

theorem upperBound_sixteen (G : SimpleGraph (Fin 16)) (hm : G.edgeFinset.card = 28) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 16 10 14 18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  have hcert : HasSignedCut G := by
    unfold HasSignedCut
    convert exists_twin_signed_cert_sixteen G hm h3 hT
      (by convert h2k2) (by convert hC4) (by convert hK23) hiso
  exact algConn_le_two_of_hasSignedCut G hcert

end N16

namespace N17

theorem upperBound_seventeen (G : SimpleGraph (Fin 17)) (hm : G.edgeFinset.card = 30) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 17 10 14 19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  have hcert : HasSignedCut G := by
    unfold HasSignedCut
    convert exists_twin_signed_cert_seventeen G hm h3 hT
      (by convert h2k2) (by convert hC4) (by convert hK23) hiso
  exact algConn_le_two_of_hasSignedCut G hcert

end N17

namespace N18

theorem upperBound_eighteen (G : SimpleGraph (Fin 18)) (hm : G.edgeFinset.card = 32) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 18 11 14 19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  have hcert : HasSignedCut G := by
    unfold HasSignedCut
    convert exists_twin_signed_cert_eighteen G hm h3 hT
      (by convert h2k2) (by convert hC4) (by convert hK23) hiso
  exact algConn_le_two_of_hasSignedCut G hcert

end N18

namespace N19

theorem upperBound_nineteen (G : SimpleGraph (Fin 19)) (hm : G.edgeFinset.card = 34) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 19 11 14 19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  have hcert : HasSignedCut G := by
    unfold HasSignedCut
    convert exists_twin_signed_cert_nineteen G hm h3 hT
      (by convert h2k2) (by convert hC4) (by convert hK23) hiso
  exact algConn_le_two_of_hasSignedCut G hcert

end N19

namespace N20

theorem upperBound_twenty (G : SimpleGraph (Fin 20)) (hm : G.edgeFinset.card = 36) :
    algConn G ≤ 2 := by
  refine upperBound_of_residual_signed_cut 20 11 14 19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    G (by simpa using hm) ?_
  intro h3 hT h2k2 hC4 hK23 hiso
  unfold HasSparseTriangle at hT
  unfold HasDegreeThree2K2 at h2k2
  unfold HasSparseC4 at hC4
  unfold HasSparseK23 at hK23
  unfold HasIsolatedDegreeThree at hiso
  have hcert : HasSignedCut G := by
    unfold HasSignedCut
    convert exists_twin_signed_cert_twenty G hm h3 hT
      (by convert h2k2) (by convert hC4) (by convert hK23) hiso
  exact algConn_le_two_of_hasSignedCut G hcert

end N20

open N12 N13 N14 N15 N16 N17 N18 N19 N20

theorem acmax_conjecture_twelve :
    algConn (completeBipartiteGraph (Fin 2) (Fin 10)) = 2 ∧
      ∀ G : SimpleGraph (Fin 12), G.edgeFinset.card = 20 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 12 (by norm_num), upperBound_twelve⟩

theorem acmax_conjecture_thirteen :
    algConn (completeBipartiteGraph (Fin 2) (Fin 11)) = 2 ∧
      ∀ G : SimpleGraph (Fin 13), G.edgeFinset.card = 22 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 13 (by norm_num), upperBound_thirteen⟩

theorem acmax_conjecture_fourteen :
    algConn (completeBipartiteGraph (Fin 2) (Fin 12)) = 2 ∧
      ∀ G : SimpleGraph (Fin 14), G.edgeFinset.card = 24 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 14 (by norm_num), upperBound_fourteen⟩

theorem acmax_conjecture_fifteen :
    algConn (completeBipartiteGraph (Fin 2) (Fin 13)) = 2 ∧
      ∀ G : SimpleGraph (Fin 15), G.edgeFinset.card = 26 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 15 (by norm_num), upperBound_fifteen⟩

theorem acmax_conjecture_sixteen :
    algConn (completeBipartiteGraph (Fin 2) (Fin 14)) = 2 ∧
      ∀ G : SimpleGraph (Fin 16), G.edgeFinset.card = 28 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 16 (by norm_num), upperBound_sixteen⟩

theorem acmax_conjecture_seventeen :
    algConn (completeBipartiteGraph (Fin 2) (Fin 15)) = 2 ∧
      ∀ G : SimpleGraph (Fin 17), G.edgeFinset.card = 30 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 17 (by norm_num), upperBound_seventeen⟩

theorem acmax_conjecture_eighteen :
    algConn (completeBipartiteGraph (Fin 2) (Fin 16)) = 2 ∧
      ∀ G : SimpleGraph (Fin 18), G.edgeFinset.card = 32 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 18 (by norm_num), upperBound_eighteen⟩

theorem acmax_conjecture_nineteen :
    algConn (completeBipartiteGraph (Fin 2) (Fin 17)) = 2 ∧
      ∀ G : SimpleGraph (Fin 19), G.edgeFinset.card = 34 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 19 (by norm_num), upperBound_nineteen⟩

theorem acmax_conjecture_twenty :
    algConn (completeBipartiteGraph (Fin 2) (Fin 18)) = 2 ∧
      ∀ G : SimpleGraph (Fin 20), G.edgeFinset.card = 36 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 20 (by norm_num), upperBound_twenty⟩

end ACMax
