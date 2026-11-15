import D4Bound.ModerateGraphCert
import D4Bound.SphericalEdgeBound

/-! The moderate angular graph has at most 1880 ordered edges on every
unit code with maximum cosine 7/9. No bound on the code size is assumed.
-/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
noncomputable section
open Classical

theorem moderate_graph_quadratic (N : ℝ) :
    N*(40670769968163/1000000000000)-
      (109916026941/500000000000)*N^2 < 1882 := by
  nlinarith [sq_nonneg (N-13556923322721/146554702588)]

theorem moderate_angular_edges_le
    (C : Finset (EuclideanSpace ℝ (Fin 4)))
    (hC : ∀ u ∈ C, ‖u‖ = 1)
    (hsep : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ⟪u,v⟫ ≤ 7/9) :
    angularBandCount C (-4/5) (-11/20) ≤ 1880 := by
  have hb := spherical_band_bound C hC (7/9) (109916026941/500000000000)
    (40670769968163/1000000000000) (-4/5) (-11/20)
    ModerateGraphCertificate.rest (by norm_num) ModerateGraphCertificate.rest_energy
    ModerateGraphCertificate.diagonal
    (fun t ht ht' => by
      simpa using ModerateGraphCertificate.whole_sign t (by simpa using ht) ht')
    (fun t ht ht' => by linarith [ModerateGraphCertificate.band_sign t ht ht']) hsep
  have hr := hb.trans_lt (moderate_graph_quadratic C.card)
  have hn : angularBandCount C (-4/5) (-11/20) < 1882 := by exact_mod_cast hr
  obtain ⟨k,hk⟩ := angularBandCount_even C hC (-4/5) (-11/20) (by norm_num)
  omega

end
end D4Bound
