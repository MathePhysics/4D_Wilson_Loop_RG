import GaussianBlockSpin.ClipPieces

/-! Under the cut-off product law `ν = γ₁(· | [-β, β])^{⊗ι}` almost every configuration has all coordinates in
`[-β, β]` (ae_mem_Icc_cond), so the clipped sum equals the polynomial almost everywhere (clipPieces_sum_ae_eq); almost
everywhere equal functions have the same cumulant sums (cumulantSum_congr_ae). -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

omit [DecidableEq ι] in
lemma ae_mem_Icc_cond (γ₁ : Measure ℝ) [IsProbabilityMeasure γ₁] (β : ℝ) :
    ∀ᵐ ξ ∂(Measure.pi fun _ : ι => cond γ₁ (Set.Icc (-β) β)), ∀ c, ξ c ∈ Set.Icc (-β) β := by
  rw [Filter.eventually_all]
  intro c
  have h1 : ∀ᵐ x ∂(cond γ₁ (Set.Icc (-β) β)), x ∈ Set.Icc (-β) β := by
    rw [ae_iff, cond_apply measurableSet_Icc]
    have : Set.Icc (-β) β ∩ {x | ¬ x ∈ Set.Icc (-β) β} = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
        not_not]; exact id
    rw [this, measure_empty, mul_zero]
  exact (Measure.quasiMeasurePreserving_eval _ c).ae h1

/-- The clipped sum equals the polynomial almost everywhere. -/
lemma clipPieces_sum_ae_eq (γ₁ : Measure ℝ) [IsProbabilityMeasure γ₁] {β : ℝ} (hβ : 0 ≤ β)
    (b : MonoIdx ι D → ℝ) (S : Finset (MonoIdx ι D)) :
    (clipPieces hβ b S).sum Finset.univ =ᵐ[Measure.pi fun _ : ι => cond γ₁ (Set.Icc (-β) β)]
      fun ξ => ∑ X ∈ S, monoPiece b X ξ := by
  filter_upwards [ae_mem_Icc_cond γ₁ β] with ξ hξ
  exact clipPieces_sum_eq hβ b S hξ

/-- Equal almost everywhere, equal cumulant sums. -/
lemma cumulantSum_congr_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {V W : Ω → ℝ}
    (h : V =ᵐ[μ] W) (t : ℕ) : cumulantSum μ V t = cumulantSum μ W t := by
  have hm : moments μ V = moments μ W := by
    funext n
    unfold moments
    exact integral_congr_ae (h.mono fun ω hω => by simp [hω])
  unfold cumulantSum
  rw [hm]

end GaussianBlockSpin
