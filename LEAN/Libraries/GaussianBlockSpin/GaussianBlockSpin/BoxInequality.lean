import GaussianBlockSpin.BoxStep

/-! The inequality of one box (the cumulant formula (5.21) of [2] in a box, twice, with the box identity in between):
with the corridor coordinates fixed at `x`,
`log ∫ e^{Ψ_b} dμ_b ≥ δ_b + log ∫ e^{Ψ_b - Ψ^D_b} dμ_b - 2 ε_b`, where `δ_b` is the unconditional cumulant sum of the
interior pieces minus that of the shallow ones and `ε_b = c_{t+1} M_b^{t+1}/(t+1)!`, `M_b = Σ_{X in box b} a_X`. -/

namespace GaussianBlockSpin

open MeasureTheory Function
open scoped Nat

variable {ι P β : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β]
variable {L : LocalPieces ι P} (pv : Pavement L β)
variable (ν₁ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν₁ i)]

omit [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] in
lemma LocalPieces.a_nonneg (L : LocalPieces ι P) (X : P) : 0 ≤ L.a X :=
  (abs_nonneg _).trans (L.bdd X 0)

/-- The mass of box `b`: `M_b = Σ_{X in box b} a_X`. -/
def Pavement.mass (b : β) : ℝ := ∑ X ∈ pv.pieces b, L.a X

/-- The Taylor error of box `b`: `ε_b = c_{t+1} M_b^{t+1}/(t+1)!`. -/
noncomputable def Pavement.boxError (t : ℕ) (b : β) : ℝ := cumBound (t + 1) * pv.mass b ^ (t + 1) / (t + 1)!

/-- The unconditional cumulant sum of the interior pieces of box `b` minus that of its non-deep interior pieces. -/
noncomputable def Pavement.boxGain (t : ℕ) (D : Finset P) (b : β) : ℝ :=
  cumulantSum (Measure.pi ν₁) (L.sum (pv.interior b)) t - cumulantSum (Measure.pi ν₁) (L.sum (pv.interior b \ D)) t

omit [Fintype ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β] in
lemma Pavement.measurable_boxSum (b : β) (x : ι → ℝ) (s : Finset P) : Measurable (pv.boxSum b x s) :=
  Finset.measurable_sum _ fun X _ => pv.measurable_update b x X

omit [Fintype ι] [DecidableEq P] [Fintype β] in
lemma Pavement.abs_boxSum_le (b : β) (x : ι → ℝ) {s : Finset P} (hs : s ⊆ pv.pieces b) (y : pv.box b → ℝ) :
    |pv.boxSum b x s y| ≤ pv.mass b := by
  unfold Pavement.boxSum Pavement.mass
  calc |∑ X ∈ s, L.h X (updateFinset x (pv.box b) y)| ≤ ∑ X ∈ s, |L.h X (updateFinset x (pv.box b) y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ X ∈ s, L.a X := Finset.sum_le_sum fun X _ => L.bdd X _
    _ ≤ ∑ X ∈ pv.pieces b, L.a X := Finset.sum_le_sum_of_subset_of_nonneg hs fun X _ _ => L.a_nonneg X

omit [Fintype β] in
/-- **The inequality of one box**. -/
theorem Pavement.log_box_ge (t : ℕ) (b : β) (x : ι → ℝ) (D : Finset P) (hD : ∀ X ∈ D, pv.IsDeep t X) :
    pv.boxGain ν₁ t D b + Real.log (∫ y, Real.exp (pv.boxSum b x (pv.pieces b \ D) y) ∂(boxMeasure ν₁ (pv.box b))) -
        2 * pv.boxError t b ≤
      Real.log (∫ y, Real.exp (pv.boxSum b x (pv.pieces b) y) ∂(boxMeasure ν₁ (pv.box b))) := by
  have hM : 0 ≤ pv.mass b := Finset.sum_nonneg fun X _ => L.a_nonneg X
  have h1 := abs_log_integral_exp_sub_cumulantSum_le (boxMeasure ν₁ (pv.box b)) (pv.measurable_boxSum b x _) hM
    (pv.abs_boxSum_le b x subset_rfl) t
  have h2 := abs_log_integral_exp_sub_cumulantSum_le (boxMeasure ν₁ (pv.box b))
    (pv.measurable_boxSum b x (pv.pieces b \ D)) hM (pv.abs_boxSum_le b x (s := pv.pieces b \ D) Finset.sdiff_subset) t
  have hsplit : cumulantSum (boxMeasure ν₁ (pv.box b)) (pv.boxSum b x (pv.pieces b)) t =
      pv.boxGain ν₁ t D b + cumulantSum (boxMeasure ν₁ (pv.box b)) (pv.boxSum b x (pv.pieces b \ D)) t := by
    unfold Pavement.boxGain cumulantSum
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkt⟩ := Finset.mem_Icc.mp hk
    rw [pv.box_truncExp_split ν₁ t b x hk1 hkt D hD]
    ring
  rw [Pavement.boxError] at *
  rw [abs_le] at h1 h2
  linarith [h1.1, h2.2]

end GaussianBlockSpin
