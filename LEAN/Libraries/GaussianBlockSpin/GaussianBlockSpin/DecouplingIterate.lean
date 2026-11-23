import GaussianBlockSpin.DecouplingStep

/-! The iteration of the decoupling step over several pavements ([2], p. 154: "after `d + 1` steps ... the trivial case
`H_J = 0`"): restricting the pieces to a sub-family, the gains of one step sum to the difference of the cumulant sums,
and if every piece is deep for one of the pavements, telescoping gives
`log ∫ e^F ≥ Σ_{k=1}^t ⟨F^k⟩^T/k! - 2 Σ_j Σ_b ε^{(j)}_b`. -/

namespace GaussianBlockSpin

open MeasureTheory Function
open scoped ENNReal Nat

variable {ι P β : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β]
variable {L : LocalPieces ι P} (pv : Pavement L β)
variable (ν₁ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν₁ i)]

/-- **The gains of one step**: `Σ_b δ_b = Σ_{k=1}^t (⟨F^k⟩^T - ⟨(F - F^D)^k⟩^T)/k!`. -/
theorem Pavement.sum_boxGain (t : ℕ) (D : Finset P) (hD : ∀ X ∈ D, pv.IsDeep t X) :
    ∑ b, pv.boxGain ν₁ t D b =
      cumulantSum (Measure.pi ν₁) (L.sum Finset.univ) t - cumulantSum (Measure.pi ν₁) (L.sum (Finset.univ \ D)) t := by
  unfold Pavement.boxGain cumulantSum
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hkt⟩ := Finset.mem_Icc.mp hk
  rw [← sub_div, pv.truncExp_sub_eq_sum_boxes ν₁ t hk1 hkt D hD, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sub_div]

/-- The pieces of a sub-family `S` (the others replaced by `0`). -/
def LocalPieces.restrict (L : LocalPieces ι P) (S : Finset P) : LocalPieces ι P where
  supp X := if X ∈ S then L.supp X else ∅
  h X := if X ∈ S then L.h X else 0
  a X := if X ∈ S then L.a X else 0
  loc X := by
    by_cases hX : X ∈ S
    · simpa [hX] using L.loc X
    · simp only [hX, ↓reduceIte]; intro _ _ _; rfl
  meas X := by
    by_cases hX : X ∈ S
    · simpa [hX] using L.meas X
    · simp only [hX, ↓reduceIte]; exact measurable_const
  bdd X ω := by
    by_cases hX : X ∈ S
    · simpa [hX] using L.bdd X ω
    · simp [hX]

omit [Fintype ι] [DecidableEq ι] [Fintype P] in
lemma LocalPieces.restrict_supp_subset (S : Finset P) (X : P) : (L.restrict S).supp X ⊆ L.supp X := by
  show (if X ∈ S then L.supp X else ∅) ⊆ L.supp X
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] [Fintype P] in
lemma LocalPieces.restrict_sum (S T : Finset P) : (L.restrict S).sum T = L.sum (T ∩ S) := by
  funext ω
  show ∑ X ∈ T, (if X ∈ S then L.h X else 0) ω = ∑ X ∈ T ∩ S, L.h X ω
  rw [← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs <;> rfl

/-- The pavement for the sub-family. -/
def Pavement.restrict (S : Finset P) : Pavement (L.restrict S) β where
  Γ := pv.Γ
  box := pv.box
  disj := pv.disj
  disjΓ := pv.disjΓ
  home := pv.home
  homeNone X hX := (L.restrict_supp_subset S X).trans (pv.homeNone X hX)
  homeSome X b hX := (Finset.coe_subset.mpr (L.restrict_supp_subset S X)).trans (pv.homeSome X b hX)

omit [Fintype ι] [Fintype P] [Fintype β] [DecidableEq β] in
/-- Deep pieces stay deep in a sub-family. -/
lemma Pavement.IsDeep.restrict {t : ℕ} {X : P} (S : Finset P) (hX : pv.IsDeep t X) : (pv.restrict S).IsDeep t X := by
  obtain ⟨hhome, hΓ, hdeep⟩ := hX
  refine ⟨hhome, Finset.disjoint_of_subset_left (L.restrict_supp_subset S X) hΓ, fun k hk g i₀ hgi => ?_⟩
  obtain ⟨C, hC0, hCin, hCdisj⟩ := hdeep k hk g i₀ hgi
  refine ⟨C, hC0, fun i hi => ⟨Finset.disjoint_of_subset_left (L.restrict_supp_subset S _) (hCin i hi).1,
    (hCin i hi).2⟩, ?_⟩
  refine Finset.disjoint_of_subset_left ?_ (Finset.disjoint_of_subset_right ?_ hCdisj)
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨i, hi, L.restrict_supp_subset S _ hzi⟩
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hzi
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr ⟨L.restrict_supp_subset S _ hz1, hz2⟩⟩

omit [Fintype ι] [DecidableEq ι] [Fintype β] in
/-- The box errors of a sub-family are at most those of the whole family. -/
lemma Pavement.boxError_restrict_le (t : ℕ) (S : Finset P) (b : β) :
    (pv.restrict S).boxError t b ≤ pv.boxError t b := by
  unfold Pavement.boxError
  have hm0 : 0 ≤ (pv.restrict S).mass b := Finset.sum_nonneg fun X _ => (L.restrict S).a_nonneg X
  have hm : (pv.restrict S).mass b ≤ pv.mass b := by
    unfold Pavement.mass
    refine Finset.sum_le_sum fun X _ => ?_
    show (if X ∈ S then L.a X else 0) ≤ L.a X
    split_ifs
    · exact le_rfl
    · exact L.a_nonneg X
  have hc := cumBound_nonneg (t + 1)
  gcongr

omit [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] [∀ i, IsProbabilityMeasure (ν₁ i)] in
/-- The truncated expectations of the zero function vanish. -/
lemma truncExp_moments_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    truncExp (moments μ (fun _ : Ω => (0 : ℝ))) n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [truncExp]
    · rw [truncExp]
      have h1 : moments μ (fun _ : Ω => (0 : ℝ)) (n + 1) = 0 := by simp [moments]
      rw [h1, zero_sub, neg_eq_zero]
      exact Finset.sum_eq_zero fun j _ => by rw [ih (j + 1) (by omega)]; ring

/-- **The iterated decoupling**: if every piece is deep for one of the pavements `pvs 0, …, pvs (m-1)`, then
`exp(Σ_{k=1}^t ⟨F^k⟩^T/k! - 2 Σ_{j<m} Σ_b ε^{(j)}_b) ≤ ∫ e^F` for the product measure. -/
theorem lintegral_exp_ge_iterate (t : ℕ) {m : ℕ} (pvs : ℕ → Pavement L β)
    (hcover : ∀ X, ∃ j < m, (pvs j).IsDeep t X) :
    ENNReal.ofReal (Real.exp (cumulantSum (Measure.pi ν₁) (L.sum Finset.univ) t -
        2 * ∑ j ∈ Finset.range m, ∑ b, (pvs j).boxError t b)) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum Finset.univ ω)) ∂(Measure.pi ν₁) := by
  classical
  set S : ℕ → Finset P := fun j => Finset.univ.filter fun X => ∀ i < j, ¬ (pvs i).IsDeep t X with hS
  set D : ℕ → Finset P := fun j => Finset.univ.filter fun X => (pvs j).IsDeep t X with hD
  have hS0 : S 0 = Finset.univ := by ext X; simp [hS]
  have hSm : S m = ∅ := by
    ext X
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_forall,
      not_not]
    obtain ⟨j, hj, hX⟩ := hcover X
    exact ⟨j, hj, hX⟩
  have hSsucc : ∀ j, (Finset.univ \ D j) ∩ S j = S (j + 1) := by
    intro j
    ext X
    simp only [hS, hD, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h j (Nat.lt_succ_self j), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩
  -- one step on the sub-family `S j`
  have hstep : ∀ j, ENNReal.ofReal (Real.exp (cumulantSum (Measure.pi ν₁) (L.sum (S j)) t -
      cumulantSum (Measure.pi ν₁) (L.sum (S (j + 1))) t - 2 * ∑ b, (pvs j).boxError t b)) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum (S (j + 1)) ω)) ∂(Measure.pi ν₁) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum (S j) ω)) ∂(Measure.pi ν₁) := by
    intro j
    set pvj := (pvs j).restrict (S j)
    have hDj : ∀ X ∈ D j, pvj.IsDeep t X := fun X hX =>
      Pavement.IsDeep.restrict (pvs j) (S j) (Finset.mem_filter.mp hX).2
    have h := pvj.lintegral_exp_step ν₁ t (D j) hDj
    have hg := pvj.sum_boxGain ν₁ t (D j) hDj
    simp only [LocalPieces.restrict_sum, Finset.univ_inter, hSsucc] at h hg
    rw [Finset.sum_sub_distrib, hg, ← Finset.mul_sum] at h
    refine le_trans ?_ h
    have : ∑ b, pvj.boxError t b ≤ ∑ b, (pvs j).boxError t b :=
      Finset.sum_le_sum fun b _ => (pvs j).boxError_restrict_le t (S j) b
    gcongr
  -- telescoping
  have hind : ∀ j ≤ m, ENNReal.ofReal (Real.exp (cumulantSum (Measure.pi ν₁) (L.sum (S 0)) t -
      cumulantSum (Measure.pi ν₁) (L.sum (S j)) t - 2 * ∑ i ∈ Finset.range j, ∑ b, (pvs i).boxError t b)) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum (S j) ω)) ∂(Measure.pi ν₁) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum (S 0) ω)) ∂(Measure.pi ν₁) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      refine le_trans ?_ (ih (by omega))
      calc ENNReal.ofReal (Real.exp (cumulantSum (Measure.pi ν₁) (L.sum (S 0)) t -
            cumulantSum (Measure.pi ν₁) (L.sum (S (j + 1))) t -
            2 * ∑ i ∈ Finset.range (j + 1), ∑ b, (pvs i).boxError t b)) *
            ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum (S (j + 1)) ω)) ∂(Measure.pi ν₁)
          = ENNReal.ofReal (Real.exp (cumulantSum (Measure.pi ν₁) (L.sum (S 0)) t -
              cumulantSum (Measure.pi ν₁) (L.sum (S j)) t -
              2 * ∑ i ∈ Finset.range j, ∑ b, (pvs i).boxError t b)) *
            (ENNReal.ofReal (Real.exp (cumulantSum (Measure.pi ν₁) (L.sum (S j)) t -
              cumulantSum (Measure.pi ν₁) (L.sum (S (j + 1))) t - 2 * ∑ b, (pvs j).boxError t b)) *
            ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum (S (j + 1)) ω)) ∂(Measure.pi ν₁)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Finset.sum_range_succ]
            congr 3
            ring
        _ ≤ _ := by gcongr; exact hstep j
  have hm := hind m le_rfl
  have hzero : L.sum (S m) = fun _ => 0 := by rw [hSm]; funext ω; simp [LocalPieces.sum]
  have hcs0 : cumulantSum (Measure.pi ν₁) (fun _ : ι → ℝ => (0 : ℝ)) t = 0 := by
    rw [cumulantSum]
    exact Finset.sum_eq_zero fun k _ => by rw [truncExp_moments_zero]; simp
  rw [hzero, hcs0, sub_zero, hS0] at hm
  simpa using hm

end GaussianBlockSpin
