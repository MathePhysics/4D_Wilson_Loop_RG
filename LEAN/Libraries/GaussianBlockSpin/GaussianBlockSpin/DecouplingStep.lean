import GaussianBlockSpin.BoxInequality

/-! **One decoupling step** of the cumulant expansion for independent coordinates (the step of [2], Sect. 5, from
(5.12) to (5.35), with the Markov property replaced by the product structure): for a pavement and a set `D` of deep
pieces, `∫ e^F ≥ exp(Σ_b (δ_b - 2 ε_b)) ∫ e^{F - F^D}` (lintegral_exp_step), with `δ_b = boxGain` and
`ε_b = boxError`. DecouplingIterate identifies `Σ_b δ_b = Σ_{k=1}^t (⟨F^k⟩^T - ⟨(F - F^D)^k⟩^T)/k!` (sum_boxGain). -/

namespace GaussianBlockSpin

open MeasureTheory Function
open scoped ENNReal Nat

variable {ι P β : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β]
variable {L : LocalPieces ι P} (pv : Pavement L β)
variable (ν₁ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν₁ i)]

omit [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] in
lemma LocalPieces.dependsOn_sum (s : Finset P) {R : Set ι} (hR : ∀ X ∈ s, (L.supp X : Set ι) ⊆ R) :
    DependsOn (L.sum s) R := by
  intro ω ω' h
  exact Finset.sum_congr rfl fun X hX => L.loc X fun i hi => h i (hR X hX hi)

omit [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] in
lemma LocalPieces.measurable_sum (s : Finset P) : Measurable (L.sum s) :=
  Finset.measurable_sum _ fun X _ => L.meas X

omit [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] in
/-- A sum of pieces split by home box. -/
lemma Pavement.sum_split (s : Finset P) (ω : ι → ℝ) :
    L.sum s ω = L.sum (s.filter fun X => pv.home X = none) ω +
      ∑ b, L.sum (s.filter fun X => pv.home X = some b) ω := by
  unfold LocalPieces.sum
  rw [← Finset.sum_fiberwise s pv.home (fun X => L.h X ω), Fintype.sum_option]

omit [Fintype ι] [DecidableEq P] [Fintype β] in
/-- The partial integral over box `b` of `e^{Σ_{X ∈ s} h_X}` is `∫ e^{boxSum} dμ_b`. -/
lemma Pavement.lmarginal_exp_eq (b : β) (x : ι → ℝ) {s : Finset P} (hs : s ⊆ pv.pieces b) :
    (∫⋯∫⁻_(pv.box b), (fun ω => ENNReal.ofReal (Real.exp (L.sum s ω))) ∂ν₁) x =
      ENNReal.ofReal (∫ y, Real.exp (pv.boxSum b x s y) ∂(boxMeasure ν₁ (pv.box b))) := by
  have hint : Integrable (fun y => Real.exp (pv.boxSum b x s y)) (boxMeasure ν₁ (pv.box b)) := by
    refine Integrable.of_bound ((pv.measurable_boxSum b x s).exp).aestronglyMeasurable (Real.exp (pv.mass b))
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (pv.abs_boxSum_le b x hs y))
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)]
  rfl

omit [Fintype β] in
/-- **The box inequality in partial-integral form**. -/
lemma Pavement.lmarginal_box_ge (t : ℕ) (b : β) (x : ι → ℝ) (D : Finset P) (hD : ∀ X ∈ D, pv.IsDeep t X) :
    ENNReal.ofReal (Real.exp (pv.boxGain ν₁ t D b - 2 * pv.boxError t b)) *
        (∫⋯∫⁻_(pv.box b), (fun ω => ENNReal.ofReal (Real.exp (L.sum (pv.pieces b \ D) ω))) ∂ν₁) x ≤
      (∫⋯∫⁻_(pv.box b), (fun ω => ENNReal.ofReal (Real.exp (L.sum (pv.pieces b) ω))) ∂ν₁) x := by
  rw [pv.lmarginal_exp_eq ν₁ b x subset_rfl, pv.lmarginal_exp_eq ν₁ b x Finset.sdiff_subset,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : ∀ s : Finset P, s ⊆ pv.pieces b → 0 < ∫ y, Real.exp (pv.boxSum b x s y) ∂(boxMeasure ν₁ (pv.box b)) := by
    intro s hs
    refine integral_exp_pos ?_
    refine Integrable.of_bound ((pv.measurable_boxSum b x s).exp).aestronglyMeasurable (Real.exp (pv.mass b))
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (pv.abs_boxSum_le b x hs y))
  have h := pv.log_box_ge ν₁ t b x D hD
  have h1 := hpos _ subset_rfl
  have h2 := hpos _ (Finset.sdiff_subset (s := pv.pieces b) (t := D))
  rw [← Real.exp_le_exp, Real.exp_log h1] at h
  calc Real.exp (pv.boxGain ν₁ t D b - 2 * pv.boxError t b) *
        ∫ y, Real.exp (pv.boxSum b x (pv.pieces b \ D) y) ∂(boxMeasure ν₁ (pv.box b))
      = Real.exp (pv.boxGain ν₁ t D b + Real.log (∫ y, Real.exp (pv.boxSum b x (pv.pieces b \ D) y)
          ∂(boxMeasure ν₁ (pv.box b))) - 2 * pv.boxError t b) := by
        rw [show pv.boxGain ν₁ t D b + Real.log (∫ y, Real.exp (pv.boxSum b x (pv.pieces b \ D) y)
          ∂(boxMeasure ν₁ (pv.box b))) - 2 * pv.boxError t b = (pv.boxGain ν₁ t D b - 2 * pv.boxError t b) +
          Real.log (∫ y, Real.exp (pv.boxSum b x (pv.pieces b \ D) y) ∂(boxMeasure ν₁ (pv.box b))) by ring,
          Real.exp_add, Real.exp_log h2]
    _ ≤ _ := h

omit [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] in
/-- `e^{Σ_{X ∈ s} h_X}` as the corridor factor times the box factors. -/
lemma Pavement.exp_sum_split (s : Finset P) (ω : ι → ℝ) :
    ENNReal.ofReal (Real.exp (L.sum s ω)) =
      ENNReal.ofReal (Real.exp (L.sum (s.filter fun X => pv.home X = none) ω)) *
        ∏ b, ENNReal.ofReal (Real.exp (L.sum (s.filter fun X => pv.home X = some b) ω)) := by
  rw [pv.sum_split s ω, Real.exp_add, Real.exp_sum, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_prod_of_nonneg fun b _ => (Real.exp_pos _).le]

/-- **One decoupling step**: `∫ e^F ≥ exp(Σ_b (δ_b - 2 ε_b)) ∫ e^{F - F^D}` (lower integrals). -/
theorem Pavement.lintegral_exp_step (t : ℕ) (D : Finset P) (hD : ∀ X ∈ D, pv.IsDeep t X) :
    ENNReal.ofReal (Real.exp (∑ b, (pv.boxGain ν₁ t D b - 2 * pv.boxError t b))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum (Finset.univ \ D) ω)) ∂(Measure.pi ν₁) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (L.sum Finset.univ ω)) ∂(Measure.pi ν₁) := by
  set c := ENNReal.ofReal (Real.exp (∑ b, (pv.boxGain ν₁ t D b - 2 * pv.boxError t b))) with hc
  set Γp := Finset.univ.filter fun X => pv.home X = none with hΓp
  set B := Finset.univ.biUnion pv.box with hB
  set gΓ : (ι → ℝ) → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (L.sum Γp ω)) with hgΓ
  set g : β → (ι → ℝ) → ℝ≥0∞ := fun b ω => ENNReal.ofReal (Real.exp (L.sum (pv.pieces b) ω)) with hg
  set g' : β → (ι → ℝ) → ℝ≥0∞ := fun b ω => ENNReal.ofReal (Real.exp (L.sum (pv.pieces b \ D) ω)) with hg'
  have mexp : ∀ s : Finset P, Measurable fun ω => ENNReal.ofReal (Real.exp (L.sum s ω)) := fun s =>
    ENNReal.measurable_ofReal.comp (L.measurable_sum s).exp
  -- the two integrands in product form
  have hf : (fun ω => ENNReal.ofReal (Real.exp (L.sum Finset.univ ω))) = fun ω => gΓ ω * ∏ b, g b ω := by
    funext ω
    rw [pv.exp_sum_split Finset.univ ω]
    rfl
  have hDsome : ∀ X ∈ D, pv.home X ≠ none := fun X hX h => by
    obtain ⟨⟨b, hb⟩, -⟩ := hD X hX
    rw [hb] at h; exact Option.some_ne_none b h
  have hf' : (fun ω => c * ENNReal.ofReal (Real.exp (L.sum (Finset.univ \ D) ω))) =
      fun ω => (c * gΓ ω) * ∏ b, g' b ω := by
    funext ω
    rw [pv.exp_sum_split (Finset.univ \ D) ω, mul_assoc]
    have h1 : (Finset.univ \ D).filter (fun X => pv.home X = none) = Γp := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, hΓp]
      exact ⟨fun h => h.2, fun h => ⟨fun hX => hDsome X hX h, h⟩⟩
    have h2 : ∀ b, (Finset.univ \ D).filter (fun X => pv.home X = some b) = pv.pieces b \ D := fun b => by
      ext X
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Pavement.pieces]
      tauto
    simp_rw [h1, h2]
    rfl
  -- dependencies
  have hΓB : ∀ b, Disjoint (pv.box b : Set ι) (pv.Γ : Set ι) := fun b => Finset.disjoint_coe.mpr (pv.disjΓ b)
  have hdepΓ : DependsOn gΓ (((B : Finset ι) : Set ι)ᶜ) := by
    intro ω ω' h
    have : L.sum Γp ω = L.sum Γp ω' := L.dependsOn_sum Γp (R := ((B : Finset ι) : Set ι)ᶜ) (fun X hX i hi => ?_) h
    · simp only [hgΓ, this]
    · intro hiB
      obtain ⟨b, -, hib⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hiB)
      have hX' := pv.homeNone X (Finset.mem_filter.mp hX).2 (Finset.mem_coe.mp hi)
      exact Finset.disjoint_left.mp (pv.disjΓ b) hib hX'
  have hdep : ∀ (s : β → Finset P), (∀ b, s b ⊆ pv.pieces b) →
      ∀ b, DependsOn (fun ω => ENNReal.ofReal (Real.exp (L.sum (s b) ω))) ((pv.box b : Set ι) ∪ (pv.Γ : Set ι)) := by
    intro s hs b ω ω' h
    have : L.sum (s b) ω = L.sum (s b) ω' := L.dependsOn_sum (s b) (fun X hX =>
      pv.homeSome X b (Finset.mem_filter.mp (hs b hX)).2) h
    simp only [this]
  have hpd : ((Finset.univ : Finset β) : Set β).PairwiseDisjoint pv.box := fun b _ b' _ hbb' => pv.disj b b' hbb'
  have hmarg : ∀ (s : β → Finset P), (∀ b, s b ⊆ pv.pieces b) → ∀ (e : (ι → ℝ) → ℝ≥0∞),
      DependsOn e (((B : Finset ι) : Set ι)ᶜ) →
      ∫⋯∫⁻_B, (fun ω => e ω * ∏ b, ENNReal.ofReal (Real.exp (L.sum (s b) ω))) ∂ν₁ =
        fun x => e x * ∏ b, (∫⋯∫⁻_(pv.box b), (fun ω => ENNReal.ofReal (Real.exp (L.sum (s b) ω))) ∂ν₁) x := by
    intro s hs e he
    rw [lmarginal_mul_left ν₁ he (Finset.measurable_prod _ fun b _ => mexp (s b))]
    rw [hB, lmarginal_prod_boxes ν₁ pv.box (pv.Γ : Set ι) hΓB
      (fun b ω => ENNReal.ofReal (Real.exp (L.sum (s b) ω))) (hdep s hs) (fun b => mexp (s b)) Finset.univ hpd]
  have hdepc : DependsOn (fun ω => c * gΓ ω) (((B : Finset ι) : Set ι)ᶜ) := by
    intro ω ω' h
    simp only [hdepΓ h]
  -- the comparison of the partial integrals over all boxes
  have hle : ∫⋯∫⁻_B, (fun ω => (c * gΓ ω) * ∏ b, g' b ω) ∂ν₁ ≤ ∫⋯∫⁻_B, (fun ω => gΓ ω * ∏ b, g b ω) ∂ν₁ := by
    rw [hmarg (fun b => pv.pieces b \ D) (fun b => Finset.sdiff_subset) _ hdepc,
      hmarg (fun b => pv.pieces b) (fun b => subset_rfl) _ hdepΓ]
    intro x
    have hcprod : c = ∏ b, ENNReal.ofReal (Real.exp (pv.boxGain ν₁ t D b - 2 * pv.boxError t b)) := by
      rw [hc, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun b _ => (Real.exp_pos _).le]
    dsimp only
    rw [mul_comm c (gΓ x), mul_assoc, hcprod, ← Finset.prod_mul_distrib]
    gcongr with b
    exact pv.lmarginal_box_ge ν₁ t b x D hD
  have hmf : Measurable fun ω => gΓ ω * ∏ b, g b ω := by
    rw [← hf]; exact mexp _
  have hmf' : Measurable fun ω => (c * gΓ ω) * ∏ b, g' b ω := by
    rw [← hf']; exact (mexp _).const_mul c
  have := lintegral_le_of_lmarginal_le B hmf' hmf hle
  rw [← hf, ← hf'] at this
  rwa [lintegral_const_mul c (mexp _)] at this

end GaussianBlockSpin
