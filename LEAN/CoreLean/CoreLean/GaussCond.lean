/-
**`lem:gaussian-conditioning`** of BALABAN_CORE.tex (`a021c13be348`). `E = E₁ ⊕ E₂` is `ℝ^{ι₁ ⊕ ι₂}`, `Γ` positive
definite with the blocks `Γ_{ij}`, `C = Γ⁻¹`, `C₁ = Γ₁₁⁻¹`, `T : E' → E` with `TTᵀ = C`, `μ₀` the standard Gaussian
measure on `E' = ℝ^{ι'}`, `μ_C` the Gaussian measure of the covariance `C`. For every bounded Borel `F` on `E₁`,
`∫F(A₁)dμ_C(A) = ∫e^{-½⟨Γ₁₂(TX)₂, C₁Γ₁₂(TX)₂⟩}∫e^{-⟨A₁, Γ₁₂(TX)₂⟩}F(A₁)dν_{Γ₁₁}(A₁)dμ₀(X)`.
Proof: `μ_C` has the density `det(Γ/2π)^{1/2}e^{-½⟨A, ΓA⟩}` and is the image of `μ₀` under `T` (`GaussDensity.lean`);
`⟨A, ΓA⟩ = ⟨A₁, Γ₁₁A₁⟩ + 2⟨A₁, Γ₁₂A₂⟩ + ⟨A₂, Γ₂₂A₂⟩`; by Fubini both sides are `∫m(A₂)h(A₂)dA₂` with the marginal
density `m` of `A₂`, the inner integral over `A₁` being evaluated by `eq:complex-gaussian` for `F = 1`.
-/
import CoreLean.GaussDensity

open Matrix Complex MeasureTheory Real ProbabilityTheory WithLp
open scoped RealInnerProductSpace

noncomputable section

namespace CoreLean
namespace ComplexGauss

variable {ι₁ ι₂ ι' : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι'] [DecidableEq ι₁] [DecidableEq ι₂]

/-- The real Gaussian with a linear term is integrable. -/
lemma integrable_gauss_lin {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (w : ι → ℝ) : Integrable fun x : ι → ℝ => Real.exp (-(1 / 2) * (x ⬝ᵥ (M *ᵥ x)) - x ⬝ᵥ w) := by
  obtain ⟨c, hc, hlow⟩ := posDef_lower hM
  refine (integrable_dom (half_pos hc) (Real.exp (Fintype.card ι * ((‖w‖ ^ 2) / (c / 2))))).mono'
    (Real.continuous_exp.comp ((continuous_const.mul (continuous_quad M)).sub
      (continuous_id.dotProduct continuous_const))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hlin : -(x ⬝ᵥ w) ≤ ‖w‖ * l1 x := by
    unfold dotProduct l1
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have := norm_le_pi_norm w i
      rw [Real.norm_eq_abs] at this
      nlinarith [neg_abs_le (x i * w i), abs_mul (x i) (w i), abs_nonneg (x i)]
  have := dom_le (half_pos hc) ‖w‖ x
  refine le_trans (Real.exp_le_exp.2 ?_) this
  have h1 := hlow x
  have h2 := nsq_nonneg x
  nlinarith

/-- **The block expansion** `⟨A, ΓA⟩ = ⟨A₁, Γ₁₁A₁⟩ + 2⟨A₁, Γ₁₂A₂⟩ + ⟨A₂, Γ₂₂A₂⟩` for symmetric `Γ`. -/
lemma quad_split (Γ : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ) (hΓ : Γᵀ = Γ) (a : ι₁ → ℝ) (b : ι₂ → ℝ) :
    Sum.elim a b ⬝ᵥ (Γ *ᵥ Sum.elim a b) = a ⬝ᵥ (Γ.submatrix Sum.inl Sum.inl *ᵥ a) +
      2 * (a ⬝ᵥ (Γ.submatrix Sum.inl Sum.inr *ᵥ b)) + b ⬝ᵥ (Γ.submatrix Sum.inr Sum.inr *ᵥ b) := by
  have hsym : ∀ i j, Γ (Sum.inr j) (Sum.inl i) = Γ (Sum.inl i) (Sum.inr j) := fun i j => by
    rw [← transpose_apply Γ (Sum.inl i) (Sum.inr j), hΓ]
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, submatrix_apply, mul_add,
    Finset.sum_add_distrib, hsym]
  have hcross : ∑ j, b j * ∑ i, Γ (Sum.inl i) (Sum.inr j) * a i = ∑ i, a i * ∑ j, Γ (Sum.inl i) (Sum.inr j) * b j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hcross]; ring

variable (Γ : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ)

/-- The block `Γ₁₁`. -/
abbrev G11 : Matrix ι₁ ι₁ ℝ := Γ.submatrix Sum.inl Sum.inl
/-- The block `Γ₁₂`. -/
abbrev G12 : Matrix ι₁ ι₂ ℝ := Γ.submatrix Sum.inl Sum.inr
/-- The block `Γ₂₂`. -/
abbrev G22 : Matrix ι₂ ι₂ ℝ := Γ.submatrix Sum.inr Sum.inr

/-- `∫e^{-⟨A₁, w⟩}F(A₁)dν_{Γ₁₁}(A₁)`. -/
def nuI (w : ι₁ → ℝ) (F : (ι₁ → ℝ) → ℂ) : ℂ :=
  ∫ a, (root (cM (G11 Γ)) * cexp (-(1 / 2) * qf (cM (G11 Γ)) a - cV a ⬝ᵥ cV w)) * F a

/-- The conditional integrand `h(A₂) = e^{-½⟨w, C₁w⟩}∫e^{-⟨A₁, w⟩}F(A₁)dν_{Γ₁₁}(A₁)`, `w = Γ₁₂A₂`. -/
def hcond (F : (ι₁ → ℝ) → ℂ) (b : ι₂ → ℝ) : ℂ :=
  cexp (-(1 / 2) * (((G12 Γ *ᵥ b) ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ (G12 Γ *ᵥ b)) : ℝ) : ℂ)) * nuI Γ (G12 Γ *ᵥ b) F

variable {Γ}

lemma G11_posDef (hΓ : Γ.PosDef) : (G11 Γ).PosDef := hΓ.submatrix Sum.inl_injective

/-- `ν_{Γ₁₁}` integrates `e^{-⟨A₁, w⟩}` to `e^{½⟨w, C₁w⟩}`. -/
lemma nuI_one (hΓ : Γ.PosDef) (w : ι₁ → ℝ) :
    nuI Γ w (fun _ => 1) = cexp (1 / 2 * ((w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w) : ℝ) : ℂ)) := by
  have hQ := cM_mem_of_posDef (G11_posDef hΓ)
  have h := complex_gaussian hQ (cV w)
  unfold nuI
  simp only [mul_one]
  rw [integral_const_mul]
  unfold Zv at h
  rw [h, cM_inv (G11_posDef hΓ).det_pos.ne', ← cV_mulVec, dot_cV]

/-- The real form of the integrand of `ν_{Γ₁₁}`. -/
lemma nu_integrand (hΓ : Γ.PosDef) (w a : ι₁ → ℝ) :
    root (cM (G11 Γ)) * cexp (-(1 / 2) * qf (cM (G11 Γ)) a - cV a ⬝ᵥ cV w) =
      (((root (cM (G11 Γ))).re * Real.exp (-(1 / 2) * (a ⬝ᵥ (G11 Γ *ᵥ a)) - a ⬝ᵥ w) : ℝ) : ℂ) := by
  conv_lhs => rw [(root_re_pos (G11_posDef hΓ)).2]
  rw [qf_cM, dot_cV, Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast; ring_nf

lemma norm_nuI_le (hΓ : Γ.PosDef) (w : ι₁ → ℝ) {F : (ι₁ → ℝ) → ℂ} (hFm : AEStronglyMeasurable F volume) {B : ℝ}
    (hFb : ∀ a, ‖F a‖ ≤ B) :
    ‖nuI Γ w F‖ ≤ B * Real.exp (1 / 2 * (w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w))) := by
  have hs := (root_re_pos (G11_posDef hΓ)).1
  obtain ⟨s, hs0, hs2, hval⟩ := real_gauss (cM_mem_of_posDef (G11_posDef hΓ)) w
  have hsr : s = (root (cM (G11 Γ))).re := by
    obtain ⟨s', hs', hrs'⟩ := root_real (cM_mem_of_posDef (G11_posDef hΓ))
    have e1 := (root_re_pos (G11_posDef hΓ)).2
    -- both are the positive square root of `det(Γ₁₁/2π)`
    have h2 := root_sq (cM_mem_of_posDef (G11_posDef hΓ))
    rw [e1, det_smul, det_cM] at h2
    have h3 := congrArg Complex.re h2
    have e : ((2 * π : ℂ)⁻¹ ^ Fintype.card ι₁ * ((G11 Γ).det : ℂ)) =
        (((2 * π)⁻¹ ^ Fintype.card ι₁ * (G11 Γ).det : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.ofReal_re, ← Complex.ofReal_pow, Complex.ofReal_re, ← hs2] at h3
    nlinarith [sq_nonneg (s - (root (cM (G11 Γ))).re), sq_nonneg (s + (root (cM (G11 Γ))).re)]
  have hint := integrable_gauss_lin (G11_posDef hΓ) w
  have hB : 0 ≤ B := (norm_nonneg _).trans (hFb 0)
  unfold nuI
  simp_rw [nu_integrand hΓ w]
  calc ‖∫ a, ((((root (cM (G11 Γ))).re * Real.exp (-(1 / 2) * (a ⬝ᵥ (G11 Γ *ᵥ a)) - a ⬝ᵥ w) : ℝ) : ℂ)) * F a‖
      ≤ ∫ a, (root (cM (G11 Γ))).re * Real.exp (-(1 / 2) * (a ⬝ᵥ (G11 Γ *ᵥ a)) - a ⬝ᵥ w) * B := by
        refine norm_integral_le_of_norm_le ((hint.const_mul _).mul_const _) (Filter.Eventually.of_forall fun a => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hFb a) (by positivity)
    _ = (root (cM (G11 Γ))).re * (Real.exp (1 / 2 * (w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w))) / s) * B := by
        rw [integral_mul_const, integral_const_mul, hval]
    _ = B * Real.exp (1 / 2 * (w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w))) := by
        rw [← hsr]; field_simp

lemma norm_hcond_le (hΓ : Γ.PosDef) {F : (ι₁ → ℝ) → ℂ} (hFm : AEStronglyMeasurable F volume) {B : ℝ}
    (hFb : ∀ a, ‖F a‖ ≤ B) (b : ι₂ → ℝ) : ‖hcond Γ F b‖ ≤ B := by
  unfold hcond
  rw [norm_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, Complex.norm_exp_ofReal]
  refine (mul_le_mul_of_nonneg_left (norm_nuI_le hΓ _ hFm hFb) (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [mul_left_comm, ← Real.exp_add]
  simp

lemma measurable_nuI (F : (ι₁ → ℝ) → ℂ) (hFm : Measurable F) :
    StronglyMeasurable fun b : ι₂ → ℝ => nuI Γ (G12 Γ *ᵥ b) F := by
  unfold nuI
  refine StronglyMeasurable.integral_prod_right (f := fun (b : ι₂ → ℝ) (a : ι₁ → ℝ) =>
    (root (cM (G11 Γ)) * cexp (-(1 / 2) * qf (cM (G11 Γ)) a - cV a ⬝ᵥ cV (G12 Γ *ᵥ b))) * F a) ?_
  refine Measurable.stronglyMeasurable (Measurable.mul ?_ (hFm.comp measurable_snd))
  refine Continuous.measurable (continuous_const.mul (Complex.continuous_exp.comp ?_))
  simp only [qf, dotProduct, mulVec, cV]
  fun_prop

/-- **The identity for the density**: `∫ρ(A)F(A₁)dA = ∫ρ(A)h(A₂)dA`. -/
theorem density_conditioning (hΓ : Γ.PosDef) (F : (ι₁ → ℝ) → ℂ) (hFm : Measurable F) {B : ℝ}
    (hFb : ∀ a, ‖F a‖ ≤ B) :
    ∫ x, (gdens Γ x : ℂ) * F (fun i => x (Sum.inl i)) = ∫ x, (gdens Γ x : ℂ) * hcond Γ F (fun j => x (Sum.inr j)) := by
  have hsymm : Γᵀ = Γ := by
    have := hΓ.1; unfold Matrix.IsHermitian at this; rwa [conjTranspose_eq_transpose_of_trivial] at this
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ) with he
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι₁ ⊕ ι₂ => ℝ)
  have hsplit : ∀ (a : ι₁ → ℝ) (b : ι₂ → ℝ), e.symm (a, b) = Sum.elim a b := fun a b => by
    funext k; cases k <;> rfl
  -- integrability on `E`
  have hgint := integrable_gdens hΓ
  have hB : 0 ≤ B := (norm_nonneg _).trans (hFb 0)
  have hint1 : Integrable fun x : ι₁ ⊕ ι₂ → ℝ => (gdens Γ x : ℂ) * F (fun i => x (Sum.inl i)) := by
    refine (hgint.ofReal.mul_const (B : ℂ)).norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_ofReal.comp (continuous_gdens Γ)).aestronglyMeasurable.mul
        (hFm.comp (continuous_pi fun i => continuous_apply _).measurable).aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul (le_of_eq (by simp)) ((hFb _).trans (le_abs_self B)) (norm_nonneg _) (norm_nonneg _)
  have hHm : StronglyMeasurable (hcond Γ F) := by
    unfold hcond
    refine StronglyMeasurable.mul ?_ (measurable_nuI F hFm)
    refine Continuous.stronglyMeasurable (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp ?_)))
    simp only [dotProduct, mulVec]
    fun_prop
  have hint2 : Integrable fun x : ι₁ ⊕ ι₂ → ℝ => (gdens Γ x : ℂ) * hcond Γ F (fun j => x (Sum.inr j)) := by
    refine (hgint.ofReal.mul_const (B : ℂ)).norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_ofReal.comp (continuous_gdens Γ)).aestronglyMeasurable.mul
        (hHm.measurable.comp (continuous_pi fun j => continuous_apply _).measurable).aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul (le_of_eq (by simp)) ((norm_hcond_le hΓ hFm.aestronglyMeasurable hFb _).trans
        (le_abs_self B)) (norm_nonneg _) (norm_nonneg _)
  -- transport to `E₁ × E₂` and Fubini
  set f1 := fun x : ι₁ ⊕ ι₂ → ℝ => (gdens Γ x : ℂ) * F (fun i => x (Sum.inl i)) with hf1
  set f2 := fun x : ι₁ ⊕ ι₂ → ℝ => (gdens Γ x : ℂ) * hcond Γ F (fun j => x (Sum.inr j)) with hf2
  have hp1 : Integrable (fun p => f1 (e.symm p)) ((volume : Measure (ι₁ → ℝ)).prod volume) :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hint1
  have hp2 : Integrable (fun p => f2 (e.symm p)) ((volume : Measure (ι₁ → ℝ)).prod volume) :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hint2
  show ∫ x, f1 x = ∫ x, f2 x
  rw [← hmp.integral_comp' f1, ← hmp.integral_comp' f2]
  change ∫ p, f1 (e.symm p) ∂((volume : Measure (ι₁ → ℝ)).prod volume) =
    ∫ p, f2 (e.symm p) ∂((volume : Measure (ι₁ → ℝ)).prod volume)
  rw [integral_prod_symm _ hp1, integral_prod_symm _ hp2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [hf1, hf2, hsplit, Sum.elim_inl, Sum.elim_inr]
  -- the inner integrals over `A₁`
  set s := (root (cM Γ)).re with hs
  set s1 := (root (cM (G11 Γ))).re with hs1
  have hs10 : 0 < s1 := (root_re_pos (G11_posDef hΓ)).1
  set w := G12 Γ *ᵥ b with hw
  have hdens : ∀ a, (gdens Γ (Sum.elim a b) : ℂ) =
      ((s / s1 * Real.exp (-(1 / 2) * (b ⬝ᵥ (G22 Γ *ᵥ b))) : ℝ) : ℂ) *
        (((s1 * Real.exp (-(1 / 2) * (a ⬝ᵥ (G11 Γ *ᵥ a)) - a ⬝ᵥ w)) : ℝ) : ℂ) := by
    intro a
    rw [← Complex.ofReal_mul]
    congr 1
    rw [gdens, quad_split Γ hsymm a b, ← hs]
    rw [show -(1 / 2) * (a ⬝ᵥ (G11 Γ *ᵥ a) + 2 * (a ⬝ᵥ (G12 Γ *ᵥ b)) + b ⬝ᵥ (G22 Γ *ᵥ b)) =
      (-(1 / 2) * (a ⬝ᵥ (G11 Γ *ᵥ a)) - a ⬝ᵥ w) + -(1 / 2) * (b ⬝ᵥ (G22 Γ *ᵥ b)) by rw [hw]; ring, Real.exp_add]
    field_simp
  have hF : ∫ a, (gdens Γ (Sum.elim a b) : ℂ) * F a =
      ((s / s1 * Real.exp (-(1 / 2) * (b ⬝ᵥ (G22 Γ *ᵥ b))) : ℝ) : ℂ) * nuI Γ w F := by
    simp_rw [hdens, mul_assoc]
    rw [integral_const_mul]
    refine congrArg (fun z => _ * z) ?_
    unfold nuI
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => by dsimp only; rw [nu_integrand hΓ w])
  have h1 : ∫ a, (gdens Γ (Sum.elim a b) : ℂ) * hcond Γ F b =
      ((s / s1 * Real.exp (-(1 / 2) * (b ⬝ᵥ (G22 Γ *ᵥ b))) : ℝ) : ℂ) * nuI Γ w (fun _ => 1) * hcond Γ F b := by
    rw [integral_mul_const]
    refine congrArg (fun z => z * hcond Γ F b) ?_
    have e1 : ∫ a, (gdens Γ (Sum.elim a b) : ℂ) = ∫ a, (gdens Γ (Sum.elim a b) : ℂ) * (fun _ => (1 : ℂ)) a :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => (mul_one _).symm)
    rw [e1]
    simp_rw [hdens, mul_assoc]
    rw [integral_const_mul]
    refine congrArg (fun z => _ * z) ?_
    unfold nuI
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => by dsimp only; rw [nu_integrand hΓ w])
  rw [hF, h1, nuI_one hΓ w]
  unfold hcond
  rw [← hw]
  rw [show ((s / s1 * Real.exp (-(1 / 2) * (b ⬝ᵥ (G22 Γ *ᵥ b))) : ℝ) : ℂ) *
      cexp (1 / 2 * ((w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w) : ℝ) : ℂ)) *
      (cexp (-(1 / 2) * ((w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w) : ℝ) : ℂ)) * nuI Γ w F) =
      ((s / s1 * Real.exp (-(1 / 2) * (b ⬝ᵥ (G22 Γ *ᵥ b))) : ℝ) : ℂ) *
      (cexp (1 / 2 * ((w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w) : ℝ) : ℂ) + -(1 / 2) * ((w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w) : ℝ) : ℂ))) * nuI Γ w F by
    rw [Complex.exp_add]; ring]
  rw [show (1 / 2 : ℂ) * ((w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w) : ℝ) : ℂ) + -(1 / 2) * ((w ⬝ᵥ ((G11 Γ)⁻¹ *ᵥ w) : ℝ) : ℂ) = 0 by
    ring, Complex.exp_zero, mul_one]

/-- **`eq:gaussian-conditioning`**. -/
theorem gaussian_conditioning (hΓ : Γ.PosDef) (T : Matrix (ι₁ ⊕ ι₂) ι' ℝ) (hT : T * Tᵀ = Γ⁻¹)
    (F : (ι₁ → ℝ) → ℂ) (hFm : Measurable F) {B : ℝ} (hFb : ∀ a, ‖F a‖ ≤ B) :
    ∫ A, F (fun i => A (Sum.inl i)) ∂(multivariateGaussian 0 Γ⁻¹) =
      ∫ X, hcond Γ F (fun j => (T *ᵥ ofLp X) (Sum.inr j)) ∂(stdGaussian (EuclideanSpace ℝ ι')) := by
  have hC : (Γ⁻¹).PosSemidef := hΓ.inv.posSemidef
  have hmT : Measurable fun X : EuclideanSpace ℝ ι' => toLp 2 (T *ᵥ ofLp X) :=
    ((PiLp.continuous_toLp 2 _).comp (continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _))).measurable
  have hHm : StronglyMeasurable (hcond Γ F) := by
    unfold hcond
    refine StronglyMeasurable.mul ?_ (measurable_nuI F hFm)
    refine Continuous.stronglyMeasurable (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp ?_)))
    simp only [dotProduct, mulVec]
    fun_prop
  have hr : ∫ X, hcond Γ F (fun j => (T *ᵥ ofLp X) (Sum.inr j)) ∂(stdGaussian (EuclideanSpace ℝ ι')) =
      ∫ A, hcond Γ F (fun j => A (Sum.inr j)) ∂(multivariateGaussian 0 Γ⁻¹) := by
    rw [← stdGaussian_map_eq Γ⁻¹ hC T hT]
    exact (integral_map (f := fun A : EuclideanSpace ℝ (ι₁ ⊕ ι₂) => hcond Γ F (fun j => A (Sum.inr j)))
      hmT.aemeasurable (hHm.measurable.comp ((continuous_pi fun j =>
        (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)).measurable)).aestronglyMeasurable).symm
  rw [hr, ← gaussM_eq hΓ]
  have hg : gaussM Γ = volume.withDensity fun x => ((gdens Γ x).toNNReal : ENNReal) := rfl
  have hmeas : Measurable fun x => (gdens Γ x).toNNReal := (continuous_gdens Γ).measurable.real_toNNReal
  rw [integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable, integral_map
    (PiLp.continuous_toLp 2 _).measurable.aemeasurable, hg, integral_withDensity_eq_integral_smul hmeas,
    integral_withDensity_eq_integral_smul hmeas]
  · refine Eq.trans ?_ ((density_conditioning hΓ F hFm hFb).trans ?_)
    · congr 1; funext x
      rw [NNReal.smul_def, Real.coe_toNNReal _ (gdens_nonneg hΓ x), Complex.real_smul]
    · congr 1; funext x
      rw [NNReal.smul_def, Real.coe_toNNReal _ (gdens_nonneg hΓ x), Complex.real_smul]
  · exact (hHm.measurable.comp ((continuous_pi fun j =>
      (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)).measurable)).aestronglyMeasurable
  · exact (hFm.comp ((continuous_pi fun i =>
      (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)).measurable)).aestronglyMeasurable

end ComplexGauss
end CoreLean

end
