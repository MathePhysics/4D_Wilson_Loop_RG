/-
**`lem:complex-gaussian`** of BALABAN_CORE.tex (`9c56d4590aff`): Gaussian measures with a complex form,
`dν_Q = det(Q/2π)^{1/2}e^{-½⟨A, QA⟩}dA` on `E = ℝ^ι` for `Q ∈ 𝒬` (`QSet`).
(i) `Q` is invertible (`det_ne_zero`); the root `det(Q/2π)^{1/2} := (∫e^{-½⟨A, QA⟩}dA)⁻¹` (`root`) squares to
`det(Q/2π)` (`root_sq`), is positive at the real `Q` (`root_real`), is continuous and holomorphic, and is the only
continuous root positive at the real `Q` (`root_unique`); `∫e^{-⟨A, v⟩}dν_Q = e^{½⟨v, Q⁻¹v⟩}` (`complex_gaussian`).
(ii) the bound `complex_gaussian_bound`; (iii) holomorphy in `(Q, v)`, `complex_gaussian_holomorphic`.
Holomorphy is stated on open sets of all complex matrices `ι → ι → ℂ`: `𝒬` lies in the symmetric matrices, which
have no interior; the functions are defined, and holomorphic, on the open set `U₀` of the `Q` with
`Re⟨A, QA⟩ ≥ q|A|²` for some `q > 0`, which contains `𝒬`, and depend only on the symmetric part of `Q`.
-/
import CoreLean.GaussHolo

open Matrix Complex MeasureTheory Real

noncomputable section

namespace CoreLean
namespace ComplexGauss

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Real parts and lower bounds -/

lemma re_qf (Q : Matrix ι ι ℂ) (x : ι → ℝ) : (qf Q x).re = x ⬝ᵥ (reM Q *ᵥ x) := by
  simp only [qf, dotProduct, mulVec, cV, reM, Matrix.map_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm (Q i j), Complex.re_ofReal_mul]; ring

lemma dot_mulVec_real (A : Matrix ι ι ℝ) (u w : ι → ℝ) : (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- **A positive definite form is bounded below**: `x·Rx ≥ c|x|²` with `c > 0`. -/
lemma posDef_lower {R : Matrix ι ι ℝ} (hR : R.PosDef) : ∃ c > 0, ∀ x : ι → ℝ, c * nsq x ≤ x ⬝ᵥ (R *ᵥ x) := by
  obtain ⟨U, hUU, hUR⟩ := orth_diag R hR.1
  have hpos : ∀ k, 0 < hR.1.eigenvalues k := hR.eigenvalues_pos
  set lam := hR.1.eigenvalues with hlam
  clear_value lam
  have hUU' : U * Uᵀ = 1 := mul_eq_one_comm.1 hUU
  have hRU : R = U * diagonal lam * Uᵀ := by
    rw [← hUR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU', Matrix.one_mul, Matrix.mul_assoc, hUU', Matrix.mul_one]
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun x => ?_⟩
    simp [nsq, dotProduct]
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  refine ⟨lam k0, hpos k0, fun x => ?_⟩
  set y := Uᵀ *ᵥ x with hy
  have hxR : x ⬝ᵥ (R *ᵥ x) = ∑ k, lam k * y k ^ 2 := by
    rw [hRU, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_comm, dot_mulVec_real, dotProduct_comm]
    simp only [mulVec_diagonal, dotProduct, hy]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hyy : nsq x = ∑ k, y k ^ 2 := by
    have : y ⬝ᵥ y = x ⬝ᵥ x := by
      rw [hy, dot_mulVec_real, transpose_transpose, mulVec_mulVec, hUU', one_mulVec]
    simp only [nsq, dotProduct] at this ⊢
    simp only [pow_two]; exact this.symm
  rw [hxR, hyy, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hk0 k (Finset.mem_univ _)) (sq_nonneg _)

lemma l1_sq_le (x : ι → ℝ) : l1 x ^ 2 ≤ Fintype.card ι * nsq x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ)) fun i => |x i|
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sq_abs] at h
  exact h

/-! ### The open set `U₀` -/

/-- `U₀`: the matrices with `Re⟨A, QA⟩ ≥ q|A|²` for some `q > 0`. -/
def U0 : Set (ι → ι → ℂ) := {Q | ∃ q > 0, ∀ x, q * nsq x ≤ (qf (Matrix.of Q) x).re}

lemma qf_sub (Q Q' : ι → ι → ℂ) (x : ι → ℝ) : qf (Matrix.of Q) x - qf (Matrix.of Q') x = qf (Matrix.of (Q - Q')) x := by
  unfold qf
  rw [← dotProduct_sub, ← sub_mulVec]
  rfl

/-- **Local uniformity**: near `Q₀ ∈ U₀` with the constant `q₀`, `Re⟨A, QA⟩ ≥ (q₀/2)|A|²`. -/
lemma lower_near {Q0 : ι → ι → ℂ} {q0 : ℝ} (hq0 : 0 < q0) (h0 : ∀ x, q0 * nsq x ≤ (qf (Matrix.of Q0) x).re)
    {Q : ι → ι → ℂ} (hQ : dist Q Q0 < q0 / (2 * (Fintype.card ι + 1))) (x : ι → ℝ) :
    q0 / 2 * nsq x ≤ (qf (Matrix.of Q) x).re := by
  have hn : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  have hd : ‖qf (Matrix.of (Q - Q0)) x‖ ≤ Fintype.card ι * nsq x * ‖Q - Q0‖ :=
    (norm_qf_le _ x).trans (mul_le_mul_of_nonneg_right (l1_sq_le x) (norm_nonneg _))
  have hre : (qf (Matrix.of Q0) x).re - (qf (Matrix.of Q) x).re ≤ ‖qf (Matrix.of (Q - Q0)) x‖ := by
    rw [← qf_sub, ← Complex.sub_re]
    refine (le_abs_self _).trans ?_
    rw [← neg_sub, Complex.neg_re, abs_neg]
    exact Complex.abs_re_le_norm _
  rw [dist_eq_norm] at hQ
  have hns := nsq_nonneg x
  have h1 : Fintype.card ι * nsq x * ‖Q - Q0‖ ≤ q0 / 2 * nsq x := by
    have h2 : (Fintype.card ι : ℝ) * ‖Q - Q0‖ ≤ q0 / 2 := by
      have : (Fintype.card ι : ℝ) * ‖Q - Q0‖ ≤ (Fintype.card ι + 1) * ‖Q - Q0‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      refine this.trans ?_
      rw [lt_div_iff₀ (by positivity)] at hQ
      nlinarith
    nlinarith
  linarith [h0 x]

lemma isOpen_U0 : IsOpen (U0 (ι := ι)) := by
  rw [Metric.isOpen_iff]
  rintro Q0 ⟨q0, hq0, h0⟩
  refine ⟨q0 / (2 * (Fintype.card ι + 1)), by positivity, fun Q hQ => ⟨q0 / 2, by positivity, fun x => ?_⟩⟩
  exact lower_near hq0 h0 (Metric.mem_ball.1 hQ) x

lemma QSet_sub_U0 {Q : Matrix ι ι ℂ} (hQ : Q ∈ QSet) : (Q : ι → ι → ℂ) ∈ U0 := by
  obtain ⟨c, hc, h⟩ := posDef_lower hQ.2
  exact ⟨c, hc, fun x => by rw [re_qf]; exact h x⟩

/-! ### The symmetric part -/

/-- The symmetric part `½(Q + Qᵀ)`. -/
def symP (Q : ι → ι → ℂ) : Matrix ι ι ℂ := (1 / 2 : ℂ) • (Matrix.of Q + (Matrix.of Q)ᵀ)

lemma qf_symP (Q : ι → ι → ℂ) (x : ι → ℝ) : qf (symP Q) x = qf (Matrix.of Q) x := by
  unfold symP qf
  rw [smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add]
  have : cV x ⬝ᵥ ((Matrix.of Q)ᵀ *ᵥ cV x) = cV x ⬝ᵥ (Matrix.of Q *ᵥ cV x) := by
    rw [← mulVec_dot, dotProduct_comm]
  rw [this, smul_eq_mul]; ring

lemma symP_mem {Q : ι → ι → ℂ} (hQ : Q ∈ U0) : symP Q ∈ QSet := by
  obtain ⟨q, hq, h⟩ := hQ
  refine ⟨?_, ?_⟩
  · unfold symP; rw [transpose_smul, transpose_add, transpose_transpose, add_comm]
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_of_symm ?_) fun x hx => ?_
    · rw [← reM_transpose]; congr 1
      unfold symP; rw [transpose_smul, transpose_add, transpose_transpose, add_comm]
    · have h1 := h x
      rw [← qf_symP, re_qf] at h1
      have hpos : 0 < nsq x := by
        obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
        have hi' : x i ≠ 0 := hi
        exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi')))
          (Finset.single_le_sum (f := fun i => x i ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      rw [star_trivial]
      exact lt_of_lt_of_le (mul_pos hq hpos) h1

lemma Zv_symP (Q : ι → ι → ℂ) (v : ι → ℂ) : Zv (symP Q) v = Zv (Matrix.of Q) v := by
  unfold Zv; simp only [qf_symP]

/-! ### Holomorphy of the root -/

lemma Zv_eq_J (Q : ι → ι → ℂ) (v : ι → ℂ) :
    Zv (Matrix.of Q) v = ∫ x, cexp (ellL x (Q, v)) • (1 : ℂ) := by
  unfold Zv; simp only [ellL_apply, smul_eq_mul, mul_one]

/-- `Z(Q, 0)` is holomorphic and nonzero on `U₀`. -/
lemma Z_holo : DifferentiableOn ℂ (fun Q : ι → ι → ℂ => Zv (Matrix.of Q) 0) U0 ∧
    ∀ Q ∈ (U0 : Set (ι → ι → ℂ)), Zv (Matrix.of Q) 0 ≠ 0 := by
  refine ⟨fun Q0 hQ0 => ?_, fun Q hQ => by rw [← Zv_symP Q]; exact Zv_zero_ne (symP_mem hQ)⟩
  obtain ⟨q0, hq0, h0⟩ := hQ0
  set r := q0 / (2 * (Fintype.card ι + 1)) with hr
  have hU : IsOpen (Metric.ball Q0 r ×ˢ (Set.univ : Set (ι → ℂ))) := Metric.isOpen_ball.prod isOpen_univ
  have hJ := differentiableOn_J (F := ℂ) (fun _ => (1 : ℂ)) aestronglyMeasurable_const (W := 1) (α := 0)
    (half_pos hq0) (fun x => by simp) hU (fun p hp x => by
      have := lower_near hq0 h0 (Metric.mem_ball.1 hp.1) x
      simp only [zero_mul, sub_zero, ge_iff_le]; exact this)
  have hmem : (Q0, (0 : ι → ℂ)) ∈ Metric.ball Q0 r ×ˢ (Set.univ : Set (ι → ℂ)) :=
    ⟨Metric.mem_ball_self (by positivity), Set.mem_univ _⟩
  have hda := (hJ _ hmem).differentiableAt (hU.mem_nhds hmem)
  have hcomp : DifferentiableAt ℂ (fun Q : ι → ι → ℂ => (Q, (0 : ι → ℂ))) Q0 :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  have := hda.comp Q0 hcomp
  refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Q => ?_)).differentiableWithinAt
  simp only [Function.comp_apply]
  exact Zv_eq_J Q 0

/-- **The root is holomorphic** on the open set `U₀ ⊇ 𝒬`. -/
theorem root_holo : DifferentiableOn ℂ (fun Q : ι → ι → ℂ => root (Matrix.of Q)) U0 := by
  have h := Z_holo (ι := ι)
  exact h.1.inv h.2

/-- The root is continuous on `𝒬`. -/
lemma root_continuousOn : ContinuousOn (root (ι := ι)) QSet := by
  have h := (root_holo (ι := ι)).continuousOn
  intro Q hQ
  exact ((h (Q : ι → ι → ℂ) (QSet_sub_U0 hQ)).mono fun Q' hQ' => QSet_sub_U0 hQ')

lemma convex_QSet : Convex ℝ (QSet (ι := ι)) := by
  intro Q hQ Q' hQ' a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [transpose_add, transpose_smul, transpose_smul, hQ.1, hQ'.1]
  · have hre : reM (a • Q + b • Q') = a • reM Q + b • reM Q' := by
      ext i j; simp [reM]
    rw [hre]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · rw [zero_add] at hab; subst hab; simpa using hQ'.2
    · rcases eq_or_lt_of_le hb with rfl | hb'
      · rw [add_zero] at hab; subst hab; simpa using hQ.2
      · exact (hQ.2.smul ha').add (hQ'.2.smul hb')

lemma cM_one : cM (1 : Matrix ι ι ℝ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

lemma one_mem_QSet : cM (1 : Matrix ι ι ℝ) ∈ QSet := by
  refine ⟨by rw [cM_one, transpose_one], ?_⟩
  have : reM (cM (1 : Matrix ι ι ℝ)) = 1 := by
    rw [cM_one]; exact Matrix.map_one _ Complex.zero_re Complex.one_re
  rw [this]; exact Matrix.PosDef.one

/-- **Uniqueness of the root**: a continuous root of `det(Q/2π)` on `𝒬` which is positive at the real `Q` is
`root`. -/
theorem root_unique (r : Matrix ι ι ℂ → ℂ) (hr : ContinuousOn r QSet)
    (hsq : ∀ Q ∈ QSet, r Q ^ 2 = ((2 * π : ℂ)⁻¹ • Q).det)
    (hpos : ∀ R : Matrix ι ι ℝ, cM R ∈ QSet → ∃ s : ℝ, 0 < s ∧ r (cM R) = s) :
    ∀ Q ∈ QSet, r Q = root Q := by
  have hne : ∀ Q ∈ (QSet : Set (Matrix ι ι ℂ)), root Q ≠ 0 := fun Q hQ => inv_ne_zero (Zv_zero_ne hQ)
  set g := fun Q : Matrix ι ι ℂ => r Q / root Q with hg
  have hgc : ContinuousOn g QSet := hr.div root_continuousOn hne
  have hg2 : Set.MapsTo g QSet ({1, -1} : Set ℂ) := by
    intro Q hQ
    have h2 : g Q ^ 2 = 1 := by
      simp only [hg]
      rw [div_pow, hsq Q hQ, ← root_sq hQ, div_self (pow_ne_zero 2 (hne Q hQ))]
    have h3 : (g Q - 1) * (g Q + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · left; linear_combination h
    · right; exact Set.mem_singleton_iff.2 (by linear_combination h)
  have hdisc : IsDiscrete ({1, -1} : Set ℂ) := isDiscrete_iff_discreteTopology.2 inferInstance
  obtain ⟨s, hs, hrs⟩ := hpos 1 one_mem_QSet
  obtain ⟨s', hs', hrs'⟩ := root_real (one_mem_QSet (ι := ι))
  have hg1 : g (cM 1) = 1 := by
    rcases hg2 one_mem_QSet with h | h
    · exact h
    · exfalso
      replace h := Set.mem_singleton_iff.1 h
      simp only [hg, hrs, hrs'] at h
      have hs'0 : (s' : ℂ) ≠ 0 := by exact_mod_cast hs'.ne'
      rw [div_eq_iff hs'0] at h
      have := congrArg Complex.re h
      simp at this
      linarith
  intro Q hQ
  have h := convex_QSet.isPreconnected.constant_of_mapsTo hdisc hgc hg2 hQ one_mem_QSet
  rw [hg1] at h
  simp only [hg] at h
  rwa [div_eq_one_iff_eq (hne Q hQ)] at h

/-! ### (ii) The bound -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The real part of a complex vector. -/
def reV (v : ι → ℂ) : ι → ℝ := fun i => (v i).re

lemma qf_cM (M : Matrix ι ι ℝ) (x : ι → ℝ) : qf (cM M) x = ((x ⬝ᵥ (M *ᵥ x) : ℝ) : ℂ) := by
  simp [qf, cV, cM, dotProduct, mulVec]

lemma dot_cV (x y : ι → ℝ) : cV x ⬝ᵥ cV y = ((x ⬝ᵥ y : ℝ) : ℂ) := by
  simp [cV, dotProduct]

lemma re_dot (x : ι → ℝ) (v : ι → ℂ) : (cV x ⬝ᵥ v).re = x ⬝ᵥ reV v := by
  simp [cV, dotProduct, reV, Complex.re_sum]

lemma cM_inv {M : Matrix ι ι ℝ} (hM : M.det ≠ 0) : (cM M)⁻¹ = cM M⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- The real Gaussian integral with a linear term, as a real number. -/
lemma real_gauss {M : Matrix ι ι ℝ} (hM : cM M ∈ QSet) (w : ι → ℝ) :
    ∃ s : ℝ, 0 < s ∧ s ^ 2 = ((2 * π)⁻¹ : ℝ) ^ Fintype.card ι * M.det ∧
      ∫ x, Real.exp (-(1 / 2) * (x ⬝ᵥ (M *ᵥ x)) - x ⬝ᵥ w) = Real.exp (1 / 2 * (w ⬝ᵥ (M⁻¹ *ᵥ w))) / s := by
  obtain ⟨s, hs, hrs⟩ := root_real hM
  have hdetM : M.det ≠ 0 := by
    have := det_ne_zero hM; rwa [det_cM, Complex.ofReal_ne_zero] at this
  refine ⟨s, hs, ?_, ?_⟩
  · have h := root_sq hM
    rw [hrs, det_smul, det_cM] at h
    have h' := congrArg Complex.re h
    have e : ((2 * π : ℂ)⁻¹ ^ Fintype.card ι * (M.det : ℂ)) = (((2 * π)⁻¹ ^ Fintype.card ι * M.det : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re, ← Complex.ofReal_pow, Complex.ofReal_re] at h'
    exact h'
  · have h := complex_gaussian hM (cV w)
    rw [hrs, cM_inv hdetM] at h
    have hZ : Zv (cM M) (cV w) = ((∫ x, Real.exp (-(1 / 2) * (x ⬝ᵥ (M *ᵥ x)) - x ⬝ᵥ w) : ℝ) : ℂ) := by
      unfold Zv
      rw [← integral_complex_ofReal]
      congr 1; funext x
      rw [qf_cM, dot_cV, Complex.ofReal_exp]; push_cast; ring_nf
    have hexp : cexp (1 / 2 * (cV w ⬝ᵥ (cM M⁻¹ *ᵥ cV w))) = ((Real.exp (1 / 2 * (w ⬝ᵥ (M⁻¹ *ᵥ w))) : ℝ) : ℂ) := by
      rw [← cV_mulVec, dot_cV, Complex.ofReal_exp]; push_cast; ring_nf
    rw [hZ, hexp, ← Complex.ofReal_mul] at h
    have h2 := Complex.ofReal_injective h
    rw [eq_div_iff hs.ne', mul_comm]
    exact h2

/-- **`eq:complex-gaussian-bound`**: if `Re Q - α` is positive definite and `‖Φ(A)‖ ≤ We^{½α|A|²}`, then the integral
`∫e^{-⟨A, v⟩}Φ(A)dν_Q(A)` exists and is at most
`W|det Q|^{1/2}det(Re Q - α)^{-1/2}e^{½⟨Re v, (Re Q - α)⁻¹Re v⟩}` in norm. -/
theorem complex_gaussian_bound {Q : Matrix ι ι ℂ} (hQ : Q ∈ QSet) {α W : ℝ} (hM : (reM Q - α • 1).PosDef)
    (Φ : (ι → ℝ) → F) (hΦm : AEStronglyMeasurable Φ volume) (hΦ : ∀ x, ‖Φ x‖ ≤ W * Real.exp (1 / 2 * α * nsq x))
    (v : ι → ℂ) :
    Integrable (fun x => (root Q * cexp (-(1 / 2) * qf Q x - cV x ⬝ᵥ v)) • Φ x) ∧
      ‖∫ x, (root Q * cexp (-(1 / 2) * qf Q x - cV x ⬝ᵥ v)) • Φ x‖ ≤
        W * (Real.sqrt ‖Q.det‖ / Real.sqrt (reM Q - α • 1).det) *
          Real.exp (1 / 2 * (reV v ⬝ᵥ ((reM Q - α • 1)⁻¹ *ᵥ reV v))) := by
  set M := reM Q - α • 1 with hMdef
  set rv := reV v with hrv
  have hW : 0 ≤ W := by
    have := (norm_nonneg _).trans (hΦ 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  -- the real Gaussian dominating the integrand
  set G : (ι → ℝ) → ℝ := fun x => ‖root Q‖ * W * Real.exp (-(1 / 2) * (x ⬝ᵥ (M *ᵥ x)) - x ⬝ᵥ rv) with hG
  have hMx : ∀ x : ι → ℝ, x ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (reM Q *ᵥ x) - α * nsq x := by
    intro x
    rw [hMdef, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    simp only [nsq, dotProduct, pow_two]
  have hpt : ∀ x, ‖(root Q * cexp (-(1 / 2) * qf Q x - cV x ⬝ᵥ v)) • Φ x‖ ≤ G x := by
    intro x
    rw [norm_smul, norm_mul, Complex.norm_exp]
    have hre : (-(1 / 2) * qf Q x - cV x ⬝ᵥ v).re = -(1 / 2) * (x ⬝ᵥ (reM Q *ᵥ x)) - x ⬝ᵥ rv := by
      rw [Complex.sub_re, re_dot, ← re_qf]; simp [hrv]
    rw [hre]
    show _ ≤ ‖root Q‖ * W * Real.exp (-(1 / 2) * (x ⬝ᵥ (M *ᵥ x)) - x ⬝ᵥ rv)
    rw [hMx]
    calc ‖root Q‖ * Real.exp (-(1 / 2) * (x ⬝ᵥ (reM Q *ᵥ x)) - x ⬝ᵥ rv) * ‖Φ x‖
        ≤ ‖root Q‖ * Real.exp (-(1 / 2) * (x ⬝ᵥ (reM Q *ᵥ x)) - x ⬝ᵥ rv) * (W * Real.exp (1 / 2 * α * nsq x)) :=
          mul_le_mul_of_nonneg_left (hΦ x) (by positivity)
      _ = ‖root Q‖ * W * Real.exp (-(1 / 2) * (x ⬝ᵥ (reM Q *ᵥ x) - α * nsq x) - x ⬝ᵥ rv) := by
          rw [show -(1 / 2) * (x ⬝ᵥ (reM Q *ᵥ x) - α * nsq x) - x ⬝ᵥ rv =
            (-(1 / 2) * (x ⬝ᵥ (reM Q *ᵥ x)) - x ⬝ᵥ rv) + 1 / 2 * α * nsq x by ring, Real.exp_add]
          ring
  have hMQ : cM M ∈ QSet := by
    refine ⟨?_, ?_⟩
    · rw [← Matrix.transpose_map]
      congr 1
      have : (reM Q)ᵀ = reM Q := by rw [← reM_transpose, hQ.1]
      rw [hMdef, transpose_sub, this, transpose_smul, transpose_one]
    · have : reM (cM M) = M := by ext i j; simp [reM, cM]
      rw [this]; exact hM
  obtain ⟨c, hc, hlow⟩ := posDef_lower hM
  have hGint : Integrable G := by
    refine (integrable_dom (half_pos hc) (‖root Q‖ * W * Real.exp (Fintype.card ι * ((‖rv‖ ^ 2) / (c / 2))))).mono'
      ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · rw [hG, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc (‖root Q‖ * W)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hlin : -(x ⬝ᵥ rv) ≤ ‖rv‖ * l1 x := by
        unfold dotProduct l1
        rw [← Finset.sum_neg_distrib, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => by
          have := norm_le_pi_norm rv i
          rw [Real.norm_eq_abs] at this
          nlinarith [neg_abs_le (x i * rv i), abs_mul (x i) (rv i), abs_nonneg (x i)]
      have := dom_le (half_pos hc) ‖rv‖ x
      calc Real.exp (-(1 / 2) * (x ⬝ᵥ (M *ᵥ x)) - x ⬝ᵥ rv) ≤ Real.exp (-(1 / 2) * (c / 2) * nsq x + ‖rv‖ * l1 x) := by
            refine Real.exp_le_exp.2 ?_
            have h1 := hlow x
            have h2 := nsq_nonneg x
            nlinarith
        _ ≤ _ := this
  have hint : Integrable (fun x => (root Q * cexp (-(1 / 2) * qf Q x - cV x ⬝ᵥ v)) • Φ x) := by
    refine hGint.mono' ?_ (Filter.Eventually.of_forall hpt)
    refine AEStronglyMeasurable.smul ?_ hΦm
    exact (continuous_const.mul (Complex.continuous_exp.comp (by
      unfold qf dotProduct mulVec cV; fun_prop))).aestronglyMeasurable
  refine ⟨hint, (norm_integral_le_of_norm_le hGint (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)⟩
  -- the value of `∫G`
  obtain ⟨s, hs, hs2, hval⟩ := real_gauss hMQ rv
  rw [hG, integral_const_mul, hval]
  have hroot2 : ‖root Q‖ ^ 2 = ((2 * π)⁻¹ : ℝ) ^ Fintype.card ι * ‖Q.det‖ := by
    rw [← norm_pow, root_sq hQ, det_smul, norm_mul, norm_pow, norm_inv]
    congr 2
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have ha : (0 : ℝ) < ((2 * π)⁻¹ : ℝ) ^ Fintype.card ι := by positivity
  have hdetM : 0 < M.det := hM.det_pos
  have hrootQ : ‖root Q‖ = Real.sqrt (((2 * π)⁻¹ : ℝ) ^ Fintype.card ι) * Real.sqrt ‖Q.det‖ := by
    rw [← Real.sqrt_mul ha.le, ← hroot2, Real.sqrt_sq (norm_nonneg _)]
  have hsv : s = Real.sqrt (((2 * π)⁻¹ : ℝ) ^ Fintype.card ι) * Real.sqrt M.det := by
    rw [← Real.sqrt_mul ha.le, ← hs2, Real.sqrt_sq hs.le]
  rw [hrootQ, hsv]
  have hsa : 0 < Real.sqrt (((2 * π)⁻¹ : ℝ) ^ Fintype.card ι) := Real.sqrt_pos.2 ha
  have hsd : 0 < Real.sqrt M.det := Real.sqrt_pos.2 hdetM
  field_simp

/-! ### (iii) Holomorphy in `(Q, v)` -/

/-- **`lem:complex-gaussian`(iii)**: if `Re Q - α ≥ q > 0` on an open set `U` of matrices (`α ≥ 0`) and `Φ` is as in
(ii), then `(Q, v) ↦ ∫e^{-⟨A, v⟩}Φ(A)dν_Q(A)` is holomorphic on `U × E^c`. -/
theorem complex_gaussian_holomorphic (Φ : (ι → ℝ) → F) (hΦm : AEStronglyMeasurable Φ volume) {W α q : ℝ}
    (hα : 0 ≤ α) (hq : 0 < q) (hΦ : ∀ x, ‖Φ x‖ ≤ W * Real.exp (1 / 2 * α * nsq x)) {U : Set (ι → ι → ℂ)}
    (hU : IsOpen U) (hUq : ∀ Q ∈ U, ∀ x, (qf (Matrix.of Q) x).re - α * nsq x ≥ q * nsq x) :
    DifferentiableOn ℂ (fun p : (ι → ι → ℂ) × (ι → ℂ) =>
      ∫ x, (root (Matrix.of p.1) * cexp (-(1 / 2) * qf (Matrix.of p.1) x - cV x ⬝ᵥ p.2)) • Φ x)
      (U ×ˢ Set.univ) := by
  have hUU : IsOpen (U ×ˢ (Set.univ : Set (ι → ℂ))) := hU.prod isOpen_univ
  have hJ := differentiableOn_J Φ hΦm hq hΦ hUU fun p hp x => hUq p.1 hp.1 x
  have hsub : U ⊆ U0 := fun Q hQ => ⟨q + α, by linarith, fun x => by
    have := hUq Q hQ x; nlinarith⟩
  have hroot : DifferentiableOn ℂ (fun p : (ι → ι → ℂ) × (ι → ℂ) => root (Matrix.of p.1)) (U ×ˢ Set.univ) :=
    (root_holo.mono hsub).comp differentiableOn_fst fun p hp => hp.1
  refine (hroot.smul hJ).congr fun p _ => ?_
  show _ = root (Matrix.of p.1) • ∫ x, cexp (ellL x p) • Φ x
  rw [← integral_smul]
  congr 1; funext x
  rw [smul_smul, ellL_apply]

end ComplexGauss
end CoreLean

end
