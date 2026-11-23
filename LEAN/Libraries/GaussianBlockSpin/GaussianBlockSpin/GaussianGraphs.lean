import GaussianBlockSpin.TruncatedExpectations

/-! Gaussian truncated expectations of polynomials as sums over connected graphs (I.(3.23), L958-L959: "the expression
corresponding to the sum of connected graphs"). The normalised Gaussian measure `gaussProb T` (density
`e^{-½⟪x, T x⟫} / ∫ e^{-½⟪y, T y⟫} dy`), a polynomial given by its monomials (`monomial`: coefficient, degree, legs),
the legs of a configuration of monomials at the vertices (`legVertex`, `legVector`), and
truncExp_gaussProb_eq_connected: `⟨V^n⟩^T = Σ_g (∏_v c_{g v}) Σ_{σ connected} ∏_{l < σ l} ⟪w_l, C w_{σ l}⟫`. -/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal NNReal

namespace GaussianBlockSpin

/-- **Scaling the vertices**: `κ` of the moment function `T ↦ (∏_{v ∈ T} c_v) M(T)` is `(∏_{v ∈ S} c_v) κ(S)`. -/
theorem jointCumulant_mul_prod {n : ℕ} (M : Finset (Fin n) → ℝ) (hM : M ∅ = 1) (c : Fin n → ℝ)
    (S : Finset (Fin n)) (h : S.Nonempty) :
    jointCumulant (fun T => (∏ v ∈ T, c v) * M T) S = (∏ v ∈ S, c v) * jointCumulant M S := by
  refine (eq_jointCumulant_of_decomp (fun T => (∏ v ∈ T, c v) * M T)
    (fun B => (∏ v ∈ B, c v) * jointCumulant M B) (by simp [hM]) (fun S h => ?_) S h).symm
  rw [moment_eq_sum_jointCumulant M hM h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hBS : B ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
  rw [← Finset.prod_sdiff hBS]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A continuous function bounded by `K (1 + ‖x‖)^N` times the Gaussian weight is integrable. -/
lemma integrable_mul_gaussWeight_of_le_one_add {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) {P : E → ℝ} (hP : Continuous P) {K : ℝ} (N : ℕ)
    (hb : ∀ x, |P x| ≤ K * (1 + ‖x‖) ^ N) : Integrable (fun x => P x * gaussWeight T x) := by
  have hI := ((integrable_gaussWeight hT hpos).add (integrable_norm_pow_mul_gaussWeight hT hpos N)).const_mul
    (K * 2 ^ N)
  refine hI.mono' (hP.mul (continuous_gaussWeight T)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hg := gaussWeight_pos T x
  have hK : 0 ≤ K := by
    have := (abs_nonneg (P x)).trans (hb x)
    have h1 : 0 < (1 + ‖x‖) ^ N := by positivity
    exact nonneg_of_mul_nonneg_left this h1
  have h12 : (1 + ‖x‖) ^ N ≤ 2 ^ N * (1 + ‖x‖ ^ N) := by
    rcases le_total ‖x‖ 1 with h | h
    · calc (1 + ‖x‖) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ ≤ 2 ^ N * (1 + ‖x‖ ^ N) := le_mul_of_one_le_right (by positivity) (by have := pow_nonneg (norm_nonneg x) N; linarith)
    · calc (1 + ‖x‖) ^ N ≤ (2 * ‖x‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * ‖x‖ ^ N := mul_pow 2 ‖x‖ N
        _ ≤ 2 ^ N * (1 + ‖x‖ ^ N) := by gcongr; linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hg]
  calc |P x| * gaussWeight T x ≤ K * (1 + ‖x‖) ^ N * gaussWeight T x := mul_le_mul_of_nonneg_right (hb x) hg.le
    _ ≤ K * (2 ^ N * (1 + ‖x‖ ^ N)) * gaussWeight T x := by gcongr
    _ = K * 2 ^ N * (gaussWeight T x + ‖x‖ ^ N * gaussWeight T x) := by ring

/-- The Gaussian normaliser `∫ e^{-½⟪y, T y⟫} dy` is positive. -/
lemma integral_gaussWeight_pos {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) :
    0 < ∫ y, gaussWeight T y := by
  unfold gaussWeight
  rw [integral_exp_neg_half_inner hT hpos]
  exact div_pos (by positivity) (Real.sqrt_pos.mpr (det_pos_of_pos hT hpos))

/-- **The normalised Gaussian measure** `dμ_T(x) = e^{-½⟪x, T x⟫} dx / ∫ e^{-½⟪y, T y⟫} dy` (Bałaban's `dμ_C`, `C = T⁻¹`)
for `T` symmetric positive definite (isProbabilityMeasure_gaussProb). Otherwise `e^{-½⟪x, T x⟫}` need not be
integrable, the normaliser is then the junk `0` and `gaussProb T` the zero measure; every theorem assumes `hT`, `hpos`. -/
noncomputable def gaussProb (T : E →ₗ[ℝ] E) : Measure E :=
  volume.withDensity fun x => ((gaussWeight T x / ∫ y, gaussWeight T y).toNNReal : ℝ≥0∞) -- totalisation-audit: allow junk zero measure off the positive definite cone (normaliser 0); every use assumes hT and hpos

lemma measurable_gaussDensity (T : E →ₗ[ℝ] E) :
    Measurable fun x => (gaussWeight T x / ∫ y, gaussWeight T y).toNNReal :=
  ((continuous_gaussWeight T).measurable.div_const _).real_toNNReal

lemma integral_gaussProb {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    (f : E → ℝ) : ∫ x, f x ∂gaussProb T = (∫ x, f x * gaussWeight T x) / ∫ y, gaussWeight T y := by
  have hZ := integral_gaussWeight_pos hT hpos
  rw [gaussProb, integral_withDensity_eq_integral_smul (measurable_gaussDensity T), ← integral_div]
  congr 1
  funext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg (gaussWeight_pos T x).le hZ.le), smul_eq_mul]
  ring

lemma integrable_gaussProb_iff {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    (f : E → ℝ) : Integrable f (gaussProb T) ↔ Integrable (fun x => f x * gaussWeight T x) := by
  have hZ := integral_gaussWeight_pos hT hpos
  rw [gaussProb, integrable_withDensity_iff_integrable_smul (measurable_gaussDensity T)]
  have heq : (fun x => (gaussWeight T x / ∫ y, gaussWeight T y).toNNReal • f x) =
      fun x => (∫ y, gaussWeight T y)⁻¹ * (f x * gaussWeight T x) := by
    funext x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg (gaussWeight_pos T x).le hZ.le), smul_eq_mul]
    ring
  rw [heq]
  constructor
  · intro h
    have := h.const_mul (∫ y, gaussWeight T y)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    field_simp
  · intro h
    exact h.const_mul _

lemma isProbabilityMeasure_gaussProb {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) :
    IsProbabilityMeasure (gaussProb T) := by
  have hZ := integral_gaussWeight_pos hT hpos
  constructor
  rw [gaussProb, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (fun x => gaussWeight T x / ∫ y, gaussWeight T y) :=
    (integrable_gaussWeight hT hpos).div_const _
  have h := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => div_nonneg (gaussWeight_pos T x).le hZ.le)
  rw [integral_div, div_self hZ.ne', ENNReal.ofReal_one] at h
  exact h.symm

end GaussianBlockSpin

namespace GaussianBlockSpin

section Polynomials

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : Type*}

/-- The monomial `a` of a polynomial on `E`: `c_a ∏_{i < k_a} ⟪u_{a,i}, x⟫` (coefficient `c a`, `k a` legs `u a i`). -/
noncomputable def monomial (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (a : A) (x : E) : ℝ :=
  c a * ∏ i, ⟪u a i, x⟫

/-- The legs of the configuration `g : Fin n → A` (vertex `v` carries the monomial `g v`) are
`Σ_v Fin (k (g v))`, flattened to `Fin (Σ_v k (g v))`; `legVertex` is the vertex of a leg. -/
def legVertex {n : ℕ} (k : A → ℕ) (g : Fin n → A) (l : Fin (∑ v, k (g v))) : Fin n :=
  (finSigmaFinEquiv.symm l).1

/-- The vector of a leg of the configuration `g`. -/
noncomputable def legVector {n : ℕ} (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (g : Fin n → A)
    (l : Fin (∑ v, k (g v))) : E :=
  u (g (finSigmaFinEquiv.symm l).1) (finSigmaFinEquiv.symm l).2

lemma legsOf_legVertex {n : ℕ} (k : A → ℕ) (g : Fin n → A) (B : Finset (Fin n)) :
    legsOf (legVertex k g) B = (B.sigma fun v => (Finset.univ : Finset (Fin (k (g v))))).map
      finSigmaFinEquiv.toEmbedding := by
  ext l
  rw [Finset.mem_map_equiv, Finset.mem_sigma]
  unfold legsOf legVertex
  rw [Finset.mem_filter]
  simp

lemma prod_monomial {n : ℕ} (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (g : Fin n → A)
    (B : Finset (Fin n)) (x : E) :
    ∏ v ∈ B, monomial c k u (g v) x =
      (∏ v ∈ B, c (g v)) * linProd (legsOf (legVertex k g) B) (legVector k u g) x := by
  unfold monomial linProd
  rw [Finset.prod_mul_distrib, legsOf_legVertex, Finset.prod_map, Finset.prod_sigma]
  congr 1
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun i _ => ?_
  simp only [Equiv.coe_toEmbedding, legVector]
  rw [Equiv.symm_apply_apply]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_prod_monomial {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    {n : ℕ} (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (g : Fin n → A) (B : Finset (Fin n)) :
    ∫ x, ∏ v ∈ B, monomial c k u (g v) x ∂gaussProb T =
      (∏ v ∈ B, c (g v)) * (gaussMoment T (legsOf (legVertex k g) B) (legVector k u g) /
        gaussMoment T (∅ : Finset (Fin (∑ v, k (g v)))) (legVector k u g)) := by
  simp_rw [prod_monomial c k u g B]
  rw [integral_const_mul, integral_gaussProb hT hpos]
  congr 2
  unfold gaussMoment linProd
  simp

/-- All products of partial sums of monomials are integrable for the normalised Gaussian measure. -/
lemma integrable_prod_sum_monomial [Fintype A] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) {n : ℕ} (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E)
    (B : Finset (Fin n)) (t : Fin n → Finset A) :
    Integrable (fun x => ∏ v ∈ B, ∑ a ∈ t v, monomial c k u a x) (gaussProb T) := by
  rw [integrable_gaussProb_iff hT hpos]
  set D := ∑ a, k a
  set Ka : A → ℝ := fun a => |c a| * ∏ i, ‖u a i‖
  set K1 := ∑ a, Ka a
  have hKa : ∀ a, 0 ≤ Ka a := fun a => by positivity
  have hmono : ∀ a x, |monomial c k u a x| ≤ Ka a * (1 + ‖x‖) ^ D := by
    intro a x
    unfold monomial
    rw [abs_mul, Finset.abs_prod]
    have h1 : ∏ i, |⟪u a i, x⟫| ≤ ∏ i, (‖u a i‖ * ‖x‖) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => abs_real_inner_le_norm _ _
    have h2 : ∏ i : Fin (k a), (‖u a i‖ * ‖x‖) ≤ (∏ i, ‖u a i‖) * (1 + ‖x‖) ^ D := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hk : k a ≤ D := Finset.single_le_sum (fun b _ => Nat.zero_le (k b)) (Finset.mem_univ a)
      have : ‖x‖ ^ k a ≤ (1 + ‖x‖) ^ D :=
        (pow_le_pow_left₀ (norm_nonneg x) (by linarith) (k a)).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hk)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc |c a| * ∏ i, |⟪u a i, x⟫| ≤ |c a| * ((∏ i, ‖u a i‖) * (1 + ‖x‖) ^ D) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
      _ = Ka a * (1 + ‖x‖) ^ D := by simp only [Ka]; ring
  have hsum : ∀ v x, |∑ a ∈ t v, monomial c k u a x| ≤ K1 * (1 + ‖x‖) ^ D := by
    intro v x
    calc |∑ a ∈ t v, monomial c k u a x| ≤ ∑ a ∈ t v, |monomial c k u a x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ t v, Ka a * (1 + ‖x‖) ^ D := Finset.sum_le_sum fun a _ => hmono a x
      _ ≤ ∑ a, Ka a * (1 + ‖x‖) ^ D :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => by positivity
      _ = K1 * (1 + ‖x‖) ^ D := by rw [← Finset.sum_mul]
  refine integrable_mul_gaussWeight_of_le_one_add hT hpos ?_ (K := K1 ^ B.card) (D * B.card) fun x => ?_
  · refine continuous_finsetProd B fun v _ => continuous_finsetSum _ fun a _ => ?_
    unfold monomial
    exact continuous_const.mul (continuous_finsetProd _ fun i _ => continuous_const.inner continuous_id)
  · rw [Finset.abs_prod]
    calc ∏ v ∈ B, |∑ a ∈ t v, monomial c k u a x| ≤ ∏ v ∈ B, (K1 * (1 + ‖x‖) ^ D) :=
          Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) fun v _ => hsum v x
      _ = K1 ^ B.card * (1 + ‖x‖) ^ (D * B.card) := by rw [Finset.prod_const, mul_pow, pow_mul]

/-- **Gaussian truncated expectations of polynomials are sums over connected graphs**: for `T` symmetric positive
definite with `T C = 1` and the polynomial `V(x) = Σ_{a ∈ A} c_a ∏_{i < k_a} ⟪u_{a,i}, x⟫`, the truncated expectation
`⟨V^n⟩^T` (`truncExp` of the moments under the normalised Gaussian measure, I.(3.23)) is the sum over the configurations
`g : Fin n → A` (vertex `v` carries the monomial `g v`) of `∏_v c_{g v}` times the sum over the perfect matchings of all
legs that connect the `n` vertices of `∏_{l < σ l} ⟪w_l, C w_{σ l}⟫`. (`isProbabilityMeasure_gaussProb` supplies the
instance.) -/
theorem truncExp_gaussProb_eq_connected [Fintype A] [DecidableEq A] {T C : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (hTC : ∀ w, T (C w) = w) [IsProbabilityMeasure (gaussProb T)]
    (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) {n : ℕ} (hn : 0 < n) :
    truncExp (moments (gaussProb T) (fun x => ∑ a, monomial c k u a x)) n =
      ∑ g : Fin n → A, (∏ v, c (g v)) *
        ∑ τ ∈ (matchings (legsOf (legVertex k g) Finset.univ)).filter
            (fun τ => IsConnectedOn (legVertex k g) τ Finset.univ),
          matchingWeight C (legVector k u g) (legsOf (legVertex k g) Finset.univ) τ := by
  rw [truncExp_moments_sum_eq (gaussProb T) (monomial c k u) (integrable_prod_sum_monomial hT hpos c k u) hn]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hfun : (fun B => ∫ x, ∏ v ∈ B, monomial c k u (g v) x ∂gaussProb T) =
      fun B => (∏ v ∈ B, c (g v)) * (gaussMoment T (legsOf (legVertex k g) B) (legVector k u g) /
        gaussMoment T (∅ : Finset (Fin (∑ v, k (g v)))) (legVector k u g)) :=
    funext fun B => integral_prod_monomial hT hpos c k u g B
  have hZ := (gaussMoment_empty_pos hT hpos (legVector k u g)).ne'
  have hM0 : (fun B : Finset (Fin n) => gaussMoment T (legsOf (legVertex k g) B) (legVector k u g) /
      gaussMoment T (∅ : Finset (Fin (∑ v, k (g v)))) (legVector k u g)) ∅ = 1 := by
    have hl : legsOf (legVertex k g) (∅ : Finset (Fin n)) = ∅ := by
      ext l
      simp [legsOf]
    simp only [hl]
    exact div_self hZ
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [hfun, jointCumulant_mul_prod _ hM0 (fun v => c (g v)) Finset.univ Finset.univ_nonempty,
    jointCumulant_gaussMoment_eq_connected hT hpos hTC (legVertex k g) (legVector k u g) Finset.univ
      Finset.univ_nonempty]

end Polynomials

end GaussianBlockSpin
