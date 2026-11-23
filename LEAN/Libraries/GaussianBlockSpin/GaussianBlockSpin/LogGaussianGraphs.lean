import GaussianBlockSpin.ParametricIntegrals
import GaussianBlockSpin.GaussianBlockGraphs

/-! The mixed Taylor coefficients of `log ∫ e^{F x} dν` at `(0, 0)` (`e` two-sided, `λ` within `s`): sums over the
partitions of the derivative slots of the joint cumulants of the block derivatives of `F` (mixedCoeff_log_integral_exp),
and, for the normalised Gaussian measure and polynomial block derivatives, sums over slot partitions, monomial choices
and connected graphs (mixedCoeff_log_gaussIntegral_eq_connected): the graph expansion of the Taylor coefficients of
`E_k = -log[…]` of I.(3.35)-(3.36), III (1.4)-(1.5), once the bracket is written in this form. -/

open MeasureTheory Filter Metric
open scoped Topology RealInnerProductSpace

namespace GaussianBlockSpin

section General

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- **The mixed Taylor coefficients of `log ∫ e^F` as sums over slot partitions of block cumulants**: for a probability
measure `ν`, `F x` nested-smooth of order `(A, B)` with `F x 0 0 = 0`, `G x = e^{F x}` satisfying the domination
hypotheses of integral_nestedSmooth_mixedCoeff, and the block variables `X_C = ∂^C F x (0, 0)` with integrable products
over the blocks of every partition of every slot set (`hint`), `∂_λ^b ∂_e^a log ∫ e^{F x} dν` at `(0, 0)`
(`0 < a + b`, `a ≤ A`, `b ≤ B`) is the sum over the partitions `π` of the `a + b` derivative slots of the joint cumulants
of the blocks `(X_C)_{C ∈ π}`. -/
theorem mixedCoeff_log_integral_exp [IsProbabilityMeasure ν] {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hs_conv : Convex ℝ s) (h0 : (0 : ℝ) ∈ s) {ε : ℝ} (hε : 0 < ε) (hu : UniqueDiffOn ℝ (s ∩ ball 0 ε))
    {A B : ℕ} (F : Ω → ℝ → ℝ → ℝ) (hF : ∀ x, NestedSmooth s A B (F x)) (hF0 : ∀ x, F x 0 0 = 0)
    {bound : Ω → ℝ} (hb : Integrable bound ν)
    (hE_smooth : ∀ x, ∀ l ∈ s ∩ ball 0 ε, ContDiffOn ℝ A (fun e => Real.exp (F x e l)) (ball 0 ε))
    (hE_bound : ∀ x, ∀ l ∈ s ∩ ball 0 ε, ∀ i ≤ A, ∀ e ∈ ball (0 : ℝ) ε,
      |iteratedDeriv i (fun e => Real.exp (F x e l)) e| ≤ bound x)
    (hE_meas : ∀ l ∈ s ∩ ball 0 ε, ∀ i ≤ A, ∀ e ∈ ball (0 : ℝ) ε,
      AEStronglyMeasurable (fun x => iteratedDeriv i (fun e => Real.exp (F x e l)) e) ν)
    (hL_smooth : ∀ x, ∀ i ≤ A,
      ContDiffOn ℝ B (fun l => iteratedDeriv i (fun e => Real.exp (F x e l)) 0) (s ∩ ball 0 ε))
    (hL_bound : ∀ x, ∀ i ≤ A, ∀ j ≤ B, ∀ l ∈ s ∩ ball 0 ε,
      |iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => Real.exp (F x e l)) 0) (s ∩ ball 0 ε) l| ≤ bound x)
    (hL_meas : ∀ i ≤ A, ∀ j ≤ B, ∀ l ∈ s ∩ ball 0 ε, AEStronglyMeasurable
      (fun x => iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => Real.exp (F x e l)) 0) (s ∩ ball 0 ε) l) ν)
    {a b : ℕ} (ha : a ≤ A) (hb' : b ≤ B) (hab : 0 < a + b)
    (hint : ∀ S : Finset (Fin (a + b)), ∀ π ∈ partsOf S,
      Integrable (fun x => ∏ C ∈ π, mixedCoeff s (eCount a C) (lCount a C) (F x)) ν)
    (d : Fin (a + b)) :
    mixedCoeff s a b (fun e l => Real.log (∫ x, Real.exp (F x e l) ∂ν)) =
      ∑ π ∈ partsOf Finset.univ, blockCumulant
        (fun π' => ∫ x, ∏ C ∈ π', mixedCoeff s (eCount a C) (lCount a C) (F x) ∂ν) d π := by
  obtain ⟨hZ, hcoeff⟩ := integral_nestedSmooth_mixedCoeff (ν := ν) (G := fun x e l => Real.exp (F x e l)) hs_conv h0
    hε hu hb hE_smooth hE_bound hE_meas hL_smooth hL_bound hL_meas
  have hZ00 : ∫ x, Real.exp (F x 0 0) ∂ν = 1 := by
    simp [hF0]
  have hpos : 0 < ∫ x, Real.exp (F x 0 0) ∂ν := by rw [hZ00]; exact one_pos
  rw [mixedCoeff_log_eq_jointCumulant hs h0 hZ hpos ha hb' hab]
  rw [← jointCumulant_integral_mixedCoeff_exp ν hs h0 F hF hF0 ha hb' hint d hab]
  congr 1
  funext S
  rw [hZ00, div_one]
  exact hcoeff _ ((eCount_mono a (Finset.subset_univ S)).trans (eCount_univ a b).le |>.trans ha)
    _ ((lCount_mono a (Finset.subset_univ S)).trans (lCount_univ a b).le |>.trans hb')

end General

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {A : Type*}

/-- All products of partial sums of vertex-dependent monomials (vertices of any finite type) are integrable for the
normalised Gaussian measure. -/
lemma integrable_prod_sum_monomial_of_fintype {ι : Type*} [Fintype ι] [Fintype A] {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (c : ι → A → ℝ) (k : ι → A → ℕ)
    (u : ∀ v a, Fin (k v a) → E) (R : Finset ι) (t : ι → Finset A) :
    Integrable (fun x => ∏ v ∈ R, ∑ a ∈ t v, monomial (c v) (k v) (u v) a x) (gaussProb T) := by
  rw [integrable_gaussProb_iff hT hpos]
  set D := ∑ v, ∑ a, k v a
  set Ka : ι → A → ℝ := fun v a => |c v a| * ∏ i, ‖u v a i‖
  set K1 := ∑ v, ∑ a, Ka v a
  have hKa : ∀ v a, 0 ≤ Ka v a := fun v a => by positivity
  have hmono : ∀ v a x, |monomial (c v) (k v) (u v) a x| ≤ Ka v a * (1 + ‖x‖) ^ D := by
    intro v a x
    unfold monomial
    rw [abs_mul, Finset.abs_prod]
    have h1 : ∏ i, |⟪u v a i, x⟫| ≤ ∏ i, (‖u v a i‖ * ‖x‖) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => abs_real_inner_le_norm _ _
    have h2 : ∏ i : Fin (k v a), (‖u v a i‖ * ‖x‖) ≤ (∏ i, ‖u v a i‖) * (1 + ‖x‖) ^ D := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hk : k v a ≤ D := (Finset.single_le_sum (fun b _ => Nat.zero_le (k v b)) (Finset.mem_univ a)).trans
        (Finset.single_le_sum (f := fun w => ∑ b, k w b) (fun w _ => Nat.zero_le _) (Finset.mem_univ v))
      have : ‖x‖ ^ k v a ≤ (1 + ‖x‖) ^ D :=
        (pow_le_pow_left₀ (norm_nonneg x) (by linarith) (k v a)).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hk)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc |c v a| * ∏ i, |⟪u v a i, x⟫| ≤ |c v a| * ((∏ i, ‖u v a i‖) * (1 + ‖x‖) ^ D) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
      _ = Ka v a * (1 + ‖x‖) ^ D := by simp only [Ka]; ring
  have hsum : ∀ v x, |∑ a ∈ t v, monomial (c v) (k v) (u v) a x| ≤ K1 * (1 + ‖x‖) ^ D := by
    intro v x
    calc |∑ a ∈ t v, monomial (c v) (k v) (u v) a x| ≤ ∑ a ∈ t v, |monomial (c v) (k v) (u v) a x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ t v, Ka v a * (1 + ‖x‖) ^ D := Finset.sum_le_sum fun a _ => hmono v a x
      _ ≤ ∑ a, Ka v a * (1 + ‖x‖) ^ D :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => by positivity
      _ = (∑ a, Ka v a) * (1 + ‖x‖) ^ D := by rw [← Finset.sum_mul]
      _ ≤ K1 * (1 + ‖x‖) ^ D := by
          gcongr
          exact Finset.single_le_sum (f := fun w => ∑ a, Ka w a) (fun w _ => Finset.sum_nonneg fun a _ => hKa w a)
            (Finset.mem_univ v)
  refine integrable_mul_gaussWeight_of_le_one_add hT hpos ?_ (K := K1 ^ R.card) (D * R.card) fun x => ?_
  · refine continuous_finsetProd R fun v _ => continuous_finsetSum _ fun a _ => ?_
    unfold monomial
    exact continuous_const.mul (continuous_finsetProd _ fun i _ => continuous_const.inner continuous_id)
  · rw [Finset.abs_prod]
    calc ∏ v ∈ R, |∑ a ∈ t v, monomial (c v) (k v) (u v) a x| ≤ ∏ v ∈ R, (K1 * (1 + ‖x‖) ^ D) :=
          Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) fun v _ => hsum v x
      _ = K1 ^ R.card * (1 + ‖x‖) ^ (D * R.card) := by rw [Finset.prod_const, mul_pow, pow_mul]

/-- **The mixed Taylor coefficients of `log ∫ e^F dμ_T` are sums over slot partitions and connected graphs**: for the
normalised Gaussian measure (`T` symmetric positive definite, `T C = 1`), `F` as in mixedCoeff_log_integral_exp, and the
block derivatives `∂^Q F x (0, 0)` polynomials in `x`, `Σ_{a'} c_{Q,a'} ∏_i ⟪u_{Q,a',i}, x⟫` (`Q` a set of derivative
slots), the coefficient `∂_λ^b ∂_e^a log ∫ e^{F x} dμ_T` at `(0, 0)` is the sum over the partitions `π` of the `a + b`
slots, over the monomial choices `g` for the blocks of `π` (enumerated by smallest slot), of `∏ c` times the sum over
the perfect matchings of all legs that connect the blocks, of `∏_{l < σ l} ⟪w_l, C w_{σ l}⟫`. -/
theorem mixedCoeff_log_gaussIntegral_eq_connected [Fintype A] [DecidableEq A] {T C : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (hTC : ∀ w, T (C w) = w)
    [IsProbabilityMeasure (gaussProb T)] {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hs_conv : Convex ℝ s)
    (h0 : (0 : ℝ) ∈ s) {ε : ℝ} (hε : 0 < ε) (hu : UniqueDiffOn ℝ (s ∩ ball 0 ε)) {NA NB : ℕ}
    (F : E → ℝ → ℝ → ℝ) (hF : ∀ x, NestedSmooth s NA NB (F x)) (hF0 : ∀ x, F x 0 0 = 0)
    {bound : E → ℝ} (hb : Integrable bound (gaussProb T))
    (hE_smooth : ∀ x, ∀ l ∈ s ∩ ball 0 ε, ContDiffOn ℝ NA (fun e => Real.exp (F x e l)) (ball 0 ε))
    (hE_bound : ∀ x, ∀ l ∈ s ∩ ball 0 ε, ∀ i ≤ NA, ∀ e ∈ ball (0 : ℝ) ε,
      |iteratedDeriv i (fun e => Real.exp (F x e l)) e| ≤ bound x)
    (hE_meas : ∀ l ∈ s ∩ ball 0 ε, ∀ i ≤ NA, ∀ e ∈ ball (0 : ℝ) ε,
      AEStronglyMeasurable (fun x => iteratedDeriv i (fun e => Real.exp (F x e l)) e) (gaussProb T))
    (hL_smooth : ∀ x, ∀ i ≤ NA,
      ContDiffOn ℝ NB (fun l => iteratedDeriv i (fun e => Real.exp (F x e l)) 0) (s ∩ ball 0 ε))
    (hL_bound : ∀ x, ∀ i ≤ NA, ∀ j ≤ NB, ∀ l ∈ s ∩ ball 0 ε,
      |iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => Real.exp (F x e l)) 0) (s ∩ ball 0 ε) l| ≤ bound x)
    (hL_meas : ∀ i ≤ NA, ∀ j ≤ NB, ∀ l ∈ s ∩ ball 0 ε, AEStronglyMeasurable
      (fun x => iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => Real.exp (F x e l)) 0) (s ∩ ball 0 ε) l)
      (gaussProb T))
    {a b : ℕ} (ha : a ≤ NA) (hb' : b ≤ NB) (hab : 0 < a + b)
    (c : Finset (Fin (a + b)) → A → ℝ) (k : Finset (Fin (a + b)) → A → ℕ) (u : ∀ Q a', Fin (k Q a') → E)
    (hX : ∀ x (Q : Finset (Fin (a + b))),
      mixedCoeff s (eCount a Q) (lCount a Q) (F x) = ∑ a', monomial (c Q) (k Q) (u Q) a' x)
    (d : Fin (a + b)) :
    mixedCoeff s a b (fun e l => Real.log (∫ x, Real.exp (F x e l) ∂gaussProb T)) =
      ∑ π ∈ (partsOf (Finset.univ : Finset (Fin (a + b)))).attach,
        ∑ g : Fin π.1.card → A, (∏ v, c (blockEnum d (mem_partsOf.mp π.2) v) (g v)) *
          ∑ τ ∈ (matchings (legsOf (legVertexV (fun v => k (blockEnum d (mem_partsOf.mp π.2) v)) g)
              Finset.univ)).filter
              (fun τ => IsConnectedOn (legVertexV (fun v => k (blockEnum d (mem_partsOf.mp π.2) v)) g) τ
                Finset.univ),
            matchingWeight C (legVectorV (fun v => k (blockEnum d (mem_partsOf.mp π.2) v))
              (fun v => u (blockEnum d (mem_partsOf.mp π.2) v)) g)
              (legsOf (legVertexV (fun v => k (blockEnum d (mem_partsOf.mp π.2) v)) g) Finset.univ) τ := by
  have hint : ∀ S : Finset (Fin (a + b)), ∀ π ∈ partsOf S,
      Integrable (fun x => ∏ Q ∈ π, mixedCoeff s (eCount a Q) (lCount a Q) (F x)) (gaussProb T) := by
    intro S π _
    simp_rw [hX]
    exact integrable_prod_sum_monomial_of_fintype hT hpos c k u π (fun _ => Finset.univ)
  have hXf : (fun π' : Finset (Finset (Fin (a + b))) =>
      ∫ x, ∏ Q ∈ π', mixedCoeff s (eCount a Q) (lCount a Q) (F x) ∂gaussProb T) =
      fun π' => ∫ x, ∏ Q ∈ π', ∑ a', monomial (c Q) (k Q) (u Q) a' x ∂gaussProb T := by
    funext π'
    simp_rw [hX]
  rw [mixedCoeff_log_integral_exp hs hs_conv h0 hε hu F hF hF0 hb hE_smooth hE_bound hE_meas hL_smooth hL_bound
    hL_meas ha hb' hab hint d, hXf, ← Finset.sum_attach]
  have hne : (Finset.univ : Finset (Fin (a + b))).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hab⟩⟩
  exact Finset.sum_congr rfl fun π _ => blockCumulant_gaussProb_eq_connected hT hpos hTC c k u d hne π.2

end Gaussian

end GaussianBlockSpin
