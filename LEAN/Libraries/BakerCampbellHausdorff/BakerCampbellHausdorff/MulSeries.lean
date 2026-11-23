import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# The Cauchy product of algebra-valued power series

Let `𝔸` be a normed algebra over `𝕂 = ℝ` or `ℂ` and `E` a normed space over `𝕂`.  For formal
multilinear series `p q : FormalMultilinearSeries 𝕂 E 𝔸` we define their Cauchy product
`mulSeries p q`, whose `n`-th coefficient is
`(v₁, …, vₙ) ↦ ∑_{i + j = n} pᵢ (v₁, …, vᵢ) * qⱼ (vᵢ₊₁, …, vₙ)`, and show that it is the power
series of `x ↦ f x * g x` whenever `p`, `q` are the power series of `f`, `g`.

We do not assume `‖1‖ = 1` in `𝔸`.

## Main definitions

* `BakerCampbellHausdorff.mulConcat`: the concatenation product
  `(v₁, …, v_{i+j}) ↦ f (v₁, …, vᵢ) * g (vᵢ₊₁, …, v_{i+j})` of two continuous multilinear maps.
* `BakerCampbellHausdorff.mulSeries`: the Cauchy product of two formal multilinear series.

## Main results

* `BakerCampbellHausdorff.norm_mulConcat_le`: `‖mulConcat f g‖ ≤ ‖f‖ * ‖g‖`.
* `BakerCampbellHausdorff.mulSeries_apply_diag`: on the diagonal, the `n`-th coefficient is
  `∑_{i + j = n} pᵢ (x, …, x) * qⱼ (x, …, x)`.
* `BakerCampbellHausdorff.mulSeries_zero_apply`: the constant coefficient is `1` if those of
  `p` and `q` are.
* `BakerCampbellHausdorff.norm_mulSeries_le`: if `p₀ = q₀ = 1`, `‖pₙ‖ ≤ aⁿ / n!` and
  `‖qₙ‖ ≤ bⁿ / n!` for `n ≥ 1`, then `‖(mulSeries p q)ₙ‖ ≤ (a + b)ⁿ / n!` for `n ≥ 1`.
* `HasFPowerSeriesOnBall.mulSeries`: if `f`, `g` have power series `p`, `q` on the ball of
  radius `r` about `0`, then `x ↦ f x * g x` has power series `mulSeries p q` there.

## Proof sketch

`mulConcat f g` is built with `MultilinearMap.mkContinuous`; multilinearity is checked by
splitting the updated index with `Fin.addCases`, and the norm bound follows from
`Fin.prod_univ_add`.  The `n`-th coefficient of `mulSeries p q` sums `mulConcat pᵢ qⱼ` over the
antidiagonal `i + j = n`, transported from `Fin (i + j)` to `Fin n` by `domDomCongr`.  For the
explicit bound, the terms with `i = 0` (resp. `j = 0`) have norm at most `‖qₙ‖` (resp. `‖pₙ‖`)
since `p₀ = 1` exactly (no factor `‖1‖`), the others at most `‖pᵢ‖ ‖qⱼ‖`, and the binomial
theorem gives `∑_{i + j = n} aⁱ bʲ / (i! j!) = (a + b)ⁿ / n!`.  The power series statement is the
Cauchy product formula for absolutely convergent series in a complete normed ring, together
with `‖(mulSeries p q)ₙ‖ ≤ ∑_{i + j = n} ‖pᵢ‖ ‖qⱼ‖` for the radius of convergence.
-/

noncomputable section

open scoped Nat ENNReal NNReal

namespace BakerCampbellHausdorff

variable {𝕂 E 𝔸 : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E] [NormedRing 𝔸]
  [NormedAlgebra 𝕂 𝔸]

/-! ### The concatenation product of multilinear maps -/

private theorem castAdd_ne_natAdd {i j : ℕ} (k : Fin i) (l : Fin j) :
    Fin.castAdd j k ≠ Fin.natAdd i l := by
  rw [Ne, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- The multilinear map `(v₁,…,v_{i+j}) ↦ f (v₁,…,vᵢ) * g (vᵢ₊₁,…,v_{i+j})` underlying
`mulConcat`. -/
def mulConcatAux {i j : ℕ} (f : ContinuousMultilinearMap 𝕂 (fun _ : Fin i => E) 𝔸)
    (g : ContinuousMultilinearMap 𝕂 (fun _ : Fin j => E) 𝔸) :
    MultilinearMap 𝕂 (fun _ : Fin (i + j) => E) 𝔸 where
  toFun v := f (fun k => v (Fin.castAdd j k)) * g (fun k => v (Fin.natAdd i k))
  map_update_add' v t x y := by
    induction t using Fin.addCases with
    | left k =>
      simp only [Function.update_comp_eq_of_injective' v (Fin.castAdd_injective i j),
        Function.update_comp_eq_of_forall_ne' v _ (fun l => (castAdd_ne_natAdd k l).symm),
        f.map_update_add, add_mul]
    | right k =>
      simp only [Function.update_comp_eq_of_injective' v (Fin.natAdd_injective j i),
        Function.update_comp_eq_of_forall_ne' v _ (fun l => castAdd_ne_natAdd l k),
        g.map_update_add, mul_add]
  map_update_smul' v t c x := by
    induction t using Fin.addCases with
    | left k =>
      simp only [Function.update_comp_eq_of_injective' v (Fin.castAdd_injective i j),
        Function.update_comp_eq_of_forall_ne' v _ (fun l => (castAdd_ne_natAdd k l).symm),
        f.map_update_smul, smul_mul_assoc]
    | right k =>
      simp only [Function.update_comp_eq_of_injective' v (Fin.natAdd_injective j i),
        Function.update_comp_eq_of_forall_ne' v _ (fun l => castAdd_ne_natAdd l k),
        g.map_update_smul, mul_smul_comm]

/-- The pointwise bound `‖mulConcatAux f g v‖ ≤ ‖f‖ ‖g‖ ∏ ‖vₜ‖`. -/
theorem norm_mulConcatAux_le {i j : ℕ} (f : ContinuousMultilinearMap 𝕂 (fun _ : Fin i => E) 𝔸)
    (g : ContinuousMultilinearMap 𝕂 (fun _ : Fin j => E) 𝔸) (v : Fin (i + j) → E) :
    ‖mulConcatAux f g v‖ ≤ ‖f‖ * ‖g‖ * ∏ t, ‖v t‖ := by
  rw [Fin.prod_univ_add]
  calc ‖mulConcatAux f g v‖
      ≤ ‖f fun k => v (Fin.castAdd j k)‖ * ‖g fun k => v (Fin.natAdd i k)‖ := norm_mul_le _ _
    _ ≤ (‖f‖ * ∏ k, ‖v (Fin.castAdd j k)‖) * (‖g‖ * ∏ k, ‖v (Fin.natAdd i k)‖) := by
        gcongr
        · exact f.le_opNorm _
        · exact g.le_opNorm _
    _ = _ := by ring

/-- Concatenation product: `(v₁,…,v_{i+j}) ↦ f (v₁,…,vᵢ) * g (vᵢ₊₁,…,v_{i+j})`. -/
def mulConcat {i j : ℕ} (f : ContinuousMultilinearMap 𝕂 (fun _ : Fin i => E) 𝔸)
    (g : ContinuousMultilinearMap 𝕂 (fun _ : Fin j => E) 𝔸) :
    ContinuousMultilinearMap 𝕂 (fun _ : Fin (i + j) => E) 𝔸 :=
  (mulConcatAux f g).mkContinuous (‖f‖ * ‖g‖) (norm_mulConcatAux_le f g)

@[simp]
theorem mulConcat_apply {i j : ℕ} (f : ContinuousMultilinearMap 𝕂 (fun _ : Fin i => E) 𝔸)
    (g : ContinuousMultilinearMap 𝕂 (fun _ : Fin j => E) 𝔸) (v : Fin (i + j) → E) :
    mulConcat f g v = f (fun k => v (Fin.castAdd j k)) * g (fun k => v (Fin.natAdd i k)) :=
  rfl

/-- `‖mulConcat f g‖ ≤ ‖f‖ * ‖g‖`. -/
theorem norm_mulConcat_le {i j : ℕ} (f : ContinuousMultilinearMap 𝕂 (fun _ : Fin i => E) 𝔸)
    (g : ContinuousMultilinearMap 𝕂 (fun _ : Fin j => E) 𝔸) : ‖mulConcat f g‖ ≤ ‖f‖ * ‖g‖ :=
  MultilinearMap.mkContinuous_norm_le _ (by positivity) _

/-- If the `0`-linear map `f` is the constant `1`, then `‖mulConcat f g‖ ≤ ‖g‖` (no factor
`‖1‖`). -/
theorem norm_mulConcat_le_right {j : ℕ} {f : ContinuousMultilinearMap 𝕂 (fun _ : Fin 0 => E) 𝔸}
    (hf : ∀ v, f v = 1) (g : ContinuousMultilinearMap 𝕂 (fun _ : Fin j => E) 𝔸) :
    ‖mulConcat f g‖ ≤ ‖g‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun v => ?_
  rw [mulConcat_apply, hf, one_mul, Fin.prod_univ_add, Fin.prod_univ_zero, one_mul]
  exact g.le_opNorm _

/-- If the `0`-linear map `g` is the constant `1`, then `‖mulConcat f g‖ ≤ ‖f‖` (no factor
`‖1‖`). -/
theorem norm_mulConcat_le_left {i : ℕ} (f : ContinuousMultilinearMap 𝕂 (fun _ : Fin i => E) 𝔸)
    {g : ContinuousMultilinearMap 𝕂 (fun _ : Fin 0 => E) 𝔸} (hg : ∀ v, g v = 1) :
    ‖mulConcat f g‖ ≤ ‖f‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun v => ?_
  rw [mulConcat_apply, hg, mul_one, Fin.prod_univ_add, Fin.prod_univ_zero, mul_one]
  exact f.le_opNorm _

/-! ### The Cauchy product of formal multilinear series -/

/-- The Cauchy product of two formal multilinear series: the `n`-th coefficient sums
`mulConcat (p i) (q j)` over `i + j = n`, transported from `Fin (i + j)` to `Fin n`. -/
def mulSeries (p q : FormalMultilinearSeries 𝕂 E 𝔸) : FormalMultilinearSeries 𝕂 E 𝔸 := fun n =>
  ∑ ij ∈ (Finset.antidiagonal n).attach,
    (mulConcat (p ij.1.1) (q ij.1.2)).domDomCongr (finCongr (Finset.mem_antidiagonal.mp ij.2))

/-- On the diagonal, `mulSeries p q n (x, …, x) = ∑_{i + j = n} pᵢ (x, …, x) * qⱼ (x, …, x)`. -/
theorem mulSeries_apply_diag (p q : FormalMultilinearSeries 𝕂 E 𝔸) (n : ℕ) (x : E) :
    mulSeries p q n (fun _ => x) =
      ∑ ij ∈ Finset.antidiagonal n, p ij.1 (fun _ => x) * q ij.2 (fun _ => x) := by
  simp only [mulSeries, sum_apply, ContinuousMultilinearMap.domDomCongr_apply, mulConcat_apply]
  exact Finset.sum_attach (Finset.antidiagonal n)
    (fun ij => p ij.1 (fun _ => x) * q ij.2 (fun _ => x))

/-- If the constant coefficients of `p` and `q` are `1`, so is that of `mulSeries p q`. -/
theorem mulSeries_zero_apply {p q : FormalMultilinearSeries 𝕂 E 𝔸} (hp : ∀ v, p 0 v = 1)
    (hq : ∀ v, q 0 v = 1) (v : Fin 0 → E) : mulSeries p q 0 v = 1 := by
  rw [show v = fun _ => (0 : E) from funext fun i => i.elim0, mulSeries_apply_diag,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hp, hq, mul_one]

/-- The general coefficient bound `‖(mulSeries p q)ₙ‖ ≤ ∑_{i + j = n} ‖pᵢ‖ ‖qⱼ‖`. -/
theorem norm_mulSeries_le_sum (p q : FormalMultilinearSeries 𝕂 E 𝔸) (n : ℕ) :
    ‖mulSeries p q n‖ ≤ ∑ ij ∈ Finset.antidiagonal n, ‖p ij.1‖ * ‖q ij.2‖ := by
  refine (norm_sum_le _ _).trans ?_
  simp only [ContinuousMultilinearMap.norm_domDomCongr]
  rw [← Finset.sum_attach (Finset.antidiagonal n) (fun ij => ‖p ij.1‖ * ‖q ij.2‖)]
  exact Finset.sum_le_sum fun ij _ => norm_mulConcat_le _ _

/-- The binomial theorem in the form `∑_{i + j = n} aⁱ bʲ / (i! j!) = (a + b)ⁿ / n!`. -/
theorem sum_antidiagonal_inv_factorial_mul_pow (a b : ℝ) (n : ℕ) :
    ∑ ij ∈ Finset.antidiagonal n, (ij.1 !⁻¹ : ℝ) * a ^ ij.1 * ((ij.2 !⁻¹ : ℝ) * b ^ ij.2) =
      (n !⁻¹ : ℝ) * (a + b) ^ n := by
  rw [(Commute.all a b).add_pow', Finset.mul_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  subst hij
  have h := Nat.add_choose_mul_factorial_mul_factorial ij.1 ij.2
  rw [nsmul_eq_mul, Nat.choose_symm_add, ← h]
  have hc : ((ij.1 + ij.2).choose ij.2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_left _ _)).ne'
  push_cast
  field_simp

/-- **Explicit coefficient bound** (no factor `‖1‖`): if `p₀ = q₀ = 1`, `‖pₙ‖ ≤ aⁿ / n!` and
`‖qₙ‖ ≤ bⁿ / n!` for `n ≥ 1`, then `‖(mulSeries p q)ₙ‖ ≤ (a + b)ⁿ / n!` for `n ≥ 1`. -/
theorem norm_mulSeries_le {p q : FormalMultilinearSeries 𝕂 E 𝔸} {a b : ℝ}
    (hp0 : ∀ v, p 0 v = 1) (hq0 : ∀ v, q 0 v = 1)
    (hp : ∀ n, 1 ≤ n → ‖p n‖ ≤ (n !⁻¹ : ℝ) * a ^ n)
    (hq : ∀ n, 1 ≤ n → ‖q n‖ ≤ (n !⁻¹ : ℝ) * b ^ n) {n : ℕ} (hn : 1 ≤ n) :
    ‖mulSeries p q n‖ ≤ (n !⁻¹ : ℝ) * (a + b) ^ n := by
  rw [← sum_antidiagonal_inv_factorial_mul_pow, ← Finset.sum_attach (Finset.antidiagonal n)
    (fun ij => (ij.1 !⁻¹ : ℝ) * a ^ ij.1 * ((ij.2 !⁻¹ : ℝ) * b ^ ij.2))]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ij _ => ?_)
  rw [ContinuousMultilinearMap.norm_domDomCongr]
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  rw [Finset.mem_antidiagonal] at hij
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine (norm_mulConcat_le_right hp0 _).trans ?_
    simpa using hq j (by omega)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine (norm_mulConcat_le_left _ hq0).trans ?_
    simpa using hp i hi
  · exact (norm_mulConcat_le _ _).trans
      (mul_le_mul (hp i hi) (hq j hj) (norm_nonneg _) ((norm_nonneg _).trans (hp i hi)))

/-- The radius of convergence of `mulSeries p q` is at least the smaller of those of `p`
and `q`. -/
theorem le_radius_mulSeries (p q : FormalMultilinearSeries 𝕂 E 𝔸) :
    min p.radius q.radius ≤ (mulSeries p q).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
  have hp := p.summable_norm_mul_pow (ht.trans_le (min_le_left _ _))
  have hq := q.summable_norm_mul_pow (ht.trans_le (min_le_right _ _))
  have hpq := summable_sum_mul_antidiagonal_of_summable_mul
    (f := fun n => ‖p n‖ * (t : ℝ) ^ n) (g := fun n => ‖q n‖ * (t : ℝ) ^ n)
    (hp.mul_of_nonneg hq (fun _ => by positivity) (fun _ => by positivity))
  refine (mulSeries p q).le_radius_of_summable_norm
    (hpq.of_nonneg_of_le (fun _ => by positivity) fun n => ?_)
  refine (mul_le_mul_of_nonneg_right (norm_mulSeries_le_sum p q n) (by positivity)).trans_eq ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  ring

/-- **Cauchy product of power series**: if `f` and `g` have power series `p` and `q` on the
ball of radius `r` about `0`, then `x ↦ f x * g x` has power series `mulSeries p q` there. -/
theorem _root_.HasFPowerSeriesOnBall.mulSeries [CompleteSpace 𝔸] {f g : E → 𝔸}
    {p q : FormalMultilinearSeries 𝕂 E 𝔸} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 r) (hg : HasFPowerSeriesOnBall g q 0 r) :
    HasFPowerSeriesOnBall (fun x => f x * g x) (mulSeries p q) 0 r where
  r_le := (le_min hf.r_le hg.r_le).trans (le_radius_mulSeries p q)
  r_pos := hf.r_pos
  hasSum {y} hy := by
    have hF := p.summable_norm_apply (Metric.eball_subset_eball hf.r_le hy)
    have hG := q.summable_norm_apply (Metric.eball_subset_eball hg.r_le hy)
    have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG
    rw [(hf.hasSum hy).tsum_eq, (hg.hasSum hy).tsum_eq] at h
    simp_rw [mulSeries_apply_diag]
    rw [h]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG).of_norm.hasSum

end BakerCampbellHausdorff
