import GaussianBlockSpin.MatrixInvSqrt

/-! Exponential decay of matrix powers and of the inverse square root, for a function `dist` on pairs of indices with
the triangle inequality and `dist x x = 0`:
* WBound: weighted row sums `Σ_y |M x y| e^{δ dist(x,y)} ≤ K`, closed under products (submultiplicative) and powers;
* abs_apply_le_norm: entries are at most the L2 operator norm;
* abs_pow_apply_le: `|N^n x y| ≤ min(θ^n, K^n e^{-δ d}) ≤ (θ^{1-s} K^s)^n e^{-s δ d}`;
* abs_invSqrt_apply_le: `|A x y| ≤ γ₁^{-1/2} (1 - θ^{1-s} K^s)⁻¹ e^{-s δ dist(x,y)}` for the inverse square root
  `A = γ₁^{-1/2} Σ c_n N^n` of MatrixInvSqrt. -/

namespace GaussianBlockSpin

open Matrix Real
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (dist : ι → ι → ℝ)

/-- Weighted row sums bounded by `K`. -/
def WBound (δ : ℝ) (M : Matrix ι ι ℝ) (K : ℝ) : Prop := ∀ x, ∑ y, |M x y| * exp (δ * dist x y) ≤ K

omit [DecidableEq ι] in
/-- **Weighted row sums are submultiplicative** (triangle inequality, `δ ≥ 0`). -/
lemma WBound.mul {δ : ℝ} (hδ : 0 ≤ δ) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z) {M M' : Matrix ι ι ℝ}
    {K K' : ℝ} (hM : WBound dist δ M K) (hM' : WBound dist δ M' K') (hK' : 0 ≤ K') :
    WBound dist δ (M * M') (K * K') := by
  intro x
  calc ∑ z, |(M * M') x z| * exp (δ * dist x z)
      ≤ ∑ z, ∑ y, |M x y| * exp (δ * dist x y) * (|M' y z| * exp (δ * dist y z)) := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [mul_apply]
        refine (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (exp_pos _).le).trans ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul]
        have he : exp (δ * dist x z) ≤ exp (δ * dist x y) * exp (δ * dist y z) := by
          rw [← exp_add]; exact exp_le_exp.mpr (by nlinarith [htri x y z])
        calc |M x y| * |M' y z| * exp (δ * dist x z)
            ≤ |M x y| * |M' y z| * (exp (δ * dist x y) * exp (δ * dist y z)) :=
              mul_le_mul_of_nonneg_left he (by positivity)
          _ = _ := by ring
    _ = ∑ y, |M x y| * exp (δ * dist x y) * ∑ z, |M' y z| * exp (δ * dist y z) := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
    _ ≤ ∑ y, |M x y| * exp (δ * dist x y) * K' :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hM' y) (by positivity)
    _ = (∑ y, |M x y| * exp (δ * dist x y)) * K' := by rw [Finset.sum_mul]
    _ ≤ K * K' := mul_le_mul_of_nonneg_right (hM x) hK'

lemma WBound.one {δ : ℝ} (hself : ∀ x, dist x x = 0) : WBound dist δ (1 : Matrix ι ι ℝ) 1 := by
  intro x
  rw [Finset.sum_eq_single x (fun y _ hyx => by simp [one_apply_ne' hyx]) (by simp)]
  simp [hself]

/-- **Powers**: `WBound δ N K` gives `WBound δ (N^n) (K^n)`. -/
lemma WBound.pow {δ : ℝ} (hδ : 0 ≤ δ) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z) (hself : ∀ x, dist x x = 0)
    {N : Matrix ι ι ℝ} {K : ℝ} (hK : 0 ≤ K) (hN : WBound dist δ N K) (n : ℕ) : WBound dist δ (N ^ n) (K ^ n) := by
  induction n with
  | zero => simpa using WBound.one dist hself
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul dist hδ htri hN hK

omit [DecidableEq ι] in
lemma abs_apply_le_of_WBound {δ : ℝ} {M : Matrix ι ι ℝ} {K : ℝ} (hM : WBound dist δ M K) (x y : ι) :
    |M x y| * exp (δ * dist x y) ≤ K :=
  (Finset.single_le_sum (f := fun y => |M x y| * exp (δ * dist x y)) (fun y _ => by positivity)
    (Finset.mem_univ y)).trans (hM x)

/-- Entries are bounded by the L2 operator norm. -/
lemma abs_apply_le_norm (M : Matrix ι ι ℝ) (x y : ι) : |M x y| ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single y 1)
  have hnorm : ‖EuclideanSpace.single y (1 : ℝ)‖ = 1 := by simp
  rw [hnorm, mul_one] at h
  have hcoord : M x y = ((EuclideanSpace.equiv ι ℝ).symm (M *ᵥ (EuclideanSpace.single y (1 : ℝ)).ofLp)) x := by
    simp
  rw [hcoord, ← Real.norm_eq_abs]
  exact (PiLp.norm_apply_le _ x).trans h

omit [Fintype ι] [DecidableEq ι] in
/-- `min(a, b) ≤ a^{1-s} b^s`. -/
lemma min_le_rpow_mul_rpow {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    min a b ≤ a ^ (1 - s) * b ^ s := by
  have hm0 : 0 ≤ min a b := le_min ha hb
  calc min a b = min a b ^ (1 - s) * min a b ^ s := by
        rw [← rpow_add' hm0 (by linarith : (1 - s) + s ≠ 0)]; simp
    _ ≤ a ^ (1 - s) * b ^ s := by
        have h1s : 0 ≤ 1 - s := by linarith
        gcongr
        · exact min_le_left a b
        · exact min_le_right a b

/-- **Decay of powers**: `|N^n x y| ≤ (θ^{1-s} K^s)^n e^{-s δ dist(x,y)}` if `‖N‖ ≤ θ` and `WBound δ N K`. -/
lemma abs_pow_apply_le {δ θ K s : ℝ} (hδ : 0 ≤ δ) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (hself : ∀ x, dist x x = 0) {N : Matrix ι ι ℝ} (hθ0 : 0 ≤ θ) (hθ : ‖N‖ ≤ θ) (hK : 0 ≤ K)
    (hW : WBound dist δ N K) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) (x y : ι) :
    |(N ^ n) x y| ≤ (θ ^ (1 - s) * K ^ s) ^ n * exp (-(s * δ * dist x y)) := by
  have h1 : |(N ^ n) x y| ≤ θ ^ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      by_cases hxy : x = y
      · simp [hxy]
      · simp [one_apply_ne hxy]
    · exact (abs_apply_le_norm _ x y).trans ((norm_pow_le' N hn).trans (pow_le_pow_left₀ (norm_nonneg _) hθ n))
  have h2 : |(N ^ n) x y| ≤ K ^ n * exp (-(δ * dist x y)) := by
    have := abs_apply_le_of_WBound dist (hW.pow dist hδ htri hself hK n) x y
    rw [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]
    exact this
  have hmin := min_le_rpow_mul_rpow (pow_nonneg hθ0 n) (by positivity : (0 : ℝ) ≤ K ^ n * exp (-(δ * dist x y)))
    hs0 hs1
  refine (le_min h1 h2).trans (hmin.trans (le_of_eq ?_))
  rw [mul_rpow (pow_nonneg hK n) (exp_pos _).le, ← exp_mul, ← rpow_natCast, ← rpow_natCast, ← rpow_mul hθ0,
    ← rpow_mul hK, mul_pow, ← rpow_natCast (θ ^ (1 - s)), ← rpow_natCast (K ^ s), ← rpow_mul hθ0, ← rpow_mul hK]
  rw [mul_comm (1 - s), mul_comm s (n : ℝ)]
  ring_nf

/-- **Decay of the inverse square root**: `|A x y| ≤ γ₁^{-1/2} (1 - ρ)⁻¹ e^{-s δ dist(x,y)}`,
`ρ = θ^{1-s} K^s < 1`, for `A = γ₁^{-1/2} Σ c_n N^n`, `‖N‖ ≤ θ < 1`, `WBound δ N K`. -/
theorem abs_invSqrt_apply_le {Q : Matrix ι ι ℝ} {γ₁ δ θ K s : ℝ} (hγ₁ : 0 < γ₁) (hδ : 0 ≤ δ)
    (htri : ∀ x y z, dist x z ≤ dist x y + dist y z) (hself : ∀ x, dist x x = 0) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hθ : ‖precN Q γ₁‖ ≤ θ) (hK : 0 ≤ K) (hW : WBound dist δ (precN Q γ₁) K) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (hρ : θ ^ (1 - s) * K ^ s < 1) (x y : ι) :
    |invSqrt Q γ₁ x y| ≤ (Real.sqrt γ₁)⁻¹ * (1 - θ ^ (1 - s) * K ^ s)⁻¹ * exp (-(s * δ * dist x y)) := by
  set N := precN Q γ₁ with hNdef
  set ρ := θ ^ (1 - s) * K ^ s with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hN : ‖N‖ < 1 := hθ.trans_lt hθ1
  have hsum := (summable_norm_sqrtCoef_smul hN).of_norm
  have hentry : invSqrt Q γ₁ x y = (Real.sqrt γ₁)⁻¹ * ∑' n, sqrtCoef n * (N ^ n) x y := by
    have h1 : (∑' n, sqrtCoef n • N ^ n) x y = ∑' n, (sqrtCoef n • N ^ n) x y := by
      have hx : (∑' n, sqrtCoef n • N ^ n) x = ∑' n, (sqrtCoef n • N ^ n) x := Pi.tsum_apply hsum
      rw [hx]
      exact Pi.tsum_apply (Pi.summable.mp hsum x)
    show (Real.sqrt γ₁)⁻¹ * (∑' n, sqrtCoef n • N ^ n) x y = _
    rw [h1]
    rfl
  have hb : ∀ n, |sqrtCoef n * (N ^ n) x y| ≤ ρ ^ n * exp (-(s * δ * dist x y)) := fun n => by
    rw [abs_mul, abs_of_nonneg (sqrtCoef_nonneg n)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (sqrtCoef_le_one n)).trans
      (abs_pow_apply_le dist hδ htri hself hθ0 hθ hK hW hs0 hs1 n x y)
  have hgeo : Summable fun n => ρ ^ n * exp (-(s * δ * dist x y)) :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_right _
  have habs : Summable fun n => |sqrtCoef n * (N ^ n) x y| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hb hgeo
  rw [hentry, abs_mul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hγ₁)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  calc |∑' n, sqrtCoef n * (N ^ n) x y| ≤ ∑' n, |sqrtCoef n * (N ^ n) x y| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun n => sqrtCoef n * (N ^ n) x y) (by simpa only [Real.norm_eq_abs] using habs)
    _ ≤ ∑' n, ρ ^ n * exp (-(s * δ * dist x y)) := habs.tsum_le_tsum hb hgeo
    _ = (1 - ρ)⁻¹ * exp (-(s * δ * dist x y)) := by rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0 hρ]

end GaussianBlockSpin
