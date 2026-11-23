/-
`lem:kernel-inverse` of BALABAN_CORE.tex: inverses of operators with decaying entries.

Setting. `ι` is the finite set `𝐁₁` of positive bonds, `V` the finite-dimensional complex Hilbert
space of the values (`𝔤^c` with the norm `‖·‖₂`), and an operator is given by its kernel
`T[c, c'] : V →L[ℂ] V`, acting on `L²(ι; V) = PiLp 2 (fun _ => V)` by `(Tμ)(c) = Σ_{c'} T[c, c'] μ(c')`.
`d` is a pseudometric on the set `𝐁` of points and `c ↦ c₋` the first end of a bond. The core's bound
`Σ_{c'} e^{-δd(c₋, c'₋)/4} ≤ 4c₁(½, ½δ)` (from `eq:summation`) is the hypothesis `hK` with
`K = 4c₁(½, ½δ)`, so that the core's rate `γδ/(24κc₁)` is `γδ/(6κK)`.

Hypothesis (b) of the core (real structure, symmetry, and `≥ γ‖μ‖²` on `𝔤`-valued functions) is used
in the core's proof only through its consequence on `𝔤^c`-valued functions,
`Re⟨μ, T₀μ⟩ ≥ γ‖μ‖²` (`hcoer`). That (b) implies it is `coercive_of_real`, proved for any real
subspace `W ⊂ V` with real inner products and `V = W + iW`; its instantiation with `W = 𝔤 ⊂ 𝔤^c` and
the Hilbert–Schmidt inner product is not formalised (it needs `𝔤^c` as an inner product space).

Proof (the core's): by the Schur test (`opBound_of_entry`) the conjugation by `e^{θρ}` changes `T₀`
by an operator of norm `≤ 4κθK/(eδ) ≤ γ/4`; with (c), `‖T_θ μ‖ ≥ (γ/2)‖μ‖`. The core concludes
with `‖T_θ⁻¹‖ ≤ 2/γ`; we use the lower bound directly on the solution of `Tu = δ_{c'} w`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Real

namespace CoreLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- `L²(ι; V)`. -/
abbrev L2 (ι V : Type*) [NormedAddCommGroup V] := PiLp 2 (fun _ : ι => V)

/-- The operator with kernel `K`: `(Kμ)(c) = Σ_{c'} K[c, c'] μ(c')`. -/
noncomputable def kerApply (K : ι → ι → (V →L[ℂ] V)) (μ : L2 ι V) : L2 ι V :=
  WithLp.toLp 2 fun c => ∑ c', K c c' (μ.ofLp c')

@[simp] lemma kerApply_apply (K : ι → ι → (V →L[ℂ] V)) (μ : L2 ι V) (c : ι) :
    (kerApply K μ).ofLp c = ∑ c', K c c' (μ.ofLp c') := rfl

/-- The operator with kernel `K` as a linear map. -/
noncomputable def kerLin (K : ι → ι → (V →L[ℂ] V)) : L2 ι V →ₗ[ℂ] L2 ι V where
  toFun := kerApply K
  map_add' μ ν := by
    ext c; simp [Finset.sum_add_distrib]
  map_smul' a μ := by
    ext c; simp [Finset.smul_sum]

/-- `‖K‖ ≤ M`. -/
def OpBound (K : ι → ι → (V →L[ℂ] V)) (M : ℝ) : Prop := ∀ μ : L2 ι V, ‖kerApply K μ‖ ≤ M * ‖μ‖

lemma norm_sq_L2 (μ : L2 ι V) : ‖μ‖ ^ 2 = ∑ c, ‖μ.ofLp c‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ μ

lemma norm_ofLp_le (μ : L2 ι V) (c : ι) : ‖μ.ofLp c‖ ≤ ‖μ‖ := by
  have h := norm_sq_L2 μ
  have : ‖μ.ofLp c‖ ^ 2 ≤ ‖μ‖ ^ 2 := by
    rw [h]
    exact Finset.single_le_sum (f := fun c => ‖μ.ofLp c‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ c)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-! ### The test of Schur -/

/-- An operator whose entries satisfy `‖K[c, c']‖ ≤ k(c, c')` has norm at most the larger of the
row sums `R` and the column sums `C` of `k`. -/
theorem opBound_of_entry (K : ι → ι → (V →L[ℂ] V)) (k : ι → ι → ℝ)
    (hk : ∀ c c', ‖K c c'‖ ≤ k c c') {R C : ℝ} (hR : ∀ c, ∑ c', k c c' ≤ R)
    (hC : ∀ c', ∑ c, k c c' ≤ C) : OpBound K (max R C) := by
  intro μ
  have hk0 : ∀ c c', 0 ≤ k c c' := fun c c' => (norm_nonneg _).trans (hk c c')
  by_cases hι : IsEmpty ι
  · have h0 : ∀ ν : L2 ι V, ‖ν‖ = 0 := fun ν => by
      have := norm_sq_L2 ν
      rw [Finset.univ_eq_empty, Finset.sum_empty] at this
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    rw [h0, h0, mul_zero]
  obtain ⟨c0⟩ := not_isEmpty_iff.1 hι
  have hR0 : 0 ≤ R := (Finset.sum_nonneg fun c' _ => hk0 c0 c').trans (hR c0)
  have hC0 : 0 ≤ C := (Finset.sum_nonneg fun c _ => hk0 c c0).trans (hC c0)
  have hM0 : 0 ≤ max R C := hR0.trans (le_max_left _ _)
  -- each component: `‖(Kμ)(c)‖ ≤ Σ_{c'} k(c, c') ‖μ(c')‖`
  have hcomp : ∀ c, ‖(kerApply K μ).ofLp c‖ ≤ ∑ c', k c c' * ‖μ.ofLp c'‖ := fun c => by
    rw [kerApply_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c' _ => ?_)
    exact ((K c c').le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hk c c') (norm_nonneg _))
  -- Cauchy–Schwarz with the weights `k(c, ·)`
  have hcs : ∀ c, (∑ c', k c c' * ‖μ.ofLp c'‖) ^ 2 ≤ R * ∑ c', k c c' * ‖μ.ofLp c'‖ ^ 2 :=
    fun c => by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c' => Real.sqrt (k c c'))
        (fun c' => Real.sqrt (k c c') * ‖μ.ofLp c'‖)
      have e1 : ∀ c', Real.sqrt (k c c') * (Real.sqrt (k c c') * ‖μ.ofLp c'‖) =
          k c c' * ‖μ.ofLp c'‖ := fun c' => by
        rw [← mul_assoc, Real.mul_self_sqrt (hk0 c c')]
      have e2 : ∀ c', Real.sqrt (k c c') ^ 2 = k c c' := fun c' => Real.sq_sqrt (hk0 c c')
      have e3 : ∀ c', (Real.sqrt (k c c') * ‖μ.ofLp c'‖) ^ 2 = k c c' * ‖μ.ofLp c'‖ ^ 2 :=
        fun c' => by rw [mul_pow, e2]
      simp only [e1, e2, e3] at h
      refine h.trans (mul_le_mul_of_nonneg_right (hR c) ?_)
      exact Finset.sum_nonneg fun c' _ => mul_nonneg (hk0 c c') (sq_nonneg _)
  have hsq : ‖kerApply K μ‖ ^ 2 ≤ (max R C) ^ 2 * ‖μ‖ ^ 2 := by
    rw [norm_sq_L2, norm_sq_L2]
    calc ∑ c, ‖(kerApply K μ).ofLp c‖ ^ 2
        ≤ ∑ c, R * ∑ c', k c c' * ‖μ.ofLp c'‖ ^ 2 := Finset.sum_le_sum fun c _ =>
          (pow_le_pow_left₀ (norm_nonneg _) (hcomp c) 2).trans (hcs c)
      _ = R * ∑ c', (∑ c, k c c') * ‖μ.ofLp c'‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.sum_mul]
      _ ≤ R * ∑ c', C * ‖μ.ofLp c'‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c' _ =>
            mul_le_mul_of_nonneg_right (hC c') (sq_nonneg _)) hR0
      _ = (R * C) * ∑ c', ‖μ.ofLp c'‖ ^ 2 := by rw [← Finset.mul_sum]; ring
      _ ≤ (max R C) ^ 2 * ∑ c', ‖μ.ofLp c'‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          rw [sq]
          exact mul_le_mul (le_max_left _ _) (le_max_right _ _) hC0 hM0
  rw [← mul_pow] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _)) two_ne_zero).1 hsq

/-! ### Conjugation by `e^{θρ}` -/

lemma kerApply_add (K L : ι → ι → (V →L[ℂ] V)) (μ : L2 ι V) :
    kerApply (K + L) μ = kerApply K μ + kerApply L μ := by
  ext c; simp [Finset.sum_add_distrib]

lemma kerApply_sub (K L : ι → ι → (V →L[ℂ] V)) (μ : L2 ι V) :
    kerApply (K - L) μ = kerApply K μ - kerApply L μ := by
  ext c; simp [Finset.sum_sub_distrib]

/-- The kernel `e^{θ(ρ(c) - ρ(c'))} K[c, c']`. -/
noncomputable def conjKer (θ : ℝ) (ρ : ι → ℝ) (K : ι → ι → (V →L[ℂ] V)) :
    ι → ι → (V →L[ℂ] V) :=
  fun c c' => ((Real.exp (θ * (ρ c - ρ c')) : ℝ) : ℂ) • K c c'

lemma conjKer_add (θ : ℝ) (ρ : ι → ℝ) (K L : ι → ι → (V →L[ℂ] V)) :
    conjKer θ ρ (K + L) = conjKer θ ρ K + conjKer θ ρ L := by
  funext c c'; simp [conjKer, smul_add]

lemma conjKer_zero (ρ : ι → ℝ) (K : ι → ι → (V →L[ℂ] V)) : conjKer 0 ρ K = K := by
  funext c c'; simp [conjKer]

/-- Multiplication by `e^{θρ}`. -/
noncomputable def weightMul (θ : ℝ) (ρ : ι → ℝ) (μ : L2 ι V) : L2 ι V :=
  WithLp.toLp 2 fun c => ((Real.exp (θ * ρ c) : ℝ) : ℂ) • μ.ofLp c

lemma kerApply_conjKer (θ : ℝ) (ρ : ι → ℝ) (K : ι → ι → (V →L[ℂ] V)) (μ : L2 ι V) :
    kerApply (conjKer θ ρ K) (weightMul θ ρ μ) = weightMul θ ρ (kerApply K μ) := by
  ext c
  simp only [kerApply_apply, weightMul, conjKer, ContinuousLinearMap.smul_apply, map_smul,
    Finset.smul_sum, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3; ring

/-- `δ_{c'} w`. -/
noncomputable def single (c' : ι) (w : V) : L2 ι V := WithLp.toLp 2 (Pi.single c' w)

lemma norm_single (c' : ι) (w : V) : ‖single c' w‖ = ‖w‖ := by
  have h := norm_sq_L2 (single c' w)
  rw [Finset.sum_eq_single c' (fun c _ hc => by simp [single, Pi.single_apply, hc])
    (fun h => absurd (Finset.mem_univ c') h)] at h
  simp only [single, WithLp.ofLp_toLp, Pi.single_eq_same] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma weightMul_single {θ : ℝ} {ρ : ι → ℝ} {c' : ι} (hρ : ρ c' = 0) (w : V) :
    weightMul θ ρ (single c' w) = single c' w := by
  ext c
  by_cases h : c = c'
  · subst h; simp [weightMul, single, hρ]
  · simp [weightMul, single, Pi.single_apply, h]

/-! ### Two elementary bounds -/

/-- `|e^x - 1| ≤ e^{θd} - 1` for `|x| ≤ θd`, and `e^{θd} - 1 ≤ θd e^{θd}`. -/
lemma abs_exp_sub_one_le {x a : ℝ} (hx : |x| ≤ a) : |Real.exp x - 1| ≤ a * Real.exp a := by
  have ha : 0 ≤ a := (abs_nonneg x).trans hx
  have h1 : |Real.exp x - 1| ≤ Real.exp |x| - 1 := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.one_le_exp h])]
    · rw [abs_of_nonpos h, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 h])]
      have := Real.add_one_le_exp x
      have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos x, Real.exp_pos (-x), Real.add_one_le_exp (-x)]
  have h2 : Real.exp a - 1 ≤ a * Real.exp a := by
    have := Real.add_one_le_exp (-a)
    have h3 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos a]
  calc |Real.exp x - 1| ≤ Real.exp |x| - 1 := h1
    _ ≤ Real.exp a - 1 := by linarith [Real.exp_le_exp.2 hx]
    _ ≤ a * Real.exp a := h2

/-- `d e^{-δd/4} ≤ 4/(eδ)`. -/
lemma mul_exp_neg_le {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d) :
    d * Real.exp (-(δ / 4) * d) ≤ 4 / (Real.exp 1 * δ) := by
  have h := Real.add_one_le_exp (δ / 4 * d - 1)
  rw [Real.exp_sub] at h
  have he := Real.exp_pos 1
  have hed := Real.exp_pos (δ / 4 * d)
  rw [le_div_iff₀ he, sub_add_cancel] at h
  rw [show -(δ / 4) * d = -(δ / 4 * d) by ring, Real.exp_neg, ← div_eq_mul_inv,
    div_le_div_iff₀ hed (by positivity)]
  nlinarith

/-- The entries of `T₀,θ - T₀`: `|e^{θ(ρ(c) - ρ(c'))} - 1| κ e^{-δd} ≤ (4κθ/(eδ)) e^{-δd/4}`. -/
lemma entry_conj_sub_le {δ κ θ d x : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (hθδ : θ ≤ δ / 2)
    (hd : 0 ≤ d) (hx : |x| ≤ θ * d) :
    |Real.exp x - 1| * (κ * Real.exp (-δ * d)) ≤
      4 * κ * θ / (Real.exp 1 * δ) * Real.exp (-(δ / 4) * d) := by
  have h1 := abs_exp_sub_one_le hx
  have h2 : Real.exp (θ * d) * Real.exp (-δ * d) ≤ Real.exp (-(δ / 4) * d) * Real.exp (-(δ / 4) * d) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]; nlinarith
  have h3 := mul_exp_neg_le hδ hd
  calc |Real.exp x - 1| * (κ * Real.exp (-δ * d))
      ≤ θ * d * Real.exp (θ * d) * (κ * Real.exp (-δ * d)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = κ * θ * (d * (Real.exp (θ * d) * Real.exp (-δ * d))) := by ring
    _ ≤ κ * θ * (d * (Real.exp (-(δ / 4) * d) * Real.exp (-(δ / 4) * d))) := by gcongr
    _ = κ * θ * (d * Real.exp (-(δ / 4) * d)) * Real.exp (-(δ / 4) * d) := by ring
    _ ≤ κ * θ * (4 / (Real.exp 1 * δ)) * Real.exp (-(δ / 4) * d) := by gcongr
    _ = 4 * κ * θ / (Real.exp 1 * δ) * Real.exp (-(δ / 4) * d) := by ring

/-! ### The lemma -/

lemma norm_ge_of_coercive {T0 : ι → ι → (V →L[ℂ] V)} {γ : ℝ}
    (hcoer : ∀ μ : L2 ι V, γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply T0 μ))) (μ : L2 ι V) :
    γ * ‖μ‖ ≤ ‖kerApply T0 μ‖ := by
  have h1 : γ * ‖μ‖ ^ 2 ≤ ‖μ‖ * ‖kerApply T0 μ‖ :=
    (hcoer μ).trans ((RCLike.re_le_norm _).trans (norm_inner_le_norm _ _))
  rcases (norm_nonneg μ).eq_or_lt with h | h
  · rw [← h]; simp
  · nlinarith

/-- `lem:kernel-inverse`. With `K` bounding `Σ_{c'} e^{-δd(c₋, c'₋)/4}` (the core's `4c₁(½, ½δ)`) and
`θ = min{θ₀, δ/2, γδ/(6κK)}`, the operator `T = T₀ + T₁` is invertible, and the solution of
`Tu = δ_{c'} w` satisfies `‖u(c)‖ ≤ (2/γ) e^{-θd(c₋, c'₋)} ‖w‖`, that is,
`‖T⁻¹[c, c']‖₂ ≤ (2/γ) e^{-θd(c₋, c'₋)}`. -/
theorem kernel_inverse {B : Type*} [PseudoMetricSpace B] (fe : ι → B)
    {δ κ γ θ0 K : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hγ : 0 < γ) (hθ0 : 0 < θ0) (hK0 : 0 < K)
    (hK : ∀ c, ∑ c', Real.exp (-(δ / 4) * dist (fe c) (fe c')) ≤ K)
    (T0 T1 : ι → ι → (V →L[ℂ] V))
    (ha : ∀ c c', ‖T0 c c'‖ ≤ κ * Real.exp (-δ * dist (fe c) (fe c')))
    (hcoer : ∀ μ : L2 ι V, γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply T0 μ)))
    (hc : ∀ y : B, ∀ θ, 0 ≤ θ → θ ≤ θ0 →
      OpBound (conjKer θ (fun c => dist (fe c) y) T1) (γ / 4)) :
    Function.Bijective (kerLin (T0 + T1)) ∧
    ∀ (c c' : ι) (u : L2 ι V) (w : V), kerApply (T0 + T1) u = single c' w →
      ‖u.ofLp c‖ ≤ 2 / γ * Real.exp (-(min θ0 (min (δ / 2) (γ * δ / (6 * κ * K)))) *
        dist (fe c) (fe c')) * ‖w‖ := by
  set θ := min θ0 (min (δ / 2) (γ * δ / (6 * κ * K))) with hθ
  have hθ1 : θ ≤ θ0 := min_le_left _ _
  have hθ2 : θ ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hθ3 : θ ≤ γ * δ / (6 * κ * K) := (min_le_right _ _).trans (min_le_right _ _)
  have hθpos : 0 ≤ θ := le_min hθ0.le (le_min (by positivity) (by positivity))
  -- the lower bound `‖T_{θ'} μ‖ ≥ (γ/2)‖μ‖` for `0 ≤ θ' ≤ θ`
  have key : ∀ y : B, ∀ θ', 0 ≤ θ' → θ' ≤ θ → ∀ μ : L2 ι V,
      γ / 2 * ‖μ‖ ≤ ‖kerApply (conjKer θ' (fun c => dist (fe c) y) (T0 + T1)) μ‖ := by
    intro y θ' h0 h1 μ
    set ρ : ι → ℝ := fun c => dist (fe c) y
    -- the conjugation changes `T₀` by at most `γ/4`
    set k : ι → ι → ℝ := fun c c' =>
      4 * κ * θ' / (Real.exp 1 * δ) * Real.exp (-(δ / 4) * dist (fe c) (fe c'))
    have hentry : ∀ c c', ‖(conjKer θ' ρ T0 - T0) c c'‖ ≤ k c c' := fun c c' => by
      have e : (conjKer θ' ρ T0 - T0) c c' =
          (((Real.exp (θ' * (ρ c - ρ c')) - 1 : ℝ)) : ℂ) • T0 c c' := by
        simp [conjKer, sub_smul]
      rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have hx : |θ' * (ρ c - ρ c')| ≤ θ' * dist (fe c) (fe c') := by
        rw [abs_mul, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_left (abs_dist_sub_le _ _ _) h0
      exact (mul_le_mul_of_nonneg_left (ha c c') (abs_nonneg _)).trans
        (entry_conj_sub_le hδ hκ.le h0 (h1.trans hθ2) dist_nonneg hx)
    have hsum : ∀ c, ∑ c', k c c' ≤ 4 * κ * θ' / (Real.exp 1 * δ) * K := fun c => by
      simp only [k]; rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hK c) (by positivity)
    have hsum' : ∀ c', ∑ c, k c c' ≤ 4 * κ * θ' / (Real.exp 1 * δ) * K := fun c' => by
      simp only [k]; rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun c _ => ?_).trans (hK c'))
        (by positivity)
      rw [dist_comm]
    have hsmall : 4 * κ * θ' / (Real.exp 1 * δ) * K ≤ γ / 4 := by
      have he : 8 / 3 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have hθ' : θ' ≤ γ * δ / (6 * κ * K) := h1.trans hθ3
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hθ'
      nlinarith [mul_pos hγ hδ]
    have hB : OpBound (conjKer θ' ρ T0 - T0) (γ / 4) := fun ν => by
      have := opBound_of_entry _ k hentry hsum hsum' ν
      rw [max_self] at this
      exact this.trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))
    have hC := hc y θ' h0 (h1.trans hθ1) μ
    have hA := norm_ge_of_coercive hcoer μ
    have hdecomp : kerApply (conjKer θ' ρ (T0 + T1)) μ =
        kerApply T0 μ + kerApply (conjKer θ' ρ T0 - T0) μ + kerApply (conjKer θ' ρ T1) μ := by
      rw [conjKer_add, kerApply_add, kerApply_sub]; abel
    rw [hdecomp]
    have t1 := norm_sub_le (kerApply T0 μ + kerApply (conjKer θ' ρ T0 - T0) μ +
      kerApply (conjKer θ' ρ T1) μ) (kerApply (conjKer θ' ρ T1) μ)
    have t2 := norm_sub_le (kerApply T0 μ + kerApply (conjKer θ' ρ T0 - T0) μ)
      (kerApply (conjKer θ' ρ T0 - T0) μ)
    rw [add_sub_cancel_right] at t1 t2
    linarith [hB μ]
  -- invertibility
  have hinj : Function.Injective (kerLin (T0 + T1)) := by
    rw [injective_iff_map_eq_zero]
    intro μ hμ
    by_cases hι : IsEmpty ι
    · exact Subsingleton.elim _ _
    obtain ⟨c0⟩ := not_isEmpty_iff.1 hι
    have := key (fe c0) 0 le_rfl hθpos μ
    rw [conjKer_zero] at this
    change γ / 2 * ‖μ‖ ≤ ‖kerLin (T0 + T1) μ‖ at this
    rw [hμ, norm_zero] at this
    exact norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg μ]) (norm_nonneg _))
  refine ⟨⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩, fun c c' u w hu => ?_⟩
  -- the decay of the entries of the inverse
  set ρ : ι → ℝ := fun c => dist (fe c) (fe c')
  have hρ : ρ c' = 0 := dist_self _
  have h1 := key (fe c') θ hθpos le_rfl (weightMul θ ρ u)
  rw [kerApply_conjKer, hu, weightMul_single hρ, norm_single] at h1
  have h2 : Real.exp (θ * ρ c) * ‖u.ofLp c‖ ≤ ‖weightMul θ ρ u‖ := by
    have := norm_ofLp_le (weightMul θ ρ u) c
    simp only [weightMul, WithLp.ofLp_toLp, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at this
    exact this
  have h3 : Real.exp (θ * ρ c) * ‖u.ofLp c‖ ≤ 2 / γ * ‖w‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hγ]; nlinarith
  calc ‖u.ofLp c‖ = Real.exp (-(θ * ρ c)) * (Real.exp (θ * ρ c) * ‖u.ofLp c‖) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-(θ * ρ c)) * (2 / γ * ‖w‖) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 2 / γ * Real.exp (-θ * dist (fe c) (fe c')) * ‖w‖ := by
        simp only [ρ, neg_mul]; ring

/-! ### The complexification step -/

lemma im_inner_eq_zero {W : Set V} (hW : ∀ w ∈ W, ∀ w' ∈ W, (inner ℂ w w').im = 0)
    {X Y : L2 ι V} (hX : ∀ c, X.ofLp c ∈ W) (hY : ∀ c, Y.ofLp c ∈ W) :
    (inner ℂ X Y).im = 0 := by
  rw [PiLp.inner_apply, Complex.im_sum]
  exact Finset.sum_eq_zero fun c _ => hW _ (hX c) _ (hY c)

/-- Hypothesis (b) of `lem:kernel-inverse` gives the coercivity on all of `L²(ι; V)`: if `W ⊂ V` is a
real subspace on which the inner product is real (`𝔤 ⊂ 𝔤^c`, `⟨X, Y⟩ = tr XY` for Hermitean `X`,
`Y`), `V = W + iW`, `T₀` maps `W`-valued functions to `W`-valued functions, and
`Re⟨μ, T₀μ⟩ ≥ γ‖μ‖²` for `W`-valued `μ`, then `Re⟨μ, T₀μ⟩ ≥ γ‖μ‖²` for all `μ`. (The core's symmetry
of the form is not needed for this.) -/
theorem coercive_of_real (W : Set V) (hW : ∀ w ∈ W, ∀ w' ∈ W, (inner ℂ w w').im = 0)
    (hdec : ∀ v : V, ∃ x ∈ W, ∃ y ∈ W, v = x + Complex.I • y)
    (T0 : ι → ι → (V →L[ℂ] V))
    (hT : ∀ μ : L2 ι V, (∀ c, μ.ofLp c ∈ W) → ∀ c, (kerApply T0 μ).ofLp c ∈ W)
    {γ : ℝ} (hpos : ∀ μ : L2 ι V, (∀ c, μ.ofLp c ∈ W) →
      γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply T0 μ)))
    (μ : L2 ι V) : γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply T0 μ)) := by
  choose x hx y hy hxy using hdec
  set X : L2 ι V := WithLp.toLp 2 fun c => x (μ.ofLp c)
  set Y : L2 ι V := WithLp.toLp 2 fun c => y (μ.ofLp c)
  have hXW : ∀ c, X.ofLp c ∈ W := fun c => hx _
  have hYW : ∀ c, Y.ofLp c ∈ W := fun c => hy _
  have hμ : μ = X + Complex.I • Y := by
    ext c; simp only [X, Y, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_toLp]
    exact hxy _
  have hTμ : kerApply T0 μ = kerApply T0 X + Complex.I • kerApply T0 Y := by
    have := (kerLin T0).map_add X (Complex.I • Y)
    rw [(kerLin T0).map_smul] at this
    rw [hμ]; exact this
  have i1 := im_inner_eq_zero hW hXW (hT Y hYW)
  have i2 := im_inner_eq_zero hW hYW (hT X hXW)
  have i3 := im_inner_eq_zero hW hXW hYW
  -- `Re⟨μ, T₀μ⟩ = Re⟨X, T₀X⟩ + Re⟨Y, T₀Y⟩`
  have hre : RCLike.re (inner ℂ μ (kerApply T0 μ)) =
      RCLike.re (inner ℂ X (kerApply T0 X)) + RCLike.re (inner ℂ Y (kerApply T0 Y)) := by
    rw [hTμ, hμ, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
      inner_smul_right, inner_smul_left, inner_smul_right]
    simp only [RCLike.re_to_complex, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, i1, i2]
    ring
  -- `‖μ‖² = ‖X‖² + ‖Y‖²`
  have hnorm : ‖μ‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
    rw [hμ, @norm_add_sq ℂ, inner_smul_right, norm_smul, Complex.norm_I, one_mul]
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.I_re, Complex.I_im, i3]
    ring
  rw [hre, hnorm, mul_add]
  exact add_le_add (hpos X hXW) (hpos Y hYW)

end CoreLean
