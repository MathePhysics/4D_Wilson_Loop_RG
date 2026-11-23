/-
`lem:heat-kernel` of BALABAN_CORE.tex (`5bbe1bc62521`): the identification of the core's `P_t = e^{-tΔ}`, defined by the
exponential series of the bounded operator `Δ = Σ_μ∂^*_μ∂_μ` on the bounded functions, with the kernel operator `heatOp`
of `HeatOperator.lean`. On the Banach space `ℤ⁴ →ᵇ V`, `-tΔ = Σ_μ2s(T_μ - 1)` with `s = t/ε²` and the commuting means
`T_μ = (τ_{e_μ} + τ_{-e_μ})/2`, so `e^{-tΔ} = ∏_μe^{-2s}e^{2sT_μ}`; `(T_μ^kf)(n) = Σ_m(2π)⁻¹c_k(m)f(n - me_μ)` with
`c_k(m) = ∫cos(mθ)cos^kθ dθ` (`cosPowInt_succ`), and `q_s(m) = Σ_k(2π)⁻¹e^{-2s}(2s)^k/k!·c_k(m)`
(`hasSum_heatKernel1_series`), so `e^{2s(T_μ - 1)}` is the convolution with `q_s` in the coordinate `μ`, and the four
convolutions compose to the convolution with `p_s(z) = ∏_μq_s(z_μ)`.
-/
import CoreLean.HeatOperator
import CoreLean.VanishingMoments

open NormedSpace BoundedContinuousFunction Balaban.LatticeGreen Real

noncomputable section

namespace CoreLean
namespace HeatExponential

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The bounded functions on `ℤ⁴`. -/
abbrev BF (V : Type*) [NormedAddCommGroup V] := (Fin 4 → ℤ) →ᵇ V

/-- The translation `(τ_af)(n) = f(n + a)`. -/
def tau (a : Fin 4 → ℤ) : BF V →L[ℝ] BF V :=
  compContinuousCLM V ℝ (⟨fun n => n + a, continuous_of_discreteTopology⟩ : C(Fin 4 → ℤ, Fin 4 → ℤ))

@[simp] lemma tau_apply (a : Fin 4 → ℤ) (f : BF V) (n : Fin 4 → ℤ) : tau a f n = f (n + a) := rfl

lemma tau_comm (a b : Fin 4 → ℤ) : Commute (tau (V := V) a) (tau b) := by
  refine ContinuousLinearMap.ext fun f => BoundedContinuousFunction.ext fun n => ?_
  simp only [ContinuousLinearMap.mul_apply, tau_apply]
  rw [add_right_comm]

/-- The mean `T_μ = (τ_{e_μ} + τ_{-e_μ})/2`. -/
def Tm (μ : Fin 4) : BF V →L[ℝ] BF V := (1 / 2 : ℝ) • (tau (e4 μ) + tau (-e4 μ))

lemma Tm_comm (μ ν : Fin 4) : Commute (Tm (V := V) μ) (Tm ν) := by
  unfold Tm
  refine ((Commute.add_left ?_ ?_).add_right (Commute.add_left ?_ ?_)).smul_left _ |>.smul_right _ <;>
    exact tau_comm _ _

lemma Tm_apply (μ : Fin 4) (g : BF V) (n : Fin 4 → ℤ) :
    Tm μ g n = (1 / 2 : ℝ) • (g (n + e4 μ) + g (n + -e4 μ)) := rfl

/-- `Δ = Σ_μ∂^*_μ∂_μ = Σ_με⁻²(2 - τ_{e_μ} - τ_{-e_μ})`. -/
def Lap (ε : ℝ) : BF V →L[ℝ] BF V := ∑ μ, (ε⁻¹ ^ 2) • ((2 : ℝ) • (1 : BF V →L[ℝ] BF V) - tau (e4 μ) - tau (-e4 μ))

/-- The core's `P_t = e^{-tΔ}`, by the exponential series in the Banach algebra of bounded operators. -/
def Pexp (ε t : ℝ) : BF V →L[ℝ] BF V := NormedSpace.exp (-t • Lap (V := V) ε)

/-! ### One direction -/

/-- `(T_μ^kf)(n) = Σ_m(2π)⁻¹c_k(m)f(n - me_μ)`. -/
lemma summable_coef_smul (a : ℤ → ℝ) (ha0 : ∀ m, 0 ≤ a m) (ha : Summable a) (g : ℤ → V) {M : ℝ}
    (hg : ∀ m, ‖g m‖ ≤ M) : Summable fun m : ℤ => a m • g m := by
  refine Summable.of_norm_bounded (g := fun m => a m * M) (ha.mul_right _) fun m => ?_
  rw [norm_smul, Real.norm_of_nonneg (ha0 m)]
  exact mul_le_mul_of_nonneg_left (hg m) (ha0 m)

lemma summable_cos_shift (k : ℕ) (j : ℤ) : Summable fun m : ℤ => (2 * π)⁻¹ * cosPowInt k (m + j) :=
  ((summable_cosPowInt k).comp_injective (add_left_injective j)).mul_left _

lemma Tpow_apply (μ : Fin 4) : ∀ (k : ℕ) (f : BF V) (n : Fin 4 → ℤ),
    (((Tm (V := V) μ) ^ k) f) n = ∑' m : ℤ, ((2 * π)⁻¹ * cosPowInt k m) • f (n - m • e4 μ)
  | 0, f, n => by
    rw [pow_zero, ContinuousLinearMap.one_apply, tsum_eq_single 0 (fun m hm => by
      rw [cosPowInt_zero, if_neg hm, mul_zero, zero_smul])]
    rw [cosPowInt_zero, if_pos rfl, zero_smul, sub_zero]
    field_simp
    rw [one_smul]
  | k + 1, f, n => by
    rw [pow_succ', ContinuousLinearMap.mul_apply, Tm_apply, Tpow_apply μ k f, Tpow_apply μ k f]
    -- reindex `m ↦ m + 1` and `m ↦ m - 1`
    have r1 : ∑' m : ℤ, ((2 * π)⁻¹ * cosPowInt k m) • f (n + e4 μ - m • e4 μ) =
        ∑' m : ℤ, ((2 * π)⁻¹ * cosPowInt k (m + 1)) • f (n - m • e4 μ) := by
      rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
      refine tsum_congr fun m => ?_
      simp only [Equiv.coe_addRight]
      congr 2
      rw [add_smul, one_smul]; abel
    have r2 : ∑' m : ℤ, ((2 * π)⁻¹ * cosPowInt k m) • f (n + -e4 μ - m • e4 μ) =
        ∑' m : ℤ, ((2 * π)⁻¹ * cosPowInt k (m + -1)) • f (n - m • e4 μ) := by
      rw [← (Equiv.addRight (-1 : ℤ)).tsum_eq]
      refine tsum_congr fun m => ?_
      simp only [Equiv.coe_addRight]
      congr 2
      rw [add_smul, neg_smul, one_smul]; abel
    have t1 := summable_coef_smul _ (fun m => by have := cosPowInt_nonneg k (m + 1); positivity)
      (summable_cos_shift k 1) (fun m => f (n - m • e4 μ)) (fun m => f.norm_coe_le_norm _)
    have t2 := summable_coef_smul _ (fun m => by have := cosPowInt_nonneg k (m + -1); positivity)
      (summable_cos_shift k (-1)) (fun m => f (n - m • e4 μ)) (fun m => f.norm_coe_le_norm _)
    rw [r1, r2, ← t1.tsum_add t2, ← tsum_const_smul'']
    refine tsum_congr fun m => ?_
    rw [← add_smul, smul_smul, cosPowInt_succ, ← sub_eq_add_neg]
    congr 1
    ring

/-- The convolution with `q_s` in the coordinate `μ`. -/
def conv1 (μ : Fin 4) (s : ℝ) (g : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : V :=
  ∑' m : ℤ, heatKernel1 s m • g (n - m • e4 μ)

/-- The Poisson mixture of the kernels of `T^k` is the kernel `q_s`:
`e^{-2s}Σ_k(2s)^k/k!Σ_m(2π)⁻¹c_k(m)g(m) = Σ_mq_s(m)g(m)` for bounded `g`. -/
lemma series_conv {s : ℝ} (hs : 0 ≤ s) (g : ℤ → V) {M : ℝ} (hg : ∀ m, ‖g m‖ ≤ M) :
    Real.exp (-(2 * s)) • ∑' k : ℕ, ((k.factorial : ℝ))⁻¹ • ((2 * s) ^ k •
      ∑' m : ℤ, ((2 * π)⁻¹ * cosPowInt k m) • g m) = ∑' m : ℤ, heatKernel1 s m • g m := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg 0)
  set F : ℕ × ℤ → V := fun p => (heatWeight s p.1 * cosPowInt p.1 p.2) • g p.2 with hF
  have hFn : ∀ p, ‖F p‖ ≤ heatWeight s p.1 * cosPowInt p.1 p.2 * M := fun p => by
    rw [hF, norm_smul, Real.norm_of_nonneg (mul_nonneg (heatWeight_nonneg hs _) (cosPowInt_nonneg _ _))]
    exact mul_le_mul_of_nonneg_left (hg _) (mul_nonneg (heatWeight_nonneg hs _) (cosPowInt_nonneg _ _))
  have h0 : ∀ p : ℕ × ℤ, 0 ≤ heatWeight s p.1 * cosPowInt p.1 p.2 * M := fun p =>
    mul_nonneg (mul_nonneg (heatWeight_nonneg hs _) (cosPowInt_nonneg _ _)) hM
  have hG : Summable fun p : ℕ × ℤ => heatWeight s p.1 * cosPowInt p.1 p.2 * M := by
    rw [summable_prod_of_nonneg (fun p => h0 p)]
    refine ⟨fun k => ?_, ?_⟩
    · show Summable fun y : ℤ => heatWeight s k * cosPowInt k y * M
      exact ((summable_cosPowInt k).mul_left (heatWeight s k)).mul_right M
    · have e : ∀ k : ℕ, ∑' y : ℤ, heatWeight s k * cosPowInt k y * M = heatWeight s k * (2 * π * M) := fun k => by
        rw [tsum_mul_right, tsum_mul_left, tsum_cosPowInt]; ring
      show Summable fun k : ℕ => ∑' y : ℤ, heatWeight s k * cosPowInt k y * M
      simp only [e]
      exact (summable_heatWeight s).mul_right _
  have hFs : Summable F := Summable.of_norm_bounded (g := fun p : ℕ × ℤ => heatWeight s p.1 * cosPowInt p.1 p.2 * M)
    hG hFn
  have e1 : ∀ k : ℕ, Real.exp (-(2 * s)) • (((k.factorial : ℝ))⁻¹ • ((2 * s) ^ k •
      ∑' m : ℤ, ((2 * π)⁻¹ * cosPowInt k m) • g m)) = ∑' m : ℤ, F (k, m) := by
    intro k
    rw [← tsum_const_smul'', ← tsum_const_smul'', ← tsum_const_smul'']
    refine tsum_congr fun m => ?_
    simp only [hF, heatWeight, smul_smul]
    congr 1
    ring
  rw [← tsum_const_smul'']
  simp only [e1]
  rw [← Summable.tsum_comm (f := fun (k : ℕ) (m : ℤ) => F (k, m)) hFs]
  refine tsum_congr fun m => ?_
  have hq : HasSum (fun k => heatWeight s k * cosPowInt k m) (heatKernel1 s m) := hasSum_heatKernel1_series hs m
  rw [hF]
  simp only
  rw [hq.summable.tsum_smul_const, hq.tsum_eq]

/-- **`e^{2s(T_μ - 1)}` is the convolution with `q_s`** in the coordinate `μ`. -/
lemma exp_X_apply {s : ℝ} (hs : 0 ≤ s) (μ : Fin 4) (f : BF V) (n : Fin 4 → ℤ) :
    ((NormedSpace.exp ((2 * s) • (Tm (V := V) μ - 1)) : BF V →L[ℝ] BF V) f) n = conv1 μ s f n := by
  -- `e^{2s(T - 1)} = e^{-2s}e^{2sT}`
  have hsplit : (2 * s) • (Tm (V := V) μ - 1) = (2 * s) • Tm μ + algebraMap ℝ (BF V →L[ℝ] BF V) (-(2 * s)) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_sub, neg_smul, sub_eq_add_neg]
  have hc : Commute ((2 * s) • Tm (V := V) μ) (algebraMap ℝ (BF V →L[ℝ] BF V) (-(2 * s))) :=
    Algebra.commutes _ _ |>.symm
  have hexp : (NormedSpace.exp ((2 * s) • Tm (V := V) μ + algebraMap ℝ (BF V →L[ℝ] BF V) (-(2 * s))) :
      BF V →L[ℝ] BF V) = NormedSpace.exp ((2 * s) • Tm (V := V) μ) *
        NormedSpace.exp (algebraMap ℝ (BF V →L[ℝ] BF V) (-(2 * s))) := by
    letI : NormedAlgebra ℚ (BF V →L[ℝ] BF V) := NormedAlgebra.restrictScalars ℚ ℝ _
    exact exp_add_of_commute hc
  rw [hsplit, hexp, ← algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, mul_one, ContinuousLinearMap.smul_apply, BoundedContinuousFunction.coe_smul, Pi.smul_apply]
  -- the exponential series of `2sT`, evaluated at `f` and `n`
  have hser := (exp_series_hasSum_exp' (𝕂 := ℝ) ((2 * s) • Tm (V := V) μ)).mapL
    ((BoundedContinuousFunction.evalCLM ℝ n).comp (ContinuousLinearMap.apply ℝ (BF V) f))
  simp only [ContinuousLinearMap.coe_comp', Function.comp, ContinuousLinearMap.apply_apply,
    BoundedContinuousFunction.evalCLM_apply, ContinuousLinearMap.smul_apply, BoundedContinuousFunction.coe_smul,
    Pi.smul_apply, smul_pow, Tpow_apply] at hser
  rw [← hser.tsum_eq]
  exact series_conv hs (fun m => f (n - m • e4 μ)) (fun m => f.norm_coe_le_norm _)

lemma coe_exp_X {s : ℝ} (hs : 0 ≤ s) (μ : Fin 4) (g : BF V) :
    ⇑((NormedSpace.exp ((2 * s) • (Tm (V := V) μ - 1)) : BF V →L[ℝ] BF V) g) = conv1 μ s ⇑g :=
  funext (exp_X_apply hs μ g)

/-! ### The four directions -/

/-- `-tΔ = Σ_μ2s(T_μ - 1)`, `s = t/ε²`. -/
lemma neg_smul_Lap (ε t : ℝ) :
    -t • Lap (V := V) ε = ∑ μ, (2 * (t / ε ^ 2)) • (Tm (V := V) μ - 1) := by
  unfold Lap Tm
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [smul_sub, smul_add, smul_smul]
  rw [show -t * (ε⁻¹ ^ 2 * 2) = -(2 * (t / ε ^ 2)) by ring,
    show -t * ε⁻¹ ^ 2 = -(2 * (t / ε ^ 2) * (1 / 2)) by ring]
  module

/-- `Σ_zΠ_ik(z_i)G(z) = Σ_ak(a)Σ_{z'}Π_ik(z'_i)G(a, z')`: one coordinate split off. -/
lemma tsum_split_first (d : ℕ) {k : ℤ → ℝ} (hk0 : ∀ a, 0 ≤ k a) (hk : Summable k)
    (G : (Fin (d + 1) → ℤ) → V) {M : ℝ} (hG : ∀ z, ‖G z‖ ≤ M) :
    ∑' z : Fin (d + 1) → ℤ, (∏ i, k (z i)) • G z =
      ∑' a : ℤ, k a • ∑' z' : Fin d → ℤ, (∏ i, k (z' i)) • G (Fin.cons a z') := by
  have hP := VanishingMoments.summable_pi_prod (d + 1) (fun _ => k) (fun _ t => hk0 t) (fun _ => hk)
  have hF : Summable fun z : Fin (d + 1) → ℤ => (∏ i, k (z i)) • G z := by
    refine Summable.of_norm_bounded (g := fun z => (∏ i, k (z i)) * M) (hP.mul_right M) fun z => ?_
    rw [norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => hk0 _)]
    exact mul_le_mul_of_nonneg_left (hG z) (Finset.prod_nonneg fun i _ => hk0 _)
  set e := Fin.consEquiv (fun _ : Fin (d + 1) => ℤ) with he
  rw [← e.tsum_eq]
  have hFe : Summable fun p : ℤ × (Fin d → ℤ) => (∏ i, k (e p i)) • G (e p) := e.summable_iff.2 hF
  rw [hFe.tsum_prod' fun a => hFe.prod_factor a]
  refine tsum_congr fun a => ?_
  rw [← tsum_const_smul'']
  refine tsum_congr fun z' => ?_
  simp only [he, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_smul]

lemma heatKernel1_summable' {s : ℝ} (hs : 0 ≤ s) : Summable (heatKernel1 s) := heatKernel1_summable hs

set_option maxHeartbeats 2000000 in
/-- **The four convolutions compose to the convolution with `p_s(z) = ∏_μq_s(z_μ)`.** -/
lemma conv4 {s : ℝ} (hs : 0 ≤ s) (h : (Fin 4 → ℤ) → V) {M : ℝ} (hM : ∀ z, ‖h z‖ ≤ M) (n : Fin 4 → ℤ) :
    conv1 0 s (conv1 1 s (conv1 2 s (conv1 3 s h))) n = ∑' z, heatKernel 4 s z • h (n - z) := by
  have hk0 := heatKernel1_nonneg hs
  have hk := heatKernel1_summable' hs
  set q := heatKernel1 s with hq
  have s3 : ∑' z : Fin 4 → ℤ, (∏ i, q (z i)) • h (n - z) =
      ∑' a : ℤ, q a • ∑' z : Fin 3 → ℤ, (∏ i, q (z i)) • h (n - Fin.cons (α := fun _ => ℤ) a z) :=
    tsum_split_first 3 hk0 hk (fun z => h (n - z)) (fun z => hM _)
  have s2 : ∀ a : ℤ, ∑' z : Fin 3 → ℤ, (∏ i, q (z i)) • h (n - Fin.cons (α := fun _ => ℤ) a z) =
      ∑' b : ℤ, q b • ∑' z : Fin 2 → ℤ, (∏ i, q (z i)) • h (n - Fin.cons (α := fun _ => ℤ) a (Fin.cons (α := fun _ => ℤ) b z)) := fun a =>
    tsum_split_first 2 hk0 hk (fun z => h (n - Fin.cons (α := fun _ => ℤ) a z)) (fun z => hM _)
  have s1 : ∀ a b : ℤ, ∑' z : Fin 2 → ℤ, (∏ i, q (z i)) • h (n - Fin.cons (α := fun _ => ℤ) a (Fin.cons (α := fun _ => ℤ) b z)) =
      ∑' c : ℤ, q c • ∑' z : Fin 1 → ℤ, (∏ i, q (z i)) • h (n - Fin.cons (α := fun _ => ℤ) a (Fin.cons (α := fun _ => ℤ) b (Fin.cons (α := fun _ => ℤ) c z)))
    := fun a b => tsum_split_first 1 hk0 hk (fun z => h (n - Fin.cons (α := fun _ => ℤ) a (Fin.cons (α := fun _ => ℤ) b z))) (fun z => hM _)
  have s0 : ∀ a b c : ℤ, ∑' z : Fin 1 → ℤ, (∏ i, q (z i)) • h (n - Fin.cons (α := fun _ => ℤ) a (Fin.cons (α := fun _ => ℤ) b (Fin.cons (α := fun _ => ℤ) c z))) =
      ∑' e : ℤ, q e • ∑' z : Fin 0 → ℤ, (∏ i, q (z i)) •
        h (n - Fin.cons (α := fun _ => ℤ) a (Fin.cons (α := fun _ => ℤ) b (Fin.cons (α := fun _ => ℤ) c (Fin.cons (α := fun _ => ℤ) e z)))) := fun a b c =>
    tsum_split_first 0 hk0 hk (fun z => h (n - Fin.cons (α := fun _ => ℤ) a (Fin.cons (α := fun _ => ℤ) b (Fin.cons (α := fun _ => ℤ) c z)))) (fun z => hM _)
  have hfin : ∀ a b c e : ℤ, ∑' z : Fin 0 → ℤ, (∏ i, q (z i)) •
      h (n - Fin.cons (α := fun _ => ℤ) a (Fin.cons (α := fun _ => ℤ) b (Fin.cons (α := fun _ => ℤ) c (Fin.cons (α := fun _ => ℤ) e z)))) =
        h (n - a • e4 0 - b • e4 1 - c • e4 2 - e • e4 3) := by
    intro a b c e
    rw [tsum_fintype, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    congr 1
    funext i
    fin_cases i <;> simp [e4, Pi.single_apply, sub_sub] <;> rfl
  unfold heatKernel
  rw [s3]
  refine tsum_congr fun a => congrArg (q a • ·) ?_
  rw [s2 a]
  refine tsum_congr fun b => congrArg (q b • ·) ?_
  rw [s1 a b]
  refine tsum_congr fun c => congrArg (q c • ·) ?_
  rw [s0 a b c]
  refine tsum_congr fun e => congrArg (q e • ·) ?_
  rw [hfin]

/-- **`lem:heat-kernel`, the identification**: the core's `P_t = e^{-tΔ}`, the exponential series of `-tΔ` in the
Banach algebra of bounded operators on `ℤ⁴ →ᵇ V`, is the kernel operator `heatOp`:
`(e^{-tΔ}f)(n) = Σ_zp_{t/ε²}(z)f(n - z)` for `t ≥ 0`. -/
theorem Pexp_eq_heatOp (ε : ℝ) {t : ℝ} (ht : 0 ≤ t) (f : BF V) (n : Fin 4 → ℤ) :
    Pexp ε t f n = heatOp ε t f n := by
  set s := t / ε ^ 2 with hs_def
  have hs : 0 ≤ s := div_nonneg ht (sq_nonneg _)
  set Y : Fin 4 → (BF V →L[ℝ] BF V) := fun μ => (2 * s) • (Tm (V := V) μ - 1) with hY
  have hcomm : ∀ μ ν, Commute (Y μ) (Y ν) := fun μ ν =>
    (((Tm_comm μ ν).sub_left (Commute.one_left _)).sub_right
      ((Commute.one_right _).sub_left (Commute.one_left _))).smul_left _ |>.smul_right _
  have hexp : (NormedSpace.exp (Y 0 + Y 1 + Y 2 + Y 3) : BF V →L[ℝ] BF V) =
      NormedSpace.exp (Y 0) * NormedSpace.exp (Y 1) * NormedSpace.exp (Y 2) * NormedSpace.exp (Y 3) := by
    letI : NormedAlgebra ℚ (BF V →L[ℝ] BF V) := NormedAlgebra.restrictScalars ℚ ℝ _
    rw [exp_add_of_commute (((hcomm 0 3).add_left (hcomm 1 3)).add_left (hcomm 2 3)),
      exp_add_of_commute ((hcomm 0 2).add_left (hcomm 1 2)), exp_add_of_commute (hcomm 0 1)]
  unfold Pexp
  rw [neg_smul_Lap, Fin.sum_univ_four]
  change (NormedSpace.exp (Y 0 + Y 1 + Y 2 + Y 3) : BF V →L[ℝ] BF V) f n = _
  rw [hexp]
  simp only [ContinuousLinearMap.mul_apply, hY, coe_exp_X hs]
  rw [conv4 hs (⇑f) (fun z => f.norm_coe_le_norm z)]
  rfl

end HeatExponential
end CoreLean

end
