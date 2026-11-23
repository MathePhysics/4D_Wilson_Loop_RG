import Mathlib

/-! **Moderate families**: functions `f(x, p)` of a field `x` and a parameter `p`, `C^∞` jointly, whose iterated
derivatives of order `n` are bounded by `C_n e^{c_n ‖x‖}` for `p` in a closed ball (Moderate). They are closed under
constants, sums, translations of the field, freezing the parameter at `0`, continuous linear and bilinear maps
(Leibniz; norms squared, products), assembly of `PiLp 2` values from coordinates, and contain continuous linear maps
of `(x, p)`, linear maps of `x` (finite dimension), the parameter coordinates and smooth functions of `p` alone. For an operator `Q`, `‖e^Q‖ ≤ e^{‖Q‖}` (norm_exp_clm_le)
and `∂_τ^i e^{τ Q} = e^{τ Q} Q^i`; so `e^{τ Q}` is moderate when the phase `τ` is moderate and of linear growth
(Moderate.exp_smul_clm: the gauge transports `U(t + e' s(A'))`), and the derivatives of `e^F` for a moderate scalar
`F` are bounded by `C e^{c ‖x‖} e^F` (Moderate.norm_iteratedFDeriv_exp_le, Faà di Bruno). Used to dominate the
parameter derivatives of the integrand of the bracket of I.(3.35) (ExpDomination). -/

open Metric Set
open scoped ContDiff Nat

namespace GaussianBlockSpin

section Moderate

variable {X P E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A **moderate family** on the parameter ball of radius `r`: `f(x, p)` is `C^∞` jointly in the field `x` and the
parameter `p`, and for every `n` its iterated derivatives of order `≤ n` are bounded by `C e^{c ‖x‖}` for
`‖p‖ ≤ r`, with `C, c ≥ 0`. -/
def Moderate (r : ℝ) (f : X × P → E) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ i ≤ n, ∀ x : X, ∀ p ∈ closedBall (0 : P) r,
    ‖iteratedFDeriv ℝ i f (x, p)‖ ≤ C * Real.exp (c * ‖x‖)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma contDiff_of_infty {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Y → E} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) : ContDiff ℝ n f :=
  hf.of_le (by exact_mod_cast le_top)

omit [NormedSpace ℝ X] in
lemma exp_mul_norm_mono {c c' : ℝ} (h : c ≤ c') (x : X) : Real.exp (c * ‖x‖) ≤ Real.exp (c' * ‖x‖) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (norm_nonneg x))

lemma moderate_const (r : ℝ) (v : E) : Moderate r (fun _ : X × P => v) := by
  refine ⟨contDiff_const, fun n => ⟨‖v‖, 0, norm_nonneg v, le_rfl, fun i _ x p _ => ?_⟩⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [norm_iteratedFDeriv_zero]
    simp
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simp only [Pi.zero_apply, norm_zero, zero_mul, Real.exp_zero, mul_one]
    exact norm_nonneg v

lemma Moderate.add {r : ℝ} {f g : X × P → E} (hf : Moderate r f) (hg : Moderate r g) :
    Moderate r (fun y => f y + g y) := by
  show Moderate r (f + g)
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := hf.2 n
  obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := hg.2 n
  refine ⟨C₁ + C₂, max c₁ c₂, by positivity, le_max_of_le_left hc₁, fun i hi x p hp => ?_⟩
  have e₁ := mul_le_mul_of_nonneg_left (exp_mul_norm_mono (le_max_left c₁ c₂) x) hC₁
  have e₂ := mul_le_mul_of_nonneg_left (exp_mul_norm_mono (le_max_right c₁ c₂) x) hC₂
  rw [iteratedFDeriv_add_apply ((contDiff_of_infty hf.1 i).contDiffAt) ((contDiff_of_infty hg.1 i).contDiffAt)]
  calc _ ≤ ‖iteratedFDeriv ℝ i f (x, p)‖ + ‖iteratedFDeriv ℝ i g (x, p)‖ := norm_add_le _ _
    _ ≤ C₁ * Real.exp (c₁ * ‖x‖) + C₂ * Real.exp (c₂ * ‖x‖) := add_le_add (h₁ i hi x p hp) (h₂ i hi x p hp)
    _ ≤ (C₁ + C₂) * Real.exp (max c₁ c₂ * ‖x‖) := by linarith

/-- Composition with a continuous linear map on the left. -/
lemma Moderate.clm {r : ℝ} {f : X × P → E} (hf : Moderate r f) (L : E →L[ℝ] F) : Moderate r (fun y => L (f y)) := by
  refine ⟨L.contDiff.comp hf.1, fun n => ?_⟩
  obtain ⟨C, c, hC, hc, h⟩ := hf.2 n
  refine ⟨‖L‖ * C, c, by positivity, hc, fun i hi x p hp => ?_⟩
  have := L.norm_iteratedFDeriv_comp_left (x := (x, p)) (contDiff_of_infty hf.1 i).contDiffAt (le_refl (i : ℕ∞ω))
  calc ‖iteratedFDeriv ℝ i (fun y => L (f y)) (x, p)‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ i f (x, p)‖ := this
    _ ≤ ‖L‖ * (C * Real.exp (c * ‖x‖)) := mul_le_mul_of_nonneg_left (h i hi x p hp) (norm_nonneg L)
    _ = ‖L‖ * C * Real.exp (c * ‖x‖) := by ring

lemma Moderate.neg {r : ℝ} {f : X × P → E} (hf : Moderate r f) : Moderate r (fun y => -f y) := by
  have := hf.clm (-ContinuousLinearMap.id ℝ E)
  simpa using this

lemma Moderate.sub {r : ℝ} {f g : X × P → E} (hf : Moderate r f) (hg : Moderate r g) :
    Moderate r (fun y => f y - g y) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

lemma Moderate.const_smul {r : ℝ} {f : X × P → E} (hf : Moderate r f) (a : ℝ) : Moderate r (fun y => a • f y) := by
  have := hf.clm (a • ContinuousLinearMap.id ℝ E)
  simpa using this

lemma Moderate.sum {r : ℝ} {ι : Type*} (s : Finset ι) {f : ι → X × P → E} (hf : ∀ i ∈ s, Moderate r (f i)) :
    Moderate r (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using moderate_const (X := X) (P := P) r (0 : E)
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have := h1.add h2
    simpa [Finset.sum_insert ha] using this

/-- Translating the field: `(y, p) ↦ f(x₀ + y, p)` is moderate (with `C e^{c ‖x₀‖}` in place of `C`). -/
lemma Moderate.comp_add_left {r : ℝ} {f : X × P → E} (hf : Moderate r f) (x₀ : X) :
    Moderate r (fun y : X × P => f ((x₀, 0) + y)) := by
  refine ⟨hf.1.comp (contDiff_const.add contDiff_id), fun n => ?_⟩
  obtain ⟨C, c, hC, hc, h⟩ := hf.2 n
  refine ⟨C * Real.exp (c * ‖x₀‖), c, by positivity, hc, fun i hi x p hp => ?_⟩
  rw [iteratedFDeriv_comp_add_left]
  have hsum : ((x₀, (0 : P)) + (x, p)) = (x₀ + x, p) := by simp
  rw [hsum]
  refine (h i hi (x₀ + x) p hp).trans ?_
  have hle : Real.exp (c * ‖x₀ + x‖) ≤ Real.exp (c * ‖x₀‖) * Real.exp (c * ‖x‖) := by
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_add_le _ _) hc)
  calc C * Real.exp (c * ‖x₀ + x‖) ≤ C * (Real.exp (c * ‖x₀‖) * Real.exp (c * ‖x‖)) :=
        mul_le_mul_of_nonneg_left hle hC
    _ = C * Real.exp (c * ‖x₀‖) * Real.exp (c * ‖x‖) := by ring

/-- **Leibniz**: a bilinear map of two moderate families is moderate. -/
lemma Moderate.bilinear {r : ℝ} {f : X × P → E} {g : X × P → F} (hf : Moderate r f) (hg : Moderate r g)
    (B : E →L[ℝ] F →L[ℝ] G) : Moderate r (fun y => B (f y) (g y)) := by
  refine ⟨B.isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1), fun n => ?_⟩
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := hf.2 n
  obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := hg.2 n
  refine ⟨‖B‖ * 2 ^ n * (C₁ * C₂), c₁ + c₂, by positivity, by positivity, fun i hi x p hp => ?_⟩
  have hB := B.norm_iteratedFDeriv_le_of_bilinear (contDiff_of_infty hf.1 i) (contDiff_of_infty hg.1 i) (x, p)
    (le_refl (i : ℕ∞ω))
  have hterm : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j f (x, p)‖ *
      ‖iteratedFDeriv ℝ (i - j) g (x, p)‖ ≤ (i.choose j : ℝ) * ((C₁ * C₂) * Real.exp ((c₁ + c₂) * ‖x‖)) := by
    intro j hj
    have hj' : j ≤ n := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
    have a1 := h₁ j hj' x p hp
    have a2 := h₂ (i - j) (le_trans (Nat.sub_le i j) hi) x p hp
    have hexp : Real.exp ((c₁ + c₂) * ‖x‖) = Real.exp (c₁ * ‖x‖) * Real.exp (c₂ * ‖x‖) := by
      rw [← Real.exp_add]; ring_nf
    rw [mul_assoc, hexp]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖iteratedFDeriv ℝ j f (x, p)‖ * ‖iteratedFDeriv ℝ (i - j) g (x, p)‖
        ≤ (C₁ * Real.exp (c₁ * ‖x‖)) * (C₂ * Real.exp (c₂ * ‖x‖)) :=
          mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * (Real.exp (c₁ * ‖x‖) * Real.exp (c₂ * ‖x‖)) := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose] at hsum
  have h2 : (2 : ℝ) ^ i ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hi
  calc ‖iteratedFDeriv ℝ i (fun y => B (f y) (g y)) (x, p)‖
      ≤ ‖B‖ * ((2 ^ i : ℕ) * ((C₁ * C₂) * Real.exp ((c₁ + c₂) * ‖x‖))) :=
        hB.trans (mul_le_mul_of_nonneg_left hsum (norm_nonneg B))
    _ ≤ ‖B‖ * (2 ^ n * ((C₁ * C₂) * Real.exp ((c₁ + c₂) * ‖x‖))) := by
        push_cast
        gcongr
    _ = ‖B‖ * 2 ^ n * (C₁ * C₂) * Real.exp ((c₁ + c₂) * ‖x‖) := by ring

/-- Continuous linear maps of `(x, p)` are moderate. -/
lemma moderate_clm (r : ℝ) (L : X × P →L[ℝ] E) : Moderate r (fun y => L y) := by
  refine ⟨L.contDiff, fun n => ⟨‖L‖ * (1 + |r|), 1, by positivity, zero_le_one, fun i _ x p hp => ?_⟩⟩
  have hx1 : ‖x‖ + 1 ≤ Real.exp (1 * ‖x‖) := by rw [one_mul]; exact Real.add_one_le_exp _
  have he1 : 1 ≤ Real.exp (1 * ‖x‖) := Real.one_le_exp (by positivity)
  have hbig : 1 ≤ (1 + |r|) * Real.exp (1 * ‖x‖) := by nlinarith [abs_nonneg r]
  have hL0 := norm_nonneg L
  match i with
  | 0 =>
    rw [norm_iteratedFDeriv_zero]
    have hp' : ‖p‖ ≤ r := mem_closedBall_zero_iff.mp hp
    have hxp : ‖(x, p)‖ ≤ ‖x‖ + |r| := by
      rw [Prod.norm_def]
      exact max_le (by linarith [abs_nonneg r]) (by linarith [norm_nonneg x, le_abs_self r])
    calc ‖L (x, p)‖ ≤ ‖L‖ * ‖(x, p)‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖x‖ + |r|) := mul_le_mul_of_nonneg_left hxp hL0
      _ ≤ ‖L‖ * ((1 + |r|) * Real.exp (1 * ‖x‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hL0
          nlinarith [abs_nonneg r]
      _ = ‖L‖ * (1 + |r|) * Real.exp (1 * ‖x‖) := by ring
  | 1 =>
    rw [norm_iteratedFDeriv_one, L.fderiv]
    calc ‖L‖ = ‖L‖ * 1 := (mul_one _).symm
      _ ≤ ‖L‖ * ((1 + |r|) * Real.exp (1 * ‖x‖)) := mul_le_mul_of_nonneg_left hbig hL0
      _ = ‖L‖ * (1 + |r|) * Real.exp (1 * ‖x‖) := by ring
  | j + 2 =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hconst : fderiv ℝ (fun y => L y) = fun _ => L := funext fun y => L.fderiv
    rw [hconst, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    simp only [Pi.zero_apply, norm_zero]
    positivity

/-- Smooth functions of the parameter alone are moderate (bounded derivatives on the compact ball). -/
lemma moderate_of_param [ProperSpace P] (r : ℝ) {g : P → E} (hg : ContDiff ℝ ∞ g) :
    Moderate r (fun y : X × P => g y.2) := by
  have hsnd : ContDiff ℝ ∞ (fun y : X × P => g y.2) := hg.comp contDiff_snd
  refine ⟨hsnd, fun n => ?_⟩
  have hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ closedBall (0 : P) r, ‖iteratedFDeriv ℝ i g p‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : P) r).exists_bound_of_continuousOn
      ((contDiff_of_infty hg i).continuous_iteratedFDeriv'.continuousOn)
    exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩
  choose Cb hCb0 hCb using hb
  refine ⟨∑ i ∈ Finset.range (n + 1), Cb i, 0, Finset.sum_nonneg fun i _ => hCb0 i, le_rfl, fun i hi x p hp => ?_⟩
  have hcomp : (fun y : X × P => g y.2) = g ∘ (ContinuousLinearMap.snd ℝ X P) := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ (contDiff_of_infty hg i) _ le_rfl]
  simp only [zero_mul, Real.exp_zero, mul_one]
  calc ‖(iteratedFDeriv ℝ i g ((ContinuousLinearMap.snd ℝ X P) (x, p))).compContinuousLinearMap
        fun _ => ContinuousLinearMap.snd ℝ X P‖
      ≤ ‖iteratedFDeriv ℝ i g p‖ * ∏ _ : Fin i, ‖ContinuousLinearMap.snd ℝ X P‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ i g p‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ X P)
    _ ≤ Cb i := by rw [mul_one]; exact hCb i p hp
    _ ≤ ∑ i ∈ Finset.range (n + 1), Cb i :=
        Finset.single_le_sum (fun j _ => hCb0 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-- A family with values in `PiLp 2 β` is moderate when its coordinates are. -/
lemma moderate_toLp_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
    [∀ i, NormedSpace ℝ (β i)] {r : ℝ} {g : ∀ i, X × P → β i} (hg : ∀ i, Moderate r (g i)) :
    Moderate r (fun y => WithLp.toLp 2 (fun i => g i y)) := by
  have hsum : ∀ y, WithLp.toLp 2 (fun i => g i y) =
      ∑ i, (PiLp.continuousLinearEquiv 2 ℝ β).symm (ContinuousLinearMap.single ℝ β i (g i y)) := by
    intro y
    rw [← map_sum]
    congr 1
    funext j
    simp [Finset.sum_apply, ContinuousLinearMap.single_apply]
  simp_rw [hsum]
  exact Moderate.sum _ fun i _ => ((hg i).clm (ContinuousLinearMap.single ℝ β i)).clm
    ((PiLp.continuousLinearEquiv 2 ℝ β).symm : (∀ i, β i) →L[ℝ] PiLp 2 β)

/-- Freezing the parameter at `0` (`r ≥ 0`). -/
lemma Moderate.at_zero {r : ℝ} (hr : 0 ≤ r) {f : X × P → E} (hf : Moderate r f) :
    Moderate r (fun y : X × P => f (y.1, 0)) := by
  let M : X × P →L[ℝ] X × P := (ContinuousLinearMap.fst ℝ X P).prod 0
  have hM : ‖M‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    simp only [M, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', zero_apply, one_mul,
      Prod.norm_def, norm_zero]
    exact max_le (le_max_left _ _) (le_trans (norm_nonneg _) (le_max_right _ _))
  have hfun : (fun y => f (y.1, 0)) = f ∘ M := rfl
  refine ⟨hf.1.comp M.contDiff, fun n => ?_⟩
  obtain ⟨C, c, hC, hc, h⟩ := hf.2 n
  refine ⟨C, c, hC, hc, fun i hi x p _ => ?_⟩
  rw [hfun, M.iteratedFDeriv_comp_right (contDiff_of_infty hf.1 i) _ le_rfl]
  have hMx : M (x, p) = (x, 0) := rfl
  rw [hMx]
  calc _ ≤ ‖iteratedFDeriv ℝ i f (x, 0)‖ * ∏ _ : Fin i, ‖M‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ i f (x, 0)‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hM
    _ ≤ C * Real.exp (c * ‖x‖) := by rw [mul_one]; exact h i hi x 0 (mem_closedBall_self hr)

/-- Linear maps of the field (finite dimension) are moderate. -/
lemma moderate_linear_fst [FiniteDimensional ℝ X] (r : ℝ) (L : X →ₗ[ℝ] E) : Moderate r (fun y : X × P => L y.1) :=
  moderate_clm r ((LinearMap.toContinuousLinearMap L).comp (ContinuousLinearMap.fst ℝ X P))

lemma moderate_fst_param (r : ℝ) : Moderate r (fun y : X × (ℝ × ℝ) => y.2.1) :=
  moderate_clm r ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ X (ℝ × ℝ)))

lemma moderate_snd_param (r : ℝ) : Moderate r (fun y : X × (ℝ × ℝ) => y.2.2) :=
  moderate_clm r ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ X (ℝ × ℝ)))

lemma Moderate.norm_sq {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] {r : ℝ} {f : X × P → F'}
    (hf : Moderate r f) : Moderate r (fun y => ‖f y‖ ^ 2) := by
  have h := hf.bilinear hf (innerSL ℝ (E := F'))
  have hfun : (fun y => innerSL ℝ (f y) (f y)) = fun y => ‖f y‖ ^ 2 :=
    funext fun y => by rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  rwa [hfun] at h

lemma Moderate.mul {r : ℝ} {f g : X × P → ℝ} (hf : Moderate r f) (hg : Moderate r g) :
    Moderate r (fun y => f y * g y) := by
  simpa using hf.bilinear hg (ContinuousLinearMap.mul ℝ ℝ)

lemma Moderate.const_mul {r : ℝ} {f : X × P → ℝ} (hf : Moderate r f) (c : ℝ) : Moderate r (fun y => c * f y) := by
  simpa [smul_eq_mul] using hf.const_smul c

end Moderate

section ExpBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `‖e^A‖ ≤ e^{‖A‖}` for continuous linear operators. -/
lemma norm_exp_clm_le (A : E →L[ℝ] E) : ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  have hpow : ∀ n : ℕ, ‖A ^ n‖ ≤ ‖A‖ ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    · exact norm_pow_le' A hn
  have hterm : ∀ n : ℕ, ‖((n ! : ℝ)⁻¹) • A ^ n‖ ≤ ‖A‖ ^ n / n ! := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hpow n) (by positivity)
  have hs : Summable fun n : ℕ => ‖A‖ ^ n / n ! := Real.summable_pow_div_factorial ‖A‖
  have hsn : Summable fun n : ℕ => ‖((n ! : ℝ)⁻¹) • A ^ n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hs
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  calc ‖∑' n : ℕ, ((n ! : ℝ)⁻¹) • A ^ n‖ ≤ ∑' n : ℕ, ‖((n ! : ℝ)⁻¹) • A ^ n‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, ‖A‖ ^ n / n ! := hsn.tsum_le_tsum hterm hs
    _ = Real.exp ‖A‖ := by rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

variable [CompleteSpace E]

/-- `∂_τ^i e^{τ Q} = e^{τ Q} Q^i`. -/
lemma iteratedDeriv_exp_smul (Q : E →L[ℝ] E) (i : ℕ) :
    iteratedDeriv i (fun τ : ℝ => NormedSpace.exp (τ • Q)) = fun τ => NormedSpace.exp (τ • Q) * Q ^ i := by
  induction i with
  | zero =>
    funext τ
    simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext τ
    rw [((hasDerivAt_exp_smul_const Q τ).mul_const (Q ^ i)).deriv, mul_assoc, ← pow_succ']

lemma contDiff_exp_smul (Q : E →L[ℝ] E) : ContDiff ℝ ∞ (fun τ : ℝ => NormedSpace.exp (τ • Q)) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [iteratedDeriv_exp_smul]
  exact fun τ => ((hasDerivAt_exp_smul_const Q τ).mul_const _).differentiableAt

lemma norm_iteratedFDeriv_exp_smul_le (Q : E →L[ℝ] E) {i n : ℕ} (hi : i ≤ n) (τ : ℝ) :
    ‖iteratedFDeriv ℝ i (fun s : ℝ => NormedSpace.exp (s • Q)) τ‖ ≤ Real.exp (|τ| * ‖Q‖) * (1 + ‖Q‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_smul]
  have hpow : ‖Q ^ i‖ ≤ (1 + ‖Q‖) ^ n := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pow_zero]
      exact ContinuousLinearMap.norm_id_le.trans (one_le_pow₀ (by linarith [norm_nonneg Q]))
    · calc ‖Q ^ i‖ ≤ ‖Q‖ ^ i := norm_pow_le' Q hi0
        _ ≤ (1 + ‖Q‖) ^ i := pow_le_pow_left₀ (norm_nonneg Q) (by linarith) i
        _ ≤ (1 + ‖Q‖) ^ n := pow_le_pow_right₀ (by linarith [norm_nonneg Q]) hi
  calc ‖NormedSpace.exp (τ • Q) * Q ^ i‖ ≤ ‖NormedSpace.exp (τ • Q)‖ * ‖Q ^ i‖ := norm_mul_le _ _
    _ ≤ Real.exp ‖τ • Q‖ * (1 + ‖Q‖) ^ n :=
        mul_le_mul (norm_exp_clm_le _) hpow (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|τ| * ‖Q‖) * (1 + ‖Q‖) ^ n := by rw [norm_smul, Real.norm_eq_abs]

end ExpBounds

section Composition

variable {X P E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ X] in
/-- The bound `D^i ≤ D^n` with `D = 1 + C e^{c ‖x‖} ≤ (1 + C) e^{c ‖x‖}`. -/
lemma pow_one_add_mul_exp_le {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (x : X) {i n : ℕ} (hi : i ≤ n) :
    (1 + C * Real.exp (c * ‖x‖)) ^ i ≤ (1 + C) ^ n * Real.exp ((n * c) * ‖x‖) := by
  have he : 1 ≤ Real.exp (c * ‖x‖) := Real.one_le_exp (by positivity)
  have hD1 : 1 ≤ 1 + C * Real.exp (c * ‖x‖) := by nlinarith
  calc (1 + C * Real.exp (c * ‖x‖)) ^ i ≤ (1 + C * Real.exp (c * ‖x‖)) ^ n := pow_le_pow_right₀ hD1 hi
    _ ≤ ((1 + C) * Real.exp (c * ‖x‖)) ^ n := by
        refine pow_le_pow_left₀ (by linarith) ?_ n
        nlinarith
    _ = (1 + C) ^ n * Real.exp ((n * c) * ‖x‖) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf

/-- **Transports**: if the phase `τ` is moderate and of linear growth, `e^{τ Q}` is moderate. -/
lemma Moderate.exp_smul_clm [CompleteSpace E] {r : ℝ} {τ : X × P → ℝ} (hτ : Moderate r τ) {a b : ℝ} (hb : 0 ≤ b)
    (hlin : ∀ x, ∀ p ∈ closedBall (0 : P) r, |τ (x, p)| ≤ a + b * ‖x‖) (Q : E →L[ℝ] E) :
    Moderate r (fun y => NormedSpace.exp (τ y • Q)) := by
  have hg := contDiff_exp_smul Q
  refine ⟨hg.comp hτ.1, fun n => ?_⟩
  obtain ⟨C, c, hC, hc, h⟩ := hτ.2 n
  refine ⟨n ! * (Real.exp (a * ‖Q‖) * (1 + ‖Q‖) ^ n) * (1 + C) ^ n, b * ‖Q‖ + n * c, by positivity,
    by positivity, fun i hi x p hp => ?_⟩
  have hD1 : 1 ≤ 1 + C * Real.exp (c * ‖x‖) := by have := Real.exp_pos (c * ‖x‖); nlinarith
  have hCg : ∀ j ≤ i, ‖iteratedFDeriv ℝ j (fun s : ℝ => NormedSpace.exp (s • Q)) (τ (x, p))‖ ≤
      Real.exp ((a + b * ‖x‖) * ‖Q‖) * (1 + ‖Q‖) ^ n := by
    intro j hj
    refine (norm_iteratedFDeriv_exp_smul_le Q (hj.trans hi) _).trans ?_
    gcongr
    exact hlin x p hp
  have hDf : ∀ j, 1 ≤ j → j ≤ i → ‖iteratedFDeriv ℝ j τ (x, p)‖ ≤ (1 + C * Real.exp (c * ‖x‖)) ^ j := by
    intro j hj1 hj
    refine ((h j (hj.trans hi) x p hp).trans (by linarith)).trans (le_self_pow₀ hD1 (by omega))
  have hcomp := norm_iteratedFDeriv_comp_le (contDiff_of_infty hg i) (contDiff_of_infty hτ.1 i) le_rfl (x, p)
    hCg hDf
  have hfun : (fun y => NormedSpace.exp (τ y • Q)) = (fun s : ℝ => NormedSpace.exp (s • Q)) ∘ τ := rfl
  rw [hfun]
  have hfac : (i ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le hi
  have hpow := pow_one_add_mul_exp_le hC hc x hi
  have hexp : Real.exp ((a + b * ‖x‖) * ‖Q‖) = Real.exp (a * ‖Q‖) * Real.exp ((b * ‖Q‖) * ‖x‖) := by
    rw [← Real.exp_add]
    ring_nf
  calc _ ≤ i ! * (Real.exp ((a + b * ‖x‖) * ‖Q‖) * (1 + ‖Q‖) ^ n) * (1 + C * Real.exp (c * ‖x‖)) ^ i := hcomp
    _ ≤ n ! * (Real.exp ((a + b * ‖x‖) * ‖Q‖) * (1 + ‖Q‖) ^ n) * ((1 + C) ^ n * Real.exp ((n * c) * ‖x‖)) := by
        gcongr
    _ = n ! * (Real.exp (a * ‖Q‖) * (1 + ‖Q‖) ^ n) * (1 + C) ^ n * Real.exp ((b * ‖Q‖ + n * c) * ‖x‖) := by
        rw [hexp, add_mul, Real.exp_add]
        ring

/-- **Derivatives of `e^F`** for a moderate scalar family: `‖D^i e^F‖ ≤ C e^{c ‖x‖} e^F`. -/
lemma Moderate.norm_iteratedFDeriv_exp_le {r : ℝ} {F : X × P → ℝ} (hF : Moderate r F) (n : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ i ≤ n, ∀ x : X, ∀ p ∈ closedBall (0 : P) r,
      ‖iteratedFDeriv ℝ i (fun y => Real.exp (F y)) (x, p)‖ ≤ C * Real.exp (c * ‖x‖) * Real.exp (F (x, p)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hF.2 n
  refine ⟨n ! * (1 + C) ^ n, n * c, by positivity, by positivity, fun i hi x p hp => ?_⟩
  have hD1 : 1 ≤ 1 + C * Real.exp (c * ‖x‖) := by have := Real.exp_pos (c * ‖x‖); nlinarith
  have hCg : ∀ j ≤ i, ‖iteratedFDeriv ℝ j Real.exp (F (x, p))‖ ≤ Real.exp (F (x, p)) := by
    intro j _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hDf : ∀ j, 1 ≤ j → j ≤ i → ‖iteratedFDeriv ℝ j F (x, p)‖ ≤ (1 + C * Real.exp (c * ‖x‖)) ^ j := by
    intro j hj1 hj
    refine ((h j (hj.trans hi) x p hp).trans (by linarith)).trans (le_self_pow₀ hD1 (by omega))
  have hcomp := norm_iteratedFDeriv_comp_le (contDiff_of_infty Real.contDiff_exp i) (contDiff_of_infty hF.1 i)
    le_rfl (x, p) hCg hDf
  have hfun : (fun y => Real.exp (F y)) = Real.exp ∘ F := rfl
  rw [hfun]
  have hfac : (i ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le hi
  have hpow := pow_one_add_mul_exp_le hC hc x hi
  calc _ ≤ i ! * Real.exp (F (x, p)) * (1 + C * Real.exp (c * ‖x‖)) ^ i := hcomp
    _ ≤ n ! * Real.exp (F (x, p)) * ((1 + C) ^ n * Real.exp ((n * c) * ‖x‖)) := by gcongr
    _ = n ! * (1 + C) ^ n * Real.exp ((n * c) * ‖x‖) * Real.exp (F (x, p)) := by ring

end Composition

end GaussianBlockSpin
