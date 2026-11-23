/-
The linear parts at the trivial configuration, for `prop:relative-average`(v) of BALABAN_CORE.tex (`d8bdc4ac1777`).

* `BsumL γ`: the linear map `B ↦ B(γ) = Σ_{b ∈ γ} ±B(b)` (the sum of the values on the bonds of a path, with the sign
  of their orientation).
* `hasFDerivAt_hol_one`: the linear part of `B ↦ e^{iB}(γ)` at `B = 0` is `iB(γ)`.
* `hasFDerivAt_meanV_zero`: the linear part of the mean of `lem:group-mean` at `0` is the average,
  `‖V(Y) - n⁻¹Σ_iYᵢ‖ ≤ 512‖Y‖²` (`meanV_sub_avg_le`).
* `hasFDerivAt_trans_one`: the linear part of the transport `e^{iB}(y, x)` at `B = 0` is `i` times the mean of `B(Γ)`
  over `Γ ∈ 𝐆(y, x)` (the first step of the proof of (v)).
-/
import CoreLean.RelativeAverageBounds2

open Matrix NormedSpace Filter Topology Metric Asymptotics
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference GroupMean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The evaluation `B ↦ B_μ(z)`. -/
def evalL (μ : Fin 4) (z : Site n) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Site n => Mat) z).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 => Site n → Mat) μ)

@[simp] lemma evalL_apply (μ : Fin 4) (z : Site n) (B : Fin 4 → Site n → Mat) : evalL μ z B = B μ z := rfl

/-- The value of a form on a bond, with the sign of its orientation. -/
def bondL (b : Bond n) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  if b.pos then evalL b.dir b.site else -evalL b.dir (b.site - unit n b.dir)

/-- `B ↦ B(γ)`. -/
def BsumL (γ : List (Bond n)) : (Fin 4 → Site n → Mat) →L[ℂ] Mat := (γ.map bondL).sum

lemma BsumL_cons (b : Bond n) (γ : List (Bond n)) : BsumL (N := N) (b :: γ) = bondL b + BsumL γ := by
  simp [BsumL]

lemma BsumL_append (γ δ : List (Bond n)) : BsumL (N := N) (γ ++ δ) = BsumL γ + BsumL δ := by
  simp [BsumL, List.map_append, List.sum_append]

lemma bondL_rev (b : Bond n) : bondL (N := N) b.rev = -bondL b := by
  obtain ⟨z, ρ, s⟩ := b
  cases s
  · simp only [bondL, Bond.rev, Bond.plus, Bool.false_eq_true, ↓reduceIte, Bool.not_false, neg_neg]
  · simp only [bondL, Bond.rev, Bond.plus, ↓reduceIte, Bool.not_true, Bool.false_eq_true, add_sub_cancel_right]

/-- `B(γ⁻¹) = -B(γ)`. -/
lemma BsumL_rv (γ : List (Bond n)) : BsumL (N := N) (rv γ) = -BsumL γ := by
  induction γ with
  | nil => simp [BsumL, rv]
  | cons b γ ih =>
    have e : rv (b :: γ) = rv γ ++ [b.rev] := by simp [rv]
    rw [e, BsumL_append, ih, BsumL_cons]
    simp [BsumL, bondL_rev]

/-- The value of `e^{iB}` on a bond has the linear part `iB(b)` at `B = 0`. -/
lemma hasFDerivAt_val_one (b : Bond n) :
    HasFDerivAt (fun B => (((moveC (oneC (N := N)) B).val b : GLN) : Mat)) (Complex.I • bondL b) 0 := by
  obtain ⟨z, ρ, s⟩ := b
  have hexp : ∀ (ε : ℂ) (μ : Fin 4) (w : Site n), HasFDerivAt (fun B : Fin 4 → Site n → Mat =>
      exp ((ε * Complex.I) • B μ w)) ((ε * Complex.I) • evalL μ w) 0 := fun ε μ w => by
    have h1 : HasFDerivAt (fun B : Fin 4 → Site n → Mat => (ε * Complex.I) • B μ w) ((ε * Complex.I) • evalL μ w) 0 :=
      ((ε * Complex.I) • evalL μ w).hasFDerivAt
    have h2 := (hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Mat))
    have h3 : HasFDerivAt (exp : Mat → Mat) (1 : Mat →L[ℂ] Mat) ((ε * Complex.I) • (0 : Fin 4 → Site n → Mat) μ w) := by
      simpa using h2
    have h4 := h3.comp 0 h1
    have e : (1 : Mat →L[ℂ] Mat).comp ((ε * Complex.I) • evalL μ w) = (ε * Complex.I) • evalL μ w := by
      ext1 v; simp
    rw [e] at h4
    exact h4
  cases s
  · have e : (fun B => (((moveC (oneC (N := N)) B).val ⟨z, ρ, false⟩ : GLN) : Mat)) = fun B =>
        exp (((-1 : ℂ) * Complex.I) • B ρ (z - unit n ρ)) := by
      funext B
      rw [val_moveC_mat]
      simp [oneC, neg_smul]
    rw [e]
    convert hexp (-1) ρ (z - unit n ρ) using 1
    ext1 v
    simp [bondL]
  · have e : (fun B => (((moveC (oneC (N := N)) B).val ⟨z, ρ, true⟩ : GLN) : Mat)) = fun B =>
        exp (((1 : ℂ) * Complex.I) • B ρ z) := by
      funext B
      rw [val_moveC_mat]
      simp [oneC]
    rw [e]
    convert hexp 1 ρ z using 1
    simp [bondL]

/-- **The linear part of the holonomy at `id`**: `e^{iB}(γ) = id + iB(γ) + O(B²)`. -/
theorem hasFDerivAt_hol_one : ∀ γ : List (Bond n),
    HasFDerivAt (fun B => (((moveC (oneC (N := N)) B).hol γ : GLN) : Mat)) (Complex.I • BsumL γ) 0
  | [] => by
    convert (hasFDerivAt_const (𝕜 := ℂ) (1 : Mat) (0 : Fin 4 → Site n → Mat)) using 1
    · funext B; simp [Config.hol]
    · ext1 v; simp [BsumL]
  | b :: γ => by
    have h1 := hasFDerivAt_val_one (N := N) b
    have h2 := hasFDerivAt_hol_one γ
    have e : (fun B => (((moveC (oneC (N := N)) B).hol (b :: γ) : GLN) : Mat)) =
        fun B => (((moveC (oneC (N := N)) B).val b : GLN) : Mat) * (((moveC (oneC (N := N)) B).hol γ : GLN) : Mat) := by
      funext B; rw [hol_cons, Units.val_mul]
    rw [e]
    have h0b : (((moveC (oneC (N := N)) 0).val b : GLN) : Mat) = 1 := by
      rw [moveC_zero]; obtain ⟨z, ρ, s⟩ := b; cases s <;> simp [Config.val, oneC]
    have h0γ : (((moveC (oneC (N := N)) 0).hol γ : GLN) : Mat) = 1 := by rw [moveC_zero, hol_oneC]; rfl
    have h := h1.mul' h2
    convert h using 1
    ext1 v
    simp [h0b, h0γ, BsumL_cons, smul_add, add_comm]

/-! ### The linear part of the mean -/

/-- `‖V(Y) - n⁻¹Σ_iYᵢ‖ ≤ 512‖Y‖²` for `‖Y‖ ≤ 2^{-10}`. -/
theorem meanV_sub_avg_le {k : ℕ} (hk : 0 < k) {Y : Fin k → Mat} (hY : ‖Y‖ ≤ 1 / 1024) :
    ‖meanV Y - ((k : ℂ)⁻¹) • ∑ i, Y i‖ ≤ 512 * ‖Y‖ ^ 2 := by
  have hYi : ∀ i, ‖Y i‖ ≤ ‖Y‖ := fun i => norm_le_pi_norm Y i
  have hY512 : ∀ i, ‖Y i‖ ≤ 1 / 512 := fun i => (hYi i).trans (by linarith)
  obtain ⟨hV, hfix⟩ := meanV_spec hk hY512
  have hT := (sum_psi_eq_zero_iff hk Y (meanV Y)).1 hfix
  have hVle : ‖meanV Y‖ ≤ 2 * ‖Y‖ := norm_meanV_le hk hY512 ‖Y‖ hYi
  have hfix' : meanV Y = ((k : ℂ)⁻¹) • ∑ i, Y i + ((k : ℂ)⁻¹) • ∑ i, Phi (Y i) (-meanV Y) := by
    conv_lhs => rw [← hT]
    simp only [T, Finset.sum_add_distrib, smul_add]
  rw [hfix', add_sub_cancel_left]
  have hPhi : ∀ i, ‖Phi (Y i) (-meanV Y)‖ ≤ 256 * ‖Y‖ * (2 * ‖Y‖) := fun i => by
    have h1 : ‖Y i‖ ≤ 1 / 32 := (hY512 i).trans (by norm_num)
    have h2 : ‖-meanV Y‖ ≤ 1 / 32 := by rw [norm_neg]; linarith
    calc _ ≤ 256 * ‖Y i‖ * ‖-meanV Y‖ := norm_Phi_le h1 h2
      _ ≤ 256 * ‖Y‖ * (2 * ‖Y‖) := by rw [norm_neg]; gcongr; exact hYi i
  rw [norm_inv_smul hk]
  calc (k : ℝ)⁻¹ * ‖∑ i, Phi (Y i) (-meanV Y)‖ ≤ (k : ℝ)⁻¹ * ∑ _i : Fin k, 256 * ‖Y‖ * (2 * ‖Y‖) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hPhi i)) (by positivity)
    _ = 512 * ‖Y‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
        field_simp; ring

/-- The average `Y ↦ n⁻¹Σ_iYᵢ`. -/
def avgL (k : ℕ) : (Fin k → Mat) →L[ℂ] Mat :=
  ((k : ℂ)⁻¹) • ∑ i, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => Mat) i

lemma avgL_apply (k : ℕ) (Y : Fin k → Mat) : avgL k Y = ((k : ℂ)⁻¹) • ∑ i, Y i := by
  simp [avgL]

lemma meanV_zero' {k : ℕ} (hk : 0 < k) : meanV (0 : Fin k → Mat) = 0 := meanV_zero hk

/-- **The linear part of the mean at `0` is the average.** -/
theorem hasFDerivAt_meanV_zero {k : ℕ} (hk : 0 < k) : HasFDerivAt (meanV (N := N) (n := k)) (avgL k) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, meanV_zero' hk, sub_zero]
  refine isLittleO_iff.2 fun c hc => ?_
  filter_upwards [ball_mem_nhds (0 : Fin k → Mat) (lt_min (by norm_num : (0 : ℝ) < 1 / 1024)
    (by positivity : 0 < c / 512))] with Y hY
  rw [mem_ball, dist_zero_right, lt_min_iff] at hY
  rw [avgL_apply]
  calc _ ≤ 512 * ‖Y‖ ^ 2 := meanV_sub_avg_le hk hY.1.le
    _ = (512 * ‖Y‖) * ‖Y‖ := by ring
    _ ≤ c * ‖Y‖ := by
        gcongr
        have := hY.2
        rw [lt_div_iff₀ (by norm_num)] at this
        linarith

/-! ### The linear part of the transports at `id` -/

/-- The linear part of `B ↦ e^{iB}(Γ)` for the paths of `𝐆(y, x)`. -/
lemma hasFDerivAt_holG_one (y : Site n) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) :
    HasFDerivAt (fun B => ((holG (moveC (oneC (N := N)) B) y h x Γ : GLN) : Mat))
      (Complex.I • BsumL (stair y (offP h x) (ordG h x Γ) 0)) 0 :=
  hasFDerivAt_hol_one _

lemma holG_oneC_zero (y : Site n) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) :
    holG (moveC (oneC (N := N)) 0) y h x Γ = 1 := by
  rw [moveC_zero]; simp [holG, hol_oneC]

/-- The paths of `𝐆(y, x)` with their sums, as a family over the enumeration. -/
def bsG (y : Site n) (h : ℕ) (x : Pts h) (i : Fin (nG h x)) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  BsumL (N := N) (stair y (offP h x) (ordG h x (enumG h x i)) 0)

set_option maxHeartbeats 1000000 in
/-- **The linear part of the transport at `id`**: `e^{iB}(y, x) = id + i·mean_Γ B(Γ) + O(B²)`. -/
theorem hasFDerivAt_trans_one (y : Site n) (h : ℕ) (x : Pts h) :
    HasFDerivAt (fun B => ((trans (moveC (oneC (N := N)) B) y h x : GLN) : Mat))
      (Complex.I • (((nG h x : ℂ))⁻¹ • ∑ i, bsG (N := N) y h x i)) 0 := by
  have hk0 : 0 < nG h x := card_ords_pos _
  have hk' : ((nG h x : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  set b0 := BsumL (N := N) (stair y (offP h x) (ordG h x (firstG h x)) 0) with hb0
  -- the quotients
  have hq : ∀ i, HasFDerivAt (fun B => ((quotG (moveC (oneC (N := N)) B) y h x i : GLN) : Mat))
      (Complex.I • bsG (N := N) y h x i - Complex.I • b0) 0 := fun i => by
    have h1 := hasFDerivAt_holG_one (N := N) y h x (enumG h x i)
    have h2 := inv_one (hasFDerivAt_holG_one (N := N) y h x (firstG h x)) (holG_oneC_zero y h x _)
    have hm := h1.mul' h2
    simp only [quotG, Units.val_mul]
    convert hm using 1
    ext1 v
    simp [holG_oneC_zero, bsG, hb0, sub_eq_add_neg, add_comm]
  have hq0 : ∀ i, ((quotG (moveC (oneC (N := N)) 0) y h x i : GLN) : Mat) = 1 := fun i => by
    simp [quotG, holG_oneC_zero]
  -- the exponents
  have hY : HasFDerivAt (fun B => expsG (moveC (oneC (N := N)) B) y h x)
      (ContinuousLinearMap.pi fun i => bsG (N := N) y h x i - b0) 0 := by
    refine hasFDerivAt_pi.2 fun i => ?_
    have hm := (LogM_comp_one (hq i) (hq0 i)).fun_const_smul (1 / Complex.I : ℂ)
    have e : (1 / Complex.I : ℂ) • (Complex.I • bsG (N := N) y h x i - Complex.I • b0) =
        bsG (N := N) y h x i - b0 := by
      ext1 v; simp [smul_sub, smul_smul, Complex.I_ne_zero]
    rw [e] at hm
    exact hm
  have hY0 : expsG (moveC (oneC (N := N)) 0) y h x = 0 := by
    funext i; simp [expsG, holG_oneC_zero, LogM_one]
  -- the mean
  have hM : HasFDerivAt (fun B => meanV (expsG (moveC (oneC (N := N)) B) y h x))
      ((avgL (nG h x)).comp (ContinuousLinearMap.pi fun i => bsG (N := N) y h x i - b0)) 0 := by
    have h1 : HasFDerivAt (meanV (N := N) (n := nG h x)) (avgL (nG h x)) (expsG (moveC (oneC (N := N)) 0) y h x) := by
      rw [hY0]; exact hasFDerivAt_meanV_zero hk0
    exact h1.comp 0 hY
  have hM0 : meanV (expsG (moveC (oneC (N := N)) 0) y h x) = 0 := by rw [hY0]; exact meanV_zero hk0
  have h2 : HasFDerivAt (exp : Mat → Mat) (1 : Mat →L[ℂ] Mat)
      (Complex.I • meanV (expsG (moveC (oneC (N := N)) 0) y h x)) := by
    rw [hM0, smul_zero]; exact hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Mat)
  have hE := h2.comp 0 (hM.fun_const_smul Complex.I)
  have hE0 : exp (Complex.I • meanV (expsG (moveC (oneC (N := N)) 0) y h x)) = 1 := by rw [hM0]; simp
  -- the transport
  have hT := hE.mul' (hasFDerivAt_holG_one (N := N) y h x (firstG h x))
  have e : (fun B => ((trans (moveC (oneC (N := N)) B) y h x : GLN) : Mat)) = fun B =>
      exp (Complex.I • meanV (expsG (moveC (oneC (N := N)) B) y h x)) *
        ((holG (moveC (oneC (N := N)) B) y h x (firstG h x) : GLN) : Mat) := by
    funext B; simp [trans, mean]
  rw [e]
  convert hT using 1
  · funext B; rfl
  · have hE0' : (exp ∘ fun i => Complex.I • meanV (expsG (moveC (oneC (N := N)) i) y h x)) 0 = 1 := hE0
    ext1 v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply, avgL_apply, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, hE0', holG_oneC_zero, Units.val_one, smul_eq_mul, one_mul,
      MulOpposite.op_one, one_smul]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul (((nG h x : ℕ) : ℂ))⁻¹, inv_mul_cancel₀ hk', one_smul]
    module

/-! ### The site factor, the average, and `𝓜` at `id` -/

lemma trans_oneC_zero (y : Site n) (h : ℕ) (x : Pts h) : trans (moveC (oneC (N := N)) 0) y h x = 1 := by
  rw [moveC_zero, trans_oneC]

/-- The mean path sums of a block, averaged over the block: the linear part of the site factor at `id`. -/
def siteL (y : Site n) (h : ℕ) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ • ∑ x : Pts h, (((nG h x : ℂ))⁻¹ • ∑ i, bsG (N := N) y h x i)

/-- The linear part of the summand of the exponent of the site factor at `id`. -/
lemma hasFDerivAt_logTrans_one (y : Site n) (h : ℕ) (x : Pts h) :
    HasFDerivAt (fun B => LogM ((trans (moveC (oneC (N := N)) B) y h x * (trans (oneC (N := N)) y h x)⁻¹ : GLN) :
      Mat)) (Complex.I • (((nG h x : ℂ))⁻¹ • ∑ i, bsG (N := N) y h x i)) 0 := by
  have ht := hasFDerivAt_trans_one (N := N) y h x
  have e : (fun B => ((trans (moveC (oneC (N := N)) B) y h x * (trans (oneC (N := N)) y h x)⁻¹ : GLN) : Mat)) =
      fun B => ((trans (moveC (oneC (N := N)) B) y h x : GLN) : Mat) := by
    funext B; rw [trans_oneC, _root_.inv_one, mul_one]
  have h1 : ((trans (moveC (oneC (N := N)) 0) y h x * (trans (oneC (N := N)) y h x)⁻¹ : GLN) : Mat) = 1 := by
    rw [trans_oneC_zero, trans_oneC, _root_.inv_one, mul_one, Units.val_one]
  rw [← e] at ht
  exact LogM_comp_one ht h1

/-- The linear part of the exponent of the site factor at `id`. -/
lemma hasFDerivAt_sExp_one (y : Site n) (h : ℕ) :
    HasFDerivAt (fun B => sExp (oneC (N := N)) B y h) (Complex.I • siteL (N := N) y h) 0 := by
  unfold sExp
  refine ((HasFDerivAt.fun_sum fun x _ => hasFDerivAt_logTrans_one (N := N) y h x).fun_const_smul
    ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹)).congr_fderiv ?_
  rw [siteL, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ => smul_comm _ _ _

/-- **The linear part of the site factor at `id`**: `v_{id}(A)(y) = id + i·siteL(y)A + O(A²)`. -/
theorem hasFDerivAt_siteFactor_one (y : Site n) (h : ℕ) :
    HasFDerivAt (fun B => ((siteFactor (oneC (N := N)) B y h : GLN) : Mat)) (Complex.I • siteL (N := N) y h) 0 := by
  have hS := hasFDerivAt_sExp_one (N := N) y h
  have h2 : HasFDerivAt (exp : Mat → Mat) (1 : Mat →L[ℂ] Mat) (sExp (oneC (N := N)) 0 y h) := by
    rw [sExp_zero]; exact hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Mat)
  have h3 : HasFDerivAt (exp ∘ fun B => sExp (oneC (N := N)) B y h)
      ((1 : Mat →L[ℂ] Mat).comp (Complex.I • siteL (N := N) y h)) 0 :=
    HasFDerivAt.comp (f := fun B => sExp (oneC (N := N)) B y h) (0 : Fin 4 → Site n → Mat) h2 hS
  have e3 : (1 : Mat →L[ℂ] Mat).comp (Complex.I • siteL (N := N) y h) = Complex.I • siteL (N := N) y h := by
    ext1 v; simp
  rw [e3] at h3
  have e : (fun B => ((siteFactor (oneC (N := N)) B y h : GLN) : Mat)) = exp ∘ fun B => sExp (oneC (N := N)) B y h := by
    funext B; simp only [siteFactor_eq_sExp, expU_val, Function.comp_apply]
  rw [e]
  exact h3

/-! ### The average at `id` -/

/-- The weighted double sum of the loops of one point. -/
lemma sum_wt_loop {M : Type*} [AddCommGroup M] [Module ℂ M] {ι' : Type*} [Fintype ι'] {C : ℂ} (hC : C ≠ 0)
    (hk : 0 < Fintype.card ι') (A B : ι' → M) (t c : M) :
    ∑ i, ∑ j, ((C * Fintype.card ι' * Fintype.card ι')⁻¹ : ℂ) • (A i + t - B j - c) =
      C⁻¹ • (((Fintype.card ι' : ℂ))⁻¹ • ∑ i, A i + t - ((Fintype.card ι' : ℂ))⁻¹ • ∑ j, B j - c) := by
  set k : ℂ := (Fintype.card ι' : ℂ) with hkdef
  have hk' : k ≠ 0 := by rw [hkdef]; exact_mod_cast hk.ne'
  have hS : ∑ i, ∑ j, (A i + t - B j - c) = k • ∑ i, A i + (k * k) • t - k • ∑ j, B j - (k * k) • c := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      ← Finset.smul_sum]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, ← hkdef]
    module
  simp only [← Finset.smul_sum]
  rw [hS]
  simp only [smul_add, smul_sub, smul_smul]
  have e2 : (C * k * k)⁻¹ * (k * k) = C⁻¹ := by field_simp
  have e3 : (C * k * k)⁻¹ * k = C⁻¹ * k⁻¹ := by field_simp
  rw [e2, e3]

/-- The sum over the bonds of the loop `ℓ_c(x, Γ, Γ')`. -/
lemma BsumL_lpath (y : Site n) (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ Γ' : Ords (offP h x)) :
    BsumL (N := N) (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ') =
      BsumL (stair y (offP h x) (ordG h x Γ) 0) + BsumL (segZ μ (ofs y (offP h x)) ((2 * h + 1 : ℕ) : ℤ)) -
        BsumL (stair (cPlus y μ h) (offP h x) (ordG h x Γ') 0) - BsumL (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) := by
  simp only [lpath, BsumL_append, BsumL_rv, cPlus]
  abel

/-- The line sums `B([x, x'])` averaged over the block: `L·Q(id)`. -/
def TsumL (y : Site n) (μ : Fin 4) (h : ℕ) : (Fin 4 → Site n → Mat) →L[ℂ] Mat :=
  (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ • ∑ x : Pts h, BsumL (N := N) (segZ μ (ofs y (offP h x)) ((2 * h + 1 : ℕ) : ℤ))

lemma sum_bsG (y : Site n) (h : ℕ) (x : Pts h) :
    ∑ i, bsG (N := N) y h x i = ∑ Γ : Ords (offP h x), BsumL (N := N) (stair y (offP h x) (ordG h x Γ) 0) :=
  Equiv.sum_comp (enumG h x) (fun Γ => BsumL (N := N) (stair y (offP h x) (ordG h x Γ) 0))

/-- The weighted sum of the loop sums. -/
lemma sum_wt_loops (y : Site n) (μ : Fin 4) (h : ℕ) :
    ∑ x : Pts h, ∑ Γ : Ords (offP h x), ∑ Γ' : Ords (offP h x),
      Average.wt (fun x : Pts h => Ords (offP h x)) (fun x : Pts h => Ords (offP h x)) x •
        BsumL (N := N) (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ') =
      siteL y h - siteL (cPlus y μ h) h + TsumL y μ h - BsumL (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) := by
  have hL4 : ((Fintype.card (Pts h) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by rw [card_pts]; positivity)
  have hx : ∀ x : Pts h, ∑ Γ : Ords (offP h x), ∑ Γ' : Ords (offP h x),
      Average.wt (fun x : Pts h => Ords (offP h x)) (fun x : Pts h => Ords (offP h x)) x •
        BsumL (N := N) (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h) (ordG h) x Γ Γ') =
      (((Fintype.card (Pts h) : ℕ) : ℂ))⁻¹ • ((((nG h x : ℕ) : ℂ))⁻¹ • ∑ i, bsG (N := N) y h x i +
        BsumL (segZ μ (ofs y (offP h x)) ((2 * h + 1 : ℕ) : ℤ)) -
        (((nG h x : ℕ) : ℂ))⁻¹ • ∑ i, bsG (N := N) (cPlus y μ h) h x i - BsumL (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) := by
    intro x
    simp only [BsumL_lpath, Average.wt, sum_bsG]
    exact sum_wt_loop hL4 (card_ords_pos _) _ _ _ _
  rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.smul_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  simp only [siteL, TsumL, card_pts, smul_sub, smul_add, Nat.cast_pow]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_pow,
    inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))), one_smul]
  abel

lemma hol_moveC_one_zero (γ : List (Bond n)) : (((moveC (oneC (N := N)) 0).hol γ : GLN) : Mat) = 1 := by
  rw [moveC_zero, hol_oneC]; rfl

/-- The linear part of `β_c(e^{iB})` at `B = 0`. -/
lemma hasFDerivAt_betaLog_one (y : Site n) (μ : Fin 4) (h : ℕ) :
    HasFDerivAt (fun B => betaLog (ι := Pts h) (P := fun x => Ords (offP h x)) (moveC (oneC (N := N)) B) y μ
      (2 * h + 1) (offP h) (ordG h))
      (∑ x : Pts h, ∑ Γ : Ords (offP h x), ∑ Γ' : Ords (offP h x),
        Average.wt (fun x : Pts h => Ords (offP h x)) (fun x : Pts h => Ords (offP h x)) x •
          ((1 / Complex.I : ℂ) • (Complex.I • BsumL (N := N) (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ
            (2 * h + 1) (offP h) (ordG h) x Γ Γ')))) 0 := by
  unfold betaLog
  refine HasFDerivAt.fun_sum fun x _ => HasFDerivAt.fun_sum fun Γ _ => HasFDerivAt.fun_sum fun Γ' _ => ?_
  have hL := LogM_comp_one (hasFDerivAt_hol_one (N := N) (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ
    (2 * h + 1) (offP h) (ordG h) x Γ Γ')) (hol_moveC_one_zero _)
  exact (hL.fun_const_smul (1 / Complex.I : ℂ)).fun_const_smul _

lemma betaLog_one_zero (y : Site n) (μ : Fin 4) (h : ℕ) :
    betaLog (ι := Pts h) (P := fun x => Ords (offP h x)) (moveC (oneC (N := N)) 0) y μ (2 * h + 1) (offP h)
      (ordG h) = 0 := by
  simp [betaLog, hol_moveC_one_zero, LogM_one]

/-- **The linear part of the average at `id`**: `M(e^{iB})(c) = id + i(siteL(c₋) - siteL(c₊) + TsumL)B + O(B²)`. -/
theorem hasFDerivAt_avgM_one (y : Site n) (μ : Fin 4) (h : ℕ) :
    HasFDerivAt (fun B => ((avgM (moveC (oneC (N := N)) B) y μ h : GLN) : Mat))
      (Complex.I • (siteL (N := N) y h - siteL (cPlus y μ h) h + TsumL y μ h)) 0 := by
  have hβ := hasFDerivAt_betaLog_one (N := N) y μ h
  have h2 : HasFDerivAt (exp : Mat → Mat) (1 : Mat →L[ℂ] Mat) (Complex.I • betaLog (ι := Pts h)
      (P := fun x => Ords (offP h x)) (moveC (oneC (N := N)) 0) y μ (2 * h + 1) (offP h) (ordG h)) := by
    rw [betaLog_one_zero, smul_zero]; exact hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Mat)
  have hE := HasFDerivAt.comp (f := fun B => Complex.I • betaLog (ι := Pts h) (P := fun x => Ords (offP h x))
    (moveC (oneC (N := N)) B) y μ (2 * h + 1) (offP h) (ordG h)) (0 : Fin 4 → Site n → Mat) h2
    (hβ.fun_const_smul Complex.I)
  have hseg := hasFDerivAt_hol_one (N := N) (segZ μ y ((2 * h + 1 : ℕ) : ℤ))
  have hP := hE.mul' hseg
  have e : (fun B => ((avgM (moveC (oneC (N := N)) B) y μ h : GLN) : Mat)) =
      (exp ∘ fun B => Complex.I • betaLog (ι := Pts h) (P := fun x => Ords (offP h x)) (moveC (oneC (N := N)) B)
        y μ (2 * h + 1) (offP h) (ordG h)) * fun B => (((moveC (oneC (N := N)) B).hol
          (segZ μ y ((2 * h + 1 : ℕ) : ℤ)) : GLN) : Mat) := by
    funext B; simp [avgM, avgLogU]
  rw [e]
  refine hP.congr_fderiv ?_
  have hE0 : (exp ∘ fun B => Complex.I • betaLog (ι := Pts h) (P := fun x => Ords (offP h x))
      (moveC (oneC (N := N)) B) y μ (2 * h + 1) (offP h) (ordG h)) 0 = 1 := by
    simp [betaLog_one_zero]
  rw [hE0, hol_moveC_one_zero]
  have hw := sum_wt_loops (N := N) y μ h
  have hII : ∀ X : (Fin 4 → Site n → Mat) →L[ℂ] Mat, (1 / Complex.I : ℂ) • (Complex.I • X) = X := fun X => by
    rw [smul_smul, show (1 / Complex.I * Complex.I : ℂ) = 1 by field_simp, one_smul]
  simp only [hII] at *
  ext1 v
  have hw' := congrArg (fun F : (Fin 4 → Site n → Mat) →L[ℂ] Mat => F v) hw
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] at hw'
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, one_mul, MulOpposite.op_one, one_smul, Units.val_one]
  rw [hw']
  simp only [smul_sub, smul_add]
  abel

lemma avgM_oneC (y : Site n) (μ : Fin 4) (h : ℕ) : avgM (oneC (N := N)) y μ h = 1 := by
  have := betaLog_one_zero (N := N) y μ h
  rw [moveC_zero] at this
  ext1
  simp [avgM, avgLogU, this, hol_oneC]

/-- **`Q(id) = Q₀(id)`** (the first statement of (v)): `L·Q(id)B = L⁻⁴Σ_x B([x, x'])`. -/
theorem Qlin_oneC (y : Site n) (μ : Fin 4) (h : ℕ) :
    ((2 * h + 1 : ℕ) : ℂ) • Qlin (oneC (N := N)) y μ h = TsumL y μ h := by
  have hL : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- the linear part of `𝓜` at `id`
  have hv := hasFDerivAt_siteFactor_one (N := N) y h
  have hv' := hasFDerivAt_siteFactor_one (N := N) (cPlus y μ h) h
  have hM := hasFDerivAt_avgM_one (N := N) y μ h
  have hvi := inv_one hv (siteFactor_zero _ _ _)
  have hR := (hvi.mul' hM).mul' hv'
  have e : (fun B => ((relAvg (oneC (N := N)) B y μ h : GLN) : Mat)) =
      ((fun p => (((siteFactor (oneC (N := N)) p y h)⁻¹ : GLN) : Mat)) * fun B =>
        ((avgM (moveC (oneC (N := N)) B) y μ h : GLN) : Mat)) * fun B =>
          ((siteFactor (oneC (N := N)) B (cPlus y μ h) h : GLN) : Mat) := by
    funext B; simp [relAvg, avgM_oneC]
  have hR' : HasFDerivAt (fun B => ((relAvg (oneC (N := N)) B y μ h : GLN) : Mat)) (Complex.I • TsumL y μ h) 0 := by
    rw [e]
    refine hR.congr_fderiv ?_
    have h1 : (((siteFactor (oneC (N := N)) 0 y h)⁻¹ : GLN) : Mat) = 1 := by simp [siteFactor_zero]
    have h2 : ((avgM (moveC (oneC (N := N)) 0) y μ h : GLN) : Mat) = 1 := by rw [moveC_zero, avgM_oneC]; rfl
    have h3 : ((siteFactor (oneC (N := N)) 0 (cPlus y μ h) h : GLN) : Mat) = 1 := by simp [siteFactor_zero]
    simp only [Pi.mul_apply, h1, h2, h3, one_mul, MulOpposite.op_one, one_smul]
    ext1 v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.sub_apply, smul_add, smul_sub]
    abel
  have hlog := (LogM_comp_one hR' (by simp [relAvg_zero])).fun_const_smul (1 / Complex.I : ℂ)
  have hfd : fderiv ℂ (fun B => relLog (oneC (N := N)) B y μ h) 0 = TsumL y μ h := by
    have hfun : (fun B => relLog (oneC (N := N)) B y μ h) =
        fun B => (1 / Complex.I : ℂ) • LogM ((relAvg (oneC (N := N)) B y μ h : GLN) : Mat) := rfl
    rw [hfun, hlog.fderiv, smul_smul, show (1 / Complex.I * Complex.I : ℂ) = 1 by field_simp, one_smul]
  simp only [Qlin, smul_smul, mul_inv_cancel₀ hL, one_smul, hfd]

end RelativeAverage
end CoreLean

end
