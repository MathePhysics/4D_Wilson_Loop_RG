/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`), the setting and the first steps, on the fine lattice of a
sequence of domains in the units `a₀ = 1` (`a_j = Lʲ`, `w(x) = L^{-2j(x)}`), for families `u = (u_k)_{k < m}` of
`0`-forms (the values in `M_N(ℂ)^m`, `|v|² = Σ_k|v_k|²` with the Hilbert–Schmidt norm).

* `wN`, `dN`, `fN`, `gN`, `eF`: `‖v‖_w²`, `‖∂v‖₂²`, `‖e^φf‖_{w⁻¹}²`, `‖e^φg‖₂²`, `e^φv` (`eq:weight-norms`).
* `card_near`: a cube `{x | |x - y|_∞ < c}` has at most `(2c)⁴` sites.
* `phi_lip`: `φ = δd(·, y')` is `δ`-Lipschitz in `d`.
* `weighted_source` (the step "The weighted bound", `eq:sf-weighted-source`): for `f`, `g` supported in `Δ̃(y')`,
  `y' ∈ Γ_{j'}`, `φ = δ₁d(·, y')`, `δ₁ ≤ (128L)⁻¹`: `‖e^φf‖_{w⁻¹} ≤ 8L·a_{j'}³‖f‖_∞` and
  `‖e^φg‖₂ ≤ 16a_{j'}²max_μ‖g_μ‖_∞`.
* `value_le_wN` (the step "Values in the layers 0, 1, and 2"): `|v(z)| ≤ a_{j(z)}e^{-φ(z)}‖e^φv‖_w`.
-/
import CoreLean.SFLift
import CoreLean.SFBoxGeom

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox

variable (S : SeqDom) {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- `|v|² = Σ_k|v_k|²`. -/
def nsq (v : Fin m → Mat) : ℝ := ∑ k, hs2 (v k)

lemma nsq_nonneg (v : Fin m → Mat) : 0 ≤ nsq v := sum_nonneg fun _ _ => hs2_nonneg _

/-- `‖v‖_w² = Σ_x a_{j(x)}⁻²|v(x)|²`. -/
def wN (v : Fin m → Site NF → Mat) : ℝ := ∑ x, ((S.L : ℝ) ^ (2 * jj x))⁻¹ * nsq fun k => v k x

/-- `‖∂v‖₂² = Σ_xΣ_μ|v(x + e_μ) - v(x)|²`. -/
def dN (v : Fin m → Site NF → Mat) : ℝ := ∑ x, ∑ μ : Fin 4, nsq fun k => v k (x + unit _ μ) - v k x

/-- `‖e^φf‖_{w⁻¹}² = Σ_x a_{j(x)}²e^{2φ(x)}|f(x)|²`. -/
def fN (ph : Site NF → ℝ) (f : Fin m → Site NF → Mat) : ℝ :=
  ∑ x, (S.L : ℝ) ^ (2 * jj x) * Real.exp (2 * ph x) * nsq fun k => f k x

/-- `‖e^φg‖₂² = Σ_xΣ_μ e^{2φ(x)}|g_μ(x)|²`. -/
def gN (ph : Site NF → ℝ) (g : Fin m → Fin 4 → Site NF → Mat) : ℝ :=
  ∑ x, ∑ μ : Fin 4, Real.exp (2 * ph x) * nsq fun k => g k μ x

/-- `e^φv`. -/
def eF (ph : Site NF → ℝ) (v : Fin m → Site NF → Mat) : Fin m → Site NF → Mat :=
  fun k x => ((Real.exp (ph x) : ℝ) : ℂ) • v k x

lemma wN_nonneg (v : Fin m → Site NF → Mat) : 0 ≤ wN S v :=
  sum_nonneg fun _ _ => mul_nonneg (by positivity) (nsq_nonneg _)

lemma fN_nonneg (ph : Site NF → ℝ) (f : Fin m → Site NF → Mat) : 0 ≤ fN S ph f :=
  sum_nonneg fun _ _ => mul_nonneg (by positivity) (nsq_nonneg _)

lemma gN_nonneg (ph : Site NF → ℝ) (g : Fin m → Fin 4 → Site NF → Mat) : 0 ≤ gN S ph g :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (by positivity) (nsq_nonneg _)

lemma nsq_eF (ph : Site NF → ℝ) (v : Fin m → Site NF → Mat) (x : Site NF) :
    (nsq fun k => eF S ph v k x) = Real.exp (2 * ph x) * nsq fun k => v k x := by
  simp only [nsq, eF, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← hs_sq, ← hs_sq, RegularAverages.hs_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    ← Real.exp_nat_mul]
  push_cast; ring_nf

/-! ### Counting -/

/-- **A cube `|x - y|_∞ < c` has at most `(2c)⁴` sites.** -/
lemma card_near {n : ℕ} [NeZero n] (y : Site n) (c : ℕ) :
    ((univ.filter fun x : Site n => dinf x y < c).card : ℝ) ≤ (2 * c : ℝ) ^ 4 := by
  classical
  have hinj : Set.InjOn (fun x : Site n => fun ν => (x ν - y ν).valMinAbs)
      (univ.filter fun x : Site n => dinf x y < c) := by
    intro x _ x' _ h
    funext ν
    have := congrFun h ν
    have e1 := ZMod.coe_valMinAbs (x ν - y ν)
    have e2 := ZMod.coe_valMinAbs (x' ν - y ν)
    simp only at this
    rw [this] at e1
    have := e1.symm.trans e2
    exact sub_left_inj.mp this.symm |>.symm
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have : (univ.filter fun x : Site n => dinf x y < 0) = ∅ := by
      ext x; simp
    rw [this]; simp
  -- a sharper count: `|valMinAbs| ≤ c - 1`
  have hmaps' : Set.MapsTo (fun x : Site n => fun ν => (x ν - y ν).valMinAbs)
      (univ.filter fun x : Site n => dinf x y < c)
      (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-((c : ℤ) - 1)) ((c : ℤ) - 1)) := by
    intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro ν
    rw [Finset.mem_Icc]
    have h1 := cd_le_dinf x y ν
    have h2 : (x ν - y ν).valMinAbs.natAbs < c := by unfold cd at h1; omega
    have h3 : |(x ν - y ν).valMinAbs| < c := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
    obtain ⟨h4, h5⟩ := abs_lt.1 h3
    show -((c : ℤ) - 1) ≤ (x ν - y ν).valMinAbs ∧ (x ν - y ν).valMinAbs ≤ (c : ℤ) - 1
    constructor <;> omega
  have hcard' := card_le_card_of_injOn _ hmaps' hinj
  have hT' : (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-((c : ℤ) - 1)) ((c : ℤ) - 1)).card =
      (2 * c - 1) ^ 4 := by
    simp only [Fintype.card_piFinset, Int.card_Icc, prod_const, card_univ, Fintype.card_fin]
    congr 1; omega
  rw [hT'] at hcard'
  calc ((univ.filter fun x : Site n => dinf x y < c).card : ℝ) ≤ ((2 * c - 1 : ℕ) : ℝ) ^ 4 := by
        exact_mod_cast hcard'
    _ ≤ (2 * c : ℝ) ^ 4 := by
        gcongr
        have : (2 * c - 1 : ℕ) ≤ 2 * c := Nat.sub_le _ _
        exact_mod_cast this

/-! ### The weight -/

/-- `φ = δd(·, y')` is `δ`-Lipschitz in `d`. -/
lemma phi_lip {δ : ℝ} (hδ : 0 ≤ δ) (y' x x' : Site NF) :
    |δ * S.dF x y' - δ * S.dF x' y'| ≤ δ * S.dF x x' := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hδ]
  refine mul_le_mul_of_nonneg_left (abs_sub_le_iff.2 ⟨?_, ?_⟩) hδ
  · have := S.dF_triangle x x' y'; linarith
  · have := S.dF_triangle x' x y'; rw [S.dF_comm x' x] at this; linarith

/-- On `Δ̃(y')`, `e^{2φ} ≤ 4` for `φ = δ₁d(·, y')`, `δ₁ ≤ (128L)⁻¹`. -/
lemma exp_phi_tilde (hRM : (S.L : ℝ) ≤ RMS) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L)) {y' x : Site NF}
    (hx : (dinf x y' : ℝ) < (S.L : ℝ) ^ jj y') : Real.exp (2 * (δ * S.dF x y')) ≤ 4 := by
  have hd := S.tilde_dist hRM hx
  rw [S.dF_comm] at hd
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have h1 : 2 * (δ * S.dF x y') ≤ 1 := by
    have hδL : δ * (4 * S.L) ≤ 1 / 32 := by
      calc δ * (4 * S.L) ≤ 1 / (128 * S.L) * (4 * S.L) := mul_le_mul_of_nonneg_right hδ (by positivity)
        _ = 1 / 32 := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hd hδ0]
  calc Real.exp (2 * (δ * S.dF x y')) ≤ Real.exp 1 := Real.exp_le_exp.2 h1
    _ ≤ 4 := by have := Real.exp_one_lt_d9; linarith

/-- **`eq:sf-weighted-source`, the source `f`.** -/
theorem weighted_source_f (hRM : (S.L : ℝ) ≤ RMS) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L))
    {y' : Site NF} {f : Fin m → Site NF → Mat} {F : ℝ} (hF : 0 ≤ F)
    (hsupp : ∀ k x, (S.L : ℝ) ^ jj y' ≤ (dinf x y' : ℝ) → f k x = 0) (hbd : ∀ x, nsq (fun k => f k x) ≤ F ^ 2) :
    Real.sqrt (fN S (fun x => δ * S.dF x y') f) ≤ 8 * (S.L : ℝ) ^ (3 * jj y' + 1) * F := by
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  set T := univ.filter fun x : Site NF => dinf x y' < S.L ^ jj y'
  have hT : (T.card : ℝ) ≤ (2 * (S.L : ℝ) ^ jj y') ^ 4 := by
    have := card_near y' (S.L ^ jj y'); push_cast at this; exact this
  have hsum : fN S (fun x => δ * S.dF x y') f ≤ ∑ _x ∈ T, (S.L : ℝ) ^ (2 * (jj y' + 1)) * 4 * F ^ 2 := by
    unfold fN
    rw [← sum_filter_add_sum_filter_not univ fun x : Site NF => dinf x y' < S.L ^ jj y']
    have h0 : ∑ x ∈ univ.filter (fun x : Site NF => ¬ dinf x y' < S.L ^ jj y'),
        (S.L : ℝ) ^ (2 * jj x) * Real.exp (2 * (δ * S.dF x y')) * (nsq fun k => f k x) = 0 := by
      refine sum_eq_zero fun x hx => ?_
      have hx' : (S.L : ℝ) ^ jj y' ≤ (dinf x y' : ℝ) := by
        have := (mem_filter.1 hx).2; push_neg at this; exact_mod_cast this
      have : (nsq fun k => f k x) = 0 := sum_eq_zero fun k _ => by show hs2 (f k x) = 0; rw [hsupp k x hx']; simp [hs2, ntr]
      rw [this, mul_zero]
    rw [h0, add_zero]
    refine sum_le_sum fun x hx => ?_
    have hx' : (dinf x y' : ℝ) < (S.L : ℝ) ^ jj y' := by exact_mod_cast (mem_filter.1 hx).2
    have hsc := (S.tilde_scale hRM hx').2
    have h1 : (S.L : ℝ) ^ (2 * jj x) ≤ (S.L : ℝ) ^ (2 * (jj y' + 1)) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h2 := exp_phi_tilde S hRM hδ0 hδ hx'
    have h3 := hbd x
    have h4 := nsq_nonneg fun k => f k x
    gcongr
  rw [sum_const, nsmul_eq_mul] at hsum
  have hfin : fN S (fun x => δ * S.dF x y') f ≤ (8 * (S.L : ℝ) ^ (3 * jj y' + 1) * F) ^ 2 := by
    refine hsum.trans ?_
    have e : (8 * (S.L : ℝ) ^ (3 * jj y' + 1) * F) ^ 2 =
        (2 * (S.L : ℝ) ^ jj y') ^ 4 * ((S.L : ℝ) ^ (2 * (jj y' + 1)) * 4 * F ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hT (by positivity)
  calc Real.sqrt (fN S (fun x => δ * S.dF x y') f) ≤ Real.sqrt ((8 * (S.L : ℝ) ^ (3 * jj y' + 1) * F) ^ 2) :=
        Real.sqrt_le_sqrt hfin
    _ = 8 * (S.L : ℝ) ^ (3 * jj y' + 1) * F := Real.sqrt_sq (by positivity)

/-- **`eq:sf-weighted-source`, the source `g`.** -/
theorem weighted_source_g (hRM : (S.L : ℝ) ≤ RMS) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L))
    {y' : Site NF} {g : Fin m → Fin 4 → Site NF → Mat} {G : ℝ} (hG : 0 ≤ G)
    (hsupp : ∀ k μ x, (S.L : ℝ) ^ jj y' ≤ (dinf x y' : ℝ) → g k μ x = 0)
    (hbd : ∀ μ x, nsq (fun k => g k μ x) ≤ G ^ 2) :
    Real.sqrt (gN S (fun x => δ * S.dF x y') g) ≤ 16 * (S.L : ℝ) ^ (2 * jj y') * G := by
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  set T := univ.filter fun x : Site NF => dinf x y' < S.L ^ jj y'
  have hT : (T.card : ℝ) ≤ (2 * (S.L : ℝ) ^ jj y') ^ 4 := by
    have := card_near y' (S.L ^ jj y'); push_cast at this; exact this
  have hsum : gN S (fun x => δ * S.dF x y') g ≤ ∑ _x ∈ T, 16 * G ^ 2 := by
    unfold gN
    rw [← sum_filter_add_sum_filter_not univ fun x : Site NF => dinf x y' < S.L ^ jj y']
    have h0 : ∑ x ∈ univ.filter (fun x : Site NF => ¬ dinf x y' < S.L ^ jj y'),
        ∑ μ : Fin 4, Real.exp (2 * (δ * S.dF x y')) * (nsq fun k => g k μ x) = 0 := by
      refine sum_eq_zero fun x hx => sum_eq_zero fun μ _ => ?_
      have hx' : (S.L : ℝ) ^ jj y' ≤ (dinf x y' : ℝ) := by
        have := (mem_filter.1 hx).2; push_neg at this; exact_mod_cast this
      have : (nsq fun k => g k μ x) = 0 := sum_eq_zero fun k _ => by show hs2 (g k μ x) = 0; rw [hsupp k μ x hx']; simp [hs2, ntr]
      rw [this, mul_zero]
    rw [h0, add_zero]
    refine sum_le_sum fun x hx => ?_
    have hx' : (dinf x y' : ℝ) < (S.L : ℝ) ^ jj y' := by exact_mod_cast (mem_filter.1 hx).2
    have h2 := exp_phi_tilde S hRM hδ0 hδ hx'
    have hμ : ∑ μ : Fin 4, Real.exp (2 * (δ * S.dF x y')) * (nsq fun k => g k μ x) ≤ ∑ _μ : Fin 4, 4 * G ^ 2 :=
      sum_le_sum fun μ _ => by have := hbd μ x; have := nsq_nonneg fun k => g k μ x; gcongr
    have e16 : ∑ _μ : Fin 4, 4 * G ^ 2 = 16 * G ^ 2 := by simp; ring
    linarith
  rw [sum_const, nsmul_eq_mul] at hsum
  have hfin : gN S (fun x => δ * S.dF x y') g ≤ (16 * (S.L : ℝ) ^ (2 * jj y') * G) ^ 2 := by
    refine hsum.trans ?_
    have e : (16 * (S.L : ℝ) ^ (2 * jj y') * G) ^ 2 = (2 * (S.L : ℝ) ^ jj y') ^ 4 * (16 * G ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hT (by positivity)
  calc Real.sqrt (gN S (fun x => δ * S.dF x y') g) ≤ Real.sqrt ((16 * (S.L : ℝ) ^ (2 * jj y') * G) ^ 2) :=
        Real.sqrt_le_sqrt hfin
    _ = 16 * (S.L : ℝ) ^ (2 * jj y') * G := Real.sqrt_sq (by positivity)

/-- **The value at a site from the weighted norm**: `|v(z)| ≤ a_{j(z)}e^{-φ(z)}‖e^φv‖_w`. -/
theorem value_le_wN (ph : Site NF → ℝ) (v : Fin m → Site NF → Mat) (z : Site NF) :
    Real.sqrt (nsq fun k => v k z) ≤ (S.L : ℝ) ^ jj z * Real.exp (-ph z) * Real.sqrt (wN S (eF S ph v)) := by
  have hterm : ((S.L : ℝ) ^ (2 * jj z))⁻¹ * (nsq fun k => eF S ph v k z) ≤ wN S (eF S ph v) :=
    single_le_sum (f := fun x => ((S.L : ℝ) ^ (2 * jj x))⁻¹ * nsq fun k => eF S ph v k x)
      (fun x _ => mul_nonneg (by positivity) (nsq_nonneg _)) (mem_univ z)
  rw [nsq_eF] at hterm
  have hp : (0 : ℝ) < (S.L : ℝ) ^ jj z := by have := S.Lpos; positivity
  have key : (nsq fun k => v k z) ≤ ((S.L : ℝ) ^ jj z * Real.exp (-ph z)) ^ 2 * wN S (eF S ph v) := by
    have e : ((S.L : ℝ) ^ jj z * Real.exp (-ph z)) ^ 2 =
        (S.L : ℝ) ^ (2 * jj z) * (Real.exp (2 * ph z))⁻¹ := by
      rw [mul_pow, pow_mul', ← Real.exp_nat_mul, ← Real.exp_neg]; push_cast; ring_nf
    rw [e]
    have h1 : (S.L : ℝ) ^ (2 * jj z) * (Real.exp (2 * ph z))⁻¹ *
        (((S.L : ℝ) ^ (2 * jj z))⁻¹ * (Real.exp (2 * ph z) * nsq fun k => v k z)) = nsq fun k => v k z := by
      have hA : (S.L : ℝ) ^ (2 * jj z) ≠ 0 := pow_ne_zero _ (by exact_mod_cast S.Lpos.ne')
      have hB : Real.exp (2 * ph z) ≠ 0 := (Real.exp_pos _).ne'
      rw [show (S.L : ℝ) ^ (2 * jj z) * (Real.exp (2 * ph z))⁻¹ *
          (((S.L : ℝ) ^ (2 * jj z))⁻¹ * (Real.exp (2 * ph z) * nsq fun k => v k z)) =
          ((S.L : ℝ) ^ (2 * jj z) * ((S.L : ℝ) ^ (2 * jj z))⁻¹) *
            ((Real.exp (2 * ph z))⁻¹ * Real.exp (2 * ph z)) * nsq fun k => v k z by ring,
        mul_inv_cancel₀ hA, inv_mul_cancel₀ hB, one_mul, one_mul]
    calc (nsq fun k => v k z) = (S.L : ℝ) ^ (2 * jj z) * (Real.exp (2 * ph z))⁻¹ *
          (((S.L : ℝ) ^ (2 * jj z))⁻¹ * (Real.exp (2 * ph z) * nsq fun k => v k z)) := h1.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by positivity)
  calc Real.sqrt (nsq fun k => v k z) ≤ Real.sqrt (((S.L : ℝ) ^ jj z * Real.exp (-ph z)) ^ 2 * wN S (eF S ph v)) :=
        Real.sqrt_le_sqrt key
    _ = _ := by rw [Real.sqrt_mul (pow_two_nonneg _), Real.sqrt_sq (by positivity)]

end SFBounds
end CoreLean

end
