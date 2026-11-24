/-
`lem:sf-vector-decay` of BALABAN_CORE.tex (`b654d81d1528`), step (1) of "The complex field": the forms of the curl and
the divergence of `Δ_𝖺(𝐔)` compared with those of the trivial configuration on the fine lattice (`a₀ = 1`).

The pairing `⟨B^*, C⟩` of the core is `pair1V B C = Σ tr(B^*C)`. Lemma `covariance`(i), the invariance of `tr(YZ)`
under `Ad_g` for every invertible `g`, moves `D_𝐔` across the bilinear pairing; in the sesquilinear form this is the
field `X^*` on the left, since `(Ad_{e^{iX}}Y^*)^* = Ad_{e^{iX^*}}Y`.

* `Xs`: `X^*`; `Ad_expU_conj`, `Dfw_conj`, `Ds1L_conj`; `regField_Xs`.
* `pair1V_Ds2`, `pair1V_D0`: the curl and the divergence forms of `D^*_𝐔D_𝐔` and `D_𝐔D^*_𝐔`.
-/
import CoreLean.SFProjComp

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse SFLocal ConcretePairing

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-! ### The conjugate field -/

/-- `X^*`, componentwise. -/
def Xs (X : Fin 4 → Site NF → Mat) : Fin 4 → Site NF → Mat := fun μ x => (X μ x)ᴴ

omit S in
/-- `(Ad_{e^{iY}}Z^*)^* = Ad_{e^{iY^*}}Z`. -/
lemma Ad_expU_conj (Y Z : Mat) : (Ad (expU (Complex.I • Y)) Zᴴ)ᴴ = Ad (expU (Complex.I • Yᴴ)) Z := by
  rw [Ad_expU, Ad_expU]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.exp_conjTranspose,
    Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, neg_smul, neg_neg,
    mul_assoc]

lemma Dfw_conj (X : Fin 4 → Site NF → Mat) (ν : Fin 4) (f : Site NF → Mat) (x : Site NF) :
    (Dfw 1 (cfgX X) ν (fun y => (f y)ᴴ) x)ᴴ = Dfw 1 (cfgX (Xs S X)) ν f x := by
  simp only [Dfw, cfgX, inv_one, one_smul, Matrix.conjTranspose_sub, Ad_expU_conj,
    Matrix.conjTranspose_conjTranspose, Xs]

lemma Ds1L_conj (X : Fin 4 → Site NF → Mat) (B : Fin 4 → Site NF → Mat) (x : Site NF) :
    (Ds1L a1 (cfgX X) (fun μ y => (B μ y)ᴴ) x)ᴴ = Ds1L a1 (cfgX (Xs S X)) B x := by
  rw [Ds1L_cfgX, Ds1L_cfgX]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_sub, Ad_expU_conj, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_conjTranspose, Xs]

lemma regField_Xs {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) : RegField S (Xs S X) α₁ where
  hA i x μ h1 h2 := by simp only [Xs, Matrix.l2_opNorm_conjTranspose]; exact hX.hA i x μ h1 h2
  hdA i x μ ν h1 h2 := by
    simp only [Xs, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    exact hX.hdA i x μ ν h1 h2

/-! ### The forms of the curl and of the divergence at `𝐔` -/

lemma pair1V_tr (B F : Fin 4 → Site NF → Mat) : pair1V S B F = ∑ μ, ∑ x, ((B μ x)ᴴ * F μ x).trace := by
  unfold pair1V
  simp only [inner_emb]

/-- **The form of `D^*_𝐔F`** (`lem:covariance`(i)): `⟨B^*, D^*_𝐔F⟩ = Σ_{μ, ν ≠ μ}⟨D_{𝐔^*,ν}B_μ, F_{νμ}⟩`. -/
lemma pair1V_Ds2 [NeZero N] (X : Fin 4 → Site NF → Mat) (B : Fin 4 → Site NF → Mat)
    (F : Fin 4 → Fin 4 → Site NF → Mat) :
    pair1V S B (Ds2 a1 (cfgX X) F) = ∑ μ, ∑ ν, ∑ x, if ν ≠ μ then
      inner ℂ (emb (N := N) (Dfw 1 (cfgX (Xs S X)) ν (B μ) x)) (emb (N := N) (F ν μ x)) else 0 := by
  rw [pair1V_tr]
  refine sum_congr rfl fun μ _ => ?_
  simp only [Ds2, Matrix.mul_sum, Matrix.trace_sum]
  rw [sum_comm]
  refine sum_congr rfl fun ν _ => ?_
  by_cases h : ν ≠ μ
  · simp only [if_pos h, a1, Complex.ofReal_one]
    rw [trace_Dbw S X ν (fun y => (B μ y)ᴴ) (F ν μ)]
    refine sum_congr rfl fun x _ => ?_
    rw [inner_emb, ← Dfw_conj, Matrix.conjTranspose_conjTranspose]
  · simp only [if_neg h, Matrix.mul_zero, Matrix.trace_zero, sum_const_zero]

/-- **The form of `D_𝐔G`** (`lem:covariance`(i)): `⟨B^*, D_𝐔G⟩ = ⟨D^*_{𝐔^*}B, G⟩`. -/
lemma pair1V_D0 [NeZero N] (X : Fin 4 → Site NF → Mat) (B : Fin 4 → Site NF → Mat) (G : Site NF → Mat) :
    pair1V S B (D0L a1 (cfgX X) G) = inner ℂ (vL S (Ds1L a1 (cfgX (Xs S X)) B)) (vL S G) := by
  rw [pair1V_tr, inner_vL]
  have h : ∀ μ, ∑ x, ((B μ x)ᴴ * D0L a1 (cfgX X) G μ x).trace =
      ∑ x, (G x * Dbw 1 (cfgX X) μ (fun y => (B μ y)ᴴ) x).trace := by
    intro μ
    rw [trace_Dbw S X μ G (fun y => (B μ y)ᴴ)]
    refine sum_congr rfl fun x _ => ?_
    rw [Matrix.trace_mul_comm]
    simp only [D0L_apply, D0, a1, Complex.ofReal_one]
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, Matrix.trace_mul_comm, inner_emb, ← Ds1L_conj,
    Matrix.conjTranspose_conjTranspose]
  simp only [Ds1L_apply, Ds1, a1, Complex.ofReal_one]

/-! ### A weighted perturbation of a sum of inner products -/

omit S in
/-- **A weighted perturbation of a sum of inner products**: with positive weights `w`,
`|ReΣ⟨u + e₁, v + e₂⟩ - ReΣ⟨u, v⟩| ≤ ‖wu‖‖w⁻¹e₂‖ + ‖we₁‖‖w⁻¹v‖ + ‖we₁‖‖w⁻¹e₂‖` (the inequality of Cauchy and
Schwarz after `⟨a, b⟩ = ⟨wa, w⁻¹b⟩`). -/
lemma sum_inner_pert_w {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (u e1 v e2 : ι → V) :
    |(∑ i, inner ℂ (u i + e1 i) (v i + e2 i)).re - (∑ i, inner ℂ (u i) (v i)).re| ≤
      √(∑ i, (w i * ‖u i‖) ^ 2) * √(∑ i, ((w i)⁻¹ * ‖e2 i‖) ^ 2) +
        √(∑ i, (w i * ‖e1 i‖) ^ 2) * √(∑ i, ((w i)⁻¹ * ‖v i‖) ^ 2) +
          √(∑ i, (w i * ‖e1 i‖) ^ 2) * √(∑ i, ((w i)⁻¹ * ‖e2 i‖) ^ 2) := by
  have hpt : ∀ i, |(inner ℂ (u i + e1 i) (v i + e2 i)).re - (inner ℂ (u i) (v i)).re| ≤
      (w i * ‖u i‖) * ((w i)⁻¹ * ‖e2 i‖) + (w i * ‖e1 i‖) * ((w i)⁻¹ * ‖v i‖) +
        (w i * ‖e1 i‖) * ((w i)⁻¹ * ‖e2 i‖) := by
    intro i
    have hw0 : w i * (w i)⁻¹ = 1 := mul_inv_cancel₀ (hw i).ne'
    refine (inner_pert (u i) (e1 i) (v i) (e2 i)).trans (le_of_eq ?_)
    have e : ∀ a b : ℝ, w i * a * ((w i)⁻¹ * b) = a * b := fun a b => by
      rw [show w i * a * ((w i)⁻¹ * b) = (w i * (w i)⁻¹) * (a * b) by ring, hw0, one_mul]
    rw [e, e, e]
  rw [Complex.re_sum, Complex.re_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => hpt i).trans ?_)
  rw [sum_add_distrib, sum_add_distrib]
  gcongr
  · exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  · exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  · exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-! ### Pointwise bounds -/

lemma regField_X0 : RegField (N := N) S (X0 S) (0 : ℝ) where
  hA i x μ _ _ := by simp [X0]
  hdA i x μ ν _ _ := by simp [X0]

lemma Xs_X0 : Xs (N := N) S (X0 S) = X0 S := by
  funext μ x; simp [Xs, X0]

/-- **The field on a bond, by the scale of its final point**: `|X_ν(x)| ≤ α₁La_{j(x+e_ν)}^{-1}` (`L < RM`). -/
lemma X_le_end (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (ν : Fin 4) (x : Site NF) :
    ‖X ν x‖ ≤ α₁ * S.L * ((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  set i := min (jj x) (jj (x + unit NF ν))
  have h1 := hX.hA i x ν (S.toDomSeq.Ω_anti (min_le_left _ _) (S.toDomSeq.mem_sc x))
    (S.toDomSeq.Ω_anti (min_le_right _ _) (S.toDomSeq.mem_sc (x + unit NF ν)))
  have hsc : jj (x + unit NF ν) ≤ jj x + 1 := (PartitionUnity.sc_unit S hRML x ν).1
  have h2 : ((S.L : ℝ) ^ i)⁻¹ ≤ S.L * ((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [show (S.L : ℝ) * (S.L : ℝ) ^ i = (S.L : ℝ) ^ (i + 1) by ring]
    exact pow_le_pow_right₀ hL1 (by simp only [i]; omega)
  calc ‖X ν x‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹ := h1
    _ ≤ α₁ * (S.L * ((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹) := mul_le_mul_of_nonneg_left h2 hα0
    _ = _ := by ring

/-- `e^{|φ(x + e_ν) - φ(x)|} ≤ 2` for `16Lδ ≤ 1`. -/
lemma exp_bond_le (hRML : (S.L : ℝ) < RMS) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (ν : Fin 4) (x : Site NF) :
    Real.exp |ph (x + unit NF ν) - ph x| ≤ 2 := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := Nat.one_le_iff_ne_zero.2 (by have := S.one_le_R; have := S.Lpos; positivity)
  have h1 := hph (x + unit NF ν) x
  have h2 := (S.wdist_unit_le_sc hRM1 x ν).2
  rw [S.dF_comm] at h1
  have hr : ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit NF ν))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have h3 : |ph (x + unit NF ν) - ph x| ≤ 1 / 16 := by
    calc |ph (x + unit NF ν) - ph x| ≤ δ * S.dF x (x + unit NF ν) := h1
      _ ≤ δ * (S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit NF ν))⁻¹) := mul_le_mul_of_nonneg_left h2 hδ
      _ ≤ δ * (S.L * 1) := by gcongr
      _ ≤ 1 / 16 := by nlinarith
  calc Real.exp |ph (x + unit NF ν) - ph x| ≤ Real.exp (1 / 16) := Real.exp_le_exp.2 h3
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by have := Real.log_two_gt_d9; linarith)
    _ = 2 := Real.exp_log (by norm_num)

/-- **The difference of a conjugated form at the trivial configuration**:
`|∂_ν(e^φu)(x)| ≤ e^{φ(x)}(|u(x + e_ν) - u(x)| + 2δLa_{j(x+e_ν)}^{-1}|u(x + e_ν)|)` (`hs_Dfw_conj_le` at `id`). -/
lemma dconj_le (hRML : (S.L : ℝ) < RMS) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (u : Site NF → Mat) (ν : Fin 4) (x : Site NF) :
    ‖emb (N := N) (Dfw 1 (cfgX (X0 S)) ν (fun y => ((Real.exp (ph y) : ℝ) : ℂ) • u y) x)‖ ≤
      Real.exp (ph x) * (‖emb (N := N) (u (x + unit NF ν) - u x)‖ +
        2 * δ * S.L * (((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ * ‖emb (N := N) (u (x + unit NF ν))‖)) := by
  have h := hs_Dfw_conj_le S hRML (regField_X0 S) le_rfl (by norm_num) hδ hδL ph hph (fun y => (u y)ᴴ) ν x
  have e : (fun y => (((Real.exp (ph y) : ℝ) : ℂ) • (u y)ᴴ)ᴴ) = fun y => ((Real.exp (ph y) : ℝ) : ℂ) • u y := by
    funext y
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_ofReal]
  rw [e, ← Matrix.conjTranspose_sub, hs_conjTranspose, hs_conjTranspose] at h
  simp only [mul_zero, zero_mul, add_zero] at h
  rw [norm_emb, norm_emb, norm_emb]
  have hsN := Real.sqrt_nonneg (N : ℝ)
  calc √N * hs (Dfw 1 (cfgX (X0 S)) ν (fun y => ((Real.exp (ph y) : ℝ) : ℂ) • u y) x)
      ≤ √N * (Real.exp (ph x) * (hs (u (x + unit NF ν) - u x) +
        2 * δ * S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit NF ν))⁻¹ * hs (u (x + unit NF ν)))) :=
        mul_le_mul_of_nonneg_left h hsN
    _ = _ := by ring

/-- **The covariant part of a conjugated difference**: `|(D_{𝐔,ν} - ∂_ν)(e^φu)(x)| ≤
2e^{φ(x)}·6α₁La_{j(x+e_ν)}^{-1}|u(x + e_ν)|`. -/
lemma dpert_le (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (u : Site NF → Mat) (ν : Fin 4) (x : Site NF) :
    ‖emb (N := N) (Dfw 1 (cfgX X) ν (fun y => ((Real.exp (ph y) : ℝ) : ℂ) • u y) x -
        Dfw 1 (cfgX (X0 S)) ν (fun y => ((Real.exp (ph y) : ℝ) : ℂ) • u y) x)‖ ≤
      Real.exp (ph x) * (12 * (α₁ * S.L) * (((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ *
        ‖emb (N := N) (u (x + unit NF ν))‖)) := by
  rw [Dfw_sub_triv, norm_emb, norm_emb]
  have hXs : ‖X ν x‖ ≤ 1 / 32 := (X_le_one S hX hα0 ν x).trans hα
  have e : Ad (expU (Complex.I • X ν x)) (((Real.exp (ph (x + unit NF ν)) : ℝ) : ℂ) • u (x + unit NF ν)) -
      ((Real.exp (ph (x + unit NF ν)) : ℝ) : ℂ) • u (x + unit NF ν) =
      ((Real.exp (ph (x + unit NF ν)) : ℝ) : ℂ) •
        (Ad (expU (Complex.I • X ν x)) (u (x + unit NF ν)) - u (x + unit NF ν)) := by
    rw [Ad_smul, smul_sub]
  simp only [e]
  rw [RegularAverages.hs_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 := hs_Ad_exp_sub_le hXs (u (x + unit NF ν))
  have h2 := X_le_end S hRML hX hα0 ν x
  have h3 := exp_bond_le S hRML hδ hδL ph hph ν x
  have hE : Real.exp (ph (x + unit NF ν)) ≤ 2 * Real.exp (ph x) := by
    have : ph (x + unit NF ν) ≤ ph x + |ph (x + unit NF ν) - ph x| := by
      have := le_abs_self (ph (x + unit NF ν) - ph x); linarith
    calc Real.exp (ph (x + unit NF ν)) ≤ Real.exp (ph x + |ph (x + unit NF ν) - ph x|) := Real.exp_le_exp.2 this
      _ = Real.exp (ph x) * Real.exp |ph (x + unit NF ν) - ph x| := Real.exp_add _ _
      _ ≤ Real.exp (ph x) * 2 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = 2 * Real.exp (ph x) := by ring
  have hu := hs_nonneg (N := N) (u (x + unit NF ν))
  have hsN := Real.sqrt_nonneg (N : ℝ)
  have hr : 0 ≤ ((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ := by positivity
  have hL0 : (0 : ℝ) ≤ S.L := by positivity
  calc √N * (Real.exp (ph (x + unit NF ν)) *
        hs (Ad (expU (Complex.I • X ν x)) (u (x + unit NF ν)) - u (x + unit NF ν)))
      ≤ √N * ((2 * Real.exp (ph x)) * (6 * (α₁ * S.L * ((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹) *
          hs (u (x + unit NF ν)))) := by
        have h4 : hs (Ad (expU (Complex.I • X ν x)) (u (x + unit NF ν)) - u (x + unit NF ν)) ≤
            6 * (α₁ * S.L * ((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹) * hs (u (x + unit NF ν)) :=
          h1.trans (by gcongr)
        exact mul_le_mul_of_nonneg_left (mul_le_mul hE h4 (hs_nonneg _) (by positivity)) hsN
    _ = _ := by ring

/-! ### The curl form at `𝐔` and at `id` -/

lemma sum_gq (A : Fin 4 → Site NF → Mat) :
    ∑ μ, ∑ ν, ∑ x, ‖emb (N := N) (A μ (x + unit NF ν) - A μ x)‖ ^ 2 = gradNorm S A := by
  unfold gradNorm gbond
  refine sum_congr rfl fun μ _ => ?_
  rw [sum_comm]
  simp only [emb_sub']

lemma sum_mq (A : Fin 4 → Site NF → Mat) :
    ∑ μ, ∑ ν, ∑ x, (((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ * ‖emb (N := N) (A μ (x + unit NF ν))‖) ^ 2 =
      4 * wnorm S A := by
  have h1 : ∀ μ ν, ∑ x, (((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ * ‖emb (N := N) (A μ (x + unit NF ν))‖) ^ 2 =
      ∑ x, (((S.L : ℝ) ^ jj x)⁻¹ * ‖emb (N := N) (A μ x)‖) ^ 2 := fun μ ν =>
    sum_shift_site S (fun x => (((S.L : ℝ) ^ jj x)⁻¹ * ‖emb (N := N) (A μ x)‖) ^ 2) (unit NF ν)
  simp only [h1, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold wnorm
  rw [← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun μ _ => ?_
  push_cast
  rw [mul_pow, inv_pow]

omit S in
/-- The algebra of the comparison of the curl forms. -/
lemma curl_alg {Sa Sb Sc Sd a0 G W β : ℝ} (hSa : 0 ≤ Sa) (hSb : 0 ≤ Sb) (hSc : 0 ≤ Sc) (hSd : 0 ≤ Sd)
    (hG : 0 ≤ G) (hW : 0 ≤ W) (hβ : 0 ≤ β) (ha : Sa ≤ a0) (hb : Sb ≤ 4 * a0) (hc : Sc ≤ 576 * β ^ 2 * W)
    (hd : Sd ≤ 2304 * β ^ 2 * W) (ha0 : a0 ≤ 2 * G + W / 8) :
    √Sa * √Sd + √Sc * √Sb + √Sc * √Sd ≤ (96 * β + 1152 * β ^ 2) * (G + W) := by
  have ha00 : 0 ≤ a0 := hSa.trans ha
  have h1 : √Sa ≤ √a0 := Real.sqrt_le_sqrt ha
  have h2 : √Sb ≤ 2 * √a0 := by
    calc √Sb ≤ √(4 * a0) := Real.sqrt_le_sqrt hb
      _ = 2 * √a0 := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h3 : √Sc ≤ 24 * β * √W := by
    calc √Sc ≤ √((24 * β) ^ 2 * W) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 24 * β * √W := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h4 : √Sd ≤ 48 * β * √W := by
    calc √Sd ≤ √((48 * β) ^ 2 * W) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 48 * β * √W := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hsa := Real.sqrt_nonneg Sa
  have hsb := Real.sqrt_nonneg Sb
  have hsc := Real.sqrt_nonneg Sc
  have hsd := Real.sqrt_nonneg Sd
  have hsW := Real.sqrt_nonneg W
  have hs0 := Real.sqrt_nonneg a0
  have e1 : √Sa * √Sd ≤ √a0 * (48 * β * √W) := mul_le_mul h1 h4 hsd hs0
  have e2 : √Sc * √Sb ≤ 24 * β * √W * (2 * √a0) := mul_le_mul h3 h2 hsb (by positivity)
  have e3 : √Sc * √Sd ≤ 24 * β * √W * (48 * β * √W) := mul_le_mul h3 h4 hsd (by positivity)
  have hWW : √W * √W = W := Real.mul_self_sqrt hW
  have haW : √a0 * √W ≤ G + W := by
    have := Real.sqrt_mul_self ha00
    nlinarith [sq_nonneg (√a0 - √W), Real.mul_self_sqrt ha00]
  have e4 : β * (√a0 * √W) ≤ β * (G + W) := mul_le_mul_of_nonneg_left haW hβ
  have e5 : β ^ 2 * W ≤ β ^ 2 * (G + W) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg β)
  nlinarith

/-- **The comparison of the curl forms** (step (1) of "The complex field", the curl):
`|Re⟨(e^φA)^*, D^*_𝐔D_𝐔(e^{-φ}A)⟩ - Re⟨(e^φA)^*, ∂^*∂(e^{-φ}A)⟩| ≤ (96α₁L + 1152α₁²L²)N(A)²`. -/
theorem curl_comp (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') [NeZero N] (A : Fin 4 → Site NF → Mat) :
    |(pair1V S (expA S ph A) (Ds2 a1 (cfgX X) (D1 a1 (cfgX X) (expA S (fun x => -ph x) A)))).re -
      (pair1V S (expA S ph A) (Ds2 a1 (cfgX (X0 S)) (D1 a1 (cfgX (X0 S)) (expA S (fun x => -ph x) A)))).re| ≤
      (96 * (α₁ * S.L) + 1152 * (α₁ * S.L) ^ 2) * (gradNorm S A + wnorm S A) := by
  have hL0 : (0 : ℝ) ≤ S.L := by positivity
  have hph' : ∀ x x', |(fun x => -ph x) x - (fun x => -ph x) x'| ≤ δ * S.dF x x' := fun x x' => by
    simp only; rw [show -ph x - -ph x' = -(ph x - ph x') by ring, abs_neg]; exact hph x x'
  set B := expA S ph A
  set C := expA S (fun x => -ph x) A
  set Y := Xs S X
  have hY := regField_Xs S hX
  set g : Fin 4 → Fin 4 → Site NF → ℝ := fun μ ν x => ‖emb (N := N) (A μ (x + unit NF ν) - A μ x)‖
  set m : Fin 4 → Fin 4 → Site NF → ℝ := fun μ ν x =>
    ((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ * ‖emb (N := N) (A μ (x + unit NF ν))‖
  have hg0 : ∀ μ ν x, 0 ≤ g μ ν x := fun _ _ _ => norm_nonneg _
  have hm0 : ∀ μ ν x, 0 ≤ m μ ν x := fun _ _ _ => by positivity
  have hsg := sum_gq S A
  have hsm := sum_mq S A
  -- the forms as sums over `(μ, ν, x)`
  have hif : ∀ (Z : Fin 4 → Site NF → Mat) (μ ν : Fin 4) (x : Site NF) (a : VS N 1),
      (if ν ≠ μ then inner ℂ a (emb (N := N) (D1 a1 (cfgX Z) C ν μ x)) else 0) =
        inner ℂ a (emb (N := N) (Dfw 1 (cfgX Z) ν (C μ) x - Dfw 1 (cfgX Z) μ (C ν) x)) := by
    intro Z μ ν x a
    by_cases h : ν ≠ μ
    · rw [if_pos h]; simp only [D1, a1, Complex.ofReal_one]
    · push_neg at h; subst h
      simp only [ne_eq, not_true_eq_false, if_false, sub_self]
      rw [show emb (N := N) (0 : Mat) = 0 from map_zero embL, inner_zero_right]
  rw [pair1V_Ds2, pair1V_Ds2, Xs_X0]
  simp only [hif]
  set u : Fin 4 × Fin 4 × Site NF → VS N 1 := fun p => emb (N := N) (Dfw 1 (cfgX (X0 S)) p.2.1 (B p.1) p.2.2)
  set e1 : Fin 4 × Fin 4 × Site NF → VS N 1 := fun p =>
    emb (N := N) (Dfw 1 (cfgX Y) p.2.1 (B p.1) p.2.2 - Dfw 1 (cfgX (X0 S)) p.2.1 (B p.1) p.2.2)
  set v : Fin 4 × Fin 4 × Site NF → VS N 1 := fun p =>
    emb (N := N) (Dfw 1 (cfgX (X0 S)) p.2.1 (C p.1) p.2.2 - Dfw 1 (cfgX (X0 S)) p.1 (C p.2.1) p.2.2)
  set e2 : Fin 4 × Fin 4 × Site NF → VS N 1 := fun p =>
    emb (N := N) (Dfw 1 (cfgX X) p.2.1 (C p.1) p.2.2 - Dfw 1 (cfgX (X0 S)) p.2.1 (C p.1) p.2.2) -
      emb (N := N) (Dfw 1 (cfgX X) p.1 (C p.2.1) p.2.2 - Dfw 1 (cfgX (X0 S)) p.1 (C p.2.1) p.2.2)
  have eU : ∑ μ, ∑ ν, ∑ x, inner ℂ (emb (N := N) (Dfw 1 (cfgX Y) ν (B μ) x))
      (emb (N := N) (Dfw 1 (cfgX X) ν (C μ) x - Dfw 1 (cfgX X) μ (C ν) x)) =
      ∑ p, inner ℂ (u p + e1 p) (v p + e2 p) := by
    simp only [Fintype.sum_prod_type]
    refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => sum_congr rfl fun x _ => ?_
    simp only [u, e1, v, e2, ← emb_add', ← emb_sub']
    congr 2 <;> abel
  have e0 : ∑ μ, ∑ ν, ∑ x, inner ℂ (emb (N := N) (Dfw 1 (cfgX (X0 S)) ν (B μ) x))
      (emb (N := N) (Dfw 1 (cfgX (X0 S)) ν (C μ) x - Dfw 1 (cfgX (X0 S)) μ (C ν) x)) =
      ∑ p, inner ℂ (u p) (v p) := by
    simp only [Fintype.sum_prod_type]
    rfl
  rw [eU, e0]
  set w : Fin 4 × Fin 4 × Site NF → ℝ := fun p => Real.exp (-ph p.2.2)
  have hw : ∀ p, 0 < w p := fun p => Real.exp_pos _
  have hwi : ∀ p, (w p)⁻¹ = Real.exp (ph p.2.2) := fun p => by simp only [w]; rw [Real.exp_neg, inv_inv]
  refine (sum_inner_pert_w w hw u e1 v e2).trans ?_
  -- the four sums
  have pa : ∀ μ ν x, w (μ, ν, x) * ‖u (μ, ν, x)‖ ≤ g μ ν x + 2 * δ * S.L * m μ ν x := by
    intro μ ν x
    have h := dconj_le S hRML hδ hδL ph hph (A μ) ν x
    have e : w (μ, ν, x) * Real.exp (ph x) = 1 := by simp only [w]; rw [← Real.exp_add]; simp
    calc w (μ, ν, x) * ‖u (μ, ν, x)‖ ≤ w (μ, ν, x) * (Real.exp (ph x) * (g μ ν x + 2 * δ * S.L * m μ ν x)) :=
          mul_le_mul_of_nonneg_left h (hw _).le
      _ = _ := by rw [← mul_assoc, e, one_mul]
  have pa' : ∀ μ ν x, Real.exp (ph x) *
      ‖emb (N := N) (Dfw 1 (cfgX (X0 S)) ν (C μ) x)‖ ≤ g μ ν x + 2 * δ * S.L * m μ ν x := by
    intro μ ν x
    have h := dconj_le S hRML hδ hδL (fun x => -ph x) hph' (A μ) ν x
    have e : Real.exp (ph x) * Real.exp (-ph x) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (ph x) * ‖emb (N := N) (Dfw 1 (cfgX (X0 S)) ν (C μ) x)‖
        ≤ Real.exp (ph x) * (Real.exp (-ph x) * (g μ ν x + 2 * δ * S.L * m μ ν x)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, e, one_mul]
  have pc : ∀ μ ν x, w (μ, ν, x) * ‖e1 (μ, ν, x)‖ ≤ 12 * (α₁ * S.L) * m μ ν x := by
    intro μ ν x
    have h := dpert_le S hRML hY hα0 hα hδ hδL ph hph (A μ) ν x
    have e : w (μ, ν, x) * Real.exp (ph x) = 1 := by simp only [w]; rw [← Real.exp_add]; simp
    calc w (μ, ν, x) * ‖e1 (μ, ν, x)‖ ≤ w (μ, ν, x) * (Real.exp (ph x) * (12 * (α₁ * S.L) * m μ ν x)) :=
          mul_le_mul_of_nonneg_left h (hw _).le
      _ = _ := by rw [← mul_assoc, e, one_mul]
  have pc' : ∀ μ ν x, Real.exp (ph x) * ‖emb (N := N) (Dfw 1 (cfgX X) ν (C μ) x -
      Dfw 1 (cfgX (X0 S)) ν (C μ) x)‖ ≤ 12 * (α₁ * S.L) * m μ ν x := by
    intro μ ν x
    have h := dpert_le S hRML hX hα0 hα hδ hδL (fun x => -ph x) hph' (A μ) ν x
    have e : Real.exp (ph x) * Real.exp (-ph x) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (ph x) * ‖emb (N := N) (Dfw 1 (cfgX X) ν (C μ) x - Dfw 1 (cfgX (X0 S)) ν (C μ) x)‖
        ≤ Real.exp (ph x) * (Real.exp (-ph x) * (12 * (α₁ * S.L) * m μ ν x)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, e, one_mul]
  have hδ2 : 2 * δ * S.L ≤ 1 / 8 := by nlinarith
  set G := gradNorm S A
  set Wn := wnorm S A
  set a0 := 2 * G + 32 * (δ * S.L) ^ 2 * Wn
  have hsumA : ∑ μ, ∑ ν, ∑ x, (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2 ≤ a0 := by
    have hpt : ∀ μ ν x, (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2 ≤ 2 * g μ ν x ^ 2 + 8 * (δ * S.L) ^ 2 * m μ ν x ^ 2 :=
      fun μ ν x => by nlinarith [sq_nonneg (g μ ν x - 2 * δ * S.L * m μ ν x)]
    calc _ ≤ ∑ μ, ∑ ν, ∑ x, (2 * g μ ν x ^ 2 + 8 * (δ * S.L) ^ 2 * m μ ν x ^ 2) :=
          sum_le_sum fun μ _ => sum_le_sum fun ν _ => sum_le_sum fun x _ => hpt μ ν x
      _ = 2 * G + 8 * (δ * S.L) ^ 2 * (4 * Wn) := by
          simp only [sum_add_distrib, ← mul_sum]
          rw [← hsg, ← hsm]
      _ = a0 := by ring
  have hSa : ∑ p, (w p * ‖u p‖) ^ 2 ≤ a0 := by
    simp only [Fintype.sum_prod_type]
    refine le_trans (sum_le_sum fun μ _ => sum_le_sum fun ν _ => sum_le_sum fun x _ =>
      pow_le_pow_left₀ (mul_nonneg (hw _).le (norm_nonneg _)) (pa μ ν x) 2) hsumA
  have hSb : ∑ p, ((w p)⁻¹ * ‖v p‖) ^ 2 ≤ 4 * a0 := by
    simp only [Fintype.sum_prod_type, hwi]
    have hpt : ∀ μ ν x, (Real.exp (ph x) * ‖v (μ, ν, x)‖) ^ 2 ≤
        2 * (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2 + 2 * (g ν μ x + 2 * δ * S.L * m ν μ x) ^ 2 := by
      intro μ ν x
      have h1 : Real.exp (ph x) * ‖v (μ, ν, x)‖ ≤
          (g μ ν x + 2 * δ * S.L * m μ ν x) + (g ν μ x + 2 * δ * S.L * m ν μ x) := by
        simp only [v, emb_sub']
        refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le).trans ?_
        rw [mul_add]
        exact add_le_add (pa' μ ν x) (pa' ν μ x)
      have h0 : 0 ≤ Real.exp (ph x) * ‖v (μ, ν, x)‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
      nlinarith [sq_nonneg ((g μ ν x + 2 * δ * S.L * m μ ν x) - (g ν μ x + 2 * δ * S.L * m ν μ x))]
    have hswap : ∑ μ, ∑ ν, ∑ x, (g ν μ x + 2 * δ * S.L * m ν μ x) ^ 2 =
        ∑ μ, ∑ ν, ∑ x, (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2 := sum_comm
    calc _ ≤ ∑ μ, ∑ ν, ∑ x, (2 * (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2 +
          2 * (g ν μ x + 2 * δ * S.L * m ν μ x) ^ 2) :=
          sum_le_sum fun μ _ => sum_le_sum fun ν _ => sum_le_sum fun x _ => hpt μ ν x
      _ = 4 * ∑ μ, ∑ ν, ∑ x, (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2 := by
          simp only [sum_add_distrib, ← mul_sum]; rw [hswap]; ring
      _ ≤ 4 * a0 := by linarith
  have hSc : ∑ p, (w p * ‖e1 p‖) ^ 2 ≤ 576 * (α₁ * S.L) ^ 2 * Wn := by
    simp only [Fintype.sum_prod_type]
    calc _ ≤ ∑ μ, ∑ ν, ∑ x, 144 * (α₁ * S.L) ^ 2 * m μ ν x ^ 2 :=
          sum_le_sum fun μ _ => sum_le_sum fun ν _ => sum_le_sum fun x _ => by
            have := pow_le_pow_left₀ (mul_nonneg (hw _).le (norm_nonneg _)) (pc μ ν x) 2
            linarith [show (12 * (α₁ * S.L) * m μ ν x) ^ 2 = 144 * (α₁ * S.L) ^ 2 * m μ ν x ^ 2 by ring]
      _ = 144 * (α₁ * S.L) ^ 2 * (4 * Wn) := by simp only [← mul_sum]; rw [hsm]
      _ = _ := by ring
  have hSd : ∑ p, ((w p)⁻¹ * ‖e2 p‖) ^ 2 ≤ 2304 * (α₁ * S.L) ^ 2 * Wn := by
    simp only [Fintype.sum_prod_type, hwi]
    have hpt : ∀ μ ν x, (Real.exp (ph x) * ‖e2 (μ, ν, x)‖) ^ 2 ≤
        288 * (α₁ * S.L) ^ 2 * m μ ν x ^ 2 + 288 * (α₁ * S.L) ^ 2 * m ν μ x ^ 2 := by
      intro μ ν x
      have h1 : Real.exp (ph x) * ‖e2 (μ, ν, x)‖ ≤ 12 * (α₁ * S.L) * m μ ν x + 12 * (α₁ * S.L) * m ν μ x := by
        simp only [e2]
        refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le).trans ?_
        rw [mul_add]
        exact add_le_add (pc' μ ν x) (pc' ν μ x)
      have h0 : 0 ≤ Real.exp (ph x) * ‖e2 (μ, ν, x)‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
      nlinarith [sq_nonneg (12 * (α₁ * S.L) * m μ ν x - 12 * (α₁ * S.L) * m ν μ x)]
    have hswap : ∑ μ, ∑ ν, ∑ x, m ν μ x ^ 2 = ∑ μ, ∑ ν, ∑ x, m μ ν x ^ 2 := sum_comm
    calc _ ≤ ∑ μ, ∑ ν, ∑ x, (288 * (α₁ * S.L) ^ 2 * m μ ν x ^ 2 + 288 * (α₁ * S.L) ^ 2 * m ν μ x ^ 2) :=
          sum_le_sum fun μ _ => sum_le_sum fun ν _ => sum_le_sum fun x _ => hpt μ ν x
      _ = 288 * (α₁ * S.L) ^ 2 * (4 * Wn) + 288 * (α₁ * S.L) ^ 2 * (4 * Wn) := by
          simp only [sum_add_distrib, ← mul_sum]; rw [hswap, hsm]
      _ = _ := by ring
  have hG := gradNorm_nonneg' S A
  have hW := wnorm_nonneg' S A
  have ha0 : a0 ≤ 2 * G + Wn / 8 := by
    have h1 : δ * S.L ≤ 1 / 16 := by linarith
    have h2 : 0 ≤ δ * S.L := mul_nonneg hδ hL0
    have : 32 * (δ * S.L) ^ 2 ≤ 1 / 8 := by nlinarith
    nlinarith
  exact curl_alg (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _) hG hW (by positivity)
    hSa hSb hSc hSd ha0

/-! ### The divergence form at `𝐔` and at `id` -/

lemma sum_shift_sub {β : Type*} [AddCommMonoid β] (F : Site NF → β) (c : Site NF) :
    ∑ x, F (x - c) = ∑ x, F x := by
  have := sum_shift_site S (fun x => F (x - c)) c
  simp only [add_sub_cancel_right] at this
  exact this.symm

omit S in
lemma sq_sum4_le (t : Fin 4 → ℝ) : (∑ μ, t μ) ^ 2 ≤ 4 * ∑ μ, t μ ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 4))) (f := t)
  simp only [card_univ, Fintype.card_fin] at h
  exact_mod_cast h

omit S in
/-- The algebra of the comparison of the divergence forms. -/
lemma div_alg {Sa Sb Sc Sd a0 G W β : ℝ} (hSa : 0 ≤ Sa) (hSb : 0 ≤ Sb) (hSc : 0 ≤ Sc) (hSd : 0 ≤ Sd)
    (hG : 0 ≤ G) (hW : 0 ≤ W) (hβ : 0 ≤ β) (ha : Sa ≤ 16 * a0) (hb : Sb ≤ 16 * a0) (hc : Sc ≤ 576 * β ^ 2 * W)
    (hd : Sd ≤ 576 * β ^ 2 * W) (ha0 : a0 ≤ 2 * G + W / 8) :
    √Sa * √Sd + √Sc * √Sb + √Sc * √Sd ≤ (192 * β + 576 * β ^ 2) * (G + W) := by
  have ha00 : 0 ≤ a0 := by nlinarith
  have h16 : ∀ {T : ℝ}, T ≤ 16 * a0 → √T ≤ 4 * √a0 := fun {T} hT => by
    calc √T ≤ √(4 ^ 2 * a0) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 4 * √a0 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h24 : ∀ {T : ℝ}, T ≤ 576 * β ^ 2 * W → √T ≤ 24 * β * √W := fun {T} hT => by
    calc √T ≤ √((24 * β) ^ 2 * W) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 24 * β * √W := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h1 := h16 ha
  have h2 := h16 hb
  have h3 := h24 hc
  have h4 := h24 hd
  have hsb := Real.sqrt_nonneg Sb
  have hsd := Real.sqrt_nonneg Sd
  have hsW := Real.sqrt_nonneg W
  have hs0 := Real.sqrt_nonneg a0
  have e1 : √Sa * √Sd ≤ 4 * √a0 * (24 * β * √W) := mul_le_mul h1 h4 hsd (by positivity)
  have e2 : √Sc * √Sb ≤ 24 * β * √W * (4 * √a0) := mul_le_mul h3 h2 hsb (by positivity)
  have e3 : √Sc * √Sd ≤ 24 * β * √W * (24 * β * √W) := mul_le_mul h3 h4 hsd (by positivity)
  have hWW : √W * √W = W := Real.mul_self_sqrt hW
  have haW : √a0 * √W ≤ G + W := by
    nlinarith [sq_nonneg (√a0 - √W), Real.mul_self_sqrt ha00]
  have e4 : β * (√a0 * √W) ≤ β * (G + W) := mul_le_mul_of_nonneg_left haW hβ
  have e5 : β ^ 2 * W ≤ β ^ 2 * (G + W) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg β)
  nlinarith

/-- The divergence of a conjugated form at `id`, weighted: `e^{-φ(x)}|∂^*(e^φu)(x)| ≤
2Σ_μ(|∂_μu_μ(x - e_μ)| + 2δLa^{-1}|u_μ(x)|)`. -/
lemma dsconj_le (hRML : (S.L : ℝ) < RMS) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (A : Fin 4 → Site NF → Mat) (x : Site NF) :
    Real.exp (-ph x) * ‖emb (N := N) (Ds1L a1 (cfgX (X0 S)) (expA S ph A) x)‖ ≤
      ∑ μ, 2 * (‖emb (N := N) (A μ (x - unit NF μ + unit NF μ) - A μ (x - unit NF μ))‖ +
        2 * δ * S.L * (((S.L : ℝ) ^ jj (x - unit NF μ + unit NF μ))⁻¹ *
          ‖emb (N := N) (A μ (x - unit NF μ + unit NF μ))‖)) := by
  have e : Ds1L a1 (cfgX (X0 S)) (expA S ph A) x =
      -∑ μ, Dfw 1 (cfgX (X0 S)) μ (expA S ph A μ) (x - unit NF μ) := by
    rw [Ds1L_triv, ← sum_neg_distrib]
    refine sum_congr rfl fun μ _ => ?_
    rw [Dfw_triv, sub_add_cancel, neg_sub]
  have hneg : emb (N := N) (-∑ μ, Dfw 1 (cfgX (X0 S)) μ (expA S ph A μ) (x - unit NF μ)) =
      -∑ μ, emb (N := N) (Dfw 1 (cfgX (X0 S)) μ (expA S ph A μ) (x - unit NF μ)) := by
    rw [← emb_sum']; exact map_neg embL _
  rw [e, hneg, norm_neg, mul_comm]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun μ _ => ?_
  have h := dconj_le S hRML hδ hδL ph hph (A μ) μ (x - unit NF μ)
  have hb := exp_bond_le S hRML hδ hδL ph hph μ (x - unit NF μ)
  rw [sub_add_cancel] at hb
  have hE : Real.exp (ph (x - unit NF μ)) * Real.exp (-ph x) ≤ 2 := by
    rw [← Real.exp_add]
    refine le_trans (Real.exp_le_exp.2 ?_) hb
    have := neg_abs_le (ph x - ph (x - unit NF μ)); linarith
  set t := ‖emb (N := N) (A μ (x - unit NF μ + unit NF μ) - A μ (x - unit NF μ))‖ +
    2 * δ * S.L * (((S.L : ℝ) ^ jj (x - unit NF μ + unit NF μ))⁻¹ * ‖emb (N := N) (A μ (x - unit NF μ + unit NF μ))‖)
  have ht : 0 ≤ t := by positivity
  calc ‖emb (N := N) (Dfw 1 (cfgX (X0 S)) μ (expA S ph A μ) (x - unit NF μ))‖ * Real.exp (-ph x)
      ≤ Real.exp (ph (x - unit NF μ)) * t * Real.exp (-ph x) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (Real.exp (ph (x - unit NF μ)) * Real.exp (-ph x)) * t := by ring
    _ ≤ 2 * t := mul_le_mul_of_nonneg_right hE ht

/-- The covariant part of the divergence of a conjugated form, weighted:
`e^{-φ(x)}|(D^*_𝐔 - ∂^*)(e^φA)(x)| ≤ Σ_μ12α₁La_{j(x-e_μ)}^{-1}|A_μ(x - e_μ)|`. -/
lemma dspert_le (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (A : Fin 4 → Site NF → Mat) (x : Site NF) :
    Real.exp (-ph x) * ‖emb (N := N) (Ds1L a1 (cfgX X) (expA S ph A) x - Ds1L a1 (cfgX (X0 S)) (expA S ph A) x)‖ ≤
      ∑ μ, 12 * (α₁ * S.L) * (((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹ * ‖emb (N := N) (A μ (x - unit NF μ))‖) := by
  rw [norm_emb]
  have h := dsU_diff_le S hRML hX hα0 hα (expA S ph A) x
  have hsN := Real.sqrt_nonneg (N : ℝ)
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hsN) (Real.exp_pos _).le).trans ?_
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun μ _ => ?_
  have hb := exp_bond_le S hRML hδ hδL ph hph μ (x - unit NF μ)
  rw [sub_add_cancel] at hb
  have hE : Real.exp (ph (x - unit NF μ)) * Real.exp (-ph x) ≤ 2 := by
    rw [← Real.exp_add]
    refine le_trans (Real.exp_le_exp.2 ?_) hb
    have := neg_abs_le (ph x - ph (x - unit NF μ)); linarith
  have e : hs (expA S ph A μ (x - unit NF μ)) = Real.exp (ph (x - unit NF μ)) * hs (A μ (x - unit NF μ)) := by
    simp only [expA]
    rw [RegularAverages.hs_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [e, norm_emb]
  have hA := hs_nonneg (N := N) (A μ (x - unit NF μ))
  have hr : 0 ≤ ((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹ := by positivity
  have hL0 : (0 : ℝ) ≤ S.L := by positivity
  have hc : 0 ≤ 6 * (α₁ * S.L) * ((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹ * hs (A μ (x - unit NF μ)) := by positivity
  calc Real.exp (-ph x) * (√N * (6 * (α₁ * S.L) * ((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹ *
        (Real.exp (ph (x - unit NF μ)) * hs (A μ (x - unit NF μ)))))
      = (Real.exp (ph (x - unit NF μ)) * Real.exp (-ph x)) *
          (√N * (6 * (α₁ * S.L) * ((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹ * hs (A μ (x - unit NF μ)))) := by ring
    _ ≤ 2 * (√N * (6 * (α₁ * S.L) * ((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹ * hs (A μ (x - unit NF μ)))) :=
        mul_le_mul_of_nonneg_right hE (by positivity)
    _ = _ := by ring

/-- **The comparison of the divergence forms** (step (1) of "The complex field", the divergence):
`|Re⟨(e^φA)^*, D_𝐔D^*_𝐔(e^{-φ}A)⟩ - Re⟨(e^φA)^*, ∂∂^*(e^{-φ}A)⟩| ≤ (192α₁L + 576α₁²L²)N(A)²`. -/
theorem div_comp (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') [NeZero N] (A : Fin 4 → Site NF → Mat) :
    |(pair1V S (expA S ph A) (D0L a1 (cfgX X) (Ds1L a1 (cfgX X) (expA S (fun x => -ph x) A)))).re -
      (pair1V S (expA S ph A) (D0L a1 (cfgX (X0 S)) (Ds1L a1 (cfgX (X0 S)) (expA S (fun x => -ph x) A)))).re| ≤
      (192 * (α₁ * S.L) + 576 * (α₁ * S.L) ^ 2) * (gradNorm S A + wnorm S A) := by
  have hL0 : (0 : ℝ) ≤ S.L := by positivity
  have hph' : ∀ x x', |(fun x => -ph x) x - (fun x => -ph x) x'| ≤ δ * S.dF x x' := fun x x' => by
    simp only; rw [show -ph x - -ph x' = -(ph x - ph x') by ring, abs_neg]; exact hph x x'
  set B := expA S ph A
  set C := expA S (fun x => -ph x) A
  set Y := Xs S X
  have hY := regField_Xs S hX
  rw [pair1V_D0, pair1V_D0, Xs_X0, inner_vL, inner_vL]
  set u : Site NF → VS N 1 := fun x => emb (N := N) (Ds1L a1 (cfgX (X0 S)) B x)
  set e1 : Site NF → VS N 1 := fun x => emb (N := N) (Ds1L a1 (cfgX Y) B x - Ds1L a1 (cfgX (X0 S)) B x)
  set v : Site NF → VS N 1 := fun x => emb (N := N) (Ds1L a1 (cfgX (X0 S)) C x)
  set e2 : Site NF → VS N 1 := fun x => emb (N := N) (Ds1L a1 (cfgX X) C x - Ds1L a1 (cfgX (X0 S)) C x)
  have eU : ∑ x, inner ℂ (emb (N := N) (Ds1L a1 (cfgX Y) B x)) (emb (N := N) (Ds1L a1 (cfgX X) C x)) =
      ∑ x, inner ℂ (u x + e1 x) (v x + e2 x) := by
    refine sum_congr rfl fun x _ => ?_
    simp only [u, e1, v, e2, ← emb_add', add_sub_cancel]
  rw [eU]
  set w : Site NF → ℝ := fun x => Real.exp (-ph x)
  have hw : ∀ x, 0 < w x := fun x => Real.exp_pos _
  have hwi : ∀ x, (w x)⁻¹ = Real.exp (-(-ph x)) := fun x => by simp only [w]; rw [Real.exp_neg, inv_inv, neg_neg]
  refine (sum_inner_pert_w w hw u e1 v e2).trans ?_
  -- the data of `A`
  set g : Fin 4 → Fin 4 → Site NF → ℝ := fun μ ν x => ‖emb (N := N) (A μ (x + unit NF ν) - A μ x)‖
  set m : Fin 4 → Fin 4 → Site NF → ℝ := fun μ ν x =>
    ((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ * ‖emb (N := N) (A μ (x + unit NF ν))‖
  set m0 : Fin 4 → Site NF → ℝ := fun μ y => ((S.L : ℝ) ^ jj y)⁻¹ * ‖emb (N := N) (A μ y)‖
  have hg0 : ∀ μ ν x, 0 ≤ g μ ν x := fun _ _ _ => norm_nonneg _
  have hm0 : ∀ μ ν x, 0 ≤ m μ ν x := fun _ _ _ => by positivity
  have hsg := sum_gq S A
  have hsm := sum_mq S A
  set G := gradNorm S A
  set Wn := wnorm S A
  have hsm0 : ∑ μ, ∑ y, m0 μ y ^ 2 = Wn := by
    have h := sum_mq S A
    have e : ∀ μ ν, ∑ x, (((S.L : ℝ) ^ jj (x + unit NF ν))⁻¹ * ‖emb (N := N) (A μ (x + unit NF ν))‖) ^ 2 =
        ∑ y, m0 μ y ^ 2 := fun μ ν => sum_shift_site S (fun y => m0 μ y ^ 2) (unit NF ν)
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => e μ ν] at h
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [← mul_sum] at h
    have h' : (4 : ℝ) * ∑ μ, ∑ y, m0 μ y ^ 2 = 4 * Wn := by exact_mod_cast h
    linarith
  set a0 := 2 * G + 32 * (δ * S.L) ^ 2 * Wn
  have hdiag : ∑ μ, ∑ y, (g μ μ y + 2 * δ * S.L * m μ μ y) ^ 2 ≤ a0 := by
    have hpt : ∀ μ ν x, (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2 ≤ 2 * g μ ν x ^ 2 + 8 * (δ * S.L) ^ 2 * m μ ν x ^ 2 :=
      fun μ ν x => by nlinarith [sq_nonneg (g μ ν x - 2 * δ * S.L * m μ ν x)]
    have hfull : ∑ μ, ∑ ν, ∑ x, (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2 ≤ a0 := by
      calc _ ≤ ∑ μ, ∑ ν, ∑ x, (2 * g μ ν x ^ 2 + 8 * (δ * S.L) ^ 2 * m μ ν x ^ 2) :=
            sum_le_sum fun μ _ => sum_le_sum fun ν _ => sum_le_sum fun x _ => hpt μ ν x
        _ = 2 * G + 8 * (δ * S.L) ^ 2 * (4 * Wn) := by
            simp only [sum_add_distrib, ← mul_sum]
            rw [← hsg, ← hsm]
        _ = a0 := by ring
    refine le_trans (sum_le_sum fun μ _ => ?_) hfull
    exact single_le_sum (f := fun ν => ∑ x, (g μ ν x + 2 * δ * S.L * m μ ν x) ^ 2)
      (fun ν _ => sum_nonneg fun x _ => sq_nonneg _) (mem_univ μ)
  -- the four sums
  have hdiv : ∀ (ψ : Site NF → ℝ) (hψ : ∀ x x', |ψ x - ψ x'| ≤ δ * S.dF x x'),
      ∑ x, (Real.exp (-ψ x) * ‖emb (N := N) (Ds1L a1 (cfgX (X0 S)) (expA S ψ A) x)‖) ^ 2 ≤ 16 * a0 := by
    intro ψ hψ
    have hpt : ∀ x, (Real.exp (-ψ x) * ‖emb (N := N) (Ds1L a1 (cfgX (X0 S)) (expA S ψ A) x)‖) ^ 2 ≤
        16 * ∑ μ, (g μ μ (x - unit NF μ) + 2 * δ * S.L * m μ μ (x - unit NF μ)) ^ 2 := by
      intro x
      have h := dsconj_le S hRML hδ hδL ψ hψ A x
      have h0 : 0 ≤ Real.exp (-ψ x) * ‖emb (N := N) (Ds1L a1 (cfgX (X0 S)) (expA S ψ A) x)‖ :=
        mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
      refine (pow_le_pow_left₀ h0 h 2).trans ?_
      refine (sq_sum4_le _).trans (le_of_eq ?_)
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun μ _ => ?_
      simp only [g, m]
      ring
    calc _ ≤ ∑ x, 16 * ∑ μ, (g μ μ (x - unit NF μ) + 2 * δ * S.L * m μ μ (x - unit NF μ)) ^ 2 :=
          sum_le_sum fun x _ => hpt x
      _ = 16 * ∑ μ, ∑ y, (g μ μ y + 2 * δ * S.L * m μ μ y) ^ 2 := by
          rw [← mul_sum]
          refine congrArg (16 * ·) ?_
          rw [sum_comm]
          exact sum_congr rfl fun μ _ =>
            sum_shift_sub S (fun y => (g μ μ y + 2 * δ * S.L * m μ μ y) ^ 2) (unit NF μ)
      _ ≤ 16 * a0 := by linarith
  have hpert : ∀ (Z : Fin 4 → Site NF → Mat) (hZ : RegField S Z α₁) (ψ : Site NF → ℝ)
      (hψ : ∀ x x', |ψ x - ψ x'| ≤ δ * S.dF x x'),
      ∑ x, (Real.exp (-ψ x) * ‖emb (N := N) (Ds1L a1 (cfgX Z) (expA S ψ A) x -
        Ds1L a1 (cfgX (X0 S)) (expA S ψ A) x)‖) ^ 2 ≤ 576 * (α₁ * S.L) ^ 2 * Wn := by
    intro Z hZ ψ hψ
    have hpt : ∀ x, (Real.exp (-ψ x) * ‖emb (N := N) (Ds1L a1 (cfgX Z) (expA S ψ A) x -
        Ds1L a1 (cfgX (X0 S)) (expA S ψ A) x)‖) ^ 2 ≤
        4 * ∑ μ, (12 * (α₁ * S.L)) ^ 2 * m0 μ (x - unit NF μ) ^ 2 := by
      intro x
      have h := dspert_le S hRML hZ hα0 hα hδ hδL ψ hψ A x
      have h0 : 0 ≤ Real.exp (-ψ x) * ‖emb (N := N) (Ds1L a1 (cfgX Z) (expA S ψ A) x -
        Ds1L a1 (cfgX (X0 S)) (expA S ψ A) x)‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
      refine (pow_le_pow_left₀ h0 h 2).trans ?_
      refine (sq_sum4_le _).trans (le_of_eq ?_)
      congr 1
      refine sum_congr rfl fun μ _ => ?_
      simp only [m0]
      ring
    calc _ ≤ ∑ x, 4 * ∑ μ, (12 * (α₁ * S.L)) ^ 2 * m0 μ (x - unit NF μ) ^ 2 := sum_le_sum fun x _ => hpt x
      _ = 4 * (12 * (α₁ * S.L)) ^ 2 * ∑ μ, ∑ y, m0 μ y ^ 2 := by
          rw [← mul_sum, mul_assoc]
          refine congrArg (4 * ·) ?_
          rw [sum_comm, mul_sum]
          refine sum_congr rfl fun μ _ => ?_
          rw [← mul_sum]
          exact congrArg ((12 * (α₁ * S.L)) ^ 2 * ·) (sum_shift_sub S (fun y => m0 μ y ^ 2) (unit NF μ))
      _ = _ := by rw [hsm0]; ring
  have hSa : ∑ x, (w x * ‖u x‖) ^ 2 ≤ 16 * a0 := hdiv ph hph
  have hSb : ∑ x, ((w x)⁻¹ * ‖v x‖) ^ 2 ≤ 16 * a0 := by
    simp only [hwi]; exact hdiv (fun x => -ph x) hph'
  have hSc : ∑ x, (w x * ‖e1 x‖) ^ 2 ≤ 576 * (α₁ * S.L) ^ 2 * Wn := hpert Y hY ph hph
  have hSd : ∑ x, ((w x)⁻¹ * ‖e2 x‖) ^ 2 ≤ 576 * (α₁ * S.L) ^ 2 * Wn := by
    simp only [hwi]; exact hpert X hX (fun x => -ph x) hph'
  have hG := gradNorm_nonneg' S A
  have hW := wnorm_nonneg' S A
  have ha0 : a0 ≤ 2 * G + Wn / 8 := by
    have h1 : δ * S.L ≤ 1 / 16 := by linarith
    have h2 : 0 ≤ δ * S.L := mul_nonneg hδ hL0
    have : 32 * (δ * S.L) ^ 2 ≤ 1 / 8 := by nlinarith
    nlinarith
  exact div_alg (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _) hG hW (by positivity)
    hSa hSb hSc hSd ha0

end SFBounds
end CoreLean

end
