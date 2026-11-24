/-
`lem:sf-vector-decay` of BALABAN_CORE.tex (`ff7468ef0e33`), step (3) of "The complex field", second part: the
projection term `⟨B, D_𝐔P(𝐔)D^*_𝐔C⟩` of `Δ_𝖺(𝐔)` compared with `⟨B, ∂P(id)∂^*C⟩` on the fine lattice (`a₀ = 1`).

* `vL`: a matrix-valued function as a vector of `ℓ²(Site, V)`, `‖vL f‖² = NΣ_x|f(x)|²`.
* `X_le_base`: `|X_ν(x)| ≤ α₁La_{j(x)}^{-1}` for a regular field.
* `dsU_diff_le`, `dsU_diff_L2`: `|(D^*_𝐔 - ∂^*)A(x)| ≤ 6α₁LΣ_μa_{j(x-e_μ)}^{-1}|A_μ(x - e_μ)|` and
  `‖D^*_𝐔A - ∂^*A‖² ≤ 144α₁²L²‖A‖_w²`.
-/
import CoreLean.SFProjDiff

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

/-! ### Functions as vectors of `ℓ²` -/

/-- `vL f = (emb f(x))_x ∈ ℓ²(Site, V)`. -/
def vL (f : Site NF → Mat) : PiLp 2 (fun _ : Site NF => VS N 1) := WithLp.toLp 2 (fun x => emb (f x))

lemma vL_norm_sq (f : Site NF → Mat) : ‖vL S f‖ ^ 2 = ∑ x, ‖emb (N := N) (f x)‖ ^ 2 := by
  unfold vL
  rw [PiLp.norm_sq_eq_of_L2]

lemma vL_norm_sq' (f : Site NF → Mat) : ‖vL S f‖ ^ 2 = N * ∑ x, hs2 (f x) := by
  rw [vL_norm_sq, mul_sum]
  exact sum_congr rfl fun x _ => norm_emb_sq _

lemma vL_add (f g : Site NF → Mat) : vL S (f + g) = vL S f + vL S g := by
  unfold vL
  ext x : 1
  simp only [Pi.add_apply, emb_add', WithLp.ofLp_add, WithLp.ofLp_toLp]

lemma vL_sub (f g : Site NF → Mat) : vL S (f - g) = vL S f - vL S g := by
  unfold vL
  ext x : 1
  simp only [Pi.sub_apply, emb_sub', WithLp.ofLp_sub, WithLp.ofLp_toLp]

lemma inner_vL (f g : Site NF → Mat) :
    inner ℂ (vL S f) (vL S g) = ∑ x, inner ℂ (emb (N := N) (f x)) (emb (N := N) (g x)) := by
  unfold vL
  rw [PiLp.inner_apply]

/-! ### The field on a bond and the backward difference -/

/-- **The field on a bond, by the scale of its initial point**: `|X_ν(x)| ≤ α₁La_{j(x)}^{-1}` (`L < RM`). -/
lemma X_le_base (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (ν : Fin 4) (x : Site NF) : ‖X ν x‖ ≤ α₁ * S.L * ((S.L : ℝ) ^ jj x)⁻¹ := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  set i := min (jj x) (jj (x + unit NF ν))
  have h1 := hX.hA i x ν (S.toDomSeq.Ω_anti (min_le_left _ _) (S.toDomSeq.mem_sc x))
    (S.toDomSeq.Ω_anti (min_le_right _ _) (S.toDomSeq.mem_sc (x + unit NF ν)))
  have hsc : jj x ≤ jj (x + unit NF ν) + 1 := (PartitionUnity.sc_unit S hRML x ν).2
  have h2 : ((S.L : ℝ) ^ i)⁻¹ ≤ S.L * ((S.L : ℝ) ^ jj x)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [show (S.L : ℝ) * (S.L : ℝ) ^ i = (S.L : ℝ) ^ (i + 1) by ring]
    exact pow_le_pow_right₀ hL1 (by simp only [i]; omega)
  calc ‖X ν x‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹ := h1
    _ ≤ α₁ * (S.L * ((S.L : ℝ) ^ jj x)⁻¹) := mul_le_mul_of_nonneg_left h2 hα0
    _ = _ := by ring

/-- `|X_ν(x)| ≤ α₁`. -/
lemma X_le_one {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁) (ν : Fin 4)
    (x : Site NF) : ‖X ν x‖ ≤ α₁ := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  set i := min (jj x) (jj (x + unit NF ν))
  have h1 := hX.hA i x ν (S.toDomSeq.Ω_anti (min_le_left _ _) (S.toDomSeq.mem_sc x))
    (S.toDomSeq.Ω_anti (min_le_right _ _) (S.toDomSeq.mem_sc (x + unit NF ν)))
  have hi : ((S.L : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  calc ‖X ν x‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹ := h1
    _ ≤ α₁ * 1 := mul_le_mul_of_nonneg_left hi hα0
    _ = α₁ := mul_one _

/-- `D^*_𝐔` at `𝐔 = e^{iX}`: `D^*_𝐔A(x) = Σ_μ(Ad_{e^{-iX_μ(x-e_μ)}}A_μ(x - e_μ) - A_μ(x))`. -/
lemma Ds1L_cfgX (X : Fin 4 → Site NF → Mat) (A : Fin 4 → Site NF → Mat) (x : Site NF) :
    Ds1L a1 (cfgX X) A x =
      ∑ μ, (Ad (expU (Complex.I • -X μ (x - unit NF μ))) (A μ (x - unit NF μ)) - A μ x) := by
  simp only [Ds1L_apply, Ds1, Dbw, Config.val, a1, Complex.ofReal_one, inv_one, one_smul, cfgX,
    Bool.false_eq_true, ↓reduceIte, expU_inv, smul_neg]

/-- **The backward differences at `𝐔` and at `id`**: `|(D^*_𝐔 - ∂^*)A(x)| ≤ 6α₁LΣ_μa_{j(x-e_μ)}^{-1}|A_μ(x - e_μ)|`
(`eq:adjoint-lipschitz` on the bond `(x - e_μ, x)`). -/
lemma dsU_diff_le (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) (A : Fin 4 → Site NF → Mat) (x : Site NF) :
    hs (Ds1L a1 (cfgX X) A x - Ds1L a1 (cfgX (X0 S)) A x) ≤
      ∑ μ, 6 * (α₁ * S.L) * ((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹ * hs (A μ (x - unit NF μ)) := by
  rw [Ds1L_cfgX, Ds1L_triv, ← sum_sub_distrib]
  refine (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun μ _ => ?_)
  have hXs : ‖-X μ (x - unit NF μ)‖ ≤ 1 / 32 := by
    rw [norm_neg]; exact (X_le_one S hX hα0 μ _).trans hα
  have h := hs_Ad_exp_sub_le hXs (A μ (x - unit NF μ))
  rw [norm_neg] at h
  have e : Ad (expU (Complex.I • -X μ (x - unit NF μ))) (A μ (x - unit NF μ)) - A μ x -
      (A μ (x - unit NF μ) - A μ x) =
      Ad (expU (Complex.I • -X μ (x - unit NF μ))) (A μ (x - unit NF μ)) - A μ (x - unit NF μ) := by abel
  rw [e]
  refine h.trans ?_
  have hb := X_le_base S hRML hX hα0 μ (x - unit NF μ)
  have := hs_nonneg (N := N) (A μ (x - unit NF μ))
  calc 6 * ‖X μ (x - unit NF μ)‖ * hs (A μ (x - unit NF μ))
      ≤ 6 * (α₁ * S.L * ((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹) * hs (A μ (x - unit NF μ)) := by gcongr
    _ = _ := by ring

/-- **`‖D^*_𝐔A - ∂^*A‖² ≤ 144α₁²L²‖A‖_w²`** (in the norm of `V`). -/
lemma dsU_diff_L2 (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) (A : Fin 4 → Site NF → Mat) :
    ‖vL S (fun x => Ds1L a1 (cfgX X) A x - Ds1L a1 (cfgX (X0 S)) A x)‖ ^ 2 ≤ 144 * (α₁ * S.L) ^ 2 * wnorm S A := by
  set r : Site NF → ℝ := fun y => ((S.L : ℝ) ^ jj y)⁻¹
  rw [vL_norm_sq']
  have hpt : ∀ x, hs2 (Ds1L a1 (cfgX X) A x - Ds1L a1 (cfgX (X0 S)) A x) ≤
      4 * ∑ μ, (6 * (α₁ * S.L)) ^ 2 * (r (x - unit NF μ) ^ 2 * hs2 (A μ (x - unit NF μ))) := by
    intro x
    rw [← hs_sq]
    have h1 := dsU_diff_le S hRML hX hα0 hα A x
    set fμ : Fin 4 → ℝ := fun μ => 6 * (α₁ * S.L) * ((S.L : ℝ) ^ jj (x - unit NF μ))⁻¹ * hs (A μ (x - unit NF μ))
    have h2 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 4))) (f := fμ)
    simp only [card_univ, Fintype.card_fin] at h2
    have h3 : (∑ μ, fμ μ) ^ 2 ≤ 4 * ∑ μ, fμ μ ^ 2 := by exact_mod_cast h2
    refine (pow_le_pow_left₀ (hs_nonneg _) h1 2).trans (h3.trans (le_of_eq ?_))
    congr 1
    refine sum_congr rfl fun μ _ => ?_
    rw [← hs_sq]
    simp only [r]
    ring
  have hshift : ∀ μ, ∑ x, r (x - unit NF μ) ^ 2 * hs2 (A μ (x - unit NF μ)) = ∑ x, r x ^ 2 * hs2 (A μ x) := by
    intro μ
    have := sum_shift_site S (fun x => r (x - unit NF μ) ^ 2 * hs2 (A μ (x - unit NF μ))) (unit NF μ)
    simp only [add_sub_cancel_right] at this
    exact this.symm
  have hw : wnorm S A = N * ∑ μ, ∑ x, r x ^ 2 * hs2 (A μ x) := by
    unfold wnorm
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun μ _ => sum_congr rfl fun x _ => ?_
    rw [norm_emb_sq]
    simp only [r]
    push_cast
    rw [inv_pow]
    ring
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc (N : ℝ) * ∑ x, hs2 (Ds1L a1 (cfgX X) A x - Ds1L a1 (cfgX (X0 S)) A x)
      ≤ N * ∑ x, 4 * ∑ μ, (6 * (α₁ * S.L)) ^ 2 * (r (x - unit NF μ) ^ 2 * hs2 (A μ (x - unit NF μ))) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => hpt x) hN
    _ = 144 * (α₁ * S.L) ^ 2 * (N * ∑ μ, ∑ x, r (x - unit NF μ) ^ 2 * hs2 (A μ (x - unit NF μ))) := by
        rw [sum_comm (f := fun μ x => r (x - unit NF μ) ^ 2 * hs2 (A μ (x - unit NF μ)))]
        simp only [← mul_sum]
        ring
    _ = _ := by simp only [hshift, hw]

/-! ### The test of Schur in `ℓ²` -/

/-- **The test of Schur in `ℓ²`**: row sums `≤ R` and column sums `≤ C` give `Σ_x(Σ_{x'}K(x, x')f(x'))² ≤ RCΣf²`. -/
lemma schur_L2 {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (hK : ∀ x x', 0 ≤ K x x') {R C : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ x, ∑ x', K x x' ≤ R) (hcol : ∀ x', ∑ x, K x x' ≤ C) (f : ι → ℝ) :
    ∑ x, (∑ x', K x x' * f x') ^ 2 ≤ R * C * ∑ x', f x' ^ 2 := by
  have h1 : ∀ x, (∑ x', K x x' * f x') ^ 2 ≤ (∑ x', K x x') * ∑ x', K x x' * f x' ^ 2 := fun x => by
    have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun x' => Real.sqrt (K x x'))
      (fun x' => Real.sqrt (K x x') * f x')
    have e1 : ∀ x', Real.sqrt (K x x') * (Real.sqrt (K x x') * f x') = K x x' * f x' := fun x' => by
      rw [← mul_assoc, Real.mul_self_sqrt (hK x x')]
    have e2 : ∀ x', Real.sqrt (K x x') ^ 2 = K x x' := fun x' => Real.sq_sqrt (hK x x')
    have e3 : ∀ x', (Real.sqrt (K x x') * f x') ^ 2 = K x x' * f x' ^ 2 := fun x' => by rw [mul_pow, e2]
    simp only [e1, e2, e3] at h
    exact h
  calc ∑ x, (∑ x', K x x' * f x') ^ 2 ≤ ∑ x, R * ∑ x', K x x' * f x' ^ 2 :=
        sum_le_sum fun x _ => (h1 x).trans (mul_le_mul_of_nonneg_right (hrow x)
          (sum_nonneg fun x' _ => mul_nonneg (hK x x') (sq_nonneg _)))
    _ = R * ∑ x', f x' ^ 2 * ∑ x, K x x' := by
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun x' _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun x _ => by ring
    _ ≤ R * ∑ x', f x' ^ 2 * C :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hcol x') (sq_nonneg _)) hR
    _ = _ := by rw [← sum_mul]; ring

/-- **The rows and columns of `a_{y(x')}^{-4}e^{-ρd(y(x), y(x'))/2}`**: rows `≤ c₁(½, ρ)` (`summation_fine`), columns
`≤ L⁴c₁(½, ρ/2)` (`scale_shift`). -/
lemma kern_rowcol {ρ : ℝ} (hρ : 0 < ρ) (hRMsum : (S.toContSeq).r1 (1 / 2) ρ ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (ρ / 2) ≤ RMS) (hRMss : 32 * Real.log S.L / (2 * ρ) ≤ RMS) :
    (∀ x, ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(1 / 2 * ρ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) ≤ (S.toContSeq).c1 (1 / 2) ρ) ∧
      (∀ x', ∑ x, ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(1 / 2 * ρ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) ≤
          (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (ρ / 2)) := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  refine ⟨fun x => ?_, fun x' => ?_⟩
  · have := sum_fine_bc S (fun y' => Real.exp (-(1 / 2 * ρ * S.dF (bc S.toDomSeq x) y')))
    rw [this]
    exact summation_fine S (by norm_num) hρ hRMsum (bc_mem_detB S x)
  · set y' := bc S.toDomSeq x'
    have hshift : ∀ x, ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * Real.exp (-(1 / 2 * ρ * S.dF (bc S.toDomSeq x) y')) ≤
        (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x)))⁻¹ *
          Real.exp (-(1 / 2 * (ρ / 2) * S.dF y' (bc S.toDomSeq x)))) := by
      intro x
      have hs := scale_shift S (δ := 2 * ρ) (σ := -4) (by positivity) hRMss (by norm_num) (bc S.toDomSeq x) y'
      rw [PartitionUnity.rpow_neg_four, PartitionUnity.rpow_neg_four, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast] at hs
      rw [S.dF_comm (bc S.toDomSeq x) y']
      have he : Real.exp (2 * ρ / 8 * S.dF y' (bc S.toDomSeq x)) *
          Real.exp (-(1 / 2 * ρ * S.dF y' (bc S.toDomSeq x))) =
          Real.exp (-(1 / 2 * (ρ / 2) * S.dF y' (bc S.toDomSeq x))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [S.dF_comm (bc S.toDomSeq x) y'] at hs
      calc ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * Real.exp (-(1 / 2 * ρ * S.dF y' (bc S.toDomSeq x)))
          ≤ ((S.L : ℝ) ^ 4 * Real.exp (2 * ρ / 8 * S.dF y' (bc S.toDomSeq x)) *
              ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x)))⁻¹) *
            Real.exp (-(1 / 2 * ρ * S.dF y' (bc S.toDomSeq x))) :=
            mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
        _ = (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x)))⁻¹ *
            (Real.exp (2 * ρ / 8 * S.dF y' (bc S.toDomSeq x)) *
              Real.exp (-(1 / 2 * ρ * S.dF y' (bc S.toDomSeq x))))) := by ring
        _ = _ := by rw [he]
    calc ∑ x, ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * Real.exp (-(1 / 2 * ρ * S.dF (bc S.toDomSeq x) y'))
        ≤ ∑ x, (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x)))⁻¹ *
          Real.exp (-(1 / 2 * (ρ / 2) * S.dF y' (bc S.toDomSeq x)))) := sum_le_sum fun x _ => hshift x
      _ = (S.L : ℝ) ^ 4 * ∑ y ∈ detB S.toDomSeq, Real.exp (-(1 / 2 * (ρ / 2) * S.dF y' y)) := by
          rw [← mul_sum, sum_fine_bc S (fun y => Real.exp (-(1 / 2 * (ρ / 2) * S.dF y' y)))]
      _ ≤ (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (ρ / 2) :=
          mul_le_mul_of_nonneg_left (summation_fine S (by norm_num) (by positivity) hRMsum2 (bc_mem_detB S x'))
            (by positivity)

/-- **A kernel bound gives an `ℓ²` bound**: `|g(x)| ≤ CΣ_{x'}a_{y(x')}^{-4}e^{-ρd/2}|f(x')|` gives
`‖g‖² ≤ C²c₁(½, ρ)L⁴c₁(½, ρ/2)‖f‖²`. -/
lemma L2_of_kern {ρ : ℝ} (hρ : 0 < ρ) (hRMsum : (S.toContSeq).r1 (1 / 2) ρ ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (ρ / 2) ≤ RMS) (hRMss : 32 * Real.log S.L / (2 * ρ) ≤ RMS) {C : ℝ}
    (hC : 0 ≤ C) (f g : Site NF → Mat)
    (hg : ∀ x, hs (g x) ≤ C * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
      Real.exp (-(1 / 2 * ρ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x')) :
    ‖vL S g‖ ^ 2 ≤ C ^ 2 * ((S.toContSeq).c1 (1 / 2) ρ * ((S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (ρ / 2))) *
      ‖vL S f‖ ^ 2 := by
  obtain ⟨hrow, hcol⟩ := kern_rowcol S hρ hRMsum hRMsum2 hRMss
  set K : Site NF → Site NF → ℝ := fun x x' => ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
    Real.exp (-(1 / 2 * ρ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))
  have hK : ∀ x x', 0 ≤ K x x' := fun x x' => by positivity
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) ρ := by unfold Summation.ContSeq.c1; positivity
  have hsch := schur_L2 K hK hc1 hrow hcol (fun x' => hs (f x'))
  rw [vL_norm_sq', vL_norm_sq']
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hpt : ∀ x, hs2 (g x) ≤ C ^ 2 * (∑ x', K x x' * hs (f x')) ^ 2 := fun x => by
    rw [← hs_sq, ← mul_pow]
    exact pow_le_pow_left₀ (hs_nonneg _) (hg x) 2
  calc (N : ℝ) * ∑ x, hs2 (g x) ≤ N * ∑ x, C ^ 2 * (∑ x', K x x' * hs (f x')) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => hpt x) hN
    _ = N * (C ^ 2 * ∑ x, (∑ x', K x x' * hs (f x')) ^ 2) := by rw [← mul_sum]
    _ ≤ N * (C ^ 2 * ((S.toContSeq).c1 (1 / 2) ρ * ((S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (ρ / 2)) *
          ∑ x', hs (f x') ^ 2)) := by gcongr
    _ = _ := by simp only [hs_sq]; ring

/-- The constant of `P` in `ℓ²`. -/
def KPL (S : SeqDom) (N : ℕ) (δ : ℝ) : ℝ :=
  CPk S N δ ^ 2 * ((S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) *
    ((S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ / 2)))

/-- The constant of `P(𝐔) - P(id)` in `ℓ²`. -/
def KDL (S : SeqDom) (N : ℕ) (δ α₁ η : ℝ) : ℝ :=
  ScalarHyp.CPd S N δ α₁ η ^ 2 * ((S.toContSeq).c1 (1 / 2) (7 / 16 * (thetaB S N δ / 4)) *
    ((S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (7 / 16 * (thetaB S N δ / 4) / 2)))

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

lemma CPd_nn [NeZero N] : 0 ≤ CPd S N δ α₁ η := by
  have hc1 : ∀ r, 0 ≤ (S.toContSeq).c1 (1 / 2) r := fun r => by unfold Summation.ContSeq.c1; positivity
  have hL : (0 : ℝ) ≤ S.L := by positivity
  have hγ : 0 ≤ 2 / gammaB N := by unfold gammaB; positivity
  have hCv := H.Cv_nn
  have hCD := H.CD_nn
  have hCT := H.CTd_nn
  have hη := H.hη
  have hrp := Real.rpow_nonneg hL (12 : ℝ)
  have cA : 0 ≤ CPdA S N δ α₁ η := by
    unfold CPdA
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCD)
      (mul_nonneg (by positivity) hCv)) hγ) hrp) (hc1 _)) (hc1 _)
  have cB1 : 0 ≤ CPdB1 S N δ α₁ η := by
    unfold CPdB1
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCv)
      (mul_nonneg (by positivity) hCD)) hγ) hrp) (hc1 _)) (hc1 _)
  have cB2 : 0 ≤ CPdB2 S N δ η := by
    unfold CPdB2
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCv)
      (mul_nonneg (mul_nonneg (by positivity) hη) hCv)) hγ) hrp) (hc1 _)) (hc1 _)
  have cB3 : 0 ≤ CPdB3 S N δ η := by
    unfold CPdB3
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hη) hCv)
      (mul_nonneg (by positivity) hCv)) hγ) hrp) (hc1 _)) (hc1 _)
  have cB4 : 0 ≤ CPdB4 S N δ α₁ η := by
    unfold CPdB4
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCv)
      (pow_nonneg hγ 2)) hCT) (mul_nonneg (hc1 _) (hc1 _))) (mul_nonneg (by positivity) hCv))
        (mul_nonneg (mul_nonneg hrp (hc1 _)) (hc1 _))
  unfold CPd
  linarith

lemma CPk_nn [NeZero N] : 0 ≤ CPk S N δ := by
  have hc1 : ∀ r, 0 ≤ (S.toContSeq).c1 (1 / 2) r := fun r => by unfold Summation.ContSeq.c1; positivity
  have hL : (0 : ℝ) ≤ S.L := by positivity
  have hγ : 0 ≤ 2 / gammaB N := by unfold gammaB; positivity
  have hrp := Real.rpow_nonneg hL (12 : ℝ)
  unfold CPk
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hγ) hrp) (hc1 _)) (hc1 _)

/-- **`P(𝐔)` in `ℓ²`**: `‖P(𝐔)f‖² ≤ K_{PL}‖f‖²` (`P_bound` and the test of Schur). -/
theorem P_L2 [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMp2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ / 2) ≤ RMS)
    (hRMps : 32 * Real.log S.L / (2 * (7 / 16 * thetaB S N δ)) ≤ RMS) (f : Site NF → Mat) :
    ‖vL S (Pop S X W ΩD f)‖ ^ 2 ≤ KPL S N δ * ‖vL S f‖ ^ 2 := by
  have hθ := H.thetaB_pos (N := N)
  refine L2_of_kern S (ρ := 7 / 16 * thetaB S N δ) (by positivity) hRMθc hRMp2 hRMps H.CPk_nn f (Pop S X W ΩD f) fun x => ?_
  rw [show (1 / 2 : ℝ) * (7 / 16 * thetaB S N δ) = 7 / 32 * thetaB S N δ by ring]
  exact H.P_bound hRMb hRMs4 hsmallT hRMθs hRMθc f x

/-- **`P(𝐔) - P(id)` in `ℓ²`**: `‖(P(𝐔) - P(id))f‖² ≤ K_{DL}‖f‖²` (`Pdiff` and the test of Schur). -/
theorem Pdiff_L2 [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hsmallT0 : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS)
    (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ RMS)
    (hRMq : (S.toContSeq).r1 (1 / 2) (thetaB S N δ) ≤ RMS)
    (hRMq2 : (S.toContSeq).r1 (1 / 2) (thetaB S N δ / 2) ≤ RMS)
    (hRMs8 : 32 * Real.log S.L / (thetaB S N δ / 4 / 2) ≤ RMS)
    (hRMc8 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ / 4)) ≤ RMS)
    (hRMd2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ / 4) / 2) ≤ RMS)
    (hRMds : 32 * Real.log S.L / (2 * (7 / 16 * (thetaB S N δ / 4))) ≤ RMS) (f : Site NF → Mat) :
    ‖vL S ((Pop S X W ΩD - Pop S (X0 S) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) f)‖ ^ 2 ≤
      KDL S N δ α₁ η * ‖vL S f‖ ^ 2 := by
  have hθ := H.thetaB_pos (N := N)
  refine L2_of_kern S (ρ := 7 / 16 * (thetaB S N δ / 4)) (by positivity) hRMc8 hRMd2 hRMds H.CPd_nn f
    ((Pop S X W ΩD - Pop S (X0 S) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) f) fun x => ?_
  rw [show (1 / 2 : ℝ) * (7 / 16 * (thetaB S N δ / 4)) = 7 / 32 * (thetaB S N δ / 4) by ring]
  exact H.Pdiff hRMb hRMs4 hsmallT hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8 hRMc8 f x

end ScalarHyp

/-! ### The projection term of `Δ_𝖺(𝐔)` -/

/-- The projection term of `Δ_𝖺(𝐔)` as a form: `Σ_{ν,x}⟨B_ν(x), (D_{𝐔,ν}P(𝐔)D^*_𝐔C)(x)⟩` (in the norm of `V`). -/
def pairP (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (B C : Fin 4 → Site NF → Mat) : ℂ :=
  pair1V S B (fun ν x => Dfw 1 (cfgX X) ν (Pop S X W ΩD (Ds1L a1 (cfgX X) C)) x)

/-- **Summation by parts at the trivial configuration**: `Σ_{ν,x}⟨B_ν(x), ∂_νG(x)⟩ = ⟨∂^*B, G⟩`. -/
lemma pair_Ds_triv [NeZero N] (B : Fin 4 → Site NF → Mat) (G : Site NF → Mat) :
    ∑ ν, ∑ x, inner ℂ (emb (N := N) (B ν x)) (emb (N := N) (Dfw 1 (cfgX (X0 S)) ν G x)) =
      inner ℂ (vL S (Ds1L a1 (cfgX (X0 S)) B)) (vL S G) := by
  rw [inner_vL]
  simp only [inner_emb]
  have h := herm_Ds1L S B G
  rw [herm_eq] at h
  simp only [ntr, ← mul_sum] at h
  have hN : (N : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N))
  exact (mul_left_cancel₀ hN h).symm

/-- `D_{𝐔,ν}F(x) - ∂_νF(x) = Ad_{e^{iX_ν(x)}}F(x + e_ν) - F(x + e_ν)`. -/
lemma Dfw_sub_triv (X : Fin 4 → Site NF → Mat) (ν : Fin 4) (F : Site NF → Mat) (x : Site NF) :
    Dfw 1 (cfgX X) ν F x - Dfw 1 (cfgX (X0 S)) ν F x =
      Ad (expU (Complex.I • X ν x)) (F (x + unit NF ν)) - F (x + unit NF ν) := by
  rw [Dfw_triv]
  simp only [Dfw, cfgX, inv_one, one_smul]
  abel

/-- **The covariant part of the projection term**:
`|Σ_{ν,x}⟨A_ν(x), (D_{𝐔,ν} - ∂_ν)F(x)⟩| ≤ 12α₁L‖A‖_w‖F‖`. -/
lemma pair_Dfw_diff_le (hRML : (S.L : ℝ) < RMS) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) (A : Fin 4 → Site NF → Mat) (F : Site NF → Mat) :
    ‖∑ ν, ∑ x, inner ℂ (emb (N := N) (A ν x))
        (emb (N := N) (Dfw 1 (cfgX X) ν F x - Dfw 1 (cfgX (X0 S)) ν F x))‖ ≤
      12 * (α₁ * S.L) * √(wnorm S A) * ‖vL S F‖ := by
  have hL0 : (0 : ℝ) ≤ S.L := by positivity
  set r : Site NF → ℝ := fun y => ((S.L : ℝ) ^ jj y)⁻¹
  set u : Fin 4 × Site NF → ℝ := fun p => r p.2 * ‖emb (N := N) (A p.1 p.2)‖
  set v : Fin 4 × Site NF → ℝ := fun p => ‖emb (N := N) (F (p.2 + unit NF p.1))‖
  have hpt : ∀ ν x, ‖inner ℂ (emb (N := N) (A ν x))
      (emb (N := N) (Dfw 1 (cfgX X) ν F x - Dfw 1 (cfgX (X0 S)) ν F x))‖ ≤ 6 * (α₁ * S.L) * (u (ν, x) * v (ν, x)) := by
    intro ν x
    refine (norm_inner_le_norm _ _).trans ?_
    rw [Dfw_sub_triv, norm_emb, norm_emb]
    have hXs : ‖X ν x‖ ≤ 1 / 32 := (X_le_one S hX hα0 ν x).trans hα
    have h1 := hs_Ad_exp_sub_le hXs (F (x + unit NF ν))
    have h2 := X_le_base S hRML hX hα0 ν x
    have hA := hs_nonneg (N := N) (A ν x)
    have hF := hs_nonneg (N := N) (F (x + unit NF ν))
    have hsN := Real.sqrt_nonneg (N : ℝ)
    have h3 : hs (Ad (expU (Complex.I • X ν x)) (F (x + unit NF ν)) - F (x + unit NF ν)) ≤
        6 * (α₁ * S.L * r x) * hs (F (x + unit NF ν)) :=
      h1.trans (by gcongr)
    simp only [u, v, norm_emb]
    calc √N * hs (A ν x) * (√N * hs (Ad (expU (Complex.I • X ν x)) (F (x + unit NF ν)) - F (x + unit NF ν)))
        ≤ √N * hs (A ν x) * (√N * (6 * (α₁ * S.L * r x) * hs (F (x + unit NF ν)))) := by gcongr
      _ = _ := by ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin 4 × Site NF)) u v
  have hu2 : ∑ p, u p ^ 2 = wnorm S A := by
    rw [Fintype.sum_prod_type]
    unfold wnorm
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun μ _ => ?_
    simp only [u, r]
    push_cast
    rw [mul_pow, inv_pow]
  have hv2 : ∑ p, v p ^ 2 = 4 * ‖vL S F‖ ^ 2 := by
    rw [Fintype.sum_prod_type, vL_norm_sq]
    have : ∀ ν, ∑ x, v (ν, x) ^ 2 = ∑ x, ‖emb (N := N) (F x)‖ ^ 2 := fun ν =>
      sum_shift_site S (fun x => ‖emb (N := N) (F x)‖ ^ 2) (unit NF ν)
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hα1 : 0 ≤ 6 * (α₁ * S.L) := by positivity
  calc ‖∑ ν, ∑ x, inner ℂ (emb (N := N) (A ν x))
        (emb (N := N) (Dfw 1 (cfgX X) ν F x - Dfw 1 (cfgX (X0 S)) ν F x))‖
      ≤ ∑ ν, ∑ x, 6 * (α₁ * S.L) * (u (ν, x) * v (ν, x)) :=
        (norm_sum_le _ _).trans (sum_le_sum fun ν _ => (norm_sum_le _ _).trans (sum_le_sum fun x _ => hpt ν x))
    _ = 6 * (α₁ * S.L) * ∑ p, u p * v p := by rw [Fintype.sum_prod_type, mul_sum]; simp only [mul_sum]
    _ ≤ 6 * (α₁ * S.L) * (√(∑ p, u p ^ 2) * √(∑ p, v p ^ 2)) := mul_le_mul_of_nonneg_left hcs hα1
    _ = 12 * (α₁ * S.L) * √(wnorm S A) * ‖vL S F‖ := by
        rw [hu2, hv2, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _),
          show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        ring

/-- `a² ≤ Kb²` gives `a ≤ √Kb`. -/
lemma le_sqrt_mul_of_sq {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ K * b ^ 2) : a ≤ √K * b := by
  calc a = √(a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ √(K * b ^ 2) := Real.sqrt_le_sqrt h
    _ = √K * b := by
        rcases eq_or_lt_of_le hb with hb0 | hb0
        · subst hb0; simp
        · have hK : 0 ≤ K := by
            have : 0 ≤ K * b ^ 2 := (sq_nonneg a).trans h
            exact nonneg_of_mul_nonneg_left this (by positivity)
          rw [Real.sqrt_mul hK, Real.sqrt_sq hb]

/-- The algebra of the comparison: `βs_Wk_P(a + b) + a(k_D(a + b) + b) ≤ K(s_G² + s_W²)` for `a ≤ 2s_G`,
`b ≤ βs_W`. -/
lemma pcomp_alg {a b sG sW β kP kD : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsG : 0 ≤ sG) (hsW : 0 ≤ sW) (hβ : 0 ≤ β)
    (hkP : 0 ≤ kP) (hkD : 0 ≤ kD) (ha2 : a ≤ 2 * sG) (hb2 : b ≤ β * sW) :
    β * sW * (kP * (a + b)) + a * (kD * (a + b) + b) ≤
      (β * (kP + kD + 1) + β ^ 2 * kP + 4 * kD) * (sG ^ 2 + sW ^ 2) := by
  have hab : a + b ≤ 2 * sG + β * sW := add_le_add ha2 hb2
  have e1 : β * sW * (kP * (a + b)) ≤ β * sW * (kP * (2 * sG + β * sW)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab hkP) (by positivity)
  have e2 : kD * (a + b) + b ≤ kD * (2 * sG + β * sW) + β * sW :=
    add_le_add (mul_le_mul_of_nonneg_left hab hkD) hb2
  have e3 : a * (kD * (a + b) + b) ≤ 2 * sG * (kD * (2 * sG + β * sW) + β * sW) :=
    mul_le_mul ha2 e2 (by positivity) (by positivity)
  have h2 : 2 * sG * sW ≤ sG ^ 2 + sW ^ 2 := by nlinarith [sq_nonneg (sG - sW)]
  have h3 : β * (kP + kD + 1) * (2 * sG * sW) ≤ β * (kP + kD + 1) * (sG ^ 2 + sW ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 0 ≤ β ^ 2 * kP * sG ^ 2 := by positivity
  have h5 : 0 ≤ 4 * kD * sW ^ 2 := by positivity
  have e4 : β * sW * (kP * (2 * sG + β * sW)) + 2 * sG * (kD * (2 * sG + β * sW) + β * sW) =
      β * (kP + kD + 1) * (2 * sG * sW) + β ^ 2 * kP * sW ^ 2 + 4 * kD * sG ^ 2 := by ring
  have e5 : (β * (kP + kD + 1) + β ^ 2 * kP + 4 * kD) * (sG ^ 2 + sW ^ 2) =
      β * (kP + kD + 1) * (sG ^ 2 + sW ^ 2) + β ^ 2 * kP * sW ^ 2 + 4 * kD * sG ^ 2 +
        (β ^ 2 * kP * sG ^ 2 + 4 * kD * sW ^ 2) := by ring
  linarith

/-- The constant of the comparison of the projection terms. -/
def Kcomp (S : SeqDom) (N : ℕ) (δ α₁ η : ℝ) : ℝ :=
  12 * (α₁ * S.L) * (√(KPL S N δ) + √(KDL S N δ α₁ η) + 1) + (12 * (α₁ * S.L)) ^ 2 * √(KPL S N δ) +
    4 * √(KDL S N δ α₁ η)

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

/-- **The comparison of the projection terms**: `|Re⟨A, D_𝐔P(𝐔)D^*_𝐔A⟩ - Re⟨A, ∂P(id)∂^*A⟩| ≤
K_comp(‖∇A‖² + ‖A‖_w²)`, by `D_𝐔P(𝐔)D^*_𝐔 - ∂P(id)∂^* = (D_𝐔 - ∂)P(𝐔)D^*_𝐔 + ∂(P(𝐔) - P(id))D^*_𝐔 +
∂P(id)(D^*_𝐔 - ∂^*)`; `K_comp = O(α₁ + η)`. -/
theorem Pcomp [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hsmallT0 : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS)
    (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ RMS)
    (hRMq : (S.toContSeq).r1 (1 / 2) (thetaB S N δ) ≤ RMS)
    (hRMq2 : (S.toContSeq).r1 (1 / 2) (thetaB S N δ / 2) ≤ RMS)
    (hRMs8 : 32 * Real.log S.L / (thetaB S N δ / 4 / 2) ≤ RMS)
    (hRMc8 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ / 4)) ≤ RMS)
    (hRMd2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ / 4) / 2) ≤ RMS)
    (hRMds : 32 * Real.log S.L / (2 * (7 / 16 * (thetaB S N δ / 4))) ≤ RMS)
    (hRMp2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ / 2) ≤ RMS)
    (hRMps : 32 * Real.log S.L / (2 * (7 / 16 * thetaB S N δ)) ≤ RMS) (A : Fin 4 → Site NF → Mat) :
    |(pairP S X W ΩD A A).re - (pairP S (X0 S) (W1 S) ΩD A A).re| ≤
      Kcomp S N δ α₁ η * (gradNorm S A + wnorm S A) := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hRML : (S.L : ℝ) < RMS := by have := H.hRM8; nlinarith
  have hα0 := H.hα0
  have hα32 : α₁ ≤ 1 / 32 := by have := H.hα; nlinarith
  have hX := H.hX
  set D0 := Ds1L a1 (cfgX (X0 S)) A
  set DU := Ds1L a1 (cfgX X) A
  set FU := Pop S X W ΩD DU
  set F0 := Pop S (X0 S) (W1 S) ΩD D0
  set T1 := ∑ ν, ∑ x, inner ℂ (emb (N := N) (A ν x))
    (emb (N := N) (Dfw 1 (cfgX X) ν FU x - Dfw 1 (cfgX (X0 S)) ν FU x))
  have eU : pairP S X W ΩD A A = T1 + inner ℂ (vL S D0) (vL S FU) := by
    rw [← pair_Ds_triv]
    unfold pairP pair1V
    simp only [T1, ← sum_add_distrib, ← inner_add_right, ← emb_add', sub_add_cancel]
    rfl
  have e0 : pairP S (X0 S) (W1 S) ΩD A A = inner ℂ (vL S D0) (vL S F0) := by
    rw [← pair_Ds_triv]
    rfl
  have eF : vL S FU - vL S F0 =
      vL S ((Pop S X W ΩD - Pop S (X0 S) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) DU) +
        vL S (Pop S (X0 S) (W1 S) ΩD (fun x => DU x - D0 x)) := by
    rw [← vL_sub, ← vL_add]
    congr 1
    have : (fun x => DU x - D0 x) = DU - D0 := rfl
    rw [this, map_sub, LinearMap.sub_apply]
    abel
  -- the norms
  set a := ‖vL S D0‖
  set b := ‖vL S (fun x => DU x - D0 x)‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hG := gradNorm_nonneg' S A
  have hW := wnorm_nonneg' S A
  have ha2 : a ≤ 2 * √(gradNorm S A) := by
    have h := ds_le_grad S A
    rw [← vL_norm_sq'] at h
    have := le_sqrt_mul_of_sq ha0 (Real.sqrt_nonneg _) (K := 4) (b := √(gradNorm S A))
      (by rw [Real.sq_sqrt hG]; exact h)
    rwa [show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hb2 : b ≤ 12 * (α₁ * S.L) * √(wnorm S A) := by
    have h := dsU_diff_L2 S hRML hX hα0 hα32 A
    have hβ : 0 ≤ 12 * (α₁ * S.L) := by positivity
    have := le_sqrt_mul_of_sq hb0 (Real.sqrt_nonneg _) (K := (12 * (α₁ * S.L)) ^ 2) (b := √(wnorm S A))
      (by rw [Real.sq_sqrt hW]; nlinarith)
    rwa [Real.sqrt_sq hβ] at this
  have hDU : ‖vL S DU‖ ≤ a + b := by
    have : vL S DU = vL S D0 + vL S (fun x => DU x - D0 x) := by
      rw [← vL_add]; congr 1; funext x; simp
    rw [this]; exact norm_add_le _ _
  have hFU : ‖vL S FU‖ ≤ √(KPL S N δ) * (a + b) :=
    (le_sqrt_mul_of_sq (norm_nonneg _) (norm_nonneg _)
      (H.P_L2 hRMb hRMs4 hsmallT hRMθs hRMθc hRMp2 hRMps DU)).trans
      (mul_le_mul_of_nonneg_left hDU (Real.sqrt_nonneg _))
  have hPd : ‖vL S ((Pop S X W ΩD - Pop S (X0 S) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) DU)‖ ≤
      √(KDL S N δ α₁ η) * (a + b) :=
    (le_sqrt_mul_of_sq (norm_nonneg _) (norm_nonneg _)
      (H.Pdiff_L2 hRMb hRMs4 hsmallT hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8 hRMc8 hRMd2 hRMds DU)).trans
      (mul_le_mul_of_nonneg_left hDU (Real.sqrt_nonneg _))
  have hP0 : ‖vL S (Pop S (X0 S) (W1 S) ΩD (fun x => DU x - D0 x))‖ ≤ b := by
    have h := Pop_contr S ΩD (fun x => DU x - D0 x)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h2 : ‖vL S (Pop S (X0 S) (W1 S) ΩD (fun x => DU x - D0 x))‖ ^ 2 ≤ b ^ 2 := by
      simp only [b, vL_norm_sq']
      exact mul_le_mul_of_nonneg_left h hN
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hb0 (by norm_num)).1 h2
  have hT1 : ‖T1‖ ≤ 12 * (α₁ * S.L) * √(wnorm S A) * (√(KPL S N δ) * (a + b)) :=
    (pair_Dfw_diff_le S hRML hX hα0 hα32 A FU).trans
      (mul_le_mul_of_nonneg_left hFU (by positivity))
  have hI : ‖inner ℂ (vL S D0) (vL S FU - vL S F0)‖ ≤ a * (√(KDL S N δ α₁ η) * (a + b) + b) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ ha0)
    rw [eF]
    exact (norm_add_le _ _).trans (add_le_add hPd hP0)
  have halg := pcomp_alg ha0 hb0 (Real.sqrt_nonneg (gradNorm S A)) (Real.sqrt_nonneg (wnorm S A))
    (show 0 ≤ 12 * (α₁ * S.L) by positivity) (Real.sqrt_nonneg (KPL S N δ)) (Real.sqrt_nonneg (KDL S N δ α₁ η))
    ha2 hb2
  rw [Real.sq_sqrt hG, Real.sq_sqrt hW] at halg
  rw [eU, e0, Complex.add_re, add_sub_assoc, ← Complex.sub_re, ← inner_sub_right]
  calc |T1.re + (inner ℂ (vL S D0) (vL S FU - vL S F0)).re|
      ≤ ‖T1‖ + ‖inner ℂ (vL S D0) (vL S FU - vL S F0)‖ :=
        (abs_add_le _ _).trans (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))
    _ ≤ 12 * (α₁ * S.L) * √(wnorm S A) * (√(KPL S N δ) * (a + b)) +
          a * (√(KDL S N δ α₁ η) * (a + b) + b) := add_le_add hT1 hI
    _ ≤ _ := by unfold Kcomp; linarith

end ScalarHyp

/-! ### The conjugated projection term at `𝐔` -/

lemma emb_sum' {ι : Type*} (s : Finset ι) (f : ι → Mat) : emb (N := N) (∑ i ∈ s, f i) = ∑ i ∈ s, emb (N := N) (f i) :=
  map_sum embL f s

/-- The kernel of `D_{𝐔,ν}P(𝐔)D^*_𝐔`: `k_𝐔(x, x')Z = (D_{𝐔,ν}P(𝐔)D^*_𝐔(δ_{x'}Ze_μ))(x)`. -/
def kGU [NeZero N] (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) (ν : Fin 4)
    (x : Site NF) (μ : Fin 4) (x' : Site NF) : Mat →ₗ[ℂ] Mat :=
  (LinearMap.proj x ∘ₗ DfwL S (cfgX X) ν ∘ₗ Pop S X W ΩD ∘ₗ Ds1L a1 (cfgX X)) ∘ₗ
    (LinearMap.single ℂ (fun _ : Fin 4 => Site NF → Mat) μ ∘ₗ LinearMap.single ℂ (fun _ : Site NF => Mat) x')

lemma kGU_apply [NeZero N] (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (ν : Fin 4) (h : Fin 4 → Site NF → Mat) (x : Site NF) :
    Dfw 1 (cfgX X) ν (Pop S X W ΩD (Ds1L a1 (cfgX X) h)) x = ∑ μ, ∑ x', kGU S X W ΩD ν x μ x' (h μ x') := by
  have e : h = ∑ μ, ∑ x', Pi.single μ (Pi.single x' (h μ x')) := by
    funext μ0 x0
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single μ0 (fun b _ hb => by simp [Pi.single_eq_of_ne' hb]) (by simp)]
    simp [Pi.single_apply]
  change (DfwL S (cfgX X) ν (Pop S X W ΩD (Ds1L a1 (cfgX X) h))) x = _
  conv_lhs => rw [e]
  simp only [map_sum, Finset.sum_apply]
  rfl

/-- The constant of the conjugated projection term at `𝐔`. -/
def CPvU (S : SeqDom) (N : ℕ) (δ α₁ : ℝ) : ℝ :=
  ScalarHyp.CPg S N δ α₁ * (Real.exp (7 / 32 * thetaB S N δ) * (4 / (7 / 32 * thetaB S N δ) + 4)) *
    (((S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ) +
      (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ / 2)) / 2)

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

/-- **The kernel of `D_{𝐔,ν}P(𝐔)D^*_𝐔`** (`gradPDs_bound`):
`|k_𝐔(x, x')Z| ≤ C_Pa_{j(x)}^{-1}a_{j(x')}^{-5}e^{-(7/32)θ_Bd(y(x), y(x'))}|Z|`. -/
lemma kGU_bound [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (ν : Fin 4) (x : Site NF) (μ : Fin 4) (x' : Site NF) (Z : Mat) :
    hs (kGU S X W ΩD ν x μ x' Z) ≤ CPg S N δ α₁ * ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ *
      (((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))) * hs Z := by
  have h := H.gradPDs_bound hRMb hRMs4 hsmallT hRMθs hRMθc ν
    (Pi.single μ (Pi.single x' Z) : Fin 4 → Site NF → Mat) x
  have e : kGU S X W ΩD ν x μ x' Z =
      Dfw 1 (cfgX X) ν (Pop S X W ΩD (Ds1L a1 (cfgX X) (Pi.single μ (Pi.single x' Z)))) x := rfl
  rw [e]
  refine h.trans (le_of_eq ?_)
  have hz : ∀ x'' μ', hs ((Pi.single μ (Pi.single x' Z) : Fin 4 → Site NF → Mat) μ' x'') =
      if μ' = μ ∧ x'' = x' then hs Z else 0 := by
    intro x'' μ'
    by_cases h1 : μ' = μ
    · subst h1
      by_cases h2 : x'' = x'
      · subst h2; simp
      · simp [h2, Pi.single_eq_of_ne h2, RegularAverages.hs_zero']
    · simp [h1, Pi.single_eq_of_ne h1, RegularAverages.hs_zero']
  simp only [hz]
  rw [Finset.sum_eq_single x' (fun b _ hb => by simp [hb]) (by simp)]
  simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- **The conjugated projection term at `𝐔`**: `|Re⟨e^φA, D_𝐔P(𝐔)D^*_𝐔(e^{-φ}A)⟩ - Re⟨A, D_𝐔P(𝐔)D^*_𝐔A⟩| ≤
NC_{PvU}δ'Σ_x(a_{j(x)}^{-1}Σ_ν|A_ν(x)|)²` for `0 ≤ δ' ≤ θ/4`, `θ = (7/32)θ_B` (the kernel of `D_𝐔P(𝐔)D^*_𝐔` and the test
of Schur). -/
theorem P_conjU [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ)) ≤ RMS)
    {δ' : ℝ} (hδ' : 0 ≤ δ') (hδθ : δ' ≤ 1 / 4 * (7 / 32 * thetaB S N δ)) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ' * S.dF x x') (A : Fin 4 → Site NF → Mat) :
    |(pairP S X W ΩD (expA S ph A) (expA S (fun x => -ph x) A)).re - (pairP S X W ΩD A A).re| ≤
      N * CPvU S N δ α₁ * δ' * ∑ x, (((S.L : ℝ) ^ jj x)⁻¹ * ∑ ν, hs (A ν x)) ^ 2 := by
  set θ := 7 / 32 * thetaB S N δ
  have hθ : 0 < θ := by have := H.thetaB_pos (N := N); positivity
  set k : Fin 4 → Site NF → Fin 4 → Site NF → ℂ := fun ν x μ x' =>
    inner ℂ (emb (N := N) (A ν x)) (emb (N := N) (kGU S X W ΩD ν x μ x' (A μ x')))
  -- the two forms through the kernel
  have e1 : pairP S X W ΩD (expA S ph A) (expA S (fun x => -ph x) A) =
      ∑ ν, ∑ x, ∑ μ, ∑ x', ((Real.exp (ph x) * Real.exp (-ph x') : ℝ) : ℂ) * k ν x μ x' := by
    unfold pairP pair1V
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [kGU_apply, emb_sum', inner_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [emb_sum', inner_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    simp only [expA, k, map_smul, emb_smul', inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    push_cast; ring
  have e2 : pairP S X W ΩD A A = ∑ ν, ∑ x, ∑ μ, ∑ x', k ν x μ x' := by
    unfold pairP pair1V
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [kGU_apply, emb_sum', inner_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [emb_sum', inner_sum]
  have e3 : (pairP S X W ΩD (expA S ph A) (expA S (fun x => -ph x) A)).re - (pairP S X W ΩD A A).re =
      (∑ ν, ∑ x, ∑ μ, ∑ x', ((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x').re := by
    rw [e1, e2, ← Complex.sub_re]
    congr 1
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x' _ => ?_
    push_cast; ring
  rw [e3]
  -- the bound of a term
  set u : Site NF → ℝ := fun x => ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ * ∑ ν, hs (A ν x)
  have hu : ∀ x, 0 ≤ u x := fun x => mul_nonneg (by positivity) (Finset.sum_nonneg fun ν _ => hs_nonneg _)
  set K : Site NF → Site NF → ℝ := fun x x' => ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
    Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))
  set C1 := Real.exp θ * (4 / θ + 4)
  have hCPg : 0 ≤ CPg S N δ α₁ := by
    have h1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
    have h2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
    have hv := H.Cv_nn; have hg := H.Cg_nn'
    have hγ : 0 ≤ 2 / gammaB N := by unfold gammaB; positivity
    have hL : (0 : ℝ) ≤ S.L := by positivity
    have hrp := Real.rpow_nonneg hL (12 : ℝ)
    unfold CPg
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hγ) hrp) h1) h2
  set CP := (N : ℝ) * CPg S N δ α₁
  have hCP : 0 ≤ CP := mul_nonneg (Nat.cast_nonneg _) hCPg
  have hterm : ∀ x x', ∑ ν, ∑ μ, ‖((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x'‖ ≤
      CP * δ' * C1 * (K x x' * u x' * u x) := by
    intro x x'
    set d := S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')
    have hd0 : 0 ≤ d := S.dF_nonneg _ _
    have hdx : S.dF x x' ≤ d + 4 := by
      have h2 := S.dF_triangle x (bc S.toDomSeq x) x'
      have h3 := S.dF_triangle (bc S.toDomSeq x) (bc S.toDomSeq x') x'
      have h4 := dF_bc_le S x
      have h5 := dF_bc_le S x'
      rw [S.dF_comm] at h5
      linarith
    have hexp : |Real.exp (ph x) * Real.exp (-ph x') - 1| ≤ δ' * (d + 4) * Real.exp (δ' * (d + 4)) := by
      have e : Real.exp (ph x) * Real.exp (-ph x') = Real.exp (ph x - ph x') := by rw [← Real.exp_add]; ring_nf
      rw [e]
      refine (abs_exp_sub_one_le' _).trans ?_
      have h1 : |ph x - ph x'| ≤ δ' * (d + 4) := (hph x x').trans (mul_le_mul_of_nonneg_left hdx hδ')
      exact mul_le_mul h1 (Real.exp_le_exp.2 h1) (Real.exp_pos _).le (by positivity)
    have hw := conj_weight_le hθ hδ' hδθ hd0
    set a := ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹
    set b := ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹
    set c4 := ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹
    set E := Real.exp (-(θ * d))
    set cc := δ' * (d + 4) * Real.exp (δ' * (d + 4))
    have ha : 0 ≤ a := by positivity
    have hb : 0 ≤ b := by positivity
    have hk : ∀ ν μ, ‖k ν x μ x'‖ ≤ hs (A ν x) * (CP * a * (b * c4 * E) * hs (A μ x')) := by
      intro ν μ
      refine (norm_inner_le_norm _ _).trans ?_
      rw [norm_emb, norm_emb]
      have hkb := H.kGU_bound hRMb hRMs4 hsmallT hRMθs hRMθc ν x μ x' (A μ x')
      have hA := hs_nonneg (N := N) (A ν x)
      have hsN : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
      calc √N * hs (A ν x) * (√N * hs (kGU S X W ΩD ν x μ x' (A μ x')))
          ≤ √N * hs (A ν x) * (√N * (CPg S N δ α₁ * a * (b * c4 * E) * hs (A μ x'))) := by gcongr
        _ = (√N * √N) * (hs (A ν x) * (CPg S N δ α₁ * a * (b * c4 * E) * hs (A μ x'))) := by ring
        _ = hs (A ν x) * (CP * a * (b * c4 * E) * hs (A μ x')) := by rw [hsN]; simp only [CP]; ring
    have hux : u x = a * ∑ ν, hs (A ν x) := rfl
    have hux' : u x' = b * ∑ μ, hs (A μ x') := rfl
    calc ∑ ν, ∑ μ, ‖((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x'‖
        ≤ ∑ ν, ∑ μ, cc * (hs (A ν x) * (CP * a * (b * c4 * E) * hs (A μ x'))) := by
          refine Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun μ _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul hexp (hk ν μ) (norm_nonneg _) (by positivity)
      _ = CP * (cc * E) * (c4 * u x' * u x) := by
          rw [hux, hux', show CP * (cc * E) * (c4 * (b * ∑ μ, hs (A μ x')) * (a * ∑ ν, hs (A ν x))) =
            CP * (cc * E) * c4 * b * a * ((∑ ν, hs (A ν x)) * ∑ μ, hs (A μ x')) by ring,
            Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
      _ ≤ CP * (δ' * C1 * Real.exp (-(1 / 2 * θ * d))) * (c4 * u x' * u x) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hCP) ?_
          have := hu x; have := hu x'; positivity
      _ = CP * δ' * C1 * (K x x' * u x' * u x) := by simp only [K]; ring
  -- the sum and the test of Schur
  have hschur := schur_kernel S hθ hRMsum hRMsum2 hRMss u hu
  have hu2 : ∑ x, u x ^ 2 = ∑ x, (((S.L : ℝ) ^ jj x)⁻¹ * ∑ ν, hs (A ν x)) ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [u, sc_bc]
  have hC1 : 0 ≤ C1 := by positivity
  calc |(∑ ν, ∑ x, ∑ μ, ∑ x', ((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x').re|
      ≤ ‖∑ ν, ∑ x, ∑ μ, ∑ x', ((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x'‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ x, ∑ x', ∑ ν, ∑ μ, ‖((Real.exp (ph x) * Real.exp (-ph x') - 1 : ℝ) : ℂ) * k ν x μ x'‖ := by
        refine le_trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ =>
            norm_sum_le _ _)))) (le_of_eq ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_congr rfl fun ν _ => Finset.sum_comm, Finset.sum_comm]
    _ ≤ ∑ x, ∑ x', CP * δ' * C1 * (K x x' * u x' * u x) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hterm x x'
    _ = CP * δ' * C1 * ∑ x, ∑ x', K x x' * u x' * u x := by simp only [Finset.mul_sum]
    _ ≤ CP * δ' * C1 * (((S.toContSeq).c1 (1 / 2) θ +
          (S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (θ / 2)) / 2 * ∑ x, u x ^ 2) :=
        mul_le_mul_of_nonneg_left hschur (by positivity)
    _ = _ := by rw [hu2]; simp only [CP]; unfold CPvU; ring

end ScalarHyp

end SFBounds
end CoreLean

end
