/-
`lem:sf-decay` of BALABAN_CORE.tex (`542c68192a44`), the steps "The bonds", "The constraint", and "The trivial
configuration", in the model `Blocks.DomSeq` (`η = 1`, `a_j = Lʲ`), for functions with values in a real inner product
space (at the trivial configuration the conjugated form `Re⟨(e^φλ)^*, Δ'_𝖺(id)(e^{-φ}λ)⟩` is the real inner product of
the values; for matrices through `flat`).

* `cosh_sub_one_le`: `cosh s - 1 ≤ s²` for `|s| ≤ 1`.
* `bond_ineq`: the term of a bond, `⟨e^{φ'}β - e^φα, e^{-φ'}β - e^{-φ}α⟩ ≥ |β - α|² - s²(|α|² + |β|²)`, `s = φ' - φ`.
* `block_conj`: the term of a block, `⟨mean(e^φv), mean(e^{-φ}v)⟩ ≥ |m|² - 16δν²` when `|φ - φ(y)| ≤ 2δ` on the block,
  with the mean `m` and the mean `ν²` of `|v|²`.
* `sf_decay_trivial`: `eq:sf-conjugated` at the trivial configuration with the constant `¼`, under the bounds of the
  weight which the proof derives from its Lipschitz property in the weighted distance (the step "Two facts on the
  distance"): `|φ(x + e_μ) - φ(x)| ≤ δL a_{j(x)}^{-1}` and `≤ δL a_{j(x+e_μ)}^{-1}` at the bonds, `|φ(x) - φ(y)| ≤ 2δ` on
  the blocks.
-/
import CoreLean.SmallFieldCoercivity

open Finset
open scoped Classical RealInnerProductSpace

noncomputable section

namespace CoreLean
namespace SmallFieldDecay

open Blocks SmallFieldBlocks DiscretePoincare SmallFieldCoercivity SequenceOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `cosh s - 1 ≤ s²` for `|s| ≤ 1`. -/
lemma cosh_sub_one_le {s : ℝ} (hs : |s| ≤ 1) : Real.cosh s - 1 ≤ s ^ 2 := by
  have h1 := Real.abs_exp_sub_one_sub_id_le hs
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := -s) (by rwa [abs_neg])
  rw [Real.cosh_eq]
  have h1' := (abs_le.1 h1).2
  have h2' := (abs_le.1 h2).2
  nlinarith

lemma one_le_cosh' (s : ℝ) : 0 ≤ Real.cosh s - 1 := by linarith [Real.one_le_cosh s]

/-- **The term of a bond**: `⟨e^{φ'}β - e^φα, e^{-φ'}β - e^{-φ}α⟩ ≥ |β - α|² - s²(|α|² + |β|²)`. -/
lemma bond_ineq (a b : E) (p p' : ℝ) (hs : |p' - p| ≤ 1) :
    ‖b - a‖ ^ 2 - (p' - p) ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      ⟪Real.exp p' • b - Real.exp p • a, Real.exp (-p') • b - Real.exp (-p) • a⟫ := by
  have e : ⟪Real.exp p' • b - Real.exp p • a, Real.exp (-p') • b - Real.exp (-p) • a⟫ =
      ‖b - a‖ ^ 2 - 2 * (Real.cosh (p' - p) - 1) * ⟪a, b⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_sub_sq_real, Real.cosh_eq]
    rw [real_inner_comm a b]
    have h1 : Real.exp p' * Real.exp (-p') = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp p * Real.exp (-p) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp p' * Real.exp (-p) = Real.exp (p' - p) := by rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp p * Real.exp (-p') = Real.exp (-(p' - p)) := by rw [← Real.exp_add]; ring_nf
    linear_combination (‖b‖ ^ 2) * h1 + (‖a‖ ^ 2) * h2 - ⟪a, b⟫ * h3 - ⟪a, b⟫ * h4
  rw [e]
  have hc := cosh_sub_one_le hs
  have hc0 := one_le_cosh' (p' - p)
  have hab := abs_real_inner_le_norm a b
  have h2ab : 2 * (‖a‖ * ‖b‖) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hin : 2 * (Real.cosh (p' - p) - 1) * ⟪a, b⟫ ≤ (p' - p) ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    have h1 : 2 * (Real.cosh (p' - p) - 1) * ⟪a, b⟫ ≤ (Real.cosh (p' - p) - 1) * (2 * (‖a‖ * ‖b‖)) := by
      nlinarith [le_abs_self ⟪a, b⟫]
    have h2 : (Real.cosh (p' - p) - 1) * (2 * (‖a‖ * ‖b‖)) ≤ (Real.cosh (p' - p) - 1) * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h2ab hc0
    have h3 : (Real.cosh (p' - p) - 1) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ (p' - p) ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  linarith

/-- `|e^u - 1| ≤ 4δ` for `|u| ≤ 2δ`, `δ ≤ ½`. -/
lemma abs_exp_sub_one_le {u δ : ℝ} (hδ : δ ≤ 1 / 2) (hu : |u| ≤ 2 * δ) : |Real.exp u - 1| ≤ 4 * δ := by
  have h0 : 0 ≤ δ := by linarith [abs_nonneg u]
  have hu1 : |u| ≤ 1 := by linarith
  have h := Real.abs_exp_sub_one_sub_id_le hu1
  have hsq : u ^ 2 ≤ 2 * δ := by
    have : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    nlinarith [abs_nonneg u]
  calc |Real.exp u - 1| = |(Real.exp u - 1 - u) + u| := by ring_nf
    _ ≤ |Real.exp u - 1 - u| + |u| := abs_add_le _ _
    _ ≤ u ^ 2 + 2 * δ := add_le_add h hu
    _ ≤ 4 * δ := by linarith

/-- **The term of a block**: `⟨mean(e^φv), mean(e^{-φ}v)⟩ ≥ |m|² - 16δν²`. -/
lemma block_conj {ι : Type*} (T : Finset ι) (hT : 0 < T.card) (v : ι → E) (ph : ι → ℝ) (p0 δ : ℝ)
    (hδ : δ ≤ 1 / 128) (hph : ∀ t ∈ T, |ph t - p0| ≤ 2 * δ) :
    ‖(T.card : ℝ)⁻¹ • ∑ t ∈ T, v t‖ ^ 2 - 16 * δ * ((T.card : ℝ)⁻¹ * ∑ t ∈ T, ‖v t‖ ^ 2) ≤
      ⟪(T.card : ℝ)⁻¹ • ∑ t ∈ T, Real.exp (ph t) • v t, (T.card : ℝ)⁻¹ • ∑ t ∈ T, Real.exp (-ph t) • v t⟫ := by
  have hδ0 : 0 ≤ δ := by
    obtain ⟨t, ht⟩ := Finset.card_pos.1 hT
    linarith [abs_nonneg (ph t - p0), hph t ht]
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hT
  set c := (T.card : ℝ)⁻¹
  set m := c • ∑ t ∈ T, v t
  set rp := c • ∑ t ∈ T, (Real.exp (ph t - p0) - 1) • v t
  set rm := c • ∑ t ∈ T, (Real.exp (-(ph t - p0)) - 1) • v t
  set ν2 := c * ∑ t ∈ T, ‖v t‖ ^ 2
  have hν2 : 0 ≤ ν2 := by positivity
  -- the two means through `m`, `r₊`, `r₋`
  have ep : c • ∑ t ∈ T, Real.exp (ph t) • v t = Real.exp p0 • (m + rp) := by
    have h1 : m + rp = c • ∑ t ∈ T, Real.exp (ph t - p0) • v t := by
      simp only [m, rp, ← smul_add, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun t _ => ?_
      rw [sub_smul, one_smul]; abel
    rw [h1, smul_comm (Real.exp p0) c (∑ t ∈ T, Real.exp (ph t - p0) • v t),
      Finset.smul_sum (r := Real.exp p0)]
    refine congrArg (c • ·) (sum_congr rfl fun t _ => ?_)
    rw [smul_smul, ← Real.exp_add, add_sub_cancel]
  have em : c • ∑ t ∈ T, Real.exp (-ph t) • v t = Real.exp (-p0) • (m + rm) := by
    have h1 : m + rm = c • ∑ t ∈ T, Real.exp (-(ph t - p0)) • v t := by
      simp only [m, rm, ← smul_add, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun t _ => ?_
      rw [sub_smul, one_smul]; abel
    rw [h1, smul_comm (Real.exp (-p0)) c (∑ t ∈ T, Real.exp (-(ph t - p0)) • v t),
      Finset.smul_sum (r := Real.exp (-p0))]
    refine congrArg (c • ·) (sum_congr rfl fun t _ => ?_)
    rw [smul_smul, ← Real.exp_add, show -p0 + -(ph t - p0) = -ph t by ring]
  have hexp : ∀ X : ℝ, Real.exp p0 * (Real.exp (-p0) * X) = X := fun X => by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [ep, em, real_inner_smul_left, real_inner_smul_right, hexp]
  -- the bounds `|m|² ≤ ν²` and `|r_±|² ≤ 16δ²ν²`
  have hm : ‖m‖ ^ 2 ≤ ν2 := by
    have := mean_sq_le T hT v
    simp only [ν2, c, m] at this ⊢
    rw [le_inv_mul_iff₀ hc]; linarith
  have hr : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ‖c • ∑ t ∈ T, (Real.exp (σ * (ph t - p0)) - 1) • v t‖ ^ 2 ≤ (4 * δ) ^ 2 * ν2 := by
    intro σ hσ
    have h1 := mean_sq_le T hT (fun t => (Real.exp (σ * (ph t - p0)) - 1) • v t)
    have h2 : ∑ t ∈ T, ‖(Real.exp (σ * (ph t - p0)) - 1) • v t‖ ^ 2 ≤ ∑ t ∈ T, (4 * δ) ^ 2 * ‖v t‖ ^ 2 := by
      refine sum_le_sum fun t ht => ?_
      rw [norm_smul, mul_pow, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hb : |σ * (ph t - p0)| ≤ 2 * δ := by
        rcases hσ with rfl | rfl
        · rw [one_mul]; exact hph t ht
        · rw [neg_one_mul, abs_neg]; exact hph t ht
      have := abs_exp_sub_one_le (by linarith) hb
      nlinarith [abs_nonneg (Real.exp (σ * (ph t - p0)) - 1), sq_abs (Real.exp (σ * (ph t - p0)) - 1)]
    rw [← mul_sum] at h2
    simp only [ν2, c] at h1 ⊢
    rw [mul_left_comm]
    calc ‖(T.card : ℝ)⁻¹ • ∑ t ∈ T, (Real.exp (σ * (ph t - p0)) - 1) • v t‖ ^ 2
        ≤ (T.card : ℝ)⁻¹ * ∑ t ∈ T, ‖(Real.exp (σ * (ph t - p0)) - 1) • v t‖ ^ 2 := by
          rw [le_inv_mul_iff₀ hc]; linarith
      _ ≤ (T.card : ℝ)⁻¹ * ((4 * δ) ^ 2 * ∑ t ∈ T, ‖v t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hrp : ‖rp‖ ^ 2 ≤ (4 * δ) ^ 2 * ν2 := by
    have := hr 1 (Or.inl rfl); simpa [rp] using this
  have hrm : ‖rm‖ ^ 2 ≤ (4 * δ) ^ 2 * ν2 := by
    have := hr (-1) (Or.inr rfl)
    simp only [neg_one_mul] at this; exact this
  -- the inner product
  set ν := Real.sqrt ν2
  have hνsq : ν ^ 2 = ν2 := Real.sq_sqrt hν2
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  have hm' : ‖m‖ ≤ ν := by rw [← Real.sqrt_sq (norm_nonneg m)]; exact Real.sqrt_le_sqrt hm
  have hrp' : ‖rp‖ ≤ 4 * δ * ν := by
    rw [← Real.sqrt_sq (norm_nonneg rp), show 4 * δ * ν = Real.sqrt ((4 * δ) ^ 2 * ν2) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hrp
  have hrm' : ‖rm‖ ≤ 4 * δ * ν := by
    rw [← Real.sqrt_sq (norm_nonneg rm), show 4 * δ * ν = Real.sqrt ((4 * δ) ^ 2 * ν2) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hrm
  have e : ⟪m + rp, m + rm⟫ = ‖m‖ ^ 2 + ⟪m, rm⟫ + ⟪rp, m⟫ + ⟪rp, rm⟫ := by
    simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq]; ring
  rw [e]
  have i1 := abs_real_inner_le_norm m rm
  have i2 := abs_real_inner_le_norm rp m
  have i3 := abs_real_inner_le_norm rp rm
  have hmrm : ‖m‖ * ‖rm‖ ≤ ν * (4 * δ * ν) := mul_le_mul hm' hrm' (norm_nonneg _) hν0
  have hrpm : ‖rp‖ * ‖m‖ ≤ 4 * δ * ν * ν := mul_le_mul hrp' hm' (norm_nonneg _) (by positivity)
  have hrprm : ‖rp‖ * ‖rm‖ ≤ 4 * δ * ν * (4 * δ * ν) := mul_le_mul hrp' hrm' (norm_nonneg _) (by positivity)
  have hδ2 : 16 * δ ^ 2 ≤ 8 * δ := by nlinarith
  nlinarith [neg_abs_le ⟪m, rm⟫, neg_abs_le ⟪rp, m⟫, neg_abs_le ⟪rp, rm⟫]

/-! ### The sums over the lattice -/

variable {n : ℕ} [NeZero n] (S : DomSeq n)

/-- The left side of `eq:sf-conjugated` at the trivial configuration: the bonds and the constraint of
`(e^φv, e^{-φ}v)`. -/
def conjForm0 (ph : Site n → ℝ) (v : Site n → E) : ℝ :=
  ∑ x, ∑ μ : Fin 4, ⟪Real.exp (ph (x + unit n μ)) • v (x + unit n μ) - Real.exp (ph x) • v x,
      Real.exp (-ph (x + unit n μ)) • v (x + unit n μ) - Real.exp (-ph x) • v x⟫ +
    ∑ y ∈ detB S, aseq 1 S.L (S.sc y) * (S.L : ℝ) ^ (2 * S.sc y) *
      ⟪mBlk S y (fun x => Real.exp (ph x) • v x), mBlk S y (fun x => Real.exp (-ph x) • v x)⟫

/-- The sum over the shifted sites. -/
lemma sum_shift {M : Type*} [AddCommMonoid M] (μ : Fin 4) (F : Site n → M) :
    ∑ x, F (x + unit n μ) = ∑ x, F x :=
  Fintype.sum_equiv (Equiv.addRight (unit n μ)) _ _ fun _ => rfl

/-- **`eq:sf-conjugated` at the trivial configuration**, with the constant `¼`. -/
theorem sf_decay_trivial (ph : Site n → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L))
    (hbond : ∀ x μ, |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc x)⁻¹ ∧
      |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹)
    (hblock : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, |ph x - ph y| ≤ 2 * δ) (v : Site n → E) :
    (1 / 4) * (dsq v + wnorm S v) ≤ conjForm0 S ph v := by
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hLpos : (0 : ℝ) < S.L := by linarith
  have hδs : δ ≤ 1 / 384 := hδ.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hδL : δ * S.L ≤ 1 / 128 := by
    calc δ * S.L ≤ 1 / (128 * S.L) * S.L := mul_le_mul_of_nonneg_right hδ hLpos.le
      _ = 1 / 128 := by field_simp
  -- the bonds
  have hb : dsq v - 8 * ((δ * S.L) ^ 2) * wnorm S v ≤ ∑ x, ∑ μ : Fin 4,
      ⟪Real.exp (ph (x + unit n μ)) • v (x + unit n μ) - Real.exp (ph x) • v x,
        Real.exp (-ph (x + unit n μ)) • v (x + unit n μ) - Real.exp (-ph x) • v x⟫ := by
    have hterm : ∀ x μ, ‖v (x + unit n μ) - v x‖ ^ 2 - (δ * S.L) ^ 2 *
        (((S.L : ℝ) ^ (2 * S.sc x))⁻¹ * ‖v x‖ ^ 2 +
          ((S.L : ℝ) ^ (2 * S.sc (x + unit n μ)))⁻¹ * ‖v (x + unit n μ)‖ ^ 2) ≤
        ⟪Real.exp (ph (x + unit n μ)) • v (x + unit n μ) - Real.exp (ph x) • v x,
          Real.exp (-ph (x + unit n μ)) • v (x + unit n μ) - Real.exp (-ph x) • v x⟫ := by
      intro x μ
      obtain ⟨h1, h2⟩ := hbond x μ
      have hs1 : |ph (x + unit n μ) - ph x| ≤ 1 := by
        refine h1.trans ?_
        have hi : ((S.L : ℝ) ^ S.sc x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
        have hprod : δ * S.L * ((S.L : ℝ) ^ S.sc x)⁻¹ ≤ 1 / 128 * 1 :=
          mul_le_mul hδL hi (by positivity) (by norm_num)
        linarith
      refine le_trans ?_ (bond_ineq (v x) (v (x + unit n μ)) (ph x) (ph (x + unit n μ)) hs1)
      have hsq1 : (ph (x + unit n μ) - ph x) ^ 2 ≤ (δ * S.L) ^ 2 * ((S.L : ℝ) ^ (2 * S.sc x))⁻¹ := by
        rw [pow_mul, ← sq_abs, show ((S.L : ℝ) ^ 2) ^ S.sc x = ((S.L : ℝ) ^ S.sc x) ^ 2 by ring, ← inv_pow,
          ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hsq2 : (ph (x + unit n μ) - ph x) ^ 2 ≤
          (δ * S.L) ^ 2 * ((S.L : ℝ) ^ (2 * S.sc (x + unit n μ)))⁻¹ := by
        rw [pow_mul, ← sq_abs, show ((S.L : ℝ) ^ 2) ^ S.sc (x + unit n μ) =
          ((S.L : ℝ) ^ S.sc (x + unit n μ)) ^ 2 by ring, ← inv_pow, ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      have := mul_le_mul_of_nonneg_right hsq1 (sq_nonneg ‖v x‖)
      have := mul_le_mul_of_nonneg_right hsq2 (sq_nonneg ‖v (x + unit n μ)‖)
      nlinarith
    have hsum : ∑ x, ∑ μ : Fin 4, (((S.L : ℝ) ^ (2 * S.sc x))⁻¹ * ‖v x‖ ^ 2 +
        ((S.L : ℝ) ^ (2 * S.sc (x + unit n μ)))⁻¹ * ‖v (x + unit n μ)‖ ^ 2) = 8 * wnorm S v := by
      set A : Site n → ℝ := fun x => ((S.L : ℝ) ^ (2 * S.sc x))⁻¹ * ‖v x‖ ^ 2
      have e1 : ∑ x, ∑ μ : Fin 4, (A x + A (x + unit n μ)) =
          ∑ x, ∑ _μ : Fin 4, A x + ∑ μ : Fin 4, ∑ x, A (x + unit n μ) := by
        rw [Finset.sum_comm (s := (univ : Finset (Fin 4))) (t := (univ : Finset (Site n)))
          (f := fun μ x => A (x + unit n μ))]
        simp only [sum_add_distrib]
      have e2 : ∀ μ : Fin 4, ∑ x, A (x + unit n μ) = ∑ x, A x := fun μ => sum_shift μ A
      show ∑ x, ∑ μ : Fin 4, (A x + A (x + unit n μ)) = 8 * wnorm S v
      rw [e1]
      simp only [e2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, wnorm, ← sum_mul, ← mul_sum]
      simp only [A]
      ring
    calc dsq v - 8 * ((δ * S.L) ^ 2) * wnorm S v
        = ∑ x, ∑ μ : Fin 4, (‖v (x + unit n μ) - v x‖ ^ 2 - (δ * S.L) ^ 2 *
            (((S.L : ℝ) ^ (2 * S.sc x))⁻¹ * ‖v x‖ ^ 2 +
              ((S.L : ℝ) ^ (2 * S.sc (x + unit n μ)))⁻¹ * ‖v (x + unit n μ)‖ ^ 2)) := by
          simp only [sum_sub_distrib, ← mul_sum]
          rw [hsum, dsq]; ring
      _ ≤ _ := sum_le_sum fun x _ => sum_le_sum fun μ _ => hterm x μ
  -- the constraint
  have hc : cform S v - 16 * δ * wnorm S v ≤ ∑ y ∈ detB S, aseq 1 S.L (S.sc y) * (S.L : ℝ) ^ (2 * S.sc y) *
      ⟪mBlk S y (fun x => Real.exp (ph x) • v x), mBlk S y (fun x => Real.exp (-ph x) • v x)⟫ := by
    have hw : wnorm S v = ∑ y ∈ detB S, ((S.L : ℝ) ^ (2 * S.sc y))⁻¹ *
        ∑ o ∈ box 4 (S.L ^ S.sc y), ‖v (phi S (S.sc y) y o)‖ ^ 2 := by
      rw [wnorm, sum_blocks S]
      refine sum_congr rfl fun y hy => ?_
      obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
      rw [mul_sum, sum_Blk _ (S.sc_le _) (inLat_bc x0)]
      refine sum_congr rfl fun o ho => ?_
      rw [sc_of_mem_Blk S hy (phi_mem _ (S.sc_le _) (inLat_bc x0) ho)]
    rw [hw, cform, mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun y hy => ?_
    obtain ⟨x0, -, rfl⟩ := mem_image.1 hy
    set j := S.sc (bc S x0)
    have hT : 0 < (box 4 (S.L ^ j)).card := by rw [card_box]; have := S.three_le_L; positivity
    have hcard : ((box 4 (S.L ^ j)).card : ℝ) = (S.L : ℝ) ^ (2 * j) * (S.L : ℝ) ^ (2 * j) := by
      rw [card_box]; push_cast; rw [← pow_mul, ← pow_add]; ring_nf
    have hbc := block_conj (box 4 (S.L ^ j)) hT (fun o => v (phi S j (bc S x0) o))
      (fun o => ph (phi S j (bc S x0) o)) (ph (bc S x0)) δ (hδs.trans (by norm_num))
      (fun o ho => hblock _ hy _ (phi_mem _ (S.sc_le _) (inLat_bc x0) ho))
    have ha := aseq_mem S.L (by have := S.three_le_L; omega) j
    have ha0 : 0 ≤ aseq 1 S.L j := (aseq_pos (aa := 1) one_pos S.L j).le
    have hP : (0 : ℝ) < (S.L : ℝ) ^ (2 * j) := by positivity
    simp only [mBlk, meanB] at hbc ⊢
    rw [hcard] at hbc
    set sV := ∑ o ∈ box 4 (S.L ^ j), ‖v (phi S j (bc S x0) o)‖ ^ 2
    have hS0 : 0 ≤ sV := by positivity
    have key : (S.L : ℝ) ^ (2 * j) * (16 * δ * (((S.L : ℝ) ^ (2 * j) * (S.L : ℝ) ^ (2 * j))⁻¹ * sV)) =
        16 * δ * (((S.L : ℝ) ^ (2 * j))⁻¹ * sV) := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hbc (mul_nonneg ha0 hP.le)
    rw [hcard]
    have h16 : aseq 1 S.L j * (16 * δ * (((S.L : ℝ) ^ (2 * j))⁻¹ * sV)) ≤ 16 * δ * (((S.L : ℝ) ^ (2 * j))⁻¹ * sV) := by
      have : 0 ≤ 16 * δ * (((S.L : ℝ) ^ (2 * j))⁻¹ * sV) := by positivity
      nlinarith [ha.2]
    nlinarith [key]
  -- the trivial configuration
  have hcoer := sf_coercivity S v
  have hwn : 0 ≤ wnorm S v := by unfold wnorm; positivity
  have hds : 0 ≤ dsq v := by unfold dsq; positivity
  have hsq : (δ * S.L) ^ 2 ≤ (1 / 128) ^ 2 := pow_le_pow_left₀ (by positivity) hδL 2
  have hsmall : 8 * (δ * S.L) ^ 2 + 16 * δ ≤ 1 / 12 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hsmall hwn
  unfold conjForm0
  linarith

end SmallFieldDecay
end CoreLean

end
