/-
`lem:sf-decay` of BALABAN_CORE.tex (`542c68192a44`), the conjugated form for matrix-valued `0`-forms, in the model
`Blocks.DomSeq` (`η = 1`, `a_j = Lʲ`).

The scalar form of `Δ'_𝖺(𝐔)`: `Φ(f, g) = Σ_b tr((D_𝐔f)(b)(D_𝐔g)(b)) + Σ_{y ∈ 𝐁}𝖺_{j(y)}a_{j(y)}²tr((Q'f)(y)(Q'g)(y))`
(`lem:covariance`(i), `eq:constraint-forms`), with the averages in the form of `lem:block-average-transports`,
`(Q'_j(𝐔)f)(y) = (a₀/a_j)⁴Σ_{x ∈ Δ(y)}Ad_{W(y, x)}f(x)`, the transports `W` as data.

* `Phi`: the form; `conjL`, `conjR`: `e^φλ^*` and `e^{-φ}λ`.
* `re_ntr_flat`: `Re tr(X^*Y) = N⁻¹⟨flat X, flat Y⟩`, with which the form at the trivial configuration and the trivial
  transports is `N⁻¹` times the real form of `SmallFieldDecay.conjForm0` (`phi_trivial`), so that
  `sf_decay_trivial` gives the constant `¼` for matrices (`sf_decay_trivial_mat`).
-/
import CoreLean.SmallFieldDecayTrivial
import CoreLean.Projection
import CoreLean.OpNorm

open Finset
open scoped Classical RealInnerProductSpace Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace CoreLean
namespace SmallFieldDecay

open Blocks SmallFieldBlocks DiscretePoincare SmallFieldCoercivity SequenceOperators

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `Re tr(X^*Y) = N⁻¹⟨flat X, flat Y⟩_ℝ`. -/
lemma re_ntr_flat [NeZero N] (X Y : Mat) : (ntr (Xᴴ * Y)).re = (N : ℝ)⁻¹ * ⟪flat X, flat Y⟫ := by
  have e : ⟪flat X, flat Y⟫ = (inner ℂ (flat X) (flat Y)).re := by
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    rfl
  rw [e, inner_flat_ntr]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  field_simp

variable {n : ℕ} [NeZero n] (S : DomSeq n)

/-- The forward difference `(D_𝐔f)(x, x + e_μ) = Ad_{𝐔(x, x+e_μ)}f(x + e_μ) - f(x)` (`η = 1`). -/
def DU (U : Config N n) (f : Site n → Mat) (μ : Fin 4) (x : Site n) : Mat := Ad (U μ x) (f (x + unit n μ)) - f x

/-- The average `(Q'_{j(y)}(𝐔)f)(y) = (a₀/a_j)⁴Σ_{x ∈ Δ(y)}Ad_{W(y, x)}f(x)`. -/
def avgW (W : Site n → Site n → GLN) (y : Site n) (f : Site n → Mat) : Mat :=
  (((box 4 (S.L ^ S.sc y)).card : ℝ) : ℂ)⁻¹ •
    ∑ o ∈ box 4 (S.L ^ S.sc y), Ad (W y (phi S (S.sc y) y o)) (f (phi S (S.sc y) y o))

/-- **The scalar form** `⟨f, Δ'_𝖺(𝐔)g⟩`. -/
def Phi (U : Config N n) (W : Site n → Site n → GLN) (f g : Site n → Mat) : ℂ :=
  ∑ x, ∑ μ : Fin 4, ntr (DU U f μ x * DU U g μ x) +
    ∑ y ∈ detB S, ((aseq 1 S.L (S.sc y) * (S.L : ℝ) ^ (2 * S.sc y) : ℝ) : ℂ) *
      ntr (avgW S W y f * avgW S W y g)

/-- `e^φλ^*`. -/
def conjL (ph : Site n → ℝ) (lam : Site n → Mat) : Site n → Mat :=
  fun x => ((Real.exp (ph x) : ℝ) : ℂ) • (lam x)ᴴ

/-- `e^{-φ}λ`. -/
def conjR (ph : Site n → ℝ) (lam : Site n → Mat) : Site n → Mat :=
  fun x => ((Real.exp (-ph x) : ℝ) : ℂ) • lam x

/-- `‖∂λ‖₂²` with the Hilbert–Schmidt norm. -/
def dsqM (lam : Site n → Mat) : ℝ := ∑ x, ∑ μ : Fin 4, hs2 (lam (x + unit n μ) - lam x)

/-- `‖λ‖_w²` with the Hilbert–Schmidt norm. -/
def wnormM (lam : Site n → Mat) : ℝ := ∑ x, (((S.L : ℝ) ^ (2 * S.sc x))⁻¹) * hs2 (lam x)

lemma norm_flat_sq [NeZero N] (X : Mat) : ‖flat X‖ ^ 2 = N * hs2 X := by
  rw [norm_flat, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hs_sq]

lemma dsq_flat [NeZero N] (lam : Site n → Mat) : dsq (fun x => flat (lam x)) = N * dsqM lam := by
  simp only [dsq, dsqM, ← map_sub, norm_flat_sq, mul_sum]

lemma wnorm_flat [NeZero N] (lam : Site n → Mat) : wnorm S (fun x => flat (lam x)) = N * wnormM S lam := by
  simp only [wnorm, wnormM, norm_flat_sq, mul_sum]
  refine sum_congr rfl fun x _ => by ring

lemma flat_real_smul (r : ℝ) (X : Mat) : flat (((r : ℝ) : ℂ) • X) = r • flat X := by
  rw [map_smul, Complex.coe_smul]

lemma flat_rsmul (r : ℝ) (X : Mat) : flat (r • X) = r • flat X := by
  ext p; simp [flat]

lemma conjTranspose_real_smul (r : ℝ) (X : Mat) : (((r : ℝ) : ℂ) • X)ᴴ = ((r : ℝ) : ℂ) • Xᴴ := by
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]

/-- **The form at the trivial configuration and the trivial transports** is `N⁻¹` times the real form
`conjForm0` of the values `flat λ(x)`. -/
theorem phi_trivial [NeZero N] (ph : Site n → ℝ) (lam : Site n → Mat) :
    (Phi S (fun _ _ => 1) (fun _ _ => 1) (conjL ph lam) (conjR ph lam)).re =
      (N : ℝ)⁻¹ * conjForm0 S ph (fun x => flat (lam x)) := by
  simp only [Phi, conjForm0, Complex.add_re, Complex.re_sum, mul_add, mul_sum]
  congr 1
  · refine sum_congr rfl fun x _ => sum_congr rfl fun μ _ => ?_
    have e1 : DU (fun _ _ => (1 : GLN)) (conjL ph lam) μ x =
        ((((Real.exp (ph (x + unit n μ)) : ℝ) : ℂ) • lam (x + unit n μ)) -
          (((Real.exp (ph x) : ℝ) : ℂ) • lam x))ᴴ := by
      simp only [DU, Ad_one, conjL, Matrix.conjTranspose_sub, conjTranspose_real_smul]
    have e2 : DU (fun _ _ => (1 : GLN)) (conjR ph lam) μ x =
        (((Real.exp (-ph (x + unit n μ)) : ℝ) : ℂ) • lam (x + unit n μ)) -
          (((Real.exp (-ph x) : ℝ) : ℂ) • lam x) := by
      simp only [DU, Ad_one, conjR]
    rw [e1, e2, re_ntr_flat, map_sub, map_sub, flat_real_smul, flat_real_smul, flat_real_smul, flat_real_smul]
  · refine sum_congr rfl fun y _ => ?_
    have eL : avgW S (fun _ _ => 1) y (conjL ph lam) =
        ((((box 4 (S.L ^ S.sc y)).card : ℝ) : ℂ)⁻¹ •
          ∑ o ∈ box 4 (S.L ^ S.sc y), ((Real.exp (ph (phi S (S.sc y) y o)) : ℝ) : ℂ) •
            lam (phi S (S.sc y) y o))ᴴ := by
      simp only [avgW, Ad_one, conjL, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
        conjTranspose_real_smul]
      congr 1
      simp [Complex.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal]
    have eR : avgW S (fun _ _ => 1) y (conjR ph lam) =
        (((box 4 (S.L ^ S.sc y)).card : ℝ) : ℂ)⁻¹ •
          ∑ o ∈ box 4 (S.L ^ S.sc y), ((Real.exp (-ph (phi S (S.sc y) y o)) : ℝ) : ℂ) •
            lam (phi S (S.sc y) y o) := by
      simp only [avgW, Ad_one, conjR]
    rw [eL, eR, Complex.re_ofReal_mul, re_ntr_flat]
    simp only [mBlk, meanB, flat_rsmul, map_smul, map_sum, flat_real_smul, ← Complex.ofReal_inv,
      Complex.coe_smul]
    ring

/-- **`eq:sf-conjugated` at the trivial configuration for matrices**, with the constant `¼`. -/
theorem sf_decay_trivial_mat [NeZero N] (ph : Site n → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L))
    (hbond : ∀ x μ, |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc x)⁻¹ ∧
      |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹)
    (hblock : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, |ph x - ph y| ≤ 2 * δ) (lam : Site n → Mat) :
    (1 / 4) * (dsqM lam + wnormM S lam) ≤
      (Phi S (fun _ _ => 1) (fun _ _ => 1) (conjL ph lam) (conjR ph lam)).re := by
  have h := sf_decay_trivial S ph δ hδ0 hδ hbond hblock (fun x => flat (lam x))
  rw [dsq_flat, wnorm_flat] at h
  rw [phi_trivial]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [le_inv_mul_iff₀ hN]
  linarith

end SmallFieldDecay
end CoreLean

end
