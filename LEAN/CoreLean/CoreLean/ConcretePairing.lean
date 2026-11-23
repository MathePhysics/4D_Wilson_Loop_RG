/-
The concrete layer, step C1 (`CONCRETE_LAYER.md`): the pairings of BALABAN_CORE.tex (`615c66b253fe`) as bilinear forms.

* `wpair w`: the weighted pairing `(f, g) ↦ Σ_i w_i tr(f(i)g(i))` of matrix-valued functions on a finite set, with the
  normalised trace `tr = N⁻¹Tr` (`def:group`(ii)), as a `LinearMap.BilinForm ℂ`. With `w_x = a_j⁴` on the sites it is
  `⟨·,·⟩` of `eq:pairing` on `0`-forms (`wpair_form0`); on the bonds of the layers with `w_c = a_{j(c)}⁴` it is the
  pairing `(μ, ν)_w` of the proof of `thm:critical`(iii); on `𝐁` with `w_y = a_{j(y)}⁴` it is the pairing of
  `def:operators`(iii).
* `pairForm1 a`: `⟨·,·⟩` of `eq:pairing` on `1`-forms, `⟨A, A'⟩ = Σ_μ⟨A_μ, A'_μ⟩` (`pairForm1_apply`).
* `wpair_symm`, `wpair_nondegenerate`, `pairForm1_symm`, `pairForm1_nondegenerate`: the forms are symmetric, and
  nondegenerate for positive weights (`a_j > 0`): `(f, f^*)` is the weighted sum of the squared Hilbert–Schmidt norms.
* `transpose`: the transpose `T^T` of a linear map with respect to two nondegenerate forms on finite-dimensional spaces,
  `B_E(T^Tμ, A) = B_F(μ, TA)` (`transpose_spec`), unique (`transpose_unique`); `Q^*` and `Q'^*` of `def:operators`
  are these transposes.
* `constraint_form`: the constraint form of `eq:constraint-forms`, `𝖺Σ_c a_c²tr((QA)(c))² = ⟨A, Q^T(𝖺a_c^{-2})QA⟩`,
  so that `Q^*𝖺Q = Q^T ∘ (μ ↦ 𝖺a_c^{-2}μ) ∘ Q`.
-/
import CoreLean.Differences

open Matrix
open LinearMap (BilinForm)

noncomputable section

namespace CoreLean
namespace ConcretePairing

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-! ### The weighted pairing on matrix-valued functions -/

variable {ι : Type*} [Fintype ι]

/-- `(f, g) ↦ Σ_i w_i tr(f(i)g(i))`. -/
def wpair (w : ι → ℂ) : BilinForm ℂ (ι → Mat) :=
  LinearMap.mk₂ ℂ (fun f g => ∑ i, w i * ntr (f i * g i))
    (fun f f' g => by simp only [Pi.add_apply, add_mul, ntr, trace_add]; rw [← Finset.sum_add_distrib];
                      try exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c f g => by simp only [Pi.smul_apply, smul_mul_assoc, ntr, trace_smul, smul_eq_mul, Finset.mul_sum];
                     try exact Finset.sum_congr rfl fun i _ => by ring)
    (fun f g g' => by simp only [Pi.add_apply, mul_add, ntr, trace_add]; rw [← Finset.sum_add_distrib];
                      try exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c f g => by simp only [Pi.smul_apply, mul_smul_comm, ntr, trace_smul, smul_eq_mul, Finset.mul_sum];
                     try exact Finset.sum_congr rfl fun i _ => by ring)

@[simp] lemma wpair_apply (w : ι → ℂ) (f g : ι → Mat) : wpair w f g = ∑ i, w i * ntr (f i * g i) := rfl

/-- The pairing is symmetric (the trace is cyclic). -/
theorem wpair_symm (w : ι → ℂ) (f g : ι → Mat) : wpair w f g = wpair w g f := by
  simp only [wpair_apply, ntr, Matrix.trace_mul_comm (f _)]

/-- `tr(X X^*) = N⁻¹ Σ|X_{ji}|²`, a real number. -/
lemma ntr_mul_conj (X : Mat) : ntr (X * Xᴴ) = (((N : ℝ)⁻¹ * ∑ i, ∑ j, Complex.normSq (X j i) : ℝ) : ℂ) := by
  rw [ntr, Matrix.trace_mul_comm, trace_conjTranspose_mul_self]
  push_cast; ring

/-- **The weighted pairing is nondegenerate for positive weights.** -/
theorem wpair_nondegenerate (r : ι → ℝ) (hr : ∀ i, 0 < r i) : (wpair (fun i => (r i : ℂ)) (N := N)).Nondegenerate := by
  have hsep : LinearMap.SeparatingLeft (wpair (fun i => (r i : ℂ)) (N := N)) := by
    intro f hf
    have h := hf (fun i => (f i)ᴴ)
    simp only [wpair_apply, ntr_mul_conj] at h
    -- the sum is a real number which vanishes
    have hreal : ∑ i, r i * ((N : ℝ)⁻¹ * ∑ a, ∑ b, Complex.normSq (f i b a)) = 0 := by
      have : ((∑ i, r i * ((N : ℝ)⁻¹ * ∑ a, ∑ b, Complex.normSq (f i b a)) : ℝ) : ℂ) = 0 := by
        rw [← h]; push_cast; rfl
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; funext i; ext a; exact a.elim0
    have hNpos : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
    have hterm : ∀ i ∈ Finset.univ, r i * ((N : ℝ)⁻¹ * ∑ a, ∑ b, Complex.normSq (f i b a)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hr i).le (mul_nonneg hNpos.le
        (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)))).1 hreal
    funext i
    have h1 := hterm i (Finset.mem_univ _)
    have h2 : ∑ a, ∑ b, Complex.normSq (f i b a) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h (hr i).ne'
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hNpos.ne'
        · exact h
    ext b a
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)).1 h2 a (Finset.mem_univ _)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => Complex.normSq_nonneg _)).1 h3 b (Finset.mem_univ _)
    simpa using Complex.normSq_eq_zero.1 h4
  refine ⟨hsep, fun g hg => hsep g fun f => ?_⟩
  rw [wpair_symm]; exact hg f

/-- The pairing of `0`-forms of `eq:pairing` is `wpair` with the constant weight `a⁴` (`Differences.pair0`). -/
theorem wpair_form0 {n : ℕ} [NeZero n] (a : ℂ) (l l' : Form0 N n) :
    wpair (fun _ => a ^ 4) l l' = pair0 a l l' := rfl

/-! ### The pairing of `1`-forms -/

/-- `⟨A, A'⟩ = Σ_μ Σ_x a⁴ tr(A_μ(x)A'_μ(x))` on `1`-forms. -/
def pairForm1 {n : ℕ} [NeZero n] (a : ℂ) : BilinForm ℂ (Form1 N n) :=
  ∑ μ : Fin 4, (wpair (fun _ : Site n => a ^ 4)).compl₁₂ (LinearMap.proj μ) (LinearMap.proj μ)

lemma pairForm1_apply' {n : ℕ} [NeZero n] (a : ℂ) (A A' : Form1 N n) :
    pairForm1 a A A' = ∑ μ, wpair (fun _ : Site n => a ^ 4) (A μ) (A' μ) := by
  simp only [pairForm1, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]

theorem pairForm1_apply {n : ℕ} [NeZero n] (a : ℂ) (A A' : Form1 N n) : pairForm1 a A A' = pair1 a A A' := by
  rw [pairForm1_apply']; rfl

theorem pairForm1_symm {n : ℕ} [NeZero n] (a : ℂ) (A A' : Form1 N n) : pairForm1 a A A' = pairForm1 a A' A := by
  simp only [pairForm1_apply', wpair_symm]

/-- **The pairing of `1`-forms is nondegenerate** for `a > 0`. -/
theorem pairForm1_nondegenerate {n : ℕ} [NeZero n] {r : ℝ} (hr : 0 < r) :
    (pairForm1 (N := N) (n := n) (r : ℂ)).Nondegenerate := by
  have h0 := wpair_nondegenerate (N := N) (ι := Site n) (fun _ => r ^ 4) (fun _ => by positivity)
  have hsep : LinearMap.SeparatingLeft (pairForm1 (N := N) (n := n) (r : ℂ)) := by
    intro A hA
    funext μ
    apply h0.1
    intro l
    have h := hA (fun ν => if ν = μ then l else 0)
    rw [pairForm1_apply', Finset.sum_eq_single μ (fun ν _ hν => by simp [hν, ntr]) (by simp)] at h
    simpa using h
  refine ⟨hsep, fun g hg => hsep g fun f => ?_⟩
  rw [pairForm1_symm]; exact hg f

/-! ### The transpose -/

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- **The transpose** `T^T` of `T : E → F` with respect to nondegenerate forms `B_E`, `B_F`:
`B_E(T^Tμ, A) = B_F(μ, TA)`. -/
def transpose (BE : BilinForm ℂ E) (BF : BilinForm ℂ F) (hE : BE.Nondegenerate) (T : E →ₗ[ℂ] F) : F →ₗ[ℂ] E :=
  (BE.toDual hE).symm.toLinearMap ∘ₗ T.dualMap ∘ₗ BF

theorem transpose_spec (BE : BilinForm ℂ E) (BF : BilinForm ℂ F) (hE : BE.Nondegenerate) (T : E →ₗ[ℂ] F)
    (μ : F) (A : E) : BE (transpose BE BF hE T μ) A = BF μ (T A) := by
  simp only [transpose, LinearMap.comp_apply, LinearEquiv.coe_coe, BilinForm.apply_toDual_symm_apply,
    LinearMap.dualMap_apply]

/-- The transpose is unique. -/
theorem transpose_unique (BE : BilinForm ℂ E) (BF : BilinForm ℂ F) (hE : BE.Nondegenerate) (T : E →ₗ[ℂ] F)
    (S : F →ₗ[ℂ] E) (hS : ∀ μ A, BE (S μ) A = BF μ (T A)) : S = transpose BE BF hE T := by
  ext μ
  rw [← sub_eq_zero]
  apply hE.1
  intro A
  rw [map_sub, LinearMap.sub_apply, hS, transpose_spec, sub_self]

/-! ### The constraint form -/

/-- The multiplication by a weight, `μ ↦ (c ↦ v_c μ(c))`. -/
def mulW (v : ι → ℂ) : (ι → Mat) →ₗ[ℂ] (ι → Mat) where
  toFun μ i := v i • μ i
  map_add' μ ν := by funext i; simp [smul_add]
  map_smul' c μ := by funext i; simp [smul_comm c (v i)]

/-- **The constraint form** `eq:constraint-forms`: with the weights `w_c = a_c⁴` of `(·,·)_w`,
`𝖺Σ_c a_c²tr((QA)(c))² = ⟨A, Q^T(𝖺a_c^{-2})QA⟩`. -/
theorem constraint_form (BE : BilinForm ℂ E) (hE : BE.Nondegenerate) (ac : ι → ℂ) (hac : ∀ c, ac c ≠ 0)
    (Q : E →ₗ[ℂ] (ι → Mat)) (aa : ℂ) (A : E) :
    BE (transpose BE (wpair fun c => ac c ^ 4) hE Q (mulW (fun c => aa * (ac c ^ 2)⁻¹) (Q A))) A =
      aa * ∑ c, ac c ^ 2 * ntr ((Q A) c * (Q A) c) := by
  rw [transpose_spec, wpair_symm, wpair_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mulW, LinearMap.coe_mk, AddHom.coe_mk, mul_smul_comm, ntr, trace_smul, smul_eq_mul]
  have := hac c
  field_simp

end ConcretePairing
end CoreLean

end
