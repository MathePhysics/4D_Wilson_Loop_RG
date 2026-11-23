/-
`def:norms`(ii) of BALABAN_CORE.tex (`ea68ea6e3640`): the Hölder norm at the scale `j`,
`‖f‖^{(j)}_β = sup (|x - x'|₁/a_j)^{-β} ‖Ad_{𝐔(γ)} f_ι(x') - f_ι(x)‖` (`eq:holder`), the supremum over the
components `ι`, the pairs of sites `x ≠ x'` of `T^{(0)}` with `|x - x'|₁ ≤ a_j`, and the shortest paths `γ`
from `x` to `x'`; `‖f‖_β = ‖f‖^{(k)}_β` and `‖A‖_{1,β} = ‖∇_𝐔A‖_β` with the covariant gradient
`(∇_𝐔A)_{μν} = D_{𝐔,μ}A_ν` of `def:current`.

Model: the fine lattice of `Transports.lean` (`η = 1`, `a_j = Lʲ`, so `|x - x'|₁/a_j = d₁(x, x')/Lʲ`).
The set of the terms is finite (`holderTerms_finite`), so the supremum is a maximum, or `0` if there are no
pairs. Proved: the norm bounds each term (`le_holderNorm`), the bound by a number is the bound of all terms
(`holderNorm_le_iff`), it is the predicate `HolderU` of `HolderTransports.lean` at the scale `k`
(`holderU_iff`), and on scalar functions it does not depend on the configuration (`holderNorm_scalar`).
-/
import CoreLean.HolderTransports
import Mathlib.Data.Set.Finite.List

open scoped Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace CoreLean
namespace Transports

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

instance : Finite (Bond n) :=
  Finite.of_injective (fun b : Bond n => (b.site, b.dir, b.pos)) (by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl)

/-- The terms `(|x - x'|₁/a_j)^{-β} ‖Ad_{𝐔(γ)} f_ι(x') - f_ι(x)‖` of `eq:holder`. -/
def holderTerms {ι : Type*} (L j : ℕ) (U : Config N n) (β : ℝ) (f : ι → Site n → Mat) : Set ℝ :=
  {t | ∃ i x x' γ, x ≠ x' ∧ Blocks.d1 x x' ≤ L ^ j ∧ IsShortest x x' γ ∧
    t = ((Blocks.d1 x x' : ℝ) / (L : ℝ) ^ j) ^ (-β) * ‖Ad (U.hol γ) (f i x') - f i x‖}

/-- **The Hölder norm `‖f‖^{(j)}_β` of `eq:holder`.** -/
def holderNorm {ι : Type*} (L j : ℕ) (U : Config N n) (β : ℝ) (f : ι → Site n → Mat) : ℝ :=
  sSup (holderTerms L j U β f)

lemma holderTerms_finite {ι : Type*} {L j : ℕ} {U : Config N n} {β : ℝ} {f : ι → Site n → Mat} [Finite ι] : (holderTerms L j U β f).Finite := by
  refine ((Set.finite_univ (α := ι)).prod ((Set.finite_univ (α := Site n)).prod
    ((Set.finite_univ (α := Site n)).prod (List.finite_length_le (Bond n) (L ^ j))))).image
    (fun q => ((Blocks.d1 q.2.1 q.2.2.1 : ℝ) / (L : ℝ) ^ j) ^ (-β) *
      ‖Ad (U.hol q.2.2.2) (f q.1 q.2.2.1) - f q.1 q.2.1‖) |>.subset ?_
  rintro t ⟨i, x, x', γ, -, hd, hγ, rfl⟩
  refine ⟨(i, x, x', γ), ?_, rfl⟩
  simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [hγ.2.2]; exact hd

lemma holderTerms_nonneg {ι : Type*} {L j : ℕ} {U : Config N n} {β : ℝ} {f : ι → Site n → Mat} {t : ℝ} (ht : t ∈ holderTerms L j U β f) : 0 ≤ t := by
  obtain ⟨i, x, x', γ, -, -, -, rfl⟩ := ht
  positivity

lemma holderNorm_nonneg {ι : Type*} {L j : ℕ} {U : Config N n} {β : ℝ} {f : ι → Site n → Mat} : 0 ≤ holderNorm L j U β f :=
  Real.sSup_nonneg fun _ ht => holderTerms_nonneg ht

/-- The norm bounds every term of `eq:holder`. -/
theorem le_holderNorm {ι : Type*} {L j : ℕ} {U : Config N n} {β : ℝ} {f : ι → Site n → Mat} [Finite ι] (i : ι) {x x' : Site n} {γ : List (Bond n)} (hne : x ≠ x')
    (hd : Blocks.d1 x x' ≤ L ^ j) (hγ : IsShortest x x' γ) :
    ((Blocks.d1 x x' : ℝ) / (L : ℝ) ^ j) ^ (-β) * ‖Ad (U.hol γ) (f i x') - f i x‖ ≤ holderNorm L j U β f :=
  le_csSup holderTerms_finite.bddAbove ⟨i, x, x', γ, hne, hd, hγ, rfl⟩

/-- **`‖f‖^{(j)}_β ≤ H` iff every term of `eq:holder` is at most `H`.** -/
theorem holderNorm_le_iff {ι : Type*} {L j : ℕ} {U : Config N n} {β : ℝ} {f : ι → Site n → Mat} [Finite ι] {H : ℝ} (hH : 0 ≤ H) :
    holderNorm L j U β f ≤ H ↔ ∀ i x x' (γ : List (Bond n)), x ≠ x' → Blocks.d1 x x' ≤ L ^ j →
      IsShortest x x' γ → ((Blocks.d1 x x' : ℝ) / (L : ℝ) ^ j) ^ (-β) * ‖Ad (U.hol γ) (f i x') - f i x‖ ≤ H := by
  constructor
  · intro h i x x' γ hne hd hγ
    exact (le_holderNorm i hne hd hγ).trans h
  · intro h
    refine Real.sSup_le ?_ hH
    rintro t ⟨i, x, x', γ, hne, hd, hγ, rfl⟩
    exact h i x x' γ hne hd hγ

lemma d1_pos {x x' : Site n} (hne : x ≠ x') : 0 < Blocks.d1 x x' :=
  Nat.pos_of_ne_zero fun h => hne (eq_of_d1_eq_zero h)

/-- The term of `eq:holder` is at most `H` iff the transported difference is at most
`(|x - x'|₁/a_j)^β H`. -/
lemma term_le_iff {j : ℕ} {β : ℝ} {L : ℕ} {x x' : Site n} (hne : x ≠ x') (hL : 0 < L) (D H : ℝ) :
    ((Blocks.d1 x x' : ℝ) / (L : ℝ) ^ j) ^ (-β) * D ≤ H ↔
      D ≤ ((Blocks.d1 x x' : ℝ) / (L : ℝ) ^ j) ^ β * H := by
  have hr : 0 < (Blocks.d1 x x' : ℝ) / (L : ℝ) ^ j := by
    have := d1_pos hne
    positivity
  rw [Real.rpow_neg hr.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hr β)]

/-- **The transported differences are bounded by the norm**:
`‖Ad_{𝐔(γ)} f_ι(x') - f_ι(x)‖ ≤ (|x - x'|₁/a_j)^β ‖f‖^{(j)}_β`. -/
theorem norm_sub_le_holderNorm {ι : Type*} {L j : ℕ} {U : Config N n} {β : ℝ} {f : ι → Site n → Mat} [Finite ι] (hL : 0 < L) (i : ι) {x x' : Site n} {γ : List (Bond n)}
    (hne : x ≠ x') (hd : Blocks.d1 x x' ≤ L ^ j) (hγ : IsShortest x x' γ) :
    ‖Ad (U.hol γ) (f i x') - f i x‖ ≤ ((Blocks.d1 x x' : ℝ) / (L : ℝ) ^ j) ^ β * holderNorm L j U β f :=
  (term_le_iff hne hL _ _).1 (le_holderNorm i hne hd hγ)

/-- **The predicate `HolderU` of `HolderTransports.lean` is the bound of the norm `‖f‖_β = ‖f‖^{(k)}_β`.** -/
theorem holderU_iff (S : Blocks.DomSeq n) (g : Site n → Mat) (U : Config N n) (β : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    HolderU S g U β H ↔ holderNorm S.L S.k U β (fun _ : Unit => g) ≤ H := by
  have hL : 0 < S.L := by have := S.three_le_L; omega
  rw [holderNorm_le_iff hH]
  constructor
  · intro h _ x x' γ hne hd hγ
    exact (term_le_iff hne hL _ _).2 (h x x' γ hne hd hγ)
  · intro h x x' γ hne hd hγ
    exact (term_le_iff hne hL _ _).1 (h () x x' γ hne hd hγ)

lemma Ad_smul_one (W : GLN) (c : ℂ) : Ad W (c • (1 : Mat)) = c • (1 : Mat) := by
  simp only [Ad, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- **On scalar functions the norm does not depend on the configuration.** -/
theorem holderNorm_scalar {ι : Type*} {L j : ℕ} {β : ℝ} (c : ι → Site n → ℂ) (U U' : Config N n) :
    holderNorm L j U β (fun i x => c i x • (1 : Mat)) = holderNorm L j U' β (fun i x => c i x • (1 : Mat)) := by
  simp only [holderNorm, holderTerms, Ad_smul_one]

/-- The covariant gradient `(∇_𝐔A)_{μν} = D_{𝐔,μ}A_ν` of `def:current`, with the spacing `a`. -/
def gradU (a : ℂ) (U : Config N n) (A : Form1 N n) : Fin 4 × Fin 4 → Form0 N n :=
  fun q => Dfw a U q.1 (A q.2)

/-- `‖f‖_β = ‖f‖^{(k)}_β`. -/
def holderK {ι : Type*} (L k : ℕ) (U : Config N n) (β : ℝ) (f : ι → Site n → Mat) : ℝ := holderNorm L k U β f

/-- `‖A‖_{1,β} = ‖∇_𝐔A‖_β` for a `1`-form `A`. -/
def holder1 (a : ℂ) (L k : ℕ) (U : Config N n) (β : ℝ) (A : Form1 N n) : ℝ := holderK L k U β (gradU a U A)

end Transports
end CoreLean

end
