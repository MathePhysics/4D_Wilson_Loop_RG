/-
`prop:interior-schauder` of BALABAN_CORE.tex (`a71f8998da10`), first part: the hypotheses, the modulus of
`χλ`, and the bound of the remainder `r` of the localised equation
`(Δ + a⁻²)w = Σ_κ ∂^*_κ(χλ_κ) + r`, `w = χv` (`eq:schauder-equation` with `ρ` in the place of
`-Q'^*𝖺Q'v`).

Units: the lattice is `ηℤ⁴`, represented by `ℤ⁴`, with `a = Kη`, `K ≥ 1` an integer (`a = a_j = L^jη`); the
cube `{x | |x - y|_∞ ≤ R/2}` is `InQ y R` (`2|n - y|_∞ ≤ R` in the units of the lattice), so that `Q_y` is
`InQ y (8K)`, the points of (i) are `InQ y (5K)`, and the set of the conclusion is `InQ y (4K - 2)`
(`|x - y|_∞ ≤ 2a - η`).

* `Hyp`: the hypotheses of the proposition: `a‖𝐚‖ ≤ 1/32` and `a²‖∂𝐚‖ ≤ 1/32` on the bonds of `Q_y`, (i), (ii),
  and (iii), with the sum `Σ_κ D^*_{𝐔,κ}λ_κ` of the last statement of the proposition.
* `holder_chi_lam`: `‖(χλ_κ)(n + m) - (χλ_κ)(n)‖ ≤ 6Λ_κ(|m|₁/K)^β` for all `n`, `m` (the core: `6Λ₀`).
* `norm_rem_le`: `‖r(n)‖ ≤ a⁻¹(5Σ_κΛ_κ + 166V)` at every point.
-/
import CoreLean.InteriorCutoff
import CoreLean.ResolventEquation

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace InteriorSchauder

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `2|n - y|_∞ ≤ R`. -/
def InQ (y : Fin 4 → ℤ) (R : ℤ) (n : Fin 4 → ℤ) : Prop := ∀ μ, 2 * |n μ - y μ| ≤ R

lemma InQ.mono {y : Fin 4 → ℤ} {R R' : ℤ} {n : Fin 4 → ℤ} (h : InQ y R n) (hR : R ≤ R') : InQ y R' n :=
  fun μ => (h μ).trans hR

/-- A point within one step of a point of `InQ y R` lies in `InQ y (R + 2)`. -/
lemma InQ.step {y : Fin 4 → ℤ} {R : ℤ} {n : Fin 4 → ℤ} (h : InQ y R n) (ν : Fin 4) (c : ℤ) (hc : |c| ≤ 1) :
    InQ y (R + 2) (n + c • e4 ν) := fun μ => by
  have := h μ
  by_cases hμ : μ = ν
  · subst hμ
    simp only [Pi.add_apply, Pi.smul_apply, e4, Pi.single_eq_same, smul_eq_mul, mul_one]
    have h1 := abs_add_le (n μ - y μ) c
    rw [show n μ - y μ + c = n μ + c - y μ by ring] at h1
    omega
  · simp only [Pi.add_apply, Pi.smul_apply, e4, Pi.single_eq_of_ne hμ, smul_zero, add_zero]
    omega

lemma InQ.add_e {y : Fin 4 → ℤ} {R : ℤ} {n : Fin 4 → ℤ} (h : InQ y R n) (ν : Fin 4) :
    InQ y (R + 2) (n + e4 ν) := by
  have := h.step ν 1 (by norm_num); simpa using this

lemma InQ.sub_e {y : Fin 4 → ℤ} {R : ℤ} {n : Fin 4 → ℤ} (h : InQ y R n) (ν : Fin 4) :
    InQ y (R + 2) (n - e4 ν) := by
  have := h.step ν (-1) (by norm_num); simpa [sub_eq_add_neg] using this

lemma Ad_real_smul (W : GLN) (c : ℝ) (X : Mat) : Ad W (c • X) = c • Ad W X := by
  unfold Ad; rw [Matrix.mul_smul, Matrix.smul_mul]

lemma norm_Ad_le_of_sub {W : GLN} {δ : ℝ} (h : ∀ Z : Mat, ‖Ad W Z - Z‖ ≤ δ * ‖Z‖) (Z : Mat) :
    ‖Ad W Z‖ ≤ (1 + δ) * ‖Z‖ := by
  have := norm_add_le (Ad W Z - Z) Z
  rw [sub_add_cancel] at this
  linarith [h Z]

/-- The hypotheses of `prop:interior-schauder`, with `a = Kη`. -/
structure Hyp (η : ℝ) (K : ℕ) (y : Fin 4 → ℤ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (v : (Fin 4 → ℤ) → Mat)
    (lam : Fin 4 → (Fin 4 → ℤ) → Mat) (rho : (Fin 4 → ℤ) → Mat) (V : ℝ) (Λ : Fin 4 → ℝ) (β : ℝ) : Prop where
  hη : 0 < η
  hK : 1 ≤ K
  /-- `a‖𝐚‖_∞ ≤ 1/32` on the bonds of `Q_y`. -/
  hA : ∀ μ n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 μ) → (K * η) * ‖A μ n‖ ≤ 1 / 32
  /-- `a²‖∂𝐚‖_∞ ≤ 1/32` for the differences formed with bonds of `Q_y`. -/
  hdA : ∀ μ ν n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 ν) → InQ y (8 * K) (n + e4 μ) →
    InQ y (8 * K) (n + e4 ν + e4 μ) → (K * η) ^ 2 * ‖dfw η ν (A μ) n‖ ≤ 1 / 32
  /-- (i): `Δ_𝐔v = Σ_κ D^*_{𝐔,κ}λ_κ + ρ` at the points with `|x - y|_∞ ≤ 5a/2`. -/
  heq : ∀ n, InQ y (5 * K) n → covLap η A v n = ∑ κ, Dbw η A κ (lam κ) n + rho n
  /-- (ii) -/
  hv : ∀ n, InQ y (8 * K) n → ‖v n‖ ≤ V * (K * η)
  hDv : ∀ ν n, InQ y (8 * K) n → InQ y (8 * K) (n + e4 ν) → ‖Dfw η A ν v n‖ ≤ V
  hrho : ∀ n, InQ y (8 * K) n → ‖rho n‖ ≤ V / (K * η)
  hlam : ∀ κ n, InQ y (8 * K) n → ‖lam κ n‖ ≤ Λ κ
  /-- (iii), along every shortest path. -/
  hhol : ∀ κ x x' l, InQ y (8 * K) x → InQ y (8 * K) x' → l1 (x' - x) ≤ K → IsShortest x x' l →
    ‖Ad (pathT η A (sgnv x x') x l) (lam κ x') - lam κ x‖ ≤ Λ κ * (η * l1 (x' - x) / (K * η)) ^ β

namespace Hyp

variable {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {rho : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {V : ℝ} {Λ : Fin 4 → ℝ} {β : ℝ}
  (H : Hyp η K y A v lam rho V Λ β)
include H

lemma K_pos : (0 : ℝ) < K := by have := H.hK; exact_mod_cast this

lemma a_pos : 0 < (K : ℝ) * η := mul_pos H.K_pos H.hη

lemma η_le_a : η ≤ (K : ℝ) * η := by
  have : (1 : ℝ) ≤ K := by exact_mod_cast H.hK
  nlinarith [H.hη]

lemma inQ_self (R : ℤ) (hR : 0 ≤ R) : InQ y R y := fun μ => by simp [hR]

lemma V_nonneg : 0 ≤ V := by
  have h := H.hv y (H.inQ_self _ (by have := H.hK; omega))
  have ha := H.a_pos
  by_contra hV; push_neg at hV
  nlinarith [norm_nonneg (v y)]

lemma Λ_nonneg (κ : Fin 4) : 0 ≤ Λ κ :=
  (norm_nonneg (lam κ y)).trans (H.hlam κ y (H.inQ_self _ (by have := H.hK; omega)))

/-- A bond of `Q_y` changes a value by at most `η/(4a)` times its norm. -/
lemma bondF {μ : Fin 4} {n : Fin 4 → ℤ} (h1 : InQ y (8 * K) n) (h2 : InQ y (8 * K) (n + e4 μ)) (Z : Mat) :
    ‖Ad (Uf η A μ n) Z - Z‖ ≤ η / (4 * (K * η)) * ‖Z‖ :=
  norm_Ad_Uf_sub_le' H.hη H.η_le_a (H.hA μ n h1 h2) Z

lemma bondB {μ : Fin 4} {n : Fin 4 → ℤ} (h1 : InQ y (8 * K) (n - e4 μ)) (h2 : InQ y (8 * K) n) (Z : Mat) :
    ‖Ad (Ub η A μ n) Z - Z‖ ≤ η / (4 * (K * η)) * ‖Z‖ :=
  norm_Ad_Ub_sub_le' H.hη H.η_le_a (H.hA μ (n - e4 μ) h1 (by rwa [sub_add_cancel])) Z

lemma η_div_le : η / (4 * (K * η)) ≤ 1 / 4 := by
  rw [div_le_div_iff₀ (by have := H.a_pos; positivity) (by norm_num)]
  nlinarith [H.η_le_a, H.hη]

lemma ηinv_mul_δ : η⁻¹ * (η / (4 * (K * η))) = 1 / (4 * (K * η)) := by
  have := H.hη.ne'; field_simp

/-! ### The cutoff in these units -/

lemma inQ_of_chi_ne {n : Fin 4 → ℤ} (h : chiK K y n ≠ 0) : InQ y (5 * K - 1) n := fun μ => by
  have h1 := abs_lt_of_chiK_ne_zero H.hK h μ
  have h2 : 2 * |n μ - y μ| < 5 * (K : ℤ) := by
    by_contra hc
    push_neg at hc
    have h3 : ((5 * K : ℤ) : ℝ) ≤ ((2 * |n μ - y μ| : ℤ) : ℝ) := by exact_mod_cast hc
    simp only [Int.cast_mul, Int.cast_abs, Int.cast_ofNat, Int.cast_natCast] at h3
    linarith
  omega

lemma chi_eq_one_of {n : Fin 4 → ℤ} (h : InQ y (4 * K) n) : chiK K y n = 1 :=
  chiK_eq_one H.hK fun μ => by
    have := h μ
    rw [← Int.cast_abs]
    have h2 : |n μ - y μ| ≤ 2 * (K : ℤ) := by omega
    exact_mod_cast h2

lemma abs_dfw_chi (n : Fin 4 → ℤ) (ν : Fin 4) : |dfw η ν (chiK K y) n| ≤ 3 / (K * η) := by
  unfold dfw
  rw [smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 H.hη)]
  have := abs_chiK_shift_sub_le H.hK y n ν 1 (by norm_num)
  simp only [one_smul] at this
  calc η⁻¹ * |chiK K y (n + e4 ν) - chiK K y n| ≤ η⁻¹ * (3 / K) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 H.hη.le)
    _ = 3 / (K * η) := by have := H.hη.ne'; field_simp

lemma abs_dbw_chi (n : Fin 4 → ℤ) (ν : Fin 4) : |dbw η ν (chiK K y) n| ≤ 3 / (K * η) := by
  unfold dbw
  rw [smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 H.hη)]
  have := abs_chiK_shift_sub_le H.hK y n ν (-1) (by norm_num)
  simp only [neg_smul, one_smul, ← sub_eq_add_neg] at this
  calc η⁻¹ * |chiK K y (n - e4 ν) - chiK K y n| ≤ η⁻¹ * (3 / K) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 H.hη.le)
    _ = 3 / (K * η) := by have := H.hη.ne'; field_simp

lemma abs_dbw_dfw_chi (n : Fin 4 → ℤ) (ν : Fin 4) :
    |dbw η ν (dfw η ν (chiK K y)) n| ≤ 24 / (K * η) ^ 2 := by
  have e : dbw η ν (dfw η ν (chiK K y)) n =
      -(η ^ 2)⁻¹ * (chiK K y (n + e4 ν) - 2 * chiK K y n + chiK K y (n - e4 ν)) := by
    unfold dbw dfw
    simp only [smul_eq_mul, sub_add_cancel]
    have := H.hη.ne'; field_simp; ring
  rw [e, abs_mul, abs_neg, abs_of_pos (by have := H.hη; positivity)]
  calc (η ^ 2)⁻¹ * |chiK K y (n + e4 ν) - 2 * chiK K y n + chiK K y (n - e4 ν)| ≤
        (η ^ 2)⁻¹ * (24 / (K : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_chiK_second_le H.hK y n ν) (by have := H.hη; positivity)
    _ = 24 / (K * η) ^ 2 := by have := H.hη.ne'; have := H.K_pos.ne'; field_simp

end Hyp

/-! ### Shortest paths in a cube -/

lemma sgnv_cases (x x' : Fin 4 → ℤ) (μ : Fin 4) : sgnv x x' μ = 1 ∨ sgnv x x' μ = -1 ∨ sgnv x x' μ = 0 := by
  unfold sgnv
  rcases Int.sign_trichotomy (x' μ - x μ) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

/-- The points of a shortest path between two points of a cube lie in the cube, with the next point. -/
lemma walk_inQ {y x x' : Fin 4 → ℤ} {l : List (Fin 4)} (hl : IsShortest x x' l) {R : ℤ} (hx : InQ y R x)
    (hx' : InQ y R x') :
    WalkIn (sgnv x x') (fun p μ => InQ y R p ∧ InQ y R (p + sgnv x x' μ • e4 μ) ∧ sgnv x x' μ ≠ 0) x l := by
  have h0 : ∀ μ, sgnv x x' μ = 0 → l.count μ = 0 := fun μ h => by
    rw [hl μ]; unfold sgnv at h; rw [Int.sign_eq_zero_iff_zero] at h; rw [h]; rfl
  have hbox := walkIn_box (sgnv x x') (sgnv_cases x x') l x h0
  have hend : ∀ μ, x μ + sgnv x x' μ * (l.count μ : ℤ) = x' μ := fun μ => by
    rw [hl μ, sgnv, Int.natCast_natAbs, Int.sign_mul_abs]; ring
  have key : ∀ p, InBox x (sgnv x x') (fun μ => l.count μ) p → InQ y R p := fun p hp μ => by
    obtain ⟨h1, h2⟩ := hp μ
    simp only [hend μ] at h1 h2
    have a1 := hx μ
    have a2 := hx' μ
    rcases abs_cases (p μ - y μ) with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;>
      rcases abs_cases (x μ - y μ) with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
      rcases abs_cases (x' μ - y μ) with ⟨e3, f3⟩ | ⟨e3, f3⟩ <;>
      rw [e1] <;> rw [e2] at a1 <;> rw [e3] at a2 <;> omega
  exact WalkIn.mono (fun p μ ⟨h1, h2, h3⟩ => ⟨key p h1, key _ h2, h3⟩) l x hbox

lemma length_eq_l1 {x x' : Fin 4 → ℤ} {l : List (Fin 4)} (hl : IsShortest x x' l) :
    (l.length : ℝ) = l1 (x' - x) := by
  rw [length_of_shortest hl, l1]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs]
  simp

lemma le_rpow_self {x β : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) : x ≤ x ^ β := by
  rcases eq_or_lt_of_le hx0 with h | h
  · rw [← h, Real.zero_rpow hβ0.ne']
  · have := Real.rpow_le_rpow_of_exponent_ge h hx1 hβ1
    rwa [Real.rpow_one] at this

lemma min_le_rpow {x β : ℝ} (hx0 : 0 ≤ x) (hβ0 : 0 < β) (hβ1 : β ≤ 1) {d : ℝ} (hd1 : d ≤ 1) (hd3 : d ≤ 3 * x) :
    d ≤ 4 * x ^ β := by
  rcases le_total x 1 with h | h
  · have := le_rpow_self hx0 h hβ0 hβ1; linarith [Real.rpow_nonneg hx0 β]
  · have := Real.one_le_rpow h hβ0.le; linarith

namespace Hyp

variable {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {rho : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {V : ℝ} {Λ : Fin 4 → ℝ} {β : ℝ}
  (H : Hyp η K y A v lam rho V Λ β)
include H

/-- The transport along a shortest path of `Q_y` of length `≤ a` changes a value by at most `|x' - x|₁/a`
times its norm. -/
lemma path_dev {x x' : Fin 4 → ℤ} {l : List (Fin 4)} (hl : IsShortest x x' l) (hx : InQ y (8 * K) x)
    (hx' : InQ y (8 * K) x') (hlen : l1 (x' - x) ≤ K) (Z : Matrix (Fin N) (Fin N) ℂ) :
    ‖Ad (pathT η A (sgnv x x') x l) Z - Z‖ ≤ l1 (x' - x) / K * ‖Z‖ := by
  have hK := H.K_pos
  have hw := walk_inQ hl hx hx'
  set δ := η / (4 * (K * η)) with hδ
  have hδ0 : 0 ≤ δ := by have := H.hη; have := H.a_pos; positivity
  have hb : WalkIn (sgnv x x') (fun p μ => ∀ Z, ‖Ad (bondT η A (sgnv x x') μ p) Z - Z‖ ≤ δ * ‖Z‖) x l :=
    WalkIn.mono (fun p μ ⟨h1, h2, h3⟩ => fun Z => by
      unfold bondT
      rcases sgnv_cases x x' μ with hs | hs | hs
      · rw [if_pos (by rw [hs]; norm_num)]
        rw [hs, one_smul] at h2
        exact H.bondF h1 h2 Z
      · rw [if_neg (by rw [hs]; norm_num)]
        rw [hs, neg_one_smul, ← sub_eq_add_neg] at h2
        exact H.bondB h2 h1 Z
      · exact absurd hs h3) l x hw
  have hdev := norm_Ad_pathT_sub_le η A _ hδ0 l x hb Z
  have hL := length_eq_l1 hl
  have hlδ : (l.length : ℝ) * δ = l1 (x' - x) / (4 * K) := by
    rw [hL, hδ]; have := H.hη.ne'; field_simp
  have hle : (l.length : ℝ) * δ ≤ 1 := by
    rw [hlδ, div_le_one (by positivity)]; linarith [l1_nonneg (x' - x)]
  have := one_add_pow_sub_one_le hδ0 hle
  calc ‖Ad (pathT η A (sgnv x x') x l) Z - Z‖ ≤ ((1 + δ) ^ l.length - 1) * ‖Z‖ := hdev
    _ ≤ 2 * (l.length * δ) * ‖Z‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ ≤ l1 (x' - x) / K * ‖Z‖ := by
        rw [hlδ]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [show 2 * (l1 (x' - x) / (4 * K)) = l1 (x' - x) / K / 2 by field_simp; ring]
        linarith [div_nonneg (l1_nonneg (x' - x)) hK.le]

lemma holder_rewrite (m : ℝ) : η * m / (K * η) = m / K := by
  have := H.hη.ne'; field_simp

/-- The modulus of `λ_κ` without transport, from (iii). -/
lemma lam_holder (hβ0 : 0 < β) (hβ1 : β ≤ 1) (κ : Fin 4) {n n' : Fin 4 → ℤ} (hn : InQ y (8 * K) n)
    (hn' : InQ y (8 * K) n') : ‖lam κ n' - lam κ n‖ ≤ 2 * Λ κ * (l1 (n' - n) / K) ^ β := by
  have hK := H.K_pos
  have hΛ := H.Λ_nonneg κ
  have hx0 : 0 ≤ l1 (n' - n) / K := div_nonneg (l1_nonneg _) hK.le
  by_cases hlen : l1 (n' - n) ≤ K
  · obtain ⟨l, hl⟩ := exists_shortest n n'
    have h1 := H.hhol κ n n' l hn hn' hlen hl
    rw [H.holder_rewrite] at h1
    have h2 := H.path_dev hl hn hn' hlen (lam κ n')
    generalize hP : pathT η A (sgnv n n') n l = P at h1 h2
    have hx1 : l1 (n' - n) / K ≤ 1 := (div_le_one hK).2 hlen
    have h3 := le_rpow_self hx0 hx1 hβ0 hβ1
    have h4 := H.hlam κ n' hn'
    have h5 : ‖Ad P (lam κ n') - lam κ n'‖ ≤ l1 (n' - n) / K * Λ κ :=
      h2.trans (mul_le_mul_of_nonneg_left h4 hx0)
    have h6 : l1 (n' - n) / K * Λ κ ≤ Λ κ * (l1 (n' - n) / K) ^ β := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left h3 hΛ
    have e : lam κ n' - lam κ n = (Ad P (lam κ n') - lam κ n) - (Ad P (lam κ n') - lam κ n') := by abel
    rw [e]
    have := norm_sub_le (Ad P (lam κ n') - lam κ n) (Ad P (lam κ n') - lam κ n')
    linarith
  · push_neg at hlen
    have hx1 : 1 ≤ l1 (n' - n) / K := (one_le_div hK).2 hlen.le
    have h3 := Real.one_le_rpow hx1 hβ0.le
    calc ‖lam κ n' - lam κ n‖ ≤ ‖lam κ n'‖ + ‖lam κ n‖ := norm_sub_le _ _
      _ ≤ Λ κ + Λ κ := add_le_add (H.hlam κ n' hn') (H.hlam κ n hn)
      _ ≤ 2 * Λ κ * (l1 (n' - n) / K) ^ β := by
          have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * Λ κ)
          linarith

end Hyp

/-! ### The localised functions -/

/-- `w = χv`. -/
def wloc (K : ℕ) (y : Fin 4 → ℤ) (v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) :
    Matrix (Fin N) (Fin N) ℂ :=
  chiK K y n • v n

/-- `χλ_κ`. -/
def chiLam (K : ℕ) (y : Fin 4 → ℤ) (lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (κ : Fin 4)
    (n : Fin 4 → ℤ) : Matrix (Fin N) (Fin N) ℂ :=
  chiK K y n • lam κ n

/-- The remainder `r = (Δ + a⁻²)w - Σ_κ ∂^*_κ(χλ_κ)` of `eq:schauder-equation`. -/
def rem (η : ℝ) (K : ℕ) (y : Fin 4 → ℤ) (v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (n : Fin 4 → ℤ) : Matrix (Fin N) (Fin N) ℂ :=
  lap η (wloc K y v) n + ((K * η) ^ 2)⁻¹ • wloc K y v n - ∑ κ, dbw η κ (chiLam K y lam κ) n

namespace Hyp

variable {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {rho : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {V : ℝ} {Λ : Fin 4 → ℝ} {β : ℝ}
  (H : Hyp η K y A v lam rho V Λ β)
include H

lemma norm_wloc_le (n : Fin 4 → ℤ) : ‖wloc K y v n‖ ≤ V * (K * η) := by
  unfold wloc
  by_cases h : chiK K y n = 0
  · rw [h, zero_smul, norm_zero]; exact mul_nonneg H.V_nonneg H.a_pos.le
  · rw [norm_smul, Real.norm_of_nonneg (chiK_nonneg y n)]
    have := H.hv n ((H.inQ_of_chi_ne h).mono (by omega))
    calc chiK K y n * ‖v n‖ ≤ 1 * (V * (K * η)) :=
          mul_le_mul (chiK_le_one y n) this (norm_nonneg _) zero_le_one
      _ = V * (K * η) := one_mul _

lemma norm_chiLam_le (κ : Fin 4) (n : Fin 4 → ℤ) : ‖chiLam K y lam κ n‖ ≤ Λ κ := by
  unfold chiLam
  by_cases h : chiK K y n = 0
  · rw [h, zero_smul, norm_zero]; exact H.Λ_nonneg κ
  · rw [norm_smul, Real.norm_of_nonneg (chiK_nonneg y n)]
    have := H.hlam κ n ((H.inQ_of_chi_ne h).mono (by omega))
    calc chiK K y n * ‖lam κ n‖ ≤ 1 * Λ κ := mul_le_mul (chiK_le_one y n) this (norm_nonneg _) zero_le_one
      _ = Λ κ := one_mul _

/-- **The modulus of `χλ`**: `‖(χλ_κ)(n + m) - (χλ_κ)(n)‖ ≤ 6Λ_κ(|m|₁/K)^β` for all `n`, `m`. -/
theorem holder_chi_lam (hβ0 : 0 < β) (hβ1 : β ≤ 1) (κ : Fin 4) (n m : Fin 4 → ℤ) :
    ‖chiLam K y lam κ (n + m) - chiLam K y lam κ n‖ ≤ 6 * Λ κ * (l1 m / K) ^ β := by
  have hK := H.K_pos
  have hΛ := H.Λ_nonneg κ
  set t := (l1 m / K) ^ β with ht
  have hx0 : 0 ≤ l1 m / K := div_nonneg (l1_nonneg _) hK.le
  have ht0 : 0 ≤ t := Real.rpow_nonneg hx0 β
  -- the change of `χ`
  have hchi : |chiK K y (n + m) - chiK K y n| ≤ 4 * t := by
    refine min_le_rpow hx0 hβ0 hβ1 ?_ ?_
    · rw [abs_le]; constructor <;> linarith [chiK_nonneg (K := K) y (n + m), chiK_le_one (K := K) y (n + m),
        chiK_nonneg (K := K) y n, chiK_le_one (K := K) y n]
    · have := abs_chiK_add_sub_le H.hK y n m
      calc _ ≤ 3 / K * l1 m := this
        _ = 3 * (l1 m / K) := by ring
  unfold chiLam
  by_cases h1 : chiK K y (n + m) = 0
  · by_cases h2 : chiK K y n = 0
    · rw [h1, h2, zero_smul, zero_smul, sub_zero, norm_zero]; positivity
    · rw [h1, zero_smul, zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg (chiK_nonneg y n)]
      have hl := H.hlam κ n ((H.inQ_of_chi_ne h2).mono (by omega))
      rw [h1, zero_sub, abs_neg, abs_of_nonneg (chiK_nonneg y n)] at hchi
      calc chiK K y n * ‖lam κ n‖ ≤ (4 * t) * Λ κ := mul_le_mul hchi hl (norm_nonneg _) (by positivity)
        _ ≤ 6 * Λ κ * t := by nlinarith
  · have hn' : InQ y (8 * K) (n + m) := (H.inQ_of_chi_ne h1).mono (by omega)
    by_cases h2 : chiK K y n = 0
    · rw [h2, zero_smul, sub_zero, norm_smul, Real.norm_of_nonneg (chiK_nonneg y (n + m))]
      have hl := H.hlam κ (n + m) hn'
      rw [h2, sub_zero, abs_of_nonneg (chiK_nonneg y (n + m))] at hchi
      calc chiK K y (n + m) * ‖lam κ (n + m)‖ ≤ (4 * t) * Λ κ :=
            mul_le_mul hchi hl (norm_nonneg _) (by positivity)
        _ ≤ 6 * Λ κ * t := by nlinarith
    · have hn : InQ y (8 * K) n := (H.inQ_of_chi_ne h2).mono (by omega)
      have hlh := H.lam_holder hβ0 hβ1 κ hn hn'
      rw [add_sub_cancel_left] at hlh
      have e : chiK K y (n + m) • lam κ (n + m) - chiK K y n • lam κ n =
          chiK K y (n + m) • (lam κ (n + m) - lam κ n) + (chiK K y (n + m) - chiK K y n) • lam κ n := by
        rw [smul_sub, sub_smul]; abel
      rw [e]
      have hl := H.hlam κ n hn
      calc _ ≤ ‖chiK K y (n + m) • (lam κ (n + m) - lam κ n)‖ +
            ‖(chiK K y (n + m) - chiK K y n) • lam κ n‖ := norm_add_le _ _
        _ ≤ 1 * (2 * Λ κ * t) + (4 * t) * Λ κ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (chiK_nonneg y (n + m)), Real.norm_eq_abs]
            gcongr
            exact chiK_le_one y (n + m)
        _ = 6 * Λ κ * t := by ring

end Hyp



/-! ### Identities of the differences of products -/

section Identities

variable {η : ℝ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}

lemma Dfw_smul (hη : η ≠ 0) (χ : (Fin 4 → ℤ) → ℝ) (v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (ν : Fin 4)
    (m : Fin 4 → ℤ) :
    Dfw η A ν (fun k => χ k • v k) m =
      χ m • Dfw η A ν v m + dfw η ν χ m • Ad (Uf η A ν m) (v (m + e4 ν)) := by
  unfold Dfw dfw
  rw [Ad_real_smul, smul_eq_mul]
  module

/-- `[Δ_𝐔, χ]v` in the direction `ν`. -/
lemma commutator_eq (hη : η ≠ 0) (χ : (Fin 4 → ℤ) → ℝ) (v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (ν : Fin 4) (n : Fin 4 → ℤ) :
    Dbw η A ν (Dfw η A ν (fun k => χ k • v k)) n - χ n • Dbw η A ν (Dfw η A ν v) n =
      dbw η ν χ n • Ad (Ub η A ν n) (Dfw η A ν v (n - e4 ν)) + dbw η ν (dfw η ν χ) n • v n -
        dfw η ν χ n • Dfw η A ν v n := by
  have hD : Dfw η A ν (fun k => χ k • v k) =
      fun m => χ m • Dfw η A ν v m + dfw η ν χ m • Ad (Uf η A ν m) (v (m + e4 ν)) :=
    funext fun m => Dfw_smul hη χ v ν m
  rw [hD]
  have hback : Ad (Ub η A ν n) (Ad (Uf η A ν (n - e4 ν)) (v (n - e4 ν + e4 ν))) = v n := by
    have := Ad_Ub_Ad_Uf η A ν (n - e4 ν) (v (n - e4 ν + e4 ν))
    rwa [sub_add_cancel] at this ⊢
  have hDv : Dfw η A ν v n = η⁻¹ • (Ad (Uf η A ν n) (v (n + e4 ν)) - v n) := rfl
  unfold Dbw dbw
  simp only [Ad_add, Ad_real_smul, hback]
  unfold dfw
  rw [hDv]
  simp only [smul_eq_mul, smul_sub, smul_add, smul_smul]
  module

end Identities

namespace Hyp

variable {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {rho : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {V : ℝ} {Λ : Fin 4 → ℝ} {β : ℝ}
  (H : Hyp η K y A v lam rho V Λ β)
include H

omit H in
lemma norm_rsmul (c : ℝ) (X : Matrix (Fin N) (Fin N) ℂ) : ‖c • X‖ = |c| * ‖X‖ := by
  rw [norm_smul, Real.norm_eq_abs]

lemma near_of_chi {n : Fin 4 → ℤ} (h : chiK K y n ≠ 0) (ν : Fin 4) :
    InQ y (8 * K) n ∧ InQ y (8 * K) (n + e4 ν) ∧ InQ y (8 * K) (n - e4 ν) := by
  have h1 := H.inQ_of_chi_ne h
  have hK := H.hK
  refine ⟨h1.mono (by omega), (h1.add_e ν).mono (by omega), (h1.sub_e ν).mono (by omega)⟩

/-- `Ad` along a bond of `Q_y` enlarges the norm by at most `5/4`. -/
lemma norm_Ad_Uf_le {μ : Fin 4} {n : Fin 4 → ℤ} (h1 : InQ y (8 * K) n) (h2 : InQ y (8 * K) (n + e4 μ))
    (Z : Matrix (Fin N) (Fin N) ℂ) : ‖Ad (Uf η A μ n) Z‖ ≤ 5 / 4 * ‖Z‖ := by
  have := norm_Ad_le_of_sub (H.bondF h1 h2) Z
  have h := H.η_div_le
  nlinarith [norm_nonneg Z]

lemma norm_Ad_Ub_le {μ : Fin 4} {n : Fin 4 → ℤ} (h1 : InQ y (8 * K) (n - e4 μ)) (h2 : InQ y (8 * K) n)
    (Z : Matrix (Fin N) (Fin N) ℂ) : ‖Ad (Ub η A μ n) Z‖ ≤ 5 / 4 * ‖Z‖ := by
  have := norm_Ad_le_of_sub (H.bondB h1 h2) Z
  have h := H.η_div_le
  nlinarith [norm_nonneg Z]

/-- `‖D_{𝐔,ν}w‖ ≤ 7V` at every point. -/
lemma norm_Dfw_w_le (ν : Fin 4) (m : Fin 4 → ℤ) : ‖Dfw η A ν (wloc K y v) m‖ ≤ 7 * V := by
  have hV := H.V_nonneg
  have ha := H.a_pos
  by_cases hfar : chiK K y m = 0 ∧ chiK K y (m + e4 ν) = 0
  · have : Dfw η A ν (wloc K y v) m = 0 := by
      unfold Dfw wloc; rw [hfar.1, hfar.2]; simp [Ad]
    rw [this, norm_zero]; positivity
  have hm : InQ y (8 * K) m ∧ InQ y (8 * K) (m + e4 ν) := by
    rcases not_and_or.1 hfar with h | h
    · exact ⟨(H.near_of_chi h ν).1, (H.near_of_chi h ν).2.1⟩
    · have h3 := H.near_of_chi h ν
      exact ⟨by simpa using h3.2.2, h3.1⟩
  unfold wloc
  rw [Dfw_smul H.hη.ne']
  refine (norm_add_le _ _).trans ?_
  rw [norm_rsmul, norm_rsmul, abs_of_nonneg (chiK_nonneg y m)]
  have b1 : chiK K y m * ‖Dfw η A ν v m‖ ≤ V :=
    (mul_le_of_le_one_left (norm_nonneg _) (chiK_le_one y m)).trans (H.hDv ν m hm.1 hm.2)
  have b2 : |dfw η ν (chiK K y) m| * ‖Ad (Uf η A ν m) (v (m + e4 ν))‖ ≤ 3 / (K * η) * (5 / 4 * (V * (K * η))) :=
    mul_le_mul (H.abs_dfw_chi m ν) ((H.norm_Ad_Uf_le hm.1 hm.2 _).trans
      (mul_le_mul_of_nonneg_left (H.hv _ hm.2) (by norm_num))) (norm_nonneg _) (by positivity)
  have e : 3 / (K * η) * (5 / 4 * (V * (K * η))) = 15 / 4 * V := by
    have := H.K_pos.ne'; have := H.hη.ne'; field_simp; ring
  linarith

/-- `‖η⁻¹(Ad_{𝐔(m, m + e_ν)}w(m + e_ν) - w(m + e_ν))‖ ≤ V/4`. -/
lemma norm_E_le (ν : Fin 4) (m : Fin 4 → ℤ) :
    ‖η⁻¹ • (Ad (Uf η A ν m) (wloc K y v (m + e4 ν)) - wloc K y v (m + e4 ν))‖ ≤ V / 4 := by
  have hV := H.V_nonneg
  by_cases h0 : chiK K y (m + e4 ν) = 0
  · have : wloc K y v (m + e4 ν) = 0 := by unfold wloc; rw [h0, zero_smul]
    rw [this]; simp [Ad]; positivity
  have h3 := H.near_of_chi h0 ν
  have hm : InQ y (8 * K) m := by simpa using h3.2.2
  rw [norm_rsmul, abs_of_pos (inv_pos.2 H.hη)]
  calc η⁻¹ * ‖Ad (Uf η A ν m) (wloc K y v (m + e4 ν)) - wloc K y v (m + e4 ν)‖ ≤
        η⁻¹ * (η / (4 * (K * η)) * (V * (K * η))) :=
        mul_le_mul_of_nonneg_left ((H.bondF hm h3.1 _).trans
          (mul_le_mul_of_nonneg_left (H.norm_wloc_le _) (by have := H.hη; have := H.a_pos; positivity)))
          (inv_nonneg.2 H.hη.le)
    _ = V / 4 := by have := H.hη.ne'; have := H.K_pos.ne'; field_simp

end Hyp



namespace Hyp

variable {η : ℝ} {K : ℕ} {y : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {v : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {lam : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ}
  {rho : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {V : ℝ} {Λ : Fin 4 → ℝ} {β : ℝ}
  (H : Hyp η K y A v lam rho V Λ β)
include H

/-- A point at which `χ` or its neighbours in the direction `ν` do not vanish lies, with these neighbours,
in `Q_y`. -/
lemma near3 {n : Fin 4 → ℤ} (ν : Fin 4)
    (h : ¬(chiK K y (n - e4 ν) = 0 ∧ chiK K y n = 0 ∧ chiK K y (n + e4 ν) = 0)) :
    InQ y (8 * K) (n - e4 ν) ∧ InQ y (8 * K) n ∧ InQ y (8 * K) (n + e4 ν) := by
  have hK := H.hK
  rcases not_and_or.1 h with h1 | h1
  · have q := H.inQ_of_chi_ne h1
    have q1 := q.add_e ν
    have q2 := q1.add_e ν
    rw [sub_add_cancel] at q1 q2
    exact ⟨q.mono (by omega), q1.mono (by omega), q2.mono (by omega)⟩
  rcases not_and_or.1 h1 with h2 | h2
  · have q := H.inQ_of_chi_ne h2
    exact ⟨(q.sub_e ν).mono (by omega), q.mono (by omega), (q.add_e ν).mono (by omega)⟩
  · have q := H.inQ_of_chi_ne h2
    have q1 := q.sub_e ν
    have q2 := q1.sub_e ν
    rw [add_sub_cancel_right] at q1 q2
    exact ⟨q2.mono (by omega), q1.mono (by omega), q.mono (by omega)⟩

/-- The first term of `r`: `‖χD^*_{𝐔,κ}λ_κ - ∂^*_κ(χλ_κ)‖ ≤ 5Λ_κ/a`. -/
lemma norm_T1_le (κ : Fin 4) (n : Fin 4 → ℤ) :
    ‖chiK K y n • Dbw η A κ (lam κ) n - dbw η κ (chiLam K y lam κ) n‖ ≤ 5 * Λ κ / (K * η) := by
  have hΛ := H.Λ_nonneg κ
  have ha := H.a_pos
  have e : chiK K y n • Dbw η A κ (lam κ) n - dbw η κ (chiLam K y lam κ) n =
      chiK K y n • (η⁻¹ • (Ad (Ub η A κ n) (lam κ (n - e4 κ)) - lam κ (n - e4 κ))) -
        dbw η κ (chiK K y) n • lam κ (n - e4 κ) := by
    unfold Dbw dbw chiLam; rw [smul_eq_mul]; module
  by_cases hfar : chiK K y (n - e4 κ) = 0 ∧ chiK K y n = 0 ∧ chiK K y (n + e4 κ) = 0
  · have : dbw η κ (chiK K y) n = 0 := by unfold dbw; rw [hfar.1, hfar.2.1]; simp
    rw [e, this, hfar.2.1]; simp; exact div_nonneg (by linarith) ha.le
  obtain ⟨q1, q2, -⟩ := H.near3 κ hfar
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_rsmul, norm_rsmul, norm_rsmul, abs_of_nonneg (chiK_nonneg y n), abs_of_pos (inv_pos.2 H.hη)]
  have b1 : chiK K y n * (η⁻¹ * ‖Ad (Ub η A κ n) (lam κ (n - e4 κ)) - lam κ (n - e4 κ)‖) ≤
      1 * (η⁻¹ * (η / (4 * (K * η)) * Λ κ)) :=
    mul_le_mul (chiK_le_one y n) (mul_le_mul_of_nonneg_left ((H.bondB q1 q2 _).trans
      (mul_le_mul_of_nonneg_left (H.hlam κ _ q1) (by have := H.hη; positivity))) (inv_nonneg.2 H.hη.le))
      (mul_nonneg (inv_nonneg.2 H.hη.le) (norm_nonneg _)) zero_le_one
  have b2 : |dbw η κ (chiK K y) n| * ‖lam κ (n - e4 κ)‖ ≤ 3 / (K * η) * Λ κ :=
    mul_le_mul (H.abs_dbw_chi n κ) (H.hlam κ _ q1) (norm_nonneg _) (by positivity)
  have e1 : 1 * (η⁻¹ * (η / (4 * (K * η)) * Λ κ)) = Λ κ / (4 * (K * η)) := by
    have := H.hη.ne'; field_simp
  have e2 : 5 * Λ κ / (K * η) = Λ κ / (4 * (K * η)) + 3 / (K * η) * Λ κ + 7 / 4 * (Λ κ / (K * η)) := by
    field_simp; ring
  have : 0 ≤ Λ κ / (K * η) := div_nonneg hΛ ha.le
  linarith

/-- The fourth term of `r` in the direction `ν`: `‖[D^*_{𝐔,ν}D_{𝐔,ν}, χ]v‖ ≤ 31V/a`. -/
lemma norm_T4_le (ν : Fin 4) (n : Fin 4 → ℤ) :
    ‖Dbw η A ν (Dfw η A ν (wloc K y v)) n - chiK K y n • Dbw η A ν (Dfw η A ν v) n‖ ≤ 31 * V / (K * η) := by
  have hV := H.V_nonneg
  have ha := H.a_pos
  have e := commutator_eq (A := A) H.hη.ne' (chiK K y) v ν n
  have hw : wloc K y v = fun k => chiK K y k • v k := rfl
  rw [hw, e]
  by_cases hfar : chiK K y (n - e4 ν) = 0 ∧ chiK K y n = 0 ∧ chiK K y (n + e4 ν) = 0
  · have h1 : dbw η ν (chiK K y) n = 0 := by unfold dbw; rw [hfar.1, hfar.2.1]; simp
    have h2 : dfw η ν (chiK K y) n = 0 := by unfold dfw; rw [hfar.2.2, hfar.2.1]; simp
    have h3 : dbw η ν (dfw η ν (chiK K y)) n = 0 := by
      unfold dbw dfw; rw [sub_add_cancel, hfar.1, hfar.2.1, hfar.2.2]; simp
    rw [h1, h2, h3]; simp; exact div_nonneg (by linarith) ha.le
  obtain ⟨q1, q2, q3⟩ := H.near3 ν hfar
  have tri := norm_sub_le (dbw η ν (chiK K y) n • Ad (Ub η A ν n) (Dfw η A ν v (n - e4 ν)) +
    dbw η ν (dfw η ν (chiK K y)) n • v n) (dfw η ν (chiK K y) n • Dfw η A ν v n)
  have tri2 := norm_add_le (dbw η ν (chiK K y) n • Ad (Ub η A ν n) (Dfw η A ν v (n - e4 ν)))
    (dbw η ν (dfw η ν (chiK K y)) n • v n)
  rw [norm_rsmul, norm_rsmul] at tri2
  rw [norm_rsmul] at tri
  have b1 : |dbw η ν (chiK K y) n| * ‖Ad (Ub η A ν n) (Dfw η A ν v (n - e4 ν))‖ ≤
      3 / (K * η) * (5 / 4 * V) := by
    refine mul_le_mul (H.abs_dbw_chi n ν) ((H.norm_Ad_Ub_le q1 q2 _).trans ?_) (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (H.hDv ν _ q1 (by rwa [sub_add_cancel])) (by norm_num)
  have b2 : |dbw η ν (dfw η ν (chiK K y)) n| * ‖v n‖ ≤ 24 / (K * η) ^ 2 * (V * (K * η)) :=
    mul_le_mul (H.abs_dbw_dfw_chi n ν) (H.hv n q2) (norm_nonneg _) (by positivity)
  have b3 : |dfw η ν (chiK K y) n| * ‖Dfw η A ν v n‖ ≤ 3 / (K * η) * V :=
    mul_le_mul (H.abs_dfw_chi n ν) (H.hDv ν n q2 q3) (norm_nonneg _) (by positivity)
  have e1 : 24 / (K * η) ^ 2 * (V * (K * η)) = 24 * V / (K * η) := by field_simp
  have e2 : 31 * V / (K * η) = 3 / (K * η) * (5 / 4 * V) + 24 * V / (K * η) + 3 / (K * η) * V +
      1 / 4 * (V / (K * η)) := by field_simp; ring
  have : 0 ≤ V / (K * η) := div_nonneg hV ha.le
  linarith

/-- The third term of `r` in the direction `ν`: `‖(∂^*_ν∂_ν - D^*_{𝐔,ν}D_{𝐔,ν})w‖ ≤ 4V/a`. -/
lemma norm_T3_le (ν : Fin 4) (n : Fin 4 → ℤ) :
    ‖dbw η ν (dfw η ν (wloc K y v)) n - Dbw η A ν (Dfw η A ν (wloc K y v)) n‖ ≤ 4 * V / (K * η) := by
  have hV := H.V_nonneg
  have ha := H.a_pos
  have hη := H.hη
  set w := wloc K y v with hwdef
  by_cases hfar : chiK K y (n - e4 ν) = 0 ∧ chiK K y n = 0 ∧ chiK K y (n + e4 ν) = 0
  · have w1 : w (n - e4 ν) = 0 := by rw [hwdef]; unfold wloc; rw [hfar.1, zero_smul]
    have w2 : w n = 0 := by rw [hwdef]; unfold wloc; rw [hfar.2.1, zero_smul]
    have w3 : w (n + e4 ν) = 0 := by rw [hwdef]; unfold wloc; rw [hfar.2.2, zero_smul]
    have : dbw η ν (dfw η ν w) n - Dbw η A ν (Dfw η A ν w) n = 0 := by
      unfold dbw dfw Dbw Dfw
      rw [sub_add_cancel, w1, w2, w3]; simp [Ad]
    rw [this, norm_zero]; exact div_nonneg (by linarith) ha.le
  obtain ⟨q1, q2, q3⟩ := H.near3 ν hfar
  set E : (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ :=
    fun m => η⁻¹ • (Ad (Uf η A ν m) (w (m + e4 ν)) - w (m + e4 ν)) with hE
  set g := Dfw η A ν w (n - e4 ν) with hg
  have e : dbw η ν (dfw η ν w) n - Dbw η A ν (Dfw η A ν w) n =
      -(η⁻¹ • (E (n - e4 ν) - E n)) - η⁻¹ • (Ad (Ub η A ν n) g - g) := by
    simp only [hE, hg]
    unfold dbw dfw Dbw Dfw
    rw [sub_add_cancel]
    module
  have eE : E (n - e4 ν) - E n = η⁻¹ • ((Ad (Uf η A ν (n - e4 ν)) (w n) - Ad (Uf η A ν n) (w n)) +
      (Ad (Uf η A ν n) (w n - w (n + e4 ν)) - (w n - w (n + e4 ν)))) := by
    rw [hE]; simp only [sub_add_cancel, Ad_sub]; module
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, norm_rsmul, norm_rsmul, abs_of_pos (inv_pos.2 hη), eE, norm_rsmul, abs_of_pos (inv_pos.2 hη)]
  -- the difference of the two transports
  have hX1 : ‖η • A ν (n - e4 ν)‖ ≤ 1 / 32 := by
    rw [norm_smul, Real.norm_of_nonneg hη.le]
    have := H.hA ν (n - e4 ν) q1 (by rwa [sub_add_cancel])
    nlinarith [norm_nonneg (A ν (n - e4 ν)), H.η_le_a]
  have hX2 : ‖η • A ν n‖ ≤ 1 / 32 := by
    rw [norm_smul, Real.norm_of_nonneg hη.le]
    have := H.hA ν n q2 q3
    nlinarith [norm_nonneg (A ν n), H.η_le_a]
  have hdA := H.hdA ν ν (n - e4 ν) q1 (by rwa [sub_add_cancel]) (by rwa [sub_add_cancel])
    (by rwa [sub_add_cancel])
  have hdA' : ‖dfw η ν (A ν) (n - e4 ν)‖ ≤ 1 / (32 * (K * η) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hdiff : ‖η • A ν (n - e4 ν) - η • A ν n‖ = η * (η * ‖dfw η ν (A ν) (n - e4 ν)‖) := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hη.le]
    congr 1
    unfold dfw
    rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη, norm_sub_rev]
    field_simp
  have Ba : ‖Ad (Uf η A ν (n - e4 ν)) (w n) - Ad (Uf η A ν n) (w n)‖ ≤ η ^ 2 * V / (4 * (K * η)) := by
    have := norm_Ad_exp_sub_Ad_exp_le hX2 hX1 (w n)
    unfold Uf
    refine this.trans ?_
    rw [hdiff]
    have hw := H.norm_wloc_le (v := v) n
    calc 8 * (η * (η * ‖dfw η ν (A ν) (n - e4 ν)‖)) * ‖w n‖ ≤
        8 * (η * (η * (1 / (32 * (K * η) ^ 2)))) * (V * (K * η)) := by gcongr
      _ = η ^ 2 * V / (4 * (K * η)) := by field_simp; ring
  -- the change of `w` along the bond
  have hdw : ‖w n - w (n + e4 ν)‖ ≤ η * (29 / 4 * V) := by
    have e3 : w n - w (n + e4 ν) = -(η • (Dfw η A ν w n - E n)) := by
      rw [hE]; unfold Dfw; rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hη.ne', one_smul, one_smul]
      abel
    rw [e3, norm_neg, norm_smul, Real.norm_of_nonneg hη.le]
    refine mul_le_mul_of_nonneg_left ?_ hη.le
    refine (norm_sub_le _ _).trans ?_
    have := H.norm_Dfw_w_le (v := v) ν n
    have := H.norm_E_le (v := v) ν n
    linarith
  have Bb : ‖Ad (Uf η A ν n) (w n - w (n + e4 ν)) - (w n - w (n + e4 ν))‖ ≤
      η / (4 * (K * η)) * (η * (29 / 4 * V)) :=
    (H.bondF q2 q3 _).trans (mul_le_mul_of_nonneg_left hdw (by positivity))
  have Bg : ‖Ad (Ub η A ν n) g - g‖ ≤ η / (4 * (K * η)) * (7 * V) :=
    (H.bondB q1 q2 _).trans (mul_le_mul_of_nonneg_left (H.norm_Dfw_w_le ν _) (by positivity))
  have t1 : η⁻¹ * (η⁻¹ * ‖(Ad (Uf η A ν (n - e4 ν)) (w n) - Ad (Uf η A ν n) (w n)) +
      (Ad (Uf η A ν n) (w n - w (n + e4 ν)) - (w n - w (n + e4 ν)))‖) ≤
      η⁻¹ * (η⁻¹ * (η ^ 2 * V / (4 * (K * η)) + η / (4 * (K * η)) * (η * (29 / 4 * V)))) := by
    gcongr
    exact (norm_add_le _ _).trans (add_le_add Ba Bb)
  have t2 : η⁻¹ * ‖Ad (Ub η A ν n) g - g‖ ≤ η⁻¹ * (η / (4 * (K * η)) * (7 * V)) :=
    mul_le_mul_of_nonneg_left Bg (inv_nonneg.2 hη.le)
  have e4' : η⁻¹ * (η⁻¹ * (η ^ 2 * V / (4 * (K * η)) + η / (4 * (K * η)) * (η * (29 / 4 * V)))) +
      η⁻¹ * (η / (4 * (K * η)) * (7 * V)) = 61 / 16 * (V / (K * η)) := by
    field_simp; ring
  have e5 : 4 * V / (K * η) = 64 / 16 * (V / (K * η)) := by ring
  have : 0 ≤ V / (K * η) := div_nonneg hV ha.le
  linarith

/-- The decomposition of `r` into the five terms of the proof. -/
lemma rem_eq (n : Fin 4 → ℤ) :
    rem η K y v lam n = ∑ κ, (chiK K y n • Dbw η A κ (lam κ) n - dbw η κ (chiLam K y lam κ) n) +
      chiK K y n • rho n +
      ∑ ν, (dbw η ν (dfw η ν (wloc K y v)) n - Dbw η A ν (Dfw η A ν (wloc K y v)) n) +
      ∑ ν, (Dbw η A ν (Dfw η A ν (wloc K y v)) n - chiK K y n • Dbw η A ν (Dfw η A ν v) n) +
      ((K * η) ^ 2)⁻¹ • wloc K y v n := by
  have key : chiK K y n • ∑ ν, Dbw η A ν (Dfw η A ν v) n =
      ∑ κ, chiK K y n • Dbw η A κ (lam κ) n + chiK K y n • rho n := by
    by_cases h : chiK K y n = 0
    · simp [h]
    · have := H.heq n ((H.inQ_of_chi_ne h).mono (by omega))
      unfold covLap at this
      rw [this, smul_add, Finset.smul_sum]
  have key' : ∑ ν, chiK K y n • Dbw η A ν (Dfw η A ν v) n =
      ∑ κ, chiK K y n • Dbw η A κ (lam κ) n + chiK K y n • rho n := by
    rw [← Finset.smul_sum]; exact key
  unfold rem lap
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, key']
  abel

/-- **The remainder**: `‖r(n)‖ ≤ a⁻¹(5Σ_κΛ_κ + 166V)` at every point (`eq:schauder-remainder` with `ρ`). -/
theorem norm_rem_le (n : Fin 4 → ℤ) : ‖rem η K y v lam n‖ ≤ (5 * ∑ κ, Λ κ + 166 * V) / (K * η) := by
  have hV := H.V_nonneg
  have ha := H.a_pos
  rw [H.rem_eq n]
  have s1 : ‖∑ κ, (chiK K y n • Dbw η A κ (lam κ) n - dbw η κ (chiLam K y lam κ) n)‖ ≤
      ∑ κ, 5 * Λ κ / (K * η) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => H.norm_T1_le κ n)
  have s2 : ‖chiK K y n • rho n‖ ≤ V / (K * η) := by
    by_cases h : chiK K y n = 0
    · rw [h, zero_smul, norm_zero]; positivity
    · rw [norm_rsmul, abs_of_nonneg (chiK_nonneg y n)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (chiK_le_one y n)).trans
        (H.hrho n ((H.inQ_of_chi_ne h).mono (by omega)))
  have s3 : ‖∑ ν, (dbw η ν (dfw η ν (wloc K y v)) n - Dbw η A ν (Dfw η A ν (wloc K y v)) n)‖ ≤
      ∑ _ν : Fin 4, 4 * V / (K * η) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => H.norm_T3_le ν n)
  have s4 : ‖∑ ν, (Dbw η A ν (Dfw η A ν (wloc K y v)) n - chiK K y n • Dbw η A ν (Dfw η A ν v) n)‖ ≤
      ∑ _ν : Fin 4, 31 * V / (K * η) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => H.norm_T4_le ν n)
  have s5 : ‖((K * η) ^ 2)⁻¹ • wloc K y v n‖ ≤ V / (K * η) := by
    rw [norm_rsmul, abs_of_pos (by positivity)]
    calc ((K * η) ^ 2)⁻¹ * ‖wloc K y v n‖ ≤ ((K * η) ^ 2)⁻¹ * (V * (K * η)) :=
          mul_le_mul_of_nonneg_left (H.norm_wloc_le n) (by positivity)
      _ = V / (K * η) := by field_simp
  have e1 : ∑ κ, 5 * Λ κ / (K * η) = 5 * (∑ κ, Λ κ) / (K * η) := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at s3 s4
  have e2 : (5 * ∑ κ, Λ κ + 166 * V) / (K * η) = 5 * (∑ κ, Λ κ) / (K * η) + V / (K * η) +
      4 * (4 * V / (K * η)) + 4 * (31 * V / (K * η)) + V / (K * η) + 24 * (V / (K * η)) := by
    field_simp; ring
  have : 0 ≤ V / (K * η) := div_nonneg hV ha.le
  have := norm_add_le (∑ κ, (chiK K y n • Dbw η A κ (lam κ) n - dbw η κ (chiLam K y lam κ) n) +
      chiK K y n • rho n +
      ∑ ν, (dbw η ν (dfw η ν (wloc K y v)) n - Dbw η A ν (Dfw η A ν (wloc K y v)) n) +
      ∑ ν, (Dbw η A ν (Dfw η A ν (wloc K y v)) n - chiK K y n • Dbw η A ν (Dfw η A ν v) n))
    (((K * η) ^ 2)⁻¹ • wloc K y v n)
  have := norm_add_le (∑ κ, (chiK K y n • Dbw η A κ (lam κ) n - dbw η κ (chiLam K y lam κ) n) +
      chiK K y n • rho n +
      ∑ ν, (dbw η ν (dfw η ν (wloc K y v)) n - Dbw η A ν (Dfw η A ν (wloc K y v)) n))
    (∑ ν, (Dbw η A ν (Dfw η A ν (wloc K y v)) n - chiK K y n • Dbw η A ν (Dfw η A ν v) n))
  have := norm_add_le (∑ κ, (chiK K y n • Dbw η A κ (lam κ) n - dbw η κ (chiLam K y lam κ) n) +
      chiK K y n • rho n)
    (∑ ν, (dbw η ν (dfw η ν (wloc K y v)) n - Dbw η A ν (Dfw η A ν (wloc K y v)) n))
  have := norm_add_le (∑ κ, (chiK K y n • Dbw η A κ (lam κ) n - dbw η κ (chiLam K y lam κ) n))
    (chiK K y n • rho n)
  linarith

end Hyp

end InteriorSchauder
end CoreLean

end
