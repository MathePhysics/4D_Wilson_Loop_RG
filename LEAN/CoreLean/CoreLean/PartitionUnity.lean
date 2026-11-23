/-
`lem:partition-of-unity` of BALABAN_CORE.tex (`bf6b2bc552ba`), in part: the profile and the
normalisation of its proof.

* The profile: a `C^∞` function `ψ` on `[1/3, 2/3]` with values in `[0, 1]` which vanishes near `1/3`,
  equals `1` near `2/3`, and satisfies `ψ(t) + ψ(1 - t) = 1` exists: `ψ(t) = s(6t - 5/2)` with
  Mathlib's `Real.smoothTransition` `s`, for which `s(x) + s(1 - x) = 1` (`psi`, `psi_add_psi_one_sub`).
* `h(t) = 1` for `|t| ≤ 1/3`, `cos(½πψ(|t|))` for `1/3 ≤ |t| ≤ 2/3`, `0` for `|t| ≥ 2/3`, is `C^∞` with
  values in `[0, 1]`, even, Lipschitz, and `Σ_{m ∈ ℤ} h(t - m)² = 1` (`prof`, `contDiff_prof`,
  `sum_prof_sq`).
* For the grid of side `s` in four dimensions, `Σ_z Π_μ h((p_μ - s z_μ)/s)² = 1`, the sum over all the
  corners `z ∈ ℤ⁴` (`grid_sum`); the functions `φ_□` are covariant under the permutations of the
  coordinates and the reflections (`phi_perm`, `phi_reflect`).
* The normalisation: if a part of the family `φ_□` has squares adding up to at least `1` at a point,
  then `N ≥ 1` there, the quotients `h_□ = φ_□ / max{N, 1}` have values in `[0, 1]`, and
  `Σ_□ h_□² = 1` (`normalise`).

The torus, the sequence of domains, the count of at most `48` cubes at a point, (i), the bounds (ii) with
the constant `C_h`, and the locality and covariance (iii) are in `PartitionTorus.lean`,
`PartitionGeometry.lean`, `PartitionBounds.lean`, and `PartitionLocality.lean`.
-/
import Mathlib

open Real Finset

noncomputable section

namespace CoreLean
namespace PartitionUnity

/-- `s(x) + s(1 - x) = 1` for Mathlib's smooth transition `s`. -/
lemma smoothTransition_add_one_sub (x : ℝ) :
    smoothTransition x + smoothTransition (1 - x) = 1 := by
  have hp := smoothTransition.pos_denom x
  simp only [Real.smoothTransition, sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x), ← add_div, div_self hp.ne']

/-- The profile `ψ(t) = s(6t - 5/2)`. -/
def psi (t : ℝ) : ℝ := smoothTransition (6 * t - 5 / 2)

lemma psi_add_psi_one_sub (t : ℝ) : psi t + psi (1 - t) = 1 := by
  unfold psi
  rw [show 6 * (1 - t) - 5 / 2 = 1 - (6 * t - 5 / 2) by ring]
  exact smoothTransition_add_one_sub _

lemma psi_eq_zero {t : ℝ} (ht : t ≤ 5 / 12) : psi t = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

lemma psi_eq_one {t : ℝ} (ht : 7 / 12 ≤ t) : psi t = 1 :=
  smoothTransition.one_of_one_le (by linarith)

lemma psi_nonneg (t : ℝ) : 0 ≤ psi t := smoothTransition.nonneg _

lemma psi_le_one (t : ℝ) : psi t ≤ 1 := smoothTransition.le_one _

lemma contDiff_psi (n : ℕ∞) : ContDiff ℝ n psi :=
  smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- `ψ(t) + ψ(-t) = ψ(|t|)`. -/
lemma psi_add_psi_neg (t : ℝ) : psi t + psi (-t) = psi |t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, psi_eq_zero (t := -t) (by linarith), add_zero]
  · rw [abs_of_nonpos ht, psi_eq_zero (t := t) (by linarith), zero_add]

/-- The profile `h(t) = cos(½π(ψ(t) + ψ(-t))) = cos(½πψ(|t|))`. -/
def prof (t : ℝ) : ℝ := cos (π / 2 * (psi t + psi (-t)))

lemma prof_eq (t : ℝ) : prof t = cos (π / 2 * psi |t|) := by
  rw [prof, psi_add_psi_neg]

lemma contDiff_prof (n : ℕ∞) : ContDiff ℝ n prof :=
  contDiff_cos.comp (contDiff_const.mul ((contDiff_psi n).add ((contDiff_psi n).comp contDiff_neg)))

lemma prof_even (t : ℝ) : prof (-t) = prof t := by
  rw [prof_eq, prof_eq, abs_neg]

lemma prof_eq_one {t : ℝ} (ht : |t| ≤ 1 / 3) : prof t = 1 := by
  rw [prof_eq, psi_eq_zero (by linarith), mul_zero, cos_zero]

lemma prof_eq_zero {t : ℝ} (ht : 2 / 3 ≤ |t|) : prof t = 0 := by
  rw [prof_eq, psi_eq_one (by linarith), mul_one, cos_pi_div_two]

lemma prof_nonneg (t : ℝ) : 0 ≤ prof t := by
  rw [prof_eq]
  have h0 := psi_nonneg |t|
  have h1 := psi_le_one |t|
  apply cos_nonneg_of_neg_pi_div_two_le_of_le
  · nlinarith [pi_pos]
  · nlinarith [pi_pos]

lemma prof_le_one (t : ℝ) : prof t ≤ 1 := cos_le_one _

lemma hasCompactSupport_prof : HasCompactSupport prof := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun t ht => ?_
  apply prof_eq_zero
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The profile is Lipschitz (the first bound of (ii) for one coordinate). -/
lemma exists_lipschitz_prof : ∃ C, LipschitzWith C prof :=
  (contDiff_prof 1).lipschitzWith_of_hasCompactSupport hasCompactSupport_prof one_ne_zero

/-- For `u ∈ [0, 1]`, `h(u)² + h(u - 1)² = 1`. -/
lemma prof_sq_add (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : prof u ^ 2 + prof (u - 1) ^ 2 = 1 := by
  rw [prof_eq, prof_eq, abs_of_nonneg hu0, abs_of_nonpos (by linarith), neg_sub]
  have h := psi_add_psi_one_sub u
  rw [show psi (1 - u) = 1 - psi u by linarith, mul_sub, mul_one, cos_pi_div_two_sub]
  exact cos_sq_add_sin_sq _

/-- `h(t - m) = 0` unless `m ∈ {⌊t⌋, ⌊t⌋ + 1}`. -/
lemma prof_eq_zero_of_not_mem (t : ℝ) (m : ℤ) (hm : m ∉ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ)) :
    prof (t - m) = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  apply prof_eq_zero
  rcases lt_or_gt_of_ne hm.1 with h | h
  · have : (m : ℝ) ≤ ⌊t⌋ - 1 := by
      have : m ≤ ⌊t⌋ - 1 := by omega
      exact_mod_cast this
    rw [abs_of_pos (by linarith)]; linarith
  · have : (⌊t⌋ : ℝ) + 2 ≤ m := by
      have : ⌊t⌋ + 2 ≤ m := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith

/-- The two terms at `⌊t⌋` and `⌊t⌋ + 1` add up to `1`. -/
lemma pair_sum (t : ℝ) : prof (t - ⌊t⌋) ^ 2 + prof (t - (⌊t⌋ + 1 : ℤ)) ^ 2 = 1 := by
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  rw [show t - ((⌊t⌋ + 1 : ℤ) : ℝ) = (t - ⌊t⌋) - 1 by push_cast; ring]
  exact prof_sq_add _ (by linarith) (by linarith)

/-- `Σ_{m ∈ ℤ} h(t - m)² = 1`. -/
theorem sum_prof_sq (t : ℝ) : ∑' m : ℤ, prof (t - m) ^ 2 = 1 := by
  rw [tsum_eq_sum (s := {⌊t⌋, ⌊t⌋ + 1}) fun m hm => by rw [prof_eq_zero_of_not_mem t m hm]; ring,
    Finset.sum_pair (by omega)]
  exact pair_sum t

/-! ### The grid in four dimensions -/

/-- `φ(p) = Π_μ h((p_μ - c_μ)/s)` for the cube with the centre `c` and the grid of side `s`. -/
def phi (s : ℝ) (c p : Fin 4 → ℝ) : ℝ := ∏ μ, prof ((p μ - c μ) / s)

/-- `Σ_z φ_z(p)² = 1`, the sum over the corners `s z`, `z ∈ ℤ⁴`, of the grid of side `s`. -/
theorem grid_sum (s : ℝ) (hs : s ≠ 0) (p : Fin 4 → ℝ) :
    ∑' z : Fin 4 → ℤ, phi s (fun μ => s * z μ) p ^ 2 = 1 := by
  set x : Fin 4 → ℝ := fun μ => p μ / s
  have hx : ∀ (z : Fin 4 → ℤ) μ, (p μ - s * z μ) / s = x μ - z μ := fun z μ => by
    simp only [x]; field_simp
  set t : Fin 4 → Finset ℤ := fun μ => {⌊x μ⌋, ⌊x μ⌋ + 1}
  have hzero : ∀ z ∉ Fintype.piFinset t, phi s (fun μ => s * z μ) p ^ 2 = 0 := fun z hz => by
    simp only [Fintype.mem_piFinset, not_forall] at hz
    obtain ⟨μ, hμ⟩ := hz
    have : phi s (fun μ => s * z μ) p = 0 := by
      unfold phi
      refine Finset.prod_eq_zero (Finset.mem_univ μ) ?_
      rw [hx]; exact prof_eq_zero_of_not_mem _ _ hμ
    rw [this]; ring
  rw [tsum_eq_sum hzero]
  have hprod : ∀ z : Fin 4 → ℤ, phi s (fun μ => s * z μ) p ^ 2 = ∏ μ, prof (x μ - z μ) ^ 2 :=
    fun z => by unfold phi; rw [← Finset.prod_pow]; simp only [hx]
  simp only [hprod]
  rw [← Finset.prod_univ_sum t (fun μ k => prof (x μ - k) ^ 2)]
  refine Finset.prod_eq_one fun μ _ => ?_
  rw [Finset.sum_pair (by omega)]
  exact pair_sum (x μ)

/-- (iii), covariance under the permutations of the coordinates. -/
theorem phi_perm (s : ℝ) (σ : Equiv.Perm (Fin 4)) (c p : Fin 4 → ℝ) :
    phi s (c ∘ σ) (p ∘ σ) = phi s c p := by
  unfold phi
  exact Equiv.prod_comp σ (fun μ => prof ((p μ - c μ) / s))

/-- (iii), covariance under the reflection of the coordinates. -/
theorem phi_reflect (s : ℝ) (c p : Fin 4 → ℝ) : phi s (-c) (-p) = phi s c p := by
  unfold phi
  refine Finset.prod_congr rfl fun μ _ => ?_
  rw [Pi.neg_apply, Pi.neg_apply, show (-p μ - -c μ) / s = -((p μ - c μ) / s) by ring, prof_even]

/-! ### The normalisation -/

/-- The normalisation of the proof: for a finite family `φ_□` with values in `[0, 1]` at a point, and
a part `S` of it whose squares add up to at least `1`, the number `N = (Σ_□ φ_□²)^{1/2}` is at least
`1`, the quotients `h_□ = φ_□ / max{N, 1}` have values in `[0, 1]`, and `Σ_□ h_□² = 1`. -/
theorem normalise {ι : Type*} [Fintype ι] (φ : ι → ℝ) (h0 : ∀ q, 0 ≤ φ q) (h1 : ∀ q, φ q ≤ 1)
    (S : Finset ι) (hS : 1 ≤ ∑ q ∈ S, φ q ^ 2) :
    let N := Real.sqrt (∑ q, φ q ^ 2)
    1 ≤ N ∧ (∀ q, 0 ≤ φ q / max N 1 ∧ φ q / max N 1 ≤ 1) ∧ ∑ q, (φ q / max N 1) ^ 2 = 1 := by
  intro N
  have hsub : ∑ q ∈ S, φ q ^ 2 ≤ ∑ q, φ q ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun q _ _ => sq_nonneg _
  have hN : 1 ≤ N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hmax : max N 1 = N := max_eq_left hN
  have hNpos : 0 < N := by linarith
  refine ⟨hN, fun q => ⟨div_nonneg (h0 q) (by rw [hmax]; linarith), ?_⟩, ?_⟩
  · rw [hmax, div_le_one hNpos]; linarith [h1 q]
  · rw [hmax]
    simp only [div_pow]
    rw [← Finset.sum_div, Real.sq_sqrt (Finset.sum_nonneg fun q _ => sq_nonneg _),
      div_self (by nlinarith)]

end PartitionUnity
end CoreLean

end
