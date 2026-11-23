/-
`lem:partition-of-unity` of BALABAN_CORE.tex (`46925ba99aac`): the torus and the profile.

The torus `(ℝ/ℓℤ)⁴` is represented by `ℝ⁴`: the coordinates of `x - c` are taken in `(-ℓ/2, ℓ/2]` (`rep`,
Mathlib's `toIocMod`), as in the proof of the lemma, and the `ℓ^∞`-distance on the torus is
`dT x y = max_μ |rep(x_μ - y_μ)|`, the smallest `ℓ^∞`-norm of the representatives of `x - y`.

* `rep`, `abs_rep_le`, `abs_rep_add_le`, `dT`, `dT_triangle`: the representative and the distance.
* `prof_lip`, `prof_second`: the profile `h` is Lipschitz and its second differences are bounded by
  `C|a||b|` (its derivative is Lipschitz).
* `gT`: the factor `t ↦ h(rep(t - c)/s)` of a cube; `gT_lip_of` (Lipschitz with the constant `max{C, 3}/s` in
  the torus distance) and `gT_second_of` (second differences `≤ C'|a||b|/s²` for steps `≤ s/12`), with the
  constants `C`, `C'` of the profile, independent of `ℓ` and `s`.
* `torus_sum`, `torus_grid_sum`: for a grid of side `s` with `ℓ = Ps`, `P ≥ 2`, the squares of the functions
  of the cubes centred at the corners `s(n + ½)`, `n ∈ (ℤ/Pℤ)⁴`, add up to `1` at every point;
  `card_nonzero_le`: at most `2⁴` of them do not vanish at a point.
-/
import CoreLean.PartitionUnity

open Real Finset

noncomputable section

namespace CoreLean
namespace PartitionUnity

/-! ### The profile: first and second differences -/

lemma prof_lip : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |prof x - prof y| ≤ C * |x - y| := by
  obtain ⟨C, hC⟩ := exists_lipschitz_prof
  exact ⟨C, C.2, fun x y => by simpa [Real.dist_eq] using hC.dist_le_mul x y⟩

lemma differentiable_prof : Differentiable ℝ prof :=
  (contDiff_prof 1).differentiable (by norm_num)

lemma prof_second : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x a b, |prof (x + a + b) - prof (x + a) - prof (x + b) + prof x| ≤ C * (|a| * |b|) := by
  have hd : ContDiff ℝ 1 (deriv prof) := by
    have h2 : ContDiff ℝ (1 + 1) prof := contDiff_prof 2
    exact (contDiff_succ_iff_deriv.1 h2).2.2
  obtain ⟨C, hC⟩ := hd.lipschitzWith_of_hasCompactSupport hasCompactSupport_prof.deriv one_ne_zero
  refine ⟨C, C.2, fun x a b => ?_⟩
  set g : ℝ → ℝ := fun r => prof (r + b) - prof r with hg
  have hdiff : ∀ r, HasDerivAt g (deriv prof (r + b) - deriv prof r) r := fun r => by
    have h1 : HasDerivAt prof (deriv prof (r + b)) (r + b) := (differentiable_prof (r + b)).hasDerivAt
    have h2 : HasDerivAt prof (deriv prof r) r := (differentiable_prof r).hasDerivAt
    exact (h1.comp_add_const r b).sub h2
  have hbd : ∀ r ∈ (Set.univ : Set ℝ), ‖deriv g r‖ ≤ C * |b| := fun r _ => by
    rw [(hdiff r).deriv, Real.norm_eq_abs]
    have := hC.dist_le_mul (r + b) r
    simpa [Real.dist_eq] using this
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (fun r _ => (hdiff r).differentiableAt) hbd
    convex_univ (Set.mem_univ x) (Set.mem_univ (x + a))
  simp only [hg, Real.norm_eq_abs, add_sub_cancel_left] at h
  calc |prof (x + a + b) - prof (x + a) - prof (x + b) + prof x|
      = |prof (x + a + b) - prof (x + a) - (prof (x + b) - prof x)| := by ring_nf
    _ ≤ C * |b| * |a| := h
    _ = C * (|a| * |b|) := by ring

/-! ### The representative and the distance on the torus -/

variable {ℓ : ℝ} (hℓ : 0 < ℓ)

/-- The representative of `y` in `(-ℓ/2, ℓ/2]`. -/
def rep (y : ℝ) : ℝ := toIocMod hℓ (-(ℓ / 2)) y

lemma rep_mem (y : ℝ) : -(ℓ / 2) < rep hℓ y ∧ rep hℓ y ≤ ℓ / 2 := by
  have := toIocMod_mem_Ioc hℓ (-(ℓ / 2)) y
  rw [show -(ℓ / 2) + ℓ = ℓ / 2 by ring] at this
  exact this

lemma rep_eq_sub (y : ℝ) : ∃ n : ℤ, rep hℓ y = y - n * ℓ :=
  ⟨toIocDiv hℓ (-(ℓ / 2)) y, by rw [rep, toIocMod, zsmul_eq_mul]⟩

lemma rep_add_int_mul (y : ℝ) (n : ℤ) : rep hℓ (y + n * ℓ) = rep hℓ y := by
  rw [rep, rep, ← zsmul_eq_mul, toIocMod_add_zsmul]

lemma rep_of_mem {y : ℝ} (h1 : -(ℓ / 2) < y) (h2 : y ≤ ℓ / 2) : rep hℓ y = y := by
  rw [rep, toIocMod_eq_self]
  exact ⟨h1, by linarith⟩

/-- `rep y = z` for a representative `z ∈ (-ℓ/2, ℓ/2]` of `y`. -/
lemma rep_eq_of {y z : ℝ} (n : ℤ) (hz : y = z + n * ℓ) (h1 : -(ℓ / 2) < z) (h2 : z ≤ ℓ / 2) :
    rep hℓ y = z := by
  rw [hz, rep_add_int_mul, rep_of_mem hℓ h1 h2]

/-- The representative has the smallest absolute value. -/
lemma abs_rep_le (y : ℝ) (n : ℤ) : |rep hℓ y| ≤ |y - n * ℓ| := by
  obtain ⟨m, hm⟩ := rep_eq_sub hℓ y
  obtain ⟨h1, h2⟩ := rep_mem hℓ y
  by_contra hlt
  push_neg at hlt
  have hz : |y - n * ℓ| < ℓ / 2 := lt_of_lt_of_le hlt (abs_le.2 ⟨by linarith, h2⟩)
  have heq := rep_eq_of hℓ n (by ring : y = (y - n * ℓ) + n * ℓ) (by linarith [neg_abs_le (y - n * ℓ)])
    (by linarith [le_abs_self (y - n * ℓ)])
  rw [heq] at hlt
  exact lt_irrefl _ hlt

lemma abs_rep_le_abs (y : ℝ) : |rep hℓ y| ≤ |y| := by
  simpa using abs_rep_le hℓ y 0

lemma abs_rep_of_abs_le {y : ℝ} (hy : |y| ≤ ℓ / 2) : |rep hℓ y| = |y| := by
  refine le_antisymm (abs_rep_le_abs hℓ y) ?_
  obtain ⟨m, hm⟩ := rep_eq_sub hℓ y
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [hm]; simp
  · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
    have : ℓ ≤ |(m : ℝ) * ℓ| := by rw [abs_mul, abs_of_pos hℓ]; nlinarith
    rw [hm]
    have := abs_sub_abs_le_abs_sub ((m : ℝ) * ℓ) y
    rw [abs_sub_comm] at this
    linarith

lemma abs_rep_neg (y : ℝ) : |rep hℓ (-y)| = |rep hℓ y| := by
  obtain ⟨m, hm⟩ := rep_eq_sub hℓ y
  obtain ⟨m', hm'⟩ := rep_eq_sub hℓ (-y)
  refine le_antisymm ?_ ?_
  · have := abs_rep_le hℓ (-y) (-m)
    rw [hm]
    calc |rep hℓ (-y)| ≤ |-y - ((-m : ℤ) : ℝ) * ℓ| := this
      _ = |y - m * ℓ| := by rw [← abs_neg]; push_cast; ring_nf
  · have := abs_rep_le hℓ y (-m')
    rw [hm']
    calc |rep hℓ y| ≤ |y - ((-m' : ℤ) : ℝ) * ℓ| := this
      _ = |-y - m' * ℓ| := by rw [← abs_neg]; push_cast; ring_nf

lemma abs_rep_add_le (a b : ℝ) : |rep hℓ (a + b)| ≤ |rep hℓ a| + |rep hℓ b| := by
  obtain ⟨m, hm⟩ := rep_eq_sub hℓ a
  obtain ⟨m', hm'⟩ := rep_eq_sub hℓ b
  calc |rep hℓ (a + b)| ≤ |a + b - ((m + m' : ℤ) : ℝ) * ℓ| := abs_rep_le hℓ _ _
    _ = |rep hℓ a + rep hℓ b| := by rw [hm, hm']; push_cast; ring_nf
    _ ≤ |rep hℓ a| + |rep hℓ b| := abs_add_le _ _

/-- `rep(y + e) = rep y + e` when `rep y + e` lies in `(-ℓ/2, ℓ/2]`. -/
lemma rep_add_of_mem (y e : ℝ) (h1 : -(ℓ / 2) < rep hℓ y + e) (h2 : rep hℓ y + e ≤ ℓ / 2) :
    rep hℓ (y + e) = rep hℓ y + e := by
  obtain ⟨m, hm⟩ := rep_eq_sub hℓ y
  exact rep_eq_of hℓ m (by rw [hm]; ring) h1 h2

/-- The `ℓ^∞`-distance on the torus. -/
def dT (x y : Fin 4 → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun μ => |rep hℓ (x μ - y μ)|

lemma le_dT (x y : Fin 4 → ℝ) (μ : Fin 4) : |rep hℓ (x μ - y μ)| ≤ dT hℓ x y :=
  Finset.le_sup' (fun μ => |rep hℓ (x μ - y μ)|) (Finset.mem_univ μ)

lemma dT_le_iff {x y : Fin 4 → ℝ} {r : ℝ} : dT hℓ x y ≤ r ↔ ∀ μ, |rep hℓ (x μ - y μ)| ≤ r := by
  rw [dT, Finset.sup'_le_iff]; simp

lemma dT_lt_iff {x y : Fin 4 → ℝ} {r : ℝ} : dT hℓ x y < r ↔ ∀ μ, |rep hℓ (x μ - y μ)| < r := by
  rw [dT, Finset.sup'_lt_iff]; simp

lemma dT_nonneg (x y : Fin 4 → ℝ) : 0 ≤ dT hℓ x y := (abs_nonneg _).trans (le_dT hℓ x y 0)

lemma dT_comm (x y : Fin 4 → ℝ) : dT hℓ x y = dT hℓ y x := by
  refine le_antisymm ((dT_le_iff hℓ).2 fun μ => ?_) ((dT_le_iff hℓ).2 fun μ => ?_)
  · rw [show x μ - y μ = -(y μ - x μ) by ring, abs_rep_neg]; exact le_dT hℓ y x μ
  · rw [show y μ - x μ = -(x μ - y μ) by ring, abs_rep_neg]; exact le_dT hℓ x y μ

lemma dT_triangle (x y z : Fin 4 → ℝ) : dT hℓ x z ≤ dT hℓ x y + dT hℓ y z :=
  (dT_le_iff hℓ).2 fun μ => by
    rw [show x μ - z μ = (x μ - y μ) + (y μ - z μ) by ring]
    exact (abs_rep_add_le hℓ _ _).trans (add_le_add (le_dT hℓ x y μ) (le_dT hℓ y z μ))

lemma dT_le_norm (x y : Fin 4 → ℝ) : dT hℓ x y ≤ ‖x - y‖ :=
  (dT_le_iff hℓ).2 fun μ => (abs_rep_le_abs hℓ _).trans (by
    have := norm_le_pi_norm (x - y) μ
    simpa [Real.norm_eq_abs] using this)

/-! ### The factor of a cube -/

/-- The factor `t ↦ h(rep(t - c)/s)` of the function of a cube of side `2s` centred at `c`. -/
def gT (s c t : ℝ) : ℝ := prof (rep hℓ (t - c) / s)

lemma gT_nonneg (s c t : ℝ) : 0 ≤ gT hℓ s c t := prof_nonneg _

lemma gT_le_one (s c t : ℝ) : gT hℓ s c t ≤ 1 := prof_le_one _

lemma prof_div_abs (y s : ℝ) : prof (y / s) = prof (|y| / s) ∨ s < 0 := by
  rcases lt_or_ge s 0 with hs | hs
  · exact Or.inr hs
  · left
    rw [prof_eq, prof_eq, abs_div, abs_div, abs_abs]

lemma prof_congr_abs {y z s : ℝ} (hs : 0 < s) (h : |y| = |z|) : prof (y / s) = prof (z / s) := by
  rw [prof_eq, prof_eq, abs_div, abs_div, h]

lemma gT_eq_zero {s c t : ℝ} (hs : 0 < s) (h : 2 / 3 * s ≤ |rep hℓ (t - c)|) : gT hℓ s c t = 0 := by
  apply prof_eq_zero
  rw [abs_div, abs_of_pos hs, le_div_iff₀ hs]
  linarith

lemma abs_rep_lt_of_gT_ne {s c t : ℝ} (hs : 0 < s) (h : gT hℓ s c t ≠ 0) : |rep hℓ (t - c)| < 2 / 3 * s := by
  by_contra h'
  exact h (gT_eq_zero hℓ hs (not_lt.1 h'))

/-- The Lipschitz constant of the factor: `|g(t) - g(t')| ≤ (A/s)|rep(t - t')|`. -/
lemma gT_lip_of {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x y, |prof x - prof y| ≤ C * |x - y|) {s : ℝ} (hs : 0 < s)
    (hsℓ : s ≤ ℓ / 2) (c t t' : ℝ) : |gT hℓ s c t - gT hℓ s c t'| ≤ max C 3 / s * |rep hℓ (t - t')| := by
  set r := rep hℓ (t - c) with hr
  set r' := rep hℓ (t' - c) with hr'
  set d := rep hℓ (t - t') with hd
  obtain ⟨h1, h2⟩ := rep_mem hℓ (t - c)
  obtain ⟨h1', h2'⟩ := rep_mem hℓ (t' - c)
  obtain ⟨m, hm⟩ := rep_eq_sub hℓ (t - c)
  obtain ⟨m', hm'⟩ := rep_eq_sub hℓ (t' - c)
  obtain ⟨m'', hm''⟩ := rep_eq_sub hℓ (t - t')
  have hA : C ≤ max C 3 := le_max_left _ _
  have hA3 : (3 : ℝ) ≤ max C 3 := le_max_right _ _
  have hsd : 0 ≤ max C 3 / s * |d| := by positivity
  -- the bound by the Lipschitz constant of the profile, when a representative is consistent
  have key : ∀ {y z : ℝ}, |y - z| = |d| → |prof (y / s) - prof (z / s)| ≤ max C 3 / s * |d| := by
    intro y z hyz
    calc |prof (y / s) - prof (z / s)| ≤ C * |y / s - z / s| := hC _ _
      _ = C / s * |d| := by rw [← sub_div, abs_div, abs_of_pos hs, hyz]; ring
      _ ≤ max C 3 / s * |d| := by gcongr
  -- the bound `1 ≤ 3|d|/s` when the two points are far apart
  have far : s / 3 ≤ |d| → |gT hℓ s c t - gT hℓ s c t'| ≤ max C 3 / s * |d| := by
    intro hfar
    have h01 : |gT hℓ s c t - gT hℓ s c t'| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [gT_nonneg hℓ s c t, gT_le_one hℓ s c t, gT_nonneg hℓ s c t',
        gT_le_one hℓ s c t']
    calc |gT hℓ s c t - gT hℓ s c t'| ≤ 1 := h01
      _ ≤ 3 / s * |d| := by rw [div_mul_eq_mul_div, le_div_iff₀ hs]; linarith
      _ ≤ max C 3 / s * |d| := by gcongr
  by_cases hy : |r - d| ≤ ℓ / 2
  · -- `t' - c` is represented by `r - d`
    have hrep : |r'| = |r - d| := by
      have : t' - c = (r - d) + ((m - m'' : ℤ) : ℝ) * ℓ := by
        rw [hd, hm'', hr, hm]; push_cast; ring
      rw [hr', this, rep_add_int_mul, abs_rep_of_abs_le hℓ hy]
    unfold gT
    rw [← hr, ← hr', prof_congr_abs hs hrep]
    exact key (by rw [sub_sub_cancel])
  by_cases hy' : |r' + d| ≤ ℓ / 2
  · have hrep : |r| = |r' + d| := by
      have : t - c = (r' + d) + ((m' + m'' : ℤ) : ℝ) * ℓ := by
        rw [hd, hm'', hr', hm']; push_cast; ring
      rw [hr, this, rep_add_int_mul, abs_rep_of_abs_le hℓ hy']
    unfold gT
    rw [← hr, ← hr', prof_congr_abs hs hrep]
    exact key (by rw [add_sub_cancel_left])
  push_neg at hy hy'
  have e1 : ℓ / 2 - |r| < |d| := by
    have := abs_sub (r) d
    linarith [abs_sub_abs_le_abs_sub r d, abs_sub_comm r d]
  have e2 : ℓ / 2 - |r'| < |d| := by
    linarith [abs_add_le r' d]
  by_cases g1 : gT hℓ s c t = 0
  · by_cases g2 : gT hℓ s c t' = 0
    · rw [g1, g2, sub_self, abs_zero]; exact hsd
    · have := abs_rep_lt_of_gT_ne hℓ hs g2
      exact far (by linarith)
  · have := abs_rep_lt_of_gT_ne hℓ hs g1
    exact far (by linarith)

/-- The second differences of the factor for steps `≤ s/12`. -/
lemma gT_second_of {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x a b, |prof (x + a + b) - prof (x + a) - prof (x + b) + prof x| ≤ C * (|a| * |b|)) {s : ℝ}
    (hs : 0 < s) (hsℓ : s ≤ ℓ / 2) (c t a b : ℝ) (ha : |a| ≤ s / 12) (hb : |b| ≤ s / 12) :
    |gT hℓ s c (t + a + b) - gT hℓ s c (t + a) - gT hℓ s c (t + b) + gT hℓ s c t| ≤
      C / s ^ 2 * (|a| * |b|) := by
  have hsd : 0 ≤ C / s ^ 2 * (|a| * |b|) := by positivity
  by_cases hz : gT hℓ s c (t + a + b) = 0 ∧ gT hℓ s c (t + a) = 0 ∧ gT hℓ s c (t + b) = 0 ∧
      gT hℓ s c t = 0
  · obtain ⟨z1, z2, z3, z4⟩ := hz
    rw [z1, z2, z3, z4]; simpa using hsd
  -- some point is near the centre; then the representatives of the four points are consistent
  have hex : ∃ δ : ℝ, |δ| ≤ s / 6 ∧ |rep hℓ (t + δ - c)| < 2 / 3 * s := by
    simp only [not_and_or] at hz
    rcases hz with h | h | h | h
    · exact ⟨a + b, by rw [abs_le] at ha hb ⊢; constructor <;> linarith,
        abs_rep_lt_of_gT_ne hℓ hs (by rwa [show t + (a + b) = t + a + b by ring])⟩
    · exact ⟨a, by linarith, abs_rep_lt_of_gT_ne hℓ hs h⟩
    · exact ⟨b, by linarith, abs_rep_lt_of_gT_ne hℓ hs h⟩
    · exact ⟨0, by simp; positivity, by simpa using abs_rep_lt_of_gT_ne hℓ hs h⟩
  obtain ⟨δ, hδ, hr⟩ := hex
  set r := rep hℓ (t + δ - c) with hrdef
  have hcons : ∀ e : ℝ, |e| ≤ s / 6 → rep hℓ (t + e - c) = r + (e - δ) := fun e he => by
    have h1 : -(ℓ / 2) < r + (e - δ) := by
      rw [abs_lt] at hr; rw [abs_le] at he hδ; linarith
    have h2 : r + (e - δ) ≤ ℓ / 2 := by
      rw [abs_lt] at hr; rw [abs_le] at he hδ; linarith
    rw [show t + e - c = (t + δ - c) + (e - δ) by ring]
    exact rep_add_of_mem hℓ _ _ h1 h2
  have hab : |a + b| ≤ s / 6 := by rw [abs_le] at ha hb ⊢; constructor <;> linarith
  unfold gT
  rw [show t + a + b - c = t + (a + b) - c by ring, hcons (a + b) hab, hcons a (by linarith),
    hcons b (by linarith), show t - c = t + 0 - c by ring, hcons 0 (by simp; positivity)]
  have := hC ((r - δ) / s) (a / s) (b / s)
  rw [show (r + (a + b - δ)) / s = (r - δ) / s + a / s + b / s by ring,
    show (r + (a - δ)) / s = (r - δ) / s + a / s by ring,
    show (r + (b - δ)) / s = (r - δ) / s + b / s by ring,
    show (r + (0 - δ)) / s = (r - δ) / s by ring]
  calc _ ≤ C * (|a / s| * |b / s|) := this
    _ = C / s ^ 2 * (|a| * |b|) := by
      rw [abs_div, abs_div, abs_of_pos hs]; field_simp

/-! ### The grid on the torus -/

/-- The corner `s(n + ½)` of the grid of side `s`, for `n ∈ ℤ/Pℤ`. -/
def corner (s : ℝ) {P : ℕ} (n : ZMod P) : ℝ := s * ((n.val : ℝ) + 1 / 2)

section Grid

variable {P : ℕ} [NeZero P] {s : ℝ}

/-- The value of the factor at a corner is `h(u - m)` with `u = t/s - ½` and an integer `m ≡ n`, `|u - m| ≤ P/2`. -/
lemma gT_corner (hP : ℓ = P * s) (hs : 0 < s) (t : ℝ) (n : ZMod P) :
    ∃ m : ℤ, (m : ZMod P) = n ∧ |t / s - 1 / 2 - m| ≤ P / 2 ∧
      gT hℓ s (corner s n) t = prof (t / s - 1 / 2 - m) := by
  obtain ⟨w, hw⟩ := rep_eq_sub hℓ (t - corner s n)
  refine ⟨n.val + w * P, by simp, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := rep_mem hℓ (t - corner s n)
    have : rep hℓ (t - corner s n) = s * (t / s - 1 / 2 - ((n.val + w * P : ℤ) : ℝ)) := by
      rw [hw, corner, hP]; push_cast; field_simp; ring
    rw [this, hP] at h1 h2
    rw [abs_le]
    constructor
    · by_contra hc
      push_neg at hc
      nlinarith
    · by_contra hc
      push_neg at hc
      nlinarith
  · unfold gT
    congr 1
    rw [hw, corner, hP]; push_cast; field_simp; ring

/-- In one dimension, the squares of the factors of the corners add up to `1`, and only the corners
`⌊u⌋`, `⌊u⌋ + 1` (`u = t/s - ½`) contribute. -/
lemma torus_sum (hP : ℓ = P * s) (hP2 : 2 ≤ P) (hs : 0 < s) (t : ℝ) :
    (∀ n : ZMod P, n ∉ ({((⌊t / s - 1 / 2⌋ : ℤ) : ZMod P), ((⌊t / s - 1 / 2⌋ + 1 : ℤ) : ZMod P)} :
      Finset (ZMod P)) → gT hℓ s (corner s n) t = 0) ∧
    ∑ n : ZMod P, gT hℓ s (corner s n) t ^ 2 = 1 := by
  haveI : Fact (1 < P) := ⟨by omega⟩
  set u := t / s - 1 / 2 with hu
  set m₀ := ⌊u⌋ with hm₀
  have hP2' : (2 : ℝ) ≤ P := by exact_mod_cast hP2
  -- two integers in the same class mod `P` are equal or at least `P` apart
  have apart : ∀ m m' : ℤ, (m : ZMod P) = (m' : ZMod P) → m ≠ m' → (P : ℝ) ≤ |(m : ℝ) - m'| := by
    intro m m' he hne
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at he
    obtain ⟨q, hq⟩ := he
    have hq0 : q ≠ 0 := by rintro rfl; apply hne; omega
    have hq' : ((m' : ℝ) - m) = (P : ℝ) * q := by exact_mod_cast hq
    rw [abs_sub_comm, hq', abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ P)]
    have : (1 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hq0
    nlinarith
  have hfl1 := Int.floor_le u
  have hfl2 := Int.lt_floor_add_one u
  have hne : ((m₀ : ℤ) : ZMod P) ≠ ((m₀ + 1 : ℤ) : ZMod P) := by
    intro h
    have := apart m₀ (m₀ + 1) h (by omega)
    push_cast at this
    rw [show (m₀ : ℝ) - (m₀ + 1) = -1 by ring, abs_neg, abs_one] at this
    linarith
  -- the value at the class of `m'` with `|u - m'| ≤ 1` is `h(u - m')`
  have value : ∀ m' : ℤ, |u - m'| ≤ 1 → gT hℓ s (corner s (m' : ZMod P)) t = prof (u - m') := by
    intro m' hm'
    obtain ⟨m, hm, hmP, hval⟩ := gT_corner hℓ hP hs t (m' : ZMod P)
    rw [hval]
    by_cases heq : m = m'
    · rw [heq]
    · have hap := apart m m' hm heq
      have h1 : 2 / 3 ≤ |u - m| := by
        have := abs_sub_abs_le_abs_sub ((m : ℝ) - m') (u - m')
        rw [show (m : ℝ) - m' - (u - m') = -(u - m) by ring, abs_neg] at this
        linarith
      have h2 : 2 / 3 ≤ |u - m'| := by
        have := abs_sub_abs_le_abs_sub ((m : ℝ) - m') (m - u)
        rw [show (m : ℝ) - m' - (m - u) = u - m' by ring, abs_sub_comm (m : ℝ) u] at this
        linarith
      rw [prof_eq_zero h1, prof_eq_zero h2]
  have hzero : ∀ n : ZMod P, n ∉ ({((m₀ : ℤ) : ZMod P), ((m₀ + 1 : ℤ) : ZMod P)} : Finset (ZMod P)) →
      gT hℓ s (corner s n) t = 0 := by
    intro n hn
    obtain ⟨m, hm, -, hval⟩ := gT_corner hℓ hP hs t n
    rw [hval]
    apply prof_eq_zero_of_not_mem
    intro hmem
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h
    · left; rw [← hm, h]
    · right; rw [← hm, h]
  refine ⟨hzero, ?_⟩
  rw [← Finset.sum_subset (Finset.subset_univ _) fun n _ hn => by rw [hzero n hn]; ring,
    Finset.sum_pair hne, value m₀ (by rw [abs_le]; constructor <;> linarith),
    value (m₀ + 1) (by push_cast; rw [abs_le]; constructor <;> linarith)]
  exact pair_sum u

/-- The function of the cube of side `2s` centred at `c`. -/
def phiT (s : ℝ) (c x : Fin 4 → ℝ) : ℝ := ∏ μ, gT hℓ s (c μ) (x μ)

/-- The centre `s(n + ½)` of a cube of the family at the scale of side `s`. -/
def cen (s : ℝ) (n : Fin 4 → ZMod P) : Fin 4 → ℝ := fun μ => corner s (n μ)

lemma phiT_nonneg (s : ℝ) (c x : Fin 4 → ℝ) : 0 ≤ phiT hℓ s c x :=
  Finset.prod_nonneg fun μ _ => gT_nonneg hℓ _ _ _

lemma phiT_le_one (s : ℝ) (c x : Fin 4 → ℝ) : phiT hℓ s c x ≤ 1 :=
  Finset.prod_le_one₀ (fun μ _ => gT_nonneg hℓ _ _ _) fun μ _ => gT_le_one hℓ _ _ _

/-- In four dimensions, the squares of the functions of the cubes centred at all the corners add up to `1`. -/
theorem torus_grid_sum (hP : ℓ = P * s) (hP2 : 2 ≤ P) (hs : 0 < s) (x : Fin 4 → ℝ) :
    ∑ n : Fin 4 → ZMod P, phiT hℓ s (cen s n) x ^ 2 = 1 := by
  have h : ∀ n : Fin 4 → ZMod P, phiT hℓ s (cen s n) x ^ 2 = ∏ μ, gT hℓ s (corner s (n μ)) (x μ) ^ 2 :=
    fun n => by unfold phiT cen; rw [Finset.prod_pow]
  simp only [h]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ)
    (fun μ k => gT hℓ s (corner s k) (x μ) ^ 2)]
  exact Finset.prod_eq_one fun μ _ => (torus_sum hℓ hP hP2 hs (x μ)).2

/-- At most `2⁴` functions of the cubes at one scale do not vanish at a point. -/
theorem card_nonzero_le (hP : ℓ = P * s) (hP2 : 2 ≤ P) (hs : 0 < s) (x : Fin 4 → ℝ) :
    (Finset.univ.filter fun n : Fin 4 → ZMod P => phiT hℓ s (cen s n) x ≠ 0).card ≤ 16 := by
  set t : Fin 4 → Finset (ZMod P) := fun μ =>
    {((⌊x μ / s - 1 / 2⌋ : ℤ) : ZMod P), ((⌊x μ / s - 1 / 2⌋ + 1 : ℤ) : ZMod P)}
  have hsub : (Finset.univ.filter fun n : Fin 4 → ZMod P => phiT hℓ s (cen s n) x ≠ 0) ⊆
      Fintype.piFinset t := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
    rw [Fintype.mem_piFinset]
    intro μ
    by_contra hμ
    apply hn
    exact Finset.prod_eq_zero (Finset.mem_univ μ) ((torus_sum hℓ hP hP2 hs (x μ)).1 _ hμ)
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ μ, (t μ).card ≤ ∏ _μ : Fin 4, 2 := Finset.prod_le_prod fun μ _ => Finset.card_le_two
    _ = 16 := by simp

end Grid

end PartitionUnity
end CoreLean

end
