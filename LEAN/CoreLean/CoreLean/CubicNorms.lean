/-
`lem:cubic-gradient` of BALABAN_CORE.tex in the weighted norms of a sequence of domains.

The sequence of domains is `Blocks.DomSeq` on the fine lattice `Site n = (ℤ/n)⁴`, with the scale `j(x)` of a
site (`sc`); the spacing of the scale `j` is `a_j = L^j η`, `η = ‖a‖`. The weighted norm
`‖f‖_{∞,(α)} = sup_x a_{j(x)}^{-α} max_ι ‖f_ι(x)‖` (`def:norms`(iii)) is `wnorm`, and
`‖A‖_{∞,*} = max(‖A‖_{∞,(-1)}, ‖∇_𝐔A‖_{∞,(-2)})` (`def:scaled-norms`) is `normStar`, with `∇_𝐔A` the family of
the forward differences `D_{𝐔,κ}A_l`.

The core's step "the bonds of the plaquettes of `st(b)` lie in `Ω_{j-1}`, by `eq:separation`" is `near`:
two sites at the distance `|x - z|_∞ ≤ 3` have scales which differ by at most one when `RM ≥ 1` (by `far`,
since `L ≥ 3`). Every site which `cubic_gradient_bond` uses at the bond `b = (μ, x)` lies at a distance of at
most `3` from `x` (`star_near`), so the weights there are at least `a_{j-1} ≥ a_j/L`, and the hypotheses of
`cubic_gradient_bond` follow from `‖A‖_{∞,*} ≤ m` and the plaquette bound on `Ω_{j-1}`. This gives
`cubic_gradient`: `‖𝖭₀(A)‖_{∞,(-3)} ≤ C₀‖A‖_{∞,*}²` for `‖A‖_{∞,*} ≤ c₆/(2L)` (`eq:cubic-gradient`).
-/
import CoreLean.CubicBound
import CoreLean.BlockPartition

open Matrix Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

open Blocks

variable {N n : ℕ} [NeZero n] (a : ℂ)

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N}

/-! ### Distances on the fine lattice -/

lemma dinf_add_unit (x : Site n) (μ : Fin 4) : dinf (x + unit n μ) x ≤ 1 := by
  unfold dinf
  refine Finset.sup_le fun κ _ => ?_
  rw [Pi.add_apply, add_sub_cancel_left]
  simp only [unit, Pi.single_apply]
  split_ifs
  · simpa using cd_intCast_le (N := n) (1 : ℤ)
  · simp [cd_zero]

lemma dinf_sub_unit (x : Site n) (μ : Fin 4) : dinf (x - unit n μ) x ≤ 1 := by
  rw [dinf_comm]
  have := dinf_add_unit (x - unit n μ) μ
  rwa [sub_add_cancel] at this

/-- Every site which `cubic_gradient_bond` uses at the bond `(μ, x)` is at the distance `≤ 3` from `x`. -/
lemma star_near (x : Site n) (μ ν : Fin 4) {y : Site n}
    (hy : y ∈ ({x, x - unit n ν} : Finset (Site n))) {z : Site n}
    (hz : z ∈ ({y, y + unit n ν, y + unit n μ, y + unit n ν + unit n μ} : Finset (Site n))) :
    dinf z x ≤ 3 := by
  have hyx : dinf y x ≤ 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · simp [dinf, cd_zero]
    · exact dinf_sub_unit x ν
  have hzy : dinf z y ≤ 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simp [dinf, cd_zero]
    · exact (dinf_add_unit y ν).trans (by norm_num)
    · exact (dinf_add_unit y μ).trans (by norm_num)
    · exact (dinf_triangle _ (y + unit n ν) _).trans
        (by have := dinf_add_unit (y + unit n ν) μ; have := dinf_add_unit y ν; omega)
  have := dinf_triangle z y x
  omega

namespace Blocks.DomSeq

variable (S : DomSeq n)

/-- Two sites at the distance `≤ 3` have scales which differ by at most one (`eq:separation`). -/
lemma near (hRM : 1 ≤ S.RM) {x z : Site n} (h : dinf z x ≤ 3) : S.sc x ≤ S.sc z + 1 := by
  by_contra h'
  push_neg at h'
  have hf := S.far (x := z) (x' := x) (by omega)
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hpow : (S.L : ℝ) ≤ (S.L : ℝ) ^ (S.sc x - 1) := by
    calc (S.L : ℝ) = (S.L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have h3 : (3 : ℝ) ≤ S.RM * (S.L : ℝ) ^ (S.sc x - 1) := by nlinarith
  have hd : (dinf z x : ℝ) ≤ 3 := by exact_mod_cast h
  linarith

/-- The spacing `a_j = L^j η`. -/
def spacing (η : ℝ) (j : ℕ) : ℝ := (S.L : ℝ) ^ j * η

lemma one_le_L : (1 : ℝ) ≤ S.L := by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L)

lemma spacing_pos {η : ℝ} (hη : 0 < η) (j : ℕ) : 0 < S.spacing η j := by
  unfold spacing; have := S.one_le_L; positivity

lemma le_spacing {η : ℝ} (hη : 0 < η) (j : ℕ) : η ≤ S.spacing η j := by
  unfold spacing
  exact le_mul_of_one_le_left hη.le (one_le_pow₀ S.one_le_L)

/-- `a_i ≤ L a_{i'}` for `i ≤ i' + 1`. -/
lemma spacing_le {η : ℝ} (hη : 0 < η) {i i' : ℕ} (h : i ≤ i' + 1) :
    S.spacing η i ≤ S.L * S.spacing η i' := by
  unfold spacing
  have : (S.L : ℝ) ^ i ≤ (S.L : ℝ) ^ (i' + 1) := pow_le_pow_right₀ S.one_le_L h
  rw [pow_succ] at this
  nlinarith

/-- The weighted norm `‖f‖_{∞,(α)} = sup_x a_{j(x)}^{-α} max_ι ‖f_ι(x)‖` (`def:norms`(iii)). -/
def wnorm (η : ℝ) (α : ℤ) {ι : Type*} [Fintype ι] (f : ι → Site n → Mat) : ℝ :=
  ⨆ i : ι, ⨆ x : Site n, S.spacing η (S.sc x) ^ (-α) * ‖f i x‖

lemma le_wnorm (η : ℝ) (α : ℤ) {ι : Type*} [Fintype ι] (f : ι → Site n → Mat) (i : ι) (x : Site n) :
    S.spacing η (S.sc x) ^ (-α) * ‖f i x‖ ≤ S.wnorm η α f := by
  unfold wnorm
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ x : Site n, S.spacing η (S.sc x) ^ (-α) * ‖f i x‖)
    (Set.finite_range _).bddAbove i)
  exact le_ciSup (f := fun x : Site n => S.spacing η (S.sc x) ^ (-α) * ‖f i x‖)
    (Set.finite_range _).bddAbove x

lemma wnorm_le (η : ℝ) (α : ℤ) {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → Site n → Mat) {B : ℝ}
    (h : ∀ i x, S.spacing η (S.sc x) ^ (-α) * ‖f i x‖ ≤ B) : S.wnorm η α f ≤ B :=
  ciSup_le fun i => ciSup_le fun x => h i x

lemma wnorm_nonneg {η : ℝ} (hη : 0 < η) (α : ℤ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → Site n → Mat) : 0 ≤ S.wnorm η α f := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h0 : (0 : Site n) = 0 := rfl
  exact (mul_nonneg (zpow_nonneg (S.spacing_pos hη _).le _) (norm_nonneg _)).trans
    (S.le_wnorm η α f i 0)

/-- `‖A‖_{∞,*} = max(‖A‖_{∞,(-1)}, ‖∇_𝐔A‖_{∞,(-2)})` (`def:scaled-norms`), `η = ‖a‖`. -/
def normStar (U : Config N n) (A : Form1 N n) : ℝ :=
  max (S.wnorm ‖a‖ (-1) fun μ x => A μ x)
    (S.wnorm ‖a‖ (-2) fun (p : Fin 4 × Fin 4) x => Dfw a U p.1 (A p.2) x)

lemma normStar_A (U : Config N n) (A : Form1 N n) (μ : Fin 4) (x : Site n) :
    S.spacing ‖a‖ (S.sc x) * ‖A μ x‖ ≤ S.normStar a U A := by
  have := S.le_wnorm ‖a‖ (-1) (fun μ x => A μ x) μ x
  simp only [neg_neg, zpow_one] at this
  exact this.trans (le_max_left _ _)

lemma normStar_D (U : Config N n) (A : Form1 N n) (κ l : Fin 4) (x : Site n) :
    S.spacing ‖a‖ (S.sc x) ^ 2 * ‖Dfw a U κ (A l) x‖ ≤ S.normStar a U A := by
  have := S.le_wnorm ‖a‖ (-2) (fun (p : Fin 4 × Fin 4) x => Dfw a U p.1 (A p.2) x) (κ, l) x
  simp only [neg_neg] at this
  exact (le_of_eq (by norm_cast)).trans (this.trans (le_max_right _ _))

/-- From a weighted bound to a local one: `‖f(z)‖ ≤ (L/a_j)^p m` when `a_{j(z)}^p‖f(z)‖ ≤ m` and
`j(x) ≤ j(z) + 1`. -/
lemma local_of_weighted (ha : a ≠ 0) {x z : Site n} (hxz : S.sc x ≤ S.sc z + 1) {m v : ℝ} (p : ℕ)
    (hv : 0 ≤ v) (h : S.spacing ‖a‖ (S.sc z) ^ p * v ≤ m) :
    v ≤ (S.L : ℝ) ^ p / S.spacing ‖a‖ (S.sc x) ^ p * m := by
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hs := S.spacing_pos hη (S.sc x)
  have hz := S.spacing_pos hη (S.sc z)
  have hle : S.spacing ‖a‖ (S.sc x) ^ p ≤ (S.L : ℝ) ^ p * S.spacing ‖a‖ (S.sc z) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hs.le (S.spacing_le hη hxz) p
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc v * S.spacing ‖a‖ (S.sc x) ^ p ≤ v * ((S.L : ℝ) ^ p * S.spacing ‖a‖ (S.sc z) ^ p) :=
        mul_le_mul_of_nonneg_left hle hv
    _ = (S.L : ℝ) ^ p * (S.spacing ‖a‖ (S.sc z) ^ p * v) := by ring
    _ ≤ (S.L : ℝ) ^ p * m := mul_le_mul_of_nonneg_left h (by positivity)

/-- `lem:cubic-gradient` (`eq:cubic-gradient`): for a sequence of domains with `RM ≥ 1`, a configuration whose
plaquettes with corners in `Ω_j` satisfy `‖𝐔(∂p) - 1‖ ≤ ε(η/a_j)²`, `L²ε ≤ c₆`, whose transports change the
operator norm by a factor of at most `2`, and a `1`-form `A` with values in `𝔤^c` and `‖A‖_{∞,*} ≤ c₆/(2L)`:
`‖𝖭₀(A)‖_{∞,(-3)} ≤ C₀‖A‖_{∞,*}²`, `C₀ = 4(84√NL³ + 108L³ + 6C₈L⁴)`, `C₈ = 512N`. -/
theorem cubic_gradient [NeZero N] (hG : G.LieInput) (ha : a ≠ 0) (hRM : 1 ≤ S.RM) (U : Config N n)
    (hU : ∀ μ x, U μ x ∈ G.complexified) {ε : ℝ} (hε : 0 ≤ ε)
    (hLε : (S.L : ℝ) ^ 2 * ε ≤ 1 / (48 * Real.sqrt N))
    (hP : ∀ (j : ℕ) (ν μ : Fin 4) (y : Site n),
      (∀ z ∈ ({y, y + unit n ν, y + unit n μ, y + unit n ν + unit n μ} : Finset (Site n)), z ∈ S.Ω j) →
      ‖((plaq U ν μ y : GLN) : Mat) - 1‖ ≤ ε * (‖a‖ / S.spacing ‖a‖ j) ^ 2)
    (hTr : ∀ μ x (Z : Mat), ‖Ad (U μ x) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (U μ x)⁻¹ Z‖ ≤ 2 * ‖Z‖)
    (A : Form1 N n) (hA : ∀ μ x, A μ x ∈ G.lieC)
    (hm : S.normStar a U A ≤ 1 / (48 * Real.sqrt N) / (2 * S.L)) :
    S.wnorm ‖a‖ (-3) (fun μ x => N0 a hG U A μ x) ≤
      4 * (84 * Real.sqrt N * (S.L : ℝ) ^ 3 + 108 * (S.L : ℝ) ^ 3 + 6 * (512 * N) * (S.L : ℝ) ^ 4) *
        S.normStar a U A ^ 2 := by
  have hη : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set m := S.normStar a U A with hmdef
  have hm0 : 0 ≤ m := (S.wnorm_nonneg hη (-1) fun μ x => A μ x).trans (le_max_left _ _)
  refine S.wnorm_le ‖a‖ (-3) _ fun μ x => ?_
  simp only [neg_neg]
  set s := S.spacing ‖a‖ (S.sc x) with hsdef
  have hs0 : 0 < s := S.spacing_pos hη _
  -- the sites of `st(b)` have the scale `≥ j(x) - 1`
  have hnear : ∀ ν, ∀ y ∈ ({x, x - unit n ν} : Finset (Site n)),
      ∀ z ∈ ({y, y + unit n ν, y + unit n μ, y + unit n ν + unit n μ} : Finset (Site n)),
        S.sc x ≤ S.sc z + 1 := fun ν y hy z hz => S.near hRM (star_near x μ ν hy hz)
  have hAloc : ∀ (l : Fin 4) (z : Site n), S.sc x ≤ S.sc z + 1 → ‖A l z‖ ≤ S.L / s * m := by
    intro l z hxz
    have := S.local_of_weighted a ha hxz 1 (norm_nonneg _)
      (by simpa using S.normStar_A a U A l z)
    simpa [hsdef] using this
  have hDloc : ∀ (κ l : Fin 4) (z : Site n), S.sc x ≤ S.sc z + 1 →
      ‖Dfw a U κ (A l) z‖ ≤ (S.L : ℝ) ^ 2 / s ^ 2 * m := fun κ l z hxz =>
    S.local_of_weighted a ha hxz 2 (norm_nonneg _) (S.normStar_D a U A κ l z)
  have hb := cubic_gradient_bond a hG ha U hU A hA μ x (s := s) (L := S.L) (m := m) (ε := ε)
    (S.le_spacing hη _) S.one_le_L hm0 hε hLε hm ?_ ?_ ?_ ?_ ?_ ?_
  · -- `‖𝖭₀(A)(b)‖ ≤ C₀s⁻³m²` gives `s³‖𝖭₀(A)(b)‖ ≤ C₀m²`
    have e : s ^ (3 : ℤ) = s ^ 3 := by norm_cast
    rw [e]
    calc s ^ 3 * ‖N0 a hG U A μ x‖
        ≤ s ^ 3 * (4 * (84 * Real.sqrt N * (S.L : ℝ) ^ 3 + 108 * (S.L : ℝ) ^ 3 +
            6 * (512 * N) * (S.L : ℝ) ^ 4) * (s ^ 3)⁻¹ * m ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by field_simp
  · -- the plaquettes: their corners lie in `Ω_{j-1}`
    intro ν hν y hy
    have hcorner : ∀ z ∈ ({y, y + unit n ν, y + unit n μ, y + unit n ν + unit n μ} : Finset (Site n)),
        z ∈ S.Ω (S.sc x - 1) := fun z hz =>
      (S.mem_iff z _).mpr (by have := hnear ν y hy z hz; omega)
    refine (hP (S.sc x - 1) ν μ y hcorner).trans ?_
    have hle : s ≤ S.L * S.spacing ‖a‖ (S.sc x - 1) := S.spacing_le hη (by omega)
    have hpos := S.spacing_pos hη (S.sc x - 1)
    have hq : ‖a‖ / S.spacing ‖a‖ (S.sc x - 1) ≤ S.L * (‖a‖ / s) := by
      rw [div_le_iff₀ hpos, mul_comm (S.L : ℝ), mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hs0]
      nlinarith
    calc ε * (‖a‖ / S.spacing ‖a‖ (S.sc x - 1)) ^ 2 ≤ ε * (S.L * (‖a‖ / s)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq 2) hε
      _ = (S.L : ℝ) ^ 2 * ε * (‖a‖ / s) ^ 2 := by ring
  · -- the values of `A`
    intro ν hν y hy
    have h0 := hnear ν y hy y (by simp)
    have h1 := hnear ν y hy (y + unit n ν) (by simp)
    have h2 := hnear ν y hy (y + unit n μ) (by simp)
    exact ⟨hAloc ν y h0, hAloc μ y h0, hAloc μ _ h1, hAloc ν _ h2⟩
  · intro ν _ y _ Z
    exact ⟨(hTr ν y Z).1, (hTr μ y Z).1⟩
  · intro ν _ Z
    simp only [Config.val, Bond.pos, Bond.dir, Bond.site, if_false]
    exact (hTr ν (x - unit n ν) Z).2
  · -- the first differences
    intro ν hν y hy
    have h0 := hnear ν y hy y (by simp)
    exact ⟨hDloc ν μ y h0, hDloc μ ν y h0⟩
  · intro ν hν
    exact hDloc ν ν _ (hnear ν (x - unit n ν) (by simp) (x - unit n ν) (by simp))

end Blocks.DomSeq

end CoreLean
