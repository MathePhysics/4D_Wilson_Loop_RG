/-
The box geometry of `cor:axial-straight` of BALABAN_CORE.tex (`46b63b49e8d2`), `def:lattices`.

Points are integer offsets from `c'₋` in the units of the fine lattice (the torus has the side
`2L^{m_T + k} ≥ 2L^{k+1}` in these units, larger than the box `𝖡`, so no identification occurs inside it).
`T^{(i)}` is the set of points whose coordinates are multiples of `L^i`; the cell of `c ∈ T^{(n)}` contains
the points `x` with `|x_σ - c_σ| ≤ (L^n - 1)/2`, written `-(L^n - 1) ≤ 2(x_σ - c_σ) ≤ L^n - 1` (`Blk`); so
`B^n(c) = Blk n c ∩ T^{(0)}` and `B(y) = Blk (i + 1) y ∩ T^{(i)}` for `y ∈ T^{(i+1)}` (`eq:block`).
`𝖡 = B^j(c'₋) ∪ B^j(c'₊)` with `c'₋ = 0`, `c'₊ = L^j e_μ`. Bonds are positive, `b = (x, x + L^i e_ρ)`,
as in the reductions of `lem:axial-smallness`.

Proved: every point of `T^{(i)}` lies in exactly one block of the order `i + 1` (`par`); blocks nest;
the parents of the two ends of a bond coincide or are neighbours in the direction of the bond; the bond
`c̃` of the proof exists and lies in `𝖡` together with its two blocks (`exists_ctilde`); the sides of
`𝖡` are inherited by the parents, so that `s(b) = id` for a bond in one block and `s(b) = s(c̃)` for a
bond between two blocks; the only positive bond of `T^{(j)}` with both ends in `𝖡` is `c'`; a positive
bond never runs from `B^j(c'₊)` to `B^j(c'₋)`. With these, `axial_straight` gives `eq:axial-straight`
with only `lem:axial-smallness` (for `c̃` and the field `V₀` of the proof) as a hypothesis.
-/
import Mathlib
import CoreLean.AxialStraight

noncomputable section

namespace CoreLean

namespace BoxGeometry

open Classical

set_option linter.unusedSectionVars false

/-! ### Integers -/

/-- A multiple `Pt` of `P` with `|2Pt| < PK + P`, `K` odd, satisfies `|2Pt| ≤ PK - P`. -/
lemma sharp {P K t : ℤ} (hP : 0 < P) (hK : Odd K) (h1 : -(P * K + P) < 2 * (P * t))
    (h2 : 2 * (P * t) < P * K + P) : -(P * K - P) ≤ 2 * (P * t) ∧ 2 * (P * t) ≤ P * K - P := by
  obtain ⟨u, rfl⟩ := hK
  have a : 2 * t < 2 * u + 2 := lt_of_mul_lt_mul_left (by nlinarith) hP.le
  have b : -(2 * u + 2) < 2 * t := lt_of_mul_lt_mul_left (by nlinarith) hP.le
  have a' : t ≤ u := by omega
  have b' : -u ≤ t := by omega
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left a' hP.le, mul_le_mul_of_nonneg_left b' hP.le]

/-- The nearest multiple of an odd `M > 0`. -/
lemma exists_near {M : ℤ} (hM : 0 < M) (hodd : Odd M) (a : ℤ) :
    ∃ q, M ∣ q ∧ -(M - 1) ≤ 2 * (a - q) ∧ 2 * (a - q) ≤ M - 1 := by
  obtain ⟨h, rfl⟩ := hodd
  refine ⟨(2 * h + 1) * ((a + h) / (2 * h + 1)), dvd_mul_right _ _, ?_⟩
  have e := Int.mul_ediv_add_emod (a + h) (2 * h + 1)
  have r0 := Int.emod_nonneg (a + h) (ne_of_gt hM)
  have r1 := Int.emod_lt_of_pos (a + h) hM
  constructor <;> omega

lemma unique_near {M q q' a : ℤ} (hM : 0 < M) (hq : M ∣ q) (hq' : M ∣ q')
    (h1 : -(M - 1) ≤ 2 * (a - q)) (h2 : 2 * (a - q) ≤ M - 1)
    (h1' : -(M - 1) ≤ 2 * (a - q')) (h2' : 2 * (a - q') ≤ M - 1) : q = q' := by
  obtain ⟨t, ht⟩ := dvd_sub hq hq'
  have a1 : M * t < M * 1 := by rw [← ht]; linarith
  have a2 : M * (-1) < M * t := by rw [← ht]; linarith
  have b1 := lt_of_mul_lt_mul_left a1 hM.le
  have b2 := lt_of_mul_lt_mul_left a2 hM.le
  have : t = 0 := by omega
  rw [this, mul_zero] at ht
  linarith

/-! ### Lattices, cells, and blocks -/

variable (L : ℤ)

/-- The points of `T^{(i)}`. -/
def Lat (i : ℕ) (x : Fin 4 → ℤ) : Prop := ∀ σ, L ^ i ∣ x σ

/-- `x` lies in the cell of side `L^n` centred at `c`. -/
def Blk (n : ℕ) (c x : Fin 4 → ℤ) : Prop :=
  ∀ σ, -(L ^ n - 1) ≤ 2 * (x σ - c σ) ∧ 2 * (x σ - c σ) ≤ L ^ n - 1

/-- `q` is the multiple of `L^n` nearest to `a`. -/
def Near (n : ℕ) (a q : ℤ) : Prop := L ^ n ∣ q ∧ -(L ^ n - 1) ≤ 2 * (a - q) ∧ 2 * (a - q) ≤ L ^ n - 1

/-- The centre of the block of the order `i + 1` which contains `x`. -/
def par (i : ℕ) (x : Fin 4 → ℤ) : Fin 4 → ℤ := fun σ => Classical.epsilon (Near L (i + 1) (x σ))

/-- `L^i e_ρ`. -/
def ev (i : ℕ) (ρ : Fin 4) : Fin 4 → ℤ := Pi.single ρ (L ^ i)

variable {L}

section Odd

variable (hL : Odd L) (hL1 : 1 ≤ L)
include hL hL1

lemma hL0 : 0 < L := by linarith

lemma par_spec (i : ℕ) (x : Fin 4 → ℤ) (σ : Fin 4) : Near L (i + 1) (x σ) (par L i x σ) :=
  Classical.epsilon_spec (exists_near (pow_pos (hL0 hL hL1) _) (hL.pow) (x σ))

lemma par_unique {i : ℕ} {x : Fin 4 → ℤ} {σ : Fin 4} {q : ℤ} (hq : Near L (i + 1) (x σ) q) :
    q = par L i x σ := by
  obtain ⟨d, h1, h2⟩ := hq
  obtain ⟨d', h1', h2'⟩ := par_spec hL hL1 i x σ
  exact unique_near (pow_pos (hL0 hL hL1) _) d d' h1 h2 h1' h2'

lemma par_lat (i : ℕ) (x : Fin 4 → ℤ) : Lat L (i + 1) (par L i x) := fun σ =>
  (par_spec hL hL1 i x σ).1

lemma blk_par (i : ℕ) (x : Fin 4 → ℤ) : Blk L (i + 1) (par L i x) x := fun σ =>
  (par_spec hL hL1 i x σ).2

/-- Every point lies in exactly one block of the order `i + 1`. -/
lemma par_eq_of_blk {i : ℕ} {x y : Fin 4 → ℤ} (hy : Lat L (i + 1) y) (hxy : Blk L (i + 1) y x) :
    y = par L i x :=
  funext fun σ => par_unique hL hL1 ⟨hy σ, hxy σ⟩

lemma blk_sharp {m n : ℕ} (hmn : m ≤ n) {q c : ℤ} (hq : L ^ m ∣ q) (hc : L ^ n ∣ c)
    (h1 : -(L ^ n + L ^ m) < 2 * (q - c)) (h2 : 2 * (q - c) < L ^ n + L ^ m) :
    -(L ^ n - L ^ m) ≤ 2 * (q - c) ∧ 2 * (q - c) ≤ L ^ n - L ^ m := by
  obtain ⟨t, ht⟩ := dvd_sub hq ((pow_dvd_pow L hmn).trans hc)
  have hn : L ^ n = L ^ m * L ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [ht, hn] at h1 h2 ⊢
  exact sharp (pow_pos (hL0 hL hL1) m) (hL.pow) h1 h2

/-- The centre of a smaller block containing a point of a cell lies in the cell. -/
lemma nest {m n : ℕ} (hmn : m ≤ n) {q c x : Fin 4 → ℤ} (hq : Lat L m q) (hc : Lat L n c)
    (hx : Blk L n c x) (hqx : Blk L m q x) : Blk L n c q := fun σ => by
  have hm1 : 1 ≤ L ^ m := one_le_pow₀ hL1
  obtain ⟨a1, a2⟩ := hx σ
  obtain ⟨b1, b2⟩ := hqx σ
  obtain ⟨c1, c2⟩ := blk_sharp hL hL1 hmn (hq σ) (hc σ) (by linarith) (by linarith)
  constructor <;> linarith

/-- A block whose centre lies in a cell lies in the cell. -/
lemma incl {m n : ℕ} (hmn : m ≤ n) {q c x : Fin 4 → ℤ} (hq : Lat L m q) (hc : Lat L n c)
    (hcq : Blk L n c q) (hqx : Blk L m q x) : Blk L n c x := fun σ => by
  have hm1 : 1 ≤ L ^ m := one_le_pow₀ hL1
  obtain ⟨a1, a2⟩ := hcq σ
  obtain ⟨b1, b2⟩ := hqx σ
  obtain ⟨c1, c2⟩ := blk_sharp hL hL1 hmn (hq σ) (hc σ) (by linarith) (by linarith)
  constructor <;> linarith

lemma ev_lat (i : ℕ) (ρ : Fin 4) : Lat L i (ev L i ρ) := fun σ => by
  by_cases h : σ = ρ
  · rw [h]; simp [ev]
  · simp [ev, Pi.single_eq_of_ne h]

lemma lat_add {i : ℕ} {x y : Fin 4 → ℤ} (hx : Lat L i x) (hy : Lat L i y) : Lat L i (x + y) :=
  fun σ => dvd_add (hx σ) (hy σ)

lemma lat_sub {i : ℕ} {x y : Fin 4 → ℤ} (hx : Lat L i x) (hy : Lat L i y) : Lat L i (x - y) :=
  fun σ => dvd_sub (hx σ) (hy σ)

/-- The parent of the second end of a bond along `ρ` is that of the first, or its neighbour along
`ρ`: one coordinate. -/
lemma near_step {i : ℕ} {a q : ℤ} (ha : L ^ i ∣ a) (hq : Near L (i + 1) a q) :
    Near L (i + 1) (a + L ^ i) q ∨ Near L (i + 1) (a + L ^ i) (q + L ^ (i + 1)) := by
  obtain ⟨hqd, h1, h2⟩ := hq
  have hP : 0 < L ^ i := pow_pos (hL0 hL hL1) i
  have hP1 : 1 ≤ L ^ i := one_le_pow₀ hL1
  obtain ⟨t, ht⟩ := dvd_sub ha ((pow_dvd_pow L (Nat.le_succ i)).trans hqd)
  have hM : L ^ (i + 1) = L ^ i * L := pow_succ L i
  rw [hM, ht] at h1 h2
  obtain ⟨l, hl⟩ := hL
  have t1 : 2 * t < L := lt_of_mul_lt_mul_left (by nlinarith) hP.le
  have t2 : -L < 2 * t := lt_of_mul_lt_mul_left (by nlinarith) hP.le
  simp only [Near, hM]
  by_cases hc : 2 * t + 2 ≤ L - 1
  · left
    have t3 : -(L - 1) ≤ 2 * t := by omega
    refine ⟨by rw [← hM]; exact hqd, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left t3 hP.le
      have e : a + L ^ i - q = L ^ i * t + L ^ i := by linarith
      rw [e]; nlinarith
    · have := mul_le_mul_of_nonneg_left hc hP.le
      have e : a + L ^ i - q = L ^ i * t + L ^ i := by linarith
      rw [e]; nlinarith
  · right
    have t3 : 2 * t = L - 1 := by omega
    have e : a + L ^ i - (q + L ^ i * L) = L ^ i * t + L ^ i - L ^ i * L := by linarith
    have e2 : L ^ i * (2 * t) = L ^ i * (L - 1) := by rw [t3]
    refine ⟨dvd_add (by rw [← hM]; exact hqd) (by rw [← hM]), ?_, ?_⟩
    · rw [e]; nlinarith
    · rw [e]; nlinarith

/-- The parents of the two ends of a bond along `ρ` coincide or are neighbours along `ρ`. -/
lemma par_bond {i : ℕ} {x : Fin 4 → ℤ} (hx : Lat L i x) (ρ : Fin 4) :
    par L i (x + ev L i ρ) = par L i x ∨ par L i (x + ev L i ρ) = par L i x + ev L (i + 1) ρ := by
  have hcoord : ∀ σ, σ ≠ ρ → par L i (x + ev L i ρ) σ = par L i x σ := fun σ h => by
    simp only [par, Pi.add_apply, ev, Pi.single_eq_of_ne h, add_zero]
  have hρ : (x + ev L i ρ) ρ = x ρ + L ^ i := by simp [ev]
  rcases near_step hL hL1 (hx ρ) (par_spec hL hL1 i x ρ) with h | h
  · left
    funext σ
    by_cases hσ : σ = ρ
    · rw [hσ]; exact (par_unique hL hL1 (by rw [hρ]; exact h)).symm
    · exact hcoord σ hσ
  · right
    funext σ
    by_cases hσ : σ = ρ
    · have e := par_unique hL hL1 (show Near L (i + 1) ((x + ev L i ρ) ρ) _ by rw [hρ]; exact h)
      rw [hσ, ← e]
      simp [ev]
    · rw [hcoord σ hσ, Pi.add_apply]
      simp [ev, Pi.single_eq_of_ne hσ]

end Odd

/-! ### The box `𝖡` -/

variable (L)

/-- `c'₊ = L^j e_μ`. -/
def cp (j : ℕ) (μ : Fin 4) : Fin 4 → ℤ := ev L j μ

/-- `𝖡 = B^j(c'₋) ∪ B^j(c'₊)`. -/
def InB (j : ℕ) (μ : Fin 4) (z : Fin 4 → ℤ) : Prop := Blk L j 0 z ∨ Blk L j (cp L j μ) z

/-- The side of `𝖡`: `z ∈ B^j(c'₋)`. -/
def side (j : ℕ) (z : Fin 4 → ℤ) : Prop := Blk L j 0 z

variable {L}

section Box

variable (hL : Odd L) (hL1 : 1 ≤ L) {j : ℕ} {μ : Fin 4}
include hL hL1

lemma cp_lat : Lat L j (cp L j μ) := ev_lat hL hL1 j μ

lemma zero_lat (i : ℕ) : Lat L i 0 := fun _ => dvd_zero _

/-- The two blocks of `𝖡` are disjoint. -/
lemma excl {z : Fin 4 → ℤ} (h0 : Blk L j 0 z) (h1 : Blk L j (cp L j μ) z) : False := by
  obtain ⟨-, a⟩ := h0 μ
  obtain ⟨b, -⟩ := h1 μ
  simp only [cp, ev, Pi.single_eq_same, Pi.zero_apply, sub_zero] at a b
  linarith

/-- `𝖡` is the box `|z_σ| ≤ (L^j - 1)/2` (`σ ≠ μ`), `-(L^j - 1)/2 ≤ z_μ ≤ L^j + (L^j - 1)/2`. -/
lemma inB_iff (z : Fin 4 → ℤ) : InB L j μ z ↔
    (∀ σ, σ ≠ μ → -(L ^ j - 1) ≤ 2 * z σ ∧ 2 * z σ ≤ L ^ j - 1) ∧
      -(L ^ j - 1) ≤ 2 * z μ ∧ 2 * z μ ≤ 3 * L ^ j - 1 := by
  have hp : 0 < L ^ j := pow_pos (hL0 hL hL1) j
  obtain ⟨w, hw⟩ := hL.pow (n := j)
  constructor
  · rintro (h | h)
    · refine ⟨fun σ _ => by simpa using h σ, ?_, ?_⟩
      · simpa using (h μ).1
      · have := (h μ).2; simp at this; linarith
    · refine ⟨fun σ hσ => by simpa [cp, ev, Pi.single_eq_of_ne hσ] using h σ, ?_, ?_⟩
      · have := (h μ).1; simp [cp, ev] at this; linarith
      · have := (h μ).2; simp [cp, ev] at this; linarith
  · rintro ⟨hσ, hμ1, hμ2⟩
    by_cases hc : 2 * z μ ≤ L ^ j - 1
    · left
      intro σ
      by_cases h : σ = μ
      · rw [h]; simp only [Pi.zero_apply, sub_zero]; exact ⟨hμ1, hc⟩
      · simpa using hσ σ h
    · right
      intro σ
      by_cases h : σ = μ
      · rw [h]; simp only [cp, ev, Pi.single_eq_same]; constructor <;> omega
      · simpa [cp, ev, Pi.single_eq_of_ne h] using hσ σ h

/-- The centre of the block of the order `i + 1 ≤ j` of a point of `𝖡` lies in `𝖡`, on the same side. -/
lemma side_par {i : ℕ} (hij : i + 1 ≤ j) {y z : Fin 4 → ℤ} (hy : Lat L (i + 1) y)
    (hyz : Blk L (i + 1) y z) (hz : InB L j μ z) : InB L j μ y ∧ (side L j y ↔ side L j z) := by
  rcases hz with h | h
  · have hy0 := nest hL hL1 hij hy (zero_lat hL hL1 j) h hyz
    exact ⟨Or.inl hy0, iff_of_true hy0 h⟩
  · have hyc := nest hL hL1 hij hy (cp_lat hL hL1) h hyz
    exact ⟨Or.inr hyc, iff_of_false (fun h' => excl hL hL1 h' hyc) (fun h' => excl hL hL1 h' h)⟩

/-- The block of a point of `T^{(i+1)}` in `𝖡`, `i + 1 ≤ j`, lies in `𝖡`. -/
lemma blk_sub_B {i : ℕ} (hij : i + 1 ≤ j) {y z : Fin 4 → ℤ} (hy : Lat L (i + 1) y)
    (hyB : InB L j μ y) (hyz : Blk L (i + 1) y z) : InB L j μ z := by
  rcases hyB with h | h
  · exact Or.inl (incl hL hL1 hij hy (zero_lat hL hL1 j) h hyz)
  · exact Or.inr (incl hL hL1 hij hy (cp_lat hL hL1) h hyz)

/-- `𝖡` contains at least two points of `T^{(i+1)}` on every line along `μ`: if `y + L^{i+1}e_μ` is
not in `𝖡`, then `y - L^{i+1}e_μ` is. -/
lemma neighbour {i : ℕ} (hij : i + 1 ≤ j) {y : Fin 4 → ℤ} (hyB : InB L j μ y)
    (hn : ¬ InB L j μ (y + ev L (i + 1) μ)) : InB L j μ (y - ev L (i + 1) μ) := by
  have hM : L ^ (i + 1) ≤ L ^ j := pow_le_pow_right₀ hL1 hij
  have hM0 : 0 < L ^ (i + 1) := pow_pos (hL0 hL hL1) _
  obtain ⟨w, hw⟩ := hL.pow (n := j)
  rw [inB_iff hL hL1] at hyB hn ⊢
  obtain ⟨hσ, h1, h2⟩ := hyB
  have hoff : ∀ σ, σ ≠ μ → ∀ s : ℤ, (y + s • ev L (i + 1) μ) σ = y σ := fun σ h s => by
    simp [ev, Pi.single_eq_of_ne h]
  refine ⟨fun σ h => ?_, ?_, ?_⟩
  · have := hoff σ h (-1); simp only [neg_smul, one_smul, ← sub_eq_add_neg] at this
    rw [this]; exact hσ σ h
  · simp only [Pi.sub_apply, ev, Pi.single_eq_same]
    by_contra hc
    apply hn
    refine ⟨fun σ h => ?_, ?_, ?_⟩
    · have := hoff σ h 1; simp only [one_smul] at this
      rw [this]; exact hσ σ h
    · simp only [Pi.add_apply, ev, Pi.single_eq_same]; linarith
    · simp only [Pi.add_apply, ev, Pi.single_eq_same]; omega
  · simp only [Pi.sub_apply, ev, Pi.single_eq_same]; linarith

/-- The points of `T^{(j)}` in `𝖡` are `c'₋` and `c'₊`. -/
lemma top_points {z : Fin 4 → ℤ} (hz : Lat L j z) (hzB : InB L j μ z) : z = 0 ∨ z = cp L j μ := by
  have hp : 0 < L ^ j := pow_pos (hL0 hL hL1) j
  rw [inB_iff hL hL1] at hzB
  obtain ⟨hσ, h1, h2⟩ := hzB
  have hoff : ∀ σ, σ ≠ μ → z σ = 0 := fun σ h => by
    obtain ⟨t, ht⟩ := hz σ
    obtain ⟨a, b⟩ := hσ σ h
    rw [ht] at a b
    have c1 : L ^ j * (2 * t) < L ^ j * 1 := by linarith
    have c2 : L ^ j * (-1) < L ^ j * (2 * t) := by linarith
    have d1 := lt_of_mul_lt_mul_left c1 hp.le
    have d2 := lt_of_mul_lt_mul_left c2 hp.le
    rw [ht, show t = 0 by omega, mul_zero]
  obtain ⟨t, ht⟩ := hz μ
  rw [ht] at h1 h2
  have c1 : L ^ j * (2 * t) < L ^ j * 3 := by linarith
  have c2 : L ^ j * (-1) < L ^ j * (2 * t) := by linarith
  have d1 := lt_of_mul_lt_mul_left c1 hp.le
  have d2 := lt_of_mul_lt_mul_left c2 hp.le
  rcases (show t = 0 ∨ t = 1 by omega) with h | h
  · left; funext σ
    by_cases hs : σ = μ
    · rw [hs, ht, h, mul_zero]; rfl
    · exact hoff σ hs
  · right; funext σ
    by_cases hs : σ = μ
    · rw [hs, ht, h, mul_one]; simp [cp, ev]
    · rw [hoff σ hs]; simp [cp, ev, Pi.single_eq_of_ne hs]

end Box

/-! ### The bonds and the bond `c̃` -/

variable (L)

/-- The positive bonds `(x, x + L^i e_ρ)` of `T^{(i)}` with both ends in `𝖡`. -/
def Bd (j : ℕ) (μ : Fin 4) (i : ℕ) : Type :=
  {b : (Fin 4 → ℤ) × Fin 4 // Lat L i b.1 ∧ InB L j μ b.1 ∧ InB L j μ (b.1 + ev L i b.2)}

/-- Both ends of `b` lie in one of the blocks `B(c̃₋)`, `B(c̃₊)`. -/
def OneBlk (j : ℕ) (μ : Fin 4) (i : ℕ) (b : Bd L j μ i) (ct : Bd L j μ (i + 1)) : Prop :=
  ∃ z, (z = ct.1.1 ∨ z = ct.1.1 + ev L (i + 1) ct.1.2) ∧ Blk L (i + 1) z b.1.1 ∧
    Blk L (i + 1) z (b.1.1 + ev L i b.1.2)

/-- `b` runs from `B(c̃₋)` to `B(c̃₊)`. -/
def Between (j : ℕ) (μ : Fin 4) (i : ℕ) (b : Bd L j μ i) (ct : Bd L j μ (i + 1)) : Prop :=
  Blk L (i + 1) ct.1.1 b.1.1 ∧ Blk L (i + 1) (ct.1.1 + ev L (i + 1) ct.1.2) (b.1.1 + ev L i b.1.2)

lemma blk_self {L : ℤ} (hL1 : 1 ≤ L) (n : ℕ) (c : Fin 4 → ℤ) : Blk L n c c := fun σ => by
  have := one_le_pow₀ (n := n) hL1
  simp only [sub_self, mul_zero]
  constructor <;> linarith

/-- The bond `c'` of `T^{(j)}`. -/
def cbond (hL : Odd L) (hL1 : 1 ≤ L) (j : ℕ) (μ : Fin 4) (_hj : 1 ≤ j) : Bd L j μ j :=
  ⟨(0, μ), zero_lat hL hL1 j, Or.inl (blk_self hL1 j 0),
    by show InB L j μ (0 + ev L j μ); rw [zero_add]; exact Or.inr (blk_self hL1 j (cp L j μ))⟩

/-- The target `s(b)`: `id` if both ends of `b` lie on one side of `𝖡`, `M^j(U)(c')` otherwise. -/
def sval {Gp : Type*} (j : ℕ) (μ : Fin 4) (e W : Gp) (i : ℕ) (b : Bd L j μ i) : Gp :=
  if (side L j b.1.1 ↔ side L j (b.1.1 + ev L i b.1.2)) then e else W

variable {L}

section Bonds

variable (hL : Odd L) (hL1 : 1 ≤ L) {j : ℕ} {μ : Fin 4}
include hL hL1

/-- A positive bond never runs from `B^j(c'₊)` to `B^j(c'₋)`: in `sval` the second case is
`b₋ ∈ B^j(c'₋)`, `b₊ ∈ B^j(c'₊)`, as in the corollary. -/
lemma mixed_orient {i : ℕ} (b : Bd L j μ i)
    (h : ¬ (side L j b.1.1 ↔ side L j (b.1.1 + ev L i b.1.2))) :
    side L j b.1.1 ∧ Blk L j (cp L j μ) (b.1.1 + ev L i b.1.2) := by
  obtain ⟨-, h1, h2⟩ := b.2
  by_cases hs : side L j b.1.1
  · have h' : ¬ side L j (b.1.1 + ev L i b.1.2) := fun h' => h (iff_of_true hs h')
    exact ⟨hs, h2.resolve_left h'⟩
  · exfalso
    have hs' : side L j (b.1.1 + ev L i b.1.2) := by
      by_contra h'; exact h (iff_of_false hs h')
    have hc := h1.resolve_left hs
    obtain ⟨a, -⟩ := hc μ
    obtain ⟨-, c⟩ := hs' μ
    have hd : 0 ≤ ev L i b.1.2 μ := by
      unfold ev; rw [Pi.single_apply]
      split_ifs
      · exact (pow_pos (hL0 hL hL1) i).le
      · exact le_refl 0
    simp only [cp, ev, Pi.single_eq_same] at a
    simp only [Pi.add_apply, Pi.zero_apply, sub_zero] at c
    linarith

/-- The only positive bond of `T^{(j)}` with both ends in `𝖡` is `c'`. -/
lemma top_bond (b : Bd L j μ j) : b.1 = (0, μ) := by
  obtain ⟨⟨x, ρ⟩, hx, hxB, hx'B⟩ := b
  have hp : 0 < L ^ j := pow_pos (hL0 hL hL1) j
  have h1 := top_points hL hL1 hx hxB
  have h2 := top_points hL hL1 (lat_add hL hL1 hx (ev_lat hL hL1 j ρ)) hx'B
  have hρρ : ev L j ρ ρ = L ^ j := by simp [ev]
  show (x, ρ) = (0, μ)
  rcases h1 with rfl | rfl
  · rw [zero_add] at h2
    rcases h2 with h | h
    · have := congrFun h ρ; rw [hρρ] at this; simp at this; linarith
    · have hρ : ρ = μ := by
        by_contra hne
        have := congrFun h ρ
        rw [hρρ] at this
        simp [cp, ev, hne] at this
        linarith
      rw [hρ]
  · exfalso
    rcases h2 with h | h
    · have := congrFun h μ
      by_cases hρ : ρ = μ
      · subst hρ; simp [cp, ev] at this; linarith
      · simp [cp, ev, Pi.single_eq_of_ne (Ne.symm hρ)] at this; linarith
    · have := congrFun h ρ
      by_cases hρ : ρ = μ
      · subst hρ; simp [cp, ev] at this; linarith
      · simp [cp, ev, hρ] at this; linarith

/-- The bond `c̃` of the proof of `cor:axial-straight`: for a positive bond `b` of `T^{(i)}`, `i < j`, with
both ends in `𝖡` there is a positive bond `c̃` of `T^{(i+1)}` with both ends in `𝖡` such that both ends
of `b` lie in one of the blocks `B(c̃₋)`, `B(c̃₊)`, or `b` runs from `B(c̃₋)` to `B(c̃₊)`. -/
theorem exists_ctilde {i : ℕ} (hij : i < j) (b : Bd L j μ i) :
    ∃ ct : Bd L j μ (i + 1), OneBlk L j μ i b ct ∨ Between L j μ i b ct := by
  obtain ⟨⟨x, ρ⟩, hx, hxB, hx'B⟩ := b
  have hij' : i + 1 ≤ j := hij
  have hy := par_lat hL hL1 i x
  have hyB := (side_par hL hL1 hij' hy (blk_par hL hL1 i x) hxB).1
  have hbx' := blk_par hL hL1 i (x + ev L i ρ)
  rcases par_bond hL hL1 hx ρ with h | h
  · rw [h] at hbx'
    by_cases hn : InB L j μ (par L i x + ev L (i + 1) μ)
    · refine ⟨⟨(par L i x, μ), hy, hyB, hn⟩, Or.inl ⟨par L i x, Or.inl rfl,
        blk_par hL hL1 i x, hbx'⟩⟩
    · have hm := neighbour hL hL1 hij' hyB hn
      refine ⟨⟨(par L i x - ev L (i + 1) μ, μ), lat_sub hL hL1 hy (ev_lat hL hL1 _ μ), hm,
        by simpa using hyB⟩, Or.inl ⟨par L i x, Or.inr (by simp), blk_par hL hL1 i x, hbx'⟩⟩
  · rw [h] at hbx'
    have hy'B : InB L j μ (par L i x + ev L (i + 1) ρ) := by
      rw [← h]
      exact (side_par hL hL1 hij' (par_lat hL hL1 i _) (blk_par hL hL1 i _) hx'B).1
    exact ⟨⟨(par L i x, ρ), hy, hyB, hy'B⟩, Or.inr ⟨blk_par hL hL1 i x, hbx'⟩⟩

/-- The blocks of `c̃` lie in `𝖡`: the plaquettes of the box `P = B(c̃₋) ∪ B(c̃₊)` of
`lem:axial-smallness` have their corners in `𝖡`. -/
lemma blocks_sub_B {i : ℕ} (hij : i < j) (ct : Bd L j μ (i + 1)) (z : Fin 4 → ℤ)
    (hz : Blk L (i + 1) ct.1.1 z ∨ Blk L (i + 1) (ct.1.1 + ev L (i + 1) ct.1.2) z) : InB L j μ z := by
  obtain ⟨⟨y, ρ⟩, hy, hyB, hy'B⟩ := ct
  rcases hz with h | h
  · exact blk_sub_B hL hL1 hij hy hyB h
  · exact blk_sub_B hL hL1 hij (lat_add hL hL1 hy (ev_lat hL hL1 _ ρ)) hy'B h

/-- `s(b) = id` for a bond in one block of the order `i + 1`. -/
lemma sval_one {Gp : Type*} (e W : Gp) {i : ℕ} (hij : i < j) (b : Bd L j μ i)
    (ct : Bd L j μ (i + 1)) (h : OneBlk L j μ i b ct) : sval L j μ e W i b = e := by
  obtain ⟨z, hz, h1, h2⟩ := h
  have hzl : Lat L (i + 1) z := by
    rcases hz with rfl | rfl
    · exact ct.2.1
    · exact lat_add hL hL1 ct.2.1 (ev_lat hL hL1 _ _)
  have s1 := (side_par hL hL1 hij hzl h1 b.2.2.1).2
  have s2 := (side_par hL hL1 hij hzl h2 b.2.2.2).2
  unfold sval
  simp only [s1.symm.trans s2, ↓reduceIte]

/-- `s(b) = s(c̃)` for a bond between two blocks of the order `i + 1`. -/
lemma sval_between {Gp : Type*} (e W : Gp) {i : ℕ} (hij : i < j) (b : Bd L j μ i)
    (ct : Bd L j μ (i + 1)) (h : Between L j μ i b ct) :
    sval L j μ e W i b = sval L j μ e W (i + 1) ct := by
  obtain ⟨h1, h2⟩ := h
  have s1 := (side_par hL hL1 hij ct.2.1 h1 b.2.2.1).2
  have s2 := (side_par hL hL1 hij (lat_add hL hL1 ct.2.1 (ev_lat hL hL1 _ _)) h2 b.2.2.2).2
  unfold sval
  have : (side L j b.1.1 ↔ side L j (b.1.1 + ev L i b.1.2)) ↔
      (side L j ct.1.1 ↔ side L j (ct.1.1 + ev L (i + 1) ct.1.2)) := by
    rw [s1, s2]
  by_cases hc : side L j ct.1.1 ↔ side L j (ct.1.1 + ev L (i + 1) ct.1.2)
  · simp only [this, hc, ↓reduceIte]
  · simp only [this, hc, ↓reduceIte]

/-- The two cases exclude each other: the blocks of the order `i + 1` are disjoint. -/
lemma not_one_and_between {i : ℕ} (b : Bd L j μ i) (ct : Bd L j μ (i + 1))
    (h1 : OneBlk L j μ i b ct) (h2 : Between L j μ i b ct) : False := by
  obtain ⟨z, hz, hz1, hz2⟩ := h1
  obtain ⟨hb1, hb2⟩ := h2
  have hzl : Lat L (i + 1) z := by
    rcases hz with rfl | rfl
    · exact ct.2.1
    · exact lat_add hL hL1 ct.2.1 (ev_lat hL hL1 _ _)
  have e1 := (par_eq_of_blk hL hL1 hzl hz1).trans (par_eq_of_blk hL hL1 ct.2.1 hb1).symm
  have e2 := (par_eq_of_blk hL hL1 hzl hz2).trans
    (par_eq_of_blk hL hL1 (lat_add hL hL1 ct.2.1 (ev_lat hL hL1 _ _)) hb2).symm
  have := congrFun (e1.symm.trans e2) ct.1.2
  simp [ev] at this
  linarith [pow_pos (hL0 hL hL1) (i + 1)]

end Bonds

/-! ### `cor:axial-straight` with the box geometry -/

/-- `cor:axial-straight` with the geometry of the box `𝖡` proved: for averages `Mi i b = M^i(U)(b)` on
the positive bonds of `T^{(i)}` with both ends in `𝖡`, `i ≤ j`, and `lem:axial-smallness` for every bond
`c̃` of `T^{(i+1)}` with both ends in `𝖡`, every bond `b` in `B(c̃₋) ∪ B(c̃₊)`, and the field `V₀` of the
proof (`id` inside the blocks, `W = M^{i+1}(U)(c̃)` between them), with `α₀ = 2αL^{-2(j-i-1)}`, `α₁ = 0`,
`‖M^i(U)(b) - s(b)‖ ≤ 4C_axα` for every such bond `b` and `0 ≤ i ≤ j` (`eq:axial-straight`). -/
theorem axial_straight_box (hL : Odd L) (hL1 : 1 ≤ L) {j : ℕ} (hj : 1 ≤ j) (μ : Fin 4)
    {Gp : Type*} [SeminormedAddCommGroup Gp] (C α : ℝ) (hC : 0 ≤ C) (hL2 : (2 : ℝ) ≤ L)
    (hα : 0 ≤ α) (e : Gp) (Mi : ∀ i, Bd L j μ i → Gp)
    (hax : ∀ i, i < j → ∀ (b : Bd L j μ i) (ct : Bd L j μ (i + 1)),
      OneBlk L j μ i b ct ∨ Between L j μ i b ct →
      ‖Mi i b - (if OneBlk L j μ i b ct then e else Mi (i + 1) ct)‖ ≤
        C * (2 * α * (((L : ℝ)) ^ 2)⁻¹ ^ (j - i - 1)))
    (i : ℕ) (hi : i ≤ j) (b : Bd L j μ i) :
    ‖Mi i b - sval L j μ e (Mi j (cbond L hL hL1 j μ hj)) i b‖ ≤ 4 * C * α := by
  set W := Mi j (cbond L hL hL1 j μ hj)
  let ct : ∀ i, i < j → Bd L j μ i → Bd L j μ (i + 1) := fun i hi b =>
    Classical.choose (exists_ctilde hL hL1 hi b)
  have hct : ∀ i (hi : i < j) b, OneBlk L j μ i b (ct i hi b) ∨ Between L j μ i b (ct i hi b) :=
    fun i hi b => Classical.choose_spec (exists_ctilde hL hL1 hi b)
  let V0 : ∀ i, Bd L j μ i → Gp := fun i b =>
    if hi : i < j then (if OneBlk L j μ i b (ct i hi b) then e else Mi (i + 1) (ct i hi b)) else e
  refine (AxialStraight.axial_straight j C L α hC hL2 hα Mi (sval L j μ e W) V0 ct ?_ ?_ ?_ i hi b).2
  · -- the order `j`: `b = c'` and `s(c') = M^j(U)(c')`
    intro b
    have hb : b = cbond L hL hL1 j μ hj := Subtype.ext (top_bond hL hL1 b)
    subst hb
    unfold sval
    have h0 : side L j (0 : Fin 4 → ℤ) := blk_self hL1 j 0
    have hc : ¬ side L j (cp L j μ) := fun h => excl hL hL1 h (blk_self hL1 j (cp L j μ))
    have hne : ¬ (side L j (cbond L hL hL1 j μ hj).1.1 ↔
        side L j ((cbond L hL hL1 j μ hj).1.1 + ev L j (cbond L hL hL1 j μ hj).1.2)) := by
      show ¬ (side L j 0 ↔ side L j (0 + ev L j μ))
      rw [zero_add]
      exact fun h => hc (h.1 h0)
    simp only [hne, ↓reduceIte]
    rfl
  · -- the two cases of the reference value
    intro i hi b
    by_cases h1 : OneBlk L j μ i b (ct i hi b)
    · left
      simp only [V0, hi, h1, ↓reduceDIte, ↓reduceIte]
      exact (sval_one hL hL1 e W hi b _ h1).symm
    · right
      have h2 := (hct i hi b).resolve_left h1
      refine ⟨by simp only [V0, hi, h1, ↓reduceDIte, ↓reduceIte], sval_between hL hL1 e W hi b _ h2⟩
  · -- `lem:axial-smallness`
    intro i hi b
    have := hax i hi b (ct i hi b) (hct i hi b)
    simpa only [V0, hi, ↓reduceDIte] using this

end BoxGeometry

end CoreLean

end
