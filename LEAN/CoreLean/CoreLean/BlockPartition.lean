/-
`def:sequence` and `lem:block-partition` of BALABAN_CORE.tex: sequences of domains and the partition
of unity on the blocks.

Model (with `BlockLattice.lean`). The fine lattice is `(ℤ/N)⁴`, `N = 2L^{m_𝕋 + k}`, in the units
`η = 1`. The domains enter through their fine points: `Ω_j` is a set of fine points with `Ω_0` everything,
`Ω_{j+1} ⊆ Ω_j`, `Ω_{k+1} = ∅`, and `Ω_j` a union of cells of scale `j` (the core's `Ω_j` is a union of
cubes of the grid of side `Ma_j`, hence of cells of side `a_j`, whose boundaries contain no fine point).
The separation `eq:separation` is imposed on the fine points (the core's condition on the sets of the
torus implies it), with `RM` a real number. The scale `sc x` of a fine point is the largest `j` with
`x ∈ Ω_j`; the determining set `𝐁` is the set of the points `y ∈ T^{(sc y)}` (the layers
`Γ_j = Ω_j^{(j)} \ Ω_{j+1}` are disjoint, so a point of `𝐁` has one scale).

The proof is the core's. Where the core compares the layers of two points at the distance of less
than `a_i` through `Ω_{j+2}` and `Ω_{j+1}`, the separation is applied at the index next to the coarser
point (`far`), which gives the contradiction for every difference of scales of at least two.
-/
import CoreLean.BlockLattice

open Finset
open scoped Classical

noncomputable section

namespace CoreLean

namespace Blocks

variable {N : ℕ} [NeZero N]

/-- A fine point. -/
abbrev Pt (N : ℕ) := Fin 4 → ZMod N

/-- The point of `T^{(j)}` whose cell contains `x`. -/
def cen (L j : ℕ) (x : Pt N) : Pt N := fun ν => cen1 L j (x ν)

/-- `y ∈ T^{(j)}`. -/
def InLat (L j : ℕ) (y : Pt N) : Prop := ∀ ν, IsMul (L ^ j) (y ν)

/-- `|x - y|_∞`. -/
def dinf (x y : Pt N) : ℕ := univ.sup fun ν => cd (x ν - y ν)

/-- `|x - y|₁`. -/
def d1 (x y : Pt N) : ℕ := ∑ ν, cd (x ν - y ν)

lemma cd_le_dinf (x y : Pt N) (ν : Fin 4) : cd (x ν - y ν) ≤ dinf x y :=
  le_sup (f := fun ν => cd (x ν - y ν)) (mem_univ ν)

lemma cd_le_d1 (x y : Pt N) (ν : Fin 4) : cd (x ν - y ν) ≤ d1 x y :=
  single_le_sum (f := fun ν => cd (x ν - y ν)) (fun _ _ => Nat.zero_le _) (mem_univ ν)

lemma dinf_le_d1 (x y : Pt N) : dinf x y ≤ d1 x y :=
  Finset.sup_le fun ν _ => cd_le_d1 x y ν

lemma dinf_lt_iff {x y : Pt N} {c : ℕ} (hc : 0 < c) : dinf x y < c ↔ ∀ ν, cd (x ν - y ν) < c := by
  unfold dinf
  rw [Finset.sup_lt_iff hc]
  simp

lemma dinf_comm (x y : Pt N) : dinf x y = dinf y x := by
  unfold dinf; congr 1; funext ν; exact cd_sub_comm _ _

lemma dinf_triangle (x y z : Pt N) : dinf x z ≤ dinf x y + dinf y z :=
  Finset.sup_le fun ν _ => (cd_sub_le _ (y ν) _).trans
    (add_le_add (cd_le_dinf x y ν) (cd_le_dinf y z ν))

/-- A sequence of domains on the fine lattice (`def:sequence`). -/
structure DomSeq (N : ℕ) where
  L : ℕ
  L_odd : Odd L
  three_le_L : 3 ≤ L
  k : ℕ
  mT : ℕ
  one_le_mT : 1 ≤ mT
  N_eq : N = 2 * L ^ (mT + k)
  Ω : ℕ → Set (Pt N)
  Ω_zero : Ω 0 = Set.univ
  Ω_succ : ∀ j, Ω (j + 1) ⊆ Ω j
  Ω_top : Ω (k + 1) = ∅
  cells : ∀ j ≤ k, ∀ x, x ∈ Ω j ↔ cen L j x ∈ Ω j
  RM : ℝ
  sep : ∀ j, 1 ≤ j → j < k → ∀ x ∉ Ω j, ∀ x' ∈ Ω (j + 1), RM * (L : ℝ) ^ j < dinf x x'

namespace DomSeq

variable (S : DomSeq N)

lemma dvd_N {j : ℕ} (hj : j ≤ S.k) : S.L ^ j ∣ N :=
  (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) 2).trans (dvd_of_eq S.N_eq.symm)

lemma three_mul_le_N {j : ℕ} (hj : j ≤ S.k) : 3 * S.L ^ j ≤ N := by
  have h1 : S.L ^ j ≤ S.L ^ S.k := Nat.pow_le_pow_right (by have := S.three_le_L; omega) hj
  have h2 : S.L ^ (S.k + 1) ≤ S.L ^ (S.mT + S.k) :=
    Nat.pow_le_pow_right (by have := S.three_le_L; omega) (by have := S.one_le_mT; omega)
  rw [pow_succ] at h2
  have h3 : S.L ^ S.k * 3 ≤ S.L ^ S.k * S.L := Nat.mul_le_mul_left _ S.three_le_L
  calc 3 * S.L ^ j ≤ 2 * S.L ^ (S.mT + S.k) := by omega
    _ = N := S.N_eq.symm

lemma Ω_anti {i j : ℕ} (h : i ≤ j) : S.Ω j ⊆ S.Ω i := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (S.Ω_succ j).trans ih

lemma Ω_empty {j : ℕ} (h : S.k < j) : S.Ω j = ∅ :=
  Set.eq_empty_of_subset_empty ((S.Ω_anti h).trans S.Ω_top.le)

/-- The separation for every `j` (it is vacuous for `j = 0` and `j ≥ k`). -/
lemma sep' (j : ℕ) (x : Pt N) (hx : x ∉ S.Ω j) (x' : Pt N) (hx' : x' ∈ S.Ω (j + 1)) :
    S.RM * (S.L : ℝ) ^ j < dinf x x' := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact absurd (by rw [S.Ω_zero]; trivial) hx
  · by_cases hjk : j < S.k
    · exact S.sep j hj hjk x hx x' hx'
    · rw [S.Ω_empty (by omega)] at hx'; exact absurd hx' (Set.notMem_empty _)

/-! ### The scale of a point -/

/-- The scale `j(x)`: the largest `j` with `x ∈ Ω_j`. -/
def sc (x : Pt N) : ℕ := Nat.findGreatest (fun j => x ∈ S.Ω j) S.k

lemma sc_le (x : Pt N) : S.sc x ≤ S.k := Nat.findGreatest_le _

lemma mem_sc (x : Pt N) : x ∈ S.Ω (S.sc x) := by
  classical
  unfold sc
  exact Nat.findGreatest_spec (P := fun j => x ∈ S.Ω j) (Nat.zero_le _) (by rw [S.Ω_zero]; trivial)

lemma mem_iff (x : Pt N) (j : ℕ) : x ∈ S.Ω j ↔ j ≤ S.sc x := by
  classical
  constructor
  · intro h
    by_cases hj : j ≤ S.k
    · exact Nat.le_findGreatest hj h
    · rw [S.Ω_empty (by omega)] at h; exact absurd h (Set.notMem_empty _)
  · intro h; exact S.Ω_anti h (S.mem_sc x)

lemma not_mem_sc_succ (x : Pt N) : x ∉ S.Ω (S.sc x + 1) := fun h => by
  have := (S.mem_iff x _).mp h; omega

/-- `Ω_{j+1}` is a union of cells of scale `j`. -/
lemma cells_succ {j : ℕ} (hj : j + 1 ≤ S.k) (x : Pt N) :
    x ∈ S.Ω (j + 1) ↔ cen S.L j x ∈ S.Ω (j + 1) := by
  rw [S.cells (j + 1) hj x, S.cells (j + 1) hj (cen S.L j x)]
  have : cen S.L (j + 1) (cen S.L j x) = cen S.L (j + 1) x := by
    funext ν; exact cen1_cen1 S.L_odd (S.dvd_N hj) (x ν)
  rw [this]

/-- The point of `T^{(j(x))}` whose block contains `x` has the scale `j(x)`. -/
lemma sc_cen (x : Pt N) : S.sc (cen S.L (S.sc x) x) = S.sc x := by
  have h1 : cen S.L (S.sc x) x ∈ S.Ω (S.sc x) := (S.cells _ (S.sc_le x) x).mp (S.mem_sc x)
  have h2 : cen S.L (S.sc x) x ∉ S.Ω (S.sc x + 1) := by
    intro h
    by_cases hk : S.sc x + 1 ≤ S.k
    · exact S.not_mem_sc_succ x ((S.cells_succ hk x).mpr h)
    · rw [S.Ω_empty (by omega)] at h; exact absurd h (Set.notMem_empty _)
  have := (S.mem_iff _ _).mp h1
  have : ¬ S.sc x + 1 ≤ S.sc (cen S.L (S.sc x) x) := fun h => h2 ((S.mem_iff _ _).mpr h)
  omega

/-- The cost of a difference of scales of at least two. -/
lemma far {x x' : Pt N} (h : S.sc x + 2 ≤ S.sc x') :
    S.RM * (S.L : ℝ) ^ (S.sc x' - 1) < dinf x x' := by
  refine S.sep' (S.sc x' - 1) x (fun hx => ?_) x' ?_
  · have := (S.mem_iff x _).mp hx; omega
  · rw [show S.sc x' - 1 + 1 = S.sc x' by omega]; exact S.mem_sc x'

/-! ### The determining set and the functions `τ_y` -/

/-- The determining set `𝐁`. -/
def B : Finset (Pt N) := univ.filter fun y => InLat S.L (S.sc y) y

/-- `τ_y(x) = Π_μ max{0, 1 - |x_μ - y_μ|/a_{j(y)}}`. -/
def tau (y x : Pt N) : ℝ := ∏ ν, max 0 (1 - (cd (x ν - y ν) : ℝ) / (S.L : ℝ) ^ S.sc y)

/-- `𝖳 = Σ_y τ_y`. -/
def T (x : Pt N) : ℝ := ∑ y ∈ S.B, S.tau y x

/-- `ζ_y = τ_y/𝖳`. -/
def zeta (y x : Pt N) : ℝ := S.tau y x / S.T x

lemma L_pos : (0 : ℝ) < S.L := by have := S.three_le_L; positivity

lemma tau_nonneg (y x : Pt N) : 0 ≤ S.tau y x :=
  prod_nonneg fun _ _ => le_max_left _ _

lemma factor_le_one (y x : Pt N) (ν : Fin 4) :
    max 0 (1 - (cd (x ν - y ν) : ℝ) / (S.L : ℝ) ^ S.sc y) ≤ 1 :=
  max_le zero_le_one (by
    have : 0 ≤ (cd (x ν - y ν) : ℝ) / (S.L : ℝ) ^ S.sc y := by
      have := S.L_pos; positivity
    linarith)

lemma tau_le_one (y x : Pt N) : S.tau y x ≤ 1 :=
  prod_le_one₀ (fun _ _ => le_max_left _ _) fun ν _ => S.factor_le_one y x ν

lemma tau_eq_zero {y x : Pt N} (h : S.L ^ S.sc y ≤ dinf x y) : S.tau y x = 0 := by
  have hpos : 0 < S.L ^ S.sc y := pow_pos (by have := S.three_le_L; omega) _
  obtain ⟨ν, -, hν⟩ := Finset.exists_mem_eq_sup univ univ_nonempty (fun ν => cd (x ν - y ν))
  refine prod_eq_zero (mem_univ ν) (max_eq_left ?_)
  have : (S.L : ℝ) ^ S.sc y ≤ cd (x ν - y ν) := by
    have h' : S.L ^ S.sc y ≤ cd (x ν - y ν) := by unfold dinf at h; rw [hν] at h; exact h
    exact_mod_cast h'
  rw [sub_nonpos, le_div_iff₀ (pow_pos S.L_pos _), one_mul]
  exact this

/-- `𝖳 ≥ 2⁻⁴`: the block of `x` gives `τ ≥ 2⁻⁴`. -/
lemma T_ge (x : Pt N) : (1 : ℝ) / 16 ≤ S.T x := by
  classical
  set y := cen S.L (S.sc x) x
  have hy : y ∈ S.B := by
    simp only [B, mem_filter, mem_univ, true_and]
    rw [S.sc_cen x]
    exact fun ν => cen1_isMul _ _
  have hfac : ∀ ν, (1 : ℝ) / 2 ≤ max 0 (1 - (cd (x ν - y ν) : ℝ) / (S.L : ℝ) ^ S.sc y) := by
    intro ν
    refine le_max_of_le_right ?_
    rw [S.sc_cen x]
    have hd := cd_sub_cen1_le S.L_odd (S.sc x) (x ν)
    have hodd := two_half_add_one S.L_odd (S.sc x)
    have hp : (0 : ℝ) < (S.L : ℝ) ^ S.sc x := pow_pos S.L_pos _
    have : (cd (x ν - y ν) : ℝ) / (S.L : ℝ) ^ S.sc x ≤ 1 / 2 := by
      rw [div_le_iff₀ hp]
      have h1 : (cd (x ν - y ν) : ℝ) ≤ half S.L (S.sc x) := by exact_mod_cast hd
      have h2 : (2 * half S.L (S.sc x) + 1 : ℝ) = (S.L : ℝ) ^ S.sc x := by exact_mod_cast hodd
      linarith
    linarith
  have htau : (1 : ℝ) / 16 ≤ S.tau y x := by
    calc (1 : ℝ) / 16 = ∏ _ν : Fin 4, (1 : ℝ) / 2 := by norm_num
      _ ≤ S.tau y x := prod_le_prod₀ (fun _ _ => by norm_num) fun ν _ => hfac ν
  exact htau.trans (single_le_sum (fun y _ => S.tau_nonneg y x) hy)

lemma T_pos (x : Pt N) : 0 < S.T x := lt_of_lt_of_le (by norm_num) (S.T_ge x)

/-! ### The number of the cubes `Δ̃(y)` containing a point -/

/-- A point `y ∈ 𝐁` with `|x - y|_∞ < a_{j(y)}` has a scale within one of that of `x`. -/
lemma near_scale (hRM : (S.L : ℝ) ≤ S.RM) {x y : Pt N} (h : dinf x y < S.L ^ S.sc y) :
    S.sc y ≤ S.sc x + 1 ∧ S.sc x ≤ S.sc y + 1 := by
  have hL := S.L_pos
  constructor
  · by_contra hc
    have hf := S.far (x := x) (x' := y) (by omega)
    have e : (S.L : ℝ) ^ S.sc y = S.L * (S.L : ℝ) ^ (S.sc y - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : (dinf x y : ℝ) < (S.L : ℝ) ^ S.sc y := by exact_mod_cast h
    have hp : (0 : ℝ) < (S.L : ℝ) ^ (S.sc y - 1) := pow_pos hL _
    nlinarith
  · by_contra hc
    have hf := S.far (x := y) (x' := x) (by omega)
    rw [dinf_comm] at hf
    have : (dinf x y : ℝ) < (S.L : ℝ) ^ S.sc y := by exact_mod_cast h
    have hle : (S.L : ℝ) ^ S.sc y ≤ (S.L : ℝ) ^ (S.sc x - 1) :=
      pow_le_pow_right₀ (by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L)) (by omega)
    have hp : (0 : ℝ) < (S.L : ℝ) ^ (S.sc x - 1) := pow_pos hL _
    have h3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
    nlinarith

/-- `x` lies in at most `48` of the cubes `Δ̃(y)`, `y ∈ 𝐁`. -/
theorem card_near (hRM : (S.L : ℝ) ≤ S.RM) (x : Pt N) :
    (S.B.filter fun y => dinf x y < S.L ^ S.sc y).card ≤ 48 := by
  classical
  set P : ℕ → Finset (Pt N) := fun i => S.B.filter fun y => S.sc y = i ∧ dinf x y < S.L ^ i
  have hsub : (S.B.filter fun y => dinf x y < S.L ^ S.sc y) ⊆
      ({S.sc x - 1, S.sc x, S.sc x + 1} : Finset ℕ).biUnion P := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨h1, h2⟩ := S.near_scale hRM hy.2
    rw [mem_biUnion]
    refine ⟨S.sc y, ?_, ?_⟩
    · simp only [mem_insert, mem_singleton]; omega
    · exact mem_filter.mpr ⟨hy.1, rfl, hy.2⟩
  have hP : ∀ i, (P i).card ≤ 16 := by
    intro i
    by_cases hi : i ≤ S.k
    · have hpos : 0 < S.L ^ i := pow_pos (by have := S.three_le_L; omega) _
      choose T hT hmem using fun ν => card_near_le S.L_odd (S.dvd_N hi) (S.three_mul_le_N hi) (x ν)
      have : P i ⊆ Fintype.piFinset T := by
        intro y hy
        simp only [P, B, mem_filter, mem_univ, true_and] at hy
        obtain ⟨hlat, hsc, hd⟩ := hy
        rw [Fintype.mem_piFinset]
        intro ν
        rw [hsc] at hlat
        exact hmem ν (y ν) (hlat ν) (((dinf_lt_iff hpos).mp hd) ν)
      refine (card_le_card this).trans ?_
      rw [Fintype.card_piFinset]
      calc ∏ ν, (T ν).card ≤ ∏ _ν : Fin 4, 2 := prod_le_prod' fun ν _ => hT ν
        _ = 16 := by simp
    · have : P i = ∅ := by
        refine filter_eq_empty_iff.mpr fun y _ h => ?_
        have := S.sc_le y; omega
      rw [this]; simp
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ i ∈ ({S.sc x - 1, S.sc x, S.sc x + 1} : Finset ℕ), (P i).card
      ≤ ∑ _i ∈ ({S.sc x - 1, S.sc x, S.sc x + 1} : Finset ℕ), 16 := sum_le_sum fun i _ => hP i
    _ ≤ 3 * 16 := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_le_three)
    _ = 48 := by norm_num

lemma T_le (hRM : (S.L : ℝ) ≤ S.RM) (x : Pt N) : S.T x ≤ 48 := by
  classical
  unfold T
  rw [← sum_filter_add_sum_filter_not S.B (fun y => dinf x y < S.L ^ S.sc y)]
  have h0 : ∑ y ∈ S.B.filter (fun y => ¬ dinf x y < S.L ^ S.sc y), S.tau y x = 0 :=
    sum_eq_zero fun y hy => S.tau_eq_zero (not_lt.mp (mem_filter.mp hy).2)
  rw [h0, add_zero]
  calc ∑ y ∈ S.B.filter (fun y => dinf x y < S.L ^ S.sc y), S.tau y x
      ≤ ∑ _y ∈ S.B.filter (fun y => dinf x y < S.L ^ S.sc y), (1 : ℝ) :=
        sum_le_sum fun y _ => S.tau_le_one y x
    _ ≤ 48 := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast S.card_near hRM x

/-! ### The partition of unity -/

lemma zeta_nonneg (y x : Pt N) : 0 ≤ S.zeta y x := div_nonneg (S.tau_nonneg y x) (S.T_pos x).le

lemma zeta_le_one {y : Pt N} (hy : y ∈ S.B) (x : Pt N) : S.zeta y x ≤ 1 := by
  rw [zeta, div_le_one (S.T_pos x)]
  exact single_le_sum (fun y _ => S.tau_nonneg y x) hy

lemma zeta_eq_zero {y x : Pt N} (h : S.L ^ S.sc y ≤ dinf x y) : S.zeta y x = 0 := by
  rw [zeta, S.tau_eq_zero h, zero_div]

lemma sum_zeta (x : Pt N) : ∑ y ∈ S.B, S.zeta y x = 1 := by
  unfold zeta
  rw [← sum_div, ← T, div_self (S.T_pos x).ne']

/-! ### The Lipschitz bound -/

/-- `|Π f - Π g| ≤ Σ |f - g|` for factors in `[0, 1]`. -/
lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (hf1 : ∀ i, f i ≤ 1) (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    have hpf : 0 ≤ ∏ i ∈ s, f i := prod_nonneg fun i _ => hf0 i
    have hpg1 : ∏ i ∈ s, g i ≤ 1 := prod_le_one₀ (fun i _ => hg0 i) fun i _ => hg1 i
    have hpg0 : 0 ≤ ∏ i ∈ s, g i := prod_nonneg fun i _ => hg0 i
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    calc |f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i|
        ≤ |f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)| + |(f a - g a) * ∏ i ∈ s, g i| := abs_add_le _ _
      _ = |f a| * |∏ i ∈ s, f i - ∏ i ∈ s, g i| + |f a - g a| * |∏ i ∈ s, g i| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * (∑ i ∈ s, |f i - g i|) + |f a - g a| * 1 := by
          gcongr
          · rw [abs_of_nonneg (hf0 a)]; exact hf1 a
          · rw [abs_of_nonneg hpg0]; exact hpg1
      _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

/-- `|τ_y(x) - τ_y(x')| ≤ |x - x'|₁/a_{j(y)}`. -/
lemma abs_tau_sub_le (y x x' : Pt N) :
    |S.tau y x - S.tau y x'| ≤ (d1 x x' : ℝ) / (S.L : ℝ) ^ S.sc y := by
  have hp : (0 : ℝ) < (S.L : ℝ) ^ S.sc y := pow_pos S.L_pos _
  set a : ℝ := (S.L : ℝ) ^ S.sc y
  set f : Fin 4 → ℝ := fun ν => max 0 (1 - (cd (x ν - y ν) : ℝ) / a)
  set g : Fin 4 → ℝ := fun ν => max 0 (1 - (cd (x' ν - y ν) : ℝ) / a)
  have htau : S.tau y x = ∏ ν, f ν := rfl
  have htau' : S.tau y x' = ∏ ν, g ν := rfl
  rw [htau, htau']
  refine (abs_prod_sub_prod_le univ f g (fun _ => le_max_left _ _)
    (fun ν => S.factor_le_one y x ν) (fun _ => le_max_left _ _)
    (fun ν => S.factor_le_one y x' ν)).trans ?_
  have hd1 : (d1 x x' : ℝ) = ∑ ν, (cd (x ν - x' ν) : ℝ) := by unfold d1; push_cast; rfl
  rw [hd1, sum_div]
  refine sum_le_sum fun ν _ => ?_
  -- each factor is `1/a`-Lipschitz in the circle distance
  have hcd : |(cd (x ν - y ν) : ℝ) - cd (x' ν - y ν)| ≤ cd (x ν - x' ν) := by
    have h1 := cd_sub_le (x ν) (x' ν) (y ν)
    have h2 := cd_sub_le (x' ν) (x ν) (y ν)
    rw [cd_sub_comm (x' ν) (x ν)] at h2
    rw [abs_le]
    constructor
    · have : (cd (x' ν - y ν) : ℝ) ≤ cd (x ν - x' ν) + cd (x ν - y ν) := by exact_mod_cast h2
      linarith
    · have : (cd (x ν - y ν) : ℝ) ≤ cd (x ν - x' ν) + cd (x' ν - y ν) := by exact_mod_cast h1
      linarith
  have hmax : |f ν - g ν| ≤ |(1 - (cd (x ν - y ν) : ℝ) / a) - (1 - (cd (x' ν - y ν) : ℝ) / a)| := by
    have := abs_max_sub_max_le_abs (1 - (cd (x ν - y ν) : ℝ) / a) (1 - (cd (x' ν - y ν) : ℝ) / a) 0
    simp only [f, g]
    rwa [max_comm (1 - (cd (x ν - y ν) : ℝ) / a) 0, max_comm (1 - (cd (x' ν - y ν) : ℝ) / a) 0]
      at this
  have he : (1 - (cd (x ν - y ν) : ℝ) / a) - (1 - (cd (x' ν - y ν) : ℝ) / a) =
      -(((cd (x ν - y ν) : ℝ) - cd (x' ν - y ν)) / a) := by ring
  rw [he, abs_neg, abs_div, abs_of_pos hp] at hmax
  exact hmax.trans (div_le_div_of_nonneg_right hcd hp.le)

/-- Two points within `2a_{j(y)}` of `y` have their scales within one of `j(y)`, for `RM ≥ L²`. -/
lemma near_scale2 (hRM : (S.L : ℝ) ^ 2 ≤ S.RM) {x y : Pt N}
    (h : dinf x y < 2 * S.L ^ S.sc y) : S.sc x ≤ S.sc y + 1 ∧ S.sc y ≤ S.sc x + 1 := by
  have hL := S.L_pos
  have h3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hd : (dinf x y : ℝ) < 2 * (S.L : ℝ) ^ S.sc y := by exact_mod_cast h
  constructor
  · by_contra hc
    have hf := S.far (x := y) (x' := x) (by omega)
    rw [dinf_comm] at hf
    have hle : (S.L : ℝ) ^ S.sc y * S.L ≤ (S.L : ℝ) ^ (S.sc x - 1) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    have hp : (0 : ℝ) < (S.L : ℝ) ^ S.sc y := pow_pos hL _
    -- `RM L^{j(x)-1} ≥ L² · L^{j(y)} L ≥ 27 L^{j(y)} > 2L^{j(y)} > |x - y|_∞`
    have c1 : (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (S.sc x - 1) ≤ S.RM * (S.L : ℝ) ^ (S.sc x - 1) :=
      mul_le_mul_of_nonneg_right hRM (pow_pos hL _).le
    have c2 : (S.L : ℝ) ^ 2 * ((S.L : ℝ) ^ S.sc y * S.L) ≤
        (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (S.sc x - 1) :=
      mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    have c3 : 2 * (S.L : ℝ) ^ S.sc y < (S.L : ℝ) ^ 2 * ((S.L : ℝ) ^ S.sc y * S.L) := by
      have : (2 : ℝ) < S.L ^ 2 * S.L := by nlinarith
      nlinarith
    linarith
  · by_contra hc
    have hf := S.far (x := x) (x' := y) (by omega)
    have e : (S.L : ℝ) ^ S.sc y = S.L * (S.L : ℝ) ^ (S.sc y - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hp : (0 : ℝ) < (S.L : ℝ) ^ (S.sc y - 1) := pow_pos hL _
    nlinarith

/-- `|𝖳(x) - 𝖳(x')| ≤ 96L²|x - x'|₁/a_{j(y)}` for `x`, `x'` within `2a_{j(y)}` of `y`. -/
lemma abs_T_sub_le (hRM : (S.L : ℝ) ^ 2 ≤ S.RM) {y x x' : Pt N}
    (hx : dinf x y < 2 * S.L ^ S.sc y) (hx' : dinf x' y < 2 * S.L ^ S.sc y) :
    |S.T x - S.T x'| ≤ 96 * (S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y := by
  classical
  have hL := S.L_pos
  have hRM1 : (S.L : ℝ) ≤ S.RM := by
    have h3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
    nlinarith
  set Nx := S.B.filter fun y' => dinf x y' < S.L ^ S.sc y'
  set Nx' := S.B.filter fun y' => dinf x' y' < S.L ^ S.sc y'
  -- only the points of `Nx ∪ Nx'` contribute
  have hsplit : S.T x - S.T x' = ∑ y' ∈ Nx ∪ Nx', (S.tau y' x - S.tau y' x') := by
    unfold T
    rw [← sum_sub_distrib]
    refine (sum_subset (union_subset (filter_subset _ _) (filter_subset _ _)) ?_).symm
    intro y' hy' hn
    simp only [mem_union, mem_filter, not_or, not_and, not_lt, Nx, Nx'] at hn
    rw [S.tau_eq_zero (hn.1 hy'), S.tau_eq_zero (hn.2 hy'), sub_zero]
  -- the scales of the contributing points are at least `j(y) - 2`
  have hscale : ∀ y' ∈ Nx ∪ Nx', S.sc y + 2 ≤ S.sc y' + 4 ∧ S.sc y ≤ S.sc y' + 2 := by
    intro y' hy'
    rcases mem_union.mp hy' with h | h
    · have := S.near_scale hRM1 (mem_filter.mp h).2
      have := S.near_scale2 hRM hx
      omega
    · have := S.near_scale hRM1 (mem_filter.mp h).2
      have := S.near_scale2 hRM hx'
      omega
  have hterm : ∀ y' ∈ Nx ∪ Nx', |S.tau y' x - S.tau y' x'| ≤
      (S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y := by
    intro y' hy'
    refine (S.abs_tau_sub_le y' x x').trans ?_
    have hsc := (hscale y' hy').2
    have hp : (0 : ℝ) < (S.L : ℝ) ^ S.sc y' := pow_pos hL _
    have hp' : (0 : ℝ) < (S.L : ℝ) ^ S.sc y := pow_pos hL _
    rw [div_le_div_iff₀ hp hp']
    have : (S.L : ℝ) ^ S.sc y ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ S.sc y' := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L))
        (by omega)
    have hd : (0 : ℝ) ≤ d1 x x' := Nat.cast_nonneg _
    nlinarith
  have hcard : ((Nx ∪ Nx').card : ℝ) ≤ 96 := by
    have := card_union_le Nx Nx'
    have h1 : Nx.card ≤ 48 := S.card_near hRM1 x
    have h2 : Nx'.card ≤ 48 := S.card_near hRM1 x'
    exact_mod_cast (this.trans (by omega))
  rw [hsplit]
  calc |∑ y' ∈ Nx ∪ Nx', (S.tau y' x - S.tau y' x')|
      ≤ ∑ y' ∈ Nx ∪ Nx', |S.tau y' x - S.tau y' x'| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y' ∈ Nx ∪ Nx', (S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y := sum_le_sum hterm
    _ = ((Nx ∪ Nx').card : ℝ) * ((S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 96 * ((S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y) := by
        gcongr
    _ = 96 * (S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y := by ring

/-- `lem:block-partition`, `eq:block-partition`: for `RM ≥ L²`, `y ∈ 𝐁`, and sites with
`|x - x'|₁ ≤ a_{j(y)}`, `|ζ_y(x) - ζ_y(x')| ≤ C_ζ|x - x'|₁/a_{j(y)}` with `C_ζ = 2¹⁵L²`. -/
theorem abs_zeta_sub_le (hRM : (S.L : ℝ) ^ 2 ≤ S.RM) {y : Pt N} (x x' : Pt N)
    (hxx' : d1 x x' ≤ S.L ^ S.sc y) :
    |S.zeta y x - S.zeta y x'| ≤ 2 ^ 15 * (S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y := by
  have hL := S.L_pos
  have hp : (0 : ℝ) < (S.L : ℝ) ^ S.sc y := pow_pos hL _
  have hRHS : 0 ≤ 2 ^ 15 * (S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y := by positivity
  by_cases hfar : S.L ^ S.sc y ≤ dinf x y ∧ S.L ^ S.sc y ≤ dinf x' y
  · rw [S.zeta_eq_zero hfar.1, S.zeta_eq_zero hfar.2, sub_zero, abs_zero]; exact hRHS
  -- both sites lie within `2a_{j(y)}` of `y`
  have hboth : dinf x y < 2 * S.L ^ S.sc y ∧ dinf x' y < 2 * S.L ^ S.sc y := by
    have h1 := dinf_triangle x x' y
    have h2 := dinf_triangle x' x y
    have h3 := dinf_le_d1 x x'
    have h4 := dinf_le_d1 x' x
    have h5 : d1 x' x = d1 x x' := by unfold d1; congr 1; funext ν; exact cd_sub_comm _ _
    rw [not_and_or] at hfar
    rcases hfar with h | h <;> push_neg at h <;> constructor <;> omega
  have hT := S.T_ge x
  have hT' := S.T_ge x'
  have hTp := S.T_pos x
  have hTp' := S.T_pos x'
  have hτ := S.abs_tau_sub_le y x x'
  have hτ' := S.tau_le_one y x'
  have hτ0' := S.tau_nonneg y x'
  have hTT := S.abs_T_sub_le hRM hboth.1 hboth.2
  set a := (S.L : ℝ) ^ S.sc y
  set D := (d1 x x' : ℝ)
  have hτ : |S.tau y x - S.tau y x'| ≤ D / a := S.abs_tau_sub_le y x x'
  have hTT : |S.T x - S.T x'| ≤ 96 * (S.L : ℝ) ^ 2 * D / a := S.abs_T_sub_le hRM hboth.1 hboth.2
  -- `τ/𝖳 - τ'/𝖳' = (τ - τ')/𝖳 + τ'(𝖳' - 𝖳)/(𝖳𝖳')`
  have e : S.zeta y x - S.zeta y x' = (S.tau y x - S.tau y x') / S.T x +
      S.tau y x' * (S.T x' - S.T x) / (S.T x * S.T x') := by
    unfold zeta; field_simp; ring
  rw [e]
  have h1 : |(S.tau y x - S.tau y x') / S.T x| ≤ 16 * (D / a) := by
    rw [abs_div, abs_of_pos hTp, div_le_iff₀ hTp]
    have : D / a * 1 ≤ 16 * (D / a) * S.T x := by
      have : 0 ≤ D / a := div_nonneg (Nat.cast_nonneg _) hp.le
      nlinarith
    linarith
  have h2 : |S.tau y x' * (S.T x' - S.T x) / (S.T x * S.T x')| ≤
      256 * (96 * (S.L : ℝ) ^ 2 * D / a) := by
    rw [abs_div, abs_mul, abs_of_nonneg hτ0', abs_of_pos (mul_pos hTp hTp'),
      div_le_iff₀ (mul_pos hTp hTp'), abs_sub_comm]
    have hTT' : 0 ≤ 96 * (S.L : ℝ) ^ 2 * D / a := by positivity
    have hprod : (1 : ℝ) / 256 ≤ S.T x * S.T x' := by nlinarith
    calc S.tau y x' * |S.T x - S.T x'| ≤ 1 * (96 * (S.L : ℝ) ^ 2 * D / a) :=
          mul_le_mul hτ' hTT (abs_nonneg _) zero_le_one
      _ ≤ 256 * (96 * (S.L : ℝ) ^ 2 * D / a) * (S.T x * S.T x') := by nlinarith
  calc |(S.tau y x - S.tau y x') / S.T x + S.tau y x' * (S.T x' - S.T x) / (S.T x * S.T x')|
      ≤ |(S.tau y x - S.tau y x') / S.T x| +
          |S.tau y x' * (S.T x' - S.T x) / (S.T x * S.T x')| := abs_add_le _ _
    _ ≤ 16 * (D / a) + 256 * (96 * (S.L : ℝ) ^ 2 * D / a) := add_le_add h1 h2
    _ = (16 + 24576 * (S.L : ℝ) ^ 2) * D / a := by ring
    _ ≤ 2 ^ 15 * (S.L : ℝ) ^ 2 * D / a := by
        refine div_le_div_of_nonneg_right ?_ hp.le
        have h3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
        have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
        have hc : 16 + 24576 * (S.L : ℝ) ^ 2 ≤ 2 ^ 15 * (S.L : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right hc this

/-- `lem:block-partition`: `ζ_y ∈ [0, 1]`, `ζ_y = 0` outside `Δ̃(y)`, `Σ_y ζ_y = 1`, every site lies in
at most `48` of the cubes `Δ̃(y)`, and `eq:block-partition`, for `RM ≥ L²`. -/
theorem block_partition (hRM : (S.L : ℝ) ^ 2 ≤ S.RM) :
    (∀ y ∈ S.B, ∀ x, 0 ≤ S.zeta y x ∧ S.zeta y x ≤ 1) ∧
    (∀ y x, S.L ^ S.sc y ≤ dinf x y → S.zeta y x = 0) ∧
    (∀ x, ∑ y ∈ S.B, S.zeta y x = 1) ∧
    (∀ x, (S.B.filter fun y => dinf x y < S.L ^ S.sc y).card ≤ 48) ∧
    (∀ y ∈ S.B, ∀ x x', d1 x x' ≤ S.L ^ S.sc y →
      |S.zeta y x - S.zeta y x'| ≤ 2 ^ 15 * (S.L : ℝ) ^ 2 * d1 x x' / (S.L : ℝ) ^ S.sc y) := by
  have hRM1 : (S.L : ℝ) ≤ S.RM := by
    have h3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
    nlinarith
  exact ⟨fun y hy x => ⟨S.zeta_nonneg y x, S.zeta_le_one hy x⟩, fun y x h => S.zeta_eq_zero h,
    S.sum_zeta, S.card_near hRM1, fun y _ x x' h => S.abs_zeta_sub_le hRM x x' h⟩

end DomSeq

end Blocks

end CoreLean
