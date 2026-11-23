/-
`def:lattices` and `def:grids` of BALABAN_CORE.tex (`ea68ea6e3640`) on the torus `𝕋 = (ℝ/ℓℤ)⁴`.

The torus is `Tor ℓ = (ℝ/ℓℤ)⁴` with the sup norm of its coordinates, which is the core's `|·|_∞`
(the smallest `ℓ^∞`-norm of a representative). The lattice of spacing `a` is the set `Lat ℓ a` of the
points whose coordinates are multiples of `a`, and the cell of `y` is the closed ball
`{z | |z - y|_∞ ≤ a/2}` (`cell`). The generic statements are proved for a spacing `a` with `ℓ = M a`; the
core's lattices `T^{(j)}` (spacing `a_j = Lʲη`, `η = L^{-k}`, `ℓ = 2L^{m_𝕋}`), its blocks `Bⁿ(y)`, and its grids
of side `s = Lⁱ` are instances. Proved: the statements of the paragraph after `def:lattices` and after
`def:grids`: `T^{(j)} ⊂ T^{(j-1)}`, the cells cover the torus and meet at most in boundary points, each
cell is the union of the cells of the next finer scale at the points of its block, no point of a lattice
`T^{(i)}` lies on the boundary of a cell `Δ_j(y)` with `j ≥ i`, `eq:block` with `|Bⁿ(y)| = L^{4n}`, the
blocks of order `n` partition `T^{(j-n)}`, and the same for the cubes of the grids. The fine lattice
`(ℤ/N)⁴` with `N = 2L^{m_𝕋 + k}` of `BlockLattice.lean` is identified with `T^{(0)}` (`emb`).
-/
import CoreLean.Distance
import CoreLean.BlockPartition

open Set

noncomputable section

namespace CoreLean
namespace Lattices

variable {p : ℝ}

/-! ### One coordinate -/

/-- The points `r a`, `r ∈ ℤ`, of the circle `ℝ/pℤ`. -/
def LatC (p a : ℝ) : Set (AddCircle p) := {t | ∃ r : ℤ, t = (((r : ℝ) * a : ℝ) : AddCircle p)}

lemma norm_coe_le (x : ℝ) : ‖(x : AddCircle p)‖ ≤ |x| := by
  simpa using norm_coe_sub_le (p := p) x 0

lemma coe_int_mul_period (q : ℤ) : (((q : ℝ) * p : ℝ) : AddCircle p) = 0 :=
  (AddCircle.coe_eq_zero_iff p).2 ⟨q, by simp [zsmul_eq_mul]⟩

/-- Every point of the circle has a representative whose absolute value is its norm. -/
lemma exists_rep (t : AddCircle p) : ∃ v : ℝ, t = (v : AddCircle p) ∧ |v| = ‖t‖ := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  refine ⟨w - round (p⁻¹ * w) * p, ?_, (AddCircle.norm_eq p).symm⟩
  rw [AddCircle.coe_sub, coe_int_mul_period, sub_zero]

/-- The normal form of a lattice point: `r a = s a` with `|s| ≤ M/2`, and `‖r a‖ = |s| a`. -/
lemma latC_norm {a : ℝ} {M : ℕ} (ha : 0 < a) (hM : 0 < M) (hp : p = M * a) (r : ℤ) :
    ∃ s : ℤ, ((((r : ℝ) * a : ℝ)) : AddCircle p) = (((s : ℝ) * a : ℝ) : AddCircle p) ∧
      ‖((((r : ℝ) * a : ℝ)) : AddCircle p)‖ = |(s : ℝ)| * a ∧ 2 * |s| ≤ M := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = round (p⁻¹ * ((r : ℝ) * a)) := ⟨_, rfl⟩
  have e : (r : ℝ) * a - q * p = ((r - q * M : ℤ) : ℝ) * a := by rw [hp]; push_cast; ring
  have hn : ‖((((r : ℝ) * a : ℝ)) : AddCircle p)‖ = |((r - q * M : ℤ) : ℝ)| * a := by
    rw [AddCircle.norm_eq p, ← hq, e, abs_mul, abs_of_pos ha]
  refine ⟨r - q * M, ?_, hn, ?_⟩
  · rw [← e, AddCircle.coe_sub, coe_int_mul_period, sub_zero]
  · have hp0 : 0 < p := by rw [hp]; exact mul_pos (Nat.cast_pos.2 hM) ha
    have h1 := AddCircle.norm_le_half_period p (x := ((((r : ℝ) * a : ℝ)) : AddCircle p)) hp0.ne'
    rw [hn, abs_of_pos hp0, hp] at h1
    have h2 : 2 * |((r - q * M : ℤ) : ℝ)| ≤ M :=
      le_of_mul_le_mul_right (by linarith : 2 * |((r - q * M : ℤ) : ℝ)| * a ≤ (M : ℝ) * a) ha
    have h3 : ((2 * |r - q * M| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by push_cast at h2 ⊢; exact h2
    exact_mod_cast h3

lemma latC_sub {a : ℝ} {t t' : AddCircle p} (ht : t ∈ LatC p a) (ht' : t' ∈ LatC p a) :
    t - t' ∈ LatC p a := by
  obtain ⟨r, rfl⟩ := ht
  obtain ⟨r', rfl⟩ := ht'
  exact ⟨r - r', by rw [← AddCircle.coe_sub]; push_cast; ring_nf⟩

lemma latC_add {a : ℝ} {t t' : AddCircle p} (ht : t ∈ LatC p a) (ht' : t' ∈ LatC p a) :
    t + t' ∈ LatC p a := by
  obtain ⟨r, rfl⟩ := ht
  obtain ⟨r', rfl⟩ := ht'
  exact ⟨r + r', by rw [← AddCircle.coe_add]; push_cast; ring_nf⟩

lemma latC_mono {a a' : ℝ} {q : ℕ} (h : a = q * a') : LatC p a ⊆ LatC p a' := by
  rintro t ⟨r, rfl⟩
  exact ⟨r * q, by rw [h]; push_cast; ring_nf⟩

lemma latC_mul (a : ℝ) (r : ℤ) : ((((r : ℝ) * a : ℝ)) : AddCircle p) ∈ LatC p a := ⟨r, rfl⟩

/-- A lattice point of norm `< a` is `0`. -/
lemma latC_eq_zero {a : ℝ} {M : ℕ} (ha : 0 < a) (hM : 0 < M) (hp : p = M * a) {t : AddCircle p}
    (ht : t ∈ LatC p a) (hn : ‖t‖ < a) : t = 0 := by
  obtain ⟨r, rfl⟩ := ht
  obtain ⟨s, hs, hsn, -⟩ := latC_norm ha hM hp r
  rw [hsn] at hn
  have h1 : |(s : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : |s| < 1 := by
    have : ((|s| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; exact h1
    exact_mod_cast this
  have h3 : s = 0 := by rw [abs_lt] at h2; omega
  rw [hs, h3]; simp

/-- No lattice point has norm `q a/2` with `q` odd. -/
lemma latC_norm_ne {a : ℝ} {M : ℕ} (ha : 0 < a) (hM : 0 < M) (hp : p = M * a) {t : AddCircle p}
    (ht : t ∈ LatC p a) {q : ℕ} (hq : Odd q) : ‖t‖ ≠ q * a / 2 := by
  obtain ⟨r, rfl⟩ := ht
  obtain ⟨s, -, hsn, -⟩ := latC_norm ha hM hp r
  intro he
  rw [hsn] at he
  have h1 : 2 * |(s : ℝ)| = q := by
    have := congrArg (· * (2 / a)) he
    field_simp at this
    linarith
  have h2 : ((2 * |s| : ℤ) : ℝ) = ((q : ℤ) : ℝ) := by push_cast; exact h1
  have h3 : 2 * |s| = (q : ℤ) := by exact_mod_cast h2
  obtain ⟨c, rfl⟩ := hq
  push_cast at h3
  omega

/-- The lattice points with norm at most `(2H + 1)a/2` are the multiples `s a` with `|s| ≤ H`. -/
lemma latC_small_iff {a : ℝ} {M : ℕ} (ha : 0 < a) (hM : 0 < M) (hp : p = M * a) {t : AddCircle p}
    (H : ℕ) : (t ∈ LatC p a ∧ ‖t‖ ≤ (2 * H + 1 : ℕ) * a / 2) ↔
      ∃ s : ℤ, |s| ≤ H ∧ t = (((s : ℝ) * a : ℝ) : AddCircle p) := by
  constructor
  · rintro ⟨⟨r, rfl⟩, hn⟩
    obtain ⟨s, hs, hsn, -⟩ := latC_norm ha hM hp r
    rw [hsn] at hn
    refine ⟨s, ?_, hs⟩
    have h1 : 2 * |(s : ℝ)| ≤ 2 * H + 1 :=
      le_of_mul_le_mul_right (by push_cast at hn; linarith : 2 * |(s : ℝ)| * a ≤ (2 * H + 1 : ℝ) * a) ha
    have h2 : ((2 * |s| : ℤ) : ℝ) ≤ ((2 * H + 1 : ℤ) : ℝ) := by push_cast; exact h1
    have h3 : 2 * |s| ≤ 2 * (H : ℤ) + 1 := by exact_mod_cast h2
    omega
  · rintro ⟨s, hs, rfl⟩
    refine ⟨latC_mul a s, (norm_coe_le _).trans ?_⟩
    rw [abs_mul, abs_of_pos ha]
    have : |(s : ℝ)| ≤ H := by
      have : ((|s| : ℤ) : ℝ) ≤ ((H : ℤ) : ℝ) := by exact_mod_cast hs
      push_cast at this; exact this
    push_cast
    nlinarith

/-- Every point is within `a/2` of a lattice point. -/
lemma exists_near {a : ℝ} (ha : 0 < a) (t : AddCircle p) :
    ∃ r : ℤ, ‖t - (((r : ℝ) * a : ℝ) : AddCircle p)‖ ≤ a / 2 := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  refine ⟨round (w / a), (norm_coe_sub_le w _).trans ?_⟩
  have h := abs_sub_round (w / a)
  have e : w - (round (w / a) : ℝ) * a = a * (w / a - round (w / a)) := by field_simp
  rw [e, abs_mul, abs_of_pos ha]
  calc a * |w / a - round (w / a)| ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left h ha.le
    _ = a / 2 := by ring

/-- A point within `(2h + 1)a'/2` of `0` is within `a'/2` of a multiple `r a'` with `|r| ≤ h`. -/
lemma exists_fine {a' : ℝ} (ha' : 0 < a') {h : ℕ} {u : AddCircle p}
    (hu : ‖u‖ ≤ (2 * h + 1 : ℕ) * a' / 2) :
    ∃ r : ℤ, |r| ≤ h ∧ ‖u - (((r : ℝ) * a' : ℝ) : AddCircle p)‖ ≤ a' / 2 := by
  obtain ⟨v, rfl, hv⟩ := exists_rep u
  have hw' : |v / a'| ≤ (2 * h + 1) / 2 := by
    rw [abs_div, abs_of_pos ha', div_le_iff₀ ha', hv]; push_cast at hu; linarith
  have key : ∃ r : ℤ, |r| ≤ h ∧ |v / a' - r| ≤ 1 / 2 := by
    have hlo := (abs_le.1 hw').1
    have hhi := (abs_le.1 hw').2
    rcases le_or_gt 0 (v / a') with h0 | h0
    · have h1 := Int.le_ceil (v / a' - 1 / 2)
      have h2 := Int.ceil_lt_add_one (v / a' - 1 / 2)
      refine ⟨⌈v / a' - 1 / 2⌉, ?_, ?_⟩
      · have i1 : ((⌈v / a' - 1 / 2⌉ : ℤ) : ℝ) < ((h + 1 : ℤ) : ℝ) := by push_cast; linarith
        have i2 : ((-1 : ℤ) : ℝ) < ((⌈v / a' - 1 / 2⌉ : ℤ) : ℝ) := by push_cast; linarith
        have j1 : ⌈v / a' - 1 / 2⌉ < (h : ℤ) + 1 := by exact_mod_cast i1
        have j2 : (-1 : ℤ) < ⌈v / a' - 1 / 2⌉ := by exact_mod_cast i2
        rw [abs_le]; constructor <;> omega
      · rw [abs_le]; constructor <;> linarith
    · have h1 := Int.floor_le (v / a' + 1 / 2)
      have h2 := Int.lt_floor_add_one (v / a' + 1 / 2)
      refine ⟨⌊v / a' + 1 / 2⌋, ?_, ?_⟩
      · have i1 : ((⌊v / a' + 1 / 2⌋ : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
        have i2 : ((-(h : ℤ) - 1 : ℤ) : ℝ) < ((⌊v / a' + 1 / 2⌋ : ℤ) : ℝ) := by push_cast; linarith
        have j1 : ⌊v / a' + 1 / 2⌋ < 1 := by exact_mod_cast i1
        have j2 : -(h : ℤ) - 1 < ⌊v / a' + 1 / 2⌋ := by exact_mod_cast i2
        rw [abs_le]; constructor <;> omega
      · rw [abs_le]; constructor <;> linarith
  obtain ⟨r, hr, hr'⟩ := key
  refine ⟨r, hr, (norm_coe_sub_le v _).trans ?_⟩
  have e : v - (r : ℝ) * a' = a' * (v / a' - r) := by field_simp
  rw [e, abs_mul, abs_of_pos ha']
  calc a' * |v / a' - r| ≤ a' * (1 / 2) := mul_le_mul_of_nonneg_left hr' ha'.le
    _ = a' / 2 := by ring

/-! ### The torus -/

/-- The lattice of spacing `a` in `𝕋`: the points all of whose coordinates are multiples of `a`. -/
def Lat (p a : ℝ) : Set (Tor p) := {z | ∀ ν, z ν ∈ LatC p a}

/-- The cell `{z | |z - y|_∞ ≤ a/2}`, the closed cube of side `a` centred at `y`. -/
def cell (a : ℝ) (y : Tor p) : Set (Tor p) := Metric.closedBall y (a / 2)

lemma mem_cell {a : ℝ} {y z : Tor p} : z ∈ cell a y ↔ ‖z - y‖ ≤ a / 2 := by
  rw [cell, Metric.mem_closedBall, dist_eq_norm]

/-- The norm `|z|_∞` is attained at a coordinate. -/
lemma exists_coord_eq (z : Tor p) : ∃ ν, ‖z‖ = ‖z ν‖ := by
  obtain ⟨ν, -, hν⟩ := Finset.exists_max_image Finset.univ (fun ν => ‖z ν‖) Finset.univ_nonempty
  exact ⟨ν, le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => hν μ (Finset.mem_univ _))
    (norm_le_pi_norm z ν)⟩

lemma coord_le (z : Tor p) (ν : Fin 4) : ‖z ν‖ ≤ ‖z‖ := norm_le_pi_norm z ν

lemma lat_sub {a : ℝ} {x y : Tor p} (hx : x ∈ Lat p a) (hy : y ∈ Lat p a) : x - y ∈ Lat p a :=
  fun ν => latC_sub (hx ν) (hy ν)

/-- **`T^{(j)} ⊂ T^{(j-1)}`**, and in general `Lat ℓ a ⊂ Lat ℓ a'` for `a = q a'`. -/
theorem lat_subset {a a' : ℝ} {q : ℕ} (h : a = q * a') : Lat p a ⊆ Lat p a' :=
  fun _ hz ν => latC_mono h (hz ν)

/-- **The cells cover the torus.** -/
theorem cells_cover {a : ℝ} (ha : 0 < a) (z : Tor p) : ∃ y ∈ Lat p a, z ∈ cell a y := by
  choose r hr using fun ν => exists_near (p := p) ha (z ν)
  refine ⟨fun ν => (((r ν : ℝ) * a : ℝ) : AddCircle p), fun ν => latC_mul a (r ν), ?_⟩
  rw [mem_cell]
  exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ν => hr ν

/-- **Two cells meet at most in boundary points**: a common point of the cells of two distinct
lattice points is at distance exactly `a/2` from both. -/
theorem cells_inter {a : ℝ} {M : ℕ} (ha : 0 < a) (hM : 0 < M) (hp : p = M * a) {y y' : Tor p}
    (hy : y ∈ Lat p a) (hy' : y' ∈ Lat p a) (hne : y ≠ y') {z : Tor p} (hz : z ∈ cell a y)
    (hz' : z ∈ cell a y') : ‖z - y‖ = a / 2 ∧ ‖z - y'‖ = a / 2 := by
  rw [mem_cell] at hz hz'
  obtain ⟨ν, hν⟩ := Function.ne_iff.1 hne
  have hd : y ν - y' ν ≠ 0 := sub_ne_zero.2 hν
  have hsum : a ≤ ‖z ν - y ν‖ + ‖z ν - y' ν‖ := by
    by_contra hc
    push Not at hc
    apply hd
    refine latC_eq_zero ha hM hp (latC_sub (hy ν) (hy' ν)) ?_
    calc ‖y ν - y' ν‖ = ‖(z ν - y' ν) - (z ν - y ν)‖ := by congr 1; abel
      _ ≤ ‖z ν - y' ν‖ + ‖z ν - y ν‖ := norm_sub_le _ _
      _ < a := by linarith
  have h1 : ‖z ν - y ν‖ ≤ ‖z - y‖ := coord_le (z - y) ν
  have h2 : ‖z ν - y' ν‖ ≤ ‖z - y'‖ := coord_le (z - y') ν
  constructor <;> linarith

/-- **No point of a finer lattice lies on the boundary of a cell**: for `a = q a'` with `q` odd, a
point of `Lat ℓ a'` is not at distance `a/2` from a point of `Lat ℓ a`. -/
theorem not_mem_boundary {a a' : ℝ} {M : ℕ} {q : ℕ} (ha' : 0 < a') (hM : 0 < M) (hp : p = M * a')
    (hq : Odd q) (ha : a = q * a') {x y : Tor p} (hx : x ∈ Lat p a') (hy : y ∈ Lat p a) :
    ‖x - y‖ ≠ a / 2 := by
  obtain ⟨ν, hν⟩ := exists_coord_eq (x - y)
  rw [hν, ha]
  exact latC_norm_ne ha' hM hp (latC_sub (hx ν) (lat_subset ha hy ν)) hq

/-- The points of a finer lattice in the cell of `y`: `Lat ℓ a' ∩ cell (2H+1)a' y` is the image of the
box `|m_μ| ≤ H` under `m ↦ y + a' Σ m_μ e_μ` (`eq:block`). -/
theorem block_eq {a a' : ℝ} {M : ℕ} {H : ℕ} (ha' : 0 < a') (hM : 0 < M) (hp : p = M * a')
    (ha : a = (2 * H + 1 : ℕ) * a') {y : Tor p} (hy : y ∈ Lat p a) :
    Lat p a' ∩ cell a y =
      (fun m : Fin 4 → ℤ => y + fun ν => (((m ν : ℝ) * a' : ℝ) : AddCircle p)) '' {m | ∀ ν, |m ν| ≤ H} := by
  have hy' : y ∈ Lat p a' := lat_subset ha hy
  ext x
  simp only [mem_inter_iff, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxc⟩
    rw [mem_cell] at hxc
    have hc : ∀ ν, ∃ s : ℤ, |s| ≤ H ∧ x ν - y ν = (((s : ℝ) * a' : ℝ) : AddCircle p) := fun ν =>
      (latC_small_iff ha' hM hp H).1 ⟨latC_sub (hx ν) (hy' ν), (coord_le (x - y) ν).trans (ha ▸ hxc)⟩
    choose m hm hm' using hc
    exact ⟨m, hm, funext fun ν => by simp only [Pi.add_apply]; rw [← hm' ν]; abel⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨fun ν => latC_add (hy' ν) (latC_mul a' (m ν)), ?_⟩
    rw [mem_cell, add_sub_cancel_left, ha]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ν => ?_
    exact ((latC_small_iff ha' hM hp H).2 ⟨m ν, hm ν, rfl⟩).2

/-- **A cell is the union of the cells of the finer lattice at the points of its block.** -/
theorem cell_eq_biUnion {a a' : ℝ} {M : ℕ} {H : ℕ} (ha' : 0 < a') (hM : 0 < M) (hp : p = M * a')
    (ha : a = (2 * H + 1 : ℕ) * a') {y : Tor p} (hy : y ∈ Lat p a) :
    cell a y = ⋃ x ∈ Lat p a' ∩ cell a y, cell a' x := by
  have hy' : y ∈ Lat p a' := lat_subset ha hy
  ext z
  simp only [mem_iUnion, exists_prop]
  constructor
  · intro hz
    rw [mem_cell] at hz
    have hc : ∀ ν, ∃ r : ℤ, |r| ≤ H ∧ ‖(z ν - y ν) - (((r : ℝ) * a' : ℝ) : AddCircle p)‖ ≤ a' / 2 :=
      fun ν => exists_fine ha' ((coord_le (z - y) ν).trans (ha ▸ hz))
    choose r hr hr' using hc
    refine ⟨y + fun ν => (((r ν : ℝ) * a' : ℝ) : AddCircle p), ?_, ?_⟩
    · have := block_eq ha' hM hp ha hy
      rw [this]
      exact ⟨r, hr, rfl⟩
    · rw [mem_cell]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ν => ?_
      have e : (z - (y + fun ν => (((r ν : ℝ) * a' : ℝ) : AddCircle p))) ν =
          (z ν - y ν) - (((r ν : ℝ) * a' : ℝ) : AddCircle p) := by
        simp only [Pi.sub_apply, Pi.add_apply]; abel
      rw [e]; exact hr' ν
  · rintro ⟨x, ⟨hx, hxc⟩, hzx⟩
    rw [mem_cell] at hxc hzx ⊢
    refine (pi_norm_le_iff_of_nonneg (by rw [ha]; positivity)).2 fun ν => ?_
    obtain ⟨s, hs, hs'⟩ := (latC_small_iff ha' hM hp H).1
      ⟨latC_sub (hx ν) (hy' ν), (coord_le (x - y) ν).trans (ha ▸ hxc)⟩
    have h1 : ‖x ν - y ν‖ ≤ H * a' := by
      rw [hs']
      refine (norm_coe_le _).trans ?_
      rw [abs_mul, abs_of_pos ha']
      have : |(s : ℝ)| ≤ H := by
        have : ((|s| : ℤ) : ℝ) ≤ ((H : ℤ) : ℝ) := by exact_mod_cast hs
        push_cast at this; exact this
      nlinarith
    have h2 : ‖z ν - x ν‖ ≤ a' / 2 := (coord_le (z - x) ν).trans hzx
    calc ‖(z - y) ν‖ = ‖(z ν - x ν) + (x ν - y ν)‖ := by simp only [Pi.sub_apply]; abel_nf
      _ ≤ ‖z ν - x ν‖ + ‖x ν - y ν‖ := norm_add_le _ _
      _ ≤ a' / 2 + H * a' := by linarith
      _ = a / 2 := by rw [ha]; push_cast; ring

/-- `r a = 0` in `ℝ/pℤ` iff `M ∣ r`, for `p = M a`. -/
lemma coe_mul_eq_zero_iff {a : ℝ} {M : ℕ} (ha : 0 < a) (hp : p = M * a) (d : ℤ) :
    ((((d : ℝ) * a : ℝ)) : AddCircle p) = 0 ↔ (M : ℤ) ∣ d := by
  rw [AddCircle.coe_eq_zero_iff p]
  constructor
  · rintro ⟨n, hn⟩
    rw [zsmul_eq_mul, hp] at hn
    have h1 : ((n * M : ℤ) : ℝ) = (d : ℝ) := by
      push_cast
      have := congrArg (· / a) hn
      field_simp at this
      linarith
    exact ⟨n, by rw [mul_comm]; exact_mod_cast h1.symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [zsmul_eq_mul, hp]; push_cast; ring⟩

/-- **`|Lat ℓ a' ∩ cell a y| = (2H + 1)⁴`** when `a = (2H + 1)a'` and `2H + 1 ≤ ℓ/a'`. -/
theorem block_ncard {a a' : ℝ} {M H : ℕ} (ha' : 0 < a') (hM : 0 < M) (hp : p = M * a')
    (ha : a = (2 * H + 1 : ℕ) * a') (hHM : 2 * H + 1 ≤ M) {y : Tor p} (hy : y ∈ Lat p a) :
    (Lat p a' ∩ cell a y).ncard = (2 * H + 1) ^ 4 := by
  have hinj : Set.InjOn (fun m : Fin 4 → ℤ => y + fun ν => (((m ν : ℝ) * a' : ℝ) : AddCircle p))
      {m | ∀ ν, |m ν| ≤ H} := by
    intro m hm m' hm' he
    funext ν
    have h1 := congrFun he ν
    simp only [Pi.add_apply, add_right_inj] at h1
    have h0 : ((((m ν - m' ν : ℤ) : ℝ) * a' : ℝ) : AddCircle p) = 0 := by
      push_cast; rw [sub_mul, AddCircle.coe_sub, h1, sub_self]
    obtain ⟨k, hk⟩ := (coe_mul_eq_zero_iff ha' hp _).1 h0
    have b1 := abs_le.1 (hm ν)
    have b2 := abs_le.1 (hm' ν)
    have hM' : (2 * H + 1 : ℤ) ≤ M := by exact_mod_cast hHM
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hk0, mul_zero] at hk
    linarith
  rw [block_eq ha' hM hp ha hy, hinj.ncard_image]
  have e : {m : Fin 4 → ℤ | ∀ ν, |m ν| ≤ H} =
      ↑(Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(H : ℤ)) H) := by
    ext m; simp only [mem_ofPred_eq, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  rw [e, Set.ncard_coe_finset, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- **The cells of a coarser lattice partition a finer lattice**: for `a = q a'` with `q` odd, every
point of `Lat ℓ a'` lies in the cell of exactly one point of `Lat ℓ a`. -/
theorem blocks_partition {a a' : ℝ} {M Ma q : ℕ} (ha' : 0 < a') (hM : 0 < M) (hp : p = M * a')
    (hMa : 0 < Ma) (hpa : p = Ma * a) (hq : Odd q) (ha : a = q * a') {x : Tor p} (hx : x ∈ Lat p a') :
    ∃! y, y ∈ Lat p a ∧ x ∈ cell a y := by
  have ha0 : 0 < a := by rw [ha]; exact mul_pos (Nat.cast_pos.2 hq.pos) ha'
  obtain ⟨y, hy, hxy⟩ := cells_cover ha0 x
  refine ⟨y, ⟨hy, hxy⟩, fun y' ⟨hy', hxy'⟩ => ?_⟩
  by_contra hne
  exact not_mem_boundary ha' hM hp hq ha hx hy (cells_inter ha0 hMa hpa hy hy' (Ne.symm hne) hxy hxy').1

/-! ### The lattices, cells, and blocks of the core -/

/-- `η = L^{-k}`. -/
def eta (L k : ℕ) : ℝ := ((L : ℝ) ^ k)⁻¹

/-- `a_j = Lʲη`. -/
def sp (L k j : ℕ) : ℝ := (L : ℝ) ^ j * eta L k

/-- `ℓ_𝕋 = 2L^{m_𝕋}`. -/
def ellT (L m : ℕ) : ℝ := 2 * (L : ℝ) ^ m

/-- The lattice `T^{(j)} = (a_jℤ/ℓ_𝕋ℤ)⁴`. -/
def T (L k m j : ℕ) : Set (Tor (ellT L m)) := Lat (ellT L m) (sp L k j)

/-- The cell `Δ_j(y)`. -/
def Δ (L k m j : ℕ) (y : Tor (ellT L m)) : Set (Tor (ellT L m)) := cell (sp L k j) y

/-- The block `Bⁿ(y) = Δ_j(y) ∩ T^{(j-n)}`. -/
def Bn (L k m j n : ℕ) (y : Tor (ellT L m)) : Set (Tor (ellT L m)) := Δ L k m j y ∩ T L k m (j - n)

variable {L k m : ℕ}

lemma sp_pos (hL : 0 < L) (j : ℕ) : 0 < sp L k j := by unfold sp eta; positivity

lemma ellT_eq (hL : 0 < L) {j : ℕ} (hj : j ≤ k) :
    ellT L m = ((2 * L ^ (m + (k - j)) : ℕ) : ℝ) * sp L k j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hL' : (L : ℝ) ≠ 0 := by positivity
  simp only [ellT, sp, eta, Nat.add_sub_cancel_left]
  push_cast
  field_simp
  ring

lemma M_pos (hL : 0 < L) (j : ℕ) : 0 < 2 * L ^ (m + (k - j)) := by positivity

lemma sp_sub (j n : ℕ) (hn : n ≤ j) : sp L k j = ((L ^ n : ℕ) : ℝ) * sp L k (j - n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [sp, Nat.add_sub_cancel_left]
  push_cast
  ring

/-- **`T^{(j)} ⊂ T^{(j-1)}`.** -/
theorem T_subset (j : ℕ) : T L k m (j + 1) ⊆ T L k m j :=
  lat_subset (q := L) (by simp only [sp]; ring)

/-- **The cells `Δ_j(y)`, `y ∈ T^{(j)}`, cover the torus.** -/
theorem Δ_cover (hL : 0 < L) (j : ℕ) (z : Tor (ellT L m)) : ∃ y ∈ T L k m j, z ∈ Δ L k m j y :=
  cells_cover (sp_pos hL j) z

/-- **Two cells of scale `j` meet at most in boundary points.** -/
theorem Δ_inter (hL : 0 < L) {j : ℕ} (hj : j ≤ k) {y y' : Tor (ellT L m)} (hy : y ∈ T L k m j)
    (hy' : y' ∈ T L k m j) (hne : y ≠ y') {z : Tor (ellT L m)} (hz : z ∈ Δ L k m j y)
    (hz' : z ∈ Δ L k m j y') : ‖z - y‖ = sp L k j / 2 ∧ ‖z - y'‖ = sp L k j / 2 :=
  cells_inter (sp_pos hL j) (M_pos hL j) (ellT_eq hL hj) hy hy' hne hz hz'

/-- **No point of `T^{(i)}` lies on the boundary of a cell `Δ_j(y)` with `j ≥ i`.** -/
theorem not_mem_boundary_T (hL : Odd L) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ k) {x y : Tor (ellT L m)}
    (hx : x ∈ T L k m i) (hy : y ∈ T L k m j) : ‖x - y‖ ≠ sp L k j / 2 :=
  not_mem_boundary (sp_pos hL.pos i) (M_pos hL.pos i) (ellT_eq hL.pos (hij.trans hj)) (hL.pow (n := j - i))
    (by rw [sp_sub j (j - i) (Nat.sub_le j i), Nat.sub_sub_self hij]) hx hy

/-- **`eq:block`**: `Bⁿ(y) = {y + a_{j-n} Σ_μ n_μ e_μ | |n_μ| ≤ (Lⁿ - 1)/2}`. -/
theorem Bn_eq (hL : Odd L) {j n : ℕ} (hn : n ≤ j) (hj : j ≤ k) {y : Tor (ellT L m)} (hy : y ∈ T L k m j) :
    Bn L k m j n y = (fun c : Fin 4 → ℤ => y + fun ν => (((c ν : ℝ) * sp L k (j - n) : ℝ) : AddCircle (ellT L m))) ''
      {c | ∀ ν, |c ν| ≤ Blocks.half L n} := by
  rw [Bn, inter_comm]
  exact block_eq (sp_pos hL.pos _) (M_pos hL.pos _) (ellT_eq hL.pos ((Nat.sub_le j n).trans hj))
    (by rw [Blocks.two_half_add_one hL]; exact sp_sub j n hn) hy

/-- **`|Bⁿ(y)| = L^{4n}`.** -/
theorem Bn_ncard (hL : Odd L) {j n : ℕ} (hn : n ≤ j) (hj : j ≤ k) {y : Tor (ellT L m)}
    (hy : y ∈ T L k m j) : (Bn L k m j n y).ncard = L ^ (4 * n) := by
  rw [Bn, inter_comm, T, Δ, block_ncard (H := Blocks.half L n) (sp_pos hL.pos _) (M_pos hL.pos _)
    (ellT_eq hL.pos ((Nat.sub_le j n).trans hj)) (by rw [Blocks.two_half_add_one hL]; exact sp_sub j n hn)
    ?_ hy, Blocks.two_half_add_one hL, ← pow_mul, mul_comm]
  rw [Blocks.two_half_add_one hL]
  have h1 : L ^ n ≤ L ^ (m + (k - (j - n))) := Nat.pow_le_pow_right hL.pos (by omega)
  omega

/-- **The blocks `Bⁿ(y)`, `y ∈ T^{(j)}`, form a partition of `T^{(j-n)}`.** -/
theorem Bn_partition (hL : Odd L) {j n : ℕ} (hn : n ≤ j) (hj : j ≤ k) {x : Tor (ellT L m)}
    (hx : x ∈ T L k m (j - n)) : ∃! y, y ∈ T L k m j ∧ x ∈ Bn L k m j n y := by
  obtain ⟨y, ⟨hy, hxy⟩, hu⟩ := blocks_partition (sp_pos hL.pos (j - n)) (M_pos hL.pos (j - n))
    (ellT_eq hL.pos ((Nat.sub_le j n).trans hj)) (M_pos hL.pos j) (ellT_eq hL.pos hj) (hL.pow (n := n))
    (sp_sub j n hn) hx
  exact ⟨y, ⟨hy, hxy, hx⟩, fun y' ⟨hy', hxy', _⟩ => hu y' ⟨hy', hxy'⟩⟩

/-- **Each cell `Δ_j(y)` is the union of the `L⁴` cells `Δ_{j-1}(x)`, `x ∈ B(y)`.** -/
theorem Δ_eq_iUnion (hL : Odd L) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k) {y : Tor (ellT L m)}
    (hy : y ∈ T L k m j) : Δ L k m j y = ⋃ x ∈ Bn L k m j 1 y, Δ L k m (j - 1) x := by
  have e := cell_eq_biUnion (H := Blocks.half L 1) (sp_pos hL.pos (j - 1)) (M_pos hL.pos (j - 1))
    (ellT_eq hL.pos ((Nat.sub_le j 1).trans hj)) (by rw [Blocks.two_half_add_one hL]; exact sp_sub j 1 hj1) hy
  rw [Δ, e, Bn, inter_comm]
  rfl

/-! ### Grids -/

/-- The grid of side `s`: the cubes `{z | |z - c|_∞ ≤ s/2}`, `c ∈ (sℤ/ℓℤ)⁴`. -/
def grid (p s : ℝ) : Set (Set (Tor p)) := {C | ∃ c ∈ Lat p s, C = cell s c}

/-- **The cells `Δ_j(y)` form the grid of side `a_j`.** -/
theorem grid_sp (j : ℕ) : grid (ellT L m) (sp L k j) = {C | ∃ y ∈ T L k m j, C = Δ L k m j y} := rfl

/-- `ℓ_𝕋 = 2L^{m - i} s` for the side `s = Lⁱ`, `i ≤ m`. -/
lemma ellT_eq_side (hL : 0 < L) {i : ℤ} (hi : i ≤ m) :
    ellT L m = ((2 * L ^ (m - i).toNat : ℕ) : ℝ) * (L : ℝ) ^ i := by
  have hL' : (L : ℝ) ≠ 0 := by positivity
  have e : (m : ℤ) = ((m - i).toNat : ℕ) + i := by omega
  simp only [ellT]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_natCast (L : ℝ) ((m - i).toNat), ← zpow_add₀ hL', ← e]

/-- **The cubes of a grid cover the torus.** -/
theorem grid_cover (hL : 0 < L) (i : ℤ) (z : Tor (ellT L m)) : ∃ C ∈ grid (ellT L m) ((L : ℝ) ^ i), z ∈ C := by
  obtain ⟨c, hc, hz⟩ := cells_cover (zpow_pos (Nat.cast_pos.2 hL) i) z
  exact ⟨_, ⟨c, hc, rfl⟩, hz⟩

/-- **The cubes of a grid meet at most in boundary points.** -/
theorem grid_inter (hL : 0 < L) {i : ℤ} (hi : i ≤ m) {c c' : Tor (ellT L m)}
    (hc : c ∈ Lat (ellT L m) ((L : ℝ) ^ i)) (hc' : c' ∈ Lat (ellT L m) ((L : ℝ) ^ i)) (hne : c ≠ c')
    {z : Tor (ellT L m)} (hz : z ∈ cell ((L : ℝ) ^ i) c) (hz' : z ∈ cell ((L : ℝ) ^ i) c') :
    ‖z - c‖ = (L : ℝ) ^ i / 2 ∧ ‖z - c'‖ = (L : ℝ) ^ i / 2 :=
  cells_inter (zpow_pos (Nat.cast_pos.2 hL) i) (Nat.mul_pos two_pos (pow_pos hL _)) (ellT_eq_side hL hi) hc hc'
    hne hz hz'

/-- **Since `L` is odd, every cube of the grid of side `Ls` is the union of `L⁴` cubes of the grid of
side `s`.** -/
theorem grid_refine (hL : Odd L) {i : ℤ} (hi : i + 1 ≤ m) {c : Tor (ellT L m)}
    (hc : c ∈ Lat (ellT L m) ((L : ℝ) ^ (i + 1))) :
    cell ((L : ℝ) ^ (i + 1)) c = ⋃ x ∈ Lat (ellT L m) ((L : ℝ) ^ i) ∩ cell ((L : ℝ) ^ (i + 1)) c,
        cell ((L : ℝ) ^ i) x ∧
      (Lat (ellT L m) ((L : ℝ) ^ i) ∩ cell ((L : ℝ) ^ (i + 1)) c).ncard = L ^ 4 := by
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL.pos.ne'
  have hs : (L : ℝ) ^ (i + 1) = ((2 * Blocks.half L 1 + 1 : ℕ) : ℝ) * (L : ℝ) ^ i := by
    rw [Blocks.two_half_add_one hL, zpow_add_one₀ hL']; push_cast; ring
  refine ⟨cell_eq_biUnion (zpow_pos (Nat.cast_pos.2 hL.pos) i) (Nat.mul_pos two_pos (pow_pos hL.pos _)) (ellT_eq_side hL.pos (by omega))
    hs hc, ?_⟩
  rw [block_ncard (zpow_pos (Nat.cast_pos.2 hL.pos) i) (Nat.mul_pos two_pos (pow_pos hL.pos _)) (ellT_eq_side hL.pos (by omega)) hs ?_ hc,
    Blocks.two_half_add_one hL, pow_one]
  rw [Blocks.two_half_add_one hL, pow_one]
  have h1 : L ^ 1 ≤ L ^ (m - i).toNat := Nat.pow_le_pow_right hL.pos (by omega)
  rw [pow_one] at h1
  omega

/-! ### The fine lattice `(ℤ/N)⁴` as `T^{(0)}` -/

section Fine

variable {N : ℕ} [NeZero N]

/-- The point `xη` of `T^{(0)}` of a point `x` of `(ℤ/N)⁴`. -/
def emb (L k m : ℕ) (x : Blocks.Pt N) : Tor (ellT L m) :=
  fun ν => ((((x ν).val : ℝ) * eta L k : ℝ) : AddCircle (ellT L m))

lemma ellT_eq_N (hL : 0 < L) (hN : N = 2 * L ^ (m + k)) : ellT L m = (N : ℝ) * eta L k := by
  have := ellT_eq (k := k) (m := m) hL (Nat.zero_le k)
  simp only [Nat.sub_zero, sp, pow_zero, one_mul] at this
  rw [this, hN]

lemma eta_pos (hL : 0 < L) : 0 < eta L k := by unfold eta; positivity

lemma emb_coord_sub (hL : 0 < L) (hN : N = 2 * L ^ (m + k)) (u v : ZMod N) :
    ((((u.val : ℝ) * eta L k : ℝ) : AddCircle (ellT L m)) -
      (((v.val : ℝ) * eta L k : ℝ) : AddCircle (ellT L m))) =
      ((((u - v).valMinAbs : ℝ) * eta L k : ℝ) : AddCircle (ellT L m)) := by
  rw [← AddCircle.coe_sub, ← sub_eq_zero, ← AddCircle.coe_sub, ← sub_mul, ← sub_mul]
  have e : ((u.val : ℝ) - v.val - ((u - v).valMinAbs : ℝ)) =
      (((u.val : ℤ) - v.val - (u - v).valMinAbs : ℤ) : ℝ) := by
    push_cast; ring
  rw [e, coe_mul_eq_zero_iff (eta_pos hL) (ellT_eq_N hL hN), ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp

/-- **The distance of the fine lattice**: `‖xη - yη‖ = |x - y| η` in each coordinate. -/
lemma norm_emb_coord (hL : 0 < L) (hN : N = 2 * L ^ (m + k)) (u v : ZMod N) :
    ‖((((u.val : ℝ) * eta L k : ℝ) : AddCircle (ellT L m)) -
      (((v.val : ℝ) * eta L k : ℝ) : AddCircle (ellT L m)))‖ = Blocks.cd (u - v) * eta L k := by
  have he := eta_pos (k := k) hL
  have hab : |((u - v).valMinAbs : ℝ)| = (Blocks.cd (u - v) : ℝ) := by
    rw [Blocks.cd, Nat.cast_natAbs, Int.cast_abs]
  have hp0 : 0 < ellT L m := by
    rw [ellT_eq_N hL hN]; exact mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))) he
  have hbd : |((u - v).valMinAbs : ℝ) * eta L k| ≤ |ellT L m| / 2 := by
    rw [abs_mul, abs_of_pos he, hab, abs_of_pos hp0, ellT_eq_N hL hN]
    have h1 := ZMod.natAbs_valMinAbs_le (u - v)
    have h2 : (2 * Blocks.cd (u - v) : ℝ) ≤ N := by
      exact_mod_cast (by unfold Blocks.cd; omega : 2 * Blocks.cd (u - v) ≤ N)
    nlinarith
  rw [emb_coord_sub hL hN, (AddCircle.norm_coe_eq_abs_iff _ hp0.ne').2 hbd, abs_mul, abs_of_pos he, hab]

lemma emb_sub_apply (x y : Blocks.Pt N) (ν : Fin 4) :
    (emb L k m x - emb L k m y) ν = ((((x ν).val : ℝ) * eta L k : ℝ) : AddCircle (ellT L m)) -
      ((((y ν).val : ℝ) * eta L k : ℝ) : AddCircle (ellT L m)) := rfl

/-- **`|xη - yη|_∞ = |x - y|_∞ η`.** -/
theorem norm_emb_sub (hL : 0 < L) (hN : N = 2 * L ^ (m + k)) (x y : Blocks.Pt N) :
    ‖emb L k m x - emb L k m y‖ = Blocks.dinf x y * eta L k := by
  have he := eta_pos (k := k) hL
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ν => ?_
    rw [emb_sub_apply, norm_emb_coord hL hN]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Blocks.cd_le_dinf x y ν) he.le
  · obtain ⟨ν, -, hν⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun ν => Blocks.cd (x ν - y ν))
    have : Blocks.dinf x y = Blocks.cd (x ν - y ν) := hν
    rw [this, ← norm_emb_coord hL hN, ← emb_sub_apply]
    exact coord_le _ ν

theorem emb_injective (hL : 0 < L) (hN : N = 2 * L ^ (m + k)) :
    Function.Injective (emb (N := N) L k m) := by
  intro x y he
  have h0 : Blocks.dinf x y = 0 := by
    have := norm_emb_sub hL hN x y
    rw [he, sub_self, norm_zero] at this
    have h1 : (Blocks.dinf x y : ℝ) = 0 := by
      rcases mul_eq_zero.1 this.symm with h | h
      · exact h
      · exact absurd h (eta_pos hL).ne'
    exact_mod_cast h1
  funext ν
  have := Blocks.cd_le_dinf x y ν
  rw [h0] at this
  exact sub_eq_zero.1 (Blocks.cd_eq_zero (by omega))

/-- **The image of `(ℤ/N)⁴` is `T^{(0)}`.** -/
theorem range_emb (hL : 0 < L) (hN : N = 2 * L ^ (m + k)) : range (emb (N := N) L k m) = T L k m 0 := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩ ν
    exact ⟨(x ν).val, by simp [emb, sp]⟩
  · intro hz
    choose r hr using hz
    refine ⟨fun ν => (r ν : ZMod N), funext fun ν => ?_⟩
    rw [hr ν, emb, ← sub_eq_zero, ← AddCircle.coe_sub]
    simp only [sp, pow_zero, one_mul]
    rw [← sub_mul]
    have e : (((r ν : ZMod N).val : ℝ) - (r ν : ℝ)) = ((((r ν : ZMod N).val : ℤ) - r ν : ℤ) : ℝ) := by
      push_cast; ring
    rw [e, coe_mul_eq_zero_iff (eta_pos hL) (ellT_eq_N hL hN), ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp

/-- **`x ∈ T^{(j)}` in the model of `BlockLattice.lean` iff `xη ∈ T^{(j)}`.** -/
theorem inLat_iff (hL : 0 < L) (hN : N = 2 * L ^ (m + k)) {j : ℕ} (x : Blocks.Pt N) :
    Blocks.InLat L j x ↔ emb L k m x ∈ T L k m j := by
  have key : ∀ (u : ZMod N) (r : ℤ), u = (((L ^ j : ℕ) * r : ℤ) : ZMod N) ↔
      ((((u.val : ℝ) * eta L k : ℝ)) : AddCircle (ellT L m)) =
        (((r : ℝ) * sp L k j : ℝ) : AddCircle (ellT L m)) := by
    intro u r
    rw [← sub_eq_zero (a := ((((u.val : ℝ) * eta L k : ℝ)) : AddCircle (ellT L m))), ← AddCircle.coe_sub]
    have e : (u.val : ℝ) * eta L k - (r : ℝ) * sp L k j =
        (((u.val : ℤ) - (L ^ j : ℕ) * r : ℤ) : ℝ) * eta L k := by
      simp only [sp]; push_cast; ring
    rw [e, coe_mul_eq_zero_iff (eta_pos hL) (ellT_eq_N hL hN), ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [sub_eq_zero]
  constructor
  · intro hx ν
    obtain ⟨r, hr⟩ := hx ν
    exact ⟨r, (key _ r).1 (by exact_mod_cast hr)⟩
  · intro hx ν
    obtain ⟨r, hr⟩ := hx ν
    exact ⟨r, by have := (key _ r).2 hr; exact_mod_cast this⟩

/-- **The point `cen j x` of `BlockLattice.lean` is the point of `T^{(j)}` whose cell contains `xη`.** -/
theorem emb_mem_Δ_cen (hL : Odd L) (hN : N = 2 * L ^ (m + k)) (j : ℕ) (x : Blocks.Pt N) :
    emb L k m x ∈ Δ L k m j (emb L k m (Blocks.cen L j x)) := by
  rw [Δ, mem_cell, norm_emb_sub hL.pos hN]
  have h1 : Blocks.dinf x (Blocks.cen L j x) ≤ Blocks.half L j :=
    Finset.sup_le fun ν _ => Blocks.cd_sub_cen1_le hL j (x ν)
  have h2 : (2 * Blocks.half L j + 1 : ℝ) = (L : ℝ) ^ j := by exact_mod_cast Blocks.two_half_add_one hL j
  have h3 : (Blocks.dinf x (Blocks.cen L j x) : ℝ) ≤ Blocks.half L j := by exact_mod_cast h1
  have := eta_pos (k := k) hL.pos
  simp only [sp]
  nlinarith

end Fine

end Lattices
end CoreLean

end
