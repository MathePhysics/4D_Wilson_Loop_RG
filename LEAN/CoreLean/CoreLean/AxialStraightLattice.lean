/-
`cor:axial-straight` of BALABAN_CORE.tex (`696dd3a66b99`) on the lattices `T^{(i)}`: the passage from the
fine-unit coordinates of `BoxGeometry.lean` to the lattice `T^{(i)}` in its own units, and the comparison of
the bounds of `lem:axial-smallness` on the lattice (`AxialReference.lean`) with `C_ax α₀`, `C_ax = 59√N`,
`α₀ = 2αL^{-2(j-i-1)}`.

A point `x` of `T^{(i)}` in `𝖡` has fine-unit coordinates divisible by `L^i`; its coordinates in the units of
`T^{(i)}` are `x / L^i` (`qt`), and its site on the torus `T^{(i)} = Site (nn i)` is `ofs (base i) (x / L^i)`
(`img`), with `base i` the site of `c'₋`. With `L = 2h + 1`, a point lies in the block `B(z)` of the order
`i + 1` exactly when its offset from `z` in the units of `T^{(i)}` lies in `[-h, h]⁴` (`inM_of_blk`,
`blk_of_inM`).

The hypotheses on the fields `V i = M^i(U)` are those of the corollary in the form in which the proof uses
them: the plaquettes of `M^i(U)` in `𝖡` are at most `2α(a_i/a_j)²` in `|·|` (`prop:regular-averages`(ii)),
hence at most `√N·2αL^{-2(j-i)}` in the operator norm (`lem:norms`(i)); the transports of `M^i(U)` from the
centres of the blocks are `id` (the axial gauge); `M^{i+1}(U)(c̃) = M(M^i(U))(c̃)` (`def:average`).
-/
import CoreLean.BoxGeometry
import CoreLean.AxialReference

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace AxialStraightLattice

open BoxGeometry AxialReference LatticePaths LatticeKappa

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### `L = 2h + 1` -/

/-- `L = 2h + 1`. -/
def Lz (h : ℕ) : ℤ := 2 * h + 1

lemma Lz_odd (h : ℕ) : Odd (Lz h) := ⟨h, rfl⟩

lemma Lz_one (h : ℕ) : 1 ≤ Lz h := by unfold Lz; omega

lemma Lz_pos (h : ℕ) : 0 < Lz h := by unfold Lz; omega

lemma Lz_nat (h : ℕ) : Lz h = ((2 * h + 1 : ℕ) : ℤ) := by unfold Lz; push_cast; ring

lemma Lz_real (h : ℕ) : ((Lz h : ℤ) : ℝ) = ((2 * h + 1 : ℕ) : ℝ) := by unfold Lz; push_cast; ring

/-! ### Coordinates in the units of `T^{(i)}` -/

/-- The coordinates of a point of `T^{(i)}` in the units of `T^{(i)}`. -/
def qt (h i : ℕ) (x : Fin 4 → ℤ) : Fin 4 → ℤ := fun σ => x σ / Lz h ^ i

lemma qt_eq {h i : ℕ} {x v : Fin 4 → ℤ} (hx : x = Lz h ^ i • v) : qt h i x = v := by
  funext σ
  simp only [qt, hx, Pi.smul_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel_left _ (pow_pos (Lz_pos h) i).ne'

lemma qt_spec {h i : ℕ} {x : Fin 4 → ℤ} (hx : Lat (Lz h) i x) : x = Lz h ^ i • qt h i x := by
  funext σ
  simp only [qt, Pi.smul_apply, smul_eq_mul]
  exact (Int.mul_ediv_cancel' (hx σ)).symm

lemma lat_smul {h i : ℕ} (v : Fin 4 → ℤ) : Lat (Lz h) i (Lz h ^ i • v) := fun σ => by
  simp only [Pi.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

lemma lat_le {h i : ℕ} {z : Fin 4 → ℤ} (hz : Lat (Lz h) (i + 1) z) : Lat (Lz h) i z := fun σ =>
  (pow_dvd_pow _ (Nat.le_succ i)).trans (hz σ)

lemma ev_eq_smul (h i : ℕ) (ρ : Fin 4) : ev (Lz h) i ρ = Lz h ^ i • (Pi.single ρ 1 : Fin 4 → ℤ) := by
  funext σ
  by_cases hσ : σ = ρ
  · subst hσ; simp [ev]
  · simp [ev, Pi.single_eq_of_ne hσ]

lemma ev_succ_eq (h i : ℕ) (ρ : Fin 4) :
    ev (Lz h) (i + 1) ρ = Lz h ^ i • (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) := by
  funext σ
  by_cases hσ : σ = ρ
  · subst hσ; simp [ev, pow_succ, Lz_nat]
  · simp [ev, Pi.single_eq_of_ne hσ]

/-- A point lies in the block `B(z)` of the order `i + 1` when its offset from `z` in the units of
`T^{(i)}` lies in `[-h, h]⁴`. -/
lemma blk_of_inM {h i : ℕ} (z : Fin 4 → ℤ) {v : Fin 4 → ℤ} (hv : InM h v) :
    Blk (Lz h) (i + 1) z (z + Lz h ^ i • v) := fun σ => by
  have hD : 0 < Lz h ^ i := pow_pos (Lz_pos h) i
  obtain ⟨a, b⟩ := hv σ
  have a' := mul_le_mul_of_nonneg_left a hD.le
  have b' := mul_le_mul_of_nonneg_left b hD.le
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, pow_succ]
  have hL : Lz h = 2 * h + 1 := rfl
  set D := Lz h ^ i
  rw [hL]
  constructor <;> nlinarith

/-- Conversely, the offset in the units of `T^{(i)}` of a point of the block `B(z)` of the order `i + 1`
lies in `[-h, h]⁴`. -/
lemma inM_of_blk {h i : ℕ} {z x : Fin 4 → ℤ} (hz : Lat (Lz h) i z) (hx : Lat (Lz h) i x)
    (hb : Blk (Lz h) (i + 1) z x) : InM h (qt h i (x - z)) := fun σ => by
  have hd := congrFun (qt_spec (lat_sub (Lz_odd h) (Lz_one h) hx hz)) σ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hd
  obtain ⟨a, b⟩ := hb σ
  rw [hd, pow_succ] at a b
  have hD : 0 < Lz h ^ i := pow_pos (Lz_pos h) i
  have hL : Lz h = 2 * h + 1 := rfl
  set D := Lz h ^ i
  set t := qt h i (x - z) σ
  rw [hL] at a b
  have c1 : D * (2 * t) < D * (2 * h + 2) := by nlinarith
  have c2 : D * (-(2 * h + 2)) < D * (2 * t) := by nlinarith
  have d1 := lt_of_mul_lt_mul_left c1 hD.le
  have d2 := lt_of_mul_lt_mul_left c2 hD.le
  constructor <;> omega

/-- A bond from `B(c̃₋)` to `B(c̃₊)` has the direction of `c̃`. -/
lemma between_dir {h j i : ℕ} {μ : Fin 4} (b : Bd (Lz h) j μ i) (ct : Bd (Lz h) j μ (i + 1))
    (hb : Between (Lz h) j μ i b ct) : b.1.2 = ct.1.2 := by
  obtain ⟨h1, h2⟩ := hb
  have hL := Lz_odd h
  have hL1 := Lz_one h
  have e1 := par_eq_of_blk hL hL1 ct.2.1 h1
  have e2 := par_eq_of_blk hL hL1 (lat_add hL hL1 ct.2.1 (ev_lat hL hL1 _ _)) h2
  have hp : 0 < Lz h ^ (i + 1) := pow_pos (Lz_pos h) _
  rcases par_bond hL hL1 b.2.1 b.1.2 with e | e
  · rw [← e2, ← e1] at e
    have := congrFun e ct.1.2
    simp only [Pi.add_apply, ev, Pi.single_eq_same, add_eq_left] at this
    linarith
  · rw [← e2, ← e1] at e
    by_contra hne
    have := congrFun e ct.1.2
    simp only [Pi.add_apply, ev, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne), add_zero,
      add_eq_left] at this
    linarith

/-! ### Sites on the torus -/

/-- The site of `T^{(i)} = Site n` of a point `x` of `T^{(i)}`, given the site `y` of `c'₋`. -/
def img {n : ℕ} [NeZero n] (h : ℕ) (y : Site n) (i : ℕ) (x : Fin 4 → ℤ) : Site n := ofs y (qt h i x)

/-- The sites of the points of `T^{(i)}` in `𝖡`. -/
def Reg {n : ℕ} [NeZero n] (h j : ℕ) (μ : Fin 4) (i : ℕ) (y : Site n) : Set (Site n) :=
  {p | ∃ x, Lat (Lz h) i x ∧ InB (Lz h) j μ x ∧ p = img h y i x}

lemma img_add {n : ℕ} [NeZero n] {h i : ℕ} (y : Site n) {z : Fin 4 → ℤ} (hz : Lat (Lz h) i z)
    (v : Fin 4 → ℤ) : ofs (img h y i z) v = img h y i (z + Lz h ^ i • v) := by
  unfold img
  rw [ofs_ofs]
  congr 1
  symm
  apply qt_eq
  rw [smul_add, ← qt_spec hz]

/-! ### Lists of coordinates -/

lemma exists_split (ρ : Fin 4) : ∃ P S : List (Fin 4), P ++ ρ :: S = [0, 1, 2, 3] := by
  fin_cases ρ
  · exact ⟨[], [1, 2, 3], rfl⟩
  · exact ⟨[0], [2, 3], rfl⟩
  · exact ⟨[0, 1], [3], rfl⟩
  · exact ⟨[0, 1, 2], [], rfl⟩

lemma split_length {P S : List (Fin 4)} {ρ : Fin 4} (h : P ++ ρ :: S = [0, 1, 2, 3]) :
    P.length ≤ 3 ∧ S.length ≤ 3 := by
  have := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

lemma sum_le {h : ℕ} {m : Fin 4 → ℤ} (hm : InM h m) :
    ∀ S : List (Fin 4), ((S.map fun σ => (m σ).natAbs).sum : ℝ) ≤ S.length * h
  | [] => by simp
  | σ :: S => by
    have h1 := natAbs_le hm σ
    have ih := sum_le hm S
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_succ]
    nlinarith

lemma sum_le_three {h : ℕ} {m : Fin 4 → ℤ} (hm : InM h m) {S : List (Fin 4)} (hS : S.length ≤ 3) :
    ((S.map fun σ => (m σ).natAbs).sum : ℝ) ≤ 3 * h := by
  have h1 := sum_le hm S
  have h2 : (S.length : ℝ) ≤ 3 := by exact_mod_cast hS
  have h3 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  nlinarith

/-! ### The comparison of the bounds -/

/-- The bound of `lem:axial-smallness` for a bond in one block, `(48πh² + 6h)β`, is at most `59L²β`. -/
lemma bound_one {h : ℕ} {β s : ℝ} (hβ : 0 ≤ β) (hs : s ≤ 3 * h) :
    8 * Real.pi * (6 * (h : ℝ) ^ 2 * β) + 2 * (s * β) ≤ 59 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * β := by
  have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have key : 8 * Real.pi * (6 * (h : ℝ) ^ 2) + 2 * s ≤ 59 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_lt_d2.le (sq_nonneg (h : ℝ))]
  have e : 8 * Real.pi * (6 * (h : ℝ) ^ 2 * β) + 2 * (s * β) =
      (8 * Real.pi * (6 * (h : ℝ) ^ 2) + 2 * s) * β := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right key hβ

/-- The bound of `lem:axial-smallness` between the blocks, with `α₁ = 0`, is at most `59L²√Nα`. -/
lemma bound_between {h : ℕ} {a s t : ℝ} (ha : 0 ≤ a) (hs : s ≤ 3 * h) (ht : t ≤ 3 * h) :
    8 * Real.pi * (6 * (h : ℝ) ^ 2 * (Real.sqrt N * a)) +
        2 * (((2 * h + 1 : ℕ) : ℝ) * s * (Real.sqrt N * a)) +
        14 * Real.sqrt N * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * a + 2 * (t * (Real.sqrt N * a)) ≤
      59 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * (Real.sqrt N * a) := by
  have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have key : 8 * Real.pi * (6 * (h : ℝ) ^ 2) + 2 * (((2 * h + 1 : ℕ) : ℝ) * s) +
      14 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 + 2 * t ≤ 59 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_lt_d2.le (sq_nonneg (h : ℝ)),
      mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * h + 1)]
  have e : 8 * Real.pi * (6 * (h : ℝ) ^ 2 * (Real.sqrt N * a)) +
      2 * (((2 * h + 1 : ℕ) : ℝ) * s * (Real.sqrt N * a)) +
      14 * Real.sqrt N * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * a + 2 * (t * (Real.sqrt N * a)) =
      (8 * Real.pi * (6 * (h : ℝ) ^ 2) + 2 * (((2 * h + 1 : ℕ) : ℝ) * s) +
        14 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 + 2 * t) * (Real.sqrt N * a) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right key (mul_nonneg (Real.sqrt_nonneg _) ha)

/-- `6h²·(sα) ≤ (3/2)·(sα₀)` for `α L² = α₀`, `L = 2h + 1`. -/
lemma small_aux {h : ℕ} {s a a0 : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a)
    (haa : a * ((2 * h + 1 : ℕ) : ℝ) ^ 2 = a0) : 6 * (h : ℝ) ^ 2 * (s * a) ≤ 3 / 2 * (s * a0) := by
  rw [← haa]
  push_cast
  have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have : 4 * (h : ℝ) ^ 2 ≤ (2 * h + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hs ha)]

/-! ### `cor:axial-straight` on the lattices -/

/-- `cor:axial-straight` on the lattices `T^{(i)}`, `L = 2h + 1 ≥ 3`. There is `c > 0`, depending on `G`,
`N`, and the index families of `def:average` only, such that the following holds. Let `1 ≤ j`, let
`c' = (c'₋, c'₋ + L^je_μ)`, and let `V i` be gauge fields on the tori `T^{(i)} = Site (nn i)`,
`nn i ≥ 2L`, with the sites `base i` of `c'₋`, such that, for `i < j`:
* `V i` is `G`-valued, and its plaquettes with corners at the sites of the points of `T^{(i)}` in `𝖡` are
  at most `√N·2αL^{-2(j-i)}` in the operator norm, with `0 ≤ 2α ≤ c`;
* its transports from the sites of the points of `T^{(i+1)}` in `𝖡` to the points of their blocks are
  `id` (the axial gauge);
* `V (i + 1)` on a bond `c̃` of `T^{(i+1)}` in `𝖡` is the average `M(V i)(c̃)` (`def:average`).
Then `‖V i(b) - s(b)‖ ≤ 4C_axα`, `C_ax = 59√N`, for `0 ≤ i ≤ j` and every positive bond `b` of `T^{(i)}`
with both ends in `𝖡`, where `s(b) = id` if both ends lie on one side of `𝖡` and `s(b) = V j(c')` otherwise
(`eq:axial-straight`, `C_s ≥ 4C_ax`). -/
theorem axial_straight_lattice (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) (h : ℕ)
    (hh : 1 ≤ h) {ι : Type*} [Fintype ι] {P P' : ι → Type*} [∀ x, Fintype (P x)]
    [∀ x, Fintype (P' x)] :
    ∃ c : ℝ, 0 < c ∧ ∀ (j : ℕ), 1 ≤ j → ∀ (μ : Fin 4) (nn : ℕ → ℕ) [∀ i, NeZero (nn i)],
      (∀ i, i < j → 4 * h + 2 ≤ nn i) →
      ∀ (base : ∀ i, Site (nn i)) (V : ∀ i, Config N (nn i)), (∀ i, i < j → IsGField G (V i)) →
      ∀ α : ℝ, 0 ≤ α → 2 * α ≤ c →
      (∀ i, i < j → PlaqBound (V i) (Reg h j μ i (base i))
        (Real.sqrt N * (2 * α * ((((2 * h + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ^ (j - i)))) →
      ∀ (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)) (ord' : ∀ x, P' x → List (Fin 4)),
      (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) → (∀ x Γ', (ord' x Γ').Perm [0, 1, 2, 3]) →
      (∀ x, InM h (off x)) →
      ∀ {k : ℕ} (_hk : 0 < k) (l : Fin k → List (Fin 4)), (∀ Γ, (l Γ).Perm [0, 1, 2, 3]) →
      ∀ x₀, l x₀ = [0, 1, 2, 3] →
      (∀ i, i < j → ∀ z, Lat (Lz h) (i + 1) z → InB (Lz h) j μ z → ∀ m, InM h m →
        IsMeanOf (fun Γ => (V i).hol (stair (img h (base i) i z) m (l Γ) 0)) x₀ 1) →
      (∀ i, i < j → ∀ ct : Bd (Lz h) j μ (i + 1),
        (V (i + 1)).val ⟨img h (base (i + 1)) (i + 1) ct.1.1, ct.1.2, true⟩ =
          Average.avg G.inChart G.chartLog
            (fun x Γ => (V i).hol (stair (img h (base i) i ct.1.1) (off x) (ord x Γ) 0))
            (fun x => (V i).hol
              (segZ ct.1.2 (ofs (img h (base i) i ct.1.1) (off x)) ((2 * h + 1 : ℕ) : ℤ)))
            (fun x Γ' => (V i).hol (stair (ofs (img h (base i) i ct.1.1)
              (Pi.single ct.1.2 ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) (off x) (ord' x Γ') 0))
            ((V i).hol (segZ ct.1.2 (img h (base i) i ct.1.1) ((2 * h + 1 : ℕ) : ℤ)))) →
      ∀ i, i ≤ j → ∀ b : Bd (Lz h) j μ i,
        ‖(((V i).val ⟨img h (base i) i b.1.1, b.1.2, true⟩ : GLN) : Mat) -
          sval (Lz h) j μ (1 : Mat) (((V j).val ⟨img h (base j) j 0, μ, true⟩ : GLN) : Mat) i b‖ ≤
          4 * (59 * Real.sqrt N) * α := by
  obtain ⟨r₁, hr₁, H1⟩ := axial_one_block_id (N := N) G hG
  obtain ⟨r₂, hr₂, rG, hrG, H2⟩ := axial_between_V0 (N := N) (P := P) (P' := P') G hG
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  set c₀ : ℝ := min (min (r₁ / 2) (r₂ / 2)) (min (1 / 1536) (min (rG / 8) (3 / 7))) with hc₀
  have hc₀0 : 0 < c₀ := lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by norm_num) (lt_min (by linarith) (by norm_num)))
  refine ⟨c₀ / Real.sqrt N, div_pos hc₀0 hsN, ?_⟩
  intro j hj μ nn hnz hn base V hV α hα hαc hplaq off ord ord' hord hord' hoff k hk l hl x₀ hx₀
    haxial hrel i hi b
  have hLo := Lz_odd h
  have hL1 := Lz_one h
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hL2 : (2 : ℝ) ≤ ((Lz h : ℤ) : ℝ) := by rw [Lz_real]; push_cast; linarith
  have hLr : (1 : ℝ) ≤ ((2 * h + 1 : ℕ) : ℝ) := by push_cast; linarith
  refine axial_straight_box hLo hL1 hj μ (59 * Real.sqrt N) α (by positivity) hL2 hα (1 : Mat)
    (fun i b => (((V i).val ⟨img h (base i) i b.1.1, b.1.2, true⟩ : GLN) : Mat)) ?_ i hi b
  intro i hi' b ct hcase
  rw [Lz_real]
  -- the numbers `α₀ = 2αL^{-2(j-i-1)}` and `α = α₀L^{-2}` of the lemma at the order `i + 1`
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ) with hLr_def
  set a0 : ℝ := 2 * α * (Lr ^ 2)⁻¹ ^ (j - i - 1) with ha0_def
  set alat : ℝ := 2 * α * (Lr ^ 2)⁻¹ ^ (j - i) with halat_def
  have hLr0 : 0 < Lr := by linarith
  have hpow : (Lr ^ 2)⁻¹ ^ (j - i) = (Lr ^ 2)⁻¹ ^ (j - i - 1) * (Lr ^ 2)⁻¹ := by
    rw [← pow_succ]; congr 1; omega
  have haa : alat * Lr ^ 2 = a0 := by
    have hne : Lr ^ 2 ≠ 0 := by positivity
    rw [halat_def, ha0_def, hpow]
    field_simp
  have ha0 : 0 ≤ a0 := by positivity
  have halat : 0 ≤ alat := by positivity
  have ha0c : a0 ≤ 2 * α := by
    have hinv : (Lr ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    have := pow_le_one₀ (n := j - i - 1) (inv_nonneg.2 (sq_nonneg Lr)) hinv
    nlinarith
  have hq : Real.sqrt N * a0 ≤ c₀ := by
    have := (le_div_iff₀ hsN).1 (ha0c.trans hαc)
    linarith
  have hq1 : Real.sqrt N * a0 ≤ r₁ / 2 := hq.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hq2 : Real.sqrt N * a0 ≤ r₂ / 2 := hq.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hq3 : Real.sqrt N * a0 ≤ 1 / 1536 := hq.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hq4 : Real.sqrt N * a0 ≤ rG / 8 :=
    hq.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hq5 : Real.sqrt N * a0 ≤ 3 / 7 :=
    hq.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsm := small_aux (h := h) (Real.sqrt_nonneg (N : ℝ)) halat haa
  have hX0 : 0 ≤ 6 * (h : ℝ) ^ 2 * (Real.sqrt N * alat) := by positivity
  have s1 : ∀ r : ℝ, Real.sqrt N * a0 ≤ r / 2 → 6 * (h : ℝ) ^ 2 * (Real.sqrt N * alat) ≤ r :=
    fun r hr => by nlinarith
  have s2 : 512 * (Real.pi / 2 * (6 * (h : ℝ) ^ 2 * (Real.sqrt N * alat))) ≤ 1 := by
    have hX : 6 * (h : ℝ) ^ 2 * (Real.sqrt N * alat) ≤ 1 / 1024 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four hX0,
      mul_le_mul_of_nonneg_left hX Real.pi_pos.le]
  have hbound : 59 * Lr ^ 2 * (Real.sqrt N * alat) = 59 * Real.sqrt N * a0 := by
    rw [← haa]; ring
  have hbplat : Lat (Lz h) i (b.1.1 + ev (Lz h) i b.1.2) := lat_add hLo hL1 b.2.1 (ev_lat hLo hL1 _ _)
  by_cases h1 : OneBlk (Lz h) j μ i b ct
  · -- a bond in one block: `V₀ = id`
    simp only [h1, ↓reduceIte]
    obtain ⟨z, hz, hb1, hb2⟩ := h1
    have hzl : Lat (Lz h) (i + 1) z := by
      rcases hz with rfl | rfl
      · exact ct.2.1
      · exact lat_add hLo hL1 ct.2.1 (ev_lat hLo hL1 _ _)
    have hzB : InB (Lz h) j μ z := by
      rcases hz with rfl | rfl
      · exact ct.2.2.1
      · exact ct.2.2.2
    have hzi := lat_le hzl
    have hm : InM h (qt h i (b.1.1 - z)) := inM_of_blk hzi b.2.1 hb1
    have hbm : b.1.1 = z + Lz h ^ i • qt h i (b.1.1 - z) := by
      rw [← qt_spec (lat_sub hLo hL1 b.2.1 hzi)]; abel
    generalize qt h i (b.1.1 - z) = m at hm hbm
    have hq1' : qt h i (b.1.1 + ev (Lz h) i b.1.2 - z) = m + Pi.single b.1.2 1 :=
      qt_eq (by rw [hbm, ev_eq_smul, smul_add]; abel)
    have hm1 : InM h (m + Pi.single b.1.2 1) := hq1' ▸ inM_of_blk hzi hbplat hb2
    obtain ⟨Pl, S, hPS⟩ := exists_split b.1.2
    have hreg : boxR (img h (base i) i z) (loB h) (fun _ => (h : ℤ)) ⊆ Reg h j μ i (base i) := by
      rintro p ⟨v, hv, rfl⟩
      have hvM : InM h v := fun σ => ⟨(hv σ).1, (hv σ).2⟩
      exact ⟨z + Lz h ^ i • v, lat_add hLo hL1 hzi (lat_smul v),
        blk_sub_B hLo hL1 hi' hzl hzB (blk_of_inM z hvM), img_add (base i) hzi v⟩
    have hbox : ∀ v, InM h v → InBox (loB h) (fun _ => (h : ℤ)) v := fun v hv σ =>
      ⟨(hv σ).1, (hv σ).2⟩
    have H := H1 (V i) (hV i hi') (img h (base i) i z) (loB h) (fun _ => (h : ℤ))
      (Real.sqrt N * alat) (by positivity) (plaqBound_mono hreg (hplaq i hi')) m Pl S b.1.2 hPS
      (hbox 0 (inM_zero h)) (hbox m hm) (hbox _ hm1) (h : ℝ) (natAbs_le hm) (natAbs_le hm1)
      (s1 r₁ hq1) s2 hk l hl x₀ hx₀ (haxial i hi' z hzl hzB m hm) (haxial i hi' z hzl hzB _ hm1)
    rw [img_add (base i) hzi m, ← hbm] at H
    refine H.trans ?_
    have := bound_one (h := h) (by positivity : 0 ≤ Real.sqrt N * alat)
      (sum_le_three hm (split_length hPS).2)
    rw [hbound] at this
    exact this
  · -- a bond between the blocks: `V₀ = W = M(V)(c̃)` between them
    simp only [h1, ↓reduceIte]
    have h2 := hcase.resolve_left h1
    have hdir := between_dir b ct h2
    obtain ⟨hb1, hb2⟩ := h2
    have hcli := lat_le ct.2.1
    have hcpl : Lat (Lz h) (i + 1) (ct.1.1 + ev (Lz h) (i + 1) ct.1.2) :=
      lat_add hLo hL1 ct.2.1 (ev_lat hLo hL1 _ _)
    have hcpli := lat_le hcpl
    have hm : InM h (qt h i (b.1.1 - ct.1.1)) := inM_of_blk hcli b.2.1 hb1
    have hbm : b.1.1 = ct.1.1 + Lz h ^ i • qt h i (b.1.1 - ct.1.1) := by
      rw [← qt_spec (lat_sub hLo hL1 b.2.1 hcli)]; abel
    have hn' : InM h (qt h i (b.1.1 + ev (Lz h) i b.1.2 - (ct.1.1 + ev (Lz h) (i + 1) ct.1.2))) :=
      inM_of_blk hcpli hbplat hb2
    have hbn : b.1.1 + ev (Lz h) i b.1.2 = ct.1.1 + ev (Lz h) (i + 1) ct.1.2 +
        Lz h ^ i • qt h i (b.1.1 + ev (Lz h) i b.1.2 - (ct.1.1 + ev (Lz h) (i + 1) ct.1.2)) := by
      rw [← qt_spec (lat_sub hLo hL1 hbplat hcpli)]; abel
    generalize qt h i (b.1.1 + ev (Lz h) i b.1.2 - (ct.1.1 + ev (Lz h) (i + 1) ct.1.2)) = n'
      at hn' hbn
    generalize qt h i (b.1.1 - ct.1.1) = m at hm hbm
    -- `n' + Le_μ = m + e_μ`
    have hz : n' + (Pi.single ct.1.2 ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) = m + Pi.single ct.1.2 1 := by
      have e1 := hbn
      rw [ev_succ_eq] at e1
      have e2 : b.1.1 + ev (Lz h) i b.1.2 = ct.1.1 + Lz h ^ i • m +
          Lz h ^ i • (Pi.single ct.1.2 1 : Fin 4 → ℤ) := by
        rw [hbm, ev_eq_smul, hdir]
      have e3 := e1.symm.trans e2
      rw [add_assoc, add_assoc] at e3
      have e4 := add_left_cancel e3
      apply smul_right_injective (Fin 4 → ℤ) (pow_pos (Lz_pos h) i).ne'
      simp only [smul_add]
      rw [add_comm]
      exact e4
    obtain ⟨Pre, Post, hPS⟩ := exists_split ct.1.2
    -- the box `B(c̃₋) ∪ B(c̃₊)` lies in `𝖡`
    have hreg : boxR (img h (base i) i ct.1.1) (loB h) (hiB h ct.1.2) ⊆ Reg h j μ i (base i) := by
      rintro p ⟨v, hv, rfl⟩
      refine ⟨ct.1.1 + Lz h ^ i • v, lat_add hLo hL1 hcli (lat_smul v), ?_, img_add (base i) hcli v⟩
      unfold loB hiB at hv
      by_cases hvμ : v ct.1.2 ≤ h
      · have hvM : InM h v := fun σ => by
          have := hv σ
          beta_reduce at this
          split_ifs at this with hσ
          · subst hσ; exact ⟨this.1, hvμ⟩
          · exact this
        exact blocks_sub_B hLo hL1 hi' ct _ (Or.inl (blk_of_inM _ hvM))
      · have hvM : InM h (v - (Pi.single ct.1.2 ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) := fun σ => by
          have := hv σ
          beta_reduce at this
          by_cases hσ : σ = ct.1.2
          · subst hσ
            simp only [↓reduceIte] at this
            simp only [Pi.sub_apply, Pi.single_eq_same]
            push_cast
            constructor <;> omega
          · simp only [hσ, ↓reduceIte] at this
            simp only [Pi.sub_apply, Pi.single_eq_of_ne hσ, sub_zero]
            exact this
        have e : ct.1.1 + Lz h ^ i • v = ct.1.1 + ev (Lz h) (i + 1) ct.1.2 +
            Lz h ^ i • (v - (Pi.single ct.1.2 ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ)) := by
          rw [ev_succ_eq, smul_sub]; abel
        rw [e]
        exact blocks_sub_B hLo hL1 hi' ct _ (Or.inr (blk_of_inM _ hvM))
    have himgp : img h (base i) i (ct.1.1 + ev (Lz h) (i + 1) ct.1.2) =
        ofs (img h (base i) i ct.1.1) (Pi.single ct.1.2 ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) := by
      rw [ev_succ_eq, ← img_add (base i) hcli]
    have hT' := haxial i hi' _ hcpl ct.2.2.2 n' hn'
    rw [himgp] at hT'
    have hr8 : alat ≤ rG / (8 * Real.sqrt N * Lr ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : alat * (8 * Real.sqrt N * Lr ^ 2) = 8 * (Real.sqrt N * (alat * Lr ^ 2)) := by ring
      rw [this, haa]
      linarith
    have hr7 : 7 * Real.sqrt N * Lr ^ 2 * alat ≤ Real.pi := by
      have : 7 * Real.sqrt N * Lr ^ 2 * alat = 7 * (Real.sqrt N * (alat * Lr ^ 2)) := by ring
      rw [this, haa]
      linarith [Real.pi_gt_three]
    have H := H2 (V i) (hV i hi') (img h (base i) i ct.1.1) ct.1.2 h (hn i hi') alat halat
      (plaqBound_mono hreg (hplaq i hi')) hr8 hr7 (s1 r₂ hq2) s2 off ord ord' hord hord' hoff
      m n' Pre Post hPS hz hm hn' hk l hl x₀ hx₀ (haxial i hi' _ ct.2.1 ct.2.2.1 m hm) hT'
    rw [← hrel i hi' ct, img_add (base i) hcli m, ← hbm] at H
    rw [hdir]
    refine H.trans ?_
    have := bound_between (N := N) (h := h) halat (sum_le_three hn' (split_length hPS).1)
      (sum_le_three hm (split_length hPS).2)
    rw [hbound] at this
    exact this

end AxialStraightLattice

end CoreLean

end
