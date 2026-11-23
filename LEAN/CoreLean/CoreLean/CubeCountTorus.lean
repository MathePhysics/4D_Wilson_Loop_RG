/-
`lem:cube-count` of BALABAN_CORE.tex on the torus.

The torus is `𝕋 = (ℝ / sNℤ)⁴` with the distance `|·|_∞` (the product of the circles), and the grid of
side `s` (`def:grids`) is the family of the closed cubes `{z | |z - c|_∞ ≤ s/2}`, `c ∈ (sℤ/sNℤ)⁴`, which
we index by `c : Fin 4 → ZMod N`. A segment of `𝕋` is the image of a segment `{a + θv | θ ∈ [0, 1]}` of
`ℝ⁴`, with the Euclidean length `|v|₂`; points are the segments with `v = 0`. The linear size
`d(X) = d(X; ∅)` of `eq:contracted-size` is `s⁻¹` times the infimum of the total Euclidean length of the
finite families of segments in `X` whose union meets every cube of `X` and is connected. (The core
takes the one-dimensional measure of the union; a finite union of segments is a union of segments
which meet at most at end points, so the two infima agree; we use the sum of the lengths.)

Results: `card_le_size` (`#(X) ≤ 2⁸(2 + d(X))`), `dist_le_size` (`|z - z'|_∞ ≤ s(d(X) + 2)` for
`z, z' ∈ X`, which gives the core's Euclidean bound `s(2d(X) + 4)` since `|·|₂ ≤ 2|·|_∞` in four
dimensions), and `domain_sum_torus` (`eq:domain-sum`).
-/
import CoreLean.Tour
import CoreLean.CubeCount
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set Real

noncomputable section

namespace CoreLean

variable {s : ℝ} {N : ℕ} [NeZero N]

/-! ### The torus and the grid -/

/-- The torus `(ℝ / sNℤ)⁴` with the distance `|·|_∞`. -/
abbrev Torus (s : ℝ) (N : ℕ) := Fin 4 → AddCircle (s * N)

/-- The projection `ℝ⁴ → 𝕋`. -/
def proj (s : ℝ) (N : ℕ) (x : Fin 4 → ℝ) : Torus s N := fun ν => (x ν : AddCircle (s * N))

/-- The representative `s · c` in `[0, sN)⁴` of the centre of the cube `c`. -/
def lift (s : ℝ) (c : Fin 4 → ZMod N) : Fin 4 → ℝ := fun ν => s * ((c ν).val : ℝ)

/-- The centre of the cube `c`. -/
def centre (s : ℝ) (N : ℕ) [NeZero N] (c : Fin 4 → ZMod N) : Torus s N := proj s N (lift s c)

/-- The cube `{z | |z - c|_∞ ≤ s/2}` of the grid of side `s`. -/
def cube (s : ℝ) (N : ℕ) [NeZero N] (c : Fin 4 → ZMod N) : Set (Torus s N) :=
  Metric.closedBall (centre s N c) (s / 2)

/-- The union of the cubes of `X`. -/
def cubes (s : ℝ) (N : ℕ) [NeZero N] (X : Finset (Fin 4 → ZMod N)) : Set (Torus s N) :=
  ⋃ c ∈ X, cube s N c

omit [NeZero N] in
lemma dist_proj_le (x y : Fin 4 → ℝ) : dist (proj s N x) (proj s N y) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).2 fun ν => ?_
  simp only [proj]
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  calc ‖((x ν - y ν : ℝ) : AddCircle (s * N))‖ ≤ ‖x ν - y ν‖ := QuotientAddGroup.norm_mk_le_norm
    _ = dist (x ν) (y ν) := (dist_eq_norm _ _).symm
    _ ≤ dist x y := dist_le_pi_dist x y ν

omit [NeZero N] in
lemma lipschitzWith_proj : LipschitzWith 1 (proj s N) :=
  LipschitzWith.of_dist_le_mul fun x y => by simpa using dist_proj_le x y

/-- Integer multiples of `s` project to the centres of the cubes of their classes. -/
lemma proj_intCast (k : Fin 4 → ℤ) :
    proj s N (fun ν => s * (k ν : ℝ)) = centre s N (fun ν => (k ν : ZMod N)) := by
  funext ν
  simp only [centre, proj, lift]
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨k ν / N, ?_⟩
  have h := ZMod.val_intCast (n := N) (k ν)
  have h2 : (((k ν : ZMod N).val : ℕ) : ℝ) = ((k ν % N : ℤ) : ℝ) := by rw [← h]; norm_cast
  have h3 : ((k ν : ℤ) : ℝ) = ((k ν % N : ℤ) : ℝ) + N * ((k ν / N : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv (k ν) N).symm
  rw [zsmul_eq_mul, h2, h3]
  ring

lemma proj_lift_add (c : Fin 4 → ZMod N) (μ : Fin 4) :
    proj s N (lift s c + s • Pi.single μ (1 : ℝ)) = centre s N (c + Pi.single μ 1) := by
  have hk : lift s c + s • Pi.single μ (1 : ℝ) =
      fun ν => s * ((((c ν).val : ℤ) + (Pi.single μ (1 : ℤ) : Fin 4 → ℤ) ν : ℤ) : ℝ) := by
    funext ν
    simp only [lift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : ν = μ
    · subst h; simp; ring
    · simp [Pi.single_apply, h]
  rw [hk, proj_intCast]
  congr 1
  funext ν
  by_cases h : ν = μ
  · subst h; simp
  · simp [Pi.single_apply, h]

/-! ### The cubes near a point -/

/-- At most four cubes of a circle of side `s` have their centre within `3s/2` of a point. -/
lemma card_near_coord (hs : 0 < s) (q : AddCircle (s * N)) :
    (Finset.univ.filter fun k : ZMod N =>
      dist ((s * (k.val : ℝ) : ℝ) : AddCircle (s * N)) q ≤ 3 * s / 2).card ≤ 4 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  set a := ⌈x / s - 3 / 2⌉
  set b := ⌊x / s + 3 / 2⌋
  have hsub : (Finset.univ.filter fun k : ZMod N =>
      dist ((s * (k.val : ℝ) : ℝ) : AddCircle (s * N)) (x : AddCircle (s * N)) ≤ 3 * s / 2) ⊆
      (Finset.Icc a b).image (Int.cast : ℤ → ZMod N) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hd := hk.2
    rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hd
    set m := round ((s * N)⁻¹ * (s * (k.val : ℝ) - x))
    set j : ℤ := (k.val : ℤ) - m * N
    have hj : |s * (j : ℝ) - x| ≤ 3 * s / 2 := by
      have : s * (j : ℝ) - x = s * (k.val : ℝ) - x - m * (s * N) := by
        simp only [j]; push_cast; ring
      rw [this]; exact hd
    rw [abs_le] at hj
    refine Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨?_, ?_⟩, ?_⟩
    · rw [Int.ceil_le, sub_le_iff_le_add, div_le_iff₀ hs]
      nlinarith
    · rw [Int.le_floor, ← sub_le_iff_le_add, le_div_iff₀ hs]
      nlinarith
    · simp only [j]; push_cast; simp
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Int.card_Icc]
  have ha : x / s - 3 / 2 ≤ a := Int.le_ceil _
  have hb : (b : ℝ) ≤ x / s + 3 / 2 := Int.floor_le _
  have hab : ((b - a : ℤ) : ℝ) ≤ 3 := by push_cast; linarith
  have : b - a ≤ 3 := by exact_mod_cast hab
  omega

/-- The cubes whose centre is within `3s/2` of `q`. -/
noncomputable def near (s : ℝ) (N : ℕ) [NeZero N] (q : Torus s N) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun c => dist (centre s N c) q ≤ 3 * s / 2

/-- A box `{z | |z - q|_∞ ≤ s}` meets at most `4⁴ = 2⁸` cubes of the grid. -/
lemma card_near_le (hs : 0 < s) (q : Torus s N) : (near s N q).card ≤ 2 ^ 8 := by
  have hsub : near s N q ⊆ Fintype.piFinset fun ν => Finset.univ.filter fun k : ZMod N =>
      dist ((s * (k.val : ℝ) : ℝ) : AddCircle (s * N)) (q ν) ≤ 3 * s / 2 := by
    intro c hc
    rw [Fintype.mem_piFinset]
    intro ν
    simp only [near, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (dist_le_pi_dist _ _ ν).trans hc
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ ν, _ ≤ 4 ^ (Finset.univ : Finset (Fin 4)).card :=
        Finset.prod_le_pow_card _ _ _ fun ν _ => card_near_coord hs (q ν)
    _ = 2 ^ 8 := by simp

/-- Every time of a path on `[0, T]` is within `s` of one of the `⌈T/2s⌉ + 1` times `min(2is, T)`. -/
lemma exists_node {E : Type*} [MetricSpace E] {Γ : ℝ → E} (hΓ : LipschitzWith 1 Γ) {T : ℝ}
    (hs : 0 < s) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ i ∈ Finset.range (⌈T / (2 * s)⌉₊ + 1), dist (Γ t) (Γ (min (2 * i * s) T)) ≤ s := by
  set y := (t + s) / (2 * s)
  have hy0 : 0 ≤ y := div_nonneg (by linarith [ht.1]) (by linarith)
  set i := ⌊y⌋₊
  have hfl : (i : ℝ) ≤ y := Nat.floor_le hy0
  have hlt : y < i + 1 := Nat.lt_floor_add_one y
  have h1 : 2 * i * s ≤ t + s := by
    have := (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * s)).1 hfl; linarith
  have h2 : t + s < 2 * (i + 1) * s := by
    have := (div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * s)).1 hlt; linarith
  refine ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), ?_⟩
  · by_contra hc
    push_neg at hc
    have hc' : (⌈T / (2 * s)⌉₊ : ℝ) + 1 ≤ i := by exact_mod_cast hc
    have hce := Nat.le_ceil (T / (2 * s))
    have : y ≤ T / (2 * s) + 1 / 2 := by
      simp only [y]; rw [add_div, show s / (2 * s) = 1 / 2 by field_simp]
      linarith [div_le_div_of_nonneg_right ht.2 (by linarith : (0 : ℝ) ≤ 2 * s)]
    linarith
  · refine (dist_le_of_lip hΓ _ _).trans ?_
    rcases le_total (2 * i * s) T with h | h
    · rw [min_eq_left h, abs_le]; constructor <;> nlinarith
    · rw [min_eq_right h, abs_of_nonpos (by linarith [ht.2])]; nlinarith

/-! ### Segments and the linear size -/

/-- The segment `{π(a + θv) | θ ∈ [0, 1]}` of the torus. -/
def segSet (s : ℝ) (N : ℕ) (σ : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : Set (Torus s N) :=
  (fun θ : ℝ => proj s N (σ.1 + θ • σ.2)) '' Icc 0 1

/-- The Euclidean length `|v|₂`. -/
noncomputable def eu (v : Fin 4 → ℝ) : ℝ := Real.sqrt (∑ ν, v ν ^ 2)

lemma eu_nonneg (v : Fin 4 → ℝ) : 0 ≤ eu v := Real.sqrt_nonneg _

lemma norm_le_eu (v : Fin 4 → ℝ) : ‖v‖ ≤ eu v :=
  (pi_norm_le_iff_of_nonneg (eu_nonneg v)).2 fun ν => by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun ν => v ν ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ ν))

/-- The segment parametrised by its `ℓ^∞`-length. -/
noncomputable def segCurve (s : ℝ) (N : ℕ) (σ : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : Curve (Torus s N) where
  c t := proj s N (σ.1 + t • (‖σ.2‖⁻¹ • σ.2))
  len := ‖σ.2‖
  lip := by
    refine LipschitzWith.of_dist_le_mul fun t t' => ?_
    refine (dist_proj_le _ _).trans ?_
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, NNReal.coe_one, one_mul,
      Real.dist_eq, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [norm_smul, norm_inv, norm_norm]
    by_cases hv : σ.2 = 0
    · simp [hv]
    · rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  len_nonneg := norm_nonneg _

omit [NeZero N] in
lemma segSet_eq (σ : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : segSet s N σ = (segCurve s N σ).img := by
  ext x
  simp only [segSet, Curve.img, segCurve, mem_image, mem_Icc]
  by_cases hv : σ.2 = 0
  · simp only [hv, smul_zero, add_zero, norm_zero]
    constructor
    · rintro ⟨-, -, rfl⟩; exact ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩
    · rintro ⟨-, -, rfl⟩; exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  · have hL : 0 < ‖σ.2‖ := norm_pos_iff.2 hv
    constructor
    · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
      refine ⟨θ * ‖σ.2‖, ⟨by positivity, by nlinarith⟩, ?_⟩
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hL.ne', mul_one]
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      refine ⟨t / ‖σ.2‖, ⟨by positivity, (div_le_one hL).2 h1⟩, ?_⟩
      rw [smul_smul, div_eq_mul_inv]

/-- The families admissible in `eq:contracted-size` for `D = ∅`. -/
def Admissible (s : ℝ) (N : ℕ) [NeZero N] (X : Finset (Fin 4 → ZMod N))
    (S : Finset ((Fin 4 → ℝ) × (Fin 4 → ℝ))) : Prop :=
  (∀ σ ∈ S, segSet s N σ ⊆ cubes s N X) ∧
  (∀ c ∈ X, ∃ σ ∈ S, (segSet s N σ ∩ cube s N c).Nonempty) ∧
  IsPreconnected (⋃ σ ∈ S, segSet s N σ)

/-- The linear size `d(X)`. -/
noncomputable def size (s : ℝ) (N : ℕ) [NeZero N] (X : Finset (Fin 4 → ZMod N)) : ℝ :=
  s⁻¹ * sInf ((fun S => ∑ σ ∈ S, eu σ.2) '' {S | Admissible s N X S})

lemma size_nonneg (hs : 0 < s) (X : Finset (Fin 4 → ZMod N)) : 0 ≤ size s N X := by
  refine mul_nonneg (inv_nonneg.2 hs.le) (Real.sInf_nonneg ?_)
  rintro _ ⟨S, -, rfl⟩
  exact Finset.sum_nonneg fun σ _ => eu_nonneg _

/-! ### The bounds for one admissible family -/

theorem admissible_bounds (hs : 0 < s) {X : Finset (Fin 4 → ZMod N)}
    {S : Finset ((Fin 4 → ℝ) × (Fin 4 → ℝ))} (hS : Admissible s N X S) :
    (X.card : ℝ) ≤ 2 ^ 8 * (2 + (∑ σ ∈ S, ‖σ.2‖) / s) ∧
      ∀ z ∈ cubes s N X, ∀ z' ∈ cubes s N X, dist z z' ≤ 2 * s + ∑ σ ∈ S, ‖σ.2‖ := by
  classical
  have hL0 : 0 ≤ ∑ σ ∈ S, ‖σ.2‖ := Finset.sum_nonneg fun σ _ => norm_nonneg _
  rcases X.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · refine ⟨by simp; positivity, fun z hz => ?_⟩
    simp [cubes] at hz
  obtain ⟨σ0, hσ0, -⟩ := hS.2.1 c0 hc0
  have hconn : IsPreconnected (⋃ σ ∈ S, (segCurve s N σ).img) := by
    simpa only [segSet_eq] using hS.2.2
  obtain ⟨Γ, hΓ⟩ := exists_tour S (segCurve s N) ⟨σ0, hσ0⟩ hconn
  set T := 2 * ∑ σ ∈ S, (segCurve s N σ).len
  have hT : T = 2 * ∑ σ ∈ S, ‖σ.2‖ := rfl
  -- every cube of `X` contains a point of the union, which lies on the tour
  have hpt : ∀ c ∈ X, ∃ g ∈ ⋃ σ ∈ S, (segCurve s N σ).img, g ∈ cube s N c := fun c hc => by
    obtain ⟨σ, hσ, g, hg1, hg2⟩ := hS.2.1 c hc
    exact ⟨g, mem_biUnion hσ (by rw [← segSet_eq]; exact hg1), hg2⟩
  constructor
  · -- the cubes of `X` lie near the `⌈T/2s⌉ + 1` points `Γ(min(2is, T))`
    have hsub : X ⊆ (Finset.range (⌈T / (2 * s)⌉₊ + 1)).biUnion
        fun i => near s N (Γ (min (2 * i * s) T)) := by
      intro c hc
      obtain ⟨g, hg, hgc⟩ := hpt c hc
      obtain ⟨t, ht, rfl⟩ := hΓ.2.2 hg
      obtain ⟨i, hi, hdi⟩ := exists_node hΓ.1 hs ht
      refine Finset.mem_biUnion.2 ⟨i, hi, ?_⟩
      simp only [near, Finset.mem_filter, Finset.mem_univ, true_and]
      have := Metric.mem_closedBall.1 hgc
      calc dist (centre s N c) (Γ (min (2 * i * s) T))
          ≤ dist (centre s N c) (Γ t) + dist (Γ t) (Γ (min (2 * i * s) T)) := dist_triangle _ _ _
        _ ≤ s / 2 + s := add_le_add (by rwa [dist_comm]) hdi
        _ = 3 * s / 2 := by ring
    have hcard : X.card ≤ (⌈T / (2 * s)⌉₊ + 1) * 2 ^ 8 := by
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
      refine (Finset.sum_le_sum fun i _ => card_near_le hs _).trans ?_
      simp
    have hce : (⌈T / (2 * s)⌉₊ : ℝ) < T / (2 * s) + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (by rw [hT]; positivity) (by positivity))
    have hTs : T / (2 * s) = (∑ σ ∈ S, ‖σ.2‖) / s := by
      rw [hT]; field_simp
    calc (X.card : ℝ) ≤ ((⌈T / (2 * s)⌉₊ + 1) * 2 ^ 8 : ℕ) := by exact_mod_cast hcard
      _ ≤ 2 ^ 8 * (2 + (∑ σ ∈ S, ‖σ.2‖) / s) := by
          push_cast; rw [← hTs]; nlinarith
  · intro z hz z' hz'
    simp only [cubes, mem_iUnion] at hz hz'
    obtain ⟨c, hc, hzc⟩ := hz
    obtain ⟨c', hc', hzc'⟩ := hz'
    obtain ⟨g, hg, hgc⟩ := hpt c hc
    obtain ⟨g', hg', hgc'⟩ := hpt c' hc'
    have h1 := Metric.mem_closedBall.1 hzc
    have h2 := Metric.mem_closedBall.1 hgc
    have h3 := Metric.mem_closedBall.1 hzc'
    have h4 := Metric.mem_closedBall.1 hgc'
    have hgg := hΓ.dist_le hg hg'
    calc dist z z' ≤ dist z (centre s N c) + dist (centre s N c) g + dist g g' +
          dist g' (centre s N c') + dist (centre s N c') z' := by
          linarith [dist_triangle z (centre s N c) g, dist_triangle z g g',
            dist_triangle z g' z', dist_triangle g' (centre s N c') z']
      _ ≤ s / 2 + s / 2 + T / 2 + s / 2 + s / 2 := by
          rw [dist_comm (centre s N c) g, dist_comm (centre s N c') z']
          linarith
      _ = 2 * s + ∑ σ ∈ S, ‖σ.2‖ := by rw [hT]; ring

/-! ### Existence of admissible families -/

/-- The point at the centre of a cube. -/
def hub (s : ℝ) (c : Fin 4 → ZMod N) : (Fin 4 → ℝ) × (Fin 4 → ℝ) := (lift s c, 0)

/-- The segment from the centre of `c` to the centre of `c + e_μ`. -/
def edge (s : ℝ) (c : Fin 4 → ZMod N) (μ : Fin 4) : (Fin 4 → ℝ) × (Fin 4 → ℝ) :=
  (lift s c, s • Pi.single μ 1)

lemma segSet_hub (c : Fin 4 → ZMod N) : segSet s N (hub s c) = {centre s N c} := by
  ext x
  simp only [segSet, hub, smul_zero, add_zero, mem_image, mem_singleton_iff]
  constructor
  · rintro ⟨-, -, rfl⟩; rfl
  · rintro rfl; exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

lemma centre_mem_edge (c : Fin 4 → ZMod N) (μ : Fin 4) : centre s N c ∈ segSet s N (edge s c μ) :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [edge, centre]⟩

lemma centre_add_mem_edge (c : Fin 4 → ZMod N) (μ : Fin 4) :
    centre s N (c + Pi.single μ 1) ∈ segSet s N (edge s c μ) :=
  ⟨1, ⟨zero_le_one, le_rfl⟩, by simp only [edge, one_smul]; exact proj_lift_add c μ⟩

lemma norm_smul_single_le (hs : 0 < s) (r : ℝ) (μ : Fin 4) :
    ‖r • s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖ ≤ |r| * s := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ν => ?_
  by_cases h : ν = μ
  · subst h; simp [abs_of_pos hs]
  · simp [Pi.single_apply, h]; positivity

lemma edge_subset (hs : 0 < s) {X : Finset (Fin 4 → ZMod N)} {c : Fin 4 → ZMod N} {μ : Fin 4}
    (hc : c ∈ X) (hc' : c + Pi.single μ 1 ∈ X) : segSet s N (edge s c μ) ⊆ cubes s N X := by
  rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
  simp only [edge]
  rcases le_total θ (1 / 2) with h | h
  · refine mem_biUnion hc (Metric.mem_closedBall.2 ?_)
    refine (dist_proj_le _ _).trans ?_
    rw [dist_eq_norm, add_sub_cancel_left]
    refine (norm_smul_single_le hs θ μ).trans ?_
    rw [abs_of_nonneg h0]; nlinarith
  · refine mem_biUnion hc' (Metric.mem_closedBall.2 ?_)
    rw [← proj_lift_add]
    refine (dist_proj_le _ _).trans ?_
    rw [dist_eq_norm, add_sub_add_left_eq_sub,
      show θ • s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) - s • Pi.single μ 1 =
        (θ - 1) • s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) by rw [sub_smul, one_smul]]
    refine (norm_smul_single_le hs (θ - 1) μ).trans ?_
    rw [abs_of_nonpos (by linarith)]; nlinarith

lemma isPreconnected_segSet (σ : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : IsPreconnected (segSet s N σ) :=
  isPreconnected_Icc.image _ (lipschitzWith_proj.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))).continuousOn

/-- A connected union of cubes has an admissible family: the centres of its cubes and the segments
joining the centres of cubes which share a wall. -/
theorem exists_admissible (hs : 0 < s) {X : Finset (Fin 4 → ZMod N)}
    (hX : ((wallGraph (ZMod N)).induce (X : Set (Fin 4 → ZMod N))).Connected) :
    ∃ S, Admissible s N X S := by
  classical
  set E := (X ×ˢ (Finset.univ : Finset (Fin 4))).filter fun p => p.1 + Pi.single p.2 1 ∈ X
    with hE
  set S0 := X.image (hub s) ∪ E.image (fun p => edge s p.1 p.2) with hS0
  have hhubS : ∀ c ∈ X, hub s c ∈ S0 := fun c hc =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
  have hedgeS : ∀ c ∈ X, ∀ μ, c + Pi.single μ 1 ∈ X → edge s c μ ∈ S0 := fun c hc μ hc' =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨(c, μ), by
      simp only [hE, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨hc, hc'⟩, rfl⟩)
  have hcube : ∀ c, centre s N c ∈ cube s N c := fun c =>
    Metric.mem_closedBall_self (by linarith)
  refine ⟨S0, ?_, ?_, ?_⟩
  · intro σ hσ
    rcases Finset.mem_union.1 hσ with h | h
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
      rw [segSet_hub]
      rintro _ rfl
      exact mem_biUnion hc (hcube c)
    · obtain ⟨⟨c, μ⟩, hp, rfl⟩ := Finset.mem_image.1 h
      simp only [hE, Finset.mem_filter, Finset.mem_product] at hp
      exact edge_subset hs hp.1.1 hp.2
  · intro c hc
    exact ⟨hub s c, hhubS c hc, centre s N c, by rw [segSet_hub]; rfl, hcube c⟩
  · rw [← Finset.set_biUnion_coe]
    refine IsPreconnected.biUnion_of_reflTransGen (fun σ _ => isPreconnected_segSet σ) ?_
    set R := fun σ τ : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      (segSet s N σ ∩ segSet s N τ).Nonempty ∧ σ ∈ (S0 : Set _) with hR
    have hhub_mem : ∀ c, centre s N c ∈ segSet s N (hub s c) := fun c => by
      rw [segSet_hub]; rfl
    -- the centres of adjacent cubes are joined
    have hadj : ∀ a b : (X : Set (Fin 4 → ZMod N)),
        ((wallGraph (ZMod N)).induce (X : Set (Fin 4 → ZMod N))).Adj a b →
        Relation.ReflTransGen R (hub s a.1) (hub s b.1) := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have hab' : (wallGraph (ZMod N)).Adj a b := hab
      obtain ⟨-, ⟨μ, t⟩, hbt⟩ := hab'
      cases t
      · -- `b = a - e_μ`, so `a = b + e_μ`
        have hab2 : b + Pi.single μ 1 = a := by rw [hbt]; simp [wallNbr]
        have hb' : b + Pi.single μ 1 ∈ X := by rw [hab2]; exact ha
        refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single (b := edge s b μ)
          ⟨⟨centre s N a, hhub_mem a, hab2 ▸ centre_add_mem_edge b μ⟩, hhubS a ha⟩) ?_
        exact ⟨⟨centre s N b, centre_mem_edge b μ, hhub_mem b⟩, hedgeS b hb μ hb'⟩
      · have hab2 : a + Pi.single μ 1 = b := by rw [hbt]; simp [wallNbr]
        have ha' : a + Pi.single μ 1 ∈ X := by rw [hab2]; exact hb
        refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single (b := edge s a μ)
          ⟨⟨centre s N a, hhub_mem a, centre_mem_edge a μ⟩, hhubS a ha⟩) ?_
        exact ⟨⟨centre s N b, hab2 ▸ centre_add_mem_edge a μ, hhub_mem b⟩, hedgeS a ha μ ha'⟩
    have hhub : ∀ c ∈ X, ∀ c' ∈ X, Relation.ReflTransGen R (hub s c) (hub s c') :=
      fun c hc c' hc' => by
        have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
          (hX.preconnected ⟨c, hc⟩ ⟨c', hc'⟩)
        exact Relation.ReflTransGen.lift' (fun a : (X : Set (Fin 4 → ZMod N)) => hub s a.1)
          hadj _ _ hr
    -- every element of `S0` meets the hub of a cube of `X`
    have hlink : ∀ σ ∈ S0, ∃ c ∈ X, R σ (hub s c) ∧ R (hub s c) σ := by
      intro σ hσ
      rcases Finset.mem_union.1 hσ with h | h
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
        exact ⟨c, hc, ⟨⟨_, hhub_mem c, hhub_mem c⟩, hσ⟩, ⟨⟨_, hhub_mem c, hhub_mem c⟩, hσ⟩⟩
      · obtain ⟨⟨c, μ⟩, hp, rfl⟩ := Finset.mem_image.1 h
        simp only [hE, Finset.mem_filter, Finset.mem_product] at hp
        exact ⟨c, hp.1.1, ⟨⟨_, centre_mem_edge c μ, hhub_mem c⟩, hσ⟩,
          ⟨⟨_, hhub_mem c, centre_mem_edge c μ⟩, hhubS c hp.1.1⟩⟩
    intro σ hσ τ hτ
    obtain ⟨c, hc, h1, -⟩ := hlink σ hσ
    obtain ⟨c', hc', -, h2⟩ := hlink τ hτ
    exact Relation.ReflTransGen.head h1 ((hhub c hc c' hc').tail h2)

/-! ### `lem:cube-count` -/

/-- `eq:cube-count`, first bound: `#(X) ≤ 2⁸(2 + d(X))`. -/
theorem card_le_size (hs : 0 < s) {X : Finset (Fin 4 → ZMod N)}
    (hX : ((wallGraph (ZMod N)).induce (X : Set (Fin 4 → ZMod N))).Connected) :
    (X.card : ℝ) ≤ 2 ^ 8 * (2 + size s N X) := by
  obtain ⟨S0, h0⟩ := exists_admissible hs hX
  have key : ((X.card : ℝ) / 2 ^ 8 - 2) * s ≤
      sInf ((fun S => ∑ σ ∈ S, eu σ.2) '' {S | Admissible s N X S}) := by
    refine le_csInf ⟨_, S0, h0, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    have h1 := (admissible_bounds hs hS).1
    have h2 : ∑ σ ∈ S, ‖σ.2‖ ≤ ∑ σ ∈ S, eu σ.2 := Finset.sum_le_sum fun σ _ => norm_le_eu _
    have h3 : (X.card : ℝ) / 2 ^ 8 - 2 ≤ (∑ σ ∈ S, ‖σ.2‖) / s := by
      have : (X.card : ℝ) / 2 ^ 8 ≤ 2 + (∑ σ ∈ S, ‖σ.2‖) / s := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 8)]; linarith
      linarith
    exact ((le_div_iff₀ hs).1 h3).trans h2
  have : (X.card : ℝ) / 2 ^ 8 - 2 ≤ size s N X := by
    unfold size
    calc (X.card : ℝ) / 2 ^ 8 - 2 = s⁻¹ * (((X.card : ℝ) / 2 ^ 8 - 2) * s) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left key (inv_nonneg.2 hs.le)
  rw [div_sub' (by norm_num), div_le_iff₀ (by norm_num)] at this
  linarith

/-- `eq:cube-count`, second bound, in the distance `|·|_∞`: `|z - z'|_∞ ≤ s(d(X) + 2)` for
`z, z' ∈ X`; with `|·|₂ ≤ 2|·|_∞` this is the core's `diam X ≤ s(2d(X) + 4)`. -/
theorem dist_le_size (hs : 0 < s) {X : Finset (Fin 4 → ZMod N)}
    (hX : ((wallGraph (ZMod N)).induce (X : Set (Fin 4 → ZMod N))).Connected)
    {z z' : Torus s N} (hz : z ∈ cubes s N X) (hz' : z' ∈ cubes s N X) :
    dist z z' ≤ s * (size s N X + 2) := by
  obtain ⟨S0, h0⟩ := exists_admissible hs hX
  have key : dist z z' - 2 * s ≤
      sInf ((fun S => ∑ σ ∈ S, eu σ.2) '' {S | Admissible s N X S}) := by
    refine le_csInf ⟨_, S0, h0, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    have h1 := (admissible_bounds hs hS).2 z hz z' hz'
    have h2 : ∑ σ ∈ S, ‖σ.2‖ ≤ ∑ σ ∈ S, eu σ.2 := Finset.sum_le_sum fun σ _ => norm_le_eu _
    linarith
  have : (dist z z' - 2 * s) / s ≤ size s N X := by
    unfold size
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left key (inv_nonneg.2 hs.le)
  rw [div_le_iff₀ hs] at this
  linarith

/-- `eq:domain-sum` on the torus: for `κ ≥ 2⁹(6 log 2 + 1)` and every cube `x`, the connected unions
of cubes containing `x` satisfy `Σ_X e^{-κ d(X)} ≤ 2^{6·2¹⁰} + 1`. -/
theorem domain_sum_torus (hs : 0 < s) {κ : ℝ} (hκ : 2 ^ 9 * (6 * Real.log 2 + 1) ≤ κ)
    (x : Fin 4 → ZMod N) :
    Summable (fun X : {X : Finset (Fin 4 → ZMod N) //
        x ∈ X ∧ ((wallGraph (ZMod N)).induce (X : Set (Fin 4 → ZMod N))).Connected} =>
      Real.exp (-κ * size s N X.1)) ∧
    ∑' X : {X : Finset (Fin 4 → ZMod N) //
        x ∈ X ∧ ((wallGraph (ZMod N)).induce (X : Set (Fin 4 → ZMod N))).Connected},
      Real.exp (-κ * size s N X.1) ≤ 2 ^ (6 * 2 ^ 10) + 1 :=
  domain_sum (wallGraph (ZMod N)) (wallGraph_degree_le _) (size_nonneg hs)
    (fun _ _ hconn => card_le_size hs hconn) hκ

end CoreLean

end
