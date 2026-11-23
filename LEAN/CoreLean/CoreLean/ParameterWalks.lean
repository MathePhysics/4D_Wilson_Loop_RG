/-
`lem:parameter-walks` of BALABAN_CORE.tex: the parameters of a walk.

Setting and modelling.
* Units `a_n = 1`: the old sequence is a `DomainData` (whose top spacing is `1`). The weighted distance
  is invariant under the common rescaling of lengths and spacings, and the grid `π_n` has the side
  `Ma_n = M`.
* The torus `(ℝ/pℤ)⁴` with `p = KM`; the cubes of `π_n` are the cells `{x | ⌊x_ν/M⌋ ≡ c_ν mod K}`,
  `c ∈ (ℤ/K)⁴` (`Grid.idx`); a cube `Δ` meets `X` iff `Δ = idx x` for some `x ∈ X`.
* The enlarged cubes of the walk are sets `C_0, …, C_m` of `ℓ^∞`-diameter at most `ε` with `4ε < M` (in
  the core, sides at most `Ma_n/L` with `L ≥ 28`); `X(ω) = ⋃ C_l`; `d_ω(y, y')` is the infimum over
  `z_l ∈ C_l` of `d(y, z_0) + Σ d(z_l, z_{l+1}) + d(z_m, y')`.

The proof is the core's, with the path replaced by the chain `z_0, …, z_m` of its points (the path is
used only through the `ℓ¹`-lengths between them, which bound `|·|₁ ≤ d`): the points of the chain are
grouped by their cumulative `ℓ¹`-length in buckets of length `M/2`, at most `2ℓ/M + 1` of them; all points
of `X(ω)` attached to a bucket lie within `ε + M/2` of one point, hence in at most `3⁴` cubes of `π_n`. This
gives `m(ω) ≤ 81(2ℓ/M + 1)`, which is at most the core's `3⁴·2⁴(2ℓ/M + 1)`.
-/
import CoreLean.ParameterExpansion
import CoreLean.Distance

open Finset
open scoped ENNReal Classical

noncomputable section

namespace CoreLean

namespace ParamWalks

variable {p : ℝ}

/-- The grid `π_n` of side `M` on the torus of side `p = KM`. -/
structure Grid (p : ℝ) where
  K : ℕ
  [neZero : NeZero K]
  M : ℝ
  M_pos : 0 < M
  side : p = K * M

attribute [instance] Grid.neZero

namespace Grid

variable (G : Grid p)

/-- The index `⌊x/M⌋ mod K` of a real. -/
def idxR (x : ℝ) : ZMod G.K := ((⌊x / G.M⌋ : ℤ) : ZMod G.K)

lemma idxR_periodic : Function.Periodic G.idxR p := fun x => by
  simp only [idxR]
  have hpM : p / G.M = (G.K : ℝ) := by rw [div_eq_iff G.M_pos.ne']; exact G.side
  have : (x + p) / G.M = x / G.M + (G.K : ℝ) := by rw [add_div, hpM]
  rw [this, Int.floor_add_natCast]
  push_cast
  rw [ZMod.natCast_self, add_zero]

/-- The cube of `π_n` containing a point of the torus. -/
def idx (z : Tor p) : Fin 4 → ZMod G.K := fun ν => G.idxR_periodic.lift (z ν)

lemma idx_projT (x : Fin 4 → ℝ) (ν : Fin 4) : G.idx (projT p x) ν = G.idxR (x ν) := rfl

/-- The number of cubes of `π_n` which meet `S`. -/
def count (S : Set (Tor p)) : ℕ := (univ.filter fun c => ∃ z ∈ S, G.idx z = c).card

lemma count_mono {S S' : Set (Tor p)} (h : S ⊆ S') : G.count S ≤ G.count S' := by
  refine card_le_card fun c hc => ?_
  simp only [mem_filter, mem_univ, true_and] at hc ⊢
  obtain ⟨z, hz, rfl⟩ := hc
  exact ⟨z, h hz, rfl⟩

end Grid

/-- An interval of length less than `jM` meets at most `j + 1` cells of side `M`. -/
lemma floor_mem {M a b : ℝ} (hM : 0 < M) (hab : b ≤ a) {j : ℕ} (h : a - b < j * M) :
    ∃ i : ℕ, i ≤ j ∧ ⌊a / M⌋ = ⌊b / M⌋ + i := by
  have h0 : ⌊b / M⌋ ≤ ⌊a / M⌋ := Int.floor_mono (div_le_div_of_nonneg_right hab hM.le)
  have h1 : ⌊a / M⌋ - ⌊b / M⌋ < j + 1 := by
    have ha := Int.floor_le (a / M)
    have hb := Int.lt_floor_add_one (b / M)
    have : a / M - b / M < j := by
      rw [← sub_div, div_lt_iff₀ hM]; exact h
    have : ((⌊a / M⌋ - ⌊b / M⌋ : ℤ) : ℝ) < j + 1 := by push_cast; linarith
    exact_mod_cast this
  refine ⟨(⌊a / M⌋ - ⌊b / M⌋).toNat, ?_, ?_⟩
  · omega
  · omega

/-- A set within the `ℓ^∞`-distance `ρ` of a point, with `2ρ < jM`, meets at most `(j + 1)⁴` cubes. -/
theorem count_ball_le (G : Grid p) (y : Tor p) {ρ : ℝ} {j : ℕ} (hρ : 2 * ρ < j * G.M)
    (S : Set (Tor p)) (hS : ∀ z ∈ S, ∀ ν, ‖z ν - y ν‖ ≤ ρ) : G.count S ≤ (j + 1) ^ 4 := by
  obtain ⟨x, hx⟩ : ∃ x : Fin 4 → ℝ, projT p x = y := by
    choose u hu using fun ν => QuotientAddGroup.mk_surjective (y ν)
    exact ⟨u, funext hu⟩
  set T : Fin 4 → Finset (ZMod G.K) := fun ν =>
    (range (j + 1)).image fun i : ℕ => ((⌊(x ν - ρ) / G.M⌋ + (i : ℤ) : ℤ) : ZMod G.K)
  have hsub : (univ.filter fun c => ∃ z ∈ S, G.idx z = c) ⊆ Fintype.piFinset T := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    obtain ⟨z, hz, rfl⟩ := hc
    obtain ⟨x', hx', hd⟩ := exists_close_lift (p := p) x z
    rw [Fintype.mem_piFinset]
    intro ν
    have hyν : (x ν : AddCircle p) = y ν := by rw [← hx]; rfl
    have hdist : |x' ν - x ν| ≤ ρ := by rw [hd ν, hyν]; exact hS z hz ν
    have hle : x ν - ρ ≤ x' ν := by linarith [neg_abs_le (x' ν - x ν)]
    have hlt : x' ν - (x ν - ρ) < j * G.M := by linarith [le_abs_self (x' ν - x ν)]
    obtain ⟨i, hi, hfl⟩ := floor_mem G.M_pos hle hlt
    simp only [T, mem_image, mem_range]
    refine ⟨i, Nat.lt_succ_of_le hi, ?_⟩
    rw [← hx', Grid.idx_projT]
    simp only [Grid.idxR, hfl]
  refine (card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ ν, (T ν).card ≤ ∏ _ν : Fin 4, (j + 1) :=
        Finset.prod_le_prod' fun ν _ => card_image_le.trans (by simp)
    _ = (j + 1) ^ 4 := by simp

/-! ### The chain and its buckets -/

/-- The `ℓ¹` distance on the torus satisfies the triangle inequality. -/
lemma dist1_triangle (z z' z'' : Tor p) : dist1 z z'' ≤ dist1 z z' + dist1 z' z'' := by
  unfold dist1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun ν _ => norm_sub_le_norm_sub_add_norm_sub _ _ _

lemma norm_le_dist1 (z z' : Tor p) (ν : Fin 4) : ‖z ν - z' ν‖ ≤ dist1 z z' :=
  Finset.single_le_sum (f := fun ν => ‖z ν - z' ν‖) (fun _ _ => norm_nonneg _) (mem_univ ν)

/-- The cumulative `ℓ¹`-length of the chain `w 0, w 1, …`. -/
def cum (w : ℕ → Tor p) (i : ℕ) : ℝ := ∑ l ∈ range i, dist1 (w l) (w (l + 1))

lemma dist1_le_cum (w : ℕ → Tor p) {i i' : ℕ} (h : i ≤ i') :
    dist1 (w i) (w i') ≤ cum w i' - cum w i := by
  induction i', h using Nat.le_induction with
  | base => simp [dist1]
  | succ i' _ ih =>
    rw [cum, sum_range_succ, ← cum]
    linarith [dist1_triangle (w i) (w i') (w (i' + 1))]

lemma cum_mono (w : ℕ → Tor p) {i i' : ℕ} (h : i ≤ i') : cum w i ≤ cum w i' := by
  have := dist1_le_cum w h
  linarith [dist1_nonneg (w i) (w i')]

/-- The general bound: if every point of `S` lies within `ε` of a point `w i`, `i ≤ m`, of a chain
of `ℓ¹`-length less than `ℓ`, with `2ε < M`, then `S` meets at most `81(2ℓ/M + 1)` cubes. -/
theorem count_chain_le (G : Grid p) (w : ℕ → Tor p) (m : ℕ) {ε ℓ : ℝ} (hε : 0 ≤ ε)
    (hεM : 2 * ε < G.M) (hℓ : cum w m < ℓ) (S : Set (Tor p))
    (hS : ∀ x ∈ S, ∃ i ≤ m, ∀ ν, ‖x ν - w i ν‖ ≤ ε) :
    (G.count S : ℝ) ≤ 81 * (2 * ℓ / G.M + 1) := by
  classical
  have hM := G.M_pos
  have hM2 : 0 < G.M / 2 := by positivity
  set b : ℕ → ℤ := fun i => ⌊cum w i / (G.M / 2)⌋
  set Q := (⌊cum w m / (G.M / 2)⌋).toNat
  -- a representative of each bucket
  set rep : ℕ → ℕ := fun q => if h : ∃ i ≤ m, b i = q then Classical.choose h else 0
  have hrep : ∀ i ≤ m, rep (b i).toNat ≤ m ∧ b (rep (b i).toNat) = b i := by
    intro i hi
    have hb0 : 0 ≤ b i := Int.floor_nonneg.mpr (div_nonneg (by
      unfold cum; exact sum_nonneg fun _ _ => dist1_nonneg _ _) hM2.le)
    have hex : ∃ i' ≤ m, b i' = ((b i).toNat : ℤ) := ⟨i, hi, (Int.toNat_of_nonneg hb0).symm⟩
    simp only [rep, dif_pos hex]
    obtain ⟨h1, h2⟩ := Classical.choose_spec hex
    exact ⟨h1, h2.trans (Int.toNat_of_nonneg hb0)⟩
  have hbucket : ∀ i ≤ m, (b i).toNat ∈ range (Q + 1) := by
    intro i hi
    rw [mem_range, Nat.lt_succ_iff]
    exact Int.toNat_le_toNat (Int.floor_mono (div_le_div_of_nonneg_right (cum_mono w hi) hM2.le))
  -- the points attached to a bucket lie within `ε + M/2` of its representative
  set B : ℕ → Set (Tor p) := fun q => {x | ∀ ν, ‖x ν - w (rep q) ν‖ ≤ ε + G.M / 2}
  have hcover : (univ.filter fun c => ∃ z ∈ S, G.idx z = c) ⊆
      (range (Q + 1)).biUnion fun q => univ.filter fun c => ∃ z ∈ B q, G.idx z = c := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨i, hi, hxi⟩ := hS x hx
    obtain ⟨hr, hbr⟩ := hrep i hi
    rw [mem_biUnion]
    refine ⟨(b i).toNat, hbucket i hi, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨x, fun ν => ?_, rfl⟩
    -- same bucket: the cumulative lengths differ by less than `M/2`
    set r := rep (b i).toNat
    have hfl : ⌊cum w r / (G.M / 2)⌋ = ⌊cum w i / (G.M / 2)⌋ := hbr
    have hclose : |cum w r - cum w i| < G.M / 2 := by
      have := Int.abs_sub_lt_one_of_floor_eq_floor hfl
      rw [← sub_div, abs_div, abs_of_pos hM2, div_lt_one hM2] at this
      exact this
    have hd : dist1 (w i) (w r) < G.M / 2 := by
      rcases le_total i r with h | h
      · have := dist1_le_cum w h
        linarith [le_abs_self (cum w r - cum w i)]
      · have := dist1_le_cum w h
        rw [show dist1 (w i) (w r) = dist1 (w r) (w i) by
          unfold dist1; congr 1; funext ν; rw [norm_sub_rev]]
        linarith [neg_abs_le (cum w r - cum w i)]
    calc ‖x ν - w r ν‖ ≤ ‖x ν - w i ν‖ + ‖w i ν - w r ν‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + G.M / 2 := by linarith [hxi ν, norm_le_dist1 (w i) (w r) ν]
  have hcount : G.count S ≤ (Q + 1) * 81 := by
    refine (card_le_card hcover).trans (card_biUnion_le.trans ?_)
    calc ∑ q ∈ range (Q + 1), (univ.filter fun c => ∃ z ∈ B q, G.idx z = c).card
        ≤ ∑ _q ∈ range (Q + 1), 81 := sum_le_sum fun q _ => by
          have := count_ball_le G (w (rep q)) (ρ := ε + G.M / 2) (j := 2) (by push_cast; linarith)
            (B q) fun z hz => hz
          simpa [Grid.count] using this
      _ = (Q + 1) * 81 := by simp
  have hQ : (Q : ℝ) ≤ 2 * cum w m / G.M := by
    have hc0 : 0 ≤ cum w m := by unfold cum; exact sum_nonneg fun _ _ => dist1_nonneg _ _
    have : ((⌊cum w m / (G.M / 2)⌋.toNat : ℤ) : ℝ) ≤ cum w m / (G.M / 2) := by
      rw [Int.toNat_of_nonneg (Int.floor_nonneg.mpr (div_nonneg hc0 hM2.le))]
      exact Int.floor_le _
    rw [show 2 * cum w m / G.M = cum w m / (G.M / 2) by field_simp]
    exact_mod_cast this
  have hQ' : (Q : ℝ) + 1 ≤ 2 * ℓ / G.M + 1 := by
    have : 2 * cum w m / G.M ≤ 2 * ℓ / G.M :=
      div_le_div_of_nonneg_right (by linarith) hM.le
    linarith
  calc (G.count S : ℝ) ≤ ((Q + 1) * 81 : ℕ) := by exact_mod_cast hcount
    _ = 81 * ((Q : ℝ) + 1) := by push_cast; ring
    _ ≤ 81 * (2 * ℓ / G.M + 1) := by linarith

/-! ### The walk -/

variable (D : DomainData p)

/-- `d_ω(y, y')`: the least weighted length of a chain from `y` to `y'` through the sets `C_0, …, C_m`
in their order. -/
def dω (C : ℕ → Set (Tor p)) (m : ℕ) (y y' : Tor p) : ℝ≥0∞ :=
  ⨅ (z : ℕ → Tor p) (_ : ∀ l ≤ m, z l ∈ C l),
    wdist D y (z 0) + ∑ l ∈ range m, wdist D (z l) (z (l + 1)) + wdist D (z m) y'

/-- `X(ω) = C_0 ∪ ⋯ ∪ C_m`. -/
def Xω (C : ℕ → Set (Tor p)) (m : ℕ) : Set (Tor p) := {x | ∃ l ≤ m, x ∈ C l}

/-- The two bounds for a chain of weighted length less than `ℓ`. -/
theorem count_lt (G : Grid p) (C : ℕ → Set (Tor p)) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hεM : 4 * ε < G.M) (hC : ∀ l ≤ m, ∀ x ∈ C l, ∀ x' ∈ C l, ∀ ν, ‖x ν - x' ν‖ ≤ ε)
    (y y' : Tor p) {ℓ : ℝ} (hℓ : dω D C m y y' < ENNReal.ofReal ℓ) :
    (ℓ ≤ G.M / 4 → G.count (Xω C m) ≤ 16) ∧
      (G.count (Xω C m) : ℝ) ≤ 81 * (2 * ℓ / G.M + 1) := by
  -- a chain of weighted length less than `ℓ`
  obtain ⟨z, hz, hlt⟩ : ∃ z : ℕ → Tor p, (∀ l ≤ m, z l ∈ C l) ∧
      wdist D y (z 0) + ∑ l ∈ range m, wdist D (z l) (z (l + 1)) + wdist D (z m) y' <
        ENNReal.ofReal ℓ := by
    simp only [dω, iInf_lt_iff] at hℓ
    obtain ⟨z, hz, h⟩ := hℓ
    exact ⟨z, hz, h⟩
  -- its `ℓ¹`-lengths
  have hd1 : ∀ u v : Tor p, ENNReal.ofReal (dist1 u v) ≤ wdist D u v := dist1_le_wdist D
  have hsum : dist1 y (z 0) + cum z m + dist1 (z m) y' < ℓ := by
    have hℓpos : 0 < ℓ := by
      by_contra h
      push_neg at h
      rw [ENNReal.ofReal_of_nonpos h] at hlt
      exact (ENNReal.not_lt_zero hlt)
    have h1 : ENNReal.ofReal (dist1 y (z 0) + cum z m + dist1 (z m) y') ≤
        wdist D y (z 0) + ∑ l ∈ range m, wdist D (z l) (z (l + 1)) + wdist D (z m) y' := by
      have hc : 0 ≤ cum z m := by unfold cum; exact sum_nonneg fun _ _ => dist1_nonneg _ _
      rw [ENNReal.ofReal_add (add_nonneg (dist1_nonneg _ _) hc) (dist1_nonneg _ _),
        ENNReal.ofReal_add (dist1_nonneg _ _) hc]
      gcongr
      · exact hd1 _ _
      · unfold cum
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => dist1_nonneg _ _]
        exact sum_le_sum fun l _ => hd1 _ _
      · exact hd1 _ _
    exact (ENNReal.ofReal_lt_ofReal_iff hℓpos).mp (lt_of_le_of_lt h1 hlt)
  have hcum0 : 0 ≤ cum z m := by unfold cum; exact sum_nonneg fun _ _ => dist1_nonneg _ _
  have hX : ∀ x ∈ Xω C m, ∃ i ≤ m, ∀ ν, ‖x ν - z i ν‖ ≤ ε := fun x hx => by
    obtain ⟨l, hl, hxl⟩ := hx
    exact ⟨l, hl, fun ν => hC l hl x hxl (z l) (hz l hl) ν⟩
  refine ⟨fun hℓM => ?_, ?_⟩
  · -- all of `X(ω)` lies within `ε + ℓ` of `y`
    refine count_ball_le G y (ρ := ε + ℓ) (j := 1) (by push_cast; linarith) _ fun x hx ν => ?_
    obtain ⟨i, hi, hxi⟩ := hX x hx
    have hyz : dist1 y (z i) ≤ dist1 y (z 0) + cum z m := by
      have := dist1_triangle y (z 0) (z i)
      have := dist1_le_cum z (Nat.zero_le i)
      have := cum_mono z hi
      simp only [cum, range_zero, sum_empty, sub_zero] at *
      linarith
    have := norm_le_dist1 y (z i) ν
    calc ‖x ν - y ν‖ ≤ ‖x ν - z i ν‖ + ‖z i ν - y ν‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + ℓ := by
        rw [norm_sub_rev (z i ν)]
        linarith [hxi ν, dist1_nonneg (z m) y']
  · have e1 := dist1_nonneg y (z 0)
    have e2 := dist1_nonneg (z m) y'
    have hcm : cum z m < ℓ := by linarith
    exact count_chain_le G z m hε (by linarith) hcm _ hX

/-- `lem:parameter-walks`: `m(ω) ≤ 2⁴` if `d_ω(y, y') < M/4`, and `m(ω) ≤ 7776 d_ω(y, y')/M`
otherwise. -/
theorem count_le (G : Grid p) (C : ℕ → Set (Tor p)) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hεM : 4 * ε < G.M) (hC : ∀ l ≤ m, ∀ x ∈ C l, ∀ x' ∈ C l, ∀ ν, ‖x ν - x' ν‖ ≤ ε)
    (hne : ∀ l ≤ m, (C l).Nonempty) (y y' : Tor p) :
    dω D C m y y' ≠ ⊤ ∧
      (dω D C m y y' < ENNReal.ofReal (G.M / 4) → G.count (Xω C m) ≤ 16) ∧
      (ENNReal.ofReal (G.M / 4) ≤ dω D C m y y' →
        (G.count (Xω C m) : ℝ) ≤ 7776 * (dω D C m y y').toReal / G.M) := by
  have hM := G.M_pos
  have hfin : dω D C m y y' ≠ ⊤ := by
    have hex : ∀ l, ∃ x : Tor p, l ≤ m → x ∈ C l := fun l => by
      by_cases h : l ≤ m
      · obtain ⟨x, hx⟩ := hne l h; exact ⟨x, fun _ => hx⟩
      · exact ⟨y, fun h' => absurd h' h⟩
    choose z hz using hex
    refine ne_top_of_le_ne_top ?_ (iInf₂_le z fun l hl => hz l hl)
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨wdist_ne_top D _ _, ?_⟩,
      wdist_ne_top D _ _⟩
    exact ENNReal.sum_ne_top.mpr fun l _ => wdist_ne_top D _ _
  refine ⟨hfin, fun h => (count_lt D G C m hε hεM hC y y' h).1 le_rfl, fun h => ?_⟩
  set d := (dω D C m y y').toReal
  have hd : G.M / 4 ≤ d := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin]; exact h
  -- for every `ℓ > d`, `m(ω) ≤ 81(2ℓ/M + 1) ≤ 7776 ℓ/M`
  have key : ∀ ℓ, d < ℓ → (G.count (Xω C m) : ℝ) * G.M / 7776 ≤ ℓ := fun ℓ hℓ => by
    have hℓ' : dω D C m y y' < ENNReal.ofReal ℓ := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hℓ
    have h1 := (count_lt D G C m hε hεM hC y y' hℓ').2
    have h2 : 81 * (2 * ℓ / G.M + 1) ≤ 7776 * ℓ / G.M := by
      have : 1 ≤ 4 * ℓ / G.M := by rw [le_div_iff₀ hM]; linarith
      have e1 : 81 * (2 * ℓ / G.M + 1) ≤ 81 * (2 * ℓ / G.M + 4 * ℓ / G.M) := by linarith
      have e2 : 81 * (2 * ℓ / G.M + 4 * ℓ / G.M) = 486 * ℓ / G.M := by ring
      have e3 : 486 * ℓ / G.M ≤ 7776 * ℓ / G.M :=
        div_le_div_of_nonneg_right (by nlinarith) hM.le
      linarith
    have h3 := h1.trans h2
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 7776)]
    rw [le_div_iff₀ hM] at h3
    linarith
  have := le_of_forall_gt_imp_ge_of_dense key
  rw [le_div_iff₀ hM]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 7776)] at this
  linarith

/-- `eq:parameter-walks`: for `κ₁ ≥ 0`, `δ > 0` with `δM ≥ 2¹⁴κ₁`, and `|s(Δ)| ≤ e^{κ₁}`,
`Π_{Δ ∈ σ₀, Δ ∩ X(ω) ≠ ∅} |s(Δ)| ≤ e^{16κ₁} e^{δ d_ω(y, y')/2}`. -/
theorem parameter_walks (G : Grid p) (C : ℕ → Set (Tor p)) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hεM : 4 * ε < G.M) (hC : ∀ l ≤ m, ∀ x ∈ C l, ∀ x' ∈ C l, ∀ ν, ‖x ν - x' ν‖ ≤ ε)
    (hne : ∀ l ≤ m, (C l).Nonempty) (y y' : Tor p) (σ₀ : Finset (Fin 4 → ZMod G.K))
    (s : (Fin 4 → ZMod G.K) → ℂ) {κ₁ δ : ℝ} (hκ : 0 ≤ κ₁) (hδ : 0 < δ)
    (hδM : 2 ^ 14 * κ₁ ≤ δ * G.M) (hs : ∀ c ∈ σ₀, ‖s c‖ ≤ Real.exp κ₁) :
    ∏ c ∈ σ₀.filter (fun c => ∃ x ∈ Xω C m, G.idx x = c), ‖s c‖ ≤
      Real.exp (16 * κ₁) * Real.exp (δ / 2 * (dω D C m y y').toReal) := by
  have hM := G.M_pos
  obtain ⟨hfin, h1, h2⟩ := count_le D G C m hε hεM hC hne y y'
  set n := G.count (Xω C m)
  set d := (dω D C m y y').toReal
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  -- the product is at most `e^{κ₁ m(ω)}`
  have hprod : ∏ c ∈ σ₀.filter (fun c => ∃ x ∈ Xω C m, G.idx x = c), ‖s c‖ ≤
      Real.exp (κ₁ * n) := by
    have hcard : (σ₀.filter fun c => ∃ x ∈ Xω C m, G.idx x = c).card ≤ n :=
      card_le_card fun c hc => by
        simp only [mem_filter] at hc ⊢; exact ⟨mem_univ _, hc.2⟩
    calc ∏ c ∈ σ₀.filter (fun c => ∃ x ∈ Xω C m, G.idx x = c), ‖s c‖
        ≤ ∏ _c ∈ σ₀.filter (fun c => ∃ x ∈ Xω C m, G.idx x = c), Real.exp κ₁ :=
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun c hc => hs c (mem_filter.mp hc).1
      _ = Real.exp κ₁ ^ (σ₀.filter fun c => ∃ x ∈ Xω C m, G.idx x = c).card := prod_const _
      _ ≤ Real.exp κ₁ ^ n := pow_le_pow_right₀ (Real.one_le_exp hκ) hcard
      _ = Real.exp (κ₁ * n) := by rw [← Real.exp_nat_mul, mul_comm]
  refine hprod.trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  by_cases hcase : dω D C m y y' < ENNReal.ofReal (G.M / 4)
  · have := h1 hcase
    have : (n : ℝ) ≤ 16 := by exact_mod_cast this
    nlinarith [mul_nonneg hδ.le hd0]
  · push_neg at hcase
    have hn := h2 hcase
    -- `κ₁ m(ω) ≤ 7776 κ₁ d/M ≤ δd/2`
    have : κ₁ * n ≤ δ / 2 * d := by
      calc κ₁ * n ≤ κ₁ * (7776 * d / G.M) := mul_le_mul_of_nonneg_left hn hκ
        _ = 7776 * κ₁ / G.M * d := by ring
        _ ≤ δ / 2 * d := by
          refine mul_le_mul_of_nonneg_right ?_ hd0
          rw [div_le_iff₀ hM]; nlinarith
    nlinarith

end ParamWalks

end CoreLean
