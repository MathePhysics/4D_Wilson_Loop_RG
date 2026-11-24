/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`c1d6d533fce5`), the step "The cut-off minimiser", the algebra: the
correction `λ̃ = χλ - Σ_yc_yb_y` lies in `N(Q')` of the given sequence.

* `null_transfer`: if two sequences of domains on the same fine lattice have the same scales on a set `V` which is a
  union of their (common) blocks, then a function which vanishes outside `V` and has the block means zero for the one
  has them zero for the other.
* `bfun`: `b_y = a_y⁴ζ_y/Σ_{Δ(y)}ζ_y`, with the bump `ζ_y` of `SFBlockBump.lean`, supported in `Δ(y)` with the mean `1`.
* `corr`, `corr_null`: `g - Σ_y(Q'g)(y)b_y` has the block means zero.
-/
import CoreLean.SFComparison
import CoreLean.SFBlockBump

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **The transfer of `N(Q')`** between two sequences with the same blocks on a set `V`. -/
theorem null_transfer (D D' : DomSeq NF) (hL : D.L = D'.L) (V : Set (Site NF))
    (hV : ∀ x ∈ V, D.sc x = D'.sc x ∧ ∀ x' ∈ Blk D (D.sc x) (bc D x), x' ∈ V)
    (μ : Site NF → Mat) (hsupp : ∀ x, x ∉ V → μ x = 0)
    (hnull : ∀ y ∈ detB D', avgW D' (W1 S) y μ = 0) :
    ∀ y ∈ detB D, avgW D (W1 S) y μ = 0 := by
  intro y hy
  rw [avgW_triv_eq_zero_iff S D hy]
  by_cases h : ∃ x1 ∈ Blk D (D.sc y) y, x1 ∈ V
  · obtain ⟨x1, hx1, hx1V⟩ := h
    obtain ⟨hsc1, hbc1⟩ := sc_mem_blk D hy hx1
    obtain ⟨hsc', -⟩ := hV x1 hx1V
    have hbc' : bc D' x1 = y := by
      unfold bc; rw [← hsc', ← hL]; exact hbc1
    have hy' : y ∈ detB D' := by rw [← hbc']; exact mem_image_of_mem _ (mem_univ _)
    have hscy : D'.sc y = D.sc y := by
      calc D'.sc y = D'.sc (bc D' x1) := by rw [hbc']
        _ = D'.sc x1 := sc_bc D' x1
        _ = D.sc y := by rw [← hsc', hsc1]
    have hblk : Blk D' (D'.sc y) y = Blk D (D.sc y) y := by rw [hscy]; unfold Blk; rw [hL]
    have := (avgW_triv_eq_zero_iff S D' hy' μ).1 (hnull y hy')
    rwa [hblk] at this
  · push_neg at h
    exact sum_eq_zero fun x hx => hsupp x (h x hx)

/-- **The function `b_y`** of the block of `y ∈ 𝐁`: `a_y⁴ζ_y/Σ_{Δ(y)}ζ_y`. -/
def bfun (y x : Site NF) : ℝ :=
  (S.L : ℝ) ^ (4 * jj y) / (∑ x' ∈ Blk S.toDomSeq (jj y) y, zeta S y x') * zeta S y x

lemma zeta_sum_pos {y : Site NF} (hy : y ∈ detB S.toDomSeq) : 0 < ∑ x' ∈ Blk S.toDomSeq (jj y) y, zeta S y x' :=
  lt_of_lt_of_le (by positivity) (zeta_mass S hy)

lemma bfun_nonneg (y x : Site NF) : 0 ≤ bfun S y x := by
  unfold bfun
  have := zeta_nonneg S y x
  have : 0 ≤ ∑ x' ∈ Blk S.toDomSeq (jj y) y, zeta S y x' := sum_nonneg fun x' _ => zeta_nonneg S y x'
  positivity

lemma bfun_supp {y x : Site NF} (hy : y ∈ detB S.toDomSeq) (hx : x ∉ Blk S.toDomSeq (jj y) y) : bfun S y x = 0 := by
  unfold bfun; rw [zeta_supp S hy hx, mul_zero]

/-- **The mean of `b_y` over `Δ(y)` is `1`.** -/
lemma bfun_sum {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ∑ x ∈ Blk S.toDomSeq (jj y) y, bfun S y x = (S.L : ℝ) ^ (4 * jj y) := by
  unfold bfun
  rw [← mul_sum]
  have := zeta_sum_pos S hy
  field_simp

/-- **The correction** `g - Σ_{y ∈ 𝐁}(Q'g)(y)b_y`. -/
def corr (g : Site NF → Mat) : Site NF → Mat :=
  fun x => g x - ∑ y ∈ detB S.toDomSeq, ((bfun S y x : ℝ) : ℂ) • avgW S.toDomSeq (W1 S) y g

lemma avgW_triv_eq (D : DomSeq NF) {y : Site NF} (hy : y ∈ detB D) (f : Site NF → Mat) :
    avgW D (W1 S) y f = (((D.L : ℝ) ^ (4 * D.sc y) : ℝ) : ℂ)⁻¹ • ∑ x ∈ Blk D (D.sc y) y, f x := by
  rw [avgW_blk D (W1 S) hy f]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  simp [Ad, W1]

/-- **The correction has the block means zero.** -/
theorem corr_null (g : Site NF → Mat) : ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y (corr S g) = 0 := by
  intro y0 hy0
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  rw [avgW_triv_eq S S.toDomSeq hy0]
  simp only [corr, sum_sub_distrib]
  rw [sum_comm]
  -- only `y = y0` contributes on the block of `y0`
  have hterm : ∀ y ∈ detB S.toDomSeq, ∑ x ∈ Blk S.toDomSeq (jj y0) y0,
      ((bfun S y x : ℝ) : ℂ) • avgW S.toDomSeq (W1 S) y g =
      if y = y0 then (((S.L : ℝ) ^ (4 * jj y0) : ℝ) : ℂ) • avgW S.toDomSeq (W1 S) y0 g else 0 := by
    intro y hy
    split_ifs with h
    · subst h
      rw [← sum_smul, ← Complex.ofReal_sum, bfun_sum S hy]
    · refine sum_eq_zero fun x hx => ?_
      have hx' : x ∉ Blk S.toDomSeq (jj y) y := by
        intro hxy
        have h1 := (sc_mem_blk S.toDomSeq hy0 hx).2
        have h2 := (sc_mem_blk S.toDomSeq hy hxy).2
        exact h (h2.symm.trans h1)
      rw [bfun_supp S hy hx', Complex.ofReal_zero, zero_smul]
  rw [sum_congr rfl hterm, sum_ite_eq' (detB S.toDomSeq) y0, if_pos hy0]
  rw [avgW_triv_eq S S.toDomSeq hy0, smul_smul]
  have hne : (((S.L : ℝ) ^ (4 * jj y0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hL _).ne'
  simp only [toDomSeq_L]
  rw [mul_inv_cancel₀ hne, one_smul, sub_self, smul_zero]

/-! ### The cut-off inequality, before the bounds on the shell -/

/-- **Minkowski's inequality** for `‖f‖ = (Σ_x|f(x)|²)^{1/2}`. -/
lemma l2_tri (f g : Site NF → Mat) :
    Real.sqrt (∑ x, hs2 ((f + g) x)) ≤ Real.sqrt (∑ x, hs2 (f x)) + Real.sqrt (∑ x, hs2 (g x)) := by
  set u : EuclideanSpace ℝ (Site NF) := WithLp.toLp 2 (fun x => hs (f x))
  set v : EuclideanSpace ℝ (Site NF) := WithLp.toLp 2 (fun x => hs (g x))
  have hu : ‖u‖ = Real.sqrt (∑ x, hs2 (f x)) := by
    rw [EuclideanSpace.norm_eq]; congr 1
    refine sum_congr rfl fun x _ => ?_
    simp only [u, Real.norm_eq_abs, sq_abs, hs_sq]
  have hv : ‖v‖ = Real.sqrt (∑ x, hs2 (g x)) := by
    rw [EuclideanSpace.norm_eq]; congr 1
    refine sum_congr rfl fun x _ => ?_
    simp only [v, Real.norm_eq_abs, sq_abs, hs_sq]
  have huv : ‖u + v‖ = Real.sqrt (∑ x, (hs (f x) + hs (g x)) ^ 2) := by
    rw [EuclideanSpace.norm_eq]; congr 1
    refine sum_congr rfl fun x _ => ?_
    simp only [u, v, Real.norm_eq_abs, sq_abs]; rfl
  rw [← hu, ← hv]
  refine le_trans ?_ (norm_add_le u v)
  rw [huv]
  refine Real.sqrt_le_sqrt (sum_le_sum fun x _ => ?_)
  rw [← hs_sq]
  exact pow_le_pow_left₀ (hs_nonneg _) (hs_add_le _ _) 2

variable {S} in
/-- **The cut-off inequality** (eq:sf-cut-off before the bounds on the shell): with the comparison sequence `S'`, its
minimiser `λ = G'_{S'}R_{S'}f`, a cut-off `χ` supported in a set `V` on which `S` and `S'` have the same blocks, and the
correction `λ̃ = χλ - Σ_yc_yb_y`, `‖P_Sf‖ ≤ ‖P_{S'}f‖ + ‖Δ(λ - λ̃)‖`. -/
theorem cutoff_step [NeZero N] {i : ℕ} (hi : i + 1 ≤ S.k) (Λ : Set (Tor (ellT S.L S.mT))) (hΛ : IsCubes S (i + 1) Λ)
    (f : Site NF → Mat) (χ : Site NF → ℝ) (V : Set (Site NF))
    (hV : ∀ x ∈ V, jj x = ((twoLayer S i hi Λ hΛ).toDomSeq).sc x ∧
      ∀ x' ∈ Blk S.toDomSeq (jj x) (bc S.toDomSeq x), x' ∈ V)
    (hχV : ∀ x, x ∉ V → χ x = 0) :
    Real.sqrt (∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x)) ≤
      Real.sqrt (∑ x, hs2 (Pop (twoLayer S i hi Λ hΛ) (X0 (twoLayer S i hi Λ hΛ)) (W1 (twoLayer S i hi Λ hΛ))
        Set.univ f x)) +
      Real.sqrt (∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S))
        (minim (twoLayer S i hi Λ hΛ) f - corr (twoLayer S i hi Λ hΛ)
          (fun x => (χ x : ℂ) • minim (twoLayer S i hi Λ hΛ) f x))) x)) := by
  set lam : Site NF → Mat := minim (twoLayer S i hi Λ hΛ) f
  set g : Site NF → Mat := fun x => (χ x : ℂ) • lam x
  set lt : Site NF → Mat := corr (twoLayer S i hi Λ hΛ) g
  -- `λ̃` vanishes outside `V`
  have hsupp : ∀ x, x ∉ V → lt x = 0 := by
    intro x hx
    have hg : g x = 0 := by simp only [g, hχV x hx, Complex.ofReal_zero, zero_smul]
    simp only [lt, corr, hg, zero_sub, neg_eq_zero]
    refine sum_eq_zero fun y hy => ?_
    by_cases hxy : x ∈ Blk (twoLayer S i hi Λ hΛ).toDomSeq (((twoLayer S i hi Λ hΛ).toDomSeq).sc y) y
    · have hzero : avgW (twoLayer S i hi Λ hΛ).toDomSeq (W1 (twoLayer S i hi Λ hΛ)) y g = 0 := by
        refine (avgW_triv_eq_zero_iff (twoLayer S i hi Λ hΛ) (twoLayer S i hi Λ hΛ).toDomSeq hy g).2 ?_
        refine sum_eq_zero fun x' hx' => ?_
        by_cases hx'V : x' ∈ V
        · exfalso
          obtain ⟨hsc, hsub⟩ := hV x' hx'V
          obtain ⟨hsc', hbc'⟩ := sc_mem_blk (twoLayer S i hi Λ hΛ).toDomSeq hy hx'
          have hbc : bc S.toDomSeq x' = y := by
            rw [← hbc']; unfold bc; rw [hsc]; rfl
          have hblk : Blk S.toDomSeq (jj x') (bc S.toDomSeq x') =
              Blk (twoLayer S i hi Λ hΛ).toDomSeq (((twoLayer S i hi Λ hΛ).toDomSeq).sc y) y := by
            rw [hbc, hsc, hsc']; rfl
          exact hx (hsub x (hblk ▸ hxy))
        · simp only [g, hχV x' hx'V, Complex.ofReal_zero, zero_smul]
      simp only [hzero, smul_zero]
    · simp only [bfun_supp (twoLayer S i hi Λ hΛ) hy hxy, Complex.ofReal_zero, zero_smul]
  -- `λ̃ ∈ N(Q')` of `S`
  have hnull : ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y lt = 0 :=
    null_transfer S S.toDomSeq (twoLayer S i hi Λ hΛ).toDomSeq rfl V hV lt hsupp (corr_null (twoLayer S i hi Λ hΛ) g)
  have hvar := variational S f hnull
  -- `f - Δλ̃ = P_{(twoLayer S i hi Λ hΛ)}f + Δ(λ - λ̃)`
  obtain ⟨pf, hpf⟩ : ∃ pf : Site NF → Mat, pf = Pop (twoLayer S i hi Λ hΛ) (X0 (twoLayer S i hi Λ hΛ)) (W1 (twoLayer S i hi Λ hΛ)) Set.univ f := ⟨_, rfl⟩
  have h : Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) lam) = f - pf := by rw [hpf]; exact minim_lap (twoLayer S i hi Λ hΛ) f
  have hdec : f - Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) lt) =
      pf + Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (lam - lt)) := by
    rw [map_sub, map_sub, h]; abel
  rw [hdec] at hvar
  rw [← hpf]
  calc Real.sqrt (∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ f x))
      ≤ Real.sqrt (∑ x, hs2 ((pf + Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (lam - lt))) x)) :=
        Real.sqrt_le_sqrt hvar
    _ ≤ _ := l2_tri S _ _

/-! ### The decomposition of `Δ(λ - λ̃)` -/

lemma lap_const (b : Site NF → ℝ) (c : Mat) (x : Site NF) :
    Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (fun x => (b x : ℂ) • c)) x = (lapR S b x : ℂ) • c := by
  rw [lap0_triv]
  simp only [lapR]
  push_cast
  rw [sum_smul]
  refine sum_congr rfl fun ν _ => ?_
  module

lemma lap_sum {ι : Type*} (s : Finset ι) (F : ι → Site NF → Mat) (x : Site NF) :
    Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (fun x => ∑ i ∈ s, F i x)) x =
      ∑ i ∈ s, Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (F i)) x := by
  simp only [lap0_triv]
  rw [sum_comm]
  refine sum_congr rfl fun ν _ => ?_
  simp only [sum_sub_distrib, smul_sum]

/-! ### The comparison sequence on the lattice of `S` -/

section Wrap

variable {i : ℕ} (hi : i + 1 ≤ S.k) (Λ : Set (Tor (ellT S.L S.mT))) (hΛ : IsCubes S (i + 1) Λ)

/-- `P_{S'}f` on the lattice of `S`. -/
def PopT [NeZero N] (f : Site NF → Mat) : Site NF → Mat := Pop (twoLayer S i hi Λ hΛ) (X0 (twoLayer S i hi Λ hΛ)) (W1 (twoLayer S i hi Λ hΛ)) Set.univ f

/-- The minimiser of `S'` on the lattice of `S`. -/
def minimT [NeZero N] (f : Site NF → Mat) : Site NF → Mat := minim (twoLayer S i hi Λ hΛ) f

/-- `𝐁` of `S'`. -/
def detBT : Finset (Site NF) := detB (twoLayer S i hi Λ hΛ).toDomSeq

/-- `Q'` of `S'`. -/
def avgT (y : Site NF) (g : Site NF → Mat) : Mat := avgW (twoLayer S i hi Λ hΛ).toDomSeq (W1 (twoLayer S i hi Λ hΛ)) y g

/-- `b_y` of `S'`. -/
def bfunT (y x : Site NF) : ℝ := bfun (twoLayer S i hi Λ hΛ) y x

/-- The correction of `S'`. -/
def corrT (g : Site NF → Mat) : Site NF → Mat := corr (twoLayer S i hi Λ hΛ) g

lemma corrT_apply (g : Site NF → Mat) (x : Site NF) :
    corrT S hi Λ hΛ g x = g x - ∑ y ∈ detBT S hi Λ hΛ, ((bfunT S hi Λ hΛ y x : ℝ) : ℂ) • avgT S hi Λ hΛ y g := rfl

lemma minimT_lap [NeZero N] (f : Site NF → Mat) :
    Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (minimT S hi Λ hΛ f)) = f - PopT S hi Λ hΛ f :=
  minim_lap (twoLayer S i hi Λ hΛ) f

end Wrap

variable {S} in
/-- **The decomposition of `Δ(λ - λ̃)`**: for `f` which vanishes where `χ ≠ 1`,
`Δ(λ - λ̃) = -(1 - χ)P_{S'}f - (Δχ)λ + Σ_ν(d⁺χd⁺λ + d⁻χd⁻λ) + Σ_y(Δb_y)c_y`. -/
theorem lap_diff_eq [NeZero N] {i : ℕ} (hi : i + 1 ≤ S.k) (Λ : Set (Tor (ellT S.L S.mT))) (hΛ : IsCubes S (i + 1) Λ)
    (f : Site NF → Mat) (χ : Site NF → ℝ) (hfχ : ∀ x, χ x ≠ 1 → f x = 0) (x : Site NF) :
    Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) (minimT S hi Λ hΛ f -
      corrT S hi Λ hΛ (fun x => (χ x : ℂ) • minimT S hi Λ hΛ f x))) x =
      -(((1 - χ x : ℝ) : ℂ) • PopT S hi Λ hΛ f x) - (lapR S χ x : ℂ) • minimT S hi Λ hΛ f x +
      ∑ ν, (((χ (x + unit NF ν) - χ x : ℝ) : ℂ) • (minimT S hi Λ hΛ f (x + unit NF ν) - minimT S hi Λ hΛ f x) +
        ((χ (x - unit NF ν) - χ x : ℝ) : ℂ) • (minimT S hi Λ hΛ f (x - unit NF ν) - minimT S hi Λ hΛ f x)) +
      ∑ y ∈ detBT S hi Λ hΛ, (lapR S (bfunT S hi Λ hΛ y) x : ℂ) •
        avgT S hi Λ hΛ y (fun x => (χ x : ℂ) • minimT S hi Λ hΛ f x) := by
  set lam := minimT S hi Λ hΛ f
  set g : Site NF → Mat := fun x => (χ x : ℂ) • lam x
  -- `λ - λ̃ = (1 - χ)λ + Σ_yc_yb_y`
  have e1 : lam - corrT S hi Λ hΛ g = (fun x => ((1 - χ x : ℝ) : ℂ) • lam x) +
      (fun x => ∑ y ∈ detBT S hi Λ hΛ, ((bfunT S hi Λ hΛ y x : ℝ) : ℂ) • avgT S hi Λ hΛ y g) := by
    funext x
    rw [Pi.sub_apply, corrT_apply, Pi.add_apply]
    simp only [g]
    push_cast
    rw [sub_smul, one_smul]; abel
  rw [e1, map_add, map_add, Pi.add_apply, lap_mul S (fun x => 1 - χ x) lam x, lap_sum S]
  simp only [lap_const S]
  rw [minimT_lap]
  have hfx : ((1 - χ x : ℝ) : ℂ) • f x = 0 := by
    by_cases h : χ x = 1
    · rw [h, sub_self, Complex.ofReal_zero, zero_smul]
    · rw [hfχ x h, smul_zero]
  have hlapR : lapR S (fun x => 1 - χ x) x = -lapR S χ x := by
    simp only [lapR, ← sum_neg_distrib]; refine sum_congr rfl fun ν _ => ?_; ring
  rw [Pi.sub_apply, smul_sub, hfx, zero_sub, hlapR]
  have hd : ∀ ν, (((1 - χ (x + unit NF ν)) - (1 - χ x) : ℝ) : ℂ) = -((χ (x + unit NF ν) - χ x : ℝ) : ℂ) ∧
      (((1 - χ (x - unit NF ν)) - (1 - χ x) : ℝ) : ℂ) = -((χ (x - unit NF ν) - χ x : ℝ) : ℂ) := fun ν => by
    constructor <;> push_cast <;> ring
  simp only [fun ν => (hd ν).1, fun ν => (hd ν).2, neg_smul, ← neg_add, sum_neg_distrib]
  push_cast
  module

end SFBounds
end CoreLean

end
