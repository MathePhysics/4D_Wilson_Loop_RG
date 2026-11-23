/-
`lem:lie-algebra` of BALABAN_CORE.tex (`b1ff7d2601a1`): the first sentence, which the rest of the
formalisation takes as the named input `GaugeGroup.LieInput`, proved from the closedness of `G`.

The core: `G` is compact, hence closed in `M_N(ℂ)`. For matrices `X`, `Y`, the Lie product formula
`(e^{X/n}e^{Y/n})ⁿ → e^{X+Y}` (`lie_product`, with the core's bound: `e^{X/n}e^{Y/n}` and `e^{(X+Y)/n}`
differ by `O(n⁻²)`, and the telescoping sum of the `n`-th powers is `O(n⁻¹)`) gives `e^{it(A+B)} ∈ G` for
`A, B ∈ 𝔤`, so that `𝔤` is closed under addition (`add_mem_lie`). `𝔤` is closed (`isClosed_lie`); for
`A, B ∈ 𝔤` the matrices `e^{itA}Be^{-itA}` lie in `𝔤`, so do the difference quotients, and their limit
`i[A, B]` lies in `𝔤` (`bracket_mem_lie`). Together: `lieInput_of_isClosed`.

`G` enters with the hypothesis that the set of its matrices is closed in `M_N(ℂ)` (`IsClosed (mats G)`),
which is the core's "compact, hence closed"; with it every theorem of the formalisation which assumes
`G.LieInput` holds without that assumption. The rest of `lem:lie-algebra` is derived from `LieInput` in
`Algebra.lean` (`commutator_mem_lieC`, `conjTranspose_mem_lieC`, `lie_inter_I_lie`).
-/
import CoreLean.Algebra
import CoreLean.ProductExp

open NormedSpace Filter
open scoped Matrix.Norms.L2Operator Topology

noncomputable section

namespace CoreLean

/-! ### The Lie product formula -/

section LieProduct

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

lemma norm_exp_le_of_one (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have := BakerCampbellHausdorff.norm_exp_sub_one_le ℂ x
  calc ‖exp x‖ = ‖(exp x - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖exp x - 1‖ + ‖(1 : 𝔸)‖ := norm_add_le _ _
    _ ≤ Real.exp ‖x‖ := by linarith

/-- `‖e^x - 1 - x‖ ≤ ‖x‖²` for `‖x‖ ≤ 1`. -/
lemma norm_exp_sub_one_sub_le (x : 𝔸) (hx : ‖x‖ ≤ 1) : ‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := by
  have h := norm_exp_sub_quad_le x
  have hq : ‖(2 : ℂ)⁻¹ • x ^ 2‖ ≤ ‖x‖ ^ 2 / 2 := by
    rw [norm_smul, norm_inv]
    have : ‖x ^ 2‖ ≤ ‖x‖ ^ 2 := norm_pow_le' x (by norm_num)
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]; linarith
  have hphi : phi3 ‖x‖ ≤ ‖x‖ ^ 2 / 2 := by
    unfold phi3
    have := Real.abs_exp_sub_one_sub_id_le (x := ‖x‖) (by rw [abs_of_nonneg (norm_nonneg _)]; exact hx)
    rw [abs_le] at this
    linarith [this.2]
  calc ‖exp x - 1 - x‖ = ‖(exp x - 1 - x - (2 : ℂ)⁻¹ • x ^ 2) + (2 : ℂ)⁻¹ • x ^ 2‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖exp x - 1 - x - (2 : ℂ)⁻¹ • x ^ 2‖ + ‖(2 : ℂ)⁻¹ • x ^ 2‖ := norm_add_le _ _
    _ ≤ ‖x‖ ^ 2 := by linarith

/-- `‖e^xe^y - e^{x+y}‖ ≤ 7(‖x‖ + ‖y‖)²` for `‖x‖ + ‖y‖ ≤ 1`. -/
lemma norm_exp_mul_exp_sub_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x y : 𝔸) (h : ‖x‖ + ‖y‖ ≤ 1) :
    ‖exp x * exp y - exp (x + y)‖ ≤ 7 * (‖x‖ + ‖y‖) ^ 2 := by
  set t := ‖x‖ + ‖y‖
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  have e : exp x * exp y - exp (x + y) = (exp x - 1 - x) * exp y + (1 + x) * (exp y - 1 - y) +
      x * y - (exp (x + y) - 1 - (x + y)) := by noncomm_ring
  have hxy : ‖x + y‖ ≤ t := norm_add_le _ _
  have b1 : ‖exp x - 1 - x‖ ≤ t ^ 2 :=
    (norm_exp_sub_one_sub_le x (by linarith)).trans (by gcongr; linarith)
  have b2 : ‖exp y - 1 - y‖ ≤ t ^ 2 :=
    (norm_exp_sub_one_sub_le y (by linarith)).trans (by gcongr; linarith)
  have b3 : ‖exp (x + y) - 1 - (x + y)‖ ≤ t ^ 2 :=
    (norm_exp_sub_one_sub_le (x + y) (by linarith)).trans (by gcongr)
  have b4 : ‖exp y‖ ≤ 3 := by
    refine (norm_exp_le_of_one h1 y).trans ?_
    have := Real.exp_one_lt_d9
    have : Real.exp ‖y‖ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith
  have b5 : ‖1 + x‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
  have b6 : ‖x * y‖ ≤ t ^ 2 := (norm_mul_le _ _).trans (by nlinarith)
  rw [e]
  have hs : ‖(exp x - 1 - x) * exp y + (1 + x) * (exp y - 1 - y) + x * y - (exp (x + y) - 1 - (x + y))‖
      ≤ ‖(exp x - 1 - x) * exp y‖ + ‖(1 + x) * (exp y - 1 - y)‖ + ‖x * y‖ +
          ‖exp (x + y) - 1 - (x + y)‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_add₃_le)
  have m1 : ‖(exp x - 1 - x) * exp y‖ ≤ t ^ 2 * 3 :=
    (norm_mul_le _ _).trans (mul_le_mul b1 b4 (norm_nonneg _) (by positivity))
  have m2 : ‖(1 + x) * (exp y - 1 - y)‖ ≤ 2 * t ^ 2 :=
    (norm_mul_le _ _).trans (mul_le_mul b5 b2 (norm_nonneg _) (by norm_num))
  linarith

/-- `e^{nz} = (e^z)ⁿ`. -/
lemma exp_natCast_smul (z : 𝔸) (n : ℕ) : exp ((n : ℂ) • z) = exp z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul,
      BakerCampbellHausdorff.exp_add_of_commute' ℂ ((Commute.refl z).smul_left _), ih, pow_succ]

/-- `exp` is continuous (from the local Lipschitz bound `norm_exp_sub_exp_le`). -/
lemma continuous_exp_of_one (h1 : ‖(1 : 𝔸)‖ ≤ 1) : Continuous (exp : 𝔸 → 𝔸) := by
  refine Metric.continuous_iff.2 fun a ε hε => ?_
  set ρ := ‖a‖ + 1
  have hρ : 0 < Real.exp ρ + 1 := by positivity
  refine ⟨min 1 (ε / (Real.exp ρ + 1)), by positivity, fun b hb => ?_⟩
  rw [dist_eq_norm] at hb ⊢
  have hb1 : ‖b - a‖ < 1 := lt_of_lt_of_le hb (min_le_left _ _)
  have hb2 : ‖b - a‖ < ε / (Real.exp ρ + 1) := lt_of_lt_of_le hb (min_le_right _ _)
  have hbρ : ‖b‖ ≤ ρ := by
    have := norm_le_insert' b a
    have h' : ‖b‖ ≤ ‖a‖ + ‖b - a‖ := by
      calc ‖b‖ = ‖a + (b - a)‖ := by rw [add_sub_cancel]
        _ ≤ ‖a‖ + ‖b - a‖ := norm_add_le _ _
    linarith
  have haρ : ‖a‖ ≤ ρ := by linarith
  have hl := norm_exp_sub_exp_le h1 hbρ haρ
  rw [lt_div_iff₀ hρ] at hb2
  have : Real.exp ρ * ‖b - a‖ ≤ (Real.exp ρ + 1) * ‖b - a‖ := by nlinarith [norm_nonneg (b - a)]
  linarith

/-- The Lie product formula: `(e^{X/n}e^{Y/n})ⁿ → e^{X+Y}`. -/
theorem lie_product (h1 : ‖(1 : 𝔸)‖ ≤ 1) (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : ℂ)⁻¹ • X) * exp ((n : ℂ)⁻¹ • Y)) ^ n) atTop
      (𝓝 (exp (X + Y))) := by
  set s := ‖X‖ + ‖Y‖
  have hs0 : 0 ≤ s := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (7 * Real.exp s * s ^ 2))
  refine eventually_atTop.2 ⟨max 1 ⌈s⌉₊, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsn : s ≤ n := (Nat.le_ceil s).trans (by exact_mod_cast le_of_max_le_right hn)
  set x := (n : ℂ)⁻¹ • X
  set y := (n : ℂ)⁻¹ • Y
  have hnx : ‖x‖ = (n : ℝ)⁻¹ * ‖X‖ := by simp [x, norm_smul]
  have hny : ‖y‖ = (n : ℝ)⁻¹ * ‖Y‖ := by simp [y, norm_smul]
  have ht : ‖x‖ + ‖y‖ = s / n := by rw [hnx, hny]; field_simp; ring
  have ht1 : ‖x‖ + ‖y‖ ≤ 1 := by rw [ht, div_le_one hnpos]; exact hsn
  have hbn : exp (x + y) ^ n = exp (X + Y) := by
    rw [← exp_natCast_smul, ← smul_add, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_smul]
  have ha : ‖exp x * exp y‖ ≤ Real.exp (s / n) := by
    rw [← ht, Real.exp_add]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_exp_le_of_one h1 x) (norm_exp_le_of_one h1 y)
      (norm_nonneg _) (Real.exp_pos _).le)
  have hb : ‖exp (x + y)‖ ≤ Real.exp (s / n) := by
    rw [← ht]; exact (norm_exp_le_of_one h1 _).trans (Real.exp_le_exp.mpr (norm_add_le _ _))
  have hpow := norm_pow_sub_pow_le h1 ha hb n
  have hdiff := norm_exp_mul_exp_sub_le h1 x y ht1
  rw [ht] at hdiff
  have hexp : Real.exp (s / n) ^ (n - 1) ≤ Real.exp s := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc ((n - 1 : ℕ) : ℝ) * (s / n) ≤ n * (s / n) := by gcongr
      _ = s := by field_simp
  rw [← hbn]
  calc ‖(exp x * exp y) ^ n - exp (x + y) ^ n‖
      ≤ n * Real.exp (s / n) ^ (n - 1) * ‖exp x * exp y - exp (x + y)‖ := hpow
    _ ≤ n * Real.exp s * (7 * (s / n) ^ 2) := by gcongr
    _ = 7 * Real.exp s * s ^ 2 / n := by field_simp

end LieProduct

/-! ### The Lie algebra of a closed gauge group -/

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

namespace GaugeGroup

variable (G : GaugeGroup N)

/-- The set of the matrices of `G`. -/
def mats : Set Mat := {M | ∃ U ∈ G.carrier, ((U : GLN) : Mat) = M}

variable {G}

lemma expU_val (X : Mat) : ((expU X : GLN) : Mat) = exp X := rfl

lemma exp_mem_mats_iff (X : Mat) : exp X ∈ G.mats ↔ expU X ∈ G.carrier := by
  constructor
  · rintro ⟨U, hU, hUX⟩
    have : U = expU X := Units.ext (by rw [hUX, expU_val])
    rwa [← this]
  · intro h; exact ⟨_, h, rfl⟩

lemma mats_mul {M M' : Mat} (hM : M ∈ G.mats) (hM' : M' ∈ G.mats) : M * M' ∈ G.mats := by
  obtain ⟨U, hU, rfl⟩ := hM
  obtain ⟨U', hU', rfl⟩ := hM'
  exact ⟨U * U', G.carrier.mul_mem hU hU', by simp⟩

lemma mats_pow {M : Mat} (hM : M ∈ G.mats) (n : ℕ) : M ^ n ∈ G.mats := by
  induction n with
  | zero => exact ⟨1, G.carrier.one_mem, by simp⟩
  | succ n ih => rw [pow_succ]; exact mats_mul ih hM

lemma norm_one_le : ‖(1 : Mat)‖ ≤ 1 := norm_one_mat_le

/-- `e^{(it/n)A} ∈ G` for `A ∈ 𝔤`, in the form used for the product formula. -/
lemma exp_div_mem {A : Mat} (hA : A ∈ G.lie) (t : ℝ) (n : ℕ) :
    exp ((n : ℂ)⁻¹ • ((Complex.I * t) • A)) ∈ G.mats := by
  rw [exp_mem_mats_iff]
  have e : (n : ℂ)⁻¹ • ((Complex.I * t) • A) = (Complex.I * ((t / n : ℝ) : ℂ)) • A := by
    rw [smul_smul]; congr 1; push_cast; ring
  rw [e]; exact hA.2 _

/-- `𝔤` is closed under addition. -/
theorem add_mem_lie (hG : IsClosed G.mats) {A B : Mat} (hA : A ∈ G.lie) (hB : B ∈ G.lie) :
    A + B ∈ G.lie := by
  refine ⟨by rw [Matrix.conjTranspose_add, hA.1, hB.1], fun t => ?_⟩
  rw [← exp_mem_mats_iff, smul_add]
  refine hG.mem_of_tendsto (lie_product norm_one_le _ _) (Eventually.of_forall fun n => ?_)
  exact mats_pow (mats_mul (exp_div_mem hA t n) (exp_div_mem hB t n)) n

/-- `𝔤` is closed. -/
theorem isClosed_lie (hG : IsClosed G.mats) : IsClosed G.lie := by
  have e : G.lie = {A : Mat | A.conjTranspose = A} ∩ ⋂ t : ℝ, (fun A : Mat => exp ((Complex.I * t) • A)) ⁻¹' G.mats := by
    ext A
    simp only [GaugeGroup.lie, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, exp_mem_mats_iff]
  rw [e]
  refine IsClosed.inter (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id) ?_
  exact isClosed_iInter fun t => hG.preimage ((continuous_exp_of_one norm_one_le).comp (continuous_const_smul _))

lemma inv_val_eq_star {U : GLN} (hU : U ∈ G.carrier) : ((U⁻¹ : GLN) : Mat) = star (U : Mat) := by
  have h := G.unitary U hU
  rw [Matrix.mem_unitaryGroup_iff] at h
  calc ((U⁻¹ : GLN) : Mat) = ((U⁻¹ : GLN) : Mat) * ((U : Mat) * star (U : Mat)) := by rw [h, mul_one]
    _ = star (U : Mat) := by rw [← mul_assoc, Units.inv_mul, one_mul]

/-- `Ad_W B ∈ 𝔤` for `W ∈ G` and `B ∈ 𝔤`. -/
lemma Ad_mem_lie' {W : GLN} (hW : W ∈ G.carrier) {B : Mat} (hB : B ∈ G.lie) : Ad W B ∈ G.lie := by
  refine ⟨?_, fun s => ?_⟩
  · unfold Ad
    rw [inv_val_eq_star hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hB.1]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, mul_assoc]
  · rw [← Ad_smul, ← expU_conj]
    exact G.carrier.mul_mem (G.carrier.mul_mem hW (hB.2 s)) (G.carrier.inv_mem hW)

/-- `i[A, B] ∈ 𝔤` for `A, B ∈ 𝔤`. -/
theorem bracket_mem_lie (hG : IsClosed G.mats) {A B : Mat} (hA : A ∈ G.lie) (hB : B ∈ G.lie) :
    Complex.I • (A * B - B * A) ∈ G.lie := by
  set x : Mat := Complex.I • A
  -- the complex curve `z ↦ e^{zx} B e^{-zx}` and its derivative at `0`
  set g : ℂ → Mat := fun z => exp (z • x) * B * exp (z • (-x))
  have hg : HasDerivAt g (x * B - B * x) 0 := by
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℂ) x 0
    have h2 := hasDerivAt_exp_smul_const (𝕂 := ℂ) (-x) 0
    have h3 := (h1.mul (hasDerivAt_const (0 : ℂ) B)).mul h2
    convert h3 using 1
    simp [g]
    noncomm_ring
  set f : ℝ → Mat := fun t => g t
  have hf : HasDerivAt f (x * B - B * x) 0 := by
    have hh : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have hg' : HasDerivAt g (x * B - B * x) ((fun t : ℝ => (t : ℂ)) 0) := by
      simpa using hg
    have := hg'.scomp (0 : ℝ) hh
    simpa [f, Function.comp_def] using this
  have hslope := hf.tendsto_slope_zero
  have hval : x * B - B * x = Complex.I • (A * B - B * A) := by
    simp only [x, smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [hval] at hslope
  refine (isClosed_lie hG).mem_of_tendsto hslope (eventually_nhdsWithin_of_forall fun t _ => ?_)
  -- `f(t) = Ad_W B` with `W = e^{itA} ∈ G`
  have hW : expU ((Complex.I * t) • A) ∈ G.carrier := hA.2 t
  have hft : f (0 + t) = Ad (expU ((Complex.I * t) • A)) B := by
    have e1 : (t : ℂ) • x = (Complex.I * t) • A := by simp only [x, smul_smul]; ring_nf
    have e2 : (t : ℂ) • (-x) = -((Complex.I * t) • A) := by rw [smul_neg, e1]
    simp only [f, g, zero_add, e1, e2, Ad, expU_val, expU_inv_val]
  have hf0 : f 0 = B := by simp [f, g]
  rw [hft, hf0, ← Complex.coe_smul]
  refine G.smul_mem_lie ?_ _
  rw [sub_eq_add_neg]
  exact add_mem_lie hG (Ad_mem_lie' hW hB) (G.neg_mem_lie hB)

/-- `lem:lie-algebra`, the first sentence: for a gauge group whose matrices form a closed set,
`𝔤` is a real linear subspace closed under `(A, B) ↦ i[A, B]`. -/
theorem lieInput_of_isClosed (hG : IsClosed G.mats) : G.LieInput where
  add_mem _ hA _ hB := add_mem_lie hG hA hB
  bracket_mem _ hA _ hB := bracket_mem_lie hG hA hB

end GaugeGroup

end CoreLean

end
