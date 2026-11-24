/-
`lem:sf-decay` of BALABAN_CORE.tex (`542c68192a44`), the step "Conclusion", first part: the operator `Δ'_𝖺(𝐔)` of the
scalar form, its invertibility on the forms which vanish outside the Dirichlet domain, and the symmetry of its inverse
`G'`, in the model `Blocks.DomSeq` (`η = 1`, `a_j = Lʲ`).

* `avgL`, `PhiB`: the scalar form `Φ` of `SmallFieldDecay.Phi` as a bilinear form (`PhiB_apply`), symmetric
  (`PhiB_symm`).
* `DeltaS`: the symmetric operator of `Φ` with respect to `⟨f, g⟩ = Σ_x tr f(x)g(x)` (`PairConcrete.symOp`):
  `⟨Δ'f, g⟩ = Φ(f, g)` (`DeltaS_spec`).
* `piD`: the indicator of the Dirichlet domain, idempotent and symmetric; `Gp'`: the compressed inverse
  `CompressedInverse.cinv`.
* `deltaS_isUnit`: `Π_DΔ'Π_D` is invertible on the range of `Π_D` (`ckern` is a unit), from `eq:sf-conjugated` at `φ = 0`
  (the form is positive on the nonzero forms, `‖λ‖_w > 0`); `Gp'_symm`: `G'` is symmetric.
-/
import CoreLean.SmallFieldDecayPert
import CoreLean.PairConcrete
import CoreLean.CompressedInverse

open Finset
open scoped Classical RealInnerProductSpace Matrix.Norms.L2Operator
open Matrix
open LinearMap (BilinForm)

noncomputable section

namespace CoreLean
namespace SmallFieldDecay

open Blocks SmallFieldBlocks DiscretePoincare SmallFieldCoercivity SequenceOperators ConcretePairing
  CompressedInverse PairConcrete

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n] (S : DomSeq n)

/-- The spacing `a₀ = 1`. -/
abbrev a1 : ℂ := ((1 : ℝ) : ℂ)

/-- The averages at the points of `𝐁` as a linear map. -/
def avgL (W : Site n → Site n → GLN) : (Site n → Mat) →ₗ[ℂ] (detB S → Mat) where
  toFun f y := avgW S W y.1 f
  map_add' f g := by
    funext y
    simp only [avgW, Pi.add_apply, Ad_add, sum_add_distrib, smul_add]
  map_smul' c f := by
    funext y
    simp only [avgW, Pi.smul_apply, Ad_smul, RingHom.id_apply, ← smul_sum]
    rw [smul_comm]

/-- The weights `𝖺_{j(y)}a_{j(y)}²`. -/
def cw (y : detB S) : ℂ := ((aseq 1 S.L (S.sc y.1) * (S.L : ℝ) ^ (2 * S.sc y.1) : ℝ) : ℂ)

/-- The scalar form as a bilinear form. -/
def PhiB (U : Config N n) (W : Site n → Site n → GLN) : BilinForm ℂ (Site n → Mat) :=
  (pairForm1 a1).compl₁₂ (D0L a1 U) (D0L a1 U) + (wpair (cw S)).compl₁₂ (avgL S W) (avgL S W)

lemma D0L_a1 (U : Config N n) (f : Site n → Mat) (μ : Fin 4) (x : Site n) : D0L a1 U f μ x = DU U f μ x := by
  simp [D0L, D0, Dfw, DU]

theorem PhiB_apply (U : Config N n) (W : Site n → Site n → GLN) (f g : Site n → Mat) :
    PhiB S U W f g = Phi S U W f g := by
  simp only [PhiB, LinearMap.add_apply, LinearMap.compl₁₂_apply, pairForm1_apply', wpair_apply, D0L_a1,
    Phi, avgL, LinearMap.coe_mk, AddHom.coe_mk, cw]
  congr 1
  · rw [Finset.sum_comm]; simp
  · exact Finset.sum_coe_sort (detB S) (fun y => ((aseq 1 S.L (S.sc y) * (S.L : ℝ) ^ (2 * S.sc y) : ℝ) : ℂ) *
      ntr (avgW S W y f * avgW S W y g))

theorem PhiB_symm (U : Config N n) (W : Site n → Site n → GLN) (f g : Site n → Mat) :
    PhiB S U W f g = PhiB S U W g f := by
  simp only [PhiB, LinearMap.add_apply, LinearMap.compl₁₂_apply]
  rw [pairForm1_symm, wpair_symm]

/-- The pairing `⟨f, g⟩ = Σ_x tr f(x)g(x)`, nondegenerate. -/
abbrev P0 : BilinForm ℂ (Site n → Mat) := pairForm0 (N := N) (n := n) a1

lemma P0_nondeg : (P0 (N := N) (n := n)).Nondegenerate := pairForm0_nondegenerate one_pos

/-- **The operator** `Δ'_𝖺(𝐔)` of the scalar form. -/
def DeltaS (U : Config N n) (W : Site n → Site n → GLN) : Module.End ℂ (Site n → Mat) :=
  symOp P0 P0_nondeg (PhiB S U W)

theorem DeltaS_spec (U : Config N n) (W : Site n → Site n → GLN) (f g : Site n → Mat) :
    P0 (DeltaS S U W f) g = Phi S U W f g := by
  rw [DeltaS, symOp_spec, PhiB_symm S U W g f, ← PhiB_apply]; ring

theorem DeltaS_symm (U : Config N n) (W : Site n → Site n → GLN) (f g : Site n → Mat) :
    P0 (DeltaS S U W f) g = P0 f (DeltaS S U W g) :=
  symOp_symm (wpair_symm _) f g

/-! ### The Dirichlet domain -/

/-- The indicator of the Dirichlet domain. -/
def piD (ΩD : Set (Site n)) : Module.End ℂ (Site n → Mat) where
  toFun f := ΩD.indicator f
  map_add' f g := by funext x; by_cases hx : x ∈ ΩD <;> simp [Set.indicator_apply, hx]
  map_smul' c f := by funext x; by_cases hx : x ∈ ΩD <;> simp [Set.indicator_apply, hx]

lemma piD_apply (ΩD : Set (Site n)) (f : Site n → Mat) (x : Site n) :
    piD ΩD f x = if x ∈ ΩD then f x else 0 := Set.indicator_apply _ _ _

lemma piD_idem (ΩD : Set (Site n)) (f : Site n → Mat) : piD ΩD (piD ΩD f) = piD ΩD f := by
  funext x; simp only [piD_apply]; split_ifs <;> rfl

lemma piD_symm (ΩD : Set (Site n)) (f g : Site n → Mat) : P0 (piD ΩD f) g = P0 f (piD ΩD g) := by
  simp only [P0, pairForm0, wpair_apply, piD_apply]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp [ntr]

/-- `G' = (Δ'_𝖺)^{-1}` on the forms which vanish outside `Ω_D`. -/
def Gp' (U : Config N n) (W : Site n → Site n → GLN) (ΩD : Set (Site n)) : Module.End ℂ (Site n → Mat) :=
  cinv (piD ΩD) (DeltaS S U W)

/-! ### Invertibility and symmetry -/

lemma conjL_zero (lam : Site n → Mat) : conjL (fun _ => (0 : ℝ)) lam = fun x => (lam x)ᴴ := by
  funext x; simp [conjL]

lemma conjR_zero (lam : Site n → Mat) : conjR (fun _ => (0 : ℝ)) lam = lam := by
  funext x; simp [conjR]

lemma eq_zero_of_wnormM [NeZero N] (lam : Site n → Mat) (h : wnormM S lam ≤ 0) : lam = 0 := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast (show 0 < S.L by have := S.three_le_L; omega)
  have hnn : ∀ x ∈ (univ : Finset (Site n)), 0 ≤ ((S.L : ℝ) ^ (2 * S.sc x))⁻¹ * hs2 (lam x) :=
    fun x _ => mul_nonneg (by positivity) (hs2_nonneg _)
  have hz := (sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm h (sum_nonneg hnn))
  funext x
  have := hz x (mem_univ x)
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (by positivity)
  · have h2 : hs (lam x) = 0 := by rw [hs, h1, Real.sqrt_zero]
    exact eq_zero_of_hs h2

/-- **`Δ'_𝖺(𝐔)` is invertible on the forms which vanish outside `Ω_D`**, under the hypotheses of `eq:sf-conjugated`
at `φ = 0`. -/
theorem deltaS_isUnit [NeZero N] (U : Config N n) (W : Site n → Site n → GLN) (ΩD : Set (Site n)) (eps η : ℝ)
    (heps : 0 ≤ eps) (hη : 0 ≤ η)
    (hE : ∀ x μ, ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z)
    (hW1 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW2 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z)
    (hsmall : (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8) :
    IsUnit (ckern (piD ΩD) (DeltaS S U W)) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hP := piD_idem (N := N) ΩD
  -- `f` lies in the range of `Π` and `ΠΔ'f = 0`
  have h1 : piD ΩD (DeltaS S U W (piD ΩD f)) = 0 := by
    have := congrArg (piD ΩD) hf
    rw [P_ckern (fun x => hP x), map_zero] at this
    exact this
  have hfP : piD ΩD f = f := by
    have e := ckern_apply (P := piD ΩD) (T := DeltaS S U W) f
    rw [hf, h1, zero_add] at e
    exact (sub_eq_zero.1 e.symm).symm
  rw [hfP] at h1
  -- the form at `(f^*, f)` vanishes
  have hfs : piD ΩD (fun x => (f x)ᴴ) = fun x => (f x)ᴴ := by
    funext x
    have := congrFun hfP x
    simp only [piD_apply] at this ⊢
    split_ifs with hx
    · rfl
    · rw [if_neg hx] at this; rw [← this]; simp
  have hzero : Phi S U W (conjL (fun _ => (0 : ℝ)) f) (conjR (fun _ => (0 : ℝ)) f) = 0 := by
    rw [conjL_zero, conjR_zero, ← PhiB_apply, PhiB_symm, PhiB_apply, ← DeltaS_spec, ← hfs, ← piD_symm, h1,
      map_zero, LinearMap.zero_apply]
  have hconj := sf_conjugated S U W (fun _ => 0) f 0 eps η le_rfl (by positivity) heps hη
    (fun x μ => by simp) (fun y _ x _ => by simp) hE hW1 hW2 hsmall
  rw [hzero, Complex.zero_re] at hconj
  have hD : 0 ≤ dsqM f := by unfold dsqM; exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => hs2_nonneg _
  exact eq_zero_of_wnormM S f (by linarith)

/-- **`G'` is symmetric** with respect to `⟨·,·⟩`. -/
theorem Gp'_symm (U : Config N n) (W : Site n → Site n → GLN) (ΩD : Set (Site n))
    (hK : IsUnit (ckern (piD ΩD) (DeltaS S U W))) (f g : Site n → Mat) :
    P0 (Gp' S U W ΩD f) g = P0 f (Gp' S U W ΩD g) :=
  cinv_symm P0 (piD_idem ΩD) (piD_symm ΩD) (fun a b _ _ => DeltaS_symm S U W a b) hK f g

/-! ### The decay of `G'`: `eq:sf-decay` -/

/-- `e^φv`. -/
def expS (ph : Site n → ℝ) (v : Site n → Mat) : Site n → Mat := fun x => ((Real.exp (ph x) : ℝ) : ℂ) • v x

/-- `‖e^φf‖²_{w⁻¹} = Σ_x a_{j(x)}²e^{2φ(x)}|f(x)|²`. -/
def fwinv (ph : Site n → ℝ) (f : Site n → Mat) : ℝ :=
  ∑ x, (S.L : ℝ) ^ (2 * S.sc x) * Real.exp (2 * ph x) * hs2 (f x)

/-- `‖e^φg‖₂² = Σ_μΣ_x e^{2φ(x)}|g_μ(x)|²`. -/
def gnorm (ph : Site n → ℝ) (g : Form1 N n) : ℝ := ∑ x, ∑ μ : Fin 4, Real.exp (2 * ph x) * hs2 (g μ x)

omit [NeZero n] in
lemma conjR_expS (ph : Site n → ℝ) (v : Site n → Mat) : conjR ph (expS ph v) = v := by
  funext x
  simp only [conjR, expS, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    Complex.ofReal_one, one_smul]

lemma piD_conjL (ΩD : Set (Site n)) (ph : Site n → ℝ) (v : Site n → Mat) (hv : piD ΩD v = v) :
    piD ΩD (conjL ph (expS ph v)) = conjL ph (expS ph v) := by
  funext x
  have h := congrFun hv x
  simp only [piD_apply] at h ⊢
  split_ifs with hx
  · rfl
  · rw [if_neg hx] at h
    simp [conjL, expS, ← h]

/-- **The bond term of `D_𝐔(e^φu^*)`**: `|D_𝐔(e^φu^*)(b)| ≤ e^{φ(x)}(|∂u(b)| + 2ω_b)` if `ε ≤ ½`. -/
theorem DU_conjL_le [NeZero N] (U : Config N n) (ph : Site n → ℝ) (u : Site n → Mat) (δ eps : ℝ)
    (hδ0 : 0 ≤ δ) (hδL : δ * S.L ≤ 1 / 128) (heps2 : eps ≤ 1 / 2) (x : Site n) (μ : Fin 4)
    (hph : |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹)
    (hE : ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z) :
    hs (DU U (conjL ph u) μ x) ≤ Real.exp (ph x) * (hs (u (x + unit n μ) - u x) + 2 * omg S u x μ) := by
  obtain ⟨x', hx'⟩ : ∃ x', x' = x + unit n μ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = S.L * ((S.L : ℝ) ^ S.sc x')⁻¹ := ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = ph x' - ph x := ⟨_, rfl⟩
  rw [← hx'] at hph hE ⊢
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (by have := S.three_le_L; omega : 1 ≤ S.L)
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwle : w ≤ S.L := by
    have : ((S.L : ℝ) ^ S.sc x')⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    rw [hw]; nlinarith
  have hsb : |s| ≤ δ * w := by rw [hsd, hw, ← mul_assoc]; exact hph
  have hs128 : |s| ≤ 1 / 128 := by
    have : δ * w ≤ δ * S.L := mul_le_mul_of_nonneg_left hwle hδ0
    linarith
  obtain ⟨hexp2, hexps⟩ := exp_small hs128
  obtain ⟨D, hD⟩ : ∃ D, D = hs (u x' - u x) := ⟨_, rfl⟩
  have hom : omg S u x μ = w * hs (u x') := by rw [omg, hw, ← hx']
  rw [← hD, hom]
  obtain ⟨om, hom'⟩ : ∃ om, om = w * hs (u x') := ⟨_, rfl⟩
  rw [← hom']
  have hom0 : 0 ≤ om := by rw [hom']; exact mul_nonneg hw0 (hs_nonneg _)
  have hD0 : 0 ≤ D := by rw [hD]; exact hs_nonneg _
  have e1 : DU U (conjL ph u) μ x = (conjL ph u x' - conjL ph u x) +
      (Ad (U μ x) (conjL ph u x') - conjL ph u x') := by simp only [DU, ← hx']; abel
  rw [e1]
  have hep := Real.exp_pos (ph x)
  have hsx : ph x + s = ph x' := by rw [hsd]; ring
  have ha : hs (conjL ph u x' - conjL ph u x) ≤ Real.exp (ph x) * (D + om) := by
    have ea : conjL ph u x' - conjL ph u x = ((Real.exp (ph x) : ℝ) : ℂ) • (u x' - u x)ᴴ +
        (((Real.exp (ph x') - Real.exp (ph x) : ℝ) : ℂ) • (u x')ᴴ) := by
      simp only [conjL, conjTranspose_sub, smul_sub, Complex.ofReal_sub, sub_smul]; abel
    rw [ea]
    refine (hs_add_le _ _).trans ?_
    rw [hs_rsmul, hs_rsmul, hs_conjTranspose, hs_conjTranspose, abs_of_pos hep, ← hD]
    have hd : |Real.exp (ph x') - Real.exp (ph x)| ≤ Real.exp (ph x) * w := by
      have e : Real.exp (ph x') - Real.exp (ph x) = Real.exp (ph x) * (Real.exp s - 1) := by
        rw [mul_sub, mul_one, ← Real.exp_add, hsx]
      rw [e, abs_mul, abs_of_pos hep]
      refine mul_le_mul_of_nonneg_left (hexps.trans ?_) hep.le
      nlinarith
    have := mul_le_mul_of_nonneg_right hd (hs_nonneg (u x'))
    rw [hom']; nlinarith
  have hμ : hs (conjL ph u x') = Real.exp (ph x') * hs (u x') := by
    simp only [conjL, hs_rsmul, hs_conjTranspose, abs_of_pos (Real.exp_pos _)]
  have hb : hs (Ad (U μ x) (conjL ph u x') - conjL ph u x') ≤ eps * Real.exp (ph x') * om := by
    calc hs (Ad (U μ x) (conjL ph u x') - conjL ph u x')
        ≤ eps * S.L * ((S.L : ℝ) ^ S.sc x')⁻¹ * hs (conjL ph u x') := hE _
      _ = eps * Real.exp (ph x') * om := by rw [hμ, hom', hw]; ring
  have hr : Real.exp (ph x') ≤ 2 * Real.exp (ph x) := by
    rw [← hsx, Real.exp_add]
    have : Real.exp s ≤ 2 := (Real.exp_le_exp.2 (le_abs_self s)).trans hexp2
    nlinarith
  have hb' : hs (Ad (U μ x) (conjL ph u x') - conjL ph u x') ≤ Real.exp (ph x) * om := by
    have heps' : eps * Real.exp (ph x') ≤ Real.exp (ph x) := by
      rcases le_or_gt eps 0 with h0 | h0
      · nlinarith [Real.exp_pos (ph x')]
      · nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_right heps' hom0)
  calc hs ((conjL ph u x' - conjL ph u x) + (Ad (U μ x) (conjL ph u x') - conjL ph u x'))
      ≤ hs (conjL ph u x' - conjL ph u x) + hs (Ad (U μ x) (conjL ph u x') - conjL ph u x') := hs_add_le _ _
    _ ≤ Real.exp (ph x) * (D + om) + Real.exp (ph x) * om := add_le_add ha hb'
    _ = Real.exp (ph x) * (D + 2 * om) := by ring

/-- **The first pairing**: `|⟨f, e^φu^*⟩| ≤ ‖e^φf‖_{w⁻¹}‖u‖_w`. -/
theorem pair_f_le [NeZero N] (ph : Site n → ℝ) (f u : Site n → Mat) :
    ‖P0 f (conjL ph u)‖ ≤ Real.sqrt (fwinv S ph f) * Real.sqrt (wnormM S u) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast (show 0 < S.L by have := S.three_le_L; omega)
  simp only [P0, pairForm0, wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul]
  calc _ ≤ ∑ x, ((S.L : ℝ) ^ S.sc x * Real.exp (ph x) * hs (f x)) * (((S.L : ℝ) ^ S.sc x)⁻¹ * hs (u x)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
        have hpos : (0 : ℝ) < (S.L : ℝ) ^ S.sc x := pow_pos hL _
        refine (norm_ntr_mul_le _ _).trans (le_of_eq ?_)
        simp only [conjL, hs_rsmul, hs_conjTranspose, abs_of_pos (Real.exp_pos _)]
        field_simp
    _ ≤ Real.sqrt (∑ x, ((S.L : ℝ) ^ S.sc x * Real.exp (ph x) * hs (f x)) ^ 2) *
          Real.sqrt (∑ x, (((S.L : ℝ) ^ S.sc x)⁻¹ * hs (u x)) ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (fwinv S ph f) * Real.sqrt (wnormM S u) := by
        congr 2
        · unfold fwinv
          refine sum_congr rfl fun x _ => ?_
          rw [mul_pow, mul_pow, hs_sq, ← pow_mul, mul_comm (S.sc x) 2, sq (Real.exp _), ← Real.exp_add, ← two_mul]
        · unfold wnormM
          refine sum_congr rfl fun x _ => ?_
          rw [mul_pow, hs_sq, inv_pow, ← pow_mul, mul_comm (S.sc x) 2]

lemma sum_omg_sq (u : Site n → Mat) :
    ∑ p : Site n × Fin 4, omg S u p.1 p.2 ^ 2 = (2 * S.L) ^ 2 * wnormM S u := by
  simp only [Fintype.sum_prod_type]; rw [Finset.sum_comm]
  have h : ∀ μ : Fin 4, ∑ x, omg S u x μ ^ 2 = (S.L : ℝ) ^ 2 * wnormM S u := fun μ => by
    have hs := sum_shift (n := n) μ (fun x => ((S.L : ℝ) * ((S.L : ℝ) ^ S.sc x)⁻¹ * hs (u x)) ^ 2)
    beta_reduce at hs
    simp only [omg]
    rw [hs]
    unfold wnormM
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_pow, mul_pow, hs_sq, inv_pow, ← pow_mul, mul_comm (S.sc x) 2, mul_assoc]
  rw [sum_congr rfl fun μ _ => h μ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **The second pairing**: `|⟨D_𝐔(e^φu^*), g⟩| ≤ (‖∂u‖₂ + 4L‖u‖_w)‖e^φg‖₂`. -/
theorem pair_g_le [NeZero N] (U : Config N n) (ph : Site n → ℝ) (u : Site n → Mat) (g : Form1 N n) (δ eps : ℝ)
    (hδ0 : 0 ≤ δ) (hδL : δ * S.L ≤ 1 / 128) (heps2 : eps ≤ 1 / 2)
    (hph : ∀ x μ, |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹)
    (hE : ∀ x μ, ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z) :
    ‖pairForm1 a1 (D0L a1 U (conjL ph u)) g‖ ≤
      (Real.sqrt (dsqM u) + 4 * S.L * Real.sqrt (wnormM S u)) * Real.sqrt (gnorm ph g) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast (show 0 < S.L by have := S.three_le_L; omega)
  simp only [pairForm1_apply', wpair_apply, D0L_a1]
  simp only [a1, Complex.ofReal_one, one_pow, one_mul]
  rw [Finset.sum_comm]
  have hW0 : 0 ≤ wnormM S u := sum_nonneg fun x _ => mul_nonneg (by positivity) (hs2_nonneg _)
  calc _ ≤ ∑ x, ∑ μ : Fin 4, hs (DU U (conjL ph u) μ x) * hs (g μ x) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
        exact (norm_sum_le _ _).trans (sum_le_sum fun μ _ => norm_ntr_mul_le _ _)
    _ ≤ ∑ x, ∑ μ : Fin 4, (hs (u (x + unit n μ) - u x) + 2 * omg S u x μ) * (Real.exp (ph x) * hs (g μ x)) := by
        refine sum_le_sum fun x _ => sum_le_sum fun μ _ => ?_
        have := DU_conjL_le S U ph u δ eps hδ0 hδL heps2 x μ (hph x μ) (hE x μ)
        calc hs (DU U (conjL ph u) μ x) * hs (g μ x)
            ≤ (Real.exp (ph x) * (hs (u (x + unit n μ) - u x) + 2 * omg S u x μ)) * hs (g μ x) :=
              mul_le_mul_of_nonneg_right this (hs_nonneg _)
          _ = _ := by ring
    _ = ∑ p : Site n × Fin 4, hs (u (p.1 + unit n p.2) - u p.1) * (Real.exp (ph p.1) * hs (g p.2 p.1)) +
          2 * ∑ p : Site n × Fin 4, omg S u p.1 p.2 * (Real.exp (ph p.1) * hs (g p.2 p.1)) := by
        simp only [Fintype.sum_prod_type]; rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun μ _ => by ring
    _ ≤ Real.sqrt (∑ p : Site n × Fin 4, hs (u (p.1 + unit n p.2) - u p.1) ^ 2) *
          Real.sqrt (∑ p : Site n × Fin 4, (Real.exp (ph p.1) * hs (g p.2 p.1)) ^ 2) +
        2 * (Real.sqrt (∑ p : Site n × Fin 4, omg S u p.1 p.2 ^ 2) *
          Real.sqrt (∑ p : Site n × Fin 4, (Real.exp (ph p.1) * hs (g p.2 p.1)) ^ 2)) :=
        add_le_add (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
          (mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by norm_num))
    _ = (Real.sqrt (dsqM u) + 4 * S.L * Real.sqrt (wnormM S u)) * Real.sqrt (gnorm ph g) := by
        have e1 : ∑ p : Site n × Fin 4, hs (u (p.1 + unit n p.2) - u p.1) ^ 2 = dsqM u := by
          simp only [Fintype.sum_prod_type]; unfold dsqM; simp only [hs_sq]
        have e2 : ∑ p : Site n × Fin 4, (Real.exp (ph p.1) * hs (g p.2 p.1)) ^ 2 = gnorm ph g := by
          simp only [Fintype.sum_prod_type]; unfold gnorm
          refine sum_congr rfl fun x _ => sum_congr rfl fun μ _ => ?_
          rw [mul_pow, hs_sq, sq (Real.exp _), ← Real.exp_add, ← two_mul]
        have e3 : Real.sqrt (∑ p : Site n × Fin 4, omg S u p.1 p.2 ^ 2) = 2 * S.L * Real.sqrt (wnormM S u) := by
          rw [sum_omg_sq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
        rw [e1, e2, e3]; ring

/-- The arithmetic of the last step of `lem:sf-decay`. -/
lemma decay_alg {A B Wn Dn L : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ Wn) (hD : 0 ≤ Dn) (hL : 3 ≤ L)
    (key : (1 / 8) * (Dn ^ 2 + Wn ^ 2) ≤ A * Wn + (Dn + 4 * L * Wn) * B) :
    Wn + Dn ≤ 12 * (A + 6 * L * B) := by
  obtain ⟨M, hM⟩ : ∃ M, M = Real.sqrt (Dn ^ 2 + Wn ^ 2) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact Real.sqrt_nonneg _
  have hMsq : M ^ 2 = Dn ^ 2 + Wn ^ 2 := by rw [hM]; exact Real.sq_sqrt (by positivity)
  have hWM : Wn ≤ M := by
    calc Wn = Real.sqrt (Wn ^ 2) := (Real.sqrt_sq hW).symm
      _ ≤ M := by rw [hM]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hDM : Dn ≤ M := by
    calc Dn = Real.sqrt (Dn ^ 2) := (Real.sqrt_sq hD).symm
      _ ≤ M := by rw [hM]; exact Real.sqrt_le_sqrt (by nlinarith)
  obtain ⟨T, hT⟩ : ∃ T, T = A + (1 + 4 * L) * B := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; exact add_nonneg hA (mul_nonneg (by linarith) hB)
  have hMT : M * M ≤ M * (8 * T) := by
    have h0 : M ^ 2 ≤ 8 * (A * Wn + (Dn + 4 * L * Wn) * B) := by rw [hMsq]; linarith
    calc M * M = M ^ 2 := by ring
      _ ≤ 8 * (A * Wn + (Dn + 4 * L * Wn) * B) := h0
      _ ≤ 8 * (A * M + (M + 4 * L * M) * B) := by
          have h4 : 0 ≤ 4 * L := by linarith
          gcongr
      _ = M * (8 * T) := by rw [hT]; ring
  have hM8 : M ≤ 8 * T := by
    rcases hM0.eq_or_lt with h | h
    · rw [← h]; linarith
    · exact le_of_mul_le_mul_left hMT h
  have h1 : (Wn + Dn) ^ 2 ≤ 2 * M ^ 2 := by rw [hMsq]; nlinarith [sq_nonneg (Wn - Dn)]
  have h2 : M ^ 2 ≤ (8 * T) ^ 2 := pow_le_pow_left₀ hM0 hM8 2
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ L = t + 3 := ⟨L - 3, by linarith, by ring⟩
  have h3 : 2 * (8 * T) ^ 2 ≤ (12 * (A + 6 * (t + 3) * B)) ^ 2 := by
    have e : (12 * (A + 6 * (t + 3) * B)) ^ 2 - 2 * (8 * T) ^ 2 =
        16 * A ^ 2 + (704 * t + 1856) * (A * B) + (3136 * t ^ 2 + 17792 * t + 25024) * B ^ 2 := by
      rw [hT]; ring
    have hpos : 0 ≤ 16 * A ^ 2 + (704 * t + 1856) * (A * B) + (3136 * t ^ 2 + 17792 * t + 25024) * B ^ 2 :=
      add_nonneg (add_nonneg (by positivity) (mul_nonneg (by linarith) (mul_nonneg hA hB)))
        (mul_nonneg (by nlinarith [sq_nonneg t]) (sq_nonneg B))
    linarith
  have hR : 0 ≤ 12 * (A + 6 * (t + 3) * B) :=
    mul_nonneg (by norm_num) (add_nonneg hA (mul_nonneg (by linarith) hB))
  calc Wn + Dn = Real.sqrt ((Wn + Dn) ^ 2) := (Real.sqrt_sq (add_nonneg hW hD)).symm
    _ ≤ Real.sqrt ((12 * (A + 6 * (t + 3) * B)) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = 12 * (A + 6 * (t + 3) * B) := Real.sqrt_sq hR

/-- **`eq:sf-decay`** in the model: with `u = e^φG'(f + D^*_𝐔g)`,
`‖u‖_w + ‖∂u‖₂ ≤ 12(‖e^φf‖_{w⁻¹} + 6L‖e^φg‖₂)`, for every `0`-form `f` and every `1`-form `g`, under the hypotheses of
`eq:sf-conjugated`. -/
theorem sf_decay [NeZero N] (U : Config N n) (W : Site n → Site n → GLN) (ΩD : Set (Site n)) (ph : Site n → ℝ)
    (δ eps η : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L)) (heps : 0 ≤ eps) (hη : 0 ≤ η)
    (hbond : ∀ x μ, |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc x)⁻¹ ∧
      |ph (x + unit n μ) - ph x| ≤ δ * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹)
    (hblock : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, |ph x - ph y| ≤ 2 * δ)
    (hE : ∀ x μ, ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z)
    (hW1 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW2 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z)
    (hsmall : (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8)
    (f : Site n → Mat) (g : Form1 N n) :
    Real.sqrt (wnormM S (expS ph (Gp' S U W ΩD (f + Ds1L a1 U g)))) +
        Real.sqrt (dsqM (expS ph (Gp' S U W ΩD (f + Ds1L a1 U g)))) ≤
      12 * (Real.sqrt (fwinv S ph f) + 6 * S.L * Real.sqrt (gnorm ph g)) := by
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hLpos : (0 : ℝ) < S.L := by linarith
  have hδL : δ * S.L ≤ 1 / 128 := by
    calc δ * S.L ≤ 1 / (128 * S.L) * S.L := mul_le_mul_of_nonneg_right hδ hLpos.le
      _ = 1 / 128 := by field_simp
  have heps2 : eps ≤ 1 / 2 := by
    have h54 : (54 : ℝ) ≤ 6 * (S.L : ℝ) ^ 2 := by nlinarith
    have h1 : 4 * eps * 54 ≤ (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) := by
      have := mul_le_mul_of_nonneg_left h54 (by linarith : 0 ≤ 4 * eps)
      have h2 : 0 ≤ eps ^ 2 * (6 * (S.L : ℝ) ^ 2) := by positivity
      nlinarith
    have h3 : 0 ≤ 6 * Real.sqrt N * η := by positivity
    linarith
  have hK := deltaS_isUnit S U W ΩD eps η heps hη hE hW1 hW2 hsmall
  obtain ⟨v, hv⟩ : ∃ v, v = Gp' S U W ΩD (f + Ds1L a1 U g) := ⟨_, rfl⟩
  rw [← hv]
  have hP := piD_idem (N := N) ΩD
  have hvP : piD ΩD v = v := by rw [hv]; exact P_cinv hP _
  have hLP : piD ΩD (conjL ph (expS ph v)) = conjL ph (expS ph v) := piD_conjL ΩD ph v hvP
  obtain ⟨u, hu⟩ : ∃ u, u = expS ph v := ⟨_, rfl⟩
  rw [← hu] at hLP ⊢
  have hR : conjR ph u = v := by rw [hu]; exact conjR_expS ph v
  have hconj := sf_conjugated S U W ph u δ eps η hδ0 hδ heps hη hbond hblock hE hW1 hW2 hsmall
  rw [hR] at hconj
  -- the form at `(e^φu^*, v)` is `⟨f + D^*g, e^φu^*⟩`
  have hform : Phi S U W (conjL ph u) v = P0 (f + Ds1L a1 U g) (conjL ph u) := by
    calc Phi S U W (conjL ph u) v = Phi S U W v (conjL ph u) := by rw [← PhiB_apply, PhiB_symm, PhiB_apply]
      _ = P0 (DeltaS S U W v) (piD ΩD (conjL ph u)) := by rw [DeltaS_spec, hLP]
      _ = P0 (piD ΩD (DeltaS S U W v)) (conjL ph u) := (piD_symm ΩD _ _).symm
      _ = P0 (piD ΩD (f + Ds1L a1 U g)) (conjL ph u) := by rw [hv, Gp', P_T_cinv hP hK]
      _ = P0 (f + Ds1L a1 U g) (conjL ph u) := by rw [piD_symm, hLP]
  have hsplit : P0 (f + Ds1L a1 U g) (conjL ph u) =
      P0 f (conjL ph u) + pairForm1 a1 (D0L a1 U (conjL ph u)) g := by
    have e : P0 (Ds1L a1 U g) (conjL ph u) = pairForm0 a1 (conjL ph u) (Ds1L a1 U g) := wpair_symm _ _ _
    rw [map_add, LinearMap.add_apply, D0L_transpose, e]
  have hre : (Phi S U W (conjL ph u) v).re ≤
      ‖P0 f (conjL ph u)‖ + ‖pairForm1 a1 (D0L a1 U (conjL ph u)) g‖ := by
    rw [hform, hsplit]; exact (Complex.re_le_norm _).trans (norm_add_le _ _)
  have hf := pair_f_le S ph f u
  have hg := pair_g_le S U ph u g δ eps hδ0 hδL heps2 (fun x μ => (hbond x μ).2) hE
  have hW0 : 0 ≤ wnormM S u := sum_nonneg fun x _ => mul_nonneg (by positivity) (hs2_nonneg _)
  have hD0 : 0 ≤ dsqM u := sum_nonneg fun _ _ => sum_nonneg fun _ _ => hs2_nonneg _
  have hWsq := Real.sq_sqrt hW0
  have hDsq := Real.sq_sqrt hD0
  refine decay_alg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hL3 ?_
  rw [hWsq, hDsq]
  linarith

/-! ### Forms with values in `𝔤`

With the convention `𝐔 = e^{ia₀A'}` the forms with values in `𝔤` are those with `λ^* = λ` (`cstar λ = λ`), and a gauge
field has unitary transports. -/

/-- `λ ↦ λ^*`, pointwise. -/
def cstar (f : Site n → Mat) : Site n → Mat := fun x => (f x)ᴴ

omit [NeZero n] in
lemma cstar_cstar (f : Site n → Mat) : cstar (cstar f) = f := by funext x; simp [cstar]

omit [NeZero n] in
lemma cstar_add (f g : Site n → Mat) : cstar (f + g) = cstar f + cstar g := by
  funext x; simp [cstar, conjTranspose_add]

omit [NeZero n] in
lemma cstar_sub (f g : Site n → Mat) : cstar (f - g) = cstar f - cstar g := by
  funext x; simp [cstar, conjTranspose_sub]

omit [NeZero n] in
lemma cstar_zero : cstar (0 : Site n → Mat) = 0 := by funext x; simp [cstar]

lemma inv_coe_unitary {W : GLN} (hW : (W : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    ((W⁻¹ : GLN) : Mat) = (W : Mat)ᴴ :=
  Units.inv_eq_of_mul_eq_one_right (by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 hW)

lemma Ad_conjTranspose {W : GLN} (hW : (W : Mat) ∈ unitaryGroup (Fin N) ℂ) (X : Mat) :
    (Ad W X)ᴴ = Ad W Xᴴ := by
  simp only [Ad, inv_coe_unitary hW, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma ntr_conj_mul (X Y : Mat) : ntr (Xᴴ * Y) = starRingEnd ℂ (ntr (X * Yᴴ)) := by
  rw [← ntr_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, ntr_mul_comm]

omit [NeZero n] in
lemma DU_cstar (U : Config N n) (hU : ∀ μ x, (U μ x : Mat) ∈ unitaryGroup (Fin N) ℂ) (f : Site n → Mat)
    (μ : Fin 4) (x : Site n) : DU U (cstar f) μ x = (DU U f μ x)ᴴ := by
  simp only [DU, cstar, conjTranspose_sub, Ad_conjTranspose (hU μ x)]

lemma avgW_cstar (W : Site n → Site n → GLN) (hW : ∀ y x, (W y x : Mat) ∈ unitaryGroup (Fin N) ℂ) (y : Site n)
    (f : Site n → Mat) : avgW S W y (cstar f) = (avgW S W y f)ᴴ := by
  simp only [avgW, cstar, conjTranspose_smul, conjTranspose_sum, Ad_conjTranspose (hW _ _)]
  congr 1
  simp [Complex.conj_ofReal]

theorem Phi_cstar (U : Config N n) (W : Site n → Site n → GLN)
    (hU : ∀ μ x, (U μ x : Mat) ∈ unitaryGroup (Fin N) ℂ) (hW : ∀ y x, (W y x : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (f g : Site n → Mat) : Phi S U W (cstar f) g = starRingEnd ℂ (Phi S U W f (cstar g)) := by
  simp only [Phi, map_add, map_sum, map_mul, DU_cstar U hU, avgW_cstar S W hW, ntr_conj_mul, Complex.conj_ofReal]

lemma P0_cstar (f g : Site n → Mat) : P0 (cstar f) g = starRingEnd ℂ (P0 f (cstar g)) := by
  simp only [P0, pairForm0, wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, map_sum, cstar, ntr_conj_mul,
    conjTranspose_conjTranspose]

/-- **`Δ'_𝖺(𝐔)` maps the forms with values in `𝔤` to such forms**: it commutes with `λ ↦ λ^*`. -/
theorem DeltaS_cstar (U : Config N n) (W : Site n → Site n → GLN)
    (hU : ∀ μ x, (U μ x : Mat) ∈ unitaryGroup (Fin N) ℂ) (hW : ∀ y x, (W y x : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (f : Site n → Mat) : DeltaS S U W (cstar f) = cstar (DeltaS S U W f) := by
  have h : ∀ g, P0 (DeltaS S U W (cstar f) - cstar (DeltaS S U W f)) g = 0 := fun g => by
    rw [map_sub, LinearMap.sub_apply, DeltaS_spec, P0_cstar, DeltaS_spec, Phi_cstar S U W hU hW, sub_self]
  exact sub_eq_zero.1 (P0_nondeg.1 _ h)

lemma piD_cstar (ΩD : Set (Site n)) (f : Site n → Mat) : piD ΩD (cstar f) = cstar (piD ΩD f) := by
  funext x; simp only [piD_apply, cstar]; split_ifs <;> simp

/-- **`G'` maps the forms with values in `𝔤` to such forms**: it commutes with `λ ↦ λ^*`. -/
theorem Gp'_cstar (U : Config N n) (W : Site n → Site n → GLN) (ΩD : Set (Site n))
    (hU : ∀ μ x, (U μ x : Mat) ∈ unitaryGroup (Fin N) ℂ) (hW : ∀ y x, (W y x : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (hK : IsUnit (ckern (piD ΩD) (DeltaS S U W))) (f : Site n → Mat) :
    Gp' S U W ΩD (cstar f) = cstar (Gp' S U W ΩD f) := by
  obtain ⟨K, hKd⟩ : ∃ K, K = ckern (piD ΩD) (DeltaS S U W) := ⟨_, rfl⟩
  have hKc : ∀ h, K (cstar h) = cstar (K h) := fun h => by
    rw [hKd, ckern_apply, ckern_apply, piD_cstar, DeltaS_cstar S U W hU hW, piD_cstar, cstar_add, cstar_sub]
  rw [← hKd] at hK
  have h1 : ∀ y, K (Ring.inverse K y) = y := fun y => LinearMap.congr_fun (Ring.mul_inverse_cancel _ hK) y
  have h2 : ∀ y, Ring.inverse K (K y) = y := fun y => LinearMap.congr_fun (Ring.inverse_mul_cancel _ hK) y
  have hinv : ∀ y, Ring.inverse K (cstar y) = cstar (Ring.inverse K y) := fun y => by
    conv_lhs => rw [← h1 y, ← hKc, h2]
  rw [Gp', cinv_apply, cinv_apply, ← hKd, hinv, piD_cstar]

/-- **`Δ'_𝖺(𝐔)` is positive definite on the forms with values in `𝔤` which vanish outside `Ω_D`.** -/
theorem DeltaS_pos [NeZero N] (U : Config N n) (W : Site n → Site n → GLN) (ΩD : Set (Site n)) (eps η : ℝ)
    (heps : 0 ≤ eps) (hη : 0 ≤ η)
    (hE : ∀ x μ, ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z)
    (hW1 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW2 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z)
    (hsmall : (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8)
    (hU : ∀ μ x, (U μ x : Mat) ∈ unitaryGroup (Fin N) ℂ) (hW : ∀ y x, (W y x : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (lam : Site n → Mat) (hl : cstar lam = lam) (hl0 : lam ≠ 0) :
    (P0 (DeltaS S U W lam) lam).im = 0 ∧ 0 < (P0 (DeltaS S U W lam) lam).re := by
  have e1 : P0 (DeltaS S U W lam) lam = Phi S U W (cstar lam) lam := by rw [DeltaS_spec, hl]
  have e2 : starRingEnd ℂ (Phi S U W (cstar lam) lam) = Phi S U W (cstar lam) lam := by
    conv_lhs => rw [Phi_cstar S U W hU hW, Complex.conj_conj]
    rw [hl]
  have hconj := sf_conjugated S U W (fun _ => 0) lam 0 eps η le_rfl (by positivity) heps hη
    (fun x μ => by simp) (fun y _ x _ => by simp) hE hW1 hW2 hsmall
  rw [conjL_zero, conjR_zero] at hconj
  have hD : 0 ≤ dsqM lam := sum_nonneg fun _ _ => sum_nonneg fun _ _ => hs2_nonneg _
  have hW0 : 0 < wnormM S lam := by
    by_contra h
    exact hl0 (eq_zero_of_wnormM S lam (not_lt.1 h))
  refine ⟨?_, ?_⟩
  · rw [e1]; exact Complex.conj_eq_iff_im.1 e2
  · rw [e1]; exact lt_of_lt_of_le (by positivity) hconj

/-- **`G'` is positive definite on the forms with values in `𝔤` which vanish outside `Ω_D`.** -/
theorem Gp'_pos [NeZero N] (U : Config N n) (W : Site n → Site n → GLN) (ΩD : Set (Site n)) (eps η : ℝ)
    (heps : 0 ≤ eps) (hη : 0 ≤ η)
    (hE : ∀ x μ, ∀ Z : Mat, hs (Ad (U μ x) Z - Z) ≤ eps * S.L * ((S.L : ℝ) ^ S.sc (x + unit n μ))⁻¹ * hs Z)
    (hW1 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW2 : ∀ y ∈ detB S, ∀ x ∈ Blk S (S.sc y) y, ∀ Z : Mat, hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z)
    (hsmall : (4 * eps + eps ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8)
    (hU : ∀ μ x, (U μ x : Mat) ∈ unitaryGroup (Fin N) ℂ) (hW : ∀ y x, (W y x : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (f : Site n → Mat) (hf : cstar f = f) (hfP : piD ΩD f = f) (hf0 : f ≠ 0) :
    (P0 (Gp' S U W ΩD f) f).im = 0 ∧ 0 < (P0 (Gp' S U W ΩD f) f).re := by
  have hK := deltaS_isUnit S U W ΩD eps η heps hη hE hW1 hW2 hsmall
  have hP := piD_idem (N := N) ΩD
  obtain ⟨v, hv⟩ : ∃ v, v = Gp' S U W ΩD f := ⟨_, rfl⟩
  have hvP : piD ΩD v = v := by rw [hv]; exact P_cinv hP _
  have hDv : piD ΩD (DeltaS S U W v) = f := by rw [hv, Gp', P_T_cinv hP hK, hfP]
  have hvs : cstar v = v := by rw [hv, ← Gp'_cstar S U W ΩD hU hW hK, hf]
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hDv
    exact hf0 hDv.symm
  have e : P0 v f = P0 (DeltaS S U W v) v := by
    rw [← hDv, ← piD_symm, hvP]; exact wpair_symm _ _ _
  rw [← hv, e]
  exact DeltaS_pos S U W ΩD eps η heps hη hE hW1 hW2 hsmall hU hW v hvs hv0

end SmallFieldDecay
end CoreLean

end
