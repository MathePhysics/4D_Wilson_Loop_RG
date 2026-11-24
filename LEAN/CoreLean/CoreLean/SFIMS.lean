/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`95f07f48317e`), the step "The double commutators", the identities: for a
family `h_□` with `Σ_□h_□² = 1` the localised forms differ from the form by sums of `(h_□(x) - h_□(x'))²` against the
kernel (the formula of Ismagilov, Morgan, and Simon).

* `norm_comb_sq`: `Σ_□‖h_□(x')a' - h_□(x)a‖² = ‖a' - a‖² + Σ_□(h_□(x') - h_□(x))²Re⟨a', a⟩`.
* `ims_grad`: `Σ_□‖∇(h_□A)‖² = ‖∇A‖² + Σ_{μ,x,ν}Σ_□(h_□(x + e_ν) - h_□(x))²Re⟨A_μ(x + e_ν), A_μ(x)⟩`.
-/
import CoreLean.SFCutoffCube

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

/-- **The localisation of a difference.** -/
lemma norm_comb_sq {κ V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (s : Finset κ) (h : κ → ℝ)
    (h' : κ → ℝ) (hs : ∑ c ∈ s, h c ^ 2 = 1) (hs' : ∑ c ∈ s, h' c ^ 2 = 1) (a a' : V) :
    ∑ c ∈ s, ‖(h' c : ℂ) • a' - (h c : ℂ) • a‖ ^ 2 =
      ‖a' - a‖ ^ 2 + (∑ c ∈ s, (h' c - h c) ^ 2) * (inner ℂ a' a).re := by
  have e1 : ∀ c, ‖(h' c : ℂ) • a' - (h c : ℂ) • a‖ ^ 2 =
      h' c ^ 2 * ‖a'‖ ^ 2 + h c ^ 2 * ‖a‖ ^ 2 - 2 * (h' c * h c) * (inner ℂ a' a).re := fun c => by
    rw [@norm_sub_sq ℂ, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [show (h' c : ℂ) * ((h c : ℂ) * inner ℂ a' a) = ((h' c * h c : ℝ) : ℂ) * inner ℂ a' a by push_cast; ring]
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
    ring
  have e2 : ∑ c ∈ s, h' c * h c = 1 - 1 / 2 * ∑ c ∈ s, (h' c - h c) ^ 2 := by
    have : ∀ c, (h' c - h c) ^ 2 = h' c ^ 2 + h c ^ 2 - 2 * (h' c * h c) := fun c => by ring
    simp only [this, sum_sub_distrib, sum_add_distrib, hs, hs', ← mul_sum]; ring
  simp only [e1, sum_sub_distrib, sum_add_distrib, ← sum_mul]
  simp only [← mul_sum]
  rw [hs, hs', e2, @norm_sub_sq ℂ]
  simp only [RCLike.re_to_complex]
  ring

/-! ### The localisation of a linear functional and of the constraint form -/

lemma norm_sum_sq_re {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (I : Finset ι) (u : ι → V) :
    ‖∑ i ∈ I, u i‖ ^ 2 = ∑ i ∈ I, ∑ i' ∈ I, (inner ℂ (u i) (u i')).re := by
  rw [@norm_sq_eq_re_inner ℂ, sum_inner]
  simp only [inner_sum, map_sum, RCLike.re_to_complex]

/-- **The localisation of a linear functional** `Σ_iw_ia(p_i)`. -/
lemma ims_lin {κ ι X V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (s : Finset κ) (h : κ → X → ℝ)
    (hs : ∀ z, ∑ c ∈ s, h c z ^ 2 = 1) (I : Finset ι) (w : ι → ℝ) (p : ι → X) (a : X → V) :
    ∑ c ∈ s, ‖∑ i ∈ I, ((w i * h c (p i) : ℝ) : ℂ) • a (p i)‖ ^ 2 =
      ‖∑ i ∈ I, (w i : ℂ) • a (p i)‖ ^ 2 - 1 / 2 * ∑ i ∈ I, ∑ i' ∈ I,
        w i * w i' * (∑ c ∈ s, (h c (p i) - h c (p i')) ^ 2) * (inner ℂ (a (p i)) (a (p i'))).re := by
  have hinner : ∀ (r r' : ℝ) (b b' : V), (inner ℂ ((r : ℂ) • b) ((r' : ℂ) • b')).re = r * r' * (inner ℂ b b').re :=
    fun r r' b b' => by
      rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
        Complex.re_ofReal_mul]
  simp only [norm_sum_sq_re, hinner]
  refine (sum_comm).trans ((sum_congr rfl fun i _ => sum_comm).trans ?_)
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i' _ => ?_
  have e : ∑ c ∈ s, h c (p i) * h c (p i') = 1 - 1 / 2 * ∑ c ∈ s, (h c (p i) - h c (p i')) ^ 2 := by
    have : ∀ c, (h c (p i) - h c (p i')) ^ 2 = h c (p i) ^ 2 + h c (p i') ^ 2 - 2 * (h c (p i) * h c (p i')) :=
      fun c => by ring
    simp only [this, sum_sub_distrib, sum_add_distrib, hs, ← mul_sum]; ring
  calc ∑ c ∈ s, w i * h c (p i) * (w i' * h c (p i')) * (inner ℂ (a (p i)) (a (p i'))).re
      = w i * w i' * (inner ℂ (a (p i)) (a (p i'))).re * ∑ c ∈ s, h c (p i) * h c (p i') := by
        rw [mul_sum]; exact sum_congr rfl fun c _ => by ring
    _ = _ := by rw [e]; ring

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- The localised form `h_□A`. -/
def locA (h : Site NF → ℝ) (A : Fin 4 → Site NF → Mat) : Fin 4 → Site NF → Mat := fun μ x => (h x : ℂ) • A μ x

/-- **The localisation of `‖∇A‖²`.** -/
theorem ims_grad {κ : Type*} (s : Finset κ) (h : κ → Site NF → ℝ) (hs : ∀ x, ∑ c ∈ s, h c x ^ 2 = 1)
    (A : Fin 4 → Site NF → Mat) :
    ∑ c ∈ s, gradNorm S (locA S (h c) A) = gradNorm S A +
      ∑ μ, ∑ x, ∑ ν, (∑ c ∈ s, (h c (x + unit NF ν) - h c x) ^ 2) *
        (inner ℂ (emb (N := N) (A μ (x + unit NF ν))) (emb (A μ x))).re := by
  unfold gradNorm gbond
  rw [sum_comm]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun μ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun ν _ => ?_
  have e : ∀ c, emb (N := N) (locA S (h c) A μ (x + unit NF ν)) - emb (locA S (h c) A μ x) =
      (h c (x + unit NF ν) : ℂ) • emb (A μ (x + unit NF ν)) - (h c x : ℂ) • emb (A μ x) := fun c => by
    simp only [locA]
    rw [show emb (N := N) ((h c (x + unit NF ν) : ℂ) • A μ (x + unit NF ν)) =
      (h c (x + unit NF ν) : ℂ) • emb (A μ (x + unit NF ν)) from map_smul (embL (N := N)) _ _,
      show emb (N := N) ((h c x : ℂ) • A μ x) = (h c x : ℂ) • emb (A μ x) from map_smul (embL (N := N)) _ _]
  simp only [e]
  exact norm_comb_sq s (fun c => h c x) (fun c => h c (x + unit NF ν)) (hs x) (hs (x + unit NF ν)) _ _

/-- `emb((QA)(c))` as a weighted sum over the block and the paths. -/
lemma emb_Qt_sum (A : Fin 4 → Site NF → Mat) (j : ℕ) (y : Site NF) (μ : Fin 4) :
    emb (N := N) (Qt S A j y μ) = ∑ i ∈ Blk S.toDomSeq j y ×ˢ range (S.L ^ j),
      (((((S.L ^ j : ℕ) : ℝ) ^ 5)⁻¹ : ℝ) : ℂ) • emb (A μ (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF μ)) := by
  unfold Qt
  rw [sum_product]
  show embL _ = _
  rw [map_smul, map_sum, smul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [map_sum, smul_sum]
  refine sum_congr rfl fun t _ => ?_
  push_cast; rfl

/-- The error of the localisation of the constraint form. -/
def errQ {κ : Type*} (s : Finset κ) (h : κ → Site NF → ℝ) (A : Fin 4 → Site NF → Mat) : ℝ :=
  ∑ q ∈ QB S, ((S.L ^ q.1 : ℕ) : ℝ) ^ 2 * ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
    ∑ i' ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
      ((((S.L ^ q.1 : ℕ) : ℝ) ^ 5)⁻¹) * ((((S.L ^ q.1 : ℕ) : ℝ) ^ 5)⁻¹) *
        (∑ c ∈ s, (h c (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2) -
          h c (i'.1 + ((i'.2 : ℕ) : ZMod NF) • unit NF q.2.2)) ^ 2) *
        (inner ℂ (emb (N := N) (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2)))
          (emb (A q.2.2 (i'.1 + ((i'.2 : ℕ) : ZMod NF) • unit NF q.2.2)))).re

/-- **The localisation of the constraint form**: `Σ_□⟨(h_□A)^*, Q^*Qh_□A⟩ = ⟨A^*, Q^*QA⟩ - ½errQ`. -/
theorem ims_Q {κ : Type*} (s : Finset κ) (h : κ → Site NF → ℝ) (hs : ∀ x, ∑ c ∈ s, h c x ^ 2 = 1)
    (A : Fin 4 → Site NF → Mat) :
    ∑ c ∈ s, Qnorm S (locA S (h c) A) = Qnorm S A - 1 / 2 * errQ S s h A := by
  unfold Qnorm errQ
  rw [sum_comm, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun q _ => ?_
  simp only [emb_Qt_sum]
  have e : ∀ c, ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
      (((((S.L ^ q.1 : ℕ) : ℝ) ^ 5)⁻¹ : ℝ) : ℂ) • emb (N := N) (locA S (h c) A q.2.2
        (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2)) =
      ∑ i ∈ Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1),
        (((((S.L ^ q.1 : ℕ) : ℝ) ^ 5)⁻¹ * h c (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2) : ℝ) : ℂ) •
          emb (N := N) (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2)) := fun c => by
    refine sum_congr rfl fun i _ => ?_
    simp only [locA]
    rw [show emb (N := N) ((h c (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2) : ℂ) •
        A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2)) =
      (h c (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2) : ℂ) •
        emb (A q.2.2 (i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2)) from map_smul (embL (N := N)) _ _,
      smul_smul]
    push_cast; ring_nf
  simp only [e]
  rw [← mul_sum, ims_lin s h hs (Blk S.toDomSeq q.1 q.2.1 ×ˢ range (S.L ^ q.1)) (fun _ => (((S.L ^ q.1 : ℕ) : ℝ) ^ 5)⁻¹)
    (fun i => i.1 + ((i.2 : ℕ) : ZMod NF) • unit NF q.2.2) (fun z => emb (N := N) (A q.2.2 z))]
  ring

/-! ### The localisation of `‖Pg‖²` through the kernel of `P` -/

/-- **The kernel of `P`**: `k_P(x, x')Z = (P(δ_{x'}Z))(x)`. -/
def kP [NeZero N] (x x' : Site NF) : Mat →ₗ[ℂ] Mat :=
  LinearMap.proj x ∘ₗ Pop S (X0 S) (W1 S) Set.univ ∘ₗ LinearMap.single ℂ (fun _ : Site NF => Mat) x'

lemma Pop_kernel [NeZero N] (g : Site NF → Mat) (x : Site NF) :
    Pop S (X0 S) (W1 S) Set.univ g x = ∑ x', kP S x x' (g x') := by
  have e : g = ∑ x', LinearMap.single ℂ (fun _ : Site NF => Mat) x' (g x') := by
    funext z; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [e]
  rw [map_sum, Finset.sum_apply]
  rfl

/-- `‖Pg‖² = Re Σ_{x,x'}tr((k_P(x, x')g(x'))^*g(x))`. -/
lemma Pop_norm_kernel [NeZero N] (g : Site NF → Mat) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ g x) =
      (∑ x, ∑ x', ntr ((kP S x x' (g x'))ᴴ * g x)).re := by
  rw [Pop_norm_triv S Set.univ (hb_triv (S := S) Set.univ) g]
  unfold herm
  simp only [P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, cstar]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [Pop_kernel, Matrix.conjTranspose_sum, Matrix.sum_mul, ntr_sum]

/-- **The localisation of `‖Pg‖²`**: `Σ_□‖P(h_□g)‖² = ‖Pg‖² - ½Re Σ_{x,x'}Σ_□(h_□(x) - h_□(x'))²tr((k_Pg(x'))^*g(x))`. -/
theorem ims_P [NeZero N] {κ : Type*} (s : Finset κ) (h : κ → Site NF → ℝ) (hs : ∀ x, ∑ c ∈ s, h c x ^ 2 = 1)
    (g : Site NF → Mat) :
    ∑ c ∈ s, ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (fun x => (h c x : ℂ) • g x) x) =
      ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ g x) - 1 / 2 * (∑ x, ∑ x',
        ((∑ c ∈ s, (h c x - h c x') ^ 2 : ℝ) : ℂ) * ntr ((kP S x x' (g x'))ᴴ * g x)).re := by
  simp only [Pop_norm_kernel]
  have e1 : ∀ c x x', ntr ((kP S x x' ((h c x' : ℂ) • g x'))ᴴ * ((h c x : ℂ) • g x)) =
      ((h c x * h c x' : ℝ) : ℂ) * ntr ((kP S x x' (g x'))ᴴ * g x) := fun c x x' => by
    rw [map_smul, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, ntr_smul, ntr_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  simp only [e1]
  rw [← Complex.re_sum, sum_comm (s := s)]
  simp only [Finset.sum_comm (s := s) (t := univ)]
  have e2 : ∀ x x', ∑ c ∈ s, ((h c x * h c x' : ℝ) : ℂ) * ntr ((kP S x x' (g x'))ᴴ * g x) =
      ntr ((kP S x x' (g x'))ᴴ * g x) -
        ((1 / 2 : ℝ) : ℂ) * (((∑ c ∈ s, (h c x - h c x') ^ 2 : ℝ) : ℂ) * ntr ((kP S x x' (g x'))ᴴ * g x)) := by
    intro x x'
    rw [← sum_mul, ← Complex.ofReal_sum]
    have : ∑ c ∈ s, h c x * h c x' = 1 - 1 / 2 * ∑ c ∈ s, (h c x - h c x') ^ 2 := by
      have h2 : ∀ c, (h c x - h c x') ^ 2 = h c x ^ 2 + h c x' ^ 2 - 2 * (h c x * h c x') := fun c => by ring
      simp only [h2, sum_sub_distrib, sum_add_distrib, hs, ← mul_sum]; ring
    rw [this]; push_cast; ring
  simp only [e2, sum_sub_distrib, ← mul_sum]
  rw [Complex.sub_re, Complex.re_ofReal_mul]

/-! ### The commutator of `∂^*` with a multiplication, and the lower bound of the localised projection -/

/-- **`∂^*(hA) = h∂^*A + [∂^*, h]A`**, `[∂^*, h]A(x) = Σ_μ(h(x - e_μ) - h(x))A_μ(x - e_μ)`. -/
lemma Ds1L_loc (h : Site NF → ℝ) (A : Fin 4 → Site NF → Mat) (x : Site NF) :
    Ds1L a1 (cfgX (X0 S)) (locA S h A) x = (h x : ℂ) • Ds1L a1 (cfgX (X0 S)) A x +
      ∑ μ, ((h (x - unit NF μ) - h x : ℝ) : ℂ) • A μ (x - unit NF μ) := by
  rw [Ds1L_triv, Ds1L_triv, smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun μ _ => ?_
  simp only [locA]
  push_cast
  module

/-- The commutator term. -/
def commA (h : Site NF → ℝ) (A : Fin 4 → Site NF → Mat) : Site NF → Mat :=
  fun x => ∑ μ, ((h (x - unit NF μ) - h x : ℝ) : ℂ) • A μ (x - unit NF μ)

lemma hs2_add_ge (u v : Mat) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) :
    (1 - ε) * hs2 u - ε⁻¹ * hs2 v ≤ hs2 (u + v) := by
  rw [← hs_sq, ← hs_sq, ← hs_sq]
  have h1 : hs u ≤ hs (u + v) + hs v := by
    have := hs_add_le (u + v) (-v)
    have e : hs (-v) = hs v := by
      unfold hs; congr 1; rw [show -v = (-1 : ℂ) • v by simp, RegularAverages.hs2_smul]; simp
    rw [add_neg_cancel_right, e] at this; exact this
  have hu := hs_nonneg u; have hv := hs_nonneg v; have huv := hs_nonneg (u + v)
  -- `(1 - ε)a² ≤ (b + c)²(1 - ε) ≤ b² + ε⁻¹c²` with `a ≤ b + c`
  have h2 : (1 - ε) * hs u ^ 2 ≤ (1 - ε) * (hs (u + v) + hs v) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu h1 2) (by linarith)
  have h3 : (1 - ε) * (hs (u + v) + hs v) ^ 2 ≤ hs (u + v) ^ 2 + ε⁻¹ * hs v ^ 2 := by
    have hinv : ε⁻¹ ≥ 1 := by rw [ge_iff_le, one_le_inv₀ hε0]; exact hε
    have key : 2 * hs (u + v) * hs v ≤ ε * hs (u + v) ^ 2 + ε⁻¹ * hs v ^ 2 := by
      have := sq_nonneg (ε * hs (u + v) - hs v)
      have e : ε * (ε * hs (u + v) ^ 2 + ε⁻¹ * hs v ^ 2) = (ε * hs (u + v)) ^ 2 + hs v ^ 2 := by
        field_simp
      nlinarith [mul_pos hε0 hε0]
    have k2 := mul_le_mul_of_nonneg_left key (show 0 ≤ 1 - ε by linarith)
    have h5 : ε * ε⁻¹ * hs v ^ 2 = hs v ^ 2 := by field_simp
    have h6 : 0 ≤ ε ^ 2 * hs (u + v) ^ 2 := by positivity
    have h7 : 0 ≤ ε * hs v ^ 2 := by positivity
    nlinarith
  linarith

/-- **The lower bound of the localised projection**: for `0 < ε ≤ 1`,
`Σ_□‖P∂^*(h_□A)‖² ≥ (1 - ε)(‖P∂^*A‖² - ½err_P) - ε⁻¹Σ_□‖[∂^*, h_□]A‖²`. -/
theorem ims_P1 [NeZero N] {κ : Type*} (s : Finset κ) (h : κ → Site NF → ℝ) (hs : ∀ x, ∑ c ∈ s, h c x ^ 2 = 1)
    (A : Fin 4 → Site NF → Mat) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) :
    (1 - ε) * (∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) - 1 / 2 * (∑ x, ∑ x',
        ((∑ c ∈ s, (h c x - h c x') ^ 2 : ℝ) : ℂ) *
          ntr ((kP S x x' (Ds1L a1 (cfgX (X0 S)) A x'))ᴴ * Ds1L a1 (cfgX (X0 S)) A x)).re) -
      ε⁻¹ * ∑ c ∈ s, ∑ x, hs2 (commA S (h c) A x) ≤
      ∑ c ∈ s, ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (locA S (h c) A)) x) := by
  set g := Ds1L a1 (cfgX (X0 S)) A
  have hims := ims_P S s h hs g
  rw [← hims, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun c _ => ?_
  have e : Ds1L a1 (cfgX (X0 S)) (locA S (h c) A) = (fun x => (h c x : ℂ) • g x) + commA S (h c) A := by
    funext x; rw [Ds1L_loc]; rfl
  rw [e, map_add]
  have hP : ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (commA S (h c) A) x) ≤ ∑ x, hs2 (commA S (h c) A x) :=
    Pop_contr S Set.univ _
  calc (1 - ε) * ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (fun x => (h c x : ℂ) • g x) x) -
        ε⁻¹ * ∑ x, hs2 (commA S (h c) A x)
      ≤ ∑ x, ((1 - ε) * hs2 (Pop S (X0 S) (W1 S) Set.univ (fun x => (h c x : ℂ) • g x) x) -
          ε⁻¹ * hs2 (Pop S (X0 S) (W1 S) Set.univ (commA S (h c) A) x)) := by
        rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
        have : 0 ≤ ε⁻¹ := inv_nonneg.2 hε0.le
        nlinarith
    _ ≤ _ := sum_le_sum fun x _ => hs2_add_ge _ _ hε0 hε

end SFBounds
end CoreLean

end
