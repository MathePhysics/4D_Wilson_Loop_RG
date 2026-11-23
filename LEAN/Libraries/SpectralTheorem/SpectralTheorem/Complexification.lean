import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The complexification of a real inner product space

For a real inner product space `E`, the complexification `E_ℂ = E ⊕ i E` is the set of pairs
`z = (x, y)`, thought of as `x + i y`, with the complex scalar action
`(a + b i) • (x, y) = (a x - b y, a y + b x)` and the inner product
`⟪(x, y), (x', y')⟫_ℂ = (⟪x, x'⟫ + ⟪y, y'⟫) + i (⟪x, y'⟫ - ⟪y, x'⟫)`,
which is conjugate-linear in the first argument (mathlib's convention).  Its norm satisfies
`‖(x, y)‖² = ‖x‖² + ‖y‖²`, so `E_ℂ` is isometric (over `ℝ`) to `E × E` with the `L²` norm, and
it is complete when `E` is.

Reed–Simon I work over complex Hilbert spaces throughout and do not construct the
complexification; they remark (Section VI.4, p. 195) that on real Hilbert spaces a positive
operator need not be self-adjoint.  The complexification is the standard device for transferring
the spectral theorem to real Hilbert spaces (milestone M10 of `SCOPING.md`).  The proofs are
direct computations with real and imaginary parts.  The real structure is the one induced from
`ℂ` (`Module.complexToReal`), so no second real module structure is introduced.

## Main definitions and results

* `SpectralTheorem.Complexification E`: the structure of pairs `⟨re, im⟩`, with the instances
  `AddCommGroup`, `Module ℂ`, `NormedAddCommGroup`, `InnerProductSpace ℂ`, and `CompleteSpace`
  when `E` is complete.
* `SpectralTheorem.Complexification.inner_re`, `inner_im`: the inner product;
  `SpectralTheorem.Complexification.norm_sq_eq`: `‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2`.
* `SpectralTheorem.Complexification.equivProdL2`: the real isometric equivalence with
  `WithLp 2 (E × E)`.
* `SpectralTheorem.Complexification.ofReal`: the embedding `x ↦ x + i 0`, an `ℝ`-linear
  isometry with `⟪ofReal x, ofReal y⟫_ℂ = ⟪x, y⟫_ℝ`, and
  `ofReal_add_I_smul : ofReal z.re + I • ofReal z.im = z`.
* `SpectralTheorem.Complexification.conj`: the conjugation `x + i y ↦ x - i y`, a
  conjugate-linear isometric involution with `⟪conj z, conj w⟫_ℂ = conj ⟪z, w⟫_ℂ`, whose fixed
  points are the real vectors.
-/

noncomputable section

open scoped InnerProductSpace

namespace SpectralTheorem

universe u

/-- The complexification `E ⊕ i E` of a real inner product space: the pair `⟨x, y⟩` stands for
`x + i y`. -/
@[ext] structure Complexification (E : Type u) where
  /-- The real part. -/
  re : E
  /-- The imaginary part. -/
  im : E

namespace Complexification

variable {E : Type u}

section Algebraic

/-- The pair of real and imaginary parts, as a map to `E × E`. -/
def toProd (z : Complexification E) : E × E := (z.re, z.im)

theorem toProd_injective : Function.Injective (toProd : Complexification E → E × E) :=
  fun _ _ h => Complexification.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

variable [AddCommGroup E]

instance : Zero (Complexification E) := ⟨⟨0, 0⟩⟩
instance : Add (Complexification E) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (Complexification E) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (Complexification E) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : SMul ℕ (Complexification E) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : SMul ℤ (Complexification E) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re : (0 : Complexification E).re = 0 := rfl
@[simp] theorem zero_im : (0 : Complexification E).im = 0 := rfl
@[simp] theorem add_re (z w : Complexification E) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : Complexification E) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : Complexification E) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : Complexification E) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : Complexification E) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : Complexification E) : (z - w).im = z.im - w.im := rfl

instance : AddCommGroup (Complexification E) :=
  Function.Injective.addCommGroup toProd toProd_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

variable [Module ℝ E]

/-- The complex scalar action `(a + b i) • (x + i y) = (a x - b y) + i (a y + b x)`. -/
instance : SMul ℂ (Complexification E) :=
  ⟨fun c z => ⟨c.re • z.re - c.im • z.im, c.re • z.im + c.im • z.re⟩⟩

@[simp] theorem smul_re (c : ℂ) (z : Complexification E) :
    (c • z).re = c.re • z.re - c.im • z.im := rfl
@[simp] theorem smul_im (c : ℂ) (z : Complexification E) :
    (c • z).im = c.re • z.im + c.im • z.re := rfl

instance : Module ℂ (Complexification E) where
  one_smul z := by ext <;> simp
  mul_smul c d z := by
    ext <;> simp only [smul_re, smul_im, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by ext <;> simp
  smul_add c z w := by ext <;> simp only [smul_re, smul_im, add_re, add_im] <;> module
  add_smul c d z := by
    ext <;> simp only [smul_re, smul_im, add_re, add_im, Complex.add_re, Complex.add_im] <;>
      module
  zero_smul z := by ext <;> simp

/-- Real scalars act componentwise (the real structure is `Module.complexToReal`). -/
@[simp] theorem real_smul_re (r : ℝ) (z : Complexification E) : (r • z).re = r • z.re := by
  rw [← Complex.coe_smul, smul_re]; simp

/-- Real scalars act componentwise (the real structure is `Module.complexToReal`). -/
@[simp] theorem real_smul_im (r : ℝ) (z : Complexification E) : (r • z).im = r • z.im := by
  rw [← Complex.coe_smul, smul_im]; simp

/-- Real scalars (viewed in `ℂ`) act componentwise. -/
theorem ofReal_smul (r : ℝ) (z : Complexification E) :
    (r : ℂ) • z = ⟨r • z.re, r • z.im⟩ := by
  ext <;> simp

theorem I_smul_re (z : Complexification E) : (Complex.I • z).re = -z.im := by simp
theorem I_smul_im (z : Complexification E) : (Complex.I • z).im = z.re := by simp

end Algebraic

section Inner

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product `⟪x + i y, x' + i y'⟫ = (⟪x, x'⟫ + ⟪y, y'⟫) + i (⟪x, y'⟫ - ⟪y, x'⟫)`,
conjugate-linear in the first argument. -/
instance : Inner ℂ (Complexification E) :=
  ⟨fun z w => ⟨⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ, ⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ⟩⟩

@[simp] theorem inner_re (z w : Complexification E) :
    (⟪z, w⟫_ℂ).re = ⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ := rfl

@[simp] theorem inner_im (z w : Complexification E) :
    (⟪z, w⟫_ℂ).im = ⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ := rfl

theorem inner_def (z w : Complexification E) :
    ⟪z, w⟫_ℂ = ((⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ : ℝ) : ℂ)
      + ((⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- The inner product space core of the complexification. -/
@[instance_reducible]
def innerCore : InnerProductSpace.Core ℂ (Complexification E) where
  conj_inner_symm z w := by
    apply Complex.ext
    · simp only [Complex.conj_re, inner_re, real_inner_comm]
    · simp only [Complex.conj_im, inner_im, real_inner_comm]
      ring
  re_inner_nonneg z := by
    simp only [RCLike.re_to_complex, inner_re]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left z w v := by
    apply Complex.ext <;>
      simp only [inner_re, inner_im, add_re, add_im, Complex.add_re, Complex.add_im,
        inner_add_left] <;> ring
  smul_left z w c := by
    apply Complex.ext <;>
      simp only [inner_re, inner_im, smul_re, smul_im, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, inner_add_left, inner_sub_left,
        real_inner_smul_left] <;> ring
  definite z h := by
    have h' := congrArg Complex.re h
    simp only [inner_re, Complex.zero_re] at h'
    have h1 : ⟪z.re, z.re⟫_ℝ = 0 := le_antisymm (by
      linarith [real_inner_self_nonneg (x := z.im)]) real_inner_self_nonneg
    have h2 : ⟪z.im, z.im⟫_ℝ = 0 := le_antisymm (by
      linarith [real_inner_self_nonneg (x := z.re)]) real_inner_self_nonneg
    ext
    · exact inner_self_eq_zero.mp h1
    · exact inner_self_eq_zero.mp h2

instance : NormedAddCommGroup (Complexification E) :=
  (innerCore (E := E)).toNormedAddCommGroup

instance : InnerProductSpace ℂ (Complexification E) :=
  InnerProductSpace.ofCore (innerCore (E := E)).toCore

theorem re_inner_self (z : Complexification E) :
    (⟪z, z⟫_ℂ).re = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2 := by
  rw [inner_re, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The norm of the complexification: `‖x + i y‖² = ‖x‖² + ‖y‖²`. -/
theorem norm_sq_eq (z : Complexification E) : ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2 := by
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) z).trans (re_inner_self z)

theorem norm_re_le (z : Complexification E) : ‖z.re‖ ≤ ‖z‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg z)
  rw [norm_sq_eq]
  nlinarith [sq_nonneg ‖z.im‖]

theorem norm_im_le (z : Complexification E) : ‖z.im‖ ≤ ‖z‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg z)
  rw [norm_sq_eq]
  nlinarith [sq_nonneg ‖z.re‖]

theorem norm_le_add (z : Complexification E) : ‖z‖ ≤ ‖z.re‖ + ‖z.im‖ := by
  refine le_of_sq_le_sq ?_ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [norm_sq_eq]
  nlinarith [norm_nonneg z.re, norm_nonneg z.im]

/-- The real isometric equivalence `x + i y ↦ (x, y)` with `E × E` carrying the `L²` norm. -/
def equivProdL2 : Complexification E ≃ₗᵢ[ℝ] WithLp 2 (E × E) where
  toFun z := WithLp.toLp 2 (z.re, z.im)
  invFun p := ⟨p.fst, p.snd⟩
  map_add' _ _ := rfl
  map_smul' r z := by
    rw [real_smul_re, real_smul_im, ← Prod.smul_mk, WithLp.toLp_smul, RingHom.id_apply]
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' z := by
    rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
      WithLp.prod_norm_sq_eq_of_L2, norm_sq_eq]
    rfl

@[simp] theorem equivProdL2_apply (z : Complexification E) :
    equivProdL2 z = WithLp.toLp 2 (z.re, z.im) := rfl

instance [CompleteSpace E] : CompleteSpace (Complexification E) :=
  (equivProdL2 (E := E)).toIsometryEquiv.completeSpace

/-- The real part as a continuous real-linear map. -/
def reCLM : Complexification E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := re, map_add' := add_re, map_smul' := real_smul_re } 1
    fun z => (norm_re_le z).trans_eq (one_mul _).symm

/-- The imaginary part as a continuous real-linear map. -/
def imCLM : Complexification E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := im, map_add' := add_im, map_smul' := real_smul_im } 1
    fun z => (norm_im_le z).trans_eq (one_mul _).symm

@[simp] theorem reCLM_apply (z : Complexification E) : reCLM z = z.re := rfl
@[simp] theorem imCLM_apply (z : Complexification E) : imCLM z = z.im := rfl

/-! ### The embedding of `E` -/

/-- The embedding `x ↦ x + i 0` as a real linear isometry. -/
def ofRealₗᵢ : E →ₗᵢ[ℝ] Complexification E where
  toFun x := ⟨x, 0⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  norm_map' x := by
    rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sq_eq]
    simp

/-- The embedding `x ↦ x + i 0` of `E` into its complexification. -/
def ofReal : E →L[ℝ] Complexification E := ofRealₗᵢ.toContinuousLinearMap

@[simp] theorem ofReal_re (x : E) : (ofReal x).re = x := rfl
@[simp] theorem ofReal_im (x : E) : (ofReal x).im = 0 := rfl

theorem ofReal_apply (x : E) : ofReal x = ⟨x, 0⟩ := rfl

/-- The embedding is isometric. -/
@[simp] theorem norm_ofReal (x : E) : ‖ofReal x‖ = ‖x‖ := ofRealₗᵢ.norm_map x

theorem ofReal_injective : Function.Injective (ofReal : E → Complexification E) :=
  fun _ _ h => congrArg re h

@[simp] theorem ofReal_inj {x y : E} : ofReal x = ofReal y ↔ x = y :=
  ofReal_injective.eq_iff

/-- The embedding preserves inner products. -/
@[simp] theorem inner_ofReal_ofReal (x y : E) :
    ⟪ofReal x, ofReal y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) := by
  apply Complex.ext <;> simp

/-- Every vector is `x + i y` with `x, y` real. -/
theorem ofReal_add_I_smul (z : Complexification E) :
    ofReal z.re + Complex.I • ofReal z.im = z := by
  ext <;> simp

theorem mk_eq (x y : E) : (⟨x, y⟩ : Complexification E) = ofReal x + Complex.I • ofReal y :=
  (ofReal_add_I_smul ⟨x, y⟩).symm

/-- A complex-linear map on the complexification is determined by its values on real vectors. -/
theorem linearMap_ext {F : Type*} [AddCommGroup F] [Module ℂ F]
    {f g : Complexification E →ₗ[ℂ] F} (h : ∀ x : E, f (ofReal x) = g (ofReal x)) : f = g := by
  ext z
  rw [← ofReal_add_I_smul z, map_add, map_add, map_smul, map_smul, h, h]

/-! ### The conjugation -/

/-- The conjugation `x + i y ↦ x - i y`: a conjugate-linear isometric involution. -/
def conj : Complexification E ≃ₗᵢ⋆[ℂ] Complexification E where
  toFun z := ⟨z.re, -z.im⟩
  invFun z := ⟨z.re, -z.im⟩
  map_add' z w := by ext <;> simp only [add_re, add_im, neg_add]
  map_smul' c z := by
    ext <;> simp only [smul_re, smul_im, Complex.conj_re, Complex.conj_im] <;> module
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  norm_map' z := by
    rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sq_eq, norm_sq_eq]
    simp

@[simp] theorem conj_re (z : Complexification E) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : Complexification E) : (conj z).im = -z.im := rfl

theorem conj_apply (z : Complexification E) : conj z = ⟨z.re, -z.im⟩ := rfl

@[simp] theorem conj_conj (z : Complexification E) : conj (conj z) = z := by
  ext <;> simp

@[simp] theorem conj_ofReal (x : E) : conj (ofReal x) = ofReal x := by
  ext <;> simp

/-- The conjugation is conjugate-unitary: `⟪conj z, conj w⟫ = conj ⟪z, w⟫`. -/
@[simp] theorem inner_conj_conj (z w : Complexification E) :
    ⟪conj z, conj w⟫_ℂ = starRingEnd ℂ ⟪z, w⟫_ℂ := by
  apply Complex.ext
  · simp only [inner_re, conj_re, conj_im, Complex.conj_re, inner_neg_left, inner_neg_right,
      neg_neg]
  · simp only [inner_im, conj_re, conj_im, Complex.conj_im, inner_neg_left, inner_neg_right]
    ring

theorem inner_conj_conj' (z w : Complexification E) : ⟪conj z, conj w⟫_ℂ = ⟪w, z⟫_ℂ := by
  rw [inner_conj_conj, inner_conj_symm]

/-- The fixed points of the conjugation are the vectors with zero imaginary part. -/
theorem conj_eq_self_iff {z : Complexification E} : conj z = z ↔ z.im = 0 := by
  constructor
  · intro h
    have h' := congrArg im h
    rw [conj_im] at h'
    have h2 : (2 : ℝ) • z.im = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h']
      exact neg_add_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro h
    ext
    · rfl
    · rw [conj_im, h, neg_zero]

theorem conj_eq_self_iff_exists {z : Complexification E} : conj z = z ↔ ∃ x, ofReal x = z := by
  rw [conj_eq_self_iff]
  constructor
  · intro h
    exact ⟨z.re, by ext <;> simp [h]⟩
  · rintro ⟨x, rfl⟩
    rfl

end Inner

end Complexification

end SpectralTheorem
