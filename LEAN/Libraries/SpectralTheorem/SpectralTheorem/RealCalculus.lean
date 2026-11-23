import SpectralTheorem.ComplexificationOperator
import SpectralTheorem.SelfAdjointCalculus
import SpectralTheorem.UnboundedCalculusProperties

/-!
# The functional calculus of a self-adjoint operator on a real Hilbert space

**Reed–Simon I, Theorem VIII.5, p. 262, over `ℝ`.**  Let `A` be a self-adjoint operator on a
real Hilbert space `E`.  Then there is a unique map `φ̂` from the bounded real Borel functions on
`ℝ` into `𝓛(E)` so that (a) `φ̂` is an algebra homomorphism into the self-adjoint operators (a
`⋆`-homomorphism for the trivial `⋆` on real functions); (b) `‖φ̂(h)‖ ≤ ‖h‖∞`; (c) if
`hₙ(x) → x` and `|hₙ(x)| ≤ |x|`, then `φ̂(hₙ) ψ → A ψ` for `ψ ∈ D(A)`; (d) if `hₙ → h`
pointwise with `‖hₙ‖∞` bounded, then `φ̂(hₙ) → φ̂(h)` strongly.  In addition (e) `A ψ = λ ψ`
implies `φ̂(h) ψ = h(λ) ψ`, and (f) `h ≥ 0` implies `φ̂(h) ≥ 0`.

Reed–Simon work over complex Hilbert spaces; the real statement is obtained through the
complexification `E_ℂ` (`SpectralTheorem.Complexification`,
`SpectralTheorem.ComplexificationOperator`), on which `A_ℂ` is self-adjoint.

Proof sketch.
* **Conjugation symmetry.**  `Ψ(h) = conj ∘ h̄(A_ℂ) ∘ conj` is a `⋆`-homomorphism with (b)–(d)
  for `A_ℂ`, because `A_ℂ` commutes with the conjugation; by the uniqueness in Theorem VIII.5,
  `Ψ(h) = h(A_ℂ)`.  Hence `h(A_ℂ)` commutes with the conjugation when `h` is real, and it is the
  complexification of a real operator `φ̂(h)`.
* **Existence.**  `φ̂(h)` is the descent of `h(A_ℂ)`; (a)–(f) follow from the corresponding
  properties of `h ↦ h(A_ℂ)`, since `T ↦ T_ℂ` is an injective isometric `⋆`-homomorphism.
* **Uniqueness.**  For `Φ` with (b)–(d), `Φ_ℂ(h) = Φ(Re h)_ℂ + i Φ(Im h)_ℂ` is a
  `⋆`-homomorphism with (b)–(d) for `A_ℂ`: (b) from the `C⋆`-identity
  `‖Φ_ℂ(h)‖² = ‖Φ_ℂ(|h|²)‖ = ‖Φ(|h|²)‖`; (c) needs `Φ(gₙ) ψ → 0` for real `gₙ → 0` with
  `|gₙ(x)| ≤ |x|`, obtained by writing `gₙ = (tₙ + gₙ) - tₙ` with `tₙ(x) → x`,
  `|tₙ(x)| ≤ |x|` and `|tₙ(x) + gₙ(x)| ≤ |x|`.  So `Φ_ℂ = h ↦ h(A_ℂ)`, and `Φ = φ̂`.

## Main definitions and results

* `SpectralTheorem.boundedMeasurableReal X`: bounded measurable functions `X → ℝ`;
  `SpectralTheorem.ofRealBM`: their inclusion into `boundedMeasurable X`.
* `SpectralTheorem.conj_selfAdjointCalc`: `conj (h(A_ℂ) z) = h̄(A_ℂ) (conj z)`.
* `SpectralTheorem.realCalc hA`: `h ↦ h(A)`, a `⋆`-homomorphism, with
  `complexifyCLM_realCalc` and `realCalc_apply`; (b) `norm_realCalc_le`,
  (c) `tendsto_realCalc_apply_self`, (d) `tendsto_realCalc_apply`, (e) `realCalc_apply_of_eigen`,
  (f) `isPositive_realCalc`, and `isSelfAdjoint_realCalc`.
* `SpectralTheorem.IsRealSelfAdjointCalculus`, `IsRealSelfAdjointCalculus.eq_realCalc`,
  `SpectralTheorem.existsUnique_isRealSelfAdjointCalculus`: **uniqueness**.
* `SpectralTheorem.realSpectralProjection hA hΩ`: the spectral projections `χ_Ω(A)`, orthogonal
  projections with `P_∅ = 0`, `P_ℝ = 1`, `P_Ω₁ P_Ω₂ = P_{Ω₁ ∩ Ω₂}` and strong countable
  additivity (Reed–Simon I, p. 263).
-/

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology
open Filter

namespace SpectralTheorem

universe u

/-! ### Bounded real Borel functions -/

section BoundedMeasurableReal

variable (X : Type*) [MeasurableSpace X]

/-- **Bounded measurable functions** `X → ℝ`, a `⋆`-subalgebra of `X → ℝ` (whose `⋆` is
trivial). -/
def boundedMeasurableReal : StarSubalgebra ℝ (X → ℝ) where
  carrier := {g | Measurable g ∧ ∃ C, ∀ x, |g x| ≤ C}
  mul_mem' := by
    rintro f g ⟨hf, Cf, hCf⟩ ⟨hg, Cg, hCg⟩
    refine ⟨hf.mul hg, |Cf| * |Cg|, fun x => ?_⟩
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul ((hCf x).trans (le_abs_self Cf)) ((hCg x).trans (le_abs_self Cg))
      (abs_nonneg _) (abs_nonneg _)
  one_mem' := ⟨measurable_const, 1, fun _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf, Cf, hCf⟩ ⟨hg, Cg, hCg⟩
    exact ⟨hf.add hg, Cf + Cg, fun x => (abs_add_le _ _).trans (add_le_add (hCf x) (hCg x))⟩
  zero_mem' := ⟨measurable_const, 0, fun _ => by simp⟩
  algebraMap_mem' c := ⟨measurable_const, |c|, fun _ => by simp⟩
  star_mem' hf := hf

variable {X}

theorem mem_boundedMeasurableReal {g : X → ℝ} :
    g ∈ boundedMeasurableReal X ↔ Measurable g ∧ ∃ C, ∀ x, |g x| ≤ C :=
  Iff.rfl

theorem boundedMeasurableReal.measurable (g : boundedMeasurableReal X) :
    Measurable (g : X → ℝ) :=
  g.2.1

theorem boundedMeasurableReal.exists_bound (g : boundedMeasurableReal X) :
    ∃ C, 0 ≤ C ∧ ∀ x, |(g : X → ℝ) x| ≤ C := by
  obtain ⟨C, hC⟩ := g.2.2
  exact ⟨|C|, abs_nonneg C, fun x => (hC x).trans (le_abs_self C)⟩

/-- The `⋆` of real functions is trivial. -/
@[simp] theorem boundedMeasurableReal.star_eq (g : boundedMeasurableReal X) : star g = g :=
  Subtype.ext rfl

/-- A real bounded measurable function, viewed as a complex one. -/
def ofRealBM (g : boundedMeasurableReal X) : boundedMeasurable X :=
  ⟨fun x => ((g : X → ℝ) x : ℂ), Complex.measurable_ofReal.comp g.2.1, by
    obtain ⟨C, hC⟩ := g.2.2
    exact ⟨C, fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x⟩⟩

@[simp] theorem coe_ofRealBM (g : boundedMeasurableReal X) :
    ((ofRealBM g : boundedMeasurable X) : X → ℂ) = fun x => ((g : X → ℝ) x : ℂ) :=
  rfl

theorem ofRealBM_injective : Function.Injective (ofRealBM : boundedMeasurableReal X → _) :=
  fun _ _ h => Subtype.ext (funext fun x => Complex.ofReal_injective (congrFun (congrArg
    Subtype.val h) x))

@[simp] theorem ofRealBM_zero : ofRealBM (0 : boundedMeasurableReal X) = 0 :=
  Subtype.ext (funext fun _ => Complex.ofReal_zero)

@[simp] theorem ofRealBM_one : ofRealBM (1 : boundedMeasurableReal X) = 1 :=
  Subtype.ext (funext fun _ => Complex.ofReal_one)

theorem ofRealBM_add (f g : boundedMeasurableReal X) :
    ofRealBM (f + g) = ofRealBM f + ofRealBM g :=
  Subtype.ext (funext fun _ => Complex.ofReal_add _ _)

theorem ofRealBM_mul (f g : boundedMeasurableReal X) :
    ofRealBM (f * g) = ofRealBM f * ofRealBM g :=
  Subtype.ext (funext fun _ => Complex.ofReal_mul _ _)

theorem ofRealBM_smul (r : ℝ) (g : boundedMeasurableReal X) :
    ofRealBM (r • g) = (r : ℂ) • ofRealBM g :=
  Subtype.ext (funext fun _ => by
    change (((r • (g : X → ℝ)) _ : ℝ) : ℂ) = (r : ℂ) * ((g : X → ℝ) _ : ℂ)
    rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul])

theorem ofRealBM_algebraMap (r : ℝ) :
    ofRealBM (algebraMap ℝ (boundedMeasurableReal X) r) = algebraMap ℂ _ (r : ℂ) :=
  Subtype.ext rfl

/-- A real function is self-conjugate as a complex function. -/
@[simp] theorem star_ofRealBM (g : boundedMeasurableReal X) : star (ofRealBM g) = ofRealBM g :=
  Subtype.ext (funext fun _ => Complex.conj_ofReal _)

/-- The real part of a complex bounded measurable function. -/
def reBM (h : boundedMeasurable X) : boundedMeasurableReal X :=
  ⟨fun x => ((h : X → ℂ) x).re, Complex.measurable_re.comp (boundedMeasurable.measurable h), by
    obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound h
    exact ⟨C, fun x => (Complex.abs_re_le_norm _).trans (hC x)⟩⟩

/-- The imaginary part of a complex bounded measurable function. -/
def imBM (h : boundedMeasurable X) : boundedMeasurableReal X :=
  ⟨fun x => ((h : X → ℂ) x).im, Complex.measurable_im.comp (boundedMeasurable.measurable h), by
    obtain ⟨C, -, hC⟩ := boundedMeasurable.exists_bound h
    exact ⟨C, fun x => (Complex.abs_im_le_norm _).trans (hC x)⟩⟩

@[simp] theorem coe_reBM (h : boundedMeasurable X) :
    ((reBM h : boundedMeasurableReal X) : X → ℝ) = fun x => ((h : X → ℂ) x).re :=
  rfl

@[simp] theorem coe_imBM (h : boundedMeasurable X) :
    ((imBM h : boundedMeasurableReal X) : X → ℝ) = fun x => ((h : X → ℂ) x).im :=
  rfl

@[simp] theorem reBM_ofRealBM (g : boundedMeasurableReal X) : reBM (ofRealBM g) = g :=
  Subtype.ext (funext fun _ => Complex.ofReal_re _)

@[simp] theorem imBM_ofRealBM (g : boundedMeasurableReal X) : imBM (ofRealBM g) = 0 :=
  Subtype.ext (funext fun x => Complex.ofReal_im ((g : X → ℝ) x))

theorem reBM_add (f g : boundedMeasurable X) : reBM (f + g) = reBM f + reBM g :=
  Subtype.ext (funext fun _ => Complex.add_re _ _)

theorem imBM_add (f g : boundedMeasurable X) : imBM (f + g) = imBM f + imBM g :=
  Subtype.ext (funext fun _ => Complex.add_im _ _)

theorem reBM_mul (f g : boundedMeasurable X) :
    reBM (f * g) = reBM f * reBM g - imBM f * imBM g :=
  Subtype.ext (funext fun _ => Complex.mul_re _ _)

theorem imBM_mul (f g : boundedMeasurable X) :
    imBM (f * g) = reBM f * imBM g + imBM f * reBM g :=
  Subtype.ext (funext fun _ => Complex.mul_im _ _)

@[simp] theorem reBM_zero : reBM (0 : boundedMeasurable X) = 0 := Subtype.ext rfl
@[simp] theorem imBM_zero : imBM (0 : boundedMeasurable X) = 0 := Subtype.ext rfl
@[simp] theorem reBM_one : reBM (1 : boundedMeasurable X) = 1 := Subtype.ext rfl
@[simp] theorem imBM_one : imBM (1 : boundedMeasurable X) = 0 := Subtype.ext rfl

theorem reBM_star (h : boundedMeasurable X) : reBM (star h) = reBM h :=
  Subtype.ext (funext fun _ => Complex.conj_re _)

theorem imBM_star (h : boundedMeasurable X) : imBM (star h) = -imBM h :=
  Subtype.ext (funext fun _ => Complex.conj_im _)

theorem reBM_algebraMap (c : ℂ) :
    reBM (algebraMap ℂ (boundedMeasurable X) c) = algebraMap ℝ _ c.re :=
  Subtype.ext rfl

theorem imBM_algebraMap (c : ℂ) :
    imBM (algebraMap ℂ (boundedMeasurable X) c) = algebraMap ℝ _ c.im :=
  Subtype.ext rfl

end BoundedMeasurableReal

/-! ### Conjugation of operators on the complexification -/

namespace Complexification

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The conjugation of `E_ℂ` as a continuous conjugate-linear map. -/
def conjL : Complexification E →L⋆[ℂ] Complexification E :=
  (conj : Complexification E ≃ₗᵢ⋆[ℂ] Complexification E).toContinuousLinearEquiv
    |>.toContinuousLinearMap

@[simp] theorem conjL_apply (z : Complexification E) : conjL z = conj z := rfl

/-- The conjugate `z ↦ conj (B (conj z))` of a complex-linear operator `B` on `E_ℂ`. -/
def conjOp (B : Complexification E →L[ℂ] Complexification E) :
    Complexification E →L[ℂ] Complexification E :=
  conjL.comp (B.comp conjL)

@[simp] theorem conjOp_apply (B : Complexification E →L[ℂ] Complexification E)
    (z : Complexification E) : conjOp B z = conj (B (conj z)) := rfl

@[simp] theorem conjOp_one : conjOp (1 : Complexification E →L[ℂ] Complexification E) = 1 :=
  ContinuousLinearMap.ext fun z => conj_conj z

@[simp] theorem conjOp_zero : conjOp (0 : Complexification E →L[ℂ] Complexification E) = 0 :=
  ContinuousLinearMap.ext fun _ => map_zero conj

theorem conjOp_mul (B C : Complexification E →L[ℂ] Complexification E) :
    conjOp (B * C) = conjOp B * conjOp C :=
  ContinuousLinearMap.ext fun z => by
    change conj (B (C (conj z))) = conj (B (conj (conj (C (conj z)))))
    rw [conj_conj]

theorem conjOp_add (B C : Complexification E →L[ℂ] Complexification E) :
    conjOp (B + C) = conjOp B + conjOp C :=
  ContinuousLinearMap.ext fun _ => map_add conj _ _

theorem conjOp_smul (c : ℂ) (B : Complexification E →L[ℂ] Complexification E) :
    conjOp (c • B) = starRingEnd ℂ c • conjOp B :=
  ContinuousLinearMap.ext fun z => by
    change conj (c • B (conj z)) = starRingEnd ℂ c • conj (B (conj z))
    exact map_smulₛₗ conj c (B (conj z))

theorem conjOp_algebraMap (c : ℂ) :
    conjOp (algebraMap ℂ (Complexification E →L[ℂ] Complexification E) (starRingEnd ℂ c)) =
      algebraMap ℂ _ c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, conjOp_smul, conjOp_one,
    Complex.conj_conj]

theorem norm_conjOp_le (B : Complexification E →L[ℂ] Complexification E) :
    ‖conjOp B‖ ≤ ‖B‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun z => by
    rw [conjOp_apply, LinearIsometryEquiv.norm_map]
    exact (B.le_opNorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

/-- The adjoint of a conjugate is the conjugate of the adjoint. -/
theorem adjoint_conjOp [CompleteSpace E] (B : Complexification E →L[ℂ] Complexification E) :
    ContinuousLinearMap.adjoint (conjOp B) = conjOp (ContinuousLinearMap.adjoint B) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  rw [conjOp_apply, conjOp_apply]
  calc ⟪conj (ContinuousLinearMap.adjoint B (conj z)), w⟫_ℂ
      = ⟪conj (ContinuousLinearMap.adjoint B (conj z)), conj (conj w)⟫_ℂ := by rw [conj_conj]
    _ = ⟪B (conj w), conj z⟫_ℂ := by
        rw [inner_conj_conj', ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪conj (conj z), conj (B (conj w))⟫_ℂ := by rw [inner_conj_conj']
    _ = ⟪z, conj (B (conj w))⟫_ℂ := by rw [conj_conj]

end Complexification

open Complexification

/-! ### Conjugation symmetry of the calculus of `A_ℂ` -/

section ConjSymmetry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E}

/-- The complexification `A_ℂ` of a self-adjoint `A` is self-adjoint. -/
theorem _root_.IsSelfAdjoint.complexify (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (complexifyPMap A) :=
  hA.complexifyPMap

variable (hA : IsSelfAdjoint A)

/-- The conjugated calculus `h ↦ conj ∘ h̄(A_ℂ) ∘ conj`, a `⋆`-homomorphism. -/
def conjCalc :
    boundedMeasurable ℝ →⋆ₐ[ℂ] (Complexification E →L[ℂ] Complexification E) where
  toFun h := conjOp (selfAdjointCalc hA.complexify (star h))
  map_one' := by rw [star_one, map_one, conjOp_one]
  map_mul' f g := by rw [star_mul', map_mul, conjOp_mul]
  map_zero' := by rw [star_zero, map_zero, conjOp_zero]
  map_add' f g := by rw [star_add, map_add, conjOp_add]
  commutes' c := by
    change conjOp (selfAdjointCalc hA.complexify (star (algebraMap ℂ _ c))) = _
    rw [← algebraMap_star_comm, AlgHomClass.commutes]
    exact conjOp_algebraMap c
  map_star' h := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_conjOp,
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star]

theorem conjCalc_apply (h : boundedMeasurable ℝ) (z : Complexification E) :
    conjCalc hA h z = conj (selfAdjointCalc hA.complexify (star h) (conj z)) :=
  rfl

/-- The conjugated calculus has properties (b)–(d) of Theorem VIII.5 for `A_ℂ`. -/
theorem isSelfAdjointCalculus_conjCalc : IsSelfAdjointCalculus hA.complexify (conjCalc hA) where
  norm_le h C hC0 hC := by
    refine (norm_conjOp_le _).trans (norm_selfAdjointCalc_le _ _ hC0 fun x => ?_)
    change ‖star ((h : ℝ → ℂ) x)‖ ≤ C
    rw [norm_star]
    exact hC x
  tendsto_self h hb hl ψ hψ := by
    have h1 := tendsto_selfAdjointCalc_apply_self hA.complexify (fun n => star (h n))
      (fun n x => by
        change ‖star ((h n : ℝ → ℂ) x)‖ ≤ |x|
        rw [norm_star]
        exact hb n x)
      (fun x => by
        have e : star (x : ℂ) = x := Complex.conj_ofReal x
        have h2 := (hl x).star
        rw [e] at h2
        exact h2)
      (conj ψ) (conj_mem_complexifyPMap_domain hψ)
    have e : complexifyPMap A ⟨conj ψ, conj_mem_complexifyPMap_domain hψ⟩ =
        conj (complexifyPMap A ⟨ψ, hψ⟩) :=
      complexifyPMap_conj ⟨ψ, hψ⟩
    rw [e] at h1
    have h2 := (conj.continuous.tendsto _).comp h1
    rw [conj_conj] at h2
    exact h2
  tendsto h h₀ C hC hl ψ := by
    have h1 := tendsto_selfAdjointCalc_apply hA.complexify (fun n => star (h n)) (star h₀) C
      (fun n x => by
        change ‖star ((h n : ℝ → ℂ) x)‖ ≤ C
        rw [norm_star]
        exact hC n x)
      (fun x => (hl x).star) (conj ψ)
    exact (conj.continuous.tendsto _).comp h1

/-- By uniqueness in Theorem VIII.5, the conjugated calculus is the calculus of `A_ℂ`. -/
theorem conjCalc_eq : conjCalc hA = selfAdjointCalc hA.complexify :=
  (isSelfAdjointCalculus_conjCalc hA).eq_selfAdjointCalc

/-- **Conjugation symmetry**: `conj (h(A_ℂ) z) = h̄(A_ℂ) (conj z)`. -/
theorem conj_selfAdjointCalc (h : boundedMeasurable ℝ) (z : Complexification E) :
    conj (selfAdjointCalc hA.complexify h z) =
      selfAdjointCalc hA.complexify (star h) (conj z) := by
  have e := DFunLike.congr_fun (DFunLike.congr_fun (conjCalc_eq hA) (star h)) (conj z)
  rw [← e, conjCalc_apply, star_star, conj_conj]

/-- For real `h`, `h(A_ℂ)` commutes with the conjugation. -/
theorem selfAdjointCalc_ofRealBM_conj (h : boundedMeasurableReal ℝ) (z : Complexification E) :
    selfAdjointCalc hA.complexify (ofRealBM h) (conj z) =
      conj (selfAdjointCalc hA.complexify (ofRealBM h) z) := by
  rw [conj_selfAdjointCalc hA, star_ofRealBM]

end ConjSymmetry

/-! ### The functional calculus of `A` -/

section RealCalc

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)

/-- The real operator underlying `h(A_ℂ)` for real `h`, as a plain map. -/
def realCalcCLM (h : boundedMeasurableReal ℝ) : E →L[ℝ] E :=
  descendCLM (selfAdjointCalc hA.complexify (ofRealBM h)) (selfAdjointCalc_ofRealBM_conj hA h)

theorem complexifyCLM_realCalcCLM (h : boundedMeasurableReal ℝ) :
    complexifyCLM (realCalcCLM hA h) = selfAdjointCalc hA.complexify (ofRealBM h) :=
  complexifyCLM_descendCLM _ (selfAdjointCalc_ofRealBM_conj hA h)

/-- **The functional calculus of a self-adjoint operator on a real Hilbert space**
(Reed–Simon I, Theorem VIII.5, p. 262, over `ℝ`): `h(A)` is the real operator whose
complexification is `h(A_ℂ)`.  It is a `⋆`-homomorphism, which is (a). -/
def realCalc : boundedMeasurableReal ℝ →⋆ₐ[ℝ] (E →L[ℝ] E) where
  toFun := realCalcCLM hA
  map_one' := complexifyCLM_injective (by
    rw [complexifyCLM_realCalcCLM, ofRealBM_one, map_one, complexifyCLM_one])
  map_mul' f g := complexifyCLM_injective (by
    rw [complexifyCLM_realCalcCLM, complexifyCLM_mul, complexifyCLM_realCalcCLM,
      complexifyCLM_realCalcCLM, ofRealBM_mul, map_mul])
  map_zero' := complexifyCLM_injective (by
    rw [complexifyCLM_realCalcCLM, ofRealBM_zero, map_zero, complexifyCLM_zero])
  map_add' f g := complexifyCLM_injective (by
    rw [complexifyCLM_realCalcCLM, complexifyCLM_add, complexifyCLM_realCalcCLM,
      complexifyCLM_realCalcCLM, ofRealBM_add, map_add])
  commutes' r := complexifyCLM_injective (by
    rw [complexifyCLM_realCalcCLM, ofRealBM_algebraMap, AlgHomClass.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, complexifyCLM_smul,
      complexifyCLM_one])
  map_star' h := complexifyCLM_injective (by
    rw [boundedMeasurableReal.star_eq, ← star_complexifyCLM, complexifyCLM_realCalcCLM,
      ← map_star, star_ofRealBM])

theorem realCalc_def (h : boundedMeasurableReal ℝ) :
    realCalc hA h = descendCLM (selfAdjointCalc hA.complexify (ofRealBM h))
      (selfAdjointCalc_ofRealBM_conj hA h) :=
  rfl

/-- `h(A)_ℂ = h(A_ℂ)`. -/
theorem complexifyCLM_realCalc (h : boundedMeasurableReal ℝ) :
    complexifyCLM (realCalc hA h) = selfAdjointCalc hA.complexify (ofRealBM h) :=
  complexifyCLM_realCalcCLM hA h

/-- `h(A) x = h(A_ℂ) x` on real vectors. -/
theorem realCalc_apply (h : boundedMeasurableReal ℝ) (x : E) :
    ofReal (realCalc hA h x) = selfAdjointCalc hA.complexify (ofRealBM h) (ofReal x) := by
  rw [← complexifyCLM_realCalc, complexifyCLM_ofReal]

theorem realCalc_apply_eq_re (h : boundedMeasurableReal ℝ) (x : E) :
    realCalc hA h x = (selfAdjointCalc hA.complexify (ofRealBM h) (ofReal x)).re :=
  rfl

/-- (a) `h(A)` is self-adjoint. -/
theorem isSelfAdjoint_realCalc (h : boundedMeasurableReal ℝ) : IsSelfAdjoint (realCalc hA h) := by
  change star (realCalc hA h) = realCalc hA h
  rw [← map_star, boundedMeasurableReal.star_eq]

/-- (b) `‖h(A)‖ ≤ C` when `|h(x)| ≤ C` for all `x`. -/
theorem norm_realCalc_le (h : boundedMeasurableReal ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |(h : ℝ → ℝ) x| ≤ C) : ‖realCalc hA h‖ ≤ C := by
  rw [← norm_complexifyCLM, complexifyCLM_realCalc]
  refine norm_selfAdjointCalc_le _ _ hC0 fun x => ?_
  change ‖(((h : ℝ → ℝ) x : ℝ) : ℂ)‖ ≤ C
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hC x

/-- (c) **`hₙ(A) ψ → A ψ`** for `ψ ∈ D(A)` when `hₙ(x) → x` and `|hₙ(x)| ≤ |x|`. -/
theorem tendsto_realCalc_apply_self (h : ℕ → boundedMeasurableReal ℝ)
    (hbound : ∀ n x, |(h n : ℝ → ℝ) x| ≤ |x|)
    (hlim : ∀ x, Tendsto (fun n => (h n : ℝ → ℝ) x) atTop (𝓝 x))
    (ψ : E) (hψ : ψ ∈ A.domain) :
    Tendsto (fun n => realCalc hA (h n) ψ) atTop (𝓝 (A ⟨ψ, hψ⟩)) := by
  have h1 := tendsto_selfAdjointCalc_apply_self hA.complexify (fun n => ofRealBM (h n))
    (fun n x => by
      change ‖(((h n : ℝ → ℝ) x : ℝ) : ℂ)‖ ≤ |x|
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hbound n x)
    (fun x => (Complex.continuous_ofReal.tendsto x).comp (hlim x))
    (ofReal ψ) (ofReal_mem_complexifyPMap_domain hψ)
  rw [complexifyPMap_ofReal hψ] at h1
  exact (reCLM.continuous.tendsto _).comp h1

/-- (d) If `hₙ → h` pointwise with `|hₙ| ≤ C`, then `hₙ(A) ψ → h(A) ψ`. -/
theorem tendsto_realCalc_apply (h : ℕ → boundedMeasurableReal ℝ) (h₀ : boundedMeasurableReal ℝ)
    (C : ℝ) (hC : ∀ n x, |(h n : ℝ → ℝ) x| ≤ C)
    (hlim : ∀ x, Tendsto (fun n => (h n : ℝ → ℝ) x) atTop (𝓝 ((h₀ : ℝ → ℝ) x))) (ψ : E) :
    Tendsto (fun n => realCalc hA (h n) ψ) atTop (𝓝 (realCalc hA h₀ ψ)) := by
  have h1 := tendsto_selfAdjointCalc_apply hA.complexify (fun n => ofRealBM (h n)) (ofRealBM h₀) C
    (fun n x => by
      change ‖(((h n : ℝ → ℝ) x : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hC n x)
    (fun x => (Complex.continuous_ofReal.tendsto _).comp (hlim x)) (ofReal ψ)
  exact (reCLM.continuous.tendsto _).comp h1

/-- (e) **Eigenvectors**: if `A ψ = λ ψ`, then `h(A) ψ = h(λ) ψ`. -/
theorem realCalc_apply_of_eigen (h : boundedMeasurableReal ℝ) {ψ : E} (hψ : ψ ∈ A.domain)
    {l : ℝ} (heig : A ⟨ψ, hψ⟩ = l • ψ) : realCalc hA h ψ = (h : ℝ → ℝ) l • ψ := by
  have he : complexifyPMap A ⟨ofReal ψ, ofReal_mem_complexifyPMap_domain hψ⟩ =
      (l : ℂ) • ofReal ψ := by
    rw [complexifyPMap_ofReal hψ, heig, map_smul, Complex.coe_smul]
  apply ofReal_injective
  rw [realCalc_apply, selfAdjointCalc_apply_of_eigen hA.complexify (ofRealBM h) _ he, map_smul,
    ← Complex.coe_smul]
  rfl

/-- (f) **`h ≥ 0` implies `h(A) ≥ 0`**, as positivity of the operator. -/
theorem isPositive_realCalc {h : boundedMeasurableReal ℝ} (hh : ∀ x, 0 ≤ (h : ℝ → ℝ) x) :
    (realCalc hA h).IsPositive := by
  rw [realCalc_def, isPositive_descendCLM_iff]
  exact isPositive_selfAdjointCalc hA.complexify fun x => Complex.zero_le_real.mpr (hh x)

/-- (f) `h ≥ 0` implies `0 ≤ h(A)` in the Loewner order. -/
theorem realCalc_nonneg {h : boundedMeasurableReal ℝ} (hh : ∀ x, 0 ≤ (h : ℝ → ℝ) x) :
    0 ≤ realCalc hA h :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_realCalc hA hh)

end RealCalc

/-! ### Uniqueness -/

section Unique

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E}

/-- **A functional calculus for the self-adjoint operator `A` on a real Hilbert space**
(Reed–Simon I, Theorem VIII.5 (b)–(d), p. 262, over `ℝ`), for a `⋆`-homomorphism `Φ` from the
bounded real Borel functions on `ℝ` to `𝓛(E)`: (b) `‖Φ(h)‖ ≤ ‖h‖∞`; (c) if `hₙ(x) → x` and
`|hₙ(x)| ≤ |x|`, then `Φ(hₙ) ψ → A ψ` for `ψ ∈ D(A)`; (d) if `hₙ → h` pointwise with `‖hₙ‖∞`
bounded, then `Φ(hₙ) → Φ(h)` strongly. -/
structure IsRealSelfAdjointCalculus (hA : IsSelfAdjoint A)
    (Φ : boundedMeasurableReal ℝ →⋆ₐ[ℝ] (E →L[ℝ] E)) : Prop where
  norm_le : ∀ (h : boundedMeasurableReal ℝ) (C : ℝ), 0 ≤ C → (∀ x, |(h : ℝ → ℝ) x| ≤ C) →
    ‖Φ h‖ ≤ C
  tendsto_self : ∀ (h : ℕ → boundedMeasurableReal ℝ), (∀ n x, |(h n : ℝ → ℝ) x| ≤ |x|) →
    (∀ x, Tendsto (fun n => (h n : ℝ → ℝ) x) atTop (𝓝 x)) →
    ∀ (ψ : E) (hψ : ψ ∈ A.domain), Tendsto (fun n => Φ (h n) ψ) atTop (𝓝 (A ⟨ψ, hψ⟩))
  tendsto : ∀ (h : ℕ → boundedMeasurableReal ℝ) (h₀ : boundedMeasurableReal ℝ) (C : ℝ),
    (∀ n x, |(h n : ℝ → ℝ) x| ≤ C) →
    (∀ x, Tendsto (fun n => (h n : ℝ → ℝ) x) atTop (𝓝 ((h₀ : ℝ → ℝ) x))) →
    ∀ ψ : E, Tendsto (fun n => Φ (h n) ψ) atTop (𝓝 (Φ h₀ ψ))

/-- `h ↦ h(A)` has properties (b)–(d) of Theorem VIII.5; (a) holds by construction. -/
theorem isRealSelfAdjointCalculus_realCalc (hA : IsSelfAdjoint A) :
    IsRealSelfAdjointCalculus hA (realCalc hA) where
  norm_le h _ hC0 hC := norm_realCalc_le hA h hC0 hC
  tendsto_self h hb hl ψ hψ := tendsto_realCalc_apply_self hA h hb hl ψ hψ
  tendsto h h₀ C hC hl ψ := tendsto_realCalc_apply hA h h₀ C hC hl ψ

/-- The shift `x ∓ |g|` towards `0` used to split `g` into two sequences as in (c). -/
def shiftAbs (x g : ℝ) : ℝ := if 0 ≤ x then x - |g| else x + |g|

theorem abs_shiftAbs_le {x g : ℝ} (hg : |g| ≤ |x|) :
    |shiftAbs x g| ≤ |x| ∧ |shiftAbs x g + g| ≤ |x| := by
  have h1 := le_abs_self g
  have h2 := neg_abs_le g
  unfold shiftAbs
  split_ifs with hx
  · rw [abs_of_nonneg hx] at hg ⊢
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · rw [abs_of_neg (not_le.mp hx)] at hg ⊢
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem measurable_shiftAbs {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable fun x => shiftAbs x (g x) := by
  unfold shiftAbs
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    (measurable_id.sub (continuous_abs.measurable.comp hg))
    (measurable_id.add (continuous_abs.measurable.comp hg))

/-- `tₙ(x) = (x ∓ |g(x)|) χ_{[-n, n]}(x)`: with `|g| ≤ |x|`, both `tₙ` and `tₙ + g` are bounded by
`|x|`, and `tₙ(x) → x` when `g = gₙ → 0`. -/
def shiftTrunc (g : boundedMeasurableReal ℝ) (n : ℕ) : boundedMeasurableReal ℝ :=
  ⟨fun x : ℝ => if |x| ≤ (n : ℝ) then shiftAbs x ((g : ℝ → ℝ) x) else 0,
    Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      (measurable_shiftAbs (boundedMeasurableReal.measurable g)) measurable_const, by
    obtain ⟨C, -, hC⟩ := boundedMeasurableReal.exists_bound g
    refine ⟨n + C, fun x => ?_⟩
    have hC' := hC x
    change |(if |x| ≤ (n : ℝ) then shiftAbs x ((g : ℝ → ℝ) x) else 0)| ≤ n + C
    split_ifs with hx
    · unfold shiftAbs
      have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      split_ifs
      · exact (abs_sub _ _).trans (by rw [abs_abs]; linarith)
      · exact (abs_add_le _ _).trans (by rw [abs_abs]; linarith)
    · rw [abs_zero]
      linarith [abs_nonneg ((g : ℝ → ℝ) x), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩

theorem coe_shiftTrunc (g : boundedMeasurableReal ℝ) (n : ℕ) :
    ((shiftTrunc g n : boundedMeasurableReal ℝ) : ℝ → ℝ) =
      fun x : ℝ => if |x| ≤ (n : ℝ) then shiftAbs x ((g : ℝ → ℝ) x) else 0 :=
  rfl

theorem abs_shiftTrunc_le {g : boundedMeasurableReal ℝ} {x : ℝ}
    (hg : |(g : ℝ → ℝ) x| ≤ |x|) (n : ℕ) :
    |(shiftTrunc g n : ℝ → ℝ) x| ≤ |x| ∧
      |(shiftTrunc g n : ℝ → ℝ) x + (g : ℝ → ℝ) x| ≤ |x| := by
  rw [coe_shiftTrunc]
  dsimp only
  split_ifs
  · exact abs_shiftAbs_le hg
  · rw [abs_zero, zero_add]
    exact ⟨abs_nonneg x, hg⟩

theorem tendsto_shiftTrunc {g : ℕ → boundedMeasurableReal ℝ} {x : ℝ}
    (hl : Tendsto (fun n => (g n : ℝ → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => (shiftTrunc (g n) n : ℝ → ℝ) x) atTop (𝓝 x) := by
  have hs : Tendsto (fun n => shiftAbs x ((g n : ℝ → ℝ) x)) atTop (𝓝 x) := by
    unfold shiftAbs
    split_ifs
    · simpa using tendsto_const_nhds.sub hl.abs
    · simpa using tendsto_const_nhds.add hl.abs
  refine hs.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with n hn
  have hx : |x| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [coe_shiftTrunc]
  exact (ite_eq_left hx).symm

namespace IsRealSelfAdjointCalculus

variable {hA : IsSelfAdjoint A} {Φ : boundedMeasurableReal ℝ →⋆ₐ[ℝ] (E →L[ℝ] E)}

/-- A consequence of (c): if `gₙ → 0` pointwise and `|gₙ(x)| ≤ |x|`, then `Φ(gₙ) ψ → 0` for
`ψ ∈ D(A)`.  Write `gₙ = (tₙ + gₙ) - tₙ` and apply (c) to both `tₙ + gₙ` and `tₙ`. -/
theorem tendsto_apply_zero (hΦ : IsRealSelfAdjointCalculus hA Φ)
    (g : ℕ → boundedMeasurableReal ℝ) (hb : ∀ n x, |(g n : ℝ → ℝ) x| ≤ |x|)
    (hl : ∀ x, Tendsto (fun n => (g n : ℝ → ℝ) x) atTop (𝓝 0)) (ψ : E) (hψ : ψ ∈ A.domain) :
    Tendsto (fun n => Φ (g n) ψ) atTop (𝓝 0) := by
  let t : ℕ → boundedMeasurableReal ℝ := fun n => shiftTrunc (g n) n
  have h1 := hΦ.tendsto_self (fun n => t n + g n) (fun n x => (abs_shiftTrunc_le (hb n x) n).2)
    (fun x => by simpa using (tendsto_shiftTrunc (hl x)).add (hl x)) ψ hψ
  have h2 := hΦ.tendsto_self t (fun n x => (abs_shiftTrunc_le (hb n x) n).1)
    (fun x => tendsto_shiftTrunc (hl x)) ψ hψ
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine h3.congr fun n => ?_
  rw [map_add, add_apply, add_sub_cancel_left]

end IsRealSelfAdjointCalculus

/-! #### The complexification `Φ_ℂ(h) = Φ(Re h)_ℂ + i Φ(Im h)_ℂ` of a real calculus -/

omit [CompleteSpace E] in
theorem complexifyCLM_apply_eq (T : E →L[ℝ] E) (z : Complexification E) :
    complexifyCLM T z = ofReal (T z.re) + Complex.I • ofReal (T z.im) :=
  (ofReal_add_I_smul _).symm

omit [CompleteSpace E] in
/-- If `Tₙ x → a` and `Tₙ y → b`, then `(Tₙ)_ℂ (x + i y) → a + i b`. -/
theorem tendsto_complexifyCLM_apply {ι : Type*} {l : Filter ι} {T : ι → E →L[ℝ] E}
    {z : Complexification E} {a b : E} (ha : Tendsto (fun n => T n z.re) l (𝓝 a))
    (hb : Tendsto (fun n => T n z.im) l (𝓝 b)) :
    Tendsto (fun n => complexifyCLM (T n) z) l (𝓝 ⟨a, b⟩) := by
  simp only [complexifyCLM_apply_eq]
  rw [mk_eq]
  exact ((ofReal.continuous.tendsto _).comp ha).add
    (((ofReal.continuous.tendsto _).comp hb).const_smul Complex.I)

theorem complex_combo_mul (a b c d : Complexification E →L[ℂ] Complexification E) :
    (a + Complex.I • b) * (c + Complex.I • d) =
      (a * c - b * d) + Complex.I • (a * d + b * c) := by
  rw [add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    smul_smul, Complex.I_mul_I]
  module

omit [CompleteSpace E] in
theorem add_I_smul_zero (a : Complexification E →L[ℂ] Complexification E) :
    a + Complex.I • (0 : Complexification E →L[ℂ] Complexification E) = a := by
  module

variable (Φ : boundedMeasurableReal ℝ →⋆ₐ[ℝ] (E →L[ℝ] E))

/-- The complexification `Φ_ℂ(h) = Φ(Re h)_ℂ + i Φ(Im h)_ℂ` of a real calculus, a
`⋆`-homomorphism on the complex bounded Borel functions. -/
def complexifyCalc :
    boundedMeasurable ℝ →⋆ₐ[ℂ] (Complexification E →L[ℂ] Complexification E) where
  toFun h := complexifyCLM (Φ (reBM h)) + Complex.I • complexifyCLM (Φ (imBM h))
  map_one' := by
    rw [reBM_one, imBM_one, map_one, map_zero, complexifyCLM_one, complexifyCLM_zero,
      add_I_smul_zero]
  map_mul' f g := by
    simp only [reBM_mul, imBM_mul, map_sub, map_add, map_mul, complexifyCLM_sub,
      complexifyCLM_add, complexifyCLM_mul, complex_combo_mul]
  map_zero' := by
    rw [reBM_zero, imBM_zero, map_zero, complexifyCLM_zero, add_I_smul_zero]
  map_add' f g := by
    rw [reBM_add, imBM_add, map_add, map_add, complexifyCLM_add, complexifyCLM_add]
    module
  commutes' c := by
    rw [reBM_algebraMap, imBM_algebraMap, AlgHomClass.commutes, AlgHomClass.commutes]
    simp only [Algebra.algebraMap_eq_smul_one, complexifyCLM_smul, complexifyCLM_one, smul_smul]
    have hc : c • (1 : Complexification E →L[ℂ] Complexification E) =
        ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • 1 := by
      rw [Complex.re_add_im]
    rw [hc]
    module
  map_star' h := by
    have hI : star Complex.I = -Complex.I := Complex.conj_I
    simp only [reBM_star, imBM_star, map_neg, complexifyCLM_neg, star_add, star_smul,
      star_complexifyCLM, ← map_star, boundedMeasurableReal.star_eq, hI]
    module

theorem complexifyCalc_apply (h : boundedMeasurable ℝ) :
    complexifyCalc Φ h = complexifyCLM (Φ (reBM h)) + Complex.I • complexifyCLM (Φ (imBM h)) :=
  rfl

namespace IsRealSelfAdjointCalculus

variable {hA : IsSelfAdjoint A} {Φ}

/-- (b) for `Φ_ℂ`, from the `C⋆`-identity `‖Φ_ℂ(h)‖² = ‖Φ_ℂ(|h|²)‖ = ‖Φ(|h|²)‖`. -/
theorem norm_complexifyCalc_le (hΦ : IsRealSelfAdjointCalculus hA Φ) (h : boundedMeasurable ℝ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖(h : ℝ → ℂ) x‖ ≤ C) : ‖complexifyCalc Φ h‖ ≤ C := by
  have him : imBM (star h * h) = 0 := Subtype.ext (funext fun x => by
    change ((starRingEnd ℂ ((h : ℝ → ℂ) x)) * (h : ℝ → ℂ) x).im = 0
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring)
  have hb : ‖Φ (reBM (star h * h))‖ ≤ C * C :=
    hΦ.norm_le _ _ (mul_nonneg hC0 hC0) fun x => by
      change |((starRingEnd ℂ ((h : ℝ → ℂ) x)) * (h : ℝ → ℂ) x).re| ≤ C * C
      have e : ((starRingEnd ℂ ((h : ℝ → ℂ) x)) * (h : ℝ → ℂ) x).re =
          ‖(h : ℝ → ℂ) x‖ * ‖(h : ℝ → ℂ) x‖ := by
        rw [← sq, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
          Complex.conj_im]
        ring
      rw [e, abs_of_nonneg (mul_self_nonneg _)]
      exact mul_self_le_mul_self (norm_nonneg _) (hC x)
  have key : ‖complexifyCalc Φ h‖ * ‖complexifyCalc Φ h‖ ≤ C * C := by
    rw [← CStarRing.norm_star_mul_self, ← map_star, ← map_mul, complexifyCalc_apply, him,
      map_zero, complexifyCLM_zero, add_I_smul_zero, norm_complexifyCLM]
    exact hb
  exact (mul_self_le_mul_self_iff (norm_nonneg _) hC0).mpr key

/-- `Φ_ℂ` has properties (b)–(d) of Theorem VIII.5 for `A_ℂ`. -/
theorem isSelfAdjointCalculus_complexifyCalc (hΦ : IsRealSelfAdjointCalculus hA Φ) :
    IsSelfAdjointCalculus hA.complexify (complexifyCalc Φ) where
  norm_le h _ hC0 hC := hΦ.norm_complexifyCalc_le h hC0 hC
  tendsto_self h hb hl z hz := by
    have hre : ∀ (u : E) (hu : u ∈ A.domain),
        Tendsto (fun n => Φ (reBM (h n)) u) atTop (𝓝 (A ⟨u, hu⟩)) :=
      hΦ.tendsto_self (fun n => reBM (h n))
        (fun n x => (Complex.abs_re_le_norm _).trans (hb n x))
        (fun x => by
          have h0 := (Complex.continuous_re.tendsto _).comp (hl x)
          rw [Complex.ofReal_re] at h0
          exact h0)
    have him : ∀ (u : E) (_ : u ∈ A.domain),
        Tendsto (fun n => Φ (imBM (h n)) u) atTop (𝓝 0) :=
      hΦ.tendsto_apply_zero (fun n => imBM (h n))
        (fun n x => (Complex.abs_im_le_norm _).trans (hb n x))
        (fun x => by
          have h0 := (Complex.continuous_im.tendsto _).comp (hl x)
          rw [Complex.ofReal_im] at h0
          exact h0)
    have hz' := mem_complexifyPMap_domain.mp hz
    have h1 := tendsto_complexifyCLM_apply (hre _ hz'.1) (hre _ hz'.2)
    have h2 := tendsto_complexifyCLM_apply (him _ hz'.1) (him _ hz'.2)
    have h3 := h1.add (h2.const_smul Complex.I)
    have e : (⟨A ⟨z.re, hz'.1⟩, A ⟨z.im, hz'.2⟩⟩ : Complexification E) +
        Complex.I • (⟨0, 0⟩ : Complexification E) = complexifyPMap A ⟨z, hz⟩ := by
      rw [show (⟨0, 0⟩ : Complexification E) = 0 from rfl, smul_zero, add_zero]
      rfl
    rw [e] at h3
    exact h3
  tendsto h h₀ C hC hl z := by
    have hre := hΦ.tendsto (fun n => reBM (h n)) (reBM h₀) C
      (fun n x => (Complex.abs_re_le_norm _).trans (hC n x))
      (fun x => (Complex.continuous_re.tendsto _).comp (hl x))
    have him := hΦ.tendsto (fun n => imBM (h n)) (imBM h₀) C
      (fun n x => (Complex.abs_im_le_norm _).trans (hC n x))
      (fun x => (Complex.continuous_im.tendsto _).comp (hl x))
    have h1 := tendsto_complexifyCLM_apply (hre z.re) (hre z.im)
    have h2 := tendsto_complexifyCLM_apply (him z.re) (him z.im)
    exact h1.add (h2.const_smul Complex.I)

/-- `Φ_ℂ` is the calculus of `A_ℂ`, by uniqueness in Theorem VIII.5. -/
theorem complexifyCalc_eq (hΦ : IsRealSelfAdjointCalculus hA Φ) :
    complexifyCalc Φ = selfAdjointCalc hA.complexify :=
  hΦ.isSelfAdjointCalculus_complexifyCalc.eq_selfAdjointCalc

/-- **Uniqueness of the functional calculus on a real Hilbert space** (Reed–Simon I,
Theorem VIII.5, p. 262, over `ℝ`): a `⋆`-homomorphism with (b)–(d) is `realCalc hA`. -/
theorem eq_realCalc (hΦ : IsRealSelfAdjointCalculus hA Φ) : Φ = realCalc hA := by
  ext1 h
  apply complexifyCLM_injective
  have e := DFunLike.congr_fun hΦ.complexifyCalc_eq (ofRealBM h)
  rw [complexifyCalc_apply, reBM_ofRealBM, imBM_ofRealBM, map_zero, complexifyCLM_zero,
    add_I_smul_zero] at e
  rw [e, complexifyCLM_realCalc]

end IsRealSelfAdjointCalculus

/-- **The spectral theorem for self-adjoint operators on a real Hilbert space, functional
calculus form** (Reed–Simon I, Theorem VIII.5 (a)–(d), p. 262, over `ℝ`): there is exactly one
`⋆`-homomorphism from the bounded real Borel functions on `ℝ` to `𝓛(E)` with (b)–(d), namely
`realCalc hA`. -/
theorem existsUnique_isRealSelfAdjointCalculus (hA : IsSelfAdjoint A) :
    ∃! Φ : boundedMeasurableReal ℝ →⋆ₐ[ℝ] (E →L[ℝ] E), IsRealSelfAdjointCalculus hA Φ :=
  ⟨realCalc hA, isRealSelfAdjointCalculus_realCalc hA, fun _ hΦ => hΦ.eq_realCalc⟩

end Unique

/-! ### Spectral projections -/

section Projections

/-- The real indicator `χ_Ω` of a Borel set `Ω ⊆ ℝ`, as a bounded measurable function. -/
def indicatorBMReal {Ω : Set ℝ} (hΩ : MeasurableSet Ω) : boundedMeasurableReal ℝ :=
  ⟨Ω.indicator fun _ => (1 : ℝ), measurable_const.indicator hΩ, 1, fun x => by
    by_cases hx : x ∈ Ω <;> simp [hx]⟩

theorem coe_indicatorBMReal {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    (indicatorBMReal hΩ : ℝ → ℝ) = Ω.indicator fun _ => (1 : ℝ) :=
  rfl

theorem indicatorBMReal_mul {Ω₁ Ω₂ : Set ℝ} (h₁ : MeasurableSet Ω₁) (h₂ : MeasurableSet Ω₂) :
    indicatorBMReal h₁ * indicatorBMReal h₂ = indicatorBMReal (h₁.inter h₂) := by
  refine Subtype.ext (funext fun x => ?_)
  change Ω₁.indicator (fun _ => (1 : ℝ)) x * Ω₂.indicator (fun _ => (1 : ℝ)) x =
    (Ω₁ ∩ Ω₂).indicator (fun _ => (1 : ℝ)) x
  by_cases hx₁ : x ∈ Ω₁ <;> by_cases hx₂ : x ∈ Ω₂ <;> simp [hx₁, hx₂]

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)

/-- **The spectral projection** `P_Ω = χ_Ω(A)` of a Borel set `Ω ⊆ ℝ` (Reed–Simon I, p. 263). -/
def realSpectralProjection {Ω : Set ℝ} (hΩ : MeasurableSet Ω) : E →L[ℝ] E :=
  realCalc hA (indicatorBMReal hΩ)

theorem realSpectralProjection_congr {Ω₁ Ω₂ : Set ℝ} (h₁ : MeasurableSet Ω₁)
    (h₂ : MeasurableSet Ω₂) (h : Ω₁ = Ω₂) :
    realSpectralProjection hA h₁ = realSpectralProjection hA h₂ := by
  subst h
  rfl

/-- `P_Ω₁ P_Ω₂ = P_{Ω₁ ∩ Ω₂}`. -/
theorem realSpectralProjection_mul {Ω₁ Ω₂ : Set ℝ} (h₁ : MeasurableSet Ω₁)
    (h₂ : MeasurableSet Ω₂) :
    realSpectralProjection hA h₁ * realSpectralProjection hA h₂ =
      realSpectralProjection hA (h₁.inter h₂) := by
  rw [realSpectralProjection, realSpectralProjection, ← map_mul, indicatorBMReal_mul]
  rfl

/-- (a) **`P_Ω` is an orthogonal projection**. -/
theorem isStarProjection_realSpectralProjection {Ω : Set ℝ} (hΩ : MeasurableSet Ω) :
    IsStarProjection (realSpectralProjection hA hΩ) where
  isIdempotentElem := by
    rw [IsIdempotentElem, realSpectralProjection_mul]
    exact realSpectralProjection_congr hA _ _ (Set.inter_self Ω)
  isSelfAdjoint := isSelfAdjoint_realCalc hA _

/-- (b) `P_∅ = 0`. -/
theorem realSpectralProjection_empty : realSpectralProjection hA MeasurableSet.empty = 0 := by
  have h : indicatorBMReal MeasurableSet.empty = 0 := Subtype.ext (funext fun x => by
    change (∅ : Set ℝ).indicator (fun _ => (1 : ℝ)) x = 0
    simp)
  rw [realSpectralProjection, h, map_zero]

/-- (b) `P_ℝ = 1`. -/
theorem realSpectralProjection_univ : realSpectralProjection hA MeasurableSet.univ = 1 := by
  have h : indicatorBMReal MeasurableSet.univ = 1 := Subtype.ext (funext fun x => by
    change (Set.univ : Set ℝ).indicator (fun _ => (1 : ℝ)) x = 1
    simp)
  rw [realSpectralProjection, h, map_one]

/-- (c) **Strong countable additivity**: if the `Ωₙ` are pairwise disjoint, then
`Σ_{n<N} P_Ωₙ x → P_{⋃ Ωₙ} x` (Reed–Simon I, p. 263). -/
theorem tendsto_sum_realSpectralProjection (Ω : ℕ → Set ℝ) (hΩ : ∀ n, MeasurableSet (Ω n))
    (hdisj : Pairwise (Function.onFun Disjoint Ω)) (x : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, realSpectralProjection hA (hΩ n) x) atTop
      (𝓝 (realSpectralProjection hA (MeasurableSet.iUnion hΩ) x)) := by
  have hsum : ∀ N, ∑ n ∈ Finset.range N, realSpectralProjection hA (hΩ n) x =
      realCalc hA (∑ n ∈ Finset.range N, indicatorBMReal (hΩ n)) x := fun N => by
    rw [map_sum, sum_apply]
    rfl
  simp only [hsum]
  have hcoe : ∀ N y, ((∑ n ∈ Finset.range N, indicatorBMReal (hΩ n) :
      boundedMeasurableReal ℝ) : ℝ → ℝ) y =
        ∑ n ∈ Finset.range N, (Ω n).indicator (fun _ => (1 : ℝ)) y := fun N y => by
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    rfl
  have hc : ∀ N y, ((∑ n ∈ Finset.range N, (Ω n).indicator (fun _ => (1 : ℝ)) y : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, (Ω n).indicator (fun _ => (1 : ℂ)) y := fun N y => by
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hy : y ∈ Ω n <;> simp [hy]
  refine tendsto_realCalc_apply hA _ _ 1 (fun N y => ?_) (fun y => ?_) x
  · rw [hcoe, ← Real.norm_eq_abs, ← Complex.norm_real, hc]
    exact (sum_indicator_disjoint Ω hdisj y).1 N
  · simp only [hcoe]
    have hU : (⋃ n, Ω n).indicator (fun _ => (1 : ℂ)) y =
        (((⋃ n, Ω n).indicator (fun _ => (1 : ℝ)) y : ℝ) : ℂ) := by
      by_cases hy : y ∈ ⋃ n, Ω n <;> simp [hy]
    have h2 := (sum_indicator_disjoint Ω hdisj y).2
    rw [hU] at h2
    have h3 := (Complex.continuous_re.tendsto _).comp (h2.congr fun N => (hc N y).symm)
    rw [Complex.ofReal_re] at h3
    exact h3

end Projections

end SpectralTheorem
