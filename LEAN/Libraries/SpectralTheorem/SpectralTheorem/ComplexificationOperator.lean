import SpectralTheorem.Complexification
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Complexification of real operators

For a bounded real operator `T` on a real Hilbert space `E`, its complexification
`T_ℂ (x + i y) = T x + i T y` is a bounded complex operator on `E_ℂ` with `‖T_ℂ‖ = ‖T‖` and
`(T_ℂ)† = (T†)_ℂ`; `T ↦ T_ℂ` is an injective `⋆`-algebra homomorphism over `ℝ`, and `T_ℂ` is
self-adjoint (positive) iff `T` is.  Conversely, a bounded complex operator commuting with the
conjugation of `E_ℂ` is the complexification of the real operator `x ↦ Re B x`.

For an unbounded real operator `A` with domain `D(A)`, its complexification has domain
`D(A) ⊕ i D(A)` and acts componentwise.  For densely defined `A`, `(A_ℂ)† = (A†)_ℂ`; hence
`A_ℂ` is self-adjoint iff `A` is.  The proof of the adjoint identity: if `w = u + i v` lies in
`D((A_ℂ)†)` with `(A_ℂ)† w = f + i g`, testing `⟪w, A_ℂ x⟫ = ⟪f + i g, x⟫` against real `x ∈ D(A)`
and taking real and imaginary parts gives `⟪u, A x⟫ = ⟪f, x⟫` and `⟪v, A x⟫ = ⟪g, x⟫`, so
`u, v ∈ D(A†)` with `A† u = f`, `A† v = g`; the converse inclusion is a direct computation.

Reed–Simon I work over complex Hilbert spaces and do not treat complexification; these
statements are the standard device for transferring the spectral theorem to real Hilbert spaces
(milestone M10 of `SCOPING.md`).  Reed–Simon remark (Section VI.4, p. 195) that on real Hilbert
spaces `⟨B x, x⟩ ≥ 0` does not imply self-adjointness; mathlib's `IsPositive` includes symmetry,
and `isPositive_complexifyCLM_iff` is stated for it.  Self-adjointness of `A_ℂ` needs no density
hypothesis: a self-adjoint operator is densely defined, and `D(A)` is dense iff
`D(A) ⊕ i D(A)` is.

## Main definitions and results

* `SpectralTheorem.Complexification.complexifyCLM T`: the complexification of `T : E →L[ℝ] E`,
  with `norm_complexifyCLM`, `adjoint_complexifyCLM`, `isSelfAdjoint_complexifyCLM_iff`,
  `isPositive_complexifyCLM_iff`, and the `⋆`-algebra homomorphism `complexifyHom`.
* `SpectralTheorem.Complexification.descendCLM B hB`: the real operator underlying a complex
  operator `B` that commutes with `conj`; `complexifyCLM_descendCLM`, `descendCLM_complexifyCLM`,
  `adjoint_descendCLM`, `isSelfAdjoint_descendCLM_iff`, `isPositive_descendCLM_iff`.
* `SpectralTheorem.Complexification.complexifyPMap A`: the complexification of an unbounded
  operator `A : E →ₗ.[ℝ] E`, with `dense_complexifyPMap_domain`, `adjoint_complexifyPMap`,
  `isSelfAdjoint_complexifyPMap_iff` and `complexifyPMap_toPMap`.
-/

noncomputable section

open scoped InnerProductSpace

namespace SpectralTheorem

universe u

namespace Complexification

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Bounded operators -/

/-- The complexification `x + i y ↦ T x + i T y` of a real linear map. -/
def complexifyₗ (T : E →ₗ[ℝ] E) : Complexification E →ₗ[ℂ] Complexification E where
  toFun z := ⟨T z.re, T z.im⟩
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp

@[simp] theorem complexifyₗ_apply (T : E →ₗ[ℝ] E) (z : Complexification E) :
    complexifyₗ T z = ⟨T z.re, T z.im⟩ := rfl

theorem norm_complexifyₗ_le (T : E →L[ℝ] E) (z : Complexification E) :
    ‖complexifyₗ (T : E →ₗ[ℝ] E) z‖ ≤ ‖T‖ * ‖z‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [mul_pow, norm_sq_eq, norm_sq_eq]
  have h1 : ‖T z.re‖ ^ 2 ≤ (‖T‖ * ‖z.re‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm z.re) 2
  have h2 : ‖T z.im‖ ^ 2 ≤ (‖T‖ * ‖z.im‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm z.im) 2
  simp only [complexifyₗ_apply, ContinuousLinearMap.coe_coe]
  nlinarith

/-- The complexification `x + i y ↦ T x + i T y` of a bounded real operator. -/
def complexifyCLM (T : E →L[ℝ] E) : Complexification E →L[ℂ] Complexification E :=
  LinearMap.mkContinuous (complexifyₗ (T : E →ₗ[ℝ] E)) ‖T‖ (norm_complexifyₗ_le T)

theorem complexifyCLM_apply (T : E →L[ℝ] E) (z : Complexification E) :
    complexifyCLM T z = ⟨T z.re, T z.im⟩ := rfl

@[simp] theorem complexifyCLM_apply_re (T : E →L[ℝ] E) (z : Complexification E) :
    (complexifyCLM T z).re = T z.re := rfl

@[simp] theorem complexifyCLM_apply_im (T : E →L[ℝ] E) (z : Complexification E) :
    (complexifyCLM T z).im = T z.im := rfl

theorem coe_complexifyCLM (T : E →L[ℝ] E) :
    (complexifyCLM T : Complexification E →ₗ[ℂ] Complexification E) =
      complexifyₗ (T : E →ₗ[ℝ] E) := rfl

@[simp] theorem complexifyCLM_ofReal (T : E →L[ℝ] E) (x : E) :
    complexifyCLM T (ofReal x) = ofReal (T x) := by
  ext <;> simp

/-- `T_ℂ` commutes with the conjugation. -/
theorem complexifyCLM_conj (T : E →L[ℝ] E) (z : Complexification E) :
    complexifyCLM T (conj z) = conj (complexifyCLM T z) := by
  ext <;> simp

/-- Two complex-linear bounded operators on `E_ℂ` agreeing on real vectors are equal. -/
theorem clm_ext {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {f g : Complexification E →L[ℂ] F} (h : ∀ x : E, f (ofReal x) = g (ofReal x)) : f = g := by
  ext z
  rw [← ofReal_add_I_smul z, map_add, map_add, map_smul, map_smul, h, h]

theorem complexifyCLM_comp (S T : E →L[ℝ] E) :
    complexifyCLM (S.comp T) = (complexifyCLM S).comp (complexifyCLM T) := rfl

theorem complexifyCLM_mul (S T : E →L[ℝ] E) :
    complexifyCLM (S * T) = complexifyCLM S * complexifyCLM T := rfl

@[simp] theorem complexifyCLM_one : complexifyCLM (1 : E →L[ℝ] E) = 1 := rfl

@[simp] theorem complexifyCLM_id :
    complexifyCLM (ContinuousLinearMap.id ℝ E) = ContinuousLinearMap.id ℂ _ := rfl

@[simp] theorem complexifyCLM_zero : complexifyCLM (0 : E →L[ℝ] E) = 0 := by
  ext z <;> simp [complexifyCLM_apply]

theorem complexifyCLM_add (S T : E →L[ℝ] E) :
    complexifyCLM (S + T) = complexifyCLM S + complexifyCLM T := by
  ext z <;> simp [complexifyCLM_apply]

theorem complexifyCLM_neg (T : E →L[ℝ] E) : complexifyCLM (-T) = -complexifyCLM T := by
  ext z <;> simp [complexifyCLM_apply]

theorem complexifyCLM_sub (S T : E →L[ℝ] E) :
    complexifyCLM (S - T) = complexifyCLM S - complexifyCLM T := by
  ext z <;> simp [complexifyCLM_apply]

theorem complexifyCLM_smul (r : ℝ) (T : E →L[ℝ] E) :
    complexifyCLM (r • T) = (r : ℂ) • complexifyCLM T := by
  ext z <;> simp [complexifyCLM_apply]

/-- `‖T_ℂ‖ = ‖T‖`. -/
@[simp] theorem norm_complexifyCLM (T : E →L[ℝ] E) : ‖complexifyCLM T‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) ?_
  refine T.opNorm_le_bound (norm_nonneg (complexifyCLM T)) fun x => ?_
  have h := (complexifyCLM T).le_opNorm (ofReal x)
  rwa [complexifyCLM_ofReal, norm_ofReal, norm_ofReal] at h

/-- `T ↦ T_ℂ` is injective. -/
theorem complexifyCLM_injective :
    Function.Injective (complexifyCLM : (E →L[ℝ] E) → _) := by
  intro S T h
  ext x
  have h' := congrArg re (DFunLike.congr_fun h (ofReal x))
  simpa using h'

@[simp] theorem complexifyCLM_inj {S T : E →L[ℝ] E} : complexifyCLM S = complexifyCLM T ↔ S = T :=
  complexifyCLM_injective.eq_iff

theorem re_inner_complexifyCLM_self (T : E →L[ℝ] E) (z : Complexification E) :
    (⟪complexifyCLM T z, z⟫_ℂ).re = ⟪T z.re, z.re⟫_ℝ + ⟪T z.im, z.im⟫_ℝ := by
  simp

section Adjoint

variable [CompleteSpace E]

/-- **The adjoint of a complexification**: `(T_ℂ)† = (T†)_ℂ`. -/
theorem adjoint_complexifyCLM (T : E →L[ℝ] E) :
    ContinuousLinearMap.adjoint (complexifyCLM T) =
      complexifyCLM (ContinuousLinearMap.adjoint T) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  apply Complex.ext <;> simp [ContinuousLinearMap.adjoint_inner_left]

theorem star_complexifyCLM (T : E →L[ℝ] E) : star (complexifyCLM T) = complexifyCLM (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    adjoint_complexifyCLM]

/-- `T_ℂ` is self-adjoint iff `T` is. -/
theorem isSelfAdjoint_complexifyCLM_iff {T : E →L[ℝ] E} :
    IsSelfAdjoint (complexifyCLM T) ↔ IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.isSelfAdjoint_iff',
    adjoint_complexifyCLM, complexifyCLM_inj]

/-- `T_ℂ` is positive iff `T` is. -/
theorem isPositive_complexifyCLM_iff {T : E →L[ℝ] E} :
    (complexifyCLM T).IsPositive ↔ T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_def', ContinuousLinearMap.isPositive_def',
    isSelfAdjoint_complexifyCLM_iff]
  refine and_congr_right fun _ => ⟨fun h x => ?_, fun h z => ?_⟩
  · have h1 := h (ofReal x)
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_complex,
      re_inner_complexifyCLM_self] at h1
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
    simpa using h1
  · have h1 := h z.re
    have h2 := h z.im
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real] at h1 h2
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_complex,
      re_inner_complexifyCLM_self]
    exact add_nonneg h1 h2

/-- The complexification `T ↦ T_ℂ` as a `⋆`-algebra homomorphism over `ℝ`. -/
def complexifyHom : (E →L[ℝ] E) →⋆ₐ[ℝ] (Complexification E →L[ℂ] Complexification E) where
  toFun := complexifyCLM
  map_one' := complexifyCLM_one
  map_mul' := complexifyCLM_mul
  map_zero' := complexifyCLM_zero
  map_add' := complexifyCLM_add
  commutes' r := by
    ext z <;> simp [Algebra.algebraMap_eq_smul_one, complexifyCLM_apply]
  map_star' T := (star_complexifyCLM T).symm

@[simp] theorem complexifyHom_apply (T : E →L[ℝ] E) : complexifyHom T = complexifyCLM T := rfl

end Adjoint

/-! ### Descent of operators commuting with the conjugation -/

/-- The real operator `x ↦ Re (B x)` underlying a complex operator `B` on `E_ℂ` that commutes
with the conjugation. -/
def descendCLM (B : Complexification E →L[ℂ] Complexification E)
    (_hB : ∀ z, B (conj z) = conj (B z)) : E →L[ℝ] E :=
  reCLM.comp ((B.restrictScalars ℝ).comp ofReal)

theorem descendCLM_apply (B : Complexification E →L[ℂ] Complexification E)
    (hB : ∀ z, B (conj z) = conj (B z)) (x : E) : descendCLM B hB x = (B (ofReal x)).re := rfl

theorem apply_ofReal_im {B : Complexification E →L[ℂ] Complexification E}
    (hB : ∀ z, B (conj z) = conj (B z)) (x : E) : (B (ofReal x)).im = 0 :=
  conj_eq_self_iff.mp (by rw [← hB, conj_ofReal])

theorem apply_ofReal_eq {B : Complexification E →L[ℂ] Complexification E}
    (hB : ∀ z, B (conj z) = conj (B z)) (x : E) : B (ofReal x) = ofReal (descendCLM B hB x) := by
  ext
  · rfl
  · exact apply_ofReal_im hB x

/-- An operator commuting with the conjugation is the complexification of its descent. -/
theorem complexifyCLM_descendCLM (B : Complexification E →L[ℂ] Complexification E)
    (hB : ∀ z, B (conj z) = conj (B z)) : complexifyCLM (descendCLM B hB) = B :=
  clm_ext fun x => by rw [complexifyCLM_ofReal, apply_ofReal_eq hB]

/-- The descent of a complexification is the original operator. -/
theorem descendCLM_complexifyCLM (T : E →L[ℝ] E) :
    descendCLM (complexifyCLM T) (complexifyCLM_conj T) = T := by
  ext x
  simp [descendCLM_apply]

/-- A bounded complex operator on `E_ℂ` commutes with the conjugation iff it is a
complexification. -/
theorem commute_conj_iff_exists (B : Complexification E →L[ℂ] Complexification E) :
    (∀ z, B (conj z) = conj (B z)) ↔ ∃ T : E →L[ℝ] E, complexifyCLM T = B :=
  ⟨fun hB => ⟨descendCLM B hB, complexifyCLM_descendCLM B hB⟩,
    fun ⟨T, hT⟩ => hT ▸ complexifyCLM_conj T⟩

/-- Descent is multiplicative. -/
theorem descendCLM_mul {B₁ B₂ : Complexification E →L[ℂ] Complexification E}
    (h₁ : ∀ z, B₁ (conj z) = conj (B₁ z)) (h₂ : ∀ z, B₂ (conj z) = conj (B₂ z)) :
    descendCLM (B₁ * B₂) (fun z => by
        change B₁ (B₂ (conj z)) = conj (B₁ (B₂ z))
        rw [h₂, h₁]) =
      descendCLM B₁ h₁ * descendCLM B₂ h₂ := by
  apply complexifyCLM_injective
  rw [complexifyCLM_mul, complexifyCLM_descendCLM, complexifyCLM_descendCLM,
    complexifyCLM_descendCLM]

/-- Descent preserves the operator norm. -/
theorem norm_descendCLM (B : Complexification E →L[ℂ] Complexification E)
    (hB : ∀ z, B (conj z) = conj (B z)) : ‖descendCLM B hB‖ = ‖B‖ := by
  rw [← norm_complexifyCLM, complexifyCLM_descendCLM]

section DescentAdjoint

variable [CompleteSpace E]

/-- The adjoint of an operator commuting with the conjugation commutes with it. -/
theorem adjoint_commute_conj {B : Complexification E →L[ℂ] Complexification E}
    (hB : ∀ z, B (conj z) = conj (B z)) (z : Complexification E) :
    ContinuousLinearMap.adjoint B (conj z) = conj (ContinuousLinearMap.adjoint B z) := by
  rw [← complexifyCLM_descendCLM B hB, adjoint_complexifyCLM, complexifyCLM_conj]

/-- Descent commutes with adjoints. -/
theorem adjoint_descendCLM (B : Complexification E →L[ℂ] Complexification E)
    (hB : ∀ z, B (conj z) = conj (B z)) :
    ContinuousLinearMap.adjoint (descendCLM B hB) =
      descendCLM (ContinuousLinearMap.adjoint B) (adjoint_commute_conj hB) := by
  apply complexifyCLM_injective
  rw [complexifyCLM_descendCLM, ← adjoint_complexifyCLM, complexifyCLM_descendCLM]

/-- The descent of `B` is self-adjoint iff `B` is. -/
theorem isSelfAdjoint_descendCLM_iff (B : Complexification E →L[ℂ] Complexification E)
    (hB : ∀ z, B (conj z) = conj (B z)) :
    IsSelfAdjoint (descendCLM B hB) ↔ IsSelfAdjoint B := by
  rw [← isSelfAdjoint_complexifyCLM_iff, complexifyCLM_descendCLM]

/-- The descent of `B` is positive iff `B` is. -/
theorem isPositive_descendCLM_iff (B : Complexification E →L[ℂ] Complexification E)
    (hB : ∀ z, B (conj z) = conj (B z)) :
    (descendCLM B hB).IsPositive ↔ B.IsPositive := by
  rw [← isPositive_complexifyCLM_iff, complexifyCLM_descendCLM]

end DescentAdjoint

/-! ### Unbounded operators -/

/-- The complexification `D ⊕ i D` of a real subspace `D`. -/
def complexifySubmodule (p : Submodule ℝ E) : Submodule ℂ (Complexification E) where
  carrier := {z | z.re ∈ p ∧ z.im ∈ p}
  add_mem' hz hw := ⟨p.add_mem hz.1 hw.1, p.add_mem hz.2 hw.2⟩
  zero_mem' := ⟨p.zero_mem, p.zero_mem⟩
  smul_mem' _ _ hz :=
    ⟨p.sub_mem (p.smul_mem _ hz.1) (p.smul_mem _ hz.2),
      p.add_mem (p.smul_mem _ hz.2) (p.smul_mem _ hz.1)⟩

theorem mem_complexifySubmodule {p : Submodule ℝ E} {z : Complexification E} :
    z ∈ complexifySubmodule p ↔ z.re ∈ p ∧ z.im ∈ p := Iff.rfl

@[simp] theorem complexifySubmodule_top : complexifySubmodule (⊤ : Submodule ℝ E) = ⊤ := by
  ext z
  simp [mem_complexifySubmodule]

/-- The real part of a vector of `D ⊕ i D`, as a vector of `D`. -/
def reSub {p : Submodule ℝ E} (z : complexifySubmodule p) : p :=
  ⟨(z : Complexification E).re, (mem_complexifySubmodule.mp z.2).1⟩

/-- The imaginary part of a vector of `D ⊕ i D`, as a vector of `D`. -/
def imSub {p : Submodule ℝ E} (z : complexifySubmodule p) : p :=
  ⟨(z : Complexification E).im, (mem_complexifySubmodule.mp z.2).2⟩

@[simp] theorem coe_reSub {p : Submodule ℝ E} (z : complexifySubmodule p) :
    (reSub z : E) = (z : Complexification E).re := rfl

@[simp] theorem coe_imSub {p : Submodule ℝ E} (z : complexifySubmodule p) :
    (imSub z : E) = (z : Complexification E).im := rfl

/-- The componentwise action `x + i y ↦ A x + i A y` of `A` on `D(A) ⊕ i D(A)`. -/
def complexifyPMapAux (A : E →ₗ.[ℝ] E) :
    complexifySubmodule A.domain →ₗ[ℂ] Complexification E where
  toFun z := ⟨A (reSub z), A (imSub z)⟩
  map_add' z w := by
    have h1 : reSub (z + w) = reSub z + reSub w := rfl
    have h2 : imSub (z + w) = imSub z + imSub w := rfl
    ext
    · exact (congrArg A h1).trans (A.map_add _ _)
    · exact (congrArg A h2).trans (A.map_add _ _)
  map_smul' c z := by
    have h1 : reSub (c • z) = c.re • reSub z - c.im • imSub z := rfl
    have h2 : imSub (c • z) = c.re • imSub z + c.im • reSub z := rfl
    ext
    · change A (reSub (c • z)) = c.re • A (reSub z) - c.im • A (imSub z)
      rw [h1, A.map_sub, A.map_smul, A.map_smul]
    · change A (imSub (c • z)) = c.re • A (imSub z) + c.im • A (reSub z)
      rw [h2, A.map_add, A.map_smul, A.map_smul]

/-- The complexification of an unbounded real operator `A`: domain `D(A) ⊕ i D(A)`, action
`x + i y ↦ A x + i A y`. -/
def complexifyPMap (A : E →ₗ.[ℝ] E) : Complexification E →ₗ.[ℂ] Complexification E where
  domain := complexifySubmodule A.domain
  toFun := complexifyPMapAux A

variable {A : E →ₗ.[ℝ] E}

theorem complexifyPMap_domain (A : E →ₗ.[ℝ] E) :
    (complexifyPMap A).domain = complexifySubmodule A.domain := rfl

@[simp] theorem mem_complexifyPMap_domain {z : Complexification E} :
    z ∈ (complexifyPMap A).domain ↔ z.re ∈ A.domain ∧ z.im ∈ A.domain := Iff.rfl

theorem complexifyPMap_apply (z : (complexifyPMap A).domain) :
    complexifyPMap A z = ⟨A (reSub z), A (imSub z)⟩ := rfl

@[simp] theorem complexifyPMap_apply_re (z : (complexifyPMap A).domain) :
    (complexifyPMap A z).re = A (reSub z) := rfl

@[simp] theorem complexifyPMap_apply_im (z : (complexifyPMap A).domain) :
    (complexifyPMap A z).im = A (imSub z) := rfl

theorem ofReal_mem_complexifyPMap_domain {x : E} (hx : x ∈ A.domain) :
    ofReal x ∈ (complexifyPMap A).domain :=
  ⟨hx, A.domain.zero_mem⟩

/-- `A_ℂ` extends `A` on real vectors. -/
theorem complexifyPMap_ofReal {x : E} (hx : x ∈ A.domain) :
    complexifyPMap A ⟨ofReal x, ofReal_mem_complexifyPMap_domain hx⟩ = ofReal (A ⟨x, hx⟩) := by
  ext
  · rfl
  · exact A.map_zero

theorem conj_mem_complexifyPMap_domain {z : Complexification E}
    (hz : z ∈ (complexifyPMap A).domain) : conj z ∈ (complexifyPMap A).domain :=
  ⟨hz.1, A.domain.neg_mem hz.2⟩

/-- `A_ℂ` commutes with the conjugation. -/
theorem complexifyPMap_conj (z : (complexifyPMap A).domain) :
    complexifyPMap A ⟨conj z, conj_mem_complexifyPMap_domain z.2⟩ = conj (complexifyPMap A z) := by
  ext
  · rfl
  · exact A.map_neg (imSub z)

/-- `D(A) ⊕ i D(A)` is dense when `D(A)` is. -/
theorem dense_complexifyPMap_domain (hA : Dense (A.domain : Set E)) :
    Dense ((complexifyPMap A).domain : Set (Complexification E)) := by
  let φ : E × E → Complexification E := fun q => ⟨q.1, q.2⟩
  have hφ : φ = fun q => ofReal q.1 + Complex.I • ofReal q.2 := funext fun q => mk_eq q.1 q.2
  have hc : Continuous φ := by
    rw [hφ]
    exact (ofReal.continuous.comp continuous_fst).add
      ((ofReal.continuous.comp continuous_snd).const_smul Complex.I)
  have hr : DenseRange φ := fun z => subset_closure ⟨(z.re, z.im), rfl⟩
  refine Dense.mono ?_ (hr.dense_image hc (hA.prod hA))
  rintro _ ⟨q, hq, rfl⟩
  exact hq

/-- Conversely, `D(A)` is dense when `D(A) ⊕ i D(A)` is. -/
theorem dense_domain_of_dense_complexifyPMap_domain
    (hC : Dense ((complexifyPMap A).domain : Set (Complexification E))) :
    Dense (A.domain : Set E) := by
  have hr : DenseRange (reCLM : Complexification E →L[ℝ] E) :=
    Function.Surjective.denseRange fun x => ⟨ofReal x, rfl⟩
  refine Dense.mono ?_ (hr.dense_image reCLM.continuous hC)
  rintro _ ⟨z, hz, rfl⟩
  exact hz.1

/-- `A ↦ A_ℂ` is injective on unbounded operators. -/
theorem complexifyPMap_injective :
    Function.Injective (complexifyPMap : (E →ₗ.[ℝ] E) → _) := by
  intro A B h
  have hdom : ∀ x : E, x ∈ A.domain ↔ x ∈ B.domain := fun x => by
    have h' : ofReal x ∈ (complexifyPMap A).domain ↔ ofReal x ∈ (complexifyPMap B).domain := by
      rw [h]
    simpa using h'
  refine LinearPMap.ext (Submodule.ext hdom) fun x hxA hxB => ?_
  obtain ⟨-, hv⟩ := LinearPMap.ext_iff.mp h
  have h3 := @hv (ofReal x) (ofReal_mem_complexifyPMap_domain hxA)
    (ofReal_mem_complexifyPMap_domain hxB)
  rw [complexifyPMap_ofReal hxA, complexifyPMap_ofReal hxB] at h3
  exact ofReal_injective h3

@[simp] theorem complexifyPMap_inj {A B : E →ₗ.[ℝ] E} :
    complexifyPMap A = complexifyPMap B ↔ A = B :=
  complexifyPMap_injective.eq_iff

/-- The complexification of a bounded operator defined everywhere. -/
theorem complexifyPMap_toPMap (T : E →L[ℝ] E) :
    complexifyPMap ((T : E →ₗ[ℝ] E).toPMap ⊤) =
      (complexifyCLM T : Complexification E →ₗ[ℂ] Complexification E).toPMap ⊤ := by
  refine LinearPMap.ext ?_ fun z _ _ => ?_
  · rw [complexifyPMap_domain, LinearMap.toPMap_domain, LinearMap.toPMap_domain,
      complexifySubmodule_top]
  · ext <;> rfl

section UnboundedAdjoint

variable [CompleteSpace E]

/-- The complexification of `A†` is a formal adjoint of the complexification of `A`. -/
theorem isFormalAdjoint_complexifyPMap (hA : Dense (A.domain : Set E)) :
    (complexifyPMap A).IsFormalAdjoint (complexifyPMap (LinearPMap.adjoint A)) := by
  have key : ∀ (x : A.domain) (y : (LinearPMap.adjoint A).domain),
      ⟪A x, (y : E)⟫_ℝ = ⟪(x : E), LinearPMap.adjoint A y⟫_ℝ :=
    (LinearPMap.adjoint_isFormalAdjoint hA).symm
  intro z w
  apply Complex.ext
  · simp only [inner_re, complexifyPMap_apply_re, complexifyPMap_apply_im]
    exact congrArg₂ (· + ·) (key (reSub z) (reSub w)) (key (imSub z) (imSub w))
  · simp only [inner_im, complexifyPMap_apply_re, complexifyPMap_apply_im]
    exact congrArg₂ (· - ·) (key (reSub z) (imSub w)) (key (imSub z) (reSub w))

theorem complexifyPMap_adjoint_le (hA : Dense (A.domain : Set E)) :
    complexifyPMap (LinearPMap.adjoint A) ≤ LinearPMap.adjoint (complexifyPMap A) :=
  LinearPMap.IsFormalAdjoint.le_adjoint (dense_complexifyPMap_domain hA)
    (isFormalAdjoint_complexifyPMap hA)

/-- The real and imaginary parts of a vector of `D((A_ℂ)†)` lie in `D(A†)`. -/
theorem mem_adjoint_domain_of_mem (hA : Dense (A.domain : Set E)) {w : Complexification E}
    (hw : w ∈ (LinearPMap.adjoint (complexifyPMap A)).domain) :
    w.re ∈ (LinearPMap.adjoint A).domain ∧ w.im ∈ (LinearPMap.adjoint A).domain := by
  have hC := LinearPMap.adjoint_isFormalAdjoint (dense_complexifyPMap_domain hA)
  set v := LinearPMap.adjoint (complexifyPMap A) ⟨w, hw⟩
  have key : ∀ (x : E) (hx : x ∈ A.domain), ⟪v, ofReal x⟫_ℂ = ⟪w, ofReal (A ⟨x, hx⟩)⟫_ℂ := by
    intro x hx
    have h := hC ⟨w, hw⟩ ⟨ofReal x, ofReal_mem_complexifyPMap_domain hx⟩
    rw [complexifyPMap_ofReal] at h
    exact h
  refine ⟨LinearPMap.mem_adjoint_domain_of_exists _ ⟨v.re, fun ⟨x, hx⟩ => ?_⟩,
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨v.im, fun ⟨x, hx⟩ => ?_⟩⟩
  · have h := congrArg Complex.re (key x hx)
    simp only [inner_re, ofReal_re, ofReal_im, inner_zero_right, add_zero] at h
    exact h
  · have h := congrArg Complex.im (key x hx)
    simp only [inner_im, ofReal_re, ofReal_im, inner_zero_right, zero_sub, neg_inj] at h
    exact h

/-- **The adjoint of a complexification**: `(A_ℂ)† = (A†)_ℂ` for densely defined `A`. -/
theorem adjoint_complexifyPMap (hA : Dense (A.domain : Set E)) :
    LinearPMap.adjoint (complexifyPMap A) = complexifyPMap (LinearPMap.adjoint A) := by
  have hle := complexifyPMap_adjoint_le hA
  exact (LinearPMap.eq_of_le_of_domain_eq hle
    (le_antisymm hle.1 fun w hw => mem_adjoint_domain_of_mem hA hw)).symm

/-- **Self-adjointness of a complexification**: `A_ℂ` is self-adjoint iff `A` is.  No density
hypothesis is needed: either side forces the domains to be dense. -/
theorem isSelfAdjoint_complexifyPMap_iff :
    IsSelfAdjoint (complexifyPMap A) ↔ IsSelfAdjoint A := by
  constructor
  · intro h
    have hA := dense_domain_of_dense_complexifyPMap_domain h.dense_domain
    rw [LinearPMap.isSelfAdjoint_def, adjoint_complexifyPMap hA, complexifyPMap_inj] at h
    exact h
  · intro h
    rw [LinearPMap.isSelfAdjoint_def, adjoint_complexifyPMap h.dense_domain]
    exact congrArg complexifyPMap h

/-- The complexification of a self-adjoint operator is self-adjoint. -/
theorem _root_.IsSelfAdjoint.complexifyPMap (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (complexifyPMap A) :=
  isSelfAdjoint_complexifyPMap_iff.mpr hA

end UnboundedAdjoint

end Complexification

end SpectralTheorem
