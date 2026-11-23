import Mathlib

/-!
# One-parameter subgroups and the exponential map of a Lie group

Let `G` be a real Lie group of class `C^∞`, modelled on a normed space `E` through a model with
corners `I`, and let `v` be an element of its Lie algebra `GroupLieAlgebra I G`, the tangent space
at the identity.  Mathlib defines the left-invariant vector field `mulInvariantVectorField v`,
whose value at `g` is the image of `v` under the derivative of `h ↦ g * h` at `1`.

This file constructs the one-parameter subgroup of `v` and the exponential map.

* The field `mulInvariantVectorField v` is a `C^1` section of the tangent bundle, and it is
  invariant under left translations (`mfderiv_mul_left_mulInvariantVectorField`).  Hence a left
  translate of an integral curve is an integral curve (`isMIntegralCurveOn_mul_left` and its
  local and global versions).
* A local integral curve through `1` exists on some interval `(-ε, ε)`.  Its left translates are
  integral curves through every point of `G` on the same interval, so the uniform time lemma
  gives global integral curves (`exists_isMIntegralCurve_mulInvariantVectorField`).  Global
  integral curves are unique (`isMIntegralCurve_mulInvariantVectorField_unique`).
* `oneParameter v : ℝ → G` is the global integral curve through `1`, and
  `exp v = oneParameter v 1`.  Uniqueness of integral curves gives
  `oneParameter (a • v) t = oneParameter v (a * t)`, hence `exp (t • v) = oneParameter v t`, and
  the group law `exp ((s + t) • v) = exp (s • v) * exp (t • v)` with its consequences for
  negatives and for natural and integer multiples.
* The curve `t ↦ exp (t • v)` has velocity `v` at time `0` (`hasMFDerivAt_exp_smul_zero`), so
  it determines `v` (`eq_of_exp_smul_eq`).
* A curve `φ : ℝ → G` with `φ (s + t) = φ s * φ t` and velocity `v` at time `0` equals
  `t ↦ exp (t • v)` (`eq_exp_smul_of_map_add`).
* `expHom v : Multiplicative ℝ →* G` packages `t ↦ exp (t • v)` as a monoid homomorphism.

Existence of integral curves needs `E` complete.  The integral curve API of mathlib needs a
manifold without boundary and, both for global uniqueness and for the uniform time lemma behind
global existence, a Hausdorff group.  These hypotheses appear only in the declarations that use
them.  No regularity of `exp` in `v` is proved here.

The Hausdorff property is not a hypothesis: a Lie group in the sense of mathlib is a `T1` space,
because its model space embeds in `E`, and a `T1` topological group is Hausdorff
(`t2Space_of_lieGroup`).  The proofs below supply the instance locally.

## Tangent spaces at equal points

`TangentSpace I g` is definitionally `E` for every `g`, but it is not reducible.  A statement such
as "the velocity of `φ` at time `0` is `v`", for a curve with `φ 0 = 1`, identifies the tangent
spaces at `φ 0` and at `1` through this definitional equality.  The lemma
`hasMFDerivAt_smulRight_iff_of_eq_one` converts such a statement into one which uses
`mulInvariantVectorField v (φ 0)` and needs no identification.  The characterisation of
one-parameter subgroups is given in both forms.
-/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace LieGroupExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-! ### The left-invariant vector field of a Lie algebra element -/

variable (I G) in
/-- A `C^∞` Lie group is of class `C^3` in the sense used by mathlib's `GroupLieAlgebra`. -/
theorem lieGroup_minSmoothness : LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞) (by simp [minSmoothness_of_isRCLikeNormedField])

variable (I G) in
include I in
/-- A Lie group is Hausdorff: it is a `T1` space, as every manifold is, and a `T1` topological
group is Hausdorff.  The integral curve API of mathlib asks for this property. -/
theorem t2Space_of_lieGroup : T2Space G := by
  have : T1Space G := I.t1Space G
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  infer_instance

/-- The left-invariant vector field of `v` is a `C^1` section of the tangent bundle. -/
theorem contMDiff_one_mulInvariantVectorField (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle I G)) := by
  have : LieGroup I (minSmoothness ℝ 3) G := lieGroup_minSmoothness I G
  exact (contMDiff_mulInvariantVectorField v).of_le
    (by simp [minSmoothness_of_isRCLikeNormedField])

omit [LieGroup I ∞ G] in
/-- The left-invariant vector field of `v` takes the value `v` at the identity. -/
@[simp]
theorem mulInvariantVectorField_one (v : GroupLieAlgebra I G) :
    mulInvariantVectorField v (1 : G) = v := by
  have h : (fun x : G => (1 : G) * x) = id := by
    funext x
    simp
  rw [mulInvariantVectorField, h, mfderiv_id]
  rfl

/-- **Left invariance.** The derivative of left multiplication by `g` maps the value of the
invariant vector field at `h` to its value at `g * h`. -/
theorem mfderiv_mul_left_mulInvariantVectorField (v : GroupLieAlgebra I G) (g h : G) :
    mfderiv I I (g * ·) h (mulInvariantVectorField v h) = mulInvariantVectorField v (g * h) := by -- totalisation-audit: allow left multiplication is smooth (`mdifferentiable_mul_left`), so this is its true derivative
  have D : (fun x : G => g * x) ∘ (fun x => h * x) = (fun x : G => g * h * x) := by
    funext x
    simp [mul_assoc]
  have hc := mfderiv_comp (I := I) (I' := I) (I'' := I) (g := fun x : G => g * x)
    (f := fun x : G => h * x) 1 (mdifferentiable_mul_left _) (mdifferentiable_mul_left _)
  rw [D, mul_one] at hc
  exact (DFunLike.congr_fun hc v).symm

/-! ### Left translates of integral curves -/

/-- The velocity of a left translate of a curve tangent to the invariant vector field: the
composition form of left invariance. -/
theorem smulRight_mulInvariantVectorField_mul (v : GroupLieAlgebra I G) (g x : G) :
    (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * x)) =
      (mfderiv I I (g * ·) x) ∘SL (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v x) := by -- totalisation-audit: allow left multiplication is smooth (`mdifferentiable_mul_left`), so this is its true derivative
  rw [← mfderiv_mul_left_mulInvariantVectorField v g x]
  ext
  simp

/-- Left translation of a curve whose velocity within a set is given by the invariant vector
field. -/
theorem hasMFDerivWithinAt_mul_left (v : GroupLieAlgebra I G) (g : G) {γ : ℝ → G} {s : Set ℝ}
    {t : ℝ}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t)))) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun τ => g * γ τ) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t))) := by
  rw [smulRight_mulInvariantVectorField_mul]
  exact (mdifferentiable_mul_left (a := g) (γ t)).hasMFDerivAt.comp_hasMFDerivWithinAt t h

/-- Left translation of a curve whose velocity is given by the invariant vector field. -/
theorem hasMFDerivAt_mul_left (v : GroupLieAlgebra I G) (g : G) {γ : ℝ → G} {t : ℝ}
    (h : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t)))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun τ => g * γ τ) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t))) :=
  (hasMFDerivWithinAt_mul_left v g h.hasMFDerivWithinAt).hasMFDerivAt Filter.univ_mem

variable {v : GroupLieAlgebra I G} {γ γ' : ℝ → G}

/-- A left translate of an integral curve of a left-invariant vector field on a set is again an
integral curve on that set. -/
theorem isMIntegralCurveOn_mul_left {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s) (g : G) :
    IsMIntegralCurveOn (fun t => g * γ t) (mulInvariantVectorField v) s :=
  fun t ht => hasMFDerivWithinAt_mul_left v g (hγ t ht)

/-- A left translate of a local integral curve of a left-invariant vector field is again a local
integral curve. -/
theorem isMIntegralCurveAt_mul_left {t₀ : ℝ}
    (hγ : IsMIntegralCurveAt γ (mulInvariantVectorField v) t₀) (g : G) :
    IsMIntegralCurveAt (fun t => g * γ t) (mulInvariantVectorField v) t₀ :=
  Filter.Eventually.mono hγ fun _ ht => hasMFDerivAt_mul_left v g ht

/-- A left translate of a global integral curve of a left-invariant vector field is again a
global integral curve. -/
theorem isMIntegralCurve_mul_left (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (g : G) :
    IsMIntegralCurve (fun t => g * γ t) (mulInvariantVectorField v) :=
  fun t => hasMFDerivAt_mul_left v g (hγ t)

/-! ### Global existence and uniqueness -/

/-- **Completeness of left-invariant vector fields.** Through every point of the group there is a
global integral curve of the left-invariant vector field of `v`.  A local integral curve through
`1` exists on some `(-ε, ε)`; its left translates give integral curves through every point on the
same interval, and the uniform time lemma applies. -/
theorem exists_isMIntegralCurve_mulInvariantVectorField [CompleteSpace E] [I.Boundaryless]
    (v : GroupLieAlgebra I G) (g : G) :
    ∃ γ : ℝ → G, γ 0 = g ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  have : T2Space G := t2Space_of_lieGroup I G
  have hv := contMDiff_one_mulInvariantVectorField v
  obtain ⟨γ, h0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (I := I) (x₀ := (1 : G)) 0
      hv.contMDiffAt
  rw [isMIntegralCurveAt_iff'] at hγ
  obtain ⟨ε, hε, hγ⟩ := hγ
  have hball : Metric.ball (0 : ℝ) ε = Ioo (-ε) ε := by
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
  rw [hball] at hγ
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε
    (fun x => ⟨fun t => x * γ t, by simp [h0], isMIntegralCurveOn_mul_left hγ x⟩) g

/-- Global integral curves of a left-invariant vector field are determined by their value at one
time. -/
theorem isMIntegralCurve_mulInvariantVectorField_unique [I.Boundaryless] {t₀ : ℝ}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (hγ' : IsMIntegralCurve γ' (mulInvariantVectorField v)) (h : γ t₀ = γ' t₀) : γ = γ' := by
  have : T2Space G := t2Space_of_lieGroup I G
  exact isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (contMDiff_one_mulInvariantVectorField v) hγ hγ' h

/-! ### The one-parameter subgroup of a Lie algebra element -/

section OneParameter

variable [CompleteSpace E] [I.Boundaryless]

/-- The one-parameter subgroup of `v`: the global integral curve through the identity of the
left-invariant vector field of `v`. -/
def oneParameter (v : GroupLieAlgebra I G) : ℝ → G :=
  Classical.choose (exists_isMIntegralCurve_mulInvariantVectorField v 1) -- totalisation-audit: allow existence is the theorem `exists_isMIntegralCurve_mulInvariantVectorField`, so the witness is an integral curve

/-- The one-parameter subgroup of `v` starts at the identity. -/
@[simp]
theorem oneParameter_zero (v : GroupLieAlgebra I G) : oneParameter v 0 = 1 :=
  (Classical.choose_spec (exists_isMIntegralCurve_mulInvariantVectorField v 1)).1

/-- The one-parameter subgroup of `v` is a global integral curve of the left-invariant vector
field of `v`. -/
theorem isMIntegralCurve_oneParameter (v : GroupLieAlgebra I G) :
    IsMIntegralCurve (oneParameter v) (mulInvariantVectorField v) :=
  (Classical.choose_spec (exists_isMIntegralCurve_mulInvariantVectorField v 1)).2

/-- **Uniqueness.** A global integral curve of the left-invariant vector field of `v` which
starts at the identity is the one-parameter subgroup of `v`. -/
theorem eq_oneParameter (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (h0 : γ 0 = 1) :
    γ = oneParameter v :=
  isMIntegralCurve_mulInvariantVectorField_unique (t₀ := 0) hγ (isMIntegralCurve_oneParameter v)
    (by rw [h0, oneParameter_zero])

/-- A global integral curve of the left-invariant vector field of `v` is the left translate, by
its starting point, of the one-parameter subgroup of `v`. -/
theorem eq_mul_oneParameter (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (t : ℝ) :
    γ t = γ 0 * oneParameter v t := by
  have h := isMIntegralCurve_mulInvariantVectorField_unique (t₀ := 0) hγ
    (isMIntegralCurve_mul_left (isMIntegralCurve_oneParameter v) (γ 0)) (by simp)
  exact congrFun h t

/-- The one-parameter subgroup is a homomorphism from the additive group of the reals. -/
theorem oneParameter_add (v : GroupLieAlgebra I G) (s t : ℝ) :
    oneParameter v (s + t) = oneParameter v s * oneParameter v t := by
  have h := eq_mul_oneParameter ((isMIntegralCurve_oneParameter v).comp_add s) t
  simpa [add_comm] using h

/-- The one-parameter subgroup maps negatives to inverses. -/
theorem oneParameter_neg (v : GroupLieAlgebra I G) (t : ℝ) :
    oneParameter v (-t) = (oneParameter v t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← oneParameter_add, neg_add_cancel, oneParameter_zero]

/-- Rescaling the Lie algebra element rescales the time of the one-parameter subgroup.  The case
`a = 0` is included. -/
theorem oneParameter_smul (a : ℝ) (v : GroupLieAlgebra I G) (t : ℝ) :
    oneParameter (a • v) t = oneParameter v (a * t) := by
  have h : IsMIntegralCurve (oneParameter v ∘ (· * a)) (mulInvariantVectorField (a • v)) := by
    rw [mulInvariantVectorField_smul]
    exact (isMIntegralCurve_oneParameter v).comp_mul a
  have h' := eq_oneParameter h (by simp)
  rw [← h', Function.comp_apply, mul_comm]

/-- The one-parameter subgroup of the zero vector is constant. -/
@[simp]
theorem oneParameter_zero_left (t : ℝ) : oneParameter (0 : GroupLieAlgebra I G) t = 1 := by
  rw [← zero_smul ℝ (0 : GroupLieAlgebra I G), oneParameter_smul, zero_mul, oneParameter_zero]

end OneParameter

/-! ### The exponential map -/

section Exp

variable [CompleteSpace E] [I.Boundaryless]

/-- The exponential map of the Lie group `G`: the value at time `1` of the one-parameter subgroup
of `v`. -/
def exp (v : GroupLieAlgebra I G) : G :=
  oneParameter v 1

/-- The curve `t ↦ exp (t • v)` is the one-parameter subgroup of `v`. -/
theorem exp_smul (t : ℝ) (v : GroupLieAlgebra I G) : exp (t • v) = oneParameter v t := by
  rw [exp, oneParameter_smul, mul_one]

/-- The exponential of the zero vector is the identity. -/
@[simp]
theorem exp_zero : exp (0 : GroupLieAlgebra I G) = 1 :=
  oneParameter_zero_left 1

/-- The one-parameter subgroup law for the exponential map. -/
theorem exp_add_smul (s t : ℝ) (v : GroupLieAlgebra I G) :
    exp ((s + t) • v) = exp (s • v) * exp (t • v) := by
  simp only [exp_smul, oneParameter_add]

/-- The exponential map sends negatives to inverses. -/
theorem exp_neg (v : GroupLieAlgebra I G) : exp (-v) = (exp v)⁻¹ := by
  rw [← neg_one_smul ℝ v, exp_smul, oneParameter_neg]
  rfl

/-- The exponential of a negative multiple is the inverse of that of the multiple. -/
theorem exp_neg_smul (t : ℝ) (v : GroupLieAlgebra I G) :
    exp ((-t) • v) = (exp (t • v))⁻¹ := by
  rw [neg_smul, exp_neg]

/-- The exponential of a natural multiple is a power of the exponential. -/
theorem exp_nsmul (n : ℕ) (v : GroupLieAlgebra I G) : exp (n • v) = exp v ^ n := by
  rw [← Nat.cast_smul_eq_nsmul ℝ n v]
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, exp_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, exp_add_smul, ih, one_smul, pow_succ]

/-- The exponential of an integer multiple is an integer power of the exponential. -/
theorem exp_zsmul (n : ℤ) (v : GroupLieAlgebra I G) : exp (n • v) = exp v ^ n := by
  rw [← Int.cast_smul_eq_zsmul ℝ n v]
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast, zpow_natCast, Nat.cast_smul_eq_nsmul, exp_nsmul]
  | negSucc n =>
    rw [Int.cast_negSucc, neg_smul, exp_neg, Nat.cast_smul_eq_nsmul, exp_nsmul, zpow_negSucc]

/-- Elements of one one-parameter subgroup commute. -/
theorem commute_exp_smul (s t : ℝ) (v : GroupLieAlgebra I G) :
    Commute (exp (s • v)) (exp (t • v)) := by
  rw [Commute, SemiconjBy, ← exp_add_smul, ← exp_add_smul, add_comm]

/-- The curve `t ↦ exp (t • v)` is a global integral curve of the left-invariant vector field of
`v`. -/
theorem isMIntegralCurve_exp_smul (v : GroupLieAlgebra I G) :
    IsMIntegralCurve (fun t : ℝ => exp (t • v)) (mulInvariantVectorField v) := by
  have h : (fun t : ℝ => exp (t • v)) = oneParameter v := funext fun t => exp_smul t v
  rw [h]
  exact isMIntegralCurve_oneParameter v

/-- A global integral curve of the left-invariant vector field of `v` is
`t ↦ γ 0 * exp (t • v)`. -/
theorem eq_mul_exp_smul (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (t : ℝ) :
    γ t = γ 0 * exp (t • v) := by
  rw [exp_smul, ← eq_mul_oneParameter hγ]

/-- The velocity of `t ↦ exp (t • v)` at time `t` is the value of the left-invariant vector field
of `v` at `exp (t • v)`. -/
theorem hasMFDerivAt_exp_smul (v : GroupLieAlgebra I G) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => exp (s • v)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (exp (t • v)))) :=
  isMIntegralCurve_exp_smul v t

/-- The curve `t ↦ exp (t • v)` is continuous. -/
theorem continuous_exp_smul (v : GroupLieAlgebra I G) : Continuous fun t : ℝ => exp (t • v) :=
  (isMIntegralCurve_exp_smul v).continuous

end Exp

/-! ### Characterisation of one-parameter subgroups -/

omit [TopologicalSpace G] in
/-- A map `φ : ℝ → G` with `φ (s + t) = φ s * φ t` sends `0` to the identity. -/
theorem map_zero_of_map_add {φ : ℝ → G} (hmul : ∀ s t, φ (s + t) = φ s * φ t) : φ 0 = 1 := by
  have h := hmul 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

omit [LieGroup I ∞ G] in
/-- At a time where a curve passes through the identity, having velocity `v` and having the
velocity given by the left-invariant vector field of `v` are the same condition.  The left-hand
side identifies the tangent spaces at `φ t` and at `1`; the right-hand side does not. -/
theorem hasMFDerivAt_smulRight_iff_of_eq_one {φ : ℝ → G} {t : ℝ} (h1 : φ t = 1)
    (v : GroupLieAlgebra I G) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I φ t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ↔
      HasMFDerivAt 𝓘(ℝ, ℝ) I φ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (φ t))) := by
  have e : ∀ x : G, x = 1 → (mulInvariantVectorField v x : E) = v := by
    rintro x rfl
    exact mulInvariantVectorField_one v
  rw [e (φ t) h1]

/-- A curve `φ : ℝ → G` with `φ (s + t) = φ s * φ t` whose velocity at time `0` is the value at
`φ 0` of the left-invariant vector field of `v` is a global integral curve of that field. -/
theorem isMIntegralCurve_of_map_add {φ : ℝ → G} (hmul : ∀ s t, φ (s + t) = φ s * φ t)
    {v : GroupLieAlgebra I G}
    (hφ : HasMFDerivAt 𝓘(ℝ, ℝ) I φ 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (φ 0)))) :
    IsMIntegralCurve φ (mulInvariantVectorField v) := by
  intro t
  have e0 : t + -t = 0 := add_neg_cancel t
  have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) I φ (t + -t)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (φ (t + -t)))) := by
    rw [e0]
    exact hφ
  have h3 : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ (s + -t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (φ (t + -t)))) := by
    rw [← ContinuousLinearMap.comp_id
      (ContinuousLinearMap.smulRight 1 (mulInvariantVectorField v (φ (t + -t))))]
    apply HasMFDerivAt.comp t h2
    refine ⟨(continuous_add_const _).continuousAt, ?_⟩
    simp only [mfld_simps]
    exact ((hasFDerivAt_id _).add_const _).hasFDerivWithinAt
  have h4 := hasMFDerivAt_mul_left v (φ t) h3
  have hfun : (fun s : ℝ => φ t * φ (s + -t)) = φ := by
    funext s
    rw [← hmul, add_comm s, add_neg_cancel_left]
  have hpt : φ t * φ (t + -t) = φ t := by
    rw [e0, map_zero_of_map_add hmul, mul_one]
  rw [hfun, hpt] at h4
  exact h4

section ExpCharacterisation

variable [CompleteSpace E] [I.Boundaryless]

/-- The velocity of `t ↦ exp (t • v)` at time `0` is `v`. -/
theorem hasMFDerivAt_exp_smul_zero (v : GroupLieAlgebra I G) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => exp (s • v)) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  rw [hasMFDerivAt_smulRight_iff_of_eq_one (by rw [zero_smul, exp_zero]) v]
  exact hasMFDerivAt_exp_smul v 0

/-- The one-parameter subgroup `t ↦ exp (t • v)` determines `v`, because `v` is its velocity at
time `0`. -/
theorem eq_of_exp_smul_eq {v w : GroupLieAlgebra I G}
    (h : ∀ t : ℝ, exp (t • v) = exp (t • w)) : v = w := by
  have h1 := hasMFDerivAt_exp_smul_zero v
  have hf : (fun s : ℝ => exp (s • v)) = fun s : ℝ => exp (s • w) := funext h
  rw [hf] at h1
  have hu := DFunLike.congr_fun (hasMFDerivAt_unique h1 (hasMFDerivAt_exp_smul_zero w)) (1 : ℝ)
  have h3 : (1 : ℝ) • v = (1 : ℝ) • w := hu
  simpa using h3

/-- Characterisation of one-parameter subgroups, in the form which does not identify tangent
spaces: a curve `φ : ℝ → G` with `φ (s + t) = φ s * φ t` whose velocity at time `0` is the value
at `φ 0` of the left-invariant vector field of `v` is `t ↦ exp (t • v)`. -/
theorem eq_exp_smul_of_map_add' {φ : ℝ → G} (hmul : ∀ s t, φ (s + t) = φ s * φ t)
    {v : GroupLieAlgebra I G}
    (hφ : HasMFDerivAt 𝓘(ℝ, ℝ) I φ 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (φ 0)))) (t : ℝ) :
    φ t = exp (t • v) := by
  rw [exp_smul, ← eq_oneParameter (isMIntegralCurve_of_map_add hmul hφ) (map_zero_of_map_add hmul)]

/-- **Characterisation of one-parameter subgroups.** A curve `φ : ℝ → G` with
`φ (s + t) = φ s * φ t` and velocity `v` at time `0` is `t ↦ exp (t • v)`.  Since `φ 0 = 1`, the
tangent space at `φ 0` is the Lie algebra. -/
theorem eq_exp_smul_of_map_add {φ : ℝ → G} (hmul : ∀ s t, φ (s + t) = φ s * φ t)
    {v : GroupLieAlgebra I G}
    (hφ : HasMFDerivAt 𝓘(ℝ, ℝ) I φ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v)) (t : ℝ) :
    φ t = exp (t • v) :=
  eq_exp_smul_of_map_add' hmul
    ((hasMFDerivAt_smulRight_iff_of_eq_one (map_zero_of_map_add hmul) v).mp hφ) t

/-- The one-parameter subgroup of `v` as a monoid homomorphism from `Multiplicative ℝ`. -/
def expHom (v : GroupLieAlgebra I G) : Multiplicative ℝ →* G where
  toFun t := exp (Multiplicative.toAdd t • v)
  map_one' := by simp
  map_mul' s t := by simp [exp_add_smul]

/-- The homomorphism `expHom v` is `t ↦ exp (t • v)`. -/
theorem expHom_apply (v : GroupLieAlgebra I G) (t : Multiplicative ℝ) :
    expHom v t = exp (Multiplicative.toAdd t • v) :=
  rfl

/-- The homomorphism `expHom v` evaluated at `Multiplicative.ofAdd t`. -/
@[simp]
theorem expHom_ofAdd (v : GroupLieAlgebra I G) (t : ℝ) :
    expHom v (Multiplicative.ofAdd t) = exp (t • v) :=
  rfl

end ExpCharacterisation

end LieGroupExponential
