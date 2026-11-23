import FriedrichsExtension.FriedrichsOperator
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Operator.Extend

open scoped InnerProductSpace

noncomputable section

namespace FriedrichsExtension
namespace SemiboundedSymmetricOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section FixedShift

variable (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift)

/--
The completed energy embedding retains the coercivity estimate from the original operator domain.
This is the completion-level form of
`(A.lowerBound + shift) ‖u‖² ≤ shiftedEnergy shift u`.
-/
theorem energyEmbedding_coercive (v : A.EnergySpace shift hshift) :
    (A.lowerBound + shift) * ‖A.energyEmbedding shift hshift v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  refine UniformSpace.Completion.denseRange_coe.induction_on v ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro u
    rw [A.energyEmbedding_coe shift hshift]
    rw [UniformSpace.Completion.norm_coe]
    rw [EnergyDomain.norm_sq_eq_shiftedEnergy]
    exact A.shiftedEnergy_lower shift u.toDomain

/--
The closed extension of the original unshifted quadratic form, written on the completed energy
space.  The shift only supplies the Hilbert norm used to complete the core; it is subtracted again
in the form itself.
-/
def friedrichsForm (v w : A.EnergySpace shift hshift) : ℝ :=
  inner ℝ v w - shift *
    inner ℝ (A.energyEmbedding shift hshift v) (A.energyEmbedding shift hshift w)

/-- On the original operator domain, the closed form is exactly the operator form. -/
theorem friedrichsForm_coe
    (u v : EnergyDomain A shift hshift) :
    A.friedrichsForm shift hshift
        (u : A.EnergySpace shift hshift) (v : A.EnergySpace shift hshift) =
      A.operatorForm u.toDomain v.toDomain := by
  unfold friedrichsForm
  rw [UniformSpace.Completion.inner_coe]
  rw [EnergyDomain.inner_eq_shiftedForm]
  rw [A.energyEmbedding_coe shift hshift, A.energyEmbedding_coe shift hshift]
  simp only [shiftedForm]
  ring

/-- The original energy core is dense in the completed form space. -/
theorem energyDomain_dense_in_energySpace :
    DenseRange ((↑) : EnergyDomain A shift hshift → A.EnergySpace shift hshift) :=
  UniformSpace.Completion.denseRange_coe

/--
Adding back the auxiliary shift to the closed form recovers exactly the Hilbert inner product on
the completed energy space.  Thus the shifted form norm is the complete energy-space norm.
-/
theorem friedrichsForm_add_shift
    (v w : A.EnergySpace shift hshift) :
    A.friedrichsForm shift hshift v w +
        shift * inner ℝ (A.energyEmbedding shift hshift v)
          (A.energyEmbedding shift hshift w) =
      inner ℝ v w := by
  unfold friedrichsForm
  ring

/-- Quadratic closed-form identity for the complete form norm. -/
theorem friedrichsForm_energy_norm_sq
    (v : A.EnergySpace shift hshift) :
    A.friedrichsForm shift hshift v v +
        shift * ‖A.energyEmbedding shift hshift v‖ ^ 2 =
      ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (A.energyEmbedding shift hshift v)]
  rw [A.friedrichsForm_add_shift shift hshift v v]
  rw [real_inner_self_eq_norm_sq]

/-- The closed Friedrichs form is jointly continuous on the completed energy space. -/
theorem friedrichsForm_continuous :
    Continuous (fun p : A.EnergySpace shift hshift × A.EnergySpace shift hshift =>
      A.friedrichsForm shift hshift p.1 p.2) := by
  unfold friedrichsForm
  fun_prop

/--
The Friedrichs form is the unique jointly continuous extension of the original operator form to the
energy completion.
-/
theorem friedrichsForm_unique_continuous_extension
    (q : A.EnergySpace shift hshift → A.EnergySpace shift hshift → ℝ)
    (hq : Continuous (fun p : A.EnergySpace shift hshift × A.EnergySpace shift hshift =>
      q p.1 p.2))
    (hcore : ∀ u v : EnergyDomain A shift hshift,
      q (u : A.EnergySpace shift hshift) (v : A.EnergySpace shift hshift) =
        A.operatorForm u.toDomain v.toDomain)
    (v w : A.EnergySpace shift hshift) :
    q v w = A.friedrichsForm shift hshift v w := by
  refine UniformSpace.Completion.denseRange_coe.induction_on₂ ?_ ?_ v w
  · exact isClosed_eq hq (A.friedrichsForm_continuous shift hshift)
  · intro u z
    exact (hcore u z).trans (A.friedrichsForm_coe shift hshift u z).symm

/-- The ambient form domain is the range of the completed energy embedding. -/
def friedrichsFormDomain : Submodule ℝ H :=
  LinearMap.range (A.energyEmbedding shift hshift).toLinearMap

/-- The completed energy space is algebraically equivalent to the ambient form domain. -/
def energySpaceEquivFormDomain :
    A.EnergySpace shift hshift ≃ₗ[ℝ] A.friedrichsFormDomain shift hshift :=
  LinearEquiv.ofInjective (A.energyEmbedding shift hshift).toLinearMap
    (A.energyEmbedding_injective shift hshift)

@[simp]
theorem coe_energySpaceEquivFormDomain_apply (v : A.EnergySpace shift hshift) :
    ((A.energySpaceEquivFormDomain shift hshift v : A.friedrichsFormDomain shift hshift) : H) =
      A.energyEmbedding shift hshift v := by
  exact LinearEquiv.ofInjective_apply
    (A.energyEmbedding shift hshift).toLinearMap v

/-- The ambient form domain is dense in `H`. -/
theorem friedrichsFormDomain_dense :
    Dense ((A.friedrichsFormDomain shift hshift : Submodule ℝ H) : Set H) := by
  simpa [friedrichsFormDomain] using A.energyEmbedding_range_dense shift hshift

/--
`y` represents the closed form at `x` when `x = Jv` for an energy vector `v` and
`q̄(v,w) = ⟪y,Jw⟫` for every energy vector `w`.
-/
def IsFriedrichsRepresenter (x y : H) : Prop :=
  ∃ v : A.EnergySpace shift hshift,
    A.energyEmbedding shift hshift v = x ∧
      ∀ w : A.EnergySpace shift hshift,
        A.friedrichsForm shift hshift v w =
          inner ℝ y (A.energyEmbedding shift hshift w)

/-- A form representer, if it exists, is unique. -/
theorem friedrichsRepresenter_unique {x y₁ y₂ : H}
    (hy₁ : A.IsFriedrichsRepresenter shift hshift x y₁)
    (hy₂ : A.IsFriedrichsRepresenter shift hshift x y₂) :
    y₁ = y₂ := by
  rcases hy₁ with ⟨v₁, hJ₁, hrep₁⟩
  rcases hy₂ with ⟨v₂, hJ₂, hrep₂⟩
  have hv : v₁ = v₂ :=
    A.energyEmbedding_injective shift hshift (hJ₁.trans hJ₂.symm)
  subst v₂
  apply (A.energyEmbedding_range_dense shift hshift).eq_of_inner_left ℝ
  intro z hz
  rcases hz with ⟨w, rfl⟩
  exact (hrep₁ w).symm.trans (hrep₂ w)

/--
Every vector in the Friedrichs-operator domain has a closed-form representative, namely the value
of the Friedrichs operator.
-/
theorem friedrichsExtension_isRepresenter
    (x : (A.friedrichsExtension shift hshift).domain) :
    A.IsFriedrichsRepresenter shift hshift (x : H)
      (A.friedrichsExtension shift hshift x) := by
  let T := A.shiftedFriedrichsOperator shift hshift
  have hxT : (x : H) ∈ T.domain := by
    simpa [T, friedrichsExtension] using x.prop
  let xT : T.domain := ⟨(x : H), hxT⟩
  rcases A.shiftedFriedrichsOperator_exists_preimage shift hshift xT with
    ⟨z, hRz, hTx⟩
  let v : A.EnergySpace shift hshift :=
    (A.energyEmbedding shift hshift).adjoint z
  refine ⟨v, ?_, ?_⟩
  · simpa [v, friedrichsResolvent] using hRz
  · intro w
    have hAdj :
        inner ℝ v w = inner ℝ z (A.energyEmbedding shift hshift w) := by
      simpa [v] using
        (ContinuousLinearMap.adjoint_inner_left
          (A.energyEmbedding shift hshift) w z)
    have hJv : A.energyEmbedding shift hshift v = (x : H) := by
      simpa [v, friedrichsResolvent] using hRz
    have hxTx : A.shiftedFriedrichsOperator shift hshift x = z := by
      simpa [T, xT] using hTx
    have hF :
        A.friedrichsExtension shift hshift x =
          z - shift • (x : H) := by
      rw [A.friedrichsExtension_apply shift hshift x, hxTx]
    unfold friedrichsForm
    rw [hAdj, hJv, hF]
    rw [inner_sub_left, real_inner_smul_left]

/--
Conversely, existence of a closed-form representer forces membership in the Friedrichs-operator
domain.
-/
theorem mem_friedrichsExtension_domain_of_representer {x y : H}
    (hrep : A.IsFriedrichsRepresenter shift hshift x y) :
    x ∈ (A.friedrichsExtension shift hshift).domain := by
  rcases hrep with ⟨v, hJv, hform⟩
  let z : H := y + shift • x
  have hvAdj : v = (A.energyEmbedding shift hshift).adjoint z := by
    apply ext_inner_right ℝ
    intro w
    have hAdj := ContinuousLinearMap.adjoint_inner_left
      (A.energyEmbedding shift hshift) w z
    rw [hAdj]
    dsimp [z]
    rw [inner_add_left, real_inner_smul_left]
    rw [← hform w, friedrichsForm, hJv]
    ring
  have hRx : A.friedrichsResolvent shift hshift z = x := by
    change A.energyEmbedding shift hshift
      ((A.energyEmbedding shift hshift).adjoint z) = x
    rw [← hvAdj, hJv]
  rw [A.friedrichsExtension_domain shift hshift]
  rw [A.shiftedFriedrichsOperator_domain shift hshift]
  exact ⟨z, hRx⟩

/-- The closed-form representation characterises the operator domain exactly. -/
theorem mem_friedrichsExtension_domain_iff_exists_representer (x : H) :
    x ∈ (A.friedrichsExtension shift hshift).domain ↔
      ∃ y : H, A.IsFriedrichsRepresenter shift hshift x y := by
  constructor
  · intro hx
    let xx : (A.friedrichsExtension shift hshift).domain := ⟨x, hx⟩
    exact ⟨A.friedrichsExtension shift hshift xx,
      A.friedrichsExtension_isRepresenter shift hshift xx⟩
  · rintro ⟨y, hy⟩
    exact A.mem_friedrichsExtension_domain_of_representer shift hshift hy

/-- The operator domain is contained in the ambient closed-form domain. -/
theorem friedrichsExtension_domain_le_formDomain :
    (A.friedrichsExtension shift hshift).domain ≤
      A.friedrichsFormDomain shift hshift := by
  intro x hx
  let xx : (A.friedrichsExtension shift hshift).domain := ⟨x, hx⟩
  rcases A.friedrichsExtension_isRepresenter shift hshift xx with
    ⟨v, hJv, _⟩
  exact ⟨v, hJv⟩

/-- The operator value is the unique representing vector of the closed form. -/
theorem friedrichsExtension_eq_representer
    (x : (A.friedrichsExtension shift hshift).domain) {y : H}
    (hy : A.IsFriedrichsRepresenter shift hshift (x : H) y) :
    A.friedrichsExtension shift hshift x = y := by
  exact A.friedrichsRepresenter_unique shift hshift
    (A.friedrichsExtension_isRepresenter shift hshift x) hy

/--
Intrinsic uniqueness: any partial operator having exactly the representable form domain and whose
values represent the closed form is the Friedrichs extension.
-/
theorem friedrichsExtension_unique
    (B : H →ₗ.[ℝ] H)
    (hdom : ∀ x : H, x ∈ B.domain ↔
      ∃ y : H, A.IsFriedrichsRepresenter shift hshift x y)
    (hrep : ∀ x : B.domain,
      A.IsFriedrichsRepresenter shift hshift (x : H) (B x)) :
    B = A.friedrichsExtension shift hshift := by
  apply LinearPMap.ext
  · ext x
    rw [hdom, A.mem_friedrichsExtension_domain_iff_exists_representer shift hshift]
  · intro x hxB hxF
    let xB : B.domain := ⟨x, hxB⟩
    let xF : (A.friedrichsExtension shift hshift).domain := ⟨x, hxF⟩
    exact A.friedrichsRepresenter_unique shift hshift
      (hrep xB) (A.friedrichsExtension_isRepresenter shift hshift xF)

/-- The closed form itself satisfies the sharp inherited lower bound. -/
theorem friedrichsForm_lower
    (v : A.EnergySpace shift hshift) :
    A.lowerBound * ‖A.energyEmbedding shift hshift v‖ ^ 2 ≤
      A.friedrichsForm shift hshift v v := by
  have hcoercive := A.energyEmbedding_coercive shift hshift v
  unfold friedrichsForm
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  linarith

/-- The Friedrichs extension retains the original sharp lower bound. -/
theorem friedrichsExtension_lower_bound
    (x : (A.friedrichsExtension shift hshift).domain) :
    A.lowerBound * ‖(x : H)‖ ^ 2 ≤
      inner ℝ (A.friedrichsExtension shift hshift x) (x : H) := by
  rcases A.friedrichsExtension_isRepresenter shift hshift x with
    ⟨v, hJv, hrep⟩
  have hform := A.friedrichsForm_lower shift hshift v
  rw [hJv] at hform
  rw [hrep v, hJv] at hform
  exact hform

end FixedShift

section ChangeShift

variable (A : SemiboundedSymmetricOperator H)
variable (shift₁ shift₂ : ℝ)
variable (hshift₁ : 0 < A.lowerBound + shift₁)
variable (hshift₂ : 0 < A.lowerBound + shift₂)

/-- Changing the auxiliary shift only adds the corresponding ambient inner-product term. -/
theorem shiftedForm_change (u v : A.op.domain) :
    A.shiftedForm shift₂ u v =
      A.shiftedForm shift₁ u v +
        (shift₂ - shift₁) * inner ℝ (u : H) (v : H) := by
  simp only [shiftedForm]
  ring

/-- Quadratic version of `shiftedForm_change`. -/
theorem shiftedEnergy_change (u : A.op.domain) :
    A.shiftedEnergy shift₂ u =
      A.shiftedEnergy shift₁ u +
        (shift₂ - shift₁) * ‖(u : H)‖ ^ 2 := by
  rw [shiftedEnergy, shiftedEnergy, A.shiftedForm_change shift₁ shift₂ u u,
    real_inner_self_eq_norm_sq]

/-- The identity on the original operator domain, regarded between the two energy-domain copies. -/
def energyDomainChangeEquiv :
    EnergyDomain A shift₁ hshift₁ ≃ₗ[ℝ] EnergyDomain A shift₂ hshift₂ :=
  (EnergyDomain.linearEquiv A shift₁ hshift₁).trans
    (EnergyDomain.linearEquiv A shift₂ hshift₂).symm

@[simp]
theorem energyDomainChangeEquiv_toDomain
    (u : EnergyDomain A shift₁ hshift₁) :
    (A.energyDomainChangeEquiv shift₁ shift₂ hshift₁ hshift₂ u).toDomain = u.toDomain := rfl

/-- A convenient comparison constant for the two energy norms. -/
def energyNormChangeConstant : ℝ :=
  Real.sqrt (1 + |shift₂ - shift₁| / (A.lowerBound + shift₁))

/-- The two core energy norms are equivalent. -/
theorem energyDomainChangeEquiv_norm_le
    (u : EnergyDomain A shift₁ hshift₁) :
    ‖A.energyDomainChangeEquiv shift₁ shift₂ hshift₁ hshift₂ u‖ ≤
      A.energyNormChangeConstant shift₁ shift₂ * ‖u‖ := by
  let c : ℝ := A.lowerBound + shift₁
  let d : ℝ := shift₂ - shift₁
  let C : ℝ := 1 + |d| / c
  have hc : 0 < c := hshift₁
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg zero_le_one (div_nonneg (abs_nonneg _) hc.le)
  have huAmbient : ‖(u.toDomain : H)‖ ^ 2 ≤ A.shiftedEnergy shift₁ u.toDomain / c := by
    rw [le_div_iff₀ hc]
    simpa [c, mul_comm] using A.shiftedEnergy_lower shift₁ u.toDomain
  have henergy : A.shiftedEnergy shift₂ u.toDomain ≤ C * A.shiftedEnergy shift₁ u.toDomain := by
    rw [A.shiftedEnergy_change shift₁ shift₂ u.toDomain]
    calc
      A.shiftedEnergy shift₁ u.toDomain + d * ‖(u.toDomain : H)‖ ^ 2 ≤
          A.shiftedEnergy shift₁ u.toDomain + |d| * ‖(u.toDomain : H)‖ ^ 2 := by
            gcongr
            exact le_abs_self d
      _ ≤ A.shiftedEnergy shift₁ u.toDomain +
          |d| * (A.shiftedEnergy shift₁ u.toDomain / c) := by
            gcongr
      _ = C * A.shiftedEnergy shift₁ u.toDomain := by
            dsimp [C]
            rw [div_eq_mul_inv]
            ring
  have hsq :
      ‖A.energyDomainChangeEquiv shift₁ shift₂ hshift₁ hshift₂ u‖ ^ 2 ≤
        (Real.sqrt C * ‖u‖) ^ 2 := by
    rw [EnergyDomain.norm_sq_eq_shiftedEnergy]
    rw [mul_pow, Real.sq_sqrt hC, EnergyDomain.norm_sq_eq_shiftedEnergy]
    simpa [energyDomainChangeEquiv, c, d] using henergy
  have hnonneg : 0 ≤ Real.sqrt C * ‖u‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hlin := (sq_le_sq₀ (norm_nonneg _) hnonneg).mp hsq
  simpa [energyNormChangeConstant, C, c, d] using hlin

/-- The canonical core embedding into the corresponding energy completion. -/
def energyCoreEmbedding (shift : ℝ) (hshift : 0 < A.lowerBound + shift) :
    EnergyDomain A shift hshift →ₗ[ℝ] A.EnergySpace shift hshift :=
  (UniformSpace.Completion.toComplL :
    EnergyDomain A shift hshift →L[ℝ] A.EnergySpace shift hshift).toLinearMap

@[simp]
theorem energyCoreEmbedding_apply
    (shift : ℝ) (hshift : 0 < A.lowerBound + shift)
    (u : EnergyDomain A shift hshift) :
    A.energyCoreEmbedding shift hshift u =
      (u : A.EnergySpace shift hshift) := rfl

/-- The core embedding has dense range. -/
theorem energyCoreEmbedding_dense
    (shift : ℝ) (hshift : 0 < A.lowerBound + shift) :
    DenseRange (A.energyCoreEmbedding shift hshift) := by
  simpa [energyCoreEmbedding] using
    (UniformSpace.Completion.denseRange_coe :
      DenseRange ((↑) : EnergyDomain A shift hshift → A.EnergySpace shift hshift))

/-- The inverse core change is definitionally the change in the opposite direction. -/
theorem energyDomainChangeEquiv_symm_apply
    (u : EnergyDomain A shift₂ hshift₂) :
    (A.energyDomainChangeEquiv shift₁ shift₂ hshift₁ hshift₂).symm u =
      A.energyDomainChangeEquiv shift₂ shift₁ hshift₂ hshift₁ u := by
  apply EnergyDomain.ext
  rfl

/-- Forward norm-control data used to extend the identity to the completions. -/
theorem energyDomainChange_norm_exists :
    ∃ C : ℝ, ∀ u : EnergyDomain A shift₁ hshift₁,
      ‖A.energyCoreEmbedding shift₂ hshift₂
          (A.energyDomainChangeEquiv shift₁ shift₂ hshift₁ hshift₂ u)‖ ≤
        C * ‖A.energyCoreEmbedding shift₁ hshift₁ u‖ := by
  refine ⟨A.energyNormChangeConstant shift₁ shift₂, ?_⟩
  intro u
  simpa [energyCoreEmbedding, UniformSpace.Completion.norm_coe] using
    A.energyDomainChangeEquiv_norm_le shift₁ shift₂ hshift₁ hshift₂ u

/-- Reverse norm-control data used to extend the identity to the completions. -/
theorem energyDomainChange_symm_norm_exists :
    ∃ C : ℝ, ∀ u : EnergyDomain A shift₂ hshift₂,
      ‖A.energyCoreEmbedding shift₁ hshift₁
          ((A.energyDomainChangeEquiv shift₁ shift₂ hshift₁ hshift₂).symm u)‖ ≤
        C * ‖A.energyCoreEmbedding shift₂ hshift₂ u‖ := by
  refine ⟨A.energyNormChangeConstant shift₂ shift₁, ?_⟩
  intro u
  rw [A.energyDomainChangeEquiv_symm_apply shift₁ shift₂ hshift₁ hshift₂ u]
  simpa [energyCoreEmbedding, UniformSpace.Completion.norm_coe] using
    A.energyDomainChangeEquiv_norm_le shift₂ shift₁ hshift₂ hshift₁ u

/--
The identity on the core extends to a continuous linear equivalence between the two completed
energy spaces.
-/
def energySpaceChangeEquiv :
    A.EnergySpace shift₁ hshift₁ ≃L[ℝ] A.EnergySpace shift₂ hshift₂ :=
  (A.energyDomainChangeEquiv shift₁ shift₂ hshift₁ hshift₂).extend
    (A.energyCoreEmbedding shift₁ hshift₁)
    (A.energyCoreEmbedding shift₂ hshift₂)
    (A.energyCoreEmbedding_dense shift₁ hshift₁)
    (A.energyDomainChange_norm_exists shift₁ shift₂ hshift₁ hshift₂)
    (A.energyCoreEmbedding_dense shift₂ hshift₂)
    (A.energyDomainChange_symm_norm_exists shift₁ shift₂ hshift₁ hshift₂)

@[simp]
theorem energySpaceChangeEquiv_coe
    (u : EnergyDomain A shift₁ hshift₁) :
    A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂
      (u : A.EnergySpace shift₁ hshift₁) =
      ((⟨u.toDomain⟩ : EnergyDomain A shift₂ hshift₂) : A.EnergySpace shift₂ hshift₂) := by
  have h := LinearEquiv.extend_eq
    (A.energyDomainChangeEquiv shift₁ shift₂ hshift₁ hshift₂)
    (A.energyCoreEmbedding shift₁ hshift₁)
    (A.energyCoreEmbedding shift₂ hshift₂)
    (A.energyCoreEmbedding_dense shift₁ hshift₁)
    (A.energyDomainChange_norm_exists shift₁ shift₂ hshift₁ hshift₂)
    (A.energyCoreEmbedding_dense shift₂ hshift₂)
    (A.energyDomainChange_symm_norm_exists shift₁ shift₂ hshift₁ hshift₂) u
  simpa [energySpaceChangeEquiv, energyCoreEmbedding, energyDomainChangeEquiv] using h

/-- The canonical change-of-shift equivalence intertwines the ambient embeddings. -/
theorem energyEmbedding_change
    (v : A.EnergySpace shift₁ hshift₁) :
    A.energyEmbedding shift₂ hshift₂
        (A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂ v) =
      A.energyEmbedding shift₁ hshift₁ v := by
  refine UniformSpace.Completion.denseRange_coe.induction_on v ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro u
    rw [A.energySpaceChangeEquiv_coe shift₁ shift₂ hshift₁ hshift₂ u]
    rw [A.energyEmbedding_coe shift₂ hshift₂]
    rw [A.energyEmbedding_coe shift₁ hshift₁]

/-- The energy inner products transform by exactly the ambient shift correction. -/
theorem energyInner_change
    (v w : A.EnergySpace shift₁ hshift₁) :
    inner ℝ
        (A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂ v)
        (A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂ w) =
      inner ℝ v w + (shift₂ - shift₁) *
        inner ℝ (A.energyEmbedding shift₁ hshift₁ v)
          (A.energyEmbedding shift₁ hshift₁ w) := by
  refine UniformSpace.Completion.denseRange_coe.induction_on₂ ?_ ?_ v w
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro u z
    rw [A.energySpaceChangeEquiv_coe shift₁ shift₂ hshift₁ hshift₂ u]
    rw [A.energySpaceChangeEquiv_coe shift₁ shift₂ hshift₁ hshift₂ z]
    rw [UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
      EnergyDomain.inner_eq_shiftedForm, EnergyDomain.inner_eq_shiftedForm]
    rw [A.energyEmbedding_coe shift₁ hshift₁, A.energyEmbedding_coe shift₁ hshift₁]
    exact A.shiftedForm_change shift₁ shift₂ u.toDomain z.toDomain

/-- The closed unshifted form is independent of the auxiliary shift under the canonical equivalence. -/
theorem friedrichsForm_change
    (v w : A.EnergySpace shift₁ hshift₁) :
    A.friedrichsForm shift₂ hshift₂
        (A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂ v)
        (A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂ w) =
      A.friedrichsForm shift₁ hshift₁ v w := by
  unfold friedrichsForm
  rw [A.energyInner_change shift₁ shift₂ hshift₁ hshift₂ v w]
  rw [A.energyEmbedding_change shift₁ shift₂ hshift₁ hshift₂ v]
  rw [A.energyEmbedding_change shift₁ shift₂ hshift₁ hshift₂ w]
  ring

/-- Form representability is independent of the admissible auxiliary shift. -/
theorem isFriedrichsRepresenter_change {x y : H}
    (hrep : A.IsFriedrichsRepresenter shift₁ hshift₁ x y) :
    A.IsFriedrichsRepresenter shift₂ hshift₂ x y := by
  rcases hrep with ⟨v, hJv, hform⟩
  let E := A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂
  refine ⟨E v, ?_, ?_⟩
  · have hE := A.energyEmbedding_change shift₁ shift₂ hshift₁ hshift₂ v
    have hE' :
        A.energyEmbedding shift₂ hshift₂ (E v) =
          A.energyEmbedding shift₁ hshift₁ v := by
      simpa [E] using hE
    exact hE'.trans hJv
  · intro w₂
    let w₁ : A.EnergySpace shift₁ hshift₁ := E.symm w₂
    have hw : E w₁ = w₂ := E.apply_symm_apply w₂
    calc
      A.friedrichsForm shift₂ hshift₂ (E v) w₂ =
          A.friedrichsForm shift₂ hshift₂ (E v) (E w₁) := by rw [hw]
      _ = A.friedrichsForm shift₁ hshift₁ v w₁ := by
        simpa [E] using A.friedrichsForm_change shift₁ shift₂ hshift₁ hshift₂ v w₁
      _ = inner ℝ y (A.energyEmbedding shift₁ hshift₁ w₁) := hform w₁
      _ = inner ℝ y (A.energyEmbedding shift₂ hshift₂ (E w₁)) := by
        rw [A.energyEmbedding_change shift₁ shift₂ hshift₁ hshift₂ w₁]
      _ = inner ℝ y (A.energyEmbedding shift₂ hshift₂ w₂) := by rw [hw]

/-- Form representability is equivalent for any two admissible shifts. -/
theorem isFriedrichsRepresenter_iff_change {x y : H} :
    A.IsFriedrichsRepresenter shift₁ hshift₁ x y ↔
      A.IsFriedrichsRepresenter shift₂ hshift₂ x y := by
  constructor
  · exact A.isFriedrichsRepresenter_change shift₁ shift₂ hshift₁ hshift₂
  · exact A.isFriedrichsRepresenter_change shift₂ shift₁ hshift₂ hshift₁

/-- The ambient closed-form domain is independent of the admissible auxiliary shift. -/
theorem friedrichsFormDomain_eq :
    A.friedrichsFormDomain shift₁ hshift₁ = A.friedrichsFormDomain shift₂ hshift₂ := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂ v, ?_⟩
    calc
      A.energyEmbedding shift₂ hshift₂
          (A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂ v) =
          A.energyEmbedding shift₁ hshift₁ v :=
        A.energyEmbedding_change shift₁ shift₂ hshift₁ hshift₂ v
      _ = x := hv
  · rintro ⟨v, hv⟩
    let E := A.energySpaceChangeEquiv shift₁ shift₂ hshift₁ hshift₂
    refine ⟨E.symm v, ?_⟩
    have h := A.energyEmbedding_change shift₁ shift₂ hshift₁ hshift₂ (E.symm v)
    rw [E.apply_symm_apply] at h
    exact h.symm.trans hv

/-- The Friedrichs extension is independent of the admissible auxiliary shift. -/
theorem friedrichsExtension_independent_of_shift :
    A.friedrichsExtension shift₁ hshift₁ = A.friedrichsExtension shift₂ hshift₂ := by
  apply A.friedrichsExtension_unique shift₂ hshift₂
    (B := A.friedrichsExtension shift₁ hshift₁)
  · intro x
    rw [A.mem_friedrichsExtension_domain_iff_exists_representer shift₁ hshift₁]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, A.isFriedrichsRepresenter_change shift₁ shift₂ hshift₁ hshift₂ hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, A.isFriedrichsRepresenter_change shift₂ shift₁ hshift₂ hshift₁ hy⟩
  · intro x
    exact A.isFriedrichsRepresenter_change shift₁ shift₂ hshift₁ hshift₂
      (A.friedrichsExtension_isRepresenter shift₁ hshift₁ x)

end ChangeShift

section Canonical

variable (A : SemiboundedSymmetricOperator H)

/-- A canonical admissible shift; the shifted coercivity constant is exactly `1`. -/
def canonicalFriedrichsShift : ℝ := 1 - A.lowerBound

/-- The canonical shift is admissible. -/
theorem canonicalFriedrichsShift_admissible :
    0 < A.lowerBound + A.canonicalFriedrichsShift := by
  dsimp [canonicalFriedrichsShift]
  linarith

/-- The Friedrichs extension with the auxiliary shift removed from the public definition. -/
@[reducible]
def canonicalFriedrichsExtension : H →ₗ.[ℝ] H :=
  A.friedrichsExtension A.canonicalFriedrichsShift
    A.canonicalFriedrichsShift_admissible

/-- Shift-free name for representability by the canonical closed Friedrichs form. -/
def IsCanonicalFriedrichsRepresenter (x y : H) : Prop :=
  A.IsFriedrichsRepresenter A.canonicalFriedrichsShift
    A.canonicalFriedrichsShift_admissible x y

/-- The shift-free representability predicate agrees with the predicate from every admissible shift. -/
theorem isCanonicalFriedrichsRepresenter_iff
    (shift : ℝ) (hshift : 0 < A.lowerBound + shift) {x y : H} :
    A.IsCanonicalFriedrichsRepresenter x y ↔
      A.IsFriedrichsRepresenter shift hshift x y := by
  unfold IsCanonicalFriedrichsRepresenter
  exact A.isFriedrichsRepresenter_iff_change
    A.canonicalFriedrichsShift shift
    A.canonicalFriedrichsShift_admissible hshift

/-- Every admissible shifted construction is the canonical Friedrichs extension. -/
theorem friedrichsExtension_eq_canonical
    (shift : ℝ) (hshift : 0 < A.lowerBound + shift) :
    A.friedrichsExtension shift hshift = A.canonicalFriedrichsExtension := by
  unfold canonicalFriedrichsExtension
  exact A.friedrichsExtension_independent_of_shift
    shift A.canonicalFriedrichsShift hshift A.canonicalFriedrichsShift_admissible

/-- The canonical Friedrichs extension is self-adjoint. -/
theorem canonicalFriedrichsExtension_isSelfAdjoint :
    IsSelfAdjoint A.canonicalFriedrichsExtension := by
  unfold canonicalFriedrichsExtension
  exact A.friedrichsExtension_isSelfAdjoint
    A.canonicalFriedrichsShift A.canonicalFriedrichsShift_admissible

/-- The canonical Friedrichs extension extends the original operator. -/
theorem op_le_canonicalFriedrichsExtension :
    A.op ≤ A.canonicalFriedrichsExtension := by
  unfold canonicalFriedrichsExtension
  exact A.op_le_friedrichsExtension
    A.canonicalFriedrichsShift A.canonicalFriedrichsShift_admissible

/-- The canonical Friedrichs extension retains the sharp lower bound. -/
theorem canonicalFriedrichsExtension_lower_bound
    (x : A.canonicalFriedrichsExtension.domain) :
    A.lowerBound * ‖(x : H)‖ ^ 2 ≤
      inner ℝ (A.canonicalFriedrichsExtension x) (x : H) := by
  unfold canonicalFriedrichsExtension at x ⊢
  exact A.friedrichsExtension_lower_bound
    A.canonicalFriedrichsShift A.canonicalFriedrichsShift_admissible x

/-- Intrinsic domain characterisation of the canonical Friedrichs extension. -/
theorem mem_canonicalFriedrichsExtension_domain_iff (x : H) :
    x ∈ A.canonicalFriedrichsExtension.domain ↔
      ∃ y : H, A.IsCanonicalFriedrichsRepresenter x y := by
  unfold canonicalFriedrichsExtension IsCanonicalFriedrichsRepresenter
  exact A.mem_friedrichsExtension_domain_iff_exists_representer
    A.canonicalFriedrichsShift A.canonicalFriedrichsShift_admissible x

/-- The canonical Friedrichs extension value is the canonical closed-form representer. -/
theorem canonicalFriedrichsExtension_isRepresenter
    (x : A.canonicalFriedrichsExtension.domain) :
    A.IsCanonicalFriedrichsRepresenter (x : H)
      (A.canonicalFriedrichsExtension x) := by
  change A.IsFriedrichsRepresenter A.canonicalFriedrichsShift
    A.canonicalFriedrichsShift_admissible (x : H)
      (A.friedrichsExtension A.canonicalFriedrichsShift
        A.canonicalFriedrichsShift_admissible x)
  exact A.friedrichsExtension_isRepresenter
    A.canonicalFriedrichsShift A.canonicalFriedrichsShift_admissible x

/--
Shift-free intrinsic uniqueness/maximality: an operator is the Friedrichs extension precisely when
its domain consists of all vectors admitting a closed-form representer and its values are those
representers.
-/
theorem canonicalFriedrichsExtension_unique
    (B : H →ₗ.[ℝ] H)
    (hdom : ∀ x : H, x ∈ B.domain ↔
      ∃ y : H, A.IsCanonicalFriedrichsRepresenter x y)
    (hrep : ∀ x : B.domain,
      A.IsCanonicalFriedrichsRepresenter (x : H) (B x)) :
    B = A.canonicalFriedrichsExtension := by
  unfold canonicalFriedrichsExtension
  apply A.friedrichsExtension_unique
    A.canonicalFriedrichsShift A.canonicalFriedrichsShift_admissible (B := B)
  · intro x
    simpa [IsCanonicalFriedrichsRepresenter] using hdom x
  · intro x
    simpa [IsCanonicalFriedrichsRepresenter] using hrep x

end Canonical

/--
The full Friedrichs extension theorem for a densely defined semibounded symmetric operator on a real
Hilbert space.

For every admissible shift the construction gives the same self-adjoint extension; it extends the
original operator, retains the sharp lower bound, and is intrinsically characterised as the unique
maximal operator represented by the closure of the original quadratic form.
-/
theorem friedrichsExtension_theorem
    (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift) :
    IsSelfAdjoint (A.friedrichsExtension shift hshift) ∧
    A.op ≤ A.friedrichsExtension shift hshift ∧
    (∀ x : (A.friedrichsExtension shift hshift).domain,
      A.lowerBound * ‖(x : H)‖ ^ 2 ≤
        inner ℝ (A.friedrichsExtension shift hshift x) (x : H)) ∧
    (∀ x : H,
      x ∈ (A.friedrichsExtension shift hshift).domain ↔
        ∃ y : H, A.IsFriedrichsRepresenter shift hshift x y) := by
  exact ⟨A.friedrichsExtension_isSelfAdjoint shift hshift,
    A.op_le_friedrichsExtension shift hshift,
    A.friedrichsExtension_lower_bound shift hshift,
    A.mem_friedrichsExtension_domain_iff_exists_representer shift hshift⟩

/-- Shift-free packaged form of the full Friedrichs extension theorem. -/
theorem canonicalFriedrichsExtension_theorem
    (A : SemiboundedSymmetricOperator H) :
    IsSelfAdjoint A.canonicalFriedrichsExtension ∧
    A.op ≤ A.canonicalFriedrichsExtension ∧
    (∀ x : A.canonicalFriedrichsExtension.domain,
      A.lowerBound * ‖(x : H)‖ ^ 2 ≤
        inner ℝ (A.canonicalFriedrichsExtension x) (x : H)) ∧
    (∀ x : H,
      x ∈ A.canonicalFriedrichsExtension.domain ↔
        ∃ y : H, A.IsCanonicalFriedrichsRepresenter x y) := by
  exact ⟨A.canonicalFriedrichsExtension_isSelfAdjoint,
    A.op_le_canonicalFriedrichsExtension,
    A.canonicalFriedrichsExtension_lower_bound,
    A.mem_canonicalFriedrichsExtension_domain_iff⟩

end SemiboundedSymmetricOperator
end FriedrichsExtension
