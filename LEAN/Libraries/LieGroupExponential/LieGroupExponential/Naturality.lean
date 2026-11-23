import Mathlib
import LieGroupExponential.OneParameter

/-!
# Naturality of the exponential map and the adjoint action

Let `G` and `G'` be real Lie groups of class `C^∞`, with exponential maps `exp` as constructed in
`LieGroupExponential.OneParameter`.

## Naturality

Let `φ : G →* G'` be a group homomorphism which is differentiable at the identity, with derivative
`L` there.  Then `φ (exp v) = exp (L v)` for every `v` in the Lie algebra of `G`
(`map_exp_of_hasMFDerivAt`, and `map_exp_smul_of_hasMFDerivAt` for the whole one-parameter
subgroup).  Indeed `t ↦ φ (exp (t • v))` is a homomorphism from the additive group of the reals,
and by the chain rule its velocity at time `0` is `L v`; the characterisation of one-parameter
subgroups by their velocity at time `0` identifies it with `t ↦ exp (t • L v)`.  No regularity of
`φ` away from the identity is assumed.  (In the classical theory such a homomorphism is
automatically smooth; this is neither proved nor used here.)  The versions `map_exp` and
`map_exp_smul` take `L = mfderiv I I' φ 1` and assume only `MDifferentiableAt I I' φ 1`.

## The adjoint action

For `g : G`, `Ad I g` is the derivative at the identity of the conjugation `h ↦ g * h * g⁻¹`, a
continuous linear endomorphism of the Lie algebra (`hasMFDerivAt_conj`).  The chain rule gives
`Ad I 1 = id` and `Ad I (g * h) = Ad I g ∘ Ad I h`, so every `Ad I g` is invertible with inverse
`Ad I g⁻¹`; this is packaged as the continuous linear equivalence `AdEquiv I g` and as the
homomorphism `AdHom I G` from `G` to the group of continuous linear automorphisms of the Lie
algebra.  The adjoint action is natural: a homomorphism `φ` with derivative `L` at the identity
satisfies `L ∘ Ad I g = Ad I' (φ g) ∘ L` (`comp_Ad_of_hasMFDerivAt`).  Naturality of the
exponential map, applied to conjugation by `g`, gives

`g * exp v * g⁻¹ = exp (Ad I g v)`  (`conj_exp`, and `conj_exp_smul` for `exp (t • v)`).

Consequently `g` commutes with the whole one-parameter subgroup of `v` if and only if
`Ad I g v = v` (`Ad_apply_eq_self_iff`).  If `g` is central, in particular if `G` is commutative,
then `Ad I g = id`.

## The exponential of a sum of commuting elements

The derivative of the multiplication `G × G → G` at `(1, 1)` is `(u, w) ↦ u + w`
(`hasMFDerivAt_mul_one_one`).  Hence, if the one-parameter subgroups of `v` and `w` commute
elementwise, then `t ↦ exp (t • v) * exp (t • w)` is a one-parameter subgroup with velocity
`v + w` at time `0`, and `exp (v + w) = exp v * exp w` (`exp_add_of_commute`).  In a commutative
Lie group this holds for all `v` and `w` (`exp_add`).

## Tangent spaces at equal points

As in `LieGroupExponential.OneParameter`, a derivative at the identity of a map `f` with `f 1 = 1`
is regarded as a map into the Lie algebra of the target.  The tangent spaces at `f 1` and at `1`
are definitionally the same model space, and this identification is the one along the equality
`f 1 = 1`.  The primary statements carry a `HasMFDerivAt` hypothesis or conclusion, so that the
linear map in question is a true derivative.
-/

noncomputable section

open scoped Manifold ContDiff

namespace LieGroupExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

/-! ### Naturality -/

section Naturality

variable [CompleteSpace E] [I.Boundaryless] [CompleteSpace E'] [I'.Boundaryless]

/-- **Naturality of the exponential map**, for the whole one-parameter subgroup.  A group
homomorphism `φ` which is differentiable at the identity with derivative `L` maps the
one-parameter subgroup of `v` to the one-parameter subgroup of `L v`. -/
theorem map_exp_smul_of_hasMFDerivAt (φ : G →* G')
    {L : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I' G'} (hL : HasMFDerivAt I I' φ 1 L)
    (v : GroupLieAlgebra I G) (t : ℝ) : φ (exp (t • v)) = exp (t • L v) := by
  have hmul : ∀ s t : ℝ, φ (exp ((s + t) • v)) = φ (exp (s • v)) * φ (exp (t • v)) := by
    intro s t
    rw [exp_add_smul, map_mul]
  have h0 : exp ((0 : ℝ) • v) = 1 := by rw [zero_smul, exp_zero]
  have hL' : HasMFDerivAt I I' φ (exp ((0 : ℝ) • v)) L := by
    rw [h0]
    exact hL
  have hc := HasMFDerivAt.comp (0 : ℝ) hL' (hasMFDerivAt_exp_smul_zero v)
  have hφ : HasMFDerivAt 𝓘(ℝ, ℝ) I' (fun s : ℝ => φ (exp (s • v))) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (L v)) :=
    hc.congr_mfderiv (ContinuousLinearMap.ext fun x => L.map_smul x v)
  exact eq_exp_smul_of_map_add hmul hφ t

/-- **Naturality of the exponential map.** If the group homomorphism `φ` is differentiable at the
identity with derivative `L`, then `φ (exp v) = exp (L v)`. -/
theorem map_exp_of_hasMFDerivAt (φ : G →* G')
    {L : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I' G'} (hL : HasMFDerivAt I I' φ 1 L)
    (v : GroupLieAlgebra I G) : φ (exp v) = exp (L v) := by
  have h := map_exp_smul_of_hasMFDerivAt φ hL v 1
  rwa [one_smul, one_smul] at h

/-- Naturality of the exponential map for the whole one-parameter subgroup, with the derivative
written as `mfderiv`.  Since `φ 1 = 1`, the vector `mfderiv I I' φ 1 v` lies in the Lie algebra of
`G'`. -/
theorem map_exp_smul (φ : G →* G') (hφ : MDifferentiableAt I I' φ 1) (v : GroupLieAlgebra I G)
    (t : ℝ) :
    φ (exp (t • v)) = exp (I := I') (t • (mfderiv I I' φ 1 v : GroupLieAlgebra I' G')) := -- totalisation-audit: allow `φ` is differentiable at `1` by the hypothesis `hφ`, so this is its true derivative
  map_exp_smul_of_hasMFDerivAt φ (L := mfderiv I I' φ 1) hφ.hasMFDerivAt v t -- totalisation-audit: allow `φ` is differentiable at `1` by the hypothesis `hφ`, so this is its true derivative

/-- Naturality of the exponential map, with the derivative written as `mfderiv`: a group
homomorphism `φ` which is differentiable at the identity satisfies
`φ (exp v) = exp (mfderiv I I' φ 1 v)`.  Since `φ 1 = 1`, the vector `mfderiv I I' φ 1 v` lies in
the Lie algebra of `G'`. -/
theorem map_exp (φ : G →* G') (hφ : MDifferentiableAt I I' φ 1) (v : GroupLieAlgebra I G) :
    φ (exp v) = exp (I := I') (mfderiv I I' φ 1 v : GroupLieAlgebra I' G') := -- totalisation-audit: allow `φ` is differentiable at `1` by the hypothesis `hφ`, so this is its true derivative
  map_exp_of_hasMFDerivAt φ (L := mfderiv I I' φ 1) hφ.hasMFDerivAt v -- totalisation-audit: allow `φ` is differentiable at `1` by the hypothesis `hφ`, so this is its true derivative

end Naturality

/-! ### The adjoint action -/

/-- Conjugation by `g` is differentiable. -/
theorem mdifferentiableAt_conj (g x : G) :
    MDifferentiableAt I I (fun h : G => g * h * g⁻¹) x :=
  (mdifferentiableAt_mul_right (a := g⁻¹)).comp x (mdifferentiableAt_mul_left (a := g))

variable (I) in
/-- The adjoint action of `g` on the Lie algebra: the derivative at the identity of the
conjugation `h ↦ g * h * g⁻¹`.  Conjugation fixes the identity, so this is an endomorphism of the
Lie algebra.

The definition does not itself refer to the Lie group structure, so it is accepted for any charted
group; it is meaningful only when `G` is a Lie group, which is the standing hypothesis of every
lemma about `Ad`.  Conjugation is then differentiable (`mdifferentiableAt_conj`), and `Ad I g` is
its true derivative (`hasMFDerivAt_conj`). -/
def Ad (g : G) : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G :=
  mfderiv I I (fun h : G => g * h * g⁻¹) 1 -- totalisation-audit: allow for a Lie group of class `C^∞`, the standing hypothesis of every lemma about `Ad`, conjugation is differentiable (`mdifferentiableAt_conj`), so this is its true derivative

/-- `Ad I g` is the derivative at the identity of conjugation by `g`. -/
theorem hasMFDerivAt_conj (g : G) :
    HasMFDerivAt I I (fun h : G => g * h * g⁻¹) 1 (Ad I g) :=
  (mdifferentiableAt_conj g 1).hasMFDerivAt

/-- A continuous linear map which is a derivative at the identity of conjugation by `g` equals
`Ad I g`. -/
theorem Ad_eq_of_hasMFDerivAt {g : G} {L : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G}
    (hL : HasMFDerivAt I I (fun h : G => g * h * g⁻¹) 1 L) : Ad I g = L :=
  hasMFDerivAt_unique (hasMFDerivAt_conj g) hL

/-- The adjoint action of a central element is the identity map. -/
theorem Ad_eq_id_of_forall_commute {g : G} (hg : ∀ h : G, Commute g h) :
    Ad I g = ContinuousLinearMap.id ℝ (GroupLieAlgebra I G) := by
  apply Ad_eq_of_hasMFDerivAt
  have hid : (fun x : G => g * x * g⁻¹) = id := by
    funext x
    rw [(hg x).eq, mul_inv_cancel_right, id]
  rw [hid]
  exact hasMFDerivAt_id 1

/-- The adjoint action of the identity is the identity map. -/
@[simp]
theorem Ad_one : Ad I (1 : G) = ContinuousLinearMap.id ℝ (GroupLieAlgebra I G) :=
  Ad_eq_id_of_forall_commute Commute.one_left

/-- The adjoint action is multiplicative. -/
theorem Ad_mul (g h : G) : Ad I (g * h) = (Ad I g).comp (Ad I h) := by
  apply Ad_eq_of_hasMFDerivAt
  have e : h * 1 * h⁻¹ = 1 := by simp
  have hg : HasMFDerivAt I I (fun x : G => g * x * g⁻¹) (h * 1 * h⁻¹) (Ad I g) := by
    rw [e]
    exact hasMFDerivAt_conj g
  have hc := HasMFDerivAt.comp (1 : G) hg (hasMFDerivAt_conj h)
  have hfun : (fun x : G => g * x * g⁻¹) ∘ (fun x : G => h * x * h⁻¹) =
      fun x : G => g * h * x * (g * h)⁻¹ := by
    funext x
    simp [mul_assoc]
  rw [hfun] at hc
  exact hc

/-- `Ad I g⁻¹` is a left inverse of `Ad I g`. -/
@[simp]
theorem Ad_inv_apply_Ad_apply (g : G) (v : GroupLieAlgebra I G) : Ad I g⁻¹ (Ad I g v) = v := by
  have h := DFunLike.congr_fun (Ad_mul (I := I) g⁻¹ g) v
  rw [inv_mul_cancel, Ad_one] at h
  exact h.symm

/-- `Ad I g⁻¹` is a right inverse of `Ad I g`. -/
@[simp]
theorem Ad_apply_Ad_inv_apply (g : G) (v : GroupLieAlgebra I G) : Ad I g (Ad I g⁻¹ v) = v := by
  have h := DFunLike.congr_fun (Ad_mul (I := I) g g⁻¹) v
  rw [mul_inv_cancel, Ad_one] at h
  exact h.symm

variable (I) in
/-- The adjoint action of `g` as a continuous linear equivalence of the Lie algebra, with inverse
`Ad I g⁻¹`. -/
def AdEquiv (g : G) : GroupLieAlgebra I G ≃L[ℝ] GroupLieAlgebra I G :=
  ContinuousLinearEquiv.equivOfInverse (Ad I g) (Ad I g⁻¹) (Ad_inv_apply_Ad_apply g)
    (Ad_apply_Ad_inv_apply g)

/-- The equivalence `AdEquiv I g` acts as `Ad I g`. -/
@[simp]
theorem AdEquiv_apply (g : G) (v : GroupLieAlgebra I G) : AdEquiv I g v = Ad I g v :=
  rfl

/-- The inverse of `AdEquiv I g` acts as `Ad I g⁻¹`. -/
@[simp]
theorem AdEquiv_symm_apply (g : G) (v : GroupLieAlgebra I G) :
    (AdEquiv I g).symm v = Ad I g⁻¹ v :=
  rfl

/-- The continuous linear map underlying `AdEquiv I g` is `Ad I g`. -/
theorem coe_AdEquiv (g : G) :
    (AdEquiv I g : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G) = Ad I g :=
  rfl

/-- The inverse of `AdEquiv I g` is `AdEquiv I g⁻¹`. -/
theorem AdEquiv_symm (g : G) : (AdEquiv I g).symm = AdEquiv I g⁻¹ := by
  ext v
  rfl

variable (I G) in
/-- The adjoint representation: `g ↦ AdEquiv I g` as a homomorphism from `G` to the group of
continuous linear automorphisms of the Lie algebra. -/
def AdHom : G →* (GroupLieAlgebra I G ≃L[ℝ] GroupLieAlgebra I G) where
  toFun := AdEquiv I
  map_one' := by
    ext v
    exact DFunLike.congr_fun (Ad_one (I := I) (G := G)) v
  map_mul' g h := by
    ext v
    exact DFunLike.congr_fun (Ad_mul (I := I) g h) v

/-- The homomorphism `AdHom I G` acts as `Ad I g`. -/
@[simp]
theorem AdHom_apply (g : G) (v : GroupLieAlgebra I G) : AdHom I G g v = Ad I g v :=
  rfl

/-- **Naturality of the adjoint action.** If the group homomorphism `φ` is differentiable at the
identity with derivative `L`, then `L ∘ Ad I g = Ad I' (φ g) ∘ L`.  Both sides are the derivative
at the identity of `h ↦ φ (g * h * g⁻¹) = φ g * φ h * (φ g)⁻¹`. -/
theorem comp_Ad_of_hasMFDerivAt (φ : G →* G')
    {L : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I' G'} (hL : HasMFDerivAt I I' φ 1 L)
    (g : G) : L.comp (Ad I g) = (Ad I' (φ g)).comp L := by
  have e : g * 1 * g⁻¹ = 1 := by simp
  have hL' : HasMFDerivAt I I' φ (g * 1 * g⁻¹) L := by
    rw [e]
    exact hL
  have h1 := HasMFDerivAt.comp (1 : G) hL' (hasMFDerivAt_conj g)
  have hA : HasMFDerivAt I' I' (fun x : G' => φ g * x * (φ g)⁻¹) (φ 1) (Ad I' (φ g)) := by
    rw [map_one]
    exact hasMFDerivAt_conj (φ g)
  have h2 := HasMFDerivAt.comp (1 : G) hA hL
  have hfun : (fun x : G' => φ g * x * (φ g)⁻¹) ∘ φ = φ ∘ fun x : G => g * x * g⁻¹ := by
    funext x
    simp
  rw [hfun] at h2
  exact hasMFDerivAt_unique h1 h2

/-! ### Conjugation and the exponential map -/

section ConjExp

variable [CompleteSpace E] [I.Boundaryless]

/-- Conjugation by `g` maps the one-parameter subgroup of `v` to that of `Ad I g v`. -/
theorem conj_exp_smul (g : G) (v : GroupLieAlgebra I G) (t : ℝ) :
    g * exp (t • v) * g⁻¹ = exp (t • Ad I g v) :=
  map_exp_smul_of_hasMFDerivAt (MulAut.conj g).toMonoidHom (hasMFDerivAt_conj g) v t

/-- **Conjugation and the exponential map.** `g * exp v * g⁻¹ = exp (Ad I g v)`. -/
theorem conj_exp (g : G) (v : GroupLieAlgebra I G) : g * exp v * g⁻¹ = exp (Ad I g v) :=
  map_exp_of_hasMFDerivAt (MulAut.conj g).toMonoidHom (hasMFDerivAt_conj g) v

/-- The vector `v` is fixed by `Ad I g` if and only if `g` commutes with the one-parameter
subgroup of `v`. -/
theorem Ad_apply_eq_self_iff (g : G) (v : GroupLieAlgebra I G) :
    Ad I g v = v ↔ ∀ t : ℝ, Commute g (exp (t • v)) := by
  constructor
  · intro h t
    have ht := conj_exp_smul g v t
    rw [h] at ht
    exact mul_inv_eq_iff_eq_mul.mp ht
  · intro h
    apply eq_of_exp_smul_eq
    intro t
    rw [← conj_exp_smul, (h t).eq, mul_inv_cancel_right]

end ConjExp

/-! ### The exponential of a sum of commuting elements -/

/-- The derivative of the multiplication of `G` at `(1, 1)` is `(u, w) ↦ u + w`. -/
theorem hasMFDerivAt_mul_one_one :
    HasMFDerivAt (I.prod I) I (fun p : G × G => p.1 * p.2) ((1 : G), (1 : G))
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) := by
  have hd : MDifferentiableAt (I.prod I) I (fun p : G × G => p.1 * p.2) ((1 : G), (1 : G)) :=
    (contMDiff_mul I ∞).mdifferentiableAt (by simp)
  have h1 : HasMFDerivAt I I (fun z : G => z * (1 : G)) 1 (ContinuousLinearMap.id ℝ E) := by
    rw [show (fun z : G => z * (1 : G)) = id from funext mul_one]
    exact hasMFDerivAt_id 1
  have h2 : HasMFDerivAt I I (fun z : G => (1 : G) * z) 1 (ContinuousLinearMap.id ℝ E) := by
    rw [show (fun z : G => (1 : G) * z) = id from funext one_mul]
    exact hasMFDerivAt_id 1
  refine hd.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext fun u => ?_)
  rw [mfderiv_prod_eq_add_apply hd]
  show mfderiv I I (fun z : G => z * (1 : G)) 1 u.1 + mfderiv I I (fun z : G => (1 : G) * z) 1 u.2 = u.1 + u.2 -- totalisation-audit: allow both partial maps are the identity map of `G`, differentiable with derivative `id` by `h1` and `h2`, so these are their true derivatives
  rw [h1.mfderiv, h2.mfderiv]
  rfl

/-- The velocity of a pointwise product of two curves, at a time where both pass through the
identity, is the sum of their velocities. -/
theorem hasMFDerivAt_mul_of_eq_one {γ δ : ℝ → G} {t : ℝ} (hγ1 : γ t = 1) (hδ1 : δ t = 1)
    {v w : GroupLieAlgebra I G}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hδ : HasMFDerivAt 𝓘(ℝ, ℝ) I δ t ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s * δ s) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v + w)) := by
  have hm : HasMFDerivAt (I.prod I) I (fun p : G × G => p.1 * p.2) (γ t, δ t)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) := by
    rw [hγ1, hδ1]
    exact hasMFDerivAt_mul_one_one
  have hc := HasMFDerivAt.comp t hm (hγ.prodMk hδ)
  exact hc.congr_mfderiv
    (ContinuousLinearMap.ext fun x => (smul_add (show ℝ from x) v w).symm)

section ExpAdd

variable [CompleteSpace E] [I.Boundaryless]

/-- If the one-parameter subgroups of `v` and `w` commute elementwise, then the one-parameter
subgroup of `v + w` is their pointwise product. -/
theorem exp_smul_add_of_commute {v w : GroupLieAlgebra I G}
    (hcomm : ∀ s t : ℝ, Commute (exp (s • v)) (exp (t • w))) (t : ℝ) :
    exp (t • (v + w)) = exp (t • v) * exp (t • w) := by
  have hmul : ∀ s t : ℝ, exp ((s + t) • v) * exp ((s + t) • w) =
      exp (s • v) * exp (s • w) * (exp (t • v) * exp (t • w)) := by
    intro s t
    rw [exp_add_smul, exp_add_smul, mul_assoc, mul_assoc, ← mul_assoc (exp (t • v)),
      (hcomm t s).eq, mul_assoc]
  have h0v : exp ((0 : ℝ) • v) = 1 := by rw [zero_smul, exp_zero]
  have h0w : exp ((0 : ℝ) • w) = 1 := by rw [zero_smul, exp_zero]
  have hd := hasMFDerivAt_mul_of_eq_one (γ := fun s : ℝ => exp (s • v))
    (δ := fun s : ℝ => exp (s • w)) (t := 0) h0v h0w (hasMFDerivAt_exp_smul_zero v)
    (hasMFDerivAt_exp_smul_zero w)
  exact (eq_exp_smul_of_map_add hmul hd t).symm

/-- If the one-parameter subgroups of `v` and `w` commute elementwise, then
`exp (v + w) = exp v * exp w`. -/
theorem exp_add_of_commute {v w : GroupLieAlgebra I G}
    (hcomm : ∀ s t : ℝ, Commute (exp (s • v)) (exp (t • w))) :
    exp (v + w) = exp v * exp w := by
  have h := exp_smul_add_of_commute hcomm 1
  rwa [one_smul, one_smul, one_smul] at h

end ExpAdd

/-! ### Commutative Lie groups -/

section Commutative

variable {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [CommGroup A] [LieGroup I ∞ A]

/-- In a commutative Lie group the adjoint action is trivial. -/
theorem Ad_eq_id (g : A) : Ad I g = ContinuousLinearMap.id ℝ (GroupLieAlgebra I A) :=
  Ad_eq_id_of_forall_commute (Commute.all g)

/-- In a commutative Lie group the exponential map is additive. -/
theorem exp_add [CompleteSpace E] [I.Boundaryless] (v w : GroupLieAlgebra I A) :
    exp (v + w) = exp v * exp w :=
  exp_add_of_commute fun _ _ => Commute.all _ _

end Commutative

end LieGroupExponential
