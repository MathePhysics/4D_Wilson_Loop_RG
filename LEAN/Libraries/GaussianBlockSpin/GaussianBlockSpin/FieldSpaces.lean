import GaussianBlockSpin.PiLpVolume

/-! Field spaces of several fields. For finite-dimensional real inner product fibres, the volume of `PiLp 2 E` is the
product of the fibre volumes (PiLp.volume_preserving_ofLp'; Mathlib has this for `ℝ` fibres only), via the flattening
isometry `piLpFlatten` and dependent currying (measurePreserving_piCurry_volume). Hence an iterated lintegral over a
family of fields and a further field is one lintegral over the inner product space `WithLp 2 (PiLp 2 E × V)`
(lintegral_lintegral_eq_lintegral_splitFields): the space on which the Gaussian measures of the effective actions live
(the fluctuation fields `A'_j` and the scalar field `φ'` of I.(3.35)). -/

namespace GaussianBlockSpin

open MeasureTheory Set

section SigmaCurry

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- Dependent currying `((Σ i, κ i) → ℝ) → (∀ i, κ i → ℝ)` preserves the coordinate Lebesgue measures. -/
theorem measurePreserving_piCurry_volume :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : ι) (_ : κ _) => ℝ))
      (volume : Measure ((p : Σ i, κ i) → ℝ)) volume where
  measurable := (MeasurableEquiv.piCurry (fun (_ : ι) (_ : κ _) => ℝ)).measurable
  map_eq := by
    rw [volume_pi, volume_pi]
    refine (Measure.pi_eq_generateFrom (C := fun i => pi univ '' pi univ fun _ : κ i => {s : Set ℝ | MeasurableSet s})
      (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
      (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℝ).toFiniteSpanningSetsIn) ?_).symm
    intro s hs
    choose t ht hts using hs
    have hpre : (MeasurableEquiv.piCurry (fun (_ : ι) (_ : κ _) => ℝ)) ⁻¹' pi univ s =
        pi univ fun p : Σ i, κ i => t p.1 p.2 := by
      ext f
      simp only [mem_preimage, mem_pi, mem_univ, forall_const, ← hts, MeasurableEquiv.coe_piCurry, Sigma.forall]
      rfl
    rw [Measure.map_apply (MeasurableEquiv.piCurry (fun (_ : ι) (_ : κ _) => ℝ)).measurable
      (MeasurableSet.univ_pi fun i => hts i ▸ MeasurableSet.univ_pi fun k => ht i k (mem_univ k)), hpre, Measure.pi_pi,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hts i, Measure.pi_pi]

end SigmaCurry

section PiLpGeneral

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

/-- Flattening `PiLp 2 E ≃ₗᵢ EuclideanSpace ℝ (Σ i, Fin (dim E_i))` through the standard orthonormal bases. -/
noncomputable def piLpFlatten :
    PiLp 2 E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Σ i, Fin (Module.finrank ℝ (E i))) where
  toFun x := WithLp.toLp 2 fun p => (stdOrthonormalBasis ℝ (E p.1)).repr (x p.1) p.2
  invFun y := WithLp.toLp 2 fun i => (stdOrthonormalBasis ℝ (E i)).repr.symm (WithLp.toLp 2 fun k => y ⟨i, k⟩)
  map_add' x y := by
    ext p
    simp
  map_smul' c x := by
    ext p
    simp
  left_inv x := by
    ext1 i
    dsimp only
    rw [show (WithLp.toLp 2 fun k => (stdOrthonormalBasis ℝ (E i)).repr (x i) k :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (E i)))) = (stdOrthonormalBasis ℝ (E i)).repr (x i) from rfl]
    exact (stdOrthonormalBasis ℝ (E i)).repr.symm_apply_apply (x i)
  right_inv y := by
    ext p
    simp only [LinearIsometryEquiv.apply_symm_apply]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, PiLp.norm_eq_of_L2]
    congr 1
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (stdOrthonormalBasis ℝ (E i)).repr.norm_map (x i), EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    rfl

variable [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]

/-- **The volume of `PiLp 2 E` is the product of the volumes of the fibres**: `ofLp : PiLp 2 E → ∀ i, E i` is volume
preserving (finite-dimensional real inner product fibres; Mathlib has this for `ℝ` fibres only). -/
theorem PiLp.volume_preserving_ofLp' :
    MeasurePreserving (WithLp.ofLp : PiLp 2 E → ∀ i, E i) volume volume := by
  have h := (volume_preserving_pi (fun i => (LinearIsometryEquiv.measurePreserving
      (stdOrthonormalBasis ℝ (E i)).repr.symm))).comp
    ((volume_preserving_pi (fun i => PiLp.volume_preserving_toLp (Fin (Module.finrank ℝ (E i))))).comp
      (measurePreserving_piCurry_volume.comp ((PiLp.volume_preserving_ofLp _).comp
        (LinearIsometryEquiv.measurePreserving (piLpFlatten (E := E))))))
  convert h using 1
  funext x
  funext i
  simp only [Function.comp_apply, MeasurableEquiv.coe_piCurry]
  show x i = (stdOrthonormalBasis ℝ (E i)).repr.symm (WithLp.toLp 2 fun k =>
    (stdOrthonormalBasis ℝ (E i)).repr (x i) k)
  rw [show (WithLp.toLp 2 fun k => (stdOrthonormalBasis ℝ (E i)).repr (x i) k :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (E i)))) = (stdOrthonormalBasis ℝ (E i)).repr (x i) from rfl]
  exact ((stdOrthonormalBasis ℝ (E i)).repr.symm_apply_apply (x i)).symm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The map from the single field space `WithLp 2 (PiLp 2 E × V)` to the pair (family of fields, field). -/
def splitFields (x : WithLp 2 (PiLp 2 E × V)) : (∀ i, E i) × V :=
  (WithLp.ofLp (WithLp.ofLp x).1, (WithLp.ofLp x).2)

/-- `splitFields` is volume preserving (the volume of each side is the product of the coordinate Lebesgue measures). -/
theorem measurePreserving_splitFields :
    MeasurePreserving (splitFields (E := E) (V := V)) volume volume := by
  have h := (MeasurePreserving.prod (PiLp.volume_preserving_ofLp' (E := E)) (MeasurePreserving.id volume)).comp
    (WithLp.volume_preserving_ofLp (PiLp 2 E) V)
  rw [Measure.volume_eq_prod]
  exact h

/-- **An iterated lintegral over (family of fields, field) is one lintegral over the inner product space**
`WithLp 2 (PiLp 2 E × V)`. -/
theorem lintegral_lintegral_eq_lintegral_splitFields (f : (∀ i, E i) → V → ENNReal)
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ a, ∫⁻ v, f a v = ∫⁻ x : WithLp 2 (PiLp 2 E × V), f (splitFields x).1 (splitFields x).2 := by
  have h := lintegral_prod (μ := (volume : Measure (∀ i, E i))) (ν := (volume : Measure V)) (Function.uncurry f)
    hf.aemeasurable
  simp only [Function.uncurry_apply_pair] at h
  rw [← h, ← Measure.volume_eq_prod]
  exact ((measurePreserving_splitFields (E := E) (V := V)).lintegral_comp hf).symm

end PiLpGeneral

end GaussianBlockSpin
