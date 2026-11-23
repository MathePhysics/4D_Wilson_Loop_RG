import CompactLieHeatKernel.KernelSemigroup
import CompactLieHeatKernel.FellerLift
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap
import Mathlib.Topology.CompactOpen

/-!
# Compact-manifold heat-kernel theorem: the reduced analytic core

The classical compact-manifold theorem says that the heat semigroup of a self-adjoint elliptic
Laplace-type operator has a jointly smooth, strictly positive kernel.  Current mathlib does not yet
contain the elliptic/parabolic regularity and strong maximum-principle package needed to construct
that kernel intrinsically.

This file isolates that genuinely PDE-specific input as tightly as possible.  We assume only a
smooth positive symmetric density representing a Feller semigroup on `C(M, ℝ)`.  Normalisation and
Chapman--Kolmogorov are *not* fields: they are derived from preservation of constants and the
semigroup law.  Hence the output is the full `SmoothHeatKernelData` expected by the rest of the
project.

The Chapman--Kolmogorov proof is pointwise.  Fubini first gives equality against every continuous
test function.  Testing against the continuous difference itself gives zero L² norm; full support
of the reference measure upgrades almost-everywhere equality to equality everywhere.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Manifold Topology ProbabilityTheory ContDiff

namespace CompactLieHeatKernel

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M] [CompactSpace M]
    [ChartedSpace H M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    {μ : Measure M} [IsProbabilityMeasure μ] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- The reduced analytic input for the compact-manifold heat-kernel theorem.

`fellerOp` is the positive-time semigroup acting on continuous functions.  The fields
`feller_add`, `feller_one`, and `represents` are the semigroup/fundamental-solution statements that
come before kernel normalisation and Chapman--Kolmogorov.  Smoothness, strict positivity, and
symmetry are the genuinely geometric/PDE outputs that remain to be constructed from the
Laplacian. -/
structure CompactManifoldHeatKernelCore
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [T2Space M]
    [LocallyCompactSpace M] [CompactSpace M] [ChartedSpace H M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [IsProbabilityMeasure μ]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] where
  fellerOp : ℝ≥0 → C(M, ℝ) →L[ℝ] C(M, ℝ)
  feller_add : ∀ s t, fellerOp (s + t) = (fellerOp s).comp (fellerOp t)
  feller_one : ∀ t, fellerOp t (ContinuousMap.const M (1 : ℝ)) = ContinuousMap.const M 1
  density : ℝ≥0 → M → M → ℝ
  strictlyPositive : ∀ t, t ≠ 0 → ∀ x y, 0 < density t x y
  symmetric : ∀ t, t ≠ 0 → ∀ x y, density t x y = density t y x
  smooth_density : ∀ t, t ≠ 0 →
    ContMDiff (I.prod I) 𝓘(ℝ) ∞ (Function.uncurry (density t))
  represents : ∀ t, t ≠ 0 → ∀ f : C(M, ℝ), ∀ x,
    fellerOp t f x = ∫ y, density t x y * f y ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem

namespace CompactManifoldHeatKernelCore

/-- The jointly continuous kernel as a bundled continuous map. -/
def densityContinuousMap (K : CompactManifoldHeatKernelCore I M μ)
    (t : ℝ≥0) (ht : t ≠ 0) : C(M × M, ℝ) :=
  ⟨Function.uncurry (K.density t), (K.smooth_density t ht).continuous⟩

/-- The family `x ↦ k_t(x, ·)` as a continuous map into `C(M, ℝ)`. -/
def densityRows (K : CompactManifoldHeatKernelCore I M μ)
    (t : ℝ≥0) (ht : t ≠ 0) : C(M, C(M, ℝ)) :=
  (K.densityContinuousMap t ht).curry

@[simp]
theorem densityRows_apply (K : CompactManifoldHeatKernelCore I M μ)
    (t : ℝ≥0) (ht : t ≠ 0) (x y : M) :
    K.densityRows t ht x y = K.density t x y :=
  rfl

/-- Every positive-time kernel row is integrable on the compact probability space. -/
theorem densityRow_integrable (K : CompactManifoldHeatKernelCore I M μ)
    (t : ℝ≥0) (ht : t ≠ 0) (x : M) :
    Integrable (fun y => K.density t x y) μ := by
  exact (K.densityRows t ht x).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Preservation of the constant function forces the density to have real integral one. -/
theorem integral_density_eq_one (K : CompactManifoldHeatKernelCore I M μ)
    (t : ℝ≥0) (ht : t ≠ 0) (x : M) :
    ∫ y, K.density t x y ∂μ = 1 := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
  have h := congrArg (fun f : C(M, ℝ) => f x) (K.feller_one t)
  rw [K.represents t ht (ContinuousMap.const M (1 : ℝ)) x] at h
  simpa using h

/-- Hence every positive-time row has mass one in the extended-real density convention used by
`MeasurableHeatKernelData`. -/
theorem lintegral_density_eq_one (K : CompactManifoldHeatKernelCore I M μ)
    (t : ℝ≥0) (ht : t ≠ 0) (x : M) :
    ∫⁻ y, ENNReal.ofReal (K.density t x y) ∂μ = 1 := by
  calc
    ∫⁻ y, ENNReal.ofReal (K.density t x y) ∂μ
        = ENNReal.ofReal (∫ y, K.density t x y ∂μ) := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
            symm
            exact ofReal_integral_eq_lintegral_ofReal (K.densityRow_integrable t ht x)
              (Filter.Eventually.of_forall fun y => (K.strictlyPositive t ht x y).le)
    _ = 1 := by rw [K.integral_density_eq_one t ht x]; simp

/-- The continuous-map-valued integrand whose Bochner integral is the convolution row
`z ↦ ∫ k_s(x,y) k_t(y,z) dμ(y)`. -/ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
def convolutionIntegrand (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (_hs : s ≠ 0) (ht : t ≠ 0) (x y : M) : C(M, ℝ) :=
  K.density s x y • K.densityRows t ht y

/-- The convolution integrand is continuous as a `C(M,ℝ)`-valued function. -/
theorem continuous_convolutionIntegrand (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (x : M) :
    Continuous (fun y => K.convolutionIntegrand s t hs ht x y) := by
  exact (K.densityRows s hs x).continuous.smul (K.densityRows t ht).continuous

/-- Compactness makes the continuous-map-valued convolution integrand Bochner integrable. -/
theorem convolutionIntegrand_integrable (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (x : M) :
    Integrable (fun y => K.convolutionIntegrand s t hs ht x y) μ := by
  exact (K.continuous_convolutionIntegrand s t hs ht x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The pointwise convolution row, bundled as a continuous function of the endpoint. -/
def convolutionRow (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (x : M) : C(M, ℝ) :=
  ∫ y, K.convolutionIntegrand s t hs ht x y ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem

/-- Evaluation of the continuous convolution row gives the expected scalar integral. -/
theorem convolutionRow_apply (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (x z : M) :
    K.convolutionRow s t hs ht x z =
      ∫ y, K.density s x y * K.density t y z ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
  rw [convolutionRow, ContinuousMap.integral_apply
    (K.convolutionIntegrand_integrable s t hs ht x) z]
  simp [convolutionIntegrand]

/-- The two-variable integrand used in the Fubini step is integrable by compactness. -/
theorem convolution_test_integrable (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (x : M) (f : C(M, ℝ)) :
    Integrable (Function.uncurry fun y z =>
      K.density s x y * (K.density t y z * f z)) (μ.prod μ) := by
  have hcont : Continuous (Function.uncurry fun y z =>
      K.density s x y * (K.density t y z * f z)) := by
    exact ((K.densityRows s hs x).continuous.comp continuous_fst).mul
      (((K.densityContinuousMap t ht).continuous).mul
        (f.continuous.comp continuous_snd))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Semigroup composition identifies the convolution row with the time-`s+t` row when tested
against any continuous function. -/
theorem integral_convolutionRow_mul (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (x : M) (f : C(M, ℝ)) :
    ∫ z, K.convolutionRow s t hs ht x z * f z ∂μ = -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
      ∫ z, K.density (s + t) x z * f z ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
  have hst : s + t ≠ 0 := by simp [hs, ht]
  calc
    ∫ z, K.convolutionRow s t hs ht x z * f z ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
        = ∫ z, (∫ y, K.density s x y * K.density t y z ∂μ) * f z ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
            simp_rw [K.convolutionRow_apply s t hs ht x]
    _ = ∫ z, ∫ y, -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          K.density s x y * (K.density t y z * f z) ∂μ ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            change (∫ y, K.density s x y * K.density t y z ∂μ) * f z = -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
              ∫ y, K.density s x y * (K.density t y z * f z) ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
            simpa [mul_assoc] using
              (integral_mul_const (μ := μ) (f z)
                (fun y => K.density s x y * K.density t y z)).symm
    _ = ∫ y, ∫ z, -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          K.density s x y * (K.density t y z * f z) ∂μ ∂μ := by
            exact (integral_integral_swap (K.convolution_test_integrable s t hs ht x f)).symm
    _ = ∫ y, K.density s x y * -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          (∫ z, K.density t y z * f z ∂μ) ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            change (∫ z, K.density s x y * (K.density t y z * f z) ∂μ) = -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
              K.density s x y * (∫ z, K.density t y z * f z ∂μ) -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
            exact integral_const_mul (μ := μ) (K.density s x y)
              (fun z => K.density t y z * f z)
    _ = ∫ y, K.density s x y * (K.fellerOp t f y) ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            change K.density s x y * (∫ z, K.density t y z * f z ∂μ) = -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
              K.density s x y * K.fellerOp t f y
            rw [← K.represents t ht f y]
    _ = K.fellerOp s (K.fellerOp t f) x := by
            symm
            exact K.represents s hs (K.fellerOp t f) x
    _ = K.fellerOp (s + t) f x := by
            rw [K.feller_add s t]
            rfl
    _ = ∫ z, K.density (s + t) x z * f z ∂μ := -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
            K.represents (s + t) hst f x

/-- Pointwise real-valued Chapman--Kolmogorov, derived rather than assumed. -/
theorem real_chapmanKolmogorov (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (x z : M) :
    ∫ y, K.density s x y * K.density t y z ∂μ = K.density (s + t) x z := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
  have hst : s + t ≠ 0 := by simp [hs, ht]
  let d : C(M, ℝ) := K.convolutionRow s t hs ht x - K.densityRows (s + t) hst x
  have htest := K.integral_convolutionRow_mul s t hs ht x d
  have hleft : Integrable (fun z => K.convolutionRow s t hs ht x z * d z) μ := by
    exact ((K.convolutionRow s t hs ht x).continuous.mul d.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun z => K.density (s + t) x z * d z) μ := by
    exact (((K.densityRows (s + t) hst x).continuous).mul d.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hzero : ∫ z, d z * d z ∂μ = 0 := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
    calc
      ∫ z, d z * d z ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          = ∫ z, (K.convolutionRow s t hs ht x z - K.density (s + t) x z) * d z ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
              rfl
      _ = (∫ z, K.convolutionRow s t hs ht x z * d z ∂μ) - -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          (∫ z, K.density (s + t) x z * d z ∂μ) := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
              rw [← integral_sub hleft hright]
              congr with z
              ring
      _ = 0 := by rw [htest, sub_self]
  have hdae_sq : (fun z => d z * d z) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg (d z))
      ((d.continuous.mul d.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).mp hzero
  have hdae : (fun z => d z) =ᵐ[μ] 0 := by
    filter_upwards [hdae_sq] with z hz
    exact mul_self_eq_zero.mp hz
  have hd : (fun z => d z) = fun _ => 0 :=
    (d.continuous.ae_eq_iff_eq μ continuous_zero).mp hdae
  have hz := congrFun hd z
  change K.convolutionRow s t hs ht x z - K.density (s + t) x z = 0 at hz
  exact (K.convolutionRow_apply s t hs ht x z).symm.trans (sub_eq_zero.mp hz)

/-- Extended-real Chapman--Kolmogorov in the exact convention required by
`MeasurableHeatKernelData`. -/
theorem lintegral_chapmanKolmogorov (K : CompactManifoldHeatKernelCore I M μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (x z : M) :
    ∫⁻ y, ENNReal.ofReal (K.density s x y) * ENNReal.ofReal (K.density t y z) ∂μ =
      ENNReal.ofReal (K.density (s + t) x z) := by
  have hcont : Continuous fun y => K.density s x y * K.density t y z :=
    (K.densityRows s hs x).continuous.mul
      ((K.densityContinuousMap t ht).continuous.comp
        (continuous_id.prodMk continuous_const))
  have hint : Integrable (fun y => K.density s x y * K.density t y z) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    ∫⁻ y, ENNReal.ofReal (K.density s x y) * ENNReal.ofReal (K.density t y z) ∂μ
        = ∫⁻ y, ENNReal.ofReal (K.density s x y * K.density t y z) ∂μ := by
            apply lintegral_congr
            intro y
            rw [ENNReal.ofReal_mul ((K.strictlyPositive s hs x y).le)]
    _ = ENNReal.ofReal (∫ y, K.density s x y * K.density t y z ∂μ) := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
            symm
            exact ofReal_integral_eq_lintegral_ofReal hint
              (Filter.Eventually.of_forall fun y =>
                mul_nonneg ((K.strictlyPositive s hs x y).le) ((K.strictlyPositive t ht y z).le))
    _ = ENNReal.ofReal (K.density (s + t) x z) := by
            rw [K.real_chapmanKolmogorov s t hs ht x z]

/-- The reduced compact-manifold theorem: the Feller/smoothing core produces the complete smooth
heat-kernel datum.  In particular mass one and Chapman--Kolmogorov are conclusions. -/
def toSmoothHeatKernelData (K : CompactManifoldHeatKernelCore I M μ) :
    SmoothHeatKernelData I M μ where
  density := K.density
  nonnegative := fun t ht x y => (K.strictlyPositive t ht x y).le
  strictlyPositive := K.strictlyPositive
  measurable_density_ofReal t ht :=
    ENNReal.measurable_ofReal.comp ((K.smooth_density t ht).continuous.measurable)
  mass_one := K.lintegral_density_eq_one
  symmetric := K.symmetric
  chapmanKolmogorov := K.lintegral_chapmanKolmogorov
  continuous_density t ht := (K.smooth_density t ht).continuous
  smooth_density := K.smooth_density

end CompactManifoldHeatKernelCore

/-- The genuinely analytic regularisation output attached to a Feller lift of the L² heat
semigroup.  In contrast with `SmoothHeatKernelData`, this structure does not assume mass one,
Chapman--Kolmogorov, or an independent Feller semigroup law: those are derived. -/
structure CompactManifoldRegularisationData
    (S : L2SelfAdjointMarkovSemigroup μ) (F : FellerLift S) where
  density : ℝ≥0 → M → M → ℝ
  strictlyPositive : ∀ t, t ≠ 0 → ∀ x y, 0 < density t x y
  smooth_density : ∀ t, t ≠ 0 →
    ContMDiff (I.prod I) 𝓘(ℝ) ∞ (Function.uncurry (density t))
  represents : ∀ t, t ≠ 0 → ∀ f : C(M, ℝ), ∀ x,
    F.op t f x = ∫ y, density t x y * f y ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem

namespace CompactManifoldRegularisationData

variable {S : L2SelfAdjointMarkovSemigroup μ} {F : FellerLift S}

/-- The jointly continuous density supplied by regularisation. -/
def densityContinuousMap (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) : C(M × M, ℝ) :=
  ⟨Function.uncurry (R.density t), (R.smooth_density t ht).continuous⟩

/-- The row `y ↦ k_t(x,y)` as a continuous function. -/
def densityRow (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) (x : M) : C(M, ℝ) :=
  ⟨fun y => R.density t x y,
    (R.densityContinuousMap t ht).continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- The column `y ↦ k_t(y,x)` as a continuous function. -/
def densityColumn (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) (x : M) : C(M, ℝ) :=
  ⟨fun y => R.density t y x,
    (R.densityContinuousMap t ht).continuous.comp (continuous_id.prodMk continuous_const)⟩

/-- The transposed kernel action, bundled as a continuous function of the endpoint. -/
def transposeAction (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) (f : C(M, ℝ)) : C(M, ℝ) :=
  ∫ y, f y • R.densityRow t ht y ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem

omit [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M] [μ.IsOpenPosMeasure] in
/-- Evaluation of the transposed kernel action. -/
theorem transposeAction_apply (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) (f : C(M, ℝ)) (x : M) :
    R.transposeAction t ht f x = ∫ y, f y * R.density t y x ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
  have hint : Integrable (fun y => f y • R.densityRow t ht y) μ := by
    have hcont : Continuous (fun y => f y • R.densityRow t ht y) := by
      exact f.continuous.smul (R.densityContinuousMap t ht).curry.continuous
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [transposeAction, ContinuousMap.integral_apply hint x]
  rfl

omit [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] in
/-- Self-adjointness of the L² semigroup descends to the Feller lift on continuous test
functions. -/
theorem feller_pairing_symmetric (_R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (f g : C(M, ℝ)) :
    ∫ x, F.op t f x * g x ∂μ = ∫ x, f x * F.op t g x ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
  have hsym := S.symmetric t
    ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) f)
    ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) g)
  rw [← F.compatible t f, ← F.compatible t g] at hsym
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hsym
  have hleft :
      (fun x => inner ℝ
        ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (F.op t f) x)
        ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) g x)) =ᵐ[μ]
        (fun x => F.op t f x * g x) := by
    filter_upwards
      [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := μ) (𝕜 := ℝ) (F.op t f),
       ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := μ) (𝕜 := ℝ) g]
      with x hx hy
    rw [hx, hy]
    simp [mul_comm]
  have hright :
      (fun x => inner ℝ
        ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) f x)
        ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (F.op t g) x)) =ᵐ[μ]
        (fun x => f x * F.op t g x) := by
    filter_upwards
      [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := μ) (𝕜 := ℝ) f,
       ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := μ) (𝕜 := ℝ) (F.op t g)]
      with x hx hy
    rw [hx, hy]
    simp [mul_comm]
  exact (integral_congr_ae hleft).symm.trans (hsym.trans (integral_congr_ae hright))

omit [T2Space M] [μ.IsOpenPosMeasure] in
/-- The scalar two-variable integrand needed to transpose the kernel action is integrable. -/
theorem transpose_test_integrable (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) (f g : C(M, ℝ)) :
    Integrable (Function.uncurry fun x y => f x * (R.density t x y * g y)) (μ.prod μ) := by
  have hcont : Continuous (Function.uncurry fun x y => f x * (R.density t x y * g y)) := by
    exact (f.continuous.comp continuous_fst).mul
      ((R.densityContinuousMap t ht).continuous.mul (g.continuous.comp continuous_snd))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [T2Space M] [μ.IsOpenPosMeasure] in
/-- The self-adjoint Feller action is also represented by the transposed kernel. -/
theorem integral_feller_eq_transpose (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) (f g : C(M, ℝ)) :
    ∫ x, F.op t f x * g x ∂μ = ∫ x, R.transposeAction t ht f x * g x ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
  calc
    ∫ x, F.op t f x * g x ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
        = ∫ x, f x * F.op t g x ∂μ := R.feller_pairing_symmetric t f g -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
    _ = ∫ x, f x * (∫ y, R.density t x y * g y ∂μ) ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          change f x * F.op t g x = f x * (∫ y, R.density t x y * g y ∂μ) -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
          rw [R.represents t ht g x]
    _ = ∫ x, ∫ y, f x * (R.density t x y * g y) ∂μ ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          change f x * (∫ y, R.density t x y * g y ∂μ) = -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
            ∫ y, f x * (R.density t x y * g y) ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
          exact (integral_const_mul (μ := μ) (f x)
            (fun y => R.density t x y * g y)).symm
    _ = ∫ y, ∫ x, f x * (R.density t x y * g y) ∂μ ∂μ := -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          integral_integral_swap (R.transpose_test_integrable t ht f g)
    _ = ∫ y, (∫ x, f x * R.density t x y ∂μ) * g y ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          change (∫ x, f x * (R.density t x y * g y) ∂μ) = -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
            (∫ x, f x * R.density t x y ∂μ) * g y -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
          simpa [mul_assoc] using
            (integral_mul_const (μ := μ) (g y)
              (fun x => f x * R.density t x y))
    _ = ∫ y, R.transposeAction t ht f y * g y ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          change (∫ x, f x * R.density t x y ∂μ) * g y = -- totalisation-audit: allow integrability is supplied by compactness/continuity in the surrounding theorem
            R.transposeAction t ht f y * g y
          rw [R.transposeAction_apply t ht f y]

omit [T2Space M] in
/-- Pointwise representation by the transposed kernel, derived from L² self-adjointness. -/
theorem transpose_represents (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) (f : C(M, ℝ)) :
    F.op t f = R.transposeAction t ht f := by
  let d : C(M, ℝ) := F.op t f - R.transposeAction t ht f
  have htest := R.integral_feller_eq_transpose t ht f d
  have hleft : Integrable (fun x => F.op t f x * d x) μ := by
    exact ((F.op t f).continuous.mul d.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun x => R.transposeAction t ht f x * d x) μ := by
    exact ((R.transposeAction t ht f).continuous.mul d.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hzero : ∫ x, d x * d x ∂μ = 0 := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
    calc
      ∫ x, d x * d x ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          = ∫ x, (F.op t f x - R.transposeAction t ht f x) * d x ∂μ := by rfl -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
      _ = (∫ x, F.op t f x * d x ∂μ) - -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          (∫ x, R.transposeAction t ht f x * d x ∂μ) := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
            rw [← integral_sub hleft hright]
            congr with x
            ring
      _ = 0 := by rw [htest, sub_self]
  have hdae_sq : (fun x => d x * d x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (d x))
      ((d.continuous.mul d.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).mp hzero
  have hdae : (fun x => d x) =ᵐ[μ] 0 := by
    filter_upwards [hdae_sq] with x hx
    exact mul_self_eq_zero.mp hx
  have hd : (fun x => d x) = fun _ => 0 :=
    (d.continuous.ae_eq_iff_eq μ continuous_zero).mp hdae
  ext x
  have hx := congrFun hd x
  change F.op t f x - R.transposeAction t ht f x = 0 at hx
  exact sub_eq_zero.mp hx

omit [T2Space M] in
/-- Symmetry of the positive-time kernel is a theorem, not an independent regularity input. -/
theorem symmetric (R : CompactManifoldRegularisationData (I := I) S F)
    (t : ℝ≥0) (ht : t ≠ 0) (x y : M) :
    R.density t x y = R.density t y x := by
  let d : C(M, ℝ) := R.densityRow t ht x - R.densityColumn t ht x
  have hrow := R.represents t ht d x
  have htrans := congrArg (fun q : C(M, ℝ) => q x) (R.transpose_represents t ht d)
  rw [R.transposeAction_apply t ht d x] at htrans
  have heq :
      ∫ z, R.density t x z * d z ∂μ = ∫ z, d z * R.density t z x ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
    exact hrow.symm.trans htrans
  have heq' :
      ∫ z, R.density t x z * d z ∂μ = ∫ z, R.density t z x * d z ∂μ := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
    refine heq.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
    ring
  have hleft : Integrable (fun z => R.density t x z * d z) μ := by
    exact ((R.densityRow t ht x).continuous.mul d.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun z => R.density t z x * d z) μ := by
    exact ((R.densityColumn t ht x).continuous.mul d.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hzero : ∫ z, d z * d z ∂μ = 0 := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
    calc
      ∫ z, d z * d z ∂μ -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          = ∫ z, (R.density t x z - R.density t z x) * d z ∂μ := by rfl -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
      _ = (∫ z, R.density t x z * d z ∂μ) - -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
          (∫ z, R.density t z x * d z ∂μ) := by -- totalisation-audit: allow integrability is supplied by compactness/continuity or an explicit Integrable hypothesis in the surrounding theorem
            rw [← integral_sub hleft hright]
            congr with z
            ring
      _ = 0 := by rw [heq', sub_self]
  have hdae_sq : (fun z => d z * d z) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg (d z))
      ((d.continuous.mul d.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).mp hzero
  have hdae : (fun z => d z) =ᵐ[μ] 0 := by
    filter_upwards [hdae_sq] with z hz
    exact mul_self_eq_zero.mp hz
  have hd : (fun z => d z) = fun _ => 0 :=
    (d.continuous.ae_eq_iff_eq μ continuous_zero).mp hdae
  have hy := congrFun hd y
  change R.density t x y - R.density t y x = 0 at hy
  exact sub_eq_zero.mp hy

/-- A regularisation datum plus L² compatibility supplies the reduced compact-manifold core. -/
def toCore (R : CompactManifoldRegularisationData (I := I) S F) :
    CompactManifoldHeatKernelCore I M μ where
  fellerOp := F.op
  feller_add := F.op_add
  feller_one := F.op_one
  density := R.density
  strictlyPositive := R.strictlyPositive
  symmetric := R.symmetric
  smooth_density := R.smooth_density
  represents := R.represents

/-- Final compact-manifold output used by the rest of the heat-kernel project.  Normalisation and
Chapman--Kolmogorov are proved on the way from the regularisation datum to this structure. -/
def toSmoothHeatKernelData (R : CompactManifoldRegularisationData (I := I) S F) :
    SmoothHeatKernelData I M μ :=
  R.toCore.toSmoothHeatKernelData

/-- The positive-time transition kernels produced by the compact-manifold theorem form the expected
Markov semigroup. -/
theorem transitionKernel_comp (R : CompactManifoldRegularisationData (I := I) S F)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) :
    let K := R.toSmoothHeatKernelData.toContinuousHeatKernelData.toMeasurableHeatKernelData
    K.transitionKernel t ∘ₖ K.transitionKernel s = K.transitionKernel (s + t) := by
  dsimp
  exact MeasurableHeatKernelData.transitionKernel_comp
    R.toSmoothHeatKernelData.toContinuousHeatKernelData.toMeasurableHeatKernelData s t hs ht

/-- Existential theorem form of the v0.3 reduction.  The supplied regularisation density is retained
exactly in the resulting smooth heat-kernel datum. -/
theorem compactManifoldHeatKernel_of_regularisation
    (R : CompactManifoldRegularisationData (I := I) S F) :
    ∃ K : SmoothHeatKernelData I M μ,
      ∀ t x y, K.density t x y = R.density t x y := by
  exact ⟨R.toSmoothHeatKernelData, fun _ _ _ => rfl⟩

end CompactManifoldRegularisationData
end CompactLieHeatKernel
