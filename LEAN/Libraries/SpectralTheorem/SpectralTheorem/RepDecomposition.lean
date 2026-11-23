import SpectralTheorem.RepCyclic
import SpectralTheorem.SigmaL2
import SpectralTheorem.MultiplicationBounded
import SpectralTheorem.SeparableDecomposition
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Order.Zorn

/-!
# Representations of `C(X)`: cyclic decomposition and multiplication operator form

Let `X` be a compact Hausdorff space and `π : C(X, ℂ) → 𝓛(H)` a unital `⋆`-representation on a
complex Hilbert space `H`.  Reed–Simon I, §VII.2, Lemma 2, p. 226 (a Hilbert space is a direct
sum of cyclic subspaces) and Theorem VII.3, p. 227 (multiplication operator form), stated there
for one bounded self-adjoint operator, hold for `π` with the same proofs:

* Zorn's lemma gives a set of vectors whose cyclic subspaces are pairwise orthogonal and maximal
  with this property; maximality forces the cyclic subspaces to span a dense subspace, because a
  vector orthogonal to all of them has a cyclic subspace orthogonal to all of them
  (`repCyclicSubmodule_isOrtho`).  Reed–Simon assume `H` separable; here `H` is arbitrary.
* With the cyclic isometries `L²(X, μ_ψ) → H` of `SpectralTheorem.RepCyclic` this makes `H` the
  Hilbert sum of the spaces `L²(X, μ_ψ)`, which is `L²(M, μ)` for the disjoint union
  `M = Σ_ψ X` with `μ = Σ_ψ μ_ψ` (`SpectralTheorem.sigmaL2Equiv`).
* On each summand `π(g)` is multiplication by `g` (`repCyclicIsometry_smul`), and both sides of
  `U π(g) = M_{g ∘ F} U` are continuous and linear, so the identity holds on the Hilbert sum.

The proofs are those of `SpectralTheorem.Decomposition` and `SpectralTheorem.MultiplicationForm`,
with `X` and `π` in place of `σ(T)` and `cfcHom`.  `X` is not assumed metrizable, and without
separability of `H` the measure `μ` need not be finite or σ-finite.

## Main definitions and results

* `SpectralTheorem.RepDecomposition π`: a set of vectors with pairwise orthogonal cyclic
  subspaces, such that only `0` is orthogonal to all of them.
* `SpectralTheorem.RepDecomposition.nonempty`: such a decomposition exists (Zorn).
* `SpectralTheorem.RepDecomposition.isHilbertSum`, `.equiv`: `H ≃ ⊕̂_ψ L²(X, μ_ψ)`.
* `SpectralTheorem.RepDecomposition.Space`, `.measure`, `.point`: the measure space `Σ_ψ X`, the
  measure `Σ_ψ μ_ψ` and the projection `(ψ, x) ↦ x`.
* `SpectralTheorem.RepDecomposition.unitary`: the unitary `U : H ≃ L²(Σ_ψ X, Σ_ψ μ_ψ)`.
* `SpectralTheorem.RepDecomposition.unitary_apply`: `U (π(g) h) = g(x) · U h`;
  `coeFn_unitary_apply`: the same almost everywhere.
* `SpectralTheorem.exists_unitary_mulL_rep`: **multiplication operator form of a representation
  of `C(X)`**: `π` is unitarily equivalent to `g ↦ M_{g ∘ F}` on some `L²(M, μ)`.
* `SpectralTheorem.RepDecomposition.exists_isFiniteMeasure`, `exists_unitary_mulL_rep_finite`:
  for separable `H` the measure can be taken finite (Reed–Simon I, Corollary to Theorem VII.3,
  p. 227: rescale the countably many cyclic vectors to norms `2⁻ⁿ`), as in
  `SpectralTheorem.SeparableDecomposition`.
-/

noncomputable section

open scoped InnerProductSpace ENNReal
open MeasureTheory Filter

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type u} [TopologicalSpace X]
variable (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- A set of vectors whose cyclic subspaces for `π` are pairwise orthogonal. -/
def IsRepCyclicOrthogonal (s : Set H) : Prop :=
  s.Pairwise fun ψ φ => repCyclicSubmodule π ψ ⟂ repCyclicSubmodule π φ

/-- **A cyclic decomposition** of `H` for the representation `π`: vectors with pairwise
orthogonal cyclic subspaces such that only `0` is orthogonal to all of them (Reed–Simon I,
§VII.2, Lemma 2, p. 226, for a representation). -/
structure RepDecomposition where
  /-- The generating vectors. -/
  vectors : Set H
  /-- The cyclic subspaces are pairwise orthogonal. -/
  pairwise : IsRepCyclicOrthogonal π vectors
  /-- The cyclic subspaces are total: only `0` is orthogonal to all of them. -/
  total : ∀ v : H, (∀ ψ ∈ vectors, v ∈ (repCyclicSubmodule π ψ)ᗮ) → v = 0

/-- **Existence of a cyclic decomposition**, by Zorn's lemma. -/
theorem RepDecomposition.nonempty : Nonempty (RepDecomposition π) := by
  obtain ⟨s, hs⟩ := zorn_subset {s : Set H | IsRepCyclicOrthogonal π s} fun c hc hchain => by
    refine ⟨⋃₀ c, fun ψ hψ φ hφ hne => ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    obtain ⟨a, ha, hψa⟩ := Set.mem_sUnion.mp hψ
    obtain ⟨b, hb, hφb⟩ := Set.mem_sUnion.mp hφ
    rcases hchain.total ha hb with hab | hba
    · exact hc hb (hab hψa) hφb hne
    · exact hc ha hψa (hba hφb) hne
  refine ⟨⟨s, hs.prop, fun v hv => ?_⟩⟩
  have hins : IsRepCyclicOrthogonal π (insert v s) := by
    refine hs.prop.insert fun ψ hψ _ => ⟨?_, ?_⟩
    · exact repCyclicSubmodule_isOrtho π (hv ψ hψ)
    · exact (repCyclicSubmodule_isOrtho π (hv ψ hψ)).symm
  have hvs : v ∈ s := hs.eq_of_subset hins (Set.subset_insert v s) ▸ Set.mem_insert v s
  have hvv := hv v hvs
  have hself := mem_repCyclicSubmodule_self π v
  exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal' _ _).mp hvv v hself)

/-! ### Rescaling cyclic vectors -/

/-- Rescaling does not change the cyclic subspace: `H_{c ψ} = H_ψ` for `c ≠ 0`. -/
theorem repCyclicSubmodule_smul {c : ℂ} (hc : c ≠ 0) (ψ : H) :
    repCyclicSubmodule π (c • ψ) = repCyclicSubmodule π ψ := by
  refine le_antisymm (repCyclicSubmodule_le_repCyclicSubmodule π
    (Submodule.smul_mem _ c (mem_repCyclicSubmodule_self π ψ))) ?_
  refine repCyclicSubmodule_le_repCyclicSubmodule π ?_
  have h := Submodule.smul_mem (repCyclicSubmodule π (c • ψ)) c⁻¹
    (mem_repCyclicSubmodule_self π (c • ψ))
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

/-- The cyclic subspace of `0` is `0`. -/
theorem repCyclicSubmodule_zero : repCyclicSubmodule π (0 : H) = ⊥ :=
  le_bot_iff.mp (repCyclicSubmodule_le π (by rw [Submodule.bot_coe]; exact isClosed_singleton)
    fun f => by simp)

namespace RepDecomposition

variable {π}
variable (D : RepDecomposition π)

/-! ### Countability and rescaling of a cyclic decomposition -/

/-- Distinct vectors of a cyclic decomposition are orthogonal, since each lies in its own cyclic
subspace. -/
theorem inner_eq_zero {ψ φ : H} (hψ : ψ ∈ D.vectors) (hφ : φ ∈ D.vectors) (hne : ψ ≠ φ) :
    ⟪ψ, φ⟫_ℂ = 0 :=
  (D.pairwise hψ hφ hne).inner_eq (mem_repCyclicSubmodule_self π ψ)
    (mem_repCyclicSubmodule_self π φ)

/-- The nonzero vectors of a cyclic decomposition. -/
def nonzeroVectors : Set H :=
  {ψ ∈ D.vectors | ψ ≠ 0}

/-- In a separable space the nonzero vectors of a cyclic decomposition form a countable set:
they are nonzero and pairwise orthogonal. -/
theorem countable_nonzeroVectors [TopologicalSpace.SeparableSpace H] :
    D.nonzeroVectors.Countable :=
  countable_of_pairwise_inner_eq_zero (fun h => h.2 rfl)
    fun _ hψ _ hφ hne => D.inner_eq_zero hψ.1 hφ.1 hne

/-- In a separable space a cyclic decomposition has countably many vectors (Reed–Simon I,
§VII.2, Lemma 2, p. 226, for a representation). -/
theorem countable_vectors [TopologicalSpace.SeparableSpace H] : D.vectors.Countable :=
  (D.countable_nonzeroVectors.insert 0).mono fun ψ hψ => by
    by_cases h : ψ = 0
    · exact Or.inl h
    · exact Or.inr ⟨hψ, h⟩

section Rescale

variable (c : D.nonzeroVectors → ℂ)

/-- Rescaling the nonzero vectors of a cyclic decomposition is injective: distinct nonzero
vectors are orthogonal, and so are their nonzero multiples. -/
theorem injective_rescale (hc : ∀ ψ, c ψ ≠ 0) :
    Function.Injective fun ψ : D.nonzeroVectors => c ψ • (ψ : H) := by
  intro ψ φ h
  simp only at h
  by_contra hne
  have hne' : (ψ : H) ≠ φ := fun h' => hne (Subtype.ext h')
  have hin : ⟪c ψ • (ψ : H), c φ • (φ : H)⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, D.inner_eq_zero ψ.2.1 φ.2.1 hne', mul_zero,
      mul_zero]
  rw [← h, inner_self_eq_zero, smul_eq_zero] at hin
  exact hin.elim (hc ψ) ψ.2.2

/-- **Rescaling a cyclic decomposition**: the vectors `c ψ • ψ` for the nonzero vectors `ψ` of
`D` and nonzero scalars `c ψ` form a cyclic decomposition.  The cyclic subspaces do not change
(`repCyclicSubmodule_smul`), and dropping `0` loses nothing because its cyclic subspace is `0`. -/
def rescale (hc : ∀ ψ, c ψ ≠ 0) : RepDecomposition π where
  vectors := Set.range fun ψ : D.nonzeroVectors => c ψ • (ψ : H)
  pairwise := by
    rintro _ ⟨ψ, rfl⟩ _ ⟨φ, rfl⟩ hne
    have hne' : (ψ : H) ≠ φ := fun h => hne (by rw [Subtype.ext h])
    rw [repCyclicSubmodule_smul π (hc ψ), repCyclicSubmodule_smul π (hc φ)]
    exact D.pairwise ψ.2.1 φ.2.1 hne'
  total v hv := by
    refine D.total v fun ψ hψ => ?_
    by_cases h0 : ψ = 0
    · rw [h0, repCyclicSubmodule_zero, Submodule.bot_orthogonal_eq_top]
      exact Submodule.mem_top
    · have h := hv _ ⟨⟨ψ, hψ, h0⟩, rfl⟩
      rwa [repCyclicSubmodule_smul π (hc _)] at h

end Rescale

/-! ### The Hilbert sum -/

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The spaces `L²(X, μ_ψ)` of a cyclic decomposition. -/
abbrev Summand (ψ : D.vectors) : Type u :=
  Lp ℂ 2 (repMeasure π (ψ : H))

/-- The cyclic isometries `L²(X, μ_ψ) → H` of a decomposition form an orthogonal family. -/
theorem orthogonalFamily :
    OrthogonalFamily ℂ D.Summand fun ψ => repCyclicIsometry π (ψ : H) := by
  intro ψ φ hne x y
  exact (D.pairwise ψ.2 φ.2 fun h => hne (Subtype.ext h)).inner_eq
    (repCyclicIsometry_mem π _ x) (repCyclicIsometry_mem π _ y)

/-- **`H` is the Hilbert sum of the spaces `L²(X, μ_ψ)`** of a cyclic decomposition. -/
theorem isHilbertSum : IsHilbertSum ℂ D.Summand fun ψ => repCyclicIsometry π (ψ : H) := by
  refine IsHilbertSum.mk D.orthogonalFamily ?_
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  refine D.total v fun ψ hψ => ?_
  rw [← range_repCyclicIsometry]
  refine (Submodule.mem_orthogonal _ v).mpr fun u hu => ?_
  exact (Submodule.mem_orthogonal _ v).mp hv u
    (Submodule.mem_iSup_of_mem (⟨ψ, hψ⟩ : D.vectors) hu)

/-- **The unitary `H ≃ ⊕̂_ψ L²(X, μ_ψ)`** of a cyclic decomposition. -/
def equiv : H ≃ₗᵢ[ℂ] lp D.Summand 2 :=
  D.isHilbertSum.linearIsometryEquiv

open scoped Classical in
/-- The inverse unitary sends a single component `φ ∈ L²(X, μ_ψ)` to `U_ψ φ ∈ H`. -/
theorem equiv_symm_single (ψ : D.vectors) (φ : D.Summand ψ) :
    D.equiv.symm (lp.single 2 ψ φ) = repCyclicIsometry π (ψ : H) φ :=
  D.isHilbertSum.linearIsometryEquiv_symm_apply_single φ

/-! ### The multiplication operator form -/

/-- The measure space `Σ_ψ X` of the multiplication operator form. -/
abbrev Space : Type u :=
  Σ _ψ : D.vectors, X

/-- The measure `Σ_ψ μ_ψ` on `Σ_ψ X`. -/
abbrev measure : Measure D.Space :=
  sigmaMeasure fun ψ : D.vectors => repMeasure π (ψ : H)

/-- The projection `(ψ, x) ↦ x` of `Σ_ψ X` onto `X`. -/
def point (p : D.Space) : X :=
  p.2

omit [CompactSpace X] [T2Space X] [BorelSpace X] in
/-- The projection `(ψ, x) ↦ x` is measurable. -/
theorem measurable_point : Measurable D.point :=
  measurable_sigma_iff.mpr fun _ => measurable_id

/-- **The multiplication operator form** `U : H ≃ L²(Σ_ψ X, Σ_ψ μ_ψ)` of the representation. -/
def unitary : H ≃ₗᵢ[ℂ] Lp ℂ 2 D.measure :=
  D.equiv.trans (sigmaL2Equiv fun ψ : D.vectors => repMeasure π (ψ : H)).symm

/-- A continuous function of the point of `X`, `(ψ, x) ↦ g(x)`, is in `L^∞`. -/
theorem memLp_top_continuousMap (g : C(X, ℂ)) :
    MemLp (fun p : D.Space => g p.2) ∞ D.measure :=
  memLp_top_of_bound
    (measurable_sigma_iff.mpr fun _ => g.continuous.measurable).aestronglyMeasurable ‖g‖
    (Filter.Eventually.of_forall fun p => g.norm_coe_le_norm p.2)

open scoped Classical in
/-- `U (U_ψ φ)` is the element of `L²(Σ_ψ X)` supported on the `ψ`-th copy of `X`, where it is
`φ`. -/
theorem unitary_repCyclicIsometry (ψ : D.vectors) (φ : D.Summand ψ) :
    D.unitary (repCyclicIsometry π (ψ : H) φ) =
      (sigmaL2Equiv fun ψ : D.vectors => repMeasure π (ψ : H)).symm (lp.single 2 ψ φ) := by
  rw [unitary, LinearIsometryEquiv.trans_apply, ← D.equiv_symm_single,
    LinearIsometryEquiv.apply_symm_apply]

open scoped Classical in
/-- `U (π(g) h) = g(x) · U h` for `h` in a single cyclic subspace, `h = U_ψ φ`: by
`repCyclicIsometry_smul`, `π(g) U_ψ φ = U_ψ (g φ)`, and both sides are supported on the `ψ`-th
copy of `X`, where they are `g φ`. -/
theorem unitary_rep_repCyclicIsometry (g : C(X, ℂ)) (ψ : D.vectors) (φ : D.Summand ψ) :
    D.unitary (π g (repCyclicIsometry π (ψ : H) φ)) =
      mulL (fun p : D.Space => g p.2) (D.memLp_top_continuousMap g)
        (D.unitary (repCyclicIsometry π (ψ : H) φ)) := by
  set σE := sigmaL2Equiv fun ψ : D.vectors => repMeasure π (ψ : H) with hσE
  rw [← repCyclicIsometry_smul, D.unitary_repCyclicIsometry, D.unitary_repCyclicIsometry]
  apply σE.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  refine lp.ext (funext fun j => Lp.ext ?_)
  have hmul := sigmaL2Equiv_mul_ae_eq (fun ψ : D.vectors => repMeasure π (ψ : H))
    (memLp_two_mul (D.memLp_top_continuousMap g) (σE.symm (lp.single 2 ψ φ))) j
  rw [← mulL_apply (D.memLp_top_continuousMap g), LinearIsometryEquiv.apply_symm_apply] at hmul
  refine EventuallyEq.trans ?_ hmul.symm
  by_cases hj : j = ψ
  · subst hj
    rw [lp.single_apply_self, lp.single_apply_self, toLp_top_smul_eq_toLp]
    exact MemLp.coeFn_toLp _
  · rw [lp.single_apply_ne 2 ψ _ hj, lp.single_apply_ne 2 ψ _ hj]
    filter_upwards [Lp.coeFn_zero ℂ 2 (repMeasure π (j : H))] with x hx
    rw [hx]
    simp

/-- **`U π(g) U⁻¹` is multiplication by `g(x)`** for continuous `g : X → ℂ`: the identity holds
on each cyclic summand (`unitary_rep_repCyclicIsometry`), and both sides are continuous and
linear in `h`, so it holds on the Hilbert sum. -/
theorem unitary_apply (g : C(X, ℂ)) (h : H) :
    D.unitary (π g h) =
      mulL (fun p : D.Space => g p.2) (D.memLp_top_continuousMap g) (D.unitary h) := by
  classical
  obtain ⟨w, rfl⟩ := D.equiv.symm.surjective h
  let L₁ : lp D.Summand 2 →L[ℂ] Lp ℂ 2 D.measure :=
    D.unitary.toLinearIsometry.toContinuousLinearMap ∘L π g ∘L
      D.equiv.symm.toLinearIsometry.toContinuousLinearMap
  let L₂ : lp D.Summand 2 →L[ℂ] Lp ℂ 2 D.measure :=
    mulL (fun p : D.Space => g p.2) (D.memLp_top_continuousMap g) ∘L
      D.unitary.toLinearIsometry.toContinuousLinearMap ∘L
        D.equiv.symm.toLinearIsometry.toContinuousLinearMap
  change L₁ w = L₂ w
  have hsum := lp.hasSum_single (E := D.Summand) (p := 2) ENNReal.ofNat_ne_top w
  refine (hsum.mapL L₁).unique ?_
  convert hsum.mapL L₂ using 1
  funext ψ
  simp only [L₁, L₂, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    D.equiv_symm_single]
  exact D.unitary_rep_repCyclicIsometry g ψ (w ψ)

/-- **`U π(g) U⁻¹` is multiplication by `g(x)`**, almost everywhere form:
`(U (π(g) h))(ψ, x) = g(x) (U h)(ψ, x)` for almost every `(ψ, x)`. -/
theorem coeFn_unitary_apply (g : C(X, ℂ)) (h : H) :
    (D.unitary (π g h) : D.Space → ℂ) =ᵐ[D.measure]
      fun p => g (D.point p) * D.unitary h p := by
  rw [D.unitary_apply]
  exact coeFn_mulL _ _

/-- The total mass of the measure `Σ_ψ μ_ψ` of a cyclic decomposition is `Σ_ψ ‖ψ‖²`, since
`μ_ψ(X) = ‖ψ‖²`. -/
theorem measure_univ_eq :
    D.measure Set.univ =
      ∑' ψ : D.vectors, ENNReal.ofReal (‖(ψ : H)‖ ^ 2) := by -- totalisation-audit: allow ℝ≥0∞ sum
  rw [sigmaMeasure_apply]
  simp only [Set.preimage_univ, repMeasure_univ]

/-- The total mass of the measure of a rescaled decomposition is `Σ_ψ ‖c ψ • ψ‖²`. -/
theorem rescale_measure_univ (c : D.nonzeroVectors → ℂ) (hc : ∀ ψ, c ψ ≠ 0) :
    (D.rescale c hc).measure Set.univ =
      ∑' ψ : D.nonzeroVectors, -- totalisation-audit: allow ℝ≥0∞ sum
        ENNReal.ofReal (‖c ψ • (ψ : H)‖ ^ 2) := by
  rw [measure_univ_eq]
  exact tsum_range (fun x : H => ENNReal.ofReal (‖x‖ ^ 2)) (D.injective_rescale c hc)

end RepDecomposition

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- **Multiplication operator form of a representation of `C(X)`** (Reed–Simon I, Theorem VII.3
and its Corollary, p. 227, for a representation in place of the functional calculus of one
operator): there are a measure space `(M, μ)`, a unitary `U : H ≃ L²(M, μ)` and a measurable
`F : M → X` such that `U π(g) U⁻¹` is multiplication by `g ∘ F` for every continuous
`g : X → ℂ`, `(U π(g) U⁻¹ f)(m) = g(F(m)) f(m)`. -/
theorem exists_unitary_mulL_rep :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
      (F : M → X) (_ : Measurable F),
      ∀ g : C(X, ℂ), ∃ hg : MemLp (fun m => g (F m)) ∞ μ,
        ∀ h : H, U (π g h) = mulL (fun m => g (F m)) hg (U h) := by
  obtain ⟨D⟩ := RepDecomposition.nonempty π
  exact ⟨D.Space, inferInstance, D.measure, D.unitary, D.point, D.measurable_point,
    fun g => ⟨D.memLp_top_continuousMap g, D.unitary_apply g⟩⟩

/-! ### A finite measure for separable `H` -/

section Finite

variable [TopologicalSpace.SeparableSpace H]

/-- **A cyclic decomposition with a finite measure** for separable `H` (Reed–Simon I, proof of
the Corollary to Theorem VII.3, p. 227: "Choose the cyclic vectors `φₙ` so that `‖φₙ‖ = 2⁻ⁿ`").
The nonzero vectors of any cyclic decomposition are countable; enumerating them injectively and
rescaling the `n`-th one to norm `2⁻ⁿ` gives a decomposition whose measure has total mass
`Σ_ψ ‖ψ‖² ≤ Σₙ 4⁻ⁿ < ∞`. -/
theorem RepDecomposition.exists_isFiniteMeasure :
    ∃ D : RepDecomposition π, IsFiniteMeasure D.measure := by
  obtain ⟨D⟩ := RepDecomposition.nonempty π
  let _ : Encodable D.nonzeroVectors := D.countable_nonzeroVectors.toEncodable
  obtain ⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ENNReal.ofReal r = 2⁻¹ :=
    ⟨2⁻¹, by norm_num, by norm_num, by -- totalisation-audit: allow inverse of 2 ≠ 0
      rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]⟩
  have hpos : ∀ ψ : D.nonzeroVectors, 0 < ‖(ψ : H)‖ := fun ψ => norm_pos_iff.mpr ψ.2.2
  set c : D.nonzeroVectors → ℂ := fun ψ =>
    ((r ^ Encodable.encode ψ / ‖(ψ : H)‖ : ℝ) : ℂ) with hc_def -- totalisation-audit: allow ‖ψ‖ > 0
  have hc : ∀ ψ, c ψ ≠ 0 := fun ψ =>
    Complex.ofReal_ne_zero.mpr (div_ne_zero (pow_ne_zero _ hr0.ne') (hpos ψ).ne')
  have hnorm : ∀ ψ, ‖c ψ • (ψ : H)‖ = r ^ Encodable.encode ψ := fun ψ => by
    rw [norm_smul, hc_def, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ (hpos ψ).ne']
  refine ⟨D.rescale c hc, ⟨?_⟩⟩
  rw [D.rescale_measure_univ c hc]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun ψ => ?_)
    (lt_of_le_of_lt ENNReal.tsum_geometric_two_encode_le_two ENNReal.ofNat_lt_top)
  rw [hnorm, ← hr, ← ENNReal.ofReal_pow hr0.le]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_of_le_one (by positivity) (pow_le_one₀ hr0.le hr1) two_ne_zero)

/-- **Multiplication operator form of a representation of `C(X)` on a separable space, with a
finite measure** (Reed–Simon I, Theorem VII.3 and its Corollary, p. 227, for a representation):
`exists_unitary_mulL_rep` with, in addition, `μ` finite. -/
theorem exists_unitary_mulL_rep_finite :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (_ : IsFiniteMeasure μ)
      (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (F : M → X) (_ : Measurable F),
      ∀ g : C(X, ℂ), ∃ hg : MemLp (fun m => g (F m)) ∞ μ,
        ∀ h : H, U (π g h) = mulL (fun m => g (F m)) hg (U h) := by
  obtain ⟨D, hD⟩ := RepDecomposition.exists_isFiniteMeasure π
  exact ⟨D.Space, inferInstance, D.measure, hD, D.unitary, D.point, D.measurable_point,
    fun g => ⟨D.memLp_top_continuousMap g, D.unitary_apply g⟩⟩

end Finite

end SpectralTheorem
