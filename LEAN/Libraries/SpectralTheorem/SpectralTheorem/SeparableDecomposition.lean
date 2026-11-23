import SpectralTheorem.UnboundedMultiplicationForm

/-!
# The spectral theorem on a separable space: a finite measure

Reed–Simon I, Theorem VII.3 and its Corollary (p. 227) and Theorem VIII.4 (pp. 260–261) assume
`H` separable and give a *finite* measure space.  Their proof of the Corollary: "Choose the
cyclic vectors `φₙ` so that `‖φₙ‖ = 2⁻ⁿ`"; then `μ(M) = Σₙ μₙ(ℝ) < ∞`.

In `SpectralTheorem.MultiplicationForm` a cyclic decomposition `D` of a bounded normal `T` has an
arbitrary set of vectors, and its measure `Σ_ψ μ_ψ` on `Σ_ψ σ(T)` has total mass `Σ_ψ ‖ψ‖²`
(because `μ_ψ(σ(T)) = ‖ψ‖²`), which need not be finite.  For separable `H` we make it finite:

* distinct vectors of `D` are orthogonal (each lies in its own cyclic subspace), so the nonzero
  ones are countable (`countable_of_pairwise_inner_eq_zero`: for nonzero orthogonal `x`, the
  open balls `B(x, ‖x‖ / 2)` are pairwise disjoint);
* rescaling a vector by `c ≠ 0` does not change its cyclic subspace (`cyclicSubmodule_smul`) and
  the cyclic subspace of `0` is `0`, so the rescaled nonzero vectors `c ψ • ψ` again form a cyclic
  decomposition (`CyclicDecomposition.rescale`);
* enumerating the nonzero vectors injectively by `n ∈ ℕ` and giving the `n`-th one norm `2⁻ⁿ`
  makes the total mass at most `Σₙ 2⁻ⁿ = 2`.

Applied to `T` and to `(A + i)⁻¹` this gives Theorems VII.3 and VIII.4 with a finite measure.

## Main results

* `SpectralTheorem.cyclicSubmodule_smul`: `H_{cψ} = H_ψ` for `c ≠ 0`.
* `SpectralTheorem.CyclicDecomposition.countable_vectors`: in a separable space a cyclic
  decomposition has countably many vectors.
* `SpectralTheorem.CyclicDecomposition.measure_univ_eq`: the total mass of `Σ_ψ μ_ψ` is
  `Σ_ψ ‖ψ‖²`.
* `SpectralTheorem.CyclicDecomposition.exists_isFiniteMeasure`: for separable `H` there is a
  cyclic decomposition with a finite measure.
* `SpectralTheorem.exists_unitary_mulL_finite`: **Reed–Simon I, Theorem VII.3** and its
  Corollary with a finite measure, for bounded normal `T`.
* `SpectralTheorem.exists_unitary_mulPMap_finite`: **Reed–Simon I, Theorem VIII.4** as stated
  there, with a finite measure.
-/

noncomputable section

open scoped InnerProductSpace ENNReal
open MeasureTheory

namespace SpectralTheorem

universe u

/-! ### Orthogonal sets in a separable space -/

/-- In a separable complex inner product space, a set of nonzero, pairwise orthogonal vectors is
countable: the open balls `B(x, ‖x‖ / 2)`, `x ∈ s`, are nonempty and pairwise disjoint, because
`‖x - y‖² = ‖x‖² + ‖y‖² ≥ (‖x‖ / 2 + ‖y‖ / 2)²` for orthogonal `x`, `y`. -/
theorem countable_of_pairwise_inner_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [TopologicalSpace.SeparableSpace E] {s : Set E} (h0 : (0 : E) ∉ s)
    (hs : s.Pairwise fun x y => ⟪x, y⟫_ℂ = 0) : s.Countable := by
  refine Set.PairwiseDisjoint.countable_of_isOpen
    (s := fun x => Metric.ball x (‖x‖ / 2)) ?_ -- totalisation-audit: allow divisor 2 ≠ 0
    (fun _ _ => Metric.isOpen_ball) fun x hx => ⟨x, Metric.mem_ball_self ?_⟩
  · intro x hx y hy hxy
    refine Metric.ball_disjoint_ball ?_
    rw [dist_eq_norm]
    have h := @norm_sub_sq ℂ _ _ _ _ x y
    rw [hs hx hy hxy, map_zero, mul_zero, sub_zero] at h
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y, norm_nonneg (x - y)]
  · have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    have := norm_pos_iff.mpr hx0
    positivity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Rescaling cyclic vectors -/

section Cyclic

variable (T : H →L[ℂ] H) [hT : IsStarNormal T]

/-- Rescaling does not change the cyclic subspace: `H_{c ψ} = H_ψ` for `c ≠ 0`. -/
theorem cyclicSubmodule_smul {c : ℂ} (hc : c ≠ 0) (ψ : H) :
    cyclicSubmodule T (c • ψ) = cyclicSubmodule T ψ := by
  refine le_antisymm (cyclicSubmodule_le_cyclicSubmodule T
    (Submodule.smul_mem _ c (mem_cyclicSubmodule_self T ψ))) ?_
  refine cyclicSubmodule_le_cyclicSubmodule T ?_
  have h := Submodule.smul_mem (cyclicSubmodule T (c • ψ)) c⁻¹
    (mem_cyclicSubmodule_self T (c • ψ))
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

/-- The cyclic subspace of `0` is `0`. -/
theorem cyclicSubmodule_zero : cyclicSubmodule T (0 : H) = ⊥ :=
  le_bot_iff.mp (cyclicSubmodule_le T (by rw [Submodule.bot_coe]; exact isClosed_singleton)
    fun f => by simp)

end Cyclic

/-! ### Countability and rescaling of a cyclic decomposition -/

namespace CyclicDecomposition

variable {T : H →L[ℂ] H} [hT : IsStarNormal T] (D : CyclicDecomposition T)

/-- Distinct vectors of a cyclic decomposition are orthogonal, since each lies in its own cyclic
subspace. -/
theorem inner_eq_zero {ψ φ : H} (hψ : ψ ∈ D.vectors) (hφ : φ ∈ D.vectors) (hne : ψ ≠ φ) :
    ⟪ψ, φ⟫_ℂ = 0 :=
  (D.pairwise hψ hφ hne).inner_eq (mem_cyclicSubmodule_self T ψ) (mem_cyclicSubmodule_self T φ)

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
§VII.2, Lemma 2, p. 226). -/
theorem countable_vectors [TopologicalSpace.SeparableSpace H] : D.vectors.Countable :=
  (D.countable_nonzeroVectors.insert 0).mono fun ψ hψ => by
    by_cases h : ψ = 0
    · exact Or.inl h
    · exact Or.inr ⟨hψ, h⟩

/-- The total mass of the measure `Σ_ψ μ_ψ` of a cyclic decomposition is `Σ_ψ ‖ψ‖²`, since
`μ_ψ(σ(T)) = ‖ψ‖²`. -/
theorem measure_univ_eq :
    D.measure Set.univ =
      ∑' ψ : D.vectors, ENNReal.ofReal (‖(ψ : H)‖ ^ 2) := by -- totalisation-audit: allow ℝ≥0∞ sum
  rw [sigmaMeasure_apply]
  simp only [Set.preimage_univ, spectralMeasure_univ]

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
(`cyclicSubmodule_smul`), and dropping `0` loses nothing because its cyclic subspace is `0`. -/
def rescale (hc : ∀ ψ, c ψ ≠ 0) : CyclicDecomposition T where
  vectors := Set.range fun ψ : D.nonzeroVectors => c ψ • (ψ : H)
  pairwise := by
    rintro _ ⟨ψ, rfl⟩ _ ⟨φ, rfl⟩ hne
    have hne' : (ψ : H) ≠ φ := fun h => hne (by rw [Subtype.ext h])
    rw [cyclicSubmodule_smul T (hc ψ), cyclicSubmodule_smul T (hc φ)]
    exact D.pairwise ψ.2.1 φ.2.1 hne'
  total v hv := by
    refine D.total v fun ψ hψ => ?_
    by_cases h0 : ψ = 0
    · rw [h0, cyclicSubmodule_zero, Submodule.bot_orthogonal_eq_top]
      exact Submodule.mem_top
    · have h := hv _ ⟨⟨ψ, hψ, h0⟩, rfl⟩
      rwa [cyclicSubmodule_smul T (hc _)] at h

/-- The total mass of the measure of a rescaled decomposition is `Σ_ψ ‖c ψ • ψ‖²`. -/
theorem rescale_measure_univ (hc : ∀ ψ, c ψ ≠ 0) :
    (D.rescale c hc).measure Set.univ =
      ∑' ψ : D.nonzeroVectors, -- totalisation-audit: allow ℝ≥0∞ sum
        ENNReal.ofReal (‖c ψ • (ψ : H)‖ ^ 2) := by
  rw [measure_univ_eq]
  exact tsum_range (fun x : H => ENNReal.ofReal (‖x‖ ^ 2)) (D.injective_rescale c hc)

end Rescale

end CyclicDecomposition

/-! ### A finite measure -/

section Finite

variable [TopologicalSpace.SeparableSpace H] (T : H →L[ℂ] H) [hT : IsStarNormal T]

/-- **A cyclic decomposition with a finite measure** for separable `H` (Reed–Simon I, proof of
the Corollary to Theorem VII.3, p. 227: "Choose the cyclic vectors `φₙ` so that `‖φₙ‖ = 2⁻ⁿ`").
The nonzero vectors of any cyclic decomposition are countable; enumerating them injectively and
rescaling the `n`-th one to norm `2⁻ⁿ` gives a decomposition whose measure has total mass
`Σ_ψ ‖ψ‖² ≤ Σₙ 4⁻ⁿ < ∞`. -/
theorem CyclicDecomposition.exists_isFiniteMeasure :
    ∃ D : CyclicDecomposition T, IsFiniteMeasure D.measure := by
  obtain ⟨D⟩ := CyclicDecomposition.nonempty T
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

/-- **The spectral theorem for bounded normal operators on a separable space, multiplication
operator form, with a finite measure** (Reed–Simon I, Theorem VII.3 and its Corollary, p. 227;
normal case, Problem VII.5): `exists_unitary_mulL` with, in addition, `μ` finite.  There are a
finite measure space `(M, μ)`, a unitary `U : H ≃ L²(M, μ)` and a bounded measurable function `F`
on `M` such that `U T U⁻¹` is multiplication by `F`, and `U g(T) U⁻¹` is multiplication by `g ∘ F`
for every continuous `g` on `σ(T)`. -/
theorem exists_unitary_mulL_finite :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (_ : IsFiniteMeasure μ)
      (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (F : M → spectrum ℂ T) (_ : Measurable F),
      (∀ g : C(spectrum ℂ T, ℂ), ∃ hg : MemLp (fun m => g (F m)) ∞ μ,
        ∀ h : H, U (cfcHom hT g h) = mulL (fun m => g (F m)) hg (U h)) ∧
      ∃ hF : MemLp (fun m => (F m : ℂ)) ∞ μ,
        ∀ h : H, U (T h) = mulL (fun m => (F m : ℂ)) hF (U h) := by
  obtain ⟨D, hD⟩ := CyclicDecomposition.exists_isFiniteMeasure T
  exact ⟨D.Space, inferInstance, D.measure, hD, D.unitary, fun p => p.2,
    measurable_sigma_iff.mpr fun _ => measurable_id, fun g => ⟨D.memLp_top_continuousMap g,
      D.unitary_cfcHom g⟩, D.memLp_top_coord, D.unitary_apply_T⟩

end Finite

section Unbounded

open KatoRellich

variable [TopologicalSpace.SeparableSpace H] {A : H →ₗ.[ℂ] H}

/-- **The spectral theorem for unbounded self-adjoint operators, multiplication operator form**,
as stated by Reed–Simon (I, Theorem VIII.4, pp. 260–261): for a self-adjoint `A` on a separable
space there are a **finite** measure space `(M, μ)`, a unitary `U : H ≃ L²(M, μ)` and a real-valued
measurable function `f` on `M` such that (a) `ψ ∈ D(A) ↔ f · U ψ ∈ L²(M, μ)`, and (b)
`U (A ψ) = f · U ψ` for `ψ ∈ D(A)`.  This is `exists_unitary_mulPMap` for a cyclic decomposition
of `(A + i)⁻¹` with a finite measure (`CyclicDecomposition.exists_isFiniteMeasure`). -/
theorem exists_unitary_mulPMap_finite (hA : IsSelfAdjoint A) :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (_ : IsFiniteMeasure μ)
      (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (f : M → ℝ), Measurable f ∧
      (∀ ψ : H, ψ ∈ A.domain ↔ MemLp (fun m => (f m : ℂ) * U ψ m) 2 μ) ∧
      ∀ (ψ : H) (hψ : ψ ∈ A.domain),
        (U (A ⟨ψ, hψ⟩) : M → ℂ) =ᵐ[μ] fun m => (f m : ℂ) * U ψ m := by
  obtain ⟨D, hD⟩ := CyclicDecomposition.exists_isFiniteMeasure (resolvent hA)
  exact ⟨D.Space, inferInstance, D.measure, hD, D.unitary, D.realCoord, D.measurable_realCoord,
    D.mem_domain_iff, D.coeFn_unitary_selfAdjoint⟩

end Unbounded

end SpectralTheorem
