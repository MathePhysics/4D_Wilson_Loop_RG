import KatoRellich.Theorem

/-!
# Cores: essential self-adjointness of `A + B`

Reed–Simon II, Theorem X.12, p. 162, also asserts that `A + B` is essentially self-adjoint on any
core of `A`.  Their proof (p. 163) is one line: by (X.19), the closure of `(A + B) ↾ D₀` contains
`(A + B) ↾ D(A ↾ D₀)‾`.  Concretely, if `x_n ∈ D₀` with `x_n → x` and `A x_n → A x`, then
`B x_n → B x`, since `‖B (x_n - x)‖ ≤ a ‖A (x_n - x)‖ + b ‖x_n - x‖`.

Reed–Simon I, §VIII.2, p. 256: a symmetric operator `T` is essentially self-adjoint if its closure
is self-adjoint; `D ⊆ D(T)` is a core for a closed `T` if the closure of `T ↾ D` is `T`
(mathlib's `LinearPMap.HasCore`).

## Main results

* `KatoRellich.hasCore_add`: if `B` is `A`-bounded, `A` and `A + B` are closed, and `D₀` is a
  core for `A`, then `D₀` is a core for `A + B`.
* `KatoRellich.IsEssentiallySelfAdjoint`: symmetric with self-adjoint closure.
* `KatoRellich.isEssentiallySelfAdjoint_add`,
  `KatoRellich.isEssentiallySelfAdjoint_add_of_isBoundedBelow`: `A + B` is essentially
  self-adjoint on every core of `A`, under the hypotheses of the two forms of Kato–Rellich.
-/

noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace KatoRellich

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Essentially self-adjoint** (Reed–Simon I, §VIII.2, p. 256): symmetric, with self-adjoint
closure. -/
def IsEssentiallySelfAdjoint [CompleteSpace E] (T : E →ₗ.[𝕜] E) : Prop :=
  IsSymmetric T ∧ IsSelfAdjoint T.closure

/-- The closure of a closed operator is itself. -/
theorem closure_eq_self {T : E →ₗ.[𝕜] E} (hT : T.IsClosed) : T.closure = T :=
  LinearPMap.eq_of_eq_graph
    ((hT.isClosable.graph_closure_eq_closure_graph).symm.trans
      hT.submodule_topologicalClosure_eq)

/-- If `D₀` is a core for a closed `A`, every point of the graph of `A` is a limit of points of
the graph of `A ↾ D₀`. -/
theorem mem_closure_graph_domRestrict {A : E →ₗ.[𝕜] E} (hA : A.IsClosed) {D₀ : Submodule 𝕜 E}
    (hcore : A.HasCore D₀) (x : A.domain) :
    ((x : E), A x) ∈ closure ((A.domRestrict D₀).graph : Set (E × E)) := by
  have hcl : (A.domRestrict D₀).IsClosable :=
    hA.isClosable.leIsClosable LinearPMap.domRestrict_le
  rw [← Submodule.topologicalClosure_coe, hcl.graph_closure_eq_closure_graph,
    hcore.closure_eq]
  exact (LinearPMap.mem_graph_iff A).mpr ⟨x, rfl, rfl⟩

/-- **Cores are preserved by relatively bounded perturbations**: if `B` is `A`-bounded, `A` and
`A + B` are closed, and `D₀` is a core for `A`, then `D₀` is a core for `A + B`
(Reed–Simon II, proof of Theorem X.12, p. 163). -/
theorem hasCore_add {A B : E →ₗ.[𝕜] E} {a b : ℝ} (hAB : IsRelBounded B A a b)
    (hA : A.IsClosed) (hsum : (A + B).IsClosed) {D₀ : Submodule 𝕜 E} (hcore : A.HasCore D₀) :
    (A + B).HasCore D₀ := by
  have hle : D₀ ≤ (A + B).domain := fun x hx =>
    ⟨hcore.le_domain hx, hAB.domain_le (hcore.le_domain hx)⟩
  refine ⟨hle, ?_⟩
  set C := (A + B).domRestrict D₀ with hC_def
  have hCle : C ≤ A + B := LinearPMap.domRestrict_le
  have hCcl : C.IsClosable := hsum.isClosable.leIsClosable hCle
  apply le_antisymm
  · have h := hsum.isClosable.closure_mono hCle
    rwa [closure_eq_self hsum] at h
  refine LinearPMap.le_of_le_graph ?_
  rw [← hCcl.graph_closure_eq_closure_graph]
  intro p hp
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).mp hp
  let xA : A.domain := ⟨x, x.2.1⟩
  have hmem := mem_closure_graph_domRestrict hA hcore xA
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose y hy1 hy2 using fun n => (LinearPMap.mem_graph_iff _).mp (hu n)
  have hymem : ∀ n, (y n : E) ∈ D₀ ⊓ A.domain := fun n => (y n).2
  -- The approximating points of the graph of `A ↾ D₀`, viewed in `D(A)`.
  let yA : ℕ → A.domain := fun n => ⟨y n, (Submodule.mem_inf.mp (hymem n)).2⟩
  have hyA : ∀ n, A (yA n) = (u n).2 := fun n => by
    rw [← hy2 n]
    exact (LinearPMap.domRestrict_apply (f := A) (x := y n) (y := yA n) rfl).symm
  have hfst : Tendsto (fun n => (yA n : E)) atTop (𝓝 (x : E)) := by
    have := (continuous_fst.tendsto _).comp hlim
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    exact (hy1 n).symm
  have hA' : Tendsto (fun n => A (yA n)) atTop (𝓝 (A xA)) := by
    have := (continuous_snd.tendsto _).comp hlim
    exact this.congr fun n => (hyA n).symm
  -- `B y_n → B x`, by the relative bound.
  have hB' : Tendsto (fun n => B ⟨yA n, hAB.domain_le (yA n).2⟩) atTop
      (𝓝 (B ⟨xA, hAB.domain_le xA.2⟩)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsub : ∀ n, B ⟨yA n, hAB.domain_le (yA n).2⟩ - B ⟨xA, hAB.domain_le xA.2⟩ =
        B ⟨(yA n - xA : A.domain), hAB.domain_le (yA n - xA).2⟩ := fun n => by
      rw [← LinearPMap.map_sub]
      rfl
    have hAsub : ∀ n, A (yA n - xA) = A (yA n) - A xA := fun n => LinearPMap.map_sub A _ _
    have hbound : ∀ n, ‖B ⟨yA n, hAB.domain_le (yA n).2⟩ - B ⟨xA, hAB.domain_le xA.2⟩‖ ≤
        a * ‖A (yA n) - A xA‖ + b * ‖(yA n : E) - (xA : E)‖ := fun n => by
      rw [hsub n, ← hAsub n]
      exact hAB.bound (yA n - xA)
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hA').const_mul a
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp hfst).const_mul b
    simpa using h1.add h2
  -- The points `(y_n, (A + B) y_n)` of the graph of `C` converge to `(x, (A + B) x)`.
  have hmemC : ∀ n, ((yA n : E), A (yA n) + B ⟨yA n, hAB.domain_le (yA n).2⟩) ∈
      (C.graph : Set (E × E)) := fun n => by
    have hD : (yA n : E) ∈ D₀ := (Submodule.mem_inf.mp (hymem n)).1
    have hCdom : (yA n : E) ∈ C.domain := by
      rw [hC_def, LinearPMap.domRestrict_domain]
      exact Submodule.mem_inf.mpr ⟨hD, hle hD⟩
    refine (LinearPMap.mem_graph_iff C).mpr ⟨⟨yA n, hCdom⟩, rfl, ?_⟩
    exact LinearPMap.domRestrict_apply (f := A + B) (x := ⟨yA n, hCdom⟩)
      (y := ⟨yA n, hle hD⟩) rfl
  have hlimC := hfst.prodMk_nhds (hA'.add hB')
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  have hp' : p = ((xA : E), A xA + B ⟨xA, hAB.domain_le xA.2⟩) :=
    Prod.ext hx1.symm hx2.symm
  rw [hp']
  exact mem_closure_of_tendsto hlimC (Eventually.of_forall hmemC)

/-- A core of a closed, densely defined operator is dense. -/
theorem dense_of_hasCore {A : E →ₗ.[𝕜] E} (hA : A.IsClosed) (hdense : Dense (A.domain : Set E))
    {D₀ : Submodule 𝕜 E} (hcore : A.HasCore D₀) : Dense (D₀ : Set E) := by
  have hsub : (A.domain : Set E) ⊆ closure (D₀ : Set E) := fun x hx => by
    have h := mem_closure_graph_domRestrict hA hcore ⟨x, hx⟩
    refine map_mem_closure continuous_fst h fun p hp => ?_
    obtain ⟨y, hy, -⟩ := (LinearPMap.mem_graph_iff _).mp hp
    rw [← hy]
    exact (Submodule.mem_inf.mp y.2).1
  exact dense_closure.mp (hdense.mono hsub)

/-- **The restriction of a self-adjoint operator to a core is essentially self-adjoint.** -/
theorem isEssentiallySelfAdjoint_domRestrict [CompleteSpace E] {T : E →ₗ.[𝕜] E}
    (hT : IsSelfAdjoint T) {D₀ : Submodule 𝕜 E} (hcore : T.HasCore D₀) :
    IsEssentiallySelfAdjoint (T.domRestrict D₀) := by
  have hsymm := IsSymmetric.of_isSelfAdjoint hT
  refine ⟨⟨?_, fun x y => ?_⟩, ?_⟩
  · rw [LinearPMap.domRestrict_domain, inf_eq_left.mpr hcore.le_domain]
    exact dense_of_hasCore hT.isClosed hT.dense_domain hcore
  · have hx := LinearPMap.domRestrict_apply (f := T) (x := x)
      (y := ⟨x, (Submodule.mem_inf.mp x.2).2⟩) rfl
    have hy := LinearPMap.domRestrict_apply (f := T) (x := y)
      (y := ⟨y, (Submodule.mem_inf.mp y.2).2⟩) rfl
    rw [hx, hy]
    exact hsymm.isFormalAdjoint ⟨x, (Submodule.mem_inf.mp x.2).2⟩
      ⟨y, (Submodule.mem_inf.mp y.2).2⟩
  · rw [hcore.closure_eq]
    exact hT

/-- **Kato–Rellich, essential self-adjointness on cores** (Reed–Simon II, Theorem X.12, p. 162):
under the hypotheses of `KatoRellich.isSelfAdjoint_add`, `A + B` is essentially self-adjoint on
any core `D₀` of `A`, and `D₀` is a core for `A + B`. -/
theorem isEssentiallySelfAdjoint_add [CompleteSpace E] (hI : (RCLike.I : 𝕜) ≠ 0)
    {A B : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) (hB : B.IsFormalAdjoint B) {a b : ℝ}
    (hAB : IsRelBounded B A a b) (ha : a < 1) {D₀ : Submodule 𝕜 E} (hcore : A.HasCore D₀) :
    IsEssentiallySelfAdjoint ((A + B).domRestrict D₀) ∧ (A + B).HasCore D₀ := by
  have hsa := (isSelfAdjoint_add hI hA hB hAB ha).1
  have hcore' := hasCore_add hAB hA.isClosed hsa.isClosed hcore
  exact ⟨isEssentiallySelfAdjoint_domRestrict hsa hcore', hcore'⟩

/-- **Kato–Rellich for `A` bounded below, essential self-adjointness on cores**: under the
hypotheses of `KatoRellich.isSelfAdjoint_add_of_isBoundedBelow`, `A + B` is essentially
self-adjoint on any core `D₀` of `A`, and `D₀` is a core for `A + B`. -/
theorem isEssentiallySelfAdjoint_add_of_isBoundedBelow [CompleteSpace E] {A B : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) {M : ℝ} (hM : IsBoundedBelow A M) (hB : B.IsFormalAdjoint B)
    {a b : ℝ} (hAB : IsRelBounded B A a b) (ha : a < 1) {D₀ : Submodule 𝕜 E}
    (hcore : A.HasCore D₀) :
    IsEssentiallySelfAdjoint ((A + B).domRestrict D₀) ∧ (A + B).HasCore D₀ := by
  have hsa := (isSelfAdjoint_add_of_isBoundedBelow hA hM hB hAB ha).1
  have hcore' := hasCore_add hAB hA.isClosed hsa.isClosed hcore
  exact ⟨isEssentiallySelfAdjoint_domRestrict hsa hcore', hcore'⟩

end KatoRellich
