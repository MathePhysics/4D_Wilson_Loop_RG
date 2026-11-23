/-
`lem:contracted-geometry` of BALABAN_CORE.tex (`63991d7efeeb`), parts (i), (ii), (iv), (v), on one grid.

* `d_empty_eq_size`: for the grid of `CubeCountTorus.lean`, `d(X; ∅)` is the linear size of `lem:cube-count`.
* `contracted_ii`: `Σ_i d(Y_i; D ∩ Y_i) + 18#(Z \ ⋃_iY_i) ≥ d(Z; D)`, by the core's construction: the main diagonal of
  every cube of `Z \ ⋃_iY_i`, of length `2a`, with a segment of length `≤ 2a` from its end on each wall shared with a
  cube of `Z`, to a point of the family of the `Y_j` of that cube or to the centre of its diagonal.
* `contracted_i`: `Σ_{Y ∈ 𝐃} d(Y) ≥ d(Y₀; D) - 3(|𝐃| + n_D - 1)`, `n_D` the number of connected components of `D`.
* `contracted_iv`: `d(Z; D) ≤ Σ_i d(Z_i; D_i) + 3#(Z \ Z₀) + 3(n_∅ + n' - 1)`; stated for any grid (the core
  states it for the grid of side `LMa_k`), and without the core's hypothesis `n' ≥ 1`, which the proof does not use.
* `contracted_v`: `#(X) ≤ 81#(D) + 324 d(X; D)` for `D ≠ ∅`.

The proofs of (i) and (iv) are the core's: the pieces (the members of `𝐃` and the components of `D`; the families
for the `Z_i` with the `D_i`, and the cubes of `Z \ Z₀`) are joined along a spanning tree of their adjacency graph
by segments of a length of less than `3a` (`Grid.join_pieces`). The proof of (v) replaces the core's covering of the
strands by closed walks with a measure argument with the same counting (`mass`, `count_mass`): if `x ∈ G` is at a
distance `> r` from `D` and `G ∪ D` is connected, every value `ρ ∈ [0, r]` is the distance from `x` of a point of `G`
(otherwise `{dist(·, x) < ρ}` and `{dist(·, x) > ρ}` would separate `G ∪ D`), so that the part of `G` in the ball
`B(x, r)` has a length of at least `r`; at most `81` of the balls `B(x_Q, a/2)` of the cubes `Q` far from `D` contain a
given point, and the far cubes are therefore at most `162|G \ D|/a`, which gives (v) with `162` in the place of `324`.
-/
import CoreLean.ContractedGrid

open Set Real MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CoreLean
namespace Contracted
namespace Grid

variable {g : Grid}

/-- A connected union of cubes (`def:localisation`(i)). -/
abbrev Conn (g : Grid) (X : Finset g.Idx) : Prop :=
  ((wallGraph (ZMod g.n)).induce (X : Set g.Idx)).Connected

lemma Conn.nonempty {X : Finset g.Idx} (hX : g.Conn X) : X.Nonempty := by
  obtain ⟨⟨c, hc⟩⟩ := SimpleGraph.Connected.nonempty hX
  exact ⟨c, hc⟩

instance (c c' : g.Idx) : Decidable (Touch c c') := by unfold Touch; infer_instance

lemma isClosed_cubes (X : Finset g.Idx) : IsClosed (g.cubes X) :=
  isClosed_biUnion_finset fun _ _ => Metric.isClosed_closedBall

lemma cubes_empty : g.cubes (∅ : Finset g.Idx) = ∅ := by simp [cubes]

/-- Cubes which share a wall touch. -/
lemma touch_of_adj {c c' : g.Idx} (h : (wallGraph (ZMod g.n)).Adj c c') : Touch c c' := by
  obtain ⟨-, ⟨μ, b⟩, rfl⟩ := h
  intro ν
  by_cases hν : ν = μ
  · subst hν; cases b <;> simp [wallNbr]
  · cases b <;> simp [wallNbr, Pi.single_apply, hν]

/-- At most `81` cubes touch a given cube. -/
lemma card_touch_le (d : g.Idx) : (Finset.univ.filter fun c => Touch d c).card ≤ 81 := by
  classical
  have hsub : (Finset.univ.filter fun c => Touch d c) ⊆
      (Fintype.piFinset fun _ : Fin 4 => ({-1, 0, 1} : Finset ℤ)).image
        (fun δ => d + fun ν => (δ ν : ZMod g.n)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨δ, hδ, rfl⟩ := touch_iff_int.1 hc.2
    refine Finset.mem_image.2 ⟨δ, Fintype.mem_piFinset.2 fun ν => ?_, rfl⟩
    have := hδ ν
    rw [abs_le] at this
    rcases (by omega : δ ν = -1 ∨ δ ν = 0 ∨ δ ν = 1) with h | h | h <;> simp [h]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Fintype.card_piFinset]
  simp

/-- The union of the cubes of a wall-connected set of cubes is preconnected. -/
lemma isPreconnected_cubes_of_reach {X : Finset g.Idx}
    (h : ∀ c ∈ X, ∀ c' ∈ X, Relation.ReflTransGen
      (fun a b => (wallGraph (ZMod g.n)).Adj a b ∧ a ∈ X) c c') :
    IsPreconnected (g.cubes X) := by
  unfold cubes
  rw [← Finset.set_biUnion_coe]
  refine IsPreconnected.biUnion_of_reflTransGen (fun c _ => isPreconnected_cube c) fun c hc c' hc' => ?_
  exact Relation.ReflTransGen.mono
    (p := fun a b => (g.cube a ∩ g.cube b).Nonempty ∧ a ∈ (X : Set g.Idx))
    (fun a b hab => ⟨touch_inter (touch_of_adj hab.1), Finset.mem_coe.2 hab.2⟩) _ _ (h c hc c' hc')

lemma Conn.isPreconnected {X : Finset g.Idx} (hX : g.Conn X) : IsPreconnected (g.cubes X) := by
  refine isPreconnected_cubes_of_reach fun c hc c' hc' => ?_
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
    (SimpleGraph.Connected.preconnected hX ⟨c, hc⟩ ⟨c', hc'⟩)
  exact Relation.ReflTransGen.lift (p := fun a b => (wallGraph (ZMod g.n)).Adj a b ∧ a ∈ X)
    (fun v : (X : Set g.Idx) => v.1) (fun v w hvw => ⟨hvw, v.2⟩) _ _ hr

/-! ### The length of a segment near a point -/

/-- The parametrisation `θ ↦ π(σ.1 + θσ.2)`. -/
def path (g : Grid) (σ : Seg) : ℝ → g.T := fun θ => proj g.s g.N (σ.1 + θ • σ.2)

lemma path_lip (σ : Seg) : LipschitzWith ‖σ.2‖₊ (g.path σ) :=
  LipschitzWith.of_dist_le_mul fun θ θ' => by
    refine (dist_proj_le _ _).trans (le_of_eq ?_)
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, Real.dist_eq,
      coe_nnNorm, mul_comm]

lemma path_continuous (σ : Seg) : Continuous (g.path σ) := (path_lip σ).continuous

lemma segSet_eq_path (σ : Seg) : segSet g.s g.N σ = g.path σ '' Icc 0 1 := rfl

/-- **The mass near a far point.** If `G ∪ F` is connected, `F ≠ ∅`, and `x ∈ G` is at a distance `> r` from `F`,
then the parameters of the segments in the ball `B(x, r)`, weighted by the lengths, have a total of at least `r`. -/
theorem mass {S : Finset Seg} {F : Set g.T} (hF : F.Nonempty)
    (hconn : IsPreconnected ((⋃ σ ∈ S, segSet g.s g.N σ) ∪ F)) {x : g.T}
    (hx : x ∈ ⋃ σ ∈ S, segSet g.s g.N σ) {r : ℝ} (hr : 0 ≤ r) (hfar : ∀ z ∈ F, r < dist z x) :
    ENNReal.ofReal r ≤ ∑ σ ∈ S, (‖σ.2‖₊ : ℝ≥0∞) *
      volume {θ ∈ Icc (0 : ℝ) 1 | g.path σ θ ∈ Metric.closedBall x r} := by
  classical
  set A : Seg → Set ℝ := fun σ => {θ ∈ Icc (0 : ℝ) 1 | g.path σ θ ∈ Metric.closedBall x r}
  set f : Seg → ℝ → ℝ := fun σ θ => dist (g.path σ θ) x
  -- every value in `[0, r]` is attained
  have hcover : Icc 0 r ⊆ ⋃ σ ∈ S, f σ '' A σ := by
    intro ρ hρ
    by_contra hno
    have hno' : ∀ σ ∈ S, ∀ θ ∈ Icc (0 : ℝ) 1, f σ θ ≠ ρ := by
      intro σ hσ θ hθ heq
      refine hno (mem_iUnion₂.2 ⟨σ, hσ, θ, ⟨hθ, ?_⟩, heq⟩)
      rw [Metric.mem_closedBall]
      have : dist (g.path σ θ) x = ρ := heq
      rw [this]; exact hρ.2
    obtain ⟨σ0, hσ0, θ0, hθ0, hx0⟩ := mem_iUnion₂.1 hx
    have hρ0 : 0 < ρ := by
      rcases hρ.1.lt_or_eq with h | h
      · exact h
      · have h0 : f σ0 θ0 = 0 := by
          show dist (g.path σ0 θ0) x = 0
          rw [dist_eq_zero]; exact hx0
        exact absurd (h0.trans h) (hno' σ0 hσ0 θ0 hθ0)
    have hsep := hconn {z | dist z x < ρ} {z | ρ < dist z x}
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
      (isOpen_lt continuous_const (continuous_id.dist continuous_const)) ?_ ?_ ?_
    · obtain ⟨z, -, h1, h2⟩ := hsep
      exact absurd (lt_trans (show dist z x < ρ from h1) (show ρ < dist z x from h2)) (lt_irrefl _)
    · rintro z (hz | hz)
      · obtain ⟨σ, hσ, θ, hθ, rfl⟩ := mem_iUnion₂.1 hz
        rcases lt_or_gt_of_ne (hno' σ hσ θ hθ) with h | h
        · exact Or.inl h
        · exact Or.inr h
      · exact Or.inr (hρ.2.trans_lt (hfar z hz))
    · exact ⟨x, Or.inl hx, by simp only [mem_setOf_eq, dist_self]; exact hρ0⟩
    · obtain ⟨z, hz⟩ := hF
      exact ⟨z, Or.inr hz, hρ.2.trans_lt (hfar z hz)⟩
  have hlip : ∀ σ, LipschitzWith ‖σ.2‖₊ (f σ) := fun σ => by
    have := (LipschitzWith.dist_left x).comp (path_lip (g := g) σ)
    rw [one_mul] at this
    exact this
  calc ENNReal.ofReal r = volume (Icc (0 : ℝ) r) := by rw [Real.volume_Icc, sub_zero]
    _ ≤ volume (⋃ σ ∈ S, f σ '' A σ) := measure_mono hcover
    _ ≤ ∑ σ ∈ S, volume (f σ '' A σ) := measure_biUnion_finset_le S _
    _ ≤ ∑ σ ∈ S, (‖σ.2‖₊ : ℝ≥0∞) * volume (A σ) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have := (hlip σ).hausdorffMeasure_image_le zero_le_one (A σ)
        rwa [hausdorffMeasure_real, ENNReal.rpow_one] at this

lemma measurableSet_near (σ : Seg) (x : g.T) (r : ℝ) :
    MeasurableSet {θ ∈ Icc (0 : ℝ) 1 | g.path σ θ ∈ Metric.closedBall x r} :=
  measurableSet_Icc.inter (Metric.isClosed_closedBall.preimage (path_continuous σ)).measurableSet

lemma measurableSet_out (σ : Seg) {F : Set g.T} (hF : IsClosed F) :
    MeasurableSet {θ ∈ Icc (0 : ℝ) 1 | g.path σ θ ∉ F} :=
  measurableSet_Icc.inter (hF.isOpen_compl.preimage (path_continuous σ)).measurableSet

/-- **Counting far points.** If the points `x_i ∈ G`, `i ∈ I`, are at a distance `> r` from `F`, and at most `m` of
the balls `B(x_i, r)` contain a given point, then `#I · r ≤ m Σ_σ lenOut F σ`. -/
theorem count_mass {S : Finset Seg} {F : Set g.T} (hFc : IsClosed F) (hF : F.Nonempty)
    (hconn : IsPreconnected ((⋃ σ ∈ S, segSet g.s g.N σ) ∪ F)) {ι : Type*} (I : Finset ι) (x : ι → g.T)
    (hx : ∀ i ∈ I, x i ∈ ⋃ σ ∈ S, segSet g.s g.N σ) {r : ℝ} (hr : 0 ≤ r)
    (hfar : ∀ i ∈ I, ∀ z ∈ F, r < dist z (x i)) {m : ℕ}
    (hm : ∀ p : g.T, (I.filter fun i => dist p (x i) ≤ r).card ≤ m) :
    (I.card : ℝ) * r ≤ m * ∑ σ ∈ S, lenOut g.s g.N F σ := by
  classical
  set A : Seg → ι → Set ℝ := fun σ i => {θ ∈ Icc (0 : ℝ) 1 | g.path σ θ ∈ Metric.closedBall (x i) r}
  set B : Seg → Set ℝ := fun σ => {θ ∈ Icc (0 : ℝ) 1 | g.path σ θ ∉ F}
  -- the multiplicity of the sets `A σ i`
  have hmult : ∀ σ, ∑ i ∈ I, volume (A σ i) ≤ m * volume (B σ) := fun σ => by
    rw [← lintegral_indicator_one (measurableSet_out σ hFc)]
    have e : ∑ i ∈ I, volume (A σ i) = ∫⁻ θ, ∑ i ∈ I, (A σ i).indicator 1 θ := by
      rw [lintegral_finsetSum _ fun i _ => (measurable_one.indicator (measurableSet_near σ (x i) r))]
      exact Finset.sum_congr rfl fun i _ => (lintegral_indicator_one (measurableSet_near σ (x i) r)).symm
    rw [e, ← lintegral_const_mul _ (measurable_one.indicator (measurableSet_out σ hFc))]
    refine lintegral_mono fun θ => ?_
    by_cases hθ : θ ∈ B σ
    · rw [indicator_of_mem hθ, Pi.one_apply, mul_one]
      calc ∑ i ∈ I, (A σ i).indicator 1 θ = ((I.filter fun i => θ ∈ A σ i).card : ℝ≥0∞) := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h : θ ∈ A σ i <;> simp [h]
        _ ≤ m := by
            refine Nat.cast_le.2 ((Finset.card_le_card fun i hi => ?_).trans (hm (g.path σ θ)))
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨hi.1, Metric.mem_closedBall.1 hi.2.2⟩
    · rw [indicator_of_notMem hθ, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero fun i hi => indicator_of_notMem (fun (hA : θ ∈ A σ i) =>
        hθ ⟨hA.1, fun hFθ => absurd (Metric.mem_closedBall.1 hA.2) (not_le.2 (hfar i hi _ hFθ))⟩) _)
  have hkey : (I.card : ℝ≥0∞) * ENNReal.ofReal r ≤ m * ∑ σ ∈ S, ENNReal.ofReal (lenOut g.s g.N F σ) := by
    calc (I.card : ℝ≥0∞) * ENNReal.ofReal r = ∑ i ∈ I, ENNReal.ofReal r := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, ∑ σ ∈ S, (‖σ.2‖₊ : ℝ≥0∞) * volume (A σ i) := by
          refine Finset.sum_le_sum fun i hi => mass hF hconn (hx i hi) hr (hfar i hi)
      _ = ∑ σ ∈ S, (‖σ.2‖₊ : ℝ≥0∞) * ∑ i ∈ I, volume (A σ i) := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ ∑ σ ∈ S, (‖σ.2‖₊ : ℝ≥0∞) * (m * volume (B σ)) :=
          Finset.sum_le_sum fun σ _ => mul_le_mul' le_rfl (hmult σ)
      _ ≤ ∑ σ ∈ S, m * ENNReal.ofReal (lenOut g.s g.N F σ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [mul_left_comm]
          refine mul_le_mul' le_rfl ?_
          unfold lenOut
          rw [ENNReal.ofReal_mul (eu_nonneg _), ENNReal.ofReal_toReal (volume_out_ne_top F σ)]
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
          exact ENNReal.ofReal_le_ofReal (norm_le_eu _)
      _ = m * ∑ σ ∈ S, ENNReal.ofReal (lenOut g.s g.N F σ) := by rw [Finset.mul_sum]
  have hfin : (m : ℝ≥0∞) * ∑ σ ∈ S, ENNReal.ofReal (lenOut g.s g.N F σ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.sum_ne_top.2 fun σ _ => ENNReal.ofReal_ne_top)
  have := ENNReal.toReal_mono hfin hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sum fun σ _ => ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr] at this
  simp only [ENNReal.toReal_natCast] at this
  rwa [Finset.sum_congr rfl fun σ _ => ENNReal.toReal_ofReal (lenOut_nonneg F σ)] at this

/-! ### (v) -/

/-- **`lem:contracted-geometry`(v)**: for a connected union `X` of cubes and a nonempty union `D ⊆ X` of cubes,
`#(X) ≤ 81#(D) + 324 d(X; D)`. -/
theorem contracted_v {X D : Finset g.Idx} (hX : g.Conn X) (hDX : D ⊆ X) (hD : D.Nonempty) :
    (X.card : ℝ) ≤ 81 * D.card + 324 * g.d X D := by
  classical
  have ha := g.ha
  set near := X.filter fun c => ∃ d ∈ D, Touch d c
  set far := X.filter fun c => ¬ ∃ d ∈ D, Touch d c
  have hsplit : X.card = near.card + far.card := (Finset.card_filter_add_card_filter_not _).symm
  -- the cubes touching `D`
  have hnear : (near.card : ℝ) ≤ 81 * D.card := by
    have hsub : near ⊆ D.biUnion fun d => Finset.univ.filter fun c => Touch d c := by
      intro c hc
      obtain ⟨d, hd, hdc⟩ := (Finset.mem_filter.1 hc).2
      exact Finset.mem_biUnion.2 ⟨d, hd, Finset.mem_filter.2 ⟨Finset.mem_univ _, hdc⟩⟩
    have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ d ∈ D, (Finset.univ.filter fun c => Touch d c).card ≤ ∑ _d ∈ D, 81 :=
      Finset.sum_le_sum fun d _ => card_touch_le d
    rw [Finset.sum_const, smul_eq_mul] at h2
    have h3 : near.card ≤ 81 * D.card := by rw [mul_comm]; exact this.trans h2
    exact_mod_cast h3
  -- the far cubes, for one admissible family
  have hfar_adm : ∀ S, g.Adm X D S → (far.card : ℝ) * (g.a / 2) ≤ 81 * g.cost D S := by
    intro S hS
    have hpt : ∀ c, ∃ y, c ∈ X → y ∈ (⋃ σ ∈ S, segSet g.s g.N σ) ∧ y ∈ g.cube c := fun c => by
      by_cases hc : c ∈ X
      · obtain ⟨σ, hσ, y, hy1, hy2⟩ := hS.2.1 c hc
        exact ⟨y, fun _ => ⟨mem_iUnion₂.2 ⟨σ, hσ, hy1⟩, hy2⟩⟩
      · exact ⟨g.centre c, fun h => absurd h hc⟩
    choose y hy using hpt
    refine count_mass (isClosed_cubes D)
        ⟨g.centre hD.choose, mem_iUnion₂.2 ⟨_, hD.choose_spec, centre_mem_cube _⟩⟩ hS.2.2 far y
      (fun c hc => (hy c (Finset.mem_filter.1 hc).1).1) (by linarith) ?_ ?_
    · intro c hc z hz
      obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 hz
      have hnt : ¬ Touch d c := fun h => (Finset.mem_filter.1 hc).2 ⟨d, hd, h⟩
      have := far_of_not_touch hnt hzd (hy c (Finset.mem_filter.1 hc).1).2
      linarith
    · intro p
      refine (Finset.card_le_card ?_).trans (card_near_le (g := g) p (R := g.a) (by linarith))
      · intro c hc
        rw [Finset.mem_filter] at hc ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 := Metric.mem_closedBall.1 (hy c (Finset.mem_filter.1 hc.1).1).2
        calc dist (g.centre c) p ≤ dist (g.centre c) (y c) + dist (y c) p := dist_triangle _ _ _
          _ ≤ g.a / 2 + g.a / 2 := by linarith [hc.2, h1, dist_comm (g.centre c) (y c), dist_comm (y c) p]
          _ = g.a := by ring
  have hne := exists_adm (g := g) hX hDX
  have hfar : (far.card : ℝ) ≤ 162 * g.d X D := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨S, hS, hc⟩ := exists_adm_le hne (by positivity : 0 < ε / 162)
    have h1 := hfar_adm S hS
    have : (far.card : ℝ) * (g.a / 2) ≤ 81 * (g.a * (g.d X D + ε / 162)) := h1.trans (by linarith)
    have h2 : (far.card : ℝ) ≤ 162 * (g.d X D + ε / 162) := by
      have : (far.card : ℝ) * g.a ≤ 162 * (g.d X D + ε / 162) * g.a := by nlinarith
      exact le_of_mul_le_mul_right this ha
    linarith
  have hd0 := d_nonneg (g := g) X D
  rw [hsplit]; push_cast
  linarith

/-! ### Sums over unions -/

lemma sum_union_le' {α : Type*} [DecidableEq α] (s t : Finset α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter]
  linarith [Finset.sum_nonneg fun x (_ : x ∈ s ∩ t) => hf x]

lemma sum_biUnion_le' {β α : Type*} [DecidableEq α] (s : Finset β) (t : β → Finset α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s.biUnion t, f x ≤ ∑ y ∈ s, ∑ x ∈ t y, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert y s hy ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hy]
    exact (sum_union_le' _ _ hf).trans (by linarith)

lemma sum_image_le' {β α : Type*} [DecidableEq α] (s : Finset β) (h : β → α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s.image h, f x ≤ ∑ y ∈ s, f (h y) :=
  Finset.sum_image_le_of_nonneg fun x _ => hf x

/-! ### (iv) -/

/-- **`lem:contracted-geometry`(iv)**: for a connected union `Z` of cubes, connected unions `Z_i ⊆ Z` with unions
`D_i ⊆ Z_i` of cubes, of which `n'` are nonempty and `n_∅` empty, `Z₀ = ⋃_iZ_i`, `D = ⋃_iD_i`,
`d(Z; D) ≤ Σ_i d(Z_i; D_i) + 3#(Z \ Z₀) + 3(n_∅ + n' - 1)`. -/
theorem contracted_iv {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : Finset g.Idx} (hZ : g.Conn Z)
    (Zi : ι → Finset g.Idx) (hZi : ∀ i, g.Conn (Zi i)) (hZiZ : ∀ i, Zi i ⊆ Z) (Di : ι → Finset g.Idx)
    (hDi : ∀ i, Di i ⊆ Zi i) :
    g.d Z (Finset.univ.biUnion Di) ≤ ∑ i, g.d (Zi i) (Di i) + 3 * (Z \ Finset.univ.biUnion Zi).card +
      3 * (((Finset.univ.filter fun i => Di i = ∅).card : ℝ) +
        (Finset.univ.filter fun i => (Di i).Nonempty).card - 1) := by
  classical
  have ha := g.ha
  set Z0 := Finset.univ.biUnion Zi with hZ0
  set D := Finset.univ.biUnion Di with hD
  set Fr := Z \ Z0 with hFr
  have hcnt : ((Finset.univ.filter fun i => Di i = ∅).card : ℝ) +
      (Finset.univ.filter fun i => (Di i).Nonempty).card = Fintype.card ι := by
    have h1 : (Finset.univ.filter fun i => (Di i).Nonempty) = Finset.univ.filter fun i => ¬ (Di i = ∅) :=
      Finset.filter_congr fun i _ => Finset.nonempty_iff_ne_empty
    rw [h1]
    exact_mod_cast Finset.card_filter_add_card_filter_not _
  rw [hcnt]
  have hDZ : D ⊆ Z := Finset.biUnion_subset.2 fun i _ => (hDi i).trans (hZiZ i)
  have hne := exists_adm (g := g) hZ hDZ
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set δ' := δ / (Fintype.card ι + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  choose GS hGS using fun i => exists_adm_le (exists_adm (hZi i) (hDi i)) hδ'0
  -- the pieces
  set P : Finset (ι ⊕ g.Idx) := Finset.univ.image Sum.inl ∪ Fr.image Sum.inr with hP
  set A : ι ⊕ g.Idx → Set g.T :=
    Sum.elim (fun i => (⋃ σ ∈ GS i, segSet g.s g.N σ) ∪ g.cubes (Di i)) (fun c => {g.centre c}) with hA
  set C : ι ⊕ g.Idx → Finset g.Idx := Sum.elim Zi (fun c => {c}) with hC
  have hPmem : ∀ p ∈ P, (∃ i, p = Sum.inl i) ∨ (∃ c ∈ Fr, p = Sum.inr c) := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h; exact Or.inl ⟨i, rfl⟩
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h; exact Or.inr ⟨c, hc, rfl⟩
  have hinl : ∀ i, Sum.inl i ∈ P := fun i =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hinr : ∀ c ∈ Fr, Sum.inr c ∈ P := fun c hc => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)
  have hcovZ : ∀ c ∈ Z, (∃ i, c ∈ Zi i) ∨ c ∈ Fr := fun c hc => by
    by_cases h : c ∈ Z0
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h; exact Or.inl ⟨i, hi⟩
    · exact Or.inr (Finset.mem_sdiff.2 ⟨hc, h⟩)
  have hPne : P.Nonempty := by
    obtain ⟨c, hc⟩ := Conn.nonempty hZ
    rcases hcovZ c hc with ⟨i, -⟩ | hc'
    · exact ⟨_, hinl i⟩
    · exact ⟨_, hinr c hc'⟩
  obtain ⟨J, hJZ, hJl, hJc⟩ := join_pieces (g := g) P hPne A C hZ
    (fun p hp => by
      rcases hPmem p hp with ⟨i, rfl⟩ | ⟨c, -, rfl⟩
      · exact (hGS i).1.2.2
      · exact isPreconnected_singleton)
    (fun p hp c hc => by
      rcases hPmem p hp with ⟨i, rfl⟩ | ⟨c', -, rfl⟩
      · obtain ⟨σ, hσ, z, hz1, hz2⟩ := (hGS i).1.2.1 c hc
        exact ⟨z, Or.inl (mem_iUnion₂.2 ⟨σ, hσ, hz1⟩), hz2⟩
      · rw [show c = c' from Finset.mem_singleton.1 hc]
        exact ⟨g.centre c', mem_singleton _, centre_mem_cube c'⟩)
    (fun p hp => by
      rcases hPmem p hp with ⟨i, rfl⟩ | ⟨c, hc, rfl⟩
      · exact hZiZ i
      · exact Finset.singleton_subset_iff.2 (Finset.mem_sdiff.1 hc).1)
    (fun c hc => by
      rcases hcovZ c hc with ⟨i, hi⟩ | hc'
      · exact ⟨_, hinl i, hi⟩
      · exact ⟨_, hinr c hc', Finset.mem_singleton_self c⟩)
    (fun p hp => by
      rcases hPmem p hp with ⟨i, rfl⟩ | ⟨c, -, rfl⟩
      · exact Conn.nonempty (hZi i)
      · exact Finset.singleton_nonempty c)
  -- the family
  set S := Finset.univ.biUnion GS ∪ J ∪ Fr.image (fun c => pt (g.lift c)) with hS
  have hSeq : (⋃ σ ∈ S, segSet g.s g.N σ) ∪ g.cubes D = (⋃ p ∈ P, A p) ∪ ⋃ σ ∈ J, segSet g.s g.N σ := by
    apply Subset.antisymm
    · rintro z (hz | hz)
      · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hz
        rcases Finset.mem_union.1 hσ with hσ | hσ
        · rcases Finset.mem_union.1 hσ with hσ | hσ
          · obtain ⟨i, -, hσi⟩ := Finset.mem_biUnion.1 hσ
            exact Or.inl (mem_iUnion₂.2 ⟨_, hinl i, Or.inl (mem_iUnion₂.2 ⟨σ, hσi, hzσ⟩)⟩)
          · exact Or.inr (mem_iUnion₂.2 ⟨σ, hσ, hzσ⟩)
        · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hσ
          rw [segSet_pt] at hzσ
          exact Or.inl (mem_iUnion₂.2 ⟨_, hinr c hc, hzσ⟩)
      · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 hz
        obtain ⟨i, -, hdi⟩ := Finset.mem_biUnion.1 hd
        exact Or.inl (mem_iUnion₂.2 ⟨_, hinl i, Or.inr (mem_iUnion₂.2 ⟨d, hdi, hzd⟩)⟩)
    · rintro z (hz | hz)
      · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
        rcases hPmem p hp with ⟨i, rfl⟩ | ⟨c, hc, rfl⟩
        · rcases hzp with hzp | hzp
          · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hzp
            exact Or.inl (mem_iUnion₂.2 ⟨σ, Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hσ⟩)), hzσ⟩)
          · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 hzp
            exact Or.inr (mem_iUnion₂.2 ⟨d, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hd⟩, hzd⟩)
        · refine Or.inl (mem_iUnion₂.2 ⟨pt (g.lift c), Finset.mem_union_right _
            (Finset.mem_image_of_mem _ hc), ?_⟩)
          rw [segSet_pt]; exact hzp
      · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hz
        exact Or.inl (mem_iUnion₂.2 ⟨σ, Finset.mem_union_left _ (Finset.mem_union_right _ hσ), hzσ⟩)
  have hAdm : g.Adm Z D S := by
    refine ⟨fun σ hσ => ?_, fun c hc => ?_, by rw [hSeq]; exact hJc⟩
    · rcases Finset.mem_union.1 hσ with hσ | hσ
      · rcases Finset.mem_union.1 hσ with hσ | hσ
        · obtain ⟨i, -, hσi⟩ := Finset.mem_biUnion.1 hσ
          exact ((hGS i).1.1 σ hσi).trans (cubes_mono (hZiZ i))
        · exact hJZ σ hσ
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hσ
        rw [segSet_pt, singleton_subset_iff]
        exact cube_subset_cubes (Finset.mem_sdiff.1 hc).1 (centre_mem_cube c)
    · rcases hcovZ c hc with ⟨i, hi⟩ | hc'
      · obtain ⟨σ, hσ, hz⟩ := (hGS i).1.2.1 c hi
        exact ⟨σ, Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hσ⟩)), hz⟩
      · refine ⟨pt (g.lift c), Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc'), g.centre c, ?_,
          centre_mem_cube c⟩
        rw [segSet_pt]; rfl
  -- the cost
  have hcost : g.cost D S ≤ ∑ i, g.a * (g.d (Zi i) (Di i) + δ') +
      3 * g.a * ((Fintype.card ι : ℝ) + Fr.card - 1) := by
    have hl0 : ∀ σ, 0 ≤ lenOut g.s g.N (g.cubes D) σ := fun σ => lenOut_nonneg _ σ
    have h1 : ∑ σ ∈ Finset.univ.biUnion GS, lenOut g.s g.N (g.cubes D) σ ≤
        ∑ i, g.a * (g.d (Zi i) (Di i) + δ') := by
      refine (sum_biUnion_le' _ _ hl0).trans (Finset.sum_le_sum fun i _ => ?_)
      refine le_trans (Finset.sum_le_sum fun σ _ => lenOut_anti ?_ σ) (hGS i).2
      exact cubes_mono (Finset.subset_biUnion_of_mem Di (Finset.mem_univ i))
    have h2 : ∑ σ ∈ J, lenOut g.s g.N (g.cubes D) σ ≤ 3 * g.a * ((P.card : ℝ) - 1) :=
      (Finset.sum_le_sum fun σ _ => lenOut_le_eu _ σ).trans hJl
    have h3 : ∑ σ ∈ Fr.image (fun c => pt (g.lift c)), lenOut g.s g.N (g.cubes D) σ = 0 :=
      Finset.sum_eq_zero fun σ hσ => by
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hσ; exact lenOut_pt _ _
    have hPc : (P.card : ℝ) ≤ Fintype.card ι + Fr.card := by
      have := (Finset.card_union_le _ _).trans (add_le_add (Finset.card_image_le (s := Finset.univ)
        (f := (Sum.inl : ι → ι ⊕ g.Idx))) (Finset.card_image_le (s := Fr) (f := Sum.inr)))
      rw [Finset.card_univ] at this
      exact_mod_cast this
    unfold cost
    refine (sum_union_le' _ _ hl0).trans ?_
    rw [h3, add_zero]
    refine (sum_union_le' _ _ hl0).trans ?_
    nlinarith
  have hmain := (a_mul_d_le hAdm).trans hcost
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hmain
  have hdiv : g.d Z D ≤ ∑ i, g.d (Zi i) (Di i) + Fintype.card ι * δ' +
      3 * ((Fintype.card ι : ℝ) + Fr.card - 1) := by
    have : g.a * g.d Z D ≤ g.a * (∑ i, g.d (Zi i) (Di i) + Fintype.card ι * δ' +
        3 * ((Fintype.card ι : ℝ) + Fr.card - 1)) := by nlinarith
    exact le_of_mul_le_mul_left this ha
  have hδle : (Fintype.card ι : ℝ) * δ' ≤ δ := by
    rw [hδ', mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### (i) -/

/-- The cubes of a connected component of `D`. -/
def compSet (D : Finset g.Idx)
    (κ : ((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).ConnectedComponent) : Finset g.Idx := by
  classical
  exact D.filter fun c => ∃ h : c ∈ D,
    ((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).connectedComponentMk ⟨c, h⟩ = κ

lemma compSet_subset (D : Finset g.Idx) (κ) : compSet D κ ⊆ D := by
  classical
  unfold compSet; exact Finset.filter_subset _ _

lemma mem_compSet {D : Finset g.Idx} {c : g.Idx} (hc : c ∈ D) :
    c ∈ compSet D (((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).connectedComponentMk ⟨c, hc⟩) := by
  classical
  unfold compSet; exact Finset.mem_filter.2 ⟨hc, hc, rfl⟩

lemma compSet_nonempty (D : Finset g.Idx) (κ) : (compSet D κ).Nonempty := by
  induction κ using SimpleGraph.ConnectedComponent.ind with
  | h v => exact ⟨v.1, mem_compSet v.2⟩

lemma isPreconnected_compSet (D : Finset g.Idx) (κ) : IsPreconnected (g.cubes (compSet D κ)) := by
  classical
  have hmem : ∀ c, c ∈ compSet D κ ↔ ∃ h : c ∈ D, ((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).connectedComponentMk ⟨c, h⟩ = κ := fun c => by
    unfold compSet
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  refine isPreconnected_cubes_of_reach fun c hc c' hc' => ?_
  obtain ⟨hcD, hcκ⟩ := (hmem c).1 hc
  obtain ⟨hc'D, hc'κ⟩ := (hmem c').1 hc'
  have hr : ((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).Reachable ⟨c, hcD⟩ ⟨c', hc'D⟩ :=
    SimpleGraph.ConnectedComponent.eq.1 (hcκ.trans hc'κ.symm)
  have key : ∀ w : (D : Set g.Idx), Relation.ReflTransGen ((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).Adj ⟨c, hcD⟩ w →
      Relation.ReflTransGen (fun a b => (wallGraph (ZMod g.n)).Adj a b ∧ a ∈ compSet D κ) c w.1 := by
    intro w hw
    induction hw with
    | refl => exact Relation.ReflTransGen.refl
    | @tail v w hv hvw ih =>
      refine ih.tail ⟨hvw, (hmem v.1).2 ⟨v.2, ?_⟩⟩
      have : ((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).Reachable ⟨c, hcD⟩ v := (SimpleGraph.reachable_iff_reflTransGen _ _).2 hv
      exact (SimpleGraph.ConnectedComponent.eq.2 this).symm.trans hcκ
  exact key _ ((SimpleGraph.reachable_iff_reflTransGen _ _).1 hr)

/-- **`lem:contracted-geometry`(i)**: for a connected union `Y₀` of cubes, a finite family `DD` of connected unions
`Y ⊆ Y₀`, and a union `D ⊆ Y₀` of cubes with `n_D` connected components such that `Y₀ = ⋃_{Y ∈ DD} Y ∪ D`,
`Σ_{Y ∈ DD} d(Y) ≥ d(Y₀; D) - 3(|DD| + n_D - 1)`. -/
theorem contracted_i {Y0 : Finset g.Idx} (hY0 : g.Conn Y0) (DD : Finset (Finset g.Idx))
    (hDD : ∀ Y ∈ DD, g.Conn Y ∧ Y ⊆ Y0) (D : Finset g.Idx) (hcov : Y0 = DD.biUnion id ∪ D) :
    g.d Y0 D - 3 * ((DD.card : ℝ) +
      Nat.card (((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).ConnectedComponent) - 1) ≤
      ∑ Y ∈ DD, g.d Y ∅ := by
  classical
  have ha := g.ha
  set CC := ((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).ConnectedComponent
  haveI : Fintype CC := Fintype.ofFinite CC
  have hDY : D ⊆ Y0 := by rw [hcov]; exact Finset.subset_union_right
  have hDDY : ∀ Y ∈ DD, ∀ c ∈ Y, c ∈ Y0 := fun Y hY c hc => (hDD Y hY).2 hc
  have hne := exists_adm (g := g) hY0 hDY
  refine sub_le_iff_le_add.2 (le_of_forall_pos_le_add fun δ hδ => ?_)
  set δ' := δ / (DD.card + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hex : ∀ Y : Finset g.Idx, ∃ S : Finset Seg, Y ∈ DD →
      g.Adm Y ∅ S ∧ g.cost ∅ S ≤ g.a * (g.d Y ∅ + δ') := fun Y => by
    by_cases h : Y ∈ DD
    · obtain ⟨S, hS⟩ := exists_adm_le (exists_adm (hDD Y h).1 (Finset.empty_subset _)) hδ'0
      exact ⟨S, fun _ => hS⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose GS hGS using hex
  set comps : Finset (Finset g.Idx) := Finset.univ.image (compSet D) with hcomps
  set P := DD ∪ comps with hP
  set A : Finset g.Idx → Set g.T := fun Y => if Y ∈ DD then ⋃ σ ∈ GS Y, segSet g.s g.N σ else g.cubes Y
    with hA
  have hcompmem : ∀ Y ∈ comps, ∃ κ, Y = compSet D κ := fun Y hY => by
    obtain ⟨κ, -, rfl⟩ := Finset.mem_image.1 hY; exact ⟨κ, rfl⟩
  have hPmem : ∀ Y ∈ P, Y ∈ DD ∨ (Y ∉ DD ∧ ∃ κ, Y = compSet D κ) := fun Y hY => by
    by_cases h : Y ∈ DD
    · exact Or.inl h
    · rcases Finset.mem_union.1 hY with h' | h'
      · exact absurd h' h
      · exact Or.inr ⟨h, hcompmem Y h'⟩
  have hcomp_in : ∀ d (hd : d ∈ D), compSet D (((wallGraph (ZMod g.n)).induce (D : Set g.Idx)).connectedComponentMk
      ⟨d, hd⟩) ∈ P := fun d hd =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hcovY : ∀ c ∈ Y0, (∃ Y ∈ DD, c ∈ Y) ∨ c ∈ D := fun c hc => by
    rw [hcov] at hc
    rcases Finset.mem_union.1 hc with h | h
    · obtain ⟨Y, hY, hcY⟩ := Finset.mem_biUnion.1 h; exact Or.inl ⟨Y, hY, hcY⟩
    · exact Or.inr h
  have hADD : ∀ Y ∈ DD, A Y = ⋃ σ ∈ GS Y, segSet g.s g.N σ := fun Y hY => if_pos hY
  have hAcomp : ∀ Y, Y ∉ DD → A Y = g.cubes Y := fun Y hY => if_neg hY
  -- the pieces meet the cubes of their sets
  have hAC : ∀ Y ∈ P, ∀ c ∈ Y, (A Y ∩ g.cube c).Nonempty := fun Y hY c hc => by
    rcases hPmem Y hY with h | ⟨h, -⟩
    · obtain ⟨σ, hσ, z, hz1, hz2⟩ := (hGS Y h).1.2.1 c hc
      exact ⟨z, by rw [hADD Y h]; exact mem_iUnion₂.2 ⟨σ, hσ, hz1⟩, hz2⟩
    · exact ⟨g.centre c, by rw [hAcomp Y h]; exact cube_subset_cubes hc (centre_mem_cube c), centre_mem_cube c⟩
  have hPne : P.Nonempty := by
    obtain ⟨c, hc⟩ := Conn.nonempty hY0
    rcases hcovY c hc with ⟨Y, hY, -⟩ | hcD
    · exact ⟨Y, Finset.mem_union_left _ hY⟩
    · exact ⟨_, hcomp_in c hcD⟩
  obtain ⟨J, hJZ, hJl, hJc⟩ := join_pieces (g := g) P hPne A id hY0
    (fun Y hY => by
      rcases hPmem Y hY with h | ⟨h, κ, rfl⟩
      · rw [hADD _ h]
        have := (hGS _ h).1.2.2
        rwa [cubes_empty, union_empty] at this
      · rw [hAcomp _ h]; exact isPreconnected_compSet D κ)
    (fun Y hY c hc => hAC Y hY c hc)
    (fun Y hY => by
      rcases hPmem Y hY with h | ⟨-, κ, rfl⟩
      · exact (hDD Y h).2
      · exact (compSet_subset D κ).trans hDY)
    (fun c hc => by
      rcases hcovY c hc with ⟨Y, hY, hcY⟩ | hcD
      · exact ⟨Y, Finset.mem_union_left _ hY, hcY⟩
      · exact ⟨_, hcomp_in c hcD, mem_compSet hcD⟩)
    (fun Y hY => by
      rcases hPmem Y hY with h | ⟨-, κ, rfl⟩
      · exact Conn.nonempty (hDD Y h).1
      · exact compSet_nonempty D κ)
  -- the family
  set S := DD.biUnion GS ∪ J ∪ D.image (fun c => pt (g.lift c)) with hS
  set H := (⋃ Y ∈ P, A Y) ∪ ⋃ σ ∈ J, segSet g.s g.N σ with hH
  have hHD : IsPreconnected (H ∪ ⋃ d ∈ D, g.cube d) := by
    refine isPreconnected_hub hJc D (fun d => g.cube d) (fun d _ => isPreconnected_cube d) fun d hd => ?_
    obtain ⟨z, hz1, hz2⟩ := hAC _ (hcomp_in d hd) d (mem_compSet hd)
    exact ⟨z, hz2, Or.inl (mem_iUnion₂.2 ⟨_, hcomp_in d hd, hz1⟩)⟩
  have hSeq : (⋃ σ ∈ S, segSet g.s g.N σ) ∪ g.cubes D = H ∪ ⋃ d ∈ D, g.cube d := by
    apply Subset.antisymm
    · rintro z (hz | hz)
      · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hz
        rcases Finset.mem_union.1 hσ with hσ | hσ
        · rcases Finset.mem_union.1 hσ with hσ | hσ
          · obtain ⟨Y, hY, hσY⟩ := Finset.mem_biUnion.1 hσ
            refine Or.inl (Or.inl (mem_iUnion₂.2 ⟨Y, Finset.mem_union_left _ hY, ?_⟩))
            rw [hADD Y hY]; exact mem_iUnion₂.2 ⟨σ, hσY, hzσ⟩
          · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨σ, hσ, hzσ⟩))
        · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hσ
          rw [segSet_pt] at hzσ
          rw [mem_singleton_iff.1 hzσ]
          exact Or.inr (mem_iUnion₂.2 ⟨c, hc, centre_mem_cube c⟩)
      · exact Or.inr hz
    · rintro z ((hz | hz) | hz)
      · obtain ⟨Y, hY, hzY⟩ := mem_iUnion₂.1 hz
        rcases hPmem Y hY with h | ⟨h, κ, rfl⟩
        · rw [hADD Y h] at hzY
          obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hzY
          exact Or.inl (mem_iUnion₂.2 ⟨σ, Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_biUnion.2 ⟨Y, h, hσ⟩)), hzσ⟩)
        · rw [hAcomp _ h] at hzY
          exact Or.inr (cubes_mono (compSet_subset D κ) hzY)
      · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hz
        exact Or.inl (mem_iUnion₂.2 ⟨σ, Finset.mem_union_left _ (Finset.mem_union_right _ hσ), hzσ⟩)
      · exact Or.inr hz
  have hAdm : g.Adm Y0 D S := by
    refine ⟨fun σ hσ => ?_, fun c hc => ?_, by rw [hSeq]; exact hHD⟩
    · rcases Finset.mem_union.1 hσ with hσ | hσ
      · rcases Finset.mem_union.1 hσ with hσ | hσ
        · obtain ⟨Y, hY, hσY⟩ := Finset.mem_biUnion.1 hσ
          exact ((hGS Y hY).1.1 σ hσY).trans (cubes_mono (hDD Y hY).2)
        · exact hJZ σ hσ
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hσ
        rw [segSet_pt, singleton_subset_iff]
        exact cube_subset_cubes (hDY hc) (centre_mem_cube c)
    · rcases hcovY c hc with ⟨Y, hY, hcY⟩ | hcD
      · obtain ⟨σ, hσ, hz⟩ := (hGS Y hY).1.2.1 c hcY
        exact ⟨σ, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨Y, hY, hσ⟩)), hz⟩
      · refine ⟨pt (g.lift c), Finset.mem_union_right _ (Finset.mem_image_of_mem _ hcD), g.centre c, ?_,
          centre_mem_cube c⟩
        rw [segSet_pt]; rfl
  -- the cost
  have hcost : g.cost D S ≤ ∑ Y ∈ DD, g.a * (g.d Y ∅ + δ') + 3 * g.a * ((P.card : ℝ) - 1) := by
    have hl0 : ∀ σ, 0 ≤ lenOut g.s g.N (g.cubes D) σ := fun σ => lenOut_nonneg _ σ
    have h1 : ∑ σ ∈ DD.biUnion GS, lenOut g.s g.N (g.cubes D) σ ≤ ∑ Y ∈ DD, g.a * (g.d Y ∅ + δ') := by
      refine (sum_biUnion_le' _ _ hl0).trans (Finset.sum_le_sum fun Y hY => ?_)
      exact le_trans (Finset.sum_le_sum fun σ _ => lenOut_anti (cubes_mono (Finset.empty_subset D)) σ)
        (hGS Y hY).2
    have h2 : ∑ σ ∈ J, lenOut g.s g.N (g.cubes D) σ ≤ 3 * g.a * ((P.card : ℝ) - 1) :=
      (Finset.sum_le_sum fun σ _ => lenOut_le_eu _ σ).trans hJl
    have h3 : ∑ σ ∈ D.image (fun c => pt (g.lift c)), lenOut g.s g.N (g.cubes D) σ = 0 :=
      Finset.sum_eq_zero fun σ hσ => by
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hσ; exact lenOut_pt _ _
    unfold cost
    refine (sum_union_le' _ _ hl0).trans ?_
    rw [h3, add_zero]
    refine (sum_union_le' _ _ hl0).trans ?_
    linarith
  have hPc : (P.card : ℝ) ≤ DD.card + Nat.card CC := by
    have h1 := Finset.card_union_le DD comps
    have h2 : comps.card ≤ Nat.card CC := by
      rw [Nat.card_eq_fintype_card]
      exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)
    exact_mod_cast h1.trans (by omega)
  have hmain := (a_mul_d_le hAdm).trans hcost
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hmain
  have hdiv : g.d Y0 D ≤ ∑ Y ∈ DD, g.d Y ∅ + DD.card * δ' + 3 * ((P.card : ℝ) - 1) := by
    have : g.a * g.d Y0 D ≤ g.a * (∑ Y ∈ DD, g.d Y ∅ + DD.card * δ' + 3 * ((P.card : ℝ) - 1)) := by
      nlinarith
    exact le_of_mul_le_mul_left this ha
  have hδle : (DD.card : ℝ) * δ' ≤ δ := by
    rw [hδ', mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### (ii) -/

/-- The vector `(1, 1, 1, 1)`. -/
def one4 : Fin 4 → ℝ := fun _ => 1

/-- The main diagonal of the cube `c`, from `a·c - (a/2)𝟙` to `a·c + (a/2)𝟙`. -/
def diag (g : Grid) (c : g.Idx) : Seg := (g.lift c - (g.a / 2) • one4, g.a • one4)

lemma diag_subset (c : g.Idx) : segSet g.s g.N (g.diag c) ⊆ g.cube c := by
  have ha := g.ha
  rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
  refine proj_mem_cube (norm_le_of_coord (by linarith) fun ν => ?_)
  simp only [diag, one4, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  rw [show g.lift c ν - g.a / 2 + θ * g.a - g.lift c ν = g.a * (θ - 1 / 2) by ring, abs_mul, abs_of_pos ha]
  have : |θ - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  nlinarith

lemma eu_diag_le (c : g.Idx) : eu (g.diag c).2 ≤ 2 * g.a := by
  have ha := g.ha
  refine eu_le_of_sq (by linarith) ?_
  simp only [diag, one4, Pi.smul_apply, smul_eq_mul, mul_one, Fin.sum_univ_four]
  nlinarith

lemma centre_mem_diag (c : g.Idx) : g.centre c ∈ segSet g.s g.N (g.diag c) := by
  refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  simp only [centre, diag]
  congr 1
  funext ν
  simp only [one4, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  ring

/-- The corner of `c` on the wall `p`. -/
def corner (g : Grid) (c : g.Idx) (p : Fin 4 × Bool) : g.T :=
  proj g.s g.N (g.lift c + (if p.2 then g.a / 2 else -(g.a / 2)) • one4)

lemma corner_mem_diag (c : g.Idx) (p : Fin 4 × Bool) : g.corner c p ∈ segSet g.s g.N (g.diag c) := by
  rcases p with ⟨μ, b⟩
  cases b
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp only [corner, diag, zero_smul, add_zero, Bool.false_eq_true, if_false]
    congr 1; funext ν; simp [one4, sub_eq_add_neg]
  · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    simp only [corner, diag, one_smul, if_true]
    congr 1; funext ν; simp only [one4, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma corner_mem_nbr (c : g.Idx) (p : Fin 4 × Bool) : g.corner c p ∈ g.cube (wallNbr (ZMod g.n) c p) := by
  have ha := g.ha
  rw [cube, centre_wallNbr, corner]
  refine proj_mem_closedBall (norm_le_of_coord (by linarith) fun ν => ?_)
  rcases p with ⟨μ, b⟩
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one4, mul_one, add_sub_add_left_eq_sub]
  by_cases hν : ν = μ
  · subst hν
    cases b <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  · cases b <;> simp [Pi.single_apply, hν] <;> rw [abs_le] <;> constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- **`lem:contracted-geometry`(ii)**: for a connected union `Z` of cubes, connected unions `Y_i ⊆ Z` no two of
which have a cube in common or contain two cubes which share a wall, and a union `D ⊆ ⋃_iY_i` of cubes,
`Σ_i d(Y_i; D ∩ Y_i) + 18#(Z \ ⋃_iY_i) ≥ d(Z; D)`. -/
theorem contracted_ii {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : Finset g.Idx} (hZ : g.Conn Z)
    (Y : ι → Finset g.Idx) (hY : ∀ i, g.Conn (Y i)) (hYZ : ∀ i, Y i ⊆ Z)
    (hsep : ∀ i j, i ≠ j → ∀ c ∈ Y i, ∀ c' ∈ Y j, c ≠ c' ∧ ¬ (wallGraph (ZMod g.n)).Adj c c')
    (D : Finset g.Idx) (hD : D ⊆ Finset.univ.biUnion Y) :
    g.d Z D ≤ ∑ i, g.d (Y i) (D ∩ Y i) + 18 * (Z \ Finset.univ.biUnion Y).card := by
  classical
  have ha := g.ha
  set U := Finset.univ.biUnion Y with hU
  set Fr := Z \ U with hFr
  have hUZ : U ⊆ Z := Finset.biUnion_subset.2 fun i _ => hYZ i
  have hne := exists_adm (g := g) hZ (hD.trans hUZ)
  have huniq : ∀ i j c, c ∈ Y i → c ∈ Y j → i = j := fun i j c hi hj => by
    by_contra hij; exact (hsep i j hij c hi c hj).1 rfl
  have hfree : ∀ q, q ∈ Fr → ¬ ∃ i, q ∈ Y i := fun q hq ⟨i, hi⟩ =>
    (Finset.mem_sdiff.1 hq).2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set δ' := δ / (Fintype.card ι + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  choose GS hGS using fun i => exists_adm_le (exists_adm (hY i) (Finset.inter_subset_right (s₁ := D)))
    hδ'0
  -- points of the families in their cubes
  have hpt : ∀ i c, ∃ z, c ∈ Y i → z ∈ (⋃ σ ∈ GS i, segSet g.s g.N σ) ∧ z ∈ g.cube c := fun i c => by
    by_cases hc : c ∈ Y i
    · obtain ⟨σ, hσ, z, hz1, hz2⟩ := (hGS i).1.2.1 c hc
      exact ⟨z, fun _ => ⟨mem_iUnion₂.2 ⟨σ, hσ, hz1⟩, hz2⟩⟩
    · exact ⟨g.centre c, fun h => absurd h hc⟩
  choose ptG hptG using hpt
  -- the targets of the segments from the corners
  set target : g.Idx → Fin 4 × Bool → g.T := fun q p =>
    if h : ∃ i, wallNbr (ZMod g.n) q p ∈ Y i then ptG h.choose (wallNbr (ZMod g.n) q p)
    else g.centre (wallNbr (ZMod g.n) q p) with htarget
  have htarget_mem : ∀ q p, target q p ∈ g.cube (wallNbr (ZMod g.n) q p) := fun q p => by
    simp only [htarget]
    split_ifs with h
    · exact (hptG _ _ h.choose_spec).2
    · exact centre_mem_cube _
  choose segF hsegF using fun q p => exists_seg_cube (corner_mem_nbr (g := g) q p) (htarget_mem q p)
  -- the anchors of the cubes
  set Ai : ι → Set g.T := fun i => (⋃ σ ∈ GS i, segSet g.s g.N σ) ∪ g.cubes (D ∩ Y i) with hAi
  set W : g.Idx → Finset (Fin 4 × Bool) := fun q => Finset.univ.filter fun p => wallNbr (ZMod g.n) q p ∈ Z
    with hW
  set Af : g.Idx → Set g.T := fun q => segSet g.s g.N (g.diag q) ∪ ⋃ p ∈ W q, segSet g.s g.N (segF q p)
    with hAf
  set anchor : g.Idx → Set g.T := fun q => if h : ∃ i, q ∈ Y i then Ai h.choose else Af q with hanchor
  have hanchor_Y : ∀ i q, q ∈ Y i → anchor q = Ai i := fun i q hq => by
    have h : ∃ i, q ∈ Y i := ⟨i, hq⟩
    simp only [hanchor, dif_pos h]
    rw [huniq _ _ _ h.choose_spec hq]
  have hanchor_free : ∀ q, (¬ ∃ i, q ∈ Y i) → anchor q = Af q := fun q h => by
    simp only [hanchor, dif_neg h]
  have hAi_pre : ∀ i, IsPreconnected (Ai i) := fun i => (hGS i).1.2.2
  have hAf_pre : ∀ q, IsPreconnected (Af q) := fun q =>
    isPreconnected_hub (isPreconnected_segSet' _) (W q) (fun p => segSet g.s g.N (segF q p))
      (fun p _ => isPreconnected_segSet' _) fun p _ => ⟨g.corner q p, (hsegF q p).2.1, corner_mem_diag q p⟩
  have hanchor_pre : ∀ q, IsPreconnected (anchor q) := fun q => by
    by_cases h : ∃ i, q ∈ Y i
    · obtain ⟨i, hi⟩ := h; rw [hanchor_Y i q hi]; exact hAi_pre i
    · rw [hanchor_free q h]; exact hAf_pre q
  have hseg_in_Af : ∀ q p, wallNbr (ZMod g.n) q p ∈ Z → segSet g.s g.N (segF q p) ⊆ Af q := fun q p hp =>
    fun z hz => Or.inr (mem_iUnion₂.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩, hz⟩)
  -- adjacent cubes have meeting anchors
  have hmeet : ∀ q ∈ Z, ∀ q' ∈ Z, (wallGraph (ZMod g.n)).Adj q q' → (anchor q ∩ anchor q').Nonempty := by
    -- a free cube and its neighbour across the wall `p`
    have hfree_nbr : ∀ q p, (¬ ∃ i, q ∈ Y i) → wallNbr (ZMod g.n) q p ∈ Z →
        (anchor q ∩ anchor (wallNbr (ZMod g.n) q p)).Nonempty := fun q p hq hpZ => by
      refine ⟨target q p, by rw [hanchor_free q hq]; exact hseg_in_Af q p hpZ (hsegF q p).2.2.1, ?_⟩
      by_cases h : ∃ i, wallNbr (ZMod g.n) q p ∈ Y i
      · have ht : target q p = ptG h.choose (wallNbr (ZMod g.n) q p) := by simp only [htarget, dif_pos h]
        rw [ht, hanchor_Y _ _ h.choose_spec]
        exact Or.inl (hptG _ _ h.choose_spec).1
      · have ht : target q p = g.centre (wallNbr (ZMod g.n) q p) := by simp only [htarget, dif_neg h]
        rw [ht, hanchor_free _ h]
        exact Or.inl (centre_mem_diag _)
    intro q hq q' hq' hadj
    by_cases h : ∃ i, q ∈ Y i
    · by_cases h' : ∃ i, q' ∈ Y i
      · obtain ⟨i, hi⟩ := h
        obtain ⟨j, hj⟩ := h'
        have hij : i = j := by
          by_contra hij; exact (hsep i j hij q hi q' hj).2 hadj
        subst hij
        rw [hanchor_Y i q hi, hanchor_Y i q' hj, inter_self]
        exact ⟨ptG i q, Or.inl (hptG i q hi).1⟩
      · obtain ⟨-, p, hp⟩ := hadj.symm
        have := hfree_nbr q' p h' (hp ▸ hq)
        rw [← hp] at this
        rwa [inter_comm] at this
    · obtain ⟨-, p, hp⟩ := hadj
      have := hfree_nbr q p h (hp ▸ hq')
      rwa [← hp] at this
  have hconn_anchor : IsPreconnected (⋃ q ∈ Z, anchor q) := by
    rw [← Finset.set_biUnion_coe]
    refine IsPreconnected.biUnion_of_reflTransGen (fun q _ => hanchor_pre q) fun q hq q' hq' => ?_
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
      (SimpleGraph.Connected.preconnected hZ ⟨q, hq⟩ ⟨q', hq'⟩)
    exact Relation.ReflTransGen.lift (p := fun a b => (anchor a ∩ anchor b).Nonempty ∧ a ∈ (Z : Set g.Idx))
      (fun v : (Z : Set g.Idx) => v.1) (fun v w hvw => ⟨hmeet v.1 v.2 w.1 w.2 hvw, v.2⟩) _ _ hr
  -- the family
  set E := (Fr ×ˢ (Finset.univ : Finset (Fin 4 × Bool))).filter fun x => wallNbr (ZMod g.n) x.1 x.2 ∈ Z
    with hE
  set S := Finset.univ.biUnion GS ∪ Fr.image g.diag ∪ E.image (fun x => segF x.1 x.2) with hS
  have hSeq : (⋃ σ ∈ S, segSet g.s g.N σ) ∪ g.cubes D = ⋃ q ∈ Z, anchor q := by
    apply Subset.antisymm
    · rintro z (hz | hz)
      · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hz
        rcases Finset.mem_union.1 hσ with hσ | hσ
        · rcases Finset.mem_union.1 hσ with hσ | hσ
          · obtain ⟨i, -, hσi⟩ := Finset.mem_biUnion.1 hσ
            obtain ⟨q, hq⟩ := Conn.nonempty (hY i)
            refine mem_iUnion₂.2 ⟨q, hYZ i hq, ?_⟩
            rw [hanchor_Y i q hq]
            exact Or.inl (mem_iUnion₂.2 ⟨σ, hσi, hzσ⟩)
          · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hσ
            refine mem_iUnion₂.2 ⟨q, (Finset.mem_sdiff.1 hq).1, ?_⟩
            rw [hanchor_free q (hfree q hq)]
            exact Or.inl hzσ
        · obtain ⟨⟨q, p⟩, hx, rfl⟩ := Finset.mem_image.1 hσ
          rw [hE, Finset.mem_filter, Finset.mem_product] at hx
          refine mem_iUnion₂.2 ⟨q, (Finset.mem_sdiff.1 hx.1.1).1, ?_⟩
          rw [hanchor_free q (hfree q hx.1.1)]
          exact hseg_in_Af q p hx.2 hzσ
      · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 hz
        obtain ⟨i, -, hdi⟩ := Finset.mem_biUnion.1 (hD hd)
        refine mem_iUnion₂.2 ⟨d, hYZ i hdi, ?_⟩
        rw [hanchor_Y i d hdi]
        exact Or.inr (mem_iUnion₂.2 ⟨d, Finset.mem_inter.2 ⟨hd, hdi⟩, hzd⟩)
    · intro z hz
      obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz
      by_cases h : ∃ i, q ∈ Y i
      · obtain ⟨i, hi⟩ := h
        rw [hanchor_Y i q hi] at hzq
        rcases hzq with hzq | hzq
        · obtain ⟨σ, hσ, hzσ⟩ := mem_iUnion₂.1 hzq
          exact Or.inl (mem_iUnion₂.2 ⟨σ, Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hσ⟩)), hzσ⟩)
        · exact Or.inr (cubes_mono Finset.inter_subset_left hzq)
      · have hqFr : q ∈ Fr := Finset.mem_sdiff.2 ⟨hq, fun hU' => by
          obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hU'; exact h ⟨i, hi⟩⟩
        rw [hanchor_free q h] at hzq
        rcases hzq with hzq | hzq
        · exact Or.inl (mem_iUnion₂.2 ⟨g.diag q, Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_image_of_mem _ hqFr)), hzq⟩)
        · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hzq
          refine Or.inl (mem_iUnion₂.2 ⟨segF q p, Finset.mem_union_right _ (Finset.mem_image.2
            ⟨(q, p), ?_, rfl⟩), hzp⟩)
          rw [hE, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hqFr, Finset.mem_univ _⟩, (Finset.mem_filter.1 hp).2⟩
  have hAdm : g.Adm Z D S := by
    refine ⟨fun σ hσ => ?_, fun c hc => ?_, by rw [hSeq]; exact hconn_anchor⟩
    · rcases Finset.mem_union.1 hσ with hσ | hσ
      · rcases Finset.mem_union.1 hσ with hσ | hσ
        · obtain ⟨i, -, hσi⟩ := Finset.mem_biUnion.1 hσ
          exact ((hGS i).1.1 σ hσi).trans (cubes_mono (hYZ i))
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hσ
          exact (diag_subset q).trans (cube_subset_cubes (Finset.mem_sdiff.1 hq).1)
      · obtain ⟨⟨q, p⟩, hx, rfl⟩ := Finset.mem_image.1 hσ
        rw [hE, Finset.mem_filter] at hx
        exact (hsegF q p).1.trans (cube_subset_cubes hx.2)
    · by_cases h : ∃ i, c ∈ Y i
      · obtain ⟨i, hi⟩ := h
        obtain ⟨σ, hσ, hz⟩ := (hGS i).1.2.1 c hi
        exact ⟨σ, Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hσ⟩)), hz⟩
      · have hcFr : c ∈ Fr := Finset.mem_sdiff.2 ⟨hc, fun hU' => by
          obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hU'; exact h ⟨i, hi⟩⟩
        exact ⟨g.diag c, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hcFr)),
          g.centre c, centre_mem_diag c, centre_mem_cube c⟩
  -- the cost
  have hcost : g.cost D S ≤ ∑ i, g.a * (g.d (Y i) (D ∩ Y i) + δ') + 18 * g.a * Fr.card := by
    have hl0 : ∀ σ, 0 ≤ lenOut g.s g.N (g.cubes D) σ := fun σ => lenOut_nonneg _ σ
    have h1 : ∑ σ ∈ Finset.univ.biUnion GS, lenOut g.s g.N (g.cubes D) σ ≤
        ∑ i, g.a * (g.d (Y i) (D ∩ Y i) + δ') := by
      refine (sum_biUnion_le' _ _ hl0).trans (Finset.sum_le_sum fun i _ => ?_)
      exact le_trans (Finset.sum_le_sum fun σ _ => lenOut_anti (cubes_mono Finset.inter_subset_left) σ)
        (hGS i).2
    have h2 : ∑ σ ∈ Fr.image g.diag, lenOut g.s g.N (g.cubes D) σ ≤ 2 * g.a * Fr.card := by
      refine (sum_image_le' _ _ hl0).trans ?_
      refine (Finset.sum_le_sum fun q _ => (lenOut_le_eu _ _).trans (eu_diag_le q)).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]; linarith
    have h3 : ∑ σ ∈ E.image (fun x => segF x.1 x.2), lenOut g.s g.N (g.cubes D) σ ≤ 16 * g.a * Fr.card := by
      refine (sum_image_le' _ _ hl0).trans ?_
      have hle : ∀ x ∈ E, lenOut g.s g.N (g.cubes D) (segF x.1 x.2) ≤ 2 * g.a := fun x _ =>
        (lenOut_le_eu _ _).trans (hsegF x.1 x.2).2.2.2
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hEc : (E.card : ℝ) ≤ 8 * Fr.card := by
        have := (Finset.card_le_card (Finset.filter_subset _ _ : E ⊆ Fr ×ˢ Finset.univ)).trans
          (le_of_eq (Finset.card_product Fr (Finset.univ : Finset (Fin 4 × Bool))))
        have h8 : (Finset.univ : Finset (Fin 4 × Bool)).card = 8 := by simp
        rw [h8] at this
        exact_mod_cast this.trans (le_of_eq (mul_comm _ _))
      nlinarith
    unfold cost
    refine (sum_union_le' _ _ hl0).trans ?_
    refine (add_le_add (sum_union_le' _ _ hl0) le_rfl).trans ?_
    linarith only [h1, h2, h3]
  have hmain := (a_mul_d_le hAdm).trans hcost
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hmain
  have hdiv : g.d Z D ≤ ∑ i, g.d (Y i) (D ∩ Y i) + Fintype.card ι * δ' + 18 * Fr.card := by
    have : g.a * g.d Z D ≤ g.a * (∑ i, g.d (Y i) (D ∩ Y i) + Fintype.card ι * δ' + 18 * Fr.card) := by
      nlinarith
    exact le_of_mul_le_mul_left this ha
  have hδle : (Fintype.card ι : ℝ) * δ' ≤ δ := by
    rw [hδ', mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### Agreement with `lem:cube-count` -/

/-- The grid of side `s` with `N` cubes per direction, the grid of `CubeCountTorus.lean`. -/
def unitGrid (s : ℝ) (N : ℕ) [NeZero N] (hs : 0 < s) : Grid :=
  ⟨s, N, s, N, hs, rfl, inferInstance⟩

/-- `d(X) = d(X; ∅)` is the linear size `size s N X` of `lem:cube-count`. -/
theorem d_empty_eq_size (s : ℝ) (N : ℕ) [NeZero N] (hs : 0 < s) (X : Finset (Fin 4 → ZMod N)) :
    (unitGrid s N hs).d X ∅ = size s N X := by
  have hcost : ∀ S : Finset Seg, (unitGrid s N hs).cost ∅ S = ∑ σ ∈ S, eu σ.2 := fun S => by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have e : (unitGrid s N hs).cubes ∅ = ∅ := cubes_empty
    rw [e]
    have hv : volume {θ ∈ Icc (0 : ℝ) 1 | proj s N (σ.1 + θ • σ.2) ∉ (∅ : Set (Torus s N))} = 1 := by
      simp only [mem_empty_iff_false, not_false_eq_true, and_true]
      rw [setOf_mem_eq, Real.volume_Icc]; simp
    unfold lenOut
    erw [hv]
    rw [ENNReal.toReal_one, mul_one]
  have hadm : ∀ S : Finset Seg, (unitGrid s N hs).Adm X ∅ S ↔ Admissible s N X S := fun S => by
    have e : (unitGrid s N hs).cubes ∅ = ∅ := cubes_empty
    unfold Adm Admissible
    rw [e, union_empty]
    rfl
  unfold d size
  congr 2
  ext t
  simp only [mem_image, mem_setOf_eq, hcost, hadm]

/-- Two cubes touch, in the sense of `def:localisation`(i), if and only if they have a point in common. -/
theorem touch_iff_inter {c c' : g.Idx} : Touch c c' ↔ (g.cube c ∩ g.cube c').Nonempty := by
  refine ⟨touch_inter, fun ⟨z, hz1, hz2⟩ => touch_of_dist_lt ?_⟩
  have h1 := Metric.mem_closedBall.1 hz1
  have h2 := Metric.mem_closedBall.1 hz2
  have ha := g.ha
  calc dist (g.centre c) (g.centre c') ≤ dist (g.centre c) z + dist z (g.centre c') := dist_triangle _ _ _
    _ ≤ g.a / 2 + g.a / 2 := by rw [dist_comm (g.centre c) z]; exact add_le_add h1 h2
    _ < 2 * g.a := by linarith

end Grid
end Contracted
end CoreLean

end
