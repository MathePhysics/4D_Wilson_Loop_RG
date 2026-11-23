import GaussianBlockSpin.PowerCountingSpatial

/-! **Multiscale power counting** (the core of III Propositions 2.1, 2.2). Setting: a multigraph whose lines connect
all vertices, every vertex on a line; lines carry scale indices `j_l < k`, line factors `L^{(j_l - k)(-ω_l)}` and
weights `w_l ≤ 1` with `∫ w_l(y, ·) dν ≤ C₀ L^{(j_l - k) d}` and `∫ w_l(·, y) dν ≤ C₀ L^{(j_l - k) d}`; vertex
factors at most `L^{(j_l - k) a_v}` for the lines `l` at `v` of lowest scale (III (2.14) attaches the vertex power at
`j(v)`, the lowest index at `v`); one vertex lies in a set of measure at most one.
* power_counting_ordering: for one ordering `σ`, if every prefix sum of the power-counting coefficients of `σ` is at
  least `p₀ > 0`, the sum over the scale tuples nondecreasing along `σ` and over the positions is at most
  `max(1, C₀)^m (1 - L^{-p₀})^{-m}`, uniformly in `k` (the form needed when the graph depends on the ordering, as
  after III's integration by parts (2.8)-(2.9));
* power_counting: if this holds for every ordering, the sum over all scale assignments is at most
  `m! max(1, C₀)^m (1 - L^{-p₀})^{-m}`. -/

namespace GaussianBlockSpin

open MeasureTheory MergeTree
open scoped ENNReal

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]

/-- The line `l` is incident to the vertex `v`. -/
def Incident (ends : E → V × V) (l : E) (v : V) : Prop := (ends l).1 = v ∨ (ends l).2 = v

open Classical in
/-- The power-counting coefficient of the `i`-th line of an ordering: `d` for a tree line, plus the exponents of the
vertices first touched by it, minus its dimension `ω`. -/
noncomputable def pcCoef (ends : E → V × V) (d : ℕ) (a : V → ℝ) (ω : E → ℝ) (σ : Fin (Fintype.card E) ≃ E)
    (i : Fin (Fintype.card E)) : ℝ :=
  d * (if σ i ∈ treeLines ends (List.ofFn σ) then 1 else 0) +
    ∑ v ∈ Finset.univ.filter (fun v => Incident ends (σ i) v ∧ ∀ i' < i, ¬ Incident ends (σ i') v), a v - ω (σ i)

omit [DecidableEq V] [Fintype V] [DecidableEq E] in
lemma incident_filter_nonempty {ends : E → V × V} (σ : Fin (Fintype.card E) ≃ E) {v : V}
    (hv : ∃ l, Incident ends l v) [DecidablePred fun i => Incident ends (σ i) v] :
    (Finset.univ.filter fun i => Incident ends (σ i) v).Nonempty := by
  obtain ⟨l, hl⟩ := hv
  exact ⟨σ.symm l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hl⟩⟩

open Classical in
/-- The first position of the ordering whose line is incident to `v`. -/
noncomputable def firstIdx (ends : E → V × V) (σ : Fin (Fintype.card E) ≃ E) (v : V) (hv : ∃ l, Incident ends l v) :
    Fin (Fintype.card E) :=
  (Finset.univ.filter fun i => Incident ends (σ i) v).min' (incident_filter_nonempty σ hv)

omit [DecidableEq V] [Fintype V] [DecidableEq E] in
lemma firstIdx_spec {ends : E → V × V} (σ : Fin (Fintype.card E) ≃ E) {v : V} (hv : ∃ l, Incident ends l v)
    (i : Fin (Fintype.card E)) :
    firstIdx ends σ v hv = i ↔ Incident ends (σ i) v ∧ ∀ i' < i, ¬ Incident ends (σ i') v := by
  classical
  have hne := incident_filter_nonempty (ends := ends) σ hv
  unfold firstIdx
  constructor
  · rintro rfl
    refine ⟨(Finset.mem_filter.mp (Finset.min'_mem _ hne)).2, fun i' hi' hinc => ?_⟩
    exact absurd (Finset.min'_le _ i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩)) (not_le.mpr hi')
  · rintro ⟨hinc, hmin⟩
    refine le_antisymm (Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩)) ?_
    by_contra hlt
    push Not at hlt
    exact hmin _ hlt (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2

omit [DecidableEq V] [Fintype V] [DecidableEq E] in
lemma incident_firstIdx {ends : E → V × V} (σ : Fin (Fintype.card E) ≃ E) {v : V} (hv : ∃ l, Incident ends l v) :
    Incident ends (σ (firstIdx ends σ v hv)) v :=
  ((firstIdx_spec σ hv _).mp rfl).1

omit [DecidableEq V] [Fintype V] [DecidableEq E] in
lemma firstIdx_le {ends : E → V × V} (σ : Fin (Fintype.card E) ≃ E) {v : V} (hv : ∃ l, Incident ends l v)
    {i : Fin (Fintype.card E)} (hi : Incident ends (σ i) v) : firstIdx ends σ v hv ≤ i := by
  classical
  unfold firstIdx
  exact Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

variable {ends : E → V × V} {L : ℝ} {k : ℕ}

omit [DecidableEq V] [DecidableEq E] in
open Classical in
/-- **The vertex factors** are collected at the first line of the ordering touching each vertex; on scale tuples
nondecreasing along the ordering, it is a line of lowest scale at the vertex. -/
lemma prod_vertex_le (hL : 0 < L) (hinc : ∀ v, ∃ l, Incident ends l v) (a : V → ℝ) (A : V → (E → ℕ) → ℝ≥0∞)
    (hA : ∀ v j l, Incident ends l v → (∀ l', Incident ends l' v → j l ≤ j l') →
      A v j ≤ ENNReal.ofReal (L ^ (((j l : ℝ) - k) * a v)))
    (σ : Fin (Fintype.card E) ≃ E) {u : Fin (Fintype.card E) → ℕ} (hu : Monotone u) :
    ∏ v, A v (fun l => u (σ.symm l)) ≤ ENNReal.ofReal (∏ i, L ^ (((u i : ℝ) - k) *
      ∑ v ∈ Finset.univ.filter (fun v => Incident ends (σ i) v ∧ ∀ i' < i, ¬ Incident ends (σ i') v), a v)) := by
  set f := fun v => firstIdx ends σ v (hinc v)
  calc ∏ v, A v (fun l => u (σ.symm l)) ≤ ∏ v, ENNReal.ofReal (L ^ (((u (f v) : ℝ) - k) * a v)) := by
        refine Finset.prod_le_prod fun v _ => ?_
        have hmin : ∀ l', Incident ends l' v → u (σ.symm (σ (f v))) ≤ u (σ.symm l') := fun l' hl' => by
          rw [Equiv.symm_apply_apply]
          exact hu (firstIdx_le σ (hinc v) (by simpa using hl'))
        have h := hA v (fun l => u (σ.symm l)) (σ (f v)) (incident_firstIdx σ (hinc v)) hmin
        simpa using h
    _ = ENNReal.ofReal (∏ v, L ^ (((u (f v) : ℝ) - k) * a v)) :=
        (ENNReal.ofReal_prod_of_nonneg fun v _ => (Real.rpow_pos_of_pos hL _).le).symm
    _ = _ := by
        congr 1
        rw [← Finset.prod_fiberwise Finset.univ f]
        refine Finset.prod_congr rfl fun i _ => ?_
        have hfilt : Finset.univ.filter (fun v => f v = i) = Finset.univ.filter
            (fun v => Incident ends (σ i) v ∧ ∀ i' < i, ¬ Incident ends (σ i') v) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact firstIdx_spec σ (hinc v) i
        rw [hfilt, Finset.mul_sum, ← Real.rpow_sum_of_pos hL]
        congr 1
        refine Finset.sum_congr rfl fun v hv => ?_
        have hfv : f v = i := (firstIdx_spec σ (hinc v) i).mpr (Finset.mem_filter.mp hv).2
        rw [hfv]

omit [DecidableEq V] [Fintype V] in
open Classical in
/-- **The tree-line factors**. -/
lemma prod_treeLines_le (hL : 0 < L) (d : ℕ) (C₀ : ℝ≥0∞) (σ : Fin (Fintype.card E) ≃ E)
    (u : Fin (Fintype.card E) → ℕ) :
    ((treeLines ends (List.ofFn σ)).map fun l => C₀ * ENNReal.ofReal (L ^ (((u (σ.symm l) : ℝ) - k) * d))).prod ≤
      (max 1 C₀) ^ Fintype.card E * ENNReal.ofReal (∏ i, if σ i ∈ treeLines ends (List.ofFn σ) then
        L ^ (((u i : ℝ) - k) * d) else 1) := by
  set TL := treeLines ends (List.ofFn σ) with hTL
  have hsub := treeLines_sublist ends (List.ofFn σ)
  have hnd : TL.Nodup := hsub.nodup (List.nodup_ofFn.mpr σ.injective)
  have hlen : TL.length ≤ Fintype.card E := by simpa using hsub.length_le
  rw [List.prod_map_mul, List.map_const', List.prod_replicate]
  refine mul_le_mul' ?_ (le_of_eq ?_)
  · calc C₀ ^ TL.length ≤ (max 1 C₀) ^ TL.length := pow_le_pow_left₀ bot_le (le_max_right _ _) _
      _ ≤ (max 1 C₀) ^ Fintype.card E := pow_le_pow_right₀ (le_max_left _ _) hlen
  · rw [← List.prod_toFinset _ hnd, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.rpow_pos_of_pos hL _).le)]
    congr 1
    have h1 : TL.toFinset = Finset.univ.filter (fun l => l ∈ TL) := by ext l; simp
    rw [h1, Finset.prod_filter, ← Equiv.prod_comp σ]
    simp

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X] {ν : Measure X} [SigmaFinite ν]

open Classical in
/-- The bound for one ordering and one scale tuple nondecreasing along it. -/
lemma term_le_ordering {d : ℕ} (hL : 1 < L)
    (hconn : ∀ u v, lineConn ends (Finset.univ : Finset E).toList u v) (hinc : ∀ v, ∃ l, Incident ends l v)
    (w : E → ℕ → X → X → ℝ≥0∞) (hw1 : ∀ l t x y, w l t x y ≤ 1) (C₀ : ℝ≥0∞)
    (hC₁ : ∀ l t y, ∫⁻ x', w l t y x' ∂ν ≤ C₀ * ENNReal.ofReal (L ^ (((t : ℝ) - k) * d)))
    (hC₂ : ∀ l t y, ∫⁻ x', w l t x' y ∂ν ≤ C₀ * ENNReal.ofReal (L ^ (((t : ℝ) - k) * d)))
    (ω : E → ℝ) (a : V → ℝ) (A : V → (E → ℕ) → ℝ≥0∞)
    (hA : ∀ v j l, Incident ends l v → (∀ l', Incident ends l' v → j l ≤ j l') →
      A v j ≤ ENNReal.ofReal (L ^ (((j l : ℝ) - k) * a v)))
    (v₀ : V) (box : Set X) (hbox : ν box ≤ 1) (x₀ : V → X) (σ : Fin (Fintype.card E) ≃ E)
    {u : Fin (Fintype.card E) → ℕ} (hu : Monotone u) :
    (∏ v, A v (fun l => u (σ.symm l))) * (∏ l, ENNReal.ofReal (L ^ (((u (σ.symm l) : ℝ) - k) * (-ω l)))) *
        (∫⋯∫⁻_(Finset.univ), (fun x => box.indicator 1 (x v₀) *
          ∏ l, w l (u (σ.symm l)) (x (ends l).1) (x (ends l).2)) ∂(fun _ => ν)) x₀ ≤
      (max 1 C₀) ^ Fintype.card E * ENNReal.ofReal (∏ i, L ^ (pcCoef ends d a ω σ i * ((u i : ℝ) - k))) := by
  have hL0 : 0 < L := by linarith
  have hsp := lmarginal_lines_le_treeLines (ν := ν) hconn σ (fun l => w l (u (σ.symm l)))
    (fun l => hw1 l _) (fun l => C₀ * ENNReal.ofReal (L ^ (((u (σ.symm l) : ℝ) - k) * d)))
    (fun l y => hC₁ l _ y) (fun l y => hC₂ l _ y) v₀ box hbox x₀
  have hT := prod_treeLines_le (ends := ends) (k := k) hL0 d C₀ σ u
  have hV := prod_vertex_le (k := k) hL0 hinc a A hA σ hu
  have hW : ∏ l, ENNReal.ofReal (L ^ (((u (σ.symm l) : ℝ) - k) * (-ω l))) =
      ENNReal.ofReal (∏ i, L ^ (((u i : ℝ) - k) * (-ω (σ i)))) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.rpow_pos_of_pos hL0 _).le), ← Equiv.prod_comp σ]
    simp
  calc (∏ v, A v (fun l => u (σ.symm l))) * (∏ l, ENNReal.ofReal (L ^ (((u (σ.symm l) : ℝ) - k) * (-ω l)))) *
        (∫⋯∫⁻_(Finset.univ), (fun x => box.indicator 1 (x v₀) *
          ∏ l, w l (u (σ.symm l)) (x (ends l).1) (x (ends l).2)) ∂(fun _ => ν)) x₀
      ≤ ENNReal.ofReal (∏ i, L ^ (((u i : ℝ) - k) * ∑ v ∈ Finset.univ.filter
            (fun v => Incident ends (σ i) v ∧ ∀ i' < i, ¬ Incident ends (σ i') v), a v)) *
          ENNReal.ofReal (∏ i, L ^ (((u i : ℝ) - k) * (-ω (σ i)))) *
          ((max 1 C₀) ^ Fintype.card E * ENNReal.ofReal (∏ i, if σ i ∈ treeLines ends (List.ofFn σ) then
            L ^ (((u i : ℝ) - k) * d) else 1)) :=
        mul_le_mul' (mul_le_mul' hV hW.le) (hsp.trans hT)
    _ = (max 1 C₀) ^ Fintype.card E * ENNReal.ofReal ((∏ i, L ^ (((u i : ℝ) - k) * ∑ v ∈ Finset.univ.filter
            (fun v => Incident ends (σ i) v ∧ ∀ i' < i, ¬ Incident ends (σ i') v), a v)) *
          (∏ i, L ^ (((u i : ℝ) - k) * (-ω (σ i)))) *
          (∏ i, if σ i ∈ treeLines ends (List.ofFn σ) then L ^ (((u i : ℝ) - k) * d) else 1)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ = (max 1 C₀) ^ Fintype.card E *
          ENNReal.ofReal (∏ i, L ^ (pcCoef ends d a ω σ i * ((u i : ℝ) - k))) := by
        congr 2
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        unfold pcCoef
        split_ifs
        · rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
        · rw [mul_one, ← Real.rpow_add hL0]; congr 1; ring

open Classical in
/-- **Multiscale power counting for one ordering.** -/
theorem power_counting_ordering {d : ℕ} (hL : 1 < L) (hk : 1 ≤ k)
    (hconn : ∀ u v, lineConn ends (Finset.univ : Finset E).toList u v) (hinc : ∀ v, ∃ l, Incident ends l v)
    (w : E → ℕ → X → X → ℝ≥0∞) (hw1 : ∀ l t x y, w l t x y ≤ 1) (C₀ : ℝ≥0∞)
    (hC₁ : ∀ l t y, ∫⁻ x', w l t y x' ∂ν ≤ C₀ * ENNReal.ofReal (L ^ (((t : ℝ) - k) * d)))
    (hC₂ : ∀ l t y, ∫⁻ x', w l t x' y ∂ν ≤ C₀ * ENNReal.ofReal (L ^ (((t : ℝ) - k) * d)))
    (ω : E → ℝ) (a : V → ℝ) (A : V → (E → ℕ) → ℝ≥0∞)
    (hA : ∀ v j l, Incident ends l v → (∀ l', Incident ends l' v → j l ≤ j l') →
      A v j ≤ ENNReal.ofReal (L ^ (((j l : ℝ) - k) * a v)))
    (σ : Fin (Fintype.card E) ≃ E) {p₀ : ℝ} (hp₀ : 0 < p₀) (hdeg : ∀ i, p₀ ≤ prefixSum (pcCoef ends d a ω σ) i)
    (v₀ : V) (box : Set X) (hbox : ν box ≤ 1) (x₀ : V → X) :
    ∑ u ∈ monoSet (Fintype.card E) (k - 1),
      (∏ v, A v (fun l => u (σ.symm l))) * (∏ l, ENNReal.ofReal (L ^ (((u (σ.symm l) : ℝ) - k) * (-ω l)))) *
        (∫⋯∫⁻_(Finset.univ), (fun x => box.indicator 1 (x v₀) *
          ∏ l, w l (u (σ.symm l)) (x (ends l).1) (x (ends l).2)) ∂(fun _ => ν)) x₀ ≤
      (max 1 C₀) ^ Fintype.card E * ENNReal.ofReal (((1 - L ^ (-p₀))⁻¹) ^ Fintype.card E) := by
  have hL0 : 0 < L := by linarith
  calc _ ≤ ∑ u ∈ monoSet (Fintype.card E) (k - 1), (max 1 C₀) ^ Fintype.card E *
          ENNReal.ofReal (∏ i, L ^ (pcCoef ends d a ω σ i * ((u i : ℝ) - k))) :=
        Finset.sum_le_sum fun u hu => term_le_ordering hL hconn hinc w hw1 C₀ hC₁ hC₂ ω a A hA v₀ box hbox x₀ σ
          (mem_monoSet.mp hu).2
    _ = (max 1 C₀) ^ Fintype.card E * ENNReal.ofReal (∑ u ∈ monoSet (Fintype.card E) (k - 1),
          ∏ i, L ^ (pcCoef ends d a ω σ i * ((u i : ℝ) - k))) := by
        rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun u _ =>
          Finset.prod_nonneg fun i _ => (Real.rpow_pos_of_pos hL0 _).le]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (sum_monoSet_rpow_le hL hk _ hp₀ hdeg)) bot_le

open Classical in
/-- **Multiscale power counting.** -/
theorem power_counting {d : ℕ} (hL : 1 < L) (hk : 1 ≤ k)
    (hconn : ∀ u v, lineConn ends (Finset.univ : Finset E).toList u v) (hinc : ∀ v, ∃ l, Incident ends l v)
    (w : E → ℕ → X → X → ℝ≥0∞) (hw1 : ∀ l t x y, w l t x y ≤ 1) (C₀ : ℝ≥0∞)
    (hC₁ : ∀ l t y, ∫⁻ x', w l t y x' ∂ν ≤ C₀ * ENNReal.ofReal (L ^ (((t : ℝ) - k) * d)))
    (hC₂ : ∀ l t y, ∫⁻ x', w l t x' y ∂ν ≤ C₀ * ENNReal.ofReal (L ^ (((t : ℝ) - k) * d)))
    (ω : E → ℝ) (a : V → ℝ) (A : V → (E → ℕ) → ℝ≥0∞)
    (hA : ∀ v j l, Incident ends l v → (∀ l', Incident ends l' v → j l ≤ j l') →
      A v j ≤ ENNReal.ofReal (L ^ (((j l : ℝ) - k) * a v)))
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hdeg : ∀ σ i, p₀ ≤ prefixSum (pcCoef ends d a ω σ) i)
    (v₀ : V) (box : Set X) (hbox : ν box ≤ 1) (x₀ : V → X) :
    ∑ j ∈ Fintype.piFinset (fun _ : E => Finset.range k),
      (∏ v, A v j) * (∏ l, ENNReal.ofReal (L ^ (((j l : ℝ) - k) * (-ω l)))) *
        (∫⋯∫⁻_(Finset.univ), (fun x => box.indicator 1 (x v₀) * ∏ l, w l (j l) (x (ends l).1) (x (ends l).2))
          ∂(fun _ => ν)) x₀ ≤
      (Fintype.card E).factorial * ((max 1 C₀) ^ Fintype.card E *
        ENNReal.ofReal (((1 - L ^ (-p₀))⁻¹) ^ Fintype.card E)) := by
  set F : (E → ℕ) → ℝ≥0∞ := fun j => (∏ v, A v j) * (∏ l, ENNReal.ofReal (L ^ (((j l : ℝ) - k) * (-ω l)))) *
    (∫⋯∫⁻_(Finset.univ), (fun x => box.indicator 1 (x v₀) * ∏ l, w l (j l) (x (ends l).1) (x (ends l).2))
      ∂(fun _ => ν)) x₀ with hF
  have hcard : Fintype.card (Fin (Fintype.card E) ≃ E) = (Fintype.card E).factorial := by
    rw [Fintype.card_equiv (Fintype.equivFin E).symm, Fintype.card_fin]
  calc ∑ j ∈ Fintype.piFinset (fun _ : E => Finset.range k), F j
      ≤ ∑ σ : Fin (Fintype.card E) ≃ E, ∑ u ∈ monoSet (Fintype.card E) (k - 1), F (fun l => u (σ.symm l)) :=
        sum_le_sum_orderings F k
    _ ≤ ∑ _σ : Fin (Fintype.card E) ≃ E, (max 1 C₀) ^ Fintype.card E *
          ENNReal.ofReal (((1 - L ^ (-p₀))⁻¹) ^ Fintype.card E) :=
        Finset.sum_le_sum fun σ _ => power_counting_ordering hL hk hconn hinc w hw1 C₀ hC₁ hC₂ ω a A hA σ hp₀
          (hdeg σ) v₀ box hbox x₀
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]

end GaussianBlockSpin
