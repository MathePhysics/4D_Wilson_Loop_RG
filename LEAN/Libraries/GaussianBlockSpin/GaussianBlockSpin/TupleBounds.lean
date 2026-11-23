import Mathlib

/-! Sums over connected tuples of pieces (the counting behind "connected graphs give one volume factor", used to
compare truncated expectations): pieces `X` with supports of size `≤ D` and weights `b_X ≥ 0` with
`Σ_{X ∋ y} b_X ≤ a` for every coordinate `y`.
* sum_uConn_le: tuples connected to a set `U` (no subfamily is cut off from `U` and the rest) weigh at most
  `k! ∏_{i<k} ((|U| + i D) a)`;
* sum_connected_anchor_le: tuples without a split into two parts with disjoint supports and with the `i`-th piece in
  `S` weigh at most `(Σ_{X ∈ S} b_X) (k-1)! ∏_{i<k-1} ((D + i D) a)`. -/

namespace GaussianBlockSpin

variable {ι P : Type*} [DecidableEq ι] [Fintype P] (supp : P → Finset ι)

/-- A tuple is connected to `U` if no nonempty subfamily is disjoint from `U` and from the other pieces. -/
def UConn {k : ℕ} (U : Finset ι) (f : Fin k → P) : Prop :=
  ∀ A : Finset (Fin k), A.Nonempty →
    ¬ Disjoint (A.biUnion fun i => supp (f i)) (U ∪ (Finset.univ \ A).biUnion fun i => supp (f i))

/-- A tuple is connected if it has no split into two nonempty parts with disjoint supports. -/
def TupleConnected {k : ℕ} (f : Fin k → P) : Prop :=
  ∀ A : Finset (Fin k), A.Nonempty → (Finset.univ \ A).Nonempty →
    ¬ Disjoint (A.biUnion fun i => supp (f i)) ((Finset.univ \ A).biUnion fun i => supp (f i))

instance {k : ℕ} (U : Finset ι) (f : Fin k → P) : Decidable (UConn supp U f) := by
  unfold UConn; infer_instance

instance {k : ℕ} (f : Fin k → P) : Decidable (TupleConnected supp f) := by
  unfold TupleConnected; infer_instance

omit [Fintype P] in
/-- Removing a piece `i` that meets `U` from a `U`-connected tuple leaves a tuple connected to `U ∪ supp(f i)`. -/
lemma uConn_succAbove {k : ℕ} {U : Finset ι} {f : Fin (k + 1) → P} (hf : UConn supp U f) (i : Fin (k + 1)) :
    UConn supp (U ∪ supp (f i)) (f ∘ i.succAbove) := by
  intro A hA hdisj
  refine hf (A.map i.succAboveEmb) (hA.map) ?_
  rw [Finset.disjoint_left] at hdisj ⊢
  intro y hy1 hy2
  obtain ⟨j', hj', hyj'⟩ := Finset.mem_biUnion.mp hy1
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hj'
  refine hdisj (Finset.mem_biUnion.mpr ⟨j, hj, hyj'⟩) ?_
  rcases Finset.mem_union.mp hy2 with h | h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  · obtain ⟨m, hm, hym⟩ := Finset.mem_biUnion.mp h
    by_cases hmi : m = i
    · subst hmi; exact Finset.mem_union_left _ (Finset.mem_union_right _ hym)
    · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hmi
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m', ?_, hym⟩)
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hm ⊢
      intro hm'
      exact hm (Finset.mem_map.mpr ⟨m', hm', rfl⟩)

omit [Fintype P] in
/-- A `U`-connected tuple of positive length has a piece meeting `U`. -/
lemma exists_meet_of_uConn {k : ℕ} {U : Finset ι} {f : Fin (k + 1) → P} (hf : UConn supp U f) :
    ∃ i, ¬ Disjoint (supp (f i)) U := by
  by_contra hcon
  push Not at hcon
  refine hf Finset.univ Finset.univ_nonempty ?_
  simp only [Finset.sdiff_self, Finset.biUnion_empty, Finset.union_empty]
  exact (Finset.disjoint_biUnion_left _ _ _).mpr fun i _ => hcon i

variable (b : P → ℝ)

/-- The weight of the pieces meeting `U` is at most `|U| a`. -/
lemma sum_meet_le (hb : ∀ X, 0 ≤ b X) {a : ℝ} (ha : ∀ y, ∑ X ∈ Finset.univ.filter (fun X => y ∈ supp X), b X ≤ a)
    (U : Finset ι) :
    ∑ X ∈ Finset.univ.filter (fun X => ¬ Disjoint (supp X) U), b X ≤ U.card * a := by
  calc ∑ X ∈ Finset.univ.filter (fun X => ¬ Disjoint (supp X) U), b X
      ≤ ∑ X ∈ Finset.univ.filter (fun X => ¬ Disjoint (supp X) U), ∑ y ∈ U, if y ∈ supp X then b X else 0 := by
        refine Finset.sum_le_sum fun X hX => ?_
        obtain ⟨y, hyX, hyU⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hX).2
        calc b X = if y ∈ supp X then b X else 0 := by simp [hyX]
          _ ≤ ∑ y' ∈ U, if y' ∈ supp X then b X else 0 :=
            Finset.single_le_sum (f := fun y' => if y' ∈ supp X then b X else 0)
              (fun y' _ => by split_ifs <;> simp [hb X]) hyU
    _ ≤ ∑ X, ∑ y ∈ U, if y ∈ supp X then b X else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun X _ _ =>
          Finset.sum_nonneg fun y _ => by split_ifs <;> simp [hb X]
    _ = ∑ y ∈ U, ∑ X ∈ Finset.univ.filter (fun X => y ∈ supp X), b X := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_filter]
    _ ≤ ∑ y ∈ U, a := Finset.sum_le_sum fun y _ => ha y
    _ = U.card * a := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The sum over the tuples with a given entry: `Σ_f c(f i, f ∘ succAbove i) = Σ_x Σ_g c(x, g)`. -/
lemma sum_insertNth {k : ℕ} (i : Fin (k + 1)) (c : P → (Fin k → P) → ℝ) :
    ∑ f : Fin (k + 1) → P, c (f i) (f ∘ i.succAbove) = ∑ x : P, ∑ g : Fin k → P, c x g := by
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => P) i).symm _ _ fun f => ?_)
  rfl

/-- **Tuples connected to `U`**: `Σ_{f U-connected} ∏_j b_{f(j)} ≤ k! ∏_{i<k} ((|U| + i D) a)`. -/
theorem sum_uConn_le (hb : ∀ X, 0 ≤ b X) {D : ℕ} (hD : ∀ X, (supp X).card ≤ D) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ y, ∑ X ∈ Finset.univ.filter (fun X => y ∈ supp X), b X ≤ a) (k : ℕ) (U : Finset ι) :
    ∑ f ∈ Finset.univ.filter (fun f : Fin k → P => UConn supp U f), ∏ j, b (f j) ≤
      k.factorial * ∏ i ∈ Finset.range k, ((U.card + i * D : ℝ) * a) := by
  induction k generalizing U with
  | zero =>
    have hall : ∀ f : Fin 0 → P, UConn supp U f := fun f A hA => by
      obtain ⟨j, -⟩ := hA; exact j.elim0
    rw [Finset.filter_true_of_mem fun f _ => hall f]
    simp
  | succ k ih =>
    have hprod : ∀ f : Fin (k + 1) → P, 0 ≤ ∏ j, b (f j) := fun f => Finset.prod_nonneg fun j _ => hb _
    -- each connected tuple has a piece meeting `U`
    have hstep : ∀ f ∈ Finset.univ.filter (fun f : Fin (k + 1) → P => UConn supp U f), ∏ j, b (f j) ≤
        ∑ i, if ¬ Disjoint (supp (f i)) U ∧ UConn supp (U ∪ supp (f i)) (f ∘ i.succAbove)
          then ∏ j, b (f j) else 0 := by
      intro f hf
      have hfc := (Finset.mem_filter.mp hf).2
      obtain ⟨i, hi⟩ := exists_meet_of_uConn supp hfc
      have hterm : (if ¬ Disjoint (supp (f i)) U ∧ UConn supp (U ∪ supp (f i)) (f ∘ i.succAbove)
          then ∏ j, b (f j) else 0) = ∏ j, b (f j) := ite_eq_left_iff.mpr (fun h => absurd ⟨hi, uConn_succAbove supp hfc i⟩ h)
      calc ∏ j, b (f j) = (fun i' => if ¬ Disjoint (supp (f i')) U ∧
            UConn supp (U ∪ supp (f i')) (f ∘ i'.succAbove) then ∏ j, b (f j) else 0) i := hterm.symm
        _ ≤ ∑ i', (fun i' => if ¬ Disjoint (supp (f i')) U ∧
            UConn supp (U ∪ supp (f i')) (f ∘ i'.succAbove) then ∏ j, b (f j) else 0) i' :=
          Finset.single_le_sum (f := fun i' => if ¬ Disjoint (supp (f i')) U ∧
            UConn supp (U ∪ supp (f i')) (f ∘ i'.succAbove) then ∏ j, b (f j) else 0)
            (fun i' _ => by split_ifs <;> simp [hprod f]) (Finset.mem_univ i)
    -- the sum for one removed index
    have hone : ∀ i : Fin (k + 1), ∑ f : Fin (k + 1) → P,
        (if ¬ Disjoint (supp (f i)) U ∧ UConn supp (U ∪ supp (f i)) (f ∘ i.succAbove) then ∏ j, b (f j) else 0) ≤
        U.card * a * (k.factorial * ∏ j ∈ Finset.range k, ((U.card + D + j * D : ℝ) * a)) := by
      intro i
      set c : P → (Fin k → P) → ℝ :=
        fun x g => if ¬ Disjoint (supp x) U ∧ UConn supp (U ∪ supp x) g then b x * ∏ j, b (g j) else 0 with hc
      have hrw : ∀ f : Fin (k + 1) → P,
          (if ¬ Disjoint (supp (f i)) U ∧ UConn supp (U ∪ supp (f i)) (f ∘ i.succAbove) then ∏ j, b (f j) else 0) =
            c (f i) (f ∘ i.succAbove) := by
        intro f
        simp only [hc, Function.comp]
        rw [Fin.prod_univ_succAbove _ i]
      rw [Finset.sum_congr rfl fun f _ => hrw f, sum_insertNth i c]
      have hx : ∀ x : P, ∑ g : Fin k → P,
          (if ¬ Disjoint (supp x) U ∧ UConn supp (U ∪ supp x) g then b x * ∏ j, b (g j) else 0) ≤
          (if ¬ Disjoint (supp x) U then b x else 0) *
            (k.factorial * ∏ j ∈ Finset.range k, ((U.card + D + j * D : ℝ) * a)) := by
        intro x
        by_cases hxU : ¬ Disjoint (supp x) U
        · have hg : ∀ g : Fin k → P, (if ¬ Disjoint (supp x) U ∧ UConn supp (U ∪ supp x) g then
              b x * ∏ j, b (g j) else 0) = b x * (if UConn supp (U ∪ supp x) g then ∏ j, b (g j) else 0) := by
            intro g
            by_cases hgc : UConn supp (U ∪ supp x) g <;> simp [hxU, hgc]
          rw [Finset.sum_congr rfl fun g _ => hg g, ← Finset.mul_sum, ← Finset.sum_filter, ite_eq_left hxU]
          refine mul_le_mul_of_nonneg_left ((ih (U ∪ supp x)).trans ?_) (hb x)
          gcongr with j hj
          have := (Finset.card_union_le U (supp x)).trans (Nat.add_le_add_left (hD x) _)
          exact_mod_cast this
        · simp [hxU]
      calc ∑ x : P, ∑ g : Fin k → P,
            (if ¬ Disjoint (supp x) U ∧ UConn supp (U ∪ supp x) g then b x * ∏ j, b (g j) else 0)
          ≤ ∑ x : P, (if ¬ Disjoint (supp x) U then b x else 0) *
              (k.factorial * ∏ j ∈ Finset.range k, ((U.card + D + j * D : ℝ) * a)) := Finset.sum_le_sum fun x _ => hx x
        _ = (∑ x ∈ Finset.univ.filter (fun X => ¬ Disjoint (supp X) U), b x) *
              (k.factorial * ∏ j ∈ Finset.range k, ((U.card + D + j * D : ℝ) * a)) := by
            rw [← Finset.sum_mul, Finset.sum_filter]
        _ ≤ U.card * a * (k.factorial * ∏ j ∈ Finset.range k, ((U.card + D + j * D : ℝ) * a)) := by
            refine mul_le_mul_of_nonneg_right (sum_meet_le supp b hb ha U) ?_
            exact mul_nonneg (by positivity) (Finset.prod_nonneg fun j _ => mul_nonneg (by positivity) ha0)
    calc ∑ f ∈ Finset.univ.filter (fun f : Fin (k + 1) → P => UConn supp U f), ∏ j, b (f j)
        ≤ ∑ f ∈ Finset.univ.filter (fun f : Fin (k + 1) → P => UConn supp U f), ∑ i,
            (if ¬ Disjoint (supp (f i)) U ∧ UConn supp (U ∪ supp (f i)) (f ∘ i.succAbove) then ∏ j, b (f j) else 0) :=
          Finset.sum_le_sum hstep
      _ ≤ ∑ f : Fin (k + 1) → P, ∑ i,
            (if ¬ Disjoint (supp (f i)) U ∧ UConn supp (U ∪ supp (f i)) (f ∘ i.succAbove) then ∏ j, b (f j) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun f _ _ =>
            Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hprod f]
      _ = ∑ i, ∑ f : Fin (k + 1) → P,
            (if ¬ Disjoint (supp (f i)) U ∧ UConn supp (U ∪ supp (f i)) (f ∘ i.succAbove) then ∏ j, b (f j) else 0) :=
          Finset.sum_comm
      _ ≤ ∑ _i : Fin (k + 1), U.card * a * (k.factorial * ∏ j ∈ Finset.range k, ((U.card + D + j * D : ℝ) * a)) :=
          Finset.sum_le_sum fun i _ => hone i
      _ = (k + 1).factorial * ∏ i ∈ Finset.range (k + 1), ((U.card + i * D : ℝ) * a) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.prod_range_succ',
            Nat.factorial_succ]
          have hpr : ∏ j ∈ Finset.range k, ((U.card + D + j * D : ℝ) * a) =
              ∏ j ∈ Finset.range k, ((U.card + ((j + 1 : ℕ) : ℝ) * D) * a) :=
            Finset.prod_congr rfl fun j _ => by push_cast; ring
          rw [hpr]
          push_cast
          ring

omit [Fintype P] in
/-- Removing any piece of a connected tuple leaves a tuple connected to that piece's support. -/
lemma uConn_of_connected {k : ℕ} {f : Fin (k + 1) → P} (hf : TupleConnected supp f) (i : Fin (k + 1)) :
    UConn supp (supp (f i)) (f ∘ i.succAbove) := by
  intro A hA hdisj
  have hcomp : (Finset.univ \ A.map i.succAboveEmb).Nonempty :=
    ⟨i, by simp [Fin.succAbove_ne]⟩
  refine hf (A.map i.succAboveEmb) hA.map hcomp ?_
  rw [Finset.disjoint_left] at hdisj ⊢
  intro y hy1 hy2
  obtain ⟨j', hj', hyj'⟩ := Finset.mem_biUnion.mp hy1
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hj'
  refine hdisj (Finset.mem_biUnion.mpr ⟨j, hj, hyj'⟩) ?_
  obtain ⟨m, hm, hym⟩ := Finset.mem_biUnion.mp hy2
  by_cases hmi : m = i
  · subst hmi; exact Finset.mem_union_left _ hym
  · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hmi
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m', ?_, hym⟩)
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hm ⊢
    intro hm'
    exact hm (Finset.mem_map.mpr ⟨m', hm', rfl⟩)

/-- **Connected tuples with an anchored piece**: the tuples of length `k + 1` without a split whose `i`-th piece lies
in `S` weigh at most `(Σ_{X ∈ S} b_X) k! ∏_{j<k} ((D + j D) a)`. -/
theorem sum_connected_anchor_le [DecidableEq P] (hb : ∀ X, 0 ≤ b X) {D : ℕ} (hD : ∀ X, (supp X).card ≤ D) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ y, ∑ X ∈ Finset.univ.filter (fun X => y ∈ supp X), b X ≤ a) (k : ℕ) (i : Fin (k + 1)) (S : Finset P) :
    ∑ f ∈ Finset.univ.filter (fun f : Fin (k + 1) → P => TupleConnected supp f ∧ f i ∈ S), ∏ j, b (f j) ≤
      (∑ X ∈ S, b X) * (k.factorial * ∏ j ∈ Finset.range k, ((D + j * D : ℝ) * a)) := by
  set c : P → (Fin k → P) → ℝ := fun x g => if x ∈ S ∧ UConn supp (supp x) g then b x * ∏ j, b (g j) else 0
    with hc
  have hle : ∀ f : Fin (k + 1) → P, (if TupleConnected supp f ∧ f i ∈ S then ∏ j, b (f j) else 0) ≤
      c (f i) (f ∘ i.succAbove) := by
    intro f
    by_cases hf : TupleConnected supp f ∧ f i ∈ S
    · have hcond : f i ∈ S ∧ UConn supp (supp (f i)) (f ∘ i.succAbove) := ⟨hf.2, uConn_of_connected supp hf.1 i⟩
      simp only [hc]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hf), ite_eq_left_of_eq_true _ _ (eq_true hcond), Fin.prod_univ_succAbove _ i]
      rfl
    · simp only [hf, ↓reduceIte, hc]
      split_ifs
      · exact mul_nonneg (hb _) (Finset.prod_nonneg fun j _ => hb _)
      · exact le_rfl
  rw [Finset.sum_filter]
  refine (Finset.sum_le_sum fun f _ => hle f).trans ?_
  rw [sum_insertNth i c]
  have hx : ∀ x : P, ∑ g : Fin k → P, c x g ≤
      (if x ∈ S then b x else 0) * (k.factorial * ∏ j ∈ Finset.range k, ((D + j * D : ℝ) * a)) := by
    intro x
    by_cases hxS : x ∈ S
    · have hg : ∀ g : Fin k → P, c x g = b x * (if UConn supp (supp x) g then ∏ j, b (g j) else 0) := by
        intro g
        by_cases hgc : UConn supp (supp x) g <;> simp [hc, hxS, hgc]
      rw [Finset.sum_congr rfl fun g _ => hg g, ← Finset.mul_sum, ← Finset.sum_filter, ite_eq_left hxS]
      refine mul_le_mul_of_nonneg_left ((sum_uConn_le supp b hb hD ha0 ha k (supp x)).trans ?_) (hb x)
      gcongr with j hj
      exact_mod_cast hD x
    · have : ∀ g, c x g = 0 := fun g => by simp [hc, hxS]
      simp [this, hxS]
  calc ∑ x : P, ∑ g : Fin k → P, c x g
      ≤ ∑ x : P, (if x ∈ S then b x else 0) * (k.factorial * ∏ j ∈ Finset.range k, ((D + j * D : ℝ) * a)) :=
        Finset.sum_le_sum fun x _ => hx x
    _ = (∑ X ∈ S, b X) * (k.factorial * ∏ j ∈ Finset.range k, ((D + j * D : ℝ) * a)) := by
        rw [← Finset.sum_mul, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

end GaussianBlockSpin
