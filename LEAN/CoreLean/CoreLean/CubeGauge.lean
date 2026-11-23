/-
`lem:cube-gauge` of BALABAN_CORE.tex: a gauge on a box.

The box is `P = {x₀ + Σ_μ m_μ e_μ | 0 ≤ m_μ < ℓ_μ}`, indexed by the multi-indices `m`; its points are
`pt x₀ m`. The tree of `P` consists, for every `x ∈ P`, of the path from `x₀` to `x` which changes the
coordinates in the order `3, 2, 1, 0`: its bonds are those of the direction `0`, those of the direction
`1` with `m₀ = 0`, those of the direction `2` with `m₀ = m₁ = 0`, and those of the direction `3` with
`m₀ = m₁ = m₂ = 0`.

(i) If `U = 1` on the bonds of the tree and `|U(∂p) - 1| ≤ ε` for the plaquettes with all corners in
`P`, then `|U(b) - 1| ≤ 3ℓε` on every bond with both ends in `P`. The proof is the core's: going down
in the direction `μ < ν` along a line on whose `μ`-bonds `U = 1`, the plaquette `p_{μν}` gives
`U_ν(x + e_μ) = U(∂p) U_ν(x)`, and `|W₁W₂ - 1| ≤ |W₁ - 1| + |W₂ - 1|` for unitary `W₂`.
-/
import CoreLean.HessianBound

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The point `x₀ + Σ_μ m_μ e_μ` of the box. -/
def pt (x₀ : Site n) (m : Fin 4 → ℕ) : Site n := fun ν => x₀ ν + (m ν : ZMod n)

lemma pt_add_unit (x₀ : Site n) (m : Fin 4 → ℕ) (μ : Fin 4) :
    pt x₀ m + unit n μ = pt x₀ (Function.update m μ (m μ + 1)) := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [pt, unit, add_assoc]
  · simp [pt, unit, Pi.single_apply, h, Function.update_of_ne h]

/-- `|W₁W₂ - 1| ≤ |W₁ - 1| + |W₂ - 1|` for unitary `W₂`. -/
lemma hs_mul_sub_one_le (W₁ W₂ : Mat) (h₂ : W₂ ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    hs (W₁ * W₂ - 1) ≤ hs (W₁ - 1) + hs (W₂ - 1) := by
  have e : W₁ * W₂ - 1 = (W₁ - 1) * W₂ + (W₂ - 1) := by noncomm_ring
  rw [e]
  refine (hs_add_le _ _).trans (le_of_eq ?_)
  congr 1
  have := hs_unitary_mul 1 W₂ (W₁ - 1) (Submonoid.one_mem _) h₂
  rwa [Matrix.one_mul] at this

/-- Going down in the direction `μ` along a line on whose `μ`-bonds `U = 1`:
`|U_ν(x₀ + m) - 1| ≤ m_μ ε + |U_ν(x₀ + m|_{m_μ = 0}) - 1|`. -/
lemma descend (U : Config N n) (x₀ : Site n) {μ ν : Fin 4} (hμν : μ ≠ ν) (m : Fin 4 → ℕ)
    {ε : ℝ}
    (h1 : ∀ k < m μ, U μ (pt x₀ (Function.update m μ k)) = 1 ∧
      U μ (pt x₀ (Function.update m μ k) + unit n ν) = 1)
    (hpl : ∀ k < m μ, hs ((plaq U μ ν (pt x₀ (Function.update m μ k)) : Mat) - 1) ≤ ε)
    (hu : ∀ k < m μ, ((U ν (pt x₀ (Function.update m μ k)) : GLN) : Mat) ∈
      Matrix.unitaryGroup (Fin N) ℂ) :
    hs ((U ν (pt x₀ m) : Mat) - 1) ≤
      m μ * ε + hs ((U ν (pt x₀ (Function.update m μ 0)) : Mat) - 1) := by
  -- the claim for `update m μ j`, `j ≤ m μ`
  have key : ∀ j ≤ m μ, hs ((U ν (pt x₀ (Function.update m μ j)) : Mat) - 1) ≤
      j * ε + hs ((U ν (pt x₀ (Function.update m μ 0)) : Mat) - 1) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < m μ := hk
      obtain ⟨hU1, hU2⟩ := h1 k hk'
      -- `U(∂p_{μν}) = U_ν(x + e_μ) U_ν(x)⁻¹`
      have hp := plaq_eq U μ ν (pt x₀ (Function.update m μ k))
      rw [hU1, hU2, pt_add_unit] at hp
      simp only [Function.update_self, Function.update_idem, one_mul, inv_one, mul_one] at hp
      have hW : ((U ν (pt x₀ (Function.update m μ (k + 1))) : GLN) : Mat) =
          (plaq U μ ν (pt x₀ (Function.update m μ k)) : Mat) *
            ((U ν (pt x₀ (Function.update m μ k)) : GLN) : Mat) := by
        rw [hp]; simp
      have := hs_mul_sub_one_le (plaq U μ ν (pt x₀ (Function.update m μ k)) : Mat)
        ((U ν (pt x₀ (Function.update m μ k)) : GLN) : Mat) (hu k hk')
      rw [← hW] at this
      have := ih (Nat.le_of_succ_le hk)
      have := hpl k hk'
      push_cast
      linarith
  have := key (m μ) le_rfl
  rwa [Function.update_eq_self] at this

/-! ### The box and its tree -/

/-- `m` indexes a point of the box `0 ≤ m_μ < ℓ_μ`. -/
def InBox (ℓv : Fin 4 → ℕ) (m : Fin 4 → ℕ) : Prop := ∀ μ, m μ < ℓv μ

/-- The bond `(x₀ + m, x₀ + m + e_ν)` belongs to the tree. -/
def IsTree (m : Fin 4 → ℕ) (ν : Fin 4) : Prop :=
  ν = 0 ∨ (ν = 1 ∧ m 0 = 0) ∨ (ν = 2 ∧ m 0 = 0 ∧ m 1 = 0) ∨
    (ν = 3 ∧ m 0 = 0 ∧ m 1 = 0 ∧ m 2 = 0)

lemma inBox_update {ℓv m : Fin 4 → ℕ} (hm : InBox ℓv m) (μ : Fin 4) {k : ℕ} (hk : k ≤ m μ) :
    InBox ℓv (Function.update m μ k) := fun κ => by
  by_cases h : κ = μ
  · subst h; simp only [Function.update_self]; exact lt_of_le_of_lt hk (hm κ)
  · rw [Function.update_of_ne h]; exact hm κ

/-- The hypotheses of `lem:cube-gauge` on a gauge field `U` and the box. -/
structure BoxData (U : Config N n) (x₀ : Site n) (ℓv : Fin 4 → ℕ) (ε : ℝ) : Prop where
  unitary : ∀ m ν, InBox ℓv m → m ν + 1 < ℓv ν →
    ((U ν (pt x₀ m) : GLN) : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ
  plaq : ∀ m μ ν, μ < ν → InBox ℓv m → m μ + 1 < ℓv μ → m ν + 1 < ℓv ν →
    hs ((plaq U μ ν (pt x₀ m) : Mat) - 1) ≤ ε

/-- Descending in the direction `μ < ν` inside the box, along a line on whose `μ`-bonds `U = 1`. -/
lemma descend_box {U : Config N n} {x₀ : Site n} {ℓv : Fin 4 → ℕ} {ε : ℝ}
    (hB : BoxData U x₀ ℓv ε) {μ ν : Fin 4} (hμν : μ < ν) {m : Fin 4 → ℕ} (hm : InBox ℓv m)
    (hmν : m ν + 1 < ℓv ν)
    (h1 : ∀ k < m μ, U μ (pt x₀ (Function.update m μ k)) = 1 ∧
      U μ (pt x₀ (Function.update m μ k) + unit n ν) = 1) :
    hs ((U ν (pt x₀ m) : Mat) - 1) ≤
      m μ * ε + hs ((U ν (pt x₀ (Function.update m μ 0)) : Mat) - 1) := by
  have hne : μ ≠ ν := ne_of_lt hμν
  refine descend U x₀ hne m h1 (fun k hk => ?_) (fun k hk => ?_)
  · refine hB.plaq _ μ ν hμν (inBox_update hm μ hk.le) ?_ ?_
    · simp only [Function.update_self]; exact lt_of_le_of_lt hk (hm μ)
    · rw [Function.update_of_ne hne.symm]; exact hmν
  · refine hB.unitary _ ν (inBox_update hm μ hk.le) ?_
    rw [Function.update_of_ne hne.symm]; exact hmν

/-- `lem:cube-gauge`(i): if `U = 1` on the bonds of the tree, then `|U(b) - 1| ≤ 3ℓε` and
`‖U(b) - 1‖ ≤ 3√N ℓε` for every bond `b` with both ends in `P`. -/
theorem cube_gauge_tree {U : Config N n} {x₀ : Site n} {ℓv : Fin 4 → ℕ} {ℓ : ℕ}
    (hℓ : ∀ μ, ℓv μ ≤ ℓ) {ε : ℝ} (hε : 0 ≤ ε) (hB : BoxData U x₀ ℓv ε)
    (htree : ∀ m ν, InBox ℓv m → m ν + 1 < ℓv ν → IsTree m ν → U ν (pt x₀ m) = 1)
    {m : Fin 4 → ℕ} (hm : InBox ℓv m) {ν : Fin 4} (hmν : m ν + 1 < ℓv ν) :
    hs ((U ν (pt x₀ m) : Mat) - 1) ≤ 3 * ℓ * ε ∧
      ‖(U ν (pt x₀ m) : Mat) - 1‖ ≤ 3 * Real.sqrt N * ℓ * ε := by
  have hmℓ : ∀ μ, (m μ : ℝ) ≤ ℓ := fun μ => by exact_mod_cast (hm μ).le.trans (hℓ μ)
  have hone : ∀ {W : GLN}, W = 1 → hs ((W : Mat) - 1) = 0 := fun h => by
    rw [h]; simp [hs, hs2, ntr]
  -- the tree bonds used: `U_μ = 1` on the lines below
  have tree_line : ∀ (m' : Fin 4 → ℕ) (μ ν' : Fin 4), μ < ν' → InBox ℓv m' →
      m' ν' + 1 < ℓv ν' → (∀ k < m' μ, IsTree (Function.update m' μ k) μ) →
      (∀ k < m' μ, IsTree (Function.update (Function.update m' μ k) ν'
        (Function.update m' μ k ν' + 1)) μ) →
      ∀ k < m' μ, U μ (pt x₀ (Function.update m' μ k)) = 1 ∧
        U μ (pt x₀ (Function.update m' μ k) + unit n ν') = 1 := by
    intro m' μ ν' hμν hm' hm'ν ht1 ht2 k hk
    have hne : μ ≠ ν' := ne_of_lt hμν
    have hbox := inBox_update hm' μ hk.le
    have hμk : Function.update m' μ k μ + 1 < ℓv μ := by
      simp only [Function.update_self]; exact lt_of_le_of_lt hk (hm' μ)
    refine ⟨htree _ μ hbox hμk (ht1 k hk), ?_⟩
    rw [pt_add_unit]
    refine htree _ μ ?_ ?_ (ht2 k hk)
    · intro κ
      by_cases h : κ = ν'
      · subst h; simp only [Function.update_self, Function.update_of_ne hne.symm]; exact hm'ν
      · rw [Function.update_of_ne h]; exact hbox κ
    · rw [Function.update_of_ne hne]; exact hμk
  have hsq : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hfinal : hs ((U ν (pt x₀ m) : Mat) - 1) ≤ 3 * ℓ * ε := by
    have hν : ν = 0 ∨ ν = 1 ∨ ν = 2 ∨ ν = 3 := by fin_cases ν <;> simp
    rcases hν with rfl | rfl | rfl | rfl
    · -- `ν = 0`: a tree bond
      rw [hone (htree m 0 hm hmν (Or.inl rfl))]; positivity
    · -- `ν = 1`: descend in the direction `0`
      have h0 := descend_box hB (show (0 : Fin 4) < 1 by decide) hm hmν
        (tree_line m 0 1 (by decide) hm hmν (fun k _ => Or.inl rfl) (fun k _ => Or.inl rfl))
      rw [hone (htree _ 1 (inBox_update hm 0 (Nat.zero_le _))
        (by rw [Function.update_of_ne (by decide)]; exact hmν)
        (Or.inr (Or.inl ⟨rfl, by simp⟩)))] at h0
      have := hmℓ 0
      nlinarith
    · -- `ν = 2`: descend in the directions `0` and `1`
      have h0 := descend_box hB (show (0 : Fin 4) < 2 by decide) hm hmν
        (tree_line m 0 2 (by decide) hm hmν (fun k _ => Or.inl rfl) (fun k _ => Or.inl rfl))
      set m1 := Function.update m 0 0
      have hm1 : InBox ℓv m1 := inBox_update hm 0 (Nat.zero_le _)
      have hm1ν : m1 2 + 1 < ℓv 2 := by
        simp only [m1]; rw [Function.update_of_ne (by decide)]; exact hmν
      have h1 := descend_box hB (show (1 : Fin 4) < 2 by decide) hm1 hm1ν
        (tree_line m1 1 2 (by decide) hm1 hm1ν
          (fun k _ => Or.inr (Or.inl ⟨rfl, by simp [m1]⟩))
          (fun k _ => Or.inr (Or.inl ⟨rfl, by simp [m1, Function.update_of_ne]⟩)))
      rw [hone (htree _ 2 (inBox_update hm1 1 (Nat.zero_le _))
        (by rw [Function.update_of_ne (by decide)]; exact hm1ν)
        (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [m1], by simp⟩))))] at h1
      have hm11 : (m1 1 : ℝ) = m 1 := by simp [m1, Function.update_of_ne]
      rw [hm11] at h1
      have := hmℓ 0; have := hmℓ 1
      nlinarith
    · -- `ν = 3`: descend in the directions `0`, `1` and `2`
      have h0 := descend_box hB (show (0 : Fin 4) < 3 by decide) hm hmν
        (tree_line m 0 3 (by decide) hm hmν (fun k _ => Or.inl rfl) (fun k _ => Or.inl rfl))
      set m1 := Function.update m 0 0
      have hm1 : InBox ℓv m1 := inBox_update hm 0 (Nat.zero_le _)
      have hm1ν : m1 3 + 1 < ℓv 3 := by
        simp only [m1]; rw [Function.update_of_ne (by decide)]; exact hmν
      have h1 := descend_box hB (show (1 : Fin 4) < 3 by decide) hm1 hm1ν
        (tree_line m1 1 3 (by decide) hm1 hm1ν
          (fun k _ => Or.inr (Or.inl ⟨rfl, by simp [m1]⟩))
          (fun k _ => Or.inr (Or.inl ⟨rfl, by simp [m1, Function.update_of_ne]⟩)))
      set m2 := Function.update m1 1 0
      have hm2 : InBox ℓv m2 := inBox_update hm1 1 (Nat.zero_le _)
      have hm2ν : m2 3 + 1 < ℓv 3 := by
        simp only [m2]; rw [Function.update_of_ne (by decide)]; exact hm1ν
      have h2 := descend_box hB (show (2 : Fin 4) < 3 by decide) hm2 hm2ν
        (tree_line m2 2 3 (by decide) hm2 hm2ν
          (fun k _ => Or.inr (Or.inr (Or.inl ⟨rfl, by simp [m2, m1], by simp [m2]⟩)))
          (fun k _ => Or.inr (Or.inr (Or.inl ⟨rfl, by simp [m2, m1, Function.update_of_ne],
            by simp [m2, Function.update_of_ne]⟩))))
      rw [hone (htree _ 3 (inBox_update hm2 2 (Nat.zero_le _))
        (by rw [Function.update_of_ne (by decide)]; exact hm2ν)
        (Or.inr (Or.inr (Or.inr ⟨rfl, by simp [m2, m1], by simp [m2], by simp⟩))))] at h2
      have hm11 : (m1 1 : ℝ) = m 1 := by simp [m1, Function.update_of_ne]
      have hm22 : (m2 2 : ℝ) = m 2 := by simp [m2, m1, Function.update_of_ne]
      rw [hm11] at h1
      rw [hm22] at h2
      have := hmℓ 0; have := hmℓ 1; have := hmℓ 2
      nlinarith
  refine ⟨hfinal, (opNorm_le_sqrt_mul_hs _).trans ?_⟩
  calc Real.sqrt N * hs ((U ν (pt x₀ m) : Mat) - 1) ≤ Real.sqrt N * (3 * ℓ * ε) := by gcongr
    _ = 3 * Real.sqrt N * ℓ * ε := by ring

/-! ### (ii): the gauge transformation of the tree -/

/-- The transport `U_μ(b) U_μ(b + e_μ) ⋯ U_μ(b + (k-1)e_μ)` along the line from `b` in the direction
`μ` (the coordinate `μ` of `b` is replaced by `0, 1, …, k - 1`). -/
def lineProd (U : Config N n) (x₀ : Site n) (b : Fin 4 → ℕ) (μ : Fin 4) (k : ℕ) : GLN :=
  ((List.range k).map fun i => U μ (pt x₀ (Function.update b μ i))).prod

lemma lineProd_succ (U : Config N n) (x₀ : Site n) (b : Fin 4 → ℕ) (μ : Fin 4) (k : ℕ) :
    lineProd U x₀ b μ (k + 1) = lineProd U x₀ b μ k * U μ (pt x₀ (Function.update b μ k)) := by
  simp [lineProd, List.range_succ, List.prod_append]

lemma lineProd_zero (U : Config N n) (x₀ : Site n) (b : Fin 4 → ℕ) (μ : Fin 4) :
    lineProd U x₀ b μ 0 = 1 := by simp [lineProd]

/-- `U(γ_m)`: the transport along the path of the tree from `x₀` to `x₀ + m`, which changes the
coordinates in the order `3, 2, 1, 0`. -/
def treeHol (U : Config N n) (x₀ : Site n) (m : Fin 4 → ℕ) : GLN :=
  lineProd U x₀ ![0, 0, 0, 0] 3 (m 3) * lineProd U x₀ ![0, 0, 0, m 3] 2 (m 2) *
    lineProd U x₀ ![0, 0, m 2, m 3] 1 (m 1) * lineProd U x₀ ![0, m 1, m 2, m 3] 0 (m 0)

/-- The gauge transformation `u(x) = U(γ_x)` of `lem:cube-gauge`(ii), with `x = x₀ + m` and
`m_μ = (x - x₀)_μ`. -/
def treeGauge (U : Config N n) (x₀ : Site n) (x : Site n) : GLN :=
  treeHol U x₀ fun μ => ((x - x₀) μ).val

lemma treeGauge_pt (U : Config N n) (x₀ : Site n) {m : Fin 4 → ℕ} (hm : ∀ μ, m μ < n) :
    treeGauge U x₀ (pt x₀ m) = treeHol U x₀ m := by
  unfold treeGauge
  congr 1
  funext μ
  simp only [pt, Pi.sub_apply, add_sub_cancel_left, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (hm μ)

/-- `U(γ_{m + e_ν}) = U(γ_m) U_ν(x₀ + m)` for the bonds of the tree. -/
lemma treeHol_succ (U : Config N n) (x₀ : Site n) (m : Fin 4 → ℕ) (ν : Fin 4) (ht : IsTree m ν) :
    treeHol U x₀ (Function.update m ν (m ν + 1)) = treeHol U x₀ m * U ν (pt x₀ m) := by
  have e0 : ∀ m' : Fin 4 → ℕ, m' = ![m' 0, m' 1, m' 2, m' 3] := fun m' => by
    funext κ; fin_cases κ <;> rfl
  rcases ht with rfl | ⟨rfl, h0⟩ | ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1, h2⟩
  · simp only [treeHol, Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, lineProd_succ, mul_assoc]
    congr 4
    conv_rhs => rw [e0 m]
    congr 2; funext κ; fin_cases κ <;> simp
  · simp only [treeHol, Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, lineProd_succ, h0, lineProd_zero, mul_one, mul_assoc]
    congr 3
    conv_rhs => rw [e0 m]
    congr 2; funext κ; fin_cases κ <;> simp [h0]
  · simp only [treeHol, Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, lineProd_succ, h0, h1, lineProd_zero, mul_one, mul_assoc]
    congr 2
    conv_rhs => rw [e0 m]
    congr 2; funext κ; fin_cases κ <;> simp [h0, h1]
  · simp only [treeHol, Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, lineProd_succ, h0, h1, h2, lineProd_zero, mul_one]
    congr 1
    conv_rhs => rw [e0 m]
    congr 2; funext κ; fin_cases κ <;> simp [h0, h1, h2]

/-- The invertible matrices which are unitary. -/
def unitaryUnits : Submonoid GLN := (Matrix.unitaryGroup (Fin N) ℂ).comap (Units.coeHom Mat)

lemma mem_unitaryUnits {W : GLN} :
    W ∈ (unitaryUnits : Submonoid GLN) ↔ (W : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ := Iff.rfl

lemma inv_mem_unitaryUnits {W : GLN} (h : W ∈ (unitaryUnits : Submonoid GLN)) :
    W⁻¹ ∈ (unitaryUnits : Submonoid GLN) := by
  rw [mem_unitaryUnits] at h ⊢
  rw [Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem h)]
  exact Unitary.star_mem h

/-- A transport along a line of unitary bonds is unitary. -/
lemma lineProd_mem (U : Config N n) (x₀ : Site n) (b : Fin 4 → ℕ) (μ : Fin 4) (k : ℕ)
    (h : ∀ i < k, U μ (pt x₀ (Function.update b μ i)) ∈ (unitaryUnits : Submonoid GLN)) :
    lineProd U x₀ b μ k ∈ (unitaryUnits : Submonoid GLN) := by
  unfold lineProd
  refine Submonoid.list_prod_mem _ fun W hW => ?_
  simp only [List.mem_map, List.mem_range] at hW
  obtain ⟨i, hi, rfl⟩ := hW
  exact h i hi

lemma lineProd_mem_box {U : Config N n} {x₀ : Site n} {ℓv : Fin 4 → ℕ} {ε : ℝ}
    (hB : BoxData U x₀ ℓv ε) {b : Fin 4 → ℕ} (μ : Fin 4) (hb : ∀ κ, κ ≠ μ → b κ < ℓv κ)
    {k : ℕ} (hk : k < ℓv μ) :
    lineProd U x₀ b μ k ∈ (unitaryUnits : Submonoid GLN) := by
  refine lineProd_mem U x₀ b μ k fun i hi => hB.unitary _ μ (fun κ => ?_) ?_
  · by_cases h : κ = μ
    · subst h; simp only [Function.update_self]; omega
    · rw [Function.update_of_ne h]; exact hb κ h
  · simp only [Function.update_self]; omega

/-- The transport along the tree is unitary inside the box. -/
lemma treeHol_mem {U : Config N n} {x₀ : Site n} {ℓv : Fin 4 → ℕ} {ε : ℝ}
    (hB : BoxData U x₀ ℓv ε) {m : Fin 4 → ℕ} (hm : InBox ℓv m) :
    treeHol U x₀ m ∈ (unitaryUnits : Submonoid GLN) := by
  have h0 := hm 0; have h1 := hm 1; have h2 := hm 2; have h3 := hm 3
  unfold treeHol
  refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) ?_
  · refine lineProd_mem_box hB 3 (fun κ hκ => ?_) h3
    fin_cases κ <;> simp_all <;> omega
  · refine lineProd_mem_box hB 2 (fun κ hκ => ?_) h2
    fin_cases κ <;> simp_all <;> omega
  · refine lineProd_mem_box hB 1 (fun κ hκ => ?_) h1
    fin_cases κ <;> simp_all <;> omega
  · refine lineProd_mem_box hB 0 (fun κ hκ => ?_) h0
    fin_cases κ <;> simp_all <;> omega

lemma inBox_succ {ℓv m : Fin 4 → ℕ} (hm : InBox ℓv m) {ν : Fin 4} (hmν : m ν + 1 < ℓv ν) :
    InBox ℓv (Function.update m ν (m ν + 1)) := fun κ => by
  by_cases h : κ = ν
  · subst h; simp only [Function.update_self]; exact hmν
  · rw [Function.update_of_ne h]; exact hm κ

/-- `lem:cube-gauge`(ii), first part: `U^u = 1` on the bonds of the tree, for `u(x) = U(γ_x)`;
the box does not wrap around the torus (`ℓ_μ ≤ n`). -/
theorem treeGauge_tree (U : Config N n) (x₀ : Site n) {ℓv : Fin 4 → ℕ} (hℓn : ∀ μ, ℓv μ ≤ n)
    {m : Fin 4 → ℕ} (hm : InBox ℓv m) {ν : Fin 4} (hmν : m ν + 1 < ℓv ν) (ht : IsTree m ν) :
    U.gauge (treeGauge U x₀) ν (pt x₀ m) = 1 := by
  have hm' := inBox_succ hm hmν
  simp only [Config.gauge]
  rw [pt_add_unit, treeGauge_pt U x₀ (fun μ => (hm μ).trans_le (hℓn μ)),
    treeGauge_pt U x₀ (fun μ => (hm' μ).trans_le (hℓn μ)), treeHol_succ U x₀ m ν ht]
  exact mul_inv_cancel _

/-- The hypotheses of `lem:cube-gauge` pass to `U^u`: its values on the bonds of the box are
unitary and its plaquettes are conjugates of those of `U`. -/
theorem boxData_treeGauge {U : Config N n} {x₀ : Site n} {ℓv : Fin 4 → ℕ} {ε : ℝ}
    (hℓn : ∀ μ, ℓv μ ≤ n) (hB : BoxData U x₀ ℓv ε) :
    BoxData (U.gauge (treeGauge U x₀)) x₀ ℓv ε := by
  have hu : ∀ m, InBox ℓv m → treeGauge U x₀ (pt x₀ m) ∈ (unitaryUnits : Submonoid GLN) :=
    fun m hm => by
      rw [treeGauge_pt U x₀ (fun μ => (hm μ).trans_le (hℓn μ))]; exact treeHol_mem hB hm
  constructor
  · intro m ν hm hmν
    have hm' := inBox_succ hm hmν
    have e : U.gauge (treeGauge U x₀) ν (pt x₀ m) =
        treeGauge U x₀ (pt x₀ m) * U ν (pt x₀ m) *
          (treeGauge U x₀ (pt x₀ (Function.update m ν (m ν + 1))))⁻¹ := by
      simp only [Config.gauge]; rw [pt_add_unit]
    rw [e]
    have hU : U ν (pt x₀ m) ∈ (unitaryUnits : Submonoid GLN) :=
      mem_unitaryUnits.mpr (hB.unitary m ν hm hmν)
    have hprod : treeGauge U x₀ (pt x₀ m) * U ν (pt x₀ m) *
        (treeGauge U x₀ (pt x₀ (Function.update m ν (m ν + 1))))⁻¹ ∈
          (unitaryUnits : Submonoid GLN) :=
      Submonoid.mul_mem _ (Submonoid.mul_mem _ (hu m hm) hU) (inv_mem_unitaryUnits (hu _ hm'))
    exact mem_unitaryUnits.mp hprod
  · intro m μ ν hμν hm hmμ hmν
    rw [plaq_gauge]
    set u := treeGauge U x₀ (pt x₀ m)
    have hu1 : ((u : GLN) : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ := mem_unitaryUnits.mp (hu m hm)
    have hu2 : ((u⁻¹ : GLN) : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
      mem_unitaryUnits.mp (inv_mem_unitaryUnits (hu m hm))
    have e : ((u * plaq U μ ν (pt x₀ m) * u⁻¹ : GLN) : Mat) - 1 =
        (u : Mat) * ((plaq U μ ν (pt x₀ m) : Mat) - 1) * ((u⁻¹ : GLN) : Mat) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [e, hs_unitary_mul _ _ _ hu1 hu2]
    exact hB.plaq m μ ν hμν hm hmμ hmν

/-- `lem:cube-gauge`(ii): `|U^u(b) - 1| ≤ 3ℓε` and `‖U^u(b) - 1‖ ≤ 3√N ℓε` for every bond `b`
with both ends in `P`, for the gauge transformation `u(x) = U(γ_x)` of the tree. -/
theorem cube_gauge {U : Config N n} {x₀ : Site n} {ℓv : Fin 4 → ℕ} {ℓ : ℕ}
    (hℓ : ∀ μ, ℓv μ ≤ ℓ) (hℓn : ∀ μ, ℓv μ ≤ n) {ε : ℝ} (hε : 0 ≤ ε) (hB : BoxData U x₀ ℓv ε)
    {m : Fin 4 → ℕ} (hm : InBox ℓv m) {ν : Fin 4} (hmν : m ν + 1 < ℓv ν) :
    hs ((U.gauge (treeGauge U x₀) ν (pt x₀ m) : Mat) - 1) ≤ 3 * ℓ * ε ∧
      ‖(U.gauge (treeGauge U x₀) ν (pt x₀ m) : Mat) - 1‖ ≤ 3 * Real.sqrt N * ℓ * ε :=
  cube_gauge_tree hℓ hε (boxData_treeGauge hℓn hB)
    (fun m' ν' hm' hm'ν ht => treeGauge_tree U x₀ hℓn hm' hm'ν ht) hm hmν

end CoreLean
