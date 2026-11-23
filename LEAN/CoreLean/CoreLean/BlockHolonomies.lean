/-
`lem:block-holonomies`(i), (iii) of BALABAN_CORE.tex (`fe7d249fe3af`): values on short paths.

For a configuration `𝐔`, a `1`-form `B = aA`, and a path `γ = (b_1, …, b_n)`,
`(e^{iB}𝐔)(γ) = e^{iY_1}⋯e^{iY_n}𝐔(γ)` with `Y_l = Ad_{𝐔(b_1⋯b_{l-1})}B(b_l)` for a positive bond `b_l` and
`Y_l = -Ad_{𝐔(b_1⋯b_l)}B(b_l^{-1})` for a negative one (`moved_path`); if `‖Ad_{𝐔(γ')}Z‖ ≤ κ‖Z‖` for the initial pieces
`γ'` of `γ` and `‖B‖ ≤ a` on the bonds of `γ`, then `‖Y_l‖ ≤ κa` (`Ylist_bound`) and
`‖e^{iY_1}⋯e^{iY_n} - id‖ ≤ e^{κna} - 1` (`block_holonomies_iii`).

`lem:block-holonomies`(i): `Reduces U α m γ` (`γ` reduced to the trivial path by `m` moves across plaquettes `p` with
`|U(∂p) - id| ≤ α`, a move replacing `γ₁σγ₂` by `γ₁σ'γ₂` with `σσ'⁻¹ = ∂p` read from the first point of `σ`, and the
cancellation of a backtrack free); then `|U(γ) - id| ≤ mα` and `‖U(γ) - id‖ ≤ √N mα` (`block_holonomies_i`).
-/
import CoreLean.AverageHolo
import CoreLean.RegularAverages

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace BlockHolonomies

open AverageHolo RegularAverages

variable {N : ℕ} {n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The value of `B` on a bond of a path, transported to its initial point: `B(b)` for a positive bond,
`-Ad_{𝐔(b)}B(b⁻¹)` for a negative one. -/
def Bv (V : Config N n) (B : Fin 4 → Site n → Mat) (b : Bond n) : Mat :=
  if b.pos then B b.dir b.site else -(Ad (V.val b) (B b.dir (b.site - unit n b.dir)))

/-- The exponents `Y_l` of a moved path. -/
def Ylist (V : Config N n) (B : Fin 4 → Site n → Mat) : List (Bond n) → List Mat
  | [] => []
  | b :: γ => Bv V B b :: (Ylist V B γ).map (Ad (V.val b))

/-- `∏ e^{iY}`. -/
def prodExp (l : List Mat) : GLN := (l.map fun Y => expU (Complex.I • Y)).prod

lemma expU_inv' (X : Mat) : (expU X)⁻¹ = expU (-X) := Units.ext (by rw [expU_inv_val, expU_val])

lemma mul_expU (W : GLN) (X : Mat) : W * expU X = expU (Ad W X) * W := by
  rw [← expU_conj]; group

/-- `(e^{iB}𝐔)(b) = e^{iB_v(b)}𝐔(b)` on every bond. -/
lemma moveC_val (V : Config N n) (B : Fin 4 → Site n → Mat) (b : Bond n) :
    (moveC V B).val b = expU (Complex.I • Bv V B b) * V.val b := by
  cases b with
  | mk z μ s =>
    cases s
    · simp only [Config.val, Bv, Bool.false_eq_true, ↓reduceIte, moveC]
      rw [_root_.mul_inv_rev, expU_inv']
      rw [show Complex.I • -(Ad (V μ (z - unit n μ))⁻¹ (B μ (z - unit n μ))) =
        Ad (V μ (z - unit n μ))⁻¹ (-(Complex.I • B μ (z - unit n μ))) by rw [Ad_neg, Ad_smul, smul_neg], ← mul_expU]
    · simp only [Config.val, Bv, ↓reduceIte, moveC]

lemma prodExp_cons (Y : Mat) (l : List Mat) : prodExp (Y :: l) = expU (Complex.I • Y) * prodExp l := by
  simp [prodExp]

lemma mul_prodExp (W : GLN) : ∀ l : List Mat, W * prodExp l = prodExp (l.map (Ad W)) * W
  | [] => by simp [prodExp]
  | Y :: l => by
    rw [prodExp_cons, List.map_cons, prodExp_cons, ← mul_assoc, mul_expU, mul_assoc, mul_prodExp W l, Ad_smul,
      mul_assoc]

/-- **The moved path**: `(e^{iB}𝐔)(γ) = e^{iY_1}⋯e^{iY_n}𝐔(γ)`. -/
theorem moved_path (V : Config N n) (B : Fin 4 → Site n → Mat) :
    ∀ γ : List (Bond n), (moveC V B).hol γ = prodExp (Ylist V B γ) * V.hol γ
  | [] => by simp [prodExp, Ylist]
  | b :: γ => by
    rw [LatticePaths.hol_cons, LatticePaths.hol_cons, moved_path V B γ, moveC_val, Ylist, prodExp_cons]
    rw [show expU (Complex.I • Bv V B b) * V.val b * (prodExp (Ylist V B γ) * V.hol γ) =
        expU (Complex.I • Bv V B b) * (V.val b * prodExp (Ylist V B γ)) * V.hol γ by group]
    rw [mul_prodExp]
    group

/-- **The size of the exponents**: with `‖Ad_{W𝐔(γ')}Z‖ ≤ κ‖Z‖` for the initial pieces `γ'` of `γ` and `‖B‖ ≤ a` on the
bonds of `γ` (on the positive bond of each), the exponents transported by `W` satisfy `‖Ad_WY_l‖ ≤ κa`. -/
theorem Ylist_bound (V : Config N n) (B : Fin 4 → Site n → Mat) {κ a : ℝ} (hκ0 : 0 ≤ κ) (ha : 0 ≤ a) :
    ∀ (γ : List (Bond n)) (W : GLN), (∀ k, k ≤ γ.length → ∀ Z : Mat, ‖Ad (W * V.hol (γ.take k)) Z‖ ≤ κ * ‖Z‖) →
      (∀ b ∈ γ, ‖B b.dir (if b.pos then b.site else b.site - unit n b.dir)‖ ≤ a) →
      ∀ Y ∈ (Ylist V B γ).map (Ad W), ‖Y‖ ≤ κ * a
  | [], _, _, _ => by simp [Ylist]
  | b :: γ, W, hκ, hB => by
    intro Y hY
    simp only [Ylist, List.map_cons, List.mem_cons, List.map_map] at hY
    rcases hY with rfl | hY
    · -- the first exponent
      have hb := hB b (List.mem_cons_self)
      cases hpos : b.pos
      · simp only [Bv, hpos, Bool.false_eq_true, ↓reduceIte] at hb ⊢
        rw [Ad_neg, norm_neg, ← Ad_mul]
        have := hκ 1 (by simp) (B b.dir (b.site - unit n b.dir))
        simp only [List.take_succ_cons, List.take_zero, LatticePaths.hol_cons, LatticePaths.hol_nil, mul_one] at this
        exact this.trans (mul_le_mul_of_nonneg_left hb hκ0)
      · simp only [Bv, hpos, ↓reduceIte] at hb ⊢
        have := hκ 0 (Nat.zero_le _) (B b.dir b.site)
        simp only [List.take_zero, LatticePaths.hol_nil, mul_one] at this
        exact this.trans (mul_le_mul_of_nonneg_left hb hκ0)
    · -- the others, transported by `W𝐔(b)`
      obtain ⟨Y', hY', rfl⟩ := List.mem_map.1 hY
      have e : (Ad W ∘ Ad (V.val b)) Y' = Ad (W * V.val b) Y' := by simp [Function.comp, Ad_mul]
      rw [e]
      refine Ylist_bound V B hκ0 ha γ (W * V.val b) (fun k hk Z => ?_) (fun b' hb' => hB b' (List.mem_cons_of_mem _ hb'))
        _ (List.mem_map.2 ⟨Y', hY', rfl⟩)
      have := hκ (k + 1) (by simp; omega) Z
      simpa [List.take_succ_cons, LatticePaths.hol_cons, mul_assoc] using this

lemma Ylist_length (V : Config N n) (B : Fin 4 → Site n → Mat) :
    ∀ γ : List (Bond n), (Ylist V B γ).length = γ.length
  | [] => rfl
  | b :: γ => by simp [Ylist, Ylist_length V B γ]

lemma prodExp_val : ∀ l : List Mat,
    ((prodExp l : GLN) : Mat) = ((l.map fun Y => Complex.I • Y).map exp).prod
  | [] => by simp [prodExp]
  | Y :: l => by rw [prodExp_cons, Units.val_mul, expU_val, prodExp_val l]; simp

/-- **`lem:block-holonomies`(iii)**: `(e^{iB}𝐔)(γ) = e^{iY_1}⋯e^{iY_n}𝐔(γ)` with `‖Y_l‖ ≤ κa`, so that
`‖e^{iY_1}⋯e^{iY_n} - id‖ ≤ e^{κna} - 1`, `n` the number of bonds of `γ`. -/
theorem block_holonomies_iii (V : Config N n) (B : Fin 4 → Site n → Mat) {κ a : ℝ} (hκ0 : 0 ≤ κ) (ha : 0 ≤ a)
    (γ : List (Bond n)) (hκ : ∀ k, k ≤ γ.length → ∀ Z : Mat, ‖Ad (V.hol (γ.take k)) Z‖ ≤ κ * ‖Z‖)
    (hB : ∀ b ∈ γ, ‖B b.dir (if b.pos then b.site else b.site - unit n b.dir)‖ ≤ a) :
    (moveC V B).hol γ = prodExp (Ylist V B γ) * V.hol γ ∧ (∀ Y ∈ Ylist V B γ, ‖Y‖ ≤ κ * a) ∧
      ‖((prodExp (Ylist V B γ) : GLN) : Mat) - 1‖ ≤ Real.exp (κ * γ.length * a) - 1 := by
  have hb := Ylist_bound V B hκ0 ha γ 1 (fun k hk Z => by simpa using hκ k hk Z) hB
  have hY : ∀ Y ∈ Ylist V B γ, ‖Y‖ ≤ κ * a := fun Y hYm => by
    have := hb (Ad 1 Y) (List.mem_map.2 ⟨Y, hYm, rfl⟩)
    simpa [Ad] using this
  refine ⟨moved_path V B γ, hY, ?_⟩
  -- the product of the exponentials
  have hlen : (Ylist V B γ).length = γ.length := Ylist_length V B γ
  set L := (Ylist V B γ).map fun Y => Complex.I • Y
  have hval : ((prodExp (Ylist V B γ) : GLN) : Mat) = (L.map exp).prod := prodExp_val _
  obtain ⟨h1, -⟩ := prod_exp_bound L
  have hS : ‖L.sum‖ ≤ (L.map norm).sum := norm_list_sum_le' L
  have hsum : (L.map norm).sum ≤ κ * γ.length * a := by
    have : (L.map norm).sum = ((Ylist V B γ).map norm).sum := by
      simp only [L, List.map_map]
      congr 1
      exact List.map_congr_left fun Y _ => by simp [norm_smul]
    rw [this]
    calc ((Ylist V B γ).map norm).sum ≤ ((Ylist V B γ).map fun _ => κ * a).sum :=
          List.sum_le_sum fun Y hYm => hY Y hYm
      _ = κ * γ.length * a := by rw [List.map_const', List.sum_replicate, hlen, nsmul_eq_mul]; ring
  rw [hval]
  have e : (L.map exp).prod - 1 = ((L.map exp).prod - 1 - L.sum) + L.sum := by abel
  rw [e]
  have hexp : Real.exp ((L.map norm).sum) ≤ Real.exp (κ * γ.length * a) := Real.exp_le_exp.2 hsum
  linarith [norm_add_le ((L.map exp).prod - 1 - L.sum) L.sum]

/-! ### `lem:block-holonomies`(i): moves across plaquettes -/

/-- The boundary `∂p_{μν}(x)` read from one of its corners, in either orientation. -/
def IsPlaqBdry (P : List (Bond n)) (μ ν : Fin 4) (x : Site n) : Prop :=
  ∃ k, P = (plaqPath μ ν x).rotate k ∨ P = rv ((plaqPath μ ν x).rotate k)

/-- `Reduces U α m γ`: the path `γ` is reduced to the trivial path by `m` moves across plaquettes `p` with
`|U(∂p) - id| ≤ α`, a move replacing `γ₁σγ₂` by `γ₁σ'γ₂` with `σσ'⁻¹ = ∂p` read from the first point of `σ`; the
cancellation of a backtrack `bb⁻¹` is free. -/
inductive Reduces (U : Config N n) (α : ℝ) : ℕ → List (Bond n) → Prop
  | nil : Reduces U α 0 []
  | cancel {m : ℕ} (γ₁ γ₂ : List (Bond n)) (b : Bond n) :
      Reduces U α m (γ₁ ++ γ₂) → Reduces U α m (γ₁ ++ [b, b.rev] ++ γ₂)
  | move {m : ℕ} (γ₁ σ σ' γ₂ : List (Bond n)) (μ ν : Fin 4) (x : Site n)
      (hp : IsPlaqBdry (σ ++ rv σ') μ ν x) (hα : hs (((plaq U μ ν x : GLN) : Mat) - 1) ≤ α) :
      Reduces U α m (γ₁ ++ σ' ++ γ₂) → Reduces U α (m + 1) (γ₁ ++ σ ++ γ₂)

lemma hol_rotate (V : Config N n) (l : List (Bond n)) (k : ℕ) :
    ∃ W : GLN, V.hol (l.rotate k) = W⁻¹ * V.hol l * W ∧ ∃ l₁, W = V.hol l₁ ∧ l₁ <+: l := by
  rw [List.rotate_eq_drop_append_take_mod]
  refine ⟨V.hol (l.take (k % l.length)), ?_, _, rfl, List.take_prefix _ _⟩
  have hl : V.hol l = V.hol (l.take (k % l.length)) * V.hol (l.drop (k % l.length)) := by
    rw [← LatticePaths.hol_append, List.take_append_drop]
  rw [hl, LatticePaths.hol_append]
  group

lemma hs_conj_sub_one {W V : GLN} (hW : (W : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    hs (((W⁻¹ * V * W : GLN) : Mat) - 1) = hs ((V : Mat) - 1) := by
  have hWi : ((W⁻¹ : GLN) : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    rw [LatticePaths.inv_val_eq_star hW]; exact Unitary.star_mem hW
  have e : ((W⁻¹ * V * W : GLN) : Mat) - 1 = ((W⁻¹ : GLN) : Mat) * ((V : Mat) - 1) * (W : Mat) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
  rw [e, hs_unitary_mul _ _ _ hWi hW]

lemma hs_inv_sub_one {W : GLN} (hW : (W : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    hs (((W⁻¹ : GLN) : Mat) - 1) = hs ((W : Mat) - 1) := by
  have hWi : ((W⁻¹ : GLN) : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    rw [LatticePaths.inv_val_eq_star hW]; exact Unitary.star_mem hW
  have e : ((W⁻¹ : GLN) : Mat) - 1 = -(((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1) * 1) := by
    rw [Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, Units.inv_mul]; abel
  rw [e, show -(((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1) * 1) = (-1 : ℂ) • (((W⁻¹ : GLN) : Mat) * ((W : Mat) - 1) * 1)
    by simp, hs_smul, hs_unitary_mul _ _ _ hWi (Submonoid.one_mem _)]
  simp

lemma hs_mul_sub_one {W₁ W₂ : GLN} (h₂ : (W₂ : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    hs (((W₁ * W₂ : GLN) : Mat) - 1) ≤ hs ((W₁ : Mat) - 1) + hs ((W₂ : Mat) - 1) := by
  have e : ((W₁ * W₂ : GLN) : Mat) - 1 = ((W₁ : Mat) - 1) * (W₂ : Mat) + ((W₂ : Mat) - 1) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e]
  refine (hs_add_le _ _).trans (le_of_eq ?_)
  have := hs_unitary_mul 1 (W₂ : Mat) ((W₁ : Mat) - 1) (Submonoid.one_mem _) h₂
  rw [Matrix.one_mul] at this
  rw [this]

/-- A plaquette read from any corner, in either orientation, has `|U(P) - id| = |U(∂p) - id|`. -/
lemma hs_plaqBdry {U : Config N n} (hU : U.IsGaugeField) {P : List (Bond n)} {μ ν : Fin 4} {x : Site n}
    (hP : IsPlaqBdry P μ ν x) : hs (((U.hol P : GLN) : Mat) - 1) = hs (((plaq U μ ν x : GLN) : Mat) - 1) := by
  obtain ⟨k, rfl | rfl⟩ := hP
  · obtain ⟨W, hW, l₁, rfl, -⟩ := hol_rotate U (plaqPath μ ν x) k
    rw [hW, hs_conj_sub_one (LatticePaths.hol_isU hU l₁)]; rfl
  · obtain ⟨W, hW, l₁, rfl, -⟩ := hol_rotate U (plaqPath μ ν x) k
    have hrv : U.hol (rv ((plaqPath μ ν x).rotate k)) = (U.hol ((plaqPath μ ν x).rotate k))⁻¹ :=
      Transports.hol_rev U _
    rw [hrv, hs_inv_sub_one (LatticePaths.hol_isU hU _), hW, hs_conj_sub_one (LatticePaths.hol_isU hU l₁)]; rfl

/-- **`lem:block-holonomies`(i)**: a path reduced to the trivial path by `m` moves across plaquettes with
`|U(∂p) - id| ≤ α` has `|U(γ) - id| ≤ mα` and `‖U(γ) - id‖ ≤ √N mα`. -/
theorem block_holonomies_i {U : Config N n} (hU : U.IsGaugeField) {α : ℝ} {m : ℕ} {γ : List (Bond n)}
    (h : Reduces U α m γ) :
    hs (((U.hol γ : GLN) : Mat) - 1) ≤ m * α ∧ ‖((U.hol γ : GLN) : Mat) - 1‖ ≤ Real.sqrt N * (m * α) := by
  have key : hs (((U.hol γ : GLN) : Mat) - 1) ≤ m * α := by
    induction h with
    | nil => simp [Config.hol, hs_zero']
    | cancel γ₁ γ₂ b _ ih =>
      have e : U.hol (γ₁ ++ [b, b.rev] ++ γ₂) = U.hol (γ₁ ++ γ₂) := by
        simp only [LatticePaths.hol_append, LatticePaths.hol_cons, LatticePaths.hol_nil, Config.val_rev]
        group
      rwa [e]
    | move γ₁ σ σ' γ₂ μ ν x hp hα _ ih =>
      -- `U(γ₁σγ₂) = U(γ₁)U(σσ'⁻¹)U(γ₁)⁻¹ · U(γ₁σ'γ₂)`
      have e : U.hol (γ₁ ++ σ ++ γ₂) =
          (U.hol γ₁)⁻¹⁻¹ * U.hol (σ ++ rv σ') * (U.hol γ₁)⁻¹ * U.hol (γ₁ ++ σ' ++ γ₂) := by
        simp only [LatticePaths.hol_append]
        rw [show U.hol (rv σ') = (U.hol σ')⁻¹ from Transports.hol_rev U σ']
        group
      rw [e]
      have hu1 : ((U.hol γ₁)⁻¹ : GLN) ∈ {W : GLN | (W : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ} :=
        LatticePaths.IsU.inv (LatticePaths.hol_isU hU γ₁)
      refine (hs_mul_sub_one (LatticePaths.hol_isU hU _)).trans ?_
      rw [hs_conj_sub_one hu1, hs_plaqBdry hU hp]
      push_cast
      linarith
  exact ⟨key, (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg _))⟩

end BlockHolonomies
end CoreLean

end
