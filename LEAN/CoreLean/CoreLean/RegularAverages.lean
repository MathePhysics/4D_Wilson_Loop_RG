/-
`prop:regular-averages` of BALABAN_CORE.tex (`396a6241b73c`): the plaquettes of the average of a regular
field.

This file: the analytic tools of the proof of (i).
* `norm_LogM_le`, `norm_LogM_sub_le`: `‖Log W‖ ≤ 2‖W - 1‖` and `‖Log W - (W - 1)‖ ≤ 2‖W - 1‖²` for
  `‖W - 1‖ ≤ 1/2`, from the series of `Log`.
* `prod_exp_bound`: `‖∏ e^{X_l} - 1 - Σ X_l‖ ≤ e^t - 1 - t`, `t = Σ‖X_l‖` ("multiplying out the
  exponentials").
* `hol_lin`: for a field with `V(b) = e^{iA_b}` on the bonds of a path `γ`, `‖A_b‖ ≤ a`, and
  `t = |γ|a ≤ 1`: `‖V(γ) - 1 - iA(γ)‖ ≤ t²` and `‖V(γ) - 1‖ ≤ 2t`, `A(γ) = Σ_b A_b`.
* `hol_gauge`: `U^u(γ) = u(γ₋)U(γ)u(γ₊)⁻¹` for a path.
-/
import CoreLean.AxialStraightLattice
import CoreLean.Transports

open Matrix NormedSpace BakerCampbellHausdorff
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace RegularAverages

open LatticePaths LatticeKappa

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### The logarithm near the identity -/

/-- `‖Log W‖ ≤ 2‖W - 1‖` for `‖W - 1‖ ≤ 1/2`. -/
lemma norm_LogM_le {W : Mat} (hW : ‖W - 1‖ ≤ 1 / 2) : ‖LogM W‖ ≤ 2 * ‖W - 1‖ := by
  have h1 : ‖W - 1‖ < 1 := by linarith
  have := norm_log1p_le_div (𝕂 := ℂ) h1
  unfold LogM
  refine this.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (W - 1)]

/-- `‖Log W - (W - 1)‖ ≤ 2‖W - 1‖²` for `‖W - 1‖ ≤ 1/2`: the terms of order at least two of the series. -/
lemma norm_LogM_sub_le {W : Mat} (hW : ‖W - 1‖ ≤ 1 / 2) : ‖LogM W - (W - 1)‖ ≤ 2 * ‖W - 1‖ ^ 2 := by
  set u := W - 1
  have hu : ‖u‖ < 1 := by linarith
  have h0 := hasSum_log1p (𝕂 := ℂ) hu
  have h2 : HasSum (fun n => logCoeff ℂ (n + 2) • u ^ (n + 2)) (log1p ℂ u - u) := by
    rw [← hasSum_nat_add_iff' 2] at h0
    simpa [Finset.sum_range_succ, logCoeff_zero, logCoeff_one] using h0
  have hg : HasSum (fun n : ℕ => ‖u‖ ^ 2 * ‖u‖ ^ n) (‖u‖ ^ 2 * (1 - ‖u‖)⁻¹) :=
    (hasSum_geometric_of_lt_one (norm_nonneg u) hu).mul_left _
  have hb := h2.norm_le_of_bounded hg fun n => by
    rw [norm_smul]
    have c1 : ‖logCoeff ℂ (n + 2)‖ ≤ 1 := norm_logCoeff_le_one ℂ (n + 2)
    have c2 : ‖u ^ (n + 2)‖ ≤ ‖u‖ ^ (n + 2) := norm_pow_le' u (by omega)
    calc ‖logCoeff ℂ (n + 2)‖ * ‖u ^ (n + 2)‖ ≤ 1 * ‖u‖ ^ (n + 2) :=
          mul_le_mul c1 c2 (norm_nonneg _) zero_le_one
      _ = ‖u‖ ^ 2 * ‖u‖ ^ n := by ring
  unfold LogM
  refine hb.trans ?_
  have : (1 - ‖u‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  nlinarith [sq_nonneg ‖u‖]

/-! ### Products of exponentials -/

lemma norm_list_sum_le' : ∀ l : List Mat, ‖l.sum‖ ≤ (l.map norm).sum
  | [] => by simp
  | X :: l => by
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_list_sum_le' l))

/-- `‖e^X - 1 - X‖ ≤ e^{‖X‖} - 1 - ‖X‖`. -/
lemma norm_exp_sub_lin_le (X : Mat) : ‖exp X - 1 - X‖ ≤ Real.exp ‖X‖ - 1 - ‖X‖ := by
  have h := norm_exp_sub_quad_le X
  have h2 : ‖(2 : ℂ)⁻¹ • X ^ 2‖ ≤ ‖X‖ ^ 2 / 2 := by
    rw [norm_smul, norm_inv, Complex.norm_ofNat]
    have := norm_pow_le' X (by norm_num : 0 < 2)
    linarith
  have e : exp X - 1 - X = (exp X - 1 - X - (2 : ℂ)⁻¹ • X ^ 2) + (2 : ℂ)⁻¹ • X ^ 2 := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  unfold phi3 at h
  linarith

/-- `‖e^X‖ ≤ e^{‖X‖}`. -/
lemma norm_exp_le' (X : Mat) : ‖exp X‖ ≤ Real.exp ‖X‖ := by
  have h := norm_exp_sub_lin_le X
  have e : exp X = (exp X - 1 - X) + 1 + X := by abel
  rw [e]
  have := norm_one_mat_le (N := N)
  calc ‖exp X - 1 - X + 1 + X‖ ≤ ‖exp X - 1 - X‖ + ‖(1 : Mat)‖ + ‖X‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Real.exp ‖X‖ := by linarith

/-- Multiplying out the exponentials: `‖∏ e^{X_l} - 1 - Σ X_l‖ ≤ e^t - 1 - t` and `‖∏ e^{X_l}‖ ≤ e^t`,
`t = Σ‖X_l‖`. -/
lemma prod_exp_bound : ∀ l : List Mat,
    ‖(l.map exp).prod - 1 - l.sum‖ ≤ Real.exp (l.map norm).sum - 1 - (l.map norm).sum ∧
      ‖(l.map exp).prod‖ ≤ Real.exp (l.map norm).sum
  | [] => by simpa using norm_one_mat_le (N := N)
  | X :: l => by
    obtain ⟨h1, h2⟩ := prod_exp_bound l
    set Q := (l.map exp).prod
    set S := l.sum
    set t := (l.map norm).sum
    have hS : ‖S‖ ≤ t := by
      exact norm_list_sum_le' l
    have hR := norm_exp_sub_lin_le X
    have hQ1 : ‖Q - 1‖ ≤ Real.exp t - 1 := by
      have e : Q - 1 = (Q - 1 - S) + S := by abel
      rw [e]; linarith [norm_add_le (Q - 1 - S) S]
    have hx := norm_nonneg X
    have ht : 0 ≤ t := List.sum_nonneg (by simp)
    have hex := Real.add_one_le_exp ‖X‖
    have het := Real.add_one_le_exp t
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    constructor
    · have e : exp X * Q - 1 - (X + S) = (Q - 1 - S) + X * (Q - 1) + (exp X - 1 - X) * Q := by
        noncomm_ring
      rw [e]
      have b2 : ‖X * (Q - 1)‖ ≤ ‖X‖ * (Real.exp t - 1) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hQ1 hx)
      have b3 : ‖(exp X - 1 - X) * Q‖ ≤ (Real.exp ‖X‖ - 1 - ‖X‖) * Real.exp t :=
        (norm_mul_le _ _).trans (mul_le_mul hR h2 (norm_nonneg _) (by linarith))
      have hsum : Real.exp (‖X‖ + t) = Real.exp ‖X‖ * Real.exp t := Real.exp_add _ _
      calc ‖Q - 1 - S + X * (Q - 1) + (exp X - 1 - X) * Q‖
          ≤ ‖Q - 1 - S‖ + ‖X * (Q - 1)‖ + ‖(exp X - 1 - X) * Q‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ Real.exp (‖X‖ + t) - 1 - (‖X‖ + t) := by rw [hsum]; nlinarith
    · calc ‖exp X * Q‖ ≤ ‖exp X‖ * ‖Q‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖X‖ * Real.exp t :=
            mul_le_mul (norm_exp_le' X) h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (‖X‖ + t) := (Real.exp_add _ _).symm

/-- With `t ≤ T ≤ 1`: `‖∏ e^{X_l} - 1 - Σ X_l‖ ≤ T²` and `‖∏ e^{X_l} - 1‖ ≤ 2T`. -/
lemma prod_exp_small (l : List Mat) {T : ℝ} (hT : (l.map norm).sum ≤ T) (hT1 : T ≤ 1) :
    ‖(l.map exp).prod - 1 - l.sum‖ ≤ T ^ 2 ∧ ‖(l.map exp).prod - 1‖ ≤ 2 * T := by
  obtain ⟨h1, -⟩ := prod_exp_bound l
  set t := (l.map norm).sum
  have ht : 0 ≤ t := List.sum_nonneg (by simp)
  have hq : Real.exp t - 1 - t ≤ t ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := t) (by rw [abs_of_nonneg ht]; linarith)
    exact (le_abs_self _).trans this
  have hS : ‖l.sum‖ ≤ t := norm_list_sum_le' l
  have hq2 : t ^ 2 ≤ T ^ 2 := by nlinarith
  refine ⟨by linarith, ?_⟩
  have e : (l.map exp).prod - 1 = ((l.map exp).prod - 1 - l.sum) + l.sum := by abel
  rw [e]
  have : t ^ 2 ≤ t := by nlinarith
  linarith [norm_add_le ((l.map exp).prod - 1 - l.sum) l.sum]

/-! ### Holonomies near the identity -/

variable {n : ℕ} [NeZero n]

/-- `A(γ) = Σ_{b ∈ γ} A_b`. -/
def Apath (A : Bond n → Mat) (γ : List (Bond n)) : Mat := (γ.map A).sum

lemma Apath_append (A : Bond n → Mat) (γ δ : List (Bond n)) :
    Apath A (γ ++ δ) = Apath A γ + Apath A δ := by
  simp [Apath]

lemma val_hol (V : Config N n) : ∀ γ : List (Bond n),
    ((V.hol γ : GLN) : Mat) = (γ.map fun b => ((V.val b : GLN) : Mat)).prod
  | [] => by simp [Config.hol]
  | b :: γ => by rw [hol_cons, Units.val_mul, val_hol V γ]; simp

lemma norm_Apath_le (A : Bond n → Mat) {a : ℝ} (γ : List (Bond n)) (hA : ∀ b ∈ γ, ‖A b‖ ≤ a) :
    ‖Apath A γ‖ ≤ γ.length * a := by
  unfold Apath
  refine (norm_list_sum_le' _).trans ?_
  have := List.sum_le_length_nsmul (γ.map fun b => ‖A b‖) a (by simpa using hA)
  simpa [List.map_map, Function.comp_def] using this

/-- The linearisation of a holonomy: for `V(b) = e^{iA_b}`, `‖A_b‖ ≤ a` on the bonds of `γ`, and
`t = |γ|a ≤ 1`: `‖V(γ) - 1 - iA(γ)‖ ≤ t²` and `‖V(γ) - 1‖ ≤ 2t`. -/
lemma hol_lin (V : Config N n) (A : Bond n → Mat) {a : ℝ} (γ : List (Bond n))
    (hV : ∀ b ∈ γ, ((V.val b : GLN) : Mat) = exp (Complex.I • A b)) (hA : ∀ b ∈ γ, ‖A b‖ ≤ a)
    (ht : γ.length * a ≤ 1) :
    ‖((V.hol γ : GLN) : Mat) - 1 - Complex.I • Apath A γ‖ ≤ (γ.length * a) ^ 2 ∧
      ‖((V.hol γ : GLN) : Mat) - 1‖ ≤ 2 * (γ.length * a) := by
  have e1 : ((V.hol γ : GLN) : Mat) = ((γ.map fun b => Complex.I • A b).map exp).prod := by
    rw [val_hol, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun b hb => hV b hb)
  have e2 : (γ.map fun b => Complex.I • A b).sum = Complex.I • Apath A γ := by
    unfold Apath
    rw [List.smul_sum, List.map_map]
    rfl
  have hT : ((γ.map fun b => Complex.I • A b).map norm).sum ≤ γ.length * a := by
    have := List.sum_le_length_nsmul ((γ.map fun b => Complex.I • A b).map norm) a
      (by simpa [norm_smul] using hA)
    simpa using this
  have := prod_exp_small _ hT ht
  rw [e1, ← e2]
  exact this

/-- `U^u(γ) = u(γ₋)U(γ)u(γ₊)⁻¹` for a path from `z`. -/
lemma hol_gauge (U : Config N n) (u : Site n → GLN) : ∀ (γ : List (Bond n)) (z : Site n), Chain z γ →
    (U.gauge u).hol γ = u z * U.hol γ * (u (endpt z γ))⁻¹
  | [], z, _ => by simp [Config.hol, endpt]
  | b :: γ, z, ⟨hb, hγ⟩ => by
    rw [hol_cons, hol_cons, Config.val_gauge, hol_gauge U u γ b.plus hγ, hb]
    show _ = u z * (U.val b * U.hol γ) * (u (endpt b.plus γ))⁻¹
    rw [← hb]
    group

/-- The reversed path `γ⁻¹`. -/
def rv (γ : List (Bond n)) : List (Bond n) := (γ.map Bond.rev).reverse

lemma length_rv (γ : List (Bond n)) : (rv γ).length = γ.length := by simp [rv]

lemma Apath_rv (A : Bond n → Mat) (hA : ∀ b, A b.rev = -A b) (γ : List (Bond n)) :
    Apath A (rv γ) = -Apath A γ := by
  induction γ with
  | nil => simp [rv, Apath]
  | cons b γ ih =>
    simp only [rv, Apath, List.map_cons, List.reverse_cons, List.map_append, List.sum_append,
      List.map_reverse, List.sum_reverse, List.sum_cons, List.map_nil, List.sum_nil, add_zero] at ih ⊢
    rw [ih, hA, neg_add]
    abel

/-! ### The average on one coarse bond -/

/-- `V(b) = e^{iA_b}` with `‖A_b‖ ≤ a`. -/
def Good (V : Config N n) (A : Bond n → Mat) (a : ℝ) (b : Bond n) : Prop :=
  ((V.val b : GLN) : Mat) = exp (Complex.I • A b) ∧ ‖A b‖ ≤ a

lemma good_rev {V : Config N n} {A : Bond n → Mat} {a : ℝ} (hA : ∀ b, A b.rev = -A b) {b : Bond n}
    (hb : Good V A a b) : Good V A a b.rev := by
  refine ⟨?_, by rw [hA, norm_neg]; exact hb.2⟩
  have hu : V.val b = expU (Complex.I • A b) := Units.ext (by rw [expU_val]; exact hb.1)
  rw [Config.val_rev, hu, expU_inv, expU_val, hA, smul_neg]

lemma good_rv {V : Config N n} {A : Bond n → Mat} {a : ℝ} (hA : ∀ b, A b.rev = -A b)
    {γ : List (Bond n)} (hγ : ∀ b ∈ γ, Good V A a b) : ∀ b ∈ rv γ, Good V A a b := by
  intro b hb
  simp only [rv, List.mem_reverse, List.mem_map] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  exact good_rev hA (hγ b' hb')

section Weights

variable {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)]

lemma norm_wt (x : ι) : ‖Average.wt P P x‖ =
    ((Fintype.card ι : ℝ) * Fintype.card (P x) * Fintype.card (P x))⁻¹ := by
  simp [Average.wt, norm_inv]

/-- `Σ_{x,Γ,Γ'} |w_x| = 1`. -/
lemma wt_sum_norm (hι : 0 < Fintype.card ι) (hP : ∀ x, 0 < Fintype.card (P x)) :
    ∑ x, ∑ _Γ : P x, ∑ _Γ' : P x, ‖Average.wt P P x‖ = 1 := by
  have hx : ∀ x : ι, ∑ _Γ : P x, ∑ _Γ' : P x, ‖Average.wt P P x‖ = (Fintype.card ι : ℝ)⁻¹ :=
    fun x => by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, norm_wt]
      have h1 : (0 : ℝ) < Fintype.card (P x) := by exact_mod_cast hP x
      have h2 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
      field_simp
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  field_simp

/-- `‖Σ_{x,Γ,Γ'} w_x E_{xΓΓ'}‖ ≤ e` for `‖E‖ ≤ e`. -/
lemma norm_wsum_le (hι : 0 < Fintype.card ι) (hP : ∀ x, 0 < Fintype.card (P x))
    (E : ∀ x, P x → P x → Mat) {e : ℝ} (hE : ∀ x Γ Γ', ‖E x Γ Γ'‖ ≤ e) :
    ‖∑ x, ∑ Γ, ∑ Γ', Average.wt P P x • E x Γ Γ'‖ ≤ e := by
  calc ‖∑ x, ∑ Γ, ∑ Γ', Average.wt P P x • E x Γ Γ'‖
      ≤ ∑ x, ∑ Γ : P x, ∑ Γ' : P x, ‖Average.wt P P x‖ * e := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Γ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Γ' _ => ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hE x Γ Γ') (norm_nonneg _)
    _ = e := by simp only [← Finset.sum_mul, wt_sum_norm hι hP, one_mul]

/-- The linear part of `β_c`: `Σ_{x,Γ,Γ'} w_x (F_{xΓ} + H_x - F'_{xΓ'} - K)
= Σ_x |ι|⁻¹(F̄_x + H_x - F̄'_x) - K`, with the means `F̄_x = |P_x|⁻¹ Σ_Γ F_{xΓ}`. -/
lemma wsum_lin (hι : 0 < Fintype.card ι) (hP : ∀ x, 0 < Fintype.card (P x))
    (F F' : ∀ x, P x → Mat) (H : ι → Mat) (K : Mat) :
    ∑ x, ∑ Γ, ∑ Γ', Average.wt P P x • (F x Γ + H x - F' x Γ' - K) =
      ∑ x, (Fintype.card ι : ℂ)⁻¹ • ((Fintype.card (P x) : ℂ)⁻¹ • ∑ Γ, F x Γ + H x -
        (Fintype.card (P x) : ℂ)⁻¹ • ∑ Γ', F' x Γ') - K := by
  have hι' : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hι.ne'
  have hx : ∀ x, ∑ Γ : P x, ∑ Γ' : P x, Average.wt P P x • (F x Γ + H x - F' x Γ' - K) =
      (Fintype.card ι : ℂ)⁻¹ • ((Fintype.card (P x) : ℂ)⁻¹ • ∑ Γ, F x Γ + H x -
        (Fintype.card (P x) : ℂ)⁻¹ • ∑ Γ', F' x Γ') - (Fintype.card ι : ℂ)⁻¹ • K := by
    intro x
    have hc : (Fintype.card (P x) : ℂ) ≠ 0 := by exact_mod_cast (hP x).ne'
    simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, ← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Average.wt]
    match_scalars <;> field_simp
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hι', one_smul]

end Weights

variable (G : GaugeGroup N) {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)]

/-- The average `M(V)(c)` on the coarse bond `c` from `y` in the direction `κ`, of length `L` in the units
of the fine lattice, with the points `x = y + off(x)` and the paths `stair(ord x Γ)` from both ends (one
family `𝐆` for both ends, as in `def:block-paths`). -/
def avgB (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : GLN :=
  Average.avg G.inChart G.chartLog (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
    (fun x => V.hol (segZ κ (ofs y (off x)) L))
    (fun x Γ' => V.hol (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0))
    (V.hol (segZ κ y L))

variable {G}

/-- The conclusion of `lem:chart`(ii) for the radius `r`. -/
def ChartR (G : GaugeGroup N) (r : ℝ) : Prop :=
  ∀ U ∈ G.carrier, ‖(U : Mat) - 1‖ ≤ r →
    ∃ A ∈ G.lie, ‖A‖ < Real.pi ∧ exp (Complex.I • A) = (U : Mat) ∧ LogM (U : Mat) = Complex.I • A ∧
      ∀ A' ∈ G.lie, ‖A'‖ < Real.pi → exp (Complex.I • A') = (U : Mat) → A' = A

/-- The mean `Ā(y, x)` of `A(Γ)` over the paths `Γ` from `y` to `y + off(x)`. -/
def Abar (A : Bond n → Mat) (y : Site n) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (x : ι) : Mat :=
  (Fintype.card (P x) : ℂ)⁻¹ • ∑ Γ, Apath A (stair y (off x) (ord x Γ) 0)

/-- The first-order part of `log M(V)(c)`: `|ι|⁻¹ Σ_x (Ā(c₋, x) + A([x, x']) - Ā(c₊, x'))`. -/
def LIN (A : Bond n → Mat) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : Mat :=
  ∑ x, (Fintype.card ι : ℂ)⁻¹ • (Abar A y off ord x + Apath A (segZ κ (ofs y (off x)) L) -
    Abar A (ofs y (Pi.single κ (L : ℤ))) off ord x)

/-- The linearisation of the average on one coarse bond: if `V(b) = e^{iA_b}`, `‖A_b‖ ≤ a`, on the bonds
of the paths of the average, the loops have at most `m₀` bonds, and `s = m₀a` is small, then
`M(V)(c) = e^{iZ}` with `‖Z - LIN‖ ≤ 1042s²` and `‖Z‖ ≤ 3s`. -/
theorem avgB_lin {r : ℝ} (hch : ChartR G r) :
    ∀ {n : ℕ} [NeZero n] (V : Config N n), IsGField G V →
      ∀ (A : Bond n → Mat), (∀ b, A b.rev = -A b) → ∀ (a : ℝ) (m₀ : ℕ) (y : Site n) (κ : Fin 4)
      (L : ℕ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)), 0 < Fintype.card ι →
      (∀ x, 0 < Fintype.card (P x)) →
      (∀ x Γ, ∀ b ∈ stair y (off x) (ord x Γ) 0, Good V A a b) →
      (∀ x Γ, ∀ b ∈ stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ) 0, Good V A a b) →
      (∀ x, ∀ b ∈ segZ κ (ofs y (off x)) L, Good V A a b) → (∀ b ∈ segZ κ y L, Good V A a b) →
      (∀ x Γ Γ', (stair y (off x) (ord x Γ) 0).length + (segZ κ (ofs y (off x)) L).length +
        (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0).length +
        (segZ κ y L).length ≤ m₀) →
      0 ≤ a → m₀ * a ≤ 1 / 512 → 2 * (m₀ * a) ≤ r →
      ∃ Z : Mat, avgB G V y κ L off ord = expU (Complex.I • Z) ∧
        ‖Z - LIN A y κ L off ord‖ ≤ 1042 * (m₀ * a) ^ 2 ∧ ‖Z‖ ≤ 5 * (m₀ * a) := by
  intro n _ V hV A hrev a m₀ y κ L off ord hι hP hg hg' hh hk hlen ha hs hsr
  set s : ℝ := m₀ * a with hs_def
  have hs0 : 0 ≤ s := by positivity
  -- the paths of the loops
  set gp : ∀ x, P x → List (Bond n) := fun x Γ => stair y (off x) (ord x Γ) 0 with hgp
  set gp' : ∀ x, P x → List (Bond n) :=
    fun x Γ => stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ) 0 with hgp'
  set hp : ι → List (Bond n) := fun x => segZ κ (ofs y (off x)) L with hhp
  set kp : List (Bond n) := segZ κ y L with hkp
  set lp : ∀ x, P x → P x → List (Bond n) := fun x Γ Γ' => gp x Γ ++ hp x ++ rv (gp' x Γ') ++ rv kp
    with hlp
  have hloop : ∀ x Γ Γ', Average.loop (fun x Γ => V.hol (gp x Γ)) (fun x => V.hol (hp x))
      (fun x Γ' => V.hol (gp' x Γ')) (V.hol kp) x Γ Γ' = V.hol (lp x Γ Γ') := fun x Γ Γ' => by
    simp only [Average.loop, hlp, hol_append, rv, Transports.hol_rev]
  have hgood : ∀ x Γ Γ', ∀ b ∈ lp x Γ Γ', Good V A a b := fun x Γ Γ' b hb => by
    simp only [hlp, List.mem_append] at hb
    rcases hb with ((hb | hb) | hb) | hb
    · exact hg x Γ b hb
    · exact hh x b hb
    · exact good_rv hrev (hg' x Γ') b hb
    · exact good_rv hrev hk b hb
  have hlenl : ∀ x Γ Γ', ((lp x Γ Γ').length : ℝ) * a ≤ s := fun x Γ Γ' => by
    have : (lp x Γ Γ').length ≤ m₀ := by
      simp only [hlp, List.length_append, length_rv]
      exact hlen x Γ Γ'
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) ha
  have hlenk : (kp.length : ℝ) * a ≤ s := by
    obtain ⟨x⟩ : Nonempty ι := Fintype.card_pos_iff.1 hι
    obtain ⟨Γ⟩ : Nonempty (P x) := Fintype.card_pos_iff.1 (hP x)
    have := hlen x Γ Γ
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : kp.length ≤ m₀)) ha
  have hs1 : s ≤ 1 := by linarith
  -- the loops are close to `id`, in `G`, and in the chart
  have hlin : ∀ x Γ Γ', ‖((V.hol (lp x Γ Γ') : GLN) : Mat) - 1 - Complex.I • Apath A (lp x Γ Γ')‖ ≤
      s ^ 2 ∧ ‖((V.hol (lp x Γ Γ') : GLN) : Mat) - 1‖ ≤ 2 * s := fun x Γ Γ' => by
    have h := hol_lin V A (lp x Γ Γ') (fun b hb => (hgood x Γ Γ' b hb).1)
      (fun b hb => (hgood x Γ Γ' b hb).2) ((hlenl x Γ Γ').trans hs1)
    have hl0 : 0 ≤ ((lp x Γ Γ').length : ℝ) * a := by positivity
    exact ⟨h.1.trans (pow_le_pow_left₀ hl0 (hlenl x Γ Γ') 2), h.2.trans (by linarith [hlenl x Γ Γ'])⟩
  have hchart : ∀ x Γ Γ', G.inChart (V.hol (lp x Γ Γ')) ∧
      G.chartLog (V.hol (lp x Γ Γ')) = LogM ((V.hol (lp x Γ Γ') : GLN) : Mat) := fun x Γ Γ' => by
    obtain ⟨A', hA', hn', he', hl', -⟩ := hch _ (hV.hol_mem _) ((hlin x Γ Γ').2.trans hsr)
    obtain ⟨hin, hlog⟩ := GaugeGroup.chartLog_eq hA' hn' he'.symm
    exact ⟨hin, hlog.trans hl'.symm⟩
  -- the error of each term of `β_c`
  have hI : ‖(1 / Complex.I : ℂ)‖ = 1 := by simp
  have hIA : ∀ X : Mat, (1 / Complex.I : ℂ) • (Complex.I • X) = X := fun X => by
    rw [smul_smul, one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  have hlog_err : ∀ W : GLN, ∀ X : Mat, ‖(W : Mat) - 1 - Complex.I • X‖ ≤ s ^ 2 →
      ‖(W : Mat) - 1‖ ≤ 2 * s → ‖(1 / Complex.I : ℂ) • LogM (W : Mat) - X‖ ≤ 9 * s ^ 2 :=
    fun W X h1 h2 => by
      have h3 := norm_LogM_sub_le (W := (W : Mat)) (by linarith)
      have e : (1 / Complex.I : ℂ) • LogM (W : Mat) - X =
          (1 / Complex.I : ℂ) • (LogM (W : Mat) - ((W : Mat) - 1)) +
            (1 / Complex.I : ℂ) • ((W : Mat) - 1 - Complex.I • X) := by
        simp only [smul_sub, hIA]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, hI, one_mul, one_mul]
      nlinarith [norm_nonneg ((W : Mat) - 1)]
  have hApl : ∀ x Γ Γ', Apath A (lp x Γ Γ') =
      Apath A (gp x Γ) + Apath A (hp x) - Apath A (gp' x Γ') - Apath A kp := fun x Γ Γ' => by
    simp only [hlp, Apath_append, Apath_rv A hrev]; abel
  set err : ∀ x, P x → P x → Mat := fun x Γ Γ' =>
    (1 / Complex.I : ℂ) • G.chartLog (V.hol (lp x Γ Γ')) - Apath A (lp x Γ Γ') with herr_def
  have herr : ∀ x Γ Γ', ‖err x Γ Γ'‖ ≤ 9 * s ^ 2 := fun x Γ Γ' => by
    simp only [herr_def, (hchart x Γ Γ').2]
    exact hlog_err _ _ (hlin x Γ Γ').1 (hlin x Γ Γ').2
  -- `β_c(V)`
  set β := Average.beta G.chartLog (fun x Γ => V.hol (gp x Γ)) (fun x => V.hol (hp x))
    (fun x Γ' => V.hol (gp' x Γ')) (V.hol kp) with hβ_def
  have hlinsum : ∑ x, ∑ Γ, ∑ Γ', Average.wt P P x • Apath A (lp x Γ Γ') =
      LIN A y κ L off ord - Apath A kp := by
    simp only [hApl]
    rw [wsum_lin hι hP]
    simp only [LIN, Abar, Finset.smul_sum, hgp, hgp', hhp]
  have hβ : β = (LIN A y κ L off ord - Apath A kp) + ∑ x, ∑ Γ, ∑ Γ', Average.wt P P x • err x Γ Γ' := by
    rw [← hlinsum, hβ_def, Average.beta]
    simp only [hloop, herr_def, ← Finset.sum_add_distrib, ← smul_add]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun Γ _ =>
      Finset.sum_congr rfl fun Γ' _ => ?_
    congr 1
    abel
  have hβ1 : ‖β - (LIN A y κ L off ord - Apath A kp)‖ ≤ 9 * s ^ 2 := by
    rw [hβ, add_sub_cancel_left]
    exact norm_wsum_le hι hP _ herr
  have hlinn : ‖LIN A y κ L off ord - Apath A kp‖ ≤ s := by
    rw [← hlinsum]
    exact norm_wsum_le hι hP _ fun x Γ Γ' =>
      (norm_Apath_le A _ fun b hb => (hgood x Γ Γ' b hb).2).trans (hlenl x Γ Γ')
  have hkn : ‖Apath A kp‖ ≤ s := (norm_Apath_le A _ fun b hb => (hk b hb).2).trans hlenk
  -- `V([c]) = e^{iY}`
  have hlink := hol_lin V A kp (fun b hb => (hk b hb).1) (fun b hb => (hk b hb).2) (hlenk.trans hs1)
  have hk0 : 0 ≤ (kp.length : ℝ) * a := by positivity
  have hk1 : ‖((V.hol kp : GLN) : Mat) - 1 - Complex.I • Apath A kp‖ ≤ s ^ 2 :=
    hlink.1.trans (pow_le_pow_left₀ hk0 hlenk 2)
  have hk2 : ‖((V.hol kp : GLN) : Mat) - 1‖ ≤ 2 * s := hlink.2.trans (by linarith)
  set Y : Mat := (1 / Complex.I : ℂ) • LogM ((V.hol kp : GLN) : Mat) with hY_def
  have hY1 : ‖Y - Apath A kp‖ ≤ 9 * s ^ 2 := hlog_err _ _ hk1 hk2
  have hYk : V.hol kp = expU (Complex.I • Y) := by
    refine Units.ext ?_
    rw [expU_val, hY_def, smul_smul, mul_one_div_cancel Complex.I_ne_zero, one_smul, exp_LogM]
    linarith
  -- the norms
  have hs2 : s ^ 2 ≤ s / 512 := by nlinarith
  have hβn : ‖β‖ ≤ 2 * s := by
    have := norm_sub_norm_le β (LIN A y κ L off ord - Apath A kp)
    linarith
  have hYn : ‖Y‖ ≤ 2 * s := by
    have := norm_sub_norm_le Y (Apath A kp)
    linarith
  -- `M(V)(c) = e^{iβ}V([c]) = e^{iΨ(β, Y)}`
  have hall : ∀ x Γ Γ', G.inChart (Average.loop (fun x Γ => V.hol (gp x Γ)) (fun x => V.hol (hp x))
      (fun x Γ' => V.hol (gp' x Γ')) (V.hol kp) x Γ Γ') := fun x Γ Γ' => by
    rw [hloop]; exact (hchart x Γ Γ').1
  have hZL : ‖psi β Y - LIN A y κ L off ord‖ ≤ 1042 * s ^ 2 := by
    have hp1 := psi_lipschitz (X := 0) (Y := 0) (X' := β) (Y' := Y) (by simp) (by simp)
      (by linarith) (by linarith)
    rw [psi_zero_right (by simp)] at hp1
    simp only [sub_zero, norm_zero, zero_mul, add_zero] at hp1
    have e : psi β Y - LIN A y κ L off ord = (psi β Y - β - Y) +
        (β - (LIN A y κ L off ord - Apath A kp)) + (Y - Apath A kp) := by abel
    rw [e]
    have hYβ : ‖Y‖ * ‖β‖ ≤ 4 * s ^ 2 := by nlinarith [norm_nonneg Y, norm_nonneg β]
    have := norm_add_le (psi β Y - β - Y + (β - (LIN A y κ L off ord - Apath A kp)))
      (Y - Apath A kp)
    have := norm_add_le (psi β Y - β - Y) (β - (LIN A y κ L off ord - Apath A kp))
    nlinarith
  refine ⟨psi β Y, ?_, hZL, ?_⟩
  · show Average.avg G.inChart G.chartLog (fun x Γ => V.hol (gp x Γ)) (fun x => V.hol (hp x))
      (fun x Γ' => V.hol (gp' x Γ')) (V.hol kp) = _
    unfold Average.avg
    simp only [hall, implies_true, ↓reduceIte]
    rw [← hβ_def, hYk]
    refine Units.ext ?_
    rw [Units.val_mul, expU_val, expU_val, expU_val, exp_I_psi (by linarith [Real.log_two_gt_d9])]
  · have hL : ‖LIN A y κ L off ord‖ ≤ 2 * s := by
      have e : LIN A y κ L off ord = (LIN A y κ L off ord - Apath A kp) + Apath A kp := by abel
      rw [e]
      linarith [norm_add_le (LIN A y κ L off ord - Apath A kp) (Apath A kp)]
    have := norm_sub_norm_le (psi β Y) (LIN A y κ L off ord)
    nlinarith

/-! ### Discrete Stokes -/

lemma segZ_nat (κ : Fin 4) (z : Site n) (L : ℕ) : segZ κ z (L : ℤ) = seg κ true z L := by
  rw [segZ_eq, Int.natAbs_natCast, show sgn (L : ℤ) = true from decide_eq_true (Int.natCast_nonneg _)]

/-- `A` along a straight path in the positive direction. -/
lemma Apath_seg (A : Bond n → Mat) (ρ : Fin 4) : ∀ (k : ℕ) (z : Site n),
    Apath A (seg ρ true z k) = ∑ i ∈ Finset.range k, A ⟨z + i • unit n ρ, ρ, true⟩
  | 0, z => by simp [seg, Apath]
  | k + 1, z => by
    rw [Finset.sum_range_succ']
    show Apath A (⟨z, ρ, true⟩ :: seg ρ true (z + dvec ρ true) k) = _
    have ih := Apath_seg A ρ k (z + dvec ρ true)
    simp only [Apath, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, add_comm, zero_smul, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dvec, ↓reduceIte, succ_nsmul]
    congr 2
    abel

lemma A_neg (A : Bond n → Mat) (hA : ∀ b, A b.rev = -A b) (w : Site n) (ρ : Fin 4) :
    A ⟨w, ρ, false⟩ = -A ⟨w - unit n ρ, ρ, true⟩ := by
  have := hA ⟨w - unit n ρ, ρ, true⟩
  simp only [Bond.rev, Bond.plus, ↓reduceIte, sub_add_cancel, Bool.not_true] at this
  exact this

/-- `A(∂p_{μν}(z)) = A(z, μ) + A(z + e_μ, ν) - A(z + e_ν, μ) - A(z, ν)`. -/
lemma Apath_plaq (A : Bond n → Mat) (hA : ∀ b, A b.rev = -A b) (μ ν : Fin 4) (z : Site n) :
    Apath A (plaqPath μ ν z) = A ⟨z, μ, true⟩ + A ⟨z + unit n μ, ν, true⟩ -
      A ⟨z + unit n ν, μ, true⟩ - A ⟨z, ν, true⟩ := by
  simp only [Apath, plaqPath, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    A_neg A hA]
  rw [show z + unit n μ + unit n ν - unit n μ = z + unit n ν by abel,
    show z + unit n ν - unit n ν = z by abel]
  abel

/-- The discrete Stokes formula on an `L × L` square: the sum of the boundaries of the plaquettes is the
boundary of the square, the inner bonds cancelling. -/
lemma stokes (a : Fin 4 → Site n → Mat) (μ ν : Fin 4) (z : ℕ → ℕ → Site n)
    (h1 : ∀ i j, z i j + unit n ν = z i (j + 1)) (h2 : ∀ i j, z i j + unit n μ = z (i + 1) j) (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      (a μ (z i j) + a ν (z i j + unit n μ) - a μ (z i j + unit n ν) - a ν (z i j)) =
    ∑ i ∈ Finset.range L, (a μ (z i 0) - a μ (z i L)) +
      ∑ j ∈ Finset.range L, (a ν (z L j) - a ν (z 0 j)) := by
  have e : ∀ i j, a μ (z i j) + a ν (z i j + unit n μ) - a μ (z i j + unit n ν) - a ν (z i j) =
      (a μ (z i j) - a μ (z i (j + 1))) + (a ν (z (i + 1) j) - a ν (z i j)) := by
    intro i j; rw [h1, h2]; abel
  simp only [e, Finset.sum_add_distrib, Finset.sum_range_sub']
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ =>
    Finset.sum_range_sub (fun i => a ν (z i j)) L]

/-! ### The gauge on the box `Δ(p')` -/

/-- The lower corner of the box `Δ(p')` of offsets from `y₀`. -/
def loD (h : ℕ) : Fin 4 → ℤ := fun _ => -(h : ℤ)

/-- The upper corner of `Δ(p')`: `3h + 1` in the directions `μ, ν` of `p'`, `h` otherwise. -/
def hiD (h : ℕ) (μ ν : Fin 4) : Fin 4 → ℤ := fun σ => if σ = μ ∨ σ = ν then 3 * (h : ℤ) + 1 else h

/-- The gauge transformation `u(z) = U(τ_z)`, `τ_z` the path from `y₀` through the coordinates
`0, 1, 2, 3` in this order. -/
def uG (U : Config N n) (y₀ : Site n) (h : ℕ) (z : Site n) : GLN :=
  U.hol (stair y₀ (AxialReference.rep y₀ h z) [0, 1, 2, 3] 0)

/-- `A_b = (1/i) Log V(b)` on the positive bonds. -/
def Apos (V : Config N n) (ρ : Fin 4) (z : Site n) : Mat :=
  (1 / Complex.I : ℂ) • LogM ((V ρ z : GLN) : Mat)

/-- `A_b` on all bonds, `A_{b⁻¹} = -A_b`. -/
def Aof (V : Config N n) (b : Bond n) : Mat :=
  if b.pos then Apos V b.dir b.site else -Apos V b.dir (b.site - unit n b.dir)

lemma Aof_rev (V : Config N n) (b : Bond n) : Aof V b.rev = -Aof V b := by
  obtain ⟨z, ρ, s⟩ := b
  cases s
  · simp [Aof, Bond.rev, Bond.plus]
  · simp [Aof, Bond.rev, Bond.plus]

lemma I_smul_Apos (V : Config N n) (ρ : Fin 4) (z : Site n) :
    Complex.I • Apos V ρ z = LogM ((V ρ z : GLN) : Mat) := by
  rw [Apos, smul_smul, mul_one_div_cancel Complex.I_ne_zero, one_smul]

/-- A positive bond with `‖V(b) - 1‖ ≤ δ ≤ 1/2` and its reverse are good with `a = 2δ`. -/
lemma good_pos (V : Config N n) {ρ : Fin 4} {w : Site n} {δ : ℝ}
    (hw : ‖((V ρ w : GLN) : Mat) - 1‖ ≤ δ) (hδ : δ ≤ 1 / 2) :
    Good V (Aof V) (2 * δ) ⟨w, ρ, true⟩ ∧ Good V (Aof V) (2 * δ) ⟨w + unit n ρ, ρ, false⟩ := by
  have hn : ‖Apos V ρ w‖ ≤ 2 * δ := by
    rw [Apos, norm_smul, show ‖(1 / Complex.I : ℂ)‖ = 1 by simp, one_mul]
    exact (norm_LogM_le (hw.trans hδ)).trans (by linarith)
  have hu : V ρ w = expU (Complex.I • Apos V ρ w) :=
    Units.ext (by rw [expU_val, I_smul_Apos, exp_LogM (by linarith)])
  refine ⟨⟨?_, by simpa [Aof] using hn⟩, ⟨?_, by simpa [Aof] using hn⟩⟩
  · simp only [Config.val, Aof, ↓reduceIte]
    rw [hu, expU_val]
  · simp only [Config.val, Aof, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_right]
    rw [hu, expU_inv, expU_val, smul_neg]

/-! ### The Hilbert–Schmidt norm of multiples and sums -/

lemma hs2_smul (c : ℂ) (X : Mat) : hs2 (c • X) = ‖c‖ ^ 2 * hs2 X := by
  unfold hs2 ntr
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul, smul_smul,
    smul_eq_mul, ← mul_assoc, mul_comm _ (star c * c), mul_assoc,
    show star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]]
  exact Complex.re_ofReal_mul _ _

lemma hs_smul (c : ℂ) (X : Mat) : hs (c • X) = ‖c‖ * hs X := by
  rw [hs, hs2_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), hs]

lemma hs_zero' : hs (0 : Mat) = 0 := by simp [hs, hs2, ntr]

lemma hs_sum_le {α : Type*} (s : Finset α) (f : α → Mat) : hs (∑ i ∈ s, f i) ≤ ∑ i ∈ s, hs (f i) :=
  Finset.le_sum_of_subadditive hs hs_zero'.le hs_add_le s f

/-! ### The box `Δ(p')` -/

lemma ofs1 (y : Site n) (w : Fin 4 → ℤ) (ρ : Fin 4) : ofs y (w + Pi.single ρ 1) = ofs y w + unit n ρ := by
  rw [ofs_add_single, one_smul]

/-- The membership in `Δ(p')`, coordinate by coordinate. -/
lemma inD_iff {h : ℕ} {μ ν : Fin 4} (hμν : μ ≠ ν) {w : Fin 4 → ℤ} :
    LatticePaths.InBox (loD h) (hiD h μ ν) w ↔ (-(h : ℤ) ≤ w μ ∧ w μ ≤ 3 * h + 1) ∧ (-(h : ℤ) ≤ w ν ∧ w ν ≤ 3 * h + 1) ∧
      ∀ σ, σ ≠ μ → σ ≠ ν → -(h : ℤ) ≤ w σ ∧ w σ ≤ h := by
  constructor
  · intro hw
    refine ⟨by simpa [loD, hiD] using hw μ, by simpa [loD, hiD] using hw ν, fun σ h1 h2 => ?_⟩
    simpa [loD, hiD, h1, h2] using hw σ
  · rintro ⟨h1, h2, h3⟩ σ
    by_cases hs1 : σ = μ
    · subst hs1; simpa [loD, hiD] using h1
    by_cases hs2 : σ = ν
    · subst hs2; simpa [loD, hiD] using h2
    simpa [loD, hiD, hs1, hs2] using h3 σ hs1 hs2

lemma inD_range {h : ℕ} {μ ν : Fin 4} {w : Fin 4 → ℤ} (hw : LatticePaths.InBox (loD h) (hiD h μ ν) w) (σ : Fin 4) :
    -(h : ℤ) ≤ w σ ∧ w σ ≤ 3 * h + 1 := by
  have := hw σ
  simp only [loD, hiD] at this
  split_ifs at this <;> omega

/-- `Σ_σ |m_σ| ≤ 8h + 2 ≤ 4L` on `Δ(p')`. -/
lemma sum_abs_le {h : ℕ} {μ ν : Fin 4} {m : Fin 4 → ℤ} (hm : LatticePaths.InBox (loD h) (hiD h μ ν) m) :
    ∑ σ, (m σ).natAbs ≤ 8 * h + 2 := by
  calc ∑ σ, (m σ).natAbs
      ≤ ∑ σ : Fin 4, (h + (if σ = μ then 2 * h + 1 else 0) + (if σ = ν then 2 * h + 1 else 0)) :=
        Finset.sum_le_sum fun σ _ => by
          have := hm σ
          simp only [loD, hiD] at this
          by_cases h1 : σ = μ <;> by_cases h2 : σ = ν <;> simp [h1, h2] at this ⊢ <;> omega
    _ = 8 * h + 2 := by simp [Finset.sum_add_distrib]; ring

/-- Two offsets in `[-h - 1, 3h + 2]` with the same site are equal, for `4h + 4 ≤ n`. -/
lemma ofs_inj {h : ℕ} (hn : 4 * h + 4 ≤ n) (y : Site n) {a b : Fin 4 → ℤ}
    (ha : ∀ σ, -(h : ℤ) - 1 ≤ a σ ∧ a σ ≤ 3 * h + 2) (hb : ∀ σ, -(h : ℤ) - 1 ≤ b σ ∧ b σ ≤ 3 * h + 2)
    (e : ofs y a = ofs y b) : a = b := by
  have r1 := AxialReference.rep_ofs y (h + 1) (v := a) (fun σ => by have := ha σ; push_cast; omega)
  have r2 := AxialReference.rep_ofs y (h + 1) (v := b) (fun σ => by have := hb σ; push_cast; omega)
  rw [← r1, ← r2, e]

/-- The bonds of the gauge `V = U^u` in the box are close to `id`: `‖V(b) - id‖ ≤ (8h + 2)β` for
plaquettes of `U` at most `β` in the box (the strip of `eq:axial-strip`). -/
lemma gauge_bound (U : Config N n) (hU : U.IsGaugeField) {h : ℕ} (hn : 4 * h + 4 ≤ n) (y₀ : Site n)
    (μ ν : Fin 4) {β : ℝ} (hβ : 0 ≤ β) (hP : PlaqBound U (boxR y₀ (loD h) (hiD h μ ν)) β)
    (m : Fin 4 → ℤ) (ρ : Fin 4) (hm : LatticePaths.InBox (loD h) (hiD h μ ν) m)
    (hm' : LatticePaths.InBox (loD h) (hiD h μ ν) (m + Pi.single ρ 1)) :
    ‖(((U.gauge (uG U y₀ h)) ρ (ofs y₀ m) : GLN) : Mat) - 1‖ ≤ ((8 * h + 2 : ℕ) : ℝ) * β := by
  have hr : ∀ w, LatticePaths.InBox (loD h) (hiD h μ ν) w → ∀ σ, -(h : ℤ) ≤ w σ ∧ w σ ≤ n - 1 - h := fun w hw σ => by
    have := inD_range hw σ; omega
  have e1 : uG U y₀ h (ofs y₀ m) = U.hol (stair y₀ m [0, 1, 2, 3] 0) := by
    rw [uG, AxialReference.rep_ofs y₀ h (hr m hm)]
  have e2 : uG U y₀ h (ofs y₀ m + unit n ρ) = U.hol (stair y₀ (m + Pi.single ρ 1) [0, 1, 2, 3] 0) := by
    rw [uG, ← ofs1, AxialReference.rep_ofs y₀ h (hr _ hm')]
  have h0 : LatticePaths.InBox (loD h) (hiD h μ ν) 0 := fun σ => by
    simp only [loD, hiD, Pi.zero_apply]; split_ifs <;> omega
  have hsum := sum_abs_le hm
  have split : ∃ P S : List (Fin 4), P ++ ρ :: S = [0, 1, 2, 3] ∧
      ∀ f : Fin 4 → ℕ, (S.map f).sum ≤ ∑ σ, f σ := by
    fin_cases ρ
    · exact ⟨[], [1, 2, 3], rfl, fun f => by simp [Fin.sum_univ_four]; omega⟩
    · exact ⟨[0], [2, 3], rfl, fun f => by simp [Fin.sum_univ_four]⟩
    · exact ⟨[0, 1], [3], rfl, fun f => by simp [Fin.sum_univ_four]⟩
    · exact ⟨[0, 1, 2], [], rfl, fun f => by simp⟩
  obtain ⟨P, S, hPS, hS⟩ := split
  have hst := strip hU hβ hP m P S ρ (by rw [hPS]; decide) h0 hm hm'
  rw [hPS, offs_perm m (List.Perm.refl _)] at hst
  have hv : U.val ⟨ofs y₀ m, ρ, true⟩ = U ρ (ofs y₀ m) := by simp [Config.val]
  rw [hv] at hst
  show ‖((uG U y₀ h (ofs y₀ m) * U ρ (ofs y₀ m) * (uG U y₀ h (ofs y₀ m + unit n ρ))⁻¹ : GLN) : Mat) - 1‖ ≤ _
  rw [e1, e2]
  refine hst.trans (mul_le_mul_of_nonneg_right ?_ hβ)
  exact_mod_cast (hS _).trans hsum

/-- A bond whose ends are sites of the box is good, if the positive bonds of the box are within `δ` of
`id`. -/
lemma good_of_ends (V : Config N n) {h : ℕ} (hn : 4 * h + 4 ≤ n) (y₀ : Site n) (μ ν : Fin 4) {δ : ℝ}
    (hδ : δ ≤ 1 / 2)
    (hV : ∀ m ρ, LatticePaths.InBox (loD h) (hiD h μ ν) m → LatticePaths.InBox (loD h) (hiD h μ ν) (m + Pi.single ρ 1) →
      ‖((V ρ (ofs y₀ m) : GLN) : Mat) - 1‖ ≤ δ)
    (t : Bond n) {v v' : Fin 4 → ℤ} (hv : LatticePaths.InBox (loD h) (hiD h μ ν) v)
    (hv' : LatticePaths.InBox (loD h) (hiD h μ ν) v') (hs : t.site = ofs y₀ v) (hp : t.plus = ofs y₀ v') :
    Good V (Aof V) (2 * δ) t := by
  have ext : ∀ w, LatticePaths.InBox (loD h) (hiD h μ ν) w → ∀ σ, -(h : ℤ) - 1 ≤ w σ ∧ w σ ≤ 3 * h + 2 :=
    fun w hw σ => by have := inD_range hw σ; omega
  have ext1 : ∀ (w : Fin 4 → ℤ) (ρ : Fin 4), LatticePaths.InBox (loD h) (hiD h μ ν) w →
      ∀ σ, -(h : ℤ) - 1 ≤ ((w + Pi.single ρ 1 : Fin 4 → ℤ) σ) ∧ ((w + Pi.single ρ 1 : Fin 4 → ℤ) σ) ≤ 3 * h + 2 := fun w ρ hw σ => by
    have := inD_range hw σ
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  obtain ⟨z, ρ, s⟩ := t
  cases s
  · simp only [Bond.plus, Bool.false_eq_true, ↓reduceIte] at hp hs
    have e : ofs y₀ v = ofs y₀ (v' + Pi.single ρ 1) := by rw [ofs1, ← hp, ← hs, sub_add_cancel]
    have hvv := ofs_inj hn y₀ (ext v hv) (ext1 v' ρ hv') e
    have := (good_pos V (hV v' ρ hv' (hvv ▸ hv)) hδ).2
    rw [← hp, sub_add_cancel] at this
    exact this
  · simp only [Bond.plus, ↓reduceIte] at hp hs
    have e : ofs y₀ v' = ofs y₀ (v + Pi.single ρ 1) := by rw [ofs1, ← hp, ← hs]
    have hvv := ofs_inj hn y₀ (ext v' hv') (ext1 v ρ hv) e
    have := (good_pos V (hV v ρ hv (hvv ▸ hv')) hδ).1
    rw [← hs] at this
    exact this

/-- The ends of the bonds of a staircase path from `y₀ + c` with `|m| ≤ h` are `y₀ + c + v`, `|v| ≤ h`. -/
lemma stair_ends (y₀ y : Site n) (c m : Fin 4 → ℤ) (hy : y = ofs y₀ c) {h : ℕ}
    (hm : AxialReference.InM h m) (l : List (Fin 4)) (hl : l.Nodup) (t : Bond n)
    (ht : t ∈ stair y m l 0) :
    ∃ v v', AxialReference.InM h v ∧ AxialReference.InM h v' ∧ t.site = ofs y₀ (c + v) ∧
      t.plus = ofs y₀ (c + v') := by
  obtain ⟨v, v', hv, hv', hs, hp⟩ := mem_stair y m l 0 hl t ht
  have hb : ∀ w, Partial 0 m l w → AxialReference.InM h w := fun w hw σ => by
    have h1 := hw σ
    have h2 := hm σ
    by_cases hσ : σ ∈ l
    · have := h1.2 hσ
      simp only [Pi.zero_apply, sub_zero, LatticePaths.Btw] at this
      omega
    · rw [h1.1 hσ]; simp only [Pi.zero_apply]; omega
  exact ⟨v, v', hb v hv, hb v' hv', by rw [hs, hy, ofs_ofs], by rw [hp, hy, ofs_ofs]⟩

/-- The ends of the bonds of the straight path of `L` bonds from `y₀ + c` in the direction `κ`. -/
lemma seg_ends (y₀ y : Site n) (c : Fin 4 → ℤ) (hy : y = ofs y₀ c) (κ : Fin 4) (L : ℕ) (t : Bond n)
    (ht : t ∈ segZ κ y (L : ℤ)) :
    ∃ i : ℕ, i < L ∧ t.site = ofs y₀ (c + Pi.single κ (i : ℤ)) ∧
      t.plus = ofs y₀ (c + Pi.single κ ((i + 1 : ℕ) : ℤ)) := by
  rw [segZ_nat] at ht
  obtain ⟨i, hi, hs, hp⟩ := mem_seg_iff ht
  refine ⟨i, hi, ?_, ?_⟩
  · rw [hs, ofs_add_single, hy]; simp [dvec]
  · rw [hp, ofs_add_single, hy]; simp [dvec]

/-- The covariance of the average on one coarse bond (`lem:average`(iii)). -/
lemma avgB_gauge (U : Config N n) (u : Site n → GLN) (hu : ∀ z, u z ∈ G.carrier) (y : Site n)
    (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) :
    avgB G (U.gauge u) y κ L off ord = u y * avgB G U y κ L off ord * (u (ofs y (Pi.single κ (L : ℤ))))⁻¹ := by
  have est : ∀ (w : Site n) x (Γ : P x), (U.gauge u).hol (stair w (off x) (ord x Γ) 0) =
      u w * U.hol (stair w (off x) (ord x Γ) 0) * (u (ofs w (off x)))⁻¹ := fun w x Γ => by
    have hc := chain_endpt_stair w (off x) (ord x Γ) 0
    rw [ofs_zero, zero_add, offs_perm _ (hord x Γ)] at hc
    rw [hol_gauge U u _ w hc.1, hc.2]
  have eseg : ∀ (w : Site n), (U.gauge u).hol (segZ κ w (L : ℤ)) =
      u w * U.hol (segZ κ w (L : ℤ)) * (u (w + (L : ℤ) • unit n κ))⁻¹ := fun w => by
    rw [hol_gauge U u _ w (chain_segZ κ w _), endpt_segZ]
  have e1 : ∀ x, ofs y (off x) + (L : ℤ) • unit n κ = ofs (ofs y (Pi.single κ (L : ℤ))) (off x) := fun x => by
    rw [ofs_ofs, add_comm (Pi.single κ _) (off x), ofs_add_single]
  have e2 : y + (L : ℤ) • unit n κ = ofs y (Pi.single κ (L : ℤ)) := by
    rw [← ofs_zero y, ← ofs_add_single, zero_add, ofs_zero]
  unfold avgB
  simp only [est, eseg, e1, e2]
  exact GaugeGroup.avg_covariant_chart _ _ _ _ _ _ (hu y) _ _

variable (G) in
/-- The plaquette `M(U)(∂p') = M(U)(c₁)M(U)(c₂)M(U)(c₃)⁻¹M(U)(c₄)⁻¹` of the average, for the plaquette
`p'` of the coarse lattice with the first corner `y₀` in the directions `μ, ν`: `c₁ = (y₀, y₁)`,
`c₂ = (y₁, y₂)`, `c₃ = (y₃, y₂)`, `c₄ = (y₀, y₃)`, `y₁ = y₀ + Le_μ`, `y₃ = y₀ + Le_ν`. -/
def plaqAvg (U : Config N n) (y₀ : Site n) (μ ν : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : GLN :=
  avgB G U y₀ μ L off ord * avgB G U (ofs y₀ (Pi.single μ (L : ℤ))) ν L off ord *
    (avgB G U (ofs y₀ (Pi.single ν (L : ℤ))) μ L off ord)⁻¹ * (avgB G U y₀ ν L off ord)⁻¹

/-- The covariance of the plaquette of the average. -/
lemma plaqAvg_gauge (U : Config N n) (u : Site n → GLN) (hu : ∀ z, u z ∈ G.carrier) (y₀ : Site n)
    (μ ν : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) :
    plaqAvg G (U.gauge u) y₀ μ ν L off ord = u y₀ * plaqAvg G U y₀ μ ν L off ord * (u y₀)⁻¹ := by
  have e : ofs y₀ (Pi.single ν (L : ℤ) + Pi.single μ (L : ℤ)) =
      ofs y₀ (Pi.single μ (L : ℤ) + Pi.single ν (L : ℤ)) := by rw [add_comm]
  unfold plaqAvg
  rw [avgB_gauge U u hu _ _ _ _ _ hord, avgB_gauge U u hu _ _ _ _ _ hord,
    avgB_gauge U u hu _ _ _ _ _ hord, avgB_gauge U u hu _ _ _ _ _ hord, ofs_ofs, ofs_ofs, e]
  group

/-- The cancellation of the means `Ā(y_l, ·)` at the four corners. -/
lemma lin_cancel (A : Bond n → Mat) (y₀ : Site n) (μ ν : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) :
    LIN A y₀ μ L off ord + LIN A (ofs y₀ (Pi.single μ (L : ℤ))) ν L off ord -
        LIN A (ofs y₀ (Pi.single ν (L : ℤ))) μ L off ord - LIN A y₀ ν L off ord =
      ∑ x, (Fintype.card ι : ℂ)⁻¹ • (Apath A (segZ μ (ofs y₀ (off x)) L) +
        Apath A (segZ ν (ofs (ofs y₀ (Pi.single μ (L : ℤ))) (off x)) L) -
        Apath A (segZ μ (ofs (ofs y₀ (Pi.single ν (L : ℤ))) (off x)) L) -
        Apath A (segZ ν (ofs y₀ (off x)) L)) := by
  have e : ofs y₀ (Pi.single ν (L : ℤ) + Pi.single μ (L : ℤ)) =
      ofs y₀ (Pi.single μ (L : ℤ) + Pi.single ν (L : ℤ)) := by rw [add_comm]
  unfold LIN
  rw [ofs_ofs y₀ (Pi.single ν _) (Pi.single μ _), ofs_ofs y₀ (Pi.single μ _) (Pi.single ν _), e]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [smul_add, smul_sub]
  abel

/-- The boundary of the `L × L` square from `z₀` is the sum of the boundaries of its plaquettes. -/
lemma stokes_sq (A : Bond n → Mat) (hA : ∀ b, A b.rev = -A b) (μ ν : Fin 4) (z₀ : Site n) (L : ℕ) :
    Apath A (segZ μ z₀ L) + Apath A (segZ ν (z₀ + (L : ℤ) • unit n μ) L) -
        Apath A (segZ μ (z₀ + (L : ℤ) • unit n ν) L) - Apath A (segZ ν z₀ L) =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        Apath A (plaqPath μ ν (z₀ + i • unit n μ + j • unit n ν)) := by
  have hst := stokes (fun ρ w => A ⟨w, ρ, true⟩) μ ν (fun i j => z₀ + i • unit n μ + j • unit n ν)
    (fun i j => by simp only [succ_nsmul]; abel) (fun i j => by simp only [succ_nsmul]; abel) L
  simp only [Apath_plaq A hA]
  rw [hst]
  simp only [segZ_nat, Apath_seg, Finset.sum_sub_distrib, zero_smul, add_zero, natCast_zsmul]
  have e1 : ∀ i : ℕ, z₀ + L • unit n ν + i • unit n μ = z₀ + i • unit n μ + L • unit n ν := fun i => by
    abel
  simp only [e1]
  abel

/-- The offsets of the corners of `p'`: `0`, `Le_μ`, `Le_ν`, `Le_μ + Le_ν`. -/
def IsCorner (L : ℕ) (μ ν : Fin 4) (c : Fin 4 → ℤ) : Prop :=
  (c μ = 0 ∨ c μ = L) ∧ (c ν = 0 ∨ c ν = L) ∧ ∀ σ, σ ≠ μ → σ ≠ ν → c σ = 0

lemma corner_inD {h L : ℕ} (hL : 2 * h + 1 = L) {μ ν : Fin 4} (hμν : μ ≠ ν) {c v : Fin 4 → ℤ}
    (hc : IsCorner L μ ν c) (hv : AxialReference.InM h v) :
    LatticePaths.InBox (loD h) (hiD h μ ν) (c + v) := by
  obtain ⟨h1, h2, h3⟩ := hc
  rw [inD_iff hμν]
  refine ⟨?_, ?_, fun σ hs1 hs2 => ?_⟩
  · have := hv μ; simp only [Pi.add_apply]; rcases h1 with h1 | h1 <;> rw [h1] <;> omega
  · have := hv ν; simp only [Pi.add_apply]; rcases h2 with h2 | h2 <;> rw [h2] <;> omega
  · have := hv σ; simp only [Pi.add_apply, h3 σ hs1 hs2]; omega

lemma corner_seg_inD {h L : ℕ} (hL : 2 * h + 1 = L) {μ ν : Fin 4} (hμν : μ ≠ ν) {c v : Fin 4 → ℤ}
    (hc : IsCorner L μ ν c) {κ : Fin 4} (hκ : κ = μ ∨ κ = ν) (hcκ : c κ = 0)
    (hv : AxialReference.InM h v) {i : ℕ} (hi : i ≤ L) :
    LatticePaths.InBox (loD h) (hiD h μ ν) (c + v + Pi.single κ (i : ℤ)) := by
  obtain ⟨h1, h2, h3⟩ := hc
  rw [inD_iff hμν]
  rcases hκ with rfl | rfl
  · refine ⟨?_, ?_, fun σ hs1 hs2 => ?_⟩
    · have := hv κ; simp only [Pi.add_apply, Pi.single_eq_same, hcκ]; omega
    · have := hv ν
      simp only [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hμν)]
      rcases h2 with h2 | h2 <;> rw [h2] <;> omega
    · have := hv σ; simp only [Pi.add_apply, h3 σ hs1 hs2, Pi.single_eq_of_ne hs1]; omega
  · refine ⟨?_, ?_, fun σ hs1 hs2 => ?_⟩
    · have := hv μ
      simp only [Pi.add_apply, Pi.single_eq_of_ne hμν]
      rcases h1 with h1 | h1 <;> rw [h1] <;> omega
    · have := hv κ; simp only [Pi.add_apply, Pi.single_eq_same, hcκ]; omega
    · have := hv σ; simp only [Pi.add_apply, h3 σ hs1 hs2, Pi.single_eq_of_ne hs2]; omega

lemma corner_shift {L : ℕ} {μ ν : Fin 4} (hμν : μ ≠ ν) {c : Fin 4 → ℤ} (hc : IsCorner L μ ν c)
    {κ : Fin 4} (hκ : κ = μ ∨ κ = ν) (hcκ : c κ = 0) : IsCorner L μ ν (c + Pi.single κ (L : ℤ)) := by
  obtain ⟨h1, h2, h3⟩ := hc
  rcases hκ with rfl | rfl
  · refine ⟨Or.inr (by simp [hcκ]), by simpa [Pi.single_eq_of_ne (Ne.symm hμν)] using h2,
      fun σ hs1 hs2 => by simp [Pi.single_eq_of_ne hs1, h3 σ hs1 hs2]⟩
  · refine ⟨by simpa [Pi.single_eq_of_ne hμν] using h1, Or.inr (by simp [hcκ]),
      fun σ hs1 hs2 => by simp [Pi.single_eq_of_ne hs2, h3 σ hs1 hs2]⟩

/-- `Δ(p')` is the union `B(y₀) ∪ B(y₁) ∪ B(y₂) ∪ B(y₃)` of the blocks of the four corners of `p'`, the
block `B(y)` being the set of the sites `y + v`, `|v_σ| ≤ h`. -/
lemma boxD_eq_blocks {h L : ℕ} (hL : 2 * h + 1 = L) (y₀ : Site n) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    boxR y₀ (loD h) (hiD h μ ν) =
      {z | ∃ c, IsCorner L μ ν c ∧ ∃ v, AxialReference.InM h v ∧ z = ofs (ofs y₀ c) v} := by
  ext z
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [inD_iff hμν] at hm
    obtain ⟨hmμ, hmν, hmσ⟩ := hm
    set cμ : ℤ := if (h : ℤ) < m μ then L else 0
    set cν : ℤ := if (h : ℤ) < m ν then L else 0
    set c : Fin 4 → ℤ := Pi.single μ cμ + Pi.single ν cν with hc
    have hcμ : c μ = cμ := by simp [hc, Pi.single_eq_of_ne hμν]
    have hcν : c ν = cν := by simp [hc, Pi.single_eq_of_ne (Ne.symm hμν)]
    have hcσ : ∀ σ, σ ≠ μ → σ ≠ ν → c σ = 0 := fun σ h1 h2 => by
      simp [hc, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
    refine ⟨c, ⟨?_, ?_, hcσ⟩, m - c, fun σ => ?_, by rw [ofs_ofs, add_sub_cancel]⟩
    · rw [hcμ]; simp only [cμ]; split_ifs <;> simp
    · rw [hcν]; simp only [cν]; split_ifs <;> simp
    · simp only [Pi.sub_apply]
      by_cases h1 : σ = μ
      · subst h1; rw [hcμ]; simp only [cμ]; split_ifs <;> omega
      by_cases h2 : σ = ν
      · subst h2; rw [hcν]; simp only [cν]; split_ifs <;> omega
      · rw [hcσ σ h1 h2]; have := hmσ σ h1 h2; omega
  · rintro ⟨c, hc, v, hv, rfl⟩
    exact ⟨c + v, corner_inD hL hμν hc hv, by rw [ofs_ofs]⟩

/-- The hypotheses of `avgB_lin` for the coarse bond from the corner `y₀ + c` in the direction `κ`. -/
lemma bond_hyps {V : Config N n} {A : Bond n → Mat} {a : ℝ} {h L : ℕ} (hL : 2 * h + 1 = L) {y₀ : Site n}
    {μ ν : Fin 4} (hμν : μ ≠ ν)
    (gd : ∀ (t : Bond n) (v v' : Fin 4 → ℤ), LatticePaths.InBox (loD h) (hiD h μ ν) v →
      LatticePaths.InBox (loD h) (hiD h μ ν) v' → t.site = ofs y₀ v → t.plus = ofs y₀ v' → Good V A a t)
    {c : Fin 4 → ℤ} (hc : IsCorner L μ ν c) {κ : Fin 4} (hκ : κ = μ ∨ κ = ν) (hcκ : c κ = 0)
    (y : Site n) (hy : y = ofs y₀ c) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (hoff : ∀ x, AxialReference.InM h (off x)) (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) :
    (∀ x Γ, ∀ b ∈ stair y (off x) (ord x Γ) 0, Good V A a b) ∧
    (∀ x Γ, ∀ b ∈ stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ) 0, Good V A a b) ∧
    (∀ x, ∀ b ∈ segZ κ (ofs y (off x)) L, Good V A a b) ∧ (∀ b ∈ segZ κ y L, Good V A a b) ∧
    (∀ x Γ Γ', (stair y (off x) (ord x Γ) 0).length + (segZ κ (ofs y (off x)) L).length +
      (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0).length + (segZ κ y L).length ≤
        6 * L) := by
  have hnd : ∀ x Γ, (ord x Γ).Nodup := fun x Γ => (hord x Γ).nodup_iff.2 (by decide)
  have hy' : ofs y (Pi.single κ (L : ℤ)) = ofs y₀ (c + Pi.single κ (L : ℤ)) := by rw [hy, ofs_ofs]
  have hc' := corner_shift hμν hc hκ hcκ
  have hstair : ∀ (c' : Fin 4 → ℤ) (y' : Site n), IsCorner L μ ν c' → y' = ofs y₀ c' →
      ∀ x Γ, ∀ b ∈ stair y' (off x) (ord x Γ) 0, Good V A a b := fun c' y' hc'' hy'' x Γ b hb => by
    obtain ⟨v, v', hv, hv', hs, hp⟩ := stair_ends y₀ y' c' (off x) hy'' (hoff x) _ (hnd x Γ) b hb
    exact gd b _ _ (corner_inD hL hμν hc'' hv) (corner_inD hL hμν hc'' hv') hs hp
  have hseg : ∀ (v : Fin 4 → ℤ), AxialReference.InM h v → ∀ b ∈ segZ κ (ofs y₀ (c + v)) L,
      Good V A a b := fun v hv b hb => by
    obtain ⟨i, hi, hs, hp⟩ := seg_ends y₀ _ (c + v) rfl κ L b hb
    exact gd b _ _ (corner_seg_inD hL hμν hc hκ hcκ hv hi.le)
      (corner_seg_inD hL hμν hc hκ hcκ hv (by omega)) hs hp
  have hlen : ∀ x Γ (w : Site n), (stair w (off x) (ord x Γ) 0).length ≤ 4 * h := fun x Γ w => by
    rw [length_stair, ((hord x Γ).map _).sum_eq]
    have := hoff x
    have h0 := this 0; have h1 := this 1; have h2 := this 2; have h3 := this 3
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  refine ⟨hstair c y hc hy, hstair _ _ hc' hy', fun x b hb => ?_, fun b hb => ?_,
    fun x Γ Γ' => ?_⟩
  · rw [hy, ofs_ofs] at hb; exact hseg (off x) (hoff x) b hb
  · rw [hy, ← add_zero c] at hb
    exact hseg 0 (fun σ => by simp) b hb
  · have := hlen x Γ y
    have := hlen x Γ' (ofs y (Pi.single κ (L : ℤ)))
    simp only [length_segZ, Int.natAbs_natCast]
    omega

/-- The plaquettes of the square `p'_x` lie in the box. -/
lemma sq_inD {h L : ℕ} (hL : 2 * h + 1 = L) {μ ν : Fin 4} (hμν : μ ≠ ν) {v : Fin 4 → ℤ}
    (hv : AxialReference.InM h v) {i j : ℕ} (hi : i < L) (hj : j < L) {a b : ℤ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    LatticePaths.InBox (loD h) (hiD h μ ν)
      (v + Pi.single μ (i : ℤ) + Pi.single ν (j : ℤ) + Pi.single μ a + Pi.single ν b) := by
  rw [inD_iff hμν]
  refine ⟨?_, ?_, fun σ hs1 hs2 => ?_⟩
  · have := hv μ
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hμν]
    omega
  · have := hv ν
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hμν)]
    omega
  · have := hv σ
    simp only [Pi.add_apply, Pi.single_eq_of_ne hs1, Pi.single_eq_of_ne hs2]
    omega

lemma ofs_sq (y₀ : Site n) (v : Fin 4 → ℤ) (μ ν : Fin 4) (i j : ℕ) :
    ofs y₀ (v + Pi.single μ (i : ℤ) + Pi.single ν (j : ℤ)) = ofs y₀ v + i • unit n μ + j • unit n ν := by
  rw [ofs_add_single, ofs_add_single, natCast_zsmul, natCast_zsmul]

/-- The bonds of a plaquette with corners in the box are good. -/
lemma plaq_good {V : Config N n} {A : Bond n → Mat} {a : ℝ} {h : ℕ} {y₀ : Site n} {μ ν : Fin 4}
    (gd : ∀ (t : Bond n) (v v' : Fin 4 → ℤ), LatticePaths.InBox (loD h) (hiD h μ ν) v →
      LatticePaths.InBox (loD h) (hiD h μ ν) v' → t.site = ofs y₀ v → t.plus = ofs y₀ v' → Good V A a t)
    (w : Fin 4 → ℤ)
    (hw : ∀ a b : ℤ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      LatticePaths.InBox (loD h) (hiD h μ ν) (w + Pi.single μ a + Pi.single ν b)) :
    ∀ t ∈ plaqPath μ ν (ofs y₀ w), Good V A a t := by
  have s00 : ofs y₀ (w + Pi.single μ 0 + Pi.single ν 0) = ofs y₀ w := by simp
  have s10 : ofs y₀ (w + Pi.single μ 1 + Pi.single ν 0) = ofs y₀ w + unit n μ := by simp [ofs1]
  have s01 : ofs y₀ (w + Pi.single μ 0 + Pi.single ν 1) = ofs y₀ w + unit n ν := by simp [ofs1]
  have s11 : ofs y₀ (w + Pi.single μ 1 + Pi.single ν 1) = ofs y₀ w + unit n μ + unit n ν := by
    rw [ofs1, ofs1]
  have h00 := hw 0 0 le_rfl zero_le_one le_rfl zero_le_one
  have h10 := hw 1 0 zero_le_one le_rfl le_rfl zero_le_one
  have h01 := hw 0 1 le_rfl zero_le_one zero_le_one le_rfl
  have h11 := hw 1 1 zero_le_one le_rfl zero_le_one le_rfl
  intro t ht
  simp only [plaqPath, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact gd _ _ _ h00 h10 s00.symm (by simp only [Bond.plus, ↓reduceIte]; rw [s10])
  · exact gd _ _ _ h10 h11 s10.symm (by simp only [Bond.plus, ↓reduceIte]; rw [s11])
  · exact gd _ _ _ h11 h01 s11.symm
      (by simp only [Bond.plus, Bool.false_eq_true, ↓reduceIte]; rw [s01]; abel)
  · exact gd _ _ _ h01 h00 s01.symm
      (by simp only [Bond.plus, Bool.false_eq_true, ↓reduceIte]; rw [s00]; abel)

lemma hs_sub_le' (X Y : Mat) : hs (X - Y) ≤ hs X + hs Y := by
  have e : X - Y = X + (-1 : ℂ) • Y := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e]
  refine (hs_add_le _ _).trans ?_
  rw [hs_smul, norm_neg, norm_one, one_mul]

/-- `L⁻⁴ Σ_{x ∈ B(y₀)} Σ_{p ⊂ p'_x} |U(∂p) - id|`: the mean over the points `x = y₀ + off(x)` of the sum
over the `L²` plaquettes `p_{μν}(x + ie_μ + je_ν)`, `0 ≤ i, j < L`, of the square `p'_x`. -/
def meanP (U : Config N n) (y₀ : Site n) (μ ν : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ x, ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    hs (((plaq U μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν) : GLN) : Mat) - 1)

set_option maxHeartbeats 2000000 in
/-- **`prop:regular-averages`(i)** on the fine torus `T^{(j-1)} = Site n`, `L = 2h + 1`: for the plaquette
`p'` of the coarse lattice with the first corner `y₀` in the directions `μ ≠ ν`, if the plaquettes of `U`
with corners in the box `Δ(p')`, the union of the blocks of the four corners of `p'`
(`boxD_eq_blocks`), satisfy `|U(∂p) - id| ≤ α` with `αL² ≤ c`, then
`|M(U)(∂p') - id| ≤ L⁻⁴Σ_xΣ_{p ⊂ p'_x}|U(∂p) - id| + C₀L⁴α²`, `C₀ = 2²⁷N`, and the mean is at most `L²α`.
The constant is `c = min(r, 1/2)/(2¹⁴√N)`, `r` the radius of `lem:chart`(ii); the core's `c_* =
r_G/(2¹⁴√N)` with `r_G ≤ 1/2`. The families of paths are any families of staircase paths through the
four coordinates in some order, to the points `y₀ + off(x)`, `|off(x)| ≤ h`, of the block; `L⁻⁴` is
`|ι|⁻¹`. The torus has at least `4h + 4` sites in each direction, so that `Δ(p')` with its bonds embeds. -/
theorem regular_averages_i (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U →
      ∀ (h : ℕ), 4 * h + 4 ≤ n → ∀ (y₀ : Site n) (μ ν : Fin 4), μ ≠ ν →
      ∀ {ι : Type} [Fintype ι] {P : ι → Type} [∀ x, Fintype (P x)] (off : ι → Fin 4 → ℤ)
        (ord : ∀ x, P x → List (Fin 4)), 0 < Fintype.card ι → (∀ x, 0 < Fintype.card (P x)) →
      (∀ x, AxialReference.InM h (off x)) → (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) →
      ∀ α : ℝ, 0 ≤ α → α * ((2 * h + 1 : ℕ) : ℝ) ^ 2 ≤ c →
      (∀ μ' ν' z, PlaqIn (boxR y₀ (loD h) (hiD h μ ν)) μ' ν' z →
        hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α) →
      hs (((plaqAvg G U y₀ μ ν (2 * h + 1) off ord : GLN) : Mat) - 1) ≤
          meanP U y₀ μ ν (2 * h + 1) off + 2 ^ 27 * N * ((2 * h + 1 : ℕ) : ℝ) ^ 4 * α ^ 2 ∧
        meanP U y₀ μ ν (2 * h + 1) off ≤ ((2 * h + 1 : ℕ) : ℝ) ^ 2 * α := by
  obtain ⟨r, hr0, hr1, hch⟩ := GaugeGroup.chart_ii (G := G) hG
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hN0 : 0 < N := hN
  refine ⟨min r (1 / 2) / (2 ^ 14 * Real.sqrt N), by positivity, ?_⟩
  intro n _ U hU h hn y₀ μ ν hμν ι _ P _ off ord hι hP hoff hord α hα hαc hplq
  generalize hL : 2 * h + 1 = L at hαc ⊢
  have hLr : (L : ℝ) = 2 * h + 1 := by rw [← hL]; push_cast; ring
  have hL1 : (1 : ℝ) ≤ L := by rw [hLr]; have : (0 : ℝ) ≤ h := Nat.cast_nonneg h; linarith
  -- the smallness: `q = √N α L² ≤ min(r, 1/2)/2¹⁴`
  set q : ℝ := Real.sqrt N * α * (L : ℝ) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hqc : q ≤ min r (1 / 2) / 2 ^ 14 := by
    have := mul_le_mul_of_nonneg_left hαc hsN.le
    rw [hq, mul_assoc]
    calc Real.sqrt N * (α * (L : ℝ) ^ 2)
        ≤ Real.sqrt N * (min r (1 / 2) / (2 ^ 14 * Real.sqrt N)) := this
      _ = min r (1 / 2) / 2 ^ 14 := by field_simp
  have hqr : q ≤ r / 2 ^ 14 := hqc.trans (by have := min_le_left r (1 / 2); linarith)
  have hqh : q ≤ 1 / 2 ^ 15 := hqc.trans (by have := min_le_right r (1 / 2); linarith)
  have hq2 : q ^ 2 = N * α ^ 2 * (L : ℝ) ^ 4 := by
    rw [hq, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  -- the gauge `V = U^u` and the bound on its bonds
  set β : ℝ := Real.sqrt N * α with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hPB : PlaqBound U (boxR y₀ (loD h) (hiD h μ ν)) β := fun μ' ν' z _ hz =>
    (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left (hplq μ' ν' z hz) (Real.sqrt_nonneg _))
  set u := uG U y₀ h with hu_def
  have hu : ∀ z, u z ∈ G.carrier := fun z => hU.hol_mem _
  set V := U.gauge u with hV_def
  have hVG : IsGField G V := fun ρ z =>
    G.carrier.mul_mem (G.carrier.mul_mem (hu z) (hU ρ z)) (G.carrier.inv_mem (hu _))
  set δ : ℝ := ((8 * h + 2 : ℕ) : ℝ) * β with hδ
  have h8 : ((8 * h + 2 : ℕ) : ℝ) ≤ 4 * L := by rw [hLr]; push_cast; linarith
  have hδL : δ ≤ 4 * L * β := mul_le_mul_of_nonneg_right h8 hβ0
  have hLL : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hLβ : (L : ℝ) * β ≤ q := by
    rw [hq, hβ]; nlinarith [mul_le_mul_of_nonneg_right hLL hβ0]
  have hδq : δ ≤ 4 * q := by
    calc δ ≤ 4 * L * β := hδL
      _ = 4 * (L * β) := by ring
      _ ≤ 4 * q := by linarith
  have hδ12 : δ ≤ 1 / 2 := by linarith
  have hVb : ∀ m ρ, LatticePaths.InBox (loD h) (hiD h μ ν) m →
      LatticePaths.InBox (loD h) (hiD h μ ν) (m + Pi.single ρ 1) →
      ‖((V ρ (ofs y₀ m) : GLN) : Mat) - 1‖ ≤ δ := fun m ρ hm hm' =>
    gauge_bound U hU.gauge hn y₀ μ ν hβ0 hPB m ρ hm hm'
  set a : ℝ := 2 * δ with ha
  have gd : ∀ (t : Bond n) (v v' : Fin 4 → ℤ), LatticePaths.InBox (loD h) (hiD h μ ν) v →
      LatticePaths.InBox (loD h) (hiD h μ ν) v' → t.site = ofs y₀ v → t.plus = ofs y₀ v' →
      Good V (Aof V) a t := fun t v v' hv hv' hs hp => good_of_ends V hn y₀ μ ν hδ12 hVb t hv hv' hs hp
  have ha0 : 0 ≤ a := by positivity
  set s : ℝ := ((6 * L : ℕ) : ℝ) * a with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hsq : s ≤ 48 * q := by
    have e : s = 12 * L * δ := by rw [hsdef, ha]; push_cast; ring
    rw [e]
    calc 12 * (L : ℝ) * δ ≤ 12 * L * (4 * L * β) := mul_le_mul_of_nonneg_left hδL (by positivity)
      _ = 48 * q := by rw [hq, hβ]; ring
  have haL : a * L ≤ 8 * q := by
    have : a * L ≤ 2 * (4 * L * β) * L := by
      rw [ha]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc a * L ≤ 2 * (4 * L * β) * L := this
      _ = 8 * q := by rw [hq, hβ]; ring
  have ha8 : a ≤ 8 * q := le_trans (le_mul_of_one_le_right ha0 hL1) haL
  have hs512 : s ≤ 1 / 512 := by linarith
  have hsr : 2 * s ≤ r := by linarith
  -- the four coarse bonds of `∂p'`
  have hc0 : IsCorner L μ ν 0 := ⟨Or.inl rfl, Or.inl rfl, fun _ _ _ => rfl⟩
  have hcμ : IsCorner L μ ν (Pi.single μ (L : ℤ)) := by
    simpa using corner_shift hμν hc0 (Or.inl rfl) rfl
  have hcν : IsCorner L μ ν (Pi.single ν (L : ℤ)) := by
    simpa using corner_shift hμν hc0 (Or.inr rfl) rfl
  obtain ⟨b1g, b1g', b1h, b1k, b1l⟩ :=
    bond_hyps hL hμν gd hc0 (Or.inl rfl) rfl y₀ (ofs_zero y₀).symm off ord hoff hord
  obtain ⟨b2g, b2g', b2h, b2k, b2l⟩ := bond_hyps hL hμν gd hcμ (Or.inr rfl)
    (Pi.single_eq_of_ne (Ne.symm hμν) _) (ofs y₀ (Pi.single μ (L : ℤ))) rfl off ord hoff hord
  obtain ⟨b3g, b3g', b3h, b3k, b3l⟩ := bond_hyps hL hμν gd hcν (Or.inl rfl)
    (Pi.single_eq_of_ne hμν _) (ofs y₀ (Pi.single ν (L : ℤ))) rfl off ord hoff hord
  obtain ⟨b4g, b4g', b4h, b4k, b4l⟩ :=
    bond_hyps hL hμν gd hc0 (Or.inr rfl) rfl y₀ (ofs_zero y₀).symm off ord hoff hord
  obtain ⟨Z1, hZ1, hZ1L, hZ1n⟩ := avgB_lin hch V hVG (Aof V) (Aof_rev V) a (6 * L) y₀ μ L off ord
    hι hP b1g b1g' b1h b1k b1l ha0 hs512 hsr
  obtain ⟨Z2, hZ2, hZ2L, hZ2n⟩ := avgB_lin hch V hVG (Aof V) (Aof_rev V) a (6 * L)
    (ofs y₀ (Pi.single μ (L : ℤ))) ν L off ord hι hP b2g b2g' b2h b2k b2l ha0 hs512 hsr
  obtain ⟨Z3, hZ3, hZ3L, hZ3n⟩ := avgB_lin hch V hVG (Aof V) (Aof_rev V) a (6 * L)
    (ofs y₀ (Pi.single ν (L : ℤ))) μ L off ord hι hP b3g b3g' b3h b3k b3l ha0 hs512 hsr
  obtain ⟨Z4, hZ4, hZ4L, hZ4n⟩ := avgB_lin hch V hVG (Aof V) (Aof_rev V) a (6 * L) y₀ ν L off ord
    hι hP b4g b4g' b4h b4k b4l ha0 hs512 hsr
  -- the plaquette of the average: multiplying out the four exponentials
  have hW : ((plaqAvg G V y₀ μ ν L off ord : GLN) : Mat) =
      ([Complex.I • Z1, Complex.I • Z2, -(Complex.I • Z3), -(Complex.I • Z4)].map exp).prod := by
    simp only [plaqAvg, hZ1, hZ2, hZ3, hZ4, expU_inv, Units.val_mul, expU_val, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hnorms : (([Complex.I • Z1, Complex.I • Z2, -(Complex.I • Z3), -(Complex.I • Z4)]).map norm).sum ≤
      20 * s := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, norm_neg, norm_smul,
      Complex.norm_I, one_mul, add_zero]
    linarith
  obtain ⟨hE, -⟩ := prod_exp_small _ hnorms (by linarith)
  set SZ : Mat := Z1 + Z2 - Z3 - Z4 with hSZ
  have hsum : ([Complex.I • Z1, Complex.I • Z2, -(Complex.I • Z3), -(Complex.I • Z4)]).sum =
      Complex.I • SZ := by
    simp only [List.sum_cons, List.sum_nil, add_zero, hSZ, smul_sub, smul_add]; abel
  rw [hsum, ← hW] at hE
  -- the first-order part
  set Θ : Mat := LIN (Aof V) y₀ μ L off ord + LIN (Aof V) (ofs y₀ (Pi.single μ (L : ℤ))) ν L off ord -
    LIN (Aof V) (ofs y₀ (Pi.single ν (L : ℤ))) μ L off ord - LIN (Aof V) y₀ ν L off ord with hΘ
  have hSZΘ : ‖SZ - Θ‖ ≤ 4 * (1042 * s ^ 2) := by
    have e : SZ - Θ = (Z1 - LIN (Aof V) y₀ μ L off ord) +
        (Z2 - LIN (Aof V) (ofs y₀ (Pi.single μ (L : ℤ))) ν L off ord) -
        (Z3 - LIN (Aof V) (ofs y₀ (Pi.single ν (L : ℤ))) μ L off ord) -
        (Z4 - LIN (Aof V) y₀ ν L off ord) := by rw [hSZ, hΘ]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le ((Z1 - LIN (Aof V) y₀ μ L off ord) +
      (Z2 - LIN (Aof V) (ofs y₀ (Pi.single μ (L : ℤ))) ν L off ord))
      (Z3 - LIN (Aof V) (ofs y₀ (Pi.single ν (L : ℤ))) μ L off ord)
    have := norm_add_le (Z1 - LIN (Aof V) y₀ μ L off ord)
      (Z2 - LIN (Aof V) (ofs y₀ (Pi.single μ (L : ℤ))) ν L off ord)
    linarith
  have hΘ2 : Θ = ∑ x, (Fintype.card ι : ℂ)⁻¹ • ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      Apath (Aof V) (plaqPath μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν)) := by
    rw [hΘ, lin_cancel]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    have e1 : ofs (ofs y₀ (Pi.single μ (L : ℤ))) (off x) = ofs y₀ (off x) + (L : ℤ) • unit n μ := by
      rw [ofs_ofs, add_comm (Pi.single μ _) (off x), ofs_add_single]
    have e2 : ofs (ofs y₀ (Pi.single ν (L : ℤ))) (off x) = ofs y₀ (off x) + (L : ℤ) • unit n ν := by
      rw [ofs_ofs, add_comm (Pi.single ν _) (off x), ofs_add_single]
    rw [e1, e2]
    exact stokes_sq (Aof V) (Aof_rev V) μ ν (ofs y₀ (off x)) L
  -- the plaquettes of the fine lattice
  have hplaqA : ∀ x, ∀ i < L, ∀ j < L,
      hs (Apath (Aof V) (plaqPath μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν))) ≤
        hs (((plaq U μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν) : GLN) : Mat) - 1) +
          (4 * a) ^ 2 := by
    intro x i hi j hj
    set z := ofs y₀ (off x) + i • unit n μ + j • unit n ν with hz
    have hzw : z = ofs y₀ (off x + Pi.single μ (i : ℤ) + Pi.single ν (j : ℤ)) :=
      (ofs_sq y₀ (off x) μ ν i j).symm
    have hgood : ∀ t ∈ plaqPath μ ν z, Good V (Aof V) a t := by
      rw [hzw]
      exact plaq_good gd _ fun a' b' h1 h2 h3 h4 => sq_inD hL hμν (hoff x) hi hj h1 h2 h3 h4
    have hlen : ((plaqPath μ ν z).length : ℝ) = 4 := by simp [plaqPath]
    have hl := hol_lin V (Aof V) (plaqPath μ ν z) (fun t ht => (hgood t ht).1)
      (fun t ht => (hgood t ht).2) (by rw [hlen]; linarith)
    rw [hlen] at hl
    have hl1 : ‖((plaq V μ ν z : GLN) : Mat) - 1 - Complex.I • Apath (Aof V) (plaqPath μ ν z)‖ ≤
        (4 * a) ^ 2 := hl.1
    have hconj : ((plaq V μ ν z : GLN) : Mat) - 1 = Ad (u z) (((plaq U μ ν z : GLN) : Mat) - 1) := by
      rw [hV_def, plaq_gauge]; simp [Ad, Matrix.mul_sub, Matrix.sub_mul]
    have hsV : hs (((plaq V μ ν z : GLN) : Mat) - 1) = hs (((plaq U μ ν z : GLN) : Mat) - 1) := by
      rw [hconj, GaugeGroup.hs_Ad (hu z)]
    have hIA : hs (Apath (Aof V) (plaqPath μ ν z)) = hs (Complex.I • Apath (Aof V) (plaqPath μ ν z)) := by
      rw [hs_smul, Complex.norm_I, one_mul]
    have e : Complex.I • Apath (Aof V) (plaqPath μ ν z) = (((plaq V μ ν z : GLN) : Mat) - 1) -
        (((plaq V μ ν z : GLN) : Mat) - 1 - Complex.I • Apath (Aof V) (plaqPath μ ν z)) := by abel
    rw [hIA, e]
    refine (hs_sub_le' _ _).trans ?_
    rw [hsV]
    have := hs_le_opNorm hN0
      (((plaq V μ ν z : GLN) : Mat) - 1 - Complex.I • Apath (Aof V) (plaqPath μ ν z))
    linarith
  have hcn : ‖(Fintype.card ι : ℂ)⁻¹‖ = (Fintype.card ι : ℝ)⁻¹ := by simp
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hι.ne'
  have hΘb : hs Θ ≤ meanP U y₀ μ ν L off + (L : ℝ) ^ 2 * (4 * a) ^ 2 := by
    rw [hΘ2]
    calc hs (∑ x, (Fintype.card ι : ℂ)⁻¹ • ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          Apath (Aof V) (plaqPath μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν)))
        ≤ ∑ x, hs ((Fintype.card ι : ℂ)⁻¹ • ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          Apath (Aof V) (plaqPath μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν))) :=
          hs_sum_le _ _
      _ = ∑ x, (Fintype.card ι : ℝ)⁻¹ * hs (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          Apath (Aof V) (plaqPath μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν))) := by
          simp only [hs_smul, hcn]
      _ ≤ ∑ x, (Fintype.card ι : ℝ)⁻¹ * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          (hs (((plaq U μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν) : GLN) : Mat) - 1) +
            (4 * a) ^ 2) := by
          refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (hs_sum_le _ _).trans (Finset.sum_le_sum fun i hi => (hs_sum_le _ _).trans
            (Finset.sum_le_sum fun j hj => hplaqA x i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj)))
      _ = meanP U y₀ μ ν L off + (L : ℝ) ^ 2 * (4 * a) ^ 2 := by
          simp only [meanP, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_add, Finset.card_univ, ← Finset.mul_sum]
          field_simp
  -- `M(U)(∂p') = M(V)(∂p')`, since `u(y₀) = id`
  have hu0 : u y₀ = 1 := by
    have hr0' : AxialReference.rep y₀ h y₀ = 0 := by
      have := AxialReference.rep_ofs y₀ h (v := 0) (fun σ => by simp only [Pi.zero_apply]; omega)
      rwa [ofs_zero] at this
    rw [hu_def, uG, hr0']
    simp [stair, segZ_zero, Config.hol]
  have hUV : plaqAvg G U y₀ μ ν L off ord = plaqAvg G V y₀ μ ν L off ord := by
    rw [hV_def, plaqAvg_gauge U u hu y₀ μ ν L off ord hord, hu0, one_mul, inv_one, mul_one]
  refine ⟨?_, ?_⟩
  · rw [hUV]
    have e1 : ((plaqAvg G V y₀ μ ν L off ord : GLN) : Mat) - 1 = Complex.I • SZ +
        (((plaqAvg G V y₀ μ ν L off ord : GLN) : Mat) - 1 - Complex.I • SZ) := by abel
    have b1 : hs (((plaqAvg G V y₀ μ ν L off ord : GLN) : Mat) - 1) ≤ hs SZ + (20 * s) ^ 2 := by
      rw [e1]
      refine (hs_add_le _ _).trans ?_
      rw [hs_smul, Complex.norm_I, one_mul]
      have := hs_le_opNorm hN0 (((plaqAvg G V y₀ μ ν L off ord : GLN) : Mat) - 1 - Complex.I • SZ)
      linarith
    have b2 : hs SZ ≤ hs Θ + 4 * (1042 * s ^ 2) := by
      have e : SZ = Θ + (SZ - Θ) := by abel
      rw [e]
      refine (hs_add_le _ _).trans ?_
      have := hs_le_opNorm hN0 (Θ + (SZ - Θ) - Θ)
      rw [add_sub_cancel_left] at this
      linarith
    have hs2 : s ^ 2 ≤ 2304 * q ^ 2 := by
      calc s ^ 2 ≤ (48 * q) ^ 2 := pow_le_pow_left₀ hs0 hsq 2
        _ = 2304 * q ^ 2 := by ring
    have haL2 : (L : ℝ) ^ 2 * (4 * a) ^ 2 ≤ 1024 * q ^ 2 := by
      calc (L : ℝ) ^ 2 * (4 * a) ^ 2 = 16 * (a * L) ^ 2 := by ring
        _ ≤ 16 * (8 * q) ^ 2 := by gcongr
        _ = 1024 * q ^ 2 := by ring
    have hfin : (20 * s) ^ 2 + 4 * (1042 * s ^ 2) + (L : ℝ) ^ 2 * (4 * a) ^ 2 ≤
        2 ^ 27 * N * (L : ℝ) ^ 4 * α ^ 2 := by
      rw [show (2 : ℝ) ^ 27 * N * (L : ℝ) ^ 4 * α ^ 2 = 2 ^ 27 * q ^ 2 by rw [hq2]; ring,
        show (20 * s) ^ 2 = 400 * s ^ 2 by ring]
      have := sq_nonneg q
      linarith
    linarith
  · have hPI : ∀ x, ∀ i < L, ∀ j < L,
        PlaqIn (boxR y₀ (loD h) (hiD h μ ν)) μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν) := by
      intro x i hi j hj
      rw [← ofs_sq y₀ (off x) μ ν i j]
      set w := off x + Pi.single μ (i : ℤ) + Pi.single ν (j : ℤ) with hw
      have hwD : ∀ a b : ℤ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
          LatticePaths.InBox (loD h) (hiD h μ ν) (w + Pi.single μ a + Pi.single ν b) :=
        fun a b h1 h2 h3 h4 => sq_inD hL hμν (hoff x) hi hj h1 h2 h3 h4
      refine ⟨⟨_, hwD 0 0 le_rfl zero_le_one le_rfl zero_le_one, by simp⟩,
        ⟨_, hwD 1 0 zero_le_one le_rfl le_rfl zero_le_one, by simp [ofs1]⟩,
        ⟨_, hwD 0 1 le_rfl zero_le_one zero_le_one le_rfl, by simp [ofs1]⟩,
        ⟨_, hwD 1 1 zero_le_one le_rfl zero_le_one le_rfl, by rw [ofs1, ofs1]⟩⟩
    unfold meanP
    calc (Fintype.card ι : ℝ)⁻¹ * ∑ x, ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          hs (((plaq U μ ν (ofs y₀ (off x) + i • unit n μ + j • unit n ν) : GLN) : Mat) - 1)
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _x : ι, ∑ _i ∈ Finset.range L, ∑ _j ∈ Finset.range L, α := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => Finset.sum_le_sum
            fun i hi => Finset.sum_le_sum fun j hj => hplq μ ν _ ?_) (by positivity)
          exact hPI x i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj)
      _ = (L : ℝ) ^ 2 * α := by
          simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, nsmul_eq_mul]
          field_simp

end RegularAverages

end CoreLean

end
