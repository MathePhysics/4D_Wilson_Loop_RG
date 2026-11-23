/-
`lem:transports` of BALABAN_CORE.tex: transports of a regular configuration.

Model. Fine lattice `Site n` in the units `η = 1` (so `a_j = Lʲ`), with a sequence of domains
`S : Blocks.DomSeq n`. A path is a list of bonds `b₁, …, b_m` with `b₁` beginning at `s` and each bond
beginning where the previous one ends (`IsPath`); its `ℓ¹`-length is `m`. The configuration is
`𝐔 = e^{iA'}U` (`expMul 1 A' U`) with a gauge field `U` and a `1`-form `A'`; of `eq:regular-complex` the
proof uses the first bound `‖A'(b)‖ ≤ α₁a_j⁻¹` for the bonds `b` of `Ω_j` (both ends in `Ω_j`).

The proof is the core's, once for both norms (`NormLike`): on each bond `Ad_{𝐔(b)}` changes the norm by
at most the factor `1 + 6‖A'(b)‖` (`eq:adjoint-lipschitz`), a path from `Ω_j` of length at most `a_j`
stays in `Ω_{j-1}` (`eq:separation`, `RM ≥ L`), and `(1 + 6Lα₁/a_j)^{a_j} ≤ e^{6Lα₁} ≤ 2`; the lower bound is
the upper bound for the reversed path; `eq:transport-comparison` is the telescoping sum, from the right.
-/
import CoreLean.SupportContinuation

open scoped Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace CoreLean

namespace Transports

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The properties of the operator norm and of the Hilbert–Schmidt norm used here. -/
structure NormLike (nm : Mat → ℝ) : Prop where
  nonneg : ∀ X, 0 ≤ nm X
  zero : nm 0 = 0
  add_le : ∀ X Y, nm (X + Y) ≤ nm X + nm Y
  ad_unitary : ∀ W : GLN, (W : Mat) ∈ unitaryGroup (Fin N) ℂ → ∀ X, nm (Ad W X) = nm X
  ad_exp : ∀ X : Mat, ‖X‖ ≤ 1 / 32 → ∀ Z, nm (Ad (expU (Complex.I • X)) Z - Z) ≤ 6 * ‖X‖ * nm Z

lemma normLike_opNorm : NormLike (fun X : Mat => ‖X‖) where
  nonneg X := norm_nonneg X
  zero := norm_zero
  add_le X Y := norm_add_le X Y
  ad_unitary W hW X := SupportCont.opNorm_Ad_unitary hW X
  ad_exp X hX Z := norm_Ad_exp_sub_le hX Z

lemma normLike_hs : NormLike (fun X : Mat => hs X) where
  nonneg X := hs_nonneg X
  zero := SupportCont.hs_zero
  add_le X Y := hs_add_le X Y
  ad_unitary W hW X := hs_unitary_mul _ _ _ hW (SupportCont.unitary_inv hW)
  ad_exp X hX Z := hs_Ad_exp_sub_le hX Z

lemma NormLike.sub_le {nm : Mat → ℝ} (h : NormLike nm) (X Y : Mat) : nm X ≤ nm Y + nm (X - Y) := by
  have := h.add_le Y (X - Y); rwa [add_sub_cancel] at this

/-! ### One bond -/

/-- The value of `A'` on the positive bond underlying `b`. -/
def bondA (A' : Form1 N n) (b : Bond n) : Mat :=
  if b.pos then A' b.dir b.site else A' b.dir (b.site - unit n b.dir)

lemma expMul_one (A' : Form1 N n) (U : Config N n) (μ : Fin 4) (x : Site n) :
    expMul 1 A' U μ x = expU (Complex.I • A' μ x) * U μ x := by
  simp [expMul]

lemma val_unitary (U : Config N n) (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (b : Bond n) : ((U.val b : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := by
  obtain ⟨x, μ, s⟩ := b
  cases s
  · simp only [Config.val, Bool.false_eq_true, ↓reduceIte]
    exact SupportCont.unitary_inv (hU _ _)
  · simp only [Config.val, ↓reduceIte]; exact hU _ _

/-- On one bond: `Ad_{𝐔(b)}` changes `nm` by at most `1 + 6‖A'(b)‖`, and differs from `Ad_{U(b)}` by at
most `6‖A'(b)‖`. -/
lemma bond_bounds {nm : Mat → ℝ} (h : NormLike nm) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) (b : Bond n)
    (hb : ‖bondA A' b‖ ≤ 1 / 32) (Y : Mat) :
    nm (Ad ((expMul 1 A' U).val b) Y) ≤ (1 + 6 * ‖bondA A' b‖) * nm Y ∧
      nm (Ad ((expMul 1 A' U).val b) Y - Ad (U.val b) Y) ≤ 6 * ‖bondA A' b‖ * nm Y := by
  obtain ⟨x, μ, s⟩ := b
  cases s
  · -- the reversed bond: `𝐔(b) = U⁻¹ e^{-iA}`
    simp only [bondA, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    have hval : (expMul 1 A' U).val ⟨x, μ, false⟩ =
        (U μ (x - unit n μ))⁻¹ * expU (Complex.I • -A' μ (x - unit n μ)) := by
      simp only [Config.val, Bool.false_eq_true, ↓reduceIte, expMul_one]
      rw [_root_.mul_inv_rev, expU_inv, smul_neg]
    have hval' : U.val ⟨x, μ, false⟩ = (U μ (x - unit n μ))⁻¹ := by simp [Config.val]
    have hWi := SupportCont.unitary_inv (hU μ (x - unit n μ))
    have hA : ‖-A' μ (x - unit n μ)‖ ≤ 1 / 32 := by rwa [norm_neg]
    have he := h.ad_exp _ hA Y
    rw [norm_neg] at he
    rw [hval, hval', Ad_mul, h.ad_unitary _ hWi, ← Ad_sub, h.ad_unitary _ hWi]
    refine ⟨(h.sub_le _ Y).trans ?_, he⟩
    linarith
  · -- the positive bond: `𝐔(b) = e^{iA} U`
    simp only [bondA, ↓reduceIte] at hb ⊢
    have hval : (expMul 1 A' U).val ⟨x, μ, true⟩ = expU (Complex.I • A' μ x) * U μ x := by
      simp [Config.val, expMul_one]
    have hval' : U.val ⟨x, μ, true⟩ = U μ x := by simp [Config.val]
    rw [hval, hval', Ad_mul]
    have he := h.ad_exp (A' μ x) hb (Ad (U μ x) Y)
    rw [h.ad_unitary _ (hU μ x)] at he
    refine ⟨(h.sub_le _ (Ad (U μ x) Y)).trans ?_, he⟩
    rw [h.ad_unitary _ (hU μ x)]
    linarith

/-! ### Products along a list of bonds -/

lemma hol_cons (V : Config N n) (b : Bond n) (γ : List (Bond n)) :
    V.hol (b :: γ) = V.val b * V.hol γ := by simp [Config.hol]

lemma hol_append_single (V : Config N n) (γ : List (Bond n)) (b : Bond n) :
    V.hol (γ ++ [b]) = V.hol γ * V.val b := by simp [Config.hol, List.prod_append]

/-- If each bond changes `nm` by at most `1 + t`, the list of `m` bonds changes it by at most
`(1 + t)^m`. -/
lemma hol_bound {nm : Mat → ℝ} (h : NormLike nm) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) {t : ℝ} (γ : List (Bond n))
    (hγ : ∀ b ∈ γ, ‖bondA A' b‖ ≤ 1 / 32 ∧ 6 * ‖bondA A' b‖ ≤ t) (Y : Mat) :
    nm (Ad ((expMul 1 A' U).hol γ) Y) ≤ (1 + t) ^ γ.length * nm Y := by
  induction γ generalizing Y with
  | nil => simp [Config.hol]
  | cons b γ ih =>
    have hb := hγ b List.mem_cons_self
    rw [hol_cons, Ad_mul, List.length_cons, pow_succ']
    have h1 := (bond_bounds h A' U hU b hb.1 (Ad ((expMul 1 A' U).hol γ) Y)).1
    have h2 := ih (fun b' hb' => hγ b' (List.mem_cons_of_mem _ hb')) Y
    calc nm (Ad ((expMul 1 A' U).val b) (Ad ((expMul 1 A' U).hol γ) Y))
        ≤ (1 + 6 * ‖bondA A' b‖) * nm (Ad ((expMul 1 A' U).hol γ) Y) := h1
      _ ≤ (1 + t) * ((1 + t) ^ γ.length * nm Y) :=
          mul_le_mul (by linarith [hb.2]) h2 (h.nonneg _) (by linarith [norm_nonneg (bondA A' b)])
      _ = (1 + t) * (1 + t) ^ γ.length * nm Y := by ring

/-- The telescoping bound: `nm(Ad_{𝐔(γ)}Y - Ad_{U(γ)}Y) ≤ 2t·m·nm(Y)` if every initial segment changes
`nm` by at most `2` and each bond has `6‖A'(b)‖ ≤ t`. -/
lemma hol_compare {nm : Mat → ℝ} (h : NormLike nm) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) {t : ℝ} (γ : List (Bond n))
    (hγ : ∀ b ∈ γ, ‖bondA A' b‖ ≤ 1 / 32 ∧ 6 * ‖bondA A' b‖ ≤ t)
    (hinit : ∀ γ', γ' <+: γ → ∀ Y, nm (Ad ((expMul 1 A' U).hol γ') Y) ≤ 2 * nm Y) (Y : Mat) :
    nm (Ad ((expMul 1 A' U).hol γ) Y - Ad (U.hol γ) Y) ≤ 2 * t * γ.length * nm Y := by
  induction γ using List.reverseRecOn generalizing Y with
  | nil => simp [Config.hol, h.zero]
  | append_singleton γ b ih =>
    have hb := hγ b (List.mem_append_right _ List.mem_cons_self)
    rw [hol_append_single, hol_append_single, Ad_mul, Ad_mul, List.length_append, List.length_singleton]
    set P := (expMul 1 A' U).hol γ
    have e : Ad P (Ad ((expMul 1 A' U).val b) Y) - Ad (U.hol γ) (Ad (U.val b) Y) =
        Ad P (Ad ((expMul 1 A' U).val b) Y - Ad (U.val b) Y) +
          (Ad P (Ad (U.val b) Y) - Ad (U.hol γ) (Ad (U.val b) Y)) := by
      rw [Ad_sub]; abel
    rw [e]
    have h1 : nm (Ad P (Ad ((expMul 1 A' U).val b) Y - Ad (U.val b) Y)) ≤ 2 * (t * nm Y) := by
      refine (hinit γ (List.prefix_append _ _) _).trans ?_
      have := (bond_bounds h A' U hU b hb.1 Y).2
      have : 6 * ‖bondA A' b‖ * nm Y ≤ t * nm Y := mul_le_mul_of_nonneg_right hb.2 (h.nonneg _)
      linarith
    have h2 := ih (fun b' hb' => hγ b' (List.mem_append_left _ hb'))
      (fun γ' hγ' => hinit γ' (hγ'.trans (List.prefix_append _ _))) (Ad (U.val b) Y)
    rw [h.ad_unitary _ (val_unitary U hU b)] at h2
    refine (h.add_le _ _).trans ?_
    push_cast
    nlinarith [h.nonneg Y]

/-! ### Paths -/

/-- `γ` is a path from `s`: each bond begins where the previous one ends. -/
def IsPath : Site n → List (Bond n) → Prop
  | _, [] => True
  | s, b :: γ => b.site = s ∧ IsPath b.plus γ

lemma d1_triangle (x y z : Site n) : Blocks.d1 x z ≤ Blocks.d1 x y + Blocks.d1 y z := by
  unfold Blocks.d1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun κ _ => Blocks.cd_sub_le _ _ _

lemma d1_self (x : Site n) : Blocks.d1 x x = 0 := by
  simp [Blocks.d1, Blocks.cd_zero]

lemma d1_plus (b : Bond n) : Blocks.d1 b.site b.plus ≤ 1 := by
  unfold Blocks.d1
  have hcoord : ∀ κ, Blocks.cd (b.site κ - b.plus κ) ≤ if κ = b.dir then 1 else 0 := by
    intro κ
    unfold Bond.plus
    split_ifs with hs hκ hκ
    · subst hκ
      simp only [Pi.add_apply, unit, Pi.single_eq_same, sub_add_cancel_left]
      have := Blocks.cd_intCast_le (N := n) (-1)
      simpa using this
    · simp [unit, Pi.single_apply, hκ, Blocks.cd_zero]
    · subst hκ
      simp only [Pi.sub_apply, unit, Pi.single_eq_same, sub_sub_cancel]
      have := Blocks.cd_intCast_le (N := n) 1
      simpa using this
    · simp [unit, Pi.single_apply, hκ, Blocks.cd_zero]
  calc ∑ κ, Blocks.cd (b.site κ - b.plus κ) ≤ ∑ κ : Fin 4, (if κ = b.dir then 1 else 0) :=
        Finset.sum_le_sum fun κ _ => hcoord κ
    _ = 1 := by simp

/-- The ends of the bonds of a path from `s` lie within the `ℓ¹`-distance `m` of `s`. -/
lemma path_ends {s : Site n} {γ : List (Bond n)} (hγ : IsPath s γ) :
    ∀ b ∈ γ, Blocks.d1 s b.site ≤ γ.length ∧ Blocks.d1 s b.plus ≤ γ.length := by
  induction γ generalizing s with
  | nil => simp
  | cons b γ ih =>
    obtain ⟨hb, hγ'⟩ := hγ
    subst hb
    have h1 := d1_plus b
    intro b' hb'
    rcases List.mem_cons.mp hb' with rfl | hb'
    · rw [d1_self, List.length_cons]; omega
    · obtain ⟨i1, i2⟩ := ih hγ' b' hb'
      have t1 := d1_triangle b.site b.plus b'.site
      have t2 := d1_triangle b.site b.plus b'.plus
      rw [List.length_cons]
      omega

lemma hol_rev (V : Config N n) (γ : List (Bond n)) :
    V.hol (γ.map Bond.rev).reverse = (V.hol γ)⁻¹ := by
  unfold Config.hol
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left fun b _ => ?_
  simp [Config.val_rev]

/-! ### The bounds over a sequence of domains -/

/-- `(1 + t)^m ≤ 2` for `t ≥ 0` and `tm ≤ 3/16`. -/
lemma one_add_pow_le_two {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (htm : t * m ≤ 3 / 16) : (1 + t) ^ m ≤ 2 := by
  have h1 : (1 + t) ^ m ≤ Real.exp (t * m) := by
    calc (1 + t) ^ m ≤ Real.exp t ^ m := by
          gcongr
          linarith [Real.add_one_le_exp t]
      _ = Real.exp (t * m) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : Real.exp (t * m) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (1 / 2) < 2 := by
    have e : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have := Real.exp_one_lt_d9
    have hp := Real.exp_pos (1 / 2)
    nlinarith
  linarith

variable (S : Blocks.DomSeq n)

/-- The ends of the bonds of `γ` lie in `Ω_i`. -/
def BondsIn (i : ℕ) (γ : List (Bond n)) : Prop := ∀ b ∈ γ, b.site ∈ S.Ω i ∧ b.plus ∈ S.Ω i

/-- The hypothesis `eq:regular-complex` (first bound) on `A'`. -/
def RegA (A' : Form1 N n) (α₁ : ℝ) : Prop :=
  ∀ i ≤ S.k, ∀ μ x, x ∈ S.Ω i → x + unit n μ ∈ S.Ω i → ‖A' μ x‖ ≤ α₁ / (S.L : ℝ) ^ i

lemma L_pos' : (0 : ℝ) < S.L := by have := S.three_le_L; positivity

/-- On a bond of `Ω_{j-1}`, `‖A'(b)‖ ≤ Lα₁a_j⁻¹`. -/
lemma bondA_le {A' : Form1 N n} {α₁ : ℝ} (hreg : RegA S A' α₁) (hα0 : 0 ≤ α₁) {j : ℕ}
    (hj : j ≤ S.k) {b : Bond n} (hb : b.site ∈ S.Ω (j - 1) ∧ b.plus ∈ S.Ω (j - 1)) :
    ‖bondA A' b‖ ≤ S.L * α₁ / (S.L : ℝ) ^ j := by
  have hL := L_pos' S
  have hle : ‖bondA A' b‖ ≤ α₁ / (S.L : ℝ) ^ (j - 1) := by
    obtain ⟨x, μ, s⟩ := b
    cases s
    · simp only [bondA, Bool.false_eq_true, ↓reduceIte]
      refine hreg (j - 1) (by omega) μ _ ?_ ?_
      · simpa [Bond.plus] using hb.2
      · simpa using hb.1
    · simp only [bondA, ↓reduceIte]
      exact hreg (j - 1) (by omega) μ x hb.1 (by simpa [Bond.plus] using hb.2)
  refine hle.trans ?_
  rw [div_le_div_iff₀ (pow_pos hL _) (pow_pos hL _)]
  have : (S.L : ℝ) ^ j ≤ (S.L : ℝ) ^ (j - 1) * S.L := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L))
      (by omega)
  nlinarith [mul_le_mul_of_nonneg_left this hα0]

/-- Points within `RM a_{j-1}` of a point of `Ω_j` lie in `Ω_{j-1}`. -/
lemma mem_prev {j : ℕ} {z e : Site n} (hz : z ∈ S.Ω j)
    (hd : (Blocks.dinf e z : ℝ) ≤ S.RM * (S.L : ℝ) ^ (j - 1)) : e ∈ S.Ω (j - 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [S.Ω_zero]
  · by_contra he
    have := S.sep' (j - 1) e he z (by rwa [Nat.sub_add_cancel hj])
    linarith

/-- A list of at most `a_j` bonds of `Ω_{j-1}` changes the norm by at most `2`. -/
lemma two_bound {nm : Mat → ℝ} (h : NormLike nm) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) {α₁ : ℝ}
    (hα : 32 * S.L * α₁ ≤ 1) (hreg : RegA S A' α₁) (hα0 : 0 ≤ α₁) {j : ℕ} (hj : j ≤ S.k)
    {γ : List (Bond n)} (hγ : BondsIn S (j - 1) γ) (hlen : γ.length ≤ S.L ^ j) (Y : Mat) :
    nm (Ad ((expMul 1 A' U).hol γ) Y) ≤ 2 * nm Y := by
  have hL := L_pos' S
  have hp : (0 : ℝ) < (S.L : ℝ) ^ j := pow_pos hL _
  set t := 6 * (S.L * α₁ / (S.L : ℝ) ^ j)
  have hbond : ∀ b ∈ γ, ‖bondA A' b‖ ≤ 1 / 32 ∧ 6 * ‖bondA A' b‖ ≤ t := by
    intro b hb
    have h1 := bondA_le S hreg hα0 hj (hγ b hb)
    refine ⟨h1.trans ?_, by linarith⟩
    rw [div_le_iff₀ hp]
    have : (1 : ℝ) ≤ (S.L : ℝ) ^ j := one_le_pow₀ (by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L))
    nlinarith
  refine (hol_bound h A' U hU γ hbond Y).trans (mul_le_mul_of_nonneg_right ?_ (h.nonneg _))
  refine one_add_pow_le_two (by positivity) ?_
  have hm : (γ.length : ℝ) ≤ (S.L : ℝ) ^ j := by exact_mod_cast hlen
  calc t * γ.length = 6 * S.L * α₁ * ((γ.length : ℝ) / (S.L : ℝ) ^ j) := by ring
    _ ≤ 6 * S.L * α₁ * 1 := by
        gcongr
        rw [div_le_one hp]; exact hm
    _ ≤ 3 / 16 := by linarith

lemma alpha_nonneg {A' : Form1 N n} {α₁ : ℝ} (hreg : RegA S A' α₁) : 0 ≤ α₁ := by
  have := hreg 0 (Nat.zero_le _) 0 0 (by simp [S.Ω_zero]) (by simp [S.Ω_zero])
  simpa using (norm_nonneg _).trans this

/-- `lem:transports`, first statement: for `RM ≥ L`, `32Lα₁ ≤ 1`, and a path of an `ℓ¹`-length of at
most `a_j` which begins at a point of `Ω_j`, `½ nm(Z) ≤ nm(Ad_{𝐔(γ)} Z) ≤ 2 nm(Z)`, for the operator norm
and the Hilbert–Schmidt norm. -/
theorem transports {nm : Mat → ℝ} (h : NormLike nm) (hRM : (S.L : ℝ) ≤ S.RM) (A' : Form1 N n)
    (U : Config N n) (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) {α₁ : ℝ}
    (hα : 32 * S.L * α₁ ≤ 1) (hreg : RegA S A' α₁) {j : ℕ} (hj : j ≤ S.k) {s : Site n}
    (hs : s ∈ S.Ω j) {γ : List (Bond n)} (hγ : IsPath s γ) (hlen : γ.length ≤ S.L ^ j) (Z : Mat) :
    nm (Ad ((expMul 1 A' U).hol γ) Z) ≤ 2 * nm Z ∧ nm Z ≤ 2 * nm (Ad ((expMul 1 A' U).hol γ) Z) := by
  have hα0 := alpha_nonneg S hreg
  have hL := L_pos' S
  -- the path stays in `Ω_{j-1}`
  have hRMj : (S.L : ℝ) ^ j ≤ S.RM * (S.L : ℝ) ^ (j - 1) := by
    have : (S.L : ℝ) ^ j ≤ S.L * (S.L : ℝ) ^ (j - 1) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L))
        (by omega)
    nlinarith [pow_pos hL (j - 1)]
  have hin : BondsIn S (j - 1) γ := by
    intro b hb
    obtain ⟨h1, h2⟩ := path_ends hγ b hb
    have e1 : (Blocks.dinf b.site s : ℝ) ≤ (S.L : ℝ) ^ j := by
      rw [Blocks.dinf_comm]
      exact_mod_cast (Blocks.dinf_le_d1 _ _).trans (h1.trans hlen)
    have e2 : (Blocks.dinf b.plus s : ℝ) ≤ (S.L : ℝ) ^ j := by
      rw [Blocks.dinf_comm]
      exact_mod_cast (Blocks.dinf_le_d1 _ _).trans (h2.trans hlen)
    exact ⟨mem_prev S hs (e1.trans hRMj), mem_prev S hs (e2.trans hRMj)⟩
  refine ⟨two_bound S h A' U hU hα hreg hα0 hj hin hlen Z, ?_⟩
  -- the reversed path
  have hin' : BondsIn S (j - 1) (γ.map Bond.rev).reverse := by
    intro b hb
    rw [List.mem_reverse, List.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    rw [Bond.rev_site, Bond.rev_plus]
    exact ⟨(hin b' hb').2, (hin b' hb').1⟩
  have hlen' : (γ.map Bond.rev).reverse.length ≤ S.L ^ j := by simpa using hlen
  have := two_bound S h A' U hU hα hreg hα0 hj hin' hlen' (Ad ((expMul 1 A' U).hol γ) Z)
  rwa [hol_rev, Ad_inv_Ad] at this

/-- `lem:transports`, second statement: for `RM ≥ 3L` and a path of an `ℓ¹`-length of at most `a_j`
which has a point at an `ℓ^∞`-distance of at most `a_j` from `Ω_j`, the bounds hold, and
`nm(Ad_{𝐔(γ)}Z - Ad_{U(γ)}Z) ≤ 12Lα₁ (ℓ₁(γ)/a_j) nm(Z)` (`eq:transport-comparison`). -/
theorem transports_near {nm : Mat → ℝ} (h : NormLike nm) (hRM : 3 * (S.L : ℝ) ≤ S.RM)
    (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) {α₁ : ℝ}
    (hα : 32 * S.L * α₁ ≤ 1) (hreg : RegA S A' α₁) {j : ℕ} (hj : j ≤ S.k) {s : Site n}
    {γ : List (Bond n)} (hγ : IsPath s γ) (hlen : γ.length ≤ S.L ^ j) {p z : Site n}
    (hp : p = s ∨ ∃ b ∈ γ, p = b.site ∨ p = b.plus) (hz : z ∈ S.Ω j)
    (hpz : Blocks.dinf p z ≤ S.L ^ j) (Z : Mat) :
    (nm (Ad ((expMul 1 A' U).hol γ) Z) ≤ 2 * nm Z ∧
      nm Z ≤ 2 * nm (Ad ((expMul 1 A' U).hol γ) Z)) ∧
    nm (Ad ((expMul 1 A' U).hol γ) Z - Ad (U.hol γ) Z) ≤
      12 * S.L * α₁ * (γ.length / (S.L : ℝ) ^ j) * nm Z := by
  have hα0 := alpha_nonneg S hreg
  have hL := L_pos' S
  have hps : Blocks.d1 s p ≤ γ.length := by
    rcases hp with rfl | ⟨b, hb, rfl | rfl⟩
    · rw [d1_self]; exact Nat.zero_le _
    · exact (path_ends hγ b hb).1
    · exact (path_ends hγ b hb).2
  have hRMj : 3 * (S.L : ℝ) ^ j ≤ S.RM * (S.L : ℝ) ^ (j - 1) := by
    have : (S.L : ℝ) ^ j ≤ S.L * (S.L : ℝ) ^ (j - 1) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L))
        (by omega)
    nlinarith [pow_pos hL (j - 1)]
  -- every end lies within `3a_j` of `z`, hence in `Ω_{j-1}`
  have hfar : ∀ e, Blocks.d1 s e ≤ γ.length → (Blocks.dinf e z : ℝ) ≤ 3 * (S.L : ℝ) ^ j := by
    intro e he
    have t1 := Blocks.dinf_triangle e s z
    have t2 := Blocks.dinf_triangle s p z
    have d1 := Blocks.dinf_le_d1 s e
    have d2 := Blocks.dinf_le_d1 s p
    rw [Blocks.dinf_comm e s] at t1
    have : Blocks.dinf e z ≤ 3 * S.L ^ j := by omega
    exact_mod_cast this
  have hin : BondsIn S (j - 1) γ := fun b hb =>
    ⟨mem_prev S hz ((hfar _ (path_ends hγ b hb).1).trans hRMj),
      mem_prev S hz ((hfar _ (path_ends hγ b hb).2).trans hRMj)⟩
  have hbounds : nm (Ad ((expMul 1 A' U).hol γ) Z) ≤ 2 * nm Z ∧
      nm Z ≤ 2 * nm (Ad ((expMul 1 A' U).hol γ) Z) := by
    refine ⟨two_bound S h A' U hU hα hreg hα0 hj hin hlen Z, ?_⟩
    have hin' : BondsIn S (j - 1) (γ.map Bond.rev).reverse := by
      intro b hb
      rw [List.mem_reverse, List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      rw [Bond.rev_site, Bond.rev_plus]
      exact ⟨(hin b' hb').2, (hin b' hb').1⟩
    have hlen' : (γ.map Bond.rev).reverse.length ≤ S.L ^ j := by simpa using hlen
    have := two_bound S h A' U hU hα hreg hα0 hj hin' hlen' (Ad ((expMul 1 A' U).hol γ) Z)
    rwa [hol_rev, Ad_inv_Ad] at this
  refine ⟨hbounds, ?_⟩
  -- the telescoping sum
  have hp' : (0 : ℝ) < (S.L : ℝ) ^ j := pow_pos hL _
  set t := 6 * (S.L * α₁ / (S.L : ℝ) ^ j)
  have hbond : ∀ b ∈ γ, ‖bondA A' b‖ ≤ 1 / 32 ∧ 6 * ‖bondA A' b‖ ≤ t := by
    intro b hb
    have h1 := bondA_le S hreg hα0 hj (hin b hb)
    refine ⟨h1.trans ?_, by linarith⟩
    rw [div_le_iff₀ hp']
    have : (1 : ℝ) ≤ (S.L : ℝ) ^ j :=
      one_le_pow₀ (by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L))
    nlinarith
  have hinit : ∀ γ', γ' <+: γ → ∀ Y, nm (Ad ((expMul 1 A' U).hol γ') Y) ≤ 2 * nm Y :=
    fun γ' hγ' Y => two_bound S h A' U hU hα hreg hα0 hj (fun b hb => hin b (hγ'.subset hb))
      (hγ'.length_le.trans hlen) Y
  refine (hol_compare h A' U hU γ hbond hinit Z).trans (le_of_eq ?_)
  simp only [t]
  ring

end Transports

end CoreLean
