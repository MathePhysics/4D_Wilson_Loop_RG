/-
`lem:divergence-conversion` of BALABAN_CORE.tex: the two measures of a second entry in divergence form.

Model (with `Transports.lean`, `ShortestPaths.lean`). Fine lattice, `η = 1`, a sequence of domains
`S`. The norms enter through the inequalities they stand for: `eq:divergence-size` (`DivSize`) is the
set of the bounds `a_j²|K| ≤ γ` on `Ω_j`, `a_j²‖K‖^{(j)}_β ≤ γ` (the Hölder norm at the scale `j`, over all
pairs of sites at an `ℓ¹`-distance of at most `a_j` and the shortest paths between them, with the
transports of `U`), the same for `ψ`, and `a_j³|p| ≤ γ` on `Ω_j`; `eq:divergence-size-local` for the
weight `1` is the bound `a_{j(y)}²(‖f‖_{∞,Δ̃(y)} + [f]_{β;y}) ≤ c` at every point `y` (`LocalHolder`, with
the seminorm over the pairs of sites of `Δ̃(y)`), and `‖p̃‖_{∞,(-3)} ≤ c`. The configuration is
`𝐔 = e^{iA'}U` with a gauge field `U` and `eq:regular-complex` (first bound) for `A'`.
-/
import CoreLean.ShortestPaths

open scoped Matrix.Norms.L2Operator
open Matrix Finset

noncomputable section

namespace CoreLean

namespace Transports

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable (S : Blocks.DomSeq n)

/-- The Hölder bound at the scale `j` (`eq:holder`) of a family `f`, with the transports of `V`. -/
def HolderAt (V : Config N n) (j : ℕ) {ι : Type*} (f : ι → Site n → Mat) (c β : ℝ) : Prop :=
  ∀ x x' γ', IsShortest x x' γ' → 0 < Blocks.d1 x x' → Blocks.d1 x x' ≤ S.L ^ j →
    ∀ i, ‖Ad (V.hol γ') (f i x') - f i x‖ ≤ c * ((Blocks.d1 x x' : ℝ) / (S.L : ℝ) ^ j) ^ β

/-- `𝐉` is of the size `γ` in divergence form with respect to `U` (`eq:divergence-size`), with the
forms `K`, `ψ`, `p`. -/
structure DivSize (U : Config N n) (K : Fin 4 → Fin 4 → Site n → Mat) (ψ : Site n → Mat)
    (p : Fin 4 → Site n → Mat) (β γ : ℝ) : Prop where
  K_sup : ∀ j ≤ S.k, ∀ x ∈ S.Ω j, ∀ q : Fin 4 × Fin 4, ‖K q.1 q.2 x‖ ≤ γ / (S.L : ℝ) ^ (2 * j)
  K_hol : ∀ j ≤ S.k, HolderAt S U j (fun q : Fin 4 × Fin 4 => K q.1 q.2) (γ / (S.L : ℝ) ^ (2 * j)) β
  ψ_sup : ∀ j ≤ S.k, ∀ x ∈ S.Ω j, ∀ _q : Unit, ‖ψ x‖ ≤ γ / (S.L : ℝ) ^ (2 * j)
  ψ_hol : ∀ j ≤ S.k, HolderAt S U j (fun _ : Unit => ψ) (γ / (S.L : ℝ) ^ (2 * j)) β
  p_sup : ∀ j ≤ S.k, ∀ x ∈ S.Ω j, ∀ μ, ‖p μ x‖ ≤ γ / (S.L : ℝ) ^ (3 * j)

/-- `a_{j(y)}²(‖f‖_{∞,Δ̃(y)} + [f]_{β;y}) ≤ c`, the seminorm with the transports of `V`. -/
def LocalHolder (V : Config N n) (y : Site n) {ι : Type*} (f : ι → Site n → Mat) (β c : ℝ) : Prop :=
  ∃ M₁ M₂ : ℝ, (S.L : ℝ) ^ (2 * S.sc y) * (M₁ + M₂) ≤ c ∧
    (∀ x, Blocks.dinf x y < S.L ^ S.sc y → ∀ i, ‖f i x‖ ≤ M₁) ∧
    (∀ x x' γ', Blocks.dinf x y < S.L ^ S.sc y → Blocks.dinf x' y < S.L ^ S.sc y →
      IsShortest x x' γ' → 0 < Blocks.d1 x x' → Blocks.d1 x x' ≤ S.L ^ S.sc y →
      ∀ i, ‖Ad (V.hol γ') (f i x') - f i x‖ ≤ M₂ * ((Blocks.d1 x x' : ℝ) / (S.L : ℝ) ^ S.sc y) ^ β)

lemma hol_unitary (U : Config N n) (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (γ : List (Bond n)) : ((U.hol γ : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := by
  induction γ with
  | nil => simp [Config.hol]
  | cons b γ ih =>
    rw [hol_cons]
    exact SupportCont.unitary_mul (val_unitary U hU b) ih

lemma six_le_n {j : ℕ} (hj : j ≤ S.k) : 6 * S.L ^ j ≤ n := by
  have h1 : S.L ^ j ≤ S.L ^ S.k := Nat.pow_le_pow_right (by have := S.three_le_L; omega) hj
  have h2 : S.L ^ (S.k + 1) ≤ S.L ^ (S.mT + S.k) :=
    Nat.pow_le_pow_right (by have := S.three_le_L; omega) (by have := S.one_le_mT; omega)
  rw [pow_succ] at h2
  have h3 : S.L ^ S.k * 3 ≤ S.L ^ S.k * S.L := Nat.mul_le_mul_left _ S.three_le_L
  calc 6 * S.L ^ j ≤ 2 * S.L ^ (S.mT + S.k) := by omega
    _ = n := S.N_eq.symm

/-- `a_{j-1}⁻² ≤ L²a_j⁻²`. -/
lemma inv_sq_prev (j : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    γ / (S.L : ℝ) ^ (2 * (j - 1)) ≤ S.L ^ 2 * γ / (S.L : ℝ) ^ (2 * j) := by
  have hL := L_pos' S
  have hL1 : (1 : ℝ) ≤ S.L := by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L)
  rw [div_le_div_iff₀ (pow_pos hL _) (pow_pos hL _)]
  have : (S.L : ℝ) ^ (2 * j) ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (2 * (j - 1)) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
  nlinarith [mul_le_mul_of_nonneg_left this hγ, pow_pos hL (2 * (j - 1))]

/-- The local Hölder bound of a family with the bounds of `eq:divergence-size`, for the transports of
`𝐔 = e^{iA'}U`: `M₁ = L²γa⁻²`, `M₂ = (2L³ + 12L³α₁)γa⁻²`. -/
theorem local_holder (hRM : (S.L : ℝ) ≤ S.RM) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) {α₁ : ℝ}
    (hα : 32 * S.L * α₁ ≤ 1) (hreg : RegA S A' α₁) {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hγ : 0 ≤ γ) {ι : Type*} (f : ι → Site n → Mat)
    (hsup : ∀ j ≤ S.k, ∀ x ∈ S.Ω j, ∀ i, ‖f i x‖ ≤ γ / (S.L : ℝ) ^ (2 * j))
    (hhol : ∀ j ≤ S.k, HolderAt S U j f (γ / (S.L : ℝ) ^ (2 * j)) β) (y : Site n) :
    LocalHolder S (expMul 1 A' U) y f β (4 * S.L ^ 3 * γ) := by
  have hα0 := alpha_nonneg S hreg
  have hL := L_pos' S
  have hL1 : (1 : ℝ) ≤ S.L := by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L)
  unfold LocalHolder
  have hy : y ∈ S.Ω (S.sc y) := S.mem_sc y
  have hj : S.sc y ≤ S.k := S.sc_le y
  generalize S.sc y = j at hy hj ⊢
  set a : ℝ := (S.L : ℝ) ^ j with ha_def
  have ha : 0 < a := pow_pos hL _
  have ea2 : (S.L : ℝ) ^ (2 * j) = a ^ 2 := by rw [ha_def, ← pow_mul, mul_comm]
  have hprev : γ / (S.L : ℝ) ^ (2 * (j - 1)) ≤ S.L ^ 2 * γ / a ^ 2 := by
    rw [← ea2]; exact inv_sq_prev S j hγ
  -- the cube `Δ̃(y)` lies in `Ω_{j-1}`
  have hRMj : (S.L : ℝ) ^ j ≤ S.RM * (S.L : ℝ) ^ (j - 1) := by
    have : (S.L : ℝ) ^ j ≤ S.L * (S.L : ℝ) ^ (j - 1) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ hL1 (by omega)
    nlinarith [pow_pos hL (j - 1)]
  have hcube : ∀ x, Blocks.dinf x y < S.L ^ j → x ∈ S.Ω (j - 1) := by
    intro x hx
    refine mem_prev S hy ?_
    have : (Blocks.dinf x y : ℝ) ≤ (S.L : ℝ) ^ j := by exact_mod_cast hx.le
    linarith
  have hM1 : ∀ x, Blocks.dinf x y < S.L ^ j → ∀ i, ‖f i x‖ ≤ S.L ^ 2 * γ / a ^ 2 := by
    intro x hx i
    exact (hsup (j - 1) (by omega) x (hcube x hx) i).trans hprev
  refine ⟨S.L ^ 2 * γ / a ^ 2, (2 * S.L ^ 3 + 12 * S.L ^ 3 * α₁) * γ / a ^ 2, ?_, hM1, ?_⟩
  · -- `L² + 2L³ + 12L³α₁ ≤ 4L³`
    rw [ea2]
    have e : a ^ 2 * (S.L ^ 2 * γ / a ^ 2 + (2 * S.L ^ 3 + 12 * S.L ^ 3 * α₁) * γ / a ^ 2) =
        S.L ^ 2 * γ + (2 * S.L ^ 3 + 12 * S.L ^ 3 * α₁) * γ := by
      field_simp
    rw [e]
    have h1 : (S.L : ℝ) ^ 2 ≤ S.L ^ 3 := by nlinarith [sq_nonneg (S.L : ℝ)]
    have h2 : 12 * (S.L : ℝ) ^ 3 * α₁ ≤ S.L ^ 3 := by nlinarith [pow_pos hL 2]
    nlinarith [mul_le_mul_of_nonneg_right h1 hγ, mul_le_mul_of_nonneg_right h2 hγ]
  · intro x x' γ' hx hx' hγ' hz0 hza i
    set z := Blocks.d1 x x'
    have hzr : (0 : ℝ) < z := by exact_mod_cast hz0
    have hza' : (z : ℝ) ≤ a := by rw [ha_def]; exact_mod_cast hza
    have hq0 : 0 ≤ (z : ℝ) / a := by positivity
    have hq1 : (z : ℝ) / a ≤ 1 := by rw [div_le_one ha]; exact hza'
    -- the path runs in `Δ̃(y)`, hence in `Ω_{j-1}`
    have hinc : ∀ b ∈ γ', b.site ∈ S.Ω (j - 1) ∧ b.plus ∈ S.Ω (j - 1) := by
      intro b hb
      have hpos : 0 < S.L ^ j := pow_pos (by have := S.three_le_L; omega) _
      have h6 := six_le_n S hj
      have hd1 : Blocks.d1 x x' ≤ S.L ^ j := hza
      obtain ⟨h1, h2⟩ := shortest_in_cube hγ' (y := y) (r := S.L ^ j - 1) (by omega) (by omega)
        (by omega) b hb
      exact ⟨hcube _ (by omega), hcube _ (by omega)⟩
    have hlen : γ'.length ≤ S.L ^ j := by rw [hγ'.2.2]; exact hza
    -- the two transports
    have hfx := hM1 x hx i
    have hfx' := hM1 x' hx' i
    set t := 6 * (S.L * α₁ / a)
    have hbond : ∀ b ∈ γ', ‖bondA A' b‖ ≤ 1 / 32 ∧ 6 * ‖bondA A' b‖ ≤ t := by
      intro b hb
      have h1 := bondA_le S hreg hα0 hj (hinc b hb)
      refine ⟨h1.trans ?_, by linarith⟩
      rw [div_le_iff₀ ha]
      have : (1 : ℝ) ≤ a := one_le_pow₀ hL1
      nlinarith
    have hinit : ∀ γ'', γ'' <+: γ' → ∀ Y, ‖Ad ((expMul 1 A' U).hol γ'') Y‖ ≤ 2 * ‖Y‖ :=
      fun γ'' hγ'' Y => two_bound S normLike_opNorm A' U hU hα hreg hα0 hj
        (fun b hb => hinc b (hγ''.subset hb)) (hγ''.length_le.trans hlen) Y
    have hT2 := hol_compare normLike_opNorm A' U hU γ' hbond hinit (f i x')
    rw [hγ'.2.2] at hT2
    -- the transport of `U`: the Hölder bound at the scale `j - 1`, or twice the supremum
    have hT1 : ‖Ad (U.hol γ') (f i x') - f i x‖ ≤ 2 * S.L ^ 3 * γ / a ^ 2 * ((z : ℝ) / a) ^ β := by
      have hqβ : (1 / (S.L : ℝ)) ≤ ((z : ℝ) / a) ^ β ∨ z ≤ S.L ^ (j - 1) := by
        by_cases hzj : z ≤ S.L ^ (j - 1)
        · exact Or.inr hzj
        · left
          push_neg at hzj
          have hz' : (S.L : ℝ) ^ (j - 1) ≤ z := by exact_mod_cast hzj.le
          have hj1 : 1 ≤ j := by
            by_contra h
            have h0 : j = 0 := by omega
            subst h0
            simp at hzj hza
            omega
          have e : a = S.L * (S.L : ℝ) ^ (j - 1) := by
            simp only [a]; rw [← pow_succ']; congr 1; omega
          have h1 : 1 / (S.L : ℝ) ≤ (z : ℝ) / a := by
            rw [e, div_le_div_iff₀ hL (by positivity)]; nlinarith
          calc 1 / (S.L : ℝ) ≤ (1 / (S.L : ℝ)) ^ β :=
                Real.self_le_rpow_of_le_one (by positivity)
                  (by rw [div_le_one hL]; exact hL1) hβ1
            _ ≤ ((z : ℝ) / a) ^ β := Real.rpow_le_rpow (by positivity) h1 hβ0.le
      rcases hqβ with hq | hzj
      · have hU' := hol_unitary U hU γ'
        calc ‖Ad (U.hol γ') (f i x') - f i x‖ ≤ ‖Ad (U.hol γ') (f i x')‖ + ‖f i x‖ := norm_sub_le _ _
          _ = ‖f i x'‖ + ‖f i x‖ := by rw [normLike_opNorm.ad_unitary _ hU']
          _ ≤ 2 * (S.L ^ 2 * γ / a ^ 2) := by linarith
          _ = 2 * S.L ^ 3 * γ / a ^ 2 * (1 / S.L) := by field_simp
          _ ≤ 2 * S.L ^ 3 * γ / a ^ 2 * ((z : ℝ) / a) ^ β :=
              mul_le_mul_of_nonneg_left hq (by positivity)
      · -- the Hölder bound at the scale `j - 1`
        have hh := hhol (j - 1) (by omega) x x' γ' hγ' hz0 hzj i
        have ea : (S.L : ℝ) ^ (j - 1) * S.L ≥ a := by
          simp only [a]; rw [← pow_succ]; exact pow_le_pow_right₀ hL1 (by omega)
        have hratio : ((z : ℝ) / (S.L : ℝ) ^ (j - 1)) ^ β ≤ S.L * ((z : ℝ) / a) ^ β := by
          have h1 : (z : ℝ) / (S.L : ℝ) ^ (j - 1) ≤ S.L * ((z : ℝ) / a) := by
            rw [div_le_iff₀ (pow_pos hL _)]
            have hr : (1 : ℝ) ≤ (S.L : ℝ) ^ (j - 1) * S.L / a := by rw [le_div_iff₀ ha]; linarith
            calc (z : ℝ) = z * 1 := by ring
              _ ≤ z * ((S.L : ℝ) ^ (j - 1) * S.L / a) := mul_le_mul_of_nonneg_left hr hzr.le
              _ = S.L * ((z : ℝ) / a) * (S.L : ℝ) ^ (j - 1) := by ring
          calc ((z : ℝ) / (S.L : ℝ) ^ (j - 1)) ^ β ≤ (S.L * ((z : ℝ) / a)) ^ β :=
                Real.rpow_le_rpow (by positivity) h1 hβ0.le
            _ = (S.L : ℝ) ^ β * ((z : ℝ) / a) ^ β := Real.mul_rpow hL.le hq0
            _ ≤ S.L * ((z : ℝ) / a) ^ β := by
                gcongr
                exact Real.rpow_le_self_of_one_le hL1 hβ1
        calc ‖Ad (U.hol γ') (f i x') - f i x‖
            ≤ γ / (S.L : ℝ) ^ (2 * (j - 1)) * ((z : ℝ) / (S.L : ℝ) ^ (j - 1)) ^ β := hh
          _ ≤ S.L ^ 2 * γ / a ^ 2 * (S.L * ((z : ℝ) / a) ^ β) :=
              mul_le_mul hprev hratio (by positivity) (by positivity)
          _ = S.L ^ 3 * γ / a ^ 2 * ((z : ℝ) / a) ^ β := by ring
          _ ≤ 2 * (S.L ^ 3 * γ / a ^ 2 * ((z : ℝ) / a) ^ β) := by
              have : (0 : ℝ) ≤ S.L ^ 3 * γ / a ^ 2 * ((z : ℝ) / a) ^ β := by positivity
              linarith
          _ = 2 * S.L ^ 3 * γ / a ^ 2 * ((z : ℝ) / a) ^ β := by ring
    -- the difference of the transports of `𝐔` and `U`
    have hT2' : ‖Ad ((expMul 1 A' U).hol γ') (f i x') - Ad (U.hol γ') (f i x')‖ ≤
        12 * S.L ^ 3 * α₁ * γ / a ^ 2 * ((z : ℝ) / a) ^ β := by
      refine hT2.trans ?_
      have hzq : (z : ℝ) / a ≤ ((z : ℝ) / a) ^ β := Real.self_le_rpow_of_le_one hq0 hq1 hβ1
      calc 2 * t * (z : ℝ) * ‖f i x'‖ = 12 * S.L * α₁ * ((z : ℝ) / a) * ‖f i x'‖ := by
            simp only [t]; field_simp; ring
        _ ≤ 12 * S.L * α₁ * ((z : ℝ) / a) ^ β * (S.L ^ 2 * γ / a ^ 2) := by
            gcongr
        _ = 12 * S.L ^ 3 * α₁ * γ / a ^ 2 * ((z : ℝ) / a) ^ β := by ring
    calc ‖Ad ((expMul 1 A' U).hol γ') (f i x') - f i x‖
        ≤ ‖Ad ((expMul 1 A' U).hol γ') (f i x') - Ad (U.hol γ') (f i x')‖ +
            ‖Ad (U.hol γ') (f i x') - f i x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 12 * S.L ^ 3 * α₁ * γ / a ^ 2 * ((z : ℝ) / a) ^ β +
            2 * S.L ^ 3 * γ / a ^ 2 * ((z : ℝ) / a) ^ β := add_le_add hT2' hT1
      _ = (2 * S.L ^ 3 + 12 * S.L ^ 3 * α₁) * γ / a ^ 2 * ((z : ℝ) / a) ^ β := by ring

/-! ### The part `p̃` -/

/-- `p̃ = p + (D^*_U - D^*_V)K + (D_U - D_V)ψ` (`eq:divergence-conversion`, `η = 1`). -/
def ptilde (U V : Config N n) (K : Form2 N n) (ψ : Form0 N n) (p : Form1 N n) : Form1 N n :=
  fun μ x => p μ x + (Ds2 1 U K μ x - Ds2 1 V K μ x) + (D0 1 U ψ μ x - D0 1 V ψ μ x)

/-- `eq:divergence-conversion`: `D^*_UK + D_Uψ + p = D^*_VK + D_Vψ + p̃`. -/
theorem divergence_identity (U V : Config N n) (K : Form2 N n) (ψ : Form0 N n) (p : Form1 N n) :
    (fun μ x => Ds2 1 U K μ x + D0 1 U ψ μ x + p μ x) =
      fun μ x => Ds2 1 V K μ x + D0 1 V ψ μ x + ptilde U V K ψ p μ x := by
  funext μ x; simp only [ptilde]; abel

lemma dinf_neighbour (b : Bond n) : Blocks.dinf b.plus b.site ≤ 1 := by
  rw [Blocks.dinf_comm]; exact (Blocks.dinf_le_d1 _ _).trans (d1_plus b)

/-- `a_{j(x)}³|p̃(x)| ≤ (1 + 24L³α₁)γ ≤ L³γ`. -/
theorem ptilde_bound (hRM : (S.L : ℝ) ≤ S.RM) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) {α₁ : ℝ}
    (hα : 32 * S.L * α₁ ≤ 1) (hreg : RegA S A' α₁) {γ : ℝ} (hγ : 0 ≤ γ) (K : Form2 N n)
    (ψ : Form0 N n) (p : Form1 N n)
    (hK : ∀ j ≤ S.k, ∀ x ∈ S.Ω j, ∀ q : Fin 4 × Fin 4, ‖K q.1 q.2 x‖ ≤ γ / (S.L : ℝ) ^ (2 * j))
    (hψ : ∀ j ≤ S.k, ∀ x ∈ S.Ω j, ‖ψ x‖ ≤ γ / (S.L : ℝ) ^ (2 * j))
    (hp : ∀ j ≤ S.k, ∀ x ∈ S.Ω j, ∀ μ, ‖p μ x‖ ≤ γ / (S.L : ℝ) ^ (3 * j)) (x : Site n) (μ : Fin 4) :
    (S.L : ℝ) ^ (3 * S.sc x) * ‖ptilde U (expMul 1 A' U) K ψ p μ x‖ ≤ S.L ^ 3 * γ := by
  have hα0 := alpha_nonneg S hreg
  have hL := L_pos' S
  have hL1 : (1 : ℝ) ≤ S.L := by have := S.three_le_L; exact_mod_cast (by omega : 1 ≤ S.L)
  have hx : x ∈ S.Ω (S.sc x) := S.mem_sc x
  have hj : S.sc x ≤ S.k := S.sc_le x
  generalize S.sc x = j at hx hj ⊢
  set a : ℝ := (S.L : ℝ) ^ j with ha_def
  have ha : 0 < a := pow_pos hL _
  have hprev : γ / (S.L : ℝ) ^ (2 * (j - 1)) ≤ S.L ^ 2 * γ / a ^ 2 := by
    have ea2 : (S.L : ℝ) ^ (2 * j) = a ^ 2 := by rw [ha_def, ← pow_mul, mul_comm]
    rw [← ea2]; exact inv_sq_prev S j hγ
  have hRMj : (S.L : ℝ) ^ j ≤ S.RM * (S.L : ℝ) ^ (j - 1) := by
    have : (S.L : ℝ) ^ j ≤ S.L * (S.L : ℝ) ^ (j - 1) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ hL1 (by omega)
    nlinarith [pow_pos hL (j - 1)]
  -- the neighbours of `x` lie in `Ω_{j-1}`
  have hnb : ∀ b : Bond n, b.site = x → b.plus ∈ S.Ω (j - 1) := by
    intro b hb
    refine mem_prev S hx ?_
    have h1 := dinf_neighbour b
    rw [hb] at h1
    have : (Blocks.dinf b.plus x : ℝ) ≤ 1 := by exact_mod_cast h1
    have : (1 : ℝ) ≤ (S.L : ℝ) ^ j := one_le_pow₀ hL1
    linarith
  have hxprev : x ∈ S.Ω (j - 1) := S.Ω_anti (by omega) hx
  -- one bond at `x`
  have hbond : ∀ b : Bond n, b.site = x → ∀ Y : Mat,
      ‖Ad ((expMul 1 A' U).val b) Y - Ad (U.val b) Y‖ ≤ 6 * (S.L * α₁ / a) * ‖Y‖ := by
    intro b hb Y
    have h1 := bondA_le S hreg hα0 hj ⟨by rw [hb]; exact hxprev, hnb b hb⟩
    have h2 : ‖bondA A' b‖ ≤ 1 / 32 := by
      refine h1.trans ?_
      rw [div_le_iff₀ ha]
      have : (1 : ℝ) ≤ a := one_le_pow₀ hL1
      nlinarith
    refine (bond_bounds normLike_opNorm A' U hU b h2 Y).2.trans ?_
    gcongr
  set c := 6 * (S.L * α₁ / a) * (S.L ^ 2 * γ / a ^ 2)
  -- the terms of `(D^*_U - D^*_𝐔)K`
  have hDs : ‖Ds2 1 U K μ x - Ds2 1 (expMul 1 A' U) K μ x‖ ≤ 3 * c := by
    unfold Ds2
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ ν, ‖(if ν ≠ μ then Dbw 1 U ν (K ν μ) x else 0) -
        (if ν ≠ μ then Dbw 1 (expMul 1 A' U) ν (K ν μ) x else 0)‖ ≤ if ν ≠ μ then c else 0 := by
      intro ν
      split_ifs with hν
      · simp only [Dbw, inv_one, one_smul]
        rw [show Ad (U.val ⟨x, ν, false⟩) (K ν μ (x - unit n ν)) - K ν μ x -
          (Ad ((expMul 1 A' U).val ⟨x, ν, false⟩) (K ν μ (x - unit n ν)) - K ν μ x) =
          -(Ad ((expMul 1 A' U).val ⟨x, ν, false⟩) (K ν μ (x - unit n ν)) -
            Ad (U.val ⟨x, ν, false⟩) (K ν μ (x - unit n ν))) by abel, norm_neg]
        refine (hbond ⟨x, ν, false⟩ rfl _).trans ?_
        have hY := hK (j - 1) (by omega) (x - unit n ν) (by
          have := hnb ⟨x, ν, false⟩ rfl; simpa [Bond.plus] using this) (ν, μ)
        have : ‖K ν μ (x - unit n ν)‖ ≤ S.L ^ 2 * γ / a ^ 2 := hY.trans hprev
        exact mul_le_mul_of_nonneg_left this (by positivity)
      · simp
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ν _ => hterm ν).trans ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_ne' _ μ,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  -- the term of `(D_U - D_𝐔)ψ`
  have hD0 : ‖D0 1 U ψ μ x - D0 1 (expMul 1 A' U) ψ μ x‖ ≤ c := by
    simp only [D0, Dfw, inv_one, one_smul]
    have e1 : U μ x = U.val ⟨x, μ, true⟩ := by simp [Config.val]
    have e2 : expMul 1 A' U μ x = (expMul 1 A' U).val ⟨x, μ, true⟩ := by simp [Config.val]
    rw [e1, e2, show Ad (U.val ⟨x, μ, true⟩) (ψ (x + unit n μ)) - ψ x -
      (Ad ((expMul 1 A' U).val ⟨x, μ, true⟩) (ψ (x + unit n μ)) - ψ x) =
      -(Ad ((expMul 1 A' U).val ⟨x, μ, true⟩) (ψ (x + unit n μ)) -
        Ad (U.val ⟨x, μ, true⟩) (ψ (x + unit n μ))) by abel, norm_neg]
    refine (hbond ⟨x, μ, true⟩ rfl _).trans ?_
    have hY := hψ (j - 1) (by omega) (x + unit n μ) (by
      have := hnb ⟨x, μ, true⟩ rfl; simpa [Bond.plus] using this)
    exact mul_le_mul_of_nonneg_left (hY.trans hprev) (by positivity)
  have hpx : ‖p μ x‖ ≤ γ / a ^ 3 := by
    have := hp j hj x hx μ
    rwa [show (S.L : ℝ) ^ (3 * j) = a ^ 3 by rw [ha_def, ← pow_mul, mul_comm]] at this
  -- the sum
  have htot : ‖ptilde U (expMul 1 A' U) K ψ p μ x‖ ≤ γ / a ^ 3 + 4 * c := by
    unfold ptilde
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) hD0).trans ?_
    linarith
  have ec : 4 * c = 24 * S.L ^ 3 * α₁ * γ / a ^ 3 := by simp only [c]; field_simp; ring
  rw [ec] at htot
  have ea3 : (S.L : ℝ) ^ (3 * j) = a ^ 3 := by rw [ha_def, ← pow_mul, mul_comm]
  rw [ea3]
  calc a ^ 3 * ‖ptilde U (expMul 1 A' U) K ψ p μ x‖ ≤ a ^ 3 * (γ / a ^ 3 + 24 * S.L ^ 3 * α₁ * γ / a ^ 3) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = (1 + 24 * S.L ^ 3 * α₁) * γ := by field_simp
    _ ≤ S.L ^ 3 * γ := by
        refine mul_le_mul_of_nonneg_right ?_ hγ
        have h3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
        have : 24 * (S.L : ℝ) ^ 3 * α₁ ≤ 3 / 4 * S.L ^ 2 := by nlinarith [pow_pos hL 2]
        nlinarith

/-- `lem:divergence-conversion`: for a sequence of domains with `RM ≥ L`, a gauge field `U`, `A'` with
`eq:regular-complex` (first bound) and `32Lα₁ ≤ 1`, `𝐔 = e^{iA'}U`, and `𝐉 = D^*_UK + D_Uψ + p` of the
size `γ` in divergence form with respect to `U` (exponent `0 < β ≤ 1`): `𝐉 = D^*_𝐔K + D_𝐔ψ + p̃`, and `K`,
`ψ`, `p̃` satisfy `eq:divergence-size-local` with the norms of `𝐔` and `4L³γ`. -/
theorem divergence_conversion (hRM : (S.L : ℝ) ≤ S.RM) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ) {α₁ : ℝ}
    (hα : 32 * S.L * α₁ ≤ 1) (hreg : RegA S A' α₁) {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (K : Form2 N n) (ψ : Form0 N n) (p : Form1 N n) (hJ : DivSize S U K ψ p β γ) :
    ((fun μ x => Ds2 1 U K μ x + D0 1 U ψ μ x + p μ x) =
      fun μ x => Ds2 1 (expMul 1 A' U) K μ x + D0 1 (expMul 1 A' U) ψ μ x +
        ptilde U (expMul 1 A' U) K ψ p μ x) ∧
    (∀ y, LocalHolder S (expMul 1 A' U) y (fun q : Fin 4 × Fin 4 => K q.1 q.2) β (4 * S.L ^ 3 * γ)) ∧
    (∀ y, LocalHolder S (expMul 1 A' U) y (fun _ : Unit => ψ) β (4 * S.L ^ 3 * γ)) ∧
    (∀ x μ, (S.L : ℝ) ^ (3 * S.sc x) * ‖ptilde U (expMul 1 A' U) K ψ p μ x‖ ≤ 4 * S.L ^ 3 * γ) := by
  have hγ : 0 ≤ γ := by
    have := hJ.ψ_sup 0 (Nat.zero_le _) 0 (by simp [S.Ω_zero]) ()
    simpa using (norm_nonneg _).trans this
  refine ⟨divergence_identity _ _ K ψ p,
    fun y => local_holder S hRM A' U hU hα hreg hβ0 hβ1 hγ _ hJ.K_sup hJ.K_hol y,
    fun y => local_holder S hRM A' U hU hα hreg hβ0 hβ1 hγ _ hJ.ψ_sup hJ.ψ_hol y,
    fun x μ => ?_⟩
  have := ptilde_bound S hRM A' U hU hα hreg hγ K ψ p hJ.K_sup (fun j hj x hx => hJ.ψ_sup j hj x hx ())
    hJ.p_sup x μ
  have hL := L_pos' S
  nlinarith [pow_pos hL 3]

end Transports

end CoreLean
