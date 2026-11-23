/-
`lem:group-mean` of BALABAN_CORE.tex (`bf6b2bc552ba`), in part.

For `W_i W_1⁻¹ = e^{iY_i}` and `W = e^{iZ}W_1` we have `W_iW⁻¹ = e^{iY_i}e^{-iZ}`, and `eq:group-mean`,
`Σ_i Log(W_iW⁻¹) = 0`, reads `Σ_i Ψ(Y_i, -Z) = 0` (`log_eq_I_psi`), that is `Z = T(Z)` with
`T(Z) = n⁻¹ Σ_i (Y_i + Φ(Y_i, -Z))`, `Φ(X, Y) = Ψ(X, Y) - X - Y` (`sum_psi_eq_zero_iff`). From
`eq:product-lipschitz` with `C_Ψ = 256`, `‖Φ(X, Y)‖ ≤ 256‖X‖‖Y‖` and
`‖Φ(X, Y') - Φ(X, Y)‖ ≤ 256‖X‖‖Y' - Y‖`. If `‖Y_i‖ ≤ M` with `512M ≤ 1` (the core's `M = 2ϱ_𝗆`,
`ϱ_𝗆 ≤ 2^{-10}`), the map `T` sends the ball `‖Z‖ ≤ 2M` into itself and contracts with the constant
`1/2` there; so the equation has exactly one solution in the ball (`group_mean`), on every closed set
which `T` preserves, in particular in `𝔤^c` (`group_mean_lieC`), and `‖Z‖ ≤ 2 max_i ‖Y_i‖`
(`norm_le_two_max`). The solution does not depend on the order (`T_perm`); it is covariant under the
right multiplications (`right_mul`) and, through `Ad`, under the left ones (`solves_Ad`). Finally the
expansion with `C_𝗆 = 2¹¹` (`expansion`) and the bounds of its proof (`expansion_bounds`).

Not formalised: the holomorphy of `Z`, the statements on `G` (`lem:chart`(ii), (iii)), and the
inverses.
-/
import CoreLean.Psi

open NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace GroupMean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `Φ(X, Y) = Ψ(X, Y) - X - Y`. -/
def Phi (X Y : Mat) : Mat := psi X Y - X - Y

lemma psi_zero_zero : psi (0 : Mat) 0 = 0 := psi_zero_left (by simp)

/-- `‖Φ(X, Y)‖ ≤ C_Ψ‖X‖‖Y‖`. -/
lemma norm_Phi_le {X Y : Mat} (hX : ‖X‖ ≤ 1 / 32) (hY : ‖Y‖ ≤ 1 / 32) :
    ‖Phi X Y‖ ≤ 256 * ‖X‖ * ‖Y‖ := by
  have h := psi_lipschitz (X := (0 : Mat)) (Y := 0) (by simp) (by simp) hX hY
  simp only [psi_zero_zero, sub_zero, norm_zero, zero_mul, add_zero] at h
  unfold Phi; linarith [h, mul_comm ‖Y‖ ‖X‖]

/-- `‖Φ(X, Y') - Φ(X, Y)‖ ≤ C_Ψ‖X‖‖Y' - Y‖`. -/
lemma Phi_lip {X Y Y' : Mat} (hX : ‖X‖ ≤ 1 / 32) (hY : ‖Y‖ ≤ 1 / 32) (hY' : ‖Y'‖ ≤ 1 / 32) :
    ‖Phi X Y' - Phi X Y‖ ≤ 256 * ‖X‖ * ‖Y' - Y‖ := by
  have h := psi_lipschitz hX hY hX hY'
  simp only [sub_self, norm_zero, mul_zero, zero_add, sub_zero] at h
  have e : Phi X Y' - Phi X Y = psi X Y' - psi X Y - (Y' - Y) := by unfold Phi; abel
  rw [e]; linarith

variable {n : ℕ}

/-- `T(Z) = n⁻¹ Σ_i (Y_i + Φ(Y_i, -Z))`. -/
def T (Y : Fin n → Mat) (Z : Mat) : Mat := ((n : ℂ)⁻¹) • ∑ i, (Y i + Phi (Y i) (-Z))

lemma norm_inv_smul (hn : 0 < n) (S : Mat) : ‖((n : ℂ)⁻¹) • S‖ = (n : ℝ)⁻¹ * ‖S‖ := by
  rw [norm_smul, norm_inv]; norm_cast

/-- `Σ_i Ψ(Y_i, -Z) = 0` if and only if `Z = T(Z)`. -/
theorem sum_psi_eq_zero_iff (hn : 0 < n) (Y : Fin n → Mat) (Z : Mat) :
    ∑ i, psi (Y i) (-Z) = 0 ↔ T Y Z = Z := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : ∑ i, psi (Y i) (-Z) = ∑ i, (Y i + Phi (Y i) (-Z)) - (n : ℂ) • Z := by
    rw [show (n : ℂ) • Z = ∑ _i : Fin n, Z by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold Phi; abel
  rw [e, sub_eq_zero, T]
  constructor
  · intro h; rw [h, smul_smul, inv_mul_cancel₀ hn', one_smul]
  · intro h
    conv_rhs => rw [← h]
    rw [smul_smul, mul_inv_cancel₀ hn', one_smul]

section Bounds

lemma M_nonneg (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ) (hYM : ∀ i, ‖Y i‖ ≤ M) : 0 ≤ M := by
  have := hYM ⟨0, hn⟩; exact (norm_nonneg _).trans this

/-- `‖T(Z)‖ ≤ M' + ½‖Z‖` for `‖Z‖ ≤ 2M` and `‖Y_i‖ ≤ M'`. -/
lemma norm_T_le (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ) (hYM : ∀ i, ‖Y i‖ ≤ M) (hM : 512 * M ≤ 1)
    (M' : ℝ) (hYM' : ∀ i, ‖Y i‖ ≤ M') {Z : Mat} (hZ : ‖Z‖ ≤ 2 * M) :
    ‖T Y Z‖ ≤ M' + ‖Z‖ / 2 := by
  have hM0 := M_nonneg hn Y M hYM
  have hZs : ‖-Z‖ ≤ 1 / 32 := by rw [norm_neg]; linarith
  have hterm : ∀ i, ‖Y i + Phi (Y i) (-Z)‖ ≤ M' + ‖Z‖ / 2 := fun i => by
    have hYs : ‖Y i‖ ≤ 1 / 32 := (hYM i).trans (by linarith)
    have := norm_Phi_le hYs hZs
    rw [norm_neg] at this
    have h256 : 256 * ‖Y i‖ * ‖Z‖ ≤ ‖Z‖ / 2 := by
      have := mul_le_mul_of_nonneg_right (hYM i) (norm_nonneg Z)
      nlinarith [norm_nonneg Z]
    exact (norm_add_le _ _).trans (by linarith [hYM' i])
  rw [T, norm_inv_smul hn]
  have hs := norm_sum_le Finset.univ fun i => Y i + Phi (Y i) (-Z)
  have hs2 : ∑ i, ‖Y i + Phi (Y i) (-Z)‖ ≤ ∑ _i : Fin n, (M' + ‖Z‖ / 2) :=
    Finset.sum_le_sum fun i _ => hterm i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ)⁻¹ * ‖∑ i, (Y i + Phi (Y i) (-Z))‖ ≤ (n : ℝ)⁻¹ * (n * (M' + ‖Z‖ / 2)) := by
        gcongr; exact hs.trans hs2
    _ = M' + ‖Z‖ / 2 := by field_simp

/-- `T` maps the ball `‖Z‖ ≤ 2M` into itself. -/
lemma T_mapsTo (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ) (hYM : ∀ i, ‖Y i‖ ≤ M) (hM : 512 * M ≤ 1) {Z : Mat} (hZ : ‖Z‖ ≤ 2 * M) : ‖T Y Z‖ ≤ 2 * M := by
  have := norm_T_le hn Y M hYM hM M hYM hZ
  linarith

/-- `T` contracts with the constant `1/2` on the ball `‖Z‖ ≤ 2M`. -/
lemma T_contract (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ) (hYM : ∀ i, ‖Y i‖ ≤ M) (hM : 512 * M ≤ 1) {Z Z' : Mat} (hZ : ‖Z‖ ≤ 2 * M) (hZ' : ‖Z'‖ ≤ 2 * M) :
    ‖T Y Z - T Y Z'‖ ≤ ‖Z - Z'‖ / 2 := by
  have hM0 := M_nonneg hn Y M hYM
  have hterm : ∀ i, ‖Phi (Y i) (-Z) - Phi (Y i) (-Z')‖ ≤ ‖Z - Z'‖ / 2 := fun i => by
    have hYs : ‖Y i‖ ≤ 1 / 32 := (hYM i).trans (by linarith)
    have h := Phi_lip hYs (Y := -Z') (Y' := -Z) (by rw [norm_neg]; linarith)
      (by rw [norm_neg]; linarith)
    rw [show -Z - -Z' = -(Z - Z') by abel, norm_neg] at h
    have := mul_le_mul_of_nonneg_right (hYM i) (norm_nonneg (Z - Z'))
    nlinarith [norm_nonneg (Z - Z')]
  have e : T Y Z - T Y Z' = ((n : ℂ)⁻¹) • ∑ i, (Phi (Y i) (-Z) - Phi (Y i) (-Z')) := by
    rw [T, T, ← smul_sub, ← Finset.sum_sub_distrib]
    congr 1; refine Finset.sum_congr rfl fun i _ => by abel
  rw [e, norm_inv_smul hn]
  have hs := norm_sum_le Finset.univ fun i => Phi (Y i) (-Z) - Phi (Y i) (-Z')
  have hs2 : ∑ i, ‖Phi (Y i) (-Z) - Phi (Y i) (-Z')‖ ≤ ∑ _i : Fin n, ‖Z - Z'‖ / 2 :=
    Finset.sum_le_sum fun i _ => hterm i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ)⁻¹ * ‖∑ i, (Phi (Y i) (-Z) - Phi (Y i) (-Z'))‖ ≤ (n : ℝ)⁻¹ * (n * (‖Z - Z'‖ / 2)) := by
        gcongr; exact hs.trans hs2
    _ = ‖Z - Z'‖ / 2 := by field_simp

/-- Uniqueness in the ball. -/
lemma fixed_unique (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ) (hYM : ∀ i, ‖Y i‖ ≤ M) (hM : 512 * M ≤ 1) {Z Z' : Mat} (hZ : ‖Z‖ ≤ 2 * M) (hZ' : ‖Z'‖ ≤ 2 * M) (h : T Y Z = Z)
    (h' : T Y Z' = Z') : Z = Z' := by
  have := T_contract hn Y M hYM hM hZ hZ'
  rw [h, h'] at this
  have h0 : ‖Z - Z'‖ = 0 := by linarith [norm_nonneg (Z - Z')]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- Existence on a closed set `C ∋ 0` which `T` preserves. -/
lemma fixed_exists (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ) (hYM : ∀ i, ‖Y i‖ ≤ M) (hM : 512 * M ≤ 1) (C : Set Mat) (hC : IsClosed C) (h0 : (0 : Mat) ∈ C)
    (hTC : ∀ Z ∈ C, ‖Z‖ ≤ 2 * M → T Y Z ∈ C) :
    ∃ Z ∈ C, ‖Z‖ ≤ 2 * M ∧ T Y Z = Z := by
  set s : Set Mat := C ∩ Metric.closedBall 0 (2 * M)
  have hM0 := M_nonneg hn Y M hYM
  have hsc : IsComplete s := (hC.inter Metric.isClosed_closedBall).isComplete
  have hball : ∀ Z ∈ s, ‖Z‖ ≤ 2 * M := fun Z hZ => by
    have := hZ.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hsf : Set.MapsTo (T Y) s s := fun Z hZ =>
    ⟨hTC Z hZ.1 (hball Z hZ), by
      rw [Metric.mem_closedBall, dist_zero_right]; exact T_mapsTo hn Y M hYM hM (hball Z hZ)⟩
  have hcon : ContractingWith (1 / 2 : NNReal) (hsf.restrict (T Y) s s) := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simp only [Set.MapsTo.val_restrict_apply]
    have := T_contract hn Y M hYM hM (hball a a.2) (hball b b.2)
    push_cast; linarith
  have h0s : (0 : Mat) ∈ s := ⟨h0, by simp [hM0]⟩
  obtain ⟨Z, hZs, hfix, -⟩ := hcon.exists_fixedPoint' hsc hsf h0s (edist_ne_top _ _)
  exact ⟨Z, hZs.1, hball Z hZs, hfix⟩

end Bounds

/-- `lem:group-mean`, existence and uniqueness: for `‖Y_i‖ ≤ M`, `512M ≤ 1`, the equation
`Σ_i Ψ(Y_i, -Z) = 0` has exactly one solution `Z` with `‖Z‖ ≤ 2M`. -/
theorem group_mean (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ) (hYM : ∀ i, ‖Y i‖ ≤ M)
    (hM : 512 * M ≤ 1) : ∃! Z : Mat, ‖Z‖ ≤ 2 * M ∧ ∑ i, psi (Y i) (-Z) = 0 := by
  obtain ⟨Z, -, hZ, hfix⟩ := fixed_exists hn Y M hYM hM Set.univ isClosed_univ trivial
    (fun _ _ _ => trivial)
  refine ⟨Z, ⟨hZ, (sum_psi_eq_zero_iff hn Y Z).2 hfix⟩, fun Z' ⟨hZ', h'⟩ => ?_⟩
  exact fixed_unique hn Y M hYM hM hZ' hZ ((sum_psi_eq_zero_iff hn Y Z').1 h') hfix

/-- `‖Z‖ ≤ 2 max_i ‖Y_i‖`: the solution in the ball `‖Z‖ ≤ 2M` satisfies `‖Z‖ ≤ 2M'` for every
`M' ≥ ‖Y_i‖`. -/
theorem norm_le_two_max (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ) (hYM : ∀ i, ‖Y i‖ ≤ M)
    (hM : 512 * M ≤ 1) (M' : ℝ) (hYM' : ∀ i, ‖Y i‖ ≤ M') {Z : Mat} (hZ : ‖Z‖ ≤ 2 * M)
    (hsol : ∑ i, psi (Y i) (-Z) = 0) : ‖Z‖ ≤ 2 * M' := by
  have hfix := (sum_psi_eq_zero_iff hn Y Z).1 hsol
  have := norm_T_le hn Y M hYM hM M' hYM' hZ
  rw [hfix] at this; linarith

/-- `lem:group-mean` in `𝔤^c`: if the `Y_i` lie in `𝔤^c`, the solution lies in `𝔤^c`. -/
theorem group_mean_lieC (G : GaugeGroup N) (hG : G.LieInput) (hn : 0 < n) (Y : Fin n → Mat) (M : ℝ)
    (hYM : ∀ i, ‖Y i‖ ≤ M) (hM : 512 * M ≤ 1) (hY : ∀ i, Y i ∈ G.lieC) :
    ∃ Z ∈ G.lieC, ‖Z‖ ≤ 2 * M ∧ ∑ i, psi (Y i) (-Z) = 0 := by
  have hM0 := M_nonneg hn Y M hYM
  set L := GaugeGroup.lieCSubmodule hG
  have hcl : IsClosed (L : Set Mat) := Submodule.isClosed_of_finiteDimensional L
  have hTC : ∀ Z ∈ (L : Set Mat), ‖Z‖ ≤ 2 * M → T Y Z ∈ (L : Set Mat) := fun Z hZ hZn => by
    have hZ' : Z ∈ G.lieC := (GaugeGroup.mem_lieCSubmodule hG).1 hZ
    refine L.smul_mem _ (L.sum_mem fun i _ => L.add_mem ((GaugeGroup.mem_lieCSubmodule hG).2 (hY i)) ?_)
    have hpsi : psi (Y i) (-Z) ∈ G.lieC := by
      refine psi_mem hG (hY i) ((GaugeGroup.mem_lieCSubmodule hG).1 (L.neg_mem hZ)) ?_
      rw [norm_neg]; linarith [hYM i]
    exact L.sub_mem (L.sub_mem ((GaugeGroup.mem_lieCSubmodule hG).2 hpsi)
      ((GaugeGroup.mem_lieCSubmodule hG).2 (hY i))) (L.neg_mem hZ)
  obtain ⟨Z, hZC, hZ, hfix⟩ := fixed_exists hn Y M hYM hM (L : Set Mat) hcl L.zero_mem hTC
  exact ⟨Z, (GaugeGroup.mem_lieCSubmodule hG).1 hZC, hZ, (sum_psi_eq_zero_iff hn Y Z).2 hfix⟩

/-- The solution does not depend on the order: `T` is invariant under the permutations. -/
theorem T_perm (Y : Fin n → Mat) (σ : Equiv.Perm (Fin n)) (Z : Mat) : T (Y ∘ σ) Z = T Y Z := by
  unfold T
  exact congrArg _ (Equiv.sum_comp σ (fun i => Y i + Phi (Y i) (-Z)))

/-- `Log(e^{iY}e^{-iZ}) = iΨ(Y, -Z)`, so that `eq:group-mean` for `W = e^{iZ}W_1` is
`Σ_i Ψ(Y_i, -Z) = 0`. -/
theorem log_eq_I_psi (Y Z : Mat) :
    LogM (exp (Complex.I • Y) * exp (Complex.I • -Z)) = Complex.I • psi Y (-Z) := by
  rw [psi_eq_Log, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]

/-- `W_iW⁻¹ = e^{iY_i}e^{-iZ}` for `W_i = e^{iY_i}W_1` and `W = e^{iZ}W_1`. -/
theorem quotient (Y Z : Mat) (W₁ : GLN) :
    (expU (Complex.I • Y) * W₁) * (expU (Complex.I • Z) * W₁)⁻¹ =
      expU (Complex.I • Y) * expU (Complex.I • -Z) := by
  rw [mul_inv_rev, show expU (Complex.I • -Z) = (expU (Complex.I • Z))⁻¹ by
    rw [expU_inv, smul_neg]]
  group

/-- Right covariance: `(W_iv)(W_1v)⁻¹ = W_iW_1⁻¹` and `(Wv)(W_iv)⁻¹ = WW_i⁻¹`, so that the elements
`W_iv` have the same `Y_i` and `Wv` solves their equation. -/
theorem right_mul (Wi W₁ W v : GLN) :
    (Wi * v) * (W₁ * v)⁻¹ = Wi * W₁⁻¹ ∧ (W * v) * (Wi * v)⁻¹ = W * Wi⁻¹ := by
  constructor <;> group

/-- Left covariance: if `Z` solves the equation of the `Y_i`, then `Ad_u Z` solves that of the
`Ad_u Y_i`. -/
theorem solves_Ad (u : GLN) (Y : Fin n → Mat) (Z : Mat) (h : ∑ i, psi (Y i) (-Z) = 0) :
    ∑ i, psi (Ad u (Y i)) (-Ad u Z) = 0 := by
  have : ∑ i, psi (Ad u (Y i)) (-Ad u Z) = Ad u (∑ i, psi (Y i) (-Z)) := by
    rw [Ad_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Ad_psi, Ad_neg]
  rw [this, h]; simp [Ad]

/-- The bounds of the proof of the expansion: for `‖X_i‖ ≤ ϱ` with `2¹²ϱ ≤ 1` (the core's
`ϱ ≤ ϱ_𝗆/4 ≤ 2^{-12}`),
`‖Ψ(X_i, -X_1)‖ ≤ 3ϱ`; and for `‖Z‖ ≤ 6ϱ`, `‖Ψ(Z, X_1)‖ ≤ 8ϱ`, `e^{iΨ(Z, X_1)} = e^{iZ}e^{iX_1}`. -/
theorem expansion_bounds (ρ : ℝ) (hρ : 4096 * ρ ≤ 1) {X X₁ Z : Mat} (hX : ‖X‖ ≤ ρ)
    (hX₁ : ‖X₁‖ ≤ ρ) (hZ : ‖Z‖ ≤ 6 * ρ) :
    ‖psi X (-X₁)‖ ≤ 3 * ρ ∧ ‖psi Z X₁‖ ≤ 8 * ρ ∧
      exp (Complex.I • psi Z X₁) = exp (Complex.I • Z) * exp (Complex.I • X₁) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hX
  have s1 : ‖X‖ ≤ 1 / 32 := by linarith
  have s2 : ‖-X₁‖ ≤ 1 / 32 := by rw [norm_neg]; linarith
  have s3 : ‖Z‖ ≤ 1 / 32 := by linarith
  have s4 : ‖X₁‖ ≤ 1 / 32 := by linarith
  refine ⟨?_, ?_, exp_I_psi (by linarith [Real.log_two_gt_d9])⟩
  · have h := norm_Phi_le s1 s2
    rw [norm_neg] at h
    have e : psi X (-X₁) = Phi X (-X₁) + X + -X₁ := by unfold Phi; abel
    rw [e]
    have h2 : 256 * ‖X‖ * ‖X₁‖ ≤ ρ := by
      have := mul_le_mul hX hX₁ (norm_nonneg _) hρ0
      nlinarith
    calc ‖Phi X (-X₁) + X + -X₁‖ ≤ ‖Phi X (-X₁)‖ + ‖X‖ + ‖-X₁‖ := norm_add₃_le
      _ ≤ 3 * ρ := by rw [norm_neg]; linarith
  · have h := norm_Phi_le s3 s4
    have e : psi Z X₁ = Phi Z X₁ + Z + X₁ := by unfold Phi; abel
    rw [e]
    have h2 : 256 * ‖Z‖ * ‖X₁‖ ≤ ρ := by
      have := mul_le_mul hZ hX₁ (norm_nonneg _) (by linarith)
      nlinarith
    calc ‖Phi Z X₁ + Z + X₁‖ ≤ ‖Phi Z X₁‖ + ‖Z‖ + ‖X₁‖ := norm_add₃_le
      _ ≤ 8 * ρ := by linarith

/-- `lem:group-mean`, the expansion with `C_𝗆 = 2¹¹`: if `‖X_i‖ ≤ ϱ`, `‖V‖ ≤ 8ϱ`, `256ϱ ≤ 1`, and
`Σ_i Ψ(X_i, -V) = 0`, then `‖V - n⁻¹ Σ_i X_i‖ ≤ 2¹¹ϱ²`. -/
theorem expansion (hn : 0 < n) (X : Fin n → Mat) (V : Mat) (ρ : ℝ) (hρ : 256 * ρ ≤ 1)
    (hX : ∀ i, ‖X i‖ ≤ ρ) (hV : ‖V‖ ≤ 8 * ρ) (hsol : ∑ i, psi (X i) (-V) = 0) :
    ‖V - ((n : ℂ)⁻¹) • ∑ i, X i‖ ≤ 2 ^ 11 * ρ ^ 2 := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hX ⟨0, hn⟩)
  have hfix := (sum_psi_eq_zero_iff hn X V).1 hsol
  have e : V - ((n : ℂ)⁻¹) • ∑ i, X i = ((n : ℂ)⁻¹) • ∑ i, Phi (X i) (-V) := by
    conv_lhs => rw [← hfix]
    rw [T, ← smul_sub, ← Finset.sum_sub_distrib]
    congr 1; refine Finset.sum_congr rfl fun i _ => by abel
  rw [e, norm_inv_smul hn]
  have hterm : ∀ i, ‖Phi (X i) (-V)‖ ≤ 2 ^ 11 * ρ ^ 2 := fun i => by
    have h := norm_Phi_le (X := X i) (Y := -V) (by linarith [hX i]) (by rw [norm_neg]; linarith)
    rw [norm_neg] at h
    have := mul_le_mul (hX i) hV (norm_nonneg _) hρ0
    nlinarith
  have hs := norm_sum_le Finset.univ fun i => Phi (X i) (-V)
  have hs2 : ∑ i, ‖Phi (X i) (-V)‖ ≤ ∑ _i : Fin n, 2 ^ 11 * ρ ^ 2 :=
    Finset.sum_le_sum fun i _ => hterm i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ)⁻¹ * ‖∑ i, Phi (X i) (-V)‖ ≤ (n : ℝ)⁻¹ * (n * (2 ^ 11 * ρ ^ 2)) := by
        gcongr; exact hs.trans hs2
    _ = 2 ^ 11 * ρ ^ 2 := by field_simp

end GroupMean
end CoreLean

end
