/-
The analytic inputs of `lem:moved-transports` and `lem:axial-smallness` of BALABAN_CORE.tex
(`a7d5e1f955b0`), discharged from `def:group-mean`, `lem:group-mean` (`GroupMean.lean`), `lem:chart`, and
`def:average` (`AverageAlgebra.lean`, `ChartAverage.lean`).

* `meanV X`: the solution `V` of `Σ_i Ψ(X_i, -V) = 0` with `‖V‖ ≤ 1/256` (`meanV_spec`, `meanV_unique`,
  `norm_meanV_le`), and `meanV_lipschitz`: `‖V(X') - V(X)‖ ≤ 4 max_i ‖X'_i - X_i‖`. This is proved from the
  contraction of `GroupMean.T` and the Lipschitz bound of `Φ` in its first argument, without the holomorphy
  of `V` and without Cauchy's estimate, which the core uses for `lem:moved-transports`(i).
* `mean Y W₁ = e^{iV(Y)}W₁`, the mean of `def:group-mean`(i) of `W_i = e^{iY_i}W₁` (`mean_spec`,
  `mean_unique`), and `mean_exp`: for `W_i = e^{iX_i}`, `‖X_i‖ ≤ ϱ ≤ 2^{-12}`, the mean is `e^{iV(X)}` and
  `(1/i) Log 𝗆({e^{iX_i}}) = V(X)` (the last statement of `lem:group-mean`).
* `moved_transports_i_mean`: `lem:moved-transports`(i) for the mean itself, with the constant `4 ≤ 16`.
* `Step`, `movedExps`, `moved_prod`, `norm_movedExps_le`: the moved holonomy
  `(e^{iaA}𝐔)(Γ) = E_Γ𝐔(Γ)`, `E_Γ = Π_k e^{iY_k}`, `Y_k = ±Ad_{𝐔(γ_k)}A(b_k)`, and `‖Y_k‖ ≤ 2‖aA‖_∞` under the
  hypothesis `‖Ad_{𝐔(γ)}Z‖ ≤ 2‖Z‖` of `lem:moved-transports`(ii) for the pieces `γ` from `y`.
* `moved_transports_ii_mean`: `lem:moved-transports`(ii) for the rule `m`, with `𝐔_m(y, x)` the mean of the
  `𝐔(Γ)` (`eq:group-mean`) and the mean of the moved holonomies; `‖(1/i) Log(…)‖ ≤ 96L‖aA‖_∞ ≤ 2^{11}L‖aA‖_∞`.
* `avg_path_factor`: `U([c]) = e^{-iβ_c(U)}M(U)(c)` with `e^{-iβ_c} ∈ G` and `‖e^{-iβ_c} - 1‖ ≤ 7√NL²α`
  (`def:average`, `lem:average`(v) from the loop bound, `lem:chart`(iii)).
* `kappa_bound`: for `W(Γ)` in `G` with `‖W(Γ)W(Γ_x)⁻¹ - 1‖ ≤ b ≤ r_G`, `W(Γ) = e^{iY_Γ}W(Γ_x)` with
  `‖Y_Γ‖ ≤ (π/2)b` (`lem:chart`(ii)–(iii)) and the mean `W_m = e^{iZ}W(Γ_x)` has `‖W_m - W(Γ_x)‖ ≤ 2πb`; for
  `b = (3/2)√Nα₀` this is `κ = 10√N` of `eq:axial-path-transport`.
-/
import CoreLean.MovedTransportsII
import CoreLean.GroupMean
import CoreLean.ChartLog
import CoreLean.ChartAverage
import CoreLean.AxialSmallness

open NormedSpace Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace MeanTransports

open GroupMean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### The exponent of the mean -/

/-- `‖Φ(X', Y) - Φ(X, Y)‖ ≤ C_Ψ‖Y‖‖X' - X‖` (`eq:product-lipschitz` at `(X, Y)`, `(X', Y)`). -/
lemma Phi_lip_left {X X' Y : Mat} (hX : ‖X‖ ≤ 1 / 32) (hX' : ‖X'‖ ≤ 1 / 32) (hY : ‖Y‖ ≤ 1 / 32) :
    ‖Phi X' Y - Phi X Y‖ ≤ 256 * ‖Y‖ * ‖X' - X‖ := by
  have h := psi_lipschitz hX hY hX' hY
  simp only [sub_self, norm_zero, mul_zero, add_zero, sub_zero] at h
  have e : Phi X' Y - Phi X Y = psi X' Y - psi X Y - (X' - X) := by unfold Phi; abel
  rw [e, mul_assoc]
  exact h

variable {n : ℕ}

/-- The exponent of the mean of `e^{iX_i}`: the solution `V` of `Σ_i Ψ(X_i, -V) = 0` with
`‖V‖ ≤ 1/256`. -/
noncomputable def meanV (X : Fin n → Mat) : Mat :=
  haveI := Classical.propDecidable
  if h : ∃ V : Mat, ‖V‖ ≤ 1 / 256 ∧ T X V = V then h.choose else 0

lemma hM512 : 512 * (1 / 512 : ℝ) ≤ 1 := by norm_num

lemma meanV_spec (hn : 0 < n) {X : Fin n → Mat} (hX : ∀ i, ‖X i‖ ≤ 1 / 512) :
    ‖meanV X‖ ≤ 1 / 256 ∧ ∑ i, psi (X i) (-meanV X) = 0 := by
  obtain ⟨V, -, hV, hfix⟩ := fixed_exists hn X (1 / 512) hX hM512 Set.univ isClosed_univ trivial
    (fun _ _ _ => trivial)
  have hex : ∃ V : Mat, ‖V‖ ≤ 1 / 256 ∧ T X V = V := ⟨V, by linarith, hfix⟩
  have e : meanV X = hex.choose := by
    unfold meanV
    exact dite_eq_left_of_eq_true (eq_true hex)
  rw [e]
  exact ⟨hex.choose_spec.1, (sum_psi_eq_zero_iff hn X _).2 hex.choose_spec.2⟩

lemma meanV_unique (hn : 0 < n) {X : Fin n → Mat} (hX : ∀ i, ‖X i‖ ≤ 1 / 512) {V : Mat}
    (hV : ‖V‖ ≤ 1 / 256) (h : ∑ i, psi (X i) (-V) = 0) : V = meanV X := by
  obtain ⟨hm, hms⟩ := meanV_spec hn hX
  exact fixed_unique hn X (1 / 512) hX hM512 (by linarith) (by linarith)
    ((sum_psi_eq_zero_iff hn X V).1 h) ((sum_psi_eq_zero_iff hn X _).1 hms)

lemma norm_meanV_le (hn : 0 < n) {X : Fin n → Mat} (hX : ∀ i, ‖X i‖ ≤ 1 / 512) (M' : ℝ)
    (hM' : ∀ i, ‖X i‖ ≤ M') : ‖meanV X‖ ≤ 2 * M' := by
  obtain ⟨hm, hms⟩ := meanV_spec hn hX
  exact norm_le_two_max hn X (1 / 512) hX hM512 M' hM' (by linarith) hms

/-- `‖V(X') - V(X)‖ ≤ 4 max_i ‖X'_i - X_i‖`, from `V = T_X(V)`, `V' = T_{X'}(V')`, the contraction of `T_X`,
and `‖T_{X'}(V') - T_X(V')‖ ≤ (1 + C_Ψ‖V'‖) max_i ‖X'_i - X_i‖`. -/
theorem meanV_lipschitz (hn : 0 < n) {X X' : Fin n → Mat} (hX : ∀ i, ‖X i‖ ≤ 1 / 512)
    (hX' : ∀ i, ‖X' i‖ ≤ 1 / 512) {d : ℝ} (hd : ∀ i, ‖X' i - X i‖ ≤ d) :
    ‖meanV X' - meanV X‖ ≤ 4 * d := by
  obtain ⟨hV, hVs⟩ := meanV_spec hn hX
  obtain ⟨hV', hV's⟩ := meanV_spec hn hX'
  set V := meanV X
  set V' := meanV X'
  have hfix := (sum_psi_eq_zero_iff hn X V).1 hVs
  have hfix' := (sum_psi_eq_zero_iff hn X' V').1 hV's
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd ⟨0, hn⟩)
  have hc := T_contract hn X (1 / 512) hX hM512 (Z := V') (Z' := V) (by linarith) (by linarith)
  have hterm : ∀ i, ‖(X' i + Phi (X' i) (-V')) - (X i + Phi (X i) (-V'))‖ ≤ 2 * d := fun i => by
    have h := Phi_lip_left (X := X i) (X' := X' i) (Y := -V') (by linarith [hX i])
      (by linarith [hX' i]) (by rw [norm_neg]; linarith)
    rw [norm_neg] at h
    have e : (X' i + Phi (X' i) (-V')) - (X i + Phi (X i) (-V')) =
        (X' i - X i) + (Phi (X' i) (-V') - Phi (X i) (-V')) := by abel
    rw [e]
    have h2 : 256 * ‖V'‖ * ‖X' i - X i‖ ≤ d := by
      have h3 := mul_le_mul_of_nonneg_left (hd i) (by positivity : (0 : ℝ) ≤ 256 * ‖V'‖)
      nlinarith
    linarith [norm_add_le (X' i - X i) (Phi (X' i) (-V') - Phi (X i) (-V')), hd i]
  have hT : ‖T X' V' - T X V'‖ ≤ 2 * d := by
    have e : T X' V' - T X V' =
        ((n : ℂ)⁻¹) • ∑ i, ((X' i + Phi (X' i) (-V')) - (X i + Phi (X i) (-V'))) := by
      rw [T, T, ← smul_sub, ← Finset.sum_sub_distrib]
    rw [e, norm_inv_smul hn]
    have hs := norm_sum_le Finset.univ
      fun i => ((X' i + Phi (X' i) (-V')) - (X i + Phi (X i) (-V')))
    have hs2 : ∑ i, ‖(X' i + Phi (X' i) (-V')) - (X i + Phi (X i) (-V'))‖ ≤
        ∑ _i : Fin n, 2 * d := Finset.sum_le_sum fun i _ => hterm i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc (n : ℝ)⁻¹ * ‖∑ i, ((X' i + Phi (X' i) (-V')) - (X i + Phi (X i) (-V')))‖
        ≤ (n : ℝ)⁻¹ * (n * (2 * d)) := by gcongr; exact hs.trans hs2
      _ = 2 * d := by field_simp
  have e : V' - V = (T X' V' - T X V') + (T X V' - T X V) := by rw [hfix, hfix']; abel
  have h := norm_add_le (T X' V' - T X V') (T X V' - T X V)
  rw [← e] at h
  linarith

/-! ### The mean of `def:group-mean` -/

/-- `def:group-mean`(i): the mean of `W_i = e^{iY_i}W₁` is `e^{iZ}W₁` with `Z = V(Y)`. -/
def mean (Y : Fin n → Mat) (W₁ : GLN) : GLN := expU (Complex.I • meanV Y) * W₁

lemma log_quot (A B : Mat) :
    LogM (((expU (Complex.I • A) * expU (Complex.I • -B) : GLN)) : Mat) = Complex.I • psi A (-B) := by
  rw [Units.val_mul, expU_val, expU_val, log_eq_I_psi]

lemma expU_I_neg (B : Mat) : expU (Complex.I • -B) = (expU (Complex.I • B))⁻¹ := by
  rw [smul_neg, expU_inv]

/-- `eq:group-mean` for the mean. -/
theorem mean_spec (hn : 0 < n) {Y : Fin n → Mat} (hY : ∀ i, ‖Y i‖ ≤ 1 / 512) (W₁ : GLN) :
    ∑ i, LogM (((expU (Complex.I • Y i) * W₁) * (mean Y W₁)⁻¹ : GLN) : Mat) = 0 := by
  have e : ∀ i, LogM (((expU (Complex.I • Y i) * W₁) * (mean Y W₁)⁻¹ : GLN) : Mat) =
      Complex.I • psi (Y i) (-meanV Y) := fun i => by rw [mean, quotient, log_quot]
  simp only [e]
  rw [← Finset.smul_sum, (meanV_spec hn hY).2, smul_zero]

/-- The uniqueness of `lem:group-mean` among `e^{iZ}W₁` with `‖Z‖ ≤ 1/256`. -/
theorem mean_unique (hn : 0 < n) {Y : Fin n → Mat} (hY : ∀ i, ‖Y i‖ ≤ 1 / 512) (W₁ : GLN) {Z : Mat}
    (hZ : ‖Z‖ ≤ 1 / 256)
    (h : ∑ i, LogM (((expU (Complex.I • Y i) * W₁) * (expU (Complex.I • Z) * W₁)⁻¹ : GLN) : Mat) = 0) :
    Z = meanV Y := by
  have e : ∀ i, LogM (((expU (Complex.I • Y i) * W₁) * (expU (Complex.I • Z) * W₁)⁻¹ : GLN) : Mat) =
      Complex.I • psi (Y i) (-Z) := fun i => by rw [quotient, log_quot]
  simp only [e] at h
  rw [← Finset.smul_sum, smul_eq_zero] at h
  exact meanV_unique hn hY hZ (h.resolve_left Complex.I_ne_zero)

/-- The last statement of `lem:group-mean`: for `W_i = e^{iX_i}`, `‖X_i‖ ≤ ϱ`, `2^{12}ϱ ≤ 1`, with the
exponents `Y_i = Ψ(X_i, -X_1)` of `W_iW_1⁻¹`, the mean is `e^{iV(X)}`, `‖V(X)‖ ≤ 2ϱ`, and
`Log 𝗆({e^{iX_i}}) = iV(X)`. -/
theorem mean_exp (hn : 0 < n) {X : Fin n → Mat} {ρ : ℝ} (hρ : 4096 * ρ ≤ 1)
    (hX : ∀ i, ‖X i‖ ≤ ρ) :
    (∀ i, expU (Complex.I • X i) =
      expU (Complex.I • psi (X i) (-X ⟨0, hn⟩)) * expU (Complex.I • X ⟨0, hn⟩)) ∧
    (∀ i, ‖psi (X i) (-X ⟨0, hn⟩)‖ ≤ 3 * ρ) ∧
    mean (fun i => psi (X i) (-X ⟨0, hn⟩)) (expU (Complex.I • X ⟨0, hn⟩)) =
      expU (Complex.I • meanV X) ∧
    ‖meanV X‖ ≤ 2 * ρ ∧
    LogM ((mean (fun i => psi (X i) (-X ⟨0, hn⟩)) (expU (Complex.I • X ⟨0, hn⟩)) : GLN) : Mat) =
      Complex.I • meanV X := by
  set X0 := X ⟨0, hn⟩
  set Y : Fin n → Mat := fun i => psi (X i) (-X0)
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hX ⟨0, hn⟩)
  have hl2 := log_two_gt_eighth
  have hX512 : ∀ i, ‖X i‖ ≤ 1 / 512 := fun i => by linarith [hX i]
  have hY3 : ∀ i, ‖Y i‖ ≤ 3 * ρ := fun i =>
    (expansion_bounds ρ hρ (hX i) (hX ⟨0, hn⟩) (Z := 0) (by simp [hρ0])).1
  -- `e^{iX_i} = e^{iY_i}e^{iX_1}`
  have hYe : ∀ i, expU (Complex.I • Y i) = expU (Complex.I • X i) * expU (Complex.I • -X0) :=
    fun i => Units.ext (by
      rw [Units.val_mul, expU_val, expU_val, expU_val]
      exact exp_I_psi (by rw [norm_neg]; linarith [hX i, hX ⟨0, hn⟩]))
  have h1 : ∀ i, expU (Complex.I • X i) = expU (Complex.I • Y i) * expU (Complex.I • X0) :=
    fun i => by rw [hYe, expU_I_neg]; group
  -- the solution for the `Y_i` and `V' = Ψ(Z, X_1)`
  have hY512 : ∀ i, ‖Y i‖ ≤ 1 / 512 := fun i => by linarith [hY3 i]
  set Z := meanV Y
  have hZ6 : ‖Z‖ ≤ 6 * ρ := by
    have := norm_meanV_le hn hY512 (3 * ρ) hY3; linarith
  obtain ⟨-, hV'8, hV'e⟩ := expansion_bounds ρ hρ (hX ⟨0, hn⟩) (hX ⟨0, hn⟩) hZ6
  set V' := psi Z X0
  have hV'U : expU (Complex.I • V') = expU (Complex.I • Z) * expU (Complex.I • X0) :=
    Units.ext (by rw [Units.val_mul, expU_val, expU_val, expU_val]; exact hV'e)
  have hsol : ∑ i, psi (X i) (-V') = 0 := by
    have hterm : ∀ i, Complex.I • psi (X i) (-V') = Complex.I • psi (Y i) (-Z) := fun i => by
      rw [← log_quot, ← log_quot, expU_I_neg, expU_I_neg, hV'U, h1 i]
      congr 2; group
    have hsum : Complex.I • ∑ i, psi (X i) (-V') = Complex.I • ∑ i, psi (Y i) (-Z) := by
      rw [Finset.smul_sum, Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => hterm i
    rw [(meanV_spec hn hY512).2] at hsum
    rw [smul_zero, smul_eq_zero] at hsum
    exact hsum.resolve_left Complex.I_ne_zero
  have hV'eq : V' = meanV X := meanV_unique hn hX512 (by linarith) hsol
  have hmean : mean Y (expU (Complex.I • X0)) = expU (Complex.I • meanV X) := by
    rw [mean, ← hV'U, hV'eq]
  have hV2 : ‖meanV X‖ ≤ 2 * ρ := norm_meanV_le hn hX512 ρ hX
  refine ⟨h1, hY3, hmean, hV2, ?_⟩
  rw [hmean, expU_val]
  exact LogM_exp (by rw [norm_I_smul']; linarith)

/-- `lem:moved-transports`(i) for the mean itself: for `‖X_i‖, ‖X'_i‖ ≤ ϱ/2`, `2^{11}ϱ ≤ 1`,
`‖(1/i) Log 𝗆({e^{iX'_i}}) - (1/i) Log 𝗆({e^{iX_i}})‖ ≤ 4 max_i ‖X'_i - X_i‖`. -/
theorem moved_transports_i_mean (hn : 0 < n) {X X' : Fin n → Mat} {ϱ : ℝ} (hϱ : 2048 * ϱ ≤ 1)
    (hX : ∀ i, ‖X i‖ ≤ ϱ / 2) (hX' : ∀ i, ‖X' i‖ ≤ ϱ / 2) {d : ℝ} (hd : ∀ i, ‖X' i - X i‖ ≤ d) :
    ‖(-Complex.I) • LogM ((mean (fun i => psi (X' i) (-X' ⟨0, hn⟩))
        (expU (Complex.I • X' ⟨0, hn⟩)) : GLN) : Mat) -
      (-Complex.I) • LogM ((mean (fun i => psi (X i) (-X ⟨0, hn⟩))
        (expU (Complex.I • X ⟨0, hn⟩)) : GLN) : Mat)‖ ≤ 4 * d := by
  have hρ : 4096 * (ϱ / 2) ≤ 1 := by linarith
  rw [(mean_exp hn hρ hX').2.2.2.2, (mean_exp hn hρ hX).2.2.2.2, smul_smul, smul_smul,
    neg_mul, Complex.I_mul_I, neg_neg, one_smul, one_smul]
  have hϱ0 : 0 ≤ ϱ := by linarith [norm_nonneg (X ⟨0, hn⟩), hX ⟨0, hn⟩]
  exact meanV_lipschitz hn (fun i => by linarith [hX i]) (fun i => by linarith [hX' i]) hd

/-! ### The moved holonomy of a path -/

/-- A step of a path: the value `V` of the configuration on the step (`𝐔(b)` forwards, `𝐔(b)⁻¹`
backwards), the value `A` of `aA` on its bond, and its direction. -/
structure Step (N : ℕ) where
  V : (Matrix (Fin N) (Fin N) ℂ)ˣ
  A : Matrix (Fin N) (Fin N) ℂ
  fwd : Bool

/-- The value of `e^{iaA}𝐔` on the step: `e^{iA}𝐔(b)` forwards, `(e^{iA}𝐔(b))⁻¹ = V e^{-iA}` backwards. -/
def Step.moved (s : Step N) : GLN :=
  if s.fwd then expU (Complex.I • s.A) * s.V else s.V * expU (-(Complex.I • s.A))

/-- The exponents `Y_k = ±Ad_{𝐔(γ_k)}A(b_k)` of the factors of `E_Γ`. -/
def movedExps : List (Step N) → List Mat
  | [] => []
  | s :: l => (if s.fwd then s.A else -Ad s.V s.A) :: (movedExps l).map (Ad s.V)

lemma length_movedExps (l : List (Step N)) : (movedExps l).length = l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => simp [movedExps, ih]

lemma moved_step (s : Step N) :
    s.moved = expU (Complex.I • (if s.fwd then s.A else -Ad s.V s.A)) * s.V := by
  unfold Step.moved
  cases s.fwd
  · have : expU (Complex.I • -Ad s.V s.A) = s.V * expU (-(Complex.I • s.A)) * s.V⁻¹ := by
      rw [expU_conj, Ad_neg, Ad_smul, smul_neg]
    simp only [Bool.false_eq_true, ↓reduceIte, this]
    group
  · rfl

/-- `(e^{iaA}𝐔)(Γ) = E_Γ𝐔(Γ)` with `E_Γ = Π_k e^{iY_k}`: moving the factors `e^{±iaA(b_k)}` to the left. -/
theorem moved_prod (l : List (Step N)) :
    (l.map Step.moved).prod =
      ((movedExps l).map fun B => expU (Complex.I • B)).prod * (l.map Step.V).prod := by
  induction l with
  | nil => simp [movedExps]
  | cons s l ih =>
    simp only [List.map_cons, List.prod_cons, movedExps, ih, moved_step]
    have hc : (((movedExps l).map (Ad s.V)).map fun B => expU (Complex.I • B)).prod =
        s.V * ((movedExps l).map fun B => expU (Complex.I • B)).prod * s.V⁻¹ := by
      calc (((movedExps l).map (Ad s.V)).map fun B => expU (Complex.I • B)).prod
          = (((movedExps l).map fun B => expU (Complex.I • B)).map (MulAut.conj s.V)).prod := by
            rw [List.map_map, List.map_map]
            congr 1
            refine List.map_congr_left fun B _ => ?_
            simp only [Function.comp_apply, MulAut.conj_apply, expU_conj, Ad_smul]
        _ = MulAut.conj s.V (((movedExps l).map fun B => expU (Complex.I • B)).prod) :=
            (map_list_prod _ _).symm
        _ = _ := MulAut.conj_apply _ _
    rw [hc]
    group

lemma mem_movedExps (l : List (Step N)) : ∀ B ∈ movedExps l, ∃ k ≤ l.length, ∃ s ∈ l,
    B = Ad ((l.take k).map Step.V).prod s.A ∨ B = -Ad ((l.take k).map Step.V).prod s.A := by
  induction l with
  | nil => simp [movedExps]
  | cons s l ih =>
    intro B hB
    simp only [movedExps, List.mem_cons, List.mem_map] at hB
    rcases hB with hB | ⟨B', hB', rfl⟩
    · cases h : s.fwd
      · rw [h] at hB
        refine ⟨1, by simp, s, List.mem_cons_self, Or.inr ?_⟩
        simpa using hB
      · rw [h] at hB
        refine ⟨0, by simp, s, List.mem_cons_self, Or.inl ?_⟩
        simpa using hB
    · obtain ⟨k, hk, s', hs', h⟩ := ih B' hB'
      refine ⟨k + 1, by simp only [List.length_cons]; omega, s', List.mem_cons_of_mem _ hs', ?_⟩
      simp only [List.take_succ_cons, List.map_cons, List.prod_cons, Ad_mul]
      rcases h with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h, Ad_neg])

/-- `‖Y_k‖ ≤ 2‖aA‖_∞` from `‖Ad_{𝐔(γ)}Z‖ ≤ 2‖Z‖` for the pieces `γ` of the path from its beginning. -/
theorem norm_movedExps_le (l : List (Step N)) {ε : ℝ} (hA : ∀ s ∈ l, ‖s.A‖ ≤ ε)
    (hAd : ∀ k ≤ l.length, ∀ Z : Mat, ‖Ad ((l.take k).map Step.V).prod Z‖ ≤ 2 * ‖Z‖) :
    ∀ B ∈ movedExps l, ‖B‖ ≤ 2 * ε := by
  intro B hB
  obtain ⟨k, hk, s, hs, h | h⟩ := mem_movedExps l B hB
  · rw [h]; exact (hAd k hk _).trans (by linarith [hA s hs])
  · rw [h, norm_neg]; exact (hAd k hk _).trans (by linarith [hA s hs])

lemma val_prod_expU (l : List Mat) :
    ((((l.map fun B => expU (Complex.I • B)).prod : GLN)) : Mat) =
      (l.map fun B => exp (Complex.I • B)).prod := by
  induction l with
  | nil => simp
  | cons B l ih => simp [ih]

/-- `lem:moved-transports`(ii) for the rule `m`. Paths `Γ` (index `Fin n`) are lists of steps with at
most `2L` steps, `‖aA‖ ≤ ε` on their bonds, and `‖Ad_{𝐔(γ)}Z‖ ≤ 2‖Z‖` for their pieces `γ` from `y`;
`𝐔(Γ) = e^{iX_Γ}𝐔_m` with `‖X_Γ‖ ≤ ϱ/4`, where `𝐔_m = 𝐔_m(y, x)` is the mean of the `𝐔(Γ)` (`eq:group-mean`).
Then the mean of the moved holonomies `(e^{iaA}𝐔)(Γ)` is `e^{iV}𝐔_m` (it satisfies `eq:group-mean`, and is
the only such `e^{iV'}𝐔_m` with `‖V'‖ ≤ 1/256`), `Log((e^{iaA}𝐔)_m𝐔_m⁻¹) = iV`, and
`‖V‖ ≤ 96Lε ≤ 2^{11}Lε`. -/
theorem moved_transports_ii_mean (hn : 0 < n) {L ε ϱ : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hϱ : 2048 * ϱ ≤ 1) (hsmall : 2 ^ 9 * L * ε ≤ ϱ) (paths : Fin n → List (Step N))
    (hlen : ∀ Γ, ((paths Γ).length : ℝ) ≤ 2 * L) (hA : ∀ Γ, ∀ s ∈ paths Γ, ‖s.A‖ ≤ ε)
    (hAd : ∀ Γ, ∀ k ≤ (paths Γ).length, ∀ Z : Mat,
      ‖Ad (((paths Γ).take k).map Step.V).prod Z‖ ≤ 2 * ‖Z‖)
    (Um : GLN) (X : Fin n → Mat) (hX : ∀ Γ, ‖X Γ‖ ≤ ϱ / 4)
    (hUΓ : ∀ Γ, ((paths Γ).map Step.V).prod = expU (Complex.I • X Γ) * Um)
    (hmean : ∑ Γ, LogM ((((paths Γ).map Step.V).prod * Um⁻¹ : GLN) : Mat) = 0) :
    ∃ V : Mat,
      (∑ Γ, LogM ((((paths Γ).map Step.moved).prod * (expU (Complex.I • V) * Um)⁻¹ : GLN) : Mat) = 0) ∧
      (∀ V' : Mat, ‖V'‖ ≤ 1 / 256 →
        ∑ Γ, LogM ((((paths Γ).map Step.moved).prod * (expU (Complex.I • V') * Um)⁻¹ : GLN) : Mat) = 0 →
          V' = V) ∧
      LogM (((expU (Complex.I • V) * Um) * Um⁻¹ : GLN) : Mat) = Complex.I • V ∧
      ‖V‖ ≤ 96 * L * ε ∧ 96 * L * ε ≤ 2 ^ 11 * L * ε := by
  have hLε : 0 ≤ L * ε := mul_nonneg hL hε
  have hϱ0 : 0 ≤ ϱ := by nlinarith
  have hl2 := log_two_gt_eighth
  have hX512 : ∀ Γ, ‖X Γ‖ ≤ 1 / 512 := fun Γ => by linarith [hX Γ]
  -- `𝐔_m` is the mean: `Σ_Γ X_Γ = 0`, hence `V(X) = 0`
  have hsumX : ∑ Γ, X Γ = 0 := by
    have e : ∀ Γ, LogM ((((paths Γ).map Step.V).prod * Um⁻¹ : GLN) : Mat) = Complex.I • X Γ :=
      fun Γ => by
        rw [hUΓ, mul_inv_cancel_right, expU_val]
        exact LogM_exp (by rw [norm_I_smul']; linarith [hX Γ])
    simp only [e] at hmean
    rw [← Finset.smul_sum, smul_eq_zero] at hmean
    exact hmean.resolve_left Complex.I_ne_zero
  have hV0 : meanV X = 0 := by
    refine (meanV_unique hn hX512 (by simp) ?_).symm
    have e : ∑ Γ, psi (X Γ) (-0) = ∑ Γ, X Γ := Finset.sum_congr rfl fun Γ _ => by
      rw [neg_zero]; exact psi_zero_right (by linarith [hX Γ])
    rw [e, hsumX]
  -- the exponents of the moved holonomies
  obtain ⟨Z, X', hZ, hX'⟩ := moved_exponents hL hε (by linarith) hsmall (fun Γ => movedExps (paths Γ))
    (fun Γ => by rw [length_movedExps]; exact hlen Γ)
    (fun Γ => norm_movedExps_le (paths Γ) (hA Γ) (hAd Γ)) X hX
  have hmoved : ∀ Γ, ((paths Γ).map Step.moved).prod = expU (Complex.I • X' Γ) * Um := fun Γ => by
    have hE : ((movedExps (paths Γ)).map fun B => expU (Complex.I • B)).prod =
        expU (Complex.I • Z Γ) := Units.ext (by rw [val_prod_expU, expU_val]; exact (hZ Γ).1.symm)
    have hX'e : expU (Complex.I • X' Γ) = expU (Complex.I • Z Γ) * expU (Complex.I • X Γ) :=
      Units.ext (by rw [Units.val_mul, expU_val, expU_val, expU_val]; exact (hX' Γ).1)
    rw [moved_prod, hE, hUΓ, hX'e, mul_assoc]
  have hX'512 : ∀ Γ, ‖X' Γ‖ ≤ 1 / 512 := fun Γ => by linarith [(hX' Γ).2.2]
  have hterm : ∀ V' : Mat, ∀ Γ,
      LogM ((((paths Γ).map Step.moved).prod * (expU (Complex.I • V') * Um)⁻¹ : GLN) : Mat) =
        Complex.I • psi (X' Γ) (-V') := fun V' Γ => by
    rw [hmoved, quotient, log_quot]
  obtain ⟨hVn, hVs⟩ := meanV_spec hn hX'512
  refine ⟨meanV X', ?_, fun V' hV' h => ?_, ?_, ?_, by nlinarith⟩
  · simp only [hterm]
    rw [← Finset.smul_sum, hVs, smul_zero]
  · simp only [hterm] at h
    rw [← Finset.smul_sum, smul_eq_zero] at h
    exact meanV_unique hn hX'512 hV' (h.resolve_left Complex.I_ne_zero)
  · rw [mul_inv_cancel_right, expU_val]
    exact LogM_exp (by rw [norm_I_smul']; linarith)
  · have h := meanV_lipschitz hn hX512 hX'512 (fun Γ => (hX' Γ).2.1)
    rw [hV0, sub_zero] at h
    linarith

/-! ### The inputs of `lem:axial-smallness` -/

namespace GaugeGroup'

variable (G : GaugeGroup N)

/-- `U([c]) = e^{-iβ_c(U)}M(U)(c)` (`def:average`) with `e^{-iβ_c} ∈ G` and
`‖e^{-iβ_c} - 1‖ ≤ ‖β_c‖ ≤ 7√NL²α` (`lem:average`(v) from the loop bound, `lem:chart`(iii)). -/
theorem avg_path_factor (hG : IsClosed G.mats) {ι : Type*} [Fintype ι] {P P' : ι → Type*}
    [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)] :
    ∃ rG : ℝ, 0 < rG ∧ ∀ (g : ∀ x, P x → GLN) (h : ι → GLN) (g' : ∀ x, P' x → GLN) (k : GLN)
      (L α : ℝ), 0 ≤ α → α ≤ rG / (8 * Real.sqrt N * L ^ 2) →
      7 * Real.sqrt N * L ^ 2 * α ≤ Real.pi →
      (∀ x Γ Γ', Average.loop g h g' k x Γ Γ' ∈ G.carrier) →
      (∀ x Γ Γ', ‖((Average.loop g h g' k x Γ Γ' : GLN) : Mat) - 1‖ ≤ 4 * Real.sqrt N * L ^ 2 * α) →
      ∃ E : GLN, E ∈ G.carrier ∧
        k = E * Average.avg G.inChart G.chartLog g h g' k ∧
        ‖(E : Mat) - 1‖ ≤ 7 * Real.sqrt N * L ^ 2 * α := by
  obtain ⟨rG, hr0, -, hdom⟩ := GaugeGroup.average_domain_constants (G := G) (P := P) (P' := P') hG
  refine ⟨rG, hr0, fun g h g' k L α hα0 hα hπ hcar hle => ?_⟩
  obtain ⟨hin, -, hβ⟩ := hdom g h g' k L α hα0 hα hcar hle
  set β := Average.beta G.chartLog g h g' k
  have hβG : β ∈ G.lie := GaugeGroup.beta_mem_lie (G := G) hG g h g' k hin
  have havg : Average.avg G.inChart G.chartLog g h g' k = expU (Complex.I • β) * k := by
    unfold Average.avg
    exact ite_eq_left_of_eq_true _ _ (eq_true hin)
  refine ⟨expU (Complex.I • -β), ?_, ?_, ?_⟩
  · have := hβG.2 (-1)
    convert this using 2
    push_cast
    rw [mul_neg_one, neg_smul, smul_neg]
  · rw [havg, expU_I_neg]; group
  · rw [expU_val]
    have hH : (-β).IsHermitian := Matrix.IsHermitian.neg hβG.1
    have := (ChartBounds.chart_iii hH (by rw [norm_neg]; linarith)).1
    rw [norm_neg] at this
    linarith

/-- The bound of `eq:axial-path-transport` for the rule `m`: for elements `W(Γ)` of `G` with
`‖W(Γ)W(Γ_x)⁻¹ - 1‖ ≤ b ≤ r_G`, `W(Γ) = e^{iY_Γ}W(Γ_x)` with `Y_Γ ∈ 𝔤`, `‖Y_Γ‖ ≤ (π/2)b`
(`lem:chart`(ii)–(iii)), and the mean `W_m = e^{iZ}W(Γ_x)` (`def:group-mean` with the reference `W(Γ_x)`)
satisfies `eq:group-mean` and `‖W_m - W(Γ_x)‖ ≤ 2πb`. With `b = (3/2)√Nα₀`, `2πb ≤ 10√Nα₀`. -/
theorem kappa_bound (hG : IsClosed G.mats) :
    ∃ r : ℝ, 0 < r ∧ ∀ {n : ℕ} (_hn : 0 < n) (W : Fin n → GLN) (x : Fin n),
      (∀ Γ, W Γ ∈ G.carrier) → ∀ b : ℝ, b ≤ r → 512 * (Real.pi / 2 * b) ≤ 1 →
      (∀ Γ, ‖((W Γ * (W x)⁻¹ : GLN) : Mat) - 1‖ ≤ b) →
      ∃ Y : Fin n → Mat,
        (∀ Γ, W Γ = expU (Complex.I • Y Γ) * W x ∧ Y Γ ∈ G.lie ∧ ‖Y Γ‖ ≤ Real.pi / 2 * b) ∧
        (∑ Γ, LogM ((W Γ * (mean Y (W x))⁻¹ : GLN) : Mat) = 0) ∧
        ‖((mean Y (W x) : GLN) : Mat) - W x‖ ≤ 2 * Real.pi * b := by
  obtain ⟨r, hr0, -, hchart⟩ := GaugeGroup.chart_ii (G := G) hG
  refine ⟨r, hr0, fun {n} hn W x hW b hbr hb512 hd => ?_⟩
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hd ⟨0, hn⟩)
  have hU : ∀ Γ, W Γ * (W x)⁻¹ ∈ G.carrier := fun Γ =>
    G.carrier.mul_mem (hW Γ) (G.carrier.inv_mem (hW x))
  have hex : ∀ Γ, ∃ A ∈ G.lie, ‖A‖ < Real.pi ∧
      exp (Complex.I • A) = ((W Γ * (W x)⁻¹ : GLN) : Mat) := fun Γ => by
    obtain ⟨A, hA, hAn, hAe, -⟩ := hchart _ (hU Γ) ((hd Γ).trans hbr)
    exact ⟨A, hA, hAn, hAe⟩
  choose Y hYG hYn hYe using hex
  have hYb : ∀ Γ, ‖Y Γ‖ ≤ Real.pi / 2 * b := fun Γ => by
    have h := (ChartBounds.chart_iii (hYG Γ).1 (hYn Γ).le).2.1
    rw [hYe Γ] at h
    have := mul_le_mul_of_nonneg_left (hd Γ) (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    linarith
  have hWe : ∀ Γ, W Γ = expU (Complex.I • Y Γ) * W x := fun Γ => by
    have : expU (Complex.I • Y Γ) = W Γ * (W x)⁻¹ := Units.ext (by rw [expU_val]; exact hYe Γ)
    rw [this]; group
  have hY512 : ∀ Γ, ‖Y Γ‖ ≤ 1 / 512 := fun Γ => by linarith [hYb Γ]
  refine ⟨Y, fun Γ => ⟨hWe Γ, hYG Γ, hYb Γ⟩, ?_, ?_⟩
  · have h := mean_spec hn hY512 (W x)
    rw [← h]
    exact Finset.sum_congr rfl fun Γ _ => by rw [← hWe Γ]
  · set Z := meanV Y
    have hZ : ‖Z‖ ≤ Real.pi * b := by
      have := norm_meanV_le hn hY512 (Real.pi / 2 * b) hYb; linarith
    have hWx : ((W x : GLN) : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ := G.unitary _ (hW x)
    have e : ((mean Y (W x) : GLN) : Mat) - W x = (exp (Complex.I • Z) - 1) * W x := by
      rw [mean, Units.val_mul, expU_val, sub_mul, one_mul]
    rw [e, CStarRing.norm_mul_mem_unitary _ hWx]
    have hb := BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • Z)
    rw [norm_I_smul'] at hb
    have h2 := exp_sub_one_le_two_mul (norm_nonneg Z) hZ (by nlinarith [Real.pi_pos])
    linarith

end GaugeGroup'

end MeanTransports

end CoreLean

end
