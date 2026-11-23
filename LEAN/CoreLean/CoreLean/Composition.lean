/-
`lem:composition` of BALABAN_CORE.tex: the composition of block bounds.

Setting. The points `y ∈ 𝐁` form a finite type `β` with the scales `j(y)`, the spacings
`a_j = a₀Lʲ` with `L ≥ 1`, and a function `d ≥ 0` with `RM(|j(y) - j(y')| - 1) ≤ d(y, y')`
(`lem:distance`(ii)); `eq:summation` with the rate `αδ/2` enters as the hypothesis `hsum` (it is
`lem:summation` for `RM ≥ r₁(α/2, δ)`), with the constant `c₁ = c₁(α/2, δ)`.

Modelling. The operators are numbered from the right: `U_0` is applied first (the core's `𝒯_n`) and
`U_n` last (the core's `𝒯_1`); `U_m` maps the objects `V m` to `V (m+1)`, whose block norms are
`nrm m`. The block bound `(b, p, δ)` of `U_m` in `X_m` is used through its two inequalities
(`[U_m g]_y = 0` off `X_m`, and `eq:block-bound` on `X_m`); the locality of `U_m` is not used by the
proof. The core's `|p_i + ⋯ + p_n| ≤ S` for `2 ≤ i ≤ n` are the partial sums `|p_0 + ⋯ + p_m| ≤ S`,
`m < n`. The exponential of the chain distance is the chain weight `W` (the largest
`e^{-(1-α)δ(d(y, z_n) + ⋯ + d(z_1, y'))}` over the chains with `z_l ∈ X_l ∩ X_{l-1}`, `0` if there is
none); `W ≤ e^{-(1-α)δD}` for every lower bound `D` of the lengths of the chains, in particular for the
core's infimum `d_𝐗`.
-/
import CoreLean.ParameterWalks

open Finset

noncomputable section

namespace CoreLean

namespace Composition

/-- The data of the points of `𝐁` used by `lem:composition`. -/
structure Setting (β : Type*) where
  j : β → ℕ
  d : β → β → ℝ
  d_nonneg : ∀ y y', 0 ≤ d y y'
  L : ℝ
  one_le_L : 1 ≤ L
  a₀ : ℝ
  a₀_pos : 0 < a₀
  RM : ℝ
  RM_pos : 0 < RM
  layer : ∀ y y', RM * (|((j y : ℝ) - j y')| - 1) ≤ d y y'

variable {β : Type*} [Fintype β] [DecidableEq β] (B : Setting β)

namespace Setting

/-- The spacing `a_i = a₀Lⁱ`. -/
def a (i : ℕ) : ℝ := B.a₀ * B.L ^ i

lemma a_pos (i : ℕ) : 0 < B.a i :=
  mul_pos B.a₀_pos (pow_pos (lt_of_lt_of_le zero_lt_one B.one_le_L) i)

/-- The quotient of the spacings of two points: for `|s| ≤ S` and `2S log L ≤ αδRM`,
`a_{j(y')}^s ≤ L^S e^{αδ d(y, y')/2} a_{j(y)}^s`. -/
lemma zpow_a_le {α δ S : ℝ} (hS : 0 ≤ S) (hSL : 2 * S * Real.log B.L ≤ α * δ * B.RM)
    (y y' : β) {s : ℤ} (hs : |(s : ℝ)| ≤ S) :
    B.a (B.j y') ^ s ≤ B.L ^ S * Real.exp (α * δ / 2 * B.d y y') * B.a (B.j y) ^ s := by
  have hL0 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
  set m : ℤ := (B.j y' : ℤ) - B.j y
  -- `a_{j(y')} = a_{j(y)} L^m`
  have ha : B.a (B.j y') = B.a (B.j y) * B.L ^ m := by
    simp only [a, m]
    rw [mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hL0.ne']
    congr 2; ring
  rw [ha, mul_zpow, ← zpow_mul, mul_comm (B.L ^ S * _)]
  refine mul_le_mul_of_nonneg_left ?_ (zpow_pos (B.a_pos _) _).le
  rw [← Real.rpow_intCast]
  -- `|m| ≤ 1 + d/RM`
  have hm : |(m : ℝ)| ≤ 1 + B.d y y' / B.RM := by
    have hl := B.layer y y'
    have e : (m : ℝ) = (B.j y' : ℝ) - B.j y := by simp [m]
    rw [e, abs_sub_comm]
    have : |(B.j y : ℝ) - B.j y'| - 1 ≤ B.d y y' / B.RM := by
      rw [le_div_iff₀ B.RM_pos]; linarith
    linarith
  have hexp : ((m * s : ℤ) : ℝ) ≤ S * (1 + B.d y y' / B.RM) := by
    push_cast
    calc (m : ℝ) * s ≤ |(m : ℝ)| * |(s : ℝ)| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ (1 + B.d y y' / B.RM) * S :=
          mul_le_mul hm hs (abs_nonneg _)
            (add_nonneg zero_le_one (div_nonneg (B.d_nonneg y y') B.RM_pos.le))
      _ = S * (1 + B.d y y' / B.RM) := by ring
  calc B.L ^ ((m * s : ℤ) : ℝ) ≤ B.L ^ (S * (1 + B.d y y' / B.RM)) :=
        Real.rpow_le_rpow_of_exponent_le B.one_le_L hexp
    _ = B.L ^ S * Real.exp (Real.log B.L * (S * B.d y y' / B.RM)) := by
        rw [show S * (1 + B.d y y' / B.RM) = S + S * B.d y y' / B.RM by ring,
          Real.rpow_add hL0, Real.rpow_def_of_pos hL0 (S * B.d y y' / B.RM)]
    _ ≤ B.L ^ S * Real.exp (α * δ / 2 * B.d y y') := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg hL0.le _)
        have hlog : 0 ≤ Real.log B.L := Real.log_nonneg B.one_le_L
        have hd := B.d_nonneg y y'
        rw [show Real.log B.L * (S * B.d y y' / B.RM) =
          (S * Real.log B.L / B.RM) * B.d y y' by ring]
        refine mul_le_mul_of_nonneg_right ?_ hd
        rw [div_le_iff₀ B.RM_pos]; linarith

end Setting

/-- The chain weight: `W 0 y y' = e^{-(1-α)δ d(y, y')}` and
`W (m+1) y y' = max_{z ∈ X_{m+1} ∩ X_m} e^{-(1-α)δ d(y, z)} W m z y'` (`0` for no `z`). -/
def W (α δ : ℝ) (X : ℕ → Finset β) : ℕ → β → β → ℝ
  | 0, y, y' => Real.exp (-((1 - α) * δ) * B.d y y')
  | m + 1, y, y' => ⨆ z : {z // z ∈ X (m + 1) ∩ X m},
      Real.exp (-((1 - α) * δ) * B.d y z) * W α δ X m z y'

lemma W_nonneg {α δ : ℝ} (X : ℕ → Finset β) (m : ℕ) (y y' : β) : 0 ≤ W B α δ X m y y' := by
  induction m generalizing y with
  | zero => exact (Real.exp_pos _).le
  | succ m ih => exact Real.iSup_nonneg fun z => mul_nonneg (Real.exp_pos _).le (ih _)

lemma le_W_succ {α δ : ℝ} (X : ℕ → Finset β) (m : ℕ) (y y' : β) {z : β}
    (hz : z ∈ X (m + 1) ∩ X m) :
    Real.exp (-((1 - α) * δ) * B.d y z) * W B α δ X m z y' ≤ W B α δ X (m + 1) y y' := by
  simp only [W]
  exact le_ciSup (f := fun z : {z // z ∈ X (m + 1) ∩ X m} =>
    Real.exp (-((1 - α) * δ) * B.d y z) * W B α δ X m z y') (Set.finite_range _).bddAbove ⟨z, hz⟩

/-- The inductive bound. -/
theorem chain_bound {α δ S c₁ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hS : 0 ≤ S)
    (hSL : 2 * S * Real.log B.L ≤ α * δ * B.RM)
    (hsum : ∀ y, ∑ y', Real.exp (-(α / 2 * δ) * B.d y y') ≤ c₁)
    (X : ℕ → Finset β) (b : ℕ → ℝ) (hb : ∀ m, 0 ≤ b m) (p : ℕ → ℤ)
    (F : ℕ → β → ℝ) (hF : ∀ m y, 0 ≤ F m y)
    (hzero : ∀ m y, y ∉ X m → F (m + 1) y = 0)
    (hbd : ∀ m, ∀ y ∈ X m, F (m + 1) y ≤
      b m * B.a (B.j y) ^ p m * ∑ y' ∈ X m, Real.exp (-δ * B.d y y') * F m y')
    (n : ℕ) (hp : ∀ m < n, |((∑ l ∈ range (m + 1), p l : ℤ) : ℝ)| ≤ S) (y : β) :
    F (n + 1) y ≤ (c₁ * B.L ^ S) ^ n * (∏ l ∈ range (n + 1), b l) *
      B.a (B.j y) ^ (∑ l ∈ range (n + 1), p l) *
        ∑ y' ∈ X 0, W B α δ X n y y' * F 0 y' := by
  have hL0 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
  have hc₁ : 0 ≤ c₁ := (sum_nonneg fun _ _ => (Real.exp_pos _).le).trans (hsum y)
  have hRHS : ∀ k (y : β), 0 ≤ (c₁ * B.L ^ S) ^ k * (∏ l ∈ range (k + 1), b l) *
      B.a (B.j y) ^ (∑ l ∈ range (k + 1), p l) * ∑ y' ∈ X 0, W B α δ X k y y' * F 0 y' :=
    fun k y => mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hc₁
      (Real.rpow_nonneg hL0.le _)) _) (prod_nonneg fun l _ => hb l))
      (zpow_pos (B.a_pos _) _).le) (sum_nonneg fun y' _ => mul_nonneg (W_nonneg B X k y y') (hF 0 y'))
  induction n generalizing y with
  | zero =>
    by_cases hy : y ∈ X 0
    · have h0 := hbd 0 y hy
      simp only [pow_zero, one_mul, zero_add, range_one, prod_singleton, sum_singleton] at h0 ⊢
      refine h0.trans (mul_le_mul_of_nonneg_left (sum_le_sum fun y' _ => ?_)
        (mul_nonneg (hb 0) (zpow_pos (B.a_pos _) _).le))
      refine mul_le_mul_of_nonneg_right ?_ (hF 0 y')
      simp only [W]
      refine Real.exp_le_exp.mpr ?_
      have := B.d_nonneg y y'
      nlinarith [mul_nonneg (mul_nonneg hα.le hδ.le) this]
    · rw [hzero 0 y hy]; exact hRHS 0 y
  | succ m ih =>
    by_cases hy : y ∈ X (m + 1)
    · set s : ℤ := ∑ l ∈ range (m + 1), p l
      set K : ℝ := (c₁ * B.L ^ S) ^ m * ∏ l ∈ range (m + 1), b l
      set T : ℝ := ∑ y' ∈ X 0, W B α δ X (m + 1) y y' * F 0 y'
      have hK : 0 ≤ K := mul_nonneg (pow_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg hL0.le _)) _)
        (prod_nonneg fun l _ => hb l)
      have hT : 0 ≤ T := sum_nonneg fun y' _ => mul_nonneg (W_nonneg B X _ y y') (hF 0 y')
      have hs : |(s : ℝ)| ≤ S := hp m (Nat.lt_succ_self m)
      -- each term of the bound of `U_{m+1}`
      have hterm : ∀ z ∈ X (m + 1), Real.exp (-δ * B.d y z) * F (m + 1) z ≤
          Real.exp (-(α / 2 * δ) * B.d y z) * (K * B.L ^ S * B.a (B.j y) ^ s * T) := by
        intro z hz
        by_cases hzm : z ∈ X m
        · have h1 := ih (fun k hk => hp k (Nat.lt_succ_of_lt hk)) z
          have h2 := B.zpow_a_le hS hSL y z hs
          have hd := B.d_nonneg y z
          -- the weights along the chain
          have hW : Real.exp (-((1 - α) * δ) * B.d y z) *
              ∑ y' ∈ X 0, W B α δ X m z y' * F 0 y' ≤ T := by
            rw [mul_sum]
            refine sum_le_sum fun y' _ => ?_
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_W_succ B X m y y' (mem_inter.mpr ⟨hz, hzm⟩))
              (hF 0 y')
          have hsplit : Real.exp (-δ * B.d y z) * Real.exp (α * δ / 2 * B.d y z) =
              Real.exp (-(α / 2 * δ) * B.d y z) * Real.exp (-((1 - α) * δ) * B.d y z) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          have hS0 : ∑ y' ∈ X 0, W B α δ X m z y' * F 0 y' ≥ 0 :=
            sum_nonneg fun y' _ => mul_nonneg (W_nonneg B X _ z y') (hF 0 y')
          calc Real.exp (-δ * B.d y z) * F (m + 1) z
              ≤ Real.exp (-δ * B.d y z) * (K * B.a (B.j z) ^ s *
                  ∑ y' ∈ X 0, W B α δ X m z y' * F 0 y') :=
                mul_le_mul_of_nonneg_left (by simpa [K, s, mul_assoc] using h1) (Real.exp_pos _).le
            _ ≤ Real.exp (-δ * B.d y z) * (K * (B.L ^ S * Real.exp (α * δ / 2 * B.d y z) *
                  B.a (B.j y) ^ s) * ∑ y' ∈ X 0, W B α δ X m z y' * F 0 y') := by
                gcongr
            _ = Real.exp (-(α / 2 * δ) * B.d y z) * (K * B.L ^ S * B.a (B.j y) ^ s *
                  (Real.exp (-((1 - α) * δ) * B.d y z) *
                    ∑ y' ∈ X 0, W B α δ X m z y' * F 0 y')) := by
                linear_combination (K * B.L ^ S * B.a (B.j y) ^ s *
                  ∑ y' ∈ X 0, W B α δ X m z y' * F 0 y') * hsplit
            _ ≤ Real.exp (-(α / 2 * δ) * B.d y z) * (K * B.L ^ S * B.a (B.j y) ^ s * T) := by
                gcongr
                exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hL0.le _))
                  (zpow_pos (B.a_pos _) _).le
        · rw [hzero m z hzm, mul_zero]
          exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg (mul_nonneg hK
            (Real.rpow_nonneg hL0.le _)) (zpow_pos (B.a_pos _) _).le) hT)
      have hsumX : ∑ z ∈ X (m + 1), Real.exp (-(α / 2 * δ) * B.d y z) ≤ c₁ :=
        (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => (Real.exp_pos _).le).trans
          (hsum y)
      have hP : 0 ≤ K * B.L ^ S * B.a (B.j y) ^ s * T :=
        mul_nonneg (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hL0.le _))
          (zpow_pos (B.a_pos _) _).le) hT
      calc F (m + 1 + 1) y
          ≤ b (m + 1) * B.a (B.j y) ^ p (m + 1) *
              ∑ z ∈ X (m + 1), Real.exp (-δ * B.d y z) * F (m + 1) z := hbd (m + 1) y hy
        _ ≤ b (m + 1) * B.a (B.j y) ^ p (m + 1) *
              ∑ z ∈ X (m + 1), Real.exp (-(α / 2 * δ) * B.d y z) *
                (K * B.L ^ S * B.a (B.j y) ^ s * T) :=
            mul_le_mul_of_nonneg_left (sum_le_sum hterm)
              (mul_nonneg (hb _) (zpow_pos (B.a_pos _) _).le)
        _ = b (m + 1) * B.a (B.j y) ^ p (m + 1) *
              ((∑ z ∈ X (m + 1), Real.exp (-(α / 2 * δ) * B.d y z)) *
                (K * B.L ^ S * B.a (B.j y) ^ s * T)) := by rw [sum_mul]
        _ ≤ b (m + 1) * B.a (B.j y) ^ p (m + 1) * (c₁ * (K * B.L ^ S * B.a (B.j y) ^ s * T)) := by
            gcongr
            exact mul_nonneg (hb _) (zpow_pos (B.a_pos _) _).le
        _ = (c₁ * B.L ^ S) ^ (m + 1) * (∏ l ∈ range (m + 1 + 1), b l) *
              B.a (B.j y) ^ (∑ l ∈ range (m + 1 + 1), p l) * T := by
            rw [prod_range_succ, sum_range_succ, zpow_add₀ (B.a_pos _).ne', pow_succ]
            simp only [K, s]
            ring
    · rw [hzero (m + 1) y hy]; exact hRHS (m + 1) y

/-! ### The chain distance -/

/-- The points of a chain from `y` to `y'`: `y' = z_0, z_1, …, z_m, z_{m+1} = y`. -/
def ext (y y' : β) (z : ℕ → β) (m l : ℕ) : β := if l = 0 then y' else if l = m + 1 then y else z l

/-- The length `d(y, z_m) + d(z_m, z_{m-1}) + ⋯ + d(z_1, y')` of a chain. -/
def chainLen (y y' : β) (z : ℕ → β) (m : ℕ) : ℝ :=
  ∑ l ∈ range (m + 1), B.d (ext y y' z m (l + 1)) (ext y y' z m l)

/-- A chain is admissible if `z_l ∈ X_l ∩ X_{l-1}` for `1 ≤ l ≤ m`. -/
def Admissible (X : ℕ → Finset β) (z : ℕ → β) (m : ℕ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ m → z l ∈ X l ∩ X (l - 1)

lemma chainLen_succ (y y' z₀ : β) (z : ℕ → β) (m : ℕ) :
    chainLen B y y' (Function.update z (m + 1) z₀) (m + 1) = B.d y z₀ + chainLen B z₀ y' z m := by
  unfold chainLen
  rw [sum_range_succ, add_comm]
  congr 1
  · simp [ext]
  · refine sum_congr rfl fun l hl => ?_
    rw [mem_range] at hl
    have e : ∀ i, i ≤ m + 1 → ext y y' (Function.update z (m + 1) z₀) (m + 1) i = ext z₀ y' z m i := by
      intro i hi
      unfold ext
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases h1 : i = m + 1
        · subst h1; simp
        · have : i ≠ m + 1 + 1 := by omega
          simp [h0, h1, this, Function.update_of_ne h1]
    rw [e (l + 1) (by omega), e l (by omega)]

/-- `W ≤ e^{-(1-α)δD}` for every lower bound `D` of the lengths of the admissible chains. -/
theorem W_le_exp {α δ : ℝ} (hα : α < 1) (hδ : 0 < δ) (X : ℕ → Finset β) (m : ℕ) (y y' : β)
    (D : ℝ) (hD : ∀ z, Admissible X z m → D ≤ chainLen B y y' z m) :
    W B α δ X m y y' ≤ Real.exp (-((1 - α) * δ) * D) := by
  have hc : 0 ≤ (1 - α) * δ := mul_nonneg (by linarith) hδ.le
  induction m generalizing y D with
  | zero =>
    simp only [W]
    refine Real.exp_le_exp.mpr ?_
    have := hD (fun _ => y) (fun l h1 h2 => by omega)
    simp [chainLen, ext] at this
    nlinarith
  | succ m ih =>
    simp only [W]
    refine Real.iSup_le (fun ⟨z₀, hz₀⟩ => ?_) (Real.exp_pos _).le
    -- the chains of length `m` from `z₀` extend to chains of length `m + 1` from `y`
    have hD' : ∀ z, Admissible X z m → D - B.d y z₀ ≤ chainLen B z₀ y' z m := by
      intro z hz
      have hadm : Admissible X (Function.update z (m + 1) z₀) (m + 1) := by
        intro l h1 h2
        by_cases hl : l = m + 1
        · subst hl; simpa using hz₀
        · rw [Function.update_of_ne hl]; exact hz l h1 (by omega)
      have := hD _ hadm
      rw [chainLen_succ] at this
      linarith
    have := ih z₀ (D - B.d y z₀) hD'
    calc Real.exp (-((1 - α) * δ) * B.d y z₀) * W B α δ X m z₀ y'
        ≤ Real.exp (-((1 - α) * δ) * B.d y z₀) * Real.exp (-((1 - α) * δ) * (D - B.d y z₀)) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = Real.exp (-((1 - α) * δ) * D) := by rw [← Real.exp_add]; congr 1; ring

/-! ### `lem:composition` -/

/-- `lem:composition`, `eq:composition`: operators `U_0, …, U_n` (applied in this order) with the
block bounds `(b_m, p_m, δ)` in `X_m` satisfy, for every `f`, every `y ∈ X_n`, and every lower bound
`D` of the lengths of the admissible chains from `y` (in particular the infimum `d_𝐗(y, y')`),
`[U_n ⋯ U_0 f]_y ≤ (c₁L^S)^n (Π b_m) a_{j(y)}^{p_0 + ⋯ + p_n} Σ_{y' ∈ X_0} e^{-(1-α)δ D(y, y')} [f]_{y'}`. -/
theorem composition {α δ S c₁ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hδ : 0 < δ) (hS : 0 ≤ S)
    (hSL : 2 * S * Real.log B.L ≤ α * δ * B.RM)
    (hsum : ∀ y, ∑ y', Real.exp (-(α / 2 * δ) * B.d y y') ≤ c₁)
    (V : ℕ → Type*) (nrm : ∀ m, V m → β → ℝ) (hnrm : ∀ m g y, 0 ≤ nrm m g y)
    (U : ∀ m, V m → V (m + 1)) (X : ℕ → Finset β) (b : ℕ → ℝ) (hb : ∀ m, 0 ≤ b m) (p : ℕ → ℤ)
    (hzero : ∀ m g y, y ∉ X m → nrm (m + 1) (U m g) y = 0)
    (hbd : ∀ m g, ∀ y ∈ X m, nrm (m + 1) (U m g) y ≤
      b m * B.a (B.j y) ^ p m * ∑ y' ∈ X m, Real.exp (-δ * B.d y y') * nrm m g y')
    (n : ℕ) (hp : ∀ m < n, |((∑ l ∈ range (m + 1), p l : ℤ) : ℝ)| ≤ S)
    (comp : ∀ m, V 0 → V m) (hcomp0 : ∀ f, comp 0 f = f)
    (hcomp : ∀ m f, comp (m + 1) f = U m (comp m f))
    (f : V 0) (y : β) (D : β → β → ℝ)
    (hD : ∀ y' z, Admissible X z n → D y y' ≤ chainLen B y y' z n) :
    nrm (n + 1) (comp (n + 1) f) y ≤ (c₁ * B.L ^ S) ^ n * (∏ l ∈ range (n + 1), b l) *
      B.a (B.j y) ^ (∑ l ∈ range (n + 1), p l) *
        ∑ y' ∈ X 0, Real.exp (-((1 - α) * δ) * D y y') * nrm 0 f y' := by
  set F : ℕ → β → ℝ := fun m => nrm m (comp m f)
  have h := chain_bound B hα hδ hS hSL hsum X b hb p F (fun m y => hnrm m _ y)
    (fun m y hy => by simp only [F, hcomp]; exact hzero m _ y hy)
    (fun m y hy => by simp only [F, hcomp]; exact hbd m _ y hy) n hp y
  have hL0 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
  have hc₁ : 0 ≤ c₁ := (sum_nonneg fun _ _ => (Real.exp_pos _).le).trans (hsum y)
  refine h.trans ?_
  simp only [F, hcomp0]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun y' _ => ?_) (mul_nonneg (mul_nonneg
    (pow_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg hL0.le _)) _) (prod_nonneg fun l _ => hb l))
    (zpow_pos (B.a_pos _) _).le)
  exact mul_le_mul_of_nonneg_right (W_le_exp B hα1 hδ X n y y' (D y y') (hD y')) (hnrm 0 f y')

end Composition

end CoreLean
