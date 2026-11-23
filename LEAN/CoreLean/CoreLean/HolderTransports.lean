/-
`lem:holder-transports` of BALABAN_CORE.tex (`b1ff7d2601a1`), on the lattice model of `Transports.lean`
(fine lattice, `η = 1`, `a_j = Lʲ`, so that the core's `|x - x'|₁` with `a_k = 1` is `d₁(x, x')/a_k`).

The Hölder norm `‖f‖^U_β` of `eq:holder` at the scale `k`, formed with the transports of the gauge
field `U`, enters through the inequalities it stands for (`HolderU f U β H`: every pair `x ≠ x'` with
`d₁(x, x') ≤ a_k` and every shortest path `γ` from `x` to `x'` satisfy
`‖Ad_{U(γ)} f(x') - f(x)‖ ≤ (d₁(x, x')/a_k)^β H`).

* (i) `sup_le`: if `f(x) = 0` and `γ` is a shortest path from `x` to `x' ≠ x` with `d₁(x, x') ≤ a_j`,
  then `‖f(x')‖ ≤ (a_j/a_k)^β H`. In the core the site `x` is found by moving from `x' ∈ Δ̃(y)` parallel to
  `e₁` out of `Δ̃(y)`; that construction is not formalised.
* (ii) `holder_transports_ii`: `eq:holder-transports`, from `eq:transport-comparison` (`transports_near`)
  and (i).
* (iii) `holder_transports_iii`: for `0 < ε ≤ 1` the transported differences formed with `𝐔` and with
  `U`, divided by `(d₁/a_j)^ε`, differ by at most `12Lα₁‖f‖_∞` at every pair which contributes.
-/
import CoreLean.DivergenceConversion

open scoped Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace CoreLean
namespace Transports

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

variable (S : Blocks.DomSeq n)

/-- The Hölder bound `‖f‖^U_β ≤ H` at the scale `k`, with the transports of `U`. -/
def HolderU (f : Site n → Mat) (U : Config N n) (β H : ℝ) : Prop :=
  ∀ x x' (γ : List (Bond n)), x ≠ x' → Blocks.d1 x x' ≤ S.L ^ S.k → IsShortest x x' γ →
    ‖Ad (U.hol γ) (f x') - f x‖ ≤ ((Blocks.d1 x x' : ℝ) / (S.L : ℝ) ^ S.k) ^ β * H

lemma eq_of_d1_eq_zero {x x' : Site n} (h : Blocks.d1 x x' = 0) : x = x' := by
  funext ν
  have hν : Blocks.cd (x ν - x' ν) = 0 :=
    Nat.eq_zero_of_le_zero ((Blocks.cd_le_d1 x x' ν).trans h.le)
  unfold Blocks.cd at hν
  rw [Int.natAbs_eq_zero, ZMod.valMinAbs_eq_zero] at hν
  exact sub_eq_zero.mp hν

/-- The end of a nonempty path is the end of one of its bonds. -/
lemma pend_mem {s : Site n} {γ : List (Bond n)} (hγ : IsPath s γ) (hne : γ ≠ []) :
    ∃ b ∈ γ, pend s γ = b.plus := by
  induction γ generalizing s with
  | nil => exact absurd rfl hne
  | cons b γ ih =>
    rcases γ with _ | ⟨b', γ'⟩
    · exact ⟨b, by simp, by simp [pend]⟩
    · obtain ⟨-, hγ'⟩ := hγ
      obtain ⟨c, hc, hce⟩ := ih hγ' (by simp)
      exact ⟨c, List.mem_cons_of_mem _ hc, by simp only [pend] at hce ⊢; exact hce⟩

/-- `lem:holder-transports`(i): `‖f(x')‖ ≤ (a_j/a_k)^β‖f‖^U_β` at a site `x'` which a shortest path of
the length at most `a_j` joins to a zero `x` of `f`. -/
theorem sup_le {f : Site n → Mat} {U : Config N n} {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hhol : HolderU S f U β H) {j : ℕ} (hj : j ≤ S.k) {x x' : Site n} {γ : List (Bond n)}
    (hxx : x ≠ x') (hγ : IsShortest x x' γ) (hlen : Blocks.d1 x x' ≤ S.L ^ j) (hf : f x = 0)
    (hU : ∀ μ x, ((U μ x : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Mat) ∈ unitaryGroup (Fin N) ℂ) :
    ‖f x'‖ ≤ ((S.L : ℝ) ^ j / (S.L : ℝ) ^ S.k) ^ β * H := by
  have hL := L_pos' S
  have hLk : S.L ^ j ≤ S.L ^ S.k := Nat.pow_le_pow_right (by have := S.three_le_L; omega) hj
  have h := hhol x x' γ hxx (hlen.trans hLk) hγ
  rw [hf, sub_zero, (normLike_opNorm).ad_unitary _ (hol_unitary U hU γ)] at h
  refine h.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) ?_ hβ) hH)
  gcongr
  exact_mod_cast hlen

/-- `(ℓ/a_i)(a_j/a_k)^β ≤ (ℓ/a_k)^β(a_j/a_i)^β` for `0 < ℓ ≤ a_i`, `0 ≤ β ≤ 1`. -/
lemma ratio_le (l ai aj ak β : ℝ) (hl : 0 < l) (hli : l ≤ ai) (haj : 0 < aj) (hak : 0 < ak)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    l / ai * (aj / ak) ^ β ≤ (l / ak) ^ β * (aj / ai) ^ β := by
  have hai : 0 < ai := lt_of_lt_of_le hl hli
  have h1 : l / ai ≤ (l / ai) ^ β := by
    have hx0 : 0 < l / ai := div_pos hl hai
    have hx1 : l / ai ≤ 1 := (div_le_one hai).mpr hli
    calc l / ai = (l / ai) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (l / ai) ^ β := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hβ1
  have e : (l / ai) ^ β * (aj / ak) ^ β = (l / ak) ^ β * (aj / ai) ^ β := by
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; field_simp
  calc l / ai * (aj / ak) ^ β ≤ (l / ai) ^ β * (aj / ak) ^ β :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := e

/-- `lem:holder-transports`(ii), `eq:holder-transports`. -/
theorem holder_transports_ii (hRM : 3 * (S.L : ℝ) ≤ S.RM) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Mat) ∈ unitaryGroup (Fin N) ℂ) {α₁ : ℝ}
    (hα : 32 * S.L * α₁ ≤ 1) (hreg : RegA S A' α₁) {f : Site n → Mat} {β H : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hH : 0 ≤ H) (hhol : HolderU S f U β H) {j : ℕ} (hj : j ≤ S.k)
    (hsup : ∀ z, ‖f z‖ ≤ ((S.L : ℝ) ^ j / (S.L : ℝ) ^ S.k) ^ β * H)
    {i : ℕ} (hi : i ≤ S.k) {x x' : Site n} {γ : List (Bond n)} (hxx : x ≠ x')
    (hγ : IsShortest x x' γ) (hlen : Blocks.d1 x x' ≤ S.L ^ i) {z : Site n} (hz : z ∈ S.Ω i)
    (hnear : Blocks.dinf x z ≤ S.L ^ i ∨ Blocks.dinf x' z ≤ S.L ^ i) :
    ‖Ad ((expMul 1 A' U).hol γ) (f x') - f x‖ ≤
      (1 + 12 * S.L * α₁ * ((S.L : ℝ) ^ j / (S.L : ℝ) ^ i) ^ β) *
        ((Blocks.d1 x x' : ℝ) / (S.L : ℝ) ^ S.k) ^ β * H := by
  have hL := L_pos' S
  have hα0 := alpha_nonneg S hreg
  obtain ⟨hpath, hend, hglen⟩ := hγ
  have hne : γ ≠ [] := by
    rintro rfl; exact hxx (by simpa [pend] using hend)
  have hLi : S.L ^ i ≤ S.L ^ S.k := Nat.pow_le_pow_right (by have := S.three_le_L; omega) hi
  -- the comparison of the transports
  have hp : ∃ p, (p = x ∨ ∃ b ∈ γ, p = b.site ∨ p = b.plus) ∧ Blocks.dinf p z ≤ S.L ^ i := by
    rcases hnear with h | h
    · exact ⟨x, Or.inl rfl, h⟩
    · obtain ⟨b, hb, hbe⟩ := pend_mem hpath hne
      exact ⟨x', Or.inr ⟨b, hb, Or.inr (hend ▸ hbe)⟩, h⟩
  obtain ⟨p, hp1, hp2⟩ := hp
  have hcmp := (transports_near S normLike_opNorm hRM A' U hU hα hreg hi hpath
    (by rw [hglen]; exact hlen) hp1 hz hp2 (f x')).2
  have hfirst := hhol x x' γ hxx (hlen.trans hLi) ⟨hpath, hend, hglen⟩
  set l : ℝ := (Blocks.d1 x x' : ℝ)
  have hl0 : 0 < l := by
    have : Blocks.d1 x x' ≠ 0 := fun h0 => hxx (eq_of_d1_eq_zero h0)
    simp only [l]; exact_mod_cast Nat.pos_of_ne_zero this
  have hli : l ≤ (S.L : ℝ) ^ i := by simp only [l]; exact_mod_cast hlen
  rw [hglen] at hcmp
  have hratio := ratio_le l ((S.L : ℝ) ^ i) ((S.L : ℝ) ^ j) ((S.L : ℝ) ^ S.k) β hl0 hli
    (by positivity) (by positivity) hβ0 hβ1
  have hsec : ‖Ad ((expMul 1 A' U).hol γ) (f x') - Ad (U.hol γ) (f x')‖ ≤
      12 * S.L * α₁ * (((S.L : ℝ) ^ j / (S.L : ℝ) ^ i) ^ β * (l / (S.L : ℝ) ^ S.k) ^ β) * H := by
    refine hcmp.trans ?_
    have h12 : 0 ≤ 12 * (S.L : ℝ) * α₁ := by positivity
    calc 12 * (S.L : ℝ) * α₁ * (l / (S.L : ℝ) ^ i) * ‖f x'‖
        ≤ 12 * S.L * α₁ * (l / (S.L : ℝ) ^ i) * (((S.L : ℝ) ^ j / (S.L : ℝ) ^ S.k) ^ β * H) := by
          gcongr; exact hsup x'
      _ = 12 * S.L * α₁ * (l / (S.L : ℝ) ^ i * ((S.L : ℝ) ^ j / (S.L : ℝ) ^ S.k) ^ β) * H := by ring
      _ ≤ 12 * S.L * α₁ * ((l / (S.L : ℝ) ^ S.k) ^ β * ((S.L : ℝ) ^ j / (S.L : ℝ) ^ i) ^ β) * H := by
          gcongr
      _ = _ := by ring
  have htri : ‖Ad ((expMul 1 A' U).hol γ) (f x') - f x‖ ≤ ‖Ad (U.hol γ) (f x') - f x‖ +
      ‖Ad ((expMul 1 A' U).hol γ) (f x') - Ad (U.hol γ) (f x')‖ := by
    have := norm_add_le (Ad (U.hol γ) (f x') - f x)
      (Ad ((expMul 1 A' U).hol γ) (f x') - Ad (U.hol γ) (f x'))
    rwa [show Ad (U.hol γ) (f x') - f x + (Ad ((expMul 1 A' U).hol γ) (f x') - Ad (U.hol γ) (f x')) =
      Ad ((expMul 1 A' U).hol γ) (f x') - f x by abel] at this
  calc ‖Ad ((expMul 1 A' U).hol γ) (f x') - f x‖ ≤ (l / (S.L : ℝ) ^ S.k) ^ β * H +
        12 * S.L * α₁ * (((S.L : ℝ) ^ j / (S.L : ℝ) ^ i) ^ β * (l / (S.L : ℝ) ^ S.k) ^ β) * H :=
        htri.trans (add_le_add hfirst hsec)
    _ = _ := by ring

/-- `lem:holder-transports`(iii), at one pair: for `0 < ε ≤ 1`, a pair `x ≠ x'` with `d₁ ≤ a_j`, a
shortest path `γ`, and a point of `Ω_j` within `a_j` of `x'` (where `f(x') ≠ 0`; otherwise the two
differences coincide), the transported differences with `𝐔` and with `U`, divided by `(d₁/a_j)^ε`,
differ by at most `12Lα₁‖f‖_∞`. -/
theorem holder_transports_iii (hRM : 3 * (S.L : ℝ) ≤ S.RM) (A' : Form1 N n) (U : Config N n)
    (hU : ∀ μ x, ((U μ x : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Mat) ∈ unitaryGroup (Fin N) ℂ) {α₁ : ℝ}
    (hα : 32 * S.L * α₁ ≤ 1) (hreg : RegA S A' α₁) {f : Site n → Mat} {M ε : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1) {j : ℕ} (hj : j ≤ S.k) {x x' : Site n}
    {γ : List (Bond n)} (hxx : x ≠ x') (hγ : IsShortest x x' γ) (hlen : Blocks.d1 x x' ≤ S.L ^ j)
    (hnear : f x' ≠ 0 → ∃ z ∈ S.Ω j, Blocks.dinf x' z ≤ S.L ^ j) :
    |((Blocks.d1 x x' : ℝ) / (S.L : ℝ) ^ j) ^ (-ε) * ‖Ad ((expMul 1 A' U).hol γ) (f x') - f x‖ -
        ((Blocks.d1 x x' : ℝ) / (S.L : ℝ) ^ j) ^ (-ε) * ‖Ad (U.hol γ) (f x') - f x‖| ≤
      12 * S.L * α₁ * M := by
  have hL := L_pos' S
  have hα0 := alpha_nonneg S hreg
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  obtain ⟨hpath, hend, hglen⟩ := hγ
  have hne : γ ≠ [] := by
    rintro rfl; exact hxx (by simpa [pend] using hend)
  set l : ℝ := (Blocks.d1 x x' : ℝ)
  set r : ℝ := l / (S.L : ℝ) ^ j
  have hl0 : 0 < l := by
    have : Blocks.d1 x x' ≠ 0 := fun h0 => hxx (eq_of_d1_eq_zero h0)
    simp only [l]; exact_mod_cast Nat.pos_of_ne_zero this
  have hr0 : 0 < r := div_pos hl0 (by positivity)
  have hr1 : r ≤ 1 := (div_le_one (by positivity)).mpr (by simp only [l]; exact_mod_cast hlen)
  -- the difference of the two transported differences
  have hdiff : ‖Ad ((expMul 1 A' U).hol γ) (f x') - Ad (U.hol γ) (f x')‖ ≤ 12 * S.L * α₁ * r * M := by
    by_cases hf : f x' = 0
    · simp only [hf, Ad, Matrix.mul_zero, Matrix.zero_mul, sub_self, norm_zero]
      positivity
    obtain ⟨z, hz, hxz⟩ := hnear hf
    obtain ⟨b, hb, hbe⟩ := pend_mem hpath hne
    have hcmp := (transports_near S normLike_opNorm hRM A' U hU hα hreg hj hpath
      (by rw [hglen]; exact hlen) (Or.inr ⟨b, hb, Or.inr (hend ▸ hbe)⟩) hz hxz (f x')).2
    rw [hglen] at hcmp
    refine hcmp.trans ?_
    have : 0 ≤ 12 * (S.L : ℝ) * α₁ * r := by positivity
    calc 12 * (S.L : ℝ) * α₁ * (↑(Blocks.d1 x x') / (S.L : ℝ) ^ j) * ‖f x'‖
        = 12 * S.L * α₁ * r * ‖f x'‖ := by simp only [r, l]
      _ ≤ 12 * S.L * α₁ * r * M := by gcongr; exact hM x'
  have hrε : r ^ (-ε) * r ≤ 1 := by
    rw [← Real.rpow_add_one hr0.ne']
    exact Real.rpow_le_one hr0.le hr1 (by linarith)
  have hrε0 : 0 ≤ r ^ (-ε) := Real.rpow_nonneg hr0.le _
  rw [← mul_sub, abs_mul, abs_of_nonneg hrε0]
  have hab := abs_norm_sub_norm_le (Ad ((expMul 1 A' U).hol γ) (f x') - f x) (Ad (U.hol γ) (f x') - f x)
  rw [show Ad ((expMul 1 A' U).hol γ) (f x') - f x - (Ad (U.hol γ) (f x') - f x) =
    Ad ((expMul 1 A' U).hol γ) (f x') - Ad (U.hol γ) (f x') by abel] at hab
  calc r ^ (-ε) * |‖Ad ((expMul 1 A' U).hol γ) (f x') - f x‖ - ‖Ad (U.hol γ) (f x') - f x‖|
      ≤ r ^ (-ε) * (12 * S.L * α₁ * r * M) := by gcongr; exact hab.trans hdiff
    _ = (r ^ (-ε) * r) * (12 * S.L * α₁ * M) := by ring
    _ ≤ 1 * (12 * S.L * α₁ * M) := by gcongr
    _ = 12 * S.L * α₁ * M := one_mul _

end Transports
end CoreLean

end
