/-
`prop:regular-averages`(ii) of BALABAN_CORE.tex (`aec9e94587a7`): the iterated average of a regular field.

The lattices `T^{(i+l)}`, `0 ≤ l ≤ n`, are the tori `Site (nn l)`; a point of `T^{(i+l)}` is given by its
coordinates `x` in the units of `T^{(i)}`, divisible by `L^l` (`Lat`), and its site is `img h (base l) l x`.
The plaquette `p'` of `T^{(j)}`, `j = i + n`, has the first corner at the origin and the directions `μ, ν`.
* `Hw`, `InR`: the union of the blocks of order `n - l` of the four corners of `p'` is the box
  `[-H_l, Lⁿ + H_l]` in the directions `μ, ν` and `[-H_l, H_l]` in the others, `H_l = (Lⁿ - L^l)/2`.
* `PlaqR`: a plaquette of `T^{(i+l)}`, by its first corner, with its four corners in that set.
* `regular_averages_ii`: the induction `α_l ≤ εL^{2l}(1 + 2C₀εL^{2l})`, `ε = αL^{-2n}`, by (i).
-/
import CoreLean.RegularAverages

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace RegularAverages

open LatticePaths LatticeKappa BoxGeometry AxialStraightLattice

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### Plaquettes in the box `Δ(p')` -/

section Box

variable {n : ℕ} [NeZero n]

lemma inD_ext {h : ℕ} {μ ν : Fin 4} {w : Fin 4 → ℤ} (hw : LatticePaths.InBox (loD h) (hiD h μ ν) w) :
    ∀ σ, -(h : ℤ) - 1 ≤ w σ ∧ w σ ≤ 3 * h + 2 := fun σ => by
  have := inD_range hw σ; omega

lemma inD_ext1 {h : ℕ} {μ ν : Fin 4} {w : Fin 4 → ℤ} (hw : LatticePaths.InBox (loD h) (hiD h μ ν) w)
    (ρ : Fin 4) : ∀ σ, -(h : ℤ) - 1 ≤ (w + Pi.single ρ 1 : Fin 4 → ℤ) σ ∧
      (w + Pi.single ρ 1 : Fin 4 → ℤ) σ ≤ 3 * h + 2 := fun σ => by
  have := inD_range hw σ
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> omega

/-- A plaquette with its corners in `Δ(p')` is given by the offset of its first corner, the offsets of
its four corners lying in `Δ(p')`. -/
lemma plaqIn_box {h : ℕ} (hn : 4 * h + 4 ≤ n) (y₀ : Site n) (μ ν μ' ν' : Fin 4) (z : Site n)
    (hz : PlaqIn (boxR y₀ (loD h) (hiD h μ ν)) μ' ν' z) :
    ∃ m, LatticePaths.InBox (loD h) (hiD h μ ν) m ∧
      LatticePaths.InBox (loD h) (hiD h μ ν) (m + Pi.single μ' 1) ∧
      LatticePaths.InBox (loD h) (hiD h μ ν) (m + Pi.single ν' 1) ∧
      LatticePaths.InBox (loD h) (hiD h μ ν) (m + Pi.single μ' 1 + Pi.single ν' 1) ∧ z = ofs y₀ m := by
  obtain ⟨⟨m, hm, rfl⟩, ⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩, ⟨m3, hm3, e3⟩⟩ := hz
  have k1 : m + Pi.single μ' 1 = m1 :=
    ofs_inj hn y₀ (inD_ext1 hm μ') (inD_ext hm1) (by rw [ofs1]; exact e1)
  have k2 : m + Pi.single ν' 1 = m2 :=
    ofs_inj hn y₀ (inD_ext1 hm ν') (inD_ext hm2) (by rw [ofs1]; exact e2)
  have k3 : m + Pi.single μ' 1 + Pi.single ν' 1 = m3 :=
    ofs_inj hn y₀ (by rw [k1]; exact inD_ext1 hm1 ν') (inD_ext hm3) (by rw [ofs1, ofs1]; exact e3)
  exact ⟨m, hm, by rw [k1]; exact hm1, by rw [k2]; exact hm2, by rw [k3]; exact hm3, rfl⟩

end Box

/-! ### The blocks of higher order -/

/-- `H_l = (Lⁿ - L^l)/2`. -/
def Hw (h nl l : ℕ) : ℤ := (Lz h ^ nl - Lz h ^ l) / 2

lemma two_Hw (h nl l : ℕ) : 2 * Hw h nl l = Lz h ^ nl - Lz h ^ l := by
  unfold Hw
  refine Int.mul_ediv_cancel' ?_
  exact (((Lz_odd h).pow).sub_odd (Lz_odd h).pow).two_dvd

lemma Hw_step {h nl l : ℕ} : Hw h nl l = Hw h nl (l + 1) + Lz h ^ l * h := by
  have e1 := two_Hw h nl l
  have e2 := two_Hw h nl (l + 1)
  have : 2 * Hw h nl l = 2 * (Hw h nl (l + 1) + Lz h ^ l * h) := by
    rw [mul_add, e1, e2, pow_succ]; unfold Lz; ring
  omega

lemma Hw_nonneg {h nl l : ℕ} (hl : l ≤ nl) : 0 ≤ Hw h nl l := by
  have e := two_Hw h nl l
  have : Lz h ^ l ≤ Lz h ^ nl := pow_le_pow_right₀ (Lz_one h) hl
  omega

lemma Hw_self (h nl : ℕ) : Hw h nl nl = 0 := by simp [Hw]

/-- The union of the blocks of order `n - l` of the corners `0, Lⁿe_μ, Lⁿe_ν, Lⁿ(e_μ + e_ν)` of `p'`. -/
def InR (h nl : ℕ) (μ ν : Fin 4) (l : ℕ) (x : Fin 4 → ℤ) : Prop :=
  ∀ σ, -Hw h nl l ≤ x σ ∧ x σ ≤ (if σ = μ ∨ σ = ν then Lz h ^ nl else 0) + Hw h nl l

/-- The plaquette `p_{μ'ν'}(x)` of `T^{(i+l)}` has its four corners in the blocks of order `n - l` of the
corners of `p'`. -/
def PlaqR (h nl : ℕ) (μ ν : Fin 4) (l : ℕ) (μ' ν' : Fin 4) (x : Fin 4 → ℤ) : Prop :=
  Lat (Lz h) l x ∧ InR h nl μ ν l x ∧ InR h nl μ ν l (x + Lz h ^ l • Pi.single μ' 1) ∧
    InR h nl μ ν l (x + Lz h ^ l • Pi.single ν' 1) ∧
    InR h nl μ ν l (x + Lz h ^ l • Pi.single μ' 1 + Lz h ^ l • Pi.single ν' 1)

/-- `H_l = L^l(L^{n-l} - 1)/2` is a multiple of `L^l`. -/
lemma Hw_dvd {h nl l : ℕ} (hl : l ≤ nl) : Lz h ^ l ∣ Hw h nl l := by
  obtain ⟨r, hr⟩ := ((Lz_odd h).pow (n := nl - l)).sub_odd odd_one
  have hp : Lz h ^ nl = Lz h ^ l * Lz h ^ (nl - l) := by rw [← pow_add, Nat.add_sub_cancel' hl]
  have e : 2 * Hw h nl l = 2 * (Lz h ^ l * r) := by
    rw [two_Hw, hp]; linear_combination (Lz h ^ l) * hr
  exact ⟨r, mul_left_cancel₀ two_ne_zero e⟩

lemma dvd_step {Q a b : ℤ} (hQ : 0 < Q) (ha : Q ∣ a) (hb : Q ∣ b) (hlt : b < a) : b + Q ≤ a := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have h1 : b' + 1 ≤ a' := lt_of_mul_lt_mul_left hlt hQ.le
  calc Q * b' + Q = Q * (b' + 1) := by ring
    _ ≤ Q * a' := mul_le_mul_of_nonneg_left h1 hQ.le

/-- On the points of `T^{(i+l)}`, `InR` is the union of the blocks of order `n - l` of the four corners
`c ∈ {0, Lⁿ}e_μ + {0, Lⁿ}e_ν` of `p'`: the points `x` with `|x_σ - c_σ| ≤ H_l`. -/
lemma inR_iff_blocks {h nl l : ℕ} (hl : l ≤ nl) {μ ν : Fin 4} (hμν : μ ≠ ν) {x : Fin 4 → ℤ}
    (hx : Lat (Lz h) l x) :
    InR h nl μ ν l x ↔ ∃ c : Fin 4 → ℤ, (c μ = 0 ∨ c μ = Lz h ^ nl) ∧ (c ν = 0 ∨ c ν = Lz h ^ nl) ∧
      (∀ σ, σ ≠ μ → σ ≠ ν → c σ = 0) ∧ ∀ σ, |x σ - c σ| ≤ Hw h nl l := by
  have hP : 0 < Lz h ^ l := pow_pos (Lz_pos h) l
  have hH := two_Hw h nl l
  have hH0 : 0 ≤ Hw h nl l := Hw_nonneg hl
  have hHd := Hw_dvd (h := h) hl
  have hLn : 0 ≤ Lz h ^ nl := (pow_pos (Lz_pos h) nl).le
  constructor
  · intro hR
    have pick : ∀ σ, (σ = μ ∨ σ = ν) → ∃ k, (k = 0 ∨ k = Lz h ^ nl) ∧ |x σ - k| ≤ Hw h nl l := by
      intro σ hσ
      have hRσ := hR σ
      simp only [hσ, ↓reduceIte] at hRσ
      by_cases hle : x σ ≤ Hw h nl l
      · exact ⟨0, Or.inl rfl, by rw [sub_zero, abs_le]; constructor <;> linarith⟩
      · rw [not_le] at hle
        have := dvd_step hP (hx σ) hHd hle
        exact ⟨_, Or.inr rfl, by rw [abs_le]; constructor <;> linarith⟩
    obtain ⟨kμ, hkμ, hxμ⟩ := pick μ (Or.inl rfl)
    obtain ⟨kν, hkν, hxν⟩ := pick ν (Or.inr rfl)
    refine ⟨Pi.single μ kμ + Pi.single ν kν, ?_, ?_,
      fun σ h1 h2 => by simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2], fun σ => ?_⟩
    · simpa [Pi.single_eq_of_ne hμν] using hkμ
    · simpa [Pi.single_eq_of_ne (Ne.symm hμν)] using hkν
    · by_cases h1 : σ = μ
      · subst h1; simpa [Pi.single_eq_of_ne hμν] using hxμ
      by_cases h2 : σ = ν
      · subst h2; simpa [Pi.single_eq_of_ne h1] using hxν
      · have hRσ := hR σ
        simp only [h1, h2, or_self, ↓reduceIte, zero_add] at hRσ
        simp only [Pi.add_apply, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, add_zero, sub_zero,
          abs_le]
        constructor <;> linarith
  · rintro ⟨c, hcμ, hcν, hcσ, hxc⟩ σ
    have hb := abs_le.1 (hxc σ)
    by_cases h1 : σ = μ
    · subst h1
      simp only [true_or, ↓reduceIte]
      rcases hcμ with e | e <;> rw [e] at hb <;> constructor <;> linarith
    by_cases h2 : σ = ν
    · subst h2
      simp only [or_true, ↓reduceIte]
      rcases hcν with e | e <;> rw [e] at hb <;> constructor <;> linarith
    · simp only [h1, h2, or_self, ↓reduceIte, zero_add]
      rw [hcσ σ h1 h2] at hb
      constructor <;> linarith

/-- The box `Δ(p)` of a plaquette `p` of `T^{(i+l+1)}` with corners in the blocks of order `n - l - 1`
lies in the blocks of order `n - l`. -/
lemma inR_of_box {h nl l : ℕ} {μ ν μ' ν' : Fin 4} {x : Fin 4 → ℤ}
    (hP : PlaqR h nl μ ν (l + 1) μ' ν' x) {w : Fin 4 → ℤ}
    (hw : LatticePaths.InBox (loD h) (hiD h μ' ν') w) : InR h nl μ ν l (x + Lz h ^ l • w) := by
  obtain ⟨-, h0, h1, h2, -⟩ := hP
  set Q : ℤ := Lz h ^ l with hQ
  have hQ0 : 0 < Q := pow_pos (Lz_pos h) l
  have hpow : Lz h ^ (l + 1) = Q * (2 * h + 1) := by rw [pow_succ, hQ]; rfl
  have hstep : Hw h nl l = Hw h nl (l + 1) + Q * h := Hw_step
  intro σ
  have a0 := h0 σ
  have a1 := h1 σ
  have a2 := h2 σ
  have hwσ := hw σ
  simp only [loD, hiD] at hwσ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hpow] at a1 a2 ⊢
  rw [hstep]
  set T := (if σ = μ ∨ σ = ν then Lz h ^ nl else 0)
  have hlo : Q * (-(h : ℤ)) ≤ Q * w σ := mul_le_mul_of_nonneg_left hwσ.1 hQ0.le
  by_cases hs1 : σ = μ'
  · subst hs1
    simp only [true_or, ↓reduceIte] at hwσ
    simp only [↓reduceIte, mul_one] at a1
    have hhi : Q * w σ ≤ Q * (3 * h + 1) := mul_le_mul_of_nonneg_left hwσ.2 hQ0.le
    constructor <;> nlinarith
  by_cases hs2 : σ = ν'
  · subst hs2
    simp only [or_true, ↓reduceIte] at hwσ
    simp only [↓reduceIte, mul_one] at a2
    have hhi : Q * w σ ≤ Q * (3 * h + 1) := mul_le_mul_of_nonneg_left hwσ.2 hQ0.le
    constructor <;> nlinarith
  · simp only [hs1, hs2, or_self, ↓reduceIte] at hwσ
    have hhi : Q * w σ ≤ Q * h := mul_le_mul_of_nonneg_left hwσ.2 hQ0.le
    constructor <;> nlinarith

/-- The site of `x + L^k e_ρ` is the neighbour of the site of `x` in the direction `ρ`. -/
lemma img_unit {n : ℕ} [NeZero n] {h k : ℕ} (y : Site n) {x : Fin 4 → ℤ} (hx : Lat (Lz h) k x)
    (ρ : Fin 4) : img h y k x + unit n ρ = img h y k (x + Lz h ^ k • Pi.single ρ 1) := by
  rw [← img_add y hx]
  have := ofs1 (img h y k x) 0 ρ
  rw [zero_add, ofs_zero] at this
  exact this.symm

lemma shift_eq (h l : ℕ) (ρ : Fin 4) :
    Lz h ^ l • (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ) : Fin 4 → ℤ) = Lz h ^ (l + 1) • Pi.single ρ 1 := by
  funext σ
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, pow_succ, Lz]
  split_ifs <;> push_cast <;> ring

/-- The corners of `p'` are points of the blocks of order `0`. -/
lemma inR_corner {h nl : ℕ} {μ ν : Fin 4} (hμν : μ ≠ ν) {a b : ℤ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    InR h nl μ ν nl (Lz h ^ nl • Pi.single μ a + Lz h ^ nl • Pi.single ν b) := by
  have hp : 0 < Lz h ^ nl := pow_pos (Lz_pos h) nl
  intro σ
  rw [Hw_self]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_zero, add_zero]
  by_cases h1 : σ = μ
  · subst h1
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hμν, true_or, ↓reduceIte, mul_zero, add_zero]
    constructor <;> nlinarith
  · by_cases h2 : σ = ν
    · subst h2
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne h1, or_true, ↓reduceIte, mul_zero, zero_add]
      constructor <;> nlinarith
    · simp [h1, h2]

set_option maxHeartbeats 2000000 in
/-- **`prop:regular-averages`(ii)**: let `0 ≤ i < j`, `n = j - i`, `L = 2h + 1 ≥ 3`, and let the gauge fields
`V_l` on `T^{(i+l)}` be the iterated averages `V_{l+1} = M(V_l)` on the bonds of `T^{(i+l+1)}` with ends in
the blocks of order `n - l - 1` of the corners of the plaquette `p'` of `T^{(j)}` (first corner at the
origin, directions `μ ≠ ν`). If `|V_0(∂p) - id| ≤ α(a_i/a_j)² = αL^{-2n}` for the plaquettes `p` of
`T^{(i)}` with corners in the blocks of order `n` of the corners of `p'`, and `α ≤ c₂`, then
`|M^n(V_0)(∂p') - id| ≤ α + 2C₀α² ≤ 2α`, `C₀ = 2²⁷N`. Here `c₂ = min(c/2, 1/(4C₀))` with the constant `c`
of (i); the tori `T^{(i+l)}`, `l < n`, have at least `4h + 4` sites in each direction. -/
theorem regular_averages_ii (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (h : ℕ), 1 ≤ h → ∀ (nl : ℕ) (μ ν : Fin 4), μ ≠ ν →
      ∀ (nn : ℕ → ℕ) [∀ l, NeZero (nn l)], (∀ l, l < nl → 4 * h + 4 ≤ nn l) →
      ∀ (base : ∀ l, Site (nn l)) (V : ∀ l, Config N (nn l)), (∀ l, l ≤ nl → IsGField G (V l)) →
      ∀ {ι : Type} [Fintype ι] {P : ι → Type} [∀ x, Fintype (P x)] (off : ι → Fin 4 → ℤ)
        (ord : ∀ x, P x → List (Fin 4)), 0 < Fintype.card ι → (∀ x, 0 < Fintype.card (P x)) →
      (∀ x, AxialReference.InM h (off x)) → (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) →
      (∀ l, l < nl → ∀ (ρ : Fin 4) (x : Fin 4 → ℤ), Lat (Lz h) (l + 1) x → InR h nl μ ν (l + 1) x →
        InR h nl μ ν (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
        V (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
          avgB G (V l) (img h (base l) l x) ρ (2 * h + 1) off ord) →
      ∀ α : ℝ, 0 ≤ α → α ≤ c₂ →
      (∀ μ' ν' x, PlaqR h nl μ ν 0 μ' ν' x →
        hs (((plaq (V 0) μ' ν' (img h (base 0) 0 x) : GLN) : Mat) - 1) ≤
          α * ((((2 * h + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ nl) →
      hs (((plaq (V nl) μ ν (base nl) : GLN) : Mat) - 1) ≤ α + 2 * (2 ^ 27 * N) * α ^ 2 ∧
        α + 2 * (2 ^ 27 * N) * α ^ 2 ≤ 2 * α := by
  obtain ⟨c, hc0, HI⟩ := regular_averages_i G hG hN
  have hC0 : (0 : ℝ) < 2 ^ 27 * N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  refine ⟨min (c / 2) (1 / (4 * (2 ^ 27 * N))), lt_min (by linarith) (by positivity), ?_⟩
  intro h hh nl μ ν hμν nn _ hn base V hV ι _ P _ off ord hι hP hoff hord hrel α hα hαc hbase
  set C₀ : ℝ := 2 ^ 27 * N with hC₀
  have hαc1 : α ≤ c / 2 := hαc.trans (min_le_left _ _)
  have hαC : C₀ * α ≤ 1 / 4 := by
    have := hαc.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set K : ℝ := ((2 * h + 1 : ℕ) : ℝ) ^ 2 with hK
  have hK9 : 9 ≤ K := by
    have h3 : (3 : ℝ) ≤ ((2 * h + 1 : ℕ) : ℝ) := by
      push_cast; have : (1 : ℝ) ≤ h := by exact_mod_cast hh
      linarith
    rw [hK]; nlinarith
  have hK0 : 0 < K := by linarith
  set ε : ℝ := α * K⁻¹ ^ nl with hε
  have hε0 : 0 ≤ ε := by positivity
  set t : ℕ → ℝ := fun l => ε * K ^ l with ht
  have ht0 : ∀ l, 0 ≤ t l := fun l => by simp only [ht]; positivity
  have htn : t nl = α := by
    simp only [ht, hε]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hK0.ne', one_pow, mul_one]
  have htmono : ∀ l m, l ≤ m → t l ≤ t m := fun l m hlm => by
    simp only [ht]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hlm) hε0
  have htK : ∀ l, l < nl → t l * K ≤ α := fun l hl => by
    have e : t l * K = t (l + 1) := by simp only [ht]; ring
    rw [e, ← htn]
    exact htmono _ _ hl
  set b : ℕ → ℝ := fun l => t l * (1 + 2 * C₀ * t l) with hb
  have hb0 : ∀ l, 0 ≤ b l := fun l => by
    have := ht0 l
    simp only [hb]; positivity
  -- the induction over the scales
  have key : ∀ l, l ≤ nl → ∀ μ' ν' x, PlaqR h nl μ ν l μ' ν' x →
      hs (((plaq (V l) μ' ν' (img h (base l) l x) : GLN) : Mat) - 1) ≤ b l := by
    intro l
    induction l with
    | zero =>
      intro _ μ' ν' x hx
      refine (hbase μ' ν' x hx).trans ?_
      have e : b 0 = ε * (1 + 2 * C₀ * ε) := by simp only [hb, ht, pow_zero, mul_one]
      rw [e]
      nlinarith [mul_nonneg hε0 (mul_nonneg hC0.le hε0)]
    | succ l ih =>
      intro hl μ' ν' x hx
      have hl' : l < nl := hl
      by_cases hμν' : μ' = ν'
      · subst hμν'
        rw [plaq_self]
        simpa [hs_zero'] using hb0 (l + 1)
      have hx1 : Lat (Lz h) (l + 1) x := hx.1
      have hx0 : Lat (Lz h) l x := lat_le hx1
      have hPR := hx
      obtain ⟨-, r0, r1, r2, r3⟩ := hx
      -- the plaquette of `V_{l+1}` is the plaquette of the average of `V_l`
      have hlat : ∀ ρ, Lat (Lz h) (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) := fun ρ σ =>
        dvd_add (hx1 σ) (lat_smul _ σ)
      have e1 := hrel l hl' μ' x hx1 r0 r1
      have e2 := hrel l hl' ν' (x + Lz h ^ (l + 1) • Pi.single μ' 1) (hlat μ') r1 r3
      have e3 := hrel l hl' μ' (x + Lz h ^ (l + 1) • Pi.single ν' 1) (hlat ν') r2
        (by rw [add_right_comm]; exact r3)
      have e4 := hrel l hl' ν' x hx1 r0 r2
      have hsh : ∀ ρ, ofs (img h (base l) l x) (Pi.single ρ ((2 * h + 1 : ℕ) : ℤ)) =
          img h (base l) l (x + Lz h ^ (l + 1) • Pi.single ρ 1) := fun ρ => by
        rw [img_add (base l) hx0, shift_eq]
      have hplaq : plaq (V (l + 1)) μ' ν' (img h (base (l + 1)) (l + 1) x) =
          plaqAvg G (V l) (img h (base l) l x) μ' ν' (2 * h + 1) off ord := by
        rw [plaq_eq, img_unit _ hx1, img_unit _ hx1, e1, e2, e3, e4]
        unfold plaqAvg
        rw [hsh, hsh]
      -- (i) at the plaquette, on `T^{(i+l)}`
      have hbK : b l * K ≤ c := by
        have h1 := htK l hl'
        have h2 : t l ≤ α := le_trans (le_mul_of_one_le_right (ht0 l) (by linarith)) h1
        have h3 : 2 * C₀ * t l ≤ 1 / 2 := by nlinarith
        calc b l * K = (t l * K) * (1 + 2 * C₀ * t l) := by simp only [hb]; ring
          _ ≤ α * (1 + 1 / 2) := mul_le_mul h1 (by linarith) (by have := ht0 l; positivity) hα
          _ ≤ c := by linarith
      have hhyp : ∀ μ'' ν'' z, PlaqIn (boxR (img h (base l) l x) (loD h) (hiD h μ' ν')) μ'' ν'' z →
          hs (((plaq (V l) μ'' ν'' z : GLN) : Mat) - 1) ≤ b l := by
        intro μ'' ν'' z hz
        obtain ⟨m, hm0, hm1, hm2, hm3, rfl⟩ := plaqIn_box (hn l hl') _ μ' ν' μ'' ν'' z hz
        rw [img_add (base l) hx0]
        refine ih hl'.le μ'' ν'' _ ⟨fun σ => dvd_add (hx0 σ) (lat_smul m σ), inR_of_box hPR hm0, ?_, ?_, ?_⟩
        · convert inR_of_box hPR hm1 using 1; simp only [smul_add]; abel
        · convert inR_of_box hPR hm2 using 1; simp only [smul_add]; abel
        · convert inR_of_box hPR hm3 using 1; simp only [smul_add]; abel
      obtain ⟨hI1, hI2⟩ := HI (V l) (hV l hl'.le) h (hn l hl') (img h (base l) l x) μ' ν' hμν' off ord
        hι hP hoff hord (b l) (hb0 l) hbK hhyp
      rw [hplaq]
      rw [← hK] at hI2
      rw [show ((2 * h + 1 : ℕ) : ℝ) ^ 4 = K ^ 2 by rw [hK]; ring] at hI1
      -- the recursion of the bounds
      have hT : C₀ * t l ≤ 1 / 36 := by
        have a1 : C₀ * (t l * K) ≤ C₀ * α := mul_le_mul_of_nonneg_left (htK l hl') hC0.le
        have a2 : C₀ * t l * 9 ≤ C₀ * t l * K :=
          mul_le_mul_of_nonneg_left hK9 (mul_nonneg hC0.le (ht0 l))
        linarith
      have hT0 : 0 ≤ C₀ * t l := mul_nonneg hC0.le (ht0 l)
      have hT2 : (1 + 2 * (C₀ * t l)) ^ 2 ≤ 5 / 4 := by nlinarith
      have hfac : 0 ≤ K * t l * (C₀ * t l) := by have := ht0 l; positivity
      have hin : K * (1 + 2 * (C₀ * t l)) ^ 2 ≤ 2 * K - 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hT2 hK0.le]
      have hmain : K * b l + C₀ * K ^ 2 * b l ^ 2 ≤ b (l + 1) := by
        have f1 : K * b l + C₀ * K ^ 2 * b l ^ 2 = K * t l + 2 * K * t l * (C₀ * t l) +
            K * t l * (C₀ * t l) * (K * (1 + 2 * (C₀ * t l)) ^ 2) := by simp only [hb]; ring
        have f2 : b (l + 1) = K * t l + 2 * K * t l * (C₀ * t l) +
            K * t l * (C₀ * t l) * (2 * K - 2) := by simp only [hb, ht]; ring
        rw [f1, f2]
        have := mul_le_mul_of_nonneg_left hin hfac
        linarith
      linarith
  -- the plaquette `p'` itself
  have hp' : PlaqR h nl μ ν nl μ ν 0 := by
    refine ⟨fun σ => dvd_zero _, ?_, ?_, ?_, ?_⟩
    · convert inR_corner (h := h) (nl := nl) hμν (le_refl (0 : ℤ)) zero_le_one le_rfl zero_le_one
        using 1
      simp
    · convert inR_corner (h := h) (nl := nl) hμν zero_le_one le_rfl le_rfl zero_le_one using 1
      simp
    · convert inR_corner (h := h) (nl := nl) hμν le_rfl zero_le_one zero_le_one le_rfl using 1
      simp
    · convert inR_corner (h := h) (nl := nl) hμν zero_le_one le_rfl zero_le_one le_rfl using 1
      simp
  have himg : img h (base nl) nl 0 = base nl := by
    unfold img
    rw [show qt h nl 0 = 0 from qt_eq (by simp), ofs_zero]
  have hfin := key nl le_rfl μ ν 0 hp'
  rw [himg] at hfin
  have hbn : b nl = α + 2 * C₀ * α ^ 2 := by simp only [hb, htn]; ring
  rw [hbn] at hfin
  refine ⟨hfin, ?_⟩
  nlinarith

end RegularAverages

end CoreLean

end
