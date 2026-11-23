/-
`def:lattices` of BALABAN_CORE.tex on the fine lattice: the lattices `T^{(j)}`, the cells, and their
nesting.

Model. Lengths are in the units of the fine lattice (`η = 1`, so `a_j = Lʲ`); the fine lattice is
`(ℤ/N)⁴` with `N = ℓ_𝕋/η`, and `T^{(j)}` is the set of its points whose coordinates are multiples of
`Lʲ` (`InLat`). Distances are `|·|_∞` and `|·|₁` of the smallest representatives (`cd`, the circle
distance in each coordinate). For a point `x` and `j` with `Lʲ ∣ N`, `cen j x` is the point of `T^{(j)}`
whose cell contains `x`: the cell `Δ_j(y)` is `|z - y|_∞ ≤ a_j/2`, and on the fine lattice
`|x - y|_∞ ≤ (Lʲ - 1)/2` (`L` is odd, so no fine point lies on the boundary of a cell). Its uniqueness
and the nesting `cen (j+1) (cen j x) = cen (j+1) x` (each cell of scale `j + 1` is the union of `L⁴`
cells of scale `j`) are proved here.
-/
import CoreLean.Composition

open Finset

noncomputable section

namespace CoreLean

namespace Blocks

variable {N : ℕ} [NeZero N]

/-! ### The circle distance on `ℤ/N` -/

/-- The distance `|u|` of the smallest representative. -/
def cd (u : ZMod N) : ℕ := u.valMinAbs.natAbs

lemma valMinAbs_intCast {t : ℤ} (h1 : -(N : ℤ) < 2 * t) (h2 : 2 * t ≤ N) :
    (t : ZMod N).valMinAbs = t := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> push_cast <;> omega

lemma cd_intCast_le (t : ℤ) : cd (t : ZMod N) ≤ t.natAbs := by
  unfold cd
  by_cases h : 2 * t.natAbs < N
  · rw [valMinAbs_intCast (by omega) (by omega)]
  · exact (ZMod.natAbs_valMinAbs_le _).trans (by omega)

lemma cd_intCast_eq {t : ℤ} (h : 2 * t.natAbs ≤ N - 1) : cd (t : ZMod N) = t.natAbs := by
  unfold cd
  have := NeZero.pos N
  rw [valMinAbs_intCast (by omega) (by omega)]

lemma cd_add_le (a b : ZMod N) : cd (a + b) ≤ cd a + cd b :=
  (ZMod.natAbs_valMinAbs_add_le a b).trans (Int.natAbs_add_le _ _)

lemma cd_neg (a : ZMod N) : cd (-a) = cd a := ZMod.natAbs_valMinAbs_neg a

lemma cd_sub_comm (a b : ZMod N) : cd (a - b) = cd (b - a) := by
  rw [← neg_sub, cd_neg]

lemma cd_zero : cd (0 : ZMod N) = 0 := by simp [cd]

lemma cd_eq_zero {a : ZMod N} (h : cd a = 0) : a = 0 := by
  unfold cd at h
  rw [Int.natAbs_eq_zero, ZMod.valMinAbs_eq_zero] at h
  exact h

lemma cd_sub_le (a b c : ZMod N) : cd (a - c) ≤ cd (a - b) + cd (b - c) := by
  have := cd_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

lemma cd_le_half (a : ZMod N) : cd a ≤ N / 2 := ZMod.natAbs_valMinAbs_le a

/-! ### Multiples of `Lʲ` -/

/-- `u` is a multiple of `m` in `ℤ/N`. -/
def IsMul (m : ℕ) (u : ZMod N) : Prop := ∃ r : ℤ, u = ((m * r : ℤ) : ZMod N)

lemma IsMul.sub {m : ℕ} {u v : ZMod N} (hu : IsMul m u) (hv : IsMul m v) : IsMul m (u - v) := by
  obtain ⟨r, rfl⟩ := hu; obtain ⟨s, rfl⟩ := hv
  exact ⟨r - s, by push_cast; ring⟩

lemma IsMul.of_mul {m l : ℕ} {u : ZMod N} (hu : IsMul (m * l) u) : IsMul m u := by
  obtain ⟨r, rfl⟩ := hu
  exact ⟨l * r, by push_cast; ring⟩

/-- If `m ∣ N`, the smallest representative of a multiple of `m` is a multiple of `m`. -/
lemma IsMul.dvd_valMinAbs {m : ℕ} (hm : m ∣ N) {u : ZMod N} (hu : IsMul m u) :
    (m : ℤ) ∣ u.valMinAbs := by
  obtain ⟨r, rfl⟩ := hu
  have h := ZMod.coe_valMinAbs ((m * r : ℤ) : ZMod N)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have h' : (m : ℤ) ∣ (m * r : ℤ) - ((m * r : ℤ) : ZMod N).valMinAbs :=
    (Int.natCast_dvd_natCast.mpr hm).trans h
  have := dvd_sub (dvd_mul_right (m : ℤ) r) h'
  simpa using this

/-- A multiple of `m ∣ N` closer than `m` to `0` is `0`. -/
lemma IsMul.eq_zero {m : ℕ} (hm : m ∣ N) {u : ZMod N} (hu : IsMul m u) (h : cd u < m) : u = 0 := by
  obtain ⟨t, ht⟩ := hu.dvd_valMinAbs hm
  have : u.valMinAbs = 0 := by
    unfold cd at h
    rw [ht] at h ⊢
    rw [Int.natAbs_mul] at h
    have : t.natAbs = 0 := by
      by_contra hne
      have : 1 ≤ t.natAbs := Nat.one_le_iff_ne_zero.mpr hne
      have : m ≤ (m : ℤ).natAbs * t.natAbs := by simp; nlinarith
      omega
    simp [Int.natAbs_eq_zero.mp this]
  exact (ZMod.valMinAbs_eq_zero u).mp this

/-! ### The cell of a point at scale `j` -/

variable (L : ℕ)

/-- `h_j = (Lʲ - 1)/2`: a fine point lies in the cell of `y ∈ T^{(j)}` iff `|x - y|_∞ ≤ h_j`. -/
def half (j : ℕ) : ℕ := (L ^ j - 1) / 2

/-- The point of `T^{(j)}` whose cell contains `v`, in one coordinate. -/
def cen1 (j : ℕ) (v : ZMod N) : ZMod N := ((L ^ j * ((v.val + half L j) / L ^ j) : ℕ) : ZMod N)

variable {L}

lemma two_half_add_one (hL : Odd L) (j : ℕ) : 2 * half L j + 1 = L ^ j := by
  have := (hL.pow (n := j))
  obtain ⟨r, hr⟩ := this
  unfold half; omega

lemma cen1_isMul (j : ℕ) (v : ZMod N) : IsMul (L ^ j) (cen1 L j v) := by
  refine ⟨((v.val + half L j) / L ^ j : ℕ), ?_⟩
  unfold cen1
  generalize (v.val + half L j) / L ^ j = q
  push_cast; ring

lemma cd_sub_cen1_le (hL : Odd L) (j : ℕ) (v : ZMod N) : cd (v - cen1 L j v) ≤ half L j := by
  have hodd := two_half_add_one hL j
  have hpos : 0 < L ^ j := by omega
  have hdiv := Nat.div_add_mod (v.val + half L j) (L ^ j)
  have hmod := Nat.mod_lt (v.val + half L j) hpos
  have e : v - cen1 L j v = (((v.val : ℤ) - ((L ^ j * ((v.val + half L j) / L ^ j) : ℕ) : ℤ) : ℤ) :
      ZMod N) := by
    unfold cen1
    generalize (v.val + half L j) / L ^ j = q
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [e]
  refine (cd_intCast_le _).trans ?_
  generalize (v.val + half L j) % L ^ j = r at *
  generalize L ^ j * ((v.val + half L j) / L ^ j) = P at *
  generalize L ^ j = A at *
  omega

/-- Uniqueness: the only point of `T^{(j)}` within `h_j` of `v` is `cen1 j v`. -/
lemma eq_cen1 (hL : Odd L) {j : ℕ} (hj : L ^ j ∣ N) {v y : ZMod N} (hy : IsMul (L ^ j) y)
    (hd : cd (v - y) ≤ half L j) : y = cen1 L j v := by
  have hodd := two_half_add_one hL j
  have h := (hy.sub (cen1_isMul j v)).eq_zero hj (by
    have := cd_sub_le y v (cen1 L j v)
    rw [cd_sub_comm y v] at this
    have := cd_sub_cen1_le hL j v
    omega)
  exact sub_eq_zero.mp h

/-- A multiple of `Lʲ` within `h_{j+1}` of `0` lies within `Lʲ(L - 1)/2` of `0`. -/
lemma cd_mul_le (hL : Odd L) {j : ℕ} (hj : L ^ j ∣ N) {u : ZMod N} (hu : IsMul (L ^ j) u)
    (h : cd u ≤ half L (j + 1)) : cd u ≤ L ^ j * ((L - 1) / 2) := by
  obtain ⟨t, ht⟩ := hu.dvd_valMinAbs hj
  have h2 : 2 * half L (j + 1) + 1 = L ^ j * L := by rw [two_half_add_one hL, pow_succ]
  obtain ⟨l, hl⟩ := hL
  have hLl : (L - 1) / 2 = l := by omega
  rw [hLl]
  unfold cd at h ⊢
  rw [ht, Int.natAbs_mul] at h ⊢
  simp only [Int.natAbs_natCast] at h ⊢
  generalize half L (j + 1) = H at *
  generalize L ^ j = A at *
  subst hl
  -- `2A(l + 1) ≤ 2h_{j+1} = A(2l + 1) - 1` is impossible
  by_contra hc
  push_neg at hc
  have ht' : l + 1 ≤ t.natAbs := by
    by_contra h'
    push_neg at h'
    have : A * t.natAbs ≤ A * l := Nat.mul_le_mul_left _ (by omega)
    omega
  have : A * (l + 1) ≤ A * t.natAbs := Nat.mul_le_mul_left _ ht'
  nlinarith

/-- The nesting of the cells: `cen (j+1) (cen j v) = cen (j+1) v`. -/
lemma cen1_cen1 (hL : Odd L) {j : ℕ} (hj1 : L ^ (j + 1) ∣ N) (v : ZMod N) :
    cen1 L (j + 1) (cen1 L j v) = cen1 L (j + 1) v := by
  have hj : L ^ j ∣ N := (pow_dvd_pow L (Nat.le_succ j)).trans hj1
  set c := cen1 L j v
  set C := cen1 L (j + 1) c
  have hC : IsMul (L ^ (j + 1)) C := cen1_isMul (j + 1) c
  have hCj : IsMul (L ^ j) C := by
    rw [pow_succ] at hC; exact hC.of_mul
  -- `|c - C| ≤ Lʲ(L - 1)/2`
  have h1 : cd (c - C) ≤ L ^ j * ((L - 1) / 2) :=
    cd_mul_le hL hj ((cen1_isMul j v).sub hCj) (cd_sub_cen1_le hL (j + 1) c)
  have h2 : cd (v - c) ≤ half L j := cd_sub_cen1_le hL j v
  have hsum : cd (v - C) ≤ half L (j + 1) := by
    have := cd_sub_le v c C
    have e1 := two_half_add_one hL j
    have e2 : 2 * half L (j + 1) + 1 = L ^ j * L := by rw [two_half_add_one hL, pow_succ]
    obtain ⟨l, hl⟩ := hL
    have hLl : (L - 1) / 2 = l := by omega
    rw [hLl] at h1
    have : half L j + L ^ j * l = half L (j + 1) := by
      generalize half L (j + 1) = H at *
      generalize half L j = h at *
      generalize L ^ j = A at *
      subst hl
      nlinarith
    omega
  exact eq_cen1 hL hj1 hC hsum

/-! ### Points of `T^{(i)}` near a point -/

/-- In each coordinate at most two multiples of `Lⁱ` lie at a distance less than `Lⁱ` from `v`,
if `3Lⁱ ≤ N`. -/
lemma card_near_le (hL : Odd L) {i : ℕ} (hi : L ^ i ∣ N) (hN : 3 * L ^ i ≤ N) (v : ZMod N) :
    ∃ S : Finset (ZMod N), S.card ≤ 2 ∧
      ∀ m : ZMod N, IsMul (L ^ i) m → cd (v - m) < L ^ i → m ∈ S := by
  have hodd := two_half_add_one hL i
  set c := cen1 L i v
  set δ := (v - c).valMinAbs
  have hδ : δ.natAbs ≤ half L i := cd_sub_cen1_le hL i v
  have hvc : v - c = (δ : ZMod N) := (ZMod.coe_valMinAbs _).symm
  refine ⟨if 0 ≤ δ then {c, c + (L ^ i : ℕ)} else {c, c - (L ^ i : ℕ)}, ?_, ?_⟩
  · split_ifs <;> exact card_le_two
  · intro m hm hlt
    have hδ' : cd (v - c) ≤ half L i := cd_sub_cen1_le hL i v
    -- `m - c` is `t Lⁱ` with `|t| ≤ 1`
    obtain ⟨t, ht⟩ := (hm.sub (cen1_isMul i v)).dvd_valMinAbs hi
    have hmc : cd (m - c) < 2 * L ^ i := by
      have := cd_sub_le m v c
      rw [cd_sub_comm m v] at this
      omega
    have htle : t.natAbs ≤ 1 := by
      unfold cd at hmc
      rw [ht, Int.natAbs_mul, Int.natAbs_natCast] at hmc
      by_contra h
      push_neg at h
      have : L ^ i * 2 ≤ L ^ i * t.natAbs := Nat.mul_le_mul_left _ h
      omega
    have hmeq : m - c = ((((L ^ i : ℕ) : ℤ) * t : ℤ) : ZMod N) := by
      rw [← ht, ZMod.coe_valMinAbs]
    -- the distance from `v` to `c + t Lⁱ` is `|δ - t Lⁱ|`
    have hdist : cd (v - m) = (δ - ((L ^ i : ℕ) : ℤ) * t).natAbs := by
      have e : v - m = ((δ - ((L ^ i : ℕ) : ℤ) * t : ℤ) : ZMod N) := by
        have : v - m = (v - c) - (m - c) := by ring
        rw [this, hvc, hmeq]; push_cast; ring
      rw [e]
      refine cd_intCast_eq ?_
      have h1 : (δ - ((L ^ i : ℕ) : ℤ) * t).natAbs ≤ δ.natAbs + L ^ i * t.natAbs := by
        have := Int.natAbs_sub_le δ (((L ^ i : ℕ) : ℤ) * t)
        rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
      have h2 : L ^ i * t.natAbs ≤ L ^ i := by
        calc L ^ i * t.natAbs ≤ L ^ i * 1 := Nat.mul_le_mul_left _ htle
          _ = L ^ i := mul_one _
      omega
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = -1) with rfl | rfl | rfl
    · have : m = c := by rw [← sub_eq_zero, hmeq]; simp
      split_ifs <;> simp [this]
    · have hm' : m = c + (L ^ i : ℕ) := by
        have : m = c + (m - c) := by ring
        rw [this, hmeq]; push_cast; ring
      split_ifs with h0
      · simp [hm']
      · exfalso; rw [hdist] at hlt; omega
    · have hm' : m = c - (L ^ i : ℕ) := by
        have : m = c + (m - c) := by ring
        rw [this, hmeq]; push_cast; ring
      split_ifs with h0
      · exfalso; rw [hdist] at hlt; omega
      · simp [hm']

end Blocks

end CoreLean
