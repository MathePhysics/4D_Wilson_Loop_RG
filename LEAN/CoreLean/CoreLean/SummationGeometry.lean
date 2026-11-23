/-
The lattices and the cells of `def:lattices` on the torus of `lem:distance`, for `eq:summation`.

The torus is `(ℝ/pℤ)⁴` (`Tor p`), a lattice of spacing `a` is the set of the points all of whose
coordinates are multiples of `a` (`InLat`), the closed cell of a point is `|z - y|_∞ ≤ a/2` (`cell`) and
its interior `|z - y|_∞ < a/2` (`cellOpen`). When `p` is a multiple of `a`, two points of the lattice at
an `ℓ^∞`-distance of less than `a` coincide (`eq_of_lt`), and, for `L` odd, a cell of side `La` is covered
by the cells of side `a` of the points of its block (`cell_nest`).
-/
import CoreLean.DivergenceConversion

open Set Finset MeasureTheory

noncomputable section

namespace CoreLean

namespace Summation

variable {p : ℝ}

/-- `z` lies in the lattice of spacing `a`. -/
def InLat (a : ℝ) (z : Tor p) : Prop := ∀ ν, ∃ n : ℤ, z ν = ((n * a : ℝ) : AddCircle p)

/-- The closed cell `|z - y|_∞ ≤ a/2`. -/
def cell (a : ℝ) (y : Tor p) : Set (Tor p) := {z | ∀ ν, ‖z ν - y ν‖ ≤ a / 2}

/-- The open cell `|z - y|_∞ < a/2`. -/
def cellOpen (a : ℝ) (y : Tor p) : Set (Tor p) := {z | ∀ ν, ‖z ν - y ν‖ < a / 2}

lemma isClosed_cell (a : ℝ) (y : Tor p) : IsClosed (cell a y) := by
  unfold cell
  rw [show {z : Tor p | ∀ ν, ‖z ν - y ν‖ ≤ a / 2} = ⋂ ν, {z : Tor p | ‖z ν - y ν‖ ≤ a / 2} by
    ext; simp]
  exact isClosed_iInter fun ν =>
    isClosed_le ((continuous_apply ν).sub continuous_const).norm continuous_const

/-- A multiple `ma` of `a` with `‖ma‖ < a` in `ℝ/pℤ`, `p = qa`, is `0`. -/
lemma coe_eq_zero_of_norm_lt {a : ℝ} (ha : 0 < a) {q : ℕ} (hq : 0 < q) (hp : p = q * a) (m : ℤ)
    (h : ‖((m * a : ℝ) : AddCircle p)‖ < a) : ((m * a : ℝ) : AddCircle p) = 0 := by
  have hp0 : 0 < p := by rw [hp]; positivity
  haveI : Fact (0 < p) := ⟨hp0⟩
  rw [AddCircle.norm_eq] at h
  set r := round (p⁻¹ * (m * a))
  have e : (m : ℝ) * a - r * p = ((m - r * q : ℤ) : ℝ) * a := by rw [hp]; push_cast; ring
  rw [e, abs_mul, abs_of_pos ha] at h
  have h1 : |((m - r * q : ℤ) : ℝ)| < 1 := by
    by_contra hc; push_neg at hc; nlinarith
  have h2 : m - r * q = 0 := by
    have := abs_lt.mp h1
    have h3 : (-1 : ℤ) < m - r * q := by exact_mod_cast this.1
    have h4 : m - r * q < 1 := by exact_mod_cast this.2
    omega
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨r, ?_⟩
  rw [zsmul_eq_mul, hp]
  have : (m : ℝ) = r * q := by exact_mod_cast (by omega : m = r * q)
  rw [this]; ring

/-- Two points of the lattice of spacing `a` at an `ℓ^∞`-distance of less than `a` coincide, if `p` is a
multiple of `a`. -/
lemma eq_of_lt {a : ℝ} (ha : 0 < a) {q : ℕ} (hq : 0 < q) (hp : p = q * a) {y y' : Tor p}
    (hy : InLat a y) (hy' : InLat a y') (h : ∀ ν, ‖y ν - y' ν‖ < a) : y = y' := by
  funext ν
  obtain ⟨n, hn⟩ := hy ν
  obtain ⟨n', hn'⟩ := hy' ν
  have e : y ν - y' ν = (((n - n' : ℤ) * a : ℝ) : AddCircle p) := by
    rw [hn, hn']; push_cast; rw [← AddCircle.coe_sub]; ring_nf
  have := coe_eq_zero_of_norm_lt ha hq hp (n - n') (by rw [← e]; exact h ν)
  rw [← e] at this
  exact sub_eq_zero.mp this

/-- The nesting of the cells: for `L` odd, every point of the cell of side `La` of a point `c` of the
lattice of spacing `La` lies in the cell of side `a` of a point `y'` of the lattice of spacing `a` with
`|y' - c|_∞ ≤ (L - 1)a/2`. -/
lemma cell_nest {L : ℕ} (hL : Odd L) {a : ℝ} (ha : 0 < a) {c : Tor p} (hc : InLat (L * a) c)
    {z : Tor p} (hz : z ∈ cell (L * a) c) :
    ∃ y', InLat a y' ∧ (∀ ν, ‖y' ν - c ν‖ ≤ ((L : ℝ) - 1) / 2 * a) ∧ z ∈ cell a y' := by
  obtain ⟨l, hl⟩ := hL
  have hLl : ((L : ℝ) - 1) / 2 = l := by rw [hl]; push_cast; ring
  -- lifts
  choose n hn using hc
  set ĉ : Fin 4 → ℝ := fun ν => n ν * (L * a)
  have hĉ : projT p ĉ = c := by funext ν; simp [projT, ĉ, hn ν]
  obtain ⟨x, hx, hd⟩ := exists_close_lift (p := p) ĉ z
  -- the index of the subcell in each coordinate
  set t : Fin 4 → ℝ := fun ν => (x ν - ĉ ν) / a
  have ht : ∀ ν, |t ν| ≤ l + 1 / 2 := by
    intro ν
    have h1 : |x ν - ĉ ν| ≤ L * a / 2 := by
      rw [hd ν, show ((ĉ ν : ℝ) : AddCircle p) = c ν by rw [← hĉ]; rfl]; exact hz ν
    simp only [t, abs_div, abs_of_pos ha]
    rw [div_le_iff₀ ha]
    have : (L : ℝ) = 2 * l + 1 := by rw [hl]; push_cast; ring
    rw [this] at h1; linarith
  set m : Fin 4 → ℤ := fun ν => max (-(l : ℤ)) (min (l : ℤ) (round (t ν)))
  have hm : ∀ ν, |(m ν : ℝ)| ≤ l ∧ |t ν - m ν| ≤ 1 / 2 := by
    intro ν
    have hr := abs_sub_round (t ν)
    have htν := abs_le.mp (ht ν)
    simp only [m]
    constructor
    · rw [abs_le]; push_cast; constructor
      · exact le_max_left _ _
      · exact max_le (by linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]) (min_le_left _ _)
    · rcases le_total (round (t ν)) (l : ℤ) with h1 | h1 <;>
        rcases le_total (-(l : ℤ)) (round (t ν)) with h2 | h2
      · rw [min_eq_right h1, max_eq_right h2]; exact hr
      · rw [min_eq_right h1, max_eq_left (by omega)]
        have : (round (t ν) : ℝ) ≤ -l := by exact_mod_cast h2
        rw [abs_le] at hr ⊢; push_cast; constructor <;> linarith
      · rw [min_eq_left h1, max_eq_right (by omega)]
        have : (l : ℝ) ≤ round (t ν) := by exact_mod_cast h1
        rw [abs_le] at hr ⊢; push_cast; constructor <;> linarith
      · have e : round (t ν) = (l : ℤ) := by omega
        rw [min_eq_left h1, max_eq_right (by omega), ← e]
        exact hr
  refine ⟨projT p (fun ν => ĉ ν + m ν * a), fun ν => ⟨n ν * L + m ν, ?_⟩, fun ν => ?_, fun ν => ?_⟩
  · simp only [projT, ĉ]; push_cast; ring_nf
  · -- `|y' - c| ≤ la`
    rw [← hĉ]
    simp only [projT]
    refine (norm_coe_sub_le _ _).trans ?_
    rw [show ĉ ν + m ν * a - ĉ ν = m ν * a by ring, hLl, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_right (hm ν).1 ha.le
  · -- `z` lies in the cell of `y'`
    rw [← hx]
    simp only [projT]
    refine (norm_coe_sub_le _ _).trans ?_
    have e : x ν - (ĉ ν + m ν * a) = (t ν - m ν) * a := by
      simp only [t]; field_simp; ring
    rw [e, abs_mul, abs_of_pos ha]
    have := (hm ν).2
    linarith [mul_le_mul_of_nonneg_right this ha.le]

/-! ### The sequence of domains on the torus -/

/-- The spacing `a_j = Lʲη`, `η = L^{-k}`. -/
def aa (L k j : ℕ) : ℝ := (L : ℝ) ^ j / (L : ℝ) ^ k

/-- `Ω_j`: the torus for `j = 0`, the union of the cells of side `a_j` of the points of `S_j` for
`1 ≤ j ≤ k`, empty for `j > k`. -/
def Om (L k : ℕ) (S : ℕ → Finset (Tor p)) (j : ℕ) : Set (Tor p) :=
  if j = 0 then univ else if j ≤ k then ⋃ y ∈ S j, cell (aa L k j) y else ∅

/-- A sequence of domains on the torus `(ℝ/ℓ_𝕋ℤ)⁴`, `ℓ_𝕋 = 2L^{m_𝕋}` (`def:lattices`, `def:sequence`):
`Ω_j` is the union of the cells of side `a_j` of the points of a set `S_j` of the lattice `T^{(j)}`, the
sets decrease, and `eq:separation` holds (with `≥`). -/
structure ContSeq (p : ℝ) where
  L : ℕ
  L_odd : Odd L
  three_le_L : 3 ≤ L
  k : ℕ
  mT : ℕ
  one_le_mT : 1 ≤ mT
  p_eq : p = 2 * (L : ℝ) ^ mT
  S : ℕ → Finset (Tor p)
  S_lat : ∀ j, ∀ y ∈ S j, InLat (aa L k j) y
  Ω_succ : ∀ j, Om L k S (j + 1) ⊆ Om L k S j
  RM : ℝ
  sep : ∀ i, 1 ≤ i → i < k → ∀ x ∉ Om L k S i, ∀ y ∈ Om L k S (i + 1),
    RM * 1 * aa L k i ≤ dist x y

namespace ContSeq

variable (C : ContSeq p)

/-- The spacing `a_j`. -/
abbrev a (j : ℕ) : ℝ := aa C.L C.k j

/-- The domain `Ω_j`. -/
abbrev Ω (j : ℕ) : Set (Tor p) := Om C.L C.k C.S j

lemma L_pos : (0 : ℝ) < C.L := by have := C.three_le_L; positivity

lemma a_pos (j : ℕ) : 0 < C.a j := by unfold a aa; have := C.L_pos; positivity

lemma L_mul_a (j : ℕ) : (C.L : ℝ) * C.a j = C.a (j + 1) := by
  unfold a aa; rw [pow_succ]; ring

lemma p_pos (C : ContSeq p) : 0 < p := by
  have := C.L_pos
  exact C.p_eq ▸ (by positivity : (0 : ℝ) < 2 * (C.L : ℝ) ^ C.mT)

/-- `p` is a multiple of `a_j` for `j ≤ k`. -/
lemma p_eq_mul {j : ℕ} (hj : j ≤ C.k) : p = (2 * C.L ^ (C.mT + C.k - j) : ℕ) * C.a j := by
  refine C.p_eq.trans ?_
  unfold a aa
  have hL := C.L_pos
  push_cast
  rw [show C.mT + C.k - j = C.mT + (C.k - j) by omega, pow_add]
  field_simp
  rw [← pow_add, show C.k - j + j = C.k by omega]

lemma q_pos (j : ℕ) : 0 < 2 * C.L ^ (C.mT + C.k - j) := by
  have := C.three_le_L; positivity

lemma inLat_succ {j : ℕ} {c : Tor p} (hc : InLat (C.a (j + 1)) c) : InLat (C.a j) c := by
  intro ν
  obtain ⟨n, hn⟩ := hc ν
  refine ⟨n * C.L, ?_⟩
  rw [hn, ← C.L_mul_a]; push_cast; ring_nf

lemma Ω_zero : C.Ω 0 = univ := by simp [Ω, Om]

lemma Ω_top : C.Ω (C.k + 1) = ∅ := by simp [Ω, Om]

lemma Ω_of_pos {j : ℕ} (hj0 : j ≠ 0) (hjk : j ≤ C.k) :
    C.Ω j = ⋃ y ∈ C.S j, cell (C.a j) y := by
  simp [Ω, Om, hj0, hjk]

lemma isClosed_Ω (j : ℕ) : IsClosed (C.Ω j) := by
  unfold Ω Om
  split_ifs
  · exact isClosed_univ
  · exact isClosed_biUnion_finset fun y _ => isClosed_cell _ _
  · exact isClosed_empty

/-- The data of `lem:distance`. -/
def D : DomainData p where
  k := C.k
  Ω := C.Ω
  a := C.a
  Ω_zero := C.Ω_zero
  Ω_succ := C.Ω_succ
  Ω_closed := C.isClosed_Ω
  Ω_top := C.Ω_top
  a_pos := C.a_pos 0
  a_mono i j hij := by
    unfold a aa
    have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hL1 hij) (by positivity)
  a_top := by unfold a aa; have := C.L_pos; field_simp

/-- (F1) The cell of a point of `T^{(j)} ∩ Ω_j` lies in `Ω_j`. -/
lemma cell_subset_Ω {j : ℕ} {y : Tor p} (hy : InLat (C.a j) y) (hyΩ : y ∈ C.Ω j) :
    cell (C.a j) y ⊆ C.Ω j := by
  by_cases hj0 : j = 0
  · subst hj0; rw [C.Ω_zero]; exact subset_univ _
  by_cases hjk : j ≤ C.k
  · rw [C.Ω_of_pos hj0 hjk] at hyΩ ⊢
    obtain ⟨y'', hy''⟩ := mem_iUnion₂.mp hyΩ |>.imp fun y'' h => h
    obtain ⟨hmem, hcell⟩ := (by simpa using hyΩ : ∃ y'' ∈ C.S j, y ∈ cell (C.a j) y'')
    obtain ⟨y₁, hy₁S, hy₁⟩ := (by simpa using hyΩ : ∃ y'' ∈ C.S j, y ∈ cell (C.a j) y'')
    have e : y = y₁ := eq_of_lt (C.a_pos j) (C.q_pos j) (C.p_eq_mul hjk) hy (C.S_lat j y₁ hy₁S)
      (fun ν => lt_of_le_of_lt (hy₁ ν) (by linarith [C.a_pos j]))
    subst e
    exact subset_biUnion_of_mem (u := fun y => cell (C.a j) y) hy₁S
  · simp [Ω, Om, hj0, hjk] at hyΩ

/-- (F2) The open cell of a point of `T^{(i)}` outside `Ω_{i+1}` does not meet `Ω_{i+1}`. -/
lemma cellOpen_disjoint {i : ℕ} (hi : i ≤ C.k) {y : Tor p} (hy : InLat (C.a i) y)
    (hyΩ : y ∉ C.Ω (i + 1)) {z : Tor p} (hz : z ∈ cellOpen (C.a i) y) : z ∉ C.Ω (i + 1) := by
  intro hzΩ
  by_cases hik : i + 1 ≤ C.k
  · rw [C.Ω_of_pos (by omega) hik] at hzΩ
    obtain ⟨c, hcS, hzc⟩ := (by simpa using hzΩ : ∃ c ∈ C.S (i + 1), z ∈ cell (C.a (i + 1)) c)
    have hc : InLat (C.L * C.a i) c := by rw [C.L_mul_a]; exact C.S_lat (i + 1) c hcS
    have hzc' : z ∈ cell (C.L * C.a i) c := by rw [C.L_mul_a]; exact hzc
    obtain ⟨y', hy', hy'c, hzy'⟩ := cell_nest C.L_odd (C.a_pos i) hc hzc'
    -- `y' = y`: two points of `T^{(i)}` within `a_i`
    have e : y = y' := eq_of_lt (C.a_pos i) (C.q_pos i) (C.p_eq_mul hi) hy hy' fun ν => by
      have h1 := hz ν
      have h2 := hzy' ν
      calc ‖y ν - y' ν‖ = ‖(y ν - z ν) + (z ν - y' ν)‖ := by abel_nf
        _ ≤ ‖y ν - z ν‖ + ‖z ν - y' ν‖ := norm_add_le _ _
        _ < C.a i / 2 + C.a i / 2 := by rw [norm_sub_rev]; linarith
        _ = C.a i := by ring
    -- hence `y ∈ Ω_{i+1}`
    apply hyΩ
    rw [C.Ω_of_pos (by omega) hik]
    refine mem_biUnion hcS fun ν => ?_
    rw [e]
    have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
    have h := hy'c ν
    have : ((C.L : ℝ) - 1) / 2 * C.a i ≤ C.L * C.a i / 2 := by nlinarith [C.a_pos i]
    rw [← C.L_mul_a]; linarith
  · rw [show C.Ω (i + 1) = ∅ by simp [Ω, Om]; omega] at hzΩ
    exact hzΩ

/-- The scale of a point of the open cell of a point of the layer `Γ_i` is `i`. -/
lemma scale_cellOpen {i : ℕ} (hi : i ≤ C.k) {y : Tor p} (hy : InLat (C.a i) y)
    (hyΩ : y ∈ C.Ω i) (hyΩ1 : y ∉ C.Ω (i + 1)) {z : Tor p} (hz : z ∈ cellOpen (C.a i) y) :
    C.D.scale z = i :=
  C.D.scale_eq hi (C.cell_subset_Ω hy hyΩ fun ν => (hz ν).le) (C.cellOpen_disjoint hi hy hyΩ1 hz)

/-- The weighted distance from a point `y` of the layer `Γ_i` to a point of its cell is at most `2`:
on the straight segment the weight is `a_i⁻¹` except at the end, and the `ℓ¹`-length is at most `2a_i`. -/
theorem wdist_cell_le {i : ℕ} (hi : i ≤ C.k) {y : Tor p} (hy : InLat (C.a i) y)
    (hyΩ : y ∈ C.Ω i) (hyΩ1 : y ∉ C.Ω (i + 1)) {x : Tor p} (hx : x ∈ cell (C.a i) y) :
    wdist C.D y x ≤ ENNReal.ofReal 2 := by
  have ha := C.a_pos i
  choose n hn using hy
  set yh : Fin 4 → ℝ := fun ν => n ν * C.a i
  have hyh : projT p yh = y := by funext ν; simp [projT, yh, hn ν]
  obtain ⟨xh, hxh, hd⟩ := exists_close_lift (p := p) yh x
  set v : Fin 4 → ℝ := xh - yh
  have hv : ∀ ν, |v ν| ≤ C.a i / 2 := by
    intro ν
    simp only [v, Pi.sub_apply]
    rw [hd ν, show ((yh ν : ℝ) : AddCircle p) = y ν by rw [← hyh]; rfl]
    exact hx ν
  -- the straight path
  set γ : ℝ → (Fin 4 → ℝ) := fun t => yh + t • v
  have hlip : LipschitzWith ‖v‖₊ γ := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    simp only [γ, dist_eq_norm]
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, mul_comm]
    simp
  let P : TPath p y x :=
    { T := 1, T_nonneg := zero_le_one, γ := γ, K := ‖v‖₊, lip := hlip,
      start := by simp [γ, hyh], stop := by simp [γ, v, hxh] }
  refine (iInf_le _ P).trans ?_
  show wlen C.D γ 0 1 ≤ ENNReal.ofReal 2
  unfold wlen
  rw [setLIntegral_congr Ico_ae_eq_Icc.symm]
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, wIntegrand C.D γ t ≤ ENNReal.ofReal 2 := by
    intro t ht
    have hderiv : ∀ ν, deriv (fun s => γ s ν) t = v ν := by
      intro ν
      have : (fun s => γ s ν) = fun s => yh ν + s * v ν := by
        funext s; simp [γ]
      rw [this]
      simp
    -- the path stays in the open cell of `y`
    have hin : projT p (γ t) ∈ cellOpen (C.a i) y := by
      intro ν
      rw [← hyh]
      simp only [projT, γ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine lt_of_le_of_lt (norm_coe_sub_le _ _) ?_
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg ht.1]
      have h1 : t * |v ν| ≤ t * (C.a i / 2) := mul_le_mul_of_nonneg_left (hv ν) ht.1
      have h2 : t * (C.a i / 2) < C.a i / 2 := by nlinarith [ht.2]
      linarith
    have hw : C.D.weight (projT p (γ t)) = (C.a i)⁻¹ := by
      unfold DomainData.weight
      rw [C.scale_cellOpen hi (fun ν => ⟨n ν, hn ν⟩) hyΩ hyΩ1 hin]
      rfl
    unfold wIntegrand
    simp only [hderiv, hw, Real.eNorm_eq_ofReal_abs]
    rw [← ENNReal.ofReal_sum_of_nonneg fun ν _ => abs_nonneg _,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs : ∑ ν, |v ν| ≤ 2 * C.a i := by
      calc ∑ ν, |v ν| ≤ ∑ _ν : Fin 4, C.a i / 2 := Finset.sum_le_sum fun ν _ => hv ν
        _ = 2 * C.a i := by simp; ring
    rw [inv_mul_le_iff₀ ha]
    linarith
  calc ∫⁻ t in Ico (0 : ℝ) 1, wIntegrand C.D γ t
      ≤ ∫⁻ _t in Ico (0 : ℝ) 1, ENNReal.ofReal 2 := setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal 2 := by simp

end ContSeq

end Summation

end CoreLean
