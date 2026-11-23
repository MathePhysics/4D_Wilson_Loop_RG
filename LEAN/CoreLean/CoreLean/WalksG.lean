/-
`thm:walks` of BALABAN_CORE.tex, the statements on `G'`, in abstract form: the argument of the core's proof,
with its inputs as hypotheses.

Setting. The cubes of `𝒟` form a finite type `D`. Operators are elements of a ring (for (ii), the continuous
linear maps of a finite-dimensional normed space, the `0`-forms on the Dirichlet domain); `Δ` is `Δ'_𝖺`, `h q`
the multiplication by `h_□`, `G q` the local operator `G'_□`.

* `first_remainder` (`eq:first-remainder-scalar`): with `K'(h) = hΔ'_𝖺 - Δ'_𝖺h` (the definition of `K'`:
  `Δ'_𝖺(hv) = hΔ'_𝖺v - K'(h)v`), the locality `h_□Δ'_𝖺G'_□h_□ = h_□²` (the step "the identity" of the proof:
  `Δ'_𝖺` and the local operator agree near the support of `h_□`, and `G'_□` inverts the latter) and
  `Σ_□ h_□² = 1`: `Δ'_𝖺G'_0 = I - R'`, `G'_0 = Σ_□ h_□G'_□h_□`, `R' = Σ_□ K'(h_□)G'_□h_□`.
* `series` ((ii)): if `‖R'‖ < 1`, then `Δ'_𝖺` is invertible and `G' = (Δ'_𝖺)⁻¹ = G'_0 Σ_{n≥0} R'ⁿ` (a right
  inverse is a two-sided one on a space of finite dimension).
* `walk_expansion` ((iii), the expansion): `G' = Σ_n Σ_{□₀} Σ_{□₁,…,□_n} h_{□₀}G'_{□₀}h_{□₀}
  K'(h_{□₁})G'_{□₁}h_{□₁}⋯K'(h_{□_n})G'_{□_n}h_{□_n}`, and `walk_term_eq_zero`: a term vanishes unless
  consecutive cubes meet, when `h_□K'(h_{□'})G'_{□'}h_{□'} = 0` for cubes which do not meet (the output of
  `K'(h_{□'})G'_{□'}h_{□'}` lies in `□'`).

* `walk_bound` (`eq:walk-bound`): from the block bounds of the factors (`FBound`: `eq:walk-first-factor` for
  `h_□G'_□h_□`, `lem:walk-factor`(iii) for `K'(h_□)G'_□h_□`) by the chain kernel (`chain_apply`) and its decay
  (`chain_kernel_le`: half of each exponential goes to `e^{-(δ/2)d(ω, y, y')}`, the other half is summed by
  `eq:summation` with `α = ½`, the last exponential bounded by one), with the core's constant `c₁(½, δ_sf)`;
  `d(ω, y, y')` enters as any lower bound of the lengths of the chains with `y_i ∈ □_i` (`IsLow`).
* `remainder_kernel` ((v) for `R'`), `remainder_norm_le` (`‖R'‖ ≤ 48C_fM⁻¹c₁` when the norm is the largest block
  norm), and `walks_G`, the assembly of (ii)–(v) for `G'`.

Not modelled: the holomorphy, the covariance, and the locality of the terms in the configuration ((iii), the
second and third sentences), the bounds of (iv) in the other norms of `thm:propagators`(iv)–(vi) and their
local form, the transposed terms `G'^T_ω`, and the statements on the block inverse and on `G` (proved in the core
after `lem:domain-difference` and `lem:block-interpolation`). The inputs `thm:small-field`,
`lem:cube-small-field`, `lem:walk-factor`, `lem:walk-small`, and `lem:partition-of-unity` are hypotheses.
-/
import CoreLean.WalkProduct

open Finset

noncomputable section

namespace CoreLean

namespace WalksG

section Algebra

variable {R : Type*} [Ring R] {D : Type*} [Fintype D]

/-- `K'(h) = hΔ'_𝖺 - Δ'_𝖺h`, so that `Δ'_𝖺(hv) = hΔ'_𝖺v - K'(h)v`. -/
def Kp (Δ h : R) : R := h * Δ - Δ * h

/-- `G'_0 = Σ_□ h_□G'_□h_□`. -/
def G0 (h G : D → R) : R := ∑ q, h q * G q * h q

/-- `R' = Σ_□ K'(h_□)G'_□h_□`. -/
def Rp (Δ : R) (h G : D → R) : R := ∑ q, Kp Δ (h q) * G q * h q

/-- `eq:first-remainder-scalar`: `Δ'_𝖺G'_0 = I - R'`. -/
theorem first_remainder (Δ : R) (h G : D → R) (hloc : ∀ q, h q * Δ * G q * h q = h q * h q)
    (hpart : ∑ q, h q * h q = 1) : Δ * G0 h G = 1 - Rp Δ h G := by
  simp only [G0, Rp, Finset.mul_sum, Kp]
  rw [← hpart, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← hloc q]
  noncomm_ring

/-- The `n`-th power of a sum is the sum of the ordered products over the sequences of length `n`. -/
lemma sum_pow (E : D → R) (n : ℕ) :
    (∑ q, E q) ^ n = ∑ f : Fin n → D, (List.ofFn fun i => E (f i)).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => D).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun f _ => ?_
    simp [Fin.consEquiv, List.ofFn_succ]

/-- The term of a walk `(□₀, □₁, …, □_n)`: `h_{□₀}G'_{□₀}h_{□₀}K'(h_{□₁})G'_{□₁}h_{□₁}⋯`. -/
def walkTerm (Δ : R) (h G : D → R) (q₀ : D) (l : List D) : R :=
  h q₀ * G q₀ * h q₀ * (l.map fun q => Kp Δ (h q) * G q * h q).prod

/-- `G'_0R'ⁿ` is the sum of the terms of the walks of length `n`. -/
lemma G0_mul_pow (Δ : R) (h G : D → R) (n : ℕ) :
    G0 h G * Rp Δ h G ^ n = ∑ q₀, ∑ f : Fin n → D, walkTerm Δ h G q₀ (List.ofFn f) := by
  rw [Rp, sum_pow, G0, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q₀ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [walkTerm, List.map_ofFn, Function.comp_def]

/-- The terms which are not walks vanish: if `h_□K'(h_{□'})G'_{□'}h_{□'} = 0` for cubes which do not meet, then
`h_qE_{q₁}⋯E_{q_n} = 0` unless `q, q₁, …, q_n` is a chain of meeting cubes. -/
lemma prod_eq_zero_of_not_chain (Δ : R) (h G : D → R) (meet : D → D → Prop)
    (hdisj : ∀ q q', ¬ meet q q' → h q * (Kp Δ (h q') * G q' * h q') = 0) :
    ∀ (l : List D) (q : D), ¬ List.IsChain meet (q :: l) →
      h q * (l.map fun q => Kp Δ (h q) * G q * h q).prod = 0
  | [], q, hc => absurd (List.isChain_singleton q) hc
  | q₁ :: l, q, hc => by
    rw [List.isChain_cons_cons] at hc
    simp only [List.map_cons, List.prod_cons]
    by_cases hm : meet q q₁
    · have hc' : ¬ List.IsChain meet (q₁ :: l) := fun h' => hc ⟨hm, h'⟩
      have ih := prod_eq_zero_of_not_chain Δ h G meet hdisj l q₁ hc'
      rw [show Kp Δ (h q₁) * G q₁ * h q₁ * (l.map fun q => Kp Δ (h q) * G q * h q).prod =
        Kp Δ (h q₁) * G q₁ * (h q₁ * (l.map fun q => Kp Δ (h q) * G q * h q).prod) by noncomm_ring,
        ih, mul_zero, mul_zero]
    · rw [← mul_assoc, hdisj q q₁ hm, zero_mul]

/-- `thm:walks`(iii): a term vanishes unless consecutive cubes of its sequence meet. -/
theorem walk_term_eq_zero (Δ : R) (h G : D → R) (meet : D → D → Prop)
    (hdisj : ∀ q q', ¬ meet q q' → h q * (Kp Δ (h q') * G q' * h q') = 0) (q₀ : D) (l : List D)
    (hc : ¬ List.IsChain meet (q₀ :: l)) : walkTerm Δ h G q₀ l = 0 := by
  rw [walkTerm, show h q₀ * G q₀ * h q₀ * (l.map fun q => Kp Δ (h q) * G q * h q).prod =
    h q₀ * G q₀ * (h q₀ * (l.map fun q => Kp Δ (h q) * G q * h q).prod) by noncomm_ring,
    prod_eq_zero_of_not_chain Δ h G meet hdisj l q₀ hc, mul_zero]

end Algebra

section Series

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {D : Type*} [Fintype D]

/-- A right inverse of a continuous linear map of a finite-dimensional space is a two-sided inverse. -/
lemma isUnit_of_mul_eq_one {A X : V →L[ℂ] V} (h : A * X = 1) : IsUnit A ∧ X * A = 1 := by
  have hsurj : Function.Surjective A := fun v => ⟨X v, by
    have := congrArg (fun T : V →L[ℂ] V => T v) h; simpa using this⟩
  have hinj : Function.Injective A :=
    (LinearMap.injective_iff_surjective (f := (A : V →ₗ[ℂ] V))).mpr hsurj
  have hXA : X * A = 1 := by
    ext v
    apply hinj
    have := congrArg (fun T : V →L[ℂ] V => T (A v)) h
    simpa using this
  exact ⟨⟨⟨A, X, h, hXA⟩, rfl⟩, hXA⟩

/-- `thm:walks`(ii) for `G'`: if `‖R'‖ < 1`, then `Δ'_𝖺` is invertible and `G' = G'_0 Σ_{n≥0} R'ⁿ`. -/
theorem series (Δ : V →L[ℂ] V) (h G : D → V →L[ℂ] V) (hloc : ∀ q, h q * Δ * G q * h q = h q * h q)
    (hpart : ∑ q, h q * h q = 1) (hR : ‖Rp Δ h G‖ < 1) :
    IsUnit Δ ∧ Ring.inverse Δ = G0 h G * ∑' n : ℕ, Rp Δ h G ^ n := by
  have hsum : Summable fun n : ℕ => Rp Δ h G ^ n := summable_geometric_of_norm_lt_one hR
  have hinv := (WalkProduct.one_sub_inverse (Rp Δ h G) hsum).2.1
  have hright : Δ * (G0 h G * ∑' n : ℕ, Rp Δ h G ^ n) = 1 := by
    rw [← mul_assoc, first_remainder Δ h G hloc hpart, hinv]
  obtain ⟨-, hleft⟩ := isUnit_of_mul_eq_one hright
  let u : (V →L[ℂ] V)ˣ := ⟨Δ, G0 h G * ∑' n : ℕ, Rp Δ h G ^ n, hright, hleft⟩
  exact ⟨u.isUnit, Ring.inverse_unit u⟩

/-- `thm:walks`(iii), the expansion: `G' = Σ_n Σ_{□₀} Σ_{□₁, …, □_n}` of the walk terms. -/
theorem walk_expansion (Δ : V →L[ℂ] V) (h G : D → V →L[ℂ] V)
    (hloc : ∀ q, h q * Δ * G q * h q = h q * h q) (hpart : ∑ q, h q * h q = 1) (hR : ‖Rp Δ h G‖ < 1) :
    Ring.inverse Δ = ∑' n : ℕ, ∑ q₀, ∑ f : Fin n → D, walkTerm Δ h G q₀ (List.ofFn f) := by
  rw [(series Δ h G hloc hpart hR).2]
  have hsum : Summable fun n : ℕ => Rp Δ h G ^ n := summable_geometric_of_norm_lt_one hR
  rw [← hsum.tsum_mul_left]
  exact tsum_congr fun n => G0_mul_pow Δ h G n

end Series

/-! ### (iv) and (v): the bounds -/

section Bounds

variable {β : Type*} [Fintype β] [DecidableEq β] {D V : Type*} (nrm : V → β → ℝ) (pts : D → Finset β)
  (d : β → β → ℝ) (δ : ℝ)

/-- The block bound of a factor in a cube (`def:block-bounds`, summed over the blocks of its argument): the
values vanish at the points of `𝐁` outside `X`, and at `y ∈ X` they are at most
`b(y)Σ_{z ∈ X} e^{-δd(y, z)}[μ]_z`. For `h_□G'_□h_□` this is `eq:walk-first-factor` (`b(y) = B_sf a_{j(y)}²`),
for `K'(h_□)G'_□h_□` it is `lem:walk-factor`(iii) (`b = C_fM⁻¹`). -/
def FBound (T : V → V) (X : Finset β) (b : β → ℝ) : Prop :=
  ∀ μ y, (y ∉ X → nrm (T μ) y = 0) ∧
    (y ∈ X → nrm (T μ) y ≤ b y * ∑ z ∈ X, Real.exp (-(δ * d y z)) * nrm μ z)

/-- `E_{q₁}(E_{q₂}(⋯E_{q_n}μ))`. -/
def applyE (E : D → V → V) : List D → V → V
  | [], μ => μ
  | q :: l, μ => E q (applyE E l μ)

/-- The last cube of the walk `(q, l)`. -/
def lastCube (q : D) : List D → D
  | [] => q
  | q' :: l => lastCube q' l

/-- The kernel of a chain through the cubes of `l`: `Σ_{y₁ ∈ □₁} ⋯ Σ_{y_n ∈ □_n}
e^{-δ(d(x, y₁) + d(y₁, y₂) + ⋯ + d(y_n, y'))}`. -/
def Kw : List D → β → β → ℝ
  | [], x, y' => Real.exp (-(δ * d x y'))
  | q :: l, x, y' => ∑ z ∈ pts q, Real.exp (-(δ * d x z)) * Kw l z y'

/-- `D₀` is at most the length `d(x, y₁) + ⋯ + d(y_n, y')` of every chain with `y_i ∈ □_i`; the core's
`d(ω, y, y')`, the infimum of these lengths, is such a number. -/
def IsLow : List D → β → β → ℝ → Prop
  | [], x, y', D₀ => D₀ ≤ d x y'
  | q :: l, x, y', D₀ => ∀ z ∈ pts q, IsLow l z y' (D₀ - d x z)

variable {nrm pts d δ}

/-- The factor bounds give the chain kernel: for the cube `q` whose points carry the argument,
`Σ_{z ∈ q} e^{-δd(x, z)}[E_{q₁}⋯E_{q_n}μ]_z ≤ bⁿ Σ_{y' ∈ q_n} K_l(x, y')[μ]_{y'}`. -/
lemma chain_apply (hn : ∀ v y, 0 ≤ nrm v y) (E : D → V → V) {b : ℝ} (hb : 0 ≤ b)
    (hE : ∀ q, FBound nrm d δ (E q) (pts q) fun _ => b) (μ : V) :
    ∀ (l : List D) (q : D) (x : β), ∑ z ∈ pts q, Real.exp (-(δ * d x z)) * nrm (applyE E l μ) z ≤
      b ^ l.length * ∑ y' ∈ pts (lastCube q l), Kw pts d δ l x y' * nrm μ y'
  | [], q, x => by simp [applyE, lastCube, Kw]
  | q₁ :: l, q, x => by
    set v := applyE E l μ
    set f : β → ℝ := fun z => Real.exp (-(δ * d x z)) * nrm (E q₁ v) z
    have hf0 : ∀ z, 0 ≤ f z := fun z => mul_nonneg (Real.exp_pos _).le (hn _ _)
    -- the values of `E_{q₁}` vanish outside `q₁`
    have h1 : ∑ z ∈ pts q, f z ≤ ∑ z ∈ pts q₁, f z := by
      rw [← Finset.sum_filter_of_ne (p := fun z => z ∈ pts q₁) fun z _ hz => by
        by_contra hz'
        exact hz (by simp only [f, ((hE q₁) v z).1 hz', mul_zero])]
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => (Finset.mem_filter.mp hz).2)
        fun z _ _ => hf0 z
    have h2 : ∀ z ∈ pts q₁, f z ≤ Real.exp (-(δ * d x z)) *
        (b * (b ^ l.length * ∑ y' ∈ pts (lastCube q₁ l), Kw pts d δ l z y' * nrm μ y')) := by
      intro z hz
      refine mul_le_mul_of_nonneg_left (((hE q₁) v z).2 hz |>.trans ?_) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (chain_apply hn E hb hE μ l q₁ z) hb
    simp only [applyE, lastCube, List.length_cons, Kw]
    refine h1.trans ((Finset.sum_le_sum h2).trans (le_of_eq ?_))
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun z _ => ?_
    ring

/-- The chain kernel decays with half the rate in the distance of the walk:
`K_l(x, y') ≤ c^{|l|}e^{-(δ/2)D₀}` for every lower bound `D₀` of the lengths of the chains, when
`Σ_z e^{-(δ/2)d(x, z)} ≤ c` (`eq:summation` with `α = ½` and the rate `δ`). -/
lemma chain_kernel_le (hd : ∀ y y', 0 ≤ d y y') (hδ : 0 < δ) {c : ℝ}
    (hsum : ∀ x, ∑ z, Real.exp (-(δ / 2 * d x z)) ≤ c) :
    ∀ (l : List D) (x y' : β) (D₀ : ℝ), IsLow pts d l x y' D₀ →
      Kw pts d δ l x y' ≤ c ^ l.length * Real.exp (-(δ / 2 * D₀))
  | [], x, y', D₀, h => by
    simp only [Kw, List.length_nil, pow_zero, one_mul]
    have := hd x y'
    exact Real.exp_le_exp.mpr (by simp only [IsLow] at h; nlinarith)
  | q :: l, x, y', D₀, h => by
    have hc : 0 ≤ c := (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans (hsum x)
    simp only [Kw, List.length_cons]
    calc ∑ z ∈ pts q, Real.exp (-(δ * d x z)) * Kw pts d δ l z y'
        ≤ ∑ z ∈ pts q, Real.exp (-(δ * d x z)) * (c ^ l.length * Real.exp (-(δ / 2 * (D₀ - d x z)))) :=
          Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left
            (chain_kernel_le hd hδ hsum l z y' (D₀ - d x z) (h z hz)) (Real.exp_pos _).le
      _ = c ^ l.length * Real.exp (-(δ / 2 * D₀)) * ∑ z ∈ pts q, Real.exp (-(δ / 2 * d x z)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          have e : Real.exp (-(δ * d x z)) * Real.exp (-(δ / 2 * (D₀ - d x z))) =
              Real.exp (-(δ / 2 * D₀)) * Real.exp (-(δ / 2 * d x z)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          calc Real.exp (-(δ * d x z)) * (c ^ l.length * Real.exp (-(δ / 2 * (D₀ - d x z))))
              = c ^ l.length * (Real.exp (-(δ * d x z)) * Real.exp (-(δ / 2 * (D₀ - d x z)))) := by ring
            _ = c ^ l.length * (Real.exp (-(δ / 2 * D₀)) * Real.exp (-(δ / 2 * d x z))) := by rw [e]
            _ = c ^ l.length * Real.exp (-(δ / 2 * D₀)) * Real.exp (-(δ / 2 * d x z)) := by ring
      _ ≤ c ^ l.length * Real.exp (-(δ / 2 * D₀)) * c :=
          mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => (Real.exp_pos _).le).trans (hsum x)) (by positivity)
      _ = c ^ (l.length + 1) * Real.exp (-(δ / 2 * D₀)) := by ring

/-- `eq:walk-bound`: for the walk `(□₀, □₁, …, □_n)` and `y ∈ □₀`,
`[G'_ωμ]_y ≤ b_F(y)(bc)ⁿ Σ_{y' ∈ □_n} e^{-(δ/2)d(ω, y, y')}[μ]_{y'}`, with `b_F(y) = B_sf a_{j(y)}²`,
`b = C_fM⁻¹`, `c = c₁(½, δ_sf)` (so `bc ≤ C_wM⁻¹`). -/
theorem walk_bound (hn : ∀ v y, 0 ≤ nrm v y) (hd : ∀ y y', 0 ≤ d y y') (hδ : 0 < δ)
    (F E : D → V → V) {bF : β → ℝ} (hbF : ∀ y, 0 ≤ bF y) {b c : ℝ} (hb : 0 ≤ b)
    (hF : ∀ q, FBound nrm d δ (F q) (pts q) bF) (hE : ∀ q, FBound nrm d δ (E q) (pts q) fun _ => b)
    (hsum : ∀ x, ∑ z, Real.exp (-(δ / 2 * d x z)) ≤ c) (q₀ : D) (l : List D) (μ : V) (y : β)
    (Dω : β → ℝ) (hD : ∀ y' ∈ pts (lastCube q₀ l), IsLow pts d l y y' (Dω y')) :
    nrm (F q₀ (applyE E l μ)) y ≤
      bF y * (b * c) ^ l.length * ∑ y' ∈ pts (lastCube q₀ l), Real.exp (-(δ / 2 * Dω y')) * nrm μ y' := by
  have hc : 0 ≤ c := (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans (hsum y)
  have hR : 0 ≤ bF y * (b * c) ^ l.length *
      ∑ y' ∈ pts (lastCube q₀ l), Real.exp (-(δ / 2 * Dω y')) * nrm μ y' :=
    mul_nonneg (mul_nonneg (hbF y) (pow_nonneg (mul_nonneg hb hc) _))
      (Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (hn _ _))
  by_cases hy : y ∈ pts q₀
  · refine (((hF q₀) (applyE E l μ) y).2 hy).trans ?_
    refine (mul_le_mul_of_nonneg_left (chain_apply hn E hb hE μ l q₀ y) (hbF y)).trans ?_
    have hK : ∑ y' ∈ pts (lastCube q₀ l), Kw pts d δ l y y' * nrm μ y' ≤
        c ^ l.length * ∑ y' ∈ pts (lastCube q₀ l), Real.exp (-(δ / 2 * Dω y')) * nrm μ y' := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y' hy' => ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (chain_kernel_le hd hδ hsum l y y' (Dω y') (hD y' hy')) (hn _ _)
    calc bF y * (b ^ l.length * ∑ y' ∈ pts (lastCube q₀ l), Kw pts d δ l y y' * nrm μ y')
        ≤ bF y * (b ^ l.length * (c ^ l.length *
            ∑ y' ∈ pts (lastCube q₀ l), Real.exp (-(δ / 2 * Dω y')) * nrm μ y')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK (pow_nonneg hb _)) (hbF y)
      _ = bF y * (b * c) ^ l.length *
            ∑ y' ∈ pts (lastCube q₀ l), Real.exp (-(δ / 2 * Dω y')) * nrm μ y' := by ring
  · rw [((hF q₀) (applyE E l μ) y).1 hy]
    exact hR

/-- `thm:walks`(v) for `R'`: if a point lies in at most `48` cubes and the block norms are subadditive, then
`[R'μ]_y ≤ 48b Σ_{y'} e^{-δd(y, y')}[μ]_{y'}`. -/
theorem remainder_kernel (hn : ∀ v y, 0 ≤ nrm v y) [Fintype D]
    (E : D → V → V) {b : ℝ}
    (hb : 0 ≤ b) (hE : ∀ q, FBound nrm d δ (E q) (pts q) fun _ => b) (μ : V) (y : β)
    (hcount : (Finset.univ.filter fun q => y ∈ pts q).card ≤ 48) :
    ∑ q, nrm (E q μ) y ≤ 48 * b * ∑ y', Real.exp (-(δ * d y y')) * nrm μ y' := by
  set S := ∑ y', Real.exp (-(δ * d y y')) * nrm μ y'
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (hn _ _)
  rw [← Finset.sum_filter_of_ne (p := fun q => y ∈ pts q) fun q _ hq => by
    by_contra h; exact hq ((hE q μ y).1 h)]
  calc ∑ q ∈ Finset.univ.filter (fun q => y ∈ pts q), nrm (E q μ) y
      ≤ ∑ q ∈ Finset.univ.filter (fun q => y ∈ pts q), b * S := by
        refine Finset.sum_le_sum fun q hq => ((hE q μ y).2 (Finset.mem_filter.mp hq).2).trans ?_
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => mul_nonneg (Real.exp_pos _).le (hn _ _)) hb
    _ = (Finset.univ.filter fun q => y ∈ pts q).card * (b * S) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 48 * (b * S) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (mul_nonneg hb hS)
    _ = 48 * b * S := by ring

end Bounds

/-! ### The assembly: `thm:walks`(ii)–(v) for `G'` -/

section Assembly

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {D : Type*} [Fintype D] {β : Type*} [Fintype β] [DecidableEq β]

/-- The factors as functions: `F_□ = h_□G'_□h_□`, `E_□ = K'(h_□)G'_□h_□`. -/
def Ffac (h G : D → V →L[ℂ] V) (q : D) : V → V := ⇑(h q * G q * h q)

def Efac (Δ : V →L[ℂ] V) (h G : D → V →L[ℂ] V) (q : D) : V → V := ⇑(Kp Δ (h q) * G q * h q)

/-- The term of a walk applied to `μ` is the composition of its factors. -/
lemma walkTerm_apply (Δ : V →L[ℂ] V) (h G : D → V →L[ℂ] V) (q₀ : D) (l : List D) (μ : V) :
    walkTerm Δ h G q₀ l μ = Ffac h G q₀ (applyE (Efac Δ h G) l μ) := by
  have key : ∀ (l : List D) (μ : V),
      (l.map fun q => Kp Δ (h q) * G q * h q).prod μ = applyE (Efac Δ h G) l μ := by
    intro l
    induction l with
    | nil => intro μ; simp [applyE]
    | cons q l ih =>
      intro μ
      simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply, applyE, Efac]
      rw [ih]
  rw [walkTerm, ContinuousLinearMap.mul_apply, key, Ffac]

/-- `‖R'‖ ≤ 48bc` from the bounds of the factors, when the norm is the largest block norm, the block norms are
subadditive, a point lies in at most `48` cubes, and `Σ_{y'} e^{-δd(y, y')} ≤ c`. -/
theorem remainder_norm_le (nrm : V → β → ℝ) (hn : ∀ v y, 0 ≤ nrm v y) (hle : ∀ v y, nrm v y ≤ ‖v‖)
    (hsup : ∀ v C, 0 ≤ C → (∀ y, nrm v y ≤ C) → ‖v‖ ≤ C)
    (hsub : ∀ (g : D → V) (y : β), nrm (∑ q, g q) y ≤ ∑ q, nrm (g q) y)
    (pts : D → Finset β) (d : β → β → ℝ) (δ : ℝ) (Δ : V →L[ℂ] V) (h G : D → V →L[ℂ] V) {b c : ℝ}
    (hb : 0 ≤ b) (hE : ∀ q, FBound nrm d δ (Efac Δ h G q) (pts q) fun _ => b)
    (hcount : ∀ y, (Finset.univ.filter fun q => y ∈ pts q).card ≤ 48)
    (hsum : ∀ y, ∑ y', Real.exp (-(δ * d y y')) ≤ c) (hc : 0 ≤ c) :
    ‖Rp Δ h G‖ ≤ 48 * b * c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => hsup _ _ (by positivity) fun y => ?_
  have hR : Rp Δ h G v = ∑ q, Efac Δ h G q v := by
    simp only [Rp, ContinuousLinearMap.coe_sum', Finset.sum_apply, Efac]
  rw [hR]
  refine (hsub _ y).trans ((remainder_kernel hn (Efac Δ h G) hb hE v y (hcount y)).trans ?_)
  have hS : ∑ y', Real.exp (-(δ * d y y')) * nrm v y' ≤ c * ‖v‖ :=
    calc ∑ y', Real.exp (-(δ * d y y')) * nrm v y' ≤ ∑ y', Real.exp (-(δ * d y y')) * ‖v‖ :=
          Finset.sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left (hle v y') (Real.exp_pos _).le
      _ = (∑ y', Real.exp (-(δ * d y y'))) * ‖v‖ := by rw [Finset.sum_mul]
      _ ≤ c * ‖v‖ := mul_le_mul_of_nonneg_right (hsum y) (norm_nonneg _)
  calc 48 * b * ∑ y', Real.exp (-(δ * d y y')) * nrm v y' ≤ 48 * b * (c * ‖v‖) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 48 * b * c * ‖v‖ := by ring

/-- `thm:walks`(ii)–(v) for `G'`, in abstract form. Inputs: the locality `h_□Δ'_𝖺G'_□h_□ = h_□²` and
`Σ_□ h_□² = 1`; the bounds of the factors (`eq:walk-first-factor` with `b_F(y) = B_sf a_{j(y)}²`,
`lem:walk-factor`(iii) with `b = C_fM⁻¹`); the norm as the largest block norm, with subadditive block norms; at
most `48` cubes at a point; `eq:summation` (`Σ_{y'} e^{-(δ/2)d(y, y')} ≤ c`, `c = c₁(½, δ_sf)`); and
`48bc < 1` (the core's `48C_fc₁M⁻¹ ≤ C_wM⁻¹ ≤ ½`). Then `Δ'_𝖺` is invertible, `G' = Σ_n Σ_{□₀} Σ_{□₁, …, □_n}`
of the walk terms, the terms whose consecutive cubes do not meet vanish (when `h_□E_{□'} = 0` for cubes which do
not meet), every walk term satisfies `eq:walk-bound`, and `‖R'‖ ≤ 48bc`. -/
theorem walks_G (Δ : V →L[ℂ] V) (h G : D → V →L[ℂ] V) (hloc : ∀ q, h q * Δ * G q * h q = h q * h q)
    (hpart : ∑ q, h q * h q = 1) (nrm : V → β → ℝ) (hn : ∀ v y, 0 ≤ nrm v y)
    (hle : ∀ v y, nrm v y ≤ ‖v‖) (hsup : ∀ v C, 0 ≤ C → (∀ y, nrm v y ≤ C) → ‖v‖ ≤ C)
    (hsub : ∀ (g : D → V) (y : β), nrm (∑ q, g q) y ≤ ∑ q, nrm (g q) y)
    (pts : D → Finset β) (d : β → β → ℝ) (hd : ∀ y y', 0 ≤ d y y') {δ : ℝ} (hδ : 0 < δ)
    {bF : β → ℝ} (hbF : ∀ y, 0 ≤ bF y) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hF : ∀ q, FBound nrm d δ (Ffac h G q) (pts q) bF)
    (hE : ∀ q, FBound nrm d δ (Efac Δ h G q) (pts q) fun _ => b)
    (hcount : ∀ y, (Finset.univ.filter fun q => y ∈ pts q).card ≤ 48)
    (hsum : ∀ x, ∑ z, Real.exp (-(δ / 2 * d x z)) ≤ c) (hsmall : 48 * b * c < 1) :
    IsUnit Δ ∧
      Ring.inverse Δ = ∑' n : ℕ, ∑ q₀, ∑ f : Fin n → D, walkTerm Δ h G q₀ (List.ofFn f) ∧
      ‖Rp Δ h G‖ ≤ 48 * b * c ∧
      ∀ (q₀ : D) (l : List D) (μ : V) (y : β) (Dω : β → ℝ),
        (∀ y' ∈ pts (lastCube q₀ l), IsLow pts d l y y' (Dω y')) →
        nrm (walkTerm Δ h G q₀ l μ) y ≤
          bF y * (b * c) ^ l.length *
            ∑ y' ∈ pts (lastCube q₀ l), Real.exp (-(δ / 2 * Dω y')) * nrm μ y' := by
  have hsumδ : ∀ y, ∑ y', Real.exp (-(δ * d y y')) ≤ c := fun y =>
    (Finset.sum_le_sum fun y' _ => Real.exp_le_exp.mpr (by nlinarith [hd y y'])).trans (hsum y)
  have hR := remainder_norm_le nrm hn hle hsup hsub pts d δ Δ h G hb hE hcount hsumδ hc
  have hR1 : ‖Rp Δ h G‖ < 1 := lt_of_le_of_lt hR hsmall
  refine ⟨(series Δ h G hloc hpart hR1).1, walk_expansion Δ h G hloc hpart hR1, hR,
    fun q₀ l μ y Dω hD => ?_⟩
  rw [walkTerm_apply]
  exact walk_bound hn hd hδ (Ffac h G) (Efac Δ h G) hbF hb hF hE hsum q₀ l μ y Dω hD

end Assembly

end WalksG

end CoreLean
