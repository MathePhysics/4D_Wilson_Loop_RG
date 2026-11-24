/-
`lem:sf-one-layer` of BALABAN_CORE.tex (`aaaa938bb57d`) on the torus of `MomentumTorus.lean`: `T^{(0)} = (ℤ/nK)⁴` with
the spacing `a₀ = 1/n`, `n = 2r + 1`, the single layer `T^{(k)} = (ℤ/K)⁴` with `a_k = 1`, the trivial configuration,
`𝖺 = 1`, and the torus as the Dirichlet domain (the reduction of the core's proof to `j = k`, `a_k = 1`).

The projection `P` enters through two properties: (a) `Pf` lies in `G'(range Q'^*)`, written weakly as
`Σ_μ⟨∂_μλ, ∂_μv⟩₀ + ⟨Q'λ, Q'v⟩_k = ⟨Q'λ, ν⟩_k` for all `λ` (`WeakRange`), and (b) `‖Pf‖₀² = Re⟨Pf, f⟩₀`. Then

    ‖P∂^*A‖₀² ≤ C_ol(‖∂A‖₀² + Σ_y|(Q_kA)(y)|²)   (eq:sf-one-layer).

* `dstar`, `hat_dstar`: `∂^*A = Σ_μ∂^*_μA_μ` and its symbol `Σ_μ\overline{∂_μ(p)}Ã_μ(p)`.
* `parseval_inner`: `Σ_z\bar f g = N⁻⁴Σ_s\bar{\hat f}\hat g`.
* `fibre_eq`: on the fibre of `q`, `Δ(p' + l)a(l) = u_k(p' + l)κ(q)` for the normalised transform `a` of `v`.
* `one_layer`: the lemma.
-/
import CoreLean.MomentumTorus
import CoreLean.SFOneLayerFibre

open Real Complex Finset

noncomputable section

namespace CoreLean
namespace MomentumTorus

open TorusFourier MomentumSymbols MomentumMinimal SFOneLayer

variable (r K : ℕ) [NeZero K]

/-- `∂^*A = Σ_μ∂^*_μA_μ`, `(∂^*_μg)(z) = (g(z - a₀e_μ) - g(z))/a₀`. -/
def dstar (A : Fin 4 → Tor (NN r K) → ℂ) (z : Tor (NN r K)) : ℂ :=
  ∑ μ, ((2 * r + 1 : ℕ) : ℂ) * (A μ (z + -Pi.single μ 1) - A μ z)

lemma hat_dstar (A : Fin 4 → Tor (NN r K) → ℂ) (s : Tor (NN r K)) :
    hat (dstar r K A) s = ∑ μ, starRingEnd ℂ (dS r K s μ) * hat (A μ) s := by
  have h1 : ∀ μ, hat (fun z => ((2 * r + 1 : ℕ) : ℂ) * ((fun z => A μ (z + -Pi.single μ 1)) z - A μ z)) s =
      starRingEnd ℂ (dS r K s μ) * hat (A μ) s := by
    intro μ
    simp only [hat_smul, hat_sub, hat_shift]
    simp only [dS, map_mul, map_sub, map_one, map_natCast]
    rw [conj_ch, ch_neg_left]
    ring
  rw [← Finset.sum_congr rfl fun μ _ => h1 μ]
  unfold hat dstar
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- **Parseval's identity, polarised**: `Σ_z\overline{f(z)}g(z) = N⁻⁴Σ_s\overline{\hat f(s)}\hat g(s)`. -/
lemma parseval_inner {N : ℕ} [NeZero N] (f g : Tor N → ℂ) :
    ∑ z, starRingEnd ℂ (f z) * g z = ((N : ℂ) ^ 4)⁻¹ * ∑ s, starRingEnd ℂ (hat f s) * hat g s := by
  have h1 : ∑ z, starRingEnd ℂ (f z) * g z = ∑ z, starRingEnd ℂ (f z) * inv (hat g) z := by rw [inv_hat]
  rw [h1]
  unfold inv
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 : starRingEnd ℂ (hat f s) = ∑ z, ch s z * starRingEnd ℂ (f z) := by
    unfold hat
    rw [map_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [map_mul, conj_ch, neg_neg]
  rw [h2, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- `Σ_μ|∂_μ(p)|² = Δ(p)` at `s = Φ(q, m)`. -/
lemma sum_dS_sq (q : Tor K) (m : Fin 4 → ℤ) :
    ∑ μ, ‖dS r K (Phi r K q m) μ‖ ^ 2 = Del (2 * r + 1) (shift (pk K q) m) := by
  have h := nsq_dsym (2 * r + 1) (show 1 ≤ 2 * r + 1 by omega) (shift (pk K q) m)
  rw [← h]
  unfold MomentumMinimal.nsq
  refine Finset.sum_congr rfl fun μ _ => ?_
  unfold dS; rw [dS_Phi]

/-- `Q'_kχ_s = U(s)χ_{red s}`. -/
lemma Qpop_ch (s : Tor (NN r K)) (y : Tor K) : Qpop r K (ch s) y = Us r K s * ch (red r K s) y := by
  unfold Qpop Us
  simp only [ch_add_right, ch_emb]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- `∂_μχ_s = ∂_μ(s)χ_s`. -/
lemma d0_ch (μ : Fin 4) (s : Tor (NN r K)) (z : Tor (NN r K)) : d0 r K μ (ch s) z = dS r K s μ * ch s z := by
  unfold d0 dS; rw [ch_add_right]; ring

/-- The weak form of `v ∈ G'(range Q'^*)`: `Δ'v = Q'^*ν`, `Δ' = Σ_μ∂^*_μ∂_μ + Q'^*Q'`. -/
def WeakRange (v : Tor (NN r K) → ℂ) : Prop :=
  ∃ ν : Tor K → ℂ, ∀ lam : Tor (NN r K) → ℂ,
    ∑ μ, (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * ∑ z, starRingEnd ℂ (d0 r K μ lam z) * d0 r K μ v z +
      ∑ y, starRingEnd ℂ (Qpop r K lam y) * Qpop r K v y = ∑ y, starRingEnd ℂ (Qpop r K lam y) * ν y

/-- The transform of `v` on the fibre of `q`, `a(m) = n⁻⁴v̂(q̃ + Km)`. -/
def famv (v : Tor (NN r K) → ℂ) (q : Tor K) (m : Fin 4 → ℤ) : ℂ :=
  (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * hat v (Phi r K q m)

/-- `Σ_z\overline{∂_μχ_s}∂_μv = |∂_μ(s)|²v̂(s)`. -/
lemma test_d0 (μ : Fin 4) (s : Tor (NN r K)) (v : Tor (NN r K) → ℂ) :
    ∑ z, starRingEnd ℂ (d0 r K μ (ch s) z) * d0 r K μ v z = ((‖dS r K s μ‖ ^ 2 : ℝ) : ℂ) * hat v s := by
  have h1 : ∀ z, starRingEnd ℂ (d0 r K μ (ch s) z) * d0 r K μ v z =
      starRingEnd ℂ (dS r K s μ) * (ch (-s) z * d0 r K μ v z) := fun z => by
    rw [d0_ch, map_mul, conj_ch]; ring
  rw [Finset.sum_congr rfl fun z _ => h1 z, ← Finset.mul_sum]
  show starRingEnd ℂ (dS r K s μ) * hat (d0 r K μ v) s = _
  rw [hat_d0, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]

/-- `Σ_y\overline{Q'χ_s}ρ = u_k(p' + l)ρ̂(q)` at `s = Φ(q, m)`. -/
lemma test_Qpop (q : Tor K) (m : Fin 4 → ℤ) (ρ : Tor K → ℂ) :
    ∑ y, starRingEnd ℂ (Qpop r K (ch (Phi r K q m)) y) * ρ y = (uk (2 * r + 1) (shift (pk K q) m) : ℂ) * hat ρ q := by
  have h1 : ∀ y, starRingEnd ℂ (Qpop r K (ch (Phi r K q m)) y) * ρ y =
      (uk (2 * r + 1) (shift (pk K q) m) : ℂ) * (ch (-q) y * ρ y) := fun y => by
    rw [Qpop_ch, Us_Phi, red_Phi, map_mul, Complex.conj_ofReal, conj_ch]; ring
  rw [Finset.sum_congr rfl fun y _ => h1 y, ← Finset.mul_sum]
  rfl

/-- **The fibre equation**: `Δ(p' + l)a(l) = u_k(p' + l)κ(q)`. -/
lemma fibre_eq {v : Tor (NN r K) → ℂ} (hv : WeakRange r K v) :
    ∃ κ : Tor K → ℂ, ∀ q (m : Fin 4 → ℤ),
      (Del (2 * r + 1) (shift (pk K q) m) : ℂ) * famv r K v q m = (uk (2 * r + 1) (shift (pk K q) m) : ℂ) * κ q := by
  obtain ⟨ν, hν⟩ := hv
  refine ⟨fun q => hat ν q - hat (Qpop r K v) q, fun q m => ?_⟩
  have h := hν (ch (Phi r K q m))
  rw [Finset.sum_congr rfl fun μ _ => by rw [test_d0], test_Qpop, test_Qpop, ← Finset.mul_sum, ← Finset.sum_mul] at h
  have e3 : ∑ μ, ((‖dS r K (Phi r K q m) μ‖ ^ 2 : ℝ) : ℂ) = (Del (2 * r + 1) (shift (pk K q) m) : ℂ) := by
    rw [← sum_dS_sq r K q m]; push_cast; rfl
  rw [e3] at h
  unfold famv
  rw [mul_sub, ← h]
  ring

/-- `u_k(2πm) = 0` for `0 < |m_ν| ≤ r` in some direction: the zeros of `sin(p/2)`. -/
lemma uk_shift_zero {m : Fin 4 → ℤ} (hm : m ∈ MomentumSymbols.box r) (hm0 : m ≠ 0) :
    uk (2 * r + 1) (shift 0 m) = 0 := by
  obtain ⟨ν, hν⟩ : ∃ ν, m ν ≠ 0 := by by_contra h; push_neg at h; exact hm0 (funext h)
  unfold uk
  refine Finset.prod_eq_zero (Finset.mem_univ ν) ?_
  have hb := mem_box hm ν
  have hn : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  unfold uf
  have hden : Real.sin (shift 0 m ν / (2 * ((2 * r + 1 : ℕ) : ℝ))) ≠ 0 := by
    rw [Real.sin_ne_zero_iff]
    intro k hk
    simp only [shift, Pi.zero_apply, zero_add] at hk
    -- `kπ = πm/n` forces `m = kn`, impossible for `0 < |m| ≤ r < n`
    have hk' : (k : ℝ) * ((2 * r + 1 : ℕ) : ℝ) = (m ν : ℝ) := by
      have hπ := Real.pi_pos
      field_simp at hk
      nlinarith [hk]
    have hkz : k * (2 * r + 1 : ℤ) = m ν := by
      have : ((k * (2 * r + 1) : ℤ) : ℝ) = ((m ν : ℤ) : ℝ) := by push_cast at hk' ⊢; linarith
      exact_mod_cast this
    have : |m ν| < 2 * r + 1 := by have := hb; omega
    rcases lt_trichotomy k 0 with h | h | h
    · have : k * (2 * r + 1 : ℤ) ≤ -(2 * r + 1) := by nlinarith
      rw [abs_lt] at *; omega
    · subst h; simp at hkz; exact hν hkz.symm
    · have : (2 * r + 1 : ℤ) ≤ k * (2 * r + 1 : ℤ) := by nlinarith
      rw [abs_lt] at *; omega
  rw [if_neg hden]
  have hnum : Real.sin (shift 0 m ν / 2) = 0 := by
    rw [Real.sin_eq_zero_iff]
    exact ⟨m ν, by simp only [shift, Pi.zero_apply, zero_add]; ring⟩
  rw [hnum, zero_div]

lemma Phi_zero : Phi r K 0 0 = 0 := by
  funext i; simp [Phi, rep]

/-- `Σ_z|v(z)|² = K⁻⁴n⁴Σ_qΣ_m|a_q(m)|²`. -/
lemma norm_fibres (v : Tor (NN r K) → ℂ) :
    ∑ z, ‖v z‖ ^ 2 = ((K : ℝ) ^ 4)⁻¹ * ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
      ∑ q : Tor K, ∑ m : MomentumSymbols.box r, ‖famv r K v q m‖ ^ 2 := by
  rw [parseval, sum_Phi r K]
  have hn : ((2 * r + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have e : ∀ q (m : MomentumSymbols.box r), ‖hat v (Phi r K q m)‖ ^ 2 =
      (((2 * r + 1 : ℕ) : ℝ) ^ 4) ^ 2 * ‖famv r K v q m‖ ^ 2 := by
    intro q m
    unfold famv
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast, mul_pow, ← mul_assoc, inv_pow,
      mul_inv_cancel₀ (by positivity), one_mul]
  simp only [e, ← Finset.mul_sum]
  unfold NN; push_cast
  field_simp

/-- `Σ_z\bar vf = K⁻⁴n⁴Σ_qΣ_m\bar a_q(m)b_q(m)`. -/
lemma inner_fibres (v f : Tor (NN r K) → ℂ) :
    ∑ z, starRingEnd ℂ (v z) * f z = ((K : ℂ) ^ 4)⁻¹ * ((2 * r + 1 : ℕ) : ℂ) ^ 4 *
      ∑ q : Tor K, ∑ m : MomentumSymbols.box r, starRingEnd ℂ (famv r K v q m) * famv r K f q m := by
  rw [parseval_inner, sum_Phi r K]
  have hn : ((2 * r + 1 : ℕ) : ℂ) ≠ 0 := two_r_ne r
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have e : ∀ q (m : MomentumSymbols.box r), starRingEnd ℂ (hat v (Phi r K q m)) * hat f (Phi r K q m) =
      (((2 * r + 1 : ℕ) : ℂ) ^ 4) ^ 2 * (starRingEnd ℂ (famv r K v q m) * famv r K f q m) := by
    intro q m
    unfold famv
    simp only [map_mul, map_inv₀, map_pow, map_natCast]
    field_simp
  simp only [e, ← Finset.mul_sum]
  unfold NN; push_cast
  field_simp

/-- The fibre of `∂^*A`: `b_q(m) = Σ_μ\overline{∂_μ(p' + l)}a_q(m)_μ`. -/
lemma famv_dstar (A : Fin 4 → Tor (NN r K) → ℂ) (q : Tor K) (m : Fin 4 → ℤ) :
    famv r K (dstar r K A) q m = ∑ μ, starRingEnd ℂ (dsym (2 * r + 1) (shift (pk K q) m) μ) *
      ((((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * hat (A μ) (Phi r K q m)) := by
  unfold famv
  rw [hat_dstar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  unfold dS; rw [dS_Phi]; ring

set_option maxHeartbeats 2000000 in
/-- **`lem:sf-one-layer`** on the torus, `a_k = 1`: for `P` with (a) and (b), `‖P∂^*A‖₀² ≤ C_ol(‖∂A‖₀² + Σ_y|Q_kA|²)`. -/
theorem one_layer (P : (Tor (NN r K) → ℂ) → (Tor (NN r K) → ℂ)) (ha : ∀ f, WeakRange r K (P f))
    (hb : ∀ f, ∑ z, ‖P f z‖ ^ 2 = (∑ z, starRingEnd ℂ (P f z) * f z).re) (A : Fin 4 → Tor (NN r K) → ℂ) :
    (((2 * r + 1 : ℕ) : ℝ) ^ 4)⁻¹ * ∑ z, ‖P (dstar r K A) z‖ ^ 2 ≤
      Col * (energy0 r K A + ∑ μ, ∑ y, ‖Qop r K A μ y‖ ^ 2) := by
  have hπ := Real.pi_pos
  have hn : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  have hK : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  set f := dstar r K A
  set v := P f
  obtain ⟨κ, hκ⟩ := fibre_eq r K (ha f)
  set a : Tor K → (Fin 4 → ℤ) → Fin 4 → ℂ := fun q m μ => (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * hat (A μ) (Phi r K q m)
  -- the fibre vectors `g`
  set g : Tor K → MomentumSymbols.box r → ℂ := fun q l =>
    if q = 0 then (if (l : Fin 4 → ℤ) = 0 then 1 else 0)
    else ((uk (2 * r + 1) (shift (pk K q) l) / Del (2 * r + 1) (shift (pk K q) l) : ℝ) : ℂ)
  set c : Tor K → ℂ := fun q => if q = 0 then famv r K v 0 0 else κ q
  have hΔpos : ∀ q, ∀ m ∈ MomentumSymbols.box r, shift (pk K q) m ≠ 0 → 0 < Del (2 * r + 1) (shift (pk K q) m) :=
    fun q m hm hs => lt_of_lt_of_le (mul_pos (by positivity) (sum_sq_pos hs))
      (Del_ge (2 * r + 1) (by omega) (shift_range (fun μ => pk_le K q μ) hm))
  have hvg : ∀ q (l : MomentumSymbols.box r), famv r K v q l = c q * g q l := by
    intro q l
    by_cases hq : q = 0
    · subst hq
      simp only [c, g, if_true]
      by_cases hl : (l : Fin 4 → ℤ) = 0
      · rw [if_pos hl, mul_one, hl]
      · rw [if_neg hl, mul_zero]
        have h := hκ 0 l
        rw [pk_zero, uk_shift_zero r l.2 hl, Complex.ofReal_zero, zero_mul] at h
        have hD := hΔpos 0 l l.2 (by
          rw [pk_zero]; intro h0; apply hl; funext ν
          have := congrFun h0 ν; simp only [shift, Pi.zero_apply, zero_add] at this
          have : ((l : Fin 4 → ℤ) ν : ℝ) = 0 := by nlinarith
          exact_mod_cast this)
        rw [pk_zero] at hD
        exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast hD.ne')
    · simp only [c, g, if_neg hq]
      have hp0 : pk K q ≠ 0 := fun h => hq ((pk_eq_zero K q).1 h)
      have hD := hΔpos q l l.2 (shift_ne_zero (fun μ => pk_le K q μ) hp0 l)
      have h := hκ q l
      have hD' : ((Del (2 * r + 1) (shift (pk K q) l) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
      push_cast
      field_simp
      linear_combination h
  -- the projection step
  have hpf : ∑ q, ∑ l : MomentumSymbols.box r, ‖famv r K v q l‖ ^ 2 =
      (∑ q, ∑ l : MomentumSymbols.box r, starRingEnd ℂ (famv r K v q l) * famv r K f q l).re := by
    have h := hb f
    rw [norm_fibres, inner_fibres] at h
    have e : ((K : ℂ) ^ 4)⁻¹ * ((2 * r + 1 : ℕ) : ℂ) ^ 4 = ((((K : ℝ) ^ 4)⁻¹ * ((2 * r + 1 : ℕ) : ℝ) ^ 4 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul] at h
    exact mul_left_cancel₀ (by positivity) h
  have hproj := proj_fibre_bound g (fun q (l : MomentumSymbols.box r) => famv r K f q l)
    (fun q (l : MomentumSymbols.box r) => famv r K v q l) c hvg hpf
  -- the bound of each fibre
  set Kq : Tor K → ℝ := fun q => ∑ μ, ‖∑ m ∈ MomentumSymbols.box r, ((uk (2 * r + 1) (shift (pk K q) m) : ℝ) : ℂ) *
    vs (2 * r + 1) (shift (pk K q) m μ) * a q m μ‖ ^ 2
  set Eq : Tor K → ℝ := fun q => ∑ m ∈ MomentumSymbols.box r, (Del (2 * r + 1) (shift (pk K q) m) *
    ∑ μ, ‖a q m μ‖ ^ 2 - ‖∑ μ, starRingEnd ℂ (dsym (2 * r + 1) (shift (pk K q) m) μ) * a q m μ‖ ^ 2)
  have hE0 : ∀ q, 0 ≤ Eq q := fun q => sum_nonneg fun m _ => by
    have h := MomentumMinimal.lagrange (dsym (2 * r + 1) (shift (pk K q) m)) (a q m)
    rw [← nsq_dsym (2 * r + 1) (by omega)]
    show 0 ≤ nsq _ * nsq _ - ‖ip _ _‖ ^ 2
    rw [← h]; positivity
  have hK0 : ∀ q, 0 ≤ Kq q := fun q => sum_nonneg fun μ _ => sq_nonneg _
  have hterm : ∀ q, ‖∑ l : MomentumSymbols.box r, starRingEnd ℂ (g q l) * famv r K f q l‖ ^ 2 /
      ∑ l : MomentumSymbols.box r, ‖g q l‖ ^ 2 ≤ Col * (Kq q + Eq q) := by
    intro q
    by_cases hq : q = 0
    · subst hq
      have hz : ∑ l : MomentumSymbols.box r, starRingEnd ℂ (g 0 l) * famv r K f 0 l = 0 := by
        rw [Fintype.sum_eq_single ⟨0, zero_mem_box r⟩ (fun l hl => by
          have : (l : Fin 4 → ℤ) ≠ 0 := fun h => hl (Subtype.ext h)
          simp only [g, if_true, if_neg this, map_zero, zero_mul])]
        simp only [g, if_true, map_one, one_mul]
        rw [famv_dstar]
        refine Finset.sum_eq_zero fun μ _ => ?_
        simp [pk_zero, shift_zero, dsym_zero]
      rw [hz, norm_zero]
      have : 0 ≤ Col := by unfold Col g0; positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
      exact mul_nonneg this (add_nonneg (hK0 0) (hE0 0))
    · have hp0 : pk K q ≠ 0 := fun h => hq ((pk_eq_zero K q).1 h)
      have hF := one_layer_fibre r (fun μ => pk_le K q μ) hp0 (a q)
      have eg : ∀ l : MomentumSymbols.box r, starRingEnd ℂ (g q l) * famv r K f q l =
          ((uk (2 * r + 1) (shift (pk K q) l) / Del (2 * r + 1) (shift (pk K q) l) : ℝ) : ℂ) *
            ∑ μ, starRingEnd ℂ (dsym (2 * r + 1) (shift (pk K q) l) μ) * a q l μ := by
        intro l
        simp only [g, if_neg hq, Complex.conj_ofReal]
        rw [famv_dstar]
      have eG : ∀ l : MomentumSymbols.box r, ‖g q l‖ ^ 2 =
          (uk (2 * r + 1) (shift (pk K q) l) / Del (2 * r + 1) (shift (pk K q) l)) ^ 2 := by
        intro l
        simp only [g, if_neg hq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [Fintype.sum_congr _ _ eg, Fintype.sum_congr _ _ eG,
        Finset.sum_coe_sort (MomentumSymbols.box r) (fun m => ((uk (2 * r + 1) (shift (pk K q) m) /
          Del (2 * r + 1) (shift (pk K q) m) : ℝ) : ℂ) *
            ∑ μ, starRingEnd ℂ (dsym (2 * r + 1) (shift (pk K q) m) μ) * a q m μ),
        Finset.sum_coe_sort (MomentumSymbols.box r) (fun m => (uk (2 * r + 1) (shift (pk K q) m) /
          Del (2 * r + 1) (shift (pk K q) m)) ^ 2)]
      have hG : 0 < ∑ m ∈ MomentumSymbols.box r, (uk (2 * r + 1) (shift (pk K q) m) /
          Del (2 * r + 1) (shift (pk K q) m)) ^ 2 := by
        refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun m _ => sq_nonneg _) (zero_mem_box r))
        have hu : uk (2 * r + 1) (shift (pk K q) 0) ≠ 0 := by
          rw [shift_zero]; unfold uk
          refine Finset.prod_ne_zero_iff.2 fun ν _ => ?_
          have := uf_lower (2 * r + 1) (by omega) (pk_le K q ν)
          intro h; rw [h, abs_zero] at this; linarith [show (0 : ℝ) < 2 / π by positivity]
        have hD := hΔpos q 0 (zero_mem_box r) (shift_ne_zero (fun μ => pk_le K q μ) hp0 0)
        have hne : uk (2 * r + 1) (shift (pk K q) 0) / Del (2 * r + 1) (shift (pk K q) 0) ≠ 0 :=
          div_ne_zero hu hD.ne'
        positivity
      rw [div_le_iff₀ hG]
      exact hF
  -- the sums over the momenta
  have hKsum : ∑ q, Kq q = (K : ℝ) ^ 4 * ∑ μ, ∑ y, ‖Qop r K A μ y‖ ^ 2 := by
    have e : ∀ q μ, ∑ m ∈ MomentumSymbols.box r, ((uk (2 * r + 1) (shift (pk K q) m) : ℝ) : ℂ) *
        vs (2 * r + 1) (shift (pk K q) m μ) * a q m μ = hat (Qop r K A μ) q := by
      intro q μ
      rw [hat_Qop_fam, ← Finset.sum_coe_sort (MomentumSymbols.box r)]
      rfl
    simp only [Kq, e]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [parseval (Qop r K A μ)]
    field_simp
  have hEsum : ∑ q, Eq q = (K : ℝ) ^ 4 * energy0 r K A := by
    rw [energy0_fibre, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Eq]
    rw [← Finset.sum_coe_sort (MomentumSymbols.box r), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← nsq_dsym (2 * r + 1) (by omega)]
    show nsq _ * nsq _ - ‖ip _ _‖ ^ 2 = _
    rw [← MomentumMinimal.lagrange]
    rfl
  -- the conclusion
  rw [norm_fibres]
  have hS := hproj.trans (Finset.sum_le_sum fun q _ => hterm q)
  calc (((2 * r + 1 : ℕ) : ℝ) ^ 4)⁻¹ * (((K : ℝ) ^ 4)⁻¹ * ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
        ∑ q : Tor K, ∑ m : MomentumSymbols.box r, ‖famv r K v q m‖ ^ 2)
      = ((K : ℝ) ^ 4)⁻¹ * ∑ q : Tor K, ∑ m : MomentumSymbols.box r, ‖famv r K v q m‖ ^ 2 := by
        field_simp
    _ ≤ ((K : ℝ) ^ 4)⁻¹ * ∑ q, Col * (Kq q + Eq q) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = Col * (((K : ℝ) ^ 4)⁻¹ * ∑ q, Eq q + ((K : ℝ) ^ 4)⁻¹ * ∑ q, Kq q) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]; ring
    _ = _ := by
        rw [hKsum, hEsum, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul, one_mul]

end MomentumTorus
end CoreLean

end
