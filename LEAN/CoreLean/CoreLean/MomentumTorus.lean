/-
`prop:momentum-space`(iv) of BALABAN_CORE.tex (`eeb72a15761f`) on the tori. With `n = L^k = 2r + 1` and `K = ℓ_𝕋` (the side
of the torus in the units `a_k = 1`), the lattice `T^{(0)}` of the spacing `a₀ = 1/n` is `(ℤ/nK)⁴` and `T^{(k)}` is `(ℤ/K)⁴`,
embedded by `y ↦ ny`. By part (i) (`Q_trivial_levels`, `Qprime_trivial`), `Q_k = Q_k(id)` is the mean over the block
`B^k(y)` of the means along the straight paths of `n` bonds; this is the operator `Qop` below. The momenta of `T^{(k)}` are
`p' = 2πq̃/K` with `q̃` the centred representative of `q ∈ (ℤ/K)⁴`, and those of `T^{(0)}` are `p' + 2πm`, `|m_μ| ≤ r`: the
map `(q, m) ↦ q̃ + Km` is a bijection `(ℤ/K)⁴ × box(r) → (ℤ/nK)⁴` (`Phi_bij`).
-/
import CoreLean.TorusFourier
import CoreLean.MomentumFibre

open Real Complex

noncomputable section

namespace CoreLean
namespace MomentumTorus

open TorusFourier MomentumSymbols MomentumMinimal

variable (r K : ℕ) [NeZero K]

/-- The number of sites of `T^{(0)}` along a side, `nK`. -/
abbrev NN : ℕ := (2 * r + 1) * K

instance NN_neZero : NeZero (NN r K) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne K)⟩

/-- The embedding `T^{(k)} → T^{(0)}`, `y ↦ ny`. -/
def emb (y : Tor K) : Tor (NN r K) := fun i => ((2 * r + 1 : ℕ) : ZMod (NN r K)) * (((y i).val : ℕ) : ZMod (NN r K))

/-- The reduction of the momenta of `T^{(0)}` to those of `T^{(k)}`. -/
def red (s : Tor (NN r K)) : Tor K := fun i => (((s i).val : ℕ) : ZMod K)

/-- `χ_s(ny) = χ_{red s}(y)`. -/
lemma ch_emb (s : Tor (NN r K)) (y : Tor K) : ch s (emb r K y) = ch (red r K s) y := by
  unfold ch emb red
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : s i * (((2 * r + 1 : ℕ) : ZMod (NN r K)) * (((y i).val : ℕ) : ZMod (NN r K))) =
      ((((s i).val * (2 * r + 1) * (y i).val : ℕ) : ℤ) : ZMod (NN r K)) := by
    push_cast; rw [ZMod.natCast_zmod_val]; ring
  have h2 : (((s i).val : ℕ) : ZMod K) * y i = ((((s i).val * (y i).val : ℕ) : ℤ) : ZMod K) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, h2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have hn : (2 * (r : ℂ) + 1) ≠ 0 := by
    have : (2 * (r : ℂ) + 1) = ((2 * r + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact Nat.cast_ne_zero.2 (by omega)
  unfold NN
  push_cast
  field_simp

/-- The centred representative `q̃` of `q`. -/
def rep (q : Tor K) (i : Fin 4) : ℤ := (q i).valMinAbs

/-- The momentum `p' = 2πq̃/K ∈ [-π, π]⁴`. -/
def pk (q : Tor K) : Fin 4 → ℝ := fun i => 2 * π * (rep K q i : ℝ) / K

lemma pk_le (q : Tor K) (i : Fin 4) : |pk K q i| ≤ π := by
  have hK : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have h := ZMod.natAbs_valMinAbs_le (q i)
  have h2 : |(rep K q i : ℝ)| ≤ K / 2 := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    have : ((q i).valMinAbs.natAbs : ℝ) ≤ ((K / 2 : ℕ) : ℝ) := by exact_mod_cast h
    have h3 : ((K / 2 : ℕ) : ℝ) ≤ (K : ℝ) / 2 := by
      have := Nat.cast_div_le (m := K) (n := 2) (α := ℝ); simpa using this
    exact this.trans h3
  unfold pk
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_pos hK, div_le_iff₀ hK]
  nlinarith [Real.pi_pos]

lemma pk_eq_zero (q : Tor K) : pk K q = 0 ↔ q = 0 := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  constructor
  · intro h
    funext i
    have := congrFun h i
    simp only [pk, Pi.zero_apply, div_eq_zero_iff, mul_eq_zero, hK, or_false] at this
    rcases this with (h1 | h1) | h1
    · norm_num at h1
    · exact absurd h1 Real.pi_ne_zero
    · rw [Pi.zero_apply, ← ZMod.valMinAbs_eq_zero]; exact_mod_cast h1
  · rintro rfl; funext i; simp [pk, rep]

/-- `Φ(q, m) = q̃ + Km`. -/
def Phi (q : Tor K) (m : Fin 4 → ℤ) : Tor (NN r K) := fun i => ((rep K q i + K * m i : ℤ) : ZMod (NN r K))

lemma red_Phi (q : Tor K) (m : Fin 4 → ℤ) : red r K (Phi r K q m) = q := by
  funext i
  unfold red Phi
  rw [← ZMod.cast_eq_val, ZMod.cast_intCast (Dvd.intro_left _ rfl)]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero]
  exact ZMod.coe_valMinAbs _

lemma Phi_injective : Function.Injective (fun p : Tor K × box r => Phi r K p.1 p.2) := by
  rintro ⟨q, m, hm⟩ ⟨q', m', hm'⟩ h
  simp only at h
  have hq : q = q' := by
    have := congrArg (red r K) h
    rwa [red_Phi, red_Phi] at this
  subst hq
  have hmm : m = m' := by
    funext i
    have hi := congrFun h i
    unfold Phi at hi
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    have hd : ((2 * r + 1 : ℕ) : ℤ) * K ∣ K * (m' i - m i) := by
      have e : rep K q i + K * m' i - (rep K q i + K * m i) = K * (m' i - m i) := by ring
      rw [← e]; exact_mod_cast hi
    have hd' : ((2 * r + 1 : ℕ) : ℤ) ∣ m' i - m i := by
      rw [mul_comm] at hd
      exact (mul_dvd_mul_iff_left (by exact_mod_cast NeZero.ne K)).1 hd
    have b1 := mem_box hm i
    have b2 := mem_box hm' i
    have hlt : (m' i - m i).natAbs < ((2 * r + 1 : ℕ) : ℤ).natAbs := by
      obtain ⟨c1, c2⟩ := abs_le.1 b1
      obtain ⟨c3, c4⟩ := abs_le.1 b2
      omega
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd' hlt
    linarith
  subst hmm
  rfl

lemma card_box : Fintype.card (box r) = (2 * r + 1) ^ 4 := by
  rw [Fintype.card_coe, box, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

lemma Phi_bij : Function.Bijective (fun p : Tor K × box r => Phi r K p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨Phi_injective r K, ?_⟩
  rw [Fintype.card_prod, card_box, Fintype.card_fun, Fintype.card_fun, ZMod.card, ZMod.card, Fintype.card_fin]
  unfold NN; ring

/-- `Σ_sf(s) = Σ_qΣ_mf(q̃ + Km)`. -/
lemma sum_Phi {M : Type*} [AddCommMonoid M] (f : Tor (NN r K) → M) :
    ∑ s, f s = ∑ q : Tor K, ∑ m : box r, f (Phi r K q m) := by
  rw [← (Equiv.ofBijective _ (Phi_bij r K)).sum_comp, Fintype.sum_prod_type]
  rfl

/-! ### The symbols at `Φ(q, m)` -/

lemma ch_single {M : ℕ} [NeZero M] (s : Tor M) (μ : Fin 4) (c : ZMod M) :
    ch s (Pi.single μ c) = ZMod.stdAddChar (s μ * c) := by
  unfold ch
  rw [Finset.prod_eq_single μ (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero, AddChar.map_zero_eq_one])
    (by simp), Pi.single_eq_same]

lemma two_r_ne (r : ℕ) : ((2 * r + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)

/-- `n(χ_{Φ(q,m)}(e_μ) - 1) = ∂_μ(p' + 2πm)`. -/
lemma dS_Phi (q : Tor K) (m : Fin 4 → ℤ) (μ : Fin 4) :
    ((2 * r + 1 : ℕ) : ℂ) * (ch (Phi r K q m) (Pi.single μ 1) - 1) = dsym (2 * r + 1) (shift (pk K q) m) μ := by
  rw [ch_single, mul_one]
  unfold dsym Phi
  rw [ZMod.stdAddChar_coe]
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have hn := two_r_ne r
  have hexp : 2 * π * I * ((rep K q μ + K * m μ : ℤ) : ℂ) / ((NN r K : ℕ) : ℂ) =
      I * (((1 / ((2 * r + 1 : ℕ) : ℝ)) * shift (pk K q) m μ : ℝ) : ℂ) := by
    unfold NN shift pk
    push_cast at hn ⊢
    field_simp
  rw [hexp]
  push_cast at hn ⊢
  field_simp

/-- `χ_q(e_μ) - 1 = ∂¹_μ(p')` on `T^{(k)}`. -/
lemma d1S (q : Tor K) (μ : Fin 4) : ch q (Pi.single μ 1) - 1 = d1sym (pk K q) μ := by
  rw [ch_single, mul_one]
  unfold d1sym pk
  conv_lhs => rw [← ZMod.coe_valMinAbs (q μ)]
  rw [ZMod.stdAddChar_coe]
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  congr 2
  unfold rep
  push_cast
  field_simp

/-- `Σ_{|j| ≤ r}f(j) = Σ_{t < 2r+1}f(t - r)`. -/
lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ j ∈ Finset.Icc (-(r : ℤ)) r, f j = ∑ t ∈ Finset.range (2 * r + 1), f ((t : ℤ) - r) := by
  refine Finset.sum_nbij' (fun j => (j + r).toNat) (fun t => (t : ℤ) - r) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_coe] at hj ⊢; omega
  · intro t ht; simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_coe] at ht ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_coe] at hj; omega
  · intro t ht; omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    congr 1; omega

/-- The embedding of the offsets `w ∈ ℤ⁴` in `T^{(0)}`. -/
def castw (w : Fin 4 → ℤ) : Tor (NN r K) := fun i => (w i : ZMod (NN r K))

/-- The block mean of the characters, `U(s) = n⁻⁴Σ_{w ∈ box}χ_s(w)`. -/
def Us (s : Tor (NN r K)) : ℂ := (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * ∑ w ∈ box r, ch s (castw r K w)

/-- The path mean of the characters, `V_μ(s) = n⁻¹Σ_{t < n}χ_s(te_μ)`. -/
def Vs (s : Tor (NN r K)) (μ : Fin 4) : ℂ :=
  ((2 * r + 1 : ℕ) : ℂ)⁻¹ * ∑ t ∈ Finset.range (2 * r + 1), ch s (Pi.single μ (t : ZMod (NN r K)))

lemma Vs_Phi (q : Tor K) (m : Fin 4 → ℤ) (μ : Fin 4) :
    Vs r K (Phi r K q m) μ = vs (2 * r + 1) (shift (pk K q) m μ) := by
  rw [← path_mean (2 * r + 1) (by omega)]
  unfold Vs
  rw [one_div]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ch_single]
  unfold Phi
  rw [show ((rep K q μ + K * m μ : ℤ) : ZMod (NN r K)) * ((t : ℕ) : ZMod (NN r K)) =
    (((rep K q μ + K * m μ) * t : ℤ) : ZMod (NN r K)) by push_cast; ring, ZMod.stdAddChar_coe]
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have hn := two_r_ne r
  congr 1
  unfold NN shift pk
  push_cast at hn ⊢
  field_simp

/-- `U(s) = ∏_i n⁻¹Σ_{|j| ≤ r}e(s_ij)`. -/
lemma Us_eq (s : Tor (NN r K)) :
    Us r K s = ∏ i, (((2 * r + 1 : ℕ) : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(r : ℤ)) r,
      ZMod.stdAddChar (s i * (j : ZMod (NN r K)))) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  unfold Us
  congr 1
  rw [Finset.prod_univ_sum (fun _ => Finset.Icc (-(r : ℤ)) r)
    (fun i (j : ℤ) => ZMod.stdAddChar (s i * (j : ZMod (NN r K))))]
  rfl

lemma Us_Phi (q : Tor K) (m : Fin 4 → ℤ) :
    Us r K (Phi r K q m) = (uk (2 * r + 1) (shift (pk K q) m) : ℂ) := by
  rw [Us_eq, uk, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sum_Icc_eq_range r, ← dirichlet_mean r (shift (pk K q) m i), one_div]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold Phi
  rw [← Int.cast_mul, ZMod.stdAddChar_coe]
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have hn := two_r_ne r
  congr 1
  unfold NN shift pk
  push_cast at hn ⊢
  field_simp

/-! ### The operators and their transforms -/

/-- `(∂_μf)(z) = (f(z + a₀e_μ) - f(z))/a₀` on `T^{(0)}`, `a₀ = 1/n`. -/
def d0 (μ : Fin 4) (f : Tor (NN r K) → ℂ) (z : Tor (NN r K)) : ℂ :=
  ((2 * r + 1 : ℕ) : ℂ) * (f (z + Pi.single μ 1) - f z)

/-- `(∂¹_μg)(y) = g(y + e_μ) - g(y)` on `T^{(k)}`. -/
def d1 (μ : Fin 4) (g : Tor K → ℂ) (y : Tor K) : ℂ := g (y + Pi.single μ 1) - g y

/-- `Q_k = Q_k(id)`: the mean over the block `B^k(y)` of the means along the straight paths of `n` bonds. -/
def Qop (A : Fin 4 → Tor (NN r K) → ℂ) (μ : Fin 4) (y : Tor K) : ℂ :=
  (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * ∑ w ∈ box r, (((2 * r + 1 : ℕ) : ℂ)⁻¹ *
    ∑ t ∈ Finset.range (2 * r + 1), A μ (emb r K y + castw r K w + Pi.single μ (t : ZMod (NN r K))))

/-- The symbol `n(χ_s(e_μ) - 1)` of `∂_μ`. -/
def dS (s : Tor (NN r K)) (μ : Fin 4) : ℂ := ((2 * r + 1 : ℕ) : ℂ) * (ch s (Pi.single μ 1) - 1)

lemma hat_d0 (μ : Fin 4) (f : Tor (NN r K) → ℂ) (s : Tor (NN r K)) :
    hat (d0 r K μ f) s = dS r K s μ * hat f s := by
  have h1 : d0 r K μ f = fun z => ((2 * r + 1 : ℕ) : ℂ) * ((fun z => f (z + Pi.single μ 1)) z - f z) := rfl
  simp only [h1, hat_smul, hat_sub, hat_shift, dS]
  ring

lemma hat_d1 (μ : Fin 4) (g : Tor K → ℂ) (q : Tor K) :
    hat (d1 K μ g) q = d1sym (pk K q) μ * hat g q := by
  have h1 : d1 K μ g = fun y => (fun y => g (y + Pi.single μ 1)) y - g y := rfl
  simp only [h1, hat_sub, hat_shift, ← d1S K q μ]
  ring

/-- **`Q_k` in momentum space**: `Q_kA_μ(y) = (nK)⁻⁴Σ_sχ_{red s}(y)U(s)V_μ(s)Â_μ(s)`. -/
lemma Qop_spec (A : Fin 4 → Tor (NN r K) → ℂ) (μ : Fin 4) (y : Tor K) :
    Qop r K A μ y = (((NN r K : ℕ) : ℂ) ^ 4)⁻¹ *
      ∑ s, ch (red r K s) y * (Us r K s * Vs r K s μ * hat (A μ) s) := by
  have hA : ∀ z, A μ z = (((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, ch s z * hat (A μ) s := fun z => by
    conv_lhs => rw [← inv_hat (A μ)]
    rfl
  unfold Qop Us Vs
  simp only [hA, ch_add_right, ch_emb, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => arg 2; ext w; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext s; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun w _ => ?_
  ring

/-- **The transform of `Q_kA`**: `(Q_kA_μ)^(q) = n⁻⁴Σ_{m ∈ box}U V_μ Â_μ(q̃ + Km)`. -/
lemma hat_Qop (A : Fin 4 → Tor (NN r K) → ℂ) (μ : Fin 4) (q : Tor K) :
    hat (Qop r K A μ) q = (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ *
      ∑ m : box r, Us r K (Phi r K q m) * Vs r K (Phi r K q m) μ * hat (A μ) (Phi r K q m) := by
  set X : Tor (NN r K) → ℂ := fun s => Us r K s * Vs r K s μ * hat (A μ) s with hX
  have h1 : Qop r K A μ = fun y => (((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, ch (red r K s) y * X s :=
    funext (Qop_spec r K A μ)
  rw [h1]
  conv_lhs => unfold hat
  have h2 : ∀ y, ch (-q) y * ((((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, ch (red r K s) y * X s) =
      (((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, X s * ch (red r K s - q) y := by
    intro y
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sub_eq_add_neg, ch_add_left]; ring
  simp only [h2]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, orth, sub_eq_zero, mul_ite, mul_zero]
  rw [sum_Phi r K]
  simp only [red_Phi]
  rw [Finset.sum_eq_single q (fun q' _ hq' => by simp [hq']) (by simp)]
  simp only [if_true, ← Finset.sum_mul, hX]
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have hn := two_r_ne r
  unfold NN
  push_cast at hn ⊢
  field_simp

/-- `Q'_k = Q'_k(id)`: the mean over the block `B^k(y)`. -/
def Qpop (lam : Tor (NN r K) → ℂ) (y : Tor K) : ℂ :=
  (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * ∑ w ∈ box r, lam (emb r K y + castw r K w)

lemma Qpop_spec (lam : Tor (NN r K) → ℂ) (y : Tor K) :
    Qpop r K lam y = (((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, ch (red r K s) y * (Us r K s * hat lam s) := by
  have hl : ∀ z, lam z = (((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, ch s z * hat lam s := fun z => by
    conv_lhs => rw [← inv_hat lam]
    rfl
  unfold Qpop Us
  simp only [hl, ch_add_right, ch_emb, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => ?_
  ring

/-- **`eq:average-symbols` for `Q'_k`**: `(Q'_kλ)~(p') = Σ_lu_k(p' + l)λ̃(p' + l)`, `λ̃(p' + 2πm) = n⁻⁴λ̂(q̃ + Km)`. -/
lemma hat_Qpop (lam : Tor (NN r K) → ℂ) (q : Tor K) :
    hat (Qpop r K lam) q = ∑ m : box r, (uk (2 * r + 1) (shift (pk K q) m) : ℂ) *
      ((((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * hat lam (Phi r K q m)) := by
  set X : Tor (NN r K) → ℂ := fun s => Us r K s * hat lam s with hX
  have h1 : Qpop r K lam = fun y => (((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, ch (red r K s) y * X s :=
    funext (Qpop_spec r K lam)
  rw [h1]
  conv_lhs => unfold hat
  have h2 : ∀ y, ch (-q) y * ((((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, ch (red r K s) y * X s) =
      (((NN r K : ℕ) : ℂ) ^ 4)⁻¹ * ∑ s, X s * ch (red r K s - q) y := by
    intro y
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sub_eq_add_neg, ch_add_left]; ring
  simp only [h2]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, orth, sub_eq_zero, mul_ite, mul_zero]
  rw [sum_Phi r K]
  simp only [red_Phi]
  rw [Finset.sum_eq_single q (fun q' _ hq' => by simp [hq']) (by simp)]
  simp only [if_true, hX, Us_Phi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have hn := two_r_ne r
  unfold NN
  push_cast at hn ⊢
  field_simp

/-- **`eq:average-symbols`** (`prop:momentum-space`(i)) in the normalisation `f̃ = a₀⁴f̂` on `T^{(0)}`:
`(Q'_kλ)~(p') = Σ_lu_kλ̃(p' + l)` and `(Q_kA)~_μ(p') = Σ_lu_kv_μÃ_μ(p' + l)`. -/
theorem average_symbols (lam : Tor (NN r K) → ℂ) (A : Fin 4 → Tor (NN r K) → ℂ) (q : Tor K) (μ : Fin 4) :
    hat (Qpop r K lam) q = ∑ m : box r, (uk (2 * r + 1) (shift (pk K q) m) : ℂ) *
        ((((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * hat lam (Phi r K q m)) ∧
      hat (Qop r K A μ) q = ∑ m : box r, (uk (2 * r + 1) (shift (pk K q) m) : ℂ) *
        vs (2 * r + 1) (shift (pk K q) m μ) * ((((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * hat (A μ) (Phi r K q m)) := by
  refine ⟨hat_Qpop r K lam q, ?_⟩
  rw [hat_Qop, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Us_Phi, Vs_Phi]
  ring

/-- **`Q_k∂ = ∂¹Q'_k`** (`prop:momentum-space`(i)) on the tori: `u_kv_μ∂_μ = u_k∂¹_μ` on every fibre. -/
theorem Q_diff (lam : Tor (NN r K) → ℂ) (μ : Fin 4) :
    Qop r K (fun ν => d0 r K ν lam) μ = d1 K μ (Qpop r K lam) := by
  refine hat_injective (funext fun q => ?_)
  rw [(average_symbols r K lam (fun ν => d0 r K ν lam) q μ).2, hat_d1, hat_Qpop, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hat_d0]
  have hd : vs (2 * r + 1) (shift (pk K q) m μ) * dS r K (Phi r K q m) μ = d1sym (pk K q) μ := by
    unfold dS
    rw [dS_Phi]
    unfold dsym d1sym
    exact vs_mul_diff_shift (2 * r + 1) (by omega) (pk K q μ) ((m : Fin 4 → ℤ) μ)
  calc (uk (2 * r + 1) (shift (pk K q) m) : ℂ) * vs (2 * r + 1) (shift (pk K q) m μ) *
        ((((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * (dS r K (Phi r K q m) μ * hat lam (Phi r K q m)))
      = (uk (2 * r + 1) (shift (pk K q) m) : ℂ) *
          (vs (2 * r + 1) (shift (pk K q) m μ) * dS r K (Phi r K q m) μ) *
          ((((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * hat lam (Phi r K q m)) := by ring
    _ = _ := by rw [hd]; ring

/-! ### The energies -/

/-- `⟨∂A, ∂A⟩ = Σ_xa₀⁴Σ_{μ<ν}|(∂A)_{μν}(x)|²` on `T^{(0)}`. -/
def energy0 (A : Fin 4 → Tor (NN r K) → ℂ) : ℝ :=
  (((2 * r + 1 : ℕ) : ℝ) ^ 4)⁻¹ * ∑ z, 1 / 2 * ∑ μ, ∑ ν, ‖d0 r K μ (A ν) z - d0 r K ν (A μ) z‖ ^ 2

/-- `⟨∂¹B, ∂¹B⟩ = Σ_yΣ_{μ<ν}|(∂¹B)_{μν}(y)|²` on `T^{(k)}`. -/
def energy1 (B : Fin 4 → Tor K → ℂ) : ℝ := ∑ y, 1 / 2 * ∑ μ, ∑ ν, ‖d1 K μ (B ν) y - d1 K ν (B μ) y‖ ^ 2

/-- The right side of `eq:minimal-form`, `½Σ_{μ,ν}(2π)⁻⁴∫σ_{μν}|(∂¹B)~_{μν}|²dp'`, `∫dp' = (2π)⁴K⁻⁴Σ_{p'}`, without `p' = 0`. -/
def rhs (B : Fin 4 → Tor K → ℂ) : ℝ :=
  1 / 2 * ∑ μ, ∑ ν, ((K : ℝ) ^ 4)⁻¹ * ∑ q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0),
    sigma r μ ν (pk K q) * ‖hat (fun y => d1 K μ (B ν) y - d1 K ν (B μ) y) q‖ ^ 2

lemma swap3s {α : Type*} (S : Finset α) (f : Fin 4 → Fin 4 → α → ℝ) :
    ∑ z ∈ S, 1 / 2 * ∑ μ, ∑ ν, f μ ν z = 1 / 2 * ∑ μ, ∑ ν, ∑ z ∈ S, f μ ν z := by
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_comm

lemma swap3 {α : Type*} [Fintype α] (f : Fin 4 → Fin 4 → α → ℝ) :
    ∑ z, 1 / 2 * ∑ μ, ∑ ν, f μ ν z = 1 / 2 * ∑ μ, ∑ ν, ∑ z, f μ ν z := swap3s Finset.univ f

/-- The family of the transform on the fibre of `q`, `a_q(m) = Ã(p' + 2πm) = n⁻⁴Â(q̃ + Km)`. -/
def fam (A : Fin 4 → Tor (NN r K) → ℂ) (q : Tor K) (m : box r) (μ : Fin 4) : ℂ :=
  (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ * hat (A μ) (Phi r K q m)

/-- **The energy in momentum space**, fibre by fibre. -/
lemma energy0_fibre (A : Fin 4 → Tor (NN r K) → ℂ) :
    energy0 r K A = ((K : ℝ) ^ 4)⁻¹ * ∑ q : Tor K, 1 / 2 * ∑ l : box r, ∑ μ, ∑ ν,
      ‖dsym (2 * r + 1) (shift (pk K q) l) μ * fam r K A q l ν -
        dsym (2 * r + 1) (shift (pk K q) l) ν * fam r K A q l μ‖ ^ 2 := by
  have hn := two_r_ne r
  have hF : ∀ μ ν, ∑ z, ‖d0 r K μ (A ν) z - d0 r K ν (A μ) z‖ ^ 2 =
      (((NN r K : ℕ) : ℝ) ^ 4)⁻¹ * ∑ s, ‖dS r K s μ * hat (A ν) s - dS r K s ν * hat (A μ) s‖ ^ 2 := by
    intro μ ν
    rw [parseval (fun z => d0 r K μ (A ν) z - d0 r K ν (A μ) z), hat_sub]
    simp only [hat_d0]
  have hterm : ∀ (q : Tor K) (m : box r) (μ ν : Fin 4),
      ‖dS r K (Phi r K q m) μ * hat (A ν) (Phi r K q m) - dS r K (Phi r K q m) ν * hat (A μ) (Phi r K q m)‖ ^ 2 =
        (((2 * r + 1 : ℕ) : ℝ) ^ 4) ^ 2 * ‖dsym (2 * r + 1) (shift (pk K q) m) μ * fam r K A q m ν -
          dsym (2 * r + 1) (shift (pk K q) m) ν * fam r K A q m μ‖ ^ 2 := by
    intro q m μ ν
    have e : dS r K (Phi r K q m) μ * hat (A ν) (Phi r K q m) - dS r K (Phi r K q m) ν * hat (A μ) (Phi r K q m) =
        ((2 * r + 1 : ℕ) : ℂ) ^ 4 * (dsym (2 * r + 1) (shift (pk K q) m) μ * fam r K A q m ν -
          dsym (2 * r + 1) (shift (pk K q) m) ν * fam r K A q m μ) := by
      unfold dS fam
      rw [dS_Phi, dS_Phi]
      field_simp
    rw [e, norm_mul, mul_pow, norm_pow, Complex.norm_natCast]
  unfold energy0
  rw [swap3]
  simp only [hF]
  rw [show (1 / 2 * ∑ μ, ∑ ν, (((NN r K : ℕ) : ℝ) ^ 4)⁻¹ *
      ∑ s, ‖dS r K s μ * hat (A ν) s - dS r K s ν * hat (A μ) s‖ ^ 2) =
      (((NN r K : ℕ) : ℝ) ^ 4)⁻¹ * ∑ s, 1 / 2 * ∑ μ, ∑ ν,
        ‖dS r K s μ * hat (A ν) s - dS r K s ν * hat (A μ) s‖ ^ 2 by
    rw [swap3]; simp only [Finset.mul_sum]; ring_nf]
  rw [sum_Phi r K]
  simp only [hterm]
  have hq : ∀ q : Tor K, ∑ m : box r, 1 / 2 * ∑ μ, ∑ ν, (((2 * r + 1 : ℕ) : ℝ) ^ 4) ^ 2 *
      ‖dsym (2 * r + 1) (shift (pk K q) m) μ * fam r K A q m ν -
        dsym (2 * r + 1) (shift (pk K q) m) ν * fam r K A q m μ‖ ^ 2 =
      (((2 * r + 1 : ℕ) : ℝ) ^ 4) ^ 2 * (1 / 2 * ∑ m : box r, ∑ μ, ∑ ν,
        ‖dsym (2 * r + 1) (shift (pk K q) m) μ * fam r K A q m ν -
          dsym (2 * r + 1) (shift (pk K q) m) ν * fam r K A q m μ‖ ^ 2) := by
    intro q
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  simp only [hq]
  rw [← Finset.mul_sum, ← mul_assoc, ← mul_assoc]
  congr 1
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne K)
  have hn' : ((2 * r + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold NN
  push_cast at hn' ⊢
  field_simp

/-- **The constraint in momentum space**: `(Q_kA_μ)^(q) = Σ_mu_k v_μ a_q(m)_μ`. -/
lemma hat_Qop_fam (A : Fin 4 → Tor (NN r K) → ℂ) (μ : Fin 4) (q : Tor K) :
    hat (Qop r K A μ) q = ∑ m : box r, (uk (2 * r + 1) (shift (pk K q) m) : ℂ) *
      vs (2 * r + 1) (shift (pk K q) m μ) * fam r K A q m μ := by
  rw [hat_Qop, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Us_Phi, Vs_Phi]
  unfold fam
  ring

/-- `⟨∂¹B, ∂¹B⟩` in momentum space. -/
lemma energy1_spec (B : Fin 4 → Tor K → ℂ) :
    energy1 K B = ((K : ℝ) ^ 4)⁻¹ * ∑ q : Tor K, 1 / 2 * ∑ μ, ∑ ν,
      ‖d1sym (pk K q) μ * hat (B ν) q - d1sym (pk K q) ν * hat (B μ) q‖ ^ 2 := by
  unfold energy1
  have hF : ∀ μ ν, ∑ y, ‖d1 K μ (B ν) y - d1 K ν (B μ) y‖ ^ 2 = ((K : ℝ) ^ 4)⁻¹ * ∑ q,
      ‖d1sym (pk K q) μ * hat (B ν) q - d1sym (pk K q) ν * hat (B μ) q‖ ^ 2 := by
    intro μ ν
    rw [parseval (fun y => d1 K μ (B ν) y - d1 K ν (B μ) y), hat_sub]
    simp only [hat_d1]
  rw [swap3, swap3 (fun μ ν q => ‖d1sym (pk K q) μ * hat (B ν) q - d1sym (pk K q) ν * hat (B μ) q‖ ^ 2)]
  simp only [hF, ← Finset.mul_sum]
  ring

lemma rhs_spec (B : Fin 4 → Tor K → ℂ) :
    rhs r K B = ((K : ℝ) ^ 4)⁻¹ * ∑ q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0), 1 / 2 * ∑ μ, ∑ ν,
      sigma r μ ν (pk K q) * ‖d1sym (pk K q) μ * hat (B ν) q - d1sym (pk K q) ν * hat (B μ) q‖ ^ 2 := by
  unfold rhs
  have e : ∀ μ ν q, hat (fun y => d1 K μ (B ν) y - d1 K ν (B μ) y) q =
      d1sym (pk K q) μ * hat (B ν) q - d1sym (pk K q) ν * hat (B μ) q := by
    intro μ ν q; rw [hat_sub]; simp only [hat_d1]
  simp only [e]
  rw [swap3s]
  simp only [← Finset.mul_sum]
  ring

/-! ### The minimal form -/

lemma Qop_re (A : Fin 4 → Tor (NN r K) → ℂ) (μ : Fin 4) (y : Tor K) :
    Qop r K (fun μ z => ((A μ z).re : ℂ)) μ y = ((Qop r K A μ y).re : ℂ) := by
  unfold Qop
  have h1 : (((2 * r + 1 : ℕ) : ℂ) ^ 4)⁻¹ = (((((2 * r + 1 : ℕ) : ℝ) ^ 4)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have h2 : ((2 * r + 1 : ℕ) : ℂ)⁻¹ = (((((2 * r + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, h2]
  simp only [Complex.re_ofReal_mul, Complex.re_sum]
  push_cast
  rfl

lemma d0_re (f : Tor (NN r K) → ℂ) (μ : Fin 4) (z : Tor (NN r K)) :
    d0 r K μ (fun z => ((f z).re : ℂ)) z = ((d0 r K μ f z).re : ℂ) := by
  unfold d0
  rw [show ((2 * r + 1 : ℕ) : ℂ) = (((2 * r + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
    Complex.sub_re]
  push_cast
  rfl

/-- The real part does not increase `⟨∂A, ∂A⟩`. -/
lemma energy0_re_le (A : Fin 4 → Tor (NN r K) → ℂ) :
    energy0 r K (fun μ z => ((A μ z).re : ℂ)) ≤ energy0 r K A := by
  unfold energy0
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) (by positivity)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => ?_) (by norm_num)
  simp only [d0_re]
  rw [← Complex.ofReal_sub, ← Complex.sub_re, Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

lemma pk_zero : pk K (0 : Tor K) = 0 := (pk_eq_zero K 0).2 rfl

lemma dsym_zero (n : ℕ) (μ : Fin 4) : dsym n 0 μ = 0 := by simp [dsym]

lemma uk_zero (n : ℕ) : uk n 0 = 1 := by simp [uk, uf]

lemma vs_zero (n : ℕ) : vs n 0 = 1 := by simp [vs]

/-- **The lower bound of `eq:minimal-form`**: every (complex) `A` with `Q_kA = B` has `⟨∂A, ∂A⟩` at least the right side. -/
theorem minimal_lower (B : Fin 4 → Tor K → ℂ) (A : Fin 4 → Tor (NN r K) → ℂ) (hA : ∀ μ, Qop r K A μ = B μ) :
    rhs r K B ≤ energy0 r K A := by
  rw [rhs_spec, energy0_fibre]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun q : Tor K => q ≠ 0) Finset.univ)
    fun q _ _ => by positivity)
  refine Finset.sum_le_sum fun q hq => ?_
  have hq0 : q ≠ 0 := (Finset.mem_filter.1 hq).2
  have hp0 : pk K q ≠ 0 := fun h => hq0 ((pk_eq_zero K q).1 h)
  obtain ⟨hlow, -⟩ := fibre_minimum r (pk_le K q) hp0 (fun μ => hat (B μ) q)
  exact hlow (fam r K A q) fun μ => by rw [← hat_Qop_fam, hA μ]

/-- **`eq:minimal-form`** (`prop:momentum-space`(iv)): for a real `1`-form `B` on `T^{(k)}`, the minimum of `⟨∂A, ∂A⟩` over
the real `1`-forms `A` on `T^{(0)}` with `Q_kA = B` exists and is `½Σ_{μ,ν}(2π)⁻⁴∫σ_{μν}|(∂¹B)~_{μν}|²dp'`. -/
theorem minimal_form (B : Fin 4 → Tor K → ℝ) :
    (∀ A : Fin 4 → Tor (NN r K) → ℝ, (∀ μ y, Qop r K (fun μ z => (A μ z : ℂ)) μ y = B μ y) →
      rhs r K (fun μ y => (B μ y : ℂ)) ≤ energy0 r K (fun μ z => (A μ z : ℂ))) ∧
    ∃ A : Fin 4 → Tor (NN r K) → ℝ, (∀ μ y, Qop r K (fun μ z => (A μ z : ℂ)) μ y = B μ y) ∧
      energy0 r K (fun μ z => (A μ z : ℂ)) = rhs r K (fun μ y => (B μ y : ℂ)) := by
  classical
  set Bc : Fin 4 → Tor K → ℂ := fun μ y => (B μ y : ℂ) with hBc
  refine ⟨fun A hA => minimal_lower r K Bc _ fun μ => funext (hA μ), ?_⟩
  set b : Tor K → Fin 4 → ℂ := fun q μ => hat (Bc μ) q with hb
  -- the minimisers on the fibres
  have hfib : ∀ q : Tor K, ∃ a : box r → Fin 4 → ℂ,
      (∀ μ, ∑ l : box r, (uk (2 * r + 1) (shift (pk K q) l) : ℂ) * vs (2 * r + 1) (shift (pk K q) l μ) * a l μ =
        b q μ) ∧
      1 / 2 * ∑ l : box r, ∑ μ, ∑ ν, ‖dsym (2 * r + 1) (shift (pk K q) l) μ * a l ν -
          dsym (2 * r + 1) (shift (pk K q) l) ν * a l μ‖ ^ 2 =
        if q = 0 then 0 else 1 / 2 * ∑ μ, ∑ ν, sigma r μ ν (pk K q) *
          ‖d1sym (pk K q) μ * b q ν - d1sym (pk K q) ν * b q μ‖ ^ 2 := by
    intro q
    by_cases hq : q = 0
    · subst hq
      refine ⟨fun l μ => if (l : Fin 4 → ℤ) = 0 then b 0 μ else 0, fun μ => ?_, ?_⟩
      · rw [Finset.sum_eq_single ⟨0, zero_mem_box r⟩ (fun l _ hl => by
            have : (l : Fin 4 → ℤ) ≠ 0 := fun h => hl (Subtype.ext h)
            simp [this]) (by simp)]
        simp [pk_zero, shift_zero, uk_zero, vs_zero]
      · rw [if_pos rfl]
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun μ _ =>
          Finset.sum_eq_zero fun ν _ => ?_)
        by_cases hl : (l : Fin 4 → ℤ) = 0
        · simp [hl, pk_zero, shift_zero, dsym_zero]
        · simp [hl]
    · have hp0 : pk K q ≠ 0 := fun h => hq ((pk_eq_zero K q).1 h)
      obtain ⟨-, a, ha, hval⟩ := fibre_minimum r (pk_le K q) hp0 (b q)
      exact ⟨a, ha, by rw [if_neg hq]; exact hval.trans rfl⟩
  choose a ha hval using hfib
  -- the field with these transforms
  set E := Equiv.ofBijective _ (Phi_bij r K) with hE
  set Ahat : Fin 4 → Tor (NN r K) → ℂ := fun μ s => ((2 * r + 1 : ℕ) : ℂ) ^ 4 * a (E.symm s).1 (E.symm s).2 μ
    with hAhat
  set Ac : Fin 4 → Tor (NN r K) → ℂ := fun μ => inv (Ahat μ) with hAc
  have hfam : ∀ q m μ, fam r K Ac q m μ = a q m μ := by
    intro q m μ
    unfold fam
    rw [hAc, hat_inv, hAhat]
    have : E.symm (Phi r K q m) = (q, m) := E.symm_apply_apply (q, m)
    simp only [this]
    have hn := two_r_ne r
    field_simp
  have hQ : ∀ μ, Qop r K Ac μ = Bc μ := fun μ =>
    hat_injective (funext fun q => by rw [hat_Qop_fam]; simp only [hfam]; exact ha q μ)
  have hEn : energy0 r K Ac = rhs r K Bc := by
    rw [energy0_fibre, rhs_spec]
    refine congrArg (fun t => ((K : ℝ) ^ 4)⁻¹ * t) ?_
    simp only [hfam, hval]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q = 0
    · simp [hq]
    · simp [hq, hb]
  -- the real part
  have hQre : ∀ μ y, Qop r K (fun μ z => (((Ac μ z).re : ℝ) : ℂ)) μ y = B μ y := by
    intro μ y
    rw [Qop_re, hQ]
    simp [hBc]
  refine ⟨fun μ z => (Ac μ z).re, hQre, le_antisymm ?_ ?_⟩
  · rw [← hEn]; exact energy0_re_le r K Ac
  · exact minimal_lower r K Bc _ fun μ => funext (hQre μ)

/-- **The comparison with `⟨∂¹B, ∂¹B⟩`** (`prop:momentum-space`(iv)): `γ'₀⟨∂¹B, ∂¹B⟩ ≤ ⟨B, Δ_kB⟩ ≤ γ'₁⟨∂¹B, ∂¹B⟩` with
`γ'₀ = γ₀γ₁⁻²`, `γ'₁ = γ₁γ₀⁻²`, `⟨B, Δ_kB⟩` the right side of `eq:minimal-form`. -/
theorem minimal_comparison (B : Fin 4 → Tor K → ℂ) :
    (2 / π) ^ 12 / (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) ^ 2 * energy1 K B ≤ rhs r K B ∧
      rhs r K B ≤ (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) / ((2 / π) ^ 12) ^ 2 * energy1 K B := by
  classical
  rw [energy1_spec, rhs_spec]
  set T : Tor K → ℝ := fun q => 1 / 2 * ∑ μ, ∑ ν,
    ‖d1sym (pk K q) μ * hat (B ν) q - d1sym (pk K q) ν * hat (B μ) q‖ ^ 2 with hT
  have hT0 : ∑ q, T q = ∑ q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0), T q := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q = 0
    · subst hq; simp [hT, pk_zero, d1sym]
    · simp [hq]
  rw [hT0]
  have hp0 : ∀ q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0), pk K q ≠ 0 :=
    fun q hq h => (Finset.mem_filter.1 hq).2 ((pk_eq_zero K q).1 h)
  have hK : 0 ≤ ((K : ℝ) ^ 4)⁻¹ := by positivity
  constructor
  · have h := Finset.sum_le_sum fun q (hq : q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0)) =>
      (fibre_comparison r (pk_le K q) (hp0 q hq) (fun μ => hat (B μ) q)).1
    calc _ = ((K : ℝ) ^ 4)⁻¹ * ((2 / π) ^ 12 / (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) ^ 2 *
          ∑ q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0), T q) := mul_left_comm _ _ _
      _ = ((K : ℝ) ^ 4)⁻¹ * ∑ q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0),
          (2 / π) ^ 12 / (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) ^ 2 * T q := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h hK
  · have h := Finset.sum_le_sum fun q (hq : q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0)) =>
      (fibre_comparison r (pk_le K q) (hp0 q hq) (fun μ => hat (B μ) q)).2
    calc _ ≤ ((K : ℝ) ^ 4)⁻¹ * ∑ q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0),
          (π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) / ((2 / π) ^ 12) ^ 2 * T q :=
            mul_le_mul_of_nonneg_left h hK
      _ = ((K : ℝ) ^ 4)⁻¹ * ((π ^ 2 / 4 + π ^ 2 * (4 * (π ^ 2 / 3 - 1)) ^ 4) / ((2 / π) ^ 12) ^ 2 *
          ∑ q ∈ Finset.univ.filter (fun q : Tor K => q ≠ 0), T q) := by rw [← Finset.mul_sum]
      _ = _ := mul_left_comm _ _ _

end MomentumTorus
end CoreLean

end
