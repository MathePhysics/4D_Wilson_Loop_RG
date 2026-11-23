/-
`lem:ward` of BALABAN_CORE.tex: the Ward identities (i), (ii), (iii).

The data (`WardData`): configurations on the bonds `Bd` with values in `𝔸` (`M_N(ℂ)` in the core), the
ends `b₋ = mn b`, `b₊ = pl b`, a complex subspace `𝔤^c ⊂ 𝔸` closed under commutators, and a function `E`
analytic on a ball about the trivial configuration and invariant under the complex gauge transformations
`e^{iλ}` near `id` with `λ` in `𝔤^c` (derived from the real invariance in `WardComplex.lean`).
`E^{(n)} = D^nF(0)` for `F(B) = E(e^{iB})`, a symmetric `n`-linear form (`ContDiffAt.iteratedFDeriv_comp_perm`);
the identities are proved for all fields with values in `𝔸` where the core has unit fields, and the
statements which use the triviality of the centre are proved for fields with values in `𝔤^c`. The
triviality of the centre enters as `𝔤^c = [𝔤^c, 𝔤^c]` (`Perfect`), which is what the core's proof of (ii)
uses: a linear form on `𝔤^c` which vanishes on the commutators `[λ, B]` vanishes.
-/
import CoreLean.WardTaylor
import CoreLean.WardPolar

open NormedSpace BakerCampbellHausdorff Filter Asymptotics
open scoped Topology

noncomputable section

namespace CoreLean

namespace Ward

/-! ### Multilinear maps on `![…]` -/

section Multilinear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma ml2_add0 (M : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => V) ℂ) (a a' b : V) :
    M ![a + a', b] = M ![a, b] + M ![a', b] := by
  have h := M.map_update_add ![a, b] 0 a a'
  have e : ∀ x, Function.update ![a, b] 0 x = ![x, b] := fun x => by
    funext j; fin_cases j <;> rfl
  rwa [e, e, e] at h

lemma ml2_add1 (M : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => V) ℂ) (a b b' : V) :
    M ![a, b + b'] = M ![a, b] + M ![a, b'] := by
  have h := M.map_update_add ![a, b] 1 b b'
  have e : ∀ x, Function.update ![a, b] 1 x = ![a, x] := fun x => by
    funext j; fin_cases j <;> rfl
  rwa [e, e, e] at h

lemma ml2_smul1 (M : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => V) ℂ) (a b : V) (c : ℂ) :
    M ![a, c • b] = c * M ![a, b] := by
  have h := M.map_update_smul ![a, b] 1 c b
  have e : ∀ x, Function.update ![a, b] 1 x = ![a, x] := fun x => by
    funext j; fin_cases j <;> rfl
  rwa [e, e, smul_eq_mul] at h

lemma ml3_add (M : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => V) ℂ) (i : Fin 3) (m : Fin 3 → V)
    (x y : V) : M (Function.update m i (x + y)) = M (Function.update m i x) + M (Function.update m i y) :=
  M.map_update_add m i x y

lemma ml3_smul2 (M : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => V) ℂ) (a b c : V) (t : ℂ) :
    M ![a, b, t • c] = t * M ![a, b, c] := by
  have h := M.map_update_smul ![a, b, c] 2 t c
  have e : ∀ x, Function.update ![a, b, c] 2 x = ![a, b, x] := fun x => by
    funext j; fin_cases j <;> rfl
  rwa [e, e, smul_eq_mul] at h

lemma ml4_smul3 (M : ContinuousMultilinearMap ℂ (fun _ : Fin 4 => V) ℂ) (a b c d : V) (t : ℂ) :
    M ![a, b, c, t • d] = t * M ![a, b, c, d] := by
  have h := M.map_update_smul ![a, b, c, d] 3 t d
  have e : ∀ x, Function.update ![a, b, c, d] 3 x = ![a, b, c, x] := fun x => by
    funext j; fin_cases j <;> rfl
  rwa [e, e, smul_eq_mul] at h

lemma ml3_add0 (M : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => V) ℂ) (a a' b c : V) :
    M ![a + a', b, c] = M ![a, b, c] + M ![a', b, c] := by
  have h := M.map_update_add ![a, b, c] 0 a a'
  have e : ∀ x, Function.update ![a, b, c] 0 x = ![x, b, c] := fun x => by
    funext j; fin_cases j <;> rfl
  rwa [e, e, e] at h

lemma ml3_add2 (M : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => V) ℂ) (a b c c' : V) :
    M ![a, b, c + c'] = M ![a, b, c] + M ![a, b, c'] := by
  have h := M.map_update_add ![a, b, c] 2 c c'
  have e : ∀ x, Function.update ![a, b, c] 2 x = ![a, b, x] := fun x => by
    funext j; fin_cases j <;> rfl
  rwa [e, e, e] at h

lemma ml4_add0 (M : ContinuousMultilinearMap ℂ (fun _ : Fin 4 => V) ℂ) (a a' b c d : V) :
    M ![a + a', b, c, d] = M ![a, b, c, d] + M ![a', b, c, d] := by
  have h := M.map_update_add ![a, b, c, d] 0 a a'
  have e : ∀ x, Function.update ![a, b, c, d] 0 x = ![x, b, c, d] := fun x => by
    funext j; fin_cases j <;> rfl
  rwa [e, e, e] at h

end Multilinear

/-! ### The data -/

/-- The data of `lem:ward`. -/
structure WardData (𝔸 Bd St : Type*) [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [Fintype Bd] [Fintype St] where
  mn : Bd → St
  pl : Bd → St
  gc : Submodule ℂ 𝔸
  gc_lie : ∀ a ∈ gc, ∀ c ∈ gc, a * c - c * a ∈ gc
  E : (Bd → 𝔸) → ℂ
  ρ : ℝ
  ε : ℝ
  ρ_pos : 0 < ρ
  ε_pos : 0 < ε
  analytic : AnalyticOnNhd ℂ E (Metric.ball 1 ρ)
  inv : ∀ (B : Bd → 𝔸) (l : St → 𝔸), (∀ x, l x ∈ gc) → ‖B‖ < ε → ‖l‖ < ε →
    E (gauge mn pl l (expI B)) = E (expI B)

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
variable {Bd St : Type*} [Fintype Bd] [Fintype St] (W : WardData 𝔸 Bd St)

namespace WardData

/-- `E^{(n)} = D^nF(0)`, `F(B) = E(e^{iB})`. -/
def D (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => Bd → 𝔸) ℂ :=
  iteratedFDeriv ℂ n (W.E ∘ expI) 0

/-- The commutator `[a, c] = ac - ca`. -/
def com (a c : 𝔸) : 𝔸 := a * c - c * a

/-- `(dλ)(b) = λ(b₊) - λ(b₋)`. -/
def dl (l : St → 𝔸) : Bd → 𝔸 := fun b => l (W.pl b) - l (W.mn b)

/-- `δ_λB(b) = i[λ(b₋), B(b)] - ½i[B(b), (dλ)(b)]`. -/
def δ (l : St → 𝔸) (B : Bd → 𝔸) : Bd → 𝔸 :=
  fun b => Complex.I • com (l (W.mn b)) (B b) - (2 : ℂ)⁻¹ • Complex.I • com (B b) (W.dl l b)

lemma analyticOnNhd_F : ∃ r > 0, AnalyticOnNhd ℂ (W.E ∘ expI) (Metric.ball (0 : Bd → 𝔸) r) := by
  obtain ⟨r, hr, hrρ⟩ := Metric.continuousAt_iff.mp
    (continuous_expI (Bd := Bd) (𝔸 := 𝔸)).continuousAt W.ρ W.ρ_pos
  refine ⟨r, hr, fun B hB => ?_⟩
  have hB' : expI B ∈ Metric.ball (1 : Bd → 𝔸) W.ρ := by
    have := hrρ (Metric.mem_ball.mp hB)
    rwa [expI_zero] at this
  have hexp : AnalyticAt ℂ (expI (Bd := Bd) (𝔸 := 𝔸)) B := by
    refine analyticAt_pi_iff.mpr fun b => ?_
    have hlin : AnalyticAt ℂ (fun B : Bd → 𝔸 => Complex.I • B b) B :=
      ((Complex.I • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Bd => 𝔸) b).analyticAt B)
    exact (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp hlin
  exact (W.analytic _ hB').comp hexp

/-- The forms `E^{(n)}` are symmetric. -/
lemma D_perm (n : ℕ) (v : Fin n → Bd → 𝔸) (σ : Equiv.Perm (Fin n)) : W.D n (v ∘ σ) = W.D n v := by
  obtain ⟨r, hr, hF⟩ := W.analyticOnNhd_F
  exact (hF 0 (Metric.mem_ball_self hr)).contDiffAt.iteratedFDeriv_comp_perm v σ

lemma D2_swap (a b : Bd → 𝔸) : W.D 2 ![a, b] = W.D 2 ![b, a] := by
  have h := W.D_perm 2 ![b, a] (Equiv.swap 0 1)
  have e : (![b, a] ∘ Equiv.swap (0 : Fin 2) 1) = ![a, b] := by
    funext j; fin_cases j <;> rfl
  rw [e] at h; exact h

lemma D1_eq (V : Bd → 𝔸) : W.D 1 (fun _ => V) = fderiv ℂ (W.E ∘ expI) 0 V := by
  simp [D, iteratedFDeriv_one_apply]

lemma wh0_eq (l : St → 𝔸) : wh0 W.mn W.pl l = -W.dl l := by
  funext b; simp [wh0, dl]

lemma wh1_eq (l : St → 𝔸) (B : Bd → 𝔸) : wh1 W.mn W.pl l B = W.δ l B := by
  funext b
  simp only [wh1, δ, com, dl, adX, ContinuousLinearMap.neg_apply, ad_apply, map_add]
  simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul, smul_sub, smul_add,
    smul_neg]
  module

lemma wh2_eq (l : St → 𝔸) (B : Bd → 𝔸) :
    wh2 W.mn W.pl l B = fun b => (12 : ℂ)⁻¹ • com (B b) (com (B b) (W.dl l b)) := by
  funext b
  have hII : ∀ x : 𝔸, Complex.I • Complex.I • x = -x := fun x => by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [wh2, com, dl, adX, sq, ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
    ad_apply, map_sub, map_neg]
  simp only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, smul_sub, neg_sub, hII, mul_neg,
    neg_mul, smul_neg, mul_assoc]
  module

/-- `lem:ward`(i): `⟨E^{(1)}, i[λ(b₋), B₁(b)]⟩ = ⟨E^{(2)}, dλ, B₁⟩ + ½⟨E^{(1)}, i[B₁, dλ]⟩`. -/
theorem ward_i (l : St → 𝔸) (hl : ∀ x, l x ∈ W.gc) (B₁ : Bd → 𝔸) :
    W.D 1 (fun _ b => Complex.I • com (l (W.mn b)) (B₁ b)) =
      W.D 2 ![W.dl l, B₁] + 1 / 2 * W.D 1 (fun _ b => Complex.I • com (B₁ b) (W.dl l b)) := by
  obtain ⟨-, h1, -, -⟩ :=
    ward_diagonal W.mn W.pl W.gc W.E W.ρ_pos W.ε_pos W.analytic W.inv l hl B₁
  have e1 : rayVec B₁ (wh0 W.mn W.pl l) 1 = ![B₁, -W.dl l] := by
    rw [wh0_eq]; funext j; fin_cases j <;> rfl
  have e2 : rayVec B₁ (wh1 W.mn W.pl l B₁) 0 = fun _ => W.δ l B₁ := by
    rw [wh1_eq]; rfl
  rw [e1, e2] at h1
  change W.D 2 ![B₁, -W.dl l] + W.D 1 (fun _ => W.δ l B₁) = 0 at h1
  have hneg : W.D 2 ![B₁, -W.dl l] = -W.D 2 ![B₁, W.dl l] := by
    rw [show -W.dl l = (-1 : ℂ) • W.dl l by rw [neg_one_smul], ml2_smul1]; ring
  rw [hneg, D2_swap] at h1
  have hδ : W.δ l B₁ = (fun b => Complex.I • com (l (W.mn b)) (B₁ b)) -
      (2 : ℂ)⁻¹ • fun b => Complex.I • com (B₁ b) (W.dl l b) := by
    funext b; simp [δ]
  simp only [D1_eq] at h1 ⊢
  rw [hδ, map_sub, map_smul, smul_eq_mul] at h1
  linear_combination h1

/-- The triviality of the centre in the form `𝔤^c = [𝔤^c, 𝔤^c]`. -/
def Perfect : Prop :=
  ∀ v ∈ W.gc, v ∈ Submodule.span ℂ {w | ∃ a ∈ W.gc, ∃ c ∈ W.gc, w = com a c}

/-- `lem:ward`(ii), first statement: if the centre is trivial, `E^{(1)}` vanishes on the fields with values
in `𝔤^c`. -/
theorem D1_eq_zero (hperf : W.Perfect) (B : Bd → 𝔸) (hB : ∀ b, B b ∈ W.gc) :
    W.D 1 (fun _ => B) = 0 := by
  classical
  -- `(i)` with a constant `λ ≡ a`: `E^{(1)}[i[a, B₁]] = 0`
  have hconst : ∀ a ∈ W.gc, ∀ B₁ : Bd → 𝔸,
      fderiv ℂ (W.E ∘ expI) 0 (fun b => Complex.I • com a (B₁ b)) = 0 := by
    intro a ha B₁
    have h := W.ward_i (fun _ => a) (fun _ => ha) B₁
    have hdl : W.dl (fun _ => a) = 0 := by funext b; simp [dl]
    rw [hdl] at h
    have h0 : W.D 2 ![(0 : Bd → 𝔸), B₁] = 0 := by
      have := ml2_add0 (W.D 2) 0 0 B₁
      simp only [add_zero] at this
      linear_combination -this
    have hz : (fun b => Complex.I • com (B₁ b) ((0 : Bd → 𝔸) b)) = (0 : Bd → 𝔸) := by
      funext b; simp [com]
    rw [h0] at h
    simp only [D1_eq, hz, map_zero] at h
    simpa using h
  -- every value is a sum of commutators
  have hII : ∀ x : 𝔸, Complex.I • Complex.I • x = -x := fun x => by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hspan : ∀ b, ∀ v ∈ Submodule.span ℂ {w | ∃ a ∈ W.gc, ∃ c ∈ W.gc, w = com a c},
      fderiv ℂ (W.E ∘ expI) 0 (Pi.single b v) = 0 := by
    intro b v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, c, hc, rfl⟩ := hw
      have h := hconst a ha (Pi.single b (-(Complex.I • c)) : Bd → 𝔸)
      have e : (fun b' => Complex.I • com a ((Pi.single b (-(Complex.I • c)) : Bd → 𝔸) b')) =
          Pi.single b (com a c) := by
        funext b'
        by_cases hb : b' = b
        · subst hb
          simp only [Pi.single_eq_same, com, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc,
            sub_neg_eq_add]
          simp only [smul_add, smul_sub, smul_neg, hII, neg_neg, sub_eq_add_neg]
          try abel
        · simp [Pi.single_eq_of_ne hb, com]
      rwa [e] at h
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.single_add, map_add, hx, hy, add_zero]
    | smul t x _ hx => rw [Pi.single_smul, map_smul, hx, smul_zero]
  have hsingle : ∀ b, ∀ v ∈ W.gc, fderiv ℂ (W.E ∘ expI) 0 (Pi.single b v) = 0 :=
    fun b v hv => hspan b v (hperf v hv)
  rw [D1_eq, ← Finset.univ_sum_single B, map_sum]
  exact Finset.sum_eq_zero fun b _ => hsingle b (B b) (hB b)

lemma com_mem {a c : 𝔸} (ha : a ∈ W.gc) (hc : c ∈ W.gc) : com a c ∈ W.gc := W.gc_lie a ha c hc

lemma dl_mem (l : St → 𝔸) (hl : ∀ x, l x ∈ W.gc) (b : Bd) : W.dl l b ∈ W.gc :=
  W.gc.sub_mem (hl _) (hl _)

lemma δ_mem (l : St → 𝔸) (hl : ∀ x, l x ∈ W.gc) (B : Bd → 𝔸) (hB : ∀ b, B b ∈ W.gc) (b : Bd) :
    W.δ l B b ∈ W.gc :=
  W.gc.sub_mem (W.gc.smul_mem _ (W.com_mem (hl _) (hB b)))
    (W.gc.smul_mem _ (W.gc.smul_mem _ (W.com_mem (hB b) (W.dl_mem l hl b))))

/-- `lem:ward`(ii), second statement: `⟨E^{(2)}, dλ, B₁⟩ = 0` for `B₁` with values in `𝔤^c`. -/
theorem ward_ii (hperf : W.Perfect) (l : St → 𝔸) (hl : ∀ x, l x ∈ W.gc) (B₁ : Bd → 𝔸)
    (hB₁ : ∀ b, B₁ b ∈ W.gc) : W.D 2 ![W.dl l, B₁] = 0 := by
  have h := W.ward_i l hl B₁
  rw [W.D1_eq_zero hperf _ (fun b => W.gc.smul_mem _ (W.com_mem (hl _) (hB₁ b))),
    W.D1_eq_zero hperf _ (fun b => W.gc.smul_mem _ (W.com_mem (hB₁ b) (W.dl_mem l hl b)))] at h
  linear_combination -h

/-! ### (iii) -/

lemma D3_swap (a b c : Bd → 𝔸) : W.D 3 ![a, b, c] = W.D 3 ![b, a, c] := by
  have h := W.D_perm 3 ![b, a, c] (Equiv.swap 0 1)
  have e : (![b, a, c] ∘ Equiv.swap (0 : Fin 3) 1) = ![a, b, c] := by
    funext j; fin_cases j <;> rfl
  rw [e] at h; exact h

lemma D4_swap01 (a b c d : Bd → 𝔸) : W.D 4 ![a, b, c, d] = W.D 4 ![b, a, c, d] := by
  have h := W.D_perm 4 ![b, a, c, d] (Equiv.swap 0 1)
  have e : (![b, a, c, d] ∘ Equiv.swap (0 : Fin 4) 1) = ![a, b, c, d] := by
    funext j; fin_cases j <;> rfl
  rw [e] at h; exact h

lemma D4_swap12 (a b c d : Bd → 𝔸) : W.D 4 ![a, b, c, d] = W.D 4 ![a, c, b, d] := by
  have h := W.D_perm 4 ![a, c, b, d] (Equiv.swap 1 2)
  have e : (![a, c, b, d] ∘ Equiv.swap (1 : Fin 4) 2) = ![a, b, c, d] := by
    funext j; fin_cases j <;> rfl
  rw [e] at h; exact h

lemma δ_add (l : St → 𝔸) (x x' : Bd → 𝔸) : W.δ l (x + x') = W.δ l x + W.δ l x' := by
  funext b
  simp only [δ, com, Pi.add_apply, mul_add, add_mul, smul_add, smul_sub]
  abel

/-- `[u, [v, dλ]]`, bond by bond. -/
def cc (l : St → 𝔸) (u v : Bd → 𝔸) : Bd → 𝔸 := fun b => com (u b) (com (v b) (W.dl l b))

lemma cc_sym_add (l : St → 𝔸) (x x' z : Bd → 𝔸) :
    W.cc l (x + x') z + W.cc l z (x + x') =
      (W.cc l x z + W.cc l z x) + (W.cc l x' z + W.cc l z x') := by
  funext b
  simp only [cc, com, Pi.add_apply, mul_add, add_mul, mul_sub, sub_mul]
  abel

/-- The right side of `eq:ward-four`. -/
def T4 (l : St → 𝔸) (x y z : Bd → 𝔸) : ℂ :=
  W.D 3 ![x, y, W.δ l z] + W.D 3 ![x, z, W.δ l y] + W.D 3 ![y, z, W.δ l x] +
    1 / 12 * (W.D 2 ![x, W.cc l y z + W.cc l z y] + W.D 2 ![y, W.cc l x z + W.cc l z x] +
      W.D 2 ![z, W.cc l x y + W.cc l y x])

/-- `lem:ward`(iii), `eq:ward-three`: for `B₁, B₂, λ` with values in `𝔤^c` and a trivial centre,
`⟨E^{(3)}, B₁, B₂, dλ⟩ = ⟨E^{(2)}, B₁, δ_λB₂⟩ + ⟨E^{(2)}, B₂, δ_λB₁⟩`. -/
theorem ward_three (hperf : W.Perfect) (l : St → 𝔸) (hl : ∀ x, l x ∈ W.gc) (B₁ B₂ : Bd → 𝔸)
    (hB₁ : ∀ b, B₁ b ∈ W.gc) (hB₂ : ∀ b, B₂ b ∈ W.gc) :
    W.D 3 ![B₁, B₂, W.dl l] = W.D 2 ![B₁, W.δ l B₂] + W.D 2 ![B₂, W.δ l B₁] := by
  have key := polar2 (fun B : Bd → 𝔸 => ∀ b, B b ∈ W.gc)
    (fun x y => W.D 3 ![x, y, W.dl l] - (W.D 2 ![x, W.δ l y] + W.D 2 ![y, W.δ l x]))
    (fun x x' y => by
      rw [ml3_add0, ml2_add0, W.δ_add, ml2_add1]
      ring)
    (fun x y => by
      rw [W.D3_swap]
      ring)
    (fun x y hx hy b => W.gc.add_mem (hx b) (hy b))
    (fun B hB => by
      obtain ⟨-, -, h2, -⟩ :=
        ward_diagonal W.mn W.pl W.gc W.E W.ρ_pos W.ε_pos W.analytic W.inv l hl B
      have e0 : rayVec B (wh0 W.mn W.pl l) 2 = ![B, B, -W.dl l] := by
        rw [wh0_eq]; funext j; fin_cases j <;> rfl
      have e1 : rayVec B (wh1 W.mn W.pl l B) 1 = ![B, W.δ l B] := by
        rw [wh1_eq]; funext j; fin_cases j <;> rfl
      have e2 : rayVec B (wh2 W.mn W.pl l B) 0 =
          fun _ => fun b => (12 : ℂ)⁻¹ • com (B b) (com (B b) (W.dl l b)) := by
        rw [wh2_eq]; rfl
      rw [e0, e1, e2] at h2
      change 1 / 2 * W.D 3 ![B, B, -W.dl l] + W.D 2 ![B, W.δ l B] +
        W.D 1 (fun _ => fun b => (12 : ℂ)⁻¹ • com (B b) (com (B b) (W.dl l b))) = 0 at h2
      rw [W.D1_eq_zero hperf _ (fun b => W.gc.smul_mem _
        (W.com_mem (hB b) (W.com_mem (hB b) (W.dl_mem l hl b))))] at h2
      rw [show -W.dl l = (-1 : ℂ) • W.dl l by rw [neg_one_smul], ml3_smul2] at h2
      try simp only
      linear_combination (-2 : ℂ) * h2)
    hB₁ hB₂
  try simp only at key
  linear_combination key

/-- `lem:ward`(iii), `eq:ward-four`: for all `B₁, B₂, B₃`,
`⟨E^{(4)}, B₁, B₂, B₃, dλ⟩ = Σ_{(i,j,l), i<j}⟨E^{(3)}, B_i, B_j, δ_λB_l⟩
+ (1/12)Σ_{(i,j,l), j<l}⟨E^{(2)}, B_i, [B_j, [B_l, dλ]] + [B_l, [B_j, dλ]]⟩` (`T4`). -/
theorem ward_four (l : St → 𝔸) (hl : ∀ x, l x ∈ W.gc) (B₁ B₂ B₃ : Bd → 𝔸) :
    W.D 4 ![B₁, B₂, B₃, W.dl l] = W.T4 l B₁ B₂ B₃ := by
  have key := polar3 (x := B₁) (y := B₂) (z := B₃) (fun _ : Bd → 𝔸 => True)
    (fun x y z => W.D 4 ![x, y, z, W.dl l] - W.T4 l x y z)
    (fun x x' y z => by
      simp only [T4]
      rw [ml4_add0, ml3_add0, ml3_add0, W.δ_add, ml3_add2, ml2_add0, W.cc_sym_add l x x' z,
        ml2_add1 (W.D 2) y (W.cc l x z + W.cc l z x) (W.cc l x' z + W.cc l z x'), W.cc_sym_add l x x' y,
        ml2_add1 (W.D 2) z (W.cc l x y + W.cc l y x) (W.cc l x' y + W.cc l y x')]
      ring)
    (fun x y z => by
      simp only [T4]
      rw [W.D4_swap01, W.D3_swap x y, add_comm (W.cc l x y) (W.cc l y x)]
      ring)
    (fun x y z => by
      simp only [T4]
      rw [W.D4_swap12, W.D3_swap y z, add_comm (W.cc l y z) (W.cc l z y)]
      ring)
    (fun _ _ _ _ => trivial)
    (fun B _ => by
      obtain ⟨-, -, -, h3⟩ :=
        ward_diagonal W.mn W.pl W.gc W.E W.ρ_pos W.ε_pos W.analytic W.inv l hl B
      have e0 : rayVec B (wh0 W.mn W.pl l) 3 = ![B, B, B, -W.dl l] := by
        rw [wh0_eq]; funext j; fin_cases j <;> rfl
      have e1 : rayVec B (wh1 W.mn W.pl l B) 2 = ![B, B, W.δ l B] := by
        rw [wh1_eq]; funext j; fin_cases j <;> rfl
      have e2 : rayVec B (wh2 W.mn W.pl l B) 1 = ![B, (12 : ℂ)⁻¹ • W.cc l B B] := by
        rw [wh2_eq]; funext j; fin_cases j <;> rfl
      rw [e0, e1, e2] at h3
      change 1 / 6 * W.D 4 ![B, B, B, -W.dl l] + 1 / 2 * W.D 3 ![B, B, W.δ l B] +
        W.D 2 ![B, (12 : ℂ)⁻¹ • W.cc l B B] = 0 at h3
      rw [show -W.dl l = (-1 : ℂ) • W.dl l by rw [neg_one_smul], ml4_smul3, ml2_smul1] at h3
      simp only [T4]
      rw [ml2_add1]
      linear_combination (-6 : ℂ) * h3)
    trivial trivial trivial
  try simp only at key
  linear_combination key

end WardData

end Ward

end CoreLean
