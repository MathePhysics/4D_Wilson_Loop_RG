import Mathlib
import GaussianBlockSpin.TaylorCoefficients

/-! **Vanishing to a given order at `0`** for smooth functions of one real variable (`VanishesTo m f`: the
derivatives of order `< m` at `0` vanish), and for smooth families of linear maps between finite-dimensional spaces
(`OpVanishesTo m O`, read through the continuous linear maps). Closure under sums, continuous linear and bilinear maps
and inner products (the orders add), products in a normed algebra (the orders add), composition, adjoints, traces,
evaluation and inverses of invertible families; the remainder of the exponential `t ↦ e^{tQ} - Σ_{m ≤ n} (tQ)^m / m!`
vanishes to order `n + 1` and the polynomial part `Σ_{1 ≤ m ≤ n} (tQ)^m / m!` to order `1`. Used to show that a term
with a factor `R_{n̄+1}` has no part of order `≤ n̄` in the field. -/

namespace GaussianBlockSpin

open scoped ContDiff Nat RealInnerProductSpace

section Vanishing

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **`f` vanishes to order `m` at `0`**: its derivatives of order `< m` at `0` vanish. -/
def VanishesTo (m : ℕ) (f : ℝ → F) : Prop := ∀ i < m, iteratedDeriv i f 0 = 0

lemma vanishesTo_iff {m : ℕ} {f : ℝ → F} : VanishesTo m f ↔ ∀ i < m, iteratedFDeriv ℝ i f 0 = 0 := by
  refine forall₂_congr fun i _ => ?_
  rw [← norm_eq_zero (a := iteratedFDeriv ℝ i f 0), norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_eq_zero]

lemma VanishesTo.mono {m m' : ℕ} {f : ℝ → F} (h : VanishesTo m f) (hm : m' ≤ m) : VanishesTo m' f :=
  fun i hi => h i (lt_of_lt_of_le hi hm)

lemma vanishesTo_zero (f : ℝ → F) : VanishesTo 0 f := fun i hi => absurd hi (Nat.not_lt_zero i)

lemma vanishesTo_const_zero (m : ℕ) : VanishesTo m (fun _ : ℝ => (0 : F)) := fun i _ => by
  simp

lemma contDiffAt_of_contDiff {f : ℝ → F} (hf : ContDiff ℝ ∞ f) (i : ℕ) (x : ℝ) : ContDiffAt ℝ i f x :=
  hf.contDiffAt.of_le (by exact_mod_cast le_top)

/-- **Leibniz for a bounded bilinear map**: the orders add. -/
theorem VanishesTo.bilinear (B : E →L[ℝ] F →L[ℝ] G) {f : ℝ → E} {g : ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {m₁ m₂ : ℕ} (h₁ : VanishesTo m₁ f) (h₂ : VanishesTo m₂ g) :
    VanishesTo (m₁ + m₂) (fun t => B (f t) (g t)) := by
  rw [vanishesTo_iff] at h₁ h₂ ⊢
  intro n hn
  rw [← norm_le_zero_iff]
  refine (B.norm_iteratedFDeriv_le_of_bilinear hf hg 0 (n := n) (by exact_mod_cast le_top)).trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero, mul_zero]
  intro i hi
  by_cases h : i < m₁
  · rw [h₁ i h, norm_zero]
    ring
  · have : n - i < m₂ := by
      have := Finset.mem_range.mp hi
      omega
    rw [h₂ (n - i) this, norm_zero]
    ring

/-- A continuous linear map preserves the order of vanishing. -/
theorem VanishesTo.clm (L : F →L[ℝ] G) {f : ℝ → F} (hf : ContDiff ℝ ∞ f) {m : ℕ} (h : VanishesTo m f) :
    VanishesTo m (fun t => L (f t)) := by
  have := VanishesTo.bilinear (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) contDiff_const hf
    (vanishesTo_zero (fun _ : ℝ => L)) h
  simpa using this

/-- The inner product of two smooth vector-valued functions: the orders add. -/
theorem VanishesTo.inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {f g : ℝ → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {m₁ m₂ : ℕ} (h₁ : VanishesTo m₁ f) (h₂ : VanishesTo m₂ g) :
    VanishesTo (m₁ + m₂) (fun t => ⟪f t, g t⟫) := by
  exact VanishesTo.bilinear (innerSL ℝ (E := V)) hf hg h₁ h₂

theorem VanishesTo.add {f g : ℝ → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {m : ℕ}
    (h₁ : VanishesTo m f) (h₂ : VanishesTo m g) : VanishesTo m (fun t => f t + g t) := fun i hi => by
  rw [iteratedDeriv_fun_add (contDiffAt_of_contDiff hf i 0) (contDiffAt_of_contDiff hg i 0), h₁ i hi, h₂ i hi,
    add_zero]

theorem VanishesTo.sub {f g : ℝ → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {m : ℕ}
    (h₁ : VanishesTo m f) (h₂ : VanishesTo m g) : VanishesTo m (fun t => f t - g t) := fun i hi => by
  rw [iteratedDeriv_fun_sub (contDiffAt_of_contDiff hf i 0) (contDiffAt_of_contDiff hg i 0), h₁ i hi, h₂ i hi,
    sub_zero]

/-- Two smooth functions with the same derivatives of order `< m` at `0` differ by a function vanishing to order
`m`. -/
theorem vanishesTo_sub_of_eq {f g : ℝ → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {m : ℕ}
    (h : ∀ i < m, iteratedDeriv i f 0 = iteratedDeriv i g 0) : VanishesTo m (fun t => f t - g t) := fun i hi => by
  rw [iteratedDeriv_fun_sub (contDiffAt_of_contDiff hf i 0) (contDiffAt_of_contDiff hg i 0), h i hi, sub_self]

theorem VanishesTo.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → F} (hf : ∀ j ∈ s, ContDiff ℝ ∞ (f j)) {m : ℕ}
    (h : ∀ j ∈ s, VanishesTo m (f j)) : VanishesTo m (fun t => ∑ j ∈ s, f j t) := fun i hi => by
  rw [iteratedDeriv_fun_sum (fun j hj => contDiffAt_of_contDiff (hf j hj) i 0)]
  exact Finset.sum_eq_zero fun j hj => h j hj i hi

theorem VanishesTo.neg {f : ℝ → F} {m : ℕ} (h : VanishesTo m f) : VanishesTo m (fun t => -f t) := fun i hi => by
  rw [iteratedDeriv_fun_neg, h i hi, neg_zero]

/-- Smooth and vanishing to order `m`: closed under negation. -/
lemma contDiff_vanishesTo_neg {f : ℝ → F} {m : ℕ} (h : ContDiff ℝ ∞ f ∧ VanishesTo m f) :
    ContDiff ℝ ∞ (fun t => -f t) ∧ VanishesTo m (fun t => -f t) :=
  ⟨h.1.neg, h.2.neg⟩

/-- Smooth and vanishing to order `m`: closed under addition. -/
lemma contDiff_vanishesTo_add {f g : ℝ → F} {m : ℕ} (hf : ContDiff ℝ ∞ f ∧ VanishesTo m f)
    (hg : ContDiff ℝ ∞ g ∧ VanishesTo m g) :
    ContDiff ℝ ∞ (fun t => f t + g t) ∧ VanishesTo m (fun t => f t + g t) :=
  ⟨hf.1.add hg.1, hf.2.add hf.1 hg.1 hg.2⟩

/-- Smooth and vanishing to order `m`: closed under finite sums. -/
lemma contDiff_vanishesTo_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → F} {m : ℕ}
    (h : ∀ i ∈ s, ContDiff ℝ ∞ (f i) ∧ VanishesTo m (f i)) :
    ContDiff ℝ ∞ (fun t => ∑ i ∈ s, f i t) ∧ VanishesTo m (fun t => ∑ i ∈ s, f i t) :=
  ⟨ContDiff.sum fun i hi => (h i hi).1, VanishesTo.sum s (fun i hi => (h i hi).1) fun i hi => (h i hi).2⟩

theorem VanishesTo.const_smul (c : ℝ) {f : ℝ → F} (hf : ContDiff ℝ ∞ f) {m : ℕ} (h : VanishesTo m f) :
    VanishesTo m (fun t => c • f t) := fun i hi => by
  rw [iteratedDeriv_fun_const_smul (contDiffAt_of_contDiff hf i 0) c, h i hi, smul_zero]

/-- **Products in a normed algebra**: the orders add. -/
theorem VanishesTo.mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : ℝ → A} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {m₁ m₂ : ℕ} (h₁ : VanishesTo m₁ f) (h₂ : VanishesTo m₂ g) :
    VanishesTo (m₁ + m₂) (fun t => f t * g t) := fun n hn => by
  rw [iteratedDeriv_fun_mul (contDiffAt_of_contDiff hf n 0) (contDiffAt_of_contDiff hg n 0)]
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases h : i < m₁
  · rw [h₁ i h, mul_zero, zero_mul]
  · have : n - i < m₂ := by
      have := Finset.mem_range.mp hi
      omega
    rw [h₂ (n - i) this, mul_zero]

/-- A finite product of smooth real functions with one factor vanishing to order `m` vanishes to order `m`. -/
theorem VanishesTo.prod_of_mem {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ j ∈ s, ContDiff ℝ ∞ (f j)) {j₀ : ι} (hj₀ : j₀ ∈ s) {m : ℕ} (h : VanishesTo m (f j₀)) :
    VanishesTo m (fun t => ∏ j ∈ s, f j t) := by
  have hrest : ContDiff ℝ ∞ (fun t => ∏ j ∈ s.erase j₀, f j t) :=
    contDiff_prod fun j hj => hf j (Finset.mem_of_mem_erase hj)
  have heq : (fun t => ∏ j ∈ s, f j t) = fun t => f j₀ t * ∏ j ∈ s.erase j₀, f j t := by
    funext t
    exact (Finset.mul_prod_erase s (fun j => f j t) hj₀).symm
  rw [heq]
  simpa using VanishesTo.mul (hf j₀ hj₀) hrest h (vanishesTo_zero _)

end Vanishing

section ExpTaylor

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
lemma contDiff_smul_pow (Q : V →L[ℝ] V) (m : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ => ((m ! : ℝ)⁻¹) • (t • Q) ^ m) := by
  fun_prop

/-- **The remainder of the exponential**: `t ↦ e^{tQ} - Σ_{m ≤ n} (tQ)^m / m!` vanishes to order `n + 1`. -/
theorem vanishesTo_exp_sub_taylor (Q : V →L[ℝ] V) (n : ℕ) :
    VanishesTo (n + 1) (fun t : ℝ => NormedSpace.exp (t • Q) -
      ∑ m ∈ Finset.range (n + 1), ((m ! : ℝ)⁻¹) • (t • Q) ^ m) := by
  refine vanishesTo_sub_of_eq (contDiff_exp_smul Q) (ContDiff.sum fun m _ => contDiff_smul_pow Q m) fun i hi => ?_
  have hfun : (fun t : ℝ => ∑ m ∈ Finset.range (n + 1), ((m ! : ℝ)⁻¹) • (t • Q) ^ m) =
      fun t => ∑ m ∈ Finset.range (n + 1), ((m ! : ℝ)⁻¹ * t ^ m) • Q ^ m := by
    funext t
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_pow, smul_smul]
  have hterm : ∀ m, iteratedDeriv i (fun t : ℝ => ((m ! : ℝ)⁻¹ * t ^ m) • Q ^ m) 0 =
      if i = m then Q ^ m else 0 := by
    intro m
    rw [iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
    split_ifs with h
    · rw [inv_mul_cancel₀ (by positivity), one_smul]
    · simp
  rw [hfun, iteratedDeriv_fun_sum (fun m _ => by fun_prop), iteratedDeriv_exp_smul]
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_range, hi, ↓reduceIte, zero_smul, NormedSpace.exp_zero, one_mul]

end ExpTaylor

section Components

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `t ↦ t^m v` vanishes to order `m`. -/
lemma vanishesTo_pow_smul (m : ℕ) (v : F) : VanishesTo m (fun t : ℝ => t ^ m • v) := fun i hi => by
  rw [iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_fun_pow_zero]
  simp [Nat.ne_of_lt hi]

/-- A smooth family of continuous linear maps vanishes to order `m` iff it does at every vector. -/
lemma vanishesTo_clm_iff {f : ℝ → (E →L[ℝ] F)} (hf : ContDiff ℝ ∞ f) {m : ℕ} :
    VanishesTo m f ↔ ∀ v, VanishesTo m (fun t => f t v) := by
  have key : ∀ v i, iteratedDeriv i (fun t => f t v) 0 = iteratedDeriv i f 0 v := fun v i =>
    iteratedDeriv_clm_apply (ContinuousLinearMap.apply ℝ F v) hf i 0
  refine ⟨fun h v i hi => by simp [key, h i hi], fun h i hi => ?_⟩
  ext v
  simp [← key, h v i hi]

/-- A smooth function into `PiLp 2 β` vanishes to order `m` iff each component does. -/
lemma vanishesTo_piLp_iff {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
    [∀ i, NormedSpace ℝ (β i)] {f : ℝ → PiLp 2 β} (hf : ContDiff ℝ ∞ f) {m : ℕ} :
    VanishesTo m f ↔ ∀ i, VanishesTo m (fun t => f t i) := by
  have key : ∀ i n, iteratedDeriv n (fun t => f t i) 0 = iteratedDeriv n f 0 i := fun i n =>
    iteratedDeriv_clm_apply (PiLp.proj (𝕜 := ℝ) 2 β i) hf n 0
  refine ⟨fun h i n hn => by rw [key, h n hn]; rfl, fun h n hn => ?_⟩
  ext i
  rw [← key, h i n hn]
  rfl

end Components

section TaylorPos

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Taylor polynomial of `e^{sQ}` applied to a vector. -/
lemma taylor_sum_apply (Q : V →L[ℝ] V) (n : ℕ) (s : ℝ) (v : V) :
    (∑ m ∈ Finset.range (n + 1), ((m ! : ℝ)⁻¹) • (s • Q) ^ m) v =
      ∑ m ∈ Finset.range (n + 1), ((m ! : ℝ)⁻¹ * s ^ m) • (Q ^ m) v := by
  have h : ∀ m : ℕ, (((m ! : ℝ)⁻¹) • (s • Q) ^ m) v = ((m ! : ℝ)⁻¹ * s ^ m) • (Q ^ m) v := fun m => by
    rw [smul_pow, smul_smul]
    rfl
  simp only [FunLike.coe_sum, Finset.sum_apply, h]

/-- **The polynomial part** `t ↦ Σ_{1 ≤ m ≤ n} (tQ)^m / m!` vanishes to order `1`. -/
theorem vanishesTo_taylor_pos (Q : V →L[ℝ] V) (n : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ => ∑ m ∈ Finset.Ico 1 (n + 1), ((m ! : ℝ)⁻¹) • (t • Q) ^ m) ∧
      VanishesTo 1 (fun t : ℝ => ∑ m ∈ Finset.Ico 1 (n + 1), ((m ! : ℝ)⁻¹) • (t • Q) ^ m) := by
  have hfun : (fun t : ℝ => ∑ m ∈ Finset.Ico 1 (n + 1), ((m ! : ℝ)⁻¹) • (t • Q) ^ m) =
      fun t => ∑ m ∈ Finset.Ico 1 (n + 1), t ^ m • (((m ! : ℝ)⁻¹) • Q ^ m) := by
    funext t
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_pow, smul_comm]
  rw [hfun]
  exact ⟨ContDiff.sum fun m _ => by fun_prop,
    VanishesTo.sum _ (fun m _ => by fun_prop) fun m hm => (vanishesTo_pow_smul m _).mono (Finset.mem_Ico.mp hm).1⟩

end TaylorPos

section Operators

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A family of linear maps between finite-dimensional spaces that is smooth and vanishes to order `m` at `0`**,
read through the continuous linear maps. -/
structure OpVanishesTo (m : ℕ) (O : ℝ → (E →ₗ[ℝ] F)) : Prop where
  smooth : ContDiff ℝ ∞ (fun t => LinearMap.toContinuousLinearMap (O t))
  vanishes : VanishesTo m (fun t => LinearMap.toContinuousLinearMap (O t))

namespace OpVanishesTo

lemma const (O : E →ₗ[ℝ] F) : OpVanishesTo 0 (fun _ : ℝ => O) := ⟨contDiff_const, vanishesTo_zero _⟩

lemma mono {m m' : ℕ} {O : ℝ → (E →ₗ[ℝ] F)} (h : OpVanishesTo m O) (hm : m' ≤ m) : OpVanishesTo m' O :=
  ⟨h.smooth, h.vanishes.mono hm⟩

lemma add {m : ℕ} {O O' : ℝ → (E →ₗ[ℝ] F)} (h : OpVanishesTo m O) (h' : OpVanishesTo m O') :
    OpVanishesTo m (fun t => O t + O' t) :=
  ⟨by simpa only [map_add] using h.smooth.add h'.smooth,
    by simpa only [map_add] using h.vanishes.add h.smooth h'.smooth h'.vanishes⟩

lemma sub {m : ℕ} {O O' : ℝ → (E →ₗ[ℝ] F)} (h : OpVanishesTo m O) (h' : OpVanishesTo m O') :
    OpVanishesTo m (fun t => O t - O' t) :=
  ⟨by simpa only [map_sub] using h.smooth.sub h'.smooth,
    by simpa only [map_sub] using h.vanishes.sub h.smooth h'.smooth h'.vanishes⟩

lemma neg {m : ℕ} {O : ℝ → (E →ₗ[ℝ] F)} (h : OpVanishesTo m O) : OpVanishesTo m (fun t => -O t) :=
  ⟨by simpa only [map_neg] using h.smooth.neg, by simpa only [map_neg] using h.vanishes.neg⟩

lemma const_smul (c : ℝ) {m : ℕ} {O : ℝ → (E →ₗ[ℝ] F)} (h : OpVanishesTo m O) :
    OpVanishesTo m (fun t => c • O t) :=
  ⟨by simpa only [map_smul] using h.smooth.const_smul c,
    by simpa only [map_smul] using h.vanishes.const_smul c h.smooth⟩

lemma sum {ι : Type*} (s : Finset ι) {m : ℕ} {O : ι → ℝ → (E →ₗ[ℝ] F)} (h : ∀ i ∈ s, OpVanishesTo m (O i)) :
    OpVanishesTo m (fun t => ∑ i ∈ s, O i t) :=
  ⟨by simpa only [map_sum] using ContDiff.sum fun i hi => (h i hi).smooth,
    by simpa only [map_sum] using VanishesTo.sum s (fun i hi => (h i hi).smooth) fun i hi => (h i hi).vanishes⟩

lemma toCLM_comp [FiniteDimensional ℝ F] (O₁ : F →ₗ[ℝ] H) (O₂ : E →ₗ[ℝ] F) :
    LinearMap.toContinuousLinearMap (O₁ ∘ₗ O₂) =
      (LinearMap.toContinuousLinearMap O₁).comp (LinearMap.toContinuousLinearMap O₂) :=
  ContinuousLinearMap.ext fun _ => rfl

/-- **Composition**: the orders add. -/
lemma comp [FiniteDimensional ℝ F] {m₁ m₂ : ℕ} {O₁ : ℝ → (F →ₗ[ℝ] H)} {O₂ : ℝ → (E →ₗ[ℝ] F)} (h₁ : OpVanishesTo m₁ O₁)
    (h₂ : OpVanishesTo m₂ O₂) : OpVanishesTo (m₁ + m₂) (fun t => O₁ t ∘ₗ O₂ t) := by
  refine ⟨?_, ?_⟩
  · simp only [toCLM_comp]
    exact h₁.smooth.clm_comp h₂.smooth
  · simp only [toCLM_comp]
    exact VanishesTo.bilinear (ContinuousLinearMap.compL ℝ E F H) h₁.smooth h₂.smooth h₁.vanishes h₂.vanishes

lemma mul {m₁ m₂ : ℕ} {O₁ O₂ : ℝ → (E →ₗ[ℝ] E)} (h₁ : OpVanishesTo m₁ O₁) (h₂ : OpVanishesTo m₂ O₂) :
    OpVanishesTo (m₁ + m₂) (fun t => O₁ t * O₂ t) :=
  h₁.comp h₂

/-- **An ordered product of `n` endomorphism families**: the orders add. -/
lemma prod_ofFn {n : ℕ} {O : Fin n → ℝ → (E →ₗ[ℝ] E)} {m : Fin n → ℕ} (h : ∀ i, OpVanishesTo (m i) (O i)) :
    OpVanishesTo (∑ i, m i) (fun t => (List.ofFn fun i => O i t).prod) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact const 1
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact (h 0).mul (ih (O := fun i => O i.succ) (m := fun i => m i.succ) fun i => h i.succ)

/-- Evaluation at a fixed vector. -/
lemma apply {m : ℕ} {O : ℝ → (E →ₗ[ℝ] F)} (h : OpVanishesTo m O) (v : E) :
    ContDiff ℝ ∞ (fun t => O t v) ∧ VanishesTo m (fun t => O t v) := by
  have hv : (fun t => O t v) = fun t => ContinuousLinearMap.apply ℝ F v (LinearMap.toContinuousLinearMap (O t)) :=
    rfl
  rw [hv]
  exact ⟨(ContinuousLinearMap.apply ℝ F v).contDiff.comp h.smooth, h.vanishes.clm _ h.smooth⟩

/-- A family is smooth and vanishes to order `m` if it does at every vector. -/
lemma of_apply {m : ℕ} {O : ℝ → (E →ₗ[ℝ] F)}
    (h : ∀ v, ContDiff ℝ ∞ (fun t => O t v) ∧ VanishesTo m (fun t => O t v)) : OpVanishesTo m O := by
  have hs : ContDiff ℝ ∞ (fun t => LinearMap.toContinuousLinearMap (O t)) :=
    contDiff_clm_apply_iff.mpr fun v => (h v).1
  exact ⟨hs, (vanishesTo_clm_iff hs).mpr fun v => (h v).2⟩

/-- The trace. -/
lemma trace {m : ℕ} {O : ℝ → (E →ₗ[ℝ] E)} (h : OpVanishesTo m O) :
    ContDiff ℝ ∞ (fun t => LinearMap.trace ℝ E (O t)) ∧ VanishesTo m (fun t => LinearMap.trace ℝ E (O t)) := by
  let T : (E →L[ℝ] E) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.trace ℝ E ∘ₗ (LinearMap.toContinuousLinearMap.symm : (E →L[ℝ] E) ≃ₗ[ℝ] (E →ₗ[ℝ] E)).toLinearMap)
  have hT : (fun t => LinearMap.trace ℝ E (O t)) = fun t => T (LinearMap.toContinuousLinearMap (O t)) := by
    funext t
    simp [T]
  rw [hT]
  exact ⟨T.contDiff.comp h.smooth, h.vanishes.clm T h.smooth⟩

/-- **The inverse of a smooth family of invertible endomorphisms is smooth.** -/
lemma inverse {O P : ℝ → (E →ₗ[ℝ] E)} (hO : OpVanishesTo 0 O) (h₁ : ∀ t, O t ∘ₗ P t = LinearMap.id)
    (h₂ : ∀ t, P t ∘ₗ O t = LinearMap.id) : OpVanishesTo 0 P := by
  have := FiniteDimensional.complete ℝ E
  let u : ℝ → (E →L[ℝ] E)ˣ := fun t =>
    ⟨LinearMap.toContinuousLinearMap (O t), LinearMap.toContinuousLinearMap (P t),
      by rw [ContinuousLinearMap.mul_def, ← toCLM_comp, h₁ t]; rfl,
      by rw [ContinuousLinearMap.mul_def, ← toCLM_comp, h₂ t]; rfl⟩
  have hP : (fun t => LinearMap.toContinuousLinearMap (P t)) =
      fun t => Ring.inverse (LinearMap.toContinuousLinearMap (O t)) := by
    funext t
    exact (Ring.inverse_unit (u t)).symm
  refine ⟨?_, vanishesTo_zero _⟩
  rw [hP, contDiff_iff_contDiffAt]
  exact fun t => ContDiffAt.comp (g := Ring.inverse) t (contDiffAt_ringInverse ℝ (u t)) hO.smooth.contDiffAt

end OpVanishesTo

end Operators

section InnerOperators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

namespace OpVanishesTo

/-- The adjoint. -/
lemma adjoint {m : ℕ} {O : ℝ → (E →ₗ[ℝ] F)} (h : OpVanishesTo m O) :
    OpVanishesTo m (fun t => LinearMap.adjoint (O t)) := by
  have := FiniteDimensional.complete ℝ E
  have := FiniteDimensional.complete ℝ F
  let adjLin : (E →L[ℝ] F) →ₗ[ℝ] (F →L[ℝ] E) :=
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => map_add _ A B
      map_smul' := fun c A => by simp }
  let adjL : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) := LinearMap.toContinuousLinearMap adjLin
  have hA : (fun t => LinearMap.toContinuousLinearMap (LinearMap.adjoint (O t))) =
      fun t => adjL (LinearMap.toContinuousLinearMap (O t)) := by
    funext t
    exact LinearMap.adjoint_toContinuousLinearMap (O t)
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact adjL.contDiff.comp h.smooth
  · rw [hA]
    exact h.vanishes.clm adjL h.smooth

omit [FiniteDimensional ℝ F] in
/-- The matrix element `⟪u, O(t) v⟫`. -/
lemma inner {m : ℕ} {O : ℝ → (E →ₗ[ℝ] F)} (h : OpVanishesTo m O) (u : F) (v : E) :
    ContDiff ℝ ∞ (fun t => ⟪u, O t v⟫) ∧ VanishesTo m (fun t => ⟪u, O t v⟫) := by
  obtain ⟨hs, hv⟩ := h.apply v
  exact ⟨contDiff_const.inner ℝ hs, by simpa using VanishesTo.inner contDiff_const hs (vanishesTo_zero _) hv⟩

end OpVanishesTo

end InnerOperators

end GaussianBlockSpin
