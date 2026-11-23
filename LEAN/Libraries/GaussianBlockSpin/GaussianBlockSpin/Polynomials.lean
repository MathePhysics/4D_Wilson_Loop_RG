import GaussianBlockSpin.GaussianGraphs
import GaussianBlockSpin.ExpDomination

/-! **Polynomial block derivatives.** IsPoly g: `g` is a finite sum of monomials `c ∏_i ⟪u_i, x⟫` (the form
GaussianGraphs and mixedCoeff_log_gaussIntegral_eq_connected use), with any finite index type; closed under sums,
products, powers, translations `y ↦ g(x₀ + y)`, and containing constants and linear functionals (finite dimension).
PolyFam g: a one-parameter family `g(y, e)`, `C^∞` in `e`, whose `e`-derivatives at `0` are polynomials in `y`; closed
under sums and products (Leibniz), containing the families constant in `e`, the transport coordinates
`⟪w, e^{(t + e s(y)) Q} v(y)⟫` (`∂_e^n` at `0` is `s(y)^n ⟪w, e^{tQ} Q^n v(y)⟫`, polyFam_inner_exp) and the squared
norms of vector families with polynomial-family coordinates. Mixed Taylor coefficients of jointly smooth functions
are linear, and those of functions of `e` alone are `[j = 0] ∂_e^i`; hence isPoly_mixedCoeff_of_decomp: if
`F(y, e, l) = H(y, e) - l P₄(y) - ½ g(e, l) P₂(y)` with `H` a polynomial family, `P₄`, `P₂` polynomials and `g`
smooth, every mixed coefficient of `F(y, ·, ·)` at `(0, 0)` is a polynomial in `y` (the exponent of the bracket of
I.(3.35)). Also: mixed coefficients of positive order do not see additive constants (mixedCoeff_const_sub), and
finitely many polynomials have representations over one finite index type (exists_common_monomials). -/

open scoped RealInnerProductSpace ContDiff
open Set

namespace GaussianBlockSpin

section IsPoly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `g` is a **polynomial** on `E`: a finite sum of monomials `c_a ∏_{i < k_a} ⟪U_{a,i}, x⟫` (legs indexed by `ℕ`). -/
def IsPoly (g : E → ℝ) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (c : A → ℝ) (k : A → ℕ) (U : A → ℕ → E),
    ∀ x, g x = ∑ a, monomial c k (fun a i => U a i) a x

lemma IsPoly.congr {f g : E → ℝ} (hf : IsPoly f) (h : ∀ x, f x = g x) : IsPoly g := by
  obtain ⟨A, _, c, k, U, hf⟩ := hf
  exact ⟨A, inferInstance, c, k, U, fun x => (h x).symm.trans (hf x)⟩

lemma isPoly_const (r : ℝ) : IsPoly (fun _ : E => r) :=
  ⟨Unit, inferInstance, fun _ => r, fun _ => 0, fun _ _ => 0, fun x => by simp [monomial]⟩

lemma isPoly_inner (w : E) : IsPoly (fun x : E => ⟪w, x⟫) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => 1, fun _ _ => w, fun x => by simp [monomial]⟩

lemma IsPoly.add {f g : E → ℝ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x + g x) := by
  obtain ⟨A, _, c, k, U, hf⟩ := hf
  obtain ⟨B, _, c', k', U', hg⟩ := hg
  refine ⟨A ⊕ B, inferInstance, Sum.elim c c', Sum.elim k k', Sum.elim U U', fun x => ?_⟩
  show f x + g x = _
  rw [hf, hg, Fintype.sum_sum_type]
  rfl

lemma IsPoly.mul {f g : E → ℝ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x * g x) := by
  obtain ⟨A, _, c, k, U, hf⟩ := hf
  obtain ⟨B, _, c', k', U', hg⟩ := hg
  refine ⟨A × B, inferInstance, fun p => c p.1 * c' p.2, fun p => k p.1 + k' p.2,
    fun p i => if i < k p.1 then U p.1 i else U' p.2 (i - k p.1), fun x => ?_⟩
  show f x * g x = _
  rw [hf, hg, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [monomial, Fin.prod_univ_add, Fin.val_castAdd, Fin.val_natAdd, Fin.is_lt, ite_true,
    show ∀ j : Fin (k' b), ¬ (k a + (j : ℕ) < k a) from fun j => by omega, ite_false, Nat.add_sub_cancel_left]
  ring

lemma IsPoly.const_mul {f : E → ℝ} (hf : IsPoly f) (r : ℝ) : IsPoly (fun x => r * f x) :=
  (isPoly_const r).mul hf

lemma IsPoly.neg {f : E → ℝ} (hf : IsPoly f) : IsPoly (fun x => -f x) :=
  (hf.const_mul (-1)).congr fun x => by ring

lemma IsPoly.sub {f g : E → ℝ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x - g x) :=
  (hf.add hg.neg).congr fun x => by ring

lemma IsPoly.sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, IsPoly (f i)) :
    IsPoly (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isPoly_const 0).congr fun x => by simp
  | insert a s ha ih =>
    exact ((hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr
      fun x => by rw [Finset.sum_insert ha]

lemma IsPoly.prod {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, IsPoly (f i)) :
    IsPoly (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isPoly_const 1).congr fun x => by simp
  | insert a s ha ih =>
    exact ((hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr
      fun x => by rw [Finset.prod_insert ha]

lemma IsPoly.pow {f : E → ℝ} (hf : IsPoly f) (n : ℕ) : IsPoly (fun x => f x ^ n) :=
  (IsPoly.prod (Finset.range n) fun _ _ => hf).congr fun x => by simp

lemma isPoly_monomial {A : Type*} (c : A → ℝ) (k : A → ℕ) (u : ∀ a, Fin (k a) → E) (a : A) :
    IsPoly (monomial c k u a) :=
  ((IsPoly.prod Finset.univ fun i _ => isPoly_inner (u a i)).const_mul (c a)).congr fun _ => rfl

/-- Translations of polynomials are polynomials. -/
lemma IsPoly.comp_add {f : E → ℝ} (hf : IsPoly f) (x₀ : E) : IsPoly (fun y => f (x₀ + y)) := by
  obtain ⟨A, _, c, k, U, hf⟩ := hf
  refine (IsPoly.sum Finset.univ fun a _ => ((IsPoly.prod (Finset.univ : Finset (Fin (k a))) fun i _ =>
    (isPoly_const ⟪U a i, x₀⟫).add (isPoly_inner (U a i))).const_mul (c a))).congr fun y => ?_
  rw [hf]
  simp only [monomial, inner_add_right]

/-- Linear functionals on a finite-dimensional space are polynomials. -/
lemma isPoly_linear [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ) : IsPoly (fun x => f x) :=
  (isPoly_inner ((InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap f))).congr fun x => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl

lemma isPoly_inner_linear_add [FiniteDimensional ℝ E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : E →ₗ[ℝ] V) (x₀ : E) (w : V) : IsPoly (fun y => ⟪w, L (x₀ + y)⟫) :=
  ((isPoly_linear ((innerSL ℝ w).toLinearMap.comp L)).comp_add x₀).congr fun _ => rfl

lemma isPoly_linear_add [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] ℝ) (x₀ : E) : IsPoly (fun y => σ (x₀ + y)) :=
  (isPoly_linear σ).comp_add x₀

lemma isPoly_norm_sq_linear_add [FiniteDimensional ℝ E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (L : E →ₗ[ℝ] V) (x₀ : E) : IsPoly (fun y => ‖L (x₀ + y)‖ ^ 2) := by
  set b := stdOrthonormalBasis ℝ V
  refine (IsPoly.sum Finset.univ fun i _ =>
    (isPoly_inner_linear_add L x₀ (b i)).mul (isPoly_inner_linear_add L x₀ (b i))).congr fun y => ?_
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner (L (x₀ + y)) (L (x₀ + y))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (L (x₀ + y)) (b i)]

end IsPoly

section PolyFam

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A one-parameter family `g(y, e)`, `C^∞` in `e`, whose `e`-derivatives at `0` are polynomials in `y`. -/
def PolyFam (g : E → ℝ → ℝ) : Prop :=
  (∀ y, ContDiff ℝ ∞ (g y)) ∧ ∀ n, IsPoly (fun y => iteratedDeriv n (g y) 0)

lemma PolyFam.congr {f g : E → ℝ → ℝ} (hf : PolyFam f) (h : ∀ y e, f y e = g y e) : PolyFam g := by
  have : f = g := funext fun y => funext fun e => h y e
  rwa [← this]

lemma PolyFam.add {f g : E → ℝ → ℝ} (hf : PolyFam f) (hg : PolyFam g) : PolyFam (fun y e => f y e + g y e) := by
  refine ⟨fun y => (hf.1 y).add (hg.1 y), fun n => ((hf.2 n).add (hg.2 n)).congr fun y => ?_⟩
  exact (iteratedDeriv_add (contDiff_of_infty (hf.1 y) n).contDiffAt (contDiff_of_infty (hg.1 y) n).contDiffAt).symm

lemma PolyFam.mul {f g : E → ℝ → ℝ} (hf : PolyFam f) (hg : PolyFam g) : PolyFam (fun y e => f y e * g y e) := by
  refine ⟨fun y => (hf.1 y).mul (hg.1 y), fun n => ?_⟩
  refine (IsPoly.sum (Finset.range (n + 1)) fun i _ => ((hf.2 i).mul (hg.2 (n - i))).const_mul (n.choose i)).congr
    fun y => ?_
  have h := iteratedDeriv_mul (x := (0 : ℝ)) (contDiff_of_infty (hf.1 y) n).contDiffAt
    (contDiff_of_infty (hg.1 y) n).contDiffAt
  show _ = iteratedDeriv n (f y * g y) 0
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma PolyFam.const_mul {f : E → ℝ → ℝ} (hf : PolyFam f) (r : ℝ) : PolyFam (fun y e => r * f y e) := by
  refine ⟨fun y => contDiff_const.mul (hf.1 y), fun n => ((hf.2 n).const_mul r).congr fun y => ?_⟩
  exact (iteratedDeriv_const_mul r (contDiff_of_infty (hf.1 y) n).contDiffAt).symm

lemma PolyFam.neg {f : E → ℝ → ℝ} (hf : PolyFam f) : PolyFam (fun y e => -f y e) := by
  have := hf.const_mul (-1)
  simpa using this

lemma PolyFam.sub {f g : E → ℝ → ℝ} (hf : PolyFam f) (hg : PolyFam g) : PolyFam (fun y e => f y e - g y e) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

lemma PolyFam.sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ → ℝ} (hf : ∀ i ∈ s, PolyFam (f i)) :
    PolyFam (fun y e => ∑ i ∈ s, f i y e) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun y => by simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))), fun n => ?_⟩
    exact (isPoly_const 0).congr fun y => by simp
  | insert a s ha ih =>
    have h := (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h

/-- Families constant in `e` with polynomial values. -/
lemma polyFam_of_isPoly {h : E → ℝ} (hh : IsPoly h) : PolyFam (fun y (_ : ℝ) => h y) := by
  refine ⟨fun y => contDiff_const, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hh.congr fun y => by simp
  · exact (isPoly_const 0).congr fun y => by simp [iteratedDeriv_const, hn.ne']

/-- Iterated derivatives commute with continuous linear maps. -/
lemma iteratedDeriv_clm_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : ℝ → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun e => L (f e)) x = L (iteratedDeriv n f x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have := L.iteratedFDeriv_comp_left (f := f) (x := x) (contDiff_of_infty hf n).contDiffAt (i := n) le_rfl
  rw [show (fun e => L (f e)) = L ∘ f from rfl, this]
  rfl

/-- Squared norms of vector families with polynomial-family coordinates. -/
lemma polyFam_norm_sq [FiniteDimensional ℝ V] {F : E → ℝ → V} (hF : ∀ w, PolyFam (fun y e => ⟪w, F y e⟫)) :
    PolyFam (fun y e => ‖F y e‖ ^ 2) := by
  set b := stdOrthonormalBasis ℝ V
  refine (PolyFam.sum Finset.univ fun i _ => (hF (b i)).mul (hF (b i))).congr fun y e => ?_
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner (F y e) (F y e)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (F y e) (b i)]

variable [CompleteSpace V]

/-- `∂_e^n ⟪w, e^{(t + e σ) Q} v⟫ = σ^n ⟪w, e^{t Q} Q^n v⟫` at `e = 0`. -/
lemma iteratedDeriv_inner_exp_smul (Q : V →L[ℝ] V) (t σ : ℝ) (w v : V) (n : ℕ) :
    iteratedDeriv n (fun e : ℝ => ⟪w, NormedSpace.exp ((t + e * σ) • Q) v⟫) 0 =
      σ ^ n * ⟪w, (NormedSpace.exp (t • Q) * Q ^ n) v⟫ := by
  set R := σ • Q
  have hsplit : ∀ e : ℝ, NormedSpace.exp ((t + e * σ) • Q) = NormedSpace.exp (t • Q) * NormedSpace.exp (e • R) := by
    intro e
    have hc : Commute (t • Q) (e • R) := (((Commute.refl Q).smul_left t).smul_right σ).smul_right e
    have hball : ∀ x : V →L[ℝ] V, x ∈ Metric.eball (0 : V →L[ℝ] V) (NormedSpace.expSeries ℝ (V →L[ℝ] V)).radius :=
      fun x => (NormedSpace.expSeries_radius_eq_top ℝ (V →L[ℝ] V)).symm ▸ edist_lt_top _ _
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc (hball _) (hball _), add_smul, mul_smul]
  let L : (V →L[ℝ] V) →L[ℝ] ℝ := (innerSL ℝ w).comp ((ContinuousLinearMap.apply ℝ V v).comp
    (ContinuousLinearMap.mul ℝ (V →L[ℝ] V) (NormedSpace.exp (t • Q))))
  have hL : ∀ M : V →L[ℝ] V, L M = ⟪w, (NormedSpace.exp (t • Q) * M) v⟫ := fun M => rfl
  have hfun : (fun e : ℝ => ⟪w, NormedSpace.exp ((t + e * σ) • Q) v⟫) = fun e => L (NormedSpace.exp (e • R)) := by
    funext e
    rw [hL, hsplit]
  rw [hfun, iteratedDeriv_clm_apply L (contDiff_exp_smul R), iteratedDeriv_exp_smul]
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, R, smul_pow, hL]
  rw [mul_smul_comm, smul_apply, inner_smul_right]

/-- **Transport coordinates**: `⟪w, e^{(t + e s(y)) Q} v(y)⟫` with `s` and the coordinates of `v` polynomial is a
polynomial family. -/
lemma polyFam_inner_exp (Q : V →L[ℝ] V) (t : ℝ) {s : E → ℝ} (hs : IsPoly s) {v : E → V}
    (hv : ∀ w', IsPoly (fun y => ⟪w', v y⟫)) (w : V) :
    PolyFam (fun y e => ⟪w, NormedSpace.exp ((t + e * s y) • Q) (v y)⟫) := by
  refine ⟨fun y => ?_, fun n => ?_⟩
  · exact ((innerSL ℝ w).comp (ContinuousLinearMap.apply ℝ V (v y))).contDiff.comp
      ((contDiff_exp_smul Q).comp (contDiff_const.add (contDiff_id.mul contDiff_const)))
  · refine ((hs.pow n).mul (hv (ContinuousLinearMap.adjoint (NormedSpace.exp (t • Q) * Q ^ n) w))).congr
      fun y => ?_
    rw [iteratedDeriv_inner_exp_smul, ContinuousLinearMap.adjoint_inner_left]

/-- One transport term `⟪w, e^{ε (t + e σ(x₀ + y)) Q} L(x₀ + y)⟫` (`σ`, `L` linear, finite dimension). -/
lemma polyFam_transport_term [FiniteDimensional ℝ E] (Q : V →L[ℝ] V) (ε t : ℝ) (σ : E →ₗ[ℝ] ℝ) (L : E →ₗ[ℝ] V)
    (x₀ : E) (w : V) : PolyFam (fun y e => ⟪w, NormedSpace.exp ((ε * (t + e * σ (x₀ + y))) • Q) (L (x₀ + y))⟫) := by
  refine (polyFam_inner_exp Q (ε * t) ((isPoly_linear_add σ x₀).const_mul ε)
    (fun w' => isPoly_inner_linear_add L x₀ w') w).congr fun y e => ?_
  rw [show ε * (t + e * σ (x₀ + y)) = ε * t + e * (ε * σ (x₀ + y)) by ring]

end PolyFam

section MixedCoeffLinear

variable {s : Set ℝ}

lemma contDiff_inner_of_joint {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2)) (l : ℝ) :
    ContDiff ℝ ∞ (fun e => f e l) :=
  hf.comp (contDiff_id.prodMk contDiff_const)

lemma contDiff_outer_of_joint {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2)) (i : ℕ) :
    ContDiff ℝ ∞ (fun l => iteratedDeriv i (fun e => f e l) 0) :=
  contDiff_paramL (X := Unit) (G := fun y : Unit × (ℝ × ℝ) => f y.2.1 y.2.2) (hf.comp contDiff_snd) () i

/-- Mixed Taylor coefficients are additive on jointly smooth functions. -/
lemma mixedCoeff_add_of_contDiff (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2)) (hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => g p.1 p.2)) (i j : ℕ) :
    mixedCoeff s i j (fun e l => f e l + g e l) = mixedCoeff s i j f + mixedCoeff s i j g := by
  unfold mixedCoeff
  have hin : (fun l => iteratedDeriv i (fun e => f e l + g e l) 0) =
      (fun l => iteratedDeriv i (fun e => f e l) 0) + (fun l => iteratedDeriv i (fun e => g e l) 0) := by
    funext l
    exact iteratedDeriv_add (contDiff_of_infty (contDiff_inner_of_joint hf l) i).contDiffAt
      (contDiff_of_infty (contDiff_inner_of_joint hg l) i).contDiffAt
  rw [hin, iteratedDerivWithin_add h0 hs (contDiff_of_infty (contDiff_outer_of_joint hf i) j).contDiffWithinAt
    (contDiff_of_infty (contDiff_outer_of_joint hg i) j).contDiffWithinAt]

/-- Mixed Taylor coefficients commute with constant factors. -/
lemma mixedCoeff_const_mul_of_contDiff (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2)) (c : ℝ) (i j : ℕ) :
    mixedCoeff s i j (fun e l => c * f e l) = c * mixedCoeff s i j f := by
  unfold mixedCoeff
  have hin : (fun l => iteratedDeriv i (fun e => c * f e l) 0) = fun l => c * iteratedDeriv i (fun e => f e l) 0 := by
    funext l
    exact iteratedDeriv_const_mul c (contDiff_of_infty (contDiff_inner_of_joint hf l) i).contDiffAt
  rw [hin, iteratedDerivWithin_const_mul h0 hs c
    (contDiff_of_infty (contDiff_outer_of_joint hf i) j).contDiffWithinAt]

/-- Functions of the first parameter only. -/
lemma mixedCoeff_of_fst (h : ℝ → ℝ) (i j : ℕ) :
    mixedCoeff s i j (fun e _ => h e) = if j = 0 then iteratedDeriv i h 0 else 0 := by
  unfold mixedCoeff
  exact iteratedDerivWithin_const

end MixedCoeffLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `F(y, e, l) = H(y, e) - l P₄(y) - ½ g(e, l) P₂(y)` with `H` a polynomial family, `P₄`, `P₂` polynomials and `g`
jointly smooth, every mixed Taylor coefficient of `F(y, ·, ·)` at `(0, 0)` (`l` within `[0, ∞)`) is a polynomial in
`y`. -/
lemma isPoly_mixedCoeff_of_decomp {F : E → ℝ → ℝ → ℝ} {H : E → ℝ → ℝ} {P₄ P₂ : E → ℝ} {g : ℝ → ℝ → ℝ}
    (hH : PolyFam H) (hP₄ : IsPoly P₄) (hP₂ : IsPoly P₂) (hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => g p.1 p.2))
    (hdec : ∀ y e l, F y e l = H y e - l * P₄ y - 1 / 2 * g e l * P₂ y) (i j : ℕ) :
    IsPoly (fun y => mixedCoeff (Ici 0) i j (F y)) := by
  have hs : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  have hl : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hcoef : ∀ y, mixedCoeff (Ici 0) i j (F y) =
      (if j = 0 then iteratedDeriv i (H y) 0 else 0) +
        (-P₄ y * mixedCoeff (Ici 0) i j (fun _ l => l) + -(1 / 2 * P₂ y) * mixedCoeff (Ici 0) i j g) := by
    intro y
    have hF : F y = fun e l => H y e + (-P₄ y * l + -(1 / 2 * P₂ y) * g e l) := by
      funext e l
      rw [hdec]
      ring
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => H y p.1) := (hH.1 y).comp contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => -P₄ y * p.2) := contDiff_const.mul hl
    have h3 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => -(1 / 2 * P₂ y) * g p.1 p.2) := contDiff_const.mul hg
    rw [hF, mixedCoeff_add_of_contDiff hs h0 (f := fun e _ => H y e) h1 (h2.add h3),
      mixedCoeff_add_of_contDiff hs h0 (f := fun _ l => -P₄ y * l) h2 h3,
      mixedCoeff_const_mul_of_contDiff hs h0 (f := fun _ l => l) hl,
      mixedCoeff_const_mul_of_contDiff hs h0 hg, mixedCoeff_of_fst]
  have hrest : IsPoly (fun y => -P₄ y * mixedCoeff (Ici 0) i j (fun _ l => l) +
      -(1 / 2 * P₂ y) * mixedCoeff (Ici 0) i j g) :=
    (hP₄.neg.mul (isPoly_const _)).add ((hP₂.const_mul (1 / 2)).neg.mul (isPoly_const _))
  by_cases hj : j = 0
  · exact ((hH.2 i).add hrest).congr fun y => by rw [hcoef]; simp [hj]
  · exact ((isPoly_const 0).add hrest).congr fun y => by rw [hcoef]; simp [hj]

/-- Mixed Taylor coefficients of positive order do not see additive constants: `∂^{(a,b)} (c - f) = -∂^{(a,b)} f`. -/
lemma mixedCoeff_const_sub {s : Set ℝ} (c : ℝ) (f : ℝ → ℝ → ℝ) {a b : ℕ} (hab : 0 < a + b) :
    mixedCoeff s a b (fun e l => c - f e l) = -mixedCoeff s a b f := by
  unfold mixedCoeff
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb : 0 < b := by omega
    simp only [iteratedDeriv_zero]
    rw [iteratedDerivWithin_const_sub hb c]
    exact iteratedDerivWithin_neg (f := fun l => f 0 l)
  · have hin : (fun l => iteratedDeriv a (fun e => c - f e l) 0) = -(fun l => iteratedDeriv a (fun e => f e l) 0) := by
      funext l
      rw [iteratedDeriv_const_sub ha c, iteratedDeriv_neg]
      rfl
    rw [hin, iteratedDerivWithin_neg]

/-- **A common index type** for finitely many polynomials (the form `hX` of mixedCoeff_log_gaussIntegral_eq_connected
takes). -/
lemma exists_common_monomials {ι : Type} [Fintype ι] [DecidableEq ι] {f : ι → E → ℝ} (hf : ∀ i, IsPoly (f i)) :
    ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (c : ι → A → ℝ) (k : ι → A → ℕ) (u : ∀ i a, Fin (k i a) → E),
      ∀ i x, f i x = ∑ a, monomial (c i) (k i) (u i) a x := by
  classical
  choose A hA c k U hrep using hf
  let _ : ∀ i, Fintype (A i) := hA
  refine ⟨Σ i, A i, inferInstance, inferInstance, fun i p => if p.1 = i then c p.1 p.2 else 0, fun _ p => k p.1 p.2,
    fun _ p j => U p.1 p.2 j, fun i x => ?_⟩
  rw [hrep i x, Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp [monomial]
  · intro i' _ hi'
    simp [monomial, hi']
  · simp

end GaussianBlockSpin
