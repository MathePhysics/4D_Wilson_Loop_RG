/-
Forms, the pairings, and the covariant differences of BALABAN_CORE.tex
(`def:configurations`(iii)–(iv), `def:differences`), with `lem:covariance` and
`lem:product-plaquette`.

Forms are given by their components (`def:configurations`(iii)): a `1`-form by `A_μ(x)`, a
`2`-form by `F_{μν}(x)`, antisymmetric in `μ ≠ ν` where this is used. The spacing `a = a_j` of the
lattice is a complex parameter; the core has `a_j > 0`, and `a ≠ 0` is assumed only where it is
divided out.
-/
import CoreLean.Lattice

open Matrix Complex

namespace CoreLean

variable {N n : ℕ} [NeZero n]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `0`-forms. -/
abbrev Form0 (N n : ℕ) := Site n → Matrix (Fin N) (Fin N) ℂ
/-- `1`-forms, by their components `A_μ(x) = A(x, x + a e_μ)`. -/
abbrev Form1 (N n : ℕ) := Fin 4 → Site n → Matrix (Fin N) (Fin N) ℂ
/-- `2`-forms, by their components `F_{μν}(x) = F(p_{μν}(x))`. -/
abbrev Form2 (N n : ℕ) := Fin 4 → Fin 4 → Site n → Matrix (Fin N) (Fin N) ℂ

/-! ### The adjoint action and the normalised trace -/

/-- The adjoint action `Ad_W X = W X W⁻¹` (`def:group`(iv)). -/
def Ad (W : GLN) (X : Mat) : Mat := (W : Mat) * X * ((W⁻¹ : GLN) : Mat)

omit [NeZero n] in
lemma Ad_mul (W V : GLN) (X : Mat) : Ad (W * V) X = Ad W (Ad V X) := by
  simp [Ad, Matrix.mul_assoc]

@[simp] lemma Ad_one (X : Mat) : Ad (1 : GLN) X = X := by simp [Ad]

lemma Ad_add (W : GLN) (X Y : Mat) : Ad W (X + Y) = Ad W X + Ad W Y := by
  simp [Ad, Matrix.mul_add, Matrix.add_mul]

lemma Ad_sub (W : GLN) (X Y : Mat) : Ad W (X - Y) = Ad W X - Ad W Y := by
  simp [Ad, Matrix.mul_sub, Matrix.sub_mul]

lemma Ad_neg (W : GLN) (X : Mat) : Ad W (-X) = -Ad W X := by
  simp [Ad, Matrix.mul_neg, Matrix.neg_mul]

lemma Ad_smul (W : GLN) (c : ℂ) (X : Mat) : Ad W (c • X) = c • Ad W X := by
  simp [Ad, Matrix.mul_smul, Matrix.smul_mul]

lemma Ad_sum {ι : Type*} (s : Finset ι) (W : GLN) (f : ι → Mat) :
    Ad W (∑ i ∈ s, f i) = ∑ i ∈ s, Ad W (f i) := by
  simp [Ad, Matrix.mul_sum, Matrix.sum_mul]

lemma Ad_inv_Ad (W : GLN) (X : Mat) : Ad W⁻¹ (Ad W X) = X := by
  rw [← Ad_mul, inv_mul_cancel, Ad_one]

/-- `Ad_{u W v⁻¹} Ad_v = Ad_u Ad_W`. -/
lemma Ad_gauge (u W v : GLN) (X : Mat) : Ad (u * W * v⁻¹) (Ad v X) = Ad u (Ad W X) := by
  rw [Ad_mul, Ad_mul, Ad_inv_Ad]

/-- `Tr((Ad_W X) Y) = Tr(X Ad_{W⁻¹} Y)`. -/
lemma trace_Ad_mul (W : GLN) (X Y : Mat) : (Ad W X * Y).trace = (X * Ad W⁻¹ Y).trace := by
  unfold Ad
  rw [inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma ntr_Ad_mul (W : GLN) (X Y : Mat) : ntr (Ad W X * Y) = ntr (X * Ad W⁻¹ Y) := by
  unfold ntr; rw [trace_Ad_mul]

lemma ntr_smul (c : ℂ) (X : Mat) : ntr (c • X) = c * ntr X := by
  unfold ntr; rw [Matrix.trace_smul, smul_eq_mul]; ring

lemma ntr_sub (X Y : Mat) : ntr (X - Y) = ntr X - ntr Y := by
  unfold ntr; rw [Matrix.trace_sub]; ring

lemma ntr_sum {ι : Type*} (s : Finset ι) (f : ι → Mat) : ntr (∑ i ∈ s, f i) = ∑ i ∈ s, ntr (f i) := by
  unfold ntr; rw [Matrix.trace_sum, Finset.mul_sum]

/-! ### Pairings and differences -/

variable (a : ℂ)

/-- `⟨λ, λ'⟩ = Σ_x a⁴ tr λ(x) λ'(x)` (`eq:pairing`), bilinear. -/
noncomputable def pair0 (l l' : Form0 N n) : ℂ := ∑ x, a ^ 4 * ntr (l x * l' x)

/-- `⟨A, A'⟩ = Σ_μ ⟨A_μ, A'_μ⟩`. -/
noncomputable def pair1 (A A' : Form1 N n) : ℂ := ∑ μ, pair0 a (A μ) (A' μ)

/-- `⟨F, F'⟩ = Σ_{μ<ν} ⟨F_{μν}, F'_{μν}⟩`. -/
noncomputable def pair2 (F F' : Form2 N n) : ℂ :=
  ∑ μ, ∑ ν, if μ < ν then pair0 a (F μ ν) (F' μ ν) else 0

/-- The forward difference `(D_{U,μ} λ)(x) = a⁻¹ (Ad_{U(x, x+ae_μ)} λ(x + ae_μ) - λ(x))`
(`eq:forward-difference`). -/
noncomputable def Dfw (U : Config N n) (μ : Fin 4) (l : Form0 N n) : Form0 N n :=
  fun x => a⁻¹ • (Ad (U μ x) (l (x + unit n μ)) - l x)

/-- The backward difference `(D^*_{U,μ} λ)(x) = a⁻¹ (Ad_{U(x, x-ae_μ)} λ(x - ae_μ) - λ(x))`
(`eq:backward-difference`). -/
noncomputable def Dbw (U : Config N n) (μ : Fin 4) (l : Form0 N n) : Form0 N n :=
  fun x => a⁻¹ • (Ad (U.val ⟨x, μ, false⟩) (l (x - unit n μ)) - l x)

/-- `D_U λ`, the `1`-form with the components `D_{U,μ} λ` (`def:differences`(i)). -/
noncomputable def D0 (U : Config N n) (l : Form0 N n) : Form1 N n := fun μ => Dfw a U μ l

/-- `D^*_U A = Σ_μ D^*_{U,μ} A_μ` (`def:differences`(i)). -/
noncomputable def Ds1 (U : Config N n) (A : Form1 N n) : Form0 N n :=
  fun x => ∑ μ, Dbw a U μ (A μ) x

/-- `(D_U A)_{μν} = D_{U,μ} A_ν - D_{U,ν} A_μ` (`def:differences`(ii)). -/
noncomputable def D1 (U : Config N n) (A : Form1 N n) : Form2 N n :=
  fun μ ν x => Dfw a U μ (A ν) x - Dfw a U ν (A μ) x

/-- `(D^*_U F)_μ = Σ_{ν≠μ} D^*_{U,ν} F_{νμ}` (`def:differences`(ii)). -/
noncomputable def Ds2 (U : Config N n) (F : Form2 N n) : Form1 N n :=
  fun μ x => ∑ ν, if ν ≠ μ then Dbw a U ν (F ν μ) x else 0

/-- The covariant Laplacian `Δ_U = Σ_μ D^*_{U,μ} D_{U,μ}` (`def:differences`(iv)); on
`1`-forms it acts component by component. -/
noncomputable def Lap (U : Config N n) (l : Form0 N n) : Form0 N n :=
  fun x => ∑ μ, Dbw a U μ (Dfw a U μ l) x

/-- `Ad_u` on `0`-forms: `(Ad_u λ)(x) = Ad_{u(x)} λ(x)`. -/
def AdF0 (u : Site n → GLN) (l : Form0 N n) : Form0 N n := fun x => Ad (u x) (l x)
/-- `Ad_u` on `1`-forms, component by component. -/
def AdF1 (u : Site n → GLN) (A : Form1 N n) : Form1 N n := fun μ x => Ad (u x) (A μ x)
/-- `Ad_u` on `2`-forms, component by component. -/
def AdF2 (u : Site n → GLN) (F : Form2 N n) : Form2 N n := fun μ ν x => Ad (u x) (F μ ν x)

/-! ### `lem:covariance`(i): the adjoints -/

lemma pair0_sum_right {ι : Type*} (s : Finset ι) (l : Form0 N n) (f : ι → Form0 N n) :
    pair0 a l (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, pair0 a l (f i) := by
  unfold pair0
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_sum, ntr_sum, Finset.mul_sum]

/-- `lem:covariance`(i): `⟨D_{U,μ} λ, λ'⟩ = ⟨λ, D^*_{U,μ} λ'⟩`. -/
theorem pair0_Dfw (U : Config N n) (μ : Fin 4) (l l' : Form0 N n) :
    pair0 a (Dfw a U μ l) l' = pair0 a l (Dbw a U μ l') := by
  have hL : pair0 a (Dfw a U μ l) l' =
      ∑ x, a ^ 4 * (a⁻¹ * ntr (Ad (U μ x) (l (x + unit n μ)) * l' x)) -
        ∑ x, a ^ 4 * (a⁻¹ * ntr (l x * l' x)) := by
    unfold pair0 Dfw
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.smul_mul, ntr_smul, Matrix.sub_mul, ntr_sub]; ring
  have hR : pair0 a l (Dbw a U μ l') =
      ∑ x, a ^ 4 * (a⁻¹ * ntr (l x * Ad (U.val ⟨x, μ, false⟩) (l' (x - unit n μ)))) -
        ∑ x, a ^ 4 * (a⁻¹ * ntr (l x * l' x)) := by
    unfold pair0 Dbw
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mul_smul, ntr_smul, Matrix.mul_sub, ntr_sub]; ring
  rw [hL, hR, sub_left_inj]
  rw [← (Equiv.subRight (unit n μ)).sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [ntr_Ad_mul]
  simp [Config.val]

/-- `lem:covariance`(i): `⟨D_U λ, A⟩ = ⟨λ, D^*_U A⟩`. -/
theorem pair1_D0 (U : Config N n) (l : Form0 N n) (A : Form1 N n) :
    pair1 a (D0 a U l) A = pair0 a l (Ds1 a U A) := by
  unfold pair1 D0 Ds1
  rw [pair0_sum_right]
  exact Finset.sum_congr rfl fun μ _ => pair0_Dfw a U μ l (A μ)

lemma pair0_sub_left (l l' l'' : Form0 N n) :
    pair0 a (fun x => l x - l' x) l'' = pair0 a l l'' - pair0 a l' l'' := by
  unfold pair0
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.sub_mul, ntr_sub, mul_sub]

lemma pair0_neg_right (l l' : Form0 N n) :
    pair0 a l (fun x => -l' x) = -pair0 a l l' := by
  unfold pair0
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_neg, show -(l x * l' x) = (-1 : ℂ) • (l x * l' x) by simp, ntr_smul]
  ring

/-- `lem:covariance`(i): `⟨D_U A, F⟩ = ⟨A, D^*_U F⟩` for a `2`-form `F`
(`F_{νμ} = -F_{μν}` for `μ ≠ ν`). -/
theorem pair2_D1 (U : Config N n) (A : Form1 N n) (F : Form2 N n)
    (hF : ∀ μ ν, μ ≠ ν → F ν μ = fun x => -F μ ν x) :
    pair2 a (D1 a U A) F = pair1 a A (Ds2 a U F) := by
  -- both sides equal `Σ_{μ ≠ ν} ⟨D_{U,μ} A_ν, F_{μν}⟩`
  have hL : pair2 a (D1 a U A) F =
      ∑ μ, ∑ ν, if μ ≠ ν then pair0 a (Dfw a U μ (A ν)) (F μ ν) else 0 := by
    unfold pair2 D1
    simp only [pair0_sub_left]
    simp only [Fin.sum_univ_four]
    simp
    rw [hF 0 1 (by decide), hF 0 2 (by decide), hF 0 3 (by decide), hF 1 2 (by decide),
      hF 1 3 (by decide), hF 2 3 (by decide)]
    simp only [pair0_neg_right]
    ring
  have hR : pair1 a A (Ds2 a U F) =
      ∑ ν, ∑ μ, if μ ≠ ν then pair0 a (A ν) (Dbw a U μ (F μ ν)) else 0 := by
    unfold pair1 Ds2
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [show (fun x => ∑ μ, if μ ≠ ν then Dbw a U μ (F μ ν) x else 0) =
        (fun x => ∑ μ, (if μ ≠ ν then Dbw a U μ (F μ ν) else fun _ => 0) x) by
      funext x; refine Finset.sum_congr rfl fun μ _ => ?_; split_ifs <;> rfl]
    rw [pair0_sum_right]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs
    · rfl
    · unfold pair0; simp [ntr]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
  split_ifs
  · exact pair0_Dfw a U μ (A ν) (F μ ν)
  · rfl

/-! ### `lem:covariance`(ii): covariance -/

/-- `D_{U^u,μ} Ad_u = Ad_u D_{U,μ}`. -/
theorem Dfw_gauge (U : Config N n) (u : Site n → GLN) (μ : Fin 4) (l : Form0 N n) :
    Dfw a (U.gauge u) μ (AdF0 u l) = AdF0 u (Dfw a U μ l) := by
  funext x
  simp only [Dfw, AdF0, Config.gauge, Ad_gauge, Ad_smul, Ad_sub]

/-- `D^*_{U^u,μ} Ad_u = Ad_u D^*_{U,μ}`. -/
theorem Dbw_gauge (U : Config N n) (u : Site n → GLN) (μ : Fin 4) (l : Form0 N n) :
    Dbw a (U.gauge u) μ (AdF0 u l) = AdF0 u (Dbw a U μ l) := by
  funext x
  have h := Config.val_gauge U u ⟨x, μ, false⟩
  simp only [Bond.plus, Bool.false_eq_true, ↓reduceIte] at h
  simp only [Dbw, AdF0, h, Ad_gauge, Ad_smul, Ad_sub]

theorem D0_gauge (U : Config N n) (u : Site n → GLN) (l : Form0 N n) :
    D0 a (U.gauge u) (AdF0 u l) = AdF1 u (D0 a U l) := by
  funext μ x
  simp only [D0, AdF1]
  rw [Dfw_gauge]; rfl

theorem Ds1_gauge (U : Config N n) (u : Site n → GLN) (A : Form1 N n) :
    Ds1 a (U.gauge u) (AdF1 u A) = AdF0 u (Ds1 a U A) := by
  funext x
  simp only [Ds1, AdF0, Ad_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have : (AdF1 u A) μ = AdF0 u (A μ) := rfl
  rw [this, Dbw_gauge]; rfl

theorem D1_gauge (U : Config N n) (u : Site n → GLN) (A : Form1 N n) :
    D1 a (U.gauge u) (AdF1 u A) = AdF2 u (D1 a U A) := by
  funext μ ν x
  have h1 : (AdF1 u A) ν = AdF0 u (A ν) := rfl
  have h2 : (AdF1 u A) μ = AdF0 u (A μ) := rfl
  simp only [D1, AdF2, h1, h2, Dfw_gauge, Ad_sub]; rfl

theorem Ds2_gauge (U : Config N n) (u : Site n → GLN) (F : Form2 N n) :
    Ds2 a (U.gauge u) (AdF2 u F) = AdF1 u (Ds2 a U F) := by
  funext μ x
  simp only [Ds2, AdF1, Ad_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · have : (AdF2 u F) ν μ = AdF0 u (F ν μ) := rfl
    rw [this, Dbw_gauge]; rfl
  · simp [Ad]

theorem Lap_gauge (U : Config N n) (u : Site n → GLN) (l : Form0 N n) :
    Lap a (U.gauge u) (AdF0 u l) = AdF0 u (Lap a U l) := by
  funext x
  simp only [Lap, AdF0, Ad_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Dfw_gauge, Dbw_gauge]; rfl

/-! ### `lem:covariance`(iii): the commutator of the differences -/

/-- `lem:covariance`(iii): with `γ = ((x, x+ae_ν), (x+ae_ν, x+ae_ν+ae_μ))`,
`(D_U D_U λ)_{μν}(x) = a^{-2} (Ad_{U(∂p_{μν}(x))} - 1) Ad_{U(γ)} λ(x + ae_μ + ae_ν)`. -/
theorem D1_D0 (U : Config N n) (l : Form0 N n) (μ ν : Fin 4) (x : Site n) :
    D1 a U (D0 a U l) μ ν x =
      (a ^ 2)⁻¹ • (Ad (plaq U μ ν x) (Ad (U ν x * U μ (x + unit n ν))
          (l (x + unit n μ + unit n ν))) -
        Ad (U ν x * U μ (x + unit n ν)) (l (x + unit n μ + unit n ν))) := by
  have hkey : U μ x * U ν (x + unit n μ) = plaq U μ ν x * (U ν x * U μ (x + unit n ν)) := by
    rw [plaq_eq]; group
  have hcomm : x + unit n ν + unit n μ = x + unit n μ + unit n ν := by abel
  simp only [D1, D0, Dfw, Ad_smul, Ad_sub, ← Ad_mul, hcomm]
  rw [hkey, Ad_mul (plaq U μ ν x)]
  rw [show (a ^ 2)⁻¹ = a⁻¹ * a⁻¹ by rw [sq, mul_inv]]
  module

/-! ### `lem:product-plaquette` -/

/-- The exponential of a matrix as an element of `GL(N, ℂ)`. -/
noncomputable def expU (X : Mat) : GLN := (Matrix.isUnit_exp X).unit

@[simp] lemma expU_val (X : Mat) : ((expU X : GLN) : Mat) = NormedSpace.exp X :=
  IsUnit.unit_spec _

lemma expU_conj (W : GLN) (X : Mat) : W * expU X * W⁻¹ = expU (Ad W X) := by
  ext1
  simp only [Units.val_mul, expU_val, Ad]
  rw [Matrix.exp_units_conj]

lemma expU_inv (X : Mat) : (expU X)⁻¹ = expU (-X) := by
  rw [inv_eq_iff_mul_eq_one]
  ext1
  simp only [Units.val_mul, expU_val, Units.val_one]
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)), add_neg_cancel,
    NormedSpace.exp_zero]

/-- The configuration `e^{iaA} U`, with the values `e^{iaA(b)} U(b)` on the positive bonds. -/
noncomputable def expMul (A : Form1 N n) (U : Config N n) : Config N n :=
  fun μ x => expU ((I * a) • A μ x) * U μ x

/-- `lem:product-plaquette`, `eq:product-plaquette`:
`(e^{iaA} U)(∂p) = e^{iaA_1} e^{iaA_2} U(∂p) e^{iaA_3} e^{iaA_4}` with
`A_1 = A_μ(x)`, `A_2 = Ad_{U(b_1)} A(b_2)`, `A_3 = Ad_{U(b_4)⁻¹} A(b_3)`, `A_4 = -A_ν(x)`. -/
theorem plaq_expMul (A : Form1 N n) (U : Config N n) (μ ν : Fin 4) (x : Site n) :
    plaq (expMul a A U) μ ν x =
      expU ((I * a) • A μ x) * expU ((I * a) • Ad (U μ x) (A ν (x + unit n μ))) *
        plaq U μ ν x * expU ((I * a) • Ad (U ν x) (-A μ (x + unit n ν))) *
        expU ((I * a) • -A ν x) := by
  rw [plaq_eq, plaq_eq]
  simp only [expMul]
  rw [← Ad_smul, ← Ad_smul, ← expU_conj, ← expU_conj, smul_neg, smul_neg, ← expU_inv,
    ← expU_inv]
  group

/-- `eq:product-exponents`: `A_2 = A_ν(x) + a (D_{U,μ} A_ν)(x)`. -/
theorem productExponent_two (ha : a ≠ 0) (A : Form1 N n) (U : Config N n) (μ ν : Fin 4)
    (x : Site n) : Ad (U μ x) (A ν (x + unit n μ)) = A ν x + a • Dfw a U μ (A ν) x := by
  simp only [Dfw, smul_smul, mul_inv_cancel₀ ha, one_smul]
  abel

/-- `eq:product-exponents`: `A_3 = -A_μ(x) - a (D_{U,ν} A_μ)(x)`. -/
theorem productExponent_three (ha : a ≠ 0) (A : Form1 N n) (U : Config N n) (μ ν : Fin 4)
    (x : Site n) : Ad (U ν x) (-A μ (x + unit n ν)) = -A μ x - a • Dfw a U ν (A μ) x := by
  simp only [Dfw, smul_smul, mul_inv_cancel₀ ha, one_smul, Ad_neg]
  abel

/-- `lem:product-plaquette`: the sum of the four exponents is `a (D_U A)(p)`. -/
theorem productExponent_sum (ha : a ≠ 0) (A : Form1 N n) (U : Config N n) (μ ν : Fin 4)
    (x : Site n) :
    A μ x + Ad (U μ x) (A ν (x + unit n μ)) + Ad (U ν x) (-A μ (x + unit n ν)) + -A ν x =
      a • D1 a U A μ ν x := by
  rw [productExponent_two a ha, productExponent_three a ha]
  simp only [D1, smul_sub]
  abel

end CoreLean
