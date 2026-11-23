import GaussianBlockSpin.MonomialPolynomials

/-! A polynomial in the Gaussian field `z = A ξ` as a polynomial in the independent coordinates `ξ`:
* polyVal_mulVec: `H(z) = Σ_Z a_Z z^Z` gives `H(A ξ) = Σ_X b_X ξ^X` with
  `b_{(p, X)} = Σ_{Z : Fin p → ι} a_{(p, Z)} ∏_l A_{Z_l X_l}` (pullCoef);
* sum_site_pull_le: the per-site sums of the pulled-back weights `Σ_Z a'_{(p, Z)} ∏_l A'_{Z_l X_l}` (nonnegative
  weights and kernel) are at most `(D + 1)² K^D aS`, for row and column sums of `A'` at most `K ≥ 1` and per-site sums
  of `a'` at most `aS`. -/

namespace GaussianBlockSpin

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

/-- The polynomial `Σ_Z a_Z z^Z`. -/
def polyVal (a : MonoIdx ι D → ℝ) (z : ι → ℝ) : ℝ := ∑ Z, a Z * monoVal Z.2 z

/-- The pulled-back coefficients `b_{(p, X)} = Σ_Z a_{(p, Z)} ∏_l A_{Z_l X_l}`. -/
def pullCoef (a : MonoIdx ι D → ℝ) (A : Matrix ι ι ℝ) (X : MonoIdx ι D) : ℝ :=
  ∑ Z : Fin X.1 → ι, a ⟨X.1, Z⟩ * ∏ l, A (Z l) (X.2 l)

omit [DecidableEq ι] in
lemma monoVal_mulVec {p : ℕ} (Z : Fin p → ι) (A : Matrix ι ι ℝ) (ξ : ι → ℝ) :
    monoVal Z (A *ᵥ ξ) = ∑ X : Fin p → ι, (∏ l, A (Z l) (X l)) * monoVal X ξ := by
  unfold monoVal
  have h : ∀ i, (A *ᵥ ξ) i = ∑ x, A i x * ξ x := fun i => rfl
  simp_rw [h]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [← Finset.prod_mul_distrib]

omit [DecidableEq ι] in
/-- **`H(A ξ) = Σ_X b_X ξ^X`**. -/
theorem polyVal_mulVec (a : MonoIdx ι D → ℝ) (A : Matrix ι ι ℝ) (ξ : ι → ℝ) :
    polyVal a (A *ᵥ ξ) = polyVal (pullCoef a A) ξ := by
  unfold polyVal pullCoef
  simp_rw [monoVal_mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hswap : ∀ F : (Fin p → ι) → (Fin p → ι) → ℝ, ∑ Z, ∑ X, F Z X = ∑ X, ∑ Z, F Z X :=
    fun F => Finset.sum_comm
  refine (hswap (fun Z X => a ⟨p, Z⟩ * ((∏ l, A (Z l) (X l)) * monoVal X ξ))).trans ?_
  refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun Z _ => ?_
  simp only
  ring

omit [DecidableEq ι] in
/-- Fixing one coordinate: `Σ_{X, X_l = y} ∏_{l'} f_{l'}(X_{l'}) = f_l(y) ∏_{l' ≠ l} Σ_x f_{l'}(x)`. -/
lemma sum_tuple_fix_eq {p : ℕ} (f : Fin p → ι → ℝ) (l : Fin p) (y : ι) [DecidableEq ι] :
    ∑ X : Fin p → ι, (if X l = y then ∏ l', f l' (X l') else 0) =
      f l y * ∏ l' ∈ Finset.univ.erase l, ∑ x, f l' x := by
  set g : Fin p → ι → ℝ := fun l' x => if l' = l then (if x = y then f l' x else 0) else f l' x with hg
  have hX : ∀ X : Fin p → ι, (if X l = y then ∏ l', f l' (X l') else 0) = ∏ l', g l' (X l') := by
    intro X
    rw [← Finset.mul_prod_erase Finset.univ (fun l' => g l' (X l')) (Finset.mem_univ l)]
    have herase : ∏ l' ∈ Finset.univ.erase l, g l' (X l') = ∏ l' ∈ Finset.univ.erase l, f l' (X l') :=
      Finset.prod_congr rfl fun l' hl' => by simp [hg, Finset.ne_of_mem_erase hl']
    rw [herase]
    by_cases hy : X l = y
    · simp [hg, hy, ← Finset.mul_prod_erase Finset.univ (fun l' => f l' (X l')) (Finset.mem_univ l)]
    · simp [hg, hy]
  simp_rw [hX]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum,
    ← Finset.mul_prod_erase Finset.univ (fun l' => ∑ x, g l' x) (Finset.mem_univ l)]
  congr 1
  · simp [hg]
  · exact Finset.prod_congr rfl fun l' hl' => by simp [hg, Finset.ne_of_mem_erase hl']

/-- The coefficients of the tuples through a coordinate: `Σ_{Z, Z_l = z} a'_{(p, Z)} ≤ Σ_{Z' ∋ z} a'_{Z'}`. -/
lemma sum_fiber_le_site (a' : MonoIdx ι D → ℝ) (ha' : ∀ Z, 0 ≤ a' Z) (p : Fin (D + 1)) (l : Fin p) (z : ι) :
    ∑ Z ∈ Finset.univ.filter (fun Z : Fin p → ι => Z l = z), a' ⟨p, Z⟩ ≤
      ∑ Z' ∈ Finset.univ.filter (fun Z' : MonoIdx ι D => z ∈ monoSupp Z'), a' Z' := by
  have hinj : Set.InjOn (fun Z : Fin p → ι => (⟨p, Z⟩ : MonoIdx ι D))
      (Finset.univ.filter (fun Z : Fin p → ι => Z l = z) : Set (Fin p → ι)) := fun Z1 _ Z2 _ h => by
    simpa using h
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun Z' hZ' => ?_) fun Z' _ _ => ha' Z'
  obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hZ'
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, (Finset.mem_filter.mp hZ).2⟩

/-- **The per-site bound of pulled-back weights**: for nonnegative weights `a'` (per-site sums `≤ aS`) and a
nonnegative kernel `A'` (row and column sums `≤ K`, `K ≥ 1`),
`Σ_{X ∋ y} Σ_Z a'_{(p, Z)} ∏_l A'_{Z_l X_l} ≤ (D + 1)² K^D aS`. -/
theorem sum_site_pull_le (a' : MonoIdx ι D → ℝ) (ha' : ∀ Z, 0 ≤ a' Z) (A' : ι → ι → ℝ) (hA' : ∀ z x, 0 ≤ A' z x)
    {K : ℝ} (hK : 1 ≤ K) (hrow : ∀ z, ∑ x, A' z x ≤ K) (hcol : ∀ x, ∑ z, A' z x ≤ K) {aS : ℝ}
    (haS : ∀ z, ∑ Z' ∈ Finset.univ.filter (fun Z' : MonoIdx ι D => z ∈ monoSupp Z'), a' Z' ≤ aS) (y : ι) :
    ∑ X ∈ Finset.univ.filter (fun X : MonoIdx ι D => y ∈ monoSupp X),
        ∑ Z : Fin X.1 → ι, a' ⟨X.1, Z⟩ * ∏ l, A' (Z l) (X.2 l) ≤ ((D + 1) ^ 2 : ℕ) * K ^ D * aS := by
  have haS0 : 0 ≤ aS := (Finset.sum_nonneg fun Z _ => ha' Z).trans (haS y)
  have hK0 : 0 ≤ K := by linarith
  set T : MonoIdx ι D → ℝ := fun X => ∑ Z : Fin X.1 → ι, a' ⟨X.1, Z⟩ * ∏ l, A' (Z l) (X.2 l) with hT
  have hT0 : ∀ X, 0 ≤ T X := fun X =>
    Finset.sum_nonneg fun Z _ => mul_nonneg (ha' _) (Finset.prod_nonneg fun l _ => hA' _ _)
  -- the point `y` is one of the coordinates
  have hstep : ∀ X ∈ Finset.univ.filter (fun X : MonoIdx ι D => y ∈ monoSupp X),
      T X ≤ ∑ l : Fin X.1, if X.2 l = y then T X else 0 := by
    intro X hX
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hX).2
    calc T X = (fun l' => if X.2 l' = y then T X else 0) l := by simp [hl]
      _ ≤ ∑ l', (fun l' => if X.2 l' = y then T X else 0) l' :=
          Finset.single_le_sum (f := fun l' => if X.2 l' = y then T X else 0)
            (fun l' _ => by split_ifs <;> simp [hT0 X]) (Finset.mem_univ l)
  -- one fixed coordinate
  have hfix : ∀ (p : Fin (D + 1)) (l : Fin p),
      ∑ X : Fin p → ι, (if X l = y then T ⟨p, X⟩ else 0) ≤ K ^ (p : ℕ) * aS := by
    intro p l
    have h1 : ∀ X : Fin p → ι, (if X l = y then T ⟨p, X⟩ else 0) =
        ∑ Z : Fin p → ι, a' ⟨p, Z⟩ * (if X l = y then ∏ l', A' (Z l') (X l') else 0) := by
      intro X
      by_cases hX : X l = y <;> simp [hT, hX]
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have h2 : ∀ Z : Fin p → ι, a' ⟨p, Z⟩ * ∑ X : Fin p → ι, (if X l = y then ∏ l', A' (Z l') (X l') else 0) ≤
        a' ⟨p, Z⟩ * (A' (Z l) y * K ^ ((p : ℕ) - 1)) := by
      intro Z
      rw [sum_tuple_fix_eq (fun l' x => A' (Z l') x) l y]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hA' _ _)) (ha' _)
      calc ∏ l' ∈ Finset.univ.erase l, ∑ x, A' (Z l') x ≤ ∏ l' ∈ Finset.univ.erase l, K :=
            Finset.prod_le_prod₀ (fun l' _ => Finset.sum_nonneg fun x _ => hA' _ _) fun l' _ => hrow _
        _ = K ^ ((p : ℕ) - 1) := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    refine (Finset.sum_le_sum fun Z _ => h2 Z).trans ?_
    have h3 : ∑ Z : Fin p → ι, a' ⟨p, Z⟩ * (A' (Z l) y * K ^ ((p : ℕ) - 1)) =
        K ^ ((p : ℕ) - 1) * ∑ z, A' z y * ∑ Z ∈ Finset.univ.filter (fun Z : Fin p → ι => Z l = z), a' ⟨p, Z⟩ := by
      rw [Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ (fun Z : Fin p → ι => Z l)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Z hZ => ?_
      rw [(Finset.mem_filter.mp hZ).2]
      ring
    rw [h3]
    have h4 : ∑ z, A' z y * ∑ Z ∈ Finset.univ.filter (fun Z : Fin p → ι => Z l = z), a' ⟨p, Z⟩ ≤ K * aS :=
      calc ∑ z, A' z y * ∑ Z ∈ Finset.univ.filter (fun Z : Fin p → ι => Z l = z), a' ⟨p, Z⟩
          ≤ ∑ z, A' z y * aS := Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left ((sum_fiber_le_site a' ha' p l z).trans (haS z)) (hA' _ _)
        _ = (∑ z, A' z y) * aS := by rw [Finset.sum_mul]
        _ ≤ K * aS := mul_le_mul_of_nonneg_right (hcol y) haS0
    calc K ^ ((p : ℕ) - 1) * ∑ z, A' z y * ∑ Z ∈ Finset.univ.filter (fun Z : Fin p → ι => Z l = z), a' ⟨p, Z⟩
        ≤ K ^ ((p : ℕ) - 1) * (K * aS) := mul_le_mul_of_nonneg_left h4 (pow_nonneg hK0 _)
      _ = K ^ (p : ℕ) * aS := by
          have hp : 1 ≤ (p : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h => (Fin.elim0 (h ▸ l))
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]
  calc ∑ X ∈ Finset.univ.filter (fun X : MonoIdx ι D => y ∈ monoSupp X), T X
      ≤ ∑ X ∈ Finset.univ.filter (fun X : MonoIdx ι D => y ∈ monoSupp X),
          ∑ l : Fin X.1, (if X.2 l = y then T X else 0) := Finset.sum_le_sum hstep
    _ ≤ ∑ X : MonoIdx ι D, ∑ l : Fin X.1, (if X.2 l = y then T X else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun X _ _ =>
          Finset.sum_nonneg fun l _ => by split_ifs <;> simp [hT0 X]
    _ = ∑ p : Fin (D + 1), ∑ l : Fin p, ∑ X : Fin p → ι, (if X l = y then T ⟨p, X⟩ else 0) := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun p _ => ?_
        show ∑ X : Fin p → ι, ∑ l : Fin p, (if X l = y then T ⟨p, X⟩ else 0) = _
        exact Finset.sum_comm
    _ ≤ ∑ p : Fin (D + 1), ∑ _l : Fin p, K ^ (p : ℕ) * aS :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun l _ => hfix p l
    _ ≤ ∑ _p : Fin (D + 1), ((D + 1 : ℕ) : ℝ) * (K ^ D * aS) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hpD : (p : ℕ) ≤ D := Nat.lt_succ_iff.mp p.isLt
        have h1 : ((p : ℕ) : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := by exact_mod_cast hpD.trans (Nat.le_succ D)
        have h2 : K ^ (p : ℕ) ≤ K ^ D := pow_le_pow_right₀ hK hpD
        gcongr
    _ = ((D + 1) ^ 2 : ℕ) * K ^ D * aS := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end GaussianBlockSpin
