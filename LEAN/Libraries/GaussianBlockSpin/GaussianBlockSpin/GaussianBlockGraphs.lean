import GaussianBlockSpin.PartitionCumulants
import GaussianBlockSpin.GaussianGraphs

/-! Gaussian joint cumulants of distinct polynomial vertices and of the blocks of a slot partition as sums over connected
graphs. jointCumulant_moments_sum_eq (multilinear expansion with vertex-dependent pieces);
jointCumulant_gaussProb_eq_connected (vertex polynomials `P_v = Σ_a c_{v,a} ∏_i ⟪u_{v,a,i}, x⟫`: the joint cumulant is
the sum over monomial choices of the connected-matching sums); blockCumulant_gaussProb_eq_connected (the same for the
blocks of a partition of derivative slots, enumerated by their smallest slots, `blockEnum`). Together with
PartitionCumulants this expresses the joint cumulants of the integrated derivatives of `e^F` for Gaussian polynomial
derivatives of `F` by connected graphs (III Sect. 1). -/

open MeasureTheory
open scoped RealInnerProductSpace

namespace GaussianBlockSpin

section Multilinear

variable {r : ℕ}

/-- **Joint cumulants of sums are sums of joint cumulants of the pieces** (vertex-dependent pieces): for
`X_v = Σ_{a ∈ A} V_{v,a}` under a probability measure (all products of partial sums integrable),
`κ(X_1, …, X_r) = Σ_{g : Fin r → A} κ(V_{1,g(1)}, …, V_{r,g(r)})`. -/
theorem jointCumulant_moments_sum_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Type*} [Fintype A] [DecidableEq A] (V : Fin r → A → Ω → ℝ)
    (hint : ∀ (T : Finset (Fin r)) (t : Fin r → Finset A), Integrable (fun ω => ∏ v ∈ T, ∑ a ∈ t v, V v a ω) μ) :
    jointCumulant (fun T => ∫ ω, ∏ v ∈ T, ∑ a, V v a ω ∂μ) Finset.univ =
      ∑ g : Fin r → A, jointCumulant (fun T => ∫ ω, ∏ v ∈ T, V v (g v) ω ∂μ) Finset.univ := by
  let tf : (Fin r → Option A) → Fin r → Finset A := fun f v => (f v).elim Finset.univ (fun a => {a})
  let M : (Fin r → Option A) → Finset (Fin r) → ℝ := fun f T => ∫ ω, ∏ v ∈ T, ∑ a ∈ tf f v, V v a ω ∂μ
  have hupd : ∀ f u a, tf (Function.update f u (some a)) u = {a} := fun f u a => by
    simp [tf]
  have hupd' : ∀ f u a v, v ≠ u → tf (Function.update f u (some a)) v = tf f v := fun f u a v hv => by
    simp [tf, Function.update_of_ne hv]
  have hsum : ∀ f u, f u = none → ∀ T, u ∈ T → M f T = ∑ a, M (Function.update f u (some a)) T := by
    intro f u hfu T hu
    have hpt : ∀ ω, ∏ v ∈ T, ∑ b ∈ tf f v, V v b ω =
        ∑ a, ∏ v ∈ T, ∑ b ∈ tf (Function.update f u (some a)) v, V v b ω := by
      intro ω
      rw [← Finset.mul_prod_erase T _ hu]
      have htu : tf f u = Finset.univ := by simp [tf, hfu]
      rw [htu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_prod_erase T _ hu, hupd, Finset.sum_singleton]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [hupd' f u a v (Finset.ne_of_mem_erase hv)]
    simp only [M]
    simp_rw [hpt]
    exact integral_finsetSum _ fun a _ => hint T _
  have hloc : ∀ f u, f u = none → ∀ a T, u ∉ T → M (Function.update f u (some a)) T = M f T := by
    intro f u _ a T hu
    simp only [M]
    congr 1
    funext ω
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hupd' f u a v (fun h => hu (h ▸ hv))]
  have hml := jointCumulant_multilinear M hsum hloc
  have hnone : M (fun _ => none) = fun T => ∫ ω, ∏ v ∈ T, ∑ a, V v a ω ∂μ := by
    funext T
    simp [M, tf]
  have hsome : ∀ g : Fin r → A, M (fun v => some (g v)) = fun T => ∫ ω, ∏ v ∈ T, V v (g v) ω ∂μ := by
    intro g
    funext T
    simp [M, tf]
  rw [hnone] at hml
  rw [hml]
  exact Finset.sum_congr rfl fun g _ => by rw [hsome g]

end Multilinear

section DistinctVertices

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : Type*}

/-- The vertex of a leg of the configuration `g` for vertex-dependent monomials (`k v a` legs at vertex `v` with monomial
`a`; legs `Σ_v Fin (k v (g v))` flattened). -/
def legVertexV (k : Fin r → A → ℕ) (g : Fin r → A) (l : Fin (∑ v, k v (g v))) : Fin r :=
  (finSigmaFinEquiv.symm l).1

/-- The vector of a leg of the configuration `g` for vertex-dependent monomials. -/
noncomputable def legVectorV (k : Fin r → A → ℕ) (u : ∀ v a, Fin (k v a) → E) (g : Fin r → A)
    (l : Fin (∑ v, k v (g v))) : E :=
  u (finSigmaFinEquiv.symm l).1 (g (finSigmaFinEquiv.symm l).1) (finSigmaFinEquiv.symm l).2

lemma legsOf_legVertexV (k : Fin r → A → ℕ) (g : Fin r → A) (R : Finset (Fin r)) :
    legsOf (legVertexV k g) R = (R.sigma fun v => (Finset.univ : Finset (Fin (k v (g v))))).map
      finSigmaFinEquiv.toEmbedding := by
  ext l
  rw [Finset.mem_map_equiv, Finset.mem_sigma]
  unfold legsOf legVertexV
  rw [Finset.mem_filter]
  simp

lemma prod_monomialV (c : Fin r → A → ℝ) (k : Fin r → A → ℕ) (u : ∀ v a, Fin (k v a) → E) (g : Fin r → A)
    (R : Finset (Fin r)) (x : E) :
    ∏ v ∈ R, monomial (c v) (k v) (u v) (g v) x =
      (∏ v ∈ R, c v (g v)) * linProd (legsOf (legVertexV k g) R) (legVectorV k u g) x := by
  unfold monomial linProd
  rw [Finset.prod_mul_distrib, legsOf_legVertexV, Finset.prod_map, Finset.prod_sigma]
  congr 1
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun i _ => ?_
  simp only [Equiv.coe_toEmbedding, legVectorV]
  rw [Equiv.symm_apply_apply]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_prod_monomialV {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    (c : Fin r → A → ℝ) (k : Fin r → A → ℕ) (u : ∀ v a, Fin (k v a) → E) (g : Fin r → A) (R : Finset (Fin r)) :
    ∫ x, ∏ v ∈ R, monomial (c v) (k v) (u v) (g v) x ∂gaussProb T =
      (∏ v ∈ R, c v (g v)) * (gaussMoment T (legsOf (legVertexV k g) R) (legVectorV k u g) /
        gaussMoment T (∅ : Finset (Fin (∑ v, k v (g v)))) (legVectorV k u g)) := by
  simp_rw [prod_monomialV c k u g R]
  rw [integral_const_mul, integral_gaussProb hT hpos]
  congr 2
  unfold gaussMoment linProd
  simp

/-- All products of partial sums of vertex-dependent monomials are integrable for the normalised Gaussian measure. -/
lemma integrable_prod_sum_monomialV [Fintype A] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (c : Fin r → A → ℝ) (k : Fin r → A → ℕ) (u : ∀ v a, Fin (k v a) → E)
    (R : Finset (Fin r)) (t : Fin r → Finset A) :
    Integrable (fun x => ∏ v ∈ R, ∑ a ∈ t v, monomial (c v) (k v) (u v) a x) (gaussProb T) := by
  rw [integrable_gaussProb_iff hT hpos]
  set D := ∑ v, ∑ a, k v a
  set Ka : Fin r → A → ℝ := fun v a => |c v a| * ∏ i, ‖u v a i‖
  set K1 := ∑ v, ∑ a, Ka v a
  have hKa : ∀ v a, 0 ≤ Ka v a := fun v a => by positivity
  have hmono : ∀ v a x, |monomial (c v) (k v) (u v) a x| ≤ Ka v a * (1 + ‖x‖) ^ D := by
    intro v a x
    unfold monomial
    rw [abs_mul, Finset.abs_prod]
    have h1 : ∏ i, |⟪u v a i, x⟫| ≤ ∏ i, (‖u v a i‖ * ‖x‖) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => abs_real_inner_le_norm _ _
    have h2 : ∏ i : Fin (k v a), (‖u v a i‖ * ‖x‖) ≤ (∏ i, ‖u v a i‖) * (1 + ‖x‖) ^ D := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hk : k v a ≤ D := (Finset.single_le_sum (fun b _ => Nat.zero_le (k v b)) (Finset.mem_univ a)).trans
        (Finset.single_le_sum (f := fun w => ∑ b, k w b) (fun w _ => Nat.zero_le _) (Finset.mem_univ v))
      have : ‖x‖ ^ k v a ≤ (1 + ‖x‖) ^ D :=
        (pow_le_pow_left₀ (norm_nonneg x) (by linarith) (k v a)).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hk)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc |c v a| * ∏ i, |⟪u v a i, x⟫| ≤ |c v a| * ((∏ i, ‖u v a i‖) * (1 + ‖x‖) ^ D) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
      _ = Ka v a * (1 + ‖x‖) ^ D := by simp only [Ka]; ring
  have hsum : ∀ v x, |∑ a ∈ t v, monomial (c v) (k v) (u v) a x| ≤ K1 * (1 + ‖x‖) ^ D := by
    intro v x
    calc |∑ a ∈ t v, monomial (c v) (k v) (u v) a x| ≤ ∑ a ∈ t v, |monomial (c v) (k v) (u v) a x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ t v, Ka v a * (1 + ‖x‖) ^ D := Finset.sum_le_sum fun a _ => hmono v a x
      _ ≤ ∑ a, Ka v a * (1 + ‖x‖) ^ D :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => by positivity
      _ = (∑ a, Ka v a) * (1 + ‖x‖) ^ D := by rw [← Finset.sum_mul]
      _ ≤ K1 * (1 + ‖x‖) ^ D := by
          gcongr
          exact Finset.single_le_sum (f := fun w => ∑ a, Ka w a) (fun w _ => Finset.sum_nonneg fun a _ => hKa w a)
            (Finset.mem_univ v)
  refine integrable_mul_gaussWeight_of_le_one_add hT hpos ?_ (K := K1 ^ R.card) (D * R.card) fun x => ?_
  · refine continuous_finsetProd R fun v _ => continuous_finsetSum _ fun a _ => ?_
    unfold monomial
    exact continuous_const.mul (continuous_finsetProd _ fun i _ => continuous_const.inner continuous_id)
  · rw [Finset.abs_prod]
    calc ∏ v ∈ R, |∑ a ∈ t v, monomial (c v) (k v) (u v) a x| ≤ ∏ v ∈ R, (K1 * (1 + ‖x‖) ^ D) :=
          Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) fun v _ => hsum v x
      _ = K1 ^ R.card * (1 + ‖x‖) ^ (D * R.card) := by rw [Finset.prod_const, mul_pow, pow_mul]

/-- **Gaussian joint cumulants of distinct polynomial vertices are sums over connected graphs**: for `T` symmetric
positive definite with `T C = 1` and vertex polynomials `P_v(x) = Σ_{a ∈ A} c_{v,a} ∏_{i < k_{v,a}} ⟪u_{v,a,i}, x⟫`
(`v : Fin r`, `r > 0`), the joint cumulant `κ(P_1, …, P_r)` under the normalised Gaussian measure is the sum over the
configurations `g : Fin r → A` of `∏_v c_{v, g v}` times the sum over the perfect matchings of all legs that connect the
`r` vertices of `∏_{l < σ l} ⟪w_l, C w_{σ l}⟫`. -/
theorem jointCumulant_gaussProb_eq_connected [Fintype A] [DecidableEq A] {T C : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (hTC : ∀ w, T (C w) = w) [IsProbabilityMeasure (gaussProb T)]
    (c : Fin r → A → ℝ) (k : Fin r → A → ℕ) (u : ∀ v a, Fin (k v a) → E) (hr : 0 < r) :
    jointCumulant (fun R => ∫ x, ∏ v ∈ R, ∑ a, monomial (c v) (k v) (u v) a x ∂gaussProb T) Finset.univ =
      ∑ g : Fin r → A, (∏ v, c v (g v)) *
        ∑ τ ∈ (matchings (legsOf (legVertexV k g) Finset.univ)).filter
            (fun τ => IsConnectedOn (legVertexV k g) τ Finset.univ),
          matchingWeight C (legVectorV k u g) (legsOf (legVertexV k g) Finset.univ) τ := by
  rw [jointCumulant_moments_sum_eq (gaussProb T) (fun v a x => monomial (c v) (k v) (u v) a x)
    (integrable_prod_sum_monomialV hT hpos c k u)]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hfun : (fun R => ∫ x, ∏ v ∈ R, monomial (c v) (k v) (u v) (g v) x ∂gaussProb T) =
      fun R => (∏ v ∈ R, c v (g v)) * (gaussMoment T (legsOf (legVertexV k g) R) (legVectorV k u g) /
        gaussMoment T (∅ : Finset (Fin (∑ v, k v (g v)))) (legVectorV k u g)) :=
    funext fun R => integral_prod_monomialV hT hpos c k u g R
  have hZ := (gaussMoment_empty_pos hT hpos (legVectorV k u g)).ne'
  have hM0 : (fun R : Finset (Fin r) => gaussMoment T (legsOf (legVertexV k g) R) (legVectorV k u g) /
      gaussMoment T (∅ : Finset (Fin (∑ v, k v (g v)))) (legVectorV k u g)) ∅ = 1 := by
    have hl : legsOf (legVertexV k g) (∅ : Finset (Fin r)) = ∅ := by
      ext l
      simp [legsOf]
    simp only [hl]
    exact div_self hZ
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [hfun, jointCumulant_mul_prod _ hM0 (fun v => c v (g v)) Finset.univ Finset.univ_nonempty,
    jointCumulant_gaussMoment_eq_connected hT hpos hTC (legVertexV k g) (legVectorV k u g) Finset.univ
      Finset.univ_nonempty]

end DistinctVertices

section Blocks

variable {n : ℕ}

/-- The block of `π` whose smallest slot is `w` (`∅` if there is none). -/
noncomputable def blockOf (d : Fin n) (π : Finset (Finset (Fin n))) (w : Fin n) : Finset (Fin n) :=
  if h : ∃ B ∈ π, bmin d B = w then h.choose else ∅

lemma blockOf_spec (d : Fin n) {π : Finset (Finset (Fin n))} {w : Fin n} (hw : w ∈ π.image (bmin d)) :
    blockOf d π w ∈ π ∧ bmin d (blockOf d π w) = w := by
  have h : ∃ B ∈ π, bmin d B = w := by simpa using hw
  unfold blockOf
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- The number of blocks of a partition equals the number of their smallest slots. -/
lemma card_image_bmin {S : Finset (Fin n)} {π : Finset (Finset (Fin n))} (hπ : IsPartOf S π) (d : Fin n) :
    (π.image (bmin d)).card = π.card :=
  Finset.card_image_of_injOn (bmin_injOn hπ d)

/-- The enumeration of the blocks of a partition in the order of their smallest slots. -/
noncomputable def blockEnum (d : Fin n) {S : Finset (Fin n)} {π : Finset (Finset (Fin n))} (hπ : IsPartOf S π)
    (v : Fin π.card) : Finset (Fin n) :=
  blockOf d π ((π.image (bmin d)).orderEmbOfFin (card_image_bmin hπ d) v)

lemma blockEnum_mem (d : Fin n) {S : Finset (Fin n)} {π : Finset (Finset (Fin n))} (hπ : IsPartOf S π)
    (v : Fin π.card) : blockEnum d hπ v ∈ π ∧
      bmin d (blockEnum d hπ v) = (π.image (bmin d)).orderEmbOfFin (card_image_bmin hπ d) v :=
  blockOf_spec d (Finset.orderEmbOfFin_mem _ _ v)

/-- Products over the blocks of `π` whose smallest slots lie in `f(R)` are products over `R` of the enumerated blocks. -/
lemma prod_filter_bmin_map (d : Fin n) {S : Finset (Fin n)} {π : Finset (Finset (Fin n))} (hπ : IsPartOf S π)
    (P : Finset (Fin n) → ℝ) (R : Finset (Fin π.card)) :
    ∏ B ∈ π.filter (fun B => bmin d B ∈ R.map ((π.image (bmin d)).orderEmbOfFin (card_image_bmin hπ d)).toEmbedding),
      P B = ∏ v ∈ R, P (blockEnum d hπ v) := by
  set f := (π.image (bmin d)).orderEmbOfFin (card_image_bmin hπ d)
  have himg : π.filter (fun B => bmin d B ∈ R.map f.toEmbedding) = R.image (blockEnum d hπ) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_image, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hB, v, hv, hfv⟩
      refine ⟨v, hv, ?_⟩
      have h := blockEnum_mem d hπ v
      exact bmin_injOn hπ d h.1 hB (h.2.trans hfv)
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(blockEnum_mem d hπ v).1, v, hv, (blockEnum_mem d hπ v).2.symm⟩
  rw [himg, Finset.prod_image]
  intro v _ w _ hvw
  have h1 := (blockEnum_mem d hπ v).2
  have h2 := (blockEnum_mem d hπ w).2
  exact f.injective (h1.symm.trans ((congrArg (bmin d) hvw).trans h2))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {A : Type*}

/-- **Block cumulants of Gaussian polynomial blocks are sums over connected graphs**: for a partition `π` of a nonempty
slot set and block polynomials `P_B = Σ_{a ∈ A} c_{B,a} ∏_{i < k_{B,a}} ⟪u_{B,a,i}, x⟫`, the joint cumulant of the blocks
under the normalised Gaussian measure (`T` symmetric positive definite, `T C = 1`) is the sum over the monomial choices
`g` for the blocks (enumerated by smallest slot, `blockEnum`) of `∏ c` times the sum over the perfect matchings of all
legs connecting the blocks. -/
theorem blockCumulant_gaussProb_eq_connected [Fintype A] [DecidableEq A] {T C : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (hTC : ∀ w, T (C w) = w) [IsProbabilityMeasure (gaussProb T)]
    (c : Finset (Fin n) → A → ℝ) (k : Finset (Fin n) → A → ℕ) (u : ∀ B a, Fin (k B a) → E) (d : Fin n)
    {S : Finset (Fin n)} (hS : S.Nonempty) {π : Finset (Finset (Fin n))} (hπ : π ∈ partsOf S) :
    blockCumulant (fun π' => ∫ x, ∏ B ∈ π', ∑ a, monomial (c B) (k B) (u B) a x ∂gaussProb T) d π =
      ∑ g : Fin π.card → A, (∏ v, c (blockEnum d (mem_partsOf.mp hπ) v) (g v)) *
        ∑ τ ∈ (matchings (legsOf (legVertexV (fun v => k (blockEnum d (mem_partsOf.mp hπ) v)) g)
            Finset.univ)).filter
            (fun τ => IsConnectedOn (legVertexV (fun v => k (blockEnum d (mem_partsOf.mp hπ) v)) g) τ Finset.univ),
          matchingWeight C (legVectorV (fun v => k (blockEnum d (mem_partsOf.mp hπ) v))
            (fun v => u (blockEnum d (mem_partsOf.mp hπ) v)) g)
            (legsOf (legVertexV (fun v => k (blockEnum d (mem_partsOf.mp hπ) v)) g) Finset.univ) τ := by
  have hπ' := mem_partsOf.mp hπ
  set f := (π.image (bmin d)).orderEmbOfFin (card_image_bmin hπ' d)
  have hπne : π.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    rw [← hπ'.2.2] at hx
    obtain ⟨B, hB, -⟩ := Finset.mem_biUnion.mp hx
    exact ⟨B, hB⟩
  have hr : 0 < π.card := Finset.card_pos.mpr hπne
  unfold blockCumulant
  have hV : π.image (bmin d) = (Finset.univ : Finset (Fin π.card)).map f.toEmbedding :=
    (Finset.map_orderEmbOfFin_univ _ _).symm
  have hN0 : blockMoment (fun π' => ∫ x, ∏ B ∈ π', ∑ a, monomial (c B) (k B) (u B) a x ∂gaussProb T) d π ∅ = 1 := by
    simp [blockMoment]
  have : Nonempty (Fin π.card) := ⟨⟨0, hr⟩⟩
  rw [hV, jointCumulant_map f _ hN0 Finset.univ Finset.univ_nonempty]
  have hfun : (fun R : Finset (Fin π.card) =>
      blockMoment (fun π' => ∫ x, ∏ B ∈ π', ∑ a, monomial (c B) (k B) (u B) a x ∂gaussProb T) d π
        (R.map f.toEmbedding)) =
      fun R => ∫ x, ∏ v ∈ R, ∑ a, monomial (c (blockEnum d hπ' v)) (k (blockEnum d hπ' v))
        (u (blockEnum d hπ' v)) a x ∂gaussProb T := by
    funext R
    unfold blockMoment
    simp only
    congr 1
    funext x
    exact prod_filter_bmin_map d hπ' (fun B => ∑ a, monomial (c B) (k B) (u B) a x) R
  rw [hfun]
  exact jointCumulant_gaussProb_eq_connected hT hpos hTC (fun v => c (blockEnum d hπ' v))
    (fun v => k (blockEnum d hπ' v)) (fun v => u (blockEnum d hπ' v)) hr

end Blocks

end GaussianBlockSpin
