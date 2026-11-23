import GaussianBlockSpin.ConnectedMatchings

/-! Joint cumulants (truncated expectations) of a family indexed by vertices `Fin n`, from a moment function `M` on
vertex sets (`M ∅ = 1`) by the first-vertex recursion `M(S) = Σ_{B ⊆ S, min S ∈ B} κ(B) M(S \ B)`. If the moments are
the matching sums `M(S) = Σ_{σ matching of the legs of S} wt(σ)` (any `C`), the joint cumulant of `S` is the sum over
the matchings connected on `S` (jointCumulant_eq_connected, purely combinatorial); for the normalised Gaussian moments
of products of linear forms (`T` symmetric positive definite, `T C = 1`) this is jointCumulant_gaussMoment_eq_connected:
"cumulants are sums over connected graphs". -/

open MeasureTheory
open scoped RealInnerProductSpace

namespace GaussianBlockSpin

variable {n : ℕ}

lemma card_lt_of_mem_proper {S B : Finset (Fin n)} (hB : B ∈ S.powerset.filter (fun B => B ≠ S)) :
    B.card < S.card := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hB
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp h1, h2⟩)

/-- The joint cumulant: `κ(∅) = 0` and, for `S ≠ ∅` with `v₀ = min S`,
`κ(S) = M(S) - Σ_{B ⊊ S, v₀ ∈ B} κ(B) M(S \ B)`. -/
def jointCumulant (M : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  if h : S.Nonempty then
    M S - ∑ B ∈ ((S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B)).attach,
      jointCumulant M B * M (S \ B)
  else 0
termination_by S.card
decreasing_by exact card_lt_of_mem_proper (Finset.mem_filter.mp B.2).1

lemma jointCumulant_of_nonempty (M : Finset (Fin n) → ℝ) {S : Finset (Fin n)} (h : S.Nonempty) :
    jointCumulant M S = M S - ∑ B ∈ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B),
      jointCumulant M B * M (S \ B) := by
  rw [jointCumulant]
  simp only [h, ↓reduceDIte]
  rw [Finset.sum_attach _ (fun B => jointCumulant M B * M (S \ B))]

/-- **The moment-cumulant relation**: for `M ∅ = 1` and `S ≠ ∅`, `M(S) = Σ_{B ⊆ S, min S ∈ B} κ(B) M(S \ B)`. -/
theorem moment_eq_sum_jointCumulant (M : Finset (Fin n) → ℝ) (hM : M ∅ = 1) {S : Finset (Fin n)} (h : S.Nonempty) :
    M S = ∑ B ∈ S.powerset.filter (fun B => S.min' h ∈ B), jointCumulant M B * M (S \ B) := by
  have hsplit : S.powerset.filter (fun B => S.min' h ∈ B) =
      insert S ((S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B)) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_powerset]
    constructor
    · rintro ⟨hB, hv⟩
      by_cases hBS : B = S
      · exact Or.inl hBS
      · exact Or.inr ⟨⟨hB, hBS⟩, hv⟩
    · rintro (hBS | ⟨⟨hB, -⟩, hv⟩)
      · rw [hBS]; exact ⟨subset_refl _, S.min'_mem h⟩
      · exact ⟨hB, hv⟩
  have hnot : S ∉ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B) := by
    simp
  rw [hsplit, Finset.sum_insert hnot, Finset.sdiff_self, hM, mul_one, jointCumulant_of_nonempty M h]
  ring

/-- **Uniqueness**: a function `K` satisfying the first-vertex relation `M(S) = Σ_{B ⊆ S, min S ∈ B} K(B) M(S \ B)` for
every nonempty `S` (with `M ∅ = 1`) is the joint cumulant on nonempty sets. -/
theorem eq_jointCumulant_of_decomp (M K : Finset (Fin n) → ℝ) (hM : M ∅ = 1)
    (hK : ∀ S : Finset (Fin n), ∀ h : S.Nonempty,
      M S = ∑ B ∈ S.powerset.filter (fun B => S.min' h ∈ B), K B * M (S \ B))
    (S : Finset (Fin n)) (h : S.Nonempty) : K S = jointCumulant M S := by
  induction hc : S.card using Nat.strong_induction_on generalizing S with
  | _ c ih =>
    have e1 := hK S h
    have e2 := moment_eq_sum_jointCumulant M hM h
    have hsplit : S.powerset.filter (fun B => S.min' h ∈ B) =
        insert S ((S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B)) := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_powerset]
      constructor
      · rintro ⟨hB, hv⟩
        by_cases hBS : B = S
        · exact Or.inl hBS
        · exact Or.inr ⟨⟨hB, hBS⟩, hv⟩
      · rintro (hBS | ⟨⟨hB, -⟩, hv⟩)
        · rw [hBS]; exact ⟨subset_refl _, S.min'_mem h⟩
        · exact ⟨hB, hv⟩
    have hnot : S ∉ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B) := by
      simp
    rw [hsplit, Finset.sum_insert hnot, Finset.sdiff_self, hM, mul_one] at e1 e2
    have hrest : ∑ B ∈ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B), K B * M (S \ B) =
        ∑ B ∈ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B), jointCumulant M B * M (S \ B) := by
      refine Finset.sum_congr rfl fun B hB => ?_
      have hBne : B.Nonempty := ⟨S.min' h, (Finset.mem_filter.mp hB).2⟩
      rw [ih B.card (hc ▸ card_lt_of_mem_proper (Finset.mem_filter.mp hB).1) B hBne rfl]
    linarith

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cumulants of matching sums are connected-matching sums** (purely combinatorial, any linear map `C`): if the
moment function is the matching sum `M(S) = Σ_{σ matching of the legs of S} ∏_{i < σ i} ⟪w_i, C w_{σ i}⟫`, the joint
cumulant of a nonempty `S` is the sum over the matchings of the legs of `S` that are connected on `S`. (For general `C`
this `M` need not be a moment of any measure; the Gaussian case is jointCumulant_gaussMoment_eq_connected.) -/
theorem jointCumulant_eq_connected (vert : Fin m → Fin n) (C : E →ₗ[ℝ] E) (w : Fin m → E)
    (S : Finset (Fin n)) (h : S.Nonempty) :
    jointCumulant (fun S => ∑ σ ∈ matchings (legsOf vert S), matchingWeight C w (legsOf vert S) σ) S =
      ∑ τ ∈ (matchings (legsOf vert S)).filter (fun τ => IsConnectedOn vert τ S),
        matchingWeight C w (legsOf vert S) τ := by
  have hM : (fun S : Finset (Fin n) => ∑ σ ∈ matchings (legsOf vert S), matchingWeight C w (legsOf vert S) σ) ∅ = 1 := by
    have hl : legsOf vert (∅ : Finset (Fin n)) = ∅ := by
      ext i
      simp [legsOf]
    simp only [hl, matchings_empty, Finset.sum_singleton]
    simp [matchingWeight]
  refine (eq_jointCumulant_of_decomp
    (fun S => ∑ σ ∈ matchings (legsOf vert S), matchingWeight C w (legsOf vert S) σ)
    (fun S => ∑ τ ∈ (matchings (legsOf vert S)).filter (fun τ => IsConnectedOn vert τ S),
      matchingWeight C w (legsOf vert S) τ) hM (fun S h => ?_) S h).symm
  exact sum_matchings_legsOf_eq C w (S.min'_mem h)

/-- The Gaussian normaliser `∫ e^{-½⟪x, T x⟫} dx = M(∅)` is positive. -/
lemma gaussMoment_empty_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) {ι : Type*} (v : ι → E) :
    0 < gaussMoment T (∅ : Finset ι) v := by
  unfold gaussMoment linProd
  simp only [Finset.prod_empty, one_mul]
  unfold gaussWeight
  rw [integral_exp_neg_half_inner hT hpos]
  exact div_pos (by positivity) (Real.sqrt_pos.mpr (det_pos_of_pos hT hpos))

/-- **Gaussian cumulants of polynomial vertices are connected-graph sums**: for `T` symmetric positive definite,
`T C = 1`, legs `w` attached to vertices by `vert`, the joint cumulant of the normalised Gaussian moments
`⟨∏_{v ∈ S} P_v⟩ = ∫ ∏_{i ∈ legs S} ⟪w_i, x⟫ e^{-½⟪x, T x⟫} dx / ∫ e^{-½⟪x, T x⟫} dx` of a nonempty vertex set `S` is the sum over
the perfect matchings of the legs of `S` connected on `S` of `∏_{i < σ i} ⟪w_i, C w_{σ i}⟫`. -/
theorem jointCumulant_gaussMoment_eq_connected [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {T C : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (hTC : ∀ w, T (C w) = w)
    (vert : Fin m → Fin n) (w : Fin m → E) (S : Finset (Fin n)) (h : S.Nonempty) :
    jointCumulant (fun S => gaussMoment T (legsOf vert S) w / gaussMoment T (∅ : Finset (Fin m)) w) S =
      ∑ τ ∈ (matchings (legsOf vert S)).filter (fun τ => IsConnectedOn vert τ S),
        matchingWeight C w (legsOf vert S) τ := by
  have hZ := (gaussMoment_empty_pos hT hpos w).ne'
  have hfun : (fun S : Finset (Fin n) => gaussMoment T (legsOf vert S) w / gaussMoment T (∅ : Finset (Fin m)) w) =
      fun S => ∑ σ ∈ matchings (legsOf vert S), matchingWeight C w (legsOf vert S) σ := by
    funext S
    rw [gaussMoment_eq_sum_matchings hT hpos hTC w (legsOf vert S)]
    field_simp
  rw [hfun]
  exact jointCumulant_eq_connected vert C w S h

end GaussianBlockSpin
