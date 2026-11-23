import KatoRellich.Criterion
import KatoRellich.Neumann
import KatoRellich.Resolvent

/-!
# The Kato–Rellich theorem

**Reed–Simon II, Theorem X.12 (the Kato–Rellich theorem), p. 162.**  Suppose that `A` is
self-adjoint, `B` is symmetric, and `B` is `A`-bounded with relative bound `a < 1`.  Then `A + B`
is self-adjoint on `D(A)`.

Reed–Simon work on complex Hilbert spaces.  Their proof (p. 163) shows `Ran(A + B ± iμ) = H` for
large `μ` and applies the basic criterion.  Here it is formalised twice:

* `KatoRellich.isSelfAdjoint_add`: the theorem as stated, over any `RCLike 𝕜` with a nonzero
  imaginary unit, in particular over `ℂ` (`KatoRellich.isSelfAdjoint_add_complex`).  The proof is
  Reed–Simon's, with the shifts `±iμ`.
* `KatoRellich.isSelfAdjoint_add_of_isBoundedBelow`: the theorem for `A` bounded below, over any
  `RCLike 𝕜`, including real Hilbert spaces.  The proof uses a large real shift `t` in place of
  `±iμ`: for `A ≥ M`, `Ran(A + t) = H` once `M + t > 0`, and the estimate
  `‖B (A + t)⁻¹‖ < 1` is the one Reed–Simon use for the semiboundedness statement (p. 163).  On a
  real Hilbert space the imaginary shifts are not available, so some lower bound is needed for this
  route; the general real case would go through the complexification, which is not formalised.

In both, `A + B` is mathlib's sum of partial maps, whose domain is `D(A) ∩ D(B) = D(A)`.

## Main results

* `KatoRellich.range_addScalar_add_eq_top`: the perturbation step, `Ran(A + B + z) = H` if
  `Ran(A + z) = H` and `‖B x‖ ≤ q ‖(A + z) x‖` on `D(A)` with `q < 1`.
* `KatoRellich.range_addScalar_add_eq_top_of_isRelBounded`: the same, with `q` obtained from the
  relative bound.
* `KatoRellich.isSelfAdjoint_add_of_isBoundedBelow`: Kato–Rellich for semibounded `A`.
* `KatoRellich.isSelfAdjoint_add`, `KatoRellich.isSelfAdjoint_add_complex`: Kato–Rellich.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace KatoRellich

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [CompleteSpace E]

/-- **The perturbation step.**  If `Ran(A + z) = H`, `c ‖x‖ ≤ ‖(A + z) x‖` with `c > 0`, and
`‖B x‖ ≤ q ‖(A + z) x‖` on `D(A)` with `0 ≤ q < 1`, then `Ran(A + B + z) = H`
(Reed–Simon II, proof of Theorem X.12, p. 163). -/
theorem range_addScalar_add_eq_top {A B : E →ₗ.[𝕜] E} (hdom : A.domain ≤ B.domain) (z : 𝕜)
    (hran : LinearMap.range (addScalar A z).toFun = ⊤) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x + z • (x : E)‖) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < 1) (hB : ∀ x : A.domain, ‖B ⟨x, hdom x.2⟩‖ ≤ q * ‖A x + z • (x : E)‖) :
    LinearMap.range (addScalar (A + B) z).toFun = ⊤ := by
  let S : A.domain →ₗ[𝕜] E := (addScalar A z).toFun
  let B' : A.domain →ₗ[𝕜] E := B.toFun ∘ₗ Submodule.inclusion hdom
  have hS : Function.Bijective S := by
    refine ⟨(injective_iff_map_eq_zero S).mpr fun x hx => ?_, LinearMap.range_eq_top.mp hran⟩
    have h := hlow x
    change c * ‖(x : E)‖ ≤ ‖S x‖ at h
    rw [hx, norm_zero] at h
    have hx0 : ‖(x : E)‖ = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right h hc) (norm_nonneg _)
    exact Subtype.ext (norm_eq_zero.mp hx0)
  refine LinearMap.range_eq_top.mpr fun f => ?_
  obtain ⟨x, hx⟩ := exists_add_eq_of_norm_le S B' hS hq0 hq (fun x => hB x) f
  refine ⟨⟨x, x.2, hdom x.2⟩, ?_⟩
  rw [← hx]
  change A ⟨x, x.2⟩ + B ⟨x, hdom x.2⟩ + z • (x : E) = A x + z • (x : E) + B ⟨x, hdom x.2⟩
  abel

/-- **The perturbation step with a relative bound.**  Let `B` be `A`-bounded with constants
`a < 1` and `b`, and let `Ran(A + z) = H`, `c ‖x‖ ≤ ‖(A + z) x‖` and `‖A x‖ ≤ ‖(A + z) x‖` on
`D(A)`, where `|b| < (1 - max a 0) c`.  Then `‖B x‖ ≤ q ‖(A + z) x‖` with
`q = max a 0 + |b| / c < 1`, so `Ran(A + B + z) = H` (Reed–Simon II, proof of Theorem X.12,
p. 163, where `c = μ`). -/
theorem range_addScalar_add_eq_top_of_isRelBounded {A B : E →ₗ.[𝕜] E} {a b : ℝ}
    (hAB : IsRelBounded B A a b) (ha : a < 1) (z : 𝕜)
    (hran : LinearMap.range (addScalar A z).toFun = ⊤) {c : ℝ} (hc : |b| < (1 - max a 0) * c)
    (hlow : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x + z • (x : E)‖)
    (hAx : ∀ x : A.domain, ‖A x‖ ≤ ‖A x + z • (x : E)‖) :
    LinearMap.range (addScalar (A + B) z).toFun = ⊤ := by
  have ha' : max a 0 < 1 := max_lt ha one_pos
  have ha'0 : 0 ≤ max a 0 := le_max_right a 0
  have hc0 : 0 < c := by
    by_contra h
    have : (1 - max a 0) * c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp h)
    linarith [abs_nonneg b]
  set q : ℝ := max a 0 + |b| / c with hq_def -- totalisation-audit: allow `c > 0` by `hc0`
  have hqc : q * c = max a 0 * c + |b| := by
    rw [hq_def, add_mul, div_mul_cancel₀ _ hc0.ne']
  have hq0 : 0 ≤ q := by positivity
  have hq : q < 1 := by
    have : q * c < 1 * c := by
      rw [hqc]
      linarith
    exact lt_of_mul_lt_mul_right this hc0.le
  refine range_addScalar_add_eq_top hAB.domain_le z hran hc0 hlow hq0 hq fun x => ?_
  have h1 : a * ‖A x‖ ≤ max a 0 * ‖A x + z • (x : E)‖ :=
    (mul_le_mul_of_nonneg_right (le_max_left a 0) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hAx x) ha'0)
  have h2 : c * (b * ‖(x : E)‖) ≤ |b| * ‖A x + z • (x : E)‖ :=
    calc c * (b * ‖(x : E)‖) ≤ c * (|b| * ‖(x : E)‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _)) hc0.le
      _ = |b| * (c * ‖(x : E)‖) := by ring
      _ ≤ |b| * ‖A x + z • (x : E)‖ := mul_le_mul_of_nonneg_left (hlow x) (abs_nonneg b)
  have hmul : c * ‖B ⟨x, hAB.domain_le x.2⟩‖ ≤ c * (q * ‖A x + z • (x : E)‖) :=
    calc c * ‖B ⟨x, hAB.domain_le x.2⟩‖ ≤ c * (a * ‖A x‖ + b * ‖(x : E)‖) :=
          mul_le_mul_of_nonneg_left (hAB.bound x) hc0.le
      _ = c * (a * ‖A x‖) + c * (b * ‖(x : E)‖) := by ring
      _ ≤ c * (max a 0 * ‖A x + z • (x : E)‖) + |b| * ‖A x + z • (x : E)‖ :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hc0.le) h2
      _ = c * (q * ‖A x + z • (x : E)‖) := by
          rw [show c * (q * ‖A x + z • (x : E)‖) = (q * c) * ‖A x + z • (x : E)‖ by ring,
            hqc]
          ring
  exact le_of_mul_le_mul_left hmul hc0

/-- **The Kato–Rellich theorem for `A` bounded below** (Reed–Simon II, Theorem X.12, p. 162,
with the real shift of its semiboundedness argument, p. 163).  Let `A` be self-adjoint and
bounded below, and let `B` be symmetric and `A`-bounded with constants `a < 1` and `b`.  Then
`A + B` is self-adjoint on `D(A)`.  This holds over any `RCLike 𝕜`, including `ℝ`. -/
theorem isSelfAdjoint_add_of_isBoundedBelow {A B : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {M : ℝ}
    (hM : IsBoundedBelow A M) (hB : B.IsFormalAdjoint B) {a b : ℝ}
    (hAB : IsRelBounded B A a b) (ha : a < 1) :
    IsSelfAdjoint (A + B) ∧ (A + B).domain = A.domain := by
  refine ⟨?_, add_domain_of_le hAB.domain_le⟩
  have ha'0 : 0 ≤ max a 0 := le_max_right a 0
  have h1a : 0 < 1 - max a 0 := by linarith [max_lt ha one_pos]
  -- A large shift `s = M + t`, with `(1 - max a 0) s ≥ |b| + |M| + 1`.
  obtain ⟨n, hn⟩ := Archimedean.arch (|b| + |M| + 1) h1a
  rw [nsmul_eq_mul] at hn
  set s : ℝ := (n : ℝ) with hs_def
  have hs0 : 0 ≤ s := Nat.cast_nonneg n
  have hbs : |b| < (1 - max a 0) * s := by linarith [abs_nonneg M]
  have hMs : |M| < s := by nlinarith [abs_nonneg b, mul_nonneg ha'0 hs0]
  set t : ℝ := s - M with ht_def
  have hMt : M + t = s := by ring
  have ht0 : 0 ≤ t := by linarith [le_abs_self M]
  have h2Mt : 0 ≤ 2 * M + t := by linarith [neg_abs_le M]
  have hsx : ∀ x : A.domain, s * ‖(x : E)‖ ≤ ‖A x + (t : 𝕜) • (x : E)‖ := fun x => by
    have h := mul_norm_le_norm_add_ofReal hM t x
    rwa [hMt] at h
  have hran := range_addScalar_ofReal_eq_top hA hM (t := t) (by linarith [abs_nonneg M])
  have hran' := range_addScalar_add_eq_top_of_isRelBounded hAB ha (t : 𝕜) hran hbs hsx
    (norm_le_norm_add_ofReal hM ht0 h2Mt)
  exact isSelfAdjoint_of_range_addScalar_ofReal
    ((IsSymmetric.of_isSelfAdjoint hA).add hB hAB.domain_le) t hran'

/-- **The Kato–Rellich theorem** (Reed–Simon II, Theorem X.12, p. 162).  Suppose that `A` is
self-adjoint, `B` is symmetric, and `B` is `A`-bounded with constants `a < 1` and `b`.  Then
`A + B` is self-adjoint on `D(A)`.  Stated over any `RCLike 𝕜` whose imaginary unit is nonzero,
i.e. over `ℂ`; the proof is Reed–Simon's, through `Ran(A + B ± iμ) = H` for large `μ`. -/
theorem isSelfAdjoint_add (hI : (RCLike.I : 𝕜) ≠ 0) {A B : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hB : B.IsFormalAdjoint B) {a b : ℝ} (hAB : IsRelBounded B A a b) (ha : a < 1) :
    IsSelfAdjoint (A + B) ∧ (A + B).domain = A.domain := by
  refine ⟨?_, add_domain_of_le hAB.domain_le⟩
  have hsymm := IsSymmetric.of_isSelfAdjoint hA
  have h1a : 0 < 1 - max a 0 := by linarith [max_lt ha one_pos]
  -- A large `μ`, with `(1 - max a 0) μ ≥ |b| + 1`.
  obtain ⟨n, hn⟩ := Archimedean.arch (|b| + 1) h1a
  rw [nsmul_eq_mul] at hn
  set μ : ℝ := (n : ℝ) with hμ_def
  have hbμ : |b| < (1 - max a 0) * μ := by linarith
  have hμ : 0 < μ := by
    by_contra h
    have : (1 - max a 0) * μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1a.le (not_lt.mp h)
    linarith [abs_nonneg b]
  -- `Ran(A + B + iν) = H` for `|ν| = μ`.
  have key : ∀ ν : ℝ, |ν| = μ →
      LinearMap.range (addScalar (A + B) ((ν : 𝕜) * RCLike.I)).toFun = ⊤ := by
    intro ν hν
    have hν0 : ν ≠ 0 := by
      rintro rfl
      rw [abs_zero] at hν
      linarith
    have hbd := norm_le_norm_addScalar_I hsymm hI ν
    exact range_addScalar_add_eq_top_of_isRelBounded hAB ha _
      (range_addScalar_I_eq_top hA hI hν0) hbμ (fun x => hν ▸ (hbd x).1) (fun x => (hbd x).2)
  have hz := key μ (abs_of_pos hμ)
  have hconj : conj ((μ : 𝕜) * RCLike.I) = ((-μ : ℝ) : 𝕜) * RCLike.I := by
    rw [map_mul, RCLike.conj_ofReal, RCLike.conj_I, RCLike.ofReal_neg, mul_neg, neg_mul]
  have hz' : LinearMap.range (addScalar (A + B) (conj ((μ : 𝕜) * RCLike.I))).toFun = ⊤ := by
    rw [hconj]
    exact key (-μ) (by rw [abs_neg, abs_of_pos hμ])
  exact isSelfAdjoint_of_range_addScalar (hsymm.add hB hAB.domain_le) _ hz hz'

/-- **The Kato–Rellich theorem on a complex Hilbert space** (Reed–Simon II, Theorem X.12,
p. 162): if `A` is self-adjoint, `B` is symmetric, and `B` is `A`-bounded with relative bound
`a < 1`, then `A + B` is self-adjoint on `D(A)`. -/
theorem isSelfAdjoint_add_complex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : B.IsFormalAdjoint B)
    {a b : ℝ} (hAB : IsRelBounded B A a b) (ha : a < 1) :
    IsSelfAdjoint (A + B) ∧ (A + B).domain = A.domain :=
  isSelfAdjoint_add (by simp) hA hB hAB ha

end KatoRellich
