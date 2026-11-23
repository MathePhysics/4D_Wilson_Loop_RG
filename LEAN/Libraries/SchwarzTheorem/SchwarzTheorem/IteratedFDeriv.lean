module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symmetry of higher iterated derivatives

We prove the higher-order Schwarz theorem: the `k`-th iterated derivative of a function which is
`C^k` at a point is a symmetric multilinear map there. Over a field other than `ℝ` or `ℂ`, we
require analyticity instead, as in Mathlib's order-two statement `ContDiffAt.isSymmSndFDerivAt`.
Formally, the smoothness assumption is `minSmoothness 𝕜 k ≤ n` for a function that is `C^n`,
where `minSmoothness 𝕜 k` is `k` over `ℝ` or `ℂ` and `ω` otherwise.

## Main results

* `ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le`: if `f` is `C^n` at `x` with
  `minSmoothness 𝕜 k ≤ n`, then `iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v`
  for every `v : Fin k → E` and every permutation `σ` of `Fin k`.
* `ContDiffAt.domDomCongr_iteratedFDeriv_of_minSmoothness_le`: the same statement, as an
  equality of continuous multilinear maps.
* `ContDiff.iteratedFDeriv_comp_perm_of_minSmoothness_le` and
  `ContDiff.domDomCongr_iteratedFDeriv_of_minSmoothness_le`: global versions.
* `ContDiffWithinAt.iteratedFDerivWithin_comp_perm_of_minSmoothness_le` and
  `ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_of_minSmoothness_le`: versions within a set
  `s` with unique derivatives, at a point `x ∈ s` which is accumulated by interior points of `s`,
  under the same assumptions as `ContDiffWithinAt.isSymmSndFDerivWithinAt`.
* `ContDiffAt.iteratedFDeriv_comp_perm_of_omega`: the analytic case, which recovers Mathlib's
  `ContDiffAt.iteratedFDeriv_comp_perm`.

## Implementation notes

Mathlib proves the symmetry of `iteratedFDeriv 𝕜 k f x` for analytic `f` only
(`ContDiffAt.iteratedFDeriv_comp_perm`), through power series. Here we argue by induction on `k`,
using only the order-two statement `ContDiffAt.isSymmSndFDerivAt`.

Write `D^k f` for `iteratedFDeriv 𝕜 k f`, so that `D^(k+1) f x v = fderiv 𝕜 (D^k f) x (v 0) w`
where `w` is the tail of `v`. The set of permutations `σ` of `Fin (k + 1)` such that
`D^(k+1) f x (v ∘ σ) = D^(k+1) f x v` for all `v` is a submonoid, so by
`Equiv.Perm.mclosure_swap_castSucc_succ` it suffices to consider the transpositions of adjacent
indices `i` and `i + 1`.

* If `i ≠ 0`, the transposition fixes `0` and acts on the tail. Since `f` is `C^(k+1)` on a
  neighbourhood of `x`, the induction hypothesis shows that `D^k f` takes values in symmetric
  multilinear maps near `x`, hence so does its derivative (`fderiv_domDomCongr_apply`).
* If `i = 0`, we write `D^(m+2) f x v` as `fderiv 𝕜 (fderiv 𝕜 (D^m f)) x (v 0) (v 1) w'`
  (`iteratedFDeriv_add_two_apply_left`) and use the symmetry of the second derivative of the
  `C^2` function `D^m f`.

The version within a set is deduced from the version at a point, as in
`ContDiffWithinAt.isSymmSndFDerivWithinAt`: the iterated derivative within `s` is symmetric at
interior points of `s`, and it depends continuously on the point.
-/

public section

open Equiv Filter Fin Set
open scoped Topology ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {ι ι' : Type*} [Fintype ι] [Fintype ι']
  {f : E → F} {s : Set E} {x : E} {n : ℕ∞ω} {k : ℕ}

/-- Reindexing the arguments commutes with the derivative of a function with values in continuous
multilinear maps. -/
theorem fderiv_domDomCongr_apply (g : E → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ G) F)
    (σ : ι ≃ ι') (x h : E) :
    fderiv 𝕜 (fun y ↦ (g y).domDomCongr σ) x h = -- totalisation-audit: allow isometric reindexing
      (fderiv 𝕜 g x h).domDomCongr σ := -- totalisation-audit: allow isometric reindexing
  DFunLike.congr_fun
    ((ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 G F σ).comp_fderiv (f := g) (x := x)) h

/-- The `(m + 2)`-th iterated derivative of `f` is the second derivative of the `m`-th iterated
derivative, applied to the first two vectors and then to the remaining ones. -/
theorem iteratedFDeriv_add_two_apply_left (m : ℕ) (v : Fin (m + 2) → E) :
    iteratedFDeriv 𝕜 (m + 2) f x v =
      fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 m f)) x -- totalisation-audit: allow true by definition
        (v 0) (v 1) (tail (tail v)) := by
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left,
    LinearIsometryEquiv.comp_fderiv (𝕜 := 𝕜) (E := E →L[𝕜] E [×m]→L[𝕜] F)
      (F := E [×m + 1]→L[𝕜] F) (G := E)]
  rfl

/-- Auxiliary statement for `ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le`, assuming
that the smoothness exponent is not `∞`, so that smoothness at a point propagates to a
neighbourhood of the point. -/
private theorem iteratedFDeriv_comp_perm_aux (hn : n ≠ ∞) :
    ∀ (k : ℕ) (x : E), ContDiffAt 𝕜 n f x → minSmoothness 𝕜 k ≤ n →
      ∀ (v : Fin k → E) (σ : Perm (Fin k)),
        iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v
  | 0, x, _, _, v, σ => by rw [Subsingleton.elim (v ∘ σ) v]
  | k + 1, x, hf, hk, v, σ => by
    have hk' : minSmoothness 𝕜 k ≤ n :=
      (minSmoothness_monotone (by exact_mod_cast k.le_succ)).trans hk
    -- Near `x`, the `k`-th derivative is symmetric by induction, hence so is its derivative.
    have htail (h : E) (w : Fin k → E) (τ : Perm (Fin k)) :
        iteratedFDeriv 𝕜 (k + 1) f x (cons h (w ∘ τ)) =
          iteratedFDeriv 𝕜 (k + 1) f x (cons h w) := by
      have hsymm : (fun y ↦ (iteratedFDeriv 𝕜 k f y).domDomCongr τ) =ᶠ[𝓝 x]
          iteratedFDeriv 𝕜 k f := by
        filter_upwards [hf.eventually hn] with y hy
        ext w'
        exact iteratedFDeriv_comp_perm_aux hn k y hy hk' w' τ
      have := DFunLike.congr_fun (DFunLike.congr_fun (hsymm.fderiv_eq (𝕜 := 𝕜)) h) w
      rw [fderiv_domDomCongr_apply] at this
      simp only [iteratedFDeriv_succ_apply_left, cons_zero, tail_cons]
      exact this
    -- The permutations leaving the `(k + 1)`-th derivative invariant form a submonoid.
    let S : Submonoid (Perm (Fin (k + 1))) :=
      { carrier := {σ | ∀ v, iteratedFDeriv 𝕜 (k + 1) f x (v ∘ σ) =
          iteratedFDeriv 𝕜 (k + 1) f x v}
        one_mem' := fun _ ↦ rfl
        mul_mem' := fun {σ τ} hσ hτ v ↦ by
          rw [Perm.coe_mul, ← Function.comp_assoc, hτ, hσ] }
    suffices hS : S = ⊤ from (hS ▸ Submonoid.mem_top σ : σ ∈ S) v
    -- It contains the transpositions of adjacent indices, which generate all permutations.
    rw [eq_top_iff, ← Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩ v
    cases k with
    | zero => exact i.elim0
    | succ m =>
      cases i using Fin.cases with
      | zero =>
        -- The transposition of the first two indices: symmetry of the second derivative.
        have h2 : minSmoothness 𝕜 2 + m ≤ n := by
          rw [← minSmoothness_add]
          convert hk using 2
          push_cast
          ring
        have hsymm : IsSymmSndFDerivAt 𝕜 (iteratedFDeriv 𝕜 m f) x :=
          (hf.iteratedFDeriv_right h2).isSymmSndFDerivAt le_rfl
        rw [iteratedFDeriv_add_two_apply_left, iteratedFDeriv_add_two_apply_left, hsymm.eq]
        rfl
      | succ j =>
        -- A transposition fixing `0` acts on the tail.
        have hv : v ∘ swap j.succ.castSucc j.succ.succ =
            cons (v 0) (tail v ∘ swap j.castSucc j.succ) := by
          ext i
          induction i using Fin.cases with
          | zero => simp [swap_apply_of_ne_of_ne (succ_ne_zero _).symm (succ_ne_zero _).symm]
          | succ i => simp [tail, (succ_injective _).swap_apply]
        rw [hv, htail, cons_self_tail]

/-- **Higher-order Schwarz theorem**: if a function is `C^k` at a point, then its `k`-th iterated
derivative there is symmetric. Over a field different from `ℝ` or `ℂ`, we require that the
function is analytic. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le (hf : ContDiffAt 𝕜 n f x)
    (hk : minSmoothness 𝕜 k ≤ n) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v := by
  obtain ⟨m, hkm, hmn, hm⟩ := exist_minSmoothness_le_ne_infty hk
  exact iteratedFDeriv_comp_perm_aux hm k x (hf.of_le hmn) hkm v σ

/-- **Higher-order Schwarz theorem**: if a function is `C^k` at a point, then its `k`-th iterated
derivative there is invariant under any permutation of its arguments. Over a field different from
`ℝ` or `ℂ`, we require that the function is analytic. -/
theorem ContDiffAt.domDomCongr_iteratedFDeriv_of_minSmoothness_le (hf : ContDiffAt 𝕜 n f x)
    (hk : minSmoothness 𝕜 k ≤ n) (σ : Perm (Fin k)) :
    (iteratedFDeriv 𝕜 k f x).domDomCongr σ = iteratedFDeriv 𝕜 k f x := by
  ext v
  exact hf.iteratedFDeriv_comp_perm_of_minSmoothness_le hk v σ

/-- **Higher-order Schwarz theorem**: the `k`-th iterated derivative of a `C^k` function is
symmetric. Over a field different from `ℝ` or `ℂ`, we require that the function is analytic. -/
theorem ContDiff.iteratedFDeriv_comp_perm_of_minSmoothness_le (hf : ContDiff 𝕜 n f)
    (hk : minSmoothness 𝕜 k ≤ n) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v :=
  hf.contDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le hk v σ

/-- **Higher-order Schwarz theorem**: the `k`-th iterated derivative of a `C^k` function is
invariant under any permutation of its arguments. Over a field different from `ℝ` or `ℂ`, we
require that the function is analytic. -/
theorem ContDiff.domDomCongr_iteratedFDeriv_of_minSmoothness_le (hf : ContDiff 𝕜 n f)
    (hk : minSmoothness 𝕜 k ≤ n) (σ : Perm (Fin k)) :
    (iteratedFDeriv 𝕜 k f x).domDomCongr σ = iteratedFDeriv 𝕜 k f x :=
  hf.contDiffAt.domDomCongr_iteratedFDeriv_of_minSmoothness_le hk σ

/-- **Higher-order Schwarz theorem** within a set: if a function is `C^k` within a set `s` with
unique derivatives at a point `x ∈ s` which is accumulated by interior points of `s`, then its
`k`-th iterated derivative within `s` at `x` is invariant under any permutation of its arguments.
Over a field different from `ℝ` or `ℂ`, we require that the function is analytic. -/
theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_of_minSmoothness_le
    (hf : ContDiffWithinAt 𝕜 n f s x) (hk : minSmoothness 𝕜 k ≤ n) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ closure (interior s)) (h'x : x ∈ s) (σ : Perm (Fin k)) :
    (iteratedFDerivWithin 𝕜 k f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 k f s x := by
  /- We argue that, at interior points, the iterated derivative is symmetric, and moreover by
  continuity it converges to the iterated derivative at `x`. Therefore, the latter is also
  symmetric. -/
  obtain ⟨m, hkm, hmn, hm⟩ := exist_minSmoothness_le_ne_infty hk
  obtain ⟨u, u_open, xu, hu⟩ := (hf.of_le hmn).contDiffOn' le_rfl (by simp [hm])
  rw [insert_eq_of_mem h'x] at hu
  rw [← iteratedFDerivWithin_inter_open u_open xu]
  -- The set of symmetric multilinear maps is closed.
  have hclosed : IsClosed {A : E [×k]→L[𝕜] F | A.domDomCongr σ = A} :=
    isClosed_eq (ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E F σ).continuous continuous_id
  have hcont : ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f (s ∩ u)) (interior s ∩ u) x :=
    ((hu.continuousOn_iteratedFDerivWithin (le_minSmoothness.trans hkm) (hs.inter u_open))
      x ⟨h'x, xu⟩).mono (inter_subset_inter_left _ interior_subset)
  -- At interior points, the iterated derivative within `s ∩ u` is symmetric.
  have hmaps : MapsTo (iteratedFDerivWithin 𝕜 k f (s ∩ u)) (interior s ∩ u)
      {A | A.domDomCongr σ = A} := by
    intro y hy
    have hsu : s ∩ u ∈ 𝓝 y :=
      inter_mem (mem_interior_iff_mem_nhds.1 hy.1) (u_open.mem_nhds hy.2)
    have heq : iteratedFDerivWithin 𝕜 k f (s ∩ u) y = iteratedFDeriv 𝕜 k f y := by
      rw [← iteratedFDerivWithin_univ]
      exact iteratedFDerivWithin_congr_set (eventuallyEqSet_univ.2 hsu) k
    rw [heq]
    exact ((hu y (mem_of_mem_nhds hsu)).contDiffAt hsu)
      |>.domDomCongr_iteratedFDeriv_of_minSmoothness_le hkm σ
  exact hclosed.closure_subset (hcont.mem_closure (u_open.closure_inter ⟨hx, xu⟩) hmaps)

/-- **Higher-order Schwarz theorem** within a set: if a function is `C^k` within a set `s` with
unique derivatives at a point `x ∈ s` which is accumulated by interior points of `s`, then its
`k`-th iterated derivative within `s` at `x` is symmetric. Over a field different from `ℝ` or `ℂ`,
we require that the function is analytic. -/
theorem ContDiffWithinAt.iteratedFDerivWithin_comp_perm_of_minSmoothness_le
    (hf : ContDiffWithinAt 𝕜 n f s x) (hk : minSmoothness 𝕜 k ≤ n) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ closure (interior s)) (h'x : x ∈ s) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDerivWithin 𝕜 k f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 k f s x v :=
  congrArg (fun A ↦ A v)
    (hf.domDomCongr_iteratedFDerivWithin_of_minSmoothness_le hk hs hx h'x σ)

/-- The `k`-th iterated derivative of an analytic function is symmetric. This is Mathlib's
`ContDiffAt.iteratedFDeriv_comp_perm`, recovered as the special case `n = ω` of
`ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le`. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_omega (hf : ContDiffAt 𝕜 ω f x)
    (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v :=
  hf.iteratedFDeriv_comp_perm_of_minSmoothness_le le_top v σ
