# SchwarzTheorem

The higher-order Schwarz theorem in Lean 4 / Mathlib: the `k`-th iterated Fréchet derivative
of a function that is `C^k` at a point is a symmetric multilinear map there.

It is written to Mathlib's conventions, so that it can be upstreamed. It imports Mathlib only
(`Mathlib.Analysis.Calculus.FDeriv.Symmetric`), and it is pinned to Mathlib
`8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a` on `leanprover/lean4:v4.34.0-rc2`.

## The gap in Mathlib

* **Order two.** `ContDiffAt.isSymmSndFDerivAt` (`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`)
  proves that the second derivative is symmetric under the hypothesis `minSmoothness 𝕜 2 ≤ n`.
  Here `minSmoothness 𝕜 n` is `n` over `ℝ` or `ℂ`, and `ω` (analytic) over any other field.
* **Order `k`.** The only statement is `ContDiffAt.iteratedFDeriv_comp_perm`
  (`Mathlib/Analysis/Analytic/IteratedFDeriv.lean`). It assumes `ContDiffAt 𝕜 ω f x`, that is,
  analyticity, because it is proved through power series.

This library proves the order-`k` statement under the same hypothesis as the order-two one,
`minSmoothness 𝕜 k ≤ n`. Over `ℝ` and `ℂ`, this means that `C^k` is enough.

## Main statements

All of them are in `SchwarzTheorem/IteratedFDeriv.lean`. The ambient variables are
`{𝕜 : Type*} [NontriviallyNormedField 𝕜]`, normed spaces `E` and `F` over `𝕜`, `f : E → F`,
`s : Set E`, `x : E`, `n : ℕ∞ω` and `k : ℕ`. `Perm` is `Equiv.Perm`.

```lean
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le (hf : ContDiffAt 𝕜 n f x)
    (hk : minSmoothness 𝕜 k ≤ n) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v

theorem ContDiffAt.domDomCongr_iteratedFDeriv_of_minSmoothness_le (hf : ContDiffAt 𝕜 n f x)
    (hk : minSmoothness 𝕜 k ≤ n) (σ : Perm (Fin k)) :
    (iteratedFDeriv 𝕜 k f x).domDomCongr σ = iteratedFDeriv 𝕜 k f x

theorem ContDiff.iteratedFDeriv_comp_perm_of_minSmoothness_le (hf : ContDiff 𝕜 n f)
    (hk : minSmoothness 𝕜 k ≤ n) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v

theorem ContDiff.domDomCongr_iteratedFDeriv_of_minSmoothness_le (hf : ContDiff 𝕜 n f)
    (hk : minSmoothness 𝕜 k ≤ n) (σ : Perm (Fin k)) :
    (iteratedFDeriv 𝕜 k f x).domDomCongr σ = iteratedFDeriv 𝕜 k f x

theorem ContDiffWithinAt.iteratedFDerivWithin_comp_perm_of_minSmoothness_le
    (hf : ContDiffWithinAt 𝕜 n f s x) (hk : minSmoothness 𝕜 k ≤ n) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ closure (interior s)) (h'x : x ∈ s) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDerivWithin 𝕜 k f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 k f s x v

theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_of_minSmoothness_le
    (hf : ContDiffWithinAt 𝕜 n f s x) (hk : minSmoothness 𝕜 k ≤ n) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ closure (interior s)) (h'x : x ∈ s) (σ : Perm (Fin k)) :
    (iteratedFDerivWithin 𝕜 k f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 k f s x

theorem ContDiffAt.iteratedFDeriv_comp_perm_of_omega (hf : ContDiffAt 𝕜 ω f x)
    (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v
```

The `Within` versions take exactly the hypotheses on `s` and `x` of Mathlib's order-two lemma
`ContDiffWithinAt.isSymmSndFDerivWithinAt`: `UniqueDiffOn 𝕜 s`, `x ∈ closure (interior s)`
and `x ∈ s`.

There are also two helper lemmas, each of independent use:

```lean
theorem fderiv_domDomCongr_apply (g : E → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ G) F)
    (σ : ι ≃ ι') (x h : E) :
    fderiv 𝕜 (fun y ↦ (g y).domDomCongr σ) x h = (fderiv 𝕜 g x h).domDomCongr σ

theorem iteratedFDeriv_add_two_apply_left (m : ℕ) (v : Fin (m + 2) → E) :
    iteratedFDeriv 𝕜 (m + 2) f x v =
      fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 m f)) x (v 0) (v 1) (tail (tail v))
```

## Relation to Mathlib's analytic lemma

`ContDiffAt.iteratedFDeriv_comp_perm_of_omega` has exactly the statement of Mathlib's
`ContDiffAt.iteratedFDeriv_comp_perm`. It is proved as the special case `n = ω` of the main
theorem, since `minSmoothness 𝕜 k ≤ ω` always holds. A scratch test checks that the two
statements are the same proposition. So at a point, the new theorem strictly generalises the
analytic one: it needs only `C^k` over `ℝ` or `ℂ`, and it is the same result over other fields.

Within a set, it does not. Mathlib's analytic `ContDiffWithinAt.iteratedFDerivWithin_comp_perm`
does not assume `x ∈ closure (interior s)`, while the `Within` version here does, in line with
the order-two lemma.

**Naming for upstreaming.** Mathlib's order-two lemmas are `ContDiffAt.isSymmSndFDerivAt`
(the general statement) and `ContDiffAt.isSymmSndFDerivAt_of_omega` (the analytic one).
Following that precedent, a Mathlib PR would rename the analytic
`ContDiffAt.iteratedFDeriv_comp_perm` to `..._of_omega` and give the main theorem here the plain
name. The `_of_minSmoothness_le` suffix is used only because this library must not clash with
the names that Mathlib already has.

## Usage

```lean
import SchwarzTheorem

open Equiv in
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {x : E} {k : ℕ} (hf : ContDiffAt ℝ k f x)
    (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv ℝ k f x (v ∘ σ) = iteratedFDeriv ℝ k f x v :=
  hf.iteratedFDeriv_comp_perm_of_minSmoothness_le (by simp) v σ
```

Over `ℝ` or `ℂ`, or any `[IsRCLikeNormedField 𝕜]`, the side condition `minSmoothness 𝕜 k ≤ n`
reduces to `k ≤ n` by the simp lemma `minSmoothness_of_isRCLikeNormedField`. So it is
discharged by `by simp` when `n = k`, and by `by simpa using hk` from `hk : (k : ℕ∞ω) ≤ n`.
Over a general field, pass `le_top`, or use `..._of_omega`, for analytic functions.

The library has no Mathlib of its own. It is built inside a workspace that requires both Mathlib
at the pinned revision and this package.

## Proof

The proof is by induction on `k`, and uses only the order-two theorem. Write `D^k f` for
`iteratedFDeriv 𝕜 k f`.

1. A reduction to `n ≠ ∞`, through Mathlib's `exist_minSmoothness_le_ne_infty`. This makes
   `C^n` at `x` propagate to a neighbourhood of `x` (`ContDiffAt.eventually`).
2. The permutations `σ` with `D^(k+1) f x (v ∘ σ) = D^(k+1) f x v` for all `v` form a
   submonoid of `Perm (Fin (k + 1))`. By `Equiv.Perm.mclosure_swap_castSucc_succ`, adjacent
   transpositions generate the whole group, so it is enough to treat `swap i (i + 1)`.
3. **The case `i ≠ 0`.** The transposition fixes `0` and acts on the tail. By the induction
   hypothesis at points near `x`, `D^k f` agrees near `x` with `y ↦ (D^k f y).domDomCongr τ`.
   So their derivatives agree at `x`, and `fderiv_domDomCongr_apply` moves the reindexing
   outside the derivative. Since `D^(k+1) f x (cons h w) = fderiv 𝕜 (D^k f) x h w` holds by
   definition, the result follows.
4. **The case `i = 0`, with `k + 1 = m + 2`.** By `iteratedFDeriv_add_two_apply_left`,
   `D^(m+2) f x v = fderiv 𝕜 (fderiv 𝕜 (D^m f)) x (v 0) (v 1) (tail (tail v))`. The function
   `D^m f` is `C^(minSmoothness 𝕜 2)` at `x` (`ContDiffAt.iteratedFDeriv_right` and
   `minSmoothness_add`), so `ContDiffAt.isSymmSndFDerivAt` swaps `v 0` and `v 1`.
5. **Within a set**, the proof follows `ContDiffWithinAt.isSymmSndFDerivWithinAt`. At points
   of `interior s ∩ u`, the derivative within `s ∩ u` equals `D^k f` and is symmetric by the
   theorem at a point. Here `u` is an open neighbourhood on which `f` is `C^m` within `s`. The
   symmetric maps form a closed set, and `iteratedFDerivWithin 𝕜 k f (s ∩ u)` is continuous on
   `s ∩ u`. Since `x ∈ closure (interior s ∩ u)`, the result follows by
   `ContinuousWithinAt.mem_closure`.
