# Abelian Gaussian check of the first-step perimeter and corner structure

A small numerical companion to the first RG step of
[`WILSON_FIRST_RG_STEP_V5.tex`](../../Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.tex).
It computes, for the **abelian U(1) Gaussian analogue** with the same blocking and averaging, the fluctuation factor that
the first step extracts from a square Wilson loop, and checks that it has the perimeter-plus-corner form
`κ_C = e^{-δm P(C)} z_c⁴` with coefficients that scale as the programme states: `δm ∼ g²/ε`, `log z_c ∼ g²`.

**This is a sanity check of structure and order of magnitude, not a test of any bound or proof in the repository.**
Read "What this does not test" before using a number from this page. Like the rest of the repository this was written
with LLM assistance and has not been independently reviewed.

## What is computed

Weak-coupling U(1) lattice gauge theory on a periodic 4-torus, action `(1/2g²)|da|²` for link angles `a`.

**Averaging.** The coarse link is Bałaban's averaged link in its abelian (linear) form, V5 eq. `nonlinear-average`
(RG1 (0.4)): centred blocks `B_y` of odd side `L`, and for `x ∈ B_y`, `x' = x + L e_μ`,

```
b_c = L⁻ᵈ Σ_{x∈B_y}  avg_{γ,γ'} [ a(γ) + a([x,x']) − a(γ') ]
```

with `γ`, `γ'` running over the path families `𝒢(y,x)`, `𝒢(y+Le_μ,x')` (each nonzero coordinate displacement in one run,
every ordering). In the abelian case the logarithm is the identity and the map `Q: a ↦ b` is linear.

**Fluctuation.** Gaussian field constrained by `Q a = 0` and a gauge condition. For a closed contour with link
current `J` (a square of side `nL` in a coordinate plane) the first-step fluctuation factor at the trivial coarse field is

```
κ_C = exp(−(g²/2) E_f),      E_f = Jᵀ Γ J,
```

with `Γ` the covariance (at `g = 1`) of the constrained field. Writing `E_f = α P + β` with `P = 4nL` fine units
and four corners,

```
δm·ε = (g²/2) α,          log z_c = −(g²/8) β.
```

Two gauge conditions are used: **`landau`** (`Q a = 0`, `div a = 0`) and **`xi1`** (`Q a = 0` with Feynman weight
`A + divᵀdiv`, i.e. conditional covariance given `Q a`). A third column, **`total`**, is the unconstrained loop
self-energy, kept only as a cross-check of the machinery (see below).

The loop is gauge invariant but `Q a` is only gauge covariant, so conditioning on it makes `E_f` depend on the gauge
condition. The coefficients are therefore prescription dependent, as the programme's `δm^σ` is for its cutoff
prescription σ.

**Method.** The operators are built on a small auxiliary torus and their Bloch blocks (period `L`) extracted, so that
the 4-torus with `K` blocks per side costs `K⁴` small matrix problems. The momentum sum is folded exactly by the
symmetries of the transverse directions (checked against the unfolded sum).

## Checks that the code does what is claimed

`python3 test_abelian_first_step.py` (under 10 s):

- `Q(dφ)` equals the coarse gradient `φ(c₊) − φ(c₋)` to `10⁻¹⁵` in d = 2, 3 and L = 3, 5, the abelian form of V5
  Lemma `global-average`(ii).
- The loop current is divergence free.
- The Bloch computation of `E_f` agrees with a dense real-space solve on small tori (d = 2, 3; L = 3, 5; all gauge
  conditions) to `10⁻⁸` or better.
- In d = 2 the unconstrained self-energy of a 3×3 loop on a 12×12 torus is `A(1 − A/V) = 8.4375` exactly, the
  two-dimensional area law (compare [`SU2_LATTICE_GAP.md`](https://github.com/brentharts/openai_math_yang_mills/blob/main/SU2_LATTICE_GAP.md) in the companion fork, Part A).
- The constrained energy does not exceed the unconstrained one.

## Results (d = 4, L = 3)

Raw numbers are in `results/`; `python3 fit_perimeter_corner.py` prints the fits. Loops are squares of side `nL` with
`L = 3`, so the largest has side 15 on a torus of side 24. `n ≤ 3` use `K = 10`, `n = 4, 5` use `K = 8`; for `n ≤ 3` the
values at `K = 6, 8, 10` differ by at most `10⁻³` (`K = 8` vs `10`: `4·10⁻⁵`), so the fluctuation energy has converged
in volume and finite-torus effects are not what limits the fits.

`landau` gauge:

| n | P (fine units) | E_f | slope to next n | α | β |
|---|---|---|---|---|---|
| 1 | 12 | 1.855780 | 2.0687 | 0.17239 | −0.2129 |
| 2 | 24 | 3.924427 | 2.0464 | 0.17054 | −0.1684 |
| 3 | 36 | 5.970860 | 2.0518 | 0.17098 | −0.1845 |
| 4 | 48 | 8.022657 | 2.0485 | 0.17071 | −0.1715 |
| 5 | 60 | 10.071188 | | | |

(α, β are computed from the pair of sizes in that row and the next.) The `xi1` condition changes every `E_f` by less than
`6·10⁻⁴` (relative `2·10⁻⁴`).

- **Perimeter law.** `E_f` is linear in the perimeter to about 0.5% from `n = 2`: `α = 0.1707 ± 0.0004`, so
  `δm·ε = 0.0854 g²` per fine unit of length. The successive slopes are `0.1724, 0.1705, 0.1710, 0.1707`: they oscillate with
  decaying amplitude, as one expects from the periodic block structure, rather than trending.
- **Corner term.** `β = −0.17 … −0.18` for `n ≥ 2` (`log z_c ≈ +0.022 g²`). It is determined less sharply than α because it
  is an intercept; the oscillation of about `±0.01` in β between pairs is the honest uncertainty. It is a constant,
  independent of `n`, with no sign of a growing length factor.
- **Scaling in g and ε.** In the Gaussian theory `E_f` is independent of `g` and, in lattice units, of the lattice
  spacing, so `δm = 0.0854 g²/ε` and `log z_c = 0.022 g²` follow, with no logarithm of `ε` (in four dimensions the free propagator at the origin is finite).
  This is the scaling `|δm| ≲ g²/ε`, `|log z_c| ≲ g²` stated in the research outline, with the constants above for this
  analogue.

## What this does not test

- **Non-abelian structure.** The programme concerns a compact simple group. Here the group is U(1), the logarithms in
  the averaging are the identity, and there are no commutators, no large-field regions, no running coupling. The
  logarithmic factors in the programme's bounds do not appear.
- **The bounds and the proof.** Nothing here checks a constant, an inequality, an analytic domain or an estimate of V5 or
  the drafts. Agreement of the scaling is necessary for the programme's statements to be right but says nothing about
  whether the proofs are.
- **The cutoff prescription.** V5 fixes a specific cutoff test σ, a gauge-fixing functional (Bałaban CRE (1.5)–(1.7)),
  and a small-field/large-field decomposition. This analogue uses a plain Gaussian constraint with two simple gauge
  conditions. The numerical values of `δm`, `z_c` are specific to those choices.
- **The remainder.** Only the scalar fluctuation factor at the trivial background is computed, not `Δ_C`, its `g³/ε`
  bound, the dressing, or the coarse-loop comparison.
- **The blocking factor.** V5 takes `L` odd and larger than 11 (Bałaban's choice). The abelian computation works for any odd
  `L`; `L = 3` here, so the constants are not those of `L > 11`.
- **Volume.** The first-step statement is at fixed physical volume. This computation is lattice-unit and its
  volume dependence is only checked to be negligible (above).
- **`total`.** The unconstrained self-energy is kept as a machinery check only. It contains the long-range coarse part, is not
  converged at `K = 8, 10` for the larger loops (the loop is comparable to half the torus), and should not be read for
  `α`, `β`.

## Files

| File | Purpose |
|---|---|
| `abelian_first_step.py` | operators, Bloch blocks, constrained covariance, loop energies |
| `test_abelian_first_step.py` | the checks listed above |
| `run_study.py` | `python3 run_study.py D L K n1,n2,.. [gauges]`, writes `results/*.json` |
| `fit_perimeter_corner.py` | reads `results/`, prints slopes, `α`, `β` |
| `results/` | stored outputs (`d4_L3_K{6,8,10}_n1-2-3.json`, `d4_L3_K8_n4-5.json`) |

Dependencies: Python 3, numpy, scipy. The `K = 10` run for `n = 1..3` took about 12 minutes on one core.
