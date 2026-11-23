# Status: BlockPoincare v0.1 (2026-09-22)

The library has ten modules. With the root file and `checks/Axioms.lean` it comes to 1,763 lines.

| File | Lines |
|---|---|
| `BlockPoincare/Defs.lean` | 154 |
| `BlockPoincare/Cube.lean` | 170 |
| `BlockPoincare/Blocks.lean` | 117 |
| `BlockPoincare/Estimate.lean` | 218 |
| `BlockPoincare/Nontrivial.lean` | 105 |
| `BlockPoincare/Scales.lean` | 107 |
| `BlockPoincare/Centred.lean` | 117 |
| `BlockPoincare/Torus.lean` | 267 |
| `BlockPoincare/Product.lean` | 176 |
| `BlockPoincare/Witness.lean` | 226 |
| `BlockPoincare.lean` | 10 |
| `checks/Axioms.lean` | 96 |

* Every module compiles without errors and without warnings.
* The totalisation audit passes, with 144 reviewed markers.
* The 75 declarations in `checks/Axioms.lean` depend only on `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no `admit`, no `native_decide`, no added axiom and no
  `set_option`.
* No line exceeds 100 characters. All files use LF endings.

Everything was compiled module by module with `lean +leanprover/lean4:v4.34.0-rc2` against the
mathlib build of `FiniteVolumeYM2Phi42`. Nothing has been built with `lake`, because no host
project requires the library.

## What is proved

1. **The fractional Poincaré inequality on a set of finite diameter**, with the explicit constant
   `D^(2+2s) / μ A`, for every `s > 0` (`l2sq_sub_mean_le_diam`). This is the manuscript's step
   that is cited to Hurri-Syrjänen–Vähäkangas; on a set of finite diameter it is elementary, and
   the proof here is two lines of convexity plus `dist ≤ D`. **No literature axiom.**
2. **The fractional block Poincaré estimate** in pairing form (`pairing_le`) and in dual-norm
   form (`hNegNorm_le_of_blockIntegral_zero`), for a partition into congruent blocks.
3. **On the two-dimensional torus.** `AddCircle L × AddCircle L` is cut into `M²` squares of side
   `l = L/M` (`Torus.squares`), and `‖f‖_{H^{-s}} ≤ l^s ‖f‖_{L²}` (`Torus.hNegNorm_le_squares`).
   With `M = M₀^j` this is the manuscript's `‖f_j‖_{H^{-s}} ≤ a_j^s ‖f_j‖_{L²}`
   (`Torus.hNegNorm_le_scale_pow`), and `Σ_j a_j^s < ∞` (`Torus.summable_torus_scale`).
   The one-dimensional statement is `Torus.hNegNorm_le_arcs`.  Every `L²` field obeys the
   estimate once centred on the squares (`Torus.hNegNorm_centre_le_squares`).
4. **The Euclidean cube form** `‖f‖_{H^{-s}} ≤ 2^((1+s)/2) l^s ‖f‖_{L²}` (`hNegNorm_le_cube`,
   `hNegNorm_le_scale`), for blocks of measure `l²` and diameter `√2 l`.
5. **Non-vacuity**: `hNegNorm_pos` in general, and a concrete model (`TwoPoint`) on which every
   hypothesis is discharged and `0 < ‖f‖_{H^{-s}} ≤ 1`.
6. **The centred fibre coordinate** `D_B ζ = ζ - 1_B m_B ζ` as a projection onto the class of
   functions with vanishing block integrals (`Centred`).

## What is not done

* **No concrete `f` on the torus.** The torus statement is an implication; no function on the
  torus is exhibited with zero integral on every square *and* finite `Hˢ` norm. For a piecewise
  constant `f` the second condition holds exactly for `s < 1/2`, and proving it needs the
  integrability of `dist ^ (-2-2s)` off the diagonal, which is not formalised. Both sides of the
  estimate are shown to be positive only on the two-point model.
* **The torus distance here is the supremum distance** (mathlib's metric on a product), so a
  square of side `l` has diameter `l`. The Euclidean torus, where the diameter is `√2 l`, is not
  constructed; the corresponding estimate is proved abstractly (`hNegNorm_le_cube`) and only
  needs a partition with `diam ≤ √2 l` to apply.
* **`s = 1` is included but empty in this formulation.** The estimate is proved for every
  `s > 0`. At `s = 1` the Gagliardo seminorm `[·]_1` is finite only for constants (a classical
  fact, not formalised here), so the `s = 1` instance of the theorem says nothing useful. The
  `H¹`-gradient version, which is what `eq:uv-hierarchy-fractional-Poincare` wants at `s = 1`,
  is not proved; it needs a gradient on the torus.
* The isomorphism statement of `lem:app-centred-fibre` in terms of submodules, and the inverse of
  `D_B`; only the projection properties are formalised.
* Vector-valued `f` (only `ℝ`), sharpness of the constant, and any converse inequality.

## Process

Written in one session by the wave S11 agent `BP`, from the brief in
`scratchpad/waveS11/brief_BP.md`. The definitions `l2sq`, `gagliardoSq`, `hsNormSq`, `hNegNorm`
are the ones the brief fixes for a later merge with the `ParaproductTorus` library, which is
**not** imported and whose files were not touched.

Design decisions worth recording:

* **`ℝ≥0∞` for the quadratic quantities.** All three of `l2sq`, `gagliardoSq`, `hsNormSq` are
  lower integrals, so they are defined without integrability hypotheses and the two monotonicity
  steps of the proof (Jensen, the diameter bound) are free. Only the duality step needs Bochner
  integrals, and there `MemLp _ 2` supplies every side condition.
* **`⨆` in `ℝ≥0∞` for the dual norm**, rather than a real `sSup`: no non-emptiness or
  boundedness argument is needed, and a negative pairing is truncated harmlessly because the
  admissible set is symmetric (`neg_mem_unitBall`).
* **Metric, not pseudometric.** The Gagliardo integrand is `0 / 0 = 0` on the diagonal; off the
  diagonal the denominator is positive. On a pseudometric space the second statement fails and
  the diameter step would be false as stated.
* **Congruent blocks.** `BlockPartition` requires all blocks to have the same measure. This is
  what makes the constant uniform in the block, and it is exactly the manuscript's setting.
* **Arcs as preimages.** The arcs of `AddCircle T` are defined as preimages of intervals under
  the coordinate `AddCircle.equivIoc T 0`, not as images of intervals. Disjointness and covering
  are then inherited from the intervals, and only the measure needs
  `AddCircle.measurePreserving_mk`.

## Possible next steps

1. **A concrete torus function**: a piecewise constant `f` with zero mean on every square and
   finite `Hˢ` norm for `s < 1/2`. This is the one honest gap left in the chain from the
   definitions to a non-vacuous torus statement.
2. **The `H¹` version** at `s = 1`, with the gradient seminorm.
3. **Merge with `ParaproductTorus`** once both exist: the four definitions are shared verbatim,
   so the merge should be a matter of deleting one copy.
4. Wire the library into `FiniteVolumeYM2Phi42` as a path dependency and discharge the
   manuscript's `lem:app-block-poincare` hypothesis with `Torus.hNegNorm_le_scale_pow`.
