# Functional-Analysis Inventory for Friedrichs Extension

This inventory is for mathlib revision `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`
(Lean `v4.34.0-rc2`), chosen to match the compact-Lie heat-kernel project.

## Already formalised and directly reusable

### Hilbert-space foundations

- Real and complex inner-product spaces, Cauchy--Schwarz and the usual norm identities.
- `InnerProductSpace.Core`: construct a normed inner-product-space structure from a positive-definite
  scalar product.  This is especially important for the shifted energy scalar product on the
  operator domain.
- `InnerProductSpace.Core.toNormedAddCommGroup` and `InnerProductSpace.ofCore`.
- `UniformSpace.Completion` for normed spaces.
- `Mathlib.Analysis.InnerProductSpace.Completion`: the completion of an inner-product space carries
  the canonical inner-product structure, hence is a Hilbert space.
- Orthogonal complements and orthogonal projections onto complete/closed subspaces.
- Fréchet--Riesz: `InnerProductSpace.toDual`.

### Continuous linear maps and Banach-space theorems

- bounded/continuous linear maps and continuous linear equivalences;
- extension by continuity from dense subspaces/completions;
- Banach--Steinhaus (`banach_steinhaus`);
- Banach open mapping theorem (`ContinuousLinearMap.isOpenMap`);
- closed graph theorem (`ContinuousLinearMap.ofIsClosedGraph`);
- Hahn--Banach and the strong dual;
- bounded adjoints on Hilbert spaces (`ContinuousLinearMap.adjoint`).

### Coercive forms

- `IsCoercive` for bounded real bilinear forms;
- the real Hilbert-space Lax--Milgram theorem
  `IsCoercive.continuousLinearEquivOfBilin`.

This is sufficient for a direct resolvent construction once the Friedrichs energy domain has been
completed.

### Unbounded operators

Mathlib's `LinearPMap` infrastructure is unusually well aligned with Friedrichs:

- explicit operator domains as submodules;
- graph of a partially defined operator;
- closed operators: `LinearPMap.IsClosed`;
- closable operators: `LinearPMap.IsClosable`;
- closure/minimal closed extension: `LinearPMap.closure`;
- operator cores: `LinearPMap.HasCore`;
- inverse partially defined operator: `LinearPMap.inverse`;
- adjoint domain and unbounded adjoint: `LinearPMap.adjoint`;
- formal adjoints: `LinearPMap.IsFormalAdjoint`;
- self-adjoint unbounded operators via `IsSelfAdjoint`;
- self-adjoint operators have dense domain and are closed.

Therefore the project should not rebuild graph closure, adjoints, or the notion of self-adjointness.

### Bounded positive operators

- `LinearMap.IsPositive` and `ContinuousLinearMap.IsPositive`;
- positivity includes symmetry/self-adjointness in the bounded setting;
- positivity is stable under conjugation by an adjoint:
  `ContinuousLinearMap.IsPositive.conj_adjoint`;
- Loewner order and substantial bounded-operator/C*-functional-calculus infrastructure.

This is useful for the prospective resolvent
`R_λ = J ∘ J†`, which is automatically positive.

## Not found as packaged theory

The following are the actual missing Friedrichs layer:

1. A packaged notion of a densely defined lower-semi-bounded closed/closable quadratic form on a
   Hilbert space.
2. The theorem that the form associated with a densely defined semibounded symmetric operator is
   closable.
3. The energy-completion embedding into the ambient Hilbert space, including injectivity of the
   completed embedding (the substantive form-closability statement).
4. The closed-form representation theorem in the form needed for Friedrichs.
5. The Friedrichs extension theorem itself.
6. General unbounded spectral/functional calculus sufficient to define `exp (-t A)` directly for an
   arbitrary self-adjoint unbounded operator.

The first Friedrichs construction need not wait for item 6.

## Preferred proof route

Let `A` be densely defined, symmetric, and `A >= m`.  Choose `λ` with `m + λ > 0` and put

    b_λ(u,v) = <Au,v> + λ<u,v>.

1. Use `InnerProductSpace.Core` to put the `b_λ` norm on a copy of `D(A)`.
2. Complete it using `UniformSpace.Completion`; the completion is automatically a Hilbert space.
3. The estimate `(m+λ) ||u||_H^2 <= b_λ(u,u)` makes the inclusion `D(A) -> H` continuous, so extend
   it to `J : V_λ -> H` using the existing completion/extension API.
4. Prove `J` injective.  This is essentially the closability of the semibounded form; symmetry and
   density of `D(A)` should prove it by testing against the dense canonical image of `D(A)`.
5. Use the bounded Hilbert adjoint `J† : H -> V_λ` and set `R_λ = J ∘ J† : H -> H`.
6. Existing positive-operator machinery gives positivity/self-adjointness of `R_λ`; prove it is
   injective and has dense range from injectivity/density of `J`.
7. Define `(A_F + λ)` as `R_λ.inverse`, a `LinearPMap`, and then shift back by `λ`.
8. Prove `A <= A_F`, self-adjointness, preservation of the lower bound, and the Friedrichs form
   characterisation.

This route uses the existing functional-analysis library almost everywhere; the main genuinely new
argument is Step 4 plus the unbounded inverse/self-adjoint bookkeeping in Steps 6--8.
