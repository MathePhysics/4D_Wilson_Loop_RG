# Open (R-eval-old): Draft of the Response Bound at VAR's Representative

Status: working draft for note l.5. Nothing here is in the note yet.

**The data relation for VAR's R-gauge representative (derived, free case).**
- VAR's data are CMP98 (14)-type averages, whose contours start at the block centres. There Q(Dλ)(c) = L^{−1}(λ(c₊) − λ(c₋)) (PRT I (1.9), p.19), and the data group is VAR (4)'s N_𝔅, λ = 0 at the points of 𝔅_k (REG (1.14); table line 234).
- Naming. This draft's Q is the table's Q̃ (#T11.19 and #T10.23: Q̃D = D̄P, here in (14)'s normalisation with the factor L^{−1}), and this draft's Q_line is the table's Q, the line averages. So this draft's Q = Q_line − D^{bl}K is the table's Q̃ = Q − D̄K (RG I (0.4), p.253).
- VAR's representative is the R-gauge one, U₁ = U′_k^{u^{−1}} (VAR (145)–(153), p.301; table #T11.18). Here U′_k is the axial minimiser of REG (1.19), and u has ū^j = 1 (REG (1.29)), whose linear part is Q′, PBG (3.18)–(3.19)'s transported block mean (p.393). So at first order a = u_ax + Dμ₀ with Q′μ₀ = 0 and RD*a = 0, R the projection onto ΔN(Q′). This is the class used in (iv). U₁ is not in 𝔙_k (REG p.81 l.23–25); its averages obey REG (1.30).
- There is one averaging. REG's Ũ′^n = (\overline{U′U₀})^n(Ū₀^n)^{−1} (REG (1.20), p.79) is VAR's average relative to the base, and the axial set satisfies Ũ′^j = V(Ū₀^j)^{−1} on Λ_j (REG p.81 l.24–25), so Qu_ax = δ.
- The straight parts are mean-covariant (derived, free case). Q′λ(B+e_μ) − Q′λ(B) = L^{−d}Σ_{x∈B}(Dλ)([x, x+Le_μ]), so D^{bl}(Q′λ) = L·Q_line(Dλ), with Q_line the straight parts of CMP98 (14) (Q = Q_line − D^{bl}K, *What Remains*). In the axial gauge the contour sums vanish (REG (1.19); PRT I p.19 l.16), so K(u_ax) = 0 and Q_line u_ax = δ. Q′μ₀ = 0 gives Q_line(Dμ₀) = 0.
- Hence, with λ := Δ^{−1}D*a, v := a − Dλ, and σ := Q′λ,
  D^{bl}σ = L·Q_line(Dλ) = L(Q_line a − Q_line v) = L(δ − Q_line v).
  This is "The Gradient Part"'s relation with Q_line in place of Q, in (14)'s normalisation. Q_line has the spread weights ≤ 2L^{−d}, with no contour concentration. a itself is not in 𝔙_k: Qa = δ + L^{−1}D^{bl}(μ₀ at the centres) (REG p.81 l.23–25, (1.30)). [To check: the covariant version at a regular base, with the transports of PBG (3.19) in Q′ and of (14) in Q_line.]
- Section (v) uses VAR's constraint only through the gauge-invariant F (with (14) and PRT I (1.9) for the multipliers) and the Landau condition RD*a = 0, so it holds for the R-gauge representative as written.

## The Target

Note l.5 reduces Open (R-eval-old) to one input: a field bound C_{resp,∞} = o(L) for the sup-norm response of U(𝐁_k″(Y₁), ·) at VAR's representative, in fine-phase units, with C_{resp,∞}(1+β₀)/L ≤ (1−β)/4. At first order the representative's field is v + Dλ:

- v is the global Landau part, with D*v = 0;
- λ := Δ^{−1}D*a is the gradient part.

l.5 says that the bound for v does not control Dλ.

## The Gradient Part Is a Δ-Minimal Interpolant (Derived)

**Sources (read).**
- REG p.80 l.13–14: R(U₀) is the orthogonal projection, in the real Hilbert space L²(Ω₀, 𝔤), onto Δ_{U₀}N(Q′(U₀)), where N(Q′(U₀)) = {λ : Q′(U₀)λ = 0} (l.11).
- (1.27) (l.17): the Landau condition is R(U₀)D*_{U₀}(1/i)log U′ = 0.
- p.80 l.26–28 and (1.29) (p.81 l.14): the admitted gauge transformations satisfy (R̄₀u^j)(y) = 1 on Λ_j. For u = e^{iλ} the linear part of (1/i)log(R̄₀u^j)(y) is (Q′_j(U₀)λ)(y).
- (1.30) (p.81 l.28) and the crossing-bond formula (p.81 l.39–43): the averages of U^u are those of U, gauge transformed by the block transformation R̄₀u^j.

**Linearisation.** At the real base U₀, write D := D_{U₀} and Q := Q(U₀).
- (1.30) linearised, with p.80 l.26–28, gives Q(Dμ) = D^{bl}(Q′μ). Here D^{bl} is the block covariant gradient at the averaged base Ū₀, and crossing bonds are included by p.81 l.39–43.
- So a field's data change under a gauge function μ only through the block gauge function Q′μ.

**The decomposition.** Let a be the first-order field of VAR's representative, with data Qa = δ. Put λ := Δ^{−1}D*a and v := a − Dλ, so that D*v = 0.
- (1.27) says R D*a = 0. Since D*a = Δλ, this means Δλ ⊥ ΔN(Q′), that is ⟨Δλ, Δν⟩ = 0 for every ν ∈ N(Q′).
- So λ is the ‖Δ·‖-minimal element of its coset λ + N(Q′) = {μ : Q′μ = σ}, with σ := Q′λ: λ = H_Δσ, where H_Δσ := argmin{‖Δμ‖ : Q′μ = σ}.
- D^{bl}σ = Q(Dλ) = Qa − Qv = δ − Qv.

Hence

  a = v + D H_Δ σ,  with D^{bl}σ = δ − Qv.

The gradient part is fixed by v's data defect δ − Qv and by one operator, the Δ-minimal interpolation of block gauge functions. It is not an axial lift. Bałaban's own expectation that the Landau gauge removes the axial gauge's factor L (REG p.80 l.8–9: "choosing properly a gauge condition we can get V′ = e^{iL^{−1}A} with a bound |A| ≤ O(α₀+α₁)") holds in this form, provided H_Δ's constant is L-uniform.

**The bound it gives.** Let C_v be the sup-norm constant of δ ↦ v and C_Δ that of D^{bl}σ ↦ DH_Δσ, both in the units of l.5. The averages are bounded by the sup, so

  C_{resp,∞} ≤ C_v + C_Δ(1 + C_v).

So C_{resp,∞} = o(L) follows from C_v = O(1) and C_Δ = O(1) uniformly in L. More generally it follows from C_v(1 + C_Δ) + C_Δ = o(L).

## (i) The Free Single Layer: C_Δ = O(1) Uniformly in L (Derived)

**Setting.**
- Fine lattice ℤ^d with blocks B(y) = Ly + {0, …, L−1}^d and Q′μ(y) = L^{−d}Σ_{x∈B(y)}μ(x). This is REG's average at U₀ = 1 (p.81 l.43).
- Δ is the lattice Laplacian, with symbol Δ̂(p) = Σ_μ 4sin²(p_μ/2) ≥ (4/π²)|p|² on (−π, π]^d.
- For a block momentum k ∈ (−π, π]^d, put p_l := (k + 2πl)/L for l ∈ {0, …, L−1}^d, taken mod 2π, and û(p) := Π_μ e^{−i(L−1)p_μ/2} sin(Lp_μ/2)/(L sin(p_μ/2)).
- Then (Q′μ)^(k) = Σ_l û(p_l)μ̂(p_l).

**The minimiser.** The Lagrange condition Δ²μ = Q′*ν gives

  μ̂(p_l) = û(p_l)^*Δ̂(p_l)^{−2}S(k)^{−1}σ̂(k),  S(k) := Σ_l |û(p_l)|²Δ̂(p_l)^{−2}.

**Affine data.** H_Δ reproduces affine data. For σ(y) = c·(Ly + (L−1)/2) + c₀, the function μ(x) = c·x + c₀ has Q′μ = σ and Δμ = 0. So the kernel of σ ↦ ∇H_Δσ annihilates constants and is exact on affine σ.

**Uniform symbols.** Write L^{−4}Δ̂(p_l)^{−2} = |k + 2πl|^{−4}(1 + o(1)), uniformly on compact sets of k, together with the bound L^{−4}Δ̂(p_l)^{−2} ≤ (π²/4)²|k + 2πl|^{−4} everywhere.
- Each l ≠ 0 term of L^{−4}S carries |û(p_l)|² ≤ Π_μ min(1, π²/|k_μ + 2πl_μ|²)·O(|k|²). It vanishes at k = 0, since a periodic mode has zero block average.
- Σ_{l≠0} Π_μ min(1, l_μ^{−2})|l|^{−4} converges, and it still converges with the gradient's extra factor |l|.
- So L^{−4}S(k) and the l-sums of ∇H_Δ's symbol converge uniformly, as L → ∞, to the continuum sums over l ∈ ℤ^d.

**The analytic strip.**
- The combination Δ̂(p₀)^{−2}S(k)^{−1} equals 1/𝒩(k), with 𝒩(k) := |û(p₀)|² + Σ_{l≠0}|û(p_l)|²Δ̂(p₀)²Δ̂(p_l)^{−2}, analytic near k = 0 with 𝒩(0) = 1.
- On real k, 𝒩 > 0. By the uniform convergence to the continuum function, |𝒩| ≥ c(d) > 0 on a strip |Im k| ≤ κ₀(d) for all L ≥ L₀(d).
- The fine gradient's factor e^{ip_{l,ν}} − 1 = i(k + 2πl)_ν/L·(1 + o(1)) supplies the factor 1/L.
- Writing σ̂ through the block gradient costs 1/Δ̂_{bl}(k). That is compensated by S(k)^{−1} = O(|k|⁴L^{−4}) on the l = 0 term and by û(p_l) = O(|k|) on the others.

**The bound.** So the kernel K(x, y′) of D^{bl}σ ↦ DH_Δσ is analytic in a uniform strip. It satisfies |K(x, y′)| ≤ C(d)L^{−1}e^{−κ₀|x/L − y′|} for a fine site x and a block bond y′, uniformly in the position of x inside its block. Summing over the block bonds y′ gives

  sup|DH_Δσ| ≤ C(d)L^{−1}sup|D^{bl}σ|,

that is C_Δ = C(d) in the units of l.5, where a datum on a 1-block has L times its phase per fine bond. The same Bloch argument with Δ in place of Δ² and the vector Laplacian gives C_v = C(d) on the free single layer.

## (ii)–(iii) The Bulk of the Multi-Layer Problem: C_Δ ≤ (1 + log L)^p (Derived in Outline)

This step uses the large-field note's tools (WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md #0.1, derived, not reviewed).

- **L² bound.** The note's interpolation (I) has Q′I = m, reproduces affine functions, and satisfies ‖ΔI(Q′α)‖ ≤ C(d)(1 + log L)‖∇f‖. By minimality, ‖ΔH_Δσ‖ ≤ ‖ΔIσ‖.
- **Coercivity on N(Q′).** Each block's own Poincaré bound for zero block mean gives ‖w‖_B ≤ C(d)S‖∇w‖_B for w ∈ N(Q′), with S the block's side. Since ‖∇w‖² = ⟨w, Δw⟩, this yields ‖∇w‖ ≤ C(d)S‖Δw‖ and ‖w‖ ≤ C(d)S²‖Δw‖ blockwise. This is a gap c(d) in each block's units, with no interface term, as for the note's G′_□.
- **Decay.** Write H_Δσ = Iσ + w with w ∈ N(Q′). Then w minimises ‖Δ(Iσ + w)‖ on N(Q′). The Combes–Thomas commutators of Δ² with e^{δρ}, where ρ is the distance in each block's units, are those of the note, so w decays at a rate δ(d) that is L-uniform.
- **Pointwise.** h := ΔH_Δσ solves Δh = Q′*ν, with ν blockwise. The note's bulk local regularity, sup_{block}|u| ≤ C(d)(L^{−d/2}‖u‖_{2·block} + L²sup|g|), applied first to h and then to ∇H_Δσ through Δ(H_Δσ) = h, gives sup|DH_Δσ| ≤ C(d)(1 + log L)^pL^{−1}sup|D^{bl}σ|. This holds on the blocks at distance ≥ 2L from the pinned region, where the note's bulk lemma applies.

## (iv) At the Pinned Region: the Same Input as LF-2 (a)

At the pinned region, Λ^c in the large-field note's notation, both parts need a boundary estimate.
- **v.** Its field bound comes through the note's dyadic sum Σ_k2^{k(1−d/2)}‖F‖_{B_{2^k}(x)}. Without a Morrey gain (γ = 0) that sum gives only C_v = O(L), which is borderline and not enough. Any γ > 0 gives a power of 1 + log L. This is LF-2 (a).
- **Dλ.** H_Δσ is a scalar Δ²-minimiser with Dirichlet data at the pinned region. In the continuum it behaves like r^{1+z} at an edge, with z > 0 the Dirichlet biharmonic corner exponent, so Dλ stays bounded and only its gradient is singular. The lattice version needs the same kind of Morrey or Campanato estimate as LF-2 (a): ‖ΔH_Δσ‖²_{B_r(x)} ≤ C(d)(r/R)^{d−2+2γ}‖ΔH_Δσ‖²_{B_R(x)} plus source terms, for some γ(d) > 0 and 1 ≤ r ≤ R ≤ L(1 + log L)^p.

**Where the boundary matters.** The large-field note's Λ^c is the pinned region: 1_m marks the bonds with an endpoint in Λ^c, which carry the mass. For U(𝐁_k″(Y₁), ·) the pinned region is the complement of Ω₁(Y₁) (note l.130; CRE (2.11), p.256 l.36–41). At blocks of Λ^{old} at distance D from it, in local block units, the bulk bounds give C_{resp,∞} ≤ C(d)(1 + log L)^p + C(d, L)e^{−δ(d)D}. When D grows with parameters chosen after L, the second term is at most 1, as in the large-field note's choice ¼αδ₀W ≥ log L. But Λ^{old} can come close to the pinned region. Y₁ is the smallest localization domain containing X and the components of Z that meet X (LFR II p.373 l.15–16), and components of Λ can meet Y₁'s boundary layer Y₁∖Y₁⁰, of width at most 2M₁ (p.373 l.26–27, l.32–34). So the boundary case is needed.

**The layers of Λ^{old}.** On Λ^{old}, U_k^0 takes the scale-h data V_h, so Λ^{old} carries blocks of the layer h of 𝐁_k″(Y₁). The layers' separations bound the distance to the pinned region.
- A localized determining set has dist(Ω_n, Ω_{n−1}^c) ≥ L^nξM₁ (CRE p.256 l.58–60).
- The global one has dist(Ω_j^c, Ω_{j+1}) ≥ RML^jη (PRT II (2.2)).

So:
- **h ≥ 2.** Λ^{old} is at distance at least min(RM, LM₁) layer-1 blocks from the pinned region. R, M, and M₁ are chosen after L, so the boundary term C(d, L)e^{−δ(d)min(RM, LM₁)} is at most 1. Then C_{resp,∞} ≤ C(d)(1 + log L)^p + 1 = o(L), given the bulk bound for VAR's representative a itself (below).
- **h = 0.** The data on Λ^{old} are the bonds themselves (CRE (2.11)), real there, so U_k^0's complex part vanishes on Λ^{old}.
- **h = 1.** Layer-1 blocks of Λ^{old} can be adjacent to the pinned region. This is the only case that needs the boundary estimate.

**The bulk bound for a itself (outline, to be written).** v alone is long-range: it is the global Landau form on the torus, sourced also by the pinning reactions, with |x|^{2−d} decay. So the bulk bound is taken for a, whose kernel decays exponentially (VAR (190)).
- s := D*a = Δλ solves Δs = Q′*ν′ with ν′ blockwise, since λ is the Δ²-minimiser of its coset (above).
- The Hodge identity gives Δa = Q*ν + Ds, componentwise in the free case.
- Local regularity: sup_B|s| ≤ C(d)L^{−d/2}‖s‖_{3B}, by the block-Green identity for ν′ and the lattice mean-value property. Likewise sup_B|a| ≤ C(d)(L^{−d/2}‖a‖_{3B} + L sup_{3B}|s|).
- Local L²: each block's Poincaré bound with Qa = δ, ‖a‖_B ≤ C(d)(L‖∇a‖_B + L^{d/2}|δ|_B), and ‖∇a‖² = ‖da‖² + ‖D*a‖², localized by Combes–Thomas in block units.
- **‖D*a‖ without v.** REG's orbit is generated from the axial element (1.28) (p.81 l.7–9) by the gauges of (1.29), so at first order the class is u_ax + DN(Q′), with u_ax the axial representative. The Landau condition makes a the ‖D*·‖-minimiser of that class. So ‖D*a‖ ≤ ‖D*u_ax‖, localized by Combes–Thomas for the Δ²-problem on N(Q′), whose gap is c(d) in each block's units (above).
- **The axial competitor.** Inside a block u_ax is a sum of F along axial paths of length at most dL. In the bulk, |F| ≤ C(d)(1 + log L)^p|δ|L^{−2} (the large-field note's bulk regularity), so |u_ax| ≤ C(d)(1 + log L)^p|δ|L^{−1}. Its divergence is of that size per site on the block faces, where the axial gauge jumps, and smaller inside. So ‖D*u_ax‖_B ≤ C(d)(1 + log L)^pL^{(d−3)/2}|δ|, against L^{(d−4)/2}|δ| for a smooth field.
- **The result in the bulk.** sup_B|s| ≤ C(d)L^{−d/2}‖s‖_{3B} ≤ C(d)(1 + log L)^pL^{−3/2}|δ|, and the source Ds contributes at most L sup|s| ≤ C(d)(1 + log L)^pL^{1/2}·(|δ|/L) to sup|a|. With ‖da‖ bounded by the smooth competitor, ‖da‖_B ≤ C(d)(1 + log L)L^{(d−4)/2}|δ|, the Poincaré term gives L^{−d/2}(L‖∇a‖_{3B} + L^{d/2}|δ|/L) ≤ C(d)(1 + log L)^pL^{1/2}·(|δ|/L). Hence in the bulk, in fine-phase units of the data,

  C_{resp,∞} ≤ C(d)(1 + log L)^pL^{1/2} = o(L).

- The local regularity step is replaced by (v) below, which holds at the pinned region as well. Still to check: the Combes–Thomas localization of the two global minimalities (of ‖da‖ and of ‖D*a‖).

## (v) Local Regularity at the Pinned Region by the Maximum Principle (Free Case, Derived)

The h = 1 case needs no boundary regularity (no Morrey bound, no corner exponents) once a is represented through scalar Dirichlet Green functions. The free case U₀ = 1 is treated here; the regular base is in *What Remains*.

**The equations.**
- The pinned bonds are the bonds with an endpoint in the pinned region (the large-field note's 1_m); the other bonds are free. The data change is supported on Λ^{old}, and on the pinned region the data are the bonds themselves (CRE (2.11)), so a = 0 on the pinned bonds.
- The action is minimised over the free bonds subject to VAR's constraint Qa = δ (CMP98 (14)), so d*F = Q*ν on the free bonds, F := da, with one multiplier ν(b′) per block bond. F and d*F are gauge invariant at first order, so the equation holds for the R-gauge representative a as well, though a's own averages are REG's (see the top).
- The admitted gauge functions vanish at the pinned sites (p.80 l.26–28). So the Landau condition (1.27) says ⟨s, Δμ⟩ = 0 for every μ ∈ N(Q′) vanishing there, s := D*a, that is, Δs = Q′*ν′ at the non-pinned sites, with one multiplier ν′(B) per block. Every bond at a pinned site is pinned, so s = 0 at the pinned sites.
- On ℤ^d the Laplacian on 1-forms, d*d + DD*, acts as the scalar Laplacian on each component. So Δa_μ = (Q*ν)_μ + ∇_μs on the free μ-bonds, with a_μ = 0 on the pinned μ-bonds: a scalar Dirichlet problem for each μ.

**The multipliers are block-divergence-free.** Let ψ_B be supported on the sites of a layer-1 block B all of whose bonds are free, with ψ_B(y_B) = 1 at B's centre. The contour sums of Dψ telescope in CMP98 (14), so Q(Dψ)(c) = L^{−1}(ψ(c₊) − ψ(c₋)) (PRT I (1.9), p.19), and Q(Dψ_B) = L^{−1}D^{bl}e_B. Dψ_B is supported on free bonds, so 0 = ⟨F, dDψ_B⟩ = ⟨Q*ν, Dψ_B⟩ = L^{−1}⟨ν, D^{bl}e_B⟩. So (D^{bl*}ν)(B) = 0, the sum running over the block bonds of B that carry a constraint. By CMP98 (14) (p.19 l.38–42), Ā_c = Σ_{x∈B(c₋)}L^{−(d+1)}(A(Γ_{c₋,x}) + A([x, x(c)]) + A(Γ_{x(c),c₊})), with Γ_{c₋,x} B(c₋)'s contour from its centre to x and Γ_{x(c),c₊} the reversed contour of B(c₊). So in Q(b″), b″ ∋ B, B's contours enter with the same weight L^{−(d+1)}, with the sign + when B is the initial block and − when it is the final one. Their part of Q*ν on B's bonds is therefore a multiple of (D^{bl*}ν)(B) and vanishes. Only the straight parts [x, x(c)] remain. On a μ-bond of B at position m ∈ {0, …, L−1} along μ, these carry the weights (m+1)L^{−(d+1)} in Q(B, B+e_μ) and (L−1−m)L^{−(d+1)} in Q(B−e_μ, B). Hence |Q*ν| ≤ 2L^{−d}max_{b″∋B}|ν(b″)| on B's free bonds. Γ_{x(c),c₊} is B(c₊)'s contour Γ_{c₊,x(c)} reversed: PRT I (1.7)–(1.8) (p.18 l.44–52, p.19 l.1–8) define only the contours Γ_{y,x} from a block's centre y to x, and CMP98 p.19 l.41–42 orients the union from c₋ to c₊. The crossing block bonds at ∂Λ_1 (REG p.81 l.36–43: b₋ ∈ Λ_0, b₊ ∈ Λ_1) carry constraints too. B(b₋) is an L-cube of Λ_0 (Ω₁ is a union of L-cubes), so all its bonds are pinned. On B's bonds, such a constraint has the straight-part weights (L−1−m)L^{−(d+1)} (or (m+1)L^{−(d+1)}), and B's contour enters with the sign of the final block. So these multipliers are included in (D^{bl*}ν)(B) = 0 (Q(Dψ_B)(b) = L^{−1}(ψ_B(y_B) − ψ_B(b₋)) = L^{−1}, since ψ_B vanishes in Λ_0), in the bound on |Q*ν|, and in the test-field bound below. The crossing datum is the (14)-type average up to a fixed factor (checked). REG's crossing formula (p.81 l.34–42, raw minus one, from CMP98 (97), (99), (87), and (105)) gives the datum as the factor exp[iΣ_{x∈B(b₋)}L^{−d}(1/i)log(R̄^{j−1}_{0,b₋}Ū̄^{j−1}_1)(Γ_{b₋,x})] times (Ū̄^j_1)_b. At j = 1 this factor is a function of U₁ on the contours Γ_{b₋,x} ⊂ B(b₋) only. B(b₋) is an L-cube of Λ_0, since Ω_1 is a union of L-cubes, so its bonds are pinned. There U₁ = U′, since REG's normalised u is 1 at the layer-0 points ((1.70) is an empty sum at j = 0, p.88 l.38–44). So the factor is fixed by the pinned data, with no linear part in a, and the constraint on the free bonds is (Ū̄^1_1)_b, the (14)-type average.

**The multipliers are bounded by local energies.**
- For b′ = (B, B+e_μ), let φ_{b′} := (α₁Ψ₁ + α₂Ψ₂)(·/L) e_μ. Here Ψ_i are fixed smooth bumps in the unit cube centred at μ-positions 1/4 and 3/4, and α₁, α₂ = O(1) solve L^{−(d+1)}Σ(m+1)φ = 1 and Σ(L−1−m)φ = 0, for L ≥ L₀(d). Then Qφ_{b′} = e_{b′} on the straight parts, and B's contour part drops out against ν as above. So ν(b′) = ⟨Q*ν, φ_{b′}⟩ = ⟨F, dφ_{b′}⟩ and |ν(b′)| ≤ C(d)L^{d/2−1}‖F‖_B.
- With ψ_B := cΨ(·/L), c = O(1), ‖Δψ_B‖ ≤ C(d)L^{d/2−2}, and ν′(B) = ⟨s, Δψ_B⟩, so |ν′(B)| ≤ C(d)L^{d/2−2}‖s‖_B.
- Both hold at a block next to the pinned region, since the test fields live on B's interior.

**The Green function and Caccioppoli.** For a cluster W of the 5^d L-cubes around B (its parts in the pinned region included), let G_W be the Green function of the scalar lattice Laplacian killed at the pinned bonds (sites) and outside W. It is the expected number of visits of the simple random walk before it leaves the free part of W, so 0 ≤ G_W(x, y) ≤ G_{ℤ^d}(x, y) ≤ C(d)(1 + |x − y|)^{2−d}. For k ≥ 1, G_W(x, ·) is harmonic on the free bonds of Ã_k := {2^{k−1} ≤ |y − x| < 2^{k+2}} and vanishes on the pinned ones and outside W. Testing with η²G_W(x, ·), with η = 1 on A_k := {2^k ≤ |y − x| < 2^{k+1}}, supported in Ã_k, and |∇η| ≤ C2^{−k}, gives ‖∇G_W(x, ·)‖_{A_k} ≤ C(d)2^{−k}‖G_W(x, ·)‖_{Ã_k} ≤ C(d)2^{k(1−d/2)}. The test function vanishes wherever G_W does, so there is no boundary term at the faces, edges, or vertices of the pinned region.

**The mean value inequality.** Let h be harmonic on the free bonds of W and vanish on the pinned bonds. Then f := |h|, extended by 0, is subharmonic and nonnegative on the interior of W: at a free bond |h| is at most the average of its neighbours' |h|, and at a pinned bond f = 0.
- Let η be a cutoff with η = 1 on B_{L/2}(x), support in B_L(x) ⊂ W, |∇η| ≤ C/L, and |Δη| ≤ C/L². Since ηf has finite support, f(x) = Σ_yG_{ℤ^d}(x, y)(−Δ)(ηf)(y).
- The lattice product rule gives −Δ(ηf) = η(−Δf) + (terms with a difference of η times f or a difference of f, at shifted points). The first term is ≤ 0, and the others live on the annulus L/2 ≤ |y − x| ≤ L + 1, where G_{ℤ^d}(x, y) ≤ C(d)L^{2−d}.
- So f(x) ≤ C(d)L^{2−d}(L^{−1}Σ_{ann}|∇f| + L^{−2}Σ_{ann}f). Caccioppoli for nonnegative subharmonic f (test η′²f) gives ‖∇f‖_{ann} ≤ C(d)L^{−1}‖f‖_{B_{2L}(x)}. Cauchy–Schwarz on the annulus then gives f(x) ≤ C(d)L^{−d/2}‖h‖_{B_{2L}(x)}, with B_{2L}(x) ⊂ W′.
- The only input is G_{ℤ^d}(0, i) = a_d‖i‖₂^{2−d} + O(‖i‖₂^{−d}) for d ≥ 3 (Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, Theorem B.76(3), p.516), which also gives the bound G_{ℤ^d} ≤ C(d)(1 + |x − y|)^{2−d} used above.

**The bound.** For x ∈ B, a_μ = G_W(Q*ν + ∇s) + h, with h harmonic on the free bonds of W, equal to a on ∂W and to 0 on the pinned bonds.
- The ν-part is at most C(d)L²·L^{−d}·L^{d/2−1}‖F‖_W = C(d)L^{1−d/2}‖F‖_W.
- The s-part is summed by parts on ℤ^d. G_W(x, ·) vanishes off W's free bonds, so there is no boundary term, and −Σ_y s(y)(∇*G_W(x, ·))(y) ≤ C(d)Σ_{2^k≤2L}2^k sup_{A_k}|s| ≤ C(d)L sup_W|s|. The same three steps for s, with ν′ in place of ν, give sup_W|s| ≤ C(d)L^{−d/2}‖s‖_{W′}, W′ the cluster of the 9^d L-cubes around B, which contains B_{2L}(z) for every z ∈ W.
- The h-part is at most C(d)L^{−d/2}(‖a‖_{W′} + ‖G_W(Q*ν + ∇s)‖_{W′}), since B_{2L}(x) ⊂ W for x ∈ B.

Hence, at every layer-1 block B, next to the pinned region or not,

  sup_B|a| ≤ C(d)(L^{−d/2}‖a‖_{W′} + L^{1−d/2}‖F‖_{W′} + L^{1−d/2}‖s‖_{W′}).

At the natural sizes ‖a‖ ≈ L^{d/2−1}|δ| and ‖F‖, ‖s‖ ≈ L^{d/2−2}|δ| per block, the right side is C(d)|δ|/L, so C_{resp,∞} = O(1). More precisely, C_{resp,∞} is at most C(d) times the largest ratio of the three local norms to their natural sizes, and o(L) needs only that ratio to be o(L).

**Consequence.** The pinned region costs nothing at the level of pointwise bounds. Open (R-eval-old) no longer needs LF-2 (a) or the analogue for ΔH_Δσ. It reduces, at the bulk and at the pinned region alike, to the local L² bounds of a, F, and s at their natural sizes up to o(L). In the bulk these are the axial-competitor bounds of (iv), with s at L^{1/2} times its natural size.

## What Remains

1. The local L² bounds of (v) at a block next to the pinned region, for a, F, and s, for sup-norm data. They need the Combes–Thomas localization in block units with an L-uniform rate, with the weight w = e^{−κ dist/L}, |∇w| ≤ (κ/L)w. Two obstacles are found so far (derived).
   - **The contour concentration.** By CMP98 (14), Q = Q_line − D^{bl}K, with Q_line the straight parts and K(u)(B) := L^{−(d+1)}Σ_{x∈B}u(Γ_{y,x}) a block function. By PRT I (1.7) (p.18), the contours Γ_{y,x} run first along e_d from the centre y. So a bond on B's e_d-axis through y lies on about L^d of them and carries the weight about L^{−1} in K, and |K(u)(B)| ≤ C(d)L^{−1/2}‖u‖_B is sharp, against L^{−d/2} for Q_line. PRT II (2.125) (p.245) has the spread weights ≤ 2L^{−d} only because its B is in the axial gauge, where K = 0. The test field that corrects Q(w²u) for u ∈ N(Q) therefore costs L^{(d−1)/2} times the commutator term, and the naive weighted estimate does not close.
   - **The relaxed problem has no gap.** Q(Dμ) = L^{−1}D^{bl}(μ at the centres) (PRT I (1.9)) gives min{‖da‖² : Qa = δ} = min{‖da‖² : Q_line a ∈ δ + Range D^{bl}}, with the same F, and there K drops out. But that affine set contains every gradient, and ‖∇Dξ‖ = ‖Δξ‖ is not bounded below by L^{−1}‖Dξ‖ for slowly varying ξ. So the Landau minimiser of the relaxed problem has no block-scale gap, and Combes–Thomas fails there too.
   - **The contour concentration is harmless for the actual fields (derived).** K(u)(B) is an average of contour sums of length at most dL, so |K(u)(B)| ≤ d·sup_B|u|. For u = a − a₀, with a₀ an explicit local extension of δ, (v) bounds sup_B|u| by C(d)L^{−d/2}(‖u‖_{W′} + L‖du‖_{W′} + L‖D*u‖_{W′}), with the good weight L^{−d/2}. For Qu = 0 one has Q_line u = D^{bl}K(u), so with w_{b′} the weight at b′'s initial block,
     Q(w²u)(b′) = Q_line((w² − w²_{b′})u)(b′) − D^{bl}(w²)(b′)·K(u)(B′) − D^{bl}(K(w²u) − w²K(u))(b′).
     Each term is at most C(d)κw²_{b′}(L^{−d/2}‖u‖_{2B} + sup_{2B}|u|). So the weighted correction costs Cκ times local L² norms at their natural weights. The concentration enters only through sup|u|, which (v) controls.
   - **The joint local problem (derived).** ‖RD*a‖² = min{‖D*a − ζ‖² : ζ ∈ (ΔN₀(Q′))^⊥}, with N₀ the gauge functions in N(Q′) that vanish at the pinned sites. Since ⟨ζ, Δμ⟩ = ⟨Δζ, μ⟩ on the torus, (ΔN₀)^⊥ is the set of ζ with Δζ constant on each block's sites. This is a local linear condition with no condition at the pinned sites. The optimal ζ is (1−R)D*a = s, which vanishes there. The constraint is Q_line a = δ, with no contour terms:
     - The representative satisfies it: a = u_ax + Dμ₀ with Q_line u_ax = δ and Q_line(Dμ₀) = L^{−1}D^{bl}(Q′μ₀) = 0 (top).
     - Its gauge directions are those of the R-gauge: Q_line(Dμ) = 0 if and only if D^{bl}(Q′μ) = 0, that is μ ∈ N(Q′) up to constants, and N₀ with the pinning.
     - It has the same orbits as {Qa = δ}: for Qa = δ, a + Dμ with Q′μ = −L·K(a) satisfies Q_line(a + Dμ) = δ + D^{bl}K(a) − D^{bl}K(a) = δ (Q = Q_line − D^{bl}K), and conversely. So the two sets have the same F's and the same minimum of ‖da‖².
     So (a, s) is the minimiser of ‖da‖² + ‖D*a − ζ‖² over Q_line a = δ and ζ ∈ (ΔN₀)^⊥, a local problem: for fixed a the minimum over ζ is ‖RD*a‖², a + Dμ with μ ∈ N₀ keeps da and shifts RD*a by Δμ, so the minimum is the least ‖da‖², attained exactly at the R-gauge representative with ζ = s. It is nondegenerate: Q_line c = 0 and dc = 0 give c = Dμ with μ ∈ N₀, and ζ = Δμ ∈ ΔN₀ ∩ (ΔN₀)^⊥ = {0}. At da = 0 the form is at least ‖ζ‖², and a has the block gap of N(Q′). This is PBG's setting (QD = D̄Q′ with the line averages, gauge group N(Q′), R the projection onto ΔN(Q′); table #T10.23: Δ_k and F_k are the same for Q and Q̃), so the two obstacles above concern Q only and do not enter here: Q_line has the spread weights ≤ 2L^{−d}, and the relaxed problem is not used.
   - **The weighted estimate in block units (derived in outline).** Rescale by x ↦ x/L, so the blocks are unit cubes and the fine spacing is 1/L. Let w := e^{κ dist}, dist in block units, so |∇w| ≤ κw and w(x) ≤ e^{2κ}w(y) for |x − y| ≤ 2. Test the Euler–Lagrange equations of the joint problem, for the response c := a − a₀ (a₀ a block-local field with Q_line a₀ = δ), with (w²c − t, w²ζ − τ), where t and τ are the corrections back into the constraint sets.
     - **The gap for c (derived, free case).** On the torus ‖dc‖² + ‖D*c‖² = Σ_μ‖∇c_μ‖². Q_line c(b′) for b′ = (B, B+e_μ) is the mean of c_μ over the μ-bonds starting in the brick B ∪ (B+e_μ) with the tent weights (m+1)L^{−(d+1)} and (L−1−m)L^{−(d+1)} (total 1, each at most L^{−d}). So Q_line c = 0 and the Poincaré inequality on each brick, for a probability weight bounded by C/|brick|, give ‖c_μ‖²_{brick} ≤ CL²‖∇c_μ‖²_{brick}, and summed (each bond in two bricks) ‖dc‖² + ‖D*c‖² ≥ γ(d)L^{−2}‖c‖² (G′). For gradients this is PRT II's γ₀′ = π²/L² (p.242 l.42–43), π² in block units.
     - **ζ is smooth at block scale (derived).** For ζ ∈ (ΔN₀)^⊥, Δζ = τ_B is constant on each block, and a bump test (φ_B in B, Σφ_B = 1, |Δφ_B| ≤ CL^{−2−d}) gives |τ_B| = |⟨ζ, Δφ_B⟩| ≤ CL^{−2−d/2}‖ζ‖_B. So ‖Δζ‖ ≤ CL^{−2}‖ζ‖, and on the torus ‖∇Dζ‖ = ‖Δζ‖ ≤ CL^{−2}‖ζ‖. This settles the ∇ζ term below.
     - **The joint gap: open, one lemma.** F(c, ζ) = ‖dc‖² + ‖RD*c‖² + ‖P_ZD*c − ζ‖², with P_Z := 1 − R. With (G′), F ≥ γ′(L^{−2}‖c‖² + ‖ζ‖²) follows from (K′): for c ∈ 𝒞 with D*c ∈ (ΔN₀)^⊥, ‖D*c‖ ≤ C‖dc‖, C uniform in L. (For a general c ∈ 𝒞, subtract Dμ₀ with μ₀ ∈ N₀ and Δμ₀ = RD*c, ‖Dμ₀‖ ≤ CL‖RD*c‖; then ⟨Dμ₀, Dζ⟩ = 0 for ζ ∈ (ΔN₀)^⊥.) Cauchy–Schwarz on ‖ζ‖² = ⟨c, Dζ⟩ with (G′) gives a cross term of the order of the gap, so it does not close by itself.
     - **The exact face-average identity (derived).** For ζ ∈ (ΔN₀)^⊥ let β(b′) := L^d times the mean of ∂_μζ over the L^{d−1} fine bonds crossing the face between B and B+e_μ. The flux of Dζ out of B is Σ_{x∈B}Δζ(x) = L^dτ_B, so D^{bl*}β = L^{d+1}τ exactly, and with D*Q_line* = L^{−1}Q′*D^{bl*}, Q′* = L^{−d}E, r := Dζ − Q_line*β is co-closed. Q_line*β on the μ-bonds of B is the linear interpolation, with the tent weights, of the two face means of ∂_μζ bounding B in direction μ. So r is local and vanishes for constant Dζ. At a crossing bond of the face between B and B+e_μ (relative coordinate L−1 in B) the tent weights are L and 0, so there Q_line*β = L·L^{−(d+1)}β = F_f, the face mean. Hence r has zero net flux through every block face.
     - **(K′) (derived, free case).** Let c ∈ 𝒞 and ζ := D*c ∈ (ΔN₀)^⊥. Then ‖ζ‖² = ⟨c, Dζ⟩ = ⟨c, r⟩, since ⟨c, Q_line*β⟩ = ⟨Q_line c, β⟩ = 0. The co-closed r is d*γ with γ local:
       - Sizes. On the torus ‖∇Dζ‖ = ‖Δζ‖ ≤ CL^{−2}‖ζ‖ and ‖∇²Dζ‖ = ‖∇Δζ‖ = ‖∇Eτ‖, whose square is at most CL^{d−1}Σ_B|τ_B|² ≤ CL^{−5}‖ζ‖² (jumps of the block constants across the faces). On B, r is ∂_μζ minus an interpolation of two face means, so ‖r‖ ≤ C(L‖∇Dζ‖ + L^{3/2}‖∇²Dζ‖) ≤ CL^{−1}‖ζ‖, using the trace inequality ‖f‖²_{face layer} ≤ C(L^{−1}‖f‖²_B + L‖∇f‖²_B). On the face bonds r = ∂_μζ − F_f, so the face Poincaré inequality and the trace inequality give ‖g‖ ≤ CL^{−3/2}‖ζ‖ for g := r on the face bonds.
       - Splitting. Write r = Σ_B ρ_B + Σ_f r_f, with ρ_B := r on the bonds inside B and r_f := r on the crossing bonds of f. D*ρ_B = ±g_f at the face sites of B, with zero total on each face. Let ψ_{B,f} := Dφ in B, with φ harmonic in B and normal flux ∓g_f on f and 0 on B's other faces (Neumann). Then ‖ψ_{B,f}‖² = ⟨g_f, φ − φ̄⟩_f ≤ ‖g_f‖·CL^{1/2}‖ψ_{B,f}‖ by the trace Poincaré inequality on a face of side L, so ‖ψ‖ ≤ CL^{1/2}‖g‖ ≤ CL^{−1}‖ζ‖. Then ρ_B + Σ_fψ_{B,f} and r_f − ψ_{B,f} − ψ_{B′,f} are divergence-free, each supported in at most two blocks, with total norm at most C(‖r‖ + ‖ψ‖) ≤ CL^{−1}‖ζ‖.
       - Local Poincaré lemma for d*. A divergence-free flow ω supported in a box of side at most 2L is d*γ_ω with γ_ω supported in the box and ‖γ_ω‖ ≤ CL‖ω‖, (derived). In chain language ω is a 1-cycle of the box's cubical complex Q = [0, n]^d, n ≤ 2L, and d* is the boundary map ∂₂ on 2-chains. H₁(Q) = 0, so Z₁ = B₁, and on Z₁ the Hodge Laplacian Δ₁ = ∂₂∂₂* + ∂₁*∂₁ equals ∂₂∂₂*. By the Künneth decomposition C_*(Q) = ⊗C_*([0, n]), Δ₁ is a sum of one-dimensional Laplacians. A 1-chain basis element has exactly one edge factor, on which the path's ∂∂* has no kernel (H₁ of a path is 0) and smallest eigenvalue 2 − 2cos(π/(n+1)) ≥ c/n², and the vertex factors contribute ≥ 0. So Δ₁ ≥ cn^{−2} on C₁(Q). Let γ := ∂₂*Δ₁^{−1}ω. Then ∂₂γ = ω, γ is supported in Q, and ‖γ‖² = ⟨Δ₁^{−1}ω, ω⟩ ≤ c^{−1}n²‖ω‖².
       So r = d*γ with ‖γ‖ ≤ CL·CL^{−1}‖ζ‖ = C‖ζ‖, and ‖ζ‖² = ⟨dc, γ⟩ ≤ C‖dc‖‖ζ‖, so ‖ζ‖ ≤ C‖dc‖.
     - **The joint gap (derived, free case).** For c ∈ 𝒞 and ζ ∈ (ΔN₀)^⊥, write c = Dμ₀ + c′ with μ₀ ∈ N₀, Δμ₀ = RD*c. Then c′ ∈ 𝒞, dc′ = dc, D*c′ = P_ZD*c, and (K′) gives ‖P_ZD*c‖ ≤ C‖dc‖. So ‖∇c‖² = ‖dc‖² + ‖RD*c‖² + ‖P_ZD*c‖² ≤ (1 + C²)F(c, ζ), and ‖ζ‖ ≤ ‖ζ − P_ZD*c‖ + ‖P_ZD*c‖ ≤ (1 + C)F^{1/2}. With (G′), F(c, ζ) ≥ γ′(d)(L^{−2}‖c‖² + ‖ζ‖²), uniformly in L. 
     - **The pinned version (partly derived).** Let P be the pinned region, a union of L-cubes of Λ_0, with c = 0 on the bonds with an endpoint in P. Then Q_line c = 0 on every block bond: on the free and crossing ones by the constraint, on those between two pinned blocks trivially. ζ = D*c vanishes at the sites of P. (ΔN₀)^⊥ is the set of ζ with Δζ constant on each free block and no condition at the sites of P, since N₀^⊥ is spanned by the free blocks' indicators and the δ_x, x ∈ P. With β := L^d times the face means of Dζ on every face, D^{bl*}β = L^{d+1}τ̄ holds for every block, τ̄_B the block mean of Δζ. So r is divergence-free off P and has zero flux through every face. In each pinned block B, D*r = Δζ − τ̄_B, of mean zero, is corrected by a Neumann flow ω_B on B's bonds, which are pinned, so ⟨c, ω_B⟩ = 0 and ‖ζ‖² = ⟨c, r + Σω_B⟩ as before. Δζ in P lives on the sites next to ∂P, where it is −Σ_{x∉P, x∼y}ζ(x). So the sizes need ζ at the first free layer, and ∇²ζ, up to ∂P. Since ζ = 0 on P and Δζ is constant on each free block, ζ solves a Dirichlet problem at ∂P, and the free-case sizes hold where ∂P is flat (|ζ| ≤ C|∇ζ| at the first layer, H² up to the boundary). [Open: at the re-entrant edges and corners of P, H² up to the boundary fails, as for the large-field note's v at Λ's re-entrant edges. In block units the sizes use only the face traces of ∇ζ (in ‖r‖, ‖g‖, and ‖ω_B‖), so ζ ∈ H^{3/2+ε} up to ∂P, with a norm bounded by ‖ζ‖ + ‖Δζ‖, suffices in place of H². In the continuum, a re-entrant edge of opening 3π/2 gives the Dirichlet exponent 2/3, hence H^{5/3−ε}. What remains is the discrete version, uniform in L, at every edge and vertex type of a union of L-cubes, including those that touch only along an edge, where ∂P is not Lipschitz. The polyhedral regularity source is to be read, not assumed.]
     - The a-correction is block-local. Q_line c = 0 gives Q_line(w²c)(b′) = Q_line((w² − w²_{b′})c)(b′), at most Cκw²_{b′}‖c‖_{2B} with the spread weights. t is a sum of fixed bump fields, one per block bond with Q_line t_{b′} = e_{b′}, of L-uniform norms in block units (a smooth profile sampled on the 1/L lattice), so t costs O(κ) times the weighted local norms of c.
     - The ζ-correction. τ := R(w²ζ) = Δν, ν ∈ N₀, keeps w²ζ − τ ∈ (ΔN₀)^⊥. Since Rζ = 0, ν solves the normal equation of min‖w²ζ − Δν‖ over N₀, with source P_{N₀}Δ(w²ζ) = P_{N₀}(Δ(w²ζ) − w²Δζ) + P_{N₀}((w² − w²_B)Δζ), since P_{N₀} kills the blockwise constants w²_BΔζ. On each block Δζ = σ_B is constant, and a bump test gives |σ_B| ≤ C‖ζ‖_B in block units. So the source is O(κ) times w² times local norms of ζ and ∇ζ, and ν's weighted bound is a second Combes–Thomas, for P_{N₀}Δ²P_{N₀} on N₀, whose gap is L-uniform by the same Poincaré step and whose constraint (block mean zero) is restored by one bump per block at O(κ) cost.
     - Absorption. Every commutator and correction is O(κ) times the weighted energy, so for κ ≤ κ₀(d) the weighted energy of the response is at most C(d) times the weighted local norm of the source. With the source at one block, the local L² norms of c, dc, and ζ decay as e^{−κ₀ dist}, at their natural sizes. [To check: the ∇ζ term, which the energy controls only through D*a − ζ; and the size of the response in fine units after (v), against the target C_{resp,∞} = o(L).]
   - For s, the axial competitor of (iv) needs a pointwise bound for F, which the pinned region does not give. The route is s = ΔH_Δσ with D^{bl}σ = Q(P_grad b) for any member b of the class, P_grad the gradient projection, and Caccioppoli off-diagonal bounds for its kernel.
2. The regular base (derived in outline). At a G-valued regular base U₀, every step of (v) has a covariant form.
   - Write D_{U₀}*D_{U₀} + D_{U₀}D_{U₀}* = Δ^{par} + K on 𝔤-valued 1-forms. Δ^{par} is the componentwise Laplacian with the parallel transports of U₀ between parallel bonds, and K collects the terms with 1 − Ad U₀(∂p) and the action's [F₀, ·] terms, so |K| ≤ C(d)sup|F₀| locally.
   - The killed random-walk expansion of (−Δ^{par})^{−1} on W converges absolutely, and every transport is an isometry of 𝔤. So ‖G^{par}_W(x, y)‖ ≤ G_W(x, y) (diamagnetic bound).
   - A Δ^{par}-harmonic h has |h(x)| ≤ the average of |h| over the neighbours, so |h| is subharmonic and the mean value step holds. Caccioppoli holds with the covariant gradient.
   - The site Laplacian D_{U₀}*D_{U₀} for s is exactly covariant, with no K. The averages Q(U₀) carry transports of modulus 1, so the weights and test fields of (v) are unchanged in size, and D^{bl*}ν = 0 holds with D^{bl} at the averaged base.
   - The K-term adds G^{par}_W(Ka), at most C(d)L²sup|F₀|·sup_W|a|. Taking the sup over all blocks of the finite region absorbs it for C(d)L²sup|F₀| ≤ ½, which holds for g small, since the regularity conditions bound sup|F₀| per unit plaquette by a quantity that tends to 0 with g (at Λ^{old}, (½ + 2α + O(αε_h))ε_h(L^{k−h}η)², LFR I (1.91), (1.95); see the triage's P ≠ ∅ entry), and L is fixed first. [To check: the plaquette normalisation of this bound against (v)'s fine-lattice units.]
3. The crossing datum at ∂Λ_1 in (v): checked (the factor at b₋ is fixed by the pinned data).

The earlier plan, kept for the bulk constants: C_v, the large-field note's input, and C_Δ, the Δ-minimal interpolant. Both are minimal-norm interpolants of block data on the multi-layer structure of 𝐁_k″(Y₁), at a regular real base. They are pinned off Ω₁, and only field bounds (i′ = 0) are needed, not gradient bounds. The L-dependence of PRT II's constants enters through γ₀′ = π²/L² (PRT II p.242 l.42–43). That is the unit-lattice Poincaré constant for fields with zero averages over L-blocks, and it is π² in block units. Next: L-uniform field bounds in block units, by lattice potential theory, in this order:
- (i) the free single layer;
- (ii) a regular background, by perturbation at block scale;
- (iii) the layer interfaces;
- (iv) the pinning off Ω₁.
