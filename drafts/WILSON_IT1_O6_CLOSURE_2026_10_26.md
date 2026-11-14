# O6 Closure: The Joint Bound at Complex σ_k of the Localised Terms with Domain Not Inside Λ_{k+1}

This note proves that the localised terms of CRE (3.27) and (3.29) whose domain Y is not inside Λ_{k+1} extend analytically to complex σ_k on D(k+1)(iii)'s ω-polydiscs, with the bounds the consumers use (map #MD2.2.6.170-2–#MD2.2.6.170-10; D2.6 closure 2.2 (1′)).
Every σ_k-dependence of the actions passes through the composite field B′ of CRE (3.15), which RG2 §1 treats as a variable field, apart from entire quadratic forms (§2). So the terms extend jointly in (A_k, A) on CRE p.277's margin's domain (§3), which contains the consumers' points (§4).
There the 𝐏^{(k)}-terms obey their printed bounds with the fluctuation factor at most doubled (§5), the bracket terms obey p.277's bound with a factor 2 and the decay rate reduced by ϑ_k → 0 (§5a), and V^{(k)}'s action part obeys a Cauchy estimate (§6). The consumers are the D2.6 closure's 2.2–2.3, 4.2(iii), 4.3, 4.5 and 5.0 (§9).

*Inputs.*
- Bałaban's statements accepted in the map: CRE p.277's 𝐇-decay (#MOMGD.55, #MD2.2.6.143-1), CRE p.277's support bound (D2.6 closure 2.3), CRE p.269's action change (#MD2.2.6.171), CRE p.267's and p.276's transfer of [I]'s bounds to the {Ω_j}-operators, and CRE p.277's margin (#MD2.2.4.74–78, #MOMGD.49), whose entailment is a smallness condition on g_K under q₀ = q₁ > p₀ (SW closure §2).
- Two printed claims beyond these: p.277's K′ bound (§5a(i)) and CRE p.277's margin for the 𝐄_k- and 𝐑_k″-brackets (§5).
- From the map: the analyticity of Ψ_b at frozen θ and V^{(k)}'s Jacobian part (#MD2.2.6.172), the chart-logarithm bound (#MD2.2.6.192), and the slot-value moves (#MD2.2.6.193). From the D2.6 closure: the source term's localisation (2.2 (2)).

*Notation.*
- C₁^{RG2}, C₂, C₃, C₄, B₀, κ₁, a₁, ε₁, ε₂, ε₃, α₂ are RG2's constants (RG2 pp.5–11). C₁^{CRE} is the symbol C₁ printed in CRE (3.43), the same symbol as (2.28)'s C₁. A₀, A₁, B₃, β₀, p₀, L, d are CRE's (pp.246, 255, 265, 267).
- ε_k = g_kA₀(log g_k^{−2})^{p₀} (CRE p.255) and δ_k = (A₁/A₀)ε_k (CRE p.265). r_{ω,k} = g_k^{1/2} is the ω-radius of D(k+1)(iii) (D2.6 closure 2.2 *Complex σ_k*; map #MD2.2.6.168).
- CRE p.276's "(I.6.34)", "(I.6.41)" and "Lemmas 5, 6 [I]" are RG2 (1.34), (1.41) and Lemmas 1, 2: (1.34) is the analyticity space of both lemmas, and (1.41) is the expansion whose domains Y p.276 discusses (as map #MD2.2.5.12 identifies "Sect. 7 [I]" with RG2 Sect. 2).
- *The margin radius.* D2.2(4)(f)'s margin condition is 4B₀e^{16κ_s}(T_Y|B′|_Y + sup|B′|) < min(β,1)α_{1,k}/2 (map #MD2.2.4.68-1, #MD2.2.4.73), with α_{1,k} = g_kC₁(log g_k^{−2})^{q₁} (CRE (2.28)).
  The terms of this note are potentials of the measure and carry no t_Y-deformation (D2.6 closure 2.3 *Size*), so T_Y = 1, and the radius is r_{α,k} := min(β,1)α_{1,k}/(16B₀e^{16κ_s}): by CRE p.277's margin the bracket terms are analytic in the shift for sup|B′| < r_{α,k}.
- *The deformed shift.* The localisation of a bracket term evaluates it at the shift (tζ̃_□ + t_□ζ_□)𝐇_k(σ(Y₀), B′), with |t| ≤ 1 and ζ̃_□ + ζ_□ = 1 (RG1 (3.15)–(3.17), RG2 (1.22)–(1.23)). By RG2 (1.18) on the σ-circles, |𝐇_k(σ, B′)| ≤ 4B₀e^{16κ_s}sup|B′|.
  So the deformed shift is ≤ (1 + |t_□|)4B₀e^{16κ_s}sup|B′|, which is below the margin min(β,1)α_{1,k}/2 = 8B₀e^{16κ_s}r_{α,k} whenever (1 + |t_□|)sup|B′| < 2r_{α,k}.
- *The domains.* RG2 (1.20) gives sup|B′| ≤ C₁^{RG2}g_k sup|B| for g_k|B| < ε₁. Put 𝒫_k^m := {B = (A_k, A) : B(b) ∈ 𝐠^c and g_k|B(b)| < min(r_{α,k}/C₁^{RG2}, ε₁) on every bond b of Ω_{k+1}^{(k)*}}; for g_K small the minimum is the first entry. Put 𝒫_k^{3/4} := {B ∈ 𝒫_k^m : sup|B′| < 3r_{α,k}/4}.
- *The size of 𝐇^{(k)}.* h_k := max(c_He^{−R_k}ε_k, S_H) bounds |𝐇^{(k)}| on S_{k+1}: c_He^{−R_k}ε_k at real backgrounds (CRE p.269 l.44–45: "bounded on the set S_{k+1} by O(1)ε_k exp(−R_k)"), and S_H := C_H(α_{0,k+1} + α_{1,k+1})e^{−R_k} at the complex backgrounds of D(k+1)(iii) (map #MD2.2.6.185-2, #MOMGD.58). S_H ≤ g_k^{3/2}/40 for g_K small (map #MD2.2.6.193).

## What the Objects Are

The step-(k+1) fluctuation field is one field. CRE (3.15) (pp.267–268) integrates one fluctuation field A_k over the bonds of Ω_{k+1}, under χ_k′(Ω_{k+1}). Every term of its action is evaluated at the configuration U_k(exp i[g_kCA_k − hD̃(g_kCA_k)]V^{(k)}), or is a term of 𝐏^{(k)}(g_k, U_{k+1}, A_k), or is the Gaussian form −½⟨A_k, C*Δ^{(k)}CA_k⟩.
CRE (3.25) (p.270) renames the restrictions, "Here A_k denotes the fluctuation field on Ω_{k+1} ∩ Λ_{k+1}^c, and A denotes this field on Λ_{k+1}", and writes the same action as 𝐏^{(k)}(g_k, (A_k, A)) + {…} + V^{(k)}(S_{k+1}, (A_k, A)).
So the pair B := (A_k, A) is the field A_k of (3.15), and the outer part A_k (the project's σ_k) is a variable of the same kind as the integration variable A, entering every term through the same formulas.

*The real support.* On Ω_{k+1} the function χ_k′ gives |A_k′| < O(1)ε_k with A_k′ = g_kA_k (CRE p.267: (3.14), and "We define A_k′ = (1/i)log V_k′, hence |A_k′| < O(1)ε_k also").
By (3.14), |V_k′ − 1| < 2δ_k + (4dL)²(1 + β₀)B₃ε_k, so the O(1) is c₃ := (2A₁/A₀ + (4dL)²(1 + β₀)B₃)(1 + O(ε_k)), the factor 1 + O(ε_k) passing from |V_k′ − 1| to |(1/i)log V_k′|.
After (3.21) the bonds of Ω_{k+1} ∩ Λ_{k+1}^c carry χ^{(k)} (g_k|A_k| < δ_k) off R_{k+1} and χ_k′(S_{k+1}) on R_{k+1} ⊂ S_{k+1}, so g_k|A_k(b)| < c₃ε_k on every bond of Ω_{k+1} ∩ Λ_{k+1}^c. On Λ_{k+1} the field A has g_k|A| < δ_k (D2.6 closure 2.3 (a); map #MD2.4.11.2-1–#MD2.4.11.2-2).

*The composite field.* B′ := g_kCB − hD̃(g_kCB) on the bonds of the unit lattice in Ω_{k+1} (CRE (3.15); RG1 (3.2), p.270; RG2 (1.19), p.6). C and D̃ are the operators "determined by the sequence {Ω_j}" (CRE p.267: "All the applied formulas are the same as in Sect. 2 [I], only the symbols represent different operators, determined by the sequence {Ω_j}").
C is linear (RG1 p.268: "B′ = CB, C is the operator determined by the configuration V^{(k)}"; RG1's B′ there is the linear image CB, not the composite field of RG2 (1.19) called B′ here). h is supported on {b₀(c)}, and D̃ is the analytic solution of a block-local equation (RG1 p.267), so B′ is "a local function of B" (RG2 pp.3–4).
The bound is RG2 (1.20): |B′| ≤ O(1)g_k|B| + 4C₂(O(1)g_k|B|)² ≤ C₁^{RG2}g_k|B| < C₁^{RG2}ε₁ for g_k|B| < ε₁, "where C₁ is an absolute constant".

*The terms.* The action of (3.27) is −⟨A, C*Δ^{(k)}CA_k⟩ + 𝐏^{(k)}(g_k, (A_k, A)) + {…}_{s,t} + tV^{(k)}(S_{k+1}); that of (3.29) is the same with (tA_k, A), the 𝐄_k-bracket only, and no V^{(k)}.
The bracket {…} is (𝐄_k + 𝐑_k″ + 𝐁_k)(U_k(exp iB′V^{(k)})) − (…)(U_{k+1}) + A(g_k^{−2}(·) − g_k^{−2}, U_k(exp iB′V^{(k)})) − A(…, U_{k+1}) (CRE (3.15), p.268, with 𝐑_k′ included into 𝐄_k, p.271).
After the localisation of CRE p.276 these are sums over Y ∈ 𝐃_k of localised terms. The terms with Y ⊂ Λ_{k+1} "satisfy exactly all the conditions of those lemmas", and the terms with Y ⊄ Λ_{k+1} are stated on the space (3.43), Ũ^c_{k+1}(Y, (1+β)α̃₀, (1+β)α̃₁) × {A : supp A ⊂ Y ∩ Λ_{k+1}^{(k)*}, |A| < C₁^{CRE}p₁(g_k)}, which has no A_k variable. The consumers need these terms jointly at complex A_k = σ_k on D(k+1)(iii)'s ω-polydiscs.

*What that forces.* Every localised term depends on the fluctuation field B = (A_k, A) restricted to the interior of Y (RG2 (1.34)–(1.35), p.9: the term "depends on configurations 𝐔, 𝐉, B restricted to the interior of Y"). So a term with Y ⊂ Λ_{k+1} does not depend on A_k, and a term with Y ⊄ Λ_{k+1} depends on A_k restricted to Y ∩ Λ_{k+1}^c.
The A_k-dependence enters these terms only through B′ and the entire Gaussian form, and, for V^{(k)}, through the change of variables of CRE p.269 feeding both. The question is whether the functions of the variable field B′ that RG2 §1 constructs extend analytically when B′ is complex on the bonds of Ω_{k+1} ∩ Λ_{k+1}^c, on which domain, and with which bounds; §1–§3 answer it.

## Derivation

### §1. RG2 §1 Constructs Every Localised Term as an Analytic Function of the Variable Field B′

RG2 p.6, after (1.18): "We have to consider the function B′ yet. Notice that in the preceding considerations B′ was a variable field. The function is given by the formula (1.19)". The preceding considerations are:
- the s-dependent propagators H(s), G̃(s), H₀(s) and the bound (1.11) (p.5);
- the change of variables (1.12) and the fixed point D(H(s), A′), "an analytic function of A′, s(Y₀), bounded by 4C₂ε₂²" on |A′| < ε₂ for 4C₂B₀e^{16κ₁}ε₂ ≤ 1 ((1.13)–(1.14), p.5);
- the fixed point 𝐀₀, "an analytic function of B′, s(Y₀) on the considered domains" for |B′| < ε₃ ((1.15)–(1.16), p.6, under 4C₄B₀²e^{32κ₁}ε₃ ≤ 1 and 2B₀e^{16κ₁}ε₃ ≤ ε₂);
- 𝐇_k(s(Y₀), B′) of (1.17), "an analytic function of s(Y₀), B′" with |𝐇_k| ≤ 4B₀e^{16κ₁}|B′| ((1.18)).

The substitution (1.19) with (1.20) then gives (1.21), |𝐇_k(s(Y₀), B′)| ≤ 4B₀C₁^{RG2}e^{16κ₁}g_k|B|, "if e^{32κ₁}ε₁ is smaller than an absolute constant" (p.7). The Cauchy formula in t_□ on the circle (1.22), of radius 1/|t_□| = 8B₀C₁^{RG2}e^{16κ₁}α₂^{−1}g_k|B|, gives the localised term (1.23) with the bound (1.24), linear in g_k|B| (p.7).
For 𝐏^{(k)}'s terms, p.10: the term (1.38) "is an analytic function of (𝐔,𝐉) in the space 𝐔′^c_{k+1}(T_η, α₀′, α₁′), and of B′ in the domain {B′ : e^{16κ₁}|B′| ≤ a₁ on Y}", with (1.39) and the quadratic-coefficient bound (1.40), "if e^{16κ₁}|B′| ≤ ⅓a₁. Taking B′ as in (1.19) we obtain the above bound with |B′| replaced by C₁ε₁" (pp.10–11).
RG1 p.266 states the same structure for the gauge transformation u_k of the shifted configuration: u_k is an "analytic function of 𝐇_k, hence of B′ for 𝐇_k satisfying a boundedness condition of the form |𝐇_k| < a₁". The brackets' analyticity in the shift is RG1 (3.13)–(3.14) (p.272), for |𝐀|, |P₁𝐀|, |∇^ξ_𝐔𝐀|, |Δ^ξ_𝐔𝐀| < α₂ on X, with RG1 (3.15)–(3.17) (p.273) the Cauchy integral in t_□ at a radius fixed by the norms of δ𝐇_j.
In CRE the corresponding statement for the bracket terms with Y ⊄ Λ_{k+1} is CRE p.277's margin: analyticity in the shift on the g-scaled spaces of (2.28), (2.34)–(2.39), a part of whose width is used for 𝐇_k (p.277), that is, for sup|B′| < r_{α,k} (*Notation*).

In all of RG2 pp.3–11 the integration variable B enters only through (1.19). The analyticity statements and the bounds (1.11)–(1.18), (1.39)–(1.40) and RG1 (3.14) are statements about functions of the field B′ (and of s, t_□, 𝐔, 𝐉) on complex polydiscs in B′ (𝐠^c-valued, p.5: "X is an arbitrary 𝐠^c-valued function"), and the passage to B is the composition with (1.19) under (1.20).
Lemma 2's space (1.34), {B : |B| < ε₁g_k^{−1} on Y}, is the preimage statement in RG2's single-domain setting with absolute α₂: on it (1.20) places B′ in the B′-domains. In CRE's setting the B′-domain of the bracket terms is sup|B′| < r_{α,k} (CRE p.277's margin), and the preimage statement is 𝒫_k^m.
p.8 records that the bounds are linear in the fluctuation field: "Another possibility is to use the expression g_k|B| instead of ε₁. It gives a better bound, but the above is simpler."

### §2. The σ_k-Dependence of the Actions of (3.27) and (3.29) Passes Through B′, Apart from Entire Quadratic Forms

(a) 𝐏^{(k)}. RG1 (2.12) (p.268) lists its terms: Tr log(I − h(δD̃/δB)(g_kCB)), log σ(g_kCB − hD̃(g_kCB)), (1/g_k²)⟨H₁hD̃₃(g_kCB), J⟩, −(1/g_k²)𝐆₃(g_kCB), (1/g_k²)⟨H₁g_kCB, Δ₁H₁hD̃(g_kCB)⟩, −(1/g_k²)⟨H₁hD̃(g_kCB), Δ₁H₁hD̃(g_kCB)⟩, −(1/g_k²)V(H₁(g_kCB − hD̃(g_kCB))).
Each is a function of A′ := g_kCB and of D̃(A′), with D̃ analytic in A′ (RG1 p.267 states the analyticity without a radius; the radius that matters is the composite's, RG2 (1.20) for g_k|B| < ε₁), and B′ = A′ − hD̃(A′) is analytic in A′. On the multi-domain lattice the same formulas hold with the {Ω_j}-operators (CRE p.267). With B = (A_k, A) the whole field of (3.15), A_k enters 𝐏^{(k)}(g_k, (A_k, A)) exactly as A does, through A′ = g_kC(A_k, A).

(b) The brackets. 𝐄_k, 𝐑_k″, 𝐁_k and A(g_k^{−2}(·) − g_k^{−2}, ·) are evaluated at U_k(exp iB′V^{(k)}) (CRE (3.15), p.268), a function of the configuration exp(iB′)V^{(k)} on the unit lattice, hence of B′.
RG1 (2.6), (2.8), (3.3)–(3.4) (pp.266, 270) write them through 𝐇_k(B′): U_k(exp iB′V^{(k)}) = exp(iη𝐇_k(B′))U_{k+1} up to the gauge transformation u_k (RG1 p.265: U_k′^{u_k^{−1}} = exp iη𝐇_k), which the gauge-invariant terms do not see.

(c) The quadratic forms. −⟨A, C*Δ^{(k)}CA_k⟩ is bilinear in (A, A_k), hence entire in A_k; it is the D2.6 closure's source term (2.2 (2), with K = C*Δ_kC through the random-walk expansion; map #MD2.2.6.170: "linear in σ_j, hence entire").
The forms −½⟨A, C*Δ^{(k)}CA⟩ and −½⟨A_k, C*Δ^{(k)}CC^{(k)}(Λ_{k+1})C*Δ^{(k)}CA_k⟩ of (3.25) are A_k-free or A-free. The latter does not occur in (3.27) or (3.29), whose measures carry the A-dependent factors only; it cancels against the term placed in 𝐓^{(k+1)} by (3.23), appears explicitly in the identity (3.28) (p.272, first line), and is entire in A_k.
The full Gaussian form −½⟨A_k, C*Δ^{(k)}CA_k⟩ of (3.15) is part of "the previous action" whose change under the change of variables enters V^{(k)} (p.269: "All terms of the previous action contribute to it"); it is entire in A_k, with the nonlocal kernel K := C*Δ^{(k)}C, and is treated in (d) and §6.

(d) V^{(k)}(S_{k+1}, A_k, 𝐇^{(k)}). CRE p.269: for b ∈ S_{k+1}^{(k)*} the variable A_k(b) is changed by (1.22) with 𝐇^{(k)}(b) in place of 𝐇_{1,Ax}(b), the cutoff g(A_k′(b)) kept on (R_{k+1}^{∼2} ∩ S_{k+1})^{(k)*} and replaced by 1 elsewhere, and "The action is changed by terms corresponding to (1.24), and by terms obtained by the first order expansion of the action with respect to the perturbative parts of the changes of variables."
Let Ψ_b be the change of variables at frozen cutoff value θ_b: Ψ_b(σ) = (1/ig_k)log(exp(ig_kσ(b))exp(−iθ_b𝐇^{(k)}(b))), analytic in σ for g_k|σ| small (map #MD2.2.6.172). The action S(B) of (a)–(c) at the old field is S((Ψ(σ_k), A)) = S((σ_k, A)) + ∫₀¹⟨(δS/δA_k)(B_u), Ψ(σ_k) − σ_k⟩du, B_u := (σ_k + u(Ψ(σ_k) − σ_k), A).
The integral is V^{(k)}'s action part, and (1.24)'s Jacobian terms are its other part. The action part is a directional derivative of S in the A_k-direction at the points B_u, so its σ_k-dependence is through B′ at B_u for the terms of (a)–(b).
For the Gaussian form of (c) it is −∫₀¹⟨KB_u, δ⟩du = −⟨K(σ_k, A) + ½Kδ, δ⟩, δ := Ψ(σ_k) − σ_k, supported on S_{k+1}^{(k)*}, entire in (σ_k, A) and analytic in σ_k through δ. The Jacobian part is bond-local and analytic in σ_k at frozen θ (map #MD2.2.6.172).

So the σ_k-dependence of every term of the actions of (3.27) and (3.29) is through B′ at B = (σ_k, A), (tσ_k, A) or B_u, through the entire forms of (c), directly or through δ, or through the Jacobian part of V^{(k)}. This is CRE p.276's "The action in (3.29) differs only by the additional dependence on the field tA_k, but this was already taken into account in the above considerations": at the level of the variable field B′ there is nothing to add.

### §3. The Analytic Extension in (A_k, A) on CRE p.277's Margin's Domain

On 𝒫_k^m the map B ↦ A′ = g_kCB is linear and bounded by O(1)g_k|B| (the first term of (1.20)), and the composite B′ = A′ − hD̃(A′) is analytic and satisfies (1.20): |B′(b)| ≤ C₁^{RG2}g_k sup_Y|B| < r_{α,k} on every bond of Y.
By §1 every localised term T(Y; 𝐔, 𝐉, B′) is analytic in B′ on the B′-domain stated for it:
- for 𝐏^{(k)}'s terms, {e^{16κ₁}|B′| ≤ a₁ on Y} (RG2 p.10; absolute, with no α₂-condition);
- for the bracket terms 𝐄_k, 𝐑_k″, 𝐁_k, A(·), sup|B′| < r_{α,k}, on which the shift exp(iη𝐇_k(B′)) keeps the configuration inside the g-scaled analyticity spaces of CRE (2.28), (2.34)–(2.39) (CRE p.277's margin; *Notation*).

RG2's own radius ε₁/g_k for the brackets (p.7's 4B₀C₁^{RG2}e^{16κ₁}ε₁ ≤ ¼α₂, with RG1's absolute α₂) is the single-domain statement and does not apply to CRE's boundary terms, whose spaces are g-scaled; the operative radius is r_{α,k} ≪ ε₁.
The composition T(Y; 𝐔, 𝐉, B′(B)) is therefore analytic in B on 𝒫_k^m|_Y, jointly in A_k and A, uniformly over (𝐔, 𝐉) in the term's analyticity space.
The Cauchy integrals in s(Δ) and t_□ (RG2 (1.23), (1.38); RG1 (3.15)) preserve this: their integrands are analytic in (s, t_□, B) jointly, the s-circles do not depend on B, and the t_□-radius depends on B only through sup|B| (RG2 (1.22); on 𝒫_k^{3/4} the radius 4/3, §5). Since the integrand is analytic in t_□ on the annulus between any two admissible radii, the integral is locally independent of the radius, hence analytic in B.
Where [I]'s single-domain operators are replaced by CRE's {Ω_j}-operators, CRE p.267 and p.276 carry §1's statements over ("Thus, for terms connected with such a cube □, we obtain all the formulas and bounds of Sects. 3, 4 [I] with η replaced by L^{−n}"; "The same remarks apply to the expression 𝐏^{(k)}, and we obtain Lemmas 5, 6 [I] with the corresponding changes"). These concern the operators, not the variable B, so the composition argument is unchanged.

So every term of the expansion of the actions of (3.27) and (3.29) with Y ⊄ Λ_{k+1} extends to a function analytic in B = (A_k, A) on Ũ^c_{k+1}(Y, (1+β)α̃₀, (1+β)α̃₁) × 𝒫_k^m|_Y, depending on B restricted to Y.
These terms are 𝐏^{(k)} with the 𝐄_k-bracket (RG2 (1.41)), the 𝐑_k″-bracket (CRE p.276: "treated in exactly the same way as 𝐄_k"), the (I.3.6)–(3.7)-localised 𝐁_k-terms (p.276), A(·)'s terms (p.277: "treated as above"), and the action part of V^{(k)} (§6). (3.43)'s A-factor is Bałaban's analyticity space in the integration field; §7 relates it to 𝒫_k^m.

### §4. The Consumers' Points Lie in 𝒫_k^m

The consumers (D2.6 closure 2.2–2.3, 4.3, 5.0) evaluate at σ_k = σ_{k,0} + ζ with σ_{k,0} real in the support and |ζ(b)| < r_{ω,k} = g_k^{1/2} per bond, at tσ_k with t ∈ [0, 1] for (3.29), and with A real on the support.
The slot-value moves |Δσ_j| ≤ 10S_H/g_j ≤ r_{ω,j}/4 (map #MD2.2.6.193, #MD2.2.6.196) are moves within D(k+1)(iii)'s ω-polydisc, so they lie inside ζ's polydisc and are not added to it. The field fed to B′ is B = (A_k′, A) with A_k′ = Ψ(σ_k) on S_{k+1}^{(k)*} and A_k′ = σ_k elsewhere (§2(d)). Bounds per bond:
- g_k|σ_{k,0}(b)| < c₃ε_k off S_{k+1}^{(k)*} (*The real support*), and < c₃ε_k + 3h_k on S_{k+1}^{(k)*}. On S_{k+1}^{(k)*} the support of the new variable is the old support moved by the chart bound of the third item; CRE p.269 l.49–50 states that the changes of variables "transform the function χ_k′(S_{k+1}) into the same function, but with V^{(k)} replaced by V^{(k)}_{Λ_{k+1}^c∩Λ_k}", with (3.18)'s "similar bounds" (l.38), and the derived value c₃ε_k + 3h_k is used as an over-bound.
- g_k|ζ(b)| < g_k^{3/2}.
- g_k|Ψ_b(σ_k) − σ_k(b)| ≤ (2 + O(ε_k))|𝐇^{(k)}(b)| ≤ 3h_k, where 2 + O(ε_k) bounds the derivative of the chart logarithm X ↦ (1/i)log(e^{iy}e^{−iX}) for |y| + |X| ≤ c₂ (map #MD2.2.6.192), the segment from X = 0 to X = θ_b𝐇^{(k)}(b) lying in that ball.
- g_k|A(b)| < δ_k = (A₁/A₀)ε_k ≤ c₃ε_k/2.

So g_k sup_b|B(b)| ≤ ε_k^♯ := c₃ε_k + g_k^{3/2} + 6h_k, and the points B_u of §2(d) and tσ_k lie in the same ball. Under (C2), g_k^{3/2} + 7.5h_k ≤ c₃ε_k, this gives ε_k^♯ ≤ 2c₃ε_k.
By (C3), C₁^{RG2}ε_k^♯ < r_{α,k}/2, every consumers' point lies in 𝒫_k^m, with sup|B′| < r_{α,k}/2. Under (C2), (C3) follows from 64B₀e^{16κ_s}C₁^{RG2}c₃ε_k < min(β,1)α_{1,k}, which is a smallness condition on g_K, since ε_k/α_{1,k} = (A₀/C₁)(log g_k^{−2})^{p₀−q₁} → 0 under q₁ > p₀.
The map's membership statement (#MD2.2.6.173: |B′| ≤ 2C₁^{RG2}O(1)ε_k for |σ_j − σ_{j,0}| < r_{ω,j}) is the case of this computation with ζ alone.

### §5. The Joint Bound on CRE p.277's Margin's Domain

*𝐏^{(k)}'s terms.* Every printed bound of a localised term is linear in the fluctuation field. (1.24) carries g_k|B|; (1.40) carries |B′| ≤ C₁^{RG2}g_k|B|; Lemma 2's (1.43) carries ε₁ as the stand-in for C₁^{RG2}g_k|B| ("Taking B′ as in (1.19) we obtain the above bound with |B′| replaced by C₁ε₁", p.11; p.8's "better bound"); (1.36) descends from (1.29), where ε₁ stands for g_k|B| (p.8).
For 𝐏^{(k)}'s terms the B′-domain is absolute ({e^{16κ₁}|B′| ≤ a₁}, RG2 p.10), and the printed bounds (1.36), (1.40), (1.43) are sup bounds of analytic functions on it with the fluctuation factor as a parameter. So they hold at every point of 𝒫_k^m with C₁^{RG2}g_k sup_Y|B| as the fluctuation factor; at the consumers' points this factor is ε_k′ := C₁^{RG2}ε_k^♯ ≤ 2C₁^{RG2}c₃ε_k.

*The bracket terms.* For the bracket terms this transfer is not available: the printed linearity of RG2 (1.24) comes from the t_□-radius (1.22), built on the absolute width α₂, which CRE's g-scaled spaces do not have (§3), and p.277's "(2.42), but with the additional factor O(ε_k)" is a statement on the support, not a sup bound on the margin's domain. The bracket terms are bounded instead by the Schwarz lemma.
For a term X of 𝐄_k, 𝐑_k″ or 𝐁_k, put F_X(B′) := 𝐓(X, exp(iη𝐇_k(B′))U_{k+1}) − 𝐓(X, U_{k+1}), with 𝐓 the term's function. F_X vanishes at B′ = 0, since 𝐇_k(0) = 0 by (1.18).
On {sup|B′| < r_{α,k}} the shifted configuration stays in the g-scaled space of CRE (2.28), (2.34)–(2.39) (CRE p.277's margin), where |F_X| ≤ M_X := 2·(the term's inductive bound there: (2.26)–(2.40) for 𝐄_k and 𝐑_k″, (2.42) for 𝐁_k, with its decay e^{−κd_j(X)}). The Schwarz lemma for λ ↦ F_X(λB′/sup|B′|) gives |F_X(B′)| ≤ M_X·sup|B′|/r_{α,k}.
For the 𝐄_k- and 𝐑_k″-brackets CRE p.277's margin is carried by CRE p.276 l.2–13 and l.38–39 from RG1 Sect. 3 to the {Ω_j}-scales: RG1 prints that the shifted 𝐄-term (3.13) is analytic for |𝐀|, |P₁𝐀|, |∇𝐀|, |Δ𝐀| < α₂, "α₂, depending on α₀ and on some absolute constants", and "satisfies the inequality (1.18)" there (RG1 p.272 l.30–44); CRE p.276 gives "all the formulas and bounds of Sects. 3, 4 [I] with η replaced by L^{−n}", and the g-scaled form of α₂ is r_{α,k} (map #MD2.2.4.73–78). For 𝐁_k it is printed on p.277.

*The localisation.* The localisation into domains Y ⊇ X follows RG1 (3.15)–(3.17) and RG2 (1.22)–(1.23), with the margin's domain in place of RG2's α₂-ball: per term one Cauchy derivative ∮dt_□/t_□² in the interpolation parameter (RG2 (1.23)), and the per-cube decay from the σ(Δ)-circles of radius e^{κ₁}, which do not depend on B (RG2 p.7), at the cost B₀e^{16κ_s} already in r_{α,k}.
On 𝒫_k^{3/4} take |t_□| = 4/3. Since (1 + 4/3)·(3/4) = 7/4 < 2, the deformed shift is ≤ 7B₀e^{16κ_s}r_{α,k} = (7/16)min(β,1)α_{1,k}, inside the margin (*Notation*); the t_□-derivative costs the factor 3/4, no factor per added cube depends on the radius, and no entropy condition beyond RG2's "κ sufficiently large" enters.
So the localised term T(Y) is analytic on 𝒫_k^{3/4}, vanishes at B′ = 0, and is bounded there by M_Y^{loc} := c_σM_{X(Y)}e^{−κ′d(Y)}, with c_σ and κ′ from RG2's σ-circle localisation, independent of g. The Schwarz lemma on {sup_Y|B′| < 3r_{α,k}/4}, applied to λ ↦ T(Y)(λB/sup|B′|), gives |T(Y)(B)| ≤ M_Y^{loc}·4sup|B′|/(3r_{α,k}).
For A(·)'s terms the same holds with M_X as in §5a(ii). This bound holds on all of 𝒫_k^{3/4}, which contains the consumers' points by (C3). Its coefficient is of order ε_k/α_{1,k} = (A₀/C₁)(log g_k^{−2})^{p₀−q₁}, which tends to 0 with g_k under q₁ > p₀, but not as a power of g_k; §5a recovers p.277's O(ε_k) at the consumers' points.

Explicitly, at the consumers' points, with Bałaban's constants:
- 𝐕_k″(Y, 𝐔, 𝐉, B) of (1.42): |𝐕_k″| ≤ E₀ε_k′C₁M^qe^{C₂κ₁}exp(−(1 − 2δ)κd_k(Y)) ((1.36) with ε₁ → ε_k′);
- Q(Y, B, b, b′) of (1.42): |Q| ≤ C₃ε_k′M⁴e^{C₂κ₁}exp(−⅛(κ₁ − 1)d_k(Y) − ½(κ₁ − 1)M^{−4}|Y|) ((1.43) with ε₁ → ε_k′), the quadratic form ½⟨Q(Y, B), B, B⟩ being analytic in B as the second-order Taylor remainder in B′ of (1.38) composed with (1.19);
- the 𝐄_k-, 𝐑_k″-, 𝐁_k- and A(·)-terms: M_Y^{loc}·4C₁^{RG2}ε_k^♯/(3r_{α,k}), with, for a cube □ on the layer Ω_n∖Ω_{n+1}, CRE p.276's η → L^{−n} in the distance and regularity factors; for 𝐁_k, M_X = 2B₀exp(−κd_j(X)).

For 𝐏^{(k)}'s terms the ratio of the complex to the real bound is ≤ ε_k^♯/(c₃ε_k) ≤ 2 under (C2), for the fluctuation factor and the coefficients Q, term by term and uniformly over the ω-polydiscs, the slot moves and t ∈ [0, 1].
The value of the quadratic form ½⟨Q(Y,B),B,B⟩ carries in addition the two complex arguments, each ≤ ε_k^♯/g_k ≤ 2 times its real bound, so its value is ≤ 8 times the real one (§8 computes it with (ε_k^♯/g_k)²).

### §5a. The Bracket Terms at the Consumers' Points Keep p.277's O(ε_k)

The bound of §5 is a sup bound over 𝒫_k^{3/4} and does not use that the consumers' points lie within g_k^{3/2} + 6h_k of the real support, where p.277's bound holds. A two-constants estimate uses this and returns p.277's coefficient up to a factor 2.

*Setting.* Fix a bracket term T(Y) (an 𝐄_k-, 𝐑_k″-, 𝐁_k- or A(·)-term with Y ⊄ Λ_{k+1}, after the Y-localisation) and the background (𝐔, 𝐉) in its analyticity space. Measure B by ‖B‖ := g_k sup_{b∈Y}|B(b)|; T(Y) depends on B on Y only (*What that forces*). Put a := c₃ε_k, R := r_{α,k}/C₁^{RG2}, R′ := 2R/3 and τ_k := (g_k^{3/2} + 6h_k)/(c₃ε_k).

- (i) *The real bound (p.277's K′ bound).* On the real set K′ := {B real : ‖B‖ ≤ a, g_k sup_{Y∩Λ_{k+1}}|A| ≤ δ_k}, |T(Y)| ≤ m_Y, where m_Y is p.277's bound, O(ε_k) times T(Y)'s decay factor. The print fixes the domain of this estimate.
  p.277 states "The terms of the expansion can be estimated as in (2.42), but with the additional factor O(ε_k) arising from the bound of the fluctuation field" (l.8–9). (2.42) is a sup bound over a space: the localised term "has an extension to an analytic function on the space Ũ_j^c(X, α̃₀, α̃₁)" and "satisfies the bound" (2.42) (p.261 l.58–64).
  The bound of the fluctuation field is printed as a size bound, "This implies that |V_k′ − 1| < O(1)ε_k on Ω_{k+1} … We define A_k′ = (1/i)log V_k′, hence |A_k′| < O(1)ε_k also" (p.267 l.27–28), with the O(1) equal to c₃ (*The real support*).
  With A on Λ_{k+1} at its cutoff g_k|A| < δ_k (the small-field functions of (3.16) whose product on Λ_{k+1} is χ^{(k)}(Λ_{k+1}), p.268 l.18, p.269 l.17–18; map #MD2.4.11.2-2; D2.6 closure 2.3 (a)), the set on which the fluctuation field obeys these printed bounds is K′. CRE p.277's support bound (D2.6 closure 2.3) is this estimate on the support of the integration, which lies in K′. K′ is convex and symmetric about 0.
- (ii) *The crude bound.* On D′ := {B : ‖B‖ < R′}, sup|B′| ≤ C₁^{RG2}‖B‖ < 2r_{α,k}/3, so D′ ⊂ 𝒫_k^{3/4}, and T(Y) is analytic there with |T(Y)| ≤ M_Y^{loc} ≤ c_σM̄_Y, M̄_Y := max_{X⊂Y}M_X (§5). For the 𝐄_k-, 𝐑_k″- and 𝐁_k-terms M̄_Y ≤ M̄, where M̄ is twice the largest prefactor of the inductive bounds, independent of k and g.
  A(·)'s terms are entire, with plaquette coefficients D_k := g_k^{−2}(·) − g_k^{−2} supported in Z_k (p.277). D_k is not bounded uniformly in k; its growth is confined to the layers where 𝐇_k is small (**p.277's A(·)-suppression**), as follows.
  CRE (2.24), 1/g_{i−1}²(x) = 1/g_i²(x) + β_i(g_{i−1})φ_i(x), with the constants' equation 1/g_{i−1}² = 1/g_i² + β_i(g_{i−1}) ((I.0.20)), gives D_i(x) = D_{i−1}(x) + β_i(g_{i−1})(1 − φ_i(x)), so D_k(x) = D_j(x) + Σ_{j<i≤k}β_i(g_{i−1})(1 − φ_i(x)) for every j < k.
  p.277 prints "supp(g_k^{−2}(·) − g_k^{−2}) ⊂ Z_k", Z_k = Λ_k^c (p.264), a statement for general k; at step j it says D_j = 0 on Λ_j. Let x lie on the layer Ω_n∖Ω_{n+1}, n ≥ 1. Then x ∈ Ω_n ⊂ Λ_{n−1} by the nesting (2.1) (p.254), so D_{n−1}(x) = 0 (for x outside Ω₁, D₀ = 0 since g₀ is constant).
  Hence |D_k(x)| ≤ b̄c_φ(k − n + 1), with b̄ := sup_i|β_i(g_{i−1})| and c_φ := sup_i sup|1 − φ_i| (φ_i ∈ C_0^∞(Λ_i), φ_i = 1 on Λ_i^{∼−1}, p.259; c_φ = 1 for cutoffs with values in [0, 1]). On x ∈ Ω_{k+1} ⊂ Λ_k, D_k(x) = 0.
  On the same layer CRE p.277's 𝐇-decay bounds the shift η𝐇_k(B′), in the units of |A″|, by O(1)(Lθ)^{k−n} times its Ω_k-size (map #MD2.2.6.143-1, θ = e^{−δ₀RM₁/32}), and the same holds for the deformed shifts at which the localisation evaluates M_X.
  With Lθ ≤ 1/2, which holds for g_K small (D2.6 closure 4.2), sup_x(|D_k(x)|·|η𝐇_k(B′)(x)|) ≤ O(1)b̄c_φ·sup_{m≥0}(m + 1)(Lθ)^m·sup_{Ω_k}|η𝐇_k(B′)| = O(1)·sup_{Ω_k}|η𝐇_k(B′)|, uniformly in k and g.
  This is p.277's "the large values of the function g_k^{−2}(·) − g_k^{−2} are suppressed by the exponential decay of 𝐇_k" made quantitative. It uses p.277's support statement at every step; p.259's weaker sentence ("Thus g_j²(x) = g_j² on the last domain", Λ_j^{∼−1}) would need Ω_n ⊂ Λ_{n−1}^{∼−1}, which the printed separations do not give.
  So the change of each plaquette function under the shift, times its coefficient, is O(1) on D′ (R′ ≤ r_{α,k} → 0), and M_X ≤ M̄c_A^{|X|} for A(·)'s terms, with c_A independent of k and g. Put c_A := 1 for the other bracket terms. Then |T(Y)| ≤ M_Y := c_σM̄c_A^{|Y|} on D′ for every bracket term.
- (iii) *The points.* Every consumers' point P (§4) has ‖Re P‖ ≤ (1 + τ_k)a and ‖Im P‖ ≤ τ_ka. The imaginary part comes from ζ (g_k|ζ| < g_k^{3/2}) and from Ψ_b(σ_k) − σ_k (≤ 3h_k), and the real part is bounded by ε_k^♯ = (1 + τ_k)a. The points B_u of §2(d) and the points tσ_k of (3.29) satisfy the same bounds.

*Step 1: the real points of (1+2s)K′, 0 < s ≤ 1/12.* Here (1+2s)K′ := {B real : ‖B‖ ≤ (1+2s)a, g_k sup_{Y∩Λ_{k+1}}|A| ≤ δ_k}. For x in it with ‖x‖ > a, put φ(z) := T(Y)(z·x/‖x‖) for |z| < R′. Then φ is analytic and |φ| ≤ M_Y, and |φ| ≤ m_Y on [−a, a] by (i): for |z| ≤ a < ‖x‖ the A-part of z·x/‖x‖ is at most x's, so the segment lies in K′.
The Joukowski map z = (a/2)(w + 1/w) carries the annulus 1 < |w| < ρ₁, ρ₁ := R′/a, into {|z| < R′}∖[−a, a] (|z| ≤ (a/2)(|w| + 1/|w|) < R′ for |w| < ρ₁), and the unit circle onto [−a, a].
Hadamard's three-circles theorem (log max_{|w|=r}|ψ| is a convex function of log r; Conway, Functions of One Complex Variable I, §VI.3), applied to ψ(w) := φ(z(w)) on 1 ≤ |w| ≤ ρ < ρ₁ and then ρ → ρ₁, gives log|φ(z(w))| ≤ log m_Y + (log|w|/log ρ₁)log(M_Y/m_Y).
The real point z = ‖x‖ = (1+u)a, u ≤ 2s, has log|w| = arccosh(1+u) ≤ (2u)^{1/2}, since cosh((2u)^{1/2}) ≥ 1 + u. So |T(Y)| ≤ m_Y⁺ := m_Y(M_Y/m_Y)^{2s^{1/2}/log ρ₁} on (1+2s)K′ (where the exponent exceeds 1 the bound is ≥ M_Y and holds trivially).

*Step 2: the consumers' points.* For P with (iii), put x := Re P and, if Im P ≠ 0, u := Im P/‖Im P‖, a real direction with ‖u‖ = 1 (if Im P = 0, Step 1 applies). Put φ(z) := T(Y)(x + zu) for |z| < R′ − ‖x‖, and s := τ_k^{2/3}.
Since ‖x‖ ≤ (1+τ_k)a ≤ (1+s)a, the real segment {x + tu : |t| ≤ sa} lies in (1+2s)K′ (Im P has no A-component, so the segment keeps x's A-part, real with g_k|A| < δ_k), where |φ| ≤ m_Y⁺ by Step 1.
The Joukowski map at scale sa, with ρ₂ := (R′ − (1+s)a)/(sa), and the three-circles theorem give |T(Y)(P)| = |φ(i‖Im P‖)| ≤ m_Y⁺(M_Y/m_Y⁺)^{arcsinh(v)/log ρ₂}, v := ‖Im P‖/(sa) ≤ τ_k/s = τ_k^{1/3}, since z = iv·sa corresponds to |w| = v + (1 + v²)^{1/2} = e^{arcsinh v}. With arcsinh v ≤ v and m_Y ≤ m_Y⁺ ≤ M_Y,

  |T(Y)(P)| ≤ m_Y·(M_Y/m_Y)^{ω_k},  ω_k := 2τ_k^{1/3}/log ρ₁ + τ_k^{1/3}/log ρ₂.

*Constants.* (C3) gives ε_k^♯ < R/2, so R′ = 2R/3 > (4/3)(1+τ_k)a: ρ₁ > 4/3, and ρ₂ > ((4/3)(1+τ_k) − 1 − s)/s ≥ 1/(4s) ≥ 3 for s ≤ 1/12. Hence ω_k ≤ (2/log(4/3) + 1/log 3)τ_k^{1/3} ≤ 8τ_k^{1/3}.
Write m_Y = C_Bε_ke^{−κ_Yd(Y)}, with C_B the O(1) of p.277 times (2.42)'s B₀ or 𝐄_k's prefactor E₀, d the term's distance function and κ_Y its rate. Every Y has |Y| ≤ c′(d(Y) + 1) cubes (RG2 (1.28), used on a cube of the layer Ω_n∖Ω_{n+1} with p.276's η → L^{−n}, p.276 l.18–24). So log(M_Y/m_Y) ≤ log(c_σM̄/(C_Bε_k)) + c_*(d(Y) + 1), c_* := κ_Y + c′log c_A.
The same estimate with τ_k replaced by 2τ_k (and s := (2τ_k)^{2/3}) holds on the larger set of points with ‖Re P‖ ≤ (1 + 2τ_k)a, ‖Im P‖ ≤ 2τ_ka, no A-component in Im P and g_k|A| ≤ δ_k for the real A-part on Y ∩ Λ_{k+1}, which §6 uses. Under

- (C7) 2τ_k ≤ 12^{−3/2} and 8(2τ_k)^{1/3}(log(c_σM̄/(C_Bε_k)) + c_*) ≤ log 2, a smallness condition on g_K (τ_k = O(g_k^{1/2}(log g_k^{−2})^{−p₀}), log(1/ε_k) = O(log g_k^{−2}), and M̄, c_σ, c_* do not depend on k or g),

every bracket term obeys, at every consumers' point and at every point of the larger set,

  |T(Y)(P)| ≤ 2m_Y·e^{ϑ_kd(Y)},  ϑ_k := 8(2τ_k)^{1/3}c_* → 0.

This is p.277's bound, O(ε_k) as printed, with the factor 2 and the decay rate κ_Y reduced by ϑ_k, the form the 𝐏^{(k)}-terms have (§5, ratio ≤ 2). ϑ_k is absorbed in the bracket terms' own summations, which have strict margins: (2.42)'s κ, used as exp(−(κ − 1)d_j(X)) (CRE p.263), and 𝐄_k's inductive rate, with κ_Y − ϑ_k in place of κ_Y for g_K small.
So the consumers receive at §4's points the bracket terms with p.277's coefficient and run as at real σ_k with the factor 2.

### §6. The Action Part of V^{(k)}

By §2(d) the action part of V^{(k)} on a localisation domain Y is V_act(Y) = ∫₀¹⟨(δT(Y)/δA_k)(B_u), Ψ(σ_k) − σ_k⟩du, summed over the localised terms T(Y) of §3. It is nonzero only when Y meets S_{k+1}, the support of Ψ − id, which is CRE p.269's "additional localization in S_{k+1}" and p.277's "at least one localization in S_{k+1}".
It is analytic in σ_k on the consumers' domain, as an integral of directional derivatives of the analytic functions of §3 at points B_u ∈ 𝒫_k^m (§4). Its bound is a Cauchy estimate in the direction δ := Ψ(σ_k) − σ_k: for F analytic on {B_u + zδ : |z| ≤ ρ/sup|δ|}, |D_δF(B_u)| ≤ sup|F|·sup|δ|/ρ.

*𝐏^{(k)}'s terms.* Take ρ := r_{α,k}/(2C₁^{RG2}g_k), half the margin radius in the fluctuation field. Under (C3) the closed disc lies in the open domain 𝒫_k^m, so sup|F| is the §5 bound of T(Y) with the fluctuation factor ε_k′ replaced by r_{α,k}, and sup|δ| ≤ 3h_k/g_k (§4).
Since the §5 bound is linear in the fluctuation factor, |V_act(Y)| ≤ [the §5 bound of T(Y) per unit fluctuation factor]·r_{α,k}·(3h_k/g_k)·(2C₁^{RG2}g_k/r_{α,k}) = [the §5 bound of T(Y) per unit fluctuation factor]·6C₁^{RG2}h_k.
This is p.269's "bounded … by O(1)ε_kexp(−R_k), hence by any positive power of g_k" with the constants named, and it is below the §5 bound of T(Y) itself (fluctuation factor ε_k′ ≥ C₁^{RG2}c₃ε_k), since 6h_k ≤ c₃ε_k by (C2).

*The bracket terms.* Their Cauchy radius is λ with λ·g_k sup|δ| = g_k^{3/2}. The disc's points B_u + zδ, |z| ≤ λ, have ‖Im‖ ≤ 2g_k^{3/2} + 3h_k ≤ 2τ_ka and ‖Re‖ ≤ ε_k^♯ + g_k^{3/2} ≤ (1 + 2τ_k)a, and δ has no A-component (Ψ − id is supported on S_{k+1}, disjoint from Λ_{k+1}). So they lie in the larger set of §5a, where |T(Y)| ≤ 2m_Ye^{ϑ_kd(Y)}.
Hence |D_δT(Y)(B_u)| ≤ 2m_Ye^{ϑ_kd(Y)}·g_k sup|δ|/g_k^{3/2} ≤ 2m_Ye^{ϑ_kd(Y)}·3h_k/g_k^{3/2}, and the bracket part of V_act(Y) is ≤ 6m_Ye^{ϑ_kd(Y)}h_k/g_k^{3/2}. This is below the term's own bound 2m_Ye^{ϑ_kd(Y)} by (C4′), 3h_k ≤ g_k^{3/2}.

*The Gaussian-form part* of V_act (§2(d)) is −⟨K(σ_k, A) + ½Kδ, δ⟩ with K = C*Δ^{(k)}C. Per bond b of S_{k+1}^{(k)*} it is bounded by Σ_{b′}|K(b, b′)|·(ε_k^♯/g_k + 3h_k/(2g_k))·(3h_k/g_k) ≤ ‖K‖_{decay}·(2c₃ε_k/g_k)·(3h_k/g_k) under (C2), with ‖K‖_{decay} the row-sum norm of K's random-walk expansion (D2.6 closure 2.2 (2), where the same kernel localises the source term).
The sum over b′ ∈ Λ_{k+1} is exponentially small, since S_{k+1} is separated from Λ_{k+1} by a layer of LMR_{k+1}-cubes ((3.20)): the part coupling to A has size ≤ ‖K‖_{decay}e^{−cLMR_{k+1}}(2c₃ε_k/g_k)(3h_k/g_k). Its ratio to the real-case value (δ at the real point, |σ_k| ≤ c₃ε_k/g_k) is ≤ 2 by the same arithmetic.

*The Jacobian part* is map #MD2.2.6.172's: bond-local, analytic in σ_k at frozen θ, of size O(|𝐇^{(k)}|).

### §7. (3.43)'s A-Domain and What It Does to A_k

CRE p.276 calls (3.43) the analyticity space of the terms with Y ⊄ Λ_{k+1}. Its A-radius C₁^{CRE}p₁(g_k) is not used: p₁ occurs only in (3.43) and is defined nowhere (table #T11.12-2).
The terms are taken on 𝒫_k^m, which contains the support |A| < δ_k/g_k = (A₁/A₀)p₀(g_k) (D2.6 closure 2.3 (a)) by §4, and their bounds on the support are CRE p.277's support bound (D2.6 closure 2.3 (c)).
So A_k is restricted to the margin's domain, g_k sup|A_k| < r_{α,k}/C₁^{RG2} = O((log g_k^{−2})^{q₁}), which contains the consumers' points (the support, the ω-radius g_k^{1/2}, the slot moves, and the change of variables) by §4.

### §8. Count Check

Per scale: count × size × weight. Fix a cube Δ of Ω_{k+1}∖Λ_{k+1} (an M-cube of π_k on the layer k, a 2ML^n-cube on the layer n).
- *𝐏^{(k)}'s terms.* The terms with Y ∋ Δ and d_k(Y) = m number at most e^{cm} with c absolute (this is what RG2 (1.26), Σ_{X∋□′}exp(−κd_j(X)) ≤ O(1) "for κ sufficiently large", encodes). The size of each is ≤ E₀ε_k′C₁M^qe^{C₂κ₁} (§5), and the weight is e^{−(1 − 2δ)κm}.
  A Kotecký–Preiss weight e^{a·m(Y)} costs at most e^{24am}, since m(Y) = M^{−4}|Y| ≤ 3·2³d_k(Y) (RG2 (1.28)). So Σ_{Y∋Δ, Y⊄Λ_{k+1}}sup|𝐕_k″(Y)|e^{a·m(Y)} ≤ E₀C₁M^qe^{C₂κ₁}ε_k′Σ_me^{(c + 24a − (1 − 2δ)κ)m} = O(1)E₀C₁M^qe^{C₂κ₁}ε_k′ = O(g_k(log g_k^{−2})^{p₀}) under (C5).
- *The quadratic forms*, kept as forms by Bałaban (RG2 (1.42); §2): |½⟨Q(Y, B), B, B⟩| ≤ ½(4|Y|)²C₃ε_k′M⁴e^{C₂κ₁}e^{−½(κ₁−1)M^{−4}|Y|}(ε_k^♯/g_k)²e^{−⅛(κ₁−1)d_k(Y)} ≤ 8(4M⁴/(e(κ₁ − 1)))²C₃M⁴e^{C₂κ₁}ε_k′(ε_k^♯/g_k)²e^{−⅛(κ₁−1)d_k(Y)}, using x²e^{−bx} ≤ (2/(eb))².
  With ε_k′(ε_k^♯/g_k)² = O(g_k(log g_k^{−2})^{3p₀}) this is small per Y and summable over Y ∋ Δ by the same count.
- *The bracket terms.* At the consumers' points each is ≤ 2C_Bε_ke^{−(κ_Y − ϑ_k)d(Y)} (§5a), and their count and weight are those of their own expansions ((2.42)'s and 𝐄_k's), with κ_Y − ϑ_k in place of κ_Y. So their sum is O(ε_k) as in Bałaban's real case.

No factor grows with k: every factor is the real-support factor times at most 2, or 8 for the quadratic forms' values.

### §9. What the Consumers Receive

Every ω′-dependent expectation under (3.27) or (3.29) with σ_k in D(k+1)(iii)'s ω-polydisc has the action Σ_YT(Y; σ_k, A) + (the source term), with A the real integration variable.
Each T(Y) with Y ⊄ Λ_{k+1} is analytic in σ_k there (§3, §6) and bounded as in §5–§6: the 𝐏^{(k)}-terms by their real-support bounds with the fluctuation factor and the coefficients at most doubled and the quadratic forms' values at most multiplied by 8, the bracket terms by p.277's O(ε_k) times 2 with the decay rate reduced by ϑ_k (§5a). The terms with Y ⊂ Λ_{k+1} do not depend on σ_k, and the source term is the D2.6 closure's 2.2 (2).
Bałaban's Mayer and cluster expansions (RG2 (2.1)–(2.5), p.12; CRE pp.277–279) use the terms only through their sup bounds and localisation domains, so they run at complex σ_k on these inputs. This is the joint bound at complex σ_k that the D2.6 closure's 2.2–2.3, 4.2(iii), 4.3, 4.5 and 5.0 consume, and the σ_j-analyticity of 𝐏^{(j)} and V^{(j)} in the map's D2.2(6)(e) (#MD2.2.6.170, #MD2.2.6.172).
The derivatives δ/δ(tA_k) in CRE (3.28) are Cauchy derivatives at radius r_{α,k}/(4C₁^{RG2}g_k) about the consumers' points. Under (C3), C₁^{RG2}ε_k^♯ + r_{α,k}/4 < 3r_{α,k}/4, so the disc lies in 𝒫_k^{3/4}, and each differentiation costs 4C₁^{RG2}g_k/r_{α,k} times the §5 bound there (for 𝐏^{(k)}'s terms at fluctuation factor 3r_{α,k}/4, for the bracket terms M_Y^{loc}).

## Constant Conditions

RG2's own conditions, under which Lemmas 1 and 2 hold and which §1 uses as stated (pp.5–7, 10): 4C₂B₀e^{16κ₁}ε₂ ≤ 1; 4C₄B₀²e^{32κ₁}ε₃ ≤ 1; 2B₀e^{16κ₁}ε₃ ≤ ε₂; 4B₀C₁^{RG2}e^{16κ₁}ε₁ ≤ ¼α₂; e^{16κ₁}C₁^{RG2}ε₁ ≤ ⅓a₁; "e^{32κ₁}ε₁ smaller than an absolute constant" (p.7), which contains O(1)ε₁ ≤ ε₂ and C₁^{RG2}ε₁ ≤ ε₃; δ₁M ≥ κ₁ (p.5); κ₁ and κ large as on pp.8–9.

CRE p.277's margin (map #MD2.2.4.74–78, #MOMGD.49): the bracket terms with Y ⊄ Λ_{k+1} are analytic in the shift for sup|B′| < r_{α,k} = min(β,1)α_{1,k}/(16B₀e^{16κ_s}).

This note's conditions, with c₃ = 2A₁/A₀ + (4dL)²(1 + β₀)B₃ and h_k = max(c_He^{−R_k}ε_k, S_H):
- (C2) g_k^{3/2} + 7.5h_k ≤ c₃ε_k: the ratio bound 2 (§4–§5), V_act below its parent term, and §6's Gaussian-form step; a smallness condition on g_K, since S_H ≤ g_k^{3/2}/40 and c₃ε_k/g_k^{3/2} → ∞.
- (C3) C₁^{RG2}ε_k^♯ < r_{α,k}/2, ε_k^♯ = c₃ε_k + g_k^{3/2} + 6h_k: membership in 𝒫_k^m (§4), the consumers' points in 𝒫_k^{3/4} (§5), the closed Cauchy disc of §6 inside 𝒫_k^m, and §9's disc inside 𝒫_k^{3/4}. Under (C2) it follows from 64B₀e^{16κ_s}C₁^{RG2}c₃ε_k < min(β,1)α_{1,k}, a smallness condition on g_K under q₁ > p₀.
- (C4′) 3h_k ≤ g_k^{3/2}: §6's bracket part at the Cauchy radius g_k^{3/2}; a smallness condition on g_K, since S_H ≤ g_k^{3/2}/40 (map #MD2.2.6.193) and e^{−R_k} is smaller than any power of g_k (R_k ≥ (log g_k^{−2})^r, r > 1, CRE (2.5), which the tube's R^T satisfies, BETA_FUNCTION_WILSON_LOOPS.md #B2.2.280).
- (C5) (1 − 2δ)κ > c + 24a + 1: the count check with the Kotecký–Preiss weight a per M-cube (§8); RG2's "κ sufficiently large".
- (C7) 2τ_k ≤ 12^{−3/2} and 8(2τ_k)^{1/3}(log(c_σM̄/(C_Bε_k)) + c_*) ≤ log 2 (§5a); a smallness condition on g_K.
