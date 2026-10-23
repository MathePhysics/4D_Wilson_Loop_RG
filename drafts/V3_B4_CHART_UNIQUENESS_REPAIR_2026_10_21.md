# V3 (B4)(i): whole-chart uniqueness — check and repair (21 Oct 2026)

V3 = `WILSON_FIRST_RG_STEP_V3.tex`. Checked at SHA256 `4B505E79E73B6F06D0C774E7D4C06D65CD790E63D5AA0605F9D7B7359CD12433` (15:35). Note reviewed by two isolated CLI reviewers (r1, 17:15–17:26; §6), then revised. The edits of §5 are applied to V3 (§7), reviewed again (r2, 17:45–17:58) and corrected (§8). The corrections were reviewed a third time (r3, 18:33–18:45) and the r3 minor points fixed (§9). The status line is the last line of this note.

## OPEN MATHEMATICAL GAPS

- **(B4)(i) whole-chart uniqueness.** The objection is real. Without the reading, the dependence is load-bearing at **every** row for U1, U2, U4, and also at the far rows for U3, U5 (§2).
  - The gap is closed by Lemma c2-fibre-smallness (§3). The lemma uses:
    - (B1), with its existing readings, including U₁ ∈ D^{(11)}(V,V₀) and CRE's O(L²) independent of the coupling and the branch;
    - the construction of V3's branch-data section (L273);
    - Lemmas two-block, c2-local-gauge (with a generic parameter) and c2-uniform-chart;
    - threshold item 5 and a new item 6, which consists of two upper bounds on ε₀ and holds for small g₀ (after r2; a third bound was implied by the first).
  - The invertibility of α_c(U₁) in (B2) is now proved at every row (Remark under (B2), §8). Only (B2)'s reading of the rows with one block off Ω₁ remains an input.
  - The lemma does **not** prove whole-chart uniqueness. It proves uniqueness among chart-class families whose fine field lies in D^{(11)}(V,V₀), which is all that U1–U5 need.
- **Elsewhere:** LIP-1 is being worked in form (a), in `WILSON_CAUCHY_LIP1A_2026_10_21.md`. H-1 and the order of constants of H-2 are closed there. H-2a ((B3)(i) at a fixed ε₀) and H-2b ((B1)(iii) near ∂Ω₁) are open. None of this changes the (B4)(i) repair, which is at V3's own thresholds.

## 1. The finding

**What RG1 says.** RG1 p.267 (`tex/RG1/parts/p267.tex` l.28; l.16 for the references) states that "there exists exactly one solution of this equation". It refers to the proofs in Sect. C [15] (VAR) and Sect. E [14] (REG), and it **names no solution class**. RG1 calls the setting the "particularly simple unit lattice situation".

**What V3 reads into it** ((B4)(i), L313; L124 list):
- uniqueness among all chart-valued solutions (h(q) < ϱ_G) at every argument of the domain of integration;
- existence there;
- analyticity on a neighbourhood containing all arguments.

All three are marked in V3 as readings. RG1 does not state them. [14] and [15] were not checked; after the repair, V3 needs neither for D̃.

**What V3 proves itself.** Lemma c2-uniform-chart(ii) (L3691, proof L3704) gives uniqueness among small solutions (‖d‖ ≤ ρ_d, for ‖A|_{E_c}‖ < ϑ_*), for every background with a site gauge of phases ≤ τ_L/2 on E_c. V3 verifies that hypothesis only for near rows (L3711).

## 2. Where the reading is load-bearing

| Use | Where | What fails without whole-chart uniqueness |
|---|---|---|
| U1 (every row) | L273 | B ↦ U(B) is "defined on 𝒜_ξ by this uniqueness"; two admissible families at one B make U(B) ill defined. |
| U2 (every row) | L300, L2138 | The singleton sections 𝖯(B), which make B ↦ d a function with Borel graph (Lusin–Novikov itself needs only countable sections). |
| U3 (far rows) | L450 | Agreement of the far-row, near-row and germ definitions via "exactly one chart-class solution". |
| U4 (every row) | L269, L307, L2105 | Gluing of local neighbourhoods into one D̃ on N_Θ, hence Θ and the Jacobian of (1.14). |
| U5 (far rows) | L313, L465/L469, L475, L3726, L3742 | Identification with CRE's D̃; existence at every argument; analyticity near the arguments. |

**Non-load-bearing pointers** that cite the removed content: (B4)(ii) "(shown there from (B1), (B2) and (B4)(i))"; the (B4) preamble; L446's list of inputs; the positivity reading cited at L503, L2078, L2132.

**Why surjectivity does not rescue it.** L273's surjectivity builds d := 𝒩_{U₁}(A′), *a* chart-class family. Without uniqueness it cannot be identified with the row solution.

## 3. The repair: Lemma c2-fibre-smallness

Notation:
- n_𝓔 is the largest number of bonds of a two-block set, where E_c = {r : {r₋,r₊} ⊂ ℬ_{c₋} ∪ ℬ_{c₊}} (eq:regular-stencil-bonds, L341); n_𝓔 is a constant of L.
- O(L²) is CRE's p.247 constant of (B1)(ii).
- c_h, c_G and r_G are the group constants (L3533). s_𝔓 is defined at L3626.

**Threshold item 6 (new).** It consists of three upper bounds on ε₀ with constants fixed before the coupling:
- 3c_h s_𝔓 ε₀ ≤ r_G;
- 3c_G c_h s_𝔓 ε₀ ≤ τ_L/2;
- n_𝓔^{1/2} c_G c_h · 2O(L²) ε₀ ≤ ϑ_*/4.

It holds for small g₀, because ε₀ = g₀A₀(log g₀⁻²)^{p₀} → 0 and O(L²) is independent of the coupling and the branch (the existing reading). The first bound follows from the second, since τ_L ≤ 2c_G r_G; it is kept for readability.

**Lemma c2-local-gauge, generic parameter.** Its proof (L3615) uses ε₁ only through "≤ 2c_hε₁" and "6c_h s_𝔓ε₁ ≤ r_G". So it holds with any ε > 0 in place of ε₁, with bound 6c_G c_h s_𝔓 ε. V3 now records this after the proof.

**Statement** (for every admissible (Ω₁,V,V₀); U₁ on Ω₁, V₀ on the other bonds):

- **(i)** At every row c ∈ Ω₁^{[1]}, U₁ has a site gauge on 𝔓_c = ℬ_{c₋} ∪ ℬ_{c₊} with phases ≤ τ_L/2. So Lemma c2-uniform-chart (i)–(iii) hold at c, and φ_c is defined, analytic and real on ‖A|_{E_c}‖ < ϑ_*.
- **(ii)** Let U ∈ D^{(11)}(V,V₀), A′ = (1/i)log(UU₁⁻¹) on Ω₁, d = 𝒩_{U₁}(A′) and A = A′ + h_{U₁}d (so A = g₀𝖢_{U₁}B with B = g₀⁻¹A′|_{Ω₁*}, by L273, which does not use the cutoff (1.25)). Then for every row c:
  - ‖A′|_{E_c}‖ ≤ ϑ_*/4;
  - h(d_c) ≤ K_*ϑ_*²/32 < ρ_d;
  - ‖A|_{E_c}‖ < ϑ_*/2;
  - d_c = φ_c(A|_{E_c}).
- **(iii)** For B ∈ 𝒜_ξ, every chart-class family d at A = g₀𝖢_{U₁}B with U_d(B) ∈ D^{(11)}(V,V₀) equals φ(A) := (φ_c(A|_{E_c}))_c.
- **(iv)** Let N_Θ := {A ∈ 𝔤^{Ω₁} : ‖A|_{E_c}‖ < ϑ_*/2 for every c ∈ Ω₁^{[1]}}. This set is open and contains the argument A of every U ∈ D^{(11)}(V,V₀), by (ii). On N_Θ:
  - φ is analytic and real, and solves the row system;
  - ‖h_{U₁}(c)∂_{A(b₀(c))}φ_c‖ ≤ 4H_*K_*‖A|_{E_c}‖ < 1;
  - det(id − h_{U₁}δφ/δA) = ∏_c det_𝔤(id − h_{U₁}(c)∂_{A(b₀(c))}φ_c) > 0.

**Proofs.**

- **(i)**
  - 𝔓_c is a lifted rectangle of side ≤ 2L ≤ s_𝔓 (injective, since the periods are ≥ 8M > 2L), and it contains E_c.
  - Its blocks lie in Ω₁^∼ ((B1)(iv)), and U₁ lies in the domain of integration ((B1)(iii)). So (B1)(i) gives ‖U₁(∂p) − id‖_op ≤ c_h ε₀ = 2c_h(ε₀/2) for every plaquette in 𝔓_c (L252).
  - Lemma c2-local-gauge with ε = ε₀/2 and item 6 gives phases ≤ 3c_G c_h s_𝔓 ε₀ ≤ τ_L/2.
  - The fluctuation arguments A ∈ 𝔤^{Ω₁}, extended by zero, vanish on E_c ∩ Ω₁^c. Because b₀(c) ∈ Ω₁, this subspace is invariant under d ↦ A − h_{U₁}(c)d, and (i)–(iii) of Lemma c2-uniform-chart hold on it by restriction.
- **(ii)**
  - (B1)(iii) gives |U′(b) − 1| < 2O(L²)ε₀ on every bond of Ω₁: each bond of Ω₁ lies in □′^{∼2} for some cube □′ ⊂ Ω₁, the designated bonds included.
  - By item 5 this gives ‖U′(b) − id‖_op < r_G, and then h(A′(b)) ≤ c_G c_h · 2O(L²)ε₀. Item 6 gives ‖A′|_{E_c}‖ ≤ ϑ_*/4 < ϱ_*.
  - Taylor's formula with Lemma c2-uniform-chart(i) and Lemma two-block (𝒩_{U₁,c} depends on E_c only) gives h(d_c) ≤ K_*ϑ_*²/32.
  - b₀(c) is the only designated bond in E_c (Lemma two-block). So ‖A|_{E_c}‖ ≤ ϑ_*/4 + H_*K_*ϑ_*²/32 < ϑ_*/2.
  - d_c = 𝒩_{U₁,c}(A|_{E_c} − h_{U₁}(c)d_c) with h(d_c) ≤ ρ_d. So d_c = φ_c(A|_{E_c}) by Lemma c2-uniform-chart(ii), applicable by (i).
- **(iii)**
  - Chart class means q_d(B) is the chart logarithm of U_d(B)U₁⁻¹, so q_d(B) = A′.
  - The row equations give d = 𝒩_{U₁}(A′) and A = A′ + h_{U₁}d.
  - Apply (ii) to U = U_d(B).
- **(iv)**
  - Openness and containment of the arguments are immediate from the definition and (ii). Analyticity of φ comes from (i).
  - The derivative bound is eq:convex-uniform-implicit-chart (C_𝖣 = 4K_*) with ‖h_{U₁}(c)‖ ≤ H_* and 4K_*H_*ϑ_* < 1.
  - h_{U₁} has its outputs at the designated bonds, and ∂_{A(b₀(c′))}φ_c = 0 for c′ ≠ c (Lemma two-block). So in the order (free, designated) the matrix is block triangular, with identity free block and diagonal designated block. This gives the product formula.
  - Each factor is positive by Lemma c2-uniform-chart(iii).

**Consequences in V3.**
- D̃ := φ is one analytic function on N_Θ, so no gluing is needed.
- Θ is injective there, by V3's argument at L269, and it is a diffeomorphism.
- The far-row positivity reading of (B4)(iii) becomes a proved statement.
- CRE's D̃ equals φ wherever CRE defines it as a solution of the row system with chart-valued phase and fine field in D^{(11)}(V,V₀). This uses the retained first clause of (B4)(i), and the fact that this is CRE's use in (1.13)–(1.14) is V3's reading (L273).

## 4. Readings: removed and kept

- **Removed:**
  - existence and uniqueness of the chart-class row solution at every argument, and analyticity of D̃_c on a neighbourhood of all arguments (L124, (B4)(i), the (B4) preamble, L465);
  - the positivity reading of (B4)(iii), at L124, (B4)(iii), L503, L2078, L2132.
- **Kept:**
  - the identification of CRE's defining equation with the row system, the first clause of (B4)(i). It is used for the comparisons with CRE (L465, L475, L3726, L3742, the last sentence of (B4)) and nowhere in V3's identities.
  - CRE's O(L²) independent of the coupling **and the branch**. The L124 entry now names item 6.
  - "U₁ in the domain of integration" (L124, (B1)(iii)). The lemma uses it at every row.
- **Still inputs through (B1):** REG ([14]) and VAR ([15]). The (B4) preamble still cites [16] (16)–(18) for the description of D̃. RG1 p.267 is quoted only as Bałaban's description.

## 5. V3 edits (final list, after r1)

- **E1.** Insert Lemma c2-fibre-smallness, with its proof and with item 6 as eq:c2-fibre-thresholds, after the applicability paragraph (L3711). After the proof of Lemma c2-local-gauge, add the generic-parameter sentence.
- **E2.** Thresholds:
  - add item 6;
  - add n_𝓔 to the order of choice (L3932);
  - L3940: "for item 6 because ε₀ → 0 and O(L²) is independent of the coupling and the branch";
  - L124 (H2): "items 1–6";
  - L124 O(L²) entry: "behind the domain statement of (B1) and item 6".
- **E3.** (B4) preamble: D̃ is the small solution φ of (i). The three further properties are "CRE's and RG1's statements, this paper's readings, marked as such, and facts proved in Lemma c2-fibre-smallness".
- **E4.** (B4)(i):
  - keep up to "depends on A|_{E_c} only";
  - then: RG1's statement is quoted, names no class, and is not used beyond the identification;
  - D̃_c = φ_c at every row (Lemma (i)), with φ_c(0) = 0 and Dφ_c(0) = 0;
  - every argument lies in the ϑ_*/2-ball (Lemma (ii));
  - every chart-class family with fine field in D^{(11)}(V,V₀) is φ (Lemma (iii));
  - CRE's D̃ is φ wherever CRE defines it as such a solution (marked reading).
- **E5.** (B4)(ii): "(B4)(i)" becomes "Lemma c2-fibre-smallness". (B4)(iii): the positivity reading is replaced by "positive on 𝒜_ξ, by Lemma c2-fibre-smallness(iv)".
- **E6.** L124: drop "and the existence and uniqueness … pp.248–249" and "the positivity of the Jacobian … do not use;".
- **E7.** L269: N_Θ becomes the set of Lemma (iv), containing all arguments of D^{(11)}(V,V₀) (Lemma (ii)); the gluing and shrink clauses are dropped.
- **E8.** L273: "the family d of chart class with U_d(B) ∈ D^{(11)}(V,V₀) is unique and equals φ(g₀𝖢_{U₁}B) (Lemma (iii))".
- **E9.** L300: singleton sections by Lemma (iii); the derivative identity on N_Θ (Lemma (iv)). L2138: Lemma (iii).
- **E10.**
  - L446: add Lemmas c2-uniform-chart and c2-fibre-smallness to the inputs.
  - L450: far rows use φ_c (Lemma (i)–(iii)); the germ neighbourhood lies inside the ϑ_*-ball; agreement comes from small-ball uniqueness.
  - L465/L469: the germ is that of φ_c and of every solution continuous at zero with value zero.
- **E11.**
  - L307: N_Θ of Lemma (iv), via (ii).
  - L2105: N_Θ.
  - L3742: φ_c is the row solution of (B4)(i).
  - L503, L2078, L2132: positivity is proved, not read.

**Status:** see the last line of this note.

## 6. r1 review (isolated CLI reviewers, claude-opus-5-5 xhigh)

- **b4u-a-lemma-20261021-r1** (§3; report 205 lines, read in full).
  - Verdict: "correct and sufficient for its purpose". No fatal or serious issues.
  - Minor findings m1–m7: the missing factorisation, the wording of the phases off Ω₁, L341 not supplied, invertibility on all of N_Θ, the CRE-use reading, the uniqueness qualifier, n_𝓔 in the order of choice. All are adopted in §3 and §5.
  - Observation: (i) would also give the invertibility of α_c(U₁) at every row, which would extend the (B2) Remark. Not adopted (outside this repair).
- **b4u-b-uses-20261021-r1** (§1, 2, 4, 5; report 236 lines, read in full).
  - Diagnosis correct; repair sufficient in substance; edit list not applicable as written.
  - Serious findings:
    - **S1:** the E4 cut point left the reading in place, unmarked;
    - **S2:** E4 overstated Lemma (iii);
    - **S3:** an existence reading remained in the (B4) preamble and at L465/L469.
  - Minor findings M1–M11: localisation, U2 wording, the [14]/[15] claims, the kept-list, item placement and the (H2) count, E7 and the citation of (b), E11 citations, the missed sites (B4)(ii), L300 and L446, the generic-ε restatement, and the RG1 line numbers.
  - All are adopted in §1–§5. My own search of the whole file added L503, L2078 and L2132.

## 7. Applied to V3 (17:30–17:42)

- Backup of the pre-edit file: `backups/20261021-1745-b4u/WILSON_FIRST_RG_STEP_V3.tex` (SHA256 `4B505E79…`).
- Edited V3: SHA256 `EBE8ABC10A5FEAF28B2E06992AFFD0B2CA07413899CF0C3E431558B2EF5EA2BB`, 5207 lines, CRLF kept (CR = LF = 5207).
- Build: pdflatex twice, 249 pages, no `!` lines, no undefined or multiply defined references. The new lemma is Lemma 65, p.175; item 6 is eq. (353).
- New text:
  - Lemma c2-fibre-smallness with proof (new lines 3715–3748), after the applicability paragraph, with a one-sentence lead-in;
  - the generic-parameter remark after the proof of Lemma c2-local-gauge (new line 3618);
  - threshold item 6 (new line 3976).
- Edits as applied, by old line:
  - **L124:** "items 1--6"; the O(L²) entry names item 6; the (B4) readings entry is now "the identification of the defining equation of D̃ with the row system, and of CRE's D̃ in (1.13)–(1.14) with the chart-class family whose fine field lies in D^{(11)}(V,V₀)", with existence, uniqueness, analyticity and positivity marked as proved.
  - **L269:** Θ on N_Θ of Lemma (iv); the gluing and shrink clauses are removed.
  - **L273:** uniqueness by Lemma (iii).
  - **L300:** singleton sections by Lemma (iii); derivative identity on N_Θ.
  - **L307:** Θ on N_Θ, independent of R₁.
  - **L313:**
    - the preamble says D̃ is the small solution φ of (i), and that the three properties include facts proved in the lemma;
    - (B4)(i) is rewritten: the RG1 quotation is kept as description only; the lemma's (i)–(iv) are stated; D̃_c = φ_c at every row; the remaining reading is marked;
    - (B4)(ii) cites the lemma;
    - in (B4)(iii) the positivity is proved (Lemma (iv)).
  - **L446:** the lemmas are added to the inputs.
  - **L450:** far rows use φ_c; the germ neighbourhood lies in the ϑ_*-ball; agreement by Lemma c2-uniform-chart(ii).
  - **L465, L469:** the germ is the germ of every solution continuous at zero with value zero, in particular of φ_c.
  - **L503, L2078, L2105 (two sites), L2132, L2138, L3742:** pointers to the lemma; at L2132 the near-row-only positivity clause is removed.
  - **Thresholds:** n_𝓔 in the order of choice; item 6; the satisfiability clause for item 6; O(L²) added to the threshold's dependence list.
- Unchanged, as planned: L475, L3726 (they cite (B4)(i), which now contains the identification), L520 (cites (B4)(iii), now proved).

## 8. r2 review of the edited V3, and fixes (17:45–18:14)

- **Reviewers.** Isolated CLI reviewers, claude-opus-5-5, both finished by 17:58:
  - `reviews/b4u-a-lemma-20261021-r2/review.txt`: the lemma, the remark after Lemma c2-local-gauge, and item 6;
  - `reviews/b4u-b-uses-20261021-r2/review.txt`: the edited uses of the lemma.
- **Verdicts.** Both reviewers found the edits correct and sufficient, with no fatal or serious findings. Packet a raised 6 minor points. Packet b raised 9 minor points, some cosmetic ones and one evidence request.
- **Evidence request (b).** The question was whether the cutoff (1.25) tests designated values of CRE's linearised variable. If it did, CRE's D̃ would carry weight in the definition of 𝒜_ξ.
  - Checked against the transcriptions: (1.18)–(1.19) on p.250, and the rewritten tests and (1.25) on p.252, take sup over (□′^{∼2})^* only. These are the bonds other than the designated ones. The only other factor is χ₀′, a test on the fine field.
  - **Answer: no.** The cutoff is a function of the fine field. This is now stated at L273.
- **Fixes, by finding:**
  - **a1 / b9: 𝓔_c ⊆ 𝔓_c.** Lemma (i) now says that both endpoints of a bond of 𝓔_c lie in the two blocks, by eq:regular-stencil-bonds. The definition was simply missing from the packet; nothing of substance changes.
  - **a2: nominal loop.** Uniform-chart(ii) now says that the germ of row-locality is built from Lemma two-block and D𝒩(0) = 0 alone.
  - **a3 / b: converse argument.** Lemma (ii) now cites only the decomposition step of the converse argument, up to the definition of B, which uses neither (1.25) nor (iii).
  - **a4: nesting citation.** Lemma (ii) now cites:
    - p.248 for Ω₁ being a union of LMR₁-cubes;
    - p.245, "compatible", with the (H4) reading as nested;
    - the paragraph after eq:c-standing-conditions, where all sides are powers of L.
  - **a5 / b: item 6.** Item 6 is reduced to two conditions. 3c_h s_𝔓 ε₀ ≤ r_G follows from the first, since τ_L ≤ 2c_G r_G (eq:c2-tau-final). The lemma, its proof and threshold item 6 are updated to match.
  - **a6 / b5: source lists.** (H4) at L124 and (B4)(i) now name what the lemma is proved from: (B1) (with (B3)(i)), (B2), Lemmas c2-local-gauge, c2-uniform-chart and two-block, and items 5 and 6.
  - **b1: far-row domain (L450).** φ_c is defined on the ball ‖A|𝓔_c‖ < ϑ_* (Lemma (i)). The arguments of 𝒜_ξ lie in the half ball (ii), where its value is the chart-class value (iii).
  - **b2: "the solution" (L446).** D̃_U is now "the solution, selected below"; for U = U₁ it is CRE's correction under the reading of (B4)(i). L450 now says "the form of the equation of RG1 p.267 for RG1's own step".
  - **b3: attributions to RG1.**
    - The (B4) opening now gives CRE p.248's own pointer: (16)–(18) of [16], or (I.1.8)–(I.1.9) of [I], which is RG1.
    - It records that RG1's (1.8)–(1.9), p.261, concern the functions J_j.
    - It attributes the p.267 uniqueness statement to RG1's own unit-lattice step.
    - L2084 and L2138 no longer call V3's D̃ "RG1 (2.10)".
  - **b4: header before (B1).** It now names the items that record readings, derivations or proofs.
  - **b6 (both reviewers): the (B2) Remark.** Rewritten. The invertibility of α_c(U₁) is now proved at every row, from three facts:
    - α_c depends on U|𝓔_c only;
    - Lemma two-block gives invertibility for e^{iA} with ‖A‖_∞ ≤ τ_L, and gauge covariance;
    - the first assertion of Lemma (i) gives a site gauge with phases ≤ τ_L/2, from (B1)(i), (iii), (iv) and Lemma c2-local-gauge, without (B2).

    Only (B2)'s reading of the rows with one block off Ω₁ remains an input.
  - **b7: (B4)(iii).** "Taken as stated" is removed; the nonvanishing follows from (i) and Sylvester's identity.
  - **b8: primitive-bounds.** It now reads "CRE's under the reading of (B4)(i), by Lemma (iii)".
  - **b10, cosmetic.** The subspace sentence of Lemma (i) is retyped.
- **Self-found, added:**
  - Lemma (iv) now states and proves that Θ(A) = A − h_{U₁}φ(A) has ‖Θ(A)|𝓔_c‖ < ϑ_* and is chart-valued on every bond of Ω₁. The proof uses that every bond of Ω₁ lies in 𝓔_c for some row c ∈ Ω₁^{[1]}.
  - L269 cites this: Θ(𝒩_Θ) lies in the chart domain, where 𝒬_{U₁} is the slice submersion. The removed shrink clause used to provide this.
  - At L450, a parenthetical records that the germ phase is chart-valued: its norm is below ϑ_* + H_*ρ_d < 2ϑ_* ≤ ϱ_G.
- **Left unchanged:**
  - the applicability paragraph's "side 2L+1", a loose upper bound (the reviewer marked it optional);
  - the nesting sentence at L549, which gives its reasoning.
- **Applied:**
  - backup `backups/20261021-1810-b4u-r2/WILSON_FIRST_RG_STEP_V3.tex` (SHA256 `EBE8ABC1…`);
  - new V3 SHA256 `7C0F494F44C10FE9B6A528E589DCE220B6BE88C87B45392DC72C853C46B3DD78`, 5206 lines, CR = LF = 5206;
  - build: pdflatex twice, 250 pages, no `!` lines, no undefined references, only the 7 old hyperref warnings.
- **Re-reviewed:** in r3 (§9).

## 9. r3 review of the r2 fixes, and fixes (18:33–18:57)

- **Reviewers.** Isolated CLI reviewers, claude-opus-5-5 (checked in both manifests):
  - `reviews/b4u-a-fixes-20261021-r3/review.txt`, finished 18:41: the lemma, the Remark under (B2), and item 6;
  - `reviews/b4u-b-fixes-20261021-r3/review.txt`, finished 18:45: the edited uses.
- **Verdicts.** Both: "correct and sufficient", with no fatal or serious findings. Packet a raised 7 minor points (m1–m7). Packet b raised 6 minor points and some cosmetic ones.
- **Settled without an edit.**
  - m1, the definition of 𝓔_c: the evidence is in the packet (eq:regular-stencil-bonds).
  - [I] = RG1: CRE's reference list, p.285, gives Commun. Math. Phys. 109, 249–301.
- **Fixes, by finding:**
  - **m2 / b1: L269, Θ(𝒩_Θ) ⊆ 𝒩₀.** The old text said only that Θ(𝒩_Θ) lies in the chart domain. The transformation rule was applied on 𝒩₀, the part of the chart domain whose row averages lie in the domain of the row chart. The text now proves the inclusion:
    - the phases of Θ(A) are chart-valued;
    - ‖Θ(A)|𝓔_c‖ < ϑ_* < 2ϱ_* at every row, where 𝒩_{U₁,c} and hence 𝒬_{U₁,c} are defined and analytic (uniform-chart (i), applicable by fibre-smallness (i));
    - so the row averages lie in the domain of the row chart.
  - **m3 / b2: L450.** The far-row values are now cited to fibre-smallness (i), where φ_c is the unique small solution, not to (ii). "Half ball" is now "the ball of radius ϑ_*/2".
  - **m4: Remark under (B2).** The input list of fibre-smallness (i) now names:
    - the first condition of item 6 (with eq:c2-tau-final);
    - the fine periods being at least 8M;
    - 𝓔_c ⊆ 𝔓_c by eq:regular-stencil-bonds.
  - **m5: uniform-chart (ii).** The germ of row-locality is now said to be built from Lemma two-block, 𝒩(0) = 0, D𝒩(0) = 0 and the analyticity of 𝒩 near zero, replacing "D𝒩(0) = 0 alone".
  - **m6: (H4).** The "compatible" reading now covers p.245 (the partitions there "have to be compatible", also with π₀ and with later partitions) as well as p.257.
  - **m7: fibre-smallness (ii).** The parenthetical now cites the invertibility of α_c(U₁) in eq:regular-stencil-elimination, from (i) and Lemma two-block as in the Remark under (B2), instead of "(B2)".
  - **b3: header before (B1).** It now says "among them", and lists:
    - the Borel choices, the convention and the derivations in (B1);
    - the Remark under (B2);
    - the parts of (B4)(i) and (iii) proved in fibre-smallness;
    - the proofs in (B4)(ii).
  - **b4: source lists.**
    - (B4)(i) adds the (H4) nesting reading and the periods ≥ 8M.
    - L124 adds (B3)(i) through (B1)(i), and the periods ≥ 8M.
  - **b5: "under the reading of (B4)(i)".** Added at Lemma charts (L475) and at Lemma primitive-bounds (L3762).
  - **b6: the (B4) opening.**
    - D̃ is now cited at (1.14), p.249, with the pointer to RG1 at the foot of p.248, and [I] = RG1 with its reference.
    - It now reads "the linearisation of RG1's unit-lattice step is the one following RG1 (2.10)".
    - (B4)(i)'s readings cite CRE pp.248–249: (1.13) is on p.248 and (1.14) on p.249, checked on CRE/parts.
  - **Cosmetic:** L273 now reads "(1.25), p.252, in the variables of (1.15)".
- **Not adopted:** the optional m4 strengthening D^{(11)}(V,V₀) ⊆ 𝒳. The reviewer notes that the Remark's argument applies to every U ∈ D^{(11)}(V,V₀). V3 states and uses only U₁ ∈ 𝒳 (measurability paragraph, L300), so nothing depends on it.
- **Applied:**
  - backup `backups/20261021-1851-b4u-r3/WILSON_FIRST_RG_STEP_V3.tex`, holding SHA256 `7C0F494F…`;
  - new V3 SHA256 `A520A59F363DED6EAE5694327DD27565233D339F5EEE585E8E283CB8E468EBD0`, 5206 lines, CR = LF = 5206;
  - build: pdflatex twice, 251 pages, no `!` lines, no undefined references, only the 7 old hyperref warnings.
- **Not re-reviewed:** the r3 fixes. All are local rewordings and citation repairs. The L269 inclusion is the only one with content, and it uses only bounds that r3 checked (fibre-smallness (iv), uniform-chart (i)).

**Status (18:57):** (B4)(i) is repaired in V3 and has been reviewed three times, the last two rounds with no fatal or serious findings. The r3 minor points are fixed. Uniqueness holds in the chart class with fine field in D^{(11)}(V,V₀); whole-chart uniqueness is neither claimed nor used.
