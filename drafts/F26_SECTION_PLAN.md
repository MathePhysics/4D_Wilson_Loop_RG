# Working Plan for the New Section of the Supplement (F26)

Written 12 Nov 2026, 19:35, on the user's instruction "Add a new section, this is important!". This file is the
state of the work on `FINDINGS.md` F26; delete it when the section is written, compiled, and recorded.

## Where the Section Goes

- `BALABAN_SUPPLEMENT.tex` has 17 sections; the last is Section 17, "Lemmata on Bałaban's Papers" (line 2248),
  whose lemmata the paper cites as "Supplement, Lemma 17.x". Propositions are numbered S.1–S.18 globally (S.18 =
  `prop:flat-values`, Section 16). **The new section is Section 18, at the very end**, so that no cited number
  shifts; a proposition in it is S.19, its lemmata are 18.m.
- Title (proposal): "The Cluster Weights of Two Runs on the Terms with Large Fields".
- Then: S.14(f) (`prop:large-field-integrands`, statement at line 1918, proof paragraphs "(f)" at 1943 and "(f),
  several loops" at 1952, `eq:dressing-rates`, `eq:dressing-rates-cross`) cites the new section for the terms with
  C^W_Q and takes the corrected rates from it; the supplement's introduction (Section 1) lists the new section;
  the paper's appendix of conditions gets the new condition (below); the paper cites "Supplement, Proposition S.19"
  where it uses s^W_K, s^{W,0}_K (`prop:young-pairs`, line 2696 of the paper, and the sequence `s'_K`, line 2690).

## What the Paper's Set-Up Is (read 19:30, paper at 8f85b18a090a)

- Definition "Dressed Loops" (`def:dressed-loop`, line 1123): 𝒲_k = Πκ^{(k)} · e^{𝓔_k}[Πf + Σ_𝔅 Q_k(𝔅)w_k(𝔅)];
  (i) |Q_k(𝔅)| ≤ Π_{W∈𝔅} e^{θ(W)}, 0 ≤ θ(W) ≤ νσ(W)/16; the cross species has rates λ_k(W) ∈ [15/16, 1]
  (`eq:cross-bound`); the factors are defined at the *reference data* of the term (trivial field, 𝐉 = 0, outer
  variables trivial) whether or not these lie in the support of the indicators (iii).
- "The Reference Gas" (`sec:reference-gas`, line 1339): Y_𝒢 at the reference data of ℓ is c_𝒢 id for a group on
  one loop, c_𝒢 := 0 for a cross group; the clusters of the step k are merged into the groups; hard-core gas with
  activities c_𝒢; Φ°(Γ; ℓ) = φ^U(Γ)Π c_𝒢; weight a°(𝒢) := (ν/32)σ_{k+1}(𝒢). **So on a term with large fields
  the paper's activities c_𝒢 contain the attached content of 𝒢** (the "map's activities" of the note).
- The paper has ν where the notes have ν_r (ν_r = ν). The supplement's (f) uses λ ≥ 31/32 for the cross species
  (lines 1956, 2177) while the paper's definition has [15/16, 1]: use the paper's range, or check line 1511.

## What the Notes Do (read 19:10–19:25; hashes: LF ada99ead6f26, pair's Cauchy note afc3b3c86e0e)

- LF #5.42: φ_k(Γ) and the attached local terms are cluster terms at the reference point; "their activities differ
  by ≤ c̄^W_K relative"; marked-cluster bound ⇒ Σ_{Γ hits W}|φ^B − φ^A| ≤ 2C_ptC_XC_KP c̄^W_K θ(W); then
  Q-part ≤ C^W_Q c̄^W_K w(W), C^W_Q := C_ptC_XC_KP ν/(4eν_r), under 2C_ptC_XC_KP c̄^W_K ν/16 ≤ ν_r/2 (arithmetic
  checked). The premise is not justified in LF for activities with attached content: the difference mass (D) of
  the attached species has the absolute part 24(m_W + 1)τ^w_K (LF #5.40-2, #5.41).
- Pair's note: (a) the "gauge" #PC4.14.4-1–#PC4.14.4-4.14: on the terms with large fields use c^n_𝒢 := value at
  the reference point of the part of Y_𝒢 *without attached content* (identity for any numbers c^n); cost
  ΔE^g_n = −Σ_X Ursell(X)[Πc − Πc^n], |ΔE^g_n| ≤ N_n := Σ_𝒢|c^a_𝒢|e^{a°+(ν/2)σ+(3/8)ν_e ext}; c^a ≠ 0 only by
  (α) productions of attached species at the step, (β) touched members with attached content, (γ) occurrence
  factors with attached content (an untouched member adds nothing: c_𝒢 is multilinear in the members and a carried
  Y^d vanishes at the reference point); N_n ≤ P_n + y_n + fN_{n−1}, f ≤ 1/8; ΣN ≤ (8/3)ΣP; ε̄^g_A := 3 sup_j
  (ε^{(2)}_A(j) + C^P(j)) + ε^R_A replaces ε̄_A; differences of the gauge terms: relative
  (8C_ptC_XC_KP c̄^{W,×}_K + 4C^×_Q q^car_K)ε̄^g_A per point of the history into s^{W,X}_K, absolute
  10Ā_K = 240(m_W + 1)(τ^{w,×}_K + τ^cr_K) + 10D^{w,×}_K into s^{W,0}_K.
  (b) the carried part #PC4.14-1b: with c^0 := run A's carried wraps and run B's fresh constituents,
  Σ_{Γ hits W}|φ_i(c^B) − φ_i(c^0)| ≤ coefficient of u in Σ_{Γ hits W}|Ursell|Π(c̄^{(2)} + u|δc|) ≤ value at u₀
  divided by u₀ = 162Mσ_i(W)δε̂_i, u₀ := ν/(5184Mδε̂_i), δε̂_i := sup_p Σ_{W′ at p}|δc_{W′}|e^{s+(ν/16)σ};
  δε̂_i ≤ 3C^ε̂Δ^w_i + 2δε̂_{i−1}; δε̂_i ≤ D^cw_K; q^car_K := 162MD^cw_K. Fresh part (#PC4.14-1.4–1.6):
  q^fr_K := 81Mε̂^{(2)}(8ρ^{LF,×}_K + 8x̄_K + 4e^{−C_Pk/4}). q_K := q^fr_K + q^car_K.
  (c) Q-parts on the young pairs #PC4.14-3a: cross member (16/15)C^W_Q c̄^{W,×}_K w(W); carried part
  C^×_Q q^car_K w(W) per member, C^×_Q := 32/(29eν_r); s^{W,0}_K gains (16/15)C^W_Q c̄^{W,×}_K A^× +
  C^×_Q q^car_K M^×; s^{W,X}_K gains 2C^×_Q q^car_K ε̄^g_A/C_M.
- The supplement already has (b) on the all-small-field pair: S.16(i), "the conclusion" (line 2177), with
  q_K := 81Mε̂^{(2)}(8ρ^LF_K + 16(1 + c_oC₁)D^cw_K + 4e^{−C_Pk/4}) + 162MD^cw_K and x^Q_K.

## Design of the Section (to be checked against S.9, S.10, S.16(i) before writing)

1. **Lemma 18.1 (first-order bound for cluster weights).** Hard-core gas of groups; activities c, c′ with
   |c|, |c′| ≤ c̄ and the Kotecký–Preiss sum of c̄ + u₀|c′ − c| within the room. Then
   Σ_{Γ hits W}|Φ°(Γ; c′) − Φ°(Γ; c)| ≤ 162Mσ(W)δε̂ (coefficients in u nonnegative, value at u₀ over u₀), and the
   summed version Σ_Γ|Φ°(Γ; c′) − Φ°(Γ; c)| ≤ Σ_𝒢|δc_𝒢|e^{a°(𝒢)}-type (telescoping, FV Theorem 5.4 (5.11)).
   This is exact mathematics and needs only the Kotecký–Preiss criterion of the paper's reference gas.
2. **Lemma 18.2 (the split).** Y_𝒢 = Y^d_𝒢 + c^n_𝒢 T with c^n the reference value of the part without attached
   content; identity; the weights and local terms at c^n; cost N_n and its recursion; ε̄^g_A.
   *Alternative considered:* keep the paper's activities and bound the density of their differences directly,
   relative part c̄^W_K times the (Kotecký–Preiss small) density of the touched attached content plus absolute
   part by totals. Decide after reading how S.9 carries attached species (per insertion or in total).
3. **Lemma 18.3 (differences of the activities on a young pair):** fresh (Cauchy in the interpolation
   parameter), carried wraps and cross (absolute, totals), occurrences (recursion with factor 2), with the
   constants of S.16(i).
4. **Proposition S.19:** the change of Q_k, of the local terms, and of the split's terms between the two runs on a
   young matched pair; the corrected rates; C^W_Q and C^×_Q defined; the condition
   2C_ptC_XC_KP c̄^{W,×}_K ν/16 ≤ ν/2; summability.

## Design Decisions Reached at 19:55 (after Reading the Paper's §6 and S.9, S.16(i))

**Why the activities must not contain attached content.** With the paper's convention (c_𝒢 = reference value for
every group on one loop) the difference of an attached group's activity between the runs is known only in total
mass (the carry of S.14(f): c̄^W_K Σ_X Ȳ_X + 24(m_W + 1)τ^w_K, proportional to P(X)), not per group and not as a
small root density. A per-group relative bound fails because the difference of a product replaces one parent at
a time (factor = number of parents), and the root density of *carried* attached content at the step n is of the
order L^{n−j}ρ̂_j, not small. Putting such differences through the cluster series gives terms quadratic in the
attached mass of a component. So the direct route (keep the paper's activities) does not work, and LF #5.42's
premise is indeed unjustified for activities with attached content. The pair's note is right to remove it.

**The convention to use ("reduced gas").** A group of an attached species has activity 0 in the reference gas,
exactly as a cross group: it is carried whole and never split. Facts found:
- The paper's prose already says this of the attached insertions ("they cannot be contracted ... carried ... as
  functions which are never summed over the loop", `sec:large-field-step`, line 1295) and of the cross groups
  ("neither split nor contracted", line 1311); but `sec:reference-gas` (line 1359) gives activity 0 to the cross
  groups only.
- At the 𝐑-steps S.10 already puts 𝔞_g := 0 for the groups which are not eligible (cross, or a polymer at a
  second-class or an unchanged component), line 1570; a group which holds an attached insertion in a slot or as a
  member is *not* excluded there. To check in S.10's statement and proof.
- With activity 0 the gas only loses terms: θ(W) and the Kotecký–Preiss sums are smaller; an attached group is
  carried as Y instead of Y − c; no later group containing an attached member enters the gas; the occurrences
  (merged clusters) contain no attached content. The class of `def:dressed-loop` does not mention the convention.
- Two ways to bring it in: (A) make it the paper's definition in `sec:reference-gas` (then T1–T3 are proved with
  it and nothing is "changed" in the comparison), which requires checking that S.9(i)–(iii), S.10, and the proof
  of the inductive step do not use the reference value of an attached group; or (B) keep the paper's convention
  for T1–T3 and prove in the new section that the dressed loop of a term has a second representation with the
  reduced gas (the split is an identity for any numbers), with its bounds obtained from the paper's by the cost
  ΔE^g_n = −Σ_X φ^U(X)[Πc − Πc^n], |ΔE^g_n| ≤ Σ_{𝒢 attached}|c_𝒢|e^{a°(𝒢)} (telescoping and FV (5.11)), as the
  pair's note does (#PC4.14.4-4). (A) is cleaner if the proofs allow it; (B) is the notes' route and needs the
  comparison of the two recursions (ΣN ≤ (8/3)ΣP, ε̄^g_A).
- **Not yet read:** the proof of S.9 (lines 1516–1545) and S.10 (lines 1546–1635). Read them before choosing
  between (A) and (B).

**With the reduced gas, the differences of the activities on a young pair are:** fresh constituents (Cauchy in
the interpolation parameter, relative 8ρ^LF_K at enlarged amplitudes; old components removed at 4e^{−C_Pk/4});
deviation members (marked activities, compared by the recursion: x_i of S.16(i)); wraps carried inside the groups
(absolute, total 2τ^w_K + young e_i; factor 3 and C_ε̂); occurrences (2δε̂_{i−1}). This is the recursion
`eq:activity-difference` of S.16(i), which then holds on the young pairs with the births compared from the first
step of the pair on. Then Σ_{Γ hits W}|Φ°^B − Φ°^A| ≤ q_Kσ(W) uniformly per member, and the Q-part of a member is
C_Q q_K w(W): summed over the attached members 2C_Q q_K ε̄_A P(X), over the others C_Q q_K M^×.
The local terms E^∂ of the two runs differ by the summed first-order bound: Σ_𝒢|δc_𝒢|e^{a°(𝒢)} over the groups
whose activities differ from the trivial term's, relative q-type times their part (≤ 2ε̄_A P(X) per run).
The attached insertions themselves differ by the carry (D) of S.14(f), unchanged.

## Findings at 20:15 (Proof of S.9 Read; S.10 Statement Read in Part)

- **S.9's proof does not use the reference value of an attached group.** Checked paragraph by paragraph (lines
  1520–1539): "(ii), evaluation" uses the sup bound on the subdomain; "(ii), the touched parts" Cauchy's estimate
  ‖∂_tD‖ ≤ 2 sup‖D‖/T_Y and the bridge; "(ii), merged parts" the bound for a sum rooted at an old vertex; "(ii),
  the product" the assignment of a new group to the first old insertion of the species it contains; "(i)" the
  second term of the paper's `eq:insertion-bound`. So S.9(i), (ii) hold verbatim when an attached group is carried
  whole (activity 0). **S.9(iii)'s proof needs it**: "a cluster whose polymer meets neither [Z_{k+1} nor the
  cutoffs on its boundary layer] has the same activity on ℓ and on ℓ₀" is false if the descendants of attached
  insertions, which reach into the small-field region, have nonzero activities on ℓ; with activity 0 it is true.
  So choice **(A)**: make "a group of an attached species has activity 0" the definition in the paper's
  `sec:reference-gas` (line 1359), and say in S.9 that the attached groups are not split.
- **S.10 (line 1570):** "eligible" = not a cross group and no polymer at a second-class or an unchanged component;
  𝔞_g := contraction at the flat reference for eligible g, else 0; line 1605: "the bound of 𝔞_g ... is the product
  of the amplitudes ĉ₁ of the polymers of the group and of the bounds of the insertions of its slots". So an
  eligible group which holds an attached (or wrap) insertion in a slot has that content in 𝔞_g, and its D_g is
  called a deviation insertion "zero at pure-gauge data" (line 1580), which cannot carry a deviation bound when a
  slot holds an attached insertion. **To do:** read S.10's statement and proof in full (lines 1558–1635) and
  extend "eligible" by "holds no insertion of an attached species in its slots or among its members"; such a group
  is an attached insertion of the species of the first attached insertion it holds, with mass at most (amplitude of
  its polymers) × (mass of that insertion) (the notes: #PC4.14.4-4.5.4-1 "in a slot", -4 "members", ε^r_k).
- **S.14(f) has more undefined objects than C^W_Q:** ε̄_A (three occurrences, never defined), Ȳ_X, the masses M_i
  of the carry, b_wrap, C″_Ψ. LF #5.39–#5.41 define them (ε̄_A := sup_{j>k−m_W} ε^{(2)}_A(j) + ε^R_A; Ȳ_X :=
  E_j(Z)-type lifetime masses at enlarged amplitudes plus Ȳ^R_X; P(X) the paper's count of the history). The new
  section must define them, so it has to carry the whole comparison of the dressings on a young pair, not only
  the weights.
- **The young steps are 𝐑-steps** (pair's note #PC4.4-2), so the 𝐑-gas (Ψ(S), E^𝐑, 𝔞_g) is part of the weights
  and local terms of the stopping step, and its activities must be free of attached content as well.
- **Working method:** draft the section in `F26_SECTION_DRAFT.tex` (not compiled into anything), move it into the
  supplement as Section 18 only when every statement in it is proved; the supplement and the paper are not
  touched before that, except for nothing.

- **S.10's statement read in full (20:25).** It works "on a fixed term of the multilinear expansion of [the
  term's] insertions": the letters of a loop are the link transports and the insertions of the term, and an
  insertion whose interval meets an arc of C ∩ X⁺ belongs with its whole interval to the slot of that arc. So the
  attached insertions of a component X which the 𝐑-operation integrates sit in the slots of X and *end there*
  (S.9: the species "ends when the 𝐑-operation removes the component"); they are factors of the tensors T_P and
  hence of the contractions 𝔞_g. The reduced convention at an 𝐑-step is therefore: **on a term of the multilinear
  expansion in which a slot of g holds an insertion of an attached species (or g has such a member), 𝔞_g := 0 and
  the group is an attached insertion** (the notes: gauged activity = the part without attached content,
  #PC4.14.4-1.2, -4.5.4-1, -4.5.4-4). Still to read: S.10's proof (lines 1594–1633) for how 𝔞_g and D_g depend on
  the letters in the slots, whether E^𝐑(C; ℓ₀) is taken on the term without insertions in the slots, and what
  S.10(v) says of a group which holds a wrap or a deviation insertion in a slot.

## Architecture of the Section (as of 20:15)

- 18.1 *The attached species is not split.* Convention at the T-steps and at the 𝐑-steps; Lemma: the identities of
  the step for any choice of the subtracted scalars; S.9 and S.10 hold; the activities c_𝒢 and 𝔞_g contain no
  attached and no cross content: they are multilinear in the fresh constituents, the deviation insertions (as
  functions), the wraps, and the occurrence factors of the previous gas.
- 18.2 *First-order bounds for the cluster series.* Lemma: root form (162Mσ(W)δε̂) and summed form
  (Σ_𝒢|δc_𝒢|e^{a°(𝒢)}), and the form for a second difference (terms on ℓ minus terms on ℓ₀).
- 18.3 *The masses of a young pair.* Definitions of P(X), Ȳ_X, ε̄_A, M^×, the enlarged amplitudes.
- 18.4 *Proposition S.19.* On a young matched pair, K ≥ K_Q: (a) activities: δε̂_i ≤ D^cw_K by the recursion of
  S.16(i), which applies because of 18.1; (b) weights: Σ_{Γ hits W}|Φ°^B − Φ°^A| ≤ q_Kσ(W), change of a member's
  factor ≤ C^×_Q q_K w(W), C^×_Q := 32/(29eν); (c) local terms: second difference ≤ (relative) × exposed mass;
  (d) the attached insertions: the carry of differences; (e) the rates
  s^W_K := [L^dC^tr_Wε₁θ̃^{k−m_W} + 2(c̄^W_K + C^×_Q q_K + c_E q_K)ε̄_A + 𝐑-part]/C_M,
  s^{W,0}_K := s^{W,tr}_K + 2τ^w_K + 24(m_W + 1)(τ^w_K + τ^×_K) + D-terms + C^×_Q q_K M^×; summability.
- Then: S.14(f) is restated by reference to S.19; the paper's `sec:reference-gas` gets the convention; the
  paper's `prop:young-pairs` cites S.19; appendix of conditions: K ≥ K_Q on the young pairs.

## State

- **19:40 (time from `date`; the times in the headings above are approximate, all between 19:20 and 19:40).**
  `F26_SECTION_DRAFT.tex` holds, in final form: the introduction of the section; subsection "First-Order Bounds
  for a Reference Gas" with Lemma `lem:first-order` (a), (b), (c) and its proof (arithmetic checked:
  2n(W)‖δc‖; 162Mσe^{2a°}; C_II = 10368²M²/(32ν) = 2⁹·3⁸M²/ν); subsection "The Activities Contain No Attached
  Insertion" with the convention (a group is *attached* if it is attached to a large-field region of its step or
  contains a part of an insertion of an attached species; attached and cross groups have c_𝒢 := 0), the paragraph
  on S.9, and Lemma `lem:activities-content` (T-steps) with proof.
  **When the section moves into the supplement, the paper's `sec:reference-gas` (line 1359) must say "for a cross
  group and for an attached group we put c_𝒢 := 0", with the definition of an attached group.**
- `FINDINGS.md` F26 has items 4–6 (the convention; S.9; the 𝐑-steps of S.10; undefined ε̄_A etc.).
- **Next (in this order):**
  1. *The 𝐑-steps.* Sources: the two-loops note (ac5f11dda03c) #825 (line 695) to #844-9 (line 727): the 𝐑-made
     groups on one loop with carried insertions 𝔅(g) in their slots and members 𝒲_g; the weight e^{ν_rσ̃(D_g)};
     #841-1: the groups holding a first non-deviation member W₁ are summed from one traversal and add at most
     ε^r_k w(W₁), ε^r_k := e^{−p₀(g_k)/4}, to the species total of W₁; #844-7: the register grows at an 𝐑-step by
     (1 + C_ϑϑ_k)(1 + ε^r_k)(1 + C_att y^R_k), under C_δc̄S_R + (1 + C_ϑ + C_attC_y)S^R ≤ log 2. Supplement:
     S.10(v) "the cross groups" has the same count for the cross and the wrapping species (factor y^𝐑_k; the number
     of cubes is paid from the weight, λ_n). To write: (a) the convention at an 𝐑-step: an eligible group one of
     whose slots holds, or one of whose members is, an attached insertion of the labelled term has 𝔞_g := 0 and is
     attached; (b) its mass: the groups which contain a given attached insertion W sum to at most y^𝐑_k w(W),
     with the payment of the number of cubes (needs a share of the weight of W: check `eq:weighted-mass` and
     whether S.9's allocation leaves one, or use the rate λ_n as for the cross species); (c) S.9(ii) with the
     factor 1 + y^𝐑_n at the 𝐑-steps and the condition 2c̄S_R + Σ_n y^𝐑_n ≤ log 2; (d) Lemma: the scalar
     activities 𝔞_g and the weights Ψ(S), E^𝐑, E^{𝐑,∂} depend on no attached insertion of the labelled term and
     on no insertion on two loops.
  2. *The masses of a young pair* (LF #5.39–#5.41, lines 2500–2525 of the large-field note): P(X), Ȳ_X, Ȳ^R_X,
     ε̄_A := sup_{j>k−m_W}ε^{(2)}_A(j) + ε^R_A, M_i, D_i, the carry (D), b_wrap, D^{w,LF}_K.
  3. *Proposition S.19* as in the architecture above, then the edits of S.14(f), the paper, the appendix.
- **19:50. The 𝐑-steps, after reading S.10's proof in full and the two-loops note #825–#844 and LF #5.45–#5.50:**
  - *Slots need no new convention.* In S.10 a polymer is "a connected union of class components, localisation
    domains, and the domains of the pieces of the loops' letters" (Lemma `lem:loop-localisation`), each piece "a
    function of the external data and of the data of the components in its domain". An insertion attached to a
    surviving (second-class or unchanged) component depends on the data of that component, so a polymer which
    holds it in a slot contains that component, and its group is not eligible: 𝔞_g = 0 already. The attached
    insertions in the slots of an *eligible* group are those of the first-class components inside its polymers
    (S.10(iii): "the product of the masses e^{2A_j(Z)} of the attached insertions of the old components inside
    the polymer"); these are internal to the gas and their lineage ends (S.10(vi)). So 𝔞_g of an eligible group,
    F(P), and hence Ψ(S), E^𝐑, E^{𝐑,∂} depend on no attached insertion of a surviving component. To state as a
    lemma with this reason.
  - *Members are the missing case.* D_g := contraction with the members − 𝔞_g × word with the members; S.10(v):
    "‖D_g‖ ≤ B(g)Π_W‖W‖ ... and D_g is a deviation insertion when every member is one"; cross and wrapping members
    are treated ("the groups assigned to a member add at most y^𝐑_k times its mass"). **An eligible group with a
    member attached to a surviving component is not treated**: it is an attached insertion which continues the
    lineage of its first attached member W₁ (two-loops note #840), and the groups holding W₁ add at most
    ε^r_k w(W₁), ε^r_k = e^{−p₀(g_k)/4}, at the 𝐑-step (#841-1), the extent Δ_g and the units being paid by the
    polymers, by the margin of (1.89), and by the half of the reserve e^{νσ(W)} which the size σ̃ does not take
    (#843-1, #844). To add to S.10(v) and S.9(ii) (factor 1 + y^𝐑_n at the 𝐑-steps in the carry; condition
    2c̄S_R + Σ_n y^𝐑_n ≤ log 2 in place of 2c̄S_R ≤ log 2, or exp(4A_j(Z)) in place of exp(2A_j(Z))), with the
    weight accounting re-derived in the supplement's units (`eq:weighted-mass`; the allocation of the reserve in
    the proof of S.9(ii), "merged parts", spends all of νσ at a merge of a T-step, so the 𝐑-step needs its own
    allocation: read the two-loops note's (6B) "The rates" and "The members' weights" before writing).
  - *The comparison at the 𝐑-steps* (LF #5.46–#5.49): the activities are built from the operations 𝐓′, the
    factors V(Y), and the slot words; all three are interpolated together (convexity of the bounds of moduli);
    the differences of 𝐓′ and V(Y) are b̄_K := max(b̄^{𝐓′}_K, r^V_K) relative, the slot words' difference is the
    words' own (transports, internal attached insertions), "already counted"; the marked-cluster bound gives
    2C_ptC_XC_KP b̄_K per point of the renormalised component, and the q = 0 clusters at a second-class component
    2C_ptC_XC″_Ψ b̄_K. LF's terms are *histories* (a component which is renormalised is part of the term), and
    "in a pair with k − j₀ < m_W every 𝐑-operation is at a step > k − m_W". The supplement's S.14(f) has the
    resulting term 2C_ptC_X(C_KP + C″_Ψ)L^d b̄_K/C_M; C″_Ψ is not defined there (the notes: m^w_Ψ := 2C″_Ψe^{2C″_Ψ},
    #T4.43).
- Earlier state line (superseded): nothing written in the TeX. `FINDINGS.md` F26, `PROGRESS.md` (19:20), `SESSION_HANDOVER.md` (19:20)
  record the open item. Next: read S.9 (`prop:attached`, line 1494), S.10 (`prop:r-operation`, line 1558), and
  S.16(i) (lines 2135–2177) of the supplement; the paper's large-field step (`sec:large-field-step`) for the
  definition of 𝓔_k and of the local terms on a term with large fields; then write.
