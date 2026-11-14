# Triage of lf-p13b2-20261108-r26

## Verdict

- r26 was a narrow round of 13b2, at LF 2fb3f5358bf1, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** m1, in #4.567-2. Its premise, taken from #4.168, was that the data of the form's background U^0_{k,Z} contain exp(ig_kB). That premise conflicts with LFR II (1.19) and #4.57, so the bounded dependence is null.
- **Trivial:** t1 (G^c undefined) and t2 (reused names ε₀, ε, α₁, each qualified only in context).
- Every other named step and consumer was re-derived CORRECT. Round 25's t1–t6 are confirmed repaired, t4 only in part (now t2).
- The round is **not clean**, so the count stays at 0. The next round, r27, is narrow.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.168 (source), new #4.168-1; #4.567-2; #4.567-2-1 deleted; #4.564 | The form was said to depend on the couplings through its background | #4.168: "three ways". #4.168-1: the form carries no coupling at fixed B. Its background U^0_{k,Z} is U″_{k,Z} at the data M^·(U_0) on Ω″^{∼2}_{h+1} and V″ = V off it, which do not contain exp(ig_kB) (LFR II (1.19), p.360 l.46–53; #4.57). The factor g_k² of (1.20)'s quadratic term (p.361 l.5–6) cancels the weight g_k^{−2} that (1.14)–(1.15) give A(ζ₀, U″_k) (p.359 l.36–44). #4.567-2 now records this on the class, as the same function of B and of the data built from U_0. #4.567-2-1 is deleted. #4.564: "#4.567–#4.567-2 those of the couplings" |
| t1 | #4.561.1-1-0, new #4.561.1-1-0-1 | G^c used without definition | The table fork entered G^c := G·exp(𝔤), with 𝔤 hermitian, closed in GL(N, ℂ), in row #T12.27-1-2 (table 70e85474db56, 11:55). So the LF cites that row and does not restate it: "G^c is closed in GL(N, ℂ) (#T12.27-1-2), so exp maps a neighbourhood of 0 in 𝔤^c onto one of 1 in G^c in the subspace topology". An interim LF definition (d4267c01cd77) was replaced by this citation before any launch. The line was split at the sentence boundary to keep it ≤ 600 characters |
| t2 | #4.517-1-0, #4.560-1.1, #4.561-1-2; #4.561; #4.561-1.2, #4.560-1.1.2, #4.563-1.1 | Reused names | VAR's ε₀ is renamed ε₀^{VAR} := VAR's ε₀ (#T11.19), "not #T3.1's exponent ε₀", at all four places that use it. #4.561 now reads "PBG's α₁ of (3.37) and α_J of the pair class (#4.60), not CRE's α_{1,m}". LFR I Proposition 1's ε now reads "at its ε =" in all three places, and #4.561-1.2 says "not the spacing ε" |

## Adversarial pass over 13b2 (promised before the next full round)

- **Readings against source definitions.**
  - U^0_{k,Z}: LFR II (1.19) and p.360 l.52–53 were re-read; its data are as stated in #4.168-1.
  - The weight of the form was checked at (1.14)–(1.15) (p.359 l.30–44), not at #4.159 (which concerns (g_k(·))^{−2} of p.365). The first draft of #4.168-1 cited #4.159; that citation was corrected before the build.
  - The convention for 𝔤 comes from #T11.26 (log U = iA, A hermitian). The first draft of the G^c definition read G·exp(i𝔤), which for a hermitian 𝔤 is G itself. The table fork flagged the same thing; the LF now cites #T12.27-1-2's G·exp(𝔤).
  - The earlier readings (u's orientation, VAR's ε₀ through (113) and (173), CMP98 (78) and (106)) were re-checked in rounds 23–26 and are unchanged.
- **Class coverage against the real items.**
  - The real *The couplings.* now has three routes, and the class covers each: the weights and the data in #4.567–#4.567-1; log d and E_k(Λ) in #4.567-2, by the Cauchy note's #C8.6.3–#C8.6.7, whose terms are analytic on the class (#C8.6.2-16, #4.169-1). E_k(Λ) = (−½d(𝐠)log g_j^{−2} + log σ₀)abs(Λ^{(j)}∖G₀) (#C8.6.2-15) does not depend on the configuration.
  - The form has no coupling route.
  - The actions and the forms are covered by #4.565–#4.566, and log d's run difference by #4.169-1.
- **Thresholds against (T-c).** Every smallness used in 13b2 was traced to (T-c) (#4.561, #4.561-1.2) or derived from it:
  - #4.561.1-0: 27c_avα̂₁ ≤ 1 and c_avε′_k ≤ ⅛, from C_{V′}ε₁′ ≤ ½.
  - #4.561.1-1: abs(V^e − 1) ≤ ½; #4.561.1-1-0: abs(X₀) ≤ ¼, from abs(B^e) ≤ 2c_avε′_k ≤ ¼.
  - #4.561.1-1.1: B̃′ small, and #4.561.1-1.3-1: Proposition 9 at ε₂^{AL}, by #4.561-1-2–#4.561-1-2-1.
  - #4.561.1-1.3-2: 128dε₂^{AL} ≤ 1. #4.517-2: 256dε₂ ≤ 1. #4.517-1: REG (1.71)'s smallness of ε₂.
  - #4.563-1.1: e^{4abs(B^e)} − 1 ≤ 16c_avε′_k, by 8c_avε′_k ≤ 1. LFR I Proposition 1 at its ε = 20C_{V′}ε₁′.
  - #4.563-2.1: 8C₀^{ms}ε₁′ + 16ε₂ ≤ 1. #4.563-3-0: 4C₀^{ms}ε₁′ + 3ε₂ ≤ ½. #4.563-2.2: ε₂ < α₁, C^c_Jε₁′ < α_J, 2ε₁′ ≤ 1.
  - #4.567-1: ρ_V ≤ ¼ and abs(X) ≤ ¼.
  - #4.565–#4.565-0: #4.48.0 at ε_r = ε₁′.
  - The only conditions outside (T-c) are #4.563-3-1's 2b₂ḡ² ≤ 1 and #4.565-0's (1 + β₀)ḡ ≤ 1. Both are smallness conditions on ḡ from #4.41-1-1.
  - All are present.

## Checks

- **m1, re-derived.** (1.20) expands A(ζ, U″_{k,Z}) = A(ζ, exp iη𝐇″(g_kB)U^0_{k,Z}) around U^0_{k,Z}, which (1.19) defines from M^·(U_0) on Ω″^{∼2}_{h+1} and V off it. Neither contains B or a coupling. H″_{1,k,Z} is the linear term of 𝐇″ at that background (#4.57).
  - The quadratic term is ½g_k²⟨H″B, Δ₁(ζ)H″B⟩. In the action it carries g_k^{−2}, by (1.14)–(1.15).
  - So the form (1.21) and the small form are functions of B and of U_0's data only. Each run's U_0 differs as data, which *The result for the forms.* compares, not as a coupling.
  - On the class the same functions are continued, so no coupling term arises there.
- **Consumers.**
  - #4.564 and #4.568 no longer cite #4.567-2-1.
  - Grep over the YM4 .md files: #4.567-2-1 survives only in SESSION_HANDOVER.md (history) and in the old review snapshots.
  - #4.168's "four ways" survives only in the stale labels file (LABELS_LF_AND_TABLE.md row 605), which the relabel refreshes.
  - #4.160 and #4.569 refer to the form's run difference, which is unchanged.
- **Packet of #4.168.** #4.168–#4.168-1 lie in packet 50 (open, #4.157–#4.169), so no done packet changes.
- **New tags.** #4.168-1, #4.517-1-0, and #4.561.1-1-0-1 were unused before (Grep over the YM4 .md files; balaban_proofs/ too for the first two).
- **New symbols.** ε₀^{VAR} has no clash; the table's #T3.9 and #T11.19 call it "VAR's ε₀". It is in r27's allow_defs. G^c is the table's (#T12.27-1-2), not defined in the LF.
- **Table fork's report, 11:55 (handover).**
  - "#4.51-2's {#D.U^X_t} has no ':='": repaired as bookkeeping. It now reads "U^X may be taken as {#D.U^X_t} U^X_t := the curve that starts at U^X(V′^A₀) …" (13a, done; no change of meaning).
  - "#4.561.1-1-0 prints G·exp(i𝔤)": this was the interim draft, now replaced by the row citation.
- **Line lengths.** #4.168 470; #4.168-1 472; #4.517-1 371; #4.517-1-0 294; #4.560-1.1 577; #4.561 421; #4.561.1-1-0 382; #4.561.1-1-0-1 355; #4.561-1-2 487; #4.561-1.2 576; #4.563-1.1 383; #4.564 299; #4.567-2 385 characters. CR count 0.

## Consolidation of 13b (user, 12:03: "Check 13b for garbage you have added during repairs and consolidate")

All of 13b was re-read: #4.52-1–#4.52-1-2, #4.517–#4.517-2, and #4.556–#4.568. The following text was added during repairs and is now deleted or replaced by a citation.

| Line | Deleted or replaced | Why |
|---|---|---|
| #4.517 | ", not #4.536's gauge factors u" | Aside. u is defined in the same sentence |
| #4.517-1-0 | "{#D.ε₀^VAR} ε₀^{VAR} := VAR's ε₀ (#T11.19), not #T3.1's exponent ε₀" becomes "(p.280 l.51–52; #T3.9)" | The table's #T3.9 now defines ε₀^{VAR}; the note cites the row |
| #4.560-1.1 | "linear in ε₀" becomes "linear in ε₀^{VAR}" | The same parameter as (6)'s, now one name |
| #4.560.1 | "It reads plaquettes only, not the currents of CRE (2.36)–(2.37)." | Aside |
| #4.561 | "PBG's α₁ of (3.37) … not CRE's α_{1,m}" becomes "α₁ and α_J of the pair class (#4.60)" | #4.60 defines α₁; the disambiguation was an aside |
| #4.561.1 | "or the minima V′^X₀; V′V₀ is a pointwise product, unlike #4.44's V′V_{Λ^c}, which joins data on Λ and on Λ^c" becomes "a pointwise factor, not the variables V′ on Λ (#4.559-1.1)" | Aside shortened to the one clash that matters |
| #4.561.1-1.1 | "γ₀ LFR II's positivity constant (p.358 l.4), not RG I's (#T3.14)" becomes "with LFR II's γ₀ (p.358 l.4)" | Aside |
| #4.561.1-1.3-1.1 | ", ε₂ of #4.561-1" | Restated definition |
| #4.561-1.2 | ", not the spacing ε" | Aside |
| #4.563-2.1 | "so the field strength moves by ≤ 3ε₂/a_j², which is ≤ 3ε₂ in the units of a_j = L^jη in which (b)'s plaquette bounds are read" becomes "a move of the field strength by ≤ 3ε₂/a_j², a_j = L^jη" | Restated units; #4.563-2.2 writes its plaquette bounds over a_j² |
| #4.563-2.2 | the second "by ε₂ < α₁" | Repeated in the same line |
| #4.563-3-0 | "so no dimension factor enters" | Aside |

- **Kept.** Each of the following remains because it carries a step or a real name clash:
  - "(not LFR I's U_0)" in #4.517-0-1 (VAR's base U₀ against LFR I's U_0);
  - "the C₁ and C₁′ of (T-Λ) are those of (c)" in #4.561.1-2;
  - REG's norm convention #4.563-2-1;
  - the readings marked "inferred, not printed".
- **Size of 13b.** 32,506 characters at r26's snapshot, 32,483 after the r26 repairs, and 32,011 after this consolidation (−495 in all). No mathematics changed.
- **Table re-pointing.** The table fork moved G^c into its own row, #T12.27-1-2-1, and #4.561.1-1-0 now cites that row. The fork confirmed that #T12.9-1's entry pointing to #4.561.1-1.3-1.1 is still right (that line was not split).

## Recheck of the built packet (user, 12:06: "Recheck the package again")

Every line of the r27 packet_argument.md (74 lines) was re-read and re-derived as a referee would read it. The arithmetic of #4.561.1-1.3-2, #4.561.1-2, #4.563-1.1, #4.563-2.1-1, and #4.567-1 was redone. Three defects were found and reworded in place:

| Line | Defect | Repair |
|---|---|---|
| #4.561-1-2 | ε₀^{VAR} is first used in the packet without its definition (#4.517-1-0, which cites #T3.9, is not in this packet) | "through ε₀^{VAR} (#T3.9) and C₁ε₁" |
| #4.563-3-0 | After the consolidation deleted "so no dimension factor enters", the colon before "abs(X^{−1}) ≤ 2" no longer read as the reason | "≤ abs(X − 1)² in the operator norm, as abs(X^{−1}) ≤ 2, since …" |
| #4.567-2 | "they" in its second sentence had "the form" as its nearest antecedent | "the couplings enter on the class" |

- **Checked and sound.**
  - The weight in #4.168-1 against #4.157's −A((g″)^{−2}ζ₀, U″_k): by (1.14), the part ((g″)^{−2} − g_k^{−2})ζ₀ stays unexpanded in the action (the weight route), and the form comes from the g_k^{−2}ζ₀ part with coefficient 1.
  - The G^c membership of V^e(tz) and the openness argument with #T12.27-1-2-1's G·exp(𝔤), using i𝔤^c = 𝔤^c.
  - #4.563-2.2 still states ε₂ < α₁ once, before "the move 3ε₂ < 4α₁".
- The packet's brief, definitions, and kind files were read as well.

## Definition audit of the packet (user, 12:10: "Did you also check whether every object is actually defined?")

- **Not done before.** The earlier passes checked arithmetic, citations, and new symbols only. The builder's check catches double definitions, not missing ones, and the table fork's "0 missing" covers only the {#D.} anchors.
- **Method.**
  - Every object in packet lines 21–74 (the lines under review) was listed.
  - Each was traced to a definition: an LF {#D.} anchor (920 anchors listed), an LF ":=" or definitional sentence, a table row, a cited print source, or the Cauchy note's statement of (LF).
- **Findings.**
  - **w^A and w^B in #4.567 were undefined.** #5.47's w^A and w^B are other objects (slot words). Repaired: "w^X the action's weight (#4.160) at run X's couplings (#4.41-0)".
  - **G₀ clash.** The table's new #T12.27-1-2-1 used G₀ for the identity component of G. In the LF, G₀ is LFR II's axial-gauge graph (#4.44-0), used at #4.561.1-1.1. The fork renamed it G^∘ (table a105d1cad22e).
  - **G is connected, so G^∘ is not needed.** The identity-component clause came from this session's own point on #T12.27-1-2 (12:01), which was wrong to raise.
    - BETA treats compact simple G (#BP.9) and connected semisimple G (#B10.1), and uses connectedness at #B10.36. CMP98 obtains G as e^{i𝔤} (p.020 l.30). RG I prints only "compact … semisimple" (p.251 l.30–p.252 l.2).
    - For connected G, G·exp(𝔤) = ⟨e^{i𝔤^c}⟩. It is connected; it is closed with Lie algebra i𝔤 ⊕ 𝔤 = 𝔤^c, so it contains e^{i𝔤^c}; and it lies in ⟨e^{i𝔤^c}⟩, since G = e^{i𝔤} and exp(𝔤) = e^{i(−i𝔤)}.
    - Sent to the fork (12:17). Applied: #T12.27-1 reads "compact, connected, and semisimple", and #T12.27-1-2-1 has no G^∘ (table 9448f31e5176, labels 21aad62e3865, verified). G^∘ and "identity component" occur nowhere in the table or the LF.
  - **𝔤^c** was defined only in passing (#A.9.4). It is now table #T12.27-1-2-0.
- **Traced and defined.**
  - In the LF: δ′_k = g_kA₁p₁(g_k) (#4.177, LFR I p.183 l.2, p.184 l.18); χ′ (LFR I (1.82), #2.15, #3.21); V′^X₀ (#4.44's minimiser); ū₀ (#4.52); C_p (#4.462); ℋ and abs(ℋ)_y (§4(c)); b₂ (CRE (2.6), #4.41-1-1); D_U, r_{1,q}, Ṽ_{j,Z}, U^r, Y, ρ_V, and W_d (in their own lines).
  - In the table: 𝔹_k(Λ) (#T11.27 via #T11.29); c₂ (#T11.22-1); C_b (#T4.33).
  - Elsewhere: C_h (the Cauchy note's (LF), s^{LF}_n ≤ C_hθ̃^n); Ω″^{∼2}_{h+1} (LFR II's domain).
  - Every other symbol carries an LF anchor or a table row.

## Read-through before launch (user, 12:24: "Do you think r27 is ready?")

Lines 21–74 of the packet were re-read, step by step. Two weak points were found and repaired:

- **#4.561.1-1-0: an unproved premise.** "V^e(tz) being in G^c as the averages V_k(tz) of the G^c-valued 𝐔(tz) are" was asserted. It was r25's t5, repaired then only by stating it.
  - Repaired in place by an identity-theorem argument. log V^e(z) is analytic on |z| < 25 (#4.559-1, #T11.30-0; |V^e − 1| ≤ ⅛ by #4.561.1-0). For real z near 0, V^e(z) ∈ G is near 1, so log V^e ∈ i𝔤 (#T11.26-1). So its component in a complex complement of 𝔤^c (#T12.27-1-2-0) is analytic and vanishes on a real interval, hence on the disc.
  - This needs neither G^c's closedness nor the averages' G^c-membership. #4.561.1-1-0-1 (the BCH openness step) was deleted.
  - Consumers: #4.561.1-1.1 uses exp iB^e(z) with B^e 𝔤^c-valued, unchanged. #4.563-1 uses V_k(z) = e^{iB^e(z)}V_k(0), unchanged. No other line cites #4.561.1-1-0 or #4.561.1-1-0-1.
  - Line length 446 characters.
- **#4.564: "the Lemma" had no tag.** It now reads "Lemma (Two Constants) (#4.557)". The 15/16 power of #4.565's exponent (1 − ε₀)/3 gives #4.565-1's 5(1 − ε₀)/16, as checked.
- **Checked and found sound.**
  - #4.563-2.1's 2 + 8C₀^{ms}ε₁′ + 16ε₂ ≤ 3, by (T-c)'s 16C₀^{ms}ε₁′ + 16ε₂ ≤ 1.
  - #4.563-3-0's abs(X^{−1}) ≤ 2 at abs(X − 1) ≤ ½.
  - #4.567-1's (9/16 + ¼) < 1.
  - #4.561-1-2's monotone comparison of the base-1 problem with the disc problem.
- LF cf6b8d8c92ec → 92b3e62044ba. The spec has been updated: claim (iii) and (iv), the named steps, question 3, the permitted rows #T11.26-1, #T12.27-1, and #T12.27-1-2-0, the textbook list without closedness and BCH, and the provenance. The table fork was asked to relabel and to re-point #T12.27-1-2-1's "used at" (12:27).

## Analyticity of the data on the disc (user, 12:31: "Is analyticity proven or cited from anywhere???")

- **The gap.** At real z the note checks that the line lies in Bałaban's domain (#4.560-1.1.1). At complex z, the analyticity of D(z) = M^·(𝐔(z)) on |z| < 25 was attributed to Bałaban's extension (#4.559-1, #4.563-1, #T11.30-0). He states that extension for 𝐔 ∈ U^c_k(Z, α_{0,k}, α_{1,k}) (LFR II p.358 l.23–30), and no line checked that 𝐔(z), whose field is up to 26 times the class bound, lies there. The read-through at 12:24 named this as a remaining question instead of repairing it; that was wrong.
- **Repair.**
  - New #4.561.1-0.0-1 (tag checked unused): at the blocks of a layer q, the entries of D(z) are the q-th averages M^q (#T11.7-0-2) of e^{iξ(A′_R + zA′_I)}U. These are analytic in the 𝔤^c-valued field A′_R + zA′_I, affine in z, by CMP98 Proposition 6 (#T11.6-1; p.043 l.3–10, re-read in the corrected file).
  - Its hypotheses hold in the units of the q-blocks (#T11.27-1). U satisfies (52), abs(U(∂p) − 1) < α₀η² with η = L^{−q} (p.026 l.12–15), at α₀ = r_{0,q}, since CRE (2.34) at the radius r reads r_{0,q}ξ²(L^qξ)^{−2} = r_{0,q}η². And abs(A′_R + zA′_I) < 26r_{1,q} by (2.39), in the normalisation U′ = e^{iηA′} of (158), since ηA′_{CMP} = ξ(A′_R + zA′_I).
  - #4.561 (T-c) adds "26(α̂₀ + α̂₁) below the smallness of α₀ and α₁ in CMP98 Proposition 6 (#T11.6-1)". It holds for γ small, uniformly in k and K, by #4.562-1–#4.562-1.1, since it bounds α̂₀ + α̂₁ by a constant.
  - #4.561.1-1-0 cites #4.561.1-0.0-1 for V_k(z). #4.563 reads "So, the data D(z) being analytic (#4.561.1-0.0-1), the minimisers, …".
  - Proposition 6's bound (164), O(1) times the field, agrees with #4.561.1-0.0's c_av bound. (158)'s "may be also described by" is not used.
- **M^· undefined in the LF.** The definition audit missed it. #4.561.1-0.0-1 now cites the table's new #T11.7-0-2 (RG I (1.15), p.262 l.49).
- LF 92b3e62044ba → 7e312ac59d3e → 549db53776d0 → aa91a5e94142 (#T11.6-1 cited). The table fork added #T11.6-1 and relabelled: table 9ac099322946, labels 967a4afee9d8, verified.
- Lines: #4.561 464, #4.561.1-0.0-1 451, #4.561.1-1-0 441, and #4.563 481 characters. CR count 0.
- **Spec.** Claim (iv), the named steps (#4.561.1-0.0-1 and #4.563 added), question 3, CMP98 Proposition 6 with (158)–(164) in the permitted print, the rows #T11.6-1, #T11.7-0-2, and #T11.27-1, and the provenance.

## Pre-check of lf-p13b2-20261108-r27 (narrow)

- **Spec.** specs\spec_p13b2_r27.json, prior r26.
- **Changed since r26** (the gate's list, 16 tags, all re-read in place): #4.168, #4.168-1, #4.561, #4.561.1, #4.561.1-1-0, #4.561.1-1-0-1, #4.561.1-1.1, #4.561.1-1.3-1.1, #4.561-1-2, #4.561-1.2, #4.563-1.1, #4.563-2.1, #4.563-2.2, #4.563-3-0, #4.564, and #4.567-2, plus #4.567 (w^X defined, from the definition audit). The consolidation's deletions are among them.
  - #4.168–#4.168-1 are context, in packet 50.
  - #4.517-1 and #4.517-1-0 (a split and a rename only) and #4.560-1.1 and #4.560-1.1.2 (a rename and a rewording only, in 13b1, done) are bookkeeping, outside this packet.
- **Named steps.** The 15 changed lines of 13b2, #4.567 included, with their consumers #4.561.1-1, #4.563-1.2, #4.563-2.1-1, #4.567-1, and #4.568.
- **Consumers of the deletions.**
  - #4.563-2.2 reads the move as 3ε₂ against 4α₁ in plaquette bounds written over a_j², so it does not need #4.563-2.1's restated units.
  - #4.563-2.1-1 reads 3L²ε₂/a_j² directly.
  - Nothing else cites the deleted clauses.
- **Cited lines re-read.**
  - LFR II p.359 l.30–44 ((1.14)–(1.15)), p.360 l.41–53 ((1.19)), and p.361 l.1–29 ((1.20)–(1.21)).
  - LF #4.57, #4.157, #4.159, #4.160, #4.169-1, and #4.60.
  - Cauchy #C8.6.2-14–#C8.6.7-2.
  - Table #T3.1, #T3.9, #T6.23, #T11.19, and #T11.26.
- **Size.** Argument 23,680 characters, 28 files. Snapshot: LF aa91a5e94142, table 9ac099322946, labels 967a4afee9d8 (rebuilt at 12:38, after the analyticity repair).
  - #4.567 (571 characters) is now a named step. #4.561.1-1-0-1 is deleted and is no longer a named step.
  - The gate without the prefix lists 18 tags: the list above, without #4.561.1-1-0-1, and with #4.567, #4.561.1-0.0-1 (new), and #4.563 (one clause). All of them are re-read and in this pre-check.
  - #4.563's consumers #4.563-1–#4.563-3-1 are unchanged: the clause states only the input their analyticity already used.
  - The context #4.198-1 was dropped (no named step of this round consumes it).
  - #4.168–#4.168-1 were added as context.
  - #4.517 is still cited by tag.
  - Before this round's repairs, the part's extracts measured 21.9k under review. #4.567-2-1 was deleted, and the net change to the reviewed lines is under +0.2k.
- **Full round.** The full round must carry #4.517–#4.517-2 as well (about +2.3k). To fit, its context will be cut to #4.559–#4.560-0, with #4.168–#4.168-1 cited by tag, and the packet re-measured.
- **Symbols.** ε₀^{VAR} is the table's (#T3.9) and G^c the table's (#T12.27-1-2-1); the LF defines neither. The definition check passed in the build.
- No known weak point and no OPEN is in the part.
- **Launch is on hold at the user's request** ("Pause before launching", received during the repairs, between 11:50 and 11:58).

## Messages

- 12:01, to the table fork:
  - the LF SHA a51211571c45;
  - the new tags #4.168-1, #4.517-1-0, and #4.561.1-1-0-1, and the deleted #4.567-2-1;
  - the new ε₀^{VAR}, for the table;
  - the two reported defects, now fixed;
  - a point on #T12.27-1-2: "compact connected" is not needed, and "generated by e^{i𝔤^c}" gives only the identity component for a disconnected G. This point was wrong to raise, since G is connected throughout (see the definition audit); it is withdrawn in the message of 12:17.
- 12:15, to the table fork: the LF SHA cf6b8d8c92ec (#4.567: w^X), the G₀ clash, and 𝔤^c. The fork's replies (verified): table a105d1cad22e, labels a8a8f16ead42 (G^∘, #T12.27-1-2-0, w^X in #T12.9); then 13ff46d49076 / 13a273bfc9f7 (BETA rows only), verified at 12:17; then b0bf93b89fc9 / 727b86e7faa6 (#T12.27-1-2-0 notes BFWL's g^c).
- 12:17, to the table fork: G is connected (#B10.1, #B10.36, CMP98 p.020 l.30). State it in #T12.27-1 and drop G^∘ from #T12.27-1-2-1, with the re-derivation G·exp(𝔤) = ⟨e^{i𝔤^c}⟩.

## SHAs

- LF 2fb3f5358bf1 (r26's snapshot) → d4267c01cd77 (m1, t1, t2) → a51211571c45 (G^c cited from the table; #4.51-2's ":=") → bd3d7b47f106 (consolidation; ε₀^{VAR} and G^c cited from #T3.9 and #T12.27-1-2-1) → 539b2d0ef659 (recheck: three rewordings) → cf6b8d8c92ec (definition audit: w^X in #4.567) → 92b3e62044ba (read-through: #4.561.1-1-0 by the identity theorem, #4.561.1-1-0-1 deleted, #4.564's Lemma tag) → 7e312ac59d3e → 549db53776d0 → aa91a5e94142 (D(z)'s analyticity by CMP98 Proposition 6, #4.561.1-0.0-1; (T-c); #4.563; #T11.6-1 and #T11.7-0-2 cited). D2.7 ad9121e3d079 → 5dedf785fb28 (15.6(d) "at every datum of 𝐁_k", at the two-loops session's request, re-derived) → 4a09176784cc (that phrase used "datum" both for the whole real configuration and for one bond's value; it now reads "the data V_k whose gauge-fixed deviation differs from that of a real datum V_k⁰ on the support by less than 2r^{ext}_k at each bond of 𝐁_k"; the same point was sent to the two-loops session for TL #167 and #167-3).
- Table ba5a8ca4e285 and labels 8a44626e2ae3: the table fork relabelled at a51211571c45. The tag set has not changed since then: the consolidation only deleted text.
