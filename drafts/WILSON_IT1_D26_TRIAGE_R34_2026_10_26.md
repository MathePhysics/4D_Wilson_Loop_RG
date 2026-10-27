# D2 map: triage of round 34

Round 34 ran twice. The first run used the isolated harness, where the reviewers had no tools and saw only the packet (reports `it1-*-20261026-r1\review.txt`, 00:26–00:35, 26 Oct). At the user's request ("Restart them, run them locally in the app") it was re-run as local app sessions with file access. Reports, read in full:
- `it1-rc-p6-20261026-app-r1\review.md`: R-c Pass 6, the collar step;
- `it1-hc-20261026-app-r1\review.md`: hypercubic covariance (RTR_PROOF_PASS, map D2.3(5) *Independence*);
- `it1-rh-20261026-app-r1\review.md`: slot values at complex backgrounds, R-𝐇 (map l.970–984).

This triage is based on the app reports. The harness reports were not re-triaged.

## Open after this round

- **Row 35, closed after triage:** analyticity of 𝐇^{(j)} and 𝐇_{1,Ax} on 𝒰_j(C).
  - It was first recorded as a reading, because PBG's (3.36) and (3.38) have no counterpart in Ũ^c.
  - It is now derived, since 𝐇^{(j)} depends on 𝐔 only through its data M^·(𝐔).
  - VAR §F (p.307) and CMP 98 Prop. 3 then give analyticity in the complex data.
  - The complex external fields of the mean-value step lie in PBG's class (3.35)–(3.38), by VAR Thm 1 (9)–(10) and VAR (19), (173).
  - p.251's axial transfer is Bałaban's.
  - Map l.972 paragraph *Analyticity on 𝒰_j(C) (derived)*; READINGS_RECHECK row 35.
- **OPEN, unchanged:**
  - the k = 1 base points on Ω₁∖Ω₂ (map l.976);
  - the gauge frame of σ_j (D2.2(4)(d)).
- **Reversal of a user decision:** hypercubic covariance is withdrawn, and with it "one counterterm for all planes" (accepted 00:05, 26 Oct). D2 keeps κ_v per orientation and ζ_{v,w} per corner pair, and uses only their averages over C's own orientations and corners. No bound changes.

## rc-p6 (R-c Pass 6)

**S1, confirmed and repaired.**
- Finding: Pass 6's A-col amendment changed V4. The collar step can be done from V4 as written.
- Why V4 suffices:
  - V4's young carrier is D(Λ) = Λ* (V4 L2404), so its collar J_col(Λ) already contains the outer layer of Λ.
  - By V3 L388 the Hessian is CRE's C*Δ₁C, so m_t = t·m with V4's mean shift m (V4 L2628).
  - V4 (c5-4-1) gives t|m_b|_σ ≤ r/4 on every bond of Λ.
  - The penalty at 3r/4 enters only RG2 (2.26) (RG2 pp.16–17 checked).
- Changes:
  - RC_PROOF_PASS: Pass 6 rewritten. Pass 5 (e) and (f) now point to it. The A-col material is removed.
  - Map: l.185 and l.188.
  - READINGS_RECHECK: row 28.
- Minors: moot after the rewrite.

## hc (hypercubic covariance)

**S1, confirmed against the prints.** The fluctuation fields are written in a gauge generated from an axis-ordered preliminary axial gauge:
- RG1 p.265: U_k′(V′) goes to the axial gauge Ax_k of REG (1.19), then to the Landau gauge by u_k, giving exp iη𝐇_k(B′).
- REG pp.78–79: (1.19) is posed on the contours Γ_{x_{n+1},x_n}. CMP 98 p.24 l.25: these contours run in a fixed axis order.
- REG p.80 l.29–31: the restricted transformations "do not agree with the group structure". REG p.81 l.3–7 chooses (1.19) as the preliminary gauge.
- RG1 p.276: the generalized axial gauge transformations matter "later on in a final localization", and (3.28) contains 𝐇_{k+1}(□₀,·).
- CRE p.260 claims covariance "only" for the unrestricted z-sums.

Hence hypercubic covariance of the step is not established. Translation covariance (R-tr) stands.

Repairs:
- RTR_PROOF_PASS *Hypercubic covariance* rewritten:
  - Result: translations only.
  - *Gauge fixing*: the citations above.
  - *Localised activities*: they depend on 𝐇_k(B′) and 𝐇_{k+1}(□₀,·), so they are not covariant.
  - *Our objects*: translations only. V4's step-1 choices are not checked for permutation invariance.
  - *What D2 uses*: per-orientation κ_v and the averages δm_{k+1}, ζ_{k+1}.
- Map:
  - l.118: μ is the average over C's orientations.
  - l.186 (R-tr): covariance not established; per-orientation quantities.
  - l.1010: κ_v kept per v; D2 uses the average.
  - l.1020: the step itself is not shown hypercubic covariant.
  - l.1087: period points are cube centres only for the partitions whose side divides Π_{k+1}.
  - l.1153 *Independence*: why the averages suffice. C is a square, so its four sides sum to −P_k(C)δm_{k+1} and its corners to 4ζ_{k+1}.
- The definitions at l.1146 and l.1150 already used the averages, so they are unchanged.

Minors, all applied in RTR_PROOF_PASS:
- the covers by unions of 2^d cubes (RG1 p.270, PBG 𝒟_j) are vertex-centred but mapped to themselves, and RG2 p.3 names no origin;
- 0 < δ < 1/6 and an explicit even β;
- the quote is at V4 L1736, the base at L2136;
- A ≥ 36 is kept, with "D2 cites no derivative bound of ζ; RG1's uses of the 5 are not traced here";
- CMP 98 (45) is the identity used for the bound on |V̄(∂p′) − 1|.

## rh (slot values at complex backgrounds)

**S1, confirmed and repaired.** The mean-value step bounded the minimiser function 𝓗, not 𝐇^{(j)} of (3.22). The repair is a new paragraph in map l.972, *From the minimiser function to 𝐇^{(j)} at complex 𝐔*:
- By (3.18), e^{i𝐇^{(j)}(b)} = Φ_b(L^{−1}η𝓗), which depends only on the bonds of b's blocks (CMP 98 p.34).
- Φ_b(0) = 1 at every background, since at X = 0 the minimisers agree ((3.17)).
- (1/i)log Φ_b is analytic and bounded by 8ρ on the polydisc of radius ρ = c₃/4. This uses CMP 98 Prop. 3 with (127)–(129) for complex A over a real base, and the u-conjugations by CMP 98 (106) cost at most ‖R(u^{±1})‖ ≤ 2.
- Schwarz's lemma then gives |𝐇^{(j)}(b)| ≤ 8 sup_{B_b}|L^{−1}η𝓗|.

**S2, confirmed and repaired** (map l.975, *The inclusion*).
- The finding was right: Y_j is the global collar, so the old term's X does not contain it.
- The pointwise conditions and (2.38) hold per bond and per cube on each layer (D(k)(iii) and (4)(f)), so no X is needed.
- (2.35) on Y_j is derived:
  - CMP 98 Prop. 3 and (127)–(129) bound the complex part of the data.
  - VAR Thm 1 (p.279, read) puts the real reconstruction in REG's 𝔘_k(B₃ε₁), and one ε₁ over the layers j, j+1 costs (1+β₀)².
  - VAR Prop. 9's (19) gives the complex deviation.
  - Result: C = 2(1+β₀)²B₃ + C_VB₅.
- R-𝐇 is now stated on 𝒰_j(C): (2.34), (2.35), (2.38) and (2.39) on Y_j. (2.37) is left out, because the bound does not use it. The (1+β) restriction from RG2 p.15 is dropped.

Minors, applied:
- 3: the analyticity is not "exactly that form". It is now derived; see row 35 under *Open after this round*.
- 4: the decay condition (δ₀/16)LM₂ ≥ L+1, by CRE (2.9) (*Constants*).
- 5: C_H's constant list.
- 6: Prop. 3 is (126) + (123); the norm bound is (56) with submultiplicativity.
- 7: the volume element of the y′-sum. VAR (190)'s (L^{j′}η)^{−d} is read as a density; this is noted.
- 8: R-𝐇₀'s axial transfer at complex data is p.251's own statement, since (190) is posed on VAR (172)'s complex domain. Bałaban's, row 35.
- 9:
  - the p.251 attribution of D₀;
  - *Inputs used*, now with VAR (190), p.307, p.309 and Thm 1, and CRE (2.9) in place of p.268's comparison;
  - the layer-(j−1) cube family;
  - map l.222, whose status and condition were stale: it now uses g_j^{−3/2}, with no c_ω/ε_j.

Labels:
- R-𝐇, *The inclusion* and *What it closes* now read "reviewed, the repairs not re-reviewed".
- The l.970 heading is updated.

## Files and hashes (sha256, first 12; LF, no CR)

- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: 19fb341f1695
- RTR_PROOF_PASS_2026_10_23.md: 53536791b1a2
- RC_PROOF_PASS_2026_10_23.md: b6b95501d310
- READINGS_RECHECK_2026_10_23.md: 07b9300f062b. Row 2 is corrected, and its bare absolute-value bars are now ‖·‖, so the row has 7 cells again. Row 35 is new.

All edits were made with Edit. The repairs are not re-reviewed. A re-review packet would cover:
- the map's l.972 new paragraphs (*From the minimiser function to 𝐇^{(j)}*, *Analyticity on 𝒰_j(C)*);
- map l.973 and l.975;
- RTR_PROOF_PASS l.109–117.
