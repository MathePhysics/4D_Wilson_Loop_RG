# Packet 14bp (BP_CMP98_ADJOINT_AVERAGING.md), round 1, 9 Nov 2026

## Pre-check of bp-p14bp-20261109-r1 (full)

- **Whole packet read** (#C10.3.21–#C10.3.24-4) on 9 Nov 2026, with its context: Cauchy #C3.2-1, #C9.8.1, #C10.3.3 (the convention 𝐔 = e^{iεA}U₀), #C10.3.17–#C10.3.20, and #C10.3.25–#C10.3.28.
- **Citations checked:** CMP 98 (14)–(15) (p.019), Proposition 2 ((52), (54), p.026), and p.024 l.22–24 (the contours run coordinate by coordinate); PRT1 (1.7)–(1.8) (pp.18–19).
- **Repairs made in this pre-check:**
  - #C10.3.21-5 and #C10.3.24-2 said that the term of weight L^{d−1} has an operator "within (1 + x)⁴ − 1 ≤ 5x of the identity". An operator near the identity would make that term of size L^{d−1}sup|ν|, not a deviation. Re-derived in the right-trivialised variations e^{iηA}W of #C10.3.3's convention: d(e^{iY_c}W(c))(e^{iY_c}W(c))^{−1} = dexp_{Y_c}(i dY_c) + Ad(e^{iY_c})(dW(c)W(c)^{−1}), with dY_c = L^{−d}Σ_x(1/i)dlog_{h_{c,x}}(dh_{c,x}h_{c,x}^{−1}) and dh_{c,x}h_{c,x}^{−1} = dW(γ_{c,x})W(γ_{c,x})^{−1} − Ad(h_{c,x})(dW(c)W(c)^{−1}). So the coefficient of dW(c)W(c)^{−1} is Ad(e^{iY_c}) − dexp_{Y_c}∘L^{−d}Σ_x dlog_{h_{c,x}}∘Ad(h_{c,x}). It vanishes at W = 1 and is at most |Ad(e^{iY_c}) − 1| + ((1 + x)³ − 1) ≤ x + 4x = 5x. #C10.3.21-5 now names this operator, and #C10.3.24-2 gives this bound. The total (8d + 9)c_{av}L^{d+1}κ_W is unchanged.
  - #C10.3.21-7 said that |h_{c,x} − 1| and |Y_c| are at most 2dL²κ_W. The bound |log h| ≤ |h − 1|/(1 − |h − 1|) ≤ 2|h − 1| needs |h − 1| ≤ ½. It now reads |h_{c,x} − 1| ≤ dL²κ_W (the product of at most dL² conjugated plaquette variables, |∏g_i − 1| ≤ Σ|g_i − 1| in a unitary norm), and |Y_c| ≤ 2dL²κ_W because dL²κ_W ≤ x/4 ≤ 1/32 with c_{av} ≥ 4d.
- **Arithmetic re-derived:**
  - The adjoint weights. With ⟨A, B⟩ = η^dΣ_b and ⟨ν, μ⟩ = (Lη)^dΣ_c, the path terms get L^d·L^{−(d+1)} = L^{−1}, and the outer factor (coefficient L^{−1} per fine bond of c in field units) gets L^{d−1}.
  - The straight segments are L terms of weight L^{−1}. The contour group is N_b ≤ L^d times each of the 2d bonds at y. Their sum is L^{−1}N_bP_b*(−LηD*_{W̄}ν(y)), and it is at most L^{d−1}·Lη|D*_{W̄}ν(y)|.
  - The deviations: 4x(L + 2dL^d)L^{−1} + 5xL^{d−1} = 4x + (8d + 5)xL^{d−1} ≤ (8d + 9)xL^{d−1} = (8d + 9)c_{av}L^{d+1}κ_W ≤ 9(d + 1)c_{av}L^{d+1}κ_W.
  - #C10.3.24-4: x = c_{av}L²κ_{W_i} ≤ 4c_{av}C₀ε₁L^{2(i+1−n)} ≤ 4c_{av}C₀ε₁ for i < n. (AQ), 72(d + 1)c_{av}L^{d−1}C₀ε₁ ≤ 1, gives x ≤ 1/(18(d + 1)L^{d−1}) ≤ 1/8.
- **Definition check:** 2 conflicts, both allowed in the spec. Y_c is instantiated at W = U^B by LF #5.21, which cites #C10.3.21-3. x is a local abbreviation, like the other x's in the notes.
- **Consumers:** no other note cites #C10.3.21-5, #C10.3.21-7, or #C10.3.24-2. The statement #C10.3.19 keeps "c_{av} a constant of d and G". Table row #T12.7-25 is the fork's; it was sent c_{av} ≥ 4d.
- **Size:** 3.65k before and 3.84k after. The growth is the named operator and the log condition. The largest line is 403 characters. CR is 0, and there are no trailing spaces.
- **Spec:** specs\spec_p14bp_r1.json (BP 3e32e122df37, Cauchy db6847aa5243, LF d72f4de24c38; Cauchy and LF updated after the bookkeeping edits of 04:07–04:12). Its check gives 0 conflicts (2 allowed).
- **Order:** launch after packet 14 r1, which runs after 12b r12 (one referee at a time).

Written 2026-11-09 03:58.

## Pre-check of bp-p14bp-20261109-r1 (full), redone after the RG I (0.4) rewrite

The pre-check above is superseded: packet 14 r1's M8 put the chain's average at RG I (0.4) (Cauchy #C10.1.4–#C10.1.4-0-3), and the file was re-derived for it.

- **Whole file read** after the rewrite, with its context: Cauchy #C3.2-1, #C9.8.1–#C9.8.1-2, #C10.1.4–#C10.1.4-0-3, #C10.3.3, #C10.3.17–#C10.3.20, and #C10.3.25–#C10.3.28, and the step map's #MOSTC.8–#MOSTC.13.
- **Citations checked:**
  - RG I p.252 l.27–32 (the families 𝐆(y, x), from all permutations of the nonzero directions).
  - RG I (0.3) (centred blocks, so abs(n_ν) ≤ L/2).
  - RG I (0.4) on p.253, with the weights abs(𝐆(c₋, x))^{−1}abs(𝐆(c₊, x′))^{−1} = abs(𝐆(c₋, x))^{−2}.
- **Arithmetic re-derived:**
  - The adjoint at W = 1 has weight η^{−d}(Lη)^dL^{−(d+1)} = L^{−1} per path term, times abs(𝐆)^{−2}.
  - The entering transport is W(γ up to b) = W(γ)W(Γ′ up to b) = hW(c)W(Γ′ up to b).
  - Each of the 2d bonds at y has weight L^{−1}abs(𝐆(y, x̂))^{−2}·abs(𝐆(y, x̂)) = L^{−1}abs(𝐆(y, x̂))^{−1} per (x̂, Γ ∋ b), so the contour weight is 2dN_bL^{−1} ≤ 2dL^{d−1}.
  - A_L ≤ (d − 1)(d·L/2)²/(2d) + L(d − 1)L/2 = (d − 1)(d + 4)L²/8, and (d − 1)(d + 4)/8 ≤ d if and only if d² − 5d − 4 ≤ 0, which holds for d ≤ 5.
  - For x ≤ 1/8, (1 + x)³ − 1 ≤ 3.4x, so (1 + x)³ − 1 + x ≤ 5x.
  - Total: 5x(1 + 2dL^{d−1}) + 5xL^{d−1} ≤ 10(d + 1)xL^{d−1}.
  - At (a): x ≤ 4c_{av}C₀ε₁L^{2(i+1−n)} ≤ 4c_{av}C₀ε₁ ≤ 4c_{av}/(8c_QL^{d−1}) = 1/(20(d + 1)L^{d−1}).
- **Consumers:**
  - c_Q enters only through (AQ) (#C10.3.26), #C10.3.25-3–#C10.3.25-4, #C10.3.31-1, #C5.88-1, and LF #4.83, all symbolically. Its value is at #C10.3.19 only.
  - Cauchy #C9.8.18-7 now cites #C10.3.21–#C10.3.21-4.
  - The dL² consumers #C9.3.1-1 and #C9.7.1-7 stand.
  - Table #T12.7-25 and #T12.13 were updated by the fork (table c4464455a714).
- **Definition check:** 0 conflicts with 3 allowed: x (local), A_L (the step map's, the same object), and N_b (local). Y_c and h are now defined at Cauchy #C10.1.4-0-2, not here.
- **Size:** 3.84k before and 5.43k after. The growth is the families' weights and transports and the move count. The largest line is 552 characters. CR is 0, and there are no trailing spaces.
- **Spec:** specs\spec_p14bp_r1.json (BP 9cf308a7efe7, Cauchy 926234eb8f1b, LF 31538d03f6ab), with the step map in sources_extra.

Pre-check redone 2026-11-09 05:00.

## Round 1 (bp-p14bp-20261109-r1, full): verdict and repairs

- **Verdict:** CORRECT, with no fatal or serious finding but six minor ones, so the round is not clean. The referee checked c_{av} = 4d in the operator norm, the count A_L against #MOSTC.11, the transports and signs, and the arithmetic of (ii).
- **Repairs** (all in place):

| Finding | Where | Repair |
|---|---|---|
| M1: "and so each adjoint" is not automatic in the operator norm, and the four bounds are asserted | #C10.3.21-8 | Rewritten as #C10.3.21-8–#C10.3.21-8-1. They derive Ad(h) ≤ 2dL²κ_W, Ad(e^{iY_c}) ≤ 4dL²κ_W, dexp within (e^a − 1 − a)/a ≤ 0.53a, and dlog within 0.53a/(1 − 0.53a) ≤ 2.4dL²κ_W, with a ≤ 4dL²κ_W ≤ 1/8. The adjoints follow because ad(iZ) is antisymmetric for Re tr X*Y and Ad(g)* = Ad(g^{−1}). |
| M2: (1/i)log h ∈ 𝔤 is not justified, and central elements of SU(N) for large N are a counterexample to the bare bound | #C10.3.21-7 | New #C10.3.21-7-1–#C10.3.21-7-2. ρ_𝔤 := sup{r ≤ ½ : g ∈ G, abs(g − 1) < r implies g = e^{iP}, P ∈ 𝔤, abs(P) ≤ 1}, and c_{av} := max(4d, 1/(8ρ_𝔤)) gives κ_W < ρ_𝔤. A path in G through the moves stays within 1/16 of 1, and an open-closed argument then keeps the principal logarithm in i𝔤. The name ρ_𝔤 avoids W-δ's r_G (#T4.10) and Cauchy #C10.4.27-1's r_G. |
| M3: the hypothesis 2C₀ε₁ ≤ c₂ of #C10.3.25-1 is unnamed, and "≤ 1/8" is implicit | #C10.3.24-4 | Both are named in the line. |
| M4: "with b on γ" should count occurrences | #C10.3.21 | It now reads "and the occurrences of b in γ_{c,x}^{Γ,Γ′} … (b may occur twice, on Γ reversed and on [x, x′], when n_μ < 0)". |
| M5: both end-points of b in B(y); D's sign convention unstated | #C10.3.23-1, #C10.3.23-4 | #C10.3.23-1 states that the contours are coordinate-monotone and stay in B(y), and takes b with both end-points in B(y). #C10.3.23-4 defines D_{W̄}ω(c) := (Lη)^{−1}(Ad(W̄(c))ω(c₊) − ω(c₋)). With it, e^{iω} changes W̄ by e^{−iLηD_{W̄}ω} to first order, and the adjoint gives Σ_leaving − Σ_entering Ad(W̄(c))^{−1} = −LηD*_{W̄}ν(y). |
| M6: physical units mixed with fine units | #C10.3.22 | It now uses the fine units of #C10.1.4-0-1: b = ⟨z, z + e_μ⟩ and x = z − se_μ. |

- **Re-derived for M5:** with u(c₋)W̄(c)u(c₊)^{−1}, u = e^{iω}, the change is e^{i(ω(c₋) − Ad(W̄(c))ω(c₊))} = e^{−iLηD_{W̄}ω}, which agrees with PBG (3.116), A^λ = A − Dλ. For ⟨·,·⟩ = (Lη)^dΣ, D*ν(y) = (Lη)^{−1}(Σ_entering Ad(W̄(c))^{−1}ν(c) − Σ_leaving ν(c)).
- **Consumers:** c_Q := 10(d + 1)c_{av} is unchanged in form. #C10.3.19 says "c_{av} a constant of d and G", which still holds. Table #T12.7-25 (c_{av} ≥ 4d) is the fork's; it is sent c_{av} := max(4d, 1/(8ρ_𝔤)) and ρ_𝔤.
- **Size:** 5.43k before and 7.34k after. The growth is the log ∈ 𝔤 argument and the derivations of the four bounds that the referee asked for. The largest line is 561 characters. CR is 0, and there are no trailing spaces.
- **SHA:** BP_CMP98_ADJOINT_AVERAGING 171ceaf47fd8.
- **Next:** 14bp r2, full, after 12b-bp r1 (one referee at a time).

Triaged 2026-11-09 05:14.
