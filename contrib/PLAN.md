# Mathlib contribution plan

*Written 2026-09-17 against the pinned Mathlib v4.33.1 and a survey of Mathlib
master and its open PRs on the same day.  Sources are the book's bibliography
(`parts/biblio.pdf`, cited as [n]).*

The 14 remaining `sorry`s (Chapter 6: 6, Chapter 7: 8) cannot be closed inside
this project: each is a standard theorem of analysis or topology that Mathlib
lacks.  The way to close them is therefore to *write those theorems for Mathlib*,
in Mathlib's own shape, and then quote them here.  This file lists, in priority
order, what to write, where it goes upstream, which source in the bibliography
carries the proof, what it unblocks, and what already exists in this repository
and can be lifted out almost as is.

Two facts fix the order:

1. **Mathlib master has moved since the pin.**  The Fredholm index is now
   `LinearMap.index` with `IsFredholm.index_comp` (additivity) and
   `Fredholm/Open.lean` (local constancy); `Analysis/Distribution/Sobolev.lean`
   is `BesselPotentialSpace.lean`; `Topology/Covering/Deck.lean` exists; and
   PR #41856 (open, 2026-09-14) proves `π₁(S¹) ≅ ℤ`.  Nothing on master or in an
   open PR covers Morrey's inequality, Riesz–Schauder, Weyl's lemma, Rouché,
   continuity of roots, winding numbers, the polar decomposition of matrices,
   Brouwer, Borsuk–Ulam, the Morse lemma, or the classification of 1-manifolds
   (all checked by code search on 2026-09-17).
2. **This repository already holds eleven self-contained, `sorry`-free files
   that Mathlib does not have.**  They are the cheapest contributions by far,
   because the mathematics is done; what remains is restyling and generality.

## Tier 0 — written, compiling, absent upstream

Each row is a file (or section) of this project.  "Upstream home" is where a
Mathlib reviewer would expect it.  Estimated effort is for turning it into a
mergeable PR: Mathlib naming, module docstring, `#lint`, generalising `ℝ` to
`RCLike 𝕜` or a normed field where that is free, and splitting into PRs of at
most ~300 lines.

| Here | Result | Upstream home | Source | Effort |
|---|---|---|---|---|
| `contrib/.../MorreyInequality.lean` | polar-coordinates `lintegral` for a Haar measure; Riesz-kernel integral on a ball; Morrey's Hölder estimate and `W^{1,p} ↪ L^∞` for `p > n`, compactly supported `C¹` | `MeasureTheory/Constructions/HaarToSphere.lean` (polar lintegral, **still absent on master**), then `Analysis/FunctionalSpaces/MorreyInequality.lean` beside `SobolevInequality.lean` | [13] Brezis IX.3; book §16.4 | 3 PRs, small–medium |
| `Part2/Ch16.lean` §RieszSchauder | `1 + K` Fredholm of index `0` for compact `K`; index invariant under compact perturbation | `Analysis/Normed/Operator/Compact/FredholmAlternative.lean` or new `Fredholm/CompactPerturbation.lean`; rebase on master's `LinearMap.index`, `IsFredholm.index_comp`, `Open.lean` | [13] Brezis VI.3–VI.4; book Prop 16.2.7, Thm 16.2.10 | 1 PR, medium (generalise ℝ → `RCLike`) |
| `contrib/.../Fredholm/Index.lean` | additivity, local constancy, finite-rank perturbation | **superseded** by master except the finite-rank case, which folds into the row above | — | drop |
| `contrib/.../LinearAlgebra/Prod.lean` | `↥(p × q) ≃ₗ ↥p × ↥q`, `(M × N) ⧸ (p × q) ≃ₗ (M ⧸ p) × (N ⧸ q)` | `LinearAlgebra/Prod.lean`, `LinearAlgebra/Isomorphisms.lean` | — | 1 PR, small |
| `Part2/Weyl.lean` | Weyl's lemma for `∂̄`: a locally integrable distributional solution of `∂̄u = 0` on an open `U ⊆ ℂ` agrees a.e. with a holomorphic function | `Analysis/Complex/WeylLemma.lean` (Mathlib has harmonic functions with the mean value property but no Weyl lemma) | [9] Bony; [57] Rudin; book Lemma 12.1.1 | 2 PRs: mollifier + mean-value step, then the gluing |
| `Part2/Wirtinger.lean` | Wirtinger's inequality `∫₀¹ ‖y‖² ≤ (2π)⁻² ∫₀¹ ‖y'‖²` for mean-zero periodic `y`, via Parseval; Yorke's theorem (no periodic orbit of period `< 2π/K` for a `K`-Lipschitz field) | `Analysis/Fourier/Wirtinger.lean`; `Analysis/ODE/Yorke.lean` | [61] Salamon–Zehnder; book Prop 6.1.5 | 2 PRs, small |
| `Part2/LinearYorke.lean` | `exp A` has no eigenvalue `1` when the symmetric `S` in `A = JS` has spectrum in `(−2π, 2π)`; `‖S‖ = max\|λ\|` for symmetric `S` | `Analysis/Matrix/…` beside `Spectrum.lean` | book Remark 7.1.2 | 1 PR, small |
| `Part2/FlowC1.lean` | the global `C¹` flow of a globally Lipschitz `C¹` autonomous field, with the variational equation | `Analysis/ODE/Flow.lean` (Mathlib has Picard–Lindelöf and Grönwall, `Dynamics/Flow` as an abstract structure, but no construction of the flow of a vector field) | [15] Cartan; [40] Laudenbach | 2 PRs, medium |
| `Part1/ManifoldFlow.lean` | flow of a `C¹` field on a compact manifold, jointly continuous | `Geometry/Manifold/IntegralCurve/Flow.lean` | [37] Lafontaine | 1 PR after the previous row |
| `Part1/Brouwer.lean` | Brouwer's fixed point theorem in every dimension, analytically (Milnor–Rogers) | `Analysis/…/Brouwer.lean` — **Mathlib has no Brouwer theorem** | [48] Milnor | 1–2 PRs, medium |
| `Part1/BorsukUlam.lean` | Borsuk–Ulam via Tucker's lemma | `Topology/…/BorsukUlam.lean` — absent | [19] Dold (statement); combinatorial proof | 2 PRs, medium (Tucker first) |
| `Part1/MorseLemma.lean` | the Morse lemma in every finite dimension | `Analysis/Calculus/MorseLemma.lean` — absent | [47] Milnor §2 | 1 PR, medium |
| `Part1/OneManifold.lean` | compact connected 1-manifolds are circles (Gale) | `Geometry/Manifold/…` — absent | [48] Milnor appendix | 1 PR, medium |
| `Part2/Darboux.lean` | Darboux's theorem for closed nondegenerate 2-forms on a normed space, by Moser's trick; Poincaré lemma for closed 2-forms | `Analysis/Calculus/DifferentialForm/Darboux.lean` (Mathlib has `extDeriv` on normed spaces since 2026, no Poincaré lemma, no Moser) | [50] Moser; [43] McDuff–Salamon 3.2 | 2 PRs, medium |
| `Part2/Calibrated.lean` | the space of `ω`-calibrated complex structures is contractible (Cayley transform) | `LinearAlgebra/…/Symplectic` | [43] McDuff–Salamon 2.5; book Prop 5.5.4 | 1 PR, small |
| `Part2/Ch5.lean` `det_charpoly_symmetric` | `det(A − λ⁻¹) = (−λ⁻¹)^{2n} det(A − λ)` for symplectic `A` | `LinearAlgebra/SymplecticGroup.lean` (currently ~400 lines, no spectral results) | book Prop 5.6.4 | 1 PR, small |

Recommended first three, in this order, because each is already complete and
none waits on a design decision upstream: **polar `lintegral` → Morrey**, then
**Riesz–Schauder** (rebase Chapter 16's proof on master's index), then **Weyl's
lemma**.  Open a Zulip thread per file before the PR; Mathlib prefers to be
told.

## Tier 1 — new files that close the Chapter 7 sorries

Chapter 7's eight assumptions all stand on two missing pieces of mathematics:
the spectral theory of symplectic matrices, and `π₁(Sp(2n)) ≅ ℤ`.  Sources:
[61] Salamon–Zehnder §3 (the map `ρ` and its characterisation), [17]
Conley–Zehnder, [30] Gelfand–Lidskii (the eigenvalue quadruples and the
signature on `E_λ`), [4] Audin (covering spaces).  The path, each step a
Mathlib file in its own right:

1. **`Analysis/Complex/Rouche.lean`** — the argument principle for polynomials
   and Rouché's theorem on a disc.  Absent from Mathlib (checked).  The sibling
   project `~/projects/damian/exercises/p2ex43.lean` has the algebraic core
   (`P'/P = m/(z−α) + R'/R`, the circle integral, the `D(1,1)` log branch); the
   contour-integral half uses Mathlib's `circleIntegral` and Cauchy.  Source:
   [57] Rudin 10.43; book Exercise 43.
2. **`Analysis/Polynomial/RootsContinuous.lean`** — roots of a monic polynomial
   depend continuously on the coefficients, stated as convergence of the
   multiset `Polynomial.roots` (or of `Multiset.map` into any metric); corollary:
   eigenvalues of a convergent sequence of complex matrices can be numbered to
   converge.  This is Proposition 7.3.6, and it is the input for the continuity
   of `ρ`.  Value far beyond Floer theory.
3. **`LinearAlgebra/Matrix/Symplectic/Spectrum.lean`** — for `A ∈ Sp(2n)`:
   `λ, λ⁻¹, λ̄, λ̄⁻¹` occur together (upstream `det_charpoly_symmetric`), the
   form `B(X,Y) = Im ω(X, Ȳ)` on `ℂ^{2n}`, orthogonality of `E_λ` and `E_μ` for
   `λμ ≠ 1` (Lemma 7.3.3, needs `Module.End.genEigenspace`, which Mathlib has),
   the signature of `Q = B(X,X)` on `E_λ ⊕ E_{1/λ}` vanishing (Corollary
   7.3.4, needs the signature of a quadratic form restricted to a subspace:
   Mathlib has `sigPos/sigNeg` but no restriction API — write it).  Source:
   [30], [61] Lemma 3.2–3.4.
4. **`LinearAlgebra/Matrix/PolarDecomposition.lean`** — `A = P U` with `P`
   positive definite and `U` orthogonal, via the square root of a positive
   definite matrix.  Mathlib has the continuous functional calculus for
   Hermitian matrices (`HermitianFunctionalCalculus.lean`) and `CFC.sqrt`, so
   the square root is a definition, not a theorem.  Then: the polar factors of a
   symplectic matrix are symplectic, and `A ↦ U` retracts `Sp(2n)` onto
   `U(n) = Sp(2n) ∩ O(2n)` (Proposition 5.6.9, the Chapter 5 gap).  Source:
   [43] McDuff–Salamon 2.2.
5. **Winding numbers** — `Analysis/Complex/WindingNumber.lean`: the degree of a
   loop in `ℂ ∖ {0}` via `IsCoveringMap.liftPath` (Mathlib has path and
   homotopy lifting with monodromy in `Topology/Homotopy/Lifting.lean`, and
   `isCoveringMap_exp`), additivity, homotopy invariance.  **Do not** prove
   `π₁(S¹) ≅ ℤ`: PR #41856 does; build on it once merged.  Chapter 7's `Δ`,
   `IsAngleLift` and `Delta_eq_of_isAngleLift` become two-line corollaries.
   Source: [4] Audin.
6. **`π₁(U(n)) ≅ ℤ` via `det : U(n) → S¹`** and hence `π₁(Sp(2n)) ≅ ℤ` by the
   retraction of step 4.  This is the only genuinely topological step and the
   one to leave for last; it needs the fibration `SU(n) → U(n) → S¹` or the
   inductive `U(n−1) → U(n) → S^{2n−1}`, neither of which Mathlib has.  An
   alternative that avoids fibrations: Salamon–Zehnder's direct proof that the
   map `ρ` of step 3 induces an isomorphism on `π₁`, which needs only steps 1–5.

With 1–5 in Mathlib, `exists_isRho` (Theorem 7.1.3), Lemma 7.1.5 and
Proposition 7.1.4 are provable here; with 6, Lemma 7.1.6 and the existence of
the index follow, and Lemma 7.2.4 becomes the `2 × 2` computation
`μ(exp(tJ·θ)) = −(2⌊θ/2π⌋ + 1)` plus additivity.

## Tier 2 — new files that close the Chapter 6 sorries

Chapter 6's assumptions are elliptic regularity and compactness for the Floer
equation on the torus.  Sources: [31] Gilbarg–Trudinger, [13] Brezis, [42]/[44]
McDuff–Salamon, [55] Pansu, [36] Jost.

1. **`Analysis/Complex/CauchyPompeiu.lean`** — the Cauchy–Pompeiu formula
   `u(z) = (2πi)⁻¹ ∮ u(ζ)/(ζ−z) dζ − π⁻¹ ∫∫ ∂̄u(ζ)/(ζ−z) dA` for `C¹` functions
   on a disc.  Absent from Mathlib; a standard theorem with a one-page proof
   from Green's formula (Mathlib has the divergence theorem on boxes,
   `MeasureTheory/Integral/DivergenceTheorem.lean`).  Source: [57] Rudin 20.
2. **`Analysis/Complex/CauchyTransform.lean`** — Hölder estimates of the
   Cauchy transform `Tf(z) = π⁻¹ ∫ f(ζ)/(z−ζ) dA`: `f ∈ C^{0,α}` with compact
   support gives `Tf ∈ C^{1,α}` and `∂̄(Tf) = f`.  This is the Schauder theory
   of `∂̄` in its simplest form and the true content of Proposition 6.5.3: with
   it, a `C¹` solution of `∂̄u = F(u)` with `F` smooth is `C^∞` by bootstrapping
   (`u ∈ C^{k,α} ⇒ F(u) ∈ C^{k,α} ⇒ u ∈ C^{k+1,α}`).  Mathlib now has the
   pointwise Hölder class `ContDiffPointwiseHolderAt` (from the SardMoreira
   upstreaming); the uniform class `C^{k,α}` on a set is still to be defined.
   Source: [36] Jost 5.2; [31] Ch. 4; [42] Appendix B.
3. **`Analysis/ODE/…` Ascoli for families with a derivative bound** —
   `TendstoLocallyUniformly` extraction from a uniform `C¹` bound on `ℝ × ℝ`;
   Mathlib has Arzelà–Ascoli for bounded continuous functions on a compact
   space and `Topology/UniformSpace/Ascoli.lean`; the missing glue is small.
   Together with 2 this gives Proposition 6.5.7 and Theorem 6.5.6 on the torus.
4. **Sobolev spaces on the quotient of a normed space by a lattice** — the
   plan of https://claude.ai/code/artifact/6128ff05-9235-473b-beb9-9f0a2614767a
   (coordinate with PR #32305 before writing).  Needed for Chapters 8, 9, 11, 13
   rather than for the Chapter 6 sorries, so it is third here.
5. **Bubbling** (Proposition 6.6.2, Theorem 6.5.4).  Lemma 6.6.3 is Hofer's
   lemma and *is* in Mathlib (`Analysis/Hofer.lean`, `hofer`).  Lemmas
   6.6.4–6.6.5 need the symplectic area of a `J`-holomorphic plane and the
   removal of singularities; this is a research-level formalisation and is
   listed only for completeness.  Source: [55] Pansu; [44] Ch. 4.

The Arnold conjecture on the torus (`arnold_conjecture_torus`) is the whole of
Part II and is not a target.

## Working rules

- One theorem per PR, under ~300 lines, with the source cited in the module
  docstring the way `SobolevInequality.lean` cites its references.
- Develop against Mathlib **master**, not the pin: start each file in a scratch
  checkout of master, since names have already moved (`LinearMap.index`,
  `BesselPotentialSpace`, `Covering/Deck`).  Keep a copy under `contrib/` that
  compiles against the pin only if this project needs it before the PR lands.
- Announce on Zulip `#mathlib4` before writing anything in Tier 1 step 4–6 or
  Tier 2 step 4, where other people are active.
- After each merge, replace the project's own version by the Mathlib one and
  delete the helper file; the chapter file then quotes Mathlib.
