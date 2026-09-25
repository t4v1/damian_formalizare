# Morse theory and Floer homology in Lean 4

A Lean 4 / Mathlib formalization of

> Michèle Audin and Mihai Damian, *Théorie de Morse et homologie de Floer*,
> EDP Sciences, 2010 (English translation: *Morse Theory and Floer Homology*,
> Universitext, Springer, 2014)

covering both parts of the book: **Part I, Morse theory** (chapters 1–4) and
**Part II, Floer homology and the Arnold conjecture** (chapters 5–16).

Every definition and theorem of the book gets a Lean statement. Proofs are given
wherever today's Mathlib allows it; what remains is left as `sorry` and documented
at the statement. A result that Mathlib cannot even *state* (because it needs, for
instance, the `Cᵏ` topology on `C^∞(V; ℝ)` or Sobolev spaces on a manifold) gets a
blueprint entry with no Lean declaration, rather than an invented statement.

## Status

All sixteen chapters are formalized. **1 `sorry` remains**, in Part II:

| Chapter | `sorry` | What is missing |
|---|---|---|
| 6 The Arnold conjecture and the Floer equation | 1 | the Arnold conjecture on the torus itself, whose proof is Chapters 8–11 with their geometric input |

Everything else is proved, including:

- **Part I:** the Morse lemma in every finite dimension; genericity of Morse
  functions (Prop. 1.2.1); Reeb's theorem; the classification of compact
  1-manifolds; `∂ ∘ ∂ = 0` for the Morse complex; the Künneth formula; Brouwer's
  fixed point theorem (analytically, after Milnor–Rogers) and the Borsuk–Ulam
  theorem (combinatorially, via Tucker's lemma).
- **Part II:** Darboux's theorem (by Moser's method); contractibility of calibrated
  complex structures; Wirtinger's inequality and Yorke's theorem; the Floer complex
  and `∂ ∘ ∂ = 0`; invariance of Floer homology; the comparison of the Floer and
  Morse complexes; the Fredholm index and its stability under compact
  perturbations (Riesz–Schauder); Weyl's lemma for `∂̄`; the Cauchy–Pompeiu formula and the
  Cauchy transform as the solution operator of `∂̄v = f`, together with the Beurling
  transform, the Calderón–Zygmund estimate for it at the sharp Hölder exponent, the
  identification of the other derivative of the Cauchy transform with it, and the Schauder
  estimate for that solution operator on Hölder data, at every order of the scale, and the
  elliptic bootstrap for `∂̄` that follows from it, linear and nonlinear, and hence **elliptic
  regularity for the Floer equation itself** (Prop. 6.5.3: every `C¹` solution is `C^∞`); the convergence
  of the action of a finite-energy solution to critical values at both ends (Prop. 6.5.7) and the
  uniform energy bound (Cor. 6.5.11); the uniform gradient bound for solutions of bounded energy
  (Prop. 6.6.2), by a mean value inequality and Hofer's lemma instead of bubbling; the convergence
  of finite-energy solutions to periodic orbits at both ends (Thm. 6.5.6), without the
  compactness theorem; and the compactness theorem itself (Thm. 6.5.4), by Ascoli and the
  Cauchy transform rather than uniform elliptic estimates; the continuity of the roots of a
  polynomial in its coefficients, the continuous spectral projectors of a matrix, and the
  orthogonality and nondegeneracy properties of the form `ω(X, Ȳ)` on the generalised eigenspaces
  of a symplectic matrix (Lemma 7.3.3, Corollary 7.3.4), and the identification of the kernel of a
  factor of the characteristic polynomial with the sum of the corresponding generalised eigenspaces,
  and the symmetry of the spectrum of a symplectic matrix under `μ ↦ 1/μ̄` with multiplicities,
  the bricks towards the map `ρ` of Chapter 7; Sard's theorem in all
  dimensions (the case `dim E > dim F` via Kudryashov's formalization of
  Moreira's theorem, see below).

Geometric input that Mathlib cannot yet express (spaces of trajectories, Sobolev
spaces on the cylinder) enters as an explicit hypothesis, never as a `sorry`ed
theorem, so that the algebra built on top of it is proved outright.

The file-by-file status, the Mathlib gaps that block the remaining `sorry`s, and
notes on the formalization are in [`CLAUDE.md`](CLAUDE.md).

## Layout

```
MorseFloer/Basic.lean        second differentials, Hessian, Morse index
MorseFloer/Part1/ChN.lean    chapters 1–4, one file per chapter
MorseFloer/Part2/ChN.lean    chapters 5–16, one file per chapter
MorseFloer/Part*/*.lean      self-contained proofs used by a chapter
                             (MorseLemma, Brouwer, BorsukUlam, Darboux, Weyl, ...)
MorseFloer/Part2/SardMoreira vendored copy of Kudryashov's SardMoreira project
blueprint/                   leanblueprint sources, dependency graph
contrib/                     material prepared for Mathlib, not built here
```

## Building

The toolchain is `leanprover/lean4:v4.33.1`, and Mathlib is pinned to the tag
`v4.33.1`.

```sh
lake exe cache get      # download the prebuilt Mathlib
lake build              # build everything
make blueprint          # check declarations, build the PDF and web blueprint
make blueprint-serve    # serve the web blueprint (the graph needs HTTP)
```

The book itself is not included in this repository.

## Mathlib contributions

Several results proved here are standard but absent from Mathlib. They are being
prepared as Mathlib contributions in [`contrib/`](contrib/), with a plan in
[`contrib/PLAN.md`](contrib/PLAN.md).

## Use of AI

Most of the Lean code in this repository was written with Claude Code (Anthropic),
under my mathematical direction and review. Every proof is machine-checked by
Lean; `lake build` succeeds, and the only unproved statements are the `sorry`s
listed above.

## Credits

`MorseFloer/Part2/SardMoreira/` is a copy of Yury Kudryashov's
[SardMoreira](https://github.com/urkud/SardMoreira) (Apache 2.0, see the
`LICENSE.txt` in that directory), adapted to the Mathlib version used here. It
provides Moreira's version of Sard's theorem, from which the case `dim E > dim F`
of Theorem 14.2.1 is derived.

## License

Apache 2.0, see [`LICENSE`](LICENSE). Copyright 2026 Octavian Halmaghi.
