import MorseFloer.Part2.Ch16
import MorseFloer.Part2.Weyl

/-!
# Chapter 12: Elliptic regularity for the Floer operator

Formalization of Chapter 12 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 413–432).

The chapter collects, and proves, the "elliptic regularity" statements that the
rest of Part II invokes: a solution of the Floer equation is automatically
`C^∞`, and a family of solutions with bounded gradient is precompact in
`C^∞_loc`.  Its architecture is:

* **§12.1.a** the *linear* statements — Theorem 12.1.2 (`W^{k,p}_loc` regularity
  and the a priori estimate for the operator `∂̄`), Lemma 8.7.2 (the same
  estimate for the perturbed operator `L = ∂/∂s + J₀ ∂/∂t + S`), and Theorem
  12.1.3 (an `L^p` distributional solution of `LY = 0` is smooth and lies in
  `W^{1,p}`);
* **§12.1.b** the *nonlinear* statements — Proposition 12.1.4 (a `W^{1,p}_loc`
  solution of the Floer equation, `p > 2`, is `C^∞`, and on the solution space
  the `C⁰_loc` and `C^∞_loc` topologies agree) and Theorem 12.1.5 (its
  `W^{k,p}_loc` form with variable `J`);
* **§12.1.c** the *fil d'Ariane*: the chain of implications
  `16.5.8 ⇒ 12.3.1 ⇒ 12.1.2`, `12.1.2 ⇒ 12.1.3`, `12.1.2 ⇒ 8.7.2`,
  `12.3.1 ⇒ 12.1.5 ⇒ 12.1.4 ⇒ 12.1.1` that organises the whole chapter;
* **§12.2** the proof of Lemma 8.7.2 from Theorem 12.1.2 (localise, use
  `s`-translation invariance of the constant-coefficient operator, sum over the
  integer translates, absorb the error term coming from `S − S^±`, and glue with
  a cut-off `β`);
* **§12.3** the proof of Theorem 12.1.2 through Proposition 12.3.1 (`Δu = f +
  ∂g/∂s + ∂h/∂t` with `f, g, h ∈ L^p_loc` forces `u ∈ W^{1,p}_loc`), obtained
  from the Calderón–Zygmund inequality 16.5.8, the mean value property of
  harmonic functions and the explicit fundamental solution of the Laplacian;
* **§12.4** the nonlinear regularity: Lemma 12.4.2 (the estimate for a variable
  `J`, with Hölder exponents `1/p + 1/q = 1/r`), the bootstrapping recursion on
  the exponents that needs `p > 2`, Corollary 12.4.1 and Lemma 12.4.4.

## The obstruction: Sobolev spaces on a domain

Almost everything in this chapter is a statement about the spaces
`W^{k,p}(V)` and `W^{k,p}_loc(U)` on an open set `U ⊆ ℝ × S¹`, about their
norms, and about inequalities between those norms.  **Mathlib has no such
spaces.**  What the pinned Mathlib does have, and what it still does not, is
worth recording precisely, because it is finer than the summary in
`MorseFloer.Chapter16`:

* it **has** test functions `𝓓^{n}(Ω, F)` on an open `Ω`, the space of
  distributions `𝓓'(Ω, F)`, and the distributional directional derivative
  (`Mathlib.Analysis.Distribution.TestFunction`,
  `Mathlib.Analysis.Distribution.Distribution`).  So the *notion* of a weak
  solution is expressible, and it is used below;
* it **has** Bessel-potential Sobolev spaces `H^{s,p}` of *tempered*
  distributions on the whole of a finite-dimensional inner product space,
  defined through the Fourier transform
  (`Mathlib.Analysis.Distribution.Sobolev`).  These are global spaces on all of
  `ℝⁿ`; they carry no notion of restriction to a relatively compact open `V`,
  and there is no `‖·‖_{W^{k,p}(V)}`;
* it **does not have** `W^{k,p}(U)` or `W^{k,p}_loc(U)` for `U` an open subset,
  their norms, the Sobolev embeddings `W^{1,p}(V) ⊆ L^∞(V)` for `p > 2` and
  `W^{1,r}_loc ⊆ L^{2r/(2−r)}_loc` (Theorems 16.4.9, 16.4.10), the Poincaré
  inequality (16.4.3), the Rellich theorem (16.4.6), or the Calderón–Zygmund
  inequality (16.5.8).

Consequently the following are **not stated** at all, and this is the honest
deliverable of the chapter:

* **Theorem 12.1.2**, **Lemma 8.7.2**, **Theorem 12.1.3**, **Proposition
  12.1.4**, **Theorem 12.1.5**, **Proposition 12.3.1**, **Corollary 12.4.1**,
  **Lemma 12.4.2** and **Lemma 12.4.4**: every one of them either concludes
  membership in a `W^{k,p}` space or asserts an inequality between `W^{k,p}`
  and `L^p` norms;
* the definition of `W^{1,p}(ℝ × S¹; W)` for a target manifold `W` (§12.1.b),
  which is a statement about charts of `W` and about `W^{1,p}` being preserved
  by composition with a `C^1` map — again unavailable, and in any case about
  the manifold `W` of Chapter 6;
* the second half of **Lemma 12.1.1**, the `C^∞_loc` precompactness of a
  sequence of solutions with `sup_n ‖grad u_n‖_{L^∞} ≤ M`.  Ascoli is in
  Mathlib, but the derivative bounds that feed it come from the estimates
  above.

## What is proved here

Where the chapter's content does not mention Sobolev spaces, it is stated and
proved:

* **Lemma 12.1.1, classical form.**  `contDiffOn_of_isCauchyRiemann`: on an open
  `U ⊆ ℂ`, a real-differentiable solution of `∂u/∂s + i ∂u/∂t = 0` is `C^∞` —
  indeed holomorphic, hence analytic.  This is the book's lemma for the Floer
  equation with `J = J₀` and `H = 0`, and it is proved in full from Mathlib's
  Cauchy–Riemann criterion and Cauchy's integral formula.
  `isCauchyRiemann_iff_differentiableOn` records the converse, so that on an
  open set the `C^1` solutions of `∂̄u = 0` are exactly the holomorphic
  functions.
* **Lemma 12.1.1, distributional form (Weyl's lemma for `∂̄`).**
  `IsWeakCauchyRiemann` writes out the weak formulation by hand — the pairing
  with a compactly supported smooth test function — and
  `exists_differentiable_of_isWeakCauchyRiemann` states that a locally
  integrable weak solution agrees almost everywhere with a holomorphic
  function.  This is the statement the book actually needs, and it is
  **proved**, in `Part2/Weyl.lean`, by mollification with a radial kernel: the
  mollifications are smooth classical solutions, hence holomorphic; any two of
  them agree where both are holomorphic, by the mean value property against a
  radial weight (polar coordinates and Cauchy's formula on circles); and they
  converge to `u` almost everywhere by the Lebesgue differentiation theorem.
  Mathlib has no elliptic regularity for distributions, and none is used.
* **§12.1.c, the fil d'Ariane**, as an explicit chain of implications:
  `ArianeThread` bundles the eight propositions of the chapter's diagram
  together with the seven implications the chapter proves between them, and
  `ArianeThread.of_calderonZygmund` derives all of them from Calderón–Zygmund.
  The individual statements are propositional parameters — they cannot be
  spelled out — but the logical architecture is recorded and checked.
* **§12.1.a, the Hölder step of the proof of Theorem 12.1.3**:
  `eLpNorm_two_le_eLpNorm` is the inequality `∫₀¹ ‖Y‖² ≤ (∫₀¹ ‖Y‖^p)^{2/p}` on
  the circle, i.e. monotonicity of `L^p` norms on a probability space.
* **§12.2, the three elementary steps** of the proof of Lemma 8.7.2 that are
  not about Sobolev spaces: `rpow_add_le_two_rpow_mul` is the book's
  `(a+b)^p ≤ 2^p (a^p + b^p)`; `tsum_le_mul_add_tsum` is the summation of the
  local estimates over the integer translates `[k, k+1] × S¹`; and
  `le_two_mul_of_absorb` is the absorption of `ε ‖Y‖_{W^{1,p}}` into the left
  side once `ε ≤ 1/2C`.
* **§12.3, the harmonic case** of Proposition 12.3.1:
  `contDiffOn_of_harmonicOnNhd` is the first line of its proof, that a harmonic
  function is `C^∞` — Mathlib supplies both the mean value property (the book's
  Proposition 16.5.2) and analyticity (the book's Lemma 16.5.3).  And the
  explicit fundamental solution of the Laplacian used later in that proof is
  defined, with `hasDerivAt_fundSol_fst` and `hasDerivAt_fundSol_snd` proving
  that the book's `K₁` and `K₂` really are its two partial derivatives away
  from the origin.
* **§12.4, the bootstrapping recursion.**  This is the arithmetic core of the
  proof of Theorem 12.1.5 and it is entirely elementary, so it is proved in
  full: `bootstrapExp` is the book's `r ↦ 2pr/(2p + 2r − pr)`;
  `inv_bootstrapExp` shows that in terms of the reciprocal exponents it is the
  translation `1/r ↦ 1/r − (1/2 − 1/p)`; `bootstrapExp_sub_two` is the book's
  identity `r' − 2 = 4[(p−1)(r−1) − 1]/(2p + 2r − pr)`; `lt_bootstrapExp` is
  `r' > r` for `r < 2`; and `exists_two_le_of_bootstrap` is the statement that
  the recursion escapes `]1, 2[` in finitely many steps, which is exactly where
  the hypothesis `p > 2` is used.  `lt_sobolevExp` is Remark 12.4.3(1).

## Conventions

`ℝ × S¹` is replaced throughout by `ℂ`, its universal cover with the complex
structure `J₀ = i`; `1` and `i` are the `s`- and `t`-directions, so that
`∂u/∂s = d u(1)` and `∂u/∂t = d u(i)`, which is what `dds` and `ddt` below
record.  This is the local model in which the book's proofs are written.
-/

open Filter Topology MeasureTheory
open scoped ContDiff ENNReal NNReal

namespace MorseFloer
namespace Chapter12

/-! ## §12.1.a The Cauchy–Riemann operator and Lemma 12.1.1

The Floer equation is `∂u/∂s + J(u) ∂u/∂t + grad H_t(u) = 0`.  In the local
model of the chapter `s + it` runs over an open subset of `ℂ`, and for the
standard complex structure `J = J₀ = i` and vanishing Hamiltonian this is the
homogeneous Cauchy–Riemann equation `∂u/∂s + i ∂u/∂t = 0`. -/

section CauchyRiemann

/-- `∂u/∂s`, the derivative of `u` in the direction `1` of `ℂ = ℝ × S¹`. -/
noncomputable def dds (u : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ u z 1

/-- `∂u/∂t`, the derivative of `u` in the direction `i` of `ℂ = ℝ × S¹`. -/
noncomputable def ddt (u : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ u z Complex.I

/-- **The Cauchy–Riemann equation** `∂u/∂s + i ∂u/∂t = 0` on an open set `U`,
in the classical (pointwise, differentiable) sense.

This is the Floer equation of Lemma 12.1.1 for the standard complex structure
`J₀` and a vanishing Hamiltonian. -/
def IsCauchyRiemann (U : Set ℂ) (u : ℂ → ℂ) : Prop :=
  ∀ z ∈ U, dds u z + Complex.I * ddt u z = 0

/-- A holomorphic function solves the Cauchy–Riemann equation. -/
theorem isCauchyRiemann_of_differentiableOn {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u U) : IsCauchyRiemann U u := by
  intro z hz
  have h := hu.differentiableAt (hU.mem_nhds hz)
  rw [differentiableAt_complex_iff_differentiableAt_real] at h
  obtain ⟨-, h2⟩ := h
  simp only [dds, ddt, h2, smul_eq_mul]
  linear_combination (fderiv ℝ u z 1) * Complex.I_sq

/-- **Lemma 12.1.1 (elliptic regularity), classical form.**

On an open subset of `ℂ`, a real-differentiable solution of the Cauchy–Riemann
equation `∂u/∂s + i ∂u/∂t = 0` is complex differentiable, hence analytic, hence
`C^∞`.  This is the book's assertion that a `C^1` solution of the Floer equation
is `C^∞`, in the case `J = J₀`, `H = 0` where the equation is exactly `∂̄u = 0`.

The proof is Mathlib's: the Cauchy–Riemann criterion turns the equation into
complex differentiability, and Cauchy's integral formula makes a complex
differentiable function analytic on an open set.

The book's statement is stronger in two ways that Mathlib cannot reach: it
allows a general calibrated `J` and a Hamiltonian term (that is the nonlinear
Proposition 12.1.4, which needs `W^{k,p}` spaces), and elsewhere in the chapter
it is used for *distributional* solutions — see
`exists_differentiable_of_isWeakCauchyRiemann` below. -/
theorem contDiffOn_of_isCauchyRiemann {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : DifferentiableOn ℝ u U) (hCR : IsCauchyRiemann U u) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n u U := by
  have hC : DifferentiableOn ℂ u U := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [differentiableAt_complex_iff_differentiableAt_real]
    refine ⟨hu.differentiableAt (hU.mem_nhds hz), ?_⟩
    have h := hCR z hz
    simp only [dds, ddt] at h
    rw [smul_eq_mul]
    linear_combination (-Complex.I) * h + (fderiv ℝ u z Complex.I) * Complex.I_sq
  exact hC.contDiffOn hU

/-- The same conclusion in the real sense, which is the book's phrasing: a `C^1`
solution of the Cauchy–Riemann equation is of class `C^∞`. -/
theorem contDiffOn_real_of_isCauchyRiemann {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : DifferentiableOn ℝ u U) (hCR : IsCauchyRiemann U u) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n u U :=
  ContDiffOn.restrict_scalars (𝕜 := ℝ) (contDiffOn_of_isCauchyRiemann hU hu hCR n)

/-- On an open set, the differentiable solutions of the Cauchy–Riemann equation
are exactly the holomorphic functions.  Together with
`contDiffOn_of_isCauchyRiemann` this is the sharpest form of Lemma 12.1.1 that
the classical theory gives. -/
theorem isCauchyRiemann_iff_differentiableOn {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : DifferentiableOn ℝ u U) :
    IsCauchyRiemann U u ↔ DifferentiableOn ℂ u U := by
  refine ⟨fun hCR z hz => ?_, isCauchyRiemann_of_differentiableOn hU⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hu.differentiableAt (hU.mem_nhds hz), ?_⟩
  have h := hCR z hz
  simp only [dds, ddt] at h
  rw [smul_eq_mul]
  linear_combination (-Complex.I) * h + (fderiv ℝ u z Complex.I) * Complex.I_sq

/-- **Weak (distributional) solutions of the Cauchy–Riemann equation.**

`u` is a weak solution of `∂u/∂s + i ∂u/∂t = 0` on `U` when it integrates to
zero against `∂φ/∂s + i ∂φ/∂t` for every smooth `φ` with compact support inside
`U`; this is the formal adjoint of the operator, up to the harmless global sign.

Mathlib now has test functions and distributions
(`Mathlib.Analysis.Distribution.TestFunction`), but writing the pairing out by
hand keeps the statement independent of the bundled types and matches the
book's own "au sens des distributions". -/
def IsWeakCauchyRiemann (U : Set ℂ) (u : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ z : ℂ, (dds φ z + Complex.I * ddt φ z) * u z = 0

/-- **Lemma 12.1.1 (elliptic regularity), distributional form** — Weyl's lemma
for the operator `∂̄`.

A locally integrable weak solution of `∂u/∂s + i ∂u/∂t = 0` on an open set
agrees almost everywhere with a holomorphic, hence `C^∞`, function.  This is the
statement the book uses: the solutions produced by the analysis live a priori
only in a Sobolev or `L^p` space and satisfy the equation in the sense of
distributions, and regularity upgrades them to genuine smooth solutions.

Proved in `Part2/Weyl.lean` by mollification with a radial kernel, and restated
here: the mollifications of `u` are smooth and satisfy the classical equation,
hence are holomorphic; two of them agree wherever both are holomorphic, by the
mean value property against a radial weight; and they converge to `u` almost
everywhere by the Lebesgue differentiation theorem.  The book's own route is
Proposition 12.3.1, hence the Calderón–Zygmund inequality 16.5.8; the
mollification argument needs neither. -/
theorem exists_differentiable_of_isWeakCauchyRiemann {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : LocallyIntegrableOn u U) (h : IsWeakCauchyRiemann U u) :
    ∃ v : ℂ → ℂ, DifferentiableOn ℂ v U ∧
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → u z = v z :=
  Weyl.exists_differentiableOn_ae_eq hU hu h

end CauchyRiemann

/-! ### The Hölder step in the proof of Theorem 12.1.3

The last paragraph of the proof of Theorem 12.1.3 checks that
`s ↦ ∫₀¹ ‖Y(s,t)‖² dt` does not blow up, by comparing it with the `L^p` integral
through Hölder's inequality with exponent `p/2 ≥ 1`.  On the circle — a
probability space — this is just the monotonicity of the `L^q` norms in `q`. -/

/-- **The inequality `∫₀¹ ‖Y‖² ≤ (∫₀¹ ‖Y‖^p)^{2/p}`** of the proof of Theorem
12.1.3, for `p ≥ 2`, in the form `‖Y‖_{L²} ≤ ‖Y‖_{L^p}` on a probability space.
`S¹` with its normalised length is such a space. -/
theorem eLpNorm_two_le_eLpNorm {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] [NormedAddCommGroup E] {p : ℝ≥0∞} (hp : 2 ≤ p) {Y : α → E} :
    eLpNorm Y 2 μ ≤ eLpNorm Y p μ :=
  eLpNorm_le_eLpNorm_of_exponent_le hp

/-! ## §12.1.c The fil d'Ariane

The chapter's six statements — Lemma 12.1.1, Theorem 12.1.2, Lemma 8.7.2,
Theorem 12.1.3, Proposition 12.1.4, Theorem 12.1.5 — together with the
Calderón–Zygmund inequality 16.5.8 that starts everything off and the
intermediate Proposition 12.3.1, form the "maze" the book untangles with the
diagram of §12.1.c.

None of the eight statements is expressible in Lean (see the module docstring),
but the *architecture* is: it is a chain of implications, and the chapter's
mathematical work consists precisely in establishing the seven arrows.  They are
recorded here as the fields of a structure, and the derivations the book draws
from the diagram are then proved. -/

section Ariane

/-- **The fil d'Ariane of §12.1.c.**

A bundle of the eight propositions of the chapter's diagram together with the
seven implications the chapter proves between them:

* `16.5.8 ⇒ 12.3.1` and `12.3.1 ⇒ 12.1.2` (§12.3);
* `12.1.2 ⇒ 12.1.3` (§12.1.a) and `12.1.2 ⇒ 8.7.2` (§12.2);
* `12.3.1 ⇒ 12.1.5` and `12.1.5 ⇒ 12.1.4` (§12.4);
* `12.1.4 ⇒ 12.1.1`, and more generally `12.1.4 ⇒` any elliptic regularity
  statement used elsewhere in the book (§12.1.b) — the family `other`, indexed
  by `ι`, stands for the book's "et toute autre régularité elliptique", the
  uses in Proposition 6.5.3, Theorem 8.1.2, Lemma 9.4.17 and Chapter 11.

The propositions themselves are parameters: asserting any of them of arbitrary
data would be meaningless, and none of them can be spelled out without Sobolev
spaces.  Following the practice of `MorseFloer.Chapter8`, they are therefore
data the chapter may supply rather than `sorry`ed theorems. -/
structure ArianeThread (ι : Type*) where
  /-- The Calderón–Zygmund inequality, Theorem 16.5.8. -/
  calderonZygmund : Prop
  /-- Proposition 12.3.1: `Δu = f + ∂g/∂s + ∂h/∂t` with `f, g, h ∈ L^p_loc`
  forces `u ∈ W^{1,p}_loc`, with the corresponding estimate. -/
  prop1231 : Prop
  /-- Theorem 12.1.2: a weak solution of `∂̄u = f` with `f ∈ W^{k,p}_loc` lies in
  `W^{k+1,p}_loc`, with the corresponding estimate. -/
  thm1212 : Prop
  /-- Theorem 12.1.5: the same for the operator with a variable, `W^{k,p}_loc`
  almost complex structure `J`. -/
  thm1215 : Prop
  /-- Proposition 12.1.4: a `W^{1,p}_loc` solution of the Floer equation,
  `p > 2`, is `C^∞`, and `C⁰_loc` and `C^∞_loc` agree on the solution space. -/
  prop1214 : Prop
  /-- Theorem 12.1.3: an `L^p` distributional solution of `LY = 0` is `C^∞` and
  lies in `W^{1,p}`. -/
  thm1213 : Prop
  /-- Lemma 8.7.2: the a priori estimate `‖Y‖_{W^{1,p}} ≤ C(‖LY‖_{L^p} +
  ‖Y‖_{L^p})` for the perturbed Cauchy–Riemann operator. -/
  lem872 : Prop
  /-- Lemma 12.1.1: a `C^1` solution of the Floer equation is `C^∞`, and a
  gradient-bounded sequence of solutions is `C^∞_loc` precompact. -/
  lem1211 : Prop
  /-- The other elliptic regularity statements used in the book. -/
  other : ι → Prop
  /-- §12.3, first half: Calderón–Zygmund gives Proposition 12.3.1. -/
  cz_imp_prop1231 : calderonZygmund → prop1231
  /-- §12.3, second half: Proposition 12.3.1 gives Theorem 12.1.2. -/
  prop1231_imp_thm1212 : prop1231 → thm1212
  /-- §12.1.a: Theorem 12.1.2 gives Theorem 12.1.3, by elliptic bootstrapping. -/
  thm1212_imp_thm1213 : thm1212 → thm1213
  /-- §12.2: Theorem 12.1.2 gives Lemma 8.7.2. -/
  thm1212_imp_lem872 : thm1212 → lem872
  /-- §12.4: Proposition 12.3.1 gives Theorem 12.1.5. -/
  prop1231_imp_thm1215 : prop1231 → thm1215
  /-- §12.4.a: Theorem 12.1.5 gives Proposition 12.1.4. -/
  thm1215_imp_prop1214 : thm1215 → prop1214
  /-- §12.1.b: Proposition 12.1.4 gives Lemma 12.1.1. -/
  prop1214_imp_lem1211 : prop1214 → lem1211
  /-- §12.1.b: Proposition 12.1.4 gives every other elliptic regularity
  statement the book uses. -/
  prop1214_imp_other : ∀ i, prop1214 → other i

namespace ArianeThread

variable {ι : Type*} (T : ArianeThread ι)

/-- The composite arrow `16.5.8 ⇒ 12.1.2` of the diagram. -/
theorem cz_imp_thm1212 : T.calderonZygmund → T.thm1212 :=
  T.prop1231_imp_thm1212 ∘ T.cz_imp_prop1231

/-- The composite arrow `16.5.8 ⇒ 12.1.5` of the diagram. -/
theorem cz_imp_thm1215 : T.calderonZygmund → T.thm1215 :=
  T.prop1231_imp_thm1215 ∘ T.cz_imp_prop1231

/-- The left branch of the diagram, `16.5.8 ⇒ 12.1.2 ⇒ 8.7.2`. -/
theorem cz_imp_lem872 : T.calderonZygmund → T.lem872 :=
  T.thm1212_imp_lem872 ∘ T.cz_imp_thm1212

/-- The right branch of the diagram, `16.5.8 ⇒ 12.1.5 ⇒ 12.1.4 ⇒ 12.1.1`. -/
theorem cz_imp_lem1211 : T.calderonZygmund → T.lem1211 :=
  T.prop1214_imp_lem1211 ∘ T.thm1215_imp_prop1214 ∘ T.cz_imp_thm1215

/-- **The chapter, read off the fil d'Ariane.**  Everything follows from the
Calderón–Zygmund inequality. -/
theorem of_calderonZygmund (h : T.calderonZygmund) :
    T.prop1231 ∧ T.thm1212 ∧ T.thm1213 ∧ T.lem872 ∧ T.thm1215 ∧ T.prop1214 ∧
      T.lem1211 ∧ ∀ i, T.other i := by
  have h1231 := T.cz_imp_prop1231 h
  have h1212 := T.prop1231_imp_thm1212 h1231
  have h1215 := T.prop1231_imp_thm1215 h1231
  have h1214 := T.thm1215_imp_prop1214 h1215
  exact ⟨h1231, h1212, T.thm1212_imp_thm1213 h1212, T.thm1212_imp_lem872 h1212, h1215,
    h1214, T.prop1214_imp_lem1211 h1214, fun i => T.prop1214_imp_other i h1214⟩

end ArianeThread

end Ariane

/-! ## §12.2 The proof of Lemma 8.7.2

The proof localises the estimate of Theorem 12.1.2 on the squares
`[k, k+1] × S¹`, uses that the constant-coefficient operator `D^±` commutes with
translation in `s` to get the same constant on every square, raises the
estimates to the power `p`, sums them over `k ∈ ℤ`, absorbs the error term
`ε ‖Y‖_{W^{1,p}}` coming from `‖S − S^±‖ < ε`, and glues the two ends to the
middle with a cut-off function `β`.

Everything about the `W^{1,p}` and `L^p` norms is out of reach; the three purely
numerical steps are proved here. -/

section Section122

/-- **The inequality `(a+b)^p ≤ 2^p (a^p + b^p)`** used to raise the local
estimates of §12.2 to the power `p` before summing them. -/
theorem rpow_add_le_two_rpow_mul {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hmax : (0 : ℝ) ≤ max a b := le_max_of_le_left ha
  have hm : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h1 : (a + b) ^ p ≤ (2 * max a b) ^ p := Real.rpow_le_rpow (by linarith) hm hp0
  have h2 : (2 * max a b) ^ p = 2 ^ p * (max a b) ^ p :=
    Real.mul_rpow (by norm_num) hmax
  have h3 : (max a b) ^ p ≤ a ^ p + b ^ p := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      have : (0 : ℝ) ≤ a ^ p := Real.rpow_nonneg ha p
      linarith
    · rw [max_eq_left h]
      have : (0 : ℝ) ≤ b ^ p := Real.rpow_nonneg hb p
      linarith
  calc (a + b) ^ p ≤ (2 * max a b) ^ p := h1
    _ = 2 ^ p * (max a b) ^ p := h2
    _ ≤ 2 ^ p * (a ^ p + b ^ p) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num) p)

/-- **Summing the local estimates over the integer translates.**

In §12.2 the estimate `‖Y‖^p_{W^{1,p}([k,k+1]×S¹)} ≤ M (‖LY‖^p_{L^p(...)} +
‖Y‖^p_{L^p(...)})` holds for every `k ∈ ℤ` with a constant independent of `k`,
and the global estimate is obtained by summing over `k`.  This is that step,
with the three families of local quantities as abstract summable families. -/
theorem tsum_le_mul_add_tsum {A B C : ℤ → ℝ} {M : ℝ}
    (h : ∀ k, A k ≤ M * (B k + C k))
    (hA : Summable A) (hB : Summable B) (hC : Summable C) :
    ∑' k, A k ≤ M * ((∑' k, B k) + ∑' k, C k) := by
  have h1 : ∑' k, A k ≤ ∑' k, M * (B k + C k) :=
    hA.tsum_le_tsum h ((hB.add hC).mul_left M)
  rwa [tsum_mul_left, hB.tsum_add hC] at h1

/-- **The absorption step of §12.2.**

Once `‖S − S^+‖ < ε` on `[M, +∞[ × S¹`, the estimate for `D^+` gives
`‖Y‖_{W^{1,p}} ≤ C (‖LY‖_{L^p} + ε ‖Y‖_{W^{1,p}} + ‖Y‖_{L^p})`, and for `ε`
small enough — the book takes `ε ≤ 1/2C`, here in the cleared form
`2Cε ≤ 1` — the middle term is absorbed into the left-hand side.

Here `A` is `‖Y‖_{W^{1,p}}`, `B` is `‖LY‖_{L^p}` and `D` is `‖Y‖_{L^p}`. -/
theorem le_two_mul_of_absorb {A B D C ε : ℝ} (hA : 0 ≤ A) (_hC : 0 < C)
    (_hε0 : 0 ≤ ε) (hε : 2 * C * ε ≤ 1)
    (h : A ≤ C * (B + ε * A + D)) : A ≤ 2 * C * (B + D) := by
  nlinarith [mul_le_mul_of_nonneg_right hε hA, h]

end Section122

/-! ## §12.3 The proof of Theorem 12.1.2

The proof reduces `∂̄u = f` to `Δu = ∂g/∂s + ∂h/∂t` by applying `∂` again, and
then proves the more general Proposition 12.3.1 by comparing `u` with the
explicit potential `v = K ⋆ βf + K₁ ⋆ βg + K₂ ⋆ βh`, where `K(z) = (1/2π) log|z|`
is the fundamental solution of the Laplacian and `K₁`, `K₂` are its partial
derivatives.  The difference `u − v` is harmonic, hence smooth, and the norm of
`v` is controlled by Calderón–Zygmund and Young.

Proposition 12.3.1 itself is a `W^{1,p}` statement and is not expressible.  Two
ingredients of its proof are. -/

section Section123

/-- **The harmonic case of Proposition 12.3.1.**

The proof of Proposition 12.3.1 opens with the equation `Δu = 0`: then `u` is
harmonic, satisfies the mean value property (the book's Proposition 16.5.2) and
is therefore `C^∞` (the book's Lemma 16.5.3), hence in `W^{1,p}_loc`.

The first two of those steps are in Mathlib — `InnerProductSpace.HarmonicOnNhd`,
its mean value property `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`, and
the analyticity `HarmonicAt.analyticAt` — so the smoothness half is proved here.
The passage to `W^{1,p}_loc`, and the estimate `‖u‖_{W^{1,p}(V)} ≤ C‖u‖_{L^p(U)}`
that the book derives from `u = ψ ⋆ u`, are not statable. -/
theorem contDiffOn_of_harmonicOnNhd {U : Set ℂ} {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u U) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n u U :=
  fun x hx => ((_root_.HarmonicAt.analyticAt (hu x hx)).contDiffAt).contDiffWithinAt

/-- **The fundamental solution of the Laplacian**, `K(z) = (1/2π) log |z|`,
written in the real coordinates `z = s + it` of `ℝ × S¹`. -/
noncomputable def fundSol (s t : ℝ) : ℝ := Real.log (Real.sqrt (s ^ 2 + t ^ 2)) / (2 * Real.pi)

/-- The book's `K₁(s,t) = s / 2π(s² + t²)`, the `s`-derivative of the fundamental
solution. -/
noncomputable def fundSolS (s t : ℝ) : ℝ := s / (2 * Real.pi * (s ^ 2 + t ^ 2))

/-- The book's `K₂(s,t) = t / 2π(s² + t²)`, the `t`-derivative of the fundamental
solution. -/
noncomputable def fundSolT (s t : ℝ) : ℝ := t / (2 * Real.pi * (s ^ 2 + t ^ 2))

/-- **`K₁ = ∂K/∂s` away from the origin**, as asserted in §12.3. -/
theorem hasDerivAt_fundSol_fst {s t : ℝ} (h : s ^ 2 + t ^ 2 ≠ 0) :
    HasDerivAt (fun σ : ℝ => fundSol σ t) (fundSolS s t) s := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : HasDerivAt (fun σ : ℝ => σ ^ 2 + t ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (t ^ 2)
  have h2 : HasDerivAt (fun σ : ℝ => Real.log (σ ^ 2 + t ^ 2)) (2 * s / (s ^ 2 + t ^ 2)) s :=
    h1.log h
  have h3 : HasDerivAt (fun σ : ℝ => Real.log (σ ^ 2 + t ^ 2) / (4 * Real.pi))
      (2 * s / (s ^ 2 + t ^ 2) / (4 * Real.pi)) s := h2.div_const _
  have heq : (fun σ : ℝ => fundSol σ t)
      = fun σ : ℝ => Real.log (σ ^ 2 + t ^ 2) / (4 * Real.pi) := by
    funext σ
    simp only [fundSol]
    rw [Real.log_sqrt (show (0:ℝ) ≤ σ ^ 2 + t ^ 2 by positivity)]
    ring
  have hval : fundSolS s t = 2 * s / (s ^ 2 + t ^ 2) / (4 * Real.pi) := by
    simp only [fundSolS]
    field_simp
    try ring
  rw [heq, hval]
  exact h3

/-- **`K₂ = ∂K/∂t` away from the origin**, as asserted in §12.3. -/
theorem hasDerivAt_fundSol_snd {s t : ℝ} (h : s ^ 2 + t ^ 2 ≠ 0) :
    HasDerivAt (fun τ : ℝ => fundSol s τ) (fundSolT s t) t := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : HasDerivAt (fun τ : ℝ => τ ^ 2 + s ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const (s ^ 2)
  have h' : t ^ 2 + s ^ 2 ≠ 0 := by rwa [add_comm]
  have h2 : HasDerivAt (fun τ : ℝ => Real.log (τ ^ 2 + s ^ 2)) (2 * t / (t ^ 2 + s ^ 2)) t :=
    h1.log h'
  have h3 : HasDerivAt (fun τ : ℝ => Real.log (τ ^ 2 + s ^ 2) / (4 * Real.pi))
      (2 * t / (t ^ 2 + s ^ 2) / (4 * Real.pi)) t := h2.div_const _
  have heq : (fun τ : ℝ => fundSol s τ)
      = fun τ : ℝ => Real.log (τ ^ 2 + s ^ 2) / (4 * Real.pi) := by
    funext τ
    simp only [fundSol]
    rw [Real.log_sqrt (show (0:ℝ) ≤ s ^ 2 + τ ^ 2 by positivity),
      show s ^ 2 + τ ^ 2 = τ ^ 2 + s ^ 2 from by ring]
    ring
  have hval : fundSolT s t = 2 * t / (t ^ 2 + s ^ 2) / (4 * Real.pi) := by
    simp only [fundSolT]
    field_simp
    try ring
  rw [heq, hval]
  exact h3

end Section123

/-! ## §12.4 The nonlinear regularity

Theorem 12.1.5 is proved by applying Lemma 12.4.2 repeatedly.  Lemma 12.4.2
takes three exponents `p > 2`, `r > 1` with `1/p + 1/q = 1/r` and concludes
`u ∈ W^{1,r}_loc` from `u ∈ L^q_loc`; feeding its conclusion back in through the
Sobolev embedding `W^{1,r}_loc ⊆ L^{2r/(2−r)}_loc` produces the recursion

`r ↦ 2pr / (2p + 2r − pr)`

on the exponents.  The point of the proof — and the only place where `p > 2` is
really needed — is that this recursion increases `r` and escapes the interval
`]1, 2[` after finitely many steps, after which `u ∈ L^∞_loc` and one last
application of Lemma 12.4.2 with `q = ∞` gives `u ∈ W^{1,p}_loc`.

Lemma 12.4.2, Corollary 12.4.1, Theorem 12.1.5, Proposition 12.1.4 and
Lemma 12.4.4 are all `W^{k,p}` statements and are not expressible.  The
recursion is pure arithmetic and is proved here in full. -/

section Bootstrap

/-- **The bootstrapping recursion on the exponents**, `r ↦ 2pr/(2p + 2r − pr)`.

This is the exponent `r'` defined in the proof of Theorem 12.1.5 by
`1/r' = 1/p + 1/q` where `q = 2r/(2−r)` is the exponent supplied by the Sobolev
embedding of `W^{1,r}`. -/
noncomputable def bootstrapExp (p r : ℝ) : ℝ := 2 * p * r / (2 * p + 2 * r - p * r)

/-- The denominator `2p + 2r − pr` of the recursion is positive on the range
where it is used, `1 < r < 2 < p`. -/
theorem bootstrapExp_denom_pos {p r : ℝ} (hp : 2 < p) (hr2 : r < 2) (_hr0 : 0 < r) :
    0 < 2 * p + 2 * r - p * r := by
  nlinarith

/-- `bootstrapExp` really is defined by `1/r' = 1/p + 1/q` with `q = 2r/(2−r)`:
that is the identity `1/r' = 1/r + 1/p − 1/2`, which exhibits the recursion, in
terms of the reciprocal exponents, as the *translation* by the positive constant
`1/2 − 1/p`.  This is where `p > 2` enters. -/
theorem inv_bootstrapExp {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0)
    (_hD : 2 * p + 2 * r - p * r ≠ 0) :
    (bootstrapExp p r)⁻¹ = r⁻¹ + p⁻¹ - 2⁻¹ := by
  simp only [bootstrapExp]
  field_simp

/-- **The identity `r' − 2 = 4[(p−1)(r−1) − 1] / (2p + 2r − pr)`** of §12.4.b,
which is how the book sees that the recursion crosses `2` as soon as `r` is
close enough to `2`. -/
theorem bootstrapExp_sub_two {p r : ℝ} (hD : 2 * p + 2 * r - p * r ≠ 0) :
    bootstrapExp p r - 2 = 4 * ((p - 1) * (r - 1) - 1) / (2 * p + 2 * r - p * r) := by
  simp only [bootstrapExp]
  set D := 2 * p + 2 * r - p * r with hDdef
  field_simp
  rw [hDdef]
  ring

/-- **The recursion is strictly increasing on `]1, 2[`**: `r' > r` whenever
`1 < r < 2` and `p > 2`.  The difference is `r²(p−2)/(2p + 2r − pr)`. -/
theorem lt_bootstrapExp {p r : ℝ} (hp : 2 < p) (hr1 : 1 < r) (hr2 : r < 2) :
    r < bootstrapExp p r := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hD : 0 < 2 * p + 2 * r - p * r := bootstrapExp_denom_pos hp hr2 hr0
  have key : bootstrapExp p r - r = r ^ 2 * (p - 2) / (2 * p + 2 * r - p * r) := by
    simp only [bootstrapExp]
    set D := 2 * p + 2 * r - p * r with hDdef
    have hD' : D ≠ 0 := ne_of_gt hD
    field_simp
    rw [hDdef]
    ring
  have hpos : 0 < r ^ 2 * (p - 2) / (2 * p + 2 * r - p * r) :=
    div_pos (mul_pos (pow_pos hr0 2) (by linarith)) hD
  linarith

/-- `bootstrapExp` is positive on the range where it is used. -/
theorem bootstrapExp_pos {p r : ℝ} (hp : 2 < p) (hr0 : 0 < r) (hr2 : r < 2) :
    0 < bootstrapExp p r := by
  have hD : 0 < 2 * p + 2 * r - p * r := bootstrapExp_denom_pos hp hr2 hr0
  simp only [bootstrapExp]
  exact div_pos (by nlinarith) hD

/-- **The recursion escapes `]1, 2[` in finitely many steps.**

This is the crux of Step 1 of the proof of Theorem 12.1.5: the book's sequence
`r₀ ∈ ]1, 2[`, `r_{m+1} = 2p r_m/(2p + 2r_m − p r_m)` cannot stay below `2`
forever, because in terms of the reciprocals it is the arithmetic progression
`1/r_{m+1} = 1/r_m − (1/2 − 1/p)` with a strictly positive step — this is
exactly the hypothesis `p > 2` — and the reciprocal of a number in `]0, 2[`
exceeds `1/2`.

The sequence is given abstractly: `r` need only obey the recursion for as long
as it stays below `2`, which is all the proof provides. -/
theorem exists_two_le_of_bootstrap {p : ℝ} (hp : 2 < p) (r : ℕ → ℝ) (h0 : 0 < r 0)
    (hstep : ∀ m, r m < 2 → r (m + 1) = bootstrapExp p (r m)) :
    ∃ m, 2 ≤ r m := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hp0 : (0 : ℝ) < p := by linarith
  have hpos : ∀ m, 0 < r m := by
    intro m
    induction m with
    | zero => exact h0
    | succ n ih =>
      rw [hstep n (hcon n)]
      exact bootstrapExp_pos hp ih (hcon n)
  have hipos : (0 : ℝ) < p⁻¹ := inv_pos.mpr hp0
  have hkey : p⁻¹ * p = 1 := inv_mul_cancel₀ (ne_of_gt hp0)
  have hc : (0 : ℝ) < 2⁻¹ - p⁻¹ := by
    nlinarith [mul_pos hipos (show (0:ℝ) < p - 2 by linarith), hkey]
  have hinv : ∀ m, (r m)⁻¹ = (r 0)⁻¹ - m * (2⁻¹ - p⁻¹) := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      have hD : 2 * p + 2 * r n - p * r n ≠ 0 :=
        ne_of_gt (bootstrapExp_denom_pos hp (hcon n) (hpos n))
      rw [hstep n (hcon n), inv_bootstrapExp (ne_of_gt hp0) (ne_of_gt (hpos n)) hD, ih]
      push_cast
      ring
  obtain ⟨m, hm⟩ := Archimedean.arch ((r 0)⁻¹) hc
  rw [nsmul_eq_mul] at hm
  have hlow : (2 : ℝ)⁻¹ < (r m)⁻¹ := by
    have hrm := hpos m
    have hinvm : (0 : ℝ) < (r m)⁻¹ := inv_pos.mpr hrm
    nlinarith [inv_mul_cancel₀ (ne_of_gt hrm),
      mul_pos hinvm (show (0:ℝ) < 2 - r m by linarith [hcon m])]
  have := hinv m
  linarith

/-- **Remark 12.4.3(1).**  In Lemma 12.4.2 the exponents satisfy
`1/p + 1/q = 1/r` with `p > 2`, so for `r < 2` one automatically has
`q < 2r/(2−r)` — that is, `q` is below the exponent supplied by the Sobolev
embedding `W^{1,r}_loc ⊆ L^{2r/(2−r)}_loc`, which is why the bootstrapping can
feed the conclusion of the lemma back into its hypothesis. -/
theorem lt_sobolevExp {p q r : ℝ} (hp : 2 < p) (hq : 0 < q) (hr1 : 1 < r) (hr2 : r < 2)
    (h : 1 / p + 1 / q = 1 / r) : q < 2 * r / (2 - r) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have h2r : (0 : ℝ) < 2 - r := by linarith
  have hp' : p ≠ 0 := ne_of_gt hp0
  have hq' : q ≠ 0 := ne_of_gt hq
  have hr' : r ≠ 0 := ne_of_gt hr0
  have key : q * r + p * r = p * q := by
    have e1 : (1 / p + 1 / q) * (p * q * r) = q * r + p * r := by
      field_simp
      try ring
    have e2 : (1 / r) * (p * q * r) = p * q := by
      field_simp
      try ring
    rw [← e1, h, e2]
  rw [lt_div_iff₀ h2r]
  nlinarith [key, hp0, mul_pos (mul_pos hq hr0) (show (0:ℝ) < p - 2 by linarith)]

end Bootstrap

end Chapter12
end MorseFloer
