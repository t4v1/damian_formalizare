import MorseFloer.Part1.Ch3
import MorseFloer.Part2.Ch8

/-!
# Chapter 9: Floer homology — the spaces of trajectories

Formalization of Chapter 9 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 275–330).

Chapter 9 is the analytic engine room of Floer homology.  Given a generic
Hamiltonian `H` on a symplectic manifold `W` satisfying the hypotheses of
Chapter 6, the `1`-periodic orbits are finite in number and graded by their
Conley–Zehnder index `μ`; the chapter builds out of them a chain complex

`∂ : C_k(H) → C_{k−1}(H)`,  `∂ x = Σ_{μ(y) = k−1} n(x,y) · y`,

where `n(x,y)` counts modulo `2` the trajectories of the gradient of the action
functional joining `x` to `y`.  Making sense of `n(x,y)` and proving `∂ ∘ ∂ = 0`
is exactly what the chapter does:

* **§9.1** introduces `L(x,y) = M(x,y)/ℝ`, the space of *unparametrised*
  trajectories, with the quotient topology (Remark 9.1.1 distinguishes a
  solution from a trajectory).  Proposition 9.1.2 says a sequence of solutions
  cannot have two essentially different limits up to the `ℝ`-action, whence
  Corollary 9.1.3: the quotient is Hausdorff.  §9.1.b explains what has to be
  proved, and §9.1.c proves Theorem 9.1.6: a sequence in `M(x,y)` subconverges,
  after reparametrisation, to a *broken* trajectory `x = x₀ → x₁ → ⋯ → x_{ℓ+1} =
  y`.  Corollary 9.1.8: the compactified space `L̄(x,y)` is compact.
* **§9.2** states the gluing package.  Theorem 9.2.1: when `μ(x) = μ(z) + 2`,
  `L̄(x,z)` is a compact `1`-manifold with boundary `⋃_y L(x,y) × L(y,z)`;
  Corollary 9.2.2: `∂ ∘ ∂ = 0`; Theorem 9.2.3: the gluing map `ψ` embeds a
  half-line `[ρ₀, ∞)` into `L(x,z)` converging to a given broken trajectory
  `(u,v)`, and every sequence converging to `(u,v)` eventually lies in its
  image.
* **§9.3** is the *pre-gluing*: an explicit interpolation `w_ρ` between `u` and
  `v`, built from two smooth cut-off functions `β^±`, which solves the Floer
  equation approximately.
* **§9.4** constructs `ψ(ρ) = exp_{w_ρ} γ(ρ)` by a Newton–Picard method
  (Lemma 9.4.4) applied to the nonlinear operator `F_ρ = F ∘ exp_{w_ρ}`, whose
  linearisation `L_ρ` is Fredholm of index `2` (Proposition 9.4.3).
* **§§9.5–9.6** verify that `ψ` is an immersion, is injective, and is unique.

## How the geometric input is handled here

As in `MorseFloer.Part1.Ch3` (which takes the count of broken trajectories as an
explicit hypothesis `BrokenPairs`) and in `MorseFloer.Part2.Ch8` (which bundles
the Floer-analytic data into a `FloerData` and records the book's theorems as
*predicates* the data may satisfy), the input of Chapters 6, 7, 8, 12 and 13 is
taken here as abstract parameters:

* `Orbit` is the (finite) set of contractible `1`-periodic orbits, `cz : Orbit →
  ℤ` is the Conley–Zehnder index (`FloerData.cz` of Chapter 8);
* `Sol x y` stands for `M(x,y)`, the space of Floer trajectories from `x` to
  `y`, and it carries a topology and an `ℝ`-action — the translation
  `u ↦ u(· + σ, ·)` of §9.1.a.

Nothing below asserts of arbitrary such data a statement that would be false:
where the book's theorem is a genuine property of the *Floer* data, it appears
as a `def … : Prop` predicate (`UniqueLimitUpToShift`, `HasBrokenLimits`,
`IsolatedTrajectories`, `EvenBrokenBoundary`, `BrokenPairs`), following
Chapter 8's practice.  **A later pass must connect these predicates to
Chapter 6's Floer operator and to Chapters 12–13's estimates**; Chapters 6, 7,
10 and 11 are being formalized concurrently and are deliberately not imported.

## What is proved here

The chapter's payload for Floer homology, in full:

* `Traj S = S/ℝ`, `proj`, `proj_eq_iff`, `continuous_proj`,
  `isOpenQuotientMap_proj` — the space of trajectories `L(x,y)` of §9.1.a with
  its quotient topology, and the fact that the projection is an open quotient
  map;
* `tendsto_proj_of_tendsto_vadd` — the easy half of the description of
  convergence in `L(x,y)` given after Remark 9.1.1;
* `IsFreeShift`, `injective_vadd` — Remark 9.1.5: the `ℝ`-action on a
  nonconstant solution is free, the analogue of Chapter 2's
  `injective_flow_of_mem_trajectorySet`;
* `UniqueLimitUpToShift` (**Proposition 9.1.2**), `isSeqClosed_shiftRel`,
  `t2Space_traj_of_isClosed` and `t2Space_traj` (**Corollary 9.1.3**): the
  proposition makes the "same trajectory" relation sequentially closed, hence
  closed, hence the quotient is Hausdorff.  Both implications are **proved**;
* `HasBrokenLimits` — **Theorem 9.1.6**, the broken-trajectory convergence, as a
  predicate;
* `OrbitSet`, `FloerChains`, `floerCount`, `floerDiff`, `BrokenPairs`,
  `floerDiff_comp_floerDiff`, `floerComplex`, `floerHomology`, `floerCycles`,
  `floerBoundaries`, `floerBoundaries_le_cycles` — **the Floer complex**
  (§9.1, Corollary 9.2.2), graded by the Conley–Zehnder index, hence over `ℤ`
  and not over `ℕ` as in Chapter 3.  `∂ ∘ ∂ = 0` is **proved** from
  `BrokenPairs`, and the complex is an honest `ChainComplex (ModuleCat R) ℤ`,
  i.e. a `HomologicalComplex` for `ComplexShape.down ℤ`;
* `EvenBrokenBoundary` and `brokenPairs_floerCount` — the bridge from geometry
  to algebra, **proved**: if the boundary of `L̄(x,z)` (a compact `1`-manifold,
  by Theorem 9.2.1) has an even number of points, then the counts `n(x,y)`
  satisfy `BrokenPairs`, and therefore `∂ ∘ ∂ = 0`.  This is Corollary 9.2.2,
  reduced to its one geometric input;
* `BrokenTraj`, `brokenBoundary` — the underlying *set* of the compactified
  space `L̄(x,z)` of §9.1.b and of its boundary;
* `smoothStep`, `cutoffPos`, `cutoffNeg` and their properties — **§9.3**'s two
  cut-off functions `β^±`, constructed and **proved** to be smooth, to take the
  prescribed values `0` and `1`, and to have values in `[0,1]`;
* `newtonPicard` — **Lemma 9.4.4**, the abstract Newton–Picard method, stated
  for Banach spaces exactly as in the book and **proved** by Banach's fixed
  point theorem, together with the elementary lemmas `npMap`,
  `eq_zero_of_isFixedPt`, `isFixedPt_of_eq_zero`, `npMap_sub` that make its
  proof work;
* `fredholmIndex_preglue_eq_two` (**Proposition 9.4.3**) and
  `finrank_ker_preglue_eq_two`: the index bookkeeping, proved from the
  hypotheses of Theorem 8.1.5 through `MorseFloer.Chapter16.fredholmIndex` and
  Chapter 8's `fredholmIndex_eq_finrank_ker_of_surjective`.  The second is the
  first consequence of Proposition 9.4.7, `dim Ker L_ρ = 2`;
* `closedComplemented_of_finiteDimensional` — the abstract content of
  **Lemma 9.4.6** available in Mathlib: a finite-dimensional subspace of a
  normed space is complemented by a closed subspace;
* `exists_subseq_tendsto_ker` — **Lemma 9.4.11**: a bounded sequence on which a
  Fredholm operator tends to `0` has a subsequence converging to an element of
  the kernel.  **Proved**, from a quasi-inverse modulo a compact operator
  (the book quotes Proposition 16.2.5 for that).

## Gaps: what today's Mathlib cannot state

Mathlib has **no Sobolev spaces** (`W^{1,p}(ℝ × S¹; ℝ^{2n})`, `L^p(ℝ × S¹;
ℝ^{2n})`), **no Banach manifold of paths** `P^{1,p}(x,y)`, **no moduli spaces**
and **no manifolds with boundary** as a workable structure.  Consequently the
following results of the chapter carry no Lean declaration, and none is faked:

* **Corollary 9.1.8** (`L̄(x,z)` is compact) and **Theorem 9.2.1** (`L̄(x,z)` is
  a compact `1`-manifold with boundary `⋃_y L(x,y) × L(y,z)`).  The underlying
  *set* `L̄(x,z)` is defined here as `BrokenTraj`, but the topology on it is
  defined by the convergence of Theorem 9.1.6 and is not available, so neither
  compactness nor the manifold-with-boundary structure is expressible.  Their
  joint consequence — an even number of boundary points — is exactly the
  predicate `EvenBrokenBoundary`, from which `∂ ∘ ∂ = 0` is proved.
* **Theorem 9.2.3** (the gluing theorem: existence of the embedding
  `ψ : [ρ₀, ∞) → L(x,z)` with `lim ψ = (u,v)`, and the uniqueness statement)
  and **Remark 9.2.4**.  It speaks about `M(x,z)` as a Banach manifold and about
  the topology of `L̄(x,z)`.
* **All of §9.3 apart from the cut-off functions**: the pre-glued approximate
  solution `w_ρ = exp_{y(t)}(β^−·exp⁻¹u + β^+·exp⁻¹v)` and its properties, the
  linear pre-gluing `Y #_ρ Z`, Remark 9.3.1.  These need the exponential map of
  a Riemannian metric on `W` (Mathlib has no Riemannian geometry) and
  `C^∞_loc` convergence of maps `ℝ × S¹ → W`.
* **All of §9.4 apart from what is listed above**: the trivialisations `Z^ρ_i`
  along `w_ρ`, the operator `F_ρ = F ∘ exp_{w_ρ}` and Remarks 9.4.1, 9.4.2, the
  subspaces `W_ρ` and `W_ρ^⊥` (an `L²`-orthogonal inside `W^{1,p}`) and
  Remarks 9.4.5, the uniform estimate **Proposition 9.4.7** and its consequences
  (2)–(4), the technical Lemmas 9.4.8, 9.4.9, 9.4.10, 9.4.12, 9.4.13 and 9.4.16,
  the implicit-function Lemma 9.4.14 and **Proposition 9.4.15**, and
  Lemma 9.4.17.
* **All of §9.5 and §9.6**: that `ψ` is an immersion (Lemma 9.5.1) and the
  uniqueness of the gluing (Propositions 9.6.1, 9.6.3, 9.6.4, 9.6.5, 9.6.7,
  9.6.8, Corollary 9.6.6, Lemmas 9.6.9, 9.6.11–9.6.18).  Every one of them is a
  statement about `W^{1,p}` sections along a pre-glued map, about `C^∞_loc`
  convergence, or about the action functional `A_H` on the loop space.

There is exactly one *misprint* worth recording: Theorem 9.2.1 as printed writes
the boundary as the union over `μ(x) < μ(y) < μ(z)`, which is empty since
`μ(x) = μ(z) + 2`; the intended range is `μ(z) < μ(y) < μ(x)`, and that is what
`brokenBoundary` uses.
-/

open Filter Topology Set
open CategoryTheory
open scoped NNReal

namespace MorseFloer
namespace Chapter9

/-! ## §9.1.a  The space `L(x,y)` and its topology

`M(x,y)` is acted on by `ℝ` by translation in the `s` variable, `u · σ =
u(σ + ·, ·)`, and `L(x,y)` is the quotient.  In this section `S` is an abstract
stand-in for `M(x,y)`: a topological space with a continuous `ℝ`-action. -/

section TrajectorySpace

/-- **The space of trajectories `L(x,y) = M(x,y)/ℝ`** (§9.1.a).

Remark 9.1.1: a *solution* is a point of `M(x,y)`, a *trajectory* is its class
in `L(x,y)`.  The topology is the quotient topology. -/
abbrev Traj (S : Type*) [AddAction ℝ S] : Type _ := Quotient (AddAction.orbitRel ℝ S)

variable {S : Type*} [TopologicalSpace S] [AddAction ℝ S]

/-- The projection `π : M(x,y) → L(x,y)` sending a solution to its trajectory. -/
def proj (u : S) : Traj S := Quotient.mk (AddAction.orbitRel ℝ S) u

omit [TopologicalSpace S] in
theorem proj_surjective : Function.Surjective (proj : S → Traj S) :=
  Quotient.mk_surjective

omit [TopologicalSpace S] in
/-- Two solutions define the same trajectory exactly when they differ by a time
shift. -/
theorem proj_eq_iff {u v : S} : (proj u : Traj S) = proj v ↔ ∃ σ : ℝ, σ +ᵥ v = u := by
  constructor
  · intro h
    have h' : u ∈ AddAction.orbit ℝ v := Quotient.exact h
    exact AddAction.mem_orbit_iff.mp h'
  · rintro ⟨σ, rfl⟩
    exact Quotient.sound (AddAction.mem_orbit_iff.mpr ⟨σ, rfl⟩)

omit [TopologicalSpace S] in
@[simp]
theorem proj_vadd (σ : ℝ) (u : S) : (proj (σ +ᵥ u) : Traj S) = proj u :=
  proj_eq_iff.mpr ⟨σ, rfl⟩

theorem continuous_proj : Continuous (proj : S → Traj S) := continuous_quot_mk

/-- The projection `M(x,y) → L(x,y)` is an **open** quotient map, because it is
the quotient by the action of a group acting by homeomorphisms. -/
theorem isOpenQuotientMap_proj [ContinuousConstVAdd ℝ S] :
    IsOpenQuotientMap (proj : S → Traj S) :=
  AddAction.isOpenQuotientMap_quotientMk

theorem isOpenMap_proj [ContinuousConstVAdd ℝ S] : IsOpenMap (proj : S → Traj S) :=
  isOpenQuotientMap_proj.isOpenMap

/-- **The easy half of the description of convergence in `L(x,y)`** given just
after Remark 9.1.1: if some translates `u_n · s_n` converge to `u` in `M(x,y)`,
then the trajectories `[u_n]` converge to `[u]` in `L(x,y)`.

(The converse — that every convergent sequence of trajectories comes from such a
sequence of translates — is a statement about the quotient topology of a space
of maps and is not proved here.) -/
theorem tendsto_proj_of_tendsto_vadd {ι : Type*} {l : Filter ι} {u : ι → S} {s : ι → ℝ} {a : S}
    (h : Tendsto (fun n => s n +ᵥ u n) l (𝓝 a)) :
    Tendsto (fun n => (proj (u n) : Traj S)) l (𝓝 (proj a)) := by
  have h' : Tendsto (fun n => (proj (s n +ᵥ u n) : Traj S)) l (𝓝 (proj a)) :=
    (continuous_proj.tendsto a).comp h
  simpa using h'

/-! ### Remark 9.1.5: the action is free

The `ℝ`-action on a nonconstant solution is free — this is what makes `L(x,y)`
a manifold of dimension `μ(x) − μ(y) − 1` once `M(x,y)` is one of dimension
`μ(x) − μ(y)`.  It is the exact analogue of Chapter 2's
`injective_flow_of_mem_trajectorySet` for the Morse case. -/

/-- **Remark 9.1.5**: the `ℝ`-action on the space of (nonconstant) solutions is
free.  Stated as a predicate, because it fails for the constant solutions
`M(x,x)`. -/
def IsFreeShift (S : Type*) [AddAction ℝ S] : Prop :=
  ∀ (σ : ℝ) (u : S), σ +ᵥ u = u → σ = 0

omit [TopologicalSpace S] in
/-- A free action means distinct times give distinct solutions: the orbit map
`σ ↦ u · σ` is injective. -/
theorem injective_vadd (h : IsFreeShift S) (u : S) :
    Function.Injective (fun σ : ℝ => σ +ᵥ u) := by
  intro σ τ hστ
  simp only at hστ
  have key : (σ - τ) +ᵥ (τ +ᵥ u) = τ +ᵥ u := by
    rw [vadd_vadd, show σ - τ + τ = σ by ring, hστ]
  have h0 := h _ _ key
  linarith

/-! ### Proposition 9.1.2 and Corollary 9.1.3 -/

/-- The relation "lie on the same trajectory", as a subset of `M(x,y) ×
M(x,y)`. -/
def shiftRel (S : Type*) [AddAction ℝ S] : Set (S × S) := {p | ∃ σ : ℝ, σ +ᵥ p.2 = p.1}

theorem shiftRel_eq_setOf_proj_eq (S : Type*) [TopologicalSpace S] [AddAction ℝ S] :
    shiftRel S = {q : S × S | (proj q.1 : Traj S) = proj q.2} := by
  ext p
  exact proj_eq_iff.symm

/-- **Proposition 9.1.2**, as a predicate on the space of solutions.

If a sequence `u_n` of solutions has two reparametrisations `u_n · s_n` and
`u_n · σ_n` converging to solutions `a` and `b` leaving the same orbit `x` and
arriving at critical points different from `x`, then `a` and `b` are the same
trajectory: `b = a · s₀` for some `s₀`.

The book's proof uses that the action functional `A_H` decreases strictly along
Floer trajectories and separates the critical points involved; nothing of that
is expressible with abstract data, so this is a hypothesis about the data, not
a theorem.  What *is* proved below is everything the chapter deduces from
it. -/
def UniqueLimitUpToShift (S : Type*) [TopologicalSpace S] [AddAction ℝ S] : Prop :=
  ∀ (u : ℕ → S) (s σ : ℕ → ℝ) (a b : S),
    Tendsto (fun n => s n +ᵥ u n) atTop (𝓝 a) →
    Tendsto (fun n => σ n +ᵥ u n) atTop (𝓝 b) →
    ∃ s₀ : ℝ, s₀ +ᵥ a = b

/-- Proposition 9.1.2 says precisely that the relation "lie on the same
trajectory" is sequentially closed: this is the content of the uniqueness of
the limit. -/
theorem isSeqClosed_shiftRel (h : UniqueLimitUpToShift S) : IsSeqClosed (shiftRel S) := by
  intro x p hx hp
  choose σ hσ using hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hp
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hp
  have hz : Tendsto (fun n => (0 : ℝ) +ᵥ (x n).2) atTop (𝓝 p.2) := by
    simpa using h2
  have hs : Tendsto (fun n => σ n +ᵥ (x n).2) atTop (𝓝 p.1) := by
    simpa only [hσ] using h1
  exact h (fun n => (x n).2) (fun _ => 0) σ p.2 p.1 hz hs

/-- **Corollary 9.1.3**, from a closed relation.  If the "same trajectory"
relation is closed, then the quotient topology on `L(x,y)` is Hausdorff.

This uses that the projection is an *open* quotient map, which is the case for
any continuous action of a topological group. -/
theorem t2Space_traj_of_isClosed [ContinuousConstVAdd ℝ S] (h : IsClosed (shiftRel S)) :
    T2Space (Traj S) := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_proj (S := S))]
  rwa [← shiftRel_eq_setOf_proj_eq]

/-- **Corollary 9.1.3.**  Proposition 9.1.2 implies that `L(x,y)` is Hausdorff.

The relation is sequentially closed by `isSeqClosed_shiftRel`, hence closed
because `M(x,y) × M(x,y)` is first countable (`M(x,y)` is a metric space in the
book), hence the quotient is `T₂`. -/
theorem t2Space_traj [ContinuousConstVAdd ℝ S] [FirstCountableTopology S]
    (h : UniqueLimitUpToShift S) : T2Space (Traj S) :=
  t2Space_traj_of_isClosed (isSeqClosed_shiftRel h).isClosed

end TrajectorySpace

/-! ## §9.1.c  Broken trajectories

Theorem 9.1.6 describes the failure of compactness of `M(x,y)`: a sequence of
solutions subconverges, after suitable translations, to a chain of trajectories
running through intermediate critical points.  It is stated for an abstract
space `S` of solutions equipped with the two maps recording the ends of a
trajectory. -/

section BrokenLimits

variable {S : Type*} [TopologicalSpace S] [AddAction ℝ S] {Orbit : Type*}

/-- **Theorem 9.1.6** (convergence to a broken trajectory), as a predicate.

For every sequence `u_n` of solutions from `x` to `y` there are a subsequence,
intermediate critical points `x = c₀, c₁, …, c_{ℓ+1} = y`, translation sequences
`σ_k` and solutions `v_k ∈ M(c_k, c_{k+1})` with `u_{φ(n)} · σ_k(n) → v_k` for
each `k ≤ ℓ`.

The book's proof tracks the first exit of `u_n` from a small ball around each
successive critical point of the action functional, and uses the compactness of
the space `M` of finite-energy solutions (Theorem 6.5.6).  Neither is
expressible here, so this is a property the data may have. -/
def HasBrokenLimits (src tgt : S → Orbit) : Prop :=
  ∀ (x y : Orbit) (u : ℕ → S), (∀ n, src (u n) = x) → (∀ n, tgt (u n) = y) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (l : ℕ) (c : ℕ → Orbit) (σ : ℕ → ℕ → ℝ) (v : ℕ → S),
        c 0 = x ∧ c (l + 1) = y ∧
        (∀ k ≤ l, src (v k) = c k ∧ tgt (v k) = c (k + 1)) ∧
        (∀ k ≤ l, Tendsto (fun n => σ k n +ᵥ u (φ n)) atTop (𝓝 (v k)))

end BrokenLimits

/-! ## §9.1.b and §9.2  The Floer complex

This is the chapter's payload.  `C_k(H)` is the `Z/2`-vector space on the
`1`-periodic orbits of Conley–Zehnder index `k`, the differential counts
trajectories with an index drop of one, and Theorem 9.2.1 makes the once-broken
trajectories cancel in pairs, which is `∂ ∘ ∂ = 0` (Corollary 9.2.2).

Everything is set up as in `MorseFloer.Part1.Ch3`, with one difference: the
Morse index is a natural number while the Conley–Zehnder index is an *integer*,
so the complex is graded by `ℤ` and is a `HomologicalComplex` for
`ComplexShape.down ℤ` rather than a `ChainComplex … ℕ`. -/

section FloerComplex

variable {Orbit : Type*} [Fintype Orbit] (cz : Orbit → ℤ)

/-- `Orbit_k`, the set of `1`-periodic orbits of Conley–Zehnder index `k`. -/
abbrev OrbitSet (k : ℤ) := {c : Orbit // cz c = k}

/-- `C_k(H)`: the free `R`-module on the periodic orbits of Conley–Zehnder index
`k` (§9.1).  For `R = ZMod 2` this is the book's `C_k(H)`. -/
abbrev FloerChains (R : Type*) (k : ℤ) := OrbitSet cz k → R

variable {cz}

/-- **The Floer differential**, in the form `C_i → C_j` for arbitrary degrees.

On a basis element `a` it is `Σ_b cnt a b · b`; only the values of `cnt` on
pairs of orbits with `μ(a) = μ(b) + 1` are ever used, and the complex below
installs this map only when `i = j + 1`.

Keeping `i` and `j` independent avoids all dependent-type casts when building
the `ℤ`-graded complex. -/
def floerDiff {R : Type*} [CommRing R] (cnt : Orbit → Orbit → R) (i j : ℤ) :
    FloerChains cz R i →ₗ[R] FloerChains cz R j where
  toFun x := fun b => ∑ a : OrbitSet cz i, x a * cnt a.1 b.1
  map_add' x y := by
    funext b
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    funext b
    simp [Finset.mul_sum, mul_assoc]

@[simp]
theorem floerDiff_apply {R : Type*} [CommRing R] (cnt : Orbit → Orbit → R) (i j : ℤ)
    (x : FloerChains cz R i) (b : OrbitSet cz j) :
    floerDiff cnt i j x b = ∑ a : OrbitSet cz i, x a * cnt a.1 b.1 := rfl

/-- **The broken-trajectory hypothesis** for the Floer complex.

For orbits `a` of index `k+2` and `b` of index `k`, the number of once-broken
trajectories from `a` to `b`, namely `Σ_c cnt a c · cnt c b`, vanishes.

This is the conclusion of **Theorem 9.2.1** combined with the fact that a
compact `1`-manifold has an even number of boundary points: `L̄(a,b)` is such a
manifold and its boundary is `⋃_c L(a,c) × L(c,b)`.  Neither statement is
expressible in Mathlib, so the consequence is taken as the hypothesis — exactly
as `MorseFloer.Chapter3.BrokenPairs` does in the Morse case.  See
`brokenPairs_floerCount` for the derivation from the geometric input. -/
def BrokenPairs {R : Type*} [CommRing R] (cz : Orbit → ℤ) (cnt : Orbit → Orbit → R) : Prop :=
  ∀ (k : ℤ) (a : OrbitSet cz (k + 2)) (b : OrbitSet cz k),
    ∑ c : OrbitSet cz (k + 1), cnt a.1 c.1 * cnt c.1 b.1 = 0

/-- The broken-trajectory hypothesis in the form the `ℤ`-graded complex needs:
for any three degrees with `i = j + 1` and `j = k + 1`. -/
theorem BrokenPairs.of_rel {R : Type*} [CommRing R] {cnt : Orbit → Orbit → R}
    (h : BrokenPairs cz cnt) {i j k : ℤ} (hij : j + 1 = i) (hjk : k + 1 = j)
    (a : OrbitSet cz i) (b : OrbitSet cz k) :
    ∑ c : OrbitSet cz j, cnt a.1 c.1 * cnt c.1 b.1 = 0 := by
  subst hij
  subst hjk
  exact h k ⟨a.1, by have := a.2; omega⟩ b

/-- **`∂ ∘ ∂ = 0` for the Floer complex** (Corollary 9.2.2).

Expanding the composite, the coefficient of `b` in `∂∂a` is `Σ_c cnt a c · cnt c
b`, which vanishes by `BrokenPairs`.  This is a complete proof: only the
geometric input is assumed. -/
theorem floerDiff_comp_floerDiff {R : Type*} [CommRing R] {cnt : Orbit → Orbit → R}
    (h : BrokenPairs cz cnt) {i j k : ℤ} (hij : j + 1 = i) (hjk : k + 1 = j) :
    (floerDiff cnt j k).comp (floerDiff (cz := cz) cnt i j) = 0 := by
  ext x b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, floerDiff_apply]
  have key : ∀ c : OrbitSet cz j,
      (∑ a : OrbitSet cz i, x a * cnt a.1 c.1) * cnt c.1 b.1
        = ∑ a : OrbitSet cz i, x a * (cnt a.1 c.1 * cnt c.1 b.1) := by
    intro c
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.mul_sum, h.of_rel hij hjk a b, mul_zero]

/-- The differential of the `ℤ`-graded complex: `∂` in the degrees where the
complex shape allows one, and `0` elsewhere. -/
noncomputable def floerD {R : Type*} [CommRing R] (cz : Orbit → ℤ) (cnt : Orbit → Orbit → R)
    (i j : ℤ) :
    ModuleCat.of R (FloerChains cz R i) ⟶ ModuleCat.of R (FloerChains cz R j) :=
  if j + 1 = i then ModuleCat.ofHom (floerDiff cnt i j) else 0

theorem floerD_pos {R : Type*} [CommRing R] (cnt : Orbit → Orbit → R) {i j : ℤ}
    (h : j + 1 = i) : floerD cz cnt i j = ModuleCat.ofHom (floerDiff cnt i j) := if_pos h

theorem floerD_neg {R : Type*} [CommRing R] (cnt : Orbit → Orbit → R) {i j : ℤ}
    (h : ¬ j + 1 = i) : floerD cz cnt i j = 0 := if_neg h

/-- **The Floer complex `(C⋆(H), ∂)`** (§9.1, Corollary 9.2.2), as an object of
Mathlib's category of chain complexes, so that all the homological algebra
applies to it.

The grading is by the Conley–Zehnder index — an integer — and the differential
lowers it by one, which is `ComplexShape.down ℤ`. -/
noncomputable def floerComplex {R : Type*} [CommRing R] {cnt : Orbit → Orbit → R}
    (h : BrokenPairs cz cnt) : ChainComplex (ModuleCat R) ℤ where
  X k := ModuleCat.of R (FloerChains cz R k)
  d := floerD cz cnt
  shape i j hij := floerD_neg cnt hij
  d_comp_d' i j k hij hjk := by
    rw [floerD_pos cnt hij, floerD_pos cnt hjk]
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    exact floerDiff_comp_floerDiff h hij hjk

@[simp]
theorem floerComplex_X {R : Type*} [CommRing R] {cnt : Orbit → Orbit → R}
    (h : BrokenPairs cz cnt) (k : ℤ) :
    (floerComplex h).X k = ModuleCat.of R (FloerChains cz R k) := rfl

theorem floerComplex_d {R : Type*} [CommRing R] {cnt : Orbit → Orbit → R}
    (h : BrokenPairs cz cnt) (k : ℤ) :
    (floerComplex h).d (k + 1) k = ModuleCat.ofHom (floerDiff cnt (k + 1) k) :=
  floerD_pos cnt rfl

/-- **Floer homology `HF_k(H, J)`**: the homology of the Floer complex.
Chapter 10 identifies it with the Morse homology of `W`, and Chapter 11 proves
its independence of `(H, J)`. -/
noncomputable def floerHomology {R : Type*} [CommRing R] {cnt : Orbit → Orbit → R}
    (h : BrokenPairs cz cnt) (k : ℤ) : ModuleCat R :=
  (floerComplex h).homology k

/-- The cycles in degree `k + 1`: the kernel of `∂ : C_{k+1} → C_k`. -/
noncomputable def floerCycles {R : Type*} [CommRing R] (cz : Orbit → ℤ)
    (cnt : Orbit → Orbit → R) (k : ℤ) : Submodule R (FloerChains cz R (k + 1)) :=
  LinearMap.ker (floerDiff cnt (k + 1) k)

/-- The boundaries in degree `k`: the image of `∂ : C_{k+1} → C_k`. -/
noncomputable def floerBoundaries {R : Type*} [CommRing R] (cz : Orbit → ℤ)
    (cnt : Orbit → Orbit → R) (k : ℤ) : Submodule R (FloerChains cz R k) :=
  LinearMap.range (floerDiff cnt (k + 1) k)

/-- `Im ∂_{k+2} ⊆ Ker ∂_{k+1}`, so that the book's quotient
`HF_k = Ker ∂_k / Im ∂_{k+1}` is defined in every degree. -/
theorem floerBoundaries_le_cycles {R : Type*} [CommRing R] {cnt : Orbit → Orbit → R}
    (h : BrokenPairs cz cnt) (k : ℤ) :
    floerBoundaries cz cnt (k + 1) ≤ floerCycles cz cnt k :=
  LinearMap.range_le_ker_iff.mpr (floerDiff_comp_floerDiff h rfl rfl)

end FloerComplex

/-! ### From the geometry of `L̄(x,z)` to `∂ ∘ ∂ = 0`

The counts `n(x,y)` are, by definition, the number modulo `2` of points of the
`0`-dimensional compact manifold `L(x,y)`; the broken-trajectory hypothesis is
the statement that the boundary of the `1`-dimensional compact manifold
`L̄(x,z)` has an even number of points.  Both are recorded here, and the
implication between them — the whole of §9.1.b — is proved. -/

section Counting

variable {Orbit : Type*} [Fintype Orbit] (cz : Orbit → ℤ)
  (Sol : Orbit → Orbit → Type*) [∀ x y, AddAction ℝ (Sol x y)]

/-- **Corollary 9.1.8 / §9.1.b**, as a predicate: when the index drop is one,
`L(x,y)` is a compact `0`-manifold, hence a finite set.  This is what makes the
count `n(x,y)` meaningful. -/
def IsolatedTrajectories : Prop :=
  ∀ x y : Orbit, cz x = cz y + 1 → Finite (Traj (Sol x y))

/-- **The count `n(x,y)`** of §9.1: the number, modulo `2`, of trajectories from
`x` to `y`.

`Nat.card` returns `0` on an infinite type, so this is defined unconditionally;
it has the book's meaning exactly when `IsolatedTrajectories` holds and the
index drop is one. -/
noncomputable def floerCount (x y : Orbit) : ZMod 2 :=
  (Nat.card (Traj (Sol x y)) : ZMod 2)

variable {cz Sol}

/-- **The compactified space `L̄(x,z)` of §9.1.b**, as a set: the trajectories
from `x` to `z`, together with the once-broken ones through an orbit of
intermediate index.

Only the underlying set is definable.  Its topology is defined by the
convergence of Theorem 9.1.6, and Theorem 9.2.1 — that this is a compact
`1`-manifold with boundary — is not expressible. -/
def BrokenTraj (cz : Orbit → ℤ) (Sol : Orbit → Orbit → Type*) [∀ x y, AddAction ℝ (Sol x y)]
    (x z : Orbit) : Type _ :=
  Traj (Sol x z) ⊕ (Σ y : {y : Orbit // cz z < cz y ∧ cz y < cz x},
    Traj (Sol x y.1) × Traj (Sol y.1 z))

/-- **The boundary `∂L̄(x,z) = ⋃_y L(x,y) × L(y,z)`** of Theorem 9.2.1.

(The printed statement writes the union over `μ(x) < μ(y) < μ(z)`, which is
empty; the intended range is `μ(z) < μ(y) < μ(x)`.) -/
def brokenBoundary (cz : Orbit → ℤ) (Sol : Orbit → Orbit → Type*)
    [∀ x y, AddAction ℝ (Sol x y)] (x z : Orbit) : Type _ :=
  Σ y : {y : Orbit // cz z < cz y ∧ cz y < cz x}, Traj (Sol x y.1) × Traj (Sol y.1 z)

/-- **The geometric input of Corollary 9.2.2**, as a predicate.

When `μ(a) = μ(b) + 2`, the space `L̄(a,b)` is a compact `1`-manifold with
boundary `⋃_c L(a,c) × L(c,b)` (Theorem 9.2.1), and a compact `1`-manifold has
an even number of boundary points (Theorem 2.3.2); so the number of once-broken
trajectories from `a` to `b` is even.

Neither Theorem 9.2.1 nor the classification of compact `1`-manifolds is
expressible in Mathlib, so their conclusion is what is recorded. -/
def EvenBrokenBoundary (cz : Orbit → ℤ) (Sol : Orbit → Orbit → Type*)
    [∀ x y, AddAction ℝ (Sol x y)] : Prop :=
  ∀ (k : ℤ) (a : OrbitSet cz (k + 2)) (b : OrbitSet cz k),
    Even (∑ c : OrbitSet cz (k + 1),
      Nat.card (Traj (Sol a.1 c.1)) * Nat.card (Traj (Sol c.1 b.1)))

/-- **Corollary 9.2.2, reduced to its geometric input.**

If the boundary of `L̄(a,b)` has an even number of points whenever the index
drop is `2`, then the counts `n(x,y)` satisfy the broken-trajectory hypothesis,
and hence `∂ ∘ ∂ = 0` (`floerDiff_comp_floerDiff`).

This is the whole of §9.1.b, and it is proved. -/
theorem brokenPairs_floerCount (h : EvenBrokenBoundary cz Sol) :
    BrokenPairs cz (floerCount Sol) := by
  intro k a b
  obtain ⟨m, hm⟩ := h k a b
  have hsum : (∑ c : OrbitSet cz (k + 1), floerCount Sol a.1 c.1 * floerCount Sol c.1 b.1)
      = ((∑ c : OrbitSet cz (k + 1),
          Nat.card (Traj (Sol a.1 c.1)) * Nat.card (Traj (Sol c.1 b.1)) : ℕ) : ZMod 2) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun c _ => by
      rw [Nat.cast_mul]; rfl
  rw [hsum, hm]
  push_cast
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

end Counting

/-! ## §9.3  Pre-gluing: the cut-off functions

The pre-glued approximate solution `w_ρ` interpolates between `u(· + ρ)` and
`v(· − ρ)` using two fixed smooth cut-offs

`β⁻ = 1` for `s ≤ −1`, `β⁻ = 0` for `s ≥ −ε`,
`β⁺ = 0` for `s ≤ ε`,  `β⁺ = 1` for `s ≥ 1`,

both with values in `[0,1]`.  The interpolation itself uses the exponential map
of a Riemannian metric on `W` and is not expressible; the cut-offs are, and they
are constructed here from Mathlib's `Real.smoothTransition`. -/

section Cutoffs

/-- A smooth step: `0` for `s ≤ a`, `1` for `s ≥ b`, values in `[0,1]`. -/
noncomputable def smoothStep (a b : ℝ) (s : ℝ) : ℝ := Real.smoothTransition ((s - a) / (b - a))

theorem contDiff_smoothStep (a b : ℝ) {n : ℕ∞} : ContDiff ℝ n (smoothStep a b) := by
  have h : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => (s - a) / (b - a)) :=
    (contDiff_id.sub contDiff_const).div_const _
  exact Real.smoothTransition.contDiff.comp h

theorem smoothStep_eq_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) : smoothStep a b s = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hb : (0 : ℝ) < b - a := by linarith
  rw [div_le_iff₀ hb]
  linarith

theorem smoothStep_eq_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) : smoothStep a b s = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have hb : (0 : ℝ) < b - a := by linarith
  rw [le_div_iff₀ hb]
  linarith

theorem smoothStep_nonneg (a b s : ℝ) : 0 ≤ smoothStep a b s := Real.smoothTransition.nonneg _

theorem smoothStep_le_one (a b s : ℝ) : smoothStep a b s ≤ 1 := Real.smoothTransition.le_one _

/-- **The cut-off `β⁺` of §9.3**: smooth, `0` for `s ≤ ε` and `1` for `s ≥ 1`. -/
noncomputable def cutoffPos (ε : ℝ) : ℝ → ℝ := smoothStep ε 1

/-- **The cut-off `β⁻` of §9.3**: smooth, `1` for `s ≤ −1` and `0` for
`s ≥ −ε`.  It is `β⁺` read backwards, `β⁻(s) = β⁺(−s)`. -/
noncomputable def cutoffNeg (ε : ℝ) : ℝ → ℝ := fun s => cutoffPos ε (-s)

theorem contDiff_cutoffPos (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoffPos ε) :=
  contDiff_smoothStep _ _

theorem contDiff_cutoffNeg (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoffNeg ε) :=
  (contDiff_cutoffPos ε).comp contDiff_neg

theorem cutoffPos_eq_zero {ε s : ℝ} (hε : ε < 1) (hs : s ≤ ε) : cutoffPos ε s = 0 :=
  smoothStep_eq_zero hε hs

theorem cutoffPos_eq_one {ε s : ℝ} (hε : ε < 1) (hs : 1 ≤ s) : cutoffPos ε s = 1 :=
  smoothStep_eq_one hε hs

theorem cutoffPos_mem_Icc (ε s : ℝ) : cutoffPos ε s ∈ Icc (0 : ℝ) 1 :=
  ⟨smoothStep_nonneg _ _ _, smoothStep_le_one _ _ _⟩

theorem cutoffNeg_eq_one {ε s : ℝ} (hε : ε < 1) (hs : s ≤ -1) : cutoffNeg ε s = 1 := by
  have h : cutoffPos ε (-s) = 1 := cutoffPos_eq_one hε (by linarith)
  simp [cutoffNeg, h]

theorem cutoffNeg_eq_zero {ε s : ℝ} (hε : ε < 1) (hs : -ε ≤ s) : cutoffNeg ε s = 0 := by
  have h : cutoffPos ε (-s) = 0 := cutoffPos_eq_zero hε (by linarith)
  simp [cutoffNeg, h]

theorem cutoffNeg_mem_Icc (ε s : ℝ) : cutoffNeg ε s ∈ Icc (0 : ℝ) 1 :=
  cutoffPos_mem_Icc ε (-s)

end Cutoffs

/-! ## §9.4  The construction of `ψ`

Two pieces of §9.4 survive the absence of Sobolev spaces: the abstract
Newton–Picard lemma 9.4.4, which is a statement about Banach spaces and is
proved here, and the index bookkeeping of Proposition 9.4.3, which is a
statement about Fredholm operators and is proved from Chapter 8's hypotheses. -/

/-! ### Lemma 9.4.4: the Newton–Picard method -/

section NewtonPicard

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The Newton–Picard iteration map of Lemma 9.4.4,
`ϕ(x) = G(L(x) − F(x)) = −G(F(0) + N(x))`. -/
def npMap (F : X → Y) (L : X →L[ℝ] Y) (G : Y →L[ℝ] X) (x : X) : X := G (L x - F x)

theorem npMap_zero (F : X → Y) (L : X →L[ℝ] Y) (G : Y →L[ℝ] X) :
    npMap F L G 0 = -G (F 0) := by
  simp [npMap]

theorem norm_npMap_zero (F : X → Y) (L : X →L[ℝ] Y) (G : Y →L[ℝ] X) :
    ‖npMap F L G 0‖ = ‖G (F 0)‖ := by
  rw [npMap_zero, norm_neg]

/-- A fixed point of `ϕ` is a zero of `F`: `L(ϕ x) = L x − F x`, so `ϕ x = x`
forces `F x = 0`. -/
theorem eq_zero_of_isFixedPt {F : X → Y} {L : X →L[ℝ] Y} {G : Y →L[ℝ] X}
    (hLG : ∀ y, L (G y) = y) {x : X} (hx : npMap F L G x = x) : F x = 0 := by
  have h := congrArg L hx
  rw [npMap, hLG] at h
  exact sub_eq_self.mp h

/-- Conversely a zero of `F` lying in the image of `G` is a fixed point of
`ϕ`. -/
theorem isFixedPt_of_eq_zero {F : X → Y} {L : X →L[ℝ] Y} {G : Y →L[ℝ] X}
    (hLG : ∀ y, L (G y) = y) {x : X} (hx : F x = 0) (hmem : x ∈ Set.range G) :
    npMap F L G x = x := by
  obtain ⟨y, rfl⟩ := hmem
  rw [npMap, hx, sub_zero, hLG]

/-- The increments of `ϕ` are, up to sign, the increments of `G ∘ N`, where
`N(x) = F(x) − F(0) − L(x)` is the nonlinear part of `F`. -/
theorem npMap_sub (F : X → Y) (L : X →L[ℝ] Y) (G : Y →L[ℝ] X) (x z : X) :
    npMap F L G x - npMap F L G z
      = -(G (F x - F 0 - L x) - G (F z - F 0 - L z)) := by
  simp only [npMap, map_sub]
  abel

/-- **Lemma 9.4.4 (the Newton–Picard method).**

Let `X`, `Y` be Banach spaces, `F : X → Y` continuous, `L = (dF)_0`, and write
`F(x) = F(0) + L(x) + N(x)`.  Suppose `G : Y → X` is a continuous linear right
inverse of `L`, that `‖GN(x) − GN(z)‖ ≤ C(‖x‖+‖z‖)‖x−z‖` on the ball of radius
`r`, and that `‖G F(0)‖ ≤ ε/2` where `ε = min(r, 1/5C)`.  Then there is a unique
`α ∈ Im(G) ∩ B(0,ε)` with `F(α) = 0`, and `‖α‖ ≤ 2‖G F(0)‖`.

The proof is the book's: the map `ϕ(x) = G(L x − F x)` sends `B(0,ε)` into
itself and is `1/2`-Lipschitz there, so Banach's fixed point theorem applies,
and its fixed points are exactly the zeros of `F` in `Im G`.  Here `ε ≤ r` and
`ε ≤ 1/5C` are taken as hypotheses rather than a definition of `ε`, which is
what "`ε = min(r, 1/5C)`" amounts to. -/
theorem newtonPicard [CompleteSpace X] (F : X → Y) (L : X →L[ℝ] Y) (G : Y →L[ℝ] X)
    {r C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hεr : ε ≤ r) (hεC : ε ≤ 1 / (5 * C))
    (hLG : ∀ y, L (G y) = y)
    (hN : ∀ x ∈ Metric.closedBall (0 : X) r, ∀ z ∈ Metric.closedBall (0 : X) r,
      ‖G (F x - F 0 - L x) - G (F z - F 0 - L z)‖ ≤ C * (‖x‖ + ‖z‖) * ‖x - z‖)
    (h0 : ‖G (F 0)‖ ≤ ε / 2) :
    ∃ α : X, α ∈ Set.range G ∧ ‖α‖ ≤ ε ∧ F α = 0 ∧ ‖α‖ ≤ 2 * ‖G (F 0)‖ ∧
      ∀ β : X, β ∈ Set.range G → ‖β‖ ≤ ε → F β = 0 → β = α := by
  set B : Set X := Metric.closedBall (0 : X) ε with hB
  have hBsub : B ⊆ Metric.closedBall (0 : X) r := Metric.closedBall_subset_closedBall hεr
  have h0B : (0 : X) ∈ B := by simp [hB, hε.le]
  have hCε : C * ε ≤ 1 / 5 := by
    have h5C : (0 : ℝ) < 5 * C := by linarith
    have := (le_div_iff₀ h5C).mp hεC
    linarith
  -- `ϕ` is `1/2`-Lipschitz on `B`
  have hlip : ∀ x ∈ B, ∀ z ∈ B,
      ‖npMap F L G x - npMap F L G z‖ ≤ (1 / 2 : ℝ) * ‖x - z‖ := by
    intro x hx z hz
    have hx' : ‖x‖ ≤ ε := by simpa [hB] using hx
    have hz' : ‖z‖ ≤ ε := by simpa [hB] using hz
    have hnn : (0 : ℝ) ≤ ‖x - z‖ := norm_nonneg _
    have hbase := hN x (hBsub hx) z (hBsub hz)
    have hb : C * (‖x‖ + ‖z‖) ≤ 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hx' hC.le, mul_le_mul_of_nonneg_left hz' hC.le]
    calc ‖npMap F L G x - npMap F L G z‖
        = ‖G (F x - F 0 - L x) - G (F z - F 0 - L z)‖ := by
          rw [npMap_sub, norm_neg]
      _ ≤ C * (‖x‖ + ‖z‖) * ‖x - z‖ := hbase
      _ ≤ (1 / 2 : ℝ) * ‖x - z‖ := mul_le_mul_of_nonneg_right hb hnn
  -- `ϕ` maps `B` into `B`
  have hmaps : Set.MapsTo (npMap F L G) B B := by
    intro x hx
    have h1 := hlip x hx 0 h0B
    have h2 : ‖npMap F L G 0‖ = ‖G (F 0)‖ := norm_npMap_zero F L G
    have hx' : ‖x‖ ≤ ε := by simpa [hB] using hx
    have h3 : ‖npMap F L G x‖
        ≤ ‖npMap F L G x - npMap F L G 0‖ + ‖npMap F L G 0‖ := by
      calc ‖npMap F L G x‖
          = ‖(npMap F L G x - npMap F L G 0) + npMap F L G 0‖ := by
            rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖x - 0‖ = ‖x‖ := by rw [sub_zero]
    rw [h4] at h1
    have : ‖npMap F L G x‖ ≤ ε := by
      rw [h2] at h3
      linarith
    simpa [hB] using this
  have hBcomplete : IsComplete B := by
    rw [hB]; exact Metric.isClosed_closedBall.isComplete
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict (npMap F L G) B B) := by
    refine ⟨by norm_num, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have hk : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [Subtype.dist_eq, Subtype.dist_eq, hk]
    simpa only [Set.MapsTo.val_restrict_apply, dist_eq_norm] using hlip a.1 a.2 b.1 b.2
  obtain ⟨α, hαB, hfix, -, -⟩ :=
    hcontract.exists_fixedPoint' hBcomplete hmaps h0B (edist_ne_top _ _)
  have hfix' : npMap F L G α = α := hfix
  refine ⟨α, ⟨_, hfix'⟩, by simpa [hB] using hαB, eq_zero_of_isFixedPt hLG hfix', ?_, ?_⟩
  · -- `‖α‖ ≤ 2 ‖G F(0)‖`
    have h1 := hlip α hαB 0 h0B
    rw [hfix', sub_zero] at h1
    have h2 : ‖npMap F L G 0‖ = ‖G (F 0)‖ := norm_npMap_zero F L G
    have h3 : ‖α‖ ≤ ‖α - npMap F L G 0‖ + ‖npMap F L G 0‖ := by
      calc ‖α‖ = ‖(α - npMap F L G 0) + npMap F L G 0‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [h2] at h3
    linarith
  · -- uniqueness
    intro β hβr hβε hβ0
    have hβB : β ∈ B := by simpa [hB] using hβε
    have hβfix : npMap F L G β = β := isFixedPt_of_eq_zero hLG hβ0 hβr
    have hb : Function.IsFixedPt (hmaps.restrict (npMap F L G) B B) ⟨β, hβB⟩ :=
      Subtype.ext hβfix
    have ha : Function.IsFixedPt (hmaps.restrict (npMap F L G) B B) ⟨α, hαB⟩ :=
      Subtype.ext hfix'
    exact congrArg Subtype.val (hcontract.fixedPoint_unique' hb ha)

end NewtonPicard

/-! ### Lemma 9.4.6: a finite-dimensional subspace is complemented

The book's `W_ρ^⊥` is the `L²`-orthogonal of a two-dimensional subspace inside
`W^{1,p}`, and Lemma 9.4.6 says the two are complementary.  The `L²`-pairing on
`W^{1,p}(ℝ × S¹; ℝ^{2n})` does not exist in Mathlib, but the underlying general
fact — a finite-dimensional subspace of a normed space admits a *closed*
complement — does. -/

section Complemented

/-- **Lemma 9.4.6**, in the generality Mathlib supports: a finite-dimensional
subspace `E` of a normed space is closed-complemented, `X = E ⊕ E'` with `E'`
closed.  The book's specific complement, the `L²`-orthogonal of `E`, is not
expressible. -/
theorem closedComplemented_of_finiteDimensional {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
    E.ClosedComplemented :=
  Submodule.ClosedComplemented.of_finiteDimensional E

end Complemented

/-! ### Proposition 9.4.3: `L_ρ` is Fredholm of index 2

The book's proof observes that the linearisation of the Floer operator along
the pre-glued map `w_ρ` is `∂̄ + S_ρ(s,t)` for a `0`-th order term `S_ρ` whose
limits at `∓∞` are the symmetric paths attached to `x` and `z`, and then quotes
Theorems 8.7.1 and 8.8.1: the operator is Fredholm of index `μ(x) − μ(z)`, which
is `2`.

Chapter 8 records those two theorems as the predicates `IsFredholmData` and
`HasCZIndex` on a `FloerData`; here the arithmetic they feed is carried out. -/

section Index

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Proposition 9.4.3.**  If the linearised operator along the pre-gluing has
the index `μ(x) − μ(z)` given by Theorem 8.1.5, and `μ(x) = μ(z) + 2`, then its
index is `2`. -/
theorem fredholmIndex_preglue_eq_two {D : Chapter8.FloerData E F} {x z : D.Orbit}
    (Lρ : E →L[ℝ] F) (hL : Chapter16.fredholmIndex Lρ = D.cz x - D.cz z)
    (hxz : D.cz x = D.cz z + 2) :
    Chapter16.fredholmIndex Lρ = 2 := by
  rw [hL, hxz]
  ring

/-- The same statement for the linearisation along an actual solution, read off
Chapter 8's `HasCZIndex`. -/
theorem fredholmIndex_lin_eq_two {D : Chapter8.FloerData E F} (hind : D.HasCZIndex)
    {x z : D.Orbit} (u : D.Sol x z) (hxz : D.cz x = D.cz z + 2) :
    Chapter16.fredholmIndex (D.lin u) = 2 :=
  fredholmIndex_preglue_eq_two (D := D) (x := x) (z := z) (D.lin u) (hind x z u) hxz

/-- **The first consequence of Proposition 9.4.7.**  If moreover `L_ρ` is
surjective — which is what Proposition 9.4.7 buys, since it makes `L_ρ`
invertible on `W_ρ^⊥` — then its kernel has dimension exactly `2`.

This is the statement the book needs in order to intersect `exp_{w_ρ}(W_ρ^⊥)`
with the two-dimensional `M(x,z)`. -/
theorem finrank_ker_preglue_eq_two (Lρ : E →L[ℝ] F) (hsurj : Function.Surjective Lρ)
    (hind : Chapter16.fredholmIndex Lρ = 2) :
    Module.finrank ℝ (LinearMap.ker (Lρ : E →ₗ[ℝ] F)) = 2 := by
  have h := Chapter8.fredholmIndex_eq_finrank_ker_of_surjective hsurj
  rw [hind] at h
  omega

end Index

/-! ### Lemma 9.4.11

A bounded sequence on which a Fredholm operator tends to `0` has a subsequence
converging to an element of the kernel.  The book deduces this from the
existence of a quasi-inverse modulo a finite-rank (hence compact) operator,
which is Proposition 16.2.5; here that quasi-inverse is a hypothesis and the
rest of the argument is carried out. -/

section Subsequence

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Lemma 9.4.11.**  Let `D : E → F` be a Fredholm operator, with a
quasi-inverse `D'` such that `D' ∘ D = Id + K` for a compact operator `K`.  If
`(x_n)` is bounded and `D(x_n) → 0`, then a subsequence of `(x_n)` converges to
an element of `Ker D`.

Proved: `K(x_n)` lies in a compact set, so it subconverges; and `x_n = D'(D x_n)
− K(x_n)` then subconverges too, to a point killed by `D`. -/
theorem exists_subseq_tendsto_ker (D : E →L[ℝ] F) (D' : F →L[ℝ] E) (K : E →ₗ[ℝ] E)
    (hK : IsCompactOperator K) (hquasi : ∀ z, D' (D z) = z + K z)
    {x : ℕ → E} {r : ℝ} (hbdd : ∀ n, ‖x n‖ ≤ r)
    (h0 : Tendsto (fun n => D (x n)) atTop (𝓝 0)) :
    ∃ (a : E) (φ : ℕ → ℕ), StrictMono φ ∧ D a = 0 ∧ Tendsto (fun n => x (φ n)) atTop (𝓝 a) := by
  obtain ⟨S, hScpt, hSsub⟩ := hK.image_closedBall_subset_compact r
  have hmem : ∀ n, K (x n) ∈ S := by
    intro n
    exact hSsub ⟨x n, by simpa [Metric.mem_closedBall] using hbdd n, rfl⟩
  obtain ⟨b, -, φ, hφ, hb⟩ := hScpt.tendsto_subseq hmem
  have hbφ : Tendsto (fun n => K (x (φ n))) atTop (𝓝 b) := hb
  have h1 : Tendsto (fun n => D (x (φ n))) atTop (𝓝 0) := h0.comp hφ.tendsto_atTop
  have hDD : Tendsto (fun n => D' (D (x (φ n)))) atTop (𝓝 0) := by
    have h2 := (D'.continuous.tendsto (0 : F)).comp h1
    simpa [Function.comp_def] using h2
  have key : ∀ n, x (φ n) = D' (D (x (φ n))) - K (x (φ n)) := by
    intro n
    rw [hquasi]
    abel
  have hlim : Tendsto (fun n => x (φ n)) atTop (𝓝 (0 - b)) :=
    (hDD.sub hbφ).congr fun n => (key n).symm
  refine ⟨0 - b, φ, hφ, ?_, hlim⟩
  have hD1 : Tendsto (fun n => D (x (φ n))) atTop (𝓝 (D (0 - b))) :=
    (D.continuous.tendsto _).comp hlim
  exact tendsto_nhds_unique hD1 h1

end Subsequence

end Chapter9
end MorseFloer
