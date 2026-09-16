import MorseFloer.Part2.Ch5
import MorseFloer.Part2.Ch16

/-!
# Chapter 8: Linearization and transversality

Formalization of Chapter 8 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 199–290).

The chapter proves that the spaces of solutions of the Floer equation are, after
an arbitrarily small perturbation of the Hamiltonian, manifolds of the expected
dimension.  The strategy is:

* realise `M(x,y)` as the zero set of a section `σ` of a vector bundle over an
  infinite-dimensional Banach manifold `P^{1,p}(x,y)`;
* show that the differential of that section — the linearised Floer operator
  `(dF)_u` — is a Fredholm operator, and compute its index to be
  `μ(x) − μ(y)`, the difference of the Conley–Zehnder indices (Theorem 8.1.5);
* choose the perturbation so that `σ` is transverse to the zero section
  (Theorem 8.1.1), whence `M(x,y)` is a manifold of dimension `μ(x) − μ(y)`
  (Theorem 8.1.2).

## How the geometric input is handled here

Chapters 6 and 7 — the Floer equation, the space `M(x,y)` of its solutions, and
the Conley–Zehnder index — are being formalized separately, and Mathlib has
**no Sobolev spaces** at all, hence neither `W^{1,p}(ℝ × S¹; ℝ^{2n})` nor
`L^p(ℝ × S¹; ℝ^{2n})` nor the Banach manifold `P^{1,p}(x,y)` modelled on them.
Following the device of `MorseFloer.Part1.Ch3` (where the count of broken
trajectories is an abstract function `cnt` together with the hypothesis
`BrokenPairs`), the geometric input of this chapter is taken as *abstract data*:

* two Banach spaces `E` and `F` stand for `W^{1,p}(ℝ × S¹; ℝ^{2n})` and
  `L^p(ℝ × S¹; ℝ^{2n})` — the chapter itself always works in a fixed unitary
  trivialisation along `u`, in which every `W^{1,p}(u⋆TW)` *is* the fixed model
  space (§8.2.c, §8.4);
* a `FloerData` bundles a type `Orbit` of contractible `1`-periodic orbits, the
  Conley–Zehnder index `cz : Orbit → ℤ` of Chapter 7, a family of types
  `Sol x y` standing for `M(x, y, J, H)`, and the linearised operator
  `lin u : E →L[ℝ] F` standing for `(dF)_u`;
* the content of the book's theorems then appears as *predicates* on such data
  (`IsFredholmData`, `HasCZIndex`, `IsRegular`, `IsGenericallyRegular`), which
  a later pass must connect to Chapter 6's Floer operator and Chapter 7's index.

Stating, say, Theorem 8.1.5 as a Lean `theorem` about an arbitrary `FloerData`
would be stating something *false*, so it is recorded as a predicate and not as
a `sorry`ed theorem; that distinction is the point of this project.

## What is proved here

The chapter's real payload that survives the missing analysis is the **index
bookkeeping**, and it is proved in full from the Fredholm hypotheses:

* `fredholmIndex_eq_finrank_ker_of_surjective` — for a surjective operator the
  index *is* the dimension of the kernel.  Combined with Theorem 8.1.5 this is
  exactly why a regular pair `(H,J)` makes `M(x,y)` a manifold of dimension
  `μ(x) − μ(y)`; see `finrank_ker_eq_cz_sub_cz`, the linear shadow of
  Theorem 8.1.2.
* `fredholmIndex_eq_neg_finrank_coker_of_injective`,
  `fredholmIndex_eq_zero_of_bijective`;
* `fredholmIndex_prodMap` — the index of a direct sum is the sum of the indices
  (proved, via two auxiliary isomorphisms `prodSubmoduleEquiv` and
  `quotientProdEquiv` that Mathlib does not have);
* `fredholmIndex_comp_of_bijective_left/right` — additivity under composition,
  specialised to the case that makes a change of trivialisation harmless,
  derived from Chapter 16's assumed `fredholmIndex_comp`;
* `isFredholm_and_fredholmIndex_eq_of_sub_compact` — invariance of the
  Fredholm property and of the index under a compact perturbation, derived
  from Chapter 16's assumed `fredholmIndex_add_compact`.  This is the engine of
  Lemma 8.8.4, where the `0`-th order term `S(s,t)` of the linearised operator
  is deformed to its limits `S^±(t)`.
* `ker_ne_bot_of_ne_zero`, `finrank_ker_pos_of_ne_zero` — the linear content of
  Remark 8.4.8: since `∂u/∂s` is a nonzero solution of the linearised equation
  along a nonconstant trajectory, the kernel has dimension at least `1`.
* `range_gammaOp` and `gammaOp_surjective_iff` — the operator `Γ` of
  Proposition 8.1.4 has range `Im (dF)_u + Im grad`, so surjectivity of `Γ` is
  exactly the statement that the two ranges together span; and
  `gammaOp_surjective_of_surjective`, the trivial implication from regularity.
* `dense_regularSet` — a Baire-category consequence of Theorem 8.1.1: if the
  regular perturbations form a residual set (a countable intersection of dense
  open sets, as the theorem asserts), then they are dense.  This is the form in
  which Theorem 8.1.1 is *used*: arbitrarily close to `H₀` there is a good `H`.
* `eLpNorm_mul_le_mul_ofReal` — the second inequality of Lemma 8.2.4,
  `‖fg‖_{L^p} ≤ ‖f‖_{L^p} · sup |g|`, proved for Mathlib's `eLpNorm` (this half
  of the lemma is about `L^p`, which Mathlib does have).
* `separableSpace_continuousMap` — the `C⁰` half of Lemma 8.3.2: `C(K, ℝ)` is
  separable, which is Mathlib's `ContinuousMap.instSeparableSpace` (the book
  gets it from Stone–Weierstrass).

## Gaps: what today's Mathlib cannot state, and what is stated but assumed

Mathlib has no Sobolev spaces, so the whole of §8.2 apart from the `L^p` half of
Lemma 8.2.4 is unstatable:

* the spaces `L^p(ℝ × S¹; ℝ^N)` and `W^{1,p}(ℝ × S¹; ℝ^N)` of §8.2.a with their
  norms, Remark 8.2.1 (the distributional description), and the Sobolev
  embedding `W^{1,p} ⊂ C⁰` for `p > 2` that forces `p > 2` throughout;
* `W^{1,p}(w⋆TW)`, the space of `W^{1,p}` sections along `w`, and the proof that
  the two descriptions of it (by an embedding `W ⊂ ℝᵐ`, and by a trivialising
  frame) agree;
* **Definition 8.2.2**, the space `P^{1,p}(x,y)`, and §8.2.d, its Banach
  manifold structure with the atlas `Φ_w = exp_w`;
* **Proposition 8.2.3**, `M(x,y) ⊂ C^∞_↘(x,y) ⊂ P^{1,p}(x,y)`.  Its first term
  is abstract data here and its last term does not exist; what *is* recorded is
  `IsAsymptotic`, a faithful local-model definition of the book's
  `C^∞_↘(x,y)` (smooth, `1`-periodic in `t`, with limits `x` and `y` at `∓∞`
  and exponentially decaying `∂u/∂s`).
* the **first** inequality of Lemma 8.2.4, `‖fg‖_{W^{1,p}} ≤ ‖f‖_{W^{1,p}}
  ‖g‖_{C¹}`, for the same reason.

For §8.3 the situation is better: the `ε`-norm is a sum of `Cᵏ` sup-norms, and
`iteratedFDeriv` makes those definable.  Following the project's local-model
convention (and the book's own reduction to a finite atlas `Ψᵢ : Bᵢ → B(0,1)`),
`cSupNorm`, `cNorm`, `epsNorm`, `EpsFinite`, `c1Dist` and `CinftyEpsOf` are
defined for functions on a compact subset of a normed space.  With them,
**Lemma 8.3.2** is *proved* for a finite-dimensional `V`, by separability of
`C(K, ℝ) × C(K, V*)` rather than the book's mollification, and **Proposition
8.3.1** is *proved* from it by the book's diagonal choice of `ε`.
**Proposition 8.3.4** is *proved* too, by the same separability argument
applied to functions supported in a countable family of balls, with no cut-off.
That `C^∞_ε` is a Banach space, and the closing remark of §8.3 that for `‖h‖_ε`
small `H₀ + h` has exactly the periodic orbits of `H₀`, are not stated: the
first needs the completeness argument for the `ε`-norm, the second is a
statement about Hamiltonian dynamics on a symplectic manifold, which Chapter 5
records as unavailable.

Sections 8.4 to 8.9 are not formalized here.  They are the analytic heart of the
chapter — the computation of `(dF)_u` (§8.4), the transversality argument with
Hahn–Banach, Riesz and Sard–Smale (§8.5), the unique continuation principle
(§8.6), the Fredholm property (§8.7), the index computation by deformation to a
constant-coefficient operator (§8.8) and the exponential decay estimates (§8.9)
— and every one of them is a statement about Sobolev spaces of sections, weak
derivatives and elliptic estimates.  Their *conclusions* are what the predicates
`IsFredholmData`, `HasCZIndex` and `IsGenericallyRegular` record, and what the
index bookkeeping above consumes.

## Conventions

Everything is over `ℝ` except the index bookkeeping of the first section, which
costs nothing to state over an arbitrary complete nontrivially normed field and
is the form in which Chapter 16 states its assumptions.
-/

open ContinuousLinearMap Filter Topology MeasureTheory
open scoped ContDiff

namespace MorseFloer
namespace Chapter8

/-! ## Index bookkeeping

The results of §16.2 that Chapter 8 actually uses, in the two forms it uses
them: the index of a surjective operator (which is what transversality buys),
and the invariance of the index under the two deformations of §8.8 (composition
with an isomorphism, and a compact perturbation of the `0`-th order term).

Everything here is proved, except where it explicitly consumes one of the three
stability theorems that `MorseFloer.Chapter16` assumes. -/

section IndexBookkeeping

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G K : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K]

/-- A surjective operator has zero cokernel, hence cokernel of dimension `0`. -/
theorem finrank_coker_eq_zero_of_surjective {u : E →L[𝕜] F} (hu : Function.Surjective u) :
    Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) = 0 := by
  have hr : LinearMap.range (u : E →ₗ[𝕜] F) = ⊤ := by
    rw [LinearMap.range_eq_top]; exact hu
  have : Subsingleton (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) :=
    Submodule.Quotient.subsingleton_iff.mpr hr
  exact Module.finrank_zero_of_subsingleton

/-- **The index of a surjective operator is the dimension of its kernel.**

This one line is what makes the whole transversality programme of the chapter
work: for a *regular* pair `(H,J)` the linearised Floer operator `(dF)_u` is
surjective, so by Theorem 8.1.5 its kernel — the tangent space to the space of
solutions at `u` — has dimension exactly `Ind (dF)_u = μ(x) − μ(y)`.  That is
Theorem 8.1.2 with the implicit function theorem stripped away. -/
theorem fredholmIndex_eq_finrank_ker_of_surjective {u : E →L[𝕜] F}
    (hu : Function.Surjective u) :
    Chapter16.fredholmIndex u = (Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) : ℤ) := by
  have h := finrank_coker_eq_zero_of_surjective hu
  simp [Chapter16.fredholmIndex, h]

/-- Dually, an injective operator has index `− dim coker`. -/
theorem fredholmIndex_eq_neg_finrank_coker_of_injective {u : E →L[𝕜] F}
    (hu : Function.Injective u) :
    Chapter16.fredholmIndex u
      = -(Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) : ℤ) := by
  have hk : LinearMap.ker (u : E →ₗ[𝕜] F) = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact hu
  have h0 : Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) = 0 := by
    rw [hk, finrank_bot]
  simp [Chapter16.fredholmIndex, h0]

/-- An isomorphism has index `0`.

Proved in Chapter 16, which this chapter imports; kept here as an alias so that
the name this chapter uses stays put. -/
theorem fredholmIndex_eq_zero_of_bijective {u : E →L[𝕜] F} (hu : Function.Bijective u) :
    Chapter16.fredholmIndex u = 0 :=
  Chapter16.fredholmIndex_eq_zero_of_bijective hu

/-- **The linear content of Remark 8.4.8.**  A nonzero solution of the
linearised equation makes the kernel nonzero.  Along a nonconstant Floer
trajectory `∂u/∂s` is such a solution, because `F(u · s) = 0` for all `s`. -/
theorem ker_ne_bot_of_ne_zero {u : E →L[𝕜] F} {Y : E} (hY : Y ≠ 0) (hYk : u Y = 0) :
    LinearMap.ker (u : E →ₗ[𝕜] F) ≠ ⊥ := by
  intro h
  apply hY
  have hmem : Y ∈ LinearMap.ker (u : E →ₗ[𝕜] F) := LinearMap.mem_ker.mpr hYk
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

/-- Remark 8.4.8 again, in the form the dimension count uses: the kernel of the
linearised operator along a nonconstant trajectory has dimension at least `1`. -/
theorem finrank_ker_pos_of_ne_zero {u : E →L[𝕜] F}
    (hu : ContinuousLinearMap.IsFredholm u) {Y : E} (hY : Y ≠ 0) (hYk : u Y = 0) :
    0 < Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) := by
  have := hu.finite_ker
  have hnt : Nontrivial (LinearMap.ker (u : E →ₗ[𝕜] F)) :=
    Submodule.nontrivial_iff_ne_bot.mpr (ker_ne_bot_of_ne_zero hY hYk)
  rw [Module.finrank_pos_iff_of_free]
  exact hnt

/-! ### The index of a direct sum

Mathlib has neither `↥(p × q) ≃ₗ ↥p × ↥q` nor `(M × N) ⧸ (p × q) ≃ₗ
(M ⧸ p) × (N ⧸ q)`, so both are built here; with them the additivity of the
index over a direct sum is a computation with `Module.finrank_prod`. -/

/-- The submodule `p × q` of `M × N`, as a module, is the product of `p` and
`q`. -/
def prodSubmoduleEquiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    (p.prod q) ≃ₗ[R] p × q where
  toFun z := (⟨z.1.1, (Submodule.mem_prod.mp z.2).1⟩, ⟨z.1.2, (Submodule.mem_prod.mp z.2).2⟩)
  invFun w := ⟨(w.1.1, w.2.1), Submodule.mem_prod.mpr ⟨w.1.2, w.2.2⟩⟩
  map_add' := by rintro ⟨⟨a, b⟩, h₁⟩ ⟨⟨c, d⟩, h₂⟩; rfl
  map_smul' := by rintro r ⟨⟨a, b⟩, h₁⟩; rfl
  left_inv := by rintro ⟨⟨a, b⟩, h₁⟩; rfl
  right_inv := by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl

/-- The quotient of `M × N` by `p × q` is the product of the two quotients: the
cokernel of a direct sum is the direct sum of the cokernels. -/
noncomputable def quotientProdEquiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) := by
  have hsurj : Function.Surjective (p.mkQ.prodMap q.mkQ) := by
    rintro ⟨a, b⟩
    obtain ⟨a', rfl⟩ := Submodule.mkQ_surjective p a
    obtain ⟨b', rfl⟩ := Submodule.mkQ_surjective q b
    exact ⟨(a', b'), rfl⟩
  refine (Submodule.quotEquivOfEq _ (LinearMap.ker (p.mkQ.prodMap q.mkQ)) ?_).trans
    (LinearMap.quotKerEquivOfSurjective _ hsurj)
  rw [LinearMap.ker_prodMap, Submodule.ker_mkQ, Submodule.ker_mkQ]

/-- **The index of a direct sum is the sum of the indices.**

The book uses this repeatedly in §8.8, where the constant-coefficient model
operator splits into `2n` one-dimensional blocks whose indices are added up. -/
theorem fredholmIndex_prodMap {u : E →L[𝕜] F} {v : G →L[𝕜] K}
    (hu : ContinuousLinearMap.IsFredholm u) (hv : ContinuousLinearMap.IsFredholm v) :
    Chapter16.fredholmIndex (u.prodMap v)
      = Chapter16.fredholmIndex u + Chapter16.fredholmIndex v := by
  have := hu.finite_ker
  have := hv.finite_ker
  have := hu.finite_coker
  have := hv.finite_coker
  have hkeq : LinearMap.ker ((u.prodMap v : E × G →L[𝕜] F × K) : E × G →ₗ[𝕜] F × K)
      = (LinearMap.ker (u : E →ₗ[𝕜] F)).prod (LinearMap.ker (v : G →ₗ[𝕜] K)) := by
    rw [ContinuousLinearMap.coe_prodMap, LinearMap.ker_prodMap]
  have hreq : LinearMap.range ((u.prodMap v : E × G →L[𝕜] F × K) : E × G →ₗ[𝕜] F × K)
      = (LinearMap.range (u : E →ₗ[𝕜] F)).prod (LinearMap.range (v : G →ₗ[𝕜] K)) := by
    rw [ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap]
  have hk : Module.finrank 𝕜
        (LinearMap.ker ((u.prodMap v : E × G →L[𝕜] F × K) : E × G →ₗ[𝕜] F × K))
      = Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F))
        + Module.finrank 𝕜 (LinearMap.ker (v : G →ₗ[𝕜] K)) := by
    rw [hkeq, (prodSubmoduleEquiv _ _).finrank_eq, Module.finrank_prod]
  have hc : Module.finrank 𝕜
        ((F × K) ⧸ LinearMap.range ((u.prodMap v : E × G →L[𝕜] F × K) : E × G →ₗ[𝕜] F × K))
      = Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F))
        + Module.finrank 𝕜 (K ⧸ LinearMap.range (v : G →ₗ[𝕜] K)) := by
    rw [hreq, (quotientProdEquiv _ _).finrank_eq, Module.finrank_prod]
  simp only [Chapter16.fredholmIndex, hk, hc]
  push_cast
  ring

/-! ### Invariance of the index

The two deformations of §8.8: composing with an isomorphism (a change of
unitary trivialisation along `u`, which must not change the index), and adding a
compact operator (the deformation of the `0`-th order term `S(s,t)` to its
limits `S^±(t)`, Lemma 8.8.4).  Both consume a stability theorem that Chapter 16
assumes. -/

/-- Composing on the left with an isomorphism does not change the index.  Uses
Chapter 16's assumed additivity `fredholmIndex_comp`. -/
theorem fredholmIndex_comp_of_bijective_left [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace G] {u : E →L[𝕜] F} {v : F →L[𝕜] G}
    (hu : ContinuousLinearMap.IsFredholm u) (hv : ContinuousLinearMap.IsFredholm v)
    (hvb : Function.Bijective v) :
    Chapter16.fredholmIndex (v.comp u) = Chapter16.fredholmIndex u := by
  rw [(Chapter16.fredholmIndex_comp hu hv).2, fredholmIndex_eq_zero_of_bijective hvb, zero_add]

/-- Composing on the right with an isomorphism does not change the index. -/
theorem fredholmIndex_comp_of_bijective_right [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace G] {u : E →L[𝕜] F} {v : F →L[𝕜] G}
    (hu : ContinuousLinearMap.IsFredholm u) (hv : ContinuousLinearMap.IsFredholm v)
    (hub : Function.Bijective u) :
    Chapter16.fredholmIndex (v.comp u) = Chapter16.fredholmIndex v := by
  rw [(Chapter16.fredholmIndex_comp hu hv).2, fredholmIndex_eq_zero_of_bijective hub, add_zero]

/-- **Invariance under a compact perturbation** (Proposition 16.2.7), in the form
Lemma 8.8.4 uses: two operators differing by a compact operator are
simultaneously Fredholm with the same index.  Uses Chapter 16's assumed
`fredholmIndex_add_compact`. -/
theorem isFredholm_and_fredholmIndex_eq_of_sub_compact [CompleteSpace 𝕜] [CompleteSpace E]
    [CompleteSpace F]
    {u v : E →L[𝕜] F} (hu : ContinuousLinearMap.IsFredholm u)
    (hk : IsCompactOperator (v - u)) :
    ContinuousLinearMap.IsFredholm v
      ∧ Chapter16.fredholmIndex v = Chapter16.fredholmIndex u := by
  have h := Chapter16.fredholmIndex_add_compact hu hk
  have heq : u + (v - u) = v := by abel
  rwa [heq] at h

end IndexBookkeeping

/-! ## §8.1 The statements

The data of the chapter, taken as hypotheses.  `E` stands for
`W^{1,p}(ℝ × S¹; ℝ^{2n})` and `F` for `L^p(ℝ × S¹; ℝ^{2n})`; the book works
throughout in a fixed unitary trivialisation along `u`, in which the space of
`W^{1,p}` sections of `u⋆TW` *is* the model space `E`. -/

section Statements

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The abstract Floer data of Chapter 8.**

* `Orbit` is the set of contractible `1`-periodic orbits of the Hamiltonian
  (Chapter 6);
* `cz` is the Conley–Zehnder index `μ` of Chapter 7;
* `Sol x y` stands for `M(x, y, J, H)`, the space of solutions of the Floer
  equation running from `x` to `y`;
* `lin u` stands for the linearised operator `(dF)_u`, read in a unitary
  trivialisation along `u` as an operator `E →L[ℝ] F` (Propositions 8.4.4,
  8.4.6: it is `∂̄ + S(s,t)` for a `0`-th order term `S` with symmetric limits).

A later pass must connect this to Chapter 6's Floer operator and Chapter 7's
Conley–Zehnder index. -/
structure FloerData (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The contractible `1`-periodic orbits. -/
  Orbit : Type
  /-- The Conley–Zehnder index `μ` of Chapter 7. -/
  cz : Orbit → ℤ
  /-- `Sol x y` stands for the space `M(x,y)` of Floer trajectories from `x` to `y`. -/
  Sol : Orbit → Orbit → Type
  /-- The linearised Floer operator `(dF)_u` in a unitary trivialisation along `u`. -/
  lin : ∀ {x y : Orbit}, Sol x y → (E →L[ℝ] F)

namespace FloerData

variable (D : FloerData E F)

/-- **Definition (§8.1): a regular pair.**  The pair `(H, J)` is regular when the
linearised Floer operator is surjective at every solution.  This is the
transversality of the section `σ` of §8.5.a with the zero section. -/
def IsRegular : Prop :=
  ∀ (x y : D.Orbit) (u : D.Sol x y), Function.Surjective (D.lin u)

/-- The Fredholm half of **Theorem 8.1.5**: for a nondegenerate Hamiltonian and
a calibrated almost complex structure, `(dF)_u` is a Fredholm operator.  Proved
in the book in §8.7; here a hypothesis on the abstract data. -/
def IsFredholmData : Prop :=
  ∀ (x y : D.Orbit) (u : D.Sol x y), ContinuousLinearMap.IsFredholm (D.lin u)

/-- The index half of **Theorem 8.1.5**: the index of `(dF)_u` is
`μ(x) − μ(y)`, the difference of the Conley–Zehnder indices.  Proved in the book
in §8.8 by deforming to a constant-coefficient operator; here a hypothesis on
the abstract data. -/
def HasCZIndex : Prop :=
  ∀ (x y : D.Orbit) (u : D.Sol x y),
    Chapter16.fredholmIndex (D.lin u) = D.cz x - D.cz y

/-- **Theorem 8.1.5** in full: `(dF)_u` is a Fredholm operator of index
`μ(x) − μ(y)`.

This is a *predicate* on the abstract data, not a theorem: asserting it of an
arbitrary `FloerData` would be false, and the objects its proof speaks about
(Sobolev spaces of sections, the Cauchy–Riemann operator, symplectic paths) are
not available.  A later pass must prove that the data coming from Chapter 6
satisfies it. -/
def IsFredholmOfCZIndex : Prop := D.IsFredholmData ∧ D.HasCZIndex

end FloerData

/-- **The dimension count of Theorem 8.1.2.**

For a regular pair the kernel of `(dF)_u` — which the implicit function theorem
turns into the tangent space of `M(x,y)` at `u` — has dimension exactly
`μ(x) − μ(y)`.  This is everything in Theorem 8.1.2 that does not need the
Banach manifold `P^{1,p}(x,y)`, and it is proved outright from the two
hypotheses of Theorem 8.1.5 and regularity. -/
theorem finrank_ker_eq_cz_sub_cz {D : FloerData E F}
    (_hfred : D.IsFredholmData) (hind : D.HasCZIndex) (hreg : D.IsRegular)
    {x y : D.Orbit} (u : D.Sol x y) :
    (Module.finrank ℝ (LinearMap.ker (D.lin u : E →ₗ[ℝ] F)) : ℤ) = D.cz x - D.cz y := by
  rw [← fredholmIndex_eq_finrank_ker_of_surjective (hreg x y u)]
  exact hind x y u

/-! ### Theorem 8.1.1: genericity of regularity

The book perturbs `H₀` inside the Banach space `C^∞_ε(H₀)` of §8.3 and produces
a countable intersection `H_reg` of dense open subsets of a neighbourhood of `0`
for which the pair is regular.  With an abstract space `Pert` of perturbations
and an abstract family of Floer data, "a countable intersection of dense open
sets" is Mathlib's `residual` filter, so the statement is expressible; what it
is *used* for — that good perturbations are dense — is then Baire's theorem, and
is proved. -/

section Genericity

variable {Pert : Type*} [TopologicalSpace Pert]

/-- The book's `H_reg`: the perturbations for which the pair `(H₀ + h, J)` is
regular. -/
def regularSet (D : Pert → FloerData E F) : Set Pert := {h | (D h).IsRegular}

/-- **Theorem 8.1.1** as a predicate on an abstract family of Floer data: the
regular perturbations contain a countable intersection of dense open sets.

Assumed, not proved: the book's proof is the Sard–Smale theorem applied to the
projection `Z(x,y,J) → C^∞_ε(H₀)`, and it needs the Banach manifold
`Z(x,y,J)` of Proposition 8.1.3 together with the transversality Proposition
8.1.4 — none of which is available. -/
def IsGenericallyRegular (D : Pert → FloerData E F) : Prop :=
  regularSet D ∈ residual Pert

/-- Unfolding of `IsGenericallyRegular`: it says exactly that `H_reg` contains a
countable intersection of dense open sets, which is the book's phrasing. -/
theorem isGenericallyRegular_iff (D : Pert → FloerData E F) :
    IsGenericallyRegular D ↔
      ∃ S : Set (Set Pert), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧
        ⋂₀ S ⊆ regularSet D :=
  mem_residual_iff

/-- **The way Theorem 8.1.1 is used**: arbitrarily close to `H₀` there is a
perturbation making the pair regular.

This is Baire's theorem, and it is proved.  The space of perturbations
`C^∞_ε(H₀)` is a Banach space, hence a Baire space, so the hypothesis
`[BaireSpace Pert]` is exactly what the book's setting supplies. -/
theorem dense_regularSet [BaireSpace Pert] (D : Pert → FloerData E F)
    (h : IsGenericallyRegular D) : Dense (regularSet D) :=
  dense_of_mem_residual h

end Genericity

/-! ### Propositions 8.1.3 and 8.1.4: the transversality operator `Γ`

Proposition 8.1.4 asserts the surjectivity of

`Γ(Y, h) = (dF_H)_u(Y) + grad_u h : W^{1,p} × C^∞_ε(H₀) → L^p`,

and Proposition 8.1.3 — that `Z(x,y,J)` is a Banach manifold — follows from it
by the implicit function theorem.  `Z(x,y,J)` and its manifold structure are not
statable (there is no `P^{1,p}(x,y)` for it to live over), but `Γ` itself is:
it is the operator `(Y,h) ↦ L Y + g h` built from the linearised operator `L`
and the continuous linear map `g : h ↦ grad_u h`.  What is proved below is the
elementary structure of `Γ`: its range is the sum of the two ranges, so
surjectivity of `Γ` says precisely that the perturbations fill up the cokernel
of `L` — which is why §8.5.b argues by exhibiting a `Z` annihilating both. -/

section Gamma

variable {Pert : Type*} [NormedAddCommGroup Pert] [NormedSpace ℝ Pert]

/-- **The operator `Γ` of Proposition 8.1.4**: `Γ(Y, h) = L Y + g h`, where `L`
is the linearised Floer operator `(dF_H)_u` and `g` is `h ↦ grad_u h`. -/
def gammaOp (L : E →L[ℝ] F) (g : Pert →L[ℝ] F) : E × Pert →L[ℝ] F :=
  L.comp (ContinuousLinearMap.fst ℝ E Pert) + g.comp (ContinuousLinearMap.snd ℝ E Pert)

@[simp]
theorem gammaOp_apply (L : E →L[ℝ] F) (g : Pert →L[ℝ] F) (z : E × Pert) :
    gammaOp L g z = L z.1 + g z.2 := rfl

/-- The range of `Γ` is `Im (dF)_u + Im grad`. -/
theorem range_gammaOp (L : E →L[ℝ] F) (g : Pert →L[ℝ] F) :
    LinearMap.range ((gammaOp L g : E × Pert →L[ℝ] F) : E × Pert →ₗ[ℝ] F)
      = LinearMap.range (L : E →ₗ[ℝ] F) ⊔ LinearMap.range (g : Pert →ₗ[ℝ] F) := by
  apply le_antisymm
  · rintro _ ⟨⟨Y, h⟩, rfl⟩
    show L Y + g h ∈ _
    exact Submodule.add_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self _ Y))
      (Submodule.mem_sup_right (LinearMap.mem_range_self _ h))
  · refine sup_le ?_ ?_
    · rintro _ ⟨Y, rfl⟩
      exact ⟨(Y, 0), by simp⟩
    · rintro _ ⟨h, rfl⟩
      exact ⟨(0, h), by simp⟩

/-- `Γ` is surjective exactly when the image of the linearised operator and the
image of the perturbations together span `L^p`.  This is the reformulation
§8.5.b starts from: if `Γ` is not onto, Hahn–Banach and Riesz produce a nonzero
`Z ∈ L^q` annihilating both ranges. -/
theorem gammaOp_surjective_iff (L : E →L[ℝ] F) (g : Pert →L[ℝ] F) :
    Function.Surjective (gammaOp L g) ↔
      LinearMap.range (L : E →ₗ[ℝ] F) ⊔ LinearMap.range (g : Pert →ₗ[ℝ] F) = ⊤ := by
  rw [← range_gammaOp, LinearMap.range_eq_top]
  exact Iff.rfl

/-- If the pair is already regular at `u`, then `Γ` is surjective: the
perturbations are not needed.  (The content of Proposition 8.1.4 is of course
the opposite situation.) -/
theorem gammaOp_surjective_of_surjective (L : E →L[ℝ] F) (g : Pert →L[ℝ] F)
    (hL : Function.Surjective L) : Function.Surjective (gammaOp L g) := by
  intro z
  obtain ⟨Y, rfl⟩ := hL z
  exact ⟨(Y, 0), by simp⟩

end Gamma

end Statements

/-! ## §8.2 The Banach manifold `P^{1,p}(x,y)`

Mathlib has no Sobolev spaces, so `L^p(ℝ × S¹; ℝ^N)`, `W^{1,p}(ℝ × S¹; ℝ^N)`,
`W^{1,p}(w⋆TW)`, Definition 8.2.2 (the space `P^{1,p}(x,y)`) and its Banach
manifold structure of §8.2.d have no Lean counterpart.  Two things survive:

* the definition of the book's `C^∞_↘(x,y)`, which is about honest smooth maps
  and an exponential decay estimate;
* the `L^p` half of Lemma 8.2.4, which is Hölder's inequality with exponent
  `∞`, and which Mathlib does have. -/

section Sobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The space `C^∞_↘(x, y)` of §8.2.c**, in the local model: a smooth map
`u : ℝ × S¹ → W` (here `S¹` is `ℝ` with `1`-periodicity, and `W` is replaced by
a normed space) converging to the loops `x` and `y` at `∓∞`, whose `s`-derivative
decays exponentially, `‖∂u/∂s‖ ≤ K e^{−δ|s|}`.

Together with the exponential-decay theorem 8.9.1 this is the space in which
Proposition 8.2.3 places the Floer trajectories; the second inclusion
`C^∞_↘(x,y) ⊂ P^{1,p}(x,y)` is not statable. -/
structure IsAsymptotic (x y : ℝ → V) (u : ℝ → ℝ → V) : Prop where
  /-- `u` is `1`-periodic in the second variable: it is defined on `ℝ × S¹`. -/
  periodic : ∀ s t, u s (t + 1) = u s t
  /-- `u` is smooth. -/
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => u p.1 p.2)
  /-- `u(s, ·) → x` as `s → −∞`. -/
  limit_neg : ∀ t, Tendsto (fun s => u s t) atBot (𝓝 (x t))
  /-- `u(s, ·) → y` as `s → +∞`. -/
  limit_pos : ∀ t, Tendsto (fun s => u s t) atTop (𝓝 (y t))
  /-- `‖∂u/∂s‖ ≤ K e^{−δ|s|}` for some positive `K` and `δ`. -/
  decay : ∃ Kc δ : ℝ, 0 < Kc ∧ 0 < δ ∧
    ∀ s t, ‖deriv (fun σ => u σ t) s‖ ≤ Kc * Real.exp (-δ * |s|)

/-- **Lemma 8.2.4, second inequality**: `‖f g‖_{L^p} ≤ ‖f‖_{L^p} · sup |g|`.

This is the half of the lemma that lives in `L^p`, which Mathlib has; it is
Hölder's inequality with exponents `(p, ∞)`.  The first inequality of the lemma,
`‖fg‖_{W^{1,p}} ≤ ‖f‖_{W^{1,p}} ‖g‖_{C¹}`, needs `W^{1,p}` and is not
statable. -/
theorem eLpNorm_mul_le_mul_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p : ENNReal) {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    eLpNorm (f * g) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C := by
  have hfg : f * g = f • g := rfl
  rw [hfg]
  refine (eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top p g hf).trans ?_
  gcongr
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound hg

end Sobolev

/-! ## §8.3 The space of perturbations of `H`

The book fixes a sequence `ε = (εₙ)` of positive reals and puts

`‖h‖_ε = Σ_k ε_k · sup_{(x,t)} |d^k h(x,t)|`,

the sup being computed in a fixed finite atlas `Ψᵢ : Bᵢ → B(0,1)` of `W × S¹`.
`C^∞_ε` is the space of smooth functions of finite `ε`-norm, and `C^∞_ε(H₀)` is
the subspace of those vanishing near the `1`-periodic orbits of `H₀`.

Following the book's own reduction to charts and the project's local-model
convention, this is set up below for functions on a compact subset `K` of a
normed space `V`, with `iteratedFDeriv` for `d^k`.  Lemma 8.3.2 and
Propositions 8.3.1 and 8.3.4 are proved; the `C⁰` half of Lemma 8.3.2 — separability of
`C(K, ℝ)`, which the book gets from Stone–Weierstrass — is recorded as a proved
consequence of Mathlib's instance. -/

section Perturbations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `sup_K ‖d^k h‖`, the `k`-th sup-seminorm of `h` on `K`. -/
noncomputable def cSupNorm (K : Set V) (k : ℕ) (h : V → ℝ) : ℝ :=
  sSup ((fun x => ‖iteratedFDeriv ℝ k h x‖) '' K)

/-- The `Cⁿ` norm on `K`: the sum of the sup-seminorms up to order `n`. -/
noncomputable def cNorm (K : Set V) (n : ℕ) (h : V → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), cSupNorm K k h

/-- **The norm `‖h‖_ε` of §8.3**: `Σ_k ε_k sup_K ‖d^k h‖`. -/
noncomputable def epsNorm (ε : ℕ → ℝ) (K : Set V) (h : V → ℝ) : ℝ :=
  ∑' k, ε k * cSupNorm K k h

/-- Membership in the book's `C^∞_ε`: `h` is smooth and `‖h‖_ε` converges. -/
def EpsFinite (ε : ℕ → ℝ) (K : Set V) (h : V → ℝ) : Prop :=
  ContDiff ℝ ∞ h ∧ Summable fun k => ε k * cSupNorm K k h

/-- **The space `C^∞_ε(H₀)`**: functions of finite `ε`-norm vanishing on a
neighbourhood of the set `Z` of `1`-periodic orbits of `H₀`.  This is the
perturbation space of Theorem 8.1.1; the support condition is what guarantees
that `H₀ + h` keeps the periodic orbits of `H₀`. -/
def CinftyEpsOf (ε : ℕ → ℝ) (K : Set V) (Z : Set V) : Set (V → ℝ) :=
  {h | EpsFinite ε K h ∧ ∃ U, IsOpen U ∧ Z ⊆ U ∧ ∀ x ∈ U, h x = 0}

/-- The `C¹` distance on `K`, the distance for which §8.3 proves density and
separability. -/
noncomputable def c1Dist (K : Set V) (f g : V → ℝ) : ℝ := cNorm K 1 (f - g)

/-- **The `C⁰` half of Lemma 8.3.2.**  `C(K, ℝ)` is separable.

The book deduces the `C⁰` statement from Stone–Weierstrass (the rational
polynomials are dense); Mathlib has it as an instance for a second-countable,
locally compact domain, which a compact manifold such as `W × S¹` is. -/
theorem separableSpace_continuousMap (Kt : Type*) [TopologicalSpace Kt]
    [SecondCountableTopology Kt] [LocallyCompactSpace Kt] :
    TopologicalSpace.SeparableSpace C(Kt, ℝ) :=
  inferInstance

set_option maxSynthPendingDepth 3 in
/-- **The separability argument behind Lemma 8.3.2**, for an arbitrary family
`P` of `C¹` functions: `P` has a countable subfamily that is `C¹`-dense in it on
the compact `K`.

The proof is purely topological.  A `C¹` function is recorded on `K` by the pair
`(f|_K, Df|_K)` in `C(K, ℝ) × C(K, V*)`, a separable metric space when `V` is
finite-dimensional; any subset of it is separable, so the image of `P` has a
countable dense subset, and a preimage in `P` of each of its points gives the
subfamily.  Since `c1Dist` is the sum of the two sup-distances, it is at most
twice the distance of the pairs.  Working with an arbitrary `P` is what lets
Proposition 8.3.4 impose a support condition on the approximations. -/
theorem exists_countable_c1_dense [FiniteDimensional ℝ V] (K : Set V) (hK : IsCompact K)
    (P : Set (V → ℝ)) (hP : ∀ f ∈ P, ContDiff ℝ 1 f) :
    ∃ S ⊆ P, S.Countable ∧ ∀ f ∈ P, ∀ δ > 0, ∃ g ∈ S, c1Dist K f g < δ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- a `C¹` function, recorded by its values and its derivative on `K`
  let Φ : P → C(K, ℝ) × C(K, V →L[ℝ] ℝ) := fun f =>
    (⟨fun x => f.1 x, (hP f.1 f.2).continuous.comp continuous_subtype_val⟩,
     ⟨fun x => fderiv ℝ f.1 x,
      ((hP f.1 f.2).continuous_fderiv one_ne_zero).comp continuous_subtype_val⟩)
  have hsep : TopologicalSpace.IsSeparable (Set.range Φ) :=
    (TopologicalSpace.isSeparable_univ_iff.2 inferInstance).mono (Set.subset_univ _)
  obtain ⟨t, hts, htc, hdense⟩ := hsep.exists_countable_dense_subset
  have hpre : ∀ τ : t, ∃ f : P, Φ f = τ := fun τ => hts τ.2
  choose pick hpick using hpre
  have : Countable t := htc.to_subtype
  refine ⟨Set.range fun τ : t => (pick τ).1, ?_, Set.countable_range _, ?_⟩
  · rintro g ⟨τ, rfl⟩
    exact (pick τ).2
  intro f hf δ hδ
  have hmem : Φ ⟨f, hf⟩ ∈ closure t := hdense ⟨⟨f, hf⟩, rfl⟩
  obtain ⟨τ, hτt, hdist⟩ := Metric.mem_closure_iff.mp hmem (δ / 2) (by positivity)
  refine ⟨(pick ⟨τ, hτt⟩).1, ⟨⟨τ, hτt⟩, rfl⟩, ?_⟩
  have hΦg : Φ (pick ⟨τ, hτt⟩) = τ := hpick ⟨τ, hτt⟩
  rw [← hΦg] at hdist
  set g := pick ⟨τ, hτt⟩ with hg
  set d := dist (Φ ⟨f, hf⟩) (Φ g) with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hval : ∀ x ∈ K, ‖f x - g.1 x‖ ≤ d := fun x hx => by
    have h := ContinuousMap.dist_apply_le_dist (f := (Φ ⟨f, hf⟩).1) (g := (Φ g).1) ⟨x, hx⟩
    have hp : dist (Φ ⟨f, hf⟩).1 (Φ g).1 ≤ d := by
      rw [hd, Prod.dist_eq]
      exact le_max_left _ _
    rw [← dist_eq_norm]
    exact h.trans hp
  have hder : ∀ x ∈ K, ‖fderiv ℝ f x - fderiv ℝ g.1 x‖ ≤ d := fun x hx => by
    have h := ContinuousMap.dist_apply_le_dist (f := (Φ ⟨f, hf⟩).2) (g := (Φ g).2) ⟨x, hx⟩
    have hp : dist (Φ ⟨f, hf⟩).2 (Φ g).2 ≤ d := by
      rw [hd, Prod.dist_eq]
      exact le_max_right _ _
    rw [← dist_eq_norm]
    exact h.trans hp
  have hfd : Differentiable ℝ f := (hP f hf).differentiable one_ne_zero
  have hgd : Differentiable ℝ g.1 := (hP g.1 g.2).differentiable one_ne_zero
  have hc0 : cSupNorm K 0 (f - g.1) ≤ d := Real.sSup_le (by
    rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [norm_iteratedFDeriv_zero]
    exact hval x hx) hd0
  have hc1 : cSupNorm K 1 (f - g.1) ≤ d := Real.sSup_le (by
    rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [norm_iteratedFDeriv_one, fderiv_sub (hfd x) (hgd x)]
    exact hder x hx) hd0
  calc c1Dist K f g.1 = cSupNorm K 0 (f - g.1) + cSupNorm K 1 (f - g.1) := by
        simp [c1Dist, cNorm, Finset.sum_range_succ]
    _ ≤ d + d := add_le_add hc0 hc1
    _ < δ := by linarith

/-- **Lemma 8.3.2.**  `C^∞(W × S¹)` with the `C¹` topology is separable: there
is a countable family of smooth functions that is `C¹`-dense among the smooth
functions.

The book mollifies a countable `C⁰`-dense family.  The proof here is the
topological argument of `exists_countable_c1_dense`, applied to all smooth
functions.

`FiniteDimensional ℝ V` was missing from an earlier statement and is
necessary: for `V = ℓ¹` and `K = {0}`, the `C¹` distance between two linear
functionals is at least their distance in the non-separable dual `ℓ∞`, so no
countable family approximates them all.  The book's `W × S¹` is covered by
charts in `ℝ^{2n+1}`. -/
theorem lemma_8_3_2 [FiniteDimensional ℝ V] (K : Set V) (hK : IsCompact K) :
    ∃ S : Set (V → ℝ), S.Countable ∧ (∀ g ∈ S, ContDiff ℝ ∞ g) ∧
      ∀ f : V → ℝ, ContDiff ℝ ∞ f → ∀ δ > 0, ∃ g ∈ S, c1Dist K f g < δ := by
  obtain ⟨S, hSP, hSc, hS⟩ := exists_countable_c1_dense K hK {f | ContDiff ℝ ∞ f}
    (fun f (hf : ContDiff ℝ ∞ f) => hf.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))
  exact ⟨S, hSc, hSP, hS⟩

/-- Each sup-seminorm is nonnegative (as a supremum of norms; Mathlib's `sSup`
returns `0` on an empty or unbounded set, which is nonnegative too). -/
theorem cSupNorm_nonneg (K : Set V) (k : ℕ) (h : V → ℝ) : 0 ≤ cSupNorm K k h :=
  Real.sSup_nonneg (by rintro y ⟨x, -, rfl⟩; exact norm_nonneg _)

/-- The `Cⁿ` norm is nonnegative. -/
theorem cNorm_nonneg (K : Set V) (n : ℕ) (h : V → ℝ) : 0 ≤ cNorm K n h :=
  Finset.sum_nonneg fun k _ => cSupNorm_nonneg K k h

/-- The top sup-seminorm is bounded by the `Cⁿ` norm. -/
theorem cSupNorm_le_cNorm (K : Set V) (n : ℕ) (h : V → ℝ) : cSupNorm K n h ≤ cNorm K n h :=
  Finset.single_le_sum (fun k _ => cSupNorm_nonneg K k h)
    (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- **The diagonal argument of Proposition 8.3.1.**  For countably many
functions `f_k` there is one positive sequence `ε` giving every `f_k` a finite
`ε`-norm on `K`: enumerate them and set
`ε_n = 1 / (2ⁿ (1 + Σ_{k ≤ n} ‖f_k‖_{Cⁿ}))`.  Then for `n ≥ k` one has
`ε_n ‖d^n f_k‖_∞ ≤ 2⁻ⁿ`. -/
theorem exists_eps_summable (K : Set V) (S : Set (V → ℝ)) (hSc : S.Countable) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ ∀ g ∈ S, Summable fun k => ε k * cSupNorm K k g := by
  obtain ⟨e, he⟩ := (hSc.insert 0).exists_eq_range (Set.insert_nonempty 0 S)
  set D : ℕ → ℝ := fun n => 1 + ∑ k ∈ Finset.range (n + 1), cNorm K n (e k) with hD
  have hDpos : ∀ n, 0 < D n := fun n => by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.range (n + 1)) => cNorm_nonneg K n (e k)
    simp only [hD]; linarith
  refine ⟨fun n => 1 / (2 ^ n * D n),
    fun n => div_pos one_pos (mul_pos (by positivity) (hDpos n)), ?_⟩
  intro g hg
  obtain ⟨k, rfl⟩ : g ∈ Set.range e := by
    rw [← he]
    exact Set.mem_insert_of_mem 0 hg
  have hle : ∀ n, k ≤ n → 1 / (2 ^ n * D n) * cSupNorm K n (e k) ≤ (1 / 2) ^ n := by
    intro n hn
    have h1 : cSupNorm K n (e k) ≤ D n := by
      have h2 := cSupNorm_le_cNorm K n (e k)
      have h3 : cNorm K n (e k) ≤ ∑ j ∈ Finset.range (n + 1), cNorm K n (e j) :=
        Finset.single_le_sum (fun j _ => cNorm_nonneg K n (e j))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
      simp only [hD]; linarith
    calc 1 / (2 ^ n * D n) * cSupNorm K n (e k) ≤ 1 / (2 ^ n * D n) * D n := by
          exact mul_le_mul_of_nonneg_left h1
            (div_nonneg one_pos.le (mul_nonneg (by positivity) (hDpos n).le))
      _ = (1 / 2) ^ n := by
          have hne := (hDpos n).ne'
          rw [one_div_pow]; field_simp
  refine Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)) ?_
  rw [Filter.eventually_atTop]
  refine ⟨k, fun n hn => ?_⟩
  rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg one_pos.le
    (mul_nonneg (by positivity) (hDpos n).le)) (cSupNorm_nonneg K n (e k)))]
  exact hle n hn

/-- **Proposition 8.3.1.**  The sequence `ε` can be chosen so that `C^∞_ε` is
`C¹`-dense in `C^∞(W × S¹)`.

Proved from Lemma 8.3.2 by the book's diagonal argument
(`exists_eps_summable`): the `ε` that makes every member of the countable dense
family of finite `ε`-norm works, and the family itself does the approximating. -/
theorem prop_8_3_1 [FiniteDimensional ℝ V] (K : Set V) (hK : IsCompact K) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧
      ∀ f : V → ℝ, ContDiff ℝ ∞ f → ∀ δ > 0,
        ∃ h : V → ℝ, EpsFinite ε K h ∧ c1Dist K f h < δ := by
  obtain ⟨S, hSc, hSsmooth, hSdense⟩ := lemma_8_3_2 K hK
  obtain ⟨ε, hε, hsum⟩ := exists_eps_summable K S hSc
  refine ⟨ε, hε, fun f hf δ hδ => ?_⟩
  obtain ⟨g, hg, hgδ⟩ := hSdense f hf δ hδ
  exact ⟨g, ⟨hSsmooth g hg, hsum g hg⟩, hgδ⟩

/-- **Proposition 8.3.4**, the compactly supported refinement of Proposition
8.3.1: for a suitable `ε`, every function supported in a small enough
neighbourhood `V₀` of a point can be `C¹`-approximated by functions of `C^∞_ε`
supported in a prescribed neighbourhood `U`.

The book multiplies the approximations of Proposition 8.3.1 by a cut-off and
rescales `ε`.  The proof here needs no cut-off.  Fix a countable dense set `D`
of centres and the radii `1/(n+1)`.  For each closed ball `B(c, 1/(n+1))`,
`exists_countable_c1_dense` gives a countable family, `C¹`-dense among the
smooth functions supported in that ball, and one `ε` makes all these countably
many functions of finite `ε`-norm (`exists_eps_summable`).  Given `x₀` and `U`,
a ball `B(c, ρ)` with `B(x₀, ρ/2) ⊆ B(c, ρ) ⊆ U` exists, and `V₀ = B(x₀, ρ/2)`
works: a function supported in `V₀` is supported in `B(c, ρ)`, and so are its
approximations.

`FiniteDimensional ℝ V` is assumed, as in Lemma 8.3.2 and Proposition 8.3.1; the
book works in charts of `ℝ^{2n+1}`. -/
theorem prop_8_3_4 [FiniteDimensional ℝ V] (K : Set V) (hK : IsCompact K) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧
      ∀ x₀ ∈ K, ∀ U ∈ 𝓝 x₀, ∃ V₀ ∈ 𝓝 x₀, V₀ ⊆ U ∧
        ∀ h : V → ℝ, ContDiff ℝ ∞ h → tsupport h ⊆ V₀ → ∀ δ > 0,
          ∃ g : V → ℝ, EpsFinite ε K g ∧ tsupport g ⊆ U ∧ c1Dist K h g < δ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense V
  -- the smooth functions supported in the closed ball `B(c, 1/(n+1))`
  let P : V × ℕ → Set (V → ℝ) := fun p =>
    {f | ContDiff ℝ ∞ f ∧ tsupport f ⊆ Metric.closedBall p.1 (1 / ((p.2 : ℝ) + 1))}
  have h1 : ∀ p, ∀ f ∈ P p, ContDiff ℝ 1 f := fun p f
      (hf : ContDiff ℝ ∞ f ∧ tsupport f ⊆ Metric.closedBall p.1 (1 / ((p.2 : ℝ) + 1))) =>
    hf.1.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  choose S hSP hSc hSd using fun p => exists_countable_c1_dense K hK (P p) (h1 p)
  have : Countable D := hDc.to_subtype
  let T : Set (V → ℝ) := ⋃ c : D, ⋃ n : ℕ, S (c.1, n)
  have hTc : T.Countable := Set.countable_iUnion fun c => Set.countable_iUnion fun n => hSc _
  obtain ⟨ε, hε, hsum⟩ := exists_eps_summable K T hTc
  refine ⟨ε, hε, fun x₀ _ U hU => ?_⟩
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hr)
  set ρ : ℝ := 1 / ((n : ℝ) + 1) with hρ
  have hρpos : 0 < ρ := by positivity
  obtain ⟨c, hc, hcD⟩ :=
    hDd.inter_open_nonempty (Metric.ball x₀ (ρ / 2)) Metric.isOpen_ball
      ⟨x₀, Metric.mem_ball_self (half_pos hρpos)⟩
  have hc' : dist c x₀ < ρ / 2 := hc
  refine ⟨Metric.ball x₀ (ρ / 2), Metric.ball_mem_nhds x₀ (half_pos hρpos), fun y hy => ?_, ?_⟩
  · have hy' : dist y x₀ < ρ / 2 := hy
    exact hrU (by rw [Metric.mem_ball]; linarith)
  intro h hh hsupp δ hδ
  have hhP : h ∈ P (c, n) := ⟨hh, hsupp.trans fun y hy => by
    have hy' : dist y x₀ < ρ / 2 := hy
    show dist y c ≤ ρ
    linarith [dist_triangle y x₀ c, dist_comm x₀ c]⟩
  obtain ⟨g, hgS, hgδ⟩ := hSd (c, n) h hhP δ hδ
  have hgP : ContDiff ℝ ∞ g ∧ tsupport g ⊆ Metric.closedBall c ρ := hSP (c, n) hgS
  have hgT : g ∈ T := Set.mem_iUnion.2 ⟨⟨c, hcD⟩, Set.mem_iUnion.2 ⟨n, hgS⟩⟩
  refine ⟨g, ⟨hgP.1, hsum g hgT⟩, hgP.2.trans fun y hy => ?_, hgδ⟩
  have hy' : dist y c ≤ ρ := hy
  exact hrU (by rw [Metric.mem_ball]; linarith [dist_triangle y c x₀])

end Perturbations

end Chapter8
end MorseFloer
