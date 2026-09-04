import MorseFloer.Basic

/-!
# Chapter 3: The complex of critical points

Formalization of Chapter 3 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part I, printed pages 51–74).

The chapter fixes a compact manifold `V`, a Morse function `f` on it and a
generic (Smale) pseudo-gradient `X`, and builds out of that data a chain complex
over `Z/2`:

* **§3.1** defines `Cₖ(f)`, the vector space with basis the critical points of
  index `k`, and the differential `∂ₓ a = Σ_b nₓ(a,b) · b`, where `nₓ(a,b)` is
  the number, modulo 2, of trajectories of `X` running from `a` down to `b`.
  Then `∂ₓ ∘ ∂ₓ = 0`, so `(C⋆(f), ∂ₓ)` is a complex and its homology is defined.
* **§3.2** supplies the geometric input: the space of broken trajectories
  `L̄(a,b)` is compact (Theorem 3.2.2), it is finite when the index drop is `1`
  (Corollary 3.2.4) — so that `nₓ(a,b)` makes sense — and it is a compact
  `1`-manifold with boundary when the index drop is `2` (Theorem 3.2.6), whose
  boundary is the set of once-broken trajectories.  Since a compact
  `1`-manifold has an even number of boundary points, the broken trajectories
  cancel in pairs, which is exactly `∂ₓ ∘ ∂ₓ = 0`.
* **§3.3** repeats the construction over `ℤ` using orientations, and observes
  that the mod `2` counts are the reductions of the integral ones.
* **§3.4** proves the homology is independent of `f` and `X`.
* **§3.5** transports everything to a cobordism.

## What is formalized here

Mathlib has no moduli spaces of trajectories, so the analytic and geometric
input of §3.2 cannot even be *stated*.  What can be — and is — formalized is
everything downstream of it, which is the whole algebraic skeleton of the
chapter:

* `Chains R ind k` — the free `R`-module on the critical points of index `k`
  (§3.1, and §3.3 for `R = ℤ`);
* `dLin ind cnt k` — the differential `Cₖ₊₁ → Cₖ` attached to an abstract count
  function `cnt : Crit → Crit → R`;
* `BrokenPairs ind cnt` — the hypothesis that for `Ind a = Ind b + 2` the
  once-broken trajectories from `a` to `b` cancel: this is the *conclusion* of
  Theorem 3.2.6 combined with Theorem 2.3.2 (a compact `1`-manifold has an even
  number of boundary points), stated as a hypothesis because its proof is
  geometric;
* `dLin_comp_dLin` — a **complete proof** that `∂ ∘ ∂ = 0` from `BrokenPairs`;
* `morseComplex` — the resulting object of `ChainComplex (ModuleCat R) ℕ`, and
  `morseHomology`, its homology, so that Chapter 4 has something concrete to
  work with;
* `cycles`, `boundaries`, `boundaries_le_cycles` — the book's description of
  `Hₖ` as `Ker ∂ₖ / Im ∂ₖ₊₁`;
* `BrokenPairs.map` and `BrokenPairs.intCast` — §3.3's remark that the mod `2`
  complex is the reduction of the integral one;
* `coneDiff`, `chainMap_of_coneDiff_comp` — the algebraic engine of Step 1 of
  Theorem 3.4.2: a differential which is triangular in a decomposition
  `Cₖ(f₀) ⊕ Cₖ₊₁(f₁)` squares to zero exactly when its off-diagonal part is a
  chain map;
* `sub_mem_range_of_chainHomotopy` — the algebraic engine of Step 3: maps
  differing by a chain homotopy agree on homology classes;
* `modelFun`, `modelField`, `modelFlow`, `modelTransition` — the Morse model of
  §3.2.c, with a complete proof of Lemma 3.2.11 (the map induced by the flow
  between the two ends of a Morse chart is `(x⁻,x⁺) ↦ (‖x⁺‖/‖x⁻‖ · x⁻,
  ‖x⁻‖/‖x⁺‖ · x⁺)`), plus the fact that the model function decreases strictly
  along the flow.

## Gaps: results that today's Mathlib cannot state

Nothing here is a fictitious statement; the following results of the chapter
carry no Lean declaration at all, because the objects they speak about do not
exist in Mathlib (no space of trajectories `L(a,b)`, no compactified space
`L̄(a,b)` with its topology of §3.2.a, no manifolds with boundary or corners,
no Smale condition):

* Remarks 3.2.1, 3.2.3, 3.2.8, 3.2.12 — commentary on the topology of `L̄(a,b)`.
* **Theorem 3.2.2** (`L̄(a,b)` is compact) and **Corollary 3.2.4** (`L(a,b)` is
  finite when `Ind a = Ind b + 1`).  The latter is what makes `nₓ(a,b) ∈ Z/2`
  well defined; here we take the count function as given data instead.
* **Proposition 3.2.5** (`L(a,b)` is dense in `L̄(a,b)`).
* **Theorem 3.2.6** (`L̄(a,b)` is a compact `1`-manifold with boundary when
  `Ind a = Ind b + 2`) and **Propositions 3.2.7, 3.2.9, 3.2.10**, its local
  analysis.  Their combined consequence is exactly the hypothesis
  `BrokenPairs`.  Only **Lemma 3.2.11**, a computation with the explicit flow
  of the model pseudo-gradient, is proved below.
* **Corollaries 3.1.1 and 3.1.2** (`ℂPⁿ` is not diffeomorphic to `S²ⁿ`; `S²`,
  `T²` and `P²(ℝ)` are pairwise non-diffeomorphic).  These need the invariance
  theorem of Chapter 4 to compare the homologies of *different* manifolds; with
  abstract count data there is no manifold to compare.
* **Theorem 3.4.2** and **Proposition 3.4.3** (independence of the homology of
  the choices of `f` and `X`).  Stated for abstract data the statement would be
  false — two unrelated count functions have unrelated homologies — and the
  geometric hypothesis linking them (they come from the same manifold) is not
  expressible.  The two purely algebraic steps of the proof *are* proved below.
* §3.5 (cobordisms) in its entirety.

The examples of §3.1.c are recorded for the torus, whose mod `2` differential
vanishes identically; the same holds for the round sphere `Sⁿ`, for `ℂPⁿ` and
for `P²(ℝ)`, since in each case every count is even.  The "other sphere" of
§3.1.c, whose complex is not trivial although its homology is the same, would
need a computation of kernels and images that is not attempted here.
-/

open CategoryTheory

namespace MorseFloer
namespace Chapter3

/-! ## §3.1 The complex

Throughout, `Crit` is the (finite) set of critical points of a Morse function on
a compact manifold and `ind : Crit → ℕ` is the Morse index.  The connections
between critical points are abstracted into a *count function*
`cnt : Crit → Crit → R`: for `R = ZMod 2` this is the book's `nₓ(a,b)`, the
number modulo `2` of trajectories from `a` to `b` (§3.1.a), and for `R = ℤ` it is
the signed count `Nₓ(a,b)` of §3.3.  Only the values of `cnt` on pairs whose
indices differ by one are ever used. -/

section Complex

/-- `Critₖ(f)`, the set of critical points of index `k`. -/
abbrev CritSet {Crit : Type*} (ind : Crit → ℕ) (k : ℕ) := {c : Crit // ind c = k}

/-- `Cₖ(f)`: the free module on the critical points of index `k` (§3.1).

For `R = ZMod 2` this is the book's `Ck(f) = {Σ a_c c | a_c ∈ Z/2}`; a chain is
recorded by its family of coefficients, so `Chains R ind k` is free on
`Critₖ(f)` with the basis `Pi.basisFun`. -/
abbrev Chains (R : Type*) {Crit : Type*} (ind : Crit → ℕ) (k : ℕ) := CritSet ind k → R

/-- **The differential `∂ₓ : Cₖ₊₁ → Cₖ`** (§3.1.a).

On a basis element `a` of index `k+1` it is `Σ_b cnt a b · b`, the sum being over
the critical points `b` of index `k`; on a general chain it is extended
linearly, which in coordinates is the matrix product written here. -/
def dLin {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit] (ind : Crit → ℕ)
    (cnt : Crit → Crit → R) (k : ℕ) : Chains R ind (k + 1) →ₗ[R] Chains R ind k where
  toFun x := fun b => ∑ a : CritSet ind (k + 1), x a * cnt a.1 b.1
  map_add' x y := by
    funext b
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    funext b
    simp [Finset.mul_sum, mul_assoc]

@[simp]
theorem dLin_apply {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit] (ind : Crit → ℕ)
    (cnt : Crit → Crit → R) (k : ℕ) (x : Chains R ind (k + 1)) (b : CritSet ind k) :
    dLin ind cnt k x b = ∑ a : CritSet ind (k + 1), x a * cnt a.1 b.1 := rfl

/-- **The broken-trajectory hypothesis.**

For critical points `a` of index `k+2` and `b` of index `k`, the number of
once-broken trajectories from `a` to `b`, namely
`Σ_{c ∈ Critₖ₊₁} cnt a c · cnt c b`, vanishes.

This is not an axiom of convenience: it is precisely what §3.1.b deduces from
Theorem 3.2.6.  That theorem makes `L̄(a,b)` a compact `1`-manifold with
boundary whose boundary points are the once-broken trajectories, and Theorem
2.3.2 says such a boundary is finite of even cardinality.  Neither statement is
expressible in Mathlib, so the consequence is taken as the hypothesis. -/
def BrokenPairs {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit] (ind : Crit → ℕ)
    (cnt : Crit → Crit → R) : Prop :=
  ∀ (k : ℕ) (a : CritSet ind (k + 2)) (b : CritSet ind k),
    ∑ c : CritSet ind (k + 1), cnt a.1 c.1 * cnt c.1 b.1 = 0

/-- **`∂ₓ ∘ ∂ₓ = 0`** (§3.1.b).

Expanding the composite, the coefficient of `b` in `∂∂a` is
`Σ_c cnt a c · cnt c b`, which vanishes by `BrokenPairs`.  This is a complete
proof: only the geometric input is assumed. -/
theorem dLin_comp_dLin {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    {ind : Crit → ℕ} {cnt : Crit → Crit → R} (h : BrokenPairs ind cnt) (k : ℕ) :
    (dLin ind cnt k).comp (dLin ind cnt (k + 1)) = 0 := by
  ext x b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, dLin_apply]
  have key : ∀ c : CritSet ind (k + 1),
      (∑ a : CritSet ind (k + 2), x a * cnt a.1 c.1) * cnt c.1 b.1
        = ∑ a : CritSet ind (k + 2), x a * (cnt a.1 c.1 * cnt c.1 b.1) := by
    intro c
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.mul_sum, h k a b, mul_zero]

/-- **The Morse complex `(C⋆(f), ∂ₓ)`** (§3.1.b), as an object of Mathlib's
category of chain complexes, so that all the homological algebra applies to it.

The grading is by the Morse index and the differential lowers it by one. -/
noncomputable def morseComplex {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    {ind : Crit → ℕ} {cnt : Crit → Crit → R} (h : BrokenPairs ind cnt) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of R (Chains R ind k))
    (fun k => ModuleCat.ofHom (dLin ind cnt k))
    (fun k => ModuleCat.hom_ext (by
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
      exact dLin_comp_dLin h k))

theorem morseComplex_X {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    {ind : Crit → ℕ} {cnt : Crit → Crit → R} (h : BrokenPairs ind cnt) (k : ℕ) :
    (morseComplex h).X k = ModuleCat.of R (Chains R ind k) := rfl

theorem morseComplex_d {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    {ind : Crit → ℕ} {cnt : Crit → Crit → R} (h : BrokenPairs ind cnt) (k : ℕ) :
    (morseComplex h).d (k + 1) k = ModuleCat.ofHom (dLin ind cnt k) :=
  ChainComplex.of_d (fun k => ModuleCat.of R (Chains R ind k))
    (fun k => ModuleCat.ofHom (dLin ind cnt k)) k

/-- **Morse homology `Hₖ(f, X)`** (§3.1.b): the homology of the complex of
critical points.  Chapter 4 studies its independence of `f` and `X`. -/
noncomputable def morseHomology {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    {ind : Crit → ℕ} {cnt : Crit → Crit → R} (h : BrokenPairs ind cnt) (k : ℕ) :
    ModuleCat R :=
  (morseComplex h).homology k

/-- The cycles in degree `k + 1`: the kernel of `∂ : Cₖ₊₁ → Cₖ`.

The indexing convention throughout is that `dLin ind cnt k` is the differential
`Cₖ₊₁ → Cₖ`; the differential leaving degree `0` is zero, so every chain of
degree `0` is a cycle and only the positive degrees need a definition. -/
noncomputable def cycles {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    (ind : Crit → ℕ) (cnt : Crit → Crit → R) (k : ℕ) : Submodule R (Chains R ind (k + 1)) :=
  LinearMap.ker (dLin ind cnt k)

/-- The boundaries in degree `k`: the image of `∂ : Cₖ₊₁ → Cₖ`. -/
noncomputable def boundaries {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    (ind : Crit → ℕ) (cnt : Crit → Crit → R) (k : ℕ) : Submodule R (Chains R ind k) :=
  LinearMap.range (dLin ind cnt k)

/-- `Im ∂ₖ₊₂ ⊆ Ker ∂ₖ₊₁`, so that the book's quotient `Hₖ = Ker ∂ₖ / Im ∂ₖ₊₁`
(§3.1.b) is defined in every degree. -/
theorem boundaries_le_cycles {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    {ind : Crit → ℕ} {cnt : Crit → Crit → R} (h : BrokenPairs ind cnt) (k : ℕ) :
    boundaries ind cnt (k + 1) ≤ cycles ind cnt k :=
  LinearMap.range_le_ker_iff.mpr (dLin_comp_dLin h k)

/-- The differential attached to a count function that vanishes identically. -/
theorem dLin_zero {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit] (ind : Crit → ℕ)
    (k : ℕ) : dLin ind (fun _ _ => (0 : R)) k = 0 := by
  ext x b
  simp

/-- A vanishing count function satisfies the broken-trajectory hypothesis. -/
theorem brokenPairs_zero {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
    (ind : Crit → ℕ) : BrokenPairs ind (fun _ _ => (0 : R)) := by
  intro k a b
  simp

/-- With a vanishing differential every chain is a cycle. -/
theorem cycles_zero {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit] (ind : Crit → ℕ)
    (k : ℕ) : cycles ind (fun _ _ => (0 : R)) k = ⊤ := by
  show LinearMap.ker (dLin ind (fun _ _ => (0 : R)) k) = ⊤
  rw [dLin_zero]
  exact LinearMap.ker_zero

/-- With a vanishing differential the only boundary is `0`, so the homology is
the whole of `Cₖ`. -/
theorem boundaries_zero {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit] (ind : Crit → ℕ)
    (k : ℕ) : boundaries ind (fun _ _ => (0 : R)) k = ⊥ := by
  show LinearMap.range (dLin ind (fun _ _ => (0 : R)) k) = ⊥
  rw [dLin_zero]
  exact LinearMap.range_zero

end Complex

/-! ## §3.3 Orientations, the complex over `ℤ`

Choosing an orientation of each stable manifold turns `L(a,b)`, for an index
drop of one, into a finite set of *signed* points; their sum `Nₓ(a,b) ∈ ℤ`
replaces `nₓ(a,b)`.  Nothing above used `R = ZMod 2`, so the integral complex is
the same construction with `R = ℤ`.  The book's remark that `nₓ(a,b)` is the
reduction of `Nₓ(a,b)` modulo `2` becomes the statement that the
broken-trajectory hypothesis is preserved by any ring morphism. -/

section Coefficients

/-- The broken-trajectory hypothesis is preserved by change of coefficients. -/
theorem BrokenPairs.map {R R' : Type*} [CommRing R] [CommRing R'] {Crit : Type*} [Fintype Crit]
    {ind : Crit → ℕ} {cnt : Crit → Crit → R} (h : BrokenPairs ind cnt) (φ : R →+* R') :
    BrokenPairs ind fun a b => φ (cnt a b) := by
  intro k a b
  show ∑ c : CritSet ind (k + 1), φ (cnt a.1 c.1) * φ (cnt c.1 b.1) = 0
  have hsum : ∑ c : CritSet ind (k + 1), φ (cnt a.1 c.1) * φ (cnt c.1 b.1)
      = φ (∑ c : CritSet ind (k + 1), cnt a.1 c.1 * cnt c.1 b.1) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => (map_mul φ _ _).symm
  rw [hsum, h k a b, map_zero]

/-- **§3.3.**  The mod `2` complex of §3.1 is the reduction of the integral
complex: if the signed counts `Nₓ` satisfy the broken-trajectory hypothesis over
`ℤ`, their reductions `nₓ` satisfy it over `Z/2`. -/
theorem BrokenPairs.intCast {Crit : Type*} [Fintype Crit] {ind : Crit → ℕ}
    {cnt : Crit → Crit → ℤ} (h : BrokenPairs ind cnt) :
    BrokenPairs ind fun a b => ((cnt a b : ℤ) : ZMod 2) :=
  h.map (Int.castRingHom (ZMod 2))

end Coefficients

/-! ## §3.1.c Examples

The mod `2` differential vanishes for the height function on the round sphere
(no two critical points have adjacent indices), for `cos 2πx + cos 2πy` on the
torus (each count is `2`), for `ℂPⁿ` (all indices are even) and for `P²(ℝ)`.  We
record the torus, whose critical points are a minimum, two saddles and a
maximum. -/

section Examples

/-- The Morse indices of the four critical points of `cos 2πx + cos 2πy` on the
torus: a minimum, two saddles, a maximum (§1.4.c and §3.1.c). -/
def torusIndex : Fin 4 → ℕ := ![0, 1, 1, 2]

/-- Every connection between critical points of the torus example is counted
twice, so all counts vanish modulo `2` (§3.1.c). -/
def torusCount : Fin 4 → Fin 4 → ZMod 2 := fun _ _ => 0

theorem torus_brokenPairs : BrokenPairs torusIndex torusCount :=
  brokenPairs_zero torusIndex

/-- The torus complex has zero differential, so every chain is a cycle (here in
degree `k + 1`; in degree `0` there is nothing to check). -/
theorem torus_cycles (k : ℕ) : cycles torusIndex torusCount k = ⊤ :=
  cycles_zero torusIndex k

/-- Dually no nonzero chain is a boundary, so the homology of the torus complex
is the whole of `Cₖ` in each degree: `Z/2` for `k = 0` and `k = 2`, and
`Z/2 ⊕ Z/2` for `k = 1`, which is the mod `2` homology of `T²`. -/
theorem torus_boundaries (k : ℕ) : boundaries torusIndex torusCount k = ⊥ :=
  boundaries_zero torusIndex k

end Examples

/-! ## §3.4 Independence of the homology: the algebraic steps

The proof of Theorem 3.4.2 builds, out of an interpolation `F` between two Morse
functions, a Morse function on `V × [-1/3, 4/3]` whose complex is
`Cₖ₊₁(F̃) = Cₖ(f₀) ⊕ Cₖ₊₁(f₁)` and whose differential is triangular,

`∂ = [[∂₀, 0], [Φ, ∂₁]]`.

Two purely algebraic facts are then used, and both are proved here:

* Step 1: `∂ ∘ ∂ = 0` forces `Φ ∘ ∂₀ + ∂₁ ∘ Φ = 0`, i.e. `Φ` is a chain map;
* Step 3: the analogous computation with a four-block differential produces
  `Φ_G ∘ Φ_F - Φ_H = S ∘ ∂₀ + ∂₂ ∘ S`, and maps differing by such a homotopy
  agree on homology.

Only the geometric construction of `F̃` and of its pseudo-gradient is missing,
and with it Theorem 3.4.2 itself. -/

section Cone

variable {R : Type*} [CommRing R] {C D : ℕ → Type*}
  [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)]
  [∀ k, AddCommGroup (D k)] [∀ k, Module R (D k)]

/-- The triangular differential on `Cₖ ⊕ Dₖ₊₁` of Step 1 of Theorem 3.4.2:
`(x, y) ↦ (∂₀ x, Φ x + ∂₁ y)`. -/
def coneDiff (d₀ : ∀ k, C (k + 1) →ₗ[R] C k) (d₁ : ∀ k, D (k + 1) →ₗ[R] D k)
    (Φ : ∀ k, C k →ₗ[R] D k) (k : ℕ) :
    (C (k + 1) × D (k + 2)) →ₗ[R] (C k × D (k + 1)) :=
  ((d₀ k).comp (LinearMap.fst R (C (k + 1)) (D (k + 2)))).prod
    ((Φ (k + 1)).comp (LinearMap.fst R (C (k + 1)) (D (k + 2)))
      + (d₁ (k + 1)).comp (LinearMap.snd R (C (k + 1)) (D (k + 2))))

@[simp]
theorem coneDiff_apply (d₀ : ∀ k, C (k + 1) →ₗ[R] C k) (d₁ : ∀ k, D (k + 1) →ₗ[R] D k)
    (Φ : ∀ k, C k →ₗ[R] D k) (k : ℕ) (p : C (k + 1) × D (k + 2)) :
    coneDiff d₀ d₁ Φ k p = (d₀ k p.1, Φ (k + 1) p.1 + d₁ (k + 1) p.2) := rfl

/-- **Step 1 of Theorem 3.4.2.**  If the triangular differential squares to
zero, its off-diagonal component is a chain map: `Φ ∘ ∂₀ + ∂₁ ∘ Φ = 0`. -/
theorem chainMap_of_coneDiff_comp {d₀ : ∀ k, C (k + 1) →ₗ[R] C k}
    {d₁ : ∀ k, D (k + 1) →ₗ[R] D k} {Φ : ∀ k, C k →ₗ[R] D k}
    (h : ∀ k, (coneDiff d₀ d₁ Φ k).comp (coneDiff d₀ d₁ Φ (k + 1)) = 0) (k : ℕ)
    (x : C (k + 2)) :
    Φ (k + 1) (d₀ (k + 1) x) + d₁ (k + 1) (Φ (k + 2) x) = 0 := by
  have h2 := congrArg Prod.snd (LinearMap.congr_fun (h k) (x, 0))
  simpa using h2

end Cone

/-- In characteristic `2` there are no signs: `x + y = 0` says `x = y`. -/
theorem eq_of_add_eq_zero_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M}
    (h : x + y = 0) : x = y := by
  have h2 : y + y = 0 := by
    rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 by decide, zero_smul]
  calc x = x + (y + y) := by rw [h2, add_zero]
    _ = x + y + y := by rw [add_assoc]
    _ = y := by rw [h, zero_add]

/-- **Step 1 of Theorem 3.4.2, mod `2`.**  Over `Z/2` the conclusion takes the
book's form `Φ ∘ ∂₀ = ∂₁ ∘ Φ`. -/
theorem chainMap_of_coneDiff_comp_two {C D : ℕ → Type*}
    [∀ k, AddCommGroup (C k)] [∀ k, Module (ZMod 2) (C k)]
    [∀ k, AddCommGroup (D k)] [∀ k, Module (ZMod 2) (D k)]
    {d₀ : ∀ k, C (k + 1) →ₗ[ZMod 2] C k} {d₁ : ∀ k, D (k + 1) →ₗ[ZMod 2] D k}
    {Φ : ∀ k, C k →ₗ[ZMod 2] D k}
    (h : ∀ k, (coneDiff d₀ d₁ Φ k).comp (coneDiff d₀ d₁ Φ (k + 1)) = 0) (k : ℕ)
    (x : C (k + 2)) :
    Φ (k + 1) (d₀ (k + 1) x) = d₁ (k + 1) (Φ (k + 2) x) :=
  eq_of_add_eq_zero_two (chainMap_of_coneDiff_comp h k x)

/-- **Step 3 of Theorem 3.4.2.**  Two maps differing by a chain homotopy,
`u - v = ∂' ∘ S + T ∘ ∂`, send a cycle to two chains differing by a boundary,
hence induce the same map on homology. -/
theorem sub_mem_range_of_chainHomotopy {R : Type*} [CommRing R]
    {A A' B B' : Type*} [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (u v : A →ₗ[R] B) (d : A →ₗ[R] A') (d' : B' →ₗ[R] B)
    (S : A →ₗ[R] B') (T : A' →ₗ[R] B)
    (hom : ∀ x, u x - v x = d' (S x) + T (d x)) {x : A} (hx : d x = 0) :
    u x - v x ∈ LinearMap.range d' := by
  rw [hom x, hx, map_zero, add_zero]
  exact ⟨S x, rfl⟩

/-! ## §3.2.c The Morse model

The heart of the proof that `L̄(a,b)` is a manifold with boundary is a
computation inside a Morse chart, where

`f(x⁻, x⁺) = -‖x⁻‖² + ‖x⁺‖²`  and  `X = -grad f = (2x⁻, -2x⁺)`.

Everything in this paragraph is about that explicit model, so it can be
formalized without any theory of moduli spaces.  We prove that the stated flow
is indeed the flow of `X`, that `f` decreases strictly along it away from the
critical point, and Lemma 3.2.11: the map induced by the flow from the upper to
the lower boundary of the chart is `(x⁻,x⁺) ↦ (‖x⁺‖/‖x⁻‖ · x⁻, ‖x⁻‖/‖x⁺‖ · x⁺)`,
reached at the positive time `½ log(‖x⁺‖/‖x⁻‖)`. -/

section MorseModel

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The model Morse function of index `dim E` at the origin (§3.2.c). -/
def modelFun (p : E × F) : ℝ := -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2

/-- The model pseudo-gradient `X = -grad f`. -/
def modelField (p : E × F) : E × F := ((2 : ℝ) • p.1, (-2 : ℝ) • p.2)

/-- The flow of the model pseudo-gradient, `φₛ(x⁻,x⁺) = (e^{2s} x⁻, e^{-2s} x⁺)`
(proof of Lemma 3.2.11). -/
def modelFlow (s : ℝ) (p : E × F) : E × F :=
  (Real.exp (2 * s) • p.1, Real.exp (-(2 * s)) • p.2)

theorem modelFlow_zero (p : E × F) : modelFlow 0 p = p := by
  simp [modelFlow]

/-- The flow property `φ_{s+t} = φₛ ∘ φₜ`. -/
theorem modelFlow_add (s t : ℝ) (p : E × F) :
    modelFlow (s + t) p = modelFlow s (modelFlow t p) := by
  simp only [modelFlow, smul_smul, ← Real.exp_add, Prod.mk.injEq]
  constructor
  · rw [show (2 : ℝ) * (s + t) = 2 * s + 2 * t by ring]
  · rw [show -((2 : ℝ) * (s + t)) = -(2 * s) + -(2 * t) by ring]

/-- `φ` really is the flow of `X`: first component. -/
theorem hasDerivAt_modelFlow_fst (p : E × F) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (modelFlow t p).1) ((modelField (modelFlow s p)).1) s := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have key : (modelField (modelFlow s p)).1 = (Real.exp (2 * s) * 2) • p.1 := by
    show (2 : ℝ) • (Real.exp (2 * s) • p.1) = (Real.exp (2 * s) * 2) • p.1
    rw [smul_smul, mul_comm]
  rw [key]
  exact (h.exp).smul_const p.1

/-- `φ` really is the flow of `X`: second component. -/
theorem hasDerivAt_modelFlow_snd (p : E × F) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (modelFlow t p).2) ((modelField (modelFlow s p)).2) s := by
  have h0 : HasDerivAt (fun t : ℝ => 2 * t) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have h : HasDerivAt (fun t : ℝ => -(2 * t)) (-2) s := h0.neg
  have key : (modelField (modelFlow s p)).2 = (Real.exp (-(2 * s)) * -2) • p.2 := by
    show (-2 : ℝ) • (Real.exp (-(2 * s)) • p.2) = (Real.exp (-(2 * s)) * -2) • p.2
    rw [smul_smul, mul_comm]
  rw [key]
  exact (h.exp).smul_const p.2

private theorem norm_smul_sq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c : ℝ} (hc : 0 < c) (v : G) : ‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]

/-- The model function read along the flow. -/
theorem modelFun_modelFlow (s : ℝ) (p : E × F) :
    modelFun (modelFlow s p)
      = -(Real.exp (4 * s) * ‖p.1‖ ^ 2) + Real.exp (-(4 * s)) * ‖p.2‖ ^ 2 := by
  have e1 : Real.exp (2 * s) ^ 2 = Real.exp (4 * s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(2 * s)) ^ 2 = Real.exp (-(4 * s)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h1 : ‖Real.exp (2 * s) • p.1‖ ^ 2 = Real.exp (4 * s) * ‖p.1‖ ^ 2 := by
    rw [norm_smul_sq (Real.exp_pos _), e1]
  have h2 : ‖Real.exp (-(2 * s)) • p.2‖ ^ 2 = Real.exp (-(4 * s)) * ‖p.2‖ ^ 2 := by
    rw [norm_smul_sq (Real.exp_pos _), e2]
  simp only [modelFun, modelFlow, h1, h2]

/-- The derivative of `f` along the flow. -/
theorem hasDerivAt_modelFun_modelFlow (p : E × F) (s : ℝ) :
    HasDerivAt (fun t : ℝ => modelFun (modelFlow t p))
      (-(Real.exp (4 * s) * 4 * ‖p.1‖ ^ 2) + Real.exp (-(4 * s)) * -4 * ‖p.2‖ ^ 2) s := by
  have h4 : HasDerivAt (fun t : ℝ => 4 * t) 4 s := by
    simpa using (hasDerivAt_id s).const_mul (4 : ℝ)
  have hfun : (fun t : ℝ => modelFun (modelFlow t p))
      = fun t : ℝ => -(Real.exp (4 * t) * ‖p.1‖ ^ 2) + Real.exp (-(4 * t)) * ‖p.2‖ ^ 2 :=
    funext fun t => modelFun_modelFlow t p
  rw [hfun]
  exact (((h4.exp).mul_const (‖p.1‖ ^ 2)).neg).add ((h4.neg.exp).mul_const (‖p.2‖ ^ 2))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- **`X` is a pseudo-gradient**: away from the critical point `f` decreases
strictly along the flow, since its derivative there is negative. -/
theorem deriv_modelFun_modelFlow_neg {p : E × F} (hp : p ≠ 0) (s : ℝ) :
    -(Real.exp (4 * s) * 4 * ‖p.1‖ ^ 2) + Real.exp (-(4 * s)) * -4 * ‖p.2‖ ^ 2 < 0 := by
  have e1 : (0 : ℝ) < Real.exp (4 * s) := Real.exp_pos _
  have e2 : (0 : ℝ) < Real.exp (-(4 * s)) := Real.exp_pos _
  have n1 : (0 : ℝ) ≤ ‖p.1‖ ^ 2 := sq_nonneg _
  have n2 : (0 : ℝ) ≤ ‖p.2‖ ^ 2 := sq_nonneg _
  have hcases : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    rcases eq_or_ne p.1 0 with h | h
    · rcases eq_or_ne p.2 0 with h' | h'
      · exact absurd (Prod.ext_iff.mpr ⟨h, h'⟩) hp
      · exact Or.inr h'
    · exact Or.inl h
  rcases hcases with h | h
  · have hpos : (0 : ℝ) < ‖p.1‖ ^ 2 := pow_pos (norm_pos_iff.mpr h) 2
    nlinarith [mul_pos e1 hpos, mul_nonneg e2.le n2]
  · have hpos : (0 : ℝ) < ‖p.2‖ ^ 2 := pow_pos (norm_pos_iff.mpr h) 2
    nlinarith [mul_pos e2 hpos, mul_nonneg e1.le n1]

/-- The map `Φ` of Lemma 3.2.11, from the upper to the lower boundary of the
Morse chart. -/
def modelTransition (p : E × F) : E × F :=
  ((‖p.2‖ / ‖p.1‖) • p.1, (‖p.1‖ / ‖p.2‖) • p.2)

/-- **Lemma 3.2.11.**  The embedding of `∂⁺U - S⁺` into `∂⁻U - S⁻` defined by
the flow of `X` is `Φ(x⁻,x⁺) = (‖x⁺‖/‖x⁻‖ · x⁻, ‖x⁻‖/‖x⁺‖ · x⁺)`: integrating
`X` shows that `Φ(p)` is the point `φₛ(p)` for `s = ½ log(‖x⁺‖/‖x⁻‖)`. -/
theorem modelFlow_log_eq_modelTransition {p : E × F} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) :
    modelFlow (Real.log (‖p.2‖ / ‖p.1‖) / 2) p = modelTransition p := by
  have hr : (0 : ℝ) < ‖p.2‖ / ‖p.1‖ := div_pos (norm_pos_iff.mpr h2) (norm_pos_iff.mpr h1)
  have harg : (2 : ℝ) * (Real.log (‖p.2‖ / ‖p.1‖) / 2) = Real.log (‖p.2‖ / ‖p.1‖) := by ring
  have e1 : Real.exp (2 * (Real.log (‖p.2‖ / ‖p.1‖) / 2)) = ‖p.2‖ / ‖p.1‖ := by
    rw [harg, Real.exp_log hr]
  have e2 : Real.exp (-(2 * (Real.log (‖p.2‖ / ‖p.1‖) / 2))) = ‖p.1‖ / ‖p.2‖ := by
    rw [harg, Real.exp_neg, Real.exp_log hr, inv_div]
  simp only [modelFlow, modelTransition, e1, e2]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The time at which the flow realises `Φ` is positive: on `∂⁺U` one has
`‖x⁻‖ < ‖x⁺‖`, so `Φ(p)` is reached in the future (§3.2.c). -/
theorem modelFlow_log_time_pos {p : E × F} (h1 : p.1 ≠ 0) (hlt : ‖p.1‖ < ‖p.2‖) :
    0 < Real.log (‖p.2‖ / ‖p.1‖) / 2 := by
  have h1' : (0 : ℝ) < ‖p.1‖ := norm_pos_iff.mpr h1
  have hone : (1 : ℝ) < ‖p.2‖ / ‖p.1‖ := (one_lt_div h1').mpr hlt
  exact div_pos (Real.log_pos hone) (by norm_num)

/-- `Φ` exchanges the two ends of the Morse chart: it maps the level `f = ε` to
the level `f = -ε` (§3.2.c). -/
theorem modelFun_modelTransition {p : E × F} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) :
    modelFun (modelTransition p) = -modelFun p := by
  have h1' : (0 : ℝ) < ‖p.1‖ := norm_pos_iff.mpr h1
  have h2' : (0 : ℝ) < ‖p.2‖ := norm_pos_iff.mpr h2
  have h1n : ‖p.1‖ ≠ 0 := ne_of_gt h1'
  have h2n : ‖p.2‖ ≠ 0 := ne_of_gt h2'
  have hr : (0 : ℝ) < ‖p.2‖ / ‖p.1‖ := div_pos h2' h1'
  have hr' : (0 : ℝ) < ‖p.1‖ / ‖p.2‖ := div_pos h1' h2'
  have n1 : ‖(‖p.2‖ / ‖p.1‖) • p.1‖ = ‖p.2‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    field_simp
  have n2 : ‖(‖p.1‖ / ‖p.2‖) • p.2‖ = ‖p.1‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr']
    field_simp
  simp only [modelFun, modelTransition, n1, n2]
  ring

end

end MorseModel

end Chapter3
end MorseFloer
