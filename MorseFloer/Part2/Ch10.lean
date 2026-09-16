import MorseFloer.Part1.Ch3
import MorseFloer.Part2.Ch16

/-!
# Chapter 10: From Floer to Morse

Formalization of Chapter 10 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 325–346).

The chapter is the bridge that turns Floer homology into Morse homology, and so
finishes the proof of the Arnold conjecture.  Its claim is that for a
nondegenerate time-independent Hamiltonian which is small in the `C²` topology,
the Floer complex `CF⋆(H, J)` and the Morse complex `CM⋆(H, J)` of the same
function coincide up to a shift of the grading by `n`:

* **§10.1** collects the statements.  Theorem 10.1.1 is the comparison of the
  two complexes; Theorem 10.1.2 is the genericity of the almost complex
  structures for which `−J X_H` is Morse–Smale; Theorem 10.1.3 says the operator
  `L_u` obtained by linearising the flow of a pseudo-gradient along a trajectory
  from `x` to `y` is Fredholm of index `Ind(x) − Ind(y)`; Corollary 10.1.4
  deduces that `L_u` and the linearised Floer operator `(dF)_u` have the same
  index; Theorem 10.1.5 characterises the Smale condition by the surjectivity of
  all the `L_u`; Proposition 10.1.7 identifies the two kernels, Corollary 10.1.8
  deduces surjectivity of `(dF)_u`, and Proposition 10.1.9 says that after
  replacing `H` by `H/k` for large `k` every Floer trajectory joining critical
  points with an index gap of at most two is independent of the loop parameter.
* **§10.2** proves Theorem 10.1.3.  The flow equation is linearised into
  `L_u Y = dY/ds + A(s) Y` with `A(s)` tending to the Hessians of `f` at the two
  critical points (§10.2.a); solutions in `W^{1,2}` decay exponentially
  (§10.2.b); the elliptic estimate of Proposition 10.2.3, built from Lemmas
  10.2.4 and 10.2.5, makes `L_u` Fredholm (§10.2.c); the index is computed from
  the resolvent (§10.2.d); and the Smale condition is read off the cokernel
  (§10.2.e).

## Relation to the rest of Part II

Chapters 6, 8 and 9 are not imported: the Floer equation, the linearised Floer
operator `(dF)_u`, the moduli spaces `M(x,y)` and the gluing theorem are taken
here as **explicit hypotheses or abstract parameters**, exactly as Chapter 3
takes the count of trajectories as an abstract `cnt` together with the
hypothesis `BrokenPairs`.  A later pass will connect them to Chapter 6.  The
abstract inputs are, precisely:

* an abstract count function `cntF` for the Floer complex and an abstract
  grading `indF` (the Maslov index `μ`), with the hypothesis `indM = indF + n`
  coming from Proposition 7.2.1 and Remark 5.4.6, and the hypothesis
  `cntF = cntM` which is the geometric conclusion of §10.4;
* abstract Banach spaces standing for `W^{1,2}(ℝ;ℝⁿ)` and `L²(ℝ;ℝⁿ)` and
  abstract continuous linear maps standing for `L_u` and `(dF)_u`, with the
  predicate `IsFredholmOfIndex` recording Theorem 10.1.3 and the Chapter 8 index
  formula as data rather than as provable statements;
* for the index computation, the tangent spaces `T_{u(σ)}W^u(x)` and
  `T_{u(σ)}W^s(y)` as abstract subspaces of a finite-dimensional inner product
  space, with their dimensions as hypotheses (Proposition 2.1.5 is not
  statable).

## What is proved here

* **Theorem 10.1.1**, in its algebraic form: the shift of gradings `critShift`
  and `chainShift`, a complete proof that it intertwines the two differentials
  (`chainShift_dLin`), transports the broken-trajectory hypothesis
  (`brokenPairs_shift`) and matches cycles with cycles and boundaries with
  boundaries (`chainShift_cycles`, `chainShift_boundaries`).  In the ungraded
  case the two complexes and their homologies are literally equal
  (`floerComplex_eq_morseComplex`, `floerHomology_eq_morseHomology`).
* **Corollary 10.1.4**: equality of the two Fredholm indices, proved from
  Theorem 10.1.3, from the index formula for `(dF)_u` and from the shift
  `Ind = μ + n`.
* **Corollary 10.1.8**, at the level of dimensions: equal kernels plus equal
  indices force equal cokernels, so surjectivity of `L_u` gives surjectivity of
  `(dF)_u`.
* **Remark 10.1.6** and the easy inclusion `Ker L_u ⊆ Ker (dF)_u` of §10.4.a,
  pointwise.
* **§10.2.a**: the operator `linOp`, and the Leibniz rule
  `L_u(αY) = α' Y + α L_u Y` which drives the cut-off argument of Proposition
  10.2.3.
* **§10.2.b**: the exponential decay, in the model in which the book proves it.
  In a Morse chart `A` is a constant diagonal matrix, so the system splits into
  the scalar equations `y' = −λ y`; the solution formula `y(s) = y(0)e^{−λ s}`
  is proved outright, the exponential decay at `−∞` is read off it, and it is
  proved that a solution which stays bounded near `−∞` with `λ > 0` vanishes —
  which is the book's reason why membership in `W^{1,2}` forces exponential
  decay.
* **Lemma 10.2.4**: the linear-algebra core is proved in full.  For a symmetric
  `B` bounded below by `C₀ > 0` and any `u ∈ ℝ`, `(u² + C₀²)‖v‖² ≤ ‖(iu + B)v‖²`
  on the Fourier side, written without complexifying as an inequality about the
  real and imaginary parts; together with the scalar inequality
  `1 + u² ≤ C₁(C₀² + u²)`, `C₁ = max(1, C₀^{-2})`, this is exactly the book's
  argument.  Only the passage through Plancherel is assumed.
* **Lemma 10.2.5**: proved in full, both pointwise and after integration.  The
  algebraic ingredient `½‖x‖² − ‖y‖² ≤ ‖x + y‖²` is proved by expanding
  `‖x + 2y‖² ≥ 0`, as in the book.
* **§10.2.d**: the index computation, as pure linear algebra.  With
  `Ker L_u ≅ T W^u(x) ∩ T W^s(y)` and `Ker L*_u ≅ (T W^u(x) + T W^s(y))^⊥`, the
  index is `dim W^u(x) + dim W^s(y) − n = Ind(x) − Ind(y)`; this is proved from
  the dimension formula for a sum and an intersection.
* **§10.2.e, Theorem 10.1.5**: the transversality `T W^u(x) + T W^s(y) = T V` is
  equivalent to the vanishing of the orthogonal complement, hence to the
  surjectivity of `L_u`.  Proved.
* **§10.4.b, Proposition 10.1.9**: the key step is proved in full.  If a
  sequence of functions of the loop parameter is periodic with period tending to
  zero and converges uniformly, the limit is constant in that parameter.
* **Lemma 10.2.6**: the pointwise duality identity
  `⟪L_u Y, Z⟫ − ⟪Y, L*_u Z⟫ = d/ds ⟪Y, Z⟫`, which is the integration by parts
  of the book's proof, is proved.
* **Lemma 10.3.5**, in the form the proof of Theorem 10.1.2 uses it: a symmetric
  `S` with `S U = V` has `⟪U, S V⟫ = ‖V‖² ≠ 0`.
* **Proposition 10.2.2** (the Fredholm property of `L_u`) is stated for abstract
  Banach spaces, from the estimate of Proposition 10.2.3 with the local term
  factored through a compact operator and a finite-dimensional cokernel, and
  *proved*, by the argument of Proposition 8.7.4: Riesz's theorem for the
  kernel, Hahn–Banach for its complement, and the open mapping theorem for the
  closed range and the invertible restriction.

## Omitted

Nothing in this chapter is assumed.

* **Theorem 10.1.3** is recorded as the predicate `IsFredholmOfIndex`, not as a
  theorem: the operator `L_u` lives on `W^{1,2}(ℝ;ℝⁿ)`, which Mathlib does not
  have, so there is nothing to quantify over and no honest statement to prove.
  Corollaries 10.1.4 and 10.1.8 take it as a hypothesis, in the style of
  Chapter 3's `BrokenPairs`.
* **Proposition 10.2.3** and **Lemma 10.2.4** are stated with explicit
  integrals — a pair `(Y, Y')` standing for a function and its derivative, since
  there is no `W^{1,2}` — and both are *proved*.  Lemma 10.2.4 is proved
  without the Plancherel theorem the book uses: the cross term `2⟪Y', BY⟫` is
  the derivative of `⟪Y, BY⟫`, which is integrable with integrable derivative
  and so integrates to zero.  Proposition 10.2.3 is the book's cut-off argument,
  with the `C¹` partition of unity built from Mathlib's `Real.smoothTransition`.
* **Lemma 10.4.1** (a differentiable function of mean zero on `[0,1]` has
  `∫‖f‖^p ≤ ∫‖f'‖^p`) is *proved*, by the book's estimate and Jensen's
  inequality; two hypotheses missing from the earlier statement (completeness
  of the target and integrability of `‖f'‖^p`) had to be added, see its
  docstring.
* **Theorem 10.1.2** (density of the regular almost complex structures) and all
  of **§10.3** carry no Lean statement.  They speak about the space `J_c(ω)` of
  calibrated almost complex structures on a symplectic manifold, its Banach
  manifold structure, the space `Z(x,y,H)` of pairs (trajectory, structure), the
  `C^∞_ε` norms and the Sard–Smale theorem; Mathlib has no symplectic manifolds,
  no space of sections with a `C^∞_ε` norm and no Sard theorem, so none of
  Lemma 10.3.1, Proposition 10.3.2, Proposition 10.3.3, Lemma 10.3.4 or Lemma
  10.3.6 can be stated.  The one exception is the elementary linear-algebra
  content of Lemma 10.3.5, proved below.
* **Proposition 10.1.7** is not stated as a whole: `(dF)_u` and its kernel live
  on spaces of maps `ℝ × S¹ → W` that Mathlib cannot carry.  Its two ends are
  here: the easy inclusion, pointwise, and the final step — `a ≤ b ≤ c·a` with
  `c < 1` forces `a = 0`.
* **Corollary 10.2.7** is the specialisation of Proposition 10.2.2 to every
  trajectory of a Morse function and adds nothing formalizable.
* **Remarks 10.2.1 and 10.2.9** are commentary on objects (the tangent space to
  a space of trajectories, the metric underlying a gradient) that do not exist
  here.
-/

open Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace MorseFloer
namespace Chapter10

/-! ## §10.1 The statements: comparing the two complexes

The Floer complex `CF⋆(H, J)` and the Morse complex `CM⋆(H, J)` are both built,
by the recipe of Chapter 3, out of a grading of the set of critical points and a
count of connecting trajectories.  Following the house style, the two gradings
`indF` (the Maslov index `μ` of the constant periodic orbit) and `indM` (the
Morse index of the critical point) and the two counts `cntF` and `cntM` are
abstract data, and the two geometric inputs of the chapter are hypotheses:

* `indM = indF + n`, which is Proposition 7.2.1 read through Remark 5.4.6 — the
  Hessian of a `C²`-small `H` has no eigenvalue in `2πℤ`;
* `cntF = cntM`, which is the conclusion of §10.4: for `k` large the Floer
  trajectories of `H/k` between critical points of index gap at most two are
  exactly the Morse trajectories (Proposition 10.1.9), and the linearised Floer
  operator is surjective along them (Corollary 10.1.8), so both counts are made
  on the same finite set.
-/

section Comparison

variable {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
  {indM indF : Crit → ℕ} {n : ℕ} {cntM cntF : Crit → Crit → R}

/-- The shift of gradings on critical points.  If every critical point has Morse
index `n` more than its Maslov degree, the critical points of Maslov degree `k`
are exactly those of Morse index `k + n`. -/
def critShift (h : ∀ c, indM c = indF c + n) (k m : ℕ) (hm : m = k + n) :
    Chapter3.CritSet indM m ≃ Chapter3.CritSet indF k where
  toFun b := ⟨b.1, by have h1 := h b.1; have h2 := b.2; omega⟩
  invFun a := ⟨a.1, by have h1 := h a.1; have h2 := a.2; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype Crit] in
@[simp]
theorem critShift_val (h : ∀ c, indM c = indF c + n) (k m : ℕ) (hm : m = k + n)
    (b : Chapter3.CritSet indM m) : (critShift h k m hm b).1 = b.1 := rfl

omit [Fintype Crit] in
@[simp]
theorem critShift_symm_val (h : ∀ c, indM c = indF c + n) (k m : ℕ) (hm : m = k + n)
    (a : Chapter3.CritSet indF k) : ((critShift h k m hm).symm a).1 = a.1 := rfl

/-- The induced isomorphism `CF_k ≅ CM_{k+n}` of chain groups: a chain is a
family of coefficients indexed by the critical points, and the two index sets
are identified by `critShift`. -/
def chainShift (h : ∀ c, indM c = indF c + n) (k m : ℕ) (hm : m = k + n) :
    Chapter3.Chains R indF k ≃ₗ[R] Chapter3.Chains R indM m where
  toFun x := fun b => x (critShift h k m hm b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := fun a => y ((critShift h k m hm).symm a)
  left_inv x := by funext a; simp
  right_inv y := by funext b; simp

omit [Fintype Crit] in
@[simp]
theorem chainShift_apply (h : ∀ c, indM c = indF c + n) (k m : ℕ) (hm : m = k + n)
    (x : Chapter3.Chains R indF k) (b : Chapter3.CritSet indM m) :
    chainShift h k m hm x b = x (critShift h k m hm b) := rfl

/-- **The shift intertwines the two differentials.**  This is the content of
Theorem 10.1.1 once the two geometric inputs are granted: the Floer differential
in degree `k` is the Morse differential in degree `k + n`, read through the
identification of the bases.  Complete proof. -/
theorem chainShift_dLin (h : ∀ c, indM c = indF c + n) (hc : cntF = cntM) (k : ℕ)
    (x : Chapter3.Chains R indF (k + 1)) :
    chainShift h k (k + n) rfl (Chapter3.dLin indF cntF k x)
      = Chapter3.dLin indM cntM (k + n)
          (chainShift h (k + 1) (k + n + 1) (by omega) x) := by
  funext b
  rw [chainShift_apply, Chapter3.dLin_apply, Chapter3.dLin_apply]
  refine Fintype.sum_equiv (critShift h (k + 1) (k + n + 1) (by omega)).symm _ _ ?_
  intro a
  subst hc
  rfl

/-- **The broken-trajectory hypothesis transports along the shift.**  If the
Floer counts satisfy it, so do the Morse counts: below degree `n` there is no
critical point of that Morse index at all, and in degree `j + n` the sum is the
Floer sum in degree `j` reindexed. -/
theorem brokenPairs_shift (h : ∀ c, indM c = indF c + n) (hc : cntF = cntM)
    (hF : Chapter3.BrokenPairs indF cntF) : Chapter3.BrokenPairs indM cntM := by
  intro k a b
  rcases Nat.lt_or_ge k n with hk | hk
  · exact absurd b.2 (by have := h b.1; omega)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + n := ⟨k - n, by omega⟩
    have key := hF j (critShift h (j + 2) (j + n + 2) (by omega) a)
      (critShift h j (j + n) (by omega) b)
    rw [hc] at key
    refine Eq.trans ?_ key
    exact Fintype.sum_equiv (critShift h (j + 1) (j + n + 1) (by omega)) _ _ fun _ => rfl

/-- Cycles correspond to cycles under the shift. -/
theorem chainShift_mem_cycles_iff (h : ∀ c, indM c = indF c + n) (hc : cntF = cntM) (k : ℕ)
    (y : Chapter3.Chains R indM (k + n + 1)) :
    (chainShift h (k + 1) (k + n + 1) (by omega)).symm y ∈ Chapter3.cycles indF cntF k
      ↔ y ∈ Chapter3.cycles indM cntM (k + n) := by
  have key : chainShift h k (k + n) rfl
      (Chapter3.dLin indF cntF k ((chainShift h (k + 1) (k + n + 1) (by omega)).symm y))
      = Chapter3.dLin indM cntM (k + n) y := by
    rw [chainShift_dLin h hc k, LinearEquiv.apply_symm_apply]
  simp only [Chapter3.cycles, LinearMap.mem_ker]
  constructor
  · intro hy
    rw [← key, hy, map_zero]
  · intro hy
    refine (chainShift h k (k + n) rfl).map_eq_zero_iff.mp ?_
    rw [key, hy]

/-- Boundaries correspond to boundaries under the shift. -/
theorem chainShift_mem_boundaries_iff (h : ∀ c, indM c = indF c + n) (hc : cntF = cntM)
    (k : ℕ) (y : Chapter3.Chains R indM (k + n)) :
    (chainShift h k (k + n) rfl).symm y ∈ Chapter3.boundaries indF cntF k
      ↔ y ∈ Chapter3.boundaries indM cntM (k + n) := by
  simp only [Chapter3.boundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨chainShift h (k + 1) (k + n + 1) (by omega) x, ?_⟩
    rw [← chainShift_dLin h hc k, hx, LinearEquiv.apply_symm_apply]
  · rintro ⟨z, hz⟩
    refine ⟨(chainShift h (k + 1) (k + n + 1) (by omega)).symm z, ?_⟩
    apply (chainShift h k (k + n) rfl).injective
    rw [chainShift_dLin h hc k, LinearEquiv.apply_symm_apply, hz,
      LinearEquiv.apply_symm_apply]

/-- **Theorem 10.1.1, the cycle half.**  The isomorphism of chain groups carries
the cycles of the Floer complex onto the cycles of the Morse complex. -/
theorem chainShift_cycles (h : ∀ c, indM c = indF c + n) (hc : cntF = cntM) (k : ℕ) :
    (Chapter3.cycles indF cntF k).map
        (chainShift h (k + 1) (k + n + 1) (by omega)).toLinearMap
      = Chapter3.cycles indM cntM (k + n) := by
  ext y
  simp only [Submodule.mem_map_equiv]
  exact chainShift_mem_cycles_iff h hc k y

/-- **Theorem 10.1.1, the boundary half.** -/
theorem chainShift_boundaries (h : ∀ c, indM c = indF c + n) (hc : cntF = cntM) (k : ℕ) :
    (Chapter3.boundaries indF cntF k).map (chainShift h k (k + n) rfl).toLinearMap
      = Chapter3.boundaries indM cntM (k + n) := by
  ext y
  simp only [Submodule.mem_map_equiv]
  exact chainShift_mem_boundaries_iff h hc k y

/-- **Theorem 10.1.1 with no shift of gradings.**  If the Floer and Morse data
agree on the nose, the two complexes are literally the same object of
`ChainComplex (ModuleCat R) ℕ`. -/
theorem floerComplex_eq_morseComplex (hind : indF = indM) (hcnt : cntF = cntM)
    {hF : Chapter3.BrokenPairs indF cntF} {hM : Chapter3.BrokenPairs indM cntM} :
    Chapter3.morseComplex hF = Chapter3.morseComplex hM := by
  subst hind
  subst hcnt
  rfl

/-- **Theorem 10.1.1, the conclusion.**  Floer homology is Morse homology. -/
theorem floerHomology_eq_morseHomology (hind : indF = indM) (hcnt : cntF = cntM)
    {hF : Chapter3.BrokenPairs indF cntF} {hM : Chapter3.BrokenPairs indM cntM} (k : ℕ) :
    Chapter3.morseHomology hF k = Chapter3.morseHomology hM k := by
  subst hind
  subst hcnt
  rfl

end Comparison

/-! ## §10.1 The two Fredholm operators

`L_u` and `(dF)_u` are operators between spaces of maps that Mathlib cannot
build (`W^{1,2}(ℝ;ℝⁿ)` and `L²(ℝ;ℝⁿ)`, and their two-variable analogues).  They
are therefore carried here as abstract continuous linear maps between abstract
Banach spaces, and the two index formulas — Theorem 10.1.3 for `L_u`, the
Chapter 8 computation for `(dF)_u` — as the *data* `IsFredholmOfIndex`, in the
style of Chapter 3's `BrokenPairs`.  What is then genuinely proved is what the
book deduces from them: Corollary 10.1.4 and Corollary 10.1.8. -/

section Indices

variable {W L2 W' L2' : Type*}
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup L2] [NormedSpace ℝ L2]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [NormedAddCommGroup L2'] [NormedSpace ℝ L2']

/-- **Theorem 10.1.3, as data.**  "`u` joins the critical points `x` and `y`, of
indices `ix` and `iy`, and the linearised operator `Lu` is Fredholm of index
`ix − iy`".

This is not stated as a theorem, because the operator it speaks about is built
on `W^{1,2}(ℝ;ℝⁿ)`, which Mathlib cannot form; quantifying over an arbitrary
continuous linear map would give a false statement.  The two ingredients of its
proof are supplied below: the Fredholm property is Proposition 10.2.2, and the
index is Proposition 10.2.8, whose linear algebra is proved in
`finrank_index_eq`. -/
def IsFredholmOfIndex (Lu : W →L[ℝ] L2) (ix iy : ℕ) : Prop :=
  ContinuousLinearMap.IsFredholm Lu ∧ Chapter16.fredholmIndex Lu = (ix : ℤ) - (iy : ℤ)

/-- **Corollary 10.1.4.**  For a nondegenerate Hamiltonian `H` and a trajectory
`u` of `−J X_H`, the Fredholm operators `(dF)_u` and `L_u` have the same index.

Complete proof: Theorem 10.1.3 gives `ind L_u = Ind(x) − Ind(y)`, Chapter 8
gives `ind (dF)_u = μ(x) − μ(y)`, and the two gradings differ by the constant
`n` (Proposition 7.2.1). -/
theorem cor_10_1_4 {Lu : W →L[ℝ] L2} {dFu : W' →L[ℝ] L2'} {ix iy μx μy n : ℕ}
    (hL : IsFredholmOfIndex Lu ix iy) (hF : IsFredholmOfIndex dFu μx μy)
    (hx : ix = μx + n) (hy : iy = μy + n) :
    Chapter16.fredholmIndex Lu = Chapter16.fredholmIndex dFu := by
  rw [hL.2, hF.2]
  omega

/-- **Corollary 10.1.8.**  Along every trajectory of the gradient of `H` the
Fredholm operator `(dF)_u` is surjective.

Proved at the level of dimensions, which is exactly the book's argument:
Proposition 10.1.7 makes the two kernels equal, Corollary 10.1.4 makes the two
indices equal, hence the two cokernels have the same dimension; and `L_u` is
surjective by Theorem 10.1.5, because the field is Morse–Smale. -/
theorem cor_10_1_8 (Lu : W →L[ℝ] L2) (dFu : W' →L[ℝ] L2')
    (hker : Module.finrank ℝ (LinearMap.ker (Lu : W →ₗ[ℝ] L2))
      = Module.finrank ℝ (LinearMap.ker (dFu : W' →ₗ[ℝ] L2')))
    (hind : Chapter16.fredholmIndex Lu = Chapter16.fredholmIndex dFu)
    (hsurj : Module.finrank ℝ (L2 ⧸ LinearMap.range (Lu : W →ₗ[ℝ] L2)) = 0) :
    Module.finrank ℝ (L2' ⧸ LinearMap.range (dFu : W' →ₗ[ℝ] L2')) = 0 := by
  simp only [Chapter16.fredholmIndex] at hind
  omega

end Indices

/-! ## Remark 10.1.6, and the easy half of §10.4.a

The Floer equation is `∂u/∂s + J(u)∂u/∂t + grad H(u) = 0`.  A solution which
does not depend on the loop parameter has `∂u/∂t = 0`, and the equation
collapses to the equation `du/ds + grad H(u) = 0` of the trajectories of
`X = −grad H`.  The same one-line computation is the inclusion
`Ker L_u ⊆ Ker (dF)_u` at the start of §10.4.a.  Only the pointwise identity is
formalizable; the equations themselves belong to Chapter 6. -/

section Remark

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Remark 10.1.6.**  Written pointwise: if the `t`-derivative vanishes, the
Floer equation `a + J b + g = 0` reduces to the gradient equation `a + g = 0`.
The same identity, applied to a solution `Y` of `dY/ds + S(s)Y = 0`, gives the
inclusion `Ker L_u ⊆ Ker (dF)_u` of §10.4.a. -/
theorem floer_eq_gradient_of_t_independent (J : E →L[ℝ] E) (a b g : E) (hb : b = 0) :
    a + J b + g = 0 ↔ a + g = 0 := by
  rw [hb, map_zero, add_zero]

/-- **The final step of Proposition 10.1.7.**  The proof ends with an inequality
`‖Y‖² ≤ ‖grad Y‖² ≤ (sup‖S‖)²‖Y‖²`; when `H` is `C²`-small the constant is less
than one and `Y` must vanish. -/
theorem eq_zero_of_lt_one_bound {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c * a)
    (hc : c < 1) : a = 0 := by
  rcases ha.lt_or_eq with h | h
  · exfalso
    nlinarith [mul_pos (sub_pos.mpr hc) h]
  · exact h.symm

end Remark

/-! ## §10.2.a The linearisation of the flow of a pseudo-gradient

Along a trajectory `u` of `X`, in an orthonormal trivialisation of `TV` chosen
constant near the two ends, the linearised flow equation reads

`L_u Y = dY/ds + A(s) Y`,

with `A(s) → Hess_x f` as `s → −∞` and `A(s) → Hess_y f` as `s → +∞`, both
symmetric and — the critical points being nondegenerate — invertible.

Mathlib has no `W^{1,2}(ℝ;ℝⁿ)`, so a "function together with its derivative" is
recorded here as a pair `(Y, Y')` with `∀ s, HasDerivAt Y (Y' s) s`.  The
operator itself is the pointwise expression `linOp`. -/

section Linearisation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The linearised operator `L_u`** of §10.2.a, written pointwise:
`L_u Y = dY/ds + A(s)Y`. -/
def linOp (A : ℝ → E →L[ℝ] E) (Y Y' : ℝ → E) : ℝ → E := fun s => Y' s + A s (Y s)

/-- **The formal adjoint `L*_u`** of Lemma 10.2.6: `L*_u Z = −dZ/ds + A*(s)Z`. -/
def adjOp (Aadj : ℝ → E →L[ℝ] E) (Z Z' : ℝ → E) : ℝ → E := fun s => -Z' s + Aadj s (Z s)

/-- **The Leibniz rule `L_u(αY) = (dα/ds)Y + α L_u Y`** used in the cut-off
argument of Proposition 10.2.3.  Complete proof. -/
theorem linOp_smul (A : ℝ → E →L[ℝ] E) (Y Y' : ℝ → E) (α α' : ℝ → ℝ) (s : ℝ) :
    linOp A (fun t => α t • Y t) (fun t => α' t • Y t + α t • Y' t) s
      = α' s • Y s + α s • linOp A Y Y' s := by
  simp only [linOp, ContinuousLinearMap.map_smul, smul_add, add_assoc]

/-- The data of §10.2.a: the coefficient `A(s)` of the linearised equation is
continuous and converges at both ends to the Hessians of `f` at the two critical
points, which are symmetric and invertible because the points are
nondegenerate. -/
structure IsLinearisationData (A : ℝ → E →L[ℝ] E) (Bx By : E →L[ℝ] E) : Prop where
  /-- `s ↦ A(s)` is continuous. -/
  continuous : Continuous A
  /-- `A(s) → Hess_x f` as `s → −∞`. -/
  tendsto_atBot : Tendsto A atBot (𝓝 Bx)
  /-- `A(s) → Hess_y f` as `s → +∞`. -/
  tendsto_atTop : Tendsto A atTop (𝓝 By)
  /-- The Hessian at `x` is symmetric. -/
  symm_atBot : ∀ v w, ⟪Bx v, w⟫ = ⟪v, Bx w⟫
  /-- The Hessian at `y` is symmetric. -/
  symm_atTop : ∀ v w, ⟪By v, w⟫ = ⟪v, By w⟫
  /-- The critical point `x` is nondegenerate. -/
  invertible_atBot : ∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖Bx v‖
  /-- The critical point `y` is nondegenerate. -/
  invertible_atTop : ∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖By v‖

end Linearisation

/-! ## §10.2.b Exponential decay of the solutions

Near a critical point the book works in a Morse chart, where the trivialisation
can be chosen so that `A` is a constant diagonal matrix; the system splits into
the scalar equations `dy_i/ds = −λ_i y_i`, whose solutions are
`y_i(s) = y_i(0)e^{−λ_i s}`.  Such a vector lies in `W^{1,2}` only if it tends
to `0` at the relevant end, and then it does so exponentially.  All three
statements are proved. -/

section Decay

/-- **The solution of the scalar equation `y' = −λ y`.**  Complete proof: the
function `y(s)e^{λ s}` has vanishing derivative, hence is constant. -/
theorem eq_exp_of_hasDerivAt_neg_mul {y : ℝ → ℝ} {lam : ℝ}
    (hy : ∀ s, HasDerivAt y (-(lam * y s)) s) (s : ℝ) :
    y s = y 0 * Real.exp (-(lam * s)) := by
  have hexp : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (lam * t))
      (Real.exp (lam * t) * lam) t := by
    intro t
    have h : HasDerivAt (fun t : ℝ => lam * t) lam t := by
      simpa using (hasDerivAt_id t).const_mul lam
    exact h.exp
  have hgd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y t * Real.exp (lam * t)) 0 t := by
    intro t
    have hzero : (0 : ℝ)
        = -(lam * y t) * Real.exp (lam * t) + y t * (Real.exp (lam * t) * lam) := by
      ring
    rw [hzero]
    exact (hy t).mul (hexp t)
  have hconst : ∀ t : ℝ, y t * Real.exp (lam * t) = y 0 * Real.exp (lam * 0) :=
    fun t => is_const_of_deriv_eq_zero (fun x => (hgd x).differentiableAt)
      (fun x => (hgd x).deriv) t 0
  have h0 := hconst s
  rw [mul_zero, Real.exp_zero, mul_one] at h0
  have hne : Real.exp (lam * s) ≠ 0 := Real.exp_ne_zero _
  have hstep : y s * Real.exp (lam * s) * (Real.exp (lam * s))⁻¹ = y s := by
    rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  calc y s = y s * Real.exp (lam * s) * (Real.exp (lam * s))⁻¹ := hstep.symm
    _ = y 0 * (Real.exp (lam * s))⁻¹ := by rw [h0]
    _ = y 0 * Real.exp (-(lam * s)) := by rw [Real.exp_neg]

/-- **Exponential decay at `−∞`.**  For `s ≤ 0` the solution satisfies
`|y(s)| = |y(0)|e^{λ|s|}`; when `λ < 0` this decays exponentially as
`s → −∞`. -/
theorem abs_eq_exp_decay_atBot {y : ℝ → ℝ} {lam : ℝ}
    (hy : ∀ s, HasDerivAt y (-(lam * y s)) s) {s : ℝ} (hs : s ≤ 0) :
    |y s| = |y 0| * Real.exp (lam * |s|) := by
  rw [eq_exp_of_hasDerivAt_neg_mul hy s, abs_mul, Real.abs_exp, abs_of_nonpos hs,
    show lam * -s = -(lam * s) from by ring]

/-- **Membership in `W^{1,2}` forces the decay.**  A solution of `y' = −λ y` with
`λ > 0` which stays bounded near `−∞` is identically zero: the alternative grows
like `e^{−λ s}`, which is unbounded there.  This is the book's reason why the
`W^{1,2}` solutions must decay exponentially at each end. -/
theorem eq_zero_of_bddAtBot {y : ℝ → ℝ} {lam M : ℝ} (hlam : 0 < lam)
    (hy : ∀ s, HasDerivAt y (-(lam * y s)) s) (hb : ∀ s ≤ (0 : ℝ), |y s| ≤ M) :
    y 0 = 0 := by
  by_contra h0
  have hlne : lam ≠ 0 := ne_of_gt hlam
  have hpos : 0 < |y 0| := abs_pos.mpr h0
  set c : ℝ := |M| / |y 0| + 1 with hcdef
  have hcpos : 0 < c := by
    have hq : 0 ≤ |M| / |y 0| := div_nonneg (abs_nonneg M) hpos.le
    rw [hcdef]
    linarith
  set s : ℝ := -c / lam with hsdef
  have hs0 : s ≤ 0 := by
    have hq : 0 < c / lam := div_pos hcpos hlam
    rw [hsdef, neg_div]
    linarith
  have hls : -(lam * s) = c := by
    have hq : lam * s = -c := by
      rw [hsdef]
      field_simp
    rw [hq, neg_neg]
  have hexp : |M| / |y 0| < Real.exp c := by
    have h1 : c + 1 ≤ Real.exp c := Real.add_one_le_exp c
    rw [hcdef] at h1 ⊢
    linarith
  have hgt : M < |y 0| * Real.exp c := by
    have h2 : |y 0| * (|M| / |y 0|) < |y 0| * Real.exp c :=
      mul_lt_mul_of_pos_left hexp hpos
    have h3 : |y 0| * (|M| / |y 0|) = |M| := by
      field_simp
    have h4 : M ≤ |M| := le_abs_self M
    linarith
  have heq : |y s| = |y 0| * Real.exp c := by
    rw [eq_exp_of_hasDerivAt_neg_mul hy s, abs_mul, Real.abs_exp, hls]
  have hle := hb s hs0
  rw [heq] at hle
  linarith

end Decay

/-! ## §10.2.c The Fredholm property

The two lemmas on which Proposition 10.2.3 rests are proved here.

Lemma 10.2.4 concerns a constant invertible coefficient.  The book solves
`dY/ds + BY = Z` by the Fourier transform: `Ẑ(iu) = (iu + B)Ŷ(iu)`, and for `B`
real symmetric and invertible, `‖(iu + B)v‖² ≥ (u² + C₀²)‖v‖²`; then
`1 + u² ≤ C₁(C₀² + u²)` with `C₁ = max(1, C₀^{-2})` finishes the proof.  Both
inequalities are proved below without complexifying: a complex vector is written
as a pair `(a, b)` of real vectors and multiplication by `iu` is
`(a, b) ↦ (−u b, u a)`.

Lemma 10.2.5 concerns a bounded coefficient on a bounded interval and is proved
in full. -/

section Fredholm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖c • v‖² = c²‖v‖²`. -/
private theorem norm_smul_sq (c : ℝ) (v : E) : ‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- **The heart of Lemma 10.2.4.**  Let `B` be symmetric and bounded below by
`C₀ ≥ 0`, so invertible when `C₀ > 0`.  Writing a complex vector as a pair
`(a, b)` of real vectors, multiplication by `iu` is `(a, b) ↦ (−u b, u a)`, and
the estimate `‖(iu + B)v‖² ≥ (u² + C₀²)‖v‖²` becomes the inequality proved here.
The cross terms cancel exactly because `B` is symmetric — which it is, being a
Hessian.  Complete proof. -/
theorem inner_estimate_of_symm {B : E →L[ℝ] E} (hB : ∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫)
    {C₀ : ℝ} (hC₀ : ∀ v, C₀ * ‖v‖ ≤ ‖B v‖) (hC₀0 : 0 ≤ C₀) (u : ℝ) (a b : E) :
    (u ^ 2 + C₀ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ ‖B a - u • b‖ ^ 2 + ‖B b + u • a‖ ^ 2 := by
  have hcross : ⟪B b, a⟫ = ⟪B a, b⟫ := by rw [hB b a, real_inner_comm]
  have h1 : ‖B a - u • b‖ ^ 2
      = ‖B a‖ ^ 2 - 2 * (u * ⟪B a, b⟫) + u ^ 2 * ‖b‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul_sq]
  have h2 : ‖B b + u • a‖ ^ 2
      = ‖B b‖ ^ 2 + 2 * (u * ⟪B b, a⟫) + u ^ 2 * ‖a‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul_sq]
  have hBa : C₀ ^ 2 * ‖a‖ ^ 2 ≤ ‖B a‖ ^ 2 := by
    have hn : 0 ≤ C₀ * ‖a‖ := mul_nonneg hC₀0 (norm_nonneg a)
    have hq := mul_self_le_mul_self hn (hC₀ a)
    nlinarith [hq]
  have hBb : C₀ ^ 2 * ‖b‖ ^ 2 ≤ ‖B b‖ ^ 2 := by
    have hn : 0 ≤ C₀ * ‖b‖ := mul_nonneg hC₀0 (norm_nonneg b)
    have hq := mul_self_le_mul_self hn (hC₀ b)
    nlinarith [hq]
  rw [h1, h2, hcross]
  nlinarith [hBa, hBb]

/-- **The scalar step of Lemma 10.2.4**: with `C₁ = max(1, C₀^{-2})` one has
`1 + u² ≤ C₁(C₀² + u²)` for every `u`, which is what turns the estimate on the
symbol into the `W^{1,2}` estimate.  Complete proof. -/
theorem one_add_sq_le_max_mul {C₀ : ℝ} (hC₀ : 0 < C₀) (u : ℝ) :
    1 + u ^ 2 ≤ max 1 (1 / C₀ ^ 2) * (C₀ ^ 2 + u ^ 2) := by
  have hsq : (0 : ℝ) < C₀ ^ 2 := pow_pos hC₀ 2
  have h1 : (1 : ℝ) ≤ max 1 (1 / C₀ ^ 2) := le_max_left _ _
  have h2 : 1 / C₀ ^ 2 ≤ max 1 (1 / C₀ ^ 2) := le_max_right _ _
  have key : (1 : ℝ) ≤ max 1 (1 / C₀ ^ 2) * C₀ ^ 2 := by
    have hq := mul_le_mul_of_nonneg_right h2 hsq.le
    have hid : 1 / C₀ ^ 2 * C₀ ^ 2 = 1 := by field_simp
    linarith [hq, hid]
  nlinarith [sq_nonneg u]

/-- **Lemma 10.2.4, the estimate on the Fourier symbol.**  Combining the two
previous lemmas: for a symmetric `B` bounded below by `C₀ > 0` and
`C₁ = max(1, C₀^{-2})`,

`(1 + u²)‖Ŷ(iu)‖² ≤ C₁‖Ẑ(iu)‖²`,   `Ẑ = (iu + B)Ŷ`.

Integrating in `u` and applying Plancherel is Lemma 10.2.4.  Complete proof of
the symbol estimate. -/
theorem lemma_10_2_4_symbol {B : E →L[ℝ] E} (hB : ∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫)
    {C₀ : ℝ} (hC₀pos : 0 < C₀) (hC₀ : ∀ v, C₀ * ‖v‖ ≤ ‖B v‖) (u : ℝ) (a b : E) :
    (1 + u ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2)
      ≤ max 1 (1 / C₀ ^ 2) * (‖B a - u • b‖ ^ 2 + ‖B b + u • a‖ ^ 2) := by
  have h1 := one_add_sq_le_max_mul hC₀pos u
  have h2 := inner_estimate_of_symm hB hC₀ hC₀pos.le u a b
  have hnn : (0 : ℝ) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by positivity
  have hC1 : (0 : ℝ) ≤ max 1 (1 / C₀ ^ 2) := le_trans zero_le_one (le_max_left _ _)
  calc (1 + u ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2)
      ≤ max 1 (1 / C₀ ^ 2) * (C₀ ^ 2 + u ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hnn
    _ = max 1 (1 / C₀ ^ 2) * ((u ^ 2 + C₀ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2)) := by ring
    _ ≤ max 1 (1 / C₀ ^ 2) * (‖B a - u • b‖ ^ 2 + ‖B b + u • a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hC1

/-- The `W^{1,2}` norm squared of a pair "function, derivative", written out as
an integral: Mathlib has no Sobolev space on `ℝ`, so a `W^{1,2}` element is
recorded as a pair `(Y, Y')` with `∀ s, HasDerivAt Y (Y' s) s`. -/
noncomputable def sobolevSq (Y Y' : ℝ → E) : ℝ := ∫ s, (‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2)

/-- The `L²` norm squared. -/
noncomputable def l2Sq (Z : ℝ → E) : ℝ := ∫ s, ‖Z s‖ ^ 2

/-- The `L²` norm squared on `[−T, T]`. -/
noncomputable def l2SqOn (Z : ℝ → E) (T : ℝ) : ℝ := ∫ s in Set.Icc (-T) T, ‖Z s‖ ^ 2

/-- The derivative of a differentiable map `ℝ → E` is strongly measurable, as the
pointwise limit of the continuous difference quotients `n (Y(s + 1/n) − Y(s))`.
(Mathlib's `stronglyMeasurable_deriv` asks for completeness of `E`, which is not
assumed in this section.) -/
theorem stronglyMeasurable_of_hasDerivAt {Y Y' : ℝ → E} (hY : ∀ s, HasDerivAt Y (Y' s) s) :
    StronglyMeasurable Y' := by
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hY s).continuousAt
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun n : ℕ => fun s => (1 / ((n : ℝ) + 1))⁻¹ • (Y (s + 1 / ((n : ℝ) + 1)) - Y s))
    (fun n => ?_) ?_
  · exact (((hYc.comp (continuous_add_const _)).sub hYc).const_smul _).stronglyMeasurable
  · rw [tendsto_pi_nhds]
    intro s
    have h := hasDerivAt_iff_tendsto_slope_zero.mp (hY s)
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Filter.Eventually.of_forall fun n => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity⟩
    exact h.comp h2

omit [InnerProductSpace ℝ E] in
/-- A function `ℝ → E` whose squared norm is dominated by an integrable function is
square-integrable. -/
theorem integrable_sq_norm_of_le {f : ℝ → E} {g : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : Integrable g) (h : ∀ s, ‖f s‖ ^ 2 ≤ g s) : Integrable fun s => ‖f s‖ ^ 2 :=
  hg.mono' (hf.norm.pow 2) (Filter.Eventually.of_forall fun s => by
    rw [Real.norm_of_nonneg (by positivity)]; exact h s)

omit [InnerProductSpace ℝ E] in
/-- The same for a sum of two squared norms. -/
theorem integrable_add_sq_norm_of_le {f f' : ℝ → E} {g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f volume) (hf' : AEStronglyMeasurable f' volume)
    (hg : Integrable g) (h : ∀ s, ‖f s‖ ^ 2 + ‖f' s‖ ^ 2 ≤ g s) :
    Integrable fun s => ‖f s‖ ^ 2 + ‖f' s‖ ^ 2 :=
  hg.mono' ((hf.norm.pow 2).add (hf'.norm.pow 2)) (Filter.Eventually.of_forall fun s => by
    rw [Real.norm_of_nonneg (by positivity)]; exact h s)

omit [InnerProductSpace ℝ E] in
theorem norm_add_sq_le_two (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

omit [InnerProductSpace ℝ E] in
theorem norm_add3_sq_le (a b c : E) : ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  have h3 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith
  have h4 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- An integrable function on `ℝ` which has a limit at `+∞` has limit `0`:
otherwise it is bounded below in absolute value on some `(R, ∞)`, which has
infinite measure. -/
theorem limit_eq_zero_of_integrable_atTop {g : ℝ → ℝ} (hg : Integrable g) {m : ℝ}
    (h : Tendsto g atTop (𝓝 m)) : m = 0 := by
  by_contra hm
  have hpos : 0 < |m| / 2 := by positivity
  have hev : ∀ᶠ s in atTop, |m| / 2 ≤ |g s| := by
    filter_upwards [Metric.tendsto_nhds.mp h (|m| / 2) hpos] with s hs
    rw [dist_eq_norm, Real.norm_eq_abs] at hs
    have h1 : |m| ≤ |m - g s| + |g s| := by simpa using abs_add_le (m - g s) (g s)
    have h2 := abs_sub_comm m (g s)
    linarith
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hev
  have hconst : IntegrableOn (fun _ : ℝ => |m| / 2) (Set.Ioi R) := by
    refine hg.norm.integrableOn.mono' aestronglyMeasurable_const
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_pos hpos, Real.norm_eq_abs]
    exact hR s (le_of_lt hs)
  rw [integrableOn_const_iff, Real.volume_Ioi] at hconst
  rcases hconst with h0 | h0
  · rw [enorm_eq_zero] at h0
    exact hpos.ne' h0
  · exact (lt_irrefl _ h0).elim

/-- The same at `−∞`. -/
theorem limit_eq_zero_of_integrable_atBot {g : ℝ → ℝ} (hg : Integrable g) {m : ℝ}
    (h : Tendsto g atBot (𝓝 m)) : m = 0 := by
  by_contra hm
  have hpos : 0 < |m| / 2 := by positivity
  have hev : ∀ᶠ s in atBot, |m| / 2 ≤ |g s| := by
    filter_upwards [Metric.tendsto_nhds.mp h (|m| / 2) hpos] with s hs
    rw [dist_eq_norm, Real.norm_eq_abs] at hs
    have h1 : |m| ≤ |m - g s| + |g s| := by simpa using abs_add_le (m - g s) (g s)
    have h2 := abs_sub_comm m (g s)
    linarith
  obtain ⟨R, hR⟩ := Filter.eventually_atBot.mp hev
  have hconst : IntegrableOn (fun _ : ℝ => |m| / 2) (Set.Iic R) := by
    refine hg.norm.integrableOn.mono' aestronglyMeasurable_const
      (ae_restrict_of_forall_mem measurableSet_Iic fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_pos hpos, Real.norm_eq_abs]
    exact hR s hs
  rw [integrableOn_const_iff, Real.volume_Iic] at hconst
  rcases hconst with h0 | h0
  · rw [enorm_eq_zero] at h0
    exact hpos.ne' h0
  · exact (lt_irrefl _ h0).elim

/-- **Lemma 10.2.4.**  For an invertible symmetric `B` there is `C₁ > 0` with
`‖Y‖²_{W^{1,2}} ≤ C₁‖dY/ds + BY‖²_{L²}` for every `Y ∈ W^{1,2}(ℝ;ℝⁿ)`.

The book proves it with the Fourier transform and Plancherel, through the
symbol estimate `lemma_10_2_4_symbol` above.  The proof here is more elementary
and needs no Fourier analysis: expanding `‖Y' + BY‖² = ‖Y'‖² + 2⟪Y', BY⟫ + ‖BY‖²`,
the cross term is the derivative of `⟪Y, BY⟫` (this is where the symmetry of `B`
enters), which is integrable together with its derivative, so it tends to `0`
at `±∞` and the cross term integrates to zero.  Then
`∫ ‖Y' + BY‖² = ∫ ‖Y'‖² + ∫ ‖BY‖² ≥ ∫ ‖Y'‖² + C₀² ∫ ‖Y‖²`, and
`C₁ = max (1, 1/C₀²)` works. -/
theorem lemma_10_2_4 (B : E →L[ℝ] E) (hB : ∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫)
    {C₀ : ℝ} (hC₀pos : 0 < C₀) (hC₀ : ∀ v, C₀ * ‖v‖ ≤ ‖B v‖) :
    ∃ C₁ > 0, ∀ Y Y' : ℝ → E, (∀ s, HasDerivAt Y (Y' s) s) →
      Integrable (fun s => ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) →
      Integrable (fun s => ‖linOp (fun _ => B) Y Y' s‖ ^ 2) →
      sobolevSq Y Y' ≤ C₁ * l2Sq (linOp (fun _ => B) Y Y') := by
  refine ⟨max 1 (1 / C₀ ^ 2), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro Y Y' hY hint1 hint2
  set C₁ := max 1 (1 / C₀ ^ 2) with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_left _ _
  have hC₁0 : 0 ≤ C₁ := zero_le_one.trans hC₁1
  have hC₁C : 1 ≤ C₁ * C₀ ^ 2 := by
    have h : 1 / C₀ ^ 2 ≤ C₁ := le_max_right _ _
    calc (1 : ℝ) = 1 / C₀ ^ 2 * C₀ ^ 2 := by field_simp
      _ ≤ C₁ * C₀ ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg _)
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hY s).continuousAt
  have hY'm : StronglyMeasurable Y' := stronglyMeasurable_of_hasDerivAt hY
  have hBYc : Continuous fun s => B (Y s) := B.continuous.comp hYc
  -- the cross term `2⟪Y', BY⟫` is the derivative of `g = ⟪Y, BY⟫`
  set g : ℝ → ℝ := fun s => ⟪Y s, B (Y s)⟫ with hg
  have hgd : ∀ s, HasDerivAt g (2 * ⟪Y' s, B (Y s)⟫) s := by
    intro s
    have h1 : HasDerivAt (fun t => B (Y t)) (B (Y' s)) s :=
      B.hasFDerivAt.comp_hasDerivAt s (hY s)
    have h2 := (hY s).inner ℝ h1
    have h3 : ⟪Y s, B (Y' s)⟫ + ⟪Y' s, B (Y s)⟫ = 2 * ⟪Y' s, B (Y s)⟫ := by
      rw [← hB (Y s) (Y' s), real_inner_comm (Y' s) (B (Y s))]; ring
    rw [h3] at h2
    exact h2
  have hcross_int : Integrable fun s => 2 * ⟪Y' s, B (Y s)⟫ := by
    refine (hint1.const_mul ‖B‖).mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
    · exact (continuous_inner.comp_aestronglyMeasurable
        (hY'm.aestronglyMeasurable.prodMk hBYc.aestronglyMeasurable)).const_mul 2
    · rw [Real.norm_eq_abs, abs_mul, abs_two]
      calc 2 * |⟪Y' s, B (Y s)⟫| ≤ 2 * (‖Y' s‖ * ‖B (Y s)‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) two_pos.le
        _ ≤ 2 * (‖Y' s‖ * (‖B‖ * ‖Y s‖)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)) two_pos.le
        _ = ‖B‖ * (2 * ‖Y' s‖ * ‖Y s‖) := by ring
        _ ≤ ‖B‖ * (‖Y' s‖ ^ 2 + ‖Y s‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _) (norm_nonneg _)
        _ = ‖B‖ * (‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) := by ring
  have hgint : Integrable g := by
    refine (hint1.const_mul ‖B‖).mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
    · exact (continuous_inner.comp (hYc.prodMk hBYc)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      calc |⟪Y s, B (Y s)⟫| ≤ ‖Y s‖ * ‖B (Y s)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖Y s‖ * (‖B‖ * ‖Y s‖) := mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
        _ = ‖B‖ * ‖Y s‖ ^ 2 := by ring
        _ ≤ ‖B‖ * (‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            linarith [sq_nonneg ‖Y' s‖]
  have hlim_top : Tendsto g atTop (𝓝 (limUnder atTop g)) :=
    tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun s _ => hgd s)
      hcross_int.integrableOn
  have hlim_bot : Tendsto g atBot (𝓝 (limUnder atBot g)) :=
    tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun s _ => hgd s)
      hcross_int.integrableOn
  have hzero : ∫ s, 2 * ⟪Y' s, B (Y s)⟫ = 0 := by
    rw [integral_of_hasDerivAt_of_tendsto hgd hcross_int hlim_bot hlim_top,
      limit_eq_zero_of_integrable_atTop hgint hlim_top,
      limit_eq_zero_of_integrable_atBot hgint hlim_bot, sub_zero]
  -- the pointwise inequality
  have hpt : ∀ s, ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2
      ≤ C₁ * (‖linOp (fun _ => B) Y Y' s‖ ^ 2 - 2 * ⟪Y' s, B (Y s)⟫) := by
    intro s
    have h1 : ‖linOp (fun _ => B) Y Y' s‖ ^ 2
        = ‖Y' s‖ ^ 2 + 2 * ⟪Y' s, B (Y s)⟫ + ‖B (Y s)‖ ^ 2 := by
      show ‖Y' s + B (Y s)‖ ^ 2 = _
      exact norm_add_sq_real _ _
    have h2 : C₀ ^ 2 * ‖Y s‖ ^ 2 ≤ ‖B (Y s)‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (hC₀ _) 2
    have h3 : ‖Y s‖ ^ 2 ≤ C₁ * ‖B (Y s)‖ ^ 2 := by
      calc ‖Y s‖ ^ 2 = 1 * ‖Y s‖ ^ 2 := (one_mul _).symm
        _ ≤ (C₁ * C₀ ^ 2) * ‖Y s‖ ^ 2 := mul_le_mul_of_nonneg_right hC₁C (sq_nonneg _)
        _ = C₁ * (C₀ ^ 2 * ‖Y s‖ ^ 2) := by ring
        _ ≤ C₁ * ‖B (Y s)‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hC₁0
    have h4 : ‖Y' s‖ ^ 2 ≤ C₁ * ‖Y' s‖ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hC₁1
    rw [h1]
    nlinarith [h3, h4]
  have hint3 : Integrable fun s =>
      C₁ * (‖linOp (fun _ => B) Y Y' s‖ ^ 2 - 2 * ⟪Y' s, B (Y s)⟫) :=
    (hint2.sub hcross_int).const_mul C₁
  calc sobolevSq Y Y' = ∫ s, (‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) := rfl
    _ ≤ ∫ s, C₁ * (‖linOp (fun _ => B) Y Y' s‖ ^ 2 - 2 * ⟪Y' s, B (Y s)⟫) :=
        integral_mono hint1 hint3 hpt
    _ = C₁ * (l2Sq (linOp (fun _ => B) Y Y') - ∫ s, 2 * ⟪Y' s, B (Y s)⟫) := by
        rw [integral_const_mul, integral_sub hint2 hcross_int]; rfl
    _ = C₁ * l2Sq (linOp (fun _ => B) Y Y') := by rw [hzero, sub_zero]

/-- The elementary inequality `½‖x‖² − ‖y‖² ≤ ‖x + y‖²`, obtained as in the book
by expanding `‖x + 2y‖² ≥ 0`.  Complete proof. -/
theorem half_normSq_sub_le (x y : E) : (1 : ℝ) / 2 * ‖x‖ ^ 2 - ‖y‖ ^ 2 ≤ ‖x + y‖ ^ 2 := by
  have e1 : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_add_sq_real x y
  have e2 : ‖x + (2 : ℝ) • y‖ ^ 2
      = ‖x‖ ^ 2 + 2 * ⟪x, (2 : ℝ) • y⟫ + ‖(2 : ℝ) • y‖ ^ 2 := norm_add_sq_real _ _
  have e3 : ⟪x, (2 : ℝ) • y⟫ = 2 * ⟪x, y⟫ := real_inner_smul_right _ _ _
  have e4 : ‖(2 : ℝ) • y‖ ^ 2 = 4 * ‖y‖ ^ 2 := by
    rw [norm_smul_sq]; norm_num
  have h := sq_nonneg ‖x + (2 : ℝ) • y‖
  rw [e2, e3, e4] at h
  linarith [e1]

/-- **Lemma 10.2.5, pointwise.**  With `‖A(s)v‖ ≤ C‖v‖`,

`‖Y‖² + ‖dY/ds‖² ≤ (2 + 2C²)(‖Y‖² + ‖L_u Y‖²)`.

Complete proof, from the inequality above with `x = dY/ds` and `y = A(s)Y`. -/
theorem lemma_10_2_5_pointwise {A : ℝ → E →L[ℝ] E} {C : ℝ}
    (hA : ∀ s v, ‖A s v‖ ≤ C * ‖v‖) (Y Y' : ℝ → E) (s : ℝ) :
    ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2 ≤ (2 + 2 * C ^ 2) * (‖Y s‖ ^ 2 + ‖linOp A Y Y' s‖ ^ 2) := by
  have hkey : (1 : ℝ) / 2 * ‖Y' s‖ ^ 2 - ‖A s (Y s)‖ ^ 2 ≤ ‖linOp A Y Y' s‖ ^ 2 :=
    half_normSq_sub_le (Y' s) (A s (Y s))
  have hbd : ‖A s (Y s)‖ ^ 2 ≤ C ^ 2 * ‖Y s‖ ^ 2 := by
    have hq := mul_self_le_mul_self (norm_nonneg (A s (Y s))) (hA s (Y s))
    nlinarith [hq]
  have hCsq : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
  have hn1 : (0 : ℝ) ≤ ‖Y s‖ ^ 2 := sq_nonneg _
  have hn2 : (0 : ℝ) ≤ ‖linOp A Y Y' s‖ ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hCsq hn2, mul_nonneg hCsq hn1]

/-- A pointwise bound integrates. -/
theorem integral_le_of_pointwise {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (C : ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ x, f x ≤ C * g x) : ∫ x, f x ∂μ ≤ C * ∫ x, g x ∂μ := by
  have hmono := MeasureTheory.integral_mono hf (hg.const_mul C) h
  rwa [MeasureTheory.integral_const_mul] at hmono

/-- **Lemma 10.2.5.**  On a bounded interval, with a bounded coefficient,

`∫(‖Y‖² + ‖dY/ds‖²) ≤ C₃ ∫(‖Y‖² + ‖L_u Y‖²)`,

with `C₃ = 2 + 2C²`.  Complete proof; the measure is arbitrary, so the Lebesgue
measure restricted to `[−M, M]` gives the book's statement. -/
theorem lemma_10_2_5 {A : ℝ → E →L[ℝ] E} {C : ℝ}
    (hA : ∀ s v, ‖A s v‖ ≤ C * ‖v‖) (Y Y' : ℝ → E) (μ : Measure ℝ)
    (h1 : Integrable (fun s => ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) μ)
    (h2 : Integrable (fun s => ‖Y s‖ ^ 2 + ‖linOp A Y Y' s‖ ^ 2) μ) :
    ∫ s, (‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) ∂μ
      ≤ (2 + 2 * C ^ 2) * ∫ s, (‖Y s‖ ^ 2 + ‖linOp A Y Y' s‖ ^ 2) ∂μ :=
  integral_le_of_pointwise _ h1 h2 (lemma_10_2_5_pointwise hA Y Y')

/-! ### The cut-off argument of Proposition 10.2.3

`Y` is split as `β₀Y + β₊Y + βmY` with a `C¹` partition of unity on `ℝ`: `β₊` is
`1` beyond `M + 1` and `0` before `M`, `βm` symmetrically, and `β₀ = 1 − β₊ − βm`
is supported in `[−T, T]`, `T = M + 1`.  On the support of `β₊` the operator
`A(s)` is within `ε` of its limit `By`, so Lemma 10.2.4 for `By` controls `β₊Y`
once the error `(A − By)β₊Y` is absorbed (`end_piece_estimate`); `β₀Y` is
controlled by Lemma 10.2.5 (`middle_piece_estimate`); and the pieces are
reassembled with `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)`. -/

/-- A `C¹` step: `0` on `(−∞, a]`, `1` on `[a + 1, ∞)`, with values in `[0, 1]` and
a continuous derivative, bounded by `D` and vanishing outside `[a, a + 1]`.  It is
Mathlib's `Real.smoothTransition`, translated. -/
theorem exists_step (a : ℝ) : ∃ (β β' : ℝ → ℝ) (D : ℝ), 0 < D ∧
    (∀ s, HasDerivAt β (β' s) s) ∧ Continuous β' ∧
    (∀ s, 0 ≤ β s) ∧ (∀ s, β s ≤ 1) ∧ (∀ s, s ≤ a → β s = 0) ∧ (∀ s, a + 1 ≤ s → β s = 1) ∧
    (∀ s, |β' s| ≤ D) ∧ (∀ s, s ∉ Set.Icc a (a + 1) → β' s = 0) := by
  set β : ℝ → ℝ := fun s => Real.smoothTransition (s - a) with hβ
  have hβc : ContDiff ℝ 1 β :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hβd : ∀ s, HasDerivAt β (deriv β s) s := fun s =>
    (hβc.differentiable one_ne_zero s).hasDerivAt
  have hβ'c : Continuous (deriv β) := hβc.continuous_deriv le_rfl
  have hzero : ∀ s, s ≤ a → β s = 0 := fun s hs =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hone : ∀ s, a + 1 ≤ s → β s = 1 := fun s hs =>
    Real.smoothTransition.one_of_one_le (by linarith)
  have hd0 : ∀ s, s ∉ Set.Icc a (a + 1) → deriv β s = 0 := by
    intro s hs
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · have hev : β =ᶠ[𝓝 s] fun _ => (0:ℝ) := by
        filter_upwards [Iio_mem_nhds hs] with t ht
        exact hzero t (le_of_lt ht)
      rw [hev.deriv_eq]; simp
    · have hev : β =ᶠ[𝓝 s] fun _ => (1:ℝ) := by
        filter_upwards [Ioi_mem_nhds hs] with t ht
        exact hone t (le_of_lt ht)
      rw [hev.deriv_eq]; simp
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := a + 1)).exists_bound_of_continuousOn
    hβ'c.continuousOn
  refine ⟨β, deriv β, max C 1, lt_max_of_lt_right one_pos, hβd, hβ'c,
    fun s => Real.smoothTransition.nonneg _, fun s => Real.smoothTransition.le_one _,
    hzero, hone, fun s => ?_, hd0⟩
  by_cases hs : s ∈ Set.Icc a (a + 1)
  · exact (le_of_eq (Real.norm_eq_abs _).symm).trans ((hC s hs).trans (le_max_left _ _))
  · rw [hd0 s hs, abs_zero]; exact zero_le_one.trans (le_max_right _ _)

theorem norm_smul_sq_le_of_le_one {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (v : E) :
    ‖c • v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ h0 h1)

theorem norm_smul_add_smul_sq_le {c c' D : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (hD : |c'| ≤ D)
    (v w : E) : ‖c' • v + c • w‖ ^ 2 ≤ 2 * (D ^ 2 * ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  refine (norm_add_sq_le_two _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
    abs_of_nonneg h0]
  have h3 : c' ^ 2 ≤ D ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hD 2
  have h4 : c ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖v‖),
    mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖w‖)]

theorem norm_deriv_smul_sq_le {β' : ℝ → ℝ} {D T : ℝ} (hβ'le : ∀ s, |β' s| ≤ D)
    (hβ'zero : ∀ s, s ∉ Set.Icc (-T) T → β' s = 0) (Y : ℝ → E) (s : ℝ) :
    ‖β' s • Y s‖ ^ 2 ≤ D ^ 2 * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s := by
  by_cases hs : s ∈ Set.Icc (-T) T
  · rw [Set.indicator_of_mem hs, norm_smul, Real.norm_eq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hβ'le s) 2) (sq_nonneg _)
  · rw [Set.indicator_of_notMem hs, hβ'zero s hs, zero_smul, norm_zero]; simp

/-- The pair `(βY, β'Y + βY')` is again `W^{1,2}` data. -/
theorem piece_integrable {β β' : ℝ → ℝ} {D : ℝ} (hβd : ∀ s, HasDerivAt β (β' s) s)
    (hβ'c : Continuous β') (hβ0 : ∀ s, 0 ≤ β s) (hβ1 : ∀ s, β s ≤ 1)
    (hβ'le : ∀ s, |β' s| ≤ D) {Y Y' : ℝ → E} (hY : ∀ s, HasDerivAt Y (Y' s) s)
    (hint1 : Integrable fun s => ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) :
    Integrable fun s => ‖β s • Y s‖ ^ 2 + ‖β' s • Y s + β s • Y' s‖ ^ 2 := by
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hY s).continuousAt
  have hβc : Continuous β := continuous_iff_continuousAt.2 fun s => (hβd s).continuousAt
  have hY'm : AEStronglyMeasurable Y' volume :=
    (stronglyMeasurable_of_hasDerivAt hY).aestronglyMeasurable
  refine integrable_add_sq_norm_of_le (hβc.smul hYc).aestronglyMeasurable
    ((hβ'c.aestronglyMeasurable.smul hYc.aestronglyMeasurable).add
      (hβc.aestronglyMeasurable.smul hY'm))
    (hint1.const_mul (1 + 2 * D ^ 2 + 2)) fun s => ?_
  have h1 := norm_smul_sq_le_of_le_one (hβ0 s) (hβ1 s) (Y s)
  have h2 := norm_smul_add_smul_sq_le (hβ0 s) (hβ1 s) (hβ'le s) (Y s) (Y' s)
  nlinarith [h1, h2, mul_nonneg (sq_nonneg D) (sq_nonneg ‖Y' s‖), sq_nonneg ‖Y s‖]

/-- The estimate for an end piece `βY`: on the support of `β` the operator `A(s)`
is within `ε` of the constant `B`, for which Lemma 10.2.4 holds with constant
`C₁`, and `3 C₁ ε² ≤ 1/2` lets the error term be absorbed. -/
theorem end_piece_estimate {A : ℝ → E →L[ℝ] E} {B : E →L[ℝ] E} {C₁ ε D T : ℝ}
    (hC₁ : 0 < C₁)
    (h124 : ∀ Z Z' : ℝ → E, (∀ s, HasDerivAt Z (Z' s) s) →
      Integrable (fun s => ‖Z s‖ ^ 2 + ‖Z' s‖ ^ 2) →
      Integrable (fun s => ‖linOp (fun _ => B) Z Z' s‖ ^ 2) →
      sobolevSq Z Z' ≤ C₁ * l2Sq (linOp (fun _ => B) Z Z'))
    (hε : 3 * C₁ * ε ^ 2 ≤ 1 / 2)
    {β β' : ℝ → ℝ} (hβd : ∀ s, HasDerivAt β (β' s) s) (hβ'c : Continuous β')
    (hβ0 : ∀ s, 0 ≤ β s) (hβ1 : ∀ s, β s ≤ 1) (hβ'le : ∀ s, |β' s| ≤ D)
    (hβ'zero : ∀ s, s ∉ Set.Icc (-T) T → β' s = 0)
    (hnear : ∀ s, β s ≠ 0 → ‖A s - B‖ ≤ ε)
    {Y Y' : ℝ → E} (hY : ∀ s, HasDerivAt Y (Y' s) s)
    (hint1 : Integrable fun s => ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2)
    (hint2 : Integrable fun s => ‖linOp A Y Y' s‖ ^ 2) :
    sobolevSq (fun s => β s • Y s) (fun s => β' s • Y s + β s • Y' s)
      ≤ 6 * C₁ * (D ^ 2 * l2SqOn Y T + l2Sq (linOp A Y Y')) := by
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hY s).continuousAt
  have hβc : Continuous β := continuous_iff_continuousAt.2 fun s => (hβd s).continuousAt
  have hY'm : AEStronglyMeasurable Y' volume :=
    (stronglyMeasurable_of_hasDerivAt hY).aestronglyMeasurable
  set Z : ℝ → E := fun s => β s • Y s with hZ
  set Z' : ℝ → E := fun s => β' s • Y s + β s • Y' s with hZ'
  have hZd : ∀ s, HasDerivAt Z (Z' s) s := fun s => by
    have h := (hβd s).smul (hY s)
    rw [add_comm] at h
    exact h
  have hZm : AEStronglyMeasurable Z volume := (hβc.smul hYc).aestronglyMeasurable
  have hZ'm : AEStronglyMeasurable Z' volume :=
    (hβ'c.aestronglyMeasurable.smul hYc.aestronglyMeasurable).add
      (hβc.aestronglyMeasurable.smul hY'm)
  have hYsq : Integrable fun s => ‖Y s‖ ^ 2 :=
    integrable_sq_norm_of_le hYc.aestronglyMeasurable hint1 fun s => by
      nlinarith [sq_nonneg ‖Y' s‖]
  have hind : Integrable fun s => (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s :=
    hYsq.indicator measurableSet_Icc
  have hZsq : Integrable fun s => ‖Z s‖ ^ 2 :=
    integrable_sq_norm_of_le hZm hYsq fun s => norm_smul_sq_le_of_le_one (hβ0 s) (hβ1 s) (Y s)
  have hZZ' : Integrable fun s => ‖Z s‖ ^ 2 + ‖Z' s‖ ^ 2 :=
    piece_integrable hβd hβ'c hβ0 hβ1 hβ'le hY hint1
  -- `Z' + BZ = β'Y + β(LY) − (A − B)Z`
  have hkey : ∀ s, linOp (fun _ => B) Z Z' s
      = β' s • Y s + β s • linOp A Y Y' s - (A s - B) (Z s) := by
    intro s
    simp only [linOp, hZ, hZ', sub_apply, map_smul, smul_add, smul_sub]
    abel
  have hpt : ∀ s, ‖linOp (fun _ => B) Z Z' s‖ ^ 2
      ≤ 3 * (D ^ 2 * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s
          + ‖linOp A Y Y' s‖ ^ 2 + ε ^ 2 * ‖Z s‖ ^ 2) := by
    intro s
    rw [hkey, sub_eq_add_neg]
    refine (norm_add3_sq_le _ _ _).trans ?_
    rw [norm_neg]
    have h1 := norm_deriv_smul_sq_le hβ'le hβ'zero Y s
    have h2 := norm_smul_sq_le_of_le_one (hβ0 s) (hβ1 s) (linOp A Y Y' s)
    have h3 : ‖(A s - B) (Z s)‖ ^ 2 ≤ ε ^ 2 * ‖Z s‖ ^ 2 := by
      by_cases hβs : β s = 0
      · have hZ0 : Z s = 0 := by show β s • Y s = 0; rw [hβs, zero_smul]
        rw [hZ0, map_zero, norm_zero]; simp
      · rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (((A s - B).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hnear s hβs) (norm_nonneg _))) 2
    linarith
  have hind' : Integrable fun s => D ^ 2 * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s :=
    hind.const_mul _
  have hG1 : Integrable fun s => D ^ 2 * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s
      + ‖linOp A Y Y' s‖ ^ 2 := hind'.add hint2
  have hG2 : Integrable fun s => ε ^ 2 * ‖Z s‖ ^ 2 := hZsq.const_mul _
  have hG3 : Integrable fun s => D ^ 2 * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s
      + ‖linOp A Y Y' s‖ ^ 2 + ε ^ 2 * ‖Z s‖ ^ 2 := hG1.add hG2
  have hG : Integrable fun s => 3 * (D ^ 2 * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s
      + ‖linOp A Y Y' s‖ ^ 2 + ε ^ 2 * ‖Z s‖ ^ 2) := hG3.const_mul 3
  have hLZ : Integrable fun s => ‖linOp (fun _ => B) Z Z' s‖ ^ 2 :=
    integrable_sq_norm_of_le (hZ'm.add (B.continuous.comp_aestronglyMeasurable hZm)) hG hpt
  have hE : l2Sq (linOp (fun _ => B) Z Z')
      ≤ 3 * (D ^ 2 * l2SqOn Y T + l2Sq (linOp A Y Y') + ε ^ 2 * l2Sq Z) := by
    have h := integral_mono hLZ hG hpt
    rw [integral_const_mul, integral_add hG1 hG2, integral_add hind' hint2, integral_const_mul,
      integral_const_mul, integral_indicator measurableSet_Icc] at h
    exact h
  have hS := h124 Z Z' hZd hZZ' hLZ
  have hZle : l2Sq Z ≤ sobolevSq Z Z' :=
    integral_mono hZsq hZZ' fun s => by nlinarith [sq_nonneg ‖Z' s‖]
  have hZ0 : 0 ≤ l2Sq Z := integral_nonneg fun s => sq_nonneg _
  have hC1ε : C₁ * (3 * (ε ^ 2 * l2Sq Z)) ≤ 1 / 2 * sobolevSq Z Z' := by
    calc C₁ * (3 * (ε ^ 2 * l2Sq Z)) = (3 * C₁ * ε ^ 2) * l2Sq Z := by ring
      _ ≤ 1 / 2 * l2Sq Z := mul_le_mul_of_nonneg_right hε hZ0
      _ ≤ 1 / 2 * sobolevSq Z Z' := by linarith
  have := mul_le_mul_of_nonneg_left hE hC₁.le
  linarith

/-- The estimate for the middle piece `βY`, supported in `[−T, T]`, from
Lemma 10.2.5. -/
theorem middle_piece_estimate {A : ℝ → E →L[ℝ] E} {CA D T : ℝ} (hAc : Continuous A)
    (hA : ∀ s v, ‖A s v‖ ≤ CA * ‖v‖)
    {β β' : ℝ → ℝ} (hβd : ∀ s, HasDerivAt β (β' s) s) (hβ'c : Continuous β')
    (hβ0 : ∀ s, 0 ≤ β s) (hβ1 : ∀ s, β s ≤ 1) (hβ'le : ∀ s, |β' s| ≤ D)
    (hβzero : ∀ s, s ∉ Set.Icc (-T) T → β s = 0)
    (hβ'zero : ∀ s, s ∉ Set.Icc (-T) T → β' s = 0)
    {Y Y' : ℝ → E} (hY : ∀ s, HasDerivAt Y (Y' s) s)
    (hint1 : Integrable fun s => ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2)
    (hint2 : Integrable fun s => ‖linOp A Y Y' s‖ ^ 2) :
    sobolevSq (fun s => β s • Y s) (fun s => β' s • Y s + β s • Y' s)
      ≤ (2 + 2 * CA ^ 2) * ((1 + 2 * D ^ 2) * l2SqOn Y T + 2 * l2Sq (linOp A Y Y')) := by
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hY s).continuousAt
  have hβc : Continuous β := continuous_iff_continuousAt.2 fun s => (hβd s).continuousAt
  have hY'm : AEStronglyMeasurable Y' volume :=
    (stronglyMeasurable_of_hasDerivAt hY).aestronglyMeasurable
  set Z : ℝ → E := fun s => β s • Y s with hZ
  set Z' : ℝ → E := fun s => β' s • Y s + β s • Y' s with hZ'
  have hZZ' : Integrable fun s => ‖Z s‖ ^ 2 + ‖Z' s‖ ^ 2 :=
    piece_integrable hβd hβ'c hβ0 hβ1 hβ'le hY hint1
  have hYsq : Integrable fun s => ‖Y s‖ ^ 2 :=
    integrable_sq_norm_of_le hYc.aestronglyMeasurable hint1 fun s => by
      nlinarith [sq_nonneg ‖Y' s‖]
  have hind : Integrable fun s => (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s :=
    hYsq.indicator measurableSet_Icc
  have hkey : ∀ s, linOp A Z Z' s = β' s • Y s + β s • linOp A Y Y' s := fun s =>
    linOp_smul A Y Y' β β' s
  have hpt : ∀ s, ‖Z s‖ ^ 2 + ‖linOp A Z Z' s‖ ^ 2
      ≤ (1 + 2 * D ^ 2) * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s
        + 2 * ‖linOp A Y Y' s‖ ^ 2 := by
    intro s
    have h1 : ‖Z s‖ ^ 2 ≤ (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s := by
      by_cases hs : s ∈ Set.Icc (-T) T
      · rw [Set.indicator_of_mem hs]; exact norm_smul_sq_le_of_le_one (hβ0 s) (hβ1 s) (Y s)
      · rw [Set.indicator_of_notMem hs]
        show ‖β s • Y s‖ ^ 2 ≤ 0
        rw [hβzero s hs, zero_smul, norm_zero]; simp
    have h2 : ‖linOp A Z Z' s‖ ^ 2
        ≤ 2 * (D ^ 2 * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s
          + ‖linOp A Y Y' s‖ ^ 2) := by
      rw [hkey]
      refine (norm_add_sq_le_two _ _).trans ?_
      have h3 := norm_deriv_smul_sq_le hβ'le hβ'zero Y s
      have h4 := norm_smul_sq_le_of_le_one (hβ0 s) (hβ1 s) (linOp A Y Y' s)
      linarith
    linarith
  have hG1 : Integrable fun s =>
      (1 + 2 * D ^ 2) * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s := hind.const_mul _
  have hG2 : Integrable fun s => 2 * ‖linOp A Y Y' s‖ ^ 2 := hint2.const_mul _
  have hG : Integrable fun s =>
      (1 + 2 * D ^ 2) * (Set.Icc (-T) T).indicator (fun s => ‖Y s‖ ^ 2) s
        + 2 * ‖linOp A Y Y' s‖ ^ 2 := hG1.add hG2
  have hZLZ : Integrable fun s => ‖Z s‖ ^ 2 + ‖linOp A Z Z' s‖ ^ 2 :=
    integrable_add_sq_norm_of_le (hβc.smul hYc).aestronglyMeasurable
      (((hβ'c.aestronglyMeasurable.smul hYc.aestronglyMeasurable).add
        (hβc.aestronglyMeasurable.smul hY'm)).add
        (hAc.clm_apply (hβc.smul hYc)).aestronglyMeasurable) hG hpt
  have h125 := lemma_10_2_5 hA Z Z' volume hZZ' hZLZ
  have hGint : ∫ s, (‖Z s‖ ^ 2 + ‖linOp A Z Z' s‖ ^ 2)
      ≤ (1 + 2 * D ^ 2) * l2SqOn Y T + 2 * l2Sq (linOp A Y Y') := by
    have h := integral_mono hZLZ hG hpt
    rw [integral_add hG1 hG2, integral_const_mul, integral_const_mul,
      integral_indicator measurableSet_Icc] at h
    exact h
  calc sobolevSq Z Z' = ∫ s, (‖Z s‖ ^ 2 + ‖Z' s‖ ^ 2) := rfl
    _ ≤ (2 + 2 * CA ^ 2) * ∫ s, (‖Z s‖ ^ 2 + ‖linOp A Z Z' s‖ ^ 2) := h125
    _ ≤ _ := mul_le_mul_of_nonneg_left hGint (by positivity)

/-- **Proposition 10.2.3.**  For `T` large enough there is a constant `C` with

`‖Y‖_{W^{1,2}} ≤ C(‖L_u Y‖_{L²} + ‖Y‖_{L²([−T,T])})`.

The proof is the book's cut-off argument, with the partition of unity
`1 = β₀ + β₊ + βm` described above: Lemma 10.2.4 for the limits `Bx`, `By` on
the two end pieces (`end_piece_estimate`), Lemma 10.2.5 on the middle piece
(`middle_piece_estimate`), and the Leibniz rule `linOp_smul` to glue.  The
radius `T = M + 1` is chosen so that `A(s)` is within `ε` of its limits for
`|s| ≥ M`, with `ε` small enough for the error terms to be absorbed. -/
theorem prop_10_2_3 (A : ℝ → E →L[ℝ] E) (Bx By : E →L[ℝ] E)
    (hdata : IsLinearisationData A Bx By) :
    ∃ T > 0, ∃ C > 0, ∀ Y Y' : ℝ → E, (∀ s, HasDerivAt Y (Y' s) s) →
      Integrable (fun s => ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) →
      Integrable (fun s => ‖linOp A Y Y' s‖ ^ 2) →
      Real.sqrt (sobolevSq Y Y')
        ≤ C * (Real.sqrt (l2Sq (linOp A Y Y')) + Real.sqrt (l2SqOn Y T)) := by
  -- Lemma 10.2.4 at the two ends, with a common constant
  obtain ⟨cx, hcx, hBx⟩ := hdata.invertible_atBot
  obtain ⟨cy, hcy, hBy⟩ := hdata.invertible_atTop
  obtain ⟨C₁x, hC₁x, h124x⟩ := lemma_10_2_4 Bx hdata.symm_atBot hcx hBx
  obtain ⟨C₁y, hC₁y, h124y⟩ := lemma_10_2_4 By hdata.symm_atTop hcy hBy
  set C₁ := max C₁x C₁y with hC₁
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le hC₁x (le_max_left _ _)
  have h124x' : ∀ Z Z' : ℝ → E, (∀ s, HasDerivAt Z (Z' s) s) →
      Integrable (fun s => ‖Z s‖ ^ 2 + ‖Z' s‖ ^ 2) →
      Integrable (fun s => ‖linOp (fun _ => Bx) Z Z' s‖ ^ 2) →
      sobolevSq Z Z' ≤ C₁ * l2Sq (linOp (fun _ => Bx) Z Z') := fun Z Z' h1 h2 h3 =>
    (h124x Z Z' h1 h2 h3).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (integral_nonneg fun s => sq_nonneg _))
  have h124y' : ∀ Z Z' : ℝ → E, (∀ s, HasDerivAt Z (Z' s) s) →
      Integrable (fun s => ‖Z s‖ ^ 2 + ‖Z' s‖ ^ 2) →
      Integrable (fun s => ‖linOp (fun _ => By) Z Z' s‖ ^ 2) →
      sobolevSq Z Z' ≤ C₁ * l2Sq (linOp (fun _ => By) Z Z') := fun Z Z' h1 h2 h3 =>
    (h124y Z Z' h1 h2 h3).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (integral_nonneg fun s => sq_nonneg _))
  -- `ε` with `3 C₁ ε² ≤ 1/2`
  set ε : ℝ := Real.sqrt (1 / (6 * C₁)) with hε
  have hεpos : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hε2 : 3 * C₁ * ε ^ 2 ≤ 1 / 2 := by
    rw [hε, Real.sq_sqrt (by positivity), mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  -- beyond `±M` the operator is within `ε` of its limits
  obtain ⟨Mp, hMp⟩ : ∃ Mp : ℝ, ∀ s, Mp ≤ s → ‖A s - By‖ ≤ ε := by
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hdata.tendsto_atTop ε hεpos)
    exact ⟨N, fun s hs => by rw [← dist_eq_norm]; exact (hN s hs).le⟩
  obtain ⟨Mm, hMm⟩ : ∃ Mm : ℝ, ∀ s, s ≤ Mm → ‖A s - Bx‖ ≤ ε := by
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atBot.mp (Metric.tendsto_nhds.mp hdata.tendsto_atBot ε hεpos)
    exact ⟨N, fun s hs => by rw [← dist_eq_norm]; exact (hN s hs).le⟩
  set M : ℝ := max 1 (max Mp (-Mm)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMp' : ∀ s, M ≤ s → ‖A s - By‖ ≤ ε := fun s hs =>
    hMp s (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs)
  have hMm' : ∀ s, s ≤ -M → ‖A s - Bx‖ ≤ ε := fun s hs => by
    have : -Mm ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
    exact hMm s (by linarith)
  set T : ℝ := M + 1 with hT
  -- `A` is bounded
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, ∀ s v, ‖A s v‖ ≤ CA * ‖v‖ := by
    obtain ⟨CK, hCK⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
      hdata.continuous.continuousOn
    refine ⟨max CK (max (‖By‖ + ε) (‖Bx‖ + ε)), fun s v => ?_⟩
    refine ((A s).le_opNorm v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rcases le_or_gt s M with h1 | h1
    · rcases le_or_gt (-M) s with h2 | h2
      · exact (hCK s ⟨h2, h1⟩).trans (le_max_left _ _)
      · have h3 := hMm' s h2.le
        calc ‖A s‖ = ‖(A s - Bx) + Bx‖ := by rw [sub_add_cancel]
          _ ≤ ‖A s - Bx‖ + ‖Bx‖ := norm_add_le _ _
          _ ≤ ‖Bx‖ + ε := by linarith
          _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)
    · have h3 := hMp' s h1.le
      calc ‖A s‖ = ‖(A s - By) + By‖ := by rw [sub_add_cancel]
        _ ≤ ‖A s - By‖ + ‖By‖ := norm_add_le _ _
        _ ≤ ‖By‖ + ε := by linarith
        _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
  -- the partition of unity `1 = β₀ + β + βm`
  obtain ⟨β, β', D, hD, hβd, hβ'c, hβ0, hβ1, hβzero, hβone, hβ'le, hβ'zero⟩ := exists_step M
  have hβ'zeroT : ∀ s, s ∉ Set.Icc (-T) T → β' s = 0 := fun s hs =>
    hβ'zero s fun h => hs ⟨by linarith [h.1], by linarith [h.2]⟩
  have hnearp : ∀ s, β s ≠ 0 → ‖A s - By‖ ≤ ε := fun s hs =>
    hMp' s (not_lt.mp fun h => hs (hβzero s h.le))
  set βm : ℝ → ℝ := fun s => β (-s) with hβm
  set βm' : ℝ → ℝ := fun s => -β' (-s) with hβm'
  have hβmd : ∀ s, HasDerivAt βm (βm' s) s := fun s => by
    have h := (hβd (-s)).comp s (hasDerivAt_neg s)
    simpa [Function.comp_def] using h
  have hβm'c : Continuous βm' := (hβ'c.comp continuous_neg).neg
  have hβm0 : ∀ s, 0 ≤ βm s := fun s => hβ0 _
  have hβm1 : ∀ s, βm s ≤ 1 := fun s => hβ1 _
  have hβmzero : ∀ s, -M ≤ s → βm s = 0 := fun s hs => hβzero (-s) (by linarith)
  have hβmone : ∀ s, s ≤ -(M + 1) → βm s = 1 := fun s hs => hβone (-s) (by linarith)
  have hβm'le : ∀ s, |βm' s| ≤ D := fun s => by
    show |-β' (-s)| ≤ D
    rw [abs_neg]; exact hβ'le _
  have hβm'zero : ∀ s, s ∉ Set.Icc (-T) T → βm' s = 0 := fun s hs => by
    show -β' (-s) = 0
    rw [hβ'zero (-s) fun h => hs ⟨by linarith [h.2], by linarith [h.1]⟩, neg_zero]
  have hnearm : ∀ s, βm s ≠ 0 → ‖A s - Bx‖ ≤ ε := fun s hs =>
    hMm' s (not_lt.mp fun h => hs (hβmzero s h.le))
  set β₀ : ℝ → ℝ := fun s => 1 - β s - βm s with hβ₀
  set β₀' : ℝ → ℝ := fun s => -β' s - βm' s with hβ₀'
  have hβ₀d : ∀ s, HasDerivAt β₀ (β₀' s) s := fun s => by
    have h : HasDerivAt (fun x => 1 - β x - βm x) (0 - β' s - βm' s) s :=
      ((hasDerivAt_const s (1:ℝ)).sub (hβd s)).sub (hβmd s)
    rw [zero_sub] at h
    exact h
  have hβ₀'c : Continuous β₀' := hβ'c.neg.sub hβm'c
  have hβ₀0 : ∀ s, 0 ≤ β₀ s := fun s => by
    show 0 ≤ 1 - β s - βm s
    rcases le_or_gt M s with h | h
    · have := hβmzero s (by linarith)
      linarith [hβ1 s]
    · have := hβzero s h.le
      linarith [hβm1 s]
  have hβ₀1 : ∀ s, β₀ s ≤ 1 := fun s => by
    show 1 - β s - βm s ≤ 1
    linarith [hβ0 s, hβm0 s]
  have hβ₀zero : ∀ s, s ∉ Set.Icc (-T) T → β₀ s = 0 := fun s hs => by
    show 1 - β s - βm s = 0
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · rw [hβmone s (by linarith), hβzero s (by linarith)]; ring
    · rw [hβone s (by linarith), hβmzero s (by linarith)]; ring
  have hβ₀'zero : ∀ s, s ∉ Set.Icc (-T) T → β₀' s = 0 := fun s hs => by
    show -β' s - βm' s = 0
    rw [hβ'zeroT s hs, hβm'zero s hs]; ring
  have hβ₀'le : ∀ s, |β₀' s| ≤ 2 * D := fun s => by
    show |-β' s - βm' s| ≤ 2 * D
    rw [neg_sub_left, abs_neg]
    linarith [abs_add_le (βm' s) (β' s), hβ'le s, hβm'le s]
  -- the constants
  set K₀ : ℝ := (2 + 2 * CA ^ 2) * (3 + 8 * D ^ 2) with hK₀
  set K₁ : ℝ := 6 * C₁ * (D ^ 2 + 1) with hK₁
  have hK₀pos : 0 < K₀ := by rw [hK₀]; positivity
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  refine ⟨T, by linarith, Real.sqrt (3 * (K₀ + 2 * K₁)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro Y Y' hY hint1 hint2
  set I := l2SqOn Y T with hI
  set Q := l2Sq (linOp A Y Y') with hQ
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Icc fun s _ => sq_nonneg _
  have hQ0 : 0 ≤ Q := integral_nonneg fun s => sq_nonneg _
  -- the three pieces
  have hSp := end_piece_estimate hC₁pos h124y' hε2 hβd hβ'c hβ0 hβ1 hβ'le hβ'zeroT hnearp
    hY hint1 hint2
  have hSm := end_piece_estimate hC₁pos h124x' hε2 hβmd hβm'c hβm0 hβm1 hβm'le hβm'zero hnearm
    hY hint1 hint2
  have hS₀ := middle_piece_estimate hdata.continuous hCA hβ₀d hβ₀'c hβ₀0 hβ₀1 hβ₀'le hβ₀zero
    hβ₀'zero hY hint1 hint2
  have hSp' : sobolevSq (fun s => β s • Y s) (fun s => β' s • Y s + β s • Y' s)
      ≤ K₁ * (I + Q) := by
    refine hSp.trans ?_
    rw [hK₁]
    nlinarith [mul_nonneg hC₁pos.le (mul_nonneg (sq_nonneg D) hQ0), mul_nonneg hC₁pos.le hI0]
  have hSm' : sobolevSq (fun s => βm s • Y s) (fun s => βm' s • Y s + βm s • Y' s)
      ≤ K₁ * (I + Q) := by
    refine hSm.trans ?_
    rw [hK₁]
    nlinarith [mul_nonneg hC₁pos.le (mul_nonneg (sq_nonneg D) hQ0), mul_nonneg hC₁pos.le hI0]
  have hS₀' : sobolevSq (fun s => β₀ s • Y s) (fun s => β₀' s • Y s + β₀ s • Y' s)
      ≤ K₀ * (I + Q) := by
    refine hS₀.trans ?_
    rw [hK₀]
    have hc : (0:ℝ) ≤ 2 + 2 * CA ^ 2 := by positivity
    nlinarith [mul_nonneg hc hI0, mul_nonneg hc hQ0, mul_nonneg hc (mul_nonneg (sq_nonneg D) hQ0)]
  -- reassembling `Y`
  have hsum : ∀ s, β₀ s + β s + βm s = 1 := fun s => by simp only [hβ₀]; ring
  have hsum' : ∀ s, β₀' s + β' s + βm' s = 0 := fun s => by simp only [hβ₀']; ring
  have hYdec : ∀ s, Y s = β₀ s • Y s + β s • Y s + βm s • Y s := fun s => by
    rw [← add_smul, ← add_smul, hsum, one_smul]
  have hY'dec : ∀ s, Y' s = (β₀' s • Y s + β₀ s • Y' s) + (β' s • Y s + β s • Y' s)
      + (βm' s • Y s + βm s • Y' s) := fun s => by
    have h1 : (β₀' s + β' s + βm' s) • Y s = 0 := by rw [hsum' s, zero_smul]
    have h2 : (β₀ s + β s + βm s) • Y' s = Y' s := by rw [hsum s, one_smul]
    rw [add_smul, add_smul] at h1 h2
    have h3 : (β₀' s • Y s + β₀ s • Y' s) + (β' s • Y s + β s • Y' s)
        + (βm' s • Y s + βm s • Y' s)
        = (β₀' s • Y s + β' s • Y s + βm' s • Y s)
          + (β₀ s • Y' s + β s • Y' s + βm s • Y' s) := by abel
    rw [h3, h1, h2, zero_add]
  have hptdec : ∀ s, ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2
      ≤ 3 * ((‖β₀ s • Y s‖ ^ 2 + ‖β₀' s • Y s + β₀ s • Y' s‖ ^ 2)
          + (‖β s • Y s‖ ^ 2 + ‖β' s • Y s + β s • Y' s‖ ^ 2)
          + (‖βm s • Y s‖ ^ 2 + ‖βm' s • Y s + βm s • Y' s‖ ^ 2)) := fun s => by
    have h1 := norm_add3_sq_le (β₀ s • Y s) (β s • Y s) (βm s • Y s)
    have h2 := norm_add3_sq_le (β₀' s • Y s + β₀ s • Y' s) (β' s • Y s + β s • Y' s)
      (βm' s • Y s + βm s • Y' s)
    rw [← hYdec s] at h1
    rw [← hY'dec s] at h2
    linarith
  have hZ₀i := piece_integrable hβ₀d hβ₀'c hβ₀0 hβ₀1 hβ₀'le hY hint1
  have hZpi := piece_integrable hβd hβ'c hβ0 hβ1 hβ'le hY hint1
  have hZmi := piece_integrable hβmd hβm'c hβm0 hβm1 hβm'le hY hint1
  have hdec : sobolevSq Y Y'
      ≤ 3 * (sobolevSq (fun s => β₀ s • Y s) (fun s => β₀' s • Y s + β₀ s • Y' s)
        + sobolevSq (fun s => β s • Y s) (fun s => β' s • Y s + β s • Y' s)
        + sobolevSq (fun s => βm s • Y s) (fun s => βm' s • Y s + βm s • Y' s)) := by
    have hZ01 : Integrable fun s => (‖β₀ s • Y s‖ ^ 2 + ‖β₀' s • Y s + β₀ s • Y' s‖ ^ 2)
        + (‖β s • Y s‖ ^ 2 + ‖β' s • Y s + β s • Y' s‖ ^ 2) := hZ₀i.add hZpi
    have hZ012 : Integrable fun s => (‖β₀ s • Y s‖ ^ 2 + ‖β₀' s • Y s + β₀ s • Y' s‖ ^ 2)
        + (‖β s • Y s‖ ^ 2 + ‖β' s • Y s + β s • Y' s‖ ^ 2)
        + (‖βm s • Y s‖ ^ 2 + ‖βm' s • Y s + βm s • Y' s‖ ^ 2) := hZ01.add hZmi
    have h := integral_mono hint1 (hZ012.const_mul 3) hptdec
    rw [integral_const_mul, integral_add hZ01 hZmi, integral_add hZ₀i hZpi] at h
    exact h
  have hfinal : sobolevSq Y Y' ≤ (3 * (K₀ + 2 * K₁)) * (Q + I) := by linarith
  calc Real.sqrt (sobolevSq Y Y') ≤ Real.sqrt ((3 * (K₀ + 2 * K₁)) * (Q + I)) :=
        Real.sqrt_le_sqrt hfinal
    _ = Real.sqrt (3 * (K₀ + 2 * K₁)) * Real.sqrt (Q + I) := Real.sqrt_mul (by positivity) _
    _ ≤ Real.sqrt (3 * (K₀ + 2 * K₁)) * (Real.sqrt Q + Real.sqrt I) :=
        mul_le_mul_of_nonneg_left (sqrt_add_le_sqrt_add_sqrt hQ0 hI0) (Real.sqrt_nonneg _)

/-- **Proposition 10.2.2.**  If `u` joins two nondegenerate critical points, the
operator `L_u` is Fredholm.

Stated for abstract Banach spaces standing for `W^{1,2}(ℝ;ℝⁿ)` and
`L²(ℝ;ℝⁿ)`: the hypothesis is the estimate of Proposition 10.2.3, with the
`L²([−T,T])` term factored through a compact operator, which is the hypothesis
of Proposition 8.7.4, together with the finite-dimensional cokernel that Lemma
10.2.6 provides.

The proof follows Proposition 8.7.4.  The kernel is finite-dimensional by Riesz:
on it the estimate reads `‖Y‖ ≤ C ‖rest Y‖`, so a bounded sequence in the kernel
has a subsequence along which `rest Y` converges, and that subsequence is Cauchy.
A finite-dimensional kernel has a closed complement `E₁` (Hahn–Banach), on which
`L_u` is injective with the same range.  A range of finite codimension is then
closed, by the open mapping theorem applied to `E₁ × G → L²` for a
finite-dimensional complement `G` of the range, and `L_u : E₁ → range` is
invertible by the open mapping theorem again. -/
theorem prop_10_2_2 {W L2 T : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup L2] [NormedSpace ℝ L2] [CompleteSpace L2]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    (Lu : W →L[ℝ] L2) (rest : W →L[ℝ] T) (hrest : IsCompactOperator rest) {C : ℝ}
    (hest : ∀ Y : W, ‖Y‖ ≤ C * (‖Lu Y‖ + ‖rest Y‖))
    (hcoker : FiniteDimensional ℝ (L2 ⧸ LinearMap.range (Lu : W →ₗ[ℝ] L2))) :
    ContinuousLinearMap.IsFredholm Lu := by
  -- the kernel is finite-dimensional (Riesz)
  have hker : FiniteDimensional ℝ (LinearMap.ker (Lu : W →ₗ[ℝ] L2)) := by
    obtain ⟨Kc, hKc, hKsub⟩ := hrest.image_closedBall_subset_compact 1
    refine FiniteDimensional.of_isCompact_closedBall₀ ℝ zero_lt_one ?_
    refine IsSeqCompact.isCompact fun x hx => ?_
    have hx1 : ∀ n, ‖(x n : W)‖ ≤ 1 := fun n => mem_closedBall_zero_iff.mp (hx n)
    have hx0 : ∀ n, Lu (x n : W) = 0 := fun n => (x n).2
    have hxK : ∀ n, rest (x n : W) ∈ Kc := fun n =>
      hKsub ⟨x n, mem_closedBall_zero_iff.mpr (hx1 n), rfl⟩
    obtain ⟨a, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq hxK
    have hcauchy : CauchySeq (x ∘ φ) := by
      have hc := hlim.cauchySeq
      rw [Metric.cauchySeq_iff] at hc ⊢
      intro ε hε
      obtain ⟨M, hM⟩ := hc (ε / (|C| + 1)) (by positivity)
      refine ⟨M, fun m hm n hn => ?_⟩
      have h1 := hM m hm n hn
      simp only [Function.comp_apply] at h1
      rw [dist_eq_norm, ← map_sub] at h1
      simp only [Function.comp_apply]
      rw [dist_eq_norm]
      show ‖(x (φ m) : W) - x (φ n)‖ < ε
      have hL : Lu ((x (φ m) : W) - x (φ n)) = 0 := by
        rw [map_sub, hx0, hx0, sub_zero]
      have he := hest ((x (φ m) : W) - x (φ n))
      rw [hL, norm_zero, zero_add] at he
      have ht0 : 0 ≤ ‖rest ((x (φ m) : W) - x (φ n))‖ := norm_nonneg _
      have hC1 : C ≤ |C| + 1 := by linarith [le_abs_self C]
      have h2 := mul_le_mul_of_nonneg_right hC1 ht0
      have h3 := mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < |C| + 1)
      have h4 : (|C| + 1) * (ε / (|C| + 1)) = ε := by field_simp
      linarith
    obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
    exact ⟨b, Metric.isClosed_closedBall.mem_of_tendsto hb
      (Eventually.of_forall fun n => hx (φ n)), φ, hφ, hb⟩
  -- a closed complement of the kernel
  obtain ⟨E₁, hE₁c, hE₁⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional
      (LinearMap.ker (Lu : W →ₗ[ℝ] L2))).exists_isClosed_isCompl
  have : CompleteSpace E₁ := hE₁c.completeSpace_coe
  have hdecomp : ∀ w : W, ∃ e ∈ E₁, Lu w = Lu e := fun w => by
    have hw : w ∈ LinearMap.ker (Lu : W →ₗ[ℝ] L2) ⊔ E₁ := by
      rw [hE₁.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, e, he, rfl⟩ := Submodule.mem_sup.mp hw
    have hk' : Lu k = 0 := hk
    exact ⟨e, he, by rw [map_add, hk', zero_add]⟩
  have hinj : ∀ e : E₁, Lu (e : W) = 0 → e = 0 := fun e he => by
    have h2 : (e : W) ∈ LinearMap.ker (Lu : W →ₗ[ℝ] L2) ⊓ E₁ :=
      Submodule.mem_inf.mpr ⟨he, e.2⟩
    rw [hE₁.inf_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  -- the range is closed
  let f : E₁ →L[ℝ] L2 := Lu.comp E₁.subtypeL
  have hrange : f.range = LinearMap.range (Lu : W →ₗ[ℝ] L2) := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e, rfl⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨e, he, hew⟩ := hdecomp w
      exact ⟨⟨e, he⟩, hew.symm⟩
  have hfker : f.ker = ⊥ := LinearMap.ker_eq_bot'.mpr fun e he => hinj e he
  obtain ⟨G, hG⟩ := Submodule.exists_isCompl (LinearMap.range (Lu : W →ₗ[ℝ] L2))
  have : FiniteDimensional ℝ G :=
    (Submodule.fg_iff_finiteDimensional G).mp (Submodule.CoFG.fg_of_isCompl hG inferInstance)
  have hclosed : IsClosed (LinearMap.range (Lu : W →ₗ[ℝ] L2) : Set L2) := by
    rw [← hrange]
    exact f.closed_complemented_range_of_isCompl_of_ker_eq_bot G (by rw [hrange]; exact hG)
      (Submodule.closed_of_finiteDimensional G) hfker
  -- `L_u : E₁ → range` is invertible
  have : CompleteSpace (LinearMap.range (Lu : W →ₗ[ℝ] L2)) := hclosed.completeSpace_coe
  have : E₁.CoFG :=
    Submodule.FG.cofg_of_isCompl hE₁ ((Submodule.fg_iff_finiteDimensional _).mpr hker)
  have hmaps : Set.MapsTo Lu E₁ (LinearMap.range (Lu : W →ₗ[ℝ] L2)) := fun e _ => ⟨e, rfl⟩
  refine ContinuousLinearMap.IsFredholm.of_isInvertible_restrict hE₁c hclosed hmaps ?_
  refine ⟨ContinuousLinearEquiv.ofBijective (Lu.restrict hmaps) ?_ ?_,
    ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  · refine LinearMap.ker_eq_bot'.mpr fun e he => hinj e ?_
    exact congrArg Subtype.val he
  · refine LinearMap.range_eq_top.mpr ?_
    rintro ⟨y, w, rfl⟩
    obtain ⟨e, he, hew⟩ := hdecomp w
    exact ⟨⟨e, he⟩, Subtype.ext hew.symm⟩

/-- **Lemma 10.2.6, the duality identity.**  The cokernel of `L_u` is the kernel
of `L*_u Z = −dZ/ds + A*(s)Z`, because of the integration by parts

`⟪L_u Y, Z⟫ − ⟪Y, L*_u Z⟫ = d/ds ⟪Y, Z⟫`,

whose integral over `ℝ` vanishes for decaying `Y` and `Z`.  The pointwise
identity is proved here, in the form of the derivative it computes; the passage
to the integral, and the elliptic regularity turning an `L²` solution of
`L*_u Z = 0` into a `W^{1,2}` one, are the parts Mathlib cannot supply. -/
theorem hasDerivAt_inner_linOp {A Aadj : ℝ → E →L[ℝ] E}
    (hadj : ∀ s v w, ⟪A s v, w⟫ = ⟪v, Aadj s w⟫)
    {Y Y' Z Z' : ℝ → E} (hY : ∀ s, HasDerivAt Y (Y' s) s) (hZ : ∀ s, HasDerivAt Z (Z' s) s)
    (s : ℝ) :
    HasDerivAt (fun t => ⟪Y t, Z t⟫)
      (⟪linOp A Y Y' s, Z s⟫ - ⟪Y s, adjOp Aadj Z Z' s⟫) s := by
  have key : ⟪linOp A Y Y' s, Z s⟫ - ⟪Y s, adjOp Aadj Z Z' s⟫
      = ⟪Y s, Z' s⟫ + ⟪Y' s, Z s⟫ := by
    simp only [linOp, adjOp, inner_add_left, inner_add_right, inner_neg_right]
    rw [hadj s (Y s) (Z s)]
    ring
  rw [key]
  exact (hY s).inner ℝ (hZ s)

end Fredholm

/-! ## §10.2.d The computation of the index

The resolvent of the linearised equation identifies

`Ker L_u ≅ T_{u(σ)}W^u(x) ∩ T_{u(σ)}W^s(y)`,
`Ker L*_u ≅ (T_{u(σ)}W^u(x) + T_{u(σ)}W^s(y))^⊥`,

and then the index is a dimension count.  The dictionary is geometric — it needs
the stable and unstable manifolds of Proposition 2.1.5, which Mathlib cannot
state — but the dimension count itself is pure linear algebra and is proved
here. -/

section IndexCount

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The dimension count behind Proposition 10.2.8.**  For two subspaces `U`,
`S` of a finite-dimensional inner product space,

`dim(U ∩ S) − dim (U + S)^⊥ = dim U + dim S − dim V`.

Complete proof, from the formula for the dimensions of a sum and an intersection
and from the dimension of an orthogonal complement. -/
theorem finrank_index_eq (U S : Submodule ℝ V) :
    (Module.finrank ℝ (U ⊓ S : Submodule ℝ V) : ℤ)
        - (Module.finrank ℝ ((U ⊔ S)ᗮ : Submodule ℝ V) : ℤ)
      = (Module.finrank ℝ U : ℤ) + (Module.finrank ℝ S : ℤ) - (Module.finrank ℝ V : ℤ) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U S
  have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (U ⊔ S)
  omega

/-- **Proposition 10.2.8.**  The index of the Fredholm operator `L_u` is
`Ind(x) − Ind(y)`.

Proved from the dimension count, granted the geometric dictionary: `U` is the
tangent space to the unstable manifold of `x`, of dimension `Ind(x)`; `S` is the
tangent space to the stable manifold of `y`, of dimension `n − Ind(y)`; the
kernel of `L_u` is `U ∩ S` and the kernel of `L*_u` is `(U + S)^⊥`. -/
theorem prop_10_2_8 (U S : Submodule ℝ V) {ix iy n : ℕ}
    (hU : Module.finrank ℝ U = ix) (hS : Module.finrank ℝ S = n - iy)
    (hV : Module.finrank ℝ V = n) (hiy : iy ≤ n) :
    (Module.finrank ℝ (U ⊓ S : Submodule ℝ V) : ℤ)
        - (Module.finrank ℝ ((U ⊔ S)ᗮ : Submodule ℝ V) : ℤ)
      = (ix : ℤ) - (iy : ℤ) := by
  have h := finrank_index_eq U S
  rw [hU, hS, hV] at h
  omega

end IndexCount

/-! ## §10.2.e The Smale condition, Theorem 10.1.5

Saying that `L_u` is onto is saying that its cokernel vanishes, that is, that
`L*_u` is injective, that is, that `T_{u(σ)}W^u(x) + T_{u(σ)}W^s(y) = T_{u(σ)}V`:
the transversality of the stable and unstable manifolds, asked for every pair of
critical points.  The linear algebra of that chain is proved here. -/

section Smale

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Theorem 10.1.5, the linear-algebra content.**  The orthogonal complement of
a subspace vanishes exactly when the subspace is everything; applied to
`U + S = T W^u(x) + T W^s(y)`, the vanishing of `Ker L*_u = (U + S)^⊥` is the
Smale transversality condition.  Complete proof. -/
theorem orthogonal_sup_eq_bot_iff (U S : Submodule ℝ V) :
    (U ⊔ S)ᗮ = ⊥ ↔ U ⊔ S = ⊤ := by
  constructor
  · intro h
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (U ⊔ S)
    rw [h, finrank_bot ℝ V, add_zero] at h2
    exact Submodule.eq_top_of_finrank_eq h2
  · intro h
    rw [h, Submodule.top_orthogonal_eq_bot]

/-- **Theorem 10.1.5.**  The field `X` satisfies the Smale condition if and only
if all the operators `L_u` are onto.

Stated as an equivalence of two conditions indexed by the pairs of critical
points, connected by the dictionary of §10.2.d: for each pair the cokernel of
`L_u` is `(U + S)^⊥`, so surjectivity is its vanishing, and transversality is
`U + S = ⊤`.  Complete proof. -/
theorem thm_10_1_5 {ι : Type*} (U S : ι → Submodule ℝ V) :
    (∀ i, U i ⊔ S i = ⊤) ↔ ∀ i, (U i ⊔ S i)ᗮ = ⊥ :=
  ⟨fun h i => (orthogonal_sup_eq_bot_iff _ _).mpr (h i),
   fun h i => (orthogonal_sup_eq_bot_iff _ _).mp (h i)⟩

end Smale

/-! ## §10.3 Lemma 10.3.5

The transversality theorem 10.1.2 needs an infinitesimal deformation `S` of the
almost complex structure moving a given vector off a given hyperplane.  The
space of such deformations and the Sard–Smale theorem are unavailable, but the
piece of linear algebra the proof rests on is elementary and is proved here: one
chooses a real symmetric `S` with `S U = V`, and then `⟪U, S V⟫ = ‖V‖² ≠ 0`. -/

section AlgebraLemma

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Lemma 10.3.5, the computation.**  If `S` is symmetric and `S U = V`, then
`⟪U, S V⟫ = ‖V‖²`, which is nonzero as soon as `V` is.  This is the book's
conclusion; what is not formalized is the construction of such an `S` inside the
space of anti-`ℂ`-linear symmetric matrices, which needs the complex structure of
Chapter 5 in a form Mathlib does not carry. -/
theorem inner_eq_normSq_of_symm {S : E →L[ℝ] E} (hS : ∀ v w, ⟪S v, w⟫ = ⟪v, S w⟫)
    {U V : E} (hUV : S U = V) : ⟪U, S V⟫ = ‖V‖ ^ 2 := by
  rw [← hS U V, hUV, real_inner_self_eq_norm_sq]

end AlgebraLemma

/-! ## §10.4 The Morse and the Floer trajectories coincide

### §10.4.b Proposition 10.1.9

The proof rescales a hypothetical `t`-dependent Floer solution `u_{n_k}` of the
equation for `H/n_k` into a solution `v_{n_k}` of the equation for `H` which is
periodic of period `1/n_k`, and then argues that its limit cannot depend on `t`.
That last step is a statement about sequences of functions of a real variable
and nothing else, and it is proved below in full. -/

section Convergence

variable {E : Type*} [NormedAddCommGroup E]

/-- The integer parts `⌊r N_k⌋ / N_k` converge to `r` when `N_k → ∞`. -/
theorem tendsto_floor_div {N : ℕ → ℝ} (hNpos : ∀ k, 0 < N k) (hN : Tendsto N atTop atTop)
    (r : ℝ) : Tendsto (fun k => (⌊r * N k⌋ : ℝ) / N k) atTop (𝓝 r) := by
  have hinv : Tendsto (fun k => (N k)⁻¹) atTop (𝓝 (0 : ℝ)) := hN.inv_tendsto_atTop
  have hlow : Tendsto (fun k => r - (N k)⁻¹) atTop (𝓝 r) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).sub hinv
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
  · intro k
    have hk := hNpos k
    have hk0 : N k ≠ 0 := ne_of_gt hk
    have hfl := Int.sub_one_lt_floor (r * N k)
    rw [le_div_iff₀ hk]
    have hfield : (r - (N k)⁻¹) * N k = r * N k - 1 := by field_simp
    rw [hfield]
    linarith
  · intro k
    have hk := hNpos k
    rw [div_le_iff₀ hk]
    exact Int.floor_le (r * N k)

/-- **The key step of Proposition 10.1.9.**  A sequence of continuous functions
of the loop parameter, each periodic with period `1/N_k` and with `N_k → ∞`,
which converges uniformly, has a limit that does not depend on the parameter.

This is exactly the book's argument: `v_{n_k}(s,t) = v_{n_k}(s, t + ⌊r n_k⌋/n_k)`
because the shift is an integer multiple of the period; the left side converges
to `v(s,t)` and the right side to `v(s, t + r)`.  Complete proof. -/
theorem eq_of_period_tendsto_zero {N : ℕ → ℝ} (hNpos : ∀ k, 0 < N k)
    (hN : Tendsto N atTop atTop) {v : ℕ → ℝ → E} {w : ℝ → E}
    (hper : ∀ (k : ℕ) (m : ℤ) (t : ℝ), v k (t + (m : ℝ) / N k) = v k t)
    (hcont : ∀ k, Continuous (v k)) (hconv : TendstoUniformly v w atTop) (t r : ℝ) :
    w (t + r) = w t := by
  have hwc : Continuous w := hconv.continuous ((Filter.Eventually.of_forall hcont).frequently)
  have hg : Tendsto (fun k => t + (⌊r * N k⌋ : ℝ) / N k) atTop (𝓝 (t + r)) :=
    tendsto_const_nhds.add (tendsto_floor_div hNpos hN r)
  have h1 : Tendsto (fun k => v k (t + (⌊r * N k⌋ : ℝ) / N k)) atTop (𝓝 (w (t + r))) :=
    hconv.tendsto_comp hwc.continuousAt hg
  have h2 : Tendsto (fun k => v k t) atTop (𝓝 (w t)) :=
    hconv.tendsto_comp hwc.continuousAt tendsto_const_nhds
  have heq : (fun k => v k (t + (⌊r * N k⌋ : ℝ) / N k)) = fun k => v k t :=
    funext fun k => hper k _ t
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end Convergence

/-! ### §10.4.a Lemma 10.4.1 -/

section MeanZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 10.4.1.**  A differentiable map on `[0,1]` with mean zero satisfies
`∫₀¹‖f‖^p ≤ ∫₀¹‖f'‖^p` for every `p ≥ 1`.

The book writes `f(t₁) = ∫₀¹(∫_t^{t₁} f')dt` and estimates.  The proof here
is the same: `‖f(t₁)‖ ≤ ∫₀¹ ‖f(t₁) − f(t)‖ dt ≤ ∫₀¹ ‖f'‖`, then Jensen's
inequality `(∫₀¹ ‖f'‖)^p ≤ ∫₀¹ ‖f'‖^p` for the convex function `x ↦ x^p` on the
probability space `[0, 1]` (`ConvexOn.map_integral_le`), and finally
`∫₀¹ ‖f‖^p ≤ sup ‖f‖^p`.  This is the one analytic ingredient of Proposition
10.1.7: applied with `p = 2` to `f(t) = Y(s,t)` it gives
`‖Y‖_{L²} ≤ ‖∂Y/∂t‖_{L²}`, which combined with the Cauchy–Riemann identity forces
`Y = 0` when `H` is `C²`-small.

Two hypotheses were missing from an earlier statement and are needed:
`CompleteSpace E`, without which Mathlib's Bochner integral is identically `0`
and the mean-zero hypothesis says nothing; and the integrability of `‖f'‖^p`,
without which the right-hand side is `0` for a function such as
`t ↦ t² sin(1/t²)`, which is differentiable at every point of `[0, 1]` but whose
derivative is not integrable. -/
theorem lemma_10_4_1 [CompleteSpace E] {p : ℝ} (hp : 1 ≤ p) (f f' : ℝ → E)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : IntervalIntegrable (fun t => ‖f' t‖ ^ p) volume 0 1)
    (hmean : (∫ t in (0 : ℝ)..1, f t) = 0) :
    (∫ t in (0 : ℝ)..1, ‖f t‖ ^ p) ≤ ∫ t in (0 : ℝ)..1, ‖f' t‖ ^ p := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hfc : ContinuousOn f (Set.Icc 0 1) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hfc' : ContinuousOn f (Set.uIcc 0 1) := by rw [Set.uIcc_of_le zero_le_one]; exact hfc
  -- `f'` is integrable on `[0, 1]`: it is the derivative there, and `‖f'‖ ≤ 1 + ‖f'‖^p`
  have hf'm : AEStronglyMeasurable f' (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    refine (stronglyMeasurable_deriv f).aestronglyMeasurable.congr ?_
    rw [Set.uIoc_of_le zero_le_one]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      (hf t (Set.Ioc_subset_Icc_self ht)).deriv
  have hf'i : IntervalIntegrable f' volume 0 1 := by
    refine ((intervalIntegrable_const (c := (1:ℝ))).add hf').mono_fun hf'm
      (Filter.Eventually.of_forall fun t => ?_)
    show ‖f' t‖ ≤ ‖1 + ‖f' t‖ ^ p‖
    have h0 : (0:ℝ) ≤ ‖f' t‖ ^ p := Real.rpow_nonneg (norm_nonneg _) p
    rw [Real.norm_of_nonneg (by linarith)]
    rcases le_or_gt ‖f' t‖ 1 with h1 | h1
    · linarith
    · have h2 : ‖f' t‖ ^ (1:ℝ) ≤ ‖f' t‖ ^ p := Real.rpow_le_rpow_of_exponent_le h1.le hp
      rw [Real.rpow_one] at h2
      linarith
  -- the sup bound `‖f t₁‖ ≤ ∫₀¹ ‖f'‖`
  set I : ℝ := ∫ t in (0:ℝ)..1, ‖f' t‖ with hI
  have hdiff : ∀ t₁ ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ‖f t₁ - f t‖ ≤ I := by
    intro t₁ ht₁ t ht
    have hsub : Set.uIcc t t₁ ⊆ Set.Icc 0 1 := Set.uIcc_subset_Icc ht ht₁
    have heq : ∫ s in t..t₁, f' s = f t₁ - f t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hf s (hsub hs))
        (hf'i.mono_set (by rw [Set.uIcc_of_le zero_le_one]; exact hsub))
    rw [← heq]
    refine intervalIntegral.norm_integral_le_abs_integral_norm.trans ?_
    rcases le_total t t₁ with h | h
    · rw [abs_of_nonneg (intervalIntegral.integral_nonneg h fun s _ => norm_nonneg _)]
      exact intervalIntegral.integral_mono_interval ht.1 h ht₁.2
        (Filter.Eventually.of_forall fun s => norm_nonneg _) hf'i.norm
    · rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg h fun s _ => norm_nonneg _)]
      exact intervalIntegral.integral_mono_interval ht₁.1 h ht.2
        (Filter.Eventually.of_forall fun s => norm_nonneg _) hf'i.norm
  have hsup : ∀ t₁ ∈ Set.Icc (0:ℝ) 1, ‖f t₁‖ ≤ I := by
    intro t₁ ht₁
    have hfi : IntervalIntegrable f volume 0 1 := hfc'.intervalIntegrable
    have h1 : f t₁ = ∫ t in (0:ℝ)..1, (f t₁ - f t) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hfi, hmean, sub_zero,
        intervalIntegral.integral_const, sub_zero, one_smul]
    calc ‖f t₁‖ = ‖∫ t in (0:ℝ)..1, (f t₁ - f t)‖ := by rw [← h1]
      _ ≤ ∫ t in (0:ℝ)..1, ‖f t₁ - f t‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ t in (0:ℝ)..1, I :=
          intervalIntegral.integral_mono_on zero_le_one
            (continuousOn_const.sub hfc').norm.intervalIntegrable intervalIntegrable_const
            fun t ht => hdiff t₁ ht₁ t ht
      _ = I := by rw [intervalIntegral.integral_const, sub_zero, one_smul]
  -- Jensen: `(∫₀¹ ‖f'‖)^p ≤ ∫₀¹ ‖f'‖^p`
  have hJ : I ^ p ≤ ∫ t in (0:ℝ)..1, ‖f' t‖ ^ p := by
    have : IsProbabilityMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩
    have h := (convexOn_rpow hp).map_integral_le (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (f := fun t => ‖f' t‖) (continuousOn_id.rpow_const fun x _ => Or.inr hp0) isClosed_Ici
      (Filter.Eventually.of_forall fun t => Set.mem_Ici.mpr (norm_nonneg _))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hf'i.norm)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hf')
    rw [hI, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    exact h
  have hfp : IntervalIntegrable (fun t => ‖f t‖ ^ p) volume 0 1 :=
    (hfc'.norm.rpow_const fun x _ => Or.inr hp0).intervalIntegrable
  calc (∫ t in (0:ℝ)..1, ‖f t‖ ^ p) ≤ ∫ t in (0:ℝ)..1, I ^ p :=
        intervalIntegral.integral_mono_on zero_le_one hfp intervalIntegrable_const
          fun t ht => Real.rpow_le_rpow (norm_nonneg _) (hsup t ht) hp0
    _ = I ^ p := by rw [intervalIntegral.integral_const, sub_zero, one_smul]
    _ ≤ _ := hJ

end MeanZero

end Chapter10
end MorseFloer
