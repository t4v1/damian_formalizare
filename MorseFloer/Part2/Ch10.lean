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

## Assumed (`sorry`) or omitted

* **Theorem 10.1.3** is recorded as the predicate `IsFredholmOfIndex`, not as a
  theorem: the operator `L_u` lives on `W^{1,2}(ℝ;ℝⁿ)`, which Mathlib does not
  have, so there is nothing to quantify over and no honest statement to prove.
  Corollaries 10.1.4 and 10.1.8 take it as a hypothesis, in the style of
  Chapter 3's `BrokenPairs`.
* **Proposition 10.2.2** (the Fredholm property of `L_u`) is stated for abstract
  Banach spaces, from the estimate of Proposition 10.2.3 with the local term
  factored through a compact operator, and assumed: it is Proposition 8.7.4,
  which is not available.
* **Proposition 10.2.3** and the integral form of **Lemma 10.2.4** are stated
  with explicit integrals — a pair `(Y, Y')` standing for a function and its
  derivative, since there is no `W^{1,2}` — and assumed.  Lemma 10.2.4 needs the
  Plancherel theorem for vector-valued functions on `ℝ`.
* **Lemma 10.4.1** (a differentiable function of mean zero on `[0,1]` has
  `∫‖f‖^p ≤ ∫‖f'‖^p`) is stated and assumed; the proof is a Fubini–Minkowski
  argument that Mathlib does not make short.
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

/-- **Lemma 10.2.4.**  For an invertible symmetric `B` there is `C₁ > 0` with
`‖Y‖²_{W^{1,2}} ≤ C₁‖dY/ds + BY‖²_{L²}` for every `Y ∈ W^{1,2}(ℝ;ℝⁿ)`.

*Assumed.*  The two inequalities the book's proof rests on are proved above
(`lemma_10_2_4_symbol`); what is missing is the Plancherel theorem for
vector-valued functions on `ℝ`, which Mathlib does not have in a usable form. -/
theorem lemma_10_2_4 (B : E →L[ℝ] E) (_hB : ∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫)
    {C₀ : ℝ} (_hC₀pos : 0 < C₀) (_hC₀ : ∀ v, C₀ * ‖v‖ ≤ ‖B v‖) :
    ∃ C₁ > 0, ∀ Y Y' : ℝ → E, (∀ s, HasDerivAt Y (Y' s) s) →
      Integrable (fun s => ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) →
      Integrable (fun s => ‖linOp (fun _ => B) Y Y' s‖ ^ 2) →
      sobolevSq Y Y' ≤ C₁ * l2Sq (linOp (fun _ => B) Y Y') := by
  sorry

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

/-- **Proposition 10.2.3.**  For `T` large enough there is a constant `C` with

`‖Y‖_{W^{1,2}} ≤ C(‖L_u Y‖_{L²} + ‖Y‖_{L²([−T,T])})`.

*Assumed.*  The proof is the cut-off argument: `Y = βY + (1 − β)Y`, Lemma 10.2.4
applied to `(1 − β)Y`, which vanishes on `[−M, M]` where `A` is still far from
its invertible limits, and Lemma 10.2.5 applied to `βY`, which is supported in
`[−T, T]`; the two are glued by the Leibniz rule `linOp_smul` proved above.
What blocks a formal proof is Lemma 10.2.4, not the gluing. -/
theorem prop_10_2_3 (A : ℝ → E →L[ℝ] E) (Bx By : E →L[ℝ] E)
    (_hdata : IsLinearisationData A Bx By) :
    ∃ T > 0, ∃ C > 0, ∀ Y Y' : ℝ → E, (∀ s, HasDerivAt Y (Y' s) s) →
      Integrable (fun s => ‖Y s‖ ^ 2 + ‖Y' s‖ ^ 2) →
      Integrable (fun s => ‖linOp A Y Y' s‖ ^ 2) →
      Real.sqrt (sobolevSq Y Y')
        ≤ C * (Real.sqrt (l2Sq (linOp A Y Y')) + Real.sqrt (l2SqOn Y T)) := by
  sorry

/-- **Proposition 10.2.2.**  If `u` joins two nondegenerate critical points, the
operator `L_u` is Fredholm.

*Assumed.*  Stated for abstract Banach spaces standing for `W^{1,2}(ℝ;ℝⁿ)` and
`L²(ℝ;ℝⁿ)`: the hypothesis is the estimate of Proposition 10.2.3, with the
`L²([−T,T])` term factored through a compact operator, which is the hypothesis
of Proposition 8.7.4; it yields a finite-dimensional kernel and a closed range,
and the cokernel is handled by Lemma 10.2.6. -/
theorem prop_10_2_2 {W L2 T : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup L2] [NormedSpace ℝ L2] [CompleteSpace L2]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    (Lu : W →L[ℝ] L2) (rest : W →L[ℝ] T) (_hrest : IsCompactOperator rest) {C : ℝ}
    (_hest : ∀ Y : W, ‖Y‖ ≤ C * (‖Lu Y‖ + ‖rest Y‖))
    (_hcoker : FiniteDimensional ℝ (L2 ⧸ LinearMap.range (Lu : W →ₗ[ℝ] L2))) :
    ContinuousLinearMap.IsFredholm Lu := by
  sorry

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

*Assumed.*  The book writes `f(t₁) = ∫₀¹(∫_t^{t₁} f')dt` and estimates; the
estimate is a Fubini–Minkowski argument for which Mathlib has no short route.
This is the one analytic ingredient of Proposition 10.1.7: applied with `p = 2`
to `f(t) = Y(s,t)` it gives `‖Y‖_{L²} ≤ ‖∂Y/∂t‖_{L²}`, which combined with the
Cauchy–Riemann identity forces `Y = 0` when `H` is `C²`-small. -/
theorem lemma_10_4_1 {p : ℝ} (_hp : 1 ≤ p) (f f' : ℝ → E)
    (_hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (_hmean : (∫ t in (0 : ℝ)..1, f t) = 0) :
    (∫ t in (0 : ℝ)..1, ‖f t‖ ^ p) ≤ ∫ t in (0 : ℝ)..1, ‖f' t‖ ^ p := by
  sorry

end MeanZero

end Chapter10
end MorseFloer
