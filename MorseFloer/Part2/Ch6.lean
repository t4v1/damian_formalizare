import MorseFloer.Part2.Ch5

/-!
# Chapter 6: The Arnold conjecture and the Floer equation

Formalization of Chapter 6 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 131–167).  This is the heart of Part II: it
states the Arnold conjecture, identifies the fixed points of a Hamiltonian
diffeomorphism with the `1`-periodic orbits of a Hamiltonian system and with the
critical points of the *action functional* on the space of contractible loops,
writes down the gradient flow of that functional — the **Floer equation** — and
proves the first compactness properties of its solution space.

The chapter has eight sections:

* **§6.1** the Arnold conjecture (Conjecture 6.1.2) and the two easy cases
  (Propositions 6.1.1, 6.1.5, 6.1.6);
* **§6.2** the strategy of the proof and the two standing hypotheses on the
  symplectic manifold (Hypotheses 6.2.1 and 6.2.2);
* **§6.3** the loop space, the action functional `A_H`, and Proposition 6.3.4:
  its critical points are exactly the `1`-periodic Hamiltonian orbits;
* **§6.4** the metric on the loop space coming from a calibrated almost complex
  structure, the gradient of `A_H`, and the Floer equation, with the three
  remarks 6.4.1;
* **§6.5** the space `M` of finite-energy solutions: energy (Remarks 6.5.2),
  elliptic regularity (Proposition 6.5.3), compactness (Theorem 6.5.4), and the
  convergence of finite-energy solutions to periodic orbits
  (Proposition 6.5.7, Lemmas 6.5.9, 6.5.10, 6.5.13, 6.5.14,
  Corollary 6.5.11, Theorem 6.5.6, Proposition 6.5.15);
* **§6.6** the proof of compactness: the uniform gradient bound
  (Proposition 6.6.2), Hofer's "half-maximum" lemma (Lemma 6.6.3) and the
  bubbling argument (Lemmas 6.6.4, 6.6.5), plus the bubble in `P²(ℂ)`;
* **§6.7** an appendix on closed `1`-forms, integration coverings and the action
  form `α_H`;
* **§6.8** an appendix giving `L^{1,p}W` a Banach manifold structure
  (Theorem 6.8.1).

## Status

Mathlib has neither symplectic manifolds nor loop spaces, so the chapter cannot
be developed on a general compact symplectic manifold `W`.  Following the
convention of this project, everything is written in the **standard model**
`ℝ^{2n} = (l ⊕ l) → ℝ` with the symplectic form `stdForm`, the calibrated
complex structure `stdJ` and the Euclidean metric `g(v,w) = ω(v, J₀ w) = v ⬝ᵥ w`
of Chapter 5.  This is exactly Example 6.3.2 of the book, where the action
functional is an honest integral, and it is where the Arnold conjecture was
first proved (Conley–Zehnder, for tori).

Proved here:

* the identification of a `1`-periodic orbit with a fixed point of the time-one
  map of the flow (`isPeriodicOrbit_iff_flow_fixed`), from Mathlib's uniqueness
  theorem for ODEs; and the elementary consequence of Definition 5.4.4 that a
  nondegenerate orbit has no nonzero fixed tangent vector;
* Hamilton's equations in the standard model, `X_t = J₀ · grad H_t`
  (`hamField_eq_stdJ_grad`), and the `1`-periodicity of `X_t` in `t` when `H` is;
* the algebra of `stdForm` and `stdJ` used throughout: `ω(X, J₀ Y) = X ⬝ᵥ Y`,
  `J₀` is a Euclidean isometry, and `ω(J₀ w, w) = −|w|²`;
* the calculus needed for the first variation: the product rule for `ω(x(t),y(t))`
  and **integration by parts on the circle** (`integral_stdForm_byParts`), the
  step that turns `−∫_D u⋆ω` into `∫ ω(ẋ, Y)` in the book's computation;
* the **fundamental lemma of the calculus of variations** in the form the book
  needs (`eq_zero_of_forall_integral_stdForm_eq_zero`), obtained by testing
  against `Y = J₀ v` and using positivity of the calibrated metric;
* **Proposition 6.3.4**: a loop is a critical point of `A_H` — i.e. the action
  form `α_H` of §6.7.b vanishes on it — if and only if it is a `1`-periodic
  orbit of the Hamiltonian system (`actionForm_eq_zero_iff`).  This is the
  conceptual centre of the chapter and is proved outright;
* the equivalent forms of the **Floer equation** (`floer_eq`), and
  **Remarks 6.4.1**: the `s`-independent solutions are the periodic orbits, the
  `t`-independent solutions of an autonomous equation are the negative gradient
  trajectories of `H`, and for `H = 0` the equation is Cauchy–Riemann;
* **Remark 6.5.12**: `ℝ` acts on solutions by translation in `s`;
* **Remarks 6.5.2**: the energy is nonnegative, the two terms in the energy
  integrand agree on a solution (`energyDensity_eq_of_floer`), a solution with
  vanishing `∂u/∂s` is a periodic orbit and conversely
  (`isPeriodicOrbit_of_dS_eq_zero`, `isFloerSolution_of_isPeriodicOrbit`);
* the **first variation of the action** (`hasDerivAt_action`), the analytic
  half of Proposition 6.3.4: `d/dσ A_H(u_σ) = (α_H)_{u_s}(∂u/∂s)`.  It is
  obtained by differentiating under the integral sign with Mathlib's
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, the
  dominating bound coming from the continuity of the `σ`-derivative of the
  integrand on the compact `[s-1, s+1] × [0,1]`, and then integrating by parts
  on the circle.  The computation uses the mixed partial `∂²u/∂σ∂t`, which is
  why it is stated for `IsSmoothLoopVariation` rather than `IsLoopVariation`;
* the **decrease of the action along a Floer trajectory**, the analogue of the
  fact that `f` decreases along a pseudo-gradient trajectory (Chapter 2):
  `d/ds A_H(u_s) = −∫_{S¹} |∂u/∂s|² dt ≤ 0` (`hasDerivAt_action_of_floer`) and
  hence `Antitone (fun s => A_H (u_s))` (`action_antitone`).

Assumed (`sorry`), each with the missing ingredient recorded at the statement:

* **Proposition 6.1.5** — a `2π`-Lipschitz vector field has only constant
  `1`-periodic orbits; the proof is Wirtinger's inequality (Parseval for the
  Fourier series of a loop), which Mathlib does not have;
* **Conjecture 6.1.2** in the case of the torus `T^{2n} = ℝ^{2n}/ℤ^{2n}`, where
  `∑_i dim HM_i(T^{2n}; ℤ/2) = 2^{2n}` is an explicit number
  (`arnold_conjecture_torus`);
* **Proposition 6.5.3** (elliptic regularity, i.e. Lemma 12.1.1),
  **Proposition 6.5.7**, **Lemma 6.5.10**, **Corollary 6.5.11**,
  **Theorem 6.5.6** and **Proposition 6.5.15** (finite-energy solutions converge
  to periodic orbits), **Theorem 6.5.4** (compactness), **Proposition 6.6.2**
  (the uniform gradient bound) and **Lemma 6.6.3** (Hofer's half-maximum lemma),
  the last of which is elementary but needs a dependent-choice recursion;
* **Remark 6.5.2(3)**, `E(u) = A_H(x) − A_H(y)` for a solution joining two
  critical points.

Omitted as unstatable with today's Mathlib (recorded here rather than faked):

* **Proposition 6.1.1** and **Conjecture 6.1.2** on a general compact symplectic
  manifold, and **Proposition 6.1.6**: they need symplectic manifolds, the
  Morse homology `HM_*(W; ℤ/2)` of Chapter 4 as a functor of `W`, and the `C²`
  topology on `C^∞(W; ℝ)`.  The torus case of the conjecture is stated instead.
* **Hypotheses 6.2.1 and 6.2.2** (`⟨ω, π₂(W)⟩ = 0` and `⟨c₁(TW), π₂(W)⟩ = 0`):
  they need de Rham cohomology, `π₂` and Chern classes.  On `ℝ^{2n}` and on the
  torus both hold trivially, which is why the model chosen here is legitimate.
* **§6.3.a** — the loop space `LW` of contractible loops, its `C^∞` topology and
  distance `d_∞`, its path-connectedness, **Remark 6.3.1** (`π₁(LW) = π₂(W)`),
  and the description of `T_x LW` as sections of `x⋆TW`.  A loop space with a
  smooth structure does not exist in Mathlib.  Here a "loop" is simply a
  `1`-periodic map `ℝ → ℝ^{2n}`, and a tangent vector at it is another such map.
* the disc integral `−∫_D u⋆ω` itself, and the proof that it does not depend on
  the filling: this is the content of Hypothesis 6.2.1 and needs integration of
  `2`-forms.  On `ℝ^{2n}` we use the equivalent closed formula of Example 6.3.2.
* **Lemma 6.3.6** — a `C²`-small perturbation of `H` making the critical values
  of `A_H` pairwise distinct; needs the `C²` topology, exactly as §1.2 of
  Chapter 1 did.
* **Remarks 6.3.5**, which are commentary relating this chapter to
  Propositions 5.4.5 and 5.4.7.
* **Lemmas 6.6.4 and 6.6.5** and the **bubble in `P²(ℂ)`** of §6.6.a: they are
  about the symplectic area `∫ v⋆ω` of a `J`-holomorphic plane and the length of
  the image of a circle, i.e. about integration of `2`-forms over surfaces.
* **§6.7** in its entirety: the integration covering of a closed `1`-form, the
  covering `LW~ → LW` with group `π₂(W)/ker ω`, and the action form as an exact
  form upstairs.  Needs covering space theory attached to a `1`-form on an
  infinite-dimensional manifold.  The action form `α_H` itself *is* defined here
  (`actionForm`), since on `ℝ^{2n}` it is an integral.
* **§6.8** and **Theorem 6.8.1** — the Banach manifold structure of `L^{1,p}W`
  modelled on `W^{1,p}(x⋆TW)`.  Needs Sobolev sections of a pulled-back bundle
  and an infinite-dimensional atlas.
-/

open scoped Matrix NNReal ContDiff
open LinearMap (BilinForm)

namespace MorseFloer
namespace Chapter6

open Chapter5

/-! ## §6.1 Periodic orbits and fixed points of the time-one map

The general framework of the Arnold conjecture is a symplectic diffeomorphism of
a symplectic manifold and the problem of bounding its number of fixed points.
The diffeomorphisms considered are the time-one maps of Hamiltonian flows, and
the first thing to do is to identify their fixed points with the `1`-periodic
orbits of the Hamiltonian system. -/

section Orbits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **`1`-periodic orbit** of the time-dependent vector field `X`: a solution
`ẋ(t) = X_t(x(t))` with `x(t+1) = x(t)` (§6.1).  These are the objects the
Arnold conjecture counts. -/
structure IsPeriodicOrbit (X : ℝ → E → E) (x : ℝ → E) : Prop where
  /-- `x` solves the (non-autonomous) Hamiltonian system. -/
  hasDerivAt : ∀ t, HasDerivAt x (X t (x t)) t
  /-- `x` has period `1`. -/
  periodic : Function.Periodic x 1

/-- The **flow** of a time-dependent vector field: `ψ t p` is the value at time
`t` of the solution equal to `p` at time `0`.  The book writes `ψ_t`, and `ψ_1`
is the Hamiltonian diffeomorphism whose fixed points the Arnold conjecture
counts. -/
structure IsFlow (X : ℝ → E → E) (ψ : ℝ → E → E) : Prop where
  /-- `ψ_0 = id`. -/
  init : ∀ p, ψ 0 p = p
  /-- Each trajectory is an integral curve of `X`. -/
  hasDerivAt : ∀ p t, HasDerivAt (fun s => ψ s p) (X t (ψ t p)) t

/-- Uniqueness of solutions: an integral curve of `X` is the trajectory of the
flow through its value at time `0`. -/
theorem IsFlow.eq_flow {X ψ : ℝ → E → E} {K : ℝ≥0} (hψ : IsFlow X ψ)
    (hX : ∀ t, LipschitzWith K (X t)) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (X t (x t)) t) : x = fun t => ψ t (x 0) := by
  refine ODE_solution_unique_univ (K := K) (s := fun _ => Set.univ) (t₀ := (0 : ℝ))
    (fun t => (hX t).lipschitzOnWith) (fun t => ⟨hx t, Set.mem_univ _⟩)
    (fun t => ⟨hψ.hasDerivAt (x 0) t, Set.mem_univ _⟩) ?_
  simp [hψ.init]

/-- **§6.1.**  A `1`-periodic orbit through `p` is the same thing as a fixed
point `p` of the time-one map `ψ_1` of the flow.

This is the translation, used throughout the book, between "fixed points of a
Hamiltonian diffeomorphism" and "`1`-periodic solutions of a Hamiltonian
system".  Both directions use uniqueness of solutions of the ODE; the second one
also uses that `X` is `1`-periodic in `t`, which Remark 6.1.3 shows can always
be arranged. -/
theorem isPeriodicOrbit_iff_flow_fixed {X ψ : ℝ → E → E} {K : ℝ≥0} (hψ : IsFlow X ψ)
    (hX : ∀ t, LipschitzWith K (X t)) (hXper : ∀ t p, X (t + 1) p = X t p) (p : E) :
    (∃ x : ℝ → E, IsPeriodicOrbit X x ∧ x 0 = p) ↔ ψ 1 p = p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxe := hψ.eq_flow hX hx.hasDerivAt
    have h1 : x 1 = ψ 1 (x 0) := congrFun hxe 1
    have h2 : x 1 = x 0 := by simpa using hx.periodic 0
    rw [← h1, h2]
  · intro hp
    refine ⟨fun t => ψ t p, ⟨fun t => hψ.hasDerivAt p t, ?_⟩, hψ.init p⟩
    have key : (fun t => ψ (t + 1) p) = fun t => ψ t p := by
      refine ODE_solution_unique_univ (K := K) (s := fun _ => Set.univ) (t₀ := (0 : ℝ))
        (fun t => (hX t).lipschitzOnWith) (fun t => ⟨?_, Set.mem_univ _⟩)
        (fun t => ⟨hψ.hasDerivAt p t, Set.mem_univ _⟩) ?_
      · have h := HasDerivAt.comp_add_const t 1 (hψ.hasDerivAt p (t + 1))
        rw [hXper] at h
        exact h
      · simp [hp, hψ.init]
    exact fun t => congrFun key t

end Orbits

section Nondegenerate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Definition 5.4.4, recalled in §6.1.**  A `1`-periodic orbit through `p` is
*nondegenerate* when the differential of the time-one map at `p` does not have
`1` as an eigenvalue, i.e. `det(Id − T_p ψ_1) ≠ 0`.  This is
`Chapter5.IsNondegenerateReturnMap` applied to `T_p ψ_1`. -/
def IsNondegenerateOrbit (ψ : ℝ → E → E) (p : E) : Prop :=
  IsNondegenerateReturnMap (fderiv ℝ (ψ 1) p)

omit [FiniteDimensional ℝ E] in
/-- A nondegenerate orbit has no nonzero fixed tangent vector — the form in which
the condition is used (and the reason a nonconstant orbit of an autonomous
system is always degenerate, Remark 6.3.5(3)). -/
theorem IsNondegenerateOrbit.eq_zero_of_fixed {ψ : ℝ → E → E} {p : E}
    (h : IsNondegenerateOrbit ψ p) {v : E} (hv : fderiv ℝ (ψ 1) p v = v) : v = 0 := by
  refine h.1 ?_
  simp [hv]

/-- **Proposition 6.1.5.**  If the vector field is `2π`-Lipschitz (the book
assumes `‖dX_H‖_{L²} < 2π`, and remarks that a Lipschitz bound suffices), then
the only `1`-periodic solutions are the constant ones, i.e. the critical points
of `H`.

The book's proof expands a periodic solution in Fourier series and applies
Parseval: `‖ẋ‖_{L²} ≤ (1/2π) ‖ẍ‖_{L²}` because `ẋ` has zero mean.  This is
Wirtinger's inequality, which Mathlib does not have (it has the Fourier basis of
`L²(S¹)` but not the Sobolev estimate). -/
theorem isConst_of_isPeriodicOrbit_of_lipschitz {X : E → E} {K : ℝ≥0}
    (_hX : LipschitzWith K X) (_hK : (K : ℝ) < 2 * Real.pi) {x : ℝ → E}
    (_hx : IsPeriodicOrbit (fun _ => X) x) (t : ℝ) : x t = x 0 := by
  sorry

end Nondegenerate

/-! ## The standard model `ℝ^{2n}`

From here on the symplectic manifold is `ℝ^{2n} = (l ⊕ l) → ℝ` with the standard
form `ω = stdForm l` of Example 5.1.2, the calibrated complex structure
`J₀ = stdJ l` of §5.5, and the metric `g(v,w) = ω(v, J₀ w) = v ⬝ᵥ w` it defines.
Hypotheses 6.2.1 and 6.2.2 hold trivially here (and on the torus quotient),
which is what makes the action functional well defined. -/

section Standard

variable {l : Type*} [DecidableEq l] [Fintype l]

/-! ### Elementary algebra of `ω` and `J₀` -/

/-- `ω(X, J₀ Y) = X ⬝ᵥ Y`: the metric calibrated by `J₀` is the Euclidean scalar
product (§5.5, used constantly in §6.4 and §6.5). -/
theorem stdForm_stdJ (X Y : (l ⊕ l) → ℝ) : stdForm l X (stdJ l Y) = X ⬝ᵥ Y := by
  rw [← calibratedMetric_apply]
  exact calibratedMetric_stdJ l X Y

/-- `J₀` is an isometry of the Euclidean metric.  This is why the two terms of
the energy integrand of §6.5.a agree on a solution. -/
theorem stdJ_dotProduct (X Y : (l ⊕ l) → ℝ) : stdJ l X ⬝ᵥ stdJ l Y = X ⬝ᵥ Y := by
  rw [← stdForm_stdJ, ← stdForm_stdJ]
  exact calibratedMetric_J (stdJ_isCalibrated l) X Y

/-- `ω(J₀ w, w) = −|w|²`: the sign that makes the action decrease along a Floer
trajectory. -/
theorem stdForm_stdJ_self (w : (l ⊕ l) → ℝ) : stdForm l (stdJ l w) w = -(w ⬝ᵥ w) := by
  rw [(stdForm_isSymplectic l).skew (stdJ l w) w, stdForm_stdJ]

omit [DecidableEq l] in
private theorem dot_self_nonneg (v : (l ⊕ l) → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-! ### Continuity and differentiability in the standard model -/

omit [DecidableEq l] in
private theorem continuous_dot {x y : ℝ → ((l ⊕ l) → ℝ)} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => x t ⬝ᵥ y t := by
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hx).mul ((continuous_apply i).comp hy)

omit [DecidableEq l] in
private theorem continuous_mulVec (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) {y : ℝ → ((l ⊕ l) → ℝ)}
    (hy : Continuous y) : Continuous fun t => M *ᵥ y t := by
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hy)

/-- `t ↦ ω(x(t), y(t))` is continuous when `x` and `y` are. -/
theorem continuous_stdForm {x y : ℝ → ((l ⊕ l) → ℝ)} (hx : Continuous x) (hy : Continuous y) :
    Continuous fun t => stdForm l (x t) (y t) := by
  simp only [stdForm_apply]
  exact continuous_dot hx (continuous_mulVec _ hy)

omit [DecidableEq l] in
private theorem hasDerivAt_mulVec (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) {y : ℝ → ((l ⊕ l) → ℝ)}
    {y' : (l ⊕ l) → ℝ} {t : ℝ} (hy : HasDerivAt y y' t) :
    HasDerivAt (fun τ => M *ᵥ y τ) (M *ᵥ y') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  have h : ∀ j : l ⊕ l, HasDerivAt (fun τ => y τ j) (y' j) t := fun j => hasDerivAt_pi.1 hy j
  have hsum := HasDerivAt.sum (fun j (_ : j ∈ (Finset.univ : Finset (l ⊕ l))) =>
    HasDerivAt.const_mul (M i j) (h j))
  have hfun : (∑ j ∈ (Finset.univ : Finset (l ⊕ l)), fun τ : ℝ => M i j * y τ j)
      = fun τ => (M *ᵥ y τ) i := by
    funext τ
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  rw [hfun] at hsum
  exact hsum

omit [DecidableEq l] in
private theorem hasDerivAt_dot {x y : ℝ → ((l ⊕ l) → ℝ)} {x' y' : (l ⊕ l) → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun τ => x τ ⬝ᵥ y τ) (x' ⬝ᵥ y t + x t ⬝ᵥ y') t := by
  have hxi : ∀ i : l ⊕ l, HasDerivAt (fun τ => x τ i) (x' i) t := fun i => hasDerivAt_pi.1 hx i
  have hyi : ∀ i : l ⊕ l, HasDerivAt (fun τ => y τ i) (y' i) t := fun i => hasDerivAt_pi.1 hy i
  have key := HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (l ⊕ l))) =>
    (hxi i).mul (hyi i))
  have hfun : (∑ i ∈ (Finset.univ : Finset (l ⊕ l)), (fun τ : ℝ => x τ i) * fun τ : ℝ => y τ i)
      = fun τ => x τ ⬝ᵥ y τ := by
    funext τ
    simp only [Finset.sum_apply, Pi.mul_apply, dotProduct]
  have hder : (∑ i ∈ (Finset.univ : Finset (l ⊕ l)), (x' i * y t i + x t i * y' i))
      = x' ⬝ᵥ y t + x t ⬝ᵥ y' := by
    simp only [dotProduct]
    exact Finset.sum_add_distrib
  rw [hfun, hder] at key
  exact key

/-- The product rule for a bilinear form: `d/dt ω(x,y) = ω(ẋ,y) + ω(x,ẏ)`. -/
theorem hasDerivAt_stdForm {x y : ℝ → ((l ⊕ l) → ℝ)} {x' y' : (l ⊕ l) → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun τ => stdForm l (x τ) (y τ)) (stdForm l x' (y t) + stdForm l (x t) y') t := by
  simp only [stdForm_apply]
  exact hasDerivAt_dot hx (hasDerivAt_mulVec _ hy)

/-- **Integration by parts on the circle.**  For `1`-periodic `C¹` loops,
`∫₀¹ ω(ẋ, y) + ∫₀¹ ω(x, ẏ) = 0`.

This is the step that turns the derivative of the disc integral `−∫_D u⋆ω` into
`∫₀¹ ω(ẋ(t), Y(t)) dt` in the proof of Proposition 6.3.4: the book performs it
with Cartan's formula and Stokes, and on `ℝ^{2n}` it reduces to this. -/
theorem integral_stdForm_byParts {x y x' y' : ℝ → ((l ⊕ l) → ℝ)}
    (hx : ∀ t, HasDerivAt x (x' t) t) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hcx : Continuous x) (hcy : Continuous y) (hcx' : Continuous x') (hcy' : Continuous y')
    (hpx : Function.Periodic x 1) (hpy : Function.Periodic y 1) :
    (∫ t in (0:ℝ)..1, stdForm l (x' t) (y t)) + (∫ t in (0:ℝ)..1, stdForm l (x t) (y' t)) = 0 := by
  have hderiv : ∀ t, HasDerivAt (fun τ => stdForm l (x τ) (y τ))
      (stdForm l (x' t) (y t) + stdForm l (x t) (y' t)) t := fun t =>
    hasDerivAt_stdForm (hx t) (hy t)
  have hc1 : Continuous fun t => stdForm l (x' t) (y t) := continuous_stdForm hcx' hcy
  have hc2 : Continuous fun t => stdForm l (x t) (y' t) := continuous_stdForm hcx hcy'
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((hc1.add hc2).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1)] at key
  rw [key]
  have h1 : x 1 = x 0 := by simpa using hpx 0
  have h2 : y 1 = y 0 := by simpa using hpy 0
  rw [h1, h2, sub_self]

/-! ### The Hamiltonian vector field in the standard model -/

/-- The Euclidean gradient of `x ↦ H(x, t)`, i.e. the vector of partial
derivatives of `H_t`.  Since the metric calibrated by `J₀` is the Euclidean one,
this is the `grad H_t` of §6.4. -/
noncomputable def hamGrad (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) (t : ℝ) (x : (l ⊕ l) → ℝ) :
    (l ⊕ l) → ℝ :=
  fun i => fderiv ℝ (fun y => H y t) x (Pi.single i 1)

/-- The time-dependent Hamiltonian vector field `X_t` of `H` on `ℝ^{2n}`
(Definition of §5.4, used from §6.1 on). -/
noncomputable def hamField (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) (t : ℝ) (x : (l ⊕ l) → ℝ) :
    (l ⊕ l) → ℝ :=
  timeDependentHamiltonianField (stdForm l) (stdForm_nondegenerate l) H t x

/-- **Hamilton's equations / the last formula of §5.5**: `X_t = J₀ · grad H_t`. -/
theorem hamField_eq_stdJ_grad (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) (t : ℝ) (x : (l ⊕ l) → ℝ) :
    hamField H t x = stdJ l (hamGrad H t x) := by
  have h := hamiltonianVector_stdForm (l := l) (fderiv ℝ (fun y => H y t) x).toLinearMap
  rw [stdJ_apply]
  exact h

/-- Equivalently `grad H_t = −J₀ X_t`; this is the form used to rewrite the
Floer equation. -/
theorem stdJ_hamField (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) (t : ℝ) (x : (l ⊕ l) → ℝ) :
    stdJ l (hamField H t x) = -hamGrad H t x := by
  rw [hamField_eq_stdJ_grad, (stdJ_isCalibrated l).sq]

/-- The defining property `ω(Y, X_t(x)) = (dH_t)_x(Y)` of the Hamiltonian vector
field, in the standard model. -/
theorem stdForm_hamField (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) (t : ℝ) (x Y : (l ⊕ l) → ℝ) :
    stdForm l Y (hamField H t x) = fderiv ℝ (fun y => H y t) x Y :=
  hamiltonianVector_spec (stdForm_isSymplectic l) _ Y

omit [Fintype l] in
/-- If `H` is `1`-periodic in time — which Remark 6.1.3 says can always be
arranged — then so is its gradient. -/
theorem hamGrad_periodic {H : ((l ⊕ l) → ℝ) → ℝ → ℝ} (hH : ∀ y t, H y (t + 1) = H y t)
    (t : ℝ) (x : (l ⊕ l) → ℝ) : hamGrad H (t + 1) x = hamGrad H t x := by
  have h : (fun z => H z (t + 1)) = fun z => H z t := funext fun z => hH z t
  show (fun i => fderiv ℝ (fun y => H y (t + 1)) x (Pi.single i 1))
      = fun i => fderiv ℝ (fun y => H y t) x (Pi.single i 1)
  rw [h]

/-- If `H` is `1`-periodic in time then so is `X_t`. -/
theorem hamField_periodic {H : ((l ⊕ l) → ℝ) → ℝ → ℝ} (hH : ∀ y t, H y (t + 1) = H y t)
    (t : ℝ) (x : (l ⊕ l) → ℝ) : hamField H (t + 1) x = hamField H t x := by
  rw [hamField_eq_stdJ_grad, hamField_eq_stdJ_grad, hamGrad_periodic hH]

end Standard

/-! ## §6.1 The Arnold conjecture -/

section Arnold

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- **Conjecture 6.1.2 (Arnold), for the torus `T^{2n} = ℝ^{2n}/ℤ^{2n}`.**

Let `H` be a time-dependent Hamiltonian on `ℝ^{2n}`, `1`-periodic in time and
invariant under the lattice `ℤ^{2n}` — that is, a time-dependent Hamiltonian on
the torus.  If all the `1`-periodic solutions of the associated Hamiltonian
system are nondegenerate, then their number is at least
`∑_i dim HM_i(T^{2n}; ℤ/2) = 2^{2n}`.

The conclusion is phrased as: there are at least `2^{2n}` fixed points of the
time-one map, pairwise incongruent modulo the lattice.  (The contractible loops
on the torus are exactly the genuinely `1`-periodic solutions upstairs, so no
further condition is needed.)

The general conjecture — an arbitrary compact symplectic manifold `W` and the
sum of the `ℤ/2` Betti numbers of its Morse homology — cannot be stated: there
are no symplectic manifolds in Mathlib and `HM_*` of Chapter 4 is not available
as a functor of `W`.  This torus case is the one Conley and Zehnder proved. -/
theorem arnold_conjecture_torus (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hHt : ∀ y t, H y (t + 1) = H y t)
    (_hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t)
    (ψ : ℝ → ((l ⊕ l) → ℝ) → ((l ⊕ l) → ℝ)) (_hψ : IsFlow (hamField H) ψ)
    (_hnd : ∀ p, ψ 1 p = p → IsNondegenerateOrbit ψ p) :
    ∃ S : Finset ((l ⊕ l) → ℝ), 2 ^ (2 * Fintype.card l) ≤ S.card ∧
      (∀ p ∈ S, ψ 1 p = p) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ k : (l ⊕ l) → ℤ, q ≠ p + fun i => (k i : ℝ) := by
  sorry

end Arnold

/-! ## §6.3 The action functional

On `ℝ^{2n}` the disc integral `−∫_D u⋆ω` of the definition of `A_H` can be
written on the boundary loop: for any primitive `λ` of the constant form `ω`,
`∫_D u⋆ω = ∫_{S¹} x⋆λ`.  With `λ_x(v) = ½ ω(x, v)` — which differs from the
`∑ p_i dq_i` of Example 6.3.2 by an exact form, hence has the same integral over
a loop — this gives the closed formula used below.  It is the physicists' action
integral `∫₀¹ (H_t dt − p dq)`. -/

section Action

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- **§6.3.b, Example 6.3.2.**  The action functional of `H` on the space of
`1`-periodic loops in `ℝ^{2n}`:
`A_H(x) = ∫₀¹ (H_t(x(t)) − ½ ω(x(t), ẋ(t))) dt`. -/
noncomputable def action (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) (x : ℝ → ((l ⊕ l) → ℝ)) : ℝ :=
  ∫ t in (0:ℝ)..1, (H (x t) t - (1 / 2) * stdForm l (x t) (deriv x t))

/-- **§6.7.b, the action form `α_H`.**  The `1`-form on the loop space whose
value on a tangent vector `Y` along `x` is
`(α_H)_x(Y) = ∫₀¹ ω(ẋ(t) − X_t(x(t)), Y(t)) dt`.

Proposition 6.3.4 computes `dA_H = α_H`; §6.7 explains that on a general
symplectic manifold only `α_H` survives, as a closed but possibly non-exact
form. -/
noncomputable def actionForm (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) (x Y : ℝ → ((l ⊕ l) → ℝ)) : ℝ :=
  ∫ t in (0:ℝ)..1, stdForm l (deriv x t - hamField H t (x t)) (Y t)

/-! ### The fundamental lemma of the calculus of variations -/

private theorem eq_zero_of_integral_eq_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ t, 0 ≤ f t) (h : (∫ t in (0:ℝ)..1, f t) = 0) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : f t = 0 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := fun a b =>
    hf.intervalIntegrable a b
  have hFzero : ∀ τ ∈ Set.Icc (0:ℝ) 1, (∫ σ in (0:ℝ)..τ, f σ) = 0 := by
    intro τ hτ
    have hadd : (∫ σ in (0:ℝ)..τ, f σ) + (∫ σ in τ..(1:ℝ), f σ) = ∫ σ in (0:ℝ)..(1:ℝ), f σ :=
      intervalIntegral.integral_add_adjacent_intervals (hint 0 τ) (hint τ 1)
    have h1 : 0 ≤ ∫ σ in (0:ℝ)..τ, f σ :=
      intervalIntegral.integral_nonneg hτ.1 fun u _ => hpos u
    have h2 : 0 ≤ ∫ σ in τ..(1:ℝ), f σ :=
      intervalIntegral.integral_nonneg hτ.2 fun u _ => hpos u
    rw [h] at hadd
    linarith
  have hIoo : Set.EqOn f (fun _ => (0:ℝ)) (Set.Ioo (0:ℝ) 1) := by
    intro τ hτ
    have hEq : (fun τ => ∫ σ in (0:ℝ)..τ, f σ) =ᶠ[nhds τ] fun _ => (0:ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with u hu
      exact hFzero u (Set.Ioo_subset_Icc_self hu)
    have hd : deriv (fun τ => ∫ σ in (0:ℝ)..τ, f σ) τ = 0 := by
      rw [hEq.deriv_eq]
      simp
    rw [Continuous.deriv_integral f hf 0 τ] at hd
    exact hd
  have hIcc : Set.EqOn f (fun _ => (0:ℝ)) (Set.Icc (0:ℝ) 1) := by
    have hcl := hIoo.closure hf continuous_const
    rwa [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hcl
  exact hIcc ht

/-- **The fundamental lemma of the calculus of variations**, in the form used in
the proof of Proposition 6.3.4: if `∫₀¹ ω(v(t), Y(t)) dt = 0` for every
continuous vector field `Y` along the loop, then `v` vanishes on `[0,1]`.

The proof is the book's own remark that `ω` is nondegenerate, made quantitative:
test against `Y = J₀ v`, for which the integrand is `|v|²` because `J₀` is
calibrated by `ω`. -/
theorem eq_zero_of_forall_integral_stdForm_eq_zero {v : ℝ → ((l ⊕ l) → ℝ)} (hv : Continuous v)
    (h : ∀ Y : ℝ → ((l ⊕ l) → ℝ), Continuous Y → (∫ t in (0:ℝ)..1, stdForm l (v t) (Y t)) = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : v t = 0 := by
  have hY : Continuous fun τ => stdJ l (v τ) := by
    simpa only [stdJ_apply] using continuous_mulVec (Matrix.J l ℝ) hv
  have hz := h _ hY
  have hcong : Set.EqOn (fun τ => stdForm l (v τ) (stdJ l (v τ))) (fun τ => v τ ⬝ᵥ v τ)
      (Set.uIcc (0:ℝ) 1) := fun τ _ => stdForm_stdJ _ _
  rw [intervalIntegral.integral_congr hcong] at hz
  have hsq := eq_zero_of_integral_eq_zero (continuous_dot hv hv)
    (fun τ => dot_self_nonneg _) hz ht
  exact dotProduct_self_eq_zero.mp hsq

private theorem eq_zero_of_periodic_of_eqOn {F : Type*} [NormedAddCommGroup F] {v : ℝ → F}
    (hv : Function.Periodic v 1) (h : ∀ t ∈ Set.Icc (0:ℝ) 1, v t = 0) (t : ℝ) : v t = 0 := by
  have key := hv.sub_int_mul_eq (x := t) ⌊t⌋
  have hEq : t - (⌊t⌋ : ℝ) * 1 = Int.fract t := by
    rw [mul_one]
    rfl
  rw [hEq] at key
  rw [← key]
  exact h _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

private theorem deriv_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x x' : ℝ → F} (hx : ∀ t, HasDerivAt x (x' t) t) (hper : Function.Periodic x 1) :
    Function.Periodic x' 1 := by
  intro t
  have h1 : HasDerivAt (fun τ => x (τ + 1)) (x' (t + 1)) t :=
    HasDerivAt.comp_add_const t 1 (hx (t + 1))
  have h2 : (fun τ => x (τ + 1)) = x := funext fun τ => hper τ
  rw [h2] at h1
  exact h1.unique (hx t)

/-- **Proposition 6.3.4.**  A loop `x` is a critical point of the action
functional — equivalently, the action form `α_H` vanishes on every tangent
vector at `x` — if and only if `t ↦ x(t)` is a `1`-periodic solution of the
Hamiltonian system `ẋ = X_t(x)`.

This is the whole point of the action functional and is proved outright here.
The book's argument is exactly the one formalized: `(dA_H)_x(Y)` equals
`∫₀¹ ω(ẋ − X_t(x), Y) dt`, and by nondegeneracy of `ω` this vanishes for all `Y`
precisely when `ẋ = X_t(x)`.  The analytic half — that `dA_H` really is `α_H` —
is `hasDerivAt_action` below. -/
theorem actionForm_eq_zero_iff (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hHper : ∀ y t, H y (t + 1) = H y t) {x x' : ℝ → ((l ⊕ l) → ℝ)}
    (hx : ∀ t, HasDerivAt x (x' t) t) (hx' : Continuous x') (hper : Function.Periodic x 1)
    (hXcont : Continuous fun t => hamField H t (x t)) :
    (∀ Y : ℝ → ((l ⊕ l) → ℝ), Continuous Y → actionForm H x Y = 0)
      ↔ IsPeriodicOrbit (hamField H) x := by
  have hderiv : ∀ t, deriv x t = x' t := fun t => (hx t).deriv
  constructor
  · intro h
    have hvcont : Continuous fun t => x' t - hamField H t (x t) := hx'.sub hXcont
    have hIcc : ∀ t ∈ Set.Icc (0:ℝ) 1, x' t - hamField H t (x t) = 0 := by
      intro t ht
      refine eq_zero_of_forall_integral_stdForm_eq_zero hvcont ?_ ht
      intro Y hY
      have := h Y hY
      simp only [actionForm] at this
      calc (∫ t in (0:ℝ)..1, stdForm l (x' t - hamField H t (x t)) (Y t))
          = ∫ t in (0:ℝ)..1, stdForm l (deriv x t - hamField H t (x t)) (Y t) :=
            intervalIntegral.integral_congr fun τ _ => by rw [hderiv]
        _ = 0 := this
    have hvper : Function.Periodic (fun t => x' t - hamField H t (x t)) 1 := by
      intro t
      have h1 : x' (t + 1) = x' t := deriv_periodic hx hper t
      have h2 : x (t + 1) = x t := hper t
      simp only [h1, h2, hamField_periodic hHper]
    have hzero : ∀ t, x' t - hamField H t (x t) = 0 :=
      eq_zero_of_periodic_of_eqOn hvper hIcc
    refine ⟨fun t => ?_, hper⟩
    have := sub_eq_zero.mp (hzero t)
    rw [← this]
    exact hx t
  · intro horb Y _
    simp only [actionForm]
    have : ∀ t, deriv x t - hamField H t (x t) = 0 := by
      intro t
      rw [(horb.hasDerivAt t).deriv, sub_self]
    simp [this]

/-! ### Partial derivatives of a map `ℝ × S¹ → ℝ^{2n}` -/

end Action

section Partials

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `∂u/∂s`, the derivative in the "flow" direction. -/
noncomputable def dS (u : ℝ → ℝ → F) (s t : ℝ) : F := deriv (fun σ => u σ t) s

/-- `∂u/∂t`, the derivative in the "loop" direction. -/
noncomputable def dT (u : ℝ → ℝ → F) (s t : ℝ) : F := deriv (u s) t

/-- A smooth `1`-parameter family of `1`-periodic loops, i.e. a path in the loop
space `LW` of §6.3.a.  Mathlib has no loop space, so a path in it is recorded
here as a map `ℝ × S¹ → ℝ^{2n}` with the differentiability and periodicity the
book uses. -/
structure IsLoopVariation (u : ℝ → ℝ → F) : Prop where
  /-- Each `u(s, ·)` is a loop. -/
  periodic : ∀ s, Function.Periodic (u s) 1
  /-- `∂u/∂s` exists. -/
  hasDerivAt_s : ∀ s t, HasDerivAt (fun σ => u σ t) (dS u s t) s
  /-- `∂u/∂t` exists. -/
  hasDerivAt_t : ∀ s t, HasDerivAt (u s) (dT u s t) t
  /-- `u` is continuous. -/
  continuous : Continuous fun p : ℝ × ℝ => u p.1 p.2
  /-- `∂u/∂s` is continuous. -/
  continuous_s : Continuous fun p : ℝ × ℝ => dS u p.1 p.2
  /-- `∂u/∂t` is continuous. -/
  continuous_t : Continuous fun p : ℝ × ℝ => dT u p.1 p.2

/-- A **smooth** `1`-parameter family of `1`-periodic loops: an
`IsLoopVariation` whose mixed second partial derivative also exists, is
continuous, and is symmetric.

`IsLoopVariation` records only the two first-order partials, which is all the
statement of the Floer equation needs.  The first variation of the action
(`hasDerivAt_action`) needs strictly more: differentiating
`σ ↦ ∫₀¹ ½ ω(u(σ,t), ∂u/∂t(σ,t)) dt` under the integral sign produces the term
`ω(u, ∂²u/∂σ∂t)`, and the integration by parts that removes it needs
`∂²u/∂σ∂t = ∂²u/∂t∂σ` together with the continuity of that mixed partial.  The
book's variations are `C^∞` families, so assuming this is faithful rather than
a weakening; it is recorded as a separate structure so that the definition of
the Floer equation itself keeps the weaker hypothesis. -/
structure IsSmoothLoopVariation (u : ℝ → ℝ → F) : Prop extends IsLoopVariation u where
  /-- `∂²u/∂σ∂t` exists. -/
  hasDerivAt_st : ∀ s t, HasDerivAt (fun σ => dT u σ t) (dS (dT u) s t) s
  /-- `∂²u/∂t∂σ` exists and the two mixed partials agree (Schwarz). -/
  hasDerivAt_ts : ∀ s t, HasDerivAt (dS u s) (dS (dT u) s t) t
  /-- The mixed partial is continuous. -/
  continuous_st : Continuous fun p : ℝ × ℝ => dS (dT u) p.1 p.2

end Partials

/-! ## §6.4 The gradient of the action functional, and the Floer equation

The metric on the loop space is `⟪Y, Z⟫ = ∫₀¹ g(Y(t), Z(t)) dt` with
`g(X,Y) = ω(X, J Y)`.  The gradient of `A_H` for this metric is
`(grad_x A_H)(t) = J(ẋ(t)) + grad H_t(x(t))`, and the trajectories of its
opposite are the solutions of the **Floer equation**

`∂u/∂s + J(u) ∂u/∂t + grad H_t(u) = 0`. -/

section Floer

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- **§6.4, the Floer equation.**  A solution is a smooth family of loops
`u : ℝ × S¹ → ℝ^{2n}` satisfying `∂u/∂s + J₀(∂u/∂t) + grad H_t(u) = 0`. -/
structure IsFloerSolution (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) (u : ℝ → ℝ → ((l ⊕ l) → ℝ)) : Prop
    extends IsSmoothLoopVariation u where
  /-- The Floer equation. -/
  floer : ∀ s t, dS u s t + stdJ l (dT u s t) + hamGrad H t (u s t) = 0

/-- The Floer equation rewritten as `∂u/∂t − X_t(u) = J₀(∂u/∂s)`.  This is the
form in which the energy identity and the decrease of the action are read off:
applying `J₀` to the equation and using `J₀² = −Id` and `X_t = J₀ grad H_t`. -/
theorem floer_eq (H : ((l ⊕ l) → ℝ) → ℝ → ℝ) {u : ℝ → ℝ → ((l ⊕ l) → ℝ)}
    (hu : IsFloerSolution H u) (s t : ℝ) :
    dT u s t - hamField H t (u s t) = stdJ l (dS u s t) := by
  have key : ∀ a b c : (l ⊕ l) → ℝ, a + -b + c = 0 → b - c = a := by
    intro a b c hab
    have h' : b - c - a = -(a + -b + c) := by abel
    rw [hab, neg_zero] at h'
    exact sub_eq_zero.mp h'
  have h := congrArg (stdJ l) (hu.floer s t)
  rw [map_add, map_add, map_zero, (stdJ_isCalibrated l).sq, ← hamField_eq_stdJ_grad] at h
  exact key _ _ _ h

/-- **Remark 6.4.1(2).**  A solution that does not depend on `s` is a
`1`-periodic orbit of the Hamiltonian system: the stationary trajectories of the
gradient flow are the critical points of the action functional. -/
theorem isPeriodicOrbit_of_dS_eq_zero (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u) (h : ∀ s t, dS u s t = 0) (s : ℝ) :
    IsPeriodicOrbit (hamField H) (u s) := by
  refine ⟨fun t => ?_, hu.periodic s⟩
  have h1 := floer_eq H hu s t
  rw [h s t, map_zero, sub_eq_zero] at h1
  rw [← h1]
  exact hu.hasDerivAt_t s t

/-- **Remark 6.4.1(2)**, converse.  A `1`-periodic orbit, seen as an
`s`-independent map, is a solution of the Floer equation. -/
theorem isFloerSolution_of_isPeriodicOrbit (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    {x : ℝ → ((l ⊕ l) → ℝ)} (hx : IsPeriodicOrbit (hamField H) x)
    (hXcont : Continuous fun t => hamField H t (x t)) :
    IsFloerSolution H (fun _ t => x t) := by
  have hdT : ∀ s t, dT (fun _ t => x t) s t = hamField H t (x t) :=
    fun _ t => (hx.hasDerivAt t).deriv
  have hdS : ∀ s t, dS (fun (_ : ℝ) (t : ℝ) => x t) s t = 0 := by
    intro s t
    simp [dS]
  have hcx : Continuous x :=
    continuous_iff_continuousAt.mpr fun t => (hx.hasDerivAt t).differentiableAt.continuousAt
  have hconst : ∀ t : ℝ, (fun _ : ℝ => dT (fun (_ : ℝ) (t : ℝ) => x t) 0 t)
      = fun σ : ℝ => dT (fun (_ : ℝ) (t : ℝ) => x t) σ t := by
    intro t
    exact funext fun σ => by rw [hdT σ t, hdT 0 t]
  have hdST : ∀ s t, dS (dT fun (_ : ℝ) (t : ℝ) => x t) s t = 0 := by
    intro s t
    show deriv (fun σ => dT (fun (_ : ℝ) (t : ℝ) => x t) σ t) s = 0
    rw [← hconst t]
    exact deriv_const s _
  have hdSfun : ∀ s : ℝ, dS (fun (_ : ℝ) (t : ℝ) => x t) s
      = fun _ : ℝ => (0 : (l ⊕ l) → ℝ) := fun s => funext fun t => hdS s t
  refine ⟨⟨⟨fun s => hx.periodic, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro s t
    rw [hdS s t]
    exact hasDerivAt_const s (x t)
  · intro s t
    rw [hdT s t]
    exact hx.hasDerivAt t
  · exact hcx.comp continuous_snd
  · simp only [hdS]
    exact continuous_const
  · simp only [hdT]
    exact hXcont.comp continuous_snd
  · intro s t
    rw [hdST s t, ← hconst t]
    exact hasDerivAt_const s _
  · intro s t
    rw [hdST s t, hdSfun s]
    exact hasDerivAt_const t _
  · simp only [hdST]
    exact continuous_const
  · intro s t
    rw [hdS, hdT, hamField_eq_stdJ_grad, (stdJ_isCalibrated l).sq]
    abel

/-- **Remark 6.4.1(1).**  If `H` does not depend on `t`, the solutions that do
not depend on `t` either satisfy `du/ds + grad H(u) = 0`: they are the
trajectories of the negative gradient of `H`, the objects of Part I. -/
theorem gradient_flow_of_dT_eq_zero (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u) (h : ∀ s t, dT u s t = 0)
    (s t : ℝ) : dS u s t + hamGrad H t (u s t) = 0 := by
  have := hu.floer s t
  rw [h s t, map_zero, add_zero] at this
  exact this

/-- **Remark 6.4.1(3).**  For `H = 0` the Floer equation is the Cauchy–Riemann
equation `∂u/∂s + J₀ ∂u/∂t = 0`: the solutions are the `J`-holomorphic curves of
Gromov. -/
theorem floer_zero_hamiltonian {u : ℝ → ℝ → ((l ⊕ l) → ℝ)}
    (hu : IsFloerSolution (fun _ _ => (0:ℝ)) u) (s t : ℝ) :
    dS u s t + stdJ l (dT u s t) = 0 := by
  have h := hu.floer s t
  have hg : hamGrad (fun (_ : (l ⊕ l) → ℝ) (_ : ℝ) => (0:ℝ)) t (u s t) = 0 := by
    funext i
    simp [hamGrad]
  rw [hg, add_zero] at h
  exact h

/-- **Remark 6.5.12.**  The additive group `ℝ` acts on the space of solutions by
translation in `s`, `(u · σ)(s,t) = u(s + σ, t)`, exactly as for a gradient
flow. -/
theorem IsFloerSolution.translate {H : ((l ⊕ l) → ℝ) → ℝ → ℝ} {u : ℝ → ℝ → ((l ⊕ l) → ℝ)}
    (hu : IsFloerSolution H u) (σ : ℝ) : IsFloerSolution H fun s t => u (s + σ) t := by
  have hdS : ∀ s t, dS (fun s t => u (s + σ) t) s t = dS u (s + σ) t := by
    intro s t
    simp only [dS]
    exact deriv_comp_add_const (fun s => u s t) σ s
  have hdT : ∀ s t, dT (fun s t => u (s + σ) t) s t = dT u (s + σ) t := fun s t => rfl
  have hdST : ∀ s t, dS (dT fun s t => u (s + σ) t) s t = dS (dT u) (s + σ) t := by
    intro s t
    simp only [dS]
    exact deriv_comp_add_const (fun s' => dT u s' t) σ s
  have hdSfun : ∀ s : ℝ, dS (fun s t => u (s + σ) t) s = dS u (s + σ) :=
    fun s => funext fun t => hdS s t
  refine ⟨⟨⟨fun s => hu.periodic (s + σ), ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro s t
    rw [hdS s t]
    exact HasDerivAt.comp_add_const s σ (hu.hasDerivAt_s (s + σ) t)
  · intro s t
    rw [hdT s t]
    exact hu.hasDerivAt_t (s + σ) t
  · exact hu.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  · simp only [hdS]
    exact hu.continuous_s.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  · simp only [hdT]
    exact hu.continuous_t.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  · intro s t
    rw [hdST s t]
    exact HasDerivAt.comp_add_const s σ (hu.hasDerivAt_st (s + σ) t)
  · intro s t
    rw [hdST s t, hdSfun s]
    exact hu.hasDerivAt_ts (s + σ) t
  · simp only [hdST]
    exact hu.continuous_st.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  · intro s t
    rw [hdS s t, hdT s t]
    exact hu.floer (s + σ) t

end Floer

/-! ## §6.5.a Energy

The energy of a solution is the integral of the square of the norm of the
gradient of `A_H` along it, `E(u) = ∫_{ℝ × S¹} |∂u/∂s|² ds dt`.  The book also
writes it as `½ ∫ (|∂u/∂s|² + |∂u/∂t − X_t(u)|²)`; on a solution the two terms
agree, which is the content of `energyDensity_eq_of_floer`. -/

section Energy

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The energy density `|∂u/∂s|²` for the metric calibrated by `J₀`, which on
`ℝ^{2n}` is the Euclidean one. -/
noncomputable def energyDensity (u : ℝ → ℝ → ((l ⊕ l) → ℝ)) (s t : ℝ) : ℝ :=
  dS u s t ⬝ᵥ dS u s t

/-- **§6.5.a.**  The energy `E(u) = ∫_ℝ ∫_{S¹} |∂u/∂s|² dt ds`. -/
noncomputable def energy (u : ℝ → ℝ → ((l ⊕ l) → ℝ)) : ℝ :=
  ∫ s : ℝ, ∫ t in (0:ℝ)..1, energyDensity u s t

omit [DecidableEq l] in
theorem energyDensity_nonneg (u : ℝ → ℝ → ((l ⊕ l) → ℝ)) (s t : ℝ) :
    0 ≤ energyDensity u s t := dot_self_nonneg _

omit [DecidableEq l] in
/-- **Remark 6.5.2(1).**  The energy is nonnegative. -/
theorem energy_nonneg (u : ℝ → ℝ → ((l ⊕ l) → ℝ)) : 0 ≤ energy u := by
  refine MeasureTheory.integral_nonneg fun s => ?_
  exact intervalIntegral.integral_nonneg zero_le_one fun t _ => energyDensity_nonneg u s t

omit [DecidableEq l] in
theorem energyDensity_eq_zero_iff (u : ℝ → ℝ → ((l ⊕ l) → ℝ)) (s t : ℝ) :
    energyDensity u s t = 0 ↔ dS u s t = 0 :=
  dotProduct_self_eq_zero

/-- **§6.5.a.**  On a solution the two terms of the energy integrand agree:
`|∂u/∂s|² = |∂u/∂t − X_t(u)|²`, because `J₀` is an isometry of the calibrated
metric.  This is why `E(u) = ½ ∫ (|∂u/∂s|² + |∂u/∂t − X_t(u)|²)` equals
`∫ |∂u/∂s|²`. -/
theorem energyDensity_eq_of_floer (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u) (s t : ℝ) :
    energyDensity u s t
      = (dT u s t - hamField H t (u s t)) ⬝ᵥ (dT u s t - hamField H t (u s t)) := by
  rw [floer_eq H hu s t, stdJ_dotProduct]
  rfl

omit [DecidableEq l] in
/-- **Remark 6.5.2(2)**, easy direction: an `s`-independent solution has zero
energy. -/
theorem energy_eq_zero_of_dS_eq_zero {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (h : ∀ s t, dS u s t = 0) :
    energy u = 0 := by
  simp [energy, energyDensity, h]

/-- **Remark 6.5.2(2)**, hard direction: a solution of zero energy does not
depend on `s`, hence is a `1`-periodic orbit.

What is missing is purely measure-theoretic: a nonnegative continuous function
on `ℝ × S¹` whose (double) integral vanishes is identically zero.  Mathlib has
the `a.e.` statement `MeasureTheory.integral_eq_zero_iff_of_nonneg` but the step
from "`a.e.` zero" to "zero" for a continuous function, together with the
integrability of the inner integral in `s` needed to apply it, has not been
carried out here.  The one-variable case is proved above as
`eq_zero_of_integral_eq_zero`. -/
theorem dS_eq_zero_of_energy_eq_zero {u : ℝ → ℝ → ((l ⊕ l) → ℝ)}
    (_hc : Continuous fun p : ℝ × ℝ => dS u p.1 p.2)
    (_hi : MeasureTheory.Integrable fun s => ∫ t in (0:ℝ)..1, energyDensity u s t)
    (_h : energy u = 0) (s t : ℝ) : dS u s t = 0 := by
  sorry

end Energy

/-! ## §6.3 / §6.5 The first variation, and the decrease of the action -/

section Variation

variable {l : Type*} [DecidableEq l] [Fintype l]

/-! ### Auxiliary continuity and differentiability lemmas

The lemmas of §6.3 above are stated for curves `ℝ → ℝ^{2n}`; differentiating
under the integral sign needs the same facts jointly in `(σ, t)`, so they are
restated here over an arbitrary topological parameter space. -/

omit [DecidableEq l] in
private theorem continuous_dot₂ {α : Type*} [TopologicalSpace α] {x y : α → ((l ⊕ l) → ℝ)}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun a => x a ⬝ᵥ y a := by
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hx).mul ((continuous_apply i).comp hy)

omit [DecidableEq l] in
private theorem continuous_mulVec₂ {α : Type*} [TopologicalSpace α]
    (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) {y : α → ((l ⊕ l) → ℝ)} (hy : Continuous y) :
    Continuous fun a => M *ᵥ y a := by
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hy)

private theorem continuous_stdForm₂ {α : Type*} [TopologicalSpace α] {x y : α → ((l ⊕ l) → ℝ)}
    (hx : Continuous x) (hy : Continuous y) :
    Continuous fun a => stdForm l (x a) (y a) := by
  simp only [stdForm_apply]
  exact continuous_dot₂ hx (continuous_mulVec₂ _ hy)

omit [DecidableEq l] in
/-- A `C¹` time-dependent Hamiltonian is differentiable in the space variable at
each fixed time, with differential the restriction of `dH` to the first factor. -/
private theorem hasFDerivAt_partial {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) (x : (l ⊕ l) → ℝ) (t : ℝ) :
    HasFDerivAt (fun y : (l ⊕ l) → ℝ => H y t)
      ((fderiv ℝ (fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) (x, t)).comp
        (ContinuousLinearMap.inl ℝ ((l ⊕ l) → ℝ) ℝ)) x := by
  have hin : HasFDerivAt (fun y : (l ⊕ l) → ℝ => (y, t))
      (ContinuousLinearMap.inl ℝ ((l ⊕ l) → ℝ) ℝ) x := hasFDerivAt_prodMk_left x t
  have hG : HasFDerivAt (fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
      (fderiv ℝ (fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) (x, t)) (x, t) :=
    (hH.differentiable one_ne_zero (x, t)).hasFDerivAt
  have hcomp := hG.comp x hin
  exact hcomp

omit [DecidableEq l] in
private theorem differentiableAt_partial {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) (x : (l ⊕ l) → ℝ) (t : ℝ) :
    DifferentiableAt ℝ (fun y => H y t) x := (hasFDerivAt_partial hH x t).differentiableAt

private theorem hamGrad_apply_eq {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) (t : ℝ) (x : (l ⊕ l) → ℝ)
    (i : l ⊕ l) :
    hamGrad H t x i
      = fderiv ℝ (fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) (x, t)
          ((Pi.single i 1 : (l ⊕ l) → ℝ), (0 : ℝ)) := by
  show fderiv ℝ (fun y => H y t) x (Pi.single i 1) = _
  rw [(hasFDerivAt_partial hH x t).fderiv]
  simp

/-- `X_t(x)` is jointly continuous in `(t, x)` when `H` is `C¹`. -/
private theorem continuous_hamField {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {α : Type*} [TopologicalSpace α] {x : α → ((l ⊕ l) → ℝ)} {τ : α → ℝ}
    (hx : Continuous x) (hτ : Continuous τ) :
    Continuous fun a => hamField H (τ a) (x a) := by
  have hfd : Continuous (fderiv ℝ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) :=
    hH.continuous_fderiv one_ne_zero
  have hg : Continuous fun a => hamGrad H (τ a) (x a) := by
    refine continuous_pi fun i => ?_
    simp only [hamGrad_apply_eq hH]
    have h1 : Continuous fun a => fderiv ℝ (fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) (x a, τ a) :=
      hfd.comp (hx.prodMk hτ)
    exact h1.clm_apply continuous_const
  simp only [hamField_eq_stdJ_grad, stdJ_apply]
  exact continuous_mulVec₂ _ hg

/-- Joint continuity of the `σ`-derivative of that integrand. -/
private theorem continuous_actionIntegrandDeriv {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsSmoothLoopVariation u) :
    Continuous fun p : ℝ × ℝ => stdForm l (dS u p.1 p.2) (hamField H p.2 (u p.1 p.2))
      - 1 / 2 * (stdForm l (dS u p.1 p.2) (dT u p.1 p.2)
          + stdForm l (u p.1 p.2) (dS (dT u) p.1 p.2)) :=
  (continuous_stdForm₂ hu.continuous_s
      (continuous_hamField hH hu.continuous continuous_snd)).sub
    (continuous_const.mul ((continuous_stdForm₂ hu.continuous_s hu.continuous_t).add
      (continuous_stdForm₂ hu.continuous hu.continuous_st)))

/-- The `σ`-derivative of the integrand of the action, pointwise in `t`:
`dH_t(∂u/∂s) − ½ ω(∂u/∂s, ∂u/∂t) − ½ ω(u, ∂²u/∂σ∂t)`, with the first term
rewritten as `ω(∂u/∂s, X_t(u))` by `stdForm_hamField`. -/
private theorem hasDerivAt_actionIntegrand {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsSmoothLoopVariation u) (σ t : ℝ) :
    HasDerivAt (fun σ' => H (u σ' t) t - 1 / 2 * stdForm l (u σ' t) (dT u σ' t))
      (stdForm l (dS u σ t) (hamField H t (u σ t))
        - 1 / 2 * (stdForm l (dS u σ t) (dT u σ t)
            + stdForm l (u σ t) (dS (dT u) σ t))) σ := by
  have h1 : HasDerivAt (fun σ' => H (u σ' t) t)
      (stdForm l (dS u σ t) (hamField H t (u σ t))) σ := by
    rw [stdForm_hamField]
    have hc := ((differentiableAt_partial hH (u σ t) t).hasFDerivAt).comp_hasDerivAt σ
      (hu.hasDerivAt_s σ t)
    exact hc
  have h2 : HasDerivAt (fun σ' => stdForm l (u σ' t) (dT u σ' t))
      (stdForm l (dS u σ t) (dT u σ t) + stdForm l (u σ t) (dS (dT u) σ t)) σ :=
    hasDerivAt_stdForm (hu.hasDerivAt_s σ t) (hu.hasDerivAt_st σ t)
  have h3 := h1.sub (HasDerivAt.const_mul (1 / 2 : ℝ) h2)
  exact h3

/-- The integration by parts that turns the `σ`-derivative of the action
integrand into the action form.  With `x = u_s` and `Y = ∂u/∂s`,
`integral_stdForm_byParts` gives `∫ ω(ẋ, Y) + ∫ ω(x, Ẏ) = 0`; since
`Ẏ = ∂²u/∂σ∂t` by the symmetry of the mixed partials, this turns
`−½ ∫ ω(∂u/∂s, ∂u/∂t) − ½ ∫ ω(u, ∂²u/∂σ∂t)` into `∫ ω(∂u/∂t, ∂u/∂s)`. -/
private theorem actionForm_eq_integral (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsSmoothLoopVariation u) (s : ℝ) :
    actionForm H (u s) (dS u s)
      = ∫ t in (0:ℝ)..1, (stdForm l (dS u s t) (hamField H t (u s t))
          - 1 / 2 * (stdForm l (dS u s t) (dT u s t)
              + stdForm l (u s t) (dS (dT u) s t))) := by
  have hp : Continuous fun t : ℝ => ((s : ℝ), t) := continuous_const.prodMk continuous_id
  have hcu1 : Continuous (u s) := hu.continuous.comp hp
  have hcs1 : Continuous (dS u s) := hu.continuous_s.comp hp
  have hct1 : Continuous (dT u s) := hu.continuous_t.comp hp
  have hcst1 : Continuous (dS (dT u) s) := hu.continuous_st.comp hp
  have hcX1 : Continuous fun t : ℝ => hamField H t (u s t) :=
    (continuous_hamField hH hu.continuous continuous_snd).comp hp
  have hper1 : Function.Periodic (dS u s) 1 := by
    intro t
    have he : (fun σ => u σ (t + 1)) = fun σ => u σ t := funext fun σ => hu.periodic σ t
    show deriv (fun σ => u σ (t + 1)) s = deriv (fun σ => u σ t) s
    rw [he]
  have hbp := integral_stdForm_byParts (x := u s) (y := dS u s) (x' := dT u s)
    (y' := dS (dT u) s) (hu.hasDerivAt_t s) (hu.hasDerivAt_ts s) hcu1 hcs1 hct1 hcst1
    (hu.periodic s) hper1
  have hskew : (∫ t in (0:ℝ)..1, stdForm l (dT u s t) (dS u s t))
      = -∫ t in (0:ℝ)..1, stdForm l (dS u s t) (dT u s t) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => (stdForm_isSymplectic l).skew _ _
  rw [hskew] at hbp
  have hcb : (∫ t in (0:ℝ)..1, stdForm l (u s t) (dS (dT u) s t))
      = ∫ t in (0:ℝ)..1, stdForm l (dS u s t) (dT u s t) := by linarith
  have hIa : IntervalIntegrable (fun t => stdForm l (dS u s t) (hamField H t (u s t)))
      MeasureTheory.volume 0 1 := (continuous_stdForm₂ hcs1 hcX1).intervalIntegrable 0 1
  have hIb : IntervalIntegrable (fun t => stdForm l (dS u s t) (dT u s t))
      MeasureTheory.volume 0 1 := (continuous_stdForm₂ hcs1 hct1).intervalIntegrable 0 1
  have hIc : IntervalIntegrable (fun t => stdForm l (u s t) (dS (dT u) s t))
      MeasureTheory.volume 0 1 := (continuous_stdForm₂ hcu1 hcst1).intervalIntegrable 0 1
  have hI2 : IntervalIntegrable (fun t => 1 / 2 * (stdForm l (dS u s t) (dT u s t)
      + stdForm l (u s t) (dS (dT u) s t))) MeasureTheory.volume 0 1 :=
    (continuous_const.mul ((continuous_stdForm₂ hcs1 hct1).add
      (continuous_stdForm₂ hcu1 hcst1))).intervalIntegrable 0 1
  have hlhs : actionForm H (u s) (dS u s)
      = ∫ t in (0:ℝ)..1, (stdForm l (dS u s t) (hamField H t (u s t))
          - stdForm l (dS u s t) (dT u s t)) := by
    simp only [actionForm]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show stdForm l (dT u s t - hamField H t (u s t)) (dS u s t)
        = stdForm l (dS u s t) (hamField H t (u s t)) - stdForm l (dS u s t) (dT u s t)
    rw [(stdForm_isSymplectic l).skew (dT u s t - hamField H t (u s t)) (dS u s t)]
    simp only [map_sub]
    ring
  rw [hlhs, intervalIntegral.integral_sub hIa hIb, intervalIntegral.integral_sub hIa hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hIb hIc, hcb]
  ring

/-- The integrand of the action, at a fixed value of the parameter. -/
private theorem continuous_actionIntegrand_at {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsLoopVariation u) (σ : ℝ) :
    Continuous fun t : ℝ => H (u σ t) t - 1 / 2 * stdForm l (u σ t) (dT u σ t) := by
  have hp : Continuous fun t : ℝ => ((σ : ℝ), t) := continuous_const.prodMk continuous_id
  have h0 : Continuous fun t : ℝ => u σ t := hu.continuous.comp hp
  have h1 : Continuous fun t : ℝ => dT u σ t := hu.continuous_t.comp hp
  have h2 : Continuous fun t : ℝ => H (u σ t) t :=
    hH.continuous.comp (h0.prodMk continuous_id)
  exact h2.sub (continuous_const.mul (continuous_stdForm₂ h0 h1))

/-- Its `σ`-derivative, at a fixed value of the parameter. -/
private theorem continuous_actionIntegrandDeriv_at {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsSmoothLoopVariation u) (σ : ℝ) :
    Continuous fun t : ℝ => stdForm l (dS u σ t) (hamField H t (u σ t))
      - 1 / 2 * (stdForm l (dS u σ t) (dT u σ t) + stdForm l (u σ t) (dS (dT u) σ t)) := by
  have hp : Continuous fun t : ℝ => ((σ : ℝ), t) := continuous_const.prodMk continuous_id
  have h0 : Continuous fun t : ℝ => u σ t := hu.continuous.comp hp
  have h1 : Continuous fun t : ℝ => dS u σ t := hu.continuous_s.comp hp
  have h2 : Continuous fun t : ℝ => dT u σ t := hu.continuous_t.comp hp
  have h3 : Continuous fun t : ℝ => dS (dT u) σ t := hu.continuous_st.comp hp
  have h4 : Continuous fun t : ℝ => hamField H t (u σ t) :=
    continuous_hamField (τ := fun t : ℝ => t) hH h0 continuous_id
  exact (continuous_stdForm₂ h1 h4).sub
    (continuous_const.mul ((continuous_stdForm₂ h1 h2).add (continuous_stdForm₂ h0 h3)))

/-- The dominating bound required by the differentiation-under-the-integral
lemma: the `σ`-derivative of the integrand is continuous, hence bounded on the
compact set `[s−1, s+1] × [0,1]`. -/
private theorem exists_bound_actionIntegrandDeriv {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsSmoothLoopVariation u) (s : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ σ ∈ Metric.ball s 1,
      ‖stdForm l (dS u σ t) (hamField H t (u σ t))
        - 1 / 2 * (stdForm l (dS u σ t) (dT u σ t)
            + stdForm l (u σ t) (dS (dT u) σ t))‖ ≤ C := by
  obtain ⟨C, hC⟩ := (IsCompact.prod (isCompact_Icc (a := s - 1) (b := s + 1))
    (isCompact_Icc (a := (0 : ℝ)) (b := (1 : ℝ)))).exists_bound_of_continuousOn
      (continuous_actionIntegrandDeriv hH hu).continuousOn
  refine ⟨C, fun t ht σ hσ => ?_⟩
  rw [Set.uIoc_of_le zero_le_one] at ht
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hσ
  exact hC (σ, t) ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, ⟨ht.1.le, ht.2⟩⟩

/-- **Proposition 6.3.4** (the analytic half): the first variation of the action
functional along a smooth family of loops is the action form,
`d/ds A_H(u_s) = ∫₀¹ ω(∂u/∂t − X_t(u), ∂u/∂s) dt`.

The proof is the book's computation.  Differentiating under the integral sign
(Mathlib's `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
the dominating bound coming from the continuity of the `σ`-derivative of the
integrand on the compact set `[s−1, s+1] × [0,1]`) gives

`d/dσ A_H(u_σ)|_{σ=s} = ∫₀¹ (dH_t(∂u/∂s) − ½ ω(∂u/∂s, ∂u/∂t) − ½ ω(u, ∂²u/∂σ∂t))`.

The first term is `ω(∂u/∂s, X_t(u))` by `stdForm_hamField`, and integration by
parts on the circle (`integral_stdForm_byParts`, applied to the loop `u_s` and
the vector field `∂u/∂s` along it) turns `∫ ω(u, ∂²u/∂σ∂t)` into
`∫ ω(∂u/∂s, ∂u/∂t)`, so that the last two terms add up to
`−∫ ω(∂u/∂s, ∂u/∂t) = ∫ ω(∂u/∂t, ∂u/∂s)`.

Note the hypothesis: `IsSmoothLoopVariation`, not `IsLoopVariation`.  The term
`ω(u, ∂²u/∂σ∂t)` produced by the differentiation is meaningless unless the
mixed partial exists, and the integration by parts that cancels it needs both
its continuity and its symmetry `∂²u/∂σ∂t = ∂²u/∂t∂σ`.  The book's variations
are `C^∞` families of loops, so this is exactly what it assumes; stating the
result for `IsLoopVariation` would be stating something the book does not
prove. -/
theorem hasDerivAt_action (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsSmoothLoopVariation u) (s : ℝ) :
    HasDerivAt (fun σ => action H (u σ)) (actionForm H (u s) (dS u s)) s := by
  obtain ⟨C, hbound⟩ := exists_bound_actionIntegrandDeriv hH hu s
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (x₀ := s)
      (bound := fun _ => C) (s := Metric.ball s 1)
      (F := fun σ t => H (u σ t) t - 1 / 2 * stdForm l (u σ t) (dT u σ t))
      (F' := fun σ t => stdForm l (dS u σ t) (hamField H t (u σ t))
        - 1 / 2 * (stdForm l (dS u σ t) (dT u σ t) + stdForm l (u σ t) (dS (dT u) σ t)))
      (Metric.ball_mem_nhds s one_pos)
      (Filter.Eventually.of_forall fun σ =>
        (continuous_actionIntegrand_at hH hu.toIsLoopVariation σ).aestronglyMeasurable)
      ((continuous_actionIntegrand_at hH hu.toIsLoopVariation s).intervalIntegrable 0 1)
      (continuous_actionIntegrandDeriv_at hH hu s).aestronglyMeasurable
      (MeasureTheory.ae_of_all _ hbound) intervalIntegrable_const
      (MeasureTheory.ae_of_all _ fun t _ σ _ => hasDerivAt_actionIntegrand hH hu σ t)
  have haction : (fun σ => action H (u σ)) = fun σ => ∫ t in (0:ℝ)..1,
      (H (u σ t) t - 1 / 2 * stdForm l (u σ t) (dT u σ t)) := rfl
  rw [haction, actionForm_eq_integral H hH hu s]
  exact key.2

/-- **§6.5.a.**  Along a Floer trajectory the action decreases at the rate
`d/ds A_H(u_s) = −∫_{S¹} |∂u/∂s|² dt = −‖grad A_H‖²`.

This is the exact analogue, for the action functional, of the fact that a Morse
function decreases along a pseudo-gradient trajectory (Chapter 2), and it is
what makes the energy of a trajectory joining two critical points equal to the
difference of the critical values. -/
theorem hasDerivAt_action_of_floer (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u) (s : ℝ) :
    HasDerivAt (fun σ => action H (u σ)) (-∫ t in (0:ℝ)..1, energyDensity u s t) s := by
  have h := hasDerivAt_action H hH hu.toIsSmoothLoopVariation s
  have hcong : (∫ t in (0:ℝ)..1, stdForm l (deriv (u s) t - hamField H t (u s t)) (dS u s t))
      = -∫ t in (0:ℝ)..1, energyDensity u s t := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hf : dT u s t - hamField H t (u s t) = stdJ l (dS u s t) := floer_eq H hu s t
    show stdForm l (dT u s t - hamField H t (u s t)) (dS u s t) = -energyDensity u s t
    rw [hf, stdForm_stdJ_self]
    rfl
  simp only [actionForm] at h
  rw [hcong] at h
  exact h

/-- **§6.5.a.**  Consequently `s ↦ A_H(u_s)` is decreasing along a solution of
the Floer equation: the analogue of Proposition 2.2.x for the action
functional. -/
theorem action_antitone (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u) :
    Antitone fun s => action H (u s) := by
  have hd : Differentiable ℝ fun s => action H (u s) := fun s =>
    (hasDerivAt_action_of_floer H hH hu s).differentiableAt
  refine antitone_of_deriv_nonpos hd fun s => ?_
  rw [(hasDerivAt_action_of_floer H hH hu s).deriv, neg_nonpos]
  exact intervalIntegral.integral_nonneg zero_le_one fun t _ => energyDensity_nonneg u s t

/-- **Remark 6.5.2(3).**  A solution joining two critical points has energy
`E(u) = A_H(x) − A_H(y)`; in particular such solutions have finite energy.

Given the two statements above the proof is the fundamental theorem of calculus
applied on `ℝ`, i.e. `∫_ℝ (−d/ds A_H(u_s)) ds = lim_{−∞} A_H(u_s) − lim_{+∞}`;
formalizing it needs the improper integral of the derivative of a monotone
function with limits at both ends, which is not carried out here. -/
theorem energy_eq_sub_action (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (_hu : IsFloerSolution H u)
    {x y : ℝ → ((l ⊕ l) → ℝ)}
    (_hx : Filter.Tendsto (fun s => action H (u s)) Filter.atBot (nhds (action H x)))
    (_hy : Filter.Tendsto (fun s => action H (u s)) Filter.atTop (nhds (action H y))) :
    energy u = action H x - action H y := by
  sorry

end Variation

/-! ## §6.5.b and §6.6 The space of finite-energy solutions

The book studies

`M = { u : ℝ × S¹ → W | u is a contractible C^∞ solution of finite energy }`,

proves that its elements converge at both ends to `1`-periodic orbits
(Theorem 6.5.6) and that `M` is compact for the `C^∞_loc` topology
(Theorem 6.5.4).  Both proofs rest on elliptic regularity and on Ascoli's
theorem, and the second on a uniform bound for the gradient (Proposition 6.6.2)
obtained by excluding bubbles.

Here `W` is replaced by the torus `ℝ^{2n}/ℤ^{2n}`: `H` is assumed `1`-periodic
in `t` and invariant under the lattice `ℤ^{2n}`.  The `C^∞_loc` topology on maps
into the torus becomes local uniform convergence up to a lattice translation. -/

section Compactness

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- **Proposition 6.5.3** (elliptic regularity, i.e. Lemma 12.1.1).  Every `C¹`
solution of the Floer equation is `C^∞`, and on `M` the topologies `C⁰_loc`,
`C¹_loc` and `C^∞_loc` coincide.

This is the analytic engine of the whole chapter.  Mathlib has neither Sobolev
spaces on `ℝ × S¹` nor elliptic estimates, so only the first assertion is stated
and it is assumed. -/
theorem contDiff_of_isFloerSolution (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (_hu : IsFloerSolution H u) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ => u p.1 p.2 := by
  sorry

/-- **Lemma 6.5.10.**  Under the nondegeneracy hypothesis the `1`-periodic
orbits are finitely many: they are the intersection points of the diagonal with
the graph of `ψ_1` in `W × W`, two submanifolds that nondegeneracy makes
transverse, so their intersection is a compact `0`-dimensional manifold.

On the torus the fixed-point set of `ψ_1` is invariant under the lattice, so the
finiteness statement is finiteness in every compact set.  Mathlib has neither
transversality nor tubular neighbourhoods; the statement is nevertheless
provable from the inverse function theorem (nondegeneracy makes `p ↦ ψ_1 p − p`
a local diffeomorphism at a fixed point, so fixed points are isolated), which is
not carried out here. -/
theorem finite_fixedPoints (ψ : ℝ → ((l ⊕ l) → ℝ) → ((l ⊕ l) → ℝ))
    (_hψ : ∀ p, ψ 1 p = p → IsNondegenerateOrbit ψ p)
    (_hcont : Continuous (ψ 1)) {K : Set ((l ⊕ l) → ℝ)} (_hK : IsCompact K) :
    (K ∩ {p | ψ 1 p = p}).Finite := by
  sorry

/-- **Proposition 6.5.7.**  For a finite-energy solution the action converges at
both ends to critical values of `A_H`.

The proof extracts a sequence `s_k → ±∞` along which `‖∂u/∂t − X_t(u)‖_{L²}`
tends to `0`, applies Ascoli to get a `C⁰` limit, bootstraps it to a smooth
periodic orbit (Lemma 6.5.9), and checks that the action passes to the limit.
Ascoli is in Mathlib, the rest is not. -/
theorem exists_tendsto_action (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (_hu : IsFloerSolution H u) :
    ∃ x y : ℝ → ((l ⊕ l) → ℝ), IsPeriodicOrbit (hamField H) x ∧ IsPeriodicOrbit (hamField H) y ∧
      Filter.Tendsto (fun s => action H (u s)) Filter.atBot (nhds (action H x)) ∧
      Filter.Tendsto (fun s => action H (u s)) Filter.atTop (nhds (action H y)) := by
  sorry

/-- **Corollary 6.5.11.**  There is a constant `C > 0` bounding the action and
the energy of every element of `M`: the critical values form a finite set, and
`E(u) = A_H(x) − A_H(y)`. -/
theorem exists_bound_action_energy (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hHt : ∀ y t, H y (t + 1) = H y t)
    (_hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ → ((l ⊕ l) → ℝ), IsFloerSolution H u →
      MeasureTheory.Integrable (fun s => ∫ t in (0:ℝ)..1, energyDensity u s t) →
      energy u ≤ C := by
  sorry

/-- **Theorem 6.5.6** (with Lemmas 6.5.13, 6.5.14 and Proposition 6.5.15).  If
all the periodic orbits of `X_t` are nondegenerate, every finite-energy solution
converges at `s → ±∞` to `1`-periodic orbits, and `∂u/∂s → 0` uniformly in `t`.

The book's proof uses the compactness of `M` (Theorem 6.5.4), the finiteness of
the set of critical points (Lemma 6.5.10) and the connectedness of the image of
a half-line.  It is stated here with pointwise convergence rather than
convergence in `C^∞(S¹; W)`, which has no topology available. -/
theorem tendsto_of_finite_energy (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (ψ : ℝ → ((l ⊕ l) → ℝ) → ((l ⊕ l) → ℝ)) (_hψ : IsFlow (hamField H) ψ)
    (_hnd : ∀ p, ψ 1 p = p → IsNondegenerateOrbit ψ p)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (_hu : IsFloerSolution H u)
    (_hE : MeasureTheory.Integrable fun s => ∫ t in (0:ℝ)..1, energyDensity u s t) :
    ∃ x y : ℝ → ((l ⊕ l) → ℝ), IsPeriodicOrbit (hamField H) x ∧ IsPeriodicOrbit (hamField H) y ∧
      (∀ t, Filter.Tendsto (fun s => u s t) Filter.atBot (nhds (x t))) ∧
      (∀ t, Filter.Tendsto (fun s => u s t) Filter.atTop (nhds (y t))) ∧
      (∀ t, Filter.Tendsto (fun s => dS u s t) Filter.atBot (nhds 0)) ∧
      (∀ t, Filter.Tendsto (fun s => dS u s t) Filter.atTop (nhds 0)) := by
  sorry

/-- **Proposition 6.6.2.**  Under the asphericity Hypothesis 6.2.1 there is a
constant `A > 0` bounding the gradient of every element of `M` uniformly.

This is the heart of the compactness proof: if the gradient blew up, rescaling
around the blow-up point would produce a nonconstant `J`-holomorphic plane of
finite, nonzero symplectic area — a *bubble* — whose existence Hypothesis 6.2.1
forbids.  Both the rescaling (Lemma 6.6.3) and the area computation
(Lemmas 6.6.4, 6.6.5) are out of reach; the torus satisfies the hypothesis
because `π₂(T^{2n}) = 0`. -/
theorem exists_gradient_bound (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hHt : ∀ y t, H y (t + 1) = H y t)
    (_hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t) (C : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : ℝ → ℝ → ((l ⊕ l) → ℝ), IsFloerSolution H u → energy u ≤ C →
      ∀ s t, dS u s t ⬝ᵥ dS u s t + dT u s t ⬝ᵥ dT u s t ≤ A := by
  sorry

/-- **Theorem 6.5.4** (compactness of `M`).  Under Hypothesis 6.2.1 the space of
finite-energy solutions is compact in `C^∞_loc(ℝ × S¹, W)`.

Stated sequentially and on the torus: a sequence of solutions of uniformly
bounded energy has a subsequence which, after translation by lattice vectors,
converges uniformly on every compact subset of `ℝ × S¹` to a solution.  The
proof combines the gradient bound of Proposition 6.6.2, Ascoli's theorem and the
elliptic regularity of Proposition 6.5.3. -/
theorem compactness_of_energy_bounded (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hHt : ∀ y t, H y (t + 1) = H y t)
    (_hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t) (C : ℝ)
    (u : ℕ → ℝ → ℝ → ((l ⊕ l) → ℝ)) (_hu : ∀ n, IsFloerSolution H (u n))
    (_hE : ∀ n, energy (u n) ≤ C) :
    ∃ (φ : ℕ → ℕ) (k : ℕ → ((l ⊕ l) → ℤ)) (v : ℝ → ℝ → ((l ⊕ l) → ℝ)),
      StrictMono φ ∧ IsFloerSolution H v ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K →
        TendstoUniformlyOn (fun n p => u (φ n) p.1 p.2 - fun i => ((k n i : ℝ)))
          (fun p => v p.1 p.2) Filter.atTop K := by
  sorry

end Compactness

/-! ## §6.6 Hofer's half-maximum lemma -/

section HalfMaximum

/-- **Lemma 6.6.3** ("half-maximum", attributed to Ekeland; also known as
Hofer's lemma).  Let `g` be a continuous nonnegative function on a complete
metric space, `x₀` a point and `ε₀ > 0`.  Then there are `y` and
`ε ∈ (0, ε₀]` with `d(y, x₀) ≤ 2ε₀`, `ε g(y) ≥ ε₀ g(x₀)` and `g ≤ 2 g(y)` on the
ball `B(y, ε)`.

The proof is a doubling recursion: if the third condition fails at `(x_n, ε_n)`,
choose `x_{n+1}` in the ball with `g(x_{n+1}) > 2 g(x_n)` and halve the radius;
the sequence is Cauchy, so `g` would be unbounded near its limit.  Formalizing
this needs a dependent-choice recursion which is not carried out here.

The book prints the first condition as `d(y, x₀) ≤ 2ε`; what the recursion gives
is `d(y, x₀) ≤ 2ε₀`, which is what is stated here. -/
theorem exists_half_maximum {X : Type*} [MetricSpace X] [CompleteSpace X] {g : X → ℝ}
    (_hg : Continuous g) (_hpos : ∀ x, 0 ≤ g x) (x₀ : X) {ε₀ : ℝ} (_hε₀ : 0 < ε₀) :
    ∃ (y : X) (ε : ℝ), 0 < ε ∧ ε ≤ ε₀ ∧ dist y x₀ ≤ 2 * ε₀ ∧ ε₀ * g x₀ ≤ ε * g y ∧
      ∀ x ∈ Metric.ball y ε, g x ≤ 2 * g y := by
  sorry

end HalfMaximum

end Chapter6
end MorseFloer
