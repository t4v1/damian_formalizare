import MorseFloer.Part2.Ch5
import MorseFloer.Part2.Wirtinger
import MorseFloer.Part2.FloerRegularity
import MorseFloer.Part2.ApproxOrbit

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
* **Proposition 6.1.5** (`isConst_of_isPeriodicOrbit_of_lipschitz`): a
  `K`-Lipschitz vector field on a Euclidean space with `K < 2π` has only constant
  `1`-periodic orbits.  This is Yorke's theorem; the proof, in
  `Part2/Wirtinger.lean`, is the book's: Wirtinger's inequality from Parseval
  and the integration by parts for Fourier coefficients, both in Mathlib;
* its **elementary half** (`isConst_of_isPeriodicOrbit_of_lipschitz_lt_four`):
  the same with `K < 4`, for every norm.  No Fourier analysis: the velocity has
  zero mean over a period, so it is the average of its own increments over the
  circle seen from `t`, and the mean distance along that circle is `1/4`
  (`integral_abs_sub_half`);
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
  (`isPeriodicOrbit_of_dS_eq_zero`, `isFloerSolution_of_isPeriodicOrbit`), and
  **6.5.2(2)** in the hard direction: a solution of zero energy does not depend
  on `s` (`dS_eq_zero_of_energy_eq_zero`);
* **Lemma 6.6.3**, Hofer's half-maximum lemma, which is Mathlib's `hofer`;
* **Remark 6.5.2(3)**, `E(u) = A_H(x) − A_H(y)` for a solution whose action
  converges to `A_H(x)` and `A_H(y)` at the two ends (`energy_eq_sub_action`):
  the fundamental theorem of calculus on `ℝ` for the monotone function
  `s ↦ A_H(u_s)`, whose derivative `−∫|∂u/∂s|²` is then automatically integrable;
* **Lemma 6.5.10**, the finiteness of the nondegenerate fixed points of `ψ_1`
  in every compact set (`finite_fixedPoints`), by the first-order expansion of
  `ψ_1 − Id` at a fixed point — no transversality theory is needed;
* **Proposition 6.5.7** (`exists_tendsto_action`): the action of a
  finite-energy solution converges at both ends to critical values.  The book
  uses Ascoli's theorem and an elliptic bootstrap; here neither is needed.
  Along a sequence `s_k → ±∞` on which the energy of the loop tends to `0`, the
  loops `u(s_k, ·)`, translated into the unit cube, solve Hamilton's equation
  up to the error `J₀ ∂u/∂s`, small in `L¹`, and `Part2/ApproxOrbit.lean` shows
  by Grönwall's inequality that such loops converge at every time to a periodic
  orbit once their starting points do.  The action passes to the limit by
  dominated convergence, and converges on the whole half-line because it is
  monotone;
* **Corollary 6.5.11** (`exists_bound_action_energy`), *from* Proposition
  6.5.7: the energy of every finite-energy solution is bounded by a constant.
  The book's proof is followed — the action converges at both ends to critical
  values and `E(u) = A_H(x) − A_H(y)` — and the missing step, that the
  critical values form a bounded set, is proved without nondegeneracy
  (`exists_bound_action_of_isPeriodicOrbit`): on the torus `H` and `X_t` are
  bounded (`exists_bound_of_lattice_periodic`, a continuous function on
  `T^{2n} × S¹` is bounded), so a periodic orbit moves at most `sup ‖X_t‖` away
  from `x(0)` in one period, and since `∫₀¹ ẋ = 0` the action of `x` is that
  of `x − x(0)`, whose integrand is bounded.  With Proposition 6.5.7 proved,
  the corollary is unconditional;
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
* **Proposition 6.5.3**, elliptic regularity for the Floer equation
  (`contDiff_of_isFloerSolution`): every `C¹` solution is `C^∞`.  The proof is
  the dictionary of `Part2/FloerRegularity.lean` — `ℝ^{2n} ≅ ℂⁿ` turns the
  equation into the semilinear system `∂̄u_i = G_i(z, u)` — followed by the
  Cauchy-transform bootstrap of `Part2/CauchyHolder.lean`.

Assumed (`sorry`), each with the missing ingredient recorded at the statement:

* **Conjecture 6.1.2** in the case of the torus `T^{2n} = ℝ^{2n}/ℤ^{2n}`, where
  `∑_i dim HM_i(T^{2n}; ℤ/2) = 2^{2n}` is an explicit number
  (`arnold_conjecture_torus`);
* **Theorem 6.5.6** and **Proposition 6.5.15** (finite-energy solutions converge
  to periodic orbits), **Theorem 6.5.4** (compactness) and **Proposition 6.6.2**
  (the uniform gradient bound).

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

/-- The average, over one period, of the distance from a point of the circle to
the rest of it: `∫_{s−½}^{s+½} |s − r| dr = 1/4`.  This is the only computation
in the elementary form of Proposition 6.1.5 below, and it is where the constant
`4` comes from. -/
theorem integral_abs_sub_half (s : ℝ) :
    (∫ r in (s - 1 / 2)..(s + 1 / 2), |s - r|) = 1 / 4 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun r => |s - r|) MeasureTheory.volume a b :=
    fun a b => ((continuous_const.sub continuous_id).abs).intervalIntegrable a b
  have hlow : (∫ r in (s - 1 / 2)..s, |s - r|) = 1 / 8 := by
    have hc : Set.EqOn (fun r => |s - r|) (fun r => s - r) (Set.uIcc (s - 1 / 2) s) := by
      intro r hr
      rw [Set.uIcc_of_le (by linarith)] at hr
      exact abs_of_nonneg (by linarith [hr.2])
    rw [intervalIntegral.integral_congr hc,
      intervalIntegral.integral_sub (μ := MeasureTheory.volume) (f := fun _ : ℝ => s)
        (g := fun r : ℝ => r) intervalIntegrable_const (continuous_id'.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  have hhigh : (∫ r in s..(s + 1 / 2), |s - r|) = 1 / 8 := by
    have hc : Set.EqOn (fun r => |s - r|) (fun r => r - s) (Set.uIcc s (s + 1 / 2)) := by
      intro r hr
      rw [Set.uIcc_of_le (by linarith)] at hr
      show |s - r| = r - s
      rw [abs_of_nonpos (by linarith [hr.1])]
      ring
    rw [intervalIntegral.integral_congr hc,
      intervalIntegral.integral_sub (μ := MeasureTheory.volume) (f := fun r : ℝ => r)
        (g := fun _ : ℝ => s) (continuous_id'.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s) (hint _ _) (hint _ _),
    hlow, hhigh]
  norm_num

/-- **Proposition 6.1.5, the elementary bound.**  A `K`-Lipschitz vector field
with `K < 4` has only constant `1`-periodic orbits.

No Fourier analysis is involved and no hypothesis is made on the norm of `E`, so
this is the form of the statement that is true for *every* normed space.  Write
`y = ẋ`.  It is continuous and `1`-periodic, so `M = max ‖y‖` exists, and its
mean over a period vanishes, `∫_{t−½}^{t+½} y = x(t+½) − x(t−½) = 0`.  Hence
for every `t`

`y(t) = ∫_{t−½}^{t+½} (y(t) − y(r)) dr`,

and since `X` is `K`-Lipschitz and `x` is `M`-Lipschitz (mean value inequality),

`‖y(t)‖ ≤ K ∫_{t−½}^{t+½} ‖x(t) − x(r)‖ dr ≤ K M ∫_{t−½}^{t+½} |t − r| dr = K M / 4`

by `integral_abs_sub_half`.  Taking for `t` a point where `‖y‖` is maximal gives
`M ≤ (K/4) M`, so `M = 0` and `x` is constant.  Geometrically the centred
interval is the circle `ℝ/ℤ` seen from `t`, and `1/4` is the mean of the distance
along it — which is why the elementary constant is `4`.

The sharp constant in a Euclidean `E` is `2π`; see
`isConst_of_isPeriodicOrbit_of_lipschitz` for what that needs and why it is not
available. -/
theorem isConst_of_isPeriodicOrbit_of_lipschitz_lt_four {X : E → E} {K : ℝ≥0}
    (hX : LipschitzWith K X) (hK : (K : ℝ) < 4) {x : ℝ → E}
    (hx : IsPeriodicOrbit (fun _ => X) x) (t : ℝ) : x t = x 0 := by
  have hxd : ∀ s, HasDerivAt x (X (x s)) s := hx.hasDerivAt
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun s => (hxd s).continuousAt
  have hyc : Continuous fun s => X (x s) := hX.continuous.comp hxc
  have hyper : Function.Periodic (fun s => X (x s)) 1 := by
    intro s
    show X (x (s + 1)) = X (x s)
    rw [hx.periodic s]
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1)) (f := fun s => ‖X (x s)‖)
    hyc.norm.continuousOn
  set M : ℝ := ‖X (x t₀)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMle : ∀ s : ℝ, ‖X (x s)‖ ≤ M := by
    intro s
    obtain ⟨u, hu, hsu⟩ := hyper.exists_mem_Ico₀ one_pos s
    have hsu' : X (x s) = X (x u) := hsu
    rw [hsu']
    exact ht₀ (Set.Ico_subset_Icc_self hu)
  -- `x` is `M`-Lipschitz, by the mean value inequality
  have hlip : ∀ a b : ℝ, ‖x b - x a‖ ≤ M * |b - a| := by
    have key : ∀ a b : ℝ, a ≤ b → ‖x b - x a‖ ≤ M * (b - a) := by
      intro a b hab
      exact norm_image_sub_le_of_norm_deriv_le_segment' (f := x) (f' := fun s => X (x s))
        (C := M) (a := a) (b := b) (fun s _ => (hxd s).hasDerivWithinAt) (fun s _ => hMle s) b
        (Set.right_mem_Icc.2 hab)
    intro a b
    rcases le_total a b with h | h
    · rw [abs_of_nonneg (by linarith)]
      exact key a b h
    · rw [abs_of_nonpos (by linarith), neg_sub, norm_sub_rev]
      exact key b a h
  -- the mean of the velocity over a period vanishes
  have hzero : ∀ s : ℝ, (∫ r in (s - 1 / 2)..(s + 1 / 2), X (x r)) = 0 := by
    intro s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := x) (f' := fun r => X (x r))
      (fun r _ => hxd r) (hyc.intervalIntegrable _ _)]
    have hp := hx.periodic (s - 1 / 2)
    have e : s - 1 / 2 + 1 = s + 1 / 2 := by ring
    rw [e] at hp
    rw [hp, sub_self]
  -- the key estimate: the speed is at most `K M / 4`
  have hrep : ∀ s : ℝ, ‖X (x s)‖ ≤ (K : ℝ) * M * (1 / 4) := by
    intro s
    have e1 : s + 1 / 2 - (s - 1 / 2) = (1 : ℝ) := by ring
    have hsplit : (∫ r in (s - 1 / 2)..(s + 1 / 2), (X (x s) - X (x r))) = X (x s) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hyc.intervalIntegrable _ _),
        hzero s, sub_zero, intervalIntegral.integral_const, e1, one_smul]
    have hb1 : ‖∫ r in (s - 1 / 2)..(s + 1 / 2), (X (x s) - X (x r))‖
        ≤ ∫ r in (s - 1 / 2)..(s + 1 / 2), ‖X (x s) - X (x r)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    have hb2 : (∫ r in (s - 1 / 2)..(s + 1 / 2), ‖X (x s) - X (x r)‖)
        ≤ ∫ r in (s - 1 / 2)..(s + 1 / 2), (K : ℝ) * M * |s - r| := by
      refine intervalIntegral.integral_mono_on (by linarith)
        (((continuous_const.sub hyc).norm).intervalIntegrable _ _)
        ((continuous_const.mul ((continuous_const.sub continuous_id).abs)).intervalIntegrable _ _)
        ?_
      intro r _
      have hd := hX.dist_le_mul (x s) (x r)
      rw [dist_eq_norm, dist_eq_norm] at hd
      calc ‖X (x s) - X (x r)‖ ≤ (K : ℝ) * ‖x s - x r‖ := hd
        _ ≤ (K : ℝ) * (M * |s - r|) := mul_le_mul_of_nonneg_left (hlip r s) K.coe_nonneg
        _ = (K : ℝ) * M * |s - r| := by ring
    have hb3 : (∫ r in (s - 1 / 2)..(s + 1 / 2), (K : ℝ) * M * |s - r|)
        = (K : ℝ) * M * (1 / 4) := by
      rw [intervalIntegral.integral_const_mul, integral_abs_sub_half]
    rw [← hsplit, ← hb3]
    exact hb1.trans hb2
  -- hence the speed vanishes identically
  have hMzero : M = 0 := by
    have h := hrep t₀
    rw [← hMdef] at h
    rcases le_or_gt M 0 with hle | hpos
    · exact le_antisymm hle hM0
    · exfalso
      have h4 : (K : ℝ) * M < 4 * M := mul_lt_mul_of_pos_right hK hpos
      linarith
  have hz := hlip 0 t
  rw [hMzero, zero_mul] at hz
  exact eq_of_sub_eq_zero (norm_le_zero_iff.mp hz)

/-- **Proposition 6.1.5.**  If the vector field is `2π`-Lipschitz (the book
assumes `‖dX_H‖_{L²} < 2π`, and remarks that a Lipschitz bound suffices), then
the only `1`-periodic solutions are the constant ones, i.e. the critical points
of `H`.

This is Yorke's theorem, proved in `Part2/Wirtinger.lean` by the book's own
route: Wirtinger's inequality `∫₀¹ ‖y‖² ≤ (1/4π²) ∫₀¹ ‖y'‖²` for a `C¹`
`1`-periodic `y` of mean zero, obtained from Parseval and the integration by
parts `ŷ'(n) = 2πin·ŷ(n)` (`fourierCoeffOn_of_hasDerivAt`), applied to the
difference `y(s) = x(s + t) − x(s)`.

**Why the inner product is a hypothesis here.**  The constant `2π` is Yorke's,
and Yorke's theorem is a Hilbert space statement.  For a general Banach norm the
sharp bound is *not* `2π` but `6`: Busenberg, Fisher and Martelli prove `KT ≥ 6`
for a nonconstant `T`-periodic orbit of a `K`-Lipschitz field, and exhibit an
example attaining it (Proc. AMS **98** (1986) 376–378; Amer. Math. Monthly **96**
(1989) 5–17).  Since `6 < 2π`, the statement is **false** for a general norm, and
an earlier version of this file stated it that way.  The hypothesis
`[InnerProductSpace ℝ V]` below restores Yorke's setting, and is what the book
has: it works on `ℝ^{2n}` with the Euclidean structure throughout.  Note this
strengthens the hypotheses, so nothing is lost.

What holds for every norm, with the elementary constant `4`, is
`isConst_of_isPeriodicOrbit_of_lipschitz_lt_four` just above; `4 < 6 ≤` the sharp
Banach bound, so it is a correct, if not optimal, general statement. -/
theorem isConst_of_isPeriodicOrbit_of_lipschitz
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {X : V → V} {K : ℝ≥0}
    (hX : LipschitzWith K X) (hK : (K : ℝ) < 2 * Real.pi) {x : ℝ → V}
    (hx : IsPeriodicOrbit (fun _ => X) x) (t : ℝ) : x t = x 0 :=
  Wirtinger.yorke hX hK hx.hasDerivAt hx.periodic t

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

/-- If `H` is invariant under the lattice `ℤ^{2n}` — a Hamiltonian on the torus —
then so is its gradient: translation by a lattice vector does not change the
differential. -/
theorem hamGrad_lattice {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t)
    (k : (l ⊕ l) → ℤ) (t : ℝ) (x : (l ⊕ l) → ℝ) :
    hamGrad H t (x + fun i => (k i : ℝ)) = hamGrad H t x := by
  have e : fderiv ℝ (fun z => H (z + fun i => (k i : ℝ)) t) x
      = fderiv ℝ (fun y => H y t) (x + fun i => (k i : ℝ)) :=
    fderiv_comp_add_right (f := fun y => H y t) _
  have h : (fun z => H (z + fun i => (k i : ℝ)) t) = fun y => H y t :=
    funext fun y => hHlat k y t
  rw [h] at e
  funext i
  show fderiv ℝ (fun y => H y t) (x + fun i => (k i : ℝ)) (Pi.single i 1)
    = fderiv ℝ (fun y => H y t) x (Pi.single i 1)
  rw [← e]

/-- If `H` is lattice-invariant then so is `X_t`. -/
theorem hamField_lattice {H : ((l ⊕ l) → ℝ) → ℝ → ℝ}
    (hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t)
    (k : (l ⊕ l) → ℤ) (t : ℝ) (x : (l ⊕ l) → ℝ) :
    hamField H t (x + fun i => (k i : ℝ)) = hamField H t x := by
  rw [hamField_eq_stdJ_grad, hamField_eq_stdJ_grad, hamGrad_lattice hHlat]

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

omit [DecidableEq l] in
/-- **Remark 6.5.2(2)**, hard direction: a solution of zero energy does not
depend on `s`, hence is a `1`-periodic orbit.

The proof is measure-theoretic.  The inner integral `F(s) = ∫₀¹ |∂u/∂s|² dt` is
continuous (continuity of a parametric interval integral) and nonnegative, and
`∫ F = 0`, so `F = 0` almost everywhere, hence everywhere because `F` is
continuous (`Continuous.ae_eq_iff_eq`).  For each `s` the one-variable lemma
`eq_zero_of_integral_eq_zero` then gives `|∂u/∂s|² = 0` on `[0, 1]`, and
periodicity carries that to every `t`.

The hypothesis `hper` — that `u` really is a map into loops, i.e. `1`-periodic
in `t` — is necessary and was missing from the earlier statement of this lemma:
the energy only sees `t ∈ [0, 1]`, so for `u s t = f t + s · g t` with `g`
continuous and supported away from `[0, 1]` the energy vanishes while
`∂u/∂s = g` does not. -/
theorem dS_eq_zero_of_energy_eq_zero {u : ℝ → ℝ → ((l ⊕ l) → ℝ)}
    (hc : Continuous fun p : ℝ × ℝ => dS u p.1 p.2)
    (hi : MeasureTheory.Integrable fun s => ∫ t in (0:ℝ)..1, energyDensity u s t)
    (hper : ∀ s, Function.Periodic (u s) 1)
    (h : energy u = 0) (s t : ℝ) : dS u s t = 0 := by
  have hdens : Continuous fun p : ℝ × ℝ => energyDensity u p.1 p.2 := by
    show Continuous fun p : ℝ × ℝ => dS u p.1 p.2 ⬝ᵥ dS u p.1 p.2
    simp only [dotProduct]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hc).mul ((continuous_apply i).comp hc)
  have hF : Continuous fun σ : ℝ => ∫ τ in (0:ℝ)..1, energyDensity u σ τ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun σ τ => energyDensity u σ τ) (by exact hdens) 0 1
  have hFnonneg : (0 : ℝ → ℝ) ≤ fun σ => ∫ τ in (0:ℝ)..1, energyDensity u σ τ := fun σ =>
    intervalIntegral.integral_nonneg zero_le_one fun τ _ => energyDensity_nonneg u σ τ
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg hFnonneg hi).mp h
  have hFzero : ∀ σ : ℝ, (∫ τ in (0:ℝ)..1, energyDensity u σ τ) = 0 := by
    have heq := (hF.ae_eq_iff_eq MeasureTheory.volume continuous_const).mp hae
    intro σ
    exact congrFun heq σ
  have hIcc : ∀ σ τ, τ ∈ Set.Icc (0:ℝ) 1 → dS u σ τ = 0 := by
    intro σ τ hτ
    rw [← energyDensity_eq_zero_iff]
    exact eq_zero_of_integral_eq_zero (hdens.comp (Continuous.prodMk continuous_const
      continuous_id)) (fun τ => energyDensity_nonneg u σ τ) (hFzero σ) hτ
  have hdSper : Function.Periodic (fun τ => dS u s τ) 1 := by
    intro τ
    show dS u s (τ + 1) = dS u s τ
    have hfun : (fun ρ => u ρ (τ + 1)) = fun ρ => u ρ τ := funext fun ρ => hper ρ τ
    show deriv (fun ρ => u ρ (τ + 1)) s = deriv (fun ρ => u ρ τ) s
    rw [hfun]
  have hfract : dS u s (Int.fract t) = dS u s t := by
    have h1 : dS u s (t - (⌊t⌋ : ℝ) * 1) = dS u s t := hdSper.sub_int_mul_eq ⌊t⌋
    rwa [mul_one] at h1
  rw [← hfract]
  exact hIcc s _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

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
applied on `ℝ`: `∫_ℝ (−d/ds A_H(u_s)) ds = lim_{+∞} A_H(u_s) − lim_{−∞} A_H(u_s)`
(`integral_of_hasDerivAt_of_tendsto`).  The integrability of the energy
density in `s`, which the identity needs, is automatic: it is minus the
derivative of the monotone function `s ↦ A_H(u_s)`, which has finite limits at
both ends (`integrableOn_Ioi_deriv_of_nonpos'`). -/
theorem energy_eq_sub_action (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u)
    {x y : ℝ → ((l ⊕ l) → ℝ)}
    (hx : Filter.Tendsto (fun s => action H (u s)) Filter.atBot (nhds (action H x)))
    (hy : Filter.Tendsto (fun s => action H (u s)) Filter.atTop (nhds (action H y))) :
    energy u = action H x - action H y := by
  set F : ℝ → ℝ := fun s => ∫ t in (0:ℝ)..1, energyDensity u s t with hF
  have hd : ∀ s, HasDerivAt (fun σ => action H (u σ)) (-F s) s :=
    hasDerivAt_action_of_floer H hH hu
  have hFnn : ∀ s, 0 ≤ F s := fun s =>
    intervalIntegral.integral_nonneg zero_le_one fun t _ => energyDensity_nonneg u s t
  have hint_top : MeasureTheory.IntegrableOn (fun s => -F s) (Set.Ioi 0) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonpos' (fun s _ => hd s)
      (fun s _ => neg_nonpos.mpr (hFnn s)) hy
  -- Mathlib has the `(a, ∞)` version only; reflect `s ↦ −s` for `(−∞, 0]`
  have hint_bot : MeasureTheory.IntegrableOn (fun s => -F s) (Set.Iic 0) := by
    have hd' : ∀ s, HasDerivAt (fun σ => action H (u (-σ))) (F (-s)) s := fun s => by
      have h := (hd (-s)).comp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using h
    have h1 : MeasureTheory.IntegrableOn (fun s => F (-s)) (Set.Ioi 0) :=
      MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (fun s _ => hd' s) (fun s _ => hFnn _)
        (hx.comp Filter.tendsto_neg_atTop_atBot)
    have h2 := h1.comp_neg
    rw [Set.neg_Ioi, neg_zero] at h2
    simp only [neg_neg] at h2
    rw [integrableOn_Iic_iff_integrableOn_Iio' (by simp)]
    exact h2.neg
  have hint : MeasureTheory.Integrable (fun s => -F s) := by
    rw [← MeasureTheory.integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
    exact hint_bot.union hint_top
  have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto hd hint hx hy
  rw [MeasureTheory.integral_neg] at h
  show ∫ s, F s = action H x - action H y
  linarith

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

/-- `∇H_t(x)` is jointly smooth in `(t, x)`. -/
theorem contDiff_hamGrad (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) :
    ContDiff ℝ ∞ fun p : ℝ × ((l ⊕ l) → ℝ) => hamGrad H p.1 p.2 := by
  have hswap : ContDiff ℝ ∞ fun q : (ℝ × ((l ⊕ l) → ℝ)) × ((l ⊕ l) → ℝ) => H q.2 q.1.1 := by
    have hlin : ContDiff ℝ ∞ fun q : (ℝ × ((l ⊕ l) → ℝ)) × ((l ⊕ l) → ℝ) =>
        ((q.2, q.1.1) : ((l ⊕ l) → ℝ) × ℝ) :=
      ((ContinuousLinearMap.snd ℝ (ℝ × ((l ⊕ l) → ℝ)) ((l ⊕ l) → ℝ)).prod
        ((ContinuousLinearMap.fst ℝ ℝ ((l ⊕ l) → ℝ)).comp
          (ContinuousLinearMap.fst ℝ (ℝ × ((l ⊕ l) → ℝ)) ((l ⊕ l) → ℝ)))).contDiff
    exact hH.comp hlin
  have hfd : ContDiff ℝ ∞ fun p : ℝ × ((l ⊕ l) → ℝ) => fderiv ℝ (fun y => H y p.1) p.2 :=
    ContDiff.fderiv hswap (ContinuousLinearMap.snd ℝ ℝ ((l ⊕ l) → ℝ)).contDiff (by simp)
  exact contDiff_pi.2 fun i => hfd.clm_apply contDiff_const

/-- `X_t(x)` is jointly smooth in `(t, x)`. -/
theorem contDiff_hamField (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2) :
    ContDiff ℝ ∞ fun p : ℝ × ((l ⊕ l) → ℝ) => hamField H p.1 p.2 := by
  have h : (fun p : ℝ × ((l ⊕ l) → ℝ) => hamField H p.1 p.2)
      = fun p => LinearMap.toContinuousLinearMap (stdJ l) (hamGrad H p.1 p.2) := by
    funext p
    rw [hamField_eq_stdJ_grad]
    rfl
  rw [h]
  exact (LinearMap.toContinuousLinearMap (stdJ l)).contDiff.comp (contDiff_hamGrad H hH)

/-- **Proposition 6.5.3** (elliptic regularity, i.e. Lemma 12.1.1).  Every `C¹`
solution of the Floer equation is `C^∞`, and on `M` the topologies `C⁰_loc`,
`C¹_loc` and `C^∞_loc` coincide.

This is the analytic engine of the whole chapter.  Only the first assertion is
stated — the comparison of the three topologies needs the `C^∞_loc` topology,
which Mathlib does not have — and it is **proved**, through
`FloerRegularity.contDiff_infty_of_floer`: under the identification of `ℝ^{2n}`
with `ℂⁿ` the equation becomes the semilinear system `∂̄u_i = G_i(z, u)`, whose
`C¹` solutions are smooth by the Cauchy-transform bootstrap of
`Part2/CauchyHolder.lean`.  No Sobolev space is involved: the whole chain runs
on the Hölder scale.  The only input needed here is the joint smoothness of
`(t, x) ↦ ∇H_t(x)`, which `ContDiff.fderiv` supplies from `hH`. -/
theorem contDiff_of_isFloerSolution (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ => u p.1 p.2 :=
  FloerRegularity.contDiff_infty_of_floer hu.hasDerivAt_s hu.hasDerivAt_t
    hu.continuous_s hu.continuous_t (contDiff_hamGrad H hH) hu.floer

omit [DecidableEq l] in
/-- **Lemma 6.5.10.**  Under the nondegeneracy hypothesis the `1`-periodic
orbits are finitely many: they are the intersection points of the diagonal with
the graph of `ψ_1` in `W × W`, two submanifolds that nondegeneracy makes
transverse, so their intersection is a compact `0`-dimensional manifold.

On the torus the fixed-point set of `ψ_1` is invariant under the lattice, so the
finiteness statement is finiteness in every compact set.  Mathlib has neither
transversality nor tubular neighbourhoods, and none is needed: at a fixed point
`p` the map `g(q) = ψ_1 q − q` has the injective, hence (in finite dimension)
antilipschitz, differential `dψ_1(p) − Id`, so the first-order expansion
`g(q) = (dψ_1(p) − Id)(q − p) + o(q − p)` shows `g(q) ≠ 0` for `q ≠ p` close to
`p`: fixed points are isolated, and a compact discrete set is finite.

The hypothesis `hdiff` — that `ψ_1` is differentiable at its fixed points — was
missing from an earlier statement and is necessary: `fderiv` is `0` where `ψ_1`
is not differentiable, which makes `IsNondegenerateOrbit` hold vacuously there,
and a continuous map with a non-isolated fixed point at which it is not
differentiable would be a counterexample. -/
theorem finite_fixedPoints (ψ : ℝ → ((l ⊕ l) → ℝ) → ((l ⊕ l) → ℝ))
    (hψ : ∀ p, ψ 1 p = p → IsNondegenerateOrbit ψ p)
    (hdiff : ∀ p, ψ 1 p = p → DifferentiableAt ℝ (ψ 1) p)
    (hcont : Continuous (ψ 1)) {K : Set ((l ⊕ l) → ℝ)} (hK : IsCompact K) :
    (K ∩ {p | ψ 1 p = p}).Finite := by
  set Fix : Set ((l ⊕ l) → ℝ) := {p | ψ 1 p = p} with hFix
  have hclosed : IsClosed Fix := isClosed_eq hcont continuous_id
  refine (hK.inter_right hclosed).finite ?_
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  have hp' : ψ 1 p = p := hp.2
  -- `p` is an isolated fixed point
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ q ∈ Metric.ball p ε, ψ 1 q = q → q = p := by
    set L := fderiv ℝ (ψ 1) p with hL
    set M : ((l ⊕ l) → ℝ) →L[ℝ] ((l ⊕ l) → ℝ) :=
      L - ContinuousLinearMap.id ℝ ((l ⊕ l) → ℝ) with hM
    have hbij : Function.Bijective (ContinuousLinearMap.id ℝ ((l ⊕ l) → ℝ) - L) := hψ p hp'
    have hMinj : Function.Injective M := by
      intro a b hab
      apply hbij.1
      have h1 : (ContinuousLinearMap.id ℝ ((l ⊕ l) → ℝ) - L) a = -(M a) := by simp [hM]
      have h2 : (ContinuousLinearMap.id ℝ ((l ⊕ l) → ℝ) - L) b = -(M b) := by simp [hM]
      rw [h1, h2, hab]
    obtain ⟨Kc, hKc, hanti⟩ :=
      (M : ((l ⊕ l) → ℝ) →ₗ[ℝ] ((l ⊕ l) → ℝ)).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.mpr hMinj)
    have hKc' : (0:ℝ) < Kc := NNReal.coe_pos.mpr hKc
    have hg : HasFDerivAt (fun q => ψ 1 q - q) M p :=
      (hdiff p hp').hasFDerivAt.sub (hasFDerivAt_id p)
    have hlo := (hasFDerivAt_iff_isLittleO.mp hg).def (by positivity : (0:ℝ) < 1 / (2 * Kc))
    rw [Metric.eventually_nhds_iff] at hlo
    obtain ⟨ε, hε, hlo⟩ := hlo
    refine ⟨ε, hε, fun q hq hqfix => ?_⟩
    have h1 := hlo hq
    simp only [hqfix, hp', sub_self, zero_sub, norm_neg] at h1
    have h2 : dist q p ≤ Kc * dist (M q) (M p) := hanti.le_mul_dist q p
    rw [dist_eq_norm, dist_eq_norm, ← map_sub] at h2
    have hKcc : (Kc:ℝ) * (1 / (2 * Kc)) = 1 / 2 := by field_simp
    have h3 : ‖q - p‖ ≤ 1 / 2 * ‖q - p‖ := by
      calc ‖q - p‖ ≤ Kc * ‖M (q - p)‖ := h2
        _ ≤ Kc * (1 / (2 * Kc) * ‖q - p‖) := by gcongr
        _ = (Kc * (1 / (2 * Kc))) * ‖q - p‖ := by ring
        _ = 1 / 2 * ‖q - p‖ := by rw [hKcc]
    have h4 : ‖q - p‖ ≤ 0 := by linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h4)
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, ?_⟩
  ext q
  constructor
  · rintro ⟨hq, -, hqfix⟩
    exact hball q hq hqfix
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨Metric.mem_ball_self hε, hp⟩

omit [DecidableEq l] in
/-- A continuous function on `ℝ^{2n} × ℝ` which is invariant under the lattice
`ℤ^{2n}` and `1`-periodic in time — that is, a continuous function on the
compact torus `T^{2n} × S¹` — is bounded: every point is congruent to one of
the compact fundamental domain `[0,1]^{2n} × [0,1]`. -/
theorem exists_bound_of_lattice_periodic {E : Type*} [NormedAddCommGroup E]
    {f : ((l ⊕ l) → ℝ) → ℝ → E} (hf : Continuous fun p : ((l ⊕ l) → ℝ) × ℝ => f p.1 p.2)
    (ht : ∀ y t, f y (t + 1) = f y t)
    (hlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      f (y + fun i => (k i : ℝ)) t = f y t) :
    ∃ M : ℝ, ∀ x t, ‖f x t‖ ≤ M := by
  have hK : IsCompact ((Metric.closedBall (0 : (l ⊕ l) → ℝ) 1) ×ˢ Set.Icc (0:ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, fun x t => ?_⟩
  have e1 : f x t = f (x - fun i => (⌊x i⌋ : ℝ)) t := by
    have := hlat (fun i => ⌊x i⌋) (x - fun i => (⌊x i⌋ : ℝ)) t
    rw [sub_add_cancel] at this
    exact this
  have e2 : f (x - fun i => (⌊x i⌋ : ℝ)) t = f (x - fun i => (⌊x i⌋ : ℝ)) (t - ⌊t⌋) := by
    have hper : Function.Periodic (f (x - fun i => (⌊x i⌋ : ℝ))) 1 := ht _
    have := hper.sub_int_mul_eq (x := t) ⌊t⌋
    rw [mul_one] at this
    exact this.symm
  rw [e1, e2]
  refine hM (_, _) ⟨?_, ?_⟩
  · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    show ‖x i - ⌊x i⌋‖ ≤ 1
    rw [Int.self_sub_floor, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  · show t - ⌊t⌋ ∈ Set.Icc (0:ℝ) 1
    rw [Int.self_sub_floor]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-- On the torus the action functional is bounded on the set of `1`-periodic
orbits, without any nondegeneracy hypothesis.  The book gets this from the
finiteness of the critical points (Lemma 6.5.10); here it is elementary.  For a
periodic orbit `x`, `‖ẋ‖ = ‖X_t(x)‖` is bounded by the maximum `M₁` of `X_t` on
the torus, so `‖x(t) − x(0)‖ ≤ M₁` on `[0, 1]`; and since `∫₀¹ ẋ = 0`, the term
`∫₀¹ ω(x, ẋ)` of the action equals `∫₀¹ ω(x − x(0), ẋ)`, whose integrand is
bounded.  The other term, `∫₀¹ H_t(x)`, is bounded by the maximum of `H`. -/
theorem exists_bound_action_of_isPeriodicOrbit (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    (hHt : ∀ y t, H y (t + 1) = H y t)
    (hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t) :
    ∃ B : ℝ, ∀ x : ℝ → ((l ⊕ l) → ℝ), IsPeriodicOrbit (hamField H) x → |action H x| ≤ B := by
  -- `H` and `X_t` are bounded on the torus
  obtain ⟨M₀, hM₀⟩ := exists_bound_of_lattice_periodic (f := H) hH.continuous hHt hHlat
  obtain ⟨M₁, hM₁⟩ := exists_bound_of_lattice_periodic (f := fun x t => hamField H t x)
    (continuous_hamField hH continuous_fst continuous_snd) (fun y t => hamField_periodic hHt t y)
    (fun k y t => hamField_lattice hHlat k t y)
  have hM₁' : ∀ y t, ‖hamField H t y‖ ≤ M₁ := fun y t => hM₁ y t
  -- `ω` is bounded on the ball of radius `M₁`
  obtain ⟨Cω, hCω⟩ := ((isCompact_closedBall (0 : (l ⊕ l) → ℝ) M₁).prod
    (isCompact_closedBall (0 : (l ⊕ l) → ℝ) M₁)).exists_bound_of_continuousOn
    (continuous_stdForm₂ (l := l) continuous_fst continuous_snd).continuousOn
  refine ⟨M₀ + 1 / 2 * Cω, fun x hx => ?_⟩
  have hd : ∀ t, HasDerivAt x (hamField H t (x t)) t := hx.hasDerivAt
  have hderiv : ∀ t, deriv x t = hamField H t (x t) := fun t => (hd t).deriv
  have hcx : Continuous x := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hcd : Continuous (deriv x) := by
    have : deriv x = fun t => hamField H t (x t) := funext hderiv
    rw [this]
    exact continuous_hamField hH hcx continuous_id
  have hHc : Continuous fun t => H (x t) t := hH.continuous.comp (hcx.prodMk continuous_id)
  -- `∫₀¹ ω(x(0), ẋ) = 0`, since `ẋ` integrates to `x(1) − x(0) = 0`
  have hzero : (∫ t in (0:ℝ)..1, stdForm l (x 0) (deriv x t)) = 0 := by
    have hder : ∀ t, HasDerivAt (fun τ => stdForm l (x 0) (x τ))
        (stdForm l (x 0) (deriv x t)) t := fun t => by
      have := hasDerivAt_stdForm (l := l) (hasDerivAt_const t (x 0)) (hd t)
      rw [hderiv t]
      exact this.congr_deriv (by simp)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      ((continuous_stdForm continuous_const hcd).intervalIntegrable 0 1)]
    have h1 : x 1 = x 0 := by simpa using hx.periodic 0
    rw [h1, sub_self]
  -- so the action can be computed with `x − x(0)` in place of `x`
  have hInt1 : IntervalIntegrable
      (fun t => H (x t) t - 1 / 2 * stdForm l (x t - x 0) (deriv x t)) MeasureTheory.volume 0 1 :=
    (hHc.sub (continuous_const.mul
      (continuous_stdForm (hcx.sub continuous_const) hcd))).intervalIntegrable 0 1
  have hInt2 : IntervalIntegrable
      (fun t => 1 / 2 * stdForm l (x 0) (deriv x t)) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_stdForm continuous_const hcd)).intervalIntegrable 0 1
  have hsplit : action H x
      = ∫ t in (0:ℝ)..1, (H (x t) t - 1 / 2 * stdForm l (x t - x 0) (deriv x t)) := by
    have e : (∫ t in (0:ℝ)..1, (H (x t) t - 1 / 2 * stdForm l (x t - x 0) (deriv x t)))
        - (∫ t in (0:ℝ)..1, 1 / 2 * stdForm l (x 0) (deriv x t)) = action H x := by
      rw [← intervalIntegral.integral_sub hInt1 hInt2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      show H (x t) t - 1 / 2 * stdForm l (x t - x 0) (deriv x t)
          - 1 / 2 * stdForm l (x 0) (deriv x t)
        = H (x t) t - 1 / 2 * stdForm l (x t) (deriv x t)
      rw [map_sub, LinearMap.sub_apply]
      ring
    rw [intervalIntegral.integral_const_mul, hzero, mul_zero, sub_zero] at e
    exact e.symm
  -- and the new integrand is bounded on `[0, 1]`
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖H (x t) t - 1 / 2 * stdForm l (x t - x 0) (deriv x t)‖ ≤ M₀ + 1 / 2 * Cω := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := Set.Ioc_subset_Icc_self ht
    have hmvt : ‖x t - x 0‖ ≤ M₁ := by
      have := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1) (f := x)
        (f' := fun t => hamField H t (x t)) (fun s _ => (hd s).hasDerivWithinAt)
        (fun s _ => hM₁' (x s) s) t ht'
      calc ‖x t - x 0‖ ≤ M₁ * (t - 0) := this
        _ ≤ M₁ * 1 := by
          have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁' 0 0)
          gcongr
          linarith [ht'.2]
        _ = M₁ := mul_one _
    have hω : |stdForm l (x t - x 0) (deriv x t)| ≤ Cω := by
      have := hCω (x t - x 0, deriv x t) ⟨mem_closedBall_zero_iff.2 hmvt,
        mem_closedBall_zero_iff.2 (by rw [hderiv t]; exact hM₁' (x t) t)⟩
      simpa using this
    have hH0 : |H (x t) t| ≤ M₀ := by
      have := hM₀ (x t) t
      rwa [Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs]
    obtain ⟨h1, h2⟩ := abs_le.mp hω
    obtain ⟨h3, h4⟩ := abs_le.mp hH0
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hsplit]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rwa [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at this

section ActionLimit

open Filter Topology

/-- `ω` is a bounded bilinear form. -/
theorem exists_bound_stdForm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : (l ⊕ l) → ℝ, |stdForm l a b| ≤ C * ‖a‖ * ‖b‖ := by
  refine ⟨‖LinearMap.toContinuousBilinearMap (stdForm l)‖,
    ContinuousLinearMap.opNorm_nonneg _, fun a b => ?_⟩
  have h := (LinearMap.toContinuousBilinearMap (stdForm l)).le_opNorm₂ a b
  rwa [LinearMap.toContinuousBilinearMap_apply, Real.norm_eq_abs] at h

/-- On the torus the Hamiltonian vector field is Lipschitz in the point, uniformly in
time: its differential in the point is continuous on the compact torus `T^{2n} × S¹`. -/
theorem exists_lipschitz_hamField (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    (hHt : ∀ y t, H y (t + 1) = H y t)
    (hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t) :
    ∃ K : ℝ, ∀ t a b, ‖hamField H t a - hamField H t b‖ ≤ K * ‖a - b‖ := by
  have hX := contDiff_hamField H hH
  have hunc : ContDiff ℝ ∞ (Function.uncurry
      fun (p : ((l ⊕ l) → ℝ) × ℝ) (y : (l ⊕ l) → ℝ) => hamField H p.2 y) := by
    have hlin : ContDiff ℝ ∞ fun q : (((l ⊕ l) → ℝ) × ℝ) × ((l ⊕ l) → ℝ) =>
        ((q.1.2, q.2) : ℝ × ((l ⊕ l) → ℝ)) :=
      (((ContinuousLinearMap.snd ℝ ((l ⊕ l) → ℝ) ℝ).comp
          (ContinuousLinearMap.fst ℝ (((l ⊕ l) → ℝ) × ℝ) ((l ⊕ l) → ℝ))).prod
        (ContinuousLinearMap.snd ℝ (((l ⊕ l) → ℝ) × ℝ) ((l ⊕ l) → ℝ))).contDiff
    exact hX.comp hlin
  have hfd : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ =>
      fderiv ℝ (fun y => hamField H p.2 y) p.1 :=
    ContDiff.fderiv hunc (ContinuousLinearMap.fst ℝ ((l ⊕ l) → ℝ) ℝ).contDiff (by simp)
  obtain ⟨K, hK⟩ := exists_bound_of_lattice_periodic
    (f := fun x t => fderiv ℝ (fun y => hamField H t y) x) hfd.continuous
    (fun y t => by
      have h : (fun z => hamField H (t + 1) z) = fun z => hamField H t z :=
        funext (hamField_periodic hHt t)
      show fderiv ℝ (fun z => hamField H (t + 1) z) y = fderiv ℝ (fun z => hamField H t z) y
      rw [h])
    (fun k y t => by
      have e : fderiv ℝ (fun z => hamField H t (z + fun i => (k i : ℝ))) y
          = fderiv ℝ (fun z => hamField H t z) (y + fun i => (k i : ℝ)) :=
        fderiv_comp_add_right (f := fun z => hamField H t z) _
      have h : (fun z => hamField H t (z + fun i => (k i : ℝ))) = fun z => hamField H t z :=
        funext (hamField_lattice hHlat k t)
      rw [h] at e
      exact e.symm)
  refine ⟨K, fun t a b => ?_⟩
  have hdiff : Differentiable ℝ fun y => hamField H t y :=
    (hX.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x) (fun x _ => hK x t)
    convex_univ (Set.mem_univ b) (Set.mem_univ a)

/-- The action of a `C¹` loop does not change when the loop is translated by a period of
`H`: the term `∫₀¹ ω(c, ẋ)` vanishes because `ẋ` integrates to `x(1) - x(0) = 0`. -/
theorem action_sub_const (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    {c : (l ⊕ l) → ℝ} (hc : ∀ y t, H (y + c) t = H y t)
    {x x' : ℝ → ((l ⊕ l) → ℝ)} (hx : ∀ t, HasDerivAt x (x' t) t) (hx'c : Continuous x')
    (hper : Function.Periodic x 1) :
    action H (fun t => x t - c) = action H x := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hHc : Continuous fun t => H (x t) t := hH.continuous.comp (hxc.prodMk continuous_id)
  have hzero : (∫ t in (0:ℝ)..1, stdForm l c (x' t)) = 0 := by
    have hder : ∀ t, HasDerivAt (fun τ => stdForm l c (x τ)) (stdForm l c (x' t)) t := fun t => by
      have := hasDerivAt_stdForm (l := l) (hasDerivAt_const t c) (hx t)
      exact this.congr_deriv (by simp)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      ((continuous_stdForm continuous_const hx'c).intervalIntegrable 0 1)]
    have h1 : x 1 = x 0 := by simpa using hper 0
    rw [h1, sub_self]
  have hInt1 : IntervalIntegrable (fun t => H (x t) t - 1 / 2 * stdForm l (x t) (x' t))
      MeasureTheory.volume 0 1 :=
    (hHc.sub (continuous_const.mul (continuous_stdForm hxc hx'c))).intervalIntegrable 0 1
  have hInt2 : IntervalIntegrable (fun t => 1 / 2 * stdForm l c (x' t))
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_stdForm continuous_const hx'c)).intervalIntegrable 0 1
  have e1 : action H (fun t => x t - c) = ∫ t in (0:ℝ)..1,
      ((H (x t) t - 1 / 2 * stdForm l (x t) (x' t)) + 1 / 2 * stdForm l c (x' t)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    show H (x t - c) t - 1 / 2 * stdForm l (x t - c) (deriv (fun t => x t - c) t)
      = (H (x t) t - 1 / 2 * stdForm l (x t) (x' t)) + 1 / 2 * stdForm l c (x' t)
    have h1 : H (x t - c) t = H (x t) t := by
      have := hc (x t - c) t
      rw [sub_add_cancel] at this
      exact this.symm
    rw [((hx t).sub_const c).deriv, h1, map_sub, LinearMap.sub_apply]
    ring
  have e2 : action H x = ∫ t in (0:ℝ)..1, (H (x t) t - 1 / 2 * stdForm l (x t) (x' t)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    show H (x t) t - 1 / 2 * stdForm l (x t) (deriv x t)
      = H (x t) t - 1 / 2 * stdForm l (x t) (x' t)
    rw [(hx t).deriv]
  rw [e1, e2, intervalIntegral.integral_add hInt1 hInt2, intervalIntegral.integral_const_mul,
    hzero, mul_zero, add_zero]

/-- **The core of Proposition 6.5.7.**  Along any sequence `s_k` on which the energy of the
loops `u(s_k, ·)` tends to `0`, a subsequence of the actions converges to the action of a
`1`-periodic orbit.

After translation by lattice vectors the starting points lie in the unit cube, so a
subsequence of them converges.  The loops solve Hamilton's equation up to the error
`J₀ ∂u/∂s`, which tends to `0` in `L¹` over a period, so by
`ApproxOrbit.exists_orbit_of_approx` they converge at every time to a periodic orbit `x`.
The action passes to the limit by dominated convergence, the contribution `∫ ω(y, J₀ ∂u/∂s)`
of the error being controlled by its `L¹` norm. -/
theorem exists_orbit_tendsto_action (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    (hHt : ∀ y t, H y (t + 1) = H y t)
    (hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u) {s : ℕ → ℝ}
    (hs : Tendsto (fun k => ∫ t in (0:ℝ)..1, energyDensity u (s k) t) atTop (𝓝 0)) :
    ∃ (x : ℝ → ((l ⊕ l) → ℝ)) (φ : ℕ → ℕ), IsPeriodicOrbit (hamField H) x ∧ StrictMono φ ∧
      Tendsto (fun k => action H (u (s (φ k)))) atTop (𝓝 (action H x)) := by
  have hH1 : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2 :=
    hH.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hXc : Continuous fun q : ℝ × ((l ⊕ l) → ℝ) => hamField H q.1 q.2 :=
    (contDiff_hamField H hH).continuous
  obtain ⟨M₀, hM₀⟩ := exists_bound_of_lattice_periodic (f := H) hH1.continuous hHt hHlat
  obtain ⟨M₁, hM₁⟩ := exists_bound_of_lattice_periodic (f := fun x t => hamField H t x)
    (hXc.comp (continuous_snd.prodMk continuous_fst)) (fun y t => hamField_periodic hHt t y)
    (fun k y t => hamField_lattice hHlat k t y)
  obtain ⟨K, hK⟩ := exists_lipschitz_hamField H hH hHt hHlat
  obtain ⟨Cω, hCω0, hCω⟩ := exists_bound_stdForm (l := l)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0 0)
  -- translate each loop by a lattice vector, so that it starts in the unit cube
  have hlat : ∀ k : ℕ, ∃ c : (l ⊕ l) → ℝ, (∀ y t, H (y + c) t = H y t) ∧
      (∀ t y, hamField H t (y + c) = hamField H t y) ∧ ‖u (s k) 0 - c‖ ≤ 1 := by
    intro k
    refine ⟨fun i => ((⌊u (s k) 0 i⌋ : ℤ) : ℝ), fun y t => hHlat (fun i => ⌊u (s k) 0 i⌋) y t,
      fun t y => hamField_lattice hHlat (fun i => ⌊u (s k) 0 i⌋) t y, ?_⟩
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    show ‖u (s k) 0 i - ⌊u (s k) 0 i⌋‖ ≤ 1
    rw [Int.self_sub_floor, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  choose c hcH hcX hc1 using hlat
  obtain ⟨p, -, φ, hφ, hpφ⟩ := (isCompact_closedBall (0 : (l ⊕ l) → ℝ) 1).tendsto_subseq
    (x := fun k => u (s k) 0 - c k) (fun k => mem_closedBall_zero_iff.2 (hc1 k))
  obtain ⟨y, hydef⟩ : ∃ y : ℕ → ℝ → ((l ⊕ l) → ℝ), y = fun k t => u (s (φ k)) t - c (φ k) :=
    ⟨_, rfl⟩
  have hyk : ∀ k t, y k t = u (s (φ k)) t - c (φ k) := fun k t => by rw [hydef]
  have hyf : ∀ k, y k = fun t => u (s (φ k)) t - c (φ k) := fun k => funext (hyk k)
  have hy : ∀ k t, HasDerivAt (y k) (dT u (s (φ k)) t) t := fun k t => by
    rw [hyf k]
    exact (hu.hasDerivAt_t (s (φ k)) t).sub_const _
  have hyc : ∀ k, Continuous (y k) := fun k =>
    continuous_iff_continuousAt.2 fun t => (hy k t).continuousAt
  have hy'c : ∀ k, Continuous (dT u (s (φ k))) := fun k =>
    hu.continuous_t.comp (continuous_const.prodMk continuous_id)
  have hper : ∀ k, Function.Periodic (y k) 1 := fun k t => by
    rw [hyk, hyk, hu.periodic (s (φ k)) t]
  -- the error is `J₀ ∂u/∂s`
  have herr : ∀ k t, dT u (s (φ k)) t - hamField H t (y k t) = stdJ l (dS u (s (φ k)) t) := by
    intro k t
    have h := hcX (φ k) t (u (s (φ k)) t - c (φ k))
    rw [sub_add_cancel] at h
    rw [hyk, ← h]
    exact floer_eq H hu _ _
  have hnorm : ∀ k t, (dT u (s (φ k)) t - hamField H t (y k t))
      ⬝ᵥ (dT u (s (φ k)) t - hamField H t (y k t)) = energyDensity u (s (φ k)) t := by
    intro k t
    rw [herr, stdJ_dotProduct]
    rfl
  have hec : ∀ k, Continuous fun t => dT u (s (φ k)) t - hamField H t (y k t) := fun k =>
    (hy'c k).sub (hXc.comp (continuous_id.prodMk (hyc k)))
  have heper : ∀ k, Function.Periodic
      (fun t => ‖dT u (s (φ k)) t - hamField H t (y k t)‖) 1 := by
    intro k t
    show ‖dT u (s (φ k)) (t + 1) - hamField H (t + 1) (y k (t + 1))‖
      = ‖dT u (s (φ k)) t - hamField H t (y k t)‖
    rw [ApproxOrbit.periodic_deriv (hy k) (hper k) t, hamField_periodic hHt, hper k t]
  have hedc : ∀ k, Continuous fun t => energyDensity u (s (φ k)) t := fun k => by
    have h : Continuous fun t => dS u (s (φ k)) t :=
      hu.continuous_s.comp (continuous_const.prodMk continuous_id)
    exact continuous_dot₂ h h
  -- its `L¹` norm tends to `0`
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ,
      η = fun k => ∫ t in (0:ℝ)..1, ‖dT u (s (φ k)) t - hamField H t (y k t)‖ := ⟨_, rfl⟩
  have hηk : ∀ k, η k = ∫ t in (0:ℝ)..1, ‖dT u (s (φ k)) t - hamField H t (y k t)‖ :=
    fun k => by rw [hηdef]
  have hη0 : ∀ k, 0 ≤ η k := fun k => by
    rw [hηk]
    exact intervalIntegral.integral_nonneg zero_le_one fun τ _ => norm_nonneg _
  have hg : Tendsto (fun k => ∫ t in (0:ℝ)..1, energyDensity u (s (φ k)) t) atTop (𝓝 0) :=
    hs.comp hφ.tendsto_atTop
  have hηle : ∀ δ : ℝ, 0 < δ → ∀ k,
      η k ≤ δ / 2 + (∫ t in (0:ℝ)..1, energyDensity u (s (φ k)) t) / (2 * δ) := by
    intro δ hδ k
    have hcont : Continuous fun t => δ / 2 + energyDensity u (s (φ k)) t / (2 * δ) :=
      continuous_const.add ((hedc k).div_const _)
    rw [hηk]
    calc ∫ t in (0:ℝ)..1, ‖dT u (s (φ k)) t - hamField H t (y k t)‖
        ≤ ∫ t in (0:ℝ)..1, (δ / 2 + energyDensity u (s (φ k)) t / (2 * δ)) :=
          intervalIntegral.integral_mono_on zero_le_one ((hec k).norm.intervalIntegrable _ _)
            (hcont.intervalIntegrable _ _) fun t _ => by
              rw [← hnorm k t]
              exact ApproxOrbit.norm_le_add_dotProduct _ hδ
      _ = δ / 2 + (∫ t in (0:ℝ)..1, energyDensity u (s (φ k)) t) / (2 * δ) := by
          rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
            (((hedc k).div_const _).intervalIntegrable _ _), intervalIntegral.integral_const,
            intervalIntegral.integral_div]
          simp
  have hE : Tendsto η atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k => ha.trans_le (hη0 k),
      fun ε hε => ?_⟩
    have hε2 : 0 < ε ^ 2 := by positivity
    filter_upwards [(tendsto_order.1 hg).2 (ε ^ 2) hε2] with k hk
    have h1 := hηle ε hε k
    have h2 : (∫ t in (0:ℝ)..1, energyDensity u (s (φ k)) t) / (2 * ε) < ε / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hE' : Tendsto (fun k => ∫ t in (0:ℝ)..1, ‖dT u (s (φ k)) t - hamField H t (y k t)‖)
      atTop (𝓝 0) := by
    rw [hηdef] at hE
    exact hE
  have hp : Tendsto (fun k => y k 0) atTop (𝓝 p) := by
    have he : (fun k => y k 0) = (fun k => u (s k) 0 - c k) ∘ φ := funext fun k => hyk k 0
    rw [he]
    exact hpφ
  -- the limiting orbit
  obtain ⟨x, hxd, hxper, hxlim⟩ := ApproxOrbit.exists_orbit_of_approx (X := hamField H)
    hXc hK (fun t a => hM₁ a t) hy hy'c hper heper hE' hp
  refine ⟨x, φ, ⟨hxd, hxper⟩, hφ, ?_⟩
  -- the loops are eventually bounded on `[0, 1]`
  have hybound : ∀ k, ∀ t ∈ Set.Icc (0:ℝ) 1, ‖y k t‖ ≤ 1 + M₁ + η k := by
    intro k t ht
    have hftc : ∫ τ in (0:ℝ)..t, dT u (s (φ k)) τ = y k t - y k 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hy k τ)
        ((hy'c k).intervalIntegrable 0 t)
    have hcont : Continuous fun τ => M₁ + ‖dT u (s (φ k)) τ - hamField H τ (y k τ)‖ :=
      continuous_const.add (hec k).norm
    have h1 : ‖y k t - y k 0‖ ≤ M₁ + η k := by
      rw [← hftc, hηk]
      calc ‖∫ τ in (0:ℝ)..t, dT u (s (φ k)) τ‖
          ≤ ∫ τ in (0:ℝ)..t, ‖dT u (s (φ k)) τ‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht.1
        _ ≤ ∫ τ in (0:ℝ)..t, (M₁ + ‖dT u (s (φ k)) τ - hamField H τ (y k τ)‖) :=
            intervalIntegral.integral_mono_on ht.1 ((hy'c k).norm.intervalIntegrable _ _)
              (hcont.intervalIntegrable _ _) fun τ _ => by
                have e : dT u (s (φ k)) τ = hamField H τ (y k τ)
                    + (dT u (s (φ k)) τ - hamField H τ (y k τ)) := by abel
                calc ‖dT u (s (φ k)) τ‖
                    = ‖hamField H τ (y k τ)
                        + (dT u (s (φ k)) τ - hamField H τ (y k τ))‖ := by rw [← e]
                  _ ≤ ‖hamField H τ (y k τ)‖
                        + ‖dT u (s (φ k)) τ - hamField H τ (y k τ)‖ := norm_add_le _ _
                  _ ≤ M₁ + ‖dT u (s (φ k)) τ - hamField H τ (y k τ)‖ :=
                      add_le_add_left (hM₁ _ _) _
        _ ≤ ∫ τ in (0:ℝ)..1, (M₁ + ‖dT u (s (φ k)) τ - hamField H τ (y k τ)‖) :=
            intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
              (Eventually.of_forall fun τ => add_nonneg hM₁0 (norm_nonneg _))
              (hcont.intervalIntegrable _ _)
        _ = M₁ + ∫ τ in (0:ℝ)..1, ‖dT u (s (φ k)) τ - hamField H τ (y k τ)‖ := by
            rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
              ((hec k).norm.intervalIntegrable _ _), intervalIntegral.integral_const]
            simp
    have h0 : ‖y k 0‖ ≤ 1 := by
      rw [hyk]
      exact hc1 (φ k)
    calc ‖y k t‖ = ‖y k 0 + (y k t - y k 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖y k 0‖ + ‖y k t - y k 0‖ := norm_add_le _ _
      _ ≤ 1 + (M₁ + η k) := add_le_add h0 h1
      _ = 1 + M₁ + η k := by ring
  have hR : ∀ᶠ k in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1, ‖y k t‖ ≤ 2 + M₁ := by
    filter_upwards [(tendsto_order.1 hE).2 1 one_pos] with k hk t ht
    linarith [hybound k t ht]
  -- the action of the translated loop, split along `ẏ = X_t(y) + error`
  have hact1 : ∀ k, action H (u (s (φ k))) = action H (y k) := fun k => by
    rw [hyf k]
    exact (action_sub_const H hH1 (hcH (φ k)) (hu.hasDerivAt_t (s (φ k))) (hy'c k)
      (hu.periodic (s (φ k)))).symm
  have hHyc : ∀ k, Continuous fun t => H (y k t) t := fun k =>
    hH1.continuous.comp ((hyc k).prodMk continuous_id)
  have hXyc : ∀ k, Continuous fun t => hamField H t (y k t) := fun k =>
    hXc.comp (continuous_id.prodMk (hyc k))
  have hAc : ∀ k, Continuous fun t =>
      H (y k t) t - 1 / 2 * stdForm l (y k t) (hamField H t (y k t)) := fun k =>
    (hHyc k).sub (continuous_const.mul (continuous_stdForm₂ (hyc k) (hXyc k)))
  have hBc : ∀ k, Continuous fun t =>
      stdForm l (y k t) (dT u (s (φ k)) t - hamField H t (y k t)) := fun k =>
    continuous_stdForm₂ (hyc k) (hec k)
  have hact2 : ∀ k, action H (y k)
      = (∫ t in (0:ℝ)..1, (H (y k t) t - 1 / 2 * stdForm l (y k t) (hamField H t (y k t))))
        - 1 / 2 * ∫ t in (0:ℝ)..1,
            stdForm l (y k t) (dT u (s (φ k)) t - hamField H t (y k t)) := by
    intro k
    have hBc' : Continuous fun t =>
        1 / 2 * stdForm l (y k t) (dT u (s (φ k)) t - hamField H t (y k t)) :=
      continuous_const.mul (hBc k)
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((hAc k).intervalIntegrable _ _) (hBc'.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show H (y k t) t - 1 / 2 * stdForm l (y k t) (deriv (y k) t)
      = H (y k t) t - 1 / 2 * stdForm l (y k t) (hamField H t (y k t))
        - 1 / 2 * stdForm l (y k t) (dT u (s (φ k)) t - hamField H t (y k t))
    rw [(hy k t).deriv, map_sub]
    ring
  -- the main term converges by dominated convergence
  have hactx : action H x
      = ∫ t in (0:ℝ)..1, (H (x t) t - 1 / 2 * stdForm l (x t) (hamField H t (x t))) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    show H (x t) t - 1 / 2 * stdForm l (x t) (deriv x t)
      = H (x t) t - 1 / 2 * stdForm l (x t) (hamField H t (x t))
    rw [(hxd t).deriv]
  have hΨ : ∀ t, Continuous fun a : (l ⊕ l) → ℝ =>
      H a t - 1 / 2 * stdForm l a (hamField H t a) := fun t =>
    (hH1.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (continuous_const.mul (continuous_stdForm₂ continuous_id
        (hXc.comp (continuous_const.prodMk continuous_id))))
  have limA : Tendsto (fun k => ∫ t in (0:ℝ)..1,
      (H (y k t) t - 1 / 2 * stdForm l (y k t) (hamField H t (y k t)))) atTop
      (𝓝 (action H x)) := by
    rw [hactx]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M₀ + 1 / 2 * (Cω * (2 + M₁) * M₁))
      (Eventually.of_forall fun k => (hAc k).aestronglyMeasurable) ?_
      intervalIntegrable_const
      (Eventually.of_forall fun t _ => ((hΨ t).tendsto (x t)).comp (hxlim t))
    filter_upwards [hR] with k hk
    refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hyt := hk t (Set.Ioc_subset_Icc_self ht)
    have h1 : |H (y k t) t| ≤ M₀ := by
      have := hM₀ (y k t) t
      rwa [Real.norm_eq_abs] at this
    have h2 : |stdForm l (y k t) (hamField H t (y k t))| ≤ Cω * (2 + M₁) * M₁ :=
      (hCω _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hyt hCω0) (hM₁ _ _)
        (norm_nonneg _) (mul_nonneg hCω0 (by linarith)))
    rw [Real.norm_eq_abs]
    obtain ⟨h3, h4⟩ := abs_le.mp h1
    obtain ⟨h5, h6⟩ := abs_le.mp h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- and the error term tends to `0`
  have limB : Tendsto (fun k => ∫ t in (0:ℝ)..1,
      stdForm l (y k t) (dT u (s (φ k)) t - hamField H t (y k t))) atTop (𝓝 0) := by
    have hlim0 : Tendsto (fun k => Cω * (2 + M₁) * η k) atTop (𝓝 0) := by
      have := hE.const_mul (Cω * (2 + M₁))
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [hR] with k hk
    rw [hηk, ← intervalIntegral.integral_const_mul]
    calc ‖∫ t in (0:ℝ)..1, stdForm l (y k t) (dT u (s (φ k)) t - hamField H t (y k t))‖
        ≤ ∫ t in (0:ℝ)..1, ‖stdForm l (y k t) (dT u (s (φ k)) t - hamField H t (y k t))‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ t in (0:ℝ)..1,
            Cω * (2 + M₁) * ‖dT u (s (φ k)) t - hamField H t (y k t)‖ :=
          intervalIntegral.integral_mono_on zero_le_one ((hBc k).norm.intervalIntegrable _ _)
            ((continuous_const.mul (hec k).norm).intervalIntegrable _ _) fun t ht => by
              rw [Real.norm_eq_abs]
              exact (hCω _ _).trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hk t ht) hCω0) (norm_nonneg _))
  have hfinal : Tendsto (fun k =>
      (∫ t in (0:ℝ)..1, (H (y k t) t - 1 / 2 * stdForm l (y k t) (hamField H t (y k t))))
        - 1 / 2 * ∫ t in (0:ℝ)..1,
            stdForm l (y k t) (dT u (s (φ k)) t - hamField H t (y k t))) atTop
      (𝓝 (action H x - 1 / 2 * 0)) := limA.sub (limB.const_mul _)
  rw [mul_zero, sub_zero] at hfinal
  refine hfinal.congr fun k => ?_
  rw [hact1 k, hact2 k]

/-- **Proposition 6.5.7.**  For a finite-energy solution the action converges at
both ends to critical values of `A_H`.

**Proved**, and without the two tools the book uses.  The energy being finite,
there are sequences `s_k → ±∞` along which `‖∂u/∂t − X_t(u)‖_{L²(S¹)}` tends to
`0` (`ApproxOrbit.exists_seq_atTop`).  The book then applies Ascoli and an
elliptic bootstrap (Lemma 6.5.9); here the loops `u(s_k, ·)`, translated into the
unit cube, are approximate solutions of Hamilton's equation with an error small
in `L¹`, so Grönwall's inequality makes them a Cauchy sequence at every time and
the limit is a periodic orbit (`exists_orbit_tendsto_action`).  The action passes
to the limit along the subsequence, and since it is monotone
(`action_antitone`) it converges along the whole half-line.

The finite-energy hypothesis and the torus hypotheses on `H` were missing from an
earlier statement, which was false without them.  For `H = 0` a non-constant
holomorphic cylinder `u(s, t) = e^{2π(s ± it)}` in `ℂ = ℝ²`, the sign fixed by
`J₀`, solves the Floer equation, and its action `± π e^{±4πs}` has no finite
limit.  For `H = e^{−|y|²}` on `ℝ²`, which is not lattice-invariant, the
negative gradient line leaving the origin has energy `1` and escapes to
infinity, so the action tends to `0`, which is not a critical value.
Smoothness of `H` is the book's standing assumption. -/
theorem exists_tendsto_action (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    (hHt : ∀ y t, H y (t + 1) = H y t)
    (hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t)
    {u : ℝ → ℝ → ((l ⊕ l) → ℝ)} (hu : IsFloerSolution H u)
    (hE : MeasureTheory.Integrable fun s => ∫ t in (0:ℝ)..1, energyDensity u s t) :
    ∃ x y : ℝ → ((l ⊕ l) → ℝ), IsPeriodicOrbit (hamField H) x ∧ IsPeriodicOrbit (hamField H) y ∧
      Filter.Tendsto (fun s => action H (u s)) Filter.atBot (nhds (action H x)) ∧
      Filter.Tendsto (fun s => action H (u s)) Filter.atTop (nhds (action H y)) := by
  have hH1 : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2 :=
    hH.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hanti := action_antitone H hH1 hu
  have h0 : ∀ s, 0 ≤ ∫ t in (0:ℝ)..1, energyDensity u s t := fun s =>
    intervalIntegral.integral_nonneg zero_le_one fun t _ => energyDensity_nonneg u s t
  obtain ⟨sm, hsm, hgm⟩ := ApproxOrbit.exists_seq_atBot hE h0
  obtain ⟨sp, hsp, hgp⟩ := ApproxOrbit.exists_seq_atTop hE h0
  obtain ⟨x, φ, hx, hφ, hlx⟩ := exists_orbit_tendsto_action H hH hHt hHlat hu hgm
  obtain ⟨y, ψ, hy, hψ, hly⟩ := exists_orbit_tendsto_action H hH hHt hHlat hu hgp
  exact ⟨x, y, hx, hy,
    ApproxOrbit.tendsto_atBot_of_antitone_of_seq hanti (hsm.comp hφ.tendsto_atTop) hlx,
    ApproxOrbit.tendsto_atTop_of_antitone_of_seq hanti (hsp.comp hψ.tendsto_atTop) hly⟩

end ActionLimit

/-- **Corollary 6.5.11.**  There is a constant `C > 0` bounding the energy of
every element of `M`.  The book's proof: the action converges at both ends to
critical values (Proposition 6.5.7), these form a bounded set, and
`E(u) = A_H(x) − A_H(y)` (Remark 6.5.2(3)); that is exactly the proof here,
with the boundedness of the critical values supplied by
`exists_bound_action_of_isPeriodicOrbit`.  Proposition 6.5.7 being proved, the
corollary rests on no assumption.

The smoothness of `H`, which Proposition 6.5.7 needs, was missing from an
earlier statement. -/
theorem exists_bound_action_energy (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    (hHt : ∀ y t, H y (t + 1) = H y t)
    (hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ → ((l ⊕ l) → ℝ), IsFloerSolution H u →
      MeasureTheory.Integrable (fun s => ∫ t in (0:ℝ)..1, energyDensity u s t) →
      energy u ≤ C := by
  have hH1 : ContDiff ℝ 1 fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2 :=
    hH.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  obtain ⟨B, hB⟩ := exists_bound_action_of_isPeriodicOrbit H hH1 hHt hHlat
  refine ⟨2 * |B| + 1, by positivity, fun u hu hE => ?_⟩
  obtain ⟨x, y, hx, hy, hlx, hly⟩ := exists_tendsto_action H hH hHt hHlat hu hE
  rw [energy_eq_sub_action H hH1 hu hlx hly]
  obtain ⟨h1, h2⟩ := abs_le.mp (hB x hx)
  obtain ⟨h3, h4⟩ := abs_le.mp (hB y hy)
  linarith [le_abs_self B]

/-- **Theorem 6.5.6** (with Lemmas 6.5.13, 6.5.14 and Proposition 6.5.15).  If
all the periodic orbits of `X_t` are nondegenerate, every finite-energy solution
converges at `s → ±∞` to `1`-periodic orbits, and `∂u/∂s → 0` uniformly in `t`.

The book's proof uses the compactness of `M` (Theorem 6.5.4), the finiteness of
the set of critical points (Lemma 6.5.10) and the connectedness of the image of
a half-line.  It is stated here with pointwise convergence rather than
convergence in `C^∞(S¹; W)`, which has no topology available.

The torus hypotheses on `H` were missing from an earlier statement, which was
false without them: for `H = e^{−|y|²}` on `ℝ²` the only `1`-periodic orbit is
the origin, where the time-one map is the rotation by the angle `2`, so it is
nondegenerate; yet the negative gradient line leaving the origin is a solution
of energy `1` that escapes to infinity.  On the torus, `W` is compact and this
cannot happen. -/
theorem tendsto_of_finite_energy (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    (_hHt : ∀ y t, H y (t + 1) = H y t)
    (_hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t)
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
because `π₂(T^{2n}) = 0`.

Finite energy was missing from an earlier statement, which was false without
it: `energy` is a Bochner integral, hence `0` when the energy density is not
integrable, and for `H = 0` a non-constant holomorphic cylinder then has
"energy" `0` and an unbounded gradient. -/
theorem exists_gradient_bound (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    (_hHt : ∀ y t, H y (t + 1) = H y t)
    (_hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t) (C : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : ℝ → ℝ → ((l ⊕ l) → ℝ), IsFloerSolution H u →
      (MeasureTheory.Integrable fun s => ∫ t in (0:ℝ)..1, energyDensity u s t) → energy u ≤ C →
      ∀ s t, dS u s t ⬝ᵥ dS u s t + dT u s t ⬝ᵥ dT u s t ≤ A := by
  sorry

/-- **Theorem 6.5.4** (compactness of `M`).  Under Hypothesis 6.2.1 the space of
finite-energy solutions is compact in `C^∞_loc(ℝ × S¹, W)`.

Stated sequentially and on the torus: a sequence of solutions of uniformly
bounded energy has a subsequence which, after translation by lattice vectors,
converges uniformly on every compact subset of `ℝ × S¹` to a solution.  The
proof combines the gradient bound of Proposition 6.6.2, Ascoli's theorem and the
elliptic regularity of Proposition 6.5.3.

Finite energy was missing from an earlier statement, which was false without
it: with `H = 0` the holomorphic cylinders `u_n(s, t) = n e^{2π(s ± it)}` have
non-integrable energy density, so "energy" `0`, and their loops at `s = 0` have
radius `n`, so no translates converge. -/
theorem compactness_of_energy_bounded (H : ((l ⊕ l) → ℝ) → ℝ → ℝ)
    (_hH : ContDiff ℝ ∞ fun p : ((l ⊕ l) → ℝ) × ℝ => H p.1 p.2)
    (_hHt : ∀ y t, H y (t + 1) = H y t)
    (_hHlat : ∀ (k : (l ⊕ l) → ℤ) (y : (l ⊕ l) → ℝ) (t : ℝ),
      H (y + fun i => (k i : ℝ)) t = H y t) (C : ℝ)
    (u : ℕ → ℝ → ℝ → ((l ⊕ l) → ℝ)) (_hu : ∀ n, IsFloerSolution H (u n))
    (_hEi : ∀ n, MeasureTheory.Integrable fun s => ∫ t in (0:ℝ)..1, energyDensity (u n) s t)
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
the sequence is Cauchy, so `g` would be unbounded near its limit.  Mathlib has
exactly this as `hofer` (`Mathlib/Analysis/Hofer.lean`), written for the same
bubbling-off application, so all that is left here is to match the two
statements: Mathlib concludes on the closed ball `d(y, x) ≤ ε`, which contains
the open ball asked for here.

The book prints the first condition as `d(y, x₀) ≤ 2ε`; what the recursion gives
is `d(y, x₀) ≤ 2ε₀`, which is what is stated here. -/
theorem exists_half_maximum {X : Type*} [MetricSpace X] [CompleteSpace X] {g : X → ℝ}
    (hg : Continuous g) (hpos : ∀ x, 0 ≤ g x) (x₀ : X) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ (y : X) (ε : ℝ), 0 < ε ∧ ε ≤ ε₀ ∧ dist y x₀ ≤ 2 * ε₀ ∧ ε₀ * g x₀ ≤ ε * g y ∧
      ∀ x ∈ Metric.ball y ε, g x ≤ 2 * g y := by
  obtain ⟨ε, hεpos, y, hεle, hdist, hmul, hball⟩ := hofer x₀ ε₀ hε₀ hg hpos
  exact ⟨y, ε, hεpos, hεle, hdist, hmul, fun x hx => hball x
    (by rw [dist_comm]; exact (Metric.mem_ball.mp hx).le)⟩

end HalfMaximum

end Chapter6
end MorseFloer
