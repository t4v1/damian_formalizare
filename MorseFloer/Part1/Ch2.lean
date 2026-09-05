import MorseFloer.Basic

/-!
# Chapter 2: Pseudo-gradients

Formalization of Chapter 2 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part I, printed pages 21–48).

The chapter has three sections:

* **§2.1** introduces the gradient of a function on `ℝⁿ`, the notion of a
  *pseudo-gradient field adapted to a Morse function*, the *Morse charts*
  `U(ε, η)` with their three boundary pieces, the stable and unstable manifolds
  of a critical point (Proposition 2.1.5), the fact that every trajectory joins
  two critical points (Proposition 2.1.6), and the two sublevel-set theorems:
  the topology of `V^a` does not change as long as no critical value is crossed
  (Theorem 2.1.7, Remark 2.1.8, Reeb's theorem 2.1.9), and changes by the
  attachment of a cell of dimension the index when one is (Theorem 2.1.11).
* **§2.2** is the Smale condition (transversality of all stable and unstable
  manifolds), Remark 2.2.1, the free `ℝ`-action on the space `M(a,b)` of
  trajectories from `a` to `b` (Proposition 2.2.2, Remark 2.2.3), and Smale's
  genericity theorem 2.2.5 with its two lemmas 2.2.8 and 2.2.9.
* **§2.3** is an appendix: adapted fields on a manifold with boundary, the
  classification of compact 1-manifolds (Theorem 2.3.2) and Brouwer's fixed
  point theorem (Theorem 2.3.3).

Everything analytic is stated in the **local model**: a normed space `E`, with
`IsCriticalPt f x : fderiv ℝ f x = 0`, vector fields as maps `X : E → E`, and
flows as terms of Mathlib's `Flow ℝ E`.  This is where the book's proofs live
and it is what Mathlib supports.

## Status

Proved here:

* `-∇f` is a pseudo-gradient (the two properties (1) and (2) of §2.1.a);
* the chain rule along a trajectory, and monotonicity: `f` is nonincreasing
  along any trajectory of a pseudo-gradient and *strictly* decreasing along a
  trajectory containing no critical point;
* the two halves of the proof of Proposition 2.1.6 that are analytic: `f` is
  convergent along a forward trajectory that stays in a compact set, and
  therefore `df(X)` cannot stay below a negative constant (`frequently_fderiv_gt`);
* the Morse model of §2.1.b: `−grad Q` is a pseudo-gradient for the normal form
  `Q = −‖x₋‖² + ‖x₊‖²`, its flow is `(e^{2s}x₋, e^{−2s}x₊)`, and the stable set
  of the origin is exactly `V₊` (the model half of §2.1.d);
* elementary properties of stable/unstable sets for a flow: invariance,
  disjointness, self-membership at a fixed point;
* the real-analysis core of Theorem 2.1.7 (`descend_of_deriv_eq_neg_one`) and
  its consequence that the time-`(b−a)` map of the normalized flow carries `V^b`
  into `V^a`;
* Remark 2.2.1: `W^u(a) ∩ W^s(b) = ∅` when `a ≠ b` and `f(a) ≤ f(b)`;
* Proposition 2.2.2: the `ℝ`-action on `M(a,b)` is free for `a ≠ b`;
* Remark 2.2.3: a trajectory in `M(a,b)` meets an intermediate level exactly
  once, so `L(a,b)` is identified with `M(a,b) ∩ f⁻¹(α)`;
* Lemma 2.2.9 in its model: the perturbed field `−∂/∂z − β(z)∂/∂x` moves the
  point `(0,0)` to `(∫₀^m β, m)` in time `−m`.

Assumed (`sorry`): Proposition 2.1.6 (convergence of a trajectory to a critical
point — the proof uses Morse charts, which need the Morse lemma), Reeb's
theorem 2.1.9, the classification of compact connected 1-manifolds (2.3.2) and
Brouwer's theorem (2.3.3), none of which Mathlib can currently prove.  Brouwer
is assumed only in dimension `≥ 2`: `brouwer_dim_zero` and `brouwer_dim_one`
prove the low-dimensional case in full, the latter by the intermediate value
theorem.  The docstring of `brouwer` records why the general case is out of
reach — no homology of spheres (no excision, no Mayer–Vietoris), no
`π₁(S¹) ≅ ℤ`, no Sperner lemma and no degree theory.

Omitted, because today's Mathlib cannot even state them faithfully:

* **Proposition 2.1.5** (stable and unstable manifolds are submanifolds
  diffeomorphic to open disks, of dimensions `Ind(a)` and `n − Ind(a)`): there
  is no API making a subset of a manifold a submanifold with its own smooth
  structure, so neither the submanifold claim nor the dimension count can be
  written down.  Only the model computation, `stableSet_modelFlow`, is given.
* **Theorem 2.1.7** in its full form (`V^b` is *diffeomorphic* to `V^a`) and
  **Remark 2.1.8** (deformation retraction): sublevel sets are manifolds with
  boundary and there is no `Diffeomorph` between subsets.  The flow statement
  `flow_mapsTo_sublevel` records what is provable.
* **Theorem 2.1.11** (`V^{α+ε}` has the homotopy type of `V^{α−ε}` with a
  `k`-cell attached): adjunction spaces/cell attachments are not available.
* **The Smale condition** itself (`W^u(a) ⋔ W^s(b)`) and everything resting on
  it — the dimension count `dim M(a,b) = Ind(a) − Ind(b)`, the manifold
  structure of `M(a,b)` and `L(a,b)`, **Theorem 2.2.5** (Smale's genericity
  theorem) and **Lemma 2.2.8**: transversality of submanifolds, the `C¹`
  topology on vector fields, Sard's theorem and tubular neighbourhoods are all
  missing.  What survives here is the order-theoretic content (Remark 2.2.1 and
  Proposition 2.2.2) and the model computation of Lemma 2.2.9.
* **§2.3.a** (inward-pointing fields along the boundary, and the construction of
  a Morse function with `df(X) < 0` near `∂V`): manifolds with boundary exist in
  Mathlib but there is no notion of an inward-pointing vector along the
  boundary.
-/

open scoped Manifold ContDiff
open Filter Set Topology

namespace MorseFloer
namespace Chapter2

/-! ## §2.1.a Gradients and pseudo-gradients -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A critical point of `f : E → ℝ` in the local model. -/
def IsCriticalPt (f : E → ℝ) (x : E) : Prop := fderiv ℝ f x = 0

/-- **A pseudo-gradient field adapted to `f`** (§2.1.a, condition (1)).

`X` is a vector field along which `f` never increases, and which is "stalled"
exactly at the critical points of `f`.  The book's condition (2) — that in a
Morse chart around a critical point `X` is the negative of the euclidean
gradient — is recorded separately as `IsMorseChart` below, since it needs the
Morse lemma to make sense. -/
structure IsPseudoGradient (f : E → ℝ) (X : E → E) : Prop where
  /-- `df(X) ≤ 0`: the function does not increase along the field. -/
  nonpos : ∀ x, fderiv ℝ f x (X x) ≤ 0
  /-- `df(X)` vanishes exactly at the critical points. -/
  eq_zero_iff : ∀ x, fderiv ℝ f x (X x) = 0 ↔ IsCriticalPt f x

/-- Away from the critical points, a pseudo-gradient makes `f` strictly
decrease. -/
theorem IsPseudoGradient.neg_of_not_isCriticalPt {f : E → ℝ} {X : E → E}
    (hX : IsPseudoGradient f X) {x : E} (hx : ¬ IsCriticalPt f x) :
    fderiv ℝ f x (X x) < 0 :=
  lt_of_le_of_ne (hX.nonpos x) fun h => hx ((hX.eq_zero_iff x).mp h)

end Defs

/-! ### The gradient of a function on an inner product space

The two properties of `−grad f` singled out in §2.1.a: it vanishes exactly at
the critical points, and `f` decreases along it at the rate `−‖grad f‖²`. -/

section Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Property (1) of the gradient** (§2.1.a): `grad f` vanishes exactly at the
critical points of `f`. -/
theorem gradient_eq_zero_iff (f : F → ℝ) (x : F) :
    gradient f x = 0 ↔ IsCriticalPt f x := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun y => ?_
    have h2 := inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := y)
    rw [h] at h2
    simp only [inner_zero_left] at h2
    simpa using h2.symm
  · intro h
    have h2 := inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := gradient f x)
    have h3 : (inner ℝ (gradient f x) (gradient f x) : ℝ) = 0 := by
      rw [h2, show fderiv ℝ f x = 0 from h]
      simp
    exact inner_self_eq_zero.mp h3

/-- **Property (2) of the gradient** (§2.1.a): the derivative of `f` along
`−grad f` is `−‖grad f‖²`. -/
theorem fderiv_neg_gradient (f : F → ℝ) (x : F) :
    fderiv ℝ f x (-gradient f x) = -‖gradient f x‖ ^ 2 := by
  have h := inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := -gradient f x)
  rw [← h, inner_neg_right, real_inner_self_eq_norm_sq]

/-- **The negative gradient is a pseudo-gradient** (§2.1.a, and §2.1.c: this is
the local model of the partition-of-unity construction, in which the field is
patched together from euclidean gradients read in charts). -/
theorem isPseudoGradient_neg_gradient (f : F → ℝ) :
    IsPseudoGradient f (fun x => -gradient f x) := by
  constructor
  · intro x
    show fderiv ℝ f x (-gradient f x) ≤ 0
    rw [fderiv_neg_gradient]
    exact neg_nonpos.mpr (sq_nonneg _)
  · intro x
    show fderiv ℝ f x (-gradient f x) = 0 ↔ IsCriticalPt f x
    rw [fderiv_neg_gradient]
    constructor
    · intro h
      refine (gradient_eq_zero_iff f x).mp ?_
      have h2 : ‖gradient f x‖ ^ 2 = 0 := by linarith
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)
    · intro h
      rw [(gradient_eq_zero_iff f x).mpr h, norm_zero]
      norm_num

end Gradient

/-! ### Trajectories of a pseudo-gradient

The book's key computation: along a trajectory `γ` of `X`,
`(f ∘ γ)'(s) = (df)_{γ(s)}(X_{γ(s)})`, so `f` is nonincreasing, and strictly
decreasing as long as no critical point is met. -/

section Trajectories

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chain rule along an integral curve of `X`. -/
theorem hasDerivAt_comp_integralCurve {f : E → ℝ} {X : E → E} {γ : ℝ → E}
    (hf : Differentiable ℝ f) (hγ : IsIntegralCurve γ fun _ => X) (t : ℝ) :
    HasDerivAt (fun s => f (γ s)) (fderiv ℝ f (γ t) (X (γ t))) t :=
  (hf (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)

/-- **`f` is nonincreasing along a trajectory of a pseudo-gradient** (§2.1.a). -/
theorem antitone_comp_integralCurve {f : E → ℝ} {X : E → E} {γ : ℝ → E}
    (hf : Differentiable ℝ f) (hX : IsPseudoGradient f X)
    (hγ : IsIntegralCurve γ fun _ => X) : Antitone fun s => f (γ s) := by
  refine antitone_of_deriv_nonpos (fun t => (hasDerivAt_comp_integralCurve hf hγ t).differentiableAt)
    fun t => ?_
  rw [(hasDerivAt_comp_integralCurve hf hγ t).deriv]
  exact hX.nonpos _

/-- **`f` strictly decreases along a trajectory that meets no critical point**
(§2.1.a).  This is the property that makes a pseudo-gradient a Lyapunov field
for `f`. -/
theorem strictAnti_comp_integralCurve {f : E → ℝ} {X : E → E} {γ : ℝ → E}
    (hf : Differentiable ℝ f) (hX : IsPseudoGradient f X)
    (hγ : IsIntegralCurve γ fun _ => X) (hc : ∀ t, ¬ IsCriticalPt f (γ t)) :
    StrictAnti fun s => f (γ s) :=
  strictAnti_of_hasDerivAt_neg (fun t => hasDerivAt_comp_integralCurve hf hγ t)
    fun t => hX.neg_of_not_isCriticalPt (hc t)

/-- **The linear escape estimate.**  If `df(X) ≤ −ε` from time `s₀` on, then
`f(γ(t)) ≤ f(γ(s₀)) − ε(t − s₀)`.  This is the integral estimate used in the
proof of Proposition 2.1.6. -/
theorem le_sub_of_fderiv_le {f : E → ℝ} {X : E → E} {γ : ℝ → E} {ε s₀ : ℝ}
    (hf : Differentiable ℝ f) (hγ : IsIntegralCurve γ fun _ => X)
    (hb : ∀ t, s₀ ≤ t → fderiv ℝ f (γ t) (X (γ t)) ≤ -ε) :
    ∀ t, s₀ ≤ t → f (γ t) ≤ f (γ s₀) - ε * (t - s₀) := by
  intro t ht
  have hd : ∀ u : ℝ, HasDerivAt (fun u => f (γ u) + ε * u)
      (fderiv ℝ f (γ u) (X (γ u)) + ε) u := by
    intro u
    have h1 : HasDerivAt (fun u => f (γ u)) (fderiv ℝ f (γ u) (X (γ u))) u :=
      hasDerivAt_comp_integralCurve hf hγ u
    have h2 : HasDerivAt (fun u : ℝ => ε * u) ε u := by
      simpa using (hasDerivAt_id u).const_mul ε
    exact h1.add h2
  have hanti : AntitoneOn (fun u => f (γ u) + ε * u) (Ici s₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici s₀)
      (fun u _ => ((hd u).differentiableAt.continuousAt).continuousWithinAt)
      (fun u _ => (hd u).differentiableAt.differentiableWithinAt) fun u hu => ?_
    rw [interior_Ici] at hu
    rw [(hd u).deriv]
    have := hb u (le_of_lt hu)
    linarith
  have h3 : f (γ t) + ε * t ≤ f (γ s₀) + ε * s₀ :=
    hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have hmul : ε * (t - s₀) = ε * t - ε * s₀ := by ring
  linarith

omit [NormedSpace ℝ E] in
/-- If a forward trajectory stays in a compact set, `f` is bounded below along
it. -/
theorem bddBelow_range_comp {f : E → ℝ} {γ : ℝ → E} {K : Set E}
    (hf : Continuous f) (hK : IsCompact K) (hmem : ∀ s, γ s ∈ K) :
    BddBelow (Set.range fun s => f (γ s)) := by
  obtain ⟨c, hcK, hmin⟩ := hK.exists_isMinOn ⟨γ 0, hmem 0⟩ hf.continuousOn
  refine ⟨f c, ?_⟩
  rintro y ⟨s, rfl⟩
  exact isMinOn_iff.mp hmin _ (hmem s)

/-- Along a trajectory contained in a compact set, `f ∘ γ` converges as
`s → +∞`: it is nonincreasing and bounded below.  (Half of Proposition 2.1.6:
the value converges; identifying the limit point as a critical point is the part
that needs Morse charts.) -/
theorem tendsto_comp_integralCurve {f : E → ℝ} {X : E → E} {γ : ℝ → E}
    (hf : Differentiable ℝ f) (hX : IsPseudoGradient f X)
    (hγ : IsIntegralCurve γ fun _ => X)
    (hbdd : BddBelow (Set.range fun s => f (γ s))) :
    Tendsto (fun s => f (γ s)) atTop (𝓝 (⨅ s : ℝ, f (γ s))) :=
  tendsto_atTop_ciInf (antitone_comp_integralCurve hf hX hγ) hbdd

/-- **The contradiction step in the proof of Proposition 2.1.6.**  If `f` is
bounded below along a forward trajectory, then `df(X)` cannot remain below a
negative constant: it must come back above `−ε` at arbitrarily large times.

In the book this is what forces the trajectory to enter — and stay in — a Morse
chart: outside the union of the Morse charts one has `df(X) ≤ −ε₀`, and a
trajectory remaining there would send `f` to `−∞`. -/
theorem frequently_fderiv_gt {f : E → ℝ} {X : E → E} {γ : ℝ → E} {ε : ℝ}
    (hf : Differentiable ℝ f) (hγ : IsIntegralCurve γ fun _ => X)
    (hbdd : BddBelow (Set.range fun s => f (γ s))) (hε : 0 < ε) :
    ∃ᶠ s in atTop, -ε < fderiv ℝ f (γ s) (X (γ s)) := by
  by_contra hcon
  rw [not_frequently] at hcon
  rw [eventually_atTop] at hcon
  obtain ⟨s₀, hs₀⟩ := hcon
  have hb : ∀ t, s₀ ≤ t → fderiv ℝ f (γ t) (X (γ t)) ≤ -ε := fun t ht => not_lt.mp (hs₀ t ht)
  obtain ⟨C, hC⟩ := hbdd
  have hCle : ∀ t : ℝ, C ≤ f (γ t) := fun t => hC ⟨t, rfl⟩
  have hne : ε ≠ 0 := ne_of_gt hε
  have hpos : 0 < (f (γ s₀) - C + 1) / ε := div_pos (by linarith [hCle s₀]) hε
  have ht : s₀ ≤ s₀ + (f (γ s₀) - C + 1) / ε := by linarith
  have key := le_sub_of_fderiv_le hf hγ hb (s₀ + (f (γ s₀) - C + 1) / ε) ht
  have hts : s₀ + (f (γ s₀) - C + 1) / ε - s₀ = (f (γ s₀) - C + 1) / ε := by ring
  rw [hts] at key
  have hcancel : ε * ((f (γ s₀) - C + 1) / ε) = f (γ s₀) - C + 1 := by field_simp
  rw [hcancel] at key
  linarith [hCle (s₀ + (f (γ s₀) - C + 1) / ε)]

/-- **Proposition 2.1.6.**  On a compact manifold, every trajectory of a
pseudo-gradient comes from a critical point and goes to a critical point.

Stated here in the local model for the forward limit, with "the manifold is
compact" replaced by "the trajectory stays in a compact set".

`sorry`: the book's proof shows that the trajectory must enter the *Morse
chart* of some critical point and cannot leave it again; this needs the Morse
lemma (Theorem 1.3.1, itself a `sorry` in Chapter 1) and the local model of
§2.1.b.  The two analytic ingredients are proved above
(`tendsto_comp_integralCurve` and `frequently_fderiv_gt`). -/
theorem exists_isCriticalPt_tendsto {f : E → ℝ} {X : E → E} {γ : ℝ → E} {K : Set E}
    (_hf : ContDiff ℝ 2 f) (_hX : IsPseudoGradient f X)
    (_hnd : ∀ c, IsCriticalPt f c → IsNondegenerate (sndFDeriv f c))
    (_hγ : IsIntegralCurve γ fun _ => X) (_hK : IsCompact K) (_hmem : ∀ s, γ s ∈ K) :
    ∃ c, IsCriticalPt f c ∧ Tendsto γ atTop (𝓝 c) := by
  sorry

end Trajectories

/-! ## §2.1.b Morse charts

The local model of a nondegenerate critical point of index `i`: the space splits
as `V₋ × V₊` with `dim V₋ = i`, the function is the normal form
`Q(x) = −‖x₋‖² + ‖x₊‖²`, and the field is `−grad Q = 2(x₋, −x₊)`. -/

section MorseModel

variable {Fneg Fpos : Type*} [NormedAddCommGroup Fneg] [InnerProductSpace ℝ Fneg]
  [NormedAddCommGroup Fpos] [InnerProductSpace ℝ Fpos]

/-- The **normal form** `Q(x₋, x₊) = −‖x₋‖² + ‖x₊‖²` of the Morse lemma. -/
def modelQ (x : Fneg × Fpos) : ℝ := -‖x.1‖ ^ 2 + ‖x.2‖ ^ 2

/-- The field `−grad Q = 2(x₋, −x₊)` of §2.1.b. -/
def modelField (x : Fneg × Fpos) : Fneg × Fpos := ((2 : ℝ) • x.1, (-2 : ℝ) • x.2)

@[simp] theorem modelField_fst (x : Fneg × Fpos) : (modelField x).1 = (2 : ℝ) • x.1 := rfl

@[simp] theorem modelField_snd (x : Fneg × Fpos) : (modelField x).2 = (-2 : ℝ) • x.2 := rfl

/-- The differential of the normal form at `x`. -/
noncomputable def modelD (x : Fneg × Fpos) : (Fneg × Fpos) →L[ℝ] ℝ :=
  -((2 • innerSL ℝ x.1).comp (ContinuousLinearMap.fst ℝ Fneg Fpos))
    + (2 • innerSL ℝ x.2).comp (ContinuousLinearMap.snd ℝ Fneg Fpos)

theorem hasFDerivAt_modelQ (x : Fneg × Fpos) : HasFDerivAt modelQ (modelD x) x := by
  have h1 : HasFDerivAt (fun z : Fneg × Fpos => ‖z.1‖ ^ 2)
      ((2 • innerSL ℝ x.1).comp (ContinuousLinearMap.fst ℝ Fneg Fpos)) x :=
    (hasStrictFDerivAt_norm_sq x.1).hasFDerivAt.comp x hasFDerivAt_fst
  have h2 : HasFDerivAt (fun z : Fneg × Fpos => ‖z.2‖ ^ 2)
      ((2 • innerSL ℝ x.2).comp (ContinuousLinearMap.snd ℝ Fneg Fpos)) x :=
    (hasStrictFDerivAt_norm_sq x.2).hasFDerivAt.comp x hasFDerivAt_snd
  exact h1.neg.add h2

theorem fderiv_modelQ_apply (x h : Fneg × Fpos) :
    fderiv ℝ modelQ x h = 2 * inner ℝ x.2 h.2 - 2 * inner ℝ x.1 h.1 := by
  rw [(hasFDerivAt_modelQ x).fderiv]
  simp [modelD]
  ring

/-- `dQ(−grad Q) = −4(‖x₋‖² + ‖x₊‖²)`: the model computation behind property (2)
of §2.1.a. -/
theorem fderiv_modelQ_modelField (x : Fneg × Fpos) :
    fderiv ℝ modelQ x (modelField x) = -(4 * ‖x.1‖ ^ 2) - 4 * ‖x.2‖ ^ 2 := by
  rw [fderiv_modelQ_apply]
  simp only [modelField_fst, modelField_snd, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- The origin is the only critical point of the normal form. -/
theorem isCriticalPt_modelQ_iff (x : Fneg × Fpos) : IsCriticalPt modelQ x ↔ x = 0 := by
  constructor
  · intro h
    have h0 : fderiv ℝ modelQ x (modelField x) = 0 := by
      rw [show fderiv ℝ modelQ x = 0 from h]; simp
    rw [fderiv_modelQ_modelField] at h0
    have e1 : x.1 = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]))
    have e2 : x.2 = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]))
    exact Prod.ext_iff.mpr ⟨by simp [e1], by simp [e2]⟩
  · rintro rfl
    show fderiv ℝ modelQ (0 : Fneg × Fpos) = 0
    rw [(hasFDerivAt_modelQ (0 : Fneg × Fpos)).fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    simp [modelD]

/-- **The model field is a pseudo-gradient for the normal form** (§2.1.b).  This
is condition (2) in the definition of a pseudo-gradient, checked in the chart. -/
theorem isPseudoGradient_modelField :
    IsPseudoGradient (modelQ (Fneg := Fneg) (Fpos := Fpos)) modelField := by
  constructor
  · intro x
    rw [fderiv_modelQ_modelField]
    nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]
  · intro x
    rw [fderiv_modelQ_modelField, isCriticalPt_modelQ_iff]
    constructor
    · intro h
      have e1 : x.1 = 0 :=
        norm_eq_zero.mp (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]))
      have e2 : x.2 = 0 :=
        norm_eq_zero.mp (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]))
      exact Prod.ext_iff.mpr ⟨by simp [e1], by simp [e2]⟩
    · rintro rfl
      simp

/-- **The chart `U(ε, η)` of §2.1.b**: the part of the model where the normal
form takes values in `(−ε, ε)` and the product `‖x₋‖²‖x₊‖²` stays below
`η(ε + η)`. -/
def modelU (ε η : ℝ) : Set (Fneg × Fpos) :=
  {x | -ε < modelQ x ∧ modelQ x < ε ∧ ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 ≤ η * (ε + η)}

/-- The upper boundary `∂₊U = {Q = ε, ‖x₋‖² ≤ η}` of a Morse chart. -/
def modelBoundaryPos (ε η : ℝ) : Set (Fneg × Fpos) :=
  {x ∈ modelU ε η | modelQ x = ε ∧ ‖x.1‖ ^ 2 ≤ η}

/-- The lower boundary `∂₋U = {Q = −ε, ‖x₊‖² ≤ η}` of a Morse chart. -/
def modelBoundaryNeg (ε η : ℝ) : Set (Fneg × Fpos) :=
  {x ∈ modelU ε η | modelQ x = -ε ∧ ‖x.2‖ ^ 2 ≤ η}

/-- The lateral boundary `∂₀U = {‖x₋‖²‖x₊‖² = η(ε + η)}`, made of pieces of
trajectories of `grad Q`. -/
def modelBoundaryZero (ε η : ℝ) : Set (Fneg × Fpos) :=
  {x ∈ modelU ε η | ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 = η * (ε + η)}

/-- **Condition (2) in the definition of a pseudo-gradient** (§2.1.a–b): near a
critical point `c` there is a chart `φ` in which `f` becomes `f(c) + Q` and `X`
becomes `−grad Q`.  Such a `φ` is a *Morse chart adapted to `X`*.

This is a definition only: the existence of `φ` is the Morse lemma
(Theorem 1.3.1), which is a `sorry` in Chapter 1. -/
def IsMorseChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (X : E → E) (c : E) (φ : OpenPartialHomeomorph E (Fneg × Fpos)) : Prop :=
  c ∈ φ.source ∧ φ c = 0 ∧
    (∀ y ∈ φ.source, f y = f c + modelQ (φ y)) ∧
    (∀ y ∈ φ.source, fderiv ℝ (⇑φ) y (X y) = modelField (φ y))

/-! ### The flow of the model field

`φ_s(x₋, x₊) = (e^{2s}x₋, e^{−2s}x₊)`: hyperbolas, as in Figure 2 of the book. -/

/-- The flow of `−grad Q`. -/
noncomputable def modelFlow (s : ℝ) (x : Fneg × Fpos) : Fneg × Fpos :=
  (Real.exp (2 * s) • x.1, Real.exp (-(2 * s)) • x.2)

theorem isIntegralCurve_modelFlow (x : Fneg × Fpos) :
    IsIntegralCurve (fun s => modelFlow s x) fun _ => modelField := by
  intro s
  show HasDerivAt (fun u => modelFlow u x) (modelField (modelFlow s x)) s
  have hl : HasDerivAt (fun u : ℝ => 2 * u) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have hl2 : HasDerivAt (fun u : ℝ => -(2 * u)) (-2 : ℝ) s := hl.neg
  have e1 : HasDerivAt (fun u : ℝ => Real.exp (2 * u) • x.1)
      ((Real.exp (2 * s) * 2) • x.1) s := hl.exp.smul_const x.1
  have e2 : HasDerivAt (fun u : ℝ => Real.exp (-(2 * u)) • x.2)
      ((Real.exp (-(2 * s)) * -2) • x.2) s := hl2.exp.smul_const x.2
  have key : ((Real.exp (2 * s) * 2) • x.1, (Real.exp (-(2 * s)) * -2) • x.2)
      = modelField (modelFlow s x) := by
    show _ = ((2 : ℝ) • (Real.exp (2 * s) • x.1), (-2 : ℝ) • (Real.exp (-(2 * s)) • x.2))
    rw [smul_smul, smul_smul, mul_comm (2 : ℝ) (Real.exp (2 * s)),
      mul_comm (-2 : ℝ) (Real.exp (-(2 * s)))]
  rw [← key]
  exact e1.prodMk e2

/-- The flow of the model field, as a `Flow ℝ (V₋ × V₊)`. -/
noncomputable def modelFlowFlow : Flow ℝ (Fneg × Fpos) where
  toFun := modelFlow
  cont' := by
    show Continuous fun p : ℝ × (Fneg × Fpos) =>
      (Real.exp (2 * p.1) • p.2.1, Real.exp (-(2 * p.1)) • p.2.2)
    refine Continuous.prodMk ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).smul
        (continuous_fst.comp continuous_snd)
    · exact (Real.continuous_exp.comp
        (continuous_neg.comp (continuous_const.mul continuous_fst))).smul
        (continuous_snd.comp continuous_snd)
  map_add' t₁ t₂ x := by
    have h1 : Real.exp (2 * (t₁ + t₂)) = Real.exp (2 * t₁) * Real.exp (2 * t₂) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(2 * (t₁ + t₂))) = Real.exp (-(2 * t₁)) * Real.exp (-(2 * t₂)) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [modelFlow, h1, h2, smul_smul]
  map_zero' x := by simp [modelFlow]

/-! ## §2.1.d Stable and unstable sets -/

end MorseModel

section StableSets

variable {α : Type*} [TopologicalSpace α]

/-- **The stable manifold of `a`** (§2.1.d): the points whose forward trajectory
converges to `a`. -/
def stableSet (φ : Flow ℝ α) (a : α) : Set α :=
  {x | Tendsto (fun s => φ s x) atTop (𝓝 a)}

/-- **The unstable manifold of `a`** (§2.1.d): the points whose backward
trajectory converges to `a`. -/
def unstableSet (φ : Flow ℝ α) (a : α) : Set α :=
  {x | Tendsto (fun s => φ s x) atBot (𝓝 a)}

/-- **The space `M(a,b)` of trajectories from `a` to `b`** (§2.2.b). -/
def trajectorySet (φ : Flow ℝ α) (a b : α) : Set α := unstableSet φ a ∩ stableSet φ b

theorem mem_stableSet_iff {φ : Flow ℝ α} {a x : α} :
    x ∈ stableSet φ a ↔ Tendsto (fun s => φ s x) atTop (𝓝 a) := Iff.rfl

theorem mem_unstableSet_iff {φ : Flow ℝ α} {a x : α} :
    x ∈ unstableSet φ a ↔ Tendsto (fun s => φ s x) atBot (𝓝 a) := Iff.rfl

/-- A fixed point lies in its own stable and unstable manifolds. -/
theorem mem_stableSet_self {φ : Flow ℝ α} {a : α} (h : ∀ s, φ s a = a) :
    a ∈ stableSet φ a := by
  show Tendsto (fun s => φ s a) atTop (𝓝 a)
  simp only [h]
  exact tendsto_const_nhds

theorem mem_unstableSet_self {φ : Flow ℝ α} {a : α} (h : ∀ s, φ s a = a) :
    a ∈ unstableSet φ a := by
  show Tendsto (fun s => φ s a) atBot (𝓝 a)
  simp only [h]
  exact tendsto_const_nhds

/-- Stable manifolds are invariant under the flow. -/
theorem stableSet_invariant {φ : Flow ℝ α} {a x : α} (hx : x ∈ stableSet φ a) (t : ℝ) :
    φ t x ∈ stableSet φ a := by
  have hx' : Tendsto (fun s => φ s x) atTop (𝓝 a) := hx
  show Tendsto (fun s => φ s (φ t x)) atTop (𝓝 a)
  have hfun : (fun s => φ s (φ t x)) = fun s => φ (s + t) x := by
    funext s; rw [Flow.map_add]
  rw [hfun]
  exact hx'.comp (tendsto_atTop_add_const_right atTop t tendsto_id)

/-- Unstable manifolds are invariant under the flow. -/
theorem unstableSet_invariant {φ : Flow ℝ α} {a x : α} (hx : x ∈ unstableSet φ a) (t : ℝ) :
    φ t x ∈ unstableSet φ a := by
  have hx' : Tendsto (fun s => φ s x) atBot (𝓝 a) := hx
  show Tendsto (fun s => φ s (φ t x)) atBot (𝓝 a)
  have hfun : (fun s => φ s (φ t x)) = fun s => φ (s + t) x := by
    funext s; rw [Flow.map_add]
  rw [hfun]
  exact hx'.comp (tendsto_atBot_add_const_right atBot t tendsto_id)

/-- `M(a,b)` is invariant under the flow: it is a union of whole trajectories
(§2.2.b). -/
theorem trajectorySet_invariant {φ : Flow ℝ α} {a b x : α} (hx : x ∈ trajectorySet φ a b)
    (t : ℝ) : φ t x ∈ trajectorySet φ a b :=
  ⟨unstableSet_invariant hx.1 t, stableSet_invariant hx.2 t⟩

/-- Distinct points have disjoint stable manifolds. -/
theorem eq_of_mem_stableSet [T2Space α] {φ : Flow ℝ α} {a b x : α}
    (ha : x ∈ stableSet φ a) (hb : x ∈ stableSet φ b) : a = b := by
  have ha' : Tendsto (fun s => φ s x) atTop (𝓝 a) := ha
  have hb' : Tendsto (fun s => φ s x) atTop (𝓝 b) := hb
  exact tendsto_nhds_unique ha' hb'

theorem eq_of_mem_unstableSet [T2Space α] {φ : Flow ℝ α} {a b x : α}
    (ha : x ∈ unstableSet φ a) (hb : x ∈ unstableSet φ b) : a = b := by
  have ha' : Tendsto (fun s => φ s x) atBot (𝓝 a) := ha
  have hb' : Tendsto (fun s => φ s x) atBot (𝓝 b) := hb
  exact tendsto_nhds_unique ha' hb'

end StableSets

section ModelStable

variable {Fneg Fpos : Type*} [NormedAddCommGroup Fneg] [InnerProductSpace ℝ Fneg]
  [NormedAddCommGroup Fpos] [InnerProductSpace ℝ Fpos]

theorem tendsto_modelFlow_atTop_iff (x : Fneg × Fpos) :
    Tendsto (fun s => modelFlow s x) atTop (𝓝 0) ↔ x.1 = 0 := by
  have htwo : Tendsto (fun s : ℝ => 2 * s) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have hexp : Tendsto (fun s : ℝ => Real.exp (-(2 * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp htwo
  constructor
  · intro h
    have hfst : Tendsto (fun s : ℝ => (modelFlow s x).1) atTop (𝓝 (0 : Fneg)) :=
      (continuous_fst.tendsto (0 : Fneg × Fpos)).comp h
    have hprod : Tendsto (fun s : ℝ => Real.exp (-(2 * s)) • (modelFlow s x).1) atTop
        (𝓝 ((0 : ℝ) • (0 : Fneg))) := hexp.smul hfst
    have hconst : ∀ s : ℝ, Real.exp (-(2 * s)) • (modelFlow s x).1 = x.1 := by
      intro s
      show Real.exp (-(2 * s)) • (Real.exp (2 * s) • x.1) = x.1
      rw [smul_smul, ← Real.exp_add]
      simp
    rw [funext hconst] at hprod
    have huniq := tendsto_nhds_unique hprod tendsto_const_nhds
    simpa using huniq.symm
  · intro h
    have h1 : Tendsto (fun s : ℝ => (modelFlow s x).1) atTop (𝓝 (0 : Fneg)) := by
      have hz : ∀ s : ℝ, (modelFlow s x).1 = 0 := by
        intro s
        show Real.exp (2 * s) • x.1 = 0
        rw [h, smul_zero]
      simp only [hz]
      exact tendsto_const_nhds
    have h2 : Tendsto (fun s : ℝ => (modelFlow s x).2) atTop (𝓝 (0 : Fpos)) := by
      have hs : Tendsto (fun s : ℝ => Real.exp (-(2 * s)) • x.2) atTop (𝓝 ((0 : ℝ) • x.2)) :=
        hexp.smul_const x.2
      rw [zero_smul] at hs
      exact hs
    have h0 : (0 : Fneg × Fpos) = ((0 : Fneg), (0 : Fpos)) := rfl
    rw [h0]
    exact h1.prodMk_nhds h2

/-- **The stable manifold of the origin in a Morse chart is `V₊`** (§2.1.d):
`W^s(0) = U ∩ V₊`, here computed on the whole model.  Symmetrically
`W^u(0) = U ∩ V₋`.

This is the model half of Proposition 2.1.5; the statement that `W^s(a)` is a
submanifold of `V` diffeomorphic to a disk of dimension `n − Ind(a)` cannot be
expressed with the present Mathlib (see the module docstring). -/
theorem stableSet_modelFlow :
    stableSet (modelFlowFlow (Fneg := Fneg) (Fpos := Fpos)) 0 = {x : Fneg × Fpos | x.1 = 0} := by
  ext x
  show Tendsto (fun s => modelFlow s x) atTop (𝓝 0) ↔ x.1 = 0
  exact tendsto_modelFlow_atTop_iff x

end ModelStable

/-! ## §2.1.e Sublevel sets when no critical value is crossed -/

section Sublevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The real-analysis core of Theorem 2.1.7.**  If `g` is nonincreasing and
has derivative exactly `−1` wherever its value lies in `[a, b]`, then in time
`b − a` it drops from `≤ b` to `≤ a`.

In the book, `g(s) = f(ψ_s(x))` for the flow of the renormalized field
`Y = ρX`, for which `df(Y) = −1` on `f⁻¹([a,b])`. -/
theorem descend_of_deriv_eq_neg_one {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ s, DifferentiableAt ℝ g s) (hnonpos : ∀ s, deriv g s ≤ 0)
    (hband : ∀ s, a ≤ g s → g s ≤ b → deriv g s = -1) (h0 : g 0 ≤ b) :
    g (b - a) ≤ a := by
  by_contra hcon
  rw [not_le] at hcon
  have hanti : Antitone g := antitone_of_deriv_nonpos (fun s => hd s) hnonpos
  have hmem : ∀ s ∈ Icc (0 : ℝ) (b - a), a ≤ g s ∧ g s ≤ b := by
    intro s hs
    exact ⟨le_trans hcon.le (hanti hs.2), le_trans (hanti hs.1) h0⟩
  have hd' : ∀ s, HasDerivAt (fun u => g u + u) (deriv g s + 1) s :=
    fun s => (hd s).hasDerivAt.add (hasDerivAt_id s)
  have hzero : ∀ s ∈ interior (Icc (0 : ℝ) (b - a)), deriv (fun u => g u + u) s = 0 := by
    intro s hs
    rw [interior_Icc] at hs
    have hs' : s ∈ Icc (0 : ℝ) (b - a) := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    rw [(hd' s).deriv, hband s (hmem s hs').1 (hmem s hs').2]
    ring
  have hcont : ContinuousOn (fun u => g u + u) (Icc (0 : ℝ) (b - a)) :=
    fun s _ => ((hd' s).differentiableAt.continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun u => g u + u) (interior (Icc (0 : ℝ) (b - a))) :=
    fun s _ => (hd' s).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (fun u => g u + u) (Icc (0 : ℝ) (b - a)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont hdiff fun s hs => le_of_eq (hzero s hs).symm
  have hanti2 : AntitoneOn (fun u => g u + u) (Icc (0 : ℝ) (b - a)) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont hdiff fun s hs => le_of_eq (hzero s hs)
  have hb0 : (0 : ℝ) ∈ Icc (0 : ℝ) (b - a) := ⟨le_rfl, by linarith⟩
  have hb1 : b - a ∈ Icc (0 : ℝ) (b - a) := ⟨by linarith, le_rfl⟩
  have hle1 : g 0 + 0 ≤ g (b - a) + (b - a) := hmono hb0 hb1 (by linarith)
  have hle2 : g (b - a) + (b - a) ≤ g 0 + 0 := hanti2 hb0 hb1 (by linarith)
  linarith

omit [NormedSpace ℝ E] in
/-- **Theorem 2.1.7 (the analytic half).**  If `f` decreases at unit speed along
the flow `ψ` wherever `f` lies in `[a, b]`, then the time-`(b − a)` map of `ψ`
carries the sublevel set `V^b` into `V^a`.

The book's statement — `V^b` is *diffeomorphic* to `V^a`, `ψ^{b-a}` being the
diffeomorphism — cannot be written down here: sublevel sets are manifolds with
boundary and Mathlib has no `Diffeomorph` between subsets of a manifold.  The
hypothesis packages the choice of the renormalized field `Y = ρX`, for which
`(d/ds) f(ψ_s x) = df(Y) = −1` on `f⁻¹([a,b])`. -/
theorem flow_mapsTo_sublevel (ψ : Flow ℝ E) {f : E → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x s, DifferentiableAt ℝ (fun u => f (ψ u x)) s)
    (hnonpos : ∀ x s, deriv (fun u => f (ψ u x)) s ≤ 0)
    (hband : ∀ x s, a ≤ f (ψ s x) → f (ψ s x) ≤ b → deriv (fun u => f (ψ u x)) s = -1) :
    MapsTo (ψ (b - a)) {x | f x ≤ b} {x | f x ≤ a} := by
  intro x hx
  have h0 : f (ψ (0 : ℝ) x) ≤ b := by rw [Flow.map_zero_apply]; exact hx
  exact descend_of_deriv_eq_neg_one hab (hd x) (hnonpos x) (hband x) h0

end Sublevel

/-! ### Reeb's theorem -/

/-- **Corollary 2.1.9 (Reeb's theorem).**  A compact manifold carrying a Morse
function with exactly two critical points is homeomorphic to a sphere.

`sorry`: the proof glues two disks obtained from the Morse lemma along their
boundary, using Theorem 2.1.7 to identify the intermediate sublevel sets.  It
needs the Morse lemma, the diffeomorphism statement of Theorem 2.1.7, and the
gluing construction — none available. -/
theorem reeb {n : ℕ} {V : Type*} [TopologicalSpace V] [CompactSpace V]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) V] [IsManifold (𝓡 n) ω V]
    (f : V → ℝ) (_hf : IsMorseFunction (𝓡 n) f)
    (_hcard : {x : V | IsCriticalPoint (𝓡 n) f x}.ncard = 2) :
    Nonempty (V ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  sorry

/-! ## §2.2 The Smale condition

The condition itself — `W^u(a) ⋔ W^s(b)` for all critical points `a, b` — cannot
be stated: Mathlib has no transversality of submanifolds.  What follows is the
part of §2.2.b that is order-theoretic rather than transversal, together with
the model computation of Lemma 2.2.9. -/

section SmaleTrajectories

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {X : E → E} {φ : Flow ℝ E}

/-- A flow generated by a pseudo-gradient: each orbit is an integral curve of
`X`, and the critical points are the stationary points.

The second clause is a consequence of uniqueness for the Cauchy problem (`X` is
`C¹` and vanishes at the critical points, by condition (2) of §2.1.a); it is
assumed here because Mathlib's uniqueness theorems are stated for locally
Lipschitz fields and this file makes no smoothness assumption on `X`. -/
structure IsPseudoGradientFlow (f : E → ℝ) (X : E → E) (φ : Flow ℝ E) : Prop where
  /-- Every orbit is an integral curve of `X`. -/
  isIntegralCurve : ∀ x, IsIntegralCurve (fun s => φ s x) fun _ => X
  /-- Critical points are stationary. -/
  fixed_of_isCriticalPt : ∀ x, IsCriticalPt f x → ∀ s, φ s x = x

/-- The chain rule along an orbit. -/
theorem IsPseudoGradientFlow.hasDerivAt_comp (hφ : IsPseudoGradientFlow f X φ)
    (hf : Differentiable ℝ f) (x : E) (s : ℝ) :
    HasDerivAt (fun u => f (φ u x)) (fderiv ℝ f (φ s x) (X (φ s x))) s :=
  hasDerivAt_comp_integralCurve hf (hφ.isIntegralCurve x) s

/-- A noncritical point has a wholly noncritical orbit. -/
theorem IsPseudoGradientFlow.not_isCriticalPt_flow (hφ : IsPseudoGradientFlow f X φ)
    {x : E} (hx : ¬ IsCriticalPt f x) (t : ℝ) : ¬ IsCriticalPt f (φ t x) := by
  intro hc
  refine hx ?_
  have h1 : φ (-t) (φ t x) = φ t x := hφ.fixed_of_isCriticalPt _ hc (-t)
  have h2 : φ (-t) (φ t x) = x := by
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have hxx : x = φ t x := h2.symm.trans h1
  rw [hxx]
  exact hc

/-- **`f` strictly decreases along every noncritical orbit.** -/
theorem IsPseudoGradientFlow.strictAnti (hφ : IsPseudoGradientFlow f X φ)
    (hf : Differentiable ℝ f) (hX : IsPseudoGradient f X) {x : E} (hx : ¬ IsCriticalPt f x) :
    StrictAnti fun s => f (φ s x) :=
  strictAnti_of_hasDerivAt_neg (fun s => hφ.hasDerivAt_comp hf x s)
    fun s => hX.neg_of_not_isCriticalPt (hφ.not_isCriticalPt_flow hx s)

/-- A point on a trajectory joining two *distinct* critical points is not itself
critical. -/
theorem IsPseudoGradientFlow.not_isCriticalPt_of_mem (hφ : IsPseudoGradientFlow f X φ)
    {a b x : E} (hab : a ≠ b) (hx : x ∈ trajectorySet φ a b) : ¬ IsCriticalPt f x := by
  intro hc
  have hfix : ∀ s : ℝ, φ s x = x := hφ.fixed_of_isCriticalPt x hc
  have h1 : Tendsto (fun s : ℝ => φ s x) atBot (𝓝 a) := hx.1
  have h2 : Tendsto (fun s : ℝ => φ s x) atTop (𝓝 b) := hx.2
  simp only [hfix] at h1 h2
  exact hab (((tendsto_nhds_unique tendsto_const_nhds h1).symm).trans
    (tendsto_nhds_unique tendsto_const_nhds h2))

/-- **The index/value bookkeeping of §2.2.b.**  If a trajectory joins `a` to `b`
with `a ≠ b`, then `f(b) < f(a)`: the function strictly decreases from the
starting critical point to the ending one. -/
theorem lt_of_mem_trajectorySet (hφ : IsPseudoGradientFlow f X φ)
    (hf : Differentiable ℝ f) (hX : IsPseudoGradient f X) {a b x : E} (hab : a ≠ b)
    (hx : x ∈ trajectorySet φ a b) : f b < f a := by
  have hnc : ¬ IsCriticalPt f x := hφ.not_isCriticalPt_of_mem hab hx
  have hsa : StrictAnti fun s => f (φ s x) := hφ.strictAnti hf hX hnc
  have hu : Tendsto (fun s : ℝ => φ s x) atBot (𝓝 a) := hx.1
  have hs : Tendsto (fun s : ℝ => φ s x) atTop (𝓝 b) := hx.2
  have hbot : Tendsto (fun s : ℝ => f (φ s x)) atBot (𝓝 (f a)) :=
    (hf.continuous.tendsto a).comp hu
  have htop : Tendsto (fun s : ℝ => f (φ s x)) atTop (𝓝 (f b)) :=
    (hf.continuous.tendsto b).comp hs
  have hge : f (φ (0 : ℝ) x) ≤ f a :=
    ge_of_tendsto hbot ((eventually_lt_atBot (0 : ℝ)).mono fun s hs => (hsa hs).le)
  have hle : f b ≤ f (φ (1 : ℝ) x) :=
    le_of_tendsto htop ((eventually_gt_atTop (1 : ℝ)).mono fun s hs => (hsa hs).le)
  have hlt : f (φ (1 : ℝ) x) < f (φ (0 : ℝ) x) := hsa zero_lt_one
  linarith

/-- **Remark 2.2.1.**  If `a ≠ b` and `f(a) ≤ f(b)`, then `W^u(a)` and `W^s(b)`
do not meet: no trajectory can join `a` to `b`.  (In particular such stable and
unstable manifolds are trivially transverse.) -/
theorem trajectorySet_eq_empty (hφ : IsPseudoGradientFlow f X φ)
    (hf : Differentiable ℝ f) (hX : IsPseudoGradient f X) {a b : E} (hab : a ≠ b)
    (hle : f a ≤ f b) : trajectorySet φ a b = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have := lt_of_mem_trajectorySet hφ hf hX hab hx
  linarith

/-- **Proposition 2.2.2.**  Time translation `s · x = φ_s(x)` is an action of `ℝ`
on `M(a,b)`, and it is *free* when `a ≠ b`: no point of `M(a,b)` is critical, so
`f` is strictly decreasing along its orbit and the orbit map is injective. -/
theorem injective_flow_of_mem_trajectorySet (hφ : IsPseudoGradientFlow f X φ)
    (hf : Differentiable ℝ f) (hX : IsPseudoGradient f X) {a b x : E} (hab : a ≠ b)
    (hx : x ∈ trajectorySet φ a b) : Function.Injective fun s : ℝ => φ s x := by
  have hsa : StrictAnti fun s => f (φ s x) :=
    hφ.strictAnti hf hX (hφ.not_isCriticalPt_of_mem hab hx)
  intro s s' hss
  exact hsa.injective (congrArg f hss)

/-- **Remark 2.2.3.**  A trajectory joining `a` to `b` meets an intermediate
level `f⁻¹(α)`, `f(b) < α < f(a)`, in exactly one point.  This is what
identifies the quotient `L(a,b) = M(a,b)/ℝ` with `M(a,b) ∩ f⁻¹(α)`. -/
theorem existsUnique_level (hφ : IsPseudoGradientFlow f X φ)
    (hf : Differentiable ℝ f) (hX : IsPseudoGradient f X) {a b x : E} (hab : a ≠ b)
    (hx : x ∈ trajectorySet φ a b) {α : ℝ} (hα₁ : f b < α) (hα₂ : α < f a) :
    ∃! s : ℝ, f (φ s x) = α := by
  have hsa : StrictAnti fun s => f (φ s x) :=
    hφ.strictAnti hf hX (hφ.not_isCriticalPt_of_mem hab hx)
  have hu : Tendsto (fun s : ℝ => φ s x) atBot (𝓝 a) := hx.1
  have hv : Tendsto (fun s : ℝ => φ s x) atTop (𝓝 b) := hx.2
  have hbot : Tendsto (fun s : ℝ => f (φ s x)) atBot (𝓝 (f a)) :=
    (hf.continuous.tendsto a).comp hu
  have htop : Tendsto (fun s : ℝ => f (φ s x)) atTop (𝓝 (f b)) :=
    (hf.continuous.tendsto b).comp hv
  obtain ⟨s₁, hs₁⟩ := (hbot.eventually_const_lt hα₂).exists
  obtain ⟨s₂, hs₂⟩ := (htop.eventually (eventually_lt_nhds hα₁)).exists
  have hlt : s₁ < s₂ := hsa.lt_iff_gt.mp (lt_trans hs₂ hs₁)
  have hcont : ContinuousOn (fun s : ℝ => f (φ s x)) (Icc s₁ s₂) := fun s _ =>
    ((hφ.hasDerivAt_comp hf x s).differentiableAt.continuousAt).continuousWithinAt
  have hsub := intermediate_value_Icc' (le_of_lt hlt) hcont
  have hmem : α ∈ Icc (f (φ s₂ x)) (f (φ s₁ x)) := ⟨le_of_lt hs₂, le_of_lt hs₁⟩
  obtain ⟨s, _, hs⟩ := hsub hmem
  have hs' : f (φ s x) = α := hs
  refine ⟨s, hs', fun y hy => hsa.injective ?_⟩
  show f (φ y x) = f (φ s x)
  rw [hy, hs']

end SmaleTrajectories

/-! ### Lemma 2.2.9 in the model

The perturbation used to make the stable manifold transverse: on
`Dᵏ × Q × [0,m]` one replaces `−∂/∂z` by `−∂/∂z − Σ βᵢ(z) ∂/∂xᵢ`, and the new
trajectory through the origin lands at `w = ∫₀^m β` at time `−m`.  The passive
factor `Q` and the cut-off `γ(x)` (which equals `1` where the trajectory runs)
are dropped; what is left is exactly the differential system solved in the book,
here on `G × ℝ`. -/

section SmaleModel

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The perturbed model field `X'' = −∂/∂z − β(z) ∂/∂x` of Lemma 2.2.9. -/
def smaleField (β : ℝ → G) (p : G × ℝ) : G × ℝ := (-β p.2, -1)

/-- The trajectory of `X''` through the origin. -/
noncomputable def smaleCurve (β : ℝ → G) (s : ℝ) : G × ℝ := (∫ t in (0 : ℝ)..(-s), β t, -s)

omit [CompleteSpace G] in
theorem smaleCurve_zero (β : ℝ → G) : smaleCurve β 0 = (0, 0) := by
  show ((∫ t in (0 : ℝ)..(-(0 : ℝ)), β t), -(0 : ℝ)) = (0, 0)
  simp [intervalIntegral.integral_same]

/-- The curve of Lemma 2.2.9 is an integral curve of the perturbed field. -/
theorem isIntegralCurve_smaleCurve {β : ℝ → G} (hβ : Continuous β) :
    IsIntegralCurve (smaleCurve β) fun _ => smaleField β := by
  intro s
  show HasDerivAt (smaleCurve β) (smaleField β (smaleCurve β s)) s
  have h1 : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, β t) (β (-s)) (-s) :=
    (hβ.integral_hasStrictDerivAt 0 (-s)).hasDerivAt
  have h2 : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) s := (hasDerivAt_id s).neg
  have h3 : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..(-u), β t) ((-1 : ℝ) • β (-s)) s :=
    h1.scomp s h2
  have key : ((-1 : ℝ) • β (-s), (-1 : ℝ)) = smaleField β (smaleCurve β s) := by
    show _ = (-β (-s), (-1 : ℝ))
    rw [neg_one_smul]
  rw [← key]
  exact h3.prodMk h2

omit [CompleteSpace G] in
/-- **Lemma 2.2.9 (model computation).**  At time `−m` the trajectory of the
perturbed field starting at the origin has been moved by `w = ∫₀^m β`, which is
the vector prescribed by Sard's theorem in the proof of Lemma 2.2.8. -/
theorem smaleCurve_neg (β : ℝ → G) (m : ℝ) :
    smaleCurve β (-m) = (∫ t in (0 : ℝ)..m, β t, m) := by
  show ((∫ t in (0 : ℝ)..(-(-m)), β t), -(-m)) = _
  rw [neg_neg]

end SmaleModel

/-! ## §2.3 Appendix: compact 1-manifolds, and Brouwer -/

/-- **Theorem 2.3.2 (classification of compact 1-manifolds).**  A compact
connected manifold of dimension 1 without boundary is diffeomorphic to the
circle.  (The book also treats the case with boundary, where `V ≅ [0,1]`;
manifolds with boundary exist in Mathlib but the inward-field construction of
§2.3.a does not, so only the closed case is stated.)

`sorry`: the proof takes a Morse function adapted to an inward field, notes that
the closure of the stable manifold of each minimum is a circle or a closed
interval, and glues these along their maxima.  It needs Proposition 2.1.6 and
the stable-manifold statement 2.1.5. -/
theorem classification_dim_one {V : Type*} [TopologicalSpace V] [CompactSpace V]
    [ConnectedSpace V] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) V] [IsManifold (𝓡 1) ω V] :
    Nonempty (V ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  sorry

/-- The norm on the line `EuclideanSpace ℝ (Fin 1)` is the absolute value of the
single coordinate: this is what identifies the one-dimensional closed unit ball
with `[−1, 1]`, and it is all `brouwer_dim_one` needs beyond the intermediate
value theorem. -/
theorem norm_eq_abs_coord (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
    Real.sqrt_sq_eq_abs]

/-- **Theorem 2.3.3, base case `n = 0`.**  Proved in full.  `EuclideanSpace ℝ
(Fin 0)` has exactly one point, so the closed unit ball is `{0}` and the origin
is a fixed point of every self-map.  With `brouwer_dim_one` this discharges
`brouwer` for `n ≤ 1`; the obstruction for `n ≥ 2` is recorded on `brouwer`. -/
theorem brouwer_dim_zero (ϕ : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0))
    (_hcont : ContinuousOn ϕ (Metric.closedBall 0 1))
    (_hmaps : MapsTo ϕ (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1, ϕ x = x := by
  refine ⟨0, Metric.mem_closedBall_self zero_le_one, ?_⟩
  ext i
  exact i.elim0

/-- **Theorem 2.3.3, base case `n = 1`.**  Proved in full.

By `norm_eq_abs_coord` the closed unit ball of `EuclideanSpace ℝ (Fin 1)` is the
image of `[−1, 1]` under the isometric parametrisation `t ↦ (t)`.  The function
`g t = ϕ(t) − t` is continuous on `[−1, 1]`, and `g(1) ≤ 0 ≤ g(−1)` because `ϕ`
maps the ball into itself, so `intermediate_value_Icc'` gives a zero of `g`,
which is a fixed point of `ϕ`.

This is a genuine instance of Theorem 2.3.3, not a placeholder: it is the base
case any inductive or homological proof would also have to supply. -/
theorem brouwer_dim_one (ϕ : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
    (hcont : ContinuousOn ϕ (Metric.closedBall 0 1))
    (hmaps : MapsTo ϕ (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, ϕ x = x := by
  obtain ⟨j, hj0, hjc, hjn⟩ :
      ∃ j : ℝ → EuclideanSpace ℝ (Fin 1),
        (∀ t, j t 0 = t) ∧ Continuous j ∧ ∀ t, ‖j t‖ = |t| := by
    refine ⟨fun t => WithLp.toLp 2 fun _ => t, fun _ => rfl, ?_, ?_⟩
    · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)
    · intro t
      rw [norm_eq_abs_coord]
  have hjmem : ∀ t : ℝ, t ∈ Icc (-1 : ℝ) 1 →
      j t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    intro t ht
    rw [mem_closedBall_zero_iff, hjn]
    exact abs_le.mpr ⟨ht.1, ht.2⟩
  have hgc : ContinuousOn (fun t : ℝ => ϕ (j t) 0 - t) (Icc (-1 : ℝ) 1) :=
    ((PiLp.continuous_apply 2 _ 0).comp_continuousOn
      (hcont.comp hjc.continuousOn hjmem)).sub continuousOn_id
  have hbound : ∀ t : ℝ, t ∈ Icc (-1 : ℝ) 1 → |ϕ (j t) 0| ≤ 1 := by
    intro t ht
    have h := hmaps (hjmem t ht)
    rw [mem_closedBall_zero_iff, norm_eq_abs_coord] at h
    exact h
  have h1 : ϕ (j 1) 0 - 1 ≤ 0 := by
    have h := (abs_le.mp (hbound 1 ⟨by norm_num, le_refl 1⟩)).2
    linarith
  have h2 : (0 : ℝ) ≤ ϕ (j (-1)) 0 - (-1) := by
    have h := (abs_le.mp (hbound (-1) ⟨le_refl (-1 : ℝ), by norm_num⟩)).1
    linarith
  obtain ⟨t, ht, hgt⟩ :=
    intermediate_value_Icc' (by norm_num : (-1 : ℝ) ≤ 1) hgc ⟨h1, h2⟩
  refine ⟨j t, hjmem t ht, ?_⟩
  have hcoord : ϕ (j t) 0 = t := by
    have h : ϕ (j t) 0 - t = 0 := hgt
    linarith
  ext i
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  rw [hj0]
  exact hcoord

/-- **Theorem 2.3.3 (Brouwer's fixed point theorem).**  A continuous self-map of
the closed unit ball has a fixed point.

`sorry` for arbitrary `n`.  The book's own proof deduces it from Sard's theorem
and the classification of 1-manifolds — a fixed-point-free map would give a
smooth retraction of the ball onto its boundary, whose regular fibre would be a
compact 1-manifold with exactly one boundary point — and Mathlib has neither
Sard's theorem nor `classification_dim_one` above.  But it is worth recording
that *no* classical route is available either, since this was checked
declaration by declaration:

* **no homology of spheres.**  `Mathlib.AlgebraicTopology.SingularHomology`
  builds singular homology as a functor and proves homotopy invariance and the
  computation of `H₀`, but there is no excision and no Mayer–Vietoris, so
  `H_{n−1}(Sⁿ⁻¹)` is computed nowhere and the no-retraction argument cannot be
  run;
* **no `π₁(S¹) ≅ ℤ`**, so even `n = 2` cannot go through covering spaces;
* **no Sperner lemma** on simplicial subdivisions (`Combinatorics/SetFamily/
  LYM.lean` is Sperner's unrelated *theorem* on antichains) and **no degree
  theory**, closing the combinatorial and the analytic proofs.

Brouwer's theorem is itself absent from this Mathlib (a search for `brouwer`
finds only Brouwerian lattices), so it cannot simply be imported; closing this
`sorry` means contributing one of the ingredients above upstream, of which
excision plus Mayer–Vietoris for the existing singular homology is the cheapest.

The low-dimensional case is *not* assumed: `brouwer_dim_zero` and
`brouwer_dim_one` above prove it in full.  (`Chapter4.brouwer_fixedPoint`
restates the theorem for §4.8.b and carries the same two base cases,
`Chapter4.brouwer_fixedPoint_dim_zero` and
`Chapter4.brouwer_fixedPoint_dim_one`; the proofs are repeated there because
`Part1/Ch3.lean`, and hence `Part1/Ch4.lean`, does not import this file.) -/
theorem brouwer {n : ℕ} (ϕ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (_hcont : ContinuousOn ϕ (Metric.closedBall 0 1))
    (_hmaps : MapsTo ϕ (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ϕ x = x := by
  sorry

end Chapter2
end MorseFloer
