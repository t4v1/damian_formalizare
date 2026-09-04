import MorseFloer.Basic

/-!
# Chapter 1: Morse functions

Formalization of Chapter 1 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part I, printed pages 7–20).

The chapter has four sections:

* **§1.1** defines critical points, the Hessian at a critical point, and Morse
  functions.  The definitions themselves live in `MorseFloer.Basic`; here we
  record the two facts that make them legitimate — the Hessian is symmetric, and
  at a critical point it is chart-independent.
* **§1.2** proves that Morse functions exist and are generic
  (Propositions 1.2.1 and 1.2.4, Lemma 1.2.2, Theorem 1.2.5).  These rest on
  Sard's theorem for manifolds, which Mathlib does not have.
* **§1.3** is the Morse lemma (Theorem 1.3.1) and its corollary that
  nondegenerate critical points are isolated (Corollary 1.3.2), together with
  the definition of the index and Remark 1.3.3.
* **§1.4** gives the standard examples: the squared distance to a point, height
  functions, and `cos 2πx + cos 2πy` on the torus.

## Status

Proved here: Hessian symmetry, chart-independence at a critical point,
isolation of nondegenerate critical points (via the inverse function theorem,
i.e. *without* the Morse lemma, as Exercise 2 asks), the index/coindex duality
of Remark 1.3.3, the differential of the squared distance function, and the full
critical-point analysis of the factor `cos 2πt` behind the torus example.

Assumed (`sorry`): the Morse lemma (Theorem 1.3.1) and Proposition 1.2.1, which
needs Sard's theorem.  Lemma 1.2.2, Proposition 1.2.4 and Theorem 1.2.5 need the
normal bundle as a submanifold and the `Cᵏ` topology on `C^∞(V; ℝ)`; neither is
expressible with today's Mathlib, so they appear in the blueprint with no Lean
statement rather than as a fictitious one.
-/

open scoped Manifold ContDiff Real
open ContinuousLinearMap Filter Topology

namespace MorseFloer
namespace Chapter1

/-! ## §1.1 Definition of Morse functions -/

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The Hessian is a symmetric bilinear form** (§1.1.a).

The book obtains this from `X·(Y·f) − Y·(X·f) = [X,Y]·f = df([X,Y]) = 0` at a
critical point; in a chart it is the symmetry of the second derivative of a `C²`
function. -/
theorem hessian_symm {f : M → ℝ} {x : M}
    (hf : ContDiffAt ℝ 2 (writtenInExtChartAt I 𝓘(ℝ) x f) (extChartAt I x x)) (v w : E) :
    hessian I f x v w = hessian I f x w v :=
  sndFDeriv_symm hf v w

/-- **Chart-independence of the Hessian at a critical point** (Remark 1.1.2 and
Exercise 1, p. 17).

Read through any change of coordinates `φ`, the second differential of a
function whose differential vanishes transforms as an honest bilinear form — no
correction term.  This is the precise sense in which `hessian` does not depend
on the chart used to compute it. -/
theorem hessian_chart_independent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hcrit : fderiv ℝ f (φ x) = 0) (v w : E) :
    sndFDeriv (f ∘ φ) x v w = sndFDeriv f (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w) :=
  sndFDeriv_comp_of_critical hf hφ hcrit v w

end Definitions

/-! ### The local picture

Everything beyond the definitions is local, so we work on a normed space and
call `x` a critical point of `f : E → ℝ` when `fderiv ℝ f x = 0`. -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A critical point in the local model. -/
def IsCriticalPt (f : E → ℝ) (x : E) : Prop := fderiv ℝ f x = 0

/-- A nondegenerate critical point in the local model. -/
structure IsNondegenerateCriticalPt (f : E → ℝ) (x : E) : Prop where
  isCritical : IsCriticalPt f x
  nondegenerate : IsNondegenerate (sndFDeriv f x)

/-- The index of a critical point in the local model (§1.3.a). -/
noncomputable def localIndex (f : E → ℝ) (x : E) : ℕ := index (sndFDeriv f x)

end Local

/-! ## §1.2 Existence and multitude of Morse functions -/

section Genericity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The **squared distance to a point** `p`: the function `f_p` of §1.2.a. -/
def distSq (p : F) (x : F) : ℝ := ‖x - p‖ ^ 2

/-- The differential of `f_p` is `ξ ↦ 2⟪x − p, ξ⟫` (§1.2.a).

Hence, on a submanifold `V`, the point `x` is critical for `f_p` exactly when
`x − p` is orthogonal to `T_x V` — the characterisation the book feeds to Sard's
theorem via the normal bundle. -/
theorem hasFDerivAt_distSq (p x : F) :
    HasFDerivAt (distSq p) (2 • innerSL ℝ (x - p)) x := by
  have h : HasFDerivAt (fun y : F => y - p) (ContinuousLinearMap.id ℝ F) x :=
    (hasFDerivAt_id x).sub_const p
  have h2 := (hasStrictFDerivAt_norm_sq (x - p)).hasFDerivAt.comp x h
  rw [ContinuousLinearMap.comp_id] at h2
  exact h2

theorem fderiv_distSq (p x : F) : fderiv ℝ (distSq p) x = 2 • innerSL ℝ (x - p) :=
  (hasFDerivAt_distSq p x).fderiv

/-- In the ambient space the only critical point of `f_p` is `p` itself; on a
submanifold the condition becomes orthogonality to the tangent space. -/
theorem isCriticalPt_distSq_iff (p x : F) : IsCriticalPt (distSq p) x ↔ x = p := by
  constructor
  · intro h
    have h' : fderiv ℝ (distSq p) x = 0 := h
    have h2 : fderiv ℝ (distSq p) x (x - p) = 0 := by rw [h']; simp
    rw [fderiv_distSq] at h2
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul] at h2
    have h3 : (inner ℝ (x - p) (x - p) : ℝ) = 0 := by simpa using h2
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)
  · rintro rfl
    simp [IsCriticalPt, fderiv_distSq]

/-- **Proposition 1.2.1.**  For almost every `p` in `ℝⁿ`, the squared distance
`x ↦ ‖ι x − p‖²` on a submanifold `V ⊆ ℝⁿ` is a Morse function.

The book's proof applies Sard's theorem to the endpoint map `E(x,v) = x + v` of
the normal bundle of `V` (Lemma 1.2.2).  Sard's theorem for manifolds is not in
Mathlib. -/
theorem ae_isMorseFunction_distSq {d n : ℕ}
    {V : Type*} [TopologicalSpace V] [ChartedSpace (EuclideanSpace ℝ (Fin d)) V]
    [IsManifold (𝓡 d) ω V] (ι : V → EuclideanSpace ℝ (Fin n))
    (_hι : Manifold.IsSmoothEmbedding (𝓡 d) (𝓡 n) ω ι) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin n),
      IsMorseFunction (𝓡 d) (fun x : V => ‖ι x - p‖ ^ 2) := by
  sorry

end Genericity

/-! ## §1.3 The Morse lemma, index of a critical point -/

section MorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 1.3.1 (the Morse lemma).**  Near a nondegenerate critical point `c`
there are coordinates in which `f` *equals* its quadratic model:
there is a chart `φ` centred at `c` with

`f y = f c + ½ · d²f_c (φ y, φ y)`  for `y` near `c`.

Diagonalising the quadratic form (Sylvester's law of inertia, in Mathlib as
`QuadraticForm.equivalent_signType_weighted_sum_squared`) turns this into the
book's normal form `f(c) − Σ_{j≤i} x_j² + Σ_{j>i} x_j²`, whose integer `i` is the
index of the critical point.

The book proves this by induction on the dimension using the implicit function
theorem. -/
theorem morse_lemma [FiniteDimensional ℝ E] [CompleteSpace E] {f : E → ℝ} {c : E}
    (_hf : ContDiffAt ℝ ω f c) (_hcrit : IsCriticalPt f c)
    (_hnd : IsNondegenerate (sndFDeriv f c)) :
    ∃ φ : OpenPartialHomeomorph E E, c ∈ φ.source ∧ φ c = 0 ∧
      ∀ y ∈ φ.source, f y = f c + (1 / 2 : ℝ) * sndFDeriv f c (φ y) (φ y) := by
  sorry

/-- **Corollary 1.3.2: nondegenerate critical points are isolated.**

Proved here as Exercise 2 (p. 17) asks — *without* the Morse lemma.  The
differential `df : E → E*` is `C¹` near `c` with strict derivative the Hessian;
when the Hessian is invertible the inverse function theorem makes `df` a local
homeomorphism, so `c` is the only zero of `df` nearby.

Nondegeneracy is expressed by supplying the Hessian as a continuous linear
equivalence `B`, which in finite dimensions is equivalent to
`IsNondegenerate (sndFDeriv f c)`. -/
theorem isolated_of_nondegenerate [CompleteSpace E] {f : E → ℝ} {c : E}
    (hf : ContDiffAt ℝ 2 f c) (hcrit : IsCriticalPt f c)
    (B : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hB : (B : E →L[ℝ] (E →L[ℝ] ℝ)) = sndFDeriv f c) :
    ∀ᶠ y in 𝓝 c, IsCriticalPt f y → y = c := by
  -- `df` has an invertible strict derivative at `c`.
  have hstrict : HasStrictFDerivAt (fderiv ℝ f) (B : E →L[ℝ] (E →L[ℝ] ℝ)) c := by
    rw [hB]
    exact (hf.fderiv_right (m := 1) (by norm_num)).hasStrictFDerivAt (by norm_num)
  -- So `df` is injective on a neighbourhood of `c`.
  have hmem : c ∈ (hstrict.toOpenPartialHomeomorph (fderiv ℝ f)).source :=
    hstrict.mem_toOpenPartialHomeomorph_source
  have hnhds : (hstrict.toOpenPartialHomeomorph (fderiv ℝ f)).source ∈ 𝓝 c :=
    (hstrict.toOpenPartialHomeomorph (fderiv ℝ f)).open_source.mem_nhds hmem
  have hco : ((hstrict.toOpenPartialHomeomorph (fderiv ℝ f)) : E → (E →L[ℝ] ℝ))
      = fderiv ℝ f := hstrict.toOpenPartialHomeomorph_coe
  filter_upwards [hnhds] with y hy hy'
  refine (hstrict.toOpenPartialHomeomorph (fderiv ℝ f)).injOn hy hmem ?_
  have e1 : fderiv ℝ f y = 0 := hy'
  have e2 : fderiv ℝ f c = 0 := hcrit
  rw [hco, e1, e2]

/-- **Remark 1.3.3.**  A critical point of index `i` for `f` has index `n − i`
for `−f`.  Stated as `index (−B) + index B = n` for a bilinear form `B` with
trivial radical, which is exactly nondegeneracy. -/
theorem index_neg_add_index [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hrad : Module.finrank ℝ (toQuadraticForm B).radical = 0) :
    index (-B) + index B = Module.finrank ℝ E := by
  have hneg : toQuadraticForm (-B) = -toQuadraticForm B := by
    ext v
    simp [toQuadraticForm, toBilinForm]
  have h1 : index (-B) = sigPos (toQuadraticForm B) := by
    unfold index sigNeg
    rw [hneg, neg_neg]
  rw [h1, index]
  have h2 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := toQuadraticForm B)
  omega

end MorseLemma

/-! ## §1.4 Examples of Morse functions -/

section Examples

/-! ### §1.4.c The function `cos 2πx + cos 2πy` on the torus

We analyse the one-variable factor `t ↦ cos 2πt` completely: its critical points
are exactly the half-integers, and at each of them the second derivative is
`∓4π² ≠ 0`.  By Exercise 4 (a sum of Morse functions on a product is Morse, with
index the sum of the indices) this gives the four critical points of the torus
function — a minimum at `(½,½)`, two saddles at `(½,0)` and `(0,½)`, and a
maximum at `(0,0)` — with indices `0, 1, 1, 2`. -/

/-- The one-variable factor of the torus example. -/
noncomputable def cosFactor (t : ℝ) : ℝ := Real.cos (2 * π * t)

private theorem hasDerivAt_linear (t : ℝ) :
    HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t := by
  simpa using (hasDerivAt_id t).const_mul (2 * π)

theorem hasDerivAt_cosFactor (t : ℝ) :
    HasDerivAt cosFactor (-Real.sin (2 * π * t) * (2 * π)) t :=
  (Real.hasDerivAt_cos (2 * π * t)).comp t (hasDerivAt_linear t)

theorem deriv_cosFactor : deriv cosFactor = fun t => -Real.sin (2 * π * t) * (2 * π) :=
  funext fun t => (hasDerivAt_cosFactor t).deriv

private theorem hasDerivAt_sinComp (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (2 * π * s)) (Real.cos (2 * π * t) * (2 * π)) t :=
  (Real.hasDerivAt_sin (2 * π * t)).comp t (hasDerivAt_linear t)

theorem hasDerivAt_deriv_cosFactor (t : ℝ) :
    HasDerivAt (deriv cosFactor) (-(Real.cos (2 * π * t) * (2 * π)) * (2 * π)) t := by
  rw [deriv_cosFactor]
  exact (hasDerivAt_sinComp t).neg.mul_const (2 * π)

theorem deriv_deriv_cosFactor :
    deriv (deriv cosFactor) = fun t => -(Real.cos (2 * π * t) * (2 * π)) * (2 * π) :=
  funext fun t => (hasDerivAt_deriv_cosFactor t).deriv

/-- **The critical points of `cos 2πt` are exactly the half-integers.** -/
theorem deriv_cosFactor_eq_zero_iff (t : ℝ) :
    deriv cosFactor t = 0 ↔ ∃ k : ℤ, t = (k : ℝ) / 2 := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
  simp only [deriv_cosFactor]
  constructor
  · intro h
    have hsin : Real.sin (2 * π * t) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · simpa using h1
      · exact absurd h1 h2pi
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
    refine ⟨k, ?_⟩
    have h2 : ((k : ℝ) - 2 * t) * π = 0 := by linear_combination hk
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith [sub_eq_zero.mp h3]
    · exact absurd h3 hpi
  · rintro ⟨k, rfl⟩
    have hs : Real.sin (2 * π * ((k : ℝ) / 2)) = 0 :=
      Real.sin_eq_zero_iff.mpr ⟨k, by ring⟩
    rw [hs]
    ring

/-- **Every critical point of `cos 2πt` is nondegenerate.**  At a critical point
`sin 2πt = 0`, hence `cos 2πt = ±1`, so the second derivative is `∓4π² ≠ 0`. -/
theorem deriv_deriv_cosFactor_ne_zero {t : ℝ} (ht : deriv cosFactor t = 0) :
    deriv (deriv cosFactor) t ≠ 0 := by
  simp only [deriv_cosFactor] at ht
  have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
  have hsin : Real.sin (2 * π * t) = 0 := by
    rcases mul_eq_zero.mp ht with h | h
    · simpa using h
    · exact absurd h h2pi
  have hcos : Real.cos (2 * π * t) ≠ 0 := by
    intro h
    have hpy := Real.sin_sq_add_cos_sq (2 * π * t)
    rw [hsin, h] at hpy
    norm_num at hpy
  simp only [deriv_deriv_cosFactor]
  exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hcos h2pi)) h2pi

/-- At an **integer** point the second derivative is `−4π² < 0`: a maximum
direction, contributing `1` to the index. -/
theorem deriv_deriv_cosFactor_int (k : ℤ) :
    deriv (deriv cosFactor) (k : ℝ) < 0 := by
  simp only [deriv_deriv_cosFactor]
  have h : Real.cos (2 * π * (k : ℝ)) = 1 := by
    rw [show (2 : ℝ) * π * (k : ℝ) = (k : ℝ) * (2 * π) by ring]
    exact Real.cos_int_mul_two_pi k
  rw [h]
  have hp : (0 : ℝ) < π := Real.pi_pos
  nlinarith

/-- At a **half-odd-integer** point the second derivative is `+4π² > 0`: a
minimum direction, contributing `0` to the index. -/
theorem deriv_deriv_cosFactor_half_odd (k : ℤ) :
    0 < deriv (deriv cosFactor) ((k : ℝ) + 1 / 2) := by
  simp only [deriv_deriv_cosFactor]
  have h : Real.cos (2 * π * ((k : ℝ) + 1 / 2)) = -1 := by
    rw [show (2 : ℝ) * π * ((k : ℝ) + 1 / 2) = (k : ℝ) * (2 * π) + π by ring]
    simp [Real.cos_add_pi, Real.cos_int_mul_two_pi]
  rw [h]
  have hp : (0 : ℝ) < π := Real.pi_pos
  nlinarith

end Examples

end Chapter1
end MorseFloer
