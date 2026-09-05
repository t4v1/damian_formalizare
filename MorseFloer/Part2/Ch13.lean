import MorseFloer.Part2.Ch16

/-!
# Chapter 13: The lemmas on the second derivative of the Floer operator

Formalization of Chapter 13 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 433–470) — the appendix that discharges the
technical debts of Chapters 9 and 11.  Its sections:

* **§13.1** the three versions of the Floer operator `F_ρ`, `𝔉_ρ`, `F`;
* **§13.2** the two lemmas on `dF` (Lemmas 9.4.8 and 9.4.16) and the elementary
  results they rest on (Lemmas 13.2.2 and 13.2.3);
* **§13.3** the extension `F̃_ρ` of the Floer operator to the ambient trivial
  bundle, and the commutative diagram `F_ρ = p_ρ ∘ (Id, F̃_ρ) ∘ i_ρ`
  (Lemma 13.3.1);
* **§13.4** the proof of the first lemma, resting on the abstract Banach-space
  Lemma 13.4.1 and on Lemma 13.4.2;
* **§13.5** the proof of the second, resting on the abstract Lemma 13.5.1;
* **§13.6, §13.7** further technical lemmas (Lemmas 9.5.1, 9.6.14, 9.6.15 and
  Lemma 13.7.1);
* **§13.8** the versions with parameters (Lemmas 13.8.1, 13.8.2, 11.4.5,
  11.4.7).

## The gap: everything phrased in `W^{1,p}(ℝ × S¹)` is unstatable

Mathlib has **no Sobolev spaces**, hence neither `W^{1,p}(ℝ × S¹; ℝ^{2n})` nor
`L^p(ℝ × S¹; ℝ^m)` nor the Banach manifold `P^{1,p}(x,z)` on which the Floer
operator lives.  Everything in this chapter whose statement mentions those
spaces therefore has nothing to be stated about, and is recorded here with no
Lean declaration rather than with a fictitious one:

* **§13.1 in its entirety.**  The three operators `F_ρ : T_{w_ρ}P^{1,p} → L^p`,
  `𝔉_ρ : W^{1,p}(ℝ × S¹; ℝ^{2n}) → L^p(ℝ × S¹; ℝ^{2n})` and
  `F : [ρ₀,∞) × W^{1,p} → L^p` are Sobolev objects; so is the identification of
  the source of `F_ρ` through `ℝ × S¹ → TW → T_W ℝ^m → ℝ^m`.
* **Lemmas 9.4.8 and 9.4.16**, the two lemmas the chapter exists to prove:
  `‖(d𝔉_ρ)_Z − (d𝔉_ρ)_0‖_op ≤ K ‖Z‖_{W^{1,p}}` and the analogous estimate for
  `∂F/∂ρ`.  Their *abstract skeletons* are Lemmas 13.4.1 and 13.5.1, which are
  proved here in full; what cannot be expressed is the verification that the
  Floer operator satisfies the hypotheses, since that verification is a
  pointwise estimate integrated in `L^p`.
* **Lemma 13.2.2** (`‖fg‖_{L^p} ≤ K ‖f‖_{L^p} ‖g‖_{W^{1,p}}`) as stated: it is
  Hölder composed with the Sobolev embedding `W^{1,p}(ℝ × S¹) → L^∞` for
  `p > 2`, and Mathlib has the first factor but not the second.  Only the
  Hölder half, `eLpNorm_mul_le_of_eLpNorm_top_le`, is stated below.
* **Lemma 13.3.1** (`X ∈ W^{1,p} ⇒ F̃_ρ(X) ∈ L^p`), the construction of `F̃_ρ`
  from the extended exponential `exp̃` and the extended almost complex
  structure, the operators `i_ρ` and `p_ρ`, and the commutative diagram of
  §13.3.  All of these are maps between Sobolev spaces.
* **§13.6** (Lemma 9.5.1: boundedness of `(α_n)` and
  `‖∂w_ρ/∂ρ − α_n ∂w_ρ/∂s‖_{L^p} → 0`) and **§13.7** (Lemmas 9.6.14 and
  9.6.15).  These are statements about the pre-glued maps `w_ρ` and about
  `L^1`/`L^2`/`L^p`/`W^{1,p}` norms of specific families of Sobolev functions;
  no abstract shadow survives.  What does survive is Lemma 13.7.1 — the Taylor
  remainder bound for the nonlinear part `N` of the Floer operator — whose
  single-norm form is `norm_taylor_remainder_le` below, and the final algebraic
  step of Lemma 9.6.15, `le_div_one_sub_of_le_add_mul`.
* **§13.8**: Lemma 13.8.1 and Lemmas 11.4.5, 11.4.7 are `L^p` estimates on the
  parametrised Floer operator.  Lemma 13.8.2 is a composition estimate whose
  abstract form, `norm_comp_sub_le_of_fderiv_le` together with
  `norm_comp₂_sub_le_of_lipschitz`, is proved below.

## What is proved here

Everything in the chapter that is a statement about normed spaces rather than
about Sobolev functions, and it is proved in full — there is no `sorry` in this
file.

* **`norm_fderiv_sub_le_of_norm_sndFDeriv_le`** — Remark 13.2.1: if `‖d²f‖` is
  bounded by `C` on a convex set then `‖df_y − df_x‖ ≤ C ‖y − x‖`.  This is the
  single assertion which, as the book observes, implies both Lemma 9.4.8 and
  Lemma 9.4.16 at once.  It is proved from `MorseFloer.sndFDeriv` and the mean
  value inequality.
* **`sndFDeriv_comp_floer` and `norm_sndFDeriv_comp_le`** — the chapter is about
  a second derivative of a *composition*, `F_ρ = p_ρ ∘ (Id, F̃_ρ) ∘ i_ρ`, so the
  chain rule `d²(ψ∘φ) = d²ψ(dφ·, dφ·) + dψ(d²φ)` is exactly the shape of its
  computations.  Rather than reprove it, this file re-exports
  `MorseFloer.sndFDeriv_comp` from `MorseFloer/Basic.lean` and adds the
  quantitative bound it yields.
* **Lemma 13.2.3**, all four parts, as `exists_const_linear` (parts 1 and 2) and
  `exists_const_bilinear` (parts 3 and 4), from the two general facts
  `exists_bound_of_compactSpace` and `exists_lip_of_compactSpace`: a `C¹` field
  of linear (resp. bilinear) maps over a compact base is uniformly bounded on a
  ball and uniformly Lipschitz in the ball variable.  The book's `W × ℝ^m` with
  `W` a compact manifold becomes a compact space times a finite-dimensional
  normed space.
* **Lemma 13.4.1**, in full, with the explicit constant
  `k = k₃(k₁r₀ + k₂)² + k₄k₁` of the book's proof, together with
  `norm_fderiv_comp₃_sub_le`, the two-step application to `χ ∘ ψ ∘ φ` that §13.4
  makes to `p_ρ ∘ (Id, F̃_ρ) ∘ i_ρ`.
* **Lemma 13.4.2** in its abstract form `norm_fderiv_bilinear_sub_le`: for a
  bounded bilinear map the hypothesis (3) of Lemma 13.4.1 holds automatically,
  with `k₃ = 2‖B‖`.  The operator `p_ρ` of §13.3 is bilinear in its last two
  arguments, which is precisely why Lemma 13.4.2 is true.
* **Lemma 13.5.1**, in full, with the explicit constant
  `M = (k₁r₀ + k₂)(k₆ + k₃(k₅r₀ + k₇)) + k₄k₅`.  The parameter derivatives
  `∂/∂ρ` are `parDeriv` and `spaceDeriv`, the two partial derivatives of a map
  `ℝ × G → H`, and the chain rule `∂/∂ρ (ψ_ρ ∘ φ_ρ) = ∂ψ/∂ρ + dψ_ρ(∂φ/∂ρ)` that
  the book's proof opens with is `hasDerivAt_comp_param`.

Following the practice of `MorseFloer.Part2.Ch8`, nothing here asserts a book
theorem *of arbitrary abstract data*: each statement below is a theorem about
normed spaces that is true as stated, and the geometric input of the Floer
setting is what has been left out, not silently assumed.
-/

open scoped ENNReal
open Metric MeasureTheory

namespace MorseFloer
namespace Chapter13

/-! ## §13.2 Remark 13.2.1 and the second differential of a composition

The book's Remark 13.2.1 observes that a single assertion implies both Lemma
9.4.8 and Lemma 9.4.16: that `F` is of class `C²` with `‖d²F‖_op` bounded on
`[ρ₀,∞) × B(0,r₀)`.  That implication is a statement about normed spaces, and
it is the mean value inequality applied to `x ↦ df_x`. -/

section SecondDerivative

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Remark 13.2.1** (abstract form).  On a convex set on which `f` is twice
differentiable with `‖d²f‖ ≤ C`, the first differential is `C`-Lipschitz:
`‖df_y − df_x‖ ≤ C ‖y − x‖`.

This is exactly the assertion the book says implies both Lemma 9.4.8 and Lemma
9.4.16.  The second differential is `MorseFloer.sndFDeriv` of
`MorseFloer/Basic.lean`. -/
theorem norm_fderiv_sub_le_of_norm_sndFDeriv_le {f : E → F} {s : Set E} {C : ℝ}
    (hs : Convex ℝ s) (hf : ∀ x ∈ s, HasFDerivAt (fderiv ℝ f) (sndFDeriv f x) x)
    (hC : ∀ x ∈ s, ‖sndFDeriv f x‖ ≤ C) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hf z hz).hasFDerivWithinAt) hC hx hy

/-- **Remark 13.2.1**, in the shape of the conclusion of Lemma 9.4.8: a bound on
the second differential on the ball `B(0,r)` gives
`‖df_Z − df_0‖ ≤ C ‖Z‖`. -/
theorem norm_fderiv_sub_fderiv_zero_le {f : E → F} {r C : ℝ}
    (hf : ∀ x ∈ closedBall (0 : E) r, HasFDerivAt (fderiv ℝ f) (sndFDeriv f x) x)
    (hC : ∀ x ∈ closedBall (0 : E) r, ‖sndFDeriv f x‖ ≤ C)
    {Z : E} (hZ : Z ∈ closedBall (0 : E) r) :
    ‖fderiv ℝ f Z - fderiv ℝ f 0‖ ≤ C * ‖Z‖ := by
  have hr : (0 : ℝ) ≤ r := le_trans (norm_nonneg Z) (mem_closedBall_zero_iff.mp hZ)
  have := norm_fderiv_sub_le_of_norm_sndFDeriv_le (convex_closedBall (0 : E) r) hf hC
    (mem_closedBall_self hr) hZ
  simpa using this

/-- **The second differential of a composition.**  The whole chapter is a
computation of the second derivative of `F_ρ = p_ρ ∘ (Id, F̃_ρ) ∘ i_ρ`, so the
transformation rule `d²(ψ∘φ)(h,k) = d²ψ(dφ h, dφ k) + dψ(d²φ(h,k))` is the
identity behind every formula of §§13.4–13.5.

It is `MorseFloer.sndFDeriv_comp`, proved in `MorseFloer/Basic.lean`; this is
its restatement in the notation of this chapter. -/
theorem sndFDeriv_comp_floer {ψ : F → G} {φ : E → F} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ (φ x)) (hφ : ContDiffAt ℝ 2 φ x) (h k : E) :
    sndFDeriv (ψ ∘ φ) x h k
      = sndFDeriv ψ (φ x) (fderiv ℝ φ x h) (fderiv ℝ φ x k)
        + fderiv ℝ ψ (φ x) (sndFDeriv φ x h k) :=
  MorseFloer.sndFDeriv_comp hψ hφ h k

/-- The quantitative form of `sndFDeriv_comp_floer`: the second differential of a
composition is bounded by `‖d²ψ‖ ‖dφ‖² + ‖dψ‖ ‖d²φ‖`.

Together with `norm_fderiv_sub_le_of_norm_sndFDeriv_le` this is what makes
Remark 13.2.1 usable for a composite operator: a bound on the second
differentials of the three factors of `p_ρ ∘ (Id, F̃_ρ) ∘ i_ρ` bounds the second
differential of `F_ρ`. -/
theorem norm_sndFDeriv_comp_le {ψ : F → G} {φ : E → F} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ (φ x)) (hφ : ContDiffAt ℝ 2 φ x) (h k : E) :
    ‖sndFDeriv (ψ ∘ φ) x h k‖
      ≤ ‖sndFDeriv ψ (φ x)‖ * ‖fderiv ℝ φ x‖ ^ 2 * ‖h‖ * ‖k‖
        + ‖fderiv ℝ ψ (φ x)‖ * ‖sndFDeriv φ x‖ * ‖h‖ * ‖k‖ := by
  rw [sndFDeriv_comp_floer hψ hφ h k]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖sndFDeriv ψ (φ x) (fderiv ℝ φ x h) (fderiv ℝ φ x k)‖
        ≤ ‖sndFDeriv ψ (φ x)‖ * ‖fderiv ℝ φ x h‖ * ‖fderiv ℝ φ x k‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ ‖sndFDeriv ψ (φ x)‖ * (‖fderiv ℝ φ x‖ * ‖h‖) * (‖fderiv ℝ φ x‖ * ‖k‖) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _)
            (norm_nonneg (sndFDeriv ψ (φ x)))) (ContinuousLinearMap.le_opNorm _ _)
            (norm_nonneg _) (by positivity)
      _ = ‖sndFDeriv ψ (φ x)‖ * ‖fderiv ℝ φ x‖ ^ 2 * ‖h‖ * ‖k‖ := by ring
  · calc ‖fderiv ℝ ψ (φ x) (sndFDeriv φ x h k)‖
        ≤ ‖fderiv ℝ ψ (φ x)‖ * ‖sndFDeriv φ x h k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ ψ (φ x)‖ * (‖sndFDeriv φ x‖ * ‖h‖ * ‖k‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm₂ _ _ _) (norm_nonneg _)
      _ = ‖fderiv ℝ ψ (φ x)‖ * ‖sndFDeriv φ x‖ * ‖h‖ * ‖k‖ := by ring

end SecondDerivative

/-! ## §13.2 Lemma 13.2.2: the Hölder half

The book's Lemma 13.2.2 says that for `p > 2` and `f, g ∈ W^{1,p}(ℝ × S¹; ℝ)`
one has `‖fg‖_{L^p} ≤ K ‖f‖_{L^p} ‖g‖_{W^{1,p}}`, and proves it in two steps:
the continuous Sobolev embedding `W^{1,p}(ℝ × S¹) → L^∞` (unavailable: Mathlib
has no Sobolev spaces) and Hölder's inequality `‖fg‖_{L^p} ≤ ‖g‖_∞ ‖f‖_{L^p}`.
The second step is stated here; the first is what makes the lemma itself
unstatable. -/

section Holder

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Lemma 13.2.2, the half Mathlib can state.**  If `‖g‖_∞ ≤ K` then
`‖fg‖_{L^p} ≤ K ‖f‖_{L^p}`.

In the book `K` comes from the Sobolev embedding `‖g‖_∞ ≤ K ‖g‖_{W^{1,p}}`,
valid on `ℝ × S¹` for `p > 2`; that embedding is exactly what Mathlib lacks. -/
theorem eLpNorm_mul_le_of_eLpNorm_top_le {p : ℝ≥0∞} {f g : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {K : ℝ≥0∞} (hg : eLpNorm g ∞ μ ≤ K) :
    eLpNorm (fun x => f x * g x) p μ ≤ K * eLpNorm f p μ := by
  have hfg : (fun x => f x * g x) = f • g := by
    funext x; simp [Pi.smul_apply', smul_eq_mul]
  rw [hfg]
  calc eLpNorm (f • g) p μ
      ≤ eLpNorm f p μ * eLpNorm g ∞ μ := eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top p g hf
    _ ≤ eLpNorm f p μ * K := by gcongr
    _ = K * eLpNorm f p μ := mul_comm _ _

end Holder

/-! ## §13.2 Lemma 13.2.3

The book's data is a compact manifold `W` and `C^∞` maps
`A : W × ℝ^m × ℝ^m → ℝ^m` linear in the last variable and
`B : W × ℝ^m × ℝ^m × ℝ^m → ℝ^m` bilinear in the last two.  Regarding `A` as a
map `W × ℝ^m → L(ℝ^m; ℝ^m)` and `B` as a map into the bilinear maps — which is
literally what the book's proof does — the four assertions become two, applied
to two different target spaces.  Here `W` is any compact space and `ℝ^m` any
finite-dimensional real normed space. -/

section CompactEstimates

variable {P : Type*} [TopologicalSpace P] [CompactSpace P]
variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

omit [NormedSpace ℝ N] in
/-- Step (1) of the proof of Lemma 13.2.3: a continuous map on `W × B(0,r)` has
bounded image, because that set is compact. -/
theorem exists_bound_of_compactSpace {A : P × E → N} (hA : Continuous A) (r : ℝ) :
    ∃ C > 0, ∀ p : P, ∀ X ∈ closedBall (0 : E) r, ‖A (p, X)‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ.prod (isCompact_closedBall (0 : E) r)).exists_bound_of_continuousOn
      hA.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun p X hX => ?_⟩
  exact (hC (p, X) ⟨Set.mem_univ p, hX⟩).trans (le_max_left _ _)

/-- Step (2) of the proof of Lemma 13.2.3: the mean value inequality along the
segment `[0, X]`, with the derivative bounded uniformly over the compact base. -/
theorem exists_lip_of_compactSpace {A : P × E → N} {A' : P × E → (E →L[ℝ] N)}
    (hA' : Continuous A')
    (hderiv : ∀ (p : P) (X : E), HasFDerivAt (fun Y => A (p, Y)) (A' (p, X)) X)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ C > 0, ∀ p : P, ∀ X ∈ closedBall (0 : E) r, ‖A (p, X) - A (p, 0)‖ ≤ C * ‖X‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_compactSpace hA' r
  refine ⟨C, hC0, fun p X hX => ?_⟩
  have := (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun Y => A (p, Y)) (f' := fun Y => A' (p, Y))
    (fun Y _ => (hderiv p Y).hasFDerivWithinAt) (fun Y hY => hC p Y hY)
    (mem_closedBall_self hr) hX
  simpa using this

/-- **Lemma 13.2.3, parts (1) and (2).**  Let `A` be a `C¹` field, over a compact
base `P`, of continuous linear maps depending on a point `X` of a
finite-dimensional space.  Then there is a constant `C`, uniform in the base
point and in `X ∈ B(0,r₁)`, with

* `‖A(p,X) v‖ ≤ C ‖v‖`;
* `‖A(p,X) v₂ − A(p,0) v₁‖ ≤ C (‖X‖ ‖v₁‖ + ‖v₂ − v₁‖)`.

The second is obtained, as in the book, by splitting
`A(p,X)v₂ − A(p,0)v₁ = A(p,X)(v₂ − v₁) + (A(p,X) − A(p,0))v₁`. -/
theorem exists_const_linear {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {A : P × E → (E →L[ℝ] F')} {A' : P × E → (E →L[ℝ] E →L[ℝ] F')}
    (hA : Continuous A) (hA' : Continuous A')
    (hderiv : ∀ (p : P) (X : E), HasFDerivAt (fun Y => A (p, Y)) (A' (p, X)) X)
    {r₁ : ℝ} (hr₁ : 0 ≤ r₁) :
    ∃ C > 0, ∀ p : P, ∀ X ∈ closedBall (0 : E) r₁,
      (∀ v : E, ‖A (p, X) v‖ ≤ C * ‖v‖) ∧
      (∀ v₁ v₂ : E, ‖A (p, X) v₂ - A (p, 0) v₁‖ ≤ C * (‖X‖ * ‖v₁‖ + ‖v₂ - v₁‖)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_of_compactSpace hA r₁
  obtain ⟨C₂, _, hC₂⟩ := exists_lip_of_compactSpace hA' hderiv hr₁
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁0 (le_max_left _ _), fun p X hX => ⟨?_, ?_⟩⟩
  · intro v
    exact ((A (p, X)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((hC₁ p X hX).trans (le_max_left _ _)) (norm_nonneg v))
  · intro v₁ v₂
    have key : A (p, X) v₂ - A (p, 0) v₁
        = A (p, X) (v₂ - v₁) + (A (p, X) - A (p, 0)) v₁ := by
      rw [map_sub, sub_apply]; abel
    rw [key]
    have h1 : ‖A (p, X) (v₂ - v₁)‖ ≤ max C₁ C₂ * ‖v₂ - v₁‖ :=
      ((A (p, X)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right ((hC₁ p X hX).trans (le_max_left _ _)) (norm_nonneg _))
    have h2 : ‖(A (p, X) - A (p, 0)) v₁‖ ≤ max C₁ C₂ * ‖X‖ * ‖v₁‖ := by
      refine ((A (p, X) - A (p, 0)).le_opNorm v₁).trans ?_
      have hb : ‖A (p, X) - A (p, 0)‖ ≤ max C₁ C₂ * ‖X‖ :=
        (hC₂ p X hX).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg X))
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg v₁)
    calc ‖A (p, X) (v₂ - v₁) + (A (p, X) - A (p, 0)) v₁‖
        ≤ ‖A (p, X) (v₂ - v₁)‖ + ‖(A (p, X) - A (p, 0)) v₁‖ := norm_add_le _ _
      _ ≤ max C₁ C₂ * ‖v₂ - v₁‖ + max C₁ C₂ * ‖X‖ * ‖v₁‖ := add_le_add h1 h2
      _ = max C₁ C₂ * (‖X‖ * ‖v₁‖ + ‖v₂ - v₁‖) := by ring

/-- **Lemma 13.2.3, parts (3) and (4).**  The same statement for a `C¹` field of
*bilinear* maps:

* `‖B(p,X) v Y‖ ≤ C ‖v‖ ‖Y‖`;
* `‖B(p,X) v Y₂ − B(p,0) v Y₁‖ ≤ C (‖X‖ ‖v‖ ‖Y₁‖ + ‖v‖ ‖Y₂ − Y₁‖)`.

The book says "one proceeds as in (1)"; here that is literal — this is
`exists_const_linear` with target space `E →L[ℝ] F'`. -/
theorem exists_const_bilinear {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {B : P × E → (E →L[ℝ] E →L[ℝ] F')} {B' : P × E → (E →L[ℝ] E →L[ℝ] E →L[ℝ] F')}
    (hB : Continuous B) (hB' : Continuous B')
    (hderiv : ∀ (p : P) (X : E), HasFDerivAt (fun Y => B (p, Y)) (B' (p, X)) X)
    {r₁ : ℝ} (hr₁ : 0 ≤ r₁) :
    ∃ C > 0, ∀ p : P, ∀ X ∈ closedBall (0 : E) r₁,
      (∀ v Y : E, ‖B (p, X) v Y‖ ≤ C * ‖v‖ * ‖Y‖) ∧
      (∀ v Y₁ Y₂ : E, ‖B (p, X) v Y₂ - B (p, 0) v Y₁‖
        ≤ C * (‖X‖ * ‖v‖ * ‖Y₁‖ + ‖v‖ * ‖Y₂ - Y₁‖)) := by
  obtain ⟨C, hC0, hC⟩ := exists_const_linear (F' := E →L[ℝ] F') hB hB' hderiv hr₁
  refine ⟨C, hC0, fun p X hX => ⟨?_, ?_⟩⟩
  · intro v Y
    exact ((B (p, X) v).le_opNorm Y).trans
      (mul_le_mul_of_nonneg_right ((hC p X hX).1 v) (norm_nonneg Y))
  · intro v Y₁ Y₂
    have key : B (p, X) v Y₂ - B (p, 0) v Y₁
        = B (p, X) v (Y₂ - Y₁) + (B (p, X) v - B (p, 0) v) Y₁ := by
      rw [map_sub, sub_apply]; abel
    rw [key]
    have h1 : ‖B (p, X) v (Y₂ - Y₁)‖ ≤ C * ‖v‖ * ‖Y₂ - Y₁‖ :=
      ((B (p, X) v).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right ((hC p X hX).1 v) (norm_nonneg _))
    have h2 : ‖(B (p, X) v - B (p, 0) v) Y₁‖ ≤ C * (‖X‖ * ‖v‖) * ‖Y₁‖ := by
      refine ((B (p, X) v - B (p, 0) v).le_opNorm Y₁).trans ?_
      have hb := (hC p X hX).2 v v
      rw [sub_self, norm_zero, add_zero] at hb
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg Y₁)
    calc ‖B (p, X) v (Y₂ - Y₁) + (B (p, X) v - B (p, 0) v) Y₁‖
        ≤ ‖B (p, X) v (Y₂ - Y₁)‖ + ‖(B (p, X) v - B (p, 0) v) Y₁‖ := norm_add_le _ _
      _ ≤ C * ‖v‖ * ‖Y₂ - Y₁‖ + C * (‖X‖ * ‖v‖) * ‖Y₁‖ := add_le_add h1 h2
      _ = C * (‖X‖ * ‖v‖ * ‖Y₁‖ + ‖v‖ * ‖Y₂ - Y₁‖) := by ring

end CompactEstimates

/-! ## §13.4 Lemma 13.4.1 and its two-step application

Lemma 13.4.1 is the technical heart of the chapter: an abstract statement about
two differentiable maps `φ : G → H`, `ψ : H → K` between Banach spaces, saying
that the estimate `‖dφ_Z − dφ_0‖ ≤ k₁‖Z‖` of Lemma 9.4.8 is *stable under
composition*.  All constants are explicit, since in the application `φ` and `ψ`
depend on the gluing parameter `ρ` and the point is that the resulting constant
does not. -/

section Composition

variable {G H H' K : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup H'] [NormedSpace ℝ H']
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The mean value estimate used twice in §13.4 and once in §13.5: hypotheses (1)
and (2) of Lemma 13.4.1 give `‖φ Z − φ 0‖ ≤ (k₁‖Z‖ + k₂)‖Z‖`. -/
theorem norm_sub_le_of_fderiv_estimates {φ : G → H} {r₀ k₁ k₂ : ℝ}
    (hφ : Differentiable ℝ φ)
    (h1 : ∀ Z ∈ closedBall (0 : G) r₀, ‖fderiv ℝ φ Z - fderiv ℝ φ 0‖ ≤ k₁ * ‖Z‖)
    (h2 : ‖fderiv ℝ φ 0‖ ≤ k₂) (hk₁ : 0 ≤ k₁)
    {Z : G} (hZ : Z ∈ closedBall (0 : G) r₀) :
    ‖φ Z - φ 0‖ ≤ (k₁ * ‖Z‖ + k₂) * ‖Z‖ := by
  have hZr : ‖Z‖ ≤ r₀ := mem_closedBall_zero_iff.mp hZ
  have hsub : closedBall (0 : G) ‖Z‖ ⊆ closedBall (0 : G) r₀ := closedBall_subset_closedBall hZr
  have hbound : ∀ W ∈ closedBall (0 : G) ‖Z‖, ‖fderiv ℝ φ W‖ ≤ k₁ * ‖Z‖ + k₂ := by
    intro W hW
    have hW' : ‖W‖ ≤ ‖Z‖ := mem_closedBall_zero_iff.mp hW
    have htri := norm_add_le (fderiv ℝ φ W - fderiv ℝ φ 0) (fderiv ℝ φ 0)
    rw [sub_add_cancel] at htri
    refine htri.trans (add_le_add ?_ h2)
    exact (h1 W (hsub hW)).trans (mul_le_mul_of_nonneg_left hW' hk₁)
  have := (convex_closedBall (0 : G) ‖Z‖).norm_image_sub_le_of_norm_fderiv_le
    (fun W _ => hφ W) hbound (mem_closedBall_self (norm_nonneg Z))
    (mem_closedBall_zero_iff.mpr le_rfl)
  simpa using this

/-- **Lemma 13.4.1.**  Let `φ : G → H` and `ψ : H → K` be differentiable maps
between normed spaces and suppose that, on the ball `B(0,r₀) ⊆ G`,

1. `‖dφ_Z − dφ_0‖ ≤ k₁ ‖Z‖`,
2. `‖dφ_0‖ ≤ k₂`,
3. `‖dψ_{φ Z} − dψ_{φ 0}‖ ≤ k₃ ‖φ Z − φ 0‖`,
4. `‖dψ_{φ 0}‖ ≤ k₄`.

Then `‖d(ψ∘φ)_Z − d(ψ∘φ)_0‖ ≤ k ‖Z‖` on that ball, with the explicit constant
`k = k₃(k₁r₀ + k₂)² + k₄k₁` — a constant depending only on `r₀` and the `kᵢ`,
which is the whole point: in §13.4 the operators depend on the gluing parameter
`ρ` and the constant must not.

The proof is the book's: split
`d(ψφ)_Z v − d(ψφ)_0 v = (dψ_{φZ} − dψ_{φ0})(dφ_Z v) + dψ_{φ0}((dφ_Z − dφ_0)v)`,
estimate `‖φ Z − φ 0‖` by the mean value inequality and `‖dφ_Z‖` by
`k₁‖Z‖ + k₂`. -/
theorem norm_fderiv_comp_sub_le {φ : G → H} {ψ : H → K} {r₀ k₁ k₂ k₃ k₄ : ℝ}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ)
    (h1 : ∀ Z ∈ closedBall (0 : G) r₀, ‖fderiv ℝ φ Z - fderiv ℝ φ 0‖ ≤ k₁ * ‖Z‖)
    (h2 : ‖fderiv ℝ φ 0‖ ≤ k₂)
    (h3 : ∀ Z ∈ closedBall (0 : G) r₀,
      ‖fderiv ℝ ψ (φ Z) - fderiv ℝ ψ (φ 0)‖ ≤ k₃ * ‖φ Z - φ 0‖)
    (h4 : ‖fderiv ℝ ψ (φ 0)‖ ≤ k₄)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₃ : 0 ≤ k₃) (hk₄ : 0 ≤ k₄)
    {Z : G} (hZ : Z ∈ closedBall (0 : G) r₀) :
    ‖fderiv ℝ (ψ ∘ φ) Z - fderiv ℝ (ψ ∘ φ) 0‖
      ≤ (k₃ * (k₁ * r₀ + k₂) ^ 2 + k₄ * k₁) * ‖Z‖ := by
  have hZr : ‖Z‖ ≤ r₀ := mem_closedBall_zero_iff.mp hZ
  have hr₀ : (0 : ℝ) ≤ r₀ := le_trans (norm_nonneg Z) hZr
  have hA : (0 : ℝ) ≤ k₁ * ‖Z‖ + k₂ := add_nonneg (mul_nonneg hk₁ (norm_nonneg Z)) hk₂
  -- `‖dφ_Z‖ ≤ k₁‖Z‖ + k₂`.
  have hdZ : ‖fderiv ℝ φ Z‖ ≤ k₁ * ‖Z‖ + k₂ := by
    have htri := norm_add_le (fderiv ℝ φ Z - fderiv ℝ φ 0) (fderiv ℝ φ 0)
    rw [sub_add_cancel] at htri
    exact htri.trans (add_le_add (h1 Z hZ) h2)
  -- `‖φ Z − φ 0‖ ≤ (k₁‖Z‖ + k₂)‖Z‖`.
  have hφZ : ‖φ Z - φ 0‖ ≤ (k₁ * ‖Z‖ + k₂) * ‖Z‖ :=
    norm_sub_le_of_fderiv_estimates hφ h1 h2 hk₁ hZ
  have hle : k₁ * ‖Z‖ + k₂ ≤ k₁ * r₀ + k₂ := by
    have := mul_le_mul_of_nonneg_left hZr hk₁
    linarith
  have hsq : (k₁ * ‖Z‖ + k₂) ^ 2 ≤ (k₁ * r₀ + k₂) ^ 2 := by
    have := mul_self_le_mul_self hA hle
    simpa [pow_two] using this
  have hM : (0 : ℝ) ≤ k₃ * (k₁ * r₀ + k₂) ^ 2 + k₄ * k₁ :=
    add_nonneg (mul_nonneg hk₃ (sq_nonneg _)) (mul_nonneg hk₄ hk₁)
  rw [fderiv_comp Z (hψ (φ Z)) (hφ Z), fderiv_comp (0 : G) (hψ (φ 0)) (hφ 0)]
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg Z)) fun v => ?_
  have key : ((fderiv ℝ ψ (φ Z)).comp (fderiv ℝ φ Z)
        - (fderiv ℝ ψ (φ 0)).comp (fderiv ℝ φ 0)) v
      = (fderiv ℝ ψ (φ Z) - fderiv ℝ ψ (φ 0)) (fderiv ℝ φ Z v)
        + fderiv ℝ ψ (φ 0) ((fderiv ℝ φ Z - fderiv ℝ φ 0) v) := by
    simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [key]
  have e1 : ‖(fderiv ℝ ψ (φ Z) - fderiv ℝ ψ (φ 0)) (fderiv ℝ φ Z v)‖
      ≤ k₃ * ((k₁ * ‖Z‖ + k₂) * ‖Z‖) * ((k₁ * ‖Z‖ + k₂) * ‖v‖) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul ((h3 Z hZ).trans (mul_le_mul_of_nonneg_left hφZ hk₃))
      (((fderiv ℝ φ Z).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hdZ (norm_nonneg v)))
      (norm_nonneg _) (mul_nonneg hk₃ (mul_nonneg hA (norm_nonneg Z)))
  have e2 : ‖fderiv ℝ ψ (φ 0) ((fderiv ℝ φ Z - fderiv ℝ φ 0) v)‖ ≤ k₄ * (k₁ * ‖Z‖ * ‖v‖) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul h4
      (((fderiv ℝ φ Z - fderiv ℝ φ 0).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (h1 Z hZ) (norm_nonneg v)))
      (norm_nonneg _) hk₄
  calc ‖(fderiv ℝ ψ (φ Z) - fderiv ℝ ψ (φ 0)) (fderiv ℝ φ Z v)
          + fderiv ℝ ψ (φ 0) ((fderiv ℝ φ Z - fderiv ℝ φ 0) v)‖
      ≤ ‖(fderiv ℝ ψ (φ Z) - fderiv ℝ ψ (φ 0)) (fderiv ℝ φ Z v)‖
        + ‖fderiv ℝ ψ (φ 0) ((fderiv ℝ φ Z - fderiv ℝ φ 0) v)‖ := norm_add_le _ _
    _ ≤ k₃ * ((k₁ * ‖Z‖ + k₂) * ‖Z‖) * ((k₁ * ‖Z‖ + k₂) * ‖v‖) + k₄ * (k₁ * ‖Z‖ * ‖v‖) :=
        add_le_add e1 e2
    _ = (k₃ * (k₁ * ‖Z‖ + k₂) ^ 2 + k₄ * k₁) * ‖Z‖ * ‖v‖ := by ring
    _ ≤ (k₃ * (k₁ * r₀ + k₂) ^ 2 + k₄ * k₁) * ‖Z‖ * ‖v‖ := by
        have hstep : k₃ * (k₁ * ‖Z‖ + k₂) ^ 2 + k₄ * k₁
            ≤ k₃ * (k₁ * r₀ + k₂) ^ 2 + k₄ * k₁ := by
          have := mul_le_mul_of_nonneg_left hsq hk₃
          linarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hstep (norm_nonneg Z)) (norm_nonneg v)

/-- **The two-step application of Lemma 13.4.1** made in §13.4: the estimate is
stable under a *threefold* composition `χ ∘ ψ ∘ φ`, which is the shape
`p_ρ ∘ (Id, F̃_ρ) ∘ i_ρ` of the Floer operator.

The book applies Lemma 13.4.1 first to `(φ, ψ) = (i_ρ, Id × F̃_ρ)` and then to
`(ψ ∘ φ, χ) = ((Id × F̃_ρ) ∘ i_ρ, p_ρ)`; the hypothesis (1) of the second
application is the conclusion of the first, and its hypothesis (2) is
`‖d(ψ∘φ)_0‖ ≤ ‖dψ_{φ0}‖ ‖dφ_0‖ ≤ k₄k₂`.  That bookkeeping is what is proved
here. -/
theorem norm_fderiv_comp₃_sub_le {φ : G → H} {ψ : H → H'} {χ : H' → K}
    {r₀ k₁ k₂ k₃ k₄ k₅ k₆ : ℝ}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (hχ : Differentiable ℝ χ)
    (h1 : ∀ Z ∈ closedBall (0 : G) r₀, ‖fderiv ℝ φ Z - fderiv ℝ φ 0‖ ≤ k₁ * ‖Z‖)
    (h2 : ‖fderiv ℝ φ 0‖ ≤ k₂)
    (h3 : ∀ Z ∈ closedBall (0 : G) r₀,
      ‖fderiv ℝ ψ (φ Z) - fderiv ℝ ψ (φ 0)‖ ≤ k₃ * ‖φ Z - φ 0‖)
    (h4 : ‖fderiv ℝ ψ (φ 0)‖ ≤ k₄)
    (h5 : ∀ Z ∈ closedBall (0 : G) r₀,
      ‖fderiv ℝ χ (ψ (φ Z)) - fderiv ℝ χ (ψ (φ 0))‖ ≤ k₅ * ‖ψ (φ Z) - ψ (φ 0)‖)
    (h6 : ‖fderiv ℝ χ (ψ (φ 0))‖ ≤ k₆)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₃ : 0 ≤ k₃) (hk₄ : 0 ≤ k₄)
    (hk₅ : 0 ≤ k₅) (hk₆ : 0 ≤ k₆)
    {Z : G} (hZ : Z ∈ closedBall (0 : G) r₀) :
    ‖fderiv ℝ (χ ∘ ψ ∘ φ) Z - fderiv ℝ (χ ∘ ψ ∘ φ) 0‖
      ≤ (k₅ * ((k₃ * (k₁ * r₀ + k₂) ^ 2 + k₄ * k₁) * r₀ + k₄ * k₂) ^ 2
          + k₆ * (k₃ * (k₁ * r₀ + k₂) ^ 2 + k₄ * k₁)) * ‖Z‖ := by
  set k₁' := k₃ * (k₁ * r₀ + k₂) ^ 2 + k₄ * k₁ with hk₁'def
  have hk₁' : 0 ≤ k₁' := add_nonneg (mul_nonneg hk₃ (sq_nonneg _)) (mul_nonneg hk₄ hk₁)
  have h1' : ∀ W ∈ closedBall (0 : G) r₀,
      ‖fderiv ℝ (ψ ∘ φ) W - fderiv ℝ (ψ ∘ φ) 0‖ ≤ k₁' * ‖W‖ := fun W hW =>
    norm_fderiv_comp_sub_le hφ hψ h1 h2 h3 h4 hk₁ hk₂ hk₃ hk₄ hW
  have h2' : ‖fderiv ℝ (ψ ∘ φ) 0‖ ≤ k₄ * k₂ := by
    rw [fderiv_comp (0 : G) (hψ (φ 0)) (hφ 0)]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h4 h2 (norm_nonneg _) hk₄)
  exact norm_fderiv_comp_sub_le (hψ.comp hφ) hχ h1' h2' h5 h6 hk₁'
    (mul_nonneg hk₄ hk₂) hk₅ hk₆ hZ

end Composition

/-! ## §13.4 Lemma 13.4.2, in its abstract form

Lemma 13.4.2 says that the operator `p_ρ` of §13.3 satisfies hypothesis (3) of
Lemma 13.4.1.  `p_ρ` is built from a map `P(p, X, Y, Z)` bilinear in its last two
arguments, and the reason the lemma is true is that a *bounded bilinear map*
always satisfies that hypothesis, with a constant controlled by its norm.  That
is the statement proved here; the `L^p` bookkeeping that turns it into Lemma
13.4.2 itself is Sobolev and is not available. -/

section Bilinear

variable {H₁ H₂ K : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- **Lemma 13.4.2, abstract form.**  For a bounded bilinear map `B`, the
differential of `(x,y) ↦ B x y` is globally Lipschitz with constant `2‖B‖`:

`‖d(B)_z − d(B)_w‖ ≤ 2‖B‖ ‖z − w‖`.

In particular hypothesis (3) of Lemma 13.4.1 holds for such a map with
`k₃ = 2‖B‖`, which is exactly what Lemma 13.4.2 asserts about `p_ρ`. -/
theorem norm_fderiv_bilinear_sub_le (B : H₁ →L[ℝ] H₂ →L[ℝ] K) (z w : H₁ × H₂) :
    ‖fderiv ℝ (fun q : H₁ × H₂ => B q.1 q.2) z
      - fderiv ℝ (fun q : H₁ × H₂ => B q.1 q.2) w‖ ≤ 2 * ‖B‖ * ‖z - w‖ := by
  have hB : IsBoundedBilinearMap ℝ (fun q : H₁ × H₂ => B q.1 q.2) := B.isBoundedBilinearMap
  have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := by simpa using norm_fst_le (z - w)
  have h2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := by simpa using norm_snd_le (z - w)
  rw [(hB.hasFDerivAt z).fderiv, (hB.hasFDerivAt w).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q => ?_
  have hval : (hB.deriv z - hB.deriv w) q = B (z.1 - w.1) q.2 + B q.1 (z.2 - w.2) := by
    simp only [sub_apply, IsBoundedBilinearMap.deriv_apply, map_sub]
    abel
  rw [hval]
  have e1 : ‖B (z.1 - w.1) q.2‖ ≤ ‖B‖ * ‖z - w‖ * ‖q‖ :=
    (B.le_opNorm₂ _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg B)) (norm_snd_le q)
        (norm_nonneg _) (by positivity))
  have e2 : ‖B q.1 (z.2 - w.2)‖ ≤ ‖B‖ * ‖q‖ * ‖z - w‖ :=
    (B.le_opNorm₂ _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (norm_fst_le q) (norm_nonneg B)) h2
        (norm_nonneg _) (by positivity))
  calc ‖B (z.1 - w.1) q.2 + B q.1 (z.2 - w.2)‖
      ≤ ‖B (z.1 - w.1) q.2‖ + ‖B q.1 (z.2 - w.2)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖z - w‖ * ‖q‖ + ‖B‖ * ‖q‖ * ‖z - w‖ := add_le_add e1 e2
    _ = 2 * ‖B‖ * ‖z - w‖ * ‖q‖ := by ring

end Bilinear

/-! ## §13.5 Lemma 13.5.1

The second lemma on `dF` needs the analogue of Lemma 13.4.1 for the derivative
in the gluing parameter `ρ`.  A family `ρ ↦ φ_ρ` is here a single map
`Φ : ℝ × G → H`; its two partial derivatives are `parDeriv Φ ρ z = ∂Φ/∂ρ` and
`spaceDeriv Φ ρ z = d(Φ(ρ,·))_z`.  The chain rule the book's proof opens with,
`∂/∂ρ(ψ_ρ ∘ φ_ρ) = ∂ψ/∂ρ ∘ φ_ρ + dψ_ρ(∂φ/∂ρ)`, is `hasDerivAt_comp_param`. -/

section Parameter

variable {G H K : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The partial derivative of a family `Φ : ℝ × G → H` in the parameter, the
book's `∂Φ/∂ρ`. -/
noncomputable def parDeriv (Φ : ℝ × G → H) (ρ : ℝ) (z : G) : H :=
  fderiv ℝ Φ (ρ, z) (1, 0)

/-- The partial differential of a family `Φ : ℝ × G → H` in the space variable,
the book's `(dΦ_ρ)_z`. -/
noncomputable def spaceDeriv (Φ : ℝ × G → H) (ρ : ℝ) (z : G) : G →L[ℝ] H :=
  (fderiv ℝ Φ (ρ, z)).comp (ContinuousLinearMap.inr ℝ ℝ G)

/-- A continuous linear map on `ℝ × G` splits into its two partial pieces. -/
theorem apply_split (A : ℝ × G →L[ℝ] H) (a : ℝ) (v : G) :
    A (a, v) = a • A (1, 0) + A (0, v) := by
  have hsplit : ((a : ℝ), v) = a • ((1 : ℝ), (0 : G)) + ((0 : ℝ), v) := by
    simp
  rw [hsplit, map_add, map_smul]

/-- The parameter derivative really is the derivative of `r ↦ Φ (r, z)`. -/
theorem hasDerivAt_parDeriv {Φ : ℝ × G → H} {ρ : ℝ} {z : G}
    (hΦ : DifferentiableAt ℝ Φ (ρ, z)) :
    HasDerivAt (fun r => Φ (r, z)) (parDeriv Φ ρ z) ρ := by
  have hc : HasDerivAt (fun r : ℝ => (r, z)) ((1 : ℝ), (0 : G)) ρ :=
    (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ z)
  simpa [parDeriv, Function.comp_def] using hΦ.hasFDerivAt.comp_hasDerivAt ρ hc

/-- **The chain rule in the parameter**, the identity the proof of Lemma 13.5.1
opens with:
`∂/∂ρ (ψ_ρ (φ_ρ z)) = (∂ψ/∂ρ)(φ_ρ z) + (dψ_ρ)_{φ_ρ z}(∂φ/∂ρ (z))`. -/
theorem hasDerivAt_comp_param {Φ : ℝ × G → H} {Ψ : ℝ × H → K} {ρ : ℝ} {z : G}
    (hΨ : DifferentiableAt ℝ Ψ (ρ, Φ (ρ, z))) (hΦ : DifferentiableAt ℝ Φ (ρ, z)) :
    HasDerivAt (fun r => Ψ (r, Φ (r, z)))
      (parDeriv Ψ ρ (Φ (ρ, z)) + spaceDeriv Ψ ρ (Φ (ρ, z)) (parDeriv Φ ρ z)) ρ := by
  have hc : HasDerivAt (fun r : ℝ => (r, Φ (r, z))) ((1 : ℝ), parDeriv Φ ρ z) ρ :=
    (hasDerivAt_id ρ).prodMk (hasDerivAt_parDeriv hΦ)
  have hcomp := hΨ.hasFDerivAt.comp_hasDerivAt ρ hc
  have heq : fderiv ℝ Ψ (ρ, Φ (ρ, z)) ((1 : ℝ), parDeriv Φ ρ z)
      = parDeriv Ψ ρ (Φ (ρ, z)) + spaceDeriv Ψ ρ (Φ (ρ, z)) (parDeriv Φ ρ z) := by
    rw [apply_split]
    simp [parDeriv, spaceDeriv]
  rw [heq] at hcomp
  simpa [Function.comp_def] using hcomp

/-- **Lemma 13.5.1.**  Let `Φ : ℝ × G → H` and `Ψ : ℝ × H → K` be families of
operators, differentiable in both variables, and fix a parameter value `ρ`.
Suppose that on the ball `B(0,r₀) ⊆ G`

1. the hypotheses of Lemma 13.4.1 hold for `Φ(ρ,·)` and `Ψ(ρ,·)`, with the
   constants `k₁, k₂, k₃, k₄`;
2. `‖∂Φ/∂ρ (z) − ∂Φ/∂ρ (0)‖ ≤ k₅ ‖z‖`;
3. `‖∂Ψ/∂ρ (Φ(ρ,z)) − ∂Ψ/∂ρ (Φ(ρ,0))‖ ≤ k₆ ‖Φ(ρ,z) − Φ(ρ,0)‖`;
4. `‖∂Φ/∂ρ (0)‖ ≤ k₇`.

Then `‖∂/∂ρ(Ψ ∘ Φ)(z) − ∂/∂ρ(Ψ ∘ Φ)(0)‖ ≤ M ‖z‖` on the ball, with the explicit
constant `M = (k₁r₀ + k₂)(k₆ + k₃(k₅r₀ + k₇)) + k₄k₅`, independent of `ρ`.

The proof is the book's: expand the parameter derivative of the composite with
`hasDerivAt_comp_param`, split the difference into three terms, and estimate
them by hypotheses (3), (1) and (4) of Lemma 13.4.1 together with the mean value
bound `‖Φ(ρ,z) − Φ(ρ,0)‖ ≤ (k₁r₀ + k₂)‖z‖`. -/
theorem norm_parDeriv_comp_sub_le {Φ : ℝ × G → H} {Ψ : ℝ × H → K}
    {ρ r₀ k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℝ}
    (hΦ : ∀ z : G, DifferentiableAt ℝ Φ (ρ, z))
    (hΨ : ∀ y : H, DifferentiableAt ℝ Ψ (ρ, y))
    (hφ : Differentiable ℝ fun w => Φ (ρ, w))
    (h1 : ∀ z ∈ closedBall (0 : G) r₀,
      ‖fderiv ℝ (fun w => Φ (ρ, w)) z - fderiv ℝ (fun w => Φ (ρ, w)) 0‖ ≤ k₁ * ‖z‖)
    (h2 : ‖fderiv ℝ (fun w => Φ (ρ, w)) 0‖ ≤ k₂)
    (h3 : ∀ z ∈ closedBall (0 : G) r₀,
      ‖spaceDeriv Ψ ρ (Φ (ρ, z)) - spaceDeriv Ψ ρ (Φ (ρ, 0))‖ ≤ k₃ * ‖Φ (ρ, z) - Φ (ρ, 0)‖)
    (h4 : ‖spaceDeriv Ψ ρ (Φ (ρ, 0))‖ ≤ k₄)
    (h5 : ∀ z ∈ closedBall (0 : G) r₀, ‖parDeriv Φ ρ z - parDeriv Φ ρ 0‖ ≤ k₅ * ‖z‖)
    (h6 : ∀ z ∈ closedBall (0 : G) r₀,
      ‖parDeriv Ψ ρ (Φ (ρ, z)) - parDeriv Ψ ρ (Φ (ρ, 0))‖ ≤ k₆ * ‖Φ (ρ, z) - Φ (ρ, 0)‖)
    (h7 : ‖parDeriv Φ ρ 0‖ ≤ k₇)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₃ : 0 ≤ k₃) (hk₄ : 0 ≤ k₄)
    (hk₅ : 0 ≤ k₅) (hk₆ : 0 ≤ k₆)
    {z : G} (hz : z ∈ closedBall (0 : G) r₀) :
    ‖deriv (fun r => Ψ (r, Φ (r, z))) ρ - deriv (fun r => Ψ (r, Φ (r, 0))) ρ‖
      ≤ ((k₁ * r₀ + k₂) * (k₆ + k₃ * (k₅ * r₀ + k₇)) + k₄ * k₅) * ‖z‖ := by
  have hzr : ‖z‖ ≤ r₀ := mem_closedBall_zero_iff.mp hz
  have hr₀ : (0 : ℝ) ≤ r₀ := le_trans (norm_nonneg z) hzr
  have hAnn : (0 : ℝ) ≤ k₁ * r₀ + k₂ := add_nonneg (mul_nonneg hk₁ hr₀) hk₂
  have hz0 : (0 : G) ∈ closedBall (0 : G) r₀ := mem_closedBall_self hr₀
  -- the two parameter derivatives
  have hd1 := hasDerivAt_comp_param (hΨ (Φ (ρ, z))) (hΦ z)
  have hd0 := hasDerivAt_comp_param (hΨ (Φ (ρ, 0))) (hΦ 0)
  rw [hd1.deriv, hd0.deriv]
  -- mean value bound on `‖Φ(ρ,z) − Φ(ρ,0)‖`
  have hφz : ‖Φ (ρ, z) - Φ (ρ, 0)‖ ≤ (k₁ * ‖z‖ + k₂) * ‖z‖ :=
    norm_sub_le_of_fderiv_estimates hφ h1 h2 hk₁ hz
  have hφz' : ‖Φ (ρ, z) - Φ (ρ, 0)‖ ≤ (k₁ * r₀ + k₂) * ‖z‖ := by
    refine hφz.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg z))
    have := mul_le_mul_of_nonneg_left hzr hk₁
    linarith
  -- bound on `‖∂Φ/∂ρ (z)‖`
  have hdρ : ‖parDeriv Φ ρ z‖ ≤ k₅ * r₀ + k₇ := by
    have htri := norm_add_le (parDeriv Φ ρ z - parDeriv Φ ρ 0) (parDeriv Φ ρ 0)
    rw [sub_add_cancel] at htri
    refine htri.trans (add_le_add ?_ h7)
    exact (h5 z hz).trans (mul_le_mul_of_nonneg_left hzr hk₅)
  -- the three-term decomposition of the book's proof
  have key : parDeriv Ψ ρ (Φ (ρ, z)) + spaceDeriv Ψ ρ (Φ (ρ, z)) (parDeriv Φ ρ z)
        - (parDeriv Ψ ρ (Φ (ρ, 0)) + spaceDeriv Ψ ρ (Φ (ρ, 0)) (parDeriv Φ ρ 0))
      = parDeriv Ψ ρ (Φ (ρ, z)) - parDeriv Ψ ρ (Φ (ρ, 0))
        + (spaceDeriv Ψ ρ (Φ (ρ, z)) - spaceDeriv Ψ ρ (Φ (ρ, 0))) (parDeriv Φ ρ z)
        + spaceDeriv Ψ ρ (Φ (ρ, 0)) (parDeriv Φ ρ z - parDeriv Φ ρ 0) := by
    simp only [sub_apply, map_sub]
    abel
  rw [key]
  have e1 : ‖parDeriv Ψ ρ (Φ (ρ, z)) - parDeriv Ψ ρ (Φ (ρ, 0))‖
      ≤ k₆ * ((k₁ * r₀ + k₂) * ‖z‖) :=
    (h6 z hz).trans (mul_le_mul_of_nonneg_left hφz' hk₆)
  have e2 : ‖(spaceDeriv Ψ ρ (Φ (ρ, z)) - spaceDeriv Ψ ρ (Φ (ρ, 0))) (parDeriv Φ ρ z)‖
      ≤ k₃ * ((k₁ * r₀ + k₂) * ‖z‖) * (k₅ * r₀ + k₇) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    exact mul_le_mul ((h3 z hz).trans (mul_le_mul_of_nonneg_left hφz' hk₃)) hdρ
      (norm_nonneg _) (mul_nonneg hk₃ (mul_nonneg hAnn (norm_nonneg z)))
  have e3 : ‖spaceDeriv Ψ ρ (Φ (ρ, 0)) (parDeriv Φ ρ z - parDeriv Φ ρ 0)‖
      ≤ k₄ * (k₅ * ‖z‖) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    exact mul_le_mul h4 (h5 z hz) (norm_nonneg _) hk₄
  calc ‖parDeriv Ψ ρ (Φ (ρ, z)) - parDeriv Ψ ρ (Φ (ρ, 0))
          + (spaceDeriv Ψ ρ (Φ (ρ, z)) - spaceDeriv Ψ ρ (Φ (ρ, 0))) (parDeriv Φ ρ z)
          + spaceDeriv Ψ ρ (Φ (ρ, 0)) (parDeriv Φ ρ z - parDeriv Φ ρ 0)‖
      ≤ ‖parDeriv Ψ ρ (Φ (ρ, z)) - parDeriv Ψ ρ (Φ (ρ, 0))‖
        + ‖(spaceDeriv Ψ ρ (Φ (ρ, z)) - spaceDeriv Ψ ρ (Φ (ρ, 0))) (parDeriv Φ ρ z)‖
        + ‖spaceDeriv Ψ ρ (Φ (ρ, 0)) (parDeriv Φ ρ z - parDeriv Φ ρ 0)‖ := norm_add₃_le
    _ ≤ k₆ * ((k₁ * r₀ + k₂) * ‖z‖) + k₃ * ((k₁ * r₀ + k₂) * ‖z‖) * (k₅ * r₀ + k₇)
          + k₄ * (k₅ * ‖z‖) := add_le_add (add_le_add e1 e2) e3
    _ = ((k₁ * r₀ + k₂) * (k₆ + k₃ * (k₅ * r₀ + k₇)) + k₄ * k₅) * ‖z‖ := by ring

end Parameter

/-! ## §13.7 Lemma 13.7.1 and the algebra of Lemma 9.6.15

Lemma 13.7.1 bounds the nonlinear remainder `N(Y) = F(Y) − F(0) − (dF)₀(Y)` of
the Floer operator by `C ‖Y‖_∞ ‖Y‖_{W^{1,p}}`.  The two norms make the statement
itself Sobolev; the single-norm form of the same argument — Taylor's inequality
with the remainder controlled by the Lipschitz constant of `dF` — is a statement
about normed spaces and is proved here.  The concluding algebraic manipulation
of Lemma 9.6.15, `a ≤ b + ca ⇒ a ≤ b/(1−c)`, is also recorded. -/

section Remainder

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Lemma 13.7.1** in its single-norm form.  If `‖df_x − df_0‖ ≤ K ‖x‖` on the
ball `B(0,r)` — which is the conclusion of Lemma 9.4.8 — then the nonlinear part
`N(Y) = f Y − f 0 − df_0 Y` of `f` satisfies `‖N(Y)‖ ≤ K ‖Y‖²`.

The book gets the sharper constant `K/2` by writing `N(Y) = ∫₀¹ (dN)_{σY}(Y) dσ`
and keeping the factor `σ`; the mean value inequality used here discards it.
The bilinear shape `‖Y‖ · ‖Y‖` is the point, and it is what the proof of Lemma
9.6.15 uses. -/
theorem norm_taylor_remainder_le {f : G → H} {r K : ℝ}
    (hf : ∀ x ∈ closedBall (0 : G) r, DifferentiableAt ℝ f x)
    (hK : ∀ x ∈ closedBall (0 : G) r, ‖fderiv ℝ f x - fderiv ℝ f 0‖ ≤ K * ‖x‖)
    (hK0 : 0 ≤ K) {Y : G} (hY : Y ∈ closedBall (0 : G) r) :
    ‖f Y - f 0 - fderiv ℝ f 0 Y‖ ≤ K * ‖Y‖ ^ 2 := by
  have hYr : ‖Y‖ ≤ r := mem_closedBall_zero_iff.mp hY
  have hsub : closedBall (0 : G) ‖Y‖ ⊆ closedBall (0 : G) r := closedBall_subset_closedBall hYr
  have hbound : ∀ x ∈ closedBall (0 : G) ‖Y‖, ‖fderiv ℝ f x - fderiv ℝ f 0‖ ≤ K * ‖Y‖ :=
    fun x hx => (hK x (hsub hx)).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hK0)
  have key : ‖f Y - f 0 - (fderiv ℝ f 0) (Y - 0)‖ ≤ K * ‖Y‖ * ‖Y - 0‖ :=
    (convex_closedBall (0 : G) ‖Y‖).norm_image_sub_le_of_norm_fderiv_le'
      (fun x hx => hf x (hsub hx)) hbound (mem_closedBall_self (norm_nonneg Y))
      (mem_closedBall_zero_iff.mpr le_rfl)
  rw [sub_zero] at key
  calc ‖f Y - f 0 - fderiv ℝ f 0 Y‖ ≤ K * ‖Y‖ * ‖Y‖ := key
    _ = K * ‖Y‖ ^ 2 := by ring

/-- **The last step of Lemma 9.6.15.**  An estimate of the shape `a ≤ b + c·a`
with `c < 1` rearranges to `a ≤ b / (1 − c)`.

In the book `a = ‖Y_n‖_{W^{1,p}}`, `c = C₁₀ ‖Y_n‖_∞` and
`b = (C₁+C₃)‖χ_n‖_{W^{1,p}} + C₈‖Y_n‖_∞ + C₉‖F(0)‖_{L^p}`, giving the displayed
form of the lemma. -/
theorem le_div_one_sub_of_le_add_mul {a b c : ℝ} (hc : c < 1) (h : a ≤ b + c * a) :
    a ≤ b / (1 - c) := by
  have h1 : (0 : ℝ) < 1 - c := by linarith
  rw [le_div_iff₀ h1]
  have h2 : a * (1 - c) = a - c * a := by ring
  rw [h2]
  linarith

end Remainder

/-! ## §13.8 Lemma 13.8.2, in its abstract form

§13.8 revisits the two lemmas when the Hamiltonian and the almost complex
structure themselves depend on the gluing parameter.  Lemma 13.8.1 and Lemmas
11.4.5 and 11.4.7 are `L^p` estimates on the Floer operator and are not
statable.  Lemma 13.8.2 — the final composition estimate
`‖χψφ(Z) − χψφ(0)‖ ≤ k₂ ‖Z‖` — has an abstract form: a mean value inequality on
the segment joining the two points, composed with a Lipschitz bound on the inner
map.  That is what is proved here. -/

section Segment

variable {G H K : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The mean value inequality along the segment `[b,a]`, the step
`‖χ(a) − χ(b)‖ ≤ sup_{r∈[0,1]} ‖(dχ)_{ra+(1−r)b}‖ ‖a − b‖` of the proof of
Lemma 13.8.2. -/
theorem norm_comp_sub_le_of_fderiv_le {χ : H → K} {a b : H} {Λ : ℝ}
    (hχ : ∀ x ∈ segment ℝ b a, DifferentiableAt ℝ χ x)
    (hΛ : ∀ x ∈ segment ℝ b a, ‖fderiv ℝ χ x‖ ≤ Λ) :
    ‖χ a - χ b‖ ≤ Λ * ‖a - b‖ :=
  (convex_segment b a).norm_image_sub_le_of_norm_fderiv_le hχ hΛ
    (left_mem_segment ℝ b a) (right_mem_segment ℝ b a)

omit [NormedSpace ℝ G] in
/-- **Lemma 13.8.2, abstract form.**  If the inner map `ψ` moves `0` to `ψ z` by
at most `M ‖z‖`, and the outer map `χ` has differential bounded by `Λ` on the
segment joining `ψ 0` to `ψ z`, then `‖χ(ψ z) − χ(ψ 0)‖ ≤ Λ M ‖z‖`.

In §13.8, `ψ` is `(Id, V_ρ) ∘ i_ρ`, whose Lipschitz bound at `0` is Lemma
13.8.1, and `χ` is `p_ρ`. -/
theorem norm_comp₂_sub_le_of_lipschitz {ψ : G → H} {χ : H → K} {M Λ : ℝ} {z : G}
    (hM : ‖ψ z - ψ 0‖ ≤ M * ‖z‖)
    (hχ : ∀ x ∈ segment ℝ (ψ 0) (ψ z), DifferentiableAt ℝ χ x)
    (hΛ : ∀ x ∈ segment ℝ (ψ 0) (ψ z), ‖fderiv ℝ χ x‖ ≤ Λ) (hΛ0 : 0 ≤ Λ) :
    ‖χ (ψ z) - χ (ψ 0)‖ ≤ Λ * M * ‖z‖ := by
  refine (norm_comp_sub_le_of_fderiv_le hχ hΛ).trans ?_
  calc Λ * ‖ψ z - ψ 0‖ ≤ Λ * (M * ‖z‖) := mul_le_mul_of_nonneg_left hM hΛ0
    _ = Λ * M * ‖z‖ := by ring

end Segment

end Chapter13
end MorseFloer
