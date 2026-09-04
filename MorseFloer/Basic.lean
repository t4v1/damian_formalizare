import Mathlib

/-!
# Foundations: second differentials, Hessians, critical points

This file sets up the vocabulary shared by the whole formalization of
Audin–Damian, *Théorie de Morse et homologie de Floer*.

The book works on manifolds throughout, but every second-order notion it uses
(the Hessian, nondegeneracy, the index) is *defined in a chart* and then shown
to be chart-independent at a critical point (Remark 1.1.2 and Exercise 1).  We
follow exactly that route:

* `MorseFloer.sndFDeriv f x` is the second differential of `f` at `x`, read as a
  continuous bilinear map on a normed space;
* `MorseFloer.sndFDeriv_comp` is the transformation rule under a change of
  charts, and `sndFDeriv_comp_of_critical` is its tensorial specialisation at a
  critical point — the reason the Hessian of a function on a manifold makes
  sense there and nowhere else;
* `MorseFloer.hessian I f x` is the Hessian of `f : M → ℝ` at `x`, defined as the
  second differential of `f` read in the preferred extended chart at `x`;
* `MorseFloer.IsCriticalPoint`, `IsNondegenerate`, `IsMorseFunction` and
  `morseIndex` are the definitions of §1.1 and §1.3.

The index is `QuadraticMap.sigNeg` of the Hessian quadratic form: the largest
dimension of a subspace on which the form is negative definite.  Mathlib already
proves this is an invariant of the equivalence class of the form
(`QuadraticMap.Equivalent.sigNeg_eq`), which is what makes the index of a
critical point well defined.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap Filter Topology

namespace MorseFloer

/-! ## The second differential on a normed space -/

section SndFDeriv

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The second differential of `f` at `x`, as a continuous bilinear map.

This is the object the book calls `(d²f)ₓ`.  On a general point it depends on the
chart used; see `sndFDeriv_comp` for how it transforms and
`sndFDeriv_comp_of_critical` for the critical-point case where it does not. -/
noncomputable def sndFDeriv (f : E → F) (x : E) : E →L[ℝ] E →L[ℝ] F :=
  fderiv ℝ (fderiv ℝ f) x

theorem sndFDeriv_def (f : E → F) (x : E) :
    sndFDeriv f x = fderiv ℝ (fderiv ℝ f) x := rfl

/-- The second differential is symmetric on a `C²` function: this is the
computation `X·(Y·f) − Y·(X·f) = [X,Y]·f` of §1.1.a, in a chart. -/
theorem sndFDeriv_symm {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    sndFDeriv f x v w = sndFDeriv f x w v :=
  hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w

/-- **The transformation rule for second differentials** (Exercise 1, p. 17).

For a change of chart `φ` and a function `f`,
`d²(f∘φ)ₓ(h,k) = d²f_{φ(x)}(dφ h, dφ k) + df_{φ(x)}(d²φₓ(h,k))`.

The first term is tensorial; the second — the correction term — lies in the
image of `df`, which is why the second differential is *not* chart-independent
in general. -/
theorem sndFDeriv_comp {f : F → G} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x) (h k : E) :
    sndFDeriv (f ∘ φ) x h k
      = sndFDeriv f (φ x) (fderiv ℝ φ x h) (fderiv ℝ φ x k)
        + fderiv ℝ f (φ x) (sndFDeriv φ x h k) := by
  -- Near `x`, both `f` and `φ` are `C²`, so the chain rule applies pointwise.
  have hφ' : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ y := hφ.eventually (by simp)
  have hfφ : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f (φ y) := by
    have hc : ContinuousAt φ x := hφ.continuousAt
    exact hc.eventually (hf.eventually (by simp))
  -- Hence `fderiv (f ∘ φ)` agrees near `x` with `y ↦ (fderiv f (φ y)).comp (fderiv φ y)`.
  have key : fderiv ℝ (f ∘ φ) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y) := by
    filter_upwards [hφ', hfφ] with y hy hfy
    exact fderiv_comp y (hfy.differentiableAt (by norm_num)) (hy.differentiableAt (by norm_num))
  -- Differentiate that identity at `x`.
  have hc : HasFDerivAt (fun y => fderiv ℝ f (φ y))
      ((sndFDeriv f (φ x)).comp (fderiv ℝ φ x)) x := by
    have h1 : HasFDerivAt (fderiv ℝ f) (sndFDeriv f (φ x)) (φ x) :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
    exact h1.comp x (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (fun y => fderiv ℝ φ y) (sndFDeriv φ x) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hcomp := hc.clm_comp hd
  have heq : sndFDeriv (f ∘ φ) x
      = fderiv ℝ (fun y => (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y)) x := by
    rw [sndFDeriv_def]; exact key.fderiv_eq
  rw [heq, HasFDerivAt.fderiv hcomp]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

/-- **Tensoriality at a critical point.**  If `df` vanishes at `φ x` the
correction term of `sndFDeriv_comp` disappears, so the second differential
transforms as an honest bilinear form: this is what makes the Hessian of a
function on a manifold well defined *at its critical points* (§1.1.a). -/
theorem sndFDeriv_comp_of_critical {f : F → G} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hcrit : fderiv ℝ f (φ x) = 0) (h k : E) :
    sndFDeriv (f ∘ φ) x h k
      = sndFDeriv f (φ x) (fderiv ℝ φ x h) (fderiv ℝ φ x k) := by
  rw [sndFDeriv_comp hf hφ h k, hcrit]
  simp

end SndFDeriv

/-! ## Nondegeneracy and the index of a bilinear form -/

section Bilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `LinearMap.BilinForm` underlying a continuous bilinear form. -/
noncomputable def toBilinForm (B : E →L[ℝ] E →L[ℝ] ℝ) : LinearMap.BilinForm ℝ E where
  toFun v := (B v).toLinearMap
  map_add' v w := by ext u; simp
  map_smul' c v := by ext u; simp

@[simp]
theorem toBilinForm_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    toBilinForm B v w = B v w := rfl

/-- A bilinear form is **nondegenerate** when no nonzero vector is orthogonal to
everything.  For the Hessian at a critical point this is the book's condition
defining a *nondegenerate critical point* (§1.1.a). -/
def IsNondegenerate (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ v : E, (∀ w : E, B v w = 0) → v = 0

theorem isNondegenerate_iff_injective (B : E →L[ℝ] E →L[ℝ] ℝ) :
    IsNondegenerate B ↔ Function.Injective B := by
  constructor
  · intro h u v huv
    have : u - v = 0 := by
      refine h _ fun w => ?_
      have : B u w = B v w := by rw [huv]
      simp [ContinuousLinearMap.map_sub, this]
    exact sub_eq_zero.mp this
  · intro h v hv
    have : B v = 0 := by ext w; simpa using hv w
    have := h (by simpa using this : B v = B 0)
    exact this

/-- The quadratic form `v ↦ B v v` attached to a continuous bilinear form. -/
noncomputable def toQuadraticForm (B : E →L[ℝ] E →L[ℝ] ℝ) : QuadraticForm ℝ E :=
  (toBilinForm B).toQuadraticMap

@[simp]
theorem toQuadraticForm_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (v : E) :
    toQuadraticForm B v = B v v := rfl

/-- The **index** of a bilinear form: the largest dimension of a subspace on
which the associated quadratic form is negative definite.

For the Hessian at a nondegenerate critical point this is the integer `i` of the
Morse lemma (Theorem 1.3.1); `(n − i, i)` is the signature of `d²f`. -/
noncomputable def index (B : E →L[ℝ] E →L[ℝ] ℝ) : ℕ :=
  sigNeg (toQuadraticForm B)

/-- The index is an invariant of the equivalence class of the form, so it does
not depend on the coordinates used to compute it. -/
theorem index_eq_of_equivalent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (C : F →L[ℝ] F →L[ℝ] ℝ)
    (h : (toQuadraticForm B).Equivalent (toQuadraticForm C)) :
    index B = index C :=
  h.sigNeg_eq

end Bilinear

/-! ## Critical points, the Hessian, and Morse functions on a manifold -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- `x` is a **critical point** of `f : M → ℝ` when the differential of `f`
vanishes there (§1.1.a). -/
def IsCriticalPoint (f : M → ℝ) (x : M) : Prop :=
  mfderiv I 𝓘(ℝ) f x = 0

/-- The **Hessian** of `f : M → ℝ` at `x`, computed in the preferred extended
chart at `x`.

At a critical point this is chart-independent up to the linear change of
variables given by the transition map — that is the content of
`sndFDeriv_comp_of_critical` — so the notions of nondegeneracy and of index
extracted from it below are intrinsic. -/
noncomputable def hessian (f : M → ℝ) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  sndFDeriv (writtenInExtChartAt I 𝓘(ℝ) x f) (extChartAt I x x)

/-- A **nondegenerate critical point**: the differential vanishes and the
Hessian is a nondegenerate bilinear form (§1.1.a). -/
structure IsNondegenerateCriticalPoint (f : M → ℝ) (x : M) : Prop where
  isCritical : IsCriticalPoint I f x
  nondegenerate : IsNondegenerate (hessian I f x)

/-- A **Morse function** is one all of whose critical points are nondegenerate
(§1.1.a). -/
def IsMorseFunction (f : M → ℝ) : Prop :=
  ∀ x : M, IsCriticalPoint I f x → IsNondegenerate (hessian I f x)

/-- The **index** of a critical point: the number of negative squares in the
Morse lemma's normal form (§1.3.a). -/
noncomputable def morseIndex (f : M → ℝ) (x : M) : ℕ :=
  index (hessian I f x)

theorem IsMorseFunction.nondegenerateCriticalPoint {f : M → ℝ}
    (hf : IsMorseFunction I f) {x : M} (hx : IsCriticalPoint I f x) :
    IsNondegenerateCriticalPoint I f x :=
  ⟨hx, hf x hx⟩

end Manifold

end MorseFloer
