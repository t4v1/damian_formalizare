import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Homotopy.Contractible

/-!
# The space of calibrated complex structures is contractible (Proposition 5.5.4)

Let `ω` be a bilinear form on a finite-dimensional real normed space `E`.  An
endomorphism `J` is *calibrated* by `ω` when `J² = −1`, `J` preserves `ω`, and
`ω(v, Jv) > 0` for `v ≠ 0`.  This file proves that, as soon as one calibrated
`j` exists, the calibrated endomorphisms form a contractible subspace of
`E →L[ℝ] E`.  It is `MorseFloer.Calibrated.contractibleSpace`, which Chapter 5
restates as Proposition 5.5.4.

## The route: a Cayley transform

Fix the calibrated `j`.  The *Cayley transform* `Ψ J = (J + j)⁻¹ (J − j)` sends a
calibrated `J` into the set `B` of endomorphisms `S` which

1. anticommute with `j`,
2. are symmetric for the inner product `g(v, w) = ω(v, jw)`, and
3. strictly contract its norm: `g(Su, Su) < g(u, u)` for `u ≠ 0`,

and `Φ S = j (1 + S) (1 − S)⁻¹` sends `B` back to calibrated endomorphisms, with
`Φ (Ψ J) = J` and `Φ 0 = j`.  The set `B` is star-shaped about `0` under
`S ↦ c • S` for `c ∈ [0, 1]`, so `H (t, J) = Φ ((1 − t) • Ψ J)` is a homotopy from
the identity to the constant map `j`.

Everything is checked pointwise, after writing a vector as `(1 − S) a`: then
`Φ S ((1 − S) a) = j ((1 + S) a) = (1 − S) (j a)`, and the three calibration
conditions for `Φ S` become the three conditions defining `B`.  Only the
bilinearity of `ω` is used, not its alternation or nondegeneracy.  The inverses
are `Ring.inverse` in the Banach algebra `E →L[ℝ] E`, continuous at units by
`NormedRing.inverse_continuousAt`; an injective endomorphism of `E` is a unit
because `E` is finite-dimensional.
-/

open Set Function Topology
open LinearMap (BilinForm)

namespace MorseFloer
namespace Calibrated

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An injective endomorphism of a finite-dimensional space is a unit of `E →L[ℝ] E`. -/
theorem isUnit_of_injective {f : E →L[ℝ] E} (hf : Injective f) : IsUnit f := by
  have hs : Surjective (f : E →ₗ[ℝ] E) := LinearMap.injective_iff_surjective.mp hf
  let e := LinearEquiv.ofBijective (f : E →ₗ[ℝ] E) ⟨hf, hs⟩
  have he : ∀ x, e x = f x := fun x => LinearEquiv.ofBijective_apply _ x
  refine ⟨⟨f, LinearMap.toContinuousLinearMap (e.symm : E →ₗ[ℝ] E), ?_, ?_⟩, rfl⟩
  · ext v
    have h := e.apply_symm_apply v
    rw [he] at h
    exact h
  · ext v
    have h := e.symm_apply_apply v
    rw [he] at h
    exact h

omit [FiniteDimensional ℝ E] in
theorem mul_inverse_apply {f : E →L[ℝ] E} (hf : IsUnit f) (v : E) :
    f (Ring.inverse f v) = v := by
  rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel f hf,
    one_apply_eq_self]

omit [FiniteDimensional ℝ E] in
theorem inverse_mul_apply {f : E →L[ℝ] E} (hf : IsUnit f) (v : E) :
    Ring.inverse f (f v) = v := by
  rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel f hf,
    one_apply_eq_self]

omit [FiniteDimensional ℝ E] in
theorem injective_of_isUnit {f : E →L[ℝ] E} (hf : IsUnit f) : Injective f := fun x y h => by
  rw [← inverse_mul_apply hf x, h, inverse_mul_apply hf y]

omit [FiniteDimensional ℝ E] in
theorem one_sub_apply (S : E →L[ℝ] E) (a : E) : (1 - S) a = a - S a := by
  rw [_root_.sub_apply, one_apply_eq_self]

omit [FiniteDimensional ℝ E] in
theorem one_add_apply (S : E →L[ℝ] E) (a : E) : (1 + S) a = a + S a := by
  rw [_root_.add_apply, one_apply_eq_self]

variable (ω : BilinForm ℝ E) (j : E →L[ℝ] E)

/-- `J` is calibrated by `ω`: `J² = −1`, `J` preserves `ω`, and `ω(v, Jv) > 0` off `0`. -/
def IsCal (J : E →L[ℝ] E) : Prop :=
  (∀ v, J (J v) = -v) ∧ (∀ v w, ω (J v) (J w) = ω v w) ∧ ∀ v, v ≠ 0 → 0 < ω v (J v)

/-- The target of the Cayley transform: endomorphisms anticommuting with `j`, symmetric
for `g(v, w) = ω(v, jw)`, and strictly contracting for `g`. -/
def InB (S : E →L[ℝ] E) : Prop :=
  (∀ v, j (S v) = -S (j v)) ∧ (∀ v w, ω (S v) (j w) = ω v (j (S w))) ∧
    ∀ u, u ≠ 0 → ω (S u) (j (S u)) < ω u (j u)

/-- The inverse Cayley transform `S ↦ j (1 + S) (1 − S)⁻¹`. -/
noncomputable def Φ (S : E →L[ℝ] E) : E →L[ℝ] E := j * (1 + S) * Ring.inverse (1 - S)

/-- The Cayley transform `J ↦ (J + j)⁻¹ (J − j)`. -/
noncomputable def Ψ (J : E →L[ℝ] E) : E →L[ℝ] E := Ring.inverse (J + j) * (J - j)

variable {ω j}

omit [FiniteDimensional ℝ E] in
theorem Φ_zero : Φ j 0 = j := by
  simp only [Φ, add_zero, sub_zero, Ring.inverse_one, mul_one]

omit [FiniteDimensional ℝ E] in
/-- On a vector written as `(1 − S) a`, the inverse Cayley transform is `j (1 + S) a`. -/
theorem Φ_apply_one_sub {S : E →L[ℝ] E} (hU : IsUnit (1 - S)) (a : E) :
    Φ j S ((1 - S) a) = j ((1 + S) a) := by
  simp only [Φ, mul_apply_eq_comp, inverse_mul_apply hU]

/-! ## From `B` to calibrated endomorphisms -/

section Forward

variable {S : E →L[ℝ] E}

/-- An element of `B` has no fixed vector, so `1 − S` is invertible. -/
theorem isUnit_one_sub (hS : InB ω j S) : IsUnit (1 - S) := by
  refine isUnit_of_injective ((injective_iff_map_eq_zero (1 - S)).mpr fun a ha => ?_)
  rw [one_sub_apply, sub_eq_zero] at ha
  by_contra hne
  have h2 := hS.2.2 a hne
  rw [← ha] at h2
  exact lt_irrefl _ h2

omit [FiniteDimensional ℝ E] in
/-- An element of `B` is antisymmetric for `ω`. -/
theorem antisymm (hj : IsCal ω j) (hS : InB ω j S) (a b : E) :
    ω a (S b) + ω (S a) b = 0 := by
  have hb : b = j (-(j b)) := by rw [map_neg, hj.1, neg_neg]
  have h1 : ω (S a) b = ω a (j (S (-(j b)))) := by
    conv_lhs => rw [hb]
    exact hS.2.1 a (-(j b))
  have h2 : j (S (-(j b))) = -(S b) := by
    rw [hS.1, ← hb]
  rw [h1, h2, map_neg, add_neg_cancel]

omit [FiniteDimensional ℝ E] in
theorem j_one_add (hS : InB ω j S) (a : E) : j ((1 + S) a) = (1 - S) (j a) := by
  rw [one_add_apply, one_sub_apply, map_add, hS.1, sub_eq_add_neg]

/-- **The inverse Cayley transform lands in the calibrated endomorphisms.** -/
theorem isCal_Φ (hj : IsCal ω j) (hS : InB ω j S) : IsCal ω (Φ j S) := by
  have hU := isUnit_one_sub hS
  have hv : ∀ v, ∃ a, v = (1 - S) a := fun v =>
    ⟨Ring.inverse (1 - S) v, (mul_inverse_apply hU v).symm⟩
  refine ⟨fun v => ?_, fun v w => ?_, fun v hv0 => ?_⟩
  · obtain ⟨a, rfl⟩ := hv v
    rw [Φ_apply_one_sub hU, j_one_add hS, Φ_apply_one_sub hU, j_one_add hS, hj.1, map_neg]
  · obtain ⟨a, rfl⟩ := hv v
    obtain ⟨b, rfl⟩ := hv w
    rw [Φ_apply_one_sub hU, Φ_apply_one_sub hU, hj.2.1]
    have h := antisymm hj hS a b
    simp only [one_add_apply, one_sub_apply, map_add, map_sub, LinearMap.add_apply,
      LinearMap.sub_apply]
    linarith
  · obtain ⟨a, rfl⟩ := hv v
    have ha : a ≠ 0 := by
      rintro rfl
      exact hv0 (map_zero _)
    rw [Φ_apply_one_sub hU]
    have h1 := hS.2.2 a ha
    have h2 := hS.2.1 a a
    simp only [one_add_apply, one_sub_apply, map_add, map_sub,
      LinearMap.sub_apply]
    linarith

omit [FiniteDimensional ℝ E] in
/-- `B` is star-shaped about `0`. -/
theorem inB_smul (hj : IsCal ω j) (hS : InB ω j S) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    InB ω j (c • S) := by
  refine ⟨fun v => ?_, fun v w => ?_, fun u hu => ?_⟩
  · simp only [_root_.smul_apply, map_smul, hS.1 v, smul_neg]
  · simp only [_root_.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hS.2.1 v w]
  · simp only [_root_.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h1 := hS.2.2 u hu
    have h0 : 0 ≤ ω (S u) (j (S u)) := by
      by_cases h : S u = 0
      · rw [h, map_zero, LinearMap.zero_apply]
      · exact (hj.2.2 _ h).le
    have hc2 : c * c ≤ 1 := by nlinarith
    nlinarith

end Forward

/-! ## From calibrated endomorphisms to `B` -/

section Backward

variable {J : E →L[ℝ] E}

/-- For calibrated `J` and `j`, `J + j` is invertible. -/
theorem isUnit_add (hj : IsCal ω j) (hJ : IsCal ω J) : IsUnit (J + j) := by
  refine isUnit_of_injective ((injective_iff_map_eq_zero (J + j)).mpr fun v hv => ?_)
  rw [_root_.add_apply, add_eq_zero_iff_eq_neg] at hv
  by_contra hne
  have h1 := hJ.2.2 v hne
  have h2 := hj.2.2 v hne
  rw [hv, map_neg] at h1
  linarith

/-- The defining equation of the Cayley transform, `(J + j) (Ψ J v) = (J − j) v`. -/
theorem add_apply_Ψ (hj : IsCal ω j) (hJ : IsCal ω J) (v : E) :
    (J + j) (Ψ j J v) = J v - j v := by
  rw [Ψ, mul_apply_eq_comp, mul_inverse_apply (isUnit_add hj hJ),
    _root_.sub_apply]

/-- `J (1 − S) = j (1 + S)` for `S = Ψ J`. -/
theorem apply_one_sub_Ψ (hj : IsCal ω j) (hJ : IsCal ω J) (a : E) :
    J ((1 - Ψ j J) a) = j ((1 + Ψ j J) a) := by
  have h := add_apply_Ψ hj hJ a
  rw [_root_.add_apply, eq_sub_iff_add_eq] at h
  rw [one_sub_apply, one_add_apply, map_sub, map_add, ← h]
  abel

theorem isUnit_one_sub_Ψ (hj : IsCal ω j) (hJ : IsCal ω J) : IsUnit (1 - Ψ j J) := by
  refine isUnit_of_injective ((injective_iff_map_eq_zero _).mpr fun a ha => ?_)
  have hR := apply_one_sub_Ψ hj hJ a
  have hSa : Ψ j J a = a := by
    rw [one_sub_apply, sub_eq_zero] at ha
    exact ha.symm
  rw [ha, map_zero, one_add_apply, hSa] at hR
  have h2 : a + a = 0 := by
    have h := congrArg j hR
    rw [map_zero, hj.1, zero_eq_neg] at h
    exact h
  have h3 : (2 : ℝ) • a = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

/-- **The Cayley transform is inverted by `Φ`.** -/
theorem Φ_Ψ (hj : IsCal ω j) (hJ : IsCal ω J) : Φ j (Ψ j J) = J := by
  have hU := isUnit_one_sub_Ψ hj hJ
  ext v
  obtain ⟨a, rfl⟩ : ∃ a, v = (1 - Ψ j J) a :=
    ⟨Ring.inverse (1 - Ψ j J) v, (mul_inverse_apply hU v).symm⟩
  rw [Φ_apply_one_sub hU, apply_one_sub_Ψ hj hJ]

/-- **The Cayley transform lands in `B`.** -/
theorem Ψ_inB (hj : IsCal ω j) (hJ : IsCal ω J) : InB ω j (Ψ j J) := by
  have hU := isUnit_add hj hJ
  have hUinj : Injective (J + j) := injective_of_isUnit hU
  have hB1 : ∀ v, j (Ψ j J v) = -Ψ j J (j v) := fun v => by
    apply hUinj
    have e1 : (J + j) (j (Ψ j J v)) = J ((J + j) (Ψ j J v)) := by
      rw [_root_.add_apply, _root_.add_apply, map_add, hj.1, hJ.1,
        add_comm]
    rw [e1, add_apply_Ψ hj hJ v, map_neg, add_apply_Ψ hj hJ (j v), map_sub, hJ.1, hj.1]
    abel
  have hanti : ∀ a b, ω a (Ψ j J b) + ω (Ψ j J a) b = 0 := fun a b => by
    have h := hJ.2.1 ((1 - Ψ j J) a) ((1 - Ψ j J) b)
    rw [apply_one_sub_Ψ hj hJ, apply_one_sub_Ψ hj hJ, hj.2.1] at h
    simp only [one_add_apply, one_sub_apply, map_add, map_sub, LinearMap.add_apply,
      LinearMap.sub_apply] at h
    linarith
  have hB2 : ∀ v w, ω (Ψ j J v) (j w) = ω v (j (Ψ j J w)) := fun v w => by
    have h := hanti v (j w)
    have h' : Ψ j J (j w) = -(j (Ψ j J w)) := by rw [hB1 w, neg_neg]
    rw [h', map_neg] at h
    linarith
  refine ⟨hB1, hB2, fun u hu => ?_⟩
  have hv : (1 - Ψ j J) u ≠ 0 := fun h0 =>
    hu ((injective_iff_map_eq_zero _).mp (injective_of_isUnit (isUnit_one_sub_Ψ hj hJ)) u h0)
  have h := hJ.2.2 _ hv
  rw [apply_one_sub_Ψ hj hJ] at h
  have h2 := hB2 u u
  simp only [one_add_apply, one_sub_apply, map_add, map_sub,
    LinearMap.sub_apply] at h
  linarith

end Backward

/-! ## Continuity and the contraction -/

theorem continuousAt_Ψ (hj : IsCal ω j) {J : E →L[ℝ] E} (hJ : IsCal ω J) :
    ContinuousAt (Ψ j) J := by
  obtain ⟨u, hu⟩ := isUnit_add hj hJ
  have h1 : ContinuousAt (fun K : E →L[ℝ] E => Ring.inverse (K + j)) J :=
    (NormedRing.inverse_continuousAt u).comp_of_eq
      (continuous_id.add continuous_const).continuousAt hu.symm
  exact h1.mul (continuous_id.sub continuous_const).continuousAt

theorem continuousAt_Φ {S : E →L[ℝ] E} (hS : InB ω j S) : ContinuousAt (Φ j) S := by
  obtain ⟨u, hu⟩ := isUnit_one_sub hS
  have h1 : ContinuousAt (fun K : E →L[ℝ] E => Ring.inverse (1 - K)) S :=
    (NormedRing.inverse_continuousAt u).comp_of_eq
      (continuous_const.sub continuous_id).continuousAt hu.symm
  exact (continuousAt_const.mul (continuous_const.add continuous_id).continuousAt).mul h1

/-- **Proposition 5.5.4.**  If some `j` is calibrated by `ω`, the space of endomorphisms
calibrated by `ω` is contractible.  The predicate `P` is any predicate equivalent to
calibration, so that the statement applies verbatim to `IsCalibrated` of Chapter 5.

The contraction is `(t, J) ↦ Φ ((1 − t) • Ψ J)`, where `Ψ` is the Cayley transform
based at `j` and `Φ` its inverse. -/
theorem contractibleSpace (ω : BilinForm ℝ E) (P : (E →L[ℝ] E) → Prop)
    (hP : ∀ J, P J ↔ (∀ v, J (J v) = -v) ∧ (∀ v w, ω (J v) (J w) = ω v w) ∧
      ∀ v, v ≠ 0 → 0 < ω v (J v))
    (j : E →L[ℝ] E) (hj : P j) :
    ContractibleSpace {J : E →L[ℝ] E // P J} := by
  have hjc : IsCal ω j := (hP j).mp hj
  have hcal : ∀ J : {J : E →L[ℝ] E // P J}, IsCal ω J.1 := fun J => (hP J.1).mp J.2
  let H : unitInterval × {J : E →L[ℝ] E // P J} → E →L[ℝ] E :=
    fun p => Φ j (((1 : ℝ) - p.1) • Ψ j p.2.1)
  have hmemB : ∀ p : unitInterval × {J : E →L[ℝ] E // P J},
      InB ω j (((1 : ℝ) - p.1) • Ψ j p.2.1) := fun p =>
    inB_smul hjc (Ψ_inB hjc (hcal p.2)) (sub_nonneg.mpr p.1.2.2) (sub_le_self _ p.1.2.1)
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun p =>
    (continuousAt_Φ (hmemB p)).comp_of_eq
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousAt.smul
        ((continuousAt_Ψ hjc (hcal p.2)).comp_of_eq
          (continuous_subtype_val.comp continuous_snd).continuousAt rfl)) rfl
  have hHP : ∀ p, P (H p) := fun p => (hP _).mpr (isCal_Φ hjc (hmemB p))
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨⟨j, hj⟩, ⟨{ toFun := fun p => ⟨H p, hHP p⟩
                     continuous_toFun := hH.subtype_mk hHP
                     map_zero_left := fun J => Subtype.ext (by
                       simp [H, Φ_Ψ hjc (hcal J)])
                     map_one_left := fun J => Subtype.ext (by
                       simp [H, Φ_zero]) }⟩⟩

end Calibrated
end MorseFloer
