import MorseFloer.Basic

/-!
# Chapter 5: What one needs to know about symplectic geometry

Formalization of Chapter 5 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 111–130).  This is the first chapter of Part II
and is a survey chapter: it collects the symplectic background used by the rest
of the book.

The chapter has six sections:

* **§5.1** symplectic vector spaces: nondegenerate alternating bilinear forms,
  symplectic bases (Proposition 5.1.1), and the standard example
  `ℝⁿ × ℝⁿ` (Example 5.1.2);
* **§5.2** symplectic manifolds: closed nondegenerate `2`-forms
  (Definition 5.2.2) and the reason closedness rather than exactness is the
  right condition (Proposition 5.2.1);
* **§5.3** examples: `ℝ²ⁿ`, cotangent bundles with the Liouville form, surfaces,
  the sphere, complex projective space (Proposition 5.3.1), and Darboux's
  theorem (Theorem 5.3.2);
* **§5.4** Hamiltonian vector fields and Hamiltonian systems, Hamilton's
  equations, quadratic Hamiltonians (Example 5.4.3), nondegenerate periodic
  orbits (Definition 5.4.4) and Proposition 5.4.5;
* **§5.5** complex structures calibrated by a symplectic form, their existence
  (Lemma 5.5.3), the contractibility of the space of such (Proposition 5.5.4,
  Corollary 5.5.5, Proposition 5.5.6), the description of its tangent space
  (Proposition 5.5.7), and the relation `X_H = J grad H`;
* **§5.6** the symplectic group: the relations between `Sp`, `O`, `GL(n, ℂ)`
  and `U(n)` (Proposition 5.6.2), the eigenvalues (Propositions 5.6.3, 5.6.4)
  and eigenspaces (Proposition 5.6.6) of a symplectic matrix, and the polar
  decomposition (Proposition 5.6.9, Corollary 5.6.10).

## Status

Mathlib has no differential forms on manifolds (no bundle of alternating forms
on the tangent bundle and no exterior derivative), so **there is no way to state
"`ω` is a closed nondegenerate `2`-form on a manifold `W`"**.  Following the
convention of this project (see `MorseFloer.Basic`), §5.2–§5.4 are therefore
developed in the *local model*: a `2`-form on a normed space `E` is a map
`E → BilinForm ℝ E` taking alternating values, and closedness is written out as
the vanishing of the cyclic sum of directional derivatives.  This is faithful to
what the book actually computes with, and it is what Darboux's theorem and the
Hamiltonian formalism reduce to in a chart.

Proved here:

* the basic theory of a symplectic form on a vector space: skewness, the
  `ω`-orthogonal of a subspace, `finrank W + finrank Wᗮ = finrank V`,
  `(Wᗮ)ᗮ = W`, isotropic/coisotropic/Lagrangian/symplectic subspaces and their
  dimension inequalities;
* **Proposition 5.1.1**, the existence of a symplectic basis of a
  finite-dimensional symplectic vector space, by induction on the dimension,
  together with its corollary that the dimension is even;
* **Example 5.1.2**: the standard form on `(l ⊕ l) → ℝ` (the matrix `-J`) is
  symplectic and the standard basis is a symplectic basis for it;
* the defining property of the Hamiltonian vector field, its uniqueness, the
  equivalence "`X_H` vanishes at `x`" ⟺ "`x` is a critical point of `H`", the
  conservation of `H` along `X_H`, and the explicit formula
  `X_H = J · grad H` in the standard model (Hamilton's equations);
* **Example 5.4.3**: the flow `exp(tA)` of a quadratic Hamiltonian is symplectic
  (as `exp A ∈ Sp` whenever `AᵀJ + JA = 0`);
* the elementary theory of calibrated complex structures: the metric
  `g(v,w) = ω(v, Jw)` is symmetric and positive definite, `J` is a `g`-isometry
  and `g`-antisymmetric, and the standard `J₀` on `(l ⊕ l) → ℝ` is calibrated
  by the standard form with `g` the Euclidean product (this is
  "`ℝ²ⁿ = ℂⁿ`, `J₀ =` multiplication by `i`");
* the antisymmetry of the operator `A` of Lemma 5.5.3, and the symmetry
  computation behind Proposition 5.5.7;
* **Proposition 5.6.2** in its matrix form: any two of "symplectic",
  "orthogonal", "complex linear" imply the third;
* the characterisation of `Matrix.symplecticGroup` as the isometry group of the
  standard form, **Proposition 5.6.3** in the form `Aᵀ J = J A⁻¹`, and
  **Corollary 5.6.10** (`det A = 1`, which is Mathlib's
  `SymplecticGroup.det_eq_one`).

Assumed (`sorry`):

* **Theorem 5.3.2** (Darboux), stated in the local model;
* **Proposition 5.5.4** / **Corollary 5.5.5**, the contractibility of the space
  of calibrated complex structures, and the existence part of **Lemma 5.5.3**
  (Mathlib has no polar decomposition of a linear automorphism of a Euclidean
  space in a usable form);
* **Proposition 5.4.5** (a critical point nondegenerate as a periodic orbit is
  nondegenerate as a critical point), in its linear-model form; the missing
  ingredient is `exp A · v = v` for `A · v = 0`, i.e. a `mulVec` version of the
  matrix exponential series;
* **Proposition 5.6.4** (the characteristic polynomial of a symplectic matrix is
  symmetric) and **Proposition 5.6.6** (`ω(Eλ, Eμ) = 0` for `λμ ≠ 1`) beyond the
  case of genuine eigenvectors, which is proved;
* **Example 5.6.1**, `Sp(2) ≃ SL(2; ℝ)`.

Omitted as unstatable with today's Mathlib (recorded here rather than faked):

* **Proposition 5.2.1** — "a compact manifold carries no nondegenerate exact
  `2`-form".  Needs de Rham cohomology, the wedge power `ω^{∧n}`, and the fact
  that a volume form on a closed oriented manifold is not exact (Stokes).  None
  of this exists.
* **Definition 5.2.2** on a manifold, the symplectic form on `T⋆V` built from
  the Liouville form, the area form on a surface or on `S²`, and
  **Proposition 5.3.1** (the symplectic form on `Pⁿ(ℂ)`).  All need
  differential forms on manifolds.
* **Proposition 5.4.2** — "the flow of a Hamiltonian vector field preserves
  `ω`".  Its proof is Cartan's formula `L_X = d ∘ ι_X + ι_X ∘ d` for the Lie
  derivative of a differential form; Mathlib has neither.  The linear shadow of
  this statement is proved here as `exp_mem_symplecticGroup`.
* **Proposition 5.5.6** — the space of calibrated almost complex structures on a
  symplectic manifold is nonempty and contractible; needs sections of a fibre
  bundle.
* **Proposition 5.5.7** — the tangent space to the space of calibrated complex
  structures; the space has no manifold structure here.  The algebraic identity
  its proof rests on is proved as `symm_of_anticommute`.
* **Proposition 5.6.9** — `Sp(2n)` retracts onto `U(n)`, hence
  `π₁(Sp(2n)) ≃ ℤ`.  `U(n)` is not available as a subgroup of `GL(2n; ℝ)` and
  the fundamental group computation is well out of reach; this is the input to
  the Maslov index of Chapter 7.
* Remarks 5.4.6, 5.4.7, 5.4.8 and 5.5.1 (the homogeneous space
  `Jₙ = GL(2n;ℝ)/GL(n;ℂ)`), which are commentary on the above.
-/

open LinearMap (BilinForm)
open Module
open scoped Matrix

namespace MorseFloer
namespace Chapter5

/-! ## §5.1 Symplectic vector spaces

A symplectic vector space is a real vector space with a nondegenerate
alternating bilinear form.  Everything in this section works over an arbitrary
field, so that is how it is stated; the book only uses `ℝ`. -/

section Linear

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- A **symplectic form** on a vector space: a nondegenerate alternating
bilinear form (§5.1). -/
structure IsSymplecticForm (ω : BilinForm K V) : Prop where
  /-- The form is alternating: `ω v v = 0`. -/
  isAlt : ω.IsAlt
  /-- The form is nondegenerate. -/
  nondegenerate : ω.Nondegenerate

namespace IsSymplecticForm

variable {ω : BilinForm K V}

theorem isRefl (h : IsSymplecticForm ω) : ω.IsRefl := h.isAlt.isRefl

theorem self_eq_zero (h : IsSymplecticForm ω) (v : V) : ω v v = 0 := h.isAlt.self_eq_zero v

/-- A symplectic form is skew-symmetric. -/
theorem skew (h : IsSymplecticForm ω) (v w : V) : ω v w = -ω w v := by
  have h0 := h.isAlt.self_eq_zero (v + w)
  have h1 := h.isAlt.self_eq_zero v
  have h2 := h.isAlt.self_eq_zero w
  simp only [map_add, LinearMap.add_apply] at h0
  linear_combination h0 - h1 - h2

/-- Nondegeneracy, in the form used throughout: a vector `ω`-orthogonal to
everything is zero. -/
theorem eq_zero_of_forall (h : IsSymplecticForm ω) {v : V} (hv : ∀ w, ω v w = 0) : v = 0 :=
  h.nondegenerate.1 v hv

theorem eq_zero_of_forall' (h : IsSymplecticForm ω) {v : V} (hv : ∀ w, ω w v = 0) : v = 0 :=
  h.nondegenerate.2 v hv

end IsSymplecticForm

/-- A subspace is **isotropic** when `ω` vanishes on it, i.e. `W ⊆ Wᗮ`. -/
def IsIsotropic (ω : BilinForm K V) (W : Submodule K V) : Prop := W ≤ ω.orthogonal W

/-- A subspace is **coisotropic** when `Wᗮ ⊆ W`. -/
def IsCoisotropic (ω : BilinForm K V) (W : Submodule K V) : Prop := ω.orthogonal W ≤ W

/-- A subspace is **Lagrangian** when it is its own `ω`-orthogonal. -/
def IsLagrangian (ω : BilinForm K V) (W : Submodule K V) : Prop := ω.orthogonal W = W

/-- A subspace is **symplectic** when `ω` restricts to a symplectic form on it,
equivalently when `W ∩ Wᗮ = 0`. -/
def IsSymplecticSubspace (ω : BilinForm K V) (W : Submodule K V) : Prop :=
  Disjoint W (ω.orthogonal W)

theorem isLagrangian_iff {ω : BilinForm K V} {W : Submodule K V} :
    IsLagrangian ω W ↔ IsIsotropic ω W ∧ IsCoisotropic ω W :=
  ⟨fun h => ⟨h.ge, h.le⟩, fun h => le_antisymm h.2 h.1⟩

section FinDim

variable [FiniteDimensional K V] {ω : BilinForm K V}

/-- For a symplectic form, `dim W + dim Wᗮ = dim V`. -/
theorem finrank_orthogonal_add (h : IsSymplecticForm ω) (W : Submodule K V) :
    finrank K W + finrank K (ω.orthogonal W) = finrank K V := by
  have key := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := ω) W
  rw [h.nondegenerate.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at key
  exact key

/-- The `ω`-orthogonal is an involution on subspaces. -/
theorem orthogonal_orthogonal (h : IsSymplecticForm ω) (W : Submodule K V) :
    ω.orthogonal (ω.orthogonal W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal h.nondegenerate h.isRefl W

/-- An isotropic subspace has at most half the dimension of the ambient space. -/
theorem IsIsotropic.two_mul_finrank_le (h : IsSymplecticForm ω) {W : Submodule K V}
    (hW : IsIsotropic ω W) : 2 * finrank K W ≤ finrank K V := by
  have h1 := finrank_orthogonal_add h W
  have h2 : finrank K W ≤ finrank K (ω.orthogonal W) := Submodule.finrank_mono hW
  omega

/-- A Lagrangian subspace has exactly half the dimension of the ambient space. -/
theorem IsLagrangian.two_mul_finrank (h : IsSymplecticForm ω) {W : Submodule K V}
    (hW : IsLagrangian ω W) : 2 * finrank K W = finrank K V := by
  have h1 := finrank_orthogonal_add h W
  rw [hW] at h1
  omega

/-- `W` is coisotropic exactly when `Wᗮ` is isotropic. -/
theorem isCoisotropic_iff_isotropic_orthogonal (h : IsSymplecticForm ω) (W : Submodule K V) :
    IsCoisotropic ω W ↔ IsIsotropic ω (ω.orthogonal W) := by
  unfold IsCoisotropic IsIsotropic
  rw [orthogonal_orthogonal h W]

/-- A symplectic subspace is a complement of its orthogonal. -/
theorem isSymplecticSubspace_iff_isCompl (h : IsSymplecticForm ω) (W : Submodule K V) :
    IsSymplecticSubspace ω W ↔ IsCompl W (ω.orthogonal W) :=
  (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (B := ω) (W := W) h.isRefl).symm

omit [FiniteDimensional K V] in
/-- The restriction of `ω` to a symplectic subspace is symplectic. -/
theorem IsSymplecticSubspace.restrict (h : IsSymplecticForm ω) {W : Submodule K V}
    (hW : IsSymplecticSubspace ω W) : IsSymplecticForm (ω.restrict W) :=
  ⟨fun x => h.isAlt.self_eq_zero (x : V),
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω h.isRefl hW⟩

/-- The orthogonal of a symplectic subspace is again a symplectic subspace. -/
theorem IsSymplecticSubspace.orthogonal (h : IsSymplecticForm ω) {W : Submodule K V}
    (hW : IsSymplecticSubspace ω W) : IsSymplecticSubspace ω (ω.orthogonal W) := by
  unfold IsSymplecticSubspace
  rw [orthogonal_orthogonal h W]
  exact hW.symm

end FinDim

/-! ### Symplectic bases (Proposition 5.1.1) -/

/-- A **symplectic basis**: a basis indexed by `ι ⊕ ι`, written `(e_i, f_i)`, with
`ω(e_i, f_j) = δ_{ij}` and `ω(e_i, e_j) = ω(f_i, f_j) = 0` (§5.1). -/
structure IsSymplecticBasis (ω : BilinForm K V) {ι : Type*} (b : Basis (ι ⊕ ι) K V) : Prop where
  /-- The `e`'s span an isotropic subspace. -/
  ee : ∀ i j, ω (b (Sum.inl i)) (b (Sum.inl j)) = 0
  /-- The `f`'s span an isotropic subspace. -/
  ff : ∀ i j, ω (b (Sum.inr i)) (b (Sum.inr j)) = 0
  /-- `ω(e_i, f_i) = 1`. -/
  ef_self : ∀ i, ω (b (Sum.inl i)) (b (Sum.inr i)) = 1
  /-- `ω(e_i, f_j) = 0` for `i ≠ j`. -/
  ef_ne : ∀ i j, i ≠ j → ω (b (Sum.inl i)) (b (Sum.inr j)) = 0

/-- A zero-dimensional space carries the empty symplectic basis. -/
private theorem symplecticBasis_of_finrank_zero {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hz : finrank K W = 0) (ω : BilinForm K W) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Basis (ι ⊕ ι) K W), IsSymplecticBasis ω b := by
  have : Subsingleton W := by
    constructor
    intro a b
    have key : ∀ x : W, x = 0 := by
      intro x
      obtain ⟨c, hc, hcx⟩ := Module.finrank_eq_zero_iff.mp hz x
      rcases smul_eq_zero.mp hcx with h | h
      · exact absurd h hc
      · exact h
    rw [key a, key b]
  exact ⟨Empty, inferInstance, Basis.empty W,
    ⟨fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim⟩⟩

/-- The inductive step of Proposition 5.1.1, with an explicit bound on the
dimension so that the recursion is on a natural number. -/
private theorem exists_isSymplecticBasis_aux :
    ∀ (n : ℕ) {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (ω : BilinForm K W), IsSymplecticForm ω → finrank K W ≤ n →
      ∃ (ι : Type) (_ : Fintype ι) (b : Basis (ι ⊕ ι) K W), IsSymplecticBasis ω b := by
  intro n
  induction n with
  | zero =>
    intro W _ _ _ ω _ hdim
    exact symplecticBasis_of_finrank_zero (Nat.le_zero.mp hdim) ω
  | succ n IH =>
    intro V _ _ _ ω hω hdim
    rcases Nat.eq_zero_or_pos (finrank K V) with hz | hpos
    · exact symplecticBasis_of_finrank_zero hz ω
    have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    -- Pick `e ≠ 0` and then, by nondegeneracy, a partner `f` with `ω e f = 1`.
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    have hex : ∃ f : V, ω e f = 1 := by
      have hex0 : ∃ f : V, ω e f ≠ 0 := by
        by_contra hcon
        exact he (hω.eq_zero_of_forall fun w => not_not.mp fun hw => hcon ⟨w, hw⟩)
      obtain ⟨f0, hf0⟩ := hex0
      exact ⟨(ω e f0)⁻¹ • f0, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hf0]⟩
    obtain ⟨f, hef⟩ := hex
    have hfe : ω f e = -1 := by rw [hω.skew f e, hef]
    -- The symplectic plane `W = ⟨e, f⟩`.
    obtain ⟨W, hWdef⟩ : ∃ W : Submodule K V, W = Submodule.span K {e, f} := ⟨_, rfl⟩
    have heW : e ∈ W := by rw [hWdef]; exact Submodule.subset_span (by simp)
    have hfW : f ∈ W := by rw [hWdef]; exact Submodule.subset_span (by simp)
    have hdisj : Disjoint W (ω.orthogonal W) := by
      rw [Submodule.disjoint_def]
      intro x hxW hxO
      rw [hWdef] at hxW
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hxW
      have hxO' := LinearMap.BilinForm.mem_orthogonal_iff.mp hxO
      have h1 : ω e x = 0 := hxO' e heW
      have h2 : ω f x = 0 := hxO' f hfW
      rw [← hab] at h1 h2
      simp only [map_add, map_smul, smul_eq_mul] at h1 h2
      rw [hω.self_eq_zero e, hef] at h1
      rw [hfe, hω.self_eq_zero f] at h2
      have hb : b = 0 := by simpa using h1
      have ha : a = 0 := by simpa using h2
      rw [← hab, ha, hb]
      simp
    have hWnd : (ω.restrict W).Nondegenerate :=
      LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω hω.isRefl hdisj
    have hcompl : IsCompl W (ω.orthogonal W) :=
      LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hω.isRefl hWnd
    -- `W` is two-dimensional.
    have hli : LinearIndependent K ![e, f] := by
      rw [linearIndependent_fin2]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      constructor
      · intro hcon
        rw [hcon] at hef
        simp at hef
      · intro a hcon
        rw [← hcon] at hef
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hω.self_eq_zero] at hef
        simp at hef
    have hrange : Set.range ![e, f] = {e, f} := by
      apply Set.Subset.antisymm
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> simp
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have hWrank : finrank K W = 2 := by
      have hs := finrank_span_eq_card hli
      rw [hrange] at hs
      rw [hWdef]
      simpa using hs
    -- The orthogonal complement is again symplectic, of dimension two less.
    have hW'nd : (ω.restrict (ω.orthogonal W)).Nondegenerate := by
      refine LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω hω.isRefl ?_
      rw [orthogonal_orthogonal hω W]
      exact hdisj.symm
    have hW'sym : IsSymplecticForm (ω.restrict (ω.orthogonal W)) :=
      ⟨fun x => hω.isAlt.self_eq_zero (x : V), hW'nd⟩
    have hsum : finrank K W + finrank K (ω.orthogonal W) = finrank K V :=
      finrank_orthogonal_add hω W
    have hW'dim : finrank K (ω.orthogonal W) ≤ n := by omega
    obtain ⟨ι, hι, b0, hb0⟩ := IH (ω.restrict (ω.orthogonal W)) hW'sym hW'dim
    have := hι
    -- Enlarge the basis of `Wᗮ` by the pair `(e, f)`.
    let v : Option ι ⊕ Option ι → V :=
      Sum.elim (fun o => o.elim e fun i => ((b0 (Sum.inl i) : V)))
        (fun o => o.elim f fun i => ((b0 (Sum.inr i) : V)))
    have hb0card : finrank K (ω.orthogonal W) = Fintype.card ι + Fintype.card ι := by
      rw [Module.finrank_eq_card_basis b0, Fintype.card_sum]
    have hcard : Fintype.card (Option ι ⊕ Option ι) = finrank K V := by
      rw [Fintype.card_sum, Fintype.card_option]
      omega
    have hspan : (⊤ : Submodule K V) ≤ Submodule.span K (Set.range v) := by
      rw [← hcompl.sup_eq_top]
      refine sup_le ?_ ?_
      · rw [hWdef, Submodule.span_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Submodule.subset_span ⟨Sum.inl none, rfl⟩
        · exact Submodule.subset_span ⟨Sum.inr none, rfl⟩
      · intro x hx
        have hle : Submodule.span K (Set.range ⇑b0)
            ≤ Submodule.comap ((ω.orthogonal W).subtype) (Submodule.span K (Set.range v)) := by
          rw [Submodule.span_le]
          rintro y ⟨i, rfl⟩
          show ((b0 i : V)) ∈ Submodule.span K (Set.range v)
          refine Submodule.subset_span ?_
          rcases i with i | i
          · exact ⟨Sum.inl (some i), rfl⟩
          · exact ⟨Sum.inr (some i), rfl⟩
        exact hle (b0.mem_span ⟨x, hx⟩)
    -- Book-keeping for the values of `ω` on the new family.
    have hmem : ∀ x : ι ⊕ ι, ((b0 x : V)) ∈ ω.orthogonal W := fun x => (b0 x).2
    have hoe : ∀ x : ι ⊕ ι, ω e ((b0 x : V)) = 0 := fun x =>
      LinearMap.BilinForm.mem_orthogonal_iff.mp (hmem x) e heW
    have hof : ∀ x : ι ⊕ ι, ω f ((b0 x : V)) = 0 := fun x =>
      LinearMap.BilinForm.mem_orthogonal_iff.mp (hmem x) f hfW
    have hoe' : ∀ x : ι ⊕ ι, ω ((b0 x : V)) e = 0 := fun x => by
      rw [hω.skew ((b0 x : V)) e, hoe x, neg_zero]
    have hof' : ∀ x : ι ⊕ ι, ω ((b0 x : V)) f = 0 := fun x => by
      rw [hω.skew ((b0 x : V)) f, hof x, neg_zero]
    have hres : ∀ x y : ι ⊕ ι,
        ω ((b0 x : V)) ((b0 y : V)) = (ω.restrict (ω.orthogonal W)) (b0 x) (b0 y) :=
      fun _ _ => rfl
    refine ⟨Option ι, inferInstance, basisOfTopLeSpanOfCardEqFinrank v hspan hcard, ?_⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩ <;>
      simp only [coe_basisOfTopLeSpanOfCardEqFinrank]
    · cases i with
      | none => cases j with
        | none => exact hω.self_eq_zero e
        | some j => exact hoe (Sum.inl j)
      | some i => cases j with
        | none => exact hoe' (Sum.inl i)
        | some j => exact (hres _ _).trans (hb0.ee i j)
    · cases i with
      | none => cases j with
        | none => exact hω.self_eq_zero f
        | some j => exact hof (Sum.inr j)
      | some i => cases j with
        | none => exact hof' (Sum.inr i)
        | some j => exact (hres _ _).trans (hb0.ff i j)
    · cases i with
      | none => exact hef
      | some i => exact (hres _ _).trans (hb0.ef_self i)
    · cases i with
      | none => cases j with
        | none => exact absurd rfl hij
        | some j => exact hoe (Sum.inr j)
      | some i => cases j with
        | none => exact hof' (Sum.inl i)
        | some j =>
          exact (hres _ _).trans (hb0.ef_ne i j fun h => hij (by rw [h]))

/-- **Proposition 5.1.1.**  A nondegenerate alternating form on a
finite-dimensional vector space admits a *symplectic basis*: a basis
`(e_1, …, e_n, f_1, …, f_n)` with `ω(e_i, f_j) = δ_{ij}` and
`ω(e_i, e_j) = ω(f_i, f_j) = 0`.

The book's proof: choose `e_1, f_1` with `ω(e_1, f_1) = 1`, check that `ω`
restricts to a nondegenerate form on the `ω`-orthogonal of the plane they span,
and induct on the dimension.  That is exactly the argument formalized above. -/
theorem exists_isSymplecticBasis {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ω : BilinForm K V) (hω : IsSymplecticForm ω) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Basis (ι ⊕ ι) K V), IsSymplecticBasis ω b :=
  exists_isSymplecticBasis_aux (finrank K V) ω hω le_rfl

/-- **Corollary of Proposition 5.1.1**: a symplectic vector space has even
dimension, and the dimension is the only invariant of `(V, ω)` up to
isomorphism. -/
theorem even_finrank_of_isSymplecticForm {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ω : BilinForm K V) (hω : IsSymplecticForm ω) :
    Even (finrank K V) := by
  obtain ⟨ι, hι, b, _⟩ := exists_isSymplecticBasis ω hω
  have := hι
  rw [Module.finrank_eq_card_basis b, Fintype.card_sum]
  exact ⟨_, rfl⟩

end Linear

/-! ### The standard symplectic vector space (Example 5.1.2)

The archetype is `ℝⁿ × ℝⁿ` with `ω((p,q),(p',q')) = p·q' − p'·q`.  We realise it
on `(l ⊕ l) → ℝ` as the bilinear form of the matrix `−J`, where `J` is Mathlib's
`Matrix.J = [[0, −1], [1, 0]]`; in a symplectic basis the matrix of `ω` is the
`J` of the book, `[[0, Id], [−Id, 0]]`, which is `−J`. -/

section Standard

variable (l : Type*) [DecidableEq l] [Fintype l]

/-- The **standard symplectic form** on `(l ⊕ l) → ℝ`. -/
noncomputable def stdForm : BilinForm ℝ ((l ⊕ l) → ℝ) :=
  Matrix.toBilin' (-(Matrix.J l ℝ))

theorem stdForm_apply (X Y : (l ⊕ l) → ℝ) :
    stdForm l X Y = X ⬝ᵥ (-(Matrix.J l ℝ)) *ᵥ Y :=
  Matrix.toBilin'_apply' _ _ _

theorem stdForm_single (i j : l ⊕ l) :
    stdForm l (Pi.single i 1) (Pi.single j 1) = -(Matrix.J l ℝ) i j :=
  Matrix.toBilin'_single _ i j

/-- Conjugating the standard form by a matrix multiplies its matrix by `Aᵀ … A`. -/
theorem stdForm_mulVec (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (X Y : (l ⊕ l) → ℝ) :
    stdForm l (A *ᵥ X) (A *ᵥ Y) = Matrix.toBilin' (Aᵀ * (-(Matrix.J l ℝ)) * A) X Y := by
  rw [stdForm_apply, Matrix.toBilin'_apply', Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem stdForm_isAlt : (stdForm l).IsAlt := by
  intro X
  have hT : (-(Matrix.J l ℝ))ᵀ = -(-(Matrix.J l ℝ)) := by
    rw [Matrix.transpose_neg, Matrix.J_transpose]
  have key : X ⬝ᵥ (-(Matrix.J l ℝ)) *ᵥ X = -(X ⬝ᵥ (-(Matrix.J l ℝ)) *ᵥ X) := by
    nth_rewrite 1 [Matrix.dotProduct_mulVec]
    rw [← Matrix.mulVec_transpose, hT, Matrix.neg_mulVec, neg_dotProduct,
      dotProduct_comm]
  rw [stdForm_apply]
  linarith

theorem stdForm_nondegenerate : (stdForm l).Nondegenerate := by
  have hJ : IsUnit (Matrix.J l ℝ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_J l ℝ)
  have hM : (-(Matrix.J l ℝ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hJ.neg).ne_zero
  have hnd : Matrix.Nondegenerate (-(Matrix.J l ℝ)) := Matrix.nondegenerate_of_det_ne_zero hM
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · refine hnd.eq_zero_of_ortho fun w => ?_
    rw [← Matrix.toBilin'_apply']
    exact hX w
  · refine hnd.eq_zero_of_ortho' fun w => ?_
    rw [← Matrix.toBilin'_apply']
    exact hY w

theorem stdForm_isSymplectic : IsSymplecticForm (stdForm l) :=
  ⟨stdForm_isAlt l, stdForm_nondegenerate l⟩

/-- **Example 5.1.2.**  The standard basis of `(l ⊕ l) → ℝ` — that is,
`((e_1,0), …, (e_n,0), (0,e_1), …, (0,e_n))` — is a symplectic basis of the
standard form. -/
theorem isSymplecticBasis_stdForm :
    IsSymplecticBasis (stdForm l) (Pi.basisFun ℝ (l ⊕ l)) := by
  have key : ∀ i j : l ⊕ l,
      stdForm l (Pi.basisFun ℝ (l ⊕ l) i) (Pi.basisFun ℝ (l ⊕ l) j)
        = -(Matrix.J l ℝ) i j := by
    intro i j
    rw [Pi.basisFun_apply, Pi.basisFun_apply, stdForm_single]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · rw [key]; simp [Matrix.J]
  · rw [key]; simp [Matrix.J]
  · rw [key]; simp [Matrix.J, Matrix.one_apply_eq]
  · rw [key]; simp [Matrix.J, Matrix.one_apply_ne hij]

end Standard

/-! ## §5.2 Symplectic manifolds, definition

Mathlib has no differential forms on manifolds, so Definition 5.2.2 cannot be
stated there.  In the local model — an open set of a normed space — a `2`-form
is a map `x ↦ ω x` with values in the alternating bilinear forms, and the
exterior derivative of such a form, evaluated on constant vector fields, is the
cyclic sum of directional derivatives written below. -/

section Forms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **`2`-form** in the local model: a field of alternating bilinear forms. -/
def IsTwoForm (ω : E → BilinForm ℝ E) : Prop := ∀ x, (ω x).IsAlt

/-- A `2`-form is **closed**, `dω = 0`, when for all constant vector fields
`u, v, w` the cyclic sum of directional derivatives
`D_u ω(v,w) − D_v ω(u,w) + D_w ω(u,v)` vanishes. -/
def IsClosedTwoForm (ω : E → BilinForm ℝ E) : Prop :=
  ∀ x u v w : E,
    fderiv ℝ (fun y => ω y v w) x u - fderiv ℝ (fun y => ω y u w) x v
      + fderiv ℝ (fun y => ω y u v) x w = 0

/-- **Definition 5.2.2** in the local model: a symplectic form is a closed
nondegenerate `2`-form.

On a manifold this is a section of `Λ²T⋆W`; Mathlib has no such object, so this
is the best faithful statement available. -/
structure IsSymplecticForm2 (ω : E → BilinForm ℝ E) : Prop where
  /-- Each `ω x` is a symplectic form on the model space. -/
  pointwise : ∀ x, IsSymplecticForm (ω x)
  /-- The form is closed. -/
  isClosed : IsClosedTwoForm ω

/-- A constant nondegenerate alternating form is a symplectic form: this is the
statement that `ℝⁿ × ℝⁿ` with `∑ dp_i ∧ dq_i` is a symplectic manifold
(first example of §5.3). -/
theorem isSymplecticForm2_const {ω₀ : BilinForm ℝ E} (h : IsSymplecticForm ω₀) :
    IsSymplecticForm2 (fun _ : E => ω₀) := by
  refine ⟨fun _ => h, ?_⟩
  intro x u v w
  simp

/-- **Definition 5.2.2** (symplectomorphisms), local model: `φ⋆ω₂ = ω₁`. -/
def IsSymplectomorphismOn (ω₁ ω₂ : E → BilinForm ℝ E) (φ : E → E) (U : Set E) : Prop :=
  ∀ x ∈ U, ∀ u v : E, ω₂ (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) = ω₁ x u v

/-- Translations preserve a constant symplectic form.  This is the reason the
standard structure on `ℝ²ⁿ` descends to the torus `T²ⁿ = ℝ²ⁿ / ℤ²ⁿ`
(Example 5.5.8(2)); the quotient itself needs forms on manifolds and is not
available. -/
theorem isSymplectomorphism_translation (ω₀ : BilinForm ℝ E) (c : E) :
    IsSymplectomorphismOn (fun _ => ω₀) (fun _ => ω₀) (fun y => y + c) Set.univ := by
  intro x _ u v
  have hd : fderiv ℝ (fun y : E => y + c) x = ContinuousLinearMap.id ℝ E :=
    HasFDerivAt.fderiv ((hasFDerivAt_id x).add_const c)
  simp [hd]

/-! ## §5.3 Examples; Darboux's theorem -/

/-- **Theorem 5.3.2 (Darboux).**  Every point of a symplectic manifold has local
coordinates in which the form is the constant standard one.

Stated here in the local model: near `x₀` there is a chart `φ` centred at `x₀`
whose differential carries `ω x` to the constant form `ω x₀`.

The book proves it by Moser's path method — integrating a well chosen
time-dependent vector field.  That argument needs the Lie derivative of a
differential form and the flow of a time-dependent vector field on a manifold,
neither of which Mathlib has. -/
theorem darboux [FiniteDimensional ℝ E] (ω : E → BilinForm ℝ E)
    (_hω : IsSymplecticForm2 ω) (x₀ : E) :
    ∃ φ : OpenPartialHomeomorph E E, x₀ ∈ φ.source ∧
      ∀ x ∈ φ.source, ∀ u v : E,
        ω x₀ (fderiv ℝ (fun y => φ y) x u) (fderiv ℝ (fun y => φ y) x v) = ω x u v := by
  sorry

end Forms

/-! ## §5.4 Hamiltonian vector fields and Hamiltonian systems

If `H : W → ℝ`, the symplectic form turns `dH` into a vector field `X_H`, the
*symplectic gradient*, characterised by `ω(Y, X_H) = dH(Y)` for all `Y`.  On a
vector space with a constant symplectic form this is pure linear algebra, and
that is how it is set up here. -/

section Hamiltonian

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The **Hamiltonian vector** attached to a linear form `φ` (typically
`φ = dH_x`): the unique `v` with `ω(Y, v) = φ(Y)` for all `Y` (§5.4). -/
noncomputable def hamiltonianVector (ω : BilinForm ℝ V) (hω : ω.Nondegenerate)
    (φ : Module.Dual ℝ V) : V :=
  (ω.toDual hω).symm (-φ)

/-- The defining property of the Hamiltonian vector field, `ω(Y, X_H) = dH(Y)`. -/
theorem hamiltonianVector_spec {ω : BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (φ : Module.Dual ℝ V) (Y : V) :
    ω Y (hamiltonianVector ω hω.nondegenerate φ) = φ Y := by
  rw [hω.skew]
  simp [hamiltonianVector]

/-- The Hamiltonian vector is the *unique* solution of `ω(Y, v) = φ(Y)`. -/
theorem hamiltonianVector_unique {ω : BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (φ : Module.Dual ℝ V) (v : V) (h : ∀ Y, ω Y v = φ Y) :
    v = hamiltonianVector ω hω.nondegenerate φ := by
  have hzero : ∀ Y, ω Y (v - hamiltonianVector ω hω.nondegenerate φ) = 0 := by
    intro Y
    rw [map_sub, h Y, hamiltonianVector_spec hω φ Y, sub_self]
  exact sub_eq_zero.mp (hω.eq_zero_of_forall' hzero)

/-- `X_H` vanishes at `x` exactly when `x` is a critical point of `H` (§5.4).  In
particular the zeros of a Hamiltonian vector field are the critical points of a
function. -/
theorem hamiltonianVector_eq_zero_iff {ω : BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (φ : Module.Dual ℝ V) :
    hamiltonianVector ω hω.nondegenerate φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    ext Y
    have hY : φ Y = 0 := by
      have hs := hamiltonianVector_spec hω φ Y
      rw [h] at hs
      simpa using hs.symm
    simp [hY]
  · rintro rfl
    simp [hamiltonianVector]

/-- `H` is constant along the trajectories of `X_H`: `dH(X_H) = 0` (§5.4).  This
is immediate from the alternation of `ω`. -/
theorem apply_hamiltonianVector {ω : BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (φ : Module.Dual ℝ V) :
    φ (hamiltonianVector ω hω.nondegenerate φ) = 0 := by
  have hs := hamiltonianVector_spec hω φ (hamiltonianVector ω hω.nondegenerate φ)
  rw [← hs]
  exact hω.self_eq_zero _

end Hamiltonian

section HamiltonianField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The **Hamiltonian vector field** of `H : E → ℝ` for a constant symplectic
form: `ω(Y, X_H(x)) = (dH)_x(Y)` (§5.4).  The associated *Hamiltonian system* is
`ẋ(t) = X_H(x(t))`. -/
noncomputable def hamiltonianField (ω : BilinForm ℝ E) (hω : ω.Nondegenerate)
    (H : E → ℝ) (x : E) : E :=
  hamiltonianVector ω hω (fderiv ℝ H x).toLinearMap

/-- The zeros of `X_H` are exactly the critical points of `H` (§5.4). -/
theorem hamiltonianField_eq_zero_iff {ω : BilinForm ℝ E} (hω : IsSymplecticForm ω)
    (H : E → ℝ) (x : E) :
    hamiltonianField ω hω.nondegenerate H x = 0 ↔ fderiv ℝ H x = 0 := by
  simp only [hamiltonianField]
  rw [hamiltonianVector_eq_zero_iff hω]
  constructor
  · intro h
    ext y
    have hy := congrArg (fun f : Module.Dual ℝ E => f y) h
    simpa using hy
  · intro h
    ext y
    simp [h]

/-- A **time-dependent Hamiltonian** `H : E × ℝ → ℝ` gives the non-autonomous
system `ẋ(t) = X_t(x(t))` with `X_t = X_{H_t}` (§5.4). -/
noncomputable def timeDependentHamiltonianField (ω : BilinForm ℝ E) (hω : ω.Nondegenerate)
    (H : E → ℝ → ℝ) (t : ℝ) (x : E) : E :=
  hamiltonianField ω hω (fun y => H y t) x

/-- **Definition 5.4.4.**  A `1`-periodic solution is *nondegenerate* when the
differential of the time-one map `ψ₁` does not have `1` as an eigenvalue, i.e.
`det(Id − T_{x(0)}ψ₁) ≠ 0`.

The flow `ψ₁` is not available, so this records the condition itself, as a
property of a linear map. -/
def IsNondegenerateReturnMap (P : E →L[ℝ] E) : Prop :=
  Function.Bijective ((ContinuousLinearMap.id ℝ E) - P)

end HamiltonianField

/-! ### Hamilton's equations and quadratic Hamiltonians -/

section HamiltonStandard

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- A linear form on `(l ⊕ l) → ℝ` is the dot product with its vector of
coefficients — the "gradient". -/
theorem dual_eq_dotProduct (φ : Module.Dual ℝ ((l ⊕ l) → ℝ)) (Y : (l ⊕ l) → ℝ) :
    φ Y = Y ⬝ᵥ fun i => φ (Pi.single i 1) := by
  conv_lhs => rw [← (Pi.basisFun ℝ (l ⊕ l)).sum_repr Y]
  rw [map_sum]
  simp [dotProduct]

/-- **Hamilton's equations.**  For the standard form, the Hamiltonian vector
field is `X_H = J · grad H`; writing `X = (p, q)` and `J` in blocks this is
`q̇ = ∂H/∂p`, `ṗ = −∂H/∂q` (§5.4).  It is also the identity `X_H = J grad H` of
the end of §5.5, since the metric calibrated by `J₀` is the Euclidean one. -/
theorem hamiltonianVector_stdForm (φ : Module.Dual ℝ ((l ⊕ l) → ℝ)) :
    hamiltonianVector (stdForm l) (stdForm_nondegenerate l) φ
      = Matrix.J l ℝ *ᵥ fun i => φ (Pi.single i 1) := by
  refine (hamiltonianVector_unique (stdForm_isSymplectic l) φ _ ?_).symm
  intro Y
  have hJJ : (-(Matrix.J l ℝ)) * Matrix.J l ℝ = 1 := by
    rw [Matrix.neg_mul, Matrix.J_squared, neg_neg]
  rw [stdForm_apply, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec, ← dual_eq_dotProduct]

/-- **Example 5.4.3.**  For a quadratic Hamiltonian the Hamiltonian vector field
is linear, `X_H = A·(p,q)` with `A = −J · Hess H`, and its flow is `t ↦ exp(tA)`.
Such an `A` satisfies `AᵀJ + JA = 0`, and then `exp A` is symplectic — this is
the linear shadow of Proposition 5.4.2. -/
theorem exp_mem_symplecticGroup {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (h : Aᵀ * Matrix.J l ℝ + Matrix.J l ℝ * A = 0) :
    NormedSpace.exp A ∈ Matrix.symplecticGroup l ℝ := by
  have hJu : IsUnit (Matrix.J l ℝ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_J l ℝ)
  have hJd : IsUnit (Matrix.J l ℝ).det := Matrix.isUnit_det_J l ℝ
  have hE : IsUnit (NormedSpace.exp A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp A)
  -- `Aᵀ = J (−A) J⁻¹`.
  have h1 : Aᵀ * Matrix.J l ℝ = -(Matrix.J l ℝ * A) := by
    rw [eq_neg_iff_add_eq_zero]; exact h
  have hAt' : Aᵀ = Matrix.J l ℝ * A * Matrix.J l ℝ := by
    calc Aᵀ = Aᵀ * (-(Matrix.J l ℝ * Matrix.J l ℝ)) := by
          rw [Matrix.J_squared]; simp
      _ = -(Aᵀ * Matrix.J l ℝ * Matrix.J l ℝ) := by
          rw [Matrix.mul_neg, Matrix.mul_assoc]
      _ = -(-(Matrix.J l ℝ * A) * Matrix.J l ℝ) := by rw [h1]
      _ = Matrix.J l ℝ * A * Matrix.J l ℝ := by rw [Matrix.neg_mul, neg_neg]
  have hAt : Aᵀ = Matrix.J l ℝ * (-A) * (Matrix.J l ℝ)⁻¹ := by
    rw [Matrix.J_inv, hAt']
    noncomm_ring
  rw [SymplecticGroup.mem_iff']
  have ht : (NormedSpace.exp A)ᵀ
      = Matrix.J l ℝ * (NormedSpace.exp A)⁻¹ * (Matrix.J l ℝ)⁻¹ := by
    rw [← Matrix.exp_transpose, hAt, Matrix.exp_conj _ _ hJu, Matrix.exp_neg]
  rw [ht]
  calc Matrix.J l ℝ * (NormedSpace.exp A)⁻¹ * (Matrix.J l ℝ)⁻¹ * Matrix.J l ℝ
        * NormedSpace.exp A
      = Matrix.J l ℝ * (NormedSpace.exp A)⁻¹ *
          ((Matrix.J l ℝ)⁻¹ * Matrix.J l ℝ) * NormedSpace.exp A := by
        simp [Matrix.mul_assoc]
    _ = Matrix.J l ℝ * ((NormedSpace.exp A)⁻¹ * NormedSpace.exp A) := by
        rw [Matrix.nonsing_inv_mul _ hJd, Matrix.mul_one, Matrix.mul_assoc]
    _ = Matrix.J l ℝ := by rw [Matrix.nonsing_inv_mul _ hE, Matrix.mul_one]

/-- **Proposition 5.4.5.**  A critical point of `H` that is nondegenerate as a
periodic orbit of the Hamiltonian system is nondegenerate as a critical point.

In the quadratic model the return map is `exp A` with `A = −J·Hess H`, so the
statement is: if `Hess H` is singular then `exp A` has `1` as an eigenvalue.
This needs `exp A ·ᵥ v = v` whenever `A ·ᵥ v = 0`, which is a `mulVec` version of
the exponential series that Mathlib does not provide. -/
theorem nondegenerate_of_nondegenerate_orbit (S : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (_hS : Sᵀ = S) (_hdet : (NormedSpace.exp (-(Matrix.J l ℝ) * S) - 1).det ≠ 0) :
    S.det ≠ 0 := by
  sorry

end HamiltonStandard

/-! ## §5.5 Complex structures

A complex structure `J` on a symplectic vector space `(E, ω)` is *calibrated*
by `ω` when `J² = −Id`, `J` is symplectic, and `g(v,w) = ω(v, Jw)` is an inner
product. -/

section Calibrated

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A complex structure **calibrated** by `ω` (§5.5). -/
structure IsCalibrated (ω : BilinForm ℝ V) (J : V →ₗ[ℝ] V) : Prop where
  /-- `J² = −Id`. -/
  sq : ∀ v, J (J v) = -v
  /-- `J` is symplectic. -/
  symplectic : ∀ v w, ω (J v) (J w) = ω v w
  /-- `g(v,v) = ω(v, Jv)` is positive definite. -/
  pos : ∀ v, v ≠ 0 → 0 < ω v (J v)

/-- The metric `g(v, w) = ω(v, Jw)` determined by a calibrated complex
structure. -/
noncomputable def calibratedMetric (ω : BilinForm ℝ V) (J : V →ₗ[ℝ] V) : BilinForm ℝ V :=
  ω.compl₂ J

@[simp]
theorem calibratedMetric_apply (ω : BilinForm ℝ V) (J : V →ₗ[ℝ] V) (v w : V) :
    calibratedMetric ω J v w = ω v (J w) := rfl

variable {ω : BilinForm ℝ V} {J : V →ₗ[ℝ] V}

/-- The bilinear form `g(v,w) = ω(v, Jw)` of a calibrated complex structure is
symmetric — so, with positivity, it is an inner product (§5.5). -/
theorem calibratedMetric_symm (hω : IsSymplecticForm ω) (hJ : IsCalibrated ω J) (v w : V) :
    calibratedMetric ω J v w = calibratedMetric ω J w v := by
  have h1 : ω (J v) (J (J w)) = ω v (J w) := hJ.symplectic v (J w)
  rw [hJ.sq w] at h1
  simp only [calibratedMetric_apply]
  rw [← h1, map_neg, hω.skew (J v) w]
  ring

/-- `g` is positive definite. -/
theorem calibratedMetric_pos (hJ : IsCalibrated ω J) {v : V} (hv : v ≠ 0) :
    0 < calibratedMetric ω J v v := hJ.pos v hv

/-- A calibrated complex structure is an isometry of the metric it defines
(§5.5). -/
theorem calibratedMetric_J (hJ : IsCalibrated ω J) (v w : V) :
    calibratedMetric ω J (J v) (J w) = calibratedMetric ω J v w :=
  hJ.symplectic v (J w)

/-- A calibrated complex structure is antisymmetric for the metric it defines
(§5.5). -/
theorem calibratedMetric_antisymm (hJ : IsCalibrated ω J) (v w : V) :
    calibratedMetric ω J (J v) w = -calibratedMetric ω J v (J w) := by
  simp only [calibratedMetric_apply]
  rw [hJ.symplectic v w, hJ.sq w, map_neg, neg_neg]

/-- **Lemma 5.5.3** (first half).  If `( , )` is an inner product and `A` is
defined by `(X, AY) = ω(X, Y)`, then `A` is antisymmetric.

The rest of Lemma 5.5.3 — that the polar decomposition `A = BJ` produces a
calibrated complex structure `J` — needs the polar decomposition of an
automorphism of a Euclidean space, which is not available. -/
theorem antisymm_of_repr {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ω : BilinForm ℝ W} (hω : IsSymplecticForm ω) (A : W →ₗ[ℝ] W)
    (hA : ∀ X Y, (inner ℝ X (A Y) : ℝ) = ω X Y) (X Y : W) :
    (inner ℝ X (A Y) : ℝ) = -(inner ℝ (A X) Y : ℝ) := by
  rw [hA X Y, hω.skew X Y, real_inner_comm, hA Y X]

/-- **Proposition 5.5.7** (the computation behind it).  If `S` anticommutes with
`J` and is `ω`-antisymmetric, then `S` is symmetric for the metric `g` defined by
`J` — this is what identifies the tangent space to the space of calibrated
structures with a space of symmetric matrices.

The tangent space itself cannot be stated: the set of calibrated structures has
no manifold structure here. -/
theorem symm_of_anticommute (_hJ : IsCalibrated ω J) (S : V →ₗ[ℝ] V)
    (hS : ∀ v, J (S v) + S (J v) = 0) (hSω : ∀ v w, ω (S v) w + ω v (S w) = 0) (v w : V) :
    calibratedMetric ω J (S v) w = calibratedMetric ω J v (S w) := by
  have h1 : ω (S v) (J w) = -ω v (S (J w)) := by
    have h := hSω v (J w)
    linarith
  have h2 : S (J w) = -(J (S w)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hS w
  simp only [calibratedMetric_apply]
  rw [h1, h2, map_neg, neg_neg]

end Calibrated

/-! ### The standard calibrated structure, and existence -/

section StandardCalibrated

variable (l : Type*) [DecidableEq l] [Fintype l]

/-- The standard complex structure `J₀` on `(l ⊕ l) → ℝ`.  Under the
identification `ℝ²ⁿ = ℂⁿ` this is multiplication by `i` (§5.5). -/
noncomputable def stdJ : ((l ⊕ l) → ℝ) →ₗ[ℝ] ((l ⊕ l) → ℝ) := Matrix.toLin' (Matrix.J l ℝ)

@[simp]
theorem stdJ_apply (X : (l ⊕ l) → ℝ) : stdJ l X = Matrix.J l ℝ *ᵥ X := Matrix.toLin'_apply _ _

/-- `J₀` is calibrated by the standard symplectic form, and the metric it
defines is the Euclidean inner product: this is the statement that the standard
hermitian form on `ℂⁿ` decomposes as `⟪u,v⟫ = (u,v) − i ω(u,v)` (§5.5). -/
theorem stdJ_isCalibrated : IsCalibrated (stdForm l) (stdJ l) := by
  have hJJ : (-(Matrix.J l ℝ)) * Matrix.J l ℝ = 1 := by
    rw [Matrix.neg_mul, Matrix.J_squared, neg_neg]
  refine ⟨fun v => ?_, fun v w => ?_, fun v hv => ?_⟩
  · simp only [stdJ_apply]
    rw [Matrix.mulVec_mulVec, Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec]
  · simp only [stdJ_apply]
    rw [stdForm_mulVec]
    have hM : (Matrix.J l ℝ)ᵀ * (-(Matrix.J l ℝ)) * Matrix.J l ℝ = -(Matrix.J l ℝ) := by
      rw [Matrix.J_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.J_squared,
        Matrix.neg_mul, Matrix.one_mul]
    rw [hM]
    rfl
  · simp only [stdJ_apply]
    rw [stdForm_apply, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
    have h0 : (0 : ℝ) ≤ v ⬝ᵥ v := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv

/-- The metric calibrated by `J₀` is the Euclidean scalar product. -/
theorem calibratedMetric_stdJ (X Y : (l ⊕ l) → ℝ) :
    calibratedMetric (stdForm l) (stdJ l) X Y = X ⬝ᵥ Y := by
  simp only [calibratedMetric_apply, stdJ_apply]
  rw [stdForm_apply, Matrix.mulVec_mulVec, Matrix.neg_mul, Matrix.J_squared, neg_neg,
    Matrix.one_mulVec]

end StandardCalibrated

section CalibratedExistence

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **Lemma 5.5.3 / §5.5.**  Every symplectic vector space carries a complex
structure calibrated by its form.

The book gives two proofs: one uses a symplectic basis (Proposition 5.1.1) to
write down `J₀` explicitly, the other picks any inner product, defines `A` by
`(X, AY) = ω(X,Y)` and takes the orthogonal part `J` of the polar decomposition
`A = BJ`.  Mathlib has neither a polar decomposition for automorphisms of a
Euclidean space nor a transport of `stdJ` along the symplectic basis, so this is
left open. -/
theorem exists_isCalibrated (ω : BilinForm ℝ V) (_hω : IsSymplecticForm ω) :
    ∃ J : V →ₗ[ℝ] V, IsCalibrated ω J := by
  sorry

/-- **Proposition 5.5.4 / Corollary 5.5.5.**  The space `Jc(ω)` of complex
structures calibrated by `ω` is contractible: the map
`J ↦ (J + j)⁻¹ ∘ (J − j)` is a diffeomorphism onto the open unit ball of the
space of symmetric endomorphisms anticommuting with a fixed `j ∈ Jc(ω)`.

This is what lets one use calibrated structures without caring which one; on a
manifold it gives Proposition 5.5.6, which cannot be stated here. -/
theorem contractibleSpace_calibrated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (ω : BilinForm ℝ E) (_hω : IsSymplecticForm ω) :
    ContractibleSpace {J : E →L[ℝ] E // IsCalibrated ω J.toLinearMap} := by
  sorry

end CalibratedExistence

/-! ## §5.6 The symplectic group

`Sp(2n)` is the group of linear transformations of `ℝ²ⁿ` preserving the standard
form `ω`; in matrix terms `AᵀJA = J`.  Mathlib has this group as
`Matrix.symplecticGroup`, and proves `det A = 1` (Corollary 5.6.10). -/

section SymplecticGroupSection

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- Mathlib's `Matrix.symplecticGroup` is exactly the group of linear isometries
of the standard symplectic form (§5.6). -/
theorem mem_symplecticGroup_iff_preserves (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    A ∈ Matrix.symplecticGroup l ℝ ↔
      ∀ X Y : (l ⊕ l) → ℝ, stdForm l (A *ᵥ X) (A *ᵥ Y) = stdForm l X Y := by
  rw [SymplecticGroup.mem_iff']
  constructor
  · intro h X Y
    have hM : Aᵀ * (-(Matrix.J l ℝ)) * A = -(Matrix.J l ℝ) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, h]
    rw [stdForm_mulVec, hM]
    rfl
  · intro h
    have hM : Aᵀ * (-(Matrix.J l ℝ)) * A = -(Matrix.J l ℝ) := by
      ext i j
      have hij := h (Pi.single i 1) (Pi.single j 1)
      rw [stdForm_mulVec, Matrix.toBilin'_single, stdForm_single] at hij
      exact hij
    have hneg : -(Aᵀ * Matrix.J l ℝ * A) = -(Matrix.J l ℝ) := by
      rw [← Matrix.neg_mul, ← Matrix.mul_neg]
      exact hM
    exact neg_inj.mp hneg

/-- `A` is complex linear for `J₀`, i.e. `A(iZ) = iA(Z)`. -/
def IsComplexLinearMat (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Prop :=
  A * Matrix.J l ℝ = Matrix.J l ℝ * A

/-- `A` is orthogonal, i.e. `AᵀA = Id`. -/
def IsOrthogonalMat (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Prop := Aᵀ * A = 1

/-- **Proposition 5.6.2** (first implication).  Orthogonal + complex linear ⟹
symplectic. -/
theorem symplectic_of_orthogonal_of_complexLinear {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hO : IsOrthogonalMat A) (hC : IsComplexLinearMat A) :
    A ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  calc Aᵀ * Matrix.J l ℝ * A = Aᵀ * (Matrix.J l ℝ * A) := Matrix.mul_assoc _ _ _
    _ = Aᵀ * (A * Matrix.J l ℝ) := by rw [hC]
    _ = Aᵀ * A * Matrix.J l ℝ := (Matrix.mul_assoc _ _ _).symm
    _ = Matrix.J l ℝ := by rw [hO, Matrix.one_mul]

/-- **Proposition 5.6.2** (second implication).  Symplectic + complex linear ⟹
orthogonal, so such a matrix is unitary. -/
theorem orthogonal_of_symplectic_of_complexLinear {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hS : A ∈ Matrix.symplecticGroup l ℝ) (hC : IsComplexLinearMat A) :
    IsOrthogonalMat A := by
  rw [SymplecticGroup.mem_iff'] at hS
  have h1 : Aᵀ * A * Matrix.J l ℝ = Matrix.J l ℝ := by
    rw [Matrix.mul_assoc, hC, ← Matrix.mul_assoc]
    exact hS
  have h2 : Aᵀ * A * (Matrix.J l ℝ * Matrix.J l ℝ) = Matrix.J l ℝ * Matrix.J l ℝ := by
    rw [← Matrix.mul_assoc, h1]
  rw [Matrix.J_squared, Matrix.mul_neg, Matrix.mul_one] at h2
  exact neg_inj.mp h2

/-- **Proposition 5.6.2** (third implication).  Symplectic + orthogonal ⟹
complex linear. -/
theorem complexLinear_of_symplectic_of_orthogonal {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hS : A ∈ Matrix.symplecticGroup l ℝ) (hO : IsOrthogonalMat A) :
    IsComplexLinearMat A := by
  rw [SymplecticGroup.mem_iff'] at hS
  have hAAT : A * Aᵀ = 1 := mul_eq_one_comm.mp hO
  calc A * Matrix.J l ℝ = A * (Aᵀ * Matrix.J l ℝ * A) := by rw [hS]
    _ = A * Aᵀ * Matrix.J l ℝ * A := by simp [Matrix.mul_assoc]
    _ = Matrix.J l ℝ * A := by rw [hAAT, Matrix.one_mul]

/-- **Corollary 5.6.10.**  A symplectic matrix has determinant `1`.  This is
Mathlib's `SymplecticGroup.det_eq_one`; the book deduces it from the
path-connectedness of `Sp(2n)` (Proposition 5.6.9). -/
theorem det_eq_one_of_symplectic {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) : A.det = 1 :=
  SymplecticGroup.det_eq_one hA

/-- **Proposition 5.6.3.**  For a symplectic `A`, the matrices `Aᵀ` and `A⁻¹` are
conjugate (by `J`); since `Aᵀ` and `A` are always conjugate, `A` and `A⁻¹` are
conjugate.  In particular `λ` is an eigenvalue of `A` iff `λ⁻¹` is. -/
theorem transpose_mul_J_eq {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    Aᵀ * Matrix.J l ℝ = Matrix.J l ℝ * A⁻¹ := by
  have hu : IsUnit A.det := by rw [det_eq_one_of_symplectic hA]; exact isUnit_one
  have h := SymplecticGroup.mem_iff'.mp hA
  calc Aᵀ * Matrix.J l ℝ = Aᵀ * Matrix.J l ℝ * (A * A⁻¹) := by
        rw [Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
    _ = Aᵀ * Matrix.J l ℝ * A * A⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = Matrix.J l ℝ * A⁻¹ := by rw [h]

/-- **Proposition 5.6.4.**  The characteristic polynomial of a symplectic matrix
is symmetric: `det(A − λ Id) = λ^{2n} det(A − λ⁻¹ Id)`.

The book's proof uses `A = −J ᵗA⁻¹ J`, `J² = −Id` and `det A = 1`.  Carrying it
out formally needs the determinant of a conjugate and a fair amount of
manipulation of `Matrix.nonsing_inv`; not done here. -/
theorem det_charpoly_symmetric {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (_hA : A ∈ Matrix.symplecticGroup l ℝ) {lam : ℝ} (_hlam : lam ≠ 0) :
    (A - lam • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)).det
      = lam ^ Fintype.card (l ⊕ l) * (A - lam⁻¹ • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)).det := by
  sorry

/-- **Proposition 5.6.6** for genuine eigenvectors.  If `AX = λX`, `AY = μY` and
`λμ ≠ 1`, then `ω(X, Y) = 0`.

Here `ω` is the standard form of `(l ⊕ l) → ℂ`, the complexification of the real
standard form; `A` is a real symplectic matrix viewed over `ℂ`. -/
theorem stdForm_eq_zero_of_eigen {A : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hA : ∀ X Y : (l ⊕ l) → ℂ,
      Matrix.toBilin' (-(Matrix.J l ℂ)) (A *ᵥ X) (A *ᵥ Y)
        = Matrix.toBilin' (-(Matrix.J l ℂ)) X Y)
    {lam mu : ℂ} {X Y : (l ⊕ l) → ℂ} (hX : A *ᵥ X = lam • X) (hY : A *ᵥ Y = mu • Y)
    (hne : lam * mu ≠ 1) :
    Matrix.toBilin' (-(Matrix.J l ℂ)) X Y = 0 := by
  have key := hA X Y
  rw [hX, hY] at key
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at key
  have h : (lam * mu - 1) * Matrix.toBilin' (-(Matrix.J l ℂ)) X Y = 0 := by
    linear_combination key
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact h1

/-- **Proposition 5.6.6** in general: the same vanishing for generalised
eigenvectors, `X ∈ ker(A − λ)^r` and `Y ∈ ker(A − μ)^s`.

The book proves it by a double induction on `(r, s)`.  Only the case
`r = s = 1` is formalized above. -/
theorem stdForm_eq_zero_of_generalised_eigen {A : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (_hA : A ∈ Matrix.symplecticGroup l ℂ) {lam mu : ℂ} (_hne : lam * mu ≠ 1)
    (r s : ℕ) {X Y : (l ⊕ l) → ℂ}
    (_hX : ((A - lam • 1) ^ r) *ᵥ X = 0) (_hY : ((A - mu • 1) ^ s) *ᵥ Y = 0) :
    Matrix.toBilin' (-(Matrix.J l ℂ)) X Y = 0 := by
  sorry

/-- **Example 5.6.1.**  `Sp(2) = SL(2; ℝ)`: for `n = 1` a matrix is symplectic
exactly when its determinant is `1`.

One direction is `SymplecticGroup.det_eq_one`; the converse is the `2 × 2`
computation `A J Aᵀ = (det A) J`, which is not done here. -/
theorem mem_symplecticGroup_fin_one_iff (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) :
    A ∈ Matrix.symplecticGroup (Fin 1) ℝ ↔ A.det = 1 := by
  sorry

end SymplecticGroupSection

end Chapter5
end MorseFloer
