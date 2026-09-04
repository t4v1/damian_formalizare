import MorseFloer.Part2.Ch5

/-!
# Chapter 7: Geometry of the symplectic group, the Maslov index

Formalization of Chapter 7 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 169–197).  This chapter builds the integer that
grades the Floer complex: the Conley–Zehnder (Maslov) index of a path of
symplectic matrices starting at the identity and ending at a matrix without the
eigenvalue `1`.  It plays the role that the Morse index plays in Part I.

The chapter has three sections:

* **§7.1** the three steps towards the index: a nondegenerate contractible
  `1`-periodic orbit gives a path `t ↦ A(t)` in `Sp(2n)` with `A 0 = Id` and
  `1 ∉ Spec (A 1)` (Theorem 7.1.1, Remark 7.1.2); the map
  `ρ : Sp(2n) → S¹` and its five characteristic properties (Theorem 7.1.3);
  the open set `Sp(2n)⋆` of symplectic matrices without the eigenvalue `1`, its
  two connected components `Sp(2n)±` (Proposition 7.1.4, Lemma 7.1.5) and the
  continuous lifts `ρ±` of `ρ` over them (Lemma 7.1.6);
* **§7.2** the Maslov index itself: the winding number `Δ` of a lift of `ρ ∘ γ`,
  the reference matrices `W±`, the index `μ(ψ) = Δ(ψ) + r(ψ 1)` and its
  properties (Proposition 7.2.1, Corollary 7.2.2), the correspondence between
  paths of symplectic matrices and paths of symmetric matrices (Lemma 7.2.3),
  and paths of prescribed index (Lemma 7.2.4);
* **§7.3** the appendix constructing `ρ` from the eigenvalue data of a symplectic
  matrix (Lemma 7.3.1 to Lemma 7.3.11).

## Status

The **topological input is out of reach**.  Chapter 5 already records as a gap
that `Sp(2n)` retracts onto `U(n)` and therefore has infinite cyclic fundamental
group (Proposition 5.6.9): Mathlib has no `U(n)` as a subgroup of `GL(2n; ℝ)`,
no polar decomposition in the required form, and no computation of the
fundamental group of a matrix group.  Everything in this chapter that *defines*
the index — the existence of `ρ`, the unique path-lifting through
`θ ↦ e^{iθ}`, the two connected components of `Sp(2n)⋆` — rests on that input.
Rather than inventing a construction, this file

* states the **characteristic properties** of `ρ` (Theorem 7.1.3) as a predicate
  `IsRho` on a family of maps `Sp(2n) → S¹`, asserts its existence with `sorry`,
  and *proves* the consequences that are formal, e.g. `ρ(Id) = 1` and
  `ρ(−Id) = (−1)ⁿ` (the value at `W⁺` used in the proof of Proposition 7.2.1);
* states the **defining properties** of the Conley–Zehnder index
  (Proposition 7.2.1) as a predicate `IsConleyZehnderIndex` on a family of
  functions on paths — normalisation on `exp(tJS)`, the sign of
  `det(ψ(1) − Id)`, homotopy invariance, additivity under block sums — asserts
  its existence with `sorry`, and *proves* what follows formally from the
  axioms, notably the parity of `μ(ψ) − n` and Corollary 7.2.2.  This is what
  later chapters should quote when they state index formulas;
* *proves* the matrix algebra of §7.1.c outright: the sets `Sp(2n)⋆`,
  `Sp(2n)±`, `Σ`, the fact that `W⁺ = −Id` lies in `Sp(2n)⁺`, the relation
  `A⁻¹ = (−J)AᵀJ` and, from it, the eigenvalue symmetry
  `det(A − λ⁻¹) = (−λ⁻¹)^{2n} det(A − λ)` — this is Proposition 5.6.4, left as
  `sorry` in `Part2/Ch5.lean` and proved here;
* *proves* the `2 × 2` case of §7.1.c in full, in the concrete model
  `Matrix (Fin 2) (Fin 2) ℝ`: `Sp(2) = SL(2; ℝ)`, `det(A − Id) = 2 − tr A`, so
  that the two components are `tr A < 2` and `tr A > 2`, and the rotations and
  the hyperbolic matrices `diag(λ, λ⁻¹)` land where the book says they do;
* *proves* the algebraic core of Lemma 7.2.3 in both directions;
* *proves* Lemma 7.3.1 and its corollary: the real symmetric form
  `B(X, Y) = Im ω(X, Ȳ)` on `ℂ²ⁿ` is nondegenerate and satisfies
  `B(iX, iY) = B(X, Y)` and `B(X̄, Ȳ) = −B(X, Y)`.

Assumed (`sorry`):

* **Theorem 7.1.3**, the existence of `ρ` (`exists_isRho`);
* **Proposition 7.1.4**, the path-connectedness of `Sp(2n)±`, and **Lemma 7.1.5**
  on which it rests;
* **Lemma 7.1.6**, the continuous lifts `ρ± : Sp(2n)± → ℝ`;
* the independence of `Δ` of the chosen lift (`Delta_eq_of_isAngleLift`): the
  argument needs that a continuous function into `2πℤ` on a connected domain is
  constant, i.e. unique path lifting for `θ ↦ e^{iθ}`;
* **Proposition 7.2.1**/the existence of the index
  (`exists_isConleyZehnderIndex`);
* **Lemma 7.2.3** in its differential form (statable entrywise, but its proof
  needs matrix-valued calculus) and **Lemma 7.2.4**;
* the closed forms of `exp(tJS)` for the three `2 × 2` symmetric matrices of the
  proof of Proposition 7.2.1: Mathlib has no closed form for the exponential of
  a `2 × 2` matrix;
* the second half of **Remark 7.1.2**: `‖S‖ < 2π` implies `exp(JS)` has no
  eigenvalue `1`.

Omitted as unstatable with today's Mathlib (recorded here rather than faked):

* **Theorem 7.1.1** — a symplectic vector bundle pulled back to a disc is
  trivial and all its trivialisations are homotopic.  Mathlib has vector
  bundles but no symplectic vector bundles, no symplectic frames, and no
  homotopy classification of trivialisations; and §7.1.a builds the path `A(t)`
  out of such a trivialisation along a capping disc, which requires all of it.
  Consequently the *geometric* first step — attaching a path of symplectic
  matrices to a contractible periodic orbit — has no Lean statement here, and
  §7.2.b (the summary of the three steps) has none either.
* The statement in **Proposition 7.1.4** that the inclusions
  `Sp(2n)± ↪ Sp(2n)` induce the zero map on fundamental groups.  Mathlib's
  `FundamentalGroup` has no induced-homomorphism API usable here, and the
  statement is anyway a formal consequence of Lemma 7.1.6 together with
  `π₁(Sp(2n)) ≅ ℤ`, which is the Chapter 5 gap.  Lemma 7.1.6 is stated instead.
* The **definition of `ρ`** of §7.3.b, `ρ(A) = (−1)^{m₀/2} ∏ λ^{m₊(λ)}`, and
  everything downstream of it (Proposition 7.3.5, the continuity argument of
  §7.3.c with Propositions 7.3.6, 7.3.7, 7.3.8, 7.3.10 and Corollary 7.3.9, and
  Lemma 7.3.11).  It needs the decomposition of the generalised eigenspace
  `E_λ` of a symplectic matrix into the maximal subspaces on which the real
  quadratic form `Q(X) = Im ω(X, X̄)` is positive resp. negative definite, and
  the *signature* of `Q` restricted to a complex subspace of `ℂ²ⁿ` regarded as a
  real one.  Mathlib has generalised eigenspaces (`Module.End.genEigenspace`)
  and signatures of quadratic forms (`sigPos`/`sigNeg`) but nothing that
  connects them to a product over the spectrum, and the continuity of `ρ` rests
  on continuity of eigenvalues *and* of characteristic subspaces in the
  Grassmannian, which is absent.  Only the preliminaries §7.3.a are formalized.
* **Lemma 7.3.3** and **Corollary 7.3.4**, the `B`-orthogonality of the
  characteristic subspaces `E_λ`, `E_μ` for `λμ ≠ 1` and the vanishing signature
  of `Q` on `E_λ ⊕ E_{1/λ}`.  The first is the complex shadow of
  Proposition 5.6.6, which is `sorry` in Chapter 5 beyond genuine eigenvectors;
  the second needs the signature discussed above.  **Corollary 7.3.2** (the
  signature of `Q` on all of `ℂ²ⁿ` vanishes) is omitted for the same reason;
  its nondegeneracy half is proved here as `BForm_eq_zero_of_forall`.
-/

open LinearMap (BilinForm)
open scoped Matrix

namespace MorseFloer
namespace Chapter7

/-! ## §7.1.c The subset `Sp(2n)⋆`

The transformations relevant to the index are the symplectic ones without the
eigenvalue `1`; they form the open set `Sp(2n)⋆`, the complement in `Sp(2n)` of
the "hypersurface" `Σ` of matrices that do have it.  Since `det(A − Id)` is a
continuous nowhere-zero function on `Sp(2n)⋆`, that set is split by its sign
into the two open pieces `Sp(2n)+` and `Sp(2n)−`. -/

section Star

/-- `Sp(2n)⋆`, the symplectic matrices without the eigenvalue `1` (§7.1.c). -/
def symplecticStar (l : Type*) [DecidableEq l] [Fintype l] :
    Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  {A | A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det ≠ 0}

/-- `Sp(2n)+`, the part of `Sp(2n)⋆` where `det(A − Id) > 0` (§7.1.c). -/
def symplecticPlus (l : Type*) [DecidableEq l] [Fintype l] :
    Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  {A | A ∈ Matrix.symplecticGroup l ℝ ∧ 0 < (A - 1).det}

/-- `Sp(2n)−`, the part of `Sp(2n)⋆` where `det(A − Id) < 0` (§7.1.c). -/
def symplecticMinus (l : Type*) [DecidableEq l] [Fintype l] :
    Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  {A | A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det < 0}

/-- `Σ`, the symplectic matrices that *do* have the eigenvalue `1` (§7.1.c). -/
def sigmaSet (l : Type*) [DecidableEq l] [Fintype l] :
    Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  {A | A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det = 0}

variable {l : Type*} [DecidableEq l] [Fintype l] {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}

theorem mem_symplecticStar_iff :
    A ∈ symplecticStar l ↔ A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det ≠ 0 := Iff.rfl

theorem mem_symplecticPlus_iff :
    A ∈ symplecticPlus l ↔ A ∈ Matrix.symplecticGroup l ℝ ∧ 0 < (A - 1).det := Iff.rfl

theorem mem_symplecticMinus_iff :
    A ∈ symplecticMinus l ↔ A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det < 0 := Iff.rfl

theorem mem_sigmaSet_iff :
    A ∈ sigmaSet l ↔ A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det = 0 := Iff.rfl

/-- `Sp(2n)⋆` is the union of the two open pieces `Sp(2n)±`; in particular it is
not connected (§7.1.c). -/
theorem symplecticStar_eq_union :
    symplecticStar l = symplecticPlus l ∪ symplecticMinus l := by
  ext B
  simp only [mem_symplecticStar_iff, mem_symplecticPlus_iff, mem_symplecticMinus_iff,
    Set.mem_union]
  constructor
  · rintro ⟨hB, hne⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨hB, h⟩
    · exact Or.inl ⟨hB, h⟩
  · rintro (⟨hB, h⟩ | ⟨hB, h⟩)
    · exact ⟨hB, ne_of_gt h⟩
    · exact ⟨hB, ne_of_lt h⟩

/-- The two pieces of `Sp(2n)⋆` are disjoint. -/
theorem disjoint_symplecticPlus_minus :
    Disjoint (symplecticPlus l) (symplecticMinus l) := by
  rw [Set.disjoint_left]
  rintro B ⟨-, h1⟩ ⟨-, h2⟩
  exact absurd h1 (not_lt.mpr h2.le)

/-- `Sp(2n)` is the disjoint union of `Σ` and `Sp(2n)⋆`. -/
theorem symplecticGroup_eq_union :
    (Matrix.symplecticGroup l ℝ : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ))
      = sigmaSet l ∪ symplecticStar l := by
  ext B
  simp only [SetLike.mem_coe, mem_sigmaSet_iff, mem_symplecticStar_iff, Set.mem_union]
  constructor
  · intro hB
    by_cases h : (B - 1).det = 0
    · exact Or.inl ⟨hB, h⟩
    · exact Or.inr ⟨hB, h⟩
  · rintro (⟨hB, -⟩ | ⟨hB, -⟩) <;> exact hB

theorem disjoint_sigmaSet_symplecticStar :
    Disjoint (sigmaSet l) (symplecticStar l) := by
  rw [Set.disjoint_left]
  rintro B ⟨-, h1⟩ ⟨-, h2⟩
  exact h2 h1

/-- The reference matrix `W⁺ = −Id` of §7.2.a lies in `Sp(2n)+`: indeed
`det(−Id − Id) = (−2)^{2n} > 0`. -/
theorem neg_one_mem_symplecticPlus :
    (-1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) ∈ symplecticPlus l := by
  refine mem_symplecticPlus_iff.mpr ⟨SymplecticGroup.neg_mem (Submonoid.one_mem _), ?_⟩
  have h : (-1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) - 1 = (-2 : ℝ) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by
    rw [show (-2 : ℝ) = (-1) + (-1) by norm_num, add_smul, neg_one_smul]
    abel
  rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_sum]
  have hne : ((-2 : ℝ) ^ Fintype.card l) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc (0 : ℝ) < ((-2 : ℝ) ^ Fintype.card l) * ((-2 : ℝ) ^ Fintype.card l) :=
        mul_self_pos.mpr hne
    _ = (-2 : ℝ) ^ (Fintype.card l + Fintype.card l) := (pow_add _ _ _).symm

end Star

/-! ### The spectrum of a symplectic matrix

Proposition 5.6.3 says that `Aᵀ` and `A⁻¹` are conjugate by `J`; Mathlib packages
this as `SymplecticGroup.inv_eq_symplectic_inv`.  Combined with `det A = 1` it
gives Proposition 5.6.4, the symmetry `λ ↦ λ⁻¹` of the characteristic
polynomial, which `Part2/Ch5.lean` leaves as an assumption and which is proved
here. -/

section Spectrum

variable {l : Type*} [DecidableEq l] [Fintype l] {K : Type*} [Field K]
variable {A : Matrix (l ⊕ l) (l ⊕ l) K}

/-- A symplectic matrix has a symplectic inverse.  (Mathlib knows that
`symplecticGroup` is a group; this transports it to `Matrix.inv`.) -/
theorem inv_mem_symplecticGroup (hA : A ∈ Matrix.symplecticGroup l K) :
    A⁻¹ ∈ Matrix.symplecticGroup l K := by
  have h := (⟨A, hA⟩ : Matrix.symplecticGroup l K)⁻¹.2
  rwa [SymplecticGroup.coe_inv'] at h

/-- For a symplectic `A` and any scalar `c`, `det(A⁻¹ − c) = det(A − c)`: indeed
`A⁻¹ = (−J) Aᵀ J`, conjugation does not change the determinant, and neither does
transposition.  This is the computational content of Proposition 5.6.3. -/
theorem det_inv_sub_smul (hA : A ∈ Matrix.symplecticGroup l K) (c : K) :
    (A⁻¹ - c • 1).det = (A - c • 1).det := by
  have hinv : A⁻¹ = (-Matrix.J l K) * Aᵀ * Matrix.J l K :=
    SymplecticGroup.inv_eq_symplectic_inv A hA
  have hJJ : (-Matrix.J l K) * Matrix.J l K = 1 := by
    rw [Matrix.neg_mul, Matrix.J_squared, neg_neg]
  have hstep : (-Matrix.J l K) * (Aᵀ - c • 1) * Matrix.J l K = A⁻¹ - c • 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hinv]
    congr 1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hJJ]
  have htr : Aᵀ - c • 1 = (A - c • 1)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  have hdetJ : (-Matrix.J l K).det * (Matrix.J l K).det = 1 := by
    rw [← Matrix.det_mul, hJJ, Matrix.det_one]
  rw [← hstep, Matrix.det_mul, Matrix.det_mul, htr, Matrix.det_transpose]
  calc (-Matrix.J l K).det * (A - c • 1).det * (Matrix.J l K).det
      = ((-Matrix.J l K).det * (Matrix.J l K).det) * (A - c • 1).det := by ring
    _ = (A - c • 1).det := by rw [hdetJ, one_mul]

/-- `det(A⁻¹ − c⁻¹) = (−c⁻¹)^{2n} det(A − c)`, from `A⁻¹ − c⁻¹ = −c⁻¹ A⁻¹(A − c)`
and `det A = 1`. -/
theorem det_inv_sub_inv_smul (hA : A ∈ Matrix.symplecticGroup l K) {c : K} (hc : c ≠ 0) :
    (A⁻¹ - c⁻¹ • 1).det = (-c⁻¹) ^ Fintype.card (l ⊕ l) * (A - c • 1).det := by
  have hdet : A.det = 1 := SymplecticGroup.det_eq_one hA
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hinvdet : A⁻¹.det = 1 := by
    have h := Matrix.det_nonsing_inv_mul_det A hu
    rw [hdet, mul_one] at h
    exact h
  have h1 : A⁻¹ * (A - c • 1) = 1 - c • A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul A hu, Matrix.mul_smul, Matrix.mul_one]
  have hstep : (-c⁻¹) • (A⁻¹ * (A - c • 1)) = A⁻¹ - c⁻¹ • 1 := by
    rw [h1, smul_sub, smul_smul, show (-c⁻¹) * c = -1 from by
      rw [neg_mul, inv_mul_cancel₀ hc], neg_one_smul, neg_smul, sub_neg_eq_add]
    abel
  rw [← hstep, Matrix.det_smul, Matrix.det_mul, hinvdet, one_mul]

/-- **Proposition 5.6.4** (left as an assumption in Chapter 5, proved here).
The characteristic polynomial of a symplectic matrix is symmetric under
`λ ↦ λ⁻¹`: `det(A − λ⁻¹ Id) = (−λ⁻¹)^{2n} det(A − λ Id)`. -/
theorem det_sub_inv_smul (hA : A ∈ Matrix.symplecticGroup l K) {c : K} (hc : c ≠ 0) :
    (A - c⁻¹ • 1).det = (-c⁻¹) ^ Fintype.card (l ⊕ l) * (A - c • 1).det :=
  (det_inv_sub_smul hA c⁻¹).symm.trans (det_inv_sub_inv_smul hA hc)

/-- **Proposition 5.6.4** in the exact shape Chapter 5 states it.

Chapter 5 leaves this assumed because it cannot import this file (Chapter 7
imports Chapter 5, not the other way round); it is proved here, so the result is
available to the project even though `Chapter5.det_charpoly_symmetric` stays a
`sorry` in place.  The two forms agree because `2n` is even, which turns the
sign `(−λ⁻¹)^{2n}` of `det_sub_inv_smul` into `λ^{-2n}`. -/
theorem det_charpoly_symmetric (hA : A ∈ Matrix.symplecticGroup l K) {lam : K}
    (hlam : lam ≠ 0) :
    (A - lam • (1 : Matrix (l ⊕ l) (l ⊕ l) K)).det
      = lam ^ Fintype.card (l ⊕ l)
        * (A - lam⁻¹ • (1 : Matrix (l ⊕ l) (l ⊕ l) K)).det := by
  have hN : Even (Fintype.card (l ⊕ l)) := ⟨Fintype.card l, by rw [Fintype.card_sum]⟩
  have h := det_sub_inv_smul hA hlam
  rw [hN.neg_pow] at h
  rw [h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hlam, one_pow, one_mul]

/-- The spectrum of a symplectic matrix is invariant under `λ ↦ λ⁻¹` (§7.1.c,
Proposition 5.6.3). -/
theorem det_sub_smul_eq_zero_iff (hA : A ∈ Matrix.symplecticGroup l K) {c : K} (hc : c ≠ 0) :
    (A - c • 1).det = 0 ↔ (A - c⁻¹ • 1).det = 0 := by
  rw [det_sub_inv_smul hA hc]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero hc)))
    · exact h1

/-- `A` has the eigenvalue `1` exactly when `A⁻¹` does; so `Sp(2n)⋆` is stable
under inversion, and `det(A⁻¹ − Id) = det(A − Id)` means `A` and `A⁻¹` even lie
in the same component. -/
theorem det_inv_sub_one (hA : A ∈ Matrix.symplecticGroup l K) :
    (A⁻¹ - 1).det = (A - 1).det := by
  simpa using det_inv_sub_smul hA (1 : K)

end Spectrum

/-! ## §7.1.a First step

Given a nondegenerate contractible `1`-periodic orbit, the book trivialises the
symplectic bundle along a capping disc (Theorem 7.1.1) and reads the
differential of the flow in the resulting symplectic frames; this produces a
path `t ↦ A t` in `Sp(2n)` with `A 0 = Id` and `A 1 ∈ Sp(2n)⋆`, well defined up
to homotopy.  Theorem 7.1.1 and this construction have no Lean statement here
(see the module docstring).

Remark 7.1.2 is the autonomous case, where the path is explicit:
`A t = exp(t J S)` with `S` the Hessian of the Hamiltonian at the critical
point.  That such a path is symplectic *is* provable. -/

section ExpPath

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- **Remark 7.1.2.**  For a symmetric `S`, `t ↦ exp(t J S)` is a path in the
symplectic group: this is the linearised flow of an autonomous Hamiltonian at a
critical point, with `S` its Hessian.  It also proves Exercise 15 of the book,
quoted in §7.2.c. -/
theorem exp_smul_J_mul_mem_symplecticGroup {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : Sᵀ = S)
    (t : ℝ) : NormedSpace.exp (t • (Matrix.J l ℝ * S)) ∈ Matrix.symplecticGroup l ℝ := by
  refine Chapter5.exp_mem_symplecticGroup ?_
  have h1 : (Matrix.J l ℝ * S)ᵀ * Matrix.J l ℝ = S := by
    rw [Matrix.transpose_mul, hS, Matrix.J_transpose, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, Matrix.J_squared, Matrix.mul_neg, Matrix.mul_one, neg_neg]
  have h2 : Matrix.J l ℝ * (Matrix.J l ℝ * S) = -S := by
    rw [← Matrix.mul_assoc, Matrix.J_squared, Matrix.neg_mul, Matrix.one_mul]
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, h1, h2, smul_neg,
    add_neg_cancel]

/-- The path of Remark 7.1.2 starts at the identity. -/
theorem exp_smul_J_mul_zero (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    NormedSpace.exp ((0 : ℝ) • (Matrix.J l ℝ * S)) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

/-- **Remark 7.1.2** (second half).  If `S` is symmetric, invertible, and all its
eigenvalues have absolute value `< 2π`, then `J S` has no eigenvalue `2ikπ` and
therefore `exp(J S)` does not have the eigenvalue `1`, i.e. the endpoint of the
path lies in `Sp(2n)⋆`.

Not proved: this needs the spectral theorem for `S`, the description of the
spectrum of `exp` in terms of the spectrum of the matrix, and the fact that the
eigenvalues of `J S` are purely imaginary multiples of those of `S` — none of
which is available in a usable form. -/
theorem exp_J_mul_mem_symplecticStar {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (_hS : Sᵀ = S)
    (_hdet : S.det ≠ 0)
    (_hnorm : ∀ c : ℝ, (S - c • 1).det = 0 → |c| < 2 * Real.pi) :
    NormedSpace.exp ((1 : ℝ) • (Matrix.J l ℝ * S)) ∈ symplecticStar l := by
  sorry

end ExpPath

/-! ## §7.1.b Second step: the map `ρ : Sp(2n) → S¹`

Theorem 7.1.3 asserts the existence of a continuous `ρ : Sp(2n) → S¹` which is
invariant under symplectic conjugation, multiplicative for block sums, equal to
the complex determinant on the unitary matrices, equal to `(−1)^{m₀/2}` when the
spectrum is real, and satisfies `ρ(Aᵀ) = ρ(A⁻¹) = conj ρ(A)`.  The construction
is the content of the appendix §7.3 and is not available here; the properties
are recorded as a predicate. -/

section Rho

/-- The reindexing `(Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n) ≃ Fin (m+n) ⊕ Fin (m+n)`
which turns a pair of symplectic vector spaces into their direct sum, matching
the splitting `p`-coordinates / `q`-coordinates on both sides. -/
def blockSumEquiv (m n : ℕ) :
    (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n) ≃ Fin (m + n) ⊕ Fin (m + n) :=
  (Equiv.sumSumSumComm (Fin m) (Fin m) (Fin n) (Fin n)).trans
    (finSumFinEquiv.sumCongr finSumFinEquiv)

/-- The block sum `A ⊕ B` of a `2m × 2m` and a `2n × 2n` matrix, read as a
`2(m+n) × 2(m+n)` matrix in the standard symplectic coordinates. -/
def blockSum {m n : ℕ} (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    Matrix (Fin (m + n) ⊕ Fin (m + n)) (Fin (m + n) ⊕ Fin (m + n)) ℝ :=
  Matrix.reindex (blockSumEquiv m n) (blockSumEquiv m n) (Matrix.fromBlocks A 0 0 B)

/-- The total multiplicity of the negative real eigenvalues of a real matrix,
counted on the real characteristic polynomial; this is the `m₀` of §7.3.b. -/
noncomputable def negEigenCount {m : Type*} [DecidableEq m] [Fintype m]
    (A : Matrix m m ℝ) : ℕ :=
  Multiset.countP (fun x : ℝ => x < 0) A.charpoly.roots

/-- The total multiplicity of the positive real eigenvalues of a real matrix. -/
noncomputable def posEigenCount {m : Type*} [DecidableEq m] [Fintype m]
    (A : Matrix m m ℝ) : ℕ :=
  Multiset.countP (fun x : ℝ => 0 < x) A.charpoly.roots

/-- "`Spec A ⊆ ℝ`": the characteristic polynomial splits over `ℝ`, i.e. it has as
many real roots, with multiplicity, as the size of the matrix. -/
def HasRealSpectrum {m : Type*} [DecidableEq m] [Fintype m] (A : Matrix m m ℝ) : Prop :=
  A.charpoly.roots.card = Fintype.card m

/-- **Theorem 7.1.3.**  The five characteristic properties of the map
`ρ : Sp(2n) → S¹`, stated for a family of maps indexed by `n` so that the
multiplicativity under block sums can be expressed.

`ρ` takes values in the unit circle of `ℂ`; it is continuous on the symplectic
group, invariant under symplectic conjugation, multiplicative for block sums,
given on the unitary matrices `A = [[X, −Y], [Y, X]]` by the complex determinant
of `X + iY`, equal to `(−1)^{m₀/2}` when all eigenvalues are real (with `m₀` the
total multiplicity of the negative ones), and it turns transposition into
inversion and inversion into complex conjugation.

The book adds that `ρ` induces an isomorphism `π₁(Sp(2n)) ≃ π₁(S¹) = ℤ`; that
clause is not part of this predicate because Chapter 5 already records
`π₁(Sp(2n)) ≃ ℤ` as beyond reach. -/
structure IsRho (ρ : ∀ n : ℕ, Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℂ) : Prop where
  /-- `ρ` is continuous on the symplectic group. -/
  continuousOn : ∀ n : ℕ, ContinuousOn (ρ n) (Matrix.symplecticGroup (Fin n) ℝ)
  /-- `ρ` takes its values in the unit circle. -/
  norm_eq_one : ∀ (n : ℕ) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    A ∈ Matrix.symplecticGroup (Fin n) ℝ → ‖ρ n A‖ = 1
  /-- Naturality: `ρ(T A T⁻¹) = ρ(A)` for symplectic `T`. -/
  naturality : ∀ (n : ℕ) (A T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    A ∈ Matrix.symplecticGroup (Fin n) ℝ → T ∈ Matrix.symplecticGroup (Fin n) ℝ →
    ρ n (T * A * T⁻¹) = ρ n A
  /-- Product: `ρ` is multiplicative for block sums. -/
  blockSum_eq : ∀ (m n : ℕ) (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    A ∈ Matrix.symplecticGroup (Fin m) ℝ → B ∈ Matrix.symplecticGroup (Fin n) ℝ →
    ρ (m + n) (blockSum A B) = ρ m A * ρ n B
  /-- Determinant: on `U(n) = Sp(2n) ∩ O(2n)`, `ρ` is the complex determinant. -/
  det_unitary : ∀ (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℝ),
    Matrix.fromBlocks X (-Y) Y X ∈ Matrix.symplecticGroup (Fin n) ℝ →
    Chapter5.IsOrthogonalMat (Matrix.fromBlocks X (-Y) Y X) →
    ρ n (Matrix.fromBlocks X (-Y) Y X)
      = (X.map (fun r : ℝ => (r : ℂ)) + Complex.I • Y.map (fun r : ℝ => (r : ℂ))).det
  /-- Normalisation: if the spectrum is real, `ρ(A) = (−1)^{m₀/2}`. -/
  normalisation : ∀ (n : ℕ) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    A ∈ Matrix.symplecticGroup (Fin n) ℝ → HasRealSpectrum A →
    ρ n A = (-1 : ℂ) ^ (negEigenCount A / 2)
  /-- `ρ(Aᵀ) = ρ(A⁻¹)`. -/
  map_transpose : ∀ (n : ℕ) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    A ∈ Matrix.symplecticGroup (Fin n) ℝ → ρ n Aᵀ = ρ n A⁻¹
  /-- `ρ(A⁻¹) = conj ρ(A)`. -/
  map_inv : ∀ (n : ℕ) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    A ∈ Matrix.symplecticGroup (Fin n) ℝ → ρ n A⁻¹ = (starRingEnd ℂ) (ρ n A)

/-- **Theorem 7.1.3** (existence).  Such a `ρ` exists.

Not proved.  The construction of §7.3.b reads off the generalised eigenspaces of
a symplectic matrix, splits each `E_λ` for `λ` on the unit circle into the
maximal subspaces on which `Q(X) = Im ω(X, X̄)` is positive resp. negative
definite, and forms `(−1)^{m₀/2} ∏ λ^{m₊(λ)}`; proving that this is continuous
takes the whole of §7.3.c.  Mathlib provides neither the signature of a
quadratic form on a varying subspace nor the continuity of eigenvalues and of
characteristic subspaces. -/
theorem exists_isRho : ∃ ρ, IsRho ρ := by
  sorry

variable {ρ : ∀ n : ℕ, Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℂ}

/-- `ρ(Id) = 1`, from the determinant property applied to `X = Id`, `Y = 0`. -/
theorem IsRho.map_one (h : IsRho ρ) (n : ℕ) : ρ n 1 = 1 := by
  have hb : Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-0) 0 1
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
    rw [neg_zero]; exact Matrix.fromBlocks_one
  have hmem : Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-0) 0 1
      ∈ Matrix.symplecticGroup (Fin n) ℝ := by rw [hb]; exact Submonoid.one_mem _
  have horth : (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-0)
        (0 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ *
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-0)
        (0 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    rw [hb, Matrix.transpose_one, Matrix.one_mul]
  have key := h.det_unitary n 1 0 hmem horth
  rw [hb] at key
  have hmap0 : ((0 : Matrix (Fin n) (Fin n) ℝ).map (fun r : ℝ => (r : ℂ))) = 0 := by
    ext i j; simp
  have hmap1 : ((1 : Matrix (Fin n) (Fin n) ℝ).map (fun r : ℝ => (r : ℂ))) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [key, hmap0, smul_zero, add_zero, hmap1, Matrix.det_one]

/-- `ρ(−Id) = (−1)ⁿ`.  This is the value `ρ(W⁺)` used in the proof of
Proposition 7.2.1. -/
theorem IsRho.map_neg_one (h : IsRho ρ) (n : ℕ) : ρ n (-1) = (-1) ^ n := by
  have hb : Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) ℝ) (-0) 0 (-1)
      = (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  have hmem : Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) ℝ) (-0) 0 (-1)
      ∈ Matrix.symplecticGroup (Fin n) ℝ := by
    rw [hb]; exact SymplecticGroup.neg_mem (Submonoid.one_mem _)
  have horth : (Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) ℝ) (-0)
        (0 : Matrix (Fin n) (Fin n) ℝ) (-1 : Matrix (Fin n) (Fin n) ℝ))ᵀ *
      Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) ℝ) (-0)
        (0 : Matrix (Fin n) (Fin n) ℝ) (-1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    rw [hb, Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.one_mul, neg_neg]
  have key := h.det_unitary n (-1) 0 hmem horth
  rw [hb] at key
  have hmap : ((-1 : Matrix (Fin n) (Fin n) ℝ).map (fun r : ℝ => (r : ℂ)))
      = (-1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hmap0 : ((0 : Matrix (Fin n) (Fin n) ℝ).map (fun r : ℝ => (r : ℂ))) = 0 := by
    ext i j; simp
  rw [key, hmap0, smul_zero, add_zero, hmap, Matrix.det_neg,
    Matrix.det_one, mul_one, Fintype.card_fin]

end Rho

/-! ### Proposition 7.1.4 and the two lemmas it rests on -/

section Components

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- **Lemma 7.1.5.**  Every `A ∈ Sp(2n)⋆` can be joined, inside `Sp(2n)⋆`, to a
symplectic matrix with pairwise distinct eigenvalues and with exactly zero
positive real eigenvalues if `A ∈ Sp(2n)+`, exactly two if `A ∈ Sp(2n)−`.

Not proved.  The book's argument perturbs a multiple eigenvalue at a time,
choosing at each stage a symplectic basis of a characteristic subspace adapted
to complex conjugation and modifying `A` only there.  Formalizing it needs
symplectic bases of generalised eigenspaces of a symplectic matrix over `ℂ`, the
symplectic orthogonal complement of such a subspace, and Proposition 5.6.6 in
full — all of which is missing (Chapter 5 proves 5.6.6 only for genuine
eigenvectors). -/
theorem exists_joinedIn_symplecticStar_distinct (A : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (_hA : A ∈ symplecticStar l) :
    ∃ B ∈ symplecticStar l, JoinedIn (symplecticStar l) A B ∧
      (B.map (fun r : ℝ => (r : ℂ))).charpoly.roots.Nodup ∧
      ((A ∈ symplecticPlus l ∧ posEigenCount B = 0) ∨
        (A ∈ symplecticMinus l ∧ posEigenCount B = 2)) := by
  sorry

/-- **Proposition 7.1.4** (first half).  `Sp(2n)+` is path-connected: by
Lemma 7.1.5 every matrix in it can be joined inside `Sp(2n)⋆` to one with
distinct eigenvalues and no positive real eigenvalue, and then to `W⁺ = −Id`.

Not proved: it rests on Lemma 7.1.5. -/
theorem isPathConnected_symplecticPlus [Nonempty l] :
    IsPathConnected (symplecticPlus l) := by
  sorry

/-- **Proposition 7.1.4** (second half).  `Sp(2n)−` is path-connected.

Not proved: it rests on Lemma 7.1.5. -/
theorem isPathConnected_symplecticMinus [Nonempty l] :
    IsPathConnected (symplecticMinus l) := by
  sorry

end Components

section Lifts

variable {ρ : ∀ n : ℕ, Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℂ}

/-- **Lemma 7.1.6.**  On each of `Sp(2n)±` the map `ρ` admits a continuous
real-valued lift through `θ ↦ e^{iθ}`.  This is what makes the inclusions
`Sp(2n)± ↪ Sp(2n)` trivial on fundamental groups, hence what makes the class of
the connecting path `γ_A` of §7.2.a well defined.

Not proved.  The lift is written down in §7.3.d from the explicit formula for
`ρ` in terms of arguments of the eigenvalues on the unit circle, and its
continuity is checked by the same four-case analysis that proves the continuity
of `ρ`; the formula for `ρ` is not available here. -/
theorem exists_lift_symplecticPlus (_hρ : IsRho ρ) (n : ℕ) :
    ∃ f : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℝ,
      ContinuousOn f (symplecticPlus (Fin n)) ∧
      ∀ A ∈ symplecticPlus (Fin n), Complex.exp (f A * Complex.I) = ρ n A := by
  sorry

/-- **Lemma 7.1.6** for the other component.  Not proved, for the same reason. -/
theorem exists_lift_symplecticMinus (_hρ : IsRho ρ) (n : ℕ) :
    ∃ f : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℝ,
      ContinuousOn f (symplecticMinus (Fin n)) ∧
      ∀ A ∈ symplecticMinus (Fin n), Complex.exp (f A * Complex.I) = ρ n A := by
  sorry

end Lifts

/-! ## §7.2.a The Maslov index of a path

For a path `γ` in `Sp(2n)` one lifts `ρ ∘ γ` to a real-valued `α` and sets
`Δ(γ) = (α 1 − α 0)/π`, the number of half-turns of `ρ ∘ γ`.  For
`A ∈ Sp(2n)⋆` one sets `r(A) = Δ(γ_A)` for a path `γ_A` joining `A` to the
reference matrix of its component; Proposition 7.1.4 makes this well defined.
Finally `μ(ψ) = Δ(ψ) + r(ψ 1)`.

Constructing `Δ` requires the lifting theory that is missing, so this file
defines `Δ` relative to a chosen lift, states its independence of that choice,
and then records the properties of `μ` axiomatically. -/

section Delta

/-- `α` is a continuous real lift of `u : ℝ → S¹` through `θ ↦ e^{iθ}`. -/
def IsAngleLift (u : ℝ → ℂ) (α : ℝ → ℝ) : Prop :=
  Continuous α ∧ ∀ t, Complex.exp (α t * Complex.I) = u t

/-- `Δ(γ) = (α 1 − α 0)/π`, the number of half-turns of `ρ ∘ γ` on the circle,
computed from a lift `α` of `ρ ∘ γ`. -/
noncomputable def Delta (α : ℝ → ℝ) : ℝ := (α 1 - α 0) / Real.pi

/-- `Δ` does not depend on the chosen lift.

Not proved.  Two lifts differ by a continuous function with values in `2πℤ`,
which is constant because the interval is connected — that is unique path
lifting for the covering `θ ↦ e^{iθ}`, which Mathlib does not provide in a form
applicable here (`IsCoveringMap` exists, but not for this map). -/
theorem Delta_eq_of_isAngleLift {u : ℝ → ℂ} {α β : ℝ → ℝ}
    (_hα : IsAngleLift u α) (_hβ : IsAngleLift u β) : Delta α = Delta β := by
  sorry

end Delta

section Index

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The space `S` of §7.1.c: paths of symplectic matrices starting at the
identity and ending in `Sp(2n)⋆`.  Only the values on `[0,1]` matter; the
functions are defined on all of `ℝ` to avoid subtype friction. -/
structure IsAdmissiblePath (ψ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) : Prop where
  /-- The path is continuous. -/
  continuous : Continuous ψ
  /-- It takes symplectic values. -/
  mem : ∀ t, ψ t ∈ Matrix.symplecticGroup l ℝ
  /-- It starts at the identity. -/
  start : ψ 0 = 1
  /-- Its endpoint has no eigenvalue `1`. -/
  endpoint : ψ 1 ∈ symplecticStar l

/-- Homotopy inside `S`: a continuous family of admissible paths. -/
def HomotopicInS (ψ₀ ψ₁ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) : Prop :=
  ∃ H : ℝ → ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ,
    Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧ (∀ s, IsAdmissiblePath (H s)) ∧
      H 0 = ψ₀ ∧ H 1 = ψ₁

end Index

section ConleyZehnder

/-- **Proposition 7.2.1**, read as the defining properties of the Maslov, or
Conley–Zehnder, index of a path.

`μ n ψ` is an integer attached to an admissible path of `2n × 2n` symplectic
matrices, and:

* two admissible paths are homotopic in `S` exactly when they have the same
  index;
* the sign of `det(ψ 1 − Id)` is `(−1)^{μ(ψ) − n}`, which is what the two
  connected components of `Sp(2n)⋆` contribute;
* for a symmetric invertible `S` all of whose eigenvalues are smaller than `2π`
  in absolute value (the book writes `‖S‖ < 2π`), the path `exp(tJS)` has index
  `Ind(S) − n`, where `Ind(S)` is the number of negative eigenvalues of `S`;
* the index is additive under block sums, which is how the multiplicativity of
  `ρ` is used in the book's computation.

The normalisation clause is stated with the spectral form of `‖S‖ < 2π` because
Mathlib has no canonical norm on matrices — all its matrix norms are scoped
instances — and for a symmetric matrix the operator norm is the largest
absolute value of an eigenvalue. -/
structure IsConleyZehnderIndex
    (μ : ∀ n : ℕ, (ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) → ℤ) : Prop where
  /-- Homotopy invariance, and its converse. -/
  homotopy : ∀ (n : ℕ) (ψ₀ ψ₁ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    IsAdmissiblePath ψ₀ → IsAdmissiblePath ψ₁ →
    (HomotopicInS ψ₀ ψ₁ ↔ μ n ψ₀ = μ n ψ₁)
  /-- The sign of `det(ψ 1 − Id)` is `(−1)^{μ(ψ) − n}`. -/
  sign : ∀ (n : ℕ) (ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    IsAdmissiblePath ψ → 0 < (-1 : ℝ) ^ (μ n ψ - (n : ℤ)) * (ψ 1 - 1).det
  /-- Normalisation on the paths `exp(tJS)` of a small symmetric matrix. -/
  normalisation : ∀ (n : ℕ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    Sᵀ = S → S.det ≠ 0 → (∀ c : ℝ, (S - c • 1).det = 0 → |c| < 2 * Real.pi) →
    μ n (fun t => NormedSpace.exp (t • (Matrix.J (Fin n) ℝ * S)))
      = (negEigenCount S : ℤ) - (n : ℤ)
  /-- Additivity under block sums. -/
  additivity : ∀ (m n : ℕ) (ψ₀ : ℝ → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (ψ₁ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    IsAdmissiblePath ψ₀ → IsAdmissiblePath ψ₁ →
    μ (m + n) (fun t => blockSum (ψ₀ t) (ψ₁ t)) = μ m ψ₀ + μ n ψ₁

/-- **Proposition 7.2.1** (existence).  The Maslov index exists.

Not proved.  Its construction is `μ(ψ) = Δ(ψ) + r(ψ 1)`, which needs the map
`ρ` of Theorem 7.1.3, the lifting of `ρ ∘ ψ` to `ℝ`, and Proposition 7.1.4 to
know that the connecting path `γ_A` has a well-defined homotopy class. -/
theorem exists_isConleyZehnderIndex : ∃ μ, IsConleyZehnderIndex μ := by
  sorry

variable {μ : ∀ n : ℕ, (ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) → ℤ}

/-- **Proposition 7.2.1** (homotopy clause), restated. -/
theorem homotopicInS_iff_index_eq (hμ : IsConleyZehnderIndex μ) (n : ℕ)
    {ψ₀ ψ₁ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (h₀ : IsAdmissiblePath ψ₀) (h₁ : IsAdmissiblePath ψ₁) :
    HomotopicInS ψ₀ ψ₁ ↔ μ n ψ₀ = μ n ψ₁ :=
  hμ.homotopy n ψ₀ ψ₁ h₀ h₁

/-- If the endpoint of `ψ` lies in `Sp(2n)+` then `μ(ψ) − n` is even.  This is
the parity half of Proposition 7.2.1, deduced formally from the sign axiom. -/
theorem even_index_sub_of_endpoint_mem_plus (hμ : IsConleyZehnderIndex μ) (n : ℕ)
    {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hψ : IsAdmissiblePath ψ)
    (h : ψ 1 ∈ symplecticPlus (Fin n)) : Even (μ n ψ - (n : ℤ)) := by
  have hs := hμ.sign n ψ hψ
  have hd : 0 < (ψ 1 - 1).det := (mem_symplecticPlus_iff.mp h).2
  rcases Int.even_or_odd (μ n ψ - (n : ℤ)) with he | ho
  · exact he
  · exfalso
    rw [Odd.neg_one_zpow ho] at hs
    linarith

/-- If the endpoint of `ψ` lies in `Sp(2n)−` then `μ(ψ) − n` is odd. -/
theorem odd_index_sub_of_endpoint_mem_minus (hμ : IsConleyZehnderIndex μ) (n : ℕ)
    {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hψ : IsAdmissiblePath ψ)
    (h : ψ 1 ∈ symplecticMinus (Fin n)) : Odd (μ n ψ - (n : ℤ)) := by
  have hs := hμ.sign n ψ hψ
  have hd : (ψ 1 - 1).det < 0 := (mem_symplecticMinus_iff.mp h).2
  rcases Int.even_or_odd (μ n ψ - (n : ℤ)) with he | ho
  · exfalso
    rw [Even.neg_one_zpow he] at hs
    linarith
  · exact ho

/-- **Corollary 7.2.2.**  For an autonomous Hamiltonian and a stationary orbit at
a critical point `x` whose Hessian `S` is small (all eigenvalues `< 2π` in
absolute value) and nondegenerate, the Maslov index of `x` as a periodic orbit
and its Morse index as a critical point of `H` are related by `μ(x) = Ind(x) − n`.

Here `Ind(S)` is the number of negative eigenvalues of the Hessian, counted with
multiplicity — the Morse index of §1.3 read off the characteristic polynomial. -/
theorem conleyZehnder_eq_morseIndex_sub (hμ : IsConleyZehnderIndex μ) (n : ℕ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hS : Sᵀ = S) (hdet : S.det ≠ 0)
    (hsmall : ∀ c : ℝ, (S - c • 1).det = 0 → |c| < 2 * Real.pi) :
    μ n (fun t => NormedSpace.exp (t • (Matrix.J (Fin n) ℝ * S)))
      = (negEigenCount S : ℤ) - (n : ℤ) :=
  hμ.normalisation n S hS hdet hsmall

/-- **Lemma 7.2.4.**  For every integer `k` there is a diagonal symmetric matrix
`S_k` whose path `exp(t J S_k)` is admissible and has Maslov index `k`.  These
are the matrices reused in Chapter 8.

Not proved.  The book builds `S_k` out of `2 × 2` blocks and computes the index
by additivity, but the blocks it uses are *not* small in the sense of the
normalisation axiom (one of them is `(n − k − 1)π`), so the value cannot be read
off the axioms; the underlying `2 × 2` computations of `exp(tJS)` are themselves
unavailable. -/
theorem exists_symmetric_of_index (_hμ : IsConleyZehnderIndex μ) (n : ℕ) (_hn : 0 < n)
    (k : ℤ) :
    ∃ S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, Sᵀ = S ∧
      IsAdmissiblePath (fun t => NormedSpace.exp (t • (Matrix.J (Fin n) ℝ * S))) ∧
      μ n (fun t => NormedSpace.exp (t • (Matrix.J (Fin n) ℝ * S))) = k := by
  sorry

end ConleyZehnder

/-! ## §7.2.c Symplectic paths versus paths of symmetric matrices

Lemma 7.2.3 identifies the solutions of `R' = J S R`, `R 0 = Id`, for `S` a path
of symmetric matrices, with the `C¹` paths in `Sp(2n)`.  Both directions rest on
one algebraic identity, which is proved here; the differential statements
themselves are stated with entrywise derivatives (Mathlib has no canonical
normed-algebra structure on matrices) and left as assumptions. -/

section Lemma723

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- **Lemma 7.2.3** (algebraic core, forward direction).  If `S` is symmetric and
`D = J S R`, then `Dᵀ J R + Rᵀ J D = 0`; that is, the derivative of
`t ↦ R(t)ᵀ J R(t)` vanishes, so this expression is constant and `R` stays
symplectic. -/
theorem transpose_mul_J_add_of_symm {S R : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : Sᵀ = S) :
    (Matrix.J l ℝ * S * R)ᵀ * Matrix.J l ℝ * R
      + Rᵀ * Matrix.J l ℝ * (Matrix.J l ℝ * S * R) = 0 := by
  have hJJ : Matrix.J l ℝ * Matrix.J l ℝ = -1 := by rw [Matrix.J_squared]
  have h1 : (Matrix.J l ℝ * S * R)ᵀ = Rᵀ * (S * -Matrix.J l ℝ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hS, Matrix.J_transpose]
  rw [h1]
  have expand : Rᵀ * (S * -Matrix.J l ℝ) * Matrix.J l ℝ * R
      + Rᵀ * Matrix.J l ℝ * (Matrix.J l ℝ * S * R)
      = -(Rᵀ * S * (Matrix.J l ℝ * Matrix.J l ℝ) * R)
        + Rᵀ * (Matrix.J l ℝ * Matrix.J l ℝ) * (S * R) := by noncomm_ring
  rw [expand, hJJ]
  noncomm_ring

/-- **Lemma 7.2.3** (algebraic core, converse direction).  If `R` is invertible
and `Dᵀ J R + Rᵀ J D = 0` — the relation obtained by differentiating
`Rᵀ J R = J` — then `S = −J D R⁻¹` is symmetric. -/
theorem symm_of_transpose_mul_J_add {R D : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hR : IsUnit R.det)
    (h : Dᵀ * Matrix.J l ℝ * R + Rᵀ * Matrix.J l ℝ * D = 0) :
    (-(Matrix.J l ℝ * D * R⁻¹))ᵀ = -(Matrix.J l ℝ * D * R⁻¹) := by
  have hJT : (Matrix.J l ℝ)ᵀ = -Matrix.J l ℝ := by rw [Matrix.J_transpose]
  have hRR : (R⁻¹)ᵀ * Rᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv R hR, Matrix.transpose_one]
  have h' : Dᵀ * Matrix.J l ℝ * R = -(Rᵀ * Matrix.J l ℝ * D) := by
    rw [eq_neg_iff_add_eq_zero]; exact h
  have hDJ : Dᵀ * Matrix.J l ℝ = -(Rᵀ * Matrix.J l ℝ * D * R⁻¹) := by
    calc Dᵀ * Matrix.J l ℝ = Dᵀ * Matrix.J l ℝ * (R * R⁻¹) := by
          rw [Matrix.mul_nonsing_inv R hR, Matrix.mul_one]
      _ = Dᵀ * Matrix.J l ℝ * R * R⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = -(Rᵀ * Matrix.J l ℝ * D) * R⁻¹ := by rw [h']
      _ = -(Rᵀ * Matrix.J l ℝ * D * R⁻¹) := by rw [Matrix.neg_mul]
  calc (-(Matrix.J l ℝ * D * R⁻¹))ᵀ
      = -((R⁻¹)ᵀ * (Dᵀ * (Matrix.J l ℝ)ᵀ)) := by
        rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul]
    _ = (R⁻¹)ᵀ * (Dᵀ * Matrix.J l ℝ) := by rw [hJT]; noncomm_ring
    _ = (R⁻¹)ᵀ * (-(Rᵀ * Matrix.J l ℝ * D * R⁻¹)) := by rw [hDJ]
    _ = -(((R⁻¹)ᵀ * Rᵀ) * Matrix.J l ℝ * D * R⁻¹) := by noncomm_ring
    _ = -(Matrix.J l ℝ * D * R⁻¹) := by rw [hRR, Matrix.one_mul]

/-- **Lemma 7.2.3** (first half, differential form).  The solution of
`R' = J S R` with `R 0 = Id`, for a continuous path `S` of symmetric matrices,
takes symplectic values.

Not proved.  The algebraic identity behind it is
`transpose_mul_J_add_of_symm`; turning it into "`Rᵀ J R` is constant" needs
calculus for matrix-valued functions, which requires a normed algebra structure
on `Matrix` — Mathlib offers only scoped instances for that, so the hypothesis
is stated entrywise and the derivation of the product rule is not carried out. -/
theorem mem_symplecticGroup_of_hasDerivAt (R S : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (_hS : ∀ t, (S t)ᵀ = S t)
    (_hR : ∀ t i j, HasDerivAt (fun s => R s i j) ((Matrix.J l ℝ * S t * R t) i j) t)
    (_h0 : R 0 = 1) (t : ℝ) : R t ∈ Matrix.symplecticGroup l ℝ := by
  sorry

/-- **Lemma 7.2.3** (second half, differential form).  Conversely, for a `C¹` path
`R` in `Sp(2n)` the matrices `S t = −J R'(t) R(t)⁻¹` are symmetric.

Not proved, for the same reason; the algebraic content is
`symm_of_transpose_mul_J_add`, and what is missing is that differentiating the
constant function `t ↦ R(t)ᵀ J R(t) = J` gives `Dᵀ J R + Rᵀ J D = 0`. -/
theorem symm_of_hasDerivAt (R D : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (_hmem : ∀ t, R t ∈ Matrix.symplecticGroup l ℝ)
    (_hR : ∀ t i j, HasDerivAt (fun s => R s i j) (D t i j) t) (t : ℝ) :
    (-(Matrix.J l ℝ * D t * (R t)⁻¹))ᵀ = -(Matrix.J l ℝ * D t * (R t)⁻¹) := by
  sorry

end Lemma723

/-! ## The example of `Sp(2)` (§7.1.c)

For `n = 1` everything is explicit: `Sp(2) = SL(2; ℝ)`, the hypersurface `Σ` is
`{tr A = 2}`, and the two components of `Sp(2)⋆` are `{tr A < 2}` and
`{tr A > 2}`.  This is carried out here in the concrete model
`Matrix (Fin 2) (Fin 2) ℝ`, with `J₂ = [[0, −1], [1, 0]]`; it corresponds to
`Matrix.symplecticGroup (Fin 1) ℝ` under the reindexing `Fin 1 ⊕ Fin 1 ≃ Fin 2`. -/

section FinTwo

/-- The standard complex structure of `ℝ²`, i.e. `Matrix.J` for `n = 1`. -/
def J2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- `A` is symplectic in the `2 × 2` model. -/
def IsSymplectic2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop := Aᵀ * J2 * A = J2

/-- In dimension `2`, `Aᵀ J A = (det A) J` for every matrix. -/
theorem transpose_mul_J2_mul (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Aᵀ * J2 * A = A.det • J2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.transpose_apply,
      Matrix.smul_apply] <;> ring

/-- **Example 5.6.1 / §7.1.c.**  `Sp(2) = SL(2; ℝ)`. -/
theorem isSymplectic2_iff_det_eq_one (A : Matrix (Fin 2) (Fin 2) ℝ) :
    IsSymplectic2 A ↔ A.det = 1 := by
  rw [IsSymplectic2, transpose_mul_J2_mul]
  constructor
  · intro h
    have hJ01 : J2 0 1 = -1 := by simp [J2]
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    simp only [Matrix.smul_apply, smul_eq_mul, hJ01] at h01
    linarith
  · intro h; rw [h, one_smul]

/-- In dimension `2`, `det(A − Id) = det A − tr A + 1`. -/
theorem det_sub_one_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (A - 1).det = A.det - A.trace + 1 := by
  have e00 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have e11 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
  have e01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have e10 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply, e00, e01, e10, e11]
  ring

/-- **§7.1.c, the example of `Sp(2)`.**  For a symplectic `2 × 2` matrix,
`det(A − Id) = 2 − tr A`; so `Σ` is the set `{tr A = 2}` and the two components
of `Sp(2)⋆` are cut out by `tr A < 2` and `tr A > 2`. -/
theorem det_sub_one_fin_two_of_det_eq_one {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A.det = 1) :
    (A - 1).det = 2 - A.trace := by
  rw [det_sub_one_fin_two, h]; ring

theorem det_sub_one_pos_iff {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A.det = 1) :
    0 < (A - 1).det ↔ A.trace < 2 := by
  rw [det_sub_one_fin_two_of_det_eq_one h]
  constructor <;> intro hh <;> linarith

theorem det_sub_one_neg_iff {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A.det = 1) :
    (A - 1).det < 0 ↔ 2 < A.trace := by
  rw [det_sub_one_fin_two_of_det_eq_one h]
  constructor <;> intro hh <;> linarith

/-- The rotation of angle `θ`, an element of `U(1) ⊂ Sp(2)`. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem det_rot (θ : ℝ) : (rot θ).det = 1 := by
  rw [rot, Matrix.det_fin_two_of]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [this]

theorem trace_rot (θ : ℝ) : (rot θ).trace = 2 * Real.cos θ := by
  rw [rot, Matrix.trace_fin_two_of]; ring

/-- The rotations are symplectic, and every rotation other than the identity lies
in `Sp(2)+`: this is the circle onto which `SL(2; ℝ)` retracts. -/
theorem rot_mem_plus {θ : ℝ} (h : Real.cos θ < 1) : 0 < (rot θ - 1).det := by
  rw [det_sub_one_pos_iff (det_rot θ), trace_rot]
  linarith

/-- `−Id` is the rotation of angle `π`, and it lies in `Sp(2)+`. -/
theorem det_neg_one_sub_one_fin_two :
    ((-1 : Matrix (Fin 2) (Fin 2) ℝ) - 1).det = 4 := by
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num
  have htr : (-1 : Matrix (Fin 2) (Fin 2) ℝ).trace = -2 := by
    have e00 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
    have e11 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
    simp only [Matrix.trace_fin_two, Matrix.neg_apply, e00, e11]
    norm_num
  rw [det_sub_one_fin_two_of_det_eq_one hdet, htr]; norm_num

/-- The hyperbolic matrix `diag(λ, λ⁻¹)`. -/
noncomputable def hyp (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![lam, 0; 0, lam⁻¹]

theorem det_hyp {lam : ℝ} (h : lam ≠ 0) : (hyp lam).det = 1 := by
  rw [hyp, Matrix.det_fin_two_of, mul_inv_cancel₀ h]; ring

theorem trace_hyp (lam : ℝ) : (hyp lam).trace = lam + lam⁻¹ := by
  rw [hyp, Matrix.trace_fin_two_of]

/-- **§7.1.c.**  For `λ > 0`, `λ ≠ 1`, the matrix `diag(λ, λ⁻¹)` has trace `> 2`,
so it lies in `Sp(2)−`: these are exactly the matrices the book lists as
representing that component. -/
theorem hyp_mem_minus {lam : ℝ} (hpos : 0 < lam) (hne : lam ≠ 1) :
    (hyp lam - 1).det < 0 := by
  rw [det_sub_one_neg_iff (det_hyp (ne_of_gt hpos)), trace_hyp]
  have h1 : lam - 1 ≠ 0 := sub_ne_zero.mpr hne
  have h2 : 0 < (lam - 1) ^ 2 := lt_of_le_of_ne (sq_nonneg _) ((pow_ne_zero 2 h1).symm)
  have key : lam + lam⁻¹ - 2 = (lam - 1) ^ 2 / lam := by
    field_simp
    ring
  have h3 : 0 < (lam - 1) ^ 2 / lam := div_pos h2 hpos
  linarith [key, h3]

/-- The reference matrix `W⁻` of §7.2.a in the `2 × 2` model, `diag(2, 1/2)`; it
lies in `Sp(2)−`. -/
theorem W_minus_fin_two : (hyp 2 - 1).det < 0 :=
  hyp_mem_minus (by norm_num) (by norm_num)

/-- The three `2 × 2` computations of the proof of Proposition 7.2.1: for
`S = diag(π, π)`, `exp(tJS)` is the rotation of angle `−tπ`; for
`S = diag(−π, −π)` it is the rotation of angle `tπ`; for `S = diag(π, −π)` it is
a hyperbolic matrix with positive real eigenvalues `e^{±πt}`.

Not proved.  Mathlib has no closed form for the exponential of a `2 × 2` matrix
(`Matrix.exp_diagonal` handles only diagonal ones), and computing it here would
mean redoing the isomorphism between `{aI + bJ₂}` and `ℂ`. -/
theorem exp_rotation_fin_two (t : ℝ) :
    NormedSpace.exp (t • (J2 * (Real.pi • (1 : Matrix (Fin 2) (Fin 2) ℝ)))) = rot (-(t * Real.pi)) := by
  sorry

end FinTwo

/-! ## §7.3.a Preliminaries to the construction of `ρ`

On `ℂ²ⁿ`, the complex bilinear extension `ω` of the standard symplectic form
gives a *real* form `B(X, Y) = Im ω(X, Ȳ)`.  Lemma 7.3.1 says it is
`ℝ`-bilinear, symmetric and nondegenerate, and that it satisfies
`B(iX, iY) = B(X, Y)` and `B(X̄, Ȳ) = −B(X, Y)`.  These are the properties on
which the whole construction of `ρ` rests. -/

section Appendix

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The standard symplectic form of `ℂ²ⁿ`: the complex bilinear extension of the
real one, with the same matrix `−J`. -/
noncomputable def stdFormC (l : Type*) [DecidableEq l] [Fintype l] :
    BilinForm ℂ ((l ⊕ l) → ℂ) :=
  Matrix.toBilin' (-(Matrix.J l ℂ))

theorem stdFormC_apply (X Y : (l ⊕ l) → ℂ) :
    stdFormC l X Y = X ⬝ᵥ (-(Matrix.J l ℂ)) *ᵥ Y :=
  Matrix.toBilin'_apply' _ _ _

/-- Entrywise complex conjugation of a vector. -/
noncomputable def conjVec (X : (l ⊕ l) → ℂ) : (l ⊕ l) → ℂ := fun i => (starRingEnd ℂ) (X i)

omit [DecidableEq l] [Fintype l] in
@[simp] theorem conjVec_conjVec (X : (l ⊕ l) → ℂ) : conjVec (conjVec X) = X := by
  funext i
  simp [conjVec]

/-- `ω` is skew-symmetric on `ℂ²ⁿ`. -/
theorem stdFormC_skew (X Y : (l ⊕ l) → ℂ) : stdFormC l X Y = -stdFormC l Y X := by
  have hT : (-(Matrix.J l ℂ))ᵀ = -(-(Matrix.J l ℂ)) := by
    rw [Matrix.transpose_neg, Matrix.J_transpose]
  rw [stdFormC_apply, stdFormC_apply]
  nth_rewrite 1 [Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose, hT, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]

/-- `ω` has real coefficients, so it commutes with complex conjugation. -/
theorem stdFormC_conjVec (X Y : (l ⊕ l) → ℂ) :
    stdFormC l (conjVec X) (conjVec Y) = (starRingEnd ℂ) (stdFormC l X Y) := by
  have hJ : (Matrix.J l ℂ).map (starRingEnd ℂ) = Matrix.J l ℂ := by simp
  have hentry : ∀ i j : l ⊕ l, (starRingEnd ℂ) (Matrix.J l ℂ i j) = Matrix.J l ℂ i j := by
    intro i j
    have h := congrArg (fun M : Matrix (l ⊕ l) (l ⊕ l) ℂ => M i j) hJ
    simpa [Matrix.map_apply] using h
  have hM : (-(Matrix.J l ℂ)).map (starRingEnd ℂ) = -(Matrix.J l ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, map_neg, hentry]
  have h1 : (starRingEnd ℂ) (stdFormC l X Y)
      = ((starRingEnd ℂ) ∘ X) ⬝ᵥ ((starRingEnd ℂ) ∘ ((-(Matrix.J l ℂ)) *ᵥ Y)) := by
    rw [stdFormC_apply]
    exact RingHom.map_dotProduct _ _ _
  have h2 : ((starRingEnd ℂ) ∘ ((-(Matrix.J l ℂ)) *ᵥ Y)) = (-(Matrix.J l ℂ)) *ᵥ conjVec Y := by
    funext i
    have h := RingHom.map_mulVec (starRingEnd ℂ) (-(Matrix.J l ℂ)) Y i
    rw [hM] at h
    exact h
  rw [h1, h2, stdFormC_apply]
  rfl

/-- The form `B(X, Y) = Im ω(X, Ȳ)` of §7.3.a. -/
noncomputable def BForm (X Y : (l ⊕ l) → ℂ) : ℝ := (stdFormC l X (conjVec Y)).im

/-- The quadratic form `Q(X) = B(X, X) = Im ω(X, X̄)` of §7.3.a. -/
noncomputable def QForm (X : (l ⊕ l) → ℂ) : ℝ := BForm X X

/-- **Lemma 7.3.1** (additivity in the first slot). -/
theorem BForm_add_left (X Y Z : (l ⊕ l) → ℂ) :
    BForm (X + Y) Z = BForm X Z + BForm Y Z := by
  simp [BForm, Complex.add_im]

/-- **Lemma 7.3.1** (real homogeneity in the first slot). -/
theorem BForm_smul_left (r : ℝ) (X Y : (l ⊕ l) → ℂ) :
    BForm ((r : ℂ) • X) Y = r * BForm X Y := by
  have hb : stdFormC l ((r : ℂ) • X) (conjVec Y) = (r : ℂ) * stdFormC l X (conjVec Y) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  show (stdFormC l ((r : ℂ) • X) (conjVec Y)).im = r * (stdFormC l X (conjVec Y)).im
  rw [hb, Complex.im_ofReal_mul]

/-- **Lemma 7.3.1** (`B` is symmetric). -/
theorem BForm_symm (X Y : (l ⊕ l) → ℂ) : BForm Y X = BForm X Y := by
  have h2 : stdFormC l (conjVec X) Y = (starRingEnd ℂ) (stdFormC l X (conjVec Y)) := by
    conv_lhs => rw [← conjVec_conjVec Y]
    exact stdFormC_conjVec X (conjVec Y)
  show (stdFormC l Y (conjVec X)).im = (stdFormC l X (conjVec Y)).im
  rw [stdFormC_skew Y (conjVec X), h2]
  simp

/-- **Lemma 7.3.1** (`B(X̄, Ȳ) = −B(X, Y)`). -/
theorem BForm_conjVec (X Y : (l ⊕ l) → ℂ) :
    BForm (conjVec X) (conjVec Y) = -BForm X Y := by
  have h2 : stdFormC l (conjVec X) Y = (starRingEnd ℂ) (stdFormC l X (conjVec Y)) := by
    conv_lhs => rw [← conjVec_conjVec Y]
    exact stdFormC_conjVec X (conjVec Y)
  show (stdFormC l (conjVec X) (conjVec (conjVec Y))).im = -(stdFormC l X (conjVec Y)).im
  rw [conjVec_conjVec, h2]
  simp

/-- **Lemma 7.3.1** (`B(iX, iY) = B(X, Y)`; this is why the subspaces on which
`Q` is definite are complex subspaces). -/
theorem BForm_smul_I (X Y : (l ⊕ l) → ℂ) :
    BForm (Complex.I • X) (Complex.I • Y) = BForm X Y := by
  have hc : conjVec (Complex.I • Y) = (-Complex.I) • conjVec Y := by
    funext i
    simp [conjVec]
  have hII : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hb : stdFormC l (Complex.I • X) ((-Complex.I) • conjVec Y)
      = stdFormC l X (conjVec Y) := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul, hII, one_smul]
  show (stdFormC l (Complex.I • X) (conjVec (Complex.I • Y))).im
      = (stdFormC l X (conjVec Y)).im
  rw [hc, hb]

/-- `ω` is nondegenerate on `ℂ²ⁿ` (the complexification of Example 5.1.2). -/
theorem stdFormC_nondegenerate : (stdFormC l).Nondegenerate := by
  have hJ : IsUnit (Matrix.J l ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_J l ℂ)
  have hM : (-(Matrix.J l ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hJ.neg).ne_zero
  have hnd : Matrix.Nondegenerate (-(Matrix.J l ℂ)) := Matrix.nondegenerate_of_det_ne_zero hM
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · refine hnd.eq_zero_of_ortho fun w => ?_
    rw [← Matrix.toBilin'_apply']
    exact hX w
  · refine hnd.eq_zero_of_ortho' fun w => ?_
    rw [← Matrix.toBilin'_apply']
    exact hY w

/-- **Lemma 7.3.1** (`B` is nondegenerate).  If `Im ω(X, Ȳ) = 0` for every `Y`,
then, replacing `Y` by `iY`, also the real part vanishes, so `X = 0`. -/
theorem BForm_eq_zero_of_forall {X : (l ⊕ l) → ℂ} (hX : ∀ Y, BForm X Y = 0) : X = 0 := by
  refine (stdFormC_nondegenerate (l := l)).1 X ?_
  intro Z
  have h1 : (stdFormC l X Z).im = 0 := by
    have h := hX (conjVec Z)
    rwa [BForm, conjVec_conjVec] at h
  have h2 : (stdFormC l X (Complex.I • Z)).im = 0 := by
    have h := hX (conjVec (Complex.I • Z))
    rwa [BForm, conjVec_conjVec] at h
  have h3 : stdFormC l X (Complex.I • Z) = Complex.I * stdFormC l X Z := by
    rw [map_smul, smul_eq_mul]
  rw [h3] at h2
  have h4 : (stdFormC l X Z).re = 0 := by
    simpa [Complex.mul_im] using h2
  exact Complex.ext (by simpa using h4) (by simpa using h1)

end Appendix

end Chapter7
end MorseFloer
