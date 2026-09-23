import MorseFloer.Part2.Ch5
import MorseFloer.Part2.LinearYorke
import MorseFloer.Part2.SymplecticForms
import MorseFloer.Part2.RhoUnitary
import MorseFloer.Part2.RhoLiftContinuity
import MorseFloer.Part2.MaslovPaths

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
* *proves* **Lemma 7.2.3** in both directions, algebraic core and differential
  form: the entrywise product rule (`hasDerivAt_mul_entry`) is enough, so no
  normed algebra structure on `Matrix` is needed;
* *proves* Lemma 7.3.1 and its corollary: the real symmetric form
  `B(X, Y) = Im ω(X, Ȳ)` on `ℂ²ⁿ` is nondegenerate and satisfies
  `B(iX, iY) = B(X, Y)` and `B(X̄, Ȳ) = −B(X, Y)`;
* *proves* that `Δ` does not depend on the chosen lift
  (`Delta_eq_of_isAngleLift`), by hand: a continuous function into `2πℤ` on the
  connected `ℝ` is constant;
* *proves* the rotation case of the `2 × 2` computations of the proof of
  Proposition 7.2.1, `exp(θ J₂) = rot θ` (`exp_smul_J2`), through the algebra
  embedding `ℂ → M₂(ℝ)` and `NormedSpace.map_exp`;
* *proves* the second half of **Remark 7.1.2** (`exp_J_mul_mem_symplecticStar`):
  `‖S‖ < 2π` implies `exp(JS)` has no eigenvalue `1`, by Yorke's theorem applied
  to the linear field `JS` (`Part2/LinearYorke.lean`).

The first three bricks towards the construction of `ρ` are in place, not yet
used here: `Part2/RootsContinuity.lean` proves that the roots of a monic
polynomial over `ℂ` depend continuously on its coefficients, counted with
multiplicity; `Part2/SpectralProjector.lean` builds, for a disc whose boundary
carries no eigenvalue, the spectral projector onto the sum of the generalised
eigenspaces of the eigenvalues in the disc, continuous in the matrix, with the
number of those eigenvalues locally constant; and `Part2/SymplecticEigen.lean`
(which imports `Part2/SymplecticForms.lean` for `stdFormC` and `BForm`) proves Lemma 7.3.3 and
Corollary 7.3.4 for the sesquilinear form `H(X, Y) = ω(X, Ȳ)` — the generalised
eigenspaces `E_μ`, `E_ν` of a symplectic matrix are `H`-orthogonal when
`μν̄ ≠ 1`, `E_μ` is isotropic when `|μ| ≠ 1` — and that `H` and `B` are
nondegenerate on `E_ν` when `|ν| = 1`; and `Part2/EigenDecomp.lean` identifies
the kernel of the disc factor of the characteristic polynomial, the range of
the spectral projector, with the sum of the generalised eigenspaces of the
eigenvalues in the disc, on which `H` is nondegenerate when the disc is stable
under `μ ↦ 1/μ̄`; `Part2/HermitianIndex.lean` defines the positive index of a
Hermitian form on a subspace and proves Sylvester's law for it through the Gram
matrix; and `Part2/SignatureContinuity.lean` proves that this index, taken on
the sum of the generalised eigenspaces in a disc, is locally constant in the
matrix (Propositions 7.3.6–7.3.8); `Part2/EigenMult.lean` supplies the
multiplicity bookkeeping (`finrank E_μ = m(μ)`, the pairings of the
eigenvalues of a symplectic matrix, `m(−1)` even); and `Part2/Rho.lean`
**defines `ρ`** as the book does in §7.3.b and **proves it continuous** on the
symplectic group (§7.3.c, Corollary 7.3.9 and Proposition 7.3.10), which is the
continuity clause of Theorem 7.1.3, and `Part2/RhoProperties.lean` proves that
it takes its values in the unit circle and satisfies `ρ(A⁻¹) = conj ρ(A)`,
`Part2/RhoNaturality.lean` that `ρ(TAT⁻¹) = ρ(A)` for `T` symplectic and
`ρ(Aᵀ) = ρ(A⁻¹)`, and `Part2/RhoNormalisation.lean` the normalisation
`ρ(A) = (−1)^{m₀/2}` on real spectra, and `Part2/RhoBlockSum.lean` the product
`ρ(A ⊕ B) = ρ(A)ρ(B)`, and `Part2/RhoUnitary.lean` the last clause,
`ρ = det(X + iY)` on the unitary matrices.  **Theorem 7.1.3 is therefore
proved** (`exists_isRho`), by exhibiting this `ρ`; and **Lemma 7.1.6** is
proved for it too (`exists_lift_symplecticPlus`, `exists_lift_symplecticMinus`):
`Part2/RhoLift.lean` writes down the lift `ρ̃` of §7.3.d and checks
`exp(iρ̃) = ρ` on `Sp(2n)⁺`, `exp(i(ρ̃ + π)) = ρ` on `Sp(2n)⁻`, through the sign of
`det(A − 1)`, and `Part2/RhoLiftContinuity.lean` proves `ρ̃` continuous on
`Sp(2n)⋆`.  The definitions of §7.3.a
(`stdFormC`, `conjVec`, `BForm`), of the block sum and of the real spectrum live
in `Part2/SymplecticForms.lean`, under this chapter's namespace, so that the
bricks can be built without importing this file.

Assumed (`sorry`):

* **Proposition 7.1.4**, the path-connectedness of `Sp(2n)±`, and **Lemma 7.1.5**
  on which it rests;
* **Proposition 7.2.1**/the existence of the index
  (`exists_isConleyZehnderIndex`).

**Lemma 7.2.4 is proved** from the axioms of Proposition 7.2.1 alone
(`exists_symmetric_of_index`), for `n ≥ 2` — for `n = 1` the statement is false
(a path `exp(tJS)` on `ℝ²` has odd index or index `0`).  The matrix input — the
rotation `exp(tcJ)` as the real form of `e^{itc}·Id`, block sums commuting with
`exp`, the hyperbolic block, and the homotopy in `S` between
`exp(t(ℓ+2)πJ) ⊕ exp(t(ℓ−2)πJ)` and `exp(tℓπJ) ⊕ exp(tℓπJ)` through the
contraction of a loop of `SU(2)` — is in `Part2/MaslovPaths.lean`; the index of
`exp(tℓπJ)` on `ℝ²`, `−ℓ` for odd `ℓ`, then follows by induction from the
normalisation at `ℓ = ±1`, additivity and homotopy invariance.

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
* **Corollary 7.3.2** (the signature of `Q` on all of `ℂ²ⁿ` vanishes) and the
  vanishing signature of `Q` on `E_λ ⊕ E_{1/λ}` in **Corollary 7.3.4**: they need
  the signature discussed above.  The nondegeneracy half of 7.3.2 is proved
  here as `BForm_eq_zero_of_forall`; **Lemma 7.3.3** and the isotropy half of
  7.3.4 are proved in `Part2/SymplecticEigen.lean`.
-/

open LinearMap (BilinForm)
open scoped Matrix

namespace MorseFloer
namespace Chapter7

/-! ## §7.1.c The subset `Sp(2n)⋆`

The sets `Sp(2n)⋆`, `Sp(2n)±` and `Σ`, the admissible paths of §7.1.c/§7.2.a and
the paths `exp(tJS)` of Remark 7.1.2 are defined in `Part2/MaslovPaths.lean`,
under this chapter's namespace, so that the matrix computations behind
Lemma 7.2.4 can be carried out without importing this file. -/

/-! ### The spectrum of a symplectic matrix

Proposition 5.6.3 says that `Aᵀ` and `A⁻¹` are conjugate by `J`; Mathlib packages
this as `SymplecticGroup.inv_eq_symplectic_inv`.  Combined with `det A = 1` it
gives Proposition 5.6.4, the symmetry `λ ↦ λ⁻¹` of the characteristic
polynomial, which `Part2/Ch5.lean` leaves as an assumption and which is proved
here. -/

section Spectrum

variable {l : Type*} [DecidableEq l] [Fintype l] {K : Type*} [Field K]
variable {A : Matrix (l ⊕ l) (l ⊕ l) K}

/-- A symplectic matrix has a symplectic inverse.

This and the three lemmas after it were moved into Chapter 5, where they
discharge its Proposition 5.6.4; they are kept here as aliases so that the names
this chapter uses stay put. -/
theorem inv_mem_symplecticGroup (hA : A ∈ Matrix.symplecticGroup l K) :
    A⁻¹ ∈ Matrix.symplecticGroup l K :=
  Chapter5.inv_mem_symplecticGroup hA

/-- For a symplectic `A` and any scalar `c`, `det(A⁻¹ − c) = det(A − c)`: indeed
`A⁻¹ = (−J) Aᵀ J`, conjugation does not change the determinant, and neither does
transposition.  This is the computational content of Proposition 5.6.3. -/
theorem det_inv_sub_smul (hA : A ∈ Matrix.symplecticGroup l K) (c : K) :
    (A⁻¹ - c • 1).det = (A - c • 1).det :=
  Chapter5.det_inv_sub_smul hA c

/-- `det(A⁻¹ − c⁻¹) = (−c⁻¹)^{2n} det(A − c)`, from `A⁻¹ − c⁻¹ = −c⁻¹ A⁻¹(A − c)`
and `det A = 1`. -/
theorem det_inv_sub_inv_smul (hA : A ∈ Matrix.symplecticGroup l K) {c : K} (hc : c ≠ 0) :
    (A⁻¹ - c⁻¹ • 1).det = (-c⁻¹) ^ Fintype.card (l ⊕ l) * (A - c • 1).det :=
  Chapter5.det_inv_sub_inv_smul hA hc

/-- **Proposition 5.6.4** (left as an assumption in Chapter 5, proved here).
The characteristic polynomial of a symplectic matrix is symmetric under
`λ ↦ λ⁻¹`: `det(A − λ⁻¹ Id) = (−λ⁻¹)^{2n} det(A − λ Id)`. -/
theorem det_sub_inv_smul (hA : A ∈ Matrix.symplecticGroup l K) {c : K} (hc : c ≠ 0) :
    (A - c⁻¹ • 1).det = (-c⁻¹) ^ Fintype.card (l ⊕ l) * (A - c • 1).det :=
  Chapter5.det_sub_inv_smul hA hc

/-- **Proposition 5.6.4** over an arbitrary field.

`Chapter5.det_charpoly_symmetric` is the same statement over `ℝ`, and is proved
there; this is the general-field version, which §7.1.c uses.  The two forms agree
because `2n` is even, which turns the sign `(−λ⁻¹)^{2n}` of `det_sub_inv_smul`
into `λ^{-2n}`. -/
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

/-! Remark 7.1.2 is proved in `Part2/MaslovPaths.lean`
(`exp_smul_J_mul_mem_symplecticGroup`, `exp_J_mul_mem_symplecticStar`). -/

/-! ## §7.1.b Second step: the map `ρ : Sp(2n) → S¹`

Theorem 7.1.3 asserts the existence of a continuous `ρ : Sp(2n) → S¹` which is
invariant under symplectic conjugation, multiplicative for block sums, equal to
the complex determinant on the unitary matrices, equal to `(−1)^{m₀/2}` when the
spectrum is real, and satisfies `ρ(Aᵀ) = ρ(A⁻¹) = conj ρ(A)`.  The properties
are recorded as a predicate, and the construction of the appendix §7.3, carried
out in `Part2/Rho.lean` and its companions, exhibits a map satisfying it. -/

section Rho

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

/-- **Theorem 7.1.3** (existence).  Such a `ρ` exists: the map `Rho.rho` of
`Part2/Rho.lean`, built as in §7.3.b from the signatures of `Q` on the
generalised eigenspaces, and proved continuous in `Part2/Rho.lean` (§7.3.c) and
to satisfy the other seven clauses in `Part2/RhoProperties.lean`,
`Part2/RhoNaturality.lean`, `Part2/RhoNormalisation.lean`,
`Part2/RhoBlockSum.lean` and `Part2/RhoUnitary.lean`. -/
theorem exists_isRho : ∃ ρ, IsRho ρ :=
  ⟨Rho.rho,
    { continuousOn := Rho.continuousOn_rho
      norm_eq_one := fun n A _ => Rho.norm_rho n A
      naturality := fun n A _ _ hT => Rho.rho_naturality n A hT
      blockSum_eq := fun _ _ A B hA hB => Rho.rho_blockSum A B hA hB
      det_unitary := fun n X Y _ hO => Rho.rho_det_unitary n X Y hO
      normalisation := fun n _ hA hreal => Rho.rho_normalisation n hA hreal
      map_transpose := fun n _ hA => Rho.rho_transpose n hA
      map_inv := fun n _ hA => Rho.rho_inv n hA }⟩

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

/-- **Lemma 7.1.6.**  On each of `Sp(2n)±` the map `ρ` of Theorem 7.1.3 admits a
continuous real-valued lift through `θ ↦ e^{iθ}`.  This is what makes the
inclusions `Sp(2n)± ↪ Sp(2n)` trivial on fundamental groups, hence what makes
the class of the connecting path `γ_A` of §7.2.a well defined.

The lift is written down in §7.3.d from the explicit formula for `ρ` in terms of
the arguments of the eigenvalues on the unit circle (`Rho.rhoLift`,
`Part2/RhoLift.lean`), and its continuity on `Sp(2n)⋆` is checked in
`Part2/RhoLiftContinuity.lean` by the same case analysis that proves the
continuity of `ρ`. -/
theorem exists_lift_symplecticPlus (n : ℕ) :
    ∃ f : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℝ,
      ContinuousOn f (symplecticPlus (Fin n)) ∧
      ∀ A ∈ symplecticPlus (Fin n), Complex.exp (f A * Complex.I) = Rho.rho n A := by
  obtain ⟨f, hf, hexp⟩ := Rho.exists_lift_plus n
  exact ⟨f, hf, fun A hA => hexp A hA.1 hA.2⟩

/-- **Lemma 7.1.6** for the other component: on `Sp(2n)⁻` the lift is `ρ̃ + π`. -/
theorem exists_lift_symplecticMinus (n : ℕ) :
    ∃ f : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℝ,
      ContinuousOn f (symplecticMinus (Fin n)) ∧
      ∀ A ∈ symplecticMinus (Fin n), Complex.exp (f A * Complex.I) = Rho.rho n A := by
  obtain ⟨f, hf, hexp⟩ := Rho.exists_lift_minus n
  exact ⟨f, hf, fun A hA => hexp A hA.1 hA.2⟩

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

Two lifts differ pointwise by an element of `2πℤ`
(`Complex.exp_eq_exp_iff_exists_int`), so `(α − β)/2π` is a continuous function
`ℝ → ℝ` with integer values.  Since `ℤ ↪ ℝ` is a closed embedding it is a
continuous map into the discrete space `ℤ`, hence constant because `ℝ` is
connected (`PreconnectedSpace.constant`).  This is unique path lifting for
`θ ↦ e^{iθ}`, done by hand. -/
theorem Delta_eq_of_isAngleLift {u : ℝ → ℂ} {α β : ℝ → ℝ}
    (hα : IsAngleLift u α) (hβ : IsAngleLift u β) : Delta α = Delta β := by
  have hspec : ∀ t, ∃ n : ℤ, α t - β t = n * (2 * Real.pi) := by
    intro t
    have h : Complex.exp (α t * Complex.I) = Complex.exp (β t * Complex.I) := by
      rw [hα.2, hβ.2]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    simp at him
    linarith
  choose k hk using hspec
  have hk' : Continuous k := by
    rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
    have hfun : ((↑) : ℤ → ℝ) ∘ k = fun t => (α t - β t) / (2 * Real.pi) := by
      funext t
      simp only [Function.comp_apply]
      rw [hk t, mul_div_cancel_right₀ _ (by positivity)]
    rw [hfun]
    exact (hα.1.sub hβ.1).div_const _
  have h01 : k 0 = k 1 := PreconnectedSpace.constant inferInstance hk'
  have e0 := hk 0
  have e1 := hk 1
  rw [h01] at e0
  unfold Delta
  rw [show α 1 - α 0 = β 1 - β 0 by linarith]

end Delta

/-! `IsAdmissiblePath` and `HomotopicInS`, the space `S` of §7.1.c and the
homotopies inside it, are defined in `Part2/MaslovPaths.lean`. -/

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

/-! ### Lemma 7.2.4: the matrices `S_k`

The computation runs on the axioms of Proposition 7.2.1 alone, with the matrix
input of `Part2/MaslovPaths.lean`.  The path of `S = c · Id` on `ℝ^{2m}` is the
rotation `exp(tcJ)`; for `c = ±π` the normalisation axiom gives its index,
`−m` for `π` and `+m` for `−π`.  On `ℝ²` and for the other odd multiples `ℓπ`
the index is `−ℓ`, by induction on `|ℓ|` from the recurrence
`μ(ℓ+2) + μ(ℓ−2) = 2μ(ℓ)`, which is additivity applied to the homotopy
`homotopicInS_rot`.  The hyperbolic block `diag(1, −1)` has index `0` by
normalisation.  For `n ≥ 2` the block sum of a `4 × 4` block of index
`k − (n − 2)` — two rotation blocks if `k` is even, the hyperbolic block and a
rotation block if `k` is odd — with `−π · Id` on `ℝ^{2(n−2)}` has index `k`. -/

/-- The index of the rotation path `exp(tcJ)` on `ℝ^{2m}` for `0 < |c| < 2π`,
from the normalisation axiom: `2m − m` if `c < 0`, `−m` if `c > 0`. -/
theorem index_expPath_smul_one (hμ : IsConleyZehnderIndex μ) (m : ℕ) {c : ℝ} (hc0 : c ≠ 0)
    (hc : |c| < 2 * Real.pi) :
    μ m (expPath (c • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)))
      = (if c < 0 then (2 * m : ℤ) else 0) - m := by
  have h := hμ.normalisation m (c • 1) (by rw [Matrix.transpose_smul, Matrix.transpose_one])
    (det_smul_one_ne_zero hc0) (abs_lt_of_det_smul_one_sub_eq_zero hc)
  rw [negEigenCount_smul_one, Fintype.card_sum, Fintype.card_fin] at h
  refine h.trans ?_
  split_ifs <;> push_cast <;> ring

theorem abs_pi_lt : |Real.pi| < 2 * Real.pi := by
  rw [abs_of_pos Real.pi_pos]; linarith [Real.pi_pos]

theorem abs_neg_pi_lt : |-Real.pi| < 2 * Real.pi := by
  rw [abs_neg]; exact abs_pi_lt

/-- The index of the block sum of two paths `exp(tJS)`, `exp(tJB)`. -/
theorem index_expPath_blockSum (hμ : IsConleyZehnderIndex μ) {m n : ℕ}
    {S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ} {B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hS : IsAdmissiblePath (expPath S)) (hB : IsAdmissiblePath (expPath B)) :
    μ (m + n) (expPath (blockSum S B)) = μ m (expPath S) + μ n (expPath B) := by
  rw [expPath_blockSum]
  exact hμ.additivity m n _ _ hS hB

/-- The index of the hyperbolic block: `Ind(diag(1, −1)) − 1 = 0`. -/
theorem index_expPath_hypBlock (hμ : IsConleyZehnderIndex μ) : μ 1 (expPath hypBlock) = 0 := by
  have h := hμ.normalisation 1 hypBlock hypBlock_transpose (by rw [det_hypBlock]; norm_num)
    abs_lt_of_det_hypBlock_sub_eq_zero
  rw [negEigenCount_hypBlock] at h
  exact h.trans (by norm_num)

/-- The recurrence `μ(ℓ+2) + μ(ℓ−2) = 2μ(ℓ)` for the rotation paths on `ℝ²`, from
the homotopy `homotopicInS_rot` and additivity. -/
theorem index_expPath_rot_recurrence (hμ : IsConleyZehnderIndex μ) {k : ℤ} (hk : Odd k) :
    μ 1 (expPath ((((k + 2 : ℤ) : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)))
      + μ 1 (expPath ((((k - 2 : ℤ) : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)))
      = 2 * μ 1 (expPath (((k : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))) := by
  have hk2 : Odd (k + 2) := by obtain ⟨q, rfl⟩ := hk; exact ⟨q + 1, by ring⟩
  have hk2' : Odd (k - 2) := by obtain ⟨q, rfl⟩ := hk; exact ⟨q - 1, by ring⟩
  have h0 := isAdmissiblePath_blockSum (isAdmissiblePath_expPath_rot (l := Fin 1) hk2)
    (isAdmissiblePath_expPath_rot (l := Fin 1) hk2')
  have h1 := isAdmissiblePath_blockSum (isAdmissiblePath_expPath_rot (l := Fin 1) hk)
    (isAdmissiblePath_expPath_rot (l := Fin 1) hk)
  have heq := (hμ.homotopy (1 + 1) _ _ h0 h1).mp (homotopicInS_rot hk)
  rw [hμ.additivity 1 1 _ _ (isAdmissiblePath_expPath_rot hk2) (isAdmissiblePath_expPath_rot hk2'),
    hμ.additivity 1 1 _ _ (isAdmissiblePath_expPath_rot hk) (isAdmissiblePath_expPath_rot hk)] at heq
  rw [heq]; ring

/-- The index of `exp(tπJ)` on `ℝ²` is `−1`. -/
theorem index_expPath_rot_one (hμ : IsConleyZehnderIndex μ) :
    μ 1 (expPath ((((1 : ℤ) : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))) = -1 := by
  have h := index_expPath_smul_one hμ 1 Real.pi_pos.ne' abs_pi_lt
  rw [if_neg (not_lt.mpr Real.pi_pos.le)] at h
  rw [Int.cast_one, one_mul, h]; norm_num

/-- The index of `exp(−tπJ)` on `ℝ²` is `+1`. -/
theorem index_expPath_rot_neg_one (hμ : IsConleyZehnderIndex μ) :
    μ 1 (expPath ((((-1 : ℤ) : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))) = 1 := by
  have h := index_expPath_smul_one hμ 1 (neg_ne_zero.mpr Real.pi_pos.ne') abs_neg_pi_lt
  rw [if_pos (neg_lt_zero.mpr Real.pi_pos)] at h
  rw [Int.cast_neg, Int.cast_one, neg_one_mul, h]; norm_num

/-- The index of `exp(tℓπJ)` on `ℝ²` is `−ℓ` for every odd `ℓ`, by induction on
`|ℓ|` from the recurrence. -/
theorem index_expPath_rot_aux (hμ : IsConleyZehnderIndex μ) (q : ℕ) :
    ∀ k : ℤ, Odd k → -(2 * (q : ℤ) + 1) ≤ k → k ≤ 2 * q + 1 →
      μ 1 (expPath (((k : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))) = -k := by
  induction q with
  | zero =>
    intro k hk hlo hhi
    have hcase : k = 1 ∨ k = -1 := by obtain ⟨j, rfl⟩ := hk; omega
    rcases hcase with rfl | rfl
    · exact index_expPath_rot_one hμ
    · exact index_expPath_rot_neg_one hμ
  | succ q ih =>
    intro k hk hlo hhi
    by_cases h : -(2 * (q : ℤ) + 1) ≤ k ∧ k ≤ 2 * q + 1
    · exact ih k hk h.1 h.2
    · have hcase : k = 2 * q + 3 ∨ k = -(2 * q + 3) := by obtain ⟨j, rfl⟩ := hk; omega
      rcases hcase with rfl | rfl
      · have hrec := index_expPath_rot_recurrence hμ (k := 2 * q + 1) ⟨q, rfl⟩
        rw [show (2 * (q : ℤ) + 1 + 2 : ℤ) = 2 * q + 3 by ring,
          show (2 * (q : ℤ) + 1 - 2 : ℤ) = 2 * q - 1 by ring,
          ih (2 * q + 1) ⟨q, rfl⟩ (by omega) (by omega),
          ih (2 * q - 1) ⟨q - 1, by ring⟩ (by omega) (by omega)] at hrec
        linarith
      · have hrec := index_expPath_rot_recurrence hμ (k := -(2 * q + 1)) ⟨-q - 1, by ring⟩
        rw [show (-(2 * (q : ℤ) + 1) + 2 : ℤ) = -(2 * q - 1) by ring,
          show (-(2 * (q : ℤ) + 1) - 2 : ℤ) = -(2 * q + 3) by ring,
          ih (-(2 * q + 1)) ⟨-q - 1, by ring⟩ (by omega) (by omega),
          ih (-(2 * q - 1)) ⟨-q, by ring⟩ (by omega) (by omega)] at hrec
        linarith

theorem index_expPath_rot (hμ : IsConleyZehnderIndex μ) {k : ℤ} (hk : Odd k) :
    μ 1 (expPath (((k : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ))) = -k :=
  index_expPath_rot_aux hμ k.natAbs k hk (by omega) (by omega)

/-- **Lemma 7.2.4 on `ℝ⁴`.**  Every integer is the index of a path `exp(tJS)`
with `S` symmetric: `S = −π·Id ⊕ (1−k)π·Id` for `k` even, `S = diag(1, −1) ⊕ (−k)π·Id`
for `k` odd. -/
theorem exists_symmetric_of_index_two (hμ : IsConleyZehnderIndex μ) (k : ℤ) :
    ∃ S : Matrix (Fin (1 + 1) ⊕ Fin (1 + 1)) (Fin (1 + 1) ⊕ Fin (1 + 1)) ℝ, Sᵀ = S ∧
      IsAdmissiblePath (expPath S) ∧ μ (1 + 1) (expPath S) = k := by
  rcases Int.even_or_odd k with hk | hk
  · have h1 : Odd (-1 : ℤ) := ⟨-1, by norm_num⟩
    have h2 : Odd (1 - k) := by obtain ⟨j, rfl⟩ := hk; exact ⟨-j, by ring⟩
    refine ⟨blockSum ((((-1 : ℤ) : ℝ) * Real.pi) • 1) ((((1 - k : ℤ) : ℝ) * Real.pi) • 1),
      ?_, ?_, ?_⟩
    · simp only [blockSum_transpose, Matrix.transpose_smul, Matrix.transpose_one]
    · rw [expPath_blockSum]
      exact isAdmissiblePath_blockSum (isAdmissiblePath_expPath_rot h1)
        (isAdmissiblePath_expPath_rot h2)
    · rw [index_expPath_blockSum hμ (isAdmissiblePath_expPath_rot h1)
        (isAdmissiblePath_expPath_rot h2), index_expPath_rot hμ h1, index_expPath_rot hμ h2]
      ring
  · have h2 : Odd (-k) := by obtain ⟨j, rfl⟩ := hk; exact ⟨-j - 1, by ring⟩
    refine ⟨blockSum hypBlock ((((-k : ℤ) : ℝ) * Real.pi) • 1), ?_, ?_, ?_⟩
    · simp only [blockSum_transpose, hypBlock_transpose, Matrix.transpose_smul,
        Matrix.transpose_one]
    · rw [expPath_blockSum]
      exact isAdmissiblePath_blockSum isAdmissiblePath_expPath_hypBlock
        (isAdmissiblePath_expPath_rot h2)
    · rw [index_expPath_blockSum hμ isAdmissiblePath_expPath_hypBlock
        (isAdmissiblePath_expPath_rot h2), index_expPath_hypBlock hμ, index_expPath_rot hμ h2]
      ring

/-- **Lemma 7.2.4.**  For every integer `k` and every `n ≥ 2` there is a symmetric
matrix `S_k` whose path `exp(t J S_k)` is admissible and has Maslov index `k`.
These are the matrices reused in Chapter 8.

Proved from the axioms of Proposition 7.2.1: see the section header.  The book's
`S_k` is diagonal; the one exhibited here is block diagonal with `2 × 2` blocks
`c·Id` and `diag(1, −1)`, hence diagonal too.  The hypothesis `n ≥ 2` is
necessary: on `ℝ²` a path `exp(tJS)` with `S` symmetric ends at a rotation or a
hyperbolic matrix, so its index is odd or `0`, and no even `k ≠ 0` occurs. -/
theorem exists_symmetric_of_index (hμ : IsConleyZehnderIndex μ) (n : ℕ) (hn : 2 ≤ n)
    (k : ℤ) :
    ∃ S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, Sᵀ = S ∧
      IsAdmissiblePath (fun t => NormedSpace.exp (t • (Matrix.J (Fin n) ℝ * S))) ∧
      μ n (fun t => NormedSpace.exp (t • (Matrix.J (Fin n) ℝ * S))) = k := by
  obtain ⟨p, rfl⟩ : ∃ p, n = 1 + 1 + p := ⟨n - 2, by omega⟩
  obtain ⟨S₂, hS₂, hadm, hind⟩ := exists_symmetric_of_index_two hμ (k - p)
  have hB : IsAdmissiblePath
      (expPath ((-Real.pi) • (1 : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ))) :=
    isAdmissiblePath_expPath (by rw [Matrix.transpose_smul, Matrix.transpose_one])
      (det_smul_one_ne_zero (neg_ne_zero.mpr Real.pi_pos.ne'))
      (abs_lt_of_det_smul_one_sub_eq_zero abs_neg_pi_lt)
  have hBi : μ p (expPath ((-Real.pi) • (1 : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ)))
      = p := by
    have h := index_expPath_smul_one hμ p (neg_ne_zero.mpr Real.pi_pos.ne') abs_neg_pi_lt
    rw [if_pos (neg_lt_zero.mpr Real.pi_pos)] at h
    rw [h]; ring
  refine ⟨blockSum S₂ ((-Real.pi) • 1), ?_, ?_, ?_⟩
  · rw [blockSum_transpose, hS₂, Matrix.transpose_smul, Matrix.transpose_one]
  · show IsAdmissiblePath (expPath (blockSum S₂ ((-Real.pi) • 1)))
    rw [expPath_blockSum]
    exact isAdmissiblePath_blockSum hadm hB
  · show μ (1 + 1 + p) (expPath (blockSum S₂ ((-Real.pi) • 1))) = k
    rw [index_expPath_blockSum hμ hadm hB, hind, hBi]
    ring

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

omit [DecidableEq l] in
/-- The product rule, entrywise: an entry of a product of two matrix-valued paths
has the derivative prescribed by `(AB)' = A'B + AB'`.  Stating it entrywise avoids
needing a normed algebra structure on `Matrix`, for which Mathlib offers only
scoped instances. -/
private theorem hasDerivAt_mul_entry {A B : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ}
    {A' B' : Matrix (l ⊕ l) (l ⊕ l) ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : l ⊕ l) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [show (∑ k, A' i k * B t k j) + ∑ k, A t i k * B' k j
      = ∑ k, (A' i k * B t k j + A t i k * B' k j) from (Finset.sum_add_distrib).symm]
  exact HasDerivAt.fun_sum fun k _ => (hA i k).fun_mul (hB k j)

/-- **Lemma 7.2.3** (first half, differential form).  The solution of
`R' = J S R` with `R 0 = Id`, for a continuous path `S` of symmetric matrices,
takes symplectic values.

The algebraic identity behind it is `transpose_mul_J_add_of_symm`, which says
that the derivative of `Rᵀ J R` vanishes; `hasDerivAt_mul_entry` turns that into
a statement about entries, and a real-valued function on `ℝ` with vanishing
derivative is constant, so `Rᵀ J R = (R 0)ᵀ J R 0 = J`. -/
theorem mem_symplecticGroup_of_hasDerivAt (R S : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hS : ∀ t, (S t)ᵀ = S t)
    (hR : ∀ t i j, HasDerivAt (fun s => R s i j) ((Matrix.J l ℝ * S t * R t) i j) t)
    (h0 : R 0 = 1) (t : ℝ) : R t ∈ Matrix.symplecticGroup l ℝ := by
  have hRT : ∀ s i j, HasDerivAt (fun σ => (R σ)ᵀ i j)
      (((Matrix.J l ℝ * S s * R s)ᵀ) i j) s := fun s i j => by
    simpa [Matrix.transpose_apply] using hR s j i
  have hkey : ∀ s i j, HasDerivAt (fun σ => ((R σ)ᵀ * Matrix.J l ℝ * R σ) i j) 0 s := by
    intro s i j
    have h1 : ∀ i j, HasDerivAt (fun σ => ((R σ)ᵀ * Matrix.J l ℝ) i j)
        (((Matrix.J l ℝ * S s * R s)ᵀ * Matrix.J l ℝ) i j) s := fun i j => by
      simpa using hasDerivAt_mul_entry (A := fun σ => (R σ)ᵀ) (B := fun _ => Matrix.J l ℝ)
        (B' := 0) (hRT s) (fun i j => hasDerivAt_const _ _) i j
    have h2 := hasDerivAt_mul_entry (A := fun σ => (R σ)ᵀ * Matrix.J l ℝ) (B := R)
      (B' := Matrix.J l ℝ * S s * R s) h1 (fun i j => hR s i j) i j
    rwa [transpose_mul_J_add_of_symm (hS s), Matrix.zero_apply] at h2
  have hconst : ∀ i j, ((R t)ᵀ * Matrix.J l ℝ * R t) i j = ((R 0)ᵀ * Matrix.J l ℝ * R 0) i j :=
    fun i j => is_const_of_deriv_eq_zero (fun x => (hkey x i j).differentiableAt)
      (fun x => (hkey x i j).deriv) t 0
  rw [SymplecticGroup.mem_iff']
  ext i j
  rw [hconst i j, h0]
  simp

/-- **Lemma 7.2.3** (second half, differential form).  Conversely, for a `C¹` path
`R` in `Sp(2n)` the matrices `S t = −J R'(t) R(t)⁻¹` are symmetric.

The algebraic content is `symm_of_transpose_mul_J_add`; what feeds it is that
`t ↦ Rᵀ J R` is the constant `J`, so uniqueness of derivatives applied to
`hasDerivAt_mul_entry` gives `Dᵀ J R + Rᵀ J D = 0` entrywise. -/
theorem symm_of_hasDerivAt (R D : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hmem : ∀ t, R t ∈ Matrix.symplecticGroup l ℝ)
    (hR : ∀ t i j, HasDerivAt (fun s => R s i j) (D t i j) t) (t : ℝ) :
    (-(Matrix.J l ℝ * D t * (R t)⁻¹))ᵀ = -(Matrix.J l ℝ * D t * (R t)⁻¹) := by
  have hdet : IsUnit (R t).det := by
    rw [SymplecticGroup.det_eq_one (hmem t)]; exact isUnit_one
  refine symm_of_transpose_mul_J_add hdet ?_
  have hRT : ∀ s i j, HasDerivAt (fun σ => (R σ)ᵀ i j) ((D s)ᵀ i j) s := fun s i j => by
    simpa [Matrix.transpose_apply] using hR s j i
  ext i j
  have h1 : ∀ i j, HasDerivAt (fun σ => ((R σ)ᵀ * Matrix.J l ℝ) i j)
      (((D t)ᵀ * Matrix.J l ℝ) i j) t := fun i j => by
    simpa using hasDerivAt_mul_entry (A := fun σ => (R σ)ᵀ) (B := fun _ => Matrix.J l ℝ)
      (B' := 0) (hRT t) (fun i j => hasDerivAt_const _ _) i j
  have h2 := hasDerivAt_mul_entry (A := fun σ => (R σ)ᵀ * Matrix.J l ℝ) (B := R)
    (B' := D t) h1 (fun i j => hR t i j) i j
  have hJ : (fun σ => ((R σ)ᵀ * Matrix.J l ℝ * R σ) i j) = fun _ => Matrix.J l ℝ i j := by
    funext σ
    rw [SymplecticGroup.mem_iff'.mp (hmem σ)]
  rw [hJ] at h2
  rw [Matrix.zero_apply]
  exact h2.unique (hasDerivAt_const t _)

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

set_option backward.isDefEq.respectTransparency false in
/-- The exponential of a multiple of `J₂` is a rotation: `exp(θ J₂) = rot θ`.

The `2 × 2` matrices `a·Id + b·J₂` form a copy of `ℂ`, and Mathlib has the
embedding: `Algebra.leftMulMatrix Complex.basisOneI` is the `ℝ`-algebra map
`ℂ → M₂(ℝ)` sending `z` to the matrix of multiplication by `z` in the basis
`(1, i)`, which is `!![Re z, −Im z; Im z, Re z]`; it sends `i` to `J₂`.  Being a
continuous ring homomorphism it commutes with `exp` (`NormedSpace.map_exp`), so
`exp(θ J₂)` is the image of `e^{iθ} = cos θ + i sin θ`, which is `rot θ`.

The normed-ring structure on matrices that `map_exp` asks for is only a scoped
instance (`Matrix.Norms.Operator`), while the statement uses the product topology; the
two agree, and `backward.isDefEq.respectTransparency false` lets Lean see it, as
in Mathlib's own `Matrix.exp_add_of_commute`. -/
theorem exp_smul_J2 (θ : ℝ) : NormedSpace.exp (θ • J2) = rot θ := by
  let f : ℂ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := Algebra.leftMulMatrix Complex.basisOneI
  have hfz : ∀ z : ℂ, f z = !![z.re, -z.im; z.im, z.re] := by
    intro z
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [f, Algebra.leftMulMatrix_eq_repr_mul, Complex.coe_basisOneI_repr,
        Complex.coe_basisOneI]
  have h1 : f ((θ : ℂ) * Complex.I) = θ • J2 := by
    rw [hfz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J2]
  have h2 : f (Complex.exp ((θ : ℂ) * Complex.I)) = rot θ := by
    rw [hfz, rot]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have key : f (Complex.exp ((θ : ℂ) * Complex.I)) = NormedSpace.exp (θ • J2) := by
    rw [Complex.exp_eq_exp_ℂ, ← h1]
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.map_exp f (LinearMap.continuous_of_finiteDimensional f.toLinearMap) _
  rw [← key, h2]

/-- The first of the three `2 × 2` computations of the proof of
Proposition 7.2.1: for `S = π·Id`, `exp(tJS)` is the rotation of angle `tπ`.

The book writes the angle as `−tπ`; with Mathlib's `J = !![0, −1; 1, 0]` the
sign is `+`, since `exp(εJ₂) = Id + εJ₂ + O(ε²)` has `−ε` in the upper right
corner, as `rot ε` does.  (An earlier version of this file stated `rot (−tπ)`,
which is false.)  The rotation for `S = −π·Id` is the same lemma with `−θ`; the
hyperbolic case `S = diag(π, −π)` is not stated. -/
theorem exp_rotation_fin_two (t : ℝ) :
    NormedSpace.exp (t • (J2 * (Real.pi • (1 : Matrix (Fin 2) (Fin 2) ℝ)))) = rot (t * Real.pi) := by
  rw [Matrix.mul_smul, Matrix.mul_one, smul_smul, exp_smul_J2]

end FinTwo

end Chapter7
end MorseFloer
