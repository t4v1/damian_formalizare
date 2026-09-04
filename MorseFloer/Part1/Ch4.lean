import MorseFloer.Part1.Ch3

/-!
# Chapter 4: Morse homology, applications

Formalization of Chapter 4 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part I, printed pages 75–102).

Chapter 3 built the complex of critical points and its homology; this chapter
computes with it.  The sections are:

* **§4.1** names the homology `HM⋆(V)` of the complex of Chapter 3 and records
  that it only depends on the manifold;
* **§4.2** the Künneth formula: the complex of `f + g` on `M × N` is the tensor
  product of the complexes of `f` and `g` (Proposition 4.2.1), whence the mod `2`
  homology of a product (Corollaries 4.2.2 and 4.2.3);
* **§4.3** Poincaré duality: the complex of `−f` is the transposed complex of
  `f` with the grading reversed (Propositions 4.3.1 and 4.3.2);
* **§4.4** the Euler characteristic, the Poincaré polynomial and the **Morse
  inequalities** (Corollary 4.4.1, Remark 4.4.2, Proposition 4.4.3);
* **§4.5** homology and connectivity (Proposition 4.5.1 and its corollaries,
  Proposition 4.5.7);
* **§4.6** functoriality and homotopy invariance (Theorems 4.6.1 and 4.6.2);
* **§4.7** the long exact sequence of a pair;
* **§4.8** applications: `H₁` of a simply connected manifold (4.8.1), Brouwer's
  fixed point theorem, the mod `2` homology of `Pⁿ(ℝ)` (Theorem 4.8.2) and
  Borsuk–Ulam (Theorem 4.8.3) with its corollaries.

## What is formalized here, and how

The homology of Chapter 3 is attached to *abstract data* — a finite set `Crit`
of critical points, an index function `ind` and a count function `cnt` — because
Mathlib has no moduli spaces of trajectories.  Everything in this chapter that
is a statement about that data is stated and proved; everything that is a
statement about a *manifold* (functoriality, connectivity, the long exact
sequence of a pair) cannot even be phrased and is listed as a gap below.

Working over a field `K` (the book works over `Z/2` precisely so that the
rank–nullity theorem is available, Remark 4.4.2), we define

* `numCrit ind k = cₖ(f)`, the number of critical points of index `k`;
* `cyclesAt`, `boundariesIn`, `betti ind cnt k = βₖ = dim Hₖ`;
* `eulerChar` and `poincarePoly`.

**Proved in full** (no geometric input beyond `BrokenPairs`):

* `betti_add_bdim`, `bdim_add_finrank_cyclesAt` — rank–nullity for the complex;
* `betti_le_numCrit` — **the Morse inequalities `βₖ ≤ cₖ`** (Proposition 4.4.3);
* `sum_betti_le_card` — the total form of Proposition 4.4.3: a Morse function
  has at least `Σ βₖ` critical points;
* `sum_alt_numCrit` — the telescoping identity
  `Σ (−1)ᵏ cₖ = Σ (−1)ᵏ βₖ + (−1)ᴺ dim Bₙ`, from which follow
  `eulerChar_eq_alt_sum_numCrit` (Remark 4.4.2: the Euler characteristic is the
  alternating sum of the numbers of critical points), `card_crit_modEq`
  (**Corollary 4.4.1**: the number of critical points modulo `2` depends only on
  the homology) and `strong_morse_inequality`, the sharper alternating form
  `Σ_{k≤m} (−1)^{m−k} βₖ ≤ Σ_{k≤m} (−1)^{m−k} cₖ`;
* `poincarePoly_eval_neg_one` — `P_V(−1) = χ(V)`;
* `eulerChar_eq_zero_of_odd` — Remark 4.4.7, the Euler characteristic of an
  odd-dimensional closed manifold vanishes (from Poincaré duality);
* `betti_dual` — **Proposition 4.3.1**, `βₖ = β_{n−k}`, for the complex of `−f`,
  which is the transposed complex with the grading reversed.  The linear algebra
  behind it, `Matrix.rank_transpose`, is Mathlib's;
* `betti_of_count_zero` and the examples: the torus (Poincaré polynomial
  `1 + 2t + t²`, Euler characteristic `0`) and `Pⁿ(ℝ)` (**Theorem 4.8.2**);
* `borsuk_ulam_of_odd` and `exists_eq_antipode` — **Corollaries 4.8.4 and
  4.8.5** of Borsuk–Ulam, deduced from Theorem 4.8.3.

**Stated with `sorry`**, because the proof needs geometry Mathlib does not have,
or bookkeeping that is not attempted here:

* `brokenPairs_prod`, `betti_prod` — Proposition 4.2.1 and
  Corollaries 4.2.2, 4.2.3 (Künneth).  The product complex is defined; that it
  is a complex is the algebraic half of Proposition 4.2.1 and holds only in
  characteristic `2` unless signs are inserted, as the book notes.
* `finrank_homology_dual_int` — Proposition 4.3.2, duality over `ℤ` for an
  oriented manifold.  Note that the book's statement `HM_{n−k}(V; Z) ≅ HMₖ(V; Z)`
  cannot be taken literally: the complex of `−f` is the transposed complex, whose
  homology is *cohomology*, and over `ℤ` the two differ by torsion — for `P³(ℝ)`,
  `HM₁ = Z/2` while `HM₂ = 0`.  What is recorded here is the duality of the free
  ranks; over a field, which is Proposition 4.3.1, there is no discrepancy.
* `betti_sumComplex` — the additivity of §4.1 and Corollary 4.5.5 over a
  disjoint union.
* `brouwer_fixedPoint`, `no_retraction_closedBall`, `borsuk_ulam` — §4.8.b and
  Theorem 4.8.3.  Contrary to what one might expect, **this Mathlib version
  contains neither Brouwer's fixed point theorem nor Borsuk–Ulam** (a search for
  `brouwer` finds only Brouwerian lattices, and for `borsuk` only the
  Borsuk–Mazurkiewicz example on local contractibility), so they are stated
  here.  Their corollaries are proved from them.
* `exists_antipodal_pair_of_closed_cover` — Corollary 4.8.6.

## Gaps: results carrying no Lean declaration

* **Remark 4.1.2** and all of **§4.6** (Theorems 4.6.1 and 4.6.2, Proposition
  4.6.3, Lemma 4.6.6) and **§4.7** (the long exact sequence of a pair).  These
  speak of smooth maps between manifolds and of the induced maps on Morse
  homology; with abstract count data there is no manifold and no induced map.
  The purely homological half of §4.7 — that a short exact sequence of complexes
  induces a long exact sequence — is Mathlib's
  `CategoryTheory.ShortComplex.ShortExact` together with
  `HomologySequence.snakeInput`, and applies verbatim to `morseComplex`.
* **Proposition 4.5.1** (`HM₀ ≅ Z/2` for a connected manifold), **Corollary
  4.5.3**, **Remark 4.5.6** and **Proposition 4.5.7** (a Morse function without
  critical points of index `1` forces simple connectivity): all of these need
  the connectivity of `V` and the unstable manifolds of the index-`1` critical
  points, none of which is expressible.
* **Proposition 4.8.1** (`HM₁ = 0` for a simply connected manifold): needs
  `π₁(V)` of the manifold carrying the complex.
* **§4.8.e** (the complex of critical points computes the cellular homology of
  `V`): needs ordered Morse functions and cellular homology of the manifold.
* **Examples 4.1.1, 4.4.4, 4.4.6, 4.4.8, 4.7.1** are commentary on manifolds; the
  torus and `Pⁿ(ℝ)` computations they use are recorded below as complexes.
-/

namespace MorseFloer
namespace Chapter4

open MorseFloer.Chapter3

/-! ## §4.1 Homology

The homology of the complex of critical points is `HM⋆(V)`; Chapter 3 provides
it as `morseHomology`.  For the computations of this chapter we need its
*dimension*, so we work over a field `K` (the book works over `Z/2` for exactly
this reason, Remark 4.4.2) and describe `Hₖ` concretely as `Ker ∂ₖ / Im ∂ₖ₊₁`.

Recall the indexing convention of Chapter 3: `dLin ind cnt k` is the
differential `Cₖ₊₁ → Cₖ`, so `cycles ind cnt k` is the space of cycles in degree
`k + 1` and `boundaries ind cnt k` the space of boundaries in degree `k`. -/

section Complex

variable {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
  {ind : Crit → ℕ} {cnt : Crit → Crit → R}

/-- `Zₖ`, the cycles in degree `k`.  Every chain of degree `0` is a cycle, since
the differential leaving degree `0` is zero. -/
noncomputable def cyclesAt (ind : Crit → ℕ) (cnt : Crit → Crit → R) :
    ∀ k : ℕ, Submodule R (Chains R ind k)
  | 0 => ⊤
  | (k + 1) => cycles ind cnt k

@[simp] theorem cyclesAt_zero (ind : Crit → ℕ) (cnt : Crit → Crit → R) :
    cyclesAt ind cnt 0 = ⊤ := rfl

@[simp] theorem cyclesAt_succ (ind : Crit → ℕ) (cnt : Crit → Crit → R) (k : ℕ) :
    cyclesAt ind cnt (k + 1) = cycles ind cnt k := rfl

/-- `Im ∂ₖ₊₁ ⊆ Ker ∂ₖ` in every degree, so the quotient below is the book's
`Hₖ = Ker ∂ₖ / Im ∂ₖ₊₁`. -/
theorem boundaries_le_cyclesAt (h : BrokenPairs ind cnt) (k : ℕ) :
    boundaries ind cnt k ≤ cyclesAt ind cnt k := by
  cases k with
  | zero => exact le_top
  | succ k => exact boundaries_le_cycles h k

/-- `Bₖ` seen inside `Zₖ`, so that `HMₖ` is the quotient
`cyclesAt ind cnt k ⧸ boundariesIn ind cnt k`. -/
noncomputable def boundariesIn (ind : Crit → ℕ) (cnt : Crit → Crit → R) (k : ℕ) :
    Submodule R (cyclesAt ind cnt k) :=
  Submodule.comap (cyclesAt ind cnt k).subtype (boundaries ind cnt k)

end Complex

section Basic

variable {K : Type*} [Field K] {Crit : Type*} [Fintype Crit]
  {ind : Crit → ℕ} {cnt : Crit → Crit → K}

/-- `cₖ(f)`: the number of critical points of index `k` (§4.4). -/
def numCrit (ind : Crit → ℕ) (k : ℕ) : ℕ := Fintype.card (CritSet ind k)

theorem finrank_chains (ind : Crit → ℕ) (k : ℕ) :
    Module.finrank K (Chains K ind k) = numCrit ind k :=
  Module.finrank_fintype_fun_eq_card K

/-- `βₖ = dim HMₖ`, the `k`-th Betti number (§4.4): the dimension of
`Ker ∂ₖ / Im ∂ₖ₊₁`. -/
noncomputable def betti (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) : ℕ :=
  Module.finrank K ((cyclesAt ind cnt k) ⧸ boundariesIn ind cnt k)

/-- `dim Bₖ`, the dimension of the space of boundaries in degree `k`. -/
noncomputable def bdim (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) : ℕ :=
  Module.finrank K (boundaries ind cnt k)

/-- `dim Hₖ + dim Bₖ = dim Zₖ`: the defining property of the quotient. -/
theorem betti_add_bdim (h : BrokenPairs ind cnt) (k : ℕ) :
    betti ind cnt k + bdim ind cnt k = Module.finrank K (cyclesAt ind cnt k) := by
  have h2 : Module.finrank K (boundariesIn ind cnt k) = bdim ind cnt k :=
    (Submodule.comapSubtypeEquivOfLe (boundaries_le_cyclesAt h k)).finrank_eq
  have h1 := Submodule.finrank_quotient_add_finrank (boundariesIn ind cnt k)
  simp only [betti]
  rw [← h2]
  exact h1

/-- **Rank–nullity for `∂ₖ : Cₖ₊₁ → Cₖ`**: `dim Bₖ + dim Zₖ₊₁ = cₖ₊₁`.  This is
the "kernel–image theorem" the book invokes in Remark 4.4.2, and the reason for
working over a field. -/
theorem bdim_add_finrank_cyclesAt (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) :
    bdim ind cnt k + Module.finrank K (cyclesAt ind cnt (k + 1)) = numCrit ind (k + 1) := by
  have h : Module.finrank K (LinearMap.range (dLin ind cnt k))
      + Module.finrank K (LinearMap.ker (dLin ind cnt k))
      = Module.finrank K (Chains K ind (k + 1)) :=
    LinearMap.finrank_range_add_finrank_ker (dLin ind cnt k)
  rw [finrank_chains] at h
  exact h

/-- `c₀ = β₀ + dim B₀`. -/
theorem numCrit_zero_eq (h : BrokenPairs ind cnt) :
    numCrit ind 0 = betti ind cnt 0 + bdim ind cnt 0 := by
  have h1 := betti_add_bdim h 0
  rw [cyclesAt_zero, finrank_top, finrank_chains] at h1
  omega

/-- `cₖ₊₁ = dim Bₖ + (βₖ₊₁ + dim Bₖ₊₁)`. -/
theorem numCrit_succ_eq (h : BrokenPairs ind cnt) (k : ℕ) :
    numCrit ind (k + 1) = bdim ind cnt k + (betti ind cnt (k + 1) + bdim ind cnt (k + 1)) := by
  have h1 := betti_add_bdim h (k + 1)
  have h2 := bdim_add_finrank_cyclesAt ind cnt k
  omega

omit [Fintype Crit] in
/-- Above the top index there are no critical points. -/
theorem isEmpty_critSet {f : Crit → ℕ} {n m : ℕ} (hf : ∀ c, f c ≤ n) (hm : n < m) :
    IsEmpty (CritSet f m) :=
  ⟨fun c => by have h1 := hf c.1; have h2 := c.2; omega⟩

/-- If there is no critical point of index `k + 1` then `∂ₖ = 0`. -/
theorem bdim_eq_zero_of_isEmpty {k : ℕ} (hE : IsEmpty (CritSet ind (k + 1))) :
    bdim ind cnt k = 0 := by
  have h0 : dLin ind cnt k = 0 := by
    ext x b
    have := hE
    simp
  show Module.finrank K (LinearMap.range (dLin ind cnt k)) = 0
  rw [h0, LinearMap.range_zero, finrank_bot]

/-- The total number of critical points is the sum of the `cₖ`. -/
theorem card_eq_sum_numCrit {N : ℕ} (hN : ∀ c, ind c ≤ N) :
    Fintype.card Crit = ∑ k ∈ Finset.range (N + 1), numCrit ind k := by
  rw [← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := ind) (t := Finset.range (N + 1))
      (fun c _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hN c)))]
  exact Finset.sum_congr rfl fun k _ => (Fintype.card_subtype _).symm

/-- A complex with vanishing differential has `βₖ = cₖ`. -/
theorem betti_of_count_zero (ind : Crit → ℕ) (k : ℕ) :
    betti ind (fun _ _ => (0 : K)) k = numCrit ind k := by
  have hb : bdim ind (fun _ _ => (0 : K)) k = 0 := by
    show Module.finrank K (boundaries ind (fun _ _ => (0 : K)) k) = 0
    rw [boundaries_zero ind k, finrank_bot]
  have hz : Module.finrank K (cyclesAt ind (fun _ _ => (0 : K)) k) = numCrit ind k := by
    cases k with
    | zero => rw [cyclesAt_zero, finrank_top]; exact finrank_chains ind 0
    | succ k =>
        rw [cyclesAt_succ, cycles_zero, finrank_top]
        exact finrank_chains ind (k + 1)
  have h := betti_add_bdim (brokenPairs_zero (R := K) ind) k
  omega

end Basic

/-! ## §4.2 The Künneth formula

If `f` and `g` are Morse functions on `M` and `N` with adapted Smale
pseudo-gradients `X` and `Y`, then `f + g` is a Morse function on `M × N` whose
critical points are the pairs `(a, a')`, with `Ind(a, a') = Ind a + Ind a'`, and
whose pseudo-gradient is `(X, Y)`.  Since the flow of `(X, Y)` is the product of
the flows, a connecting trajectory between critical points of consecutive
indices must be constant in one factor, so

`n((a,a'),(b,b')) = n_Y(a',b')` if `a = b`, `n_X(a,b)` if `a' = b'`, and `0`
otherwise.

That is exactly the differential `∂_X ⊗ 1 + 1 ⊗ ∂_Y` of the tensor product of
the two complexes, which is Proposition 4.2.1. -/

section Kunneth

variable {K : Type*} [Field K] {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]
  [DecidableEq Crit₁] [DecidableEq Crit₂]

/-- The index on `Crit(f + g) = Crit f × Crit g`: `Ind(a, a') = Ind a + Ind a'`. -/
def prodIndex (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) : Crit₁ × Crit₂ → ℕ :=
  fun p => ind₁ p.1 + ind₂ p.2

/-- The count function of the product, as computed in §4.2.  (For critical
points of consecutive indices at most one of the two tests can succeed, so the
sum written here agrees with the book's case distinction.) -/
def prodCount (cnt₁ : Crit₁ → Crit₁ → K) (cnt₂ : Crit₂ → Crit₂ → K) :
    Crit₁ × Crit₂ → Crit₁ × Crit₂ → K :=
  fun a b => (if a.1 = b.1 then cnt₂ a.2 b.2 else 0) + (if a.2 = b.2 then cnt₁ a.1 b.1 else 0)

/-- **Proposition 4.2.1** (algebraic half).  `Φ(a ⊗ a') = (a, a')` identifies
`(C⋆(f) ⊗ C⋆(g), ∂_X ⊗ 1 + 1 ⊗ ∂_Y)` with `(C⋆(f + g), ∂_(X,Y))`; in particular
the product differential squares to zero.  As the book points out, without signs
this holds only in characteristic `2` — the cross terms `∂_X ⊗ ∂_Y` cancel in
pairs there, which is why the passage to homology in Corollary 4.2.2 is stated
over `Z/2`.

Not proved: the identification is a finite but long computation with sums over
subtypes of a product type, which is not attempted here. -/
theorem brokenPairs_prod {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (h₁ : BrokenPairs ind₁ cnt₁) (h₂ : BrokenPairs ind₂ cnt₂) (h2 : (2 : K) = 0) :
    BrokenPairs (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂) := by
  sorry

/-- **Corollaries 4.2.2 and 4.2.3 (the Künneth formula).**  Over `Z/2` — more
generally over a field — the homology of the product complex is the tensor
product of the homologies, so the Betti numbers satisfy
`βₖ(M × N) = Σ_{i+j=k} βᵢ(M) βⱼ(N)`.

Not proved: this is the Künneth theorem for complexes of vector spaces, which
would first require the identification `brokenPairs_prod` above. -/
theorem betti_prod {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (h₁ : BrokenPairs ind₁ cnt₁) (h₂ : BrokenPairs ind₂ cnt₂) (h2 : (2 : K) = 0)
    (hP : BrokenPairs (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂)) (k : ℕ) :
    betti (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂) k
      = ∑ i ∈ Finset.range (k + 1), betti ind₁ cnt₁ i * betti ind₂ cnt₂ (k - i) := by
  sorry

end Kunneth

/-! ## §4.3 Poincaré duality

The critical points of index `k` of `f` are the critical points of index `n − k`
of `−f`, and `−X` is a pseudo-gradient adapted to `−f`; a trajectory of `X` from
`a` to `b` is a trajectory of `−X` from `b` to `a`.  So the complex of `−f` is
the complex of `f` with the grading reversed and the differential transposed:
`C_{n−k}(−f) = Cₖ(f)⋆` and `∂_{−X} = ᵗ∂_X`.

Both halves are visible in the data: `dualCount cnt a b = cnt b a`, and the
index function of `−f` is any `ind'` with `ind c + ind' c = n`. -/

section Duality

variable {K : Type*} [Field K] {Crit : Type*} [Fintype Crit]

/-- The matrix of `∂ₖ : Cₖ₊₁ → Cₖ` in the bases of critical points. -/
def diffMatrix (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) :
    Matrix (CritSet ind k) (CritSet ind (k + 1)) K :=
  Matrix.of fun b a => cnt a.1 b.1

theorem dLin_eq_mulVecLin (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) :
    dLin ind cnt k = (diffMatrix ind cnt k).mulVecLin := by
  refine LinearMap.ext fun x => funext fun b => ?_
  show (∑ a : CritSet ind (k + 1), x a * cnt a.1 b.1) = _
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, diffMatrix, Matrix.of_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem bdim_eq_rank (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) :
    bdim ind cnt k = (diffMatrix ind cnt k).rank := by
  show Module.finrank K (LinearMap.range (dLin ind cnt k)) = _
  rw [dLin_eq_mulVecLin]
  rfl

/-- The count function of `−f`: the transpose of that of `f` (§4.3). -/
def dualCount (cnt : Crit → Crit → K) : Crit → Crit → K := fun a b => cnt b a

variable {ind ind' : Crit → ℕ} {cnt : Crit → Crit → K} {n : ℕ}

/-- A critical point of index `k` for `f` is a critical point of index `n − k`
for `−f` (Remark 1.3.3, `MorseFloer.Chapter1.index_neg_add_index`, is what makes
the indices add up to `n`). -/
def dualCritEquiv (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j = n) :
    CritSet ind' j ≃ CritSet ind k :=
  Equiv.subtypeEquivRight fun c => by have := hn c; omega

/-- `−f` has as many critical points of index `n − k` as `f` has of index `k`. -/
theorem numCrit_dual (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j = n) :
    numCrit ind' j = numCrit ind k :=
  Fintype.card_congr (dualCritEquiv hn hkj)

/-- The differential of the dual complex is the transpose of the differential of
the original one, so it has the same rank.  This is where Poincaré duality
actually happens; the linear algebra is `Matrix.rank_transpose`. -/
theorem bdim_dual (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j + 1 = n) :
    bdim ind' (dualCount cnt) j = bdim ind cnt k := by
  rw [bdim_eq_rank, bdim_eq_rank,
    show diffMatrix ind' (dualCount cnt) j
        = (diffMatrix ind cnt k).transpose.submatrix
            (dualCritEquiv hn (show (k + 1) + j = n by omega))
            (dualCritEquiv hn (show k + (j + 1) = n by omega)) from rfl,
    Matrix.rank_submatrix, Matrix.rank_transpose]

/-- **Proposition 4.3.1 (Poincaré duality).**  For a closed manifold of
dimension `n`, `HMₖ(V; Z/2)` and `HM_{n−k}(V; Z/2)` have the same dimension.

Here `ind'` is the index function of `−f` (so `ind c + ind' c = n`, which is
Remark 1.3.3) and `dualCount cnt` is the transposed count function, i.e. the
complex of `−f`; the conclusion is `β_{n−k}(−f) = βₖ(f)`.  The proof is the one
the book indicates: the two complexes have the same numbers of generators in
dual degrees and their differentials are transposes of each other, hence have
equal ranks, and the Betti numbers are determined by those data. -/
theorem betti_dual (h : BrokenPairs ind cnt) (h' : BrokenPairs ind' (dualCount cnt))
    (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j = n) :
    betti ind' (dualCount cnt) j = betti ind cnt k := by
  have hind : ∀ c, ind c ≤ n := fun c => by have := hn c; omega
  have hind' : ∀ c, ind' c ≤ n := fun c => by have := hn c; omega
  have hc : numCrit ind' j = numCrit ind k := numCrit_dual hn hkj
  cases k with
  | zero =>
      cases j with
      | zero =>
          have hn0 : n = 0 := by omega
          have hb : bdim ind cnt 0 = 0 :=
            bdim_eq_zero_of_isEmpty (isEmpty_critSet hind (by omega))
          have hb' : bdim ind' (dualCount cnt) 0 = 0 :=
            bdim_eq_zero_of_isEmpty (isEmpty_critSet hind' (by omega))
          have hA := numCrit_zero_eq h (ind := ind) (cnt := cnt)
          have hA' := numCrit_zero_eq h' (ind := ind') (cnt := dualCount cnt)
          omega
      | succ j₀ =>
          have hb' : bdim ind' (dualCount cnt) (j₀ + 1) = 0 :=
            bdim_eq_zero_of_isEmpty (isEmpty_critSet hind' (by omega))
          have hbd : bdim ind' (dualCount cnt) j₀ = bdim ind cnt 0 :=
            bdim_dual hn (by omega)
          have hA := numCrit_zero_eq h (ind := ind) (cnt := cnt)
          have hB' := numCrit_succ_eq h' (ind := ind') (cnt := dualCount cnt) j₀
          omega
  | succ k₀ =>
      cases j with
      | zero =>
          have hb : bdim ind cnt (k₀ + 1) = 0 :=
            bdim_eq_zero_of_isEmpty (isEmpty_critSet hind (by omega))
          have hbd : bdim ind' (dualCount cnt) 0 = bdim ind cnt k₀ :=
            bdim_dual hn (by omega)
          have hB := numCrit_succ_eq h (ind := ind) (cnt := cnt) k₀
          have hA' := numCrit_zero_eq h' (ind := ind') (cnt := dualCount cnt)
          omega
      | succ j₀ =>
          have hbd₁ : bdim ind' (dualCount cnt) j₀ = bdim ind cnt (k₀ + 1) :=
            bdim_dual hn (by omega)
          have hbd₂ : bdim ind' (dualCount cnt) (j₀ + 1) = bdim ind cnt k₀ :=
            bdim_dual hn (by omega)
          have hB := numCrit_succ_eq h (ind := ind) (cnt := cnt) k₀
          have hB' := numCrit_succ_eq h' (ind := ind') (cnt := dualCount cnt) j₀
          omega

/-- **Proposition 4.3.2 (Poincaré duality for oriented manifolds).**  For a
closed oriented manifold of dimension `n`, the homology of the complex of `−f`
in degree `n − k` is dual to the homology of the complex of `f` in degree `k`.

A word of care is needed over `ℤ`, and it is the reason this statement is about
*ranks*.  The proof of §4.3 identifies `C_{n−k}(−f)` with the dual `Cₖ(f)⋆` and
`∂_{−X}` with the transpose `ᵗ∂_X`; the homology of the transposed complex is
therefore the *cohomology* of the original one, and over `ℤ` cohomology differs
from homology by a shift of the torsion (universal coefficients).  It really
does differ: for `P³(ℝ)`, whose integral Morse complex is
`ℤ →⁰ ℤ →² ℤ →⁰ ℤ`, one has `H₁ = Z/2` and `H₂ = 0`, so no isomorphism
`HM₂ ≅ HM₁` can hold, although `n − 1 = 2`.  Over a field — the setting of
Proposition 4.3.1, and of `betti_dual` above — the difficulty disappears, and
over `ℤ` what survives is the duality of the free ranks, stated here.

Not proved: it follows from `betti_dual` over `ℚ` together with the flatness of
`ℚ` over `ℤ`, which is not carried out. -/
theorem finrank_homology_dual_int {cntZ : Crit → Crit → ℤ}
    (h : BrokenPairs ind cntZ) (h' : BrokenPairs ind' (fun a b => cntZ b a))
    (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j = n) :
    Module.finrank ℤ
        (cyclesAt ind' (fun a b => cntZ b a) j ⧸ boundariesIn ind' (fun a b => cntZ b a) j)
      = Module.finrank ℤ (cyclesAt ind cntZ k ⧸ boundariesIn ind cntZ k) := by
  sorry

end Duality

/-! ## §4.4 Euler characteristic, Poincaré polynomial, Morse inequalities

Everything here is linear algebra over a field, exactly as in the book: writing
`cₖ = dim Cₖ`, `zₖ = dim Ker ∂ₖ` and `bₖ = dim Im ∂ₖ₊₁`, rank–nullity gives
`cₖ₊₁ = bₖ + zₖ₊₁` and the definition of homology gives `βₖ = zₖ − bₖ`.  Hence
`cₖ ≥ βₖ` (the Morse inequalities) and, the `bₖ` telescoping in the alternating
sum, `Σ (−1)ᵏ cₖ = Σ (−1)ᵏ βₖ` (the Euler characteristic). -/

section Euler

variable {K : Type*} [Field K] {Crit : Type*} [Fintype Crit]
  {ind : Crit → ℕ} {cnt : Crit → Crit → K}

/-- **Proposition 4.4.3 (the Morse inequalities).**  A Morse function has at
least `βₖ` critical points of index `k`. -/
theorem betti_le_numCrit (h : BrokenPairs ind cnt) (k : ℕ) :
    betti ind cnt k ≤ numCrit ind k := by
  cases k with
  | zero => have := numCrit_zero_eq h (ind := ind) (cnt := cnt); omega
  | succ k => have := numCrit_succ_eq h (ind := ind) (cnt := cnt) k; omega

/-- The telescoping identity behind Corollary 4.4.1 and Remark 4.4.2:
`Σ_{k ≤ N} (−1)ᵏ cₖ = Σ_{k ≤ N} (−1)ᵏ βₖ + (−1)ᴺ dim B_N`. -/
theorem sum_alt_numCrit (h : BrokenPairs ind cnt) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (numCrit ind k : ℤ)
      = (∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (betti ind cnt k : ℤ))
        + (-1 : ℤ) ^ N * (bdim ind cnt N : ℤ) := by
  induction N with
  | zero =>
      have hA : numCrit ind 0 = betti ind cnt 0 + bdim ind cnt 0 := numCrit_zero_eq h
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul]
      exact_mod_cast hA
  | succ N ih =>
      have hB : numCrit ind (N + 1)
          = bdim ind cnt N + (betti ind cnt (N + 1) + bdim ind cnt (N + 1)) :=
        numCrit_succ_eq h N
      have hB' : (numCrit ind (N + 1) : ℤ)
          = (bdim ind cnt N : ℤ) + ((betti ind cnt (N + 1) : ℤ) + (bdim ind cnt (N + 1) : ℤ)) := by
        exact_mod_cast hB
      rw [Finset.sum_range_succ (f := fun k => (-1 : ℤ) ^ k * (numCrit ind k : ℤ)),
        Finset.sum_range_succ (f := fun k => (-1 : ℤ) ^ k * (betti ind cnt k : ℤ)), ih, hB']
      ring

/-- The same telescoping without signs: `Σ cₖ = Σ βₖ + 2 Σ_{k<N} dim Bₖ + dim B_N`. -/
theorem sum_numCrit_eq (h : BrokenPairs ind cnt) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), numCrit ind k
      = (∑ k ∈ Finset.range (N + 1), betti ind cnt k)
        + 2 * (∑ k ∈ Finset.range N, bdim ind cnt k) + bdim ind cnt N := by
  induction N with
  | zero =>
      have hA : numCrit ind 0 = betti ind cnt 0 + bdim ind cnt 0 := numCrit_zero_eq h
      simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty,
        Nat.mul_zero, Nat.add_zero]
      omega
  | succ N ih =>
      have hB : numCrit ind (N + 1)
          = bdim ind cnt N + (betti ind cnt (N + 1) + bdim ind cnt (N + 1)) :=
        numCrit_succ_eq h N
      rw [Finset.sum_range_succ (f := fun k => numCrit ind k),
        Finset.sum_range_succ (f := fun k => betti ind cnt k),
        Finset.sum_range_succ (f := fun k => bdim ind cnt k), ih, hB]
      ring

/-- **The Euler characteristic** `χ(V) = Σ (−1)ᵏ βₖ` (§4.4).  `N` is any bound
for the Morse index, e.g. the dimension of the manifold. -/
noncomputable def eulerChar (ind : Crit → ℕ) (cnt : Crit → Crit → K) (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (betti ind cnt k : ℤ)

/-- **Remark 4.4.2.**  The Euler characteristic is the alternating sum of the
numbers of critical points of a Morse function; in particular that alternating
sum does not depend on the function. -/
theorem eulerChar_eq_alt_sum_numCrit (h : BrokenPairs ind cnt) {N : ℕ} (hN : ∀ c, ind c ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (numCrit ind k : ℤ) = eulerChar ind cnt N := by
  rw [eulerChar, sum_alt_numCrit h N,
    bdim_eq_zero_of_isEmpty (cnt := cnt) (isEmpty_critSet hN (Nat.lt_succ_self N))]
  simp

/-- **Corollary 4.4.1.**  The number of critical points of a Morse function,
taken modulo `2`, depends only on the homology — hence only on the manifold and
not on the function. -/
theorem card_crit_modEq (h : BrokenPairs ind cnt) {N : ℕ} (hN : ∀ c, ind c ≤ N) :
    Nat.ModEq 2 (Fintype.card Crit) (∑ k ∈ Finset.range (N + 1), betti ind cnt k) := by
  have hcard := card_eq_sum_numCrit (ind := ind) hN
  have hsum := sum_numCrit_eq h N
  have hb : bdim ind cnt N = 0 :=
    bdim_eq_zero_of_isEmpty (cnt := cnt) (isEmpty_critSet hN (Nat.lt_succ_self N))
  show Fintype.card Crit % 2 = _ % 2
  omega

/-- **Proposition 4.4.3, total form.**  A Morse function on `V` has at least
`Σ βₖ` critical points. -/
theorem sum_betti_le_card (h : BrokenPairs ind cnt) {N : ℕ} (hN : ∀ c, ind c ≤ N) :
    (∑ k ∈ Finset.range (N + 1), betti ind cnt k) ≤ Fintype.card Crit := by
  have hcard := card_eq_sum_numCrit (ind := ind) hN
  have hsum := sum_numCrit_eq h N
  omega

/-- An alternating sum with the exponents counted downwards. -/
theorem sum_neg_one_pow_sub (x : ℕ → ℕ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - k) * (x k : ℤ)
      = (-1 : ℤ) ^ m * ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (x k : ℤ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (-1 : ℤ) ^ (m - k) = (-1 : ℤ) ^ m * (-1 : ℤ) ^ k := by
    have h1 : m + k = (m - k) + 2 * k := by omega
    calc (-1 : ℤ) ^ (m - k) = (-1 : ℤ) ^ (m - k) * ((-1 : ℤ) ^ 2) ^ k := by norm_num
      _ = (-1 : ℤ) ^ ((m - k) + 2 * k) := by rw [pow_add, pow_mul]
      _ = (-1 : ℤ) ^ (m + k) := by rw [← h1]
      _ = (-1 : ℤ) ^ m * (-1 : ℤ) ^ k := by rw [pow_add]
  rw [hpow, mul_assoc]

/-- **The strong Morse inequalities.**  For every `m`,
`βₘ − βₘ₋₁ + ⋯ ≤ cₘ − cₘ₋₁ + ⋯`; the difference of the two sides is
`dim Bₘ ≥ 0`.  Taking `m` above the top index turns the inequality into the
equality of Euler characteristics. -/
theorem strong_morse_inequality (h : BrokenPairs ind cnt) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - k) * (betti ind cnt k : ℤ)
      ≤ ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - k) * (numCrit ind k : ℤ) := by
  have hsq : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
  have hb : (0 : ℤ) ≤ (bdim ind cnt m : ℤ) := Nat.cast_nonneg _
  rw [sum_neg_one_pow_sub (fun k => betti ind cnt k) m,
    sum_neg_one_pow_sub (fun k => numCrit ind k) m, sum_alt_numCrit h m]
  set A : ℤ := ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (betti ind cnt k : ℤ) with hA
  have key : (-1 : ℤ) ^ m * (A + (-1 : ℤ) ^ m * (bdim ind cnt m : ℤ))
      = (-1 : ℤ) ^ m * A + (bdim ind cnt m : ℤ) := by
    have hstep : (-1 : ℤ) ^ m * ((-1 : ℤ) ^ m * (bdim ind cnt m : ℤ))
        = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ m) * (bdim ind cnt m : ℤ) := by ring
    rw [mul_add, hstep, hsq, one_mul]
  rw [key]
  linarith

/-- **The Poincaré polynomial** `P_V(t) = Σ βₖ tᵏ` (§4.4). -/
noncomputable def poincarePoly (ind : Crit → ℕ) (cnt : Crit → Crit → K) (N : ℕ) :
    Polynomial ℤ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (betti ind cnt k : ℤ) * Polynomial.X ^ k

/-- `P_V(−1) = χ(V)`: the relation between the Poincaré polynomial and the Euler
characteristic (§4.4). -/
theorem poincarePoly_eval_neg_one (ind : Crit → ℕ) (cnt : Crit → Crit → K) (N : ℕ) :
    (poincarePoly ind cnt N).eval (-1) = eulerChar ind cnt N := by
  simp only [poincarePoly, eulerChar, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Remark 4.4.7.**  The Euler characteristic of a closed manifold of odd
dimension vanishes: by Poincaré duality the terms of the alternating sum cancel
in pairs.  Stated with the duality of the Betti numbers as a hypothesis, which
is what `betti_dual` provides. -/
theorem eulerChar_eq_zero_of_odd {n : ℕ} (hodd : Odd n)
    (hdual : ∀ k ≤ n, betti ind cnt k = betti ind cnt (n - k)) :
    eulerChar ind cnt n = 0 := by
  have h1 : ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - j) * (betti ind cnt (n - j) : ℤ)
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * (betti ind cnt j : ℤ) :=
    Finset.sum_range_reflect (fun j => (-1 : ℤ) ^ j * (betti ind cnt j : ℤ)) (n + 1)
  have h2 : ∀ j ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (n - j) * (betti ind cnt (n - j) : ℤ)
        = (-1 : ℤ) * ((-1 : ℤ) ^ j * (betti ind cnt j : ℤ)) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hb : betti ind cnt (n - j) = betti ind cnt j := by
      have hstep := hdual (n - j) (Nat.sub_le _ _)
      rw [hstep]
      congr 1
      omega
    have h5 : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨j, rfl⟩
    have h3 : (-1 : ℤ) ^ (n - j) * (-1 : ℤ) ^ j = (-1 : ℤ) ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have h4 : (-1 : ℤ) ^ n = -1 := hodd.neg_one_pow
    have hpow : (-1 : ℤ) ^ (n - j) = -((-1 : ℤ) ^ j) := by
      calc (-1 : ℤ) ^ (n - j) = (-1 : ℤ) ^ (n - j) * ((-1 : ℤ) ^ j * (-1 : ℤ) ^ j) := by
            rw [h5, mul_one]
        _ = ((-1 : ℤ) ^ (n - j) * (-1 : ℤ) ^ j) * (-1 : ℤ) ^ j := by ring
        _ = (-1 : ℤ) ^ n * (-1 : ℤ) ^ j := by rw [h3]
        _ = -((-1 : ℤ) ^ j) := by rw [h4]; ring
    rw [hb, hpow]
    ring
  have h6 : eulerChar ind cnt n = -eulerChar ind cnt n := by
    conv_lhs => rw [eulerChar, ← h1]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, eulerChar]
    ring
  linarith

end Euler

/-! ## §4.5 Homology and connectivity

Proposition 4.5.1 (`HM₀(V; Z/2) ≅ Z/2` for `V` connected), Corollary 4.5.3, its
integral variants and Proposition 4.5.7 (a Morse function without critical
points of index `1` forces `V` simply connected) are all statements about a
connected manifold and its unstable manifolds; none of them can be phrased for
abstract count data, so none carries a Lean declaration.

What *is* algebraic is the observation opening §4.1 and used again in Corollary
4.5.5: the complex of a disjoint union is the direct sum of the complexes. -/

section DisjointUnion

variable {K : Type*} [Field K] {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]

/-- The count function of a disjoint union: no trajectory joins the two pieces. -/
def sumCount (cnt₁ : Crit₁ → Crit₁ → K) (cnt₂ : Crit₂ → Crit₂ → K) :
    Crit₁ ⊕ Crit₂ → Crit₁ ⊕ Crit₂ → K
  | Sum.inl a, Sum.inl b => cnt₁ a b
  | Sum.inr a, Sum.inr b => cnt₂ a b
  | _, _ => 0

/-- **§4.1 and Corollary 4.5.5.**  `C⋆(f ⊔ g) = C⋆(f) ⊕ C⋆(g)` and
`∂_{X ⊔ Y} = ∂_X ⊕ ∂_Y`, so the Betti numbers of a disjoint union add up.  (With
Proposition 4.5.1 this gives Corollary 4.5.5: `HM₀` and `HMₙ` have dimension the
number of connected components.)

Not proved: the direct sum decomposition of the complex is routine but requires
transporting cycles and boundaries along the equivalence
`CritSet (Sum.elim ind₁ ind₂) k ≃ CritSet ind₁ k ⊕ CritSet ind₂ k`. -/
theorem betti_sumComplex {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (h₁ : BrokenPairs ind₁ cnt₁) (h₂ : BrokenPairs ind₂ cnt₂)
    (hS : BrokenPairs (Sum.elim ind₁ ind₂) (sumCount cnt₁ cnt₂)) (k : ℕ) :
    betti (Sum.elim ind₁ ind₂) (sumCount cnt₁ cnt₂) k = betti ind₁ cnt₁ k + betti ind₂ cnt₂ k := by
  sorry

end DisjointUnion

/-! ## §4.6 Functoriality, §4.7 the long exact sequence

Theorem 4.6.1 (a `C^∞` map `u : V → W` induces `u⋆ : HM⋆(V) → HM⋆(W)`,
functorially), Theorem 4.6.2 (homotopic maps induce the same morphism),
Proposition 4.6.3 (a Morse–Smale pair on a submanifold extends to the ambient
manifold with the same critical points and the same differential), Lemma 4.6.6
and the whole of §4.7 speak about smooth maps between manifolds and the Morse
homology *of a manifold*.  In this development the homology is attached to
abstract count data, so there is no manifold to map and no declaration is made.

Two remarks on what would be reusable.  The proof of Theorem 4.6.1 reduces the
general case to embeddings by factoring `u` through `V → Dᴺ × W`, and its only
homological ingredient is that `(i₀)⋆` is an isomorphism, which is Künneth
together with `HM⋆(Dᴺ) = Z` in degree `0`.  The long exact sequence of §4.7 is
obtained from the short exact sequence of complexes
`C⋆(f) → C⋆(f̃) → C⋆(f̃|_{W − 𝒱})`, and the passage from a short exact sequence of
complexes to a long exact sequence in homology is already in Mathlib
(`CategoryTheory.ShortComplex.ShortExact` and `HomologySequence`), applicable to
`MorseFloer.Chapter3.morseComplex`. -/

/-! ## §4.8 Applications -/

section Applications

/-! ### §4.8.b Brouwer's fixed point theorem

The book re-proves Brouwer's theorem from `HM_{n−1}(Dⁿ) = 0`: a fixed point free
self-map of the disc produces a retraction `r : Dⁿ → Sⁿ⁻¹` with `r ∘ j = id`,
which is impossible since the identity of `HM_{n−1}(Sⁿ⁻¹) = Z/2` would factor
through `0`.  This Mathlib version has neither Brouwer's theorem nor the
homology of spheres, so both statements are recorded here without proof. -/

/-- **Theorem 2.3.3, reproved in §4.8.b (Brouwer).**  A continuous self-map of
the closed unit ball has a fixed point.  Not in this Mathlib version. -/
theorem brouwer_fixedPoint {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x = x := by
  sorry

/-- **§4.8.b.**  There is no retraction of the closed ball onto its boundary
sphere: a map of the ball into the sphere must move some point of the sphere. -/
theorem no_retraction_closedBall {n : ℕ}
    (r : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hr : ContinuousOn r (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo r (Metric.closedBall 0 1) (Metric.sphere 0 1)) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, r x ≠ x := by
  sorry

/-! ### §4.8.c The mod 2 homology of the real projective space

The double cover `Sⁿ → Pⁿ(ℝ)` gives a short exact sequence of complexes
`0 → C⋆(f) → C⋆(f ∘ p) → C⋆(f) → 0` whose long exact sequence, `HM⋆(Sⁿ)` being
trivial in the intermediate degrees, forces the connecting map
`HMₖ(Pⁿ(ℝ)) → HMₖ₋₁(Pⁿ(ℝ))` to be an isomorphism for `0 ≤ k ≤ n`; hence
Theorem 4.8.2.

Here we record the complex itself: `Pⁿ(ℝ)` carries a Morse function with
exactly one critical point in each index `0, …, n`, and, there being a single
generator in each degree while the homology is `Z/2` in each degree, its mod `2`
differential vanishes.  With that complex the theorem becomes a computation. -/

/-- The Morse index function of the standard Morse function on `Pⁿ(ℝ)`: one
critical point of each index `0, …, n`. -/
def projIndex (n : ℕ) : Fin (n + 1) → ℕ := fun i => (i : ℕ)

/-- The mod `2` count function of that Morse function: it vanishes (§4.8.c). -/
def projCount (n : ℕ) : Fin (n + 1) → Fin (n + 1) → ZMod 2 := fun _ _ => 0

theorem projCount_brokenPairs (n : ℕ) : BrokenPairs (projIndex n) (projCount n) :=
  brokenPairs_zero (projIndex n)

theorem numCrit_projIndex (n k : ℕ) (hk : k ≤ n) : numCrit (projIndex n) k = 1 := by
  have : Unique (CritSet (projIndex n) k) := by
    refine ⟨⟨⟨⟨k, by omega⟩, rfl⟩⟩, ?_⟩
    rintro ⟨⟨a, ha⟩, rfl⟩
    rfl
  exact Fintype.card_unique

/-- **Theorem 4.8.2.**  `HMₖ(Pⁿ(ℝ); Z/2) ≅ Z/2` for `0 ≤ k ≤ n`. -/
theorem betti_proj (n k : ℕ) (hk : k ≤ n) : betti (projIndex n) (projCount n) k = 1 := by
  have hz : projCount n = fun _ _ => (0 : ZMod 2) := rfl
  rw [hz, betti_of_count_zero (projIndex n) k, numCrit_projIndex n k hk]

/-! ### §4.4 examples: the torus

The function `cos 2πx + cos 2πy` on `T²` has one minimum, two saddles and one
maximum and, all its counts being even, a vanishing mod `2` differential
(§3.1.c).  Its Poincaré polynomial is `1 + 2t + t²`, its Euler characteristic is
`0`, and Example 4.4.4 follows: a Morse function on `T²` has at least four
critical points. -/

theorem betti_torus_zero : betti Chapter3.torusIndex Chapter3.torusCount 0 = 1 := by
  have hz : Chapter3.torusCount = fun _ _ => (0 : ZMod 2) := rfl
  rw [hz, betti_of_count_zero Chapter3.torusIndex 0]
  decide

theorem betti_torus_one : betti Chapter3.torusIndex Chapter3.torusCount 1 = 2 := by
  have hz : Chapter3.torusCount = fun _ _ => (0 : ZMod 2) := rfl
  rw [hz, betti_of_count_zero Chapter3.torusIndex 1]
  decide

theorem betti_torus_two : betti Chapter3.torusIndex Chapter3.torusCount 2 = 1 := by
  have hz : Chapter3.torusCount = fun _ _ => (0 : ZMod 2) := rfl
  rw [hz, betti_of_count_zero Chapter3.torusIndex 2]
  decide

/-- **Example 4.4.4.**  The Betti numbers of `T²` sum to `4`, so by Proposition
4.4.3 a Morse function on the torus has at least four critical points. -/
theorem sum_betti_torus :
    (∑ k ∈ Finset.range 3, betti Chapter3.torusIndex Chapter3.torusCount k) = 4 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    betti_torus_zero, betti_torus_one, betti_torus_two]

/-- The Euler characteristic of the torus is `0`. -/
theorem eulerChar_torus : eulerChar Chapter3.torusIndex Chapter3.torusCount 2 = 0 := by
  rw [eulerChar, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    betti_torus_zero, betti_torus_one, betti_torus_two]
  norm_num

/-! ### §4.8.d The Borsuk–Ulam theorem

Theorem 4.8.3 itself needs the mod `2` homology of the projective spaces and the
commutation of the connecting map with `ψ⋆`, so it is stated without proof (and
is not in this Mathlib version).  Its corollaries 4.8.4 and 4.8.5 are deduced
from it here, exactly as in the book. -/

/-- **Theorem 4.8.3 (Borsuk–Ulam).**  There is no continuous odd map
`Sⁿ → Sⁿ⁻¹`.  Not in this Mathlib version. -/
theorem borsuk_ulam (n : ℕ) :
    ¬ ∃ φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n),
        ContinuousOn φ (Metric.sphere 0 1) ∧
        Set.MapsTo φ (Metric.sphere 0 1) (Metric.sphere 0 1) ∧
        ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, φ (-x) = -φ x := by
  sorry

/-- **Corollary 4.8.4.**  A continuous odd map `Sⁿ → ℝⁿ` vanishes somewhere: if
it did not, dividing by its norm would produce a map forbidden by Theorem
4.8.3. -/
theorem borsuk_ulam_of_odd (n : ℕ)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn ψ (Metric.sphere 0 1))
    (hodd : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ψ (-x) = -ψ x) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ψ x = 0 := by
  by_contra hcon
  push Not at hcon
  have hne : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ‖ψ x‖ ≠ 0 := by
    intro x hx
    exact norm_ne_zero_iff.mpr (hcon x hx)
  have hneg : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      -x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact mem_sphere_zero_iff_norm.mp hx
  refine borsuk_ulam n ⟨fun x => ‖ψ x‖⁻¹ • ψ x, ?_, ?_, ?_⟩
  · exact (hcont.norm.inv₀ hne).smul hcont
  · intro x hx
    show ‖ψ x‖⁻¹ • ψ x ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hne x hx)
  · intro x hx
    have hxn := hodd x hx
    show ‖ψ (-x)‖⁻¹ • ψ (-x) = -(‖ψ x‖⁻¹ • ψ x)
    rw [hxn, norm_neg, smul_neg]

/-- **Corollary 4.8.5 (the temperature–pressure theorem).**  Every continuous
map `Sⁿ → ℝⁿ` takes the same value at some pair of antipodal points; apply
Corollary 4.8.4 to `x ↦ ψ x − ψ(−x)`. -/
theorem exists_eq_antipode (n : ℕ)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn ψ (Metric.sphere 0 1)) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ψ x = ψ (-x) := by
  have hneg : Set.MapsTo (fun x : EuclideanSpace ℝ (Fin (n + 1)) => -x)
      (Metric.sphere 0 1) (Metric.sphere 0 1) := by
    intro x hx
    show -x ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact mem_sphere_zero_iff_norm.mp hx
  have hcont' : ContinuousOn (fun x => ψ x - ψ (-x)) (Metric.sphere 0 1) :=
    hcont.sub (hcont.comp (continuous_neg.continuousOn) hneg)
  have hodd : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      (fun x => ψ x - ψ (-x)) (-x) = -((fun x => ψ x - ψ (-x)) x) := by
    intro x _
    simp only [neg_neg]
    abel
  obtain ⟨x, hx, hx0⟩ := borsuk_ulam_of_odd n (fun x => ψ x - ψ (-x)) hcont' hodd
  exact ⟨x, hx, sub_eq_zero.mp hx0⟩

/-- **Corollary 4.8.6.**  If `n + 1` closed sets cover `Sⁿ`, one of them
contains a pair of antipodal points: apply Corollary 4.8.5 to the map whose
coordinates are the distances to the first `n` of them.  Not proved here. -/
theorem exists_antipodal_pair_of_closed_cover (n : ℕ)
    (F : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hclosed : ∀ i, IsClosed (F i))
    (hcover : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ⊆ ⋃ i, F i) :
    ∃ (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin (n + 1))),
      x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ∧ x ∈ F i ∧ -x ∈ F i := by
  sorry

end Applications

end Chapter4
end MorseFloer
