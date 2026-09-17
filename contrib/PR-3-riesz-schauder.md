# PR 3 — Riesz–Schauder: compact perturbations of Fredholm operators

**Branch name (suggested):** `halmaghi/fredholm-compact-perturbation` (from `master`, independent
of #43904 and #43905)
**Title:**

    feat(Analysis/Normed/Operator/Fredholm): compact perturbations of Fredholm operators

**Files touched:** `Mathlib/Analysis/Normed/Operator/Fredholm/CompactPerturbation.lean` (new,
418 lines), `Mathlib.lean` (import line, via `lake exe mk_all`), `docs/references.bib`
(`brezis2011`).
**Opened:** https://github.com/leanprover-community/mathlib4/pull/43906 (2026-09-18), commit `bebf4d9`
**Zulip thread (2026-09-18):** https://leanprover.zulipchat.com/#narrow/channel/144837-PR-reviews/topic/.2343906.20.60feat.28Analysis.2FNormed.2FOperator.2FFredholm.29.3A.20compact.20per/near/625102271
**Workspace:** `~/projects/mathlib4-master`, branch `halmaghi/fredholm-compact-perturbation`
(from `master` `a218e50`); full diff in `contrib/pr-riesz-schauder.patch`.

**Body:**

```
Let `E` be a Banach space over `𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`) and `c : E →L[𝕜] E` a compact
operator. This PR proves the Riesz–Schauder theorem and its consequence for Fredholm operators:

* `IsCompactOperator.isFredholm_one_add`: `1 + c` is Fredholm;
* `IsCompactOperator.index_one_add`: `(1 + c).index = 0`;
* `ContinuousLinearMap.IsFredholm.add_isCompactOperator`: `u + k` is Fredholm for `u` Fredholm
  and `k` compact;
* `ContinuousLinearMap.IsFredholm.index_add_isCompactOperator`: `(u + k).index = u.index`.

The last two complete `IsFredholm.add_hasFiniteRange` (finite-rank perturbations) and the
index API of `Fredholm/Basic.lean` and `Fredholm/Open.lean` (`index_comp`,
`eventually_nhds_index_eq`), both of which are used here.

The proof of `1 + c` Fredholm goes through the Fredholm alternative
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet` rather than the Riesz theory of ascent and
descent or the adjoint: the kernel `N` is finite-dimensional because `c = -1` on it; on a closed
complement `M` of `N` (Hahn–Banach, hence `RCLike`) the operator is bounded below by a
compactness argument, so the range is closed; and the cokernel is finite-dimensional because an
injective finite-rank correction `T + h ∘ P` of `T = 1 + c`, which exists as soon as `E ⧸ range T`
is infinite-dimensional, would be surjective by the Fredholm alternative. The index vanishes
because `t ↦ (1 + t • c).index` is locally constant on `ℝ` and `0` at `t = 0`. The perturbation
statements follow from `q ∘L (u + k) = 1 + (compact)` for a quasi-inverse `q` of `u`, together
with `IsFredholm.comp_iff_right` and `IsFredholm.index_comp`.

Reference: Brezis, *Functional analysis, Sobolev spaces and PDE*, Theorem 6.6.

The proofs were developed with the help of an LLM (Claude Code) and then checked and edited
by the author, who takes responsibility for every line.
```

**Labels** (bot commands, each on its own line in a comment): `LLM-generated`, `t-analysis`.

**Design points a reviewer may raise**

- *Why `RCLike 𝕜` and not `IsRCLikeNormedField 𝕜`?* Only the Hahn–Banach closed complement
  (`Submodule.ClosedComplemented.of_finiteDimensional`) needs it, and it is stated for
  `IsRCLikeNormedField`; `FiniteDimensional.proper_rclike` (used for local compactness of
  finite-dimensional subspaces) is stated for `RCLike`. Generalising is possible with a little
  work; `RCLike` covers every use in sight.
- *Namespaces.* Lemmas about `1 + c` live in `IsCompactOperator` (dot notation on the
  compactness hypothesis); the perturbation lemmas in `ContinuousLinearMap.IsFredholm`, next to
  `add_hasFiniteRange`.
- *`isCompactOperator_of_hasNoetherianRange`* (a finite-rank continuous operator is compact) is
  stated at top level, like `isCompactOperator_of_locallyCompactSpace_dom`; a reviewer may
  prefer `LinearMap.HasNoetherianRange.isCompactOperator`.

**Verification on master `a218e50`** (all clean): `lake build` of the module, `lake exe
runLinter` on the module, `lake exe lint-style`, `lake exe mk_all`, `#print axioms` on the four
main theorems (`propext`, `Classical.choice`, `Quot.sound` only). `lint-bib` cannot run locally
(no `bibtool`); the entry follows the file's format (no trailing comma on the last field).

**Checklist before opening**

- [ ] `git checkout -b halmaghi/fredholm-compact-perturbation master`, commit the three files
- [ ] push to the fork, `gh pr create` with the title and body above
- [ ] comment with the two label commands
- [ ] Zulip `#PR reviews`, new topic
