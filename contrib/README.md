# contrib/ — drafts aimed at Mathlib, not part of the MorseFloer library

Files here mirror their intended Mathlib paths so they can be moved over
unchanged. They are **not** imported from `MorseFloer.lean` and are not built by
`lake build`, so they do not enter the project's `sorry` audit. Check one with:

```sh
lake env lean contrib/Mathlib/Analysis/FunctionalSpaces/MorreyInequality.lean
```

## MorreyInequality.lean

Morrey's inequality — the Sobolev embedding `W^{1,p} ↪ L^∞` for `p > n`, and the
Hölder estimate behind it.

**Why this one first.** Mathlib's `Analysis/FunctionalSpaces/SobolevInequality.lean`
proves the Gagliardo–Nirenberg–Sobolev inequality under the hypothesis
`p < finrank ℝ E`. The supercritical case is absent; the name Morrey appears in
Mathlib only as an attribution inside the Rademacher proof. Closing that
asymmetry is a self-contained contribution that does not wait on the unsettled
design of Sobolev spaces themselves, because — like the GNS file — it is stated
for compactly supported `C¹` functions and needs no Sobolev space to exist.

It is also the exact input `MorseFloer/Part2/Ch13.lean` assumes repeatedly: the
constant `K` in `‖g‖_∞ ≤ K‖g‖_{W^{1,p}}`, on a two-dimensional domain where
`p > 2` means `p > n`.

**State.** Statements and constants are final and type-check. The four proofs
carry `sorry`; each docstring names the ingredient it needs. The two that carry
real work are the Riesz-kernel integrability on a ball (where supercriticality
is consumed, and where Mathlib's lack of a polar-coordinates change of variables
bites) and the Riesz potential estimate.

The full rationale, including what Mathlib already has and why the cylinder
`ℝ × S¹` does not fit the Sobolev designs currently in flight, is at
https://claude.ai/code/artifact/6128ff05-9235-473b-beb9-9f0a2614767a
