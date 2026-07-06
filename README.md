# BrauerInduction

Lean 4 formalization of <a
href="https://en.wikipedia.org/wiki/Brauer%27s_theorem_on_induced_characters">Brauer's
induction theorem on induced characters</a> following Bernstein's 2007 proof.

The main result is in file `BrauerInduction.Main`: 

```Lean
BrauerInduction.character_eq_sum_induced_linear
    {G : Type u} [Group G] [Finite G]
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    (V : FDRep k G) :
    ∃ (ι : Type) (_ : Fintype ι)
      (ns : ι → ℤ) (Hs : ι → Subgroup G)
      (ψs : ∀ i, Hs i →* kˣ),
      (∀ i, IsBrauerElementary (Hs i)) ∧
      V.character =
        ∑ i, ns i • (FDRep.indLin (Hs i) (ψs i)).character
```

## Building 

```bash
lake exe cache get
lake build
```

## Comparator check

This repository includes a `leanprover/comparator` harness.

* `Challenge.lean` gives a concise, **pure-Mathlib** statement of a corollary of Brauer
  induction: the character of the trivial representation is a `ℤ`-linear combination of
  characters induced from linear characters of *solvable* subgroups. Its statement uses
  only Mathlib vocabulary (`Rep.ind`, `Representation.character`, `IsSolvable`, …) — no
  definitions from this project.
* `OldChallenge.lean` is the previous challenge: the full, elementary-subgroup form of
  Brauer induction (`character_eq_sum_induced_linear`), stated with a few local helper
  definitions.
* `Solution.lean` proves `Challenge.lean` from the previous (elementary) challenge theorem,
  specializing it to the trivial representation and weakening elementary ⇒ solvable.
* `comparator.json` permits only `propext`, `Classical.choice`, and `Quot.sound`.
 
## Acknowledgements

This project was developed with substantial AI assistance, predominantly ChatGPT and
occasionally Gemini AI. 
 
 ## Note

This is a personal formalization project. It is made public in the hope that
parts of it may be useful or interesting to other Lean users.
 
## References

Joseph Bernstein, *Representations of Finite Groups*, Problem assignment 7.5,
May 2007 ([link](https://www.math.tau.ac.il/~bernstei/courses/2007_Spring/Representations_of_finite_groups/pr/pr7v.pdf)).

Jean-Pierre Serre, *Linear Representations of Finite Groups*, Springer, 1977.






  