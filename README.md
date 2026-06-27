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

## Acknowledgements

This project was developed with AI assistance, predominantly ChatGPT and
occasionally Gemini AI. 

## References

Joseph Bernstein, *Representations of Finite Groups*, Problem assignment 7.5,
May 2007 ([link](https://www.math.tau.ac.il/~bernstei/courses/2007_Spring/Representations_of_finite_groups/pr/pr7v.pdf)).

Jean-Pierre Serre, *Linear Representations of Finite Groups*, Springer, 1977.






  