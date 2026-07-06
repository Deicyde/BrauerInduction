import Mathlib

open scoped BigOperators

universe u

namespace BrauerChallenge

/--
Brauer induction — trivial-representation / solvable-subgroup corollary,
stated using **only Mathlib vocabulary**.

The character of the trivial one-dimensional representation `(1 : Representation k G k)`
of a finite group `G` over an algebraically closed field of characteristic zero is an
integer linear combination of the characters of representations induced (`Rep.ind`) from
linear characters `ψ : H →* kˣ` of *solvable* subgroups `H`.  Each linear character is
realized as the one-dimensional representation `h ↦ (ψ h) • id` on `k`, written point-free
as `algebraMap k (Module.End k k) ∘ Units.coeHom k ∘ ψ`.

This is a (strictly weaker) corollary of Brauer's induction theorem on induced characters:
it specializes the theorem to the trivial representation and relaxes the elementary-subgroup
class to the larger solvable-subgroup class.  It is proved in `Solution.lean` from the
previous, elementary form of the challenge (`OldChallenge.lean`).
-/
theorem trivialChar_eq_sum_induced_linear_solvable
    {G : Type u} [Group G] [Finite G]
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] :
    ∃ (ι : Type) (_ : Fintype ι)
      (ns : ι → ℤ)
      (Hs : ι → Subgroup G)
      (ψs : ∀ i, Hs i →* kˣ),
      (∀ i, IsSolvable (Hs i)) ∧
        (1 : Representation k G k).character =
          ∑ i, ns i •
            (Rep.ind (Hs i).subtype
              (Rep.of ((algebraMap k (Module.End k k)).toMonoidHom.comp
                ((Units.coeHom k).comp (ψs i))))).ρ.character := by
  sorry

end BrauerChallenge
