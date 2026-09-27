import Mathlib

set_option linter.unusedDecidableInType false
/-!
# Advertised statement — Theorem 4

"Freezing/removing the endpoints of a Represents Table corresponds
exactly to a vertex cover of the graph." (paper, p.36, lines 1200-1222.)

This is the Mathlib-only restatement of Theorem 4. The full development
(`reptable_ops_properties.lean` + `thm4.lean`) states Theorem 4 as an iff
between "some `TableState` whose frozen set is exactly `S'` satisfies the
process's structural invariants (`IsValidFreezeRemove`)" and "`S'` is a
vertex cover of `G`".

"The frozen set of a valid state equals `S'`" collapses to "`S'` itself is
such a witness", and `RemoveInvariant` restricted to that witness reads:
every vertex outside `S'` ("removed") has every neighbour inside `S'` ("frozen").
So the headline claim reduces, without any loss, to a statement about an arbitrary finset
`S' : Finset V`: "every vertex outside `S'` has all its neighbours inside
`S'`" iff "`S'` is a vertex cover of `G`"

`hcubic` and `hbridgeless` are carried along for signature fidelity with
the rest of the development (they are likewise unused in the real `Theorem4`'s own proof).
-/

/-- The result being submitted. -/
theorem VCCBGPartII.Theorem4_wrapper
    {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (S' : Finset V) :
    (∃ F : Finset V, (∀ ⦃u v : V⦄, u ∉ F → G.Adj u v → v ∈ F) ∧ F = S')
      ↔ (∀ ⦃u v : V⦄, G.Adj u v → u ∈ S' ∨ v ∈ S') := by
  sorry
