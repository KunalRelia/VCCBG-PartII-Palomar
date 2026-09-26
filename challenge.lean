import Mathlib

set_option linter.unusedDecidableInType false
/-!
# Advertised statement — Lemma 4

"Every vertex of a cubic bridgeless graph is listed as an endpoint in the
corresponding represents table." (paper, p.30, lines 1018-1019.)

This is the Mathlib-only restatement of Lemma 4: the full development in
`lemma4.lean` builds a custom `RepTable` structure whose `IsEndpoint`
predicate is *defined* to be membership in the underlying perfect
matching's vertex set (`v ∈ R.M.verts`). So the headline claim reduces,
without any loss, to a statement about an arbitrary perfect matching `M`
of `G`: every vertex of `G` lies in `M.verts`.

`hcubic` and `hbridgeless` are carried along for signature fidelity with
the rest of the development and to document the intended class of graphs;
`M`/`hM` stand in for "the represents table's underlying perfect
matching, as guaranteed to exist by Theorem 3 / Petersen's theorem".
-/

/-- Replace this toy statement and docstring with the result being
submitted. -/
theorem VCCBGPartII.Lemma4_wrapper
    {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∀ v : V, v ∈ M.verts := by
  sorry
