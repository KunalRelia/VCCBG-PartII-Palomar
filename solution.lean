import VCCBGPartII

set_option linter.unusedDecidableInType false

/-!
# Proved solution — Lemma 4

This module imports the full proof development (`lemma4.lean`, which
defines `RepTable` and proves `Lemma4`/`Lemma4_matched`) and derives the
Mathlib-only wrapper from it. Comparator checks that the declaration
below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.

We build a `RepTable` around the given perfect matching `M` with a
constant (irrelevant) `row` function — Lemma 4 only ever uses `R.M`, so
any choice of `row`/`row_pair` gives the same conclusion for `v` — and
then invoke `Lemma4` from `lemma4.lean`, unfolding `RepTable.IsEndpoint`
back to plain membership in `M.verts`.
-/

theorem VCCBGPartII.Lemma4_wrapper
    {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∀ v : V, v ∈ M.verts := by
  let R : RepTable G := ⟨M, hM, fun _ => 0, fun _ _ _ => rfl⟩
  intro v
  exact Lemma4 hcubic hbridgeless R v
