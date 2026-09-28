module
/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
/-
  Formal Lean 4 / Mathlib Verification of Theorem 4
  "Freezing/removing the endpoints of a Represents Table corresponds
   exactly to a vertex cover of the graph."

  Source: p.36 of the paper (lines 1200-1222) and building on Properties 3 and 4 of §5.2.2.

  Statement (informal, as in the paper). Given a graph G with a set V of
  m vertices and the corresponding represents table R populated by a set
  W of m endpoints: a set S'' of l endpoints in R is frozen (for some
  1 ≤ l ≤ m) and the disjoint set W \ S'' of m − l endpoints is removed,
  if and only if there is a vertex cover S' of l vertices in G that
  corresponds to the set S'' of frozen endpoints.

  This file builds directly on `reptable_ops_properties.lean`:
  it reuses `TableState`, `Status`, `VCover`, and its `Property4`,
  which supplies exactly the (⇒) direction of Theorem 4.

  Modeling notes.
  • "A set S'' of endpoints is frozen and the disjoint set W \ S'' is
    removed" is modeled as a `TableState G` in which *every* vertex
    is either `frozen` or `removed`, and the frozen/removed assignment is
    *consistent with removal*. This is the hypothesis `hremove_freezes_nbrs`
    that `Property4` already takes; we name it `RemoveInvariant` here.
    so it can be quantified over directly in the statement of Theorem 4 (cf.
    `remove_initialState_freezes_neighbors` /
    `remove_initialState_satisfies_invariant`).
  • "S'' of l endpoints is frozen ... W \ S'' of m − l endpoints is
    removed" is `AllFrozenOrRemoved`.
  • "The set S'' of frozen endpoints" is read off a `TableState` via
    `FrozenSet`.
  • The bound `1 ≤ l ≤ m` from the paper's statement is automatically proven:
    `l = S''.card` and `S'' : Finset V` with `[Fintype V]` automatically gives
    `0 ≤ l ≤ m`; the paper's `l ≥ 1` is a standing assumption that G actually
    has at least one edge (so that the empty set is not a valid cover).

  With this setup, Theorem 4 becomes an iff between "there is a
  represents-table state whose frozen set is exactly S''` and satisfies
  the process's structural invariants" and "S'' is a vertex cover of G":
  precisely the (⇒)/(⇐) split the paper's own proof uses (Property 3 +
  Property 4 for (⇒); "just freeze the cover, remove the rest" for (⇐)).
-/

public import VCCBGPartII.reptable_ops_properties
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables (matching reptable_ops_properties.lean)
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The structural content of "freeze S'', remove W \ S''"
-- ═══════════════════════════════════════════════════════════════════════════

/-- The invariant maintained throughout the paper's freeze/remove process:
    whenever an endpoint `u` is
    removed, every endpoint `v` adjacent to it is frozen. -/
public abbrev RemoveInvariant (st : TableState G) : Prop :=
  ∀ ⦃u v : V⦄, st.status u = Status.removed → G.Adj u v → st.status v = Status.frozen

/-- "Every endpoint of the represents table is either frozen or removed" —
    (Property 3: the fully-populated table's endpoints are all
    of `V`). -/
public abbrev AllFrozenOrRemoved (st : TableState G) : Prop :=
  ∀ v : V, st.status v = Status.frozen ∨ st.status v = Status.removed

/-- The set S'' of frozen endpoints recorded by a table state. -/
public abbrev FrozenSet (st : TableState G) : Finset V :=
  Finset.univ.filter (fun v => st.status v = Status.frozen)

/-- A `TableState` is a *valid freeze/remove outcome* of the process the
    paper describes: every endpoint is frozen or removed, and removal is
    always consistent with the neighbour-freezing invariant. -/
public abbrev IsValidFreezeRemove (st : TableState G) : Prop :=
  RemoveInvariant st ∧ AllFrozenOrRemoved st

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Theorem 4
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 4**. A finset `S'` of vertices arises as the frozen set of
    *some* valid freeze/remove outcome of the represents-table process for
    `G` if and only if `S'` is a vertex cover of `G`.

    `hcubic`/`hbridgeless` are retained, as in `Lemma4` (a cubic
    bridgeless graph, for which the represents table is guaranteed to
    exist and be fully populated, Property 3). -/
public theorem Theorem4
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (S' : Finset V) :
    (∃ st : TableState G, IsValidFreezeRemove st ∧ FrozenSet st = S')
      ↔ VCover G S' := by
  constructor
  -- ─────────────────────────────────────────────────────────────────────
  -- (⇒) If some valid freeze/remove state has frozen set S', then S' is
  --      a vertex cover. This is exactly Property 4 (which itself only
  --      needs Property 3 implicitly, via `AllFrozenOrRemoved`).
  -- ─────────────────────────────────────────────────────────────────────
  · rintro ⟨st, ⟨hinv, hall⟩, hfrozen⟩
    rw [← hfrozen]
    exact Property4 st hinv hall
  -- ─────────────────────────────────────────────────────────────────────
  -- (⇐) Given a vertex cover S', freeze exactly S' and remove everything
  --      else; this state trivially satisfies both structural conditions.
  -- ─────────────────────────────────────────────────────────────────────
  · intro hvc
    classical
    refine ⟨{ status := fun v => if v ∈ S' then Status.frozen else Status.removed,
              reps   := fun _ => (∅ : Finset V) }, ⟨?_, ?_⟩, ?_⟩
    · -- RemoveInvariant
      intro u v hu hadj
      by_cases huS : u ∈ S'
      · simp only [huS, ite_true] at hu
        exact absurd hu (by decide)
      · -- u ∉ S', so since S' is a vertex cover of the edge (u,v), v ∈ S'.
        have hcov := hvc hadj
        have hvS : v ∈ S' := hcov.resolve_left huS
        simp only [hvS, ite_true]
    · -- AllFrozenOrRemoved
      intro v
      by_cases hvS : v ∈ S'
      · left; simp [hvS]
      · right; simp [hvS]
    · -- FrozenSet = S'
      ext v
      simp only [FrozenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hvS : v ∈ S'
      · simp [hvS]
      · simp [hvS]

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Directional corollaries, matching the paper's (⇒)/(⇐) split verbatim
-- ═══════════════════════════════════════════════════════════════════════════

/-- (⇒) direction, stated separately: a valid freeze/remove outcome's
    frozen set is a vertex cover. -/
public theorem validFreezeRemove_gives_vcover
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    {st : TableState G} (hvalid : IsValidFreezeRemove st) :
    VCover G (FrozenSet st) :=
  (Theorem4 hcubic hbridgeless (FrozenSet st)).mp ⟨st, hvalid, rfl⟩

/-- (⇐) direction, stated separately: every vertex cover is realized as
    the frozen set of some valid freeze/remove outcome. -/
public theorem vcover_gives_validFreezeRemove
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    {S' : Finset V} (hvc : VCover G S') :
    ∃ st : TableState G, IsValidFreezeRemove st ∧ FrozenSet st = S' :=
  (Theorem4 hcubic hbridgeless S').mpr hvc

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper's two-line proof (p.36, lines 1204-1216):
    (⇒) "the endpoints trivially form a vertex cover (Property 3) ...
         Hence, the frozen endpoints form a vertex cover (Property 4)"
        → `Property4 st hinv hall`, exactly as invoked in
          `validFreezeRemove_gives_vcover`. (Property 3's role — that the
          fully-populated table's endpoints are all of V — is baked into
          our reading of `AllFrozenOrRemoved` as ranging over *all* of
          `V`, rather than being re-proved from a `RepTable`/perfect
          matching here.)
    (⇐) "we can simply freeze the endpoints that correspond to the
         vertices in the vertex cover S' and remove the rest"
        → the explicit `TableState` built in the second branch of
          `Theorem4`'s proof, with `status v = frozen ↔ v ∈ S'`.
-/
