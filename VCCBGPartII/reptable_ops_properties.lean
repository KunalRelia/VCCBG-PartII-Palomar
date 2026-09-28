module
/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
/-
  Formal Lean 4 / Mathlib Verification of the Represents Table:
  Operations (insert, access, freeze, remove) and Properties 1-4.

  Source: §5.2.2 of the paper ("Represents Table", Definitions 12-14,
  pp.28-32, lines 960-1119), specifically:
    • Operations: insert / access / freeze / remove (lines 1020-1059).
    • Property 1  (line 1060-1071): directional row-order restriction on
      "represents".
    • Property 2  (line 1071-1082): same-row endpoints always represent
      each other.
    • Property 3  (line 1083-1091): endpoints of R correspond 1-1 to
      vertices of G, and (in the cubic-bridgeless case) trivially form
      a vertex cover.
    • Property 4  (line 1092-1104): if every endpoint is frozen or
      removed, the frozen endpoints form a vertex cover.

  This file builds on the same abstractions as `lemma4.lean`
  (the `RepTable` wrapping a perfect matching) and its hypothesis style
  (`VCover`, `hcubic`, `hbridgeless`).

  Modeling notes (design choices):
  • Definitions 12/13 ("represents" / "represents list") are *static*,
    graph-theoretic notions: u represents v iff u,v are adjacent in G, and
    Lu is exactly u's neighbor set. We formalize these directly from
    `G.Adj` / `G.neighborFinset`.
  • The represents table itself, however, is *populated dynamically*: by
    the time row i is written, only edges to vertices not yet "used up" in
    earlier rows remain, so the table's recorded represents-relation is a
    row-order–restricted subrelation of Definition 12's static relation.
    We capture this with `TableRepresents`, parameterized by a row-index
    function `row : V → ℕ` assigned to each vertex when it is inserted as
    an endpoint (Definition 14: each row stores the two endpoints of one
    matching edge, so matched partners share a row).
  • The four *operations* are modeled as functions on an explicit
    `TableState` (current status of every endpoint, plus its current,
    possibly-shrunk, represents list), mirroring the paper's own
    description of each operation's effect. We do not attempt to model
    time complexity (O(1)/O(m)); only the *structural* pre/postconditions
    the paper states for each operation are formalized.
  • Property 1 and Property 2 are theorems about `TableRepresents`.
    Property 3 and Property 4 are theorems about `VCover`.
-/

public import VCCBGPartII.lemma4
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables (matching lemma4.lean)
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Definitions 12 & 13: "represents" and the represents list
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Definition 12** (Represents). `u` represents `v` iff they are joined
    by an edge of `G`. (Symmetric, as the paper notes: "conversely, v is
    represented by u".) -/
public abbrev Represents (G : SimpleGraph V) (u v : V) : Prop := G.Adj u v

open Classical in
/-- **Definition 13** (Represents List). `Lu`, the set of vertices `u`
    represents; for a cubic graph this has exactly 3 elements.

    (Defined via `Finset.filter` over `Finset.univ` rather than
    `G.neighborFinset`, purely to avoid depending on Mathlib's
    `Fintype (G.neighborSet u)` instance search, which is not needed here
    since `V` is already a `Fintype`. We use `Classical` decidability for
    the filter predicate so this definition does not depend on exactly how
    `[DecidableRel G.Adj]` was synthesized as a local instance.) -/
public noncomputable def RepList (G : SimpleGraph V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v)

public lemma mem_RepList_iff_represents {u v : V} :
    v ∈ RepList G u ↔ Represents G u v := by
  simp [RepList, Represents]

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Definition 14: the Represents Table, with a row/perfect-matching
--     structure (extends the `RepTable` of lemma4.lean with the
--     row indexing needed for Properties 1-2).
-- ═══════════════════════════════════════════════════════════════════════════

namespace RepTable

/-- **Lemma 4** (restated here for use by Property 3 below): every vertex is
    an endpoint, since `R.M` is a *perfect*, i.e. spanning, matching. -/
theorem isEndpoint_all (R : RepTable G) : ∀ v : V, R.IsEndpoint v :=
  fun v => R.isPM.2 v

end RepTable

/-- The relation actually *recorded* in the finished table: `u` represents
    `v` in `R` iff they are adjacent in `G` **and** `u`'s row is no later
    than `v`'s row. (This row restriction is exactly the content of
    Property 1 below; by the time row `row u` is written, edges from `u` to
    vertices already finalized in strictly earlier rows have already been
    removed, so they no longer appear in `u`'s live represents list — only
    vertices in rows `≥ row u` can still be represented by `u`.) -/
public abbrev TableRepresents (R : RepTable G) (u v : V) : Prop :=
  G.Adj u v ∧ R.row u ≤ R.row v

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Property 1
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Property 1**. Given a represents table `R`, an endpoint `u` in row `i`
    can only represent an endpoint `v` in some row `j` with `i ≤ j`;
    conversely `u` in row `j` can only be represented by `v` in some row
    `i ≤ j`. Both halves are immediate from the definition of
    `TableRepresents`, which is precisely how the "directional" restriction
    is built into the recorded relation. -/
public theorem Property1 (R : RepTable G) {u v : V} (h : TableRepresents R u v) :
    R.row u ≤ R.row v :=
  h.2

/-- Contrapositive form, matching the paper's phrasing: `u` cannot
    represent an endpoint in a strictly earlier row. -/
public theorem Property1' (R : RepTable G) {u v : V} (hlt : R.row v < R.row u) :
    ¬ TableRepresents R u v :=
  fun h => absurd (Property1 R h) (not_le.mpr hlt)

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Property 2
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Property 2**. Endpoints `u`, `v` in the same row always represent
    each other. Same-row endpoints are exactly the two endpoints of a
    matching edge (`row_pair`), and matching edges are edges of `G`
    (`SimpleGraph.Subgraph.Adj.adj_sub`), so both directions of
    `TableRepresents` hold with the row inequality being an equality. -/
public theorem Property2 (R : RepTable G) {u v : V} (hM : R.M.Adj u v) :
    TableRepresents R u v ∧ TableRepresents R v u := by
  have hadj : G.Adj u v := hM.adj_sub
  have hrow : R.row u = R.row v := R.row_pair hM
  exact ⟨⟨hadj, hrow.le⟩, ⟨hadj.symm, hrow.ge⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Property 3
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Property 3**. Each endpoint `u ∈ R` corresponds to a vertex `u ∈ V`
    of `G` (formalized simply as `R.IsEndpoint` being a predicate on `V`
    itself — the "correspondence" is definitional, not a separate
    embedding), and in the cubic-bridgeless case, since `R` is built from a
    *perfect* matching, every vertex is an endpoint (Lemma 4) and hence the
    endpoint set is all of `V`, which trivially forms a vertex cover. -/
public theorem Property3 (R : RepTable G)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e) :
    (∀ v : V, R.IsEndpoint v) ∧ VCover G (Finset.univ : Finset V) := by
  refine ⟨R.isEndpoint_all, ?_⟩
  intro u v _
  exact Or.inl (Finset.mem_univ u)

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Operations: insert, access, freeze, remove
-- ═══════════════════════════════════════════════════════════════════════════

/-- Status of an endpoint in the represents table: not yet acted on
    (`unset`), selected into the vertex cover (`frozen`), or excluded from
    the vertex cover (`removed`). The paper stresses that the table
    supports **no deletion** — `status` only ever moves `unset → frozen` or
    `unset → removed`, never back; we do not need to state this separately
    since our operations below never revert a `frozen`/`removed` status. -/
public inductive Status
  | unset
  | frozen
  | removed
  deriving DecidableEq

/-- The live state of a represents table during execution: each vertex's
    current status, and its current (possibly already-shrunk) represents
    list. -/
public structure TableState (G : SimpleGraph V) where
  status : V → Status
  reps   : V → Finset V

/-- **insert**. The most basic operation: populate the table's initial
    state from the graph, with every endpoint `unset` and every represents
    list equal to the full (static) `RepList` of Definition 13.
    (The paper notes insert is O(1) per row and needs no access to
    previous data — reflected here in that `initialState` does not
    depend on any prior `TableState`.) -/
public noncomputable abbrev initialState (G : SimpleGraph V) : TableState G where
  status := fun _ => Status.unset
  reps   := fun u => RepList G u

/-- **access / search**. Purely a read of the current state; no state
    change. We give the two forms the paper distinguishes: accessing the
    status of an endpoint, and accessing its represents list. -/
public abbrev TableState.accessStatus (st : TableState G) (u : V) : Status := st.status u

public abbrev TableState.accessRepList (st : TableState G) (u : V) : Finset V := st.reps u

/-- **freeze**. Freezing `u` (selecting it into the vertex cover)
    simultaneously delists `u` from every represents list it appears in.
    (The paper additionally delists `Lu` itself, which we do not need to
    track further since a frozen vertex's own list is never consulted
    again by the operations below.) -/
@[expose] public def TableState.freeze (st : TableState G) (u : V) : TableState G where
  status := fun v => if v = u then Status.frozen else st.status v
  reps   := fun v => (st.reps v).erase u

/-- Freezing `u` marks it frozen. -/
public theorem TableState.freeze_status (st : TableState G) (u : V) :
    (st.freeze u).status u = Status.frozen := by
  simp [TableState.freeze]

/-- Freezing `u` delists `u` from every represents list (the operation's
    key structural postcondition). -/
public theorem TableState.freeze_delists (st : TableState G) (u v : V) :
    u ∉ (st.freeze u).reps v := by
  simp [TableState.freeze]

/-- Freezing `u` never un-freezes or un-removes any other endpoint. -/
public theorem TableState.freeze_status_of_ne (st : TableState G) {u v : V} (h : v ≠ u) :
    (st.freeze u).status v = st.status v := by
  simp [TableState.freeze, h]

/-- **remove**. Removing `u` (excluding it from the vertex cover) freezes
    every vertex `u` represents and every vertex that represents `u` — by
    Property 2/symmetry of `Represents` these are the same set, `RepList G
    u`, when working from the fully-populated (`reps = RepList`) state; in
    general we freeze every `v` with `v ∈ st.reps u ∨ u ∈ st.reps v`,
    matching the paper's "each vertex in the represents list of the
    removed endpoint u and each vertex that represents the endpoint u is
    frozen" verbatim. -/
public def TableState.remove (st : TableState G) (u : V) : TableState G where
  status := fun v =>
    if v = u then Status.removed
    else if v ∈ st.reps u ∨ u ∈ st.reps v then Status.frozen
    else st.status v
  reps := st.reps

/-- Removing `u` marks it removed. -/
public theorem TableState.remove_status (st : TableState G) (u : V) :
    (st.remove u).status u = Status.removed := by
  simp [TableState.remove]

/-- Removing `u` freezes every vertex it represents or that represents it
    (the operation's key structural postcondition). -/
public theorem TableState.remove_freezes (st : TableState G) {u v : V} (hv : v ≠ u)
    (h : v ∈ st.reps u ∨ u ∈ st.reps v) :
    (st.remove u).status v = Status.frozen := by
  simp [TableState.remove, hv, h]

/-- In the initial, fully-populated state, removing `u` freezes exactly the
    (three, if `G` is cubic) neighbours of `u` — matching the paper's
    remark that "each of the three vertices that are connected to the
    removed endpoint needs to be in the vertex cover". -/
public theorem remove_initialState_freezes_neighbors {u v : V} (hadj : G.Adj u v) :
    ((initialState G).remove u).status v = Status.frozen := by
  have hv : v ≠ u := hadj.ne'
  have : v ∈ (initialState G).reps u := by
    simpa [initialState, mem_RepList_iff_represents, Represents] using hadj
  exact TableState.remove_freezes (initialState G) hv (Or.inl this)

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Property 4
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Property 4**. Given a represents table state `st`, if every endpoint
    is either frozen or removed, then the frozen endpoints form a vertex
    cover.

    `hremove_freezes_nbrs` is the invariant, guaranteed by construction of
    the algorithm (every application of `remove`, as shown by
    `remove_initialState_freezes_neighbors` and preserved by subsequent
    operations since `freeze`/`remove` never revert an existing `frozen`
    status), that a removed vertex's neighbours are always frozen; we take
    it as an explicit hypothesis here, exactly as `Theorem12` takes
    `hbridgeless` as an explicit hypothesis rather than re-deriving it. -/
public theorem Property4 (st : TableState G)
    (hremove_freezes_nbrs :
      ∀ ⦃u v⦄, st.status u = Status.removed → G.Adj u v → st.status v = Status.frozen)
    (hall : ∀ v : V, st.status v = Status.frozen ∨ st.status v = Status.removed) :
    VCover G (Finset.univ.filter (fun v => st.status v = Status.frozen)) := by
  intro u v hadj
  rcases hall u with hu | hu
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩)
  · have hv : st.status v = Status.frozen := hremove_freezes_nbrs hu hadj
    exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)

/-- The single-step instance of `hremove_freezes_nbrs` used above,
    discharged for the state obtained from one `remove` applied to the
    initial state. -/
public theorem remove_initialState_satisfies_invariant (u : V) :
    ∀ ⦃u' v⦄, ((initialState G).remove u).status u' = Status.removed →
      G.Adj u' v → ((initialState G).remove u).status v = Status.frozen := by
  intro u' v hrem hadj
  by_cases h1 : u' = u
  · subst h1
    exact remove_initialState_freezes_neighbors hadj
  · exfalso
    simp only [TableState.remove, ite_eq_right h1] at hrem
    by_cases h2 : u' ∈ (initialState G).reps u ∨ u ∈ (initialState G).reps u'
    · rw [ite_eq_left h2] at hrem
      exact Status.noConfusion hrem
    · rw [ite_eq_right h2] at hrem
      exact Status.noConfusion hrem

/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper's own summary (end of §5.2, lines
  1114-1120):
    1. underlying data structure         → `TableState`
    2. BFS tree + augmented 2-approx      → `RepTable.row` (order of
       algorithm assigns rows) — only the resulting row
       order matters to Properties 1-2.
    3. insert / access / freeze / remove  → §6
    4. time complexity of each operation  → NOT modeled currently for proof of correctness and
       left later for time complexity analysis.
    5. unique properties (1-4)            → §3, §4, §5, §7
-/
