import VCCBGPartII

set_option linter.unusedDecidableInType false

/-!
# Proved solution — Theorem 4

This module imports the full proof development (`reptable_ops_properties.lean`,
which defines `TableState`/`Status`/`VCover` and proves `Property4`, and
`thm4.lean`, which packages these into `Theorem4`) and derives the
Mathlib-only wrapper from it.

Given a witness `F : Finset V` for the `→` direction, we build the
`TableState` that freezes exactly `F` and removes everything else, show it is a
valid freeze/remove outcome with frozen set `F`, and read off `VCover G F`
from `Theorem4`. For the `←` direction we run `Theorem4` the other way to
get a valid state with frozen set `S'`, then recover the closure
condition on `S'` from `RemoveInvariant`/`AllFrozenOrRemoved` applied to
that state.

The Theorem4_wrapper challenge is stated over a bare Finset F, while Theorem4
itself is stated over a TableState. Hence, closing this gap requires some additional
work here.
-/

theorem VCCBGPartII.Theorem4_wrapper
    {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (S' : Finset V) :
    (∃ F : Finset V, (∀ ⦃u v : V⦄, u ∉ F → G.Adj u v → v ∈ F) ∧ F = S')
      ↔ (∀ ⦃u v : V⦄, G.Adj u v → u ∈ S' ∨ v ∈ S') := by
  constructor
  · -- (→) Build the TableState that freezes exactly F, removes the rest.
    rintro ⟨F, hinv, hFS⟩
    classical
    have hvalid : IsValidFreezeRemove
        ({ status := fun v => if v ∈ F then Status.frozen else Status.removed,
           reps   := fun _ => (∅ : Finset V) } : TableState G) := by
      constructor
      · -- RemoveInvariant
        intro u v hu hadj
        by_cases huF : u ∈ F
        · simp only [huF, ite_true] at hu
          exact absurd hu (by decide)
        · have hvF : v ∈ F := hinv huF hadj
          simp [hvF]
      · -- AllFrozenOrRemoved
        intro v
        by_cases hvF : v ∈ F
        · left; simp [hvF]
        · right; simp [hvF]
    have hfrozen : FrozenSet
        ({ status := fun v => if v ∈ F then Status.frozen else Status.removed,
           reps   := fun _ => (∅ : Finset V) } : TableState G) = F := by
      ext v
      simp only [FrozenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hvF : v ∈ F <;> simp [hvF]
    rw [← hFS]
    exact (Theorem4 hcubic hbridgeless F).mp ⟨_, hvalid, hfrozen⟩
  · -- (←) Run Theorem4 backwards, then read the closure condition off the
    -- resulting state via RemoveInvariant/AllFrozenOrRemoved.
    intro hvc
    obtain ⟨st, hvalid, hfrozen⟩ := (Theorem4 hcubic hbridgeless S').mpr hvc
    refine ⟨S', ?_, rfl⟩
    intro u v huS hadj
    have hu : st.status u = Status.removed := by
      rcases hvalid.2 u with h | h
      · exfalso
        have hmem : u ∈ FrozenSet st := Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩
        rw [hfrozen] at hmem
        exact huS hmem
      · exact h
    have hv : st.status v = Status.frozen := hvalid.1 hu hadj
    have hvmem : v ∈ FrozenSet st := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
    rwa [hfrozen] at hvmem
