module
public import Mathlib
/-! we define vertex cover. -/
/-- `VCover G S`: every edge of G has at least one endpoint in S.
    Only common thread between proof of Np-completeness and polynomial time. -/
public abbrev VCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ S ∨ v ∈ S
