# VCCBG Formalization: Part II (Theorem 8)

This repository contains the formal verification in **Lean** of a result from the paper on the complexity of the **Vertex Cover Problem on Cubic Bridgeless Graphs (VCCBG)**. 

Specifically, this repository formalizes the proof of correctness of an unconditional deterministic polynomial-time algorithm for VCCBG (Theorem 8, Part II of the paper). 

---

## Overview of the Formalization

Theorem 8 is proven via the conjunction of two main lemmas:
1. **Lemma 6 (Soundness):** *"If Algorithm 1 returns Yes, then the given instance of VC–CBG is a Yes instance."*
2. **Lemma 5 (Completeness):** *"If the given instance of VC–CBG is a Yes instance, then Algorithm 1 returns Yes."*

### Key Concepts & Analogies
The formalization strictly mirrors the structure of the paper, covering:
* **Novel Data Structure:** Represents table.
* **Novel Concept:** *Diminishing hops* (conceptually analogous to augmenting paths used for maximum matching).
* **Graph-Theoretic Theorem:** Bridging diminishing hops and minimum vertex cover (analogous to Berge's Theorem).
* **Algorithmic Result:** An algorithm utilizing diminishing hops to find a minimum vertex cover (analogous to the Blossom Algorithm using augmenting paths to find maximum matching due to Berge Theorem).

---

## Related Repositories
A strict superset of the broader formalization being carried out of other results can be found in the main repository: [KunalRelia/VCCBG](https://github.com/KunalRelia/VCCBG)

---

## Building & Verification
To build the Lean files of this project, you need to have a working version of Lean installed on your machine. See [the installation instructions](https://lean-lang.org/install/).

Next, please clone this repository. Then, follow these steps:

```
% cd VCCBG_PartII/
% lake exe cache get (or lake exe cache get! for complete download)
% lake build
```

---

## AI Assistance Disclaimer
The Lean code in this repository was generated and refined iteratively using Claude (Sonnet 4.6 / 5 / 5.5 using the Low / Medium / Max thinking modes). Gemini, GPT, and Claude were also utilized for debugging, with careful cross-checking to ensure logical soundness and freedom from context bias. All proofs have been checked and verified by the Lean theorem prover.