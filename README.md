RGref-Agda
----------
This repository holds an experimental port of the RGref prototype for rely-guarantee references from
Coq to Agda.

The main advantages of such a port would be
- Agda better supports definitions of recursive-by-reference data structures such as reference-based
  linked lists.  This needs mutual inductive definitions where one type indexes the other.  Agda
  supports this directly, while Coq requires adapting a very cumbersome induction-recursion encoding
  that forces making the main computationally-relevant universe impredicative.

The main disadvantages are
- Agda does not support separating proof terms from program terms the way Coq's Program extension
  allows.  This can be somewhat alleviated with lots of refactoring, but it still clutters the code.
- Agda does not support tactic-based theorem proving, making the proofs (potentially) more brittle.
- Agda does not support a clean separation for extracting only computationally relevant code.  Coq
  separates Prop and Set.  Agda has some support for irrelevance, but it seems complex to use.

This implementation is *extremely* rough.  The Coq implementation is already rough around the edges,
but this version currently lacks many important soundness checks.
