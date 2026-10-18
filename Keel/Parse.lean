import Keel.APIs.Parse

/-!
# Keel.Parse: total parsing

A parser monad over token buffers (`List`, `Array`, `ByteArray`, slices) whose
every parser is a total function: loops and recursion are well-founded on the
tokens left, with no fuel and no `partial`. The laws are equations for
`Parser.parse`, the meaning of a parser on a list (`Keel/Proofs/Parse.lean`).
-/
