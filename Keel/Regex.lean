import Keel.APIs.Regex

/-!
# Keel.Regex: regular expressions, matched in linear time

Terms over any character classes (`CharClass κ`), with zero-width
assertions; their meaning `Matches` in context; a matcher by Antimirov's
partial derivatives, compiled once per pattern to numbered tables with a
per-call step cache, for any `Mode` (search, prefix, whole text). Laws:
`derive_correct`, `accepts_iff`, `Nfa.accepts_eq`, `reach_length_le`,
`compile_test_iff`. Imports only Init and Std; each dialect keeps its parser.
-/
