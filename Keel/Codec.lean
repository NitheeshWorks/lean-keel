import Keel.APIs.Codec

/-!
# Keel.Codec: lawful codecs

A `Codec τ α` is an encoder and a `Keel.Parse` decoder with the law that the
decoder reads back the encoding on any tolerated continuation:
`c.decode (c.encode a ++ rest) = some (a, rest)` (`Codec.decode_encode`).
Codecs are closed under `seq`, `left`, `right`, `map`, `refine`, `sigma`,
`sum`, `delimited`, `lengthPrefixed`, `many` and `manyTill`, each lawful by
construction; base codecs are `token`, `lit`, `rest`, `nat`, `natBE`,
`string` and `bytes`.
-/
